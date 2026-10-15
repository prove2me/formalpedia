-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5164
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:57:17.557695+00:00
-- url     : https://prove2.me/submissions/5312a33c-95af-4e48-894f-f5cffced180e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 928597122 ≤ n < 928776978 has `n! + 1` a square.
For every such `n` a prime `p > n + 1` (from a per-sub-range list, each prime certified by a
gcd against a product of all primes below its square root) with `j = p - 1 - n`,
`Q = (-1)^j j! mod p` and `N = Q (Q - 1) mod p` has `N ^ ((p - 1) / 2) ≡ -1 (mod p)`; by Wilson
`Q^2 (n! + 1) ≡ N`, so `n! + 1` is not a square mod `p`. Checked by the kernel
(`decide +kernel`) through the frame `BRFrame`. -/

set_option autoImplicit false
set_option linter.all false
set_option Elab.async false

namespace BRFrame

/-! ## 1. The criterion (Wilson + Euler)

For a prime `p = n + j + 1`, Wilson's theorem gives `n! * Q = -1` in `ZMod p` with
`Q = (-1) ^ j * j!`. If `n! + 1 = m ^ 2` then `Q * (Q - 1) = (Q * m) ^ 2` is a square, so its
`(p - 1) / 2`-th power is `0` or `1`, never `-1`. -/

theorem fact_split (p : ℕ) : ∀ j n : ℕ, n + j + 1 = p →
    (((p - 1).factorial : ℕ) : ZMod p) =
      ((n.factorial : ℕ) : ZMod p) * ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) := by
  intro j
  induction j with
  | zero =>
    intro n h
    have e : p - 1 = n := by omega
    rw [e]
    simp
  | succ j ih =>
    intro n h
    rw [ih (n + 1) (by omega), Nat.factorial_succ n, Nat.factorial_succ j]
    have h0 : ((n + 1 + (j + 1) : ℕ) : ZMod p) = 0 := by
      rw [show n + 1 + (j + 1) = p by omega]
      exact ZMod.natCast_self p
    push_cast at h0 ⊢
    linear_combination ((-1) ^ j * ((j.factorial : ℕ) : ZMod p) * ((n.factorial : ℕ) : ZMod p)) * h0

theorem crit (p n j m : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hj : n + j + 1 = p) (Q N : ℕ)
    (hQ : (Q : ZMod p) = (-1) ^ j * ((j.factorial : ℕ) : ZMod p))
    (hN : (N : ZMod p) = (Q : ZMod p) * ((Q : ZMod p) - 1))
    (he : (N : ZMod p) ^ ((p - 1) / 2) = -1) : Nat.factorial n + 1 ≠ m ^ 2 := by
  intro hm
  haveI := Fact.mk hp
  have hw : ((n.factorial : ℕ) : ZMod p) * (Q : ZMod p) = -1 := by
    rw [hQ, ← fact_split p j n hj]
    exact @ZMod.wilsons_lemma p _
  have hm' : ((n.factorial : ℕ) : ZMod p) + 1 = (m : ZMod p) ^ 2 := by
    have := congrArg (fun x : ℕ => (x : ZMod p)) hm
    push_cast at this
    exact this
  have hsq : (N : ZMod p) = ((Q : ZMod p) * (m : ZMod p)) ^ 2 := by
    rw [hN, mul_pow, ← hm']
    linear_combination (-(Q : ZMod p)) * hw
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have h2e : 2 * ((p - 1) / 2) = p - 1 := by omega
  rw [hsq, ← pow_mul, h2e] at he
  by_cases hx : (Q : ZMod p) * (m : ZMod p) = 0
  · rw [hx, zero_pow (by omega)] at he
    have h1 : (1 : ZMod p) = 0 := by linear_combination he
    exact one_ne_zero h1
  · rw [ZMod.pow_card_sub_one_eq_one hx] at he
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination he
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).1 h2
    have := Nat.le_of_dvd (by norm_num) hd
    omega

/-! ## 2. Modular powering: four windows (8, 7, 7, 7 bits; fast for `e < 2 ^ 29`; exact for all `e`) -/

def w7 (p a e : ℕ) : ℕ :=
  Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow
    (Nat.mod (Nat.pow a (Nat.shiftRight e 21)) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 14) 127))) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 7) 127))) p) 128)
    (Nat.pow a (Nat.land e 127))) p

theorem win (p a x u d : ℕ) (hx : x ≡ a ^ u [MOD p]) :
    Nat.mod (Nat.mul (Nat.pow x 128) (Nat.pow a d)) p ≡ a ^ (u * 128 + d) [MOD p] := by
  refine (Nat.mod_modEq (x ^ 128 * a ^ d) p).trans ?_
  rw [pow_add, pow_mul]
  exact (hx.pow 128).mul_right _

theorem sh_div (e k : ℕ) : Nat.shiftRight e k = e / 2 ^ k := by
  show e >>> k = e / 2 ^ k
  rw [Nat.shiftRight_eq_div_pow]

theorem w7_spec (p a e : ℕ) : w7 p a e ≡ a ^ e [MOD p] := by
  have d14 : Nat.land (Nat.shiftRight e 14) 127 = e / 2 ^ 14 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d7 : Nat.land (Nat.shiftRight e 7) 127 = e / 2 ^ 7 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d0 : Nat.land e 127 = e % 2 ^ 7 := Nat.and_two_pow_sub_one_eq_mod _ 7
  unfold w7
  rw [d14, d7, d0, sh_div e 21]
  have h0 : Nat.mod (Nat.pow a (e / 2 ^ 21)) p ≡ a ^ (e / 2 ^ 21) [MOD p] := Nat.mod_modEq _ _
  have h1 := win p a _ _ (e / 2 ^ 14 % 2 ^ 7) h0
  have h2 := win p a _ _ (e / 2 ^ 7 % 2 ^ 7) h1
  have h3 := win p a _ _ (e % 2 ^ 7) h2
  refine h3.trans ?_
  have ee : ((e / 2 ^ 21 * 128 + e / 2 ^ 14 % 2 ^ 7) * 128 + e / 2 ^ 7 % 2 ^ 7) * 128 + e % 2 ^ 7 = e := by
    norm_num
    omega
  rw [ee]

/-! ## 3. The factorial table

`mkT W k j f acc` appends `f = j!`, `(j+1)!`, ... (`k` entries, `W` bits each) below `acc`, so in
`TB W J = mkT W (J + 1) 0 1 0` the entry `j` sits at bit `W * (J - j)`. Nothing is assumed about it:
`tabOK` checks every entry against a running factorial in the kernel. -/

def mkT (W : ℕ) (k : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) (fun _ _ acc => acc)
    (fun _ ih j f acc => ih (Nat.add j 1) (Nat.mul f (Nat.add j 1)) (Nat.lor (Nat.shiftLeft acc W) f)) k

def ext (T W M J j : ℕ) : ℕ := Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M

/-- `tabOK T W M J k j f`: entries `j, j+1, ..., j+k-1` equal `f, f*(j+1), ...` -/
def tabOK (T W M J : ℕ) (k : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => true)
    (fun _ ih j f => Nat.beq (ext T W M J j) f && ih (Nat.add j 1) (Nat.mul f (Nat.add j 1))) k

theorem tabOK_sound (T W M J : ℕ) : ∀ k j, tabOK T W M J k j (Nat.factorial j) = true →
    ∀ i, j ≤ i → i < j + k → ext T W M J i = Nat.factorial i := by
  intro k
  induction k with
  | zero => intro j _ i h1 h2; omega
  | succ k ih =>
    intro j h i h1 h2
    have h' : (Nat.beq (ext T W M J j) (Nat.factorial j) &&
        tabOK T W M J k (Nat.add j 1) (Nat.mul (Nat.factorial j) (Nat.add j 1))) = true := h
    rw [Bool.and_eq_true] at h'
    by_cases hij : i = j
    · subst hij
      exact Nat.eq_of_beq_eq_true h'.1
    · have hf : Nat.mul (Nat.factorial j) (Nat.add j 1) = Nat.factorial (j + 1) := by
        show Nat.factorial j * (j + 1) = Nat.factorial (j + 1)
        rw [Nat.factorial_succ, Nat.mul_comm]
      have h2' := h'.2
      rw [hf] at h2'
      exact ih (j + 1) h2' i (by omega) (by omega)

/-! ## 4. Prime pools

`chk6 P T`: `6 ∣ P` and `6t+5`, `6t+7` share a factor with `P` for every `t < T`; then every prime
`q ≤ 6T+1` divides `P`. A number `q < Bd` with `gcd q P = 1` and every prime `r` with `r * r < Bd`
dividing `P` is prime. -/

def chk6 (P : ℕ) (T : ℕ) : Bool :=
  Nat.beq (Nat.mod P 6) 0 &&
  Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T

theorem chk6_rec (P : ℕ) : ∀ T, Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T = true →
    ∀ t, t < T → Nat.gcd (6 * t + 5) P ≠ 1 ∧ Nat.gcd (6 * t + 7) P ≠ 1 := by
  intro T
  induction T with
  | zero => intro _ t ht; omega
  | succ T ih =>
    intro h t ht
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨h5, h7⟩, hr⟩ := h
    by_cases htT : t = T
    · subst htT
      constructor
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 5) P) 1 = true
          rw [hc]; rfl
        rw [this] at h5; exact absurd h5 (by decide)
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 7) P) 1 = true
          rw [hc]; rfl
        rw [this] at h7; exact absurd h7 (by decide)
    · exact ih hr t (by omega)

theorem chk6_sound (P T : ℕ) (h : chk6 P T = true) :
    ∀ q : ℕ, q.Prime → (q ≤ 3 ∨ q ≤ 6 * T + 1) → q ∣ P := by
  unfold chk6 at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h6, hr⟩ := h
  have h6' : P % 6 = 0 := Nat.eq_of_beq_eq_true h6
  have hall := chk6_rec P T hr
  intro q hq hb
  have hq2 := hq.two_le
  have hdvd : ∀ t, (q = 6 * t + 5 ∨ q = 6 * t + 7) → t < T → q ∣ P := by
    intro t ht htT
    rcases Nat.coprime_or_dvd_of_prime hq P with hc | hc
    · rcases ht with ht | ht
      · rw [ht] at hc; exact absurd hc (hall t htT).1
      · rw [ht] at hc; exact absurd hc (hall t htT).2
    · exact hc
  by_cases h23 : q ≤ 3
  · have : q = 2 ∨ q = 3 := by omega
    rcases this with e | e
    · subst e; omega
    · subst e; omega
  · have hb' : q ≤ 6 * T + 1 := by omega
    have hm : q % 6 = 1 ∨ q % 6 = 5 := by
      have h2 : ¬ 2 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 hd
        omega
      have h3 : ¬ 3 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 hd
        omega
      omega
    rcases hm with hm | hm
    · exact hdvd (q / 6 - 1) (Or.inr (by omega)) (by omega)
    · exact hdvd (q / 6) (Or.inl (by omega)) (by omega)

theorem prime_of_pool (P Bd q : ℕ) (hP : ∀ r : ℕ, r.Prime → r * r < Bd → r ∣ P) (h2 : 2 ≤ q)
    (hq : q < Bd) (hc : Nat.gcd q P = 1) : q.Prime := by
  by_contra hnp
  have hq1 : q ≠ 1 := by omega
  have hmp := Nat.minFac_prime hq1
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  have hsq' : q.minFac * q.minFac ≤ q := by rw [← pow_two]; exact hsq
  have hdP := hP q.minFac hmp (by omega)
  have hd : q.minFac ∣ Nat.gcd q P := Nat.dvd_gcd (Nat.minFac_dvd q) hdP
  rw [hc] at hd
  have := Nat.le_of_dvd one_pos hd
  have := hmp.two_le
  omega

/-- pools: `6` below `16`, `30030` below `196`, `P3` below `32761`, `P4` below `1024000000` -/
def pOK (P3 P4 p : ℕ) : Bool :=
  Nat.ble 5 p && cond (Nat.blt p 16) (Nat.beq (Nat.gcd p 6) 1)
    (cond (Nat.blt p 196) (Nat.beq (Nat.gcd p 30030) 1)
      (cond (Nat.blt p 32761) (Nat.beq (Nat.gcd p P3) 1)
        (Nat.blt p 1024000000 && Nat.beq (Nat.gcd p P4) 1)))

theorem blt_t {a b : ℕ} (h : a < b) : Nat.blt a b = true := by simpa using h

theorem blt_f {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · exact absurd (by simpa using hb) h

theorem P6_ok : chk6 6 0 = true := by decide +kernel
theorem P30030_ok : chk6 30030 2 = true := by decide +kernel

theorem pOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) (p : ℕ)
    (h : pOK P3 P4 p = true) : p.Prime ∧ 5 ≤ p := by
  unfold pOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h5, h⟩ := h
  have h5' := Nat.le_of_ble_eq_true h5
  refine ⟨?_, h5'⟩
  by_cases c1 : p < 16
  · rw [blt_t c1, cond_true] at h
    exact prime_of_pool 6 16 p (fun r hr hrr => chk6_sound 6 0 P6_ok r hr (by
      left; by_contra hc; have : 4 * 4 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c1 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c1, cond_false] at h
  by_cases c2 : p < 196
  · rw [blt_t c2, cond_true] at h
    exact prime_of_pool 30030 196 p (fun r hr hrr => chk6_sound 30030 2 P30030_ok r hr (by
      right; by_contra hc; have : 14 * 14 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c2 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c2, cond_false] at h
  by_cases c3 : p < 32761
  · rw [blt_t c3, cond_true] at h
    exact prime_of_pool P3 32761 p (fun r hr hrr => chk6_sound P3 30 h3 r hr (by
      right; by_contra hc; have : 182 * 182 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c3 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c3, cond_false, Bool.and_eq_true] at h
  have c4 := Nat.le_of_ble_eq_true h.1
  exact prime_of_pool P4 1024000000 p (fun r hr hrr => chk6_sound P4 5333 h4 r hr (by
      right; by_contra hc; have : 32000 * 32000 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c4 (Nat.eq_of_beq_eq_true h.2)

/-! ## 5. One `n`: the test

`fm`: `j!` from the table for `j ≤ J`, else from entry `J` by the loop `lp` (rare).
`nN = f * (f + s) mod p` with `f ≡ j! (mod p)`, `s = p - 1` (`j` even) or `1` (`j` odd); this is
`Q * (Q - 1)` for `Q = (-1)^j j!`. -/

def lp (p : ℕ) (k : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun _ ih i acc => ih (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p)) k

theorem lp_spec (p : ℕ) : ∀ k i acc, acc ≡ Nat.factorial i [MOD p] →
    lp p k i acc ≡ Nat.factorial (i + k) [MOD p] := by
  intro k
  induction k with
  | zero => intro i acc h; exact h
  | succ k ih =>
    intro i acc h
    have e : lp p (k + 1) i acc = lp p k (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p) := rfl
    rw [e]
    have h2 : Nat.mod (Nat.mul acc (Nat.add i 1)) p ≡ Nat.factorial (i + 1) [MOD p] := by
      refine (Nat.mod_modEq (acc * (i + 1)) p).trans ?_
      rw [Nat.factorial_succ, Nat.mul_comm (i + 1)]
      exact h.mul_right _
    have := ih (i + 1) _ h2
    rw [show i + 1 + k = i + (k + 1) by omega] at this
    exact this

def fm (T W M J p j : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
    (ext T W M J j) (Nat.ble j J)

theorem fm_spec (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    fm T W M J p j ≡ Nat.factorial j [MOD p] := by
  unfold fm
  by_cases hj : j ≤ J
  · have hb : Nat.ble j J = true := by rw [Nat.ble_eq]; exact hj
    rw [hb]; dsimp only; rw [hT j hj]
  · have hb : Nat.ble j J = false := by
      cases h : Nat.ble j J
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true h) hj
    rw [hb]; dsimp only
    have h0 : Nat.mod (ext T W M J J) p ≡ Nat.factorial J [MOD p] := by
      rw [hT J le_rfl]; exact Nat.mod_modEq _ _
    have := lp_spec p (Nat.sub j J) J _ h0
    rw [show J + Nat.sub j J = j by show J + (j - J) = j; omega] at this
    exact this

def nN (T W M J p j : ℕ) : ℕ :=
  Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p

theorem cast_nN (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) (hp : 2 ≤ p) :
    ((nN T W M J p j : ℕ) : ZMod p) =
      ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) * (((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) - 1) := by
  have hm : ((fm T W M J p j : ℕ) : ZMod p) = ((j.factorial : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 (fm_spec T W M J p j hT)
  have hl : Nat.land j 1 = j % 2 := Nat.and_one_is_mod j
  unfold nN
  rw [show Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p =
    (fm T W M J p j * (fm T W M J p j + (p - (1 + j % 2 * (p - 2))))) % p by rw [hl]; rfl]
  rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_add, hm]
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · rw [h, zero_mul, add_zero, Nat.cast_sub (by omega), ZMod.natCast_self]
    have : Even j := Nat.even_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring
  · rw [h, one_mul, show p - (1 + (p - 2)) = 1 by omega]
    have : Odd j := Nat.odd_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring

theorem good_of (T W M J n p : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (hp : p.Prime) (hp5 : 5 ≤ p) (h1 : Nat.blt (Nat.add n 1) p = true)
    (h3 : Nat.beq (w7 p (nN T W M J p (Nat.sub p (Nat.add n 1))) (Nat.shiftRight p 1)) (Nat.sub p 1) = true)
    (m : ℕ) : Nat.factorial n + 1 ≠ m ^ 2 := by
  have h1' : n + 1 < p := Nat.le_of_ble_eq_true h1
  set j := Nat.sub p (Nat.add n 1) with hj
  have hjv : j = p - (n + 1) := rfl
  have hN := cast_nN T W M J p j hT (by omega)
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with e | e
    · omega
    · exact e
  have hsh : Nat.shiftRight p 1 = (p - 1) / 2 := by
    rw [sh_div]
    omega
  have : NeZero p := ⟨by omega⟩
  have hw := w7_spec p (nN T W M J p j) (Nat.shiftRight p 1)
  rw [Nat.eq_of_beq_eq_true h3, hsh] at hw
  have he : ((nN T W M J p j : ℕ) : ZMod p) ^ ((p - 1) / 2) = -1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hw
    push_cast at this
    rw [← this]
    show ((p - 1 : ℕ) : ZMod p) = -1
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]
    simp
  exact crit p n j m hp (by omega) (by omega) ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)).val
    (nN T W M J p j) (by rw [ZMod.natCast_zmod_val]) (by rw [ZMod.natCast_zmod_val]; exact hN) he

/-! ## 6. The prime stream

A stream is a head prime `ph` and the packed gaps `Gp` (8 bits each, gap / 2, low first).
`sp i ph Gp` is its `i`-th element. Once `Gp = 0` the stream is constant. `sOK` checks every
element against the pools. -/

def sp (i : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun ph _ => ph)
    (fun _ ih ph Gp => ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8)) i

theorem sp_zero (ph Gp : ℕ) : sp 0 ph Gp = ph := rfl

theorem sp_succ (i ph Gp : ℕ) :
    sp (i + 1) ph Gp = sp i (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := rfl

theorem sp_const : ∀ i ph, sp i ph 0 = ph := by
  intro i
  induction i with
  | zero => intro ph; rfl
  | succ i ih =>
    intro ph
    rw [sp_succ]
    have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
      show ph + 2 * (0 &&& 255) = ph
      simp
    have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
    rw [e1, e2, ih]

def sOK (P3 P4 : ℕ) (f : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => false)
    (fun _ ih ph Gp => pOK P3 P4 ph && (Nat.beq Gp 0 ||
      ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) f

def SP (ph Gp : ℕ) : Prop := ∀ i, (sp i ph Gp).Prime ∧ 5 ≤ sp i ph Gp

theorem sOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) :
    ∀ f ph Gp, sOK P3 P4 f ph Gp = true → SP ph Gp := by
  intro f
  induction f with
  | zero => intro ph Gp h; exact absurd h (by simp [sOK])
  | succ f ih =>
    intro ph Gp h
    have h' : (pOK P3 P4 ph && (Nat.beq Gp 0 ||
      sOK P3 P4 f (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) = true := h
    rw [Bool.and_eq_true, Bool.or_eq_true] at h'
    obtain ⟨hp, hr⟩ := h'
    have hph := pOK_sound P3 P4 h3 h4 ph hp
    intro i
    cases i with
    | zero => exact hph
    | succ i =>
      rw [sp_succ]
      rcases hr with h0 | h1
      · have hG : Gp = 0 := Nat.eq_of_beq_eq_true h0
        subst hG
        have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
          show ph + 2 * (0 &&& 255) = ph
          simp
        have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
        rw [e1, e2, sp_const]
        exact hph
      · exact ih _ _ h1 i

theorem SP_next (ph Gp : ℕ) (h : SP ph Gp) :
    SP (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := by
  intro i
  have := h (i + 1)
  rw [sp_succ] at this
  exact this

/-! ## 7. The walk

State: `n`, the prime stream `(ph, Gp)` (`ph` = the first prime `≥ n + 2`) and the record codes `R`
(low bits first). The code `t` (see `tsel`) selects the prime `sp t ph Gp` for `n`. The fuel is the
number of `n` still to check; at fuel `0` the walk requires `n = nE`. The body is written flat (lets,
`Bool.rec`) for kernel speed; `walk_succ` gives its meaning. -/

def wr (b : Bool) : Bool := b

/-- the record code: 2 bits `c`; `c < 3` gives `t = c`, else `t = 3 + ` the next 6 bits -/
def tsel (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) (Nat.land R 3)
    (Nat.blt (Nat.land R 3) 3)

def rnx (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) (Nat.blt (Nat.land R 3) 3)

def adP (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3))

def adG (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3))

theorem SP_adv (n ph Gp : ℕ) (h : SP ph Gp) : SP (adP n ph Gp) (adG n ph Gp) := by
  unfold adP adG
  cases hb : Nat.blt ph (Nat.add n 3)
  · dsimp only; exact h
  · dsimp only; exact SP_next ph Gp h

noncomputable def walk (T W M J nE : ℕ) (f : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → Bool) (fun n _ _ _ => Nat.beq n nE)
    (fun _ ih n ph Gp R =>
      let c0 := Nat.land R 3
      let b0 := Nat.blt c0 3
      let t := Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) c0 b0
      let p := sp t ph Gp
      let j := Nat.sub p (Nat.add n 1)
      let fj := Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
        (Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M) (Nat.ble j J)
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (ih (Nat.add n 1)
            (Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) b0)))
          (Nat.beq (w7 p (Nat.mod (Nat.mul fj (Nat.add fj (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1)
            (Nat.sub p 2)))))) p) (Nat.shiftRight p 1)) (Nat.sub p 1)))
        (Nat.blt (Nat.add n 1) p)) f

theorem walk_zero (T W M J nE n ph Gp R : ℕ) : walk T W M J nE 0 n ph Gp R = Nat.beq n nE := rfl

theorem walk_succ (T W M J nE f n ph Gp R : ℕ) :
    walk T W M J nE (f + 1) n ph Gp R =
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R)))
          (Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
            (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
            (Nat.sub (sp (tsel R) ph Gp) 1)))
        (Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)) := rfl

/-- `Cov A n`: no `x ∈ [A, n)` has `x! + 1` a square -/
def Cov (A n : ℕ) : Prop := ∀ x, A ≤ x → x < n → ∀ m, Nat.factorial x + 1 ≠ m ^ 2

theorem walk_sound (T W M J nE A : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    ∀ (f n ph Gp R : ℕ), walk T W M J nE f n ph Gp R = true → SP ph Gp → Cov A n → Cov A nE := by
  intro f
  induction f with
  | zero =>
    intro n ph Gp R h _ hC
    rw [walk_zero] at h
    rw [← Nat.eq_of_beq_eq_true h]
    exact hC
  | succ f ih =>
    intro n ph Gp R h hS hC
    rw [walk_succ] at h
    cases h1 : Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)
    · rw [h1] at h; dsimp only at h; exact absurd h (by decide)
    rw [h1] at h; dsimp only at h
    cases h3 : Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
          (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
          (Nat.sub (sp (tsel R) ph Gp) 1)
    · rw [h3] at h; dsimp only at h; exact absurd h (by decide)
    rw [h3] at h; dsimp only at h
    have hw : walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R) = true := h
    refine ih _ _ _ _ hw (SP_adv n ph Gp hS) ?_
    intro x hx1 hx2 m
    by_cases hxn : x < n
    · exact hC x hx1 hxn m
    · have hxe : x = n := by
        have : x < n + 1 := hx2
        omega
      subst hxe
      exact good_of T W M J x _ hT (hS _).1 (hS _).2 h1 h3 m

/-- one sub-range: the prime stream passes the pools and the walk reaches `nE` -/
noncomputable def sub (P3 P4 T W M J nE f n ph Gp fs R : ℕ) : Bool :=
  sOK P3 P4 fs ph Gp && walk T W M J nE f n ph Gp R

theorem sub_sound (P3 P4 T W M J nE A f n ph Gp fs R : ℕ)
    (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true)
    (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (h : sub P3 P4 T W M J nE f n ph Gp fs R = true) (hC : Cov A n) : Cov A nE := by
  unfold sub at h
  rw [Bool.and_eq_true] at h
  exact walk_sound T W M J nE A hT f n ph Gp R h.2 (sOK_sound P3 P4 h3 h4 fs ph Gp h.1) hC

theorem cov_init (A : ℕ) : Cov A A := fun x h1 h2 => absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

theorem tab_all (T W M J : ℕ) (h : tabOK T W M J (J + 1) 0 1 = true) :
    ∀ i, i ≤ J → ext T W M J i = Nat.factorial i := by
  intro i hi
  exact tabOK_sound T W M J (J + 1) 0 (by simpa using h) i (by omega) (by omega)

/-- assemble a big number from 8192-bit groups, low group first -/
def asm (L : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun a _ ih => Nat.lor a (Nat.shiftLeft ih 8192)) L

end BRFrame

namespace BRData

def TB : ℕ := BRFrame.mkT 1680 256 0 1 0

def MM : ℕ := Nat.sub (Nat.shiftLeft 1 1680) 1

theorem TOK : BRFrame.tabOK TB 1680 MM 255 256 0 1 = true := by decide +kernel

theorem TAB : ∀ i, i ≤ 255 → BRFrame.ext TB 1680 MM 255 i = Nat.factorial i :=
  BRFrame.tab_all TB 1680 MM 255 TOK

/-- the product of the primes up to 181 -/
def P3 : ℕ := 0x30e06b35ee39cf75358315a5c3b9b2bdd2e46e25fd10a14382537a2e71312

/-- the product of the primes up to 32000, in 8192-bit groups -/
def P4 : ℕ := BRFrame.asm [
  0xdf0c850baeddb2128ac9d0fd36dd0ec2f329ef90aca3308ae6b7bcedec1424921497fc345111e60cc412113537268a736f809fc9cefc2bcbe959a57ecf6fcdc7dc216df46f82fa5bf3720c4270cf6fb13e1dcf489d98985e4f734ee9fac8505c106eb7b2acdb6bb26b79b9cd02729d2a2b215b45d1ad39b752020674f4f03993d6c7a96c9df2c43cdd5fcdd4a2a82b5082c3e0eab548cededa2cc10cfb2c34e6f98c290160b64fdf83e7d3438e6077c84a97d92b85d47ac7b128a35167b6e0531f91938128b16ed40b0ea8ed276a4a879f7c745e779c2215fa0572e7a15cae72ee309c077cfb5b3d707818405d883f07d24cd50cd5cefb61fd23ae30b49766951623101af6e194dae9d45749c5926504c31b2e31d16b3a1d8d8f628e30e1137c5dd8637ac50c416fb56e780354d53f83146505e0b75b3fd791dfb6d1cccdf46dd3bacd8c80998bafeec517c181f3bb39e1a7ff75b63960e7e4fbfa4ab3cd18f8673b3d211d62f5e0b3e98f4fcf16bc36e8d7000957b714c4798645de1678e06a21c7cc25ca8fd857afcda85428c1cff131cba807766664cd1ef92b24719ad71a1cacc089d80d1baf2446d3f91edab2290690b4fb849083f3506e79ef43443cfe351c5874753757cdb387af230e22804870783e587646125c93d5e22899c55a15ce29a46aa788de770abed396e6fa35fc451018422e12cda42c1968eb0b94f01da5b9943508ea2fe4ba6651d5d47287366890f2cd535e3789780c5933d6df7e974200cef40380b365f780703c6c344beeb37d043d1ef50ebe5b4b1dc45ace9088eb5474968a0e3305d300ae7a40322ab01357e0cffcf44216a95c444ff2a19bac8a80242e5b642615b266fa3b82e4ebec98b03bd5f61703e03d249324888f88edca090f5ed1243e0a4675f6ae3953d13092b10e09246ac59dc44eba77e164dbfe0f4949818965554093616dc9e4d28ec2f4206870ee44b9ad38fba67c42730b4845e2204f42dcb968564cf342d81da1dbbcb2ad1f705abde27272ca6eb434e635441102a00bb1b3837369200971d33813d146a5507c16e5102a5474ae182d25b8f97aee76e787fb717b4826f264800d01b229407e10b46c31d717cace03707e9813842dde7b9c675f84a599ec1ee76abcbcd5643683142b3af9a5e3ba165a9c8a2d3a8d31de317adde8d146dae44c42d3d79b56996c6c55111ea3f81174d232c5ae8bcf0f11585f68cb32a6395e58907339157f0717bc3ea165222c9ec5363162cf78432b92d4ae5025439cbe242ad10e1460f96a3b9257bb1a9075a34866508f80116c20e59d9ef0bcc790262003e760d1d5a97248b955f6cc61eab2893f5cb8e57f2f293c308165efec92b10c382c1a7f4d7b6b32691a1b62141c02811f4b3027674bebab643b34a70f166e082f1a3489b265b5b1fee25e582b1b076210fe9a,
  0xea98014cae2ac4237f4b4213a735cb3415a1380744196e3371ef349273475b1a9a19eea2b2d83e892b4404ffc9ec8f00c804866f9a9ce72904a292c8101dcfff2039576180f44def879add63b1eccb590677693cae9f49dbf554c6ceba32faf6e84616a64ecc2681a2c895e1090378b6222b56e1bd9cb731fa2064f7b7f066b45169170ba0d08741bd1b0820d77238b47918f994c8aced205746fc0ff5ddd8cf95dd8ef62dd050286266519e45e40e5b2950b8b223c07f101ce162963018ecebd501267eaddb02f56ee6b654257d20d3bf13f73db708520ed0117af6564bb8b0a469856a8cc3e2cae84a242db11e2b060f957bfdc5baa0d4c74a319342609401e3be3e2cf7e1993561e8784857ff0965514a4a9f7a10dcbb1fea1c8cf72786bf6e32594aa1d4908db83d4dfb1c3f8cd9d7a4aa673346618dca07b597d1815974f7e7e86e6d40001b0442574f4404912ee91e38bd7d52aa3eb4ba0fbd5446f731b1baa64f5d05d16a29f33c5cf42cf1f8c2f1d0f96b9a325944e8f02b0169806f2efa153ceefd95679ff923ecc80ceafb98996c16305b5e644d2071399cb7883f6b8a85be82455a9824ef5c3288e149fd62ecee29447798e1f5ea7d3919c51b567ea37288bbefe5b6d943b1edeccad5d4a1284aeddf22256e16e5017fe48dda91d4a4172047b9b6ebdbb35f04afab8a3534b41b758159b035c092cc36876c6db744cdc4558288c5ada4a7c4ca4ef963e05eb3b79ee9f2ba92cca910e4fe4419e33cd12dbd87527274732251e53c0c447842cca8504abf89fb2a0fe66269142a99315d9cfd1cb18ff00a8c0cc9b7d21e6b2d9bba36823cae88b84340801e5c81472d1211357bf791b4b9a83cb8f885a19b4d93e68561301fa92d04eac64892047c44106b572731bc2bc586f7d428463bf12880ddf84b9bcb8b75d18f68f07b2d3a4529f33c265efaa9046e94f310aa9a47d70bf8cca38f0a707a6ce8c2756003dc094a30edb3a17ef3aa4894be8e5d72e22421f097677b90ef6274cb0fe493550d58529e9b9331d11bb641d336d163489ce32364bdf6ed4b327e5a56409b1e276f1ed03f5afc4b1f1eb46f50ea2bd818b6ce560fcf4033323b7f46aab313f4bc2688a9e8ccc1545c5c811b34d48d14308a334a169c2016d94e11129100571fa1dd1c841f5a7bfccbabbc545dba69de8cd04f05f4ad32d476559836d35aca9a7381fa618e0c7e7855e9cd829a0cabdbe9e3c01746e3ae03c2e18f4aa76ef419e3de8bfe4b21500785d9b6964477b8a840ec2cdc45f3227e280e2c5f8f6c6a26c3881003f03b9c89575763154d252dc974ecf290538b9105fcea649307d65a15a817627084c27089384b6073f28023d245a2d78437adc9909abf78ae77d00006f6386c40a33acffa01cdf3667bf58b5a38e6502cd21718fca0d04aeabb5d7635e4b4,
  0x1728b345ae1d105890be726995db87cb8d8643422401f2b9d4fd947140af5fdd89523ad14c14787386bde21dc9610b22e07e931ba28009eb69a71e1cfbc0df11d42c4526b66824c91f442c5636d120007e4d24e3bad931045a7365deef650235aae6a3996d4288b7a45118f689202f6eb7631f39ccfe3ed30df63f6dfa1eaea9abcfc0fbb1889d08158387786d5babb4711aeca73bc3b3e7f510660123273125559e32ae86789b3eea846b65e518bd1b82f86a68b6622dee93c66f28b57bb32c66c334eb0e4e18da04a01e1458f10bfb1b91ada31354048151dc2f7b5e1d35cd094790b3a592983b79c98f2002554d6ac0753e09d4c95de4b0a2dc4af58bc18ba1c404b3cf1f6f5e6353388ba00542736dafb6b3890ed4eb1aa021baa0a1027503756833e069161f3b5df47575a40f2ed8ae5cf84444b7fb646bd1ccb521788b5d39ee4e9492f45b5052f2f8d973d0e798ef2bea1edb9884c1f5ad82ff9f2da775d8c1abba03a5c92ff2c3ccc31a8afb22947e1d06745a05cf02d819e21c1b9eeb81560ef0e999cbf56d4bdb20ee9ae7563555bafaaa67efb0cb235529236a4abc3bbed82dcdf54e45470f179f2174157be3c2cad7e76c7b9fa12a3cedcea2a33cdb5facb5327aead5e2ee441ebfe4a944440623d53d4bdb3e5fa4e7f03a0f3ce18b1b2507fe33b65c49534c5ef0e31577cb2e11c80dd4827e40e09ce1cef2aa8a0b6d04973a6431ea0e721a266ed55b1d51682cf24816a6ef7c28d315fd2c4efd94b46caeb7fa54aa9b6e0b0061cbdd73b551b7a80783e8e600f9a9162f2199788c98a444e28ebb46b57043028fe6c474260640a987cbb7babaf34191506f6a669df1064bb5d3a4522f3706dd1a5615ca291b33cdcc418266d52fda48d187a9bd0c40513361bd5652581c1b2ab80879f9b9c802787745e17a9791fe2d94f2bbbf9e8bd08fed5d2fc21b095a1d18135390d99ffac0dba4a55c77a4ccdef9c1b63ab95770f5296498093b9806389530270a161a78b2759215b5156f0b69960117f858d201d20305aac1d8936d3d8c70293ead432613a327abd5d6b7ec767a694bccfceffb2f505bb0e8cf019e8ba6c25ba9c8a66d8ab729be0c889e5c33b9b003a2777b2ee1a7f1ac50a0b600f9df13abc417f92e56a627fec3318cfec09c3ce8ed11cd38beecc9fe62800f28b554bbb032d54ec3265b9510da2763ffbffa465ebba8541e162029eb43803ead99cc036eac2906e2508acfd0b87815960f33f1250c4c93c84772fcf343e319166a963b9438080e93537495f38e222f30b9388f432d57e061f06db832fc76cd7c2246cdbc725791eedbb0f020e4518bb711c9947fd13da39b34eeaa20b783fda7c7fd6bb5a6bfc5ae0aac9be0260efd746edb56cbad7adf1f59b4ef5590ebf5dc901afac752539f95fa616c0121643f4021b923b,
  0x3c458fee709566842171df4fdf91d1866173d1b733c3309816fb19e69ff4d6644f481709bd1680e21b432a184cfcde4bd4f9b43742cb46b2f3ffd58b5ca10366aa342a9454eedf37ffe61d5b7b01c242438d0aa617697b258e4b6e05f86953963e9b1fb21af5ca4ee94189cb1a9899de56581900c1cb81777ee13638ac508ece1dd9c8bf76060130ee98831d9c1fb6548e12387a276ccb9a1faf40a2ee45223252152bd2949b6b5a7ee3ed5c2879d3abcd1a50c7fafe7d7464053500e063887b01e11ff8f5c27000443e192c9ec6511816a4ef4f6c73c364b4b4e11e4b0f6f2bbe6941fc1002d33c2ea0d80d7c2e37e70d298651f344f10070630a47cd0f686b749590c52fe4333d58a21b210eb744d4e7df8a6d79ce7137a4ba9425114e86d112ff16e899cd2041bb3781489ce56232fa4de91c7ae07bd635bf1f0e554e20163b0a43ed81ab1095811abc702564c76b49adcbc3f5264e74823a695e1847b559021d6babbe9d6989a4eb4d5ff4dff6de9169bddcac984a8bf3d9f653c91cd620b187bdf4e086e2cff33827ccf543d72f80d31c0cfa9b0ec3344ac92fd84b3a3671009f4929fca57466981b49b59806ec5b95115c1d11b21099d94bf85ef0b7bdfdcf30ef86cc521e5a4d267c48da55d3b81706d40dd2e26357d7c865da72c94fd723e3cd37aab7bc2e17c9ae1368ca36ae70f1bb5432a861bc0a79709b81f23807835b1bd97dd958f89f546ca0e74a4d91f2231841b97abae7f63d1dfa52d8d2ecbeb25f730e389347efe4030f78f44b1349e216256ce33d6dcbfd14f9b722f85a32cfcc28fb734de661fad78e2c6065b1a970274a9d4c4b238078e5ef2675620ebe8efc5874a7560f17ae9186eba32895c80e9ab5a9367ceaab065805a41b340cf88a6316b15964530bdee05e98635f268eb9aefe7c81d872c1f52d89472c117d4ead5cabd5874110e0a849337c38acfc60a476b55091afdb9c59ea0200bc2c98cb8fafcdb89a5593e6169294a2d7ad79b4d4bd02449d332f5f101f8a95a668b28a9aa5d4ee6f63265932a22b93e6b08c3cb4ce49b2114839ae8d669db30e78886393dfa8e92535a3232ce2d3b388df674137547d46af3ac76aa08a3962b010a924cecef13be7fc1ee1f857c0c1b148c8350206d93cc1c26bdf2f2083e0632187a7170294c132c8c96452ed414567d17115f3d810463dc5845b0e4b2150676860213d04f9e6b1ee1530faab6ee6281c815dc26cd93cc02c8ed58742168b4bcfe102c25dcf152f8c36ededf5c24b756d43201d572e5ec91e785f50244eac7936a17ebe3e80d537492d9ddbfbc53ed3828000ae06dd1478f12304cfaeaf8b594901c5010f524a109d67422dcf2e00b03dddfcb9ee1060b28f0156ff8707686b109c780e98ff3732bd116d2f70c96ca688419b65cdc52070b6929bfff088a3be5f,
  0x33fb30670ccc9d9161ee291159b243d56af86e6c0d29675ffa2c459c998f0c513dd30d097fc73d45684ecd2c87d420a96eddb72894cfb6b134d8599ab23ca2ce27ef0706a741bda8807b24ea39ef3e5da8774e5f2219c3cbb5573bccfa96c4c5f9b3a11dd2cc735f288dc3a82281b63255a99bc8a5e1c55002df7fda7afac36a1d276383158d287c2a4db62276a331b0b14239ceb7b72b9229337e828e76bd3b13316c1bc98279fb890663222d6f91722909d219a67282cad6eed54326f5e3ea9b7aa50d70e0e9caeec704373d0bf36057bfed71c9e794676fcf07be1e1c0ad66e7790c09f157620dfca3e522db1ac9e18ff6aa4f5ee9f682e9b4a56211d5d51aa3fb19b25926b06393d3c4c47ae87ed8c52d4f19f54ba73ad3fa32cc3da4857c98d0fa5363a46671d532322b398f90422bd732d02d272ed70fbfd0cf7be141b677000847b96d192296c900eda94ea4023fdf00bf2e7a6a9381d832e4e1189a35136b481179ba243c5661a527b140c93d9997eb066a8554bb1b07ac04974f076092dfc159a231f26ff9e7fec54a1a4afc94c723cbc812012373c707e0c81c5783247e3416ec84e3a4aa240527a9339adade0e966d9acc3a1867b2e62b4ab1f43d342508113196ac649cf973d1f98067ebe3662022398d0617ba378bc09596a6403112db6adcca330e099daa38cf9f921c1459c9f97d4be291cb38007fc34a018edb5af08589e98b71ab0e99acfda859889c4a0360109261ff6e40c85327af396767fdac713adfe8caaec684bbcab3fea995f660af05b974c5ba6ebf52d1f8e2b31117cb8faf93a0e939836d3b6af25604d7d5b4f6e144a0485d0c5b5400d4713de63a2736fdbbd20ebb835cc9591b48e10764f4744729730117cf94bd42e70f0f2e86b609f59053a2f94f83d2c855f49bc0563edc62683301a6f1af059fbedbfcf1769c0e1fe4ce07b65de8b71ade682636d0abde0bd94cdde2e1cef86e715d495cddfcdf0e420d7fc6c7b523f6cc2a181df5c50d713f7142e22812e9b36d83d5c41a754fe1e2243d67bcc372a7bc1f7b3cd66155a6d68f2d78535f6ead61180b20a9b7345e87ee56618dcbe69453bfb5db4ed7337f698e5b98735b83d30c6b59ca226c04df477bae76bb50da3ba91f4f324c51588c99d2b8258edfe273d77883d519f5059f50178c73612660f88af6f622035e53bb5cb8421128833d0e2963696885b2672976bc22bdef66a3f79a1eeb5745b266abaae035f56d7da1f92773d588519cfb671cf7f840b8c0eece8eaafaa8cdc7bd8e95db47b86de2f99a5c118b3d336c0cf108f8b13199d11f183c61a0e7fe7d42a609536ad880d22ef9acd6e7a26f94aa1aaf1cddea57ca24edf80e18bb54dc9142b3f9de36aa66add5c83fa9a1b3827de04c3ac9a362fe20443937a0dc21250e8d6183c51a530b2ff77d24,
  0x556d7e991792de0f391465729fa66f7cb4cd30e9aeda0d488686bbeaccac9ce166df07cb523e600a3b36496464fd6e277847eea66bbfbbda8d20d01bd4dac96841254b0ff6c61a90385a3239eaab5887ebdd5a6bcf72691ab6644a094162fe467ce8c72e372883ce54ca28eb67362b5b180ca57cfc027037004145ac514e280b4249af145522f74ad3b0f6eb124e1ba8e994e4ddc0dbdd8cf3f80b42f338206e5313438d9856c4af110573fa215009a4a69f506da8f1fc03695d08ba2ea83ba5b5a7e289910d1ded13d31f5810300e41bc97799d709db61c06dd64bac664891f71d68e45800f73cda9d18f19015497d2048b5193e343f89677fa0fc96fac78929ca8a69f8eb195e7705bb820a2c1d044b922b3b6cd5504ff78a3cbededfb7f1ddaa0ed0869a39884c6f13673cd0cf984a8bfdb025a3bb1af56f4031d5d5b37016db05548dedce76724a7fd52bfdec469e49a2080da2082e93fb0e7b8984d7515b69b3237649436f27c00b00035ef33f41f982ea205940153bfc318e858a5987c952474bca14aac913b1b4ab909216ee44902547a558dee848dd30c0c77b4d2794e7b6b4757e9816025934a0ca36430fe238884e8e64fadbb0d3bcaba4a39af73014f4c5e97e70e5de24c3fd9d2783b3a430158d1a672220b22612a92cf52e32121f8a5aa83d3d87fcfed7751c93bad78d5787354ebe4574d159fff7971b47dc3e0bb5c71f97a51f75996eb949d7565f8e6a18beb27aab1db5b87394d2b1525140e3493920f7b50ea878a9be48bb9e59ffc3746855d8bdf084cf0ce93a39f6f14d5b3a7d76372b40e5870bd37b3449fe5689e]

theorem P3OK : BRFrame.chk6 P3 30 = true := by decide +kernel

theorem P4OK : BRFrame.chk6 P4 5333 = true := by decide +kernel

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 928598372 1250 928597122 928597129
    0x13050609011e180203060c0408010c08060904060903110f0604150902101206050a031101030b060f070201140409020c1005101206180606091a060414010f052106 70
    0x8015001200690400a80c00791a212000c041003001103103810000b64080320441660035116070702d900940601440c400c01c0008078108028000721068080240102d204541d01107030149400c580841c0d1041482c0003080110742c050303200703050b800d01c03a082681c88912011002444c00403c10078224041c0c0c48081000100031200709224120340404105000d60303030b03260f070025207102c01001c01441000310620014892a640e0340004004000c058912088103480c1d0900030324448a02c5032090101e0b0500145134018106003049407140c2160300261420000250300440b0621841e040b5110202001c1c400414611240c0c030080c290211800018400c0b035048000c50816650010a840c1c001e0100300001c1082c415007903800f000880d4040b44c001040c041d141c4680310038905000024010070310701180407451107115400501d80c068100080c4600c00198401c1110a100318002c20410303d00d0011010115401a14006d440407481d042c45401c0086c1114200c40d45a513080101810001d08800d1207881d00303 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 928599622 1250 928598372 928598383
    0x60906091d0a020108131a0103060207030e09040b0118060e09070f0b070c06270824010302060702040903052712030723010b09010905041119150c0b1305 67
    0x2070710700d01034540350055400181c50180014280c0c81c924160310b80000c10020304280c019010f0407000d00102ca5540c69051503c002d405c6084200c001c5000206681064581000c1080c4581c1d03200d020580030303030300300714620301e420386c2820580507640c2d200c0c03d003c00c0301c91441c0b4286110395801d10003400200c0c40c1100040d00355200d41d200c3c1c50040000c00141c000310341528808070943c1c5903410300c00d602d0f5240901c8013403500280072131105c6101c4030b4013001c80c0c4032401061010034501e1404886950840c20340460039461401e120007948000c0400540005042c280c0010b0719240c02401c100e8141040a20303000940000c01c0e0f451340e40e036040230b1950110751038406540b2100d951444010f5007040703140da8902d540d4113008100030007441840c40400c003243c0002d401050b00c942e0050159403555a6440440000d098140c40407074200341c4806591905d41800098a56010038642a2034502482c02c0c41007640c4040384940f89040102d0035452a02141d00410f250f80940c40c0c0c01903a60507200181000790409 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 928600872 1250 928599622 928599671
    0x901140103030503070327030305010f0522090c1805060112020306010804391505090108040809010302041a030403110f150a0204080d0513320406090609 67
    0x424140005201082d8410b040e41c1c1e000c00241800900103181d4140204400c0c082d941e80c420207101011200c08040c1c0c50b0b00010b040b00d0b00094100c599030740301c0c02008544a50104440e81c2c1c802e1810412903c0c0300c1c950040c2d20318030700a048541c06280c0b28031b00d01c2c041e510340355442d12030140c4030300c1800180e513400a00c0030f051040300c840850540c181000000c10211000c1d002406c24400c400e214008060525601000108610910305909040081000303103c0703181d105200b42501034148014000e8064800c41e108810169901203031f5540b10740d00d946094204510403410980d0900010070140c9546460141140c10403007081e49038900751a0041ca110910403080b2660340000b12250350058000494543c20702c0818140b00e0981e81d0005540024011540a0310a0740301d10915050210b40181c001c00c03c0d02d14071100360313071480d4841049421a2881035004045048007005402c0d0a0542c0702d03280b40c8680000b00003242103551440e40c141503482da13400043c08503a6410b24016010302003103c8104d038 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 928602122 1250 928600872 928600901
    0x20607030b0a03020d050f25050d1208090c060d1b0e1516080a09050a150219111f09080f0a02091e040308010306050f1302040b0d1a0901 60
    0xc0012030030100381c0c02440c41c0f0000340150314440415082102c2400300c40703643c0108004603001440080c00700b03050441d04000481e0071400c02100460b07241004069444a80c0d041042d0042c84610072808032003450780140a181d040c0111486800140c1d504001411480c1240700b000c5000b19104020b6412612031100c11418406156580e08154452001c2805980c41c0d10003c2500c032840c030503480911240c090b00042140f6400030301d610000d5044982e02c0c06a48050f540c0c2040c40e03464446010003406004c03100d60259001080090a400502e0704000299110b2202caa1704131443e4000700c0c10040b090050051445203500d4880681d5512200700001410418000d02503c030200d01855261000c03100080e01801401001900300228030101480018114607014910724107400d004001c4a405e01041707800c01d0602c000300c0d180849004100f40114510202c1728540380c2c16a08000c024020440d11641202111012074081861a59603100e004021390300c0900a01d0142507890846003400d40d103145 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 928603372 1250 928602122 928602131
    0x60406050c0c2a04020d05070f140301051e062110140402130803040e0916030515101a0318060f0403030f02070212011d0c030309040f0b06030705070302060703 70
    0x2a080c900042c4452482c6035000400c10b4210483c06122005428541890708a4000240c2903940819984040d2044034170f43c3d80c00028183c03104084512103081c501ca070070301010a00060103903190034040c2d0f02218000c0c000845680a030300c804031741180c00031416042030301c075000c42220341d94071903690199002614414002c003060500030242e017652010120540110b501250812006003259440000b0781440c1e0110707529240d4525244030340b20f004403084626405504007103191450a207800509a0350301501a210310b10700d88082030400c0e0340060040e100e8a60000c1c00044d01c1015032501d80744035031900d03407240d502e01e001c20b0302c14009911411500c000b0342c00f02080003100704600141d282c0081e818a00031401002c0301030064080c1c0126034001e50310840802382071208110540c40010300c14103415205940c000d02c001519203510309800e03c2e07900340d04200001451441c0c42d5100d4981c0e803418001c0018520190000304000341c00448a04020810010301030040c180c0410090b0307071005492a0911 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 928604622 1250 928603372 928603387
    0xc1106060112020d020702030712060f15060806010e040f0605090c070c050118081203011715011403030403330c02120f0706050c03061c02180403090e0405060406050c 73
    0x203005610b288002000b0990100b482140e15265404039491250000d089800b03658507100b1511551944441c21102a07251640d00c803a41c4031540240404200000e511740c0d856803810300d094510140c02800c05040116007105140265228403400c213403a1207800c0000f07061070a00c000d00a011101404000e4500e905020303003000581500c901d00c1c1a07070000c0c42c102d600301d4a035040e002113a901c0e90300130105500032220390003d00c0805101550480300403005032074641c8680c00d020f80d2140411200c003188464080b0040c4900d1184030700c054120503020b41100d01d040d80d01d85031868003da42405841c1801a142140d4131721204840c14002a1440300300300704801c0c0c0c01e0041c080d42c1c0306810003440340b8842002c41c0c001491454903080d202c0c0250440da0a03c254a0141a0a07400e6401202e901c0e10484010400c0035607180350744c0d03c00801c5079015105182d40c629003d40c2c84101c600003081107040007007540012902d0606035170b2041c0a2803151000f040e41303043c03d20b803580654030300402c90301c0480028070040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 928605872 1250 928604622 928604627
    0x140c0426060115092c071b0b070c15020711010809060402010e0d060e0a0203070602030f04120204290a0e19050a1503030c050c010203040b0708090301140405010c11060601 75
    0x1c40c1165000c030b10304032800c8503200082d25a8440b581c09040c0505480007031400d4400040010140c0d0240403004000c1a52441401c0d25000d01c119040046c5100da014030100141e140303803045410120030b04069204961507036030000d60400391419280310310f40204140d0100220f14001000014003400d0640341031502c480520380d05c140061001e810084540d40194054990282c4a44810f4001609028030340d1340c484869610341d2340c00000c90280c40342d0000099040c0c80802030b00c804a40540519203824945941142620b103e4001170ba8090303980e28240f105045240c81c44281c510105440c8001a402c0c42d0402c0701c5441e065225110400c04a4108802c03d407940b4400b840ca40c648c440009595200d0100c400c00412050008002c0c1e0041c8000100c1490342003000242c200b0700c54012540041000001280c1700d0140303105c3c4803103900090145c0750024110fa00a440f01220180000031001030543d41240303040800c6c1c509036542d075990310708a803944d5030200e05507042140c010300900b418107000000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 928607122 1250 928605872 928605883
    0xf0b12060111061914010603091205040b0406030e03040509090d03050108010b0f130b0405070e0a1505160f02040603032604080331120f0306050f0405070201140c0426 73
    0x50180501d2840032070164882142e0100b41d4800116001c0304c40c03503860310307c003400522410302c081d1407004001c08442282c6108030101c400340c0700d40e6808141400e280201c150301800c10904d070005540030511000c21962030b40c5094911074020705004000400c032405000e4200c40040e0814452a41446490545a00c42a03d51210301c031081d2480d960a0100402e0b0300d0051080300b105561250411081c003000b15030141801890719011114405920354810010460aa0031603007880403c000348a80043c2c0c2c205010401011070050040b090146900c6c4c3c00902201d02c00c0e0800c0300403070000c8600c202c8482d41c41c0d07502c0d06010102000e03c611810b04e603e0740422400020505009000003210074080404d06486000400940011401c915001d81c034000d2100f44c2c1c404243c0d800205071600c4000c180303100b4024901110005040500b1b0101d225050002a0800800800039592602900d1700c58032000c0e410340b40702d440f40c950f083d610f0301e0406c50240070640c00000081040c00da00c40e0706c081c081c0c40c041007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 928608372 1250 928607122 928607131
    0x5030115030c051c0b040504151a09010b030702030f040e1005031605060d0b04060803090f010207060e060304110d0c090b01050f0d020c0c120109061506020a030e03070f0b1206011106 80
    0x70741d130700c0703030384032100d44068016800519005400d200a00042110140d03200c0d10103180f482d0140401d017007203081c00000030103198060b070f0301c80b100100400c20903442c1342c021a0840300b184196407501c00d85d10b107900510380c85030b03000c010610b030020108038280545506d0300c80940801c81c0500000d000100e04c028003111680540740c4074010000341014101c2540d031100710215000740c02401042ea0300c0038078984941140c4281030245180306a220403540c404500340c01030710420348400001501100910180350001441150a80c203003441d00e1510b03944509514601a00c110608801c040c1070290380c20503612606c1d48281409818007100071038101c40025120803510001c401a1603194015101d440d280c400c075007907a048020038804545002c019000216118024801400070203088240710410240e540301d5280141c108003d10130001e40305201540600c1001012980029103031203180c40344401c15406001d20348000100c0c466518803142140d07510030340908011050303001c0c018038a03440d02001403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 928609622 1250 928608372 928608397
    0x1b0f0b06120618010617010f05010e010b18240c0106060516030c0501091704081216020f01020c19031401050606070f03211d0c0307060e010e03030a05030115030c05 72
    0x41455020f0800d40c4003400420f40d1418642224a142c2c0102d8003c00408003c0300d440d0781000000300b0740130125403542d070403580000f1080b40f50202900d107a600083c071945071581c0c0102281c006401d5402108041010300d40710b030003902c0d9160510300d5054211104c80e802101444400c0c04100d448042d001500a1a01c1d01420010120421807415034018903206200605044807940e444c0d110354a000080c0c01501d40400c01c8031421920a1138000302800f03032004154014104054400041c107041c1d10603200c00f541030049a0b840c81d440c10014a0003035580e0314204203420800004c200740030541c50300c3d01404410300001c110b00d05002c40820298401c01da0050100300f004403c1c141054442c40c0242070b10342030031205c0707851018a0102e1001800500004810a400b08142002070303540104001c01380090050040400b249041010340b000707642c05c0a05d50500c0007804107180c02d510140b0080001004a41d5035541c2c80d03041148201d0050190a450380815282090104481d50000100c030707482c1d505c0300c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 928610872 1250 928609622 928609651
    0xe010501120608011b0908010e0c0607020f040c02030d0b0427080f0f13080102090d021201060302031b040c080118050a110a0801062c060a1b0f0b061206 67
    0xd8407a07400390425a101080942c0307020108180e40034280b04080a07900382e0340c0e48101142d9600d4085007030310901c0c410005160041504205a40b4201006080c001d10241c924214900502c00040444400e0401c83c400b61704000350326850701c031030762140d09a00c6030708503003c02034907040106064514080f4501c1c2c0400000e10411501880442019120110100c004640d910074400b1004170264100180030002202c1e0451b0101d4100818000c0d642020300140c10114601c20a4080081100010445034150b55035401c2c04000340c1c4050080400d404086100c121010303900388240811141902101000c01c041140107001e1043c000740c4e40c00c21b4118140010645840f05000300d0010828904107803502040000e1352904a07070040c00c0e0a041b10469100d101418194058040c0f0418049507260a46220900b4100035454000d0240000e104a4541882400740080030080b600700400c2c0c0a40c2c00c1c0800368900c1c01004803212400703070301282c1a01c0c411807003441140300d251b03071340f401421540090000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 928612122 1250 928610872 928610897
    0x81608040206090a0e1e070503060f0d0206090a0e09120c060a0504170a0c11060a1209080d0e060a050a0c200f241803040b071109070f030c090e010501 66
    0x80361300000c0034024203010300780b07039080c0010000c051000c1058030100b42d105010004911034090410389118083c00340c9040c904005c504108a2280c012801c100c1c1d01000c2400412030380e80710701904001920074110b01c0c2d0ba01741400e5142901d840340b01340c03180d02c0d04001007140395051000420459004205800045600c4c1c46070303d803406038030708003010318010444041841500540d0004200742498000c034004003d00381042c0500c8001d101d0704012001040c100108040d89d14419807000000c20300800c6040d003058060004402076600000d038840d41c0c1c0c0d00c10380502882d1800b505c18203800c8035151500300b01444c1d21701c6000d4030a84106804e0980000c5040e000d008081081c00041c101c26411420740f1102e40c00b6002d01184498140380034040f0b1842c0800207806801c480c01c1d4001d8011030000150700741494814031449552111000b1501c40001003140c02e582e0325080c100c0d500510131030300d4924400d02250002005c135400b03e06a40100590390104002c0b6007002c154082c1551404e28080100d24030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 928613372 1250 928612122 928612129
    0xc011202040b030403050901120908030c0a050f0706090c0603090c0b0904020c01050a050924150d06180308060105120105040c05130909020a081609150302031b0108160804020609 78
    0x1403940a1001404000b08000030958044024184420240c8407034080d00c1082c0003810172030b00da080780200bd00508202080443c0c0c000d0300607101d01052880e080e443c2248158400c04107402400c41191225107030610074040080c00c0c03007140090883c42c030301000035402c1e50b201c007e10002640316580c3d40010000b00326000e0707102c07a01241e42c007140300c200a2101d400c005489030300828084469200714002da600c503107420032044030034ac071030980301450b004d807261141038050009800c4412090b41c841160f00350380d0001030050007a080400c041001340d04040c16242409000954000c1c034140c1084401c1000324405414801c0441c15034509688c00540c5500c0c034003041d5040d02c1a0403034040104a80c001c0007514407800c2d00400d824901c02d8414140d030a60352107000e99550003070019102102d444031001c0c454280c0b03a81c050070410504044110a0340d60340d03001f0a0408100710031065803085110340303032002940c101c904560000c40344420044040c54509000702042e03000740c402407044100040e02d0980e0758 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 928614622 1250 928613372 928613377
    0xc0203180d020d020918160b070602161208041b03030c030c05190609200a03031b020402030f071d3d0f140325030603050102130303021e0c011202 64
    0x1380c2c00b620380812403d0000d40c200e1141d250748504840351041c49411180040740290640840e030400d80320034103007074032550f88070065003041c1a03c0030b080000c1100e0700041070000381b1050924034240c80da40c0707640c2454140540741d1201a68103500502c1741c0c050400010707512500c4418150f0b01480c001c81040101e180c07950070311204011903200c0b54001c001d50000e11543e94400100948212944046286116240102100c0c0a92a203620085201c0c041000c80c1c051402c00101c4580b02031030254400d650f03400a81260015500703018075800580070040c0440d002419451042d1880070501060581000002d0110010340002000c20f0840b01064000001c0d0340c03800b005d0161110810101c071038a6403002049400b400d217842c00001c81c0b40c0c0500d0303440c0e068142124014a4074003294000000c001b105000d000d2440d10162080595071100000419070a202030702104d0307025a000300300c603403450800a08d040910412184d00c00004451428000310005942500913001c0c288154010483e00b50b02c0000e0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 928615872 1250 928614622 928614649
    0x2c090c060d27230309040515180603120f040f0308251104020708090d0b0601021011030a1d010c03020301051206070207090b060d0905070503010c0203180d02 69
    0x1220100c1c054541420039000709038100d00b18003030103800a1001ca000440d084290001400b607041028000d12101e407442001c0b0801d400c03020403203140480b54000700d401c68504446030300302c60403e070034910404c0c0b0b40311100314024603110140210500701040001d44508500390400800d400004198a405081c03005840080c0302c1026185a450b41d00d061004455110f910300600d8440c0c0348000c61503c00010004000c825007020b0f1501e140049501031200075480794409941c10107080c028252550344114480c1c0d100e5201d1422541c4900b46940060300c0e00c056490301102c0d01d0704100500e0b00340946a0180c981c0990000d01c085101051480304a030780329040d900e101607550901d4051441242c042e00114100e44091b279200c68000d91440034180c440c00103444401c0103802426080255070484d401034001c01e03800a1605203011954281c59045942e0700c40b00b110759400c40d62042020345001e03c0f45101d0250240040e500d843d41c42c1d0239070b4182440c22044541705011080195056444000c25104132 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 928617122 1250 928615872 928615879
    0xb060c1c111002041e06091e03060e07150c111e120102040e100b07030f050906040e1506030708010e10090c08060f0a050604050909011b11072c090c 65
    0x80340c44202e06540a0340c4540034680310803580003081a00c011a00c03c07810101e0b055a50f40f0300d01c85003031941010b074000c1c0c00c0300101c8103259041d5000c80402c05620030325564000c010b009000345403416100084e0740c009118081c0902845160310000300e1201111601886800c6422410740f126004085005c1da101120540e040503500156006028055001f07000742d608502e4030562030765508102e409828100d00501000340d50a000c4100000d000d1144070000c070950b804c0c11400c1051400104400d900942d00039140d0780200c2040c041d40f03011010b00c01d4800401964034500d0f51400340e81c041e00215041c4030309040070990300001a081111101e00030050000a4000d1140c00034007800204110310030b545141c850550200314034203614000d10b440b0219000a8001820546407804000c4113500080078001d40d9500c030802070030301c891105500c40000220741c6138524420092084a0714018544d0072800940304066601070409590741c00d04045080782802024050742c0303403441d090501900e98800c0d0741 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 928618372 1250 928617122 928617133
    0x3121b30040b07140a0c06050a1b0c0611090307030210020f0a060c0f030c020d052805040e010b0403020901030807110312030115140708070c0b0d0506040b060c1c11 72
    0x20400c00d400c07000d0007040c2c00e5035000c850b8608501c0031013482c45400c02e01c001040a00b100c075000200c07035400080d400b035a04600021140040c000d01e60031040580d90160014045914540802c1081e1040007923101d40500490305100c03280c1d012a6542c1002d0201a1044007142841e64030305100704400c04650350711406a8040111916060340130f41041074005d070101d80e40c142c42c0020588a407041c40740d4010700358024540c10462110980d004d5210703c0d2039820306e8030f00120304281c400e907501c100a00f0000e1680d40e181c0e00c0b071601c0603017540340708181c0100b070801d8000c004c2080503964660b00c0c1d9043d02e0304092243d68420f141d241008984200d491416058002c02821016600b842c1020b14100e540d4031100000301d2104c0682102c0840400e90000c0410406205140c080b0703096030090030415104250700444123480e0300c0d4052003500b00d0f0704031003142d60300c1c3c0c810010542803034040c60f43c50080c19503815040505980d41a0744451128100100740201074013200440351051615600140c2118240c92 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 928619622 1250 928618372 928618381
    0x6120507050f15130e0702061e060d1b0602010615020606010e01031b0c170a0c0b06040617010c0306141c29090105010f0509011215060803121b30 64
    0x8200b006588600c0700e41d001c5c0400024146030001c2002840345180c82140b90051841c0c03613036142150000740286800158010080000070440c160203c941410714150032506450b0010090079100560001126208181048052030b0340014440d50011000d00380f00c2c0c5a0448403004800030822140700b0368030110f1b0420b03420740d026000700b032102c243c600444180303d079851a01701402c0180301c3c60984c2800505e0821030000495000c024182d0095001040840d0b2580d6a480c04020b14042c0340303254856035500e5a51994441c0c0504c5043c1c001c109007640d41d0302c00c004500002e480342a500030822241461004510100031381d000900e50070300345141c900070258003041a5180e130300300110340c120007035803a12001240088008448004403207000700181c0c4030b6801c05903000d01500da007040c22900e10b40036045520741048a4040c90000e03200d100d005689442e03810001c80c01011000c2d2208198034000d0700c1e80b50413819060201c41500c0f03500020a02004c5100814800e10282486002c000c13144460a01 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 928620872 1250 928619622 928619647
    0x11e030b0f04020319020f0c03030709080f06010f06050313052d28061415090709080304170a0605270325050124060306120507050f15 59
    0xa90640d031054030705889210000060004a02c0140c0b8600503104003003c02c3c80741000c81341c00078503411801d0a003031403c01c180030b2031083c65038006031542004201860350034400c1450400c0044650416180180025494001c0d01000e80d403486c055642007010010001d09100401d1304840440c9074440c00315044040b141e55440c050301040c5d00e224140300c000b100f41c030b58640740004500c41e0440450320500c600b1ba0780034a01c1c054035159004229680e90300c884032a0603076415003082a01c01c500c0c2c501540c4010078480c00304801d00d00020940424080305c808203202100c000803e440a60324403540b01c3c81125a500d000754580800510001e041d207050004004101d60f040502c40c01104180d038200c072200400c1c0035510386030b00400010f46451300400d090001e02c43c20300301001d418680075800025001840da200480c0c10b0b100c4100e40a030b1503c0500081000700e0385840b80000502c0ca070440d010444166030b80f11504d0705001e00c6281d1041901c0980031240d40e407880f4106a12550862201d80d440341e1a0304d88 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 928622122 1250 928620872 928620881
    0x7141908090103050603191202010b1504050d1a0a0c121503080c01020418020a030c020f0a1e121701080705090c0307180f0504050a06030819050c011a0a0f0b040311011e03 75
    0x41c02300550900c5a40072490600c05400f1400c14103000a0505007070405081c40351104000000341c6804011040541034100c0d51100d10340240007140d008540f1006607840a4401000c0380c80c4050060b2510940c402250203040c011000d40381d01c03150f9070740d44080842d12180a4015074126001e0783c1e00ca0b510000c1c01e41c15907402407422144640781808882c00d0b440080c0c1c2c03211040c88a0780c54a80048940070001180000400d8480301d0400300c101d8081c0d22510b80c00c0c5514400088240421a0400414107260130703456980c1c010407030b6400900800c1d0900002c28864100036012401e6802c000c000316030201d02562040000480d1494800746495860310704c0f0306000c1151250034040c0d4605008501c201110f4010002a42e40294019117001c140465103401c5024018200040000601001c22011428020035a0307905603810603030079040311f540410003040400ea01201c0b0304e03044060700300b1085004006980440750841b010001004c28030005841a51041034092242c541a4400c100130a815510 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 928623372 1250 928622122 928622153
    0x40b0603101a1302040e13030201020f0711041407020a060506040921030507021603020d0201030e060c070507121a151f0f1d0d170714190809010305060319 68
    0x24054821031120201c4422403040b8086e100da04000310313001800d0700042c00d1310207108502c00c2c400107113001c80000c04c0d42c081d9049480201d0712030000701204e0345c4502e0640560402c2c12010440761360682000306c0e0195581001a0b0700070180350f11100043d0041c0d9640d0703c9000084d40140c050044208941683c1c3d604a40301c0105030042841e240c0480c00061002500390b0405281c400039000e00c500319000c11001d44075a11307040741090327250070303030781d0038040c0140007440c0201072001007039840f110140780c114140f4900ba000010003403621000c4501003440b10700d000e40c520440082040264036058540130301a9500c83c0b4403508801a0321b03003152419243c1901c01004095035441126003410948119a00341d080880425850001c040300d102601d8441c1c110001f5612840061207034003c08003c0300c0c081d0f00903107c16914039080c1c42e1903102d00a41440310030000c4000c2005003803c54003940e80c80c001d9010340030055041513543d02c00100d10351000c012075400c9080e00361340015140e603d4a4401601d40ca00395 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 928624622 1250 928623372 928623379
    0x30302120c03011d0403140d090c08010506011202090d0605190c0206271c0201060f03080a080106050f0d05040201090302181501020f061807051008011d0f040b0603101a 74
    0x40c1140325403540070044d02d0290394140d5405c401090324040460301358011a01010b10103984002e000005503244603200010001c8800104040c6020340016000001e281c21216066004000c404425500c03071700c035a11a154003a0b80000d00742c5504840b40800c20100d9044080c40386040c480b1844103800140c2a0320800111754410f1940111402908148600c0b09050010f5400181c0d001d41c414024800a20300318054400028120b039120f404110003001075000340d403008400900d5041c041d5000c0d0040d405000385050691908403c0c94041440c0e00c2084e02c603d044039505da0205045a120340c85c840c0c011a0010580c40c07010503440c424a03044001130f110810031840c80046603160703500110b103009116201070b01800c2c541d61071665083c1d00c074415060009081c040c0a00200e02a5940d01c1c00924442030b650301e6902941c1041429905c01003041e6a8070b1140300c1c13010403c845107031900780855016520012102440d00c980313002c0b03440d03c2d04d44441001c505050108094070240020700d411190030084 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 928625872 1250 928624622 928624649
    0x80c04050a0c0813290405010e0f060703020a022d0c090601051c060b04030b07080a0207121206091802030c0d030e1c061e05070306140d030302120c0301 67
    0x1c50203011206036140c2840410034020000e05035242c400070100409004040c2202c0609030354809a40c0402a40d001c4034520641c40140002d1020034860b101c44845118020911a50b2074008507a9600b00246a10708050700040d50080d403e20034080b01407001400505422800154031560071090310009040d840c2d8840c0c8081c000701c0d4030f810000580594810f031141c03803070584203201070b072203074691a2160f515043d2254000034006000b0b030001c0000b54000c00c2c5d4903e04c1d0a14480082c40440054600c402041c01480b44e40c0200c4c802100d405005c0c005810070054041041200700082c040c1580000c5000c0c0c40d00e017070301044040030709841c44894400c8003540c800103065030802004910005000d000101c442c000f141041c1084000782e00610380407903410304038906035941c1c3c0c03080c0e444d11104444100c4103850b600c610030103540a20303904030f0b4080c1024005541461a03010300303040c105c081a4811400c10030440c09041c00795040b0f400d20500c0740d510807014900b0780c4500c44598402e00c100001007904 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 928627122 1250 928625872 928625881
    0xe06281e020c0a121e03030504030206010807050a0b21040c14042003061c05010f06060e09041502040b07080910140405130b030f0c01020f0703050709050405120301080c0405 76
    0x209030000d565200900710040a410081441c80c183c3c20740c03008841c0c900c918000111301c020041c481710491032007982c0100301c616182c035000341031a4042e4005040c0d42d1000b0b205200640d28403403028180c80c0203415140d01c0e92005144501c02c0c41d440304441c2d03000c00407070040c4420300208540d22001e44542003100300c00c0001d007009000031261140803071026149100700994242078100b0007150000c400412a90032840c04031040701300d082d01d40500300d486a6554507031001d24445400380034000c2400d420802c000d80c508a0129070003031001400240165420058200c42c2c02407a41640c0113450300c10780e00e5031280114074003507103070f03500c001020f5202e10303042a508501c841c41100780c22a0980455402400c0610300802d0101031031002510801807900c0d640e146c0309035282005040182d2036240c00805806003c3d200190030004404000440764015071020320210701d0000d40c2501b1114844400986940e40c0e0820504005000404d2510700f040040006214a00040c081c0b00c0204115000c001c1d0b07848 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 928628372 1250 928627122 928627127
    0x1101060b04080304090c030605031e010c080906070e01180602030d05060d05120703210516031b180306020a0f1805100e0a03050609010c1803030e06281e 67
    0x2180b10b441c64540c8104400e0124400340d80119107042d10b50704011540300d44520000c1d0411000c503614100d9000c0305203044a03029024080c0401030041400d08502505107000c0d603c0e00d86500a1880c4107018107248d19a499034460420b00114407100801046080e85406009450f03a2103041b8482450303040c50007040042c5441c618190ba0540d01c44018850305c00b0800202c010358102503010f40a20485071039a0210701c516941001c0e00028083c40080d051030a02c1d140c81013601219415820035291000d020388070200380e140000040c40506191061300d5020030084004000707901300a04103400801c0c900701207600b02032002c491811070745a800040440414251501006200e00c581c4102c580d94000050360040d00f41aa0b580406070421004607200e489a62400c20141c0e81085669074035045482211b0b800800e14280404143c2840c000328990b441c000e14002c008040c8620810000444990b000e288001d800000300041c44c42c01000a10305901070b1650b607410340100c3c2e0400c0031504501c1d1952 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 928629622 1250 928628372 928628377
    0x50f07080601180b090a0207051c2a140c030f030f03070f0c2f150f2506050430140f040e10050d050d0f0c0605071101060b 54
    0x18254001006182e01e000003040b05400307200c03c00340e01141ea42c0354101031900c85500162080494010259540d540c42c50314500d0040345003014841359000040c03c01507a5884810407222507100801d2500401e142c44089051022854004041d01358910f1220341d10180400c40c0c0c04031041c118140c9040f0b10316100003640724418028441040c0000700001900f4502400c80f884040300c040ca041000440555520025050022203581001603850301c4051105001e080f44941b80c541981c141c000442419101c40d107a01401e000d00c92114404903031620301d00f03444154400c1800210580f620761455500341103008090640f030584440740005101d003541407881100418003030303400d100711400000d000c0c001c0f62143d042140c5450f40b10030421803440060001c001900280c905003000b00e4541c140031008041c0140d013a070143d40100200800c44021540224602c2c59416003401d00040340044580100c41ca0440c401000309160300d44000c0c4403a20768000c0380c0e040c1000794800200519511a40d0082050 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 928630872 1250 928629622 928629629
    0x80601080c130902060c01050103120507031b050114040b040c0603050402060d0b0a0503030703200d140f040302100f084005072408010308041e0b0d0207050f07 70
    0x81c0d1006071400c5040c1020981e14000d50b00100c40000d000806500180700c5900c80d180e03280311a91184014405d000c0c03003000d0600010650b0030300503e00b096559015002e44070f14551207070b00c0c1c03201140d0320302030190079004810352080c11000d01055107014a003150045400740c7d01a079525070003580102c0e00f54000e110b464090780e00200310b00c5c06e1944650f0200d010702040c1030103d420003e00341e00000c082c0c6040000c3c00e0018403d444002c01c115022044460400c51540302220380d610031416203c00c01d070407950a11a8041c680038944d69002c04101c200064456030b40300940000210008040d0b02d0740c028406042846169520003d6813210002071850420554199034421404008030200f0300017000c17a5003004601d00541c000c0c400e07040c1c43d014100422a4013a0f40e8004551a905d050000300c0440c450b6560068204120b0755415a220790005004601079100000220640701c1c00d00410a00d5240003080e0000c861940e80c2092112200650000c1c5000c0342c1500c9101030b2419017074408581d074401e8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 928632122 1250 928630872 928630889
    0x11b0b310b150f04051003060c0518060306010504150903050a060204050405150a1203170f101e0e0403110d050d1109060d0c110a050a0c060302090102121b0102031906080601 76
    0x3c000007008020b00014154500d02c103018000080000c566015000d0804040d44506031550000f0526450000400031003901ca62410020000342d61b8006003904d00b41c52507104c1c00001082000d105035608034140c1c1026185201e03500ca880100301641e00184145c0c0d905070303810f10039621382e000103000d015154040c6030340c4540c0b03007003050040f4411880580035080c000e1501510754500d014080701106410740d181d0303124500721000c0102c0b210741100200f00402401e00344d01c82040c0d5006d0000007103089401103041c0554203074045402e141c4031306a4109449000c5045c0e800000c3c1010380905181d01c8282030708815807e00f0280c4054160140c142c0d02401805040e8900e4990398800b000300416024440e402442558001c00d4000a010081d002c03900c0d20135001042901d0755403c041588800c0f41d071022007014010803404000d641e0128548502040f10030038107898054015452958294684185240b58404000c01c0145008285001400ba08280c401c0128903143d6210540310402402203000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 928633372 1250 928632122 928632139
    0x1c02060906040b0f0703110607080114210105100b09010c1b03051515040204150c020307080d05041409090304120804031703040c05011b0b310b15 64
    0x5410400020816400000c0041d442d19444954421403a04186401c0b03030110303c00300e1000b0406400c44100f042d01e80a0600815140c608094001c010500c140501108a98054607445090702c610000c0b01c1c911040d0b5030308110810060044d90f000740421a688045014802000503a040210003103508124060f500d8080050550310340c40e11030644450701d100781c02c218500000120310300740080f203442e0307070116801c24890919005110300c4040034000e130f6214900c1088100203800d4002c02e4800030a19504109401825500010f410644180d00601150141041e00d8801d04d80c4640240299280c0e1050000e03000b912801380100b00100b150016501c3c1d1017004280001e00d040a04c81008604c80ea28061500740c80b40c1d6065a03105410416488401010042c803040042c0d0f900c80d4406810286012448542c4100803c080100044c5010702030913041c902054000c03074100f0b5070711600380c142204090306c00c0142021440154940340c007601e80014420101d02120a140080d00e42c40b180100903e9 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 928634622 1250 928633372 928633429
    0x90207060f1a010f090b250204140411010e09011205010906052e03031709101a0439030209040e03091806010c060f0209100305060a051206130203070f0f0311 69
    0x410741e9020394081f88000c000740001c040182d840380618240840d41042400e511305203407074258a9800060004d6048c40b2009244c242c25455a94846044500d102c50448401d461410103e004010102c8060301d21781c100003c010b050460b0450740404220041050030a60502988503060040c207400b0040000e4181c1c68815042a119103049800c040c080081e5520501d4400700001202c00018030501c0c80e21500c80781240d1440c140c401d8000b110000040c00e2045041c86007100c00c948d82d090510301984000c40c0310084030a100f581038410ba181c000c0d004100c0b1580030300310165250045031166115802c8104131a02c1d900806142501802c4103071161803e904041d940d29000c1c100b00076140800981c2801901c16a9640d44402d02c8071114607180000c15041a1b024000e007641c983d008280102c0040300341607a080000683c040e0310101e1102c00818041c220f10009051003000c2e44061100c4ca5103060120300ba085420540c000c691083c039074980100720500910035002001b100c01c1c40380020540a45 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 928635872 1250 928634622 928634647
    0x5120c031c090b0403030201060f15021203100e0a20130e07210618060308031504150b030f0115020a15060f060509040f0501050901090207060f1a010f090b 68
    0x80c441c100340d42021120161160400406504140e00940050703460314030420408108203d40b1000d4140440c650b280c02e034200341c1c060b65940031020310381a03d03040080003c0c4600440c43e81000070700401c1000d4000d03800d08001e00c1028106125169109040c3d00c0c504489400f030f640c0440e001d02464810b11041189043c0d40c42e101c03408010105800c1c8241d20907000310104003a40d9980d0320344075460002441d1820145032440003086001000b9020b413616a06001080c0340c201500e1780084107680d03101e04180340c0c0001c1005040403440000850040240100e04c1d002c5030b1010354851600030381020216aa07814031072082c0d4070b803014584056044a154000491a001038091b40e11801810100d4142e6954046080c2c0c90384030b5101400003100410075400c2843d050181408040c9030590500a5504000c0000d0500300180700d83c8034a254000360680030840240c000c2c54072200d501c482045981d000c05c0c450080d0b0300c007800e80386d400601d0081c00060b03101e004085400685a010b04040d013040f4944210 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 928637122 1250 928635872 928635913
    0x31b03022a12120f0a0e071406090402070b01140303030f0a0c11070b070525050127090203150a14010f0c2907081306230c0405120c03 59
    0x7150424042d000704480c81d405024014056150a108100390341d107050f980005055002411102082d414107424201281d0000b8841c402d88503400c2c0c50b480c0c01c03414031002980e03a204a280c016000b900104004050005603544581281d11162041d041150000205912440105c400c1d603080740040010038119546ca81c480000b50410b420070300c1500041c05000c1d4030b0070030b00364084541c0550001c0e89408115003408801d00d4044416407013203429130a4203040c28054820f004140c10800700d07151101288903412500244000021142d40ba59a1036a0590001e540304450000e69004140300c600c25a040c54480e000032142146007c01082c24030100445008080a04120030002c5452002c00451960340003184050105c003d90a40824490181065444000c014005000140082001d12308a521b166403000f5440400018000b41c1c04c04002d640314000405020160516400c010703499110000520a03900d0445031000300302c4210001c0c80da55500d0f81c0005404d6001500c0c11440c40c10801c44 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 928638372 1250 928637122 928637197
    0x1205040809181e150609030709050a060f0509070824060c0d090f030c03030c03050c06040507030339050a0803100603060f06021f060b0a031b0302 64
    0xe20520707010000d4001000d420340a049101d800904805001c0b001e0504500d034032031096030b8180880c0324a031000d00c140c4903004030081d40c0d014640000380c0d20306d1603506100040182113420703410000e80c04d01d808054020680b40c0643c144102d05580c5c0490149000300c1800d220340d20b01e949425050f41d503003006616174999070050010310300345c00e043c450a95440308040c00f582050080101402000c000e030003040d6003055031142c03916980100050000c629011072090940e034140c103000700743e0703142482c048505200d510b443c0700a070300519052000b04007001c1a030a04580c000c5d940d00304580409540041003076140034154001c403982201200a400303521002442d424003030019941061002d0312601c9040e40100d440034843d2643c4c58061141c60b0301485613101910620540320307422401c250001c0d40c1c558498418146084100b002e09d07007102d6154110002030180389040d59215400307c40041c01610b1400569908074078080c1540d140f9520030300c29070394290312440104158502400c440842130044c0c01c1c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 928639622 1250 928638372 928638383
    0x4090b07180b04061701090e06311112070602100e010e060403090306050a1e02070204060b04090f110a1e090b120612010b09011a0c0a30120504 63
    0x344002010b8000102802c024074451300c6407040744410306942d0103000c1c016000661603a20b01004400624000075034541d1148110703000034610174001d100001002260080758111044440c4900100018003904188011080c0c2d1500c0750b60070040c1d4210745070b84140c001c00d00142e0083c07039030b20f21050b21303604400580710201000140c00f0180700e0b000c2d41085000c64003075000c908030000c10010030602d441000e900240d0b540080050281004911100e50f0009000c00350498001c02e003a0255605c9601103c01040c0000c0381c150768580d40da0303510000c0c0c0182181e80c07010340d2409000840c590164012a015081d150b07032650084407404e401c0d03c440c00c2099000208010201a000c00c016101000410b400c80828000c01000d152400401003100c0380c41b0031450f2142d0410711044d0342900c907030303105905548241d11480c20618900801c0401d5010304515a030144c0b25a00f0150180220f49000d444140b204a11301114a11540418100e40c1a1007040d100001c0302d64461303014082c038980c8401c5d0000e100b50b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 928640872 1250 928639622 928639667
    0x23060f100f0c1401200304020a0e0c1204030f021b060d0e1504051c0516080903010f050f040506010b0f0a0807030f02120105040f060e16020c130b090604090b07 70
    0x142c49402400c001e240360f450040c3e569400340e5000003501d04007030b84019500b1079214507600d066400b1034101c0c4114450007101500810114502044403400c0c1d81c0b080801000186070380c54036003401001c006c1405802005070089004808642603240e1008590a0016081d04c0c9400d0070742c0d00031402042200240d0f111406460030606032003c05082850086001c0d100410346100a948450a072000018810003032280400607080c860b64800e400c0d408141c0c00c41007003a2203495a101107805000c510301c404041c907180c0020070102015001100d80100d006d001214800d0380c0b25180360805108600c2450324620701407001c14002c030710680000398000d00710b02c1d0101c2c18448c42c0355400140e07001920180c940e4082c0c0d40040c40310341030a115020300c210a900003400729502d04003d904d038484019281210552050b0009826280204003c00b0749032009000c60b4103500700034814030014481540c600e4800c4140d07601145561a241c02400d0600b0340040e208030700d0781c0b2128070969818182e6000e590721424507 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 928642122 1250 928640872 928640897
    0x20c0114010f051e28030507141c05190b04120302031b0c0c060d020a14031003200a0f030308011203051204020307030b07030e010608120307080c04050423060f100f 72
    0x610104044040614000d505c0c60303007140f8100c3d080002c00d0f0441c041d1b0440c00c0c1c0380c4040c2c2d03940f502c485020520f400700410703040340c020b410710b582003200c0c0e800155800c8400048550030001030b005241e12460041907110500603000008505134802a220b4505c04003907041c1c0721480c025410000c0c1a14646caa003200ea403c640140864032507085007c0540400e039002c190300c8401600049020408120004c03441d15503d021000b400602d1040e00025140141350305460351150340c11450900c0d51800205402c1c0070b503031307a2046100c4640e05400201c00085001000003003440031200c0704411154180c442600b0490300942103014176200030f0050703a047c81603080000118500c09580d0b800744200d13507004654100c00804080c00c0da100f5920089443d0b015010300108051203106581e0400f0f80761400010f2178481c40741380c018501958010070340c4a8500101080790591030240360440041146c6580f109668120411404050180c101904110241e003280b000502c101d1803003e13a010f40d03080c262400c154 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 928643372 1250 928642122 928642159
    0xd082506090f030206060409080d020c030f19020f1906110d05091606090b040303082703130b09030c15120103060e0601120309120303090204020c0114010f051e 70
    0x207a410301030702ca2009202e4114181030703050110543c020002d441c00d000210f0b0f42d56408519101f90405086055408074485010510900c101d400305a21218200c4d100e40346140311030108103031000c9001c0584035902100d0540394002c120684040103585000c0d07042c0302c0546036400a807100c0c5000c1221070004209110000503c0d1089034020705000c001400048141980e109181496030801340501906481c00c00080c2d2201084030f007a2a4145015511500c60814160038130303001c2c0070941441c003411588079031b54900c0003010b89401903000a01100c0580d81c0c1c120342820748107242c5540d405401420414900f800c24000818200c04200031103481c01c071075502c80c0007000c5000e802c03c0b07660b00d499400c070040049041100e24090206880480280d0400e035070040c1c92001035104421803840e25100c0c0d40107140c003d07400490100c1c2c02410079540c5401c41d1161754020103600c60b5080101c006176002158400c8403d009400b51440540070a944480c0c0000c11441740d0183c41600d50b0200400b12142e07400907 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 928644622 1250 928643372 928643381
    0x112020708070c1e1a070c03080c0f070b0906120907270615050703030b03030f0a080601080705040f0b0f0c120c190b040210030e0d050a0e0d082506 65
    0x103008482c503460342ca082c100150845584107201300c120307980b03280050010b108400d00041554000000e1296562928900400b25812a91000c0d00074040400c0c14030b5105400300d0030288408483c41a903c125880382d90102d454062600c0042d00700c0014842d03401d21070f100c800100d810000610032100c400e07a80d566211100c82d955840c00d88440610411001c90100c0360142c4805001403400413100b1400d5030500510900a1180c080c003016110703008016140c60610449800c00d1101e01c085540e83c0c818440649102815200940003644400000d0a514032490a8409450007001032220051408020207203581102a1103401c8400401605e40e82c80f10401803101c1e000b9030105c80a407101000781c10541041c01000f180c01422540c9031805000440c2280000c0e407095044031502401c444100088000300600a031190484c071a10a03425000c030b40000141407500d00300c1d994043c54181c8041805058100035070b00510301c0c84248005296040e20340002110507201e124410351000300d81c4c80340d00a48 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 928645872 1250 928644622 928644637
    0x402030c070606050406030215031b0a08090d450e041203060503030f0c1005040b1008011b0c05030c030f0d0b060901021b010c020915040c08090c0112020708 69
    0x3000622881003080d1400f40000421040b02c081000030314540100d11400001c0c0010503290400000056405011001043d50504d0000303401c0d8844441c2030001d80003600540301c0b10014822505200b5030305108100d03a50741c07020202c0d42c000418102000c0000540200303c0961002000340100c5c008100c07551941c1d90041c880088404858241801e040f0f01e004803003c9424101810480240403981700003044a0000c41c00301c0c0040da03680644030711241400d006880d900041c07800e020a010520182400d4140503400c034500c0d00480176500d44103282221b0310502943c1e40c014000c402c0c07204442c010305c1101d00c400d010f90261307450200301c00513250075030384040150590600d003c2020f005501451054211511007134500d285018070400020355a41890745015007040d005185042d420791242d12150040c1c0d50241130f02c07816080ca600501d52201c0304814141c01585010300c1000c0c60b41c4540581030080792050060402800300000450b9012103851000c1900c1d40c080006e840081c00d440c0040c07029 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 928647122 1250 928645872 928645891
    0x60609010c23240f09030406181e081216060911090a0f20030a050703021b1f062405040f0603020c1203010515030a2013120308010302010f020c040203 66
    0x705240816841410030060311300340342100c0c0c040400140d09030000440301a40e05509109640012104204410305e1298009003000c0c1448001c4a40400790300703042c1002c3d01c802005a403140c081255a000752801004503440c6064201c452440204195502c8034421500031010964138010040214001c01c000f541d80c80f182907039440306000711505e9403041c11700380e0041c0480c444c01e10a03007581410b180c0c08003902182140307a65402148401d4041d80c101e809201100c1d6442c4a06440b41c011651190000c140c01811130818117141341070400345104100a89080d034018080c00300c012400308224600007207018052000c01c00000c42d81e805103901480041c14541e80142e80c4100003032000d41820411510384407044000e00052004e550380c0c01e404200c01c0c1d581c2401c162030f0307500c510b5400042e000400c44160700c0308100c0f42507440d00c0300240041c00256008058204d41c1c036551849641007104400001c0d00080414005000542c071401003040e4610701841266843d44a0400050032a0f0040d01c09025 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 928648372 1250 928647122 928647163
    0x12190e03070302010606180b0307090312030b0f0609030d050d2301080c09071413090606081807030f08071b061101270602070f0614040209060609010c23 67
    0x101a4240205001b401c0c0c140340000b000c511075002074400b507500b409000c00c1c00c84040f0020f00c140c5c0c49541c030940150740000b80400041d0b1034100140c0103101a0200310b000d1032000310f02c072400c0e04200c0100d40d190710703020340142411b600b0174104594903044500401e085507101c51442c2d02d02d40a501034080751103004040b4410320b51410801c5440c01ca149003182e40100c1003a0204010741d0380005c0c1d072710705403031a0301e100503954001a91241d54441c610742107205a58601b94001c00e95503880110f1510402d4240540b80130b607440303030000c603070743d080c03684001403440d0f5800340d02c0c5000800e4403001c0c4c140c3c1441040e00040c0595402036189104485420040010704d010202c191800005d001d00c2c0054031040d8507408803407407515055080540c403240b010305000d400040364400c2010110008661740e40001c0c0410640c85c03080c100141c003c0c0b003900c099100340c12023000700c0c5492821078210342c80c1ca00c058480580702086542e43d0340781c00205008090300c0080707109064100c40c000b030020b041c40c00c1c191140e112 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 928649622 1250 928648372 928648387
    0x2307060305070309111903050615010e01020a0b06060d0b09041101140a0e120f0f030405181e060a1706040b130506071206050406120506010b030c12190e03 68
    0x9003181d00081c2a41e082505040200d008514038554041d100d040503289402112064014240c3d00107060340000d105208010070030080303c030451442c0c0c0000030242c0c0c5480401407500700481c0c3d02e14a070030000c1c04015404000c1403280c0b92502c001d0007101c00b8000044ac40b51112400600d51903421942601c41284540f18845590f0348154941000685181300b28200b481a80c070007040c0810050680c0d0241c42c05650350950080308204000f50145020700720340c03400d00405180b507120b40061144c1802074501d0108180100e00c2601294464101d402c02441c10841843c4680c641110291041d03400061188011808840c201840040e000c0348a0041c1000d05191514860821340140380c06030207051003c1c13000002c3c1000c0b81c1907403c243ea41c60000000708400240c030005142d590300c11a403191800d000050b0010156000151041c040e03810343d12243e0b0f843c03600201e180b004844a401d4000200900d104a855002c1550703005201801c0d1041c0b000400c01a01045402c510b080c075038568000b16540 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 928650872 1250 928649622 928649627
    0x1602280215131a0426160f080703030e0f12060106020a0201110c010e011809180b18060118020705010203131b030506220b04031d060405130207230706 66
    0x10007400e901488480000c1c0f402d150f8411805580118081d0348898050440f54403004040b03208040103003010340d100744144104520304400e0500c00c000007404102400149240d0224a050880c0d425071281c82002c1c04180070010140302c1d5000c1c1d00e50000600d010151894002c1205a01900c250740003822010b80324000908100880c8440c0c107400d42c0700101e41e2100c2d13613019160710308a1320207091440c0d4407010080e90002080303060700003161941c030309000c0041c05400c1d9030051845030302641c42000181c03104c1c0d45404517040c0c043d014205070350006004115104508820040d100c1c403030360006084c01d0322030b902c5908be80e0040d6000c0641e1050620040309100210107101e0407814504c4100400510715901c16444010051285180c10060484a410804840044942e980e88104a18450314044c80c0c058010105042c01442c0c04000c0500801c00341084000c0310245e900060581d46111482c0720b8480c060b40c0210b10868601d03d416184000540e1048851a02c0032807840281c07804900300780c0d00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 928652122 1250 928650872 928650907
    0x80907051210091406040809040f0b0a140d150209010e1801030605130b07030906051b0d05040309180b011d013c0905091602280215 58
    0x554032400282400500e00003002840441241e8610700c0814400c02c01c0c1044109805000b2503211389020300c070300308001c200c8800002c01160720300721010400701d1036078401342080700c4070408855000300008400740000c004142003071604c000014808418194940c2d14070b003022140c075046110103500400c640c0b082c0c1da0002c05c03085840304188c4640c180d03020048800e441c0444180303c0940a42d9807007010440b10359010080301d00c1580c0007071100349182008000200103050314203043e12000c1c60300011030f025842480600d4054144082c80d03504045c0d1010614000705800341c004c07828812070700400141c1c540340e42c5140e00d42c2041002c0c0003030341c50f445c1c40024000c402d40101104064007681540c10b001ea0300440e03241010703041d449103119031b844d071701200c9004541c21298411f22600240402e94080d981300242500303030f5006a403018010b40b81d8141000300c1e032401c29207103c0581c03c42c0d0081c2c088400018a1000e4282c00641109a5101c2c150007003116598604c04140c03031800005201c1070600b04600d913 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 928653372 1250 928652122 928652129
    0xf060f0e0f150f06180103050a0501080a140c040606080a050906071e0e04020d0b180c0316032c06100302100e0301020d020310030c08030306130c120507080907 70
    0x60410440c54261101c01c89034000400c24200100d60140c004020f0f120203074000c025800142529035034a91005000f120344d8511007000f40041e04040c001214a50070f40107090403110320000400c10040e0913070705c1032566000c101d8010a5880360700f400540503035032401014007c11040d21461a141000102c410039a10010030341c004c668070a00501c511264000c1c070483d0f007140702140902d601e01c03c9000407110300303110000440d4042d0011889070345040c040e13032000710748140c00c07100c0f040e010034074503569440d0705803c854000d4010814030024004010f5018400d21440031407030002140082002009507001030000b07e160080101c00324219410400c00c9144c0c1c002d803c074132a85802c0307444c5a0016008500441210003042904a901c001c162025010740d040e50f000d5030700a644070710300104241d1756030040d0300c010344035800d540000081e40c04010041b81c0c00343c000940b072400c1c8d200300000440042c0c21740a061300b040059514410b04101154030030075000e030309956241102030510000302860144281c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 928654622 1250 928653372 928653389
    0x1030e1207051b09060904050a21090f031203150305070b1812070317040824070801030b0103061109060d0606080709123002010b01120b06070212100f060f 68
    0x2001984d441c1c500a0f540a50103c400c0445941c9928040c1d040115040004050044040e418400b00c440007003280d000a01990b40c06080c903540e204411950280c42c80302801130034900802890041c070039044259080e8030300403403038505e1380c1c0c82da150345c075244240d071000341c2c038100102c3c00003210001e51186104002003100c3d0280c00003c0b03801120384814203444002d01900c0031001100700009100160f030002e09110059034041d6450781554034051402e21306103502e2041b6a40022038542c06655420b0503039401c01c074010103c1c1e0842c2d441034002d0144c0c40c64024a10801d11101010f540c901005201341810113501140c0340b0f01e0301c040a8010301029002d481404610f000c1488500404540441465001a40c040c0000008000224203014280d140022460680c082c2c01c0c45540540201a0200003030381d442a104a80c68a14400c807013a10710b0040d8410000c0003284003500c0c11042e6103000c1203041040d10010011745a5003011102103011061010f0f860300303410001c3d008480d614500400584 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 928655872 1250 928654622 928654663
    0x1608030d0605090403050306040c110f030301080d020105250905100507050105061c111f0203070309050406061b06060b0c010c0e040c09060f09120b010816080d050901030e120705 78
    0x17980c015105000007000680155912a4079034034103803007a40c140c0b4581d41800309403501c00d6141240c4680302e87c000d0240b291907201d56440018030743d1051040600c903a81c1d26100c0e000d950030540f072a8031281e0b59038114404100c0000e001280c02e0381c40000c98401c02e00300da00e40a680c1c0c545441e140d070035180010039880c030560400f400c1c1c040b824640c084044a8551100c00fa000d40c0002c04001520007280044105441d0304200048030300c0c03500040140b1003280252580c0c2c030b0f02035445040006a075007500401c0c0020f5400c59401d00720b58001071401c1003403445484086040d03a00c1d440d0100307098001885086aaa4642c0e0321984420b4011401305213146042d241030109442442d4081d200d2a014442e650030400f0102282c2c0b0010300c2942280f01400201d0384070301c800683c0e41881095000280038a0f2083d0094a07180000005540d40b14008c580121000c1c0c11904280e80e801c0d01d07035401c2201c00a0502d0784524540581800910145039100f0198903841d03181c00060400915004c40b040e1404c1c00a00782 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 928657122 1250 928655872 928655881
    0x90b03070503090f0105090c0d0212060403020c130506151b0d02010b100e060f0309070306090302010507030b031f020d110409050417120105240c0708060a0c080606070201021608030d060509 83
    0x8110b52381040c5064a0380b007c5020244081000d01c0d131a10014601c42c05018140b00405501003004002030380b0403124441c6a20440302c94404071070080c2c074000c0d4401510003103522540d07250409002c100c200c10740c01c1c110713007505010114280f10700e110503040185d40da0303400408140341482c800d0302061300da4030304001d4000c80d00300400d145202e180040742d07000001100040001608004000c06541e0001c2d0a0080d00d00381d14000e8040c10f07050384c50402180c00c0a601c1540390038009408030308000300002120445040f10141402944507441040c01c840c2c03610350400040d03140200400c000c02884c400060249000d0a068403102442200e101c60584100458919018030104882c156103040380c904001055a80010303800128050040c44244404209140100e1000c202542141e903c02c084d96060340d46c00d400c58082361021160750380480d40c4400070400d40d0400768007030b090492040c01200c60b500000c8181180311203840c2e012040d203600014084420f01e41c2406945c00400042d50030400c642403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 928658372 1250 928657122 928657141
    0x1b090605060403020d081306030e0615030c01030b030c0d080c010506030a0c031e02041e0506270c160b011505070b1f2606091c0807090b03070503090f0105 68
    0x160f40302c040e200f107203040794580034015414111014140c00c51050a800c81e628a8040c0c040d0440d1030840c4241d001d006e001450b0000603285103526a81c0c018060f14500380754038019002480b01282d41600f5100e1080600699103580d1080c004260054100a44500c284200030b030a440c0300501c1903029801c4101e0764400501280292001d80381e00034529520038448110114854654840196100382403010503280081465007401d080d407421a070620566590000f400640010388032207030b425060100341d1611341c1c0000c4000f140c0112540301c3c400d183c10890074000c9400f001420702510352000b0340004109a400d1031682c01c5500743e583c24010308189041c0c4650707680303035001000c094014a110041c0c030048035203c031164000d48a1582c1d820019925100500400300840d21200b10903c10318000c074000c00d0001407040441102c20314a1400c1c0d000800c411201c1e10800381280d001d0041c1e440010400300c1060018502c683d03085c2c0d440c00d41b20301c0c0590016141c13030000c1e29100c0540c1d1604051061044 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 928659622 1250 928658372 928658377
    0x90f0301060819050102130306021c1e0c09090c0807081b07061d0a03080603150c030403051b06130320120c0c0603010906260601121505041b09060506 66
    0x700d40f10290a00d42da00c2d400c0450192243e0400ca00542c0f0b4820400300030402c5a1b8060007030800c2c0700140b0303c0100201160355003140c02d511303080e0b420f08944540c02d10001545400005040100b40f40140700e40343e440c04180299160024a100807401c018101b12415a00c40d42c100e03030080001900040c1e130f512010410105201d002006414203071a8004018440101550b000120740f840c42183d071514803508006218080550b5002d10900581001842400d41030303c04a01030075401450500d540c43c4c641d0141e900c1e80c010000901c41d4240381c201051140782c14040544220b071040a08c914030300592400902d0004c3c4e036188001250341d14100c02d11018000a42ca0300c1c1c40d07504a00c000d035240040301125251584804450f503201000100101c1c0f06504d54001400b102c14065540925030350002c00310b806903030018002402c981c0200010041d1014401e0050b1038107000e03c4281903210125207091043d110211010364411444000400f582020100075400510701600304000280c00c201c001190352 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 928660872 1250 928659622 928659643
    0x50c0403080d0b0117041a070906170901090c0b0c1c050324060c0c040c02031e0a0905120321130807020a0e131a070e04240803090f03010608 62
    0x1c56a40584070f001d039001e2010601da078680144070305202d281c54a4041c61000700440c082d0034001103440400c0380c240c010007a100560b403050702d07407200d544294082042c021000501804096498201090200c4c10190100c00a070113001401c5941d03141001c9a43d28002071445070728107500358070301d22066090b84a0140d0303800c014688404031030031403030211ba04045200c0520659122100081e10342040e00b0000b6a1803a450050b5000d0107239410108040e42c581c0038170344280700800000040c074090203003118020700f5140428240081442d0300c90010860011402d00280703016400002c120f0720400c0d503074208101c1b14030300c005200085e02d4026800d1418941ca014018040d00001c12480215030301c03203451401400ba0501741c44080e20b03020014144006d0b2981081d50940220031440c004581e81d0040144601c1568039040b801d003001c8418031001348040d10031030f48154200c903403019500907052412001050010001c584480e86e420030491401c1540f1030b02440b0760701d0300707500f00407140000c41c0503401c8 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 928662122 1250 928660872 928660897
    0x16080c0913050703020303031003061401050a031412070303051f052101020912150a060b09090604020c010c05030114090f040b040203150f16050a080103080c01091704030204050c040308 81
    0x400750320720b8814034081c05500029814003003c010002081c0340c0000502c1241e01034507062000c2c0f286d04500b04540071080c01481d800044400c0d0510124503100c4c082085c0d03803200022aa980001644c0701803607038102c0c0404500113902d600900c01d80d480300301140303101030010800404d0083d1400e030024108160403c45841d0810050004d07800b1000d00394107031010800d01401004000222070a1907841d034811401034414040c6150101711000014030030b600a480100f030308145020707000410812000d80c000c001e554011307001c12203250380000038004d01190a00903120700d0380342d504041c40006220900710f040f0b1f0050440c20204551000700000ca26001a001448070000b92568000b2074180084664000340010300d82090287d02c050b4140715501c00c1030b0700b200d5124002d0410008541d5031041058100c0098240401440850100e00c018041c0710480000000c0e038003055900c81034030307000102c03409598030b1000c0f600f0401d504040c05003591154000e44e0b441d2426040d0365070881140071720b5101242 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 928663372 1250 928662122 928662151
    0x250207090c0e041802031225231e15130812090604060f020304050c0f030f1902040f061802030c070c141002060c0a1d0d0516080c09 58
    0x70741c501820040c100b485010700107200400410302c0c0c051203400c850500702e009200ea910441c041c01c010206998115000c458078081c10b4402181c0c101041b000041d00b41c42103141c03151805800e102514000c50080b030f109003d07090b0384520b01001912440900d449403540e4100254200c40c3c50352848050b0b900441c00c1010150015003414032000501690080c84801550308090000c1e902e0300182040c495072051505000000c4210030f00010390000381e60040690b804800340d8212032402d8070310364601800203011a102c420002882c02c0c40c008110710000e4040703050701490310a508040c00341e04085050540c090144e00e18201d80340035a0a2100707101c03c01c05a010020030701000c001000c81d0185600150b034500803a49440b0340f2001c0300d01584020b48501c4001c903040300200d0021500074481c119030304050b42810034a0000342c4003845461025029210742c41e0820011b680d42100d0011407074000e4008000c0d800e20115160307c2011140c002d952154800701540100d0303035940c484190302c091403600c40d95 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 928664622 1250 928663372 928663391
    0x20103240e1f0308121e010303050a0309062903070605090d03031e020306040b0a0501020d1b0f08040806070201020405060327070e0a0b0409050c06090111060106050325020709 77
    0x51461400c2c1d402521003808080e00205000316a80908002c40d203401c4000801d0b00e40c4214070208851610b81ca06c1490603d10040011034007440140c0b00a40e25800c010905045a5070750b4001c48024101103040307844030301c1101d42408907901080b103400c4410781c000c1040c1c0342030410240503170164502d0706104042d0030040404251094210001c0a0039a68484c04a0380d10f41c0d08481c0650030494082c2d00a034a040704c0c0304a203140040c9243c0840e601a00074000d0f1109110085401450011010203060160514800001d002c9604954a280183c0206031075500308000a030920704058446411a80180024001650303042e044039000301c1e080307070700b15080b2020542840f05e205040450001e18041d140e0f001883c03180020245100301002c20301001000c034803000300412121011006441030b48a843c0c0070300a070510400411000005040c0740c900115880610391414509810600000b10040180b00f1a41d0401c41400030000000340345030105225541d000b903a8400743d1040b241c000780c40d010104c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 928665872 1250 928664622 928664641
    0x61215092d0b1005090a0302010503070309050a0602030a05060618010f09091503031e1403040516330c03180801020c07050a0506070f140309090a0504020103240e 71
    0x4044079844800461200c000302010240200000c40c452802405041400d54900f84600d04441260304024119100c4a0558004580c9500700a01100a0599510501000c42c1b81007219038800d6200300e80140c3d580c0750101800085d0b40020340400e00a240500540700703c00c1192076a000108400c0c03812907903c002200d0121030341029503100401039481d1031448105034407c00301400a41e4001e40703442650480240340c03001c020754031480080c00981c00000281c4270b0b50020006542023406403040768608130b060307503c4020740380345036010503940354080760030341040e4074081c013920001001030400c0030403407030201005040104040c07801010000c2928400b60410310300d0505201a04101000f103403a5032100300340e6541c400d414001c1a02c00c170b035009030004440c60070108450f80258801c0d83c8254020381c0341d6400051007103142030024540414403051945440b584c250501c43c2901c02404500d0341090700003d001c85e000110f000c0385032941003103641c0c0c030601e4a82984c0111807050340d100312147e07a0342101 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 928667122 1250 928665872 928665911
    0xb0f07080d0213090b2103040b070c0b0301080607030e030f030601050a121b0809010b01020d0f020f10091a0f15030109050607020304030507060207120204020f070b010b0406121509 79
    0xe0ba43c99030300f003903001315145041d0b0380308a40404081c0d41ea1000008021802400001c0050080d1550b6008110500520076000e0151958921035000007501940720001600190000d070030111080c0c0c0040704000182e41e0600032175440403019800340d807801038090442039403403000520090601000040c4bd640c2c4520903100c441365042c5840b010481035074030740a4001c3d0242420304500c0040d0086010400001041c03040029400050f0020712000d0b8011500b40c4a0200031102e0b0000e41c0100280112408000d1101d00079910341030a00241d920303072514005001885800322031203006130324010040365200038450103801c01c50701e072441e424016041000a000d801c60100040150003048240000c1607000800783c02901e10440a0316a040c1c0c607010120392307503050b070701c101444085c0351847c510150a00380d000f8100d84c00303010266480c061894071621001c41082c1d000c1c142610000800300151517000c00120400001d031030051102d190f14000c071441c003c4560240c0451680d60f5113180351302402140c01e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 928668372 1250 928667122 928667137
    0x160804121803050d0f17072f030a1b02030c0103020d0e01090b07080906100306021e2d04240908120408010c090302101110021605070b0f07080d02 64
    0x1041480c0780e100c0c41c1c41912404140e02c1032010881e070424100d040e602951401c242c1d6030342250880c0c055075884000302d61111004003004440d400c801807440f1030010030031820300c10b0340741d460086588881e0f644009080e000708502e00c4a02c480d00c20030103001a600407901001d10380e802d00c0c0140e00c441c41034111000a10160003040019031030107102c40100903c403150103200321425107500005503103e0301030649400c000c85000c1d90030100b00700248009041c80e07002d0310348006508a0106034a4a10f6165141d660040d13a0000135131000c00d803551008a034031034030001c81c030f0142e07207280f4205403402c408131580e0590503080305c92495884205c0d4160900c50220000142001012100c0b030840e0945040e4443d44640943c1006500f018a09103003070b40540311290450380d02800e01c0310b0745030f0404012100d00c000049404040d0041505000c0d186130140003602452086c0078000c091034a151601500d84034042d880002c4c0722009000d08401041d00805844400d504088041e55035811030704140c0c020f1180d0314 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 928669622 1250 928668372 928668407
    0x30a0f1104120204060b12040b040528060507020c03030a03020d0f1d0c0d1a071103130f050f0d03121413051b0f0f030a050d0f0816080412 61
    0x34000b0b8400d55410320000168000d60301002582d4440c02100103a100d602e006003182169031011400040c0c01000c500d074050301840a139a0014800036000307086520b12040d80222910074008041440510b1140540050031350008202c04585140445c1e100d003d00c1030344003741a0302080c400c0600c0c5e0140c0101c580020444010000300c10550010300c45c1c0c030400c403c5110140708000c00030710381d410044940304500d80c1017081000d00c81c45282044515030402454034040000e10f509207074800004001510704041120402911340381007443c400e4810788160700c1144108a5a80742000c00d8503403180e08903411740c00d450550480c19000c0c10304e0020b031000a0711030a081440c2010032000c400010fa01d400801c0c443d4050b03844c00311014100e214a800c841300e62590284c8494488900c0c1c1c90048641d41e0503250107010f40d080480180c0350207050030042c1c814480815110343d10245040d80c0480c040b0f44c4903180c0c0012040c10030241c9002004840e0041c4010028048143c1404000e400351031141c00481400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 928670872 1250 928669622 928669627
    0xc0a0c0c060c0c120201020601050d061e0203061003060e06090709080a111003051509100803070b0f0702070308271c11120309091509040303050402010909050903030a0f11 75
    0x1103200602d25142c901c0700381e4901000c40000b00d49202c8601484c000b094050b80280b1842e420071082240c208000c0200f140c40316520b11205600c035480120004403483e408100580340c1c5800428402e03420451302c2c0352030415181400601207030410100c42c6403c9101076170b04402d981d4074840d00391200d0100b03400040c07552042c00441000c202c5451844409400143c610701d00c283d00390141642176038020786948090820046410f00c15041401041d0f521203110303040c40c190107690f1003486085921144041d44c2c020007600070010144207042c038040c1c01a42500c005d01c80c0500c2c40e01c4507084c030b00505c081d43c400c001d89281101001c81045520780c0d051038000701105d4110005148100b0240350082c0101d030300c401c0001c9100030b03034640b40805c59400108203003d14680b052600802c244018008c00e00000e20308496a40300003611980d840038400c91098400090505081c0000750240e51030380d000744900f0f4202410040d074040d000c0156504010051170200c0d242070440c3d4001d020307095a07202c651001001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 928672122 1250 928670872 928670879
    0xc0207031a0103051c0806150d090f06140106021207060b151209010e250923160c12020c040c0314010f03080906130504020310051c0b0c0a0c0c 63
    0x80c1007114101c910402c111901c44d94990b241d2200d0446000c152404580040005401814035035541c0e0002d00c0041c42e03143c649044904035000304c1d241040c058138420111002d410800029101c0c0b4100c400311419960281d6150040c000c0d40c4040c0c203040d85c52881c00c041450300c02c004054100303411015008145403030365035100c0803241d80c640242e5908841001001d002c1000041d06108640d12042010702414000c008805003501c0c0d030b19908050a402100c40600040c0000244030b01140b941c1c1403404250b02c242c0c00c4160b0041c1880191842021401d083c0b40401c01e03a41205e8a0400183e001c1d103507206603070144000360304041030745140a402c541002413590080d40d041c0d102400404010500408590321000095040c00c1c01d80401802080b0411003080750380b400b840685640c2e416031100030302c50341d22030b400310b8140d030001e40305544913115004c000d11040ca401c052400d00d940c00c00c0940d030901c600c2c5854441442c10040d0600d43c1d4194006004a034147c40303400e14402c0780c0c1d0441000c0558aa4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 928673372 1250 928672122 928672163
    0x7030504020112050c030c07080904020403050a0312060608040b04050c19080d05031e0907030629040b0a03030e180103050604030216060e1003090f030c0c05040612060c020703 77
    0x604460807800200180c01014140d140392064a0280b402c500c2c07550305603501c102c0321b003102d43d0101c2400c0e0f500d80d6052216600300c4d6607a000034805503120300040c2c46060201e140c003800025a0054001000d4101a024440c0f03e510030032240e40103401425180c441c1d2a90305101e410300c1d1450081641043d00600c9900b8180300c21165042152200d408880700542c04a204840900082ea040401100c485801404901d9030010440e0080c0011055984507582e0341d9560b001c0302c0f507000c0310ba04800d002103007841070340b01042000d1850f454103940511840c05120300083e9024080d02009050141d4070442031045d8807403907240d00d100d00c101050200e484d61070381460359031103008071011001441a00381c59074021070035030042812544251901541c00c1e45441c204000c9810490781d27101003680e640e000f6000314135141040510103009440301e203c8240a03040c980c01600f01500518000e5040200401c00b410340a4000c0910341c1c0c01610003c0e022490392822802d201c0d8960025020101c0032311142080c41 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 928674622 1250 928673372 928673381
    0x20f06070b010f060203070b06120c0a0608100e040f02150904061e1205061315062304020a051e0d020f120a090b18070314030706060b07020307060c1a0703 68
    0x1440140d9110003a5030307444d8120b9a0f4480d00d403000f05079002c0d480215125041c091141c994000f500400c0c1c0b10060392402c0070a00e56046175000070000341d1288141300c0d410001c024070501410907802081440d141c66161100220324001e4001d024a01800791080b91016a40603102d44610090041c4145969440c2510130b06019071640f14110071407880c00117148036000c203081107480d0b000300600f40130359900d062002c048012500689040415407000c92821074640304800180072200c03500501415014000801e84021480080c01240f04107e403140440d08502039030595022101004010b1744070b0034441c000c900600003400340c00c0340041808601c0c00c080d040030f051103201d62940061345944180c1c1d0001a1400710b20050200c100d484081180345d407018039a80343c0c824540044800c841d90703039507528140403860048508142c1011510004204080c0228402040000941e5080c42a9900003a0302c07485c0030b100d840c041c0001903142c8010040d003e00c4d403840c901046400c00b1071500d4400e10150141c07 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 928675872 1250 928674622 928674629
    0x4151803110601060915050409090b071701060207140d0f060b090a1808030903120405060117010603050c01050901090f03030302041701090b0601050f13080f120a020316020f06070b01 80
    0xe4280e00750680d100c1000441c40d04858055503007013080ca14010181c146032044119040400c402084081034070589406040760040c0304201c41c5d00c048c50700e030300e0040c421000c201400c882140351100400005a0014410090b541c07200240c916401c02100090303c4842c0314040103100640c41c8408005101e4140d0001c2c4035194181d49000d025510380b01c503401125103a820496031504022072034000316401d9405198820f84100841c0c2c030b4100031881c0c8020145086504403800d91240006214902040b0300a83c414514040244506400d5548454582c3c1c01c1c4a5035604000001c42c40c200b0980c42644208010036400078054111500e070308004000c2c1d801801180807a5501c10240f040c1d0a4051081c9603030715800c02d82c40c19441e180c9200454842d48111940e41503c0b5090000c100030301451144000104a80401030880c1580e522075141001a0102080003c4030f00344040c001541d000b108444000031310208800c84101c03107100203032400c08001e0801c2c0e002800401c66030100000c0741d949138180c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 928677122 1250 928675872 928675877
    0x2307050106060c05030418061d090d02030c2107020910060305072d20150c07021012060f060c020a080309031005041716060501050a050f0904151803 65
    0x326501c401043e1940e505201000700700740d1042104001c1d4246e07030004003001145282c00814500c4d03440405201d40041c400700405540300010521003100f034100001000a103860001d1400c041c2181c5441c2e844180e000101130402c0c40c880b400740d032403c2514049581e0158001c0031039190741803002c080500e1003102d0082901091510010400442c0100040784450400c280d085c46080c900926806959840c0800002400039407101640343e010800d021480414011004004103150410800d084040182540f8030100c2c04114100c09178031860028040700d11340c1c0c10b01d440e14859050b4401700a15565106803a1001c1c58000401d1031030740021300d581260700840b002c1c0b0505445003952130b10b81c1b00380264554190b0160150184024040e0070896115004249580700b20395449100045a441008070032501c203950348031081040a42c0c41214007400098a607424510300301004101e14020044070644241c524a00207070800c10000c02c00309176102e01d4074080c0000050b15142c2a070910003070b0000c030301 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 928678372 1250 928677122 928677131
    0x909060f01050904080d020a02100f140f1308180603073203060f190306050105240307031a100906030f02091c020102030708030c0910020a050d05090123070501 70
    0x90b80e240035070384540a50b40210f4424908801888500c009501c074110b1442036004100e007091501d080d9100e0501200c0c8010b00c041406810a8081d18620000410103035013a4102e0050003c1c0c4d001c4e008540741002c0d882959103585111100c5c0c248294101c4900c038580c4403070000200410590310210500300b401c81c2072100d80201c8024810750303c0e0700b410084100100d140c207000203145460030702c40030030b500c0c0c50180420500c0a81e02c800b007000c80e01d50303800036550783d174071840104014240440117140e0b00440741030301058034044441500c042d102c0601030300d04045c0c0702c080800706900e940c040034014100007804005030740e181000c060700d0141e840c420f0b10082450b2495040c400c2e0700500888a070940002c054800d800403d42441c08003a100810a80c11440144940000904104001d40c000d8000d440550388800a2400304445100c0c1c2e501f0040440d085151240c002910004241020300c050b41007554949600383c00407a4502e0456500302e4051010035044001344008600070b0810a010f080240b0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 928679622 1250 928678372 928678379
    0x1050d0203060615070b042303040e0403050703120213180e071e080f030711100c03080402040f3303050d0305091608010209030730020a03020909060f01 67
    0x419184404806500354000200041191420400c066140d0784032003000e50030f00c60b46494000d940001210100c0d08200c42d03684950408103201400544075101030700541c0380608052610f0514007001e0002000c0c08408910b8000f054016001c1d03010306140450f00710344414411942c0310b60309417030b4444c50540404186608418101d42d0161080790f10200c40103201032450000344079441454041e0850040d8041803020458410921003031081c400c0c808011502e810079401e180344104510b282c610710800d03c09a00444a94200c101a0340c00f58050400c02c3c4155035600105001d859040a003950721850240c0d0704400c880702c2d804010904544007103100940031800440c144070300e02400060010350100314008070403817003600125800110141030b954030410100c0400307400c0009030484200341c1d4000c03902c0401400d0030080c0d40010300310241581d000089002c0030721246070326800b00010300e0701941209001d54462a907504005c55014020703000c586006c04c4c5103078a0302403e88902d04413400380300000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 928680872 1250 928679622 928679629
    0xd140a0f0b0a1415030f070e2e0915050d0515030604080d060f1202040f0b0a0b09030a020303030a091505190c1b0c0f06230f0f04140103050105 63
    0x301d0700c411016141422450600000c0c2c860071518000301d591181c07000c0c94079528403038940702441c0a803040710011049404d002e50064040042085414010340b81d0341072805003080070301035028407098040c2e41c1c2e80c102642e02104454064650b08002d030054001002c41c0e803c0c80c2d00100528021040c0c0c0700c00c00058540c02c0c90507003160094542150315070700200206000c2030315071009101c2c11201c131000049440c2d850500701018011b903030020102c00f800d000311200b5420507029810758030451540802c0003840800014403415454000d03440581b80c045400540380c0c13020440c0e00031007030b0000c080300d84900d004181000546002c4004a90041d0b0040a9441290050003414091445c3ca440c02881041d115440340003800325000d85810000850b0100701058043d00300540168040c81c003c404250900d1180365030050260304c0700c0f08029140e085d0b01030b20284810b4006a0000e0300381c0c09556814042102142401110400500c1c1540054001080b9408212940c00d01d10203803030a1049aa076441007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 928682122 1250 928680872 928680881
    0x112101150e09010614070512120c03090618151f060513030f0f08030f0a0b1207120c08030d0209040f111204031e020a0218010b18060d140a0f 62
    0x40c02d40041038000140708150194510007a0403294081090401d00700340c40700351809060005c2c041144000081c0f00d00300c4030280288990201000c0451071940c109007042c44d6540100420403100b0300362800200034154418490080071007031a405010017400c00141c00408115103047c00001085044030008a0307078002c405a61400e01d4405080300c000c0c0c915114a80400d0203a00125034a80c0c00d202604001095040a5030240b80b40c004031f08441c0c98a00082d0702140c440d43c3c82136210f103203100504401140300160303480070f84000c240d185107003513030f140f4050342c007810700303800000c0680804221158019a10f03030180c41030a00880d03043c00f040c030070701c11203804903042039040e024042030400c20615840c0184032a00e8101d8401e1408440315510004401c620f10503000507180140c120261031015072030107541540031010341c540035250300d503d0800301150724811a03003406900307440c62201d0704c4079948460a445c0c208250407014468003241c3e111003103094000f00d03a0b60551603c1c103549549490014402c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 928683372 1250 928682122 928682147
    0x121409071e060f170c07060e0f07030809060d050f0417191b06110405030f01051e0709030f080715060602030f0c010204090609050402031207030507030311210115 71
    0x81e804a040c1c18040222489503101d10000280708612560075003020034412014440c07450610120740303a420b5403501c0c50076110001c00000c4903601590f01c0c0b01c1e810320301040100c11280e10080c5595281c5900d008650706002e805032441d5198a09070412000c030242803502c61186228083c00305056a804003010194012044260003200c002d00e0007a0340d01e030050490f507102c558140e0708000102d0241e5916415224092385030a0320f1030300400c04020a0034100412440000d030710000340720502e85142182c40401c90191014025010030001c0740a0a0040004001442c2c00100c10140e204440c00e000742c080c1c0c4030250860f45c008030035601d100429298418141900c4450380554a080c030304103241501c507081484d4004555608004c0024103c080d882024000c0140000100361842c05004050620704024000d00d0304c0d09041000c000026405021641144e515080c0012024800000303140755002d800044c90902084d628840450030314152035904131601c043d07001e01109004802141c542c081e004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 928684622 1250 928683372 928683419
    0x2502060414030705060c2203080304301e08091c12090c090c14070f080c0a050a0b090d08011406070804090e071d070c0312140907 57
    0x400c0c0000c8a01c901d4081c20014101241d0070402507450b003e06000c1c00b03690382e0b188900c1c001894500d0b2500700600c2071015000c20909452140f450300d4110f41c601c0004d00041000620070030280410f016800f42102c003180d079104180301e800d03121030f002c0d1904141d0041c03071140c074107003004800415100e00c4146108092003006400c4d004400c100302584201c07400c0c018400c0c0031103582603040340205071094a0500b802250502c11484c9403080c41e0045903c022014400c110034480e034080e2101c4240c00315410345030b002010740c460422a080c0780c0100d0041003034003c03140c00b6084030482407010005500200c5409200100d000e42c980315400c6554031204018140810056401040740c90408001c2c21090000070701007900e0501c0075525149103a015420058526544048501078843c1c200880005011100c520071700c5207291510f940145c02c002042841006102c1d243d8030101031042020101c800e00585090040e402a00520711039080115071003c0e0620403c8000900c105511820040301d60411 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 928685872 1250 928684622 928684633
    0x3180a0f110a0b182112040e010608070504060f0314040b0f220204050907030813060207090504021509040b041e050903030c340606140102010b060910090b0301030b2502 74
    0x5505002c2c8200e41c0b016030010000c98aa03c1782c1d05190705022000024560701855662079060621703011404006030081c03000c22010a08015410f60440212015a01141401c209046002c142103003c0d115101c1000c00030340301c840901c0f00700920310500f503020b0200101681d42560b45e40032509400c1c0107550040c0700f010140e1a00e0740c00f6041a0340400d40081c10203007138441041d181d80b01c560095020030544041c4404081082100503818009540130f0000d880d018441d600742600021004101c1d560710450a6800003101441c0b5a40d40d4041a01900701030400d002110300f101d04100c1200d0146d614a00245c14500011840c00000c01142e10270b16880d0300c100e00300300b64000707180c41814100e46d152902c070f1b00107006500100054410600000e205010118440b8141200da0342c114040b200443d041d681000742c91842c5540c1c0740180d4804a105030340c0c2e0700318500d11180032181ea106540c849441000000300100c00d11402c2140790348030720054000c0c5405101465010030070040841503030b90040c1c011 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 928687122 1250 928685872 928685917
    0x80123090105010e0f0301110a0906030509032a0708031917040f2a05010e030a120f1b1a060d0809100e03010507032a0503180a0f110a0b 60
    0x508201506444050a400000b5901031701013030071500d5892072007142e10804038008124591101c0e540307014184505d03041c030880c200026001e58a005a100380103100040b4590b06401d4103100e0800c22043c01c0b071808070b80ca5180d450501c0e54495103c4042d200f4420032110320b45607994010f00310500c9541e40c034005107215568a45843c10300d0b050300b010440758004900424100100c00b8000040d5856440d060706080034034000024107412006484240a50444000d010104110180040c075080c01e0b400d1500d98030b2101030080782e41c0e0801c2c50403d01828048818031003480040992110000348249041ca07064449e04208640b26038071040051140d44200050150b5050034565900e82c4911402d0841c480e06414002a00f5240200c0340c05001982e6000b0f52070340c4401c100c8111110202103500d07a0400c1d04c2450303000700144401000c1c0d4202082008100361200010005048a146c000d00341c01d0150500b4500182c1d036401140e80e50703205d08070300318020641d051841c00301d0310100403030300000030709809 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 928688372 1250 928687122 928687127
    0xb100602070f090906091703010807060905100c0321060e060103050105130b030106210b160504030609050a060207080a030b041a010e0d0203031c14131e1208012309010501 75
    0xd206800312090340c0c607000c64600203a6041f2001c0009180c00c1e00c1c458903581403000d4549440301d942d00080070003030503810406c156124103014418100b11071400c8020600507060688003010106c82842d0f6403400240c00840c18200d550010342610322081c041c3c42d144e11208011410b4560070700034903038042da0340030402c80f170680c0b00e0707000c51a41800600041040341e030703030304620202640318440d11041c401880d0b040d60400c6a10711616070f100c42080701100c444820410014024082d47c00000c01d055a120f4200d814801e0030070072901c0d060740c409415035440119103880102900709103100e001090600080f528646014010f44601040500c3c0c6d45803c3d00c140001100c0d0020620389a03504040000002d801589051009006c0840030b4080c2000300c0341051085012074405441c080c01081c2044103100c50007072000d8220000d503400907035003512522248030890342c0042c806401402c100321041001c00481d04100100c0c12a14401c0c1c1c9200c015030726055403030784000e448030200da004240300c3c014882c960 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 928689622 1250 928688372 928688381
    0xd15030503120a1503060c121401050f0a091104060906090302150901030b0a03061505121b0105210f010603020c150702010b0d1104050603030a0c021309020d0b100602070f09 76
    0x1200f4101003042005070752103c034503032030741d4005030b400c6da4031401200390030380d041100e403414243e901c0f20030003600309034035060b002020b41805998170801d03441c402c4015590342d03c4020400b802c00181d003008281500c042c10611540944660404940c07400c0d070001e902c1380148030300000c490b0040e2450285564515121610b64401003d2070305040d62207e0180c2103458561031880594842c40c0d001404000d0030741712104075161a40304521038040100122901080410b4000550b1003001461110354000c40041c0d0740d6004e901d11140d0300d405500b0800c100d00340c0c68a80c45016050401683c0b02c03e9803503a008409a1058004e0701d0007541c0032046038640310078174040c4030390f01a00501c000a5507000f1710380002e2038400035407070031388035101c00c4032085803071303143c6803158a4104030304a009515080c422100039021804464020388602445440002d003980c26820401d24183d004008034800015480c240091030b40c292084642c001c55501c0c0030400c2e41c0009140070603103400001da2000c45190220160181 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 928690872 1250 928689622 928689631
    0x21b0d0516260d050103061107110405040c18060e01090c0f0c020604180e07050d0c09050a11030903311a0c070f03030215150f0f09070201020d1503050312 68
    0x684038200140c006034250b000c0c0c03150300500140031465500d07508000c8140e8810005004420804101480004806401b20b19031044241e601040550380c900304000861003e9001000700345075030060b9030098070b50398401d0702502c01d4240d0061007a41c03030f000a001194404075201c4e02165520200701d00b22402100100c1010380b004100300d14013500c0311010300c84075007090340c070038030046c0c8441107034403180c4051145001401e81560740c1c540102103622804030380c403081d00c1207001d007554420228070880800e82000034000603001c2d40c103689041145030f5075500e50110b2203400c001e07080800020001803001d04800051030200d40f0400c00c050030000d08a03070320410341c0f1940d00ba03003208101240214170140300079001022403605002d5000d04d1130801906050902400c1d8419405050400001304a81084a94982d009981051003075842c00701052000b584408503d604c07203a850200040264150024840c141100d0028400c4d00007e000c01d800c4164603001c010526003003480000911141e08110303643c070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 928692122 1250 928690872 928690913
    0x100b09150a0207030201031404051213030804030c05030606090108030318010f0608010519020406080117010209091006030e060f0a150905130b1e0a020f0d021b0d0516 73
    0x885605200e00340d9028050320310160700940401c10540d030f0103101c0d12440d07a481d000311210510f0281c0c0c40545442c150004445011808034107041d00f102010780d09800355510198040d030b00c075101c0c14003001c2440e0714070a452003485114000399060415442e1a03049920180065003036032039406074540030307030144034484105660758600f800420b64207018400040080500004582c2460040e0b42a14a040510030180c00e004110801c01030380e12940c200e046a03074004142620002070516035003e4802c0781c4103a40d01402c100148180100584807040c200e40b61134070108000c140503c881ca0b00c07010221020b03040030300b860b0006050030706c0581000f04001041403001c40750540300c400d4103088900580780c4a60b100200802c03074041083d211680c54202024161440300320814400030390032558000e003402c05907500800c03008002419007003650800700700381d03400b55101c0300041c00b0410031088608140049220f00201d9544440c01002140d0a000072200207100c0d03441c00381c803a5601000313841241c071007 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 928693372 1250 928692122 928692139
    0xc180302151c020a03050609041a040809090702011d010c091a0c0a0506061c0f030e01052104050c090601020d080c07020d03021c110d110705030102030106050a17100b09 74
    0x48004549a40002c1e910500584800807100000c00301d400c0146958060001c481c10f10010500e21002240310170000016414943c1d118503040c4000d008582d171494120405105010b2003907011342210f004400c1d040f00050b81c41c100040a03500b40c902c0c03881c0002c04a1135651044c40080961306c0000304842841804501e0003080940700744c81c04513a1401990030741c22201c103011040c506520002400e9400302551042c55505440341400004202c3d8001d09000d84081c1030480b41e40a032003520403106007038961010f10704c00715000c3c140303004e4202c0e001c8544c0d001303001d0000d5072880c3c414203a42c083c41c8181d00420350a41e40344810345022102408100903240240418030060b80c9140c900c160841c405e034060084202c00e01419680400e00300d800c08140101701070120075004002030980321010b041e141c00064120114582410111503420045d01035000000100384030344c0206c000c0404c0401030742e407541e400303044460104000805807103415014100000c10420343c030401c1c01804920307400800300b44 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 928694622 1250 928693372 928693387
    0x901020f0417070b0405130c021513030e1509090709090f06060e040c140702190b0703140c0712050c040c0306090e0c0d08032d04060c18030215 63
    0x15425007080e844a402241211000c2480803000d2000c0401005842c2d01c160500e420900016044c0f150039100d0396203141c2d07403100c00c400399100704a4145c419180b50103a0a0341e0030f15000f0480440d40081041e004680c030801d50924500306030b031704188864410250325003000640700030084c595902400310010440b040f480400c51018a1291414030400c070348000070303418605a005440381400d1074040d40714503e000b0002c07000399003018051440a0b44040f8007680e4a41c3c51001508019101c80c0202840c568642c021410f01e000701c0090411600989034002000790401003820203100c1d44c00c0d00c070810742202e1800c20603509500da414042e948240183c5003400d1200c400315040710781c20940c2c03000080d02c4031420444210380d0f104540401841380081d1a1211100000c40d103e2850700500a20542c0000006904080305040a2001d0001900c0e1860311029000c11001c8440e000e0b035091382d020b4a0454050000e038040c40b8070034011010581550803051964003002900c07522007460808079141008000d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 928695872 1250 928694622 928694647
    0xc0c100908060f06040e010c120b060c16060e03061018091e02040b010201020f0f160c0e0a050a1a0d08130f1d0f040b2d07020f120a0503090102 63
    0x228400d11444500c01204e00d490401c000580f02c150007011540d03450080d01d15031040d801840310b1150204000081103280f20700300440c089219481810009000719100f64814440c0a603001c021194640e50b401c80340b0400e1030030140c4698069420050418030200100800c0342d08501103035070a100d6000c0084d01d1051038481e4111200079030305200c16100e000d0120011441c080c4500041c000080c802103061103c8550945414407804c1900d242d0348034081900c003441040e4012003281070b644411000080b036550190000011029521441554100300000341c9443c024440d21810344650445c0c2c0c1c503d03c00c0381090101d842c415010540741e182003084040d0700005101c40326002070603000c584580135031800480303000d1120b00322094030307118150340d0a00c1405101d140c0c010341c109800090103d0b841d00c901c2c1208642c1894007880301102c100f03040d12a00400e015058203032240b506502601c0c20010390044240e1201091340428024140511918030ba5601c10005107074402c07400390006240c5600c1900c0d1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 928697122 1250 928695872 928695883
    0x10806100e0a0c020c040612030f050310061b0611030406050c0708040605130f0f090f0606081b040317030f07020f0303070c26130f1d060d02040509010f060b0c0c100908 74
    0x10101f0460208d200c204066214100c0c00c1e0324281442d0090a40c102050f42d04401e401610814041101603103412907443d89007440281810303130050341000210307044c4c03050100607001200c054949a1400380000c140c0d00c0201c0468840d140d03c5030f01c103858281464030960741500911600100b1041c295008100f0804030504503014081c0c50b0541c2d8000e07850700c44508265900100414010341c1040d804112582c2c1000c10250003110031080d003180101c80c2d02064080d0700450380060507000d1101c502c4002032048800070741c02113490781d00f940340344da503112000c5e61f0f1111401e64a00491b4030400c0050041e5109803241803450340306010000340000c0203801c184420160300d074126490300c0c000560000e511449084030004007903440d001c41065280c03450800c4180b203103001c0c18806c111044001a160340c0d504050f1582294020810405420b0012110f4000c004e84e95020004038600a00882ca090141040d280c0c0300030b546001b031001a908400b4005904180003019084c880c201c2000715000d0310034800b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 928698372 1250 928697122 928697129
    0x5040f12021b040603020a03020f01020f06161106090a08090d14010c02070e0c04030f062a09050d15090606050303030c0901031a032d070e010806100e0a0c020c0406 72
    0x2000890b0455003422007480c2422411403003586402020030042c4c03505201d80c41242d030115070110950355502c00603410700c0da280d000e4401c00d0050408010700c19040789048400400705503682003440185860081c0c1c5e1784030507070b40701020b40d1110b80500300180e0141c0c01061803c0000e400011030b030b44656514804080000c005001e01d9448611440455074108184802450080b051000e207091500601841c0e01c41d9020103007602e40b0210309030b030a02106400c0329032034400961b8003001011000000d07401d0300b403d800100f00021280700307000500e45030003024901240d801654081c64102880e0802c030041842090403119203407145400a85940c5c2400910300c1650080c60b92503440108034001021544014020340b2505042500103010352000585031080b4800030301107000300f1201160711a030f16000c100510b01c49101d03104002c1420200b403680581283c3e0304c00304842258407000580c0058450340d0145a00100b944000100e24003010b4011642d5910f00b80107458442c0100d0001c80d00703070b800703641 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 928699622 1250 928698372 928698377
    0x1061205040303110f030f0a18080d06120b0402040e28020a0506130315060e180c030303070203070309050301051b180618012613050708070e011a040807050405040f12 73
    0x4200007000700c009040b00d034401d204200c2081070074508000400c0c85101e01d9000b801d4000701280f203420bc050740340d012201078003110190240d40c401e01c3c5840c03072503080112000c81c0640e00748219500e11a80021740501ca000701a00c0c540703034041242200020380e000ea1003069130b100c0c2201c100040d41d921510002d0400642c8107048144a40c1035007007445403c6100e0074040070b00c52030300604121175400c011380d40750041f000d41c158400031204600720b240f81034413000d20650b150000205102c02550004001c08185100380c58195074981c1c1ca600701801c07541e0490350544c86400c0300c00b6420701d60045500811442c41d080c400b40103c8512000410603613009400d40da0f00c1244022901c400703030368204500381d0014101000e540200b50f50b000800300001e0380503101916070501e0f5060f410420a050248030040d0428004030303544160741d0500054419002c1c4074140306500b09005140402030300d0000c807000d40d0740c000018440ca915020a10005010040c010b45066110304401c20004803a401c991300820b0450303 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 928700872 1250 928699622 928699627
    0x1803052e0203101a0a0509060d0b130c11011b0c15090c030b280506061204060911030d050403240e0a0b0601260402010c0b1806060901061205040303110f 67
    0x4620700168800c120b460310113503003c0c0f0041c8003081d070000031503040704019645a501c0e2010408510046c00749000105e0b40f250762489007100000b0294042415080a13a40c0d0b0000403a50310065401c1307600400501d030310120b00c440b140170500e0141e484222418412807042400150b072001c3c1404846a03c501200c2c80000e00b602001481442d2142e59000038100c103c2111410b14048105d21141d0b6082800240c1c68807040010203c0d541c00c81078039010802d05000c01c0701131a09142c40c20040001110403644e03100060041412030400040d22040d000094496510742030440d100c00c0b14070a03100075041038083c84150200d1003034850780120300c18134483e240101b901105504c0d040b20116001803c0310304002c03000c0500b5071500c40c9c5e034010300d03440190b000e145001a00c490004035252401600050110801c038410700058202c0c61422a07044203000082d18202d07101c1c0010004038076000c2c031036080010769242e01107140b50140d90005400c01e100341400240d2850681034070020b81c21100c2c40400b02c8001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 928702122 1250 928700872 928700879
    0x1803031908160306050603040303090804080102210c030906070309020d150218040203160503040c051f0e0102190b130c0906080c1212070812040b04031803052e020310 73
    0x1044070002ca0050b45041c00d010b05400c000110b038041c003008101804154071801e40b5810300980c20308a402030078161002755070710107004100c40081003c03d07600d0144182c2c1e1800254061041100b0369006503e0f45010788001d48801c00114060110004260781c001d0741c041e42d20700000c20407100c5c000d160911400150b101d1580e104030704030405500c2596401240100100802041c60f01c2c0d54141035001401c0554617602c450410f50081e010030f401c401c0d0070040d030400320505440500710040e10a0902d0350307908681c1c07095070f004a840d0110044a42e140100c200f0002c000141401142d80e0301054102000b240001c4940703540082c03d005e40d00009ca12a66400309102860090003400383c9030405580096580085c40c458a03611b142e410b00c2044000d0020030b01004116001c021a154031216040340c0781c0c07609050611500d008002d44084020840d0f041c00b005103494a0000c2c9800c0300e4000300940051543d503a02c40c91408170a844205c1191807076856419088941d10185028005141c60001550309 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 928703372 1250 928702122 928702141
    0x1f080c030f1b1e060315100903031b0c09090c0806010b0a0905060a030b0409080a020111161b03061a10030504120305091006080606120f0d0e010c02040516080a0b061803031908 77
    0xb13510041000c10091234000d001003504400e94103c4460b4003045401000001d00b041c0c070205907a5048910030609108580c0240002c0b0040f10007600c0a00741981c02690362014090080d01c607240301076010a4100c0300400c818a0400003402c0d20007a50304021a2014030080051b04aa00811049948410210f1080e80c0309909118480303040405410f2146005120010510929034099005080c4400e100c0b5880005a5a0500310001c0d641300c02c0c1440b45403022090070079620155140d42d409100002030801496100c5e004450046030082460718500c07003000001c601801004048010030302c108a01c400800d8403a12680c07004003541c0010f0310383e50030000204582c6101d004200740995001e07031031100c826140418503c11018160a003110040d1a010050342c82e0102c151010358880d01e020108800c0c024482c03071528844c0d40d1a958a610f55881041e004100c480c03080c00c131900400140240c0072002c10744e5000c0180b200004040300d091140d644804e000344034241c581c00c0000356010b000d11041c8070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 928704622 1250 928703372 928703389
    0xf050f0f1c1b0b1f030f0f061d0105010603050c0901052706040902030603010c02030a1205190c0206061005210c12040f0506070221031f080c030f1b1e060315 69
    0x680e40522a02e04e8a5601c8a0010401c2c154020f041001001d0404040002c141c2c01075042c7e506c1e0704408100700000006050003000244110b1380403a09100010f00c1410544c0b0440e082004140c4815050280082904408980d400007100c03400003681c0c074452080e542c0e000070b0801070071007200142e40ca06c1c081c0d060600350343e5000c0c810400c0d940140520401c2c1a081341020400003410b03a00040c446e981c0c1020315840c0d0003405412030105c1d1130440c01e40704250b80030070118070462085c1d4808a00300002c2004644d1841480504040c1108d80c0c0c40d01e600d64260f1800180d08424519a42400c201200340c200c0c1844006441c1100d03101b1014925004012061101c941d1201c0c0c10f001030303c3e03100c4903d078602c0f103554810311204031900c40010008240c403400a03130032903254540546031402c26440c2d80009581d0451000c0c814800e00c40c2d4040f2411001d40014054210603014070311142000c003140c140000c40141444d81046180e01244208041e01c804000c0c0d44104500c03190101161449400c0c011200b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 928705872 1250 928704622 928704661
    0x10f091104060e1519030219080105030304170f1504120c0b0f09010e010501061805150a030b0a150201050106090503061003030e0d020d0f050f0f1c1b0b 67
    0x10042030004002071074110302101003076001600c0340084c0042c03410786030b9020310400004034100c0f8000244108843c1c0c0c5507018068601d0700652030f01e01c001004e0801d032130503102441480d07031540c0b04001c2446440d80e02e031412543d0004031802c0340c00481444030030324180080030f450100443d106404000501192480760303401081d03a41400c10b0049007075100c4404000703004201080b0980b070349021840c06d070000d501420b01d9198000003041256180c2c60020100031683d078144691552a030004119403400700010006519484201c41c074100805109501602c4940c0314213501140d03021002441e00c0544202c80042c031425400010301d50b06160f07014041c1c40881e00101d0096210104000044044240310300c203484e0503003441c82e0441000000140c0302d480b00c0000071741007280c10316440100004001c4c640000340c40f0704295450260b055032200e507100c02da0601903905501c41099410302141c4001031405803e103501e0f003030040c1a0510700c4c400c1c3c24141220200c500003014810098120003811551031207 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 928707122 1250 928705872 928705901
    0x14190602180909030d112b23010905040215030412140a0219231c0f081b0d05070e1008010b0912100606180801061a070c050306010f09 59
    0x1500f0510b10701a528001e1011040c0c5482c0c2d0f8003071600d84525020140d402855a508007801003652804c1d00303640051500700910400c13400c058a8406802a01007800321021149a9000d081d81c039180264000e0032014005a13007033601c20300e000f00143c0e00340c4025032050340a1400100c103462a407800a10100803241d4100c5120001d000050b013481c0d0108501034001c4940744076880104190070030140c1714440c801fa40c9060f81c25500503400300900031640609900208011242c2241407101c180d441004c50201c1c100004d0301c031030000e8195904100510014100d052030310742041c40504230b0600321442650741c0004500000d1507550700c2c1c504880721270303c5250300745080800d5516101882c001801020110351141410440c1501140400c01c403c80d4941080c0009200c480d6560034058192103844802d1a441920400c011a0042050180c1c40456180b55140307810080710031000c0d1816004040121401c18444200140b955003c001842c003030320021080500d1245001300c0ca81c102c45c0c400010038034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 928708372 1250 928707122 928707139
    0xa0c060b0f271b040b130f15020c090f010501081302040c0306080c0a030b130302030c03040f061404260f0a0305040602010f150308070f0c030309030212010b0d1419060218 75
    0x2042c2c0c1c1c030780b040c0d408445c024a07403107860340d6054200c44840580ba8206805088010600042544c0c901c1b84501d00000079809507020800d1541c14040c080b14106c891442d14100c8100420181d4450503140e0750010007030a124031035206650000b816201c0032410b09000a440315401e10040c0300501c0154100d031401c440034180700b4519650220b404000500e2320030340903080501602418000d10031513425802074402d41e5612500d5116050000245008000000b035140d80304035400b41e0718604132070a441e5140d200b060100c0345401514140c44070b21141c00d000717002d01408920540c1d0100414424580b19440300d949540c01c010000f0701b11011314440c58003881c10608039031000710041c0224000d5179001440c0da81d403014941000641c03241200300013081c82c1190040041856030003511042500d10031244104584404c1040302e003039074000807005501c203c40581c0d4500103800c03c1030450400d0f481c0e60544211980041e02c017401c800712090141c50260300080c040740850090822200420710440700c000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 928709622 1250 928708372 928708411
    0x210f03091a0415241d1f0e090706080622090c18060806090d1d0d080c0d02010c0804080a0e2202070b07030c051b01110d09020f0103020a0c060b0f27 65
    0x4079054054034424100b003250310346d80807040c3d0309141040648030b400c0f00030400c1e08040188a83d602e402c0e00c28140002c0c0300c074001c40c403146000c540040440c3c81250801c0c50a096a103110001009900130480340e0700c503001400074100e42e201c9080102030321a10800507106240c82451810910020200d6282e07812041803800d103141c02c54011030010342d0214a40307404050a001160b1544140130018240c2030010401c46151030000803244043c520300c0e402480076210248017030391841c0044d600108072000601041114074070071941214244002080c00c1c0c0104280e4034a11804800d100041e2651a000a4050140400c0f80702c103513080003562404108240c0324882c0141640034001c2005445200300259044882e000d41003040451203001c0007564400c1d0070310224008040782c0008a014040a40040b4800e41c001e1007501c00d5aa200c1d102c074103640c0c001c3e5a03031700020144a200c1c42d83c80601403110380c1c0f09848094400050200b150700724070340a00303101c03042c1d005441d005081d202900744d01500d00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 928710872 1250 928709622 928709669
    0x5040f050a2d0b13090516090c050d020705100221010f0f05101206060e1009061b1e0303020c070b07030c0f0f210f03091a041524 57
    0x6201c0c280c1c0c0c002000581c03100340d000081e81a56040b552144c21810800880184071020170b01300c4188000c001c074845030f44d54503040c00050701c054500040100f0000c0c0019071001c003d80d002480114410f20980d519128500040e0040360010101348280b00c800159218241c10540420785c05404070108454806241100c4800000c0341802403c2c010303100141d5035400745004508810000d14008000e004003a200d0030000e24101c0c3d00996180319003e60107901c9100740c0140720500503110759030f503841c0d1a46100c0d08070b16902124800d04940c02e0700307402140c1182c583c10f01e00480d01d00d0b2080c1d8015941d0144d8444461802001d5080380b0904141040b0385000250800380d03c960080d4810000701c2e4180c55400d00e03c041011003100502074000009081070598200ca1111604841c2c544030b0040042000c44201c0032202c2031100200740d07600e4188a40740d42c21521048646c0548500e12141804c0c2c050080c1c1e8054418003900112007105061034a18490000101d4001a101040094078540118240b5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 928712122 1250 928710872 928710941
    0x51804110112050c0a0e010c020315180304080c0a1d010306180206070516120309051311160c05042a2604020906090c2205040f050a 58
    0x410aa00390081101240d0007036850009603030a50004109610384020160302d80d9101103074500005958202c07030f10203980659401104075801800805004040702c101e4541c0060140c66240d10f014542c880034880102000181f02418440c80600960b01c581002d002c0300003e25040f0102c018090942ca0218410007900d8a0469400110100300c005400182d001086005100a5086030700016131106210300012481c500c510500346440c0c039140c1e50054100b031040142c0c00180080c142480402540c6400d00c0e4032240740304207510000310707010440111101c55200300155141d07001801074010500140215200080600b0780781413155100f40a040c1c90351003282c040500000e40000112003403c0e00c81e240c0e0311403894000c0c050041100c07490304080031110044800301c1c0f2407044400080c4640c1000b0314610301804200c1b00d240d003003002e04140c904200313000b0b82e0340c0101e451f001c003800181a41c1e14020800c41c1c07254800d000640b4101641d81e03c3c00c0e44c00940b0781803a40c48140c0340188490b40071284 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 928713372 1250 928712122 928712131
    0x314060108060705030703110307080624070303090c09060f06080108031207120609180b0c0f2a060f07110f1b0a0902030103060c1706091816080d090518 67
    0x20407641d40c0d40c6860060b00185440f00710300200720000b102b00480b440c1c100c40464010b2900703c0b0030390040543d40c50b01c0303000c61090080c181480a418861980081c4c00ba4200e810f813984030340505102e00740c49003140c0b8110b6100d42d01180307500c40c50480400c086074104c401e030340c05081e00102031845d10082c00b4100051141c060041d10401400400404801841c0d9008101400c40c0c102c05002041c40101c2d00103244000b00c4060342c20040c580c008c5074010601004a0b80034030100003d0030308010341581d169028890b0206200d404400c500c0320201251014403045114860142c846e19050501c0c2900400c40c04108100084039403020548a001000004000145440c8041040b0400e02c0c0d607804140314020781d61000446c940003000210412450f1382090000b0615551600a0f401e1401d0000d50548016282c103500095103101007501150101c50030741488407030700c007100d00c01c0e4032420300b140c640340c6541e00c030b1403040d000f80c0c1000d06400d621005240052208940c5030022807030311900618003413005807 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 928714622 1250 928713372 928713377
    0x100302150306131b020106050301060302030c062109160608040f0b071b061a101b140d1e0504030218090109020d0308060a0f0b0d09061b0903140601080607 68
    0x20002d034882d40ca2280000d105000da840512842c4040216001101d11032844400075500b01038000c01d40c0c1c10144642c40407a5001401024424012003d229450b44000c03821078002e10300d5a4403142c90b50301d81c1815070081c500500200401c88911200009580894015004102c01c00081c00089414001e28480c507603081b0f400b109807501c44100a594852035103424544140c01c10302d035207080c07159542c80921003500411140210140c040300b001124642c04201001240c1c003003070350035444a200c54194000c00c5c40750498800d00c26407800307401c0c41c01000181c410002020028403041541d100d90711819124941c0c2421030074903055900061106110f5100b80c20122804400070b103440100b50030401049802030b01d02c82e1045501d00f001041c4160854005010702d441c00301c0050581d00c400c0c90070044030004558141445d0b0741c0c41c01031024008220307003030342c00b10b4441c2d40b00800d4816541c03031701030054902c0d12030b00e0840d4514600862641e420044401490300582c0c0104001030010030126030000151 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 928715872 1250 928714622 928714627
    0x231e13050105183303010515011b05031608090a0801020a0e040e12310501090306020306150d0c0e060a080115091203080a180804050d080d0e01021210030215 69
    0x842680010a040e082c07100c40d0701301040206000b82050701d040e4010280160003d0004e903455a01602031055040d240a00080c00300240f103504031400d00040040c0c61080003502d180400012038a0905d200d8500f0544005000107620040c80c98950b40020081151900035801c00c0403841c0013401d0728140607080343c003c45d214604411446805d0201030360302441140000e480c6d489038484030340340c0240c281c40060070920880302103c2c0502080100d2040702d50503900c201c500790550380e55502030f401c054046c0d9000b03447c9440c80c2c07410b110040054603000c0d0803900700240e00840c172003005201d2168044107600501041064900301c50307001c424641503800c510074110400155a2049841e06010f90002c561003282d00364900030144d01c026070074003424480400f031006410200c00421803420014000344100c20030001044181082c18500705220301030048107050074610130011b400d40345400d020070a586d500244203282e45c516003032081e4100783c03151f0403140752508640c0400c0092018a4900000c071101 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 928717122 1250 928715872 928715881
    0x110d21140106030504030f17010b070501180318090501031119081c080c12150402070c0902130b0301141c0609050604120315231e1305010518 62
    0x54020300c0c5065204586040d1640c0d40c0c0800a000702030a0358100c3c001032418081e102c085202c0d2100d035411b0803c8007009080741e442e080d40c1003a40d81c0a0b110441e031700e540390004602140e0000d49078200643c0280c071544259a52800072086202c0346400021201d403401c0c0052021408022986d40e8400007602c4444290380c0d103e41c4192a603503503034000c840910070101c04110034050340700003104002d443d0f1281100c07a01c43e808409801e000c0c90000000003602c54001422a003505008507a5926016000501d400900d441d00549100f142e0406440d0680000d040400078102c10202d500400d801000c1605550402081034840201d104040d44516900d040c20719403544441030001c07041c0c1d80b0010800416005141c0692210f000f100d042c1c51180c4484d1001a2050003801901c00c5095031030003014502e41841e802c2c141d158010b4060407d024006010b100c86902c5011903035120748103030002c202c0c401f81d4280800c000711400c1210320304090f00f4000104002e466110814401d0740c3c2c80303c0c0e0040a581e4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 928718372 1250 928717122 928717187
    0x70b0c03090607050a0f0303020910090b03151f02011d0a020102030d0b03151303020d080c0a081f2319060c141608060f0609010611010e12030601110d 66
    0x5008405803d1032982c0f11b02504040d01607004100d1440242c030081214100c1d20400c0e03c0700c40c0c0d14401c0400d455010000103820481c10b01c503003200000001c000c42d0300c0300c4086240c1c000c1c041d6070700010750243c3c2d03444581e088100c00c010303203403880d10403000000d003586006680000c1d00e0340a5801c640107080c1e10384800d180c10780c1d4180400811440742510000c218079050400d4180703038503c00820780150044080c10140c161217402c7ea07a100384000603c6514144c60918115099400248181c03441c00402c40740b912840341c1d04081720005c00240d442c0030f41c001b00030721081c0843c10251200d144038a501452110203030380703100c40d140100c0b081410300681107141418071700158910066060200c1c0122140b08001030b030030b640004240c505031022250103540d109400d075480e00b03041e00c03540d5200341c508004100c0c0902c60585804240402030020070140d0b0810001352400c991b1081e0008805804000c2004650f80200c1c8001d4080f8580010550700d0620700002c1c00440a01d038080c1200c64002d01980301000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 928719622 1250 928718372 928718383
    0x51e120102190917060f010b0703020102090616140a050d052b05090c061c021e041541091504030b0906070f0c151409070b0c0309060705 60
    0x200038004051203000e002a0080001e402c5015607004644d0007500710304c0c4400c00003481d5110f042e0140c00c03440b0617400c00c96082107176007000c0021011903408000300c04580e11440c2c041c00ca0301c07032108100c0f4070908851070301d00603408030f00000040f00c0e8071002488011490004007000c40c40021308000b17079181142000880c06c00f00c55941c0c5036900c00280d190b030443c0c1000741d1140d4400c842c100c00703503a26402900c040010342d22840f0200030150701000c5d100c00c001e8011ba401030480c03002c0d40c403600111080032030604019800950010481c2070b0391084850b42030b50842100300308500f504107108004034050890344c41d0b50a0007107136448864a031002103a9403140300c10440c0d50304c80b0000c1030503c0d00300c2c0c1841100565030007800300300c5c5c0513480103000c500585000144240110441d8448003d00f040d100c100b102d00b280d00a4003038a0180041a4400314400e151054545643c1c901400c03803482e203080f0700c842c0d25082e215070080e80101420412003c13071b990040251035002c08111000e0b03540b6640d900301240f424 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 928720872 1250 928719622 928719637
    0x305031b1b010b0a0803040b0a05130f092d0c0e03121803070302060a050a0306050604090b01140a2f0312190504020f0103050405070902030c13051e120102 68
    0x1040004612291a1440c0d801c00381e820a4030000f805203c46034000d000d280010f52041d41640d45c01800b050103104030311405000d030303500989001818900c0c1c0305121050071026900060300c0c010b82e00002d00c602c8903603005022200010400500d090301184c56010207505481800754242e55407144c1c42003050f032052010341c9000f04001c00b1a400d84580d400d60b8110750b0b02c04044101c4002440e01c9101e014100030071424102c80e00180310301e09040f4180700a4485030301c07460719001019980c48010a469031a00042c2002d01580790002800348a4900090018003102003070001380700b018411220015484801c0d500006040080b42d00340f4811360900c20204050300150510600000c10703400356105141c510280f054112014221000c0c03400d03e015001c07a0b0342074602a40080050407003000b95400303600130a41051041080740c411980c1c44101c54100d8100b40c44417914180001100f80000d014070752030b140580400c41d1401101007001004ea0b0080c001c003080507005039040d036040e00b110301c0c2c20350548000c03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 928722122 1250 928720872 928720921
    0x4030c0b01050a0b07020915040c0f0801050d0305071e0204150801290d080d0501140918060a1805070603060501090807050616020a030618120f080714090a03080301090e0a0f030503 79
    0xf00c1203810000751100d5500140240010542e00001600e8034080b80001033f55a0103031030351850480b250b207070316042d01d910f5401c402030107070fa0300e042600503125032144100700081401c2e0002d030a810602c1c01400c2d220a1040f2540b404405c2c411035038186942140028101000c40da130f890f07082c010785400c4803a03006001d0349008940c0340000001c1c01260150b0301c0071280d1421190021035954240c84903020100820151000c2e40c004000100008000d601030051848400044d40c4a0a11540e40c649006215004800000d446400130841540c1103503080000d4a4000c018084103414100800e40e24010111861603001e0a81529001e6440305502c0388061070300b00b4400d100007100d4072550101401d0100301141c500094030200070505100d0541c00d50720b1001550741c40f150740c03100c0c4001c96030260100240c02c0410010441c034050f40e65410300b100020340c800c00e406503c81d89001026011506001920b001d15044148111700040c100c070307082d400301030b1315045c6141c0300d881c1d202c181040d103600300200344203 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 928723372 1250 928722122 928722131
    0xe0310020d150b070c14011103030405010605120c0d08070305040b0a0905010f05090d0312020f0a08010906080a390b0325231204030c0b01050a0b0702091504 69
    0x101c500c80c1c0d0040c0721503240781402e2450480c1c1d10340d910200b6103e140700c0500341d054201000d10401d403d00d86440d100660501d4103070403400301502024110340c001c0d58120b031503070f541d00001c0207541004005100010003210142469032814008940b0b007141d994001404d00d00006460790806004e40c042c0d40141c070a071215592650400080078014003858011140443c0c848c0041d81041e038841c00c2101c211712000f82031000b5401a90340d0585081d40705550b40040307a5001c0c00b13030a07000d0302028094a940368030f9668a80055140c48821000c4a00c250400c0326690444c6441d1400301c1c454900030720004a00c2480d41080701c0068a0750540100c05000040c41e80d0207041000600d00458805140200c0000712101d026110300748880303841d081031100c0d013004282d01d02045c0e61100c40d200945001c507410180c14a01d0150f4000d10024600011a4101c020401e03281c0c10301c003070100310405140503000589003200094204070800d840c90060200003440b0384c010300000303a600da00e202003840b92440060018030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 928724622 1250 928723372 928723387
    0x100e060f040312120204030c0509060301110c010c170106080f0a0b06030a021b070503100c020c1002070e0709050d0204090515010308030a0b180433060e01060f020d0e031002 76
    0x43e20b054a54492400098000d00343d40d403007180718401c8404803a40114903102a5281105100048a0003004142d244d580c07030013010900700c44000281214080f060000134070b40307017626010b0200d4a60602e03400e42030240000520049402000d025044004a800d8441960350940c1ea10701070544108a60740141011052028202c2035401416000000c1e10006d1191101405050346d01c9a40e0301c031786a415030140c4180852400254018242e00441e441030381e43c1c0c02807660108886000b80814500145e00102c2c08200345030b00c3e060803a400000501c0d08802e95032a01c400140210300401c0003030312455503107242c80c080002c1008110f21150484803054220b6941c1c1c00c02e88181e40089400c0da50344c9051000142c2c0924082d4a030054000c01c481000b0300b42d0302e850311a0000280304003240c0e0b003c1030b013814081c0c0700070704107061891007031180e140c010880c0da0134035a00d100b0811069114200384850040360440741a00801c4018040c0c1c100c2c80c00c0c1849843d080002880c2601502141038110320028060 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 928725872 1250 928724622 928724633
    0x3020108130f03021e0a0f120c02060c1c0504060f05030c041d0103030f0207032d02060c010b0a14130e07170a02030f210702130c02010b03070b0405100e060f0403 71
    0x22034244117060b0780d5684010310000e02c0b0780c03140c0000800405001c803d116407030014240300640341c804480ca20700301400c3c402d00c1d400304105900103030010070140e2005403515542c1e0956990408036810518045042918250002d0004882d0a40326024003d01100051031031502009960042240c10148800441c101c0030000c5940d1080c042517002962001c0e85420b000d0002552100301d90748410000d070043c0d4040362940e1241c0000484100c1c02503c2c2d444000035903146000380101280640c00043d00004030002c02146507800c1d070040b04074400340c9000090316a9001085401d02d1440c000c003042800300c080c0d01e14100913250f0040c54a8450400b00c4803c0d01c100050201580341c803d41c1112400700391340c07403050b51342c0d00b004103800d80c0004c00000b00b04c2101802c001030000c2e10301c06403150444000c034800f40f006844e154801c05006030740da008400316600c2d04101140040500c042040d24060624010641d485600c103180c005004240340c0003005900e500b0110359601c041c0842954603940c40385002d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 928727122 1250 928725872 928725883
    0x9032d0804120b010b04082a12031c09020a0b1602090c1209060105031f180b090c010e030d03090212072603160605090c0a0b0a1b0b0103020108130f0302 67
    0x2903c0c0c030344600380040303204881e402c03c0303c1c03e6694440081c80681da450b0300c500c4e10314070105a43d251840d06203c0312381c4c00da11603a940c0304000c0710305006035407590341028148641099032113840c0c2c001c03400c003c01c440c00350701c0320b11010b015500d9070500c1c250b54142400c402c80e40c1d1700107071800035000001e0004001120007000080c046120b4102d00b60701890311070003074590751a8001c0c001c907035058200004101000c06038441e43c0e00b00c0c00300034001145a2581d5101440e45c0040e807602034950400010410401c580280901e5a00d45005d0a14581610009000c42d48c1c030702e1600259401d240c0d4500d0058190750b92a0f111001420f110740484504544544c0500e042e1001400781e40c8110800c011200e281420100a50b12440c541140b50340305118540c480030301800300640001c0a50040411150440e00d900700c048015089102c00107030340380510310000700041d403e86111507030503004c28141c40c00501030303020040c11a502460455a5034440220800c842441000000c0440c04181c640408050f0040346 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 928728372 1250 928727122 928727159
    0x1207050309010c0527010908060a05011a0a09051e0909100c1403060d1502190e0609011202180d050615010c02090403031509060902090a050109032d0804 67
    0xc2c455851020b005540600074070701003030b06201500040105c01c0c03a018244030a00501454600c144503500d84006081510940300d40141c0b946500040c480b01c0e41c15600d41545c000c4445401c2d24100e4621001401e0b113505000d000e10441c40e030700407001c0b201e001c50201d00d0607500090400303841e4145440880c2c1e45140c81e40c00e8481607030900c051440714500503180c0b08421070840780c2c00f07865651170800b00030102c01440c40850f80c0d20320600f00d80030401d00500c00303850004002440068200040c15001c1e0511102d0011988201c3c0100194011030341c0c44100318281039044803015845440070f2401c00e040f21040980d958000c07070712014807820300c1400654280070b03140140c6c00e20f01130503203540119401e4040c444081c7d081f81100001c14002803181d0f2001741100d040e00042c0444a456980a01c2900c0e0598000c0f00d0326034001c03420003e07601d810209103006103c2400c03c0e50b80d2500d15521030742400003800240c02c010400081101403c00c40001414109038006091765480b078594440d003151190401 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 928729622 1250 928728372 928728391
    0x11a0406080307390312030e0309060f0c01060801140a06050102070311010c0c1e0306050f0405070e0c0f0310080607020a0809040e030d09050c091b1c0212070503 71
    0x81000075620030100440d00810b07000140c0710304100c00030800342a0304803914440c9421110f084000f118100402030300001541c4a00c0140d461407172048002400c0d03c0441c4000091a08200607200b031a42d540400c03101c01d020842000343e00c3d5000900001c2c010b02c0d180e0b00003422035003010b20192076007001103034051003480118003c002035519000120ba486000d8003004001c0146140c3c500707101d6001c2d92116010910402d4800d20954890a50400010100c690380e2152000404140f00700320480c0602c1d680300e150500d5911441c41e00d80c0702d45035102024032440320130482e807038049910214594225803144074550380315036417400c214240f06283d4286100d20b240303e01a60000c2403e991000c955040e10680041c0704600300800503041100420f50b028070541ca6101c01c200207504440b803801100101c0d4060005080ad08003138105000c0124001041940c44003503e032a0340c540c0000701e0b0191024403140070707910381c406a14074518030001d210b8103849404002d8075004102d00d9541c0140110700c00c900720b0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 928730872 1250 928729622 928729631
    0xe032b0906080405101d0d030203070219020d0f1e0804140102011e0b030c130c020c060a0f05030c0702031615030b0a0b030c0f070f0210110d1101020903011a04 70
    0x6100854070303034000f40c4000b4150382114414403003031403407134000241e003a000880d000324070600b4040700c1c2d04d481e406034512800b194010003084000c58052201c0c24a00d9426019448422113580c0041c001d1030205000414000c0b40070914010b02c116a01c1180c07858240101491a95400e800c0041d915001441101030340054070301710b840d440d441030140480500ca40001984072060181e402c6018000003031a894043c8140071803812699682411103a0014804400054040360325034000e0503c076500007841d0041c40108000c0070281d42c0b041d211488400689030840e11b945074882d450030346100c2d894019515115641e4481c4050703401203840b000709c07016240009160030404a060b0203443d000708105078460106041004202a90401560321821856401e8501044165a100d264021044c01d482c00c0c1c010700341000031801c011904450103002810300c040100e240d07410701603484540c1ea0382042000111200403288100c03d40507141c884030014001c1c40341001c0141d45c0f158000c0020a91849107050 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 928732122 1250 928730872 928730879
    0x9010e06070e0a060f200c030d0c05010b060a080a020703090b0417010606181403011805030c01060503010b2d0a170c0a0617040c03020904140c100f0e032b09 69
    0x2401c01d8800382d42e00d945030506e020a8403e1810541189502d00300d4840c014440388041c0390354148809070718100b841d10b9440340ea4181d41042401c6560880b41180151010401c80081640001c201f503404050f50f400569102518601110005415070109686550110300480c4249200b5180041c000b03505000300503007a6903e200716a0340501c0356201d034035900e80940c01e0041c05004001d04941900250010642405c080c600050801d101041614030350404a2101440c9500380144001040101c000344260102d007000203001154429401e649501c0e51640106243c0e0201107508603084000c1600503001d568030050003400110500100d030bd8010303650000c1441c43d00040010030b4894942d0760282c0d82401020141071484003074429288102440c1c800001641c8403644503101307611842a00601c1114140014940400a02c40c64810303a41300c14a00e0710f00c0d5200480c040c1d40541807030411001d0016901090501800c1d402c1008441150070008451103400400c2100c103001e55901d0302482603a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 928733372 1250 928732122 928732127
    0x1a1c170a030b01181412011b051b0a03080613090213050702121201030b06030f0304030c03020f010809120f0c01090f050607020708122803091b0e040b09010e06070e0a06 74
    0x700c3d000d81c1ca22003403c030f6540082030a001036222034200c281c800014401d80d840104045034800c40c0c8180340042ca0015124ae0440d21032140c0032022100c007001032003c0b000907503020384010700081065000701c1141026804200c0b481e00700c0b045098028181c0c840003500302d04c9510103448125039040c0940300c0c1400c030600b07428a05089510301442e26011409503401c0d5034078034400c4000544026850710030702c0d003082400d420510090009500c01c40365500b502d8074500c14401103019034900c06043c0036500c401c20501c484003080140841e48080b84080c0d4403690410340c0c24040c00758075241091507180290000400c040ea0f0700c400e0740c0901030011101103550740101265510518000e44a203604001030001080c601800504412001303002c0e08040307042070300390209a41b40d1303240c0d010001a8403000c41c40300744014440186c04500c940310402007050b05010300554550000390005140001c0303140002d81001082d0701400400b41c1741c1042d5103041c284982c0080494921603240745c800c0c40810400100741d030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 928734622 1250 928733372 928733417
    0x120e070803090409030224040b01090e0c1306090e1e03070309120203031c15090e0a0b04110904050304150534140706031a1c170a030b01 60
    0x80d1490011442d0007180000d01015054201048041d4414007500c02145a6220105c054110358031413412014540750070042403180040e80020394085c41e11809598254020980032030740c000075030358144080c104000d402d0080503d41e001c0d15000749058402c403200302d0041000303c038001d0583c90b004d611a203070f61041074481c40303800001030101d55500d904011542056650741002070008017075038107100ca1a080410200c03100c03403404079540e5031500d002200c0c00e44561070314003070000903204026500e69045025955889010007521901001001400300038100070404e440e0308004d40f4040986c1003514059960b9045805441000e20240c41080681d078030400980700c0800c05400e0043c086241455840300810304d101311000299003178550f0f80c0215294089164a58100b103000300701561402c42c0c010201c80c450902e41030146401c3c01070010315910544194040da41c03c0d42420038184844c40c0c0810007045640e921801058085900400706401d60300c001008202a01d0314180102502c0d00405c000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 928735872 1250 928734622 928734629
    0x7020c01080a140f0a0905030a0905120f1216120e0a060503090703020111030c060124180608090a050105150406090c080a022d0304141b060a03110a120e07 68
    0x410f003000018005110340c015040d0881506034001406a60030b8861504646c80b40c8080e00104155980812640c100001c4540540703a418000e0500d42c0440b0704003680b1101a101c40f64940c00c0c1c0840c0d03402041100a1a0a54a65010b00d1088610f010207074090403441500340300d2481842001800100c1502503021a071041686802804a8a04540c0103441e04c04007022035108a00c0144401450402d04110f100d018000144048036002d486000c04240032100000c0c440400c02d49101559028142040100036204e150924072596590040d003149400744202d805081982401c00340882c1d070440d07c0e4a45040082900e090028036220030001081d500002c4d0341d0320004180000090801801c0d40c0074010420116450310341e04aa46c800148003400182c0100ba03802100100380300c01c102280000d0003500404401920b505001010080e002005410009002c0c000c00152004d1480c4641e000e03002c941814483c0d281c03615000c040050029010f0f02003947c2c232034600ba4030b50140010018000c0c044 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 928737122 1250 928735872 928735901
    0xc03020d030f0204031a060a092306010203092d0d33062324131838010309050307060603050307050d180b0c120307020c01080a 56
    0x1103a00a29044000302900d0820010140c0d0078400480058240c031400c0d2a000401004402c190800c03d08104881c0010b60080002a1074003103070541c641c41e00100c1c6400095640190790685d038400005078203510542e822642d011151140740544024102080c0070b840c0300355000c1600301c060720001d100e80303c009041d02810301070181c060021031901031203215142e41c441818440480030f003030700003c2c155002e41c0c00007004c0d1a041c9501d903032250741410300f0b210307038040856a10346145180c803442184c40d0040700145c6500303100014818003e400380c12420008101c0340d001503a03407002541c81e890060241030500208001000740e13400b501e210340c100340d4010421806a09009940c400019402407041032401c03030340c5000034400c51000c91000c1c4140e8005501480183d991218070745440b905041ca41c142e018140020002c04120b4440740c5d001030416982d07012046943c41000410a901e0702081c1a080c1701d00d00400010041003c3e40400e070421140d8080c0c80b0403149850b0019060f00740e03400b16144051 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 928738372 1250 928737122 928737133
    0x50a0e0f03071103030906120702210d05060a0b0327030d06170f060703020706090501061512020c03030403080a090f110a080c030a020d0f150204050f03210d060f09090b070c0302 78
    0x230080706000c40c00d41c100001e4011160041d4200c00d507410940c40720901c0307440c020004118401c0c816424003580b648035004484504c0e6007801c00075800518000903040f0000c01d82900b40e0301c2c1066180c0b2441401000c6044200d130740341c46400c070720b040c09415180100c0d4640f42280d40c0e64074050384002002c84ca102d9000010b0903566480200c02c40007500240020b6890503201c03064000400c03000c0c4542c1c006018103140105181450080242000070756044100344280304209000034101c020040e650050307814039024559407242a01540609608040079051014194102c810000082012010810141c3e4038090065951aa00b030701e40d0840041a501600f108000000502e40380014000b218410340340d0581103415500ca02c250100702c5031160803010b9000030244060f103040401014004001c500810781c27121405901000c4d04410720076001c1c10940410b5040041802da00004060041000054090b690300d21a9101401c0c2c10b2030261200c406200101e098144112440079049800d40c00625 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 928739622 1250 928738372 928738387
    0x12030a0e1c060e06010e0c040e0402190902030a0e0c01090e0f0601260109180f03030e0f0a1104050f07050a1d150d050f060112050a0e0f03071103030906 67
    0x1103620241c0d544001c50303050412036040001d4040c420100c1102000000b81165030400144010800e0044c1510340002c4041c401081500781c41884254030903810388000092051441c1030350045070302c1d5000700c010540084200000e0032201e17400031411002b400107c4030755500b100010343d11021035004104012403401c0010705000c40740b00059400010601d000d00228103464802c1c0172103000c0031462301c400c004a03401040b5802050243d40d0403100c0000010309205000c0c1d6648171070481c0d0320001403c2c10385070f0a0840d0710102c2031004016500300300040d280301c0ca07000c0ca460003c4600c2014094030075890080450305a012001c5941d2051066031559454190303481420354a074140c411000d0f07500c0003203450000300d5444209914001c1c800020706035449444994410b000c0e6100103209000d032044000c10081d0b0740c0e9201d44011a2440301142c0095651103c0c0d00803000341c40c1650000d4158400c680d4072240c003503000001030455078007410ba4811150746106c01c1503100d00c5601080355114a0330302050 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 928740872 1250 928739622 928739629
    0x50402070f1b151b021002300d05070e130c1215050d080c2b08060108150105090312030402030f0c100f0e0d0b22081801020a060908030612030a0e 64
    0x403200300340040343c0704d02c2c502d694009202e0b0700d1020842d000582065014440c80f50140040190010414990200400e070180c10404a40210280d10300e0300342d168004a5020350061003180703407446020f800008019010254007000e4150014220300040c02e0060100d0710003498840d084104002c460b11001080c84c100801c506000c8603141650015810001036481443c10042a4105a034882070b103a2105501b8545000c0f0842064800f410302204608003c19a0b070300c4290558040740e440804103000e100c1c40c2c0125124000c3d041429003500c0b850180d030090f0344011000e548954800c908840c40c040b05000e1450325105a00381d020707007082001c4c0240442c0b038011480c85040f00060b04c0d145102d00103c900140c1c100125070019a510940340e4180305030100510800041c02c03400a201084030000741d40da400d410300c1503100c1c61045140941704030f00d00d0f1f03100f4040160f04a0f080517007409003540c9030412202c3e44e0300c1910f6861203000c450304415009840801528041091134881d051000d01c4030050 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 928742122 1250 928740872 928740887
    0xf0219020d0c0b190e240c0d0c1718130f0203010b0c0d02030a0203120a022503030b040b010203040512070b03010b0c0613020f10030f1406091008030a030e0304050402070f1b15 77
    0x1071b0007030301e60502031800c0005040082100b40b8280e50303917540f000205824808000c4400c0c0ca010004000100a803406a60b464116885074203416a071000041981d4410346000702010406440703003600000002504142c200003500301c01e22001c098820410820005030b80d00d100b0000c02c980581c00c103224025000611341c59040e4009040880913150030b100c520f80300072840039500000e81c5a01c41c03c200ca07050603810300c540c0f420840b050310100917031244900040d640b40100d10419200d00b001114041032f441d01480224002e00e601040d0310344a5842d46034401c5241c010243c02441c504c128000070708032110702c60828142d190040c040d5000c20b40030300c0c14041248001c589000503d61281407601a5150303600c00c8070031001460807081b03182c0c00d1100421094240141044103817410030340c01070245000c040704840f045451800c00003907075001d0000c45815030246620582d4003a00c0402e4200074484c03000d02210b81a4030400c0414041e4141e92448070000c8050b0107000c0c4220008020107090741d01a155 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 928743372 1250 928742122 928742179
    0x60403140715051315021e03040f0b09030403200108041112030f04050901080609060621160e0a1b111603050106150f0219020d0c0b190e 60
    0x1440c050500b10401540699605907040140305030520460070500020a402c0b080c984244d9105519044000c980d03602000c6000e0001c507184400000490b007085a0601c030a050f2035488481544603103409a00179450f50090300c400d44222a155408408100d224103100202c2c10050711002c1c06511a0b845115078100c01406882d00700440c40b00c01c0a410100300040e00401445401195646061000b4044003210682c04001c080d8410703418899000b0021484661100d4151542020004d02071090441d4050200342d40703115002d0a010340110b89620414141038500d209444100707074844c90745500484444102e5140440c0c00d02c1040901e5030310899040072402d84034001c4030050b1640000070010044103500407070325070b9500c8100300601b4000d04019918110700342449001c83c003134004069121070001280d4201050350240324021561900c0000e03179510707000500c501c010340e15155101415400b0449060410401d0780d07180301024851543c2045403403003d84440300c550384404e000c4074050100309 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 928744622 1250 928743372 928743383
    0xe12031801150515090d0807080412060f050105010e01020a06050702010e011503030314100302040b0103060b0c0f07050f030a0b07200c0405060603010302060313030e1905030d020604031407 83
    0x484400c540e1109020b82e50426031203500b5035003071074500000c200b2001c200401140d83d03440d040c003007030132595603d003940d00c11a50055800c03a0303a00d070036260580315441a40c11510f03841407080304540a20509502825940c140044108401e07622440151030809400500d50b0050b0f10603036481b000611141c20a0b07800401d00d00000c81c05000900c0c00f1820f40e104a060401c01c1c59420000700b051503458041c41350101e1302006007403a541441400c00595403000d02019002d680c890802039040c1e4403950082d0024000c8411071516500b10400b410340715040c01d0b094242600c41c1e544045140d28005601032200c1c0001801003070741c01000e40c2c8002c202c00008041000b849040c446a0005c603800c100c000c4d0601c3c055001030000c95009038100301c1101c801500c03081c00b84406000620068031800304983d0005c02048214010840515044a140074a000030130381040f042d1045003200301d8641c1045c2d0135288201c1c199400a18025000ca943c4c1004440280001c3c100040d00c0700900c0c0020000c00c12503011302e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 928745872 1250 928744622 928744651
    0x10b0307120f1a09010b09060304060c1b030c0c05030601152304030f2609010e0312042c0403022107061b080702341805090f010e1203 59
    0x5071142000c0319110400707908802500102c0c80c5007803521400042c0541b1010401c141030140b105c005c9001408010401400c8035583c10900401600822100040e02d10100e18588900c1c0b5524004202c00321003c001c075501741c1e9280c4040794034130700894414141c800546506050503a100340403100780205803241034105d40c0c0300300714007086081341004001941c041c440707410080609203002c60001c03098042c400390000170a0281607041c0310714021148a0032003403034800c2ea200248400681403661040d003402c4a100002400200044000c501e48402c0d0b15800c1c03901e13111000041c1024070004120740090040c0c0004c0c00c24516003406a101241190b8084400c0d4105041a5070f00320854000e014600d0145114150030320b4406c3e031151050354003803600d00c06411103001211103800c00100250b640719068103000f110f500d10040c070740e1109000306810311a155a0350b9540300b108000300002d45404406014a09504c504c1c6001401202c05a0800900501d071000607140c0250040d04082c16607410580c01 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 928747122 1250 928745872 928745891
    0xf070318050102040603140a0903021e0c031f18022b0f0c0312050712110307081602010f091a03061305040b063d050903031306080f010b030712 63
    0x3d00c042c10141140340c50004200c80c104000350b4456500074210000d00e410040301c040003c0c1d01281c11140c0d4610701124425034440c043c1c03a1814584817001d0700790035120f080e841d40c078104810b21004582c41074590042201d810461040001c5200504029404c138040c004081d08005841407510740032210507415145150440d9a015880508107005a41050440c1d01c00e100b84109404540000d40050612625101381c503940d4a00302e455030745091060051a41070400301c400c051045840315070780100c5103039586a44027140703050492804c209038000b0345041c000d441d01500500c0e40f00242e40c803c1c1024501c0f0142c450207150142e01c02001c06801c5100005c800005e4103442c00b07000c0c010b0f03102c1d00c0c1e0030004e49410820b0042d0b10811590344000700510341c01d00c200c0000c0c000b00d400c00341e8540314182444a2003082d0242c4192240c599200d4040c4000180c0110007001c0c1c88048040e24215520400c2c00d8507284290314001740e00b030191030001d0300d04001048100780a000b007140015901080850040719 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 928748372 1250 928747122 928747133
    0xa050f010e130204090b0d050d080411030d02101b050706150e0f041214090f031501060503010e0a09030e060a20010c110607092601060f05180f070318 66
    0x482c0c0718940081d4000c2001e10840095018114610300e050b107111805880030b4031400c2e5a01000c000310800d01c41581d02140601c503552070184a00320018080340c000c10740044000b903580031214000b0031900e10740100700342c40c62428081c40e5140401c1e5070390941440003d4456100500890b0f1951008501e03d0701c00003942c40787d220385140b2840985400700e000d8541400c141d0300c4152250540c1041018914882d4825024070050f50703400d680c161240d804013502c1e0000710b0715180504400d01000ca00300e000000d01e40380d0050095050790090700c40c100446c1c0711104c015040d151071210003404900a89100d0540d42400340c06820f898107940742c58401e03800c0045016000c00f00c0c8940c0350710543d4484160341c07040e9170000d03800c242044196008007690301d40f02c0030040c96520710307018141d01d070000c580075240c101404003001c1019a008000030020169942d013032207481c42c100c1c031829016080d050607410709801000a1584514403008118005a50b00da900b14000d051590042d85509074000c1280302060 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 928749622 1250 928748372 928748389
    0x180309030709021c05012103091205030304021005040e010b03191e0c1706010302071712041406040b0c1606020d1a2409041b020d0315050a050f010e 65
    0x41d41c1c00d0040c4e840d0000f060210160a00e07649480709030f402e040040040c2c614862040030074044018820b0030b00b00c41d515003190040801c0e8080302c81c44014801801c00d0000210085000300e1086038600420383c2580015110341c000d03403040c00064240b100c010406113030707800300559001c141c03c0d4040740b4440d144125142182e078681c005494000183c2c290710a000c06034440c40880b259141001c7c00f440761600503402e84000f000b41200e0405402049180401802641c00600c500c0840100703a220005036803015001c000840e0706941150404030207400c0300f2408180d5074001e0b5009a9010340594076124420039039070041008244201300c000d07090700851800d10181c03880f260510000b09030310030711b4109808180035950700144074903100d0401d41f00b070201c5188505892041103038459281c8032000001001010711617001200c3d4007012401c103028030740c0810a80d20007940750700d08020984840c68158941e445600907650080306908003840186800105000000380501d8003045090450740400c0710107 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 928750872 1250 928749622 928749629
    0x71a0708091b0607021e060f0705012003040b060307050406031a0a06051305100e0c0c1b0a0b0d060b0a080403020c0306070e060702040f020c03120604090b1803090307 73
    0x1406035018841248410300400c001c0004008842042944040001e0030f58859070400078400c0300c0680d00840170503040c981d00c007500d141c004c0c00c890705d0340e07000d01450380c0030f1340014400c0312a07501e4010b003034401c4070010940308460020016114219515070b0394006481d02c0280000da81803160090005495945010f5180034620400300c2080350302100e544008400000303441d1800c59410040180103e80f100444441e403110304c918007091640701c51003800b034031000c1e5030803500025924100700100e4494040082099483c0507049403c01900e4107261034511110004650f40302150ba0020001d043d03902c3c0103001c980b907100383d000481c1c13981d54417040d1040d4081503821010070307107217410481415014030078403c1210007540030389218a4550340c000d12034442c00460074810403000c6241420740d00d0b194800f21240111040455441064000d829038039000701d560040382c50416400502c850030903008101040c0d0313200e4642000d540324404410420a8000c5800600b84002d200707003107140da410030000004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 928752122 1250 928750872 928750877
    0x30f07060b0109090c200d02030a0834080a090203030d090311010510060212031902071407032006181002031e0a0f02010b0a030809060c120c01060509010e0705071a07 73
    0x5a403804911b184010310142c203003400c00c0d0029002d021004e41c0200413210700094510784290346641d01010035201d11115041c01e502078000903020301c10800e420b000210381c20f001e42c90301c80c0e049c0d6907041140f095940d00100290190024020366101880325002090f41a202c0d04055404810130102c480c2103580c00c07208402c81d0104c68a0810140c3e406002d200c03804143d401405241d0b01c0c100c2610310400d00f40d6030308030a4141d070000b03c02c01440310200c10f501c4804802000c0c0e40080e0f3b134030305140140c180d18a020360f10b014404090b6825a107480d40032181c001903c03450246080303114600300030310010103104520a5000c00c0011302d0101d000301303000d0510001107040aa441e030101002c014842c00320500c002083d603251030030b11041561210b00c444101d0340d1003440203985051020119030180a071a820001622403100c04001150300035002e01060604100204406941c441c00c2103035a110a03c0b90740c0c0300c3da8005000c1400c05209400500909010f204048480011600c0ba0004420120b508100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 928753372 1250 928752122 928752137
    0xb0f07020d0804030b061203040e13050d02150702071a0901090b0a0c050606040204060e1519110c01081017030421111e0904060b06130e0108030f07060b0109090c 71
    0x40064008070150000001c2c0da07d044c05404d00f54003070b5502d1149000310981c509082000941100c041d10b8058042580b1030140c9000c1c10300c00c00c000e9035036412290b8201442c0080d40000f40c0c0d45100040c005c04441c104406444500b00d540c0c006043c680c08800058100500907801003000d132105001000040c0c4950764254903a00c0c0d90410500b002000f4114a216500400003080910b6202407004a80d000845240012920040e43c010942c813170b019210003103c4400301c0f40b00c50f440c0c004c013101d5948a50300b020798500310074641c011120000c080321411882d00004c3c1080c00340b030001c10340310596112050300300ca1900b502c440c404c01200303017018000250641d03000441c20030411403040c1a0401d031416a0b44150000b0741c9078200d03881b1b0307441800782801940f402d0b0020b41400038540200311038500c0a001940d844009202d00b101c8420240101c52111902200009070194000100d4a07003406030507a4504044155480c00043c1204c4d16040c2d0401030b62150100d205c0945200d9035460b400c1540341c011 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 928754622 1250 928753372 928753379
    0xb04030f050910030507120f0903021603080f16150504140a0804120c031407080f16061103090a0603020921100e150a02030f0109150b0f07020d0804 65
    0x41025240c0c00140c020080c003800300b501d0b03e44400701507260444203401d01150580c1e07034617000c68000c10b00186450216050200d49013001d0181e90011402c1c0e4000c0e42a10b90031428080e8000d030a4840d80f2004010400c100454102000c008018000c031000d20040d0320040c16064445072a9003200e80508044a81d48106200402851810680001c903c2c08050721502c12207440f410050301403440b078030381c0700011000c41c10100b01d0f0010200c00038641c0060b60906040345504980e641300a03500a001c5148a218100503160350001381d11211800c0140c9602d5100d03040040898500d100340003150110f100a001c4000560780350744040002c0d0460759001a222079400d020000f0007a1100c06018000781000003900340c011001c121036030356220074a030204041c410070081c1894600d541b810500c40000c4041404842006500150301400202c003604045903240e101000840d089480301c001c11410f130341002c010302c080c110082c002200284204500748140b80d00821900020500220380d070000000d01407 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 928755872 1250 928754622 928754627
    0x1090e040506071d090406021b03031006080906100312031e0519090f020607021f11010b040e0307121103130801060803070f0f17070609020414090d030f0b0d0b0403 72
    0x44c2e460b050030580004034034502012400d02c82000e0f101412943c2c0008010000e03100d115011000701404c401283e9492500000340c0001d4001c0b40107040c0041c81400c0814800e0000040890040b18091181d800c81481c1d60750b609036142040144000341600c441c0745001e130411001040d0b507010725030000400c40c0e10b0000914030085610b508502545131903c811007000c10b00c070754907100c0d4150b4169021544e90001d400010342c042108640314021504006d04080110307400b99280c00c1008490009011040074001040142c1714400760300599540140150404238008111582c08220b640c10a0045c10b01000c0129007036521490b03445a401e00c0e0408104011a024892180106024800344d414030104c2d941c0e80914505103880030b42000501e2074240188030300cac20b5451040e1040301d00c003a41d983c00103280c860040c0240c22000d91040b40703028040d061242071445c01074880c51070300700036003604020440d01390002c0020844c0b1000080d9105901003140d00e0300201040468043c042c0d8000615292a00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 928757122 1250 928755872 928755887
    0x7060f0201110301091431020a0e01231c02010f0314011e0906051f02120a0809010e0a03021c030b030a0803011a180108040f0b04110406140306060f01090e04050607 72
    0xc4581c07140703001d00400049882145c0c01c0701c007401187c40050b0454114000501c40c11155080b4110419075000005000c6200c21000030b2424030b03110544140264003800c104115040650f6040684910842c1400562050000b0310920955007800207410100110244c110b8909800804010705103c007402c0200da214002c2030300811440d0800e0000e981000c001c070b5501c80c2c0c20400c0d911482e8010104082c158024272411444000b0000140d8564442500c020305501e401d4501e00115440c02c02c5000d059800800c0303103840182c060700144907082e00c3c80000a0313140302c000550810181d4688010740165003d10281450030700402d591600c0e5414210794000d0000c440c6400f002c804020403680003903010520135800448824240900d003682e55003060b038480d41108000411018505040000700f00092100301301c1c5460a0310100030068403008603c603e0b0304d40414259061b80103c00040080c034220310030310360700841803600c01c80710341c0d40725400b50070208195400c0703c0345c0d0006010000980d501038071 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 928758372 1250 928757122 928757131
    0x3060e010e071508040201021c050d140403300216110d0b060d11030307050a0b06010914040b01020c030d08250804061104050a0b030103050607030e07060f02011103010914 75
    0xd000003030701e00802c08043d454184000000e12490b0340000c1c0540e0300034080303002c01d089030703144103680c0700c82c45000108541d119900341203c01303280541d0041c1102e105803501d0f2040c0e0385034803032044810044406294a40d0056004006d050340049241c000342124001f0f4103120f0502ca60022011070340e49460968048042101c5000e165124541c1c0d010900000e5107942011064810000074400d84c14030f20a0b080301c40344019014480064900200800081c8400d4a140211000a02615100011286040603104001d0000820043ca1003c1c1c545a8801c103000310050045602001181c0301090800c0011021200441e0800017007141d407440b034215030900956814214a110f001046001d400038038060406402c0310794508040c0329424040007140c01803d8000c1004030380a5440c0b088010560090008560902441010a04450280c0101c1d4000c0501034003402400d828101e080390362012802c1c903101150b40b0b4000c540c5000e030541c0c0045000c3c0c40304260102c0c415140a4440c9034040000c1e0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 928759622 1250 928758372 928758401
    0xd1d04020c0a08070c03020a08150a02040510120b0405070503041b06050a0e030f16260c011107051c2901141f0f02060114180402041503060e01 63
    0x1c8001140702001c6210b0010540c000592526001c040c01c24035000d0070b41e900004c1d040400100041030304240007512b54100c072041e014000040d9100c0d0600b1050380203500c51075800a40010310000114003411882c0f400a511000008172461035400203420344030242d4020020803c00800e00050082070400b600700102e0440015050a2812100030020720414155408110001ca1100d005560034014501d00700808802c5a02c0c2103466403d00c44c0c9040d00380304503042540c01101cac0c000c00183c002d1040900c40f00000181034005000c500545042c0440e14049115004000c40460b09646520300c1c0c2841c2c070410044500307221102d29200030a402c2d05000190f0070071058981c103040c0a82c803112681582c601d5214005200200404500854424901040381d640051243c0e45919030051218241c05460b50841e000ba90741c410501c118505000002a0084000640c0c003140f0180a914a0303007240c8060000a084007500854410f20290354004035079050f242d42d00389803451824061301105c0301c041b0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 928760872 1250 928759622 928759627
    0xa02031914010e061305070203090f01031506141b241308090303041703190f0507030813120f020106060e0f040528060302010207150e041d0d1d0402 65
    0x2000718044980520032000781d1000103001400c140c5403450700b40d82d50214920288064180900041c0d01c0340c1184240500840c0724501d05c050541c824012a944810f542000032141c9040580884042e25003d110180e0030100b00541401550980000365030074500d003002d0481c0003110302115050300e106040b0032030306150040502c1900c03200b8002840400b903001c409596101000030202e0f0650056074401c10354440580207149c91513102000508400d0009104003504180e10f55054986180d002c4286c0005542448180000b90182c8429900702d80c0c040c501038402803a981d140c08000101c80003800001c1c0e05841204601c3e50240105405810303903081040d40000d9000204508140480140d44141d49070008100381c8584c612046817046138800c103002c01070600070b1144001c1c3c241480128010706c950748001030005410b002c9aa11100d159807815010113805003048050138a903e100003040d001c420811405040400008201004c503486a02a0410b403d540e2091015045100d50242d03004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 928762122 1250 928760872 928760891
    0x71503231303020c0a03060617060903120901140915010609150311070804081b0d0f1b1502070f0b04080307120c0b0709030506070c020312210a020319 66
    0xd44409a074000120100c400e90122241001c03860042402a200d40007100303008003005001d03007a08000160f80a0120416a40d0a0320344820b9441104a4014103513801c18443c03000220801011542c00c1495503001040e00207000d4540ba00313044040e1032002e441da0009452a0b20729980030042e83c010429070901e60740c09450303c42c8059203801c60a40365410156903060b282000e56042c8291040c40b074001601c50b0b10380340c50301c280c02c0d5110041441012040881d80c1a002c0c54070f080071020855951201560011a05950f01c46d01084070800814000d094000c2011a9050f5440f000c01c609652a600601c05189846000c0074643d106400404900c0e44c02c00043c0b0440314000100c440161b441a41c0044d140c0d5190001c07508118102001040008500c040c4901c4513840394152054901036010766445495107802920310014408009400d500100301041d1844031032009000035615080708207010346041e403034403401001c0c201c071050181c540c0401480b0b1000759205c87c3c2d080220221f40b0400c082c1382d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 928763372 1250 928762122 928762181
    0x109030506060103021c05011509080a0f080a020c12030a03150506031b192115030b0604090203031b06010626100512010c030b06091509060c071503 65
    0x700511a40c181a000999480303c11800403100c0304219001e08200a1542c4a034980c100800c0e18074180c0340011028040400c00e10300c0812000005a8442030000e6010b000b07a075600d40c80d4100484a0040d809800341002c072a4488052407101f410b220340103150f0380d425501003d4100c8020341c0070200d00e41707440d000074000c5488030030441c2d8001c48003000c07905285e80c0d01d920300b4880e80b01d001500b01403101c0054803218803a400032210101810034400d080c80c2d03035a5950100f0120f0301c0022004401c032441d4a0100003188401e04450341085000d070001c40c006102c2d4001c00d20315071145454000303c11400c1d4442c0c0c6091014408240503107400d15001001940c1213010410070046c80381c02c101840900d4001c82ca040d140d007038031344004001c05400a80740d5040104441c5c024021040108082801c0c407101c09641d10340b1380100c5402140c000c00480700d10386013860880160300030019894021008110704a040d800030400341009203804a20b020300181e0918001702500c551510701940c955010383c2c542008071 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 928764622 1250 928763372 928763383
    0x8010e0c0a2007050a15080c0a0e01030506062a060609190b030a021503060a090b060f0d09170a1d0906010804061523060c031e09060d05060f01090305 66
    0x550074080e14405440030072206041803c283d22450f0f02c40a8a40005040c81a50140300b00350315254442c0003546d40c9008e609401881000303806000104001d00700101c0e503000750700c42500481c010700001d0800300d0482d0800b540e6281c031100c0300c000c0c00160006d041410000c000e40c552010050f101a07001c1d0911100d5010541c2106c1f180d000034030f440d00840c07019520108070f1401c171690010810b4050700c110040920440e441511080d0103601c408401240700506805440d02c500c5000e001c0c2d1b80307081000d614038a0140c200d03c86020740c807611200698089003131100200c1d0140e90003801c0c0fa41d00e01040c0c50260070440220302145100c2881c2c029003000d48d03a002002548203600382003820b1956200e144c000c0042140042c1312515481d40d00340030580429244880004000c0381c6003c1e1a49000742c4204144c2e4020741e4200325880e03200304170b1004041d05030601e0580c10303001c00c0001c83c2441406d00000788250007074151b48400740e5075002048001d01e42a10205080d200c01c1c206648000c0c1140c90f4191a0b6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 928765872 1250 928764622 928764647
    0x105130527220f080c03071a1e011802090a032904020303040b030705090306070f0e0603040c1412150a060504050601080f091e06060312190c0212010c08010e0c0a 71
    0xb03c0c0791007040c0c0a200104045808000e00b00084d039550f03405915103041040c4014106802da240c1c1000040e440d003940440c03127200ca48901c2d0100c2c00503860196124505d4881641075801d2540034031007401c030307a1203110f40e54024611440d20030348800c1e00b000c204941000c501c20001c8001092000380070242c1c4002c006c0705c040e25000700c045036880e91280c10a8403e4442c00c00c143e40c040c0710b04410070940d59401400219103010701c7d9a280010400310003004000c0c0000e50f0084c002c00950a82005213010109028001d0680076028904080d019070300d1a0400304c250f551111500300a00400c4421039281c420380010b40406c80b810806810010300003400003400600013900d50f2031040128409080400c2050203c0c449460b00400e001c3c0301e2000c03030352955410b6409034064840c005089000c2e85140098498400441d40c21140d800b040e41d8088429231f6240750280e80118140c0d41c6071b45200020300514040300c2880d203400790654501a03025001d020001c101c00d0001130244408481294007401e40d01c80f0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 928767122 1250 928765872 928765883
    0x9030403080d09030c08030f040c050f060d0e0c030a0c060201050610020309010c0813080c0418031e0c140a0c050415050f0a15020d03050603060f06010513052722 71
    0x26440f95160542d00d515540340082c00c80e240c08020400d46140c000c00081c850b903c546c406548645d0340700c4c14404034141c80c1c010250300900a10542014004540c0044899408c44c1c04444405242030301083c1002c11110301690200b944400a0200640901a05404c02001d480c0020b02c242e01040c002d4690140c0160603040104a10049086c0a0520306a81d407050481001d03d4803550340b00794441d502c24503070050900071401c0114070b00101441d041081c000c6605074407001d000c0e600c01c580183d8502e4030b40e100301003400000d540c080c1c0030a000720a16442a01c45900401c0f80c5001030400c00c1900e07134251b00141c4614286074080050140c941d03a04011510140c958000e420341d400001424a803290b08105148110350903034411040c3e000454a0078581c150700c00b0005d41e100d50040c5a2502c038215915502c82c0070000120708194400e400500c030254032403020642c03c0c0e440d600018490105036108407540074001c40410000d8a124800f980c0081e0404090199800310070a240302007903910034041c09 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 928768372 1250 928767122 928767131
    0x7030203060a0915030b10080a02010c1e0c1701151e030503030c070b16050a05090301020705060421050921070906090f0e0309030c0f030a0f0b0a0509030403080d 71
    0x8980325107220401403c10310354107000c4002c91550002e2802c01d184401d8a090080201084100e5070341c42c041015100c0840c00740c400c40001d40c005441e15a03500c40d08407140034810b40504036030000c02143d640745500c1a40d91080551400b0208110b80c4001c02d5501c000d42d240000320316900c244188280700f01c60000d004070036a4203102002d400303604107035030015003140000001c10450303090400043c00c51030b00c0b8440c440d0840e2a0f0300c2281055804055156011500421145d0700c058003880240040c03c01c020009460309405503103050828105480840f030101401d103d0864003a659100030600013010b2902c2070030008148000341941840b1070a402e11190f0396007400c15001c01c240406009437023112001c0c4600f560b90003080b00100f12804103103a40c0e525040d0020b0051070080122000e18400030010030403000108100030402c04000500f517030520454208200043d04400341d00103460203100041e450b03181a000f0304042d26401031500081d03820800c0203000056164066804008000f5400034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 928769622 1250 928768372 928768381
    0x405160e060c03030a330614220503120c06040b130c0b031f05061c0f09030c050616020706230304050309030114060112050a1d0f210307030203 63
    0x14003900c100c0e103041202c0d000000c100000302c003064210920b06081c02e041038096010640c40c514003400c440501d04091512020200040c52080c000440200b06280d40c0ca850904004001e10a074040d4110354190414031640c1000a441d0a00c42d05030701c0c00d0184140307490140424180c6d61900b1005000a0100040c2004a2031011808410018481d4401000c1c141e65860303020080143e0000c40b4804103580a00200054451b10390810364101d80c00900300c84d00740f9802120503051181e4042e070740c911075a959041008440020f000b103850700780c000c0d03e504410030864107000c0d0030b0150043c1892038050a1070001039405500003076180444800349080c8a0790081104e91800780c0c1d2517841c2d203800e001c00100510040c0702021000307240b490000c50080081819900d038030b00340c420b8212800c1d4046004c24481c2e0300c500e040c40e04001e510420001d00002c0441085050f03450070580005002c80d56405100c210031001c4040051a00030b0040c14407046181d0310900315950144001401c42003010340210104 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 928770872 1250 928769622 928769629
    0x2010c050c0904231609051915051201020307020303071202120412111203060f0f0307091e0506132d05090d0c0f021c1b050f0405160e 59
    0x74907060200801c20451800d05050a40d40310000e0511184000d4480340484050b000000342004c0c800903501250392480d1030607240c40300520b802841c000100c07100d251308104150051103840001c0c1043c0d42c3c1300030061300f001c0500c074590002c02d031101e4542c2e20410a00200603000429039034060041d14149441e034044038000c00181c02a04c4c000d400071041c05051201b00003001000b140308540725a521000940810545907840c103410440665a0004001143d828100390801e44503000c0702a00c08c42c404417000b8041303850b0040d2507100b20185076645100e0018080c08a81e80a4491a01034040c0081d062400c001420648030b034040c1550a60f0ba00084508007502a940d886031584450310070890380c050b60000c001070b10044546400074041c01c10080c8800380201100748a0503000802d510540100c0c0d828480f8100190b40d24030390000c107401002c4001a500c0d010110702c00303000c0402c1200a4075190903c020600c04d004140e04c12420f000c01c20103074000890798100c4884c1d403454950341084450010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 928772122 1250 928770872 928770883
    0x150209011413090c03051005122d190b13150911030705010309170a0201060b04081b01080106120f0b041409060f01080d03051b04151206050d02010c05 66
    0x62815808002c2103000e01d0340701103441c0c90100d50307042074140107003800440114102c450486500c12400040700d0207201609240000402900c42503040b40d2410940308100407003e503494050700d034004903410042410140a000c0078400c114580c0e0f0100804680d682d403001c0caa4001032a00c0400d9030f0001c85481844664038040040c501c00d20030400803c015800c00f004004030710459103029206075400080c10794403a20801050175040044d00180c0c035444a604a082d0b40017006a001315901c1d2540402c03050410700c020001071240f00010300d0b40c00340010342c03000c0f858202e0000c18144401c07503004000c0190880c2c40620003d00358240080c1e00c0c00303a0900600280b84d1701c241980c21500d000c4d42101641c01401e00b41e402611014112101d07680e8071201c22035020801d0050070125000300049440c9d41340039402103034221400c811454014641000ba940c55500543c2c0302100303041107111310302c04492308644001011301e20030100340700190a0601040381503516000090400c807a198a8005014080c040d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 928773372 1250 928772122 928772147
    0x90e070912030c0605060a08031b030417030a09060e0108070c0627060e1912020a151a0109050f010f03230105100c020108130503090a06020303070207050d15020901 72
    0x80c1c412080c00d5040050491107106000c65446141401103401da04d8402d030034204031194840250b00d014000031440682c110391040d44200382c0310a00022842c01425901c400c405e01c0c0d0100290b446888110009204085907884202440b45103c446201a42d000d283e560784816641000c404505452a0501c01001c0b100000c9003a48681c07603c0f8000444403000c0011280e01404052101010032881284c84940c140d00326034204020443c140d0005012617114004002e090050714040460b58480401c560080703020150f0341c5a452201800c106034205510f400d089080c030b08901142e0030500072405112112400340d05104102c016890000d1181e0010000c140354080d141d42210106850205405000c3c02403a2040310402d04e9503130740714406e691541925030140c0d46d407201501c40180780c400d00c109061060303445001c100884c0d401c3d500d61813500e1000340a00d83c0215501d1400000c000e052907444c0c1c000c0c51107036050015005c0403503200300103150391100810740145c1d19441640143c0e4031890110 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 928774622 1250 928773372 928773389
    0x15060901050c0618010e0304080304030f050703050a0f02010807030b240d0608030903070b0f030615040509090706081b070b0907051507060b1c0f05010f0f061a0307090e0709 76
    0x50801080a00004e9450403159081c002803259100209840b51a801a03004003010740e88203000c100702080000100e1015580902c081d10101502c80d2070faa810444038010640d0341d00c20005883c011940c3c017100141d480b41c00c0d07183c1041241500000289a4030815800052032008001b802e0b030031080700c1d0110340c4281d00c004400c02400c0d40d580013141c0c9a80040701040d120340150030700001c44850210445e440200c00c00715079840c6a17102d2040003203054484840810511007840003244c980c5070110583c0c016192103000b450050714102e001840c141d001000f410201d4141e2045204c80030300101540c0c58254070180c0056160b5030080003903e410020751100b584682890040c611000d2154018007403140108002d0044800c12018003054a02207009481031166010050700030600c180364446205200301c002180140d414a1000254bd0f00942a4095107503550010005403d1840c9483d0280e01840d080704d0852412190182140015201e481942d04501e00001c0c80c1070f224103c1100034080d0007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 928775872 1250 928774622 928774633
    0x1508040201022401030203070b0f160521090907091202060c0c270a0203060f010305090a150609050a0b0a0e191d0f150109150801050106030203061815060901050c 71
    0xb83c004600040b0203100a03030187c05800f1001c00c00141403c100d50401c070a07030780864a0040803100d20081da042c1000c0039506401604011200d60441010902003000094807060321045e481081104050001c0e01e02c070305100284008118003140e11800900c071a07012911540c40e1040020400d080c64001c0701c985034001500345001512440a49001c0902d190500c1100b0040d07031220701b020124403054542651010172141c902c0810340c402e4110070b9014480c4001e907070b2502030030366991054040c0d13500b50301c0020761a000140501d440a102c1d040d4824106c0768140a01003016000c51811300700c41c0110924441c14400050780d002c030b114000c4000b124000010403e408501411011220360710307058440d94003504c03041c80c29204001502c18501c0003031503000708580c2d02c1d040c25000180010f04000c0580c001c440c0002519000a04c5a40c1c0282607a44001d65280340c0f007410002403130816031859070300303d0300351003444403108204070502920041a00c0b12940d070b0820400507100c1c0e01605c441d00030b4a200b40d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 928776978 1106 928775872 928775923
    0xc19080d0906020915180a0e0c0a051e0d05011403250b04030f030f08040c05061602031e060603030403031e03110703022401150804020102 61
    0x81d0500500c0c009140005c201203000314512601c2c0c0540100ea40c0c4480c01c0c0c010104c840061084034010072031801c3c0440010070300c2000d0840300006401050120001d8001c004a490b06280c41258610b00038030f100b805840d84c0c0c400b52018813464100400000e00c03d1188000c4117a20038005d0140450380440c1d8a407080c848c015001c5100f1a00309000005601511040184060350041c00440002441802d01405c0d50050005c003200300311040b0200008038a00014220948400310741c02a0342d48a030009094503492917120103503042c0511a81030343c6000f000d80d180003000402c0800da03202d6603201010580c51f40120304c4003070003240843c040d2040b0080341800d0400440c005003000502d9402080e4254010703045104120301503401a410041020341c5106081301c0300903000c194001a6051080d25554610381103061818043c0c15408542103a00030b000601005200751851250fa111 = true := by decide +kernel

theorem cover : BRFrame.Cov 928597122 928776978 := by
  have h0 := BRFrame.cov_init 928597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 928597122 ≤ n) (h2 : n < 928776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
