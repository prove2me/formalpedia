-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5023
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:29:33.00072+00:00
-- url     : https://prove2.me/submissions/fe5666be-9042-4810-8fef-696d9f93a488

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 903237410 ≤ n < 903417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 903238660 1250 903237410 903237437
    0x10314040321020c01021314061215041103070f02010c08071b051024050a1e0f090203040302190506061516050f070902090117061201050411040b0108010312 69
    0x2c44003041003078400140d101040c01c0c01c005034190000c0c80f6084a51030103820075602c4010041c21030313201d2981c20750085800d001c02c910600c035103c641600003503071070511301f00d0164030f0000500b91107010794080f40b811004400d0040164001c0d0010a03c41401c1c00203020070074801e00000d00d070f000000c008402300102a815418060004030301c0031100c0f500f000030b903220007080726407a1004d88158001d024402c200d0b40c074104a211072081c6044103070740000780f0078080c5514003400c00c2900e0340310720f1400e9964410013030002880001b00b183c140c020040704002603206d14003418060f0500c116050b43c1412044815900c074000381011580503804001220052144500c038422a03a00780500c880341f072300e41580c001916091080020754401c8080e4003000b102c4c00c5646406004c01a8010b60030000d0100d44801c249203e400012080d8a41c032140c01340c0314180c2412410703061801d40d20181e030207440244507040c05840505040c003455501c54400e00303100046514640d502d281000d1100e9001c2d0070031007044030006 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 903239910 1250 903238660 903238697
    0x20d140a0305060418030807180305060a0209150a08040b010b16080a0903050a050c04060b0c07061b0b13140c1315030209091b0d05030715020d09080301030b01050103140403 76
    0x18403103410f07450310b03002d100e05e4900074003068010b88088020480c01020300740001e13100d0300840b003620ba01134003912041c1c42d500c400001030b41095121070341c0244115880411282c12034050180d441566960060500301070614050000040c0c00245030a10108246040244540d0705160819480164580d1340e00042c20202c80750015500020460300584900d00188100059030310800501110108455695900171181e144030741034051840307401c0300800300009406681245001582440400c108000517980c0f060381c9001140c0398070640c040e138862a0140a03586e041c14108180300c0000384031590340240040d08012100b044228550341381c060095050300381c80001001154040d200c100c3c0c909001c424140c4940c518070136070082c42c1c2e06e40d400705100d15090f1079240764107401c07102851a110032a110700703074a081c0d0201c0f11503060303800700f024062280a9210310400680207000c0c1c541ca83d410b5213450503110364181d101c9410103042c4007204a40c95080103c85401c01d6041c1070800e6075000400740d06 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 903241160 1250 903239910 903239921
    0x50c0619060b181e0102060c070c03060f020d0f050108070302121002070b0405060702061611010b030304121703010f12050106030213050a0b011418040b0303130501020d140a03050604 80
    0x48205080443c4000345101109180c8199100844010200d100c18250b02d03141e0107001e4207002d00591044000c52913043c460b00050864a0041c031483c0c40041d244d85415064403801e02d40c400982d83e0000303000c1400b4102c2d2203a1003a02282c040180a45c0d41740c02c110030383d43c103001e00001e8407449042100b4500fa06003004403c85545041506548603019800c0a100c805021038013511907004a00001d41124400b00e90903128802402d031140c0c9149842e0300440d0b14082800b071001c102d43da55100342c2901d5500700050402403040b004c0c44100c9801c286450800d00b0b618015590989a0500051204c10701100c5020140e07800406800070403801070a0040c050300450f80701a402c12030700c04050520700141e0708010700c03c08082c08240181000b5800458020031010143d07542c0c42401c1c4406106401048409000588000c1c004500c10014000203402c50f440341d42d02d0060480d0100c41007089503018090307840d1b400f000c2d042602002001010502c242d01c04c5115140c1019611000111540c0d22a4001c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 903242410 1250 903241160 903241169
    0x60804120309050c10120e280308070c0303020d09080c0709020f0403030e13090b010f1d0f090a1403070c081605090402040207060e010b0a140f040905030c1b0103050106050c061906 79
    0x2c0c8190100c0c0089151103d0200414900c0045940890f80710002082308204000b03070b05075621582a074400c2c10446250911000480c01c00da001c108054009160b40100c00109020b400010350311820304103138518284582e408034041c0c1d0f006101014210070a2026101201e406041803400c490a01c80014a00d48204c400800300a150030f80150610400150a82c1a10200c4c800328a040f82c48224402d4442040b0304103440208803003000030704505c8040c04240d04414070b1002c9070520b001a079180d105e4503c04440d07103600c56001080c00401e01010544500c0240541800340028400d040030b0750f02c061000b8081e080c00340c0707104800700d0115103035903040b1000b0940148040080001014070640602000d0401511a500d0310b038020804a1150340c00107031845000b0030003e4402048802c0c803001e40765140042d03690b404240002070710702506200701d0300c0181040e0b01000c048125800094116001a04040100003040c082620369102c0028030582001e141c2200c14841090099000080c04a5820 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 903243660 1250 903242410 903242447
    0xd0204060e070c02010e0a03150905010e0114090d0c030f05180d08070201030501050303090612040503040b07080c061e1f05040606020a1a060d020127060804120309050c10 75
    0x104030b0056800030240c2c1507640b00740d0300ea5900c1c0f03400900b045103101041c00003403c0b008546440c0700c4004400d61040c02d41a05c90800880c0c030041c51a182400c44102d4241203008030128001c02c050300c81c00b4403e6030030052040c2407207400d541c06d6481c010001c80b41000b140c401d21500091803c9480d1001c0f88201c00f44034024a0030380701c042300d441d0840350b41e00818002c901080c1068008100e07480c0100988051407800b8000c242407082211085c0710f5102c003d001a910341c001044041400d6105a004000c1680149021952815006042840c01c4001030980550490a0405001480801d0030580c1c118110103403001640c46040a07200c5110310960040707521602d0301400040e207035000310b07001181d42e008400c03200442c086481ea8035880c2c00b04682e090307480b02403615140c0040d8003585400141120f200d105540110070200c03801c901d00265000400442d1484040004014840040a00d00c148624003480300d01d1855642940e0b402c1404001407003080c022450307079002440303034901c1100c84010740d6 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 903244910 1250 903243660 903243689
    0xa0b180712211409010c0c030204050a14091902100e0933060d050403140c01090b010815061c151a0109080714041e0506012a020d020406 60
    0x14211101854101c0030442c8160a4015807589502035101500c0380216820504e113412038600044500814a01e011136400a41c60000700140e107882c03240910651040b140004d41908840180e9001640200b4120b001d0f448bc807150000c03c2040c08407080e1255055a961040541e1759900355546001c3c0306540d41c0200229041054501c082c0e010b05044031403229076005c50804461100d4807504090030b0a0ba04020104030101c04003100b90700042e072180c001c0c902000d0601031214011a0340c0d000703c1c10400d445c0e4441241078248400c412515004000b442c00a1048008484000d260301c00c0c010b0085204c2e103100f100f1801f03e40c03094522410b0290380212000c810400034400c040c010b1a40e6070100b2030380b40307803104100704a50103110168241c80c4c00c1c1c030003070482034074010081501c00f03902803925070041c0d01e60141d00a00c1c0306c4ca88c0d845041200400b07021070b1510340070000404030170003c140501c1c8240c951440d90b400007518000280d4440d01034814598070f0f4114000b180140800c0d038000750220034000c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 903246160 1250 903244910 903244913
    0x140f0c1302090904210c0209160306210c140904150f020703120b100503180c0a0801020a030c080105060a110111030f1b03010b121005041e0e0a0b180712 67
    0x80000700c102c074000c81c038180f17a4a4088004590308501e404000750881c1052010400052821081d145055054680411816280c040106c80c44401512041c01940704c03228803401c001881c3c0300c82019040ba62007544040d03110000185070101c003d800900a002d143c0101c1166240c10f400c0980d015454117415503844002d4034008004c005841980d007178240c5842c10762a00c0f442c0c80040e50512101607540c90342180c9628050008540e026014811a8410700032028003948450f0301e03080003131020301e0005071550320803003000e0141ca8551040c40b00b001049001840305965840039100706451515050844046810103d801024180b050800c00100401000500340440c190507124041101d00c03584010000c0d045010a404207003c0d5800e82a018807910800c00305080300c0c01d0b8012070001c400016156078101040442e024907400d00c0064807a030303c16a8422009004800f4502d206c00c0007409540303040e032681c03a40190040e0019403466049849002c80b01020047c0c0c40290030204040014080305 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 903247410 1250 903246160 903246173
    0xc0e031f050f150907030612120807020f120708091305060117090d2609030301060912080405102003070b0703090b07050913060b07140f0c1302090904 66
    0x100d440d0204280c1800000340034450100d055900405100f049a01c0400d040c00402a180c98020701070000c056981d600010301e0203200b416050040c2c001c56043c290504030003c000d05c0390000034001c406551010409254112000480320340d505a84e04440b0b85508107490201c6043c441d141d015640111010b1200d44282e000380d00c450701480090302ca011b0002076075440c0c0075114204071040c91098111110740c610a83c06070040000058499001103032184608250901c0d0b0002610242840d40c00170006201c8107402009142c06000c18900c100c0405500d83d0f00c00e059846039000c0d041c040e44205480081180c00349a03044820014419442540008145e40310350303a0304410400c0e1080c0d60381202107101030707020340f007401445600310f10800e110b0b036119070090361141e1244c43c000d9040664045d00c13540c0900c4a01c1440060b141c1c9101c1e450352080c0c0d90a100248500810314495150040d403402240d1000000300070038501c8060f508024008200003002c2c000f402195207081d045505c0b81e0401c000c03c5803 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 903248660 1250 903247410 903247453
    0x11060405030903010c020601180f02210a050c04030803190e191a0402031b010212041e0f06080f1b0304060915020301180b0616050304080607140d0c0e03 67
    0x2c0582c02009810803c800499072040c00384110120320302c8008850980c41003680100000c070711015005840c001740820610170540c50440144107029100088c4456020180611900000c0c40d4000394142400e540342e49009200c080c0c6000601400c407500c00c003000c000c17a044503c4c86486e00c8242c1d18030ba4418001b04400119401044440700c0603418120728680041e0511400303070380c0240c014103050040c5140b0300d4402d1a400e040034198401e6400042c3c0300c03070301c2d8801003001c0d01000000c80c1100c0c50780d991b135109140c42034125a50fa07440c00c100034003101d580725803030580c40001c60700d00c4540c903142c0495040d03803001e07035100c48207400c04c0020402080c454150848420107100344407400c0781000c03140d503e0b002c0340020700408000444e070140308115814035400481020400801061807d4101c1c440c594000c0c01e04d1a0031600c940000c20300b005210707024000c8691180b09401c0502c000c0d1848900c414091040910a42c2c0042c3d0321144208142d100380955010141d01908440000360305103c0d1414210 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 903249910 1250 903248660 903248677
    0x30717250f1701061715040e0d11010902010203070b1305060c09090603010c092c0f010510030e060f19331409040f1707020a050306091c1106040503 65
    0x3004801e641d9141d249103902d2604903103c5a9a0780700590303042e00131080c807410241081c0240005800c414080365102e2107611000404035000b400903120042d800f42400c0c904145440450349004000303000350340c001c011240d00750341c4001c2541d19540c071294408400109036102500c244512400c21200c02c0e00c20703000b010200d40454100c05c03140e44400800d4241d171a02001000042c6698100700320560120f800c2801c0090510090300642402480160102c03408032800c40c0c0044252004120500341059017a000d0000c0346801d0224100d03501100f43d4410000e010030a801c4401400291071100c4d8101880404101c00e10901081d0b084d2000c2498a81c001ca986060301c41082c1d034020345544c01c040381c40080b18030706c20f21b40020517281001c102e403183c030040c400d5079101c5e0b030108803c2c002a030a014188051ba5540700440d01e90b070b89401804007940d40c40d00514020350212003802807903c000a214401e0059a191490110314145030407129426860004203c0e489200144420840040041c16004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 903251160 1250 903249910 903249917
    0x7050303040309090e0f0d0f050424090e04260f030a060501020f030c0709020702040e0307030f140406020a15230108060a0209060a0c0206160602031506030717250f 72
    0x2c290746244e17165110031b0700f0207684d5031101c410142d059025400b401060115410068240380e03a60203203200f0300f01c000c10b041840440540101c904c15030441d14100161480c440f082c601407501b40d99049600c0030110042c3d80442c40002c2008421000000b1a0040800c02e04004e89078103000f5203c2c006840303580641400744c0078601e011910013000005031103002d14002d004204092a0200800003507108013801c2c0e0300152038903040000c04104100074602c0300d12950380e0f061084882c0c0d500500218155070301c0c146e0940200010030680c0d0340010b2298440750441d0a80600b03a01842c0c24000600304800310700d200d000001d076151609100080164120b982c6041903d595645d40004c0c4002ca100d51034006600950601000020a114450074447d082c800781c64140341030204000b20811144201081301c0542e000001c0103420000c0403103012411000780c1e400f42c00d42c02c0202d00540810455403203012002141c000084c1c4014043c22500000184510400b01000b564140104980c0c4a1401e40010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 903252410 1250 903251160 903251171
    0x9010f2a08060f0906060c031b010605060702010806010807090f06050c10051333051510091a0d06061815051204111509040c0201090f06020901050705030304030909 72
    0x1041d0151282510402008105a0004aa080c02c0006100c0050606508014144042d0a18020804c02040c0d4070f001103c4400401e01460140f03800d40c1e226400440c000c4106010190050740c011101d203800c0102424061a240c1d00d0342000c5401c0c07901a40010740955440070001070310354014000300203451000064039500c5640c1d09086c025264151480a0b00c51803043c0344201042a41c80320008950100012404490001e1800ca20490280080c801a81d0b642c03014442c266522104105540c0416165143c2c80c0c1041d11018210403014803a80b01d0703400212950340b864450304011101d9080b80d00d0070421035143c40d024010104140400024a078076030410000c40c0d1070811030741209024096981e02403500d140c5c142c0b4100d00d041d01a000f01e50017101d0003a04400c0769114000488115005880c17a9111b180c4902000190380f07031088003205691403c1104400310301c01da50301c0007410360404000f50b500c40c0e4600c0121014410301c1e401800314000802440101940405c01c8011600c002006110f07 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 903253660 1250 903252410 903252491
    0x41104060e09040809210a050c01122309030906030901060608010b040b1c090501180b0723070201140d020c07061403070c110a0b120702070b1209010f 66
    0x20000d400f92000390006405005841c0e03a40f9100c604014104d26001005d1100228501e01c1860020090812207580e001801c00c40b805580c81408440c2030740b55900107008101c2844030300301c811501c8118140007940503d00080300d8901c00c0040311503820004d0038140d901c0c60b2410a203070080100e0b011308030000711160b00004031804500f0545040c0c0b202c0c020301b1382c0b0700100ca01548203070200c42e2400230300380c0d41c071084110003045003880b4510b031000d892201e240252180345170204407a64020088400d1010282d2580c4410740c40303180c5200b01a00304210b841d5101c0e81800141c440300e040c499000c05482d00041d80c0c0380602ca40c1d8010300380001300340080703605458803103c042e2400b248a801d404850081400080d00d001d1180548821950081240741c0100700c6e0040458404030301504603611503e80080c140134102c1d0015281a800b40003880545080c9042c800900b40b81d100e0342c0e00f01383d134070180c2c1c0c00850b009910070b40c04102c401101c0ca504000840e07060302e400b25413400380000da0f0405035500d100542c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 903254910 1250 903253660 903253669
    0x40b030102090928050a09050f0609250819151107020613181505030a1109071206030f200906060c010906020a08012907030815041104060e 61
    0x41c10710800820520560783c07414040c0410401c00801d16814020701c1c030340b130f10b100010340c4140790048a00c844042400411b82c10300b54a80b50780072450500e5a884001042200d00001c541c0300d1041204044042c68102c815103031202c02001504008054000c1e12900e80c85030070f0714000c00c5141449440001210f0f039103440150201d5030034030200300c88050104492001450303d0710040c14102c07014044c0c800c0880d01c035109035000540c03080c41101111382c2c80c180c001c0c3c05402201e00000401d002c80c000d0480800ca035841c0a407011145070720b180942412400f2a0f95140568082e03030008401c03600411100380d032410b20124400885000b03403184c1c15803d8a008810901c1c0390100d000101c080c0030f43c00f003a2517100500890b5884179486480315540c035500c034000900c480c001030203000300e03d40d141c45143d41000030b0244000b400700460015802c07682400610000008151006550503040101007a80c41e682c00f902501c3d0b1b441e44260b03000f0f2034400e0300d40310185000050420384820740d0b04d41595000400600 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 903256160 1250 903254910 903254917
    0x152d060c060a0e16080303010e180a03031e0203090703081606090803011503022b020705060c0301080c01020a0b0406050601091205060f0702031c0e071a04080c06091011120c0c040b030102 82
    0x5c501603001040180000c0348201c00766604151100211084040d10036003450900b000c3c52011800203071100d00094415507041811100d0385410705046246040940800341d4803482844001c11071100450402c0324001c441c40610046600b200b024803d00c901e601c1d1244d03603941309000d03903d45a0b06521814044500c00c0c801e42c0c0d1892030380580c010303143d942c0e480315040110321030030518401502084894000b9105103e0140190b118694542d1203506000d00e180c00c008040c0c10300780c1198400c01403c0701066001500e2171300145c200800148645030301c8012207054425801c118402c0c00b8521000d0200b200c009900c501c100315640d81c000140e10342c2c0004a03200e20810080c1c29101000c030b0120030000007564401008594844129030717440b503a50302d4580b00d11035400c12880c2940c50100c0c0030403448506010307601c1c01d900121481d504d03226071035000030002802d44482c0801c10084018011002c10200001e44100751f02074a00c0f0340360070312002265580c02300707100c801740500c1c00c11600c555641014004e8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 903257410 1250 903256160 903256169
    0x702070302152125020105040c0504020705030301120c210203010507020705030d03020c1507020a03030506060f040b0901032c0f0d050403080d0204150305152d060c060a0e16 76
    0x1403604601c0c002078254020300080e0103100c44454000800c0ca0130b415a4150400f14002c0383c0005c51185007508010042455036030009001b5801040031340c0c00203401004690545000d01900c0c0c48000042c2003c4e50090140e4210314142041e4024404104150000b031901300d902c00c8000f44072990310102c0898940d4410700c40c251f0036610100f5441d52803030003500603000303501c4842c04841907403000e030740b12f542918011b584040250300010300440c1803503454082e4170740c86802590200d00e0444031644d459054850b0784203041216801090360000c45c2c0c0b00c0d03044500c4480d001e0307850081e60081c103d840e456446200c081c4820a00c0340c0d01d004941d42c0030104d10494441d03520744806040514588a504007680301110403004d90b5070070040130034011981004007000c91500d580000c1c0f186840751141b4080c4680002035031251180d000204288048200600440d0f141d6400418100c071080c40031030024010703949110180c2c0149000c106400307107240d0149072400b45403400c4414444090403850240142c1e4043d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 903258660 1250 903257410 903257437
    0x40b1b0a03080a09060b04050c09090c1207050c010f09150e0c1026010e07030501080105040c05010509010513030b060109120305070b040c09020a030c03050c180f010512070207030215 80
    0xc1d004201076130051050034010100410b0103e5018001022130320100c5404900070000f04007107185040458446521001c3d42840d82d203048080c010803603200600070030410800c10300062591002c08207401030342c2000080c1c0028005860240b500e2011140514040c154081c0b4002d40108070000c0015681e03110203000d8500482068209404c0b20ba07541104155490740c0c1528413010868004000d201c0c3c02007851030200000742c20120b8009050704c0043e80720040580c180028407010441c1d80d44044c04985003403d040c0d48c1c2d02c0000c1c0069075070f8010a850701c0424880d0401c004280401c0c11354480c8140001d90300c4420954880500002c550403120307015001400a00c840740018a41c0021641c01c107010b0a4128141a45c0303075182c0c401d903400f05112200203a01c0303c05074105590180030301074005424208041c144510b5400e1040d0703c482c000080c42c8500305a51800d112a4080c40480d51034051110b410743d001d2418100182d9203c0701341c0710482c040c02c61500d8151038445d652003a101c2d143d10042 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 903259910 1250 903258660 903258677
    0x806090406140a0b012c090403020106170c030f030403080d020319021909050901080d0302160f0803010e0c090904030e2116050a030503190e0303040b1b0a03 69
    0x50000084000300100d800075641c0001601000c5018451403060101200100b0100400070004250040c0d510001c045440c4180c000005110300071401c1c0d0403848141d95011041c1c8d07540c00c0403405491076510202d4040c0c0c2c00f1024035185900813400c130300c80d0481a81200e12203070902c3c49196813440341d03200107000d0003000d01102c11507011030b400640d0040016020000c1d1000c50741c05403022644103407071b0555002c10610702c001402d41c00c051842c0003414100c03946500d540c90b10307010640394402603500f07404040d400614039081c0e00c04450304021164120490b0710229843d4a17108a0591081c06449000442c2030001161201d590003240c6441201030004c8106450f256001d89900c00c5001030b0662000b10745180300c0e1f486050000d48290081044020200d003002d02c00b085061842c43d0304520b008160720b0000b40085440001115a40402190014000c444080d0300301d40300f42d0300c0343e56607902d0302000400117031400c0c0301c0c0c02420000ca001d180e442c040034182500b42d5950f50312064000c001c101e840 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 903261160 1250 903259910 903259921
    0x13060e0709050103060b13050d03210209040b09071d150d06060207080a050703030e210304050f010804082b06030506070e01110a060c12020408060403020606011115250e040f0c08 78
    0x20350720b02d4009102c0c1c18040d0400c3c1c0151028050f10708519140bd0355103901141c4030041786006e01a03e60781e0301c41a10b2140c042d0425410050074010b151070341580030381d00009802e20a440d203001a40940c002e1411039a2503035001d41d9031102800321846545d00600c24210049050500400e94181c2c035039120008042240c61654151480808914115404507024074030008001a080031050000000005165614240810005042852403915040103044800c200c0080c0e400801c440c0c00501c03102030846000090000254281459000c0a84050920000204001d0000f80080c000d0040380c13180c000c03000800004560300c2c080c110144015520801c03012002c5030580d4000401c5040520b04884070040044041d026640f01d50711a4909611070b60811080c0f5506008041c5c20480900c0c0000c10540c00c1010b29a4807100d031019540ca0480100100b00f000c08030680001a41c0710368170303140c0c03061000080302821145a080101e4051400c2c1088901884000d02c01d0f44080140f603251741c402d0b42c441 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 903262410 1250 903261160 903261169
    0xf0703030f05091c050106060201450302030d051513050c0405041a032e050901090b0a0b0102100c0207090b030109080310090605030d0e13060e0709050103060b1305 72
    0x1202140c18080b007040200701e66101e0104d02d11960100404207080d00c115071400e5802c64556030b00500c21a450003034280001002c090ba040d090104080d000003c900031925503500e003070490401e036108441104d10100800d500400900100c2404840800465894042803151b85680040043d0f00c140780c1c9044204e90065a40150303040b0f15070004d900d0038035888801140c21941058484942140707080102002460100026441464407401c002c2c50140b5402c0124890040c125003600410b80b900f001416411003544461601a086072041c40c06041800307005d4010180506c0c40c9006000e48000003280b1855401040ca94004660080c402503283c1484000106103a062503645035480d0700350100403030340003c05035001c1d0f0f5250350040c0c80c0343d141003180c500301c0d0810707840240281c000b20708a1607000d0304440c4051403403000340c40381540707003100c0c00ca808000c00c4c0315088200700001007000c0c40207556106040000340d17002030302e00b00032a80d280d0b880e07002d0301d00802c8400004520110070501c8141030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 903263660 1250 903262410 903262427
    0x207030201110307020f07331b0b0106110606010206011e0b071202060a090507030b280f0b0a14010f02120406120605010c02010212031005060c100507020f070303 71
    0x40d00c0001129618a0003190099009071040001603100e00c0710a00480300621203540100445e1903010004410480304003041d0b010083c60420901c0c03222007540b5518000c07825592039418a90700c00c01d0304a010302c3e100050000a0203508005641900d500c0c2042100207074107402420141c00821507a0304e001c1d60a01704e4425950152055201248002903201100e00903001c4c562207038403502d4401020400007407030004024034861801e800d0403001000315070003040341010b81c1d401100d20845541c490146651404c0480c0f10003a800038001240c4a070342001d40e2002ca000e004225043c864020000100325800c2064010300d950441110710500c0c041d0b018102d100100d88460041e6000e00e000f1140d16035850b00554440b0002c502c0c003018500460b021807161801070a800d0800c500890102d1700003d40c3ca0704070380c07101c0c02c82906c0040451f0642003883d4100d00207141c01080280e84140411003192101c2e500448600760b58140008158150700120704a00c11012000c01044107515540301203607039a0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 903264910 1250 903263660 903263663
    0x80417041818030c261b060c0403120f140a030b0a05040b060913110409061a0a0815010504150323060105030a1a0d050d0207090b0102071e1511060a0c080a0207 70
    0x110700c030441d40102d807440000e40410140701b415011044812800582402402049203404000801c02440080c01c2c54460300200d9020346030118102c28600002e44218507002c1b00042c01c0600800c0b03850a85506422141e251803058440c0101c0d0f0f541c3d042400152440d14240c140c0c800030a0204881c80e04203a001441c0d202a000c00c041001310404602111036449504038060240d11140184250074201c0903401e610b60b8a1000646001d50400340284ad0600103400d1450f010081740900790203a11901c182d40140000d0101c241c540846040040c00078003036100110713150103280316603140c0d0740440b0007101d11822041e19180d203541c1d1149a10750041243da000903c44030b903c4041c86215032500105030300001c0c03051005140c9019000c030042e2400304294403181c609800e10200d481d50740d034041014002c0341c80c070841d0045004a03038400d40311001e02076040715036a00c1c2c00010308206690301003210089008410180c40c280c1d01c40c0011740e003e980400180002090707007400400c03003000c482c1e802002d846 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 903266160 1250 903264910 903264953
    0x2003090a0209090d0f020a020112090203071505040612020f042709060603030206180712050312070c0221120705030c07170f16030201080417041818030c 67
    0x21140c80e800116601c00554088410754080c003000140f9503040121202004141d00080a9041c0190300080045480301040f007400d035184e5580c081152000c100340c00241489e2214090401c1000d4001411600240b06500001d104100d03004032550503442100d20190307a135040185000d0504074245100c04a40d180f40cc426184d6240c80042f00d0071501c80c01080c1d6104184c0480c0440c95418000d29100d030180200b0010079402c054003401c03030000640300c02124090780d0355270503955580c14518114000d043d08100e0501c031300c40030481900e5100c0265107510b4404c0340e8840040855102d0070810a40600f80540aa44035480001f80c0394101800b0301021032040e4212440c0c203000c02c2c1c985081c001181c0c0500104c0a00a9002810305c009101c40e40000002200a0807081000900e014903d5958400a0f051004e01d9002c501403025210005081c9055031a210f550ba40c0c1d5500c40940101c4130074034101842e480c2c07207511600c5052803500207050941669486c28410300d02d4a90169940e040d8180c030829 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 903267410 1250 903266160 903266173
    0x303150a0b04030c1805090c01030b01110a0614130b070e0d02030f010c03050114091f080a1109010e0702100b040204120f0c060804050d030237090504200309 69
    0x3a4241c40d0001e2016501c96007074045400c1c0303030005641c00c0d00d221042c8016814180020810300c0c090011380322114001c2440c022881d4001000141ca04001c00d821144507070003092048400c3c01400c4d04030900c24003031003041e0b10b00380d0756400d000c440c0c0b401050b000500307a11507000801c103200e21400d030010881d0401080220100d016a00003403a00c09000d101340102d9466107001001c0c5d54141c4525801404082003501103078488000140e104440101000443c10000f0005449081e07000c4d00030004d48202e80884881021509041c000c032180c01c07260a114083c0c02c4008543d1411181045015004030b40080c50740c5003e04801401401c00103107075039005907007031000080780c2000c0c0405140090103400782c05030020850600303484084081d04042c080c80003060520001450005002c0c3d0800e10b140740050300c0748542c0710000d1700d03040304220495801d441c1c00c4501a004500350199415201151592850311741c0e11000d00040e5035035407000300070400e043c061041184028800a580c49400681650300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 903268660 1250 903267410 903267419
    0x303140d020a0e0901050f03121e03010e0103050606010f08180f0316140610030b09010e1b03010f06080319090e090304062a06090812240604080303150a 67
    0x40b07800541c05500024028102440300c2d040c031490503409010f041c0c0d030000101d1505000b0a90314880212038000140001441080d45205402e0000502c0782a60016a0f01d582d200301c0034444840030f0000b5201806160003151482d0b0040070b0500d190502038580c1149603a80c001041700b440c04121802c1c2d09405038203440c42110600380000d100908a5071000001d28070f41c3d0910655800380105070b0052130b03002c00c0510030600c2101c0c0403241209d6000c4184a0166a0101340ea4090400074000b41d007148983c000c00da0319138130038940d2a6411002540200f000740d44540d021400c3d9041c038443e0b203800360402c0064401640315219480302e04a840d052080c03070f0300c1d501c035200101540221030101051b003011501380525503210b85001880b102200c01e0b1503201d4004030217400c07030f900741d03060007480c0680d95064282003002031010b4841c0302024200944440c5402081a49010605d884000c210000400200c1c11403602206840980c2c0c08a0011421f541d0b40321145a44043d550421560100102c41c0014 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 903269910 1250 903268660 903268687
    0x2101b050d0b1f0e03070803090409021c121403040c0311030114090d031b08162105010302030c040612020907170705343c0c06020a0804030314 63
    0x108a42d005030030702c054020f0f112002040740c4a03034286684aa00301d107804021855002041c0c0b004600d0440380010220900e200043c449075410750b20040e641004682c11083c040c3d804100800c00e00704d52600455041424030400031440101c80003049100c40c2d0345c041c0085415200c1c50f240a05000d000003036200010f1130300703184401c0101c400400c0ca078009d00d080c64240303a0602030001d2260307410601c1c055080842401600b800002810142e0300b0402c0300c145000035100e10740085184a01000500d010050001180060402404203900a01c51412601118141403003041c08030f1b08070b081c100340c1801d155802c1141d20a0b0140000042201107001c420180102c448114010485510354603900d444502c07144e0300810f50b034650102500092607503a10100342c10908468040d5200002d443d400040c2c44805480300b22001c4440e290709066415001c4006000d42503e200e10b010f1071011407107c0d5604c02c03c0343d80c2c1c070743c01100509141c4240000c000181c095440c0003103042c4013900742400e242c007880010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 903271160 1250 903269910 903269929
    0xe040308220b01050f01180b091f030203150a1a0c010e01060e09060f0606040302041d10020406080108010b0a050d0317130b0601020705010206010b25050d02101b050d0b 74
    0x1640d00300341e10700c01041949041441711910000c2804c0950700c0d040d40110030082c10409203c1c055000d500010001085e58407805420807806000440041d00454560020001e420031280b000961111412425052401800800485603241c84641d00c403c0c0d03111426202c4d4000716404142503494152401840c50b0a0044501402040000000d24908803074220315051014002a2441803550300b400916240d001c02c60b0700740ca406035400300e41854050f4128908400b6821719650900525845540310030300c54000380225000f9a031102e8440e62207840c07943c01c80e8030803c030715548039030004400c10a6051078085011600c2c060f081210304541c040a400c3c4061b5800c44681046540c600c00d15010824a0f40500da00560203100904541d030030030700042d58502060091074075194001c01d0b50315040c1c00c0d40301303003103000560200c1b02a5007403024545640d0f241c3c048402100540503011140e52106180e20480d4124590803c00f14444198141c05403036035070201c0d248268458442e170200c1c0843d10f501601 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 903272410 1250 903271160 903271163
    0x10603050f0a140703020f070c030b070207170c0103090c091503020a080303070f0e031e01090b220201050f04090e0606040507110307110f03070b0301050f01090e04030822 75
    0x424030703290045000c803914070000c091040c15480c101a401d000b011180c10254000d810b07040059035440e50713583d46a11406000e200a000750280000401000388c1d2110881c011450f680072141065166000b050341c4000e9000204040c1d48180308031516580b1035040300000b603006040342908103032240740312000d4a60803105c030074009280020410031410941c4413440108510b40166046080c4508020b1400000c03010300360410201200038400c50380d09220003121203031040c0c4200c0d07008200103600c81c040c00c02101c00352401d202500c00204560083d074081c0e0221100b044022032400d115a0054a440d000303850b11b808550410710010070585d0703545c07141800c0044d8040003041c003032520400300015218011718480820540006401c0b0788000041900c49055119400d9282425408041080302140b0305007035901d44103081c400582c101e01e2100542c16a00c0580d100340194132900015204150140f2982c12028400340014020911440340300c0d42003880c50703210002545108505043c2c0b468912030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 903273660 1250 903272410 903272417
    0x10207020f0a06051c0b0d0506160e06030f041e0515010918060b041b1707020d1715040e0f1006030c0e070513092310090e03040e0106 59
    0x28008103615185090301044901120b220030940d0800324010031034010003036040142c01e9403800107400b01d05250009010440c002d0880801c807405d500300680d41d1001900d181149456440b502c9903040e00c2941c0b15810103401400300351031900c40c0c04e50445c800741f00620907142414000d01300f018041842d0028a00f00b40100020208a600c074540d001c0700304810f070700004206142040341c01039000c4103401b120001e504920005201e0308524042806010104c004241d0b010000340c40126a68000c0410a481462031424420039564a04240d0b41c5c1d00300d606803000800c00e89401850031441c1001074550040308000404e500c0c0406201080030303503803071815050343c540001206000f07028041152815140181a06000c041d14688a0a070131080750300a4140c011400c600240680303010320201c5036055250345410304410b55a10000e4001d220064406100444800e00440c141440c16001030240100a040d00b49552400c14004020036024404004601051100040a03204000b205000304441d45 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 903274910 1250 903273660 903273667
    0x70b1f060e010815030c010c021306031b080a1a060d0b0a0501061704020609091003080d0b04111305040b21011d0304030f0b0703060506030901140a1a06030a09050d020102 75
    0x100241ca01d0000401341818502282c2c8000005e0b070780006c02401d008400c5c2042810300e00e0318004510711152509a40b0010360808800000704030f0154074800e4070080c108000511540c4400c00a5211041c3300320140000f800c0c2d82e600c0d43d404442c080800e0300810010800f241c100304558403c200030604032903070a81d83e566000104038007034000c44001b04000c040c0f10110366910b0185e00148071404ac203a90382d4003c114501c0060b4a89501c0140d40c1c020b590001d015036107400ad003c407241c000e0914800083d004900f01401141c01410b104151050900242a05a8894189030510000300010119158040c860500385211a0890101f4030440f410603000494031440c40e40b0450a52402002030044035032080200301f0109140d0032681a4003039200c40030030141c2c0c98064048014019942219510900010a20054203c1544064007040341403510707074082d94540c4406011902401001c0e40000082403040030503241c20300c010342e4040d13040c040020300c0d102c0300d8071440c0c5000e58131405000540e5000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 903276160 1250 903274910 903274937
    0xa050a03020601050a0f030b0c040806280c0512070207090c031a010c08120619060e01020105221502070807120206060a140405070309060c0c1511070b1f06 68
    0x18850280909400d555080e617280c0b13010740100b14070041d0310000e40751700000c04c0458800030700c180440b0010b10a20044550904198070f02d25941c0050096010401024548944c5c0340c40b05030107490901d058540b9058240112440c40c1c03061450300070241011402030721000301f02e6800f1886a203e10000307554001503080318a4000d100040f03135050301203050110280f40080042c2211003203078040042455240f6043d11024040340392144507150282109005c004045490f65102d000d0b0906075009a0090000752600744c2491209840340b4009045060311800780341c049074441c040c290200c030b850907005207030500035228819140c10400d001c075058628200140080c550400503e0f401c10310803501c26202034035200b00c41107985d07600402940a42e40790000070707c00a010754049012180c000606010000c2e04200007070034440842000c44203c940b16281c1e0815000c00e2050140d081c0c400540e607031400d501503c582e030b0308100040c601c540035180a440c1c4868001202c5101008000d251180c3c8103503445c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 903277410 1250 903276160 903276163
    0x39050c0604060e04151a160b0703020d1d030a030207050c061204051c020a060e0c040527011503020d020d14010f1103270a1b03140609100b060c0a050a0302 68
    0x2d90b10b0198005c0b000e6a00340011a441141c020001c400d40c0c080c0c5a07107000c480f505072082c21000401400d92040101080812030b0150010480c04c16060002c00c46004010024500b603203184003500c0c101d52003885030303660550081d4010146107010303800301e860084810002408a038804441010704002d10b5041c00100070040000d80c3d014504510f103080c2d288210f400003591042400e4000e0000c039202c000c13071182078a00f40300c21034401401410134081232410158000700241801e0034640c041002d0301d400906541c040c42440148002c042e6154165407641d0208488800c1c04401680e11020800701980006d0510001010340d45c0c4200020540004994003481102c04042401a5400b420001c0040742c00c403010b003004c6048802c00004540560540249281848281c00282a40d41c000304070200a4454203461003101d106195000d46403038a000c007503031280c0041d24a0a010307404031182000c5009030380c0102c600301502074851420070705902e01c5c4500d0700e0408407065a06412800b030000a142c0d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 903278660 1250 903277410 903277421
    0xe10090f1e1502030c0405300f1005091207060c03050a0b03031e0c010c180609210303020f120f100f09050402030705090403020d39050c0604060e04 65
    0x204600101000075075403940003401100700d0403444850390020000791a48000700c141c402800014107001066484081c8980b400e680444080e014084604214440844009170072510118020f02410302c0c0716420700e1000281a000d80304a101d030040f08086010209610080e00d44140140b5010030f03410b0750484041d0407100c02030550320350b8a00f4540e10000946000040740c801204041000360b10380c180600740091809a404841450b50921303203020509503010341e400100103d0040e00340c0c00382ea44c41000b580c8043d5a4070031600103040b501350001c3c44102d16591428400d019007805813501e8002d0561508560001107400c500a2072072060240c0e00e9402d1030395641c01504a200761401c5420220751001140303840c40781c0048103031100001801c64505100c2000241005021200182090300d0060b40f81d1034904003010020305242419902c0212844411201e0942c0051001c1c6031081e0600909044541e0340e81500c40d40700d80070f141c3e0308507226140100000c180c59500c00d120101c00d02d0070130060703c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 903279910 1250 903278660 903278693
    0x30c070f020307030b0c030709050a05060a0503091e010603060609050708070c0804031b06020f010b090a02070c030f0305030601021c0f20150709050f09070305040203160605070b06041503060e10090f 87
    0x20b000bd44144071a80740c45048030690581424426107907524000203a280240940490043c0c181d00010003034a140c054100c403003968030828090000d141c035043c213001107408c11651100010450008140c0960185500301782d298055070741c00d4078141c5c4075140c04000004254000c03100921418080000a5040c08201c0250840344003d11841d12000005585440068a040500c0341d00081c440100016410100000c5900080b460b041c000981000f50194204840c02d601500800403c180241c0040600405c4048940c50700e8448100020003101d41415403000c425070300742820725401c1c1724501041050440300c04c081d150300403071a2040c2c005000306180d41c4494000c0722841e00c445841d076105026140d00035013914000400f84c0d40d500010b4a4410392000c600c842c90843ca0300460001d03401002070102c02e0044000307400030b8840b5014002110f0034104003054202c0652402e100107102034009079400d05090080f81d6517048034031b80c0d00044951000c001c640740d2551285890402c5868040c40d075000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 903281160 1250 903279910 903279919
    0x4050a0b070503010906140a0e0601230d0b01141903090807060903180f05061e0a090f15021e0f2e05100603200f030f0c030c070f020307030b0c03070905 67
    0x8910b1a80401c0d80c44c0d146002740803400c40030340700041b1a40d1248885d8040c0c00302d480c081c02e522800d071042d01805540b0500145e0b8200d400e04440d002c242d40600405032a20b000c990a191401e01c44041e40e050a042142492082641316008280820000401b40005500407000021004424074024007103030032811441c194400348060800103081c00703103100c0e003c030307031040c0c64a542d02c82c110019200803410a6940407401c03d004544821001d074040406c0098802507030011a03826103c06655091900d8251940d005a01c1607584030304c6c03020f0f44680b4040b18600c03101203868007501c908400303091902200c50aa180c405912075a8030007600440c0a5000ea06c65000070000f9007044041c4408660150040c80207041e02d400e002044034441416030b2180082058040d0707150b962070030f6000c81c20342c4299034902c6030b10384500210300501d603243c040b640220040400203103000003a5441c03c0c130407046039400382c0c0d05004a00001012803918082148900c1c0701c101c8059481c0f5016101800444591b004240034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 903282410 1250 903281160 903281189
    0x18060301050a050c25141b1807031805011b03180201092121020f1506010e030102040b030a0e1504030c02131d0318012604050a0b070503010906 63
    0x10030194801c4036004074064045c5244034040309990074000003882d178010910700203000c1911141c2004102c3c030010001840e81084c01e406820108030a10a1650260611401034400720341103901a6001d2a400c000950140f80b08052070307200c081c21901ea82004441014800c040110010343c18425810107202c0c07045a0400340499030002030009666000c0c03804c4c62100c0006124000c6001240c40300455400441c95600003902108070100d03442340d10034a400341c8074070041c42005e0341000c165004001100115080c0da6500d1100441d0407880c0b02603242c0d0103560800010071324000349402584654100380780440c481ca54000928030b000448000f14103070404a8062200095000621140300741d01100c40506290107015000c0050490b05480c92051743c0d1140c19080702e030310101c0542540d10b001d10012210b0b030780f010015607401402e81100201d5048000500025250304055240c100d4002c104031400d84c0059a10035240c0c4070141c4040c8080344010004028041880c056030b8050440308282014 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 903283660 1250 903282410 903282421
    0xa020d1107060c02060c190218041104020a1202130e06060307020a110a0503061314010c05041502030415050903060a06030809010c0215130312020d12021818060301050a05 75
    0x88518441c040d02c030800c10b0010310b000565803a08207484220210406a0b824030074031154070a803410104108174015500911700110480c15142440d00c030b541c2080540400301160000c0000a600108511080c407000c40701c2c40108801f6072010704412074203540302c80072142c208841078140b00d00041c065440b400c020020840003580c04102c164400e40c1c0101111000303041760002910301c0e4016000141c05200365410420040300120306e615030307a8003c01c0e007520340c050b050780d80a090b04c00010840020590411007000a48855111030301e805803244185ca06040c0ca0b01533125260785c15400710000968003180101040c80c045c04a2a00001d00071000c1180914650301c5100c18000c12400c10b042c4a07046550344250b485000d28081e03c0341c0c170244115a54814590400e0425060b401300340c6d01d40c1d603850707a180748190000901c080000c006894001aa101c03034a40e240281d400070300901074032060300210294a03160111070344c200d0500f1700ca1410f40b03468100241821503d00514104245050409001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 903284910 1250 903283660 903283663
    0x7180b041e05060d0f0f0207030201140702070614090a080613060b010516112e0e03010c1e050d061d060a1a16050a0c1706071d0f040e030a020d11 64
    0x1e160070f1040e480031480c108885c215000500e00c030744001241c2c81c00001e51404055041d0b0052800d4894050100038a845d82034003280e603040b850003400003103205040090607158040020303012083c80140b82d000c08644074001241444415903443c4820030b100010b08082000314052265098028603201e82050200c0303900c0c10b508520a5030140a4000e188d00c15107580d25540200c050005103012150f00d01f00640700c40c00000000d00c40c000700012000c040c0b0b035100e494180101b020300105580c4002e010300b00368900e51500c2003824150424481c00b001011005841ea0250500500a040840b80c403400c41c83c1030200b07401c20007010a4410000c6e048144002550026440180b14081d40c00036201c08141c0b502c1c4d0788a00584c10040c2c414442c0c031115a08008103205c11205031030f1644510030741c0d0010b002004e9519902503c95802149141d00003c0d0b03403802000c5401d0020794028400d8158148240201b41154070401500303020380c10014008860310307010414a9109401d601d498035880b40a1142d26 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 903286160 1250 903284910 903284917
    0x90605011b050718140705030601031404020a0506030603071509060f03020a0f0e060903011d010c02032115090f0a06141f0302070b15030c010e0f0907180b041e0506 72
    0xb040c51505104804e220440b6600a010b60b0b105001c110700c00d8200444090500e400032030349180001d091110509407140c0011380070340610b0780a80070a880d85d08000402406420043c1a5a007601c01c1c1c80700001e000c1c0607524403680e42c01c07141e03c03400320142c1450401802c040f0700394680320070725004000b404800d03035100200f4400d184151501ca00961b2110300044c1c4a40b0070400311503410342c01d01c4400c1e81c407500013104036008440d00000800c150003241074103030f07228018420000103554184c03000c04a46203c030042e2590040c6442080842c114003640020b0655031300385da8135500b660f40c580c1002429503c038490140034140c001c0b03128410800382800103e400844211901e00703e0030303031f203001040140640c05661186500540410316403400010840042c60286580c40c482c0c40f50805094455020352100c9006410140801c00d490882e441400b0307448002601308030812801800c801c165507072075400321020323013241800c541d80c0d01d00d030120a00c2800d010103065079a2060b0610200866030ba00d9003107 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 903287410 1250 903286160 903286169
    0x141602010810030b06130e1509010606020106030209040611190503040303050601022107171c110406050f0a0905061b0609150115090f0905060910360204090605011b0507 74
    0x203d0b003641c0141d0440c407007d45004901d840d40c2d445082d500014640d40034aa8511820030300c4000c000555484030200c0c20b80705644006504403010a01203008252603410144600300c82071509440c1c03030783da140c100c41814020384a00000031008400c0c4000c06906019058002409100030001d0388158180d040701c4e829120501d0080303110000f501c1e0100250030b004015119944080349880d200342c2c0390307204800d54000c11100300d043d14080d5081c0c07104a02d4801d072010340b20181d440c1410030610784035007500750344001040d000740444044005866a5910300400d10143c043c036207400ea641c000c0c0011441c240c4003030254802504080b158600411128681034115003078860801c06602e0801019121002c0a8014080700040104080707020300052b0407150003444207440e250310a566401c02c140001145000716084003c8605d42012905644481000e048100120030351100c0d1594485c0c50481c0e000f84e01c10418251200000c10080d030700184109070f1100b200f1035100b00000c1540d0340c580c40d120707a4001c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 903288660 1250 903287410 903287419
    0x3091a0108030a0c11040507020304030510020a090b1803060a1d240709080607170f0405070e060103061d1008030a02070504330504050a0603030203070f0201141602010810030b06 78
    0x8084d0180003400c41140e2945001601c10000e50904a000a4496006001c280c509208040c0002007980241c400c803481c281090b92810101d80c100b14050800ea80700380300c021422603032049800e01d1550b080c41224000c02c0e00d044001764a441070304040c440780c50381c04100c1030f0941005000d4075114100c1c0441741c42048502c064105280d86858080d03034900b802d0303044078005102d910100840c480d04080c4041c803554001118003d00d60f6440314000700520300311402000c98004031001c0001c00340384000b16800600c1414040392181c2c8640070020003121986400341c44003050700501c10100603060718a000360041c50b015510706008840d0203551502c55100e228081c1d90f1700c40140c0004090200d0102c0c8250a52000244c98a8031840ea961180084c1c06454031030340c40c0c50082546280700d44030329002c40c6c0c0c0c540c02542c20120980c48040b140c511441c4281d06100c0650114074004441d1f1005142c0300d8440e06403041d21902130300006046901c002e00a21610040010500c00b140703840b01c0b0079501150445 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 903289910 1250 903288660 903288677
    0x14010c0215040e0406050708010e090c04200a020102130b0403080316020c10030213080d0207031b1508010e130b22020901091a150f0f120703091a0108030a 68
    0x1d582400342c0b01c1e41d4010350050420100f40410024140c11150041c091a42c0e406c0890341ca40ea14080258001e48814019611140400d5041d08058000c81e01031b12131404164524200c1481c20354840c0c1c0540b0081d00141d500141410300d1451503284103002e04140300e841420b1604664a001030b074400508892080406450801410340c4200041211040d001c0c0481c04544080300f07014003e90088141c0d0030300175000b401c0100780898001813449400446d503000340032691554980c8900408548003008ca181c00d40a808a94220214202001380ca040c0d81c2d81d10466140c040240b016040180000754800704021110340440c42c4c5009258020703040c402281500d60700080000c150f074200040094100c2d13418000040c068411368480c0c0c00e1a000e407100c054401c000302c420021100001e0031420058242400301840001c040c4002c3c000200d00f02c110b80d85095100c5140c4603110208580070000a9140c10b62201040010707064441d03079003c1c6020340b44c91941040002da482c0c0c003502c46c00004111111 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 903291160 1250 903289910 903289939
    0x20c04050c2d0c030f030109180b070e0a03050609030c070b0a05070201030b060d0f050105101106040609030c080304080a1409030d080c040f03060506090606130b07020402040801050a1514010c02 85
    0xa0080f2000c0c0c545800440350ba55503088042105500300341300e6080044d2810001542c07141003543d1002e0301c140c0c00600d446140e500e1f490180c03040803840541a81080980c6808000113004002060150f2a050004d40e201d905619406203410540c1c0c1284404003024041c1e1038505030084203131007402c0d0342401d000c42e0050008010440c94018241c00c0f502c550300700503001241d811703030341c0c803282c141c4400751402d1513602c0300300e60281c8070010050070b221300d181e001d100041c01140e80ca0b8014052548039180243c0c9410f1941c0721409540c00588003500c0709200010480038190304100c4100b400552041203d0030000306000003a02d54011034084002c1c4040318000030301c0a000102150b0161a0050f00451450b890781003c01c002c20089030b0b09070040c01d40002165180c94007106a80d480c000d1940c681584509008420000b504036510890300301d6028000811510428060140300322801100041c0c0300517051464045000713607500c00c0c944100c114821143d01e0343c1c0507031110201e940640c0d400001102c103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 903292410 1250 903291160 903291247
    0xc03070f0b1b06180606010c0809100507080a0201020309150402010f030c020c0d06020301090f0203130f02040f090f1208011d06130e06041401021312050703060c020c04050c 76
    0x40444142e24050401001100d4481e4030110104049036012a0a2651048015030300c00c004c512001e8649034003408264001e15118028a0601c10107281081c20007009980703240390f45d0071004a900c0540d4001c42002010780d8100b09080d51a2020340d44404030f4109600040e0415500140f040105611400d0910455000b04410081e02e040a000003881e4003207410554001e40081c0a2241d05900b410841d40d8010100d0098902039011154001b50807260b51b6a50285041400400c90700319448055a15843c5402d1090354503942c01088800c5592810345030000c040000300b0a81c03410301401c3d01c010300101c1c01c40440004249156600e250a0751503000009614000d010718151030203007410703404240e098000c12101d001e0ba1040e0b204a0310140c1107a03041c0d00303030700032041502d8249007580d42c2041681d00104040301c3c400d00800585041a0301c0b40c0b05c9500395003401c264000964401c03141e24000f800c091045561040000d50342500b041250910b12500d042001f040341056010b280b141d4034012078 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 903293660 1250 903292410 903292447
    0x8061c05072103080903090307060c110913060b192102060406020c01111203070e010c12020304150c2102104101031401110409020c0c03070f0b 63
    0x450314500c9621071442d01040d00c18503005000324001000380700410b032068030000544032001d10080c003603c0380380d00340007044403034242c0b890b019680c04420117a51030054440245140c001e545182011424040d54200070040c0d850f69071480d4003540034902843c3e201544140c082081d101c40c3c032200c003252072580703050b5036002000d004080d41c4100e001800060054002424140c21a42a21010490002550565242c682070321090802640c10400102010b1007041a111011014108035528100c5600c03000c00b480a2040b8070000360380001000d2107024070220b29180034120a01e0101b20512440e41e4039014120441043c00b940c0340280c007400c40443c000c0c00341c2c030368560061404000c4104851083d01c044c000c100c2c160742c3c0000104400c850b03443d00b00790741040904060710031000540d01e143c1d22019004048403c100c40341d50307200c640540c2804141c005000a00c400701c405600c41074204c4480d406c1c105840002442940600f000300066200c4450510031a01d5074003105444410341f50048000703a0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 903294910 1250 903293660 903293669
    0x3100f0b1e161407030309080708060c25060609060b1602130b06131a0703020312090c0d050106090e240406022505010e010507120f09020a030f1208061c0507 69
    0x400400d00f0303c0d0280040c00008903130182d81c50103a0705a440300c59036254100b03030255217000c1d0440c0c800102a080c48030b00511184100c0c4c05d0414464005004451410701007030030807140f142d03d895042244500d240540f40241c42040003803072822191028a0383d10741c2020100034042c03100050503108400d900d078409828074902910055481d04841d8808008070050700885d200d040b00385e01204584070310581601c068a906800441c5003d0b410b412a00b89410001d00b10070062140e040074684e1a250720040d14012345c840da00201d01541031501250580300207418111865004401124131104519030650345800300304d940001c2ca488038107041e4007a102c0c010701260350400c42020641c007030074030a000c002143e0140c4000c002c645012058103081c0d40c0d098811b01d0009014500c0004050099403184201c1091410006440825540405c0b20031203140d00c16518072202e0b11010060200c562202c0c4c160b11514600050f081c0740c04070000314194030f00058060b030103481d41000300800004001020140 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 903296160 1250 903294910 903294923
    0x4050d062301090501081209190b0c0309130e0d0c0c09150509060904030e060904150b1e070203030412050a05100b0f180105041e0203100f0b1e16 64
    0x100c4490291042240703003841070000d1507203407000004103804040b80300d45e0355880c501c0e403003031904114504001301c1580d007584502c2411400d11000034144220300c001c0c41c0c91022540a1502c902103c020400e00000e04c05c1c1c2045614203150320340e400c030032011541107260501800d0004013420f46c0d003400c000b2201c440d000b1707402c01480d000040d05481403504405046446c02c031100300340c1d50764681c184035100d80103560050110350030381040c07049480d02c10080d2543c924050400031b2400d11400d200d040800c0c40c3e41c0140143c4e0f800160002051904808204042030328203005480c2c01c00fa84e000c0707980da1045200d416200e80e1116602000c104050000c80c030300e180c02804541482800c26222401000c044800a1060b144a04501c01d10b092050051210002e4072144101d580e1130003041c80068510140490150040110804404101c61000d540100781c00310076402c0250400202030070690290708450011102404155902e0b03812041c50101c1544804c072441d1525080e09250716a03900c142c800903c203 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 903297410 1250 903296160 903296201
    0x360314190309150302340c030b09060708040816060e0d022d120f070b0c03060406300201020c04020409050906060406150e030a0b041a06040c0504050d06 67
    0x605038824003240c250303281034040383d034402c2e49000e05508034032440000803407000316000c81510210140c0d03450407500c41c03151300e8030205103140d40d01c000030a5816081124404030000a1055006c000c005c10790340102d203400c003000b5608058030340c000103014001c0c4000c803852448800d0420401960082c0180c440c1000840d200402000307030280d1503038112000040425100700c0301c1c042c007542040350300c62940420b0015115003d43c2ca03848013121f50000741e44c1d100005041003a180003c070300c80b030f1803441072042d152500d4807400c1590410042d68215070020340c8002e240d011a81200e00d80510240840d1603421a001030a4203501c010b0381007840d41d55001c2c0e8020700c08540058070102e00e4100c07500c43c81c00035040d110f0a80d1040d040004881180c040c03508854500116424a2405039110785c0010310020101d07400c8074041d03511044403150031a011684031718034002d1810242d421b45081500048111024003841c9090f4600511500407480380070f100303074070346010713a424802e0765400880c1c07408091061010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 903298660 1250 903297410 903297413
    0x10b0d061515030231060521090307060507020a1101080403030608011521080a05070c080706200615150904180209011a041202040209090736031419 65
    0x25006840d001e17994004121040c49049020380c4800401300020024025440c103019044420f038101c82e071003820000d00b10352072485441400c400030340300e0b5203040f000310340d10700103450a001075450141c5200c09551080008000184005188002000003860000d0741655607050407005004c45034000442540f816011503440f40c0d102001c03105540c06d540c800c901c919066040300c1191010828041d100c0c1905210218a440c032500091101030301848824000f6074a810019003000383d180d1040010910025640c040040c1c1e1800c2052034040e0784024148510b00141c03144024040b5521040c802c52041c000d003440d0408034419601da001001d401080301d10340c802c02041f0f100d01401401e070f1040c032000d000010030082d440d03070421101d00d94844160900740341c0250000b00984121003281d01503001c2c00012070907100c2d820b07070030b209900b16035078024000071040702409411111500d0381c041d0007981d110341030590845401c04044a61007000034441c0c810b071818240c10b00803124126018002c40c1500c0f0030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 903299910 1250 903298660 903298667
    0x60f090a0305060601170f06010503250905011d0a150210110a081f030f0305090d111507050c0906040605060d05010f150219030216031b08010b0d061515 67
    0x900c9144c080c0c85074032840e40d048a0741e6441035001c5421403e8a413411001030f81075407098000d0360300001d414000380503042c00d041080b181707507480c40d0102000621010703040013a5130380071400c5a000c103e07964244960144075004100c040489010301b0038610010b082d0110b142e8400c20410031001c10441d030400007207826094401469000c502e280b400100352078049a1a0180321a582002d038078411008050381e8595515040040b01010065050150511a01c849070b00d940d103c9000c628800e94006014450034401c116101c0f0103048041d59942c03007070003800d0000b40000351115416074103c0d10b01c003160b56140c0001d005801c854228540100002c1000c48180201e50000c43c181da126520702128585c42d18030510082c0c01e001c8500006030320031400d1501d00308562008406060280c410b6940c05030240540b60700e81069a0300031504681c1c2d0618212140c42d44d0043c541c00781c50110020b22207000484001900404915005050250343d11113400400b50304048440003805540c0d60090340004603000039 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 903301160 1250 903299910 903299923
    0x18020d230f0609030c0706230307020c0109090e03070215070204060b0703020705011b02060703030e0313030b0108031315210b0108130803010902090d020607211706060f090a0305 78
    0x208201d2242d4000301c0c1402e40c010058401003004030006004603413600e58200c800c0000000000e065281e15095031187c01901c4e00150304c580751a07002048012840390004103485d40d02e9100016851410030302400c0d464011044451040d0110f8800305400500c291500080c403660800a500914020300040d2090001014001545c069001d841041e81d84200547d080d01c2c41d6103a4031001e100c07540ca8031006150402c0903225880c00b0380780c00124514035600706407642d4000c80480c402221204d40400c03c21441c083d4003400f410142c000b6608080e10344035540c00b102001d019108142182080300400e00e07104034071345152112200040012010318003844d04c0102140600c13640040c09510005160b00000081407901503405a1410f2950303191010f200e00a410500c0300942c085200c000041c09a6220701c007030a4240e001c0e030407800101440c03a900c1e42d00c070764882d09440140030712461030a04002a6112040d4030000a4400b15558031071460010018800c1700d1000b988011101408001d104001440 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 903302410 1250 903301160 903301183
    0xc05010f031119110102040b030606030403180308090a09110301060c080d140a0c0c120813020604080d08090706050a12060e1303110c030a11030a02030f100501060318020d23 76
    0x44c0c3d0f03504a540d0903d94240e11460040d00441002000420610b040440c01958420300a240c0800c6654151100354004091030344152110280824000ca03589050030010300189007c06040100d03102c4910440c049000501c5100140008250f01b107007400100c5d01141c107130010500040114980081d038140c1401000c1d41d5100010340b400040d411700901510382c0b51403080d0400744104102052030300469502c0300041c01c1d01d5030002e01550034001601c807000508086c200307000180203c2c85505100030705001d401066800903600c014070411030585c1040840304182400c0c500400c44541c0d4040c15000741c8110f40c4401000200001040b041380ca81b0034080322640d1080c1d55801c04504883d0200e550340c9500070003154103400000e1050000b03043d61482901c108000f8064603200003c940009042101949100c0c41503040010007651494103845000d0140203a0300b802c00007600e0440001d81d01c0e8416907402030041ca81310708079000303001d0382800e813503105402600c1c4000c86c03500b050659903c9090842d031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 903303660 1250 903302410 903302417
    0x60e0f0402150c0703150e0c0f1c050a051501050108130804050a080c03070b04261009030906020c030706050a0e030c1c11090402060304030f0324080d020a0c05010f031119 75
    0x1000000e2150714062447c158180c0c2d030003094540001820403256003503100e80c0c10380c400129214079034a40d0340f6141c100c0d9024024400b030b01400000b402d089003441200814a00c040b0218001481107a03001105150840e000300c0c10720708004581c4c9441c0b8100c2c0b184d42c0003198443d000d03d00024030407200091160013020140c1c1a03400c032581c1c0b040e01e000b55020318042c1c07100c2c8520307100281c4002c80c181c10b1120303062500c0310116509040303074800e5041212010b107019800510201c1040c085d40f5010010060300c40000d07002000d405251000060071170192200305402c00142e1450b010043d50100280300c05044020600702482140c60740300c0c4d08801d07071294111b9241d5104603901d00b10b80740890050340b00315000307801c0c2480e5503200c0d0340880d10681001c007503501307040e0340301c1d81301c406158081180001c2c01d11000101404c142000361091500c03040c1e062000031980003010b51b00000d400384902d0401c684083c00c00100301c40201e5020fa0243c00380d00300c20510040d010440f01c01540101a08070b503014110748 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 903304910 1250 903303660 903303683
    0x305030a0f230301080f070e0a0c0909090606030c060906020607080703090b01181103100308031b04090b040b09040302150c0903030c010c090602191112010c080402011101060e0f0402150c0703 84
    0x80c0c401d0340302c440303901c44c0e50180c2245230300003880d9880580007244200b506140c580c0110341c8070400c02d4121071000340190b80066031105d0a00c2000280c1a1311030180545080c0899402e00c0e2031f01c001e66400c0c00915050400035404081001c0b18043c2d041410141d0740318450b9800c560f12100040640308854042651907030911f4a8060750081d40403c41340112a0440268a03c0b811034980c0c4004d0762002d800c040c242d0759082210b010301d0381d14402401c0980844e01c07001c21b0b4003104030b04100076a0114000c84d4445c14000303041c000003d4000400f89000801d002945d1000d0352600002e50160041c40c40407a0107000010703114916000660014980e106240c90340440507407100c0007203949601c501e03540505001244c08580104000f081c811a51000c01480822606000750302603007541e10440254000c203840e58103020440d030b0081c18400b20540940000c00c41e4510300a4500240c50018152200380c58001d0003207820364403030140021a40802e120929030380e4029606c01c41c1e0b141c3c600c0c4000c4d030f0401e0052 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 903306160 1250 903304910 903304933
    0xc0609010c0914060c070f23090708061302251b08060c0d021306020a0b150d030309050a0b040b0411151c06320303040305030a0f23030108 61
    0x208103000036030700c00880c4140040f14000030703c111503206000d050f501d07205141002078a800c100e80c1920240901142569204603d078511032a004544400640b08108800400000d9a40b145156510017400c881106042e464014008000e100b15414100d0704405000200c48042030140f0042d4400d10401c001501c2c5a40c1408080d0030f407189000d40002034118a011038460346030340d07003d019542e00341035006181c108010300300c2c50742c540c899200c0c0000d43c000032a031500307020400124581c08240e80d00d9402d50f0308085000224000c400d0800181071555502c81b000074014100714401c8a50762050f1000002e0400703052169500d141101c0403541e4100c940000c82e0541484242c0305110150482d015090201440c1c40d405100b1000b42000b00e05651540b0004000c007803007409441c480c241c26030300c000200b51492a41101301c90342c0c8145011303600400c001c0002420000440e41d10302400e103090b05a050024030200d03100307841010340c0b11444500d00f00e914941d00005005604076034070fa500b1039030031030602c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 903307410 1250 903306160 903306167
    0x70e1206010b0c150c2703150f091c030e03090406090615030212180a0204060f0501020106090908031611030f0a0e0d020901030b0618012409030803012102060c0609010c 74
    0x1c88020f00d500704140040207418805030049501b600c02e12036400c0c07001030340c0d01c082490b000c150030403501c580e080e400c18000c940d016020703041e4010070072101410001209a0300049400d0010804008060347da1403201c99044080c0241e400c070110041c401d00c1055940c171806806443d4501600400590a050f040380c028020700c00c07901170020704401c00f40240d03100028440c0040154940c0d072014000e042d00c041c01682c4c1c40c032640b030150011490ba44170403030504000900319002c40c1c1200c15194508400f9201141880040c0c0f64001050950301140c100d0304c0000701c407421020114880349200121300140c5d414030381e4028049a00065603055a0701046004008411040510181d0000c40d80c1d03005001103070481041981c000307405020709a181c21820350342c0d0440780090740084c1c4020b203101c0030f006050184c0c031518840f51900c0e14104502d5070464032080b28512061142d280d0444040118240c60005084407114058004090700d80b00c02c69800070a032140c100711541c028651030700c003070324126601 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 903308660 1250 903307410 903307453
    0x9060e0703031b0807050604030201152c060301021b0a02090c0f070f08090319210f05030702100614040b0a0602030417070812040e070512070e1206010b0c 68
    0x4140d43e500c1c0004124458540121a980364103441383d500030003100700810303003c201307280c0100d101e6400003030001c2100c4100145070200303400c0844002c0a412001c035000440c005225880e040c00c00310b14440e0b80701c1600186c021300c5101c1c440c86d809042c4503c0315066140208403d41034500a840c007182603590b44a0500d8280f246004085809105101010200741d85206501c0610302c214542c2e890010141d00017850420310305000703035407d40100c0c0c2400c00c21484a9249000403400409444103080300b240140540482c901c1e10303400c0201c0070001410140c42044610380c4540c2c0b200081007155260300c00100380c002d8100042c4e0146040402d505164185a8003007004c4070f8403640914101400c056010000301130911034101d01f44180314001ca5031020900001d10890581c2c401181d4540c41c0c0000c001300c0f41c800511403010300c1400d10803880c400c0d00d10f0035901e81c442c9592030040c0070190950001805583e061411604c24410040049444030b4604000c104a01004003240c10034200d1400e81201c205 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 903309910 1250 903308660 903308663
    0x10b0a0503040302010618020a11030a0e0d0f0c06050c0f1b04110706021204031412060105030901090506190605030111071e05010f0f06060201050f1812040909060e0703 74
    0x140108090410144500099908540b082c0b0002c21010b0740e407000e01c4000b0700307141540070351b0960009184000c682c2007490022000303a08000346040c02c21302403024004004810000340100c25401d900408c108210102c10603045d0700c503001c04100750b201c503001000341c0c20400706600c262003210541246221f00090410b000c0840a610140c3d0340310b02d4040c400034059240307000500b1001031080c1c4000a1503400940125080c0c075400303a419207414200140304a11107001881c07030140030841c011001d21b0414050398440001e08203160780351900982c0da80184042140540b00380102810300c4040400380c00c8060324004018400c2c44001e0310750040508840140112400600d01000a000007980d01d048800900e4101031403030503518102c5c2c65150035a00c8801410100e641e49030039009400076135110b00c202426162000700300030f1410b903100500101018080c00d00000f041054400710080c00c10026100404400145480700e40d40c0c44d8460150020280c11a205411300d84034500003040004d40320f04a9 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 903311160 1250 903309910 903309929
    0x509031603030c0f050c0a080c0a0c0b0901080105090c1206060705010e0a110406230123070201140a050d0f0615120528421a09040e0703050d1107060801 67
    0x100117607035450074941d00030080707e1610300901168001264410bc600001031084102c0350b079407004420700041084d58140c2000f0700c101d682d0424403e1131310b410010358074460001078444982c1d07121000015030500a00d40010019070a0044031007407400085000030b94280300e030207030103040c54241040005840c1c90b80102c1520020041454103a81c2c40d03a1000921030368181020005501040061102181000300761601d01e000060640d00310750340207849100d04034182102500b0201810402001d034442e40f40d40b488003a4442c2c4d000c0c4810405980700c0e6004050f40b1802d455031014404010b440303400d818606108452600740010155903030020181c101840302c100d601c406242030801003005090303a031020450f08184203840103421103048103821a0440742c0010008001c20303440c990a500d007007600202c000b2860140741e25607050b031403015500c02c081c0c00c07500403400b0120001c801e80b4110307050f44007030310710320445542c0c44003c3e800039032101000c6c04141c141c885103501c07050141c0e18001e0a01c58101c2c00d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 903312410 1250 903311160 903311173
    0x304080d020c032a0c1504260d02030a0e0904030e060a030c0215090a08070c09110d0b0117180109021f091505090402030703020d091407090603150509031603030c0f050c 74
    0x140c64000080104103d86c01100c500f400d440d980903071514404202401d0f00c4e8040c20f40c81e00c24031242004031211241c0d40d8802540341c000d4005000b00041d60200d8980e00540224004c03400f0140078540006548034007410894940c1c580804c014040c103a28940f00c000741c0188085084100e85109203180b16007001c5c0018038042c102c66136040b07081d900c9504141c0c0c5442c010100868100300a0255010503400140c255440b206441084406ca5600001590602400d04800031030b903005406038550048084125020100061012031b01501074484001d6100740700703040490b20544890400642c4041c10703030303c04900355255050f10b5a07081e54514103201090041c042000245007540066034441014076002d400c1c04403c201c2d00041c7c41101c00b007140d80c6103900000400d40171b402c1081e40c005281800c1c040c00b049103191900041180b940c088400041c1d11040060750884c01002105d8881094240501450f10a8240140104a004041e80000300c240d074040f1000e074840c4c030a131a407505185029084 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 903313660 1250 903312410 903312433
    0x10c2003040605090d050a1b05040c02060106080c07060501180e0d050405211906051b0d0b010309020a09060302180f0f071b031106090102040b0a050304080d020c032a 73
    0x415404c10304030302d42e1162414a1900c0026010b0044481c110712825045914240a454281001100340c02c041d006520300b1010056a40e0f000401c1411202c881c00d003141d035500c401d4900080381c801c0700005000e02d400c01000090111441c00048032000241d00c04110b0002d42302d10369610781e082040f040e400a00203000902c828038000c03040c0036020190501d00c001c400201c0c3c40702c50070400c3c1c00d00c0400504100003a41030034841c05000359944440030320040e501c854500b0f41c0b40d900324000c1620540c4450b584100f9446264001d602c1100280e800034010703070400780d0f03d200c014084d00d03560100300e0050400d00f00d0700c0d41c55100010b149014111102c2c01d10000d03900c0a4540c201e02d08000c09030810440450380708a500300104ea03041d080540265034112003440030100592501c10094200b0201c0d0784100130400425140c0420f9415400c0c80e4030b012962074681d030910040706c1c010704415006551000130b0501e40e9800010043c842c2c000f804880d44010030007106490300e800c00000b1104250780104c50030b01c6 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 903314910 1250 903313660 903313667
    0xa030509010e1f030e2802120f0f19080306090a0902041d010e0604050a1211190605091605062802060f252a05010c20030406 55
    0x1000351418074091480302e20780070008000e88610540c0001e000000840382a505038113006001e0f0224010000b090781401340c030b18218200d1039802c0003903c0050910101011582c48894503c01910010100c40c0f49000d080300302a01e032000c2500034440c0748038847c0511052140321050071010b40c0c1145415003541d96050a02000384401095404020b45d00e44018ac016900e504c200c0a4412049410210344088076002c0d138216485188844042e078400010000002d0700041c0480c1e80c00c2d817103d480080040140b009444a042d1030013a0070301801060340c84641100d0000b08441c1c0c940c001c600601141d2a00b0600e070380c94044001d58401c1c0520080c902f80b0141c10b010300140440480840300d020101d150f050280090300c1403001100050300540c05128001c9201001c01d60454070300c04060008011580c001400320050060340c40034040c09034000301081c03034880700312011860f0426800f0035908403031405034001c0c0540d80740600840d03080c0c01e142c01d110603000246608124030784021840c050030400240e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 903316160 1250 903314910 903314917
    0x3052b080a09060b090c0307030e060606040b0702012016060e030601050f0d1a011d09060406090201090e100303030507140708071106071505070507030e040b0a120b010504050105040605030a0305 85
    0x1030300d42c3c6485060328281922103d41c02441802070300300d5280c9904050f41c008095400108448545920460601450383d44076011503007207951081860b6603a40c040d200513180f21820920340c40585074112854419803201040b42c0e0b0a15008508082d811512004142e031264841b924080d019071000005100c4c0381081a400c2846020040c00c422120200e030313403100c0b4140c40314000d5a40003181c480040146008050500350761104c0291038920364a06002459550200100040c00c01c1c1e44034a000c1d019a4007410500c0094818140d00c1099450035541d2503160079114442180021b01d000c001507821842092001408182c4800ca00d00c4c10581d502c6a00d81900602c0c419558440b058610070f19658500d00245040d40c807840e2984600c00382d03500c03003104a6000800f805c092000811a0310700095120800202004003201c0000307520812001084903207200e0f4000c00304410550040c8814041c1542ea298100c1d079046806000f260b89131070600c03042c0c1d0704a206064042d03120190300c0c0d000074003d1019 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 903317410 1250 903316160 903316163
    0x71a06040f020a051c06030201020d0315050907080f060126040c0e16080901061d0709090e0109050f07030305040e0a020d0c050301140406080c01031107080403052b080a09 75
    0x8140124641c0c008822a40203510741c1002c0350b03001521707429200c6460b140e500c041649040c1005058070315000070b5242c07426403100000301941d4880b15207204c250720341048080c0070042c02c40c06441c03802e94000361090009a5400c42c901c94241c2c0041c3c01507200b06895150000682540c1d65a00008000e034860040060001c0340d46503000c0002044010b103400c0007511070408045980d4050403005030140030140c024144c0c60060f414010b0502108104a19030840c01780b109803000a01e0f5a04441151410090742005041b54101306a082c403400c015000b040c01c40c1c0c00750003505c2203800c480c4240c0c3c0d59402da502c130082c0452001d002c100022030b0050b42e8550b014400e041c0162802d0105c07440c41c1c0c2100d2190300450013040020005001c080200d00c40f0150001c03040c0c5041000500f01410720396640038041c40f42d0f04040e20358050230b13503103507030b61041d42e2000d5409203819803102e45038541640c5841610b01d0740d014a00081189228511711b25501080c0c2c4a12500c51102369100c8039050b0002d030190100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 903318660 1250 903317410 903317419
    0x5060d150f061208130602030c070521010f060f1d040305070302191a24100c060e060f0702190f08120403081618050f0406030c080109050c06071a06 65
    0x8005254400035210f0f01d003c1e4030070000c466907860301c0340c0108000c9500b50000b4045500074881c02c070310a100011490181d0b14116980100c0c010b040000d4110000030442d102225400c1401201418105e500054161900c1800c80c59915480c0d02880040c00c01d00c0b1540400d103035101d0007050100b80074000a000c004d00a1042c0ea940c140c0c041e400308000c0c0c0b400304040300d004118204000b081502c4140d0766410540803050710121004c000c003245c1c0030800341c01c01c0b1445454100111074802e400389100b8085d180c0e1101041c8181d110708044030342c0b102421940740b810000d110740015100c030310100d00c080f00341c0c100000c4a07142003111b0319003280740400f100b0110340d4100c00b080340c0c502d0000d100074542e210307070700c259581c0d007442c0342c0b000780300010044200c2c41c030f001c0c4a02d182c02c00790740ca00d40c14501402d5030030613981400c03150710100003d070140003a944081d001e00d00010010038640d5041d0440103210340510220b81c8010760f02800d000552198103006049030254200580318901503402954010301c0040 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 903319910 1250 903318660 903318671
    0xd0f2a0c0c0b130f14190503060a0c12111903060605032206022205011103040e060f1203040801150302100e011e0f0905030724170a060905060d150f 65
    0xc0d075001921000d034003d10030800e217180e03078407010303281ca030103ca65400400c40c80500620310b04400b084e43c403c0c000d0002c19406807140788074042644910b0884141c1e4201410a102540913181d01d2081036011807000807814042440ea0200680640200b10031218280d13201c62866440000c03c0040e02d1903071070440c890349241c085c2480401c4543c0050482c401e40d0100e0031811820000600720380303611644c0143e041c41444251268030b808003205890459102c1004403000365144000a00e03032000304540d096114441044404074540c00001900c1600c01d4030000b0044202e9044170400050b03081d03c40203601500509200d07103401c1c4105111030380114103060810b07160512000c48406c0c15401d44203032001031044144030070000d61061040e8020071058024007409410501c501003208061080754a00a00d480c2800303000a1182c548c0b520154980035041d0610300303100c0b00d150081c0c0540e128400484d07050002041c0035240c41449031084983c40500134800c02061f1040c94080c1c0070640e00038001d40e9480 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 903321160 1250 903319910 903319919
    0xd02040e0106030204140f09150d05030a0c0b0f090309041107171917040b0709030506010b0324010207050906040f02031e0c040f05060d0f2a0c0c0b13 66
    0x4140207010704015100941c0b40c07400d106107180341030041503440d84520080404501c2540381c8808141d00401c910f00607035491050a000308642d10001c2d20001e00510000030300340c1e0b1081d840030001503032070b10036004296980c441411004c070f00d00c001d44141030b40d900104001c203460b1500b0361100240c211148105c5040c540b01c3d4440d035580303600c5900081c16a642c005562940100340c1403003500950386600303050400c0d8040d804a0740c4d003858001d000030403110807030300032510b090b0081c0c80c03150040d0b078040119030140d07845042815164105540c3c20920844030812800442c1980d95038030000a0b0690048c949a07182404000348100007912082e04180d56100f821034a441c540009c4d80b142c510945031130003811150410081a8000070701c0c070a030000040c4010301c9690307207890300e46045400803511142c6400034417240c40028808030440061940c50501d44000d011540112200100740212034205081d26045065401c0c1460b03540080c440350302c01c507003804240602d0313000c0c2c80d500380d64104200c03c85489c0c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 903322410 1250 903321160 903321179
    0x12060905150c1c0b060a02150903250c0e1006020705221d1905060c070c12020414010801050f01090516110703080703090f120b010509040f0204050c0a032702060d0204 73
    0x24003032086c0107811014800b4442e541c4600005e03046402c0380001d515008007440900000880c8582c00410724007210201c1c0c0c1440f8442140c0b41c064464086040c1c528140400c070101c0e07001c01d5128820150090500008040c60300c3c60600c0c580e40203002c0582c0c044560102c8040c010603030340300c101101c1c55001072030582d01041009252001c1c8030030791000000c440c4906203035103402c02c010200803100900b0000e907000200e0624215084600030700548002c8143c1348005005002803011500074113654200000f880081500900d0151040509000141e600c810410090300e01c211036100459004444220034148564008048d511350441610f180700c5c1c0360ba0b140501c1d980078400603000192004002d00030840d152101c070009203025410025203d80660391201981030510485104401c080300060a2141c10348054416a0340104100700510740000b007404903420144007800001d150801c0360140c008001c8040c40401140280031a641e10a41d003040103980c030a40c000d4041075002e10000a03071041d07 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 903323660 1250 903322410 903322417
    0xd020d0204091401020a02010b0a0f0b1c1406010305070c0b060d0201020f070f0e130c2c01090608010c050412170408010e01060311030303060d03120612060905150c1c0b06 75
    0xd80e50000d0382c2c0398910306c0002d0a6803007058450b4414840d91a0802650014214400884543c005880c0d201c001801400c0610f120140e00320200d20300302116405c0c01c92201d16224442c0d002600c0400c0203480c1c401f000c5645080c0709e04000c001e28002000314505150160030040740910502c1103d4000300080c0321541013812a601221a082422405001c1e100c0f44100301540180346520009402610780c6480d610300c0c850388940e807483c1007540100c440c0d80e550485a0300c00468107240214041d6544d030130000043c4624031901105500c0c00140380f02c0c0d00c0c4104200c80484480902289202031952070768940f50101c2c0142d40081c800c10400092000400e01501082d01d041c080009031040c61402c09040017004401040e01c641c104004101e25943c170b101083d04959010b142a0000010000e20310005000940001c201e2203c0b00d03031300c001048450b811001d1028810300075121004100b0300c40701ca48002c2a908a48260340602080448040350300d400c0402c1800e50001150719419003000c20420360 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 903324910 1250 903323660 903323693
    0x4110403021e040e0d080a0203100320030c0402041a160b09160501260709120c090b09060319030c0c08101103060a0302190503060c03040c140d020d020409 68
    0x601100350b00c051406204880445410701c0c00b030300421303850a0005044060003071560110030743c00300104280000201110f009160711004081503900c0788040c40c00e012071b00c0c660030780c0f092288110325281c0d41050300035034080742c5600e600804401003007010110346800c50340840340c0314002036000b0008035040d05040e6003e509410003901074000c1604194000070700c1078000d00c2c10320102ca12114900034a16104c800c00c09010030b000350060700c0d5030004480c2c0000c2580100300d100452075080042c0040907040400301c0f030a500082104100e40b030140550503000700c40c003076816004031050034048e841100b00143c200388246021020740c2e519640f851700c9080150001d002503405469140000c0071107116113032100c0030013500642507142103c00154a19414000240103040055101141d40020008980a4200142501c0e440d14140503000c00c103170000c40c1d050b140e84071000340000301649500400c09000c50081e141d4030101840ea002c1c0040014110070890b0065550340e1120046180c2d800501c3c440c6 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 903326160 1250 903324910 903324949
    0xb03010b0406120c05060a080a0e16080d020c180106200109030314060a030c0b0904140106030b031c02060105090c090d060b0f031c0c0318030c03151a0411040302 71
    0x466a13040488007081d03503401c458011038081111000e40368003d0780c616484400c102c0c01156030f48601c0016810040003084004201140d0344000c204090042140900c00c4510340c02c0310f540d82694000c001044140b180d00c20f00c01128800188059842150903081548411f00c0380016084014101421a105001e00f0340000c0d54586211000c07144602d00d00381c118104441d0f9055003820b5845428030059980325088000307900107100380c06078803240c101d11f4180d400071149000c0d03903940f90009009040c0d4041c100d4400c2c051240d41c070309280383c0c288a06c12511040c1e801030000340e003800c0902c802c419019217070030309008d42841740079595981d85280c800344038800e240204005c001c000910000140b0244c880e0700c6a0071258045d030803040d4004001c445040c241c07508020002c0541025161941c440e01c0c44007040810071008811f221004400301c0c00c50b4819084c3c802010980303070b00c410132998220144405514110750710411468660814854810031a4481d45095901e90000f80310381150111140c00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 903327410 1250 903326160 903326189
    0x1b0a03080a0c05090a05091f0f1d0f0609040807020402070c0e0a02070f0609140a08070213020f1c0e03040e040606080a020105220e070315140a05040b03010b0406 71
    0xd0039407a0040001d544501e0520038108020200040c00008044c068a07001d04600b4001680110700d0b5203201c1d4807882c109040c40203482d2a482034210441c0c0d0381c0218001120baa4013030a041034603a08945219800c82c0c481050a603d8010801505030070140c01903410341d40500401025946a200070f1805e188075001c04034645141c01000c0d28450300061030614650300c140f02b500c000c01d06000218039551f40c80362001455203900c4c42d090014074850988120140b144a0f90041000500301c01044683d0089514041013000351107000c09901c24084403000c40441800302421b1241d200600313070070740d410340301c0c0c08107048a00d41011403840e0019886040172519100c14001441440e1141c0c4c03000e040c094000d000d0300c26103600082d08501c01e200d441180c800d040d0105500c00c0200c502c1c80e9018000b0b01c1d04105c0d803401d1413000100a00029640c4a100300e4688000150380d041f5507210352001c03c400707095140520705e4602000010080754071075036050f548410a41c0640d50301d40c810b20001c0d001d042c01d480308 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 903328660 1250 903327410 903327421
    0x8370308091014090f0f030703140c06091f05060a0509060a1809061d0706050309120403030807020d080621010f32070c080913090804150e151b0a0308 66
    0x14000c5c1e40580902c19800c04040021145c20200403260f1403601828040707040c01b0701c1d1111700490303c14051a561680101401e01200f0203012a0a14020355424503400080d200c01e0f00c0507040790411360300e0359804100d44008001d06d0074071280c1c01c0e9100d04000d104500c8a9580c060f8407443d070810303090124100766580c80101c1044004c0c8103a0041c040691200c000c0b00140026040e0790f03607494050399052000103c002039041e20108107800200c00101b490380e440c2c55491030090022002990351101600403583d80130000c900c00c01416200b40b4005200c603c6d1551201c1b031410020052541c032481d60b5498001c12080e1756480c1c00b270403080168a001c059144c0128108080301d14070b0705031102281058107014132400d079521180c41294a600071080640d42c00c1080d00242c1080c03c0307003214100c1c0e81d007005c80d05402d0250b240702600031102896078000c4010400700301142d4032803d9558003540068080c1e91000941d654034090181d6807031152503244aa408001c1d00c07854100c8400d000ca00082d0f02604010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 903329910 1250 903328660 903328663
    0x90a050d080702190c05040506120d020a0209090d120513020307080f150c030a0b06270f1519090e0405010603061d0a030f050906040837030809101409 66
    0x440050310342e034030203113800500c0c0e469400c03122140c424240710715212800304006955804d4201240103001d021620101110380340a5250040c0e4101070780303c3c00391500050480710000c91114191f00c0141e54005140c498107003407130001c0c08040c11041403803515004441c01a01c04102a07405040c2034002007071107a08a010071440c0c070b2094400108244c0d00001880510500e440940390003240c0c0c0d41000c2100201c20000c50800d001d00d030070b440340c80303c152800d000d07041d441c120308071103080d03002c0e50080000304541d0b05000550710b0b21901d241c2c419204000300704075003c00702c40b0460504000d282000392665120401011620141c4d81560a0f0b55607140400401505214080032041050085141c040200000d00e03105d00104401505000391800300503840b51140089504164006001c0c50f00c0f40c0c1c9401e000c44e03940c1c1140ea11081e440300b0740114500080d0b0b00010321400110100062245171030607a41c115044800a8030540c000d129403403600740031110030700445a105031208614501450000640b6 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 903331160 1250 903329910 903329923
    0x120301090f06030b280c0302031b09060f1b01021b0f0601140607050c041107150b0d0f03030e061303032417031e0705060c0c030a08090a050d080702 65
    0x30584103182c4402000002c044105880c2d00813580c54a0700010660f204101350303445c04103100400c001c0d1600c96210040703a0103901441c01103204200041d458a40801d48495511a60420540c488414001c2516520544008140424411440700441a140746026081e0b82101c0804407000d0814404409d90980803c04992030303070910b200030b041b1945841c040030041103040c81001d002d81400a141c0c0c0910508210011b0088130143c41002429004008000d5580221004890804510401c5143c001e03050107941002c200003490180f21081540c0c404503d03e80c008012404c4c9034485c0b06150641d201807148501c00c601205000c94007120728600241107502614040209070300244130040c0710210408480242c610307022095020841c0c0503804c5145001351a11050260070810740e2510300c1100c24040d0820b944582d044a1203500c0c0c100d5040c14502452180503003035803003403040d800d1162065061a40080710070b8140c0340c9111140d01c2e510300f400d031040740340070200b014441031126056040155 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 903332410 1250 903331160 903331181
    0x30906190506010905010f021e060601120608060c0901090801060306020301090e03070f060e01060308130f060f050f090103110c06190b09010504051e010303090e10050303091003060812030109 84
    0x700018a400b01c0042c1c11030f6640d020741410441c00d1000500f210703008000344c0011181c0740d0521542507902c4601d2923038a0307400311403840c001401c4030100d06d400d081602500b420f582010000e0f08450b81c41154007a0190850841c41c1d0411103610713000140c0400078481d01024600406001d43e481d1b050105c0c0400782c640e0240c041c0f225a00402100d0b004c902c5000d01540680c0d070114001c41d0805094002d1400742c4501d1700007a0030488001114900e0b411080c000408a6100314941e0302c51690710070301624116940740c0b012020a50070031810080300d0044000708064001410b0003d145000c41e001b000711600034581d1141c1c140d201000307000c004074045040c05680d4882503001e0045030091404920403c60611600380136a07164408169000000700141e41c0c403c01f94110549030b50b941e42401444091075200301d100303030081d26001c02c0841c103000c0b41c02c900390741c00034005525141c2c01e1400e10000a840040d09402c1517034500000c940c1100c2030000c0581400e01004464403035041030300e400e04680381c0421 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 903333660 1250 903332410 903332461
    0x903141c0903111e210606090f1b0d290301050c070b0c091915020c1e03070305030a0c03080a06140904050309060d06031e0b061014030906 61
    0x1e04100046803a8990b1003820019642c00c01041081e011340ca82e54079aa442c0c465000b10300258092140b01c0350310303c04814040000480314540c441200340003030f60005545540c12104414005500032800840c411800307a0103c403d940780c410351700980300442e20000170060b020b408500160300d040400001e03408044030118000c106038208001c400149204020000b00762000520006200070300d1036007950184c0d24044d1803d6012800b0030b0b121940424103001d807140c45081000d4280d01d0a10019540d02c42d0080a0400b5464400131111600c1d03221038113180070785c0748c4584c800200c00110140054840c0151f181c950300ea03081441d01e001b4040c0d038002091280d8041c0f81c0b1070100300c1082c4000f140141100e094030031010a0700c6034201182148a901030841d017200d400580550544404d500950032a4002d2029000410300e081016640d0113139440085d008a503900082415843d0103194501420b0003420180d15020948984071407d400490300110290800380800c00709150ba45c0409044d00840f04 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 903334910 1250 903333660 903333677
    0xf1609050f1014030c06030103111201050f43032708091903120306060807020601051017040c050102120f0a0509060c010f05061302040609050d030903141c 68
    0xa110040d0340c5010700c103c4100119050180e0000c0e00c00b885400e0a82da40944041d0303480d1384a0510506103103000890b00d00400340c4504c0500301d0b850602c0f540c0d009001025030742c210340c0c0b20010641d580d04001c0d07001210040941e106003030f603801480d01802e82c560303e07098411246284841e0150407200c48810181016900c2c8890580c407074080c0180c2c080c0954001807940d140d120b41e0000c1041c4045580e01d030b000c01c048001010003406080303400c05049207030079030b41845850385500c401c44400e141902c034140540d00410050003d40360241c00d0100c03c011501d00011040b00d14003c2c0c0012000a4034140c419416211041c0001d507814400100d500306d01c900020710300950918031a402c0c0c820303c4141d03403c01601041440300e0742e90300b60888007800501d00003440034000108181d00100016603810344200741d1030035440d054400ca4000d4804076207150301c441140301c1c908000d0201d2214038500c22002c21504240210009404210003810403183c0c6008064181c550001365441c102c202c2d241106002000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 903336160 1250 903334910 903334921
    0x318053c0f06030901200c0c06040b07150e011e06050111030d02090d0614060102060604231b12010f09090c170106150e130e120c0f1609050f 62
    0x301c5940050072020359005989550311400b80d4010150302c01404900c0d40d05041c0310440040450281c50400b06074000d80e4510341404040021920461145c006038150130f000f0000400d11140c1c0503011048074450100d000710001400302d084070303180c000340444184000040e01c850701c41441003d02606080c00c1c0074040701d40e101a07040d900d0103400085039440d0b400090303800e00303601c6405d002e03104958401000c7c020f20955aa22050300501120030314010311800c000034905150a024030782d55051581c40301d4001c0400b41c11b01c0c000704403004102401141502540c15154400e000042110070400801c102d4594105455440c49018035804040700604000d03250010039034050703c105c204c6400b118080c5110146003002070240a095206055a0004080410790705030404404010314908840b2184883c2c103c201e500100e078140010741c01a139015401500c609280e14000f00740c2290690102e034844580c1d1900203103047c207600040e554a00c400743c0c5c1007044032030b07174050523410141d0b64000c400d440c80e00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 903337410 1250 903336160 903336169
    0x60609090c0b07050a0221101409120d0f02250203070e10170a020307090b03160e0703050c070b09071a1207050a0c05031201030c0e130318053c 63
    0x10454083e1140203840b003812a0000d84550488450142c1c0081e14023109102246070001d21542081c030550b0f68003c00022881140401e031303210703d01c8044d04103e041113000b883c0340004242e10b030510f80341203508116000c8105516001c80014285024062001c40060701c103050909626500c000e4028031304009211000800141c050107550104026a1401a206985a1030042d40c544040e4050069201c080f1b00101a6001407581440135800ca410b445480050110034061920840c221040d040c00480c40f00b520903040305170003a021030100383c24042140c9500700c0c981e00581d48128203074810581040761448030144600c107650b04503040d80c100900c450000040d484001c040c54100800000e0441c003450288501130703456a0032800b241e403100900810242c490400b03000588070303071502c0040001d4a2484d107a9191058500030300c21504101e440d9826510380310312042509030700e0401000070070261036210285a500c0b540c0943c100b001c800c05c407102020f0201c0354000c03003805031507241202450380703e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 903338660 1250 903337410 903337423
    0x6090201111506100e04020309010e061503151807140108071715460f1203030b040f0203061f09050d0c050a0803030103050d03020913020d09060609090c0b0705 70
    0x2098904c0c0880501c4902e044500040d0701480a80c80b910100c10b212440c14150310042460712060115141ea440f180032047c1c840c0555807040b030741035201c40d0408092410070354009420408001c02810502000384085003404001c0c0c0012542d0801650a21006d6a00410594014440e400e00d13041ca80c0031001c218039008002004a00c201104c000c0030161398540d98650a008031040b8104004180302d0080c81c1840d0688400d48412042c9600c81c0309140ba0300516600103c0d074115120500c5d01c1e02d0404414912005d914095060545d2510740d84801d41707440c01034425800f42c40c20700603624504182000004441500c80085a2100d1110002c0c8a60440b170f408081e0b820031520f07110304141902e009055081c02d6080550422200326002034421000006541607130b00c20306c20f80304101c01030703030b011402ca000382075500c2d40c84001034200b6401840541d00402c4010819000810f00ba03917280c460809640b00d43d886512081e035516040d109000c0a685a0009491038124141c5880c0440d25080d80d510f4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 903339910 1250 903338660 903338671
    0xf01060905010e090613050c0a090e06100807020a0b040308190b0112021b0f1e01181101050c0d020309040f0506180c070b010320043b0703060902011115 67
    0x2101d4003040c141d51b03030b07401c80741d200500940061040e480c3c0035400c40d2841d0880c003611070108154100201d94140002c9000384100d10180490031441d80c400b9040302c3c0010060300d00740550042c080ca82c000700d07400200e0644654000d48401031a41030a440e85500d102d081d180905e20355282a1340100035030b034804400c04401540344d070050b8850f00015203500e80c0c0b09042c2e00030500d5208409132a00c0000e03000c501e00342c02001c4513484a0a160b051328100e82a00d22650007c003446010003219000540d400b9035803a2044818035106003003a82614425260031f55182441c1c0240c1d0011840440c01e1405008418405581990602050402a011541c0120305661040d15610103000240082060f80f040e182c40079000450542d095a50b402d010451006404020000d40301c0a2022109800c03d400f90022010aa109650280c02800e076450509100e03025482c003050192000e502c4420000c10221000d1805500c00081d104001d20003d01005a152094481c07900304520303d05120f40440205503008 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 903341160 1250 903339910 903339919
    0x10b0c0a03031d030403050c010e0111071503020d020a1e0f021b0d1704061209231606021f05241507031706040b0d02011b020d0b0f01060905010e 64
    0x507070b8140c0d420110200803c00340510010a002003482800199030780d000d6001c0c0c07100c030003801c1c0100044440446400301949030768890641044100c2e40c50700301d08100c0a40c3c5c034005062610074000c0c0406e90340700c8030b9210300085041c20001c414280051403640302c0065410019005402050065106e0306980102e0f0755006e405182611607483d101040c5d84600d038000c8147c0b1001c5950001c4802ca500240212070004020058450014031b4500c111a10150081c1004a2020100806080d2013001034129107003400740d11884074010704040141e4000e41001e4001d48540c03c20310300f11000300b00e036000102e10114101005e00502c060300c0c1408103c3c1d0f43d088400781140304220008220306412a550002d050365000413a0720030302d07500c03c00c2d00b903940015861408540d252003041200351101a240c0641c049840c01d0b81000541c06401c2d0b0405000140b003080100040310f400003000c503008000c1c15542c1e201c3e04020080c16807241c00925002d00043c2c1014048141404002021040ca220070700c2d010303 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 903342410 1250 903341160 903341171
    0x90d050a020102010b01020d0f180f080f0d090506191413051905090613090b250903020a170705180402010207090507020601030821040c06090603050c121b0a0512010b0c0a0303 77
    0x40d18ac280a441c4040c08140d43c2c51b13070304c0e03540e641038280d65600c0c080c1c1400140d00645c00842e030014420044030301142c1004054a0400c03403a221861894030407142c006083c8136100041b0070b10010450040d00e4205500350303c00d17010506c1c06013030000840c0b01200c450700c4c1c1a4811028001c2d42e54103100190862800e5880416101c0143c0d020001447d00013006000a5010000c00003036a10054014400c1056554107802540741c000d01132b50008018080207500000d0120244071001503080d8031300e00b482004089590741a6100c000c1a40c003900d1120208482c170001c0308100565070100b12110040c400550100294642118020b44408040c040100040c800045a00401c000d80c0b211240b1140f07801142c02150400780f918045105003031085001080384440005005402841078901c96100202d4030f030b191085044412040100c024080c5540402c0780310f00728041074601c4060b10b2001c1c0c0c0c50700c540b0f5a0303251400f201c94400005138815000c16604104107402c0e2103000c01c1d04042550f041c10003288 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 903343660 1250 903342410 903342437
    0x90706170c07051f060f121505060301060e010308071a0f06090a020c1f050109060e01090207020a080a080c0705041118030705030f0307060e0601030302120f090d050a020102010b01020d0f 82
    0x4100403070041040d0000c401413103903040c90f4980e02040481d4003008050505650301e0900c0e801c585040c00c4050058181714540b030038040c1d42500490381c040c4005000107402c1d610360a140030048020b0f081622103810229a00b4100030420840504800000000d003815103091000e9040d4004010b001324060036032140403070301412154040d501c41c07291400c10f0300c41213040f0300d02001c11074a00760308001c045800e00300002001d6045110b10380560b403c61100c21290b0b8201140755001c1d5200c98400c0360880c1e034034000003840110900c00141024821106c0359520640c1c41d140518203580e07500314500c100e1070300c50707207044241c80c0d5000c40307440d41500301d07a241a002181d000641090243d0703000303540500920404960501000c0010003d51344a001f0400c01070820030001030360340340e007400000c0241c1c0c05060141080402840605094540c002580d40392841c00004560441441202162164020038910f4115a02802941e0314481c003880104142210740070300a0079440b581174001c05200721540c1d02103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 903344910 1250 903343660 903343663
    0xe1501030207120c170c0c040507093b100306060602031201140307090f02070606170a03080a2702040b030a170d09050f1507080903071101020f15090706170c0705 71
    0x500d104d0861174483c0c4692440c2c1c0420b0b103a6083c1d2401f148a81d03d4070001616442c0a2940c3c101582c400000d60607079a9aa1102000440911005007542c103005070605481c03801d500b881c0300e104902c0c82e810100c41c28035500c0e001d410382d50541c0000045d50001d00c0480c044030880515603044511200100d0180100b43c0b002c00d0074510785400804c2510b0800302d41104032078850f00100340352031180108002c8242e44100102040551100440083e0051184040030034400d2400c51340100b0b00201c00200f003065000e580050355020754003102410204031481082d4542403040b4161042d003a0050000b008a42e5a04000012008030201d120280481c014403101e80552200b94510b0344003040b20040740c0d501c1c03003441d564100604400342d624428400a04554802c50140b4005c101c5034004600f0b00c0459500d455400b044058400c0c1144200b8810041c0032074200640c01c98014041c0d20300c0a50304061040508080c0b0a030072440a100c1c0150020307128010862940e40e000c0e0301001840d480380300c4c91078840e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 903346160 1250 903344910 903344933
    0xf0a03020d1d0c01180302031c050d09030206070914010e13020c250f0806070e0418140708010c1b0303110d050f0604051e100803040e1501030207120c 66
    0x18401802e034110700d0b6140003400119140000400d0f01ca107100b0f40d640003c4801e07041c0207030000a4054005154025041703815407004401045070341440d500304031f042c483c07890443d5800001a80180e0214090014003070308690144043e08007030308031490509001c000a008040c0c1342000f140525203510320003200c2c05103030741a54490725401c5c080c1c4500300740c0d80c00c2940101c0c4807900844004a2003200004e19003501300100e104691281d4050007a650354480d00342c42405514000c6070304030703880b04540c030b041c41c03540404244030501c94032145110080d5080b2280c035000090308500516890100110003c0340c01400c1d040581c5540c40d000d030300c0d008291408402403e00494500302619020a80704545207098000030f100d146407080c841c50603580c242c00c101c20781390241e070307044811080c02d900c250142a015075181c1e48058011460180c0707076964141107245902c29030010303400d48043c0d07091110340f004d03c1448014825013440c0c15130420740d25444103401c0c20f8603078501c2801c1c0586c48540c9030401c50f041002c2c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 903347410 1250 903346160 903346181
    0xb040605091923040c05040b03060a050c0708190f0201050601090504020c0f06130302010c0c0b0103060b03120c25050105033c0702012003070311091906080a020f0a03020d 75
    0x220301a698188072214040e1800d84c0c04440c4002410070102d42c50400384941500c80100070010a095201e00286034004c000c0507010041b0b480e010000301c404105194010417000c8515418036217201e0040300c2c024460b04038542c0340b00469041c0024000076a82c814620b40035144100d0380165541c44c4452684d240a812041c40d17502e901440c000c0103408081c074145110101d00a4000f4000706102e103400701c403140b0390584000c04454140c0010310218109d0f40c4024680c0c0400340840d14150420390108005802038550044241d004d4844641503d0900c089000c880102e0801c0c001c0440c1001c00107070a5000040151524044045880b142680c0201c014542c0c20010707000c0840100007002c100c1c20158003190b04101643c2403503030a01d80340c0101a820710b0f202c10b40b5500c1c41c1c21601c940710110081d007891030300081c10300c509021070f400e1550b5a103c0b6107403090780c1c0c00504a2141c42d004020706200c0000b044001098418040450f1380310284003124108800351500503514404810302c4c0001b4043c00300c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 903348660 1250 903347410 903347441
    0x533131a09040506040311060c1c090624080109120302030702150a0f0c0807021c0c15050906060612132a06020f07080a0206130305030d0204090b0406050919 69
    0xc0c0401d022010644d18055800780d5030b0311507034128415803559075520030b807483c540f046420000d0440000e00200100e0b50104050008103580c4070a03120319050b1165003100360300c8440498a0380403411040361540c0001e01800740280222040d54440c281403518000540d0181900080041c0120b4420301040c180c10221254803015801e01032081802030801e010070000040ca010070700c0703400c24040c07009140300d210158001c1241d4400c160750510402c0ca4032100e041404004400600000c1007500411200130400341d0000f01803070011445490705001808060041d00d08002030394200300403070700c807903070240c403501c040080017146180446d9515145454002100c0c1d107180c0180d882c0c1d080300308d030710704403070166007280c619128007905140c980c452440340d100254000e9002c5001814128042c20020254401604ca1140e59841e032904507402144201c00f200e5000074140003407407047c4100d40c40103800780c90400040d4140b0b0081010513401900b69014038150204945c015a001e41005034810140031 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 903349910 1250 903348660 903348679
    0x40504110912010903020c01080105060307120f020a02010218060405090c13121a01140a031e021804060609050f130f0c06020705030f0a050d0c050106090533131a 71
    0x30254020144e40d14110014055140c0300b4402c1d600c1200e256040e104024200b134a5a103c81c2401d8503113900e500b600c03668558070f80300364000600c0d0310f20203000c4c0340c4240c1d0005659010040c1c444440742800900a600c1828280802e2020f51504420142d0251a030042c0f40d130b6500b8296400c4000c46d400364000311100c0301c02c0c2010000c024000c0d5125603140e0110740320f09056600d40200032003102d9110300807500107540c1082080841c5030010303010741020038072180400c1c815840d004903074000301c006500c220300110402804100031682c03191000401c403940c030820150070090401e440100024041031040020080c90f50188500500074240c070a920040911600e0759400e0042c3d180d15403031145501c240194000ca603034140c408507040c21100d52000103005400b8203018292864411000d043e1907a65803144c1c041501941032003520300410645461600040d42040410324414221141d581900c403042c4c088070725a04d4180c02c512605070f00d0340e40800e4481802031583c10314401c010b8080e900c2401e04 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 903351160 1250 903349910 903349939
    0xe0615090a06081e0c030a0606170120300708150d12020313030606050a080f07050120030d15080a0b01051314010f0515030403090608072f010b040c050405041109 71
    0xd0f0700c4981200c4100c022070000000b9500d40c642220b00c2c90704080d8003e81402441000107150700004c002055008803074505827419254400850104802d04030109840370781440b00710f40c1c0040450341d016041014140c5440c0010340070400c1e141401500503c01820342c00c0503146603000740155907202c4400c44550085942d41c0c18418050010b170302c5403901900c40d41d01c0225141802107100001c03500d00d40c0c01082e5491900c001150b064945d00c40503032030301d0f0025a80840c0640300348000d15106800304000301d100d41196080e0801e048003076011010f1640024211400604040381c11811207000701c900c071404400a00800000e000032622440c1d58900000010840e00020500c81d41a0740f800d0726020040100d000420341a03100c160b0300640410a07a85c5c042024522409110780d0040c01c5140a0a0700311a100c0c1c1ca18032079030900e200541d5001c403613250017503841c000d204400300d0200441e0b00707203d0100101d04c003401c54403590154502840c2c8075103101e001444140d04851000802804900340001d41 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 903352410 1250 903351160 903351173
    0x8191b03141b1f18020f0f01030b060307030501051005190807030b0307032105091503040302030f040305011a061801051e0c1b0603070e040f0e0615090a06081e0c030a 73
    0x100e81d00c11035054508220104004d100800140e101c0e940a0400c0c81d000104034100054070b9030b11102c8504140e240c103141c16450701c581014500440b9180c40100e55541401c0400140112820004041010a00c0408909040d41e14803190a0340035007884461515001e00c120050b05205c1e8041d40c00d0f104506002003001030041c100e0140140c40c686c41e1104030301c04c51003100c0700e01c603886d202030b8810009a0410000b1210000445d08148640101c92420780d051a034441d4a0b00180d2080e40d04d40d64811910003403140300005c0c0200810115400e51418542882107031041d80d04050941c104100400c004c241007000c41504840201c4070081c59840c0c581c1040303100d6070b0312424094109103001c1d0200d07104a5084c01015a0b00031034154a030301006054038802d100007884c01b03001c0c1c200000e4940c0d03901c0c196040188251800ba030401e042e0300c0c041c0340500e0b0505c108000040c14003418140751040030054414041480c0b000306110b45072003124405404401e610b003a27182809560b00d0b00407100d0b10410440b0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 903353660 1250 903352410 903352453
    0x30d0c05060603010c0c24110901030506040506031b0303160c2909040f1503030203090316140f030f0d050d0b040c0c0b06030a08191b03141b 62
    0x2103a01280c1095444000381400e0b80d40c01c1d040c55021070b101000d00800160710080d0340e20303840418409080b641189000700001d483d81141030303001c5d050000540029a5030b040c00382a620030425903042c01a41443c0300440d940310409849007540d078900c00e1201000f96024022101410300085d10f90703440e5403c40c140118a4069449030b500c1b81090595003081d0425282140003850295014440c20101c0100610000d418003403200c04142e943e580032000b01d4914000d0000155010394000c41c0c0b5003001505040ca0100c08002c114407140041408204010f000072106400c400107403200046680c0500200c2d20700402070540c0c400a006103217a08005580c0900509803025442d18144484c000b1881400106c90304501e84200242c0c0284924007ca9610804940c00440260032110b050040d921a00016002000c10249503011b600381c244020754402640c0f114074864200d8007061916954001d01328601c0c85c00a040e13210b8010800d04e8107450000421031100c020341c07040d540b1000c4e400d90040032012 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 903354910 1250 903353660 903353663
    0x90415081501080a06020306150c0109110a240302090d060903080a0203040503090103091403122a04060e0402090405010e060108161b060b0a0b070c080606010f0e0a05030d0c 76
    0xc200440714607851801ea0352a03040710959405018000d02c40c0c1c42d011301135407009203c0740d0040940e03002e8146040c5a103000b0502405d040c07000203038144682c40d010146411a07a403007403080c954118240034160b03801000c0c0c5941d24191003c68240b011002c410340c080e01031001403d9015400301040300c1403005030f811600469129036180b000d10f13954422a0001c0740020358000c4d25541c000c2c01658032550207640090703002ea008030020036803168040520307495076005030a00542e400008060084509504807055a507035510701c41090716000034482089903001e94440c00042150003030740d82c2c1c69a1a2a0304403100b10a000c1c1090000d91f07110503440d0300c81d19090310420300060b840c20000300b142010034940311000c1007650715241901412464200ca0540300c200a5605541e6800c0b43d278880d1362050b0147c402010310750f603013a40751001402c11440509883d13024002070b81111707003003200d0b030f03030b88261b43c031195144d00c2c10000c484151344c01c0800c441c001c0a40009405104002e640d108154000c440c0c00301c00c1c0d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 903356160 1250 903354910 903354913
    0x2131d010801050906040825020303030a0c0305011202011407030507050a0c0311040c0219050106080d0c030909060b1c0207061109270a021e0a09170d0c061109041508 73
    0x50700c6000b03a16170b4801c0304071405440041c007405426000b5803000104220b488040c010f0380b407162242c2e0002070441c0e0050744c40c00d044559422041d4200b5805005a60041c007540800c00c40c102e640c0e0300042c040b5031400c80441c140c2d2900244900401d4082c0c01519500364010040320403030f0040c1e02e03000512420134001a200c50b40491101105031819026000415074141d000d0502c8519100b110b6841c0741720000c04580a540340e080102c3c11100c100900000301300b0b01d9850b11544080740c18050043c00c40e54202080060600206100344001e050464118070310a4403412840055080080000c0c001e100d4011300c21342c10029461229108d6801400c4080f1084403100104803007009a0030040e0100101c04e11030105400000b50101c442c0c0c0d000c6c2001a44140488140c441c1540e800c0955a00c200c0c242800300f041c80e001440701001d801c0d06100c801210000800c1c90710b90010014062079101c0d000207203869221944904202e444100b518107400c0701520910102051350403403c0c4400e500d002e0305103103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 903357410 1250 903356160 903356171
    0x71d07080c1b0a11040b0a060311070212010603110105130b030709121a09160e0405070e07080106020105070912060c0210110c0c03010c050a110c0603181e030d02131d010801 76
    0x13145010f219900c401ba000400d03400c40f551400d13109401a010700e001020243c1c00500900000d80c44002103124020f01d44400002d030181540740074000e07180c0e40440c090401c40309100203400b102300e04080b8416202c0c0c2e050803603100d982e00d490403100401240c002c4d0300b605400d1040394040200c482210800d5840c4c008410500d40d40720507896543d51418082d080312998000000c1010309400d00d501c42e003050252050f200f0058654501030704030340017030f50071400182e06413004024065080c46101e030400c03000e02d0059a4640f8014100141b005004405455990b40710000030714a0300070480525002500756040c003403001d00220021903a0403000803660300d809003841d8040b00e4a018403c4480c005a25150380b81460401001118001c5001820782118483e032246240c2c1c550342c00e400342d4400d030141511600a01c11011042d400c060385101c4900c0507404034145426078403408000c5c0c07005039065103401603c0d40d08202a552034250305602640c4c64500310081c1500142c00458103078140c03850344009008 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 903358660 1250 903357410 903357443
    0x3191206091104050112180311010b04090f02010e0a0314032a06040803090109080424030c0905151e07030207080714040209061c020408071d07080c1b0a 67
    0x1d80d419150181c1030010100001e0244d580200354a800a00ba81803000038070b503003041209485810380210550200d61060300395001250240241030030300e402650103200161040d6141086142800f100038107000c40c0e1785034501346460b01403120f8000c54003d40c42142d81c2c00c5c80c03005641c41c0c0d4000c13000740410380800c4074501c44203100d0107030300125480d804000781015950741e2100c0d429608090007428880d5201c01c40381020401160203800504912901d9940018500154101c000070f1032264406060620104000701d0750040304072000c81d181500d1002a8a4046001e10041d10070101242c8414030451300d11495000400c01406070144280c080b203c003d41c640d424542e072070b00b081c880c80b0040001090b8140c51030800360041c0641040150079681840c0c43c15038942c0005043c1182d03032003825404541003180c0081002204c006111060180c0a203007900d84444078030100041c000000c5c4000d83c000f2030110310301c0310b0403514988120441030380064510b501c101d1319182205410f9441c2c10b45480c40c0072 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 903359910 1250 903358660 903358679
    0x6060f06052d040e010303030609230606030a1d0d0314150f010c06050711120f1204140d0216170c09060103021e0918060d1403191206 59
    0x104151102d81840c1c00c403800d40080b6031101d003850038503110090014003000500003599070031540039601c6074502144041c100245101140e0844482c6003007881e000c003400710300c070756102140c0750041e4050300c0701c543d00c2d510500308401620003d20024030242c140c01031041e81a00125010042c00a0fa036004e2001c5802e5041c2c1d0b240c10f40c41a9124044444140b10075007040c6020451004095810f040094003400503407030780003c4800c100c40b00804214141d50800e002c039404e0005034001c1080b0034107541011440700300b8040b14040c014130243c001202c000400c00f407080d891800c0482440c40f808a07403040c0d1803484000d40300c2e0468402d421027041da0590108400581c50174005602c14510000c12548003400100182030310040c3c202c0d814503908000e52151a81e040d0780c000164041100c81c01d5a4450b007a09001700710000c00703400703203002c080700c0140078040e603501894403e500d40110a22084400f0035480d80d046100d1224001d02812060714500ca005401020126084041c11410001107940c0d003404c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 903361160 1250 903359910 903359917
    0x6070b07030b150417150c39070f0b041e0f061101050f040b0c03151c02090f0c040b0f1c050609160f1103190309120c0203030301030201080601021906060f0605 70
    0x86426079138503c00191070490182c05400c1402185007007000b211010149904e0300e080003000c23011842020303407402c10320b200c08101020042c100c140e0000142450206460030b035010728022010004c142c07151504507103514018030400380008020155007150303618009000d0844030440b0f8401b030750034500000c418000620791a4440c3d5003001607a207195860340c01c203004681c8001e00486103500c40c616a21820341300d10000614001003031002360340b0103025004114001c00001c040070304035080c4008004010085809480444d200005800d8a6820220080340c0c41c3c042e1502012108120124000f54104a50049801003105840910140e124012103a0a6071400f070113010224071442080540144501c10311000d404541d000e0300c0c1010005414840083d4038040c440001076141c003100418001d41c0551243c492000703041c1074240c150f1683c0441c0d02c9000500c4081d062040e41c20000300a039000707026410415440c07104916014020340707001c8000b8500f0340180c6014903580030340031420f537001d00c08030b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 903362410 1250 903361160 903361183
    0x11090903030601173106060602070f0f140d02011110060311041b1b0512070303051012030503070e190806010506090904110f060d06051302070206070b07030b150417 72
    0xc0410600d003045040000c40c82d80005c0b40202d1321340341e540c2030100d0030f50310400016000d00c0d03010300101c0d427818441004030441900700e5200d8030258039041000c03400f908000318140c0f906550605a18001d0f000596200d0703c82d03c6121818000c500c004102c0804a074860415a44036a4544c40d80421b02400d110885064010801c103042480c4508c4400c030b80100c1e80030800d11204020b014540ca130960b80d040c10000e1210311501e00043c081001c1c0201600350141541c840f08201d5480e00c0540380c40c550424000244601406005002000c5544540324401041030020064041140b45940860308030b4100028481c070962402030b03400105051500500300c41e84140e000340304c55120344864640702c0d407559142c2c10603a40301d80080d401402c50340716100507215030b00052500003200c2d881c0c8014400c00c1501e9680b515200740c8100030060041e41e035030341682c60498001401c0e00850366400f009074000d00500c428a50300078094200e2200d0010850300402c2625804c040e20503190a40c82d91051f5a0941c007a0b1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 903363660 1250 903362410 903362431
    0xc02090a0e060a0e0d09080309010c11030a050a0507141804051002031806010b03060a03110a03020301090b071106130b062b050c0604080316030c1e051c0206070c1109090303060117 79
    0x649c4819840390803d915030034001c0700e1021410301c01c200000d140602041c800c8038141c2042c003401e0705104d010b000e80c000900328030020101c0d1511042c0010b06100c441034031054508100c0e000300d020f001c420006a0740d1010b100d2030840d541d05024101a4100031010390000b0a4800c080c00416480001c106590080e90081c05400e0f001f4116951446d03455a90114075801c9003022000001680c4e0900841212074050104070303407070b4208420024003800c0302100910440c0c3c81081885004281da6001c5203100c1d401040001c1170740c40300c000185155014910381880c41e001c18089008490904003e54440c5100c0c8046540d40701e180f5080c401c20380202c0c85007914a40040c0000885083d0064100b903a45d0b10900e04030321520b041d81d54a88880d006070030301d910320f03103041d05079202040304c1040050a9035454040180c2d1803500024020368628000300031104110340181c0075001c01c450911803401280e4010710000480c901030601c195030f50021907406001400041154442440040c2e0950150340b0204 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 903364910 1250 903363660 903363667
    0xe04120201110f07080d020a0305040218010302030c09041b060809010b04180807031206030803040b0106051819030c17060601050a0c06020304020a18090506160c02090a0e060a0e0d090803 82
    0x400c22102d410088040d00c185c00100302628004801e407008007001d141e15180040c0d0f07400d1900500491171100504e249400178902e0051001d640c1c0007601c00040c0c0000c076000c1006c0d549515012550341b451009204007040c5116021510a8100f513215105082c0e14000300001c035519410403080e24024400d50307003031801411a500c0850244001814194082e0030620407202d0320000007811250301d41d01c103954540c4080144400c10030280b5a13640140030340d02e000e0b400d010818a00315840c802441e82103215441031000b150484111078050401583c1040350403203503540d030f1401074a9a5405542c140f106000d984001010307076004100b91a01d940e1250340b841c200f40c4e000d9855130b0095001600699000b101010300060010021070302051210641e0f0000c10910b03000c2c60460300e1b05a000d0080300720100035514043c3c4ca2544441701d952204d404841030f10300b5481c0e1201c0200104007030f9040071300a01603402000504d1500350080480b5440c1802140d4403513002800840340940d0034040d64100da0800c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 903366160 1250 903364910 903364927
    0x40f060501080f0c0f07050d03050714030a2f07060501050a0303120b011209120806090c0906090402130f06020607210b012a0b010503060702030301120507050a0e0412020111 76
    0x22080301342c0c440042d09043d441d000c0a1030a10b0342c1e90b000820115141d07400b80e50000078040c0e05004e080e410000f00e0801092000c00d960300030313416020041c000164255074400303c00d402c0200c210800700300b440e803819025103444000007840c800d5000e00b200f61942410b100000605090071000402100d4141d542d004040240135880000340c02018866410455121820180a441c0d80f00c2c02c181148140036590410700318002c058140c0400401142c4141c200348100701c0800030580446155000450b0a15501c07070020002030001c0c01101a00f42211003805001700d0002581d41008059407025003c41d941c50f0342c1d0b01c0003168103100000d21205c1051102c001c2039404030303c5810030540b0040504180c007030406084410080c204001c1c0840603030400e84080f4805116070b22500d44e001d040d00741c0241030249001b1201079600d11041c8500e8103501a005840800d1001c148820340c00303020000c140002d0143c1d519441740045900796030a5442004090b84581c41c14014410349401c00b070641255810205807 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 903367410 1250 903366160 903366181
    0x50c0d02031507090b2b0905030409021317010e1c090611030d0f050a060f0f0b09011403150114070203120a1205010b0703260105091009020c0c040f06050108 69
    0x40d0280e07007880102c84021034069150805403290b43c0702020142c003100136550303040b00c1d0031500d1b03034070f041c8440c0ca0b2020311004140040102e40c10789180b13910159484a4181241604c1002030303008500404c00300058001c8941d0641000b4400011441113554141c2c2c00c0c072288410020000209020030020081005540c0c001c1040c114000c8031303802502d04119800d4a000140d031018246440d20715039072001c007e0700c10480e22402e005000c480754040000d03403c202c8055190b0030380d4000c4200924001c100748103da813041c000c1003600e4507080451620b0707082080340d243c100f045421480b0300bc100e034040310144100d0f000302aa60050f400500404841002181c0748500e58030000a5008002c10508040c03084a140d010301390003881d5120010340d5030542802d004113510b00720510380704c40722000d031140e941e81c50710695907074151842142d4003461603c42c1e1000301100100c1f039002c0081a400421030b828801c5010800703225001d4180c400744400d042000c8090f0403030740381d80101408150b1880206442444 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 903368660 1250 903367410 903367453
    0x916080f01320a0902061902010c0c0f0b06040e0d080103021815010f020f010c02241e060301181a090d02100203060a030204060806160503070801120f080a0903050c0d0203 75
    0x103a0100020030044e2078010554680c010710000800c0f111040b003500070b5550910503103071403844514258052050769a604851540e83c00405040c0c03e08010100c2d4055990350301041c8594141001c6400b0300c00e0428003e881c050003448140e204180701845161034502c20344050740306140d882c01e001c85541c0810015a5202a40300b03000303085100f40c1c5404109481d09101d0b1100d900003a8000f08540386642c3e80c16688440c10307002016408000400703000002184002000c1004041e482c0c1702016622000404c0c010059000765481040c520113044090001c2d00829190b41390b03588030109116625107002507500c00f041c0070303000010b900104032112103482d80d5000e59000400101403408080d0baa03000103056491641120303040741c114009100c001ca23071202c0030194024041c108203003140350080016003a0b110501c11b180310a4259030260307080040f44410190340030341c0041c18540707901c401c2c5002007103c1000d0204603070307612941400448c64500f420750304a00302d50042c020104002e206c80300c1c426582 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 903369910 1250 903368660 903368671
    0x3040323070f18060819170c0a0c171605150c07080d1106040c030b060102100e0313080325080415020c0f04180602030916080f0132 58
    0x2114000b0806240400c1200018100c924002d06007108450621040b00c6680c0d10244140c0c0c03000183d0316100b00240b821481c0700d6081141c0080007070940d0621911071041009521031070059280d01c10801800540c81800d607401001e02c404003201001e40290b5030140008242c50003460034000708594540f600003c1c0010700d0f04010310f4240340000080610f00044c580107466150003082e03c00b041c49900140c11000360925000408150801c0d0300d50040c0d0201e00d01014001c0321001000a696900800c642d07082c101c0401803c100030b11010021340d0b01c0c0d801000c0031108904d1040e1000030389a000000360745d6030208000e10407003c0000ca02910282c86202c0c0030407038910209210005144140008800c00f08520f6005892141007000800540204400740944114940b06041c03200c501e8424107403c0300e40d400380c80140c0d0b03501d61500c06458100380316030001703651050100200d41441c3c04039403101c20058a400070b010b03031006040ea2143da607403044011801c1a807903414003124641d4003210f054128 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 903371160 1250 903369910 903369913
    0x2a020d0c11040b0a080102250c0b0f3703060305060a1d07060504031502160204090203030d1a090106111b0103110f07150e10020d11040e1803040323 65
    0x11030300300f008188449040c0c3e04c460896540400c80c1206040c3d1003119050b9102841c0c6250004c0c540f0707980310443c44005e030041c001d01200100307001058900d54811600000a0324116400e01d0805006981c1c100c00c14042035108000036400002c07802e4001d014810a07a90b01c0400740c07016a81e1524014000c0041100c407101c40b981c013800080500ba0180408000751926540700f0b070b034950542c100700074088040550181304034170400c1a0380410340d121b03082c50105da6045030702080c2c020b01d500009240d03000f0101182c0001e031405d1650442d640d4588010500700074246d8000455171380c0c450007918200003062110300203400c00982c94080d0f848402c034464240f03005041c0010740f422414000d0651750020323444058844c000080704000d0001c3e0102e560aa41d01200c01444009408890f031912805200c90003410300d600802d1440b205005508101c2c0c03110146184691030340d9403019850500c0c00705031b0707854025064005070100e5030348001c4200c50680b9004483c114800e2010042ca89450030100c01c50f1645 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 903372410 1250 903371160 903371171
    0xd0203250210081005060a0906051809130201140316050a021c050703180501020c210d02061008010b010c020d240c030f05010f0b070804092a020d0c1104 67
    0x50703407018418404400740e035603400f0342440c10300704054089640350040e520a0806009044002c5c1d403001014040e141c1c1c6203040340c1c6445114030b1018440806d480c4503036100031500c080000400065001e03949407030003603071203404807000161000d40b28403013503a00c0303940404c419000401150144004103c1e01440e84112030941d04100080d110525587d485040022030000f035620600d944031821144034150b03600d50082241c40c00300081e54a09880c0000d0340144007480b8000d5260f141d402c3c110b1944540103099a814541e0084029114002199001180403003c1c50206984070144958044a036042c0c540300455002c94003008000501030700c0c2140d90b104911503240001c11921000300e00c3d80e082034008147c030204a08050165480c014040043d00e00d4a00104103803000c0404407800c503002c84c40748503031f150100c0c113100919108640114100c5400c203224540480c1c020a210308060680c0d80200c0001c0042a500300d03241c00c1368101e040c0000b081010400007041c0a01003003400310310000c100162 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 903373660 1250 903372410 903372413
    0xc040f020f032d040b101d07110304091b1806050702040b0402280f030209030705060c010209030607090e0c0403020d12091703030103060609060315020304081201030807060c020d020325 81
    0x1018101120f0440e10b1a00501c184945481b0b41e800c1030700a08400c03041c2c59081c204031900780803c884010040f030700304003003040e0b500454441401254060102410103000d038000231900c20000c2e01d88000194001000e08900040414030742c032500d0161006961020b240180d42c0c2c0800014001440080b50321039402c02840380c2114030030702d0600d01000016103499501aa078000500400c2c000c045210915004110901542d035012a952080c0c03482110400c2c1c0b1610050001c03802809030800c51601440341e08203008800f03030046243e0040320403001f0138900300e80e01d002c18040240114800290040100ca03200c0c070015a50b80340a0200d04190f1810205040e40e80e803c034080302c010740d0410071403508004014401d201c114041d0002900790800180401e0786540d98601d00c0500e40b441c007801c040e03400710120300bc1110f5241111a20705d005090150b865840b414003103c40da000310300454034030b0320305518400ea150011690a1041c8240e401841c10f20726140c041003d074a019062415603560b00c003400c0d10 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 903374910 1250 903373660 903373741
    0x80d03050601090f090509011a010f111e1015060509010e040f020d0b130c0206042006130e070305010302090a09060209120f060112022d040606020c040f020f03 70
    0x10401c2d0171003c10b540c1404581e250843d42c48104034616038200f401c2c407000598015000440d41e021034501400c43d04ca0f1041c1e05814503003114a40811a03580740458003e40200241c0e51035440c0d90814100308003400c000d5200000c0c6458840c0b40302084082c08540c00642c00740241813a04200604041004100e198011089908c00350340240c2e603680d41e00ca082410700f426200114030149c011010000e0703940040001c0e58400008000400a8900c010b0321150f80c1504019405511b0f4003600898071682440c0841484606901414002144480010b80c45134400c0c0030729812660050283c074040d84840900501604c1030540a61385181c0130000010941c9410075036000701e0007502c2c041c0c198404407801c501c1c10484181d1224900f40d0751078454401503503400d01c001006014420400d61482d41564407101410094811154424544840003443e40c0d0045541c440c4402c04075010440220140c0d0048124040c2e428040002c0700140700055030400514a01d039003840304099145800317101520f184 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 903376160 1250 903374910 903374939
    0xf210209010303021b030102040b0d02030907080f0a060e19060b01020c0a090902040c0504080d0c03111c020601060c150908071b0602070e040327080102040303031a030304080d0305060109 82
    0x40f80140e01020713080c5000501c1503514034038400100d000307510305071908240e14900d0143d0030400d010a030380007000c20a007950400c503900003803c10209488880074440c142d1601c07102c140300300f0b9881c1400c1c06442ea00302c0c000414a4200c0c4c411101c0c060100c02d0907601c40d14020268102c0c20750540c03241c00c040002540d110911781c001803001c103c02182e0b8040c030b8070521090703941820a10081c080140800e02284501084501c1d03850150710708100c0003500c0b404d085940160050720401280212030341d900ba038121604012407400340d15000c403500380e40d0f0785408030f03401c1ca00309074043d0403041a2a88142443c03165044843d546000e14002400d101c1a81c440300076150f20034640e0003032400304200c104249501032019000400d81d11261100324582520050125450340a41000b01d102500c1d0101401c041c680a00010b4a12900210348903500da142c06030040078028030003941e100c1c00310030070700c0c5a213800802c9400380c889040240412074030f280303016800750402414483c14030109004c0418510f0900428 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 903377410 1250 903376160 903376163
    0xc021203070f080a0e07270b0d111503040501150f0503070e0c040503060c0c06070203072d14070504180302031e090411030106031d1c1b031e090f2102090103 69
    0x26403950f40700c0b41250501d100f400c200c421080d6808c000740c0c3c461070764484a2050025030001030960034a1120300014003801a5204680292913000c020f0000307001c41540100102d0f1003d85000111030b4940d06c02d044200594031600b50b06901500003130080c500a01556900300101d001e03803030704041e12a0002420014100e428400c0b8000214001da0301c8481000695000314480c0003461070b0400544914031040d440b4000025910360312100801e03080501d2401c0040303550445012081241560007003501c1c0c0c030340341c8550b602c90b600740020078028540904a8200c120b9064000350701d09844500301d00e0507100700c904024516042486480000d8032680a500404100c0c41c60b0345aa070343c10702102600312001c0b400d12901400c01c40e12504800c640c0040e00c2d81c0c05e680803803400c1140f81170b010800c80354040b5100c2120003001c06040d14004158106610304040f42d0100325003074072001000c5049239a640c0f94895458000141c0e0710420040281c2d65600b54160520702c031003d9100001c0d00801c9194100783d00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 903378660 1250 903377410 903377429
    0x3d1b050c01080a0501080a12020c150306030d03140f10030f03020102031923090709021305091305030d0c120c02061603020a09090b120708010c021203070f080a0e07 72
    0x40040c0c25a4404440d0340c0c02010703040108011350518908035910801628024042442c1c2d01900b24064000c00c68914030401c0206a0b05400d00c50003501083c035003003521014000e02c0b4038800c0e6070b0f20074024002c0c24020b144110a0200542d2080d440504018004c3c00e4000b2006040748040042007058440306019406600056074030704002c1c81400c03803003180403e002c200314627140b4113194120071804044680070034440220442c1d1980c800103810100c135030744000386031440050400e401100480e0880c0072210700322011001641e0b501101401c00c0f03011170f0004c003141c1080005140d84281603200301b610313007401e14102002c5100140e03440700f162008102c40c00507900c9081004200001d00c902140d08000078a01581400c1001d2005450745509024981001e6200c9030000d40e603480f403c1c00c400c099107490342100c03400350340c61064a000303041c0c038621740005001d00b50f103410740c012800080b40d003e03102e15940c00b6071410074240d0131103121401400395200d09480e00300d070300403525041040c0d1010f03012481 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 903379910 1250 903378660 903378673
    0x18080702193b04051005070e060c070311060f07060f0b0d052109060a030f2d110306060702060738010f0e07110a060c0302093d1b05 58
    0x2c0800000d081d2441d0054012040308000002c4c60105040e02c682e81e14410114507915411b00070f0b03d051040c125020b40241e80800c00d400345100000303801c2c080300d0188182c11074213900c210138800e842c400c10046002140c010008600003500f283d0124201c00c0306c0c84000901c112014001410707604548030152260f0b40b08209800017007000400042c2d0519911124a1a01040d100880c20a0140c161130724145a41d5230011000313030016400070309040341c4e01080c1144000a5103680d8114021942110040c5841d0115442040c41c03404100c90003058000d14890070802c4580c2002000d40c82440201c0c2d074090400031a15620880030600200440c501208500d006401d05408201d07060580c04075124a000207030410200304443c3c050350304220f0501d45120010340c0290000c2c07600b5841e80d001448a450040c4480c80c03036906070b000d4201b4070b6045800c236003040d41400d504100c00f070614203542d500406d540720f00c0c150f103014200c0350001580343e1709005507404840c00060052007280c0c1000d5176075400c8070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 903381160 1250 903379910 903379979
    0x100302030a14010303020d0c060b06070303050f07090b09040c0e1306150806060a1107120803060a080a030e10090e091b01080403141b030d0c02011808070219 69
    0x5000300d82c40244409900300b440e603d1614020f50742c02e8030058420920998111941c1884051382001c4201c078806860180c1e19481450014002c260496481a0301103600c0c01160b00c1c14442d003500c0085401d03081c0a03e0400b0031401c01c000042c15082c103940c00b840380c83d820001c1c0980300e422205602a024407000144203150010b0310f000341601004034010170191604000c2c1c10303514402610288500c0307242ca01c00004076540c141c0d00d8030410360402c401505a81043c0f008101100c4015441040d0603541d01d002c20395030344c11941c1d4031403c40c003004002c2205005030614504100007007600801c000e29042c0c0d2402d580342c0d6805013103202a603540e00c1c517402c4003d01d80400d4a1844500440620078a03040300f02d854075840c01000d28100c4901814075500001c0d42d101e20248229010000c400000c042c1d03607a4914012100d0001e0107068007142c050350a0044940140400c4080c820500390403100c00303842c2c008613900300003043c3c0c49001c1c540901c0c0340148002c10801c2d400d0054800000b84182132150040c0c0d40b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 903382410 1250 903381160 903381181
    0xc020102060c1c02031815040501060b0301081c051c0501051509090a05060f040513020a080d09050423040320060408090d110411040f0f050f12030910030203 69
    0x4107400400d2108008804000125080a038658114a100182c5a88030501b542183e03a07600a6843d80740d2160a000708601014922410300591091008000c010360b2218402c6a6000910070384910f508448504140c0c0709030060340104ca01020f29049203811100b600001c071f01300030612801455590784005101d14140304040a007400e2202c04094241200400082c04a0380028064800d8039200e80118020b5107401c02c040002000080062009103050b81195010b030075041c20913171081701180000186102c0204410003400c046594407a405406c0209100213892030000071420000c00382c1041001c0f510000704180510300c02d558809040d51070140d54980648090703944140c0f5080601404001510314080b5040010181c0760404017581d542483c45a038078074403d40d150014107101415141440280044c02640c0c9580c942129554855400070015006809070303540191004401000500d400c054101203c04604100c038a8048000080707410645000c15500200740c000c030900a14055 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 903383660 1250 903382410 903382423
    0x110a0302041d1611010609050c070201030b040e190503070c06020c011404081f0207023303040b070810081902010e090405072303150702060105090403021f1404030c020102 75
    0x1030b40751044941405581c06103011021803035071003405918159800506030a400c003200030101c1c1d95003004145028800f8460550183d401240000d01c1e040b2030702e9442c40c00f44144410100c040c001081d04550380f88201d041a0b00c83d80060302d461005114000001d440c0c00c8400303001e00040d0b400350040c056081c0015211500f40710381641c240700d0a000c140a40100041c4000e600941c00485c1406400700e200c10800030710544038045d420070141c0d0f860440c135400b20100c0303140c000002070918000c502140c00782001c90000755030081c0f68651100125503134512403504d65400046e2000c12403241030340d58031003038500f40f0145805103251110021440c103541e000901c20004400a8881d041640303001c1c2d660701e8407440c041c00b5000ca020140400086648200c2c009005600b5000e0129042a200c0b07a58440d0000412550f4600520485002140c141000c40b2424000c580c141c0082428060464030040003030101c0c0030504030190b0303600112040f4100090003a006900a40740d00200040300d0000909110 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 903384910 1250 903383660 903383699
    0x720031b01020931020a050c0f01151409040f051e150705120f150d05030319060605120c070c0e0609070306060e060f070c031b1508040303020d110a030204 68
    0x404041303078544d144032400215840c0241c9200050703480500c001c09484e10b015007210122984030345c55107504140c1c01548111075900100d4402a1510754840194040007202c0210700c1d0000c0705d44010500241d0f440c0b1121244074403440698952503a000b207031206081d000c00d0b10305602c0d0702c03084003107144140c01000d041e0405c0f4640750281c501000d182c800102c28001410343c2c40300a2084000400c1e440c03070070709400f00351000180b0900641c0007505080395250015522240a9824078035031410040861207200300301c60741c940702c4ca400c0030209100d010300864010404a039103002041117000189000b841302014240340c02000160b401d0290a0040803240140070406051401c81c00740000d9400440c3c030340c80c1030300403246103a0f902202280e000e09030290041c0107040428602c0040b04000130701c2d0040329007002c45c01017a401d0507610910941034164403000b100100c3c485401140c0401d03c01d4004102c04440300c1004200394540c051910800c0d03010f8003882000990208041c40421140c0d180310136a40c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 903386160 1250 903384910 903384949
    0x6020307030801050f180a020a1803110913051f0f050403141605010507050306031507080a05060609090c220b04062001020309160501080720031b010209 67
    0x92041c1d5400b900341241030044601c00c03d55045840000d0390703907004502500b4038500c5100c1040c1841001d50b00650091054200030646840c040807440700088041e0044a4025040074064030104081c04076044014120b90269961756800c0c1001c43d42c10030007041c51003d00610026040146101c0030f080f1004d11400030740060909080c403006c0b0380c3c41060700c04083c40b44001c0a80d0350b1883c4591510b04054900014041c3d400d21080101c800d410901a5103e9101078040d190403141d80c41c0c4c40c480340b6104030b07800404110031038003181e44011680c0c05242e0003031000c1e008926001c2800006203000e04111142200c0b40e00005451014ac0569154003020200c012009841b0506051030500d140c09107004040410000b41620039400109201944850011000843da02d0400e00c031000c1d03c511400f96240d501d015000400140c1d548550002403041c8220383e51070441404a00c40c5c10384500b01c07014103208904c0705000b00c000c500f21000e01130a0300e00840000695a0031401d040c085c800c091468800d054 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 903387410 1250 903386160 903386167
    0x503040e07080f0a0c02100e2805030d0b01030609020705061005041505040c18120b10180b031609060302030c040522020118060c03110102480313060203 67
    0x70414160662600154210b802048940172554101d00c3e1500350114801c4607404c007011241400b0000c07540242c0c000b0070075181402d108100300310000000203048028115401001041400ca200394012500301c00305260100712a030b901d020f0001603810521065660340c000c401408605441040007900801381583e0500000c0040218601c0340d210343d1060500035511146e24040c60b40c8a80701411030b2080302c00240c1440c54031041d032041142c40a100842c2c008402502080081c03019015a50480780040721824880500a04140c00f0300442070301c40341c140c4a02d602540301001c51680c1d500140204110001d2200e140d40109881c1076101080d0302d018a141c030b024082c0c203481c000081011780a0340c0e0f559041031020b5100488403244003041424a003041501c0c040340345503010b40c21804040c060758410b6001a0703120092801c0740f01e03c010307050313080c07101d0b12000c04c00c202503044248140c020055008209511210085125151b40c0a1f020440c0c00000312508003d4a00301c401d000307064035200840c01c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 903388660 1250 903387410 903387421
    0x8010c020705010e150d0902090f01090c1b021207090234020303121005090a0b0102100e19110306010801020a141c11090d0305030105010e091e070207030f0503040e0708 74
    0xc1115a9010501c01c942c000440d01506c0301e0503007149000707071342c060064003142c609607a5502c40ca441c00c0c003075407886504010000d0900c0d0710550b010880c241d180301d2800d48040c16036081000c2d10b0f07210039865020b40151607001038030402c00c1c03020740b502e04c001c4902c01c20500f102d4002d6040c410030f0340080141452200c8005030242e200001030740c2144a8000e4403540343d840e81c44c0ca81c01c1c2140ba55024a6000d00c0c0007080256040e499000180360500c01e80072105049090340041058650141e10344109610100c0d40f192100002d1500111a40c05000900c00822003038002c241040c1c400d811002c466900002c80b01038041d40100a80504000c81030b105041140b104042d41e00203201019220f00251100c60a684031003500302160106180200a04161001480c0280460b0003d2003450f0201c0c1c40c00c084950f070b500301400b030a4824a0348011084198003008000a842c40014100c44214030440101000040c0501e408942041c003030402151240c1c901860350500c104000c1140381040b0040c3c09220 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 903389910 1250 903388660 903388669
    0x2b110304152609030d0b06270d02041401030302070f1404021819140a0b07290c0d0b10021e031c0509101b030e070b0408010c020705010e 60
    0xc48459a20340b06180440011441c01e41080c8045480314030740651050040240c2d0001c0101a2156001d1701806104800f00800c01da078001d944900c2e80e8141a5a111400440205402e40350f0070402810041801119000f00701141c00f012a8420210a840014070906404001e600c0082c18541c584c03066050030000309101c4921001201070081e90041004100013001492800752410301a100351500d4202c9280c0071000021403040840ca035802c1003114001f42001301705e55056622442981c3c0c50101c0070780d9040014440e07018198040c45000e42c01e01400320390009294001d480720000140c0325040703ca07004084800a0210328498441c1c0301071403d82c69004140043d104000a81d082c44065900404500354811803d10040350480c082000d0040c0c0712a034003480c0511415011241e40c000481090303402c89084020003141d1941c1c1d00f031a28482c9110307400030280d5804460654540310355070400040e55030402d4208041c01d07512503404010a076810401040100350920300200404444000315 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 903391160 1250 903389910 903389939
    0x3f0f09071d070504031a181603081c020406120b010305040335180601050607020d0f0507090227032109010c0203070303170106030e060c030403022b110304 68
    0x4541406a1400100d0b4a402142550001c41d00030f21000032102407840e0f42116030b081101c45841080716072681902d81c0d00700198121300420724244102403681507803503c00158110a41e02c456000304102580141c05241c00508014a9141c68103d0810841034428040d104055021810586407000b0040441e5010030100d90a45003150b1034a5080302c0700c0381c40840600f0802c0c1008030010150203001030100300340048500d03406008140c481c10390301e40d8104580d42c426104044c1d4495406405140070440c1c040400e51018070038000c0b5643c2c0b9603035158a8050781c004d0506451100205ea21002c440e07804007121400904044018088940d006001c2c4594103000c210344040300c060114803030302c00c1d03409401842085500103044403001c0340d603072030014140b0001480c420300704260301d400011040e00901504000998104c003500c4641e4411614440c00d8000030000e4085205070300800f015803200c40301d95444100031010010003007141080c054450b44101c8066000d1758400c00c03003000400e0264460 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 903392410 1250 903391160 903391199
    0x50106140f0301050f031006080f070e0c0403112706040506060c1b01030e030706020c0114010305030703080402010c020d0b060a15081609030b070306050a0f030201053f0f0907 77
    0x74000011034600c0847e00d003802e081d88040c0402d20340040854504d80000b840000c80144204039440d244d1140520403d546c3d00340d4040c0c280810521046c80040e01c07050b41503141001c01707041100c24500b400c0c0440c0100b24800c40c81d00303c0c0e844007018007000f07042c9400340c590310142c2074600714540301c560401c15940b8050701a4060765582035005441c013680c860b4002c3c2603410040c0c8100d9496581c00d08041000394410000010150310f005503201681040980c02412250446e01071070505806840030f5507180340007407081781080340309c0c426070300140e132030500071ba4045015200003a51407800a05011358090607811030f0103900c15107140d00d0001540214030310791001c10050440a19000b4040548440140e034100600d01456107040111344c81c2e050303202c903045400455039000340f00d0740c8800d40207140c1c00e50b00019000410800c40810010800c1e445056007602c0483e448c44500e2044005a60182c09480c00b4002000304100f071100b250410003e040c5c100843d8130140c10340c10f02e01100c182c0c0040b549805d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 903393660 1250 903392410 903392419
    0x7090902010f1407020d02030309210d020c0a0306150515070c0f0f12080c0f061e01030b04030f0e130b04140c04030b0408301e0c09060d0c03050106140f030105 70
    0x1b031404544040c010381d5040c00c000381407c03005140008440241d48003041c990100c83c86a812003402c1c00b840000c81d1001d00901500d02c65a4170b0458540802808800c1c0e0a142400703010200001c494944540030260004040138050301d6218900c0d00700c070100c0d0664800b00d08480c90441c107124122401c0c0c501002c54182003501c3e91000c2c3c491401e820140141c0690f8202070040094505c2c0b0508049001031145c920b4030039091044282c0010100d421900703010250443d020701c1c0000300007a014006080340488107040000b00c5101c44000034002c010b8400c00e0302c1d200e60f19548102032504007409085030801d0b100c0d0448502d45800070006480b070003070b440040e0070504010302050900c052003007101c1500c508008a01c0d10701a41c2600f02841c84c90b41c0060904a088410014102e5201c00c8505182802c1d1000c0d003c170f49450b1440c8800040c0c2001d0802e030750103d820032407505050b00e00d118091342c1c5840b94801180c998503140c80688010b4601001450440c010001c2200c0c8050302e2048a0540d03a0488 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 903394910 1250 903393660 903393679
    0x1030e06161d0307060503011d07021e192406050310111e190806032d0604060b01111b06030705090d0609170a1704021207090902010f140702 62
    0x240c8582c040d1182945054141c0584880880c050303504c24011350507214280c5200646205d0709501d46071129084818000680000c01c50010340c481c420002c241c241d0f0084221500c1000b5070600038800203c02500b00c1e5404944012140190700004544403a42911201007000e80c2ca40000300751948641d1060a0085a44100350001c0c0254181030740d9401550390486c0d84926404000d1820562000d01440d035007101c5210b11a240d9071064005c00c3c45680003030b000c0c0049035a4007001e451840d07480d20011051510300301012940c0300041146620441c02001b0120740d018104002622400c4940320b0003040f504a82c2c1c3c1c2240603401d5400c0c6111242e000d4078000d549075594901101c8070f0081160f0300ba8040c2c010a00c41d004d1108503004000c5080c00380c00c2c0640003200310403800080348921300710b07000407a800c414903404001c00b03140d01070391145c00030b8054000d03207903403c00300703800e100c4590810201c4603510583c1c40c0540d43d21611884050b0603e041044102020420394861409882c8000b4420f0321580d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 903396160 1250 903394910 903394937
    0x130241a0c030f07050114100b09040c020709090606030b06010f0c11030c31150501030e0c030607080f07030207080405060313140c040e061b0a2c01030e0616 69
    0x800468201d80200b00708983c51341d900d07140c03a60180c00414210302d18004000c1c0814130482c1505181300484182605091034440c2c114140405850000d0001003540a0303c100020328074600d005410305a807203810b0000b52103046107410044c510002c0c14490402030100b4603110299040004044c400d80c1055001e8201c840c2000041c0ca00416982d07ca6001081c504140f940e150018038102e000c40c500150150184240f070700c0d124101d80002500741003811110004000550182d80503074840103e0304140c603004c210510210b850240152070100c002400c41082080d15103440014a0304201c1a15007507141200780d8440c40c0c418000c0b4000c213071184100001080e00120185051000301d9401160f8400222100c00b000e9203c68030140a64015810200d070201d010302c0109400f80304041814882080045850603059150010071514050041c04080c82e4601d0102440d007040720800301c118190904405c4d4001003d580c0844000c00d41c6500000038486908003180303400728004680e20388100d8013101c2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 903397410 1250 903396160 903396163
    0x905070918032007060f031d19020415030803070807050708091224090705060705060406050601050f0c0d110a020f190f0e0601030e07080604020130241a0c 68
    0x4140c800749992084e041c1c00100710f81c0200080d0f505124a4a00f0002900301d1000ba805000d00c44c010140d0b55040001c46080e0b045118003140322440c0081e0002500740074200c03030400300000c0e540058414582c00320806c0f0455500421540e0f0080040c90103904002103030b075503502d5070700518100c0c078450340795103000e4103010100300074006000e9800142111a5824824049042541580d0079034050080382c0c80400d1b507080100494154551000007001c0a540300e031a680300a103809000d10707042040402c80c5000861b04400076020000f00ca0000d04940010000042d09034441040c17001005d03042460503030b0140e615540202c120800a469240d0f0080b0305003083c152880d001c3d00310030502d150210020650b201c0c01e440701881060207880c1003200c2548002d200d5030f19589031007929600d0380706d0300000c3c0040d44141041e21900c2c4081071202c0b090801100540040070130071100c030741c503541d07a0714514407420582c41c640c1400690300c92002241900b00540c030990300010840b502e08000001400d09004e010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 903398660 1250 903397410 903397457
    0x2101090e071d15151c110a0503011a091e0a09050411040504030e040f14010f0317131a1e0c2a09070f0f020601050604150c15090507091803 61
    0x892107046075540c142400a80000304171800c2c201d0803d442c00001100303204081040324281d4046458003400c2d80e207400000401e850741c468400401150500403265540c850352081103004078202c0c186030f00c00a0000034407405020a030b0002805504100a00c004a03d0400700f40c5104481640e001c29189d843d410b0550320031948030f5595412a1a00540100002482e4407558a1686150f40405180d98854003008401550300000d801c8080c00950189102e2088008006244444800808056036204032030880002c490415000140004003814804002e600d20702a441190b100b050a0108403618651f450804021411000f241000b00c1c840a1404281c114600e250080a4000d1071500e00001001d4440c440c0c01940440c45283c1c10820750390000c500c00341079450180909080501c0c10101c0c05064102c9026035007409081c90039000490f41101c000740030407200c1c7c0303000b1a0b40d843d075140c000c1c41e010041c3c0c043c8aa251502e11610122070a449101225641500e0000c0b1840c9000c400c82c5888903 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 903399910 1250 903398660 903398689
    0xf1005091f0b120c0703270b0d2f090f150307020c0907030c020a0201050703030e0115141903020402070c080a0b0a05011d06062101090e071d15 63
    0x14080703400001c0b107140c03403030080111070100750b4290785039100e0850b694042d0140020090100301c20985012681021100300403407070450400c03c02c880c41c1d6681e5051a9540000c1e84034402c03540310a00030450b07456070700c8441b4580700c0341c54103605501c0001000985a002e0700e402c0d03a11a000005100c4000c1d03843c01c01c00381c40c11080008040e0ba9043c03455000c3e540308410258107000d03565000000e10003130f00038411034080c40e80e41e8020741804640c6900443d002d0707011200031024140d40300c83e9040001000d101e81d0091041d030b401490241403c2240e401d29a0641d6110b0380e03c20306840f00641a1296038905d0003003201e50581e005a11202545003c100071a45608280f2003071140131001410b111208404070700403c030b550010021a44c0301d41d0100c1c010760201d03024802920004010035a9800c10308c005140301102651381103846030520502d44481c40003a840901c00c240c841007a100c0c0200180301c2440203004140f80300005484000061209080040c843c842864906401c210291030f210380380200e42 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 903401160 1250 903399910 903399961
    0x60e0f03030c010204030303061d0c160b0906060102060a2c1c12050f0606090f031009030804050d0503011a090102120a0c110f011d04060302120f060f100509 69
    0xb181c05485082c000d4129220690009082c1140003480c0340001c0c5543c06c560140a2506940341d07034002004080342c0c082a49060040404807640020850800d1140c1c0564503000182885042540c00280740c910060310081d20989080d4a2007807984590889038140005e0840851410102400ca02e0030010300d000c022002000129039071001690182000900c40c210781c1c1d0820054030381c105116412a41240c0ba01e401810402c6420b10302e29001c52150200003008003104c3d0070400303058200b001d550620a0071408110700d40c051004000c010f0045145e05110f600d801803c6624001c1da0001d00303400c01c407071100040d800003134003105640700b440300b40364101032100d40c240c0d40d28808200416807500110181c81c81d0060500680040c07800b041540d2002405a4840d40e072005000300c0110b11800c503c641983c4076540380000001601c40c0b8031740c2c0c0180308444d00608004100300000c04c2c146540140b030250119200401c00c00c03d20711401102041d5001a00c0c0307030b425640c980c0c10010814002900dd44102c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 903402410 1250 903401160 903401167
    0xd0c09290f210307120816050301050904150f020a02011103060a0b030702070905151c120311130905040c14060d020a030b0307080102040609090605061204380f060307060e0f0303 78
    0x41c07205c09804038845540d561340314540d65440c0c4d05003400300740d0000185400903908100410161400e4800a5040340c003072140400800c4040b030040f011100f01031000c03504a6004541144015028411814000c22100d00301d440c5190060005181c2c00302801500451140440412407140c07081107204003800d5402070070001420038100c1a0700343c0d410118401e1003544019003801070011160081e80000358040002045019000800e070094815440900b40001c024040d041e0031a0355103050300000d240e6003800091500701030a001145030724607042072958040c030748004941034032440120750407440c07425001070b02c9452500046028101c60ba4a0a0340362040b0341c004582d022040d4010b02c1103075030755125003000903940d50108055610b6881020343c814000e1103c0500daa100c1803440c0d5100c1d106050809000e0002c0100070136440c1124041902541802d035009410198100c1d800e80115500500003040d1502000180e580c141d507000350f408001852030700038090f80b1641201c22030750800506032601d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 903403660 1250 903402410 903402413
    0xe06030f010303050c1245010f270614030405030a081e090d0f0201060e0612121b2404110a080307060510050d080a05090d0c09290f210307 61
    0x31a11482d0074142110007211807801c1f103581a055000f9101040f000b040c6401103070300041d160820a0440e810a00082c1c1804002185000b00f0280c444074a000a0b10051400d0542c010b15100320402004c07040340c801c006100c00f082000054034014440c40c40d01110641d03070a0031a01000b28003c01c0401d510b203483c010301214090108590f4030f00b0203655980d9906080c0b401c0304909860721489011252506607000c10b00c1418954131550802801d0401c8800e0080c03158001d06455218022480920031902d0b40300307103044014841d038840b140000c00b480588840e41c100000110002038002425030812007600c0d070751610741d07030864001001000c007076a0311000c090a20001402040300c19030b4806d01419808299171a080048020058000c0d074018141506d60034140c0d80b607030000c0001c590204105032610001840481c048000c0c00191001007101000d001d20340a0f41d051840e07408461082540400c50540c40780e0024010743c0380300310703500024015541000210b0782c1d9000800034550100060080 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 903404910 1250 903403660 903403687
    0x15030f0b060f19060806031e0706030b04230915090d1b05030403020d08040e1005040c02011a0f010509060726071709031015060e06030f010303050c12 66
    0x3407003640107032801900703290b80d502003003c0b60100d4075101c0704450700350b002402030038403484041da403080c2c01070308440d4000e5413102014400120301c1d00e014210783c4808420300c00d4070742c5130041c40001c003070654080c8400c14201c04086044080c0f01509102e490001c40001c00e4038104005410084200e03188220b80c07070500705030300c0391a415400b0711100414042403a1018007a00710809440280c1c01c10f02450500d030440e401c1107010401242d064802e800107100c0810011030b0181442d00070200383c00651000c510300f81c144815611240d241509592415860020f5004110940008036000300d4021001079804001a0f94178010110901d40207000072441604002403140c00c002e43c0c005014621018643c1014000601c0c40743c40c0c0010001d43c80e005181120160352000340c9804480103090f00e04a054600312102102c006016080014080d03c0003008200d0300104c01412507881a20a1440c501c5d01e0140400085410311008040200000e441c0702c08a0043c080040003c25564805513200300c03441030034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 903406160 1250 903404910 903404933
    0x30a0f0f0c02070f0e0c0301030b040320031e0a090519080a06021e0304080f03040c12051b01020307030c080702030304030f050a02040b090f040f020111030c07090606020d080a15030f 80
    0x905104c010f0140c0492110f0085078003d00c00e881648401d46560b0840d41c40c9860302902404c02ca05000100403130414951210301c0004015007084011034031150100004404c9009400d000c24545500f040030b0030045500c908940252081601c001990086001240ba65100305a0000700d550203510314038030030000700790020408103038015503512000c2484801c4450074071058400400c8510100098404840341001440c1d00c54050050f110032950f4510402035034000340c82088495400402400c01d00000c0d50368180340c000710030300c01542420715541e03014000c02040040030340b803a50042662411942c0800843c2d0144d2b1344804040c0c0d00d441e10b8505035030b0311480304404030321841c1804e600c1c2c401d500701499140c4c8141e8061800450076190740c0c4881c3c0c200203001c2c1081e030400507500018215503904000030144811502c000b0300700149401701d0101242d810f0b03084407007103421080ca5104813980c400c02083e0080b40070200042c00b010b224a002002c01c0c0e00b0352008128007a00840c000c2031010704102c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 903407410 1250 903406160 903406169
    0x13020a0210140f0f0901150e062b06240611100c08010308030405070515070209100302010801060f0921050c0a0810020906090d0c05180408030a0f0f0c0207 68
    0x240900d2814031810001000c00b1034007080e49201d02d80003e00600c0e0b0586555400401803000042d005a03881c7c280140c1c2115134029400f139a8400c0f0600035981054460b00d03100d0202000c0d151100c00f84001d400315100c009074400740c405a1103601e00a241e008144400702d00c1e4410340c4c00d6400ca1942d0781000b1b0708003c1501e05940d1640100c1d0f03004900d030301160040c41020720481c4c0e40c06009031b0843d5908059500064420744141c8030791140481c076a142e80000407400c4180307071862a2100841e10401140d024001e182d11617185a0300e00810050360003881460640d2418101003107904400c1e003048892140ca60302c0034044070403910010140f40c2051404940e054052801d540520352020103101c48400785200b82c06656100045520317200c0710550103480f008800508040c80e080310240055080c2200304001d80305003035401410051440e003940f02ca0700300e9543c02c000190a00d06600d60a44501006210b04402c503115030b69214a0f5580d68001400d00794a144100003400490700c00030350302e0015004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 903408660 1250 903407410 903407443
    0x7050f1905100c0f0f120c030b030705060f180118180b061608090301060b0301031a09160302040b061207031506181a12010e1f120b0613020a02 63
    0x14007a407001a9405407007001c40041c4c442800c11240c8400403a035032642c0194030720401103401003440320080d05000e810301c0c0103882d030703004120001110101030a08184d41e00ca075101e4131041020a02075000f100950382e00091038815003651a10110050300c41c48141c50030305000c860b02c088003048002d03040e4410240d800f4400010483d0f41581001d10406104000001011451621214000410f208010b000e5000003400110b02141e031800680c80e290002c3c1c0040780c08182007084c41880e031140e00c000a42c0300c182d05000705503510300b051440d10564100d0001038011a10f4840768540da4850104075040c0d01b680c502420540c0c40c14a1006004114640c14200d031078201d0400000d4061245000d0641d50801c400801000c80c581401421700c008000245c4040344002d00c049a00250b800124a0080000a01010071441c0c1034012441034070000b1a40d021072005039400b0301c9014980e480c20a1007a41c03021030004d06460f420005502c00b2070800c10381c440f1900001d40c900151340c1c08600240113540c00b98 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 903409910 1250 903408660 903408673
    0x209090a1a0f0f0405040c17100f020403020d0f050703021206040212070b0f03060f0409050f0706090f05010c0f060203070f090503060c030c0f0418140603070b04090207050f1905 78
    0xc00c2040348502d01d010164050f1050001209500d80b9030f00c1990803610403000300401e40e564080304a01c41c440c0000c002d1060300484250a61304e0300c580208600012183c4046203400e0550b800a104407158600181526412440040030030804002d03035806142c0062000701c0c4038041451041d030314001214201e025498a9902c403072410000a03c142c15213072603421141c03c0501c03000c64010203410081c480d590000c0507811550882e113803071140c10485801503020382440907595008915080e050303448a800c100740818100301d0b519200c1001000c0d11001d04e4200c1d44581c481c140900c0308042c400028200130701c0081403202d826045a034440c0080b00c2a2110724041c2e68500400d074540d0340440302d0708810442000056801100c042c0108550306502c04410b0900d0713101d10841890840c00c00c8400b51541e540d062000303c032061070381516480f09089000300f0110303081c505d03d865035005030302c102101550003003804000c0100038485540c0d034008110488001411448041000300b8411005840364007444 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 903411160 1250 903409910 903409961
    0x3040803060f03060601120b01021e0708060c03010f0e041b0b0301091805060109090f14010b040e010c0c0303020f0d0e07090e030a1d060f120105010921150209090a 72
    0xc90041e114079416150504156072008101c0e000e400c2300c4140f0303811801120b4910702c1058180102c006042c0119004013909810034400918010011702906508141403004200c0c1c0d00c034000c01002030f030b100801da407001c545403481c010300714080d1500074000c40010828041041e10a0002941c101c40c4140414440c07100d4014520311a42d4483c00301030040d030000d00051000080940198030610311410b24207074145203036100ca16841f40c021400d1595079450711210b0810f490035028900e40d90f840e28000b048000d032100806820015802001010301d238020407011030301440c0006a414200c4c0010b014030100101805094484030035000b40b2444901d0019400c0b800800003090343c44100d01a1903046152a20078070080741001da168680754081410006603a940509402a060130b40710307803a0006084d41040009040f82d0111341000b40300f501610405231905202c038401a4400d41c10100d40301000020074041d10103072285080d00c0d5001840c038800d0028241055101c82030b160092080c842004005 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 903412410 1250 903411160 903411163
    0xe010b0f061213020f060c030408060105060a02030d05090f0f0a021005120a020903011e0e07081c0507141603061406010c02010f030605040c0c02090a060b0403081b010203040803060f03 81
    0x715403015030480c1e00500016100c0482ea0f40b00768400d40000c140b140c0514030301c00010340b20791207a064402645c0010408000050040090502401d02241c2541c1880305965000307542e801003c0d514081c058131580841c081c51400d001000015941c0c0c02a50481490034900613a285004403049004d1704520101c1c0c0200b0303105106071062601c450000034050344550015030003a4100a020b103506568808000001c4020809e00020b608a0301d41c2c0803401203c0c280071241071a0040c1d0008410390803c55001211039501c124019030000c10b07003400c3c1d46480d411300b841c0d00940310b00300600d005445081d104041d03e440140860b01224410801400000380c0710b107400c0c50001c0d060710030f540821400303111200158003810a1003070320601841d0004030b0a076a6000501610103c481001c081414680741c6415030401d44861540b1205524041c440302c0d10f0301051075030502c264440900300030404541175400c010700640740d0604010103c000c0d9224105401c00350100da00c00d45800d84681c01300c0b02040b141c1e040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 903413660 1250 903412410 903412417
    0x50a08010503070303051e0d180506130209010524030a0b1201020703050a0c0303140c1e040f0302060703140a0905040624081503010203130b010e0c07031805040e010b0f06 75
    0x9059503040d01f0190150f42c41078039100d154a401d5400300003401808140701d403505c1803507028000695921603176425414654100200545040940328103001c8800140c0c5038004918112107041d41c001da002c1c450014081c0981c6501010403002e10b03000018040c4515250b00260381e40801280ca00610040e2601000e0807880307100e000801068041c410007203410b000310643c40f6010b0103800d0100e071080f441c4000651070981221101c0b01d1007404681c000a03202414220840c01000484507494103042045000319040c0511000388980c000064110800d40720311182000546150300f2903845405d00c220203804240d66001d600c1c00b80e03240540004220702103403020500d030050001c031a9808030342c10404a555500007011000b11002c0074201c00e0454a0900c01180710b045c2c210300c0010820040d142c550074400c0182e20081c0030810403024409404000002c0362249949810681480030850030b080c04040340e2640015840751800c0f00500c840300c0c06400141c2c03a071108640e0308061866910400c0352501 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 903414910 1250 903413660 903413663
    0x507020703030c0312110a030e07060c15050705160b06031c0518030708100b0a05180106080402010e180601200a170409150305101406040f09050706050a080105030703 73
    0x18491581140800e020300003c0304070752171155011030008a510030061040e8081c00e0b8810020365035050035500048184138260141c143e6140c60f0082c01c0b0a078440a045520014020b1001540c65010601e428000d0084500241c402081c41465070a60305052954140440f0000d0003401070044600d500c403041400111290341c95150582071003a10700005a0070b1201541440e05482048030200e1030750001c200030303d01f03029030120200d0019030010034031100288550100b8000c0000c600f075407454480c0d40499905588243c074008071a0344e10740c001250280040c2d014541c1050041001910322209194031511031a03081e00e600b54800e40500c1c0241d6115000b03440702096811007907c0c1400669002c116404000c20420702906040e00c6407400002c541511100c03d0b000960980e04200700074081c0700c607102c00c03109c0b51810083c0c0c00c80c400803014400e000603d028402d035500d01c801240552a035118031101500101111171407500c4040182551388007000902c00b003802c0c680006035502c1c0014490082d09d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 903416160 1250 903414910 903414917
    0x30915160e150c010b0112180f0c05060d0501330f09150201090c0603051605090d0b04110307140d06020f250308060d020d0803070309021e0301050702070303 69
    0x1150101012100e1000a054440e488000c0102c00402c1c880150050800000034800015645142400140007031152601c2075440703508040c00c901c0c80c07508003158400350705e030000340061400c00d0301c1c0350255000031141c100990110010075544410085a8030103416140aa9280c0b000c1741c0f0512400b50080c8880500d180c10800320a2544c10000e1086107024001c90250074810b1810b13442d801e41b04841c008024108006030b5448100000b4480e19800307c5004010a040c208501d0420051504c0344009030603415051020004140b003580d00d8072004442d06940120031180c6d6070030585001101103031000900340c86031050201c08155492034010b0382c3c800c0440140740b001c0f81c0c04282d40f140042d410068041158036414068400e0094618880c46000d008a64440b07400d5545481c010340f285c50068185400342c480a0f01b510b00580380d84910883d45900680c80f83c3e00c82c1e40d9100c045015040000c1c000750040e5564001c40101c24400220b51750300da07800c400a120f00e9480c41d40881c0c7e181c4580c030014000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 903417266 1106 903416160 903416191
    0x1101090608040803010e04140a0302061009020c07120609120e040f060b181f20010b010c06051f0b07170f0a080a0b0a0b030915 56
    0x15040a0038010114201519500064081400303a06c000803c07041c041003d02031b0a54507101da0084c0d500c200c409030030f40c61030029141d4401340c41c2e006104a4100c0003090340301543c020340300c00703081c84002030a15500c0c0c03417007a105030010a032080d96907507907600010000c0b802060150b41e140c1074607101d60729560504810702017101c5151009410703451030010148034203140170046841585041c0342e4500310080f9000018190b440c0703400100f0004088048107805180c04c260301049071042d64404510480b5545030150980c4d400704115800076141560710300c0021078560005800104201c4078403504981001040100740c070940020300103804c0810007104100b0044a8604e41c80d030680c1040c1d081a42204940705640074054504040c03000c01d03000501a074025500038519002c00803c01d010b101c0c0d6035003d01113994029583c48425000711400c0c40840c81150340281c1c001c101c100303a00e800d0f = true := by decide +kernel

theorem cover : BRFrame.Cov 903237410 903417266 := by
  have h0 := BRFrame.cov_init 903237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 903237410 ≤ n) (h2 : n < 903417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
