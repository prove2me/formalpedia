-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2662
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:22:33.429842+00:00
-- url     : https://prove2.me/submissions/fecd9f1a-0801-47ee-a9fe-c3ec6b4a751e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 478597122 ≤ n < 478776978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 478598372 1250 478597122 478597151
    0x80f030d0c030204051014090402030f1603020c0d0e13020c28030503010510210f14060f09040812161101110a0509030c030f011506021504021e040501060e010201 71
    0x1355120300b50300800c074503400324a00d62084510390840e00d1f800c00c00034504014000000c0c281e030400d540815032002054188408115046031628010310242429403c001941c501252500110786507d01030141008135165030303544490402140c11074000c800c54031000042d81d140e41c0c5214080200d20100465220352038410b144520131044103a043c1d80f0545941c0c244020312611120140441d800c0c01070704452003900d07c0355901c075523801c040c4c194000940e0440c0d0840301400d562605403011141c107110300038007200751951115140583e0050700c003208640c50b14a49505240f00d10002600342c1e54001043c000c00c00d48406894640c1300d400d80e2050a00000700c076502c0d01b25541020380f0f0034440c00800041103100d0003103000d0800f488005055400000002d070100c0d081000c440c0d0680030340e964441c01d6142c10110008200003524241c0300400b10400c1c0d0381040500180b0161001e03205001800900198010305040b545540714040d10601295960710f00242004800310407a90142d400d01c03400692910 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 478599622 1250 478598372 478598377
    0x7020601050a172b02210a030504020127030b0c0309100b04180b0106030501120b04080f0903160302010801150804020d060b1804050705040212060415080f030d0c0302 73
    0x5100402c0240501d1401d000c0d0700d10a070b01c0701003841e801d0240307004070800030b10b903010405188212098940c28040c0b84000013410f203000060703180094868a018074048144450546002c612503080004c1e00d1340b11030005940d5074901c050100311085042d80c101000f0400c1c01c090804a902c100074840a50303c1d41c001116550108980714540c83c0c7c401c0062031003241050b040314840030405080003510600d88004040160700b1000c09498074080030004100980d8141b050a0060500c9003450032400c020b0350350400510b4028002a081040124401c03001682d440d00301c41100c0001000c0754400d5001407070035140041d480c40141d011400420000480c040030152008080c0c0729a551403440340d60716420010618100e001c01d44515079211400080c2d07880c3e940986ca01d0b6429500342d80064603103458224603007001a0411070241d80103021461481039214070464022908036000f10301c090203480c5440c000d0780302d541700380903500c107081401c050010301000403c07000a00d80400e00036102c400c00c05030300340d1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 478600872 1250 478599622 478599629
    0xf0606061b020f0609030f01060510050702090723070b0403030507110a02060d110c07090e030f1b0a0b0703230c0a0807090b2818090c05070807050c010807020601 71
    0x120360031458000180380001e0f6004250301c0c000e10050401d2607003070119141c0601d50000d80740d203039500c103400d009078900704050144071000c0e4a0064502195540800d83e1903401034041d0003404070b400348501e4842081d2074860035950075880342070f481d03d0980c00c0110040400340c40c1a008280362902007071a1601c6007121003844207040004102c803200c40c0e0b0034441c56900140d120000341c0c2e541c040141c03049103504000e0503c040e500d4001c001c000d080099170400c81e150085c0d40310099004202c400521106071082e6807042c8245000c00343c6248a040c1d0742030402c1c0d0179550003000b82c040001005040e0b60960300211441c1c5070310a00205040418103460072003042074403807265036041130081d405520701c1218070a07808001894401c20240d40d0740e001b6011500301e4484440c01c1480c000d21120035000c1c20080504034421490701c0700d6070401d40c15540c0c856404c68020011100d889510740c0e064280500c04071010382c0d5000d000b0a5548082c1d090280e02c510054a54500041c00e102c0490311b4a440051414180d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 478602122 1250 478600872 478600907
    0x706060302180928050703230303221e050106210206091005071a16020606091b09060409020301081e030a050a03140a0c110d27030209040f060606 64
    0x9190200e61800301040411314201034007076500348003c0010014443c480086116260f0000d0385401e105d41038455401001112a05038818010032800130070f040e03070860126003144c11101c081c0c511400c09000c80c00700304810460a1a10302c000000b0080c0550000341220f001c15641c0c51050000308205071100300d141c0c0040d512084c00c0c080d40e10545070030200281083c002d4109140b0303080f0780740e49003d00344a8170f4015902e481119010081c400000700840c514a040e2440035242a00d8880f0006801c0c100c0917109081c4100320303194110001c0c104800700c52500000030405a220740c0e80e0159400030350300034064107006004110006080d15014441c0048400a080c00355040c422105002c80300c1d5040820a03804043c0c03681410a0b41c031808000190007060041ca01042d501307007440c00608640d000082c4888140c3c400c00070b060180b0340c8440e0750b104220a440da0140b207075000b07011150302180d00d5000603601806820602080210114002c0700c800d110302401c0c032403103a440303c09849040c94008194007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 478603372 1250 478602122 478602133
    0x2a08060105180a05070c02120c010201050c12180102041706090c0102010e070b1e120f010e01080307060905010228020105060d03140a030914150c031e0a0b030307060603021809 77
    0x42181360059544a2068640001c038009241c0010f0360300c096401003841c1d10b8218030b14482080d41e080c014180d0005c81544440d1401e085069070a900081c001d08a007034081c1c01c25401c565441007074040320300500b406140503060349103812050303407200015541c40346944503440300461194010301809040d003002c0070151881074505000703404941d0003080c1c244008540e02d03031800c40010403140540300590940107500460f00e458080d0a238409010780100128030207040041001f00e90010498014540c0107030045860344c280d140160184c05000d10490200e03c402018400c003042c4001014030161260780240001d48440c42801072489650b0000780001d14148a0081b100c08000d0003040860340c00d280001d910380c001d4941c103907080b00d5200606595001440d1650a213074030303101201c1c2c11481001002c0d24504145000c0c1592640788068120f1086010000419040841c1d2040740c4031500681504e5860a0500e0709500900c0395003c200d00c82c0441c6a80c10340187c0c0481d1050b481400010024070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 478604622 1250 478603372 478603381
    0x3130501151d091f0b0402040605071a0606090607020105090a08030a0f0806060301170a120815041103040212120408030a0801270b03240901051f0e042a0806010518 72
    0x113840194910100c200c0580b25014032041d500d561000700014aa10b60310291035802d5481c04400e080144004815040b55960503c155981c4800c12503855500072280240c1e00e4170076100586031400340034461507110103228000a8034200100c000c1001c003003d950343d0801a1600203042d1004207081e80c10a40002c824001842415001184607680c0820281194004215941e03070954501502e002c0800180d1000c00b4000305041121840c10000001c6a06000f19a90217020030040d000c0240003034412180104900c00c01070003072010183d012841c4d20030303580e16902e8078039a0f582c03a03111084441c0050f007488000640f096089540c40040705581c030490306942d408942d03050140517a01c501c56407602550b00d200341c100d450140191b56025403480040b41030703d040203801e400c40e01c005100c01400c1104524407468103442e9140d24041d40e142003881d00c110f072100d04000f8000400761004c400d010500407406d002e500007580e486000c50b201d520440300182e0300c41c0148013500800d1182800960410b2000c43d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 478605872 1250 478604622 478604653
    0x914090d0e0108061f02011d0706080f1003140303190e060a0908041e030506060d02090a022505011401080d0f050d090804060c11040b1503130501151d09 67
    0x1107802c24802050b1500161000403a45d25041c4540c41010142c1e545001c40a6500d0588000141c0240791030081c102480c5030442c00360030b00500400b6011071401c4023001403075400c0042c843d407001c2c1d42c10a10f4000c962000c041855925802940c084030f48071303e0103140b0b49854501d030294035a848810f0015202d1501c4000d06803000e0030140400300d40500d4180400b18559000440c029000701d034000c0000000c9296040c2541881c1c405002c61b802080d04685100168a80d18803194000c240c40100586d560350b5040100e04110102c031030700b030140903038403c241c007030010540115400c0090a0009841c0e82d0365140c80540d640345031000c4402250122071301c1d0207910f01660251441009100010038040e041e0754665601d41c0c0300760004030108081460450920001842c0040d241d1420744040122801e4140041e403014201480c0c41450540080014224039150000020250f07002d40284034450350111800507401d403038050221540c1050064a84107040604241e003e00310303103005071041000b1003010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 478607122 1250 478605872 478605887
    0xb030a030c020d151a0a09021602010c140a030903021206071e09030503131a0c070504050a023702010b0a030303050601180b03010611031801030b0d0c0914090d0e01 72
    0x2502d01100c1600b1000c1906078a0007481145c2d4020441c05520741e10f400704002d4a8043d40d00202d6605106122003030810a100840b020410b8090030590740c0c001013460907048400b01d650080f000e07401038130720001c01c05400c891494262842200e1000e0307881500b8000941c3c0300400c41300078000400700200c0c020f01200c0484800d404178024640100344603202c1e00c501b0302d1a8400441e40288251001003088040c40e400641c448025401556902e401c000700d901c65074034440d90050318842d130b03034420204151034840e81c12134002c80503140e00d1000c1e846117110000300f148140c101c00b808120b03101100040d01841032142000c1110000c1c420000035085880c11801004020704a45c14003414007151803541d1103641c01c0c6e0000300b101c04001c0c3c1c0c0e00c0d810b01d04001d00c80f9118001c00c20183d8004e0040035000f0b00a00c5015004001c00e00c1e001542c07940d0031000ad19807228054000e13001c088101c1c0e01083c1403c4581014200e0041d140c03e541d019159070902582c1c41004c40e04180000d1002c40c8264060f6108960 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 478608372 1250 478607122 478607149
    0x14070918020f13230612070b0f0307120504150b0d02061206121b0a0b0406170a110a0e03060105090906041502070c120215031b1b1204090b030a030c02 66
    0x41c0060b00d100c004400071081c1c2c20030030403410911841c1c030800103d032510a0390710701b00700408006040017034a0400c045580d4041c1000c080c00c1d9000c00300009040c107100d03144c225065020b07441d0500460420741032040e0b1348883c017040c12100d18103051301c1040718180b4181030801564040d019a15280c108264218000800380640c0c0d40280c2a1242303001c0e18401300301d6181c0141810550550491098041210280c103942c0141100001403100b0801d2540003020294440300d018114689030f0380d138000d108010441d03070341740c0100c503100803440060b402e41c0202e0f000e0701c00c00300b03604031013244c2d0301c840800000c64022500041c096002000050002d0810560040c0c0641d240b00b000d414481555119000d54500d82c01641104011402c00400e5142105041d0801d8a58003e100c2c50340c10f080c50401d0580c00000c6402048200000360b4404666000d41802c071407000312819950b2420400c00207030007552007407203001182810410004d105103004102180c24990640fa145900d6803a0342c240984141d0f15407 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 478609622 1250 478608372 478608409
    0x5070609050a0c0f0905060d020d0201020106051c06050907120201050c19060e0c040e06060d0f0615150f0507021c0507030c26070b03040503040314070918020f 70
    0x544000941c0800c02000003d20500000c00002c2c140800b00400301c40c43e0388034038403090a100c203002994031b0344002c00c0d40f20354040d40c840b400e1003502c3c00140d01500c3c9079031090360050030441c5880d0313401414031180c145292280d28181b00503292006140c0c1e9428050281720001c1d101d18809100540c0200300824031049038070305441c1400c809100d035282c4031501d0715098800c0350301c0c0d017198140c2481c1444860240c0c0d00c102d408000c801140404280d40d1040244918058040780e05407038280480910920b042d9030380321b041801202c1c81901c1500c40c45050303114141410724100860540c142c0120f1a03003c0242c8583c1d2814185a41c03902081000301030701000420402c60b0401030f5021440a00075800514021111840594a00941c0da5a150902c40700280703c00d1804948100208022850500b03c41d200710006072240c43e1800c0a50070b40c807072503000900482c0041c480c0504203c0104004040f1021408100203c0101140f8007070407030100e6030000d40c42124961100082c0c506003442c40000d10b19117 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 478610872 1250 478609622 478609631
    0xf071b120f120c0302131d0619030803040c03060b01020f031e0d1d06010501031401030f11030a2004052811040308041a040308180f0901260d0f050706 66
    0x2c1194008460240e90810002500020440340c04075103480080000c10314070010810000984ca182101654050100c40c4580d86684041150080b140501d00246030004a0a903490500e4504607541d028944070884800f407c22100740d01a60000c2803020b506088580030714074040801c00d401e0000420b50030415030201d014400c0c40407509003840f800c01240c0c0c603000c0c00300c40900c1424002e8039000059009078101414041c00d00014100d0900340e60440c1d138000c4c1c942121054a2811240e6428140412609445800704800c02d019540a03100cbd0310440301c1c118406200421401d11060710000c43d00500905880c090340b1924500104000e80c00001c4d0140002e0034640b005441081d961140c0e0007514071640215042c8941ca07000340901140c1d0915844030f9181518503a105c1142e07010304030f0300c01381d0428401c06000094662015000f64008002c20200a0750384560f08104007480c151540750300300140c91940160190005a03090004074582ca0f002c03032500c0a43c034111081e0340000000c90700d85885 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 478612122 1250 478610872 478610897
    0x2100506010201110a080f0a0b03030d150b071a070203180906030a0203010f0b012c09100803120403030f0902010212071b060905030f0303160e030c090f071b120f 71
    0x1107402170a00f015550303840f101c480c2809004100c1140d006001c000c08507181400c40c1c3e0403964000111a4031604403040401c4071142c1c210145148030480e88041107685c400030b031040401a007959a9684820580d0004400d51074032038040ba42c3e80203188401c82803840d00a001201484d000080ca54085070040484800e8046603021034207560013103041d40711458a449060602c0d60700016000c461912004800b00000a04d014480300d1351040c2030420300034070502c030100b8099085201300002a0040b8000c407940c0342180000380e104054100c0b02a0300103490290300c040741102e9402014100b40c0c059005143c880e106000d0500c003644074003000c0700d11206000081c0c006d0344c41890202c000b0956511907018452410080c18249a80000e00a0a5801c20410849065490f185607480c03000d05103803071f01d40030703801c040403d2508085031400c0341c2c820030341e8042181c00c000418415110306559615001e4506080142100e41e80c10540010540d0031506081e00340caa12409108000301207502c5c3c0141d00001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 478613372 1250 478612122 478612151
    0x41103100501291b060601030c210c0c06060303020c0103060b18090a0207150902030d05040b0a0302090a0503061014030d0801031b0321080705122701060b180f0102100506010201 78
    0x101c200410b10b5a01710004200440da007511604c5111000350420142c044187c1c000545102810f2091b0340202d80d84a0000740c24a215802d00c007180380d4402010040c00f5101c1c2000780d540c882812489001a00303041011900024080654840c3c1501040389140d0808440c200720000381300602d902c1050717600f03001c4203000ca034590582c0c0242412100d800203c2d10600d005043c10820b4410300d02e418004100701c200406003944080b50440c00703c6107001a10b07070f20000c0018142c0c110030b5004690602c40da5041c48590090030a00d04102c0d03031040d4455075091816028507445060950302c25022840740801000841c4520141180340e520740e030400c408c09a20b0f0358441000e10002410b03840c900b00c01500400f0403039000f08910703400c481541840f41c01d1a102d0b0341d101c4c00c0107100038803444800408921992400d0100e8a07210201924000280030b0581c4034402c10b842a00507175030307449411503043c800d451103041007950045e01140c1030f40541588100c10000c0c102500c0f01900e142d0440d0740e00c0191011450 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 478614622 1250 478613372 478613407
    0x40213061202090c0c0303010603090c050907020d180b1617120106172412010c020a03021b060301120807020901090f0b030105060306070c11060304110310050129 71
    0x900c1c01418480d1051a0042c82401d18009101900703491080103900c0444100005580c1110090718002c1a84038141c58841004d00855009a802050325014481242d4000c603042400300a00e03a6401c10740700f1a606490308001040c4100e0002550800c580c0c2021440420394100207401100e01002d11081e410b0000c030f443d8010107400e591420030300c005024056004100c201c2150540c49400c40d103042010307002d001c4802c10204a1464008058016400e071070300c2e201c440c9494005c40007080841c1001c00084d4840c0503202c0120014051000e40c6001080c8080c034010703c0241c041c10084c2103a0070011281c0d07000c0d0300c1030740c19500342e83d06001100c0140d4501105c0b074081c040074503000c500d500d550448842610305c3c0304540742c4030364100341c20480030b524009103640d4442c40a00d00162201e0302402c010f088080415607281c1c010b030b0700208000030f01c583c0c1001e0303000005042d41160760301310b1503801c01c8007250300a000d4290308422624058503110442c0a810b21499581c082251800034240d01c141044d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 478615872 1250 478614622 478614629
    0x2150a02031b0304030210080c030c0c010e1501080706090305060601050307020f0d0302040e0112031e171509090d081f0b03070306050406050f130906140405030c0706111504021306 79
    0x60f0f000060038011400c0840c980750045956080010a50400a490300600e010050a02c5005000850060a0090b007500030b220175600180603140b003c900e410440c46481024010000544078500c4005070480c403441e030074403c403500a4084c24064880301d00448a80c3e00152406045220700f00b150a9010000e110800010015407801aa07aa00d08216076031806416071100702c000f4540c90300a1b02080e0801d41084c280c1001d5000007240040b0305030305554180c440404e441b20380c1d680c0000c00036512072045101c0c15120b001c0300c051031140e45401d9025070394025440384c03200264038140400d076450100c0c02c030300319010140d0070780c848801e40310341c10212a50011030b01c41000030380b9514104034504140c40b8420261034207031044041d00455401003244101808500c5211598401c469000d0101a90200c201c2c8581c400d2440d9032800c09007090b5907603030041c68486195024000700024918006d030100c0c00340019050140604811440040080340e000030800d982013010125030b00140d854074400d00015 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 478617122 1250 478615872 478615927
    0x40e070906021603050a02010e01120608010f0b060a020d1101020d05090d18050d080711102d0c0f0c0806240301050609180127060c0c02150a0203 64
    0x301460030000a19100c0c0308403030f0352000c11005005101041001c03c1c0c1c06031040d0203080c400900c404180040f51005802500c8120076480d0070808280e1000c1900b04513a5106208024810070881004004240c483c80c034148000d4fc4c09034039100c1c1806c0c000c2d01e1039a103003503181c0b00060a0840e1400340200b528000c8a0000f144d4011400c102205074202207a81c0380440d220001c8441c00b82400003141e215888403402130b01010000c078440f002c00007101081d049100740907000c860001c0007800040d0006554203440c40001c04000c07a01701003803004e01e9110700034040c0c9645011184240b6108c5000002d4110400d40f4145000000840c2e00b103020030a840c020000f4410200c0345103c0380c11103032605103180740c0d40c07407181c0d06150612509035144524a600054070b0240019040111094140185182c4a1801c4400700c100701e040400b21883c0300344d108080c0607050034015801e00701011a100340c56114000d600c5210280d501030980c90503006410388200500480c0d24141000500d0307481070700003c860082 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 478618372 1250 478617122 478617137
    0x31306140f06090f19022b020703230a1115090d09090e030304020411070605150405132a050a0b0c071a0a0e0607140601030c060f120902010203040e07 66
    0x1d1900b0100b181c1680001d0400c0480c2e04d600700107602d2140d03044a407642d0041c0c1500420401c0a40b042c1c80000c04601284c07011005814101000080c017170340001101760081000504054500d48031284000c0c0c1c00781030380d2075852811001003000d40c4d9406011140707080301e00ca81014416010030784080280500c507000010b00310001601002850080380b904144150b41c1031103001981e02c000041600d40055040b580403400d4980b200303450304c1d82d020340380001d4500d50a00b400d20460520b03070030400701d030400103440078846580c43c211a031001c2c4141060003444014140340c3c0d244100c800e42c1020007001004404440710b85d0b81c03400041d100705240d4111880f010400551100d07125010801c84c8001e1414103003070303c484051801103a400d401040e00d62010700c070344a61080da286c1c1c0c6007070031507001540c81f0b000e101d00500c100540076940d0340240001c4540035000b0b480490b0550040003800da600455568820207030101c0b000c406c0291215281c1213040d8441444080b903c400c1004010b440366289591711034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 478619622 1250 478618372 478618381
    0xb0a030506120304030c0329010905040c09050f1807410108130501140106031407031a0d29040507140915120f010e070b0f031306140f 59
    0x440303290901100c040c2d5108203c00c01c0010326140d08032013203a230082c17100c1c00807142e04600074004107800414107049201000c004a048001544a140078500a08e6030014258448151904480d415181407100a10810000c0e1310015040c0d000d500d00e10306e41013902c1c59165102c55041c0c8110f94440d9150300142540648524003007a840006000c2080c0040600c076100e007080040d00200b00600809600401d44041000707000094010320750030948c244c81c80000d580d540700024000c0a140302c2c610401040c01001c140558031134080d16284a0802c01c1310303800101c18108001c0b0500d40420b01300c80400480400f08001d83c0e60f00d80d0901c1c081d40103900c4410031b2500b4074103035003051000c3d0003007d030500590905a9003a103804007015405003c1180707881c07064540d0750000d05003100c1c008217200b45105041058100c1c0906410142c1040c0d0035038201c03542192120850713180783c060760036850b8100b402440056020840f240410540c039010b8400000d030300c0750b80004505248000c0710b040c07150012400600 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 478620872 1250 478619622 478619629
    0x2010b09090c13050601092102030a03080108060907050102030f090112060f0e091513050c030715090e010b090405072007030c0b0703020a0212030409091505060102030a05041a040b0a030506 83
    0x3c0c58552072440e0100958608040080c01c003802a000e408449456000f104440e2064410704a2901d40c0050481d4041c1001d4a030043c202070b000d016a0500c0c0c001c002c085031115070001400416210140c000d182010409c106001c803a8000da160345040141040c219500e04d05c0602ca1040500880f203030a40706030f81440a5030000080c090180c21241d402001151907845480401c59080460341004608951030ba0404e41c0c0742c00707022031a45915019000001070783c8034250120300c4503c140c5445040300c00e40d44107100380300d5500c00d10505510500030413404189240640c803150780701246d41000e80d0f400c1c88006842c3d1a42c241c80d080d203009903200e1541401400f249802c83c01c0100440301c00391f4035001d0550b900035103078400284000d0151108100c0745821403002e03c1034402800d07419200300300c41e12031030601030580714015440105903031400000c260346502c040106c40d0000b4417138507040d00d080c2c41d104d9402d07c46400d81c45088580401408082203503090040140440e42c0580d42c00300b2642840400c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 478622122 1250 478620872 478620889
    0x1d0c03070b18010c1505150307050d24270b01050907120c03061d1501020c03030406120207080a020f2a040504061103011203080109060605040e0702010b09090c 70
    0x1800411003070161a20079003540111000001c2c0c02c0c6050304512040e8504401d03652042d03034603044113500f45400c00940c001807030103c1080090840c200d504480d40c030410b0001c0100314090103442200c201145a003150300d40012a8080d026054000075050881c40c071500100c2c0300d1181050346d0421012401e005d10100054040c0074010407070303045402d400d104201030400e120f46032138810256200c001800f0198001da022200805a40e584070050f00e41001c119401460110307140b607002c403410110401c03654400240e81c059160083c0040d0f1600b818180c0a84180140310b65101d499502041340340000354414002d031424014540041048501104010f4140382c0d103242403000c0c0512082d4001c1440400364011840030b2416103000641b0b807283e081030005410109103c24020500100000c6c0040380e08004800c80ca010341e581101e02c0e41c8038448401611084e201c0c031400550244402c2c48a0b200103105260000c0c002e00000030384686030383c085040303800216115291a000030305648154101a01e4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 478623372 1250 478622122 478622129
    0xe07050a02120a12150b1813060e06060d1b201b040b150f13140d120c020411030718032a0807030f11010f170a1d0c0307 53
    0x1000d03070030f00141940c02007a5699801aa02c406501c0e00c1030031600a410400000203001c1c107084c1580c3e112820710700c201d0141250000700b40641c840010380f140b006420320445c01501e15140203100303d512580200f00540c0c21000314410781070740d64100c0c4141844040c03450400754895480710b0042622407490014007100340c84244205812000f800102141c01083d800d60010703089070001750011984010071507901c05080385900300440002c28400680400f0701400810302c003c20354000325900c844040c10545240c6c020300782c100c41e208001d400000c405032403410340008a40340000840d80581c00160688054400051211200106004d482603000c460140980301c01c0000d20425480c543d00d090b00010b4501c0c0069241c003643e220181060440c000010040c03e81d142102c110315240e08004003112000303130040b0754240d20440118611350041e44a000c41041645403c1500c424019946846480007020740b0101c9984a404220303002d110702d40d9403082131951005100613000d480078145040119003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 478624622 1250 478623372 478623403
    0x424090c11010c02060712020c0601030f0b061903021011010213080705030705030304030b071e020102030a0606081e0414010903020a020901080619021309020d05100e091011040e07050a02 82
    0xa10020aa80c0005917940c120381645452120088840351400090040307132009891400345000010030300000d0302c600c2c844035000e242d400d00b07691601810000c01004200c101c1c02100c0243da806c102524001c640007280c5a810700f44100078180030300105007243d005500761004804140018050350808108010141c8020f40c01001a2810980026541d0040e031100074101c1041100040d481403017940c84d054220141a00c400c07682181c00382c042e0103500203c2d141d5030305928103a800500c140c40b6840a40c0981583c441607440b41d020303114600c09003600140181d8400c618058070340400312091062840b241d02035405007407007003131a1040140201040e40090403680c02281403040000c045090386103104490303d001a039032444002c00400c1071103903070711041c1010301c0410520000001900254441c1451460401f000d40c1c50328001d031101030003a11000c1451b4030480e680d40241c482a80302a11608032686100e08085d942d1124520048003101c3d107800003075000c980c4003001c64040158101848080 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 478625872 1250 478624622 478624631
    0x1505010e0607110d140304090f05040c050907020111030c0408010b04020c0c100207030b0a050a0b0d0308060d0602040519080609030301080a020f130c08160203090f0424090c1101 78
    0x31000145103000740300703014007820004201c0000a941e5180c0c11000582d000c2c44e102803900c00c2100c01d80e102e800600c100c0700d080d400d020820880010501c919445681c0c4480b0041d41d0b14100400d012501c04001c112200f036640c2d44070015074080210015500c94000c003600070366902c0c14486810b080d1409410f14038004c80c01400880314a0802003a080c280341030580704481700d41500c44040313242c203505500280c84180030301c040c8a690005500103d104a10320581400540007440901c101074130340400140c00580240c0208126203003031040030300e10134001c00016007000d07114800124140e11813011204494100001013100f80003c1c40001e501810b441d01560456140009480d159984000c0080c414005900e00201c0345e5101405074490800801041040b0028100d0103050354505451801c0030b00340000c18400410301c000111b803944000500303500301c00100e440038440604101a0348102c042042c0c0181c0b0800144a401c150087c914240003080458170070002030f1016002540c0c003407041c3d062 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 478627122 1250 478625872 478625897
    0x605040f0501031110170705090108070f1205151320040b0409020a140d090203060108161502010e0a0302012009010f0c0206040812030105030f07051c05071206150501 73
    0x1080784506086007035070fa0310b44160b42644100c41040406c0c242101e5100c22005100d0565845400703481d060400f0703200c0c02c0503511418401da50b400b0448003008001842d034491020071580c1900010b030001c0c01240d0311840d28054000040d020420ba0540707100682e42c0d882028586071009842101e4243c0c0300607540d1034076041409203605031059004081880345c0015521100f14820300006010b41d0401c103201b522030482030700c010094140d80a00360f10030700c41c0f032002151610000c00c1d5000c207a008218000d03285454240141d55101148901d075003555070f00e901c680b40f40481171003040301140c4268000102240104e0341410040c074140b03038508580c482400041a181d81004208002160a00300703070707a006200c0c2c40001c541d4801c0350044402070042101c44010f0400841c0030b14142d40d0201c064070700382c0d610007222a580c0c450511925501509080c039408071400b260b00400d0b21240120259a03610762510003081919142201c2184c411340d0303444d03000724904541202d400180000746801d0715103010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 478628372 1250 478627122 478627133
    0x7050702060706090f0816023a11030a0c0f1d01060509121f050a05060307050d060f0c09050102010e060402100e0303131215060f060f11010f0605040f050103 69
    0x40c442c4001c154a07a128080c4c0d003031003c03102075100344035400841c031a601c2100101c4072035411002c00040b8018420212204100c600019072402e1410958521103444914041c03200c150990348801510040500d101c200f002d5101404000c400a014007050100c0c1440c0c019150014074040d4004d81e50402e210b010103414103140001d503411640e25103041501c2c0c0d502e10300001d42c481d0940c0400012403250b00140a000050f407030000790a00764540341004a6501c0b6520042034030f400300c5070303142d054100500500540c548a102c0100d41801468009441141509814212001045110041480701d0000c021643c4d09000b0303003102100c0c06014184900302640410045807035070340c42600b2300081400c680701d9a2010000e44001c00c1c655125110410b5454800b00c40400c2032507015149002c2ca001c8410442c1d21602a0600f00c8414010210350140361080c03c0301e0442c80301000718100185094840c21400090050005509444a00090322850407040000b11400c140281202d1402d0100400120704c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 478629622 1250 478628372 478628377
    0x1706010f0f0e0a060e2d04022a061006030c0e011416150b0d030e0609040f092411071e02100804051501080618071802030405060705070206 61
    0x421820100046000c250080d075001000580d1a50030083d244400204070341d0100503c5040c0906071240007070428001c0e00c580131450381e08506603000c0b402096600d42c07410150f0040561901c01c110415114500d00c030f80141c2c5102004240d166a40540144440c10307960300f032107200030402d41c1410004580c103414040d050280001c0d4041c1800746802488010b64905000c5426071401c50124000340001403404808050030100d40c2c1c05054501035400017103080ca01e489410346505512090002c1c0207044c10030580303a02508210390044c1d1a0708900d4249041c90041c2c0b90111310681e1008405030002203a1400000507201e280210343c180840a01011005411a2001904003404020105100700014401c802e42e803c001c0d0442c24502052074039a0f4440c0030f4a000324070078000d69110040b0002841d04206e020b01440b06950460008210000701c00700e01540e046a01c041030f031b0101035a9464144804080f2400081e040b9000002c2104202081c0b20b5503030f01c48a40e0404508081d07154000ca070990 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 478630872 1250 478629622 478629647
    0x1b081e1c09020f1005040906080303010e0106090e0417040e0a0f050a020910110a210f0903120e1504140109090903050a080405010f0519140f15010e060a030c170601 72
    0x8042424130041d03180d200344210b9001c0c0609140500203141d540041c15030341d5100b407140c41e803951a00c0e400030903000d2246481c07800305c48080c9410150382d10780d92513804c0c2251100b45000381001c010800080c4081e41601258403c2c240c00d08002008a101c04910042d584020101d01c1c00e184108082c0d252139944125400a000913031070301c182400040d00741c0c00c1c6451326114000d805012090030302007807454868004a00c01c11541da82040c4401081000d85a40203103002c0208010700f43d85041204034800d403100540c0000003005800d441080300746a03a00b03a4482e0b0054409903690841c4d0000c2c44d41c12980c014024206104108601d94a0740c80041040c082c4032120010030070070f200801c05100c02500641c002401e4610200310358240103411603202800aa42004900e0902045044805107140000c0c0b00d04211070b5207490a0713a83c01c58040074000403e8040307040c0100041b601c00305486010250422400701d440000741c145e8650b1001e4140c0380280c4280da82c42d49802d04200003a40c0c00b10780d00062 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 478632122 1250 478630872 478630879
    0x30f05101401020114130c0911040e040501021215040605090603060117070f0e01090e010b0906011404030507091d0712120905030d090e0c0405011b081e1c09020f 71
    0x1075080040040b40034007034844001c03104100c00b01c144007031400d1410002d01c480b48114160044940c0d0303070358100e080d282c9108100c40c0d02d81c8288410403502d6501c200b030030b610521820005150542110340300c24101020350706840204801401074100e8106442804007410080382c4050f481d03d4827400095a80c0cc05004092240290149d11b44030840304104084c050421020800420b50300c442c070507030403908244501400350342080c62820b902c901c180300d410301e28403000d400c1101130703981e800055664018420f1004000f03401008008003082042c850034000e043e50450219400800b4070102600210070003030145560003841f801c03c56884121440c101543e40070401140e070405404081d28412556409160513002c0c102e02003000b258020440b4090700c4d581e403e064003e48840c151400c1c1801540102404180d0003611030209421840c0041e41c650b11404c0e5243c03425405003108084140d0040c0700212080c004680c4008206030051201e82202250348100a6000f0316000601500d03007912100c1d00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 478633372 1250 478632122 478632149
    0xf06130207081e0915120a050105031c0210020c1f3303020a060339080a0204050d0311010b0904020117181606110607140c0f0d030c030f0510 62
    0x5031100d184144c40320500004c06a90884110002e07481d0b00c2d44c00403c842ca48041c8200c00101010a42d108444c1a0382d800340c003c0c4400500b540c0b492145c41000c3c1443c509500c2040700d40b18181c0c2c1b16000605413600c071030015081e001000c1002848243c0b49260105440381070240c0540740300c20040e0203200084022440c10303d502c1202c0c484500b05180341c1c0000e0342107441c070768020034203d4168114038101d00d007150045003000508030702412107036641c20001002c400c28405103143d00703104048054000750800b000514081d9900001051543d800100718003192004001346a454428440c0d004000019640341c0c0c0702d0314095000034001820000230402540c14440170807002c1c503041307445c5500000a242112041c203039a20345004114850b03c60ba0002480304180302d94905008102036008061644880030f00f140c2c030302058421303604100d101d000070b44100d104e0300003041001c1100d54112078864400007410701c3d00c208010195a200904058014108001c0c0103140c0c0c0411509001ca500e444046203 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 478634622 1250 478633372 478633417
    0x2150a0207020306132a090207050f010911090906100504020a05191d01030204080a03081b04031208010503010213050f01030f0203040c060801050114030a110708030f0613020708 78
    0x20024020750102030740500c64281000017502c1e0004281401c1802418108030502c2c4018042243c0076441c207000200c0050080304001c140c2258000e020308901c52000d0f10510440402100c0c02c41307441c0c0d041583c400ca0703807d0141c003071802e00b007191a400202013009410f0030b15015606032a10b000a01c40e00d80220380c00989440c003648168180c88484215011007640c007051a80000c0241d0940002c42000c0310b0251000c00d0958020710884041b5000c032070150402c2d0055440c10346103450300030008051000300c0c45150780e075110044001d102442c03117174580078844410114014140181600710501aa02c10400c42ca491030315011003e00310b0380c003142c840300c3c1e845d4000012070190190000d0003c003e800441408104100d0012004c242c070030b80e59402c405a030340c642c0110780e650014000c1407070101042011420207003141c0c05c01c00307032850f0710101e05180c4540d50350b60b02c1980d8012605600d102510340700744031303031407034400901d00501104900a605140490b00c6003c040c1c410080c40c2c1c01d80e501d0305000c56 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 478635872 1250 478634622 478634641
    0x40e18190311061003050d0302070b1302120f06070e0103090b060d06020c01020a0e030c09010b180604051c0c14100e0a09020a1d0d11010507020f1009060207150215 72
    0xa02c01540d55002d03940d031410080300c402001d103d0307400103d03594051003800c011400d203e803098411042d00043c0c0d540441c0c40700c4010011202e803554060b03030400503c4590188803001000580594002c90000b080d0074507107050024504034400c51818100350038162160b01141240b640940c00600445410388048400d241000082c4900044007510354000314481b4021604201c0d06008942c0c00d078103440303182c50010704009040c40309010704260903105005100605540d84400070611340c003d000b417071805403aa400120718074090002c0030300d0b00420860103020006486050070007400c2d400380c0b60b0890300500c000280a0240e8005840800403400b840742403564610f8242001818412030440d40d03001c100c60b004148240f4004640c1030104482604046030500a9500c00a070b6000540940352041120045030103501c00c0303000380d03072024040d884071010303a6401c0b10310705010b002600c800c00c4d02072800d40003030308000180d0703c90603000b0102000c12540c180c000c510703520740c00c04507040400e45507151890b1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 478637122 1250 478635872 478635887
    0xc08150117010b090306010f0b030117071e05030f0606100e0411040806090f03160f03051308010c031406090f070c080f03100b160b100504050408040e181903 69
    0xc461440e070300d40009414034240005003880482a401d40304580c3c3c0701c070300b00d81c1c41010038032410408000030401001004010204080c0c44406c9200396407d40790303520201d4000004c2030501003450b28140200f0401d901c0c00300b205a00f425500301c06401a8604040041c24044003481c4c840c1c00e10040c612016019a941d0340700d0032950465400ea151100c0c0c56400140d070b0b450f8210b42c408510300c22a48070284004000083c2c83c4044451120240203080655906a40903000390044003405403c0c0718801d120704150405074040e0030b03607000000d900d24103480000c003914200c2044c4200b040d2200305004054a4003d0b14590010254001c020783c1d40b01d02600300c030342c2012140090328a2402140b142110f01c0c0d01001580a612442071907141262100c010b900680b1a04d10008140c1001d0400b0704005503625004551069401c600301c1d4038650340d84042000d9410440301202d403d0b1000500784a0ba0b5600d6650fa90040288481c02c40d16141c2c41c00c601c0d58940b110341807103880f6450680000708140c41a081c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 478638372 1250 478637122 478637147
    0xf0f0306090309030123010501050f0d0c03090c14060f071e1a01050a0e340306030b0a09021003111902011b02030f090f03010908040608190c081501 65
    0x11901640361066019440381c0128100f18840e50a011402242407a4850384482d8580418564001a441c0c0070040d9910303071049151203804182800403080070f041c14480e5171a483d4998501261803d22481c0c480880d2129800043c0301000005100388c25495501c1642d40c2c1c0407080400c0360742c40c0e0305410803074010303c2c0324666900701c0e1040000100030440c05c8041c0c0e020030507141045c141c040e40c84500b003000ea14014003c50301141d0300d48001900c00c2e140350200d56003103101545443c0d41302c10146080400e43c0002c2c5188008a9201d82c8200200480d51044980c084c443d51420040c0b00401c0c1e002030f686502034000c5008050322500f244104a411314200d0789034003000c030300501075200c451402034040c0016024005400030820101040c0c43d0000c41251440b110046c52546020000c0003005004c081140480750550b50b103030038140000c0e40c0400204081e282ca521400b2141c5041210840b9480c00e20488801d101d0501c00889030458005014682044161500880744481000100c583e03040004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 478639622 1250 478638372 478638379
    0x70f0203160e01080703150b010908030a0306030b0a020a05072d060e1005060a170c09010305030c0f0c0604090b0d020307180e06062412010e1006110c0f0f 68
    0x80300c0e42548140d8105001200e0a284070b41001ea0b0761039100da030b01c0f8081c0744000b43c15200000c1d040700090000340d01600100005041c4a014140c44803015403442e0031503440c68020954486060040c0014083c0c0294000030090040d45010b80b483c0c00203206010f585c60040074800810102410404086401d030003101f61162100c0f0310300694102940584204602590f481c06104140800c4007510700503a48602c50180182d0210b40c500062081e190410700700044140c000c00001903d1503071004410303030003107004200441e2160242c3c108c0c10300b480400c05141d20154040f0a1040c05c41d110b01054a080700c1110788000b60300c00049021420201841000940c10301800001140071340b40d09103070b41c0e440701c0340300350801c1010782410307907240d9540e0244c84d060750210b6000d0040d60022070b4003240e00c00b0303010078200d45810002c103075011011a031820b03000941c08041070001c220340340142c01400d034028581d91a280090110002c0031640fa030b84000c0c0024052104c00041e401d03c6c1c1c4030b400011a8180c80507 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 478640872 1250 478639622 478639633
    0x6030b060f120a03051b0328320f03040506220308011802040b070501050901050c04031106070512040306241419080a05061b0403030203030a050a14070e09090706050d02070f0203 78
    0x2021802560114040450440c0840381c44142d86c84e02c0b940c6405032200f1500075a45016440404003980c0300d104010060f09c1c16010807c010365890304a0155000394032940080910342003214444404940001070307041140d007800019004240d008000740d044609c500c16035001002c95004032006442540c200203106100090070324100b005c1540402d00c82d40502d0000c000648030303d01e0b0312440d03114900c405407a00c548103041402030b01c0c01800501b6504d1240080301d1281c2c6103c1001d081d41d0f041980183c80c1a0340d5950509008131018440c015203c2d1102c0e200c01415050124900307002d10f00400d0b150103105042d5804009408041d000009420004100c40c80ba20300382c50840e684030340032240310106c520300251010040018500350f4056a605401842c1507640e00380300c95005000013400300d001182c0342d0720101140c1e4108010540200c2c0c050703a421100c40994030a0252203103026203903c0d401c0d4012402001a50b6202041d90740a10200c0c4015035a440603090071205902d0615011b076060144 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 478642122 1250 478640872 478640887
    0xf1303120e150c070b010602010608070605030603031e040e010b070b13110a090209010921031421060f1905270c0c0f0105040f06021c06030b060f120a03051b03 70
    0x21200a003004900c61050490703181e8947d02d00324280c5c0c03201c2c0b003101c03000d40c4031040c1030010350b010fa806503902950180849061600106400707031110600e55140014400029050004d001000361041c00341001c14285490aa4244d662183c02c0b60010b0408020380401002c10f020400d4100d998200420000e14415200f03488820b41c0c0020b40c00101c0260200348034010025050040410546000c0408404507020260307913141960828505038901d581c804003006145c440d016280040049689510446003030b0307160400a00c016030100b02c000610940e11450100100c82034000c0001c141c500c25288044010288000001000d03001c40700480514216401c1220f2019800058042d5001c0d81003141e4107003000d03070301c0e0f607089500540300903103014400d1804102141031a0020520000314401c52011305103c255420304464003034004031065804403061003030510341078400d0b031600a0112400c0100700401000c20b81d0340d2110240040c1802800310b038542006916038a000b170a0409031043d40d070303250f20 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 478643372 1250 478642122 478642141
    0x4050c09190b010206011a03060105040b04030f030e06070b0636041208090303010e13121211040f12030507140304050307092903190b0f1303120e15 65
    0x300c031442071019403400740c0000e215071000a00a048030410100c03640e81e4210408070b0b030800d600080040381403080406c00028954400340080004500803002218000110710b402000742c1030940603203100e00300a000c441c2c08901410310301c4c0e40001c0304076110000b01c0b500452110180d103503041c244035034030101c080c02d10404100d80e01c030300d120342e10a40f0b65403c01c002c0c5a405544503801520300300b180d0f40c0103200501050b81e0010341a074001d0f2004612405440e10780da90f9031043d061140c8003900244811403012000340c01406040160380325104c0380c504050419812140d4010f8512540c0b8814000b03e444009250046007202c0019800000c02007d2841e00e10100381d0341d90140c0315180c001c2c42201c50006018540c0c0c4944d40c0e45902840040242c58140d400590301030b191a840191b0500905200a803d034401c101800c601900c500c40030a02441c00c05078410200700001d040c24190700400c108000040e40c003034134421650001400000c0e5111014088c54548403803d04282008502c40e01801555007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 478644622 1250 478643372 478643401
    0x191a0402040e1506130303081003060921090b09041a0409031d0f0a050108040203070b0d0b031603050a032d052703060c1b07030303020c0709020909010b0304050c09 72
    0x30f0220841c8581903a0040c2802594800c1c2c000c00e508400c94010180300092041550941002540800740b00d060344035254003040703c0c0c40480850f10314009642d00703002e441c00c0c4ca000c1c650203c4e480c01c08400f503a03d031240e141c81d640702d01e5048a00c0303681c0d1172180401101d298003061025800150042188403a903103000b600100700c242d103d83c941d0740d54401d81c00c00c0b071030304610081c400740028060030f51083c640401501d58201c050030403a810300417407901007000c10501c8080c2c00d42c1e99050720041044000107040c14140030740c11180f5884c0b028800c0c4244003013440007540303d54040d0f040c035000d070910310704121301d4a181d48010301201b110202c1101c4035030044d9020f4040c1022030101c0b04080c0d81a030031400698980c282d4074210311782681058000640708208034015180d0071081c2e00da041d110010790008182841160b40045000c80c0d0701081011200303000700010000790a02e044110300e0845004001038107280140300c1c0181c24900000040c08004060043d10150280a41850341c10f0402804205104 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 478645872 1250 478644622 478644631
    0xf0b1e04080c010215040507030303090f150b1008041707080f0f04050111030304050a120528080f01230607061805010510060c0b070e0901030b09010f05191a0402040e 73
    0x1031240c5c92011040e001364504803805580d105004205031451950300f40c028008815050b54800b80d07040d1040f0206110300241c0c0010b10071102c0000d05c0040d01400c020b0b01c054030301c11200401141000700000a0769000e03406080340d07501644107803260300a281040b2507101e441400b0003070f0740010410084015450001d40191070b42600c035044110040039609581e400211000b030041d2b40007402c0a00403900392a220001c0c1c42240c81c0191406248540c0741c0b08a1251285c4030100141d58403240035080d50081000c3e420081a2a05460a514120321101da485155440c41c0f4011180a60780d80a680c44200f20744060750721203402d01501c843e84012313030130034503465000b0b0b2441c2d420040051038000c0510718100039103078a030712450704404036601c8540d0081402040b510501c0000c01d01450712750f984403100c0b402503105407410505445e1000ba0700d429030f4840c000c400c8400d4209010b02c400d81f6043c0d8040c1c2d0801c0321020b0005180c800c2000c0000f00562090091274006200050220b920025000c3c0c0c240329 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 478647122 1250 478645872 478645877
    0xf012c1816090f0218011d0406030302030304060b040207030c0b0c130803210c180a05040e0d02010c14030f070201290109120209010b1810030603030e0a0f0b1e04080c01 74
    0x158114100d080c0c080e44225480700305c5a20f88031802070155030040c0d288030440e120341c070541da1043c0e03007840100e0100c85040d0000d40c00b50b40040104001c001c81c1c0d00031007030361002c00d6400b0342c180082c07a0740103086d0000100005041490740030000b9046541e6400362070340c003a54052900d21195039030b85115100d0780300c0074144992081000364803442008611410380075502c1d1035880381c901412a40380400302c048809040354044a40c070780c0010140d9843c002c0001c90100030000d0150b03a010168068212510f06807200188854000c0041110302c8074000d5907400703800b8100881390f50340c0d0a0012401002000301011384030560752082e0314240d40d05c2d240d40e80010300a881d012107154172184155140d845650000f54003802e0040103001904011001d4000603150300821030045240b00300084a10000c00c2e521070000360743d22020018558080f0b103011480c0802c1c0e4100d4074a6040201184072440c042c02903004008000440c0140742c01c003414a03081c3c011461190680f5161601c03066603d0b01c2e103c0800a00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 478648372 1250 478647122 478647131
    0x903030e1225030204050405030433080630072102041104033e030a0b090705370f1202180a050f012c181609 48
    0x100d500340700d20300c0c5805289210040110488280581c81c1040304008401c40c0c402c440880080107848a00480b80680d1164010315140e43c01e0164004034400034885920106903402c282884035010786401d20040b4810346082d901f15964a004600c8582170f00d508500140e4025140c40d00402000c0090f148003607943c0151079801d5900c1960740001204144212400d1160240032001032030700f40e1207900d1404011403071070f00303080d600d84446090301c022200c1d421690100c4804924a00d0220f070081601010f150104071091800e200841e903074a400d00401413071400c00070040b81184500f0010040101402032800005440d600101000c8030102c9031292a241840180e0200d10411504201c0079906e0800f441c5000c0c6c0e140c0303807241c180700407000c0c1d0980e04502e20b44d4081c1c10407a24200f50a1160b0403002d004140c50904040395481040305910143c3c20000e980a00400700358101034140b24206503150a044a83b01c1075801526024090056400c41c403070f807018904218640ca11840888894000400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 478649622 1250 478648372 478648397
    0x60807140703030b011e02120d0908040f03030924080c0405060d0f14010303020319210b0102151e0a0e060f040501180210030c0c08210a0e070b0a05120403090303 71
    0x100c0480e20411406c1c05608202c1041a6200200d80500514401464040b50307080440d11001c00542c02500050b10007041c0c41001e005241d044040c00c001000c1001001040c4052a0041b00c6406840b04c5240c003049070301300100c0c1e0103c0c4104183c030701070b010041001c0d079250b100c070700440700824054801e902c6250500310100181444044a98100d9030550080d5103001176080c6082907407100b160f140001c0c001408003171540510598920200800900400100800c091001928003503200600342c8d05610f00604001d01c2c860115401c00200d1082a8022015107819034600040d00315901009940d00c1020200510a0ba64004c01c50007103014000800c6010001400a00ea405800c50042c0d0481105a08030208030b201c2d5000c8080c01c220351404114078000790380e940400e07a1080381c1010b040312048100100080e44095a6900606c940b00104040512401140d4070385000340f10300006000c010900388001805001129841c80803814511010700c0d281c68060706c0c2c5001e500055000a00b4014101c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 478650872 1250 478649622 478649657
    0xe040f0c0908030a230c070e0a14010602030901050c0106030b13021003060302030c010806040b090901051b2713060915080a0f0b0c044a01060807140703030b01 70
    0x480842020f40c0d24005c14095000e400901d071408410080400b03403013000768484048040c400800070703240e040035481c0c035800c20207802d000ba201070615668140342000c0c0108481c81d00003045600011083c02d21039180d1018200180c01440300380e00240c070599000041290200c211111041528403c03920819811a001c404804450b40c0f4000250507605c43d0424006540c021038401d503004000071302c081010304101c0041040800b0980c0c1c440c025070f4403902805042140b0616000841021b50380190900c0c142d000c1c40e000d200706164540c5948017004032407610035114071b032215408420000091050545e10340501c001014101c00781c00c0078460700c0001180203a008180c805c0c24580104c880c02c803039404d60300c0702904541d0140512440755010000000c5401c52080d882a101c0007402c0d10700c0600c03946d6041c3c03030807160003440580048038400340580c0c1a40341012107541074038020b142c046915956000d055a00c404d0a031900520307503801261440402d03030b0542141803104003c0e82e03007055941000d03111 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 478652122 1250 478650872 478650877
    0x5030111131e12051c17010902130e010308040509010b16020907050c0d03050f01060c0b150415180c11030d020702180907170a0c150e040f0c090803 65
    0x1004800301c0c80755082065001c29001a10744603040494003041c9a80c54400840301116240120380940204090000c1c2e54111051a0b07a09061400e00709244440440c0c0d5540c021414024042e019501241d2000322696000c0110094038403228200100c0d6164280350350150040e20615100f0b000800022030b005c005035095441600740b1909940c0308000c940c5c204100d14100504207801c20800707008820300a0001c1001d5215001f19403030000d0b183c00c0034600780410b114160042e50a10a4842c52040044d01c24658a0380c80640c44820400c0d5004500000d00500485104070b5440b8680250105000e000c8504841040d5100c050410030410710700c5060fa0545a4848910748640051001c440341c1c0446800034018244000c00d000c000354506800750941d80c9040d2a60300c82680440c0b0103210065100f038643c20740d0607501000344400443c550b901030000e522405441902c1c500c821001080d039001d002000c2001e0002401800003a1841c9420002810802c1e061703400914104000038512801204 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 478653372 1250 478652122 478652137
    0x333060506040311030f03030a0e15060607030807170a0e0613031b05030906160b01080105040c050f011b210905030a0f080c03070605150306160f02010603150605030111 74
    0x604140c03958462842c0c2d04c000300e4445401d8011014030081450b410700080d403150301c0d01314001492041500384c3c07d2500710008160512881c64600344445541e600d000d5410050303052400400030fa607069004c56001850055181e4004521004d001812040d600b0a08843d540107040301c0e080d507601380641c4140a1240c402602085103142010007108039201c59a045900a908581c50503d0520225900c0e50200c441c0103c10340c030001c0700c10b08110400580b1401060800024002c41c1800d031910704000d070442c40751038410420651185400c1e401b81601c20444a1114020b1f141c2032200d04115403130103141d080c0c0781d050348040703030103c3d0174a8000c825403402e0343c0010700180031921040d50b4100c00000807010566030310b10144003118024408100900744248110320104041c00c0001000d0a151020308540c0d229401550801005000c140c002e42250b0f0014601241c92009100d030070303401490b0710741000d000743c03241005002a00d19680c1101040701c1007a4000c011090360307200c808006010308a07 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 478654622 1250 478653372 478653379
    0x16170408012a0807171b03090102091f0503060609040902030604050a020406060f080a050903040b0c0307110f030d0c080d06030f0209010b04060f030f021201060807080105090108030d090501020403330605 89
    0x83c4100d9002010450441d404039000000a106c030045d1414030b060303904112590301c001c0c0e40010341c00b86035007084480d008480740185a455694070034200058407902000300014001e12010500e0700c10380d502c0d0707003101c103e40d50007a0603641c50382407604045441d0343c8101400e902560a011001807150b100300308d0004030480070742d230313482d140d443c0c0b51040c601034030015100003864401480041244c4403001c00603c0c0f240c84120082d6502c1e4417a1a00d89a006800292103109403a10051103845407804911001c6182e11880c110007402514500400f86001d44c2011a100314034014010003080342202c080007403d4000c0303520302c03516039039402401c0f9a0f00c124006d0300009540c2c0140145d13500d00942043c500060311840150404020074610807425000f40c0c404400520010240280150403141c4d1901412095802092960406108954911481054056103039644429100740300b4290b05407806140e10801c0c0745021000c50702c00f0820b1201640c0381a09011010750000784061162140700100c44019 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 478655872 1250 478654622 478654637
    0x270603060f0d061104120510060303120b01020a201305040f0201110c0405040b06040509010b031c120c020a1a0702060711010e0f0102031b16170408012a0807 69
    0x4802c1c010031840001048900d50b8a400980361600d8005000d000038061030001c4ca080c0d50070b00d003802442e159800c000300c440c01d840c1501c14408240e00011011040701000808a104042040102d02d084151072018111080c02050324007590f618642c41e41c1004400c490348640ca0400c1c0846004a442c1aa0003e000442070600180194041c4404011000d44001605c075041085004103090301c008031303012980001d00174108061381c50203100c1c00e504444030130003c00040d4440404a582c030040e00c0c83e070490000d030003502d20641c68450320000d9501c00d08081e00740116124020702a40c0c80007145c13030885102c6040300f111200e000d100040c0328401c2903140d008040d6511048403e0324805500301e50030001d5501d80191a007110010404c4026081c200400103941e0319011101401d55910240100e02ca0101003140110420011450f502c00c9070f001009140b10204c00b034451071180c0314039446000c9c10750070078508045101c8120b010060700e1050003685c48032100038010171520021304680d50b20210301c20 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 478657122 1250 478655872 478655899
    0xf051b07091a0904060507121107141603080d060b0d0b0f061303120302090d030c152a02070e1f12030507120201060918050f031c021e27060306 63
    0x700d8001c2600280075080080603205854230b22400c2c6c800c4101130100c00140021100c08100070021010046032100e009030070f480c0c40b030518002c03c0103030601c00903080000204200d400c000e03540d0300600c000c0107404030265841c8031445e4640701500c0c00a030401d2248503181024112410181d040b10007041601c84030030882411582e0741d43d40844810b148030200b581c00d00c4104969151280c1d228100780c00b0341c59a00300400d09142c40b8540401c0302280003041811f1140d05108000001c200e02150380002d00d60b045112107010301285040d40d2540b0070208030903200306010b0801d000c0d43d01104c00e260038204901d422071301c0703510494029228683c01400102d0030482200402e02c0d00640d01c008001c130b0b10011403441c0c1d07541c0c1d05005480d0031800c803407030051801a035001002020000d02251802d01b00c051410800710b03807090807969444000380d00450b500000d02e0120f00701c1c020049681c880c2001500783e01d0340105030380b0f03001c182801d031462191031400c550010300e10703e0702d2801c1e00d100e06401044a02a500e0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 478658372 1250 478657122 478657133
    0x90605010e150304290603070b161e050601061e020a0804091a0405010b0408011401080d0f02100623010801050f011416060b240a0f051b07091a0904 65
    0x20b0042c0d40055428010000400e00e05244007480c2888100800f00390824201f01420005c00d540100103500082000c95030200300074a038100020340000180088510300b640c808071004455100070414002c0d070300045419500f003901c01100114201c04290b03240e07011081039a43c0e020501000e401901b040c030041208031180e42243e43c800c1003642c80201c00b108170001140540340c00303800103c4241c0300401c1c2480400c2023485070180074103210403103015a5140c0349502d510754240c81c2c040020403e81c600c0700e040d074a00030803181c0030316030884401700103060b84c4070340140345620400c1c0340c50b06a03d003041980c00a98480c0c001141a14001008a244103c5880040d140c007140c4080c0b00d8000e04041c0001c94803540c08030581ca444600a50000c1000c5030010300300b150110705440445401100a039840f041c1e52050001d4803c2c84500741040302001c4c01410050310f180c050128210768035803104c080d4501c09070001c076050003224040182801001c0c08100b801c034030307038554100540e084445000050007140 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 478659622 1250 478658372 478658377
    0xf0302180a020c070b031e061e120d1e021c0509030a02030115050f090c03040f1121100b0d1502120a0501180606020607120b0613090605010e15 63
    0x54507220042c90542244440360a00745154071907010700c000401003080c81e040c4500c001108407031240d808015850080001400742c0302c102880520170b105400100f010b0303120445502c00315205c0c01c0444a14854066009050b940f21a044000e0840303003000c1c8502c0c2600004517150341c6403452603103010060410400321051342000540e0f982c18402d40c04c402c009078500b885614550101d06400501d000d0a100074040681c0c2800c0d101c40c0503801a0080000030301505c0192074115600504a040502082c10000300c00c00d01c00100c158400d65041c40a62240140e0b0245001c0d41c0c1c4040a40f01e0b01e20750710f0340c80001c40310208056908108090100c50020302c0c00000d8542c440f4081c8801410180408050321080760115541a0055910001440306403459072400400615070581441340a05051000707454960141c00f110502c103140140d070b01c480c411600440700502c0007810588e00c401381034510114110951040d440751500c0c000300800c043d44541610741e032903c405480da00d038040c1c207a00e40300c01c582d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 478660872 1250 478659622 478659631
    0x50c10020309060c010e0f0a0201021b010e06030f0f0708131e0c081605150a030b0d0503031f080c0906130f020310060305070f140702060d0903020f070f030218 70
    0x14042000b8004280d650003000d0850581184000100c0003030003042d851130031a040d4100c540f40c0d4030aa112200503030380003c601c1c000040144030b10030915101d034010f81d0a80c20942400d580036401000300300c5070f810788ea041c0728420314069a02009c0394451800c22f0710190780a91340c400c07002d4034074201c0394041b5142c400070580d820542e11802d895481240c41d40c0181c401950040708150304140040c20541e170740c00403204003418003194000c00e0300859445482c1d5070320540002006140c0c441000b80c03200d030741e00500150341036000000d803a80c0b4a07110038420010700396003403041000d508074040441e103880000791140300403070094071047c03203626100304002c000da04010050103580c0d1580c0080d89020400d0000e5402104e41d00072421081d428104040c06449004000c8130402c12589101c00000758082142d408450850084a075505640d001191040c811409059442420240e0000806a000803440e0b04a071012040d82d81c510345542d044000b90301c1c10710003c1d601c0389214070240201a805c00585401 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 478662122 1250 478660872 478660877
    0x1801050f0409150507080f010608100603180c1e090207020901030f02120f03030403030c03020909010302041a15030a11070525170609010507032f04050a0b0301031a04050c10 76
    0x142208944400f0940c1c20031241100012088428001e4421840800a01500340390601a0301850600c200401600980c4240c00815446614220034440c80c401c0c40f80400d40c01505101e29292513460302d216203186203201d255154801d203000540300946100b5100030981c02404400664030b142c41e107007034840902d1400da9000303208444280c0514420443c41e01c0381d0b041c06000c1d540364545400c01404441d4050050ba090500401c00b11801e9035403e6503a50540e82c2c1180d002034080040c20486032800000e20316160404074241c44034011008040166224451404003401548078103000030466000e1707031100800d181d001d50748081c1180740710110040e0040100c4400c0b05c3c11340d503601d0a1110300615001c03140c0d054200c9010302107000c1081c02010b9100e040c50400744100041c0a01c00ca4280d443e80b54042c1e05030702402c141044101240d0f0486005040080c10041d0694850f040b6051549c0207100c00c0f1030709803410b0300700d40d5110780c0c0c0c060240c030544c1c04c480076007000810042888030a00808648404 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 478663372 1250 478662122 478662143
    0x70302040b1f030504210f0f110f0109020a090b01080a1a150a020d0810030813051f030f060b070b0405010b06031003020f0307050a150903150b1801050f0409 69
    0x6091400741151400500382d0340d40411641000c0c200b00f0008180e46000800d0410f82e101031440e240e4100003601c1c0c40d0125446e21103681d170404001203400050225800e000e07800781c0c00101a440005400c2015490300883d90111801e580751719100031a4200b9000fa8046000080010b041c104a540074072040084250711940c6e4400d40310000e2a407103200b00d02c03900c503004081210400d16604200001d07a82030142068082d0307040900c1c800c102c0d8805031200810042e400103030002d000304400441c070700a06019009500c01464201e40602c40314000b58640300081c1f502d150711b4401c01003401079074100c403240f03c8214a400c00c2912a03031010b070f40c0244280c9156489d03c4107002142c484200843c0308030030749194481d1103800c510401500000c0c091100784281c0c05450b0070f02850307030b8944892040b5110540d290000010a01090360b0b040c0ca9684040d2007440c0f00502001c8500498000c4140403004803040c03000340f02c0c4c5030046043d02c035080c098203800c81c8c42d00090140305e00f0950300a490860160b0f070300d40c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 478664622 1250 478663372 478663399
    0x2190f0e030a0c030b06030a0201020705060c0106030606060207170303071b050a0210050409060806150f031504030314010b03072a0c1202010e030f03270607120206010503010b03070302040b 83
    0x3403800c021980200c510b640076000404c240080e110f00a03400840450250001840d1900000c3d40c820913030181d580b05107000078440400000961285005560101090141a640e03c0010b9101c80c080d2140c8503401d0f030419010501042e0100450744030340383c1504c50072618001d0810920441031034003000c80c0d19208454840015981c1c5006814071400542d507460341d5a400d001c2c68409030b90711603101d80c034264000f105002401d0350800070380c1e600c100169946076040c101c0800084c03602c421a90390a00308029072040c0002e1541c113400c00282c40010110410003640d031980c00c02c000c1d10003140c0310000180782180901640341422406500d054034007864420000c501d81707410012141a80c01b1340320b40050410203104650300907801201e5150103c001c0d00c190f02c21381d04665120300c10120b600c000190040c03e440c02606407081c0762041040060b10154484400d0b1503c04c02224012102e40054826007000183c0c0b0700e414081c9120000003c0c5c003900045d4907650030f001c064244a81034a6000213002c1580 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 478665872 1250 478664622 478664629
    0x30b060409060203130312060302060304021203070c0306091a07050d0e011d010209090907050d0b07170c18092818050303150603150915120f060a02190f0e 68
    0x10740c010f8600903140003030b03e1106e00e000380560751000100c8600904244081015035a00c100740c0f07034801d4042d02c809109990a0905509500c1407d00090848048020200a00a8540c001c00308284a100813000742007c4440b02c16044c9000c03211440041d01c2000151000d010a0b041040000190400416003007140070303400003803c4180740d4070a0075a60208040419107400c0c11072540001210000d07105460902020511040900c213019103445050004140054840d9201040510300e540384c0c0300b603509120b0a240020391003440d1385540015034268450141c902038030802d0082d02c00c29108031610100c0800f400d000038101c00302144403aa104108860000e5003c0c14030800e0788648069030350391a112005074040c1c2840100d9a00500e018000c000702a480d5415284400b0380c1250548130030b81c0c0d10030050840b0141125010742050800080103000200010ba032640312118200b40d509075598a580c0030100d015030421140c401c40c0078154480400d000b0134681003060131a1404041103080140030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 478667122 1250 478665872 478665877
    0xc0a02030111071a0705090d0c090c0e03010509151306090c030b100f03080a0c05030904090809010207090207120c05030c0d021b01020d0c02060f1e09030d110601030b0604090602 78
    0x31488a0b100000d070300c820815020000c0014207a50b4044104a050440f0000d243d07000781304800e400f610800150a0038480c0004030315000300842c000602004401000003840c0143c50510b240c00303036080c8008a045560081038050341001ca9030303c0c01d440e070340c0c03100c114a5215144010503601295901e64040c003056111a109028601840840040341042d4001032244100c55001c00100080c083d001d01c00641c000d801c4031b0b4200351924001d024581941440da045200380004a6403040c0307030640340010409a0030180c5600c120176000d440ca45903403800c1c0c1c03009030311485400500313290b22141d940064501a00d444002c10f4042c0701144d040034a000083da182c086113100d6040513034003549030314807a01e440d100300038100d41c02032000d4400d0b04070744c52000d8207256a00c44020b2280c100071032082c40c5001c42d00180d0324060034184040d500c031803940358840c09a900601c000c170301034002c04441e090301c00d0041d200b140424040b0303c000c0806138a0354488441c0300d4005000e066100b40c40346040c00210324079001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 478668372 1250 478667122 478667141
    0x21801051804140f0112080d02070c0b071101110102090f040f2d0615120f020c0111030a0c030603050703120e041d0609070f0e0408040b2101290c0a020301 68
    0xb80c00e443c9081002005482c1d030016802048400440300000c40011410000e8074810300c00300c600540c0751017107450280e44c41c81154000c88036000c00428410309104da43d07440c02c00007402c00e072a540f50240b04440c85900783d00c541041c250b0013100c8038a400d40c0c941495401080c0304c488000b000299049000e050509841f0880d10714210307071000312a407500454161061400900c100c400710380110b60b0000e8050a044140100c007000c2c0c5944000003040c20301c181e0104c600010255008100080c2d0003900f0b11200e400c20380c0c80314581860904101d0000d07019108113000c5d80c1d002401444039515681e1100f10106554001b6400c1104041c070a24080c1c03200d018004d9001000541ba032001ca44010744245892001406015581e000d0300c0204008031a54840409407090072200840326922400c0888076881603520508001e000020300c40b4100e803a0307a0302818404400c982c0c485c804c0e42d039010315050340701d00f0700030b10810541201d240d10882c004501c01040c803001000306032004142c83e43c0000342150b2000e41c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 478669622 1250 478668372 478668401
    0x310050c0d0506041a040c02150903120f010302060412080d0609093c020f060309070f090213140103090515090114240d20010e0301021801051804 64
    0x10704201c29500c0d4041c46502020640f0f0800094501044054215040c548104e0080d5901c0c2c00c0d05414510900401c20a40c040e020148881d00b4840021560b83d80a4441a0b8485c6007a4000c1804081080c001c0c504880e001000282080c5c2071501c075044c1d10010400c00c894082081006001513102d80c080c0b5001899050000a5481a541400c40015000e00d805008840001c02e010340c2d4503040540652081039400600c461290441c03004c100891800c02065600081c08403c011042600007a4081a6285800d02c401d896945041c440142e004d0003158480381f8060b0002400030041e4511003101c0d03100145808079050b516a02d40c6070070304003285417103400d5821001c1003101d40d680034080c00c2407102241d44904124a0000032a480200600c1c1c806000034034940003940640c1d599681c2c2d40a82a0072050034424a0ba0b89620801050700c0082c0b545c1c0420002c0304c00300d0309464188240d41c3e41c296003104620302251803c004403030680c000e0402e0802c01c441001604a01d071524891031000d44020b9 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 478670872 1250 478669622 478669627
    0x90a291b0718050702010506130b06040b0708031b19080712140a1a090612010b0a06080709120b0a09020102120a030506090903250804030b15120c030a110310050c 71
    0x101082c03419900c004125600b035a05084c10300c0090740328451900c500c505010800145810b100300010074070311450344021303210038000c524003041c458003100540c004d00011402203402c0c24001000d02700c0e40100080724070001d0110075034a800b07d001d00c08032640b2602c90315217950b003d010b8100c403a04540c4100724408040342c40008100c1c48110920035143c2c001e003246820002d400000c8009600094010007181c00303501c038100303081300440c2d094000d044001401040500b829840702c000a08508040310340c40009140400300054204440d440c0038800d175009410801181d0395095000050285094201c0c114400c0c0b0a11010752050480941070120203a40c0110b500e051203c200718001501401040e2150802c000c4c01200d50345c500c24900070b0b40210031100c1400700c03403410030348024040c907480941407000c00000c004141c2001d0007000c00784d0038120340300317010111700300c0085560300700112850340c166120301601008130b5004003158800105c0101260134a2030f44402c14030507510103172803141e60110007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 478672122 1250 478670872 478670909
    0x607060c030b040605101b080c0d02010b040513030305041a010803040e0c0c0c1905040f0c020d09030320030c030d0506120c030a110609030105010605090a291b07 71
    0x5010b4412060302c1101d0a201c2c6905103000100003a610b402c0d540144408911410380802ea0820503c641d170380c2044205840751070039107001c0d48030380742281c404005500c0d00c0c08082840c50301d88038290181011602005501b10540d600b0f500600740600181c80103074100b603001400740400ca006c2d5010340a500702540d11240745c542e800c00707841405000300c08181400d02c018514010001400c1080307802c11280c0c4040c5165450718804819800d412054006003050300840e0340c0702007a045205078040c1c0f50308903140d1462400e4120342c440c036280802000206a2400483d00c02e4910551080381c00f011010342c0d01d000034500744c0c10b103154840d1001410381d50315807082214502e84044048000c2000d04090300601110f940004d8880d2400c40000f0314801c5148503041d07141c3c07a501c065a00c0c200003d0001c120958440901510b140c00c500051031190b400307e003000c03901443c8824440740c546603881d08400319030403141540e6520707044081d001020380c001c02e80495541504001a8008107040c0d042c04070040c60 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 478673372 1250 478672122 478672127
    0x402030c07050a141204080a1704030c080309010e01030e0c04110d0e0a0203070602060403020c0105160b090a060b04020c070e06040b180702060f0c030613060902040e0a0e0a03080a1a0607060c 84
    0x18040c4d60350300079801884200b10500010a500c8d0030980c4c0f003840d841840591215016160144d5007014020902c40d0394003140d4400004010714a481090701e407050908122401101a1950707180b98003216080016401c8083c103003030700040c422500700069541000f107000101011540803540b41c0d030041e0302030110b0000b5800c040c4110400b61107030340701402c0d06103080d031400303503035842c50542c01030400a0008507203000c11480803200180c2c035802000e50000d800c1c600840c2e070340c40d40c0405003511528941204903030a4500740c4202c075181d15911002d0a0421b141086001210360020072041c3c0041e1032329020b04460381c40c110b140515000e058215000c6040c000002868607000503c40311000c0300c007006000c6401c080d48143c81d8080400c460070110f0030302e1100c40d500504081d0740a0002a4000301c0c2c00700c0d6804a44070898072800c04c1041c200b03c2403082035a001d42d0750004100140201d018040071640c1c03104950840d05001c65881c0c8076080140741c100124200d640540011341d4100c0d512881c1c4a29a42d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 478674622 1250 478673372 478673383
    0xa1104060909061d1207120e0a150305010b1c1d1212060409031e11010f020c0f070e0708220f0b4f0303021e070c03020402030c07050a14 60
    0x4500001010b404513000c5d46042d4500c034840f409007a00d10b00e03052800005224401994403ea00900340c1901d566503035141024282d030301501d11000c01d00302000424028240d400761400d204140502d24200e0320300344885030040c040c0401240b12421040f80f9660303003500400001080285224000c0d58601da6039840300100c80d40a42054070460521111001080d406200c884600b04981429600380380b040320300759403014648024003107a50820040c5251141158060442000d40310113885581105880c043d0310389000c1d0086c0c821040d00b10740800e052900c00c01e2080da1001c07031080004402030502040307030411000a80115440e219551142c0208540901c0c0c0c960040c094602070990021500d690703414500d03051548800903075022040c04009002c0d07808600302100b0f80260640c600e2a00d00340280698400d40a4045810086181181c0d0344102800c0710105070300304900049450548e402c2201941c00035003130b10aa498240485004908240300040d800340c419000305921002140d500ea0800 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 478675872 1250 478674622 478674671
    0x9150f0f090803030f071b140705040203010803030f0c0c01060806010f081519061a03010302040e070f06030c0903020603100806090a030519031116031407050a110406090906 76
    0x1407052802c00c101200003064030b4100840781d42e80e00180ea6400001c0302c04180716007141840c0395044890005021211880000e0600824192003000f6107030b10034401039110a20407101346900400000d903e007452202960340005c80e00e801586040da01403482d0342500c85035040130100c1e4112000411a1400341d0308003100034041da5000d0500700d80101c10260000100a0407118402911555620003c1a945c8020090464041501410503050111903d1a0802d000c101d000b90320700740d00014603200001d41101107a0740c5007960801141030441c200c001d0401846408217101a18002100607a130710405144520f11000b10701007802d10b84803000d881c046c00030b85010300a4000c804400c0c0440d500000300c9107200962750310011152103d040c124020469942d82c1c0c00400c3d40421018902c44042a602280d94080e0795aa4802000840c2c507022038820480010903941c08403000000240092880c0140d10318000c00000700c2950383c3c4d0b804400d9134200d55046480650390f0180950400001c40c070540310 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 478677122 1250 478675872 478675877
    0x20106060e0109030f06050628031704121407090c0c021e0604140d080703080411040510030201030504060b0310020c070b0a1b11041d240c090109150f0f 67
    0x400d203585c56180b100000e2200c094580394445e0002006500d5001c50403005d00350441840000a03100314215446d08050b01084a8500e000c080b9260800d1040003503500303484a5008a11800c88071360f0741d0003200030b0454040c5065014a80000071a8440e620440c440c0c54103031344900520711160300c1000702d40010000502602c112941c1d17026001d40703d40d400e44007034038009144160b400944070700107202041c6440c0f000785518000680750040640c40070100d401648102d544001c003c2c1c880741008191081210a5000120340c01020005980b2079004650028081d881c001018100b8030003007810026111b901c40a483c1e00000c201d50441005c00516004003e1202400d0810340b04000080000f800002e4008080d2124440c50b424061500300d0301503240b50040081007168007181410314101d00100300e020303550254082d4081054030041c2e100c0000e031002109480e882e038035254900c409030800103100707040040941022030807046c401d0701c47c5c030044440c2d100d80c80c102c03c4a00004001c400d89175000c808 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 478678372 1250 478677122 478677137
    0x1403070c06111b2701060201140114090406020706092a090509030f07080c0610090501090209010e011101141f050a14040c0e18010e061801050904030905030706020106060e01 76
    0x1003000a01d0b003c2840d07000440d62010200301c07415085100c0d6032500a000e000751100d00002418540550162988100b5900503002c2686d80350382c0e035085648000301482c1c00c80000320015000910070b81c01481c0341441054000354500050f150050041ca240746210b49075800c444600c05010a01c40c00c1d00e0080c00d16070f0080c00b40341f5055901d1030300d80c054420102e03200c1c20003150850801070113005072841e0300001c07000c440e110b03d0000348a0486148501c00c40302c08901c1d00001085108460084401c01c10040e10b81d510407000d044011a403c0400000040c03c555a841c100301c0b1171303405040114040c0460400f11205180000b02d408800002988001d20995881608000e014003802da000200e2104407800038211100d445c054a621400303403011075104200c203405203c44110a00e041e41a91004681c805060351240705000d20394012401031250140800010405454a000c0003a40103203e881e05404195031480840e00c0c1400c6070f0030440240c0d44585081c40207542c000140c2010700d009107490078 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 478679622 1250 478678372 478678393
    0xc030803070f021b0d0f05010914160b0301060c020d021306030807020f0108010513020a050d020a050a0305101a090a0e040506040b07050901090306021806192606010c1403070c0611 79
    0x907178503800503400500c241d402c3d880e944140002907010400a83d003043c0601249100075686c55200d01c1c3c0b2000d52614039020303840c08504601c56406a80c1600d82a032a1725401070703141c1c0c0802082010429040383d10a40e881c05d1009052414003c100c0107500c40d42d0002d0b15400184100002c00c01d403c80c80701d0400004000400c045d5403498000401130021000044e03032114491030803600362003001014030105000203600b00074143d0010060007107001c10f941c100b040340c0300c000c8910401046c1d40b044520300715980c0305d003460703160701c003002810300000007080b20002c2e41d50782e200128010000c83c0d0544943d000081004180284e07400019884202460050310340142040080c203005c090b400041c0526030701140580003041c181b0b1358404010030007001c2079119a08c405541c443d0080c1d081d8602d0005c0e1a8010285803512040f0501040c040054143c18251351071b030f0011580b03004001c00981e100f1222501004141303400703000620949024010340e44e01282030180282000001c0c81500b01158050540f51 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 478680872 1250 478679622 478679629
    0x9091e1b091608090106050a0608010315050108070515091003061502070305060a0905010b2206062f03160501020912150105040c0239060403030215040c030803070f021b 74
    0x40b01d20840ba00b8011182d03154107103124018071694000d40d801819880c0c020030702035005240700381268821122510485408210203083e201c1c03e00c20100070364810700702446075113081c100d10001c800d4116a41814110350000140e1154010390742c8001095846005100314240018405e024030514001000380d40d103542d5495a07034240052541407503a90790101d41040040030b400026803600002c2030219107051541e08406000520f05500d1010351401000181240c011040103941014180e441c50b50300b60f504030074640c8002c003900105543d0004200680707406440c0181c0400d124020000180c03a00c9041c0c0500c11780100001312820180d01c00c44403081c007045201551815520181d03404224890a180c0c140d02d03200742500c2205001112600d14401c070201d0740c0f04a8900e200b0403114003c861504000d2080611a601000e8016007051104a002c0f80440300410f0b003040c45003000c420f03801e80c0d0346c0703404c0b980350001d3710510b000031610060940070030b50410103400c0c0c0342001c801c5401a0080340000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 478682122 1250 478680872 478680901
    0xd0b09130b0a0f020307021c090f0b0d0e0d0207051503280b10021506060f0d05150a060302030f0a0209130905010212070206090f0d0e09091e1b09 64
    0x41826070010002000100356400844070041c0c168015912401c01100103901d641ea00c00150300008003000e4031103901072080101100f101d90813180100c0460078540c800106901180c00d200328036464000440d240c0500700700300203c003a6542c0c05042c1e003505103c00c010b001d20310b41c160741a001d1000d00900210030300d240c86a904600410302c00030280d000002004001c3c1000104140e031100c895000564081d0b0045000014030006001501d495a0f1fa002002a14040c200f00312124000901030304250100607405030b40c02041c41c52250307603003501c0000080e04490982d00044002500442809041910070130b42c5500046001340a50030440c0c2100443c040c402d49018001e4150349500c4000d0038845c1c2136046501001c184041e5031140c2c0780c007010103580c412040c1c030b901d0101c0c0301718000800f1880340419196200025503079422f0b690303000720003044002c600192403c000780c001c0000f0004002886100e0340c0c0341d12440006000c4404c510b10304100725030603268510b4049d40243c0c04105511020641 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 478683372 1250 478682122 478682161
    0x607050a03091505130519090f06050310020a0507030c050a0c030602120f04030509101809060302030d140d0504291b070f030f0903060504060209041a0915040f060b0d0b09 75
    0x210041f0041902c08a40300e403607555071107509500d1406010b644940c0141c0c02c07100079900d060f0b0403180e4020b12107442030200c2c400d00040d003002850511016000038852180750090b1401281150100c2d59251070f01d00001040360f1044038400d82c00540503c00d2050011960740c4042456096072162425850242040c480d000038a0302c103091116500b5101d9010300c9402000c60350030210302c10840d48880001009110324001640300c0d1140090003644a88a000a03421070920400c0a600304818208001e003d0980684122400d8103684c2c46442007103821481c2490603103880c544070b42c07a401d0ac0700c40c82441c0070b061203254000440801c0410080b9002c9242400007075890b141507c03044501c8001181c078a0410340009090604001c20304c01404042d13000382c50501e100311000c000070310b00c0800351544071404e0011b2603004101100041e00390a4402003114140c100608007103070320260f44005a003114000d8200042609d004100701030000b910384a40d00c050041520b10074040d06120070021203031002a031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 478684622 1250 478683372 478683379
    0x403020c010f0201020f0c01060905161e2703060c0203040e01140102030705070b0306040c1e030905010b06210c130902130b120708060312070b060607050a030915051305 74
    0xc0341902e80e14801d504480519002c41d9180e6100c0004a0425020f80020700c1040d0000b420880490015240e030704c0c0c40080b10101d502c0e203ca00004d06140e4044590f01452403400707028012034901c840a004110820541480f0400460303851704501d80f00b03040321442c4800804642c003e010074000740803100820790540301c10b48100c01c401c1c99013a004070301c0d510403200c0003411409444400038210704e00030003441c010f00303086a05100170003808000311101941510350100d452824188414628001c3d03020030100c03401040082540001d11000c120168407460744040417050703100b04411071104101801c0d4000004610487c648000744410b4941c0c1c84d050b00074a4940b6500084800203607030301880a10042860b1600c0c03c1e01d4035002d0041303202080013255010082240c08001481c0703407902085c02007098080c0b6000e6800c1c600c50381c56007462294018581c0790048001c00140300860070400480440e540719580d0b403000a1b0078107410422500002032004144074081c40941050880700300d00740d054a0058 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 478685872 1250 478684622 478684637
    0x70c0204091403040f060e03030906070605130816030801140a1a0702090c0406030c02010b100f1701080c13091101080702240a0b060f0702010819020307120606080403020c01 76
    0x1c0c14007100103000c080b0b07241c070944400200000d0640707400b0f1102c81280c41d903881d212280340c82070050646901c1182c0300190311510412a00c0c0c0062003d5100e40e030805280b5040305a40303d50380c0e66000481d8440d4101161100075441c5260070541c1c05010103000d8407000e903026040745030341008124a416039015214603491803150307c21203242145c080d41c1c0c0760f5800400e8041c0e00e05014424101030740c0b09020b4140080d09142030214010b0050040da400c00e0006442419410040d0004958055040010404201064104c422058800d4104d80c0c0605100f030090301386400700c4410041840501441402e4090511000f10081062900c200443e40800e09050301150303925071049082802029240040d841d2000690210b48240906280719103a041c0c41081100480d108000c103d004028844035a601d007000a40010351140c00d0490300038442e0f04041d5011510a6000030503a00204c500000040740310001118815180c050040100051b0038080c8083c200703034034002c0d100c0c080b80c0882d072b0501408 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 478687122 1250 478685872 478685891
    0x314040803070c061a040b060a08010311030c040e0c03011d12071707050114180319051c09020a05100225050a080a020901090b0907030b0301020702090f100e070c0204 73
    0x114521020f00364440d10800080c040640c80c50802c0302e400340c1c1980254038100c11040c05040001c1181c00c292178540300c11100360700e186d4079043c000c48880c0c80c081c0c16020780d14964441c0e4680740141688908030340060300c00414030304141801c56140e0840541500b1000d070381c406035a000407900d10202d9007a500300e950f440c521b908101030044820012030524200000350142400f1065101500c21510054240525181c01c40c803901c00703091405480d50250000c00c2021048180040c03c2031003810030b42090750500a1042c46070741040902c0180c1d40f052920f50b01d441d030840c5060700c5000003400040f1801d102248140310001d54444268550600080c00020283d282c0f40407402000b0090000a0080280c541c80c0c00d00701d03445505d401022400b0308650700002c56900c51900420703443c07105c058100c0020b51b40e0548100c024000085903190195803c004810242e199031a4840c07003010050311701107450800c1b0305001c001c100180e00603410f000c01402403242c0c5c0c0b60701501c0c0700a400d03011100810b40040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 478688372 1250 478687122 478687127
    0x1006080c0f0616030e0d08030a0b03030a0914030c060a200312040f06110d090201080a0207030e010c030507050105070c0516030c1211060a020c090a14040b0a0e070306020c070501031404080307 84
    0x2e0300d144071503024480c0800c00741009080c7d802140b0441c2c440c00148007010000c0c082c140d40f801b800c1a0f180104a000c403041c03105004000c805c4201590060466010b290b0368400308500794003030103285c0001070488440184040c509068000359480ea800254034060100700502444100034200070020b0014030400c0013401401e03040021030340496481e80341d60300e0100b40040e004040d500c070100d02040400000551000d418401d98400503095110516440c0900c0011240d05a0012080701409000d110a201081d401d00c616449100b250300d5000410f130750350400c540f0300b6411804414210303803100c0701400062284151001192050768942d4411079080c506854044540d80381182c200c4004510421540e90000b007500c6148001c2d1b80e5504541c9689041c24191122000900c450029400102d40002d1340340c41000c0e84076020010000d844800281000d0500580e2341c011741c0c03082e17008503c203601c1403014096407005180c242000c104581c0c0307800003600900300062002c0c00c24840030001850260 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 478689622 1250 478688372 478688387
    0x80d0b01030e01290409053a09030b060d1a06030c092e0b09011d190602060901060602060115030b061204060f020702130c0e031006080c0f061603 64
    0x4120b8402071056a5540070303110066018003800412455031513070140880c0c140b80c410203c80540042c00b400000001c41c11031112a101c00c4500150072030ba8034144071100507000c016803000300d103983c1c941d045a80745042125030307150701070306003032140400681c4100089c0c102421015041003540100e0003d6451100003420071042e1540700340c100e90b80c1c5080081e041325400311412014031303808903214250f40c0580d030108a12518016150040c1e010804103003070b9801400000516802d58000d00740c11001207020510007544d0b01c0c6101220102900140a46501444440c1d801980c4400800945113000030003562428181b08402c5010144203507480c0c014466000041080d1014009540d9008000040406d003082241c041d50310b1490040c19460b1400c0074001c950020360001c204d14991100031018500400d1032100e0700e030600035100070044498406118807419001c0d4103c0000300146400c3c900c1c0d050210340c9000700c1c8074601710500244241e81719000c1d00c00307030194003444040d07020061800391a40d5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 478690872 1250 478689622 478689641
    0x1005030a0b121b1c03120b0d08040b0c1c0c031103070501020f0a02010c050702180a0605101205013c05030106030c06020c0108070801170709050c040806010e04080d0b0103 75
    0x107001d0f65910341560315403503440000d0b40ca026102c0303101c900521004a901101203010080001e80e1014010202c1103580d0030025000f0001041240000459078803001c0a522070b902c0b4840d2040007045811014005222035128041c01044d041101c44840c0402003a4500c0071400505110003c00301c42548401081507942e5964041d00840d56030504003600d4205401c03103940c5000660070030507000340c018802c13815295181e50151060303581d100210260f16200e00c0040c8030180700c0b0b81d1068001502d80e5502140c035401401c82e12540c0045417441f07550010b5a405030000c4030a5581010302e1400000d03502801c00640c00a41c100000719250804079031350041da141d04c007035403660a007d404418000c00324560411a81c036602220007941440006481155045400c1000f00d4002d9004201c000302461154030850300800584030200d445003600c0040380d400359200e91400070081414440d9480401a1502500740d1a8645503949499034440d1071510605141b00d07951a255105010241d000c0d80198280 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 478692122 1250 478690872 478690909
    0xf060d020330030a060f0b0a020309270a150f0503070306020307120501030b0601080f070921020301062d030f0f0c0302090a050a0b0a0315090816050115051005030a0b 73
    0x4a04154080b807005c5c081e5409000307030144080000140c81040700c81210082d498540145040c04900d4040003c6000030b140c90701d11000d040c088208142c0c00c1240081d10503110036000150f42105800c8080e6105080d4102c0203180103012014402c2740e40004105086981c41030002da0b5035074070746004070381c2c50110042c24281e090925002104000440392101d00c03940c400ea0320052035580e158400c403440c0505441000100741e6200c41448420400000c9950103c2c0c0030905564220300c40d400700e42110f0499102140e42129071580125400710200800202e000c4e907402d000c0418155294020310303002e0080001e0040340e044000604002e40000408015600200026060314161030108080c080403149495158038140b15600603152003500c07081520740061a920a5410807540071000f854442001d0b540c0c03613024130030a0200444420f4610f500380c425000850009103007540d002d41c25405da0850b511942d040c20100002d140d02c44280c0c3d40c421034031807002c20300c0c1580e50302107050501441d4500f5a07 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 478693372 1250 478692122 478692127
    0x1009060b0909030a0305220f1416031b0b0307050c0109060204080f010e01051005011809090311010c020309060d0c0c050d02150f091c260f060d020330 66
    0x180b8a010001d00a4841c2c3c07a28103200595680107648044000050080c003900d1a00315004081210f40070001a0700d13102d0494500300f050b684100d140b41051000c01907040c0c0486540500402a01c8a040c01e4101e0000c3c407800c5902d0708101c60010b0303a0000400410070003d000c1340f48004044250007050166407c00c03011582c0b0780e00c65101607101d200a032600794180d070804943c2d460f111014414079206075031020b501c401c1141170034011100c0d1444000a58800e042c10000400e5034401442401503182c4079445050014008072071031800d40b130155220100b03540050105418944601048420a001941c000510b038070503000306995040070510064018880c041c01041281e0300040c8100d001060b1903407540d84c42da40d40c27030300e403000d200101c030400c0068005210030502c69080758014030749030010382840f044008500c0c245000d580040d0342c994918103940028041e2000e00307640e031640c2000d42960111819001500442e6842a4580001017080c05603c601000c0c040f05914003184503802d004040d5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 478694622 1250 478693372 478693381
    0x1005060a05070b1308030c0c210309160f050d021818010b06090f06071e0305041d15060d06030c080d0e0d030206060f12010c0f030e030901021009060b09 67
    0x38040d0304441412103a840898002c04e050103506050040000d5020210516545d180c0100c400c09404c03241408120b4401c00c3c2c5140c0108000081c690586d0302380a0405499140007400b852900c04480349602c10035a4a140500003800070403400400d64206940321101007003280701059907038542e400304003420600c80080c0319007017a07034045400c100900340d002032120201072000c20400c1c0c8074809030707260303c80091080842c035800c0001c00391004c103010300e245404d4508094800d4001ca2040320f0100c0000700009014403040088904640f078140c14022103544a01d0586500a0109d4444100b5441840c000c220424600e10300e40190020f9948a002d0031455541e4451481c3c0d43e41c0150351440102c0c041b6020040d2904090b000c412540303400d54001c11032a2a02014408410400b10a284c0c1002c42d46100040e000f409008a519000940d0b48401040741001402003c1f2000481c0402c1c0391341040044034500da90004a00514420040e80011a01024501880204425000c080d0000c00190812 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 478695872 1250 478694622 478694627
    0x803030a05070f0f0c0615030c0314011401050609041a030109030302040503060721020702010c0f08030601020f1c051305040603080a020c041401030303020a121b1205040308060105031005060a 84
    0x1c501590003a1115421030040c040b09a44180c044658000021254000403010841039004400024031030038040c101c1c55100d8235164415a02c9810513150790208141007190444244a0040d11071074070710030f0201c1541000d00140480c07161031240b5100e907444040c021021032240207140c1840074028003c000c0018146005400b07901b0030700ca581e20038003c00002517038190003005a0151170007036040c0c2480c0e010340000310760002e40101c0c42c160304004505d80307030b03030001040c1ca140c01c0625409040e94a440b4030742500028030741005440c800e02c040d04024405810641406400481c03000d81b800c20070786404140b2010b030969441940107aa0150600b4000814810140c0007480b90b41002d03400d41711405540030034042514102c1e840301841d810700400410100e8070a50240880b00f103240707040348040507401c07030080517148010710304a10500158a0b8001454002407180c1c2d8113014001c1c14000d03454591400340200c0f80050026061182c0040000d20941c60b01400501800004054075110440c00400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 478697122 1250 478695872 478695881
    0x40807060b0901270b0319080712270b1b010b030307061b0c050c040b01020a1a2e050103090309090e07060e0607152007062c0d180803030a 61
    0x34419080c000c00c13a903560f80c8045008039000750102800030001a20492240503c804d001c000941d80a00203124010000399800401c801d000210359842e5140d02d140340e006d1442c01d5469544034000c14102d81d04000214038281601d0142c030000c001d00100003850041607001d032044c1d10190b0b0385800000348800c10495142e100301601c01d030000c160341d10302148000c04d9820220122000e0f2041d44030740c44a201c1881e01d60861007603c2c0042c4103a80c0500340c40e035150000c3c5d031740b400b548950301c0009404200545a076400302c0c1140e95101004070b20111002c0740d20141e003c20b107000b410304068580308c40300d09240c0501d09002c01412020401c11a05c4400c03003442e0307100c410038002c8200084d8040c2d442d556524242c1c5c1569010b6801c0382c07030104100100c8000304020310140703203001240005821507480c0b09203460040e001c1140507030700125000d000e401f025036610b109140100b076291044010a0520040050b840343c48080354140700c4091905000d80b4030302c50100740d028000500c0000704200482525410 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 478698372 1250 478697122 478697159
    0x10506030c250b061504050603190c0f020d02030a05030a0c020a05160303020606180a150b040b0c07211202120315130630080403030203070b090114040807060b0901 72
    0x80c90003d0b882d09010456104142900351500d617030180018406468800011138004101500c1c8580102c5041883c0b07080d540c5c2c010448000caa01e840b200b01e81146c061150309400506071000c0c41c94840d1020000e4450300001d480c8051140d0b56260821595000700003034000c80fa0010111150031160910200d601840c900048006002e08030109042d8100108082c0503520100300043c0c2603518190404000c10085009114811030001c0004199030b8850090004e0f016442d40d031542c611408a00341e1801321250b004540302c101484018001d920390f01000314402e80e110910014250b40000d08034078204109440c1d034a4501c00000f8404091030149a88815103c01d0f1624030002c1031306802d00040703801c14402c000980e000b942c1509400341c021640741f01084424000520a081d4548a052007a04940c10480c0507070300c0022601c050182c1c05203410b5202d49004000d201911104884490046c07000d4401007117094082828001c00c00c95410031401080090603420980d81c0d1150300580701e241100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 478699622 1250 478698372 478698383
    0x41b06082a0d023f150415060909050603060402030a080a12050c0c2512050708030304060e12070203070315020d141503010504170a050d06060203030403030c0302070b010506030c25 79
    0xd10405a00b080b04c02044820000500441107035914072482c611603002003100140d020f65105601c20601c003420085101510190342c030344502500b0510188200e40b0f01070b001c3c502ca81c0c0002e0410006039030000321102c0d001d84c0540c84503180c075150001a00e800b07030303001080154076040c4000c103c0d00014041c05080071103086000c441004801d0360300b1a0210350941c4034040d1075812603109010f1210550fa090805902c1001114407580d9528011419070300140d85c112005901d8101894008004011951000000d400300d50721700566580045e68512451000501b0040784440001e43c201a65042d180c15000c0514140a9a5000501c030401c040c2d040b0703011440c0c990501100220b90405101e0b162207280c1c0540c190401c40342c1407130040e1aa1300030113583d0b01004410040d103c41100c4a000c0e150061040341c000b50303168107151a002c2c3c26610740e1000542010710500040c0040741c95802914112441524220f41d29150300614150900c2240003d04d1b1039912040e910741c0c084c0740b4000e41480c1c0c5001d030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 478700872 1250 478699622 478699687
    0x40f170409230709030206130305060f09010b060a02150c0903030c060a0f060b03040b04020d020604090507080c03070219050f01020c0321060d140a0605041b06082a0d02 74
    0x18020b40d001560000005215940300b400181070010041c41c004000b80d20051a1030740e280d95541c40e040049a40d014040040024440540424098140c1c0c60300f048800c541080c2218030000d40d585011065803200d401c2c400c000c58030030188002151980c1c1d5014082d607030b4612912503025510340080d502103d88a01c1e001c1144041da01c0c82c800c4405a91540c81e040f0b01c0d684907030f201e0b0344c41e40101500a0740d0210800b05000010385d59040100014141d807900450a071910002c090401c48d00205010880c400410400c040b440d0f002c100c40e601040101034024030071820f82401864418000c0c0d00f165070b5817000802d0362480e00c002002d0200b0609841c0d6070007010303160702e0344240d804005440950b0403103441c40f07140c80000c44a8020002080445084944800081d1228015a80c080e5003d54003c680c40195405240310381030a600504098217206040341000c0300d11074040d103101d211403003100200c0341103000304601c608104c90021b200100d0039921200c1182e03018510b41c6501d04041114120f8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 478702122 1250 478700872 478700921
    0xf03060c0e0603010b0711031e240606161b0602010605031b010f0f0516030512090106060f120e060c030105190f0314010209120d020f0105010e040f170409 68
    0x900f241e040e1549804c0e01c509040b82540c80b00c0903c010401580d915004601f50481316011501180c510070241400404155504901800348281481c440040c245c05000402406031a0b520849528903201104140200201c0c10100d4850302002182030281c00250707400036140d13a05401c00404c1c2d50003101030f5100c2c400314400000c01e2011004040b40400c402c4140c8045082c003034400f0030740d4003195003040743c6820f000b191826514a19140201c0124001050702d0500011441e401540b14000a00810030170303013808000741003146d20366031034030410030702400c5d100c0155055080580d80c084e0940403140d980c1090140f20500d60024000c09010b8100200d030f149003107503c682c400c000c81c0c41030803000e50342509640f501d1034010b84102d065a85503408114a030f400342c880c68280c1185454690103094983e0014000906206030b08039681c016a05280060001441d216142508940c1c0010047c01d0000c89141045110080d641002000c0700301050000d0101c050350045182d10215400d2200d80094 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 478703372 1250 478702122 478702129
    0x140309040b030c0307060f09120303020a0305060f0a170c030a061a061c0c170403030621051207020f090c1207170406090501321b19090f03060c0e 64
    0x44100d2a04e80c95400f9903810131850303000d0610101c0c01020b43c0b40c9075980586503d10b490014000d14030880000340c0c00a1000c031301ca641885100d070018030840307030403000d00c10000c0000d0390410300d4000e0f110029419400305204540802000c41c0e81840501030782d043c81041e042c03220041503d078801c410000f0440e01040c12601d072803411105e80d140410705002c45003040b0800640140700c0d04403540140000350700010040000c03003140700d20075407080e500410320a082c144000e52441d1941d920b40007040986560700700181011540e5611181c0641819440381c035140006000e00020602854002000b01c0c03c1c044140380000041c50260f01c2c591030200c107502d40c07a0f0116150000d02d070341103184281200201d03001482c5900444881402a800404c001c0079403c4151018804072502480d9480d4100c00700b40d044000c100307603a03404800441c08035252014015003c030144114580c09442d0030b400c1041c40012400340301210060074202c4032902c500c681301d1500e40010300000301070302c0104180c1800d1290a24 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 478704622 1250 478703372 478703383
    0x6080601090501140d1b090f0b010f0207060c0803060a05122107021f0225030606140d020909150a020d0b040c09060c0302031216080c070804140409140309040b03 71
    0x244c015203070419585950311540c242050521007a80e0480e81c0a0000a16100c41e008852000c442c0c074a001038442c10100000d00507da805902c003055402c04441084030702e821074420030040790000d822544c0c035030312200080c2d24041550030090303001d2000601e0202403140050005044240010307400c15181d542d1601042a0091000c000d500c0340d40f1682c1e440320fa0816a0310000c41d2280d900454011b404d20313500d269441d8901c8010880c41e150560020414052540520302c0240540d80c5240c0707640112801185c000d45421070040e01030b1184102003003002c01d080000100303003c43c0074000c18080c10440e0f08100654017059064480300c0c20720529202500d840e201d034014800084d01c51403443d0b450942d00307a45120a50100b502507005c240b1204210100f6513189600c5140b4600141d46180607680c005495504080e2018a4080e0148000000070350140c040b20251060b040d000a443c151400002c0e015001e100030003807100b541d03014401d806880000c040c000c1e6400442d024041a81440213141d80d81 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 478705872 1250 478704622 478704659
    0xb0a020702060f0702060910020c01170103050303010608061f02071409060307030605130b0408070302160e0a1d1b03060106031103060d0201090e090601031e081b0c0406080601090501 80
    0x20307420031040040300303c803a0051814900c042c090f2801d009080c00080d015800d04003038100541c022408025480d81c1c03182a910b220804140c40c00c0d81541141c8907569070740014040c038014403c41d000881c81316034885400445440078144100c44070f088010b8003d44a131018803030b401c00ea08410044503590301d0a0f68690380b10707170000380c0180001e52554540e000138000242a800e140314100000c00007048924001c184175500a4120695600251500030714160310283c095034245040b400501c0403510002d803150f002489a80301203208500d080310540e07284508030390b0800c030740f1800e0800d40954980c14141d034620030084041d0f03049031f03a0b240000d4055682205a048080c1c8040002031000d02e03003154180c0c64940103142800b0415282d90b41c0c580318400a41c0c03c0b002d20740c0824010020400410720345044c0c82200810003c64010030f039510071150203003090120414410309205000d0071410844a40614170042c418090580e5609600361240028091980b1440c2490700108948036411901c2521 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 478707122 1250 478705872 478705879
    0xf09051914030a1d060906120c0d0e030714030c06010308070512030108010e0d0e0a0b0304170703111903052a070902040906050607020105120c0c0d030b011107240c0f0305070b0a020702 81
    0x901a06108d203042040e0010144448418207000c10b40c0d481c1a6881031000401c0c60000a55890182d42403802141300d0003490032200d68000c0100050705034000c10143c0c11298400482c984039105468007508200c040828025030342008400010302c01015080750412a0001c025101034524200f0304441100152078002c0d0405203459041068450b03800c021580b1601400c6007103450920031100b0719043d40602c07410380015520300c507a82c4145d201400000000c038001c00f807490340100369580241550181d159a01a46e82c0c02040d0440f2905000d0a050b20f2520480c0542e5078071510f81000304001d4003d40144501540740080108007414507500310b41007030b40c0584075141401801821124140c400900700c00e9420b005002d00302c1c5101041054403d100ca090b203002c6118142e100006101c484942c2440c0032030f034060141003001005d602c140310b010340e444614a02c120115410251200741c10250024250170041440009060713101c4060300c4c280d40f00f0320201c0c0c4a81c0760101d0040a0380603000b4042d51 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 478708372 1250 478707122 478707127
    0xe0f0103030e151209030325080f13060e0d12020c031909030b070905150a080a0f14010f142704060f1401090f09051914030a1d060906 59
    0xd6525040700107081c280d81401d0158a00b400403e011301074030f001510b2003501c9030b20210034003180e540d05071900e588079201a00e8000031500074110050180d0000b400c400c04421005001c1758841d60341070142c09826400c0a8240580000f062480d40d42c1c0245041c1d00002a0941800382980c1c407403402201e0a8141c080015070900c2c0301c00c0340f1b01603203004501425061185600c030020000e042d4000d1700344200a0340e15400001c3e45018240202860040101001305908001418009400c90952034002915010010b200307100e01e407038400141840707110b002d03084d941c0c100000ba940680c03588440c144c0d0a14950407030b12501c0401400020383d04181c148903680c1075068064480f8001c01020b541c00341c001c0340b000c01e601110843d56400c42c1c40034200202940c80100c0148000b03550341c0100303c9840051407003049000d1450302c482d41c4038420b04421118010303030320300c1d03a200b44101040160b6002907118280c035555030200300d010b0f000e61400143c582180890500c90401c5140200c2070351014207000d443c552 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 478709622 1250 478708372 478708397
    0x207030f14090f10051e04050109050f06120a060815060a0602010501030503070308040503090405070c02191a09030a0219030c080a0308010b0c01060f08070e06040b300102070c0e0f010303 82
    0x1c03841104c141c040140a000000c410207a001c0001805941800d88940d15030a0a00042c101140e681049000c1c3c0595500842c02d521102d0485000103408088181c040d1101b8000c100506115402003e040c8a1000000c10200c002c04c1140d0066004076201d04090755209030603400c1c0d039001d10019016410910201010034010100641e106d071007038060b00d2601c40280300007000c5500c00e9841d0800580801000d2085003000c44904000c008443d0110030245d28240141d0b501c40d0041d507101745a65000715805003161000c0004040c5954020255080740d42e0440c100c07401040244000c2e5011004000000307406003002c50707150620b81c5c15a5400c8416803c110500034254018a01c40350650b41c0c49000003500a000c0d1b404c0300c060304002c40600340c080e01d41210699040c4025002030301c22403400ca2030000301e5a40e07100000e94584a03003a4061002102c00e8400342026401840c1404c81d400060400100086950340c00c0903202e6004a66007542c4031030380d81c0d81c1620403d01009001c19101060b40 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 478710872 1250 478709622 478709629
    0xc1805060307030c0522140708090c0a05040906020f070602070506070e090c090f0916110f07090507021603150608030a120b0a090f020909070f1b0c08010207030f14090f 74
    0x1164100d401d40480c0c6d0440702c18200302022101840304100c081c51a003018030090302e40c407014064106100b400240700742c040c4e090000302c5040c55846018440c2ea69a01d10b401008508d405448240310911310040c1c86103194103001c40658040c84e012034580c01303030500080c0940c0c020f5200206d03040015001e8040740da580c55081806601411410383c1c4520149680d10099945d030700da0710720032902d003166210b6010607403601034041c1c0403042240b00c081c2c0011454402c14500040c42e08101c4603124008a225202c00006a08000d402e9540400f00c0c400324601105100002c00d460a0540c2840b90401445a980b08107940703a01034140a00002250040601007400158215000c0d05400030300300e4820301d03500c001090882c3c0f183c00300c0e0a401d82e00801d0900651610761b8032964481c000f420148480c43c40e1207001041307091a81140b031080c5481e1444002408600c8400c080a080001c0c000c5545840c1410b014048645145409000aa0b40040a4080ca80380781c11381b080803c016040701c0354184101c041 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 478712122 1250 478710872 478710889
    0x5030d09060c06140411041d1c1403090706080f1e06150705060a0c11030d180204090b0a1a030d030e0a020303030117060f0705030c03130c1805060307030c05 69
    0x161079590304c41500702000311304104e61900903403007104076140d50340105d0184002d885150b4082c16100d101d11248441a000100d281128000750304a03803103881407469010b8903480c40315840d50246410200401945d4640001d683c0b045d03400c503441d2703002d582d0342c0da0445480040080f9052005403400d400707042c4074030021440440d08203100425200100c00a44000741264200c10400d40d000d911410511401c90307a94400c142820010340340c0701d22010550343d5000e50764400d400515090554501c4414001c0344d00c5071840c107003254003c1041c8450b00c414101301c2101401540c112045a1409504140040201810403071003100500070f450803088140c03040e0002e201c1210142e03418001c03504128016902071001750301a00615481e12a07510040a000c1e1070040020458814191504144542c40d134201080d039600071804005e640d80c0e590703503040448401224610007032205c1c802401c04200f00c0038965070314400b462501c01c200951303a541c4041643d41c080a110150004003c10028401400c00991 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 478713372 1250 478712122 478712147
    0x41203050d270b010e0108150403140d02070614010501120c0e040e01020403120212070f0201050d05010305031e070c030b1312020604020f040b0f21010509031305030d0906 75
    0x1000402e501080100c00221a0301070084880e10081d8051104010b0382441280c050160681d10149560400d08a503564240c000d803000c0c02030304000005402c2600c91022525520310305a10140c80b05244100c1a02070f4000302c10403580c450074000d40001c61000c081c240c504a44050b55074030300c4040e13072015000007441c81722000c6c0c0030011049010030307c2c3e407210b00412001130b0107a00010381d00c51031070030700d8240c1c1d1441c02d029501315080710400d0b102c18600802a50b908035000110103c4c2c0307103420720040c2d64500c581c1c921000322908101c0004140440803010b04880303c1000c1e082495000000075034643c9100b00e40c00100600312083c1d050000c20400800c5a13884040b07a0300701c013138690f0242c4481c806081003a0341440142d00a408100450420b9044401110300c1601c0500000e40030b1400a440740700702d40e11150040070b400b0380c28811080341c070300f50000c140c1d800d0000f00100e05144c0803268980e444a00713414041d400d15100004c2d6403c002807006c005039080d03941e910015042507811211481c0c07101 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 478714622 1250 478713372 478713397
    0x50703020409090503070c1505071104020721020c0a0617090c131a0103020301140d030e0d05151807180b0915090a1802150c060c0a03060b04120305 65
    0x1c80400c000b00030b80b01d01d00d600c60094004540300e801c0c524200711b0f00900e50304400520040840c0180790990007100f41d0340500c0e8030048000411444030040303030003401006000b07012b101d801c6074908c0c410340c1003903080360325204140e0956203806c0980d0184500944241b08000004082c141d11680c60000307060314a4200c1d50040503109201603c00004421a02610410202e075581c0d112244131280b8078284060889002c0c201542150315011505540302000007070340c1e000f410041c0000e02054420b0201d82902e41000740540c8188986040c025959101d0000d050312081c1142c01041c4012800344420102140c180300401e00075040c01700103d0081d84800d003500110b074566940e95026610100c03101d01c04c110701c5a09140748401c0008100e40c58002034802e110315407900e07019810440150590f41c40c5a6019244e250030318008800c2040c6510915071062002c1c060f90051241d01c0340203500410380e4003030b155414007140d070f200c2d2a00c81291289103c3e0a4070381a0352511600081d0140020300594113030750 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 478715872 1250 478714622 478714627
    0x105160f050304060806010305060d15060902030114090a090b041211030a1e182d0608040201080a0c08010e06130509070504180c0603110c0a080307030c020c100305070302 75
    0x3039455480554462004580c141c00204007030242a030b00030340c0c042d0b01070000d19003440603081000205400c1011b00780058100d4001c1c0140d070704444200e4120b1802000752250856403076944179072499000080241241c800c200c5c4001180e05c40c081c41c001c580c43d0396003104501603591542c0d03071120341c1788603182c4806050010b04689124416014405401850480d031a0320001a258400361350072120340303103607120900407600c0b100640c1020301c1749150142c9501c00090142c21081c010410ba59203074032441c08a0400c80e01d400071030507a6001c00a940580e01c00c2c0c81d051119116000407e040e50000c10000740042d224400401954600382c0606400c40005403000e80a004030a00c1d40c4c0c280d42080f5501c82c016480707504100103600742803190f1040304c422600f0b40c845218082e0381d03140c2112440e01c602000c068a61409911a503203032030844158034010811940408000d182945194000b1159600402e01d0700c40341e19803113400455105280c400040a070b094400c2c1d82030341074006000142400e030426500703 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 478717122 1250 478715872 478715917
    0x16020a0615050a0503190303020a0e120304030c0b030417030402040902040c1107270e010612060902090604060b12070519050301030b100810022101030b0406110a0c020105 75
    0xc62207a03850580c1c1015001e0042800d120902000b99a01e03072144c0d0203903004014030303d0184013000c201c4c80c2650385841d01580d41c00424604840502d1a01d034680c3d4002165110100e03c030b880000104100c07885040305003402a80ca0b8040c18190208450180140c0d4420801c0c11480840708002d5502500c0107000041c00301154000c01c0c100d03000c800039000400c65001000c8100d050402480d8000c15925507058138280e40440042200f03140101400b00c030a131924181c0003d04001e4024001424501c0b4030130342c4000b9141080000303050305643c01c4c1c1c00758180001054190900380141c0c019038003a401014945003c02080300c500000c01040a4104041400100c0100f02d811841c9200f10030240d40740ca8595040d4101000c0502000d068800300c072070006c208010905000c030b07000c1c0c0c40004103403006840c4c01b54070039500082922001d150124074400341c0040208000c82c41014062030003076504008400444200100e1403080d01100c3c40030801c0c0702c00c1c0e07500541c0304100610701d500c407880503101c0c140c52 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 478718372 1250 478717122 478717133
    0x3010312050d0f0501140109080d020c0103052706161701031b03060204080109030e09040210121b0906020f010506061812011802010f080c0304080c0f100b010905010c0b16020a 77
    0x90a030405022420000b40706d410940e400150540035201e840702a0106400001001c3d6803810290f000d80e0506440340000384904194000c403014134002ca03121b1040759034290703808ada112141142c801c5000b0001c1100c0c0c2504c03511a080011b030003450b600f4440807590940d22003240880c40c580d0704031505ca0bc50240440000e80900240008203030b50400410070744040d250160040360213a0031726001b10504000c000c090b9031100800d0491090303908040c0b1611a0800c1c00c0d0300035040a0035400e00c0e8030034002c0320404030b40d030141c005030448050f0350030398a04c14681c104031070030385006403580b0364080010b0051000114180075000340322040200151003241e0410200d83c2591161a1980c01d02404000a0b00a550700400ca5a003000345900e440300007131406400394811800040c101500380080410220813200040002d011107011502c104c6540c0d000c0c90000001500c20a2880750000d039040b034000403954040d2882140035030b8040020181030352110716031410350003250940cd0451041c8003000d004500f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 478719622 1250 478718372 478718381
    0x80f01060503060f06010c03142116030e0304090b011803300e2b060b0f06040806070c020d0b191b020c060d110307120501060807020c0409060b030d020f0f0303010312050d0f 76
    0x1983c003002b000c00346407a03003440d401601030380d42500c24141004041c2d041c6e610040102e5095420340080080d4046290b0012207405580001070100c000003100c011040c007482485020f804c50b0707030031701402c414860f10001e800c118084c000e890303001c00c8214046020911f414110070081400c4046110805680c001251420404d500800c0d541a81d03211103000041c10144400f100019040e103459207080e1074101d2003503844800400c40410041902071007811592a80402003486810810740901800c1821b02c4030f4800003c103400b110081d1501c21025090550080c1400c40354240d600504001480c44090002c0c070b5000000341d0345016a142c40a40002501a0155014040035911580d80042d1040742c4002c440301a080350382441000c00400c454598001004030320325005a80100c1c0c00150391078100007601903003056aa041c000c603104003500941c0092004050144801141c41202812611039100e201c28000070b41500c0c2407181d0103850b50b019034028414000142c900042c0d100100362440201c6 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 478720872 1250 478719622 478719667
    0x1c0e0d060501090e0307051902010302090406030b060f041a0105090a0b030702071409060d02040e0f01020d0c0201060510050909150301110a0e100e19080f01060503060f06010c0314 79
    0xc55844005200d0540a44115129440904021403526107281c91307507583e0b121021041050303920413000d03440469100c3c0c0c05803004d03102c0107001031107981c0e00c17898020340041c0219030180c0240422001f44202e03140c00e001b081c902000c811641070b102ca0200004550691010b0794450300a07081420010ba05d1100600442c451542c503400703000c0150030300050b035400010280c0c009210350405001e0080680c1e4051104448176412600010090613140c821070070715802c0011100503510101e40192070021540000c040500d403a0700070018940c44408121010380075254100008409105007950382c1000c0b442c00307400c40000504e0500861084001a003550200e446428440c0404903205c00050740101340c1c250184021212010050003c00e0001e0080b8881ca003202c5c404c43c1201b4170102000f62038030290014040e540107586184505250160190225108590007132285c2e00c005941c20703001100ca03074050203050756503100002e86520101e815030f03102d04101c408504100b0000f08507289629a40c00302c03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 478722122 1250 478720872 478720883
    0x11106040b0702070801150b071407060e0112020412030503040f06060305030a03060e060904061a030303010f150c08091e0306070f090b0c030d02031018020c010c0e031c0e0d 76
    0x41c2c80c01d10402810501c507a805243d090303041140e0520312091310456401940c40100c2c1c201d40710049400c1031100e007102820110007074018060b000c40d1060340607401d08943c80081e00e55207d2284001a402c00702d119034450640d9075113803460100c002900c500c000715001401100440074020140e21458200e0f60f00d54070844107580000b0b520102240c140c082c080082810002d081d05510b0040c0108045180040c0024080ca50350542440c5401c0c0309003117120008805002c0300d80701c0da1038604020550a283c058800720504038480c0844a52003684a500c50360380c000d0480e400d120000c000c1c02000c03074010b2042c0d511690345102e08041c0d41c8081081620071006c1d503440722080a1040c1e03004e0105000d03500550310b2240308105820402500001300d03031401d034a00800517907a03910010318000608040c0c20003002c805485002640101068010f0300704a41404001c11003401d000c0801e0383c1c081d9040da00c0b02e405401030746500c1d00201c10300c204400c110030207040c45041c0c03041c91340003c0c104800c0c1c0f4604562 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 478723372 1250 478722122 478722143
    0xa151107051501081203060108041b0b0f04050f060f0d110f1204020112060f3311010501051c02090402010c05250b0306030a120905042904150b0901110604 68
    0x8a9002000058400b040c07822040d0710f9403c11a00080101c10010009006076844540e4202c501a01d0b84038be0005054100440d500d6030145e546d094150740c0240f25807031280003101c3c20400b1502e007090071510980b50400c80c0c2442d003112145440060010441c0c5040c2c0750a0502c08800b92524080040c0444100e00800043c02c3c40c0030310024000c40c20501343d14800c2484c00c0c6003448110324001d58072007a1041101140112000c004200401c410145030142a0f5074074132910300c24082d0011944410076401034003d100c1030f0303210fa0500042d50920021201401c083e400c101c800340c2420303126160002d0043c580700c8001001510390900d070440040508801c1d544031241142c03011580a059005040f60380425895800d1020000f0b0390340c0c4465101900d103280d0311311a500460b00504002d0000d00014105100040c054502c402031a91014201042101e14245106107454030784900c031002284038841d450300700d04200000285420082403941803011600250705401c4040142a1055104500910 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 478724622 1250 478723372 478723379
    0x321090a08040f05124303230c030a0f02010c051501150c02060f03061f020105011a0a02101a06190201060b0703171b120a0e0a151107051501 62
    0x83c00c0700c4c0b5804a20150340203038003161000842e20030f026040c3c40c07090000321b80381e105032021200300440d81c00000401d5204c4080010400025581e505041644100091003541c441c044407a01e50407c2100346a050708483d10300c000041c44402d000700d4050041c98003000c001007036074610345028010401c440c10030341060010800e518050f071001b0814103441c80e2510460f891540455a58082e0400c1040500780100000d070aa031100c010941c5110a602c0240d50004640c140c080e000740020701420300364001d803413920400b40342e110342200d440c00f5165000b001e62440c410001c000601e10124a106214101e0b41d00020a50f2608060f052681188150b15031000940700c01900711807990344040f0810000388500c1000c03903044120b0f030b02a00b100300401582591055144203d0940044066003030700000300309544e030340a2054203c2d114600a9030204010701e1018951941c2d50400003000b095000c0e03500e00c140c00500d10f9040204100000c00410b410b00b61265909803e0a0392010031f07141d140104030041 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 478725872 1250 478724622 478724629
    0x3f02030f010903050706050c090607080a02010f09020102031c021318060501020601030b0a0207060204050d1101080c090a090b0a0f12030e0901210201020a0209070c11030321090a08040f05 82
    0x4160200d49400801c1660402d50340504540112400940b145594400242480c81c0941c1151180c1c00300504450707941e0781d945441550758101f0030000d00158600101b0080b41c001610550032025016002582005100b141c0390968194060040c0003980c2c0a10141032100344505800c0c0151038211004100c0c0124040c400d003c03a00709a111038119440700340100089102c40401d1f41c4c10118440c000b50740ca21042c201300700a8031803a1310090700404090202c10601c0a5240d0084880d80260303035010342078442c0040042c050042010065202c3d42426081210ba0032a6101d00c01c848009442c0d0300d08241e40d43c061005c01c000540c04081400c074000206410164003000c8640b0480007142e46520950603d0308607440001c00340c0410081c0c0703105003a05015a8020800302a00c0d541c014902c00c00b500c2c0200004202c0b10700803408036100c1d0900240d205aa02d00401a200154030804c020f54404110701c03400514400042c040031918043c07000440c0104078040c0c02400a00719100c00c0007040e81c0781400380b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 478727122 1250 478725872 478725883
    0x12010b100c03022407050a09051302040801050907050108060d1703040b0906130f12030f0f0e150408071b1a0414010c02032505040912020f03040f3f0203 67
    0x1301070449401481c1d80f41e00301c2160396400101620700913417640071491082d98550030540010364400c0c1180b2072580503441c07a0b0000c1c0309840914009101903224907041640c1d13a0b94900405000c11031110014120f400d011401101c454010031000c000d62100b402520f49540c01544c055882014040822001600400840d6084411000b045103e40c100342c40d18084200c51010003402c00c101070307600b0041c103482500300301000088100c3c200302c06504681441c004258445070b15000b40030301107884014015a50300d6a06c1150000c00d51850031442d80d403030b0850100102c600e003007403508000000c00c21521650b000d002c1d540325540b04695844c00d20f0000300120134260b801e207040003003520a000043e01c0119840402058052450040700340505040350340194641045422a02d880c40c0b6005100402c0c910007030803025602510211444a107459442e441030f4007481030351840c108001c001000034802c01c941403000b185403000507130382420015040154403510303810506844898503000d40c9424003d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 478728372 1250 478727122 478727143
    0x13020907020708071203030e01180501050c0a05030a110403050a030801231e03121314040e151f140a050a140607060209030d1812030e12010b100c0302 66
    0x6240c00c5280c2000b0b0f5030303990240e00842000c500c8a503100d508050283e002480d00c03c010070700910142440e1454445000c031110801d82c0c0540c01c290103d4040d0b10311500b03d890204183d82c0315403840d031f1000d003084083c104050303040400e4001000000702144c005e01c103400c3d80c0c0341300e503071641c1d42e40d4508052101400e00210f441c90820340c86019421480c2c1d0f5a15a00c807000c4d050210040b50740440c035001074204918580001c3c080d41e030005280c3d0003030888043c1d00c5c00740d46c407032103450b59407412500621081310500d1080700050380c00b80303403401e1648180c1940103500c804608407120101d8800303170344200c014500380c1c0411030702d0381401c0701102c0929005041c0000740c030717007610017000b5107182040040c42080d540d1621409030400080d070105200352034040300d02944015048030108102090010700c45040781640382620f0003032001c0031030a00703590f92811300095056528aa05c181c009020040d050604294050a56581d0759004c0c440b0780342c0455410111071f954944010314803213420040d0604040c0c50 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 478729622 1250 478728372 478728377
    0x4090f0b09040b1503030316080f070905090a1107120e181b09040203100510090b030c090103090b04150b0105130b09220504060609020306100318020913020907 70
    0x6591001c0d100d4042855000b50000425405070300c4401d03030301c1d155102d03c0420303d805020010800200501c031012260026502c0c1d560031443e56554240701070058000e498020018840702d000708804d1805054031500440c07040300008204038410121a03580c1d000d504110360340065441e070540010340081811901c3d8000780c800c0542508541c160000f2440004c01030510042500c0d06e5210001003901071342c1c9414400303842190340741400205602d8440041c41341c03520074041c9042010b2518840d440000440700145046421911041d0400c3c032142c1040010504141ea82c50500d0007240407081421300540c01888003005100311240d4000a6424103c5a10305000c420004014032103044500710301122207501c00c044c0c03141c0c0200700090302101d10201845c061208090400f40f0302a503940083d0280d0f1160f0b900700300c525665101c04081e0702080394000d9010200e0b610302c1d041e1030300035000415040749c0066081a160010303070000d0500c44041d40c586c01d4080001000c0421030a184904980010060 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 478730872 1250 478729622 478729631
    0x3020a080613061104080f010f0b0105070305040323010c0e1c110402071a040b090c04230a020408010603050610050d020a030809030102070c080f060a020301051003020702030c090c04090f 82
    0xc0c2c404980b094501c0010126a5140d502c001d0380300d080b00507200540703449419101e002c20081c40143c081c00c0c05c010034240a80c900f808060456000304c08a0b01c503190716031219420706d483d51305d800390f07180b4940c403e030321000d1002d0003906501030003131042ca80174a009440d5007560700a4101031101000c0748074843c000e81084088000041402c4055009800c8030448001d0f1f56403d5518049502c100c6c08106442218454010301c01002002c40b460b078490040700c81150401030b213443c02c00003039a8017215201581801201180b142100440705954000e88900025280c550b4890350a42110941e80c000d423416000035082c0314400101d64440c400814080354444140151074002569480c15480028a5030070006500001602c00390155071003550024504c0340c03090340e51809180c5136540010981014000c40c1c00140c0d42c0e03d158401e4a060f84c1001d0a1800d101e10a00d100341d0080d031004006a81c98400c00d03034803081c0c540c5d8240d0082d10444c0300822142d152450b0a00600c00d07560030b840200040c9082 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 478732122 1250 478730872 478730881
    0x3020f0c030703060e1905030304120e090f1027051e0f07140304030806010806030105040c0521011b090b0c0c010e1306031217100306050403170a0603020a0806 70
    0x3603020603070303400c040b000905c00102e0540a180c0f5544000030000490200d000c0d6003804070100103148070702c0c01903d0f18510a2800da40468080d00380c4003409038001d148101055074540107004d40ca51024048861107066030b01c3d900451504200411040c40000c4854840410799141d402102d03005400300c04007814255076441c4200402034010000010400203030000782d460b51143d1909212880f00840250707490400e42801004080c0440700325020514500120b680b508052003070b1071103150400350b840400c42c100300801c60410b505c0c060000d80e040c0d905400112011080c45841440c0c0c800700c010180c140c811481c00f500c41e40d0540d001484c0700c0414071074402003050204e0040c48407482444c120081d1040c035800101d10038622820301125500d040004001c0080502d8116049005030315001602030368240705005c0d0b034408495480c00c05d000280308000096031a00a241c20a200b030422564420b01024180500f03001182d104e00c280307451f02420415820801e048001910311a006000c442c0ba1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 478733372 1250 478732122 478732129
    0x31905032109060a0e07031a01150c0c0506180603010e0609060108090c09060607120206070e04020c03040e13020d051006090636090c0510050c1009020d02060406020a03020f0c 77
    0xf001000c00d41e5064036104801081c0e841808600c1c040c5a0205040e0142143c8140300c81e00882c09004100c200b69040e112906114010308400e04055801242505000d00b48810300100760059a54505c0c402c9075000d81c080155a140061030203807501182c4d81d451032401c40204068200007410303403810304c9110014042d080d0000b0800803040e280a80b03074282281ca9040124205201d81003018120418031040c1e00d050f1b0b0b502181c218041c0d5100e0750750b00441001c0408200892082c0180090507501c2000200050598100b00d2940110744c100080102e4030190085040e400030312000302c54640008042041d28040b5120341d5002d4a04c5441c1007020a00702540b032110410b460400c1e4030b26001c91500d00413280030400c60017070b61110103401030000480d00d144c40e50206009004051140355401c040c004603a2060050300d084404090043c40c03c0b81c89c80c0304500c001e015031030b42030344c2258003c065800981c07103401c010300080601f603000701060480d60900906200400400340002c0d0400317141c42d1007998 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 478734622 1250 478733372 478733383
    0x60301110310030f1502043804030609080706090c090c020d0806010503040f140c040b06030717100e0117061005060f0d14010b120a2702031905032109 66
    0x20344c40500c981c003150103402c1920301c1240050890031078900028011505071074220401c43c140707120f01982c41c910542c0f14490040c44500380c4c0b070058100b0041c44100302081240e0090620f0500440055181000d19160030003501c40300c04050328180502c290030042055944500001160984003825039040c01120091003084040e0100d4100a8044081020b1050f510700034021a03034410030054400c503509124640f19103000040345d104d18131b018484000d0b030600b60701702d81c03040400b0303a150540c800710a40c0e131500203000541040d4611031401c801080207018420100e000c0c0201642e4410250483c2007100d2401c28000c10303040960954280c104229200c04040e034040c081c0c103d080c640c031020b420060704010041c0001800110441d1000001c00003c141c0c0184140140d809007084203580e44c00070001681c04600d01c81c1c040c0070304202c5010030b42c2c0c01c150b01800d003e44001c041c1c9502408500709485000c0c02c000e410f4070300c5c0d080080e0005032040318003140c002d400006c0740d24101500c0c103015200d0f1070303c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 478735872 1250 478734622 478734629
    0x524030a020d1407030e0c0a0e0714160c0504061706190b22060e010e070521190612021305090705032a040204030203030d0c26060301110310 62
    0x354000c1016080d406040c0c00454010241440f050020b00c0c01c08001809450003032010a42c0340034003641c1400505011680c48151029401030002035100c8940c1191641480540800c3e01181401000c4003c0380410310894442d00804c5807107038541c01e04c01000111a801c1d4080841103083d0490b4540d2140c2c0898515032200289074000c01210003a42640003501d0741070170b42d65100c0c120544120b07091800441c0640745a04412003001346c103844604032400c0030400e0140d004042c1c5142c0004100c94814001440c240302c900c0d0240240e030000c0000048aa40c2c00d484040041d000019229091000c2b442454010100c00c540024013076100d401080084402e16041100162540c0020320103101c10003501000f8240902140d00c540d0f4116802c0280a03d0074020142802e0301c1100ca04a41c80e0034000e540540b90014040d62400340f40380e004000911500d6816800c0c040703028000313419111b030511000e101c220b11154a40c03007442d1600400d030840714480107501c41c958003071051202c0d040303180d04a070080d0b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 478737122 1250 478735872 478735891
    0x7050f030a030804080c031621020a0f02010309060608010b040c0311090105160503040b13050d080f2a070503160608060d060e011107060b0d122102070507052403 71
    0x10358803942007981580c42501e03d00002c1e0320000400c0d03a034030b05108c4a8401564000c0c0c0d0b082d404101032988411000030040e1b8000c0040e40100809800300b0382000d442052503205041c005601801070307440d40d05503a501e83c04108113075502d0044107024107040c000c0c42c40c2c5016078a820851030f03001144c003181074000c10107603904019010030f88060904002d05007182082e00841140d032110364401000783c145d88149000c4c9a940c50301b8100240500301301c042d1039082640541c506080c071148104140d82500800400500360f1904071880b1032104402104040d0596502c000e0b0001c14105010f141c07814401201010700080168820800c2c7d561040340c0381e4011100300c0d03000030045800d0030080040c0c41071406101c903a51130060800110701e013581c0100003862090100f80001e50b1404108050782d50100c00103800483c2e00c511564403107200c4c080c1480780c0f80d200f29032100088100c6072060100d80000508817811741c407030202072199284c24a0814200aa003180c13108418014040c0e181c6217000c081c02031f410 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 478738372 1250 478737122 478737137
    0x309120e0105090303040e010512161503020d06031101020f1902060f0c03160c1d0601030203061206090106060201050907061d0607060f0c0809010b01020703020909070e0a0506010207050f030a03 85
    0x1030307038840c0080b00c4070030500404070307a122600c4924803140c00c042031240301d1141c2c02c101c50781e0036680000300d9251802541c521045813058035115a03024501c68104e00f0781c08140c4d0801c003001d800200ca108020140d405024504001c450140000e4542001c404110b5100d030703c0f82c00760001d40c004100c0303a10b0700309d64144c0b485621074032084107082c05801550308510190001042c1550716042230703100301d4802c2c1e0050901601080c0d40b039031041d11420045146916034080c0c4070001c0c000794080c0e0015a00309401410003c038000b500b0203035500384841910100000e94417801d040003071580c240200342c0c1161600000c0c162007440d1132000381c205542d103101c0060020305094144040d95441d8195096150440c000f84030000740070700c030031004064051400000c01c00b11404900c910005206006c0700030010b80090807081c1c00e6808110809000621a40c1944641c000100703103c04890901c03030054401660104081c10401d0019040c01c00941141c3c1c00b030900700039a034801d50b60024400da01250141086038 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 478739622 1250 478738372 478738397
    0x3121906030b1f0b0c0303060103060f030305030612100c03021c050f04030f03021204030509030105151305090c030a12020c060a12020a200a030e12060402011215140907030912 77
    0xb080440150f01a4030612000728901700200000700003544551000d070303000c100f155140c40c640f20843c150703408040c000034001c1c80092503e0900d100b060051000c3e520485492a00d02c0300c14009407812004184002500411503240b200d100c0480207103d160881c1d010701462a00c607003909801c600c01800581000404030908412900035412075549000b0040c0c0703d1142d24141c10702600360b60040c13110030702941c80c02000070b24210341c00ba07000404c03a00003800c12038460841103c04001c2e020240c01340072240601c080c015000c2e075081200b004802e110b0714104605120803a40030b810314100c051f6180c0988010002592000d601804c5da1900844c6070400686800c0c0840e82240d00200c40e050668178004001c03021140d40000140c03541040e48299542c0700c01403481030501c8400f051141c0780e0041a4001c901040c01503014401240c0341c481103902c000741c1c000007001c1a0114081d198032003070f40c2d081039980041030781c10704000341ea0b071040b510304050001919690b10500364a030034940540c10000d4201004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 478740872 1250 478739622 478739671
    0x305030408160b0103031e14090d0317040f17031509130c0e1906150503040516030f140c0d290c0406020106060906050a0315030503121906030b 63
    0x8800b0142c02c100b140c1042d41e101e10b0003806100400a929842c1c5001c201c00046040c4244000a800055030b4501400c1a48500511528820048048050001d021010360211002c0040980b103503010300300901e0070710500e0400c220500324481015184640c204100040090b07060201088080d040e0b40085540c1c0e9002c100d000c42c2000c040009000805120b40001e540c07016182c00c03030103039a405900e0440c901c0450407400c1142c42901c50020752218010720220414002c00280d580203000344c0c00d80d910b182e80083c84e02d40d210010380044a92225a0b98600144220405841c86842a030390041010803890030005140e00540d110040030481202035403180480580d841c200d0108500c5245000c03400c090303865120940043c06848010b6180c4400010f869215041c4041200d00b0b5803a41d0b80b6200280304120064200390000300416052420000000b43c82040100190300ea000780c80c1d402801c004d034030f0b0010303070245500c030f14841740c20500180041500550603e8200102c031030008030b000d1120800 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 478742122 1250 478740872 478740907
    0x30f130503060a0b030115050d0f0614040302160b0301060804060b0f031b09060d0c0e2a03061311040b0c0c03070609030521030601210c020c010801120305030408 71
    0x16a0140116814003101d44601d401c42200c80c48128024407009100125040a003d47e038801e499001c44080c00c428041807031119a8591180036072004500c1f00c1650f101780d0f400040a44c2c00310010b030b001c0d0340d1150450300c543c801840034280d41803180345194580440100028070160026003120b46d00d6580e01c1640d0344802640d4130810016050300c000c000b034201d00401d070300c1001d005103000b2190702c13002401034034000d940c10412581c04218100748500b03041c003110f86110300514200906e00c44c00504c0d411581031900100044903000310065491501100340f00341c501c0c5003640341c4030090804e0420342d1100010001d450694031a05542c980b07861041c00700610303052460f0a41074050040c40400f10351664445120016680140212407266042112014000740f56400950300c005082c804524158842c6400d00001c5c825000024145040c4500840444182e10885005030f40b001e0b03006100b07945c04c40d1141e40100441e8644544070003503620098001d01c0700a0006000d1a80001c92244400b1600c00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 478743372 1250 478742122 478742129
    0x2070f05060d0b1509090606070b2e0308191e05070c0b160c0e1003020d080903060a02040906091a011b0510060501031103070207060e01030603140a0320030f13 70
    0x90844d1548000190141da40d00200c41c55000756240320010781c40341420070485001c01c0e880a0f045c007041d5900b01a030100700c2003028461100107144004c0380a580e20404242d8061805100034a41c0c0790303000c2d000400314030401c001300c2040c00000c80155003e6078401500580c045602c0c1031481e6a0550b0b8603059138003130a10340003001e1028002c500790403051040000c2c900d11034440c031891040386440325950010041e00301ca41c014100d290007428401803c00300040c0426501c10034110b81048003290009040203030032900c0d0031050382d001c1402c0101542c00d014480040030300c602d0800051a110441403103000d0b5a0941034103000c440300040c4542e00c1d084e050f0b00c0c045c0c0c1c0c0160035106040f8032022854080c040c3e9214240c0040c0c1480e29845190080c9000c9038007551894000301215440e00d042510004050070131181070541d1500e001000c80c45522003106d0f020461400381803548107524001d00401d80000f9400d055030307050504c0000c3d00e080082115031143d04c051449498000c4681c009582604941 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 478744622 1250 478743372 478743379
    0x1e050402040305031206060f0d18060207050d18032307030503040305071e05060d0b0102010b0a080105060a170d05250302100f020f0f0d0e01110a0f02070f05060d0b 72
    0x1d400402e0000200c083c061403808561842c0c01c41e11050704018840c0a610b0042c0814901003251800095080d44144c3c00c2c80c2d181c0b425290f4110032510744504030382020109450540000c0d00c2101203d40c442c00180304620302d031000e04546030464031084d10244600511071100b110349428a10640b104200180041d40c0c003004a075540d03512490802e80300c030324602c203101c1180001403800d00300c00151580c06059130000381c26142011503d0310804003410031040554199569040740d0212a00da88001d100600150380000c111410203a007032141d1042c45900529a0340d80510080101c82c001284c605001040751030580d49400c0c041e00100b403064100300b0185040904101940c0406401141000040881c100100201418442544140e110720384102c003410300100000000c900084c005040d001140c51301c00a8125044160725084510a0940e42c49100d80484d000548903845240c2e205107070f0395803000e0b1021a19102d0b00766030606c0ca60140c6845903002081c400b441c1040d5a00410203400b004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 478745872 1250 478744622 478744627
    0x3040f2a050d2409020405131502070201020312090f07150e01021507030f150e0402090901020403120c02010c1208060a120b07030b0a030b070503070e04090b011e050402 74
    0x4514140300e0248400103005510540d41002510b4642070914508141d00103902040e00021000e0452000381d0600200161540d181280740243e100c62190074800c6118940100072200a4140001d00100b081080c040b40340c0100301d000d0060341d010003510010440081c443c113a41d2507800041e4181035481c0d044103840d204038100003c0307044603e000c000810340d982d00d906441ca9891401281c4a144600799845c0c00011140800c03285482a449800c00e0011008006403000360f048202e015484c41d50300192000502c082030100307500d004481580c10442000c000c600d450701e15070310002c01c5000902c012003070000801404080da40908400807410f41d00c5411101d50341844000540040e5080d83d0f102d0146042071004680c0c1c030071480b1070400700c0340c022840c501c40e55070f202421406460440c802c0d03500100c82060000003d034442640c030780500f415449090312881c25080003407170001d0780d101c030511440c10402c051020920305541141034078540f0440c806001400c40d1a800100c25590002e60080c0c0700 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 478747122 1250 478745872 478745903
    0x51b0a0c0602030a0f2a0f1101060f051c0f020105072a06090611072903070201050a0f02091c030905220c09050a120201030b150c10060b070803040f 65
    0x260b0788226101101071204010300c2e20741b64100d0000700b50340c00d40081080050444a01068021028100500d50914007400d108031a0b0311054203542d004c0c0d1110309002c51428060041d4513000c000b901d00009494608440c18503240c680c00c0540f449604060f0600c04000384031420301c204582019104040c1600e4451265108aa141144007640c41000700244400c440450702c503100b4000010030703505680c01440c149041c503042103424221140c00c2d184103c2e0280707010a541d400500614404c3c0003e400028031f030701c2c0c00386520081e6020058080c000304e10410601c51590707500300000300d001d1a05461642c04100b0f07840c0a45104405802440e4018100001d42c00e001401100c00b50b0b4060582000748100820f402c404d4901580501405038040d10000d8140441000e00c24030250181c0145808101011060b01107008c0100507001414030a8000401b0160380004000c0e44200d600d11804c10018107241c0102203601c1d004035140101441d41c00000304082c030007009a410021608400c0103180d070600e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 478748372 1250 478747122 478747141
    0x3130b0f04030201050a020f0427061503180b07030203060109090f0204140f0a0b070c1509090c09030309061b0b0106020f0d090806040209090f07140a050301051b0a0c060203 76
    0x504840c02c0b80150309010000343d45540324002d4480720b11143c00d0080c00c05050580d40712401d180c41150100030025483d451071500c246001e800f004220605203416040010b51004050310010501d515000c00c4002c428000070302c40426055200460f482d0040e200d45510300100c42e80000d40c2d00000c11075003045034105200315554001c0c000c540b41141448054842402440208414150b0080d84a10300307203020460b00b4019030003000124404c0c150240305a0b202d072000309114520180e030800080d00c0301d405020541c42403064040c04c40040c103007803081d03074910f90f0f0080050295000d10000c0080e8040010149011032070101025940416556181d40e1139910007903450940e80440031301d6114440703031081c003240500343d03180c00c0d036881401502d01742e43c032a020704c90004400362000c070321172182e114149501c007400c1c05828003500e07652908205817070b100400c000828141d5042144a039251000b44443c410f42c544089072030710002c901203a181e94840d08140c459809108001d401d090000007000305002 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 478749622 1250 478748372 478748401
    0x90312090901090e010b0301090c08071a040e1e070f08180c1003060e0c0909280506130e0703030216050f0f01020a020d03050705060c07110d0507081501030605010e07021203130b 78
    0x4480c40200c80820b80e88378003940344403001801da805807020820041c072420782c585541a078032011100603100c242251901d032201c60f41080b98541d00081c04800c1501520348c0c001ca805030440b191000c3c0f9080e0400090040d40ca58041001e40b0344181345403203000c09a68040d0b00400c009114414a03941035203001c0e56450f41035802000118464814000040e4202c003a4a001e8908070390701c2000d00004007001d02c0400002e1102400b1207520039260030307030418040241d025501c0000699400b500070580340d4034010b4940300701c40c0e0100d410562042c6007442141c540420b1f5011f0003c00701c401c103042d140c02a00607070408440001c040d4200c0440c41c003102c2030681120003002c0c00d61080089030749565859601c41424041c00c94000e109403107088101c845031900c0865140054024015034007110768618015180585d40c3c0c120f003a0011800d0010400e202c00c62046900510005a1900300762900107002915601805004608003202102041c44020100308000120b40c0c425101d10590401c8541d91642c00e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 478750872 1250 478749622 478749629
    0xa0e0c1b0c0d03230c06041b0f0303020307050f030306180a06030b01060c0c0b3901020c0109031211040501140405152805030a091e08090312090901090e010b0301090c 73
    0xe09410340302c1300c030340b0008801c882800d1003010144c02070352140da64000035045002a50b489109040e0b6000c50303c1c4001074043e50080d0310036001550340302c00e41e14140f410400d20103e80d0103503400a02c10016640c5a140c00d007c941203a00344205100c0d0388031a400401008643c20280c0b440303507000b0000c10842c1d00039409819503401546d001605c280d41d0428080144203c10078001c05207c1b01d0442c0b013030001441a41880c2d03020b5000ea000d5081495040a030890f084140304076102d039118115002495000900c0300c00246405000748a04064405060b285109034801d00b81001100c0745c88652400000701510050b00c80209128500c60a070030040041f40c001e01c601080c81c40341543c0c075610344c140c00940312070300b074601d0344a01d425603030340410340e0000780101281514440601e40d00d801c04078008003003110034244503161481e100e003880070604d841e01c0294440c20002600800c020517495655003034460442d140b8250200c2c1001210f41c0d11405441c1c1d880c81c064043d828100d8400400400148070003e8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 478752122 1250 478750872 478750907
    0x112020703020106031a090d1416080a030f0506150c190506240a0b090402070503040b2113020415050d03020715050403030e040f15030b01050a0e0c1b0c0d03 69
    0x2051000d007415801000340c841f41450340c45007401039145400350424401c0c0c0150590590b080c000d0b004c0b04618007006401e07040b038064000160001d1604d425106a039900a0401c604002c1860803901240c220214006501d920040200742185482da0402c00b64070505c100b0180d1408190071454800d50b0b409083e10384550f04101541245010350202001c402d2000c0020710f2100ca0303502c0d0910540c51980070702100b036000398003001490301040341000100001d00c441c0801e99602c884c0078030b5000e0b9020740074025581c00c40b01c80c0180081d0685004160503d140c04441c000381403041190340714050400741e403100e50400c80c80c85000f418150045105812681d07450446410301c090842c00715070601c201d00005010400e5140f18800e0343c203190341b0092a0b0402d00100140401c400310941d0021249940100c035502140030041c81203042c01c84201c8014081c00001c03500509003508914154050064001d48070000b50806401042c4108039009002001900e80d00000301710707050003401c441518804400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 478753372 1250 478752122 478752143
    0x1c0f0218041509110d0302160611070501021203010b0903011e0507030c080621030904290d0c0e040501110f040305060105060313080d09060204090b040f050c04050f011202070302010603 81
    0x8542c9480c040c465807240d100c1d0340c450350742c40e0000030050030700708001c0294210b104034806c034103403040300c6035101c40600b0036034403580c3c1641e40c00a4841d190185e00c0d00b00c241103411014483d40c2e0500b114017900d0542c0c46500745c60b03803107040144c08603004028005912060302c901080145504180785d000c1c81c01100c40750341c03c1c0003199181030199001c40d000e0301d2680d00124404842130442580c090101d8940070724205403071500c101e510010303041e030f0800c00c815400541104a04101d1445500c2c00b02c0007407074151603409204003291030b80032140380d0f20b200f201c0b02101e51070b0014080040a521403c0216000c902840e211603041d0401440c0d038001d400101c0755131050300004105458524260388c800c43c140c10310020000760550707680140360043d610b540215034445140e5400a02c0c070f0700261001e081d112000150b901c0101041105440c1c62401c0054428031b1310701401a20b0500c5c1d4200c40c10340d00160b8000b0141e0b01c0c04001294001c030711045044090307102040040c00c00d03a040d0484000c89003d19240d00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 478754622 1250 478753372 478753403
    0x6120e010506060f07020406050a06020d09090509060c0f0c060f090f0a0803180a051903030b010c030c0b0603070902040312170c090f130516110c1c0f021804 69
    0xd080352400d503842a8088014008800e4003401880100741740343c400740001c11116035a9012600c007013520b40119015801c480582c20b82c680d13000c2c1c0d070384000b4030400e00103102c01d04081d400d29440e048007410f541041d043c00600f10b020030624008903030241c00502c044568520740591499400441621740801c82c1c020150b60200e0860b0001c1c442da001c9412000d05855078071000e0b900090681c82d42d2480000b8001e01e51841e0110700706100805419010031011031407604103150040071036542c2900581031042035009200402e51010042c01d6282d4002c02000403030b25040e000900c0c000b0300754481010035000050100c2041700aa6800c0c90107401602d56052501c0400e13030081c5440822902d00b02d06090900003d100362030704000708003010001038400c2e0140742901c1c01c1d6034203503107044888052501001040d10308040d400f2803c4556078200381c0151907045407090010301001e54584a070500340c107a02244c0001d00c4030203188140c4440c3d0042c6888440643c80c500510440c01c00c56055a8003d0800c4801 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 478755872 1250 478754622 478754651
    0xa11131403150a1503050a030f09091103040605190606050c060903030106140306060d0e010e06060102070812030c040b0a0c350c0c040f062408130302010e070612 71
    0x426800c0c100031a082c440d41d0f00c005400c0018440440018010350b940ea00c0040441c0c014040c14003a18002e54035038140040d1040098180c903055449509c180c1c0ca01034030846000b031640c05480d00710fa44840c022455483d098450444040c0c0020030740320172450403d00047c0c03560450b004040c03400b1503c055036119a1004800c0f601c1e03020034410040032616002d9040305102a2000940c1c0c05807000f802141000440d007003040403108a80c20305d000c240e540e80b04442c0007a40c01c0003080e41c03040c1d0034402400c00f581000815a01c03080309800030040008040046030b21086c07080c00707440140802140300c54442c44815801042c1d452041d8082e600b060400c541240010140024144601d044000d1134511035204502075072581d2080703460a00500600070012696651402601141417400360301080c490b051804d891003804d82c81d107805190030303554080414000e401c03040f140e40c0924540081102c0c2040c5003030603405010b103000092081d0184250202704650010042d054201d903c0302d00b00000c0c1c0415145 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 478757122 1250 478755872 478755883
    0x120905031e06181c0c06050a050103060b030609100e0a080c010c1107120b0402010219260c0706030c02100f140a0c09051018030f030f050a0c0b0a11131403 68
    0x2884943d810410202120b0419075101310049406031418080101042d1110000c480c425981a54a031b904c400042091041d140907907010f14904402074406800c0415440b90b44039044100285d0031603d070842680c0002c0c06200d41390406400804180d500d010004404c3d0081c21038168201c0800e1040c5962105840009540d40a07123078003400a1082d085030713440384106848010412070441c490484031600300300201703000d0507400340319020071204024903079114051034040d412800010342c001d020844081c400000d15030100d61303080c1000641d0340a0008202c0c00c00c000c039085194107504090715032803003203d154441c02d910b5010030030106980c1c135845600d034291903034100c82e4400203104c02c50600c41890280c40c2400482030354104280d6031003100d1081c1890451592007564413107036916048040c59007002c00c08036003c040e440c0031464921421030141620168000c090301401200000480310003160f48040c0c0865203c8041903210411000050b101203043d02940104220369103401c1454180001c8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 478758372 1250 478757122 478757161
    0x801020c06131a1008100b1f0503010b091f270302091f0807030506011a030402060a120207080304050a022e031e05040b151c120905031e06 61
    0x19400d8842403080b00c003025a8058040052070b2244d10300003401200c00c00100102400c0a030000c03910030400c000b00114280701528020200c00d4426540f0314650340902113038107440d10140030903192210701011564440484a80c50715400003d0510f400e966000310402c0912612454507185254200c5528603101089110081d000382c2e1680108a000c00e80b1013141c4c0c0c8031091320740440d000c250740382700d0907242c400b0b0350303100340e40c1d5421001c0184401481e060081000c60074403010305243d800c1c0756020030800d1051075103180400000c0c11a08000700113940458000310b41201004d0717103d04081c1460303a100c64001b40704038030407585204407903a1811205407480c0b001903552020498104450026006455a41600e025082c19103900e01c4604a9512902c2e005902403040b022252811110801c51100310307000651140e08841e9041e402c55030514440e02c1c0051b03000314088401400190165a403551540200344e15006040302420300b05406059070220b00b20601c1190443d854140ca82104203c00c0e88 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 478759622 1250 478758372 478758383
    0x50709031209050906010503250f0801090b1c0c051509011b150902060904110a08130506070c1b0e061314180f0d08070e040b010206010e061206010801020c0613 70
    0x600131b0740c09400999404448651320000100c3c038a044801d078030100c407010001140811a5400703000798010020350161100b403070104040b0200c6c1c800203c100c42c2d6440b000d01c2e5200d1880b1000d0400501401c40002801d01900c00300fa10300990701040d013035400c030504484c0000e05070807548000015904851030000d80000b0035880c0321719403060b840c0140114100690b0401c06c1002802c80c0b0307850368480c1540940014038410b41b21a000f4400401342d1201401d510106100d440481010920218542d80c0140341410003c084041900e011744102540035440c8024007101702c0300056441d46146c4c2284290412100e411504c196012658129160458104404495070000440265200300c08040414483c0211500c000003002560318010030b40741e407500007800300001e200e1310704d4214803045100d940c2283d080c840320841100003941d4540c148a80c1c046030481c5000700c0d9494503078204084200820505865440d03031a00034190203580407809011003031040c1d2001904901104030304206040e4441c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 478760872 1250 478759622 478759639
    0x50702030f1603110a232d0115060503071b020607060603020a050a0305030d1d060709151115060402160606031a060d080304030e0414041b06020c010c1505070903120905 74
    0x700a42e021a80b100401699110700b80041720071010084005800f06c1c0000041001100380247d01c0382507841178079082d643d60407134110501800b90000b050301c2d0b100c0b140b890f06104246003030002540b00d00c25500085d41050000401406104160f00700406482c000c0e1508002d42d83d440090003045c88443c403010303220390001d0280b24101042c982000c2c01034009208607003030b04c054000101d400c0100907205100800c5070700c0ea08102181010b0a00c040a103003904100d090788913003d80a1740c5880d4034940c00c504560281c40001c115545590541d1a005400300c7c038410340d82014545440100601d000075a000050500c0c040388400d5400402031080030081c214119500b4255100c400b2a0000b42040313090004c00124444130340c03228440c0040b5641e0000d4041d80c207003020709010400070908041700d0140b6050002c24002e2540000c0c0411a401007840c16032100c60707150601003000f200035200300700074509003c103010000b0381c04111300050360b00810300c82c00621a41481505c0f181004c0c4111500207014 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 478762122 1250 478760872 478760903
    0x2210d050903040e09060907050409110409031101020408010204081011040b030a0b0409030e01110a0b01050d230105100f0806060d0812010602030d0b0301140a050702030f1603110a 79
    0x11030300925040391003442200e003000c3c3c44016584140d0030444914485501000c02c0200d044410803e6200034001a90200442c010a46555403072640c510101c501803a22061381200300b40c4180c3c2007003100e080e00c2008640315921140c481d8040d6101e0311500c0d00301e101d003c085506110f980d01c44c0ca0300c1c08541d801c0052825140c405107007403030b400080c8120070381c581d140304850454a40c1c5c06001d08882c0300e5039450200b448104005400c000c0791214244440c0d1000c10680c001540d851704503030654800b2101064410183e00d001800031100110700c14503403e8035100e841d00c80b04150045c5003c1d005d10400c3d4203805441e4500700d103041c50503215007070309680046c01280c5c19040c0700071440a020b0190a0161800c81040b055014545080c0d00480042c1e10009010703550728898880c0d60b040c03050480081c40704540051810100c404e000d08114007855844000ca07030f0b024001c001302c40c0d50042c50341505449101ba0391514240e51602901580828a01c50b2480c95110020458154181d071008209800801 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 478763372 1250 478762122 478762147
    0x60207081c110106240810090e0c0303070b070e1927020c0d0909062615010803030a140705030a0b0402090616050f21160816030221 58
    0x5564804001d10102d001941c0d80160203000d1100580764007002c0e24480211003e420410905400c5980d081084601c14084a8200d11010310222044075901050750030302e8000060402d0003400c00b1030b40c1817100184035401c0181016005100310b0391a1108031641d8829000e00040741400d1081d5074100c240b280c3d0511183c4541d5080070482c4103451514061031000c84000b800302e07400302c40c440e84180d000c3d034003840405c0e41c80302c2c0c03034405010600c0c002c0c0040340c074029016a01e40c2100c0e00c00c1c8800c61482014441c500c0d070810145145c0300c01d90000c01c0703403565a20314160f101e80c03003542d80f41400ca041c04400ea00f40c020110000b405202c1594400e46143d4403050310000074441035200300d40c070903000c002c802422356448001d801c420a00003000212144070780340003480e0070040880100b0a81100036800782c00314128204526a80c90a00c0c001d0b03490310501442000e031a0076a00c001d008107400300352220f50b038a2030f000e900d045a10035021147c824820542c810f100040f09a0f81d100c03883c0040000180e40b29 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 478764622 1250 478763372 478763413
    0x902181809150709030f06020315040605060406050f0d0510030515010e0712110d0609150b040b07050a0203060103080d0b150f18030604032102070201050906090105070605040b010f06020708 83
    0x5444c98034a511a0716070b41c0f882201319003101c080e00c41c0d980110911a2443c07486140007160341088808004140c5040c001c10fa05006078440d0406001340441c901201200c04004c1382da041c00c01c075808200301d01c1c0c03020250b01710315218001900d43d445040f00c1d10003024101589241a550b40440907031495503000c600b206c42204c088269600161505903107541e1402e080f014180c00740441c0004155a4140282035040314890500c0c0e00300322030411070030002c80c0e1400c0c040b24140c1b4051006290344101c10b007044e47c07a10409180094151064400000c00c0c41400805494810740442040c480760380b6034020000000750140945408803010000300190b004400700400c52042d40c184400c0284c6000c1c8000f90821008440075030206602818402480e0001407251252654071402141801d0550300001c100c3e000700c4030f1460141c280040e158900d68020002e849415521080c207000c03914180c9040540d1010030301c138040e01c00341010008500140049244c900343c83d81a401001001c9200d80c9904442c03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 478765872 1250 478764622 478764631
    0x18140103020d1a03210f0f040b040801021305090405070918020406031101030c050f030c18031e010f0b0306160c0b0a0614010309030509100306090218180915 69
    0x16508000c000e441032003d004000e01ea40082e40c101d40100c03840414036003010000d42480000b18003401001505001500541d100c854904614546444101c0e00050340d0f8440da0b0060000d440c4049800150084150014500f594950007414486640e82050021200040c0d4000306641c100311400d11508502d80c0c802003615030319805070011000305e50045000c41d02560410740300014400740d01000355030140039595801130145031482c6041032414002c001c900020700098001040010955a80341d03025400d48500200101565000c020884187c0b016070610064080f1070b50921b5440c040e0680c00c1e2248a8070484050b001d001180e4031540c040607202500b4464405210300c440390000410080089507200f11409280096118141622101c0c0c40760b0051407981003601b84030a40c00029404815640800c1c01906c01c00600c00c1c1c52076082d8094000341e00410526440850081030185901980c0c0209040075506601001c0500000c618110405c4034142800d60241d465081c490300d510941e079500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 478767122 1250 478765872 478765877
    0xf050a0804030c1e0f02030d111b06040914060a0506090d02040902060d050c0a030609150909240c08090d080c030907050409060506120a0b15030106030f03020616181401 74
    0x10000320b0f150500056004d003105462940100c0001c1045050812603c83c28801608084042500c1080742640e00c005100c4905483c0c000d80b0360700c0f040383d2169802d94001c2d000368801800134a0b0310700c5054104000c11500c0d64880e1009c00303000540d60404c1c0d0112000a5400792160804500d00e07000d000c040c1480e00000c81c2c000700e040007200d0941019100701c81c001e2581d400c0b41f65443c150720317000070107a9085401902c0304600d00040705090941065003241120100000421000218140031804200c4201d540403a8041c00c0b0b03900e4208860750f40900d00d40c5401c0c0c0c842080d03544501c052a5900d016440d10f0602044000000c640c02004d00405141d00022180445d10900d807603902040a882d225070781110003d44a40600086280c50700007058103044c20001018068142c0e100c40c115120054043d03094a03492004034692900d080d080320025541118035650301d040c480c42d000b940c0b42803c45922018050100d4146441442030000c00140607040c820996030a052018020303130f180015039907034107 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 478768372 1250 478767122 478767143
    0x170c030909040f2f04050703021e0406091706040f050f010c0309120e1e03010605060c0d020606010516080a0314090f0601050102012a02120c0c010f050a0804030c 71
    0x5680c07204600380c4101c0c0309103041501c1c0c034402d140c070b0418203800885001590403403030900f0a0f0080100b0030101694400c860200381925400740c00e800a1043e582d40401074401e08403a51118041c45004100f01d80040e80c503500081c0c2e130340000e4154004c0542405215801c02c0b004100802d01016400c80001d0140b025100016000c512035401c4038598400c0002180d00c40183c2d40620190340070482a03455103040000404480c10001111907500c0c3c039500785500d99035140ca0410fa24254000b0b000b5000c00307402d81382c0c0c0d012940c0403c0d55a4210859660052040d00001921548034030140c4c0e1100300300c000380d5041c240070bd546010706900a541501304165645041070100380c03883c541035010741c000d400980240c0b56550442410050705030880c40c19a07040c90008160420540ea00384820306850200102034103100d03d0890400c400c0d403501000c104d20208038134407001c00200340c414003d642600c84080040c0308810a50706c50080f01c3da00004201408000350220307010b0707041104801e10a034120071 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 478769622 1250 478768372 478768387
    0x906060f0402121504150603060305010f0c0e12030d02070506150114070803041a130b0c0315092d01080d09060c1104060b0c0c031624030212010303030912030504170c03 74
    0x100146c4940c031150001c0e480380c00803c280002885060880e030300c038403800e0102c002d08000280680c8500000b090080326500c80001c0029401e006465901003103c1d01550364071900d040c10b82d680c00c01a0b03000201031074042080b840b590301424100541030740c2c0084207810220b098503030441542004105031902d840103100901c180c415000e01501c50300c41140c40803070b054128244400b2114000381191300101d030420510440060348890300c032000c403080318502c1080d52482d650346ca42c0c103e102182c428080440041122411000d84424141c400c49811600320044860085801c880580714040114208035903207000702d14202c1d40900c05540190005c10105d54800903401d56a001000c1e0684c030350800c0d130350382e1850315041c0020311900e031502c030414909070704000b10b1140074241d0501c241c0c2850040284036175500c2c00380d019501807030900c081841c15580c0d00d040c0507000d0480042c08603245030680c0591002c1c0f501a2140358004ca4109000428021f1801c0010019500440079200284000e00106 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 478770872 1250 478769622 478769651
    0x80a051201030c180c1d0114040f1a1603260403020105010f080616050901170103050a140a030909050c070203240c07080d0c050409050906060f0402121504 68
    0x19009510032103044080a180200c600c001c42d0030b070520380510500b0a0700c16070741c0c150301004d40385900c20120040446c80e04650010f948a01020029542c4503501007000110303044642c820904427460503503c074228840c000c0701345c100da00c2412010000e600414a01c2000300c0c0c899100d00c141040c4031050952101d6260780101100c5408541c2140140e4403000140304040f0703006078003c020b0030000020003241c18003603041140800083d0300e8000304500030403031032842d80c82281c80e0710034020001031206140d61282886070300c421407030750242d503814031118031422141400140c0000d43e0707030155160100941001c100102604014020703802d071240a021800241e81c0030b1000c0550030300340856403941d20320b020794000c10510005108500c401410311001300400c0e8180111a00300103684000220041030601c1610310303010300d40002102505c0c00007000145000000c1c0c0074000c90040366802004a022810041a0700c40c0314610791454440f00013141c10384801a9131101c0c2e000000304049052028901c41 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 478772122 1250 478770872 478770907
    0xf020405090405060a060f0602070b071b0f050328020904150e0102030f100b03040305090303040306060815150f042703180608011a130b0d020d0f020306010903080a05 73
    0x3915141c1040050103071701507107441881c00916041045002c01c1c1d10302080079440d080d41d8400d0440c06100080c2d95800c00c072201c800400e00d0240c80d211000307c01e845080120754403c40b4020b05010388103004035070904902c182403403582e61407004901c01c1c01880c0784c0d0900000184c0680304940303661108800c506000028083c0d00c50704600200010b0700ea203488440b039510500090924103586801510910500072500201da038481c0d014280030380d42c0c1040e440440c2c034504c11030344050700103443c214002c48c00010110f07050b000c80e071041c25940019280c4080280200c2044100542d00202070071001e01c0134207045d00401e812043d4002c0b4947c04003802021207200c0c0c01341d030101700c000030001c8540280c0c6660200354040944602e00d402e070815814200e101404130032003e686c448204010a202c201d40303e042020300050400d00c11540d85514003043c0402c069002882d41140a504140c0020345220301f520a403446054160754240d500b03840c5031540728942d0700c084500010010b00b00710b440e00f885071034101c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 478773372 1250 478772122 478772131
    0xb011101050a020d0f0209090f041a1905072c03010f0515030f060c09011d0406082805061f0f030b0a051303140912100c1407050a060f02040509 63
    0x40566213180b46401c4404681a00a0003c81c80d4814400c4044541f25500b800d45e00446400a142c880e0b16181002a41c110521080c0c0c0c8090100208102c0455112841c894080a09900500182e00c508a065444143c080b000d4403400100f24240c00340b0600c40320418451340710180c00003a01d10800d5440d501038403011540b80d41031360074047c9200d02c2810100802e02c808510a40906101c2c01d0680011002d8800c585d81c80e810003419441064000f0302d21001a2402c0f0342c0100100441030340c40c1401900c9100e8400000500c4690300d200d9410f281d0702c0c1a001509130750000c0a0700e003950700c00c0c1c2c2d42c07592140c520408081c121504000403811703a140c0f246103406035008042a07011880c04074210b200752240105283c074407802002c00040042e4100d0460190401b0100e5450b89400440b00401d020b00740340501d4010078807070007046c80407460040d4044007408403160384015001300390310b1114000307100e4130303038000c0c07040e0701c1040e000000c0750050f4071103a07103d000c00002514055481000030100c82c1c060741c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 478774622 1250 478773372 478773391
    0x9060409091103030a090e0a0605030a050609120a050403060e0304081005090105060103061d04030224040c08030403030912170d2306010c031407020d0309031b0b0a030b01110105 78
    0x6001d0010301041d0440b1098205045000314500000014000c040340001d114800903112441d0100c0e00c0a03010f60840c2d0f0180030040e0072500d8014481c00c000c4e40e07461741681c0f680401d001d2103800a00141c42c0e0313001c4405042258a07100e00d02451583c0b00401014012401417041c08107001c0441c04401c144130700340340d00e040e0f03603000700b00ca00344052420308440001e4801810b051a00780100312281d0120540808044c00c00e2880c0115a9181410307410146452110b044814081e15a44071511781d69850a000c0c600076540342e10200d03217030503840e992071095010260210b030040e04d00b00032442841c203101103280c0c03203100320840d410848040b10000350452101150000d403900c511070118112030b1001500c040d04140c01100d03505014001818419a201000d41081080c0c00d8820082d020341c0129004540d0107003e01078085214100105588914001180c0c0d071007846041140c0001e401c00c0303810a40d607925004074070f4100f0f4a9415002844c21202050501c640014011010b003000e01c540c40c8a802e520 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 478775872 1250 478774622 478774631
    0x20f060a0f030e011a0d060b04110a03060e0f060d050a050a1406100302090615070c0902250309050609031f0f0e0307051905030d0203090a0b0109090f02011409060409 73
    0x44018043d603014403100102a80b40c07032440301c281e5840800300a2101e0b02a120700860000782d08092001e0702020100b9038015090082d80c1c4020400040200101c100303a03602003048944808441090442c02d5440d01d80c07a9054201065403450a16010038006200d01d0480d04006c60350340d940b904103084108196140103481e009080b08043c28040c803903000c40e88440c0141c0c15402c5a0004810b001c0c003400c210b01440d0205d02c0c00c00c03208a010b08607044035402a0074140706035603030250200071703500c001080140050464079601c030902e40464599800f0303515403038060701d10741044240900e540269003000e03414810100803400411703c0c24041c01140c0c02c04400841c0c1019510b07810016030f10189200c940a9004004070300101b1404210804103000300c0341007020301c003014100381e4918050025225110713803002050181003000061031401451098610382140da0380d0b0a448000c94500b07030405040312040c02034000040d84210840d038034a200d0600b01034246240c5502055554100707400420f400c0c0c0d543c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 478776978 1106 478775872 478775897
    0x12080d114b07050d080c07080f07060f0b03160f0b0307031103070302090f0d030e01080718030c0306050c030712090501060b0721020c030c010c020f060a 67
    0x151488008105071010003400300781e1081104840a00c100e010240c0704900950721507225102c1031070413a052401580380c12180d41e1000340c4199212404029040018510b8881c009031051881800501000c0724014585014100f00b410300b0849080d48080003044062084c1c070007540d40001300c0035240d894080040c0c01403e039100001851000100400481d6030707043c0d0142152200440390700094000c54030074840c0882c0d00c103102400250041d1442d07441540074000d03040c0c102440c0d180a201c214415007020140c149a0341048882d8030003480e0410a011840c0a201d0300640300315100362650400000140442d0520020005000d44a070040340a21100313500400040c014107105c142d541040e1f1810420710404d2020200764030800703507500070010744002251600042d014004152140d0032800644401c004140100c0e4407514202894a01b916181d000e00340310724a9458800d2603d8070b = true := by decide +kernel

theorem cover : BRFrame.Cov 478597122 478776978 := by
  have h0 := BRFrame.cov_init 478597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 478597122 ≤ n) (h2 : n < 478776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
