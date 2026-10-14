-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1130
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:22:16.095246+00:00
-- url     : https://prove2.me/submissions/6114da1d-4847-497d-b81a-7741b63a9f3e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 203057553 ≤ n < 203237410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 203058803 1250 203057553 203057563
    0x8010302060901021510030213090515040f0609030e0f0a0501051b160321180902070f060f0b0f010e06071704090603050601051c0b041202010b0a0306051b030405 71
    0x28020700300841c040105a0003404030341c0000c02c0100340388009180020025043c0c181611040c0d000b410107036604035818070113000b171805094100d4000d2120313910112001401600003041950308544407819100050100d00403810041e0080e0780d494804007000003080810074024041c107105d80c0c0900400c0040d070340c0200aa640a01800d40c0c24582504102c070094207080141191001c0c1c050018000300c1086020303449034880205000c1e401700380c0c1140d0103090326090202c1075a120000e01900081120304626001061203911500303419404102135510803007901c41d140031034140d107912198800081d050000d1101d545032000d107480c5030a0074450003c84c810b84030b012000740c1666080f4412030000340d504400c6074010280560b0400c82e140da2030070002c3d00e45400b0b024051043d00616459445110312641d04c500c01c58002e0b80d0600301d0340310b55903032050000b030031900c2d0415552038070440c900c903941d0068008010b40c001c000108507071400402045046250342407140c103000041c0240000303d600014 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 203060053 1250 203058803 203058809
    0x90a0e0a060507050c06090717122d030a0506030c0d080702060307110d03150506040b180415030b0103111f0c0807080403150510150309020f150a020c040c0801 70
    0x79001800b82c98000b4121203510504140b00102d20445040c89242c0100245000889401c0642c0c00451240640e445460320b55511181d012024240140007103200207101e1120300c44880d0241060001001e01c209060ba04102d804110f240c0c0e0f04d8042200c1401c2c203001c950300203c0200d4140800310103560311200036014080002c4e004040c04400a84407500403030745810a0381e2a0400c40789401e900031801009411020181d1080340c904a00c005894200a820345041e58008289641070001300b144244150a40a01c601d0344039884000301041a01c452500401460040218042c05d41c110f08210784512220f1107110b00803803146591014480c1d00c03480c960a03214036440c00b1511800e45040480300e60148101c0900890400980041088280ca4640c50744503030b8908103000d03945d1289080180900741d485005030b040c044100c140e51a52195019007881440106041c0080402c140410509007041d21255801d0038001860304c000c3d90100141c000d8503108032014000000c607110b008180c00d80601c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 203061303 1250 203060053 203060063
    0x31608040204060b030f04120905061606060905181207030509150403051207030807020d0807140c03040b1e040f1202130f0501060f030608030901080403051c05010302090a0e0a 77
    0x1402003011959a038015400414051141e603071030781020a0240d048a03800d4a0407a0444501445030741070390702600842040740c400901645c180b010000e41d040408010f01812176440c0c0c2d8980001c280300ca9030b072080c070b8012030120581230800500c59403460310701704c41c95030079024a040901c03124000071790103400c90746080300a440c20044001000800030349406560030007032850207420302c0000020b10080c080c024181c0030350f8070b500807600e079100b050fa100c03c1d8400d00400001c0c5000c0014640b140201c070b0611031085140780091400501c4001c2c5800d50700503030010742d03d040f000100e10218024501400d40701d07154a1aa00745440d00d8016070301703003d0900c0c0c4116040c8a070000f4546055580b04411200301c07801d00c03001440350b80307481e1034801c00a107424090070000c1400b46020700d45d02c030310034410202500c150000a41c50000c40740019100c14900900850401070704020f42081c0010f0140300d1080e40c6204e03040400c16505510402c4541070004200324119807601c1400740e0744000010342ca007807803a045 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 203062553 1250 203061303 203061317
    0x51006091401031205190503100605030403020a060209030c0a0b180303041401180504020310150e060301090b1908030c1b030604030309031e080f06040203090a0305090d060e100e030316 81
    0x75102074032240280501c0c84082151b038051902c1d507582000007580f080310401d5100b02031584903002660316000544011300141e0004005000040040e40141750540005040b121886203500008034080d0383c640100050352404070700c160480b03402d0001c51407103000c00c43c0554241407c007075201d008120f103400c00a04000c2a00018912058010100e402404c40030304155900d242840d103400360504284905141c02c541c001520007840d2003000e02484c0d00d00020010707499071740707043c42c1000500500180c00d64003640045071007008030502c1440703000508205020315100c0080c200c0040c2401e00f17091034a422030311040158402c0c3e40c2e01044140e40140c1c1b5082c00941c20385941000c98035048070100c2d107104007404a840480c01070300205894413408070b00404940940d521820f02050313000c15502c045a5501540003000081e00074409840080c4001c3c0011007408440c2e00d812042d200030420411b0720340c008070b40300e1709003403001c0c0a80748014021000a5242d828440e81031400440a00d0344641000784c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 203063803 1250 203062553 203062583
    0x10c06050c040e1608010911040302130e06100305060106023c07080a1106090a0b0a020f0307030306031a10090911030a110117070c02010c0204090f05100609140103 72
    0x1050382510b0252480402e60b007400c0c94458400202c2e914083c400c1e2011804000000030807149038010401d4068581c0c00c400e0038640b46600380300f000000451210500350b11140c0d603111600b410020307688910214026000c41a1130340c2492030410700180c106c0011134000e50801c00481c001c1603041c0d400102a5174919811482a0703603004106015050340c40743e01d001d000000900c0280000b0a03180050182e403020500941d4042041a144240660580c21103080350040011200c5c400151205000c0350041d1031101c4180103c0f00d04550000380102c0100741c0d592018014800f0b48402902d0700b101d112141d0b00075080c40d0f9a20708241580d441000350281d12884a038003000301d4581079070750740540a01181c1c560700e0303c0d2501140a03d0074036005800100c80324519203859040212450280529072602000540b094004540d8005014020b90300282c980c0d461100084926000c0b018003030141d0702034000902c81500c0e24054400c154400f0400d43c1c18449401c0c000048000c2003030440c0e6004540c0120300031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 203065053 1250 203063803 203063821
    0x5030f0402010c14010f060803190813080c0d0f030207050c0415030f080415050406080a0c0c0b0403120c030b15030403110f0102040302040c0903081803010b06040b12070c02010c0605 80
    0x43c6400d001401020011034009014005401607168010819010310603ea01d400050f80e49000b40c9075100100c42c0035402c13200e940c50040c840300e6006064a54012a000c0d425165a05940c3c401c0b0903c0359254010100960b6079503100c115108000a02e02d02546440400e0f02c1d0141d8560342c0101d404c2c462503131500c4019441d1184400710b0000c41e40600105132080d040d0500007030075005031040302201c220801050322203030b00c1070303007242c003524029200e54850f516003801c030740002d0000e528a81e00380300c0d038041c410011506020085100e944203a44610903400c100e0505001e0303c84580c2800c00340740c00e02d49550b2003a9244009807170080d1030807482d240c80e59900e042c1107407040c3c0030300103d07001801180c010002211040d0000d0050301c1c001ea03800e02c8070400c0c04100b200c3d00c045130711024200e5641404001141501207042c00050b0704000c002180c81311640b000209694403682c0008015040040c060220b2410207003940e501106905254850424680020300000480d100c02040a40c0d25000100c443d6 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 203066303 1250 203065053 203065067
    0x60503041a06120f0c03010605091605090109030c090f0c050f07030516120906020c090403050301050f04151203080a0207020612131a0403080f0622020d050406050121020105030f040201 81
    0x88041c10413180b1038540c034090713142c0760003e074600d090003542007040124039030806109050241d11681c030b064040325407000c2c0460b4030340c001c82d03034007810845459800008117190801900c0030f00103221001824030300500300c4e070045803d10703610b40003488000e00040c1413400211081d1211980c03d0309145560303100c0c00001c0076401c14003500043c0310500701007210002d03d40c0425100103881e602e80845291603c04000c000d096401124003c2c0001c5041006010368104070b855407404020281002c00c5d40e44a8010f0714071005815009140040704200e10203080c141c0c05a113190b001095200d00b140b600c0415000305007135110f403124006d2840c03071210100c3c030025002011268101c2e003125100388498181e0070010380c900d50035035041d400184010041600d41d141210058022280100805072609005c4400c110043e650f400700540c603a800d006061614a040c0111440b50384946030001e400e604100c40641546e184000c800c0300014105410310050360000100ca8001100070101640742c2d8440c80101c0da0b130 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 203067553 1250 203066303 203066329
    0x2120c0703021504031203090f030e030c030105070f0e010c02030d0305071215090c02030c1506030f06010f0914090712151a010f0e0d06020304060e0613030801060503041a06 76
    0x12040351860110021008040c4c01540d1141c0300a550304a207a0004806031850b04c040a0310f0f100c161419100020b0003580580e21500018041d107140101d26400242100d5040f5007540c041950540c1030568203511030f42c41c001c81542400c202c060700500d600440d50b200700d060032000c00c0c19501c0002c116218000d0b075501d8444c403400c250521094541d440a40380c95176882c23003064910784c2000c8024803500e00200c240c03036224504034000c282d1101c10070f085140199010304811342501550300d080158510900c9441d000e002500510303408540f4204202044410343c1841ca500c0045d1f030400c0c4071500c0400304801086800c14261040c41c0700590804084040703040c90b411404602c1c2a220110030440d2400701d400c0d1150980300d840e6400c0007650141c9429405949107039005003402a2100015490341c050b50f001030081d0710008114a00c07250705132a0810a4911044140c2480c13000c800301a4084461400342c10289001410342c00c141d665014000403122540f00351400c1e040c0050b031b240d00c5880c110444 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 203068803 1250 203067553 203067559
    0x2010b03070314070e0c18130204030320010c050a0806040f090605040c0e13021309050a0c0312140f0c01090c0b04031e02060708180d06020307080f0702120c070302 72
    0x7026030324a0214400031001d00c1202003070081140015918401e845ca1500c01d0f4405c8144500e0111441030001e11280c002145560142881950340c031424a1480034001079882a11703620505c0c582400b40e2904401540b80310f0788175a040840c52108140c3c0582501d140c0c09003824020319641314600050050441e0b905840b401601d030040003014003071241c03c12030140d03002d2a5100a81510380000c460060340441d495660010061226401400d1940e10300780c80d03c8003141c0020780040b096659a0070b1000f08003055619038601c910600900950240c000080c0b0380500b0103076041d6410600e40326150080201a150000010030461b001c00801c0d00305007502580100c10351219511112004a15002408251881100500f07080074121005590050309a001880a810100e040d40d6103812503208100200b00d031803100e04228210740f1101c0f098802d10303124840150303c91030906801003407150700806560840a10401b440090350b0049028120070080c49400da90b40c06139000c949181c24116070000b50 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 203070053 1250 203068803 203068813
    0x18030a030e010c051002180108100305191703090d11150601050903031c02181509040506060412030309030305130b0118110304150c170c09011205090f0706180b03060102010b03 77
    0x41310701030403100340c030741c7e00e0091301e17044001d03100c29142200203511030100800c0d551142013010b1100703495444c958401889603443c0c01c0a01044100700440780c10940d0100c10075800a240c1100c0543c2000c42001c2c000e0018005010035180011252840d290280c002c3d03050040000b03007070442d9141801120141c030310f40c201944403c01d003400040c0080d4007110303c2c0f04601280c004040e07598a0312451180d01100441da4841c1031020180c1040004d0401a152503440300042200180ca20320344028140a103011341c4000920310a2824003a0070368038010300900c14940c4000410740010004c03004a410b480006071b0700c0c0481010281c1c203c009081c400b92900c05100040200b004000e01e40021110f207491343c1d5014404440101c01c15204000c0071402d024007408000c1c002901c85402c2c0000d408210703014540303505401c8820100404035142600d505515802c6103a2001c0101000c00582004040915005609542c00c00074520010028041e4054154001003c540168800d4004400d28400201659 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 203071303 1250 203070053 203070067
    0xa0e1806010813050601150207051203030a1b020d030c200309041d030316021906090203010501060813110a0b03010f030b160c0f03210218030a030e010c051002 70
    0x5002220484806000400c0c40c00040d445041200103a0841035001d001040310380d08212001c10010700d450240801c52144040005090756a41001e04130030707059201542d9241000707100d07281540c20303004070045400c400200210382c050340000c120000c04158071380000c0e509100c80d0120f0346805036440c62445003a0140b50441401130100c001c10144c04226000c100380000380d10002d030540b00350484000a50000d000103424131040d051140c980f0b11440c41030360103484061030f1110303a0001e140c2046d80c40940d1026098210b0809104150150100d810310180c5840c1c20400d04154921155006244140c0101c1540090712a111a440500750b0039840903182e60b11499129581142c521050b030b07020715607034007140b01c00e058940498a8202c0c11b5490000407072058076041920301600d4011803c10032440d030380d074003448403051110301d035200465000340c0d03101c040740d40c2c03a40e040c2c0407020220b110b50040c0c42a00300281d049500040500c000f820094103013901c5003411420405181d0042c00103600024450f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 203072553 1250 203071303 203071339
    0x3060f0406032f030a02030c012d050d0f2711092509050303040509040311100f0b04110712050712030c03060b0a080f13060905030904050c0304050a0201050a0e 70
    0x148104901106603d042041c8010405075588445000607401d600545440b0000d5446a820300b49401005c00202d40031a001c0c003c1045c0e51000607402c000040da0100c0c1494041545014040a240b58020180300044030391402c02c2c01d040310040c0c0c03603600305e621886540401421540301d004050005000380308514092003907020100301120b9450601e888081d88120b0107000310002c4056500c05401981000d081100307002c3d21000213442a014806211412001f07000b040000f60f0805d0345c1c4080c0070034051441100da1043e22602c0c4400d5110b01d09080e40044940304030360036501d29a421504a51003440150010b03100c520400d0009440035000c0004403100365095002840c3e40e403240d44c3e04110259413480301030540d014110004001441840101d8610f903141242141c002018000c10405c3e18082d56074101100c8810f0380443d07140c2c001007103e141629052043e10303445031100c200d036403452910b50f031481d8032041d421000034144080803410010a41c070030007140e4110000503086c94081000714847c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 203073803 1250 203072553 203072603
    0xe070b1602040e030310091512031701080f100b180406021e0412020f01031d010e010c140f18040513050c0402090f040e1207140d031103060f040603 65
    0xc00da01407410010000c81000e4004200c82c8600d20b00c0c03550072030340f6040004030b1000d442007130079071140543c0d000030104441b40200f40780c80c0c102d4802e8a800c40c1920400c0c5040440840580c04405142c0003c0c45859035608081440000c00082c2080064a2903004001403d00c03200704049620283c20002088200007140d1300502e07030040400d4001704808030701c2c40080c82600c124020b40c035074490604004001803d02544a48118205044c08074a0f001445031440d0004112400481513a441d00c03038142d00d804081c0b00b02460500c0c2407900d40002c8182400345071030b9206015940e80650f10029451022a0704004a404001e000602c04c4c03006040200d070030325460b01c2115040e10140210010702d10310340780c01c0c0f00310303a0050800340030180720100040c10400101a960362118881c002c0710031010704603224400502c01d00e8451300da840880f80c40c482080d86407004e41c02c001000c1c1454240240344101c202000d6a5011200300e400550303140500010501600003944004c0c89030a42d07040c1185c0034100690 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 203075053 1250 203073803 203073847
    0xc050312090708150705070321020d0c030b0405010627081212060103050114040e070914101202030703060b0f0a080f280807030c0c03110108010603020316030e070b 72
    0x200d1303030060740b40d0113404500748080c0c035000c000c200c0401c8007800082c01807910b0181101241041c03001d100c082c010050582c0d216000c02c4400ca682c0d00d0000310510b40621070801d0f00c4030103650030006907060140c00340c807001500310800d0750810f8110311480300919000409014014180a41740c0c090030b51000d08030789400c00b81c0c1e401c0c1e881042d039001508552082c45480c0c12140310008048103162424144001820071f8000b40b0300c0ca0180304004503501071140035401d254002da8015003070301d00e4107542d00c50011603590810405e491080c056100940d44c0042d00030705994100500184d0007404a0001e458080851705c078030307048100c6a50008090302c000c106807041c940cdc4078041d0b074540c4085414001000610001404031000e0f60010358021074100d102601d002c80c03003401c1c5484209426228081078031010340c0112801143d414850300a9644620094014a1141025130070b500740400a4245403041e841c502c2c0c00c140d611610308001e0302c1e08100c0d0800814081c0c22056030350824011207034403000d03004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 203076303 1250 203075053 203075069
    0x60c020a0b07050c0a06020a030e1b030c010819020a0e0910030b070c0305070813030206041403010f050408090f010e12030904050702031c02090d0206030108010e0c03010b010f0c0503120907 83
    0x20300000c801901880071078144c3c2c1d5010f00a001e55403d0342c1d13244c0009401c604003a0081555544000030300840400001d01040c44101400607826019010036103072600d0600586e04022000003845211400c064010300c808592840240c0c58003800e0701d0854a88070001d04d9241d06c01c400c41e09010360303a05400425026a40600100b44980d0b43e904400c0d00d00c05040c42000740022400c00c03020f00030a07451009401e49110505d03503560721310307607940000b4401c0d049604416501c0c14480301c16103c40c94248140c0f22407040c0210240301600e8192104603060154001a9004642d92042190b0aa01c9460300340400e40000b40050120904d01807050360f290018040d01d801641303040040350580380004150342d18074030711904182691504900c9500030f900060200c0780c0012a0310140001a503a80015501815110b400058501d1032603550303030728001c0c0c0d40c11040d000364075103000c905d0542d07803095251003080e1240c102205500041e1800900c2c3d482164400190718a0311014045400300c003140b14030485201e2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 203077553 1250 203076303 203076323
    0xf12070e030f030703030906060b0301172109060a0306080f010c020c0d0203060c0f090d0f0b0a050f0a0b0310060609170d0206310302030921030301140d060c020a 71
    0x850906a4a440d0341e4180c0030702d50700078000d02c0d0009100313401c000e00440c441c40c0c01181d400d0340c640902900760001e0f0081c43c0038591100100b2802da40800042003406400c264007146004802e02007603032072046000346409260006030b0024418000d810170801040d076030013100c04401364400e1aa00034601c02c10050014084c01310360980d1450101c1c0c0e00403a064000340901416110807104000f9640040b98596a80d08240040700a50751101180c40b4518020b002d660007404d0540b41c0a004100010b0118140500e40390611940040c1e5424196000042480005140017040f0029140844a18040c950380c0e04003400403840580c40720004040360740c101320545c00414210351b07132074a5010b0701e036180e401603010b01300107110f00c006066148111603003c641680700c14002d02c0c80b0325a1181d41c00c4180c01590001480801c9070521790503030080800010503144882c40c8401d126038407484103124444403010f000300407020a60b1151380362506140c1c030200400130401101c40180d200c3c000d03540c1c256894400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 203078803 1250 203077553 203077577
    0x303050c0d050301050f010f02150c0301030c05010816140714101803051e0408030c010e10020a0207030b04081c05041e1a0403090f08010e010b0f0108070c020301020f1207 75
    0x10800e503416143c00411b0154035142c098011100380824216510461050072100c0c40000400700381c16010350011400d150ba2036041d0f040601c000c00c0c155001504002803e4100010810a04802108030403103262014040c04800d070741142070301852002408950880002043c051400610440005940b083c07c2c800d5882d110011078510446600103004034000308200e911080c401c0da40c00b48080c039520034803801e090b2140c8065246401011090440c0c1c1c0d95490304045013001040340c41800c07800d03503034154030300010501c0c029106c1c412880300904901d14180400c04100c070300d0082d1080306108001c0003e000615408210113044152016076200c29240c440030821084a990884032755002030511080190b07544131540d442d00700600a40402c02a054040342c1c0000700218507004000b99400403400100104286084030b168002c4648546a58426a000d690b041400075511001c54104049111128008603000e44030701a541414043c00203800c0c000c0e0082c01c540a40582250740c0c0e0032010740c030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 203080053 1250 203078803 203078807
    0x4030b0a06031a0402060f0a020a0c05240c0a080a090608010e010b04230901080c090105060a090605031003020303040603060918031407030201060306060e0417033d0303050c0d 77
    0x161400064035400444402c003165011100f40d06810600c003418140c1f400c0e035076002d150242d411411056006802a54141040c042c1800040d00900021a814510f01519507030152540c00d2441c207030a9001d00c041000c400f2042d0038418100150741105c1c0f10fa5586110700c0000702144118003030301e4086200d1200100e40c8440000c052810303a0040c0c03110602e41402c01c52202c0d10400070708459070401c100c14001440c07503102d55043d18001e091100c01041d040300c40b8010003505080582046010303030310038051040b8003940301420400701c80290929503034948811809800100f05a000a509031100203400120326a01d86d00000c100ca0070b5140030001c03143c003240c0011003d001194003600103401040301c8181803010400900c1c070b03203100380000140c80c1e43c1d07650b60a050b038081d0361080341c010041c3c1c42000203001c07940c48040c0c0c0309094150001c0c0780d03140044480d038600440103282d226103408118450400300d181a51801e004108402117141a681e0303140c000c009500040000c45039000c2e910903248124 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 203081303 1250 203080053 203080061
    0x15030b010c030503040203190b1005010e0901050d03021507121a0a0303031e060f050906010507051209151c0e0703020a140301021c0203040308070c030806100e0a08010204030b0a 78
    0x605941d4184620050b40b4200c480d908060020303a80350240e502c104c03070050180d200d800209482812400300314034180c603030310365800480c0c1e10031414814426102001075403003030140341c1521070031581d0411441c001d060482c43d081c000c44283c48038081c800c0a10450307607004560031031140440300d028003888402001c4030030300700b101c10451a0004540ba5060001034081d421401d0480050244050000e01e140c40500030b85031a540000d0b0103160006080c00b9038144045881e034850001e0030458038044096440f5980c07042c0e000200074142c0f50100c0c80c1340b110781c3c07110b2030200701080405a040d107880c000034603402c1c4d42125074403501c641464811070b90729414001c12014102c94009103a50b541a1500300d071651404509420540d00d075508000440d4404a54889020050352900c070040c2c40340391519025100d62805800d400c240302c80051007000103644141242c0e44003100b512002c0c6034a006480c2541d19075183d081e030315031041c6404008241c40c40705501400c1101c0c01030003408407603210740b00514200d03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 203082553 1250 203081303 203081321
    0xe03070f05010b06120412050c0a03091a09060d0c020109020a06080603100606021b03070503031306090b1201140d060507171b16050c04021201031a0f0a0b0123041503 73
    0x4030030172000203011461030704030741c1504002c41c14028030b0102d0040f50181040070300b0300304a01082298401380100c00400d0808900014980c00780c5140c4030803400056000c0c0503441c683c0309444c1d200c22034009458800e401c44a5030741e9015203155401d9454981c040c115000894410b80070307200701040d503940001c540c01480c0440301550042c1203590280c803001c005040d400701c2600e4041c85403841c0050301e502c4c200018505d00194041c00750003036050010041c52440030b0780c040e0b118203806110701400142500a4281121590520070840d401c8140108100019281010707018034505002c011070703180c1014003a00600303607031103004240b07582da22480c4002c65490034000c80012000c0c000c245100014010008000b030150007211440b400c41400141641c0c80848003d5616201c40010010401c000a1511512030800e540030990324201901c65074403200242015080e40e111400c030607080e40203903000e5500c2e20014040700d41480d42d8030041606580030380300341710380c82030211100841d580c4a03115078000c0c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 203083803 1250 203082553 203082577
    0x1a0105030d0f08060d1b0305010203061003020708040b03042406140301090c0e06120106080c0f040c080604021e03040506100e22080f0a23130506030405010e03070f05010b06 76
    0x149446002c180145c06000e070004540d0005580c9481900f050016100d100a510800001d03940f490210b003440706d45442c43c2c5022042c5401400440001102802620300b81c80b418201c15480b565541010121603112540070059a004d81c0c0110300f1211030b030b40103c01540d00000c6000d64034141181031500700c4d21080030140c210716600c0018020303009000075542d0011001041164140030701c080a60840307613154046c0799145d00c00340100c01c460624034052401c41e039089400b00b000c107242c1d85018203403e200030900e0784070b507500003480800300400e02d044c81401c143c824481d944070b1a0030301d403e40e6a038801391100364214401d10301c0020705080301c011041c803c550f485182002101007241011440190034400c8070080c9081c003100b41010402c0019000c90301e100d9403580b4004503045900a2003038103403640d4080b800b00802c807040900240b69a41803c5600940c1c0d00c81d92a80d0b5400c00500500304000340340c906010009a540038050205c8d1048070f910f016400800c1012400820030010f446205202d1103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 203085053 1250 203083803 203083817
    0x3020a05040b0409020a090b09060402030717060102010e15180604020607060b040207020904030f1706100e04020906040303090905060102060103121b02060f181e09040507031a0105030d0f 82
    0x45007050b0b000031600407000303400411485001da000070540600f0350801301d8000da452020170300d10300d0010700d820342226040e00d04500c0d5051005000348421645001c0308405541c0102040aa034402d600c4040822048403e5980c0d02c12035901001050000781c44803150114101d400c401e0108011980c2802243e009200624248490f6a500068211004a9548617500b800b003400540c4032100e0813881240301e0341d12000d108150010240c84030b021207580d4550f00e642c500030409a900c030940360000c91159828261a11424240000c029104c0c980c40243c020102240c00800c15800c18055802e03150140b10034840d59880c40c1c01280d0301c400074800500711000801e245080540507420b4508030303000400001d4084003158000c18071542c4051034a042d401d030000780903410721242c0c46201560381001c031f40704c1055164080308200307603900582519100d5a8450007150802c04108035260056038402c1c519100d989000c0d41940b240702c1c2c2480b90502034012084402030151252102c20b00c10f00441c1c41d814 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 203086303 1250 203085053 203085059
    0x20405011e030b06070809040c090509011422060f0806070206010603051f0305100605091303030c110703080409060e06090412050c0609210f07170405060d0606030b0a03020a 76
    0x84014201c20504014140c0e5005a074495403100b800800000d40161a900c0c0e076044882c1c1031201700e0b1030383e1419400b0000070742018815552048102ea045480c0c0414454080c50000c000505035503c80c604c0d1401000300684072400d0000b19007040045803426900465001d59907844180c85000481e80c900041c0c01000060164a00a5020b290060ba20681c1920080c00c40c0c1600000703081540c1007600c007039010b2882050b00d0080f5000700000b9050607680c101160920344104a041e403580e41004041c907440b0fa0213a0203462080d4100d8520410440484200f26900e0820303c4c3d02e51f0141c01440c003442e08060001c5201a14920194000e08001c1c000080ca550755483d80b0840d0000b1030001c0041181c2005002d440385800c02500d80a010a0005404040448907190f041c0d417440c000d03c0d40099209110251f0380c184040103603084241c100c10000c04141c603598211180d442140c00c1203034042400702c0c004c0c00031190381e8400300954540740c80c2040b4104000003002481800c520000351b0288c407806040c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 203087553 1250 203086303 203086337
    0x2120d0c0e191a0c15010905010b04030c0506030c070b040f0b1b0304030e0406050402040f081c050304080a020712060207050d1b0305070204200d1407050a20061e010902040501 77
    0x82d155140c1d20008a070305240c0907200391810545c6858a00b280400c080005205440c0075104180c010625404d80301d160515503612030b03003481810302c189403203800c012002503845040f4900b1100751940c0b241040d419441c040c94100719010300c140060301c00100d1200001c8446080044000071003801d03d80d1035007140c0d170342e41d030440b84042c80ca4446504551940000591529a80050300143c101520094a17250a0413100c51400780181d804000b01c040b00314034036450a4124088030381207030300b00e20340ca80c0d1600650810380c42e106840e40045c0400200d03201802c00d01503158080d0044901c60010342d00281249070044400d01c08441e05940b00460b201070b40c000081c003480080c04a5072000c1c00204070011a600192074030740440d00d1790070020400080c02c0084204a12803046e032942c8400303540c00c0905140301700424a00075281d40348140002c80900e0a4070181c888030100c10040310804550151a114090000840808802e0f0240301c3c0303036500206503403c40d4001d6400381c5006a49124842c1d01c042c0e00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 203088803 1250 203087553 203087579
    0x80105090907090c02030714030f03010303080405120d021206030f030d0c030b0907170a050c070b04081c0c092108090604081605010f0e0906040c02120d0c0e19 70
    0x6911440b40346800180d90800f40501986042c540d0040e64451042d4189120300c02c1500100d100150010440780079030501d0b0209907030549805181204a5981d20304c3d0852500e080b5203099015810045188a0300340c43c80d40007001c0d50a900c01d905501601c0700c0040c95034514500e946410950014400d00000c00c0c03441d40400c070040d0380d5140c082845128035000c00c41e120f41c180c8441c0c0c00182e4607048842e403c0201101c1c10f801554510007081240303000e11941c0010300034500014240044040840c052016100603500c1d503650250051048081c5803040c2c4005110b41c0d04c0300c002050080f0f400150b8030b44010f5046035140c0d008a80300909403503a95410318154001c40c0310300d611120500000c00e0002d0300700040500d08000803680e82d04c2078200400035111040c0c00380c1e0328040001040d41100f480d1501060950042c80a40d000315015a41800590504d4040030302c0c1c00c40f4100116021481c44030341d410480c0d04030110b40352a08003002c10400d0001202d42442580e01c42c901100c0d04000200f200d800b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 203090053 1250 203088803 203088811
    0x5070201060f1409070f0c030c020a0306021b010f0b09060402071403030406050405010b09040503160816081207110d08102706050a061d0a03050106150807020d08010509 74
    0x800000d449486142071840720b503003900100c58400c00c845055415040000d0b800e50429501d003171041c20341e2407070354006000e501e05136401010001000d40c02800c40d2510f22010000d954030000540d02d03000d216010781d00744107000403002d40c80d41c00d012681c400074029108800c07883c84050140d0241d969100c06200c003940c80b01000322824003d11040d00c95441301413000e58050707880b80d5400300f0319041a051580c291002d00a5140c4109520b40501c00040d00010489140041109800301d01c1240d60a052800d17016a103489002021b600496004010546008080741c0d000c841c0c403002e40d52540c3c41c0890360001c5110007594550300c0015642c07034180c041d01c09a6404400203020701cac0420b442e100d6200709422401d100c540001c4441c103803000c03101c10302d000b4100505410307540a044070349091001015042d4680c0f2080380c1a16103150100c5503114407100380080d50f003000003807200320365a41510113600c1100c91010002601840824001c0e0320108040814102590310500e851b420b0004000c00c1d41c030086c0c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 203091303 1250 203090053 203090057
    0x20108090a2118060806091f06030c11120909040c1809141218040b04090302030301031e020d060c02010e15060a05180f042603010f0b0304050705040507 67
    0x30701c0100000d030b03410404184402e12100064940c0c00200c1003c1c0983d2801114469104a061000d102c8103600c800c10380e601c1042101c03c1410b5031070780c451035607010800c001e02140200c0f00c1300010400039050381040c00541e140d9034034440131300d200904082d00c403540c0658a4000721001c00c01c00d5020b00e800e50320503800a002c2c800782007440d83c1e85c000c1650a5100e0300c0b80702c0e0440303071200480020b01c2a10440b8010200450700540401e52420840007124840d508503005000e0841100030019120342d801034800300300140080101c01800c0c2000f958030781091004489a04102482c104005d050040c006000b42d80a0544051200c10307030340d000041c1c80074003012001c640d6284030f2651804030802443e0848030143c030801d081d6040000911030303d1081c54100c280160118180c09000d04e51881c0c4c42c60f8443c9000e201a0710036190b40c90728010b0441212062a40d12002d91046280d0300000e000550480300b44c2401c2c024116925071440500d8001100c01511a4200c2030040203a81819003009038810898 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 203092553 1250 203091303 203091313
    0x408091827031617160b060306060906040f0b030610030c081c030f140a060503070801021201090b01090f0e1909020108040209060a09090b01090e030408070b0702031501060309051e0a02010809 84
    0x2114440100e6007180c6044000c01c2c0303c0317803401814450088100f5402c842c064014184500d00b038400f0485a100280c1407a0007242c0c2c80719000111000c5ea8840101e8041c020290b4000341082c03041013980e0203280c0410b81b0020380f41e4000040c8403100180313105035009100c0700382119010a100640003403943c2e0340502e82d01511030310942c518507044200144a1108090700284460514040c90716141c0240c1108207079038810800d001203c40e100b1502c03411aa4007450101d030007c410f50040f505500260300944040050080200f00b0302e42c1258914403400b18901d80c00d01c0031903245c99480c1500c1e000040680416a0180410050308042e202240d0020020b40b1403907041d6038401c0341100f22031003a0020384180c0400c0006105140780c40c0501e41e4160304140042d4105070400d20150740380c4a140c03180a941041c0040c000703046480502401480c58440580c1c0d1a096940d40009006003050003c00ca40c00c1c003559099004020210b100e110746007130414014000c400d1550300651b0307290005008a0154421 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 203093803 1250 203092553 203092583
    0x30709090309050d0614060418080d1103070f030507020303131101032a02070915230303030a0e0f0d140c100c02150a050105100804080918270316 64
    0x1340050b50004288540340000c1c101080e0b03502c401c1d400c4005170071a84528203041d6012003203600400b60300030703040d00311a40303542d2400500d070400020703c08000340c4003000780040100102280c0041000c07200141540f8148091380c0c9501040303071240300403280c0050081c2c10f2178601022580c0210408220041810000344405485070120400d0302c1012072099402e420701c1010005a0341408250002c2601d80e00178440c1c50f15880089100c8000350280340705170000d007900716410b80c098004100c588030001d02a80e5603418a0f9440d90080d094200700c040f000d00c22088145980b4100203880e9490083c2d99454400320100d184a049090f40300e1400031030288942440750104012610a071030307500b0700540040c41c0f820141c52652011640080c8030103481490301d03004210741e442d004038800a40000e07141000060740c0342d140c20307a0176010300802e05030402c1c2c41c00034034944080360744602c6000d129105040e41c0b4041040302d030302c4c0707841c204d4107112410781c0c0041c0549544080f00501c81265944602412489042 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 203095053 1250 203093803 203093809
    0x304050c150a09080307021305090a08030a0501050a0503030307080612120c06070315080c040c09081603030e0409031704081e031005180402010e031f020304020306130203070909030905 81
    0xe844410100420400a414022643c00c038070b4000007001013034051402c088440d00043e5008071001c1d440e0000a440e200018414136051008810656000c1d10306501c90030076000d4100200401d02880d800703600182d1000c07489107400010f507442440555200b8031960344040038030442c2551111050a03034401c039560380f2003440749407001d01885642c40004011903d04424010103860007160301b00320820521400788038000c1d01191206005200b41c0300481d400500e480d048130700c0081c41d0303c071807203d001e02404c00c0d6002d100d00402c80c0840340640d861001124103102040121001c0020040100d666081d03024001103402000e80ea020b40070358941303801c010010303402e000110090700030908031044c00002c000d54180038001308805001c0548800c0681020702030340a00d038103400307800a81031000415100c45940c1d02081407003d00905165902400a11041050b0203074106a40c00c0740b0900560300064109051410901d506e03036002001025410f2500705500300410f540340c001c3d030400140c600c1c046900d032 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 203096303 1250 203095053 203095069
    0xd060c1103160606050d020306040611090604060c0b060108060a05010c02040207021f020d02010908250c090902090615030f0703060e040b0405010e160501050c012702090f04020310020304050c 84
    0x10400407180c4850070b80c00d14061085844a401503881103041c1011103000d41c034005400e41d80030354807880c0000d290a100b410b21103c0c1c050700036803a40c041000a4013049480e0300131184115107104120300c60303036a203903100151030000342110b00c1500b002104004011a41c23140020f9159180007800051401c0101e0f008118480c80200140d400c004501e1040c1d20381940c100060f4500c40d00c0c070700c002c02420307000703039521611407080c40f801032500e10360803140415488a02206002e99640500d105d8002c0313a8802080001c1d0001c01c0e0309078070405c1c04200003100e43c1003488010112800c0108400d02d103540c0c000c4100002d90010302400100750361030601044003151b41c08128021400b8504e40d10061070a46001400d5410500007a9110b4000514010080c181c02e03a0503000d4031001d0802d0351f190909843c02138014a81401003408010040041019920145401c0000706000740c9580d090390340c80031000b001040c42554001d400d0340c8601d04d000315000150303001c0c5400c24410b0080d954905005000920b1003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 203097553 1250 203096303 203096317
    0x7210e060d061d10080d0203070f0809040e010b041d0a030309030c061a09090a02031b042309010606080c04050603180a140705040b060f0d110301060207090605060301050d060c1103 79
    0x50f0081024007100c09202c000d0400101442001001c003090000b40c001d440303020300c02c1300034071040352181d070402004400029103040c910080e10401088155003c80760107028840e04d103d0250f0701d040240082c60300d01c0c0c880002c210301c10600030a036101c0346070380c01c070300400480d08161308010000c440d240010f02039005c0c000e000071f06001000d0044610404000d1400409440d030205075100c40003020043e00c0c0400e000d01008910351340b4001d10844480418094082d0501018606501d940c81c00c0c0448080c0c40c20501401d1900020068261a03144c140c44265060307515600c0c01000b80000c1000e031070706500859100884040f0b00720500a20103c03186040c0c070900d011900c50007401420301c6003a204000260052000311000d0000d00002000300751244540104403812000008003a00d4500140d0840b0713a0048800e9011980c0707695616000392074581c240102510a0300b040c40004a610701002a24140c1d50002c0a590101c0b0055503110001d141d000440b00074002c0e241c0d8004840181030001d4400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 203098803 1250 203097553 203097599
    0x4050d030f02070603020408100507020f0f0f070b031b0901180e06040510230307080a1202010e010228020c030706120e03160b090a02060f07210e060d06 67
    0x4200c40e12101a0510f80710350061820548140402c0207200000100e44841d20541e140006844c2c4901c1012801c0c00c2c00d02e802e184061040c880b0341c0f591528002002102e0303510840984a100d612a603500c0624401902d200304c8940c1d011594040740030000008180c200c90504010750040b520b0307520132444900c264003400d91613003802d081080c181000d010ba250f20101c982e010640960410312a407030640e800048481036609954006002c6071401c101080280209c0e800b210301c07070082e601c0d110f81c0c110900f010100055080030031010400405000303441c02446074160728054180d04103400c0203544071205805046100c4c80d070f00c2c0c024a4406000b03600117010b1503911480410586050803080e502c0c502001d039890b51040100c2500341c5400c0d0000f40c40c980e4082000c4030907840d0100d10701c2c030b40841c029020390f12440004010f012844040010500315200e0700e468480d280403491749000c4003000344103034400306102c020303140c006103410780040c0226849140300092594035440e0000308a52104030b140b503 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 203100053 1250 203098803 203098817
    0x9020108010e1e0f0f100e070e06070602030c0918060f0f01180e01170f0d0e0a0e0c090f09130210180f0614040605040b0306011704050a111c08090604050d03 69
    0x82c2007000d4100345a0b0101b001503841c01d1082c545440100d480600500031030402542d1601d5410580d00c0004482e0f070250805025510b90401001021080d4000e4151902c6443d13071200d4071201003480c0380d155120311401444042509001000d02c00c040010034601410000d0010145200c5800c0c17071401c40c094484501c02c17510940c18890881d4882e40b2811403903085a10a0f0100d8154550000f044100d411781f42c07814001d1a9001c902007200306880c2e0300800c0410506208004616801c40090154400304032403101d84486150188040d803041920001c03401307619100b48001604007a0100d45842896180402080d840951840040341303207030700f1641592401000400120360301c07600345401c0c1048010103d00e41484d2240180280c070451160140e055004000900c1e00e078068000030360881980781014a0300c2c0380a10f0496180d07070303101c14221100064050710801c0340c00e1107800e09000440d100090f00c4084c00d142c461110030303001000e0981d031103001044040350541300c4036048400e051003500c0d510 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 203101303 1250 203100053 203100061
    0x206070c060206130b0a0e0f1b0a09060501200f010905030c0709021603030f0603060906050f0a0b1c0f0f0305071103010504021c020d020a121509020108010e1e0f 71
    0x90412074064544034058100340003c07408220007084c3ea50b0400c4c640711000421f0095400c59900300b5403189408640350161010300c208020000d41129402a012030303800c1e0010f034441d41078a04603002c8c2d0003040e00041d4083c18245880c00000364455a020350002110071040280640c1c5096822859003102c03c1d800c04142582d05c2d01c802c028920103030950b44415130411040b41101d43d4441c04000000d01050340322801c2001c0300107154403403005160130003800d10809010b03080c08000360600f0340b100b18182d40c05070001201c0841921642c0b046c4800104600744904210034000c419840311082a1424800f54116500041d2030807180c0364501e03c030b901c0311510744145051040700291081031240c0242d041000f0800140d890013040314042e2040703002e501050380303640085882001503d00c02500516101d03000310303007503040b002181889403003850044040926482c000c010340d000324400a02081800005204030001e1300d1104c1c2d44070000c081c0f440000501c3c095278118260007030700c0d83e6120302c16442c140 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 203102553 1250 203101303 203101307
    0xa03021e0102062a0f1e0a0e01020a02130b1f0f09060207030f0305030a0b0904030e0f0312070b0711190c050339030f03090108060d0b0408160206070c06 67
    0xf03964081c482449052007016040c0401240080c2901060220407000031860f000d049031105803028070500000709004807a1641000c000c0b6440745941e0000300740c1800c41c000f01584002645250740c0da0180240402d951000e68600c040c144003850350383c0c4009404103001c8100502481c2c1c46605200755909604858a05400b42c4100380342d4100308215003120000f48003044130204c5805180703605140040d602e54a0215120050010700e1806a00203a5035060000385075000d0083d0300c50382c070122280320300c45a50404142e519500c682000100c40750500c441c8000c81c09030255154000d400341094407107600c0f0301402324100040c00304410041c030503e203d00414400c28130342c498040c0c41b06030f0007820a408078182420344446007140500c0340030040e00c01d13030680b411000e54012403043c016048070410340301c101c81d40d502d80c0c10000115000611110000b035903407501d12010a000781d040380e109031094407641c9606405500810201207460903001e140c40c010303255500241413050007504150f03191800e103480 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 203103803 1250 203102553 203102563
    0x2031f0608060405150a020702040903020601080f070e0408090f06040e01090c08012402010e0313090c0206040309030b0408040e04080c072309042a1a040f140a03021e0102 75
    0x128030a0b80c0070200300000182d00103004505081410b003c440c0a0b80c61042040281c403c4d454000d41040c2402c0703154042680000784141038411020980d0407440400c5131042e0345a0540c41084001175400000c280030801d500010440c51358090104154a4402c1c00420f2041d442640040340700e25910f00100b1010b0214850301090042d140781141072075240c001c0c610300707101c40c0b408180705031300980d241105024000d40c000c140000c044000c2c4d0b5100c84616810084503c0c40388280c1c0702c0c140c01e0004c0840036510208080e031083d039054a906039507609603142c208401c04000c4c1308449031001040080f030002290321303001e417007144581d5a9035600e140d84c1100c1400c00002c4d82c020140442c0c5034501c01403050b200e10800c1d0719134505845000c0259a5400c20301da4017240f40681c0724581a44d40c07000005a100b0340000c00948200400000c220740c0c0307002d09498144100d1040603c1c81400b800c0501040012031076501342410000c3ca5a14250346a0700010101c0f139131061940706031750340420016415601446 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 203105053 1250 203103803 203103809
    0x111071e03120b0a09050903090f0f0d1203020c0703060209030f01050106050412061404060e12030f19020c0d08010603060b0403020312070302190f1e05250302031f06 73
    0x4200c1410055a001c0c2607080c524100101003502c41e40700070101d494000780d0400903c049a418001d600740311250030303101d60041d8191030083d48900caa64245040400e0403a028000c003821445440c0d4240c0c9911100c01c3c0c03401445c0c801c15808201c1043c00b40c1080000f6406580510f000690700e82203202003529081500c04464550707410701e4010001c268120094504698454400d00e0003104c1525001009124801d0801c80780340703504042c403092003070b80d0b4400005000321004a80c4c1c0120481c0804541d4001180c025454020050001305240b4050540641383c43d81c0c10000341c20304081c09400c60900c0c1c040300b4182c0c0042c02010040049030740c10300404d0018900210481d103000d0450300860307201c1c64180595a040503000820a080501c200041003d21855122501c5145880d01d041e40041c0480d40054403820f134810b0f941c100c941c1246000b110740c00c0e4071200601022000ca003450075900c950700003413920b0b52072040380000540c50034080c0e040c002d1050464542642010208001102e080350 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 203106303 1250 203105053 203105093
    0x1504080d09230123130311030d02061902160203100c090b0702030a1101270303020c1e0121110903070b0703090b16060207050a0605091603080f0408011107 68
    0x99161070b240e40c0040300500311144540010440580d42c3d610b080051180442c244441c160708500001404007001c0c041d1403020b001c5060300d4070018425070480c0c5d6080c0503540f0b020141e0300c2e0b0303c40340402c0c0690750007846e89012041648007605015000203080244441d030015000d40c5900d0b125941a5104500d4009000300248039400e0080782d07000710b039a508560100510a2120b02c40100c02a0b0003030f03040342c5e00c410b01d05510309486201083e85c00703c0e07403006210440143c466401c94064a151282c00025000c600340407114440995100460b015030940408280e00001200d154034041514000c460641000c66500c0360760300c0c072403010725180c07010350b5000e0400c0000900096002a40c01501e05044984400d480368650b8009440200b1451b007440300200100e100103500700401801041c1c152940d03014000c200121b030741d10100d03580c40f4010003059603006102c1c4001440040c08040140c0954400d842c01035041c0b6071504045030031503078040518a0818004980c4004000c0c410300d14849002000c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 203107553 1250 203106303 203106359
    0x30a0c0b0d0605010f0203041e120507151409060a090302042f0a1e0207090204031a24122404120908030901110a0506040809010e090606091504080d09 66
    0x3901c074008c3d4010707880400d903008841101300420340383c41c3c4068031406410b041110340d646410b0f079940c2800c3c402c0226248490060b000c58502036810340390040c0312103c0003403070a0340714820005194403641c000c01c18020220400f00c050b0321103114800e140c4035118003c2c0c8001c995080500300d03986151281d040c151000b0804800c005c0c0d84400e000044200391901d10705000c8a503d01641890342c50b4102000b0240301150000c00d02078444030204da062241c0c0704440c03081e02c803601c62500042c1010001001c00c02e41c1d06c180005420300c003860b01d2642c1c3e602c100769564400c00b0758a002e8441170203181b68200580040034001030011485402031403c4090600200c45440c011200d0348a000d6075940038180100c1c82560350310320106024014250341d104003030310218039180c540360707580340c02820001d4001120b403440e01c4020304119005500075040203010f036040c000080d04100013028018120030442c00c0038000003034100d00400210f20281d08685800f400d80f400c02e60700f05850340e0507120001091801d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 203108803 1250 203107553 203107577
    0x301091d100509010f05190b0d050a060501060f080403020705011404030615050f01181505071545060b1203090f0103050f0711030f13150306051509030a0c0b0d060501 73
    0x840e4055207c1c0810a000400c0340326050b000070343e0781804004050600e00034070800404002c0305030300981c140c40d2070b621000900c804854044910340011075006025a21641c070520256000700d8000704541140c0c02020b160544a940f60703416070b03480310401041d005040c1e07414800ca20303100040c0c101c050380a00e807480510220070b08241c0c50500394407501d040e08254400711803000744540b00f01e40b022a007142e5070044010f0000781d0b007401030010003030494481e02c4400d1088501e480803035a101700714030351809440a004500500d2070041c01ca01904440b255a070b400c0c802c003503403143d8580043e020119400b55868403a00d03024040003014054580e41090b01d4201040701080e100b500444d00a985071030f165a4400052a00314510f1245c007400240500c0d012a0220649481803a01c605840d104420080c0c00002c80b8029000d4440030700542c0c1c0e0000746c5007418040540450060007880703100a003110045042c0762513001c4c80d0785154020400d10f0f02d00080c1d5620380703081c5020b000004d1101b0719051200201c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 203110053 1250 203108803 203108821
    0x9060a021005060904020a1509051f0807140a030203090304120b0417030c07030e030c0603100303090503210d1e06090510050312180307080304081606050301091d100509010f05 77
    0x4124001d4000d0748c05400c8003080d529104c4c02c0c03014090213010342281c07014000003040d0b4184000e41013945000030008000034500601ca64880b200804003042e07140e0500d00103180076406500000e040c0c507010700c4180300c005000b507400a00032700d02038001e0310801c80a041c14100030303c44031405103803002104401c00502c515460340e0380450390b40c0d60709403030403441b1400b030000000d003009000c0d412075038440303008402c0c002410041c150100c100e1b8881d032118612203070380d002030540300c0195119034528100f0b0400d812500f180342c10020a00e6405000000621221f030b84042038403010095114003a0513550042405001400e105598200004e42420300c0c5980c03070440001d9942002c120000043d001c00b05ea401d56440c1c81038000c10102c0d60040c2500e079000d0300e0380242d50b6280c00030f22840d02e09100c1c0c00c40314034825001d080003005803203460741c52510b981c0c240840c40c001b405003044034010700011a1b42110055500780200c1e000820400700114803410b040391032600350b03030b4500c00c1843e02600c2c140502c00104 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 203111303 1250 203110053 203110069
    0x8150907060e0d0c031103211608070506010303030609060501020a0b0105150d060305030903280f030908060f010f060e03060415110a1205070305070804020405040809060a02100506090402 82
    0x25469151000281d40c01001194400041c0c00b0f00a02c2d1142c800e03c088104048840f1705030043c1d5054048503025a419155105510b64001590b03070100410488900000d503e400c60341c00660003010680c1c603101c0140e813540e181103006d07801038001139600c91052060601602500000301402d20041c6024856a01ea010705a401841040d1140c0050014003034100341001c140d420718030b00240d040000c15500e091080d141d40c4200350320352286c000c0d410300713030503102d00e08070201c620180d0701d12a5001800315546617406c10340150800e40c144000a04002058142007151601c1585211100e400c01d514120801d001d007100c0b42c000009102a402141c040754400068065105401080c1c01d0400d14110b40800001c3c44112020124060002080301205030028040b29001a00702d10802080d0785803c01202102c5c02134030300000040031000800c0151130103411050700280200503852030000c5050008140740d0000a100c80541c0201784004d000003514400c242d030194095404234001c0c43e00d940010149 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 203112553 1250 203111303 203111309
    0x181003020f0a030b1f1208090907090f0e0c090a060e1009081015120804031719030b010201061e030203060a0b0906010c0302030d05040c0302040b0a0305031c0e03040b0408150907 78
    0xc002505005d260b011410340b901c0003403030346088030030605d40c06007008000d0760f01c07160b00c0314051281000442c107080d2041030b0384000c882c144140e2102c0c00d418540100102e580241142c103240f5800c0c08401d1702c5542e06030301280146031a4590543d180032250502c070080300300d00c034181c080c40340d4010304106401003ca031001c04062412400565880b4901d100b08240702d1540200140b4600706124004003c034a600400c15a40160524000880c800c83c001e1003a12480d03802040c0c0451070021510554000e80005890b80c4050001262140d19071002d1010304d80440313144990891440d108200754203050000e1a04a440c4d05ca0601c2115401001b1074508407000e0419130403c4010310521050600c01e0068510107480208280102d04060800740303c1401203000c164480c2e1b10301441c0302024584042d20310101c0c0e501c0000745050900003030040074120b195401d5081031540341d03140744000f141e041c0014001307810354007804c0c0e854500300703902c262034400480c030307441c80c140c24001c284051050000759610403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 203113803 1250 203112553 203112571
    0x614040618121b15020c070b1314130504060c031a0a140d1208010513020a0905040f090b010b0703020105180709021b0609010e010b01051c0b181003020f0a030b 70
    0xf0000344006528045581d0000207400c036100368020320a480410f400800490100d141110841502d9003c40c0c0300300e120748800c45425150202c1700700000318503030101e20190100113000c94030451078000301d00140c4504940484600e40d86030030607c24140c052158021040100c0c00710058081084d01280720045240222a041d601c0d80115080715036401e60003444455002c1602c206948402e04080e0180d170007030190034401e480c0c4a807034844c3c0e040c00d4800e507080c0c03e00303a03502d0498180c0307000f00380300080941e50009000b270350310f030a0503202084040e000c0600904441000e90350f608c007141402030844801a1450440300041c269004803000300040000903510365200050b980e0102c100c007003459600ea1000301d8968060101003041e40c040640c00382607030801010080c05a0500c01004558610030481103000802808040d00703180c0f2282d51050003007000191622041d2040002418685001120072158500804034203000f1418209104182d103041943e0ba500f100781580d483d58a4503000803d0484 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 203115053 1250 203113803 203113817
    0xb070c020306060405040f1202070614030c18010306050301020c1608010606090b0a120e10060e0108030a03021b0102031f0504090206070206030709030c080d08091902060c0307061404061812 83
    0x420f220400c08080c001d19405500c1c03a0441040308c4010303441740103d105403008200b2000c2000d83d404a160b00700c07403180c83c0d030410407440d1418509402541e2854074203600e041640c0d405000c189910b00b44010301c0c00100b45d10040400c15690500c0c20524000c1e604100c5c000e07410a10100500740d045902c01e820f80d00c1070100240c803070011003812a5a140c03070140c3c6002d29030801d10b83c48034075540411007240b01b1450b8481032100c5034070340880c891209800e1040e04241d510130800140460310a50140c4068951800c1c1c5a0714106c2c10b029090990f0000d592078864191414980c05a048480201000030031096a041c41002110780020b6803d0244a601a009000000004100c1071140c00d107070000c4c560207003458a0b400e840e0600d0542e28a6540e5144c2c003c5406003001c41c0081e0000207402c1a411184180c90302500000e03401e100440d00002014a0b5501c41804003100181c11800b550145a191210440c02494242001404e4456030b801d185441c2c45800220008030f058102420040442801c00341 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 203116303 1250 203115053 203115061
    0x230a1410080705150706110406080f010e1f0b0406021e0a0b01032406060525080318100e010b0a0902181002030f0f04080c0a0b0711040e0114040b070c020306060405 72
    0x104d030038413804200410461428484078102c14056010f003081c0d0b445a41c511841d03a0b1804c80c0c03001d03a5076080c003880440508508c00204a000070f05c0402e40c66007041e50049072000e5507007245036a550419000207016810243d80340941d51002c2c4503204502050200410300c40140d5110b000c18100b0601015100c0c140d0b1042201005030084044803070080d1807001080126520040103109812495015074411406005401501c007010030182c0d0301c582019a841c0f86d03403507441e00b20245100d1010f407040030f40138141115040c0c22144c40b42107820020200040745483c00c090402105400c5071308061301d51403040c044840351030a0340140c0914000300380c481c2d1a00c0714080c0016865801b854600d40402c050026a0340c0e40300c0700b1103024004031203200048130494900b0504118400d156801a40500101806144040354801c1c071003a203001070107480000c0500400710307070500f510412405c4000c180444402d002c02c0001c183c00369075200c4103030302d410a1001c041d607000a032124809400e162040392150049 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 203117553 1250 203116303 203116339
    0x1707020411190e060901020c100c0f050304080d090e04020d050111040902090f040615030f0603020a03050607021015051e0d140f0c0f0103230a1410080705 68
    0x34400702021950380640781c0000068100180d90040201e20008420440030300750b60a0a1040d5511002c0580145c0750354110031b01400491884008042c040180d15141e0320049151a044e6107036403405500519903550400e0006403034045d209840340104280850101300380c201070740c015a003041c0e040713808000c00e82e440e00b0058090701c8410201c40c074600c0b00150021fa40007056004001e000ca00b81e40c8201c03151945400c110403512a8400d003440c0c0001d13a00901503441c840e9100101076042844001103160301d98003c5140302c5840c0c0c20403140c0758454400c0c8004a50108020205081e8a20b402d0151000d6008213a2040c0041e01c03e0b140181088412410f1000c0c0b55401e040340b07040007405001c603180d01424900c20502c04840c020046002d0000010301c0040007140031207030b03900043c00d600001580303400110010900d4079046001151b00d55080ca0b01ea44803100000e02030401c40602007404141c0c1800e0100b00038019141c1201e0021011040144140c00705580c2c00f1101d080f206401d4110440d034030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 203118803 1250 203117553 203117561
    0x4020a080102040b040503010b0a0803030106110708060c0a030f0c02030a0c0c0b03161b0308010b0906071704050f01111c0c05030f030f0c12161202130501081317070204 74
    0xc9400154008100410b01c01e20660140c011264110000d0004a050b6418030000c0c510328020710490f80c004100511515010346824800b0084000458403807690340c0d00706d81d05140e815a00d01002d178900040038904c40f070307040c00341c400500c8040408101201108001a42c0d07403150000000510460390404e505201000c1802001001a118081d40d42c0c600802041e441c1c0c07401c042402d0100b698003903c50f5005201488a00ea0668140c541c82d4060f400c0615072412034112411007a8426000c01032000020a4045204044401049026107907420701041003101038104004604000340300c1e0719003001c06800900d20041c1d4400001d8805d140580503000c84090420042c0a0918400080c1840119604100551055491501141440d01c0703000c21014075114243c143d1407401200008500c0d02c88011082044003101b07401c2a82d10701045d40949020780e044800d40490041d0103d20810041d60440445a84040c0c0381c05084010011a0383d40e00c011603003c007400000040c0407802c4411034480c0da01c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 203120053 1250 203118803 203118809
    0x31222090e0705040c0e0307030b0703110c0613061b0804021e061207020a020a060c0309050103020c0a121b140d080402061b03121810020a12050a06031403071209051804020a 76
    0x801d540c0ca90740c2724148462000070540300000040d00e04585111041c45101c251440e01f04008083d00c455115500d44440200301c03240142c1d0115038981084003015220920080d06c004262100390030b91030305004001c0300b940281c04901c400159041d58a9060740c1d00011107000841985510945440c4d5180407860f10901340c4009403c402c2c0201c010a601e43c0122900914610036951321000a4a4030011426409211504407250f8800c1ca0408002421520610741c194200d140c8960120ad803c031700b030700f00504995820b581040c500d040d4104152414003000e40f001368181440042e50409901084852188200180525a0344000f10001080510460b50300002d0701c442503e4500348104001c0d00802c0030f81119119119001841130702a01d907002f82d810743e1540c1d8503520b50064040c2000e0000c0c00d00204004400c276138809000c00015400b080f050042041ca000071508e460140c9045010107001d142d1250a215454400308001c0ea122070b40c0c48611048200440a03c1d02c0c0c40c40451241d00c0075030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 203121303 1250 203120053 203120059
    0x5130806091501090c08240301020409020c010e0a0803010e070c02040c120c0c080a21020706021c060b04030303090203010e0601090e1009050c0f031222090e0705040c0e 74
    0x206201d91140c000410004900c000418915503903600c491600c125a000400800840d03c10400181c00e15017860900540c0341c60340408000c03070501000060700320303400340e00503400055020400080c10740e002d10455800340700180041200341c50984850380b43d80030520440e413040c10703a080040c99051082000300322159020780180000e0b90321800c0540400414516003150a141114000c4050320906204001680000c0d04515101014100312910b07004486099020000c1584941480f0840e200074101140100001a22030541c00d00340c80c070300244d80002c01d42e140c0c1441004c0c0051600b00c0101c4040b01e502d8140020382040900c082405070210700f0f280002409280000182000103801c80011100041d040e25030705100d403000c1d0000c41e040004003821560000c040c965203418526006806171100401300d8a222a00c00312614031a1b00a2070025540f0321146103000000d83c41004a4010300008a41030001c20707401021941d90b00d034a88901840780743c8803103004000600a04240c40000005 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 203122553 1250 203121303 203121313
    0xb0102070e0a06030b0f0402010e040b03070b0f040806070906021c140d0e1212010e0603070e01091b030216170d0c030504020f0a080d050c1501060c0203120910051308 73
    0x4114910020711051001351045d00d41000000c940d0f0b4941c142684c40380354140c45a00461002030140070041a42c0415640c06100e082c001040b245080409043c20b0140031003095522824903284600344500907204205200309203000784203560300801e10a441d1702620000702c0c84803180503001c131346860b111206224220340000e481d005007a016005103044001000c211040324924076445a894420154680f07070241240c8014450801da5403555500000c00504981c001c41d01c0300700503600014281d0221101d290b0f03170b141030092a1419440030100c011542811410184140b149515040d101c010082c00031007102c0c0a1340034500d00c1b200b40c80e0401034800c401c00c030000c2503604c060010142914240c1c49440002c414101c140b5055507410141c50740c01010300303040d80302a002500c2540000c00340f545d0134050811007192102c601c8542c240204a00d07503812200101d42d005144c2001d8604c088034045074400c100030760084c1c031414403240038400c01e072614564501d0340500140800c611a040b00803030307001e0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 203123803 1250 203122553 203122561
    0x140a0c0306091a092802070503040509070c0303060e04240e01060603060311041107080309010905010903030903080702060c0313030c020931030c08070f0f120201060902040f090b0102070e 82
    0x1143e04200f500300402c1c0c1e500c0e00540c481c00403007103a170000000c1c2040e0740d0304294400c0030012510740150916031f00c6502220b0401c3e480d40700245d032070b942c12520100056403101d01c4106050b49400f40000410b030007198400241002c1d00ca00d42c0e40251002182403050f1b12021101c510702c9240c3c800c014500900d4020400c0e20b488150060280850748803d0307449501c074001281c082d1816108864800355034400e014540101940c504006400040c60a540c55503940140c1012480030b028a806c4144641e0340003030048045e18002c5c02111016150340219402a4100120791809008590f0850200c64101000c12050b1804441e4001302e00c2d0001d400c00005014030410080f408001c01400c030900c0b010b080189942c00c1d030b00e401001c5160000e40090302c41d901180c0800d803031200034a5602e005d6042504032210688034802d21345829030b000c442402c011801d41d4000c50342841950080c11803050f040d0700e05071034160160142e06460180520f059a2a245010168001c1049500900f4003040c0b0041d10b140c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 203125053 1250 203123803 203123831
    0xc0d080c0111090f040c051308010b0108010608040308010302120a080c010614060f030a23150f0a0302091504091202010911121e011d010504060c0201140a0c030609 72
    0x44020000380d801d00c0089403202140301c00b59091104050032010a03441c481c41088050a040c050403001d005003080395100300880618540007070103c0030004540c07141c0801c0010b0081070145d0100080101800502c00000e0b400150700c0e045a404890703c00c0e078000d820200f9030a102171080010000d05002410802000040d001002101d058110000030180c4c204148280391142d0314807031221000801c0020300c00011a40410548441144040c0c800c0a6103425111800f80070380300e034101240d03a404544101e1800e030f110f15601580030741d4080c4d007452940d40880c20621001c0c205903000b400281c524030881e100e0f58454000c1c1600900352844070455050041e00070301d0140000d0b65031590000d07408000f4100300080280303500001004280324800c5400e0703041d031220902d80e513103445c0d501c07444003600d910031740002c1000044081c4000111800d08d0302c0e0000c03c540310205801c040da41481a69203420102103030300350707224210100c0442d690076104800c03002442150081140c840c0b5021070469003207 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 203126303 1250 203125053 203125057
    0xf0f040216030c021014030f09010612030e280515070506130c0b07080d05071202220915060c050708150402180903031506070b0106030509070b09060d020703020c0d08 73
    0xd40240d0305417400102a003021180917180c0c990812820350100003282c601d0740c0e01d010300d541c0a0030340c40001842e107031101c0020794002090202500005d01e100758031802403400c200c40c400c01d04420300c4c41c2d480034030f14140c5079031010069102c3d1030300c112111866201d102144400f101c11085c0e001d8165610391520216071440d16404201c10785040702c40e60004120140d500e0304807420650008140c03030404600e4004103000c0c0c0300c0200f4030030030083d0485280c2400c0c2040d0000c1e02160501510000a0000da40722608820729140c0c44058940e0400154141c01c665080007481907620602d000c0454100504142e440c250071a8130041d15441036414240140c2018440c1c1401584201c400001541426910f81003504054580e4141038100b0800f0600c60800c016500248010250605003442242c0c4c80e06200c2280c2680000042038445003000b0f200602800010b02403c03000b01c6a5041c090103402103001030145042540450b40d0024940c1c040c14001c10000002d140001e10000e038010351498014455 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 203127553 1250 203126303 203126327
    0x220801090c17060115050d0f020306041113030204150b03010303090e06120d05030601020f03030c0a0212160204050a060819030905040c080f100e070e010e0405060f0f04021603 77
    0x44a659600403820b2000c162018591919400040042c0d03424201100342442d0100c0740c40e01800b604200c00d0781015841c1c0600350844000e0000103031645802030601007031310042c014910107034404008102c00c02000700c0c1c046040d650191000960040c0390f41107003602c42e01c00d070030100a420010000000701640300c00708400359088418401c10985030030040c0614400281c103145119008500c42a0303480780315001a641c4660148101c07045140c003040303c0703030441e802030303c2d15020030400182001007180c040015030b40c0e0b440800c102601c3e020740944008001d0a1a1400912070f680341c0d004203007603080c0b0b43c1011010300007210942d00d5401198401c01741240100808030049410308070000380a10340b610402030560850748504a1a54905c280b030000081d0061017501000349005010405440c0c14120320f01c503003601c0c1c940d026403442c14000541342002032011039104500b061b00300710858660010a00d50840300765420b07042d00c0000c80015000c0c2c000d0340c00410b12082c0340a00c4505150307000c401d070490703 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 203128803 1250 203127553 203127563
    0x7080604030210060e07030923070e07080702121804060801140603010b1c150c0c0c080d0f20060705090906030708030a0c06060e180c040b1522080109 66
    0xf1003590600000a6402030301c80c0441d442c0c4504001401c41d4002c2d00480c00c400d21030540e8882129131a41410501843e000c00c1582c503a00074070041c000e50350070282c1d46170070040328142001e0b1440c00c2c401c02592003010038031300891084086a000412007150302a0300303884400405c1800842d807500c42d031500812246801180a144140228078a41410703c1000c0e95488044c0100d461544070901035904100c100748100c80d00700d0020f228078880001440384641c48100da5480d1003011001d82041c840340b10035074000d41002c2d0060100088100d4100d015250a03800070b042030a40000d94402000844a5420b070348400f60203032200704101d0641c410001d220180044860074200d44400e001c1c150741d41003502400146920400001803d82e02a20744204040d20070940882e07030f192100007841c40828151841c0611049041e80501e11400600440d1049081560104080112007000408502100c03a14843c052000109081030300c1c0508001d00c0310741030000c1000383c03180d5507400684c0240020102516 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 203130053 1250 203128803 203128813
    0x5070210030f0c090f050103270c0e0a0209030601350105090f06010b09060c1c02031201090515090a02090a0305030a0810062a0209041208010f0302011706060c070806040302 76
    0x543c140c0a4900350003600c408805800440e41400d00540003000c072810420030490900256410100c030325a001401944550203818100d41b07040c0d04c00c0b90b42c1402802c821586030040c070842c001070701c00281d01c6044036001400081c52134000c80e613824605982d20881400e050150007070002001c0e0540015000d50000d800b1030b92501400300c0000c2d1180021b000c4c501d40605c003040752260030b1a1010180c503c900ca120191252840c100c1c4000140320304c00012034002d41c2000c268140d41d1a6401002401020303030601c00c0c440d501d49600d41050034914000101d12410003a4042044024a40c0c141e800e400c001400c01c002032502d90504590f44e8002c031100100203204100050451000d00e54064103c0d20203440d010401c900200c5046142810f442e110a021a840c289540140c0d4961100a000e03a02070040040c96285c1d01000412541c0160403500c004150940c0c100700607640a50480701c0a501c50410b0480c580701e500000d00076108c0d011000f6400e100380d010200c0d59800220708540141d00c00d8003154 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 203131303 1250 203130053 203130071
    0x303060f05220c05120403030f050a020307020a2003011103160f1d0414071214060d110d1b0f05220b0310021606110708070f0305070210030f 62
    0x1004060b01c5084090300b9102d04482c01c003100c1c080c0d411071001c40e038150411908080303c042c120b151141c8112010b41c00603456908000300036400744111504184008000c0d031840c5045040a9625406203000804803815001440c191001300048181e0083d0014004d01100c5444031115005420544a22002d03e039101c4c1c1300317041e070790042040c6c03600102180c440780c120340c0c94030002cac5807581400103559420580307a81640f450681880c14041c410000303902c074009011b050070900c008503070b04261800030132070b400e109008541d034441301c48250950f44900003c103040b8840b0301207200714014400043ca0810094800c8007003003541c00700d2100b0b455690824504c07085da2642040310b800c17003190485440706e14020307244103503d0f03158221440301807000d4102c0b64462170007030041d0f04a92114080580420b101e695400410400780600300d00e15800381c04a81c200380e450785034030b00c0c51722994000034406211103680c00e08042c0510244c0720b0490700105039499032a00c61801601a0141441443d940c41c5000841 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 203132553 1250 203131303 203131309
    0xb060901060219080d020a05210402032e020708030708130812091603050c0109051504051207090c1d0102061e190f02040801062310050c03070303060f05 67
    0x24504031041e0364010503034844003904400b000ca12030082610f0300002046080792074612400142841e01e6160b075100e07502d0f04a945d03800084112003504002810b0b074071003484056500041d4400e40c41031628250903e0741d8000d18407103040fa1f0540142032089002090400c28012140b02031031040c00107441c1d01e14035a90f09207200c5c3c40b200e0002c20040c03d10000784400c0c0d24a54042035a00d901580c00803c41d201014206135100d845421a4022182940680e44000455902c604010003c002c140c41c00c0c1d16500e0b0003c540603241c0501d0158901844440081c48140c0700b080210500505c0c410354100111781000307a004101c0c040039000d05c058404c0700000b05000e5440042c00c02d110f0501441c40040801000148030f03418039024002a0380440700c2581c4140c030700b941d4421405110310703c16006a41d5407030300414a0a48003541d0241d0004003405010000c00d034001d103482c0014000031107159552500c905803d440c10300a542e03105101c0d200129004041603050361085068606400108144039690010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 203133803 1250 203132553 203132569
    0x1107060c0605060d050105130201021c020a020d08090d0602030402040b0d0f060b15040f0f08010b100302070203031b0c090117030a08060a03020907020618010902010f1803020406120b06 81
    0x948400614100060004105203502c40e07900480d009014910300a0035842d103609450064818401040d00c0c445001c08660301007040494003100003c0604518200603806500c60a02c48006801000815502c0b010402d140045400200d00200071017a0012315080003002508201c1d01203000368034280c019295458104000401264490225540c4c1c1400c2e64440c4050040318060f82d400406004104110300e04450181018004201c03502c0d400710b1800d4080c00c0c140d2003682c803c064592400c080302c2e1a94491030300c400701c0000c107424003690f100c03500d2000c280356106480c1c5111042c1240c905074095200045070340032111a00301c0392025140d8882503802c1c82c7c00a030342e0f145800c0da80104075130944640120b900680c00440100000e4900d913803034000c5903500008032200001a0000e50800c0882121168410012190701c00201b01d0420705070f00290682c014075815a050003810020900d003130b1265142e1a004d99405002404190394800c824030812403120382c01ca03407212099000800303078104080 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 203135053 1250 203133803 203133809
    0x303060a05010c020a09020c0a0605010e010e0c03090f03030403030911030606060d0905190804050307060504030c0611010e0f1c2a02120d0206010e330301020705070909031107 77
    0x22200c92510301e004019150f990a02000f2600900380c50340025015009101a0000c1259100a00200c0f0b9091a181b002c50740c1c1600143d1038000d81c0b10041c011416200e54441e030200340080007960721380303030348040d9490306542c07a16516040c40300000b0003003016410380011507000c1c880c111001e240d0058404050300c40c0000c550094200d40c00b440709120720700d800c2c1c00003914079020350280d540c400c84c06642d14102e030340b03031400680e04880c000a0410003420304011510040c100e51801e00e0401d13003555901c2011001500c5180200804240c0b1500c846000703610035002c6072000000c4492008050326299100e0324007000c0d200ba03212580c1d6529444034040e28500d01c0000218201d020b4a10800310400581d031030015040c2c1e00041441034118070385504005071050049140c004100540c50400d01d9403a00030001c040e5100c0c950001c4900d04905040c51045112034a2114203040001840c0007281c0240581c0401a099110718000024200c99990000d0703011802a5510710500307103141b18840c1d458240e84 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 203136303 1250 203135053 203135059
    0x50108070509070f0f30021b0f0a021e0904050f012d0903140423041803080606090a1d010501020304061e0c06020409020c010c180501110f0d0804030f02030306 70
    0x3c2d030758030070292242c600016100f94003c0c1d81c00a000880140e600746c60310079035042e1101c81d40000c0c801e01b03100860018402442c030060081c501e9080810010340c440c109000001d0040d5081580080410800c0414241a120151014082d844d0504003560348110622021411394079001c85800070407090b100e00c031007c1180364030103101201c0e1341c4011802048252801e070200102d11350410941451100280010140e00000380c071002280c01c10b110240c141c6c4050b40740b0a030710700401c13090100049807076500c4164050408003034540d9418082000c521400526960281245c580420031141800009100c2041c80240301c0c0d4a80e02c1d500160395912982c040d0f00003007801303c01401400c200350000d0100c02a10340c1750500c3d4030081c603502d12090f80c1003504115132554020a950b65034034070074854100e0100040c0f4140d005c101d940c06000070544a00c1c02882d040111211080280000401c244085903101900719950f5036002a0300901c0003000361404c6000500e03c1711840003281c0700005890044d1030003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 203137553 1250 203136303 203136317
    0x5190501060c2307080304080d031a0f010e03060c0403030305090a030507140111120103030e010905090109020f120a140106090303120504060906150f0e040809060c10050108070509070f 81
    0x80d4854400120910101d42d804644481603c4080881801858000c051440046440b0307401c0107800d500b0204500c0100c420149070260740c0500002856512610040c10f40d102e0f9600c814250048601c1c500d10001c043e0140f00310401d11100d101c3d1a0006c1080300e000c1e550800280d1030300c0895645503007802d040580024004e100c00004a083d40f0303050145408a440000740f071940540c50360480c1c0d0061185000c07840c8500c40104141034000ea0011841e2000f480c082c00840c4c141070016084900602800911641c00b044c04460001c065040399040c05160f03020300100d01e0003002d4440039186250b0120310b4240c0201c0001850b1b8003170b600440907642d1580324550b501109040040041c40000c0c07040e954a9143c03280350000c95828441e06142c482c043d1180c1c01214100420000c2103002c44d0310a01c0707011140d00c200030204100c13400361807080740103c03a015591020348496601d044180800074400c0e41c940000002d0100c00050503408039001038805594aa5822409481c408110310b00c0e00f01280740 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 203138803 1250 203137553 203137577
    0x28080a060614071b08060f010315022106040b06030c0d0b0105030f070c0c030f030206090f0c01140307030207020a090c0807050a0e09100f0b070507080c010c060b150a030519050106 79
    0x70b840365041400c2072035902c20462545e0f540190b240c04130a940c2c404803045d140006005101100605101507188010194075200282a801100c10401c4082220042d00c050104041e41e403960440999040c2c010700d0340d078403400c11040300b0b807940c1c1c0301e80001001caa180940c1d0503081d50150096a1040b090900080e0440d96202d03010399090b0180081196040051340000c80050a45000d5481040c020f138000c1c6514900b0500c0b01c1d1600c7c48010314010301e43d12542c82030718543c0e809410240d40400d038079881a00c0e5160745805502901580704006c1d8170845155011502001541c0440d40c1d0342c00d03e0359403143d00d0308c0322402501c092142618120028003c42102407040c10000c2046802c40c1030083c4000402d5940c1902d25170501240e0800f8520301800105082845010407032030000e0100d84001d01040d401d2800040d010b000d8205004100d07545642c2e040581c1d030303108072005100100c0140300756610181c2038402401407108582c40e001000040034030358403003e4640700799030503600181c84440c80001e03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 203140053 1250 203138803 203138813
    0x308030a020309150c0d0c14180f100215060406050906061c060801060302010210050106050319060306020a05030612010e030d0b0316030c061e020606040228080a06061407 75
    0x40b00511161031803089910500e4010351a941d214417800c110008075071200418094041601c0075000c01104010504074030341010b5090008030744242403072070084500709080001140c80c7e6540a0000d90b070001003400030300880e40d008120704d164070090115a214541e68441000119201c5004180d0051840400103603039041140041503d0800b10925141c0403240120a0701503c0781078108030400d9441b440e00b007046580410640c07000b0f1051140610041d0705011005002d40030090683c0c40003885400082140d07042580310001131a0000c000750f580307076969600030780365a01c00d4036414000c05414070b1a01301711034103102d80d500744d0003500003071458070310403400c440098121140100d900d4003846c80c0141d01e0780040c44d03850b801140300309021800c540c90141c004e8030741c000c00c0903001c5030b131007036200081d5946901040c2590b10043c105c50060b210712903510f040c101c007401c0e0102698083c650501030481d454104110070302c02d01107000c0c103001c0c41e51031b003070708440c141c6541584c103840401c14008100050 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 203141303 1250 203140053 203140057
    0x30609020402070f060606020f03030613091401060b1207020f0607050a05040807091a06070f0201080a1b02160504090b1515071101090609030803060103051911180a0308030a02 77
    0x2900080000d400c2c01d901c1c2d01d0f00b0500c4292104201e0341079035114810442c050301806806404054580594110329240c4c01003807400d181c1c43c1c6200c0c0b0710750f0750360040810020072803240c589071151000200219078071040a030f100c41e440b41403980000e9000c0030016103042d10001d800e082e1080d01324043e0a4949803240e007500d403034014444101c02e1007000c0c000400c03602010001031000380010600481c0c0b000c0c010a02c0c07c090544680e500303000e0032040205901081170181080000c0d682842c0a142c10394130b010b813010003010040c0c81025402c4115441c841c1c5154002144140360807641e45034071110340c0c0d9004000c111140080c00070729658040c00001c507010b040d5000310421307001c06405c1280440c41d00c4010502caa101a8080724203001510380d80b8825688003400302c01600c180d08200030b03024150b0300c3e415a54040144810304046d200c00000c3c40c1514030765510005120f11101c00d002e824001c95181105811885204605400c0307464507907000e1401d540c00c40e0460303800201845c55500c518411001075 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 203142553 1250 203141303 203141321
    0x91e010210020a03060e0601050c031e0d05040b0f0705130509100503120d0501090501061403060118060c0510020f040b0a0c0b01030311060a11090409020406050603010e091509070306 80
    0x58040ca114041c6190319500061007a00ca1a66002032124207200c0203031001500a03044504000e01803001507507030000041116043c2e01600001214100100c0710940c880c4100d40c3c5d1000d00780d0500c0180000c100415500034020200400d540360286d40c0c00200315624043e03422102040e607250882003003282010310001e608002420075401c1581d45480c0882e00d0400100e681c140f50403000519038660003220300c01d441c09429240c00a012035454104010400700c0100c200c000c40030400800308810742c1c0070314100107120464188602e03c0c1d03681c460000d452520036243c251403602915214161441042c421515203504039620f807402d180c1030900500254100740c0c1541e090000c883c5a940c0440d4031008081d00031842950784d0142d10610911890800101070542c00806041890718511b04442000381d0f44811001d4a001810245a0000402600143e40020f4003c60004008100000706c7d0400783d1107030304004221070580c00a4086101a00c004403500c0c1402d4000a1050001503041d8015941d6 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 203143803 1250 203142553 203142557
    0x603060a0b010e100503091e1c12090809010f02070e18100e0102190503040515130f06050402041b02060106142b1a01080a1107140102090f06091e01 65
    0x18124020300444e10a0480a8003640424008030800900c0c803010070141c01a00c00034101c041310a501885010380d6255a4903180000c050b00d000750000b0688118241c400740c0c0d985510078060202c1d03908044d100b07544003002032800030780d184424058481c00019a20b00b120443c0403440c0680d600ca6811500810000f032a040d854010f14442c0d0643c801240074418901558000050350740070210180d910704c410301480e200901c2800d00800c0081940464034054942c2e01010411080c2d44540c0c2090210240000040c4581410750940050044c5540282e11462083e2020403204494185100d4806c030172040c44401640301d10014007006100b030b03103258107244c500200e00d42801c9000281da0000d02c4200c1020344104d040d001000d0166819015804508408000c0804956078060000b03185406c0240114ed98548810700002c0390700c840021924010b804c04ad5554040180c000b10340d01030342c01001c1107407050ba01100203006518101c011075402440040507103030b1080ea040281c0040303034402c000f0641 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 203145053 1250 203143803 203143817
    0x11070b0a0b03060907051f021f0f06081612120f02010f0c050903060106050313020d0c0e01180b030304230420070b090102130506030c04030c0e04020907080603060a0b01 74
    0x480b510304000c094004c0002c64042c041050404040c480055008400301801d40d110841d5600070540206020a00982c40c14030f80071201d0082c0c0d820400751000b00b625190151800000140c5200089a10108003071901032000070b40e982e41d41c0141800039003079800741c2203207034081c2c8015407030f402141650b03031a80c040d00020510020501805046480401086000c83e80002c0c0c240c900785001c0c000300d40500304c0c0c1d0401604605040e06074502080c0403802c000d0150781c07030300d2205040c0400354480c500281760f441c1c4048115030311400b94002201c1c0d0051400281e50802c013082405141c04000e0f02c2c25613012030500e00d4a9034010030306011a03d03519035216041a503c12080c108101a02c04c007074243c100d0716031080c1d0358003900c1c50400020070000300304070030603441480540100c3c1100210101103901c111001d070703225220f955108545205651000b00048000032002505454100d80d50784107500807123164034155206041902c5518048440c9030745500940c000842031141548041e15401301071415032 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 203146303 1250 203145053 203145071
    0x90b0f0f16060501030b16020d02061b0c1606110d0c06092f0117010803040306090c2301110c0a09110405060711090105100c0b06120d030c021011070b0a 67
    0x3422100f0030381041e196800150108440c070b108120488811013481d10081203554040c4200030b454640c00340090381094560000d02407680820070645202d11102d2050345c40b030064603040e1815184040c0700b4480030038540c130385260a4510105005000078010b0716030321105011503881c0401400c91602c210b03907840d000f042d51144a001c1940e841651440006030046da21070900000d000c120150f1100015103d081c001031161758408402d8034100d0b907000c0000f103091021450300c010324209541050306d140740352800640000316040b1868002ca1402c0e2070b01030040700014410743d180d03103d40320034580040b20760b00d0410881415500442180060700843da0405443d000000d25035840b140040c1c5199840d000c440246290078002d490051404503035914010208000190407010320300f0025046e0491a80028030f642c032524102c00840007000140c0d41c400c89409c0c1c0c080d00810161402c02e005100d03083c1d0100541e8587d00c6034080e55803a403903402c5d060000c99903400d0803d4a000380030700e0301726845090701 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 203147553 1250 203146303 203146313
    0x60907061e031b0e0f041812031b0215070e010519020f03040906080f0a02100503060f0a030501050702010b010203090112020304111c060c0305060117040c05060c0c01090b0f0f16 78
    0xf03007582c01a91405035000405040005000c010300100d403045103807002c1085513840101d80850328680c4034107004000f034101c450070340040110b010103413410501c024103204110f0340412410f08040600d07603250950307160034000f25280c0010a59441c040b42c000c100041e640c100c0381c2c140c0d520481051040b5111114600350b22030450704513520425000c0c0c3c90b0780c0300780400d4034144040d4140140c040c00070503800000d0340001c0d8034500c0030083e01060000000c046801d0f902c84040c40741d20000040e0042e500e8035030f46e180681c020038048901c00015440c2c5440c01304203610100c111184481c0580d0b4960740c4058015a10b802940060310488050920300800e5a0755120403115108122a98800300202d010b1810420141d42a8020441c10145894100700d030903030f00039902001c4140c041c03100d0303961940c80340f809220740059900501d5000c280401c00041c007140004045013030034420383c0d03801b0702c00da86e6210001050117003040c4000031075018080000c40a203128064040340075500c00ec00c20300d001d907441d1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 203148803 1250 203147553 203147591
    0xc330c061e02070201110c060a08150a0b120f09120d140a140108030703120902120f030d11040f0b0f1903060608060913030e04090b01140102060907061e03 68
    0x48800c1c030507004580c000c15036802c011a80d9202100c3c0d805032940203074000c0011414402d050004041c045804049a0580b010500807103588402520718141c0d1500c822071010240c000351610409655210000b544010914070050b01840d403600007407201102d101030180540c0c003c10786040119645007031141a440040e044180600c0f1031080001f100d800300c454a00744080140c1000c2034035407042000c040041d60102e4080f04102c140341002684e4a42403001030815a807030f00900102d44544000303020107842c0840107211410f8229010003031004034140d4145a8084c92140ca1484010307000304002c01074040c0c004186a40220080a203802180c40708152480da80c124150300095840005004580e0018042904400220351919035484e0248501c581900644401410400e845800c1880c640b5943c121440c0c0c55030281030107005603120301306020142c2d0441c1c1c02900601c2440045415040d010485100362a07195443c05039a0412000c04130218604a01c0711040542d038941c2c488150080c142 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 203150053 1250 203148803 203148851
    0x5210702130f0f1d06010b0301060807050f040801020706051609030b0411011404060206040b0a06080309010f14070506060306070309020d20271008030d18020d0c330c06 74
    0x120340c044c403c080000051601a0580010034454803c00040c010f8070382009289a000740c040c0b43c0140d580344280c600d00021300565001c1c071415800441c419041000c181c0009119492071007103221034010044046034440c1d5148406490111903101140102c0d040401807800d402d018102001690b400c400b540b031302d9030701550090300160410f02c1804204000044815000780091000b4080b46040c4444d140d224402d664519040c40012200d8008080c0920072100801598200d400d442c1ea803a401c2c140e44550007152024030900403540041d018034002d1142003203c0b5000f070008450120199114200480c5081c1d20b01403400744d0300c182e180c00b17a070740074201d407841104181c0c0d00180607603801d9081c0c0715078000b410840400f440d00c0410f000303000000080d02c0829080342c00224040a50800c043c101582c0d07020065001200084103e09004600f83e0f200c00301c0b80c0c601203c2c87c1907003980c0314000500b239005454140e034078110f9400c040c90350310035820a002c083c014180016410400030920149243c920 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 203151303 1250 203150053 203150081
    0x80603011407020f0c03010c0906080a06170a0510200a0203160c141021060b0a030605031509070501200a051b04140f1306060305210702130f0f 63
    0x100550070504140001409410250008e200000b040300c0b000d44400164010541003010507400200c1e0b4552a03040280200300001a8060203801b43d141a5103a424a42d020784a5200b25101402c42c4012807017181c804045442400404243c80c00d2000207640c04205400118070040c8681c14401030795005440e00240708815000340d0f6860006ca000d200302c00094140c3c4500c48240e82941e260f034009000c0b400940350000001c0e03c50700c041084900929464118110114002c100f060203179425a120f402524421030460b0b5584c141580054542241101c00b00c0060b0400642002294010500040b0a4040c0d1060300320304540034009a1a04001402c1500c040d0f0100b50000c44010004c1d2450752483e106035814841c13a5071428180c0c64601016246281d4030071190000b8207000101c0c442e806105920020500c4065030341d0401c42d54441c0d90030403840003400141032641c12403044808a503482c50703010b009101c1c8402a45254402010144a410422070700c4180342e4620f840340780729580c40100b0380 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 203152553 1250 203151303 203151313
    0x18061806111c0e0f0d020d1401091514011703090d02011215030c050d02030606270903040806060d1101080601030617030d0f090308040b040812010e06031011070308060301140702 78
    0x984100545450410300a90040f6500d1710300501588491001001035600701d860070414041c0701c1c0440d40102266603015040c1c1c050b000030460a805903400200c50342c0c2c0000a8202180d0b00d82020450306d0031403086420f81940200a01552800c1000ca8917000702d005050000c0b40d903410300c0103c0143c2d025040100202d2180a005108005035204d050001d0032041c0c600b440304100d9980825a16080a00621b20504440044010f90134152003029041661007210800c1390911a020541e40c3d0031600861485004a000040c200c1c20303c0101009000e40145c2004030400c090350054821080203082e0130304040d00c46c030010948401c0d030100d07030554210240040d550388c42c86c070b2402c0044807080c90402d05020304040d020004254404446d43d002a008028041c4030b485601d041c66552141e00241c1700b048040c0c8000240c440b18840c01c2a114903800d4058980d00c00c1f448410908030340b200c16118004c0c40d03080c0020f00c042803040c414030341c2c00f501c0035000060135100b1100030300448404584080050f409 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 203153803 1250 203152553 203152577
    0x20702010906090518090c19170303190b1306080d0909090b06100c0213050106020d03050f0112080904050906010303090f0b0a08060301020d060618061806111c 70
    0x100203003080041c4490f15040742c1403410440002c4900c45141c06006402400700c02051103500305005544080d00003c01051092035001c100f130450b01124400c0303140280c00420360106550300403040701d01c03501c1c2200c08400b555035a0848003004105490302d803600564607040c10f00798001c8510824004d089824001c0c4000c1c1c00303649000b0143c4410b5000658543c0c01c204500001860090f41190000300440c0c50900522140707204071081c40080b04041c4d4400380c028003501c00c01807641d000c1c1c2e068401c5035080e40d02e159040042603098500039140c11032102d1440004218924003c0c0b00004118031800c0d8041c40c1400035000503050303030401c1e155500540c21001c010000c061b04036150000804c500d6a01c48001c1c2e03e070030449005030040078000030030700c02d40d10006640d59070f080d811540c440c001c15200b00030894640750001d1040e010621882c005011030003000c20654012446801c00c01140310010b142d07541450303412103181145c0d20020b51300e8490b500c064082e0504842250480213020341d1242140d4107 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 203155053 1250 203153803 203153807
    0x309030f08073b1e090c07060906270506010905060109120c060905150a0c02040605040504050a050c06090f0f0301060806010e09070609030812040c0512100510082512030302070201 79
    0x48140561032050400c00c08110702000c40b00840c130703900f03081120b10301029a01c0d91000c00b110f1007140303001408036150038001020000e0760707404a0203203011003404800c1c4200084180ea0042d00400e40a40701c0d07408540100201d841607080303954401d0043c03601410842e6176140903c4101c418000c129010114000e05004c01175000c6d0b90a80201002c071600c2c00844000a113107401403149120352010032100141580554075a40c002d0760003000094401c21040c680781c10308a0b1615005c40d4100e8190240e0320207a80b0b01e10349001591541080200020807868080c0c0030420003924807140c1540554031707110001040344c0c0a0003100d00a098000d030361001c4e460701035044c60a0403160381051040c0800a10300340042a401004da640e000c0003c0c0704210991214203048404103225400103510000c401182c0600e4070010610749060480103c00740000c0d100c8001400a0008900401103190312030b41c01010492101c00c51481b5000c42039425105442d03d0b0301c491050150307050b000b500071035000525041156 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 203156303 1250 203155053 203155157
    0x5030a03030e0d050405010903140a021206060a06081603180219080601050102160905090708010e0106090e06010e06330306090f1b0a0201020f0d0902030d0309030f0807 74
    0x30400e4071341145054106000038007500d04a005c080c14426a0361401003507914104806d95403140c009112074a551b803a402c5940d178450f002c907610b500800380160005011405001c0e0140140e000b03a0320f8403810804540101e00800740495400b041418540f08680540ca40340c000d400b1003600c080100c80141c0c200111189401e0040c1c0c0414115849950701c540300b020507000d044142d94100340046056100c602036607203001c0c5d042c1c10444440d40f8203020494004015809101128141a8180841d411071508162640030900c94040011441000072305a480d0000c2c0d0611262014003480b4410070003204a8003440d40d80b4400201c0e4490b0000502c452440c000008030750240c610301da844203d1401c0301e42c1248828200c40810040c0c00e0120308254024000c1d0143e507446960310f810240c1311030551042e180641141102070b402806040700c0025418424010b44030300d00d4042d15802800852010111080301e0000c004c042089140d03003441e5038403424882402d030001a201e42440d500404407030150081 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 203157553 1250 203156303 203156323
    0xb0304060c111207111206150102190203060106050f070602070302060a0e0f0a02150c15010609050607050c01120207021003050f01080c0f090a0e0a0302010603050709091104110405030a03030e 84
    0x5603100380c1c0c0f40c00885a01500b12040c0c59808081061341c040100d0205110600b05240c4004501600d41006611164030f020318004500990803901c848420103401c50400d4242031010750150032140042c82114080c400800480085072440ea01d0860151941406c0b42c110b0b10f01100180c004605018401d40d2034013810b910030f00c0840160003c11045004103a5580e85200000d002e1030003012b0221111040c4010782d5030000003c03003607403da5142e822000902540902840c000708180c040003042d2410950107039414640d04c84000c044c0c980c01500107644007034101c0c1c4103030034080e020070900e00113840306000d0010483c0c1030303100451f260034034010124401034141c101c103c40d5480220328141d5555041c0c410100190261000d54a60325201c0d503000c080d08000311441060300c61140104100742e03055005008483c00740c819651030540b6006010140d480e40c0a000d080028030104031021403070550300040c14648202140c91609036a000442d0130407080000c1940429a1101c00c0301074084280805105 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 203158803 1250 203157553 203157587
    0x19060807110a02090402030f0708010b030f0607200106030609080304020a0504020a0909020c03190513081501230a2d0302010807050d0b0312031f060212130b0304060c 73
    0x1c014024000203564942215010384504a0740c3c02040c25501c0900c071091740e040031502601c0c00d00f901c401509002c0c080c1031245d54001d10880741030611001c808510790f13000701d0207650740030030503982d05200348032440e9040e1441203e5540c445000000505502c100c40341c4c0343c4140392103a100d01e054010001200300d2540264059401001002d16890b4010060001d50f241034900507210100c1d14440307451030141c803403215a00c0700040050703140c494000380030b0082c41022075400d58402d6110500c1c1c07074451882001006440c8c5050300103001880740c480034500800901e1050036880200a40042c020b88a07641c003500038401e0020611009041c0c05400100c803031071408411407091301e164002072014200400c41004c210300801c4402241985030403180600c42c1c002c0c100d03001d029140d446028103600c1aa4a140100162000d255000240810707a4048076000e8010b41303003651801007400c0b802c0d4084551001c1180180c0c90200d00318018901841c0114044d02d070009241002d07400240800400216840c1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 203160053 1250 203158803 203158817
    0x3060e1003020a061b0c14031209210312010609050f0931081215011b020909120304050c0a06050319020a1214040302061006081602070519060807 64
    0x405a01c3d40308500040b642c1510308040c00d00e50b5420561440e00c40c1410040c010843c0241c0000d000c074445090f11080c210840541e0512800006001345600c80c4411181e0010440d00a625200441e203404103494200c16069a1501480c424203103d006002d0300480003041d0030403018840c608149181c08008102074404801c14100844890303d40d42c011710048444074655003030495001c4001c40c200401035800411940c0368880300c40000c0fa1b458040301c0c5848456604544841c156100e516151483c0c4421290000c10918079002e10581400040003808940b00300840700c410f5010200c000d502c80c40c0100f018048403d40b00b8200000f41c2040d42c003000c04c000091080c00b01242e9001031800c5030039191040103a4815142c102a07802e00d07284074817259068a44a14240c00407490341c0400c0c4101d11980c280d400d43c0c1d50b00300200e80c00001d04e01407040018030741c80010342072182e00c00943c0810a800d0040312860765a50000030700000140d1004040d081028604220301e503045070000350010f40500b000c903 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 203161303 1250 203160053 203160059
    0x90405011b2303040f0f030201091e020f09060a08070b07050706020102040f090903020703020d0b06040e03030c0d0f1410060f030504020d0305090f09181902100c050c04020a03060e10 80
    0x4102c2d4a0080306001d1101c4001000c1002c00922030400c8846035480f41c4660181155424080c0c002d00300e1010a88100201e141c0224024802c0520350011a500038001061441a40b080c0503000030001c1000390450007006010941d0382c000c1254000800087c41700c07680d2914240390a900701a12688000b09580c0140800c0c041e030a40b12442070240c9013645000100c1d8021800d0882c5030079000d500c069040a1401d5141c2c0a01c000010640e104000c256011b010315903191885540da407208940001c1800004d100340d600d40100c64100351701710010303164085a01032142c0b17040c48070b07400e00307482400038980e00c1c070400c001003500800081400c101c1810104040e00c1e00c3c4d000700d02d421216050090410070005030420b004ea9445c090b548100c1000362190040349005840c1002260204019400368400e1807034a9692080520f07400b5040e550107010900c84030310720001500d50b0200424122954084d03560178100703c0c0c580388086c0403503640f65500814054940401d4091261002d4525a40407000300f07014 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 203162553 1250 203161303 203161337
    0x100204050f0406060807050a0306210201022b1b0507060206061e060403080c2a0a0906030c030602030702030705030313020a06020c030a1103160b09210c06070809090405011b 76
    0x2680c0d0150721800e187c0c2d40c03000201d400303c004000a822110301448400c800350111f844030340c0c4646045100784c0841d0b2680c0f0300189000314400c035140740c0c2481102d26580d8a0805031140200640a452501d0041c021406541d106801c7c08110340103640107074000420001c051400056210a03021f00d500c110030181c604101080e0390344100d00000d4178206002501d60348806007042a6850030352400081c0301c2c80051100840c802070000c00c20b503441103200d15004101c001c258401e2204a0b58000000c800309483c6a45410107504020326031010750006016a40102c1d60910007503100795108901c1009640c01881000140c059580010007194440300241c074042d280003548420302c3d1707001101010500c0000d80041d14103d2144401d041d03200e001000001c44000319400740c240c04034116250314407110703140c01c048807441c040c942c060100e6101c200080900e0502400805102c0c0c00744190503d00204400490030740c41c4184c8084416a64a1581e421035038800c00612016412910b00030041860407059 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 203163803 1250 203162553 203162567
    0x513091403130e040816030507140c0306010906050303030a0c05090603040c09060e0c0318010e0a030206090d0206040201020703170906030f070f05090109030219090908030f07020c090f18100204050f040606 90
    0x122010500c000c20384241030054003a1010b2961004c06070ae01c800b42e10322040d81340d00e80d060840b8020b00c6004000b24144515015500660b08007070019070175503481440300c2b00580a280908020b20500304802c04083c1c03944801107210300d00440d1413008051500404400700d44507503100c032101001c00c20034424414803070300c05c4a42012980c4403185404961030b50a50040468401ca10818883c00c000c4904050b00854030030b100e024020256200b00f050364a050342c03105c00444d0002e005070811082400092480c40b03100c020080518087c1c2d080041807000715540368000e488400702002c070704007000141c0e640315100c110881d8861a2082c00d04040d8000a04000d5090000a2003010281208900c0762400c90803003009004181f010300c0000c1c070301c1c145032503194010f880c84241008a800003402482c000510700c0b14008010b449000150b4622403014500c4801070070807480c010b0142108003070000308210300980d0180603900140d80300d28050401128804000409008900b420020000c3e2908402 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 203165053 1250 203163803 203163817
    0xb130b0304170c2a0a090905060612010e0106060507020933040e010c08040c06050a091701020d24050103050c120402061210060e09040c0513091403130e0408 69
    0x14940c1c1c9821111101c24101140d150130f80d080411804010009442c059180340c00140050b40d034020000e464141010a9869480002e40390341d00c0040070070701c039042861801d4581b4003920300000305054281c000034203580423039002100051000c0350705400c1d45080301c82103822003400108018545544038001d120608804d40d202240c101c849150f1a0946685e045a034068010400802074003118240150a94200b0f84041e80d2610301c1600100c3c3c414080d208131615025162241041189455a52881fa181403065608a95002d00540d801d80049001d0b0b184251082040703512205080800514010303001c2c1d100034101420003082c803443c9400c400440307842489c0c40401d05881e80da1400031807c1480b40c441000e80c542c4c40101048400800e0703034082001c0d1100c5e40c0c0c41005440c8160700b00007640c00c050320043c00705100440c04105500d0840300d0345221200280d00400d410704192141440846540a09102c68000103203d454040180082001070492280513449506140d229600e0030b010b83d403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 203166303 1250 203165053 203165093
    0x601032901111501030b0a05160c08180d0c060f09031104020a050405180f0c03070215041b08030301051201020415050906120a0c080906131b08070b130b0304 69
    0xa440b411441051160741c1800702e01d05400c0c1c0240d6528a00061180d00854116400601d02000b055003200c0da203003400c1c0d0303041813541c5100c8201c41a840e48030050f0711402c80b0000f800c01004245d4115100c00c18480c0340c0710b01401001d02150b181200240080d000d00c0c03109000c11984010034800100d03160450701060074141c80060300d5101c0074005451a110b66001640d00003075112100d8001d00c414540c03207204440583c1100a02d488407500d00d841030000740c5080e800743c0c003d108508034031503014045079845402002001940e11a07040b90101000454020701ea80b038100200600160030100a4945000701c1d41000314540703442c040e03004030050b8030040b9040810200003002160303075403580c06948240381060100310035418100a4900103144201c5503101007074020000614110300030902c01c0c0710780d48815105190750323a207980e0f0780c0c0640c80801c034500400306540c170080f070321440820a00c0090030600000c16503e0b213014884010303071902584074000303100e0100100301c00683c80c6003040d0360300380001c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 203167553 1250 203166303 203166317
    0xa11220908130b0703030b090c090d02010c0803070c06180203070e0a02190e090601090503060a090201030e0307030c140a050d030e0a150204180e0a110112140601032901 74
    0xd2a04407041d2254003031250594450000100d889403070040100741c0184207442c1040060020000d0000203503003100c4100d9480c2c018068200a41059051a10403074414134003c10b02c1c20250b0ba4054058009480140000760b00040706410405a880f0310701c1041c070340401e244513440305580080e0760b500c12130207851200805c9101247e10031900d034040d2075941080c0c0790a4001c424603000f0081c912100b08a003140b1514420010500c51350080209405891000d00508056500c61454201a04418600721704041d50b84161001020062000c0c1c01c4807482a5100c2c64854001e04080c0d541c1202070f289400550055000702c000610300040041c0444054240410000004945030342814126500a098014100c159000f00c41c420742c010001c0c0c954054103901c10920503078070042107905801601030f840d0f214482e4000480d0181c040703081c00150514000c00c007036030810000c006031552003c818602840c818144503840da0076000d03041c101001504483c41051010f4100042c203100103400030305201103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 203168803 1250 203167553 203167571
    0x10f0602070503102703051e0a0e04020a0e04050a0203061002035401080c0c070302090402060f040e061008061c030302041e1503020c03032805090a1122 67
    0x15584c4c9401d01034111340b030a50174220460030b010701282e01c0840c129050751200d102e070340751230000441500d08000140c0e845a08041070142440000c0d4030a0101005010041b5440402c1c6c3d079642c05601c1c130400c6044800340e240d00301001400b121040035400d400564005103d00e00ea280c030b100c800208030007800c450381081d070781158101100c80c210485080c000343c0d8048241400380d206102c06200911000ea80d281d8055035500c464800c28011002c000c0c650341c010180400142c5428440560040d00050045241008016075001c203a48240d00860751200c90f107040051625001c00141540801401c00c2e41280c6800c40000304040750010305102d07450790b40700b0803d041c9440303603041e60050221900001c9a0304840241580b00091502c1703587c1c01070580c020303200141c030300c2402074641800044004506540314007903546203400c4400c3c440e011401c00e103a0280a6021103010340b074010851708025221211280c2002c045600440c040d003400352030826403c242a000c0040d00f030000035583d41002840e840703 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 203170053 1250 203168803 203168831
    0x11b06020706020d0c0206070e0f0307060305060411040f03060b060f04030f0f02030106091a1806120309030a030e130e19080405040501060206160f020705010e01020102070c030b010f060207050310 86
    0x10005201300c0240307131008400d0542e0300091400c1c000c1c0c209803030749011059002d0403c560702c0e1122020a03016044400c0030001507000707401c899044031000340003080c2090405044001e076000f544c400c0c002103442000c100300303202c0c00340b050081001c000c0d45c1c0140b405054030300075005440390b07100003800b0305d00b409007070410312440c02840c4daa5560300400030b000d0566104070380e001400b126040800080f101d50790a14003071034050310251701100a00041c00003a6101c3d01004030600780b001c50440e0a000c1000364500903a010701c03a25820034030903281d2036452210340051005400c5020b17408034ac464039214900440031000074800da942c0030540d0000c44c4a4645250105090090354001038001c2e0800c000401c0158000c10b180e84542c031421682039094001240441d00090b4a400e9400582c12030a07040c466540710f070410740080750f01800050304c0c145c25561032004100f2240d1044e110030600100601418001d8581c0c00001d00c024801072450605210020b9101c240000c007031540941d640c41d100161813 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 203171303 1250 203170053 203170057
    0xa080c09090901050114041b0e0a090c1205060105210a090f0807030e010503010f05011b1b051002030c06010e04050703120807080a05070f030c02030d061403010b011b0602070602 78
    0x2110180c4045100d0801400b4280680005e01070858103560040411a00d03080030b10035001d00000101001e80000000041941c1c1603502c85802600446c40d9031021036941c403207001c1c5503001000d40d615400e8004140441500b10b4001800e0307241080010407a009800d004020240d04541550080e03000307548508801400900c07901e0002442049589010b0003405008005880028080c1c1c0302e4006044051004507641d1200340a241442d501045c4148803035440380002d4031001100751008006c490f4a912450722440d40703c000d004800c003004009209a00b884052031840000c00d000071070610440e114119101e60050040c000710f00041c40c005801d0000030030480005580210300c803680c6c012242001043d0860494086011841150108225140c2440b035944100c1c0940c0d150058000035640490141071101480b10071440b0910145241c03400d1792007603200600745c1ea40c0003a1a19030391020306003924441e906150600c522151100c10a184500c060380e402944103000590307803005454190000c4c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 203172553 1250 203171303 203171317
    0x1101061d04020f0109030f0308041a010305011a091905060303160b01090501080c0609270903070c08070503030301030210091e1e05010e12070e1f0b0703050a080c 71
    0x9082a03400410300030248020500880c000e664042a000580006649482880c48020419607065218401181c45005d195820510034200403000c030b02d14007210003900b0f0080c0c100b900c03907075500c51151445100c0004107081c100002c2e61a0b20340b40c9001c19905c214503080c1d40303005100700d4a64001400c01d541c00d008407402c803038003c3d0004003070003030a080c01801007200740600c196462404c000401c880b200054a00900700d0024406450280c0d15814040301d5160b0444000d0030442c0c02d9500582c905945003802c1c405c0d803401e4000c5031104040d007000869107189502070000c50b045000d040c404e0f03441c00302c200c90541c4e4041e180600007004c2404c0032108d82e0210380c0100482c8038018800400f00821014400807540c01102c0065a01d2800d206c0d10b9081c030f400c1c0f00385404540c82184141030f03070074122107205140c00340d9001d03200941d6030340202e0000b0480c1117074003684405507500300902e842044800c400290079030b80e0040e030809079980e41c00762152207819140c000b4005480e000903005c0070007800b00e40403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 203173803 1250 203172553 203172569
    0x50f0105120a06050c090907020313151704082205030a08090303130b0304060b060307080109050c040504060e0405010c020a0521160f1101170a0b0a0e090a110a030b07110106 76
    0x2083ca017020703800751290051041c1601c01e645140108825a00c0001500c00f600c40c410780e0000322615155100c10700e241040402c1c0c0900c41d04a10801c031000b1300300450780c8118041d103009a901c454030425020b29120442e582e04200241020510142e10009031030103d65903c4003655582300940c000217481e50040104100c3c40501121002c81d180c401b20000c0d500a80c451780c810b004078007904040040c0c900048840d44d0002d03450200411540d070b055081550445400c0030324a01e040e131210301103020b44001e030b0005c040d042540c80c02c0c0003c0113401d00c1a00a000310502c041e2004540710f58426072958810b8040070419a09403a285440c203400e0001c540301d099804543c401442c04da45021f0341d150162103029908040b0640e01c403079080d405203410075120742c4800650340c4030307035607421005004003131036103501d80c10950a0001207080b0304409000e43c081ea4000b4018480800301d032500904890554180b140110002d07002000090f400e180d15070741261960404079800c0300c5001000703005100c10741c00052 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 203175053 1250 203173803 203173811
    0xe07031103040311060c07080901030504030e03030f28020304030809030304150206040c080f0a0201030f060515180f06090103020c0a05030a180b03060105040e09031615050901050f0105120a06 84
    0x309604071300103070901c01450065a509030782d440400750044c02802005442c0c6081048480040d610036071081e41d0051080c10030b802c0c0608840042469601315800d400101540007655480074494414402f400c203000c0e803160081003181100c025124091484010b0401c0400300c0d84a03529038041c41507802800c01c88074001000c0029000081d9180c00c19103044d650207880038404500c000020909101009116004000760815640118000d040d618500700200b41e80c2c0c100842d256595902c0c003e190100055102e844200014003484c3c44030716584664411020341709010303902d0b02c1e5071058610b4404242401a1240c601c084000c3c02c0c4a00060b00030410300000403c818550f401c034804684064140582800761611200081c0303082c40140c03282400309400b0b06c41000002c0e50301e41401e41c00300044040d42c4c1449501e01083d111040b891500f00c40301812050080070300300084c440c031948046d002000748004e05044407011041e41c010b0040c540900514000c0c5c1c602d0000422542a10700e6201348204 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 203176303 1250 203175053 203175061
    0x30c09150d0312050a0902220906051312030c0c0213090b0403111603020306182109040f050402011d0a030b09010905120301030b160915080a0b04150e07031103 70
    0x42060754407203d80301a003403604000c5008080c00d4030840c3c500e070780e0107000d07003c1e249012100c0600d01d250f03980305224500c0d110380080d80043d54a000d280d00440c014100000502614070b01005440e40c0d8680e40c104051130701d9005070140340c0c00419081100c0c7c050315031607996513010940c0b1b005010050400741000e0200004d1204242c0d03c001e150090747e82d210241c2e12003c03010b10746d0005071469848069415030000011504103c10350045000710308403c0c0459043e50008a0030551b00401401840001d40c0d010408060ba1708207070050014410580d80d04200c01e151590019106084c4108681c40294612900455075118403900e440a50340025a14900f468040030543c003a05803030004440c91b0052100401581c01d2800c00d40741070f00c1e481614046c0c1640c890202084149004503400108041d0810008a403042502e14140810781c656515030145041c00d134080a07214002d0415015610380021442e044400915a50584141102c200255214400124041c1c5a030a034803e00e00d101c000140 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 203177553 1250 203176303 203176307
    0x612040507030204110c031b0102090306010e01030303060e0c07030c03090902040b09100c020319020f060f030403090b040b0f070204330909030801140d140706020c040b030c09150d03 80
    0x7090031a4400c40f03050004007441c07414202c05000340c9a8031403a0307600500c17601603450010200c03c03c00000b58030005081141c1c401c0000e00e407400c08e80c403503014648160014024143c0c580a488003030004800c1500c080d050084465a41d03104600d00030701001094204502014442d10911005010303120040d0f4440d80c9482065003182e1046084038807824a10501180c03c5004011a05980d50003e01515180898241c120803005804200b242d0005c40d00390360380c4180e92282c000c0c1000d01c030398400160312490245000707080c81741c9640201540354000c0c0800c0110340304c00400c0300c20800041030441c3d210781c82440858080d00144c4500410301c13920451108050b04c40c10256100d4a41d0301c0000002c00f6946c0b415071046401da0b080281c0040c0c0b03040d006200400c6003400e0000c840d00d024101001000d030586130252441811a01e003051908141070400c000c1e41e04100440401104440800c00d0030b5004000a54400c4803600c1e09004e41c03586800595800d072500c184600031480034001d121600c40e54640 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 203178803 1250 203177553 203177563
    0x90e030a11060f010509040501020903120703021605030d0f020718091a0408030a020a0c05010c02070801150e150607051005070f0302031006231314011e0e06120405 72
    0x8803000120209144411503100149290160410703030300e030146070703420141800703803000c0014020381725503400f0841c42a0941f0200f00501422802c401d850f900c0350b01510300242090b0340c01c8408100003044107024040c40d50702103006070703035800b55041c5503c610304002000d03420300d03c030395002064806c0c4000d0030344100100740c1c0240034814030500c0340607000f00083c80590311a0350192400750281c1c1080c4006100d4500307903402488054100e04080c481076143d039503001c0c25035207140703909001a04010300c10001207809009143c480b142890300300c0f021909011203888020f07001004460202d003d080c00f0b20090702c82c50704955400c1d40242c00d0f02e50b907a80c0e28810402030030381511480001800440f000003814843e00c2524001d60007241020000c41c9082c2e011250b40c400b120350812603980410056140044030030041650713103500964441c41c60303e070030240886012000e01e4107040c05001c842c1c044059030312203041c181d0849142066040c00c4808070101c0c417140902d080b4842512607001c02d01081c4a40015 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 203180053 1250 203178803 203178817
    0xe090a1b060807110d050d0b0603070e0f010207080c10090e0f0114091e06040b12011e3e040305010e01050a06051503180106030308070f03020a0c0f020109090e03 71
    0x1c501d41180c0318140c084403041300c0f8280800d11a04014904104070344a1001402540c00009002c83d0070010140003e80c04e074419a1000c1c0400e8104800c0c0c003080c00d01e65070900f40d100c024006820701e07038500040c8079226406a018144612440384008540038000e4a180016204803a01d4008070724108903018407d61080c050041d0101041110080c0da1801740c450b070b0b208064503548546246902e1b10b55040c0a070010340010340c00303070701c5071003001803070301e81c88011401c2c1c41c4074200200b0b81d07000000030038070188180070343c0403072407400d104c651102541c0820481007040c100c411112420500940c035aa0480d142c0c0ca199210f060b0b0000d4004140700c0150003201c2d00c141c090000b000940c82d030302d108204a403500c0c031030365802c06202048106070a0044020307540c080d05a22070110502c004440c0039084604a0b0030450108881406110480e0303072102e0740b81c1d40380400e170408614000400501030300c2070720303200001019820342a546408692050303008600402c0d42c02003c0c04084000031986031603802c100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 203181303 1250 203180053 203180057
    0x1504120501060b0309160e0705040605031b03070c03080c13150c080d0507080702070302100f02030c0a0b04050d05041a0d0b03010504060606261308040b04030602041410090e090a1b06 80
    0x100d400302c1c0c11f4501c0d01d406401000203480c0c5614203442c3ca00160b820340c200510301c00d408110084409407801c9440010b510617800f6994195000b842494090140c03030b0043c1c4041101001031185403030392661440d10a0030303500b0160340b82114064500c0c00303c4072540102c0d4003e0900343c0100e1420001c1c5403035040030707010382c10a03128501540d45140f0126507844180c0300107584061098405d030a0036015040740b110300c0c11144143c03842c003107902c210300b450a8113884044516540c400c08110502100380b0a409044c2004d10300b0610701460002c03112401d03040820f6800d0f48580000380ca006610080d4000b41100760040c00074402c9161505101001340b0240c810040440d5107242c10002542201b100d0903207100e0301203c0c9007400c0d1550640380c0c407c0b9445c494201c2e1000070410011030b840d1100310280c802544500000340e03a55040240211506110758070541c0100070000c1100c218be40c0054804003900c400d40103807035141d9604c9040900e4990040d0000d4150a0a103030711420881e101c09100003070364503c4d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 203182553 1250 203181303 203181343
    0x3041206060b0a020604062310030303060b04030302033013020a05040908070b07140c01050105010e18040f021306090e0c06070309031202030d0e03181504120501060b0309 75
    0xd00ca40b600035128003542040180c10420000b00014503d60090b0842c4100000c01c10441d080a03881012142c800d9034101c0841101c48400c004042d030501404001c0c000708580d440c00c1c00d05c1c0da500650b41c0c1c014038502002c404003400d007a1030070188241c0d0055206902c2c1d03000c0b10103404c0104484070b07c030b40a54000e0b8000c80d00202c0c081000d081901900030001e078008186807500b10681c50307001c103102010700245c0801400107540189050382d00043c02c040d01224000082d107514200c00506104030300940e1600030007156000d0b0f04000300c20036200f5481504408810780070b040700d10021f0489501002c9003006286050340208050409610030760b001c503000801c4070b00c2102980c040203030600424400500050f0b4800701400000d070b075105020201c0d02180100c03800d0210054092040d600c5c00c0c1d801401d540e0000c5180740c1c02c0c0070314401c05008140c0a848600b00d541501c000744415106900034049071011072002c040400c85d003580070000a02040d10440c0e1281000071801d911942e200018171400058 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 203183803 1250 203182553 203182559
    0x1c020109050303030c25050115061706010f05090f0a1d0a020c03030412020a081b0d09140105090a05040204060e1f0f1b0204092306090712140304120606 67
    0x10071240540070782500300341000301001c0c840c444440175140c6140340030380c106c1101000074424002e40384044030321100c040380d113400d004004004040e441907004001d003520003031081598000304c0394044a81c1526280d0368410b00e86004c61601600c6229132904210034003400503060b2070100c490342c0c018581103810801030700d84101d000141e0003241c5e090442a0410400301c0d0001e4060400700304a1040c9006440d41c0d00150b0729042041d810402c1043e044109030320003024041c1081c820124a2407150800580250074001c980501c2e800c6050003a042c8600011941c0403540c2e2810b8a4005000040003550f03a2a1a02030051520941d040c016005a26130b0842c0c10100f61401c105913145280742e61902100a07036407004991258103081d56100c00752801c203405000d61201d0107005e941c140a1401031b420500c01e080c0c034007004039107190714203d150043c40510204482c00300ba034400701d4500c1a440c1c0c806140c9820314461000c9500c0c28801da5100c002000500c004200c0661040e071070184004000c2d0305d503 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 203185053 1250 203183803 203183809
    0x60f29030c1c0902100f031802100c0203070f091d010c02060f1e090d030c1b120306050303210601020f0a140f0616140c0c01140d020a030203040204060909020604030f05010b1c02010905 81
    0x1e07208e100070b40c040592040320b50100c0c0301d03058080b1100c4c00203085420640ea00c0e4290b002c80409078100c60501034507620b0503c103050001c0c10303404042100000800800044880c000d444a9000d011088500030b02d102044004074031201542500b416601125040d0606058040d42d5020004030b0030042401d00c0b800f8000e80340a1410040a0842e540c07941e00f030030301c07141d80707034030541e804400000c0030700d503503404046940d45081014149078100124105061030585014070a404002000346045622041c05c1c081219000728030400d07e190b10206820752411030380c203128105174480c2ca142d00c580c49000300304556584850b200c00303070304401da40f00c20b01c4c0c207122100d80ea486403240b40c40f0f0040a44c4036000c0340c240341d4800c043c0b883c0689220424582000843c0e042e40c0107070ba21142041c40040c0e004028841540743c28400c1500402d03a002c8100000300c00d80d80800d906000d6448080c0c03000070411a1001480310030341250701c5080d030051850840e1803400800d086c1c4051400340580c001080b1507c0031580341 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 203186303 1250 203185053 203185091
    0x411030f2506140301150306030c2903011d040f0503070b1b0414060a02070807060c0b0604060501020a03180509100315050c0306060d060f29030c1c0902100f03 70
    0x6864843da185541e0a2a5581101e0401200c0c0e84080503a03642c1e0020119010310926005800340000480401100b4600d800c02e00b5403445103003001d044104010040c2421450600c00c420102070b00b40d00081c0c0c0e850500c0b4104c12003185000e0814040040c5410070081c982200d54854900008444019500310420101c17030b01443c00b54480030310070b008a81115140242c0078280c04030302441100d00e1207869980d05828400d45500040c0450703070001c845000c118100c20710715400300c0c040d00c04004440c0f911000030365416043d0000b0702441a140000a02c1d00040d00203180608000351641901d030800e0314011040000d07900c81903808072042500604101d03103074010036014880f41c11240d815911804204047da07404651810f402d60398030345000401e010440c0010300180314a020085081d11074a82281a00ea40f014285003542400c2081003e2102c100c800c1c1c885180301c1c0c0c0620725043c004070b02004002c05090201952150002d120f00c1c080d10f5000c1c0c020151302a40707584c280406014000b00344101 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 203187553 1250 203186303 203186327
    0x50a051329121b0409021c050606010f0311031303170405060406140402150f040e091c11030703120e060a09030f020c010e1306050a030809040c090e0411030f2506 71
    0x115400228041861400d9002817021500007044d264403142032441a6540ca480030f00c0450301504444100500e568001080203240302c00c50500340041c090100030540d661100500821300c1151804450050510644001c020340e1105050318082e82040d062207035440001b10760840b9a0b9003031201102900c0381d0070b5001d60049034081d0a6614901c90702594110580102a00041018040c03000049018080f4001801090540040c04111100b030060644007030b2002c85200171300440042d40c0600d4000001203401d01505860a000c2c455440e55600003e06501361840d80c45109140078083ca20701c42c2c1c0d1040c0d4000744a42c842c0c801c1d60410510603600c0b44a00300c03405011559404080e01242040c400443d14140b40140010b025929480003669102c90b540050f1941c540201d201c070350710f00f032034803520040e410181001c40955151140d903204001c4020030082c0048a10811a43c4a4808000c0ca4540007a03081c00d80e001078544450302d507407001380b00c002d04440c4903c0100000c0c2050180d00c0764000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 203188803 1250 203187553 203187583
    0x150905041502040819152301050a0b1206030109060507032f0a050904060305160905071b020f042d0513050a0b0919080a03050907050a05132912 63
    0x103030b9054045c0100c0d284a1010060701c505009519900345a10684074070b0711408218150f000c1c4020340e001c244500500141c01241c00350400356010310100c0e580405a03000c1803525040ca00d07440d03448a0103e07024100090300241024104024001314541540003440e0070f01d030a118103aa18400c000094010810010755030602540030044960507034072410003810000d00240002c642c6a0b9a5510140703041c912414801ca000c2a0759001e1000c601e45010b100d030030001500c0d1212054100c06114014000300f076500911882188242030f02a407502e402814880b94072410300391404c0d80006d9000054285020b0001140b8903110010706402c0031015601c8a0f15040001030900a040759a07030900c4100c064403e082500ca4007694920030520340d1002c150442c4500305c0281c659201345d00180a80d1000b5003c1511504500c105219030346900c00c4401c00c550040301c0e04003e102451020200414010408081c086480c8120142e4a507004d814400040801d0b655041e04442e42d03000b40b5100c1c004081ca0710a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 203190053 1250 203188803 203188813
    0x5040507030c0e0f0a0512060708130c0501050703030e10151d0408030618070e13050601080a0f0213080a03020f030313020402030601110a1209080a0506191509050415020408 76
    0x5400c062040070804040a031005d1499034958000980189040d03007801d805610800801c40c02d1940041d600790400300000c00d02d40402e14560318800311900c0340c001c41d81000b10214881090502c203822100007070000c0310a4a01e44504942004050100c0a190150115000c0b0002510301030301041840080b000100d074003019156a9916182540090020341e40700c0c0d44000d4004508016030b01150060390306844650f890f6110301d042c06880c1c0d40e0030320905103880c0b0740b4003048200e0b41c0241c03c0c0c60740071000f01d600180400040d284100207004071401181d01c0c1115500100d948030b40080d0480c07003180079400b00d41846000c000e045a032031008544001001d041d129075980181080d030085c3d0307080310050411150007509800c407185028604403054603040902280e030440c1ca03420414441c042c00b0300c00041c050216a0340c580302d54400c80640180c051100b03c059034507900342d0b558031205109000444074650607540d041c001005c1c100989054402010603c1c180c8003e103c00e02c2110704980d0000b0143c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 203191303 1250 203190053 203190077
    0xa0302070e0a15060503061503060f040b2106010801050f0108070b07020a0509042603010602030a05031e01061d0105130303110a2f181602030d020a050405040507030c 73
    0x240100e20050950700b18161245003030030003c0711102c07225000e401300d80c0e10b058803454400c042010352403924010781503807403041050101c2a00c9030071084001a5060310301040380c0b10700001043c2c441c0342031070304520300d000505505107040d14082812812500d00c00300922454031502c0065002950030312969840d94042902001402d2040d009000d1140c0010610036116540301c1c04148001c604070b80840701e42c8125050fa080e2144040d41c13008290208008040c11981000400307940c80c410350180005000c400b01c00100c0e40900c03940d141603014458403601d6519607452101034428045900c1c0c01c00400580450609203510a1050b604400b50801212588518540301a900715803000310b4901e081c0a50841140822800003840c048075012284107146072040302131a20a50f214280f0880c418010702d101401c038080d420300c21075007061881004480d00080c205c001d038a944104084003400d00e00105205e03401b10f800c28090b008603541a102070010355a47d4100310111090a1081004500382032018 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 203192553 1250 203191303 203191319
    0x30616120209090115050f03070804120201090c05150408030a02010c08070206060f01030e030c0d120e0102031b030903070f0506010e090c0d0b0711070e011d090c010804111207030c080a030207 84
    0x10708040002410047d01c5c210f02c42010106662040b5081404961401c042c03004018015041001225030780c8020003101d011a61400d200c500c0c14071840d4030488a1920791000c3c3e844503005c6a00820101d01103994840102c40040d01804105170184007240c081d1001034001c40c000303d9094814400102228109131240d40198000c105000d0406c400348403d00000180d0384007080170b40c0c03590000e52205c0ca254010113034501d042c0d403811076a001c0360b6401030043c00103000610903a08403c010f5803d0183e1070359074201e0050f245000d0b40001270300070894500c1c030006000c2c010441e903050b1030291780c0c1c4550343c0d942d10f5002655090250f07402508501403604a6000c5070390106400e401c252207140900504920800884c500030341c41d00400c484014040040100303018101d003004800e4850001c441551505000c00b80e210800c4038405414802c181000a04212681010400c1640028031504461204402080e9502043e00045605510385a40810a58400030342d001c940390b410360050072038038104000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 203193803 1250 203192553 203192579
    0x1180e010e040c030203150a0f111605030c0303011811070206071203060521012d020d092a231c0f08120106050a0e01030c0e0306161202090901 63
    0x1501c01a451400200050750181f28040c01c0e50b0080c04000954280102c25070300312a18103042101052405000c80e5425000e4415145081281d181c900640c40c011309103142540310340030441506000000000c9110307500400c40b040741d06a8070204001031601c43c0010700309846040340281d8080000d12083d4001900c400d540c041804c1c2500d00840c905a485000c03030100414980a5041c0b00c074801a02484a9000d04c14001881000e10701210700c0034124a072a414560b0008111100310380019040101c0701781508400c4045a00c130503600a240f501880c1000c030030005604030320407500d14000005480074840307107040403a00100d0b81c0f65a514000c2c0301b0040c2502441c200008000908080c68000c50101c0c4003801180d40508040c56494204c51402882c90005812100030b001050242e240000c0d4401c0942603400700a0800181e940520407060300ea01c0300e0303a042954144100010040445208030807405901482c3c0c0f500004000ca048040059001e01c441c0650040303c01d00041103031041c0000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 203195053 1250 203193803 203193811
    0x109080f0711030a0f0230010f0b10080403050d020f190305090a111e03010e07080d02070e0f2a04061713031b0c030b0402010e180f0603160e0601180e010e 68
    0x1407103001c40348901000c6c9600801c7c01046d02042c1d545240184680e0b03580c2c02407091898040305d00301d203c0b4443c0c002c080c00c0114080c2c8040d0400a003c41e218410b0781055049030f40c3d102d00f00f50307400d886d00c0a02c0d9204410103400b020050000f800d28000c2402c1460000e08020220340c840144041d12401109210310000c040760003503c2180000c1007484039440a100d032400180c01d001c00781140310b0400c0001d502d002000c1d8008021540003080400c08103500d403100c80e4120880400141d825155003030001c190008512131500e01002c001044102d0111060040048850307503182e581c6420000790b0a07001354602118880e1059620901041c0040c0c400c80700d00100c0421111715401c103c00c1900d42c00b81010f07180e04212600b101c0b1006105c01d41d82c20000e88003104100315030044661201d003e8254810070040e19041d012040080070880760b90342031000ba8610740d070500d191220301f96102c4150854000c01e88901d40801d69004145d01c61b80142c801010640c1e070b24005020a82c0d103005c5641c00740d510014 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 203196303 1250 203195053 203195089
    0x20c060d0609020409091718040b0f0603070c0c150c02091b0d1e02030408070b070e0301020a020c0f01020f1203060406050d032d0e060c0109080f0711030a0f02 70
    0x4107010482c1d24891018101810314004005071402d15840c00b041c40f6800501901614001800203403d000b5000710103620001c015540418409440000305522007140b14602e03a0100c00841001407240c0e01000d4204002e00a001c0014110f42e00c900900c0340c0a5607001c8000060030811481c0007505040200940000c6821100740010300c6150034200103030811407044000917203408841500c42c010360381006e640c00401400710705d1400d150342c0c0c06c4114810070100405140d200030000e160b00d4052076020540c200007070000d55843c25042402500c40316100e41c244d1082c905a04c0c0c16065510024002d220f0b40107150007440c031070344a54000841c60304010207007644280c070b814021030261254103640181610a440c0e02000d601100e160003140008900048003007024041265280c43e417064a0100340a41900d0941d03030740303084407042c034090654220064140200003400300624005040200b4090f4040c041210340f01d21068101501c5100f91a0040c0202c0c6001130700b0400341c40c0a400080088400c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 203197553 1250 203196303 203196311
    0x23030a051b030304050a03020705030c09130201030f1a090c0a05030415020403050a060c0813110d020d06061d07170a020306040209030730210c0605011e08010c020c060d 74
    0x381c0c41c418590ba108890032030b82ea8208500640400d80c0401c5140081d003022000f8040d5802030704080303900d50000500990508483c13441103015640a0f078811030a51a84c0c0500388075443c8001c555170004040d4040c014007450840c0d0004034034a01c0c0c01c06580394036940e581c400d80b80d03803200e882c2d103c0c0c100092024050350a500700400000203804000d2456038600c11000400c5414020b40080c1122070001c04010b1386804080485002444400c1c140d882040304488072620340e815030010816850001c40c00038601032410502041030340807514080071131412441d00000355500d1040445030f80030f8510700741d1201032005d00450314205c0c55801455100d28017800c010f0511740050002881d02d812680840c0700407003440041e04d614100d0f840080502c09072200c111404820300e54621000d11080000341c40d0420001d070781e201c0e1041c810b5490858540e0068028080355031503802e4206140c440d141a01c12300f00040c4800100c0c400107005070424403142da0050b110781f0503500240055584080040500709030341e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 203198803 1250 203197553 203197597
    0x15050405070e07120501061806030c02030d0207080702030c0616060c170717011d0a05040201090b0408070503060609070219030207152106051c021c030c23030a05 71
    0x148451030703103c1c903070b103544600d0580f50f541c44101c200c86060b0040010032809400540700c05a10061841c200c4000c1c0c90300250900904e1070803400c6000c0c0c2c0f09150405c40c0002880420300c03144c0c00280240d0350085042d030700740c0e041c0101084581e125050300d0f45900344194a815011502951281c9890900b41c01c042105040780401d2182c2542c0031101d24000ca00b00304851661b484d400700a550140c02c401e448895000082d001e01230b0140001032031041c2c0e603902c40740000e085901c2003820200401034810740948851315100309548a81e02d031300480740284035a100086031441d10300a0300307018041c40c0d0090460458182d00c003c0c0410b6542c1000d0702076203d101c42c00a070a040d81c1503117615195144d682c03148918080641c1440440b88050b040246a080001c14401c03550b99001090300010100004403a07201e661004c515503900c01e13450406a0510401104145074120f1001c0103503500c1030710080052980343c1c01028603100f140c1c00114955000780890a1558040d0b001010303000310f0b414103040d10720341d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 203200053 1250 203198803 203198819
    0x1a03070915020a0f05030d05010503070513050907031707030e061312021f03090c1a09121002070303021b070f1206020915090901081207120e10110c0402071505040507 73
    0x40301c0001182d0503400003401f00c00f040c00c640304d05405020b0880c06050707001e2510707000030800a074440f000e6000d10b0381e8501240580300100402c6000b50ba2040c000104c482100c0169107058002c00c5054003c00c410b00e500c80740c03524107071003180e6001110981d0f15281c1410183c001d44460580c2d142203030800300041d001002d00c82c003070040301000040c9903008201500b2910746084642e07a9984025500610b05000c14942c0f1010810360740915000e581e40c040818024107643d180440a001d2210064400194182070650507001000417901d050640054110716180c2e02d40d40d203910744140f5000c0390030040709209244001040d84101030003070501509211000c0c002039036000000382802c601140005210080c0d051034507640303004118000c040c1c400c0c070b200540908014410385900501c2540c80d1164243c083d8068280c101030000b02515182d2a51040e100217070449a908200350032900c200003d07030550b46818000c035032103141d110001c0035000b00e00c2543c4034050100a0800c6843d0701448001080d240 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 203201303 1250 203200053 203200073
    0x20c100908030603190206040603050712020a0201050f07020d080705210c040e0601091406070303090b1f08070302180a0902030d020a03090f120209100504060308041a03070915020a 79
    0x107004201440da24203001080500e00950ba0440801c6171413442d9a003005665694181c0b000c841c664100440c0e641d66048089a04284c40c10014451910110311543c46a0b0305500c0184124241c1c68400c82d240c989c1c0b40c00f80d9884901c001c0300b000040c1d1090009594521580241c01d401d2240c0d85ca030000c56680c2c1d28508551034045400315011000414204092410f030000d494005100b801d101036214185030f08020422640b411590103607800203544410188242e020040a94106140080f141801d69025040c4040305880040c0102d040340701040f090070200d03164007220303401030124426a83d06d507203503510098024098810702d541c4407203620240c0c4051000880040041c0c3c0030380030f412420300d00035041c8911500304ca00700181c070040500c101d01341d0400100500d90125014000b0781d4800c12007a107600c0175901300f140c00c203080c400000204484030020f08180c03100c2c1a00d1520300c0741041d00c80041400304a81c014005000c000d01000060140c500740004681d10344103860026440f81c591903410 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 203202553 1250 203201303 203201321
    0xc0311040806041a0f0f090a081917090309041e060f1d1005060d0906060b09011202091c050102090a0605030402040c170a0209030a1e03020f010603080706020c10 71
    0x142c0040c82000100000c001a0030502105040c04040c582001040580c056400a05a018a4001c1004101080020804100e0b62070b070184046036070785045e072002405c01c0303419020400441d28950103000c0b1561002d010314810007801008505229001080202414856104a4958508180d400c52820427401241c01519441101040040ca0000c1601007500c11040741e10703411068009020548101e00001021900100d4070319071901040028071004003002d030001014285814000136a408209018020641098881050941000103181d042c0d01c140305d001a80108000c01d2800070110110710101080d000e00f000505101610001c581d00001d140c0041012450203c2007100314508bd028000701101d03146407100c030b080001d9414210002c0e02902c213002194000c20034104a4808005032112250021908a00b1004030b071500404402184401c0d001400380427040342c2185c1050040710116540240442c1c42c00f80c603521440000d40040c802c1c3c00990281e0303818458411040c1c0140002 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 203203803 1250 203202553 203202569
    0x13030b010519030b010909060b04060e0105030115150809120c060a1b0206010614131205010e060412080a0b0916020c0f090406090f080a020a060b010813060c031104 72
    0x10a505010401c03680c1011070141c80b0300c44044030024000201605415070441c0c030800c0003c00c3c02007040c54050090700042c0c01203900540703030010000701024005a2f044c100c6600307030000c100102c1054190508118503026103860b44030b014407442c0301c451040c14515848a0041e0948080000b0910605a03591180000180a03400715080c0701e03909659124400c1d0259005c18000d40e0386000250294a507401482070f001802045031070003101c02000d104030742c61014070729043c0441c01e483e0710300300700500c00b10403042d10250320b0540b9040041034000703203030381c001c0b03400c0300300c00f01031864866040f47d071036074000d01030301010361540000030094132030a0051707010328400e10701d078202c4041c060402031401810381c450350710031191040c626040e502c0c3d03969020b4005030401350118041069040000c20b2107003501006009160004100e1b94159020601d0ba0301540301d070106001070304c8403000444050b10b0a580c00b00040d1030540382c840c0003c3e05a03011841d10f9a01d803d011401c0341e00c00314070501da40c200d9813250030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 203205053 1250 203203803 203203823
    0x411011b03030b0319031205041704030602070c0b09130b011e0c0b0a0c0504050402091f09030b01050103021e07050c09010b1e13030f06090807150b01110c0409081303 73
    0x450345018003c0140c0c0540c0071105068280c1c0c5c41e02d005003818100700040d00740c03e03030b10300c042028003440d070032000c044002004038030f6a12996840c06000a521490302510507084d158001306244030054122035186400030890341a04286154110083c18060030a506202c1d410103842002501031140b400d016589841c0e4070340201007070a14241004004108a10291034031200d8681c158009007620f05a410640340141c6951403903000c90841c0b11441c0036003905044142026540c0750b401003506003628480e50450740035999400064059014644164140464400300d150070f61132000060f02d281d9008100300e80c00b00b4150000301d00054401e8001e083c00c4440082d0b40c8903c07015040201e000f410ba41422540382036070350440c9410042c81c1740001804000d19500301c1007448080c3e000209484d411640035540c80c2c4084c50040e07250070a0221441d4901e080501030046903001d6032642440e03d1688001d03010000c82c0704200802450360900844e85003800f480021849100b45410801541c41070200709 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 203206303 1250 203205053 203205071
    0x1050414012a120905150907090c0504030204090809040f05150d0c03030c0c09061401030e0c0d120c06141b0301030f060213090e07050405011d0411011b0303 69
    0x903080d80c4002c00c040350720185075a201d1142526889112007004030302e14244419501280c080005461a501d010340380703200b90510b039540d100d0400040da000300c003290b0446010665541041d070030b91310a1030407000400c0c82440204058146604150000e40c82400040d03d800003000c0080c0807a0300c0c5001c2e8800305540e9034200620070003101c40d1401185e10880e20700390405515036800d6407030040c43c00003d08201500d4900700070040a0103e40c0054007680005120450721082c0d0034a41040d909000c81c00641014064191903d010031199544d41c8090100180305103a13481711070074201070900d40c1c1c0800a50003c0350740030a402c2c3c4111500c1c020076014651107800c0c0544510402d40c88201d2080f600f80e000c10042000038042510070b0703600c9a01040241e15002460b107514410304c0268804690036003044841690341c13001203840403c0c1c45045074100306598803014020300d0b0444441424280c03070f581e2804103007c40e9400312540c1004005150210700c10280a034180c026102c000012008252580d00c9a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 203207553 1250 203206303 203206343
    0xd0902040c03150f050303070204150e0c03040204060b0327030915040302090105030607020a1202010b090108060a0c0201110711031e070e09060708070c0f021f090906080601180e010504 81
    0x400044c0014070500c110281004002a160310803e080280300341d03624540014400c0303016584000038400c05682c0000d074a4007240c074480584c0119009c074881c5203480e80114200d0144030a0340c3c06001c80100d42d44a0f24610721180c050055800b059496510007800102d5403551407611030ad0804800c00d5440e80c8031843d500c107010400720180c10440c4aa00600100002d1a80c0080ca0340302071034000c000e620004594400690040110407490303500501c1d1480003081c003601c00156030340102d039181c1c4208100300030070344100d00725600d20001381c0c00814204060350100d01c0301c58903c071030307548000c06a40d02d560240900c10848140c5030100003580c0c00c034802c1004003059246d15164071580c1040030b0a154584941c00400a001c01030440d014084030300006030602071103c03500203100744d010b000d26415040040c1e01d000007146814040c000121a00300109440b00d240c02003e007100c80c0140203002d107900b4030700320441b48800289041c00003a926800c16080340307024000c160180f80544441c020001d007038544 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 203208803 1250 203207553 203207591
    0x703150606021c0e0105031504110c061303050f0d02090904060606090603020406051b030d0c0302180a0e0f06030a060204091b03020309070902030903160501050f0f0108030307050d0902040c03 84
    0x900070402e6003d0100d0f80b00c2d0708a903400070380040902e0100c2e81d07995405d00014122080007411a001351402c0018a0408641402052510030980854240b42d59221031207011000c0204002c0000e90f007031103030010200e1440c0186c1101c9030039020150400b001440454082d007403c40c0c083d00c100d0341750901000103640200541e4064103c03840c040d40b5141c28800042d00034800d0300c44400046071058120031031500280700b0740340c8600c1160010320400010b510010041d4201d296101c0e11380303803106a001964a0310050001c100c48002c0c00318501560746c220140c8403a0401403209415000c3d01c18500b0000303e0724802040601240d030000075244400d5001c1081441880c4800e41c01e01d4410000c0c0f1a1800d8000b41030002c450513404c0240e544e90b96240f07640d007540150344001c2d51958900c3d10020401c2819000248250100a0960390340d039180068200400828855450960000c1011849852243d0020401c9070540d18011036a10380c550b005c04c00311014100d21304002692800400d50303280c88207203 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 203210053 1250 203208803 203208823
    0x3050a1101081f0b0904060302031006090f0605090a02070f0209010303030e07090e1c1803080c01140705070f0813031109011401020705060322030206040b1006080f0603070315060602 80
    0x1c071050b04000c0818088443c030205004602c030210011074009465940d64000c07002460b405800c1c3c502820344030003040c0c040c000038018070051134100702640b20520060311400c811210010701000b00e0707448408901c130080d80010025102d055001d5803807005a03c03210b03442070080d4825540041d4010400c10302c0c42c201482a040000020300b1b02881840c089400208a001400300f00000301c41e64403103200c195a41c40c103503034020300c0d22801d2a5000003880201c4c0084c003000d814a0000b4485840103440d03003800c0200466010000c40c03420300405020801e1107400404040c42005242d00e414011544100c2c15195a2f004489504281508204500b00f81042e280142041c6640c0203000002600103900e07040c0710300800b07000d01004400151115801d41500d140f01c020310040c10100307000c500b0004d40396582140c054030103003d1007011503412034100500c4001c480499039034091503143d0134640130a17541c0c041c004a0b451310940c100131010481e02e10300d030344204ca028240003600b01d181031000b0707041c105914 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 203211303 1250 203210053 203210071
    0x302030a0206160906271202030606030102130b03190911030c03070b041e0302060403030c05060c27012c010e1807030c0212030c0a030b040e0c090a020403050a110108 73
    0x100c06140f410741c20003451400d031042414006804482c00020070007041c8200aa20f02c088155000012000da501011400031030094090b1041d070307a510024103090340b10342180c0000c0d8000056041010825100c042d60f0040700780000c94001403000040d244c15183e40403401d4070f81071103100d03004034240303420440b4945000382034018080c520302e446178218181c0540d00c01d080d21202c2c8285800d03070030380d2880e0808003c1c41e030082c007043d2140e450342030091074682902801c40d528881d83c030125040d008401300355080d19406036031502e481d2140c0404081c0401c0906400c90502c2008101380b501c0594000e52000c40206043c0c40c6901c5609030f000041c010100302c0328542c007540300c0c0800383d4003500c94454503950180e031a08020451241000d030407481c0440c1040302110f0094044248840031000500500f84801140d906001e040f25103c2080200d642e02e000c8454564440c2d100d0200c141084d00105601c003450b110011704060744ca45400b07040075100c0d242210380c0751101030314000035038100310103a81101e140c03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 203212553 1250 203211303 203211331
    0x4050f060906060901200102181c170d0f0e010506010c0803131a04030203030619050f150f0a020f060f060d0822060201020903010b01030e10050c0d02070302030a0206 73
    0x800100320700890103490340307004a0700000d43d410141d000b50318881074254628030307012203141038101060003034001e1081d1000001004059a4482c43c107800311844003c812117214001c0c08603951440c0c3c0580d400c10760040500800d00c815040000203109032001034402c07100209510f07c000708c0e500d08403000102282c2c1070100c840c1d5035402040840c0c06482d4000700f1007202841480240c20038030741c0c14842c03010000b020042d2a00304810141d020000d0340c000d80082e216102a2906014003580d40c0580d4061075401c240c00101c05525494040b4550948528489e003051800b01c80015899840d030004104c0800f5071b01040348908a580200302c1e81d58044222856000035041c00b000207015010300c804090078400000c52510034203440c101100d00c002c1e10001c40c0040c2d0959481010713021f5040031140c170340310703511308004001c4070750007401000d10109461020380700c20031514081200604014142a0100c54207202d201e00840380340c4010040180a90011a01d6062006000707290010040003c0850055 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 203213803 1250 203212553 203212561
    0x210b13020c10020319151511070605072111030c0109031409060304080a0203130303080411010f0905061b060709031407030809060d150314010e0f060114190b0904050f 73
    0x164010180d40311001c800c000c0b0b4100a20b00c0044000761320342e0080407031847c6410381640b035603403c0a0134140f41c0c0e140c0000c1d143c5455860005170360703038020500e01404490700400205000c5149659002130308045041c1500c04401c4d09035503070b1460300810007101140c0c0d9038041010174190032110705046001440342a0740740c01d60340c40106200d80000b402c01418032102042407041e5500030304c1030b6820345c5001c1d801000120340d6030034024060032064401f039810222411004443c0d5110b03401c0056440c4041c0c403068812442c002c18000c031903010403440802110030b1224040031520034882103018820350b650700f200c11070450801c03502501c0b600004600f564050304041000824140030b03103c1c840404c8801d142c0300c480d5220042d005d01105520701004031183c06000c01042a0000c8190f10300031000000c0020740304d0050501e0303541c11f4070464200c0c3c503880790b00100412001108090501040a8000400c0c210080100ca8480030380303400c2400700d650041080f960700e08040c4122036024405004c05201420 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 203215053 1250 203213803 203213821
    0x15220c03060506010521071103070507031115041d130b0a090c0b030403030606020c060c0613030908151906030308040201201f05070207030201210b13020c100203 71
    0x2085210040007a5281c000080140e030091040d2504500718482c00100d9000500001403195800c8580368003260800780c10701d03041300000058a5006620000418116045491b400f209440c40c904070340d0301040c1c0c1c040715590a01d0389001341000704440c803103c0c005031aa8041d000311039071000700400407140c42041c40e140442d00110100b034100b111504005000d608034100030b0b4541601350072903a000407000060100b0035500d0303840282111407039402d2713070242d007181c208001d018460320300f48a145502a4000c00c0941504420032504d02c1c1c4241010446150ba030b001550414034214003040140c10b002c420410100d908058050500d49500d40030000f0a0950340d0281070000c01500c06410084025008643c0916101e00721800d800450700b00e8220342d018480d110780740e80c12a11107440c40d40c10103010405440c00000d408040c0e82d41610740c1c440001e03061690700344542084500da0f01c0740e0f4880d4084032981c0c80c3c0d10a462010900740801507a00c04c0f005201038600340c29050341c400018170410030059205 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 203216303 1250 203215053 203215073
    0x4110d02131e020f092b0201030b04090203151603020403030504090510030506100914060306060108040f0209191b020c13090c1e09180803040f051522 66
    0x1100040000c1d505601d58440c8a0742c442c021021418a200107407401c1d144502c14040d003001603080307555000e1a40c8036015084603900664400b6000c41d00f10824100540c040d400c441c009030302c041c000060340800368001a10f4014040c0d14204121494014800b0360134004041861910003820250310f8030703182d43e500030400d108611030190316554a0000caa0881c0c890380d118001150000304403501d03800c0c000404215001a8814685001e140c80740b25603c080f94080114418100100a84602d90303a000c015200e01500420807104005041042c00040e99152541c9001c0e0407210040f00c0301000f02001d4104a68140d0341482e40608001c2480e01c4442d4001000080311000792800c40c0400b1034401c0c000d010380181100108640e600f02000b15907080c10745c03c200310750341521000342d120543c0c800040302102c0e01d207400320005c0c10f0088011400328414600440c0c0091042c20240c034610240e450301414000e24440100b140140e071030a1003000421074402003c04100b038100552200b0040d55041c03441 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 203217553 1250 203216303 203216329
    0x4050108130b07111005240f030304060c15020304050c040b0415050105160501021b160f09050c0c100b04050a110d05040515010311030d050a1706120a03050304110d02 73
    0x488030101c0300741800203001d4411a450620411b0099040c03031500480100b10801940350f409001508045840ca00b414903c1034a05c0c0141c0a1450142014006ca4003d101d10308140c07112002e04181c0c00740c68140f440118030450140020300100700d0404c04200c20740d204040110702c581e09002044c003507000d1308410182141c20908000d60347c0c400c1c0c00340c0000000b42503400a0702e50751010620701c80280726850120003a12085081c1d55410050103e00c0102100e41d004189984038442e00c103000c610696400b041e00000c0c11003c8604140c250309816142010440010f1036013500e4180b04e1070786d800d00c0d00482b5080385014030103008410851020650a000304180111750035216808281407050034008001c035100f0042c1104020360b141d080400c580c6240002c99402481031010443c0072507c1042a144c1007045a5905010b20441810101460714007070030321544140090701e451011401000910305962103910392544074038140c101090038a240207600341c080d0b94010300200043c2c1e58290b4440309 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 203218803 1250 203217553 203217557
    0xc021e1e120d0305040b0112030f0c02011b050309011701121113050403050c060f10031101111e07090603020f120a05070f14011d0f0d060f0204050108130b07 69
    0x501010300c0001880d040315a080e500442c05000044058540e1681000d84a0741c00b484410103140da03603503901418a086c02d0005000544440e102c2030006118080c2c0100b030f1801413511008003003d01c41001c245207030000003194103620008596020b075801050348100203400c007040301043e41c03405031030407003a4880b00300007419007c0305000f07540180c0c1d5110080000c2c02c4c039400708101c0d918141c81d025003154010494584c103803007188001001610310102407880340041114009255246950350b101401103007076028184a012610180751810800022001c0c0182701e000070026598403459505007255a0040b803043c1d4200581800503845009140c0010074040d40c1140d01c07030040100c014100604800024140d0090400c00075030200c40000b808150b41c0005e910181d904001001525181030000d1038a800100c828595a01c0340b0700703080d049014502c080c10035000561166038039000c66040e20100390200c1c2d400b01d0300f071100d540c1c404001c1d5440340c00840d0a507420f035402d446c0c00003880c000400d0602 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 203220053 1250 203218803 203218849
    0x6181603020a050f04110301030b0105011d03070e04240b01090504090b01120f1203050a18050a020111031e0c0d0f050f030604020712030905120a0c0b07050c07060c021e 74
    0x303400c1c4c541b644080080416081030617220f5840f440d01d544090b07001c0c41454005000c00d92041303007000034514203020b494401070080003005d18020301e140008a00400c240d52500c02d1010600305203d400341101004041c1c82e0001070001c074004009070013041c450300441c1c02180781000741400986104102419240174031403294201280f85040324604042503401882041110041c1070390359010380129000f000100024058038404c04d0403590b008041b41c2c8068000c0e48a00a0500507500801c600c624401e00982503a2400321807175a00b20242100c25045020550005030360001034100340300500404002c0e10b0094603201241e0402046401520041040c42e000040800c0f0780b5501d660450380b00a5000b41800d010210314000600100500d000564585c01104401030540120000b1901c610141d51030340c00182613107442c1c1c1e85110782d0042c8501c4c20301004109141d440281085100001d003ca5070314070740e95200da4070610140c0b400e03000c170305010545440c0307009690b940c40780c10f252010304980c90091 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 203221303 1250 203220053 203220079
    0x402031e1602190c081501030605010b0306031c0909060602100f05010e180304120803180708120304020a050a0b0c0d2a030e060301090c020601081204051c0506181603020a05 76
    0xa4142021640708007100d200e04a030110001c0c08a1b401203040320701401e400c000e2a03917107800c00f0383d25110031100180e26801000079403c0c052408103220742c07040c00b1443c08024080c0c943d44500c0468900750413800150748585003050364140f01e4010b01001c43c000c40418881545014030b0301e003d007800030b441640700341000e924101c8000030400c240c9000f041d01407180c0302d40d4181414180195402550800b98190a40010040700c4000060000417548080020000351404101004040c3c1001e00104c0c2e022650f0340c000a41d5680d805c1d8840058a2900c1299560b0204088064a024400c03d0014207000300c042411040050b0306030240c95028405001500c1124a0f01e001c030b030003099090610754040d2002c00085100d142c690f2100070765032103070303001c48615988410003590b0f58a2540030040154408000c00d200c503040003502e030040d1540d1044050801e0701e4030340c0c1e018117013601101c50042035021304d0440500418104108001c000c40840c10114030350864003c204011114082e0324024415904c0b10 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 203222553 1250 203221303 203221313
    0x30c0c011202120c0720030d0e18070e0a090b030606090403030e070803090111010501120f0c12030203030703050f04210c08040308090102010c051c1107020402031e160219 75
    0x300c3c14055001d01152542c0f4108010000b1030b00b101c01d041d50050034500004041c2125064000c0d840032000300282080424810101ca80c5509038070134a0700654100420501a50070b50201d6010314081e0f02e81d0040d500307a003814412a0741240d8003022820303082c5100f00307a0545007c54040c0d04481c050307403030b0440c0399600d081c05e502400640d0584003c034840c803000041c5050001c00640b00710340c401d0782c846c003a980c844c48800e402d0b180e003030040d8036200c10441000d070b00285107605c0700d04020f481506020380040e507424098110858046091340075030000410001559418800c9940c4440c0222900f03000e810907450b90080015181014a04100e254001c8000369004040c1c0040c85603009140b503950356100d240082580e04165055400366092100d0001e4450040c800d842c6098901e1400c4101040201074070300103046410241c82da0000c0400028015031605c5c001140300f0700400c2d140e086184440d642540385088002c0041483c026810701401400360702080e565210011514450440206400c00c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 203223803 1250 203222553 203222557
    0xe0312030c210412020f120405040903030e16080d0801030308070f1407050325030c082a0a0507090e0a170903070e01080105060d0c0513090803090106080609030c0c011202 75
    0x8440703030a20442c100310401000c3c0d4064a016102d90382510b001c0030200e02215600c40595200b50403210040c04288041d04056100001082c001e143c04102840c01c0b1000034103103901d079035400c48a218201c1c0c06105410701004881408801c6203810308130313589952002071024030007a020000300208000d242d43d00c284583c0d80c80850460742000542d6603055440c084c7c0d9a94020750860841d1881000300d00b088121005421a20316099218044024020b544100642d8041240c100d54035500e41210511040300b0301450000e00109001440100388074140203103048001d034001050b1f103003800c886610101001c1a141503140d8070490311001c90311000c0b03003e40240500000340f505486403001c002020311074103240c40d04075000c101c000c21250701c4020a020320030308507031b05c043c180441d46041040781d805c104035500d8180f46101d20000d542c0c5455a118155603000341c4074440d2580d16098107018201c0140304854128160301c3c0254604882440d14546076000000c8481c1440520340510885202c0342d01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 203225053 1250 203223803 203223847
    0x1051201061d09090309090a0513020603040302070f0f05010305151c14060c1b060708070f02010b0d110307050a05030a080c1e01060303090902030907090509010b06070f030e0312030c 80
    0x8150040e00c0c02801017035aa030071540c03140d403141d0410400b159500780a0b10a26004490828000070010700c19001d0250f1944050000c43c02c40c41144000604030091200fa580506081003881e010f00b0b103010300050580d5000f4244030181c44803e9950300c00c540c1e900c00000c064036100d04094100039940d08028001c04a2020ba038905401002d04000507024840d0040042c007240c5140482e40e40d03802030741c4580d9282c0032034035000400e0b108000304141600401d001545044540700102c7d4080e911004600c0012000c1003c80c0e000e988160402000c1c5400c0c44403e007d0f040030340315074660078a4900065659414020040c0020400040820300354405200300c0f10800c81f0380b44d031400603034110b0000030b0003008180b06c1038000078221030000c1503008050003281c1c043c03481c600003005440d0070010f0703403030040c40d0151102c0718940d66140d9101a58455001500000b03009014034200900d980c01d01034607000b0751400703161094001e011240d841005c0c007400d5940208900041588519101d402d4031b0303041041c20 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 203226303 1250 203225053 203225059
    0xc090612060e0f01030203011805030d050615070308010611010b06040b0915070b0603071401020604060e070f06030204170d09030f030c0803010308030a0f0501290409021b0c01051201061d 82
    0x400c00c0c0c96aa01c3c1ea018102c0e482039008025005090101c06142d500c101d0000b08550010404865154802c1d0025030f0403810042243e01000244040d409059002c1001140401c894000401c0b00a1b0492040004105035400a00c510501c910006105108500130383d03400d400d020406441d181c440750b201c540f2901d140c01c1556074071800381c24003010381c04007211310510902c03031690045640c2d04940311700501500180c000346503a4907940e449070050b16074984000e40034402d0b204000ba500703403080300340d0b00100305e035460040e44c41d420055611608019024992541c0c2d0000c420001d24a40c8040e04a003101c2c0c00a810394842c208614044440e50310806024040500110003c428011030200440c0180d010103000c00ac82d6012030082c0042d90000d1066004110401c0c1890b00742400100e454404200c034010000d18103a11200040c0403038214a09004002c03210780303203800c507145040002800280003400c256003001c2e103d07020040c400c041406450704000794090b03103041d269118604580300090007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 203227553 1250 203226303 203226329
    0x806031e121c050106030902090402090601030902150903060f04170a020f120d05071d15070204021303020102060906040b130204090f03030203151806040506060c0601060e130c09061206 81
    0x30b60099001009592075284000d0f107040d0001031460300a204004e030150f4054103480700c0b43d6594007008a048001450320f0b06054a130010240140d580403980e00f0004080e481290711030b000c41c0185854480c0003450380d62051815402e1002040b504d5001d010f54400007003144d40e444000c90400c908000108010100f0b0f489114048005c0c05048005458101c41d03104082100da90341d150100e410500d0591995808104504c0700905070030a2024460b4411000e045075203059036650209013260f002560442e0022003441d000c0c001c569042c006c494000c00250000c0240b400c180c1c03241064800090300c00c4c60005440341d03043c811901e498004030f0701076070051880300002d0240d05020b0046d40c8112501c80440c0c05100c4421494580b014604101c00e0762440001d41d10758845041c440144070141c00d4550215050002d075010490030400140138045903510039050942040c20300c68011005111060401c0c00c10380081181c42d44007c001d011603845150402220029000d414010500c1e504600c0b071790307006 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 203228803 1250 203227553 203227567
    0xc080609010207111e01030f0b15031510050d05190f05060a06020a080913110a0201061406040e0f19020f04031703010315091704030303090c05010806031e12 69
    0x19806400300c1c1c4d006448250900420104003c0c2198281c1184048410708501c06201c6512070f134403000030380804200000d03601c640800041d940c1103581701006407202e400400c0103401e001d00d1700c228103021310030f9403441c210718202b040c00380c0140031310388400228540c3c0b04001100c02c50301090306210f20b42c01d11000c010701e101080310790016040480f40103024050076040000c1051000490300b0503ea0042c0c01c0e182495070130810000007000c0c06e45000c0c0d01c641c8444200103c555030200902d540041034000080700c901c1c213003071a510340e801c8101241c0301e60b5092004014030300e120420164131582800900c9840d94a1164410a41d100ca040030900c8070b1000c9640701469007038030010802d4a0046144500300400b00105a10707910003400700410b40c00120403600c088940c2c9821049000d071080c54002d40f80c1c910365161000680042c0d0007580000d807240e105009010780b00c00c442c40500000c1c42d00e100e46142c24808640c0e5240030520840d00258403610707850310b07180180b01c445520303040d21007000c2d51303806 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 203230053 1250 203228803 203228821
    0x703021005070e1002060c04170c0a08070e060a1d180102130f0f0308220503060403030b0913021c020103020c1b121603030e0d151b0e15070c0806 64
    0x150f001c030560700401d070410442c0c00443c00040c1c407512074107a101c3c0061400b8108a42c080c8400040c80c5061054410f4641602d81940c0d003803040800b07001e401d4000c01c41d461814160f540d07a000060403050084543c41010301c288a61403083e0102000c15804c040003a80301d0101070f01003652800e105a4903544049264202c00a0080a2000b02c41d0008100d21f41c85407074414885000b0151b100c02460300c13000300603c0465001c0c0c450100500d4094a244181141c0d0361004241071039000c03182240080d0303840c4120082442d2101280c3d41041402ca00001307890942c0c2d0100b0f000c0c4804540030603481c0119030700282160b100b9012210034003040ca0aa03a081600380015154000b516940c251240300c618100c060303800d070001250100040d01803444041c8074a1610240d4842c402c07600519045603e100d01e8034041000103100c0f00280010080014100381c03100034484100382c4159400c0c00f0000d080184603100c1ea03c030880346020b22485103850750f4806a82c907058049a145070701010640c096035040141d1380e0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 203231303 1250 203230053 203230067
    0x20603191b09060305160c020d120216080d0f0e0a1806091409070501050a05190f021204291303081321060e070512010915060b030408070302100507 65
    0x1a0340c1c86181c119078490f001a020785104480f4880c04041c0011041c62240c46004800082070016100c100d02200d25241c04809070422070740340c0056440090701d0b2917104c0312819030a005050404c05840130100e1400000c12440302040403804115200020582c1d545c0e9074040e400c018000000c0d00085030412801c00c6e8058a081c0c45444c0c2d00c030b450054480324050700180400d10806c2c0100c041d010702c03401c0100644164110b40d0190303040180600c40408103003008412003600c001e03681c58002c2d25200d40303e0001d15180c540403c0108018080c801000342e0908415285034840540c036080078800144810b00c411805142200b40d2000b001050000610040c04000d140190b07510b0040c00c5070584550a01c0301c40101c2064800320440d90980080200d089927201c0c2281d002c0943c140d0354803607aa90700060801843c1046445076075560003624041240c0d0804c0f80282c0401107078140142c03450908415054003000300f000d40451000110002013600c2805146d0342c3c04101e03102000103040101e0010f00700c2c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 203232553 1250 203231303 203231351
    0x160303021605060909040b07030b0405040b0603160810051504090f1106030606120403030b040e0c090108060108030f0d06030c0605210c1603020f0d0201020705151302060319 76
    0x1001c121603011446050402c100c425070701c800b03000000e1684407a034840646000040041d420995111162030403680d0760f015a5000d2409100700208a0901508040c181590414031020003200c10034104450400400c40d04000d240c1210005013545e6610010303180c80443d051451b5020385040c3c0b0050030444040f010400050042114860a05080045c030180b8403050f10501e07480841402200030705907404a00a0b4000c0c0709180214142075214085015602c14000c2c0402c6030f003000300903c00b0350914400b124010400301c07000b000c541d4174003a0030603260f10a1403495591400000b80e0480c2100c07854001c4c1c801141e100580e0100c0b40c0d5a007100810541200c84e2855046d902d0704090344a1098185005025a0f680c4a400b4a040503241c032020701203440200450641c0115908454601000e02c9888c11140c07864002680e260314030701d009400c1c08004130800d41c03140d40203418002e9020201148035045541910301503640e40707c10190300d480443c40010f16000c01d0401c00c03451040390800c1041040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 203233803 1250 203232553 203232583
    0x80c011119020d0207150c0507030606090f150e0408070b100501030f02070b011404140a0203091525090504050a0603020307060c0213020a051c06060f050702030d1116030302 76
    0x607100200310126114902031034040e005a11241043c040c680002c5100c0c40030f030607241400ba0707200c42e00d56600c9040190640c401e940c9070b6515602005081a00c0c0120316000b40e50717020030040c00080d0b04808400720180d02424042c4440c0300c0014040241000881e02c00c40d800649100d8589440200200b685405026075030000c0d040c404403164014003070090f200030300e5110810740010783c2005100c1d003e5500d545040f5a0080c0c4450b442c2c2e5000104014843c00f540c800c0602681d01d1420035000c6241c07100e2000300401400340c0300100411400d400f1810050740a03106508040800a0030003102c0c180301c141c00882d401890041881019191075100f0030031244258191521140c4da443c05842c40a00c04901035000038030400e0b082c0941d9140e50003801100c026080080c2003100e032650481300c61030070102000b0342c190307038890503c10b803504424000d02003611498107504d49070107a80480d80781c1c80b0100b0707204240010501000340215040c410700c11007821038841c1c040707601d41e00c1c14000d580341100801007917 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 203235053 1250 203233803 203233837
    0x3271404062303030f070302011a030c0607060b041b0f02120c030702040b0d0611030a060905061309030e030613030e100905090c0f12090f01090308060409080c0111 72
    0x480c2014001d01c0c04941d10340007080030071500c1e28001401c04031840c88203949400204400034181d0078800107402054041d0b400040c000820180b4040c0e222503400c2e210f0300c0390348820074010050f95118200c40c403082e400840410b40c1231400000c038024002c01c0a440c402456400e02e800d000f1039024280858201043c0d088400542064224050b00d11444a210046410400c444000340c2059003240700b404802800c40120300703400e500c464048401c030b034035014025034001060105041c803e009940191103e1003040003e0308101c40042c0c482c404419011038902c2e03c035000070081c54010500d550360210040c043d2003451400c011007003290011710408401003105c0d40340c407140604040c4126852031b0016217034100f646c0c5c10181000303202c003401800091707039410801065004a480401601000b10a400b41040c1403e048200e43c0c140504040c40b84003030382c5004160004641d00c0a00343c0e8201c0000d5800051010440c241003140748a2400701c02003a600703000d0b8185511500d40010902c00490344034005e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 203236303 1250 203235053 203235089
    0x50c03060316030b06010c141b18061c060902040501061e0c0c0504091412180103140c1c11090111120a050d021b010504050c010c05190327 61
    0x42c11980b0360780005800794013144005502c65020b0035451461078014480f03210f001f43d40c104032910381170103489101c49a8030f00703484601d42030070030130a41c16101a40400220341480c018000c940c0c0158104414030b4540d21124940040c804e46512000c0f04d1500588240510368441c0760151010304c0d020074540c0d4049951b03201c00115071040706460f403007035446450b200d030703251034a010400a81000403040d20110b440004501045204000e25841080e102c03008030b4a60403843c9004046a6450366494141418a0f1828140e1070740d40d101a40c2c030850f50141e15480d184000320045282d483c3c041c95651082c500110f41010007801ca020340b2000d8400d0343c540810307000382d503051070b11071100340400300304080280000b882d051f008401400354002d99800040c1010781c42c1421007480e100c801e900d0311240c0d41d5003080c401400024170680c003a902003070030103000045d510740d50f9a40e5001c4510240c0c04c0184158100300825100318418400c0307003400c1780707681000c480034240a41d901040e48a11040c0d00c3c000d0b2016 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 203237410 1107 203236303 203236333
    0x6090809031b090c040e13080c1014090c090a020d0b1008041b0614091801030506090c1008011412060a0f05010f0b0304020d080409050c030603 63
    0x40702e82c20260603061208040e0081c040340c0458000300018480301088a180c0c50300030742c042c0c12045241e5000d0604918600841400d50384500440d1046050810150045030700a0305251600701d5036111810220395414001c0511904402c240000404d030a03840c0e8040c1c20315280780c000c046140181400080d6095414480ca030300842c01c41d205000c00d104c64980c0040d42840281480c460142c1080780240009030303040a1079590410000c0c4900380d80c3c842d114108142d80103011200815612031074403035250042280d450110388160425600306181170030b1400340060f029102d4004590a117898000c82000e01145150001000c00710300c984a901045142d00c51001010005911100079502c80c0a582d4117038004c0c413030313031005d51014081c8031040c1046a0700907504851488608001d4070b003550b16400340d80d120041041c5001d00700030102081e90011071055070100e013940c03e02401c202070 = true := by decide +kernel

theorem cover : BRFrame.Cov 203057553 203237410 := by
  have h0 := BRFrame.cov_init 203057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 203057553 ≤ n) (h2 : n < 203237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
