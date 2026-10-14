-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1240
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:56:08.356226+00:00
-- url     : https://prove2.me/submissions/7b145838-ed98-49a9-bff6-061b14e05382

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 222841726 ≤ n < 223021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 222842976 1250 222841726 222841753
    0xf0609071401030c0207030b093a0207030b06210d0c0302060901060b03041112060a051e010b031b040b1204020301060603141816030f020907020631020a08 68
    0x7805201a05040614058409021907408584101583d900040c0d40f9120388400c15031615040036103050036101004042401840050702d540342d0007aa00340701c00f8029022080e04140d0312403c0758803026050b162b5070f00c00902e151404081d00401000f00c41103807503a00042c1d182e80340c074001031032030454003280e4240b02c0c641c203054040040302d60000c9104028440c139800d00c2100c01c003e010140004180c441d030705041d41d001d613960b003404080801c1d040088550501d00340071003a0141c03005a036142d50140f03160001070300c001c01c0e590140b4145d0380c580d0000ca10310b487c4c1c084404500072014828024041003444042600100c641c0201024400240f000140303060900405084540ba68403100a06140c4059521610181c1442c0e90340013002148030007250440303035a0b15007880043d23551410020a0008040300304802240d00d504010b0094417420f10310742e2031a10581c0d4545080c1c504881c120b858501e408040100c0405507201d40d034040c01c00441c1d500440d401714501900980191070b0716042044002c0700c8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 222844226 1250 222842976 222842999
    0x51506060d06171614010c02060915030406050c0a0e240f0d051311010810051c050105330d06060b0306090c0405100f0c0c140f041a0906030f060907 65
    0xc400754804c0ca0401c2e1528401d0f1400c0082c82e18402d05100c84000000255542c8100760340383d1402c05403943c0300103a0404070f0480594800c40d41260060319080110300502c00390001e44501d458241c0381c0c1c6036020856000c015266805106110703c44900d00d0710301070b1400740c4001034019031102440c2503840304d20b00300b888005d8650041248510348108150030303002c50781030512100c501d04203081403500303901c880c902003081a6560f00010b0301b04c140110446285514601c03482a071a00030300c0204480d032510581640058006030703618440a841c142d84801e4170700054034202401100402018404581e40c4d15281550400d83c02084442008404c106143c18006045640008140c640714038090602c130006c0c1c0b01042c80002d03002000007100500a03035a00480d01c414055030003a028201d404d5035007016074034500012105a004640c051440102e50406000b0702414007880004101140b25407024000c5400c0018040380c0d241c0710b18074038061402002d000d66405822803401604120b0300f04050001c5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 222845476 1250 222844226 222844243
    0x20307030606020c060415200334060c02150a05040209060108040506043905040b040b1c0f14060105030c09070230040b07110402030103051506060d0617 67
    0x25908a2090300c445540e50b24100c071b060742c0b0019004100c204008404440c010102020042c210126a003071406e060f0303001001c1e00364015100050100a03024940c001107503207003491502400300840e41e11100280a0f07070808800c5013607d1040f5509003680301c1d103c800111054541d030000c1d035661018042542011490103520540a007000142810b0944da0b85503030317032070041c030203416559181305803032100031480410002c40107102c0341e524080b214410040003400b1107100e0b06229500c0c16070584594105401910311008000701040d48480704c0c0307501480032000400d4229245210449403e000411562100d030801c80c121006290b55030515003890311301000d05100c036101d41c00f10300420103266800225132401041c1c884d00284107000c040003449070320124191031507051801040100b01c90790403001070719005008114482e42403080c00240400ca02c0203000103010750708041103011040c074500502603004003010f07049600c1d11251001c0f620465000750404e00c04000ca01c056481c1c102c2c0c0030400041c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 222846726 1250 222845476 222845489
    0xb090f031c03230105090712060e0f0901200706020d020405040509030309010e01090f0f1505090102090f040c08040f080405030a150c020f0c1306090c0206061002010905030f07061e0203070306 84
    0x30760030350405c00016652800140410704106081801540182c0c85400c002c0040c82a042d0200c40c0b030810f003880012005080b507901d103280d840c0c061415556581458203080e2074003040c840b145041125101d9201070b5101800c81580c1c25000c000024058440f8491988109100300c041c503282d0800400d110301f50b40c400d0712036200680c141040b44021610660000b000241e200d03210804a03125807615450341e818007551010b000f4600010495a0141034008041a102c00c82c0c1180c0c1c0414210200000c45000f45081c10000d0180000140001c095034041210f041c010241d19007425618400645071800201d0115001d1900c0380c00700d0200065405010203c0c1c400b4005400c2038405941125941d814207004107218102c0c001c030103900030b011a4408009402d840308284180c4001c00800382d5a04400d498407409600d041c0b141d480503910622030014150340c402c000d54a40741e40400c641406c0d070000b600a5842541c0c505010608011805070f02d00d1891000c42d0141e00e0789001d5101400b00c59156010701c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 222847976 1250 222846726 222846791
    0x1903030210051b18030a050c01090605040f030809030a080409020904181101140904090f020a0803040308030a2d0518010902030618030909070c0c0b040b090f031c03 72
    0x101c09080244184003581010b9000e9403550464450001860f046180c8160140120346d444000d024020070103600303543d004c4e00d544000070f590b444100c1e060311961094141d01c6107200c80900000e442540180326440c0d0040031a100d801007519201c40d1540280c0c800c012190340091910780340c1c2418000d40f1080c10102e0f038100303203082d51390325405000102070035003a041190802c60202d80398035140580701080805841013080c44c407a0f140041400d101013074183e210700380b200400a500d500000454099039800703e003450443e250322000c00050300f4110514940b0300702e5400881c902c0e08801c807410900c0d00d81001d003c01c141c1005030f05540d402c40307255108041e590500800802584001411310303003000001c601c0e40541c0303c800a01c2404d6000e2110030617803181d28602805100c613840b0344060103007030089650a06c1c441d65140382c2e803000c0c881da200700304483c0c2003070115207100d01c1e14203600707018120082d05a410380040c0407890062510103229150103e81e0312100b20200112105150f91205160420b9 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 222849226 1250 222847976 222847981
    0x328020301120b0907170106180203040c17120a050315060421060b0301020703020616030b09060f040603051911030601050108180a05030d0e10091e050309190303021005 74
    0xb240450001100c2c058001036004001c1101c0e607408000700f40080104003100c0d031402254100350341c0645194842c40789410110445650365400c1ca108807401168400300036000c15150000c80070320384505c0c90501001d40a03099036860b6070260f0000a005148030f44e940d00741c1e00e151840050842c6900f00700c64038002d0b0010300c01802281c0c030b0240c06211340615078844848909551030100040c0c9004121560076500100b0150700309500011424010b881c000c00d181000c07034030400e048003243e08548825500c03e5040700850301a0400f4150404a0070000d00046852030703d07615171901e0009400d0318540c02c3c100c0c200115080c0414820715144915040f005800c29526041c0003c0001e10041d24180d0002c00340d0300140320888c4104209040664440b05503500d0314a5920420001c15241c0c40151040c0a60859407404145034861400095440f0f420701104042030009200c1d1010441001c4030248410003040080d0303503c43c440500030040c0b28440350f0404d419481c0003030a00d108444801e0b00079040105 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 222850476 1250 222849226 222849239
    0xc0415110318030a080f120a09050604020114090a3503030c130e04060b1f0f0806011205041110081012020103090605071107080307150207030309080328020301 70
    0x89402c892034001d501c00b460206000024100500040e0040541000103050740303078003e00c54060704031041c40c0710101946969a0040d00c05584460f035009000c5c0d04000d002800541c005c842e0400450f900c45030a504000050022a4407043e068205070040e1200419007034441001081c60414000750060003120400c1c004507803607403070001030000d4401100204140c0c3c201d80e801407900005000d842940708280c2441d08142008107007404501d8010710f13000d4101c0080040184000c4400314540d0f8134115000324041003282c07140390240500341000140a101c0718501c003580a460300590141108134124040382e0100100446101c1d9000d0510141508021610014030b40c05402c845142d00340d0524030a4510040f0010220000003d04040c544401d0040d600e500106500d84035010302d040f81d0035142c585100960b00e029070500201208040315a40542c111690003a0441603c6402c0208101030540e44010b215001150034001c41c1d001c940e810440c80c011394000521b240000403045103194100711 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 222851726 1250 222850476 222850483
    0xd0605120c0307030609050a0b0c2805180103060807090e0d020c0a03171b0307050c03030906090103020c03041a071101080114121501120215030f040b0a060e0c041511 73
    0x12000c5e04003941c1d10300342d4040c0f140c140455801a648240008503514162882c0c140f1f0f5006a03444541740c0e042108000b92410107841000f1150b0407079101c01e030405c10301d2000d07413541001468003a41003586079000094111820042c41e00500580e52011550200d406900da19021241b905982158031640e03201c03000713031501611101540c0e000500344440e8002041c5c40f021920408075140407200d5895205041c9920120203071031a10300c40d100341d07091070240004042c1c4c3c038041d6a05450780000c00304007580c01580246c4c01000404c1c94030040d41e00b07050f6541075800c030849440316811b2110070002075080400800b41071320b01440c032007402c1031130081d41011031415504480091041c06060b80302c1000140e800c0030001600f440010341040c07159581c50340c20030b082010582d08100d000d804d88004000050b03500c0402c0c0d91042c0e96500004c110340e0f176103880e605d45c034840c050101c423074259a8010124041c600160302611904041a00584e5a407070208510150045041040100015004810140007002c03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 222852976 1250 222851726 222851729
    0xd170105060f16050724020d120f060b04030c060801150c0f050f0d0f02070611030a030b06040902030c07150b0d110307050603090d02010b011e0807050f0d0605120c0307 74
    0x546003d0711842407141040300f840401401a1803440307551400070700c1d50140b800311010106007540702d5222406010090365a082c4000150010554042d00d0001069055100740c941780c62600b80480d85a07a00d038850480c1c2d0740f05800641b004501d02c4010702c041303508070040d039004100c0d0200728011501000e10003003140d406070b54010003230480a800601070100801c1021001c0c0044003e4850b480b44400010706130044903680ca8001d80210800003c00c18041c0840d014013200c0000911307c1c003454201e00f01d00a040240d032865122405000100b11030b28a440518418112a9403c659070580f60070719411007200020054140c80c2000c254011a40321710b0b0307003003135825440701c003140f032104020b00080e060488642005401400210811804080000d2008140101500200041d50b0303014011100c3e00c120010321242d03014192084580070307106010003503010388c0502e081d0b401c0003400c8168880f1944806440007031a40c907104180b26a28100c225242184680030052050b100d120b00401d8484a56 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 222854226 1250 222852976 222852997
    0xa06020f09130603060f020a02060c0d0912020a150c021e010b030a05010f05061206011a040902030a02130b03071413030209070203070c050307060804082a0d17010506 73
    0x114241020340e148000361110418028145091958031100050003031030644010780f845404c042c2060818601e61080f19070004250740501500e9440302a040d40340e500424004140e20340d034440300c002040f0700000e041020942c0b0b82c06403490815a082c0003c184540c1203134003504514104035541c0c025000690340c0f462141c2070519001c40108255024014120040f0fa0340c0c050080607210f074104141988007038600b0703170081c0080011351922024415030035002d404240782e030b5000500600810b1561310042c1405200743d400d051510351500c0c2e1131000c1e0303002503c10400403a0003052a81c0c009148880f80d40107041055569410362810200081c45410400308500035080006580006c4210880100c00a5900030300302110904202c24025900d50101c2c1040d10b071080c5124000c44c0519021580e0740032a080c07561908103648860300c0b035400710b03404600820018000448036500403036400c01d68400d0580c1c610041c1415107568003010b400a51481420716106035500c0051041d580d851055a40c00540c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 222855476 1250 222854226 222854231
    0x60f05042106090b1905011401170a090606120302062512180f12020703050a030e0117090d0e03030301150f0c0c03050606010908060412260a0e010c0c050a06 69
    0x10301c1c14030b00001c01c40004003401c6003d85608100010015142000700503100800800c1680e030b80f8084403410008201c0d020340000c05414510510805003040240c12251508000549003000d51b144011070700c0a034008030322504910040d009240c0c0600405500444100f102d1601e40700300c40d510a2040744c90f100c500c080c03044107001101e0300c41d40c1d03a0040802c0f01e50540944550081c4d42043e0640d00c41211003110b40795070740c01803c042244082080c90403a82d0082c010039000400f030b40c040d81c0c00d0105458440c10884042212840d900b042c00c60729000d02c0c19113002e082c60510414009010b01c1d660f18106011380c0c4100010170002d00401a00d030800c00b0f591a10007503000340060704580400c020b00010300110b2603000d020051020105407240240c6090701d8030880a40e6030403484d80c69080032140039010004120110f110300d40608401e01d48402ca0170716000d6000303c006502900c9420540302603484556440003000031080900c100d901d054040c0c245810400c6c6c06036130316544c03800e644070300030540358 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 222856726 1250 222855476 222855539
    0xe01020f0c091305031305150414040203190203070e0a06030605060d020a05040806090312011a0304020d02060c010f020714030324010c02130c03060b0f09060903030c03040f060f0504 80
    0x4081400d08000c1c0e4400140c90342c6d1082400404030750100750007841c0c4105400b104020500601c03900b128200d540440c10b50324448103100801000703410040143ca44000d09194800c400d40d081e10013144592100d844140d503a480010500c919030000743c00000c00d2601d8000248410766035801500c1c40312000c4900541e540e80a4002280e89004130303800780017544a550144244148040b002e011074401c85100700c90140c0c3d0754809011280c0e419074645400d414100003140c09800c0202d18200000e0015282c51314082d11601d440d030031a04000b5a81010720750200b2000c00300540d2840110700c40024000070b5085040c840c46104100c4e10949242c41584481d4071809026402281c00c0300049800a050000c80c2c00c200142202600059610a000030301e03100d800710340c0000c0041640e01c8039031211407603401c1400e07902c1130210aa021001496041c0300034001b10340c075404100f0003000034082621034003441c503280507005081e83c40b82080314005c1c442e06200500c0080081144909a0400b4541d060304c0300c0c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 222857976 1250 222856726 222856741
    0x4031a06090114190f080a0b0a0b13020c070b0307090315021e0c011e020c190309060302180603010b07020a09020f030f250e0a090e031603120204150e01020f0c09 71
    0x1413000c0d4800305820450345000104003c0c0410700740341e018001e4202c00c07010303607490007014110781020789903070b40c818912004080e58413a25409407641c114400300f01c4585540b03a180c0c80348107420485d510000205204001d001300070890041080c102e200b000709500f45002c16000c20bd09a0542e8200c81c003a370300100310b098186409400490320309154440c5805000300b1000100b001c0d601c400c40e0b100e0144214480000c60044243c4100d52072a01552010344403030809408034041e40c080340c84d0038240a142d5a41000c7c0e0381e41d5000850007040c4141142c1c2ea522280d10610000000f01d41c030412480f4414021090460300c18002c82e9440745041c9104042540ca04e01c50840a00c00116641d010310b5500c0c0350080780640141c524014400215100c4110b140e03148840020344203503412050323007508140310b40c1800788200300c0900382c0c103842403d0402050f03104840a1b4100d0b04181d0040031104410811005015041444204001d10a20183c110440110469a07681d545d12000d42d001d18413280008004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 222859226 1250 222857976 222858019
    0x1020106122d0609020a0815040b0c0c0f010605010305011505040311011101050f04030e030c03031c0209060f03010603060609140f01140a0305040507121505060607020604031a06090114 81
    0x14207560908101000d00b50908030b00a15000100720301848014130003040d4130100188888400480100a003840d039140c0e5a01108110040d210380700b00f41c41800300384034104050003020407101d01c2d0b500001e101d0f46850001420b5460692000e07810150b5041c4034034440d50f001301258144c0707411248844c42d8062480048555048055410105500e0001401142d100901e4164003403400703540c40703080e600015004c05031035400c0082559410707801008000044000300c018802d4804c1a0b010060038941c40c2404550540d00c80c0b185103442500000c0107011454141c402c05010380070b0707481d000e9802800e140c07105050340c1c40c1d200358610800c180c032204c0040d82e20a03083d00320740b464480580d42d260404141c015000e80310030b4404a6460040020114980d0790702c00300038814a4206c00c00504501c0107007601c1c40107107005047d094005c2c0e01004080c016031282001000203611a844c946e0000501e404a840c01d104094600c500c1a646c860042290b071443c080b00244d100002c441e1001c0c41c508105000e500c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 222860476 1250 222859226 222859283
    0xa0609060e070b120a06150516060212100e010513051806091612020a060302070521040f080c010c02091f0b040905100b0d18020312032502061602010207050f06150102010612 76
    0xb40c0d000091041d540f107400300030140980074810304000c8dd291500074100ca000400d02a66810052154610459207a55001907404c05509480115065548049142407440841c0d4040300b40c1d12640520700e169411501c0c0f40000c14009901014000d82d031346c0010340c001d0f064400c1400701900843c1c04c1d002c0c440184403c5002d0f40480e010236440c4000800d070364100d901b051003002c01d4821070f4140000c40313100205000e04250b4059490041c0161507600308140024081e02d540c00083e805440c1c080540e50010076003003d07044991800740c0b41e1745829212025108010b0182561405130841080046075003001e40b80c8280c0302c0d04e00407801302100398030402154804080603603d48503c44030081c4820644004501030540001981c4074401143c14103128840340280001c0140c1c400d400241d10401c05a00030101215107100140c0780c0b844544440e0310701180440201d1035500403c091002040c407480c40b1138803540d800e00003400100d1800c2112403000c081180d01a140d104680341448007070400b03004c1240c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 222861726 1250 222860476 222860483
    0x60608040c2427030c0501022e020f0706150311010c030c0b0c13030804060906090803040303030225201002060a02030402030106170c0f0d050a0609060e070b120a06150516 75
    0x8440c0c0e6035034205120416a20706c1402d003d4010345a003540c140d20b100b00c480031210100f070b4502c10604060380d10038009520603102c0721311040060003a0000103619000c2c0c0cc02c151044600380310700c113041d800d250f5100f6510000c01810710031140c5524001a4122501100d01c5801401074510380e81d0744106001c0c94403413640f81d069400c000300004020480103802800030b50b856980d54541445d00d0318400d8503005440e008582e0319a0040c0300c1040000d00c65001455503400c801071b0a40054102076814400324071130203040f54011550243c4464410700b04076080c0d410842110702081c00c030051140651120300c050a810b030b803190000005025500c094114000421420a051403000c0c070361040503844200120b11a0700c900818040c0e4030742c1d0b190031010241c080d600540501400c4c4415038904004041030001214100d49480e02c10f00303e40f00901c00000244040107c040e960880b00c10001400304c03004004500d510f18107042030000c1c0e0f0810b414400c3c00816820180da40d24aa0317801c10043c456081c6005 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 222862976 1250 222861726 222861797
    0x60e0a0503070c050103060518060d0206040308071401110a1107030c06020607082505090d02100c15050921040906090222030b0622060608040c24 64
    0x84080020000081038900e0090800c0341c001500c542c0110140c40c454450664440702228a00300c810080800b620f030464002800c0d007840c0c0c2950740c08038125410651003a1150800803e0311400d200384464403c84100d1284001c025040c89110301030410301404182208020304c10300014411038080103c1405503801c44012a030a0f03544000007940c8150807900c00000035200301c08203642d00f04000691781c5054001c403200c41491075025046556410841145030311425a460310360141e00c84024411412016036141803258109007002c400c0be210042c0b8030300381c1030710709400c1014000700401c200032400100303156480c580312018640045c9020b181c21104900303103003007000210a2615402408103400800c0f5031240080c0248228040800e144030142c40204040000390f110720b03100c90b55144600ca400401d81400312910840c8044071065002440860720281c140418003800c90891402041c10741c4407201c408448100d0003410544500302c82c000e202d8600c90804011500c441012084125a001c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 222864226 1250 222862976 222862993
    0x30815130e010c20120a021c020102030912030903070204110d05090703021503070206070f0302070f080a080c070809011b0605150406140109050613030b0a05040c0e04110904060e 78
    0x242c000d040891880307020404030740300d004440213140780102c1041c40c00c00190072000c4d40340ba4258019400310030450118000c40208081c180a9020122800f0301c1d144d00040c0c0b81c1c40d15210031494031062403440b1100d400c1c08d004005116a00100303c8400980c1607502180a08080c1c500f9209806020188032410703082804012800c90006039031021a402224001d03081990184120894807043c0c882c003005811a00009000b64007550b80070030005510f2800616000482d101c030341d080c207006041142c81000004955500c0c0340c1c0a003100350810002584a40ba0036499a02c8128500c11510b000c5c2c1070000e644403e00d850450410030030710041d003122041c0040d19000d06500e00c449030490702280308510b01366002c0b40751000000c45030f0407000c040e1990720140e03050070100240c9400c0001c2c002024500e014000c00011500910f00f40030700c1c044540031440b81001d191100a601e4079411550051104c1c40070000400c0b0721401c55030100d0f005961507a2a45ca443c04c0c50005171111816803141403081e10032 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 222865476 1250 222864226 222864251
    0x30203090909060a0501051507030c02011107031b0503030c0d0e010e0409050c01031a1503040c0f06120b0301090b01090e070306240f03020108040803090f0d09031203050403081513 79
    0x2803d80c4134641d002400c200c81c4e81c81310308001400a644440004c0700d10103005010002c0c1c006d03290641258014140081102000324034a45488901d0b04129034440d410000d9149807140402804081c00b012001f4600380200904040e42c0d0720310700c03031210301003101107450018035900641c50301c2c00b46000a40300340642096800d20550700c410315402c81d800a40f03006038510301305c4600341d025402c4600042440b2141c4003280c200101a41014005480084543c407000a040000301c07000002059640c5443c3d902c0c4403d03000500440b00d5801ca22400f03641007107540750000d0600c089040c1980c000600000e556480035148900c2c1c44200c1d04000c0c14545010340c2c5408c00e0201101c01c60400c039640d0b490f98401e13601d440d400805105541320003030100301800d0100740040d04640c0510f0f4130401e108101c6042d80c034040342c0646020841211300e000f08074801020701c00d00c030304040e200140d400c40d410103100c075040c45c0d50b000700315680c01400b0201c5600d01280d010b4007a501e2040101c80703185050b0b410300050b54450f4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 222866726 1250 222865476 222865483
    0x1091b060f120b040204240810051203090d29010312030e1e03042912070224040b0a0203070804080d0e0303100f0608010b0a030b040e060709140102070f050d030203090909 75
    0x40000a421f03020b640c0c25664800d80515114291030f003080341005241030140001c8006900048009000a00400c4060b031640c0d148503240e80e000d403040b02e081e83c0c4082c6c1c0c1a04070072850740e101404075000d940140041001a1a803590b00b020518001a80c0c60009100c10700f02424008480031940e00d001c1d11503e000c0002025200784d5080d84444800c42081d0741c3c5840e441c0ea0075080b92140410244106520010300d90541c5601603000c0c01551001e840d085002118044c0050440059413001c2c001c0c4014441c0740000382e54082070b610070441c81c5040050001d49205c800400041503907000180b6081c01c280c180d00800c83e5150358400301c0303481c3c0c24460700c110b0301e052150046824204a405000901e21301c600d47c068100c600403940985401c403a08421000b510a058455805c42c0d2a82000c58145904100b014850001d03580d560b4032302c50401015501c2112020130f074604540c49070505014240915100b002160800c03160082011004d2505909500540189940c811710b031004221b81c0e200c1c0403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 222867976 1250 222866726 222866759
    0x60906060f1216080c1903020f04020c0307080a020d050403031e0201060b04082802011d06071203050a0b0a0515031806090a0b0105010302040e0402040207022101091b060f120b040204 80
    0x40c4c043d99441d00006040c002c0d11418150181c40c40250144104054100520700c40040007014102524200310b02e00703464035551001000b210344242c001400718545c0d6040c403070f070310000815281861600d4615100100610702c2629441200a03182c03c11a00b00c6000b580114024070704040c51035125569001031984031780b441d001240c0d030b1900d80200c0400c3c03002e600039141050b903030507103030800410700303403001e06165982e0b9140c1241c0003802042003501180001301d90101a0391590782c081904d01e0000e01100540744000032460185000d072005210680c2c522111014070450201e0507902c07036517050000300d40c005000e0400c000f5030103500203103c203440c8082100c4503c3d174041c04000c0701700c0e66074a0044041f40b04902c1030201c500407007004140149000d4008240d5280002c0159103400b40b00f2000f141c071446456a41442c680d03440c0032400c10030081189180070302e031805440d58052442c0c0300d0003030824100a60500100b1400d242400400205640080d83d040f074081c02c2151200d486025645c1044002c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 222869226 1250 222867976 222867989
    0x15040c0e0f060a20013c0606090515160521030108031b0c030d030516020604050613050a0c120605010b3f0f010512060906060f1216 58
    0x34a040c070300ca9051140440700c0c80400755459100e4021290310510507480001e0000300c039952225408440c0740d244c0880e0141070103030304a03400c401da5803401e000345a840c0510312031001542000d500b0025250013205c00404c46100b980c0403042e2041c2450001c4c0c00340314402c2c1002440300301c2d0801f1000d01c81f00281c45801000c1c0d072002100c0400c460305004030b090200b4846c00b0301c00c0d402041040d0704807081d500e0816990b40100c1c121001c01411000090030038a00c81c032580000381d681e008101c80c1602440e040345040c003486c00513000904080d19210713180c02d40281500040b03040320b1681310801204010302e640c81500810000361490300c401744c040143c5000c1a054603d90700b4180041107400000044641002c401551160f80041d081c180c1e01c0ca10768419405000d4a2001090800071217074061064401c030b0007000f590031b180d070422040002e002c2c802101c0c0c640c0c1d0740c8000c00300920000b0000e1140d40012040351940054600301d0002590311285146082c102e0107a03c070f41e08070300e94041ca0100c4c1911760703 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 222870476 1250 222869226 222869239
    0x1203030403110a0b060f121e0c0103091e05150405060627040b070201020f0c0c0a15050f0306040b0d0f020306070f090303050d0204030501060308130b13090515040c0e 73
    0xb0100c446a4601c2030030009000442c001c008245680350505504240f003801600300f1a07503a203000d031500c7c01c2110403100f5070300740362020880e241080c43c1840300042008090800704144201920750340d01000d844070690518611140040d41800420825106441c0f00000000a14581460056102e607016941c0c0b60051042c0c91000c08008030111120580d00c0780c10b4080041a511070300c0f034030115100034100e801503540c200007055400e010307100201020800e550042550541e00c400f84014440c40f507220714085080c01c2070750a00b81d60701030304403038070000d1f1000044d4580c0c0302d01001074024403a03014141ea10000821841c405c00c0f0020081e010381600032425100c0c0303652000c2054506986501d8000c0c0000c813100320500c00640903c01a0840e8800544014145501ca58031242110043d4005030350307c240100b42c1c1024980a00220805400060b1501d804c00520b03034100d0344e0541d941d0081a402c5a1520000f0380742e905070304001030586100400902c481a6004405404d842c000d6081c0c500941 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 222871726 1250 222870476 222870497
    0x1009050103050a1a130602030402180c04030c090b010905010f020102090904151b05220f030b0f0115050706090618060b03240106030c1e020304090e1b01120b1203030403 74
    0x113030342c4100d10400345041c0034000d9040303c1e91008025030005104036030180c1620040407e401c1580e00c081c0c4601c02c0c001505940d541103003800640b100d5a46d002030f03c0c0c14280a0004501e90b0b1149501d401c50b1420f0030584c0900320141020fa002e4001c010030380c0e4002c80490b0400c02488007013051650450b81100e401c000044800500d0002c0f10110154040890402c00101d0786420980704607655420b0161462400c40b0b4a85580c038507041c04950050b94210000c1042c880c6912480c01d03990700501d0446e01d00d1812511048000c1c1c09400342d0007001d00f080b903450160000388005074000e0002c8162840704003000d054145000c0c001441c4420f0921300070700c2140203150002008900d206050030307843c5503040035030386004002ca02038140014081c00300003001c1c8804800945541007034843c050903070080c0d51a681410901800c4035401203000199501c11300044c0d00700544070300340c0041d10320b00f860030544070b80d40428080080c0090203103281d040100d1000540c10500e010000d940120b100b5680c0040c0071 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 222872976 1250 222871726 222871763
    0x501300320062401110c12070e13050c241b010914060c0405090f0a0e030a030203040203012007061d0f030d050c03010b040902071113050f0601020f0309091009050103050a 75
    0x4030001021207031b0126568a0b07843c40d00c00e10b50984411355070222403d0a407124040b280030002078a07000103088512601404205051060560000090301d0001c4a03203800c0c0b10041c0b480c0705024803c0d01c080c4000401059070002c02030304494440010000384440c207400c3c030340030f000600c0b00d18910f0030602810380401c01e9404c04104075411200b00810228581c0c9a610715881040c0001c1d10a0441d15550324011088000500c060004503419440042c2c9030303d002d00616003501e42249452200c00424103400c0b0498911500391340e20940c00150001d00b28005250080a10b0b0f000c224040c250720405540b4003003204c000000b440d03540202c0d0b20500ca241c86070103881010740000c0c040e4a03407650040c0000e0041c0c0400d41c1c0030b040b01c28020524100c540b550280803a042100160580780c1079a1140c0400c1030300ca0354050040e42000b428401081c082001d007401644074080e0442c0303140700300343d40400700c0c0316901103c0400c00602500501081156541e01c6e025946203a004421a000c14803d4440c0e03415 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 222874226 1250 222872976 222872987
    0x1806060406030915051e1803091306030605010f1406072102010e030d090c0b0304021f0203040504090b0108010b12100b01020f0709060e0106050901020601090b0d0c03060501300320062401 82
    0x40c11f596100850a0113034400800c030050610400106990342e036080d0000101c3d4890007568001d01d044102c400a440c28a09868440c0001340d0007980103d0b020003208001036030a004540c002c0c010941d0780605800108012800341288151340d0b541440003164081c000b880952090321020312410b235501086070f0341c4003603d0550000301c2b40a5404903854004106d00c035820805050b40401c01c0c0b060303e18064403900024211030340c80070309071078031103c01005020b100c20920030800440070488040e080104450041940e80c000c00c0c00001c031158a9159070402d40c1d00801c5100b0000300b0340c81c1618662602c48902c04d004102c54416542440c1c0c0e00c3c1c00005900b80118221000e0755410fa0190440e40c1c00e01e81503002402400c3c11a5070440ca95603482c90100380491a00e0000d07504c01c00c00800c640d450710900125161292041c031204003814251624003240b440010255140e040c01d05c01800c42e5121051840100600b00110a9001d100100f1411440603041c0c840341c02012250301c0d20000300f01e00116007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 222875476 1250 222874226 222874261
    0x180c09011b02211501060f0f021f0e01060801020f12010b0309030403110a0314011b03021303020d0203120a08100f061b080405030307050c1806060406030915051e 71
    0x402400b030001210f800c41c16040c0080c903012110044440041d4441c5280400c41001da00c1400040e032448010f000d4143d01480e0380026118610003001d40441071541c8145540d034042e03500c1c60156a1b13004041c0341c4182034115100901a48008544805246040782e2050703004c6802008620307084400854500d01e40c5c0166405941140019800c19003566034500900f1801c00c0001e90141d020707140000010712038548241161012000429000c0c031607980f5008002c1e0b44030100c400c0c0360040c4a4000c1001c01010074604407030301120b0132030b5101001c0c0013007802c0611222444142e03a07800074900039019001081180203003880500f07202600d0780c1e580d2107181035415009000000301d80c1c010f062900507401c0e00352031429016860007840c10780d8580010380b6540c82881c0c02c84568000004c082c0a034900b80781c807400300c0300001c0c0c00c00384103140c800001a0316103c0c0f8051541403540d10680d8000340030313202080c01c2d404905072101300000e00304000088aa240008403080318800c40c003000600c480c600041210 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 222876726 1250 222875476 222875479
    0x305040812090c0d1506080304050d0b0402040609090c0608070c0309140f090a060503010e0a02061912020a0c05060604090c05010c260a0f05070302030d050402180c09011b02 76
    0x242080c0141003600840300002d070107250540700b1900304900e15561034035001c105a00c204580f00ca641d02c10050344c001e0307800c3c0d0343c00300280d60010b10040000da2110840c1503451a40240c5405850b40c41d8400a0024006a000042ca4600e4001d00701d040140c0c0350418810350b412034544005070f548000c0102c0d00080b85520040000348000b4081200c05041303580f02c3c1286100900583d00b2602a40c0494045401144c0e95001c140d194802003007582800c4c0300d0009030b45503010241c91200010740114200344585140089442d14005a08003003a01c03030b04480c1180c150501c2c2c10f541d01c0845003001400d106949205680d10b0080a000c601036160a10403030303803281d40c03005260800510300001900d4580c0d24a8080d1450a50400260344581011404490803510300104945981122000402080c955002c0304240b01041001c4401300c0d0b000801d07500100302c0000003003502c3d0740e0f034030220742001040203c45e01814141c2060008041d140c002600780140203a0741d41c0131821040f00600340446207040e019 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 222877976 1250 222876726 222876743
    0xe0315071b030e03120d0b030a051203070c14060708070c0f02060d271704030302060a0f02040315060302040e03160623070c02010915080a0b032515030504 68
    0xa40519850303100c41080318040d0802e0402c4450442c01301382440807070f44008031460f600281c103c4e00e0444a00c5000c01c0034206070000c0010b5803060341c0b0300b0f543c0c40d40e503540e690144a0100004510307900c00c1400c82c0807503078051121a13054100344c4c8590b541d424142e81a5002c60381c1100002d5295100c0c558001d602500721014034a0644281c0a11590354401c0c0c0345440116201d44012045041d035008480c15690b5070f040542e5041c20900301031080554810000000c2c1508010800109600241050700000303841e80c0002e8100c040c180460080c480d6600040c031000281c440354501f005d9035840601124000d54080c03082d00080f204030343d16403180c0c40d60300d49506280c850300c00c0410807a501c00a11903da080000c0c40f450340d80300c022111044220740d40d00010703000318801030465910111000040c803841102c50312540c800400a0601340d0b00400d42d001640d56869a40f15964040000030f0107110a400c450301520105011a01b8800e02030040216041e0f644880600892217403103505d1040d40c010094 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 222879226 1250 222877976 222877997
    0x50402100309020f1503060306060301020f1e07060e010e07080c011d04020d15180b0904020d171804140c0403020607151404060b0103060602060a020706060b0304030e031507 76
    0x75402403011000c1a608000d00c2500802d40d51078209219a485680045a980383c0c0b51210815181400c01402e2074026401400f80d902082e118070161075540440039900303021400c504403014814019950003405003420150080c13100b85040d07022400c215060741c25112120380399591981d07601030102100307002501e8140f400d0034203d040c09003040c0807940100050324201c2c84104500554411964091210203603031010004026005881800d078100ca003410700900c941c280004140403170060021b0300a00a801800e020411a050f40e00400301c102981d080c0c54490030051220208001c1100d0341c000e9144c000e01c40b1054242e54042807140c02030b85c060a240c14116428001e0760740200703078120340d1107007100b0320480c000d030490040300d40002c00301c0c2081d8000d2a0a007005416914a00d91460602d89000824072500d0750100b4035603032100c0612400361703a84507d40b40c12001030890b580607a00d00680401403000305a44408509030540d0120708941c01d8803100e000c0b011003102c0c00c2c0c03040703c00f14900304c80 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 222880476 1250 222879226 222879259
    0xf0c052806050d0b06070b0603060708041a07050c3018040908040b031608060f010e0108060f0a1502070b030f13030e03010f05100605040b0d18120c05060604050402 72
    0x8140f21408001e01007003580741138010512a03017180c2c00444101040740104291030a08010284c0d00c50058500329085041944498490a0f5106940742140704042c00040790f482c0100110782c000c01d80c00381110301108141801542c00710111100e8103103000c030300c041012144081425203103000300c0412500d821505010820004206e035100840380203005210000d4901d0313100000c4c501c62081d01e0702111419003128402400520010702c10341c496510110004841c1e40d200d80c01c1c00c2c4010080c20407082c10707100d60000170f00b400000040154800490780c4085807844c025072142c1c6020096400f00c400c050b4460f883c0600c2400100c0d002403c20201c400010340b0003e009082c07103162402402d00310314208000c03003c6400d40c0c020507618802c441e01c540500c00030030070b040c041c0340080c85d0500c4c5c00c504003414a6500d4145d80b040c000100629074031507840c4d0746900340c4013400000043d40320401585800da028000f406001c1324600c103135014020302c0002085814180182e0f44116801461a04601055003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 222881726 1250 222880476 222880487
    0x7112107140f191e0305030d11040911120601020703200604090204080a020f01030605030309012d110105070804020d060e0111130e01090b06071502070f0c052806 71
    0xa000a03880031641c86000d0003600c2d40418054802c0704902070035182070a00300300940300003010103400a510b144d42c50410218501200ba144200007050003c50100340205500c100b40c001c40e0440354803186844044603060b001540108803000c1e000c82040790607580c0300016a2200e07181d10024118841c02441000c0707855509001350b000400c0100b005003429192000344049801642084a155000d5407015003546003800760b10308000004d19041c05403604101c0407945900074441000c0c180000041180c0e000440001c040e60700c145c0f86000e4a814903160300000740074507040302600020794078120204012038400c40c580d61040760054039000b0084c004d91340381d000510388030450840d55507950294030100483c620050101c18480e15410864901340000000c1071941a440901303113a01e00040a5225101c00d020707140c1554100e074940c404c140740d03449644042c0c41004401003003018069103d004229804460302c0649409a404080e10908464040101190383c601a00188401c0e503040101a00c00e8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 222882976 1250 222881726 222881759
    0x1d0c03010b0c0a06090c0e06040c0e0409050102090405040b07110c2101140f10090b2404031e0b010509060d06052205011b05340807112107 61
    0x400f1224021000d464020846103030316021035203051200e00070404034020401c21a00000112810070404400f90302c00342018950361500c50082e502c52140c00f00344042903060b2659044050000d0141e86880d14203580c21a41c1110480302040580c006001600d5000481451910b030181c02408080203106282440c400440b142052540d00d8040e10001c02a8030a070850049040000e20f41031400c1c0b018008200750000c1d000038071010301d400d002130150f03a2250b0780c4c3c2c1d103261540e03403008119821070a00d6810310700c0f8940002d82602c10010a10440300c0321405a009124001c500c81c0c8940d980b01c00030082e1422064504030b0b40440140ca100c40894043d40c40240c010341003048418003e002d100700303003d0700d0701114001d441c641d41d5909075400c1e50200885072468041b240c41c0c40c5282503040091240c01101314aa03100a010801100341d840d01c00c2c01d03480b109403941080c6680d07150100c600c1c01981c5460442100b1b400f45004d202080c261507042a207c0c124842c1c0f40c800340595a0606149200490b0f03031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 222884226 1250 222882976 222882997
    0x1030f0c0b0c1e0c01020a11030f1b03010c0c03050702040f021c021b0613080d0f091209062f030904050f1e0c0703050a20071d0c03010b 60
    0x2451001032080d081d01c00404600c05040c01a10940f42e5000020303000b800f9400c48042d01c2c0c3c10401015105030381c0450400c0d80d1580c0040030107400d1584501180ca0100d0301c0d155520b5510900f42440071600424450700c8408000710300030700c0002d00c603170001c5424114404009010803010f02c000001441d140e048016103540010006003007038603450040e03070000b1500940340d881641c0010b04044450460010741d2501101c0340062070f0038100f10845601081200c3c501802168011820004080c407d82003200380381d00e401c409011900c402e080004d5a500c0d500c03196804a442e02c072001518500601c503410128440361210300d0154444400e8078030320b0803240c0c2c4030900f500041124210302d948500c01c088c014034001c400d2505a1401e5150442043c0307560301c000005550390000c112440c071400b81120900c0768540b5142e516071003c944141c1d050100a15406081e01082141e200b5a542c00140401200d444619000a00761000160410054140c6289004070380820040c001020000010004136a0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 222885476 1250 222884226 222884243
    0xc0901020f031617030103030203160f051c030c0f08010620010c0804120c0f020f0301090b16090f05150a20010507110309030705040507020c031509070f0e01030f 71
    0x1000150076056030b000488540007000303d0f826510900c0710440d50341e1214214a08000c0c50b650440e02d0195407170084510810300740c61040704040800010100e402d40059201c4225100810020070000c81100000700e100c0000e0310700041c10720f05a210341402d90142e17580d915680b00a07401d1602c100ea40c11030401803004104032068104010500911444030030b0305207543c0b4140d03181001e02c0c10040d8604009903030410030640b502190041401314100345801039044441030204400000401d0152010072005021000c42c2010464541038804c5814960803041d070b2140350b0a0b4981034601004a01c03809416044030380404144032100441c030084c1075101d0703c0c0c01d0215241050005a20b490107410b6201065a5100c10903c41001d8002da04c01000c0c82d01c035806982440b5418003c60740d137909611400f03103d80c0e02d030300100310002e009100490680b00d01030b040e0354141d80070444180030602c007035a401c82584121540001c015949000c1a03041d50070b105500c4502c0c0c1d10b103440b82180d560552605071280c80 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 222886726 1250 222885476 222885493
    0x10c03110a050708010c091502070e040c1508060906030f0c0904050111040618060309020607300314090f0d05030c2b0501090204080309010815040606081902040e0c090102 75
    0x10b0b000c0006000801c0700c80c00110302501d80150040a04440e58842203418003e20545004990041000c10a45400300300b4590b00359602d0404601d8102d03181d10640340e0390461540714032b20740c0d4000f0040d44901c03000c0d14200050703107684e0709140c0c0d03545a841810f01c0f59003000c0710070107a501e06500c55541041c0224000b00e0f6240b44141052000da220703500120100d0481c1d40555815942201000d0040c242410100400e103040d0b004210b19108110004010030301c103920003198443d01c0020003d5a400a070004400320094103000740060403102480c02e108031824000400c040300003d000c20344a26030401a110240c510042903810350030107080c2c0d2140803010301050341880c05041c4811000d0102c08082c14500e503101210408036032040e0040100540100024000541c2c00011966540c1080c079051a2581e40c600b106088940f0700001564400d062100010340264040d04590080800180d0f16a40324200c0e84108201d01c04c1c0c0c4102e80051b81d0290000342040100c202504102e14103006488000c1e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 222887976 1250 222886726 222886733
    0x1804020904050c070c062d09032301060e060102030712090b2701032d15090b030f010218120f0106032006130302040513050a030509040506040b010c03110a 68
    0x8036000c48a0038503121021a130303102030001e07550580d0010034050814100c40c021041c0c01000003251a205034407003204544d000ba2043e4810024070000316002014003071400c00400700750007000c00f07580030501d4642c20080c011408402913a082d50040205030021881c115141daa06081c4e24200114001401084000021f00c08a0381c2e0080410381100b04e42e40044902c440c8903a5074540b032420035607042510744010301000130740c0b0241034044800c0d42c007407861b0440c2e046803a400c003501c4907801e04130b1100015072001881008640218040050880507104003480c041041403c070701031040980b07840350701c014441d2502e04028800d009031204003001d88010001100e8450300b51800f6502c00c0300c0301c09420b4400b003100c681024568420020456046141c51200326800310390001601000e44510b81d184046140c2d1004600380000c0704d540841a614051498240030f0650742111468a01803070506000a180b841d1034421f65001500584643c030060b182c0c1c0d2401c40c0e20784204000c2141501c01e00c41d085011 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 222889226 1250 222887976 222887981
    0x15020301080607120c0c0311120d0b1c08070b0c0d021303020f0607081b0f070f090c0c200105090a12120201060e071404030b010b0d0e0c01051804020904 67
    0x20700040d50042516040041c001419804107603002640c42c2d1a04099011040d44102150b0b4100e03090b24042010340d100e5820b0f54207100c0082c200400d6006d00180400700c216583d002003a00c1c080843c0d40c00704507000b90220070190b04440c40d0061003c0c2e002c00005000641500304c03d134015445424060421b0701c1e07507165008a0b0301ca404d04055881c1c000782c0c20000c5142a01e140c680c81c0d0710030b8884030b080416594441c280782c01004468142d05201e4402408146010400d100050000008a0340041e82d200e4551050f54800d002d0322400f41d0400c0402ca0003503004030a40060316900040c42200c80c084010700f4a402541c81041c14104601000042c002d41d0340c0c0301020001d0b082030403648482900b585482800d10032501d80c01e40542e41010070412078001511105540881c0d2070a0540000d01018891807061085030402880c0200310000800d103141d0072005071480d241214401c01020b5111004c05030b94448071514540000c4041201661401321040e20b040303c41d10260000d420148100300003402d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 222890476 1250 222889226 222889229
    0x8060a020c280c09020423040902100f080f0c1204020a0522180809091302040c030501292a0703050a120e0a030b09100e1006170607080415020301 64
    0x1d42c8081d0310702e003802e014100740c54400410603803e04500c1c05140ca0407841500540600c02c03855101d244144404a448a42000910310740c0144030a5400540c44400b41900c907145107144000388060000a426103610340502c1c0c001c101d02e1003101c0c1422170768902c4417030b4800018030072600b100222078001381584500d0784006003400c0c041c1e01e0380d01048407841c012045580b0741040110080304d104588001c66000c204440484006550542c00e5580e1030220071b9031b620100300001d410514001d626401c0e04c0e85607100a043e503940e41148000b1419581d0015441d0141041c0034503031000400040718464025403031005102c0340c519850040e0842000704a0078240c0b194000d6441e81c102200e180d0800001c0402884c0340f2009080111020b074940e00821604001408001e049000260104962031810000c0d4810700c0440d132002d00c035000901c4a070b15110b08420f042d1041381803e000010445c003288080484841c600f001c01065503030350380e6104039a1450003030403d5840707e040300c0402c068003030180021030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 222891726 1250 222890476 222890533
    0xa020a051b0d0f03021303060507021504060f050106170a0f060f0b090a0b0316081e04050706120c0813020d0209010f0e0a0603050a030c1b030309030b0108030408060a020c 75
    0x21101c2c0400606051411001d2400705441000382c0803041600704080300c01d41c2d402c20400036569030303404401c1c3e1034140c83e4182ca10503485150100310401c081508001480e240e070280600c443e07640d80d0001e40e0180601060704000880600020303010083c582d024042c0c26045440100345165200014002000039030800e01a0a20000d0348020a0808094480c02010289056851854002000f000600344c030f0740e04204222140c408228001100c05120891715101480d03461036080030f1a04503035a1070544601e50120f018003c02101000441c8224550070b12940c469200c9075071036205122110603200f50882c0d000f5014018840542c1b81c00310814060413184940700401d0317007010348505000c4802452103c41c030b400c06409000290340460945c10f02070f45800c00c403801c4238031881c1c0320481d01102c1c00310568070003000c8070010500da80104940200c0f0b004018080182e603c1d10000340d101c0c03080c4c0c0506c040b15807010000c0760803003065034000d0040300c00180075030324014128540480e20180d400c0c0c450 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 222892976 1250 222891726 222891733
    0x31f05010f05010903021503060a030b0f0a0e03160b18010606050c06060f1f090e0a0c110f06220c120302010b1e01050c0c0303030c070b010603090302060a020a051b 72
    0x1070184080c0110440d010704000d0804075101444c0d603000078800c00301518190101d220100206105403240c0c4000b00142d54480d01c8000a440c100045100486d0101e407250505414800800c410501c00703c1120407100304a0410300326544035860f14001d881000d400103408180d2800080c005107000e1144001901c5581c2c2c41c0c03680c03011442c0e0168038111014090707501c10400030b0801d1601d50747e0700c014600c5940031210702819004070b01c039007076551507216444801022000307410030403a50240d9000c84d0394003907039440303100ca2081c03d20142540c44203040e00d00398551b03005401154410320303000d02e042c0c040c2d0074030040e2841540c8a6900c001d022913607070380704030101d812851190041503020f00515001240c26510b00d01412080c00084850043c0c11001c0b50610a000428004860041c40515032030760020301202c0e541d04008100019640c00000240c50004264001068040c1f00f030184a2506030150f000b001c0c152644140030340254040f103e52820300c40d0402130514010701d005903684036040051b014 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 222894226 1250 222892976 222892979
    0xa091e0303020d0f0c03030b0102100c0509032404020d14030406021609021c050903070203060f0406051803030f060d0b13121b120c050303040c080c01030c0c060506031f0501 76
    0x40d1801c0f090f031a0740e9051005082003502119401400321140d507816107030102d003105200f4010b0b0304040c4402d00c0d85102034144041c043d0159042402440381403130a50031142a20000711000120104644641280c1c1c1404c00c0401d025182c0760080003502d5008841c441180116412268a10780c8940e000d90b0158100201200c1c002032291300350002015150419850420203000d41c480003030320302800a60305039440d40030520444040056604841c6e000d002c40b080340c10075030440b40c066002102c04903489810701c0c0008192400d03c80d0f00e02d40e080c194070015410354441d0001a4410301009040070741100c06c12040300041888400161b000fa0106c0205000f80040ca040400070420304100040900404a407800701c0002003080031030000350032640c4030502e22a9400100d1741e10901a401500c60302c07012040c00103205588803a1011100780d103080340c44801211006400f9241800c902c0400700f00e895520402050311500480d9000700020140c94800c210030740182c9075400076100c1c1284c140e603034000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 222895476 1250 222894226 222894233
    0x9020429160b040b07050903030307030c0927060902070213050a0b151c05220212120a020c0306011d0a0902092805040b041b0b18041802150a091e03 65
    0xc0890308181180f5241f860a403030b00010a559200181200080566402c81c14100521449400d4040c0003071950307a1003240b85004d40507503004040c400c8500c1c0c013464280700090380141482240e4040d60b024241c114002d0034814040001d0400500d0340d58019205c0c80c01a0319075a880d0146a8a4504080070a494170b08203501d0110800c0001985a00585807200780581d00c100c1c0204041224920344121000c410345101080150600c00000035031380c40340e001070b540f50041890250610313003840c4d07007252039400000042503920351080c81012a048040d017004500030314018402c542c0206080d82c0459001419800f0441c2803404441f0140780c44070880300800110ba403005840c1e041420100c2c00d10503400c2503102c0c80e24021014000070302401c40300110003503c070351204a0500605242c0903844e200c0d811541c041810b5100340c200782d03100b90310302140e90b40c00c00c12540010805a4014000001840b03800c481454541e202c280c3d10001d000b1720365400640d00704102c4400380c0f50050400540d40c224954503 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 222896726 1250 222895476 222895493
    0xc13150c11010c080412020f0604060801051512060603091f020406090b03101e080a03170a0c020703060b01051c09050111030c2706031f09020429160b04 67
    0x800c003410800b100090b800030605000a8a041d216280221820380c00c1500c00221044508d0004540141c1e001c940000c0b41a041310070383d41240d10940d0111224100d84e1020300b4a4800c50000c4144240c2690100f10542460005183c2c840100b108550030142444141c54202d00120076000302c25400040c10b000b0103902440e032000400300111507a0650510341c00302a0050a24018006407400192061082142c2190510300a02403c0140d071400e484c01d0400801000e00000956103858040000c20340000725481413411503029079004e13140040c00c2d65283c801420565011034100001405940a0400407400407450309815003070014828015203803090a54a41c0b40c00c2c0c4c18400400e00800096180711001c503070300344881c4440d00c071148840e000d15884a000c1c3d03c80d050340100020007044202400040c106805900700c0454400259417454900143d00c100e009080e02d844070310f013602001d1100b000640f00480c14030304416080415100e26400210050007090b524000d22005100a118248 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 222897976 1250 222896726 222896753
    0x40b0601020106062303060105040b0301030609110901060f14190e040b0a060c080c070f06020607110d05040509040c0e2a040506040b03130204110403050615090c13150c 74
    0xb814420403a00707401030660055140001d1441c5c01e510000001122603115004a47c0a0504159a50b07201d5031070382003102c000d100504045900c115000400501d501e0480c510034101c40b095900c0e40c00170000f280c02140c0c00603400026290054050206030584442d03003001042d250801d07a2000b02ca408900200001d550380c52000c0342c05134150ad034081c17001b203500003c50100e42d07030040300d40b540c0c600d4040391107840c2c10156031040c0081c00400a0114500e40e0104405000c0d500c2036851303200004900442c1611200109051300105e07000304000c00c02c5080102030740b40d02074005c400310200703c0c2d03072504040d0032008200c840c0342d002a10030f01d007024807060202e9140c040800f20b615442c10a070800000c12030601c0307540900036030f1450110020300001c80f0701030f6841c80c0740c0e80074000f801024200d02a142494005010444a500403840000c0e03050b500c201c0404071240d0010059900c90712030035002c0410343e1000540c2c41d007114482d24041180301f8180707a035960b1642d10b603075101074002d9a270030300d550140001e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 222899226 1250 222897976 222897989
    0x1050a122d1a0913060906050105190602070909050a05070f1503020906070f02060d0c08060f03030f0307050a020a05070617061903080901020102042c0f041509110603040b0601020106 80
    0x604038000b00421400541400295055520881c103440700c92245480829411000b0103070350070710900c1030400a85802c1903040359000e580ba1910808a0308078129070f80028018540107a2000c2d0040203c00038981200104c60701982c01e4031140b20581e00c0d201d04041c5550031060480041050810080780c41003000c1d101e092041c9011420841c2100c00205144240e01019168002007511401555101422610300e909a41c60401101601d101d01500e5500103c0e1524031900c048151000a82400700490300c0440700d01101c10b2440d59881800d440703903003011100004610a921007080040e170304005074805440142c817a401a00081d2181040d00c00006100c14011842c4200c9207050000c4d203a42c0d04d080d258441060341e241d212510040340280900d03401f108040514030805c016440070014150500040c12058000903070b22880e88100403d81943c00802500c001c202485400030b250b40a5600544181d011240794031007e000a03025400a503002e4070b800d80b00034144000c03980c091050030010300c3d8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 222900476 1250 222899226 222899231
    0x1020306090903070f081b100501180903090b03041403030a0506030105060a0501120903030e0a060605100206070912020109090c0e04050907050d1104060305011b02010c180501050a122d 81
    0x20b5540d07520140061018020300c50b41d008684946000e018030701c140640041b4108641e4a482305502ea2809001c0030701c43c8240c0085040640d44107048030f402020540d40d0151201c0707014629156400469070b00041055400c0071401c1000508010140001c502440100030b000c141e40c2054402c0608580028100c203109010007541080340366041101140300803200000001c50349001c6c1000c3c0d000e8030040550303002e24042c5c03641d103004000e0302d9030050b425581d01355046900c14080d0f0b84160394488090301c486010500d20401000a0458020704100030380c41854036403200c41d5160880f6013515424100c00f00030542046002100f402c0500c40e8582c00084e401c02403c41c5032900380425510141450302a14200840154600645130390304000011039214008101d10040c0c080c0600c407161143c44010015420010400141c6100c2c0b01029103841d010740000082c1481c22b00196159404071111200b801890f4075010000c000c0741c0f0a18000d4841140103030065035051151024058210bd0725203001403 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 222901726 1250 222900476 222900487
    0x10801051003110102010b030706170a020301080a0f060f02040b1b0c09070509041b020102030702120406140a0c060f0c030b12070e0402010903053a021b0a0b040801020306090903 78
    0x7420307080c0090840390000842403075040e100c00100e01404021900076011b200c1c0d1a400910340341d10003101280e0062180085030161100d81c61031090307100c01c1c40f40c802c041e8010300821010a00b400b14505c41c00e486140f0000354003405498003800e903041948400d19080e0003045007402014031000c403401950421018114041c2403400051b01214003400cc04104180442c3c00c0e091034a60307500040c52451044540181c1c00c0ca00e0310024040d41c0200d038104014041c0024000c80404058140c46c140e07140f0b900c442c2010602c20619012542018403404200000c2030764003030101e1001c5c85400004060503a001c14181d10b41e0b00c0160617079800c0000b4038003440710075610046011001ca80c440541c0e9407507120520986032800100c0e4160804d03040907086004050b900710134101d10381c5075902ca9915400c03010f000e46032804035400103241d0210b054405a003200320f0040001c00e4031520703040015001441220f91549440b010000c9400c950040c0c08940e40c00401c1c08402d1411144842c2e2104c40c2e080110f2414 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 222902976 1250 222901726 222901741
    0x1003020a080a020c0309030304120203010615080721020d0b010e01090e040f050f0d1d0609060a0f030e010213142e170a09020a08060709060c0807050d0207030b01080105 74
    0x10000b01140d950300e80c0451440715950b01441151510440101182c3e10303152a28024074426aa03084120312a619020b40026294070506a6000741c1c4556222140c8a98840100340c0f607104510141840916081401c102c0320301c081e1014003d502d16501000841e07036900c00024004811507401581801502d85081110100c02c02c0340a03032181d48500c0058005165207080e030320f48450300452520a0003060343d1940c0c10707980310349004000082444200d120800da407003403103424458102541d812000c00c02c0b55031401400784c0140301c070b01d080c1c9180014056038682a1242241c108401c01e03881c00c0d8000000300b08030403110362544403504c0101c44610741c401c1074a8801400c0740f25110140110280300110346905806800302a44690b085003903a1014504010741c1d000910322400220700c51841000d001c5206080014251301c103c6c82e90303c404042c1c90410605940c0142c0490086600100400c01c0d000042d0051214000408580d0005c148850451419081d5500c0580100c42c00380e15101c01c01011 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 222904226 1250 222902976 222902987
    0x20a183f060902150f030a050c040501050904020901021203010f03050c100203070b07030b0d080304051504030807031517030c06010b0c1b2e020c060403020d080a0504081b1003020a 79
    0x3154488000a141c01951020803054a02044289800c000221304150790090748001075100307403040c000800c21a03985120b001014042c0f8000c40b400a5410300c9841101c3c20710340d000302150341c0d050048a081400c80004c060b0f1541c426000401c0c05180e0744400c10030040300b0828581144021030309a0381c2c1d0301007560000e50341d00410700040c0128540310b001c40c40050081d0310240c865400904003004000807810003090590064400302c8042c802c8403c0b01481220301d482c518040c075459601c40307500c0e48452008030003402003c51010b01e001c00c081c60000d001940880e0345606681001c000d503846416200c00c15060000580c814100341d43d04000d0501042004548140c5001c0384440d699120040c1030003082d034814544a01c4a003025106d180c0c080a0304141c84405202c0d4103580c211444024072409004a6010350b00c002074000001a08500c000b030503100152001c1009440c12905056441c07200f00c0c9001000b084100d40503c80807640900c80c2070009503a40e04805508082d0326203c400c2c02e0080c070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 222905476 1250 222904226 222904349
    0x60c0a030203100806090d1e120507090b03040f0c050108090a230f01050f07050408120c01020c030403110906150d050603070f06020105010e0108010507080109020a18 73
    0x201036000001901100152543c90050a2100c0482e14985840e001203544c03a61700d101518086001d0f0740301d02d007044041c55818405400e00340d913840e1380700800118140240c0405494174040c49050380b0041005007002c0d01851140c4e018804a11a4a0207800c01e240d000241e80c201904029040702007202074bc10000b00e81c031055a000072a03c50441c0c59010400d10213416607104012030040c060601d40b426015042a4080e019081551000b502d600000340c81c548100c0c800e161240d00700040906070805601d02400204200c0800503142c141c41109070750559005070822212000440301c148000d08140030016806001079500242c401074040d07500590380150b805400015450b400041c009031018000a80180001c0500d1806107464403c0030303002e0403090180c1c001800a0a00010f8500d00c1401142c5c000d0320241c55080a5908148a01010b50300030070248040c403410010a000d110480c013100130041100e440e0301c0c4000b402d840325800031806d08220916140100401c0205070a105416a80 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 222906726 1250 222905476 222905497
    0x1512011811041d06130f080408060403110304140114071b030303050a091a090a02062704090323040b040e0103050d090e0105010e010c0501140117030324060706050a0b01020f060c 78
    0x81350007001b403510f50022418840020050000442d0000310400c2c00203803603010300e200362254404281d03188421540c80c0250311480e1914001405500c0095000300360401810501e070b414589004036070349408018554021192180d070024840801c203140e4184581600491940000e1004503a9621440b10081c1c0604841002c0f100c0b54001c101d10040811400700741941c0a04200c2c0c407018008a55003002215040000a46407a41d0030000d152610384075005031250326442d2000e0305035000d910700c80d1510400303119981c032103800c2101081d40081c01e0094401811482001025981146080e41c00c101c41e4840410612110480c18000c9060a086d03144c150b41c03083c64079105d40701ca24401240d0f440c041040180c5294601035500e0440003040c06058181c481650b020804008034007841c03030b9240300c2240c143c0191404244004000c02c02c00d500c01e0340142e001042d99052046a03142c0c00120355007501d002090300d40d943e281520340e580610a162450b01090050465403030b14800400d50741c0318011849 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 222907976 1250 222906726 222906751
    0x20f15010f05041e0e0f0c09060303030106050f0412080304021005070f0b060402070f0507030b0117030307030b04060923060a0308091507050f061e1512011811041d06 73
    0x69681c05130307500d00d007040c6203a04000e0201e0300600381c110361284020b00c5043c04500440c0009602420182c0b000c3d0301130800940198a140c1c60400100d48680060003081d005010412002500e80300260800780350074064244980e8a040610401c02110742d090440424800140100808a141020700c5480550011604100c0e644d5520000d00241f048080041030323200191000c1052200020303260040d03e03c10061040d190740c807401d1042c2060842884c0d01e01c198001c00016401d41c2c480e422000b408031020304081481e41e00c4481501c10383d840030210825000c104c15a21b2038034450305000c240c00c52015a20303400c08a045440c0d100b00b500c1070181c103d000303401a1680100e8406040d00311a8915044025552401c600540158907101c05843c55009001d003d80070029400c0c4142000e80103243c20001103401003250014401d074455a0034851016560315009401e41d41150141344c10795512622169030803800400c01c010071148103a00c465400d40c003c41c0b400d03184210005c3c5543e00800030f07a165 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 222909226 1250 222907976 222907991
    0x20c0108010b090907030f0207210201050906070c02031903030b090105120a020906120d0903060c0813231209030106080309010f08040609020a060c05010f11031311060a020f15010f0504 81
    0x303030080c040407d805071550b480010a0000e120740250300b0104038108484c4400d00c1d000c5254202e00340c0b5015100002c0c2a00520b01282180340248107031040188080c060b42c0070080110a40030401c1d5600d10700b600401d0300c80c1d0b4160914a08902401d014000403074881001482d810070490b03586a00410080c0114000c5001c00c00c2c47d5103200c218a012080c1c801103482036255981c0c02011041144422a0704a00742034504008034001c080c01d51080045240e49490010940c54171f0062402d241d0020055401d110805044c04c04c05102100e0000507010704541c0d108211000c0c1800c43e01654130068061f0005d011744080d0b80e03403144078020380351050301d4039060035202e41c200342d80140340b0000c000b54044072072140014041d40081c2000b00d034500035002003114081320210702c021f89100303040c2444841d01c1040024401c9840f440a10ba042d80602440c080d0b161010b00450810b0780440c0714440903a214640d42601540200b04032044030122207115030455140504650000b034040c018540708513102c114 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 222910476 1250 222909226 222909241
    0xd0e0f070b0c0703050d0c17040e04080708090a0f050109050d080f03043905030d02060601050d06030204140103020901151e17180c01050f0d0504021507050d020c0108010b0909 77
    0x100f04080c5070400d06890241024200240c5601940d841c12208100b10240b070190354075001d010345007107810b0501c00000c40c0e565580c0340c071001d5110030400c59030010305108840f45074075103140b403030b000c1c080007032440703907480d040c10005000040241d100600c20840c0700305c3d00340010204c6065a0080c003129500c0c0d034072616a4944008020900e2038440c048406010240440a03402414900c030440c1c0702200c2c1e44801d44807014180c031034126030404000350b03000d9804503003254420002007140411402001683d6600d0303034009010780f0501414100c50394425401401546007001c08540142507452103400c100508150103440540480fa4500d041040c80020581c414043d0016100070000f005004d582c0f4900700154044034541c200d5807115074800d2003280ba030654021030444445404002c05079042ca81308001840c054000144220380000c1400c01504554406901a03d21075204002603c452800b005e40285040a81c4902d6410480078030010041d2200311005c4800020003610381042560fa0301c007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 222911726 1250 222910476 222910483
    0xb011b02060415030213090608060f070e12010902030d030b0a140307091409010c1407021516050a1101030506010f03050a0b092e060e2103030c0d0e0f070b0c 69
    0xe010511100d40203000c40c201c0380d4594001c00390001241042c0c03e056468402c10811180360340038600d0f12b64490400f05040101c0c49141c2c0b030380030030645086203400c90401c0106490400030115404160f44400603481186002e101424003440d2618040090980410004103d400980303e4820000000746540d43d031600c0a10100c000b400e10417109200c0c0041c0c1100f0341010590403100c1c14815460700307405440c03182c400e9030307448000007440c4922420514a502041039119420084100e060801c02c04211008850324082d0025401500688064070742410100840c2d4102100b49041520308400c01c0b0340d030713178110100c1e000301c0714140390008155550782e42040087c2070512000707a000e4008802c2001c680c41100003001d003901040c0d034850444044103440b10044a10780504000f051659600e40030904041001e5118020114402102c01c0c125502c80380c25a4000c0e07518800c54080029040c1c030307000150048410b002a400010445614882c03912038680d20f031409521918000054499203811081 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 222912976 1250 222911726 222911729
    0x50c0303130302030c0d0b1b07060903020703030801080c060403060908131e09050603060601050c071503020711010203092d18070201060e1003020607150504150605040b011b020604 79
    0x19085990398201032600c4a0721119a2104a100384202c2c1548182802d00714a10110719034029000c15480d105ca00350b0101207a02d4072103024440b0b0701403000001040540c09007000890207a00504949070541c10300500301c9005070812001c036070000d404101c0c82d46480c400c8408490f0400c02c0088c3c0d10700c071448d00341b00c24402c0d500b0a12607100030030408119407114689221040391420b0229810903075808034241511011108540d054020f040025200d5024600821701c4100e20401d4034111501c5854030171041c80b060005100099000c5241390030047c0074049800340c84000d0000b5410029607000068801d0412416003500124046004031035078046107100d900050000d01c0c26841c44061100010040821100100150308090000480ba1040f0742898000d0401c00c3c4071b40f00c00c0b415032b0280400ca44c440d010031120f043c1504800c40f40c0410300d11415015501c0b5004900c0c840001d00c00c4542500d020750811031103246040f0039407036640c0c0c000d403030140c221500c1c0d062a0661400c5000003a1103000b207 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 222914226 1250 222912976 222912979
    0xb030402040b060d0f06080d020c090c0c120409090303060e330a080f010605040c27051c050609030a050706180b0c1902060c04090e010603021903061d0a0b04050c 71
    0x801d100c0010302d1440d50000e109481f010012035050120b144001ca035580c0c11022643c1c1c000311008045031210072400010070a0344040c1c401c0701e02c050245030803c6d2181e4000d600001c41d0035913400c04001055850b001d4203000380145451102caa0070004000741102c01000000f181c0302c0c50449501c0c984042c580c0c00003411500013440d0716049551010003a45501003003480b00519460004041000c0c40e16100f054a9112a503a40159461007001800d9002d0080c404c101d0703000003800303000030300b65880c0720444031001c0200f4060305a00400340b81c12440d00d4406881c4650755041440341d19a45640642668041904514041600440170031100b076440c40d44078010704050203410410211000f140003c0c00c042106942c205000c1841032400c036141d100540f115088800204000c2068034603a8000024140c0341200000f22140e0300e90001c3c412800d2440010403482044604106010381c80c0302d811545c0d07207003003030210951105040c0c15448040d20180142225500000326060041c00c00400388400d20 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 222915476 1250 222914226 222914231
    0x10e030111031f1d060603191112100e1f091a090c0c0604030c061d1612050304090c2105150d05070302010f0c05030409050f07090b030402040b060d 65
    0x1000303030440e20305000d031800421514940c510f00142c21451404084c00c00c042040f4034132125160744c020055161310142040340480c03086141d816691003584518024000034111443d40c46804034840c40400200a00004681059040401108948180459202410140f58103a4080221803100070b0400c0f50420301881b0720708411984502040744048440050403140019596500e0343c40c003029105a0701035151507004800400c0000c1e01585804034042d100c0c1c1001324000c50030030f03004074403030044006102c4554803e11001445c4110480c00c600a40611050194800485e403078956403480350b4803418500b5907680c141100388600c59100c640e0314640d601100d00004080381c91700c03c040d0000713a0b414107030b00c99601010845032802c00030b9041180c0d80180508421407039500103640b22058640e442060001030303440c601c00100d0600041c40036140c0740c00000307a1400c2901d40130f0650507009250380f0500088400610a001a41e415254480d50403038001c945024094003003a006e000d184200c2030001d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 222916726 1250 222915476 222915481
    0xc06090a09020f03010f0b0304050a110a0b0a0f08010f081906060b030c04030203060601051204060e030c0a0302010501170a030203180f040c03051918020d1109040b011e030b06010e03011103 83
    0x44843d0066040b10144425080308036140d03001040544000d48005200e0360042c1c20302c100041001c41c0c0003140000c0107101c030f400a0b941b124040745039402903c1000000b158182c10307601050300004118050b00b030342d100030b4581c01c0c105041142c2d190749600b44214107103078241d150b1040048580102001e8134000c0c03041902e80c00d1000b1103549a80007401708911074000d07600090110351142c0180e440040040354850141d40f035540b149001054040c1107003000c0d000c00c2115800c1003004000c0080c85070303c298000034442d071400d0038015158442c03c0e1004203580016070f11001199000013921035800c44008620a035012810000d0080320f40403441c1900070f402c028403c100d1681640c0007921402c0b8400e07a181400011028940840b445a00303042c4400945c5c90700b0002600b1b226161883d03007849410703031418090301c00000550000c402c880417a000700c8a0310040c03166112120058903159a007500d03250700c0c0c40c1140c0d01c14901480040a4504001d0708552800c4641d50940181e1581d01400c1c041590f00e0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 222917976 1250 222916726 222916747
    0x302100903060c03022502030a050313081c17070e0a030b070f020a03051804110309030a020d110c010f05090a03031e020f0d0513170c0f0402070201020c06090a0902 72
    0x840480c0300076141e180c035011100300c583d4040d00896004085442002e417505042c54201c00c10025036500c26070b0144900914000021320810003850002a409450b000740352403c40740a01d01220007109203200110f4100810a158000001c500303003610580242d8020ba458940c102c0d41c103108907411315800352842000005108480d002c0d14062030060355980140000c0000981c3e039103411100040005004108a00001c0f03000c2500c400a504000e2004ca0241905c1c5080301c1aa041a142580c03150000139040d482035804209801e1800c03000c1c01d20b00000106401030780d4441010005441c180410500d5001030f03544a1400c50b40c0c0c1540082010380416140d013401003506644130f6003510740389804050380c44610b000180480f443c0c9001002005a460280c40484040d00300b1800d030034810000041c003203055190202d03024131a005a8005007802603c0c41c08000380e4504028889010707610400690000d40d03404070381505e4095003904c0c2c20355202109004a030448c2140d500c1880704510101e1044403c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 222919226 1250 222917976 222917987
    0x20304060b01020d0c0303050c09120114130b060f040207080c07082401260a0305070201080606040806040b04111c0203060703111801120f0506011206050d080f04030210 74
    0x1640c015041004400700746801683e4030390044e901c2e28081101c030001500001d1103034114540c02043d44030083e00300010380d03011500d0384880b03003061001030f510303240c2d0002d12000e02c10300142c2c0301c1c062502c1c04000b44560340364106600006890715000d00540d08114406489a0301200c0700650312040c0e0750b0f030b5031030b000d54240d0b01e4007554064106580510284002042000040181d6403e520b07003c1d6680c9918104258488268000b60504e00554010b0815204c510900600640034000e48401d0355485c40c5200050030100700030700c05441810305200500044400149a9512a074000305402c200d4403203080280340c403039110030410380c450044091003040d01c80c010207501c900e030720a03001c440c01e81d240c2d03030300680541d481c8a0100031554018065203181e8561240300d142c01e08418105500d00070200c2480c4010340d80e104625048540e1200144411940e02c60b80101c00c0c1002410100682c40c10500025410708220300040d00d07015021800f0b240c08058a800c990045500410000c52643e180001420 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 222920476 1250 222919226 222919231
    0x106030c091e0203011a0702030c06040611010c080705180d1e060f05040b16050c010603120e010315230310050108060c0a0c030f170f06100309020a260d030203 70
    0x2000d42449082c0b010740181e4000c2c2d80c1a20f00001e0343c42c00c000c10600d40034060b038201c0c9800ba41d01d841882c083c003200d61180e40051000d0b1009a0f0b594240e0310070582d807a800e60b002801048200251107040282680d88041607681070000740a0101503c0360a50000710040000d1303101404055810300e4056403203c80444102d001c903c16003007840b60780840e4018100b11082150050140861400001c810702c08149021a440c00c2c9814a40e040c022550000c508640090300100c5280c0c0170002c414990035005103143e40c02000900e01401280031042500642c044240f00e615124100210440c00c1614078444800b041c41010382115a1241c8840006015203000c0c810041d03070b4050000421000820307001222041812070312140f444071f400e550122459400310003004e003040100f4145001410301d550031140502400010080707141804000c01229080300844d1000303043c43c140e50800140ca41030501005c427010b403010340300c00d200f96448152a601408402d03c800d400b40340190b443c400d030181d01a60 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 222921726 1250 222920476 222920501
    0x1082a090307050a030221030421110904031707110307051c050310060f030b03010903020606030c041a090a110a020106090609060b19030e010903110115061b050106030c09 75
    0x5942ca03688200340000400140000394200915902d06a440c034002c10002c1ca51400f041e0840b40f8041e80d405d40c006034034400c0e52080e025050910761040612105c00880341d200ca500700d984a000d401c03c1d55014100c00d50207504940c0d410306080001d00c96a01607503210301e50f20f0b04041581e658002625105885017080001a01e0002c4140411484613114005403407007100c070350202502c4142800f01c01d90b40704441f0800c21040640f19a5410140c1c0c600703000d00d400c11803294008000c1c60820711308141c00c0c074080341150b500444c640402030342e40c0280d884420712024070641d40341c070480c1c6a0400240142c18282d840744c095078400600c08042940c1503110301e044906420042110544850110082c0c42d5107200e6801200028018400e00003400c1d40c02c40c40018090500094200c410003007176003540d600b44025400700d80708000100d5808028016201202808811020043d080038005000c13502c00001040740008404104030800009510141c095a009071020019075629400100030704903498001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 222922976 1250 222921726 222921733
    0x90f1e070b03040521040512031801080601020d03091401020c03040e010b04030c0513060503160501030518060c0307090e0a020304031b050d030e120a0f020f190201082a0903 76
    0x301003032040c042d64000c0e684000505003034035081d82541549030340b90b21942d5040c042040700043e140c1d00e00038490840040e020140d602d816a000d140510b06907142c01d000c0c184000c2504000240e0780c04201402c40070f087c1c0c1030005059a107400e0113666655904941ca0b2103620008003c03064010000c05002150016108481c1c20b0fa01e400b40881030340128032000707001014144080c04285000c610640103a80b0f034990000303600740d8a80000e482c2601841071602881c00200040c0425685409450703403080c0207241d04110040300e00c178440c3ea2603000511100d0740d000007201144a0381d100b0700458008202c05803d8400a090824501c002540192000c4010400d034160740000c5581800640710703030070b802038080c110180601e1010340240003141a280301380e004100e400e40800c01240c1c003800014846503036151001481020181c42c0030180915885180d02081c4101e4400c40228403200100d9820701c0c0c81c040903101e12440441401000c2c00e107250041d94035100030403606c4410081c101a00c1c048045 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 222924226 1250 222922976 222922979
    0xc0a0e091515070803040b0705090315060a050a03050307020621241e010815040f0b01080c190c0206040806090c0301150f09020a0203120406090c06030b010e0108090f1e07 75
    0x2500780318240c0c008050510900004021449680e101f6a202c2481d0038000e11344009a000241404490a07000c0078001002b4240281418441d040c1e8015010540340382041d1403c544035283c0c1c134003620000902c10303100003d1242c001c200504a14403040919070501c400c90410f182c100c2d1a4100040700c10400ba101d0401e41c40007454010058100e01842441c00001070300b00c0320045400c000024586103845007004030340100740d00c69104400600400b5100012840795540c00100a5540545407180c492020301414903200302c00700c207034541d0702c0c0c0d04c1c11306040b2901944045841405a5841045640950030400000071300205200305252000c5000700300060940c0a006a40001400f602c800985030000920803410940e004100089440c0110381c1001d02d0a0030310030050380300b11002c0359843c1d1030700d04090130071900b03805d0312011300007604040c490528042d00003001203050042003070401c01204040b0310869801c0c0300495281219105540036104842c03070855052003000403410741885080f80 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 222925476 1250 222924226 222924259
    0xb0105040b060703050a1404080a03090f050d0203121309060329090d050d09170408010609060e0f1b04060e0109080d050306060d0609021b011505090c0a0e0915 70
    0x843d006260325071140e90a000703140c0b100704d45d208014071031000d9000f020480400c01401c00c00058030703858881c0c1c0d560700702d46080ca03107001c100321a02e600c824018113500317180c40010b0b540407458070030107a80b0903300d031b8850389001c441c100c4035540341c1d012019143c40e100000c000e100203400c005031600c070900980180c5100500480400c407604581601003a00045200f4140a1003003006201c4030140c642c000c5000e65141e2260700c080351034803a1211640c0700009042002c07503002c0c0180401000071a0040102c2c602d41042da84103843c000b0301c00c9070080b01c10000107076131100c1900300480f02e05c09065401d03100c0ea25240094124000790a40d2404504441c40005200c40c0c0010041458142962030301d0031500c0326000d000c001c2d0007140ca0011115110a000300b140384062014204605290318a000c0403081c50305041d007181c001500004001404e10710911440e00c41d096170315088440c0c0311a445e40c40d01c444804070f40b01002400919400f014080500074100b601d41c281d0466190700f16141c0c6807a419400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 222926726 1250 222925476 222925489
    0x1f030c15030c081018020f0414090a02030907060f051b0102030601030b06070c0e270c12061501110712060212011203020a0201081503060a06170a021809070b070b0105040b 75
    0x8401400c03041c0d0328541806443c480785c4905404409115000d03040c03032482c1c64426019007090f001419048135451540107285040482950494080d03101140b5504016604548441c2540241ca05100c112540316080c644100b04951130322a00040340c02c9090302d44140c05020358000d54072140080e00b00868240e040c68013101b204c2c00c0700d60040c0300c020014586000300c8049900240807041503840401e030340d00f20441d4150710710f802c800360030003901e14003180804003d20b801252030445c1e440d9020004114085001400b11042540c003420040001d41e4007511051825540340c110000710003100700c50504104240c0c01802d009900c051840f02c043e81c960600802030040301c030b00170780148e00204003000554000e03490742e90001c48100d0a501d0320946000803900d000c1040d145641d01540c2c49404204412901c0c20a03d00f105a00c4042e1003141c00c56000207000804e4041e91190303000c40c01e8040b8945450410000380200354004000e502e8888609010701c8030042440303000e0003141000503520f802e18261 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 222927976 1250 222926726 222926731
    0x803070207142e09050607030804020405070c050c010c02130f02071403130603021804061205010501060e01050a140405030604290402090109020a020106031e11090601081f030c15030c08 81
    0x2010b01e082c201c103110080000f01c1c0d0803443e00e020300160810120b4240c580c80020404280241c13542c1c07607181868070600c03040303682c01811304003089a110a0300700043c80c0840d514480034001d103401030300c0100c20300015181103200103450340083d00d05400607001512507005040171a00440e80f058040301c151341d09507280d00c202d44a40301c2c0304459040600002d402a4007906480c1c0318294204111720000c1c021508442c01c542001c84071420010310041009424040c0c2405448545010b2000c1c888110019202d0f0003980140f40a004807415144000080d5800781d4005000080498a050415040c103005442c102510740f001c06030003000c191031541080d48031500035540541a0151a881c102600000790005401c440840d500e907400000411607200e080400600d000d000f40e04513006505d0031007102d5490100580c014107070ba0b010029160b80045145601040c000e8075081c14080050342902002d0240c2c10060101500c40300105450b242c61620718580a001e440802c601c0402c2c0d581a9240b00c2c08 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 222929226 1250 222927976 222928009
    0x101d1005040e150a27060602030f0d1407170106030b0d0f050307050d0503010f06170406090c0b0a02030d18210e090c070b0c03090a0b060607080307020714 68
    0xc20042205104070706240d0343c40880314501c150464980d500190503151140d0001c1c0381482400d0300724a001c104281030071101da50070102005814030b41500651240145a4441c0ca43c0f00003055151210ba001c2c0c10040c045903460880e50101c1c43c100a0140c01d2182611140d05400820000843c20328082c1c0700c3c28560301e500501403004458145d031040503000c603207581125640000e20034000098000c01003540700301c12940300c8030345a41c1800340900e6160341650110081000181802e0000a640b100c00d64019030006c6010600b0000b030b007811501026150b00c0303c500ca4100190310304800e075020000c0c141803900c488007881070b501c41100f0300c40c0003c03050002508614a049900304501e05070203030080c03024141c3c2880741c500720b58000000c2c03903044120351382900494000340072400c10a81290311580a00c5a02d039250650030040c0c01581c0c3c80101c0344000f401c58190002041881e074644081c3c595540d8004a442c1d0340b8900a40001d407560103030b00c100d41d04403000e010300070014034051203901101e241 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 222930476 1250 222929226 222929237
    0x10207120b07050705101b02010b0612040203121b070e0702031b1609330e0c090405040f110f130506041104170610030809010f0e101d10 60
    0x185803100106454050102c40c2841000c2102c5000101c2c1802000c041240302d6100041b2101407000c01040d00035038a050a0071039141c8000740907507581d000143c138140b510071010014565079a00c0402d250003a484901c1d00398180100d040740d5a100f401030904140120801602d040b9541d908a40d90324940c1600d541c000f40e003040c4403469521001e240c2000320304075840101c03520019100d1400c0992143c540100358403c0d1159000d00e054120741400c0f4005000c0032401040d00307034110025418050b0300d40182c50440002d01d010440000390107041c1c600d0780c040100100010309042c500080c01604c040030488510205c4401c004ca14903044000340d011800250020144020040c007100041a006082c00d078010b56480c0c0200440304003030003410103840043c4c18488074005003c00329103048001420741144e46004182800002e1501c4150307000c0c41828207100107a20482c1c04166007444000703192503045044480121103c503071000d85061240c80c91151078004522000901c10150346032400382000c1403 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 222931726 1250 222930476 222930509
    0x6050411030c0706150f060915050307110c031506120d120e15130c0801020315132003011401020604080714071203050d050109090c03170d020309100b010207 69
    0x40c2d0410003081c400d03214040000310f011130310020600704130350707504101e600104003182841115080b0300d00350050851303902c10384a08466010700400c0f80c0b00040009082101038403e14001100411041c1401c101c01400d56000041c80b0100c000a40b8044034120301c21a121000044c4514010032100c4407008260b45070412600d044207010081c0851294025440c41200112409000e00c030801c54010160aa00203008a56508028107540c01d00d400c550680d920400502080707080c440b0040416074402d450525065800f245c1c03034401030807104601031000341280e210844c2602c1e482c0c000c505075854400410081c203801030049a8a40301150020209102040070401240543c0b2070a4000c11564049940413916215010a40e052502d01200844c001003154681a201401945d000d005500c40c20445441b2a0f01d07071b1203a80c40ca80c0700207007480390884101c1114500c40c03421181c0c82d0081e580251f5a80c108030800650b20b100d08000030b4115032600000a403998404681d02c0201e4104908101428 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 222932976 1250 222931726 222931741
    0x50a0c0206160f0821010e0112080d05040f050607020a08070212070314060601020c0d121d0a1d0601050403050d050c15010305010c0210020408030f0d0f0608060a0605041103 76
    0x5920041e058118982e50040010008101400c5880954440ca100300d07112801d0a20041c007041c0b140b000c10107503042039401031040400a00c4501d04444c10751034409080489810407107000d21841803038001207401c120030417051003070000e4412040d0b840351044489030781d1090300403a115020044014400c0c101003010f600985030400e01c0584411354070003072310301480e42c039680c040640141e0408080350b5000842040419070701405100c3c0c0084055900d202c040000e5651190f8a1030403022100522504030501d103461628500304900100c000b602c05400943c4541e030450324803049140007400030080000085480d482030307050760300303c80d48030703001781101c088001c2c0c1529541c0010003d00700c0c5c7d105075020046a080c22004250081d406640006240c24600400a050000c050321101803a070040004000c0350b41e0020403a0075454105546c01c0c1c517245181003050180403412400341c841400c1200200d40b034200414141e0182800410420001d82c1d6070b000c1c4002d4641d0995096002c2c4414400541c01 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 222934226 1250 222932976 222932989
    0x1207200606130b18070c06050a05010b0f0a0e0909011a041a100203070609060204030209130201050915040905270a050604020103091a0f01060e030601030c03111302041203030c050a0c02 81
    0x54503030013000075048030f555400403ea540c00c102c0750344000842d0140994240442071050a0300448603941c01e020b40e605003550024148586d00074103010f01400035000d0217140c0f1030501c0c3e05800400030a0560135040548103980a040500b04181135410700c1c841c0d0003400d140c9031041c8040401302e202800820701250013000202c038000c0014000b0340c0020003198000403500c1c4164a00c5620031440183c0ba18198018000c20f40b01c01800c02c400c1d400441c28000c05070307130808150745540300220780a40c0d0041e040b00700c241703031402150f000484c002c0c2064248080035101e860079071420184c00400c2c105151500d418681e40d041c6000014083d074000d5000321340954403c0d0400b18613540a20300205d643e1916940100500008031401c0e446000700c20014401c49600c100d020500c25000ca00401f02c95041d5102e4a4140825100040c14040c4051200f06c04d80c0b5208940e6807040160402191100d41c0d40380d0070b010818041070102e001070310b00a031058480f4001c0c025030301c2d0300450382c2d280540c01007541c2c02d0102 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 222935476 1250 222934226 222934241
    0xe0a0305070c0806090d0e0d020901141c060504060b0a06170c070203030c0a110f03030f0d1104090b09060109080c010c02130c090306050609010608070f05120720060613 74
    0x52911a1080c08241c0010400406020302c17803200040866001e01c0d80014800c0051580c028400d241d107906c40f2004d6a60110401c1c1591207449140050241c1e03400010700a55100c3d07400380804c1514403000044c400681e000074800c6000d042e0500c19100f0203000c0040c0b856a0b80103007404900c13116450307a08000540d010940c4400c000920514051050300081c0c030b141c00c5140d14044c103501800c1d92a081000c140c507018810b1a054820f81400c00c00400081e4607070181d0142110404c10201d02413106030800c0d0880901c507a1015039065440c0e4070799140c00054501104814010140103000c070f1004d5202c0c813a0081101c16a102a080400b421b400444a070344e6200000c1c1c0e0301042030342c06100070031410f10400001d4105030710745210092031031900e0420f8130001040c05101d030022100401140350080340b4954464010326140310403101001054031140203445024450f01c403600100700695070049440e21007411305020384078102035040c0886a079098112a0b4940107200c81c1d51190102055411010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 222936726 1250 222935476 222935483
    0x80901140c030705070602010e03040506090a0306060e0703290d05070306050a0204140409051c0903120c051b01090b0c030408030d09200d02010518120607030f0e0a030507 75
    0x41203111403600350344050300410741d1000301e0742001900d40d0400200708501001800540001c0c8071410318008455168003c910984d402070000107040d013440d81c0c900705c0e071101442e8002c80070807403161500b00d0403224213800c8446e1720100c1c0c90501c9103c002503100941c40400b0341c0300d22248548422050910480002d0000f00f100c8500c80c00e24003000044003030080d1846245915401a2240e1604408090340c000d03400159004518080000001c82e5001c50080000c1007482e60640345403179100c2c03085a08148640c006024550060324200415034420b00c0b038040d90303010300704130344440c84d8580705c4580020803e00060301103241d0001c00c01540301e456018003a803074402c1c0b0549003459036070540c1c182035501002507440000c2c4e07554000310400c148660728190380d0803030b0041d90020003034900202c0d9103c1d501c42c20203414000b01044050404840305403601c05000c0c06044200700b01d58031511641e6500302075401802090402c400390a62000b584125015071450030020040c40e50261029a01303540170341030a6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 222937976 1250 222936726 222936737
    0x71e08090d0f0f050f01060b0f03010e0c0c0703030302090f0108060a06110a0206030f060102150403050a03020906040302030a0f060629031e09100c0801080d030f1b030b040f110304080901 82
    0x15808610282081d1424502a03001740c61800071080c0c00c1401c50310107420012401030140301108998412200741e9055031240e01d402005505c03506000b9031a402082c0c007000d00c9210741c3e136003c81010b81c942c01400201600780c4171204420301e0f02c401501c1c1d0403030440d042a0010040740e000c03c0541e104920300f401110080c000da0303040d4401c50300410560b80c0200e6644940750840400d004803540c1c10809080381445004561140d410203690041243c840d00300da5401b01a00443d404480d40c0c4d405c01110011503000301260710310655890010741030703512100e081c0c0e41e561910800186c0c0c00c0c02f214283c60251007400d0300c80584002c0241205c0d16400c041e003040045102254003003039003900c172204207001d0b03407000c0c009040035014810288280e0740a01144408c00000c040100b041040000341c208120341c0c2410041007240c1039144840c003e114240c12040c806400c100b9004c0c00355015404004021400c0c0c42c1808052811102d48058403540402072080780c00c1040002c0c040b546002c0588998001450503 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 222939226 1250 222937976 222938003
    0x1008070b0414041a040c030f0603060e0d05091804020307150314010501090807030b0406110a020a1712221209030215040e061e0a091b02010b0f060a0201060504060b071e08090d 77
    0xc80308440380c07500f08a5400340c0cce400c011003800c101009006460321241c0f4000d803402e4402000301d000c160031a500124410948008681107507018864440603210303107103000c40030214100340100600400403055481054410022405500c90340c0b40e402620705000c0105200c500e580d480495a1900070400d40300c080c0d0394544140c002ca00100101900700d1560700402c801c2110341040200340c0725003001c00359640070070081c24a070302481f1440342d680080c00e4004290b10801d0100d1020001d140f000d001010603500c14070206c2040d030044e03900401d4032b001362010340400c0e241842003501e81c41540220200e40030440006911480c1030700303403aa4241c0041c01030200700d526410118003100c02c44c1d041145d11940b5007100c1e00ca007407820040030080c40c900f88000d000d00c0b0300850101c0c12003211060041e0260720700140070f12115000750404c0c1c005140241042245556540c440c4000343c2000100711048106080d0303c0c500f503c441d60705001403030b821850080c0341400e2042000004446400300b140c2111107142c6 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 222940476 1250 222939226 222939251
    0x6151804060603020a1205010e0402040b040f060e07091a030a0e0f060106030c0e06030f041b0f0f03020102070605180609131a1011030f031008070b0414041a040c03 72
    0x41e07000109002e0b1800358a40401c072401801c0d80020421480003a8502001004000310040b60543c0003078064a000030894404c401050103000e5040800050506002c3e0000750ba001c1700781001d00c16103003030b03940c450030584442c84040031201c004121501200c060001c1024007009030300070350364010000102c403002c02d0030302012418030030240e00006c0840e82d1603c1c407001303070f9400481d81010703ca4100d524524602e85013010302e440c0000a040a07050800010b80c2400c00350307000004130090141c00003024909a075030004c0c101c104506000482c0140107907040011300c11301440a43d09080c1068240c0300c4501400e90601c50140c00c8201c0595205040d40800c1c441c51245207c2c0d0102c10403013a2007428404581007c0c41200042d4202c004100f02100d0b5004002c01302c048151071103541607054082e6261100010115180d595401200480c000e5000001d22003195400500440704250120a041280f220401c82200e000740c41c1a401e140d5490f60902c002d190a0b4411a020000e50a0018030094040d1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 222941726 1250 222940476 222940481
    0x507050d0305190618050a020c0316120203071205071a0c0c07080c0a061101020f0c0f0708060c09010c060609110406090504020304020a1503110a09140906151804 71
    0x5801601007603407076041c07040501203440880441c8550f00d406100840c0b0f01011001c89041d41000384408a56a40205030b489070b5a0b011940780400b0081200e44650090b0200a1440c41100b001c030340056113102d03101030941c004026901100d400c4035416844583e07128003964a64410700e0304840600001510403910354034040050301884208031155210f2403040e00075403510b205074200b100158801408101107565a5101c242a60f180345005140400b1803d01c46019014210340f41c007285030089016a003108000602d0382601d00303041c04480b45075550b8011a504c414060b15a42c60380d480070015103200e9406404502c18851240c6d5002035140d45c0e458260080f1040f0142d405120b40d400201009581c0d44004002c0c0640400c84045185080550000301d1102c03c920441e00c1d800907444c043c240d6640039a203c6a08601e9070220550340f15044000101001c10030700400101001c2e80340442c3d19410f026040380c0c821503002d000203800f40b1617281883d146810150000d088c804035585c42d0005a00c4a0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 222942976 1250 222941726 222941743
    0x51008090a02060d0e0c12030906130905041214090117041e050606041a030304050d0f1203020301180e1f0e03040b0304060518030a030504060b060c0606040b01180510050705 76
    0x2500002035640c001c07a5000c0c10100713441b881610403440090b10050502010084514252003112084e503a0074644042203c80105075000c100a586404204010700c5a40200b00108590a54840750070340d8060b20b2100c21030040e50071080c000703050400c0d000d00720b8048101d01a0003d004200c048089141d00c0340303607a8451402d11084529821200a10043d820f050080c224030b01101030b1040064001c6038007080c0e1f01c1c06148600b6100e101044240f00c14030209040c0242d255401440e10b20441c0b0301404003030040c5d4401c1c80765421002821984403840c00c1c451080c158585c41f21409420055004011101103417800d0300d1011039250b0f82c0900c001241c1080000b0030040000303031010307a200e00d01418640c0881d200200319070141410300c4140300600342c003c000c80e99200d03218200000d9a48a50815030010440c0701c03000c030b80203c000102c509034150005502840b07001c0441e420700c50f0f01044001116141e801c50600120400f102c04184a24a004090302d00b080005103000d03400c05581e43c640304d20701803a1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 222944226 1250 222942976 222942997
    0x20c0609041e0902040b03030703140901230a1b021309061503030e040e011103010e0c16060902042004050f0f04091218151b061a09060901051008090a0206 68
    0xa4034854011400c16004000c10006e01300d01440c1800610f481c09031041c103586000c802c240c040040c030b0385810b030f01030340003800f8001454415003503505400c9181240396200000c404081241440600c0c80c811070300b0040010746601410001460340e1a1000d000900700040007110310585035100c0308400362200100600460281d917440418030040f134140b00445040909000302070b410f151000c011285982c00320b03811144010740e00c00d0030380d441d41101100d5004a04c0114104117642c03612000f8895503801410b145030088804111419448041c00301c1074110a400c14a000b5003800200501c6c036100c15441500500600f0840781c070071040340020100c131040313030040310500e400303e00175100683d010f42e202c09030740d0166010844c1c0700d0800307508008524180c2c15031000c102103580d03100010459003501e811881d5014505021204900c00c20b41107400170701020600402011000400903e4489221412550040c2c403030152041d104204940b00c0c2d400600000040c42030b42c540b200140c58002c002e0688810 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 222945476 1250 222944226 222944231
    0xe190503061e0c0306010e060d020d0c0507050d02072103030b19031a01140616140102041505031b03130c0f05010905010513090e0a0c09020a02010b010c03020c0609041e 74
    0x16951010b07200440068800100440c3c1071007080340c0b90340c0150f408031403000100c810945800d50f100c03502001c0e226140038600c0e05400e0170007000246810170041c1103180e108509840200704001805c0b0b0391120940b1480a0b10940006100810301006240702c50141c042e283c04620401c0c00780110b403c0700384c1c044c1424a030422a0708200244002c8101801094441f041010119451300444483d4540183d40061007a5000202c0c003030302c074440300b03e04121203510841b101d01180080840c00d0003074203d403081c1c0c404000e0400401ca0010711820450f0b20840122040703151194000740c0300300b056000104000ea01e50988414400410110401d03038009244031503994000310b0a0800042c004030003a400981801014072918001040100500042d41c3c46004005140b407e016625407901d103191a0190a0420132840840d101040c3d030002c080c0741310f4503002401292101001103c40343d404000180050300400c5491303603039141220080408aa00400104180080e22000c030305107415807042c88a005d9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 222946726 1250 222945476 222945511
    0xa020a3c03050d09060806090c07050d020105040b011a04230904142107020d02040b151902070b19030f110c0c01050415051608030f0117010c0e19050306 67
    0x5080080420700c0d80ca81c44c0c18542649071000161012001a00b802c1c843c01e10302c00000c0300c0d07248071801d4034042d642000c100c410740400040701a0003010b040d0307020782d070301c0341c0207800403a484690308001c90b51540d8540328185000e00c0d002240035503020645c2288041a00000401c006da41c50142c914091400340c01188504030022042074078048134008481c015540c040d2800030165007520a494040340c040d103d003140060a440050f0040002180072036200a1617a010700314055000c0c0500501b602c10442440d030b80c0e10303a000c248d03642c1116103e07e1580c0441081004042010250038000807038036400d011400091450801040d61a01c0a448002c81804100404d00400800c20380025580c20700f88030785818180102148031640303840c118800d002000418003522401203060b19900e81d000320203981c50341007103c01105c42c00000c1c89041c070342014003000c8818440040c8244481440745e619004480100c4000b8810f02e8885100d0b40b503c1400e186000145645051080b03d01c15490443c4000004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 222947976 1250 222946726 222946733
    0x50c09160809011b030b0a0e0a02090301050f0609060132121003031d0a09020708070b070201020a09050103051e0108030a110102180d1704030506040209090a020a3c03 73
    0x6003070040104049a062000034280b680700c441050400c40024a00860180c80302004140c4100103680013500740d24a8508004004c001d6030302800c1501d1040f0001d04c02500d0360300032a010b0213015103429500c00740ba01c4c040f80142d0b020308400b1108229000050308560310f140d00d03980c181c52102d505000700c0140000c000f04011000c80030341398000302e0800d800b0369480c15514001c0100400d000b2840c40307003034681504546551361030307a0b0600802824005558400151402d402c0503000180210b4202c1051000314061500600a55001503401e54030008500e240c0401100130b0140034052150241c82c40196036a031040780d00310b403406000c8039002182c1d50980c0403c010880340a217030380d0f00c1082e4410b00160101c5040707080810020b000866102c2450401c1d407c090004c003440070b69504102c00b00160020801c4004030b04036100300d000b1611916a9a070700d424140d02c5402a07400254000e16002c0300340050009031000790100d00c3c817840400c440f080501c42841004840d01040020805544800c01c00c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 222949226 1250 222947976 222947987
    0xc030f0c080a0b04060c030b03010905011505060406050d0902010c020303160b07090605031801181b0b0c1e100c0905090a020c150604110304031701090b060f0304050c0916 75
    0x4100c0c140061500c2c16454640d035100600180c03000f02225155107602000303601c41d400c60600410002d00801c21443c80c5d01c1e00d07500074003190030b0130310300119044000206440c000082c0c9003207907895103034280f80c121014100300060400300c00490600450001c0f040145e1820005403da0a07102c03444000700d0300090900c04211b2034010702800401022100070f00800341c1c08415280c003c103151106050104000c03241c68013400c140c03d40603c028081019140c240301411000c1d054213242032000360300d0b00e51100302e8104244251101c0700202c0e4030160b1003c400286e426405001c61401800f9a541105041c0d40d5201340d64140c18200006440c02006020030700d000014036420652907402186810020000c03130340c6030361355280c00d09200b107040f40c005000d0f42c0361904010fa520a804000036640c0c40c3c9840c0c0500082e00389903d00c0c242165070400494030255a200710070350751000500c00d504015007103c000354240d00041c0221003d016000700e81c3d02c0c40e143c54000310b0280751102e150806004000b00c00821 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 222950476 1250 222949226 222949229
    0x30e03070c0b09090606091018031406010f050102010b100e2808070927050703080301030c082109060703030b0411071202030412020609041407081803090312070f0c030f0c 75
    0x820313a1b00700030b0801c0640d203058540340d050150b410541940c400314030b0603282d03a1459074006405c2d094100444201c501002c0740150580303089115a0881c0c0b62a440120300301c81c1c0520703602d60014504ca81030104540100c03040b04c5428002071824003000b1a000001241b10b46002000003800303410202800070640c24400f00000c0e080040301000030001000e82e040041d000c01070745001103a00700042006022050220b6001385401404845da0382d41e491402200c1c101861050180d02e0041510180340c0b01a5100031580d4140c0e141d12140c2410109002c2200b20341c007044084050641d10741e403210044c1c94600411f003c0b0144000966280d00860504115444202c1401c41c2190020003084c4580d040521700c5000d00c0750180d400d40d813600c0740180420028604103410302c00000c4c0440070414a07070341c420389091203940c4090104260040c0341001b00e5990258080e040d606402503240c2c01d40c00d042000c082c5c40c12600640c02142c0600c0749850700424501c1a030401ea403961403035044a400c2c000424940390 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 222951726 1250 222950476 222950479
    0x501060f080a08160201090e0403080106031406100503060102031e040305011805120313060f0b03070503070308030c070309031202010510050907080a050c09030d050c010f150303030e03070c0b090906 87
    0x84800d450ba55014075072240e5444c02e0078620504505905691040e407070130019019070701c60500c0c9814903040c0682117000034880c41002a0a05080c50154640f1400103406032001419a40388810400c0098540b500700406280c1113220a100101880309560002c14484003004840780e41c0d20f0450528600356a096001c200900c0c1840300b025001400014003038074450300081038503440b42c40e0f0103540d240700c03c60320784083c00f42d605140b20110713803010590280c10010411000c071071540340e0311000d0544900e41440042c06a860900000300503540314030007402c4040c403034a80015000e45940e40c0501c6101c100d2290300c0145e64070380800001c07912214040c0003400c0704a502d81228a02180b0040020400820076002561101c010829114000094400341d54006090314000580701030b0044c15604104041a69036003040070031444c007100d03031003080001c0e15460401580541146c909801509225030784004034441007040c803010a90b060180006041c4032610f69135111850810440c015001500c0103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 222952976 1250 222951726 222951733
    0x8190305071e03060302040e0f060f0c1b030706090c090c020118020f0a05040c020f15070e12030403060516180b04120206070b07020d0801080606090403050d180501060f08 75
    0x32145640140c121480b504500114000b0607445107000c6001e4551684000d402134140603412000090204d0622541c1c0101001c486081d80e405104040b800800c1d42c80003c004c00c00c000d521114203001030307030120704000c0c541124a0010b4594625040fa520894140e90142094034103214034645405a00c0113170328244024002c03070000e02180c50038031304e583c000244240d5141d600030307050307440300c004120040400420400050210000294444503040e551000d00c0c0a1a41c8401501c04801901d0340118003540d5030b0b40b421001901805070034001305600ca80c407484241300010000d000380c02114030070001815610032034258a500504401e04910000d890041e809509000d006890402e031801c842c840d1412a100a503035001040380b030321880c0305c09070140107500200700189400140c60640241c50355560710341031b070342c8200340d03a1280820390b00507a1042405010501092080c0701a07c000304070308800283c550311a441841d94080b60745030844044e5100c070b600b00007215010400100a00819014 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 222954226 1250 222952976 222952981
    0x3040815160825030b030c0114070602090d060e0a120c03021522050312100803090915120f010e2b0306050a06110d11030904200708190305 61
    0x91115a00c41c2000c51001c00000c000000d4400c004407050a100b1a0241d4803842d007000018001409090003c1340103029100d02da00c90451035210b190100d1101a4171020a410311002d43e44683c0654030078400190b100401683c003030003196803841216111200000142a400210320b49942e01c01002514101030040384e0f00c03000e010035004542822074001d10321940c402d581d69500c0084100c4450044003e40c0400003802100704040080201114802e00b1821102c43c1e40f01e480c020003428460080e005a0740051284881d5400c11200558000034141d0000070192641c03070104881200601304c00080364440c02c0005900e00003840342d66940110740d4041e00c04010725040c1404400c000011440c1d00080480c5071070642c0d44203920440c0940f0008104115041d610340c001006a18a00004d200d00d0240011080015000321000a0140d03052405107040110b98410440141070302d28031841c02c807081004134048010a1401403107010300c211181b503210466401580340700c03045442e548090601d80400d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 222955476 1250 222954226 222954241
    0x3250213150b03163e011802150a03061505070b061e010c05030d0e16120f020f0f0603090a0308010e04031b0302030d02210a1e0207081b03040815 64
    0x100c04c2e038003440798100202e00c0207004070300041c5010413801c200c00f81504d05c1e200f13984c080c0a52041d0b550b0600d19600038850390026004a10100c80d89003402076108000005180760104000064200820b450800007206a038603240803407000f08080399500003c070001f401031b04100d50020a60b40140c01610411141c4251684080032101140542d9042c0b050015240c2c041000c10403c69445800041080c0510307130002c540716949562107009510741c00c62014000c11240b06550400c075000760000203a81031840d95809015169050989068220110304070318981780d01e0f440015800380c407080d00280085841030400429401040c1c001d80c0b070803410310007800007080c3c1c0a07580317100140340f80d81c04011072140c500e42689584180b605000070680041038a428040744c0195141d8965441091001940d907590f0001007100c5d03c100034a6440c00f500c800342d9074481c21903405082c02511900f00c1c0c07031070420042e40c0f40b07051102d00741300c802032944002410710450034180051041ca12104104000d00d05000c0c6 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 222956726 1250 222955476 222955501
    0x70f0c1a070216051e13060303020a02030d1106010e07050d09230102030603060a0b12011109120303090a03030b030304030203070f140d080d0902150a032c03250213150b03 75
    0x2a01c04c0d414146055034516160b50342440074020151b4041700f04246070743c915019480b101201c82c140e10074040c4046c0002e000340201c0705418400d1140d4080d01e104e80c01c1c03004ca2641603401400750740c00c110044c001800c0d848a01c0c461a49000e00031400009001d40100c00b105070f080070018144010307401401400501c0d1030020304142c0045019001203504100200403072aa0280c1c105070050660820040340300010003003004003c03038007080d15090502d901c0c0b810850350300e1009031200c010941c0308180610100303109910402c0e0074076000301034a00d426503d0300081e00c0c142c1c558105484403500750100304003080d0302c0405c0d0700c1607003410741d04103403170181d50f480703141d0300d4016805440b444c2070301ea502c01003c41d66074488114075011040689519000e0280008004140c100d00214807800304e400020b002ea9001c40f603c480b0f07014814015407420b103090740340e81807200e844d5000116100b088642c030700c0103950703162005109000d0014001f070741540e225580d094007c155481003450010400c10710010655a1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 222957976 1250 222956726 222956749
    0xc120a081602010512010f060f11060708060301150b09040605010e01020d0305130f0f0201020c120703020402070c0504021605150606030a020310030501150911030906070f0c1a07021605 81
    0x444141c04510070b8001a1351500c110080d0340c1400b12400008542c1d41c02101010341035510341e80d9240c01030344840a040c0d50103501e02028004562204c40007504c1c2512641c0010b5208074003038004100c0728154603000c0c4529030107070410682c0000c0440e035a405802d0910403d8001c100c00d281208540b800c500000c0e444001c40d480708001c15403900b0001b15036120781c000c03a01180e07034002c0c11a0031244460914004044038003000b28010f00030321b41c0007049403800d8580140c0f046841009010307243c0c82d550030030000b588904d00489104100b0000001e507a81e171840981030860b060b0320000d64045a610301036042001e80307000500644026018028a600d40d601500c5e4030a83c0140010b9aa840741507511020b0840769100618560034125041100e88c4000a56000c03950f03200e40c2401506084001c3d00b4860104442d449078a610110010703000300e101d0510800348650f682000506840301c4c0e120b204403107185060b000c56001c2000c007071100300e42e0304000c50200c41c0404000e1075003e90601c00020000c4040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 222959226 1250 222957976 222957997
    0x191707030e0a030602070204050603011b1107170c0108010b0f0403020d050a0230190204051b0706020a090b0703020a0602030c0906070b07020c031606030c0e10020c120a08 75
    0x455808101805141d0803184500001c114605040d40c0f0b1603c00083c1d4080b100c00c901442c100b5020440364141402003000c00e09540b0810100e20003800c20441e001000040f002c50701d40b1a0740da0010348411030380c0c11442c00d050a1000350820b0b8003204009000c4410690050b52a41d03009c21094000707404090560301501d90446544d040240c0c0340c101240b80110000010754000031448054446400a914001404124480008132000458211521100904440d200002c1d404410100602e001e51155920a6154070965040704000c4000170440e0003540d821100300e0344c0001d6030300d06641c2101c03081c8010040c2d110458a0902203039002034588040102c005c0c4410b401001040c201c20071141600c00c800b03400b038040c41d22503280d401c00b000811407d50302c020140c041d4a01500640c10003040381413118004510030b0322490300c0c05404400406841000c0303020820724190302c2030550340e1010900700c404c00650041003201d450604001321404440540300c85907000c0ca401c100020890400e48008025 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 222960476 1250 222959226 222959273
    0xb010308070309031a090c040b030709110f041401020c0f03100504050c030102180f09040201081602190602090406060509241b0a0606090b130e12030a060819 69
    0x80c5150a0f90142282d4000901e07070400c03106404078902c0300c41c41c918410600032044030064101c201c20300044840c2800801d4042d00300500c1844560815000320b03884801480e103c5240c50140341c0307a03c409130401e4000c80180340303210790602050360341007040a469490403990f004481805c00000380c1e41e00c5060b000030040a8030389000400340002031020801c1c030038000d4000d42d600c0800400d40030410f0b40c03070740101c1c1c4156039a84c8031050505100410910856060f1900d50351a215218621003800220307950000710710400c1c00000e000300740084545003171440ba510150701e9201042c100f1003a1242c0d9000041044014000703072142d503031031209099080d181070009024012160782140039601c680c00d02d28203c05040503480c1c0c014080020b00941c200c0c01180100042602d980c0170b4030a4450880034250b00100c0c900c1e14040c1020180d0140d103851880358121050352070304460b0400fa54204a034005012655010200030f124000d020b00d1514450b11030001c02407480980e2401e04000001805001610 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 222961726 1250 222960476 222960487
    0x5070c030315270e1b040e03041a2b050915090c010c0515010305060f1005030a11012c030c1507110102070306110306100f08060f01050d090c090e0a0b010308 69
    0x40c0716501c81030310590020180c03007100c0f595584072156a070701c051019018038034161110141c440040300340c0701074844103001c1c007620500e641812b140941141c0d03d5240f404142d4007007404100300a5105201910004c0c0001c01c182c03a000d04007a0034005080b09080c50155480f0400c00d04100100d083c0007001824208200107090a0a105207407692018100881e02e06000000c0180040043ea41d803040c41d800403482001c1d43d44010499040c1e0280c8240ea070160b00c5012002c002031580341800041410615048009020b01c01d80c030305104c15600c080002c80900b9044108040c03d052100494131201624041091842d91401d50300340e1140c8070001d4040c0590b62900351840e0300c280514401181c12080901641100b440d44125030791050b5070291241c41111400c40400d03000d80034924110301c06895088855948405000d0040f58200c4001d0400c03200b0010440260090f1081c0141c0303e0051207460022410070480340111550248004200d50000c500c500c009242041600e0540b0703400181580c60301d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 222962976 1250 222961726 222961799
    0x4020405130515270604020112020919030302160b0712030b090f0f01120201170c04050a03030305040506150d08220e0702060708091e030d05070c030315 67
    0xc40300d81c0000705103000700d424145010503401c0859000c0d042880c5101c0084590f4402549201c0140d143c8002e681c00510000740990b005400b5882031496030000076183c0704808001450381440e4006c861f01c803420201d4180281a8104000345040d1400002c0c110050704140481c0d0540c09040c4004003414020518691164825000070b03000140c003a00740400303410541e04070419002d04569650800b580080006002ca90b81c0c801c0120780c03601070312a0759140c1c2d0502c041504601e40203045c20f01407082044006040d80311201c07100021400307941c0000b520f0400e45007207400e003000504284425050210546803035036510044c00030f07582d440b0550564481c2545000d2210780840390107107403003440c184030020302c0d04000080107120b200164240e600c6580c4406054072181801d4031a240c080c0e0001c0c48400d1500b80c2900d0a8450b80a060b041340d007801150300066007907034000c507845c1c400210310003240020150540216113940c9403a0095890a604103410084902c0302603402454842072222a207021 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 222964226 1250 222962976 222963001
    0x102040506040e1b030c03070c0201111c030509070f05130b060d0903020c0409030210090804030c080705030f01090203030a0c0201030e0f1c09030c0620010f0f140f04020405 76
    0x808000d0070032900c0d603503501403004021608940d004000314500003d00340c200e00c1503040324800c003545900a0b0079520b4080003151800509032040b418071602051010301301e41c01300801d040c000b2130014080c5049035250b2005050f2400036002d001d8a52200d0403d00401d11080c14250581d41d0070b0f01c010300500350800300900504200041e4a402080002700b280c07030344007130f900003008180c081d4003196000202041400110703039501e600500140c20600e41105615201e0b00440b00d0305000f203041c281000d440791681c4c80c0e00003030740d0300402c0254410300b4100300600b420310580702e0401a4400030448500303550007080e2a8032424480c0420410100c5150341168029881500e43c14808000c8402441c1103542281e80c0e05250b6110340030101001d441c0100c2d081c444c0c58510140d80d40840103c0c002460007a0a0710000c4804000b8030940c200c1c541d000c50101024410844c0c036080d0328002049001c40c0800326021a607201e01605018550311007001450799100c0c201d15000f0b076040d20300042c05e55079803406061 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 222965476 1250 222964226 222964229
    0x105061216091e02191103092206050301140a0b03030307080c030c04120c0302040b040216021314040506040b060a080607080a020c01060308030f010905040515090102040314150f220203010204 84
    0xc3d12071010070f0410304c0044034140c1c004600c4598071340115110001c00f6047c2d0301c1c0560002c0300d40c04215212000300300408101c1c841c011039000c01020460342d8a400000342500c2c1504a0910300e090504100230381d52411f401141d01e4400203802442c95800c000740c000708a00e100901034120f000c00003000c0f44e6000c800320203d4000323100080803200708058034600312100c56001d10040e84a00d003402020b450f140b401e40708840c842c03403000d4044c10010440e5400e00041004c0b24100c483c03c242e0307440044c03100e80b0481307090500c5544103c3c050840c42c54a80303400c0c030a01c0c401900080c0128047d84043c8450100050b501350445404d0070218520743e078082d4000301a105481c0301e0426942403400c000108071100007d18003410040c0c0c54600700381c2e20780c403100c0e00701e85086a01403e954030001e08181c00d440101d42c40c035040881c03000003615041c1c0300d07165820a031749400181d140300e6000440f028103440b02002c0254000d09003034460141401c0100c80d08030100c0756221041d0029032503e05980071550309604890 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 222966726 1250 222965476 222965531
    0x3030a0e030a0b0a02070c0501030c02030409051e130b0c030c03040311120d06050102120c07030f0c050303032403011b0e01030204151e020721060b030708010506121609 74
    0x6100d4a41360100c0006508194005c80309600810783c04580303507010b405200f07090040c9078002d6040510780300d130000240c140980310306440c00841c07480b5090070381c1c203990261140e90420140300c0c0709141840c0501503810000d1281904110070b0003402498911075007100c0e0010381610f08420445440b50245040409012a201c00381400240c0f5281c180c80540103075003210403d03001c1c0c03032040030412106101d074410034010113038030b800c601014400214148491001140990402900c0d6911800400d1440c0d00c262840010300544114103003086000e9071603d0700240050780240300440e07071992a030044403004001031007480500d0501d0780710342c0d01c42d42c1070714001c11040d510a141e10b03d030110050300030001802c408020707030544019a02010b000044810443e071101e040400110b000d5003627080c0700350943c02d0071111580c4940740a4440d80d010025070002e0f054110000a0794100340c41000500075001c803c615107500469961071a10014000b04400c03640440e80109800380305503908442c030360b4006040c8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 222967976 1250 222966726 222966743
    0xf06071b052a030c06030c1e0d0e010605090a0209090103020f01030b040609090b130803130c050909060a0e010c0207150201021b030309060c0415120e03070803060f01090503030a0e030a 81
    0x2a504044464440210042c00303034180c800e10708608041c44640d100460303a01400305010042c01c2e043c00c01d40342e041c0d05100011620103013071446100009040e150010900c00c05a9103609040c059450140da2207070300881200811494004071002040070b008052001902c65005003103c240c0b20b034000e410a50709560002c0041003d02c5e2a0207d20300200541c000a952030032414000840c02507541686030b604540000b4580e040d03988008480d070450904040c2101c0080f11030300000345c0d83c0c0726400010300500b0711102800042c5041c449000c221882840d1507009a0304081103070551540107c0e8110540e5400069006500074155069002e8800c61400311208401d4019000702e92074040013550150416209442c501c0d15401d1008d032440c0224046c1045032082c04100038001400740c001c920013081090b80102c2c4956030b01d90298255004000151405100002004601d10740b0480c0c2e03004150003402c0510300c1508000100b9940e000d4031074002d00b070114019486407907035420442030a07540e5204410 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 222969226 1250 222967976 222968023
    0x40809060c010218030303090615010c080307120f110904020706091209140103230603071e05040e010501030506010506071e060f0f3b030706020406020f06071b05 71
    0x81c6001354403401110780074209001c000e052518000c000c81e801140c20100a15480d19994195214038103850519070510101c00c034140e0001d158074020314450102c903102c07040c4041080c0c1764001581c42218806150b0b51070501d100c1d1203500302005881c21000180d8005132120304034644603005190425004d41000d0440410340b01d940d500030b1401040c1e580d144040c0c0e444c0e0070001f0040d0160b40850840c01c02c0c0010000c260b001c00d001034180d588d0300240040481c0c10b11607a43e001c029500c07810150710915140d8158090106040500690000000043c001c006a600d1a1903207500c40c2e01c10b010386403040354005600014444541c010410031100c00304000900300c024a4004000d00d13141c2d04130b2880a00342898002140380c10300c14120b038010642d1845000c070b2181006040f101400321101d002042a810b120006c0c90000c0002d4880544580d90041e42e660130450064940410020411013a600103420000b840354403000d000000c1400160560010140c0e00e4410f00700900062404400c104079500e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 222970476 1250 222969226 222969247
    0xb040f0207030f030504080901110c10081803070c0e07120203090102070c091806020d02040e16032f070804031a0f0601030903051909030b0f0702010c210504080906 72
    0x1000c126200340c0f150111024100004c1c1d05840b006c541c082c000d403000384500c01d0035502402108544401c141d090303403000241480054001205142100c0c00101500c08108100003e80300400312286688029410009690f84110075607030180542c074002c030040c1d404500da4900905a0702e0425841200a6489103011a0243d000703402110060360400055000000c081051788a409008402c10500b2a039191135521098043d44c00840032a44040c2d0030800024960920400c1d180101d02054043e140c02d042020300909a0b1520410040e8910000352502450a010170944607a148100c581545940460601000c18003a079400508030b60030540c86000c1040f64080d030a4415504140e8007641a110400110200e440e0928004d001c51000c100400800c134007420174010032a40d51605054040e103d65030244608001d8032070904170240141031103400c2d41c0a0107640c1c20307500e082c0341c4044a055241d5034460b43d0b501c201c5a412410380c0d984040307000c6c088103000711031201d5006050b6543e110340655 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 222971726 1250 222970476 222970481
    0x2211204080c011d060d0903091e09050a05130f0201090902040801020d0c0203040614070f0c0b070b01060c02090112030e06040803071a011d09030910120c020a03080a0f0b040f 77
    0x14800b40c0003504007011081000c2d40140041004c0001410b51824001d001b80c41000074004100150107000007014002501d400d450401d0428041c4c000d6255802403528644005440c030140207401d0390380c100010810000600504030f19445d0b0020b07081070310f81601e07000503624a80c098200c8034810380009008a5400d4054000301032200c8819810454080d100c40308a850340140d000c5c10001580100c002a000c0c000000541005401015120003c4115070f4440318042c12550110b5000640421610300f80448292841d0041c0306504041c042c0c85007030f40c005164a4014041c2d0016982e44814080a01d84290a182d56080024003000e58803a00c43c0d90156603600700c1002220400e4079101d007104800c086550040c1211400e80885280781d1030743c4880c1d4420840204194403e00c014090425682c1e208000c032411060140c40380501420003216031010b865480c1e040c00c040d036011107039450001c4e500480d9940e0100f003811001a01003040c550500c0030745400002d413544942001c040009021603503 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 222972976 1250 222971726 222971743
    0x30804050d031b030218030105070801051c05120d0e060c1309140105040b030a0c061e03020a0f0806030a020307032306040503040b130e1603180221120408 68
    0x50301119840e46400400310203686400381d0204042c003880c1000d0094038000c0d0080c100d0607000540148104490038046030848170f08891b8a4001412034004101034240711140200b19481940500d074082d099845090765083d9800f07030f0700030f0034a000441c6a0001c2c0305602c10a80003054030140d80755820055210380b1241c20035402603542c40601100000d000c0380522070303c1c6540d40d0102e402c2400380e00c1d2000b00030040850b5000b076030b0140507030b9100c10300040e803200036040a00019110014842959000c40c1003100c1004901c000b8103104000240855403c0b1401107070254440ca451509540c070b40c0086828141c0404009402d48194072001c410031100f03c0410f00759139150800b1036903540350545055a0346109490203800707600200000e003c0d1194080040c2400744680d1016420140e691705039070104c600440b5081c241480507238280300e10540c1030055020080094001c0c94400b03e550300003030944052603e01c01c22140b600780c0c11048200d028002c404c1312140b003424544d01c0c3c0380d403107040d252990003d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 222974226 1250 222972976 222972983
    0x4030f050d030c0201140c0307050f030a2f160804170f01050f040b340315050102010b0a09050a0b03010e071403070b030f0702010b1c050c2b0809030703030804 70
    0x400180d600c41604c14803030310400d40d181c516591865114065040d205174000f8191504101c002c000000c4104031150045001e07040e0a1000604e48102031621088210720f0150600359915044142040c01e42136010303560180780590b840b07007000580786840c20b4035200d04d07070080840005998403014842400b043c0c040071041014001c1c40641d6907400c1000c0100400c44004200341e0810707000c215443e034041c450480c0240c0c010628074001644480c2809075411104154001a0711041d15000018404041c800140300c01e0000b4017888404400151304140c0a014501e285aa19800191500c0050f0000620800042e001b08106020000403903100c1e8898051405400383e88501040c083c00c00160381000c9a89481106065844281d00075144800180c5a1402c541d210440340b000c5540b11000c0c0c04010101c444000c61803019441d03c542819203100a461240700c61010920f0440b2a0401c800601c1191586590717004506150005241c0260140643c05100340f0707402004268004a445014901 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 222975476 1250 222974226 222974231
    0x9020103110702010504030308100306152909120703021c0c06050a050306040209030114160f030203060303070206070c0909060209122a060708030a0b01180b0a050a0504030f050d03 79
    0x400e01d0003051188500c000090010b10b0800c010004644503013420b54006805842a00c040d0b907032034903054256500d9004032500c0c4501c02030200052203002a503c4400c04010702110014403011620301d00d40c1c0148211a4080c009640700010f002005204042c05181d0050602c8083d41550710400c1c0da0a428501c21541d81410f8103000c101030340100706440880000c1d9460390b203140c0e242c0051001940045500c5a010f41d260191030b00f001c00134401817413140049000c04107000088060060003021840081f0b000e26104009015850300e0100031503c00c180c041e0f4081c3d40d02c10082c50101b89082003540a04603440c90000c0041c01c1000c55001004090300c1190780c02486080d0900550700c0c3c0d4240a491001c0880400e4010061380342e0710595485140c00401841c1014800d803258040b03980115207070341c01f0683d1040d03400403540e0813006580342e010281c011f41c0031950900111840f14071506004105001011601c2c6003018401e404960103940d224510080701140780c90030b030b69540609080280841e0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 222976726 1250 222975476 222975491
    0x5100c090512030a0e0a0b1603080a0903020a121e170601080717060105091507020406080c0a0905090c100e03010b041b0507081b1c02030a09050108100509010909020103 74
    0x207082c0b801c02036004001d0014518109860700c0503201000c0107541c0d40d810107581d20000600401200140050221101c0d00e04044009490000c00c6408002d2100ca806441e100c414804a540041d1021b5003580c405000d07907018541c40001d940584407000783c00c1c4c200002441d000381031075101c41030440340460b03d4a081c6082d03c84c64010f40d03000c0c104540e0040090300c459204540c090074036811981102042c10f01c076150941400105905c014400e40c00c1c0c02c0c00c2000074641c0110f00f041d2207484000c0c00c4200c06444054803c000041740c0340803503c41c5800150302d480c0402c0202d0014041141460002040118045c0803280007800c0d103002103540500c030f54a0025080280d0030240940680b4600c80c10312a02c142943d400f0a031a541c005540c2a5048a01403100c0b603510021280740e0081c3c02c01d940001d10451500e405402c205841c800c0ca64011500180046003030203800000c64019140242080405545e50307014003d07048086611266106441200008617402c0d030b0303401264094000c0e0303070620002 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 222977976 1250 222976726 222976729
    0x6020706090815071211040b070b0108031821190b0703090201021e01060308030f0906070315090b0d02150408010b0f0a0603020a0513030305180906090106050c0a05100c0905 76
    0x109001c1000c095180f03400800102014803422648a82d0b6042400010b804900c400c1840003d81042d0007420704041d00046000c00e03c0290840e050042240200a615104944925a42030006134864500031124521407040b4085003010030195030050208603022617a00c40108482e918081d2810307656100103002090940e0b100b406028400b41c0c044e0014401c21001c0310f00341c1c03000841544e074020a03542e26800071000407502802580206480303000f02a15007000503280741403850140101051520780700803255051003000e6600219030800303c0000e00f003000d000c040364661101c0d0750f00a40c0001160302c1001eaa8404401a009480764480200300038007200043c8240c0b5510060010750080d080003080050b01d01c02c5e00201041c50f01d0b49042420301c01348120414404000350421801318a000c1080001000000400340354101c04943c9520207080800205556200c10702030300007040780001c1c880d015244200400d401582d44a402c940ca041240100c0307070000c3c565400114000f400512002405 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 222979226 1250 222977976 222977983
    0x80a0f0c020901051e1c020109050a0f090203060604080a031710030209180a05030d020c06060f060702150f0a030b130615050c010605090901150f080723030601060207060908 76
    0x140350780900400d0035a42488200045a03041d09009080700100115200c02a01c4403114070701644076903003481841c00d480740300150049406402950140d5070303444041004100c0c1c0010700701110031740c03c401a502e88808000c503c0603c1103800044440c841d00e00614109544808003e8528078500c4c1011995210115205c0c100704841c032000c1c3d4002c2c410701c0400c41000351500d2004d902c0c030600044811a001c19a99a401c40d00004120282940d0200305211400000e120745544683d04071000c1541801c0350000901600842501a009501c0b840c421140c05803000c2c00c84130428012441180c540696844c0140541400d44071f042c0199a0410702c200c6002640c021441901c04607516001c010240850480f0366421080e614002507407900800203441d203c00050301e0188110000110301e0404d0641c502c064000b640d80b201400f8030851004000755100400d02c80306490301e624604404940802804180464001140b5814080e0800010f1090340016180c011607415458144456a4441c619a02c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 222980476 1250 222979226 222979247
    0x70f02030105090105190b1c030908070501181502011e020405031209030d0c1e11010e1219030e060f030106141e1c060f05120105010f0306020f0d09080a0f 68
    0x108183d00c20f603401b412522542004c64075820160840b4074032074901700c0202524241c102c1c11360206160754001e001110742403010f5409804203003006200d050b480f071002d0b080d8407440d11030f1034111820b251088404c07500c00e411441d002d6960740c10035550f55001c0c6085400075485403044502c241310306004010a00c071102c0035070b0340542e4014094002010409000e0300c0581d891081140d02018212809160304000140700d05014001c40c00c4801042000300058800d00c8200c2a170791048440088507001d1740c100058003102c0b072080310b44000100215207006d80c1c00450070300c0082d40c4030307501080444006136100084c5048414590300c00c0c400d502841142d01c0f03640300b142c51b4000130142500058007081c01030350040900d200c0c40000ca103480340b01d00700c141c4212179042e08001000c400390101004185819886001d119519034001c0180d5450040003000d140d1044c8801000e02d0740101f20207045188640941e200514482e400303020820192604025a0740b001c289003020a1400704031892541c890f118042 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 222981726 1250 222980476 222980491
    0x50f0c010201060308040b090a0b030c0301090605010c05070b0c01060518040b060d080d05191401030c0b0a1209020409080408070303120b0d020910050d030806040c050f0d0c03060b070f02030105090105 88
    0x6180904020381901f165002c0e00c501ea4020400c460b00203074070717082c0500851140e018461703415165418800d004007500c00740e0384080c1c100844502c014001c0340c000b140d200c089076a9629095964921503100394003500702c0f94000c2d07a011212080200c500184d10006610071071240c40c0c410380c90741c0e9107410420400c0030702030040e00b00c50341070005110004031980500c2d04440864034109114010303026032400e0740d04000005003d20105401001040307041c4000c00050f11810396200c0c1088003600c002080e9006188110700c0046e181c280700415900d0b02c0e40310207082030b000300101d0b66585c1c44080700c2c0d40e50689448210001440b50303c204241d424030744101000d002004140b074a83d8030b80c540800040c13100c050105942030405c071000003200d9032800041050140f10340c072520b03240c0c6405000c110440d4601221740040c070800304041b1151940e4401214500380c946030002a07075660800e022001480315070071001c450305000520b40f0034407544c0e03460304c000386100720000c2c130656980302d094609072141603440b01c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 222982976 1250 222981726 222981743
    0xf0313050405160e030a0b0a090201021b0d0b13020405010303050a08090a030c0b06130c030c0e030d1e0203070506010b3007030b180106030506011e0f0c030e0d050f0c0102010603 78
    0x90125115680c03921140c140182210001d13086c0b5110904084010303140c100101343d0f2098908110b503014000d0740d1804902140d00b1b80d680360f00764007082e4a120903c20003484081c0500000b00d1172141c1401d03400e003491300640308109079a180c0c503014205900228810b8082240c040008010300c2000400b030184503416940c0c1254403829603201100c3c0403018221507882402020001c42c408250310031901c80702810741d80842d4500c04d040028001c40c0e040003940c1c0c000c1e0006105424000e030003040158801c006c0c14071501128040030302c02c904601030003100400714002c0d800001514060600544140c0314140c040e01c100400c044c200c02c414401d21300c0c859030740074905000105403a0003903004440c4003201a1007824041982030700111510026000740c000f080e0742c3d40074442c0c1540c1c080c0856070003a1840c014407050710120703c405441d01c001040c1440c02c00a6034040030b402c040c821002080140c001030407403400101c1d14501541c4810700d141e030045842c820318030804040c0d071050150008403070700000c14 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 222984226 1250 222982976 222983011
    0x10f030507170a120905040b060306030303150607120201090b0606070b19060f0f0e090a050c06130510080702010c022b03110f070507140108060906030f0f0313050405 73
    0x1500a165400c4245000c2d4000c040d801c0d4040782c6080c0d50700e0218415950f41600060500702000101e0780c68140351401888140200200d58800204894004e95200d5003a10068500000100c0c5881000c10080509603e0020514460b4054108840143c0b240e80d00056555624043c00702c14007540c02c000c0d1034588c4000101d2880c160084044540320040c24000c42c0c039507118842d50f0100130003548980030050350020101305c4580d00002044e0070004035006011000041d44590781c0c0c0f507403502d61103440344400185491304041108005e100070000a400701c500c0e2a40704801921703400c81212070f0400b5500702540b8821251000c2a603590310f421420b03c404107070f000c483c0046c2280c01441150801e243d40c62292025600d002406000d40d158840c84039581c448451405900f4a40c00b6403060034501700110036107155a070080340341940310070b00f40c8082d038a5907107140009162500c2c081da6008503009030901c403041c100c00807004041c0601c9c40002984025611002d000443e50100c03402d44030b03400d00302c00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 222985476 1250 222984226 222984239
    0x180606230609120f031c0507090509041707150e0f03040f062001061e06080601050702220e150105180412030e120408010b2e091a040806010f030507 65
    0xb1660300380c100c810300326a01c4c61283d80d0702900e50340c85800704482d00c00d040000300c0d907090f6413400b449900201c05d1504241a80c9000b000c919603100c0540300506040c1c00d54070b0b54108200700d605641106420059101005118a504c54028007900d41c440610340219024030f22244800000c8800301ca2201503100e003007600d41902124003405000703412181044c40240b210100e40700340503590107411107000340a1807520b064101800c0480310342c4204140182c4004002003030303030080199000d0b140c044c3d070702104c104580c0030341d0120620305c440728820461500300e540700701110004120600061800c94603905903254002c1080c20140c0c544070110072101100003400084880311410203c4440f0308000c10110707041007642d41082c2110a128100100204080018960034040d1210100c0151124103440300b00c00642111808040c000d40f088041e0b10060403915841200b0b00b40c0140030241c0081c40e003000c2c8010000c400d500901c60000f5a00c1240000f180481c2c48250280442e64440c00400c1100d00d01003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 222986726 1250 222985476 222985489
    0x10501021506064810050c03011202011803050d03150f0504090804030f03020a061a03121b01050f01140a080a110103060b0a030e01050a181401180606230609 69
    0x203511604070300d5005410495201c0545113801900800e0102c0c07440c2407900c070800380790442c030842180c203840c10001030201d01040340b0100c0703066488038600681900303200d00060700d200c428044003178480b03400b4402c0001400400705464500480c00d55080c0841081060034020000c16401054423482000a0802c8140303440e81c002545544910000d1781055900d80302c141038120410000d401582021038503604004403403061283c059030301c45c10080e07000000c0c40842d54070040303034248811500001901c441400c50380c80070b101c40525410000c2c4060318100c00003c0c810a001c2c46000c5540c06800d00340300c03c62401400d00ea0680b41410006c1c030140342c02e030f1504e910301d14004041c181419500c80003c00c920801c0341c01000c4000c42914045007403000c20305420708450000301034000a900c2c0551340151540043ca40001540d00918255440005d00c54454010010b1403031484c1c00030f540740c1c1e001c4c0400c01940c0124049510044464113030076045400b030944a0785160341d682c0d101e4401c0084404600e46070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 222987976 1250 222986726 222986767
    0x20714030601120f0f06140a02030103050604030f1e0309051e0a060902060909040f020306010611070b03041419050613020a0504020706200c060903130303050a0e03070e01050102150606 81
    0x5110107180c4e601c55403220b581d100805042504c007252a80c10b00d0301180300d000b528640101d4503040c11031556156840f850f4580b0340103000201001170208980301c959102d00075805205040402100190002070300241c005c2040d80011621070140c01e034000c1d44601c40c1c000c0500c4084030300002d0914101c03a03641d54801010036440407a4070260920540c0244d89402d008144542c0c4107515501e40c44005004051805405a2152040014101c000303070b03100d40049103036412a00c445c200e25407a5207030f0749000810784405a02001c0399108001140c000103010b145610a2140110196203881e112818150303e014011400650440480300d410801d9080c0b55000b0f1111602031140081c8001c541031581844444d10f60041014043c040b51080c05c00b101032010a40100c5260019460000f1041c00b100382085103200150521502003184105e55010301e0a44c0421403000382a05e90003925801e0300c1400403801c1c01106c0c0148900304403440000290708985009e4a401081a4106510f1117240161503651 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 222989226 1250 222987976 222987983
    0x402070305031b040e010b0301061704030e010f0c02042f0315060a1106070908010f020415030903090f0b0a090b03070c060c0c060e030909070215060f0a18050702071403060112 77
    0x1081300140300d01e8401e06060280c4051044140c0e40d5140c9403004018001c0800340f14043d103025400e001c002a005121004081e4081c00c09900300d452516050b1103148a045c00070b9009410180080300c6103502e200e080f207400a602c0e200515204c0c6c043c403100d405001c21920303007070140c2404802d400c007482c10b0b8002cbc040f00c80da2440c0c2007182503160030145003404015510070740880da20341d03003d0215180a0041c100c2c16160704a003181014949000248500f0010343d40074145aa103404010916111b00024006000f4000801000790341e295a0b0214503840203020000040015501140b01009681181c1c007602c0903648040102801791640c90060409409801c14044038090440002d4403030b024024003a0b58000c01346441d1410203007841070300a8020000380440d00008041d402a035040c68220743c021030192400301c040301d4041d004c58155080c540000700720314542c00f005020030801d500194441e090903030a460070241e07109a082c8000030050603141d40f6401041c014840701c0707180a042e0b9150b600 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 222990476 1250 222989226 222989281
    0x402030c0405125506231f120b0a0b010801030b040615180b031b01050d02031302060c030304020307240509150c060f01061b15090203030c0a020f040207030503 70
    0x504130404040c50700142504880c1c40c00c010300f0a000c4584100c424001c5980055031401d8202d246a0805074401014000040b8201070384444041d074600030000509800c003841d9030500380509040c500e54000700c402000705400c00e4a00011035100d490041d0481e80e010781000740c1030f1500d035a800c001d485626401000301d05c020f0300c0004c808040da14802c0405c220604001581140d10051509000400c0c150300c03880701b00311043c06030b166400400c0f950344440d005001030b12a1200020b460601d0404400654004004942070700080004801503002c1c510032812580d6071741d82d40e0400c120103201034140366418000b6284100955001d8402001644001041c0b090703c070500c81c6003800305800c984440511644000e040160b5820034003403460242406041100b0758642d88000c100e0140350010300145507900700b1004140d0030000c1d40207824810743c020300307498640326520452962003000348001e174412150081007000c41e00f80751080340d69040c1c1560704c1c0e52a641e43c0f00052002c5001c0c01d20300c010b140302d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 222991726 1250 222990476 222990583
    0x204020d0b10051e0901020303041e0b0403030516140d0f0603020a03050109030f05040b1b150411151305210102070804050a05060a020d030b0f0402030c040512 70
    0x1591a4184a142c110710b4603101e403156585500e101d0003000030802802030550810030303101c1c40d1f13030000705503544281d0224124820700d0034007403103620711b0451600c024840d04802007031008250300b60300464862401e40c1d10282400490460481e400948504100003507642040b80b0702c1c050681c3d4000400d96144100702260565a0b940812921401a801510301da55505000000c04d075104028804264540ca80340341441e041c000300383c05900c21404000484181c03400d10b030b0400e00c400d001601d1684230658503942c03a45002d08103048a503685245961042c0c202d0401d03504400e1442c41a511500030400f0803036612414442440002400d0a1240c44901c003400d01d10000b0346001d0004240c00c1c1d200c0e0a50380c1e01d8900d45030030f10081548507088284501000e011400207a640080c3d9810f11064915000c45e0a00c020004500801e0b5118034040d0858000810420102c3c1d841c2d000304111801502d001c7c5901002c01d6806071654140c0e6000080c0c7d00110b8484840d4202c800408400d5800c841d00308200038 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 222992976 1250 222991726 222991729
    0x1903060506040917070615060827100605011e0507080706090b07020c010315120b0a231e01030b0a02030a020f030114010f2a050c04050f04060b0402070b040204020d0b 73
    0x2c092035800f00c03000b5040085c00d081001403d01542c031000c800c141c40303030b03480d079040a20180c581e5000034901c0d0114600020820346000c0080d50288031200c40d5000d07144512901880c40c0060710041c041c103408a040c0704902c2c01b10801c0e40082558a080d903560310340c1400c4065440c2c5410382d201325030640b4070b103842d0380703048001c036141206040c0211155002010394450000024050340d01c1c040603401140c0c40103e0800101d20305800b00c40760a680b1807005035807070362007100c04030081c800c4442042c201003500c291110000d0f5600011740c05901c2c001968054410100c0703441c1c541c3c05003404020f049030150000700b40303e1001394010b50b800000300c5c0300160030100340b0704241c10590002da12140f072600d0704507901c001030350308001c50b2a041186403825101201d80c83d560304180c4054803d524981c0300c241c501003030a20100340860000100010000d10860800242c020401e4200b9217050741c0051070b00ca00341e505072401e4400c07a40417591001910b03945565540030000250170404001040311b846545c0c00256 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 222994226 1250 222992976 222992993
    0xc01200303010b030103050105060d0f060506030a0c06050a1e050a051e0d020304020f090c0414010203120103050312091603060b040f06060207090c03020405093702071119030605060409 81
    0x707040c0f110310560b102d40c50b5050690035220042e24180c0035846801c15140490b5002480d80001034214030042020707101c1101082c60075002d1600a4038620208601240300c960020040100200c145d480024450a0062011310900304800f030001240c01000107481e507034090005030506809000004020784a41540801558000f03031039458642d600004200444c50101c1d081c45050100380c418441c140f500f400400c80c41c0c45a030007840d460141d111030010b1168801c100310340c040c00d1402107405055030741385411580c0b6046904d1041c070032140c250002d445280d0009002075005d141014800c002403031502e035038004201400c040e5030002c0d154130f01c0d020030010600030140206080e500601d15180303421180400c48a4040404040500410003000079130f5480040c2500100e9035018035400461428845295901c001040b1592030320700342c42d11010001e107901603e49035002c0c01c20241c1031a400b07020011000740030b80a502e5190442d081c207001080c1c05620850b4003204c043d10014200c0702c3c0e500e5101a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 222995476 1250 222994226 222994229
    0x80c010603050a0c12030e0618060d020304060b01021606030f09060e0c1903020609060a031803030c1707020d0309020a0b0d2901051e070f0b040212070501020c0120030301 75
    0x80d190b011009800070800c1d4034038030340005d00000303028040300307866558024040c2c00c0e1112101d119000201d09040302e020544aa50413241000b003415a82751a84480a00030b5002101e0a841403441c00d220f0001950020a48044000d40300b00d8120440d820844143c00030702103460020359a580e10368681001803a5485811219840b1a0040c00b0726680c440c00c01a2580c0340031080130f28020f000f00100011703100c1034152218100c0c200c0c0c1150700d6000b5098110300501e01d00d196042e02c414503144250074580c241e880f8800c6103a240e902d900ca4403401003030030102a00309070703104001a800041054450303407103940030b404d00e14030003090400b01c0c41c0d81e40381c0c41c9459042100312840301580c2d0030004611520390f06480c000800e20016010580741001e00280a0b4040d180301030700d10590721910014411108070484421552140c89000c009000341880c05034506c1c211022801510500c41c0d01c00c11000c006480400c45505034010101c2d001408011500001c0003c6480c48504d5286c60f24000008107001650 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 222996726 1250 222995476 222995483
    0x603120305042109060804051908040f050d03082a0408010b01080a0b090601051303020a0b070605070201060317130902040e1b030f0a1a03120a0905090609060d080c010603 75
    0xd07850a15050868a0303201c0c1c078040a032260308480c1c0707080806400030080300455006051148050781d490404500704006c80e640003020f007021400ea10200090700e40a0003d4440c0d03000c015842c1034941c4d0038084906003601015020a1080002401030918805041c440619070b410803030400342c03140d4903041c1e6500315401007a29651290384580003547e01864117503000c0390041c001c0c0000034040010443c00d89010308080c0c100140029440603a00070f01220100031a80640005001985d40402700c50075040500b04940203402c2601080050388140510825a034001204c1041681d0205003c811a80325035489151140324040c0007405031811720141000f44000007041d0428601401d403020100184020407034070074800d00512905910ba10350940e8000b010000c0011003000d1100b06024480b184141c640e0b0500c00c0b0001150118150409808550466141d05591a03203a07010024000030884600340c0014080000690521b003600114450301e00808060b440c0131040308070982910a15007094 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 222997976 1250 222996726 222996731
    0xa090b010e250801470f2d031501110f0709141311010f1101020c010b0103150b1905090a0b0705061005130b030102040b04030f05070807050904060c020106031203 71
    0x411081200144a485c00b0080c0401d04c251003640307440841c080100440c1d03612102c0c8400f8441d2402c041e42408580202c020b0403280760300d6040c01100c00c4818451a00b0314003d031a4840420386520f58030310152401110303c1800005440d003050700449018940b45c4902034035215003803490010403028070902010700300221000c60044030007420301549003005009625410718506d071800c08204020001900101c0034a000c03441c0384948442182c401490301071900d6a54800500c101c00d4420540c04000151001c2e00c0601404002900d9100c00040d10f00c21800001010080c2c1c4901c07802c5284403680c04a036a0928508190b050030100d851403500c1d8000c0350503000005840310038080100485544145a04c403028081402d101c0410070a000313114110001b10340f502c50302c240c83d5400390141c0b00981000d0110300d454650301c0c1002d00318408070800c1500c483c0102e003400301d03850802042d10810b0340d801404c4001c0a4481c2d9a8081c010031b002d100030021035688980c0400000c141d02401ca04003c0160b801 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 222999226 1250 222997976 222997979
    0x30b0402070c0906062d05091206180d05040306020904020d05070503040b09010204030309030f020d05010507120e06040203190f020306070e0f010e01021c0302091011060a090b010e250801 82
    0x7007402ca0351399412074410301c200040c4114645400d03000d251440034101d0207200ca401d90742c44081c0c07100d02440c80995840b04044008048400300019900e1145980900010021040c1910340e030700c50304440c0da0040090f40c100f0042c0003041c03150f0020a40240094001841c203110380c0f9080c000c8807816130345c041c0050000000c0c8010301802c9040d0300c1d008400c0302c000310700c1c01d450b41d03a0107054980e1511008050b10b00c001c00d40b4085d566540311940e009a00400240b1452620b95801455024517040041002e40790116000e440740d0300003100c43c440c80d8054010b214264800100d2090340341e240f1070881d00210441c61030303070060301c040c00040d004902a07100d14800a0380340d801c00450860404103e41005040d080d451000da034005000000000d0714200d1030101c12034544e08801070711846104640000c0424040d202480d80904021056a0305070240c40c1243c9464424001b81c4a14000203401114880c0050004801e03038011507800c400748401054155000c9100700e41c8084560300c01c0000308094400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 223000476 1250 222999226 222999239
    0xc08060405071d0115020102130816060306081207020a03050703080909010504090c210c030b011707060203090105090a0905040f020f04090503070809040b060c030a02120301061e030b0402070c 84
    0x39803000d000e640303c1d01040d148010301e01c5042200148245e2260000301040b40515a00130f5040302d402a510741001c040300c50b1211440341d40d0b806203520b44070150302400400244940310384a00400c0e0b40550000e0244001030041002043e0400c1c40d05031b034401c141030400400101e00704520b03001103101d92401510f83c15000104200008160301c1140282c2c2048001d500046401c8440c00548012030080785071281c048000307150440d20f94070010010b0f5034649001c418001002c8829040b80c4c9031403818841454051507046c0c9411040c407442c805a0310a2100702da283d030041d0003a08010b540500901ca4460b5034540300c40a603801900c043d14411300340311500066007840c285901d1000c4e8192403d000300c4200703580700b6130350780309440340a00b0312100450b4202c4540d076190003080750032400804003502c40710580c5009403654001004407000d407007960302c0303241082c20103810390741215080d46411030301c2035a908455032203810759414041016035449044529030342d5480074054a50041c020044154141345 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 223001726 1250 223000476 223000483
    0x1502070f0603180f150207030806040506121e010f050708042109060819020703050a020705030604020d03110c101808060114121c0804120f0815030a0c08060405 70
    0x800075010903003400c1440e0000120101140c0c0403590000000c10b04441c40d061403205000d0542201280500000380c0205042d03104041a014441c110b9041141780c80300f00820120300780103408031919402942410000180745e002210160380300c1d40000c25140080f40001c8111801140d81e070000c1030b80801030105100c0c0d03c0d4403001004da18625180c2e001000c1490240c0042440e1080804110703086000032041c03150100b401e81000981c1800b1364030f40d03885180240103900060b0880f001440390400008081ca400250140542c0e0042c01d054403000258034200c0f064136012088081c0c5101e0a04240150346600e0100c07c104102541c48200310701da2400c20b000d2030025648844100e42c0030710018402601c684110f40741c0705500722a00e0400a0390b1740c40c9182015035021801d041103034011940d242154105211921661240940f503484050285042d203649000b943c0000c0000e200d8800107100c01c0300d09900458900c0014200c840f0304621f076480c1c00305403619421a8020360040814001000000c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 223002976 1250 223001726 223001729
    0x70f03600c05040b0a0909020f091c081c02072103150509070f110d080412172214070303020712050312040c030b100305070918060903091502070f 64
    0x480074030034201c0014005002d0f000320300031054030450000c1c51000240c0503001c40801040d10344070030b6403180944407601347d2513001507120501851340129440c5117001040c401a950907030082405040603011032a551183c0c4984907890662076080184001040b00c440d1101d084c4407214801c02031341c14a1810080540f41002080100036843d400300340491764074402100e510860910b0005405407500c0000c8800e1003d60300d40c15110301907a1030b411280e03a031202c2c280307100f5401030156039460b12000d0030403500300941d41c0f240035950b9100d2000c036482c11000504c0b0542d055900c00300d80340074030948c3c40c0d0f101c144401ca8100d100550029004004058040c00018002c04403868680b501e10415120907480340f040e0003070303001c00020080005081003003840d021405103410001401a518000d409031440d040f80380000c1ea1548511500050089070900515012000b594030119000d6415030318a80079003011007084007405413480000c21407100c03818401103540380a030b00a1001c06c1c0741c050708400e1010300303 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 223004226 1250 223002976 223003163
    0x61a0f190b0f090339090103021512010b090a05010504080d140d06090b120106030816031e0c020f102a06050403020303010e100506030106050912031902070f03 70
    0x19403217901d02d40e641320a101030442e03030183c07182a0250003150b010460341c4108141d081543c0040310021881000c0e43e070203480c0100050f00d10380c135807580f00d40040d1068002d81c030a50207254001c0310407100661040d00d000c07062079422040a4148645014241c0c15229240c024490440d60b940c904a101d20300b001c030455440d104039008001e587d080d92240e803820710075810601401118101014105440340740e032210300e81855001c4031400d10f540c1034001c2c9445100801640b00303840f1044030a81600d4004031124800c0700c1501d40800140710040b10360a02600c40000401140400d01a02d02060150040394811803182d40070350341d2036062040c1a00b8901025082c80011481030748140440d86600c1d0450381510072900305a0f481c2c8001000041d64108a8100c0d00a0703400049001742e030024950801000d2030103039409556405c1c2d241c40300c020000704284009440710b40070623192005c00061414408000b0121007401c01e41e201d40821401c004a04980c68202e02c0301c0f94100900c89200907281001c02d40603 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 223005476 1250 223004226 223004323
    0xd140c0c03070b13050d090501030f0b06041a0c06010e0103120801030201020d0503041b060305010f0b0c070608071209050c0906040203040209040209060607061a0f190b0f0903 77
    0x1105000c5540e2400b0760a4024102c500711000b0454148116a00b9a502544401110285060004d000b000380250b48503960100742403640c4003445240d18040c4495120001d030800b810030346815000c10060066052283c1101810440303288810b2090052501030080003c81d81855407640c58055400490220a2003c020f1400011f2005030781c003144000c0c2e01c110502d016a141e41301c904112103120001010221210181500000c01d550141c101c40d040742d1001d4407030b108440e611600d0044038031800c00103545680014009009141c080c40d090b42d040b909925058001e802c080174131104541e41040e060b2081d500510980c4400d2405003003190b4040d1041d28290b066090940c04205003a4001e00000d200e1441d820010301c45881c0d14041e100074070342081c42400004000d0507402c00001c4502c16245c05148220846221030600504c001e061100032140c2890051402c030b0b00c01110f4000e4280e031125950200300c046000c0c4d0342040200c00c032640a80b50f81030171031000c0d850b1004002803100001c003d8207 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 223006726 1250 223005476 223005487
    0x6100608010e2a030a0b03010e01140a0f020906181504060e1003020f0d09020f030a0206040311010e1206070329010e0d1a01082109060a0c0204020d140c 67
    0x14880740c2e41180c5403010301d9540100020443d030003401c5200030f0380404100482001045034140c0c00145414000754000c00410180f140514280c0d8091000001c6204000c0b0105106552591003840304400f0600010f0070403180d8400141c51380e1010320460b03102444c603000d4025600d80303443e1610b070560019003032030b282614103400a4550480e0010706441042040b00f030719030043c080d03011655400b0b550080995521240482c0780b0003072010f40b1042e4018209020051401d0900103810103480b1b030000e124508261071031759030082c001c10350b600444c104148500440e81d01d86a203000300040c8859000a00034a2402c407500400f250084404500307840d9099050303005031054050b02d500440802c5c6000c0740740410380320118254400701d071001014450b0455010b80840c00c68070810703060700d49100681c0c590b181e50034460808112041c940c11140c0400300300704401c502d4008010b06620f43d960420003101c41d401e40000d0200c0c2c1101601004241c1ca0b4190b410003051130b82002030748640c04452583c1800c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 223007976 1250 223006726 223006739
    0x31e050105010b1c0c0909062705010303140c070506162f010e0105070b04050715020607050307031a0406030602030603121903021308061501080f040b0f0a090c080610060801 76
    0x10400c00481100940d45c44130200c03d454070610701403004e0100f00c4014070005c0c0e594216800001920700c2004103210780c034402007140b1311440c09464100da0300b523620700095010032404e410295015104248451190a40c0052682c80f1200900100c0c03149078125280544107003460f020341c1a0409412982e0302410300b00c45010021885031145541c001e283ca0491460084010b81e0a8802d5043c040c00100381003040104020000400f10156410586201241000e042e0305903603410054030b02001051003440040c901c40d2107a44160002e80e8402c80e100b51117511180032400b241e842e40c10a03200381d900041042900c0c01d0400c01c1c0c10384101d070411224508031196144040782020315200700704240c0c000850041c1e0200e55911704d005041000d0564405080541c40344015048010a00740459645000101c3c40032040c0001c52096410001088095541d01ca8840700c031200205031100459960008401041c0950700ca423015001c0c001c01403080e804e080148440300e26456021030100451350b001070005 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 223009226 1250 223007976 223008007
    0x3280e01230d021201080109050c0109060c0f03030b190303020c01020c0105070b181501060f0c0f030c021203120103020f03060103150209030102071401150f05010906050f04031e050105010b 83
    0x4070440040454451010b2502c1001030302c501643d060b44000800008110800190700c100d1800e84900201c2d01c280220400654107114540b00701d60120b03048a6208020810364603800030084c1c40382c640024001c0e9154002500703506036902c5005d05981c0d03c401441056010489002d0280090005040641a04000901a10900300d005080c00d080f04041034210100c40d01104020500c042a1001c0081c80085032821080074480d07000002c00c036a0450070318501409540b13213000c0d00440148e162064949049e00e0071040844226000051858003030301104c802e0016200c41c580301c2000000ca94954010000040d0146031594843d4000720700420020340740500c11002c06a000d400546c0381c604010000e07009000d07440e0050042c03507100501c18600705042d804000056801000c04800d1905c03072441c810100d640c3d0180501041d5460300600510f40200c003c0c20929a801e040c2915240d220f5a8180c1d1030b03050f04044503120307151413994004001c401c0c050301e0302601815449a05185511290035035 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 223010476 1250 223009226 223009277
    0x608030412031b0804181107080405091506031305070e100e04080f1308010e070503030a0c020604051302030f0c0a020a02060c0109050d0207080115151103280e01 71
    0x784098202c05080100301203c02a00941d0415001610f49070303100030101c1c0603800d13416140161403a10702c0c0003142220324800c2d10002500403140c82e00382030414080c84000180980081c0220744041c2c00888a503452000442c4269040c440c0b0301c11000007031030124030b801d05981000c03140e002d60034108080c0091600d4040100c03040030281820684079410300210380d21942c03810400aa10004d154444840c601c0314100c02c80307408000800a52184200c01074603200e460180640c140c10800440d00e80302d10aa600e964103500040200385403a0743c3d100050144011844100381076078010040008841c07000b503070a90f100824015991500304d240000945800ca80d1000a100c0c140120340c4040902096015046003035001086401c4403202c4c18021b5682c18040c885c1c0b003140c0d0709160903010b031425844507000449000b07030b03040d400d4240c058a0503200e05003072104003003051006024200704045508124044200c000e5090728000100410060200d110b00354514103001040c58107402900400c0762011 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 223011726 1250 223010476 223010483
    0x307081f110408010e03071a09060406020f25032601030201033206120106030c0504022107051809010312081906030c180b01080703021e030711010608030412 69
    0x1988440c0e22210410034000d0b900111401d618100317141c00320240000080501901a819100340c06001d10552020982d084440a0343c9030080400302d40060b1954024000d8080c500302001d003080007401d02c130000000000d00c6500d02101501055042c50b4000c0c0c1200c07408582c03049221700003110310780b80300c01554040c0700084c1010744e500031007021581851140384198402c2012070b408180205140c58000c003013640e00c0c0d4450140441d8003c2a040d0510078841100d80c0f20100b014035034540000c2100a4000c03100003004240010000e4105080d402040d03885208151181c42c0c03222021688d0102440c10034045038021007510b001030001c503800f1121031050700420300d0040307a280d4502034105510208030f04514085820110040100254203541c0025121b0075444100e14030090310ba02e00a41d42c0d00284640407800c40d002082000e40709030020009030304461445c6103505001e80c003081d00c40e4411a0b2030301c00510b16520041807500280607410080600c44010360902d428403010318482c40340010001c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 223012976 1250 223011726 223011731
    0x804060c0303090f050102090a0801021603030504020a0816090c0f0912020a0e15011403060f090c0c030a0509040b030c030705040b030f0303070c050f060f27010c0203090307081f 78
    0xe1040611a03041581030b664000f0300801c15800c54a0305602075080b942104d0f214802c0c000002c5030301c441c140b0a903400722001c0168000d24030700c59241600200030140099130000d005003c04900c04504000382c03200c0b01140f0b401c640101e0700e0308403000c2c100c0341416203c00c101f041c80c859025440c3d6102c504a401d0301c28803091549600c0d16440002e803511140d6001c4c42040110000700518129003440741405100280c841d9100c3c4c0c14025030071400791000300c80190f808024980e440c45c0c6810854121039010342107440c030610f00781d208045545181c2000c1c00303100c0050b90000d000341d91401c140c000e0034168142600100005142e80b000680c98151a00503503004a9440b085040d9696007001038554039034240702a6070740d81c101200000c0982ca120042616a80f00714034008041640006031548100701940045205854851030504101d080c8144000c4606c81103145544100081c03143c41040f07a031540065656540007401d050501403e5803103c015908402d500a03400091503a641319840e0700103000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 223014226 1250 223012976 223012997
    0x126060c0d15080303060112020306030613020d15050414060f0a0209011b0c0303140a050906030a0e060906010906230f041424060304050c0d05070b0a02030409110304080406 76
    0x6100424481500000702c0c1c02d0194006003240700800214007460003070781d03142d00d001900c514070b5040e84815a00f07160186e0118000880d28482c0b50080c2405503c0100740302074170042a124a00c89010b1340c00004402640ca00c148020419028170a150506010003c0c08446c9000c400920310040001c044800d0141c0000f10400c01c0c3e031081c43d0800303030105000c0c4030300a00500c509041c0c3c1c104080340412000304401c000322908064140064445c04040c69807101d203040840300a000007500040c00d90a201034896640c41c11141090007840c4c880e00c0d6400040c040d640c50301d500c007400d0b10340a91104103545011030b5120303070010644c000d003805c41c04182d0f402d0050340301d0080810010711000c66039003000c140700c2082c803c2038030701003407110185096030b2060685808803100304412844180c500a0455220b2503580c42a0b050a40c101803c1c9030249081d01d005030780d10150001560320034020305005800c0014280400a014810404c1c03074010b10b070384c00b0f0079440c10b40d44226141c460350249030240158580b9 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 223015476 1250 223014226 223014247
    0x60601080114012f0a030305101a18150d0c030b04060602070b0306060c0f0a03111f09060902060409140a1104030308180a030306060e090c0d2a05030126060c 69
    0x102d201321090088119004440d40d400d00500074001900e103000c3c10b40712018001804107041c2c11540e0b400400c400b0040ca0881852051807242e00310188440e00306c1c40707400c5044460400200980b030f41514824002c10707003090b0100020f003180e840d0340405100d986010000c0c80403541c001915410f5440004c4603a80d80e4807081d000840501800502d80080e10880203000618403000c1005000f0511a81300d918803007140044407070b00c540e04500c410501005081c0840304290141e00400300080c01140c000039103070003d030041000c82d0f03c550820404207498542d216400c849241040d90300007503102e4108451081d03140c094501e84164031001c2e0400404001255205c4150012504285080d8040310459441490040e0107026184610b02c08980700d060308618908042020314411003205458501e48007445103800014841c2c4480001c020644080c420f90506510405000455258035010b84942c540664003031603c0240c4000c1c883e00c0c1d0fa41d001d010b01441c0c001001c0e85c1040311045410f88441041c0c5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 223016726 1250 223015476 223015547
    0xc09150e041e0e120a1b02010c0b0916050604031106030613090c090c1707050a020703020a03062a020316030c02062b0e07031203150806060108011401 66
    0x40580003520348000a0486811080c0c2c400241d074600d00c0d095444c600003902d0301c00500d002d900c4644021502c0c0c5020412001004074074000a584141401c1000001e2502e50943c6e0b80c004442c4e514955000212400300100b0360224a002071804a400300d2809066583d51400142817a01180c054040803002c184265909140313908050304140c8108500000c0341091010303442075104100c02c480c5060a100c40c0d09100e040d800d1814001385490500325150050100c4541d03000c0c401350421802030107004001039848614020080d8012080410900b149100ea079103909003100c51002804080401030303c900b40c010003075401d01400e00508040f50012070034142c49a00030428001c0d0301441c00a009910240c05a81c0c2c41c00940320740344074010940260500e10125114504c540480d5840000d01700002800d0b214808180d00d81c40c940803c0c00500d6846034000408990840c4070706402c90010402503591114110b0700400c01c081c1c4440720070b410340e070000c3c0c50803407001d4101440002c9240b400301c2140045 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 223017976 1250 223016726 223016741
    0x907050c150a0f05160c05010f110910050c072304020304030521060105120c090a080f0f0a080f070f080c0d08010806010303020d1d03150106030c09150e04 68
    0x34800d0352aa011140c0c510601500112150009149080e95006007405036201d0705201c0d03d0102030041d5801a040d0741611030407003c580c215a5907480c4e4010b0701c002a420b020b0001c0607015031030280e860720b03d600c00300840f10403100080310402c9420701101c2d230808800240082198508007006a02145a592084a260003101e034250058000002d00080640c002c0041c200902041400d2501c2c020000308205c44280503909980002d0081c04050009410516229008244040201d01d408a180c000c21210006940114220b80241c124a806454140f20f100c50003a40b040c0036180c5c00c84265512190b5004004441c0320140c0c000c40d131082080282d40c03c11201c40e030040d01032030300d03543c0c1c0c6001c0d5980c07041a0164000003070003000000035914800134840381a02d505801600c00b00b150300c002141c400c5e00a0000c400f02c0c030442990958191014402052550004054030500e581840c002500b9550b941900904015100e00c00308070024207010005d048450500d41502c05a02c8400000d014181c035 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 223019226 1250 223017976 223017997
    0x2301060e010b030109150f060e0f120a0506010807050604030303090303020717211504050915010902070308060607050d08060609040f020d050117070e07200105070801050a030c05090705 81
    0x210340002c190340781c055010714100c0d0400d00e002d220001040c01101c2c1204040c0c80340328545280050144481070042c03100c41e8403244050b15070720441c0c189c0c80006450107066200003170241c02c0400320b4414403006003c05805402644010a0a80c0c94900850890720541c8005030815542d001d140b0105842a01190100380e003045402524001d06100070340c441c1d2000d800381080d03540b505502100c0e02415102d0510427000140304081c511600c0c0c1c01c0c00040c04000348155100c0c018002042c8241c0d06803142c0601820f440d110060f1a10034074a8081d21006014049600c50041448130380005003001502c5c020340c0c180c2d468403007070603110701001c5850760080010082e4070a0074803088408150403035018242c0600341c40c10a20541c2d0317a83c4ca210710191085100c090294225040c01c2c0030b5043d501e0901a000070b0580f0f4603c07105040f03404008640072041c003920425944a901b030040c02c40c2d200c2d6691b40034100840701a0701e8a440d654034003681502e9881060b0140c2044000509101d0161080d100400d03107 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 223020476 1250 223019226 223019249
    0x61b0609061416140f07020a050a060512061c170426010605010c02150903070b0a050909010b0306060403060b0f0a1203081b030103030806040f020430230106 69
    0xc0442070300d40c80502c1111903120740c2818202500c1070b1441080346074074401509a04924051005000001640c030945042c0d800074505000024251606c6803448028040c582e1010380b687e04554041500510140072948101c202c0d442681c840f850b11040356103209c0d072190044d003083d500144010103e01940e800100f209622482103030300c100d80c00c00c06444202076040200324003500c3e40c00550b4054112100a13421203c0da21450703110700040001440314030030042c00c8800c1c5580d500c5402545074000480f80001840106440ca01c7d42816015240901845072000e0304624166001c11520b005a11003e00101d4980c80703881c0d01d5032104840b4040102d8064071003d0b503561645021881d0100400f000ca0004484400081400c401088111545c600144100d031940c1d1035620210354802c0302603d5150300030f59036022281245850301c01032009100e0319a14007c1e10700c04010000d000403030101104130606448078041e0020b4114407250800c02c80311042d003401d41801e034140c180103000c42d8104a404c45c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 223021582 1106 223020476 223020491
    0x903080c030f07150c140d02090418061407030c0c02090a1d100e060c0d09030507060207110f0f010e101106040f06050709061b060906 59
    0x480d10000c0303908000080740041c1190307105600c100c030454069001d1040d8040140181c2e0034117942401d20310318451300b46003505002e03c5104c490100c500d41c0080c1030010f41d51030754000070780d0310310081d40303c498400b013440c00c00d0040c2241207614906211410001d480188139004049407001c0d982d5594400c0d075516400d01c03aa0901c0507151495407500c80400305001c3c01110011100181e008005162001c1b40c0c02c3c1031021901c032031034800000d4000c41c04100341e028035802281c40181728246c0000307807050541400c4072280030310800284103070300014011013800700b82c0f01d48800c0b42004480198031a2020b03401c005070450031404440c00f1451902501590345848811180b90341140d052459050303401d62446030401400b140c04031001da80300c1364410103000d218410140e22141d9402e0100146003802c10140c40e1081030b02d21300d2032000d0b21841000411400c1c3d00b1070203186500c030f44240700c400c = true := by decide +kernel

theorem cover : BRFrame.Cov 222841726 223021582 := by
  have h0 := BRFrame.cov_init 222841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 222841726 ≤ n) (h2 : n < 223021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
