-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0359
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:24:15.942474+00:00
-- url     : https://prove2.me/submissions/18982c01-01cd-4dff-827e-d6423de8be7e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 64388492 ≤ n < 64568348 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 64389742 1250 64388492 64388509
    0x40b090f030c0d0b040f060c1808070501050f0a0e03030a180909050c060a1803031707180506070f081303030908010c050301062006010312020c011e0c1b090f0506 71
    0x100050283e502d24141130742d64a07041400188221640e80c5a040c07410701103165445003040c007071a6601d41c00303003510265401121109160b4420a03040d40070050501c01a41c2c0038058410074511081107a440b80c0500c801034900b04501300c0801c1e014400401c507554401e51081c01c0c10342a400a82c0c03a103a11302d407640c0300f8030190740000c1001341880e0f1001091680c0340c20210700503c2c0e20082403402000b4000c4620282040b0300341035000350b00080c0c05c0700b5992080d20b007c010060300304001d41404040e8040c01300c41c46643d08070500c652031003203a000c1000d6040c881e5031348030141550392081c019680e40706881c900341c5010449010903000207900d41400f00b0014014422404a41e12984a4a0a60f80f90480c00c54618213002041d486010817180c441d0a81c0d0300411419007c0d61044115940c84a8001c10003807400150f050000e04204000e4800310ba80f80084103840c007032055a1804040308030b02800c100044485184004e8030604110000203006105603120203521846984140220f850711000c010351003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 64390992 1250 64389742 64389763
    0xa0b0705070308090d060212041a040f0b070918020c0d080411060306040b0409030903060b0609150912030a030603020a05010e1c02040f15030219180203071202040b090f03 75
    0x1d91240c103051000c141c014000d80181d050040940290304180d40e2600b0581e0480c0d59025031142c5a4070900041103195003032042007600285120f0042c2c80d05031103400c201c031030b51031002d0030314001000890821031081c01840050710074408110f02494500c413001000750310025080d43c8038011043e071a15002d1244801900468004009108240c501d01c2040301030751020b04400d51055540a551009032564001c0c2c2d80380c10b0103038890010030b03499414610140c5111980c218821101000740421903503a98080c0c2800e45090b03a80c103611100000c0104002458408110b0703220700c8080b49921010b0740c182c121030107480c804c0c0c40c01c41d14035139901e0064440011200080d50300c550150900f42907c40116903100c455400100040368050044402e48100e0307444000c29600101e601c40c043c4158101089036080090041810444880c0341010001e0b50020003962074070b41b03680001c0404c0140d84038190340301e200648a40115991580d500a551155000f00c1c80603000305100002c000e078900c1c0c04503922640 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 64392242 1250 64390992 64391003
    0xa0f06020a031119081c05060102150912040305030a140f040302061303080d02120105030a0f02100c060204180c0306051021051812180f01121103060a0b07 68
    0x912031942c0503640440005400c00e824451110365050640c0d41020384071005004070740256884000384140501c0c15035841c0c250a00a0400e0144555a41e0010300348440061800e8103c10315280c0c1c100140c01d0000030110301030310400115011040c0000400100000500354a0300501440c0f114002103007801207d141c03803409a414081000503040c2200145020300000d041d030b48000303482c0d5440100503084040c2000070103038040380d504014280c118000d030250508500502c0d41511a54520003035019080300280181650045480980d02950061009a070321540954489488510351048106049892407000307082c451141c3d1490300078801e09040c0ca00213402c418044050305801e4501d07a0400c10748404840844a00418645452040c0c50081d0642c0b02c04040310b0103c1c0c600149801024030004581c0c8504015220b01c00021510002c02e000c0183c400c3c0c181da01c51070300162a0b81c400303040a82e40f960b0500101d0b091070060b10b00294468142201d03c0e552840d2a401c61400e94000c01600410 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 64393492 1250 64392242 64392253
    0xc03090628020a050903010606120b0303031027020a0f08010509130308070e06040b13060503010e01060804080d0e0105010303020f03040b0909130c03050307020405130312050a06080703110a0f0602 86
    0x80014507400612424110713044c89450f150000700800d085440d41e070300c602c0001d20181c0c03415040c412140184c1d034019004400443c151305041c1050048240c0700e20170303607610910380c00c0c03003802c4407800401d01700d802e180e048021500c4507640c1c3c0014100804d0034a20f0800121713544004500d900d841440d031405607000c2c1582011243e001c3d40e0a4802e01005080042400f5042c2d48490f51591103000a102400410192030b44540c40d140c0c00820f01c1e050781d0490f105220044c00140290507244910b1411111146130840c030540b21030804404600c6501404081c035424082c8034044034605400040c120781c071a40c00c8400c50400b980f0300d0782c3c0ba80643e00605045030410408404640b0341142c905030070a00d0441c80507010009a034629032222510f91045400741c001081c00020b5140910455601600394458011031240f2580d004000b0101010242078080d5990302091050400303501100c0540300c03800460308810f460b400c01603e0240c1320030b070380391084250701000301c7c05616407a0010111001c0750018034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 64394742 1250 64393492 64393561
    0x2030106053406021810050a05070303020403020a0905040c09020c0d031a101101050c07080306040213030501020333011b030c050d1d01030b031002070c0b030c030906 73
    0x540b03640c5041c1d0440880c40c1a07403034100b48500d116001c0c0c08554400c44006982d4240c0d808100060300f190001c45208500581d0382908031504101181d001380032a2909030703650f010500e0700758000d0281e031300f01030f402810301c0c8804164008039030301450045001c1c0c01c85000301662442980141d10800c107428025410508141c260030780203812840747c05c81008030140d0300f5148840030403030080091400c10005600c2100c5c4c803001e1074080c403a4039088149003100c180b40802640341d0102512028010b24080d45e8001070b0780c1164403404c04020051940040255500d080c54010916181c407a45403040d46a42d4200c800380c00030164a801d90205041030715200c04503c1a02c440c003044003102c1c07a0550600c4190b0700c914001410912400d1000301f00c680b10b20b940790181000b40950a41000e03801418103140450311890f035900051a10b1442154180140c4d4880c01454003200103012035100000c1003101000b40700e042460392014500c902c2d42e5508407807882e036541c0d00c241c0042c980d26604040580c0380f02d401a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 64395992 1250 64394742 64394767
    0x201030f06030c15020f011505010914061c18110406060c0209010504050606070614180f341401170c03010b030408040320030d020106050105190c0b07080a050a0203010605 75
    0x4d41003041e005507020320700c0c1d00c8070302c07425515017101c0d40c1007440c0d0f0000d00380303c10741e00302e0034080c040c4c1260317110b040b01d1011900100d03d651060411503041039200a513518504d00440c4c0241145886001000031000f030103150145225840f41c9506119509100010582900c1451b4000400c0c0c0c008014640691808090200424016004540110080202101045490181c071002c10510b81c248030301464240c000c0c081001c29050384c9012a08240840c581da0580050010007821610b0903100801502c8800030300c8043c09514081071001c068803001420050500140c80e09038000e0300d9844000007410452180c207401140c0000c80c00c0c03003d00040c400c3c041c03248040d65205215092891a19483e0b40f2403407a441d00e2284000c43c0141c90054288142c10240040c200100203400217008103820900007070981d00803902c4000f10045451008603007144141001000aa001503204000b0305140c04000c01600c011981c809980f41000081088000c3e1071086030304132446562010b007000d4039240708 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 64397242 1250 64395992 64396019
    0x20f0906071b0b0405010e0f0321090a060215090307020a09020a051303050606010e10090501080a020403060e060405010c0203041805130b1e0a090803280c09030201030f06030c 77
    0x15510300400c22040041d00010038002d5000d400c0c59108183c130b8528010005107450381e81d841090140d203108880d160f02c0e450000d15042181c9110f091010345911403604098103000740094158817000c0d4040000d48203070007181e030f450f1090010a142c4c5070b81d5500d00141d0750700e101d002c034000e400803076103881001352030241e90240400b010503150462030404841031030060baa400b50815202504558144484d940e040369404050000603102916510340c203c40103405c2c0c3c5484e10070710b4103000d844000502d51004a90444001d142d004400b04a0401d800ea0200e0b0350f144101c070f0841d0103602e880d806400300b60002066074102e40090507500e00324a20080303120302078030001c0d12820504925010310b400007401490000e205901d141030410382c50b019044010f500702006846405120b251065030000305c0c001d0801c99900207a00c2c400c0d1b0326050303110481080c2c80e0034001d0401e00114034008032003000660010708801143c1c001d0741c060020581c4500800112101848010403235003617100c0402004004000c03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 64398492 1250 64397242 64397257
    0x30c030c040f0b09010216081f09150501180203010e06010509040f050108030a030b09041e0203100e1006061d01030b060c06010f03051507020d1d0d0302010903080604020f0906 77
    0x4545042640c2c840440364070510a802000f08400c0100c1c4000081d6810012120311154101c0441146850940341603191070380c401e2503546040840d0407440b117800c0c00f50010b580300d40d8171102103a050105d000444008103001c0c000d44110300c456681104443e200c60081e01e060f07036550540440d1139150013006403580d83c4400c401c40d40168803001e00e17032001505403290134002c1c000c09010f15510f0780100700c020200e443c001c030b4042c4100d42a41c24040451401c542d0000e01c600070010200c0300c0456800003030314181608030441052400c00390f2140e100e4502007800495002412024807580c2c1d01d81c401039034400403521a030811242c05a400c0d45440d0b01c40d0300a200c0d10240948040e01e803802ca041c40904040c3d090f080850511b50911081040000c1000650600300c0582c1c900c460504056000075100c0300390400c1041004002e400d04140c0101c10700c51902c1146005107088084481445e002e400307041000c8042e804101c44a00007001030405000f1620211240d040396481c3c05c15050800885412010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 64399742 1250 64398492 64398511
    0xc06010509270c010e0409080702040b1f020102070b0601090e190204170a0213060b0304081e0c01050f010602060108070501080a0f0203091c14070209041104050a0914060903030c03 79
    0x8a80c00507005041c500d00d41c2c82c0c01c00101a101e400006400900034000300da2025020703601c0d1090007008605c0300415a45d010360304850225980c0da0203800103c00d04480030740050308488000c200c21903290150300600c2c64600c1851603000c5130fa5a8070040d601400c40307100381c607005e0503010009485042d1031600c448001034003440060400362110704500c42c581081040d161190702100c44c00701545480b140d071004c800c44506091200c1d60400409180c1c0b800090030041c01d030341d008146241040c4c82c81504014240400c0000d0303032100c0c0b03080d8109028100c00e40385502e00c05c1080d13002140384c038030206969041c1c4100346d003300021450f1000441c0c00e1100107103209840c44d030f510300d41c82c60800e0900055000d04912001080203900403201120054172180c1400140105070410003005a0460145ca0840341c045410440365a170b9420402030321400324205a900515020400046180c140e0089442c00d0040c16001c3c118001100c1d655902d110544403c3c000358418000644c034009020300665100c849803 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 64400992 1250 64399742 64399771
    0x90618071806020708060901020a02070608040507030503031003031b02150705031204051c020c0f01050903150a150807030816020d080403080a030c08040c05010e01021501080c040b0102030c06010509 87
    0x144040c1c1d4074070303040750040c00c0181c20801c41040100010800780f80c0021285008524110179154069034485051003903000703020b4103000080074046c041c0004c0740150b4100e07003904d60301d01d408440318180388542d0100320007280c00030000e170101c40e1040c20350390b2002e035001e001c80d5104100402d0705103240c1c0207a101200c051004010034081c04403800342c1c080c0940e00c9003004044898000781c00900b102d0518071140c085600140d03038942075607603115140041010a0a007259688254004282005d0410b0559005840050305005c00300e4240d03880414000c0c0d0000400c0011511048841e80301c07a5581f0000d00424400c0c4003182c2150030181101d40c18501c000e00030341542d00f13640e4400d01c81d0b0b00507901c2655400d0000c1110005590140104c3d0016200ca141c880324078030306a42d4009089009001c2d0604000450a404029034001c000440c440c250354040b040d415a0760f1043d0543e225181a4014065424008600225400041591401c0706c10601034a100e030300344806d00c84018001080c01e107004456 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 64402242 1250 64400992 64401017
    0x90a06030212030d0c050322030507050d08010302040b01090b030406020c0304051e0109140d120201020c030d020705010e0102070c1a040506070b0915060a0306020d0e01021308010b09061807 83
    0xc216030b0148081c00d19000c2c5886155041880d012152000354003010711104004102340c26907401d82d0707150543c0a07a800d01411404070705089580b4082d0781c0c0c00404601c25980e4040e9040c2e002044203040300c0c4200d400f4001100801e004403600f41c1c1610404603050028008240041d8054025146a190400460b130070320382e4400c005115400268400088400b640d00465010359005110780c0140c80c1c10401100300c940981c0120b09862103034000030b040c81020050f200d1b0301c2740c802e404596002c0c014030f04407600e0303403009403100c8020360050f0070483d51036181001c505036a04040c02035850301504508030144081c0b45c910705041c1c50079207c1e111078034808200408507156480078044c00b0701c940140040b021b81d00d0320718845480c02640701480074809140c5800c000d002d90b180780300309042d254030100242e00c56200c080c10102a2074088036900307195001003030200a40b210a03003100c042b00d9840b40280706900c500700031311400341d200f920042d400101940c0070103103040e070201e25541c04c90500d14142608401 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 64403492 1250 64402242 64402249
    0x6031c0309020607021c1a07050702090603071502030d05010906141012050f010302090603010b031c090803031e16050a08040201050d0f05090d020f07060c03020a1203050604240302090a060302 84
    0x40e100d000c0031a40380b0206c0c4400174826903684800601c0b0300004d124245003023101e005440c034014410001d1080800d4000175a090320184039000082151070289581d0354001d01e400781d00c1780c015002420409141900005401d45a4003482b0122103500107a90580d8000d1400d100003c1509038190b07082c003c400140602211003032003043c0c41050162116400ca50440c81080b41803880504107034402c5e13040810300052a500800d80c82107150740040f0417030f5140c19200080c5c942414a501a21450001004002c4803c2000e441068520580d210380e204540d2016491078011070340c1c1013101d000420900804007014000c0180316009801414060300300101c03030203800f06440f9400b0221428944442c10b0002c01784040000e030f840442c00d40042c040d01746a6048060b034914481c86000c1c20000000f05180c01d040c02070160305025a0810407243e0078081e0440e000d005000140c1d04a40034901c1c0c4035240485240303000100001005c0708042c1c5010b6860364080100200011b4030040c805603841d00b0010043c0e5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 64404742 1250 64403492 64403509
    0x100b0301080109140c13050a181b1d01031506080319080106020a110d1103030a02010902010206390f0703020a1703040816030e06040e090606031c030902060702 70
    0x2140100201e001c0055213048001905001081c20300d0703901102c04241c0320f40c1d81007122074040514280000b640e54402c02008058031001040d118011000b43c40c030f406001303003a910010000c1f0240c00543c450380d42c8401c0315034a2221003c4c07015109190800520005d01c54800d041200301203864086020368803411451305581c007100001d00c003020700f1b102d0a000c6079040a005401000d107800500341c10003068503024611541c20341500c0c85050044154070401c4507058080e411000090100c03900c804c86440068020020001d01b0b038058030600000442c00300b150651206415421701d002c510110802d0300f054541e9031f1746034030114881d40030310804035214070001c003400100b40240c1c020a011012030030420300d1111108060b5210b41000c10400010030031180485450003c400c0134894014030740d007400c4070080c0940004a5000600140010310b48245008050140d5109819128251200c0c0d0400d9500c3c144130f0036454000501c01c0c5400480c6010741e010311102c900140c641480d00216500290144 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 64405992 1250 64404742 64404749
    0x1090c0e040b010b030108070b07290a110403020f010309050a02031f0b030c01020d14040f0306060303030b0d020f040c1106090102040609090c02030d050c091002010c1106060a030b100b0301 83
    0x49004100520061955150040604040c505e2655040400b2030340ca440990182501901e8009644404c10030404002790300d000b1030204100c1c400c0741044410744c2d51603080d114041518103084014000c6146042100d0841c2d41c0100b21034082c106610042d0041d00d44580181ea250040451400c090780b414001d00b80c0d40003043d10009204200030903082c007107035501a60a0b00a611100a260459800103001000c4004a0601c2c1c1c0309210700441040c0a0320498002c0c98120700c001d0f031f00100304125a0404000d0720300c20746040c003070200e5160074003040c01000a0007960014500c400e062880c1031a0f070040341444103500d40308014030158920249400070a0f200200c0c03aa50015003007280c150b22407109400b4007203042c0240800741ca5040020f6480c0644000c0504880c0d9880220f620501d80030202c1d07101c41c1024048000c0310100c940c0c080e00070800010000086240d80070f95800c0c100020036a244582001006e0141050554a4071102410014680b800385101040003003600005003001d14000d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 64407242 1250 64405992 64406009
    0x903030209011215260106031a0604050402012001020d020c0d021905070603020a030612030810140306180a1401090c050a14040e07050409030302120c09010207060e0301090c 76
    0x440100100040040d5403440b000b901d81460041d502c089900010725103000ca589851415660942d0700250b081d81c5c0f41040309540e21586010800410482c100101d52115190b4008601070740d900c5100f0300042d102c040300d0003400244400e0342e50b19840f2043d8140040caa8041b0b00050510365032429041c101e902c0010704070080d510041d09030013410303410085070444044204840020894595074a69212182e000e401c0c00d06402140c8540f89034481d41c003120081c144500004d0034811903090150028130252500c14000300505808502e100d40030402156041d005001030419603200b444001c44103201081108850047c01d200380b0104100d2030000000f28109000000d4550141c0b50400621aa5910050080011810030072404801c06960034009505550100312075010601c01400c1ca0119004668400c0c07901e0300b11401e0540c181d002d081c060b0300301150520f00340c550340212001801090411801a8001001804880d00c50710641d102100050000f150692040c0d6075601e03219880c7d0041c0c4c85 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 64408492 1250 64407242 64407247
    0x1c030f0c0c02101b080d0902060712090801020f040303031a220506010305150d0203160b09090604020403050c24040905060108060f090c0f0705060a060512150a09020301020d09030302 80
    0x154500f14540c0f100001103420814003034400c40d001081001c075442006000342c40701203a0500006400c0d004039089960047c541e0b0b43d2421146003403440365110b4003110000826141011682d034005101302c6082004607416103050500d9035508a0180100f03001a066941c900c041c0303c0c031981c881020440100e8a11202c108510320240c031100d0032141d00070281810981403030144503140f642141200c6000d082521101c084020a0001c81c0c644011015034045a950039240090200a400f000d0031407203a04403400001600d4100401050780038a00002e04980c2022030ba200f06403601045034150601c002010201c51110740240c40b03070a401c164081d05101c5c0e01c034410401c041da80405526842002165060000d1990201180141000401402c800700000407040b681800311416164080c1c0d020007111407525100e480c0202030b140c6480b40c2e90140f140032140e0328100c41e01040700c0e5184406a8012501503030340010700800782c01000c0c07050340c05550030461800c068441e40111119103003e80c40141c1d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 64409742 1250 64408492 64408517
    0x709060602030a080c0909061002190602090a05010806060301270c090501030617060a110c01020c0d020606060705030a050708071505010e18030315030309120d02010f020c1c030f0c 79
    0x80c001c41c4000c08084115100704044005035440c4503185030030070419513a8415048507210160328108480c0c0380301a03400d0382f00c0c40840412140303400600c0382c900c1c29141101504d03074030801564400000d540e581c0c0d00207414801806414844d01e0584807080d000b5107001c04504003620490225501c113611040001e140000a000c90350305030003440d0003003c060584114581d540001141c851801400320001c00c0e0702d50308400d000d0003202043e501e0080940d402150ba400944808560701c1d000c81d40c405d0094010301002940d14642070080e00c091542010195241100070039003107409070700c5480101c80840c020b11000010940d0031201c0070001440ca880020310354100703e44101940b0000784a400c9550b40803804645004012080d26080800c40c40d0501d0400042c00c000780c2140074031518260001da000070a03112a120000f6021080950b5030001c2142b036a130880700c501030b4422a07a9660655002c03030075510240c51201c806c9980300f40303c0e140c0051a000d422103c0d00a58040750b81c143c0010380c459401c03d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 64410992 1250 64409742 64409747
    0xc0603020301080c220b010324030210030207030206010608190903030e010e0d0c03030f0914100f140103020909010e030a03020405180105090f10091815050415020c0709060602030a 79
    0x10f84d07041a003110038919030703540b850152100b030b02000031000d046500c8000303d82c4140d0090300801500c03c054080b441d49500d8100918544403103601c0264818041c0242d40c00420b4040d100301c0f484541c1690262149a0a001042c0c54001c1d003c2c1240f0015455120604501e1009100c1c18107418030a40e8003052590460051600b9200c1016203080160400840f0040c5540c11041500301194541000310b030403200480c01200401118201801030810701d04180341c10880450918500b0060f65030801c40c9000f102075400444108201d041088030102c40103002505e03140c1c002582c03006105002051844601007624215001007843c2800b00360040f030180000c0c9000a00c102c1640c00601e5590a02d40c54880007445c581000740944103905422800b0519207040d00f1080c601403c0066001d00c440800c2c26280800340c910f99400361100c5000640601e114101402001d00a03034004e81d00c0c104200c3c500d007040000394403214050794948140000010341403a103000e103200a0056801468a420581401 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 64412242 1250 64410992 64411003
    0x220f02100302032a0a210c021501120f0204051807060207060f2d1103040e0703050108010213030803060402040306050f010305070f0605070807020a1d0114030307030c110d0c060302030108 82
    0x100d404400b01c50282c10803c0e013034001658048045480c010854181c60b01c3c0708a6440d210000c980c02031070810450720201a0009a0710304050741c4505941c01e07981c1d07940c218200d0601840e4004044120501d02d54000d071500da0007440d0041401210308034800002d0980078980003007588001c0242e040794004015468112090000c06609410b2415a1402001181e120318220804016100141c400e9101c5030070f11407502006007070500c0b812240d50f562100c4128401c00b1048842000180c02c03c000030403080010300039a440d04015a01020f0501d055668445094100510b00d0390800d50902001012481e24050103014290b0100c0110742035045040c11803c122803074002030b002164a6504100e201c0d8084121045541c12806131500c90a551001911031040c81e8000d003c44545194801140d155800041d81203407150088408104229003e241c4c4a0042c983c014010130b24000c1c3c0c03e401718101e4801c0c2503003900e00070040644200700b40c1e22803450017029008640007980c0400107101c1000304124 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 64413492 1250 64412242 64412281
    0x30507090207020102060a0c050705100e010501170303270106030303050405011d1c0309060501081c021b010c05070b070f0309050a0e180c030f030901090e220f0210030203 75
    0x10340c03602c1d2040e00007075612a0041d0100f12016500e40c074002031075110b44107656140d94000700380c9050308840c0d2860000340c441d412000810b9440c7c6800080e43d016103040d411003440400d0051411651000241102a5920509514a1110104d41050450080c4034440103503102c1d4400003402c1c10582000c03403c64a072034540c0d0228108950554110001c00202c90741c0a84a400d10002080b1250000702d01802050100401860400c4004102c042c404140310900c05581c0242c101d5000d01d43c070040f42d60305189412241480380380e041604095100d08c1151520b103000320201d8018a82d07442d40150a40c0c0644000d0b40c1d40c0c81d01c00380b4003041560204446004260440314008004c1c00c004030740803054805010f01204480032411460a8030307040c00001d00800d8024290360b10b03d480c0704a50341c1c42e6400708805500242100c0000304941c2da031064450302952405007800bc0d48001c145541700e07000f0544030155020402c0850400041e034412440c0c1034003643d40d0b98007503142d05206820b1718242c901e154 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 64414742 1250 64413492 64413509
    0x6020922060614031302090a020702060403060603030206100b031303090506190908030c070504020a1101090b0105031e0303010501030216081606052202060d1509050121052e02070b01030507 83
    0x10a00c6000c030417807600f005e07000b50100c4181c0107540300c1814000091085840c001d400074404100001400400d60014042764026001d55000343d6900840d451040018020f00292a1041c8007184100808205d00d015440c828100355109540364000103580d81c22640241d008211000c1e402c40e9001d500415080050015030000c41c2810b4000240d103841c0c0c04140546401a0760100700c0c6400d461045030841c031508020b0000300300590305814441c00998090144030f010f840b41181c0d100d505400360000e11120040d95024506590914004502a42c4144202107031464a01000f402041c2c5070401040052840758100814244514191080d508010304020300d0b0400c0c2d04510036a07110340609200c40359411100943e075070441500350030080c001c50600541503810300b440415440b0032a481281a43c0c0c0494007410450004043c42c000c0050310760000f4150b40080b1180c8501e4120350345141d01c1603900b004c035409848100d80c4d03180c00700d8204d0003041d00d0900c020001001401818000035002c4c0900d003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 64415992 1250 64414742 64414747
    0x6010b0414060703080105151908040605060a030302061605070b0c0a02390301020d0e0a0c0801060501050a050d02160303090611130b0702030307121206050a0303090306020922060614 80
    0x752006400e6880c144a1f65004080101ca2070445282d043c4c101c0d1086c8039a80c1c1ca82c100702d03e0544004080200442d01241c82c2854500414030500d0140e09130f0003220b500d940203240b19502c140001c10528001d02c401c0b02400801e00501d80081c0000480c40c0c8141c03554a161516034043c070390000d1616100d95031420710080c1c515958564002180c84180c540310f958921a04403000820209009218000d01143d82d689080c40450f051080800c84a0301c06000304221011242c4502d006d0342211503901c01ca030701084c010441d020400f030280300a0a185000d0120050070001903c180c0010600f60b41d1041700025924110a41009001c0c41191301c04040c02e08143d0501d0701301c408590300c224950007001e407070074004100101195010030844801942c0000096194440e007000074100d0f88803e003000143c1d500b05030307002c2040c0c20841a0b050440360175550703007003401c0e107140c031070000960000048982010310840c031128910440990038450701c0c0e0b51900001c2851514100522a00c2a5600440c488104 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 64417242 1250 64415992 64416007
    0xa061e2306040c05030604090c090e010209130218011812080301082b05090a050a090203090d02030f09040207030c0f12120515100c0b0103050304061d0108040605060a030506010b041406 81
    0x507641e010385c047e42c0024802e041030604030420012a0301c5031300685c0c28144200103200041d006810f4142050302c40b01c01448601511100707030f000e00b0440140d41e00c5903080d0460b10b50f01c16980303040038040b1280c180c0c10058803680c0210703029400102c02c0e165081c00100410130034404006011078030316107071005442c2851a9440002c0303500140808000c002c000300300503030b440c0e41d90152200104801001d00746015030707507205040650000c9034403110600520f403040d4141030010048580d900d00b02c1400900c0c0c0000081004021340240394240c2c1080044081c42000840c0c404034864024010703002c02c5840039070b18070001c10703c0c0c0017203205102c1d45040c2000d021045041c8000c4d1a00204c044805c40d20500301c6a03422980009228405004180c941c40000240400480104103480d0301e50380e244010109400703090540c211407000280040d04005c00a00816055807201c2e400060040010500319666207416180c201e003030b0032840500000007010041c00b14001c0030105030010a071032090610700b0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 64418492 1250 64417242 64417247
    0xa0e01021c080606121602010e0d020a150e0105070e030601210609140304140103051b07020405040309180204080d080103050604031d0a030f030806010509030a061e2306040c 76
    0x118401d90405021180b4040707840c0d90b58500030b8802d0b5038109031541e210f5107860700e950282c01c01d98001d20405940b9040c1074941c03044010a003414000c0d065001440e41c06515519807800100e0085080003450380c41e16010700d0580b0a0040074000c088540d18914402c00f81003c25082050607400301c010368030084034440503154640c52111845410002c000740b11744c06801c00c0a1030b4540704160805c036000c006004940311124016a0710001000c0e0ba0400c015075a0100d0703200050100030502140c07800603c41880145419005298004c1c8289008800103030744014808074035485d81c07078500c101ca80104050141c0f400400050202180901d48249154516180e103900e0b01c134003500180400803440501919501701885400b01c0850152881c00c44039501c2c20070380100075512504038001082480401c0711980310b84281e0710398050060190605074001e980c0c80e0000d000c80801c0b1100341d500031407544066115403080003440c40140d9a0b82176030a040c460221903d180c001c0156100f24a4032030f06821941e07 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 64419742 1250 64418492 64418533
    0x80906011217120112031409130b010c1502040e09070b0a08040302070b0f03090114010b0f070510020c0f060901050c04140f030607030b0418020d020402030c0d0504080a0e0102 77
    0x90700074400d1040300d003050000180611807038100f0304026041d90300009072148881c1001041c540280c0c0c405081e004654040c0b0001d01c60042c10315404001140458400d079040c0e0701000b482001410703c83c1c2d039050a90380b4851250088584090030607400f14041003101d4041d2007140e40610700300054405141007091400c0c240c09072030b4000080000354800030302014001c01a02c405480802c603400d0b1145000c1140700f00540c0111511215075092a806109070080140454182c52581c88010f00708000c5141413035194114242c2600c0d1403140c400742c0c000c1891284020204200c051000c1c10088503025842ca14221024200100980c58601005142011a010f850540c3c1840b0005211489841d001524a805a004180d494000c400c10700c0031150b055800f501300d2850554041c04864004100d8002a48401c6006034001c8a00c101c080300600d01a0b0055501606046580c0c3c00d0500075840007040390340803182103a45800010303500030300d00c0d0070049410003d0000d1008007480d110305040220102d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 64420992 1250 64419742 64419779
    0x90120070611070b040516080a03020c1002070f030c050405010501050406081902091002010f0c26270303190218040504020402190c0c0f030b22020405040503030708090601 75
    0x120ba45a0321a26000411011941c02d81d803c50151026800d141c144a5101c0c92519905804080b050784005400c000126038280050342640161124440200a203d2010010070b500000c50281900c042001040035800b100a180203d48217400b841c1444140011600180c2009040c40000d100c00c01c281503200302c107540d0003900100c1a050041c08045820060b000f1010181c0e0b11101c00c00048000ca58158000185c00c500054140041e245040040d100454803040040300e0000640244124030b81d00c91690b038000120480c0000e10140c000340c040d0410685d51010305042d00004241301d0191181e28040d03203e151740600071850514102c0c0c84a202c0f407200c14a45001d1512040013406569969041d070f04070b203224085032004600305190081c41008100d0088420b5050700340701140780c05402c00c801e020b80e980007034100078a441d01e49074000512000000a10184d00511a1000680712402100d002d507124500a585900f440709018003224002445862594030076001003018546c0c01c03182080c103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 64422242 1250 64420992 64421003
    0x8090f1507030902042003060301050601050406020312040516060f0905010801230102120c07050102010e0d0c0f1b1427070c020f10020601030201020f0609070311220509012007 77
    0x16060138808a0003501d2910300b141400c00e00e2403030080130200c8810082d4072840c0128000c0040c1d81d2000010749180c011802030704010b9000b8001000c220b14000000d54005000301c0032240004928a036600064116800c1040081c40d400021640c80d0740200309000604001d00b0189040d41c18601c0c070442a4200361340c049014110110030168990003840300160006d10b4030300d490b0352280c00400469540200f1311030075005618200511000c41800704d6411040111503907925403580ca181c5a0315000c001001080d1581c0c1c60100c248054501c10069a800518460708054034070300d000030401c60110010400f640c0710303c0c21018840d5212543c3c6503070340da200c8424101003506030440e00100c2d2041c000c1e481000e170064621035010702d00310380014040781202d100340c2c2102d4a00801d1000d80c2c0c1c44a109840e01c40495102d0142070002901401031500115000b81980c00281d200a0701140c480c00c81d212500b164a5442c01400b0000000f0b008a030b000c004484070022441c88100030102e4075101e060701c003804 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 64423492 1250 64422242 64422251
    0x20a02180417030408090307060e030c0406030b040f03050d02120f0115140a02011104120519080a120b031516021222031b0f0509060105030a05151008090f150703 71
    0xc02548100780d514a01b40503084580031038490201030805001c0c2c04e0660f00c2807080c10719200091038507010300c4003603d40c0300c900340416485556880a19007640b160480500c00b0a02c4006034a515502c06012100101e025207951070030406a828024881038119130300b5500d068921280041c1c2001000300503103410170001e0b5840d041c8440807401040d82020346141680c0001d170000e48030380d640d005a04118080c0c000c3e00c01d5100803040d040f45200485c803008103812024406015501c0c001c202080710400d13483c20109407400c3c0c480c0000e08001d0201b20003100b0b00e802d90103014800483c075030b1071085040c0c01c4c00200702000810019400502442400b03d40f0110410388080441c000080500001c550100401ea12035514074401b15400c040e9002e00d02400c00c00000001d0a403410081076070040c441a15044d141d62542c146c401c1c06850018140110041d04a4040f400c603103509410002070b01c1c140e61042982e040690070306083c90000a2a003c00303521013011503d400705080782098004d942c5040024 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 64424742 1250 64423492 64423501
    0x1050603040f0606051804060e0c13050603031605030a0801080c06160503070206070b0108060601030c0c02011209050d02070503060c0703020705010c0317160f0c0c09200307020a0218041703 83
    0x1c0c0a01040d1700520380001254880070f186035499185280510f10403501845905c0350080711941e1443d40035883c69001c600500f907180608015480b05410001c040e05a0340b41280c0c14a8800da109403404044955038030000f8140039817948601303003c2c0902403d00180c859a1a950001106070164a44511301d04540c1030729641085420002c076940650301410440d120301d050308018001c04402d1161081901514000403140d40c4244a5014038810588810110351010713001195200075500001a400340e8610f54480880d0042024940c400010f81c010310b6054280700c00d142c18900090b24102d49030000344004400240c01260703840030b5410a02c0d000e0380c01d2616040072200ba05c118610708442080650900070001c80c4803407003007410b45160329050300c0702c601c51108076194001114050100400304209005014250b00480b0141500b2001000a02c0205600103001c0e031060b601c04c0d0151703018000e0102181440010145513405040320f41d41d1a00e0583c440c031081488618150154200000016 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 64425992 1250 64424742 64424753
    0xd090b0f090109080a0309150f0203040312110a08030a0f02031005060702180f070f0513090b010c08030c07030e060415030c0909140403030608011107080708040510030b1801050603040f 81
    0x1e0020507011044990700c0b05d4034140600402000d0160480034010400150b45003401103003030303048200301d55008614080c999182d1510014000843d441000401c1c2001e0300742d00c00c1000013000007030080315056a07074200000d03500c0445200444840702c0c18010b2040100040c2414a011b044a40545029a5600316880000e420001f400c0100b805107040a0600644034010011a449541e43c0c0e2a000c130462880e40c402d81d002c1c010090340501001080c4030601c4200a00d4100c070308440e906042c86c1c0c44400e40c0360f5401840b90005c41d0030100300d050204c0d091003803640c0020700061028040c7c9040e460141401182420181c1c0d8001c000181622514501300d0103125045a000508007200108110030503130b50650302c148000c0e40c00b640005d041002c08500d104042c0300d0741503441c1842d92482d01d400e0706642d589410350011b101c240da400c482807000041603190060100000400c1d40d03400107420f803000c0308214400064100040c000407a030001484103483e1203007100d40081e044504000c09440600e0007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 64427242 1250 64425992 64426007
    0x15090c2d0a030503090a0909210504080307080d110c0a0605100909060f0506030c030703031404090c02030c011112010905090709020f0a120513020915100f020d090b0f0901 75
    0x79000155601c0020034080301202921116104131104084159550b40c0b100658110031805003e00500c1060560f41c459210340040302082c060403e00d060a035103441440c1540c102003025581050005004890380015105000300c0c1d10003400c404c0c0c00c0038980d800302c0c0c0e590200b42030010700c441e60750000b01c1c0102951040340001000a424144205d030424580b610140800b5058080307205e0400000c82e5091034007282514500c0310250050030345034a0354030210b883c4c600754082c140b00090100400b06640303259000b5409507203030745d40046545030041f5074603c3c02c503140c000581c00080010b1010340300c40902e814485044500d178440c007207460384407507103000c1c02c0c0340c9164080f510b5a40700241103200b00c0c040b0310280444a116031a4a02081c1441280d0401d856003118412000309403e10700c0401072030501c0c0150b40090b00c0e03c02005240e880b400c0803c215034040c2001c80041109140701c44501c5504100d111412442458030b41c1546281001c034a529000301d00c3d101407407450219010304103901c82e43c136 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 64428492 1250 64427242 64427329
    0xa03050706050a0c022d09010b030a18080705060610050703080a022a16080601031e05030c010608070e01150801051c02031204080d0207080606091b0a0215090c 70
    0x10034502d010401ba03441e24086c140c2003500d41082e20011040542c0d2506004190480301c1049840349195a4030aa4400908240540700c41c104041041070b00441c15000282000324450401484642045804c00030444440d503094010004100302c001b0000303a21104050300301900d10f0340036071200040d81941c1d04185120090740c8403003407408680d5803070050001c0c0c207059a14007240b00c07481d0700707849a429503212202400042c02c50082d40f0208103000590700c4186c4415030041045d030b0305042c0f4040d590b5003540d02561040009500946007423201c0350070301000034010035141080310000d10030800082c00c0500144911846070002e09801d15800303c44501c5400c034913a0040030340d007010540342c3d41c00c0e20a030840e0050103203500c10000320821660001442d8806e90324518001c02a03a500d42040011030000200000c00c8414440c82e01307428115035001130440c8080540150940c0e0254807414204410024002d081c141d10028a80e14182c458008a1b04440050341c01b0000650130510017810344280d602 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 64429742 1250 64428492 64428499
    0x10c0503070c1404021e070204021323100c0f0507081207110a030233030103061d1903052a1501090203060603011206060302030f0d0305060a03050706050a0c02 70
    0x3095070410085091082c2034440004261040b20150f01c2404100d02803102868140c00c00c41b844c00d2100d08008000d007000703920040000d413138070300c074401d401540200d182e000f00700d070032641c03908072106010788200c4000a00d03040d106884e24002424000300740c1281624080c00500c06400e003001403000034000f040c090621340003103034960340e00d02e01c4166899100321001c0c0e4440450406031070540c540810054100c0740c0007042c0d52158088080c8411503004c60720020250360705840003000b4a0720508001d540214041e180001d11281e00f080d8108003886d40440e03d90792900a80c02e40320729803e842c4000220680c00d86469616081a000a4400501011f2034200a00002c0084800745480051403113840800026031040e1740e6607411258059010954070158407a200340014000010862949000a40140404903125989402090405c00300110004598010450341003503640c06001d180d800c80005d0354040c0342c1c10b245889070f0751212040e000349070070000700040f002c9000b4481e4405085058006 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 64430992 1250 64429742 64429747
    0x1302010804051e0c1203130513060f061d040606050a03090c050d0c080f0309030c010c0302211b030c0606040c090b0f040f06050703020c090a0f0212070801170a0b06010c0503 76
    0x5070a9581c030b40180203c0c9209511501790090f1289020080e94010030b5901010110a42444204a014241c108005800d590780f030400141070802c07281c1113001400c0b162299120030300035508102c800a10517640e6400759041c0403003009079540c494102d680b588950318001030000b420786045000444d01303170b00c220780c00030810300104144241000304804959100d011201207901c0c90408c2600c9000c2e24a2440d4036810503030340040994000e10402070b0302e40c804c1c4191622121031103407910000443c8100c0c00201d8101080880b4010307030b00310b2102000d42c0c483d00154144144a551155a4003005252a0207562501c030701c0550030340a01d1003040900002109a900e88403240c01c1036055800038424079032400c2d0502e07400030384035009070210b4045c10b4140d4040e11050703031218240940164041d20000459035100245488417000b440601641c0c10012170100742d034148000c0c0282800810307000702d804d5141301580f0441032800080c0c12010654000031602042c2d503018016107410340c04207005000b90000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 64432242 1250 64430992 64431043
    0x4060305030f030f07090614090604091503030f11030412020319030804030e01030902091f0f0902090f010306050a0306090203030706020d09062d020d060906030308090114130201080405 81
    0x3100d000d1441244c40203c916059580c015040724003034410712400c004600042400c109100b408030081100800c09840750b85001e58600d04141101d030425801d8000f0f00340301d0f40510400d40d00c0030412041c1d9030740745824000c43c0c82c0e4160103a1a072203548607020200802e4400c040864406004042c0c01c2c58040c00300d1003100c1c429003801391a58204880490000340805c141c13420f02d60280c80388001c015000360006020f80c2e1a03420510140e0310880880c00c443e60701c50800201e030006c0c00c50001c0904202d550150f201c072030302c200b44410499941025414141884000e00c11074503401c54101c200c0c3e801690120b0f04450301e0002c6403e40c41f95000c06030610b8000144005011003d4104845480c41a20100588490503403c5000c82031001d210107110240b010311045442d107650090035503079841d50000900c00d680c440d4090101c0780298400c601003151042002010760003032003501d42e4070303249000080c2113141ca101a4140302a1341e00e40241070140c01800b00701400030400c404010201d002c1402d02c800a803 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 64433492 1250 64432242 64432267
    0x30f0103030305010504150e04020d02041e060807050904080f1908090d0806030606010c03090503060103060510080102030c0f0304060209040504080d0e0309030c010c0816060c03050606090a030206090406030503 92
    0x400d0005a0229040c000001042e04061141301028005040e40718031032420110b03070011400000e0400c1e64003018030448480542d640d4410034070b8004d203001c50350081103401450581501d0655111100c1900500c000700702c152640c4c5070081d8019030100601c2e0ba220100e0300b0746403481c0176440380007403440c40003d1420249900222502c4c0100041e1003111070000c4000022a9045401c580c04c6030983c2180c40486c102d075000c2c408441026100341889040f0703e8807400440c1c6800030980c019140c8c55210340c00d003c5111b842d03900329805803095400030741c510310b020b0007802d80707a10038a21000c107140c10010000b030620907140d050354001100144140041d08113070a021100781c0060100100c400d1610400c00b60802c0008100d4801d85805000340900c00103200041d9001105c0038016120450100814600c00300785481c80011140704500c00a880c5031100b0008044440c001c02c142d004036420400036185580d020158000c4950440360107030303903800000114019000c140d000410350320000c900c0c450141c5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 64434742 1250 64433492 64433521
    0x902030c1522170d0914030106080f0615010906020307260a020a020a0801020a0813030201090503120f060f01020303150114040b12060411030112060b1201050f09070602070519080303 80
    0x1070009118085603862000055198803e420384c490200307440300c504000705030b5a03a020070204c5800500026000d40e9900750182000d81003680e482003508100c0c00c20411010145050200a001780703401011942400b901950320311a0780c5c1c0c0030f0084c02004840c03c0d1141900c51039509900c45010400e622a0400180030390349042c0d454040340b050394400e10119000b401403007511800350b15a50748008c2c6480b140008913021604201c10340455480d03004040102d001003000300328441c0b145072000054580150790384a03541002d040c05100352903201c2298840c0c0e038000181da0b04072422200c12241e9540c0000140c0e034140c240c00520056074000f0400085103100c00300500341c0442c0c40c100440745035a41408010440e200d10890404a0b1000c1c8014010003005050075a0007603c2020001044401103000840c00c403500080120242c2d111000c004208800d801c00c030f500018031000410300300741008400b94807111180116405207919407014180e00880842502c0286034400c00d4982c3c0b400c6c245203031402d10 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 64435992 1250 64434742 64434749
    0x106081b1b0a170f0d110702040908040f0e010608060402160507090204030615050307210c0e15041e0b060706050408030916060e09070e03010501060509030c01030902030c1522 77
    0x82c50f000c0c070b81c41072a4450400316983c10701007135042450b0218800c246002040000e04008000c082841790b01c0040e01c0c0e070312a83c0c1240b40901c034510b454a14109003251404202e410010888409900401006400010350707904040200c0c0c0160322000da01703c026400c00c0d02a100508180320340000000c410340564004d02c20b4902600d000e1007450b074188011480002c142c450305405920a0b44108600140c004441c407000c4d010041c0c0341c0d05180282c483c82d41e040c2c0140c0140051040300c1d81445940c400c00d0b03004030401d080954040c02050740c0f1044560500c030801c03800c1c0384856225003811b5500d54a0104503200d00b42e2016040046041c00e003031040e940c1e00111444007091203a0b00c2401b14084101720950100e41e0079560305840c00f2007240600403040070103006401071210110b440003103950280078040c080e00c515034406440340103007400c00d03150080000086050514112020015031000b1500503902a4251081c00c00007181a8981d1410300c80ea05c07011200200620001e000021185041401c9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 64437242 1250 64435992 64436003
    0xf090e10050f1e010803030105042705010f050603010504020a03060f0b0d050109030807020f060c090a120605060a23060c03090a0311010212190e1f020604020a0e0106081b1b0a 77
    0x103000030300703c0d0101c03000420700800b44940d0083c00100301034681600074038210880342c01f034005c441002e6481c14045404031041200c01d6510b401c40c50025011034459664451011070080c0700c1070405402143c00b000340b43c080548910b0700d62800182c4c44409030021418044003501001503482c1608001e07000b400d04c40c0c1c00301e00145010010074140380c030009031b0302c0d0406241009404c0980b03949024010580c04554841e400c811206c81c0082c10280510030304544900900000c243c2c1c0c64070300c0070010543d0264210b42c02d0b12803541d07400c2004010000c44220103200540da0035640b4110400ba45145014442069901155100000c410000400d1034032102050a03021500400f440c600924002d000e604000f60301510148481410144144907507454107034082d26a04400750b041c035080020810482007c40580d00c00c0c0b092000310300384145003100a040d001400d103415410004010803000001d0440d4400210025440540071300607001c071100d03070b84585841d1030040068424540c0390141030b43d080d1035 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 64438492 1250 64437242 64437271
    0xf10060e010e011a18060705010203160201110403030e0d0b13030306050d020607061e050c0a020c060f031f1e090e0c090705070303021c02091302040f090e10050f 71
    0x14409245140e40e8140c82803101c0c4180044010881c04180341c10500180e00c4a907500020a40b0b11b89641c4028090076021f8800035a892900040180b6070b0030201c04030200b1607240c00315503500c0080180554007600d51510340300c03014480c010001008060071a80150804103004288100c03800c000749143c40d680d202c0e40781400060750720010010780780410070300a500000200a160b000074495800a41c5031740301e1200f1109014160102001120002c031030f140034880740002c2e940b40c001d404100500254804403049864142010403480440c04040c16810408901960005201d42c2044ea4403001d40000c0304087e41041c500030424030700f0281c520507404018079082c1d51000c900c070040f40e0f106003400c3c06000c580081e00c421108403502c2d400100140e003015420300c240e8501c100100391215503016526800f68490700c00d5400c02551410090450034100e2040008110714514000f40d201142c1035160000b84164034001c0b900e0810070810048841c00386002e0400c105140c2050282e401055280c04444 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 64439742 1250 64438492 64438499
    0xd080903070c0302131b02010b0301060b040f060e0a0b0d0618290303120f0103120f020d05091305040318090b030a02060c03120f04030206250f020f10060e01 69
    0x9460384125007001e00090b4089a061015040801d5024100400d15000190201e1003c1041c0940c100100681d030043c0d4594000412031318090164002804070f0004280c035061518140b00c038a401e5510030801800720300c1c80d2101042e0f0b68006004000c05221001d190307140355045200c0003d207202e01848a0040030503007107286240d00c91160000f1184040c0800c12050b04c0303111000300140c0406819a414030042284540c107a0900310018043e0704401c0c450b902c42e504500d002141c02541e10022010020400c1c0c0c40003200d6170004002d003413241c00b420610360f10070308400412040c003404100e8801660422050108040c1d101d0711100f054240345900840f410740750110350054810003a03102c1d52640c4005524005881d04800914071850140126032130841024401141504100d40c881d100552180401041c19010302240f588044003043c02d4008030155801881c036090315206103c2080310050207a03004c2c0f4020010703101c400d5400022540c00440d01400320010341158040d4080c13104600c0f0000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 64440992 1250 64439742 64439761
    0xa0801050a110705030a0c02130609050a060b030402010203030406051302040908030906150f04020d020903060c0c0d022805010603050303090a050c0d020a03150b0a030614070801140d060b120d08 85
    0x49070000c4d4044040e610703007403000744201c65106007c58103a1b07200c0510034070700303615003402d00c81c110007051400000701c4c407490000480e5003200e4003a07200d220440700420030030006030790100071243d20a88c000400078642d100c400400040e400101d4001b508545050a4902803120f100d016620914015089601c0c1d81da40c154902130071010710840c5600301c4144011041140b0f01038029103880040701c2c2005061280300c00c0003c0c40c00c001541ca11078103540c0055440c0a0388414441400500b4641c0001e0100784989100e002c4500200444200c0c0c07030404031009410040290800700055030044216522030034103a40d503c0e140d040417181240d03e40320391240c0c84000e040044481e021150020300381c0d80d10702e02c1d50b01c4800e98500080d6041201c41d40c1c03420b001c0547d50b01c403c05075015501030140044e4010301020270840c00d0001400c15014882e17010010021494002c070b00421003241504e800a01488034601007024007118100030354003002a01d940c8920140015204100a21954804600b40ca8640c0c55 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 64442242 1250 64440992 64440997
    0xa0c0302030c010e010815030120040e0a05010b0406050a030e0714010908073f03030209010318020d060b0609030604140d05030c0f1303081b100b0105030a0e0c0a0801050a11 76
    0x1139004c6018003000480a440301806029501009000403841c0241c0703070511100c10b10040d0310384401120119051041c6000c604d90b10341d00c0b02041e04208a5541041c015070400d028034441c038030420100203003040360706200307820544411140c0c0341210415034580104103040229240c1460004000c0c140020300340030006040011030350240c1d00703100f0801e5a14920b140740f1001c0e0002c2102e00000815440c1d2183c0c0001c014414180680e5006032260b124130001800d0381d105100d10b81ca2410360080d85400b41c2d9030300711042e440c039a2007100050302c2090100841d42c0c500a440c155a03240c05040200001c1c8084104420415080320b000e0b03031042109030134207075510300054030b422241c194248030805050030400000c12902c030a045551b960790382d4996580103030354040c10020091107507d0b1754401c019181040024032000c02e001c014000c0740c003407200003841c80c00014000d00005454260300e010821040c42000d0003501e000e0540c001e22a2912582070192138141c4642800a282c805005081c0031031106 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 64443492 1250 64442242 64442267
    0x203220c080d0c0807120908030a0302030108010501061716140403030905041112041b091805010b010518090c0c010501080d110a0f2402030106021b030a1a0a09050a0c0302030c01 78
    0x601c45d060605c2900c81032015040c200981c400d002040002080404040000d0301e46841540e1700942d60790b04004c14582540c0301a44410113101c1c8600a56100045804906034008001c01d554404040d050310121001c1c3d487d90713030314419108001404424964084a0b907400c0c0d85c01030b6024030209c0c0c1e0b0b15034410200d104501d00c0c4102d03050100702140c002041d80d0301c5030514030090130b00c1c200d9098a40715070700700b100c42c81510443c1142401c4261020004280074810302c44100342411403c201590703002c48108980c0c0c1040074407072041c000025001c4030b4188141d070703030009941c0d0007049150b0311240780541d64030620901c00c020482e0080088402000007426242a50340195a98a20441c940c2c0d0200000080d0f0402503404040620f444031140c000d10107180200303444d60080412040a1010702000c08545c10130a009420030044030000c1108820140c00142280340240070950b034014040008040c5124010018010706100e0028040a018501d055038001c4094500044400d401560030304d00c05070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 64444742 1250 64443492 64443503
    0x8070602060c09100c050a0206040e070f11030a030b0a080105010602011e06050d0609050312090303070f050306090411130c030207021201020c0604110411030103060c2007090203220c080d0c 83
    0x2041811045c81203c42c018018031079000c4884d14141b9500082c040c0d045a00011443c6440108110100340c2c4030000307000c100f5440c1402030380c5003003d0403110303280c0c410001403506050300c82080c45100d840f51408076000b889103000801141d40c607180c0080c0a45107a41c00314041c183c10f00c1100801c1301d100e1150104a900040c00450980000e0b0340f92005800b1041080c1c840340030030301003052401e403004145031003045954051a503c0c90503244c040d061890281c80d181c00c02809104001a6480b03440601303801c0b0340c02482040c08000d40320b00082c0c1c40161983c0310f40e01d40e400c00740e140c2c2080b0341540103000350510845071300c1038034500050940e00300d0040d9800041594040d0001c6400b040000ca40700c48a940040d01c082035443c112080f001081d4002c0c0d1044030880d9031100c1520400e680008a800d2a00e01994007206000012024550b6003202d80203c0c03400560020108080b840d242042400143d038003402c0c01d01da0001c070b00382151109000e104810050040c0601381111038814003a0514040d4440c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 64445992 1250 64444742 64444759
    0x6091706010618090504230708120706020c07060908011103041a0a0e0a11090a0504030503160905040e0a021906120929070f0f090b160204020408070602060c09 70
    0x1041201da000c03040a0302e10f1994244100810f5680203402540e220f84d00403145110504440442c0c0c45c480700e41601c078107042d90469001800141d0b03000c1000f0520941d4921036903120f08842c1800402846488483d0344a481900c2002520340c3c1c100800c5401c540d00d81c0000c00032640080c080850510040314006d1520080c1c00d1041d800e0054010319681000301c1c0d010000d00a440c0700e031454900304016000351340b140c180c40c9501c949807070078840b01a44a0030814080c0010704040da0701800502000c0c1c14011454115181c05140320710030300c100401810010400d100d050740c14280035884000c2c00d04c0c1a8066038828950600e00c1e5a000b00d000201e8a0940c0c508800c419850340c464000e0010b150110b45d01900403030042081e950700c0030a8501e91444907807041e01800c10100141c020030791100403500344180e1841d00e18405800070403810403aa0710078400d40e5204000940d40007406c2c24000b000f58404d202090114500500080c2281555031a4084805640b40c02c2c14407500390150b80c40203503000d0780700e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 64447242 1250 64445992 64445999
    0x70810050f0c0a020c0406060512131a090c04090803060405091c0522030b0f100312030c020f100509120403050705062214040c0f02060105120c1201060609170601 71
    0xb48401020110103a1044d11050300f0010000b4054600a80c4400002100070078001510035407404d05079003120090444980031030981d0b403262503510401e98100c040600d0703e80003501e202000c1c060716402c40001031003000f40d04128034002e001d9400980c0c545001d41d02c0c150006110b5400042c0850750484d20000040e50380b0b1484104942561000501c0310303602070002000c40c0398485020228003d54824107602c07540386080f03281c0d109010030080c0000310b40c0444010800c0420403d8820708000b252524003c00c20120a81c416440c10170300d80300d102807a1142d01d030b8000e091030780c03a4007803401a000c0005803504c0200015100303140d07010301d00002d080754210450410a9181000c02000100d00d4a807100521000383d80c0580b0b400c400550104210750f00088a14101e07161600c10f20780b036141c003810007144c0d040110794002e550b0401401800d0041819500036840d0200400c50001018001010054009021449103018000a12401c030210755482000300707580f00920049081007801c08001c000907840d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 64448492 1250 64447242 64447261
    0x5151806060d02071a0402030c09130b0c0403023001110f2a0a060606080f06040b030c060a02100c0203030903030a1505120a1106040b04030803090c0a08070810050f 72
    0x81080b6942d191a801c10a01000881d40c560303c1011503d640c04022092070305006150820200850780c600c1860800d0401291041402d601c01880d034000007190300917514210b0064079845180c00103948800c0c1914040d0005400614001c407144641c04584000900b41c000e043c281d900c2071610b210b441c0c00034046070080c0b00300389001e0128000c4000070785c8000caa01a00070802c402d400d03080300d49103400903140b00c000d01c18280200c030300504003407410083c070780381240540c00c4890021308894403441d290495007426580070002c4031460803005100c0340d0359085505000e0364840142d50a07400c058100b8050841e80c1e400070050f0780c03180c020030000c1c502d507582d000203940042c00f03000a442d201d8144d001c0007007840e4403081a02078940d40213500400507601103048c00b1a030350340045c0d00144199400c00003800f880d600101034500300c03684107401c2902ca48404170500d0034900d50808441e0411542103001448140000d51882218481030565442e8050103150b40255001150349a40f6050880c0c086000c00c40b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 64449742 1250 64448492 64448497
    0x70311010b01020309040203040602041205030d111303030e0a0807060c050c040504050a0305160b070c060f060602070b0d021606020406110307030f0e0111010608010509010c0e030c10110105010305010515180606 92
    0x40c45000300528cc25141d5491880211072440151030341d5102181c180300b041c11910400e400311440000c05400c0c95000c45a01083c0304403408008e0800096508000701c81e01c1c0c01445101518003c005e440020352501e40c000d2451642e4034058a0611030000108074a0a02e4426940550f4002c0060221801261000c0d104c9500844588001030440207100010602010120307003e02c0066a84404010300c03802d000c000d807000700842080d040c1c40d0080410440d0b400203005821115080b484a0300c0c0d04c0c000e01c0407402800780c0c41045600d02031340d1420000b0001142d0051060f034500c2d071100d242c0d5104000c4100e07030301c1c0034078240100811011107034580700602030340302400d1440e014901800308040380041103095134116480369150341e44407424040c46035030038098581c1c58002840d0251014030f00e103001039500c3c0750050b201c80c000c4990b01010041c480c456407002d42900f252200a02855035039240c403a00030082181e103c030f14020058500c103d07500e089617054101c242007800300002512400200304003503 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 64450992 1250 64449742 64449751
    0x103050c04030813030c03050606040e0f0c0907020c0d1101020d02030a0e040f0e030d0f051501090306050601051b0607090e01150e011e1706060f1b150903070311010b01020309040203 80
    0xa4031306a500200242800490703a014501c2000030b45540c1c00c3c41402e102c2500c940c071501000d2038001c0c40520740810b1000803080c1c0d8846e0300300c40f6400591600e00050b4200303201d61170a1074115600880034028403078004000811280280e00702c8140c490195400c83c2c0b64003c94008000090f1220305604452074075400c075065100c80040300003031215a0412042c51680210b203884030139a102d03c0e2017410402c091148980c09621740d40750603080341d07035080000c018424a00009195980da04041011644103105696014242460544c2c0c4504040407a03940d41c02d0490359000011915a07011034014208203d02c0d04948420426511540c900d00c0f09944908000942074100a074102c41e1130015014a00c1c21550f02000b40c0b201d1500c0b010003000050a800000d001d58010041040079090309646e80049507560f25200d40c1d843d03103c51640314071741d04111000d06441280f41c4110f0600550380e4010004000702031090311001c3e12541410700e2a4241c605020499025820a1045080c54201a0002c5a00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 64452242 1250 64450992 64451017
    0xf020f040311030c0306090c010c0c0e09030c0d0c03120504020414150f0603040b040f21030c030c1106011505040503030d0912090e0c0702010c060501080f07050103050c040308 77
    0x1000002606955540c0040d4010b075a9040c400c42c00c2e98140c20309000000c2000c0081e0090309032440d0860441c1d555090340c1045504100c0000450014040f0429038a0003a200b0228840c050781440800180d80e5001101000010700442101062050144d00004100703589602c900c10602c11420051004040061069811613107030307040410009003050102e4419590700c211004102d482c481400803c820703550003640174040410038400403503403842da40c5500c1a4069070080e12400c05242000000d2100f0b01410841c801748500d46036030640682103205007a0350360b50108181c1c8072680040b218480f411a1a1a2a822520051002007020320382407501c202c040c1046e030310b01030b035a8020034a1980081040e081c1e45546041d10410071040030211014400c1c6482c10b25019418500d10300d4180001400704003810b14001011750441e4000c1e07560060f000d0300030904102d0380da95030003030b95264101902542e207140200200498150f000e446034038024a4107602240c00c0a043d42d8943c41c4d15402904642107 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 64453492 1250 64452242 64452247
    0xe150909010308040603110702090406051b0706020301170a0c03030e0102121602030d08040b06090402010c02041526070905090115030804240509010c020109050a06020a0c0e0f01090f02 81
    0x211034031000d0405000314424143c031965a450544002c080f0384142ca003c00708400c04208010150b580c03412401d42090308850001002d45405c1c111001d0040c50142e21100d04401007044c2c405c2c4112030340950704a4002440040d1800415902144c41e1a1900002441020403e03410b00100384035036500107a00c1010b0045981032a00071185180541007003000c00a4103c500d111201142401d10164011030f43c6030801080a05040c0d5030b4488418004181d01d0080701c250300000d0035607100c1c480180c801a0050000c0244290099501c41c802c0617a02448140c0c0300e2140010341d118a0b507001e942c5003c03c5041c0501a40750400003d00050710f000741102001e5929034204011680e810007400c3e001350b00c40d01c0303502d80d99807400454000f10664036118002c2495040c00d0300c220316411004641110809182014140c812840182d071501c0311a0001034003e585004082486500000c91110040c0541c0c40207540654074860b0902500040321600304091000c3d00400488110760080503049401c03020150 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 64454742 1250 64453492 64453507
    0xd052a031006080f030301060f0309030c02120a03030501060813020108090309030102031006110714040209011403090102070b0609061804060e0610090b0f0109170f01061706070f0e15 80
    0x24030304004415030340c000d42e684403010454003008010f054446040c59018608640c982040600608007010003501816210b200392000c26214410f0a425540e001380701c92803e4490301e100954407401100704602091403c0004540c65000c0d038015880b0307000e50044000303181d450354011a00b42c1005408501c052006204040b40c0750303400c2c0007440c03281c01e500240040591408800801101c282c9020a046401c40842400303058924002240082420740d40540d4401b0040012070340300c444120842403401b0080144500c00206400070300002e0701919051440e6258401008200d11069900642c8000001e0035041001c004d5582035034003d00881d80060985100c500702c0d400e00004030307640920010144800c0c070030742c2c0c03c07031045a40b01c04061f070f24940f040d400300b00080c004c0682d0b03018103860010151031106031040100301d041c00c0c0c0b011000003030242aa4500d074041640a614440d42c44a000d150001800c0d5131207801c5100314801c032540c4240f05411840240f0111744a9800107042c0800c0800034003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 64455992 1250 64454742 64454749
    0x2105041e05120c0c1011070e0c13030309180b031c050f070f0201080702060f0c0d0207150b0418030503041509060c0206010305060106030213140105090306040804050a050d052a 77
    0x20312101045001418481d04290300f0081e8107100d081c00d9805020506e0006d41e101600018400103440161034200c0d1552900c000001e101d00034503440001e150040240401003540c4800310000311003181d00030006000030030103010182e50b100e01186400d0352010183d007440e40401c5044420b202d205043c84c41c604243e0003040d0354282d025100544500340c0c4c801380d640131564040c52195001d0414030242c010390900c406544030025004d0810081c0ca0300100e0503180d0140030740e04841d00c2543c0a00b50820030030113145408054440101078611491070b00032400781481060304134000180c1e06560712031455503659171301d40c1c0c2d1140d41d000707203200f882e44d841116000804500c41d00c1d81c00d03410b40c0c000701a25813452600303900d132103030503040601058010303c0480361120b030880850003941c004000002d900044280101d500d80280d0300d009030326111b00750a210502c11403200400035160251003e001091311031060003041500f49500414642c001d40440c0c070b6103c054001000c9046c001680502610b140f003000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 64457242 1250 64455992 64455997
    0x7050d110613030605040507150c02011103090a061205090c03060a020f0d140f07020705010c0b0a151214010b0901060c0606031410061406070f030203040e072105041e0512 75
    0x4c0b40d6240d0b0f41c0c801c1c84203110080046000624654400c403919060b05200102404030250000307061010282501d01c03003280030300079034501820180820300c155507a54030042006610418907c9a02c2c070340004100441e502081e030080400d406001003640e41c036108003450085d480070156079040d11003030000185041c4d2a001e684404522608150914200410840401c4078003400410565000030420005640c0111074980e81c0c3d42c01039820150340d0364202c040409801043d00341c2e100713429410340101e0007048852015a80d0350198894801010108901078202d03441a0f0030759500508000042091354880e0100d00f8141e88900c40200d04c8565030340c0c800d90061141d031240603c0d6000031440c0b03100d05c01203200d0103009088a600403559020040c012070020300c10018080c0c685041c0307100e1001418004c1046600901d22071300340c1400d030329005000803c1541d10021800c100030301c80b100c8024011144c001e2500558001201c807030072030310f50403401d42412200700003200d250181141c00c540702c4035580003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 64458492 1250 64457242 64457249
    0x1060207032013020d0b0904020a0504020d020705010207030f0f020f190201020a14071802070b010303180f030309030201030e010b1e030f01060b03010510081308070204091b03110307050d110613 85
    0x141c0c0ba0076001255400f0703034a0881b0301c50302802c002030400001d40e41e90780e5103070700b01d030b105840c0165100c0401420f00c0c080d100d0018050201c0d80005100e0701015801503042005162aa03034101104000007400ca881d80e110b0100c60100398040ca420030101800c0c552061002c1d0703c140110341042c08242d480000b41c1c495401c82001725080a2001c020251a143c2d0000011420f1401185006007030b5842100001040c007001d4100011840040140000c0d50520006040b6030321881050641d03d02d00186a5542c500040f40001e080090034200c8450500035000a0100108004100c1896250104083c08500003199241c0314450078003c0c911020b21541001e05540a140b596a40c100380c00e0281152002502104001040c020004c07202103462045036016484560306507191407600008010304403050000d00091417451260100c4080c848200b01164070885200748280d01500c201500c4440d148900343e0005640d071400c5e000071790a008110b00318007000f481282450303040180d000c0045245d40 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 64459742 1250 64458492 64458529
    0x5030f04032105090d120603020901262e0501031e0201030f0f05090f070b0f130314030304020a08010606020c01052a07030c140d020402130305060a06140306010602070320 75
    0xe84480398158006d142440040c1c00b090103005640c0f4581c0880e003004c205215000000743c40150513250745c0045000c0c0b10f6108905000c4690041d103910082c40d00d9043e00605000d098030a10030212580c0c0c40c0c3c084e543c100ea401607102542110f0004841044842007507040b030405d41e0b43c0550070b43e42d00752442002889101c0c0c4100140b10b243c02003d0519180c0000030300d54080e848803900300b1138008240212a01e4000d03408110761120700003e031501c4080040d810082000189120302c500103503002001c1c601c00d44c02100e201076129a1907403403e003201c0244c0184030060704120032080080d4000d5000b8000111a007000b10380340c90480c0070403c1032407250072a0014a0304004002c006000c001c003114009009404004922203002e0000203444501c1100000c1c003907600440d803042c80c02070069074080110b80060940d0401d24100c00d01307034020f00690107120210300750340702001c05500f000070382d080c169001500100390480c115210302e04100720b15210b280d00040a60074801c619120145d02e910380c000d070403 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 64460992 1250 64459742 64459753
    0x51501080c01170411060a1e0c02180708060d151103010e07090f05040b03010f0f0f062916080703050a081612021608041805060105030f0403210509 65
    0x350300060203c154003201844106070381c418880455141e07420601e10f0401103c00503500c0e030001c80280c3d103034003041c1c4200061184003d0366421158105032280101ca1003141c0c240390000210f4074040d20048192081d100040d2002c0000340c45043c51442903c5440c0910141a400300708407007090140c808074058024080c00c0480100101d1314100c0040f500b10130349003010078000c0c2c20491460f0408003d8401c251140d03450f480d444082d07032029444951002e034041001d01c0056100b4255502400014644031503043c5448400030b03094964103003020ba03030201503070a060b040c101540002819040041d50200c002c071100d44e00400034a2210013807034924420344403151500d030b20400103000008010104031340d401007070a030b20041680c00303440825903000060005840d41320480040030000d6003614010003413200000d010414203010741c01401e07842d5012074103210070b5450400445460205440306100c2004107800f05000901403000c0e03001c94550700034003005664800c8442c80039124240c03a400c06031f4104 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 64462242 1250 64460992 64461013
    0x5010216030f050a08040b04020a15031b03020909060d05030f0c0d030c08010803070609031e0207090b010e010813060b0913110901050a090e07050402040303110601140f01030905150108 81
    0x1112031000402c549080c00c0c0e00f0008804800390140f14010070080400350880009021036440b100040d020b01075519600000c10803038240035000780340a4030130900d1200d203a018a01c0d600c2c8640211668048040d0074500c49072900383c1031002030f440c401001c540134041403064007070069079040601004402c03000200f040034000c84010702110004403120042055400062040b50400001c132000796501c480006540c00041c00e0456400d0204401c0c3da82103400001c45903485603000540c2d0040d503035507401c10031a1007405c000641e16040d00c1e0402d10b010a449070000f8803250520f02c1e004000300d01850300451040904400518500021101200d44030320302142c03901800a83c848400c0c0c4a1805c1d5544183d80d41428001041c100071031151000903a150328031140020818040d14004040152055454503101e103000341c0390001c0b41807101003510980000041301007200300010300d5030802906083e00c1c018800011030242a205405540138402d25024038040900290124020720050024000d41c001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 64463492 1250 64462242 64462247
    0xb090a0c090212060d0204150f0501021b090601050c01151805060406081f0603050f0715080103080d0c021509100b0402070503030a1e09051b1e010e0105070501021603 73
    0xa80005015a01c103203c07a800d440009904a5006401200c9414000000d0b10000c2c0c090000d10f00207070b0391403135502000103500c1036803007030441601c2c0f00343c080e5045544030031b01c01d25400701002403440d40b0a56032004182c0c1540940000d148465003100003042e075207005c118503c10503003180d03c00082c00d1701e00c281e040071204846c0304482d00b04030200d0f010320000b0702e082c180f903a8030b80480c041108010300017005403403081c1603a40a00300031039100d015580079806040129031240b4107840356462071604240c0300580c3c18031404007a8140c03940094480d0815100844510044c001500d64400354440c140303858298420845289120f1000d51000708405145002024292011560103a010343d0060000000094010054075030105841c4000501503c0c1c210f203003400951031400e0303016180e18201c2103000307001c00401e00c07a103000400c080d0021806209810f116490803541d503460314411160340c44401540c40344413000900c010524260b41440304a441c0c1900326840084242000b01012b00214100754 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 64464742 1250 64463492 64463513
    0x6190c06060b0c0c0f03010e07080610050d08040909060b0d060b010e010c0c0b0705030403020d06050103030206060a03080304060b0a090f0207170715051306050106170a050903040608130b090a 84
    0x45012007103800e103c002210359a8950003943c016105140503180896652401d43c0020098404a8120b810450390303043c46c0c60300e41e00103507580c3e0306203031140300c003c1098241101030704285548086c0e04e1303103050300d06a2240010000e0940031140e5640354042c090341c9a407070034849a1803502401002403180d80c2c1c48005410410310070a10390502c0409440c4001040951a86c0300495840b00d1031103507542070314035005082d4491030304003d51280f1681d08600620406a121a050302e10a4084903025118241003100300049480010f15a84040001a00156007a00004800c10010b442e40a0098545403500140c418151010700e40a81c007045000604c4134810020a102d130300060850316048154407003011006460b00703100c00003a02c5401061069181c0394800101a410290410155860304801030682901018000c80d00e405d900104a0910b00c1d88509070054103070400440c500b9207007481c00c0d61221030040c0b806204445103040c510100c3d0645014030b01c107010034006024020142d103000302020 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 64465992 1250 64464742 64464749
    0x15150f02240601031a0d020415031208010312020304030f060902010201060302030f030a0207450203010b04030302060601030b03060106030908090d0b0108061503030901030b2205070e030a0c060e06190c0606 90
    0x901030241c4100280c0b1144400c511b00c6805580105003000c951030110030b040c540d80c1c002032030600190090841d00d58002c90171810f0b64803500d003801c0c0c0c601440c007040342ea9015600018124041100f02c000024046610000a4502c10700000c21003d03917980000b800c000600a01820a800028400078901c1d41489002d000d80f0b400d00c1c883c2e028280c034034494819100100d00300303500c3d008002e60b00001040c04c1000242e401101102c295030300d68482496116a80140c80f08801521410021904960281c0640c988500002d002008968a040d0b01140035004151007610f8000d8200000c00300c1d500d514200750300f1603004107201c04c1594504001e0394944a002040f200c9001b0082410f1341d8555008405c4400c1c2e20743c24a07010401c118503034000760a442000441111082e032050f803010701f5540c503420107849008aa1103218081500c9000d26407070350980c1d10020500421030000b4007980b4004c002031540d01002500071410f000e824007030784d410603860980c2d050124070702c0c0d60340c035081003042d00911028 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 64467242 1250 64465992 64466021
    0x618060201050405031b070e0403050702040605060304200f06030a0e070e010609150306080f0f06060a050a0306020d180c0807170d0807050906120a15150f0224060103 73
    0x2140b40c0307500c0d0592a03014100c0d2100b41d0802e051b09201c0b448100704010006001000c2c48641d2a042514021f0941c3c0d2000408238052402c0030f800040602c1c103103090300d21440d0030480d00004905150103074840c00c02c0c0c0c2500035070b0169140c01030010f00e0300c41d00095441070700b00e0b0340c0c000f41d14035500044074507141d02c070b0b440b01402020080040c021701e80d100340c1e010704461280107040403903524440280d000c2d14250300074141d5817040200c281094040011f560364082051019501d10380c40d180c0610052100314050749420017100101000080d8840d8000c2084040c0c2450018800911880001d5a070042c1e074415034052802c00b070140004002404080000c0a0714440c002c084030000e0b442645501039001200d05003c00c140c0028113031401881210721680008100369940c40c10406e0700d001c1c0303803819034148218620b0320000b851000041c83c7c501c401d0311815840e18280e103108130b40444103d148101c96034114010303100c061405103070b2024140824a007002001001c1d00e40b841c0010110780d11184075801 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 64468492 1250 64467242 64467251
    0x7050d02060a030b03070e04030302030403030e06100311060d020403050a0b01140a0e040c1a0a020606030d050415170a0f0e0d0f1101091b050a170706030b03160618060201 75
    0x181d890400702c8900d182d5a00b0701040c54209540064246030b0303954081c26040c99030000300800c066043c0e0056100c0e03446500c04000e03603100ba10907265100012074100350b101c41c2d400d43c14000300c1c050240c1c50b070b80355200400591030804a07904a40603a0001d601c1200d059100c0b181d50b400b00704003880142d0240c806040071000381d000c82000524410414416400c02e109001d0100d000d02c4200c4181c5000340401510200c0c80d0f440e030700074400490f4041003a5000600a02c0c000c10480d01d400b00d08001d0740c207119503c0c80d0a0030706051182e28242904a50542070002c0c181460070000d4610755414400c04064400184410850407910299000032035000740b00d400c500c0360300602d07580007030415021140925040c51020b11050007180100203000001c0c0c8410054444c01000d80c030460300310700540d00c05441c220b101c6642c031010101020281140d000a6800051f0213000b0244242d0202c00c441d2401000c50713024400301c100030769005e040c0c1c0d040300c0001044040301d00c0c40140e13201c006000419142c4000c01 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 64469742 1250 64468492 64468519
    0x1d0304050924040203151518030313090b03100c0903030906030b100e0f040905070f050a0b0d0f0b06130905060f0105041202180f0601030507030b012010060f03050705 73
    0xc200c40c2c250045886941d020002c520f800181003249800704002a144030100009800700c4c5a0701d401100000032560a0a442070285090120684080b10424101c8600003420280c2000280c041e1140f0341e07802d40306400c1c7d588001103d41c01190006465500d078402c02500f941401404d880158101c042814102020a0307899201c40c00d110680f5061032030506205111540024402e010800031180c1c003d04200102040c088017041060454091036a10209156240d05101c03038140f0f070b4400d5920524090140741001071854000c031040180d0305800160002c090800540386800c06480251590702c040d0052003000d641d031007148e80001d011a1034492140911700020719a104502608070300048144e50340c0215166000054150301d20704a03504424500301d801866150022564140064103101c04940c1c8180603110341c860034241a52003800c0806200943c8042e45c048280700c119910441e2000400406940302c1c20014144529440d1f02051541c10040e2402c06183c100c544101c00303005030103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 64470992 1250 64469742 64469791
    0x110d14070f021e01021b03031503011104060e0a05040501181a03030409021b0319031802010e010e0d050607050a031103010b040302190905040b190b010207090f1d03040509 75
    0x455010340348581e094440700c183c4010380a40208284135031104e00c010400500c050021010354410800e0907920780700040c41201b00740c00c0c2c2e10244d0654401c400104070038042d891003100301551660001d0181288141d40d40041000c50b5000d9124a0400512075140e00d40c8071440c3c000c0c1d0300f0301c00916010781801c0f21090000b07a142d01c11031084140e165400109c3c3c41d465540c01490708070629000055030740f909038180041c0d00060071030716000c0009181040809440c80c0441c8016a01078060b580c1c001200380550054404051039420700707600525007414071002900400040d845034040e07517102c80e102d11036200c010703042e0303120351446800b0ba1400b4801401000d03860350545d400c07a03030110b680b20210101a1501c0f0125011034000000da9401c00080005200402e03110500640b50302008000c416003081300c1b00204c07825000041d0050b0031212082142060301c0e0003036100030941000c0000d07441000884090003a407001c0680403240c1000c00e041006140100d42a98420800c01c00c03440b400c914031703104 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 64472242 1250 64470992 64471003
    0x203010e0d050a1209050109030e03070603020310050d08090910060f44010e0103020117040c0608090f0708101103010b0301150e0418050118030804080d110d14070f02 73
    0x24804000b00c80208100e4031324183c0242d40e049030010020000402982402008043c1e003031441c6009102e0900005912803091003244d1054541806203001c05040100700300c10628400d0064510b5041800351040c0ca0f41c86070b2450340614824640200024500748020300640c0051122109009071244603008610403003c80c000b00a80c42d201c4010b0b031020000340c401d08518440500d8982d05c1c500400401c400089089442c10b0720b001343c0710301106070b4078242a038100b0718045500512009030303110308102d25405402583d07080452841510343c000c070300b01c00c114038085a03070380004040d5201607059008440c0070701c0b42c04440402245014503541c10a40420403503c0180700e02103018450009842d62248a4841c5101d41c28000b8414005005e4100d19031804241001c4151815464162110038a4091102c0c4140040d45074540d1003140d500d82d12109115005201d60302c40064440d18659180c9042c0002880c0c0e411508900040d06c5005222868070203200170308060a000c2c2c8010030001c065000140c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 64473492 1250 64472242 64472257
    0x40c170a11130609050a090204050117040206040b0c07090b030c010f140d020c16050603070c0b0a0e0a0b040c0603050f060904170c030403050f0102091f02030705060f040203010e0d05 80
    0x301041c10003800078100c00c2481900981041c40034204408503c0c9075019200c0d0048075000c82c0c050b180303543c0352a4106e040348a10302c00d0034081070b003040c965182c50b022141d1b815401400101418240343d5503185c540081d41c404220b40780c180d0801d071402d200981c60fa01c01c004681000364001c061000301c08002a02d81d10751903030a0000d104070f1038542045201390703104584840400341e00030f5482c0c40c940d954042d03603680b982078285201c41100340701041d40e0809000752071040220f6a1000c41e081a20f0f25240303002c00d40500a034940039142d41c0c40e049031510030011680f06601c2001c1c0100280f50a041c039042c02d91130307070300544100743c01c00c001c0c0280e0001c0283c50179040f5400b01c54088076034542d0314110980056008100506030004a030341d44e004403010020b00b04132801001511404141c0000e424207e104034a00c240d40440480ea02c2d205a00c0d00080e41940b4803c0e60045034a060300640702d182c031344901200d40d501c080d0000070401007107080070301543e80b88a40711002488154810706010f03280d40900d02 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 64474742 1250 64473492 64473511
    0x3100905070314030d1427060a20040e01170601030201021506030f06070801050301200f0703021005040606090c030207020d080c2b0305010f060212070809061206040c17 74
    0x30b011000b1035101340700321048038441070020400c0c0900a1540701c000001250042d200340c451450f07140382c001020b0500c00f42101410080c00040c2e40745000701e4003e0002c242c075030400140c2c0b40100707001c5200a40082001e08504c040102983d80b41c0068140508030210404a03603130040d400400040c0d13000900d1000000040350380e4012a610903010078035200d19610200c1c0540f041805100c051600003140d141690011780c02440324850700b8001800b005007000303000032040d82c04c0000e00c0d281c00134100a051514800d10542d00300a001e00009000d480d001da8094034031980d030720001c02c545c030075a1040e81e4a003020b605095052414940000e5204481d5200103003013010001004040383c4000e10004001040580b4001d2690406080e03002c160765242c54840082407501002190301c070070b000340b074908650940d401407541511b4840c203104c107034002040c226000380d018010043d003039a854000d40002d418086083d040c0346050301c101300c1510900ea070300c041402990105104540b1f103040520368017031440d5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 64475992 1250 64474742 64474763
    0xe01060e060a0e0106030b0f060a0f0212070c0311030f030f03071b030e0409061503050a0506010e2518080a0b151c110d0318150c0b070c050106060c02031009050703 72
    0xc80401c1070b00c08d41807625a441180015184480d542100c0c114842c3e074032a9085460b0501100400e030740d0703407103913440140244e00f42c140304200103102d0241680401202a0a4421a52180006a1a6410852018107490004020040100d81c855030782d0344503500c1840c290b4410500383d20090724401400f5141e40c0940d4642d4003281c140203c41d004240c05101000d00f41801655a050050721213a17030f100c0451743c50003420000035401c400d100001d070168002c3d42d82d200b01d006141c04402d00802c450304100c0107100c1001080c0e121400403002c04070083c80301c04040c050503519450b0603080c203603008242c84040700b01801c05e120951140c0c060000110000c54082c41c403001d56081c1410f000c0c0800000c103a000380b104002c0002c0640c07201e90180100d4803641d0411601da10f8286021b0110400742c0d0810001e100442080c01140e500c00382e0580102d0f0368100084000c0040c0c07215429a00b26410400203c1c48500c0014114282040790012a0a450300200038220b00b03541c40c1a12807045200140845019 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 64477242 1250 64475992 64476011
    0xd0302120a0203100806070f110a020a06050703090f0311041d0c0d060b0402031312082202040b03070906170a0503181c050c0a06030203040b010303210e01060e060a0e010603 76
    0x4880c0c000a8070170724088681c9441c0841008110701c250303245c00d00009800c40c1031a405118002042040c50f54000c0c150000c0508000702100d203500035120903001c1104180c40040e4149025003103102075401920200100c1d040030082c0b009403103068110a180918640b44000c01010118403640120000c585001c0000343c14140507026202140166611510000a02172064070004c00499900d00c034103c0d51102c0c11140d04140d038000c100701c405044101c44040000402045020742c224018070003040041d2484108001c24074004441c0c203e110f0b0340e96109006e0005014010302d8003034541825004103402d41841d91029128051a003821110002c4c21140903041da558009038821061700658214245459003001a50303503070501807a40c090112200c0118070301e4842c4c008c50b4440c0360001c001c000c0c00d918603138044035004001c004581504038283d100c0d94082616001c0c0710a140710500003c20342a0900e0403a2111110107801d45208071180c1408000c103248000d4a10b04440040c00c0000300c0580 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 64478492 1250 64477242 64477261
    0x290f0102030706050f010303020111120402060d02040b07030809011a010905090a140907050907080103260f070b0f150d0b0603030405040c110106060504120f020f030a12020d0302120a0203 82
    0x1451001883c00e4101002c0104800c2c211180504a034001d034000d0124140700e10080015103d0b1240c0104010304c40c07000a0b0141c28540010510340c0e900c1d420042c40c240d039803488145203400c0140c04900181020341030090804090042c400c107021003078089030100303c0c81000644491114890140a540543c00240c1d10200580c021410100d000441d1507091410070b00385900d40e504e5004543c82810503201086000d403041a4580c1a079502c043d602c07040e0341d0308520b6810100159075182c000340310b041103c0816480140007404c207079031144004e250181009114554412401080d01031564610910104030b566822038030f990303464000084080a0710340001281c1184259040726410a04001c04401042d9005540310303a81001e050003040390329110302c0111954480c62080b03e480b400c031b0f40341c3c1001145a107030514494503c000c0110104026a82c00b09040c070301401001d40f8141001096003030300b00d03010b0041c1130802c0c100d40740440c6800c8190104401c020710162410b4070700380e07010002920404 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 64479742 1250 64478492 64478497
    0x13020d05160609061d0a06110703050d1701050303030402180a0e07260a11010f0504050904050105040309060809070611150f0105031b1003020307090b070b0a290f010203 74
    0x1d0100e92031190751038480c2005450040c944c465800003510003070300d4404070070707030301061a95406004203d04021031078414202c9040c0f003180400c2c40140580c4a000000401c10013090041c0b481c50380301e049800c000c1040303003017020b501648064040d0700100304000040e55078110f00c140d10070394800004807a49594480c180207103140d009840307503442038182c08105001390441201c034404203140c901082000c00074503943c480104820060158a503928200030075030184401d48107804680c9803c0b030410b41c0c0c510025400d40d0003600d068400c1d0359654140002c4c03541c45101400076107020b003000569400c2103c0c0c2c09690310f0582c07044000704030320007200b03400f030030018403d13030003d21205a045265400c1020000020820a202d054403038400c00c44a500f00c04200c0c0c50103800840d0080c5600c00e00c01a46000b6000b0790302c000c00310760403c9401c004c0070611003500006006406c0c06018220003500d0880100701c122980c204031841080c14082c20300d410001c81d002180624070003942d2084a00e0030500040c0e1550 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 64480992 1250 64479742 64479763
    0x30c0c0f12060509010e060103060f15030804051018090207080c0618060709030510020a0201062304061a0306040e1609090b060909030a03270f11040513020d05 70
    0x1100840d0010751645401e914400e0700d401034200308400d4031040c80d01c0e800c80310960b810b96600e401080c0100b01080d03455019468503000700a0126400248210501180f2441d4104030740480300481e00340180c0c1446001081c000d03c003400c061800400d04480b004100d03849100e0400b0194000882d142080b51a07001d5505003400903007100c0e01c40c1042074403019519070a10100006110714000038081611407150801140c1c1c211001d420041641d00b1108040c2d44000e12010940d03407a0f4200252801c0f12a07500554a032071039070303441e0094100800308000d4481d85d82c0036141c0420328580c204070498014044030b40140e000c40c0c0025041869032001410320404400c19680d07400711030800520b6940d0390700220352031407280f1a00f2170150385039003c100020703070255145c01d0a60700a10500e42418040e92107501c0b50b2081c0310302241c1448143c0e0755611006401001281c0300c00c00c2c40c0781141080381030390321101d1003201298140000d00d44070040d0300f101c504403030000e4450045c0300310210512400780b01d6050750 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 64482242 1250 64480992 64481009
    0x5010518040609021803210f130e040819030213050603060310020c0307030219030903021c0c0f0501021c020d0f03020f0a0503090d08090a08031e01090f06090504050604030c0c 77
    0x480d450f4030114015482d40302e800e18001c0c01050700900c2d20000001c004a00c4000f0807642a080c00c0446d0754241503500040402c409c2502c28030400b140744c41d1680303041c2d8401c9204400060b52003d40081d011140020340b40040305160060080025a241c1e4031232500c1900c40640340103460381c0d10140024a001480000b200c411440020070030241c13400800148801d07030080e021200000012040040c020803051070180010b17840304c0c0d0920040c54800e4407010440c9a891218030400440d8a9070014185154000d603036259280e101041256010b00090215038051000501d44140b12040a92504a40c956000c108040c65095146d80d1340254145c3d20741101003007041d0b80342d013980e05c0d000e84190304c1070b210380e08140704d0080c9a0b650280306030949482600f105025124005282c1d4560040e41c0000d0300206004407001407103070b40f040c0001c0782d085c0200407908000c9250300100302e4003c1211000d07044049550700305404c000200340005442900554140380010b4400b9a42c14000303a00e00d001c2d0840c404 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 64483492 1250 64482242 64482247
    0x70b0304021519030e12030c0304230607030b0108060102240c04180609060506030903070b0c190e0f0a0303020c10030b060a0306050f060711120c0d030504080105010b03010501051804060902 83
    0x40f1564140d102026640171003049a155252140d0b80742181c4c0812504900001e00400000c5d000655118000b0028084910440304003130041b400c882c182501182c00d800002d07070361822015030b0340c1e11075612600031b582030000d03210b00382c1041b0440d456150518444400600c2c6100410800c1c204102118000c040d2011440326183c1886c403c5005003800748500681e0fa400d1103c08511441c00303500302d900550070344004502d00a402d0769110b0019a0040812241c8002840342d920011018003200c1e0540020b9910b1003080b0100c90100844055041c0c0c0b51070003030805000600000f41c00140c40d994030401111105da200b00410000c03400b034240c480710340390810808500303955041e406400602c103448041340c0390350781c0d901d50005210081c01000001307403c0c0d565201601446040c0504a0381d10030780810140c5010100341c134046118014250710441c0011000903081085100038072030103001d0f0040c60782072807a55143c034000034220b0081c6075110307043c00a411108803050751142d0289005000d015000d54 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 64484742 1250 64483492 64483537
    0x90201111509011d030403120905090a020a03050a0b06180d050a080a0e03010207020117040f0b090714030606010c030809030706060f0302130b060301060c0215040b1b070b03040215 79
    0x840c1a0400e90b9000c0056003858101524040c0444c010852003070110700646c10300c0d14640b0781c2c40d0084c8169030200103010302c0d120049299100c0006041c415452000090382d618890000103003100d000400386052513242c141e04040340d507214130444145000e4100701c0448072800800140085402c900000c05602c0341020780001c2060007005010710640d641c442c400c96042210500d4280e201d0702500030700007911901710a012000d9119400c1c1c020b0f01519202c0c040d22601da503003407440201594122407651066004124a000c4c00c2102c0c102c0c120305a020740b0749824400000b81c58180daa11005081c007610710002403d000c0100b059880c0070b42c200c4018004559505240e200d0140d1a01041c2d004100101d120f00018606020b40072000e80301508952841e8680001220148590941203074080240d00891040403074000292018108810301c0598071490040843d403144c0300c01603501d145800030f04040122880040580c0d5110381c040d14800da00304400c0c07401c40c909102c1e0041483c05141061482c4c03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 64485992 1250 64484742 64484773
    0xa050f0f041b08091b010c0b0a150806060a0902130909020d120306050f030f0d08090102040b0708090901051f050a090806041209090e10020a0302040b03072a0f020409020111 76
    0x15010b284800181e50012485c11091995034440021250205009228480020364801300c65541701000c581c0010346240d491010300e00940060303110000d107600410601200f86045103481004004036a0214500009620b180510b540c1c2e909c20010041d0f90341c196501035447e0030018240715036000c1d030400c40c150140032000e40200114024540613100701d41901e505410300040c44182e1001c0007008090343d8503d048100d40d100c000401d00307451950280400500480300d000a00a002d00c1448040d40710300070318050100e0050140d012074820042d514504030400b00078581941141c103503280c9590365890603c429031307203485c1c0da500c010441c1c4190000c00051021641c2016a200910355514000c0340d602e06090044c1d400f04003e100c0940c01000c1e401d00c0201c650307402002e81c9580307410054142565070186002c80e800403215140404c900d02c08011401000442c150b0b00e0a0150301c841d0100f0a01e80c683c14103241000fa40280110382d40e41c80c44040d07a000e0720065061180c00c2045620702c03106034541 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 64487242 1250 64485992 64486007
    0x11103160305061c0b0c090d08090f041401060806040b1002031903021e0c1216030e030a0c0b070215030703141005060702060f0904020a0e0f0a050f0f041b 68
    0x3034001078600740100c3c1c3e0340d1070a881c090100003914002160140c1490719040384000c0d001d0083c444401c02000b035850f054031114a514101c901803000740b511400520107000e080410b00c012140300c4c038074003044819904114880e40d4150b91282c50207152b143c0d00d040100e001003601c2c0580030382c0444c6c1d000c0364110280d40040280550b05c101c139000c000d04a002d0000b40c0036800782c0218a208085110039050180d04070074041c09213154245c4c200c8650002251155640e80d00c01034082000300810295001810307041003040d20103080940c0104000c19080e2240f466154183c000c0c00100f4000103040010345d0382d0380301c4000120100d082d019a076030521140c0a4024040461000302c0025003400041d40764861710603d8013101d03000b512151404e60f040c4d0030440e2a40c001181c20329089400d00014025459610282020300c6180e25425510803503442081485011103180b28843c1020710340c140715685580300c040b045898140c40c0519528010400600036003800d41c1d00c1c120301400b0400484480f940041c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 64488492 1250 64487242 64487281
    0x30312020d060308181e0f0d02040504030201050609010e040b010e04030309050106060302090f03030c06040b04021201050702070611031c0c1b0f06150308031617040b0106030c181205011103 83
    0x490004103500c01c0c11306c0381d070f101c0302a242c1606081000201405050680d0102a8504001d0403024818005ea00180890310709690980050395103c0c00c2205a04040c0140c602408104081c811245420b556070001c0c054140185031020b814203010070105030180d080a492694054001c2c0183e940b10380008009402c0b0441e12031094100074032001c600d0801108848985206030090f00c0c1c180e499490391890706002500803600104011104d00500100784101c6025401586c0034000f1245088401003035441504501d81231a0005c000044040d60901080710110100c00000300c2c10700800c076000d42e410081d41031034a034020b0300d1001c1e040400803200c01441405100324070800038080d84000841c6068094040100721103020000704411540041340843c0e00220b6107000c05104500203941d880c0c0110540d03080352101c084400610000d501805094900074080c981084501403000c0d01d244128418480c81040c41005420001841002e4200d0b03002948800381e0300b956400c0405003021a444280e8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 64489742 1250 64488492 64488517
    0x111309031e090501020c04090f150b090a0c08041101120c031506050304050d0315030c08010b0f030d0210090809040203130506060301020f07060b01110607020109031107080304030312020d060308 85
    0x140c1120201d000300b2008054840690090110034082d40601004060f035860a0720200810301030030002924087d00c050f8030401e100d102207101c5512000703000310980d0160511180c58108190300c860b643d400441141d101c3d801c403500712241542c400042e03403c2034a81d100c03510494100b00040c2c10b81c079007640012071494410070340010b503559205800c0b41c550000351001441a0050700401003101d200f600101c800084000004003610798075075032594450110b9010640382d9440d010034542500d4030b28618161508203501502d448601000000d46600c080a1007a40d9a90b0707402404090003030300c2065410008003c0d1046540307052100c07582c081e03d00041d404941a103d84e2000404908040c0280d6144100c085000d5003000010740d07904c0d01074083d50360719a040241d100c20003084a681000014000c00b01d0707400004000c00a41402050285c503e0f080c0d01d05c1d40d000c4032080080f00c000008640440e5054644048003601e54101c880c0640f041c400000c0b2001d04004c404801c2c0310803c80141440c00c0c601 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 64490992 1250 64489742 64489787
    0xf240a120b0105060a050306120705040c080411030609030418020c0105270712060b0402090405042117040f03090305030304050717061e060102100504140706110a11130903 75
    0x700b04029080c81707400211000100c09102285d001d091080b2104414020401641c0b4090748900c0820116070b100c00a420000d5184001e22060100303400300400440f2040d00545118541314003c1c0c0c0d901d204030b12551074403150340c0a10b0079110300564180c0d000000284000e00c42401c048010860041191440c1045402c69141c2e22014280c000b5401080714102c50054924060f2602d440005100e00e4072046c1e04250204518180c1d44d84911455200d81c0c4510080c0d88000f01e50f2481c10017101d0071402c5201441440e800131000e0300c0e142d141e83c950140e1300c0780c81900804981d140c115100403041e807000780a4032002c801e01007008004511002a80c034000311024540a4118030b0030b503111810b840260044141015480c00c2c084448400d0307501c120180102c2d031b003001300f080588045079411141601d410350720801c044101c1c0411700c5500001c0005242c400100c6840745001900c074040070400070503003124918010a5604c4003041201c02c41081a4208414081400c01a00004c1070304401300080500 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 64492242 1250 64490992 64490999
    0xb150102060906160807200f070510080420060301080102270d0b2205100c02070302060409020307090314010c09050303030c0a050d09020301020a09030b0f0f240a120b01 74
    0x60b0b1148510002d056082080c0b07200c11090b01c0648006d010007040000f44d070f01c07558140c0360141d40c01038080e50020081c800321105101c80c5007044040d42105110301a406403222a840e0310807100da40103600090b00c10104d003865403d0780401e1030309148941c4c10040c0400009030490065000e04550350612051400e44404c0081180181c0491400380350300594600c480c0001c80c032120310300360380b03c820039080114134843d4010101c040030b030440d01141d45a011100d05175a4410300d002d100f98481c0a40003c049460455000a4a5014501803502c07541d81c08000628101c0c0710300d184074000c50700882010055941220014080c0c14040c4048010950f14840040d0904000049910400c1021480c60603c52443c0080742c141d8440c100c3c034601c15481e800181c0250b40c080c80241070031811a01c0d40860310b0f04c2d5251501046000400303058840064404003e02520309199180d444040505114103010030801c2000a1861108007140c0001c8040c101040c074002500c003454a00b8000c145c42c107038580e80c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 64493492 1250 64492242 64492261
    0x70e03030304150c02070504051602162402100c05090405061e061b030406090303020f030a05070803070507150f110708041a040e0a0b0a0602010c0905010f0c0b15010206 74
    0x1c1964001c04a466581d0b062520141641c02621280c0443c815501038582ea400001c00340ca4007070381d10122190107802c0007006903804102c10361136146c00c6d901001c1e26a1919210086c18240060800d110002d405c1c44041414400d000840002e0705000c0c0030084460120030041054208841c868010791402c0042019858004620703400450701e5842d2a4038505100c0a10030a500512030300c483c408400550710550a50900141c0050304882d038513a1800381c0b41d414000c0c41c20a0403612201c803a042041914400d0360f01078101c2d01a00d801040c11075036900c540c00308442501c10088045d0840c24511125000c40750320b604200c200c580074440034001c20911070040016032003590340050a00c1c90400c001c01c0560b00142c2c1100d41c015140d0035041c00c050392100c851044180846c0c05041c0240e5a020203801483c144001c1c074003500c154030003040480d074002d001030200e1809009481c14070400081c00380e60113100d81007000d1840d0380301c0c1d8040c0300d500309071002e60910b0030652249800341c0100d400181e403220 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 64494742 1250 64493492 64493497
    0xc0d02031c02090d03110a0203010513120c030903120905030613060b06040608011e080303070305060a0608010b0a080a110703050415030b060a0c03020102070b070e010f0f0203090f0301090204060608070e0303 91
    0x41c002d040191070761517950151040484204184150300401c0c4161016070b40030300c1114802c02e0481030030b1425000910b00444035a4098845105002c000303801ca40200e03034425140d000f0340e544882c40c0400b4001c844401c0d40c003544039501c0302d5071502c521002c11915810803c0c00f00c0303009124410503c443d0050100704174641c003d6000e540d0010344044010446001c64030100709498100080000c14261030300b41d0700b410355100b11400d60111740c44409100d824281a025000204112f191822132541401d0b2140b1881c0b103100700506c100140740740440c00c1c414071075009a00094080e41042c1e030302d0030b4524000d80140c2280c800c000c1c06524100c14004403d00034001c04030a450700524081ca0269514000c2d00c80004014042c2c00315035080c04007500080115051034020802d50f01c41c0d0754071002007000140724141100c00e450030440e10303d11165940e034000080c2c8880803c1111813074102e00041022900524040e0000303507002e4100400081c03844d4010540b80e001e110305585080c0d0846000e42415501d1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 64495992 1250 64494742 64494757
    0x90d0210110a030b190303110d0c03050706090203011e0618060f0b0c0a0b0408030919020a14010e0a060509190602030d09080702040606120b010809060c0f0c0d02031c02 74
    0x44200304aa042c103240700764010401c11100514000c00450400754941c14035542e9003040340451419012140b1100c0c00704030b101c1e810340ca6072926000343c1005a0f40141a030041410050030030362101c8440d811960207400c00c0350b0101078000034641c0200724403055070140c612440380485c280060181404080b00600841e000e44064600314541a480c1094a00c001d070300800882d15540505042080041c55194403640142d0107210001d4585c00d04a00b45030809100f10350108812400d0003100005840d044d007a5000c0320b1400301d4845102c03411500690340705841540059001d592480b02080c00c580000151405c2c0310103440035545030382120701c8170402d03458502540026a10034400401103402c9500080c0c502e40c8501007203170402819038046000d079116500f02202090201251003140002c520655500e075030b0034a40076000d400c103659051307140c94014060040303842d40014a0200842070300c00300c543c203c0354a800c684131941102c800944a400131860280300741c900802c1700403d1011070007501c184 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 64497242 1250 64495992 64496021
    0x61f09090c03030c1505011508060d02010c080a0e030105100e010506030f0f070c02120a051006030209060d08090303040906180e0303070e01020f07080c12030f030109020f070605090d0210 82
    0x4040c21038a003610fa4444d07a40b42250844290300f040214000f007402854000c200e04184802003844081d0064030a12004064a00030140041d03c003000d41c0e8400740940b40140c21407101c039501c0490401c2110308984400026415600f0302040c410a500041c0015085412100c00e400140e601c807800c11030140b0042e501c0c0c1c040e50560301d011901c100100e200294000d5041e0401003030328140340d8081899250b4075510194aa0011081d502c1400300501c29280c210100c2841088120b045900060500c0b00150441b8081c06840014004000c0208222540c2c020001d007280e41f0f440c1d88820340c074007404090140010341e0000143e510144851070050088211900010b18110307914488121000c40e00300709264111b11800d0f2803206000000e11504c07028000e41c8000e0008007a0b80428400d852180c5851074081d540b007041001d50080c9020281da05542000d080541d444010740d140c2a000d01404070080c01c001d03c0c21052002400d4002129981841c4640a0303d000300358101408081781c2007610000b0f071 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 64498492 1250 64497242 64497263
    0x1030507120c0309140a0b0c0c0a080313020a030b01030309080105060924090703020a03150b040302130603061107060b01181701090c080304081219030209060903061f0909 75
    0x10012002c1d04010240b85461400288102035515500711840c07003084c1c01900d41d008842140c05120308180f005500c041084251854031003140c18040d510038408202400c0110048045030100c50300001003082a03030010648000261a402c012041e12020f200c210045407040500042d02441030103524401c110061041d0450390303903450703810450390000c068000114007400c61b56080d5501c011009008a15550340180c99042d9141c0190440f810350500505105107080308020f0a01d40104a506895041c2e83d2080b465030034405010103020b49410090540d81480d4908100c0c84ca04005040d482d03000e08004d00041c441040155900911401d000d030283e500600f0034403400e002401220800b245410000400380c01d180c030f40454508198004803c55000010100900907003000504518026099000d103440c0b50300030041c8201c21800740740002c1c10b07000b0a45091035920942a0342c5c0184d00901651040e142c105136641410f0403003100c800c3d5490f40a4070101d016181445200c43c11a81b10700c40c281c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 64499742 1250 64498492 64498517
    0x61d0106051204050a0b04031d060412030f02030403080a0804110405090706050a140d05060316060e040b0a050613050a0906120f0f0515040215091e0406080a030806040b01030507 78
    0x800030010701c00d130750074850b052440c00012600d00203240704500982e01c443c0b900e2501c4000c80d00340307002c1c211914403a43d002c0c0400d201011103400e01445150345818200b11854800d80d083c1e0845c05203038406840c81902050301c0700110780042125104a2140c07480102a240000802c8210340050381d1250090b4014101400f08900420040c85503c0c110300342410364000c40603c10a007035000052841c1440c0d220400c1c025039080800404900ca0f41004803581e2190600754010240103050303180c3e52195031500c10b101d40c1ca07114076400c54098107029100300d9a44800703200c00c1c4d50600c118414103004e05014070002868408510504042d00d124004545005650303840d580303d8560b4085003500c403440010b0185002444c10040c40c54139004105c00a0120300d0f190042080c1400b00001d1404000002c004141c100e1342c0344021075220040d00c1096428a00070341000c100104a0754100144901ca064650400d160f0003640d030307e106100403035060242d404d502e0011420307618140c3d8000081919915000e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 64500992 1250 64499742 64499767
    0x7051002100f11210108030c0604060b01051606020c0f0c0325050414091b100c060e0708030d060504020403020604030b041707060b18010b040504020c0c040906061d010605 75
    0x40d00007000078101055a410f4000d07040a10340c0502c0c10b003908441d001148000a2802c40801c90042c44544055070400c91203805607615008010001402d080c1d03145803ca0f41a0300890607030b42c0d01c96081e201c0d99030f10b5420b8507201c4000d510080d4a11064840d64043c548540000200c550030010701801402c1041d94031b801c0d1040c9500001030362450158a400c001c54117484610440c16452108a44002079041046a450915408089803c3d41c40d45100c4140701d5612400700d10f140c144030614001010709084d0a00c00d000303080c450f40350b101d40d000704400041c0c81c50000024001901c40400100300d05940c80041000f00e1199200080d0020b10620041001c140301042503544180601c601c40480780312410000c20741c3d4001c0500710740c0d0941d86c4110b0129410020784107001c012061360100d284d541000c41d601114040d510403548a03640000f46c82504400034446910601c101810500541929103050340c0602103a0040c002d0500380c103100607041d42400d009140c12200103441f550725109004c5402d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 64502242 1250 64500992 64501001
    0x2070b03180c030a031d0d0f06050402011206081905191118040b150111070b0409060b0703021b0406091b0810060e010c06110d0b0901060c1a070207030507060906020705100210 77
    0x1d595004015500384000304004d2000c0300c00042c0f05489c002514034140c0b001400f08a861041c0c0c0e00854039100c03080c02201400100e600707400d22814589000300e070081c6044d61400314032101c841035640703240313900c802040561b0307540802d1150204e0745412010003a8400b40307030300e0904483c0a04001c0d60301000c101e400c0d180030014101141c062500d80c205281403100d03030f4680040b6920182c01643d0001c0c0400031011070b8400c2c140600440e020755071805881d610020342c0c0759000400c08824069200741120a035886900c460300824080d0b0701030040d10030b020301010341154082c40d440301040c0480001807103c01d064001500f83c803002c1c0c031016606c88200004407804446080708031042503496007030000300b414880203003600800c08030703010940c4621441404620302c0d041e44a0810b01400941c6000004d070b6001e107910310840450103d40c1c103039468200481c03030304520340d00251050041d1034001c40c900b54042130100070341c0d6154080795a030a60ba101813120500b801c00b5044010381201d8403240300c0c14000e800 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 64503492 1250 64502242 64502297
    0x60b0d0c0909030216030311060a1406090c0d111216020a080a140c0d0f0207080a020111030f0a0804060501062609100c020c0102060f0402090f0702070b03180c030a03 73
    0x403102280c0d01d2505041c10317650b140e081940841c41c28004030700d400e1010007072154031408400e4180108001e84200b2440c03620080c1007580b0030304110001810128002c01a43c40c0800d21450500105501911107503207a801082a022182c031807800160342c0d800302031030b00b10920341240c0c01400800c00b1a12448050340007904200c00300400e44000049140482020b840c100c44540d0140c4540003155801506629904100700195000900c00b0070040101003040740c41c154080c20300304200c0b202512000d0842c4200340c05001898000300d0030144607540031141500c500d1044804000c0b0340d80b661030580300002c100405111070300d102034466040610035058543c2051f01041126410154a16690306545400600e80c0045e80a150030003410340c0c2c1041000e81150030100c80301c040e414031f50089104203000504410f01d24207070001190105100304010801060340c50500c80d1281800c0c004081c1d90510300c00c50b0340080c824200340d044907203404140072084540c103440e141401e1500c1402042c0b010703c0d011 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 64504742 1250 64503492 64503497
    0xa05060d020c0102070c15080c0301090f021605070315090c150c050d0e330f120c1b060702060a05060d020603010306090506160512062209060b0d0c090903 68
    0x912140b080c003400030300206403083c11701110b02803c0c103440c000c0c02c001c400005010803400c141401282c50a0100301c0c0d05480d41ca58021030014204100200a88600701c001081040381900440612001190741402c3d41e2003140c5546c4001d0005201a050b00ea40c1e840160230030700c01030f038100104108103401500c48646030034441400c0c402d6803102ea0802d501c3d030481801040b40c580c61450186007007026540c17003000c0c980c80c006080c800d11203030b015500743c40300b00040a02c40c0083c41210f03d4659005a520040507002c8200051500d45002515508084c107026940380380e03e242824030750004181c0a21500c007540c01048103a40740fa604901510010b80595088080c402c40400507840d030000a5011f58040c24011070b503603000c0d00e04075140540040c00d00c3c003a0a144000d41044035848012504084145841c0015603240e00001440c404400d260004c034040c4a103845048018551700030351801402408200301504445080c0807040703038030103002006964140c2d01448034010350790001c0c8400d4002d1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 64505992 1250 64504742 64504747
    0x12030a0603020909010c020c0109080615010302040b0c0304031a0402030606040914011409070602010902012106121a0105030304050616080c030f0408060105060909160e060a0306050319020a05060d02 87
    0x1d8000c503041083c1503c0c010040c1e5100d07002d51441c2c0750100440c0303604d01028a0004003242c07801203038a0303c1d544081e005001071198400b41c03403040d0f1b21907019a030103098220429680c41c10f10700c940990300d900610044030f4641900310320003044200d0790305040c070079900a0f000e400b150351203100f00030003003981000c01c07941c42542c019a040c00b00ca0910482414101080c000c0042d03080075a02c480c5410183e0b400303031003160305003060600183d0313208030849880340d1050744078040589185107480250074250005164174818904034010f01805035802c03c0e04131807030700b16500c4507602d035014151284035038010b080c1c10a10801450804001c500e141185d618041d50040d420402c410780c0741419540040d043c0c009010001c1024013405405010060040404540c0103151000e4100030404d2444024020035004000c3d01054442c5d5000322542441c16100030010390340e402d01c1c2c0c080540180f00c2401001d02034400c0007010544410a40d60100c0080e4004010000f150728000c100810740d4003d0f0100c00e22030307809 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 64507242 1250 64505992 64505999
    0x902040b040b030910060b0403020f030601060203120c070204091514070225030f0807051911011b0507030c0617010b0403080906070b09010203010e070e130c05040308070b06190812030a06 82
    0x10340305070386c06064500301040c1e860b0f2441c01048060310031550001c0c0300c2e4014200402c080ba40000c1280c0d40a900302c003541140e940d51403040d0205007da0b00300a90840c0c249020781e8200552005a01c040b840e82c00810001c200301c1640322200d0850450301c2d00b0240c0c0c00804c0a42c03002e4001d41815030402a00508100d106440c6e0703489100d800c86441046405000100321f45080013018400d05c5040720394603498229655a6071506200c00da11010200d0522160400500400521907540b10500d508001110f044d00e5507850603000d404850302c20f900000e00b52580c04122000c190b0080e41c100c07441681114100303400c5441d202940d0307000d02c052a51001c410010b40d00000c1c000308683d403040070550001622585040691003404174000c5c001c4c0d08104003032040c1c04c811340e22102c12100b00b10410400084014581700142c03104d2003107404c00f401c909804103001003007100003081507101c0e07103033030f5150303403800035074206c05807800300c0758000c070f02d5190806c0c07182c1010b40b0203410103580d0188803c24045200d5a8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 64508492 1250 64507242 64507273
    0x304030c140f030f04050102070506180f131a030607090605040b340c09020306090f0901020c010911040b0109061d130204090209040b010e0d0609080f03070c0c0902040b040b0309 78
    0x8280003884d1540350210b0300b00455a0103101d014010701003652058074000e4401044400b440c0c000e02564031402c0b848021242e6a00c4402a0f10395800a07088200f005414213542d11040d8440021000d110740720720400038080502c00c0a8050884440341c07100c9061505101c3d50340e00f141c10110741503a02c1072001011210504100c0c0e00605000006030010b08184aa420401c010075400d800c21000c0c40d004105201c0188c0355110300360f5224000c681d02400701e8880342d10060192248405000c0158242440b00c0148003021140c1d03405c4160488041210400040040d180036480d841004041088042489441d00081ca20740c2c0e10020020641c000c18040001710302c04907001500104441030f0b010640000c981031038415503905a0090074031044124a04000071412030301050014015600c0d10854030810009e04140c0e44e0100407550030700e84a14207514028105485c428007601c60b04125000020203074554400c40d021b0b0b0398541d68180c5018140b8410158a501c0501105401d10440303440d00032011 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 64509742 1250 64508492 64508497
    0x40b031504030504060207080607090b0a0903081803010f06050d080703030902100503040302010c0e13020f040b030c07030801090e0a1106090909030301050f010509030d0c0317010603020301090c050304030c140f03 93
    0x9100f912010303111820000024604000c94111204986c0000180042103400c0402082116007086613036076540300c011022140e1442d180d00003004110007182200814001c0c241e408114030094000304440740141c2c41140655034244525a00080c042d460400400d0b40f2000508a10b4020304000c43c260034540c0c082000e09130181c100c0780001344003105000070158203000740302c5200d001d49014540950f03118000760810000c0d4510012041e170000c0c21340034100322441a500200310754803645846c0d2500c210b000704c45a1000c1c0c400c6000521101c004280061700d440f41c4201142c018004207461459aa910100042032240c0a070380010240658000b036035900041900c514070b8000996125454201403240d041400040742d41840410300c1504c00d5900c00046407207140d0b100345456010701e0350605003601d225409022003202c407944040003248045e0550003d504a91410364100303d002070034601298140401e480007030000e42c07000018004590910b050400c0d8005c500280e9410070307201002145180e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 64510992 1250 64509742 64509751
    0x60d0b0703020307030501050306100b0d0f060906030204150b0409020f090301050a0605010e3109020a150e010e10031d030c1b0301050f180a06020d0207020411090f040b0315 76
    0x2c1d000070820403982e0b0316000d40b50050405500402050a0507a03030214101618052800c00c500003280101101c42c1039041005030784000f82c0e00304130485e101d000ba107010301105d01040c0d001d40e0401108a0f1042e0080851204461803000700901b060704060141c4082e610000b80942d50030b40500840c0d940703a90038402d040c0180260030700000c580d4034000014000155104420340b042d003124814640c40c90700f0780d0303404e088101c82102e18000800c46001800041840030006500241c050320081080803040e90000400c0e10141c40d11466007007400c00442e40318840030b441c0d07508103004158550011b0b00980041010a5a0344820039052a05140403469a000048810314a41c05071500780303a061030514072185004402d070000c0c0308a240580703180f09035210117004807114a01005011305450820310190a0b1607078003107010741d074619600309010040d41200f101a40308a141514140500c9801c00869502e110041d25545a144624003000001d00390302024980501484844030030b00c11940a045126 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 64512242 1250 64510992 64510997
    0x91501140705100f050a1b05070b040204140702060106020613080406120b090c0d050c090306012306120f090a0b1b040302060d021e04050d020904060f0c050309010b01090e060108060d0b07 82
    0x3140350211b0038405445288484044641303915089010080e4040100d4030340751b810007004c85040e192440400e004150145500a280e60f0700d200380903455038042600380c100c1d20150308840f4907440b00b98060360443c1442c42d0007014401d0820041190a00591928580b41c10740381c2c00160b10030a607008180002c0080320000045031000440e14005203442c482c1a0300f1005401c500c3e410f04110002080e580d6070180140b449840c5403211440c0180c01c02c03205104403203c081c0049454041d040c03620b282400056036848400c0c44e4800000c1e000d410005892004650000000c005c0380c0c890705502181c0015502c24055004e80412000c0050b0302c840700205410301c01c2007401a03840010700d14031407003104a82c540041341c12040000300b080d0703620741c214441d210390115040e91380ba89862602000410015002040c1a414070081794282500704028520400c00b02c8000d004000008004545120341401500b454002e60030104140303505c60540c082c0d02040180611a085c5046d44a4442c1c000301102c00e0b030700 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 64513492 1250 64512242 64512251
    0x20304080114041a0c0706110301050109060e18060d080f0702180405060103060b0609030f06060a06032a030209030307080901120b060d0e010b0d0c05091501140705100f 74
    0x440424800c40303003200804040020b450500c0d56540540d81c03a24030b4040c0c01c07807038400b02080890f8a000c0071102060781c0120104100d4071542003c40ca83e4209214450205040c40400601c2501a50340c01ca62010020404c002c103014207404980090809002c040e04054103498400014041600502802804560954656840b0320404c20141160ba28400b00c001481051000180d00043d00d01e040d268403a03004201c4410307034400305049000f04186654944510300c00301581c000007061080c024034042e1756218045442c0d05003502a17a02d42304501512413400031401040d246101c03281c00380a80c907842e0149c07900301481e001a2564000d81d2050311100b030005a030409668200701840b40418070084140809a001030004940b03008181c2c1c01440c00c0d071528060b481103075080d80226140000100901c070002d00b141454114500540a194090004900412400c1c8840700340340d0a1240140d41d0b2901800c8a0f9660940b284c0040340129524450000c2c8414011828050b060040300007490018 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 64514742 1250 64513492 64513499
    0xc0105090a050706030e100609090b0c090a0e04020f03010204080601060306080d050304080a090f0f081b0906191d04030f0903080901180308070f020a080c0d06050a020910020304 78
    0x1421a400a848444981d010000010006002040701c0e41200c109040010f413044409018905083c148040001114503140d00410903402690203e280d83e406a41030f00519034827402020040d10442081940c80b070042001000740e8400c640788240d01c14400b1345921000803200012a0980c0c00940003100ca64001c0001444120340c10702c1a8001070200340000c0108408404000d0301621002d4170103082ca03600040e0b808010b46c01091001c0042a0200426131100e0741c0e05070401b500d8907a40508103050040c403000b40790070103e010101c158840010304504850b100c0d0310801480d1008155480300148515800241521444209841420b07915100c00307440c0c83e261030010404c180b0b41d02c4001c140311f031010303007803000c01c0b102415105429401c0c20802c0d60003074444529200e030b04082d4030090401c040011303c030040000c8603250304884c600c259030031805107440f030300d00c5511a8481002c0c2904038400c0440036011903200d030007803504001c2c3c181d0014503004002011400c907006000204002d81e10008081 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 64515992 1250 64514742 64514767
    0x408030115021c1b14160905100510140706090c05030109171312082a03030408090d02030d020a150b01020a020f01030b0d06050901050610020d080a06120305 69
    0x70303201440c080c400341041c00c010342d0070000c20000c162145800c100e011990070f680c0b41c4010118980c11900900c50b0210603000007074241e40e8210914003100e9111000740009944521405414000c24810250913026401c2c01d0a100441c411104160200000c040c1107044a80101d802051214040c21380442d40ca4218241662507003500d91010b406a0700d015003220109148041540750406000712917a95400c102c501780d800070010760030241c031520409402500704049400181800002c603016034500c80e411121030210b440800c0349000710313600104009000945030100400c0c2c0305a00030204a030513103168021a107458421002c401c0580e0286020380c06120401840200d0b00f000f6030024403c040803000002c0d01c0f01e029a000a01804607900094103581c002d420400c0c5070304014001154401840c1040806402d059038030211951030700c0c020501604080d03c505116515a4008024802d005082260040001800100d000b82e039201d0210340e8001e2035107660707415400396a440d5122141c1d141d00303 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 64517242 1250 64515992 64516019
    0xb060402040f0b040806011208070b040804050301060603060906050418060b0612040311011103070903080904060308030702100c02010b01140304140609030d060f0311060c0f06042406030803060d0204060b0304080301 94
    0x8003404261420058000270b405200300d032407169012030040d4050300c6519142c0c96034001c642103907501d54206900880c00d280d00d94008000c50714441400c2c402e0035520300c180821902030b25448175411400705d141a01048454102442440010302094030744422040c070764500020649085000800900c00b5070000e0009024800a541c0d03c9910b84c1e2450401510280500901e031100904108005c100e041c6542e0780c50340008003c0d90007401266603407803c0c80c40203403a00c01c1c49000610061408001903100c910500c40d050310414103860303840e40101d114569504c00d402c0240115202020700064070000c080a100c454081c000c244002c54907184034a11a03403d80b445500401600e100920081000c60340003c1510415202582d4060769840140103050504021860352000c61040b03805100401c042c454100c000e4017031850701e070307205e120154115906503241407001518080301807010071030500d80305025400c3d0920042c80051640da8079500540987c004842c16146000d01000400020544009 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 64518492 1250 64517242 64517249
    0x30f0504180c08150a1503022514060f011802070f060c0905030c090402060307020a1407030c1e0308160506010e180a050312040642120b060402040f0b04080601 70
    0x4c0d52a02d45944408160740c0f0000307228111401c2640040460140e00030b41c101c0300d070189840d004082d03c0c0044089003103d4515070804940c42002c805c0f40580003200850118001ea1200b07134403041d103901e80840e1480700c0c0d0280200c0c01e011a401c1101e0000505600c4070118002d12810020500800d005c6022303090320442c1c1d108500903082309840081d2507032241c81d665070095045600f107480380c40740c1038224030341820343d4001041c01c12001c6203840c556600007001c00c1101d10603450112069203410050151000c0d0010074084102420411b100140c4100d0103000c80f6544650441080900c40d20b82a1900b182a8054002043e20f402801508030316010808100ba0300c0c44000e003840f40080d0307140f80e56441080b58090b00201c00c9000300d030420956030400031420090b43e418580100c1050360040700c85c101444121a510031040700a035400345103286290465a50040740e9021a580e40c1359002d03120001000d480e8850b50810010580804405080c4041c1c4403180910351101c0c00c0c103102c586080c3d010380 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 64519742 1250 64518492 64518511
    0x201050705090d02090c070507030804030b131110050f0a05072a030f05010b09070509090906090d030908040905090708161a0d0605130b090609090703030f0504180c08 73
    0xc0c1c01503d444002000c0300c510f0341918507282c0c42c0e41c0c45e41030030410f00442000400c6030041e80c4001060046040250045da4090504a0703410386407031380109001321b0017000052801001d00d001051074540440108403507007590501914100507080c5902007030348401c200c5004114042480024000070440045103940f40c00d03410300c0ea4428040780001900143d100c010042256403406400300002900060040138014140d06901c2c2452000513000303412400845000784a140002007500b00004ac15034050b03500302c0043d00070b45481c03801c00c50103426240020303194850304110004511809208131482000c0c00b0380034001c044c2c280b8001d18108a554002d101041030300078814854000c000e4299002caa8400036240e40d2200064442d202501182c0e00c022b512030b104c201d24005c96502c0d604009020340046501d0b00c0e1580e01c44003000740c05181a180c900040c0d00901d000d10000e8052624240982c0701d9040003800e10b91794500d542c0c2c8498109294441c600c0e10360043c000d8190704403041940000c81d10 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 64520992 1250 64519742 64519747
    0x308010f0821041203051b060403050405010c0f0b010b070203070902090108070e040e07090506040e0708120307021f15080604020d1b0906030804030201020c03030c0d200d020c010201050705 83
    0x80c00715a94030100000e01840d4440d101d800d910070003010040310018250007410b07040d980581c1c14060140d4010b0741000c4920082c200305010300c044003003001ca21540c0e044c0c903618107180c180b01c0111000004030508403240c1c405980c4420118401803a02802004056080b80c1c0c0c50846105050400481d40d0200019600601c1040303000e81c1c00651a550003c05441d020b549044803000290150500281c2541107008840c4040340c1c030000d5410841c442c20b0300b40d80900181480c2004aa03460205100d20100d075004468082c440c060010010342d040007140c0b0483d022070a90840b65403540c04c51001c094100c0c0d0fa030716507203c004141000b02034000d0107110040c141e9071078250041030000380312080040000c00c001e0428408215a4503612002d030800c0d510401805450f0b2070310005561003030009034090721420000142510b03001045490120b42e0300f0180208890074902a1218011003441c000d4005d6298074001807480c1c108a003040000640e80100341040c40e01002900311000640f00a0400c4802c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 64522242 1250 64520992 64520999
    0x3110307020c010e04140f0105190b0904050a0b060d09120c240e0304080309040f090f1104060b0705030307090b04081203091009080a080705071a061302030109090308010f 75
    0x20400241461003800e103000555030904c00075000304045803c000505150006004c0c51012910210303050f140c017585c1d018071741c0c44007080c1c0c00c8076102c2506c0340c0310a4800401c00d0011904040d08001e0f0407426050004c5207000001e80000c4042d000160422401551100312400344112800616605c184a09240003d044681c44684000c62039030003166551102c000300e4902100c0b90b500011542140500703407903e4903140c0d14125181c1d80050851480340d0708028415128010b140306000c1c0582d44035105104001050b5601e107100c81ca4030042c15403041c1d86050000d88040318600501c3e000303200c0da018640e02e160607040030b00441800d070482d442c012010b00041c454048000b070f0014107200c00c404030035207903914070313410b240b030410a81d00c3c6464a40c1800c450300100501c02c0050002c1c0e44094841000a641c0d442d0304582030b014001300a803114801d0003580943c0603841142c40c0c0c010f5000740595841b60340528a030b1069074400e0384540d00036a03490314940141603100c20b0781405820340c40c012000f050324 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 64523492 1250 64522242 64522247
    0x60108161a070b2e030206031815010b0904050f090604030f140414041803080a0b0a03080a0302030106080a02030c07030f0c0609230f07090c02070f0303020d121803080c04030b040605040303110307 86
    0x148074030309d002a100300106032031000b000400a00480c0d0807000c0b04641e11091074204c180c000a5886024906081c04541c500c240d080d00544a49007400003070041c0d40c0c40352401c8449111040350030707080c000c2440c8510b59403d1668001c0018160007043c81a40c0407e42040c0005c07600d24480c68803401c0500225140042e0388640c41329042120b81c0c20118651841c04002006060710350300c02440440c0c00a15040310700c1e015009503041b04c03000d4441050640c2c0e1000c1030340581c4812500c100c1091020404400001e001c0c54071028506a00d152940b100c40301c41d074440080300c0084a080c1c3d2210100c4051520700040e0b2841810900c001d40040e021055800f900b00e0354400c03160040c12034454032608107459040c820001e0500130b04080d01c60090381c9541e4113010b13449400c2c02d100100043c4001003030321460074150180400808071240310342a034000d01d490840320000c010304407021510742000001f020031610740c2a5030089018080010391801c06240c040c2c03c4a44003030508624002c18000c0004058 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 64524742 1250 64523492 64523497
    0x3010b010f0302090a0e150306130f0303110d0f06030c121e02040b0306070309060b0f0916020106050a0b040f1208030c0d0b0402030403030c02060108161a070b2e030206 74
    0x1a0758180581c4500350300d000a520a481c40d00700c006400350680410052003a60342014a100e2400e4055031081d40758030089810720101f00d50050302c008000104440000c2c80fa60014001100c45840507092103c02c03801d40d401e4130349444012031003540b145014000e014142451400500b210f46440001c91703025560000f201c19102c4a0030b0318582d00c04100020354880c2d03006480110b20080640d5564030300140098000c1900000940304949060240b69035410700804085141d00010a0a07105945500480c51400701100e080401c55480c2c0d040010341d070310f80c81c40a0317001d8940c05290944450910540c529241c807103900141c9010141000c02c000b00d00c50310211790304100005007c40d0b5440640c16600007401c0d40d00d08450300144000308200034958940d000c0c901e154019400d542d016660f500480b60340f5003880c05400b60f410030f809400c00c51001d180c0300c54640c000075041001d080c1030098483ca00d0219003150040f0280052408481c115500b00d450807240b842104040c0017160b056401046407030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 64525992 1250 64524742 64524767
    0xc02030a020706031a03030a180e04080702040513080f04030b0603070f05190b0d06060f080402030705041d01060f05090903040e070f050c0a05070617151005040807090203041103010b01 81
    0x151741d11395014404950034540040d031003010301103940d14061074500800000b003100208000b1044500d000c1464000032200e540075a40080010781405295002c00004000c040c0449001c00400c07821a000a201e85001d0085a403050180d103880728030b035041c90403010303100416851082d008480b00b0b1150b1207030000d01000740d46040e10600b50707191000c40d401007a849640c1007191140030114903651244072580010781940e05036030701c1c6c1d03804008658056486413400d580c020f505401c42c1400307001c64109513218681080160f04480112040c4007940307400c41d039441d084039003100a422001d00490601c1d82210b1f801007000c10040d480c2516100c0d0480a1a0020300341c01c003046408400042d0343e600c01c80a1381c054241c2d00f0290b4100038014a0f000b90340e258148100070115600d40000c00c40d5070301800c0000d00c6610031544000094698200304180340421144600c01c0c03250501010a035000b040003d000504110381e001a03807401e090034070402420850310f0241c0b02e0780c1002001407a50340d0110104511 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 64527242 1250 64525992 64525997
    0x303050a0905041515120e011b0201200d0603080309060603070501090b030f0601050d020d0510050a03020a090c1106010806010e0c030106021009061d03040f08031603050f0d060314010c02030a020706 87
    0xd0031700a0b681120b03044461984640124107152210107130341010751200e1140c25154407a50804100640140c0c00c0c0c6083c6409403001a1150450f4145043c21400410007900b20107000907486841c0d82e00c41129401c156902c45035a405101000315070305040001901821003401c1001110b460520f4450b030506c0700800c002090030001000c40d43d941d008070140d590180e4420000d549595441403c203008060031984140b104111100010710340c1081d60124040d641c000c0c0048120724240010310000d400c444407541d04100300840c040810035010b01c13103240030f824035a001c5c1c405549000019503010501400f24100c1100410041203025000612081484601c00000c9007010b945e040079401020314003201500e4080b000d51007069900040028070a0741c4111000d60031080d1110700d41d643e2070040c2440b1002507220101e40c003020900039000707060524a0600c01030b18003c2e290050205032206640210f81442e0000020f00d000c1c03200380035151442c801071004500780010044020341d54482e0f40300b480c09 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 64528492 1250 64527242 64527269
    0x604080102070c09050f13030309020d0c1d24060304050a0212030a030c0201020a0f0f020a05060a0b1c03093003050c010b040903020d14070501020c210a0504051201150303050a09050415 81
    0x11503c800b42d8044070346800c0dd03241d035040d0f9a0b031000304605112a05003200d0410000002030412101421f001100c0051a20302d407502d42d10302005e01c80154170241c0709449034421100c0c1100160340e501c28045815081c50040c640325003030924003030103841c15407030b001c001d5900501c806082d4a90150091140030241d2408030001c540000040e41085102200a0841d010700ca0401104d10465081440e061109484080d000050b02c03480c40403006152000600040041008004901010011400203a6218015480314000124500b00106510001c0b0007241e070216040405541c21300c10941030324030a0340c041c820303e45166002900c45407030841036024401181c0c9443c200039007050503100c0082d0b101d402190b0f105104039207269039440d20540e405806d6000700781050420462000c0d5651007860f03440d00c0782803d0814003005039101000100306819035036900e0241c05100c8543c3c950300254040c2d114075688081c03401c00100311074036980009001b1418046041c50400540808004403039020b004500c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 64529742 1250 64528492 64528511
    0x1080c03010b071509060c0e0307050f0a03060c1806020d0806040203040f060507050c011d07050a06120209120607030b041109150d0b030f0c010206150607060b0604080102070c09050f130303 83
    0x4c024294410040d144a00e0030303c2050f5443d4120346065054842102114001a610303020440b0305603051a0b196040b090120080000808075003000c06000310508020713408921303000241400c09042d5000342d0040c5c0c420003105406c140c0004050b90848410307038041d8514901501c400c4100991400d000300515035a00014404500c07400c10341e840c540c80c0400903c1030440394011451059035222035a0454003401d540044c003440e2000c050b4045400341c0d00c0e2090f902034a00b00d108025006040d00755040205684943d4420360705010107031080203e80c0700040e855040d031041c40100d03010ba00d42c0f125048400c1001c00c4280e61140e42c00700301003400507a901d98641c9107440e1039000e0083d0084903034140c404c410000c16140c2000c500e010007200207900b00c66803a55401800144050702070340321900848100408408114035030004c8218080161201d85065070b100c0885007240d2003800b081e20b820100c0031b001c0c0660000c42c000da0303030000f980b00c181b003400382481d443c2c00701404040c800c020141340c1e803004000c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 64530992 1250 64529742 64529783
    0x20a02010c17041415160f0c030c0308030907060203090102072c0414010e0102070b0403050702010306030813062304050d0501061d04030f081005040c0210021801080c03010b07 77
    0x80607011000002d03070740b01d540c0e41c042001e00b002e5007840d9521400e02e08814095156010081d1581c10840075400c003062442601c03200c8044150300f209452030040700758040003207600b052841e0020b6100300d051039524074040c070305141451010340000301150403c00185003143c2e4001000c40a0f035040304007030946c0720b082900c2140b144140a01c6001540f601804000a0140340e4407070f800149800c100074001d135541c18864500704c0c451040000c0120000402041c0801e10860203003034903c0c818107000518580b03036201c1d8015500808030b0030910400c000c800340622a8480c0310241004159814005c103c4002000301c4454021790203058000c03040f041c403100500209401c050018540452145024003003154191143c4a0449082e0041034080c0002d900107032092950b0340c0b04030040031760000c0d203030704040c1004040e10990310303e0802c42c400c245401c6a4032285100500040c07101d0b04030072142e01031010002d03150110042141500540a1004014405035a800c540845501c00c10040c40d6241c40c8905 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 64532242 1250 64530992 64531013
    0xe070f15020106170105040b0705031003030503180604051e0f03030601030e03071407030b06120601050103050915090c01080f0c03370f11070203033a15060906020a02010c 75
    0x805207440c10715803140e2204c1980018050340c01050810015550341c04c09840b148415100a12801c00142c410000709109802841e041042102140541c40303030010042d02d096000c0d2030650309a00506190050003010385045441042410080c1103242d00e200c0e5450344030300004118074141034883d0000320030b00300103104072141d05900c9003102c5000c1c40d6040c841a529402408102d8030082c62502044551030503100105080303204400401d4607038245001100500f0002d0f1016001e44100801d8030580f10100c00c80500c04c4080b680100700c158a03480005084040c080c003400c415501240c1801a095000411660311082c070718102108044400340400b02005001d15402103500c500c841941d01c0160340d04113030404106d001003030048210710710424000d8852000001d42c140c3c4208000f685050718181c00c000704d0030a440700c0440c20305000000d01307200b44040c11b40032a40d90340c071103401e002088514040e501034480303841c0510f003240c20700700013a548200e5914041c1c14070408203a10310803c01340011 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 64533492 1250 64532242 64532249
    0x15020c06070605160905030d0e010513030609021504050306150619020604030201060803030907031b080105010e070f03110d051503160806011508010e1b03040c0302040e070f15020106 80
    0xd032940e51800d905000000f02401d490804610f400da0096498042c03182c040d2000366040100035201811603484151018035250226506000c4140b04103402c2061054180000710b01509004c2001c210520400c054400a000f601c805084203110900c400d84002800642c044032050554280e619908000750300da01a26191070320780005020300019042c2e0104003180202c2c420340007808000c1c1c407481c1c1e65403603000c101c1d8108102e5021407002c1005c01c8810041c0e5040c00c04055014407001e484414003403d60700260060b288030a58001030151181d4405404821030755185020052104a0f171041102c0d440384289107440f0a071510040f42c25001400030040c0d402c40300404a07400d80000c03040e40c3d00b04044610903022280105800044d00098810109a418040360f45100003a8200b606248034180f002d02200f0b4034104c4840120312880448000310b000320302a0b0030400301146540304020603114049418203254210480c100900040b010422003520305800f08004450b120140890041c1555803 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 64534742 1250 64533492 64533499
    0x1110c0607031707140a0e0a1d04031106070203070807060b0a08061b0f0306060c0312010608060a050f090c0904091b030c05120c010e010302040e0907090b04090b0115020c 75
    0xd035680405403c802001c006001d25080e0000c00e0759511019640314440781580d4407581010802e51741000d20600e80c502881038010045010113450752043c6014104030924030426641100c140014150810b0302e200c0f8504540d03000b17000314a403141001b516030141c00c0006140a402044402c1048025000760b445030300c7c013500f40d92030556a80a41603131200d0681d207050404c60a00d1500001414020803103200442810203e4a551155800d0102541c0070390310010340f6010600c10b500141c4001d80c0954000c0802d60345a4409003400b10820004c42000d80c041032141401655580041d125400107680c4412a0341c0c00365280c150400102d00a03114240f0018003044041c81003a0110103d140600240c8e0302594402c90b040f41c55609029542200c0044100207030300c0f034aa0718074603620582c200949608103140c0941090740e034603d402c2030390340103450503900341e005010240300c401e00c984030b6400408030480e8140704000107500d5075121624103000d241d00d0115002c0c5011180c0d80208840000700c100034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 64535992 1250 64534742 64534747
    0x4031101020313020f0604061407050f0d05071209030b07030b030313081b010c020306040f0c180b03060903090607150e061806010e0c19120204090209030613080901110c06 75
    0x41140300000c1d43c80350400c07441403850300c07410591801c1c003d040d00c06403440c80d1504403a84140d01610000d903081510115000d100e541c6401c46004820320007030041d604142c41e91502d40c00285030104d64034512502d51401c021000302e080001c6a4080e510a030070001e1030030003303044014403010034218800e00d900c10a8644018500050341980090410808503142610300040030485004548900c0c00003000307941036100c400401d011034000e03170401030340500c0b80d014921400e03610b07051003441d090415140130a860b50380450071124201441802d80c00390281e4013461900c0d4402e070004255014a1802800603640188102a400c850764407040c003800100040300e40c546000d01e080c10401d60380c1c0e401c2c038000d4000c10300001400c4441c452424000c005404215080083c0002c1c04410900d0990405003006041c1c0240c0b100003c3c0c0e440140003402000f070001d42c0d98030100c014140b40c05d0002d031a4441d490081e84071413000c1800c140945284102c01d00c1c0010400b00c0c030490301c0380b420003080740003540072100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 64537242 1250 64535992 64536001
    0x30c091003060506091e0705070b040b07120501050a0b0a052208070806060d0305160f03120606020f070303030e240a06090902030705090601020718020a18030f0803040311010203 78
    0x15904200c040302d00c00e107402c3c00306503900d4061142c00318007a1580d602548801d07000d803800c00803400500c0c0c2d000700f40e4507080d418010691601483c4010691342520b804044400b8441065030203c3c00800c1e0310301c010818007082d40b500000c01c00600040c0b00c8c1d042c0359080460850170242c4603008440640149100c0c0e40e800780f040d46492281541c09d0b20030014180f051441c0000c0d042c0e80031030a40c1c800e5000030009009040562419145a4030100640c0602c8501c481c0c0b200000300f0103128451428006d40e60704101c0000444030800312441904030030155442280340c0780301600c00141440a030b82d45454041038015115400d5464441032920751503001140b071011148101d0740e4100503200301e444807820304c2450f5030b412022080780c228401c040e4050300072082c03d00c2642002400319401c061b0610490f81510b41c1d90402071400d040d0090700f02200d03a000074141361215400907210042480c0d403120392402c0c0e0300e1651800e0f070044400600038580a8084000f03018036000d0440324024080e0740b4000e559a181 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 64538492 1250 64537242 64537261
    0x10030b09030d0203010e0114010c050303130f060c0305090d0c050c0613050d06150b030c0313170d051506030c0d051003120c02130203220f0606260a0c050f030c09 71
    0x1b00340140c003d15180c00218200f2980315042e0f003218a03801102035460768540400a49074080c080400b92101c1d000410000e00042e038902c64818100f1013580d00240c0c50034020012400e0040302c03124101000004003041d40414070100f5007054064044800b59640d10003807245081a41c1550b025640c8081c1281c180c1c020300156401090f20400f4040403a4610b40d01c0d850088114001a41d00b00e6174440c041c4009002c2c1e201109190303100138010740c44282141280c0c819414941d000600b0900107546031810b0040014007281800703030f6044111012130940c50700701105410b034090500103440c11503c420204a4400300d880a981c05103401c00c4459007a242503000240c00e003101018200c0c050013a24642b052030789aa4401c1c0e0b802101d40c0c50703038000c0e213810104403007101080014055410249402d0b2050001d00540705a0000b0b00c90881e04c00002c6c10705503544202c402c5a042c1400981d00205040303400202d26400d04800d480f022140520440d45910204e403829000c1c0700a00d03000103039041803108060 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 64539742 1250 64538492 64538519
    0x406120302160e10091a031207060e030414010f030912050a020f0a05120a0e040608060105120c10030e03070c06020319051201150c0b010f180510030b09030d020301 72
    0x200302900d80c1890700d50f1003034120061001207400a45081c8040014040319019800810305460b4a042d110024030b02580000d00300000c1070900c0480d0500000c2ca00c08211881c0174180301c000303071040950f0a00e807030301340c010039010b1400d44014100302000607142c0c0c240340a9804100017a130004031160b070401c4003c0c40a0070952005d08108090300c100c1e14901000c02001981124255000010304a035a100c28144040b40c0c01041101083c82007503c40300e101038131680f00c1c00c8000c00c6460020f005c1540340000780005054030140440c03140e0044003241e00c0300d4481002c5030011040c140340c00900002c28292003429805180c800406442c4a25000100254004080c000c071401000c1d110981d441072502c140e4261203004868030341c071810500104085104640d8030f400881d610b081503250803090f82d42c0e0300380031882600551400c000307040e01400380340e8034a0403c0f0441c2d0403494042007542440100a481c110704c83c403001b44215903440025031515018015548001450b0304255200d5844802819034034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 64540992 1250 64539742 64539763
    0x318090e030702090a05160f030b03010e0d0801060c0b040209060d080304050d090b041d1005031002070b07030204180e0f07030302011406031203010b07030e060d090c090b0a0501050304020406120302 87
    0x1402c00c0c8001c117645101500c00d10b4060840302c9280e4040f105820700a07102c0c06a501c103c00c050640e28500d80c1116202800745400003070307040000d030107810181e00028282400603040142000b40783e03800d42002400c03191050b0381140d01240d401c00c2940d200340006014101061000700000c4000c4140f008208000401034550009070721941140e640b03c5605c541c0901507441081762035042d0002403016000d01c5c5800c04c0e008400300303912101c0c00e41c076440480c1c42d044480d001c10200550004159007403040c0f0152040e00181d4510b01545014034280b202c50b20302c00b101e595001055903607200407801d0201080b40c030604c64607a00580e860160b50f0300b000303030081002d9540c441f801c032003440c0019110b14002c0f03580c18010010624180c01c0d43d00704400c9510941124808805114007450005243e07650320024000c02d00c0c20203004164401d00c1c3c82d0100c01e0310b256900c0384000a060941403034003941c448176900182c441c2880c09a443c3d035510300010b40039000c168054449541c4650800051682c0490001300342c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 64542242 1250 64540992 64540999
    0x204090203090d020f0316050a02090405070f050f010e060c010626120a080115140304150e01090804140d1203060815011d040317010f06020d020c0d0318090e030702 72
    0x15488190004da072118411581c810060304100320303d0789001038031a0184440e0f400742d81101c84608042e404103450003001e030b4040d201039110041c1008030252460680014120075034a608848410030006000e030100204028460302c008141501d880c242503201c6402440c219400e10802d01c1058061000700314503846140260140386001c00c00851101c00300e610504050356a0b400703da280006010246110104000812854403c08040f0b8100b00010314051401072507514440c05c0d540b881c12080b6081350720045aa039040c9030098011078082c901313440842d0070b01c04140000100d54800100d004a0891005041d081c0780b42148000540c03541c40b11043e01d0706e644c2101c0203210700d0386a180a4100912440e01e8038400442c0c030b00706d41c081c4ca03100c80d60828030078140445000c0c0e20410b130b0400d106c026040300e507401028800800c1840d60402c03900301c841d0b1050016004ca070b242741001c10907a141000010302441601e074140b203c0ba10b07201c00500c0c01000505c008010307107481214201d44a610195090340b1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 64543492 1250 64542242 64542253
    0xc060a020406030606020c0607121e05040e0609060904061a030f0303040209100e07050a141207090b070506010e0601051c0b0f0f06070b060301150314010e010204051e0a09020409020309 81
    0x485c140001009500d101c00180303030504003942551021401014402e1000030070880d200c42175500e40b512920240d00410f651152030716107080c240030900d641c2c00145414410600c6070b050105940700c0c411503d4001c3e070031190100c0c94800100225803e81005c00304940c051140c02da0880e116807011002d0b50260b0720071a8440c4061300c07640d5000d050715445000e11050960b80c1000701c0c0945001364001c1c0404000350400c1000c21241a0b8035141a030003040f42d6103040d03880070f020441c40e158060445030140002c54600341c141102c81d220295581c80c1409150ba00d041c9420200340d0b640e0241d020750340102c04c06801e500c4102c040c2c5800e14090441c480c20140103007a000310f40030301c1d441c003078841c0c159100c00588030034200081c903116940e00e100b02402d1290503558a03400e6624280200340c1000144d806000001d480080246002d0b007114410301165003c0d0b40f05100510a43e910139180e11104803804040e00701080c010310004940c00c0540d801182a2840001c0018019406401551040141400303490 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 64544742 1250 64543492 64543499
    0x17070b1b03040503160c09051906080607120e0a051f0606020a020609042a02030a020c06040e01050d14010606030b030c01090b030a02070f08041403100b06040e0c0c060a0204060306 79
    0x1100c1d000554005000350024005040c040a4a081510360340c0d000304403003003d11760384104178012164151541a0190440d07450311070161140d0103080000c158800081200d49459480244951401c0e9a4200d82c15120201000008010003074010255044016505484150110600d1484480c1d410141040c00c0c0b100c00244140040340d4048030307a402908007840c007444801000021f0442c4040c1e001d01b0b24072510301e6070f092452aa240101c460194006507aa10124200a881e116420318054030444d030410040c4251007650008038111042074440c0740d0200c49500c0c00b003801122900c13004c0140d62030010300246442c0c1c075411210322440240c0a9030030301a808001101c4803510740c0035241c443e000c1080400c90019043c1d0051640c42d01800c1d404050034660703542d00c2200d40c002d92007050202e030702410b1040b00c0c0c40c051120a144041180007000340c0c140f65008248103000714803440100340c404800095025030b114040314421507024040e0f0306203240011000009402c1801004002442e010011 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 64545992 1250 64544742 64544791
    0x30106020f0c03060103110102010e2a0d05070b0307020f150f010905040302070e07020106030f050c0a080d0c0803071e080a050106053105090a0504021f0509040917070b 74
    0x40b400304018014001581c00c46e00c0b03000d03912a414004078119980c41c42101484181804400da41004c1d032410546070074041c4c1400100300e800381082071b1043c1e030031081c0c00740050070009505045a820722440741c2c0740d0790b9500090742420001c1681c0c2c0c4503070048002094209101c0442244514143c034800c076002d03603c59191600300c0c0d0303080320018096071241000b40301d0a1103411a141d80a41c0c4c0c1d200110300161266241568501d188008480940c00415001102c0c507007943c0410152005400800c505140030f500101900400c1c0c5014045a0000002c14507141c400c0d82040c0d0107407007072440313060003d0041034010081ca2007129000c142034909000403c18030300c200f08546000c215448062080c1c049580140304038014000701d50240d1140e44400902c60311104801362042d09282c600180c189014014040030180111191119034032248221120580000554501035000d580000381501e2602d048003243c07039a001281c60f10310000c20020100001140002d103e8812403040b085807041003541d0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 64547242 1250 64545992 64546003
    0xc0801090e0d0c11041401090b0d0816080d020301080303060f01091d09030712211b050306040b0604172104120309150c0b06010206041104090c090c05030106020f 71
    0x40c0c41e03550700700b0300341e200e1101d00c81d4032600c81035801552140c0e40d42e405a00050129801d542d4000e2610407880c00401055145200d1004152001d03a0710940007000303680e960381316200c0c0c060103c1c0500310501e03410302401a01029a48040c15103001159a96180c84c125039507608200c9015110b41658103142c4540d501c0791990100b1981490fa200000d10041e0910040c0c102c002031003109144001e00104011504ca40681120361256840d000d0f0f940e0071100d031200055071a0032096a089090101c0c086042240d000c0ca042e440c41d480c540700c7d8580d1113400c000703006428684403840d8001c10100340460143c04069600010380421000c59003201c1d50f4030550795101c11095240c4c024000c05010800817510961261a03596109161508c500764075004c1102100310f1520303202000451105880040180b102c10507038004101740001c000c640341580d1a21081c80e140014540102d48031ba00034010040040034520107001654024412a83c5a20008102c0d40003445a007006215041050400b107401050 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 64548492 1250 64547242 64547261
    0x30102040603090618053415080a02040b0d020d140109020310050406030f02060f04150c0309080102120a150306110702030610120f031103030a0603030e030111070b0406021b010c080109 81
    0x1915008000d550f60407803c092003204e07c01d5445000b12280d0101800e0302d01e170030103043c0c01c0c444120711401c405c80060000e800240880350040c07040106010f0400602c082e220b01400d8050017582e1003c03030070030300006003c440340000501c0c8003040020541c01090307009107200c0c50104801402d0301e542c4a080000303490491201610b031450305011703d005414a00e000304460f6410700c00041c5820303940c1001c000c5000341c003a1888001281e40400d4010103502169000050180714020360410380754519441c50044017070301c01a101c1e5900c3d424602c5002c01c0740703110303002560406020419251401481019603119090881c8607000c0c2c0000610070301040c68100090782c114000d0007212040d02d903503c100c4c1c1440304006805016603200d807940308400c1000154410a030301100400e1051451801901740884a40014031030303410300441000e40303455402034401194014180400d103031201c1c144a4024070610b001a549010462400c00584005400040f21400d01c1d9a902000d0f03a69590520111443d524 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 64549742 1250 64548492 64548503
    0x5030402090606070c03030c1b030506060910081203090d0804030903030810210605010f08030a08100e090708060c040e16020c0405091b03060705030c0315030102040603090618 77
    0x101240150404110180d8000e0340902054580a400d0302c8144c032094250740200c0002d95503403000020030520041000d030390041c18100348452815507440316114074008024901514590b00000e245c4501092180010f0080800790355000701c01e0025042a640101e40c000e1180c0302e005103243c80715100f80000392207260150340d42c284036400c55500f196280340150840040700c0e07640301301080300588160400e44100c000b28104458140714038060381900c10503480020204002d85080140080100031507681050510b40040c0c039035980c0d1203424003512142c01c003035040c60841d8200050980c0000e104816950070000322070a964800c00b08003114031940c0200201407994601103030040c1000240c6025a18050056441001012012600f1910100c41c030306a15440282c22034084200c0c50907448030388070280c010345001e252441019005100142c604841c844000000035003030746005412800340c4600038022766a07199200c200234007403e00c070141a54076134605030b90703d0070302184480c01441e4140c1c002c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 64550992 1250 64549742 64549747
    0x806010608070c05160906090f0903050301060c0302030423031002040f050103020d0b03100531030c0201170405030d05010b031005060a03060306020705060103060b15070f03120515010e0a030305 85
    0x40b10202e41c0c0c440662000c985071703c030f00c902e0003c045054a002c075014000540f0006940b500e84803000301030b1003500064201d85031514540c440480d60003012281909ca29040c0403120740d00a15003249580b00d564000f0100e24800b6508140804007404020000d01c0107c0440e082c4000301102c10040340700d60302c60380c282004041400c2180794013036009002941611600003c24050130710100382410844001c01110541d9081001405000d1035132018100c685515038001800038a8101c082c40414020040d042c80082c1811b1802c6a201d418034000c4021641d28004150174585002983d0760070402400b00c0703c82c184030000c40c90300f007448281e0303118060381c1003a00b48a46c41c00041c0706c000e41c0310300c0c0c0000405488040106c040344c1135000601d179031403141c03000301101e626608102e41110418071103103100756264299450070011280075121415040011040900301c5450243d80301540100c98100d01f90418040010036207620410340d4401c4000e0725550001040d480c204070810490340001070104d00d05 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 64552242 1250 64550992 64551001
    0x10902030f030c07050f0d1401090c140a17010605030d020c130b010e12030d020c070306060b0a0c170d0507030504030e01051c05130807050a17040e0f0402040f06080c0a0806010608 79
    0x202240d02130201c0058001c100c0740d07455480f159500303030048c0010052030391110710400c10456030400240007428800881c52420318404000344000010f8420050040540116a500b141c004c1d0300c080003c0c0001400c035140c4440f01c02c000f9440398600d00300240f144484c1c154070040c8058074043c00c08a094141d450108030143c801c2007182c4020340464980c0c19210500c00404803849520003450086400b00c01494020f1460ad400011340c0c501e5040400419002d10201d8511908940394000d0961704c58445050440c10610346440340c007521031015030b01410001400103c54041e44509c1c0558000d582e6405c0c0840c02600540d590304c9807603030006903c044052200d00c2c2c011a58801900a43d1a6801b90080c0b061521880f0f855009624103036103542181444408001d003101c012112002021400c500b01443d0108085100310018007940f004040315001504541c3c5580c800d0101180699080201760384440b4800c0e80d401a00105c1801100d80700030110b144140003e4450485070141c0d2b07202c002d5511b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 64553492 1250 64552242 64552249
    0x8030105090702070332010b030703030c11090a0e0609010b011202090111070e010810050103080406032408030301090b042714010c050d1d0c09071103030405010902030f030c0705 78
    0x2e1518007103018000d80031000074070302d1a014503400d01c5484d80c280480480300a914514910804c103803a01d80c9085a520b1603510003241110849416040031008900581080a100200010134660142d550810015150f509034882c0700c41940d1241110313804d507500c1044900302c8040c2813000d40410a900c0c08408000c4031900180802c90041c50580c260f1001055824a4428282c000701081465480144100c050070001904c80c0440188240182d52554466140501c540d01810007019101d150340c000014015100c1849003030206681000c007607403801c000d62079420038002d000d21a0f060040040d8030345018060700345054941c2c00703008040900d50110034081207040c8022a1081c441000c2c241b04c10b6801e00c552803003080e09072a032550368550012120201e40088900050400318205c0d01c0e00d00c6040018001e01f6000156403a08054031038080c180c40f203000102038450b0790704c000803c1204100040d049405094400d03400c507850996141441d07034480c058a5500290756000103010851b500c0c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 64554742 1250 64553492 64553509
    0x140a02100f15031b03200306061c150b0d06090b0a0209060306060a0c0203060c040905011505190909020a030e070f0806070509040f0c08070e04020f0d0b15210a0908030105 75
    0x300004c01081810369985d6000207450541011041c0c00402c0b021015882c103061241c107600c000f0880700789d88803200c80e400c001c1d030384281f030039015020381c0f00c0305400c603103030407166000140d07524004004003090324007443c0003409400b4030321007110101c1507080844c0c04c403081030082e1003010750f000784850b080d41c3d642c2c001d210301500107011220421861030340c1d04002d0b80381404418011904201095642c6040c000c0709000e03610182d12980154a148842d0152158014103460101c120401c95200044400404966149958100510715480080c032020b4060b0540d1003418100100000e807800d240c2d5801c0340032030002c4580b044040b00d030807410008150500c00d10017401c4030000107200060741c40c0c900c40c140040b1915510328034049504001800292600b2004080e0030510071101580b4052800a080712580500d4000c0800d50b07131100344407589603841b000850510b08140c040f0603260315195000030f003d4071280008119280805000c5030b1585d01e14000e1a091640080c20130703103140d02c0c1109000740903 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 64555992 1250 64554742 64554773
    0x51003291305060615030606030402040905030307030903031506091215060e040204050f06100309080906030405010519090b01060c110a0e0a0c031b0807140a02100f1503 74
    0x880c01808140c14016140d110380380541c0e1405038400544101d840c20754035249001e407206200703d490000400101110f242225805541907031820303140e07202d40c400f14000c0d04170348000503c1d900008c82040800340d40340d400b503c1450302035a800d200c84035070341ca00b41038110118003813680011241c2c2030500c2424a5103947c2010180319049100340b41c0011010b0034229012a004148007039030708402c1c0015403031b290084035001401c60000031060b040c07950000d290783c3d41002e000c0e000d1545442c040018410b0400c2560130740c24002d055984c2c1d03444c3c1480c2490003841d0031508004090314418036124904428030680030000d50040a064030360342496000c0e952a010002c00301c4080102c1040034000e602e0b402070034001840f42c101ea180e85800c1080c1140c003074440d0844484200b41c941000392449524003104244406207900701001e46885400d008c1312070311442c910040340c52600141209102c0c1c1d0024505188820b5107104001034203c0008400030380d1000c0006044c0ae49400340240089184141c201224 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 64557242 1250 64555992 64556033
    0x180f020108040302190809010f020d080a0c09180212090715030b060d140103060b1203030c03060105070f0b0108070911031807050a0308030105091302060301060c020d0c08060910051003 81
    0xc1c0f210300c0d1006051280345500306e404110111720801e8550f00440c108415414034005000100d4003040003c003201d4006207140031030b84e107a8048070100c81c010514280a029003402e034500c210300c2581d008003e940413104088606542c0720004816143c0417401105035007039a00b880d0b0800501d040214098011108043e0f1b201104000c9104909200c2c401c07a04404214981741d0358a40c17450034500e040b1080004064000c80c1d45c54000c4070420300101c00c480d03108481e8070380140c4940b561001200c3d036004e00d41c0c00800d828140c1c1d8030400cd214110018604176040c031003c03a1805a141c50801d01964400c070030490038414280301041c608003800002e0440c003d00f21040301c0c0100c1c2e070740000440c0d0050f10ba006481ca07181c000014402d41c01d0011095a00403065401c202c05550076501107100e503c4144103507410008061382c2c0b681190703902d03513050310001d800c003d80d0302c881600c600c1c040b070b15240d09588040c0a44030300390300080c4284080c0a541e210b4840c1e00d65502c8405d00d1511180f045052392518001c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 64558492 1250 64557242 64557253
    0x90714011706030118030f030e0102031005190308031306050606090a120f050717070b09220908070305030a050a050709050105091201140612030304050604020d050a020406090c0201180f020108040302 87
    0x1403c40100900c003a000e0f00968403034585880d1950041c085a027000104a040c0c2d0041003003003540d1452075217200071075000741c4014002030540000c1c4450242c550f000100201c200005026201c800e2200c6000c5c5240910020402d50b11031400300f0544d8070800d03c1040d0012921042000369080404049402c1d41c0a60b495010f20364285c0d4032039043c000607800040d094401d0480045408004000003400b40000301c100c10701c1c003403210001848030420680003050310074840c031040700f5610344c5410104007a079005696a0300c52081d45006000e41e0000c58140040500d407800103242001d0384d01805003d02600d40380c0e4a40c4274100390045806034001c0d085c1a030080324031411540e0b040824400e00a13448480c10281c001d60600c5403c01159034001190f200b495170081c000d01001c5240801d50a4102e98100c42c4115451030500e0101e0503d604c0500c003a50140c50000001503e8165070842155841141c0c001c000071a5120414810082c4180c8049c00740642e580c600d40040d4068841d450b0010700a004445 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 64559742 1250 64558492 64558511
    0xf1b0a0e0c07150606030c05070c0e060310020a0503040201030c0305060f090703090f0c080d05030903040608070e030313170111030a0b030102070f0c0302150a020a02010c02270907140117060301 85
    0x4505410707503c00c094415940c10041104903410b2003a46e58030810b03494130310302d0b06445031664801084103000300c0c100030441c4408100240e40402006105d151100c40954585a40b2400a040d42e0070844090380843e0404400d00d201a06c80d1054600c9140c0050403200101d07416400d2103035240c0c004114a0a1555400c151800f0078505082800d016102c4c03030358650381d207007420140780c107208048440e4802d0040a00c10f00c540386c90080291010b40b011480c0041403940d640c00c003181e81c55006502207416000000302d0320060516515460143e60f0f01d603032095011a840d00d0349600301c941180d9104d1001d001407000c03e94030202500403801580b001000541000301c25111841001441e500c22600c0021661003013045082c030400c00698120013545c024108902050042e44031032003008000e041011000e400c10866441c2c030024440c03030091003030700003116685144102800e4400d44100c201e600c80d41900103900c0700c100300103441185043c0d68044440e043e0900c046070030000609003982c95502e4a0029 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 64560992 1250 64559742 64559753
    0xf0309021c0605010f050f09011203021608010c113009091003060e0601030f0206210a0c090b0708042105010c031b0c080f0a09170f1b0a0e0c07 63
    0x700c0e006015200026155152041c145494400e0703600c00c40c0076190400c2022580d6961801c07540c111000144441450b0660380780c200c4c14a15120300f14007480c44801e0f40401c9030141580100c40814540d00c44241c0b40e181800c0640d91a42038480500208640c0141015629103080c41851442d141000103802c003110300340000c034800701c12900001940d09088040080c8881401501e00311210003020306055411500c56400e503605000019014080004001440d0030f035240c0d00000c0030034200c40c0b0b041a404c03c500408050004011a00002030781c0d02e0001c52b50a0948044581c1c030780e40242c2d50341c40c1c1803030b000c2c44d42e0912018464150141d203140304e20102080c4203024207001070715030b541e0014140751410b2000c54101c44900c035803000c01003251301450000324500c0c00c45d00709292051100d44c88143c0000101c8850009400c0200490800c00f1011444c900c001071911907030032120181d0f084080801c256213100c00039040700503841098800100402c421803a1b0030b0342c016aa205806140801030341302c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 64562242 1250 64560992 64561039
    0x7020604051e031903140714160201020f010509010b0102070b031e09100c020102121f17031b0706020d0203030f06061c0903080105120f2d0601030303060602060105060a0f030902 78
    0x40c40c0400e0f16941c1c0c1d000c0080105142d03c0e801f0303280e030034a0040700c010f01c0c4c0005224040c5020412400e103039028a8400c3da07008000100441d400c20380244403d1612418042c080d107842c2881b10301502c201d1001085803c070313501c03c0da4400d80c180703850600c2a001c90140c09000e00c2d4050880c1c941c901841c0c52005800485004440c408004e9800140c1d990403c2000f94114100042242d948a10603941280d840340349180c580044030140e00008600a50400f0503506501c144421002c2101c202680311129603004100c500071540e0903000d8030034144100f501642c80b840211560f0070203052510010301c00f0318210b0050502480208094003460882c5215003048407a0390105074046816000100300c11b103010079148844041a20203000c0760b0441c02c0c1029900c0407036038801035200d1a40f0001c4e0710f08500d8804070800c04100e410031600956500e0402500500d990302610006015443c00440d0034180b8604959103802c80c4e680c1c071840302d04248401c40040c2107682080740c0c455007201841e800701c055a42c8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 64563492 1250 64562242 64562287
    0x320906041409060a030b0718050310060e07020703022112040e1602010e12030604020f07080d0c08010303050406080a0e011e0b0409020f060c070b1204020907020604051e03 75
    0x41c104120403611003040401c56000340035921929415009100180c10b1060607a041100340c00d120a1428420000c020502c0c0e140d00b1031500b40c82840300e4100e5894440d0071103800ca44a03c000e08180b0744582070304a0716104a0301020f50070030185400034012090049035401c0184041082d134080300c8100c40300b00f045a105038450400c4403004401c0c0240851550703d0150000d00310f0000b00041819900d030191911003a011603a0070590200011301d03691500d8040300c00c0d0407044004180c0e1000c1c98503041d1000d4000840d01e0307030504d1400390f00c0714405004181c8141602c0c0c05807941403e02d46071000c1222031110080040800a441d94048804d94000340280c81701740d840c1398803000c06506901801021075100450080c448d9090501e09c40241c0c86600086424540c2520016078030008056101d01c0d02d02c0300d40c01007030881c50000e24503201c01c1400040b20b016038400c5031120410303169810120307030b10581558040c02030382021940ea90b4800040300005910940c413001c1ea81850700c4000141000d946410303 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 64564742 1250 64563492 64563509
    0x616080d05100e0f0907060c08091f080a020f16020103090203010e03030601030f1a1c1a060411090f060c0705060403050d080c0c03120a020f0d0c0f32090604 69
    0x840900108501210b100c1c2d010702804c005000d41d01d0401581c036035591080c411001880705d011005000c1c442118122105240d015102141400b0350118800100d00d40c2403501002480c250003041c400881402116641002400f006042400c034030f140600c0400b046100301c0c1070641d240281c0e00180c50070300601c906100207001440e100d240010014041c1c502400803104900e107032595800a504494210302c0e44280190355407201d8900309039000c902d41c20100b0b80640320904a0350b01100c8418847c0702c05115075030036101408030341119040c2911500039081c01951280c00c1708000000e506040014006020701d03902107131002d540d03690108e01154015013040d11250030503140c9600b501c1d00418417030303001800c007039410f860203401c00c0302c05880e8080c001c42480900f061074045403205490740c05460130310486c4d0000641d5400030500c000014031038805400040b620465804a203036000d050001100441258000c1080910416081800c5428295410000f10034044044587c4452002d4805881680c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 64565992 1250 64564742 64564771
    0x1101050412060c030b2407020121021c02040518061309050a020901060e090f04050304050a0902090f03070f0306050402030307050d08090105280b0a0305190611090616080d05 76
    0x8101c01425980802084c5d409581005428648101440300e0401030504038003245440e0016480103c54a0500441307aa1580384000c2c1da17a500b0703248990003418500040840c5d03201d881d20300c00c03e10b0203a0007540b06c3c16611080302c20b0780e850418011a0840e91100303000380754404043ca1550710504980c8490420b99083c0d0000c49044110304201036502e014184604114500c0406000059080c820040441007e00340e240c0c08203041103010829100500002400710351442d81f00c00d000002500301c03103c0d0521900850f0450000c42c1800703c0d9400aa54034080b9641c003087c1140c07504000b62070b01070022a098407041090310042503092180501280310740e07446890074108014400e0964034041d0202c0c4025001401600729111050440d01080c64031060204005c40d8001c0014081441ca03400a4100d001ea80c0c002e640304a0340f0f555013000c1522507102000345860340e07182000c013030090107a030780e8000038100710820205244640141c64036110f001454513207000040a00b080c0c401c2600c4c030340219060b8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 64567242 1250 64565992 64566011
    0xc090108010909020913030c050615040f0b0f1005040e0106030605030607020118031d0901031506090501050604030b100b040e1611070e070210020c030a080108030c0307110105041206 80
    0x80c8485006100e600c80600c210002900081c0c02c9240c082c01e502c8075614204420b000301809040b030b0195068000c1c0945145140c00c01c0c41062840d00c3d08a0144190314282000d281c199080c41403030050b260142001c14035a281e4420b220001e07100c2e00c81e00341031010a0100280241c3c030100a280a09113903940420810701c0e1906041c604907016110000750f906181d2045012510402c070000e4061b0945809403072440c0210078000030f031b20780305452500b0860400021041c002c25250040c034448400d01c04002c0181d80d48085030231200207009071a07200a0400040010a102401c00350b000300d9075807002541c1070fa85286040d4a607010394482000481d1003070401840c03081d514080c480310045401c141d00026004d00280f80c89281d40e0040240310022080030603100c510801c0903da50001c0c40034110b5488025419180c0d0301d81040c18503400264070480003103400380010040d2050082040300440c1400d0203990382d030000ca41c2d0160f6882c1000b4040c800010305031a040c80b400740590040c14000303000402c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 64568348 1106 64567242 64567247
    0xd0f0c02060d090f020a05030f0c0d050309030f10140613050a0f0207060902030706050c03040303050c10060306020924041404021204050d0801050301090c0605160b0c0901 75
    0x3c2c2c01108400c116022080c044d031280225516152241d0347c108150780d5141c0303003a5103401600b201022001c10f04095145100440c420f80c10b4a041c0240600400c0c5003905200046003103610a0715020f000028038880d10094201054500f4082e261103000328a211500c0e00700358600c81e5540001500283c500c0c0d1100d50a504c0300f4100395540c00c000d041c40c078040d2a040401f84e00c01d01800100284060250046440c0c3d2403141028506241c0b0303544040d9059041101071070780724081d21082080800306445050041c5129a00c010b0300d40083d030051154183c40b0009050f00c90307985a00c490a020f01d0901500c040310450210303c6501104c40011030041c0c001d41000308007112502c001c1c0020448041805840c024065507010090380c2e0700c100b014280c50a119002e806080c03280b03400e2250350701c980700070300901c0c4505403008903401d220303990f000440d101210540825400071400502569 = true := by decide +kernel

theorem cover : BRFrame.Cov 64388492 64568348 := by
  have h0 := BRFrame.cov_init 64388492
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64388492 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 64388492 ≤ n) (h2 : n < 64568348) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
