-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1166
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:33:13.743496+00:00
-- url     : https://prove2.me/submissions/6fc4e5e7-2ca0-40b3-b2e0-59ae1681ea80

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 209532374 ≤ n < 209712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 209533624 1250 209532374 209532391
    0xa020907020c010815030715050405060d06080c0d0c18020f04060c020909030403030e09040201180e0a0f0e0304090e03040305070803030a06091b0e0a0b120412021b0616020306 77
    0x29030009a5541e01140c4c1c150702042420450454a6920300403035582d80b42c62107001d5401035005604c45540c0e00c9a0203d4000703003002401c403510350100d100d80c4001003000340304000d480d104900d20003501f07003481c4000310b840c0c0c1d81050744480051b103007800c1c2410781800ca0460b440e881d0b9007040b502506800c1c14000e0006080281d0310900070b885c0c82c1c8141f1a460b035000d4640304443c0d0080c8070400010f80e01050040c01030200342c0b1f0b100c0b0f60b51264030060301e41c04e800c502c01b4285504c0d4030f2408606600c8120001d0f105a03100802403100114080300d00048414070324100c0c1513900300708001e0006400c80d40000c0400c581c250100c03840c0550ba6101c3c00d0900460b0782009556030000001d00c5044241806040080d045400c0c01b0480c4070320032041921203020740c0d0902c81c24001100c469130701d10380d1a0881c000041c90700d0002caa5641c83c0e100a00310300c0081c100d4080342d5a031000b4007a1656248005880060707602c14a1000031507000b60340402000350008a95024002000a00500182c07014000c25008e079611 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 209534874 1250 209533624 209533633
    0x91509091f050f0105092e05030d081504020c03030f041a091c0314061210020a091e050a030807020f0d0308060a1e06081012031106100308030412020a02090702 70
    0x2a4004404180042c1e2180740325802000500501d020356818000d040c00c1d108541819080b451007ca00f0114025404a9410702841082e030292981004c02148103007840e441c01c0046216480800c422401080c00342401e660084c80003889030340110080300d41040c0101c3d148804840764a20140051200310b1b11401d2a401465200401d006a0006140005454201401300e05142d151490703d190004098074461900f07131494a03100c803000c4c000501d209500c0001951780b0400c50b0303c00b900204581c03040b044243d400954800c80c051800c0029800d550000b0a62001c0502d5903c0d00c10072070300822030a036800311800c09501e1250303071000c401c40602071003a1554502e5192040030000101c840358051b144100300844c180510389401e001e8042650740703d0800502d40d440c2d003182d407418010580c0145416142e0400350b01c2c03c1c5a000040034261341c07401c2e02200e6040c0ea421f81a40b42c110228400100101014800b1600007010441d4030450003440d071040361201681500001d40ba10f40c25292100940c01 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 209536124 1250 209534874 209534881
    0x130501150603060902040e06100c0b0112021302190f090b0a0305010e090a0b0a020703020307020d0b040203060702030a020d050703210605030f0604050a120216030b0114091509091f05 80
    0x10140070702801030500c03201c1142418903054251180c50390041c23000d48118801d81d0480d0100e801141d05c454022b03000303440039020b0740e1a669023412400e0369020991080141e618400c860503010700844421103107524180c0010385072448241c440800309072041080c40008c040114081003e00c0162a26140c00d60300070981c0c0d40b61001c03025400070090040a510780080c0301a501141c2700001c500d401c200346000c016a22203890034100c0c01e500131950000d510484201800d014441d014200d180241c0c000c071306960301038580d42c07016603a902c00d005000c5c01681104010300600d90160018268941c020708001c03100502280c903200c0d40440c40c2018103592036942e4400e0003139003010449408003e00d400e008007014141502d41513650433607400c0003001701c42c3d8600d400c400e01303100744410ba46020b400c0014a6078039450703180c01c3d051028240581d00e00c2404031f00c015111450a041918044c02810019083c02c2c5881e1003404401c000040c00d805031032003001980340c444c14150154500c900c500502c00074030b904 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 209537374 1250 209536124 209536127
    0x9010204050108090a0f0305160c030819090f0b0f04030b1807140a090216050a030e01031b0c0b07050f070c0f060819020903010f050705070b0601020d050a081305011506 74
    0xc00141c0001c01551142d01c01d0310010b12140a0714006c142c0500301941c5806070b440d030a450b03181296000424000549000204000060014001d282030345040000c03540300c104012510f542e51440740c290390b0600141d0800164001100500140006410071480c3c035480c0c0d1a04c2c0602001502e0700c2c80184014403178170360000410b00125000c0d11070b41100315666007504001802c3e2420381e00541071030703560020f503900d900840720000402440d07128058440319200d90070090000414100041d01083c245281140360f40c207010030686c41000143c551502980058580d0b0b00c80780c01c02400c500c1402070800005003419448809422070030300c195000305d00c503403c02c2504080110254092001e00800b0000c0c4110b0218104c2001400d603c0c03c40c00607280c1400c000060f01408680e6424031209203001c09024509900c0030007030042c1c0b4028480f4091076101e00004a9076008020109070000d80300f030003580e90041c45004210f8102114100d103504800142c3c40341030865040001c1c11090400c0c40c81d007000380d41d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 209538624 1250 209537374 209537387
    0x506060109151d03100c020304090f050103030507030e0102151005010212092116031a180c0105160507060f021c0c080906070c0306051e090c010e01021203090102040501 74
    0x10100060003080b003a0044801420752203a0600844081d0890950030129403004c0140c030440145012060098109040001e5140c2d8440c1c003a0100081c10a100150610302d82d004540c12294107940c3d9914022460f10200d918110003501c8604501030f4a01040403505044c8005000d40340034427400d00c0341d5280c0000a441c081e5034840a0b440c07140c1c18006180d0903910641c1c0e082c104121103060107101c054608040381805100b0a24408591f00c0c46004800c0c0b1403680340c011500b040030701e41c03001c90381c07241e84080b40c8405401050580d40d9220403001921b5510403405840c2000070f48102e00300c51442c55494509200c180d8008100254084018085050341000f43d0300b8041e104030100b03c04040071520042c43d000c40b2920281401c14000340c40d0030a43c4541c01101c00a0740c0003105650020345910300f8402070141a2141e801100320b140390001e0300c0000c2c07070800e030090509100600d514002c070030041d07441c0003c91341c00300d0550180130f00000764096900004d5124030b101074001a5a00e0a001c00502203 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 209539874 1250 209538624 209538629
    0xa0c02030d05030a1413110102031b010219031803140d0e0307030207061412040305040b03070e0a091a12070b030f011505030603151005060c03070618050a06020306060d05040506060109 81
    0x1040c1d10402031100d000c006d000000b40b11074004101c110901844030040c0d20307601c2144100d80c00e20445034074545034100194064090702d4100c2103e2924503040700000c03400d8480c0301e1581450f5445445034000028003c001d1811841000a1100d040c10200d143c640102d032100740030313165aa000083c629040513414021071015000506282c0110201c1814001c043c0c050440700816914036035002c10700717050007032064a0082580e026481e40c1c83c503007020020318007040c0e4043c080c000d044030300010071040482c0c01040582d22840e02c00d060003009150401c04024803102c03924106010b204004207010f200301006510444102e00d4110711949400c0b03142e01c08030020405e800070000c007801404034659000c1901c070b06030310303220414400c10745400a80c8400ca030415841075071300070000601006000d0010000e40001d9000364030400078420f141010340c99a003480701009000750440340074000064016400b45070041005410141092940c048dc90129282900c05407078961142081054035a40503100401 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 209541124 1250 209539874 209539901
    0x5090c070807081c230907080c010e1c030507050d050412020f0a05030d0906090b070201090b03090a0b04240b03030901030b19090506120705060f0a0c02030d05030a 72
    0x541151510742200c0382c0039800c2c006020860000d403028062102c10385207121504420313820031500107800c09101500c41d00f4001900b154980000040400c1030114004044418940c0500455800c5900450341c4400c40d10582c3d50008000e5286440a1801e0b4540d114943c801d03112240e49041900b402d03803901c59200f031076800700403040000740680300781c403d4042100740e13041d20201902c4902400280c840e620a0b00025090321429070b0321500c480d07100e10420100d91040c1c44018616440790000d00c460301c541007011307000c101c2c0312004104c80c02c0441c00542d0f001c2e10200a82e00e4101c2c1c196920010001305070360607541c510940c19420400200b145583c14450350b01801089194030b000003003501c034050003030107505155640c00b03d03035102d480342c1461070601c0d072a084d005450687c0790042800104010b41d443d84c051178140104801158000079204203903540100a1401c01030200c810030041c2e0b11129003501000550991b920040e107003009103018480107034035116100d14111540f80308540544000b9130 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 209542374 1250 209541124 209541127
    0x6090b07030c080c3c06010b030c0a02100e0d0305060405070804170408010f02041409070903082a06041b0317090103021209010e150906130606080706050405090c 71
    0x1c0e4001144800d0036034071160007038075002051411810044481e102c800c500c1310350000c418005c40f82040d900313510001c1c03041000030a03807640406650b5407824012005030050410205200450000107030640704103903c11039055040482d444016681e034044001e085a2000072101c441582501865a020605440800841c40d00302e10080c800800a000504000003140c0921030500680c01120043d100310310080c80b10002d0360210704003c1d80036104801100c02c681584030100d00d4001c1c2c01c0c90140b400d503582c0d000f0b642c1c11901d81d09004c0d0f00601c04507007002a021902c24955030f8018030342c1c0d041022030003e00140d240ca400c062501c00c1c174000c0403c0605440000034030018108110003c5203180091000303803900e0072030005030002e200398804030280329181030412000305c3e015004110a0070300340042da592403000c0e185000c0d280d1f07029030b0011001e0300b20b54002200300c0116075a819125010b03031008542156a0107074a801d102c0c481e04000001a000181880f443c00c08406682d0000131284025 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 209543624 1250 209542374 209542387
    0x60e07020a0201030e01060b21010501030504050a11041407051804020310061103070b041202010b01180909111306060806030c031c05090301060e090d0f02070b090121020406090b 78
    0x3500d450700880e0080c1807540d600c2d03034010ba40300250b0101c8090030207005460b680e1030120b03800140c401c051541c2c2c1140b00a003480042000e511a000720340c040c0358000002c00006100e179540c08090310070400881d0b0010707510720555170580b807a00b0400b8002e40311a1545a41c2d001c1080c00b01030030948800d81680203a00404c18440e01a00c920441421103885141c54198403400107041c5085205941d030281041d15140144020f01014a51502c45509103800070055030340300b43e005503500b0704920300300c21020600750010880c00940760000390b0341e9403003481da00880102a02c0020011b803403801841a529a9844090000c03541045899421a070700701d0051004e00943c0001039a100d60305140ca500c811494840c2e90306280c0a6001d0383d80000e00240244001d54440421000d500c404441c00742c880c0c420f40c3d005080681c02484241e1061042e40d003d0b0101070704080a000c83c6034403d4801c2410400326a8148140e101d286124010116601d24007580e00ca281c801c000f4411006900905412102003020 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 209544874 1250 209543624 209543627
    0x10e0304050103111204031e0306050108060d14010e0d090f150e15180a060c050703170c0313141509011b05190204110c03090d020a05120709060e07 65
    0x10303182111070902c3c02040d40d40c05034030b070b114260180b61001c50252140c0d07000d202c00c15030450510014580b2940c0d480d04880c40000381101960380b944500c9020940f00e40c0803800509298038014640780c020075090038003074010b008031406c450341e0300304001c605e0300009002400c542e8809443d000500240d48600061400d2840500c1c000482c103010205010314044a4883d40c0c440e00300c003604440c40c42120703e4480d02e44a413594151005d100381584145075001e00802c4550040002e00a090b0300103000f084400d04554902c0c00c43c1c40c0311004050740140034004008c1c081c2041000f40000b80364400603050b00e070301d4402d406945543c640c440600c40d00811040c010820342c03100c26916101800d2a01700c086014845504103034002c0c041000d00b20780100343c550345150350301c4140d00410b2442501c0801c07d09500412103c400d024004d8007500d140c00410060b541460420048020b01e03000401c000c8013581c1d541d00244541056902082940d003001c84200460800785c420480105a140f46407460391801010 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 209546124 1250 209544874 209544877
    0xe01050f0325050a0e0a03050d03091b030c050406121a04080d02121b040b0f0f0405031614030102070f030c061d010618060e01170a08030a09030e03010e03 68
    0x20008040000840022030107240301c00303030316100d002c0c1203010302c8404020640200184c0c0f103d0a49400309281442465843c10310124501c100c9030440c01400791416608030132400350184810503281003080d4140d00c544a11102c1c3d00c84021407080c2d500600c06071a15050000b511021340c04030303102c850003915281c0801c2000c891622200300520a80f33049565520f03003418a8050003002901280c0b020030039116180c50b408026014080049502140705d0709000c0c004450700c01c901884082000500c000360301034491802801c0359260000744607080c562a040401d10b442104203480401101d514010401645201c0404020700000c0d402036240c10f2560302c80300640d184050b0018204010002d42c04207210055100d55240ca440c0704e01d050b40e0207589042d0f0760103402c0f00d0082901c6215903860380c80081c03940344660030454020000b80c800c680c0c64504103a070b00301448500e8075076500559a1000004032414020340c030454007d40c0001d20210139080080035440d440450038017aa242610742141d4040020 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 209547374 1250 209546124 209546137
    0x307051603080f16150f15030c06110705042310030c05010c0501020705010c1e020303100603020a02070f06120f05100b03070c0b1503240a0c1b030903060605010e0105 73
    0x151169194521811584065844103029000340e4400c800e105602c105c0e50054900d00c1210031007800001c5500c01c0800341454640f100514802c071641003040503900404003081101c207100c007031b510342a0361240460162001d080200c080640802d003079408074400407400c142c204004642c0840307500c2c10355481040300d8009000365410f02c2280711962007000740075011904503070342c0b040003030200b40d130100009010b040c9500c030303140c03a59042e40b08400300c058400415a48906520b001c0b14441c140b911030164000e41c4803866002c21030003140c0c2c0200707501021200c0c660043c0203690300c00303a40b0814201c015040702c03118007181e00000c3c208018000c68004041001082c2c60003501e505a690321081ea00b6591400402d40c010004003101d41003200c2c8a8204a00c3c0440c0081507080c0c40d01c8101030804ca00a50209000c201c501414400c08100c0341c0040f42d00c003114810081c24401b03100c1e20746800451000d100c1c004201c00107000440e042c01081510301440300108028200a9008111000082c00900581 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 209548624 1250 209547374 209547397
    0x10b04120b190e1e0d050301030215120403050d0606030e0c13150305010f0c0207050901150c0b010b0c0f1902060711090108030d0c1d04020d1b02030705160308 70
    0x601050042c41c200319036020a100d400301c10441a49401c0c1c055031142d000d060201804a451401014030034000304407249042140d42e038003031650b801c560801a80c103003207014460300c1c0c5105104a01034500d4450050340034a020343c9a050b10360b4001c1c2c8044041e59030540021003050300b0066050115500013402134505a000c0310394901075220111410010700c90340003007030440e9024050000034440d065204800f90101804103100c01440101c0c2640e68031641e1003130907001400c103001084081500329031080964030b00d05d441c51440f030840e140c0c01c04c04c0d0000e8104010b203034400504039120280030415851521915409082d101840786c0305054140048d01c4e02901403040007440d42c080001008841103a040010407000f010f58581518540eaa0084020100d071140783c1024640c03d0381c056242e404104000f40000a000300788981840040e4000c15400c0c480c25480d030750480345a2210f40e800a200342c2c0750f94006d40e110980c508141c2e14003c1d40000110b00048500e80c10f2011a5988080741d01045030b0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 209549874 1250 209548624 209548643
    0x50a0c0b13060615020105060904120804051207030314060d030917010e0106060305010608090c090a0b040e0d121410030809060408070311040f02090306060f030106030b0f040308010b0412 82
    0x11200c00c80d03254810030074000d04891511070301080c4907040c03411042c40c240b02c980c020030082c1e50b00c40500c0700c1100196400340c0f10f00c1f4051144010315114180c0140c1c403522036004e603806074504407005d55054001440460209480d44c81c2480c82c099050790640d070110f811030300c600040265840207001080280150744200c00d2005003049080025044006041c001e8070003003020a903258001801040e0070300440340050b0748140400c07038203c0001528176181000600529054a446400c20001c0540f0031105410640b0795820305001e400610800207010040c1d1140c200d60100002500110350b49201a50f160305d26042c20b0000986203144044140c80c1e211a085545400d0700001070b00600450f4442655807181070300c04001c0000300b2482042004090b5002d2201100180c0c6181c02d90203404081d40e015801240081e866140c000c60b10041c1d0100900005101500d949660741104400c481110341001008107020826500c041020b00508051402c90705146c1080a081414808840c000e0005140c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 209551124 1250 209549874 209549881
    0x20130507090b040311120703080a0305060a18051b0c122a03040303090b03090a020427030507151112041b060f1101060f030b041e14060601050a0c0b 65
    0x14803161006016140410b03601c5a640345800841c86410300201c2d401042c1011030381040b482c0002c3e540003039991160748507080410344001180140070040c400341d07000032020350004215144203c12401d03045036035800310301481e054140002c400c01300d0030b82184140d01004018501d1401160700369803c44002c015940c0da050092802c043c0701803e0082c5459040611100e8598000020040040b41d02c00d0301c51194660740c0351010b81950100725079482c1c0580208a64a00518156208401c41c40550340c020000d064500726541030399071020411400f141000409506022807010140c444e525241d00500024000c00c003610603c0c05611020040d140c1260041342c10421190705d504074041d4480310741a003aa6844a0040207110404125404529112a04510254180181d900f5102c9185140c800140381d95920300c0e80c0900148140c032014480e44101a007180d0f1215032816031401050900d440c400c9a08005051a0001e410507042c020100702d11018180c111135281400c5401069100c2c0f10758 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 209552374 1250 209551124 209551127
    0xc1905090603010b0a0f030302100903050306100309050303090d090e0108120304030203040e0f190b100e06040302042c01060806040803070c0c030b0709080307050a08070c0b07050a20130507 83
    0x1503035810315903214814040120b18440c0703410b84c1c81b0489019034210384203607500480309400c4858101010740000e40400001e442400d01d000340401d291114580040c04094039260141903800c2601c1005954100c10711101d041c0c1d0b488540c113006050a210032007455407418801c503903527103081407a0f007015080100c0050180360003401610024010416481010320b401c1ea201100c142084501c21403a681850aa8690000d944580d420803000035140108a140010003690074494144059902c454100800300041e10b81e030180e800c8107070041c0c56032034124011f08201c103003081012b00f5041c00380c1c4c5803010070003e1a000240d103d070455000b1400e903599480302c06d401c6a184000c13210103403410620120010070424184130b0544500f50940d0b6083c60b15858443ca16164800d000c006000356012003000c8000c20740d1070008090491045000a83d1255681c1c0e079004290014001a00d0a422102d0034500340300410703600a441c945080c1d12424013081c184001410510400d4035071000d25910b800203008213 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 209553624 1250 209552374 209552381
    0x228020a0f030f020103110915220f030606060809030a030203060f18061e0d061a190f05060f1207030e1009050d08010303080f090319030b030c190509060301 69
    0x500d0400c0c0e0a602080e141e040190b600050b21200301c1c0001d1038410358851080c1400c048d1034a05000034102c00340c5005080044109402c01130900d80c59440510b94030444040180c1030070004c0c82551451010b0301d02c2c5081440c126005c81d031000045c0902d280c10458181404400c480c0f40c03000f0f90500680303a84a45005c20040c4800342c0d00c45412031040100d03002c0f0441c1c010f803024443c113030895400200380b05601080f00a010b4420300f04c1e030000c840d103c001e800600140c1018040d601100701081c0c00000e0000021a521400048a04291101a014080c10000081280103000302380e83d42481c001c4070410420192248202c40708921a10401007555a03101c0d400001c1080f04c98001c942d8441036440f030780381c02803019110480301413080d80074084d000b50140c1c40c202d048a4141d1107043e401d55413038a000e0860840105400d4032404108807400c0c8001c006464007803411582c0d40e0004040a40740c0503d4a44140d41c50340c1442141034036100d0072182680380c030a00230b4940c140c6044c5c00b56118640480e014 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 209554874 1250 209553624 209553629
    0x70e0408090a03500a1a160207140103020a030905030f0405041a0f01050d060806010e0f150604050d02010905180603061302090604182102010c0228020a 67
    0xb0002542c80041403102004074242078070000f80d5084e10b594403640d07000c985100703080f4002c4200f5820700c01c0150121620264004080c0d60001a0303100303c10316940741c007a8170341e43c3c2d01450b00101c0c40d0400c0c4004c001441c0d14041c100000c0f03000030950b603800d042200c13000e000d451403001d040540004004244174469004220216030103011240c4562454690301400c0c2c00c68010035000b98500500218200d0341201e00c0101410050034200720507a255004460075806001050381c4241c031010009140d210800419000384950032041c542401c01550348402d995014114440610492400a0440d07403000119402c50f001100c4400c2070740014401078640205991005900c18030200b0507040602403c00010f100740000c41c180d800c0e80e601c940503030350f2184640801940040750540024036609069000c0d002100010444c8552818265500d010022003031117800e801c030160311115030b086078090051207064403ca00241031201c00713043d0340031080002c01d00324415480c02d460b0803a0554482038200c001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 209556124 1250 209554874 209554879
    0x813021c061401060f031a0607081308010207030801090e06010b0a020111030a0213080a0b1506040306090302011b050708031b091002011509090203030a0e040b040e0a05160602070e040809 82
    0x20b00c0342403082120800c0300901c10000820203600d240c2012602c2441907000f100580360680039484812400d010141e0400082111032401c2040348410306001000000000c146c0362002580c1d402482c0380043c00098103a00268259040803028081804049103060641c0c1e40f800d070447c2c48148502c0e00b2070240c00a00080c4440ca02e00100340001080f26400600c0c440005415401807076990b10039032a51a620340d580a8042c3d503503100450298041a0168003036544002c02480c02c2540b01d4880c03504603465054100c026071364900c1602400c0c0305041c45400301080c541401030a04141c4d44462810303201c001c0100a006581d000c034250400d044600740c8041c1c0c0002b4003004002e6441c804041e00a00c82c002c1c2c02e03000c642144d8000188011280100100303d54082c026500b02094418280c0701002006040c4c1e500546686050201d40c0340c0340301c0c54943c00707a1003001313045444c0c40f410a642080d62200482d05110011041803280d036030009125400c50344035880d4581a40d035141011001e502038580c1440c1e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 209557374 1250 209556124 209556131
    0x20402130b070203070b030c0f0d09120c02040c030506030a030c020414161101021309050703060512032110211203050105090604060608151309050304080d0813021c06 73
    0x80501c10300019160261003a800c50b44002e071104459503441c0021104414110010401d040c90811582c0241042501900011401d0001981e502ea1105510042600000c2010101e241986000d01403044006c005043c200418180500400c0e11040007520103018406400010011515554402d40c0440c0c8640d01902150802954002c800180340301007000151501014824014041c400c8442e2006284590100249850007200150030b0080005060503510ba000003601e465920801009100304c45c09195160403d001e01e14002d1540070249100c1182c0742c04028015007290800790030303607004880d528918600720001170300300c103080000140704000070a40c401609030503801050594000311481034055598400340b00446a081c8284d00014a121002c200c000920000002c1000c1c0090500708a030342a521a041c156000144111150b81c00054208580c90341400025060710503840c08074500c0c00d25402c01e0301e807251040006881205104502e19002070010101340c000e41e030040e801d1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 209558624 1250 209557374 209557379
    0x60702031509030c0d030501050901180e100209041107020f061c0905030322150e010e07030809104e05160c05100b03120310031505010e0402010c02040213 68
    0x1e0f0b00e039001620252220f11466003003009140c000e0166905850019000810030fa10700304582090401c5250150900d0360f454544030030005007805004940154881c00bd079986c00f00703106210886500340902004820244040001680d9156000c0000f0200320b4070f940d02c80581c1000182218001000f14100a14051422080140100c0551311600052041c6060940c1562241d580442c02c200d0017410103a0710a4440d0000a00e40d00c00c00d03005100300000150385111226403850440d41b40c0084c2d41c0003c0100381c40c0884c0c9068111054030302e400d8500a808105422034030b80001c80a04500c0500d0546064014005400035401e0000c0112852000d02d107400c508003024000c05003030345c5860702807011941e4041d5803405011010091035205006003c3c8071030310b0030010003d10740c0c1c0a6596040c01180b40514044003030101441c01548840c0c8038014a0749903113426000345a0f0b00e4140010581448010441c00b14985522588650282032402e0326104601c0040c009107e01070403080640d101c2c1002 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 209559874 1250 209558624 209558641
    0x3020708070e0a20070303051f170f1c1d041b0306050103020a02070e100305011d06280b010908010203100305010506090411330a17070e0607020315 65
    0x42c0c3e000c1c02603440c0c00c002e80c80720580094062012103400c5402403600300584000607100c2d0707200c0d50703100c3c440c400440002c0520042d601800001c5a03c107015140248001c2e2aa1900078884103102c0c0c0d001100406442d0003010342e1004c0c8070b5403100800d00b482081c07181c04988a03d410080c2c011210f009008201d002c0d0780f8009120307611031803288070000074949140492254001d01c201d4641d60156002414090306c0c1880350290041c00400e00803103120120000800038a0901854041d0305503c11481d480d48010306500780b801034000c3c040800f460020001183c1c01c3c107041c4601008106c40c2e2070104d11161072000589140c2c020f03078056070b983d610000411906081d41d0310a1000d44c4d125400070b10040d03c403102001815002954040c15905c0380030000c0780c1d1450f00b40021844194078555514500d03130300f0740c40d18107a44000e21680388203c00004e10103124030382c0100da6900b0b400c0c1a004000660400706001043c10140819081c083c11340007070100195601000090f900d4000110300742d02c02c0c6480d450 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 209561124 1250 209559874 209559899
    0x312020d05041a09070e01090207020411031501021213090e0a050d03320f0618010603050414061501030209040f020301121e051b0117040b010509011409040f0302070807 74
    0xf031400d8009503a0011640c800008600c1e034040b0703040f00313905c0031290342000a010029801510201d038010350b541d000e5a454500100610711840340741c480140361180d1079002a00f8600180b0705111609420044022035408180318402964405c1d5000071700c030765101c40c0281c035040c1d010101424a10030329001ca8011039068010701c601c088800d1543c4503408131802452014034021456500e900540170024450340070030149070b94845401005842800907200c0f980300003c8080e041000020344800801c001d03c100c032502c81f5102041e4034018442460203551280450301d142c081c0343d0426800041107045542c840e0082c0c910740488210440d0b0703a50b940c281e80544980c40000c00c40e075090080c0a0703108508a410940644c0341d40040141041e0181e180c2c0392001140c0120248e8184444000806401864110120f1203075101e0341c6140b0082d41084100403002138140d00c54800c1f011503c0c07610302180c03100e9020b01e800c40d030f1108007118401c8240c03600303901303124842d007210301c0d2032180c2440007914030302015 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 209562374 1250 209561124 209561153
    0x1205040b16170d0e07060f05071101090e040b070201110a020a0204110c0304061d01030b03281a0f0903580e120405060d0b040c110c19030312020d0504 66
    0x417074200c140d60310780c10365102e50141001030100300c090092030003241c0c850340000424001450071410954a404500c1d2442d8030503502619402200c004000e0071b03640910a068082c01071064040c01c221254070700a5540300300c0440280195118807618544641c04000d89140242c070100f500d44441d26154001d11032217040844981003001703020042448c1d4080e05c510326895402801500900d00d21100c104100c0e103024078411943c8030703640081e03000310745840040740500094800382d00071414112601e443d6400041e2590b241d907001003101505002400425489c01c0007800da60362034980000d010250300e4216030000340000100300a850311028801c408000c0308401916041041061582402c0d40d5003642d02120045c8560401c02400a071030803902403d46900002008a0340300405000701c1c0c140e9042621b510f01182a020010101ca03809209481c2ea44505803400c0445000001200740c14006c41c0c80047d042c0014490180c10043c4203404541020107508270602c003c0c145854250b0098a070030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 209563624 1250 209562374 209562401
    0xd0c020105011406030708090a170d0b041431060504050d0305010f0608190905061b07020f01030b0a0305010e0706170603100b120703060501031205040b16170d 70
    0x103001168483c816009a41c611001030a03050a669940d6020348208101070540c0301a40329490744c10001034a0416003180045070601c00c82d841c0c0135921003a0b8141c030140c1244601c1241088405100c80a00e40750307003a0302170814000318024600700d101d4000b40b481944041c3d0440c0d0110114041406055042540590310490455800d2144450102c00b01d0f6000e0007400c00c1206c00c3c1900700b00b130358030402c42c0d030b034104045c41c051908014158048070203c0b07a031104101d07a00e401c500204411340710a0040143c0b00c00103040d4051a00500380e0014101b003100c00d4506040c075030340b11008592500d40d000c0c42e401640c0e0000007081448000fa01d401d0b0340712440e02c10540019102c0700042286680114521700a050181c01065004c024040300d00c0500030108060b500002080810450700000b00303d444019401359600195950460402c4140103038030b40c8611003442001c02c0100011180001200c95040b0700f01c24444040442d840c1800080180100813103107120003007502c0d84580070a034813203881031404 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 209564874 1250 209563624 209563631
    0x50f0c01020403050f0d0503011202060d0504051b0f060403060f06050d05030910050a0c0f022209060f05090303071103090a06050d0f11090603040602040e040804060315030c0311150d0c0201 83
    0x4001c40295610341d40d01d40240000c002303100410500c044403030684242c0f403008201174200700c005400345007200c070f04940585065101d220b407e242010a50303c1402090001c0d14903280344105000400d002d03120b1484014074959545089070b9005845900c400701400c0e009094074854200c42c10310560b280c0114042a2183d0224040e103807000e4000c1046443d061300315100c0b000384074043d803200e1080680341e880980c0c01052000d100c20701040155034400000c86620342c00078462100303003499412144040c42d41aa014038200a20030a0f40e00081913075030100d45441d00360220a10320000038118010002060340065440b03001080040e0090041d080035107003c0001c00c8942c144180341e9065a044003a02001c460003046810f20070700f07150380115803180c000c80b00945460741d42c3c103008000500441d0155005c03080414148034045d40340c041e42184042e0380e260624860304540b5031001d6030030720b0b101c01402e007042d81d4404016a00c81e00d69802d8040500a81ea80d01c62014045c04009491403c2c0e510005518 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 209566124 1250 209564874 209564893
    0xc0d0302070c0506030411040e011d070e0f18060f06010305060f1c1407030309031506060807030e01140c0903010e060c09210a0501150b031501030c050f0c0102040305 73
    0x400d10036101c110350081d15603030b2038918040c00c1c8070b2240c1c00540151601030340071840e42643d89503401140c8502c40e481000241c00c1c4c401800c0b111628a09884c640281d4200d80800c21a0000030980240c029000c255030301ca070741d22161600303480b92520080c6903850303014410802c100c1354030000c0c02c20300c101000e8809229558419042151510203a018158082d00340046802c9140800c8841e240b960703c04c1b0f20b0307526041c01026803c2d15000d69680102c00040407038401707204102088070100720b60529150309204040c140f42c80034000c0540100700c0010103559204a601100c02500030aaa4040358010007091742414074003804035900c10729440e0b000350300303080c21a8400600014114410141c003a04141004039500070020100c080d1076000c800d14400f105544c91008003449101900d612a50001991039414410004200c2507517001d00750040c0140f041000390150500c444a104000340f03000907119550100c01d40d1035010320300240c2c40000c80841d0300b5850900541c002c20a49021741d00b211185030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 209567374 1250 209566124 209566127
    0x5010f05120408090415030f0215070c06050a050403081314010c05060a15050a06051206010c02030606121f0204050a051017090709090302030a0806010e010f0e1507080c0d 75
    0x800c010729034816007249030001e00425990405804161002030010030070520300f04c085643e0b11420b0b00192902411752850307000b1450f25003015404e8002440c44176080000e42d499165120816105880500800143d030340b90742031060044034091503004d80c4482d02c0d820071542c1030351000030324000c2d02090040c90800740b65030340c0692650000d059110000f000f09a4070904000050010003281c11100d8013228804180750f41c4410041c0d026216035903816464101c1c1842d00e0900ca04090001070500030b020900e800540c40c0883d2044d4000c60079100d150128200d0726110b4548041c2c40210070b003500e2104038100a81d142a0001c0c000c40e1011078001e494181c89908204143c4500c48000003c9800401e42d07081d10300070311461076402290441600c50040d82e9a94000c25a6200241240140c000003001d00c541508010601d800447c20b10b010246d85003031800207072405a403c4a03070b005115075192a5540b540e189140b140d0400c0810780490f8407040145404141c030740003040b00c0070f1140a900340c840c6496 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 209568624 1250 209567374 209567377
    0x90602060c0409020d090803011e090b090f10030203010c09030605090c030a1e060603061d0106081f060308280302031b0705240910050c09010f23030105010f05 70
    0x400c00808801c2c50540342c0b54601c8000d5020126440913142c8841c904004510220041c600070404d141c92801d5a01600d41d511501c8161508138403080745c50152540190340700d40c4065644400343d880d00003035a488071040d120304000198002580341d0b080015084499038000c050740101c0e071040310180f04980342c81c01c000d038481c100030300c0349a0950710100c01d100c01f107080ba00301c1000c4241420201c1d141e22030640c482c1400e0707841540007a56507544944000e90350004801602c4a01070500000b00100d0781001a56526003410841e00c40064442e80c90503801c2c8007580e40400020340d0b001308a590b88030291101c8105611214200c803046a0064a805000303500a0003100d00c6140c24841c0b4220752014107021250ba42c108542c02d51315071003090305250600000d04415203c1c2c48100b40845403618080801520b0100d179a04005c80c000e01780b0080c844201680b00545051203000d003810410100329450454141c250855546c0d01d010401c0e1648a5544810b40114160740003a640d24009546144096a59 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 209569874 1250 209568624 209568631
    0x20c1614011106070c0321050412030504020109030b191409210702131b020a02030607050a08060f0f10050703021b060a030e03091801050406320d021c0309060206 71
    0x40da0402000204c2c218800c0c1542c801440c0301f03003800012003103a101020840c0e0b000030002011342d0b50303c80601050001050054a08001502d000d000501d02580000c3c010129407100030409411035010443c070700c1141d80410600e180808040200c000340300380040100005490021003800f4090113002001144084030440700d5a0300c074110302d03248040d030900100c0e1209030a503841e41d5656005001c20003030100c203003200101a40c1c0c0148085800c40c0105800c0c02c9001e4961001e101041010355131043e0840411503000c401143c100324500c440704003046030001c20044040c1d0000d0711901d00c140460b0814003800320039011b5404c48400040e0650310f010004001d100785940f01d2814094002d00380d20a0b04020858010a8182c07802c00940c980807030050810300c4070303512030385036507400500041c2424414480142811030740b450342c02141803840e000e807921002c0d410710402d0074694141c9494507400003031000641d01078148080d035100c0c0b18929002c842c07a840c0450004640d640d0001e0031f5480011070500 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 209571124 1250 209569874 209569907
    0x2070b0c040312050a2006070201050c03010f03170c01020310030c0b07020f060903010e07081f181b1806030209061203031305100606090806010602120301030206030604020c161401 79
    0x44003203900c005132059084464032608102840f4402c41103004604200f60312005000300401c0740381094000a42500c90080c081e60250006100400c8a048400e020004903500b062150280c001002014091842002c0600074250300000c10322050b051008640c0c1c00b202e0040c0154500d43d51107144100061203441c0029602c13400f4060851000d1801100030f0880d940014000114405200c444d01e051005507488000c290304503006420052003200503001920503290740030000460324601100c0e604881070000b400d1600c0074940c114001c0c2c4d50320600700107000071280100b11210759a1065007d00384600041f4040d0080030301185250070020315403105640c000e030166082d580c443d4501d65110503020010f036501d00c02d11030749843c43c1d05540306401c0506841c2ea81c4001c500d040c205998a00321060344468115803002041e04040740144045e0703410742ea81111810b030b0341c0c0c88840c001070290003015a020068011850750000c550b083c0002c05080f2000e00e603042110b9529640103440b0f034020301e101c0c0c0c82d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 209572374 1250 209571124 209571143
    0x103050708010630020a151209120309150204080a12032a1b0602030a0b0904080304080901090503011e0f1107060b010314100302012312090c0d030302070b0c0403 71
    0x51400c1404010690946043c428554042c143d0002080c100042d0310191f640d01603030003241105a4014500c8541c0c150204090000d12190769924903180d4898400408150380d50580c0f40402c000701003d140000b88001080d520fa944801e179041e01d902d2100000ca402c0d4803241a0010901c1c000c0c01a000160030078181c3d0000c1c100018550113107449107045000c2002800a4000030062001c0300000155000b00c2d00180c880c03030179a08100856161080d00c4d41b0a0400c1d404000c0005da10800300d0f603000c2e511070103e60f11842c5110041e00e40ca040c54006a03819400c00000507000007140c213400104101403070050019188114a031011249c0c07150b83d00a10305401c0283e000424595080b0701c041500600d00041d0542c001248030901d0f610641c2c06001c03101803040e00700155a442140c0a421494041011140740840c0235505482c1c8164001000641c0800000a50f000000d01c00c48078460340181001d28038400c00d02d0001d000b035116200c1142c88503200d601040160309004156016650f00c40d480e003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 209573624 1250 209572374 209572409
    0x916120c02030a0e011209060204080c030105060918150c030f01050103180201030203150a03080c0d0e0a140a05041e050903040503060c0d0f06030f031d0f061c060e01030507080106 79
    0x481d03a200c0501080e41c18001e5219a03620440003907c94001024010f03880140ca49040950450800342c0c00c03281c0034803d81c10a0f0900c80b0703da0f54030407400c0c2c001100011400c2c203001e5214600d420600c1007400720720b0414103002008030200e45007005505c6081c640302901e18507078036100103600b1160f90518841e103200701d14034000c005502982c01117401c189801c1180d02e2540130f540000301e409090b5041254589000308030580c450f04100314141007588a0304191002c542004041048210f561040710f1b51590304201001243d11003a8003080138000181041c061000b242c9036800100750074100300b0300240e2800340001d16003031f40401070f282643d00040240c940c40e11000c4c145182a040007441c420029980e9400480420340ea00ca01c0e40150312601c07036041072005c1420701801c814505000c000300f424810007020025503918403c5c2c15000400c66489071900c1e03c2c6501010001402042200098502680844c0e50348200620714126031140f421111307038031780b86c06103682614030f20303c26101e060341621400b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 209574874 1250 209573624 209573627
    0x80f0a0c05160c06020d0801030f020409080c0f07060e01262203080106030b060319270c03121403130f050a0606050906060c07090509010207020916120c02030a 70
    0x20490010614009003030003142c08428081240b410000c0b20460300040c4104a15501445050380c0840542000d014640c55034135680702c13608000400921640d40c0c0c201110410104100f0389414075415004c0b940030740e038002842d664850f094000e0102045088170584620740c420a1003e0740d89841e031401d41e08000d2907456100141a000e014410445940c0100103149200900103509042c0030341d0b20b44681e0752608901508460501c640540a048200f0400c188502e215480c1084400008000079400c00d0310140445801c00c0d0500c000c81d417504141c404001d202c0f900c4107034800c0d07034000c25002c2d072540864a402e4035071098403920090a44418400100e10440100120003181c4c092407600380d801e94159151400c01c60028000c90b8016650103092041d4100305072019841a01038405a1501c102907240503500d5506101d503080c1e16031601c0000d00003417000e4066902455024203070381e0403400d02a409441840c04c0910600014150000303016560300749000d0045e1900494014602e000c480480 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 209576124 1250 209574874 209574881
    0x5100504031b0c03120503070203120a0b0d0b01051c02031c02160602010c0e040b0303121b03070203070501050f01030c05060306010908030c2b1413150f030b01080f0a 73
    0x10503400d100d441c0d01e600d103540d1002c25459001038401d07104030107050b0461030f00d082111204104202040414003c002ca416000412549080310083c440c046c41c0e59403051a0010b4040c3d51900794020410001c1801000301945000f0305842c400c4504404200c0c80040c11114840b5054019500d640201c0303684c0c9800000e2410241c520101c0e105440c50503800168010480a0703a030320240060707541c3c40c60070181c1d56101849904041007120203001d07403410783d40001d0303480c007810201060740c0e2842e80114650203014400e1010741c07903040e00400d0306c0307203001e2a02a48a40005000b51402d50a02000410b400000d40312036050702c4e03220307020101142c100000d00405420040109061003813024000c11540d00400243c65229003042c000c204400b01c0d40c2030b208502d600c14204036034607107100b5000c4d0301c401d82003040148650380f0046802e07250710380c40c0c81a100405d155840034003c1c4880c69200e401083d0700c40507003694400151420301c220300005d00110360903007003283d681031071682d15030120f00a42a80e42 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 209577374 1250 209576124 209576131
    0x906040b1b0409050c03010e091f0b0112060602010209100c050d03050a0209030109060e070501030204080d0c0218010e06011103090a030206180a1502070b0307050f07020d0807030e0a080a051005 85
    0x401c80303410640c4485426044800668003c20510300110041202603c80f0810305d80c4a0b65580c0038000c1500381074225441c0300581d07c0e0103210305445107500180e99104201d8250010110381d001d0009542d9248068001e5211041040c001d4005510b009101c0740218030901c1d409034460000c0c1030502c150301084004100282c180303640144c01b004042c0150b0307402d00603c0a49801808005400e02c3c1100c0003d1a0459940c001414107006010030400044e01164080c4440740701e003017010710182e0900c00644818600003c030800e06080d0000401c82000c003041c118841d041c00e882d0012003801d0352004681e00d000c1d8410455201144642c24001404c001d00900b1041120380002403034020140f0000c5c4620803503030052840d0400646014805a5041004030000c107080c1491501d982481c2100030441c0c400e19501140c01140041c03d841152940070061301425040b5418139255a2070781350042140044691051050744c41d100080780301d40003c11040c03109075102d8010b00189010b007403540064007008 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 209578624 1250 209577374 209577421
    0xa060c0305180607050f0f1603020d05070b1210050406051018211a06090f0601021204060f02161206050606040f06110d02070605071b0801061205060906040b 69
    0x8007102c1c14240c0b608009040010b2185004e81101c0c0000041c05d80b0b0000c404c510b48081da0722400341c0440707a0104409041c15690103880089140743c26007451403500c54191700050a2620015484403102c0c06881e0081c09000c2100da08100359988000b00420b5540c14010907a205210003544404240185041c00090040b0a0320115583e51140150055621040d001503240b00582c800020002c83c05550300c0f4038104207a060155003840703000701d001c08000400c5040e0740100400410341036130082000144414003c40e516941d2a203d0714024681c01101c04484058807515410710020542105070001f9241c0501c61407441c1405502c80a0207002c006d022150000000c11001c100c101c4000030141c090a60360b254104082c8182000900d0862403040e181e045401c01c20061080303c0d4803000b19a80d0135049140b61081d640c40101d41b030a94010b5500c01c8009628100b00010024441071000903400c1c0030780203070b4020740c3d02c14460307584480b01120010300e840700c1203000a200b6110416071200d0b500b1007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 209579874 1250 209578624 209578657
    0xa051005100507060b060304080f03040f200102241308040306060b03061305070206010303050c011508251202011103190903060507020a2001020a022d0a060c0305 71
    0x12800820500441d0000007400510300069003018480c0300c0c0643c1c0074602081d60000d1452800e0348aa40d49405481c00a4000450000c08542400411345801603802c1d0010b200d005485061107a01c8103100d11034107070f2409405201c0481c0c4440c5541c90b05908103900001c1c81800f04e50320540078440a180300f060844121500340004030100703030540310364005041e130074001e20368a007403407401c00c059181c5510320310741c3c01c0d42444200011346030f0100740c01d411aa8035003005a00c820301c8014050141c91000d02010003c1503604001818010001c0c40d0000c510221401d9403441d58102c01030400c48001e40110002040e403140c14100651240610101240c420003d50f801e0000324108018410b04c420355890026080010038810702c0114421950041c020303000810780300b0780f95942d070044c4c00034904540a1a00f07400640c0e1565034000c2c00030b100080c1c0d000b0704619264541d8440d08030360034025041142c0c44010b2540c5200e02e4180014004103858840d2220390340d181e07803694100c9042d803201280101c10204d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 209581124 1250 209579874 209579879
    0x12062101090602030105120712020105130302040212010608060a06171825051e09040501020417060f0711070b0c0115060215090d0917150403050706061a030a0510 71
    0xc0c419114010b11541d0056a40c0d4904401c0110a4a00c07184210564112807420000d0070185090710103c00e40c2070a104d600c8240384504c0041c10344440d0b2010f900300e070000480311138001c2d2111116050b210551915040c0c0e0700c0d00d006004000205009040104008100010114141d00350056010714550311070b1500c501d609010034288411000140345118288520038119400308100da0003405058842d00161046040100d4030511400b811902504034800400c0a110085d012500a8907144204040e00c07049840c2d56980c804049480ca45c290445030040340b4564032910b0035400240d0014000c013061030500144510b03580c02801c8040ca15941e42c541c4034101c10344000c1c640700910942d000303070040021308032259900107001040170120b50011412080301d00d130828001c07804c1c0e0b1f0751100c0c2d403c1c40c1c00c0154081441c01c100141b000242c1c1c404141088201130384003005200c01c900c40d013418400e85039602025039589080b03003941001f090080c40028084407560340710640c06109008600255907 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 209582374 1250 209581124 209581189
    0x40b03010912080c03071b0549050f030c0d0c0f02011406031e1f02030907060c05060f040317090601090605030a020f061e0c010c030e01021206 63
    0x3a031601d42182c01c620b00000e038a142507040400507511001e1401401d00d1458a01c000400c40d05495071010746025034a144c40f030034070404101c2d820120700c407101011004508100c1c0d40b1046201d48120308585803120800c3c44584c90313440024004008951122400c4ca031301928141e002341c10081c030003581e512050102c0d00402e1814061405074680755100c08880d450340f04002400d460401c0740c654041c203140d000740280d0352000103c007181c0107011822600d00c1105510300d24140101e8260307142c17800b00701c4090507050f18910750040d8001c071418000c9460382030fa64a0700380c50760320084030041c0c015000b19001442c0b00400b01f030300319401403291519041c2000003805810b9640720030b40e00720301c06500036001030003642d501d0310032500a05400c07002803200744942d5000030000484421007901407a03001c244c9510b01c1d000140c0d440690540c801d01c150701c400d00303141e546008107404000742e0300013414100111600103041c82102c02d0000b4500074400c45031f603071200b4007140f40004604000c109503100381040c0f860 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 209583624 1250 209582374 209582381
    0x40824010620060a09061d120f071a010504180305040b03040f02030d0c0b01091802040e030c060411040506040b0108060d050304080f0105270304060318060f0e010f150b030402040b0301 81
    0x2100510304c0000e00c1c07415401c102c01220402c1540c040030305400c4602420703c1400103130410080410f140096550440716190f191540610f100081004440003440c00001c02e0103285641612000e1714100700c00703010030041c3c1c42040d18443c405008a80200000d20600800d00021a03100d0301a4562170b22600130b55011030714142110034890005200900da071301c10031003059802401824444404e201c04810f82405200c44041070100901c1141c1d2094032030001c80080c81070310b02050101055545501e4241021340038501004180c9205510f0507000940501c1d051050414400040c3d440c00b110341d4442040c4030100700d0703112040d141840305010001d0158401c00050904142460011401c0d0906070402c04034108040b4107506104121442419400700000944046900034980070030b00394520341e12030032945c01c01240a00345d0f504000320044800d4052700002049603041c0d00821111005240d07680859100c17074010b04951a03116070801c908000e0601a54101e03000410005a0100031400603084 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 209584874 1250 209583624 209583631
    0x30c030b0402010e040204080c040b1f02030c10060605030402040b0409020a060c110f090f0a060b1315030b030d0c02031203010801060302090a02030c0a0c08071704082401062006 78
    0x31860000401c0110f590050a24001c4203003914254100341c03c000e8090b444100410010b4000c950700c1d9022443d99030381e01d402c41c003491401c0104001241021400a440360301c01c044e100d001e4800e00808a640c1c003102d101c1c0004981d03c541c0c40600315240d0303a0030072010f003140c905032355800364451f9904400340e921024007600900c4240ca0b4105918010302e401074082c1258075400b803151496502d0461952503540e00b49038840f04240d040b00e419540c2d1120000108080e400c10058110702203000c0c0c5150300b01020103419202d0b010340b00d5800c17001c0c2c0142203054078000501690941c0103903118820290003079010900442c8014241e440c00610620290701c560026030064107181e45070749081007542042400301d41c11549606043d442e601e0417907107061030752144030a1101004000002502440440c030140e50606502140c140b08010340381810707050540180c010250709005000d4902c054080e1b400156040071025110310896130f180a000340e807130110340048809503029046d0100e40c41c200c28000c0511 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 209586124 1250 209584874 209584883
    0x1b04020c1b19080a0b060613080102090a0504051e07030b031009020f0303070305030408160614090606030304061d04020405100c0c0509040b240406031a130b0a02090406030c03 77
    0x14007816601000101c034421600c40000030794494003800090808140c040c104c513000000e0484070745440e00414580d220348910140804042c07400411604010740080960740b80842e4400042a00d50003044202c4106466000c265101c103c1a0751110081c000c0580c3d01800c1818002065800080842d082210403e40d07299116a217049450845c41c0c4498042c051101c02c1d0011400c161055802a1882c840a800604810b10204449141d0005c0134418182941e0088051186459900092420f00da09407019403881c051900024a14200001950100c403515611070782c0310800985810f042c1c40c0c0c040e00c03940e0001d40070000401c86448104591311440310954801400f4070607410b04100401c81e54000510071034101090002280c01c036403a4981054101003051300c5000c3c2c144c01040d19520781074160750041c0c2011400030a1108000c0144040a25a205455903588001c455800ca40700803c0c0280b031100c4c060041411010b6a80c09001a111f0144c0002117003904c0380c80390441c52000364008c95 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 209587374 1250 209586124 209586163
    0x9060e0a060803040803031f0b18030601080c0102032703030a080403110a02012010150608010b1908040807061e0b0a0506300a0603050d0801081b04020c 67
    0x92040c0092040030010180c1001940c10281050402c0c2d40303030300c03015244011072440148900c0401301300403841d00062030844000d0f80d43e00300ca2080060031420214446100e4004c1c0b41c0005000b807004901140061416409140350041c101055080940500d000074071000c0700140501c040d450800043c0341c1e25485d502c942c051840d0601d002802c2c1c03445c07207503908056003041303000a00603600100d5084000b6280040015040200e6400900c4e019400b049980500c3c10501103000e580c3d846d1020006986c42c42c0c6d0303502100c0e03072944c20345205071069020b110180145400119041c41c4250704981d0041c0c480d41c005860000c0684400040d110402070342c103040c680b0001881e032483d07150320170345440c5681600c0a001142c0b501c400035540c0d0181d41002c0c2141011400b858600540c060103043d512031460410340b5150505070184802040c1d140022141d0340b103010360082005000f4002070781220401001801229001082d007004040c8041007181c1040c2c00307000c4604183c40c00d0200c0000c10030305030f8803603 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 209588624 1250 209587374 209587381
    0x6050304020915010923130204080c190311030304030b15040c0813151104030b0406050c040e0103020112020f03040b04050c01030e120703021204060207030209160203030f04020a09060e 81
    0x105860000c0c000001c100c1158168074040c0e6001074206089406c8818141000b1020303c1880030b81c1d08060072150707031041450342e52807081d450700d42c094016691034004907607050225009012100805801d00c440d41c0b02d1401040001802103038401101d100b001d006e490519580380c0d5800c0d0b034035000b41d620b01d081001315920986241414850795030250600e00e403105071070405c0f00d81415003030280349010b004088103001c0c252010f0f80740d0b0810f185203d90104141e540700d942e410164440203003640d089903540d04000124003050031a500f41c0d01507619000459410764a90780c0190780500c82d024002c400d181e0280081c1d40b070709030658051032096001da0401e0605140c82d14006040c01e030441c5d11141407516000c2120300b5000b00040c0824a4074400c100c076666a581030900380e00d004000500300c8000003001801142ca203502240381000c4920a80f030300507060310741500c50382c00c1524020f80500140e0050000900000c0c0398281250810b0020301210f90041d1204031420035103075650044c1441c0040901030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 209589874 1250 209588624 209588629
    0x81002030901140609160e0d030909060b04030c0b1309050a0e011103070507061a190603060b0a0c020d0f05010f1d06010305070303080709330e0a06270605030402 71
    0x80724071102d00c460803d40985860302c0056050080501003842c0c28801044404038a406039003141d200c50f000030901d00d50301000d45402845400c4500480b01c10500b010400580140f41000b51401d4039801f100480650341400e82081d00c0340c100c2000751008020344103000403024021312405015200902c808501c4c904d00400030360039900c0d1040e040c86608410410006d01541c0202964001e40c0d0242002c502808400a07101000c3c840442d440d501180c621640d0150380c0000074260101e0702140c44c10701032031365180c009400074052000c959004c2080182c040005241501c0d100c0d003d207116100840741403074540c0b115800c48100c81c00c03112800d0742c1c1d2a00b200d0000c3c4c03850160103a120000d4002d0405604640c0c3e55521410b07688002024086c80e60701140ca501c0c00740c0584800307006a108441c040820722201040b0612288103102007040300081049000c41c42051080311080700a0680c040c5546007050445108a001c141007441804079010410308000700c084000040c2000d03a68640c507810107004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 209591124 1250 209589874 209589881
    0x7050d0203040305190e011e020a050607020705031b010212091c060507091418220318152106051f0305010e07080a02030711061003030306080f0a020607020406081002030901 76
    0x41d00c0d0500c40f46da502800941ea002503984030021400e80448002d0280396400d81c1b603d0503415000b0154000c103003c00c130000b50b000484500312003046046525849201415078071300900d0003221801038001420445100785244000c10300483d010708041c1d14410802411824a14441c904407803c0d42c07500140300d0516031040300b42d0098041d0740c02804002007028006802032007444107522404800c0c2d800102c421070b4865104040910380542010354041510340184900000000400f00c10050b44003c160710701d182070840207401e4151580c620760300840030044c0314105000c6c40c06c0349030f0791183c2001c1820340b1041030016958005c6542d80d00d108804e902c0c0501a500c05030400c5400c1c0d04101e00b0800d000b503200e442990016004100141e4a0325011811600c100c90710101603103521680091041031000c3c01281400c0328020365081244075140d0a900323490f680c600d030701310003a541700550341c802518004008103202032005200190302503807000d255041c40c915801e01c4070792581c0801000941c800a02 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 209592374 1250 209591124 209591167
    0x180d0b040b090f0a0209060f13020702011b11040e0c0a0905060901060203131a070f0302031c1802060c0304090e0604060b030c0915040f020301140307051806010807050d0203040305 79
    0x10f030000200e0840c40707aa80c1e04a50801074402c1c0250030101d80640c4032031070950301880700a44400114101d00081c1d101070b41c0505c104078005400004096580fa51040e109425a81d1107500c00e41c0b2140c0d40401c1001500356500c03500340174018080150341559a00150f6001850001008506494040d0400c011700780140c0c00305081d500200107210031400b2940100c819109110230340c440341d8036501502d01a6005545008055080401c0744030b050680001c09444400409405000424103444041003511803254034644090460080d0388014034216000d0316211000301c003102e040968414452003078cc1c4201c41547c100350002c01c21b01040c03000c24050f08101d0542a0014800a400c0c040422825003000380503484d020006c2c1714100039030342c840e00714240075a400311065480e0350f1034a1241d8054001c440100d0b200748103030040050399081c14040e1142d00c00c20002c080805030b035528015500c1040080c9843c080281c1000701b15603800580c80514041c40c0a0f1742c581e40c0b200550711140d020b194402 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 209593624 1250 209592374 209592391
    0x1602090610051e041d0a150305061501050d050f0403020609011505090c09030105070e01030e12030a050601050c06040f06060603150603021b060109050405010b1005090105180d0b040b 80
    0xd40181981c2c00c030080f1100c001400792240718881d04060300c03441c0c900954016140240310007610f1a0240300c030800d0a405220901780030003101458408465000846100040140d04400300103814190101c13403d42401506040c041d1401c030000c4012001c1301c2c02103507100e01142101e0284070600d50b0400165900c0208130300200680031099880045c0d801d110b01c11603100c2c60440000a0b019903604080c0c1d0388180020f4000d00103400c00b900e015007158080240c080c00a8509804055034034400130301110801e0b080c6402a14686034907070640302400c0020841030500508124190300b00108000041c0310794080d038600c00c68141c551601c20240c0d02c460b8040803c041c1000c2051038500c012280c4482100e900d400c0040ea00c10451800b0280310800d01107030012170046800000e86415281c1190b44030301e10810081181710035141c00c000e2110040500803001801c144070013005c81d4040d600409444440215844803010588000b40c0010b401e410200e410f0850f81c024442048001c0040c4d41d009001c9 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 209594874 1250 209593624 209593639
    0x8060103140d080105150912010e1606091a090303040902030615042d0918120503010605070f020d0c081c03111204060f09081809010e04060c1416020906 67
    0x2003000401c443c6040c000c0520454201103516400400c5034129517810001500e110070589419120900900300e05c0c103000700c079000b80c40d220500c0f2807035204200113890090300c0b480c1c01c190508403000b17058032078074401109803a02000030b10f80c5941d082000d000104051900941d40b49084000d200e8041c8881217182d00035101170206105103c0c194109200b803841d0030295801c0000c1c000d080038500d03425a44402d401070f10b0b00140802d00043c81f454280250f004a8040103000c800d03040494061000b4030410f40058400c1c04000005031021004441041c002041b440000300300e6103d035803200d4a564070069443e070042c24031009144101c05040240c4005081c2000030010102101d00da610880d900d290703201c0403250029042040503031201c142e000858030108810202480d060450742d000c8100460241e01c02107607000c0302c1c5003010f8918140d90f4040720f0100303c0d4403640d48080140c264034481d0414041500300c031790298042d140207072001d46c0b1b00a8045210070f281e170043c050303058000b800c0b85010350300 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 209596124 1250 209594874 209594893
    0x4060306050d080a0305040510020409060f080d020d0c14060106031d070f050d0501150b030f01080f03070303020a0c02040c09050f030109080702120a0f0302010603140c0102070b0c160806010314 85
    0x620f094500d400342500f40403c140c0c2ea10b01c1d0a50038803c200300d0034008a88082004680e5525a602c48020380720341c09024580180c540e42c0c495a41d190003007261005a100c1d401d1004070a10074810071103168424898408841c80340c009107410a41c00b44c000c800006c0d80c0c1d00b1040030705554132460050400b00300025000d1142040c0e4502802446ca0043da4010454140d56408110096014864950341800400d00380fa440c1d459403090b50344141c80102508087c0c0001141e80d0310f001c2110034400400200031072030041c81e6941503010707400805d40c4509202a403c201000768480e4000c030190041d096031124086824101080074440b58114454002c2e8076110300880090412001c6600c004e804813200d404994103c007120b032a145250b04010b09210a0002140405d40c054001c041928400d02c40c1010b48580c140c00d056880e984d0110050069102c0c003800c100e40000c1d40018035070714500b0002e440c1d4280b50040c61100901d041c1c0d001004d103510080041060040d651518101541a00c015021079003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 209597374 1250 209596124 209596133
    0x70806040e0d0e060d020c01050711030a0c260d0606090f08060a1503050307060b0103050112150c0203041a070c08030f030c09040b090901050405120a0507031404050402040b04060306050d 82
    0xc5220710140c0034480c10820f0480d0070b035141c106031800c0e017a604005542e1440a4068540a0003007690f18001207400c401c028242e091011003503481401955450f5003100030917840381c0d4092580b00c1038246880c1c1700302801c141da82d440c0800801468400040c042102450580c0040c403806055100d260000c0201c034051201800103c1d03800d400c0f090421010900050306808500c051200398030080951000062403010040190407408a0032401d1700d0400c82030782c0c1c90303904010ba500b641c000103001c0010100a118140700e258802e40281006104a90400d0740f1840403107460752400b00c0c403100090300419103500308503a04d01c110005e4500d8001550400485c060000a2800080c240040c081d0000c42c42e003025450301c0d07104008840001b002203402d82400600309000340011388094495001d84251800d1513070017401180c010244640d511382c035240c0c0d651412540c4120680c0304c201c148408120000c1e50780e4950004e0400703080c41c46992659076103401d6028046819a50240c0e020780a504480400308 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 209598624 1250 209597374 209597383
    0x92906100509010e0a080747030901060302031f050c0a0c080715060b0405030d030b0108060d023706020c15070201030b09040b09010608010509070618090212070806040e 74
    0x10781c000c3c2480b0062200c1840005e4007503000d50407800191240c40d20001c4d00f9201c002e039010440442e140c1a025580d4a4029412a00d10088010034240c1031400c0e0100c420043d003000795071008041000282058403540000c0c00c0c5129040c0301c0080e800c0d9904416a00200c1e440340303581000c800c04aa51a04c51400ca000e0414110030300c0c090500b41010914000340401402c12034108104800204140b94990b20040d102c0e4000b07002d59402032044180200c03e59010748210076010005841c1c290940c2d03121000c000d180c0344203400880c1c008503403152422400747d0b00c0038250907140d0b018480c1c503d03600030504142190881c683c4070f00c08651109400b41c10a844e120204070324108000d001d1543c0310501e0005801a0081d8540300c3e0b041406001003109000600080600841400c03000b44207a5507924215400d81b141503440c400b842c0c000301c40c10000907004885804d42c00c2d0403103001451441e903c44010003280c2080c600300c0e402d58204001c1203205a80000c602d80d104404a40401000344140c8001c1e589 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 209599874 1250 209598624 209598637
    0xc0307030f1b060507032007140301060f0b09011b11010c030512041401050a0207170703020a170c0705090c12060619120f020306030a0b0a0929061005 66
    0x500da0045400401d101e242d81d0194030100e1001c4010540998a2000070241d5209540031b40000f446000b160840111241000c44001d80c488000d001040c1448034180098200154555041d1750b526000140e2152200211000b080202340b40390301c074241400050540e2011450040115401c00b0740d170000140300b2001f02c02c00c0300d03083c43d02c01c49c010300b286000c0e202440340d041e580d09242c10070410413042100c0404901c1c0030b82c04410091219450b240d00d03981c142c3c020018000c007040c40360f02020f001d41035034501602c2210f0092045a000003250b48803003480002c140110901a180003a80004902c01000410300502c400d58140803607143c500c5c200243c078001c0709680c6888030066000324485681c4c0700140d03004d440c1501e681d0301070950b450318042c1081c140c40c00807000701d50a002c1c45444805032442528030481018026028581d5144c0e503465026400419500302d4554452980021425840c004808415800d11442641c00c0d030384003516461600070002c520030103031200604041d9510105540c1d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 209601124 1250 209599874 209599883
    0xd09050a080c0a0e04080d09082a0a060b0402040504051f050a030201050f0702010e121f05040201050703080406020d11090319020a05041104030b09010c1e0801030b0606070b0403020d110c030703 85
    0x130070362140e1414580510a03000141c0302941000350810500c4244030003800d120600c00342e5215090903403403000c1010308176161000b01d40d411100000000c221300344c002d0789013003000500c0140342644410000701101c0003611491004601c1107400741102e16102440c03809003000702c800310348417032031607000034079900c141c0f0010080e40c1d03400308801e003c41e401020500708484005000c1c41c855030840d1f480c0741e610005070a444402141403415121282003d2080030b00598040e580e1034a044c1168500341c03211000603104894080d403c00440c2036a16861140d0108086a4021a0780d914400c504052034030540308a880021550004444010ba507140b8001d400c6a03410386000c51299801020b18006009580c400381030041c01e4010400500010b500029520406442d0002150300181e107a4074140030004110000c181ca001c0140f0129000c010070b01c1e84004022321081c90155550788503480f101c0240c50403005a4080528004515004450190480030a60080035034002c45000078dd9940303900d11001c1c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 209602374 1250 209601124 209601149
    0x3030304060b031e030a090504060b121b0708070b01080c090103060b04090203011a210d1b020409030e10050c070e090a051519020a1e0e030d09050a080c0a 68
    0x5082c0c60900201041e044112844600042000c504640f03e0344035244010000f07d580c100825646003078031401043e1042e43d240b907404c2540300c05411580b000c018003142c0821011400a03032401030300380000c182c010301c107062031f64451031545040d91601d441a0002c3c18180c00c51143d080c611b454000c00c190440ea0400008118070340b45201285c01880308807400703074155090041048891b80c1c0d808000c00500010b0745d4102054603504403c5007565010303d400c18071900000002d205840c4031703031041140034854a0f00c2d040e1000240d8001800c60720f44180490124404200424071407810540d0007020010a08109241800c40c0d0451500c8210070300030f000421a4007004283c0c1c40c0d0042218050741d41d4880c04540e0955041040146d90b207500311001100900070b43c100d0303c100c40981c021b9031042c0580e030b10395003001c0e12501303c1c16804100d858001c40810961002010042c0c1c0e003007010554070b01c140d85680b030209003031401344170400304a600301d0309070b0f68420740d130f40703041a02c4001e05c0104861400114a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 209603624 1250 209602374 209602391
    0xa03030c110d11070e0603061302040605060d090308060301060b0a12020d0501032006071505090f0607110115140d0303020f0a0801062c010f090305120a020f06060303030406 76
    0x9503040291180a070041c2d01c59451240600c03500a10b04462940c0001e08458045a07030f512103c000e40c00132641c613600364220314040340e075441d01654492461440140003044030342c0c90300b000c105660400702a801806440c0c030751100c01d05811484040e04285d056009002080c00d0101401c264030070b40c036883c0108610030311008580c80a5038152032410002140c141f00550b900d0030651503025407034000501400c2c409408444511340401191030305036101034a00248003054507082c4c01000c00510f4034100b40100d0048681885080c84414403500071500c0d002d40381c03080141c1190840e111120580d00385100c0c0c850500c21805640c80d400c0c8409001c036984108a2002c0c0340c120080c0c0900701031450b9044012528524a0303400c046414107030b5119a95148161070f50601414100c501c10b4582440402010071018855208400200c46000d681c10403007031890b81d0340e85117440d10050b002024808000428030504c0c45a05001418284034542c000f03002600b41a0002602c074400500010721559984800 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 209604874 1250 209603624 209603627
    0x40210030c050f070606050a0801022221030e0301240e240111030706022710050d02120109060806180c0d03140d0501030201081e0a090516030c030203070b0405030a03030c 75
    0x10050070018041180d010b84c9c91900070701035001805030340b03032013600e8001101c801d08a0a140c02e00f21400b101c0c10409a0b03134a500c0120703c2c0659500b0680821119960b4103d090301d0074003400041c40f450340304003150084128500e565204140d00910720a42181e0203028080c078109211010703510051a003030340700f81188001079461450703100354240c26020200b4801e007440308980c054800180c5140420f20350010038071203940d03d00052210a540000c0307080782d80020314400c5004e00390000300b00700014544001c0100348a48900700b68802c40b19140c071038009010a07181804210b402c04401c4403130309000701680d080b550310b031200d20f03c42900489114440303409040c07103041c00414030072080c040d29984990020014000d030609020680c040341c20300010807114501359a00b400d99186030084600c60362201420080505490041560036201701581c00e4041e080c84044100110300c03c40801c0400e52440c070600d030a03d0480e5201c2d0b11030400520040080fa1800301d41800c1066140c40c0004080a10200 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 209606124 1250 209604874 209604881
    0x150213050f1818250602010b04050108100e070504020408010e0106080319080601090b07060b010e1c0f0f0506090619020901080601051b010203070509130b030703290a0203040210030c050f0706 84
    0x844202c64484c002d41681c0e510244800401510420b0f0300a004409501c030901c030a40f4400e210741102e580c4082e17460810344440741e020051071009007041d140d9291b48c0310002016a08280c00860143e5552074004801c54400d20031840105480d4004e9800c010307614680303080100708a2140010f0000348000100183c0c401c2c1c1000003d411180d480c1d07500e4051a042c000010305000001902040b99035032142901c1c90068541118030800001e04480c103155a540c11009450400046601c00201c568400c00990300780a013a10418060004117000d14003213102e4a4061807005c2c1050210f8810030061040742d03070201c034035603201c082800c105980d03400c00400c00c44d44690b090807a803840e51003c020702c60500d520900420314407108882103240300c1800f504a8080317490103045254141e0041c14108001400c1391045010403c41e0318403041102185504100c501c60212807620b001503000080100310701d06600004841c0c0303603c1c1382c02c000c82c90b10100c020b040b5214400d8082003081e804100901040070640 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 209607374 1250 209606124 209606143
    0x13080615061602090a09030201050f090304060f0302160303091208090312130218011701051e04030207090e0303180c0a030201050306040e0f06010302042304020d150213050f1818 78
    0x8100340524681014605c0040c605c90508800650030100072804035119030b00c03014065900300d40910b20309450444140c4070343e802c505d801c4003415001d00404143c1a001030505c00100c4c041c2e2008510b01c031591621101c021003a640c1201488005800d2004240000094500010f045420200c2545400340d4540101044000c000e500070743d00e200b804840c000b0701b442d040c125110881c00b8205001c034042182c1c2610404c90706294003c6404210030100c00030140060b07045402401034074015a160603036882902d1465440801a42c400400e00c1851030f030906000c201540100c0190182c0404800000c6c4071071785910002e81008004404105540e40b527500960050b82518211100d950310003030a0741c3c507110f00f444180c0c0f00f0b178036051083c240ba0006044000c00e80c1c98804105d100e55465034204070285d22030950540360702c0d1119442c41d501d40640e100425a100b08210100b0002d890f10080080440001d50403078050b5115802d0340b01e0f01c502460030340b40c004040c4040c080320000c0c460349043c034002104 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 209608624 1250 209607374 209607379
    0x18030b0a0e12090105090f060c120301080d090302090622020c0705040b01020105061c26031605040b0702040e010219270b030103121103030c13080615061602 69
    0x4144038408500e94046020303003001c0d10564100d0b50982c0c2c110142030007911940c902081080001803043c3c58503914807294400020a030380e003006488501c141c0b420b403511110502c000d20000043c49013030010030402031111142d152500d070342030455020656000000d00b600d0700031000a002d410950764a1000d80b90180c0b0761004c115151300490038070a540d80001d11450303001d90b05d400c29170701142d48103000e01d45c03140e840600b40038403408501e0790381d4100d0b4441481c2903404030042001940e0028600c81c2c9640c0012070301410302d45a007482d07458100c9500d41545040b05000080108101c941c00c44810740d0038064045800140d1011503c032690301a210b0300c0d0241c0c802240415400384a26040b01c02a040c0c2481e8441000c90420703010f161b121540200e0003500001b5800344010000a40c02165418641e491071a15203648204003e101e841d5810584001401c0100420f05100e01d200e20410f100083c80403a0007805103003021a0307559100030404e00414022040001c03440c262000512400d008103034003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 209609874 1250 209608624 209608643
    0x10140c0c15090a050607120507031b0c0302030c01090323030702090708040308011e03080a020f0703080c0f0105151504030510140115080612120301031208070903030509011803 77
    0x891100352590049142d14400c03a00c0c4280424103040103001e07641070326841b1594150b00c481c584010703100303504010401c50400080480340580081024140c98040344541d80c00400c503800c5104040c104549041c00d141045295103082002c140b10088509080036198000582c0c00240c502c520700f1403103407000103500131911000b400b50a582c4584003600c140e002c3c0e59000d9640e622140c603940f5403d4034090505503144024018400b103481c0a000f000c00c00402c0c011500240c407015074590030718205920076120601c01056a041c01340040c04102d6421040341700820207403500382410300b00389002080090180c605c84034440f0601d00c0140c101c1d00a90740100442c0d212840b22204d103000352042628801803a4a0b50b000059201745e4902000b82c610503d84642c94544d94070000c0c41f84502c0e0302c040ca0311061040b000c0e040b4040d80341c48011750203140a107540040d11032a0f060043e003c40f501134900010007828003020001320f40e001041d61200a400d20b02600b12010703c032000307910a2425000074121039075 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 209611124 1250 209609874 209609899
    0x60509131b090e1506190303030f09060906062414090303070506010f030c05090613050c161119080a030804051c030902091f1710020a02070e0610140c0c 67
    0x8002520030200140840c41304c038203644007800e00c06280d469641c0b80404c10203524041c40002e00a07004150002c00c44580000c8561072900d4440944440b80c4090b18503913a10001489890800b11a0300342c030000003000c49a6000c07040c5402060707104040d80c031491581010510b841c19503014012690700e1504502250740650b1a0b50801c2c00e0407810748000c0f540e62040d040000740c5401c0580070203100b920b004000e01c00e5164401c41139000303000010490750349990100010000b00e06e401d0034501500b40500b007090241d0f82e004090101110307030350504103080c07810540c041003061000074101200c20b9045c64507141d5901c440c6001c9180c5803004600503250b50325101d01802c410380c0741c0d21040d00c680c000c0700c1070702b4251180c2015070100d030070005190743d00941e1000248000d02c0e03000301c40010000c410b4111642d403900200c0910480e0008014a40140c005120030015107841202c0d450b0800c4040b14551409120100c02410141034521506a198008a60520b1400080c001d40c115098050802800d000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 209612374 1250 209611124 209611151
    0x102040e01080d0c0b010b09030c1302090f0a080304050d0609061a041407050d1107050d0503060a0911030708072709061a0d020f0d0f0906060509131b09 67
    0x42090041d82d030103104420b0011400d91286051010150b0008011001a401c01705c402600b82e0103d41115014421b400302c0002d1612101c400000310b5001150060304c070a021800c0051a50381d0300481480340e4008074003440000804001c40c1c04940c4201d551310380780000751802d41c01400512801410052034103404840280390170300c1484102c14115010403c01421500c0314035034000551b0070100161090220030600c0c0407030341c418440120a0030300d0b641014021303a84c5501d02041c5442d034800090340030042c0106070419807226405021520414007844a140010403400d00005040e94100300c401c01c08075243c14015402d0030448200308058508a43ca014100044582d0a210380180580303050000079218600000c2d115400c459206854505200c1e020200c0c0a50801840c072026240100103088145841e8421010100c038013410100c0c524505007031000454460b41e01c080c1c0110121403c100001800003031504195a1081e1184003031080341005410000013500041d400c24501250900680e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 209613624 1250 209612374 209612399
    0x12010212061203032a1e040603150b070303090c0e040f14011103040204200c0109051c120c020712060203010e06010906090b0d090210030510230108060d05010204 71
    0x160700c1a1415400381e252549410b9903440111102c140c003c0041030b9011036012800c0c1d04800c103c184011440c2460704906815214840904a0064800001804006164141c064040c170020f03922010081e00c1e00e021103204251003840070081c10036aa4588042c10070450103d82000b501c03280401c0360f12847d09107841000c008920a041d50303c07011500200c41c00d90310500950804038290340d18603040d03880e1907003481b001c3d202201e0b80040116581d1035000400010102400404005000205038140d2505105080c1110000c4090426800d00700e019003440c1c00c40d241140100406500051402414030f00b00c0c1004829042030004960182240040c0107094020b0350680e48040c14104641d100c007001943d5140040c81154042441c11034100040400413000d068040720b100d20200c1c611a150340004d40020b040984400800d580b581031150709601202d105014019140c0341c001000300c103174401d01815001e0050681005864170025800c0c3d10341c851038842c465031040003507403a40c5e141c5a40d01403a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 209614874 1250 209613624 209613631
    0x306031e0b09060705041208070614010e0c03100b0a020f010f0204050a050901050102120c0106150309060c0305040c09021c180308070212040e0903090307060305010f080f0c01030b12010212 83
    0x20400c41c4081a00da0401049040c01412240c03125450103140484a140030300301c501050380c0c106001c1c4800000300d1418002c03100074900a90400074550704000c014102c03440003920a111829007841000032144c0800004416100141da401d134035030b80d10a00481c605039688540d00c2155081c4403503514105003d40240054501c1100c116070075a0725a002c0c4291078009102d9240140c2c00311900c2210b5800400041c4100c02c1e02d00c001090350754035051007041c0742c0c111135403041c0042d5a0794040d8003804030b14468110080d032185030500103401c05031a01620880341340a8003044603070018441a40803954204070602c3d0900030400e1116035201441c12080c6031403d4400e501040010300000c10503407001c80c40c58020880c0701e0780141803a04007a0000b6a20340001c2c04050140700401c92458507a0b130030010700004000a0b0b4000c2003941c1084920810041c143d44840c5141d404505c2c0c41d82603100100d101c00e821842840c0000d80d41c0c020000085800882d00e104210b654400690401c1c03600c07100680910 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 209616124 1250 209614874 209614883
    0x30d0b040504050705040b120607120c0e150c01060806090f01060e0c03190603020913030207120503030f0702250608060108040b040b06040e070f0e07140a0e010306031e 74
    0x225554210a02007540c07021a001480b43d00302c0038041c8464981035001000600d4050701c415403c0701030802613850003509032080804101100c8507510100d61500415901000910300703641601603c0000c01d07a2100e011189084520001c500c54444890940c0540700619066040394810304001d4542610380c2c14109804c0c110754241200400c0100024060743c0c09440301812252456880703554040d101d5003c602030991854490740c002000da51480103060044c41600a80c4002c008075140c0640740c480d184c2d0140020134801d42e2180d02040003c010307242c5c880b1003000d03803074840d07036501030101d05004c0000d00f00802c0626101011040720305d14400300d01070350b455403a035030007588401d4010349190004440050800000311300140024014802d104d42001d070240c4003103500806d81a0721814486136421812540a030b4180410886401c2905940c20101c5410205004400c10100c040ca520400c0d4805050264130305440c003841c1d21a0380b00b00000e64024610255121002d215002c1d40c1189003400d0380c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 209617374 1250 209616124 209616131
    0x110a08070219080a1401020d230105040506011d04090c030b01060201140c070609030903020901090b010206160f1d090f0a0f110301260a030e03060f0103021804081b030d 74
    0x36002061040c102c040e183c900006000e0070407156610044118844464030a41d50284a120754400d0076000d61305001088000d41c00000352032100132070f038100059020b1413046081009101059030400032080d025852031030003242540165001c1000742c00c82040082820100000000c18004d06182240c140d800690003440804084000c5000d40b020507140c07603e06950410944001841e95404001c0c09442410710b00b4941d40e40360009010208240d018044668454051242d9580d047c44250b43c00030500c2d4664103a01d610580080c1014040c513600702c1880304100342460b000b15001c00d03410118200802404440c81d1400d41031381400c500752500301a190400000c4442d0307a41d24020024202204280d80c5e0840e0310340000520489110f0410321545403944200740c01d10141882103220a82c003036120800301d90b1031201818030703101d0024070b40f00f40100c00500520060b524420360031203036040c64010300429101c5003040407062240f6501c0340441c0140c090350b950071541c040003624150034901800c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 209618624 1250 209617374 209617399
    0x110a02151b0d0e04022107020708070501080c03181c050d060605070210050d060f0807080606120619180605090d020109031205090a0503030106050909100321110a080702 74
    0x4aa0b00c0803003080d5100800c4034080c0742c8000341441e5014016000408140d442c84c0703486c403080c41e00324a00540f40403005811081060042c024100b000d00000c1c9800c1ca0300e604145441c02c00d20455001c05014180100145283c1d414004000c000c140441351012032980788a480501000c1e0a40c2e108c0c00380840903d040a000054150085099922040c1c000d0003101c404580308101319800d61100000c0d18146655403408146008694803100103841c00300c004100d0a820241070514018004180d40d2064050780040d010b410404101c3e145c1144107003014007800762030140c2c400c2c080c00501c00e0754409a401c2c82c0c0710f001440001d41107103001d00849000d9481720b2190907000c900340d40c4400b00140100c1e1800c02100b0850410358401c6601400410503201c5030b1707031907a8800b07040d94000c6c0d209400040e40441e89000d1440c0070303c54150004441021500028596600c0ba400c000c415088510042150011441503078090700486005004180596680c4082c1e403078200019003041d1800d9000d0765203807404 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 209619874 1250 209618624 209618677
    0x150f03070302190903030503040213150e040501110c03120702010917090a080f0a02090402030703060908030910020a0e0d030c0203010203240406061e0309060c0f0314060907110a0215 80
    0x544c0a50307805a41d801e18542d120340a04c03680c000c1c01100e0b803141a0751688855403108004000502910041d0708103070b0710781040d0828609407807100701d9030022540200710842012100104039107038a03403900e282c000b541da18810183d0040400d00e00140001d0a0581102d011004c1040108041241252105041611122566074401d5104d000000c03a5001c0300003180589022901d01e82e10610040446000c607859580d10001e0303456004080780c2e084408814040166004d115007010080707455021820302d1031400d40103100c0c200b000305103801030827265610f100740740c0700300c1194074503c0c1c01400956407410188407840180110401c0c03c050442c012542982900c3d0901603442159507640c6c2e4650030800800c088040ca41800820394107056440351001c0018000740201217411721592500010303042c0510010341641d000070349038010010802c040040d582e0b40d20380c43c280c00140700c0c0b500a200e102403440607131500103c50000ba50062803075902c0d0702d880f8180c5005108540001c5000d1004843d0041e4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 209621124 1250 209619874 209619887
    0x15080403091202041107060506030607020a0317070324091a09011502030c0124050301020712180807030506070e06030903030a180615060212040b0306150f0307030219 73
    0x80040014511203001c00070080050124000e03180000e000054440c4050712110740341e800440101d802a45403070401c8803503d002d00c44a42d0140a0703002070a00b03048150340003402032085450302d80081b4070381d0340032583d0075100342d0101120054812400240420707005c40545401c171b25201e41c005403828031a510300200c0d4900091460068054800c10560342041044081046e425000100b1440700344007946240009018041c2290440106e8114242310303050001e00ba0302c42c907002a03020340c0c010010480050751700c15002e001402103140441540194016610794504c09510264003403003035110100a1040c0880e9484c040c00b45600da0709089100a03050006078041114001010740044c0000b8a030543c05400c42c1101251540103080d500d01103940c1c600c00c50b503200360194010f45082005000c619010054001c68010b84c523469403c0910f006000140e51000800490082c50b101000c6040100d220b81510104e045080c0480d0312403400f8003001700250064051910b0000604030910001070080d40c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 209622374 1250 209621124 209621131
    0x6030219080c2409280302090c070f030f05041a0c06060414010e060a03080708031605160201050c030403050102270105040b030f10051f021c080402010f091a041508 72
    0x11001d203428404a0754040c440d080450783c4c40d0000d46940101100301010401ea490151320750402c0312143c0d00b540140110210b0003050142c2c41e00c81003081c40040b9502c480c0c2e04805036411315150303104070b401c041b040301d990140d9031200e004da0b6075118806030801490710190080c5a40c0e0411640e4a558030000c11050302c99040510300c001001d0401031050550f030356001d5921900c050410b40c0c00796a01e030354404140c1d00506041d00d41c0400481802070510044282150340161842c02c00d041240c5160310301a00c1c1c01c0003c0003814030400082c490250b002c03d00586004580110007191110001407000c8244010490301100c16401080190300f258002c105481c00d445082e45400c0c25555245450080984080c0c0401201c030f14641d40020142c0d101e411459a4483d0b011011388144000b12019140582402a0f2402010395186a0303550307652149100c0d07449602444d00e4101e190440d1350a0b90244401d40000c846040d40484040311100c0c860028401c941f12000140484881d1543c200c4644005a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 209623624 1250 209622374 209622409
    0x6170a030809031207181505031e01030b0606071707030305090d1404050d0f12030209040e0105061e011e0c0b070e0306060f15070606090b150a03090606030219080c 72
    0x20000701d08174910404906a41034080303107145e42c02580726404640c070066007854100001c1c03c0001044918590701604903024071100307204450550444d80c0d03407104444020b01e0701c1c0c05010003103980424004101204280320350b0f038803c0990380d0035050600034060302d001c803014601d81c4158140d0300740700ca20030780386294003a06001040d4140741c104030411054004510050b58a050b100b245000801c0707880f03408074811481903d00680d80c072040380500007982c44140712903400e81d150504101e20354032490507007410419805140c2c034501e1100001609c4814020508600080d2a44498a01150003400c000f40590041154070343e586c3d920541221460919080d4031740607004540440c04a040a001a94020400905070442e12100300d00742040d40d041402d00380c0e03410b900c4840c01c00108403d44900c21140703509440c0d2000540d0300311409101c80c0700e407407461402c143c1e9998032a01402b60399800a0041e40d8000c0001c80b1115071141c0664406506001e04a40340c014540101014039001c0e14462005481 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 209624874 1250 209623624 209623657
    0x702092a0a050a030506010c0822090213090525020a06150302011b0201200604020a0f0b12100504020406050702010f0206160c080c07080a1b03111306170a03080903 72
    0xa1250813000b901003c1c101605114a00c1d0f01c001c001024207029040001d496003907a5561442c04410b0000c18005a100c1c1c0420f510411016402c00040100364050302c01900c4c0124075a01d07001030a03c0c1d0286c1d480082c8010140c1000d009030016804910001070501454040c003c2200480350348604042c03911009010a0b2419810102d0140301c2d80c602c1e42541c01410501b4424100100c100301c03044030115500403940045042100710701d042803400002d404508d641411803820402c0c41140c0344245c03002c41c030701d00d0108400916907120a0044a018000107013080d92200c0e07880034094440d40007640c0480c0032074001c52009151904c001050361180c0c0b2a16030385100141101019038144a01e0301064070448002c12079040c0212082245100800124000345814081405c00030001504000b225000c00308001007000816000b20041007044811078843c0d00b009500400300d00107001a501101c0301400c07004072400c17500700108130b00564900a0701c49800c00d42d1208c030550f40b40d22982086401c60b401 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 209626124 1250 209624874 209624887
    0x2070506030c121b2a0304030b130602070503120601031a010806040b0609040c051308010b090a0b01050d0f02130807150507031701090906060b0a120c03020702092a0a05 74
    0x10350f11540307810100e2448241032a88905510389003540c004010043d0892031580720304540380a41c5042051038851102560429065030b031000685003001d48044085403901100c0703014049540d0444424540c0003003143e50307a10f03a0900380e106004084518901107460180d101021404000e4420500c00e016941c28449503141c00030071004203164540543c1101003440300342a00c2c1c13594450710503241201c1d1200c40d2184c0c0e02d0988040f028a01d6041418203074100b162445084c6c94000d041608200031400204c5d4440e06040129030600410f004154024181607155051481c95401841d00d030700e5001c0032170711060b298003140c0c3d59140c1e58440c00d902504603100b400116480341c070140102070f2003850700101ca81810f13508003d00450a810400c19a695102c9503401c0101e60b1082074010a40e00d040c2c6420083e440c440a000e01003464100c0c3e48080e1901105003e07640700f5070403106400d60040c8102c0c001d08100440824110302030780111840d001c4000b080c1c8009903910195603050010390303101c42c40d01c3c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 209627374 1250 209626124 209626147
    0x90b1804170706180203190c051c0501180c06180504150807031a0a050702031b0c0301020705070801051b0f0711060a020303070f0e0d1e08120702070506030c 69
    0x300000610525007414072814000540038000d40c0b10140e03e404c42120303102c42c107004250406840b017021140d483e140a54800c0090b00c1c80c2058000c4038001c40e00101172285421302249051b0a82200810325440c1115038044d210f0064003c1c1485070003150f454002d10340300d18003540d03032101c141000c040040f540d01040001d8035003500f1840020841c0261602020303130b01d10031107141c03e00c19002121260f01c515122550420110740729035000354902c400707112600300b1040182d101c2c4503030103c000d03065949103d0380c001d43c1c40401c03490260701c2010b4021580c0d00240d003815520792100d406504c009502b001c02280c14044001d01040400e01c80f510080d1422203811030703894031175201107012250102c500402c4105962402d01504640030b45401460b9240342241004203000c020100450501c102c1c20018413044d20740400c68804541e1080f40d0b074811700345406440740c54072600f500003041004005114052185411601c5000740055000c0b10700c20740e200d4080260600013220041c0c5804d80074403402d00c504 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 209628624 1250 209627374 209627393
    0xd050d020f0c0a03120e060c09040c0c021c0c08030901050f0d060803030103030903050d0206071d01030b03070807181a01030c26100b1804051e01090501090b1804 71
    0x88000744086071901c14801c04190410f030301098283d000c01c3d00300443e40d41105650042c0c40e18901102c02030461840c040300840c0490051441e800d010f60307583d850403003089001d0b01c4801c01554004040119409030064455401941c41c80702300c41a1194040029221600000f42c522164050f1600e40c2020045007101d84250411062107100e1a190200081d00030014401140a907019079030300b00d25141142801c0d860300710a541601c045500074001c21655a500c8883c6454a0031102d1400f0780341a4460300403009001c89003055a03040c0252100018039000c00101d20049030042c2188140581e182040309003140c105148081d084100045100c6e0b80e0342c46940840230307412040c2003642c5480d44102c150304000c0d0b080400f011400b00848144400107400000400003400c6401c103003407a1a1000c500d07041c090713807a00c80c5180100e4a84020030308950490112520000039181d43d5401ca40c2c0d54002000a070400303224000420340f404070440c035142001d2401e00c200b003032059000b0340a5151580e400d0040c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 209629874 1250 209628624 209628637
    0x40e07140d0602040915050105030f01091503020301021602040506030a080706021c0f091106130308070501140a06030b1312120605030a0803220b0f09031309090c05030d050d02 77
    0x1007044803034094001107092001e007002e002000400030b0300101240002c009868150010b81c107002080c01000090b03807061610506560744120302051004000800d5150b002c4140c1000790305500100ea00403040004059048459001303c80621403900c3c2d2005058642c150302c0809071640c881040b018020510540041c414a00b0300700e500605507244810302c85c1115110303105140580c0e1108444000c5c0400540380c1002c8090440c3c105d0324110901503040c06019451100400c040408103021050000c07c1d40940d52200743c2404407016132a003051060020142404200c031100202400701ea00c004402d0550390f02650300c8240d00103284614002038907452030510071107010310703140c500128a689050140d195054400e9040b0394070381c00c00c0c442c003d803440700c0600d0316a6041c20100003c80032030040640700f6000020742d0701c10590394444c03008840c107512910718000b041d072003401c00c00156070045038020300486000700c04a403682c0c1d40b034004250b212032000221074005582481315052000955004050303 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 209631124 1250 209629874 209629879
    0x120305070302030403060507080f0f0105030714030a080313050d0318022e0f0207080a050c0108090304122f030c01030c0903050a030f0f0504050102060f041505160e040e0714 76
    0x11300c0c0e0780e40d13105000d680c1e0854040000031440024801080344001503280c204c04403c002c04ca040d07040901090396681c0c103114a801644200000719500e450911541c0340032500102d100d5036a2802c81403038043d52111500807126481840c26a0b14010702c42d20400d42002c10800316101c00703032480c0d000c100e0758402c5415001c01130072500200c0400b111038131080140388000d684441030385d81180c1d00c001e4104030241d402400c550300860301a00001d400440e4204040809082c08083c83e01c070300600e203246009a030041c0e613071010204100414440b49e5005d1400d1445450300021300728410f80c01c480748481c0e10850003900b40e40030030043e00c200d41c042d070001841e0022502d4017070720165070394507002d15015008200307401065406041241c03156119068414800403803c3c918a0a4a0400000e5442c240104044050300c0c0c2000480e00300070b41d480d200d51100e000c400d014840c40c241258145100086100303044082200c0001402135030520740203180f5042c0c0000c020300100392601900c07140b4103224219565 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 209632374 1250 209631124 209631127
    0x3060918011b021e120a05211510030c12051305060a0f0501060207080703060203070e0d150b0d0203120c011b030902010e0d150c030609090501140109020412030507030203 75
    0x40010200001061010186078001c1c00c8601c1168401c40004002503140c00b4260089102c81e14404a03540032036210100914103240c0d610b981004803510a01d240308010f0300723000c20b041032001242c415809803180550880e088007a03842d03221415070803120b911319100e000c180705c3c0c0255116502c0716071000d0341c080b03186170070300c2c50750103540e641d0b5400c04e0800c81d140a030040e0b554820400403420340c0b282c18090904d500013400030300e040c000f1450350341c0c1003444000e000c0b640003c00180369a109051268101c43c015040038529402443d1201d00d000702d210140c0c41180c500300b14000340e032500120048800da0003901914802d400d0001e003142c035034424001e4030b4440d900c0300340403010b03680104501403030304100303940001d242c0e40f00344001862032600d41c50483c428194808407102145840c1c6078900003090204000503003841041090b005410180c1c0400089450000c010301408010342001e040d2082e180303000c41e17182e0b1302d03040c41608a008501698160039614000c6000003401440100181e40c068012603 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 209633624 1250 209632374 209632391
    0x3031d0303070f0506010e1501200c0418061404020d08030601090308030a05190203010f092004240309020f0d1a0901060e010803160210170a09030e0a060f0c0201090815100b0306091801 81
    0x330141e0f404e000790b010506400820303500910803507200720300c241026030001d0350b6107040c1030300020358440030004054610400003000c21b10350f07030064020000035a030007400c0c1c5840785403100c400802000200c80400171036030903140d13002980d100c0d07108681c1a2412098444c0c129401e000703034140184601d46e821012032889618114000c408070016000500460007032a1151116a07144c170300c500c00c030070301030402d060914849800582c0c5240d00d45082402c192180344986030f079424201c1400d030317000c007029410b54a0030040c885c110700d06400003000c0c0da06010b00300305140d0782c80702c8191362440b6903002042c268200e0200c40780181f51200a80c50050036030300e8041e51152081d000d464025900752030840c40341e40e80b84c07030000405400141400390403104507000705400740380a07405000c1907070300fa52200030800d10000b840c2c00c40e8042c4032054081c00b480d004440044404401490b1542d10031b03588018a20042c400000300403080078112842044003401044081d101c00d03032504103814074014040d010f5500c80514 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 209634874 1250 209633624 209633629
    0xf0201021309060314010501030c09090503071a16090806011a07080c0a0606060e0a06030b030a05100504020913110d03050c01050708010302041503031d0303070f0506010e1501200c 79
    0x6018010b482c0703001945078071310b01c0c05180c1001d0740c058401281e4142001000400d074400752540c01c840c002d64012840300d080d071500600354410781e04001c2c507411603030b0040100000d403d841c1d40d114113100c142c1504c0204200c6026118082140305000c2d0075400400180300c0200990805029041114070a03410800c0594800c4150703085041118102d600c644101c2d014481c240c0a10002441c0504103041140700700c0010a14680790783c02650141501c417020400f02d601c04100054841ea0000103981542c079a516194010700016078080e84a9003031100451001c1029103107106050341e00010070b24084452500b4810340c200409402d4040c010103107c0c005010034207002e940d01c183c1895544e000250305610420007214070f0500107011001800c0010320000e5041041140340e002c0e054404000d4142c0f00001038610303c02d07410020013040d456281101001000902c6a06031094000060429a112803004e80c4010082ca011800940144103141203103038160790f1115040700200942e01104d4041c0302 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 209636124 1250 209634874 209634907
    0x16020a05120f07060c111002030919030c05030102130e09190b0604060603110d02030a061a04180b0d03080415060f1a0c07030212010b0a09091e080a0f020102 69
    0x10203010364120306200c941d0030900f404508044c00e003e04180358505099150b0141840c90420b04a000703003841220700503800c0c020400e803600d03020002c1c003030340e034010354100b01c03086401d058401152882c0c070094002c2454031301802641d00309011710321030110207032900801d8000100301030b05100d00742c000d1820250303c0d00e1420340f07407001c1c0501030f104030003071800c00100b44002c440043c0d002500309403520791400c40780618001114252078000c4005604d136180c00000b40020a11076104ad050006403c1450042c0100d5801400c125220401c001240c107124821b0403040e609015211544890121038490010f03004490b8140c01501919080401c454404600000c840071030704014410444803004020041c1e142c000014180c40d41402c1d20b042514802c0c03415078500d15804000d00c102c040700e4000401d90350952100410250040002c440c0543d908110401000304603411703250743d107941c221064a0341001e5444041250300040140c5465103001c0211030080d00400d00404554081190400b0510002c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 209637374 1250 209636124 209636149
    0x1416020301050c040e10030c140a090207050d08011a09101209050105060a080f060601030507020313120201121406010806010c02090f07090f0b030106141911060703060b16020a05 78
    0x4000703560b11341c01c0002c00954100c000b4428110006001410320004042d1600001151000c4c11400b20b98004180010b2901e0350b02c0d0000707040c085c0b0101e00d000500800203880c00341c008058842c0c010070390300d407040514907100d200e0b625a009030040000950908201c001214006020300d482d554111070400b0079070036100721490607034050b0b442d9400e00460b071a02142c500014501131005101080484a8007500c41d000140a203052607607420000c0d03080790091080328000e150b0180178003512500e8140f4140c40500440c001c1c0c0c00500005507074038285800f4490185282200700c2d0750703a0b250f5290801182c2c1c1c0003000781807078100490520716a00684130300712460f0240356006901c0d0007500d840c0c403004081d80c55540c41340c404403400540410400ea410000c9034191101d0740350007800504205022619440354070051005081c440c010411443c0e80310364030000c1340f5805019103801781c440c0041201600d405010b00500458101f00494005801580c86903400744060018140c6940c1d85001914030000074 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 209638624 1250 209637374 209637391
    0x3050708070b040b0606121f1203020d020c060c060a270303060e0709060c03050706021306020a0507090e0c09090a0807050f071e03080a030f050a02091f141602030105 73
    0x5010411030f6113049268084010f84525040001910500c0d10b42a005055160803941903000707007402442070790044011301008543e100300c00c0c0310b0303160095903407039004045030042c055100903072880e20b042000c40e0b070150001001004a9250035400070020103a41c0c6000c0e000000340460003040b040c2024013001c4140c0a524001203061510300541d4800000403c101c04210410b001404000c0c0c11202092942e601441e08944079082e03850a070009101c0c28074030504c960310540d400107600ea800151049820301c00d1058034000da0f030b2408440140d502c0f41e01261a03a40124204000c141010103001c1c1e4481c4050084501c0c01e0810740300c0201942c4120010358007a0040049201400310030000c031070003045505003454131800c0010350b4802d001094000205020320004112400f540300742c108000c505100c140812081c02d0103d4003500079400003c0d0030f801204405c42d92034020380182d416922000702521241e2002000b2070440a0b9507001c8011311210307541c200007103400358070244602445103488 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 209639874 1250 209638624 209638643
    0x10e0f0709060e161b02061215030a0503030c07030e12011d0c010c06050a090c1413021206150c0a0b0109050f04030e130e1c0305090a11010c0305070807 67
    0x1401d0011003a6407564208420141403602030001520581000e1603202c0b445151103101a5007900c081045001e05130400ba5100c80b000c00c1d280d49200007603540074011411051403005000030b040502d0349503420204080c1c6190410300002d0407000d0110001c0640b03510034a170001403c204100003c4a801c90704600030341c140e551f102e030402c00980d0300040040138000c01001702512000040001c260380e83c291401009540c403040410b60744143c603041141c445d90f105000b11003480e10343d51001d066501000b0b00034841e500c261000c040c9081c0e01e100705c40e100040389042c458155912400c1c0614041d006100d440d0040d0204801c040b01d41007407210700038461041591003660752402903031409941c0d01404003184100c0090911001a0708426010603040c0305941852100002c1e020120081007000601f0303105000d21110b81062112034070076103080c030fa05500d04000301c0d02c441d0180d650b40e40e6400c000078184103c085500c582580102201c0059a219180041c58040140c2e100700f419000f40608441c120f48 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 209641124 1250 209639874 209639879
    0x117010606210c0e060309060a050709030b06121e010c030c030b06090906040b030a2d08040612020904020705030c060a0203060112050a06081204030b06060a091403010e0f07 76
    0x42802a90000d007182d00e4800006101c1c0c142010700034208000400c0000d6075852088561806920380083c4500000d2146840385002000759466500854910050070300c4c01001404190084c11183c05032500003544460542d0b8400920518080b240680101d80c81442080405840707000c0f000c0028140000c00440c0d047d918601c060203035909601107200303150820024140b0780c0c46810a680c0040c100f1155440f413901e68102240007080da0200d21500360107100310074401d20424001c2c00c6480c01c4d03000f424850b802d0020850114070020804005d100440802040142e18819440b4081c07072460038a005241081e2500041d00301d130f200c6201101c0f03d400200d00320b61303244024800701d6801058442d06500e14604040000e01251031401c24911299480000c1a4582180e0340650094201441240e000c120841042c41701600188400c032440d80c1e55034009203c40c14204251038007606151100744d19182006655402422000740c100d42640d03030352548410b1407404110080030307045508003900728a170 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 209642374 1250 209641124 209641169
    0x903041a0c0607020a1109220204110d0b0a15050307140c07030f0b07170c07051c0e120d0804020607021c23030f07060b030a061401051309030e01110708030301 70
    0x55014055104011800c100000c0c040f0744209101d230005650681c2c480315880f440000c0c001c3c514182c1a46038030700040b844045600d180e07070241d40780d4030040b28078441459032a0603844078170080d14002c1000840502c04107401d18010300c2546078040c40c1e044640c9c01c0150340c0f14202e2034210709a009880f20740040c603c941c1841014802c4a40150744c03840e00030100600e8890008440802404490b042c0c1400282001400f009201c1d109070810f944085c1c500001511100910010b40002150311600004032200c40004000880041015150701d032030b95160f0310b5400f001881c0c0c20190050340c0014501495408802d0105d003c00c4000c1d1242048401911030241f40c447d02e40108440520fa50780104a0740820100200a48040d40d41c02000800ca070030304500801c0c101400001c0090049041c6030a0422950012111605940d42a0750080165421588a00940707018000c041d0100b80318001440c0d031075118030079440c00c0c0070a81044071442c95a0b444000c0c5598800da200d00e2221081d07132013141640c3d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 209643624 1250 209642374 209642393
    0x715060303120e060105010e01030603060e0706020c030a150f02070206030703050f071706090406061205010605032e0e01020f070506090c0f0105031603061203050a0311030903041a0c0607020a 84
    0x2248010010440e110f0b0f60442140e03200418000c0e075050042302c40034000780c0c0c1c0c403d401c00d0003c1c41c3d002ca42071201ca1210b580c070303903514201405800094015001340c0c070301c1410005141c1080c3c9270010f195640e002106001000100500ca03d0400c1a0380c00b0401a409600d0b130400550240f0032698000401c0e01d0007012100015601514010070420a0100d02e003880c0080b507a1715800180480d4100300316161442e0010061a00350712140f8615072015009080c0700301036010f1340856070280c0c1038407000ca4882c047c40e00d0391094643c0071140d003d075110369031000012a5101d08100103005c80018500382c201c40452000b80c01003402164280d11240c200507510901780304641440e80c00f602c0060f0603101190000c3c00c2400010f06800c040254822403c400e00c2c8240c05c21002031281d040c0d4800c00d10494200108680c1c003481c280008030b420039009902010301c0d00102da00c29044100511f0806e401d0000280345a0302c4c81021030704114081c4001c0440000901c001d034010105a0000c3c29441650300d440c0909 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 209644874 1250 209643624 209643647
    0x9090b04321008030f0d091703040b010b1c0c0e03060109020c010e030a0503070f090e010902071a0408090607060f0e01020403140109020a0603090510091203270b0c0715060303 77
    0x7041c96211040101c1e001c00400d603480341082c5c0c03a80c1c1d9250298005102d00812034110301500d1812107007804a08003041c04011400795001c0c00440310a6a01d07030411171214401c01a85511840c510311000003040001c0d0700808004280389407040e48011420f002030703d024401c0e003140c0348042d800100c6004c5c5800902c0340308000b0364494091410554000300213055400020030381818070450003c0e000855120b15030b04c401a003503a0000c680c803540c580300044000d40012400710b416401102108a084100f200f603103100e0b07684010140d1070064102d06200664101e05000c69080b1380711480e07010307901520300076101c0131588c000006031034620f14104100300ea520701d81c0c80340c03840c0d00d00781079440561104e0b0300c40415611325040c0070444040030b117055494481c0e85000d0b800c02c2071030036145400300442801302c03061000980c0e42c02c0c1701e07000c400c201141020459280340e00000b2a12071540001498180701c0541c8410544c03622801e0403550780341d0002800c40008000a16640da800500401d6000012802e8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 209646124 1250 209644874 209644891
    0x110c0d08060d08031009020a05031e09120f1c0f06273612020708070e0702030415030e1011031305010213030515070c0309090b0432 58
    0x85a041107004145500810075000e441076000000040d000e160308a031500007441624000c40d034031220b925005003160010350380c5144810304494a030240c0388003251418029602e00e009010407030080d80c04d600c0154868509055115030502c08080b0310001078003600000d40e4a2000450110f01814407102112801d410240c11040040001c1c6611100e0700a03050b28034824041c0010030022405a4400300e2a845815208000c1240419144140001c00c1441428456024510b0184012030203a0b1150030600075002d45900c0400100300100010600c250000610700680b460592104000000d0b1030355280001c0100380c8500009026400030040c0300c120030a8001c08200038581400c0070741c0c0a02c0040d119140080e02404003c00b401800c0d411594040c1102045400b0780c1d40d24035005032500c281103015040442c1c808001981140159081420258503541d5011f030380703040102c0040206134082009400c642e960411000c1c0701d460703c04030900c0741a550b8943c0088001d00817900d1400314010001d00c2d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 209647374 1250 209646124 209646137
    0x1107120b090d12240909020f010f02120706091704150e010f030f060e15010320041502070b0a1d031203071d0306010f06021e19030201090501110c0d 65
    0x842c1c2680a103603946805542100800d00c680c50b83e1002c3d0500a02410316030183d204400002a1030b05c01b5400030701124825201c29a2542d150001940c101001d0a1078a02581080b4015844996003800410b8040e00c9010b001038030014580310b05030a00c02c003c81c3c150610000250501910810b603032600743c0c0203824540410f034640c0d240c000a01c03502c55086030b0428561504807485e0700c141c2c145c00640c090300041da505212480c2440c10104901c00c100c40b82804203103044040c2c17040317007000303030041402040f040e080c180b425181c0f1050680c0c80310710081035021070007100c2d808543c4194120041000342c000b13030b40c2c05920012030400603002d0b140042c0510301c40c2c1e109840a1495440d2202542e81c0415141401001e407020318100a82c00d60340540d619500d40115000072425000c03682074501038442d1342e421070f0b20501d0801e0b42004c140041407900c0201e0b60069501c0c1a080303a031268905040b504c0792002188585040c2e9900c4e0030745071500000e60135460046024030180d8010000d40000085d11314180c0b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 209648624 1250 209647374 209647393
    0xf010f0b0901030e101a01120504020d0b07020a05120702100e09040809040b0406091b050304050703020f01121406010806010201091a040602070b0103151a030c0405071107120b09 78
    0xd03168840d004040c1c0c1410380340c4580380000141400114001d00d04a2030900007000c600d0182546041820400da0100700076100d00e40044030507101712485117901825512030700c03440f07481b20400204010310681c114441d030000c0e50b000075018003426182240302d0142c1341d00c44030184100103103200c0c0000c88004000e03807083c1408080d90b5581003250002d4110485941d01c13282500402c01070809c02c0b200c284c11604150001444d14100c0d40200400b180f14040c096100000080c100c50038442558050400ea00400090025141480c10150b40e01c0b0b0506040196401c0620401d066070700441e003a0102e051014100304065810062059010600b44020400a0b9043d42e95110444118442c00030341c2e0900b90001d001c10030f26604480406070483c004640320741c0d591034281c4590f800f28044401217414618407000109005050841001c40200980002c82d110801d2100522005205c60100840a001c00c88000f00030b11246000d001690079401400e10f0905102d100c000c0c0181a084c0c0552001114 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 209649874 1250 209648624 209648639
    0x18050609011e270e07050a0212030a020909010b07030306080f07030f020d0602070507060207120b04020105071104020a1214070e10051213030216030b0105061c0203040b0f010f 77
    0x201c00180441c0304070122030b5203540003c031a01146010701d8160800b0102d40010110540b2410800f1102802011512561102800c84040c0074002a03c40564080150801624140005554090400b00006003001850400103070107000a910901d5000d400240c0c501c03c3c141e03d03016190150646034003c1c089050107041e40da0741c1d82c2c043e2002618a0009030b1400c0d08541d11843c40d4900581c000700259220062810480c0c0c503416507101e07500c003611914100052061b038860458180f81c3e0460303007146140e6100d07001950b840e80460421150034966944c5545259a00c2c0702806088541341e8501c1c00c41031a20154004494821095a602d0102c440130050003503485070100030350707801c1994110400c2c8814501552180110410003807000070107010811141c000c909101c8041d8003a50880d500003800c207000c4c2480030058040a406118804014001c80c00c0810003000048542d42260307070960107005054049070005c2c0c50407074022460006003c030390340041440c1400740850406240503039151150 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 209651124 1250 209649874 209649887
    0x10c020a030504151e02030309070f030f0b0a0b040603050606010e04020405030a020d03020f0304081b1002061807050904060f0e07150e120105090f01150515090613061805060901 78
    0x144511140c106a03400340b610f1040300840d0385c04c0022400020007049520000e5101d42049540c5215446084c0001174540c0e80140201c048a42000e61105282c0c05034a1f0305580b428000c0c007030300b1010b0319040d0081031520740c0e02c5000c00031170143c0702502d000d0070204c000500c8110000001489680188000d00090340c001c03546111065040756500f43c481c1052400782c1c20480f00d02101c07880c030b01000c540007800000108076044a012a03210142d400302401c42000f41ca0f8070030040003401641701900261400400d40054200c2049003000c40e2501a40c80c0d000036a12581160300711805600e940040c0300f9489640a02c0c42810155806411100e0500c0c102c0000040741d400718000700056843e01c50160b0700c0c3c961003c42c2c00004c0b14001e0000d0b10f8254000e50340c6448100d00030422758a4241001c402810503218103050701c1d8010043d400c40020340800d451203070895050305a100c10b0030401c4080a00c400c10110005100c0c540329081996058150b02c04008a141d000c103001d034104000185050780c0c080c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 209652374 1250 209651124 209651129
    0x10f02090f040203040c050d0f031209080901032a110601090b09150d0212060f07111e030408060f0a0c03060b04121104020406180503070b1207140304060b0102010c020a030504 77
    0xb0342c0181c480d80c80e400c081c2107502140e400b1300d401841d0071604000380040d00900d00c5415000e42c560407427104e414490007041321100400500380410038404007034698802d13042907000a1901021100d1100340070606144505206e4140001c1244907080a0b070207e01400024010f2090344030400c15016003c01180010740c0c014043c800c002442c0d030740c2100355603c3e503100d100c0706074000d40081501e40a40c0b01d25643c0e09020741c1d04003802a04180042c81c0984a59041c4810300c0500f000341484481441c4101e03103900c0c807101e1036000c80c0428040030411071010070a207031040c4101e200980c0d40b8103161248508441600b00d1300070030075060201c14019952440c0c200ca0803951550707504a500c1e105030034250084c00d050704003a58427a0000600042e00c80d80441c90300507000b001014810215903800800d6918909841a45210300041c440384548440c0071807120751146243c20081d03201350b0312000280b81680f0850f401c45000d0765550880d034240d40c0c248500413801c9070500040841d44200e8802070602d00492 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 209653624 1250 209652374 209652379
    0x8030a02070312020f07060906080a092001050c060f0402090f010b09060f13030b0106030b0d02030c0f12010501032f0120030405041406090702030a08070e0d140f010f02090f 76
    0x80c01100e0307260f1003004001c051720350b803074203403440c4a85845004208049920030000003544540208018065601c02c0c8600603921200c42c9200408002d0815480c00701c02d40c1880c14044140300307040c0011014000540715160b0411043c41603d8070b441004101c240c05000c10928100107401400080301074021100303119001c231402c6484900c07a2010003854400e40034619100032018500000300080801041d050f038000c2d40742801494458014031442d07200150010754141c1c444c003429012400d0260305102030a0003e01110190514429080e0a41d0400c2c0c1c000c44c0c5100908188031204001c1e12401c140710b0141e8041e51844070302c00030000307040959091294480c91002141070500e4102001180c004001c040c100b400f040b00c1c280381449210a0440303516001c1e40030b00c0001840c451020049509940140e02c4405040e100c0c144101d40a0381c5441011f9080a81000e404020503124003c00d2003000300240100001518924487d007501d46071402c80c403d440c01805150000d03a5003500d007100c2881c05 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 209654874 1250 209653624 209653643
    0xf0114040f0215070f0b1605072f0d05030403030f1706012106140a060e010206190609140915060a03061104090c09030303060803030c0313060f0c030f0608030a020703 73
    0x1210403815640708510f0004e10940e0000050010820036014947c032401d50f08800c50010035011109480034890b04600900704250281c2200725003143c0c81030070040c3c3c0242a4008500d00400021600a401040c2c050701c00d1f90010604008141c0d004001c0d070041d9605180c909010381c45000710a0140901806c0c07a4180020700005a04051209044500c4c00c1080c42090110581d600300044004521410640c06045c9807880450020300614183d00c0000041c1d00400d85a91503106810078052480c0003250025120031000600c041e150048080490018104001c41c0c1445030740180351a40c070000c0700e40303520018401c0180681d035490907441160340101020408801a210740305403840b4541181145500d000f409070504c0f540065040142d0344070351001c02009456141c002c2d902c2c081120440301420707040002135080111031070b880003000c0c440d50021030511450002e0005450050705030500080d5103100344540500c0c2401010000d1104101551410401010080d156095400080d040c1c1d4039 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 209656124 1250 209654874 209654899
    0xd140708090f0901120209060612011205010917040e13020306191407050301060210050903030a0209040902030d080613060b0304030305061c08030a1b170a060909050f0114040f02 78
    0xb11000b48030012000200b041e1002d41e1501d200400c41d80560100ba070080b80700200080a9040c9103003110b200c1d844440710422260310300500142c2100b41c1d684100c50310354039101c080f07000074858820321940141c454100c80e01d56040400440100c04001c001299005440382940c025803008115a900125040b403140011401c00f10b401e40941019071201c80b01c40401000c1090503644400030b181a114144d095580b082c082d010b80b10700344c2d0703801e54090800b5001040480c01101c000e600400400310058000b003011034203a000281425006240703d0003090803a0108201403502410994042c001d0140c100091805e00c05058000c0c04000d10007802e15503035a011820a03034803110112144074040741c080700322100d24604286107400c15600c01e00101d0411400c50120038039199480c4442075266156283c6005100303e0120558000d0001088503039900300108010306580101c40c030b058064002400004401040c1c282141c121480c08804041c0410500c4005a4080380743c1410a4045903c08800e18 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 209657374 1250 209656124 209656129
    0x50c070209010801020a030e030a0207140406150804020a090c020718110a03090302060f15012109080903060622020a02031902010b03070b0412031413060207080d14070809 75
    0x891000040e40c000300e030000020303d111054004040520107654140041141045c0981c0c0d24002c140c1108056000240d05222820b56102c0625003a04020008200c1643c0c403c0440741544481d40414001039809041205504018410000030240103204121004041e0720080d11801240251072411043d504d00040031101354118460040e10b4241c0d19599010b444000f40003400041c5085015001c0c000000d906881070103400b501c1052404840700b1082c0a91004440008200b00114200402401079036070122092098520380c521400510f55143d840d4409c151034a807004000c0ca114040c0da21580c84455840344c06c440000b10014005a25180440021382c01c1d0300900a00034004079000400c41c5034194150051028040103400f80c0340b50301c3d00c1c0c0306503d906105601500072035104e08420540042d21031070300701104c03007552448207052548030f642c1208401c0455100b1801680400401c3c48000f000b80200d0401c290241441440656461a80c6005005644010305003d10110301191581c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 209658624 1250 209657374 209657377
    0x30c0a050915030c03040605060d110d03200307061a0a0501050a020f0a0b0a0b09091b0406031b1509291317010b030307110d0201020a120914180406050c 67
    0x102911425500d0f0300c1c001c0c84d8134020b074000700c1c0c00f941c0507404c1c84007144c242d08000f00400402c9030840d0407000c007900c011040c840105888a0101c0c01c104107900b940d00103412a030781980d160044c000146a03a4481d03428164255000203801c0d0300d901401c08014001640c418205e50211340081c2003850f10343d0300205080c0d003006081308030391911f8041c40441c4c030101309038440214402d00300101d003003000c03c00560600c62103100480f80302c0110f6009041016121036080e812103140500240040340040c1c0f0f80ea50340035824841e00b80900407003c5010240a000f500c9200c40b01c61030703203601d0031100311440e00c920801082010011040d40001d1000c00b02444c4030300c0e100b2107400741c0704040c0070384001d0f039906258080300c101180003d0840d440c08021052628000c02191a0560006402d20a08444000b08200c20300c0f401c4c000c1341580b1989585a00045001c030300a4228030b01501c40f0b1306520705c3c1c03008402c4141c03d0044007522441a0305900042100900300560700309030855000902ca50b506804400346 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 209659874 1250 209658624 209658649
    0xb180705070c080a020a091a1507023604050a0f060605060313030806100503040215070f0b04020f010809061807090204080709060f0b1b010b06040806070206070203030c0a0509 77
    0x5100d091500880c02e50800501c8a2a042c4241c0d030b0b021149584604a9007103643c06181410848440c81e00b1041d41c0c90305070680b1412907271006025260116540c00140311110268250b101c0b45081d01d10f504000a040c40303a00c500c00403500e40c502c1e15181940da0b1039240c03610348000074103105c1207000842c24015130f540100c0160601500781941c90400100501409880000490005040400054040c200484c41066000c8a521402e0031a2159400c000400d00046014907550718184407101c0440c0e01040c0440c0740902461821060b805c1900612641d9410018000d06006500c2d007030205002000036459401207425090800f01440c4101d960308152265114185241c004a4040790f140c2020540404a450400c170402400f9030b580703007080100d101480b54404502c01840b0314880c0b0000d40c8140400c04080100020b24500742800184094225406c140444d902c401c003008421501048502d41008213400114194908013030060744610600f1100c404001010603c0000c6031980c4030006030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 209661124 1250 209659874 209659883
    0x10b01121512030e03060a1109010e150301030c0305060f0f0705030a0608060901140115052506050f06030f010908041203140d0b1009080a020d080d060603060503010f0b18070507 78
    0x81d0700b107428003c01c0c0008000034203220380100400700302280030510428811180d02d030421810540c00000566103481d40e41d800c82e802c4141c00e0b101d10303820041000110f020314401c00e004182142541062450580000c0440c0101c0f01384005001e419186125443d41c0024a07103001c07030b5030741d603024100d001820155000c054544624024007881d8841904004035103182112030540b16a0786e03d12400901500d60844d40100d0010824207100b0104d50050a540707541000e80c2c0210103089a49040440701c007100c4120503004620207210a901d4140080c1d2098250500240300100c0c8517262000944182e1098030300d0115400b1403c8101030140c041038100c0203403100c41075211018442200701510381e5461081c03062014084018100d40600418400e84890000900340202e00d5824800748000505090318404401c0c000480d9011881c05100043c01d013a541c04210181f5000901d0309442c12103214441c194200403800f0265190400c21000d6081c161000e20b015855100d0150360600c00e0000180 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 209662374 1250 209661124 209661149
    0x30f07080706110a23030106050307021513031403040b0a0209010309050a11011b0314030c090607051f0e101d07030b16030c021903020c030d091403010b011215 70
    0xa8010f0010009405081c000c0e032201d0b003207070042c03081c000b100484002c444900307070f00c0a00051048030310440244d940720340140112402940f00c100030580e008030031224155081c1e20341c0c41c2d4600301644146524804091201c40c641035051640da0b45a0b00c1e4402482c00c02903941c003151280c500d80c40381d00703c0050705421030f05440034000241481e40004050070b0405011038184c0c0d004441d0040d40700006c1c508150907660344201081a03180c04851030348054110440042c0c00e00c80054255503000052420a1141d0300518034030f50100801040701c40d2010000d80828640101c00302020b0001c10b4503a02c85000e0303e40080c154105a400400d5401d030507070704002610400b140801045080030080f8000c02d01640034a8500b4224002181900d41322074480006801c11004461030480303c07902e4003681c500c240159040c0d0b8a04101007803a00c804200c40200213580e1000802600401803030307400c00d061082e0000e01c03180d02a440068600842c40d1041d040065803400f2100719048602425000b5142c05425407 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 209663624 1250 209662374 209662391
    0x1203020f0d0b090c04230409082b060b07031404090510090e06070507240c021006080c100f09031505040b07110606151218120309030f07080706 63
    0x90010000080e4650090f0202400700e400701803100e084e1001c9441c200c4e41001e40c51611107140600e4005d14010782e8000d034480711160001030901001c1c0c41d41410343d9884c1d0a058100b900030140c000b5143d01d400803801d107040380a022040c0743c035040b540840e425082083c0701c0040c0c03070f0a041142c8107603401000420703e84030900c40214003e69000302101c0034401c1c1071180c5500d510040752074600568212020540802403030300081e103806004150301403140e20541600038101400c0d420b03512109600c00040c3c20148059110003031600c00c0102500d40e2034014444000e200d408100703100043d01d00c2509001400790100b0b2340621030701000c0080c550081400a00140008150f0040d15003501c0840d014a0f060300010300c80341c41000c070000d03d4402d002c0142215260348080c4116107a0006094010036002c20215040d020301010385030282095241200941c140603240b42c1c2040c040c1040c0d80900d0408009000f801030000065940980749601c202d44d6030205032500136201d128101c0c00602076400d04244 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 209664874 1250 209663624 209663647
    0xb040801090c060f090302040902010309020d060e190209010b0c0f070305150c12041101020a0206030f0412050a05040e06040207120306030c141309020105090a0305030a031401060c1203020f 83
    0x60303490768072815000181d2a01c81030280d50000c2d00102c8900000d04002d41000540b0300b64020201182c01814005030010454000c1141d42d03403a810151100c60702c4503a007a11040b010030619100807a065a00031030841d06074001680c2600610516035120000b00310518003aa0a0140c4ac04000c10401101c2100d5528581a515841103240840942e030001000036908030504046800700309601003e4071103a0303a10f035901d040ca425075000d2141180314102c0181d0050701d4541c002d601030759070000c80d00c0c02d178038042c584000d04800340b91200042203000d03c440003146c0d070080c0645082d01c0d07241071a040250364000100740240070303c0760090000c100407000d54172213503050780c04202a00e002c0c42c804010b29489100102880300f0301e07000d05400c00000403200502090b6a40040d64062052600c10301d0000c116000602c2c0c10442c2e0819517868100080c500d450720f415225001c1e5003c00000b400d83c180d1315002c009040c0301c84140f005484460602210b503402840390307040300c140803c508601600c038409d128a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 209666124 1250 209664874 209664881
    0x618020702011b0f0c0902090112050a0213180501060e090f06010224150316030b04080d0501030305030a0b0406050913031107080c010e03070503030a11070503120d0b0d0c0b070c0b040801 82
    0x1301a10400c2ca0a80c0100300b5081c580210703a124101070311104500d203e8600e0b0a030050200800b00c100e101c2e401e1040b18610210880048010100f000c1c0b007901c84c0c10540c0301071040340c0041c3c0c00001800b10705000000035499200003140e21a0240c14500340d284e40f80380050781402d072015010f52103009030303c070070f0007803054001002800390f4491181791803000c0c1d000c0e0526a44100043c1d100a81c440d041c131040000036041d107a21035200780b1803c2c20307a041054845044003565405c0c1c01c202d010072001310400412000c18840c2da00e0580c0c0840b0207002862400001c21800382020b00f05401c04089018100107142c0501070700304a203485c003412591040e60b141c00c00c0e41c403007660030b040e5400074901480c0c46038280390000c0c9040540d28001c2c00345140000302c100596044812214160550140c04800a61503509004610b03401e5150380141e9592a40450140c04440659001c50700c1aaaa52002d001245000a051042d1145001c5003643d070748850900366907940030785d4008242c0c03810009020980d42010341 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 209667374 1250 209666124 209666153
    0x3060c0304050d171501030914010e150f06131b081501050c070e070210050103051b0d0302070b16170a020601080d0806150f031015030618020702011b 66
    0x41954102d601e8804112014050101d42040b100a0301000c140407041e6a05c1040320804141400658020703d66222a81150001d4004078542d42d180400c880c080e00500560410441e140440c0c000d07031501d032551401186001c5c3c000da0040d46190600035180d013140d8002c0405c2494400426402c196400000b4a41030f07044a1704a81d00e01030500d000d9155002d00165070740c811034140a44207040c1001e144940c00d13031009205804510640321036424443c07461040502075400790002e424420035040640b010030b801d20004900a87c0c070017200d840030036804610349043d5841c6060342035403102070405580a9144102e03015000c42011440500300d411000d004000906058080e9007803603036101441502c1c0c99020200e40d010071203400c0090f00514100d0080c04209005d00000c13810100085661541500103e5040310048241131b0140070b011517959207180080c555240600c66142480340c6159848429003c0002050b000716840e011680112480c52001220001101c600e05447c10645001800c50 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 209668624 1250 209667374 209667383
    0x7050a020429100e090901020a0f0c020d200301020c07080d050309060714070b070203070203010b04021303030806040e0a05100501080109030f05180303130e010e060d17040503060c0304 81
    0x440320102c2480000b08003000b038500750400c448400b94034802c0c4107024180c4649002008100381d4103480507a61043c18500072111003000680324442ca40002d03001c1c05854000e0410310813003840301001680c1e1910300c0d40d2a190b01204c444880392590098121190130111015495400404ea11a03c00d6001444c40c044070b080404a40180344800d03000e440354802078800340138a0300b03c203000400e03d5005003030700120740a0300030540d03241040b50385400503e48425100310005800002d10502585005d0195103420718080300c0031031908440c001181880840d500c07000b400d2203034500026040d5500d5a00504c1c001c0c0500c400d13149140f0140c502107448a110719440c01007145440c0002c01d10f16070510410101c40e5040e00c42158039803040c9000e076402c2d008012031400082501c4e44000c2551400d00250060311090018480ca241c100741404c80003580523000100840e440c4000c01032195181c0900c44a140d4000a114038101003802c01c13017002d4400d6070401072305841800240000350f01d600008501c1107014 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 209669874 1250 209668624 209668631
    0xf0106060216120803041e0501020703030b0f19060c0302070b030a0b190e040f111503100b03130204090312060e01090b030a1101081509010b030106110d170402010903060207050a0204 80
    0x1e8203014200b010b142c01002d8a40f0301c4c00e100240001d0140c02285a44207200d42c1b005001003026920349003640d111880480000c0d1f16682000600d003004100306800000c1100c95129100d00d105c250315000c00c40344603500800c4003c040140c00d1500920850000d4204442d00b280d43e460410700c01000380c4145980e076801800326240e66100c4174082d440303800039503540071030390300c8103403620385505103200c44605c13058031403031089060304500d683c50039040d1908402030801d09459181c076044c9070320098034903400600441c408000b00000c2d1120340d480c1000780c5504880000d00f0f14980e040840320b400d400301e0700c604051720f0440c001ca4151340c9800d81394100c0350486014071209e41c81d0f400f4075440b404450401081100c00c015001c0d100d41c026070509034001320741c0d00180880700d05c0800180d1300110aa02c0011032000000c01440001d074040741a06219210b0070080500d083d00c0c00d0020015000040380c1240c07031124401107400c42e88608101c600564005000355151380180c10001d1b10340d512140300328480ca19 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 209671124 1250 209669874 209669879
    0x4050906030a0309051e04021201090b0609030c10110601060804061107030c1713031a01050a0303021203041a0a0c030b041806020d0f0509070305010506010e061b0f0106060216 77
    0x400040000105615a843ca04130600d00400d0003c1800c00030f002212000b6401c814924540350361014104032924100b40c03180c0c0b545403544c440c0c107ca004004c2d50f070003840104061821902c00091600700540d0503a02034407da0f502000072500e06181468030b4840d8040e103000081c115500001c0c05014a0288404100100d00e40c00b0303002480c0700e4500001d020505808004020804456458503480c42c0015003d142020307200c41b00c0070b80010f81d0030071150440c400d044841c000b440211030038050001030790303020141c500315100603684420040c031186400900000080c2009190110042d0f202203030100c1c80d040d4200510b240014010380070321040080d02d842400d1031603181500500ca10300d010280c2c681644503036511103401961118140000c050340300d440a400501962068602c911081d90207401c2040c00c52801909540001d4040c5042115034078803980a50341d040111080d4100c0f4081c1007607044d0b02c00400c20306045421760b03e900c0e69442d0000000b401034010036464000e95101109c840d0194 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 209672374 1250 209671124 209671129
    0x3030807120903140901230403030e030606030601050d0804030c0f15020607081305030705100b13060b0901120e0d050d0c03051b0c0304030c080a060c0c0b0609060f040f0204050906 79
    0x280302c0403000d000141c10700c0200080c890090000c1071030803018940010a00c0d070041d032030720301e40a906440c07810001001604005050340100508983d581c11406030003241415000a40d494406019151107804c803020420704010f00042160011603011031000701079a600d1610079000b60080c40340609a091030f81c40012810310110f505031280e4442c3d00d400725943c8032202e0904a580c040f900c112941d01c800c001640c0424020001c0b040b8140300507001203550740c0c1c4403052050700500070403050f0a441c10003405016170120b04090740e00901080c43c040945018a0060501800ca0700005541a00641511040d43da911000400610950280034459060b11501c11400c44000b1a60b40182110049200696805c07400080c11840142c10869003000d03140c3d22003210042079039102c0e107190f5002450301410032089004050b0462800e0511121803046521035441d01c1c8402407105100d54418000113050b940e41a010040d65440070303000b0050000246c540f00003d600c28001c0d680314030143c50000c0c1251 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 209673624 1250 209672374 209672381
    0x9090c07051c0908060f041b0609031707020d06050916050a03020d06021201080c1005030c0702190902180301061203050d050c0403020d050604030f051806030a0b030105010303080712 80
    0x115403003801030201c2501503805201040000310890b0400c442404005050b0f0f00411280340100c50034500c00c2581d04151906402c4111160302026001e442c80e1030412a003904400d80000322074000c0043d091041c034021400f4842e11903650000c1d8001e00340660340051182507405184200e89010803144220300315200d070b000c925594862541d000606243c14801800e00e11107040c101c6200e03510244c2428401c59100f01d0300c410980100105600854a425640c80c002e520440d402046003801460340c20b025403185024400d40700080d004080c1c9080c98141c14140c2c60314a00205000c0d00119110041082d41c5805509001c0e20144203608051010400003804494100d900350715072503581c0391142d0b079100d03040548002041c4c6041d4100610001025031180b40101c1d4241c1d01c507070f01800b480e141c1450068451446c031087c10b0100b1a060045282048800c02420480c20040362019101e903035120204001d042540842c80e0075500302000002010741001c4c19501400058503026111002100000100c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 209674874 1250 209673624 209673637
    0x5180303060604062a030c06050f0705040b131503020c012901120905030d09050f010b0604051309061503120507050a0204051f03050601050f0d020d171b0309090c 71
    0x4100700b04802c01c07135180152005900200b49441d40603081551100884090280c210140d01080c2c07080e0100080200742c2c422540e00803200412004c05060014008081d40283e0103030082c0034100107410380c1401d8480b51074000400000000c1c01100041302c3d00103010390405500c014045d030805e41c01045c1c5c0030040100d40b00c000040308548181d10491401140c24012b810f41c500700003036581031040e0108000b4401024515100f0b1404240d0b50400e28100e07140c5904c1501c00c1e0950707490202c51028558549045038200d980072682d03008a042900902d90050042100040240d4a01141e008641d8619818441264043d01e130009004004100c250b4291191043c0102a034205c401c0150040c034050303002d0ba4200c03954a00c686107520394a03641c0440c0f52a96041983d29078801c000400c1985480c0885150485050b204140071031500e5002c00c1c88032852000050070580305107101c81c11007001c00c054809040f20f010055650310036042010b0789036889007080314081c413501c1000504200300c03172003201e89 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 209676124 1250 209674874 209674879
    0x10207090b090c0f1b0c01090501020105090a060e010e010e0d090503070f0506070305040b12090f070803040905060102010209180609010608062d040e0106170607021b1c060518030306 80
    0x50f590b900d0110f07140b644465540400203105001105400e251040e004010804510003041d13a03414003000941384036480d80c0403e0440e81014100209a0804161411005c0d0702600205030b00c1c41c0c1c080b14038003500c40c200700031449618000e0704520340107000803010000c845a0b01d0360a034180d11502450740b507890078010b00e10148409002009a420280001d129250003803a003a400d158883c218900194000c003004a005e850200501000007018403504000440500092901ea89040c0106891b0302840c4121000c0300d07907900015469900070340450b224058002c2c600b00a8024119100d4500c550565459020325906000841c00c00e0240d10b950780201801803c0004075200d030001c0703a9201e44c088100f5071a041c6407480c07d0714140c0f16401000c41c0d14980d400003056060070281012440e142400d00504164007403424440c00c903030042544002c00060b2405198808401008078102905a00d41144031901da41003010600c42c55034481740c083d50440719500c03044a04081d000340e0300c0c0010f866295 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 209677374 1250 209676124 209676139
    0x8070b180a0f05070e040f0209010b09033a092102060d09020a0504053d0e0c0405030303191503080a0c02040603020a06080405060f10030b06010c1b05010207090b 71
    0x4000c03548250b02030b000d0911500440e840340c0d8071052041c840a01c1501c048484810310882c5070218035112000354050101401010b080c00002000650344082c00d03581d0701d58000407400c08140348a5100d0150590030403402c040303040500c0800c030040c140c120911408002160140d48a84c0b4000603082005406400820643c28401c00407a1900186942031007242e109100a9000607a80c4850003524400c03a60143c00c2100d080740d1803403881c030319291855507000041024a140105181e07075548072007580d813008501c0c0b11946d00c00c203880242e0300c41c40d00002e42c140f0020003040103039000b00794004007150b2a0b203000e04c9514043e0b00c3c02ea601d9511404001c00050702406000040e512815240400743e000070000305005030f4a4010031028036064029400280c5848108800c0c048104204c58104816001b8440e880c9041d0800d1162445503003c01802015401d011a43c181c2c4110a0242d20581009481c09404040e10721205013014620486016010302c3c2000030380410307980b140a40d201c20141034074 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 209678624 1250 209677374 209677393
    0x6100506030115110d030e0c0d0b0103140709050c1305032d01060b160c0605040e010501030f140f061f0e04020c010905100f1d0c0d080405030a08070b18 67
    0x82d18a20020f400c0302c402c00550a40c0d115a10604020003005000d01c2c0e01c00007032904d00201828103000400480134015413200700354800054030042030504607a00700380811a021708408141d82400f40300d0f4000c820040c2404244035612194900074000795008031401d0328001d0340d5906241d111015116003d80b103552040e40c4e007041d00c1200c554100341d54440320000410640b611f40b2100c0700d40101c1050241d05102c01010310801078030081c0d0707202500702400c10a09040c076007000f0191040050046504141d140c0c6030103400032146030414003000090f1903c5400b03e14041c0070010444104590861103103401c1d0f81c014200444025108950200a96a40408241e0a030078000a0350000002e8006590b035800110049902401041070712440902c01050b000c0d526540c19055407403084042042680c0203001d4441e03c1800a042601100c05850918000c1c40718240399080d40104e522660305402404d20220810921100410902e480340d01800069142c0300c0307900c40b440c0700d40c1003040050751013031842 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 209679874 1250 209678624 209678639
    0x50105030303391e09100f03140405030901020d030e0318060405030304241715040603020402030108070e10030506010e0406020d0c0908011802030c01050904090204020a0f02061005060301 82
    0xf554402d07501d030145024000e042514400c0e6211030411044005010882151907015400f18820034160f80e0013a0b0309080c4000b0006a1680407010000f05003d408a0801041802904111428808002154050f252900700a52a540304400150060117909224450079001c0d12407911035141c240000d508140750004101d445031251041194401c1091000080c2c503942003005202510f0b030040011000401a0700030450042c600c1412414072140d007a41400d00c5c0540704990741c1c04074070b40d011721401d01c1072040841d004100301d4001035005400080003251800c1c00080600c112140c103070001c4590b0ba68050329101d030b2002400018002d420040041122441032800303190487d005da04010f140106921005080300c450303917017901c0413980003003041103048020301c985440c0190580c14102a80099800291070784d6403c40d02e181407003804030340041039858a41c00729131f1545c3e02074400c40d5038028681c1c0150000d03c00c101e5040040c07042d000041c08000924038407000b260000313807800b0300b147d0a0004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 209681124 1250 209679874 209679901
    0x2030115140f180703020a0f0e06120a180602131d070e060f030907050f01030c02060a02030a0f06080307060615080f060402120411030d14091c05061810050105030303 73
    0x1d00c1caa00006883c03141c0c40d90200b00f00854066000ea480041c0e83d0300c08242c0c05042010001c80c00c3c824015044056a51030300d070102140d6145502c01014102a5500420301004101c102001c030080e080004c50b031400c01003264010504080659280d0340130580d540c81000c1000d64521000d00c03d6980a40403070708041c081c40301c1a085400040403a41404900409141d040e00101d5006c68558810b0504010b1400c00b1040c0b840c00c801d0a21f0140030380031004401a40d26000589408481c1c4c0e03000000400055003548510a08030301e607403082c0b112555840c09240d503600210320a03500c5a14002000030351103a5414a454201e00e60b45403c00b4590310743d514620700081c010300d800e070400d4082008203030b107081c8400c1144c8100d00c20500c440b1605810021706141c00007880c1440b007845041000002070024040554144013400c64020400f1050007005240b24090408010140d118038020b1011200c0710000041c0c00a03c50801c8460f4151803007240c00554034203100e502c0e055001000030a0b0b05002d10340 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 209682374 1250 209681124 209681149
    0x70b060307050909011e0e0d1d030d0206061c0c0e0a02120103080304030810060e0603040501061e210b01060c02030c090c0903060a0c1403190906090203011514 70
    0x2030586000d50742d281c012070032004088030882010b955501ca0b0107041c207020102842851882c800c01c00001ca0420f0015680e040191600c00a002d071082c80010344015008080c4d9610300b001d029241c8400240308c001c3e5481005480e06403140d0f4020a21655500b0142907240c01e031754001c08408000d501c0c11072115880f01d000741540440c15000c01c1400003800b82204401d001318441ca100641d00d00e03060800809004c80074041142d0468038907010441968010300a03820700f00b08036051562a200d52074403500501260b40135600c1d48503c400c2401c22a000185c3c41c82c00c603100c0c20422002c2c0c4403810800400303611208030040806003000014032296205070110a03015101404990448210200042c017001c400c80350310303c0b0980c00260744003031810284503207030300414104420f000e4110f405e407000c0c003c08a9112034402010021001a00c1106941ca183d941e010444004020550090900c40040d100c8010b05034003940c00d20078038030840b00b2220f00c42c0d0201c034407101d402141e05080c0c800b04240469280c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 209683624 1250 209682374 209682379
    0xe09070312031b050901030c030504020a18022503020f0f060a0c0e150a120e061b211803090d0224130806060a030308060112111308070b0c03070b06 65
    0xd1000350110102d240c1503c03403114594880729101d100490004090b1015003007103508260400c000d100045e2508240441580d0300c1603440c124440b10300031154020300410390801030070303407080c181c41c2e0402800e88052a0030074004d5003a580c043e03000c80141d03035851180903136807c0e099201c40002000400356078040c1600d60b01a145c008000040040061400c2c0084020b07212425800140380b110b0b01e4010a07100d074104c403021070512000521424054a44100030800c030040000c1150700c0c405183c481049070801d42c40c50301d2400360310803405c40c80e146030b4104031860b41b41c003200401e158a0a1500005544d02c2540080c01207654484a500b0710080c103661803400b03041c0c0755840030480030701109840542041c0e1065002400580d280125091510002410070750149900c0001403011030350040f07042e40e2003202800c0c00b1540b5001c0507101e00007003a041d07050801c030841c080340c0305207910511411541201e8131081180d035810f45030043c6003403e2150200072039041d84100303d074500003511201060781c0310500 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 209684874 1250 209683624 209683631
    0x402010f0c080705011506170a021308100504110604081b0a090606210c050f0f0d020c010e06011e091109060301031a0c04032409080a0906090e0907031203 68
    0x865451000b540c108001c1200c1d03917516109040c441030011481c43c80203040d03e141501070300b983ca0884a08203a40a0600b40043e41c00140740840c2d4500002010000c0100400f12420405211101d100030a41034808803010150810240c0e42d42c0303056410b640603a04041c010304420200026425084042507840e2a003100c1c0c904c200086410161084000902e1544c8401c0b00b413500b802c0420200d14451810340100900d0560f80c4815958804181d44040c0d125412141e50703100c1d41c8440103080c0c001e00b070002c040c1e00d000181e85c030f0030400306400c12040d05030140100e03001643c880c0c092440e800c0340408078010902268bc401c101d035060642011464030350b040082490080200007040150340260000c1d2a03034480d400034081611101c15440754000d0481c00c81134101802d40d80d43c0598040301510404110700307000300142042c00254480c100c0300398800702e480c2e038450380c5400c007030b003020a94031030784012a440c6880000d2481040410522444884c4086c3c4606410b5035540013504100c06501c0003095503 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 209686124 1250 209684874 209684897
    0x60c0611030901060503060604060b030711120304030e130e2503020d12090801150501050703050c0d080a0c021903050703091203080a0506120c01030e011107061d150402010f 76
    0x4030380d0000e5008140240001c14101d08140070701d454564040c04c3d4078061032900d04200040721034141620381141c1c06241800b440180326a0462501e000b41c0030410070000000140700400d0740114551046840030344248100c07106d103414883c115401c903c074a0541d9080a00c00e16028061542808280d582d0a030810784001e03140c0e008608155410741c41290018041c03503030b6000194008004900612212000b48841c40c0d514078089011030700340c80307640e043c0301000c01e602c41054090020b41d41c418107420101c2c2c450410000008040380400e4a04606c498a0072458203a881e101040c0703440391088000c0325003400b4410350780840d4a0783c001c22042d0201b00d0f1403400070940003200111040c10328004c0d620002341d41080c040c0e4004a4001515043c07107849040c0d1031440c80100441c01740d0b180507090038000b803090f811405140c0905155005880c03203c8000444004201d465844100084d0b0080240d401604000c210f6a035591b4041308603020418004d00014015032141412040d400007a03c2c2c4001c0f81078 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 209687374 1250 209686124 209686151
    0x1a0711090601121406010201140103030f0c020a03080c01150501050c1506040209060c010e150702100e010608030406120c02010b060304080a050d020c0a0b060307060f1409031504050d090f060c06 85
    0x8401c4080403a1444002d07045c0f040c19a8240215109010034044810701545555009082842d50340c90900c280190008807400795503580682400039034200c640c1603a05c00410052500070801004601704003482101c020400394450320944411504a200809103009080c0c5000380000000708501d600c1a000c002d094015242c840c09000c00300c03441800031544d032400185803410400445500082d417030b4034070208120300350700041410042e08079100000c1e00c0400e0100c69809002140c000e0100f51100081c0010159032000b1010880c201102d010030055206400403401ea4680c800b43c0c0d584840103101040120f85804014002501d840c1040c078680003040508800ba80c0000300070703050b6a08034224401c1401138030300c60558020381c1100030700449800c08801070a42004c038100e41007001104d101050f01e40c80300004030307020000b00504032441001000244401c00808031401c072040d00980b4000385030140104030b0718081d5880c240b000c6403030700c0c101402107410107911001600c6203502c4001c40f99054 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 209688624 1250 209687374 209687381
    0x2030a09170409050108010b010e01030209030c1507140d140a09050904060518070506161e050325120305060102011e0203060a0e1e09030f0c071a071109060112 70
    0x4101540940e02e0303501d40019201282c0f81640b02c1c0049034180304031070426a9000e00c03005130503c401d00b00140c842c0310650100c0e140000710062079805c002a54010301c04628280d0140008de48207540010b00111856035080d02c0310580d41c1e2903808034030f000d0a0407010079800300140012058a24040d0b400741d07038440020380d1502c4162015581c6035551400d000165120002c200c0f0801d80c00c0004061051428001c10384510031a284901c1e655070701c4e4081c0b000c00412002c0802184c4c114855031020003400e050090710380e2f11890309010b44492080c0c002c080320f0841403455001c2070304113804800c1c0490014055018280c0144068119566403070807003c11032201c001e0b0200030614100c0141c80e41b90407400e01c0005d400d00c1c0c1011280f1842682004a0003100d04844c110f480200d03404030031903445080c40e00d40740d4041c07400000404500410140300301d80001526804648040b10740322258070202040003c5480f81150160110803d161190b0385800c1500485800001c18540034016148001d49003049 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 209689874 1250 209688624 209688653
    0xc0607081908040c0602010911040f110c03090f030601030c030305030a06051306090501050a050901090207031106150f0907080a0b0102030408010f05090114091902150301080a02100801060e0402030a09 88
    0x300e1182c1c0c003400284101400d212024003450300003001026110f40303d105020512400c003500c901d86944074106101c0d07284d0800000301c1d03140d801094842054045080c6c4941104071290f0182c070282c03441300414900080c80034101c035006030315060818195142101c3c80d60006000a042c6500c038400000d5a03124400816500e1000c0380c400a03c83d8100981c0506aa9040e03120a101e484024014459566480240e40c110f60000400680c1d48606240c00d982480c8031181c00300c50b50065404001100b00d80b0b004a00d012081100e80e028501f180a08210140406a80c96400038000c0e05c0050340003182c40d80406003c4505004403410306035561003140c00c0d500450b44581000340c8070003d2000401d400d026412051000580301203081c513201d29850764440040d042c500c2128401184003055494054407030391074150180301207039079686030719031039595100b0418202e001d42c90a455855000c0c2c456030480341600e0040d9100a0305014400c200400303900040c08415401c0d965a41c00e5002809001c200e010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 209691124 1250 209689874 209689877
    0x18140c1806030706050a0e060702030106030503030c0c06070906050a050a020f2e0204140d030504050607060e0c0d05060105190f03030f090f0b031323071401030204080c06070819 78
    0xc500e0010241420507070154811001d1010034040341c10866002032810300c4d02d280075600070780c8035422400081d01405c480d6001400c42d010000500c00da80c0070000051161107500300440b00b00392540401200c00c40f0340391050f036002900900040c15180d00ca00004e1a0255040c8101c90341920400710440c103202c1c0e84101d442c50000361b40c1c01e094100301c04401c44003041c1075196003107040c40d161002100f0340c145419502c0d0700c06d54845000d042094020800c0d00c000c0c22000d807117962a07100c649003010007801c10303140d02c0600784a1000f10300b89924110044070798560f4081d0261085034a05018015440a0001803d0403024410b2002c0b4040e5202d80c4950000c60003541c403070788001402e881c06000803c05410840301030200da00c0c00e202d0100503004a0390090700d82e041061080c4074a042410b840f800d5040e001100052249100c1006900010074800351500c2000984c0c03045d14800065040b4451403103203d007540c221108407001c2e0301d4004003410704a8050806145406900301040e0014001d4084110 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 209692374 1250 209691124 209691169
    0x603150702330a0c11030703090f090903090b1b010f150b030702061b09030a05070513090b0604050a1b090602061b120a0f1109090a18140c 61
    0x4442e01160a0151001241001c040740b50140c0469030b00394184014824250592501488455203100c2ea04062201e414801600e03110300c058940281204668810360643c00000400400d40c02401d2013801202d9a05880f14040649480e04c440800d401030b06c0882d454500d0001851030504003801a0744802012001c0007400d0b40702348820020504098010b0180e598040c410003900c290005007554010303818101040300240c5465200800c1d104028049406000d59003032070082107000100c1e0b01c25130b10201c031030580700c412401d00b00c012500c10a0029000400a01c04100c01d0706050344100e8110380441c0010808030851090072050f00310207000100001e022a004016040d4103206c1e081c1c1000c180075849000600400501d4420700920110044402c80440490014446c0d5440a82d8421120000340560075582d81c5100d00380e005040514010600c2800041404c41d161044030031039142c40d066204448410349861545c08108402a4294440c0e00302d01e50842e07850a00f0000d0b04c4041301c1d4040e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 209693624 1250 209692374 209692393
    0x510060b09130b0d03030e0a021008150f0d061e0518060f040f0204240605090906060a05040315090206030115110a021005070228030c06050a0e01080603150702 70
    0x1100c2c8030781c00c050314a00c80d0300d00300700140140d8403040da043c8001d80600e00480c10400002e01c40c0d0910403100d400a50080e446a01208202c4d0003014842c420b080340c0300f010000034070480911039035048405032a503004050402c840001111544800d036201c031940140341143e0301c24801c2000302d03882519505c0405204074244508108108101399100540c000b900c11f06050640d03a2580000300c02600074401d40e16510481d0b21034030241c1107486001030510004601d80d80e500e00c040c09662100107e81e008a41400025840381840000c503111010141e80b502e02e010b00d980c6039110b20000ca800d54612580d100c80201c00540d844a02641c0030f480074040d031080c6007060640280c60304401e6640100300750440402d5102580d120715855600a1441c203080d80e65107518070015254240407518102004d020340c404040000d0700c1310100d000d0320711032030f1a006100e85500c42512203004035907030103000445011480c00c40c1e5220302182c82c0c00000103401c270744584c0880700906243e400c0445441d0016407181029 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 209694874 1250 209693624 209693629
    0xf030103141009210c060c0801090c080606030106030b0105190807091403060c09033c030331050d0c1104021305090907030516080607030203060105160510060b09 71
    0x20b8441c508450001040500a80c1c0e03200e4405900911010404251301243c107520300b03008007401d00a00c0e50184003040300e45600d0341c01910760f000a0107010542032030701e0b4076003100340e0140250501a0b180244020304513843c001084001d0142da9250b54100142881080d88101d003818102c0c42101190300c1e000141d01d0b00e61401440d0005035441a00d407215054140b00c51628080340e40307504404c140b501da5603a040749038046407911a4250488401ca01c0304048181e103070b101020040c0b8264509480713522810740100034503030b0348d000079140b810350321034456001d0b000c407001d0a508a5611000c2e015203000490580c44c0c41d41010407000b03002d800300d10012507240030424030050450052a00710b0703003181020800388604840400c1402418064100813000c14034204080107503000555000c011500c071040100030b0254401c84030300c41c54010340b144c240030800080c00b90003601d1003842c2c1a580c003030502c1c54550480e0411056000c05540d5409003465008602100d40113070780140c8040f440503503072040c00006 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 209696124 1250 209694874 209694883
    0xa0501031502160f0222020c071202010f030b19061808120715090206070f050c01261f0602070303110c1518090106080406050907030c0b0f0f03010314 66
    0x246079051034410040e0b07000c400604500f243c403140d00700e0058900c00060f4400f0400c90b801e4440344550211920450a075069481d4004000130303245807064400c01d40d92616030704504240360800030b01180240781c11003141446548540791018009000c010311040c0040d06020544031500a00c000656001462007641448801c40b0014100c200003006061700156940010f40100c0400902400d21481d411400b1440351300081c41c403d400905040d5182d216160812079000b000c402111319010300320700b00c8050340c019820410b55201c041c1110b015400320842c0fa500745003004080d4820030800c64040b03002c0ea01580c4441002d40fa050b0004d01c0b226081d0304010f000c113554000342c07610300d5024032840342403622100c40000c989102d007148940c5400b4001b00c1c0480d00c1c100c0a9415801c52b141600000740d5544c00000741307000d1806440d08120b140c6079a80010780780e01d02c134040500303042c040c05008c011005000f8014000d00100e518110304080300c02c0402d0404d540280c0c01030314151940003054280190900 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 209697374 1250 209696124 209696153
    0x301061b05060c0a050d0e030319060503070620060a0c0207090e0c04050408040e040b07110c090402010503060604030204091a070906231204060906060b160609020a0302090a050103 79
    0x918000404529a5030780740d9600009014089082010605150780343c000c0c02900c03001800e5203c14003c200700c60181981d00e80049503c41140482c0900c6103102c04e04510940c0e0682d0070203005048101c0c2026800e0f00d620a0119a4000b00b1502c51035110380c602c1d05000c007a0007410320840120701c00e2202c500082c5401001d401010f169482d14600380380303040300094071f0041e0281c1510007050130703580e40c14098524000c0d0f521440340103084030100000c2052407142180f09400644800e0008100707568680c2e61042d040684a410010100c0072502541c01040991750142004104c00d141a4803640850180c6061201c2103646003c0040f18107480d402055096621003032621301540000e10304030008148100407040c0c1d4150b801758110400007000c1c40401c885a8080c124032032420340c00c00346840d80081c24854409c4d070302d072480c00030b0100b940d4121808440404001c03060035500008680c8409009002c0804100d900c054001d40c0000182c41c1c003d13041e8030030880484001078661550030a0a098004c21 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 209698624 1250 209697374 209697407
    0x50309041109220c111c110609010507020613020d230109060b03010b04021e0c070b03150406090203060d0201120906050405030c1605090103081b100608070e060114030a090204050c030106 82
    0x118005848180002e04101802c801b800905240c6c00d03a04410354a0805005210116004600030050750080540041e0702525103a1b00b10b540990341c105003646060640000258402c4400d20307500081201c0ca4401d001d0a0000400015030880b030100c1c890031120b204d1801c44a1545030101c400d07484c0742c01c0c0324a41002c48217640541c074101c0d6401004161266074604092201408101010311680400840e0013601540024964a0a104404500b410080c40c50644690b042010216811801b0f000703403801400d014065071406070855005440280c07007c0505001156034020540c0810303442e001c1c0900440c0a03001851740e0302d0030031911034240207410a0741004508109000c102c81c0e260403101a044980022589445000ca412840e0b20990040c1d00e49400c2e204400c8002c1c1c0050380303035003e0400c5442a50895410319682c0702110040705c030032078440b0301003110b8044c4545200100d900031503100501000000b030a4004c4e600180803a20141c6840b80440c0c408001401141d4100c030011b01d08203e80d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 209699874 1250 209698624 209698637
    0x1514031506060307080415181b1523040605030402091302031b0f040c0905040608120904020703120207080409060501020307051c020f100203090d0903050309041109220c 74
    0x40d9022403003c1c40090030110401c02d150f8002400e001500c4002c04030700220340001c6c494600c2e20390558900e10380451050b2182503c140c21800b540c00040840400c80d40d0700d458074038101e24070800035a08283d250410001c0d14101c004030400d044010402040a442140c0b00d2035102c0c00d082c010b00c01c00c888001c0c070701e41d1a4a18044c440c0d000d40c1e00041c0e001300c0090001a560011041c8401248010040d1540385030803500300b607181d2034199002104d0300281d690a0b81d040041d64ad580400659402e0b0403038000c14002c2d810400400c0c2810305800500400b80130741404071f940e0360342144400480c0e0052409807400d0030b012800340500c2781d0500642c00140070900c000c6040c180f898841544640754010301d94242c08581c90071540040c024000401c0f4003120900b691022091048080085d600031280552940110084988842d004400b08000d480d000801582845c121a080c0070060521800240e1419001d100706c02c0b00e0365504a41c280485501800d0f000b03640c10502c840b005480d40503d01c001800031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 209701124 1250 209699874 209699881
    0xc0e041122030c09020f09030a1203230f04060e030d050a11070503090103151a222103020309040c020a0c210611120403090609060807200115140315 65
    0xc1843c03030042d24040400141d488640410800a81c440d241c4229010b0107041d40d14400e1140b841a1901c140c00300d0f850a1062080c0340d0400d42d413420700c00903d46810303400507003c01c0c400c0003406e4203183e01c54814140001d650f076954410a1440c0c20a1080f601142d03203031810440e041c00f090044014940007804540e062241c2e9580b015181e000d03400c505810151b07108034100c0094881c072580402000743c1c440848881c0381c01d410b00002548000422450205011510024402c140c83c040044950419140d682c0d13191800e12442d401c0c1c6e0550041e8110f00c028480500680d9035072003a840003111a400400c441e0780c85161011800c0300b207504c10141d05540400c054803420048480c598403940c0a0790001e80e0440544621140e07024820001810300030318020070007050f4100410100386c91441c1c48120000b613888404640d44d400490f4a0340014424501c0724072000c800c020640c00c8207000310008034041499000c0b80035500701030703071200c0300886180ea400061403c0620885064060180a0300741034174 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 209702374 1250 209701124 209701133
    0xd0f0c03120f0801050405100e010b07350a110d0809100e190f050604030804020a0906270e0a08030a0e03040f0e1b070807030e040902090a0c0e04112203 67
    0x20300505c11140110748400004203150001044031010301403400059013656100c01941d4296001182d080b100305022101c1c940248003c2c404498444400140580348805119150300d00350b000b044840007401042e4000d0903000343c0603c000e200948903075581a0140c50204001803600c08400c5c80d0722a00ba02c0e06141403255040403919003503c8a007071540a9038903c5610b801c81996034191805883c80c000c1100780006c01d58440800b0340110b000319440307a085034440074800f04490b0b01d4802c0050b10840c441111701c068844001e245061101311200103003a809d0051804d05000c0da440f4202d4030312000100300052100e1900c04c0440ca82000001542002e00741034001060b000a4000e03030241203400300020303110440c22164a40c3c0102c4511100341c03500401d141040300d5810006007240428015280c58a1030308051250002c40c1d0380040441032240c03184803035040180394644002040100c5020403000a4036603000c1d5115100034800e200ea503410010500544110001800b408458000d060810224 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 209703624 1250 209702374 209702387
    0xb120102030109090210171602070b0d0603051513032102120f0115020a0605090313030501090201020105011d0402091504020a05130807060906030510090f140a050c0f0304020d0f0c03120f 82
    0x248d810807031403403803040e4040e05903e024030390f5104004411002540700c0c06224a44c100d1404c40b417091040310000030030201c050b440c2c06000c890352103041c501c071010350300428841c550301781504107810100d6511000e144407000903a44030110100707030440f4038000d100026149804072801070543c41400e82c20860300080080d11940c00c0b4501608040e118401700e0043d003010700480380c00842840e000c960f210740c0c0b49403840c060b010b010810303409546088000501141c40b80c0c1c1c006100300e034000348412207559607800c21201e410042c10008246040d0b605541d4a5192071000709105d52941d103669032100c0340c0c1406a10300029541121a90381c00004042004076004000c20064410f2130030013150a43c1c40c292010819102680b04555842c00c0241210700800d0540c00a810308401c00781d41c401d1552844101000d44501b5a542842c2241c03c0001c1000b4251200145030880c0c4001c28110200c1c1d880d4803100240740407204203403400410031104108014010241c2c1341240c0c41d034104505029010380001e040f4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 209704874 1250 209703624 209703631
    0x11030901020a08030402130e0706021002030705030c0a0207030507140a0f0506030c03040f0c0b1809040201050f070f1506180506010e09040525050418020d060b12010203010909021017 80
    0x1003c80100109046540c6c11700e003100f075150020020070186100e0243c080c2c3d1a0200e100b0342001d4081c0d50300080400c1000c0c02280e209609030740b9881c3c0780d0345408660141940c40740e4901c1d0114018000007000084090220f03c008050344c1d103031850b02404c0d0030100320281020342c0c4146a54100d03c001004182c842c401644e0703205044034412a200d60b5181046c540085c000c410052480010080106008841302d0142000c0340003401503d412102c0305080c442c031404261006030108a0600c01c00c1200074040f4001c201051040c15a902011155500c2100060b4803000307848540ea00c2d40c0b0280300007a406400c3c500308040c044070521603402e201c40003811180c0207031040c500407500e01c40046d041c0141004030f9069080100c0c0c04503c8030925800b03140500205000e03c900c11400d01d0810740f011203207006284400c0d0340040c01003d901100d0b98a400060525954860b0011284030f039244038a00284040c6000f40b61101002c1819000c0348100b0441d0100042c1041c01d004826141408121000b60216030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 209706124 1250 209704874 209704883
    0x40f05010e2e0f030b0306040605100f0b04050102010510060c0b180f0c01180614090a0b04030b06030706110a0f080d09030e12010e0303070e0a050604060e0111030901020a 75
    0x18440340d610040b60400010703100e400940c1503200c264080c02ca4010818001d02c0300a6911025100e6141408605480f2101e001c0c9915501260114020800d5540300c0c0380c0140b01c1c030980010070380c0e8407600580703d4001d550106d440c501e0046010020b40d6020f000d01c03684260040402801d6504048010b8042c05110f0300244c200111140040c010798003011510074162140012200d4141100c52200e9452402d4000381d030014041180180241030110100341c00e032135164583c4200c80080d402c114032107811590030954020300c25540000e0b080068401400654026407801d4001d14162041c589880340941c0302004001c85406081d240c4240800c01c0e07048594481081d061002c0079081100700c17401842c0d410044185002018010940c00103856a020501a81e00003140070411090608035186150450001c2d001000000c0c0c18600c1a00040307000d140042070a08942d8448000c280d064000d03410000200c2d0051003176100942e0810200c01d00d000b09007005607d88181980002e40310008503400a0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 209707374 1250 209706124 209706137
    0x70603110d020f0711010f0f0c05010b0907020d09060c0f030f02100204170f01150312050d050103150e2a0f030f010212090d0804030c0311010c030b0a0b040f0501 71
    0x20488000501101d040c0500300506540356141c90b0304003c00e0b640010001c940f40b40d0310101c0e20f04c013540903240302400c0d401103071509031000c3c41c800710a0780d031071300e0701a0216500e55840b03049140700c1d51858501d602030004e550092118100c0c1040207840808150808400e200f007a5018800290f03110656800c0c45030b1500d0902030800161b40280e00d010101c4800024580c0003181c0850303603904001e1400030b4000c0034000c803110041d68540c0a403c80d41600c104c5801948048000d0011491003001e08020030490b14285241c80210074000040701c1082e0400c0304c6c0d0b004214544500480c06000c2c02e1000382e251006071200c80b44080b907804542070300e494003072040f6079074501c0c1c401107591348600c082340450060180d8541c1c940e42c02c8124003c2d88900d410340d01c2894094003180074410002405164a0019141e444003030b151030f14180c0e4a030f0352442c4210100a05108403000861081c024002c1000982d00c002c1284040002005060056504905808107091004010040070168104119802801d010303 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 209708624 1250 209707374 209707391
    0x5121218120a1809020a0f14090405070c120e0f06090a060f090314062d070c0f0212070e09010c0801050d1103030307180b0301030803061509030a05030405090711070603 74
    0xe5400f081d2501929140e444030040004100e41c1c0ca400900b58030a0701c0c3d41e2025910410310056540060400f00404001410300c80c141c901d042a42c46036401a07542d040c46d0740e110740303983da51680140f00c8801c41c0001407500d00b1520080e00709075060440c200380854000381405a208046525825907100360030402c612080d02c1c40c815070044182001071600942201141d211040030b0366aa0902074a1610520f150704d0003170000c1401c0540702041003401c0f000840c09035182d640c0202c600b80030b060b074269003150002c1401d1006948030807030711005107481d43c0039004e031030300e000c0c8046421000208464105d0341170035150000b55a0105160781510340442c2e01130405107036801c1c03c42ca080400c2440a8041c0f000009010000b0741006c5060032000c4c40d51910140d05480d07840c030300150300003880300800b0130341c0030700200c3c1081c5001c600d00102503c48004260601114200091800b03020304d0090320f1300c2d00005001e0010b400e00d0031800780d020001e8140704518024052640d41d07500d40a124113020075581340c0740c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 209709874 1250 209708624 209708627
    0x9060b0a20190b0112030c080304020f0409060b0907110a030809070b03040b090c030c010504140d051b01021b010c03140409050106030b130b0603070507080705121218120a 75
    0x1d10054500c120844803640d240c009281d0199200000c1903d540805100014a03618001e0803190300c103900d66604040d12405594401103500060310403a88041c50f0700000c01c954071148200800783e0701a00011409035092070a008040d80050540d03401c222030355507480052140015036080490b490f240c81041035a4004c200703420040160000341e0700190010600082c020342c01d480601680c4c54609480c00c0b949681c08040d6100d601243d070a010035030070b10007005070900b0a85150b14080d00a000020b103082d95503510f03801d00d1030006920103802c00001000d809942e04200c030110115010581e4010921148006003402c115400003c040007080e86040d4450030703591081d28001c0008000602c41545c60700d8018000d0a2504441782c0518103220222090b24a54041d00c008944080c218a1031600c564500f207465510201c01a40c007640200520300c0000e00c1000b1600c108a80e040c2c0040d00c80030554841905103002600321071408180d0089410810700c0411920003515203206000d5070303452800d00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 209711124 1250 209709874 209709917
    0x5040809131d0319050301030b01031e0c08030d0b01030527030705070603050610030504030e01030218030a0c17160b030a2d110c06061e090c0d0609060b0a 68
    0x103050120404108810740003000c00000352904440403100c3c00320311380200c0f070304881602003444060310030407241c0010000b043c484407040324982e102c800e100002c05103d40302c2c4030900c81160b0089203103510004e02d000418031103101d084010a001d01c3c00b401542015494007011245501c84511803070740320518400490810001c0340e0030369034041d040d03035020307951100b0140040c02d080b00c0c2140902e03203040b105d00c0fa02d41b280c8682842180e041d00c4000d600040e190044000350040c2d2000e1304484001d0000c0e4034240d80410049444500c03944080503103a042244425104882502c48072942d0b001c03506c0b1264030b41e800c504003803e540e0200345440d101e1356482c00500c0985065203154244505030000b011102c24142003c03441c0d400b4080d414080d6280c0002d10007402d10428880345840e42096000c5080c516061a000c0d03034810320304400e1003500e911040081c04c0f14030107480c0881e100500142d0f24607108890b005544c0140000301042000a1900b0000d903900d00c5504803481c01c006140895802a0b0180407 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 209712230 1106 209711124 209711141
    0x50606010215250e1206060316030201050304150204050a030501020d0e06390c0d030b0604030b1906030506090d030501080f19170a0917010504080913 66
    0xa00801d1000729540f40303420085946422981540d84c4c14500441e0341d040c80191032641810010186060015042860001d01c19001000941c0c1c020341030304c1c1c3c401d07004a985918001d1440000d0001d01c41e135081164070804606010080c00015405041980d940384020410124004d04090341c03130340220342c03600703991000805040c0c1210400c2e040c00f40b090903c2c510110034403510310540502e500100d00030359080e4800e00d12040c241d54140920f002581c000c0d140e07145082e0a6482e64142108000c141002e9800040c2c0701c9020b01c0c40c1c6ea44032500550300072058818038140551069252981c1c2014030000a0920380081101c91001c21003400f000c18001c018114501623103020741c00c80c02800740680d404421640c41031142e00b076100041410804994a1405640c200813011035046d03c1080d240304181c2c9002c0030440040c510f007045401d41c1104a60104102c2d0082c80c808001e40300d403c = true := by decide +kernel

theorem cover : BRFrame.Cov 209532374 209712230 := by
  have h0 := BRFrame.cov_init 209532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 209532374 ≤ n) (h2 : n < 209712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
