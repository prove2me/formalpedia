-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0157
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:09:39.428919+00:00
-- url     : https://prove2.me/submissions/f95968f9-89ff-494f-b9e2-ecf736295c4f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 28057559 ≤ n < 28237415 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 28058809 1250 28057559 28057577
    0x3050709080f0c03010e0102041a090a0503070b040e01090c050a0c0303110a1709030a05040e040c0f03060e0d030c020706031508030a170606040303080a0b040e0102030109021213020a0b0703 83
    0x10303040c1840001c06070301510700905a483e507002d007411309440d40c07004104140d030310411080000b100c50b07030443e41c4c101c400801c0c500e540d41e009a0005c0d6008181343c00407130f03044c040c10f0800100680c0d10001801150000400c04103141e0761131910340b040703511204403c00407030010030034214002c1c494004004001c0c0719041c0011851000e810034450754010107406400310710040d0564102e0030303005d03120551006a001c01186030004505000300180118410b100800521801060070041c410019402038090181011002541c81c00d241e809412491383c01c070318500503480700c101421320a00440d041c40030650010301c1c1345441d2560490040c64120050b25202036600404691070a040c00205403106041e070320740c4441d0407407140b03141310303000007402c80d502c600f608000400c0040c0d00b18100b1036000044c0440010300050324000b00d03019040400200d02503510020012584805070b6001c2c141103500f18461601c256a001083d2210070101c0402951080140c2d030b00704005041c2c10700408816200340340000d21 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 28060059 1250 28058809 28058819
    0x1c060207020406030b090d0210090807020108090f01090f1101020c09060d0312090f0201020f030901140a021c020607020d050304021509130e010b0906010216060e0d0206030c1305030703050c0103050709 88
    0x1801c03400c0d0b86e000480e800452183c061941d0400c60b03c1c096940c08402000301d00c04a84d1000c040f442011002414030030360b8070000301480303000e100f20440314100000178801104c2c240752112289403103400440b4403a034140401d003107e5200048140703441d00041c01120700c41d1a08020030560060a80e0110300300081c071a10226140c0041c00390109151280c2404500004284006410508414a00c210f130380c2c01030046a000ea0b0303016142c1050707500b40c66403407680e0b025144d00407424012800070018034114174000c40210700c2c1d40054041c0c41612140d00f50344400b0b0034800b0482c2e86100555001c1e600c1010102c4580031261000020001d4580086c516204150440c05d03c0003602d14142d211011030759101c2c01c2103243d0400c2c6545640c48803003403010744410740c0f41a8444154842500824082000c107020742041c5031640d001d00a11700350018030941e107900e40400c41c841d02d5401540070072080412080700244c1c0341400110041946e0340000909616000c031070044000744001403080040007803000c030001e0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 28061309 1250 28060059 28060073
    0x4090501150807050d0b0f130f03020a05010608030a020309061305150d05070503060108070c08040515030a0617030a05032a070b0610090308090303040e090303090106051c06020702040603 82
    0x614049400000030800e40b801d6403903400c00e00540e10890042c8903824211000070204074415501002201382e101e002d441d1205401c28542840c50001c00e6810380b59600410b16070001203112900740711350003d01c007151700e450b50030b502da000310030034007000d81d00502022903e1f1400c1d030003a11a0b62090f45184590580c0c600014124200c15120301c0070308400042d4000c030f81c0c001806096409400c0d0f0904914504003480020b00510b4014420020402034800722010045030000310360090030018180d41d004044016407030040e60080d41c0d07100c201480d1000004650661942900060505002840c204050f01d101500c9550004004c0c4071814061403c0003071044c42140003c01a039080ca10303041e120303003291030420100340d80544031030300c40c404400b11040344961000600041d01c2e070080c3c069803915008030100b07180d0f019503000420b600d640b280c00c10010101c0040614840d6480100a003c040d9562040c0140a175000344503030003c3c01105a990301241d0f030391700140041d03840500001845656178443c04 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 28062559 1250 28061309 28061321
    0xc140702150904020a110c1c0f0302150a060801060503061003141f060302030d0e10030b0102010b120d02061807061409030706120b120c010e0613150f02031e0904090501 74
    0x11001c940c64044150011b14104004c40d00904261082e40410725103540e01c160b200d0601000900303041c410030305281018400d0060840f0b0010411080f80701c0e04040030382001501d07150007000400c1d0704e85140011a490000340c5540204044010700400360b0941d11840f1214480740c000a21074880e08172128123001c40c15071100b160b8002c401c4000ec02e036081d44101410f00c802444104100111540300c0009942c5039901200a5441070400003645042000143d0150a1041c0b2701c640c0640c6904504040503800b24541050480c50750030340701c10740e6805240e90b844452031179001c0080c2e40704040c14440c0c14080c0034983c903a80c8400300b40508000a03500041d180031140e400520004402d80c40c4075410004074083c500100c0012524002c4922070f840b1413507560221086910304003c00010b580d005074551004a8240c0300112030004510340e00d03402c0c80c0392146410385c500e40014140358400c9072610b2000c030940754005100704226190781050100e100040d008003180560141c0d54003013100018900740302e86 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 28063809 1250 28062559 28062577
    0x518100e010902030f01060c020a0501030b04090f06020306030f03070309030b070e040203150108010605040302030307170f03070906180305060601080403110d0903060b030102041809050325060c14070215090402 92
    0x3d6980e15001032034811810060740b01d5014005c43c51140c034016030300d07100d090040e924280381c009a18a000c2e40001c000c2d00c8120360142c410512840c52105000c03268005500c1804260101c0c5c00d13224841024550f28420a11701900103410a8014000682d00c2c40100340c0086040c900800b0b18000000082c040764026104110500d044801a0701d0a50f0030200290041c00c079410440e0400340b843d008a500d9104401004003209800860407500364480d80035a141c84da025240035803030b4540481c2c09811903000f03005501c04100c0401410f8000d001412421054030703404005801d05840300c10043d02c003d6006041103092200c0c02e5450381c1c04120801c5040110081c070343c0d17080501c45c910f05011048600400c400c9020745d0040205102000b100340e14801840c00e0a040021407103a24200306040d406401d1601000000f66120580010079041c00c2c031280381e001719420401d104180006580340080360b41c550400b060309000c03e40252409204d190062688802d46a1a02d41c4c1c0c0340008080b45c3c026006 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 28065059 1250 28063809 28063811
    0x60307090c1101060f050d150f060602150a0203011401050a02010902130603030e090915130203060703020a031a150c0102130f0e09011e180501050f011d010518100e0109 74
    0x814460702c1401d000301c800904c00452503090240c241004103003040d9100c2c0b8064400005540000c0c003200d12580002415102d0b800100b01d144d45482e002900c4034034101c880401148444007040c11103490703108480c12034500d00981c0403540c40c541d0055550f50021514882503540e80e03100754015881d0400c0318440d81200100000303400d411807070050101030400302030501a504903400c10140b4480081c000c014000d042c000c070a45135031021100314401100c1030009416004602c188198a41c040e006403000b0f200d60380741070054500c0d208190064000c005e02c215400900b0407600303090703010f840000700162512003002502d40106682500b214900310fa1015000719a0080c08001102c0c0c03010300e0030340100454000f0302121300c0a0300c40035620152444259910ba81e11216103c0c500c0301c960040e0041c0d640400244102d107000b03003426640040034443c10040c2e070a10f00800e000c00314100d02c41c0741624001012540c41d0800b65425080d460802030000000c03040c0700c1c1012038801d0760980800e00174070160344 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 28066309 1250 28065059 28065077
    0x1030503030117030c0a030e0d05030a03060e060d03020d030b010507020405090c1503010f15111c090b0c0604061505030303130201090905070206040f0302190606050f060f12060307090c 81
    0x141c03c00b00000d0680c82c0300081e0010700104d85540d401189009100d901f51400108001401d00040d00e1070384c80000007081071100040c4034034440c0c1c160304640c0480388030311f41c2c400c86546c680041c00500b10524500400680103421840180c40c00307648114440c0703c040c90942d00740321042c4d0104017220303020f076150206603110350b43c24807052501840ea031802044900500b419545401210440d00c245405240300d81c0340214412042907100e2410324a288142c0001ca680d01a041042c0120040c284290040060309013000462404045c0003102c038a40c1ca0800108cc180c2d65607100c5400034000d000448065002ca01000102e60703a0800166005484403140080c1780c0003e07100161003031000d54850040182480100421250080341c0f05600640100700901854a985400ca003001c49100e0720940d260040031060f002d00860303078440b10584070241c1c1c2c401d0b000050007080201d01e00600b04520207d020401804d007540100c461480d41144000d01107e82042d211400e540690b4242d5000e5400211410 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 28067559 1250 28066309 28066319
    0x2061801021c021903090f06050a020f07030e130501140108040501090210120f09030504060e01110f030a03050f01052b170c0d030506091305070302120a031d01020a0209060d0605010305030301 84
    0x4090001905485d04041000f03440d5075980040100280310050102607031400003075004121074045540c812880c46c9000d070f442c0c240b41b40c0a0807161303040c82202d002e0301a402c0e5108980416101d11030586507683c0e007034030f040c0c1510001120101e100400849155490340e5405006032540d01145000f03c0e11070312945a0720030444a0b100031581410343c2045114200882100400e421100301e4041c3d881c42d250030080b442440c0b0040c0c91680d04250104894452007180403d12070010002e480780d0310f0295401e20140d198810000b507800000c0c041c003030f4071203070226200c180c1e4508078242100c1005004201c0b100c0308400c2c0c80d00107a030b2455000d2411b00000004000700440014840c000c0c5130000e41c1420011400c00e41e001c9012100010426060114200c80001c04d01070200039002c01180d00900340120040500c0b406030315480c1003074040300855692040c0030844828608a603081141c1039004000c48072294080040040e406031610f03801000e0342011030041070b03e6021786030186000380000c40c0d99500d85 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 28068809 1250 28067559 28067587
    0x603060203191a01050307030b190510020a0c15020a06020d05010306060801021206060f04081b090601140a05030403090519030302060901061802130513090c120302061801021c02 78
    0x542801807525182c56004690001c40f10401d0081c05428a05652682d03141e0000b030300140003101c1c03003a034030281d03003122004a1300c2400002c3c810f881c03060b503614401c05903808003665035001c000381c0117000c0d240c00034040c0a500308901c2c01c1380b114241c6204503484042d080c0c4521b07040740d000800c0844481e0f01e950051090111034005d5500030151080214a40405d0b03107491201010080c081d05e214039000241d4143d00014141a9000761601d08140c51000c0a44a0030008508005881d03c0c020018080055400d6005901100308000e16804d51450843d211030119002e074130003001213052041080011465880740407440ca0107000600001c4841415070401a10301080145890345683c100241030041f0080448071b44107040e180343c00540c442203c2c01400d443e442e400d40201e81c01107803410181d09042855000031000c41e01036003001080c2500c5064466000c1f549110103805079100102103034102e10340d5400ba000c001849000142002a0b81e01c480b40c2401d0714130450044940c0204400b0854142c0c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 28070059 1250 28068809 28068841
    0x909010e040209010b19081f080105011a0307020615010302070b0f040c08030406020304050d020a030f03080a060f12152004260a08030705070b19050603010902030606190302040603060203 82
    0x100403201401c1600702d204846c945c0301a40449410804840041602000c10508500d885140752407212129601d07600c409008210904c2141c400c0480085000074141c02d65040340c0c06044981e015055558413000c0080481c0c0005104034100341c0c0c00c001c281d011800c8101c484d4003903519900c828145c0c0c07d280c14031002c9869690064515a001007200f00606034001089408580c000d66060a8420480c0002002c1502e981d00c0540a0f0700603100390030405a0018101c0d1141e04808030420803107841d00c0602c022405c41c1d00603d10300e403000c440108041501c0d00d038280c5019817203a8001c207408044a13840461201e1448911116420200c0d00740f21000004a410841285410044040d040403010181d070f03ca14a81c00a4402d450000103c3e05080c4190226100300750400209c504c9070904545104000f0250140d0444181c40d10000c01c800345010300503109000d80060040540d512003504110f00300f0b40341c00108040d04142080000184c6481c011340b002907002d003000580b41d10300410241c00c5410f0f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 28071309 1250 28070059 28070069
    0xd0804050f0a15180803220602060403050417010b0301060305010506180f0604050417040b1c0203061807110105090c0306100b0d11041701090201020d0302040b04120303020909010e04020901 83
    0x503034510207103c0341002140204014009240510080c0250810901d208100d40c00800e001c2c04005890200040074005001102d601c075164240c1490342c444c0c040f43c030344000b6a8014000341d0100b104005000004100d0725844a0302070001076464284030001342103c1d8154030454850351124100a000e02d408038107440d145821401d42c201905d00702c09511040c0c00010943c510442c2e682000c11305000c1c0801d092191240400c408a40d900c4c2c0f18410758109800c10720312032500d04660000d4061907200c0d8000e40e402160050805101c2051101d03284450000080c078501c02c00000c43c03200c500044090080c503000701161009015188105010301d4185040100104540f001c4d40404100310986031040b50045c00b1141800140c1c0380d8002c010309110b10035a8882480352081600e0f0036028601035208112140c401d808a84d0300701008081907090b805903101d507400c0a5030900041000c2c20011307240d003801620030700d0300518000c204000546880f0007a006114849aa0400c00085017005886a80541 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 28072559 1250 28071309 28071319
    0x305100803090d0605070c0c0308090a090b010507020f03010f0f05060a06050703020615040b090403050a020601090b0604050105030a0213180f090b010909140105010b1216050301051c020d0804050f 86
    0x61140b5000c2160490b20110041a031030399100003c1070503204803003a03000e0542c03141041c08815501c2c01d01040b150001540c0034400c1c08a003100158070740c0705210342041558107031101c80c02c090030fa800304104910714038000c0750103548620712a248101c0c944501c9140000e0303403100007480d04003842400b007c104c1581084003404410000d00001c00e40000d0810343c45000d07020b84030000c0403030ba0041000f07845200400c070780001307100080c4810150403c0182840261039400c441e19680d864010500381c2c0c21580035260000807c00003807049510a400540e400311242c0009440c11000300c117030b030340d000246500160201c1c40102a40d03840e18194024040c000c11300801c14031040882d503c42805101c010b00c0380641d5a591071400c0c000b000012194201c2c4424068000c021035a920222103409502412a600b80072904200107001c5003d80100d48030410301c00c1d6540c60035a0300f0030301800b460b08101c19454005448560070040181d50368441d4005003072241d0f030141d455178946010301c01e0790520361041901c25 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 28073809 1250 28072559 28072567
    0x16050c040603020306010b18060307120c0e10110c030f0d180501050423030d020601090c08040f060c0219030c0201030c03050f0408030a020c07080c01020c01050a0f0302030a0212070305100803 84
    0xd84e0380080e03000d040d82d40d040d0b082ca81e602460b5038005018551000c22607001440030003004041508500101c0407e002030b10300f40250107001200300c41c0d1038a01c1214a902030701501242022510a10070007142c83c0089085070318541703505000070300d40742507542c00c01d00550003924108182640042003244420285c44103d81c0d25041c200045e12902850140c6001440b10f80341d031421104480e4601d1004c40e030007a056803201091030200070b440d05005d004e04002c1506004031409858030610020b8402d58104000444e24030240d500e43c0040c10345050400114803420b403540c0710100818030a04180c0c0c4c0f190b107443d1940389071407001505840c2e604520900381458942006030024882d03503007550043d400a02c8640d260b4420800c0d000900503d03402c040f03d4803400b10080f1341c45800083c200d0184500342c00303c0342207440c103030011581449098114000161102c80f1a42414043d070051a00299940070140c1080214881900c2e0b5180031260792000075103500c180440401c1c14202107001c2d2021030301035894 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 28075059 1250 28073809 28073813
    0x40f1410021504020d020d020d030c0209090a030203030c03070903050303090706090603050c0d09020a0b0d060306052d070c060c0302030f1807050105070609060c050c0c03030a0914010309050316050c040603 90
    0xd1510040c0f01038007070000380381c020046554642c103482c03550b54010006022000c20b070400070100300b10400100e00400821011952131030300041d4401905900d44e00452a5541d40401503920790006000103050011499001c40094028000341d8071030540540180300c40e81c98000c00a10024055004409141c54001440018011441180c90025004502140540143c40866014010355014000c9100040380c40409420a90841c20882c1c1c0144000d05c00c03511800000140c011a00c50460184241201c0862403501c403460200d0b0f014565080c0658643c58a807155002e0310f480c0300082e00000e81c00020480d00e1040c03402550381090f24a50080c150400d600e036078a5548442d8003850341444000b182000c10800c5641200340407035400001440080300040340070300a608075030005096406440c203090701c1410000141d48a1620a60f02c2c030700064944043d10320042c0981d164641003541310300c04600424002c0004060382c0141200c6031007000c8240c00c05904041221101501c100c0c1443c900f000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 28076309 1250 28075059 28075093
    0xd080703080a050c042303030c010902040e03030f16210e010c0e10120b03010905010605031207020f06070516060806030c0405040b16180b070b09061306050c040f141002 74
    0x140c1c1c00300c01b0721a50440e03141c009080900b0500c00403070380c103100009001101c90019001800410310175603052081110644205842c0d00040f55042500380759600010801c000313580000c01000c4081c14001d85201c01d2018003514004c224401400c03550300c2e0200074020700000d204070094a00c0341c0ca41002100e212a00207400c5600d8044030000b0400c410850b0b10211001c0d900810388024002d00800c00c900b43c610b00207018080c107115042c0b00c0d00800c0f41c44038150300e80c00100c0d070713000c0d80c0200303103190711030a071820000590008001a01c60b4411400640a07860107000b04001800c1c25444034115807509104142c6400740314003419006a080c4400d1200003170820881c190010164441200707076a140c2c034012503440320000c4c65286001d40b4008002801c4c0311010007800d12a006049100c0355545010f0125601e902c2903c03d280400655a0780e4000b180c00c07039204641200390f440206d03142664482006060701500c1d006044000075210441c20310b860b01c0d141c546070002050018200c02401403d2840e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 28077559 1250 28076309 28076317
    0x1a040b0408090406080a050f01150b0906031b03090606100c15180512180103110702040902040b0a08010f0507020a1211010906020a030c02070501050f0d020c07050d080703080a050c 79
    0x7030401c038000c14454415a2076400560103041c01404452046400b404e0840c0d482032a4107801c0b5035540307010001400d440314802d81380c0030b84a0411405142030b19030f5050120030380c8000d1425112411140c40b005000c10f0150040d401040301000510311410440c0070401c0c11f43c040f07203000741807004007201c0e000060480611000300c0c40300d51500003005186051009084140044010400d01811030001d100110820240a10123600100c42005c0c1d800f2200641c119081e41c851102007110900070940149000c1d005480101d201030408600c10181501040010703183da0403104884e5101c030050556181c01e4814564000650302c018402845070341c80f000c0c0880403540303a140c01c000c0341150070102c5950075041040c90561200c0704555030020404010000e0500707000c1c41d0014002c1d96400181d5603c0f80c820340300500c0d0301e210610300e8141c200d180c1ca4000c0d0f00c8006005a01e0003060790000c0c807a61900707440d494040c041d07074041c1d0361040940b400a0010000030021120305240034240400c94400304169 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 28078809 1250 28077559 28077563
    0x30f170106140c0a02090c0403061505061b0705041b081005100503071407030c05060907140d060e01050901050f0a02041409060105160c08010e03030c030403180801050103030c1a040b04 81
    0x10302c3d91103400d5040036080030381200020303421040e100240800f5142000040c02182d014a4003049054210090101550b419214061313100809000c088c5510541c40036820020b050003048400566940020609071102c2940d001010f14011125401481d00101c1041e40030b0241d4440401080c1480b000600740000229010100140030000542d03140c0180700c0000c00c3d603561006161208241d2600400040f84050112464000d074004a5044140010a481a81c541c4901415400702c41018498040308400e01603c0560b01c50424044924080c8903060243c84290008101c500c1d0a2038290300810000c0c0103200010f10401003008514110b0b4161651081c003200c01d8030407511400f004031114050051880301071401701650b2010096446250340c126481d0381d0080c00520003001803580c803800100d030800540c1d40208000f60000f44680016074840400c0c00001c80070701d4485081d50b08644e8240c10460205501034441c005200031280d203d50410240381030b418040c6810781d00d0b808080c0d00a840 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 28080059 1250 28078809 28078847
    0x212120408040308030103080405040c020c011e0215090607030e0d0203090418061d0c0307140f0105040e010806040317070e010e0301020903010c1d040c090e0403020316030f170106 79
    0x3003410000d05200b00c4000f940c015108503142d503103074200102c0d5a8002d20550348039901d0a4600d110751400410020381c2c81170141c5405001101d41d401c014501e850004a060841c014203015258071500f100070b0324080c02c0d429000301300510b0800700c06801c039071a148070301c00107a202110001020758004215094000e0940d0007180342d08915988003103040552900a201c603040014521420b188000c00540d4140c0050807075041e84481e0083c10f0b11032140f809400d102c88801c01c060300f018200340c01c405481d50410314199261541d41e030b00380c0d03135400e00a03001001207405c10000e1000303056010000080001070013131280d03c6820700ca40003504d0030440b502803506003c4040b96217101981c0a605445010700c01030000e011801d90501c000b40001004040e05110940402110f11031341064030a5040c0303e645601d4092025040114066003101f009200310214402000f503222490601d901383c0313003207d2103522400715036000000007408541130340b80c0004103519600c004110103a80a11030f00c1c030517034620758 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 28081309 1250 28080059 28080061
    0x31605192a05030702030606040501050312090607050d020d0e06120a050a0608010218040614010206060105070507030f080301030311010c0503130203030d050c1201080d0509100e090f090d021212 85
    0x905100d499850015181d2010706410041d0078042c010006142d044e108a0a8601ca43e407800d08000407104203018084e09a8441d4404155140040005012030300008120b1410501e103039a91a240c5034100c4000401a00450f50040038507401800045801004451aa040c031481008402c0103003402400031001a8445010420b00406036200d02c0191014900030365584014004220328a130702d8080250180f840c0c03410004000d034440c482c0c4040e00b10142c1c0903281d141c8500b001182c00d9040040192124000c1540001c0005e0f074034840102c400d4480c0c96025181d62441c2000742c80704030b6480c404841a4101815000050390050403640e010f402051304000240290000c0792560082140c000c20192400007400001311407c00a880e101d0311107a0070040d280c1c2c940c0245616054080b94000c0816014402d01c885881c104106601d404000d00d400d002807050300001418007801580c0140065510405004100d4400c0c0051a005406400145240300307a0503501700f00b81c4900725180040c025074034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 28082559 1250 28081309 28081337
    0x12030604090807140601050a1205060604020a2007030b060301020309060403081b03090601140604030507030602031306020d0c0e0301090308010b0703021504030207080c09012102040204090c0503160519 88
    0x8802c3d079040581110036103900c9519154450f40d6200c00380a160700c00e00c4101d80003e00154a40500e6031060380c0940540540c2c2c41c0e020520029401c002c0500f014002454071008403852001c000341c01d80d039103c2e4003c202c0c3e039107141001a0264030250086000364010410080d03111400100b103500542d251a080c40b46075210f8928004140301c5084087d241c000002c2884400f2900107260f5041c1c0703a917107940d810241d121a04000c4070348528032000b413403034000074420408540c0c10b6003d580c0c468144840400c0301066659054120382c005560050740b0742d0313580551079400742e2113200c0c0035038410250000c0040500035100a04955014414004505000200c99042500c2230001c50b90500301c90303100d048207042629010307413101d50600600000307100c0ca44003581d40b8905043c2c07030b83c100c0d92514114104400c1e83d11041e00c1281c2200d0080e070b0410f408100003d265800c900c92000044815581c4a0f143e040c10301b010a8803a80c0172015408100c0d003070007034400181c5115000e401c0150345051814200584d1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 28083809 1250 28082559 28082573
    0x1e070c03030e010f090203070501050c1015050d08070b0604060b042303061003030212030c04060c0203010b100e03010609020c150a0b030319030c0f020c0d0305090a03060204050a081203060409 84
    0x142c15000415400c026800011304059009019000e10031400c4d1082c480d00c940044445000d0b50364120080e602040244118004550044242c4001c0d0626000d500740c42e240899159030408500b00c4003400006407280c14025011150340d001070f005c850600082749066003455050069001d12000354404c0c0c10700c0034085000c0085450401e2001d82550618600002c0d602002c0d0710f148400d40140c0903218540d0948a5a141142d124240c01c204d4607007002d0900e00d00710341d00500b01400320b03099940c845d81100c40740d071810070361100001181e0720300314400350080a05081d200588d021054050040c010444c01000208a2148110081c59078034500c1d82c8140022000e4182c200d98190140400a10001c400801c0d80301209840303480c0c3c40500040c816401c04440041e4060b0031100140c10100c50b101a81c031748030007040300490191401900f4440068001580c080c40303039100b1a03a20760b0000c0c0411040c1000002c0c1c000a2840d80f0262903400701340c1c00d10207130501c002898244074076a68004070f0100121 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 28085059 1250 28083809 28083821
    0x60717131110120c020601060f0806011b020310060b03100e090606040b190603020d061217030c040503070810060f060c060903050f0304060605011b02010504091104031a040b1e070c0303 81
    0xd0f540e000c1c0904044130304040e445150a01540e40080c07004048030301c46901628000f4051201a51540b401c01e03400c422102e121888204200e0341030084e0143c0f1031280605004a40103007a42c40d9081e0317502d00b0480019030783c101055002c1c3c3c80e100404801c02103043c5011903500d501c41c4c400e54012500b007005400282800d4800c05909a158041c1000407414030b6050b4007030040c000300e891741049426290300350b551036007202d140005c0101c403400c00c0d070242d0b030041d000243d0380042d40c0c4944907003000c2c1c0707880001e420308600303400001e03551f8009001c8684110160003000f0050020b2141541250b060020090518013000300182450b9150303c2c1107400c0501ca00c0440d204003811034a4282c8a040c40e03d0f1540180110340301e281c1c0058103410b0502e82401c181e84041d445668142c46051500d032501c10010058554029200750404c001d00001020418941c20b14480d1450026500002e280c00c2c5131500c0400c0c8058501402c0e0a104864001407a805480b01500070659081c0088580e8141c41c0032405410 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 28086309 1250 28085059 28085087
    0x6091506041a0a08010c080604060321050c07030302030306100f0c030e0a0e070806040b01080c07020d02030a080a020a0c140105040608100f080106031401050903070f1103060717131110 81
    0x90403400c0000e2845041d400000300c0e40d01587e82174141c0c0c480c50b041000755209804041e000407000d015011120b4400b00c51010852000d00f407842c1804d80800009041c25925401900540c20000c200004c43c90201c1e465030700d07040142400c020800c43e01200801d00c10300b43d03200406001041c016424a556201041f5001b0702204441d0140c92400c4000281400c60548105001f541019040c1d6000c0d0700a04803507216850502500d42408043e0302001900585000260b8142c0125a0a00c0c0403075031a00041c441c0e0308681d00100f10000311880e0a034a92203055100c15041b42d181c0050105907039100c002c682c212150743c5000b20080c5c40c3e02d56980340e850402d921400c1d00307240d03070300c0c00017000385064001c0c800702c074000d8618000014060303100ca0b00740d407000c0310294641d030400c05c8502c0015a001c1c90302d80000f809820417450342c585400c013081c506038050b101240411007402c00c5144c01c61005d000345600400c04040310510000351380d207050241c1e8030140140c7c800c0b0304103800801040e2007071b100200028 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 28087559 1250 28086309 28086319
    0xf0606150409050115020d09030209061c020402030a020306010206070e0609010503090309090103060b1201060e04060504050a0506040501091101020a0f1e05030d050604060b030c0d02030c0c0f0c0306091506041a 92
    0x540d44005c410440419109a400540030f000603940c3c245006100b0001142e03000781a20105603142800c2120411400a00458541c440007c04001d0b840320300c090b503c5020314247c016a0782c107209002901e000310080c01c5404000c100303424100345032242c4040c0c0d540003000b030901a032031340c50316180d50b03095000d50100c06400c4a503507000042030006641044070701c03002c1901d05080c0c004e542c0301c01500765895801071003500300c1c004021800154503a40000ea125000e6000d88014010741e580d0b503030921405403800d4840382c2d1034500640c180411103540c0c11407074009000608200a81da40e510804840c3d0740c0f00030340b40b001c0900400b640c90f041c01c204003503950390241c1540d136202c03280000034004100569256000300d1070040042151240d807000c82e401540d15040741c03404e0403802190390000c0d5000410686c0901400d2114090700b4a04100c40b0070003071070b0b40700078056806c0c20606042c0341c0341005024103080c0e484071a000f03c80099510b04544c1250b01590007040c290030b1002d8090700d80202c0b450141e048 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 28088809 1250 28087559 28087561
    0x902030f0715030623030304081f060b03060108040b0711031b06010b0c1c05040b03040b06040f0b010e040510030f030f0306060e060306060304020a05120109140f060615040905 77
    0x603010440606071900b8011260665101c0c034011811150140129401e441600c141038108502c90400d10000c40002811680b410b40c46441035418111034127100010744001001e03039029101c00780a501c018100c4100a03501f103140520001304100e41c0500054001d6031300e8000702d40c21a1040c01000741c0b200d00b030b03030480f595200500c1c3c041c42e03180d072413140b0006a40120000401c54200c418110f850004800c002020042141c0c3c1c0980082520408103000f84030080200082450b01c11f40039503c5203020703c50301c142c0d500c1c1403401c1c003050b41e001c088034145072494480101540da801000c403c41003101903c00103540c0e41c4522066036454580d030030242080020303510400425510441e0b903800503003d81e41c00d01009503648000e0718040c5440d03c00360f40c004800d000280c19810040003940c0d01600007048a01d845a0706d501140052240703c40b42c0a540c1d444884490034070203100310035512150000f000f403c0900d410400a52150805802c5500c43c6c0c40400ea15400701c00d0310426280641414501004a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 28090059 1250 28088809 28088833
    0x50d0b0603150405090a020f090703020c010603030c06051005011b05010f020c0102030916080304060f0210090c15050301050303301e061807030c050f13050f1005040315090203 77
    0x30721044000c40b284203d0034400000c81c103038070115040e403880382d028050b200c640f0480c03410040001c3d80101890101642841103100802c824003503140158002d850b81c0d82410181c0c1410000c0e03603002400090081039443d020401c0d66130268605806102c20040d00041800c1c5241003805001c4d40c4039480c1500c1c1c00070652040341c84065000314003941c0d0f0b0000301c0d000c0488980340300a03001503034410040590410f10040040c1e80c05070a1880004c07a0711700c140c650440a14805000300c0c1c5503140155100504114244025078cd441000a000341d1203040c201c2c219031400000a82e24031401c0440d1240501009c146448021805000d03031001d42d888140d90b1442c030700601c0f545603001c03c0994800c03950200da4045170141c10a0700f204109401d4a030342520fa1b83e9255142540500008400714042107401c10940c07051199100c0600503c40c0100002442c907880c0c5002c11981c402e100321a076219500f01100c400000b80c11000b140c007107070783c002d501d40c001c4aa00c03100440100b01010003c0e400d4010020b600070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 28091309 1250 28090059 28090081
    0xf0905100f1202060711030303070c0605240d020102210a09090203041a0c090d05030405030c0102030909071211030f0601170915060307090c0c120201050c0a050d0b0603 74
    0x12080100e0418062240c0e500d110600501840d0b208a00840c80c00d14084405802c04800401429004280381c1d00d0f125010000f0a00e154011101c04000840c0c1c0c1c0e101c4010004e15004154112114004c0b000c2c000d00c40340400001c03000300d01c0c81d951148581c040c00604590080c00f49401000754581c2d0802042d0098a01c0850b582c410840380380041c42250700824a12403501c2624042ca80000903200c060b00382d034201300e14100014041110b1001c080c0603130343c0166554409881414070500107591218070f410300f45480d0180446a842c15504103100c02003413a00c49240c100c4d448a814602840c00250030204c10004000f841160300f0f080400004105a8034211402180510000e9803015404094540e0006030001e056603002283e80110407061445040590301942141c4020107850107280d441032100100c4003501940300c0842c4c0b1b140092801d000704004d10240101c12070009110610780b1000484032480381c081d103d4288007020480d100c00e4180c69000e102c4840000d84615540e0034547c0683c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 28092559 1250 28091309 28091311
    0x90f06010f030507081212101a040503011d031c0b060d0509151b07170301030506070f0206040510090609020d08030a110711010f0c0501050c0307030f0209010c1b0f0905 74
    0x50362604c00da40b00010b074003000086182e0030440740d82d40d02e410a090280000711248019041c849200304914005c04e803040030346071500e4041d1440c140b8a0b52a07103040180340c00e482c0e80c0e0482c03503c6800b070080414410080441154240c0390203022442d504800c4403400030040141d03c0d100703030700010081502002003005900c0207018001d158100c030b490703c0c087c0650310000f0000300c0310080c0c4600600782000080001c013026065988c820f172003c482041c0c565284480e2604240c3c020754066105200380000c040d0040b02c2d8030b19614040c8003900461410751255592156101100743c812a1780340712800902c41e560703000c1041c40f68014442e021300209401d00200641064070442c01c0d07281ba041d01946404a07aa0466810381e901c10352010350f40001400549048000c480c4140078441d01c00b01c15800101c00b171040340d114882126400381c0300c0c2850315000f8100ca542d098086181e40c41040a40c0b0380340c0c0c00c0948601800e84c0b02c0345180c00c03400c0c91110503031100c0036503100c240035074800c0d0000b007820130841d000301e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 28093809 1250 28092559 28092563
    0x3020c2803030b030f07060f050405040e0a06110313020114070206120a0b03010c080609040201030905100207050127111306060203030a0b0102060402010804080702240901020d09051305090f06010f03 87
    0x60103121458000c04d03450b140703c40c8604100b584850020007441e80902e01200500c040d5003086400d080d915004170303090383c40400200190307810810b8803408000540c030520003100c81c0456141e041d450700185440d03041100301c2000c2e050101a0803404240089041160104c9501500701d640b1017a401781c0c0301009070829148201d015082c81001401820144126807410080780e60b8140c9584070402032185400001c1e006a0415440e0b000307a002250040040482926804c800140c3d25100b41c24100c0c00c5800b480164101c40031040c0040b07121652480781e4580e02600946408000980c0400050100148202c205142820104009000340e0040003540c031804841c0014021205c00a00490302da035402c49000707010400c0318001c200403c2c4150082d2007064409041d58017101c0d9201c58950300300b0807113000341940503030009804810b568180034051099080d814240d02c85400d18000500e030b20112821100c0b0a0754035800104500000c02115a83c800d1a400380d40055859103100445e07c5e0440c081 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 28095059 1250 28093809 28093811
    0xc0e030105160f0813060e03071101080f0402130e0601060c031b1a070306050316060e030a0b0705070302070f03030504060212040b0a0f0201020c0d0801090606020f0c0103020c280303 80
    0x81c00c6aa0382059000c40c00d1403942ea400450315030800913501c6000250020240d0079100c50003a00082c02403081e491416500300003991500c1c0540760024406903515611810040c1e2070b028040c101c90301403526034000e40d0484141e12215030380703019400142400178140403d0302c00c2c2ca0001540d1a08520744c015814080e646104127103c0703000034000303042622040240b103198144190001109005811074200101d0b1402044d4199900002450004090100c20709003580d1182008001e8202a560510200581c050300248100b91144900c8460040c906014040001480002c00d4070910881001d80601051140080d4036814024003a42180c010f15000d48241c007000e0042c500400290380890f003015191600d0012080b50849040a051484006541d0207102c54099a502880900d007460310325a03510002d07600d400d903a4410740704164403501c20340d0000c0305580c02614000c101c05460410038200941d403840d0410309107160840f60403581801e110345c100d114012300c009110300c2d44490301a42d4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 28096309 1250 28095059 28095061
    0x609110f04020f0403060b01110105040b10080109030c02010e01030e0601120204140108121303050f060610050408060c031503060405010b03010c08010e06040c0e03010204060e10080103080d0e07090c0e030105 91
    0xc2400304900c10302e00c45045582060008200041c0c041d0040060041c0600d0418204001800700f10309444040e50100c0740d600c4008200103901e041705031090018404171000b03028504294501400c0d00344c003c000a410440202617000e8140d000c0d40000c0c103941007070012502150381d00c121603051400c00c00001c078852824094a0610b103000801124140d504080107015100355000f9a5007465102a0041c90440d552140000100c0e0301400310010320010079016205174501071041002c03030030345480e2404c20300c07000b07000a000107040000c160354403007001c00d2009c0c0e13203496043c228405818207c1c005c030340c18451041004104001904413040c4d803981580280034641402e07a043d240070300c09008000b0b15080420002d0f162f40740c0b90300001c0d0b1186007400c18510413601e500100382aa80150000c1010a0662003200c440341400d0790300074001c0d00a4900034041d1350559a423550544568851a0703c03040e2500007040032204c0a000140003800c9000d03007002300c00d4141b500903246045a440301c61107946828 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 28097559 1250 28096309 28096339
    0x60305011a0603070507020d06050106030c020c01050408121b0102030403020a0b010b03040b070e040f0e030408060c0a0801170124080f06010806060607030c020d03090e09010b0604030605090a060911 87
    0x7500764080e03110010801401c544d1040001c4807580c019a40c140e1b4044141d80e41c100101d01944161400707091150742c04641458030b50000784c50408001c91690401c2410082001100404510090f480c84d94009495840d0300b1070310303e01140c0300403503010001544004180020503400140103120031b4801e400c02d080980c4d0b5400c011089004c02c8502821100004000840d110303c507040004061000070000500c0c0f0092107904801c0b102c1c82c04001240340d00000d020300c1a50010415158004107201e90141b0702201400000c0501c0b50622400031905a21101811804020f40051030100309040f40c990784801c0071582d820f0081d41500c5054000d001f65001c4082000d404602c4605854102005010b86d48401c010b001d91030b40402e9059040048031603080c00141d881c101c860400d0303402a42c4100c00141002c15402801c8009080503625030714007480004640c5030030080c1c1c1d040300d400c14000a1195079040318103090922409009040b1031824442e84100864544610300342e0400f0350b03411044861207 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 28098809 1250 28097559 28097591
    0x81908060a090e06010506030406020c0703080a0210020405150c070e240904030c021201060b04080a030906020a0507030f030519030906050705040b04030636030e06030c0d05090c0604030606030501 86
    0x3d02c0c1d103075040c2c001c4001800a8180b542c020354210f8801d060051030010118919814805560801c0354020400038246004542c10040350b5070b013801c0341400314640b40c9440001960003c00e0400c614855002160305070200700c1c10b2003004018100c1d800d030a441c80c03800c0380030342907001c583c4544600100f106442030190340c1007159000d0b209035410340302c0c1010222140c0822400203060300c14400659240d00c0003003045004d04016000905610300104500e86140c0b402070411461900440210760040d9100c030081100041c04a04903500255010482081420111610310038003c5100b4800110000001e595034154842e5040398081e40040200c0e8030348000807a00e900c60b500c070301009510207020520100c0e80561000c102d42c19030140030182c46840342c182c1c140c1a4031301444140e50300300c1e070f819a60506810050403e280d40040700d50380d240d45050303240e080d080d008d02546401e00b6544ea000086070740b0010001ea009071680206a691560342d0b80ca880710142034a030008582550070321204c14504800 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 28100059 1250 28098809 28098821
    0x30f02180406320f060402040504060909060501120201050f0904020d11130602010e070918020301060b0304150203040201050f0a09030b0a0228020d1b0206190e030c1309081908060a09 80
    0x401c03001e07604192604ea0040e800f503a4083e141c95442a42088001403036501c03440350f44001c1026071000320710a202c40c145a011500164800d4061405405041c00182e030b02008550700719035402d8116031180035117408200240645010000d01a1400540e040405020300151010b40d01c440101c0602079150f8404a007681c12060100740c0c0343d407010405100d141e0268108850860f400480c540d071000490300041c0c03d503150f0b944403052400d8000280020306c56900c1c90300c07094180c403a1b815895420103a000070441c2c46100b802880100c004502c58010500c0f07104020011504203600480074200740e40b0420003075000024054080308206481400e84595070000400f0956640150101e280320368025101011250348041d02c00c503032404003400503650300000c1c0c000c4d10740a4072446400031070700310050f00031804001024840d0b0301c01503001039581d80d01140260011380a2030302084048203841c102340305002d0905550003800e407800c6036103c156441900c8620840040f145030020070f0380d5a0a500840355 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 28101309 1250 28100059 28100141
    0x60b03150112021206130c060806010210020903010905060c1c0e0709020a021606020309040b0102031804110702090406050a05010506070c0b13030203010218090c1201030f02180406 79
    0xe60801000742c540c80100c0c0c040014000390940041600c1d0710b20b02c906000c01252070004650340c0c0300e02002805030702c000c0c1001078410f50510301000d060810001c0d5440030860002d20780d0640000d130000141e01e003904000c043c1c0751301104880f82070620795003107840f0350005203803912080c07009102c50722005813074007400b0280a4114090042503044c40b080d40082d502410b0310809510604198840d03041001c0034100084c0103540c06142c50306412001c102c155540406213034115070061014409031313003c01d294102085000c50300003421031000d299400c8940a1141c0c00303584071900404010a1114540003117216400c410400c0080f6078071041008080e0103454005400f090400a00303015000300000180304685401d4040011950b880c0c0c0001c0c00d9074401c41a2040c42e1041540545290400d0342c00c807070304803a0020101d404c000c20b01d4034401103068144009098440008800400c0d91183d11759200e00072000c01c0071820350f1910341003800141c180c00c03290101e0400440c180904601d222034080690345 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 28102559 1250 28101309 28101343
    0x806040207080403060b19080303070f031e0e070b070c0e0a060308161a0103150506040b030d0e21060103030206070203030609010905040512130812090a05060703050408060a0207060b03 81
    0x213411038650340010000800c0246d0402c210303c403403248400300001070702c5c0148010402159a0310740210000d00640003178000006240c10310440c0c0486109902d41c607040e842d080e4000085180c65060110324026181e440300c406042c00042c0e4900b84051061400c0c01d072003020070702c481aa100c82c21104103c91040c072029110300c0c0c0900c40941e11503c094a0000b13158000c1d9140514075400709021010000203030310844284191080c0142004543d0182c25803180c8122820400741c007003900425198185500410200020b4509010955031107078480b01c884500d10080d14074644503000130325035440003808150094400e01d00001e03003041c03001084a21500c4060018902139217003809190191502800031140360007110b04456943c610796010b003000303500400d44801000e02e00f80666041c603941401c0031100f00d004101103526912174a090108a0b0425121030340d946155003400c0720030340100c5d00040c0032401a4014130a41c2801500a00321031401a0b10811102e1100b070704155680c3c00c0302107407031030030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 28103809 1250 28102559 28102567
    0x307080a0305090d05030d05010902071e03020c040e030d0e03071e020a031202030c0d050405210601062111250f03110109020303030109060e0705070302030f0703210903080604020708 80
    0x16042c2441c3c050906881182264288551f05204009491098012100455000c1071000501040c68440e01214000b85103d01e212101c548000307464036034801c0c089018540f98202c056174500200f04885114140903001c0154103088080540c49500c160b4098440300e50500c0303046580c20369220502501a4002c2902045505d140c1d40d00c1a4411084142d0701507004c240042c641868003440846038101315955003d6540c0c0c181400c200d00001c2a151410300c0c4444001007582d50704000990906440719420403000c1e0b103400800314152407008041c018401800c208a42a109400c0005051014140300420442a840d9080a0901d101d90480540708240c1602d511000c64001d480951a0845580000c82d01d10b0407500482d2843e1b00070780c080c0c11160350300c1c1e00400502c3c9141d500f860f013041d11707460002d18103540c940700203540e801003414180048000083c441d003014010904044030f820f00c42d600c40d2482251032012401130000f0070040e0007003000480040d00b580342a10071280e00e42d5210350b946040c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 28105059 1250 28103809 28103827
    0x30c091909022b06080a0b040c1205010c02100b010e010e03030904140108011d0d1805040603080928140609030f06071e080c1e13050307080a0305 64
    0x41240c0494140622284100100702480540020420f560781103086940d403800c40510161484034409106a0303a503d030500500980d8030201700c5107038a980140543e50aa06c95003040e6481ea0301c0c0358040c030487c0b009412a0001c000c010742022075012981e13025100da2211303503d41c14050700c2c407007480302d4001041d1490b010880d6014850000295a007e03007164108034890021508a511201320038050b1000d8100400c8502424003074442c40041c041c40b88442d0a00c030510140c2d2341e0308801c2a10051026078485100d42a018043c4c600052900420510140b035413401c0000082d0302007000b10b809205402c1d14020508004281c0303801c0e0412621140d41c005141500c0c2d000c101481034807050f40032a00308200b9043c0e82d0200302e207003045081c240c082c200c40d04150784040e0000d1168640d1441d5115445c0c0361a161a4000c4040c80e4031038214420b031655602c061080841c0c0e10310104940f045010041000801403941b180104240c400c26401c540e100381d102c80380c0b140d503900700110050026000300303d90a0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 28106309 1250 28105059 28105069
    0xd12060e071709120c0c0a1e030807030302190905040b01020a030f110307080c0609160302030303070f0c050106030b010f05011106070f0513060201090c170601031407170d0311030c09 80
    0x40d200308001e0648202e0304805901354810f070300003101c000c21039101404c40d001600d03201c00150010a1b18946050603940d40400440d08004076100141c1245008a481b80c10f00d0f003e178044803040601d4240c0184080c400c140054908600750046a0003a0b1400300390310099400080d09a10443d01038483c4047c1c4030107010300721021000d0807010009800140501000503000a019040200c003c0010300000d2a050501500e0032072900001000b01c0000c000400168030003104498020f81c651501c80c170b0481210005580c80c03480d0000c014819860140004280089008203d050700c07000440c841d8060b683e20f004407801000c561a150031500240c001c01c0d07085002c0d20502c9041080c500b8120b0400c1c1c101d0520140641d0158401c01c0540d44501c0f1000030041c2030841240030f0108544891003100386e208503607075900014080101142030014070349042c1d81041044034004c080058411041840384910036458003050100400403d00b0020303000b00c5401034034107880c401c4070031650503418942d08e002084 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 28107559 1250 28106309 28106311
    0x30b150f070b09030a080a02090d02150304050115060e010c020d0b090607020d0e031506030a0803100801150b070308071206031110090515030408070b070302130504150b03040507080d12060e0717 85
    0x5640190b144241c2e800684441c154240310200133004682c076032034107042050a40700ca4445200c00030000c400c0610016822000001c24607500380b0384003d21401c2c030301c00300702c8820900c10098a60081d56040211400c0c0000d586403159066074240c8081c0010440180c4050508507411075240d000920403000d00749a1843c0d040d8040002403c94104009549400c22254003e03240c2e444201c150038010701a0003000d0040c09e0030040c13038501640c140d901d855510381c84d134011400000c0030400c0d00004a0f8841d48660402c90740685510300801c0107990b00d18210215404034a1042d000d00a0140384409035400b90600e02c04a480c081c2081020311a0921380c2c0003580e100400440c0d000006000041c045083c06c16960710410b0292801642c42e80d1060318100c5205083e8402c3e4441e41c101441c41034200d10301c1510008940304541301d90f45075111b61420900b03000c225040720b50311f0b21800041000e41da40c80920700550b5260314204100f00c41e140c60140301c11060465100d00465102100001a02c0d42c4003d45 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 28108809 1250 28107559 28107577
    0x1e060f060c060902060f340c030b0601030608071203020606060f040b0c190b010303200705010309030203220e0901050c040e040615080d030c08010e010303030b150f070b09030a080a02 80
    0x50303c6c2040703040700644260040c002c446c2242c0380b02d81a441c40128134401c3e840c05071010911072410304a180d44c5484034410349000c0100450101ca0114840341d019070842c0d07011b030001100303540340161a042044400d13500d4100c290014403c10b8045061740c04e0040444040c80204a001464141800f89014091b807004000c02400c0c82502c1c4804810303904c1100c5028094400c004480b8154074500b40200081c0303d01d880712688441840c03000a0040e00012607008070b035820700300403072030034405d0801b43e0440c000d03210161103007141800b29803400c0710010442c005a800840002c002900e92026440c200c540880e001c0b80d000b4401c200030b11101d5190f00360701d9030003445040c01043c0f800028541c3c0210504c540c0c482009a80320344010b10460360540030b0841b03251203516040b90298544542d0800c5a441880017809142c0c2c0c03265031680a486404030306c87d907440b19900440e502d901007005060581c0c051003060358411072401c0400c0f071418010080710540c60840e665850a510b481504030000c0d032000c018 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 28110059 1250 28108809 28108819
    0x5060313080903100e0303060907030209100e01140315040c300605060a09090c0e0306010e07030905030a02070302010f03020405181801110d0507030c05030a020c010f1e060f060c060902 81
    0xd0204e10030120700881c11601c3d8060061a2079041c0f0506000721968050000414180107104905c1217803a0701c0e00034628a900b80c900202d14a1910005139603100320381c2c1868450390f43c000308005820000d106070b2881c1070019038041004092074401101c5407503600c40c2c4a1200141480d4900b01616110000c0020100c01100068410f50b1070001803070590140c211000460410b10003001030166521803110a4011030030000c440c90b003507200081d101c4034140110754201e9000c001182c6070038400d0303000500480c0c5c82801c40341e447c00e00c250b001e569550103110880c0000d6414443d02c1c000c502c24003c0c2c6040707030405401e121400107055143d0a22400061100b07190b41010114480200803d000702510082c01c4100c2d40e96410344020841c0603510700030b01c44001e050803c4c6956001c0790f07100c02200e5100c0d80d03030440140c54800080c06e15025007801040f08400c1130400c0940c40c0040a07480d0f8030065154035810804c40d05613242c424507000025413040c200450048c46004c408580c240c1c000703240c02880140313 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 28111309 1250 28110059 28110073
    0x50903011e05060f091009090f05010c090305070801090b0f04021318030e090c040611010902090c03012904050613180b0a060804021c0201020109020a0303031505060313080903 77
    0x162040c40024880301e020805a20350061000d00e061410302040c510700180ea1500551420301044075140c2000d10414100641c1c2e00300e0042400300c00c030641c1445940c8540240125004c4000c001c0c0b00e20940d00083c1d0f600c0c011884009074006052040000c1a688598410941d54074061520524071000b4400ea030803402c5003400c049200361a1081c10444824900425080a80d0303003001411038070349001881c010340043e010300040001c110300303440480d0b0300c40c0f1707001c44105400c114090140486010003500301c500c038000e100076000d08801443c11303607040c2e0200c41100209001e03001515140b000c550320381d0980400081c0071031b003040c00050490110030540781207425500c002c01c81c941440400381c040240e0350b40031802d080b23282918074800100590b1074000034504290f0006442200c45507070707464491a00d001c0413021039000b0f401c01d0050b0380d0002d200c075042e990f83e4200580500110b900401e02184a241c0205480c0303444c2e016a13000c1d5070307030f084c2c0c030100361059503035210700c5600c03070329038240d01d4030a0f21 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 28112559 1250 28111309 28111331
    0xa060b060909160f02190b0402120f03030a23060f0102070b030901090201090602030c06070507060914010b03010e0115150201020f03010f08010501050607030e0f0402190c02150403020d0305090301 86
    0x400742d00d0056040e58858502c0e0a50350300028101c480d10079030442150070000d292408902942d088000aa421188500c2961103e10010780c1006d00c4030600b00c5607010307290b6080020a008005544101040f500a01c84c031141440780005070540c900820f14814006808504142030104080000354810700440d41a01d886844500441d001251240c10a80d155800103045581c0701e140c2500808150005600f84000210503941ba04002000780c400c0080200d6400c0c00d106264200701d10072a040344150b54100c890b400a0f0340a004500c560502a609010002d421a001445601007220100c00d894640a043c0140d140175400707502c103403d04540d001d012800c0400030a40043d40200440340e10584d4013490030030a11b003501c6050341715510514040c058034010139045600c41c046120111161020400b4100020f0003d00030f00300e561449105c0403c4036801141c1000c0032020381c50085800310300b0020a042100804d2155001c02500303c2c00368000c00d400240030b0000360a03811402000420501c0001c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 28113809 1250 28112559 28112569
    0x6040b130f1101020c12061501050403080409020d0609050f10082109040e12030901060803090d02040207060e0610030c05090601140d42051507020a03060204080106051203030601020a060b0609 84
    0x6d04103540c0340d0380048040c81180760030710b140c05d0b005070000e0030028240303441c64907030000d14001c51103401c44035900040c3d607081994156010380054400c1c0103007040641049016868444002c546114801981101c00318540e0000105d009000c035101c0014008800e29000d400c1e8070340c11803c103183e081901c900700051406d4003400440d451403604040c3c1e81c0c891074400c04250079642940c0c015061030700100400c00480d20b8220340c0e0386000382c05035000b503a110b00c1450024001d245215241605004001c2489681d22842400c007007241c0c00741207890007080d103900030402c40e40b07000e4400c64003084248090100b2a1444000f0701445612100001040020b00e849002c4000e01c0070600e03003103030a001e0629880c501070314501542c407840b80c814a0404900f40b034042038000300b4000091039200000701d0460210f5072181c0d51a80a113901a40554565985080c80b5000c0e05050154a128906041c01d000411200000b0349109000507800bc02102030591182c0000705550884981c001c1c17401c1000c1401c588030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 28115059 1250 28113809 28113829
    0x90402040909060e1204050d020d0201050c0d050d200d0905070b0406020c0901120c03020108100906080106050405130b0c031e0906040b07020a0b04081b0d0206040b130f1101020c 78
    0xc0d900104c0c00d5030440c0c81803802d201859541c0700e805d40701804203100c95140c1d03031104086150706aa020b00480c00e00d00058459016030700341d01d1500c0c8140c4108201d0103074040c003c1c18a4403e40002408144100c02800c3d2000f8141000ca00c2c03a0032090010f408c0482d800d800844409005038140d40380242c60b256111346c9544135420243c0582e000b503030b500c04281020b80700f5600400390302c181340101c5207480d135440321000805e01c40a030400c9207090201c0c40c3c10b4610a9080c0c0100302d0740c801001916641c5010034040c0c4960703c00d6510882c0341ca03000590507490600e00c280c50301e038031205100c5241e542412441c460303000a080c000941951040c42c0c00e4120030952018041c00300c0d10000d1605180500e4140c100704402801c103411034101c03142c1840028142c402c0382e03810561120400e6151220310354445250003000c4c1030308280348902c603034007021542c02203559801035014010300411039031407a10300340c050141224000c01001d43c15240301c4c08103107001c900601c00310051040d2006c00813008009158451 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 28116309 1250 28115059 28115063
    0x20a0308160c140303010509010504050402060313150c0801030b091612060615031b03020906180f03060123031c03020c010b09090f071a03010302120703060606030c080601020a05030d02090402040909 87
    0x4030010042c41607107040b0101c10300402b82181d0520945c42e166000c81c4141c00040c0181c9581405408100300700400590807900c002c100400c20170050340c40140061030748000303100035103100110b40c01055030340e600402c20200800c13248000c5103446103480701c000d10b08030200405580c1c0a0f82c464001c1544c41898000400c00640303640c021818140503458004d052403d07440500a0500c10003802130961144010344282d07074002c006510701e041090b00800e4580c502c070482990b041c0a20000410220383c19581c00c1125003070080c5040302842c12a0034156540c00f1b8210031400b461007140c292403118400e400801001c2085000854458584008030300807000644000d80a5004111070324410a41004a41c001f401c0036003105850400101c1c01c0299480107020290080010030140c01820808000b40300055070701510400041d40e466600500402010800c50300040c1b501000c01d05943c40001c643c2030075900700014500e003102c40c00c00c11000b0b41c00b1030186500a5028880020107105500c52100c100d4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 28117559 1250 28116309 28116313
    0x909071a0924040b19020c0d021c0503040902030106030203091c0206010b03090f011a040c030501030b010506090109030f050330010b1309020f040503011d07050d0303090f031e020a0308160c14 84
    0x5045c1c840a81000080c0304041e000782c5403200b201025946007000703580c1e03d014803072110760444a80d003032841c254801c07608459032a500000001038029410f030b00030b5108514100070340d81c0c0c000782a8020b001c0403482211110050f4089401405000901e00065400c06415001c50b200340c1009a21542565841c0001c04c0d084c941408148145090500880460504038503003002558195514080b5049060203181d000d04da0106940825074043d00001e005150402c032610780800451a0281d640d51242c2c0c40c04500c40707050300e80211111010910105011212101b22010fa82422a14113150700f140303500d0000c0385413030039002480d02824401441144c1d41c903075000d6030307940c00c2030305250a55440f910700e0b0740440021039820030048408941002034503421200300c2c00504050404802420b00c000700074000315202103a420030550400c1c01c41c42405800d90030703014565124042640c880d80504005000328040c82e000803050f1140070021200d405090918031181c180580b00c15401c510a091001017603 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 28118809 1250 28117559 28117597
    0x380103020405010801060f12050304050303040e010503010b0915010e03011e02040807080c01050a050f070206041211040203070504030f0503070f030503010819080a031a0909071a0924040b 82
    0x581010b01441d03000d03010350340c0241301140c81c02480284400283c410b04c0c0c108840103012508204091048030020140101202c2e200c03510703007860003400c400030711903c0c7c0300390f213440c0c0d089549040104026204090385005c0c00f405010110041d110320590603400d550655030b80200210028182c14000c2c0e4501140300b0041c2c41700d003414411464100660022041c5a000c0080800d0a0b03901804881d61099103140041d2504e41840d441e440750b00404500a40c03022000c50040707070b02054412001d6034203001e4200040717030701103040c1032004a100c00c2d5210000607900308418008104401000f00e000c0d88035104883c074118041d01ca41960412185c41180015000401007140c03260400c481495881c602c05d409480c40001e40e560f2200d0311458130144289038940300c00030351640d40d810a1402491010b08101014035041c0c1e50700380c480745240038050103041c140c03600c003c51584241c2a50310402000d0b01800050b109030442c0103034171080000b5016104010800030031802d43ca10098954400b00343c0415240c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 28120059 1250 28118809 28118813
    0x611160b07110306040803040f031107120201030c080c090d02010e04050a1d0d090e06062701021504080a0806150414010e180c0313050f0d110303040c03380103 70
    0xb10b9001091500c242d0169080c4030104110760100e0b0b40165000c0d00c050755030a5907290aa0700f005032300d01c0d4030403d40940c0800141c100001d1a00c4040e43d4802d91301000340d45401c4105840b2601e0591390340949003024401c0e40c07441d04044032502001401410002c5111103060001380503180101c034030b40c20840d21004811241c41c00308102180e40515100a000b90710303d0200c0c01030000c489442001c1101c1d00440105440d621070340b007203680c101b4800514150100b107516003040102001e00c2140d0041c07041606000e0b20131007031700030180110b511007100c03460014102c002301c82e0503a0181c00345921051025040c0319521001d00104001d140c040100c1b000d032001d02c400074090100021025008108258200b040824403400c4580d01046000c4110b48071344031030a51861940c06020000c115100e455500c001c01c1074000f400b901a00115642c50400c6e0420112480d00da0000340c3d0003e0210b83c410701e0502c0003c11403401c600e103a0003c1c8480020742c040c191844203d0302044c3c005400403118040049c02 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 28121309 1250 28120059 28120073
    0x20a14010b130f1b020307020f0103060e090106060206010504060602030702062208060906060103020901080402041a060708090310090c060f210c080c0c1203041713080c09010608010611160b07 84
    0x103441c558980a1030f05084d4a9000b035140e01c141d5400130b102c3d00301d54101401980c002c0d4842c2000e000542c071718481900e01040b685000341001d011b00d5003d0700c40d2000006a6140c03c0c001c04050707031004d0380914102240d135800c2c02641c0c0c00500d40c980e504d03403059020281080f0040110700003891510010282800d00f22185800c110000d80014109801007210403075a036008944036421640c1514002145410340540001c502e40080840f80c2c840da0008032441804259406029060320480550b003030740c904500c1c6081120000c030700082001e40440810043d06001d41c00d2220b04400f1818040c00c45075481444009203240d9160903001c3e06d5599061340034030703607110002c0707640710316007811092405403c1205140d0750040440000640c2c440000000e0801440c5146940052092440c03141c031045044000c2c1c4a580c6640102d0b0042e03c180200221a45014440c19040320900c1d15000701d240d00b414412180100c8011040503280300380c0030b0858000e040110203500070461040c1980e100d0f080e51400c08 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 28122559 1250 28121309 28121321
    0x3040c0e1308041401020a02060307050421030c0b09010b040603060f0b0a080c10030e03030108070321090b0f0c1005060f061905090d0b1e0c0307020a14010b130f 71
    0x30103090300c1248120026610b40200c4068a00340c080010100498200403454214041d0f0000e401100105c107210000e50441c0140040d24110803641c5015410006004402d441e10303400900012102c00000000c6501d4009254002200200100741c000c051401f08040d100d481c1e01c12038041350342d135801e081d000c40144944013120200f2a0309507203591901504c95500c98003824042c0c07103441d10070203107050a4020f500103507201d400e0710256612507a641d01d040762601c17031500c801ea41109480014014444194400501e2180c5035161040481d04000740319103039804c124804140031030100580c40d12840c007000b2000380340c07042a5002c12640303013441c180016407140e60225801024180404c1c000d880c000f9001c80e0140e00f051a040342c440126600089101c5140380c3c0182c81e040e2042c0601a1f400229044000107200149004155488041c00c02d00d42c1d04c421a0010016000f41e15050005602d00740c1c19a403a009070030011512000a00000c0d0105440300d540c640001e40d03910607046184504d028070 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 28123809 1250 28122559 28122571
    0x70506011a07030e060c01090c030b04020901050111061501050702031c090602030708091c1506080606010c0f0f05030c032803050906010e04020303070803010303030b04201204060e0303040c0e 84
    0x5a007800c4560750050000844144c00600c00d0340003182c421000c101c01d5210000580d040300b00350402980e68103090303202c2c01c016101640185040800402c40d03500400507041d0038904100142080d070780303401c50302445000024000341085020403da80140c0d4042295142912035154200c060143d0b203d40a0301aa1003030344024190b40013030142c41c001c03810080036149038103410b071407100d9190b010018043c00400512802071044e13004c80384510100e00c0680c00030059401c00c43c100d4080d5110f560054545412211004104031748003902e4000040c1101e141f07015035417107001140c1c180183d441d8202e0460b00400c0907440002c510484212581d200d10360340c1e28010340c55050270046810400602600e942e0140181d03079080c10301c40041400c545040084541c601d0700000d000c0d441c0d503120324006014007040d04030240300d07509115011580490b01c8244407200c0701d0512150b858180d09801e032000030070000301305071480381d81d070080d985c0302400034002144101d104190340000641880022030580708043c00c5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 28125059 1250 28123809 28123859
    0x302150a020c09090a08030604060308040305030703030f060b0403080d1b020c011e140307020703080f0405130606020304060c0309030c0824061525060f0605060306031c1407050601 79
    0x9000350080c1c00f0070f42c8800300d86c000e01126920354030170b4040f4019090940c402060300170005400020f021020000d4060a807103642c1c14491242d081403014203543d50b07402141c8900070200401c0001500400043c0f010f030580d5030000c140d080c0c0d00c140c544c240c103409010800141e0000c0c240005036691080350350708100c600c00d0381202c402a4000004007000060000c801d6203070000808982040d000b0007600005550100700555159808807810005030080e00c101c600500b4030084041a00351580a1041a075405a0003181400d25106003281d031000002d406505004800c900440400c00040c0c289000d8603203400246003c581e14600c81e0035110310000300030b80d15400c034002c0c041190b48282440a483e0302e5a00a03946844800300b400d0305924a0703901c0d48400c144141412001c01c94250098064820400c0040048994840c103014043c80200c4142d50300d0f0f0801458480505160001444460394524048110300c44080100e0420fa05c280400c4c0c402d68131002c01001540000190b440010755a100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 28126309 1250 28125059 28125061
    0x60503121207091502010b0103050a02070f0803070c05070b1210031106031806090109060b01110a060207060b03030a02060405010501050a0312030507021906060807050118030f0c0302150a020c09 85
    0x548008140110003803140201410404200701603c603250031805080d01100c0d082d60354001d00d038080d00a000311000710b4042405c0100080c000d2070b440c0700b50390740540c1080481a41200b1a42d620300315501c0105071205018040c0c1907480450402c008507800b5020708145950f5409441c1c0f00103083c0030000b80004c2440010000910000e000700b000014594011b54045840c0c0d01c03181850031803c0640c90b041d45161141d2020010104015004405410b02510341046425519801100c2d4591840a039172240d43c80920000000f410544c010201e01d8041c0b20002501408500000d045500054042005078851000c0c44284031003881480d0041500f15000290030b0f1030742e9107081c07003894803802200a150780e500018004074001d1007281c48281c0315940310038002c4110f1502a00404850203040c00038442c4142c085129402013011010007002090010308103485c59641091f0040001d41c201e0f203813654400c0000058423504824151844801c5509031907c025200c0240341840c90307000d0600c10017000d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 28127559 1250 28126309 28126333
    0xb070b0f150310050403030216060c1701060f1b0506010e07080a061805060d140d08090106120f03020102090319121d040f0603140303070f02030304080d02030916090e01060503 77
    0x900f1803061226440040f9143d640e505065009004603000002c48106c00c0b6254010801664014507451403d03803114001384d615440700800c101c0c030034000c1d600480d1440d019903581c41c5c0182240914490404000140e00c10180c2e03a09003460000c0e806100030602c4001070154154115410a0303019076801c0c002c004451a00281c401c04004440d100081e4036944c202241c544d48450701c221141580050f0100890719500340700d2913468050354004000500600d02254030003406026640445004828200c0500d403162500d03c0303040e1180c08220250b40d42001900c0d595141402140b003226480b080740e00b5144594208010074440c50001201000001c26242041d490301002007101d061099a00050400305800080001d00ca50340014040c8003800e0488060120000700440c400c0704103540b0310414081c9031000780da0301d02003968000d046400c00d00000c413001c410f550207558411103c20071505000300a410400d980ea002e60440540c041d110303990794414040074001c04c0010f281c154002c0446d0008a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 28128809 1250 28127559 28127563
    0x80607020f0a03090b220609090c09030203070303050c0a15020901091d0103080903070803121503060405060a1a0409030914010f0e0409060605060c060a1404020d030807090b070b0f1503 81
    0x15000d5400f40d0340d80421280800846c800c11195007003c95409002c0352078484101601d061107610400b04100d04186612880e14841d0300c0170811070707a000e00280b0b80c65045a40c1550b46030082d00c05003417284100400040885c00804071812140405000180d50396000d40c0014a41d00e40c0fa048841d0502614003154000192000180d04582e0030510f0641c80310b021400203400c083c066404118580301c0800e002446800c2c040589003c1c43c098801c51180c00d80038418181c03034000c2150050950b13086007001400b0041e0765003003450160400c00c05480300c41c1010000804803800418254002401d42200b03005074a55841c0d912403018007400c2108040c14a05402041c031906405035038003036071300e9020030000c001c503e4000001815006003c5501c4071101d581d42c0d41d50388400c960000900382400e00c0b031130b114000d40030410b000d10780142800d0701001c6161003c4d00d1030301000c0c11500c1004210a40040d091000c40050203850b4405c5040c840742e8107066015081c00306018168804968070340c1e607525010350340 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 28130059 1250 28128809 28128827
    0x1003020316031e0c0503011a04050a0509030706050705090901030f02090c0c0a03030e160308030405060705030105010f050a022e1401050307030b04031202030408040801230711030403060204080607020f0a03 90
    0xc03040c080a1042d07920310b007042000013140d02507a015800c00e2864a02035081024021403807101742d504110300da64007240d050661b6000c6d240d00b4242d81040200c1ca0200f5401d80045603c5407180c146203140c440380c44c2c082807014809906c140e0304a414048034004502d0404a015008980d1404031401e001ca019070040c4c552864400003400c2c1650307110380d211701d1007091040b268000d00d41032003160240e0f62401c2510340c031390046034111024060080041c00c1c00b405901901e0603a00c040c0c0d10800c4480009109072110740c40030380c0080c158424000340007000401e110780d5030260b010307031a022a03a802c1c44240140581d403040c1030400030a0800c80045c055618006009800c89030050700084054449040c207480c40c0080103514041c0c680000100418009120014001c03504584020011000031344411814036620706445201019040c3c0403c5440e44903040300c1020b13400c0c00301581e15042c1e807a41c3c0c0b2003c980c4241d1090300d1540100042014280c0c060040c4400d00c260b000c041c00400000350360003011b00c04 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 28131309 1250 28130059 28130093
    0xc14040e1605060c0f010f0b0a0806040506010302090402130e1e010b090a0c1103040303020c0109050402090906060a0203160501060f0803040305210d0e010906060603090b040b0a0b09100302031603 86
    0x12541395541d038410050141917107580b500801c031800c8092901d00103002800b10140c014100c0172800a1303501d8002500034407954010020b4030159007194208070b030725480500240e03840004640e040300140c09500c0303405003d00c421002400c02c45c43e1508101702e81704d0144042c00d2640d1502a014130542c0f5441007079580901800c0000540d4928205e040e101ea00c810202c4c1103d0303200c0800c000c4109500014012540b480980354260203c1c0c1d034104001c160320a0411168100580d10007090b02801c145020304024042030043d6400d0140d022034807100c4c000c05020640d5540e44404041120807407050b014400340094602852404d41182c650660f04d1520031340d02c0c10001c400c804400c0d008610241900c9208041c040c081c450039101d07030092400790180d44001e442007807816200080c0203000b442090003241e4400034500560341d460300c401e1414500180180102e548503005004656203000510b8030410b414000450210f0460044c146011402072003074080c03011581c010b0000c1f891084040c18000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 28132559 1250 28131309 28131319
    0x302040203060619080f0c0c0a060b0f03010f0207020f0906030d0509041b0201021810090303080c04090509060f160516030c02040501140415060503071b0c14040e1605 73
    0x145541c0c0114003d4400c01d581030340307490860307507100c03800603480341003280542501d1302c0c0c40c066926000c1d1070043d28810b4041011295000000c1100010159080900003080040816040d003035070b0800b090135190710b0f20790600120360016000c02185000c0840700d00052064804401d07a20702000400d0f034982101c5094010b00c040410030000c02d5513150040a4000c0c1200d140441c81d0360218030103030107508034108003405030b000320100b0840c82c00c2c1070f000145e01c8191030f60754404240c0755450540325454040d1040081480030080421030403064000c0a0050401c03034001c01041c07030101e401541034000901a5800901e145039644441c6a0210944042d580c4081c9001c1030701400d8642a501c0418056009410905040c00010060520544240100c2d81918144820040c0404600340c1e61100d00480300462800d10100d10703524440d10aca0036001c50705080008185c080c1c2c0e20351001c00e45560380402d007110407400307a0502c5402c040c060003081030307500740003040324080d001010490050075000d41401030b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 28133809 1250 28132559 28132561
    0x801110705070515041d1608060901050409050c0301020f0a08070203040b0712030e0a030e040c170c03070c0501140a0b010507050c010f180e040b011d0c0702040b041e0f0903090302040203 82
    0xb03c0304c0c032007150010046240d4004500c2c69045108840b0801154a040380303e021055040c43d00b401100400d100c0e402c000c1068000340e0a040400000b04201c900030785603841600d4068005880900c01000c00088201c0c4950700c82c28554001088a8002464841190000c1c841004450081c8040d28002903115011311000780c1c81e16011001080c44002d103168a105848180e014582c201b04461001b11041c1e4090040c807024010940b4841c0542d042e000c03103292040c001445080e00c0c84040e6411801500d00200c08210a80b200b9003901ea06a0460381c032103422509004040400d07200d01d0807040020f003001820302070a9119991102098842070381444210038180317800600c10380c20075240034106084001318503240d4020980d40081128100c0325226140000300b4006030341404140d040b00e540b405094565543c603c0320782c2e5900440c00c00c030b070499150565410260360b540150f4411071074400391145a44110f0007644181e031800b44000040b01d00c0d001c41e0b4000b00740d10900c686c0a494040d9409039403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 28135059 1250 28133809 28133839
    0x2040c17131205120c090d050105040c1e03020d110d020a030503030703050708010506160303020405180a060608040507090e0c1005121602101112010b03070809011814010608100608011107050705 85
    0xa02402600c008d200c2d500e0076040004024003200c4141c2a1100e515400701e000040000701600100c0f51f00001c4e51000640d443e903030029050289400062101403c02da8540c03450b80d0204130020303483d8104170b038160008820820f4031036041c401c0942c01981071501c00c078194500030108801d4400d0806814188000060700010b050207074044800402001e0401c0030f005003005202e41408006665030410141054800501c061055409034003480d008405421011b1421420b44000c0052207012081c40c003a150100706d89030b40b0301100218030340041e29116616424000d4010003404010251004805280d04004145034001032594400c0c0c4103642c0024000207144490f0030030f000c0e00301410100c220100c004207541c061003004d140128501d49030003a0640b9510b000c1ca0907070b00d030203110300e001c01b9811200c000800d607205200c019014030000001006a202c00809091074803d044804000b43c4803403007007060050074403c9134900e461030b02c051810038000c1d60304c481e2584445e22406120f10001c01c22801 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 28136309 1250 28135059 28135069
    0x20d090303110c06030702010209010306080604020f06070c080307060b0906010c080a03020f0d0903210204050609010c0204090606030c06110102210601021603030f080105040b010c02040c17131205120c09 89
    0x680d845000306500e86901c6d090800034040d52000c0c0b41280042e01302040000e104400151603030003580e00600b11071454034084140b010b90742100d80240c8401030b0800e40024800c2c414030080045501420b00881d4101c0e00340300f40720452030050032107810403505110b201c001c00c4050701a00c48075000b0785001340c0d4031680000415414002c0c030088110b040e140c480355208042d000480c940c0340300c40e45680d03440018a00b4482a0480c0254071910b50400c104100d640e10a620840076804040d100500000e02c0d810b9036101c040450ba6941c0003144c0e1003c2c42d1005101c3c1c1602300300b000d9507060540009500e4480c541040e201291018030030106002e600d5000701d601603000f8410294501c81b1192003d040c03680d2810000c010883c001040004254403c00214180c1818000c0c6080d180040e11190441c2646600713201c010f14002c015001080402010800c0b034881c040c41c2c0c2e83c020580495000350344055800c011180010703100c9008244a010000021121a1400c55951290a550500343c5554403000821 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 28137559 1250 28136309 28136323
    0x501140306240d020a120308010e01080703060b01120f050603010b06130302040b0d0b0a0b01030b12150a1814010c0206040320030d021b01140615030a1503030807020607020d09030311 80
    0x170f5108090580200d600034560708405140ca00035a20401640da81d440768001d01d02c42805040c0c01900200803e101260300c1703400240f041d00040c03400024034410203451800b101c4803071611440342c589940c10b0081c6c0340790900640381c0c8135404a0b07450b0b107408128810000010020310000307000c0c1e916088141403594480641380c3c45160040b50007201d81c0340907820007008116000b1460301080c500403003490035050001c050281289010014a0700801c84000180c458900509192446440342000800c0c080710400704010f251003041410300302c613034503030803a820b680e8400120011507000c9010000401d5200280c1c03e40d0704c02d5101203151a00c0805201801d6200d04c0030748e48040b900001d455205040c40c0a00c0101959a420080110503007501e003141e007085003aa010b903032003101c510000041d502d506009640014491800140100c0e140700d0b00341680318594410f4012440c0d403400c004840d0740620965a1121207480076180451040002401c0854207001c0941085113061a8024200c4208600 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 28138809 1250 28137559 28137563
    0x106140711030309090c0301030b010b040b0406080a0e030c0c0102060109090b13030e0a06110607020609031909030209070509011b050d0503190e0c150f0703030209060708030a0501140306240d 84
    0x71742a00e03e040d00d4902c0855100380f00840b8200c0c840307000003a2a40710f502c280c500307031241d6002c69450301e441c2c1a4100c60440001d028070303586a540b1000008004410001841031441980c0a420404262000a030030600140e114024071410b294225000480000030241d000a100ba000b603003281744d5050454660006200701030b000100f4a20102c0d4071380e0030142e03200b03c1004030811620255039000040383c454405492070085940240171450311007003409801105080b09140c01c001c43c0d95a0b03000903891180980d041c00100c0d100084444e501e580c07142c9001d0340c2e054219a00342d0702c80070030768440c1d60325410003c04c001081000b2000ca4501819407081041c2d2900b900d20900240c020404520b0b12210302e80c040030b00c2866071007620b070400040042030b100070540d0342007080e040c41c1c0340d07450a40c082d40c480c0d0009540414104200030009414001860003460444c03c005010360400300302d034140031f1801110303910a51141c0208261070144401c01d4021016200055001c0c007481001318641e05082100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 28140059 1250 28138809 28138819
    0x2010311040f080703060606020307030801050907110303040c0609150e060904060909120e0409051506010203040305100c030c090e070e0406180504050c0409080307030e070b0708120106140711030309 87
    0xb00189210740003811900f680e014940400c0160758404042e1f07a07074451144003c003c00d05a030300411040c5081c8003403d621070014148024a00007030803519066178003c49044580c0c90741c4540511210b0f83c0200c014000e0039203d55892000449014050324446850000c2032040000080d401c4840e00e0340d801076002030000b04800d02851603145082e502c0f002c58000880001b039101c000140a03840c0a01030104011b030410081c00c50070341000e1040b00241c1d001804079041d880708002c00000550100903c00349003150030b40005840d40341c03500003020b031001c40303149104000c22880c05000084405208681001d240d040c103207007160f07000020402410103680309242d01018005064100011600854440c030320a00c190bd0280400710700300004c403001c000303000d8040001840050740c44c6000781c0c003288103004050308642030180c2c1d03015a038805074486a0100c4140c54045101c4503081b106c0034000d4050122800c2c00840c0a81d40c2030142e985004047c805008840919030151540e20b040c41150442a00502 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 28141309 1250 28140059 28140089
    0x80d0f06141003050c04050d02030a080a020601030b07030c050d0b030708030a09031109040506130609021f031a03060712020c030412020a090905030a080402192306160201031104 78
    0x40d21101d03000304803402c0c015030148015680740391080c840c640c030403400110185d0409050a00340b024000c5a220100c1e050b21541a040010610f450050710a1045d01d034001c0c0406d41c12352a180c20141c00141c600001e040c208010a440160080151a48118a04400207101c46170318006071030300c5025030002202e40400a0380306602540288002c040c0c0703000344266a541403805050200c110b20440d4041d00582104004c1400d42250290b081252070140b000490090456000105d0700803520b44d50712a441c8a0010102070315805004441c094038105060209662207800403076140c0000034040f074104000c00c5d410b42e0801f07015905480c444032106080383e44503a00c41000c8228441003000503441880c08600001e81d1010743c3c011002c20310340c05805181803981b01d003401da400820107403007242e00c0300c4950302d040c03070141c0c0c5000c42a00070a00031100c40c102c4142002c0784648500e8201c0c0b03c0340100000c00011808280e401c8000000c1e56080ca00003510030b43c0032000d030b855030156070441082000020 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 28142559 1250 28141309 28141319
    0x1603030206011502120a05090a03140c040b0904050a0206160b010b09010314130f0c090c080a0e0a11060f0f040303030606020c040c0e040507090b12010305070b0301030b04080d0f06 79
    0x1d5840c1a00d29455481803200b264610503a0b58040f600710407441100200005d1010034400d8010f000b4001c806050700c04080d48070340e1841303145541024201050744c400c20125400d803400c1c0c011090512410360f1111402d0400751100741d120103442c507000c0c0c0079040014080700004e400c010141d100d150016641e0f8040c1d61210303000030855114034645800242042d115020345c03290098107c1c0100781c4002d41802d00c249607920b004252840c050f090342c80541c020000540d100c041c1c0103c0c5107101c03040c3e4400f001c5107803a1007620115023422013802115440b140506001071404075a11119402c1143c846c4c0d03d44280d0202c50140b44280301d6610840080454008109601604981300b943c5036034003541d01178045201440704942ca065541c1c400142d40e050816a01c0c10b095000e640c001c803141c540540305a84611075607401d42d01020b801d421a0184c02c0c010014481c060010b40b01410b455260240380d549180c0390149082c801038006054000c00080c12405642c103a4400091039203464401c3c000f1950310 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 28143809 1250 28142559 28142563
    0x51f020c102a0908070b040807060e130e03120c0a1403150307060f021507050a0309020a0f12050c04020a021518060a0e0c09101202030102090603040609020a06020109020d0201080916030302 83
    0x40d20030048548500b4002042c1b003a2103e05035001d650b200c000a013442450309204945c110302e03070800e0513008407503d07851015001c0907000d00003058600c60000c41d600c09840c1c41400402d50010028100328806010344010141d01400da280010804080750b03803a0344801030290130214600f1b07420340d403612a034800010081c0e00309490054400b8203800381c0c0c580800e030030080d00c0c030243e08580500000da410408510500c0c00307584105452800507100d0508240c548801410987d200e03044054290008901101004400c201c440c2d4074a90a940943c20b01680307250203940d8a07050000922508030800005051210512403103010f0040c6501711a1903080c0181e10750020101510a41e042340541480700915080440c040c9010740c0860a102090924000c030310300c000c0010000403130f032554003048500704558070750000c0c600441c011200000c0019103441049001d54982d4421001c0d641098107480240e070b0764410401c4482d030203003490340b03c9944800110741403517035400e0b2038045465103e4000c000e250f40 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 28145059 1250 28143809 28143827
    0x1502030702060115030204030b06010804080c0f030306100309020306040f05100212070e04050402090601030e030408010207060b01030e1f1505060307020a050c03070b041701060b0403051f020c102a 86
    0x144d00308003074001c4071020120b040c0d10507404083c00404c00e900108085520803290103500a00803288203080c109901c00080c14003102c00742c0312120390710100c10700ca80c03882c0004d4011003c1c030131410108400010f81c0e000c60744400c4000d202505003171546c0590420300c4414800c1c0310482507581004c5554940300c83e000401d106003954400b002400b143c0e001009402c00748a514040d6070003d01280282c2d9a400c011000350225515800e100d00090000141c424400d0004e440a603116110100784c20203280001800c170f42c001404c007070391a800913819080807000101c03940c2007080c4100d40401c0760660001461455840c1e98411504264004104100b0b160f0209020781541e21920650788010424010955900e0f514014800c0043c820041040402c0405641c0c181c0c6085040001c240b281e95141404050f8016900c150740315009006c05410325003492841e40000700d400301c0210300384400002c0c219035a102c08030700d001680b580d8600558480050f001d1070b11448a007640e03000ca06001d00d010040c40c40d69 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 28146309 1250 28145059 28145069
    0x4090603060506040903020606040f02041e1502060f04080702010512010e09070f0503120322030f0206070302070c030209090c04060b0a0908030f09090c0706060e071d01021915020307020601 83
    0xc40d01c008103c0b189414000c084000760964020140383d03c444c402c01004008100d2000103d03a4200000078420706403120f58202640c0209204441c9840c000020340b080090425000031500b0181c20440d02540303494005030400d82044155840741120b05c010380e00c41c421300110a241c0d00101c3c000103a03003000607154900c60164002995600c3e80e8980840e9090720a50042c0340c1c0c96009542c4600320f201001020b50751010349401513580e4074611828600b07480c03000800a90029070b842c1940b41e03007a501003000e40d8000c0054a400c42c80d001603030f11046080b6203039020080c80759141030046600c4060401141d01228402031041041650703805040d00d07294000140f203004160010f20024104c000401510132010b91000c03294078007c1c52100300421484000c0405a100c031050004001044080c03042e803000d440350035250011801d012038058280f1000c1c44002c02100207c20b00030780540d82c042804060303041c4043d00c000c9a01e603c0e1400e5541101d982003841e1520744040208200303d54009025030480b4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 28147559 1250 28146309 28146311
    0xa051504050d0c0203030d0f0204030f12080f06060d05091005091c020601030c0324050c0901030612030c03030c0201020903100209010305010b03010e010302011b0203061003140102040311040b030102040b0409060306 94
    0x1102c1200c05603444403043d00c0c00f0303505030424008111804070540108030000d01110005203415200c1e034800c0804909880107840c043c01c0000081103c81c0c0207203501c0c1d003108d09550301c0113080c600a000122580304080a00002c036840f034010400d100000c0111071448010718109014910f09540d002e40d81e124007040c4121100342000030700825a002042c4141643e4004108000c0d00c0e003941c90781104c010108880302000e40c05980c02d0078540d146032007214010b002c0c898109a640130352400040030b5500e207811007080c01100c0c4072131078002a000300721003038203690505012410f91040c640903402802a10900d42d0540100c05200c2e41030361560f8010004900d091b00d0412103a601c418a08040d4002401140360403d810801400507601603410711008000b48224000f44128550109080c8a03060362851103015040c0300034002c1140021135200202c8a9900850070145582c441072074004038445441c0c01183d84004440d030a0b01c0c20f4049a010380120030380c0558403a66541024003e00745072005403855 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 28148809 1250 28147559 28147573
    0x70b0702160b0c10020a090302061209070f0602060f040c1a070b010603021306030915020412030201050c030c0406031508030307181406071b0509090307060e0f06010312020a05150405 80
    0x41c0d521043c0c60040d400480105442030100380380800a40c13088010f641400780e4a1030010050396401c0c0200031403035800304410440e04000b400e00b40740081540150301c0b552101202800742950000c1d0f19580a400e54801c4141c0c1c1d10b440c1088801c40c0029001005648003c100020304074149500070b000d864800c42d0100302d00d03aa60b543c101d0488c040c010096484007000603080104078403903001034101d40d0086034444101031300400010101e9010394403580048600406281c1403680a06c03031203a000380030007109403039854804540f20040c42a4000c01e0140340e503414910890384416916103002c1c000705402c0b66620f040182000d0081c0c1030071480c0c50f0030704aa0043c041038103500c1c880c00300225040a442030381030001d9541c4190650020b2006000400d4200e400018180c0d54040840e028006a0b0045c590301c80880c141901521145401c4040a41c4501103401040c0e0001034030504481d0080342400385650340034822420807601c044050914455481c084a0203034400c0c922034003462081c0308542003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 28150059 1250 28148809 28148819
    0x302090a03150911030d02030417010209040f0e0d0f050418090f030201090b1302010203040311010302090d0605010807050901050607060c051c0b01120507170604090501020c0105060913080d02090105070b070216 92
    0x38942c0f07004081b500503001400200030108400744190203107180040090700300344001010508546070800c02034062502ea85044412200c01d024501800c0014505020208000c550107001441144650011440840c252464000c520751110101d80d61202c5204c482c0b0180c0d0070000d01030850841d0540b5101051000b045040071800850000d5a506030007550800e403458450b80d44c2e0060007818207042c55001c121250280c1d44584070040c515100d41000606c95041c40403c5141ca40c4030b400540c06103501d00c005211980e1080c080d261350f03e0780403101042e4265404030440300c6029000594132604d4149000b40840034850f0045803590100303130f07036410514038205010419280162220004070b00b01040c160f403000001e40b00b007684064090004109003090f641c4283c2260b02c121285030150350b41d1028840540340040300c3c0d03500100308655007200d012132071320349001c20300c0740c8800303e20410f074001500c07a440c0c1d0040040c1c1e511543c01121440e42c9207440c0001035140c02090040001e980164480460 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 28151309 1250 28150059 28150063
    0x6030602070b07080f040308131209030c080309010e0603060f09040602070515060105090405060102030f040602011406060903060705070f080a02010c020f0106380f1909060f0302090a0315091103 85
    0x105c80c482d640041e610603107407518159051031004d0420f04001c4607404000c1e0200b12141801c0e000440d0300d960764900e1601c3d44c141840800055003004000d42c104114803403d030380c1d203c0c2e030860031840d003101c40590b0b230384030500000c4404021201480c0c10150001c2000140000c46d8054807255008006588002165005002854000701d400c0d60200e0000e0205103001c2c145a4019503004e4410b0044038a0070a426580c2c00312500194810780c010b0b07460f1080991106010044e66400c010b0a480490405012500080c2c039884000c11308010410046042c80900004203500c20400d504130892a540e1541c640d030081c040d1001c0c2c0e40344005803051008110898a0520a106c02c41d2100c0c80040410108400900c440d0544214086c0e4078a0980ca92100c100c103550006000028103041c116690b00140c4100043d150b0203040304506000001008100e40c581248604481d256245001641c6041050010750000c4441e08050413081d0081200d88400381a030340a4110607006070210f010704480c0720b00b00740d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 28152559 1250 28151309 28151311
    0x50c01060603091a070923030c060705030a050a05090406030b0f0f09060a0f020c15190203150d0609051002250f030806030a050a0803060a0617070f020c0406030602070b0708 76
    0x181311a0034118000d03007080c00d10681941101d040d2030220682e9640e0034601024040c00f8150300c003900d4101c04000e0280c5020001c0d90340308001502d01e14200303560f940310303141c40e40035070741a803002d03c80000313001d0a040e4840c2d01103403130040300144100515905c1c3e040441c030541d0100d0380710000e18004000728200d0506100c1c003900c80d00d0310f20000c0c0400d544405801001d80034825081091030380900020301040c00506c004072170043e604401c0381491030901c010003000135501d048055054810002d00541120900c80116090390070380d8811405045445c06200034110410003612030700a020065094044580042c4030a00d1041c0d007000640300c044041104042507108010081aa103048840000b40104003280d8080401000d880100c1c200b9168141001c203290340454040340c001040040d14076056215401800c01c0303280c00426070b110b165004035640e001802d4041444040b031580c0184500c02c000240791142c01400c1440030b1030f0749191590182d00608411100c4004402c00581c1032885802d6031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 28153809 1250 28152559 28152563
    0x180504050a02011404050d14010b190317041d070306060908060411040905030301080705030d03051311041b0305060f040c0207060c021c030e12070812030a1b050c0106060309 76
    0x1e0706016120ba0300645a500d01c00f0703580624604280b000189950303605944406190003485540000e2a01903220703400c40380800700c2d0030b21840410807018201517050140301c045c1c0394002c00103200c00c0031410945001c2c0c0142e90009000781920469082008031036803481d40a1000c5480511150352505401d03911f2500d9405010207541c8150000743c04102e4401c69801061000381000034121826200c1900b140d2090304040380641c4407110810650804010243d02c81e42c2c10310f420409824003858100ba54214500003405411510320070061594a0342e01c1044080d0040c01c803458000d155400250240034220784162240340305c5803c40080703017040e00030381c015064141d0240c8201410080207803003000100d402660400603100303c05c58401400100e04240742d000e5203d008583c01c039482007000e5142c4090039249690000701c03040200c1c4800040f100440600381290036126902d05001c03100078860145e00406400d030040b1200c0c400c41d0000020000e00034403400902489882e4101902621508000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 28155059 1250 28153809 28153813
    0xc03060603250312020f07050105040b04090f0b060406090e0a020307080105060a09050a060e130b030304120602090405131a07140a020c04051807050414060f011103070302010618050405 81
    0x100d0410a030042d00840728551000c1210321502e074894032040340020020304a240507901118801c254070f034082286e00300804003407802c5440c0504120035111180174500c245800ea0303464107246140c1e450141c001445040010302000d44680c0e0354400142144007910407161078451140105502034240d000301c92280d51740d034907004942d9280030288101c581c00792031288100310320a1000704041e50303403042020046c0020340d41c0701c82a2a43c10200070881d5685006040d0003031402c0c401ca05951808400e0710101d44459200c02004002828903002a11071492003541c13092400c01000880c2d0302205450740050702864490b518000224024401c40100359404000704540020911109249c1401405132900c81e1058800c8250403c020074180c400a4070003041882c448003a80800c004208119802410215024004448290294003003800c002d04202d0043c1c80c9641291210390282542d000084c44013400c481d41c46105040084c02403400780942c1040c4500d590146480582d00d00600e40641e4000c00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 28156309 1250 28155059 28155073
    0xa0506150a09050906060406050d03021c0302040f0b18010807080c07030507050105070e01030c050703050304060b040e06010306050402040501050d0b0604240602030d06050a0e010905070e09040302030c0c03060603 93
    0x88600440400c10585a8404103001021480c96410b000742c50084a03c0402414103003040c0041006032501d07a0011070140001200b06c00200b41e001541c1400742107404800f1a803d90701401c100e01a224a03085090100040d10001a220f496840102010742d000119002c2d00c54062004403100103064441d0800246020040703611f40142400a0180301c0c42818440d04e0311455a4441e400d5500849092012400c0c03a001e55070030356014021003000401c54500a8071307044c0c0a0390050820701014001a02c615501d64100c4815111a481003640d8414a070032642d45681d0392605030068030048600b203000c3c5040c8400003816040ca0603403803000a9100c000040c4c1755a900007448020300180000d1403a1000d403080760929603070810a01c0d0007810140d80a1980c03107092561403026038060303521440c040e03400341200b004030300b04621065043d140300c20004a0345845204040340c66040390307040c040d48219030f881400704240c0c0010040111b0703801013040d140c0e01100181090346840d0212045905608070038 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 28157559 1250 28156309 28156321
    0x3020603070f0309020a03030810170d110708070305071d060a05010507150e0d1d060a051c0204060c150603150207030c080705011401090204060c08030402030c04111b0a0506 76
    0x403815940c20b01d140000d600000b680018078030380080e50050340460801001d100c4506500007000018040c1140b041025085c000e000c3c0303998004034840d001c1042940303004104041c406000131001010544201d408454407800c0031911759101e4441c052030034141c1a10001e20303100301401c0c0c40c4280c0d402014100740710301d08001034526900802007141d00c080350140c01c0c2420552403040401d040c010710007c000015450601070641c410b6000b030000301d000c0c51005140c15603a103100315804c1662034a030650f2038280390b80d14411080c2c03009409403441e03070001c540419040e600443c0d0140140c081c100e6003400d40d021507980f50441300a4003002e840d610000000900078245d80d0001d010b2644285440c1914002503100c08007960003440048a8503510b5400302c0d1000540f00703050343c0c00360401da01c04501c0c05152080c0030b4511524160000c005600c00300014007950f070184289891040702a0003400760441d0000c040300c1507070100f10b40208510200d41d03c807000450010381c08071001e60100c01010a600d80d4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 28158809 1250 28157559 28157567
    0x1d03150c090301050403050307030e060105100f050c06011206141b0c0f0318010905012105042d0b070f0c080306060f0a111504150f02090402120402190302060307 71
    0x5228100d003a00801c0081220348003413041500c203501035a100754803810a010010243da400014000190b444100188441d03079942e220b07001e94409034200360404145940055409025103240c004250184800003d25400f641c80694102072041d0700400686071103181709618010f01f0740c0c10142c3c000f510401b0355920791210008020502601080b5203016410b144441c1ca1039001a88041003d00c000032844c00355600b198180019040034201502e511312809100c000006286040e41c00040d2a0b20208080c404130400100103000048220820707804a5144202d680c03e40302011039500d86c004c030020348254400c0d40b2002c01011700d5550014146001d84822026030005400c06500510400484690b00e0085000b84180940d9840d0141a44030600c2d1050408100758254821010311004110001d01d025442841c460078901000500900f8241c40500a0094246094010b40700003900c018400103103082e94452442116105d20744c80244491502c1c501c21032000a400083c03c0c00403805407402 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 28160059 1250 28158809 28158811
    0x312041809080903010608210f0a0810050d081201080c03070b0912031201090b0f060901030203040606050307270c17040501020d050a05010e0604050408030a0b0f06191d0315 76
    0x190b4a1182407655420000707007100d001da44940803c2d880455020041c3d0407100c0280b00503154a4082030411121140c244458840c0d0320101080040102c000703401c58040b43c0510018280191110800010a160010443c0e1140c1c11000c8901540390000a0008000036071008038200500501030031454024210b00c3c5420600d1801c3d4081d040710740500400130200050000c038090040070300251351404000100b1a030a0070740c07607405210401000846074035408101c422005083c42c00581d0780c0e94504222000700419000a40d150240b48400a030746078110010300041c1d00300109a2058609a8200c902214138501032040410383c091040052411881d200d5035000c0c2c02040007524140075810721804807241240e1440c9030995840c0180b02c0f0f40d9040000c9940101c00b03890400150406d6143d42e0000d0100409410718143c50b411075980d00d071a8a2001c180700c00000e01055100d6491010711140d81c0101143c020005005540075149006148040300100e40d0140103071503100ca196001c007004440c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 28161309 1250 28160059 28160063
    0x100f0b0703021203070e1201020a080402120a060f050709090603110d03052203030e0d03090b0d180501052d01031e12030902030607030b09010e04050a020907020c0312041809 76
    0x40ca401007022040302001035101d0b40242d603074081c40c0c00d409800c200c0c8014681400e038031580e1046c02601d00041e00200202e400ce50110340c20804403903d008090715003500214000d200d582401d14003c075409240c1c018034060782482c4c6a1400c1c0700d071039015001c1182c17070903c0080d04018200d01c44403102e04041c503180030f42c00c1c06031800310324241e05591411626401c401301e440c2802031103032080003495449100d01801400413a801c4841516607280108905014094602000400200b440c0540140d5004a11b4080080f1014a41d03c803d410003034020542222800c00c0d40340702c035903a21940c14026641014981016600241030703401e60310b51460f45554040c0e00c00b860600f0014100114005803a40d01c06c14507696000300d038035490b610500d0f060030405840700c000c0c141403400984169480c2c0000505483d203401a40c90260b07601d080c003030304e044403008000c1d4004080409101a0075800300304049424010386c2180c59200c483e801c030301264441c0f44180c003900345480340780403040c0c059070300a014014 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 28162559 1250 28161309 28161313
    0x1030516020c0d03090312080403020601060e030a03030f0209040c11010f0504050303040308090c0603090a03030c09060512090a080301030f050106060f050405012105070905090604060f03020910090203041a100f0b070302 96
    0x781e00c070761f1090701d000500100c04000c00c1e07a60080004250707040200c6400b402052500c185140703581d00120382d5402000800806050301d80c4040001c42040e58152030080b000208144000c0081d070501614000a080c0c070104154240142200f402c07410b07000301c44c040c9a000d030007940b555451381c404440701c4102030290607980c0142d1744150410394070803000d1800340c0d003c540503140d0014180340180446140e214000107000280408001054001041d5098800180446281c1d40e0317900780000c0c20308000d44402040c180e03010001001f4411a600101501d500c240001c020203502c1d01c41c140c1d21b41525502d07083c00210100800d1005520820b6084c003c09841084403180c056102205019100103c4000d00001c500c2d040400951a00c440041c0d00581c06460420500e800c12407500021070b080e0101a0058403e4004507402c01c515442c04001008211001c540324109481c08140c01e458000d10110300c03c01e82c03400b18400200c81d480b18401c8032251030030502d8180c50320b41e840c052a048010154294 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 28163809 1250 28162559 28162577
    0x207060818010606050c0105100302010503070c0303110f0a1103040308040510031d0303100b16170d15030309090e060a0f0209031603022d040f0f14040201030516020c0d03 75
    0xc1c400c00d005020107003406407101e81d22103000f0340a00e0b0844400400f08260701d01030400800c00360340c110003102e400a5070340c5096800003a150405601508200c3c854a03003000d00010030702d02ca41e0444000c2c0c01c03048203556818000c0968201d82c15582d006c1c1d804058200d0408000c104030924003c030321030841050a00300400c00000d211611400c04084812038100d41e0800420412076078000c40407080138001040c9030b00e003000c2c500a075642401e0500040203000050080100340300070030310b40a80700d030b0911060040c803065612000d1525800d04a03c411000f25203d1203020030742c0042c6005001b0100381940091100740d03250f43c1d0030b0001c0c06591800a1070190708014450981e1014030000252900d402c00300403a0f02d01d9481130202e00c4005400b010018980342c003503441d140c02c10441101a1a40441d00802c070004a0010310303000f400284480c4024a140943c040305881d00c90200c2c510030340c000d88080205a032000b025501d0008040403000c0142c0008081e1451840c1c044509003000c1d01901d800c0a0f0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 28165059 1250 28163809 28163851
    0x906050f0d23040c05010903230a05060c0408010501050603011d0c0f13080c030102070c03140313031a0702071208070804090c270303080621060c04030507051002070608 74
    0x120b010600b030128641050004020502c4141e05580009110a10f0181645132554039500b550f03551000100a14424003c400da2203040200052048940c200c420b40f03285007014040a04a80d0083c0300309840c039400e00000051900d007142c241d0b412238086228041c1010b20610b440604824010300c0480690000d020416070b034541c550161181400010088100c00c2c10070b92603900d40f1000c28401c900c207070300401002002a110001001c00c590744400b002c0100c24108865a0560159086602c1d207044076650000c240441d0415540040d402603c6420450700e5140c002c0340c0324005801600d40080c0d4246218001509442c001e00c00b0500425a060500f40c807181864252a080c003103140000b803042d844c0202d03100e000e001c549202d500c00c00090020034950f580c09098000002d2000e4070a0708800d6082c070101140e14005070250160000707071401c501d0b0100b40c1e02c41c0342c2c009020a903150300c100030001c515400c060340c501c0c0341013825800526040d0301c1d14a0894008600504544000c104c02d610540 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 28166309 1250 28165059 28165091
    0xd020309120c010b0a080c1507030509130219020a0308160e0402070305031f050f100c06090c1412060a0504020a03080a080a050f04020f010509010e0913030207060906050f0d 76
    0x1d0b40e442840004103002d00000108081e40304540c0101c0944e070130035a40a0b001e6990203905514521103109020381b54030407401e00352030500903544204e4012100e041c0590412151307500601050741d091280501641c6003502c01c03a6107486a4400401003050003020840340400c0c1007000d165096107241c5520003084140c04034040c0e030403d00f030450104034040306001c42c402a11010040d01c0700803098140d0320030301e000c000403183c400d04480e190007100301c100c030b11545a20460401041a8000b82c041c80300d00110310303004c150090144200c412400000100003034034a4a1580f62100720b000d280204801e45600c032200f0010070010300101d0348980046400000a040040504104030700358491440500d451001c00060714002052241035aaa0008020040c2d4074600c0310a0501d6080c82c0c0340e0748484d4240300503140b0313041c245045039108003400c040003e411120201040201e12030b0b0f00f03941030b503592014180c40c0c412983c06a00e001c20814040c0b0010030440002034960004d43c010089041c800301104c0103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 28167559 1250 28166309 28166317
    0x10305100b041d01080a0c0b160b1e060402070c140604051801080706030606021902150408010f0b04050402010207030b04080d0606030507030e030922110408030a02010c140d02030912 80
    0x3100040c10f810703400c02035a00035600140109845809010600069030328400340c488240501c8901a00c04158030741c40c1c03030346980c1151100d68411000015410103815444101c074844030300c4020660304000041d900e00b814002d4581580c1d000c0c00e0f000266091001d06040d1811400c003443d0084000c3c03200081540d00d02c62a80c02180048050b2084e80d410103050504000c01c0303400001c10b05090000c1001016030000b40b1506043d49880d02c0103070002d061000030802c580d100f8003011000390220f004904640198810102204120740030810707102040c0500007135035012200680560000842080403900070021a1350240c822503803185001310840051040316115001880040e51315020040c0b0b907038262013454404a1400021802d02411070002a11441e40390b00c98200819a061000d4503101d1682044c80034021040080e9111078071540840c1c0d580c2c00004407400190b0034002c60100503030040340c0844400400e0310030b00e803420b42032020b03e0019610161a403502840b0b60320b40721641074070b80e82c060 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 28168809 1250 28167559 28167569
    0xf050109080a030501050105130b0903010b0301020d1401050904051e010f1404110301091205090d0c060203071e03080106030c0e1f0f02010213030f0206070609060f1a01020606010305100b04 83
    0x81d42c4034090002c00404640c0140c2000e8140701e001c00c11000c0a11407003080c41d0448032a100707520703a01e2002c00041f030302401580003a0790b055800480c1c001c411136242c0e0403400d40780e801012680641d80c0e85008000d28000242d0300a4241d0b00094840c2c2e005801403c1c41c00340d0034035190008901104041040c0084411a42d03458003240c480310103100030402c000340d048a503031200714024442082c15440307840e070000c0c1202560301800400a4007441e01d0321a0000d9020141c1c000303800e60080c5503078910180d100d9000b05001c4602c248250340d5112480d15090451440310b0701640e440751030340c0c00c100d0250010310480c1100b4042c490040900da40540e5000008511404c4c08a070b412a882120003000d451044011501b000b075900510689250190300441c5804580e000149480c4504490003c1841c6108180b400390909051003040c00c14404903802c140c80040e40110304001240f0ba002c00b00a03e4591001c4150040e0840c0c000300d0380643c03180d0040b580142c031104104100503607940001d500c49c1d10a606c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 28170059 1250 28168809 28168823
    0x40308030907031712220602031e0c0a0e0609060705060a06060e010207060806090711060c071101050708180f0a0305010b100905010807050a0219150c0e0a0509040f050109 75
    0x28410400c5000d40366904040c903041040c104140117150b50707802e03070000702505910320b1102e0500c1c071000050a030200510f03070008400c41d0ba03418007042044c4c611614151111007000700f080440e1035404003c013110001d000741d0380d0b51004424104101700c0141c0c001105a60300050170310080b80894002e018190280030100300000d8904d103403502c0a01501c1c01180745070b0564111010800c10142c100751015840b070b03822602d031210b6071f841c4082982e12203001c900a1038030344115010000c070038100758000c04446015544000c0181c0c030b00001107445126410b8000c003280c0040c08600d280c2e481d04040c00304001c1c001000d064403004500c000c01c410308202c0e40195003680d100c503090f0156040c240c00190b903500c10381c5000b980c003504100c00078191143c05080142000310019002d80014420700851444004405a03039a9641c040d02341082203d0b0740d0300407090940d140048150701c1c41e009140004c0011805050160704900d80020840e125000038020343d1038105640244000030001e203d2102c0c4503110f00300c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 28171309 1250 28170059 28170073
    0x30a03050703110406050309010e0f06011809110105090d080a020c04061202030303070f02030702031c260601050a090302090103060e06090303011a030703090209010b0406020c0411090909030403080309 88
    0x10006050380d201600035400d15103070070410404010450100c5055440c0d500300030f075480d1a100b001d58014811100c2245180c005c00c0c425480000003c2080d504071016102c41841f14886001c1d1304040303c800380801000b070724409070107103069409200500b1245000078035402071400c06441c5d00f00703d5400b5814181c0181c00c090201d8110341340602c48c50000d081410a1504000780c00c1d0b010176076a00c00504290103000d0058003d100c0325100f0811601c8880d40607003641c028204100c007aa000c996047c4d0b260300422115600b0003448581565954101100ca42e001c1d00ca54540034010b5a03907612000401003002490100403001d41c440c1e00c06607008612400002419103c0c0c13056a600b0600050404001d40d0000c100410180031000080101c3c0e035106118260f60f9201d280040e40103000c030074002034001d079050000180b1040e090000e0401c8580740c0c0c0035030341d0098000c0100030468840003442c00340458244004074035414581c04080d405248002100d2401e44c0300c0d00c540d00a600b040700c0282c7c0ca640640 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 28172559 1250 28171309 28171327
    0xc080601060207121101030506060f0a050901081531020c0703032703061a030a0308060906030a080301030609030908120405100f0e090c041205030304020306090a150506040902040e03 80
    0x2850000c00c80e643c0220030400c0c1ca035603002170b00000c11000742e04168481020901c95500c4004640d46002082201555402d00540107400e0350408a0141c3c042100c08000402c2c0021185900c9468900202026001d650304150015801400d451021503032910310401c807204811403004080307050f0380c4002000d10510394a002402610f0301500380355403000501d401e00e54994400d0b1030314103a070303800200480e00960044802240c049802140be07458410602403c0c14560001003607401940d054544440302d580e29010705550306402040240858010401000403900f45c1c4d104844042c401d10f00301c000c0a6650901910301a40d01096a02500300018200064503184ea80629007040d10300704190016810740014000504070214a40250f078400009900072040c2c404550103030a558807100d48140090500c00c0c1d89800c211000ca000c1d01c01d8030007241c60080001140c51041d81d00c0301045801240704040c10f03028003c00360019401584039210180165201d01501000132112001903071117880034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 28173809 1250 28172559 28172563
    0x10050402100302040308120712021206040b030319080a0603020301060b0a11060f0406020702010e0402030709180e0a0312090807060507020c12030f0f04030804081606050306130c0c0c0806010602 85
    0x3030071000d03050503c1044100300143d41d402c161802c403d40300ba9507800b640e03120181a41c40c025031002075104e0500c001070f02c40102e003c2c6407205001d408291002c000b2000c56409150741c9105108919040203001020740d682a4410089664400070b0300b0008251036503240d02080c05c0d21519000201d40b4580030966061081d44410f25000b5000d040000380010700741610300c2005c58001410140c01c1d079800084c43d40030b41e4012103121401c808040e02c21941c9203403810005141281a00070b0160640c0c07628840310a155607401041c01003c041005410300322403955042e1854800c140c00f800040ba00e400041c004034801101505d08103000b00710109070340c82c111000034140008615018400d00401c82c002541003800001c0d50044820144003583d82c00c0d08150b021018010769000405130320b800a40412114004a81c410350014545a5010742039100e11041d14940000c6410350741005100d494690a00d06c1500706140e0f400080c03c10780907510968440f50002801ca03003050300f240d070042004014042d81 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 28175059 1250 28173809 28173829
    0x10905010515120c070f140c030c030106080304050108130b040308040b0f041104050702010605030a05030408070f14100c0203030c0f0610030b040809031618060e1509040602090310050402 82
    0x140707042c031807801d04220b00c04444048080c09800d40b101c4040780034810402d100d00c20b86146070f00300c0601300e110034281200d01c1c3c2c0d9000f00008680240914404903a4500f0140a560180c03070100300503500f0581041e0044a041c24001c0011614241c3d19030a0800b01d18520580c9004a009a07a011041c3c5803e0a044180150150080001c040c0703400400021691520020400300400c40e80880c02c2c2d251410100d016012941115a040c000c0031043c1e010808004010310440d10800142d401c175a03035070030a81e401101188101225842d250002c0c10061a055101d5034040d03d150a0425240d103c540110f450740c0c101d030086900c41e510030b80300490700110800856070b0010a07030030b40619181c20b40d036a8040444002d00000d10001c000b05001055580071310040c82d1404c03400a5001c0c16903038905000c014109151541d2401c1403404030081091250b0a981078450095001c10084160701e800034882506002442a03030440d40c04d005d5034450740c0d01031044001c2100200c174041080e08040c0100000d01c0300d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 28176309 1250 28175059 28175089
    0xb150702090f01060f0e1f090801060801110d020c01020f030703050405070801110703180518040c0b0301030309150c17280f0c0c0f0b0a081b040909020112050109050105 74
    0x2804200420801d41e000010070300c3d2170014580f010350041c502c03020500c00711401e040c2000d08074140c3d07040c88030594005200300c01c98140200a0001590300e04240c0c1c00c036070b540011060241000c0000d0000050b09030028848080c400300014030b807055600c1302034007681094409000084c1c4820500c41400b4040215801404184008100800f0280c4503640f9611402e00002e0a001d1120001641d644e05940282d00030320001c0c0041c00c0510a03410000c4005404039000c94400403c4a404621014501c0a03281079941c0b5440c1c440304282022070812980a0b410030f00c00030003503000301283c0000c1c02e03104d440b00d26982840300d494a40045100303c50450781000c0494000c42c142c41031601250380d0010005180210342d0620b43d0032141e45080c18901c440c410380098100341071140c0d00007100b40440d801010f1031001550f41c030080d0385034107105583e19560524007000d00348007030000348803080e000c0e070245450510504046078403410f4001103000351403099012062150351000100305604007107010b8002d202d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 28177559 1250 28176309 28176331
    0x5070815010305060a1208040306060e04120e010e0105220b0a0f0203090f060705070b0304050a02040b12060106050a0909060b0c240a110904020705010b01110106030c050f040b15070209 81
    0x32408101040c1200078510406c0c9516000c41401401c0c801150304031806540c0103041804490b8496012042e0030300151411910503003100300300c6160300e2040703a0091020105035034001d0503200c00c1004680d00d8000c1001241d807d484403c0c42c40d180014015010001c1c01580401070301c441400d280903110131301e0100201e056402c1003101c5d811647d1001d4100511000c221071054076074185041091070005260064546100000284400e000c000550032090610840d0240550402a030522100e101650000b0807035621140040c001c490084002c0c2c450a009032800f1400070350743e0408032054445c2984918107a9400045071004503c007400500a0ba03c01103103902110042c03004d095030f1505000b1308842c089961107003008010302e001d004861440f0707401041507481d82464284207000700401c1c040359021070048100291554810700840e4100c90f040101804064170745410b014888050451080d44190341f05284202992000c8460b6000c40000d1300a0352940c030248103201d030640010303000d52151703 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 28178809 1250 28177559 28177561
    0x40e03040b16050a0c091406220905160608040606050f03030403080c03070605090d020d0e01020a020f03030405040501030b0a0501060315050f010c05030a0e091f03120c0605070815010305 82
    0x8058441214982000c10b06506003907074030350a00034100440c0180c010415080d1400009480300f064010001c604081400300c0444d071941c80030440404800c01721079900c1c030050428002d0071030040d88990020382c040d10954026070182108004e8400740d5410500100b0060001c0c00180103140c460000070b40016200c00001411a100181c0c2c0c2c0d008605c402001d015002546a081848c20b00582d03601c194064801c0c06a400c00d04103181d198994201d03298014451541840d101600c05e80c40c02c0310003001a00540102c511903003c0c044092034101e0980c0d0580300c00c000005280d1150f04c00c45000718007500c40304a8600f0402810701c19504180d0041041506001d07045000d22050705941d0b00f283ca080756880414004180140c55802207194098003500001c03500c07801c55074000060601e840b13011200b40b1859030344c0341d41d103605042e51404001c000160002c2e00744006400076004074180c08060800101e501c0b000e644400c10b03204100e6650f0b000410f15401d000b42e180880402c80407001d02400c05201e2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 28180059 1250 28178809 28178819
    0xd0f0b040e0c0d060605030715020609010b011215051228030206010612090614070906090b04050d140a03020a021f0f0305060402090603041b0b1303020d021309050705040e0304 77
    0x2e6146240c030300c14071070580340029008210b401c4d131080000b81800390036240c40395515141c81d0f800c02c59801003103000d40608800102c0010042c030540c4406c140513102e02e00b0b42071800c01c0450007030000301c41d00f0306a80400080410700e1f59030384141c1406801c2caa002008054400a0781f11002c5c60a40f4031041c0b0003018403603520000b40c01040c2541545c1d907920b858442d892000d0004406041c107404060308040c81c0c2959942040100c0f06103c0c85240c160b195148180e80d070303030000c03106001c0b584950400c0660512040c452490700b0082440c207540180b04261403004d122110030b00b421780210040300580c0c4014082411406e0080310138040c440c8c1c201a0b000700d020541c1c1d024110340d0000c4902c604042d5590300085050395a40e055941c1000090181a104e1426180240a51003060507502c03c9400c0007000180d010544000c440000a00500c0e145c00742d071560303003030040d00607042c0c10407a4008039020703041261441c0e1744a290800b900a10040c0045458141480221290b6a0007480c07150010170007800 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 28181309 1250 28180059 28180063
    0xc0f1502030f09062a0d090602070f0513110d09031209020f22020a02060105031b060706020d0207061a0907020601060e2101020301060513051804110d0203030d0f0b040e 74
    0x682000075138100c0e40d162440120200b0f801c0b070074000c40f06030000307185540829003c00144111414181c1e2640810162144d0701640e442c0358622420f003070b0501040050155080120203500100380400000c1014246c4034100491031b0046c1c550909441e95800c203080915610600c103c4c52842c103000e082244e0340782a00810b1400319050b08550248648082d0301c04c405061103242c1103030708000c41045403502d02c11500251148002c1c071446d4402d21a04c8a07440001004007000c65034800014255450a01c5681d1001e001e900300343d0b0550881076003809442c0c08558240144464a0211170035140202060401c1280c0d50740050660f8045600050041c0001908160340d2071100f003080b0b51181c03451141440c4140103000101e910b04955001200000d500e03908140500480d5001c203016140540d1a00180466060307810b420381c0e00380c42d140010401080c4801c0b00504a08000b0700940074492154021900e541e100c40140000740da0740390341e00984603016202e00703200c48400304c40070301056400e0850740b9 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 28182559 1250 28181309 28181317
    0x8060618060304050c060c07060201050c0c033c07060f1407050906071a0601021207030203030f07030e0604030e0a1e14010504030507030c051503060d060f02070c0f1502030f 76
    0x16000d440700001180500208011081010b20000c0c860356865801c000c081d81c4612462144c007001d0360820010540c204082402c0c1c9410081d6a0000c1d0700b403a0400542c1d100320019246a90745000c0d40c08120505040404d00d5141c0a820717810185030346d9400c1c0c0c60541d044401e00b00078014800d2905105040307400322403d00540107001854035070b03180c214810001e0094450514010000301603030624405081801d090544100426026a452510b030924000510b01c03031150014010380003000020584820600a0f80e04a02103150006050170100102403070820241c0302a00031500c0402101c0c521b00d440040341018240005c030b00900c1d59100031910662a1060041748000d050541720202640d04c41d5003910015500101105c95141d901c0c2080078900d01203008841c0034846510b030120700d000301003040703a02070340300502440c9250901d41c07600001800c900e1404e2180b29000c0008202040901c048034000d40122592030700d446140c100d0f441c000c00a030048220079034000f4000404c40881758000e803 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 28183809 1250 28182559 28182607
    0x3020405060f1207030221030d11040806150a090e0318180406050604050a180f05010213060306080c0f06040905220302010b01020106081b010c0816030c03080606 71
    0x2180584a6000103102d40901212064001c02520180442000c0020301603041302e000360384199a00802c1e0982d020081503500702d0301d805e50310800403c4031404076a400b0700e0005000749103460820380c80c0c004032410310b4015100026004000a20a1030034a00b2b003c0350401400c000c44104010180d504941e51a40600d010540074105491154800d58940c1984119800b409460750074003460301d841d10b00700414050f1002c41c095480e101c00902d00d420144100140c01003650110001881d10340d03030700e03410380700000d00880d0555001c2c885500f507541058640c001815240c0c0300420002d091200480c40d1050801500e032181400860800907030b150f00080310140c4810010114880d510407011f111703803180c4020041d421a00f104204402c1c19419030212000c0b00c000d034024019155241c4c0b805941e5081d88204001c044007088881590b98041c94100c9508c1c1d21490b005814030502d00d584250342e82840c070003a40842c152050030030805a1110350f40d58800022515a03040050301887c0303036072600402c0f0f11 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 28185059 1250 28183809 28183811
    0x503151504140109061202060301050d031205090f1203040c0510051e030a23010504020c01060509070801030507060305090604030e03030c100f06120b0c070314030c03100905070207030204 82
    0x8680c03544815081500000340160040c004011031540740402034a092140e41d50951070042c012403c0c01d81071404140703003500285000c1c00c1d64240020014400d590b0310088040c00b45142025092a120b17024852107007800c0e00140c03401e021080055400e0a4420440c0100010200104800a81100700d0442650400e84120070000d071001d01c01d42c3e0a203d041c10800b01c2d0460742c0358443d168102c10005512031030050406002c0c0342d0b06000202c446070649140c51000f41005401401181020b40c05404460324041c00441d01a56500c00b0a803034403c2030312190000345032100103109015042081900405091030100520710386040c45940751040544010f0801001c0b002c4104c01e95400c10036141d80440c450269511030030007820110052118074001d40c031442c20841d0004010040840d10400c50360040c2c3c0c11080703a6110b5040748001d034401c502c110280300030003000070341c3e4850507400355100d01c1b40d0010a070360f03a080208541004400d03139400110a17078184420406860303400b20708501100e606440c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 28186309 1250 28185059 28185061
    0x1306080910110a0e0f090a02130302130501051903050606010521070309020411070507030b0a02040e0403020d021e0a120201020d020703031a03060601090e040201090e040308160801050315 82
    0x46031424440404054a80719051102e0b600d11a40140024007000c50759494001111403180d090080e400312504280d07030701400a2002465102c01c50700180301235441e8400b16011192258001280040c0035411200e4076039855005000d142852072440c054141c201180102e100d140d542c87d107070384a41c010500b504210001c261503061080c5c580d850791001c0386042c1d6030500c074500010020004e10010b007050b4030550500d0604441000c20384110740c41c80d604200a051400e0840d252035804034405882d503a44903500b00710001b80014002d031078500a511a502502c90102d226100900e800400350018481004040d446180071000242034102d2680c01000e2101e41d400440c4280d009001d030b8110680041d000240110405074194001150a03440343c24403060500010107161396a042100c1c0c10340803c50008042c0120b1140324003840d4480e10503d000841c81c0d451703510742083c0e9103042d2011400708004d00240004500898210b02d80381c0c88501e031a4005626050000e0740d1000c44407401c0310b409000e48 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 28187559 1250 28186309 28186321
    0xc1d01060f0c0206120403120e07050906031c020307060608070506040302010305100305010606050a080109060b1c06030c090b120f1009050a0f0323070534090203060f06130608 77
    0x24007611210b0b6001403845886441490040a14010403901180000c100c0f000001101c1044c1c45184000e491440c0145401c50a10091059031140640600c1e898860554422220b0000c40c1c5441140c4000c2c0d400345840b60320341d2030301006481c03451b0090b0700d403a0440c010610954603000261001c9336024603020505485110300200092403c3d00040c2c002e5007801c002140c802c4d040700041249080550710b01c681e0761ba0782c04602003240c182d03002c0d0b0134039803101700700e1000c8983e440b40100c096001821302c0080c0c0303240c1e00c0d920005001415440101020384460494065282401c580210340b000c0101624681d40d49031000c548881c0c3c0200c58441c02035075540914284030f010052444405d0b44002c0c5418508000c0c2006044402041740c0311002e9000c81c800c4e6092200f45005540810358004010700800350102001c022030820841300e051801c2c0c04000c5888079480b04074642d0000c0001040041e603a05040733042c4180f2084801e0864081e000801c04c2d03103241441c50400c1000c68070790745841513403500c1e00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 28188809 1250 28187559 28187567
    0x100c12090f06111e0306090c0306030f0106080610060e031213050303040b0c0601060f05040306200703090f08030906090607080f0304142b03050c090a0f030c1d01060f 73
    0x8800c01800840c0303800c2c10440340c81c04020081210700c00307160300140000a910004c5500c0e20003101e03a160400101800708003035a081c400a1a0044802000e41d41c40800c0c519406085406640c8010641d9100e20107004001f1801c0f4a1800a004030745480d10b00d2070101d5000c179035180c81c0c402e01c2d1056030300c0015036070030020102103403c00a088000d0a0f02d076166907032003035054150401211a441801010000030340980100f5201070381030459101c3c2c1d030810780346d510f440b0010050812100b4524400d038499860407189800200720440c800d807250800c0b90300305868030030304c10280d07040780b001b40c0d00402c004011955400c0c00d4409014007111125a90b861500d000e031064040d00030440d0300319102009000030050200002d07581215203404072030782c40059405d4004125001031003006d10580d1210102c2801d0702c03d4104a500c041810040d0345801c914801080c2c5007400d56000405101594005204100c1d0b050030f10380003040100d504481001c0c6024180203000018840c0b6814043c0c0e020300d0030308003805 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 28190059 1250 28188809 28188833
    0x303020d020a05120108150f070203070606080a15110717070c0f03140d0c0305070507050307082a010e01110109021e010329120708030d060503100c1209 67
    0x140c804290346911803820b018010390452094100100380000000c611706c5030002c0c2075940c681ca100e0700d0301d003103817200c2c040d5100c2048083c1010046000401180b00030800a01a03200100000b20040c10301c0d43c1e1600380030210054101c0e05001c1e19082860303403800711040b401a90003240e00019802d1500800018a02503481251002804020700c002d0014450500100d000b00b203c3c004c0c10b00c1903440540c500d00795100e000d071114036004145056201008284902e0282008500c00c0f011140456102c0300040d107415401d0b484180c0690040354002401c03042041080080c02d140751406c800340d0f4010002807c0450501c51340350400a041c0500390b41420b094004004054024042001c190300d06c0d03414034840c3e110b000740c00b40445d0400800c0e9200c20740c0e9030381d0300b410400090740c80680601034800f0000d0350b02000340c601d03440c4c0c8502440814043c50a000511510b8685040020380c036150100345414031b2440f240020030286401001410190083c00d000e80e00072466100141c01d420602e403c41c1c03807500c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 28191309 1250 28190059 28190077
    0xe03010204030b0a0b1009060f0e030a0b280504051509030d02030901020a0e031615020c121608070b03040b07050c0a050703020f0409020a0e0601020a080d09020f09070516030302 78
    0x100c01e424400071134890340c880251140709a40001510743c0c10300301035600c03074500c0c41248000f54441108500c9070f84180d120740280c410080984044510b0394486d41c2803000296200f01e800c0265a9518036000d1b0402c0d40301b00b41d43d800c0310b8203106c1c03440c150701c4054885203c80c2448480c0700c6114000b0744108000d00856205214604c821503c030304000c20b1182c000c1d0048200302c000f184645140704c400e0304c5e00085541e2000401c032096100b01d421300110600511900c0d49240541c4511981c62000355035481c070154003619000024200c0c1c102d40810000507818507402000765421114003400340c0001031040f00d61094024080c1075031500c030140c04071018410101d8a030f18a00076940124200000451201c040341e000300c5108030b1002c138071410007003160140c030802503010050132002c0241260f107240030341d03203e42d05005036680b4052075186e180c040d51004600e0788401e0b5a41a0607000c40c034000c010902d503558140e80c850380074a051100a003484c407a80180000741e90344402e9070020144207030100c0f840c0c85 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 28192559 1250 28191309 28191323
    0x9060a030207170901020706030e0c010c050c060a0309050c010e100302090f0a0602010c080a06061d040605040501030f1403091c020f061903060b0702030705090c040506190219050c010e0301020403 86
    0x1e9000240c000064000c1c1e40498011f002d00c940c0080d10510901803014603112510151500360300c178a005507020103691724125014021445104019990b00340505103480d0941c42c045400e449618000d0304000c01040c4241c1480200b029070041501d0319050040c28440c54200180d07174040b000e0004070080980c44295038003444000c00801c00c0c43e810b401400544c2e090b511111004d840e1542c01c40d0a40311180135110001c2c10f402e0811200d00140c684040a181d009000003c6040c2c541001c0f8050311000d80080d034031843e07a0602c030000c00a0510642521007444405541400917040010302c884c28150810343d0103807000080c4030203660741c0038424048054001c2075607a4442e168a90154081d0b50b41c0c0307202d00400c0c90000e0000d0001c1c0c203081110070150307000300589170841c10f100400440c0c02c1d014001108030401804003188a88401c402800e4008807403000d91400141080002c3c581940a0600d0401e0007842e4441e20000d02c0c0020454420f070804d09005001d46d00c03420110340213000d5903202608803 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 28193809 1250 28192559 28192583
    0x7230c06041a07020c01051905040803030a0605090f04030903020409030509040e210f1909090603150b18010b1c150503060606030412080408040902070c14040c0509060a030207 77
    0x2260100c62080b0241c2002e580c50203d80c0c0d240341c20b07626038600c5030134180030400c02c1240c000340800e40000343c0d0040d80309091031400c00c0c2e101c40c03840385540c0088440000b8940d031062b080c0074910b000008036034802c01c00c401c0c18041c2e141c244c0d401040305c00c6900c07009000c1c07a00d65410204043c000d4080d2110703160040e004010003122400c460360784100800300c22008900052100c07120500440c00c0307880102070310b0f0b45603107450384c161039019110034070503800001c03c600b0032030110f0300709058028600154001e0400400caa120b602d0444201c0d4085091180b04d40402e4042c85140d41540c4901811a407089c07040a40392012025030300780342c4050a68104065143c6021080300b80b03010071580b000c0c0c1e00d06034222130040d5184000e200080c8400d48000c0d00c0f0f8400c0d040e407180000d00c01c090142d4024414640141801d036105c020000b03a8201c0c040c21540c40d60b501c072080c0a10540c00d00b403121002801c40c0d05105400c00d5100107049132141188d214080d034800035a0030505401b03130b01182c03181580074030300341a8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 28195059 1250 28193809 28193813
    0x22031101140402130903050304080919081606050703021c030f020f0711010c03020a0609030207030803070203030a05060102010204120305030a020c030c0f060a05071d0406180906060e07230c0604 85
    0x1401c94102c8003207124000c44410400400b0252143d1060789a1640314a8a141c0300c0e80c843e000703290440a0002e0b07108480c4400d01c2006000e29100d1070040c40520004d0411b80311541044000a400390800410080306119000100ea40001c046942031101510723032212412220089000d442d015001c076030040c0c000540d0750034a42040008001e842d006203522039105662030300444580030030b0300004c2d0041c2e000c1560f14011800c40d510110309540b09004580c0c030240c0c0c944d2000b525400443d140d2015820110421100142a0040e10350080091008520305404d25a20700030030f090340b0b00040c04210780840011802c40c0c5c50380c121038048000030100d070340359041d41d00c2e0565140480300074a8050b000c0e01003c200c4000240c0a02c500800390750726038540b0000f0310101500b00410130801d0f541c0c0161280e40004210301003000b00c90001095400c0400d54220a0420302c05840e20383d4400101407003c0410000b000790f10004142035040c00080c914000d4660000d0741c1942c1c062031412080b940190400d0000b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 28196309 1250 28195059 28195091
    0x1005100c02010201051005061b03070f030f1e020d110c0303070f021e060d0902040b040504030908070f0b0906031b0f0a09080a0506010e060604080604050d1722031101 73
    0x2203a100b40e000340700c01d0790384641041c80d028031480780ca03404ca8014800e044134041344130202d03040101420205ca081511645a42010480701750064000c94902d041160342250300507448150380e1822020b0548070302c2102002540c428401204000700810807150303074036991007480804c0350a10001c04407a2160990f0034060005d080100c401ca1044002c4041030403c2d284d100510007000300c0081226041c020040000070180c8081070b02240e010740d452001c044541e07a40d2041500640c065a11090b80906040d200c03840e10700c85403c800c611090f02001041000c064000302c4854407002e0760601d4480c2c40700b0392449550342003046408501040819036000351080c000140c20030000700e41e45d20304001c0c2d80740a020b84030300c80d248024225401c0b5100605c44c0300b890302d0f403650708020041c210619140da00c041d16414080300380d5003218103404c100c0c42407180c203038082800d00c006d04140c04c900340d40d410130ba040300c0219411500c1e0301d1841401e03010200245400364144000410800c002402103501683e8012 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 28197559 1250 28196309 28196327
    0x60305030c010c0e03060408090906150d050106021b060714070b03010303050a03061d060108150d050a0b060a1508060409140d03060609080309040902190303081905060f010503100510 80
    0x14000307102d01c1c031244861710380090786038001c0313030440c0b2003074a800040400d0000f40d00300104100c0d00100c1452201003400030a100400c5110501200002c8550400074020b090410100110700c100300300d90400d00c000d80d00ea0049070180c1d0341c440302d50b6034006641c0300e410382400c3c0d25a210b03910041d1b010000000381500311009103c00d00071503508002a80d101c030441c1c080000d030800440c4088040f0380c0001d102c0e502a6860719000f1605e1108021103094280001c0c0f00c6140701001200c3c4d5410800c2210704100040c020641c2004080703542d212031505010303185844074a442d1600042103001000b2800588495001c2164960001d10182600900e45c007415901c1d200012848002844e0001c0043c507a4805d00d800c0d0103446d030400195280c03480d540c00308806842030660699000321190044030724221050462001540709031a005907070301d41801d4254068094001c4000b01034201410042d555540008001c1c0424007401c001c0c0e140c0e215100c44000a4005410180e0414428000251301c160000c11034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 28198809 1250 28197559 28197581
    0x1309270507030c0807030c06120e07080c010306090902061207111014060409050606040e0c030d0201060617010509040201080a02120403120e0f06010b0f071b1403012a03060305030c01 80
    0x140180f030703924038050303039205558800079180941018051080c6d41c805c28041078101c1e540e03000840c00e4804005068100f01990340420081e5220140250465805024107070090602140411440c441d58010540c039114116402e03a01d02125070001e02524007901c0742029a20504c411076540c0040609410020031108066036103030107406000500b1807504d4000c00240983c044060f000a807203000a110181803a441c0a004500860b000308009450404c51008990855800841c50034034000000d00741e24008000c01c242d02d4180300050100b9218198500d4100741d0a01c0c0c620796a0365101015030090040d0300007140c11000c44028442403507030100341d03841c0fa100c840d60200300e460712290071079a4804004210280e5504080f0042185001c00e034090040e02e222a001d10b8079007951a41c510443c0005400d2007445200d2110f01130180004101c00140b417002c0540c020007828821017052161a000781045100042c040e4a541000c1840707a007000c002107910408490301c0f482d4100d03445001e84070303420710 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 28200059 1250 28198809 28198823
    0xf05030d18020102210d0f02030115020d05040506090406030501020c0a020907020106080a02060d110c01020d0b01050708120606040f1d090703030903080307020c1201020903070803130927050703 85
    0x100c0049180c904480d070001c1d03a050b002850229903e104040c09408220622034041000344942070300300700240264554049603000040e529814144a40502000c00e00c01900719804010a0020305421000711800d80e00103c0d4440d464508240006015182e80d41009015500200303407603503030000c00201900c100d803080741d5158181d40d44890480c00c83e40c8500c100c1c1490382c004429480503060100041030384001400d4041050354064000342c005500035151201c107a1b500042c0340c00b11140390b01c0b6480340408240782c01f6280c003600340c41d511124080d2041c8007140e2440040402d070b0541e501c4088400401062440b1102c00303030b80d0141040840e01ea00010b0700b100c0d00c14030004907542750204980b01580d515454844500d070542e01c0d44403c54000030b000c0d50a602c1005041501076441003800c131100c4440c4400565506140010f040c00d20605510600c00c1e030f80b003440130300e80c5581d8049154060f80c078100c00c0060031300205407041c0c1004c000d0341944c1503080403100d000c105004000c5418000d403406014 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 28201309 1250 28200059 28200071
    0x70305070606050f03030f03040809331201090b0102010e060703090b0f04020307031205040f0e16090509130f020d0c1a04050f0f0f1f02011413061104030f05030d 71
    0x5015141040c1385000d0703071641080141087e440c59080142d50080d000c1e0942d5070804403501c0104940800c0224040b40c038000d2034950f0402038824041049407201140140d5080070b0a00b28407490701c2006004000f507558480000d402940d200b540141d0400329030808694403414030020140050801c000d00f960781588035400500c0070b003004c0c140c1c41c0c001c5034040c0003441d203185552503243d20042e540081d581084070822001554105441c080c1c1c000e00030001c507200b00d44c14075044407451485913502c68000d0104440c0104107555482645a40c0010020040b0502e2125450312100d583d4280c7c1c4000e5103c10390304080000e0100c3e10429200b03a07120101c02c0b680308025221480c02d5401148142640034078040d41032412400c1100042003003034005055440d003002c40000144500da0481d00c858003802154207030602180d824041d60400103a82036102070741d0300f000c218410204003400f0018101c0b42d180d40740500b1100281d8125402986c10050100e000c03840c40c038100b070b00c03903110010741c07040641811 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 28202559 1250 28201309 28201319
    0x1060e0a0602150a020a17010905060111010b0f1002030408030c07030507080f03030402190e090c0108060a030302070506070809030d031e0b060711010e030312041202060f0406110f070305070606 85
    0xa4a05402403005000000a1340d5a1080c10065406100e070320042001d6a00041c15408244409501900300c0010203e51032400310300041c4082c040c29200c0500b0303070424007410605e0b10340600c1030070050f07001c1d00c01d405e00c04070f002030070380c910300c500c0e40101483c0c8000120380003e00404624102500d02c1a42500d2402d41c0e24840f40303503034280b0310030b1520040c0c02c2000030ce00140341070004554510780e140c40b4001001d81e107403c02d40103503200310b800921a0308000c080410540e4420b07400360384260101d0f01a1071003401c1da00c000b55031b0040303801150302a1800003007050500c40c601c0305480668100808540900420b488010b029190650110307a6442d04041d10445601681c0902044071801400d0b0b507050429507100c03801c0100180c4081c41c14062041d104040648040c001000c200048018800150034146001c4508250311a0848115080601800751421042819070382180d0815804030715180b2026140d44907204100411240040000e40001016003200240054502039102080640d42e83c2c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 28203809 1250 28202559 28202563
    0x906010806040b0703020315040903080403120204061205090a0209180d09050f0f130c05070c050a0b0a0f030e03070b010e060f0a05011211030a020903060109090503120402010c02040501060e0a0602 86
    0x20740b00207109902c0500002c0d042d501c80d42c082c550006101000c1694600c04101007001c0300c010320010740c0011203840400c000c0c0340c1c01034002045070380c1d43c54085140c2032800900a00c0051103e00c0340580a07203500204200b05c3e400c1181c11016500101010031500b0200d041000c1c0c440d80380c000c411503020b00303103004103240d00501c92a41111806003205010f00410300c03c000404440c100c2083d0300c00160200c940c0c020415100e0b10707000040a4032020307941c8540c0c2c14006111840c0342c0c41301d40725038200c402c01d101c10341c195401d403504080b10307081103002e00096002c26400303410603086464162002003100000c0c403c102810034100c41412080d05850380b55101071001d03480d81403a03000d82004105000300311651045000e0080f07090407800c00100200030b4245403038a60301c00c0d500f170f040701c1e90086000e01282c90107102c07141c01881500310802c40c0300c180f6501c3d15224024041142820f0140e00001410b5901441c4605015503005000704140e40e116040034000aa00c803002d03a00900001c1e00c046803075400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 28205059 1250 28203809 28203811
    0x2030d1e05130605090301090b0901020c0709150b070503120f04030305070305040b0f0903090307090c020c0303040f090b040204050301140103050105070903020108040b07110d0201050708060a0b030403030b0303091201050906010806 101
    0x281d1a800300b250350405030152015440341015541565031640c02174003280039019014007030b100e8000050b0303440d5902c80c00f052400d45150400c4840034503140e40c82d800b0103240c80b501011200460301c180d44a420a08249003180642000a60200300d0701c007c0045c00c13901e00001d188240c0c843d8404100075190108110b08555040360300808076082d00000c01c0300c0506140b440c83d0b0010582080720700e40385102d4042707400c1120030f9000da10f102d6100c1d030107c0501c1e9014400c040a0000540c02103080c20b10700400c4501720000c45c0f20300c4440070b9503410070401d15291a01124041c18014000340610307540d0360f40c0c3d8506400244020342d000d5103054085580f4038401e44010080383c0d0142d441903a941c480d42c550107410703080980010240322400c1000d0702c4450041c0841c8080c040903800015440c076012201030700f03468005081d984a1100f44500780105145542a81d07040798144c42c0c0054861740000c086851441001c0815500c50900d08944c0b90032a01500110300c201d40450a81d4843c1c4d9945403090343e1500 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 28206309 1250 28205059 28205077
    0x4080604030e12010606080a0f050601050304120504030606030807150c1413050a03081c020702150a03060b0d1a040c02030703140717030106020c010906080703150302030d1e05 77
    0x14804500401c0c0b041e1803403a103000b40240300641240d10041d5040c2105d1580e4440e40c04107503000708014542d0700c04d01c2a24402035039002e0030700592410000080480c440107000501010b440c030044648544240103980141d03070301c920304005107901c1307062024041e000118101d468110422440d4403030792403406080c098001070345442d5200140b4654240c066000b0401a00480c840e030703100011160b4482428400450062420580d500b03d40842480c0401c1d5100a41400b98010450040140c4400414010302034006401c0e0340c0302e05240030202c01030074a0764084407c030708020401c0341c20b00b4101d0f80a02c2c10510407049244001000d0011300c01902d4600710248050380091240c000424060101c1840c0c001c1080746035481c00c0001e98940328894803010b440050984040f005104040d0104100384100c0d0702400d240d111586401d600030070001c0000d0208040607160001c0340001e1903080c003100c01030750b8024107840c3c07070503111f2070020980b00e190742880448250f080741c0c44240c240a5011146070917 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 28207559 1250 28206309 28206313
    0xc1501032907030f020d09060902030d0c030807030221090c130b0913020604120503090108060d0512090303280806090115031d0604050114070306181104030503030405070e010b0408 79
    0x39940e0b4a05030018010302c10307110141902040411107580107449581d03c042c0c842c050004043c1e0050041c140b501c060380c1401c10910032545201c4011940002e2900d42c03084c09031030003580d110307001810014211404165410411404824050100c04c00308035050742107425101d00d525030004c0019003007500c20080d007280d000131881d0702241c007080d4095030102c1100e001410303152802d030380c0d103c12185241c200c89044d50180c00c04203100b0f005691149a075508801c04845d24407802d00c4030380312251600100e0001501030b0800080110320ba4030103005442c40007610780701400201e04808030b48941056041d0703411000582c0140056034901c0c2402401e4180e50145150b4803010070500c4007078006082607412100408100d01a1440f8a90204840d034415031158001050040b01e80c50203050010000d070220301418204a0140142c001d900d100560310101d0020104000f514080122010b10454001824900000003004288500010300310201c40794060303c001260f0b43c803080b050150050307025446039a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 28208809 1250 28207559 28207561
    0xe0d020d050f0412030306120c0801141e0601020c190f060207180207020a0b190305060103020a02030703080414010203040b0106020c0402040501090302010f0306050301181e0b040201050706020c15010329 89
    0x20071181301407000d4511a01300000e1154403001405529904448102e400f00c10000051008150038016076030521082c81d80310030142081030f4054429003c07600e00c4400c0c00704650014416a20810000d03a50b000080c001d4043d074000f0503032811800301c407406440400d402c540400107115200095039000c4464841c4203421107400078040c04081e500c4100185c3e8460344116002c03c0c1d081d007400003405241c0c0da6403d041d0101d1a059005019914020001818540306020300c100302600801229000d0b40d02d232038400c41a94603898400000345221204c0c505540c404000c2200300301d2030b400107030305030b0f1038940032183c91079000d2003000141d10441c01914002040c5550400c0103500604518280000e00c4c2030116515031120007080c00c541412848014132544a4501c00c2801506034000d0f004d070110310004042803c09031900802c2d6000030380000d04020000030000c09219080c0c0c10303074503802007580c140c4a0b41c001d04001d0106d044020701060f5003410104102e001c0b011401d008000400407600c001c0324003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 28210059 1250 28208809 28208819
    0xa0f03020607080a02030d02040609080105132001030905030a0e0a0807030206070b060607060f06090f0212010608040305130602070e01080a1104020c07050a0905011d0702030405060a0c060e0d020d050f04 89
    0x40303804c80305070750007544814400c0a001b0412400a04050f2080d5500d0b90001e41c40c3c40c0105003034490241240411400d020164030214000444020b212030502a65032108103080340120300401d68220702030403a00000c03542c842c903258400c10101d03105800f00e52000c92a40c84600190f180c0303266210080d4040000c000c003100144501400341d070300c210f0042400341444c0d0151a0b0f80c05450380f90140d405030719503d840601403000c2d503106003c81e03682d01c0102141400c51000300e520042c10180548014040c0410026040510402c202c40000c0003107d00448841d9490b040a5600d409602a0001b5803440d8000460003070000a040780042d0b800030000702204030300c0320900c0025803104e0346802d00e50042040104403910b407103010b8001441c0304400000d40b0340c509401480c0d038420450000c4998109d000500010513400001d9500307031802194030640c0d60120748030545046140c0200101018107015504800000200780c6004281c25038094414603150201d00700c075144504064504c411901380300901c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 28211309 1250 28210059 28210073
    0x1050c25061b030c03050c0403020a030b0405010b0a030606141804031409102a0201080403030f1508010c030b040b01020a0b0916080a0309090506060a030203061f0507020a0f03020607 80
    0x241041c010440003560402c0c101902c00720501115811011079101c109030480d003581072156660254440403007030b04141c290350000d80305c44410301c00038040b88514004181446402e520440c460704004108420040d642d103032a0000d080c5900c680c9640035501040904c0508000d40420b203c405444144011a5196541520341c41c190b1091014144010b00c401101500c0703400e99183e040308070741c5a801d0081c1e4071103109103040c4001d81e490010350701c14011200050360010203040d0000d41c1800c01041d40318080b00c036100144119006510701016a030301c0040e0104043d405580048501c2d542803290721110020f0100b9907d031004841c6c01030303002c0502d8201141d065054180c001c1070703c205840c6009a115844010100c082d08200119009013801c1420543c00103072600040c900d44205000c03514140f00001e8643c003c0070640d009040c1c0001c0080c5256407030b000c5154694092040010001440c02c10040c050341155508901840403044007050641a485d002000c030380e40280418603040044e40c440d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 28212559 1250 28211309 28211377
    0xc07031e1101020a030f0e0f1f0906020a0908010c03050c041a0c01020d0c020f06100b0702030f070906050414100302101106010e07030f020c0d030e0309031002090301050c 75
    0x11007000003580001040c00d4082c001400842c442da03401240000079151074100720303a8400004030082e405801c0411b4084c10200c3d01d0701801d0b4400da4070030480510320202c00d002d09048800208a10300c00654003141540007420302c0140d0704180c008108060040c2021382c04c4078010365a98503030450500c800c00c284002d44c0104549001010b24050500340c0d10315001c0d0a903040504218002603c41c813111200607410400d0441500c034050041a8a041111241c0103080c81030180315940e84000a464056407400c01c001c07204200b149040b101201ea0b60324a0400030079a90086911980c10072a2868154891032143d42c0501c910600160880340380d0b500b0004841d42c000c851105201354a50a000a03402c00c0c807046008102c81c0f01560780720b00d01240020f0032100305408440e90307c0d1040c0003540c205da01c0090403c00f03101450900090030540340d4002c5107540a0341e1a516898400c0400039040404160052b0200100c01e0b0001d00254491143c42040380c05050344600b404401032200b41c18a1000107808 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 28213809 1250 28212559 28212617
    0x9010306050a03050307170a320304060506041104051c0303090f030507030e0904110f1f0201060302030106063006030204020a020a03090621050907090501031a0c0703 73
    0x398699a460100b07002d140780da40300744c0d82904040703542014884410489104900954841c0d8500320100708082d0a2a0ba00003076800180d82c00342804520340c0c01c4d02d0340c0001003c03004502c56160700c2d0034680300e0701904003203440750300031400d110a000c50803600170150703415241d0082884a100055020102e000d4458120a0b07003050746070381e2030f400494400f81d11600018002d948141d955081d41c10090940b500154205010700b12200401c004180101c01d200c8090748201c8609114080c42000540c40c10486111001d507020a44185520584c0551003c4200c80c402c1d40240052660360768280cad0206103035040195145030303203003008601c02c0c00d900c0d084007580d581c2040004d016840b0740200c0c0807078000c0201040036038080c042540a054020180200608a03882c106502c5801d4000100c840d805000d41c810100340c40d06c0c0401d004078002d001c141c001c0d00c81144100513039039590074544992070108900c0c12850000c0000300340c455000d0012144600d4142e1030b2407581e14007070b030450024510941c2d01 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 28215059 1250 28213809 28213811
    0x20c0102040b0406050a0206060604031e0f0503030a0c120c050909040305071502090f030607020705061b0609070608070806100c05100c05030a0b030c03150603070b070503040e0106110a08090103 85
    0x30100b1001d1124000c0c00c0507010340e60781c1c00c1e10788183c500042e24020025100902c6050107110410004c3c1c140d22001000300f134038010f401010869441d01ea140e001119100401500002c4200125004164801400c907205a6200015aa0103c46081c100c0781c203070bc10700001510400c600005420103e28440d002446841c24618011282d100c1e00d1032412507011500c1c06a0700006c4501d4507150603503092003140d1007200507040398207081c3c0029603038007940e00ca80c40c002c040200700b400b01a0b80c1c0a10888014801400355072462034038404c0325455207141c0c064000400d04070404038032400e220314421481918050003000812061b0603040d02c4501d440350003210240308640041716103c80c0c0d03000700141e4405944600303449042822030721007940e015070709481c003903407002e50000385e0755900040000940700d01c04003a81d41520f95002090800b442600440b015400c005402000c0101c00030042003107806400c809405a41c81c2d8030201c1f862414000754140345c2c0e00c40d03000f060200354180001c041d25501410 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 28216309 1250 28215059 28215067
    0x606040b1206040c0f090e0d03110706060f06030e0304080604110a181505040e03070204020706060f031101091409071805130b04061d0a0e031c02070201030605010207050a09020c0102 80
    0x740c254a400b5045a0440c0d0080110104115540e41080c00030b015013514401444284141d02c8400c0d5126112004003041680301c00003500ea848150382110005500501c0c09d010309500c80129070300b007000c28442c00000920b03002552944480100584080c3c85a02020301100d03203880d215248001c3d40c10294030f611082c030140000b07160300c0e500032004c010001c550700891541140d41d50307100c400015a006601460402a00c0c04c0402c1c4007000311400503504503401620b40c0740e0390600d0750040078542c0064060035451400441844101002d2a036049000d80e40c4058146e158841c2c100700d481c1c01c009180d000001800072070b9445000d601e00c070101200d42d07800820170560b02c00008500300040e1445a5030640d4031140c080903800d0a000e0040075040b00100c039001c04007810300b407136118880100450656951340081c050700710418000c0300d060b81c1c03601c60040c1ea440b01040c4120000d61122200b01d02107840d091000400394000b0510300100c1d0030043c074080e03860345000e00100180d4803011240940b035500300 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 28217559 1250 28216309 28216339
    0x1005100e1507030c02010f020f1203090a1223070206030402130b091503070b0406050313050f06070e100f02120d1404030504081002070c0b07030e0a03080d0b040506030606040b 77
    0x81c05401c0d52030099442d03070038004075800003410007500c0c0000e440442d04418041e1200e05000940d4045c420124000349669940300c41d506410660070950050004070582500f034a050b90100f8220a0080800502d1170a0010300440320b03040e100c0d944000750000414400113004d49858082000010705946020400b1a0304800041d22020201c0d01450f4546c551001c18a403400e04010309000f610b041410945010f050a07009002400000d10745c40e07105034800e038040b0400c8030a02034440b8007042101103403403d0401d001c0c007400e284039401111f801200c0d18450407805600c5030340f940603800925000b0300f009540907006800d56511170101150595200c00401d0700e085c040100d140d100c1c50080d500e50362101d00b000c24960501c094560280314031401481050701080c245030a58048910036060195140702514050794240310b6071014590000908800009105100300140400703400e0f80020002200008100411205d0a540094141c0e00800026900d414617a001c2e040c69500100030705821381c004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 28218809 1250 28217559 28217599
    0x402160b0109020a02010b03010204290c010608060610020c0f12010902090a0b010306050d0c05130b060a021506031504120504030b090d02120705060708060a05130501030b1005100e 79
    0xa80c494080b0682c001841d158803942840f6400300040118025850141781000e8600054070390800700c900c950752110914440c14001c41290400e0441d40c000b40031099440707404644814044400b180141500382c040c0f01c0c550305c0070600d02c400d2200104141d4915800406000f0301c00641d0240c454a990baa41c40b044c05a940c0711219882403040e040049000c1880000040c20f172100e40d0b2146c0e010f00c0d003940c4e50f40000307011000c1c1e82040c0c40080d5007000420419030f02400240410340c104940100e00020354141d040e50204d04000180e02008281030b00d611420141643c0b4a20703d21f55241900e40000880c0001d0b11001006134070254a15180d42001e03101c0d266502411420341d10200c00e5803048149410a41d010300c2074107011034003598000d05240044c0c0343c4a0304d407500200f4140c20030003403e0011345155181c00d00c0802500001d003c010046080070301d600d00500b0203000039244070a4400c0080e00781c4100a00c0c0c0001c0e41d101401c1020203d0700e0b0007043c3d0310710300c0c40c15007154004013104005042e4411 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 28220059 1250 28218809 28218811
    0x160804110414010302040b0d050307120314090607110d020d050906070618060c080114100c0510140a0912050a210b011128050f0d0801050312090a03020402160b 70
    0x18503a4040c00b40c1d49180b04000803201604203a178092105003e548012030008410360f0452138214480c5002c80f080c201080300100015500303004000c80302028858500b10011b03001e4840d4440c0c0d03e0705100d404220000b1940c0300003842c00800180d0040c10300020451107140600700008015040a050040550f110410b4610084d4402c5400071902245810f10825025800c050081414003200c5941418010407880c0306080c01c0c24041e105140d900e04030a03102c0c8000040050704181075886902d4461500c3c1d000e040500b51050341d00d040c81c00410300703c80b030711301c5503e000951041d01188910203036a01501e842e08014900c1080c4901140203200e0050001c00341105009048800109006184000340917000019011907043c4c3c00b8220505944c04d280710f49603040d2001d070346004080c1d50f140ca0142c1c41c01450b14145036840c0980d1194a0380150040240384c1a198100e0641d09112402c2d60b00c10070b00e000d504145507015041600c200b0150a00d80d00a100c1074032010141e00c06a140c0361165001144 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 28221309 1250 28220059 28220081
    0x70807080408010e1b010503010e0612070303050a0e190501030e12030408040f06030b0906090c0d140601030501080607090e1008030c0c0306060103020c0c0f040216291608041104 78
    0x51244d54001c0d580005025080c0b02003200154500e000858500080450105009105850550001007038455403100c0709204402d000300c040b9a440c0e600d07443c008086811440100c40850f0500031114140d10301410f03400d00e02091b41d14042c0e140c524017401100034005100503034581e40102074a84d8489414070b0b00840c8038900031012543c1e541c0c5403030402291a0340e030f03500080030103103000c420314001ea5500c00c07143e07044481126200d1813501c5040811b6150301c5083c036185080c91030b0040030110040d100026510414098904000607a0b0343c81c002074640303000301c801800040c0511014000c13151040025500004031281350407010b40c40701c05642c590391140b007007200b5941c400c2d503d101c0f461034104612580003800381f90960400c3c0e00240c80c240e4501044140a1242201c98502d00107070301d03540c3c1550200521295a25404c06031410503889402c0c580014841c59800d40101d03541303549040700d690f0300800a086c24007510840025085640d110050012180070900948040b06560fa501030580300603 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 28222559 1250 28221309 28221311
    0x902180105010906030c0206040204090c05060a0306090e0303010302030a0f0314040806090601080c1003051902030c040911030c04060f020c03030a020c0307210305031905040b0105090f0f010b07080708040801 91
    0x35040c000003421071603c030350104041500700000459450345c0071070300341c1e0080d40c181c1c0c01040440d914609901014030a8000940000303010030024207456040e005602201d000100c1044100341c0c808081e6100d1109000294056106503004400110710601484107903000e460540004144407250080544c01544003d0f400e81c802c40a100500e48240412401407050300020440900040049034008071790f510a00181759441d400242403c40e0b5198640f03254841400440d0b40c0d00c3c00d51015140f07074015000313012245140c200c00e200400360b200c0441c0c5c0035000c0421a130b414240b4021080f100c0c1c000c01441001180200082000c0b6524204040c0486c1c001d590054444280640c0c10315140c1086640030304c0034104840d20781c02540300b4a10005240d2034041c034120340c0d02e0344ca191010300540100d05807200720500e800104428000d4a000060580e20101c47d01d402c540c54040c50310f00c0d810710541d00785d01c001c007050004100d03c2c68072000902c0003030b11500196080c44070303a46440c805a00981e014032116 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 28223809 1250 28222559 28222561
    0x40504080304060b03060f070f0e04020403030203070302070608040305070210022a01030c020312180304180203040b0a05040c05040b1302030a0606020607020f06070804020f12070302010e030d0819090218 89
    0x13400340441044082d802002c50f454002580518a0340207007450040c001c6030042d01250070f100e00300d5240f080001610556681d592450020360300d9200f800145c3c0180141c1001080140c411089079001d15019500c4e18244070340c1d40c00f004203d40b075841c0306001f0f40c416418104480c0040e800440f4440722548c00c083c2c0e4041d560740c0090b084e12602889401150800c0001d9501a0b00c00401290810401482d03040618540420940345104940000346085130280c4100500c4200c0d4000b10b00c80c0744101481c481c40d8461400860580d0410344006015040f08042400b850900e1b07071200e282481c0041c58207000079800102c44089034410344582d2107040e210001030085070b40422080d90407055510040549071107200c056511120702504034810800040d0203d030640d900c0e4101104123540040200d4400172480060540e1000700b0304c0704034080f075425203040d940e1340b5000c41c40726480710b0f641d1a00d21a954481c1080400060f401e4000300025588590000160300c03910600c600c0e50102185002d01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 28225059 1250 28223809 28223813
    0x618110a0e04020f0d050f041101030605010210020d0b090a0507020d0504120b060102121206101103070f023006070306080d08040206070b01030b091009120806030a06050a0902042306130209040504080304 89
    0x20409c29800c0407818582047c0081241d0b9a000582d500d80042402c0e0040e16000240e030f6010250000c2d409690b4811001801c1c02075000c2954006401400944c08503280424071400554050090340300e00c0401081303e90f211804202503a9007030f507000f04c0520581e05481c08980b92840c1c290800016203402048072003c0201608100c104c2040344a554142141c5448102407816920701c21400010004101d13111440d0031274443c641030403500f101a44503094441960301c0494a000002c420301c0a83c0d11030b100c041280617019126000941708014060854140070410035030b011840540f04a8202c8010400c03003001c0b5030440400c5000e580f01e5010b03881641028190203140602ca03188041d01a840c088030b40d800105140e1401c40301c4071141c02d01c10a5030740c800000a080602443d0054009424a01003003d003440c43da101690307480c4200d40c104081600d850300020705c10000080c81000f400d40c2800300d0040d20b0038031683d42160409000140c5032030708020114080d103d0540f0129646103000c014442 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 28226309 1250 28225059 28225073
    0x120c010605030c040209061b03071e02040507082703090607030503010303080a020c0703030c1a09011b020703050705060309030c0304090b15070c03030f09090618110a0e04020f0d050f04 81
    0x180f030000850f4190b0601900100244045c864407808071001015850811101d2a040c8140e84400350450800d510b00c082444900880e401803131412407041d464200014001401212414000c5640086003950140c4215891a8110340b0b00d1525080384014041a4025603842d07004000491207950390a07141d51661801a12107500030f00141413660051010700c084840000da12411242c261924200c150801c1c00c040124454840040b040f5005243c20010701220540242d02d03210303200900800c0310400404100d8485405000c000c2083d0420308080003c2c2c03415202a5411661440640c0e00d080982c0100710300e140e0065100215a03602ca80d41810603207000d080600d414140104002e140050540c0e81d02c850400c2c80c0002410300501072841002d4500c20801003024008558041002d56154803401c40b0070107010fa0500640d50600c4030043d0408840c0041e0307041d009243e10394000909020301084080e400201c44161a05000e2140e00002e400364000e0601510b10300841b1080da04050402c88 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 28227559 1250 28226309 28226323
    0xa0603023f0a0209040309050d0f050706180504050c040e0403080603070501050702010804030c0c0801060e01050f010203040609060507080f040605070c05040612060504170c060711070506040306020705120c01060503 94
    0x104084000510007405520101d1100d182540c115000840c42e0b503503203029141d90100360001a040065000c200040017120b000d0000028042c00c102e41c0200d503695021501c110407100010080d06124900300400e08103904180d4008900c903003014142602c51607180340800c2d0854041d000900201d0a02503c1d003002e0040c403010f02400c1c43c0c181e01d840040c0e00040c1c1680400b0b800181085850304882c0c0920010001c000040c0603250004e100c030640c1d61408440b916400c2c000c00e4030454404440c98569800001101d084a50a07280d848040b46010700c00c0d03e03103401c80c14007600c86a20401c448400d80079444010409040c1a031039a503200c4850781400709011103140c12250055281220510003051810100e900607036001c603010130b90b55101e16107000f01d45104904080032200104008480c4240407032160b205031001c0e84c03a040211020501c0e69a03804403882002c2e00014200414001710f034203500103180e090b01582c112422103103221402c101070f512a0030300d082e40307965400f028801b13440d05100d40 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 28228809 1250 28227559 28227649
    0x14011202121207030504030b0f0c070b060a090e0c09180a0f1506090c020c040608100b0109090f05011e0501080403050306010203091203030a060e090d030207020312030a0b0a060309050c090a060302 86
    0x89c2d50307480c002102042078401c0e10320103428042400c00040940c3e80d06811407005d40300c032007420f001844070001225030380e401c1d4501041c4607812440029117120150480000c8840d4140001c001d8840e40e511a1901d45844a00c20ba940040d1560240c1d07040c1000d024100051204a10021f00350003190402401c0a18820a031485542022000c01c001c5100050f21143c40c200190001140464400141c0d000c40880e80080b0b18a4208280880e205856902590498021482c0e06100c00162000300c0140030b542c6c0183c3e80030a0322240801c0c0864031500146903c044103004a80c54107000380c000944817804100c401c00c00c1d90001041010305580d6010701030051804002c100b00380e00340700d0725003519222840140c1c001c0541c003292a60079540c0c20401d81c0351300090105069520f092201c1e070100949895040c850044004c50340c00100188030784a41c4030840d8124010700451506d076410071a96410141c820701e001c0e51181c60101c0942c5da01c020200401d00c00841281c16044114003210300100103a0300 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 28230059 1250 28228809 28228831
    0x6051306060905040b04060b03071707050103060b0a0519050c1504060b030307030e0f01140307030f0b01080105030307020409060e0f011506020708060406050a0f0606050d14011202121207030504030b 87
    0x107020000744413000d880c0d001b546c0040301042c44010310020a00d81021607000207000f54100300c00c4840014082805c000341c3d00203990a110b402d4455110181e64031803690000000340c0100140036160070180090f407440010b5290483c607000a205420345000a00740445040300c03401020700c810007131a481081c00c0301c0c800750040e41c1015800d4a0203417101008103003140c0075032040e02004200b40e210b0201c0802c08800a0b00007038980c104800000c00401e0300c4042800e4003450043d8800c2990b0007903050504031100140114a84031181d828003016141280088641640307810f0040007205040c460303030b608402c1ea03000011324000142d00c04249003204d40d11800954101316418040510003041055200703400100100b441d403100314a4000603c2500030003840245040f00110300c49901c140205a0101c000300140001c81810b050341101c100280301e00d80c003252164800c01e006040c126035040b100aa13803000e803880c0c8030030003404015607803004108030700158001409004100101c0600350700700101e468 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 28231309 1250 28230059 28230061
    0x4030c03050102310605030402030c031903020d0302070b010b070c030b010b070323030105061b0607050d050a1b0c0203030d06031109090604030c2a0f0f050102030906070201080403090306051306060905 88
    0x1031314800f031200e00d0140303004002c0c0001c0000c0c00c0d500c1c1042580f00c0d607000501103c16020a131450102032580400d42200180a0070003042a810700c42e0095440f500d401280c40044c03a46010f1b03a5403c3d81c1c1c0907400482c1c0c045031450000012a840365072840c0208520000a81e80c3c5125140042001e0340b42484080908640c07011015039400c6841034030f06480307054bc0e880d0740c1c6d403800c103160502458580b004000b00380309201c10055800d9008e0090701070100c5078a01404182c90703000700380040d46e50103030040103200c008109445203284140e10810a050000e01560700c0c20030428010700c142d43e95a0800d40724181d003041d5480c1c0d1400d1150700d00c0d500c0740c107030300180c070141c285560300911018510710301410034546810f000e547c24012a20500c0400500301c61000c07125640d030400c0c0780300610744c4a2054034110584002079154004405c0302c403a000c0c020001446d00d0f900303500540e113071207000d40f083d0200014041e0210024a0368460305000b40300350880c0140780c100c10f181420640d00075401a406444c1418 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 28232559 1250 28231309 28231387
    0x111070b030402090408040305011a09071b0305090d05060112030e0306040c09110f0d091103010b030303011a1201061805010c11040c140708120708040507060e040204030c03050102 79
    0x10055a402c194100c1d040140341e201c508200501d40110380014000703501e06402071454140350352081101000a503034000481e50f03100d1007600d0f00020085034692803559008582d001074801c0008081e4001c1c020900c662513401a2529032925100341c02000f84522220401c906054100c850007a142d2030850040c80c1c61328040e500c4081d03c010707510443c40015204c1c503007001c516032041e0555160101410860303850b801000050b102601c080c500590b100140102410020b05044c02000383c90900503005603c3d5918081200d40e511a800e13581c902004800d12242e25140382c3c02035540c1c02448070303540d500e240000704520b00c091700390389a10242c1400110903007580040c0c026140c408050320304580c0022020001e10f400d0f00d05d0980d502c03404201d8000015660100414100900700801c0309500c244000c0d642c504041c4c2c1d900310243d42c050560b5020040403c02640b0501c403828400d41c01820140c18259a50b0725050300610940085509035000305640b407908422400c81c0d031441c441c00c000c441d0419044 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 28233809 1250 28232559 28232579
    0x80c0301020c2505060c061b030108030901080a090f050a0b0708061c03182603090d020d0606030506070801080c01030c0e0423041a010b030601020c0f030f0d0509011107 74
    0xd070142d01d06021a60150500c0031195140f0a0081402a0101d03960f0203603106940d4803417408a03040501c1c0c1c1100440348a000352540142c9041e00d98050013140b910040c600152201c20009144080c8242c03140b00c4040020105000d00b181c080c420320080602540a241010848000038886420043c0f9041081802e584085051145403c0c8000079a140a51400c1c1280d0710807083e1220048050140800100c0c0210340306484480c46070407541c10000c0706c46100c0e0a0700c3e842a244015801100d502c90100546840b00c030b40b1100c00d00c1901e0019100d5a07035a18181810302c100c81d00004140001d00400c001d5606105000c2103580901c1c5c01c10485800320320103402840306002050155a49800000c14141410305191002224070101c11131407600b454503e1040040600d4015580e01031f000000b529196001503e0140c0c105030040c3c40d070032880b5000d00941c241650600d0382d040c8941c4000c1c1c1090340090125020510065861564603400080094440303642c1c1c40400e0301c1c544c026207040100001e0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 28235059 1250 28233809 28233823
    0xb130c0801050f010c050d02070f06020106050901140d0f0602090108130c180e010204090606030b061309020f07120807020105010b12040b09010e15010306061d04030f12020c07080c0301020c 83
    0x721503e03e09250344200403200c0402c0700c0c400074a03034860302c1405408103400082d2202100c29030992000c110b038641d2070803800d94580d441032940043d00c01c4018064001d0040300d80803100350207441450184141d03212407010051000c4251501c507400540b800c0c0c156400041c42d0ba02000c0810715004604d280e03598262606540d00c210b881400c00c1c0070203400e0342281a0004016250070500075529103445500341001403545200c6c3d200480e2410341400c1083c20300c43c0075034040c209500c1c0384859107031820103428003a500403100e942210b1402c0100c08001500c5180c500b9208082da95100a103180646003e401c42e481a004610240c409000364600010009802c40d403182d88442d0402003a00c40c01d106502515451822400c5402100c00c81e14403e680c0f202c1090489025400c1840503603a43d4464940345590103403000c0c9001e48d10000103000c01d0103504404020b098501d44800c08092510700c81080b038004440381d02e0b060708040c00c01c100c07080007041448001e03142100218030348801501066501d6103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 28236309 1250 28235059 28235069
    0x60301030201120b011115010f08060c0403080705031608090406050405090309040209240324010c080304020f041a01030e03090a030212030c0304090204050316030c050d02040207150b130c0801 84
    0x1032134280040c1c1c2c59100b480e1b2030b85e1407a144011583d0032084001c4003102d0f441d0034041e042c00d4800019001400540004121b4020480030032401c0c0b0301411a252001035a020321015542c42c40200460003101a08103070101c0303403038040e0100079103e2000d0380c20881515110b511a51140d820b041c28001c1c8840044200d821005080704e00503a140e040d8008070740b07000507642041c1111a0031020608880005400a5216a001320703043e1001400006144040305010415039000504a103009030010782508011900140000c0203131146050700400a016604501c016548000c4007107400381ca5543c241c0211410340780002e020f141070034010380214020216a04c00a440762503101c41440240700240203d547d6110401c00b501d0ba620f0f142c0d051030001e54864411a80a071141d200340403465404501070005482c1d020350743c1c8030f50342c1c80c0a040000c0c02085146c10380e8841d0b402c000d40c1000611011440650740307002c00c1c0c0890703252161010081c0b205d140f2160002810f0400d0385c141600c6903c1608141074503 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 28237415 1106 28236309 28236311
    0x32b05070c140105040b1602010b0405090f150f0408091201020304030c110102030a020706180513090303050c0313020103020d0e0d0818011517010e03040e010e010506030103020112 79
    0x8400721400741c0b1001a01b00400c5c24000d4013603040254000610002c60002c260b200014100d403402d0b210b40800b90b00c10211740b40c02030300c140300c2c85101000050a04246143c103c90b818500b0b10028002059120002081c0030143d550240301d00c1c211040c10000c41d2240740525000d400c203d2460f0742602c60080d00d9060540d10362001040b90401d1160354003410300a8506081603441142001d04085412129003005c203841e01e81c04041d452020680501003000311141c280a400c84e80c01810284030304c042001001054092b80380c00000159080c070300160340f040121990782c02000c060f0150900c43c01003801d0086510b60102c1080e00840e0740f07405201e04102c140940074200e4683d140b4109041d03a50a00400c800f080f0203402c40b040103500000800ea803907402c1d00309070440c3d00c20b81081d01003007100c3c00144050050402c00b603000d4041941c8461945d4103580000e8414010300504000c16 = true := by decide +kernel

theorem cover : BRFrame.Cov 28057559 28237415 := by
  have h0 := BRFrame.cov_init 28057559
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28057559 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 28057559 ≤ n) (h2 : n < 28237415) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
