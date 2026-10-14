-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0176
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:16:07.040894+00:00
-- url     : https://prove2.me/submissions/07dd657b-99ab-4cce-ac74-493bdf7f154e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 31474825 ≤ n < 31654681 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 31476075 1250 31474825 31474829
    0x30c03080c070e070219050c09011e0b07080901030b120f0102041706060108012c0109060305070b030403080f0a020f1204060b0a0f09050a020405030601080c0a05010806131d0313 78
    0x1c601900780c00140c00140700d110a4403501ca0341c0e01416503100c808a000340c84c15250001980d071442003d0b0000f59588920810501030010320001020101c12055038413420619601f00c0700d16680140010000211003000360746180d4800d081c0070903c4544900400c0e81e0b00c54401b000f604a20603035042c0a46844190300030000e6450001124020000c59100140d450000ba0703400350004010800400c584028840070b01003400005008680c04500d411503c26120000e03001030031480d50780c14007002040000c1046030010503200d900f580c2140340c03649000c0d00591000300001c200c150700c0d10000d42d040510f54111208190300c5903005840d040701d944036000f00702c0102d07401c8410b030340b40c207401e0b5840e072809014100c2117030041c00c0160402402d1103200c0c00038041c060520541d0940912003c00e50350b500340400c5007e401e00c80014002200c6035801c000419010742d201c5418070520300300340f1006842e08100c55410039085040480c28199104203182000b02d10782c0c04890500000c9032544ca404440050081 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 31477325 1250 31476075 31476097
    0x1020c0a0e010e0a050126030d090b0f060a060203030c031f0608071205090309040b1c05030c061e040602070312020f04051302030106020a0b0405010902030d1110061a090604030c0308 80
    0x81c03d561044a980202d44082c02083c84c068402e0131900b8038448254080601d034060316050300c4c00c21000062401c1543e60624045495038500d00401c5910120341d91138a50108040340c07604480c0b407030000041c0d107a10000d403000c0540c42c400000119600520006010f01c1042c403149040c009540b45401414068140c98103c001983c04440a5466106004d00350081c590171020798540201c0c401040000c02607007407100e822614919410609415400c54213420b13038054006184d40304e070900d000c40c1c14540020641c2d0702041e00212201c002810604440f64004e504c81c1c0c0040e40c3d004039080644462804882c00244d00b4000248200a80d5002c0050812150140c800c80341940342490150180d000034010007006a12100b1000302060000000a4005001c0c5000040d19080d68011a0407c640b841402012802100000c8200c0e0710820242001c50a4074004020381800c00840c8841c80010382c0c440303425414042840d00d0a03035629070840d17009540c8110101600d82da81d14180805402000c00d4603 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 31478575 1250 31477325 31477349
    0x1b041403060717130204150905010302090a05040302070b0a270503010c091404021b030c010b0108070f0c0201030f0f0603060b03010b030303070e061b0a0303050402030f030c120901020c0a0e01 84
    0xb8444902400740352804509401110001c1e0b51445112806001c20030400e036440b90f101c0118803140780300c2c660704501a20320080086030351742c194014000392140140c00e0700716a03440c280812021075030108407441640c1d0605403442e502d03100404101d900402c0700d80340201d401c01d803000f44d8040f8251004090100c038030550083c004605204429100c0d0622031103004641d0b050407060754014a0a94020801c9584010b040300030079080c0000c0b41d20b59080070558148a030740d9801707203c0b03140d17801c40840340e0300c80c8991400c00c880c0d0f503806100501991860703130000e0515440e92503d05100301c103a0420710386990b00960401c0542d95a00307102c8050903510305414081c0d441c1060342907444c100407045032f05c184040e0700c4050301c280095050120945c440c0103031840c0812035601184c100c01d802c0c00240c910901076a070100d101d0400b801094102900100d4050240d0b000700b0400d003003010040b99094101d184c80b0801ca44641180380141c8c101200060280d40c00416420086160008482094160b88041c0154 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 31479825 1250 31478575 31478581
    0xc0e040207050c06070201090b0d0b010e0d0206090103050c09040c05090901290f040506030109051621020d0905060f0708090705010c0b1e0a0c2309091b04140306 71
    0x20204901c07076514040c2003500003100992050400b08001c260052040c58003410f078a5480c40d005013039800c012a40e00c03001c2d8450320144100d40c0e100041c224181d01c1118418400039284c1c1c0040c0b900e04c80d18080c103041c035844070000341000d41164191002c1c140050405c2c840382040702402885688181080d40c03003440500300200d041041501e0041000e18121022a1a83d01e0703801d46c0d0070103070440d04003882507031400c01c404a12030320303500041d500070003a01c0c1011610303081c82805035220a0303181d04a80c0810a121070700f07181012800c500e01e035040b4002d1000507035a101f464005006409400005003a07440f4080c140f1008561590086105c2d5509070b40d006610380300d4858854a4180c2e44c801c45c1c0c00204181390401c045400f800015030040d030b0440c50600708010a42601242d110300b1103060340b202d50742e51803007000c1940010002400701000901a141c1e001c02d000105d0381c81c0904101d4900980000c4006032008044036207049940c0b02150300240c80d1039032814151081c0f504044894000e0040c4004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 31481075 1250 31479825 31479829
    0x80a0501050c0a090e1305070f03060b0306060a120c030f14061005092e0b21041505040201091e0f1d240607060609060e011d0601210c0e 60
    0x2c0c3e03003102080f642c6010860b85018000303014054040c009400c062540e81d903003400181d040180d540140701d03c0c9859440c0c6850360070041c0484003c0d441950094000c0b0f4200600790391440c500000707031134a07642004c4074105981440d41924241d030f00001c00341603260398600140a0040e0019078102503000450326a0b40d211005210644034a214854001c03000c00081123a0120700040200c3c1c101150004400c034006903007001341c800d1041d5000d04050b12000881c5c401520111001c82e5041040b100100b41d036050550340d4038603054484034078907003469950001c1001c6a00c512000e2005044103a50b180690f40450b040d04c040c04a103201e8500c3e440310690001070111005058070705e495803280c0022400d9980d12113828612011200203400c0003c40316002c1180d0b40d100e002404107503001d440b0000e4814144103100c0202d0300740f0f03044941c103815901c0040042495515205030b0900c0158400f0132a521104016200382000c080f00901055084000350f00490079170340614640980e0740e03502150030b690402 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 31482325 1250 31481075 31481077
    0x61403030f07060203070509190302011808030403080a0201020c100f06090506060a08040303061a0705060702010509031b010609180605060105090102070302090606070203060108060a0b0315010501030c0306050406080a0501050c 99
    0x38081c0319641c0600010021860301d601656001c0e403507050407031500400d00001025800c0c68189424014000d480a0055503030103104406082c90130144000e2960600c000366940340a42d1000900c840f030006184c00c0070520079010f03200000070110841e0040f010841c0b50030040c0c03506040e260703140c40c40e00000140089150150701c1c0103800c0604030607e401d41006c0110b8064000910540c181501c034040068100c40d6080440d49107044508815200c54003480c02c5820018040d269004580c1010140100110040200d8078940c21640d03501026104a445c01130241c019580800c00c10f5203452030903160100c40850720020b162140e80c0401855440c6001514180a101390107401640044020b10040c1001c09009400180081040c3d04103003140e0b000901e0002c090704944000d4200405003d407907090b034058001e0591301240030f4808124200490742c1c1d404014400c40b0304054856419a480c0c81c001d0b4080c1e0003812001e130042c80600d841d0900c80d940e44504d068110f41c0c41d0701e00303400602a412088 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 31483575 1250 31482325 31482337
    0xf0d05100e071a07030c02011b0b010602030702130b090c0703170c0406021603170a0203090405180607020d14090f0a0305010b0a090911010c080c0105070207060905041401051e060d06140303 83
    0x5219951000c6c16600112852051400810801d410f1240d6040100f41c240f00460f008046903401156141c0d56441803001c10341c40f01440184013400d0203121f030143e50f10400704d46e41c0815600d290b01d40720b80380c500b4115210303401d02c000080b01400d02c0d01030280000c1002c0003003094031683d4088500140e100300030200f014903144005424582d5030407180e0680c4003030314000d081d808100c1c8101c03414503803082d0002d401c0341d00607035084c103104000b62000d0f00d540318240320690b03120317026001030040d4500c2600b01400c42c110034529284130032400a41650603582d10903900c007084002400c8d14a540780ca83c9812802007010703a26040c403501c0400300011741c0301214007a50b400b1903440f048807880e40410b40015a01042152130490b0309060034001046a10801d120f11446600c0550092070068038105002d806015250441e9015070b040c40001d24128002480407411650150791040030101d01200c40e03014117400508070b0b40e0000300080d080000c0c00381a0014426281920300c10041ca00000b81016a42d01c298 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 31484825 1250 31483575 31483577
    0x4140c01080a020a0309060f061a0a05180d050a051506100212070203070b070b070e010e01020c01080907120605010527010b0f04030c030303050a0b060301050f0d05100e071a0703 78
    0x140024000b885503000340010b42590304010503680d0081d56071005550025450002d610340e25803041112031103c00c25180d40340102280c40e40f411280c000700a01c0d600c20020b00c549240d1907400d001c1032a4450a1012500c5a040416242d0308400b80ca0650740301e044100c1d6131140b0070501d80204540f450902d0043c0400429500100844c82100a8a406c141c1044c0c2c4203aa01d4014190001201c1d883d04000300247c5200e400300700c0c0c13070740340586004e00b800d41110110303410803401c010842c2c1d141e41c00151032040301c0d0003403c0405041da10940000d00c0c001c9107030000b1482c3c1e0b80d2104c03c04100112340c1c021034143c174021a6850380d03c1403145c0301c44101076100000c0b03040d081c05131001084046519001408000c06400b0003614181d242c2c0c0703540d680011154030450000790b560041164240241c410b13103204207030441e440391440d450000042c40c0b00600c038107020310400c44000d080081040401c0310460300191144140701c240c125008141c0c643c041031060b01c40c4424011961140840c03201e023210380480d41 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 31486075 1250 31484825 31484837
    0x13110301060b1b0c1207030605070c020913050a02040c05040303081e041506081504120c0c09020a030207020a03060b03060903040b0d0c02012307030b06040509040201080402180f04140c01 82
    0x2540c0440c811a41020100074004d000d010500021a141c201c2d102c200500048000c05046156180600403124014054400c1040c001841c00042ea581c00c0d032103802c40381c11030100c01200c080f0300f0010304140c00d21030001c1d405490407980c2d02c00944c002010304101c0c3e0180e01c070020143e40380b48000b076000c1c845000c0d226141b2a024005800200ba52102d050f1459501100189964940410034903103804c10002c02c07040c0801004100810182d200e030303e01e10804038540310075404410b5603a449160f4050041540030f50300404c0441506e880303581a5014940c00520302e141c003540d0703801c010b4000e000141101c0c0c024068000010901031001049500315072040005178600b4603482e0f6424000d002a0b0341d12021552252480c59601a00c201c0082c408030b0040d22180700c90600c1c200c0034041741c2906d9801c07800390b02d0600040002d07030340d0b06108660207502820600400d03502c0b480021455800c06c0c42c81228444c001c07061098142c00c50386282e100f14800c05110784001964421181d88030b2848003440e0009071 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 31487325 1250 31486075 31486087
    0x6030809060310080609011e0903021c03090f060b09071422032a090603030206011802070203030705100b0604120f0302010e030c0102130501050a0207030602070c0e13110301060b 78
    0xd1600085501082c0075034008a21031311010041d0600b0002c1e203890505079111078020200904441c1c6503d002407508004000d00c13421030768080d48a03040951038000c8103d8490010112038000d070427480707071181d000300d0140500c000d51402400a1900103803440c0074080441c00103001d18014464038520805582c0c01600b0110031404007000c0302e445444c9842565095103000000411030040700310a0303034007900300080c800306181e040c480c0c403109648400c8001c2d003840c40410119401062481c1540e210070583c1807100f501c2070b4464040d205400c8000e40501c00011400184180841c103410390b010900018402c0131048810004a80954080c560700316401e010302e20001034030f084d001700e0785a220340004120f0314080c100540c2141c210601c054420b03500004c003056100c0352440700e0b00162109003400790811300c1440b4001c0d42c404082c0802401303960300040d80c03000e12041d0391243e40181605e1549007440d117410040840c1607440ca01086a40c1c00c2e00038095562480e040c099541503c1c1e03000141c6003052 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 31488575 1250 31487325 31487329
    0xe010f112b08061c030519020606030f0d1215030c030b070f0804150c020c0405010906030b06030a080a080c1603200a023109030503100e0f040206070311010c0e040f06030809 76
    0x800c4c1c1c3c0904809101b01009103140500002c02109800405500035003560f282450501d42405c101c41604072007500180c05900303e0030382144011003500c05508001818280c640c10182c10060241c20103803c0d4541d4200000400c004040c9203849241195900794101011040c161902203051303c0050207001402c20100140d107203540182c180072446d1040340c6400d514500070070100ca000313070840784c0d8407a101d13841881800400c80d4082e1300101d0550092410702125100e040d010b0003451603443c2048515000306515000c800161102072204c41c1244140700c24a2901030300b07000c450030001032800301d5240e041c1d55000d00801e40c002c1407500540070520b80e12100404800c608100c01d1f0f0180d17104c1d18400c036040071408078840c40c20854071a0f11043e03546d08005e07a9840d143c14255005405189041c01008000d00d103222507290040da06440300c50f00d42c001407606880e407286604603010b45600c4e10250710703c0c0030b900c09400030349200b040d10200030302e00f5011211000d030b628038000580b00d42010880c04002e8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 31489825 1250 31488575 31488619
    0x203100b012001020c010612050613150f0b0f0d0f03050306040e07230a060207060c0602040b19030605030a030509090604060e07030218100e010f112b0806 68
    0x31001498180b05855484202040702c0c1a14101408560743c007003000061071070244641c17000380a00d080840300300d14642d030342c1e00e60f03541005000386a4103880001785070801841c0d008621001c103070300740c09200505001e06140c00501d8035640447c4142c128117065600d40c01c006d0240c000850700600e000303903a4800c2d510300f60341d40d0740003811090300256614542c440500f000c4c4103240152110446400404804144842464a8182c0c2c01c62188016600802c00560002200d4040390a5400e2101d250341c0f117400c041c4028040c540c0000b07840c500c00144001c00c84a00c2500001404c0c031602d080210319143e40a150351085204002004210100300c010414038011b017446910900003040410090348508004081000503181000400e07004074401f9800380b6010030913101d4860664800c030340030800300001806001d0485445060104030500407850622450302c666010b4840307403c0303d4840005488481140315101022451009606100c0703220912941641d4010a8000c00308548181a40f0140c52a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 31491075 1250 31489825 31489841
    0x2031603150b0111100b03060a060b1e1201060e03100608030a0509040902030106080307031409010504050904031808030403020406080c0105030c0a05131409060a0302060a110c1207030c0909020310 86
    0x50240103113070880d505104101c2d0070004401010041101e48030740c01890300d042d402030000c440c01c0e410101c1c14000c90300c41c0d6040c0c038004c0a00764810880141c904050700c90754456020143d0241405000200d4940e4100f16070910b841810780c100e81c0f000c401060224121140f0740074520143c2c00c204001d49055100710090200c00400a10010340105a640041e085400c01e520034101604003081c040c041c91303001001c100602500704681440c2c22800e000084c034500c20342c014288500e0b080008941858814030500006c203102082c000313003094030f0f050065030305e40052100b02c1c459810b15501044c0c0e00300c045400c4101030b4040e160300e829900c80c2c1240c140300c2d80103c40045c0820100b408544801510031501d0f200410b6500e00b180100741e0400103000e94400002c0c5280d018200420040005848010031500c0c080004c0c50684286654600d0207410814200b0f450365020285030a1806800400700305042264811202c4140107503507801c020b41543d050110296041e0000b080196401c6202c0c4c1114034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 31492325 1250 31491075 31491077
    0x30c1009150801080f19032001050103030305090115030c15020a06141801021306050f0909010b09030c01080403050a030515041e180b0c0901020109050a0f02031603150b01 75
    0x88480c1e164600038002440405041e40081c05120040103802020b00118040b2801707007004d02a2408a0041311808890202000701000014007045801c1c000f03141d184082c800035803000780212351390703420010702606c4150344042c0746520744040311244920144100044a501100c1c08007054986050042c00e941c1c2c004402040d0300448242d07000003400d5228440051080c0901e801407400d0003001e1100064010600408030313031040104503201d840c1030840c41c00f2100589001c603030b01c40c1800107e44150003489019a0400a5140086034a40c002070242501800540c1142c1c00642d41c0001111046e4041d1005000728000b00059041b09100390881680064141070b070108003032038240800d088030106600d2414060300c800f0303145640700150007000440d40c15005e0286001540d9165172441c400c02070319882c11401c000445200350790003900813a000541002c1900d02181c03d03401d00c40f8101c125102d040388280a0070140180d40c0b03945080402c00d80341c0000303284c3c00c6911000c401c1402820000701140c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 31493575 1250 31492325 31492337
    0xc060f06030a02060c06010312050a020c150c030408010f140118050a090b18070602030405060406030e0a0506071805010302120a020307031b030c02060c0c030a0507060204120803090c03010902030c10 87
    0x102c050f0301d83c10b00900d07040002200501903585182410015110042400d01c1004001c01c0400401c1e40d000800c181d48090480304120395140311841ba42140c0302d80306403c51a0300001ca40001d2030503041d4059802c50402c1c0c03800780041d03444e140034600010424020a144102824140b400c0000282c0c011544408a003100050300806c0d6104c003807128608980c9146102c0e14165503082e101024013401c401403c01d80005e6092508040008025000742c0c054042016910b1160082c260340030004880400c2e04501900d665090014008001815481500c0321100c488000081c072544280b0844080b165040d201101584610754203501071741c0003074288020580c58807404442c0c08000403101601410301d40f0f00061210703543c04082d0408500406514110005100d2620840c1c4048102c4107041c2c51444c145035507003003510703042c1c00901403074000700078500c0306002403800c0090180c011409811464211000140c14104041c241c41c5203440003034158109403d1031816040c00844240c030200c16081103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 31494825 1250 31493575 31493593
    0x30702060a23040e0601020d08040308010512030d0e010e1603030905010c0204020d061517040f0305031f0902070c0b0304020d061505031005070905090c030f100302120d030b060c060f0603 82
    0x800902c0d0800c0c1c20100213001c80700309001c0d4660301046041002c140ba82442e503507a02c5e042d1409414040c05101c0c1c0e80c05260000003e401ca280d0900071100c42038405002045580c0100b00c40c0f5009007451440640d0038401d2911640d50b4100d07031240081200d13416500ca803242800c107001110348044565089030401c0d004d2142001c16007842c029030020b46410b502d21041c201504d80010518015906e04018500207403040c04089011611a9030105425050007a6a0b803140030382c0c080348a507661a100d64101240401080c039502c02c0d0002c0c0107070f50080c6c10040045845000c1803880e4807064134000d45c04181510300c02d0005115400c42803150742c1070089030381107641c0c07040840d04102511081c0003201d943d40d0100540d0030741000000d4080c080039104082030385411440ca680500c400303401c45150f02c420b1000600d00c0c015911040010396400b904496000700300f03103081039641440d0703c0c44070086800e00302d0600c400c2c20840e05827002c409544004002a40350041c8407a40840040e1510b0b4250250340b0305 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 31496075 1250 31494825 31494887
    0x60a09020a080d080708100f0e0c090a060e09160206040212010e01021b0105012103030504060603080c030712030203091e100e0706080702030f04170a0c080c0f03030702060a 76
    0x614002c0c508079469a084c203141144000f8280b92004000c0320040309242e1040c460002c0440c1890151006804101c000703440e284551800350207030081c80e0342c1c040c650400105016a20484081c10040141c0301a00b540d281e50400391a0464004034040050340300034001409842d00303041c2c2d16a0400410300010301100000850b40c203a07805410040240040b104030000c051009114039801044004108850152185401c08600035200380c05407c05132150081021700c141ca912440c011076001e01110341c0c800d084c4540a4880c0c200910649100030049249051140240201c038460900c2d20041c01e03c0d14071502c0700350358004d68441c1100c054403990890860403c810720640d42c80e010003900410580f451300e84024000000286201c00715041400401042c0581e10166402d840c0002c000104854481c401340e886c282c203003013002c3d0440398002d1000540300d13004641800c02d4a002e4608015281d0340da0140750f585e1051080c001e4014504010310b05a00b4030800c040b9590828103091144003540d2412 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 31497325 1250 31496075 31496083
    0x100306020c07030302100b03120f0903031606200306060703050d021605120405090402130b0d0803011d0603030703080601090f14040605010e09011404020c0f0114010512060a09020a08 80
    0x3072403003159030101d60107105054041209010200042c0814012000d801000c02e48804084c0d0f44e0380c070040c5001c40c030392034a0150341c0c05461080300040c0890b51a90100c0c200d00c10446010982074442c80c0c980204110f5502c0e00140022034030700705242561464440b0024042194401031050701001000c0c40302d00c50341c02d424001004200e1141049048014003818101c0c20440100913142c0d10503020001000151613800f025039009404a03105020300c000c50ac0444081c1c444000d52552200b001e4840b20208600280518180e41800013403101e40442d10094200c0c3c440d003941c45a615a105003d010002032041044607406801071511030441c036520451200c0407805a00018140d841a01c030320101410076100d810024942442c0640481400300041102e410060040e4000741050a04030001500c99404032002a01c002003120411403911103003500030540e084000a0b00e1404400020b03c528000c06a070b6206034016018000315190b402c1400000c111040c8103d8001408510006c1e0144040c4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 31498575 1250 31497325 31497337
    0x180b1317091810050103060602070e010312031b090312090501020a1202070302130e060c090d020f0102030913050117060402100c030c080307050307030b0301020f120c04050402030702100b0102010603110910030602 93
    0x101103001501e080c81300140589420350424011580980000c0140104541c5486c0c1183c0d0051442c9003241c0d01c0a00c1100a08462114a560071680f4a4200301481c0e00c00881c0080303a01401c3c0c400d080c181060400c8864070847d10070180140c3c01510610045a1f400034940498070300c500444440075980c0d80404c080b8090620701e2160140c1c0e4140300c8001107400d01480707a200041e0b1808929224502c000035002505c9568040c0c001c44019802032466402001200c0c01031400400b803038000c003074118145001e030509000d54000d1041400000d00031040014045016590091040d0794400105104440c0c00608603020340810a2001c2203101051b8010300542c0140c4169454a58a01c4d040b180038003598086654580607a00c1040b00031440d41c0f0135002d540702c1100c00718102c82262104c220302242806140c2089034040d1000050040140c0c00180011000b04201400d1040340f07801001a800c850041c4070190414500e401c80c03015030301c2c2a2a0b100e0f884a04c0c0104003011944a846090480c0c0041c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 31499825 1250 31498575 31498591
    0xe1903060b030f0a050f150f0a1a130b03100c14030c040e0a0203010602060f060102060106030c0e040213030b010b0f0f07030c05010905010c0207090908090607020105040801180b13170918 82
    0x1b00f0200c0c0405441031201984145c504410700f03440c5c2c1000b01c000d00400f00020310200003c2e90310300507840c00745041d4007484049080107041600843c0c106409000408007104524401d20602101c01c8012005000303030503041d5099100c1884a528100c0c00007050b500040c00c05030305603410080413522642c9541d8807401342100c078000588035810160042d281200280000501640034004c0081681c3d0003c0c8060544500c0d1a0105640001d400159600d000303e03000281d1160000c102d83c10303c2c4c42120400400c50f409800b414001f6680c0b0741c502d030503071f100d6040d14081c0c0c50390070010b006042101d00000c050003886840d03d10100c844940f1054215030450310100e41694458a68006103a41004620050080d280007005024003a9442d04464400c074a803141c0220804501c40065a00502c01d4400814250000b8000941c0c1c0303011000d1400302d80030f4102c80440b141c0c030100d04103410746201c05803015440105a58201c00c01146210fa0707400c01c40c42c041c1d20810101c503d008024280070168062210307 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 31501075 1250 31499825 31499833
    0x51c0801050901290d050a0b010e0f01050a0309020a0e0405120406020a030f090306051005130b0a050f0a03080c030310060c02010503042409150c02031312030309120c030e1903060b030f0a05 83
    0xc01f10014054500620040381000044074082c44196542d80c800e0303a13201006d003007080d500c8059001c160094801c0c408041d5000c111510005509a035a0780d08500c61489282a160040c10b020310000c9140258080d0300010f034424180400000d00421700082c103102541880c02d4155500d03030700c0302e0a546045680040b4100060810412428000000c3c02c00010707045051000c80501404500c01c2e6a82d4030071103104005041c9410010345030520b0f8a0055038022424a5507420b13070405160303503680141c2d60381500c6400000c0c0000c0d828445c40d040c8012650507551740c0d103140c0340c0b501c0303520140c0500382c41801c503001c1006001d0954a00d80c030910b8411842030012078a43c1d054412a20200d0303080c0da220710150b4004110140f0ba10751480500c0c0700b6a0240d00344498685942c0c1000c4008107400c0500410341106080c85400d9560058680f43d0810721039524095030350440014000004191010b0382c803644050181400021240c2d0421942c3c5e490143c00c596503420320100c80c40c50b00d2083c140603170709900 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 31502325 1250 31501075 31501081
    0x4050a02090c04050d0f0c030b070801080708340b0a0c030e0906090402060d0b040507030b0f040e060112080f0304260703090302060d0e010504051c0801050901290d05 73
    0x180207420a90280c1c00d1000307903003030500d00f00c085172842229201c006d1200b4909514101000054164a8050341e0006241c15191410f200c0182c5484805c0c028071100e0701c1180000948000b0000b0051464140511102440c00900c542100c800342004070030603411600f4040030403d81a40d074081e00e4581425034034005d00e030545040192199000540c0640180c00e05400c018041e151424510b07045a0b05071790b40c80d0780d6140d075082e440043c070542e00d110b98807d041c00d043c0600c6642c035401c801c801100c229030711a04031a90700204400c84403084d5080c2101d400c0180100580c444204007000400d001c2c0070203a150141005016112340d04c120350071140000e9405000c1c500454100d0403081310b134080c9169924018254401400f04800f0b8440244610310008a0b2107038208203400900210f0514002884140ac05160094850012003903c0100308103101c1c1d110502d610030040f1038120f807000b8118158036402d10442490354002c00c4c9a8040030b42d22100342c103000c00781075402010341081c5620001140d003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 31503575 1250 31502325 31502329
    0x7140f061f0501020c0a140d20090901020304051b0f0604030b010608060a060215041e0f02030607020d080c280809150105010e240c0102090316030c09051e04050a02 72
    0x15030710390007841c110f40c800100c0521584800c40c151003078450b080c000321011701e00e000c0050561480e41800810035516001120f080d00080d8500c410200c8040303541d120039039142c5051708c0c200d010813a0054882d92051910428003200500103c0d116480030300b00618002135500807a140d075005030f2080b1a00020b903401080b0070741c0c0c4102582e80001701103500310900f07490b02900070355699110030342069251450780800d0800c400401c40210900c000a85540c0c00c840368100f50501030b2a00340168040c1c051140040c0da00e0703201040c1200c48a0441e101c20020303840b240580c4009400c864607c0c41703642141030500c803d40c4900700e54501800015650071401b031420820300c50030000214468045141181c1c018000350f1780041c050110310740c0c1541d01084210840032204040000244101041c120002d03918244140c10740051958140c142c00300d8440a4140383c4c0c0b508400c4162001911001d8811402d03c095040c5810160301b0100341c0c40868460b440f41480108200d00c01d41f01110071fa0b0242c2e41480c01c42c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 31504825 1250 31503575 31503631
    0xa051b0901081216060c030510060809030a1b060e071a070305030c0c25050906031902010c030512070c120201050f0106030c020a0503030f01050a0e01080307140f06 72
    0x400c0e60340d4440e5500d07100e142c0d55550902200044000e101184158590000c0c1140c0c02c0e03400d0300f00d03109202070340022001a00801c8140d41c1c02000742005023000c11382c0d40c011111107008403440c1000b1403500301c4000c4100d4903400506014000d0300010103400c00801c10b00d010700024030030617102070040185001c00c89003801d1402d0b81c6041e40d00106002c0d98012a4021080c8ca034445801c9000c070360b4595410f50490b0030600840032030102c3d4903188810214100b008420f42d001c0c1e61003611805c03c2034880030101030391807540042d150150305000c00c120006510070070216405a2003414218108540c0202e00d42e070600b0101d4110000400d400c8040d81406004000c10f400050903000807c410300f800c580308200702005014420030300d5141c656241c00b551007000b41c1e003505074004040e2a00ca0504404400e4000f1003845000d200d142070b0380002c1194149548042c0c12a000e182c000c5141035100c0d9200644506000c0e61003645019200030b100c01d11105006040c4107058018101d040c0508441c018403c0e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 31506075 1250 31504825 31504873
    0xa0c0f08060a050f011202030c0a06020106210b0402010309080d020301030b0411010c0507050f011103030109060807060206160305060d0204090302280c0314010213090213060c0206030f0411030a05 86
    0x182c1d90414080c824203905000c0c4c2c40d8195541d50421001d00c602c14004641b07070410070603050f60050324400c000103482d40c0c10361240e07090b6515415810390001c0641501c03205110003040180491244c94041401903000768040d02400384250701c800d00303082c1c3c0e882e424400c0b608260b2007542c4001d001c90401013003010304460204510000d0070441c403600f4032900c17810342c1d507100750040600414007480c44c0812a030084924051540c806c01c1100d03038a60b116429240504020310842c00140f041d48c5000c00c0090001c152a44280008012405844002c080c00c9001d0078026002c990002c000480c1d000150301c0c0c80c01200d626500a40040668000d614802080120301c0b040c40e848910011104000140c0a060040101c0b0380009407810600341c410107140c024452000da00100c0000410001107007542c50300a4286e80c0d001100b013444c81039980c8415510081c104c41d000b0342c0604200006040f0121103410300ba04203018680305144140c006011900c8c3c040910010340740c2d03a022040102150b042c07d03080c43c40c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 31507325 1250 31506075 31506091
    0x201050f010b07060e1006090b0a0b040b03160e10020c090109020a17060301060503010510030c0b040612150b041403010510120308180304030b0a0e0604081b0a0c0f0806 74
    0x5030075071410184000501a1120080013961502d140400d031110401404144000c00482000205c2d5500c82000080440484503809091000b81c0064685507080981d0103c1c0c61841a492540c0e540d03403000807034240301e00d40d44c82c01d001079400d120758140c4074182c01e1000440b01d0380040c644400b48004018040b503059021002e00d5004018a000b640d60011402181401f094004140ca8550300f0001c3e000d0312194006a0700b5603c0c00080000318051040c0c05400c0740d01580303601c0074258130f400d1481c00c140304a000700c1e030120314401c000d43c500d00102d0b0f00c011010320031402e0103034800e5207031901043d542c1d200c0d6100d01010044501007401900d800c0c8159500820030100c7c001c1481d2421650481d80340f0800c0e40501400302030000a6a140344d403a090554280318502502d17a595101d141c0001210016619280b20603e0103540a80740980083c1c040d0203990001d80f081d040616800d00d00001d04006c070aa01300a00609501c080002c401c840008081e220b200790740610316082c50322091500900070b041c95 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 31508575 1250 31507325 31507351
    0x2040915050105040b09011704050d1b020f090c1b01020c0c01030603050c06030405031306050706050f06090406020a14070f02010809070f030210030e0d0804030201051308181c12020105 81
    0x1d07030307080003c59085466418059880307821003c01030f5101c1b101040c0345680803141c10104000c022005c10310f6600303040903071510445506840c5030791000c0d94400000941103000000c45030280d140c031590696002081c144618074042e81d182d980041c0c1c10044032880020b81d00480c1201030344500744512104810700f0302e4208215890364841541e5446220b0310240540303000004071381400000c1c0b00711020520b040e4a403000361076403144003d156504c8120251049443d01000c00d80c030125240b0b1aa004450040503c3d02a80b5551501c10003507101e586030303c080c00071032800341001c076911802608404c0d0007104441812000d1380009400c4a00040005029030010341c003c2c0b100c10000e0110760180c94046c0c0b8514111801c40310140c00611401141c44203038822001d00d824550350020300300d0b00c0380307100b035000344000c0d00c80c025545554142400700500031442880903040483c109101c2d40b041c40c5008001310308440c0c10350700d504c8900c1d400700415500a041d00d001043c90a070240035094010380401e5080e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 31509825 1250 31508575 31508579
    0xa020310110d050405010204051503040b0109060608040b07020c0312091201060602100b0303040308120a0f0216020609180708040b01060914060d110c03071a1608090f010203070302040915 82
    0x356035442078504054840d540e500200e005c0c01425415540540300181022088500d907941411458008550454006c05980b00108118041f400f400d0304480c10750710b4150a680340da5407400c2420400500c01c1c01184510500c0749920b0303404018066100f030761502e00543e9401c0480900c8088640c1410246c003e1307060190400c082d980c005072440e41c80c3c50300074000514410b40d00c00241180700315440075040074008100c0010144c2030700461030140701c010204000605240c841181680190000c00c5580d000c030340209005070030302d0b4000700100c04005020388001144c9102d5150201400c0c4c40c5000085e03130501c108800c10a040710b0701405040d00303040210b641c510341030004030701030148140031303009101c08640744001b240f094004140402200789100c0d29441890591940d940050b82d051300c9086a4281001c5080740300c1111a004ee00314005000646440c01000d51311b420001d407031400e95100c0c8528401c5a81d40a1010b0340c0240910341d40542d446242c0401c00f02600c0140420503036000e01980b00b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 31511075 1250 31509825 31509851
    0x2010f0b090106081305120c010b03010516110106050405010303021f05010b0d020c0f0604060c0e010e06070f0201050c150105210a030f090f0306050901061d060103050a0209040e0a020310 82
    0x1086045a050313142080060b40d444810031003100399072000404511441d11665524174415011b04041150040200200780e403160800d400e9440507a062009201d5401b081084244500894800c0806010000c40c2c910380d210042012241d007640207a0060b00035000104164130b40899007849102c0042061100c2e504002c070908240c421040e6901c0003d50005c3c24410203402071150349004202ca0080e80d03034034a024104400035240c1c48140c0000a43d107200001300946c017502c01344030f04110142c4450f00b0050070780d980d140b54070710100091b4140041404080b00046040002596401903801c848035954500402c2c048440c4d00117140884030b0b9443c3d900c441100d00300050380340d4040d826180124005407060b00555050410b90000510095009008414824290001e5000da11114001c108007603a07809071070650000c41c1e102c0e1040740c0390704000c07414561003600001d4001c0003801d0014601600e0b00001811110700300030300303c3e141d000551035400f54903040c031410200600c0c1a40074401d824076107003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 31512325 1250 31511075 31511089
    0x602060c090f03150105040f140103020d06060b0703030906060f0303050d050402011b05010e0f0708120c0114150901050102030c0a030311071712070311030a0f090c09020a02010f0b 79
    0x205400620001050140301a0b6690034542001c02014003900c002c08000100565603220074060030b4000c5040499a4541ca1901e00c42d5074030b194002140940242d0031075007007003da40d00c0c3e400305450041d00d9107404910b0424035001884850f10945002400007410303e4071384140c807010760204013024040b02003000800e4015013140c02d1140480000542c40d6260701c01070302e000c0b02180c203112048940460329810000154010b40c510603003041100c440880801c0d17160340e9000b40d4013510513640c0140d9012503a170b81c200d0014182e5400e640340040352458039030140313500c00002164000a0000541c2e803142c0b181c14620100e502400080c070155143c5101d1390311060755207070600002010156140c0914400c200e1040035160156488080d041c070b000020000c220740c40d0480300344428202440030202e030f072079400b03440f411104000c0030b485c4d1402c40d44c0b42c02941000384242c04081c454240ca44840000259040c46003a020b4400c400e00143c0750280c10f0402800c4a00301d180380d04403d8500b000c1c0b070080b0350380d40b1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 31513575 1250 31512325 31512331
    0x6020d031404030e094506040f14010b03161403060403140c030d0905030406020d02030310061103070c0e01060216050609040e0a05150708070f120b0a0e090c19060206 73
    0x40e070444c055845000011010084151140c6c0010310a100c6840407000d034102c03440a420780c41c1d000081c0300c200521113151a20700130385000302000415100a800a226104100c2da40d0629100000382260341201090038421441003803c20340380c00d154140150400142c0a402060050b0010105032a103a98041c250001020151112200210703407840003050420854255424080d400d0042c2141454619641d030014001c69001d07000e00c0e815250340034030000a5a210b14030343c8404e40030580c9024001d4803094200e56500519000401046c0003007848405408002c02e0613901c00c041961420f00024103100400020310615106103408020356960f140a9400700c0794100e40014640141c940010704d0025030090007031080c00390009420b1020005084c0d14880c0c00c03181c0741c071505580c4207034044503d0902412801c0105117034101c0401748503643e506c100e50340c0c00041c082e4008252124402190803004503021032072903110400c91103290820400b01c100d80485101c010341c502d030270903c010303444000003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 31514825 1250 31513575 31513579
    0xc0a05011803060f0515010804050606010e0a030b07020a1101020c0a0302092e06030c030b090f1005030f060a0b12120a050708120601020c030606010c0318090606020d031404030e 78
    0x11000e2402400c0c00041e100010b5038403c83c10814902030b103049001a04084405100ba41b207101d00c6081da55008208503441654800050b050954804006441070b48802c0e000300e800c0500b241c07010000800144a0300d000b0001c640081c440e0b549607180048580580d01c000904642100c2e94609003511001201c0050b05d03030403540150540d94010192400c01000c0000c0740c410403c6d403051310180888884a030090324002d80d81800701008410084d0260362218690a4112400c0300000c0c1c071400c040c5c20b4040d0071901d8480760301310703241e906c3c400a0b25040c00302c01c7c804015000b00c414401034020b64403440c02d58500540b625070352480c19000c0c90b40c43e80311200498a802e81700154192030180b00300d0840746000ea01050458494001c807004900c3c0c5d1008450003400351060380141f02861400040d00c40c401c80059642007a298696941210040e81c1e59025506c0705035141e4002c80d80d55614010203014002a900070404810707000401000d0754507807080c607041020540180804254007040c103900590007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 31516075 1250 31514825 31514837
    0x30206030a1103070914040203060a03060c121a01020f07080307030f03060902040b07020148060603030c1203020301060206010e07050c070f061d03030a0309080409060308070b090c0a0501 82
    0x40c1c41d06240604240018035445490000c10048003d4103d0590304c107a416145041c0405010319003804201c0c0b0080d02e03001e6120720355500c20030000307a0a03007001d0030041c0d052511405c20000280361809640c0300307a040032250182c8103050030345943c2c104525500340c0404c03001049000e241c600507035224030400c500034041085009944540307500035040316004002400381155100c1d5209642e114517040030304224000364518103460014020422030198060881000a20707000750003141c414041d000c910110001e203e2036010341e012036828800c8038001e40c00398031400000009880c15244007072580125205151050006002c810343c00504941550309040180303031203444002d810388242c0110213140d0300500c0349400120f1904030030540141100c145845081c05c1c240e0b0454501441d600c1c51141a806501c24803d6112142c0300c0d8000c0c6654500031040c03640b605841d0b6182000b501e20710707041512000e00009802080124101c2260340c0009210041c1c03d130144200c1c001003000819201c0c650400030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 31517325 1250 31516075 31516081
    0x1020403023a030c060c05182b0c0603050906040b1f05130b040b0103020a020c0d02010e120102040305100204080a02090405071502061009020c03040b1606021206030c01020705030703020603 83
    0x1500180c00300c4074081001100003032524004000380b0380311360b044507100d04101070f001d001800354007644c640d0303c280882c65803031303a4100040c0005041205046006403609440450516003080c40d4402c4060095680c0301d61107003030800c0034055807006851f405547d8481c604020100d0a115846900444503020b81440700c074032040e49010f170803c160400b6610203076141910600e0000c40e446079040c0c04c41694184222291800150201e003e409090740150300401003403041c3d480c3ca0181c9415051050501d0205820017801041c2110144007500101d40e60001e4180b0500000300700b42d44100362843c105602c1c0c0750038004415100c0c114900c00a00803489080810200902070100c04080c03c0304078245491075101ca0b10007944e4400c10745071001010071301c11001c01e20300c81d94000c9502d400a0300c00214a45442c01045010a5008240b5041c410b100902100f0000345103000428000407402003501490034900e04042c24030000c140300034159400690300300b005840100e034503801c076901103500549a076 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 31518575 1250 31517325 31517389
    0x210702070303140304021809010f050705030c180d05070806070305060a050a060804050c190e0606030408030112050114010b040905330a030b011706010b0a050403080705030d050c0d0c020102040302 86
    0x40a500003c4564506420401c08d110300154410200303001d44110521043d180c000041c1c44501c02921341c00c03100745042060405204c503601c21015049000b8203160082d100c1900d60506001c01c40d081f02d0295007204041c409070b0340d49401155005101122078954081c03403c4005448801648503140c28010203100040c14440c007404011109000640542e800503008011180381403030901a8034420b04022000c23400500300b000a4038030441d40015100e02d540d080040961845461041c1100da6640300c4050b00c6400303007040411b5000702010320000703864504201c2e0100c16503134001c0809220500529150030f410807452042d000041d81254120b409003c207030301240560311650030107040780e1694400002c0031404102c1d0500100001410b88040742d0321075450341001d00c2070364909000100284420b0005c00c100b01c00402c041481001202d02c0d096031403480405032032040314062034408000c100010254014001c075880c44506100840c5800d05650014004000c943e55000c240815039002031056 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 31519825 1250 31518575 31518589
    0x50a061103070b04050708150402060403061e0906021206060a020a0201080705070b010803120705041203120603060f050a06050409020105041e0e040f0507090603021011070b21070207030314030402 86
    0x41e03800540f041582e1519085c210742d680031a10a07031100344904611002409580c0c82070b980150b50041486282515540301c14014020340340e08809100f0098240003d02c020510440101c1e40c8582070158565402d007101c07c070b036a000104807a004e0703030b42000707030118560380170540c401510360900b8180001e813264007003190107024146000f8612034030a4008194210004003800c080f580808000307969950b151002c5a590165110b0b0311541c0880e24241400240035007204901d0080510b8005540d65581d00c45505070342c03921131002c0d50113a4a03c180305c1b1082883c0103e4000e08000e407000d02a42c03e10ba80020020b00c910b2081018002e00840300c07115004003103132100018102c4000380b11130344c1000d00704a01d03401c402010031900d52144da140000c28010b10302440c0c084a40040528000e9010a403050b92051950807180481c3c1c00b84a4001c07502451381400303005002220281107014158a0050034503417100548070f00c0665100c16801c200299000c0300111403940740c80c0303070380c0e0312510341d44041120 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 31521075 1250 31519825 31519837
    0x102210706270803010e0c09150306011202030726070e0915100512010510050405060304020d1205040302010809070b04051c05100b03010f0b010e0f0f0603010b1207020304050a061103 80
    0x1442c01d00c0c98100c0240041007000d0360603240d5204909425449404c5640c2d00c601c80d82d010550440d40c6040500c01a126401c041c640c4800306040c01508240c10704c01e500e04a0f482100c500020440e03c024008120402d03131440500303404031403848481d6082c60b40c80a40180442480b052299001c1c0c800100c0e40451714103480ca616001803d8040c440c090214060001d0700310441c0c14a10b03410140c0001050b1402c0038011070540507075111140f42505113400d01207603030300040090f84c20440d501d10020000e110140b0030b04440180390759498a45080d8400100700c100081c103031205035400303084107021803c04101141c04491003120101d2910b2039035041c0780c140003690300b005030803805000320781244440d00350000b84080c0c900324003c21800c105010801c00300c829407010700b070001e40c0d1140c08404500b81480c080c03c10718001400700d00d4001c40700c0300107101503109800411515202183e0200c00c0c105400513141c1203116070000e181443d040101092601c100ea12a14042040c605102c0540c847c048c130444903 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 31522325 1250 31521075 31521131
    0x9040207080a0f02010605060d1a0d060f1401030b06010c21020a060b121b0d0f0501020901020115030b0609100509070905030705100903060f140709050102210706 71
    0x140360400c81c2050080d60300031a1a240100c0c01003c03c03908424410312940d02a100003c00c120b08000c81c00c181c0600030541d8125080600d18410b282e20115594a0003040305a0700c1050041201c421041410040d900305001004d4440704010051000400620f20326500100a1820215005443c00c084401200380c0b4404c0e0b031215010200c18410f80c1d030104100e0b12440c02103c041c40000107210074070960103241d150402c0d15411811200c0050300d4bd0742848084458001c240c42100070542d1520135030300ca1140d004682c60385d80020b080c00d242d40c082c0074000d40803032240701300030700303180703036840f8000d1441c0000d020720b21a200000024032903400c0d141550000d45000b034070005a92500c018044e120001ca40503c91107441030200001c0c072480c0076544441440210390342c0300020b526640c1c0d414080c2a00a400d01002606c8181420b002010004500d104a013150394107000d841c034050019061400d84400502611407610070044032581c0e20f012500e401c2d61008001440c0c002a9001240c940740c841e400725 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 31523575 1250 31522325 31522327
    0x40207110a140108160203030a0b0402040911090a08070608040303020306010314090606030106090e0d030908040905071206080d0c260f0c0c03030c0a0803040f020406030f110405040b130503090402 86
    0x2141c4402c5624112140c11000e0321041c44948a00c10100c80da02d81e00322007040144c0c81040001c002c4500c54222060810b40074202500b402c0d01d0310501c109032070420791240c0302c4000208620a4a04e08010b1007402409088042c0c9400342c01c141c0b0007802c0301c000920280c1410f4000000c40c440c4e9100c0d0380f201c8155010b4018151140c1003040040da2503180a459551082d03003440c0001c42d4000c010700c200040d4014910003443c41140320724094001e0104a00300340c5d0f03180800c0c040000e00c070029008040c455151079580004942c0740308411411104650404800740d8456000c041c207907070700506000c3c0026001100d1020142085080c9449003050b070f8180513140c5400300b000c080220081d80079241c0440f18005444030256104103040e524020101d0074060b96104808120110751820001d5811038003031668503420602c1c6402142c1034a804d54002c5541c400801011800e00c42c072642083c480480448041c0720a08054840005210000d049c040f203055081034502d0410008008813510b1600141c425 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 31524825 1250 31523575 31523579
    0xb0f160f0c0f0602010c021516020f01110a090e04050304050f19081e060f04080307110d020d030e0d081501020a05011d06010b120f061201140402151305040207110a 72
    0x685001070b5200381c10156003018080b010441c0045248800b605014002c81c0c0150340d4042102c10148840611780254000d00055542d0b00c41c0a00440e40a0b038014050a95900308880e401800005581e200c164503010440500000880200484080758000c030303a03a07080300c0340c43c50003e030f940d0000c0d907685211001e0a0000061841011031420079641100c00c5010390060040744039900d4ae84100da02c00310000c80d07240060001a0b08101845d00040545031070a400343d010440d0302c1c42c21038801d10000159200040c0224110303854040d881c600c80890002d400041142318010f080c1100c040d01d10040c1040309442444503074400c0101c2c404054100c0001d0002d800d041c980310f031081c030110341c106807070b8000c440000c21b00c164540c04844112680c035845079040d0f543d10900125240000e00302580c000d20110291194030300900600382001d0064462080d50300300343c410007900c0055000c0c1e800030340205110315070404120080c48001c8030000c1e64090303a244081c3c0760555100c1c0d41200603a0380405071b10f0f00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 31526075 1250 31524825 31524839
    0x1181b02070303030f140c030c04030203060114040c03060602030304140309060f030114010201060b07081305060f0d0c09060c06150302060309070801050903071203092103020a08010b0f160f0c 84
    0x201102d0207a2002c01003000c42c21a41ca007035900940f020b551b00100403001c14034001c0c165000b9680b11034800d4046003410345035400281010001e900031961000c141601804030703d0188941c0b0b54101d8681010860780d443c046000c1d40304c0c0401480070b841042400c09887c40107606008032440c6403801803010360355000c0741c0300100d0160802c0c06a80801d80b0146040d1640303500510030712065401e511159030900310301e0340e1402034680c09154071044c501c10301980010b603030311081d01401380c1d0301590300e0007a202c00d480f20b050401c0391a4800e1130b80c100b001c9090304012194115000321505500082e0100e1181d40499264910200c240e01c020340104000040000c1c500300400c0040945540c40001e212030307254000620340d240242280504284100a50b0301c100c0d41c003d9100e490307164840c40200583c031101110038100b03d0f107006075540100303400284021405901c0681507001d8424008420709050414102c0500760041044541c8903200600001c5c0600105c0c00300740e45400d40c011740041c0c0c100d031a034403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 31527325 1250 31526075 31526083
    0x170a0303110c03070b09010908030103060b010f0f0f031d0601060309020306010816050907020109020904050c0a0b070807140f030c0304061704020f010806041112041106030403050301181b02 83
    0x401900024603200d241a2510448812111400701c208000c506240a0352115041e148020301035041d251b5070f5a50410004940001030350003580140300c00541960688009000009034080c1c002c20480b2410091a11503000a4510a80d01132881c00107030502c0746141610300103030018170455042c400c0da0000280507506800c01e83c005442a000d41709140da0b280c440503030b95083c080c2c0c03084a01c60300c54401c0c009810100b4190382c0c841410300c00401c0c901000c0c0c011a50720781d07040e6000e89841c1c00581d0741e049181400c051b190300600008013841c0c5040c5258840071601e00420720000e190700081442c601001404000c4881e03030120040c2626500e001120325165240d0140c80f400f80404c1d0421020190541c100340c0c0c092143d80c01610a951102c4035000440780744000810165006568002c201d07025000c030f1000e007805004030a01d201b1141418101850410220590240726150802c10000040e40c48010799045400590324450400b45500c4084094012a0000c2c5403410b41c502004055981c005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 31528575 1250 31527325 31527343
    0x12060411030706080f01140402071e05070605070b0402060d060803120106030c030504050c010f0909020f0d05090d1d01050f03240301020406092603040e0405010b01030522030917 78
    0x181240c41c000c2d503403d010750b00f040c821170340100c0318070300c400041001c03000d0350003501c90360f480042006180110994440300c417103101d059102c00d050001200601088400c0200f074003e007166081240c01d20125540b00c03100108001c0c03009000e2600031602590f030317070420341224001e0108001034940300c40700085200c41001d030910801c00001d00701030000b01018041d2080c580504e411102410400b0140001500c802014205250070411055400155040548081c004003103c50340d041c1d42c0c614030742c0c8080782524005010074082d031700046000071103540c01800341803490360480308101802484100585113800382c1c2c3c5018808181c0001080705004100d90b41e08409240300481340158460300c01030500300e0207180160004a42070b5001807190301d1040341e1000c403c85000c3d201c01840c07080b512119003160481d40c0034008c45882c0c04140000c11200380901c00c9402d50a2904000ea80382ca042003000040c03803c0c0701d00030b6a070400001002450710a072104805001050501220384039003001e440c0ea80d501b46 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 31529825 1250 31528575 31528579
    0x50c0405130c12111012020301090b030f0d05030609070e040c08091b03030d1503020604030c031709150901030e1c020c011d1c0501050405010203190506030d0e12060411 74
    0x1a18040b542c2c001d41043d10320100c3c2c1000e01120b18138006014041c5e40c03c05005d482042c855014080d005407100b0740000d40c040d21403c100402c4c6038840e1414149400d03000f01c80d684503a001603202240880d401426607500c288200e070380c1407181e2a800c10039282034031100741858000d41400c50300c09059070840ea80a00a213800710860750001e8038003c081c11031442000c140c56042d0000c01280d81508070316040040b152a0019851015175070742c0d400070394641d1141c1d000315240c074032281c1c040040c40020900d09540104401d03049240c112041c0c0045c80300a021f0165032044600416021030380c0c1d10075401065103a403e81c0840e0b078002a5440c2c540c5581c00107546a030014070943d00c4a01403548684c6083d41156104441000a40481d10411465110400b0450104003807074264902150090080c107000f503014000060b524207107509003240301e03407c000742d46506a040c01e050050a88001840403203001580c03400a8101024000060b9000041100140c56216450501041c401e0351000d9103211001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 31531075 1250 31529825 31529843
    0xc0b090a0503031c0b0102070815041a04030e010c1e050109020901050301020a05070209180d05040e0709050904030e01030f090c1d040308040f1712090706080c0412050c040513 77
    0x156608040e0f40e0702c2000408130362108142c41035039002a594000900d43c0c075050068402003a210b8021030b207000f85c5c50f107200440c2c041440030700090107c44514281c0650009030810824a002d8030050b0134100650f008034100500d5554260500c407480e052403100310b01400311165011460304019018000910040c0d03c00e070750043c000aa40d240500c200e40c8584040e8031513900b407408507003c000030401c0051034030040703400420540310303040003d1010304801d00b8180c135081e45840c24401d48200c24207008107000140004504140119610301002981c003d6040c0b404903002042000120f0140600c070201c140d02c503082505040400c051203042c48140d50055001207401250241101c00c100c0c1705660140108080070013003004100c461078481e07200b60242d0040b0300c9500380001c40b0000c0750301c01c0100d6417000c545142445072404091103050300901c03c0d458a04100d060000b180d510600c25842460810808000f081c400c02c1006d0109108861000300104024a41802c61000c4001c1651044410185c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 31532325 1250 31531075 31531079
    0x40e180601050316050411040503120d0c020c09041509121205060d21021f0c1806090506181c14060702100207020f21010e01020306101b0c0b090a 64
    0x3c0010701c1d003010380a450a10000b0034030b8902400020840c8441c4507403800c07800c1102149989040105512044010503415175400c0c0040408041f10310f210604011508402c14400860707447c449650b030016008070110111550604641e00100750452000f05502c24115407602d01ca81c02c0002488002c0943c5001e001e42d540302d000f00000c1c2420100b0040580307019442104001c41401d810b1030808a1600442e02040c140741e140080d404000120004181d40b02c1c011450403e80c0803109040c500030050074094000d00302000501140e4450066500900c00426144a100c146180760303210300d40080c1c0101c034141d1507000d91144100c40d000040e125440c41c1c291203403280310009074080c03288070141d010b000d4650f0035602460196004035400da03805001c08029410b00c0c3d0380c408000c4144c0e001c005188400031504116039080d00d03035810308021980d20620401006071100b228814500c00c0a1802da880e0402042404402c03c0000c0c20150401d00c03c1d000109a0a003020001c201a2004030b4003c00350710303 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 31533575 1250 31532325 31532329
    0x3090106060305040807080306011205010909020a05040e250519090c09030503040902032706010905060a080c090403020f1c0e0616030e030715020303040b06090705040614040e18060105 81
    0x20070a44e001003956904105540100b4940e0001c1c5800c0342d01490b0155600012048038000c0e00c1c000e800070380350541d459110ba821880c0c01350301e81005010a46042c4910b0140d5a01070f41c548010550f075081d4030441460160b1850881006880030f01002400b90300c0c0d110341c0341c3d020304050026000c0c902c803d030300c0c02d0000030820b4020b4032407404076030380100298501414403005202a400113004042c170507141c0a03c40d00c120321088800d00c00122883d00400d160746c5000d00010942d10050105800f8180d6218240f001c20310100b25a15076107415201c0c1d8503142c4071854128070300f0204032461045800f43c00310760b89211050000b5410404059540c072048001180d04001c100e108541d54070010083e401108400a4021030480409200c020184c85007569200c0c005051940c240d10f81400603040002080108400100351640044094451205d14a0204c070060001e100d0b0340aa4030a0117850b40e042199035602c1c400f160301408a03400c041c4c1260800c03100c96420044042c80b100124043e400000c5814 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 31534825 1250 31533575 31533581
    0x90a1811030114060901060f020106050a090b09070311040e0405150403020d0806010206150d0510020d0c0305100602070e0a02070c03030503091b0604050d0204140c0403020310090203150717010902030901060603 92
    0x4d00b402810729203a640781c04815581c1841848099081d95220980021955a0300c81498001c006036a40401c00181800c204940002c0c0200a1010b0504c1c2044030701d003002d4100c09540540319940040c42281e100d40c10202d2400c001010050340c25a55401000b0816501107454200c050540c1c4544c00241c454400580c0c079031104591180051214003000d1b48140303014070b5600322541c007450a81c0d80104002005d0720503603200300358030604942c85c0c0c40004541d9a046c40780e580d121428030011034640d8244640252a2000e920403a1480024040414803694282c0e0491310b525a0203008010540d41d207184c0a080d50300204c403010320034081c8001e88054245543d6980c040450003d040c41d15060a0030f00300075000c5d07003140b010307a00300c2d0f034540140c3c40c480801d180701800baa2960b600715854510f5481054a4a40c0c484103641c043e42c00d241d140f40050b20300103800c12000680f0342001388296103032401214240380300f040882d042051113000107202c000a500450003045190001e000030303600c0300000c0e015 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 31536075 1250 31534825 31534831
    0x80d1e021204020f0111011103010f0f18020306061603030c120507090314011401171213030201030f0212070305180f0304030f05010e060405030c010b010c0b06090a1811030114 77
    0x50404100d0002e401840c01c03a03a1181c0655050510f01a410105102542100c2100288107401000000144940800001c07800001c0401101112078a400d015080c43d40008a482043d00d103070700400440c8581d034900b81901c050b08030b1902d2101e03681c0c1090030010094440304664001040d24070b4020b00c1d0074221802001c7c42002651101c0691074a96502d00c0072040c45008580e5440d5640c42d4400a06003400b0201030007403107261400260b00380c09074030840c28910701002c02070000004010309410000704014401c00c8075024240054007540d0f6043d01320203481003801802c18804800104149140c05500c101c0c05400c4204180380b6101c10208501d40c1d0b10100c1c0752000e2940c1c41400108001041e001030029828440c80000c901c004071100350500e07140741590f00301c40c2e84e0404600700c20519000d104151015100b403a01017003440198840380c40c10341c0050659401031280100181007d80c15400100182401d80402c00c15061141800310044641c018800e2195080003007080d6007403140003990380 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 31537325 1250 31536075 31536097
    0x120c091a060702011101020c07030b18010207030f05130302060c0105040c08030a1704080903010e0a14010606052208031c0605040b09270303040b010303110a031e020a080d1e02 77
    0x220b400103680040d906511484002c0301659001c10884d00010002d10140000703620446c1e101400741000c0031100034581d0071181c038042d03581c41801000c001c030b0b07030000c0e004514040d04c0c24010303591405100801082d001c1a00042d4015400180c901900001580240d100e940100d9900320400d4458511070380300d1191f0001440054005810310707181468640d5059001441042c030945004144d00c003003800e482d120303180000a500441d041006101c07003455140c006034511002000710f81c1c140f000c0613100d80590001450f44011501a442081c1e035060045406052034400700ca03103a441e030f0f600345000c103008000041080e500b4942c4c00145801c0034000e6046000000f030a000a0384d0740d02007003000c1c05244443c10120790450444d411800e001c1400218012400748010070150f604504001c4e0400c00140144070060b0b1203c02c03010701086d4000ca0820170714510648083c4a55107854040385009180704015110b00070004d044465140d00e50b021b900c640302e00079021448604207022520481c091030203066 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 31538575 1250 31537325 31537327
    0x3150105040209060c060106020c031002121302012105061002150406020309031204050307020f01081509090709050108030726030a020d021c0b030609070602120d0204120c091a06 78
    0x10140d8601a00680703012034010301040d0038120184041da141001c01c0e88250003580012180c10014202403028041c41515010b017545030402e655202101c24800400e000322203094110f16104580c8038000c1c14590001c4d104c05000ca8048596540b0b00a04081c0c503500d00c520070036862281118004180e00b000d03080c08004007103290795181c40e400065030004142c1101c0303010400c15942002d8991000e6405a8040d000958440d84140705014407208800032141c10300203a44104070b070020901a82c0c010502c8103a4450403039440340c502c11803034007405400c40383c1c6140c1017a00201756150000068000640074040000202090705510380da0102d90000d201c68516041002501ca800190028100c0090007200180f8003402526503101c804580181c05034065241d50300020145420002540c01c0343d0f2032405441c800e40307000406940c0b424071008051360310402103042c2d440c00166605641c010070309903082d045010158036203a6040c0545001c2c918086103051412410850344011801c1c0203800a0021 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 31539825 1250 31538575 31538579
    0x2120f060d030909021b030a050703120501050319030207170c100e0904060c0507020603011403060f06130e0a1b0305060702120a12201e0a09050d0507050301090b090606031501 77
    0x782e80070f036001b220901481049581620700800f420001049140d9040c0e0311a5115201032070000c080303014407902e15072514103000040c005940c0100d8020381a03409120808440c01c95842c0c2071703051203407541c03010348185c0b01d46480c4600060701190482100b441181e000500c0d01c00c1c800c4c29114482d0008446800000306c100140000e501c9900101601c40c00c0e003070a0342455026030000700c0c80e82c0309800100e1a0250107042d80058141040320784c0c4c001c0c260068a220600d0510040381c00f901e81c176070f40e0741005a101c02c47c0d0524210240000c080003508070301411108806080b20f02c807900ca06200403601d034880d550016860b94408580b2565403070a0344500d40c90318890322006c41d04461420314045100383e45040c0301c0b080c1d240320810042d04800c09100381e0b031242c82d0603461004844d0108000001600100405188107a0008512040e0b0340120b401c68845006401d1481c60840d6076001303140c00d0342ca420804028408180166403041c18101d08071099035865034181340d120f400100841d0b007803071415001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 31541075 1250 31539825 31539839
    0x60a060602060f0a020409020d06090b0919020f07050d021c02070503070506030403031d160e010302090f0c1b0a020f06120a0c020102090409080c070512100902011202120f060d0309 79
    0x24044d0403480504025081988414480c8120391104079518441552500204001001f5015141c2c240c2002c0f107081655190500e1800d00c9440c20400b1a035000d036000a404007201c0c1007905480400b5040001c90750701d0802040d01035030716281146107000e041d140f54540d0071141d00c00941130701598806000b800000c0e10b840d040c0f00c42904068030403403d140e1621800558000d8001041c00b180c0440c40041014419059908842460541041e40c01d007407464010b00150320b4540c0002e4000d00c0c01d6201032119520707110b040182c2e010312200c464090a4202c420050315000048483c001c1d8001c441c010351403422801000024814502c4103420104258002580d912150f480140d081c2c11600000d841c011581c8006012100002c0d0102c8a0f0a00070440304120042002240d020f400180d4504111b0b603c002080355440703049001c0310707400f16114081c4000310f9108250069154801e000195214100b03108608440001122a80d01800450000030404c2c90001001c00078640c1513220425001d0400c0c01c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 31542325 1250 31541075 31541101
    0x70207090915180210110712050a080f030405010506040203130f0203010b060f210c0f07080904090b0703050603030f09010c080906040608011406190806010c051b03060a06060206 78
    0x103410b607421070020070308101410890007000d800c08045020f251010f80d1510402c0a14007800c43d03024204903c0c22601050700500080c0030f03055400c502c0380402e44008a01d0802d14204c080c030001001e01b640443c14507003004401002c5c601807881440203002031340c2c5100500080740000c0301c1c2805074450b118031460208034080d2050100f54005170001c1510714034180417034200e07032003c0074a2172440000660803071501101046039a0744559817010104600b088191000302c0c0c09010071400203103400040c41002c101450b03044528039500504140310304c43d0642028581c2c136100316145804642001e0025a8074030700030044030b03207a81e002c11405d424090030b81c0046a1030b2400d0081160802c0082200810320f91300d01c0040d0004000680d1580960340c1400d008a4441c042d814001c0c1c050714050200d0840b8801403401d001181d0868984040b03d03035610310049a4018540e200035020340075001009031b8140c00118101d81405c0c040c1c04480d820344451907540b013154a18852a001600000c021404016841e0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 31543575 1250 31542325 31542341
    0x40920040e060114040e010b101206090f0e0f06040201050d090f0f0c05011805090a02090301020d0f020a0e01080105060a140c030a090e090d0e060c070b040b0901090b0307020709 78
    0x1500001d03126580c00425880d1100a070400c280f000035a800e1010301e4549400352441d43d6085038001c3c480500180046a00180580081d9090003004220942c03098400c0d03112000a100600b428032080d40446113650051200001d104420700131883c01400c07442d40000c0d800d01407941a96528138104880ca850701c000e005881d411918442d11002001c085844044084502409800b1411903149004005050105850408000346c070303101d04200440d584402c42d40350302081c0290096590380355100028028403840c40000015032034030f02c5480607001591f02034030070320600d41c5680d000c40048a005403032207842440f85c80c0d4400010416a03d401c2c0c826403448070121100d6907090b0400300303d070010724116000b0540980004001050421440c03402194694105846001810b212000901d008081c0c607010424603000301400210342224420402505000f000740403802619140c4600b1560001d5000303505044c0003840e00b280216030b1400400c03c4a0081320755400819900e0f00d00030501010f003100c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 31544825 1250 31543575 31543579
    0xa0b0f04120606050f01021c230706050405010b2e0c0b04080c0607081e040309050402070b1005060a0206010306050703020409110703020d0201060602070611030403060e0607030b040920 81
    0xe110000d50128401950078126202d0840402e0403030400092000f01810300f00054115400000540c091815403101c05400b040341d85880107501043c0c0344640c003584098a82c9880001d80011340c0c030b041c015039500007401607105100910130524140100720107001030601035480304000b0300b800c41c1d5104c41000c040419015030300789050b100407184c603040001c0204860035182c1c480700141409030348a05024079a030040c118103044400e41086c08803d003c442100425084c20043c02c0089030605004100001c020030b070040081d50346400c3ca2400c0d07126003400345c5840b80c1c03d2410420100d490300c1e08905564541070070340c0c002e0190b686035885441c0038203406031101090590030007000c50078103010300480b500f40c80f6280740590354680514001740b07018818405c2c1801c691410340140501c41c0c0c0812010110b40076807620480c1c0d07003510f06001e811445691b20060905162101360380308014003003400b0b8441d0034541c80411074403842c1c106200954072403800003084025440c58845040491240c400d5002e980 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 31546075 1250 31544825 31544827
    0x6030b030c0915031603030810030f0209070e0927070302010c170d06030602043206090f10030506030f0601030309061b06050a051f0b03040803060d0b10030b090c0a0b0f 74
    0x1000100342007240d6858140342c1845c0b006418014950080c00e0306402440e402c0910300c10604e9901c50511600c10600b00078482c030034200c00300301b4491107040c81d000b6000b802081d2482c0e03170510030a600d0130035180700b8100341c068241000003c40028042040011070307806848000e8507050607680c881c440e8540e01007591180100348912181201d0a106403005144500001a6142c3c1071200140540700781c44440404000c0c004090066461090003030160303160182c40711919004010000f550601d0070310040d43c2c208550505001c0303c41d600da0015405041c1c29030544202803038260080c6d4451009020140104540000400c8124440c210611002a0b070303184001c8034440c56600c803400d4950070340d20107000a840300280240307008107070450313849800031000300050113140044091230303804010300140a6200c0400061465250b58220400055200440c50120b01d08015004c002060710300007900d03000b1b0324100003240d043c00051031441c0c0c41c1d8014809612645003035210f2100d40e00c58204000c0003c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 31547325 1250 31546075 31546111
    0x5040e1c090b0703050307030f0b030d080702070e0408070c1203050306100c02090f07020607020304050f090a02041701020a02060a020304050a230706030f0e0309090106110109020612070906030b030c09 88
    0x1507840203080f9091003941c072641d59050240d401001e48803403d1080a05901e41030804e206c0d40d4000640341c0c04444241049100c03035550020590800b0403550200c08915850010030080081a00007405502c0c400d107c50100b107600c03040454810000b000000300440c40400101e1281e1130f0a00102501203942d03c1c1543d00810aa4040b4203084003c0d030390b1002035000c01c001d02041c2c4d074040c00541c2e403046640c802541041d1520002412144000340c0c45e43c000ca0001020880c5520350740c04460140400d0702140c801c0d05c40000b46107001f540301c800c800c00140980e80124a5040c190f00880b8051038008004061000e12521294032507410004040035180a01058181e0584140104001001e580d00c0008900c07150f800f542c03080d6441c4614400683e042000801c1d03103a6606030400e415a00d8501c0e1950005600368803503401050f84c040003940c8401d02064840e49851841c113074a11486003030780d400c0049903403100b080d07095a05058520354550003590b2009054145481d1455218403044180c51480e0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 31548575 1250 31547325 31547339
    0xa080706020703030b100c06020d1d06040506010603060339080c030c100801060507060b030a06021c05010501021911090c030405060f0606040911090406060905040605040e1c09 77
    0x26009280455450780c02080c0442895050700c1608200f140584502820007801c4d4001480c0600e0710600420065003c41d0079800c0d01825801844031189544024110408031a41c0070381d5202c0488040710a84241070012030070030721074010783c0200c940c030806044401c031164694011440380580780e07001d0809a00011086540b521302d819000340b01000c00f41c001025040c0500d03040c1104612090301400340701601101056124070050704441180c9001d503160039a40c60f1000c0a4229041c006600d4812511014107010180d0300400c042e00510b602c4001c0c0c150b5402010b0300b6030394244103090258000030030400c5007121212000b66128400c50806075400d08580003e8520142600e42449030400807040108014003082815005822210702c41e5842c43e044000a040f4400c40c001c4104c016220320501c4a2800c00c8000d6806142c0003c2c002c0c480300d80c0318040108a0162413055521450400c180098a82854428400c1c089520809400318900702d50b0030807452210741109100b0400c070710100261030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 31549825 1250 31548575 31548577
    0xf070b030603160e01090e010902060d0c0207150503010509071818060e040605041101051912020f030901200906030f04020a0506070b042907110319020304030203120a0903060b030a08 80
    0x1810140211058550514483c10126800c14030036007ca689081d030090056076840c010b540c2e0200207100c0216130310021800032070508003203510040401e901b1110911511340c00001450503504280c82c030140d0f41d55000300854150071640354001040001c41c00030b0101c40805425541310940d601c40108200755914600c0301014021607058418543d200240030401000380d0340155140401d103007890030b2200c0150000b03200c25400040c02d06206051075403501181961b01a1001040e4000e04151a40780c06014580079002c41403d4140d00d2100c2041c05900e02004c106440c2c4220300a0405030031641e84200200d120507000d08240e0b4498680640000c0c01c2d603480f0003d28445105541d400c0023801c0901c0d2407290320702c1189440c00c186c00754030700070088546a030490b59031280141c80d11040019401c160141544103400d107850b2000c1206440d40c001e150000300910440384281c04032140c0d4007198280011a00450103560300151040008001140b05ca4008289040c4002d09494900082e80d46415031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 31551075 1250 31549825 31549829
    0x6011404090218040603080f0c0115060807020d0201020316080406060905160806030303040206070201030b0f0405010605120f0702070501140f030f04060b010c020603060402070f080a03140106020f070b03060316 92
    0x41c1030b400080c01c0b00864200b000d566880441500d040c400d5504564803200349014105101300105000700f40011481406d403c41e01c400380130403810b108101d4681100501ca0f190803101c3c400580701c2c5000ca8400d8910500c201e0b44601c052401c40102e001250804032800c48010340151201e42d20b030080400c008110b440380500450034900c0441d03044844000c0900310302c0d0002c0c0328520907081841001302603252041220700f030a83c2441c0000e5038518a8001a040b4504140b26980180ca007000109a181e0481e00502c030355410310112107502c3d5600c40b4241224201100c1e8031005802000b4108501c0d40140c0da00d8122a99946005003445072a40c2181c241e9041110743c440030400d43c41c24030061001e40d02c94207031020028a0031400d002e500d40c01042c868031018100a001d19400212442400b04101142c905641e1010015a8402d600400200501500680703010005584000000d20500000c1c0354000300c10300b5805400302c50300d8074601003600d8000900c6980c16001d232030b2841c0c2ca543c0c3c40100f0140 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 31552325 1250 31551075 31551089
    0x1d04090503121503100908040902071b061d060408070b0901090902121501020d0c0b0c0c0613061508070303050f040b07031205070309020117040201030605060c0102091c0807060506011404 82
    0x1c1040303c04251404086014941c09107260801980214212208840c1a10007808025a031528586407100b410314a0903000a16005100340210f50581d00c0351410041400c03805412074219451800c10000c4e02c03c501c03c02041e41e005050804c40c101e4150042c184d12181410a202c51580c1c1d61942c40c1a07034010f82d0100580840507081100d044901c11000465850a04c02400001c83d52200034042600312080604150700207170005100c40c003da021644c2d440e082500317548c1c950070200b521501c540c4010404549180c01d200c0340c10303070140840f490701040b03d0012000704000e40c9161010b4810350b10a0940c0c401c0200108408511490001d000b0b0503840c0c42692890b43c406a0400203004448001e08004101030070035801d000036030307441070b40740c6000e100b00c2601451980791807006038001c0c03440c6c1d80401d810a07804540300c2d0501c8030640c0030f0301041105540d11042c441c0700044107011a808480000e00c1c1c4072040c030540b400b0418952010750b200d0700606003400d0030283c0703d0540495403c02e40c0314038 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 31553575 1250 31552325 31552351
    0x120402150429040819210207050406091503060e070306090308240604031502091c0c060804020d030807230703030608061302090907050d0818011d0409050312 69
    0x428207402c092070000e1000300b01c03aa90415040c07160141c0c440f407071300c0d040c0140c0c811003002c0305003441041d400b8800d400d00c80c480351080c2c003500801d01a480340002d21849115a2400c0000101094980607240700081e0110b2400106425583e8440007008110310f9087da074400c1e24008030006400c0d00c602c49405010f030f200c0c9001d500d4007060161a0001030840c03e18142103400c3c1d00101502c54400b52019a58000c1800000c0c1c405402200024040c4190255000d4541403a8103c10401c1c0149200d101340100c1032030309002d4461000355004081a100250044c02114030400424401d0008a800c040707981703404904c00104030a40c0201041e0b6040ca80b00799500090044101601489031074000d1140344094810303850000003400384601c1c8000064096080e100c000b48269000f8400b50f00905030080901407031000701d040400054209140411003a10b040071907202541c064204060b102442c4019128034031114014000506580349040340e15100c01e020b4400d402504118141c854184d10441c4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 31554825 1250 31553575 31553609
    0xa0605060306070315050f1302040902030601020f06010e01060503090a0507080c04140c1902151509010801090b16020f0f010903022812110d0201090308010f05061204021504 76
    0x500b816409000401450b150411007000e8507000b500200484408591210000135000089134400c01c8141c0c405004a20014020480c00081d074043c1d07010380300c2030342143e11040300c5504840d941c1200303006c0c13052107814900c0104400752003000159480221041554524483c0341e80d44c0785040000e41280340b0301c1e08010182ca42d1800e05210b01410382d80141c1e00c0401c85d08104001862511403414014044413608051814140c001c2200ca41c502c03024900031040d91803d07240d90008401c22152180c4034000200c000100c2100500a240483e42c0001c030300070141d26007188151000080c48080e03015030040340b81a00c3c02600510410240c05408030002c03d00c0b41a601e0003e090090140ea200f1481c2c50110300d050310070441c40c0085000f2a84905d07184c100241070f0074180c800c00c0040c403960030940b0401d04001110745e0306401c0100028880c1d140c107422039889689405d41e0500500031941c210a00748140340088046401c0ca40d0494000380c001e5422405046581c503081d40980c110740c100590790006 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 31556075 1250 31554825 31554829
    0xf03151a03010e0709180b0604050601050405030607080702010f0e10090c0b0a11010509010c02100b0301181b05151c02040308040b04030507090c080708040c0503060108010f05011d0601180302030a060506 89
    0xe07042c40307140040071101b402441543c4000c100c00300a8080da016542c3d0704001140b590003081281c004c1c00c1c0080c02c85105c0c1c40c14400041c0451b10454514005500b8001141244a550b00680c20840c05d02c5025102030310b88030305d001c1c0042c5400c3c54140c07001d030040000040c2e4111030100425000015613148108444081c52a6080d41d401030304c034107566898003402103111503010400b15001c4c80310f128080381d80c41e28040000d014100d0201c88400100300c00740b000c02002100700313044c000040031220a10a050f600c0301040706004c0001203507641100c0c20400c030860f0111441039480340405540c4014202070f03c036110100c40d81c101d40c0045007642000941070050040400c402401003030307904024407006c00500402803ca000140070041448010b1000c14100f0500c1c050700c4002d0403015046034810360352205c01c2400307040c00000003207850b41b50400104c0c10082c9030302e940d2110504d0301111070a60700e4190044440c00310800ca500148499040d012005039001c0c400c0700e000034011a8041070508190342 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 31557325 1250 31556075 31556081
    0xc071205030f030c0702030304090b040506101b050102190908060114060f07050c040c030219110304290a12060501050313030509040e0609070305070f03151a03010e0709 74
    0x18006061581900000180c03001007214195240300c0031554880c0c030360b400c0520b098050020029030500005c500407680349203d82c0890800d4000b1502403105460b02000d001ea036680790505d10000403c02c010710343c030300744400503884109486600018034101400340c10240403c0c0c104074080003d40000420010040104003040c0505107801020f4904da0701e000010f42544111400310700c00e4040801c1100900009000380b001007200a0030038050b004405200800942c00401030f02000c0312210890020248649090b03101116814010340c900b50030600780060080002c0307880d4500c00c9050010401c4050050301400c9403041c0340d1603046103c8512080c039425906c1d107800c80da0401c5400c0c000c200b110301981c000d90510079050b040081e40c1d000304101050180000b400c20b04030328820300c4c003441040c6000040300c07412640a001990034154035a1000102400680310281c407145400ca5a0082c100d003584c420f81c01016907241d201d0101e903140e0b01007801d403034881243c24180c5d08042001c000d005a180 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 31558575 1250 31557325 31557329
    0xc0a0507080304061413050f0a03050a11040501150503060d0f0c030602040603060b0702011704050304050a0308070605010b0306130c0c0b0109020d0608010e030703030b060d051003050c030601030c120302010f0507050c07 96
    0x7229180c101182042030390031421b618454607100c0c540c00171900c44a0303220040d500d00950340100c181c13440d40456042c204000319800007054055881d00f0000250300038110030000906405584451450303c85a003004005002e01200313480c100c101c0c480080009105c0d03280000258403c0d640580c58600d8901c016048a0050b803047c003103a6020032841005030f83c8809401940c1820001420362070300d40c0c0c1080c52540c0225049607812100500010081c0a0080041e0600746d120b82d105104980e25070032202000d02043d215682c0041d034160100e40408016003107440000b10701d02d80401e02914940340d00003407441c00c0e40702c2021650f00040828110400c0d0044001620400c17009100307610000d0360140e540e11030b012029040568812a1961551f900c0307080f00d6a00e1380c003010900c02c0703040440030381c0b01481c1e103403004580310f1051402e03100300c0b401c0114071541206c0d00a40c6500b402460700b82065041036440000300c0441d50b071880400c43c1402c1c28880c02d030003500380340d6a1a482d0141042c60034941415030f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 31559825 1250 31558575 31558607
    0x8010504020d03031a0a0603020903010501081912120f020a020d020609060a0f021b06060a06090e060913060501090c0f020a050309060f070c06020604020a050906090402060c0a050708030406 83
    0x420025844507a049045141d0600e4000f480101408a10100c074170034001055018000240000d519035254014020f000000c0300204416640d80b00c1295480b03524400003411a00c0c20f049403c00309524840b0f420070320455091080c0610030448801040b03911040c01c0c429010350201d071201c00e46a040107100100002c2e40000d0803141890200d069450100a119400c0181c0340c0c84110101d420b00e8042d1814a0320128207013502910281d03000c0d03103a030b4040f5461030103200f81442c0007520074441c0a42c10300700c1e6041c005100054407200240030403800001c06040b400030032680300c0300005145103d4075000346580701c000036040700c034600c00400c40002210400d0840d8407002c4410301041c0301008491880500f251519a200404209a213182c01445409824600d000c6030020300035802040d4984501e10854030080190340311000c1040e52402581c6240e00030001600040040c1000001406060005422a400403069986252138444190041b190b02c0e040458104042c5410007400c42c0b01c0420 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 31561075 1250 31559825 31559831
    0x1090b030d0c1401090212010f05070801030818010311030a06030203070501020d0801140102070509040507050f10020d030504140111040315020403031b21050903070609050f04020d141905010801 85
    0x8220001410b072100c0c40c101400c1c681d000700f000c016548003584482c3e4807940c06403403462a1480005103a008010181c000140c49003082c00094115210b010264143d80e0b005000764108601100f00d88500003055501c541450b81d5064000d404402a0303020310b202d184210004118141148103050400505601581c159800f210a00d140103400100d242c1c15503034181f09010614003000b00403460306143e03611258001c801c003400c3c441400000310f400300c00d0f40c07815616440070904000c18080000f208803201801601300c4000b90f81075520036005150044c2c01424580c02400e04d0458045c210b80c148e007640d800d024000a0100b080001900f03081540ca02503000c02c5007031600e180c40103802e04440301d201602c0c00d0005040e620070800220210320640240d0400b031441c071010440040d00507404804554420b03c90010001007182c4511911002d6840207401101144031030700611000e0f4019405002426403a12441503080d207014604510035941580703002d03810b010340031b1240300b10307a0181c1001d020741e41 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 31562325 1250 31561075 31561093
    0x103111005090f04050405010207060926090105040312020a050304080a02010e0604081c0c0602030a0e0c030607020c040906110a020c01090f12030c0203010906090b10090e0d0302130b030f01090b03 86
    0x501da00107042100f105a074007013040c0d59070780b80c0303035009200d00c0b00300901c13403403401c20413500303008a02200b4050560000d00d0036501600b094284080c07030107684501400158100410b00004840009804214079140100d9200c440699205800e40c1c001d0b4020890a44c00001e110301550781c4500004507074042a51117038a014145802c0c5500c524130010143d0045c0e040c0c1c850f00a80c0d0703105181070800c0a4005204540b82d05000c00f08001410300541922100c0c4118041802e441c600469084e001e1180c94000380040703143c41003400082e0402c0c00060b140380d40d5800d024003140705d41e40001c00c8030302c0050303010340041035903d4009842c040540d0825150400b1000c002e101140c2d08011503a20a901801d00041c450f0452000a014001914004018904040d10401000541580b260203042c00c42c0c101c11456072030b464220304458400089200d01e900200e100c035031181c001c3d8002c141903000c070705600400541f606402c900e5540251092981b03c10154010010800c20344101103011030100e001d002960 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 31563575 1250 31562325 31562329
    0xc17040c090c120e0604060e01050709050120030408100608030c0706030213080f01050108060702010b15031f0b0d0b01050f0d0e03190201020304050d08040c090908090405010311100509 81
    0x80e880e004102040d5540c03103004890364010301c244240159101070901c008501c400d44252118402e403800c5980358101205264482810301170f1a105541d1a0303500352481c1e00d000c1c011075154080740c0c4030121401020452190030b010500081c400b8000c00ca00074480035620704a0f0400b114010351040071150000c1c03140031080400441c801040305d80510340581c941445020806600e562540700c00054401c03085503504d04031040d0031460407a034404090701c00c1c0703030b0343c545c0140c0c01c4c1c0301842031256101222902402480803114007a5030000742103000800c1c000381e452201c0e0b0300344200703800c034124181b0003055817159003400d8001d10f80040e90a180c42c40c00d009200005100a009002c1c0390f0703428540302c0261100c015410800d0700d0528103003040d554668030196102034000c1d442074909841c14014910254881c0740a00f1119002e40e03480f403c5507603294a0003d01c2001030001c00c0d01103441007810001c81245a98134003a09019501070640034080c40810010013502090b40e0400a0603c42c05001c80351882d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 31564825 1250 31563575 31563593
    0x3010e06030a02090c0d060f08011a040204050d0b1e07081506040315020d0e010203190506030102040b120403050403020d0c0e150a0506070201020102040902040902030412050c0307120219060c1704 86
    0x9581051869110782c00c511b5450040d09654011104c034919000d0005030006054012403551290044214040303106c480034081680300c1c90240302d030030001000e65040080c001072010341c0c2c0070016103510000d1000a00c601885800e0655032a400a6014402c0c4108000d041081e18160030f02180c209141a1440d1b4034806000c407012003520070b07258041845060750010341c00c48681035503840000c40d9079107099001c00d5200e401102a00d034040d81f0b0300c4001042400d05100303c6042c0c03003011611605144151980c1c44945a00034804ca0401c01d080c000000107032543e00b002c030340321480b8a002080481c1846024220a0001420485032091240d019900c90300c1340925181510410f581180e5510b88500050780a88034942c804a0701501c0060001a0f003540e82e4051070050340b10350110b1f13907841700d01c6404490a0290000d01d80c02c0d6001007160f030300000c40c11a1100c1c4420810f00540d030010b02c50030902c6010300c41006003985e40c66215446070384845d5000400f40c1448100307030151210350420351601000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 31566075 1250 31564825 31564831
    0x318020108090c030604060501080c060f090918060a051806040b041e150b150309060c0304060608030c010e0705010201060b04090507050c03040f05010807050406050306130612050303010e06030a0209 87
    0x5201000001c1a201c10b01030100e00308480c4060100d070300d41e04051401070018842441403249500440303088082c2442e040c021158420700100b0003500b00494001080100d54025100c807803880718142d0300648034141801818400d291038140003a0f2850035940c85104411000b06c265904c2c1c0000041000050301e444110b40c10a400c070b0740c00141d0221015004200441551020b803441c400b0542024010702d036600034030202442a20000310001600c09140307050700058807078600d81e82015002034445071110001d103038494050440400d07040c0d0f440d1584d42c2180d0050306001e20503519240c01c1c03054000c041100d50b00a01007840200015031500c41c0c0d00d00d1902850040b0342186031100e01040b81d40d4800c0742a24005035081054030ba5590307030f4504201020026126490100314400001084c031350040d41030740d003142d03070340c0e19a05d1442d59008104107446102020700c03c443d9683d054007003480f1280c80105080c140c0f160340103596039410400d41d20b4028100805003482503000d94803107401a155401d0391070f0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 31567325 1250 31566075 31566077
    0x11e0b0108070e1c080904020d0506031c021f021303200303180405130c06050703020f07060c02190e0a06050f06030702030a0503040c03080f0403030e01090609050112020d0f0b01080703180201 84
    0x80c03e40460b282c005d2044c0b0035030502691050010825422986a03030f404140a0041101183d807200c9904240541351040c808141d4096009402d542c1c11440c402901c00d9801040002c0c010b2519001b0201e03030100c00303043e8000740c80c01c1c42d8600381c01075074084c03c004c40403203510110019410109004440320395946541c00c01d60050341c0799800b003a074900003809041581c1e50b02441503001d450700d48500400300c0c1c001c0c15080d8014403618401c4114030340c001c1b440341c081e2061030762800d08020403074091001380e500d445e0465849042c03004001602c40704188001d07000f0440050040ac034145400100700ca500b013218941071045004209000c007082e00001211980c14050414944a9982e4102805041c04991025161650004010500c42d00342c00080091300c0c4a600c6010400c05c54100442e02504980582c4020910110050210390b014440c040341e000c4041c000586041c1c00e81d00c13400305480680c49044089030b201e1001007041e607000a451035004030985800c11003442e45150301e16000c040d40704d01034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 31568575 1250 31567325 31567369
    0x160e090c0d0902060f03220201020703030f0203070b010605030714030903091903080a0206060907030b090a0f180c050f03160e06060405030303040c0303080108160314011e0b0108070e 80
    0x51000c003000e400c20040b05030010807141c0ca03030780303509140c0b13200341c0c0110340d211006003d085d00300c481d090741503c0920180e501a4002e051103820350754191a0404090040707003d51109121410001c0d601d0400070340a0180c82d50380545905100b42c01804020b81c1c03250440d0500c00a00030801460400025903100c02c208460080d850a90001c07008904d04541c0c2020340480700001d84030701e04580000301e0501901e0161185a0340780d840c404100d04903509885441c2d403205060340400c48204481e006222500107030000014402c100ca0007a880740da480c1c500884040001b80c0f010420361070560780d46101c50030250080c0514500300d444580c410040c0b03010b2980e66400b4072010800701e4841000f43d4020b0311024045030341d20700b02410035500400e1640702c220000742020f000420a58404584040d24000f41c02d264038500b81103949540300c00c080c1d10900300c4250360302e0701c40c000c00d282d05107080031000c101090000b460382e07400340005111010042903001840390b00c2e0032824041c0c4449004031280c0107520141 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 31569825 1250 31568575 31568587
    0x30c051e0c040b120607020105070e04050115030c020709062705010f061d0604060509090703020901050702120c06030708070809070506220f09020406090509040203030915090303070b160e090c 84
    0x1500f411075032402c4c040380d40725000c02c124140f030b01503010500464407611184207c1a2020400c41911000d0003904401c40c0003e5143d001c80d4041d07001000300078641d0060318034181e1660130394400c03a41107a0040701d0b0b5032181444410f42c58200c000181d240011100d042c4620b44c1803040c1110300c1a038a204400070445e1410100d0256086000010100c040c024003040d42d0341e41d14100140b607504000300003442804a1004500c1e40d41c000e100311401c440041e11580d00304200c1303400304130f0604040703841600305004194002d003140d603906004620034041ca84820681e81080b4030020848a0018420341c180ea104160901c11541c9040c243d0343c1e88001a0070301c85002e40544806407119426500c8050348101c40301c1d01044546040d00540152003607a50790380e000581c0c440420402680c261000b07509604104211711941c1003010114601045288200b4902000400030038519400840f05540303400642040c007079074140107214042c0c234250604e00b01c1c5a00285400059286c200640342d81c1c120000000c2e9 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 31571075 1250 31569825 31569829
    0x901021e010908040902040501021006050a050111030408060106030c0f1812031803050d1d060301090b0619030603120c0506010e060d0204090b04020103050c030408030c070f0f030c051e0c040b 84
    0x19610b142e0740010340c26101e96880c0c000a01a412030300803d070140c0100c01951241403d070303125001c1152401071a158082d45044010342e85010344603505005400100700c082030880302000307494002c20b00782d80e0000305040312600080c1505442030300002008610034840210403400000c06003900d41c124070940160311941750607075000600001c041c5003042000000014040c0110300c41048900988603901070811041c019040c24800350038141d4400402d0005101405050380610a14800580218504500d40d1804d4009400e04071000700040c0d00d5800034820016540c0c3c1e680391904441c00e0484604500c1d039113031a1030f1801405a444948203004c0021495907032004010440b580140041190000606240c512003000703d405a000c203007450b000c80e003440104d02c210380c800e07600050b10504540300c012140b0351641c8282e6007641c41e4008200148085505840100c0d41a8429100e680c507a2501d07280c5207060680c0c080e80c03400c80d00d49040c02c480300c4400210b002d2180c204101c83c000341c806a1900 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 31572325 1250 31571075 31571081
    0x90c03090b090a0506070201140a02070501180c050406060507050a031d06040609080606030c010f080c041701020a03050a0b061e0f0703050c070503011107030c1713030303050c0901021e01 82
    0x98081c246484200034010340580215007148068010b0040e2100340d981c980c420b900381c03915441e101caa502a80d00000700d1884032a80034003c11071080001051410003e0071035840868481010380e80c01074008020041480c6c1440307078100038205420010300700000e0f500d40c1511200c00c81d00142c10b200f50034400d41380200c96098200301c4040002c04050b22143c40d0305009005801500500c0090720507540460014900001e1420380d880e13059550108840c1030a800b1030300d090011f00202d04503902400085801c20141a243c0d220382c2d2140001600c0701d074001c80c01000c0c0d400c0500b21017822483e00b0843d0300c40b030314ac0d1402c0b601418440e41743c2107094840d041c2e481c000c3d4440e0383d800071a840c8003c9484001c0650002c0100142c4a000c801c5a69990300c6e402010308a603040729003402e115904000f0f41d0700190240d40c00c4600c260103900c00d507404520b50b812180c06940200850043d625500006004054041c0302d0b064010010b007501500740a4201c0000c0e60b2482101003201c00988502000c5020700d100750 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 31573575 1250 31572325 31572341
    0x9120206031306050112050601121211010e01022701080103150b0d050109030206010305120a0503070e040b0301140a060e090714030f0102072001030218090604090203010519180507090c03 82
    0x80f4100070741d42e51241c0c0d6600c0c4e0b5400c0607044070341d800707000000201403c0c40490f4904880e0804e130800040482101d0545080300448540c209554a440150400c20b600307102912000d405010410701d01e15041c0c0310340118103107446035141800340341c00050010507040403020040945c0200d002840c20100c200103142c252079020010700540c2845160010168007081d454122880b0b2000c40c0c0d009211805521740320b01070300e00b81d100000d6060002500c0c05102e04404104d410000c1c0c40010b0b00d054400100342510016004119561180014000080581d10a98008140c1c00c10007203403500b81006180e88030b400e248903621203c068000880000d5400b445120464502d104c021540c9514504e8103008802a01d0a41820030403d030b222080c10b54001d000f01d40000c0381e61104441081004030030401120009001140c101e43e503940301c08010b807400d200c1d0328007a5003481c20f012180c00486022500303981003554000200903d03841d2010001c4c2000410409807040414003042c05945440e0450041c6008 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 31574825 1250 31573575 31573583
    0x15080a020c01060e0411030d0c0b040201030203070926100c05040506070203030405190311010c03120e0f010e150c04030b0c030a0b1003020d2403030804020d12020319091202060313 79
    0x1005d0008110b008244000280300c250240c0d0240343c4000800d56005900c1c4001410103400c070030000d00198481d60042d98420100e0401d1160a51203003908103080c5809900d008540c0c000184201600e0300403c900d013000003c0303c1e0144491401c1f044003c01c24011445400c0c0550707004240302046541c2403081d94081e1501410401c08012030784800c40c4800b40c6448217480700b2104502e00100c552042c400a6850341d09611342e0031440d60b0101c130b981c00418110702c00c10f40d81c0c060803521520094083c0a07402920003100000c18041c039041d8080042b4450103440e0b840c0050040000700001016036010701e500040300380d07101e5243c0ea208500d000c0a04411010b440e84031102c2d0342901c24454142c6d0151410380103010040240700180031140143c003144020090b690b96206004000091150b035500e41c0c01b42c03010f001109260259950781030600150352035003015810200d00c03450505000c9016140c590f0092409110070f501d000b0f0310150862598002078010000007002882c020b4a11000309403c0c3d0340 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 31576075 1250 31574825 31574849
    0x20d020a0906030b010201051b070309030602130302030c030c010c03050f0d020706020d140405100b06090a06020d0f0804080d050a140406021b01050610080907091505040615080a020c0106 82
    0x4010488441c500500c4003092411300304c14a903520511a50307110f580040d04030112581a24002c1e003058000c24022003c10003466004000110140060016892054034220800d41588100b504080c40e111280d4001d6000881d00111a80d11000724400d05405062295403907502050030310280c400d120401500134000076034607040081c02c1d030042c820711940803020011000501d00d103140c42d01c000d8074041d1040c0d005076182002c1095950140481080c000d0006103045410404200700c107001e03602000c00744c0c002034401000e003030304047c88505c000424581094549041d40c0c402c030032401191107128607180d96000150040082d507000031901c4141503c0980989040d18081000e0341c0a00c04422025103c3c101000c419141402210f01940b001400031070f22040c62076080303030200d0b4010a460b2541c03185210009549030076100c0d80b4119510404a60403240c20b0000b4801560b5580e403014809015407402d0030344095200030036a4000c0309400700540d689407804c883c6409014150000d81c0d20b80c00f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 31577325 1250 31576075 31576087
    0x20703050f100b03010b030c060c070e01080f010507021204090c0504090f050117210904060f030b04110a12020f0406090e0309030706050301030f03081f0308030406050604050106090315020d02 84
    0x240001e0207820044003160280500f2484100345030907280c10644894159001c00c0c2410070034030742030000e000c82507290030450304c10980e01e41480404040030ba1044046070480c11a02e494000f0038003030b06501442900080c500c02e07148900c12102c1d4460ba00c645001155142003401d5054420400c0f1401048901e0301031002e20141e45410006201c00e21450a44600c050000c010b070140120b00d80e100c000004142020a50002c5150142da500a00c1e94540c810703030729107020501c208bc0b0040b04001c0c5000755890610741c0f80514180c42101940022141301e00e01d004001c00815401140004840b581500c03640c09600a100100e0090103160b04001011802c2c096503282c1e001001026103d50b2800300d048928030b0356109820741e010300c8207000180c222940050000c02007801001c5840d0000410740580454100040103092040d241d50400c1b00d43c1d4400001780000e01c015809510b401640846c2c00f007141d075142c242e02078040100c40c4401014901140c100340288005035059440700040b106040d90340758 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 31578575 1250 31577325 31577353
    0x30901020a090503190b06040b03160f050103090c0504090201020c03010c0c030e04050c16170d0501050f191208070203160618050105071401021c02030612011b0804020102070305 78
    0x14116158070000601c510344001002c1c940000d4445008009002a50003440c494589100903900140210340054590b0300c90003954504111000056880c0f00c00c1c98403041c00e14103280c542041a602070340c10075041c0002500072030014162101200e03c100c4000500f03640c41c0c030060341005c50350707920a9803551a103002114600e030404d240b1260588640d0f03070f42e103c3c17510789810070003100d82c01d640456118109018188040314140408285180115203d103800d92040c286070495030300080d0a040d80359240c0d07004100380d0500b87e0546411400840e64414000e0503074070011002c0e000d030f105100b0003101152000007405554401c80ba40f2580140940b4900d040c10f0901c82c4002103d881404001030b00300c000700c102c8402c2e044030001690390507592603140c00004c4d1507214035200c0d03140c81c00d60195802c001c142d1101c800d80c4100d21245001c43d202503100e140032030400001804598080c40541d060403d50306191104028681c2c00b960310f4100301641c0e48440c00102d10304a00c64000501038410b54103018124 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 31579825 1250 31578575 31578577
    0x21314011b0219030803060319080301090915050405071a0c0c040f020408031206031203040b0f07140c060403031503020109030204020711120f0c0109030210031e0f020c0d0305010b0322060203090102 87
    0x140701c00f23400f10307480e15580c2a24200044a0090090501c403402d2005003c40c074125007184181d079004d440303074401200450410004880c1c00f600c04503480da02100d41000307245a05d012014241c0c42c10982542000100d088843d200d8072001c02461041c1c0e0386042c442c180850560581c8c0252994a0890303855140511440100d4042a5030451082c49840004000d0b005040d040380d125a9225001c8012615042e42d0303444170076000780c1400107008400c540080b500c0780600260203101d05680041403a03050130305000c0c040702d8950b0319030020503600d80804c0c03015036008208a41101d505940043c0d4a84840c188500c420303100c03401156100401001c41494a40d0009040400704000020b03a0b290711400ca00548602800b440020f41101d0902d40c01d440d00c40c000d40c0309012424400c0c400916914400803018122205100c071b0304103883c3e001c04e04105554041112005031450b90130108015410b00701c00080038000101043c0c41c6c1f44112035107104c00349418000301442540060150340328140080d01e940030b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 31581075 1250 31579825 31579831
    0x1305191a03190818010e090a23070905130b04090302030418021e09040e010c0c15150b0a0201020c0703030509030105070c030e0f030109050307030201021314011b0219030803 76
    0x441d00c0740034580035441c01c0b45281e60a07403550040840e07142c00c0340030212903510100b40403202e060003001c4c84d0310201900c4a0402030701c203101800001800486140768031144001c035540d0380c1c42200d0900200110150046007050507294203e81d541c1440c42c401d40b10388083d01401400ae41c1050400729181d040580000103001076401206194060201e00c0800c00224061a50b1080700d1921441002d174500300b8142c014051303d4000b520104542002809041c00c4d60415034503400042d864081440600803200c500b250481200030301403045401689403850b005005011b20031800500040090300c1034000d60441d000d0041400a0724400c44c0c1d00e003400707007254001c42c502d80d00075400e110000380c15903c0303840301e6102d40703034182c4031444505040320034001d601e4640c410b156055941e441120b40410003c002a0041d28841c2d400503a85120a000010141960b07620046141781d521a88198903078100c1854205807030a014005803c3c03005000007100d011103900d04900146040c0c102100f03100810009500c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 31582325 1250 31581075 31581079
    0x3021f0206011a09040c0507050604150c021603030503090307050607120b0301020702150c0304090f0b01030b01020f0a0318050603160315060801050f060f030703090b0606091305191a 80
    0x141d40e0f9803003968400842104208118186042010840360701d496448402440460319103182001701e20303610b4030716044041c0c40a851204035107044440151260080c0d078540d40380c82c4081c21510b5482150030408076440d000007002e0140100004407001003c0080d590101e4101c001c0710000e0901c210080c0150031034002a00a05042a809141508050080b211031542c054001c8201983c80844c0d103480da00000c071300720100d00007000009074075600d034062030641060000000400d0180301d00054100c8401d03041590554000801c80006001e010035425981c503010708094009071501003d0404501180d00840d03030024011041c400c0211b001070442c1c104280c0c1e0f860401842c2d241110007044507030035100d14000200c6540041c00320f802c1401c0c0d9045402c00c040c0c01c1604200600380c0d5000e03180c008076031000001e41d40d0540001489920f8894680088040e1402880c0c0039090012501e80c040d08088058005d40310300205044010201000c446d642e070b80c0404121641c0e0b0094035011914010810714 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 31583575 1250 31582325 31582333
    0x403030c12060b0306010f0e0607051e010e1506062b0606050316030f020705150a0501060309030503160c0213020a0905190303110102070204060f030308090c091b0403021f02 76
    0x7011a080c1d80c071614003660302c403680e01400d5079a88001110406444800d13142040100040c6044580302c2401805039070344200c0c05440450588800821051010510385000d0307818800d0004a40c10003142507086242c0000b80e50300c8a980354000300700c00788690ba03c00598800d030b40b54800405c1740410480d2020000f400001d0082955520080710240000e9810141000d43c001960100034040c1d4000000c3c440300b00009414075079103441d0715041191003203096081041c202c0820218201600c13400f0702620482c142002a01c0c0030351801442070000a1503400200f110022001c02c0c0c50080145440640d4010100410b012505a0f810007940152003800040b4200f40d401041614110301401540700388030800c010040d01c4c5850455416500546644095500300245005a11103020b604042d01c0820603540942e403441c58001d03d4084c00034004a5250843c0c0040d03002680c600035a039410500940003461545220744c101801849982c1c8025401180039951203848205111030b040500340340c3d020703a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 31584825 1250 31583575 31583597
    0x6080c0307060e06160503040b07120203030c09040203090c090c09040c03060305060c070804090908070b070201090f0213110c0c0a0503060f0a050711030a030605030c010309020a0e04030c02090403030c 88
    0x205507190603501882c008200d1601031000c69007040d0003d00441820000149055161a2107030ba00f140d002c1d411400c07610310300140040074272070031944003807580c0007510080d4690302d002c02a030602800799071042c900ca80d80020100c0e4090100b0000c481c0a2940180b250041d410b00750f110804541c000c550140c00780e4180f0010700d40842c043d100e2107080302e800c1006031000b681c03500c1480003103a0128504680410307061001150b620f216216201c0c515101e100c50070340d42e03909410040082c181c011700c84400c6a041841d40070000d00c01c0c10305d141246034141d0700b8400d0740c05103110040c040d141b00324681c00d00110200d030070550703042e000608800103c016128021056122401e058441e08200d032012032130020702c0c001c40d0780c030400c41d8006940f0001900c0c01c21403042c211000242582d104d4410040000e8561000703100b913250501c55004002d009084c20030000b950340e80450000a618450030070502c540d080000c0034180130710009160103078014165a01441c0c03900e00500180b21451205000590f10401 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 31586075 1250 31584825 31584829
    0xa210c03050f0c09010219030903050d110714060703030e01020d1e0c0207060c08070201030b06040608040c0503010203150f040902040204030c0905160903020405060a170706030e071a0304031403070306080c 90
    0x31541380180c180d0141c00080e0004100a031046031150301281041120180000071a900b07200100c20307402a9a0382c0200d117080c402105140402c21b800401400c030502e02103440d955249412180c07003d0741800c000c07504c04503c0c84401d0080c018954a00103090400303001c03114407481c41101e5807983c14100410007842030b2a00c0103d80d11451ba004020104200361200c101065150024204c0c281c4149404240440b00402082842d0065844240801e40000c1070000701301a000700343c0087e05090303000f141035141c403210111841412010281c0155100d041c03850700c0381c640343c0011316400e40283c4199034541d96403170101d44031a46031150b01d036041d20306000f148500c00b000c41c1c0d00c8080805560343d211510b0854007000010200a8101a4048034904002a50b080d240c400f100908407404d020b40030383c42c6001c90150544251000e5074031150400c91041c40300078001440c4028412405403000e89030799480c0b8068070340d600b41d6011802010808030401181507410b0300444190794400c025070b20103801d0402 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 31587325 1250 31586075 31586077
    0xc14030307051c0c0905010804060608010c0f0305070f08130c0527010603090c050f0d020306180c0105040509010b0a050d0612030e040207050607140f0d060e0c0304080a210c03050f0c 80
    0xc00300017040c8081c1005998800c80d00160001c0c040c140004d4010741c0e514045085810000b0480f000c9800041e16442039a0588201c6510006500300709034410b038000c000801c0401c1c0100000c0d541c0e1018100c03c428001140740c01c0c80a0f081c09040c0135655610703050102410244504015005500d0794004601c4910074025148078551019211007018200390800c824200612055900458100c42c2c28000d030380d08000c903502405e10700000e0044960b03050601070a08001aa445040c80b04c100010082902c0d1007020904603a6010b500030303100c0342003040031181c0e407140e1030407941d4003800e19401203030440b25081e103d07191a10a84a00c2e0609462000b407205a0003402c2c401f8001d5001400042c80e0340380a00692551504072039242d43c0b91101600d2484040c0e04800341d40d0501e540d80344030a2020000f000e10f5560400102c89401e420740c80c040e03030b4240b5a80f0440394590100446000c00308903002401c817500c40d0720303200b520090005615001c001002000100c40d0003e042e64514081280402c40390 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 31588575 1250 31587325 31587341
    0x110331050307030807060c0215130f0506040b01140f0105030a0504030212070317010e070e0d080d15080c0906030a0609080915090306010609060f03021312030f1e09060c14030307051c 80
    0x11030727008c510703966154441c511400a240580e84460300591410008209018141c0720754400d0700c80c0c4515505010810008400d100c462030b0142c07800080201007aa0400250395110071800c20109484d038540c90100e040a0b40c660691910140100b6220109a00300f90741522004607004010001c0e03030b88006580041340290384160101e1500842003580703041c03209084800354010400580b030300c103680d1901d404a4201020441134442103020a001c010410b000c1140f0799841283c030760b940360800c0710019459403c00000242101e540b044540b08112411040d00c064240c01080c0c0140007519818051182e8450f5410512034002c5000201c0c2507030084034100140c964950f0b84003061420f840b002d8000b513100040d94203041c400d0b503c001070400b425003100301c0c07120311981d40c06460741500b56000e01a0360142c000c00c0c901b040c2e010400c40c5020f03404014041290310301e02e02480c200c2500d06003190071180400c2c845071070340000010040e002d50003000070101e103070001401c105100c540448900c2110380791 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 31589825 1250 31588575 31588603
    0xb0103090804150201060b030a0207050c0d0b16030b0d0f05061308030c090307030204020703020102121b07080f090a0609060f050309070b030405030f19110331050307030807060c02 79
    0x600c418050042d030a850f0400d048141c1c000015910b442d44003d604030780040355840e0140e60001801000c00205221102c600b590680d08003c8060203aa600040c91000501440c00401c4123700b003420640b1a401c5480103001c090212103200c0881d08100b06c41302180d0000352650310601021035181095a120400d0f9503801042c800d046440f03250303405c03602d54001c0e00755030b030f2621401d240030016994a03c01041103620039000140e40b41c01c992121f101c05000203010807000080201c41c854040c0031003003110000d17984002001e0707480140c10854103e0b4066070b900d00e5004510f00d4008134895421000841c00e4030180c1e195040780f01c44440c42190203100c11159529141c004030401c010b13080c4024003454000707100d00b0039070341050440d1100f064039070004880450842600b071048810f042d00032540070120072040000e90b1900b4840b905c1c0300074001074013000c0b00e100090394030709042000b2007480000180c00700a094450603513a0341841d0b005500548020703218941b40c07809000b410b88c00018040200c440e0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 31591075 1250 31589825 31589827
    0x60503060915030d030c0309020910080105010605040303050f03040f060e0c0102011808040509070c02030607031a060405010206040b0406020d09050f1204030b0f0c0d060602061009050c0d020c01020c0f100b01030908 94
    0x180c0384d0124050014000c0c14014141c5841a01e4016924500e210340709150b072032202002c441c6011109400e480041c0e12040500030100000c1c00403070341c0801210040450281030b2503030f035115480c009080d8501190007a107150301c0c2c080807a80d118400328801c030344280241d000740119440c210100c024504041d4004100c1798040004008900300700328030980c81300e00c60800540c0340c1003030340119080840485402000a54401c09000d404403a80c6448140000c2503d086003040c4c2401c3c0043d540307043c094009000f81e1140030000d010420150100c545030b01c040356007440303d0500f5192031581c0f9580d2180d100c109001c1d603100c1c1c0e800c4c151101e0030b840031285c2260002d201c0d0b859040c10743d04510000303042d0b952082c00c00c21010f20b0000c014003070100101550f50003011035160180f0803907101444e40e0484884142002c0a00080007100401d5492410781210016522581303140782c240240f15a0744070706218080c0351000510508042084104c401c00e2090510211901000440450301c216000510041c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 31592325 1250 31591075 31591093
    0xb06040605120a111303050f0601050a0323010204140102070b160212030c03160510060305060c0a091701020a140a020703080c030d060e070906031415150406050306091503 75
    0x2c9440c2c007998100ca020000000c14001003980e50006900100025950311029202001000750400c082c1408601600c041c2405504000002d84072100610000d0000210403240c84140b416403003003208004d25100086558a0791200a84080c80b85110284c1c0513024480001480441c943e04840e0000610001c0c121070403070b40c0e42000300952030480386003418402401600100c01040000709004d40710180f400100348442d05d07000d4545072041249825050a00d0300400000b0ba00040301c94011854494054484002500880d4400341c5988400720b502030b13a6180203003002c01980200b822001950310041c100300c0c0341d440a00188920241c04006a0102500b00b01165400b4042c2c20942424020b49242c4403040342c40b2019102c142d001180c0303600c0000c0074422407a411901010081c40b4030f08003031010584101e05406c2194004060000308070840e4000c0100c3d565140012a406240480c071175140c544802d4001e109801c200c902e60702a01c902c0d004160111581e14540c20512801801088251 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 31593575 1250 31592325 31592347
    0x5010803090904050a0803040606090c170106110f030417011b020a200619080a09050606060c012403050c060903060720030706050a0b1005030a150b0703050703030b06040605 76
    0x42d0028001d403268054000b0f080c0004414900542c0207901840b408100c450510309003d007110600c61136681806180646c40d2425900c45072054110354290828012503000140703c642006500ca100e12300c1c0303000001d0080b4005c280d000420400550b07000c004c00003080780400d9440b100300c01c41107200142c0d004642040c000f900c2c5414071305c0640c010300010300c0da000030000031400d40e810140040b01070f102454203140301c090b4408403603640320310005800d0012149640781c0a032206030203005e5034060140042c21080c00c8a00b5086101800e2500c85803103200d451540d0041614441c0e400304a0301c0740a0b000451501c3e283c00b1042d90100500107000d40b4964540a600707841070640158a00d01000c1c404e41040e2500009001621460740603420224040c0740c1002940229000141c0da24442c0300e0031040354030000ea0000603290700c004070900004024489004892040c820b03507100840c048000a48d02c1c080603400300141948a1003520b050040e04040400c104040c003d034010500001d00a21191030b83d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 31594825 1250 31593575 31593589
    0x3020303180102040f060509010e04051b0702060702030a0317060d11040b030a0b09010b12010c05160f0204091208090106051c0c030503030f100f0312050a02150108071502010501080309 81
    0x3400780480010314182d5100100c3d804480b00758007100110304082121081ca58000c191450340d000704480130801441c2812040d40050414094500c4c10200801c5d1103045440d540110307892580c000302103034240d00b03503458028230506000301e003030300c0040c2000089500c90501100d0942626401074002c08000d41e6407060200030040161302d19072500c501c01500c3e020440e0300120780d004e030300b82400100d507000800302804901e1400d04c4041038140c0c9030040e100c000307540c401c0660341c414050080c5481c40c06002c2c00c2c440c0c0c8400240c070010b58014680781d182420003101e1b84902c0111030240c2c48425090b030f20091581e00302c0d00c043c410b0541000e034030780c000c0300388507540e4440740c00c168802c400a00c03031035440cac1e1240f0340303076410440e1056004070000040c0246014415101c0000740025171039419102e0031561744000d05503e0b180c1d5241480f20125400304034a0080c00a40020b04001c514240d0960352405401d1381ea26003442002008000100c031355001c50302c180610750503030301481d00075454000d54600344441c3c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 31596075 1250 31594825 31594861
    0xf06040803011a0904060b090307141804020111010c0c03031404020108070807021509060402012a081e07030206042a030b040309050a06021014130213060504020c010f0606020a03020303 81
    0x284280130441680b0a9486100e480080d001c900400d641314181c0f0001c0c5443c041c45a000000b004148011000290ba02c2030b4900080205039001402207032610301c01604c0030084d0422019403542420600801c8a90188210b0b00b82da00940d418000c80032a804409440d00f429640039000448103030001340f44500813400d10f40c20030090b10407980340d004503a4101c0100c140070f5425000907000003041c0001d640e4056201c1035525040c0c0301e020f074007010601c0703400328814118500808800012510b8580c0641c0b2580c01c218a1400804032540c3c0c1545250007900c1d24000c4404880301c501540c00040c2d8460340c010034031706d1302000d00442c442181c2961154800300b82d00410031030070406000720229050310b030804803400801c1940c00400400740b80340800829074480d101a885011030802c00c1040300e1800a4469500c0c50301500c6517160b0004000c19a0098060358002031b821500004a0364889001540031440d031142e080341c10040c0c0c2d0346805040380c80e60400e1401900691041c00401c40d001d0501411401c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 31597325 1250 31596075 31596119
    0x91203160f1b0b04050609070b0d0b01030b090f04060e0303070e0d0503040503010c0504090c020c060301030f02010e0301050c0c010e0609060f070c120903050105061f0302072a080f0604080301 84
    0x190b10500807400001c8940c80d2201100d4a10f01d0030b00303100811200f00480b5400c18400b00c050143c65040500c81003e60049504850003140c4039201508141d01030381c8420408ac0029121102d1071800c1020080340e045c3c161070442e42c5901e04000b00c4070301000403082da409188242e0701c50303000e00c2085c4100401600001c00a0345d0602081000040340d0740e0902c01d0894003c015203074143c64030300c0c0a901c0c400f140c0740002c0d9030040d0b4000b030104014954917841202e0560780e03c04640d600c0b0f1105400125180c041185c1c1d45601580f0700018417954000700c0300501461840300c00280140110007030802d4940340262146140c650018020900805121440301c3d07001c0c0d41441c22003800466a03c9601c40900c4030780c803000119400300b40a06c2840400e004050b0702c8401502c2c0b910350f030072aa03040c40e403044400441c41e004065001c1501010403034144010320740c2603a0390301d1409642541d1140042e088889114104103403043c841c0d180003242011070128400d85e00480c0c803905680c42c0c0105101e031586201c545107 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 31598575 1250 31597325 31597337
    0x12080702070b1c18030801031b050d0201080a0207050d030b0a06030b060706050612010212160c0201080106050d0e03071101020f0a0b0408070c0504020a020a0b060d05100b0411070506091203160f 85
    0x54501e201c03503140a5101c0c046d0381d501d070555140d03041035081e051540c10304108212110b1000d0044d9100c3d20581300d50141e0a19007408141c3c1c0b40900c490080c0282e0350010101c0c0618410420520380c5904500c3d00c6150480b280c40240307950700d50035821203407c034110542140003032003a800401e40940c0920303400b940160031560300b00001c0704071908a07405070048110000382d9109112100c406480344c900c550085060150810405800180078031105125a108012000030300503640a0150020042c040900044035100c5d031292411005c0a0305a5440c0350041c4a80d080043c40800b000507001c07100394003d041d03000c0035107403a150f00c5a554402c040a44000c01420b81c00242030301d861004100745c000c980c4c060304120a4514102d10510344c0070f403146105080400c0d400c4045003010904000091858a000038201201c20218000d0f2003401600c0001000202d140000d110011810b2445510350500fa2000c000c0020084655400203a503c00d11200710096428250303030003925803204070041403c00b2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 31599825 1250 31598575 31598591
    0x60602060c03061206010e040303110a020a0609020a09061205011a061804151202040e0318061b0a081b01152312030403030206010b0703020309190302040912080702070b1c 75
    0x1c2c9103000002c7c0d0004178155805000c10040c580e061084600000340309401e03032314140002000950341c0c18091800740106642d214200119614402c00c60000c0c0404c09090000e15039442c5490350708074442c0402d40c0c095092030650200300507801780702680050000c00c550705080260084010046040c46403a80240d500d010f2800d0100f0051a450300900c04140030f605645c1c0c861040c84156070000316410b040b544140081c40d02130000c800c865440340300650300180c88040100e030100d07640c60441000c0c1000e0007181d210200b40182c1800034107090882c11000c010340901103103c58200d0b079003a4910441100034110a00005540101000c0070031200524418800350640003c0d003d0890500c016103d648001400c10405806110150042203040840c0d42042d8090300c02944030303c02c0000451081038112200180e500c0c078401e1041c00355030041c1003003041564a20744581a204002c0340c5401094403600012401440000c00b10300340c80310841d226040c000c00900b40ba180440301280c50411072346600ca1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 31601075 1250 31599825 31599859
    0x151308030d05090f0c06250b01080a0308010806090604060207050c0316230901030609140102030901061a0c07060305060102071d0402100c080702060d020702130c0909060602060c0306 80
    0x80d10750a04818400a100e003004600c2074074001001c0502c00c070a40141c0c0380e8088075503400301035a0040c0d540c440550f441100c4032240400001080707a000702040030070400400c0741d4900180c1880110312135110359800da42c03140700d155a81c850031203080c2c61951000000800191075600a40f00d8603201d1001c840450280c44002800d00c002e0904c4440840e0030203030108060b5100050302c4903084211440403101c1c880620110b0449801400007500194459189904000c1900c0204031800c5290340215240d0038a64030450203005144101c2c0d401d44203684e0410300d02c003141d40858403035a681a0082043c0c0745403541c10303400b8041c0102140d06501461200082c18101150b0500c4d210100d00741000c01482e0510400018541e040c0c80c940400041c0308031000010311100c110b401098044841d203440e0950641110064170440c800250001c140081c60403010103a600216110002c0340c0301c8070300e8251135107a22403c655007842905e00592060000c16109a550802182c0240700981010f03030341e081c00c440d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 31602325 1250 31601075 31601077
    0x20f070f03120f06060516050a0b0c09040b040c0f200d03050405070609050d080c0a0602040e0a0b1e0108060607020a081c0302071101050325021e060615130803 70
    0x12040d03000c512200d4400180b1030681c03181a51400710608204602410001e006010303000304121803840c480c100000ca01401010441c10410b00d0b0b0141010b06140b0340a000401ca0360000c40015000d64209030700341c0c2c00d62034103004843c200c0004d991030028529003040219000514900522034824145040c0c0e4080d010030320031900d900354151400706050400e46070032441d08407960721000030484031603418001c80d540e072998015110341008180b5281c0ca0304201803030404080001c01049039100050000f8070504d480041441070208203c20001c914126050082005040c41d100303000701e1107100507103025030068140c0c0d90040000b03800325040c19030507804071b0504003a42c2c100d14800c0e840075500399148410a180940404001e28003541011050b6031a01c002091700c1790410705005011000a2201c82a10210208004010070500607004002806074461080d81c6054100c2d908403641c240c9500400503101740180e002501d68444028501c1c020f901c5a04000310703c5e2001c2024050002c1c40e450300300 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 31603575 1250 31602325 31602353
    0x90203010e0c070f0210050711040b011e1106070309111801051c120503010806010f03170912070e07090b07020319050f240105030607081501031509020a080c03040b0a020f07 76
    0x7846842d520408c0f4200200039500c040740c05445a400c0924045090344d01c00b010260000f0000c6800c5102c4509113810f94140254107001d403d81e110f48130400c95071030b030700d0342001d85607034002c01180700c500380e15000380000085c203d803c00400180341c1e001000075013800d00d0603141340c40ea41192010160700c00d543d000303481151071040c500054004001448212014000c1600500200790b83e0b0386d00c0361641d9110640820b030901c0e5640c07242e90100f00a110741d1130704100030380c084045906135003200b030315444141100b040513120a40003030004580495510201000c50344459002002004910040f0380881c81d01848480129800c0c014100034108510b03003001150704005200414a50300c0d0301243d911010068164850303842940b00f40c1c180304403980c0000c19250441500c007940d02d00e40306603400680140c07009084014403907810410009080d040340d40174107036030b400540d21514030361603003d40e00c0305500051300c02a22070002c5e9000b1450102040d40182141200309808074207003847c1c2d4030382aa81860355 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 31604825 1250 31603575 31603577
    0x9050108070e0d230717070b0406020604020f010311030708010315020c0c040216210206060105030f040201080912040e011a040f15030915021b01060f050111070e160306090203010e0c070f0210 84
    0x1581b1200681d05001d4240a042c41030386e1941424603105009503902005003000c0d02480d080349007800c240c1d00c030ba0460041d0000c4960043d9507814402c00c01032000d40240310548034505101505100711019000702c0e1407580c1ca200013049000e0703281c02044002c0d07210440b0710409100c210340c040b0001c2c0d42005601205011849012465015034802904200d0001c28480c10403400b00b041001911a03400b40c2c1d82c01580a280808a40d500c00f03400502d800e04421403201d5800c004107001403102c500751180d50507210700c407004110090130034613045c0c030a002d81d028180c951081a603042c000c040594001020740f07044d82c40c001c110401e45403a000050f230045c408519000f80c00050078044e0f0400080107246075901d0078001c10010789006203c0b282d10301c0360b014030f504010004050301215141008000090142d1108060450030b10003001150038100f801102c010a007030860018030203800384203881c102da04c6a080c9901c1940d44c000030400550010501f11109a001c800100241c6c85514030700b80b800010b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 31606075 1250 31604825 31604849
    0x825032a0504060305012106090c08121b0601030b0103080f0403060204230d0503030703110d18020a06030c08060f0414040305040504060e060d020609060c010c09050108070e0d2307 79
    0x80900040176600140c0009100f980c003984048040201401c40103031060b08900d000500c4c2c1e4072803030040c01c565181d5011485038812070300c1c0880080d484400420610442075460420501c0b203200d241c4d01d9807001d12000d801c1c0c440c104e00400200c2c0d0b0340401403080700d0031000090714180e113136030f2080200e8115400040414000142d440c0c000c00743c00d1254404e0711011900107011900c2640c1e1329036644401085401059101e5401c2034501540c041501c0404a40c0f8800348104803402d24003e02040002030280e2244060010000340c40b8081c1c4112981000c0710341d141c0e000c070758400303080c000401500070120760043d55401400c00c80e801419030b81d034041c0c0e02c46c0c0e4440341d0303c0e450801000b0544250360889000307600a1024880c01e07585581d0354401055050b1952601c80301c8980020b1203d00480c0e02001c00355080c00320840904da40000a00d080d124241c80302801034603150b000b212212640340038540c10003021050440403810600c029103110741c090000d031810590046d03019041c038044c0e6010f8008440 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 31607325 1250 31606075 31606079
    0x30807090501020105090d050a03180812071404150903050303040606080c1009091d0607080403030507030203041e020a080102040609030c14030607050304020d02040603080702010825032a0504 84
    0x40e2106004008000910082c4a10b00301070042c5922045004032070414444001006944c01d4041d4020401007680c056210007060310f035050258040d886004254002d00c0c0100c00540d203a8054081501081d00d8003462500303050230180c011280d01c003180c80100030b2019445001000400c100000c0d4480c900c5010b001c81c00a1600e12280e1901810130b051034860580c00c00e10300410780d4400c0e0348200b00c50100748041024070300c092041c0c4102c1c0340408200003500521080001d841d4120344903034042c1d80310355070411555564035022000c07070105440040c8510442c0313118020a680d104056a04240010190350304c0d43d40d520a810300320307130082e0300c07800c085018007504005201211140c1d00003000d0403103e1510340c894080002e41c849400800003400d00c8008408203040d91030b07001350300e00d20315800380c02001398648030f040c0009280c20210040b030001c0c28960000344100311f0150241c000f942c11549000d4400700404058015080e040032603140300805030400c04460b0b92100b1030308459a05a100e030b6030780b24 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 31608575 1250 31607325 31607327
    0x50304080f27011d010f08100b27040209090f04171801020708010c080c0307030204081501180603030e01050904140103120f0e010206150f09010e0a0e07080606010c0c12030807 77
    0x4605100c4100ea0481d84c08003100702a60000d4540218030401d15000003140d030380f8500044807024a41000d000c1c40c20100d50000e4860040f10320209001c00d280302020001c400e402084240c1c41071201c19034000b58007502045241d14051041d54000707100b043d150703074105402a82e04215820100680d140310b1a0620440003658040c002c43e40038004600091000c070310305a6010703105000290000c101c012001000402151003541514094103058003a21050700c0f43d1254101c44c44802c0c003a8212054110a050740e08003050300c628401c8a6041d10f41489001d54130b001540c01d82c004c5011141c01c0ba490f08500c003500015083c03118003a42c440d1000e0076003090301c201d005150b28030040c000c00074803c1c074110640e00703aa0005101c662007060018004990705110000c51441060b001c40d00ea00702c100031001060308607090310050b108025225041080c0549070702a01d0f5900458440d0720126042000425a0365200309145800315002d1000b0b901a59550041410482d440c075105030001595501408001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 31609825 1250 31608575 31608587
    0x118060506010e030a08040509090a050106090f0b0d030806010305060a0306060305011d0615190b120103050c2403090102040f08011e0603080a030903020f010e01020c070b0406050304080f2701 84
    0x410300c203800800a8800e140e42c0c06c001480343c4c1c0656032090500e2400161010000c10003444490b0780400240400c3d9039840b01540500010a40c52030920b041074018940b50400d42410f01400c0c0c0c1640d1002000d440b83c100540c0107000240c61550020741070500071003c18080d0107148001d500c03d000004030f0410808143c40c6c030340000802c612042d0802800d000440801107000e080c0210111341c20b04001d1090150141444041d43c005618030901050b0030040b80c0100c4020340c1200c3c02581910002c000280401956054440f8940484002c0b07840d0080c50140c42801307594041e03271841c001460151145000c1e6a114407560020f4084d071345035070b40d94200e10b10070800d203040d000c2401c0c0305020840c11595500c01e54010251580e04140d950300f01c4070107162003004007208030b090040081003c02c0c0740d000b405001c0d600c8480144903501c540324002840e1002c41d01168211101d80e5141810b540300d540d1014040c6d44070403030318103028070144640c2c00c0001c031041c180f5807440b00300340c0d500d400d1560220003d004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 31611075 1250 31609825 31609847
    0x6060b0903030403030332090d260603010f0603082101051503040203010b090108210c0a020d050703080d020405100309080d0e010e03070501090c080601080a03050a02011806050601 79
    0x4142014800349006460020076a000e4a07414200403490400c9882e10004164075080c0800841c082c4110000000c1600c0346554080e01d8050107850781c0d6a0064030681d80322421102480010386402c050741c00e50301d606100d05800600090003c6510000038444d0821754100d6041518500400114910108001442c4080014003040303102999807611000a1047c0003c08104140c0d4030000000340855500798044a044040140441c41958403082515514600721a200e4102c1d00204200c6580c0905c0b0340503200c6446500006158814082c0d003403180b86da2290303400b120304d803261110210000300f000d40030b07206048003007900580700d500e001c040207030760a1444040c80c00d041c035100e0880080b42d002c0044858991442c407011980300c0010301124018403596502e0b24503800701080460800506401071044140600d020418094844072880d803144420704c100040d07030340210000740000b030080c009040c400307045000010f8107040070a0310f030b001050b00a10413610255a80e0401c04c0540c0c2105001e04 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 31612325 1250 31611075 31611089
    0x50603061302010f12090b01180f060e01050d0f081c0c0302070507090506060715020a020705030f030406030c050c01020c0706090b07030509120c060d0603020405010e2a0c0d05070606 80
    0x78072201e4002030510041c500054080083d0754036134201003c0e098004046903540203001c00b4076507950b00c019880b54a0b107071104510160070306519480c001414027604040c1c2d15160114501070b460081040189444240116540c0110750081030104d107004002e042e10645109424000c907120101006c106c071250480c3c8414188180903c00104500041e100145d50f18180006119100c039030000b400c500400c90010705010410984650044090300500b00300c1201750200d411194503081050380754082c2c2290000c0a500c207101c03c005051180e0496030003021941004e03032411842034049800e80e88045240e80c1e50b544071100821015600108100042990072100f5080c80c980317980c020818824500d28600c10f00b82420b070408006020b000580d003400b801442e5035929815440010060f002a02c010303071007507251800000300c40c3c50030b4004030300ca04003810b0b00a420080b003e440080380941e900e00c92828bd4014019203511071800c010300d220701cbc001e40c1c40302921038845150890a031103103074010348 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 31613575 1250 31612325 31612351
    0xf05010215010e060d24020d050108030a080415150308120a0e030901051b0d1205060405060d0b090a0b240303040302011e02011103010b0403050d08090d030e0c031005060306 76
    0x401d07880f644250828002c8400c105400d84034205541020415420001244e42018869100c1c6010f91b00a0403131410510091000b6a6502c0752252603010700c3c141540440e46150000f0005058003401d509415100c00c03001074001c0340842c228540b40c009802c121010f00000441c204003490720704030150b00c899000c50510110b001542c0450300e80c000c02c11440d06020001c00c0c52022440050390211603171440743d04407007010005410042c244c84070294030701011858070300850100d00740350081034400c01014003050745103c084c0d600e080c5200c40c0100300000c03a00030041c0e140b000880c0300c044503006800120388040e4007403041002e944d0802c3c10b21681842980200410401070340c22281000b000099140c04003810200b000c0280d0240848210f49441804004000700d8107400c3d04018005403409031007200d48140e203122065420a100b551308103810790001d0000c0c6001403207904404481030354202900c03014801d940110b4607018104040201481c0c0314000c1050a044c20408164005c901407169 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 31614825 1250 31613575 31613579
    0xf05040b0301060302100509120d0201020a0f0201050f070c0204020c0f16240309051e03180105030601080103060e0c06030a0515060313121e0309020307060302072001180f0501021501 80
    0x10301c206c2d00130a055081c000e003c12144040e40d60440e048050142900903900c00c0340c8194802030003544038115140c003165509003241c10152051190034441d161422000400361180700b0706880c2441c00d40b8040b64850740801c00e02c02074100500c00d115145012200801e00304c1c141000003001009503030040c01410810031446001031320441c0342d60350f007042507040028041c149410440d08200c0308070f644100c00c100d14070030414a55000002090b40101e9840d01c00020002a001120280b0060300d0b56800280001e00500116146501c81c2000c114003408881c04040c41c41d010507081c0d003049803445c0d074650381c580070482c1620b05590841c040c8242140c0b13031490f52900c114003100d80101540c02900301c400b0000c0360841180030b6070f004030610345002a04c00f0b0b1082d41c0d00005015126009080b4001d0059050004641d40031380203552032035a110741c0800b0700f03030790050308070103001080448141000891810481194420070031003014080913005a035106040c0000a4642442210980c1401c5200001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 31616075 1250 31614825 31614829
    0x50c0a08160506030405010204050307030b0f010e1501140c0a0308060915030615030703141b03030310050607020418050604141204060309030903050d090611010b0d031b0501060f05040b0301060302 86
    0x74601901d40880383d9544030f445505181e802402541c00050305403050400100501070b10302c12451048007054000304040c5e0b260465400214019a503400402c1d1130901d082c0c0346980100074500c6c8140d030400301c0f02c0c100740d82042c220303103403800683c0141c0115654000b4030045051411085a0004561030b945d02d5041c04240403035503986006240e041c460152442071010b540d001d00c00b00b4000c45c6c2100c0581c681c1300080c0900d83d101d503443d00c01003000d80711401c48000c460030048140c0e0702c512149030108040030b01d0a02440300301c3c1d12800d0200d9002d9a10301c41d101203c20b5411000210600850046c8614501850f0148140030b6010054110340d000610048401d03000360100e074140e0707072549808180031842c2d2606403010001034200510300e004101e240f1403c0c592011501080711b00c2c4e9035645207e0052400064201c2d0300c102c01041d009000d2004200200340610080c10800e1503102640b448029180c076210708480403900705260420031800c04205d1443c1038050100c0d620812402080854650b83c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 31617325 1250 31616075 31616113
    0x3010510120501060801061409070908100c020c0a0305010606120902060706020f09210c01090b070305030c0c0a0c05040b09060f1c02040504060603020a060f05030a02030a0612050c0a08 81
    0x42452103040c007210a48003082000e40081008000c03040c0240032144c5c8541c0600f0f2003080d010910b038054141c10000400d00da200e00c2d100300c00c590084018041e40025008280b001d410014000c0c001d51064030864001a110342c1c1c4544011070060300009031a504100d402864201390050451096003000301c403102684e1440106e845c0103901480040e6541c1012440306410700909440c0d40d80181403800c1b252183c207010704484c1d13051420400f5244940d980710010740c2c0c03110071402041150034040c40300c400041d0141c0300464022401000301418240c50130646481d01c0f00082003190b414458000803c07150030a40120803000f0001c030303000c00b110301c1d04501054810646c00213852240c80c1c11010580f00e000d500c08942c031300c0c0360058002d0010f40b41904004001d043c2a01c4124012485a200045c070b01d441400403030342242180d0f0340d461454035103044d400040d400103808001390301d549850008544440000b10000148910060030102c14000104000781c8400d40c8000407a800190b4140c8040038002 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 31618575 1250 31617325 31617329
    0x30d02060c090609010e1c0b09070315150b041d0a060302010c0f03030b12010204031401020f030103061505060304050d08071103160804050303040e0115020a020d020d030210020409090201020c03010510 88
    0x1480b184d0711910080012a4400b407202105500704550a10684c0406c0788103190401e070b1401102c220095494440313142d681c40f02207210103440a455640d8214200ca01500b00d42d07208004111040540c6440f5206140c031688194002c0c1900140f04c01007840180c040b018040c0e01903804101000211728640010345071035100440200012003030420842014020b921840e1345c4400500000080504085068001c1d4080d02090f90110b5203039144840c0840c05000b01e4403108824580f080c116440c503507519010b0541685105403085102c1c4001c03a80d51a10005548264003c00c0202032001000d507001c2e00054019096008006c0141600c00802a002084030307286500c0f040418207815a60a1642040c0241e40241d0390500001a001072400104a40c1c181640d1001c14400503842d5400016a50b070005c00500a40001c00c0f60020b10251411250551030103009006456540d41d41001840c12039001d0f4000d4090341d503403941c40c00c0c1956810005080c090700294000c0003681002100c00e002a0304034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 31619825 1250 31618575 31618579
    0xa030b070306090501090903020f070b0f0304150207060203010504151a09010e10080f07030216020108040201030e070303260c0405040510031502030402040b0d0213020309011404050606030d02060c09 87
    0x1004105031510951040d0024220301900700300958407420b403c13000d0012004158010f04c15904110828400403c42c4e00c125900345850500d00503141146028a0304010819070304944c011800340c914110a0000f031a0140c0324400c0103990b903040508005c1100c800000800000c210210144180070540800f0050f400c0e02201254441c00600c004956030744c2c030654480d810402140d42020500d81041d2464026036180e0400c5000e40c0d00d65404408a024030f9102e4020030755082442800742d4020400345030068018500420304075a40040a803030450b40d940204e00003980400e04a030310014403100003d9450315203c0038641c900b0125060502401640201446950381c0d40200f207041c02038401980c01154000d80d0b5000440c68450208025003017201c09074010303814100340b542c262905800710103d141c1e00401c900580d0711644075403402904000c101600d15961080d0f40b404003000700c845548100e11400040213249040c10178142008032042940082d9403009052200b942c44240680d0b180702c0b42 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 31621075 1250 31619825 31619843
    0x4050d08090a050307060e0d0203031e10090e0708060106020c0d02091e0109020301180209010503040f060b0613080d08010f0311030703060c0806040b0114040b09030a02040e15150a03 80
    0x9003070200d81c10301c0c0c41d0b5400100140310001e8204100800350b00701c0440004000282c81e01c1030300413002640c84c2d1004481c0b000703544c0d480c011000c0f651070000d084903420205056035502c50036150200c810440708444a00c074143d074402d074420803d12074204080c0c0e003d0f011610284c0f030401c0c06200401c01188080400078490141c110004140380060f22840c1c9840210740c40001140d655100083c009510a004103c2144140c1a0300c0381c024086000f294250f201c182d440d185542d0700ca032a03400300d5140800c1d0460310140c4407031030340d80709544e03c4001e416842090341001006a00d0508404e103000105100f2a06010b221001000f81349491010402180e0f003000007180c00b07a040400090802c00325400c01032846140528980c0030741d600030301652145400b61000c0204902070740042d1170195801c00700d04224a8208414000c0c644660054020300c2000740c22900030701465030000c0c081d0381070803011900950000e94008007000c180c68002d0f8020300c0d83c1004100015000c40480c4a400450001070004c07d2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 31622325 1250 31621075 31621081
    0x6040b1b030304080a0f0903020607030305060310112101080304180209100827071205070302040507020105040b0f010e070503070512070509030d05131a040b04061806030504050d08 79
    0x24030440303580c10106188003a240c0c0c80c07410345013081e259000241d1400005134510801c00203140641109415280c0080c041424160156412005401c0043c4095010301079103880d106007101a0207100513020078011540e45810309403203500c0c5190800e910685645c03201000410440201100300d03426100403000f1001c60b004059400c80281c411038100e80d8004000c603401042c90396201540c2801040103012190800510504201304180c104c021901c01c0e0704194020800030541c3c10351410a5403154066801040c0d41340c0010b8122103080301c4c3c903400360b5144d6041104221710450740c1d60f40300a0b101354003896541072440040d40801c004000505200e000008074520a004e8400c0c0c680c001407a502d880207d15024200074041d812004401e4001c0c450703928000030042c02032003551070084686038200162442c10303041d0301d6990700360403515200303400030400880d110a0000081018010645404250031003e0b849801c074082c0c0391f0f02000030185000c051100007130012920243ca035002d0314103500e40b51 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 31623575 1250 31622325 31622347
    0xf02160305092101050105010305010909020916020f0328110601050904020117041a0703092004020403050f06090d0e030c01110106080703030206040b060f0a150905090903131406040b 80
    0xc1c1101101d800310f02003d500c401c041c2054002030705a500030303603050203242d90b41c44410041d941c903014025481244400041d0840f80d0058140c600c0454501c1110004003500c0d110608540c0100c03c240160149488100d61440034484181d001151501d480e0a0100c0406541d544514043c082c0500c6034108c1d60204040da0700c140b69646010442102400c2c03e418140303482c403180c411111495180707814400c000381d4407901a00c945043c1c00e0700030340c0d045088900d191203500b00d40705000fa40f40d030007070f820300020001c039204002c181501c8222070000c0085c1d08206401e031386014062a1150100502040301001c1600c000c0749502e11120203013407a40070200089552070142885811400ba075200380a000001c0c1540012503c2c01503000e0360100400707480d0401849036903940c00303008070340000d419942006026942440d00102092034039003074401944480004101080a40c1e03c90031540c400300c0c450780322030a0311100300d0080c60b1035000390428200c2c0c6808942c080c080c1d813103280c02c0c1c80400701c0d10721482 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 31624825 1250 31623575 31623589
    0x170606040b040801090506010b090d0609020402070803100612020f0a0e03120a020304030201030513031e230306011d1c0501060302040204030308010e070f12020a21050702010f0216030509 82
    0x2501e41d088000e516282c60701c03032441c003c01807050300f03803901d1042c0400024400c1c0d00d0b80460300001c1c0003414810928455449210141503501d03022a081a403c0003604082000980a54081c42066602c0c0140324a0080c004001542005940b14040d104001c009a4403481500b1142c0d400ca40b03003031840c6107c410400107414001c0c0710342c150803d4000080c008101035408402002a20b100741c030100443e4850300c807034081c003988485000380419a901605407501c484201c4900000105242c00c001590b160004682070100082042c10314100201c103220056810090940300c1c8803105540264049142000030085101d058980002c100812402800d004d02034111102454002d8800d6544558a1a00810306da60074801c400c40c070f0900402151344140304001c00190a2002d6841d041c00e0b50200c44d14000950010804c10240074030030032945140c0e04014010b2508602030f5200003842c1c500b20a020f403d40d540c101001441c68410072486040c14100b60b10908503c1d0545071203a00c3da00144089020 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 31626075 1250 31624825 31624829
    0x2010c120b0f030a060b040c03060305070b031f030b01060e01020303040b04150e01020f07020a06020d0e0114070b0a050405010f180b0901290f01082401091e0e0606030717060604 78
    0x5000d010035884c103101454100e0554210300356000c2049003091001102210f0042c04002d080d0381003c42e003005940c5041e00034540001141d040482200c213401c00d090034100d055803088074128400c1d07004018003500301c0181e0a1880d000c0c0051444c626150340d500201090041c001040507040c040007842a00350396020080d80284200210b503503043c190344207411031700300c0a003c901c222400e51f00416130a1001c44c211005201c20f46452160408000c011b403482c0d0000901040c080009109020200c0c0080f0f100c603008501c02d5500080c542400c1c2865401e40d00c0e0303e43d00b41c1c2180c0c280300107031440b8202280743e44060758005580803e1903c590a9041c0034141c1c900310010700900140600c2410104503824954195045825542c4000f02e0001076520050445d02d503080c10760343e000245515000f0f5107004c803812030149007100c1515105d200c1c0644069a0104800b200c00700702d5810310010b0080d45e07500350000c008890322070462426200c01485203080c0c5601307050907070488000c10900e488080642d40 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 31627325 1250 31626075 31626079
    0xa09080c0708070e060102030a081909060f09020909030a0e01050c16030507060801060f050a1d09010b18060909040305071103060a0c080709030305040b072607020a0602010c120b0f 79
    0x11880d548400300b940ea00118000c6481203504400410985e600010440d541c00c40140ca40301f0680d903034021160801c01084030050101901c800c90800010f00318803030f41841b03550381c450020394070710580144000c6410051078040c03d548104010700301107401c29492402281c091800a5490480c990084d0901c04507420002400159a02c04130402001050650640d140c1d55600f040980c3d0300c0e40100d030405404070045002c15820001603002c94410350810403020110040d00201c014031001107070415100368440029101d0202d480d484e8042400110450104112812800c1c40e00107000100199030180004082c0b1100142500421484855100303881c0c8004041c0c5c0e07014603002c1d0108000d090301c46400340c0003a01c901d000401f41d50141c0c040006036070301540c60358245401d1800200180d80000802e83c0e950361088900b2000045058001c0e46c2d000d070300c08502c0e8460785c00348140f00c0f017845190040790559042040c0310440d2640110103070034010074140089241020030700450024010341c8075140e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 31628575 1250 31627325 31627333
    0xf0105040e0403020705130b0a0b03070201090b090105071209020a05210102031e01052202031005040609020c0705091905040f05010c032405060d0c02030408030d0509240a09080c 78
    0x402410340110f00d840880700180c41f08041d40d000210500203c60034032405a5111a80c00018400f20f01340401a6610545900000809128944078a204010122000508d60391104104881140d1154400302103024404040c0059a0b03554001003200f07403103000b41e600805801d90411009940c0010740030b403006468000715600d040c04201503c209000108131a105081c00f00002602e00700b034412003080e440241e00302480326010200e4900650320161400860500c00c3c080840c00355110701c100310050030420b80c0181e948140ba00c0d41801e00685a10691041d440241042252032442d040410786940c14038001882c0c1d0344a10380180310011030540503046620305040d1251094060340021a0310340701100c41c2040d664803500841c603240c40c5014403a0840800d010354228962150000c21142d5001d00541e03062644640d81c0c07901e1904080101c0703240c00d0700c0d10706010442509100940d1724071544043c211603030103103070f1106280080107088007100c0c55944a1035810300a64200360340040000e04203503 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 31629825 1250 31628575 31628581
    0x105010623041205162c040503030a111306020304031a010602210d0513060605040234020d0503070c05040209010906050d0603020916020f0105040b0609040c05062701090f050f0105040e 81
    0x12000c0072000c180704080c1070a40c2081ba0904849000302c00c3c070036607100005500d1035640e400c810000d00b8584804ca144094180400f6031010901d02d1142d0240c1160303402140c0355032031820044603894101c1e5100009207094001805001c1d40812148005005007107107449980040c000030103d84500c0001700101c5240c54240809118200180148203024107000e0001d0380d1103030100000ca21030040080402c403606094407128035042c0040ea6842c2d01c0b007a01002d4402c5150300828420060300f4800c48160f00300203600c0c410011701268070b6000d49402e81c0d0450511030501c0010f020544140034100910001182c1c0c152040f05a80008001c0c5502800301c1965040c0105004940d8800241c12005405003d00c0000d001130140700d901d1103560070400f850790036110a400d125610801074400d0701c201003213100106035921910000e08601305e40d0407030312440c041c007480d11300d103400021a0040d0421041650400c02c0d01001e0340c3c4002a80c2c01180c1202e070481d81000141c034184100d1344800d101e4000c407420 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 31631075 1250 31629825 31629839
    0xa03020301030201170f1b040e0406091202010e030d050408090a0305010c0f020a170319020304030816080601020607030e0705031207060b0910030f0807080705010501062304120516 79
    0x6507040b2403007a01c542d03400f080f48200700c5007800000c6074480303200d440308000951002000784600f01010b045407141403030203403a181c403900b805100300c40680742c0a440d1034001c01004140b19565039001001d1008100c00300301c8413107036074070f034810980c482121980780c0e00801c061004810840c0e50f40c070001044114816a42d29215002e03049485000010501142c541100ca40c001b0480c5c0040729030013083c4001030420b00807171501c1500060502006031000601810662410b4401507001d91b0080c1c403400702c0b9181580b10f40e800d0f0b02400c0c1030403040100501c00e0120b10f0f600000c1c00358000a2505001c100d61003492141490146944c1c0102d9041c03003500c50707003004d20a01000801340c02e070040009126402c0b0080502903200d000307071021a0050020f50040010507403034814110083d20408102c0e10707014141d280c80c810740e00300f10019991039560f00010008190001001401c1c03803603000c0c1082440d00884204c0c60240603a200d0007051035000c0110808004082c8103442034514000b100c0310b4800d8072002 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 31632325 1250 31631075 31631077
    0x30309070617240109090c0f1409060403080c030408030a09090b040b0603040b0402040b1003051008010504050d0305040303020f03150301050609061003050612030a020d0e0307050f010f030e01020a020312060609010e01050304170a0302 102
    0x1240e500411270000040c245400e0140c1103170201480501a149440d02c3d55882c419541d003d580e20407143e0000340f00118030418180014880a00c0070390300c005105040551003003c030342c0c9400042c1d01c80c506e48032980055442c0c2405803a1700c06e402000c0c4031040d0b903403400804c000e4007506a86660200b04108890316041e05640200d00620b2500340c0c1c084007a4035000a58202c3e40c00b030760081c04c00d80c00b0a550307404c1c840c843c0d006681d00510070f00c1c0140c1809451507220501e03420139111540b940841038101c40060509104107036118004541008440c04c0a00124100754a81803064080540b1000000d400d6100d502c04a03d0b480d81000840351768a0088000a403104401204440082d1140008244915000400c1e2082d01c40082140202005190045d074508846010780028107880300300140c3c0241003840a0244011240c01459a4840d0311b00e00e1000301d54003e1407148500c0703041c82201c40c1c0b40d030301c00005050007400303081407070366503c482c1044d05500c0110b0840c0445a0000507100064686c5a0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 31633575 1250 31632325 31632347
    0xf060b0307021014010303020604021e1302090102061e0c09040e060405030408120309030d0c030b0409030905010f08090a03200f150903031b090a030203030309070617240109090c 78
    0x143c000c000b0140d00400107440c4000a04c4040c006901160124006d85041001d0b484690b0300d0310391541300c04e1140408a440202c10540764002254045941401542c05001c1c0f181d0010403036842c1880200400e0044c6104200030b0102c9420010108040303c444d16217902c00400c00211000320341035844c1074a400d035070783d9200340903018850091900301da180c050f000055a000c0c085841c050b48c10008240140001004840103074403c1549801c035828580d10b44d84600700704c05019079942d8551074100000500f181d039080400504001b6290104070035101c02080905c0e807250305103004820016040301d00000c26540701c4141085010b560981403c00d100001d42c140c0403000410948030310b64a41c04642d842e80422500000c0c42e854550900c1e842800d24001028030450003060307280e406031603030082451604211240d24082d40203e00c10710880d5040b20800d596240140c031602c0c003910b0188407004c1e407400b1201459040386007a040b00d090580c050009000a00010401005072040c0014000c04001d400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 31634825 1250 31633575 31633603
    0x1205040807050708070605030610260f10030f060b06070b13021c02010507060e210c060a0903020730060b100207060e06070c0f0f0305070e060f01030f060b030702 71
    0xa10000240c803a0b005c54000220f4205454032402c607038500040c8403590b017000001d00100800851007210b07014050030f0030803d18411500c000a10f18048100300b0070042c000e04405c0240c0442d540c1040040c1c81c15504195081d403100002c907400880f28080303180c50207284002849210b144041040d07180d02c0f801d11170360007402101d030b03e40d0b800080c403064201896a481c01a000410801c81c1c100410b410743c001040049449040b00c203201c03151034580000c034100d15060403180b000007580d141c0c00c044c108a0340e81c005002c2c040401c881041560040d50365002807059803081d40305141d842c56a1206c000c00050f600b1131041311605010928036008001701407c0202500c100741c50818011460f04c0003642074161499500e4280503035410404014094000800031074840503001c6000c158400e00c0030801004140c0480102e03462403c40c039085003041159004200e444072030104103c1c01d44d80d0f4813580d004100d02030030001180c600e010000005011242c1020f4120203000090100144d80010f4498603900c0b5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 31636075 1250 31634825 31634833
    0x1b0b0a0e010306060905120a0212010608070b1201061107030501060603020d050f0609010902070512160302060a0e0606010e061219060b090d020103020a120c0e0907020c031b01120504080705 83
    0x6800540890f100360207070313800048581e0000c0c0318601b0303c0000c0514485100701141c0240940b940040d211858851300c29030b181c2d446100801941c1010080c00c00540b1190720000e007402121458809510b005206100806c0a0305000d800c0190003071003107801660b004002406115243d010240103907000d030800c02d19070ba1412000550144841021500401000b0055049a403900a101000c4c1d002500152003501a4680140c208060240200044051103c400c2407040a50802030f0500500600c0ca010150404554074401c000201c4c0c2030398804002d0801060340211030000c201e05e8000e07080603000241980040c85100c0c51004070800003000b036400144030040e1030300c842300018050040f01540000481d40c030a0019800394001d030030107032210316103419900210200301054490039100c0602042540701000c0060800e40c0c0c40702d910078280c1c0020184582041c021907038400d508a170040180c4000d55503425071760700c00d0844602410080c2d03400e210324106070824070a158021001198240701e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 31637325 1250 31636075 31636097
    0x4032709051b07110f13060e18030a0203040e1801020a02060603120406020c0607081306030903030b01080103120807050c0d051803070501080a05040f0b040b07031a0d0204091b0b0a 79
    0x6102d1080b50181c40d0b00001d0f502007141100e081c020901d440303810340740e4060481031444136258030b1417103407400415a511034061241040948011103c0f0344004a10aa4104000502d01c0c1e5800100325811906101e07031500381581c4240c604000c1500341540c844c01035000090b8440c090764005081e41c01801d08a060300c25624290503a062603101e00d10818005d0381001b07150242a180c40c101410a00340525005482c000d2040e0038403400307000036084000417968408606080c10ba16200e404482d103020b003001c01a950540d1103040c18105031141007410001000001203200740300f581581c0e4808400c3c0201c44050403d03c1002c2e1158200e4031880030b01c602c003402c19000c10b00d40011030908888060f1251f081c903031601442080034040042013542d080c0058410700000074200112188203901030018100ca609100c03400409454111200c40700240000c85c44800540d5a0781041e00c0d000d60403500003e81c145c0515103201203490040a000c03c410684500160b0302407c01d00411200415541d0020004e07 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 31638575 1250 31637325 31637371
    0x15050114010c03050c01020904020f130f14060306150c0708060a05220f0209010b0306090a060b1b01090c0602060601110102130303030b0105070b0705090a17060403270905 75
    0x1000c24456507000921111811012a01600042140041080015140010200c0442c0699006c088408500140041c01750310b5910030884130700180c0011a40c2c06100b030701d4084040d4210040c242a00d100b83c00020103e11941c1d00c940810090090458481c2d440d40c00c25081c840e1101d502e4480c18650380100400540c18480038440c0b144a460b0b21680561350f0042201c031150000d103c8841121032010510240c809a5200780d0841c1c000c041d11101c81da602d02e0a1024000300280c0a84005500780c02d2074401d011403000c82c0256000c89c003400301c4c400d040360318611943d4050110038030054001c000004021402950205403188a40030a884030f1841031803440300705081740311311603d8410818540c08c06000203880f81c2c2003950015014035143d401e02c4001e40310402102e10990390840842d400107500c1c1454102100e0b01c6005000440001941021418a250703c2c0c010003400182005040c002d40303c003140c41d00800c40907102000c1ea80304001c07601d500b184401480c09031510b41c01000000400c0701c4032 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 31639825 1250 31638575 31638599
    0xb0d0c0f0803091c0213050a02130503010207052802090f06010e0303040f050f0117070903060605040c0203030c030a0e060103030305040b0f071b080c0a060207060b0a23010516150501 80
    0xf0345024040b9203101420a80d00100341c00c0c4004200e07840558850a0703e040c0000c0d020383c600400c0d0186c0c0050f502c4542228030150480d50303520280c040d90051000f4408104085002c0c1a81c0c12a00c041a0468425249841e002d50803c00c000358001c5010702442005017145010502c50102a00c4210481000d6810140d03a0300980c1304440c40c44080e07000920140c2045a214038074108181000100c0e2100e8010b03000082c0d2040303e084c0001501e148041043c0582801903000802c0b090b1420401c1c3c500c6101d00a48900c4010211125128000042004d0b59607580c4040c1c00c48042c001a201c80303503102c2c64018040c0c030054405039002c034030305000301d4290032413400d455000d00c6007a181d040d02d616401458110361042e0704030039140c0c264184020b81e04010309100c050000c9201b50030060781c58103a0b10b022403c64011801850090a00500500000300009090740414241c0d030009110071131080012219442410034a030000c091401c504010081201100c0d465501588400d0000e41e8a84c6440090 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 31641075 1250 31639825 31639837
    0x203060a0e030d0b130905060609060103020a0e0103050408040803040602240105180402040b09090c0111070b0f1c0c09150e13090512042d03050307020f03010b0d0c0f0803 75
    0x30742d00100040c01c000611030340701410b10800580b007645141c0c3d2185e0302000700c4100c4c100c1030310030350803281c1007141d2840c28072009079200d182404c00314180719080400410102c2d00307000144c14541e0720750228041c004000d0581d401003602d8421641d03550b4944600a4840c6101404004d488100605501e90090605803c07811307200d0243c019200d442c484031410040841c090700036030300300e40c0c2c80340508c04644076201103e118000c14802403151b492144001000904c10404455042e040314074203001c103a01d5117040b0f5021542c11070744a92078904003554226180340004420501924190781244c4060b044030381481201d00701c0394280201005440c041e64244061134869900c59010ba0f0030700300815195021303070f003406e000da42114812201d00c1e00403c100c0e0300c503030000300b000b04000090200c0001502e55100c21030040200e513228141c5141e0361140e40e030042c1f01c0c000740318040712140b01e1800e481c00d511006110500902c05041c540403410b00b0b840d10391040c050741800411001021540c01c0f0004100c6103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 31642325 1250 31641075 31641101
    0x2709180a080904020903010606050a110c21030c010203010810064106040e040c080a120302030408121302040b220b060403120203130518040b0601140f070203060a 71
    0x400400c0c036a40303003035180c1d02c21400c0740d51081d030911003101e89031024803030314020300b9803070f1103e03030703580080711310150603580d050038843e0081d801108034101d162135a0b03480181d0340039000046120910b0ba80030305030550088e000320712020b41c40030000141500000840741a42c80c10385004110060300c0e1002c42ca0000201c040c1401055465900420518610080300f021050002d40343c0c8000307558070000803010f6000da400703a100203502405110601a4543c804401021850010680340d07103255903a17032043c050030308240185036011000809000c0c0c40300031145052940d04081c081c038a010812448143c2900b8420f90040d13140030304113815828400010307541700b000c0030f420b00d400d203110b5183d9a0160482103070301390b0000320600001002400c0540700c0004030900b5000340d510385a8460a0000001e0310b54031a601c54055001d18900c406e03c0a040719030071030307000440da9915507901401030302d11541c2d00200c420804000190f5400c2c461840c4090200d2070b10860a4610f01e80711690420162021200501 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 31643575 1250 31642325 31642333
    0x209060604081c020c0d0605100503030901090b093001050c03060604030f06140f1b040e0703020304030212040801090501050c0405150a03150e0915040308070c020105270918 76
    0x3006000000c40070009103c2c02d20484802510140200742000050502294030079110400d00400b4580d54143e100601001c2d8015418003203da000200b5502c118800c40d8124100021280f5503074840d03034446030000c03070482818114032104582e040c01705c90070041d2003c0254a840046070380441039070708490045c41c0007058039052a066444c3c4140c2200c2051007260420b40d1403884c4218200446c0d41e0038030031903181e0800c810603c0c00e00c041d0a1140b5401c01d902110074010003080c42250341208265402695a01d4010307126961407a059107814030b140041203d6890100b4000f40354401500310210682c420402032116484441946049000d94095694003030007110003280f5004028015141ca8040340c900850140e401c42e03c0d1181001054001c1c0c40300c10b0509003042284101001058a4070585054555030b52034079490041040e0006081c3c4070810048401c4442507a200d101600c1c904c000c990300c000001e4038000b40d80c580020307504101a01425403080003d040082c10400ca85c02d000c00e00e0050 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 31644825 1250 31643575 31643593
    0x9010c02250f08030318070501080408090402210603070501030b03030403060507020709020d0b040501060807140c0a060e06040c0602030301121205160507050114070c050405070e030a0b04020906060408 88
    0x300c5a04060703080090050741c0e00c600090203180c1c8008640188050b10185a8038240176440104424045000c202c165002640c2001241da028846503401900200c09a8440e440040001d02078400e80c070039480001c200301c03916400140d001d064140a444c2c110100c2e40303a07559420041d0706031002185001c0c0c1c580c00c00e120410200743c480d00203540c02480740c4182c0790910384070620b01c0d0032a001310b201207084a035601044402800c25201d20381c0540503600308a107032440c2c502d10003007003a44458580c0740c05c120301042140107084100498090980c0c40101800084042c2d0060356480c60308480035501c40c036a24000003003c50010044905940c0c200191044100c001d480313081d078100420900e0800c00004005040f0080160951141d2036441207002d4503d0034a46400104140c0800728284000c100c100700010018484000300c0301129400e940204043d903d5078020344107406104c844640602890100504100d0742c241c20a1003a48200d9202440d625580107002c524002c5000303078841c0b070340807410f2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 31646075 1250 31644825 31644853
    0x301050f0d050a0b100b030108030a0c1b060e0f0a030f0809030a02060f03070201050a05070509120a0c0f0f080a0c060c050703020a090b0301050604020702060703081506030f0403030509010c02 84
    0x14030340d08060050314071008040070340d886910f85080d48800b501c8040441041c40050100c500340c07900105241c40410b0b040d541400a11034403803103258445000e1007011011034040007041d400c0c0c0d41c46107050030801c8003200d94640c005020700c5d0071403085500c18012448420320720301e405c54080301503036000402000d1188407503440400795405501e40d55458480d01044100682d206c0d00206900c2c141c0200450312804d0468001c0c0c00e4400242c009a07035030741410200500302ea4880c06813512403070304882c2801c40d070515244840c2007031a0140c02070300d254002000403c55289004e4001c003165000603900080c02c0e65003484546a014858000300002c805540030090f00e0701c25131545d8800750041d0207807a425942d0342c1c005017885155620020788c968503908006068542071003059480001a6020b618009565002890a200d5880700034144140303e408100178154042801c1c603600805000d1680da0300748050009018403003160700f02d0000303040000282d0044010f0180e40031711242900104008190414 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 31647325 1250 31646075 31646089
    0x1060801061107050616060b0907080604020d11160314040302090a090201030b090a0c11121209030408100504150b090610020124060f0f09090510080f011401080a020105030105 77
    0x495205640f1545001042c159a107400500a9100a16103020400c0591402c0019207403420b21040c8a980c10404004c1c1184d00b01501aa000c14111401a900c081d6950908001c040081d40180041c20105540c40b0107004d942c02c00071003a000b40c403400c0074480130008401c0305105900000350020011008564004a503400041000e40f0504000c5905403510004c610516021940d800ca243d8a6001c0082095004801e402d400f644180c0941500e80d1340d5a140e03a503921800c0300044280390803000050700601d00744266406010000140c03825544500c0b0b0301c1000e45802da0f0151440c49030094039031210769203481201c402400c06040c062043c1c0c0c0d010100303c2e03d291284900360555403220340c00f80f0020f03280f51219070100300c00c40c0044000e42c2024401440d819a4a558400348004007500c2460580c1055103501180d40e01c09c1c010900d43d0310046844010032550344001a01c0c030646410480000043d00b10001d851001007c0e070320395a9848140035914010038502034003103002000188a00c2c10081 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 31648575 1250 31647325 31647347
    0xc0409060b10031505010e030309092203050301061701050f1302130308120606120a1503060903050a0305070e0d0305090d0503040b0307031407090b090d05030a0201020a02070e0106080106 82
    0xc100001c421000c1800700d0681100005500c0000b55111380020140001c1c992510181a0a10b00400711480000102c0d9607480303203031801742c8545260400103a40750008150410748541c000b0000f40b00d41c90b2407801503c1c41d0020300541d004109004404d21b010308540c4000c6040742c41c014000c020000b4100305100c00444035840b10182039800b04400c21691a183d07803103134015403064030f425980c0e880300d0550580003800901007034412482002081c0c3ca90884195881e08007046541c0056a2004000b00c40001220b80d40000c19040c203051705c031070a0640003000740020710810349051140b603440400850b00c51443c4203410398080b00c0034001c1c0000c81d11800103002500c40c0036018001c0100d072038480914542099202c0005c0540002c00c02410030f80c14007501d00404d101c0e08084a0a0800c2c0a001e4841901070103110b0001001007103c81c80c0396a403600a1190b160090103480d560089684000d003c0c1d401080e150015100708140010b41c51094245130341203419aa4604003141d017032110032521b00c0300389 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 31649825 1250 31648575 31648583
    0xb0105040b07051c0f0e0402070b0f0c04081b0907020715050f0405040f020c070b030f040f050a150e070806010f050603060102031b0c0f04020717090102070801110301081606020c0409 80
    0x483c0310003081d01c068000b902e60940541c4505c0c02d1040703054802000300c00c10700d5841d4000d50040c000380b00000c1c80041d000c0c2e0052810405103803543d44000e1212075500a55010394080d00c01d410780d0a26900391102c000201200603a0420b101d0362301d444082c1e9945005100d12000b02c0359810b2920300d0544103a0142ca0f03080f480c5403407145070907920070000d01901c0110303510321011980040c41c1000520100080d100078051140190f045107441a10112a00d4000704041c10103004400c8403001c2004c140310319000a988a421140c80d5904034519200420005900d48194464071b8404034a00700c000030050f040b10078070b0081c03200c40350a003000c0c0311403500080e0281c0d0643c84148040221140b84020013054184244024200d00700320b0002c100800b81d01c0b800c45d6000d07600c10040000401c040c40d00f808040c07622004811b07618100400100d251603502d61151015508e444440c103051a840c02c000d5040f82d110500702e80c0700411401842d40c40807898410f410260f4406110701840d0b041941085461a005e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 31651075 1250 31649825 31649833
    0x604080a03060806011e1e0e1302120f010b03010207150b010507240606050403030806010f050c0d20030c0601031103010603151e02030105030c040e010906060602100c030b0105040b0705 81
    0xe41c2d83d9141c50034000780c00008030503505800281c144805568041c0061a44060b840d240c28424101e03012070712070f80d0190180c034014940c0080c00e4103407018810b080d01c83d409030212200c18010b85d0a140ca5070a00e40040d1900c0d42051205009841e05000707413966280c2103c906241662201c00e0640113214000c0c80d0b6040c40024015600400d91060843d00c5114600303190300c444060390340710341c0100c035441d41144040c0481444248003217a40300c4841d0394803031030030300300950030f209a441d0541d081e001e41e401c0218039102d500d8a00221640c4026540d10b51180c5014a062103055004559201e00905080720025800500104049010100740150302103001d8000105240c40b501c0e601c030b400140b0000300c51a5915841d0b1030750141242114081007034102041103003154103000019440702c52011599209036180c0c0ca10b061f400400b980801c6c003a40c1e201408011702a51100c0281d12400602180ea03c080d1404102c4c400b2680240900c04088005031744152610342070444d0007142e40c0001c0c0055410b445 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 31652325 1250 31651075 31651079
    0x3100e0402120a050d020c0108040b010608060a0f1403120c120a030f060311090601020f100908040509130b0c0a050d090f020d030207081204140f01180b030402040b0907020604080a0306 81
    0xc018054018104e00510183c461710019800103450220322004250400c40c40e481040b02103480a040c1031305485c0c00b803518205903264100080c49418960300b144e400804041400150810011040c0202440035010790b030080c07441f100e4518407409541b4030541d81e0380000312940c070101c02081c018401450349050000f44a440c4800c481c046403090b800460342d9056240c2803180c0e40c0341c146c001c1c56009009100034200014802c98007500c520344000c124200715201e00f02042004442000d072805860003425021485c60045485441300a03444015100d81020001180821008100300c60030491b060301c1e114644588113403088020044078a060301e04800c00703100030006030381d0b0460000342d040c003a500070900b050514403154180380c4c58210084001c00300704002c00014209100d0451050f41c111090762414804a0048c0c2d02c22109001c0102d03805003013040810f2200c1c0d078402a5003d80d000741c50401440341c2490600ca0409000c1d01e840000d603000700000380000e81c1355001000064014503000c54415 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 31653575 1250 31652325 31652359
    0x2011206080a030306140d06050c090603090106061e050a140403020306040c09051003020109030b060103020f0c0601031b0e13260d140601080403050a0203040b0c0d030b0603100e0402 80
    0xa04035800a10a07504040c00c1c4000f415410700030701c40586082c41d000e0700544001300c001400603805100041c819912600014120308040059802040780540031076030380d20342090000d008121034010100800d4103200d2802d80c14012510a10102215840b424034040b1003103010b4800600a840c0542441400c21020006031000e0003514041d920030404a0111800d04c1c030442e094903001040250903c0505104001613a030282420044035003021444000e43c54000040b406845100302003c1c03611800242c2161142000034918100e90160b211005040d246985075020745c91180b281c010400c1c05036010a0803003d8440c3c41c0340d11184110300300e590755003100e0038003e00c4400307140c4404076443e07000c1111800c0080d14050344110741c0002d501c4505919200001904100300508060100030b170115612424a00030402c8074040d0902120003600c541035804e0141d0340e2100d0020040001c0c1c01c120417944141420020350740108440c40c1c44800e814100000300d0740541c801441660b010070f16a0814002c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 31654681 1106 31653575 31653581
    0x7090515090d0809030a030815030303011802031008010e0318060403081b0102040306060b04150e030d0309050a08030c03040b011d0a0507170f090114010f03030c020112 74
    0x4050b09060070740c05800303a04612a0144615140c01051640015465200d100241c60030700710000d48409060f100d000a2248035040c000d40c9128015200180d0060340e4050010880181c0f1345036140070036400c7d2840d200c6003000d250000034611a10941c0300072454102c0c182078440924091556413204102d12910550322200f242d00e01046000c0d802c290120b038002c6410060501005803203031007901407548184107503c507609003030282c048c8460041203243c928140c010042c12181907851019005055100b000700c4980c01070049a070000b8922401035402811228903081c1c4900d0681303044281b494044c1c1000d800390041e01c01600c0307108843c0c5126681300c00c000101180d01d4580c2c82080e2410602050f00e031009034500020491100403015400b445940b1060080c4407240622840141d541300a0152841e940503044050020a02800c0720107016841031401e0fa142100100e522011 = true := by decide +kernel

theorem cover : BRFrame.Cov 31474825 31654681 := by
  have h0 := BRFrame.cov_init 31474825
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31474825 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 31474825 ≤ n) (h2 : n < 31654681) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
