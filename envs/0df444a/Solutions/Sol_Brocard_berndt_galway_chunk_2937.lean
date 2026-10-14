-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2937
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:11:05.839621+00:00
-- url     : https://prove2.me/submissions/83b92de8-4a23-442a-a40f-90f38df6cd61

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 528057553 ≤ n < 528237410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 528058803 1250 528057553 528057577
    0x30e0d050709061e050319026c03090307031a010e010b0712051908011502011103042604030804081507020a020d03020c060a02160506070c150c02131a0402 68
    0x40340b4907a880180c40d0200c1d20201d0704004503504240100802114809003400d44502d81500c03440315140041040c0072041ea105000c425080c00452071013030f00da2707048032410780c41742c50540101c0d21205414510f004040000ba4184510b14020040000b00800391004001c000c05509960340c0340c1c1c40648566400340500304c1d280b6014001350b000724540c0e03100115140c0003070501c00d00c2e1010061121152820f05d030a200045030201004100384ea40200e051626400144000c00c10f8a0960031600290f21010b00302174910100c01a140f0044050521200c130000e401100c0644d1b12070b941c0c80c00c040c00360440c1c441c2000d41d0164003007a04e0150003070720009204044a0b4040c01c490440341c1e0801c13200070703600f11042d03085200300714403601d513034640000502c00c01c0d0380b50300100071000c00b0115400387e103011504518014042800080000380241c030450b410365482d1040c1ca0104904072404441d09141c03c207000e548030441c481d941940c03049a5005084075899400da21100014001c1030100340d00c155641a80 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 528060053 1250 528058803 528058813
    0xb0a020d050f130602060f0a0c02070308070c0b0c0f0c030102070b1306110d0f1812200109030c05060f04031b02060903030705071d090703030e0d050709061e0503 71
    0x3500d58410030050520124248007a420035250707090030410440240c00490150340708800307101c0c0c0d0140b4130b08265404111410180704a01d800c1e50000d454140510000709850000b141d04010495070098a030042d0000c0c0394400c0d11b611640e10055036440c00c0010844a80c06001650705c200e0030180201c0d00d00c25000304031040340380c4a08032241c030a100100400d8840580d02e0301c6040c000100c1c90000d054189421801141100030250840122441d0000889889041c00c2402c80050741d241030959100c10103013041c64910307821180041c401c510380c00c0740c04120b51030049880105504412094102c03130040c0c0482e1aa0b680710100407249410a803006004100001445403414000d64006002103102a10542c00c040c003440c0840d00d9030700403010807112500420742c10700a1204014003e0b140480c08001c2000c00c1c2082d1650780e0f00c80f550f50102404002c010201c00c2000c0e206c40c0c0c61503e080d07502000f129002c0c0c0e5554103601c0209214003400440610450213890714075120300440090f510300030003800c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 528061303 1250 528060053 528060073
    0x602061305011407032003100621090b040b330d020406123305041a042f0102030f03071404080307020a1703030a05070e04150503070b0a02 61
    0x145640d92840110349a64a503501c010b201c50b005a0030a0003880c4035200802c9080c0d060986244e182520410000d800030140f04000203200311050620882e1034a0030024001059207188210518040601529040c1850001d000700140c0c490b450740703c4c0d40543c42e1310025490f020b01c056010315010400821000c0c4010b0304403c032505190320107100f5500240a10100005680814166401e503801405031402404491042c480c0c0061303d007602040e48480120340240d0905010040403101c0c56100940b42d803180020304005120405074070b8035090541544040c901445c280101c50904c207592000000300305210a961007c07405441c0103d14160040c50070260600d480701442d0304010110810013002c401911002800640140003609088019641d01c0b81c840c014010040f0490b40b1142c1c80e007944030700001300948003105498200e200c50202040c00e0300c543c4000c90b03a9090500a05500c135162921090706141858407480440302c047e416a01180d941e803d483c0018002c50288c0c6c030160704041601 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 528062553 1250 528061303 528061321
    0x4020703022e1118010c0201080f1e1f0501110709020d060b04080a0303050f06090f09010b060a0e0f09070203190915080118060b09040b130509010b1009060206 70
    0x8542018034048180b44491814105105441d803050640b244500005015034802c200b003603140d1105103003824000210720b03403540001d2408034001c2c048882c4c1b0002e41d001c07805250071161010b0083d00b42c0744000c0710f40d00b80248a04612900c2855140404c0485040011594040d13000c001002c0c3c0c0280c0540b001a2402c01b540c0e01a44c050300085c480d607070341d8042c00714600e4030090207440948200c000070000c001c024a0007400701c0314050050a140fa4004c420005160303180142d25034014000ea0040980361a0301c2005070150642c0b1203640e5202c00c1c0451091100b55104805150a08040350b0500580081100b44500c4000940708440144c0040010240c98082e1080380c070b207500c2c00d40c501802025940d01d14001640086540344002501500040084591034003243d03481c0c04030380004110481ca0580d00503020312a00034640d000d592545c161071081d6507008400f030229805d04e14240140d140143c681c070700900c1e86c0040d0900c901307240c0b0412039490784281c1c1031000341c0d181a0020501505c880c085 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 528063803 1250 528062553 528062593
    0x1a100302130c030912020303010513051501110f0d1112040e150307080a0818040b0a0302040b1503090709110f04050108040f02060c0708100b092a04030b0105040b0402070302 76
    0xb01009164940c40b860b00081c0780c141c8210a01c0030a5400366443c2d504220030032500c0f0b246184042000d40c1081e0600101e030384400d4103202111001d00b444900c140c800ca010b6814400b10175225006809481c030b8500c1801e420400e1801a0072a0209540030802030003400070701c500950203007031318240d010f4000807000701810011030907420000f0105c03000140e44504a038500720000c08210341214000c22011490310110f40d061035406030407142480071420400120b5180b00b210321010384100e44485001e20300e40c0360a8562580300110304030080c0c0e0b0340f500001b0b19982d010300713115550780c1520340307906010850800c0050b511403840e0044980d14161901c001191001e102500039240e0014212801c0016501d0100901400701c01802500609103800307080d0782051071500e0024025810300030151031564401881036803289140e02c085c010b8803034048610701c07000c051480314014014001004000c0c003c442c43d1035812a0000c940030301c0001c00342000d00060703000b00c1c0d00007409130b072203046800786132202303414 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 528065053 1250 528063803 528063821
    0x1d1207080702040b06030c12060d030c03141b010603140601180906060b0a0f030e0d020a030813060e03030a0b0406050f0103181b0f1e050603180a1a10030213 69
    0x103c0880d900004000241c0c503540255480c0c0f60200c40010f040084040c000e407107990101048071341c11060881d0362800390060000007402810055031004960f54410120291101c842aa10740f50603890000310b40e050080008c1e000c2500d951180003051400352400141d0b45060b500c5069041204001010180015100a280c01c96405032a0100850109100f001800f00303070049545401f605035803034001a04075100941062101d404c09840e0042c1d07140c0024520b00307020f078145480282c5030b40d69215210b400c02100401030003a4244101214181000405940a009040760170070401b0b80c01c0040100b00c540b17521529800110f040c5c0d884c5880d6000b0391040038951500c2a0406000400359603480903e2001c3c501009c1a58800c0c4041c41004406d01544019194007980308101c2200c4200c50000b081e15481039138800d2000000040b00d4104103110482c00c0034010342202c0399503085180005c004152601009804403000001078031030318401e40e007002125000b8140e901c2c804180b20b4002e0203008002 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 528066303 1250 528065053 528065059
    0xf1202130e0321060a030302062a131d070c060c12110d0c050f03040605090a0804090b10051e0a0903021e030607170601301d1207080702 60
    0x2840e0900428002440b191155200480c003502030b42c2640030103060f002c0c01050003050303014405d00000e500040c201342c000150010303040101950b0407183c002800e07445000401503901180c4008009290740206c02a81c0090030451000344c01c0326445003900e0011100180021a1a2021350100741150701c40300b40840c007481d0072441040030005a20a60b900840700520549000901540f482c8140c8030300d04641402d8a0031030324bc0149034246d5401c900020b4009000980d0f034101160003002c0401c06002010344c452841c64956036203822003402007109400c10303401440407180504000d4468001c0320090401c0741d414400c010100ea01400f91034001406903000e01111580110259440281d4035940a004402a40e51130158405050505002400000500685101030714904c51020000c0798021820718190b901e20b507110586204d150484942c80076031454849030490403a5043c0c000700302a20410004642c2d6504148c01699101c0c0191107803040c3c413501b8844100011104002003a80c18002 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 528067553 1250 528066303 528066311
    0x22030210050a06080d090501020f0a080304200d0b0604150b03071101020903100605130203040b1303140c0105070f02060705120c1b0601030c05060909070305040f200a0f120213 77
    0x100861340c0351040c070111400c042a01030b030b1704110395a0f04101c640e80345420b40b4042c10340404207039214001400003400051582040c2c1c0401e0707814801554070740e02004801808a1069003907400d2503c808802501c2440c02141895544020014103110080454103010546c0b0714640c0c0703141d000c494201d215080b144d0f40f950200300b0075015950401441d190104d0023140041d050380b0300b104000e80b9403034401c00b810300390b401801000081800d010b102c81d0300089000c0c400040310410303c1c04981902c09905040782d824404100c0310510b400543c0034070b200e170840b81c450101024003501c1c10707669004100c0740f25001440422202400f100c200f038030580c11001c03540389075007000800396090511400d0307200c0705582984000010030900c1590b4000e0402060280ca0070340c0f40c46180e80110b0085030000740410149512400880c00300540f0440398134005401c1070201540c4e40c0c0d07941280309406024801d0520513081b00c000030500c803480308060011239401486070404100c06501703008180080c0102a010306a0f5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 528068803 1250 528067553 528067559
    0x11d01051b1014060301050610110c040501030807060c02060412200106060320090a0308090d1709040f0e1c0c0507121e0203120f040306060b0322030210050a06 70
    0x20000000100311050b00403900052000048081d584020301c528840c0e0306040c2409030a4548851000d61080a40740c88002c55110b5564245041100e00e2000e42181c5400d0001090000140217410901e10a40083c80644038120040b603503444281c40c06002d4158296544003c1c03030051242d2201c42c00010310b00120001114100c50031201c0640c41030700420b8551091005040204006003403104174030094605040d240c0d80401c0c07083d011408000c00c080da000031001102d41d1200364894000d03602514402151552115038006a00452800341c0254103081c3d07c5140c66000e4000c800c00e20345000010314805491609041d03580320095400010702081c0d4446d11301081082c00f10101422000390f890210324418a088080c9000c2160540006100408400010303900841c90185107800341840c00d03110b405004a49200f4810740d400141a5407074400001b03081c003029006107202d071100f4051451840c655841c8407108000095000307005030001c3d02140500c031080d500c03003908071258020014115071 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 528070053 1250 528068803 528068857
    0xd0b0f0303070c05041a031c021207051c030f2d090206030a020a050c03030f0f0a090515040311010e0c0a09060e0f070c020901080307050d020313140409020607140c011d0105 76
    0x340444034004400440645500c00270b40400c102c0a4241d803030980c062400003583c440c65100c280d82100449500164041030711103510030707044001ca40420080c100302e0392000d0100001a0b25034201c01a0003402d4801040b41080010312134962042c1c7c018144d1031644d625082000c0082d4001ca048009200c1c080c810001150410805140f0448200f0101c40c511304000d030000441440040042c681103040074030000000300e020a00d038420740d803071314005505525581f4041d00e40300707610580c2100350f44c80c0424400c812100001c0b42440101300751100c004081e203540d1614107841c510701030740028141ca00d0109808855550286074809903a15103001a000c0c20390008008580aa01c6464982e0020480b80d0501c00709105403104010680001c526006d900b1180d003030a0b848038403d0310222200c40d030721a0354544031a0481950540d0061105944590514020b00760304640e0b10404224800c1c0c0211281650107403203243c20030400401e000c210310010100441e0705078000202800800e0b0900b5900400076 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 528071303 1250 528070053 528070063
    0x1509180f0c0e060d020a380a091d01030209190507120f05010f050f041508010c231c0f06030303050a0c090302180c0408030d0b0f0303070c05041a03 65
    0xa8403074007225000c5880d10114500c07030003028224521807151105082d00590703c80541c0c4080b10181c5488644604510301c4907088090618500b80c0a070a8100d8404101a6800018510420162601d100d0301d03442d00414206821801010b00610900900501c0589800c5a03165440003003860f1a05100307400c100d081082c1c60007a1074400c0441d49201240c0d0030030030903000b82c48000035002c00c108442e41c54003907004030368527961203021300400b6910151320705d544030f03a0810460481c1a60400d8085070795440018000e007440d03107031040054488164803201009143e17040011900c1c000c061406d110304403902a03030840d071a40b568401c00355241080ca00e2903d40740110b20040d0300076140000e0303514240c141e50027a1503070b030710199040025a00052005a503802c4510148005100131b150840d030754450108424400e07504042d2481c400070030081040c4070590000c07002180203030707a08000a600d9000381542d078001c0c0d040c000d04d0786461031401e10003401c09500008441c5184a0080801d2000b030010074105 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 528072553 1250 528071303 528071333
    0x30f050a031706030c061b01090b0601020d0203030106050d0b0a0e09100605060703080f040201020f1606030609050f06150d0f0e060f130b0403020c100507050d03150918 74
    0x1542008032698103050300900030440010111691a10510700100001e860310103005410344141c5021801090100a41040030120340c11003008002e0280542000503410714121903241c014407a810201e4525440441540c1c120f41080d161181030017680c01142c405411340c20002604120b0094000400f1a20483c00398002c11850001d4142d98001103001015249a0382003a402004204082000a580400003a50201c0041807c0540391500e100407801c0010103080380229218141701402091285480380044903800c1d00d0411050b96583c052030305844048034401c01c040001d000049150800718102c2034801c15801d0491f26284480e04079000b2120b40f40540c0328643d540390401c10894401300201b40e0440d2010504403500d00d40300001e5100d0180c10b041c000c11651050010070f00301070080040b55420324000703041046a0241d00c2c001040c0d508140300c01d80351480b030501400b440c280240b107900f00e248910213015406500300b40894010b0000c017265526401c01c8480410086141c003003d4030301c6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 528073803 1250 528072553 528072563
    0x51e010920070b10241b0b0405060a0b011d06030a0f020c030403020f030c22140109021c06030b1303050d0f09020a0f05060d050618070f0f0e03030d0b0a030f 69
    0x1a90820300c40104503404c16800c140c001c8101c81840b03240050441090f0642d50f60340c0d1078066001903a0350040700d120194072900034040240c00080c0000c0000106125110f800180d1041180d804160011118540c4420a6240c0c0d640f0481c5545000c6c1000002107902480403000440c01c030145c168160704985c410707000b245580d00085414000c600d0310b0340c0080c8101c40218018210007482c1d00001720701d0310008038418102c5c0c21840d80498071100341d800c4868100080c110080b020360307441814102079030103519420001c8245801c55454a041d1b40300304000c1c1ca8028411160564a12407410506040300b4401d03414030000340116245c110141c02a1541c0301007000b030220f085100c91040c000200201c0e001105841c2035185c06010742c1e12100c081d2210f5115024001c51582c59140119000100b640da448003440c121000b001070703164010345412940c07501d039030312500c1c40000d2280807078108034414202a415041046207000320b014603008030000103002445440d80503503907500d10103400d44103042262 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 528075053 1250 528073803 528073823
    0x1a010f06020c0405040503030f04020a0f1206050108160608063006011d0a110405091509011211190503060f09061825210501051e01092007 61
    0xc4400d605001c0610307803450569040c0681c1c1800c0d41e41c95180d020080c51140700110040005003555143c5058000038000103141859850b01c4000420305840c3d030ba0001c2d42c0e91030401c400010128000191501c80d02000401c8184260505504448030800502019440100c0080004e11980748840141c00c8051000350842080020140d460074140141d11080300940d0b11464a440004801d0b1103136845841031400141c000c01090f492a400d000700d07040290448513035001c0045400a01d51442c503445000c44240700c850782d0300c0c052000c400030000001895407000e20040d8056050042d620780300c0510204080c0790b81601c0f00d0202c2e01e0101d0498241641d891420b007400781e8030034144031759504071811904842400762030b620700302d03550092406554014854008a00071016400c000e81018010203048400504d2412003080a6041b060505880a500e44004a034041307a0070355151500c8841d03005400c80d140c0c6418401c000512481410940c801684600c0640030011240140402d0b849400882 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 528076303 1250 528075053 528075059
    0x13150213080c01022a03070e0702100b100c150608120d051321021c0906091409180a05010c090608060a0e0a0e0c100e092406071a010f 59
    0x51400402070b20807410354000c40e030b0511203240c60714100d10a0301c03600917090b05014601404a1b1608489511201800d540c1c034040c4030803682e01080d4a410b03080d0309002400001c00020422140002691140c00030850346403460f4005002d25050380c140d54141c0b40000341055952182074208106141c5003010010300207545414444c00b4810150030003200c00c4845128546580c980010072000c18003808008607004004510f54802c210782e482042030342244012031680d04201a00c507008500910300400c0301c1610110b009101d42030f230711a4044c00101a01841e0300c400c684d8110150808011344000d01650400b5800b1034024000c0d285403104903500c0240c41840c0400041140e0360107041c4a10800e50100100407100c1d4040e0b2064100040000000d00401c40e4034030907107058069514107070481404440380e800c05030012000704058400351260041e0342d07184003180c054203919080c620190451320f80e00d021541483c81c0a4440b01e44a000642200d06160650700c0441c9401da00c03509409240880078 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 528077553 1250 528076303 528076319
    0x18170307021809030405041d011d1b060f0a0203270f01030e06040b070c0b10090c0f02211c050103060e03070c0509130f12030b120613150213 62
    0x1c486103140c1d0b8000c0d00d2182481060107840380701e00d00c0340d01d05c00d43d11803078800b0f000c1d07401040105116036060006c103c030f031411308154010180f903c0c0104050b4001d100801c0b9151a000c4452460300360300505440c075200001d0481e070300640046503420304611080c09400d030030311480906d00303484003040303030316900d04000000400919072001034040e8101428501d085030b42100002d09550010b038440d245a5155454400803200700074903200151038916100c0c24440c0603421007503804181c4c0c11580703050065110690b82680e80e1403040c0c4107040164442881e0402c2c4124881806030400c2e032041486140034060108100c1f043c106880080100e9030365401041040040d225070508a000c1c82d02441c240245605c61100c5840d052040600544000002501c4810f03202064108150301c105c0b41c4c0c0703240c60b903030030301c0540010301e04400c40200745005068003091920201d4180c00d0b0003801c0040409a5980080c50501d001c1034104035114000b940c0700029107119070010b0a07180c504a424000c1d00e034601005 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 528078803 1250 528077553 528077569
    0x801030501110f03150f030106090207050d140a18120302010b010f020c01141b01020708040e0603060c0409150315020705060604050103210c0f11130e0d1817030702 72
    0x1110b0600340100301045150307a100c816a68080c408141e074040b00d0103c400403410060110070310642c194179240010840d01459400750601a0040c0122000c02c4981d03802501cec64030400514481e0b00303509001d120003041c4200c1001030b00703030350400c04d04043d117650f01030061250309168070440150b51114091a903950b4040ba02d070a09040e0341c401003904905050010b842088048003030f0342618000120300340d420710743e540c41c0140c8200800003190b4403101d6050160464000f4054070000800710004500c0c5860001603950141070f1582a25107840c1c980a0301d1001400140a5030b081098401c10000120301c000c0ca052820040e014405a070340c040e0351520a0400f1002007155100340d10341001800407603000401420b40342c250410b0302110309480c0d01d09803203d603808c0100500d660541d8800384200190050180b503044429200380215444c920346001c113492100d0540ca596500c0840c0c11051244203030b2b0b41c030100200c5110054002a212510360080790741c46109039a150b84000f5400d0b00f10304090038 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 528080053 1250 528078803 528078821
    0x5030103060f1e0c0201020c0d1e030209061206041b090815040f0609030c060906020703120207020d030806130e06091c2c040e06010509090a1e0305040b0a0801030501 73
    0xd0800000d4035407007003a080d543d0703410342d015181a030f01c00307114102d14000d504669841581d98201c840c80500400010908201d441448100b064a080320808444c024003c2d502c3d90306008060500307100340a5070310800d4800c02006941d2241c4c4032021110000d00c540701c90b030000380c0039a44402d503643c00c0095842c03802c540c400c181155003030000300700300c0071400d00200380c05500d91201000c500d0082a00381141c09500c1e03442c020b028140f9280b88081000049d0380209005440f03901c0b030b2048026000f07241790490040f00740c040e420003034a5000b2000640f040300c0c59580124020719561030741114003000e000712a1590034941c825481201840002882002000f4250041c113050b01195002c1d050000d000c0720040503031455902e481841540012058034440061150242c020400d4007103030303a107040d5564420320815000d00000c2d0f021811080c2c0104450044e550080d080101c0010020441c1e07030340341d840e06010742c01c001c014072010810b400714000900c1560b00c00d079526842541581402821901401 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 528081303 1250 528080053 528080081
    0x902030f06040c02071406180a060e010206160816050415020615090103030906080c04210b0a02032809020402071b050d0b15010c0506070c14010b09040b090703050d0503010306 77
    0x170400700005041e04034400c0c0c1040c801e03039265488030b043d2102c070152003031018002c1d0344c0510401408240640e00c44094400302c07000f6802ca440c603446180040007001120890780740040c0c036120016440c0702484d1580c00c103003040c41c079002c1d240c961303111014103a8803500c118400050700100c05004110f891404040f080a0302162149201d5241d5680a0410611885032105202d40203002a44080601040d54028203a403c1f0f00c41950700800340003401e040000b07034211002801e60003c50000c01c8284240c4e40b080081d01c540300005d880440300b03244604402691401f409403220702200040e25a0b00242000612840940011812195111036007120640005004a84814010010070f4000c407101b070300007541207108100c00c412200102d0305001d0309103010381140b0855040c8030304a0f6020503400c2c041801034001241a11540052600b615480307040f0301c0d48940c40d507011070007107010f440425030030039240303002ca812a070b40e2a5916420403114103441d4002c240003100400c144503103805842034a062354 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 528082553 1250 528081303 528081313
    0xc1e0901050f210106180905060901053d0e04030f0f08061e0d05030a020705060c2d01060906051c0b160c1e050c010801140d020a0902030f06040c02 65
    0x844081400000100d192048801c01e06030f43d019841401e52102d00039150440200883e01340c6030a901001d0702e1810070864052003100001506401b042c0b190310300805409140c4500003111310b4100e48140b038100584160154a8820003070881e00440c1444010041944500b13054942801c001d010540c2002e440401c0c00316050040b004158801c0704e155002c0c1c0e00312490403220080e500c1c08188641004186904541030040404c01c2c0200000600910740d016400c8840d40e544035014040e0354040c034a100241940408009560400c00740d5400d42c40000c1041040040304100702854296000d07540326544c101d9440205002d6810800c94046c9007424460502000c074469a94250640400410b035400031840300030300300c4140d80b00320000140300340c01440e28102c40208420404a20001181c100c88038030400c40c0c0391150394003a0352914102d41d00419083d901c40c00c088203210400c548844103e070310543c2284040340b20800c074400f031405007104125020542c03406c0070a00c02101c5090312030006540c09 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 528083803 1250 528082553 528082579
    0x50105060f190507200a080f07090203060118030309080105010b0c06160509030f01060e0109091509020301021204030804171e070219172503020607050c1e090105 71
    0x1800341102c89110141c4074071502020070503021200b50003420001406050003004003200310b0304c40f03c0c03403120301d82048503d10324280d5240d6610343c2d681b000c004661500e401201c010400000d03694040e6600c10810304184887e40440a000c0c801e0400390f40044000c607882040c2400080300920400d0b0240050003c0e4520b803003c90310071540d8074900101682070440030601d00c8500540310b0010760314030810160480d01c00310300b031103c4035002c0d05660007400243c20b01000001071320f21690081d20b6061790011344282e03e54002d2035004001d040403140c00d0fa015902005030352500c1552140b07141c859802580c500300203050a00d0034070440c50303036000008200c40003030002c808401030320880803001c40311521149503540c0c0c071403000c151841041f100030300184504002c0022412545d0b0508090f090510381600e58600c0035011800000316030b00a1210780049000b024030050030131400070a0307901e01441c103c2d03135620300709000540071255050b400a40851b42e205e1310f032141c0c2030000c50a40900811140b03420000b40d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 528085053 1250 528083803 528083827
    0x1c05060c0a0e0f150c0c1305060d02011b12030b030c04091502090d0b01240c39170f01050c0d231e060103090b012705130605010506 58
    0x1000a401c40d1058039121011071080e40c0c0d80a0501a02e5410311449403245c51000d1015207800c4840f1117140202e1080701d01c40c1c2c20701c03c00e1184034070841e8003c28519403141660011141400c49032403414200710f049002c030002c1820f124501c080041141d902280d0801080d06242c14013104060407030003541030000003800200182d001c42480b0410600058499003040d00050082180d2040548120b006d003001040d40c0302c0c01c040001005c040b1600d0b880c3c0302c03250304500300c9042d41040000782030341c510400e0a10110035103109440c1c0e042c03c580e2482c0c90f110319035040c204a03c0380d1540800c511001344502c0d2040c102047c0100003207440b500000f001582307414040701140388504251b402000703645449900b40400d00882038025030ac041107004146151580900c000c1525800780500c00301d43d41000182d0541c403a014114245610840032040c43c0d10780620003001e89899515910b441900c0d810f05e1400305103900c2001c2c811900050900703a09502410841e0407504d041c2c01480c0600b0301002000d035010707 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 528086303 1250 528085053 528085067
    0x603070903030503060103090807050307110a0b041202040902211c02060a0c0c29220204090507120c0e0c0c0a03120f020307030510091b0503060406051c05060c0a 71
    0x41c1c2c150070195642c1d82c80100482c018900ca4030010308141c0b022a05c2c0742030000000c00b07401601d1241e0014580c00c4045410808d200a05119a4a10b02d20420042c00a48000c0c00100945480944045040002a80004c01001c0700081446000c0008024070079052402c014510803000070f80c0b00e205481024810013500d5402c0240108101910761402d0054140f040c42d010000c15007010240000d80607519004082e88560400030351490350610102d003060f203100311007104000c04801ca003400300c9101d03806d0002904a0000c20b80b5240034244002526407409058002104d10509105c54030608200003040d80803000341030801145000c0c0880000e400300000c13104001d94041c184002c12400c85040a07004e009501c23032141c9014000b00911910a0f016000030b8010600c2007100400d254690700284200d6000a0030480001d003800c001100c1c15009400450304903001a2010658a40381c4021a0904411290745100910f1310402c007024004180880e82d0450002c003001440c00819490090481e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 528087553 1250 528086303 528086309
    0x110907030218040e070503030a0f020c01031e09020f190608150a03080c0f160311030c010909020f040f17070e090c011409030109080c011a150a110105040f020f06030709 74
    0x103640d4500d011130416200300501c00041100504581d552584214010032404180910401500c00c43c2c0301908258001c0c0116040c02d8280c00640066011881200340940301891090b80c00c0602000306107400e0702c035040c01080210070666030303004880c9003040082140000800c2c0a01d2120f82000d044c00656441c0647d000300d03a00074140a80744e070160400d1a003050701c40c1c4c00d040c0862240d4000c1400c0d1510321417411007100e003d8001c003c040c010010a15440e0982d200313405000605030b040c00d12140c94681d000d024401041c450807400d10341c643c0580349040f81660003003040c07103081b80c41c15040036004001c40c0c1b000e4104a0940c3d01c49041090645548418a507803150602480000d0031101c00004420748210350b6000b4001d01c0b605070305040a520700c1c0d00c0b48030705801650801c1c06002c1c10115402c40108622006046000300380300c8158070b00b00982049030300c10100001c80280c2100c100f8240a0740c0e0149024080b5120710b142c651042200302035a204086014040501c1001503003500309000d0340403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 528088803 1250 528087553 528087559
    0x13090206040302010807050f030703090b06061305060307030204030f060510080307050307080918191b020c060d0b030d110705091608100f0b030a0501050a05031015030c03110907030218 81
    0x170b50722014025a05406818a442102e0f0b101004008116a058000c150030600501044405031034907814042c241c42a030061407900c1c041e01000700a1410001d0040d82d201590f4a0010305040e125514049040c043e02415542d80b0b4546051040d620071102d0032500a0000700b000f18a801e02d6035403800d4813809a40c101410481000c1000036003074540031008525501701210150491808504c0205d034103030040a080305692410307214180c017003008207005021220070380007403240000c000c0c108419980136a800c40b9116480d924a2000703a2400c000c0e1200748030282c2c50300f02c02c0600310323140305141404690044c0c0c0304070030850034801d02080c9941240b510198528040703000303545907203841110140035804198401c86400e40000c2200d40c201c040d40c081c00703488078140040e90f692400c0052408150080c550705411000284854112b5944489d001c1c070414a003400080e0350b0303925204c110004a50098078205104030f001c01192900e01c22550f48011070342030440c00c00034450b0306200c004100d903240e43c1c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 528090053 1250 528088803 528088817
    0x1207030b0109030611120a0e1506030a0209062403071106070f12110d0e060a060b03131b090212090106141e0904030e0a0f06020303040b220c051309020604030201 71
    0x6019181d0074101c3d1b030203064a40001b142810107408031001014074110440d80c0c0c0c0604100070040c000310030209400b400b402001085071803903a8082004d15034000d005194413400290300542c640c5070005954001050300f003d9035480346020070300503240408803065501907401420802005d0742d0420051480302600f031901020024582d510b05c8003c22102681004404002c642050902413940021302540f1050040d51748645840c41913109440b40307800781c07a00d52034003480080c261000c410300407040c103401070b0080a45180305102010b0721000700d800c1010f80d9038002900800764030301443c020313401036a07620082158501c0e0030458641d0380112041144990725420062110a031022481c40e0421f00040a0b280d49080916005e08100070b15205503000f000001c800180a8480115050031107402d500618076613640c1d5a111004400c004001c0e200c0810010494405c000c104000c0200c0030340300f40403244441c0e0400c010003520901d000030302842030381025240030050715000c2c01c0d44c00700c0c0d40c20700b08a5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 528091303 1250 528090053 528090071
    0x20d12080a1b0806010c021f120506030616020304090507051e0306030721051002030a060630060816090b03030f1608210a0b0103180b04080c0d051207030b01090306 72
    0xe44030300b9407a00280d4071a800140130003844c00082544032942c0d001d130301d540c0000c400c04110527059900c12522954190800400910340e0380014001c1c134a18605441036901c0c2c180c48410140848205481040000d4000b09402041204081c003c5411610f0352042500350b00d0708130f0010341d45000300d009500450441c1400040044085a0380001c150b902005444100034405c64000017074004584d020306076820410002a103601803044903400c5030082d4440403107944400001850b101d41039404103401a624400003500750010b1180075141c1c03c280b5410f6485901e4000c1040640e1302d507800e80c0c1c0c840c6d04200170420f000340c9440102c9401444204a2030312103142410000b50074020340300c0844820158084054682001c00c09051107003402c0401003001c00c414000440032150021100c2840b9a4400501c1011403003d0244039442440b070a1410b1a050b000080941404112000e140c0405e0000c10129080b241c1e14003030300c5c1d214040d46020490720606c507000800380a8144000341c841681c452880b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 528092553 1250 528091303 528091307
    0x11090d02010e1f0c201c050a081c0c0912061508010903050d0c05070c050f152d0c030708030a020d060b03011508040b0105011209020d12080a1b080601 66
    0xc500c8000540411100c1d481d0354580c040d1020340006000c48200c42c440c81034801090300582840d04000014203410004240900c8095950340740344070640300c5100f290911000641400001c1c0110000c0711036203100c0d0507084404030240e6008400bc00240f0203154801d10802e110400c00980349600164041220412030804e607204099076044203240307500341140d41d0f0525410500604c0501b0034030104100001c0c0703410b0112020302801c80000c000700c2027600100904d15001d02c00400302e40000306100825842c4c40c00300c030b1081d40208001340f6944200d00000c50f00c10901c0d09400401144160068500740c0c03802002c684900c501640145595408400305031580c215070705980c2d01c103a204104103c402c0c0c0380c1c110100503801c00d103c1d0440301c104040040350950b204500da10f0107250301000d51081030b42864015070780703009000e00d41560141d80703071103d401507500c0d2007103101ca42d0b0107100789298426980c80b004080b00c0000b4004035209040c400705464080c0c008001c407106020b1413030890752544801c001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 528093803 1250 528092553 528092569
    0x21e0112061d090105010501120c020f0d0806031902150c0f06090601030b010801180209060616120906050a0503070c080d1a120c180a060b07050604030311090d02010e 73
    0x15a100d4240342010228038285504110704242900700d000c078981d070740e507100c18078240ca00901420703000032500140c601ca0100c09810001501806006403014200b114030003c0c0b03010b0101c441103000607003100c04d02125050038083d0118030340843c0b00c0008141119004910192820300c0302c1c03590031200203030511402900f44038281da82c03084c00c416150070b810311840b030a5443c2028041901c402c070440b40000383c0d4400502c039400703070302a440150314180c1c56283c0070006a098000c25160b0030400402a14500840c08000011418481e071a18001c4040301c10000b400300400c0e400ca0014400308008552620350444256a4000c02c1490306181c10140c0c0d1400704501e0144c28440100c02c0d0500100403098001070364003513451a002e0b50b0580f103001c03e40c4030b459a5040c1c8016843d07001600e402024604003000e5807101d5110301c1e401c0300440d01a0756845160002e9121030020b8a898000700c1c2400b040590600074042c142c41280009400c00e40502d0004a100d1840e20001b8180114840c4200a83d00c407081 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 528095053 1250 528093803 528093827
    0x160e1002061b120108060402030d0f0c0308071202070602040e0108060f01090213030b160e1f14040302031c180b0d0504060b1011070e07091712042709021e01 69
    0x200f1014650b03440032059070300c0c802624220f201c1d0150381d000000091142c0c03100e80c1007202a9852005610003a00d0940d00402c029000c2e404000f600c0b002d5015515050008110580c860000169128034158054501c60010b811684050b00300c00148680003460b88122810740f2084d030401070b504d202d220a00f0616150360381c4000c001c04200c00810900182884402d0402c01c03c9840b0750207421a1a07080084190313a80d1400d000002c0340c50308440a40d8440c0000348080b41140a01d20f103880d882360006403904055848940c0c00716861301c00301090550184140c5240039884401d0320211341011030001c564050024001030300c2d80c2d0fa000080c10f0110380d400c511041100907106c0a4071449400e8001e00f0035408440d1a8150321070160000349442d030042ca4284601c080b42d0307a84281c13a0030111050744e180881c003440308491080705650f06450114100400040186940d10158108202c2e9200605002d001c455900c15241004105c05a112540b100a000c0844034841e5088158000141c41d00d10401c5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 528096303 1250 528095053 528095077
    0x803030415151202130b130e1f09050d08010303020703021315080f01200301120804030503120105010908030c0703030807031104140103050c040815040c0e160e1002061b 74
    0x7074000919071126140701d00c3d505009503a00d14050b9000305104090300c05048425410100d01403140141520503848030012142403001c3c1c2d80c0030b480e8201c0ca07000703154080c1c2842080e1949c07900c00c1c1c02040400c22a919244101e41000c035419891074601035107407492884080c0c01401c0e10030b4401e12184190707001c07801401647c3c503110b251035280c1610035501c51000c2d094182c103603c1c151210104400703140c41d140b034140402058615507030802823403e00c020740759001103602d00c809110110005400f131018120070703180500284c410b1345c54030000400e4104550f1100001d80c10800002000a4000c203044064032740604004072141c580d540201c0007040e802c0000d480f0940d0106001c103c101c20b114030310001003000d03a0140200d480d00b01c50003502d1310461041e0b14442d4414605d880214801008041d4082e01905141c407030169a01a9002e04c2041160004100070520100190082d000340341100170940c292002140600841c0c0080c0d90350401400000c040d0b40d1649862078040801002c44907808508 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 528097553 1250 528096303 528096341
    0xc090904030c0302061b0403060b03070305120d0c0e0315100f030305070501060f12240207060e0f0706050a030f0b0613031103030a080c03070c02090c0c12040803030415 74
    0x241c10014034035441010218018081e0740041004076039051076105070303040340c1e424281c80c1500e160389490042c010b09441076054000e441c0c000001c100288025020340030340420b615070703a111441c50308040f250145844010301a42e2603c040a6403400108404ca00350032545188450311050580304d058403990740041010b400b04035022080603802400340500da482540203100d84c076150310421482c0541d502844400a20300c0d40c030700021900e6102600384200c0c0c40300d0702051005100ca440c00030390f401003600307072000c03500c90311101c42071401000460081548400504181c85c00c000e4000c202d44110490001055113401c00048907280c81da00405510b04010100303541c45004085800b405801b40c4019160585e130111350030f4240c14044211280310310076548008595a840400c08650303080a011b5208100000c490640182c40350030199020303101c85284240c590046500d200d190007080100800e107803405210170401c80c480003003900d4201d503002c0e6a10082510000215000f0884100a9582e10000c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 528098803 1250 528097553 528097561
    0x302060a0504091a032a06070b010806160e0f03070f0e060108010f0308030601052b051603020c2e050a02040f0501020c090435091f050307080c0909 65
    0x20050003210035070942808442c0e03944c1c02c451040d00e400060980c154024103064000b424074555038625034840c0c0740d03602c004101c160000c200c10f500309000031942c50700584014400ca080801c01c043d8084240203a0419002407494002c014084541440d4000c1c0c0001c0103600c060b0f90140040c80c040c00300040703045c0003696546000c418442050300c0160119420740e0001c02c40802c041076003400d032500480382510303684448004650071b034003a1040e000e80c2c0303038030300c2450480000c0c10b204000103040c1d070b440c08141030810070042000101c0b01d000203024140304000444c1c4400d40410228081081d41d40025100c00e02d04900d4042240d401840d414501d14100c104103240e1035a5020304291078810940d0b01d11907490344016644c3d1802402c42d690700030400c10024001030110b9640143d14020b4014100c02c2e2510040d2070645c41e4a00d80050850000102c0d100c4900d0400400c81109001c0d0b41c00e4594201c3d4041c0000740640c0301c0074040301e081010a07000a4010b95000c422103d403002c0140c2185003c2c07070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 528100053 1250 528098803 528098807
    0x120203090a17030f060109031703060d0f0b10060e03070311010203160c06020c09010305100b1306121a0709140f0a030317010b09030d0c0203100504030c1104091e06060302060a 77
    0x20080781d100150030b04c900003141d0079522951501069039402a2480322844480445036a03640000300701c80c3d840b03001d403010b41d00026007010b281030100c2d2043c0f81071062824901d42d1413032400101e030421020010310014100c415a4006021002ca9802042610400101c2d0300100c1c1103106000040520041060300001008882050001160701c282d0958040315920380811082e10000c0c032018100f6071100d80d0b4414189201d03802054a00d2000b450858101d0003810581c05540340c2da0310054403000c1c003004a506000d8584480ca0041300e0004200169180c180e5001d0504d401078041c603100d852141010038140c0e2038560302c0c0c02c10070800a2004ca9229500d01d802009821040440311886491500008003540c00d0b0054030041389005014002c400380c078020440d030703e12000c0130070313a41445010240040084c1c81d00c5107500541c02130b640c5407240d811a0610a221040c02c00020740554a032003200d10100c0c4440b09115403400c0425120840c414560a200d00600362540001c2d60141c0d0000e50007040503 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 528101303 1250 528100053 528100057
    0x204110c0d0212030f070915020d020c0402131e030209010e1e010333050a06080d0e090103030804020607062408070506070228090b0a05060a120203090a17 68
    0x102294040310030302038101c8012a11204150079041c4404000d00120b0400320030200440c3c2d01800c01e19081c407180c1c1e41c1d00c0007019070144420050b03000d600500036402926906005141052070151000c0d03160894800d000021401c240c411755280d101c202440c055128540d405820095400424a03c159611907044a2809e0020358603026000c0000301610380031810321031002d040341d070060300c44c2244810300c2c2c40c20b41741220450030451052550801c00000c0c070400d44107443c0103045101c40022001e040c501c01038603116425140c641071004a0a031148995140b020003030560703a151502031826112440410454011040018015400c1c0902504941407524242d4181a000b803d011211a40c1e86089601d0382d0380f5004890f00007808010103c09420000e50190000c1c3c00103185266881215032078541d040060382001d042103842d100c0c2d2000600d45480c081e0007900e000c59050f850507944050181500f020082010b10303454010000580c0c00c1002d12005402039004081011a80c2c919071200e441c2c1c3e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 528102553 1250 528101303 528101317
    0x313050304080105191e021602030106080a03020c0a0e011514072004090807140a0b010f0315060602030a12021e0d0f061d1302060703110d02031603030504050a020411 73
    0x8074100700c4001040701040d004400b007000c140107004042d9042d1ba14410041d5110a0064007080c60081403140180c90034031030030340140f03003680103080e0000c03161400074200b103a8502002d11465104a00f484021000440d441c1140c647c89504d00d2440c28103d405d4507000504090350000c0c0d000819000140b080381040c00700c1d10411030400d19681880e2070200000c94480d044050150001880b200000070040032440c0214550701044a00d41c3c4442c0c0c0d40c5181c80c10098105c80003401300c0103810030070046000c4500746101046041403018600b0301000a60300e010750540701e8100650762112214080159046804078400b03a48a510012540300d0341c040c2c5039110300c1d030a06595180401d49050203145108041c140c44026034016140040c98440350340b0b440c00a805e403140003414000c06030040e0740b42070040c403141c0c1c8280c4401030104528480705082c441e01500020035904100b0450344050003000d1103034039007a81418002520f40325810301c03914110348a140207400c82c0c0fa1010324103800c010315000d410b130 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 528103803 1250 528102553 528102571
    0xe160f12091b050126060f1002070e07081303120f060b040302030708010c090611030d0513021804021f1101090f021f0e040203060409021008070318170313050304080105 74
    0xc2c0b980e03480c01103030b0648a00d8100c20342060b407545424038200403c4075140d040703440180307560340b05017907032001900308070030b0b0710782600540d011150406c400c0141541c0e03a54042503d04111091b4900b010114418005490005080040c4652902d81491240d80181e0fa800e031514010062607440f203001c030303401c2c3c1d02500050703109200303900c0001000d14050146842e1014140d07030342202d1a15048081d00e00020745e0307000c001140418804400c0e481c0c4207114261282c00140500401c0c0081030051040070309403203810340102d6000004100140e00c86008550440350a80c0390f2340c85140000808540d41e10036000c10a04a500b4190307040c050000d0800c00c0700d03600e4000c82d0480d1155a90032002c01800d443c5044042c007054450b01110b249141541c0515842007010b4000f050841d030650004103660f100203980000316610700c0030300000a0703040c40303881e4a031006011a00d28080042d00e07072a40110111a0074064584000000740003003900d048130584803503001d812281c03960b40b078446445c080c2c01c048a040c80 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 528105053 1250 528103803 528103853
    0x2809050d39050f04110f0f040b0703020c0906060c0a11030114162007150c060213030b01050d030e060304020307050d200108060d03081b12010306060e160f1209 70
    0x181c0c500d014441d85d10407562185d001494007a902003010b13440e03005100e209010800600c40080c402c600c610050540238403950281401404100070000e000070007400c3d50303000303c10601605600010008214000341d030444070075408800100d0000780034080d039030070308092582110140000800102c01e036601e1215070740c035078142d6150b00c0e0086400007502e0600c0021154040072080100c4c105401180907520300c2031038002d2001e6042e8881405903800224000b00da1080b0480c10018000c60700d1030640980402ca8180c4420501520014040d481c035610140c0319910000214046640802c09400104005402507428038158101059542d001c8012140140d03120907100e0020f6203c0c0400340c0c4901001040424104400d48084a003d0401880c07203861412000150300b42445c04806040c0604200038592615070441c40e20800f5561143d21400f0100c10034800c0c0000f141d4901d010703d990070b48610340080b041d50b41c44400c48510901c01164410180340c034409800384483c075400d203040f0b1003802480b85 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 528106303 1250 528105053 528105079
    0x210106030602091e0d032d080402030c060c030904110403050f0f0d09060f030504050c04151e0303140d02070b0a14090703080a0f0c05032809050d3905 66
    0x4114180505139003540408034142070301c0007901441010743c42041c4422001d48041034070f902c41100001c1c040d10400440c0d0760754100400c518040201e003020641c103036009814030090280640d40c81c082c1005040c883da0300c071940c800544116a00b0754005580182c2215800c82e00d02d07130b481e5290080e003a401300c4140104007a00516500508a04013200e6503540d850f504480c068100b10000d19018204031214010503201400d991344034094006c544031640c1d800d402c440c0c54000303800130001c08031320408000f00700005c0030800f1a0b04400c80e0340360410003076203d543c0e9071900349141000703200e03203000144409800007c0c0499154613510002d42c0c40c0f07003c1c041c0e0120340c035601602030f518440f5210003885100104100c0c5909441194030b19045016420001846212035030754074150f401c2540200c402184100c90010f01d00d64026501842d2141d90034040d4180341071002103040c0412102000d8010340d0350210070840e82c0c948600c1d00002401c41800c41c024030307001000c2102c500c4014804c03984100407a013108 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 528107553 1250 528106303 528106339
    0x9060801140d02060c0a200102280303110d0903080f0901020c0a2009040f0512070c051c14010507020d02010c1706012606040510031121010603060209 66
    0x40700034014014003200d41d242c141c1e401c001084c0c0c0711010a0189009017012100010b040c2000441501d003504251103d1000100009140066892080d00ca10300b204c000c400a1006501601c4800340d0145804941921f001065032500e201d400c4031031922524040f241414541e0248130315005400d0131a1986503a115090003500341e0113612500320b03030340d000220000001030540301e0082c00b000d0240c4080040d001e82c0c0e000600403010441d41595107464045904040080c11700c812881602150710040c242681394a607030390310340c00600030240034210310103d01d020b4651540007500d10300c0e84181c55007061040c1844460103032a00b90b402c5001342c85401007540c44540180144c400e507001c0743e82e43c4a900d04280d10303981c100f0300010300313000c0c1409458040c803140506201e02c02c1e4646d150030b03521100941001c20500088600003040c1a21004000c8020f000080310550300f211001401c0314112000b01c000603051b80391115101508642e986804c01c00010820150094000000111100240f40101070a9 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 528108803 1250 528107553 528107579
    0xb04090b0a0815060a091a0f010207080a0803071205011701060b03360a0309060f0e090a0b030f010f0e07051e060f0d0204060903050c0a0f18180309060801 68
    0x54607005410081c1c690000710140140e0907030113a402004070805503601d0780300400710b4020f595070180556503060140b100e07060082d442d20a0032028401400140d251204e120344806049500526280000001c14001072103200045001105904204070b01d50b900d00448800380d102c3c00c0000107550a08000140140e00b81003a02d10501d881903280c010305040d00304904070030000c07801d80f0f800010b000d41026403003141000386110480c03003912010070407810700c02c0103020181c8111000080040211300001c950f15520000c541100e0b007a2400f1030401e0281e400039003042008000321800e90310b409508032100760a604240500041c80042d5500d140d150000d00c0010950081c10030381440032440c10340c0045c104040105552108450035170b04080308901d40320166800350303200c04001120400c0c180107002080c00405203011040314030341c00142c5030401c0c1e074030011040d2191006200920900c0d03604110290400152400034a01e00c0c081003413145400307000c80416008407130002c0c00050000c42c040c040300b10 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 528110053 1250 528108803 528108809
    0x2003010e15090604180510021b07120209040317040302160e0606190c0c0e01030201030e0309031c090f0e10060c030215060d06020d05070e06040e010312180b04090b0a 73
    0x41071850b42d6078400d020103062000c56031840300030815001d5005c1b810a204081d800001d501015a40d1907644898800f04c000a9040c0314254000190130004050207112030600c480d03040e00d01903056a1a401e06440c80c5c0700100c0c0052403090340e48208270030558042038041610300481c00c480110382e11369901081e0314400303e036110f810207420003821030341085100c84007642004901c1c01c45040045507603800d0600700540d100402040900300180704660305402100300c1c00000d8001942050300400000c0c0d6200420317194800529807040084100510a22180014015082c8860f54280e42c035031007050000780441f0590001ca003c03000103d06603100740d101e1160503826600030002030b2040782a4514180e0003900f10341e1b0016a0180c1030001480500140c4070f28400c4602c00552071801b03500203050864800c0034540b02c2c100405c401e0041d440820810f5041d6500000310b01c00d54215110180c0310601c074082c0b07400d0091110440056940883c070f00400985900e4002480086054028030081e030302c840c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 528111303 1250 528110053 528110059
    0x20f0303030a0b014116030e01080105040902061801090803130f12030203030a0b0604050a030521130b07020402090904120f0309080a0e01170109150812070b0a2003010e15 75
    0x1e1602d6240c1c55104490f121126540c805d910f0040c0343e5250401084940385c00b10041201c0400e04060fa40e040317510035004180c15601071002c2c1600d41d0002d201c6200d8ae92242800ea649512003402591203a010b10340540941d1084079914420b40c104801c4a12052007102e014031541c0c0804100380b001e41204502c202c0e0700d500114290307161004220b024110420003039810107018840091360346d0310102601d009501030f44c003425000c070700b004803070740d2604914440c00e010040820406519502c4001c68804072074050307a54640711b0156200107000f03481011102076200e04c44106100600480340c6620400c0103440d102d66a2841e06080c0070303000d8400620004c0c081c003906201c0000b40501035940a0410f40051512040502c0c010748458170040087c1c100009850341c0ea030a21811015540940b80600004001811620a1440039003000e00c11241d0003004840b0345030104400310025002150201c104d40c503403514111002c2e8641301603030001d11815460f5a40007020600200c80d028220072014006 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 528112553 1250 528111303 528111377
    0x90b15040e0a033606030c030c08251b06050924150112050403021c110304060c0c030c080606181026030f090301060509130f020f0303030a0b01 63
    0x1400d400c00e668041d007400d01461380f0407081c48000e111003c030145003c1d2000f61000180e0411400c4e0040071a0070180b83e11080c4080e42d002d0201040702044550b0350760554040020030f10030081003ca5480c25605000e070002c1c400d071443c0360b0800c01250441481401402c04403000c48003008034030340d6080d01d203800106a18480601040032101c03980310070490a001810840c04d40104195410125174040300c0a0380103800100c90b14030607022002261042450398500b5000d240f070184031980d100d2045100303400900c07007190842030030441b80210000066030003002c0c0c49c45403981c174442c407512800c0881c0e551303104982c80e8480180d80f80c42500c05500440318903150072466400d0013281e41c1c011610004c4403859948a00104e2002c0d1030402c000d0102d900c1880c0720680300e83c8840700341403e49217203030401e0780b24001c0c803010412484a50503c2d005501c2d00501003000c0c0012500210310f500203000f00e03c2ccd0f018000041041190102070300300819218003030303885001114011100480144500c0000300e429402 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 528113803 1250 528112553 528112577
    0x620072009010e01210f0b011e270e0a0302010e0d0504080c010f11250602070602060f06060d0207051605031b1203160f0506090c01050a12090b15040e0a03 68
    0x6076001c0d500e17030944a03852408101c8a4a0b100d1112820000c00c03103804e601903005018103200c04030910a0104048841c074110703410b1694021191b0050700c00c0b103410105004c071001c00c0c1511a0004a10720b0210f40603101c11201500b0020701800b502c2e064185284101c59601020603c210121001c907011100600302601c4050011640030070b500b00880e04110720b0110142292100303101d401000031800c4c00d20358105540c045174450030034040c0d001d038040d5000b040d02002100e4010400581c040d41000403011984e1314603000032047d00410880049140c0f01042c09401c000d400254841c0001d81c1282450301242d80c0c13030425540c0d1103079044c01112001d00189014450038050202d0f085101e02e00300b620308101000a00c241819400b0303100fa18980040c0a40500b80001404941c0d045105a005850b1340603110001030514401d286212003045812040055040650307032040d10403982c441c84c00303086030400d164000c04181d40581094400e80c0b138290a8100d0b6140000c3c00c42c801c0d03505480c0c2841f2080 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 528115053 1250 528113803 528113819
    0x311091c03020709020f07050106080307112404060306050405100f050d060609020d0c1e081303120509030d0f09260d1107030f1701030620072009010e01 67
    0x2103098800c0307066204489001c9003000240c0080c1002144400d1070039280c1c0e8290a000d400c0d2101c41d80441da42d600b08101880110b032060341844041c0c1c205841e50101304512181d07070310703491809002d19040c011020401041c001c0d4140c200034122041160184200e48a002910418040c10300c9407e501c40203400c5c003008141400501042964000c0400154103655840e0750010382c0c1c454410741350710703a55607148009400e401071451146500c00c02241e8007808403107a0b0103404050080c1500101060001d030100400d403207140c500c00748261602060002d81090f481a547d05d8010410140b03101b4200303156801c1ca40514411021400c0c2c1054402c0101b031694510090f808524100116000c8420880300a4140060059440210030308084c0c036620421410b00410082c41c41900714100101c02c031154030852402a840c034156038010744000350007842c03000d100743c150f10a428581c8851201041c14804c0c440c06011340c030303119610304c80c1550a844420040062101090080b07030f40d0f201c0f003e4010322440c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 528116303 1250 528115053 528115099
    0xf0c1b1302071a2203080f15010c12050705010e0a1703010806150d051903022415010203070b0702030909060901230a0f0807091401120809010e061215100c0b09160b0a031109 76
    0xa103040cc0b600c1d019058640d18203440b0380d1079501005600c0a111082007101c415641282c00c44214519030865040c01c840c0794942002805000c18a240e105d491521592130300940c40d401c613800720031900c500140341030000c0c000d11400810390260040c01c0803803004400c00d4810000d12148601030581a40d01c00c928070841c0341400800e10304500c03040c0406400039103400301d024082c011617001940c42d0202002006000300c80248681c1c081d50a0030010450b40c1c0303440c218103c21407050307001d000c98652902e011a0b04030301c03154810003401d0b10b055400900c000c408507240040d1079130710b2014044684a0010421840800c0c030070b17100402d003181c0f003910104900c0805020042c205241a180741480b150004510381c05c0000c0010302d02031300700103004265421760b01d00841445c00384da520042c200d682902030000000f210028148805000c001071046905000c202139850620014140032034a58001ca2031641020811401017480d10b00c2480d56801c2e00001e464082c00300400c0004501c2c0311104442d042 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 528117553 1250 528116303 528116333
    0x81606030c0e1203070b01270b0a090902040905011e0f090302120729010602011b020316020a090606031b230f0c1b1302071a2203080f15010c 62
    0x1030006103e60000181d840e45014000c08525032203101e022101040140708c120300c0d000701d6100914000441d0015240c200020048802061000490042900100380070f0070f402e9600800317551901d124100f5038030780c09551402000c07225a0030807584030f1134007910045074403030f02002c1c01607400008540c0007500c40c0c000071309001c1d100700d040c8440d050402a9220a074203048925001c40b8403031100520400b5424032a00e0b2440003031603140d0144c40c1c1240400fa480340300e60104101c0c1540c04a020500395210b980f0300300014052118104503036556190010014009900c026284002c03142100c50b845219070103c02a89605c148901e035407200c00391240c49268010b40184060340c805104600110344140880341c03a205041030550b0325030004078100000c55540150841c074843c2f0520255010442100044141c8006880e0030050358030380105418034030101c034000518110b0420340781c01c101540702844901906181170382c54280d8555400701110124070107225030000384480c8040002c110200c03000d082c0703 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 528118803 1250 528117553 528117589
    0x70b0906030a0c0c120338090603160e070e061309050411030d0e0a09020f070611040305120403020f01080f061e12030417030c1905031201081606030c0e 67
    0x41103050b540b506100ba010503035050109644071410b100241000c07400315860412428048203c0687c6020b050307002d421015070074080c02d0344100040e001c1d1420002c102480184200c124286a602e0a01c52061003003103540d100010304a004c10b40b2141000002d44400f000ca031184040d01c2c5040c50790f544000c0000901c18bc0f0500307000500301c501c6850a01c210400030115039525008440320300d00384288401541d1040140510400107040001000070076140041c1c0c1c84400400c00d801d8140c103030201c6005640018005020300880d55043d03003090300043c0100c80c825900081c00c60710083c015141c2413012500c203400500e0384000030355240380010001071405040a00820528160301c00316010214140000a66a1000800b489045d15600c2d000c0d0251040000031458100003e0300e841e00e482c62a0101300000003808450010018240b055a08640d10480715a02c80d40e55810450340d103680c25500800b400c9640c010110703081d8171a0142c91407580740d540b10355030350780a48418808610a03400c000c1c45 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 528120053 1250 528118803 528118817
    0xa06080a0906090b070c03020c06210615030907090b01050717161203020c100b0a06080415020a0306060f0311031803040b03040606050a0b03010e0406020c010b130608070b0906030a0c 80
    0x2030f09409031140204003031b0392004511074181c600a0300c6d04085208440c8a0a01070041d500000d010840c1d00902c81c05000d80d84445403500c1001c9080104025800e0072220b40120800414290024415040b01e00d002014003900411b4001950a803051080140c000380c0b004400c0d401c2c560591009010320094071540d08125481c0f1b407140d084622414602000203074000985510000b4200910350340b10300380c03840c00c002440840b40060030002c4140304031030a100c45480045e040c860380410542c4440c3da5001b040d5901c105e04040140202900c8c003603000800c0c0c83c00e2080811f1031180c898400c40c3d900c04a1400c1c95916100c958000f01a0107903100d0f480d500c02000003048803e100c4c00914015841030801080b4103050100700070340c0d800c0359000030081010500041120f1410b0001060300700e034009500582d40c0c154482818090500c07003064a420804440006042e580903500440c1140c5649d021b4030034450710394680381c52500c14030071200c0c2c0c001000d00204903104400e0340900c5014109040a80b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 528121303 1250 528120053 528120071
    0x15030b06210105010e0406050f0132070201092411030418021305090411040f0902060c0f01050a02070503190e0d06020a020606090c1206012705040b0a06080a0906 71
    0x10301c101c0121404070500700d11100c010402540c00c840700703d2024204803024465642000c0c00f181803604100d0391a0704000685980e1881d03c12488602c1a1415100c41c041068020102e0621040d40c800d00d4100e0028510316800110342a0355140440d248000d00030f07403007184c0b800101c00c50341140c2900c0c00c60381c180420000010005840c03424000410b070880c2015890b0f901c4001606001e0031568441401040303e801007000081001d00d415125450803100040d0000c411210480108880d540081d000b440000341d440001b07000051030344c00030604800901140d5540d1049400742d0042d03071001065640113000141103800e120040c81300440c003920300389000707c200900083d8407040891040d14016070000d10220600d0341400310903440641a1482c0ba000d0a01c101c0d060124421045c030840e800e046940801c800b80c1c42940400b502c0880580c0003440400513010070b03403816a4610607144510314004071041c980c181340c1c0760744048500c0e80e21404101d5943e00035010241000500803a200b554400000d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 528122553 1250 528121303 528121327
    0x1050306040311070b120a1b050409050a0216031205010501091409040809030106120b060108070804062a020c0f031524030102070602030a0c031505010c030e130504051615030b06 78
    0x7414040b80b0580c1c01c403005090800c4240210341c03008003401c1a44146a2540c8c00060b001000c803030840d20703007000c002501e50713540c0c414500074040d40d1607120180c0c0180d065070050561000b524101c10071455810846039030317110010349000007684100360f030780c0d8100d101e03046044c5020589558400e0060405500c1d0100c00c0e00007900f1505140c0003089140f65400076403050080d10102c07142d10180130708001c0003e0600b442c0240040728002c5c401401075846022a40f604008060b6010ba99040c900130074030006a581c1001e5155064a035000340101103035809907515103400641107068200c181100c0080303440340104107602a030f01c0c643c441012450070001d00e40d2504d00348018103806000b402c4c01601c030305114070104150b0707020f01c01c0002050300741501d0320b000520200c5071404480342420811100d040b146410f440702450956010b03482500024818407004031904228485c0744a030f81500c64400c0d4041c01100c03254201d015415641c603904074405407850180c3d01440c030b014002000075007072043ca6050 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 528123803 1250 528122553 528122557
    0x14070e06071e12020f010b03030d0216020d11040b0102010204050d0204021b0304030606030c0b07030906030c120203010e01030b22030e01050904020a09080607030b03120d0905070b1e0301050306040311070b 90
    0x402c0300e400103020010f0601560520002c2040b1044c00c0083c002d0412080000e5502e008510341102e29603800507500000c0d8403407074003e9071496406040a000c680e80f41c101311b104038843c10403250041d424450f00700003c0d80b06200b102c040d00d00c010004403490b0050b400340002504030000d811654200d2134148854504200082c0c4001d5129010200c0c0040c2503103840c502085030340d88008040082406080006508443c085e41621103c0c40c00142405049004840b546070300101d100c5d096100000100d00e5450303000741d2a06032402545200f58584800158080042c0701071031213070320002030080074400607105018903900c0c0801450174600b041c0b19400000c08a0740301008020110718441002c0010040620410f5400b103000d0a0801243c1c818a0110307468907102e902d01003440000085103405510607911030030f000c0c0c1e040012540c0d0180c07184c6030083c41d680681503000e81c3c0e03c03407544548254a09402100e050301d4010b00988002c0d1682c0d40c0554001c1c0384008000c00c01d0181050100d4400c2030140 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 528125053 1250 528123803 528123863
    0x90a0c0308091c03080711120d020d0b010906120b010201020403060c110606090c2208120310050d08041202180a150b030108030a050a02070315020d14070e0607 70
    0x10480b40c1c0c41e8184800c20668820038811000c4005907144000082034100681c90b0748002c0742c1c02c140c55200c0c441c3c40303050b040400c0540d0040f000480461401070804442d0302401249500700303c10001c0d00e510740015140240507200705030019813424404c00c80320240e5002907144000600016040645940d074400c20740740d0740005800000c0030711030107100c00c110802101d50021400d54416a0f01d083c403a01150b00e52080b02c40401304612904254403407800c050795090000c003030000a407001303030885140280d51944280c0301142c1219040c0000b04907890300100400010340c0c030481080c5041d2411051301c0c00d4862007038007660310203804100300c10301d8508422404c0c400c2d00c0481c8006000460340c0700d84181c08501da00510070715402403006000201d400800c491042d10b1500b005500c41404110032803078240b440d00001c10060942410800c2070728540c0240412291080e000c1c0404424408407000b1404102c1e01e150003e0a01c0e0018451420200c0042c1192401503100102d00ba81c80200300709441c1c0069 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 528126303 1250 528125053 528125063
    0x10507051804050609130309081014011a0703080c0d0f15080c0307030311030d0903020c01030c020a050a02040c0c0f0c0515031308091f090303020708010e0312090a0c03 74
    0x50700c41d07248030401004501e115030403141080541800030100b03609050050030a040d401d0090040320606001c2d00322a00180030000845403440c0c00790058070007810b400004c40700c5942104001041004281d0900d118480b410280b007800c3c0400390f1000c0312509405000c08034181d50410a995000d03c403409140b5142c8512000801c03890301a0505103200c40c81c60348454420307044120500341d2030b503000c01c4a0341100d81500d0081d01031b10030b402c20790f4191700c29015180c024501e400108810142c000c22055082042600c041040002d25407007a607c407100c141c4001c0190704402e0090006103040d81c802000c40d0901e14004050009640e2241703550380d40c0803001e4074501a9094100640c0c50450301a24450814440d014114240340080c4030160041240061491001246801481d02d4001a07612007400304410700544004649025141d95082d000c00c0d001401052030114621105002e03070b07449030884000852030048041c250908551000d0b01044003401480c0604010035003031a5004080d602034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 528127553 1250 528126303 528126307
    0xf060f0a060b07050c030d0906080105040507030b0d030e0a0f0513200c030c0c0a0e07111002071a061e0d020a0905070f03060f03031733010914101b0501050705 70
    0x16004042c503104000d044d1f00e040010050040c0302050b4001600c40c1118410f89000c60340d0344038000103401070f12808280c0d50308104013089120902d0b6008000800681080e40d17091041c07500c40c1171001c5031008a0081640000d4040008010b0403076913030100c02c95180010440841d11481c51942c05103074004030340c158044e030002c20714101c09541402201c0014074112081c6160514054460b00110301c001c1180c03050111045d254900703008140f050340400113000104542e2050f00f880d00d2204c1181c010120140c01c01c12400044c99801c24281c00904500760b6500002c02c080e0b00c40401460b03c1c01e40034100c1e004000c88a000071a0002c40c0181801556142c688805040711928020200d4503684e105018418004404201082d04103000f83c0f0a00d19059450809564100007000c4000300044010744101c5410301440b0ba080c0100b0908420300d109076520091365603107011030300c400c05a00055551069228003105a40c6004e42c00c51101401c104400c2c0c442881603440f001c0c2110000c54445001c1400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 528128803 1250 528127553 528127573
    0xf0f05030a02031c05042d02090a06060224180307020a0b03092a01030c03090b0c040602100605211e28030c080c0109080f090108090f060f0a060b0705 66
    0x6103010031600001380902001641340c42d4481c081d9032172040e013a111401c0385016201401191140340c8154658002e041c1c2405030400d440110014801e034420200113004c1d0001b180141000c5800c0130700406a1b002419205899130040035a94020315400d080c094442082070b407005032200c4622100038240c00c1c05a50700d902d0181d00190425590810710070409140600c800c6409041c1065030500e02c00038070780080c040e08087d00540007802e00c0390015201c40c4584041010340c02404009000ba07907103e038241c80402c0b4000300c1100c240c560900605502c20341103101b80301100b03180d98540e041140c1d424103d40c142141849011300a01c103440c404281901b2018030980e4443e4003402d0914241d0300c2d07002c0d599010f1070648000380180301b03000004040b01c00010f40d0341d130340318425085241860b4006402d00e40e6003a0000c060341c40c6a220303400c4680803440c8080011460000840c5d002820343c940c1d0050b000e15902c4c0c4041c52a09200101032482e00c1c1d030b45600104020031540c01612100d84104005d0640c080 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 528130053 1250 528128803 528128827
    0x160803070e03030c0706051e0c1f060f1a07080301060206040c15080a050c0405030706080105090609011d061f17090f0a201c0611070f0f0f05030a0203 66
    0x800c40c4507160003580100301941c00c01c1c03400140710040f14154a0400c3c0ca030101d29210060208440012000108003c1101c02d80500d02003480420b040f8a2194035500095858850b026140706100384181103240380b100f081441e007103032000e2144444000440f46806030302c0c2d481600c1504280c01030801644880208820072180a203004090510100651002040f90384014012000280b03001191500c941c04103a081b0250b5041e240034000040c00c0c1e91140b40c40b60360050240c0030911515110356182c230041070160501120782c0d41a131765400700d50b00510038840000084000003405c159045405203500c261040c10ba1034448c802c0300174541c0c44548050800d89001d149003c0035008200a03004548151002d8100041c0200d2941d03012801c0c0340144c050300c900ea0291507010854a400c41d4505514070030400c50b00002c0401e041c888c81d03041066290401c141d0b00c041c05000c50040c59004103590400125004024005110744140c0c80181803402c03d99600341160428540b403405a0b00104440001034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 528131303 1250 528130053 528130067
    0x1503120908030f1623010b04060b0405030303010b180402030403030f1d07050114040918150513080906090406090203070306050111120703090911070b09010b011d010516080307 77
    0xa28100079414102d181c4800c200d0f520440c0b0120b1041491004414100520010306860300010030010b03056070502d11040c14040c208000302c40348201d1034038602084154034103003a1415250064020f500f56802c0032001c103281c2c0d1100304034144407100c080d02c0b18055910360001f580301e14425980444e21541e4440c00b0420380e403d1410070150303006140340b00100404002a103404032502407902c10038006000c4140080c81c0300ba90810210075090028481140303001403100b0900520801ea41d0340440d4901c0542021105c0503500000b400148035488008519403501030243c03814020861860107085400040c121903a644c40b40088036004410030404941622030040200030a003484080301404400080c4c4075540854690000c0401180e151300381031042e01608054101da82c020410100503024110045d00810300031104081144005000200180070780340b44074070181c41c2c0d88203a40c1049a000c0300340302e80000301410040f090008001c0b40e0380b07020086d10501e0042e04001d980303082c10100107004c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 528132553 1250 528131303 528131309
    0x30c031707020d06050612011b0f020d0215060604091401051509011403150d03020c0307060f0206063c03160308030a02030601021f050f0106030516050304050115031209 74
    0x42041c4008009a21031809071914075034030900000d22580d6007000500300c5680405105129881c2c11580410003a071500d59004508040e200d82c1e80341a0001e1040703030b03a4000d4200c20001600010170070300c142808503000c541c010328010041400c2c40d494604180807a00031301c0c4007160b0184080010422803c1052003580b1451008882900d82000364002902c299503040002641040000004a003480703411101030301c0c104001e01030745204481c0e04000b591440031442e0320b0301c82d014901000400d80c0c0602680c00800358650081d014503034400c410041d600e841f04503501400301440d40074400600321800291034000308407814400303524048050620308610544122054003404105001080c03000041d00c1e071108a41101603940c1d07070341c3c00040b800c061290002d00308490001003010307914006908028406c01c040591881242e0317807074200720165001a01e212082c0c0441c1207021440c1840383c1d00940d0310074052000402c4030701d0100b04941044031581c0c000c0c1c07610039046014805044d40308440e40e0003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 528133803 1250 528132553 528132593
    0x1a0a15080c0105090d08090303030c0409050601030501050a030b091204062f1513120c03020d1d0103090512041e060503042001020c1302090a12150209120106030c03 72
    0x14070280040003030018070030505003500c41e03e001c49102d820001c002089031000e22001e0b080c0d03622401d1403800503140e0780190181c1c000081c104800612554402d11a02d8100e800c000d068039007003451a12110921440a8912039181c0628100400e0008421005100404403076540c50f01aa40d400c0001014100c40503c0311090540e6140790f10312032000196040045251450400003038549500072003121a800b84d0050000e10b5280d52800025009091250100d010340c0a882e000030304460211030f00c074410100340e003194080c200f210345503512031b500814403140325000b254141c801071048005542c00c207500c402c00e80d0000c1080580c5200030050210024a142c2c10000d0949c1007a59420445040c00c90104401c6450711328412840c1e1710810240f10031102c042c06d450485020700c055078010354880181580200d00401c0002074040409241e01700a5400c07203030a40f200c41401155001035440003421540c0503c899042503180c1d4803c0c030a000056100d028007003070300c0b4510303d0801c070b06076840300308000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 528135053 1250 528133803 528133813
    0x170c06031006050f0c010c02030a03050a09020a15090914070201110f0409020a0c0803330102100c0905030d050712030605010c02010f0201020409090506180109080d091a0a1508 77
    0x4a41aa0101c2420966110b4141a40c69411201aa660902030030345280c16541c00e00072441c44082d00400107041e0a00d0f00d58041c0913994403030a2050584102507030003074111103820000c00c03488034410000300d10003e0600c1c11010b017940c0c400170720065642c08041c0b00603201c03c00040c4150683c0910514240410714204a41012459050151540658401e8888880d0002818840c041c42016a084d5040d44447e00580f20705184200300540701e51040c0b00201900c1003203518806800c01c07009448140c04c140c2c024101c0d0509031500340003904030410b5102c107121388900086040ea40511401100103200d50b02d0316141c000d5070800001d0504d4140e44501414a40481400581da2007142da000b102e0b02802e145ca201e40004e50b00301d00a1095a10800540c1d00d49502d1000300b0201080d0742c4d014081d41c5800070603c100c641d2105003240c00305080200418810002c800c45960a40c1000290301d00904c24001159600905c102120310121080c00038960b0340e01030018a125a424664007a140000040c4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 528136303 1250 528135053 528135061
    0xf0601021501560f04091d0a05030c060f0411010c14070f09050c041202120a080d050f07090602060a0b04020f041220030303011208070507170c0603 65
    0x1540715181030007038503400e25031201e50300c4100011401100a07030007090661140f22110000480c5501664074410070441c489056650020001606542445040c0c000d030300d182c00e06d03240203003006080583c2c1084c0c010083c4905151901020701c03040074254002e401643e500d40c4142d00450500200a000c0c0164140b90000d20020921080052180220038240b0f85d40120090400c2c3d4a05100709460750028031070b456001c1411240c0211040c1120010442442952101c50f10841d40f0b02a80c0102011030b0581d451070000741c6040c200180c3c41c4400201038880d50b02c1e0a455802a69200e091120701003501d500921000344142402c0680c44016490a810302a0070540004e454280c05007000400c2a11130364014215500c43c0d04032004c40100302031703940d40c40769940310340c6011740640e00003501c0102c100c40700000a0708546503100481c0d00001c020318516030828454240d054901413043d0303916202407000b403002503410000c24000c0c08100705510891074031066154940040421107900070324044c0180 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 528137553 1250 528136303 528136333
    0x106180b03060d03180611070609150311040e0a020415031a0907020c130906110c120d0632010309020105120603030c0a061a04060302031506060c010c03050f060102 72
    0x30340c1c0c0142e4121046110803c0301d04080b01c0078603203410b076070081102070480021045e1304182040c4440a0b80010780b450b160703444205440c856400c2c420044030030442804e0b004428460740c8420180c0103400d051034207040c0c544035000002c1d28210f44c22100300d0340c0050180580d041c1c1500e600f28603000d500d0305029942800480300c10b00c6241c1103045000301601008248520b00034030075020410405010202d1008000c11880040d181c244015030f00c891034410040350b2003110200302c0740a10030203402407201d24440400900640d02440e500c01d0001e0740c45501240608801031003403000c0c803240403900000d104043ca5000e811006201c00f41c180340c905800c10300183d81100903101592000c10449a2075070f1a140441e04610070760b2200001030040324401400c00078681d0024a8821045001d00c0315802c10009000c2251014080658903500a64031002e020081d0062203900800141000b0309100a03600d00b50b0a550502030f5140100c0d45500c10040c03001c8081e03ca0640c040c000f40f005021043e0a0410 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 528138803 1250 528137553 528137557
    0x11190b2b15120f060515032506030504030203070b0406180812070e1503180a080d05060a030b220c08070519030b07050c01091b080d0207140d03030e0105040b0106180b 73
    0x4001c007402d0300c403070004034001294242080a007202074117580c0c08c0c00c602200342202401100d06091070610003040440c0a0f8420f200f440c0c45140d00d0707001107103022455103a00503002e030002c1c402c680f010b032141829074240c9055217510f254240714207a10f0743c4a98024a01841e03600c0001c02601c2081201d51104000b41e81e1600314090070082c0304445a5640c541c51101c4d004200729a29540f00c0e845154907041c00c100001c4000c26585102c410300300b00b01d0700c5080402c901084131344400f5101d0a008404035090b00103400403082001003840c4282d070f80d0a0700d603607901600d0005900c414056082031004114500302500c0701c2e007081c0e940114100e8070b1400c50b5504103007508007400503403c03c40c010400c155030352004d500521a16410210780034011281103605e105282c414010380400b8011a00742c0c101e880d00004024081c0e0318445a1224160342d54001c3c841800b07000a400d5080503140d40b00d03214082020303c02c440c01140102e20f08020796043c104083c2c00801080c410100e024040c11080041d4106001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 528140053 1250 528138803 528138833
    0x50d140d0915050c090922020103021b0d0518030307020d0f02190b030604060b0703020d0315090f06091508071a1c050411190b2b1512 59
    0x800059082039410040c0141d603074100c114039402d16200501005408a0001d086455400c1b180c000e015601c0c60200c121842c0d4071310500c10759100b81d800b02001507011342c0142c40d0000c0f07640805a103070580e45860600d440c401d02c2803040411800a40012180d540710344103043c1c160160011440c18180d54042412a641140003520880010310341104564900c60b10300404015815202c46903903d80e02c0012855000745e414601c1180b0382200010014454825038203056010303000b40001480d00c440c290090b10b0042030030400c40e02044c10114200302c43c2e100b01d6481348101e910000c0d105041a0200049030032900340d07150000d035801400c0040001c001101015100c115680b640a00c040c40702148140c050500180c0302c1001c040e61030309030b61009074822480707035020704031680e207400b28a418000302080b0032040f0744030454280400e00c0020004c4000f4241d5604045075400c040c643c0801040010108140390340e1165207516034034010304a0031002501030b10f16546125031407074855441e4020304800e61 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 528141303 1250 528140053 528140077
    0xf03201c0e1b13060806090c0906040902091b210406060501050301030804031709060f03040506010b1e160c030c0314120a0305040609021f110a0503030f0c070519050d14 74
    0x35219181c8001c3d5500041d00030901c0303200300c582c6820071082640c1c031171244d11415801040700000141c900d1130103005407140d080c1c01500010858541b1031406030200d241d801c490759181420440c00c0803441c2d52055002e40c3e4040031120010300c0c00d041c641a400d030741441d400703141000824030060021416a40448044950200d5104d5440b010f421081800b80241f010710b59000a022070038003080c00390540150700c00c0384524161503080e07803111296051070080800300011740c40c02d045401074042d0680003d00034550303030011805118406583d140000c016070340040b10310f444610700400400486441d140c40c83d01c0c0100240104074800150b030304040c043d004201c4101034640300420240003099002c0c0c801183c0142c00d081030300a90f40803030700a010b10040c0b00700014501c03e191080680000c80c104024aa001d40034500d180c4490501200201002c1d25030801e29004004080c00580104500d001910303407044502621190380c24a0342c10001440b148070305002c6200003c0218000301e40c11109022201 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 528142553 1250 528141303 528141319
    0x30b01090e0c100309080301150e01031b0509030c1525020f0906010c0b07030203160201111602180a092307051c0501060e0a1104060f03201c0e1b 64
    0x1e03010031406400017000140c08414008001f20b402800081d01061840058480d0462014800011011511402039000c02052401c09880440e8400c1c40141501c120007402c40e250f81c40d061002038003030000684001c0c1e0220340040c01e049032440040882d540c4005c400100d120180e12034004ca03051256500074503210320744240000305141e0040e00015101d40c2c1110085029250890015000350710560b040e03004424500c281e014401c0c414011100100c43d0300081c5401c1c81296284806012403042e0100e91020315010580c80c65100030124612030280e400010407814914184094408100da150111800d0148444110400c0c001540703001c841c01902c5818111181c003850701846051100020404c0d400e045c40000ca0140359071005000348000c001c104203c100789a89103102d40b24901c22500819804866100c0050095008529103041e00300b580c01040d880c0840146c1c180c0c000c1b4142900e400d00744203200ca011380e86200340740c402c0070031380010125556140d440321490305031000c80758810800 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 528143803 1250 528142553 528142579
    0x190b0708070515070e0a0f17120f0a0e06160201080a021903090215210603030d0c020307030e042702130c0801031515030602090a1e030b01090e0c 64
    0x2640003103607071068002d81078031110091480c0c06040120240c400500281c904000494507141040e5244101c1c1d400700784208070b5a02c2c2206500c002d00740d4001828860142d0303082c03031402101c240d0043c080030240c034582540c0c6041d40074000c2c14900c070401c0054003909003800700a007294040403201d90170907024201081e4a0340c80c114148040d00c14608442c255940000d400c40d1160b8042d08041ea070b06100311030820801d1184e00c0d9400842c081c20780190b21680240f04a035400554045407250846005415640b071305081d50625000d0f80c3c4e800c510030006900004900f024594081141c1e04003000c101c0d030034041c154264048184c03020204071080c2c0c1020030140c13198219540d1071809000740e481c504003441030055465014151000c00d1100b80c9500388101d00c141100c42c2507102d500e440e07807003240c1117070308180c00c50721054025003103402050780103c24044046050105014844801240303807079100406401c1d403409100c8000180d20002d0020700740710a854200c00d000ca400401c3c56426a01d520b07442c80 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 528145053 1250 528143803 528143813
    0x70e010801200f03151504050a080d05031314060103111c0c06030222060306060224011401170a1a03060402100e13020307020d090e070807050d14091b190b07 69
    0x5d60405541c3e124110f41001c2c903c80b50302c98090b00807102c0031100500100d5854110985400c204414000082e00400c0010864258508221307525401a6842500501c0516606281110030f8000340c40c10b1360342400c52691403a08880b600480c20708080743c4402c42d109580d070780f655010340380034410505801049103207000c100c00c03916480140340f20710f5294540d55101000b070300400d5a0b000e42c00040c01109500d810101410306180c440d0302d240c40421005030f00e4201e013000d902580e084424100100c0601c1d42c28542c00c5941b03180c1c003c4c51010030005107070208188070303598050b01c040c503103000c0d03080202004007581e00c10600f801d60803654100307000c0c41040c102c0095070748820100400016031001c41070106c00c0390f0000f42d92a54485940758509540c0c0c840c0345c241000e240c00c8403d680082c41c111300143c01c0620442c094803810039402d101142e8100c210350b00e102041d1080b20180102d51107c155209c0d00400b4041d40b5040401c25039000d5886512503d80e0450010107001e80902c1c4000021100d040007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 528146303 1250 528145053 528145081
    0x1021e012c061e0105010806011709060709060c03090504020705031b07050a0504060806070e1306080606150307090b0705190303020d061406160204090203070e010801200f03 76
    0x28140121860001101103945203070640000c1c0e0380103240c403895001509100420b0081c1d0701d050341e820b80c0b601c0141c2c0382c4001110420307001050f0358101300e80c003c000003040c20760304070050140c0107403000303000b0070303d0f1020b002495002c0c00c0c0c1c8083c04100050310340901081e0803080310700c16a4001c3d100541e55505600b050b9146115050380c05080603003141d40142100790209401003581d108507001c0400790768900411082e101c09000d60030194004402180360b190003402e603207051510140ca951500006212850111071081d440100c035500000100f0210703203006110038030200c244004903030640c1043d510040440ea8180542d20510500007104401d02504000c0301e00081036403030700c1548181462030300a020f500406440b88a15061081c0070074250003044041030000801b405550829540a810203540c00c10058240d03005030782c615040d800750301c041c00201c000c1c10412050342c0c5254981304a680c211500042c09074280f001e000c1d5000c00414000c2c0485543c81003481044d602c1c2d0301c0e15036801d40c041d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 528147553 1250 528146303 528146321
    0x90f030d1218140d02240c0702010e0907050405030c0a062003040b03010b07111206060402071103060406020319051902031f0609060212070b0414030d0515040c05070201021e01 77
    0x244840c100445100c40010300c1c60080c012950a9507003400760041141d54002d22060100c0f1b4064005000440e8001800080c0000c240145012400080d254000c550328400559403140003910010b0203108031305042119840120042c0d80810089107001070081c000c040461851030f1280001d820210500c5003001550064043c0702c06c80c56495941d007a1a000d56032002e41c080b50300c11005540f4a030b062600300d00e00b004010307003080030344450395902d800c10000b0341c802c0000319036244028201200b030361000c00040d881a84549801a80c034108a03003141050303144d003590325200314200010400300040310540000c48003980c11001d42c4a803214054250341110203040d10808101c01c44c000100d4642c040110000ca0310ba075025178913140e9001c50350070f02c24840d00c2e10140c0360b141002d0114000800c9d0341078108580444109490400718445200d005680c1c041d20b401c130b0424500f58000c1c5a901c2c0c00d10810603d11000e04005241c0441c075400030f500c03800100002114241442d4010208100070340046981d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 528148803 1250 528147553 528147563
    0x61205070b030414101b0804030e090702010207050616080c0406050d090c05041401031205091c030203071a040c0e01080615030715090306140103020a0e09190503090f030d1218 77
    0x41c0d85d10031210400202a501c108000d90380070707220700c0d003001d07070180d0b121501481d05a90350001608001051003d42500035000c0c40841d0b40c00c0200c1008a02d040c006140078801c0c605820801c46600007004001c0328010f0402d040c3d40004120030090550441b00b184d9164111501c04070350113591f030410001d009400d512044c7c110b403d08440b049042848942e09041c0d80c85200000c599940814007200c0601480b25000c1e084141c501d080200000d400175000d540030711030f20450746000c0c26035940c04030500f403511041044051000a010820540b128080082c012440300c1c503000d9890b1058881c1d48800140141400c8022005420710548003070104602270404148030070100785a81c54000e1a0400f1340c44141c3c0d0070b529040c10b40c640b004255031583d040300d40090038282824100b14041c1130321400a064500c85120f6010480c0c6c21802070013651500360b0154010b103842c2c0180d0020710454003600e0388501c0c40b031b07040314541c800f440d074004c03001e0a80c0c41c01c10b1038009810004232000d112070035040080940 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 528150053 1250 528148803 528148813
    0x30d0f05340308091203160804051006060906031109011d180112030e04060b07021009150309060f0b0a0b07030c0209091606020703030203030412120606020c0103061205070b030414 79
    0x189900002c0e1640100035100440d040401c0c0100d05d0303201400180d480c0707000803c04880c04865503104004041d0450300500503920b0000e81ca440360422105590f00c03c03c0842c856044c1041400d41510642d030300ca114409216180038015000200b4241904084d94244217400c003003580152100240c504a504881c0c59900c41540c41f5020700301034054801c021030002e481895001c0c001e003818010402200d000102c4142404026801c102008a40391175542c00c020084100040c5200c01ca445119250a03940300024028010300b030240580f1401c0c0483c0707018500b4051070040c541c441110400485034092007068480d480ca10301123a0070f229015019500c41c59541c144000f00c1b03404140c600060405554021407955506e030260707210707000c0c1d100c05009a0010f00010b00820200e04041d58201702500c1c0c085581010b003000842110115005240180c2c13000c9030b03500d402d580601c5076101503c10400710706580b01c200e503113031075036088580960185140084082020400d6254010210441c0364081d52 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 528151303 1250 528150053 528150157
    0x1050418050106090609360203031201120b09011b110c040f020c0105180c010309021c05060703050903091f051c02090103200d1127030d0f05 62
    0x2800345c20f070360048111252621803d4480500708440c445080e0440c0c0c100075002000360300c0701e03089207002c0d440181c0c0c040c04204100200c05002d0402a03020348200b5040b00e00448050501c0303202018004e044c40741903071405002800c3c81a0310020941000a00d1800300c004100c141c821508094000c610f00b500542820444000e14003103801070004024071310000c0216940b40401040c444640a05004c1903801c141281c0d882ca5109800080c4440e00141c02039084120481d116060000a55800d0f0742c50707003111082c8101d469040c026650480c2400000b18140f2441c0c4000654a85061000203d9601c42402d41860540144165885082c01c042c1e6050309480c0318429101950001078540c0c0040d152404400b49448150410310054041919160500003800744d040000d100d02c00054a11510900101c05035140e600c4c851888985a0190721350324110000070302d40707402e014049841c00d210055a5042c00241d01005a03032258915448446880c5041000034696481080080c520482c10700c0941d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 528152553 1250 528151303 528151319
    0x627080f06060f01170411060f030108010203040c150f08091612031205130f050f03030a06091a280906170c01030e0606040e10020c0d0908031201050418050106 70
    0x42c49210142e0b048809440100d004445010340300900c0340c50218031002140c080741000031881030b0ba10016010501c2c201b201e42a0b190190400d07801005180c0d0001304020030010200d02c2c60000b0b2140038410800415002000350000041031400c404001c104000115264010040e90300101e507008524145c5035216503e80d44503205011058000c80c041c04815207400c0151f11039030344107609100b84503c0300d5265a440e40c918141280b030649140c45580c40450031044244000c600a031040840010756a10309049070007502c01c0000000400329200310f1b82c0c465030301d51714803240c1c03050784142100180d2a41e01c0035000111085402c144d4010345461004500c0040d201c0041801c100c4810844080c0c0c1c45560045081c0e64941101901030b0f00444085a1036051607000364400c6041c4406030f8000d038604141c10012030b001103110803010361080820b0540e250f00911000d019200314005540351014508441906031410b00c03c0502880c1e0398002e65501c420704a002d04c1400e54070034002c1c03148580d14a04 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 528153803 1250 528152553 528152563
    0x5130b0a1212090e0a09141605040b06123601021e18060d091415010617040b1509040605010e2419030f05250627080f 52
    0x40303809080b070b02001100d540c0140c1c2d4501c02c84104543d852560350782c122a02000d81740c2e00a00300d4a07031040358201c0f422014113011102c021222410440f4086162404010680d1020fa07186030080d1420084500c0040d501e50449510160354010036000c0c0000e602c0284c01600c0c16014902c1079040c034401908007000c19002003040c6c1c0e20703010041c071030b181d02c0007607c0354140b142d011004a0101000c4445440d400c02c403014155a03076813100c00140915003500c88440c4100310b1b03a0394020079003188042c1105a604001c1d194094405486c0103a03c4412240d440140b02d90041c10240000c01c110002400c5840b00b0311000608107005010400c02c0d0400d40b40039006441c0a0198905a9072031900060040082181070903c03110300e044580307044518801440040100c2d0401c108801c4250400807000c02d103080640c907401d0384900028104006a00420a40e680d00044a800c03030b01c01143c0100400e9602c00ca88071790100843d070310340001c0854803514540385201c5902c400c546002e280307400c520529010a03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 528155053 1250 528153803 528153839
    0x705120a0b011d063705090f130b0a06030f0f0201030e030c030417030403050304120b060105070c0e07030e011a0108060904030921021c031101060308030105130b0a 72
    0x41c80d68240d80303070354021a000d44580701a03c8180000e100081080c64034210004284d4600001400e4203410364001004100407217200c10303964508207608101a05240e1320140d403005200300190403e042001c00301034005400c0101401c040e17030b160042090165654080d50056034810500306841071146045001101909003d0b4007003031505070783c5042001d0100c110b482c41c9407004080c52a10341000305d10340345601c04d4800820644000e002c0800040c8082001380050000b0404106220b000d6261465036048014104bd040100c20b010000008041c8200c0009a80400b98080303041c0e960644118000c003003001311b41d4525802d2106000118829481c056460242a40e0710782c0c1ea982c407001400581c54040d10020f000812203c010807007417518860600401c0300780042c203400c0f0303051900001c40c080264030900d14250b030310f4007090b03042503041291891031041c039200901150f4559220007615003c1481b0b414041e4881b031405900ca40c45547c07100305c0600000302184140c6484841030508108440 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 528156303 1250 528155053 528155063
    0x40b07032106080d140f070302150c130803042403090605150307050f030601060807050d0203011413090b061903020d0507050906011b08090637030b1806030705120a 72
    0x4201551382c5c03141c09a814109000c800070f03407415550104821560f1700c2614140d045004001c40c103080404140100c81c000c540c01040d058072a11a11000999690700d0303440382034254010001003080100c0030307445121103022004401d00e00000010260042d00c4d2159000700614506003c00c04108202080000004010350440b1903150300c41051001d60215511b20b1079066002e035004003c000d11602d0155403007041d61030201d04140750700d00007100f603070800c2c1c2040020f1900c0c01c20784980781c14803a0304440d48441c1e444c0c00b40003a90054840c07843c0140050001c030300586000c541300800d200700c07d103034000840d03014003a84a0820a03040c107646690b074a01810384955440d1011840c503604c03951820310042d0912546030f4a2140a43d51020030742d1181c101c05400000c05e1100303a00c4540d070420309000d103602803140041c8035100e500d40600c0200e1483c0b0711038181450a2a01251a1034040130100341071019080c6500a458460000340340c4506903101c59400032003580d05256042c004208018003510130 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 528157553 1250 528156303 528156313
    0x4020307020714030d050904020d1b0302090301150b031605220329072703120206010f060512090304120507030b0f0c070308060f03071715060105040b0703210608 71
    0x2c03c0c109034860404060302400210240044070403443c20758004c082da00d8240c94001210f86640704001d4002c00c0b5841c180b408a43d010841c104503080030301034094480c3d2400b071070111550500790081c00900002c0c0c402d5140e42e16068581c01e5507402081143c40d4903545d00c490445541c40e082400d100c070040c50108131031309410454869090380d0841013411b01380b11a07401c1d0300181c0d6194030086800e1991600c0aa442503248811039080d020a0110321000e1805283c0ba034003c1c4400050191030101d040c2d0020400f140407000c2001010752220540d0207013182e482107100181c0700e20048510f5400381e40c11009040c0b480390701a40c01c000c00041c0311000c0341e01c1042040842e0b5100c11281180740c0b0225088600181c081203413200091188a0550307211078000c107803d502a00d5940440e1400605412814a100100495114640701002541821004c04074524114540000000e042d4011441244001400400d00108040c0a07411020403100f4500d0300300004c55031540c0c0359000d08158841c0503c14091 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 528158803 1250 528157553 528157589
    0x708070f08060601052205060d0204030506150f0d030c0203010608030406020601090605060d0507030914100e1903050703140a030501030311010b030d120b0402040801020a0912050705010c11040203070207 89
    0x80824090b2148005031a90386c2402203001c1c1e480c070f10b0420f2002d031900450b0040400300d03441d42d9840c090704d0078224440c1e00584070360071450039500d01400030b0409000107004084514031548c800701804c3c003055066841180644d10303441c0565003604040781c029495420807402058405000000d00100c507074943c00c0f9250340c0d07602c204e10822291070b40a000d40265081001c0716210080d40c205640001040c5000540003000e1b407030b002d4924144100030302040e007141c018a41c014100740a066021710030701d0060040f03440c00d42050009402c05c183c004090003000f289150515000d54011080b0245505011b40d0303400c0c038568000d00415090004902051074009030314080c00051090900046015005001c2030351180400d031084400340072050146902d508003c0400e03160b81c0040d000034004000096101d80495102810b00c10032a0481d1540300d400250500200b0b50001c0d000c0201e40c028289011080f100d0704020115130507c00b14150800e0000090045140d80002d0b00000c070b900c020703600409944 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 528160053 1250 528158803 528158819
    0x40b12030d150b0f1605030c060601020d050421050a051507080a0207081806090402040b03010f051212130e01030f0605073b0423010f03031e0e030708070f 68
    0x10b94050385041c400c00380200340000f01074500505028400e05007000303c401540d0f0340d403850356002c4c203503e000036001181400481e5804000c050201c1031142040d0f41820b090085e0203c0200040c1024003495500c2005c07881400428480d40701110b400100766992080d0509164845450a69030b480c0011645800030700f01a0062096401c00c0398000805c0b40341c1001d821b14401c1c42156410f0003944540104059845550703544006e1006000b10481141c583d072400c0b85900329084540d01c04c50041200035490300f0100c00c08030b01038409005c0410441d4813014009850041203030150002c81004a080b40040b0074003001c4660b9560b0648104014820340d982c0c160125042c5a200c002c06804007404000c000c2602403422500c00c032a09040540c940c21885e4400144c10386401440b0020300a00c1c00400328505640c000d4003501501c01005500e50f000c0c5140d9001740714a500d19841e4484540d03180f502850780b842034014003201031009080302d0300d89441e000100d444074007500c100b07014402c9000c03000039418 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 528161303 1250 528160053 528160091
    0xe01150806180601081803030916080a0201171b0703030f0b0415050607030c05010f0e0d05040506070201210509010c030b0a15030e0f060718060c0b010311040b12030d 73
    0x89041c0b41c1954075143e14006454145002e401c060344040048070b500d4000000f000078500ca2402c4a0003001c658504030700103411300883d5000b800e22038001c1c01c2002c001d030b6081040649140d194161080310303039407141481c040d4070b100c16001c2c0200400c0081c100092551541201d80c80114109041100c1d8083d00b0030041101c1e0318180c804021303800345004100b10302e045406894820300030f04004229200c2d039552503003161220499428440d075034401c020b5011000300040003a0440d82e0520a103401c5c20280040d0240c092207900a042244012490820208410302c590b15030041c2e46081c00981008005940680035602d1240c000a14040360101c3d9403130140380072021917880428403079100c03d100b2070403406815031180d07007030075881100d000414840003000070a00c41d8985642d0b40000c002e50081180458407954400d50421185018220204e029419914112035000b843c0130044814000480c001d440d920000030350090384803d6091000502000070b0030060400d0a040042c10707001d024020042c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 528162553 1250 528161303 528161329
    0xc02190b06120106080c18090d12020c160806010b0703120b1314040201030b0a0e06040509011803180e0c1602041107030c020a0e13060509210a080c0918100e01150806 73
    0x20354040661409a140501c00342920b02b55a04000361600c83e198038400d1038144d01010a84107200501010080c030300c420700040c0c0c0501042c01c00c41c2d00e0103da50710000c014641450803902c81d95512040c402c65651180c01020100ca01000144006503036220302d11000707501242d0a90110341008600e103001c0c5401e40000040d91030080081640d503c940003070000400e4014070800656581300001d003004100c004e0f00400c0340748a03a4805400003900101e0440c08240703580130101042d0707624103011603090135500f60740440041034005400e4048600008020b441c80350591400113100180e82400d01d0b6110138a0b29005000b42d652001030b603500c01d05032440329402c440c42c00c01014024031140c002030540d005180c10801440c122f5040c0080f5540c0c1081103400a1040407156400141c102d9446070000711080c0d20101c00120103061144079008500c00c000442c0c1c520500c10300200008440c3c10400505602600140d000700c42c0941e19141c0045108e83c500052a011900e070500003001c51401040c20088 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 528163803 1250 528162553 528162571
    0x3030403030e15070f170306090f0601090b04080c040e0303040f0f060e070b070b0610050f1e041e080105060109180e060403120c02190b06120106080c18 67
    0x24151454404585240c11401c00a5000c0c503040c01c02c01c00b418001018068060043e4089600801c03246007441400b1404981d01140388014000c01103181c1d207541300150f100031480f00602e41955500300403104071025401a8903d140f0100b00440c1d84080000c0b0b014030044191340c02c210251001181580d40d0000b01c90041043c4200040d080001c0c10003000c410701c4511030880402c09507954505242482d00c25000800360310404100482448001005203800280680c2c0505558401c07440040ca1031142c024002c04514000500d12240e908000b50b0301c1500109050035500c030f548440f0304140071403240c1c8211364031002e081c2000c0f0701c004c41880303040d0244d4416114008031529081c0300b0442c012010f003056040c0750303881c043e000c109a020b00a13944690b2107a076500040804c281c071203c4c00c607110009940c085604c41c42e61184158820300e46001c01c2c580003c04074003140d507020001803000c005512510259400c0440000d11160b0004110005880c01c640030700c0030340e140551442c1182c030122082c4607 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 528165053 1250 528163803 528163807
    0x708070b0910090b04090b011e0c0201080c0706050c030901060e2806120609050d0302040e040f020a08070e0103031403070c030305040215070809032e050702101d060105040b0303 78
    0x103075850107800548a07035209041c0184496500c2c1802d0f2099080740e40140c4400303403070300c0703280d569507900000341038640c800c0c0803c000645c403011400401c041e41c0310b18000d060085500110700b061030240e041c0c8000d25803160b030500c01450284003503000c0ea001511344a295608060000c100d1800c100300c1c4521940a201001102c802249442d0512903071401d0b40c1244240d949201081e505003040c4000f110078028103000c036641c65103162491610f50140c0d083c004141c810b02c0140544291b0702800c40d042030700002c4040d110903960001840707402f499440390b042d51203203a40000700c0001082106040324025200d880f8141c2c240c800b1145d491004440d0038000038410104440007902079030140e6009030020740340717900641c42103400e00e080303600c150015034690030042040400d92500b000301d82e01d2901070380107034020441c01012020340c4441601031142e0046d201c00000d41e0440c420070600c04003d80d103050078000045103030154903100410f49080805400ba00300081043c0c01c250003400540390b0003030000c41c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 528166303 1250 528165053 528165067
    0x901140904110c100c1409190b0a230403060207020415061808070506040501030504050709050901060306050c0f1605010b03030a1706010207050109170705180106080703051e1302100f020708070b 85
    0x140c0c091f8001c10b81d07150b20034044a40205c05103c0d90030054051301c0601045a66080281406040c12200107500620030444c4085200c800e91032a050354112940440e01580b81c640d10b01c0010050901981c0c1c3e00b21b01030401d1400640c60364840c64103907984281c80000c4036081e4485001076101c07035190040a03003200701000200001d5109502a9510a000c1e0050f2100d15888035031210607200207441c00501a034540d00c0c14070034080345d88200c40e0820a000c00704c1e480c1100520012004c0e0055030030040380b00074026140c4080c8402901703c40309018005044d65a103040310304014200c641c10340c4404200c22003c02c0041c40740e5000040c11004d540058485008091070922032600c0503c620340070809600808500090a0325403201440440c50501a15141c81d07042040c003c052081c01407070f19040506000610a12030800c940d2581d00030a0f0100c10181030350f407003043c8151456800c2c0e000303410011000104081c0f660110801245012590940345c4440e07a5a20306903482c18180030758002041e081004c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 528167553 1250 528166303 528166337
    0xa05060903010221060118050a03110a09051e151809070e01030c0608090303040314090103230609061834030615090305030901140904110c100c 63
    0x150400e10001030003d0300c0c00303400180060750007041e072402e03038000d24103031090141560f00b00340707000075580d09600040041850007000540c0000340e40301c080d10001e01c5404520032500c03a010800301804440c281030250b818000000700c003030414455903c00881d02600400c55101880450683c004801400c3c01403000490b090700484500140c080c010342d10551500090494466000d14006e602070100390700d40754a480405410342e08000d0038a034490300200304101c0041d80158860303507a00c1840504a40f03540c0c0400c010f07001020010240c64151003059038035402c3c002060310381403089206650082c2140c6504040c0322606c0b079a2058241e8407040d0710000b61039404014205061610301d001801d0b83c44c100308020643c40310701f0306014070001e92100c074140400700110310580f08101300361401004040c9542c95103500c034058180d41b90704221041856013480100d5070103032402c0200c014820012942c149030b614040b075000400391152400340e003115440041071403190283c00c4800d078440c101108070003110 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 528168803 1250 528167553 528167557
    0x7050a0213060f0b030402030715020d11150405010e0f03130902090f0603040b091c0c1b05030f0124080a2916180b090126070801030b150a0506 63
    0x503200e1550b800c400140540c12241c031800034955400515601d050a00605080c25480d4003c41e04001408004a15261740041d20000c80400340c9410710520b540a800c0a0410890a1540003100304000910007402419440424140510800c5541d01c1d01d40e00403142d1280619070121144a06401d001c008100b5181c009021842c0e0040804074241108000501103400c00e5400340d8008400804210450400f0000f0849101c3d16004080441c410200300074410100c810000303140c3c810f9080c240071088a02c072034800c0940001800e840d00038008015144c001e100500e412030168003440b40310340c402c4c080c0c4002c0501762030b0404081e000b06103950720b4050580380f1740c00b0810041c9045c0c540c024541e0a03254440c900803d082c12580003510103100c030003000d00c090b004210340c4400051904105c010316244c102e032107041302800c103440608004034902c0230041c80000400c094440c21030030415aa07070300510882c10f8910642060803261141c40504e010b80e01000d041681040300d92a0030f0040346041c00c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 528170053 1250 528168803 528168829
    0xb0d080a031b120e010f0c051306050f030a090203010e070312202107060509101d060402010311220905010614030105060304060e03130e15180703060f170705010507050a02 75
    0x1080302206c041ca4070084074882031514000400c080b908040d0008002e001e60000c03c034a19110b03082155040c0a0500c5200103042c0c600700030ba42d500c42c181152001c2d0030902038952010240d600a65507420048001000c06e00241c00240b040d40701d0107c50110716590101540400c0014045010990420f14458011034034010032860140100740005031a4001c4900c03c410000142c4160100140d410065030480803910a4500e515000c0310341c1090700080302c5078480e40900e0045500d4420864990306440303901c0c0400d640721890414410051985030034101191100c00082001faa0386074011a030080b038410750451004c2003000104810702d00080510b4101d03000d06030002e030b558003110800d0b03e56804024688008002c0c88810051130604035042c03039000d41080c0344129031001c10f50005400121027044200750306ca1040226110760320aa00040252000c90820b907c00c0d44c4818000781e1111103031200c501103218140000c586c80d4070450940f14120380c40001000d00c005107070308010140581803 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 528171303 1250 528170053 528170081
    0xa091b0e12060613060b0313050c060703230d091b0f050d060b060d020703020c0406050405100504180c0f0f06020a08040b09030a060614041a060f0d0b0d080a031b12 72
    0x14000704907494244021405481c03230000f041d02c94207403460700d903050003102d0114510030341090040e40c001c00d070018030640c80c010031060400755a10700c4a6815003a80201c2110205241c40e2443c10b2040000706103100d480220325a46101c0d82c5540c41c6070000d00326400b4080c40d178000703020080060004000d900800e8074030500a0496080414420f800400c0381c110500a5005034481019180e00d42003e2050401410055400b40010314141ca154251b4038020b108040c0980e036180c084009a0211880c44602554030040510003140c4d40c4051182d1215240100c4580400559002990b44d000043c1c05e441168030940880c1401e00e001168015904221117154240c0105651080001e0851080070301400d010041445441080024041101e20090034444c0c01040614401c40980e01c100a403404040300c0303000542e0303c440c1003101c2d03009016a01d000c00e801407000c081d4041006000809450004919501003140c003542c0b1403185181d40c145502100031030100300b075a1344005820703040154820040c0e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 528172553 1250 528171303 528171311
    0x2d0d0f050c1e0a0207240e120c060c03130308040609060503070903030e060903011b110318370501030b09040309060f03060b0f180607031209020a091b0e12060613 71
    0x5281130901b4010f120500208004074021005040d90440d01c3d070400c1c1c5906079944102d098220f10081e40d5440c08142d02e03881410086080300c0ca00100300200d4050340f16801e140d1490307969031302d44203009401c140107410201d45042c038003180240c1f040c1c047c0d900c1441d140c0c0e58154424550b45007a16001d0449110b150840c00810029031191824081c410f00d417041200010b042044000d80105103908400d94044981c10070848103c490381d0044107280740140c02c4500982c0d1444004100700078080540750b80e40a01d000c0b001c0400034118010680c0c044640030380b0240a11011201007052440080300c0050100301c000d607007480641d10500d6032001402c0d95060006849881e10001c204175000398004050b034200004961440039900403400e28104c40599106041c64a1a40c0103010f001041c901d04088030381e101c50b0801555680b4010318002e01e10700f00200028280340d1f40b110f06518080d0014030200d1a0401410054141184015001c0c0d0110000d081151554001c107c07988901180e0080e0064031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 528173803 1250 528172553 528172559
    0x11d060c0301090207061803091502121c0b0d0b0a060f05061603050f1611040504120c02010c12080411030d0c0b0c190203031b030c2d0d0f050c1e0a0207 67
    0x10084100000d44c2c080d2703e0780c1005510b044c0e018007038024000489400c540100c0090003400016006a80c1003000708501c95507581c030342c00307601c0c001488103104059108007110318880c02e21100510240c012100850144032a07511012121800200c0e48034880e0420420001e1240c040d6400c04403004886c400c1c07030001d203400310003400d032230040e0803021410350380e003450f00d1619041240c404044256100107980030302c074030704d132584440b680c21300270b4241c030004d025062080d5421a8482d02d20308202d1640880302e10050b00d40042d0042c01094100c03012511070040341030118040c40c0c00105180e0105c103d40d034035405a105682c40328440354019103141c00c03242c024490f0540c900348850106543d0880ea40c0116180d1a10000460421502000c449018181042401504440441154415410140703902410203a40340c41241096180003203150300740b0702080b0b8060b601580e410562241040210900080d224a8602140c9100b43c3e01400300c09520780805102140b018006800328440b5030040d104a555 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 528175053 1250 528173803 528173831
    0x807030c2f0112090201050702012d05030105090a1b030b010306030501060602031207080601020606090603340b0f0406080903040312030b09070807090b0c160305011d060c030109020706 81
    0x11806010740d116a08072881c08207507400714030f0300c101020b200c03024020a48950006001403068480190420611201200e03481c1c07003c02060030304503140000d09444864950004000d60028011329200d0141c05011417801141c5006240d41e10032812214a45e40901c1d80059006280101c84581450384550700000880d8083c45404001e1520380c001d556a0041c9000b26a00c42c24020304100510665500740000b03668001a030651080e0184e80d40c455a46410300007a02e045030751100e40714041030004900e60110402d952000244038540c1580d03066030b840b254401810b000c0c480e80c2d00700c40d1001340001c1003014442c0c01031607013080541c02501c0c90a42c0325111420381060289203040030030389440300c03600c59040c650991680708aa914041065080140c001815002944154210a400400c115550f08000e000442c10032038203580440c0303051759a1610b60701070042000d944a41b8404400410058400440ca40c0d22542040c051540307103a007005c40710710080d00583c2d010f8525030b60311603011002c0c003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 528176303 1250 528175053 528175103
    0x603051902070503070501060f0e0103150209102003180d020111060403051206310204080f070302030d08010f150513060e030c041a010e040b10090311030a0807030c 72
    0x207000f00051950b07282d01e03007089030035101c441c1e0084c0c0b4603d0840c1802c002da00681d4640c941940e5000e1200d0f0101c4400540c004082d00078051943d030f04ca0000114091410b400c00440e16140581c0030708281c01c643c540b0300d0316459014844443d44041c4600ca003050642c82c0c6800303840c00140c814103100f110303140311038403040c5002c8007100c00700d0104000248944014550085a80c2e000300e04450303040307100c9412094030700214002d00490100150641c1c1c4000c10302d02e190140d030301419041e13044802e25520b41c0842c60782d40c003140c44182c3c007900801c2a04003100344641607090584420319807003603c0c40e1500e00b03200c281080780e0b403604040003400d0007202d40c05c2007420420070040c0500e6880c404a00000c0081605024110001d14815440c0481c04d10780465200592942043c0900341003020059201c0800c015045500130654050041140c888405411519440c10b4a008090351000d409100041c1a42c4103031001c00070300f1099050051800080c4101c0f08001e0240c41064410141c21490481109003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 528177553 1250 528176303 528176317
    0x6010e0f120303010b03100902160206030a2007200306010611010f051314010e1207050703060e1c020106061e03201b0109020a0e07090b130e130c0603051902 69
    0x2d00000030078080f02800c60560040901200b108c11440e0104c4400c41d10420408039a009005800100c0041c80c2c40f1025403080030001d0314480440c0760b81c400c051120207a41d21900e07040b80c10444051340030502212a503400040314001400074561642000810b07520400010b0680b03826640351001c90707083c0000703805080c0c09400e0b1090311300c1d2002034038034110005000401244600ea031400007100203108001400c4e441c2c280308403501e666034141c1c4d0308105060a001d42c101418403420a505418100800500015000340e2090711103012070750b2540481c03ea500c03c0c851040015244c015000c402922560310610184441c2000108021802d0351701c2c201c2a0f140c1e0032511451000320340c00941c8a48844001c00205500000308103158599000420306880c40c0100c03585040904002541503000e80070300c9025103c080c2d811516a442601c04198000c824000c0113490003102021402000040c00b4001d0210341c44001e00752010f041500840042400a2080703400c0f034180315407a14201d140748000d085c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 528178803 1250 528177553 528177569
    0x903160807050f0108100603050c0d060b07061508070302040203060604210605010803040b030a0209060c060a0509150403050a0c0516080622050a0303021309050901020904060b0306010e0f12030301 86
    0xc09882d040030000c01d00601d00b9094140b00903071081100e03907681110a20140d886500b00092281c41c1c80040740b409001d01e03140249030514211000c108a412440a070198a00c07511050128251114100c120450f1910642d60254850241032005180c29000741d54411405403000f800c1654645100042e01440f05420f55000c02180c500c5080c42400d000d840d01410070f5200452500c0d241014501580c40b000384550300207540440c640205580d0b80c01114030100300c1d00210340c0e03941022100f5500500058800e0019449074912240800c58000102407140d030701a114036082102c0144107072907906138444219458002c440d1203031841241083d02902030040c0000410540c5865007000404c080180500c1400070020600700002503000110780801503414500540c035000c10000060400a4540242075102d0030a010060540c00560113032410080884041c001641d5400000c60700d844287c0d000d600003181c200c9000344505002030b880d406a88003034040701d920148601e080d42550002c0c0c10040c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 528180053 1250 528178803 528178813
    0x140702090406020c010b030c0a03081e0a050c0d0306051806041506020a1509170f0904061706101a07170d05092503171912110306060306010509031608 66
    0x25900109228a807544138040d801808d60080c20000900358001500c4002d203889400510000031030504154030741d440c86220a00c0352105180c88020303129401103c000d010b1407141100364a1a03500c6809460110764004e0103107240e050742404e6410001c5030040089800585600044583e030801150301030041c00035501030031041c28a8980091614101c0100601c200e0a0a011001082d4540100f046908103688456520046100740d807000340a120940c40c4e02c545050800078100782000c0110b81c1d0600580155035095440000c1002041d14070701910100e56022145140d54101680c000e0111601410071083c500305075801c03004181d44803000342503c0c662030b44180040d01c82c0c2002454450348041d1508841508000300d20041c4504501c006040362802e2003407407010201010440d5607001d401048213000404041002d80306000b4000c290103510320b408078003071b45d004000c400ea81c014180184078030701c0c64a540004450903005148000e52500425645030b00c01494241924010041036000d40 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 528181303 1250 528180053 528180067
    0x210512040302011e020f190c05121b06190b0604120807020a05060304050d05070c081e0714030a06050a180507060318050a06090507090c0201151202010f14070209040602 74
    0x40c1c0c20400340513940e9101c0e0043c001038030501d94080070b0318600701e12144008612074051a0499803c030780c0640162460180d43c19003501c11a00500800c207004004007003a900899101c1925518401210304025201c4000003e0040724940d8100b0314803403c0051035241080d0310340722003404071051990101c42d003080010b102c0e0114142000034000070002201e04604629042d280c0756140c0302c0701c0c42080c0030000c0c0020070a04103d00240c9550280c0b03100e02c212070603d60300c03000c1c190449200401e0400b2610405034005007200700d000105064003000b070080d201d00101a41c90b0805494060803500006490311020400710766185000e48210f80900c00404445e8a000405411030740d0a8582441240e255180780001c2400001c00c0350196511110002d02ca000c1030038001e003000e07800e400141d0b01d14109500800c3c000c0d0305405c40501c8440c0200c00d404c1c2c2e542d0b07490300b1004802c40d190000780420401c42507203560a001c2c940460442c400c28004914000705540011584a8100c0d000c96400e507010a00c2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 528182553 1250 528181303 528181331
    0x7020f01080c0f04080303011a04050a03080c011503150b031b0607110d120e010c110d05070314010e06060303040302101206030516031104051012020f0315040b1321051204030201 78
    0x441c40c0c000c9c12850003850582030501090300d5404501001d40b9041000540781e000210962100340610342d0304c6c169900040e102c0c40c0c18103014000c0c5100c482c00a0804a0040c2d580c9000f2400d007500d02440c0780000b903084954014814223801840082c0e4542c4081c10100c04580c0b01c1d0103d83d10300341d00c10850400528210f5101a00000c5009601410001e600c11403900040380455446040c060403a04552000240d142c41440e040e0035410080c81c410f079155405100344030540001c0c1c1c1010764282a0b4020782d07142024903580c1d0040c5c1c440070398400314401404011500800c581260301525040c0490798030b03103907161203182181103007404281c401203903070030020301c110a80320a0300c01a00702e800340000d0500d94480c0718121128003e0302c010008807603105045685426410f131185002500f61600a603010074074801003842154242c466051110000c1c141100c100309403100720740e00c85110443c500e0803194480741e40d0140200b0b201441000c1280b000104078888045100e544603500100302d50f0885840 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 528183803 1250 528182553 528182579
    0xe0106051011120c101e0c0806100309110f010908070f0e0105060a0906050c240109060b03132d0c08010e030708090411040e010e0906070507020f01080c0f0408030301 73
    0x150009580240100a034160001c110202c482540d1803002c0351400c0c0003031300310401c070803440ca46d411550f15040d90111000e4000d41c203548520407c0f52171880348480c1e03c50941c03d4030000380c80146120940e001c5c1003074919010541c45600b040605d41107072040d442d400c0b001e252582540200300d0044100c40c2c00c1142d45000a00300380900b0b41520918100018120064802e402c3c82c0600c2043c4200032401c401498401c000005403041c01401d070300d81c0000d10049510a8100038001c0c00d0b5224104500401c0784000311080300e01400300c030403c2c1c3d00541100d49401807003600400817220400c810b4810704016510310400c1c050030783c0c0030b02207c00d2500c1c9041203a40c21a182648c41000b181c00600c58007020648210036214110001d540100e5010f0800e130f44400c9911598201091b281c5034200040740c6805500300b654031811a6000f04e40c0243c41780182500c0394050b00714020362000900380b6804a0354804c01c0d200da00301d08203800305070031311000094103603140e04560089000b079400400104510400101 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 528185053 1250 528183803 528183823
    0x806091501140303030a0c0201020d0c0908060f0c04180b0d08030603012f0f040519031a010312050d111635071505011203030e010e060a0e0106051011 66
    0x22900c0c0c2c8070410b000100f41c03a8000140802003d50f51146034003801070007901114a403c0e5030b603008210380d544040d005420000c080c000c15115100301800141e00e043d8200f5514004c8040700841800d0624116006580280e1840702054460300d40c1110501e580b10b809150300342c4c0b40720381c3c00e41c0d480385402000c1c182100c00410141240d44803060803102d441503045c5440120282031410070381d41d14601071048500340304a80c080303600401c1141c5901d0380c0c4184642034506807481f50001c1d07651420300c06101e060186081c0006000c8052804241d500c041c0680002c211341c111240d00440c0080b0440103c07811504040410507241e210242810f00f00141d03044007403071801005116550810b801581d10441c5d51400c20281c220b018001078610a204844103501300000c0e03400c1d801d01c00c0d981c45244810b400d803904442100800d0410810000c2c41006024203030315a4100c2f001401580c2c1e90f0b094800161810f01220981956100303404280c5841d07107400400300ca0100d0715105c01d0b040d4405281032030080b0702c071 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 528186303 1250 528185053 528185069
    0x714061806250509010201181a092b020a1502030106090b030f0612030403050109030210050703091a0604090206040b0304021c1106130e07110c0301090f17040806091501 74
    0xa0300b00703046001c0714000c01c0740d124100e141c425124415000140d004080c10400304d421940700f42000020000500c0c0c00c104c3d0201424607030740e030646440d04043d40d44c10303070760282c02c1c501003022120ba40d580689003c1c0380308181c218411a010039036a130f10b52201030347c405c00600c00704a800000500180e504192440001c5c040440d10a107985061415240c6d44500a480d030ac0c840c82c2c118403950150201002503d01543c0c00800811030541549000b941d50a100f6403040c507014280000620500d010340f01e6455459044030585c919180780343d0302e2035010000200010390003695810500b0140c1c035840050405840303d1040300c2c1d62400c0030b00400c41800c1d047c0d5006402901c9040440c8001070200074030805089040c0d49440d242c8074050600f00950300715411011001d4100342c02c10030801e61025402d0304c00e0b9100070640d00e008601c40c1c213050a840a19230081d200c0083c81c00e03a600041c9504100b0a901244846042d0130716465032480e608000c0c007034803070b0b88081d0300c001d001c01100380ca501005d50041141e0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 528187553 1250 528186303 528186331
    0x10f0c02010e0f011e021c110d030e031615200414011407051b03010e071a04050a1d0901020a0822051c17100b0714061806 54
    0x260340001d00815109010501518011604000036406030f00a0140202c80941c8401e0000200c0c2d002540d070102c030b562140302c049403011a103c20034050203040c241b21140a005d002002d80c00281036001c0e1026540b242010700c010414001228800c0740740314800c41c401c00101120110003408401691402050000141d0040e0703245884071440c0c1044070100d821440503005004a18801658420490311070f400d40d40000140e64010494086815900d002415030600903410f90b50b130905080b101c13a14207403c240e900001e4284540e11058645054100b040c450b254075081c0c40d02d010983c0300308a035100c0c01d1100d5242d560001040c0c010307082c86c0da010040b8402182002a03001008012600103032008815208402d119480088224000ca80064000040300c1ca038003075880994000070000c40d80640000d010b0360500c1900703c00403070428040c0e035000000b207030200d00300186410b86611070710040b6500344801c0d106071942242446141d10603800408006044405403e00c0ea09000005205404a00c00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 528188803 1250 528187553 528187577
    0x90f080d1b03020c0a09060510030b0102100e100207030306051002011406060304060b040606050316050c06061c12020105070e01021c0809010b120604120c050c090712020c0c010f 78
    0x446190196022541e100d910114041801d0076800e0818440c161500b19500540105084646070844011500255a1250f10640c5440c084044079071388100710380143c11080e1816202e00e099000789803185601c000343c030744200c0d561146004981c05284200c1c0443e894020400091070141d00c8010b080d2403600082c0141c1240740d210b4154070100422940c82a030002c40840c0c1400240e901154000034050700c204081c07900d5000140850700101e0b00140c140b60316030a440081441002501c00c508550ba009024640300d0008021640605001503956240e0b030140304408100300c0c0a20341c0042d400b54000080714104003400500709902a8519410b562008001c1c2c802c003a21111500314000700780c41c0c80d60355030b10b46108143c00341c1100c1040e164059601c0b040406c203d0300120344d03503003d54410400c80c422802486400ea502e00404c5001800307541246408650700c1c185082c0599002a4900d0f2440282605101c070b541203030080e15840c0201c0c0d000100d2640c0c2c0796005074064102c164103003002d80708103107 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 528190053 1250 528188803 528188807
    0xe070504030615170a1b050d02152826070e03100c02150a09050706030203090703020a030f061104050d030e13060612060f0608041e12090f080d 63
    0x10991000500c042ea940428005200e070b2500c0002c0542100d14014003420b00f09070b009541d45c003001e9400e5445510f400c40d107110400a060341c200440340042c120803c184030039000c21041c0390785400580e1951400b000020410302c2268070f20007070180c8800190852001c1c0780300c018603004400d14004203074030f600c07420300400150250040d07501485900d45560380380c3c19440440e04281761200c0301c07000282424690f51040390013003000c4980005840c1c15410a5940050703090645100c1503010700190001102401054400e40013554850310b030304115580c09940f40d010802c1b44032250700607108104030440b1842004402d0151021102140480382e06040c1440e0000e40c1a00c900d6800405001951191b007100d6121202c5e4403929618440007000034941c1e40ca40540b105d001102074084052400c100820f010112542c040243d915540d20078145503202d9039010000220194801040d0b183c24890000080c407400e0b030111008981d03598084861f140c214000300f40022508030102170380101c00c0b2407802607 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 528191303 1250 528190053 528190057
    0x503070c06090c1802090f0a3b100602011410050118090c03020304030f030e0d0e0409020904050309040606080906131703040c03020a082d0c0d1b0e0705 67
    0x26084100080d07104402e10785424142c2d142c0e800005131010301d03880280c440c000c42c0d019100050050b1219100d6200d210704010200314240100a00c07400c0a0b80000040045004003281c62000210600407154038507512198101c003c6410040d01d6031207880500030954280140d00c01d801c00349000c042241002400e051001c0b01a0254504000307000107640c86051f00d0803109002001014010810f8501c40c40000700a58000c039415000f05590700010200d41d442440f400f541905004050085c0e2980707c84d08590f010751500e19940e1050b1103401d00e07000740e0344101c500c80c0101d200e54000d45e40c7e8070242e414041520550b901c5407044c04404030801a2104002c06e45691045005605050056003450902e40c03041c03200ca21034500d04400b20811003000340054901065900858101c4c40d01540c90740001d50321000c040807108141c042d4600341b0001c000402c0da1202020200c0b0644541241d040b0125003414441c80c0c06a40900220ba08840c480c1100c6043c040a0700348a0403602c024034280102034454 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 528192553 1250 528191303 528191327
    0x903210712030b130e0a0b01090c081006020616050d0203090a110a050f0d050a0b0f01061409100e010201060909030507170408490f0207080c151e030f0601050307 71
    0x502e44494001001c003c06210081010364880075041d010f5864409d400f0040c00c3e100c0344403021420180c04159501c03020303411201160882d90051a1a503683c0000d1250036117070030b0200b8144482408026406a039034000f41d442180450010800310109003041c5d0f0700341806540d03180c050307a0780d0a030611150301d4a41504c3c030780117020341c3c103003024403200e2804916000c1d900c80041c04000607842403000e2401c080f0701140c129095030740e4981051031103c40d030b402d05100d03070b94203150310550b00c020f46c20800307010780d0810b0b171001414000014201d80e80c6401d101681c84240085001071400145181003011040780114500120640c0500f0142843c00155450390b030580185605c621010340319001d0360b0508407001100d6000a4041800041c88030b60016101101d1200c0000c9103c40c100043c010b880002e0380c00c21510614010042d8645080901c0400c80d40d00b0300c062680c900030441019806540700301442d05441022440d0303078030b02e001e2108822590b0060841410041d0130024403a150341d01180080003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 528193803 1250 528192553 528192589
    0x40801140c0a090509042109060305060102070f170f010f020702040e0706020d052805030601030b090408042319030c091829091e0303040b04080903210712030b 70
    0x6551a2424982c502d82820b02003541e00d1400508000041540108d9410841c0d80382d460074002c50311040d0069803140154000c0ca6800e075000d85040241c03103000140e140700c00340b8010070b41d1070380d072140d204e01400c3da25440344881703616400140c1c2c10110f04240c46080030100710040940941c506080b002912405080d40f400100700c004600b21703c1d81604401d444030003040d510311002e0818001d41028240e03800c00c40c0c000340420b1034403000f2603060a0800b41984250f9104180d503203810b0800c03e031101e0f1902c0320700d0001000c00320034120007480d0300d40d401c1c40c000100480c071000c09507030320314680b40d084605c2c81e40280790f10a0915043c40c004114801c03c0e02d0000342d1202500b0b0740f5a03d220840402c001c2201601d404820b002c00c140925100c0c0880c100b1101c81815030b68100410380034001c0c0c0e65034031080c2c07402041c00704600c000601092110303006e8800000010141c40d4241508030b4510f800c142c7c43d01c1100a401c0c03002508004101c1010051030291090f810180440080f680001d11142d280003030352a4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 528195053 1250 528193803 528193819
    0x91d040302030f03010602150109052802090301140a0501210f06110d0906050109020f1602010e06070b0f070c08090910050a031511130312050708040801140c0a0905 72
    0x400c050090069810390340c40015001d45035a51550000c0d07407001807980fa100c50300180380010482c1d900d00e0050b14454060b5044d4211790055081c0310224030420749030845c1100d642400390401c0d6503000c0c050006000c001c0c104050180c141412040e04481c01a4028080944540360401501914030040d500e800c7e080110501c0d80041410004040c01b00d40500d420f00510000d0002490102030340314400c7c00d80240300c20440c580e00d9504078422481000034105066205010087da0800c40401200029106141181c0011815408641650442c60044600c4000c0744100040200031901c295804270300c0b4501200b40b15619201c4d000940f00340f007981030041e900c0c1d00004041c481414050401800050030220303807960b4a007081c0c10351207511001b0032003041c1028844c480a40010080d181e081c16203200c0e5192880c55551006207100414100c0400d001042c03200c8808100398001820040c00000b002213030480c2d004a08010103000205150301d04041401a000c07155030154441c016104140d5a40d6 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 528196303 1250 528195053 528195061
    0x9050906060306180106180203041205090a05120102130e0712060609030f05121c0b09060f060a0c05030f03090d090b27040c23070f060203040f0b0106090f06091d 71
    0x240134040d503407c111240d2100c070104003108010340d4002e40c4110b00070710094000b0619610115094030880320740690010400905010500c0d0441c80381d004100b04070700042c0340040d1a207000283c194240c0c02441c0c441980803c20040540144480318808088203007000f5490a001c0c010700581c0440c003029040041c02e16100d42000030401980141104441e1001c0c2c40d03890020301900d8165910044000322810401e158102d03003090f00c44607001d445e004140c017990b09074a4051100039080205103008001ca01011000890070500003800c900001181855a916200014a1a0068030f120100801480c41002c103c20405542568230800341d50404d0a03045040700c02121001035081c0c2010390083c600b60103060082d030402e4420f000c51040240f82509005c0d10341070203c0a0041c410f000d010030610325003210004000c1c1d401981d110340704107002d032003136000d41d102c9644801c0c00360042c10204144c1001445003089200d06400105040e2420304c031064280455680c9002d90412845175001000000c6 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 528197553 1250 528196303 528196351
    0x60902010c0209041101110c06090d030c0f030305011a03060d02010503072d020d02060106140f0d020d0f240509060303040302130b0f0a03120e0f0a060909050906060306 74
    0x44810398000f0200e5165080c01e007000824140d0786944540410b41004204807981d8000c90000c100075401814142089014024403020b0030303419104404102040c058039000036102d40004006501a50700080c0c0b540c140103003840599030b40701304803068000c24020060f82e56141010b01e1003003603082c6090f0352a516070190955900552070b02213115811100311b1181c2c1400f0070502800c03c41600c2e4211040403082d058140e0b29200b003800b5220028200031542d04400c0900e02c000c010410810040754078050003003094100b01d0700031944d0314020342d072100140049130100b4040d501e5003a0301d0549403003546090408a03a40303044a8450f05002d040300400098481e6000d0055800840e00034000d0400064240080c1000b032100646c0f583c407417160440303521000d00f485000c2c2c07001d40341d100703034058001050b02c10250381800e0300c680b500fa840a003240482e0a9031702c03403007080c100070303c13070380d101d08a0080c1413504041c29103c0040031030600d0361201c000c0106a0b078000410980243c189120342151816600c28 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 528198803 1250 528197553 528197567
    0x20c060a0902040e0d0201050a0b040e030a030c1b030c02040c080c07020f0406051210060f0f06031e0f0f050124210c08061002010e1f0f05010303051209010c0c06090201 74
    0x4968818055003204440c03051b0107400546c07003080623040802a4031740c400c040004a0742c9a60340b0030195801031280b012154000d80c8002c00c00300041c01c0100c00140c04000000c01003019041c101d0020303148400380b804604281c081e022604803141891242450003069281080c0100741000e031103082100c0001c1c410780c8681d33100c0b4001d00310103003100d61451414a030b0140c0d00d44481c07100b81000c0d49001000204c042c1110011004d07030780000b000000300d43c54840b00310003416400c945120309160b035035030403030340300042d0301c111060301841d40f40100d00719540b00c0c0c00030100c0340168052800100d00300103080d60380d00040c0c08120210154140210b450040ba004118010064007407264814540094a01e800d50040c0003144120411144080c003050a540200d00fa200c1d460703082c0c40564481c01c001c2c2c0340200603100301a00b880100701c001851a01840b800000c0d5070080e030041d03002c10f00014580009128114042c1c0e031112265009102c2c0f0a4800c0d4010100300317500c075014225a644414150440e0721400c2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 528200053 1250 528198803 528198821
    0xf190b0f150d0f06141b0301080606010e03011b110d0306031211030f040f170d09030b1f0b0408070f030b060103020906160b01050102160f03110111030328020c060a090204 75
    0xc000e900f03102508900217484c16034051000704050540e01210458003400c60b0b0680d074401001d00820341750b01005480c00031400031041d501d0b540711011101c90540440c41005486040d40d2034030740c1072122031001d5007000508022802054108682070011550805026244032a0f500d042c4c04403144010199045001c1c0c0b81004d100c030100024005200320000307003200291a100c45070080301800040c040c641da44c0a0352028004207004400c00c00110f1841c40c1310b19400b842c610070b07036410400c043c40040302c4244039801181c20618003040901c010002002080003618059280305400e60640e2180e0304503900040000341050380004104400d61654015500b052012000380020a105881d04664803042401078034014030507001c0055200c880841c20508441c08020f402e0021415612404015100d1001881c184289042c41c18260441000114421807900301c086030300300407294260402c88002c25444d0315641c018028101e009101040c49074002c41441000140c20328a4030103d4042c00c4121 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 528201303 1250 528200053 528200063
    0x503010902030619060f0b0c06070e1c020a180501082808030921070204050a11071112030c150c070c09020a020a080a02240f0c07050f190b0f150d0f 65
    0x14001400201500180149500003402d8600310754444804507504201030221541c004c3310981d00c401d401da0f050180e2078581c0d0010b0480c8500c55181e00c00e8a1007004d40628024400e5a41e40040120301e200340503500346804035028800c40c183e1030540c82002c4009118010340500000008107100c8141044421450550303281c1401300140c00c42c1099141e50400d81c01a80503500b4080003480c51201c0e403051813011115884801d0409401c0c0c1c07a0900d00f075451400d2250002c490510700311070b400c0100054903498641c00000c181400382040c0d14902400c001d0a4030400310810b001c0c88002400719140d0707005403a104d010040c0c0300c50880c0b408902c0c0258014026190b46000900088601d50200d0140b05441e890071540606003050000b001c08070310116103031b40c078440661011407601003690700280403e83c024001c452642c14000c0c00b450405107041d58800380d01c684012844100702400c00855840034400340d80703032054030b42031941c146403a43caa40654490100c4030210400c128080c24580d040704e03042 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 528202553 1250 528201303 528201329
    0xb060a05090a24051b070e070201050703050709090f020904020c01050103031d010905010c260c010b0f1003050c040f0b0a0f0804120509060403050f0f0c030607050a2a03030b0901050301090203061906 87
    0xc2c0400c01981c4200b03450235001942403400080c1014000c0c0140c07401225039981d10f03074846191600080080075401482d482458082210340516511400507154545040b00006129451442d0141c19445841a10f01d50003c5121900c44241e800c080203500b100c0080c04e080c0c1c12000945811440303040c102003c0005040040c0c1c0d80880c2454910150481c034901c80000c0010050810030014082601ca05041e4070a0310190000c0711248203411243d000b2010001a50500d52182e1409001a1403508654002c40002c40c0b41003045170300440c0108415907071b052041e483d0070a40c55030100e9000d101e05580a11400040c1003601e41ca6941c02c0710025074001c803d80d80524030a001140e1030303e07413007504031100e071095503014030542c6030209840b0f0050801d80c031980d00d403400e440400e0303c1c0d00317601880d4580703080ba90030756001620101101c54544103100340d40008040203808200108540181c011038002d80c9442d4049006880004500307410a0460701ca80444840041c0e0440184c0368540100c00c0f14500 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 528203803 1250 528202553 528202559
    0x1803010c080a06170a140a0f030804030e120c091b0c06150604061d011209080306012318030a050f030c0105150a031202010b060a05090a24051b07 64
    0x1001d05414010058008244440c80e0740d424112021046100a142190400c401100018a0302d0901c3c81c200d49448040d55882c440f10b03166141c17001d405071001c0c0c003c030300c555040008040e8032140496032482c0864003410380460b422041035407052001c0c01c0385d000312110700102c0d02a1441c24100d621800003400b04994407402d8882d40c6448040c1070700c5440a50040c1700500005143c40c100340d405941e000c0e510f8500e00f005001e40d00d001c54040070344040c180140c1003031540242e6898020201c0c0d060244003611b81d241400e4000420f021211800c4152481c0781e6040300200b8444481118081e00301c0114165038400d1600010741040c5c02884001c150788102900080154004006020052400c200800070740d61003d0042d8112602c08200b298031040b031314010700004108041246425140b840000381808212001c0f6925078410700762403020036008520302110780380040000000d07040500b200035280c0500561006140c41e020024000d00501182403015904152440c40035403003c00704481d46070756 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 528205053 1250 528203803 528203807
    0x11011515090b190305130206091504050409030e0f010f091e0b03040506062e12090c180b060c101d010203070305180c150a051605030d1b12021803010c 66
    0x1000c843e04010030b007040c000411048490550f8190585c02403d054035201e040381c200b1400712851013035803e0f4103109101c08103c6880c0c41c402e901005100780c0b2a000041d40610404c82c50240003140380e810000d403500c2e03c0222640c4000b020040792680d1890703030002c0c4602100e1030039100854110410303442d0044100000d00130000b03040d5010360b50a5800c2800d0440024010417030001114005285614451401001d5481006100301e903201d40d0400007100c02050366003445500c0c0075030241c4c140140000c03600c60340e41d030140f0030708001e510101e0341c40707160804003851a0748a510f006010500c85940d01c1c0310030030301d424048480c4010440c02000b15560703c0c05600c00303801004140c8001202045042c1e82c54070349480083c40701c80001c00180000313010080400c4404590744001403483c100041031102c80306081c0d1190856285911400c0a103469460107201c140c1196004070b14a403a46030342c50b078042c0c440784c0c04c41400307001001c8400000d81d03120400384000001e022605299034040d071800c0251245a9 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 528206303 1250 528205053 528205087
    0x90506120f0601052701051e0405090606030c06130e0a1b02070609090c0e120f121207031407030c02030715050402100504060e060d09020a080304030311011515090b 72
    0xe2402c58440040702003164082141500c040d0814844800880041c00103150007420307146007403420b070046d23890003581501143c10350381c06641c20441a030044060201e03502c1c1c02c1c80000115035050b100c2074100100044640114225441a120b4104008000c5146104150465a144240f02124621800e200b400c000d5445d050347c442c1e00009001500d001c1806030391801340e6a100e61480e0b03680b40d00c04400000304600c1c144010710803000740c400c803d60b503000108180540310b40c58160b10f00700764403442c012086500301d881c01011a010186404c0c44030b514195000d00580e0020f00920340001c4803e501c4a080c0d01c0c42c8241030700901880049101c0101d0649280c216520551098072110840058080c003501d42d40036900030742000c100300d111000030300d0806c80c029001c030100b0348801095001c1d940c0c0110380c40c510290400440c1ea04002428418180c01c046101d0006030300c80020041480554040e8241d055035000c1c003548600e012140d2035006100d420400040c04820000b50303611188258014050 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 528207553 1250 528206303 528206309
    0x30e032b0e06091e0f100e03160806040b100e0c07030f03050705160503120a02030708090d021f0e070f0f09110d1104150c0218060a090506120f0601 65
    0x4440c8052150740d420b081007562a1002c024102500500c0070860032030316a084a0040e80d000440c451088140b5500c1c15480081030384240c4480315000119400d050609440c0b031840020200c01520400220f030b0002641c0354040d4100d50321030125103550358825640506540403084410b8014288401007487e00024903980d4420b0315256980d1003082c40580139604101e40b00c602240c0140001c2402d800d08244910842d403140c1c096a150802081c94000c1e0f1410542c5d2503e921540030082003c81c5420160040d000300d603010040810007544a0001d40d1450045900282000140d0200406040e0790b0000b81c0030081c2c0c8003d840140f610380e42c583c03403070314001c1c811000d01204001001841011900c903415502c404a807055217040091544007000d454007801562254000308000034200f80740088a4081042a41d1214a081c0d01401001740c0c0014560911995140110a0011035640e500041c1c04455000e81c0120f910307a41c0318002144883c0b803010f10180360182000320340212a011030640d0503 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 528208803 1250 528207553 528207557
    0x6061e0a2f07170a0501180209090318040b0a050d12080a14011202030325060b01170a0504020319031107060f090b03220b0907060503090703030e032b 66
    0xe407046042244140e41100d40042400b07410901c02400050859031092016584910440d21000b07111359515084072041403089098007481b2030810f0451400c3e0000d0345c0c010000e18000c60524a100341c81c1c0000400100d02a8452503607042104e039661100c090500040400500580c0701050b513041000e01000700600b003000007a030070400a601d0791440e10030300c00840a0062040406d80c2080c0e070714254a0742d02e4200f682c1c1880140400c04020300c0c51106600419284000402811103238507000e0190f440015803071f81484040040f8045d030242c041c22a40e40314178010404505621240003013428092075a2090180368030030a0140241600104644070780324041c012110000d82c1c401c0e00f200d20000517002d5800203601240c0401c40c510049010715006004c120601400e0f15940d40d00301c52110143c1c0c0200c502c5420034082100109040c08803c00511150a14034510b18100c00c1c847d455405901000b002c0c44190782c10303168103840810103402c0c0d501c410051a00d4020011841d41c41e00040e4010030b41c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 528210053 1250 528208803 528208847
    0x1050601090f0e091006060f1103030f0403050711060a0309020307090501060e0904031b11130506090a090302030f030702070314030405060a030f1509020d0f060b0306061e0a 76
    0x400d501c1118100c0855298105050440d42010300200184501410040c07080c403441c030f401140d40f4414413a1000070500780e25a2115241905006422818101e06c01802500140b0401130040241c141440c1d000380c1c5490b00950790758076031600218440f03802e400d0a421050100f016805c064241d4000400703503000b04e04460b4500d60b94001401075407001d01403100001c254101500140c10803502454006100e400c0144807900e6460072022080b14410b0203941301202040045e0050a186100c00c1e900c4450326801d010380d00e045000b003011400c0141c0f0340c2c013403250b444089400707151090040d1185090b800c0fa10750343c0ca06090038025643e02e00313070006807044240300c8a12007502c8000401c030350071240054905c5003084040d41041c1d0051404100d0700c2c0405440b90b070441125003540300414080c007400a00140c495128a861000300c4010790100300005152241c103015212680341520790040080700c045541e60604801c108800e41d19840c144240080410010f0010b90085080c5080d4101010619 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 528211303 1250 528210053 528210061
    0x709020901181a0307120c08072a110d021302030619122306070801141905150f1809151305070908030f13080a0203030d05130b180105 59
    0xc509100940b24a250100f040181d0210f0082150040c0d50300c402c0034108400c02581c0c01024a003506c040e400d2a00c0090400d004001b48183c1041881c00020080da800d0200031400100040c2118414080500301e04010f035807011300d541c0d50580007011264050b0100210703070070100085000e50170030f44229124400307140b00740e0591910300084104444202403414200701180d00d8243c0440703066101528494259014100340321010803d050003a80c0a035240145585065110400e9400106c101032140b8010b469181000c52440070f0541a90303011203c04000204503202031100744141c0c05000b0708803502080d4080303c40c1a105540e4040d00003a25020550742d9405120031520f02011142d581c8107200003d00b804c0d1002c298440c640c4000076007081c080c2180c407804013030b00c0d5401c010a03006009000080d4031304050742018056009003030000003000222403581c0000d491340581551a02c000343d580000462092140240308140c42d0004692045414001c400b1504203e603404110340750341c2418041 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 528212553 1250 528211303 528211337
    0x10f060b03041515033801080c012001051003050132070306050301021c110901080f071407030c050c12060a0905010e070e010302010809030f04180e0709020901 70
    0x10303886a5884591403e1440c1c030780300c141004000c5040401c1d60004039500100000f0301c4405090340c21010100a941034404454545007052900e0820324501049040100801d40c1c001602171401c1400b4248030000800420041c008200c82c40040c0d5520341c244014031028150a030480c000786d034000c000900882c4200942c40020b044159010000300501c0d006c4000c4030035100c6482074100f0f516180124105687e03c001a00303980050411101039400c040c8488403140c05440b070030030308001c0900c60b5804e040744100041c00241005104c902c4441d04000060011842094011340e201d1194145a0f228601401c004106034101d1a04496620405450340304600d0107811900c809440f000041a599036000605400b034895007104076095925001c1e52481d2010600255000c1c10349041c135020298514000140400303000f404d02850f0340c00401002c0365a43c0c05000700d506884902584080c07501da42020341d1300415110304110514010f0035408201e80185030010b10295809a8619800a03080111 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 528213803 1250 528212553 528212557
    0x24010608010501080105060c0a02090c09100305040b0604050717190c0c0210180e01230d0f0b0601140d1b0311030a110906040821030411090c0d0e010f060b 68
    0x202c9002c1035130400104200d203004001424040b1071681907480195181e4003081682c5002e69007104580d1000c95210018101a600020321000d240782c180841c0c1055202c8602c5014080d0102c1d000396150340001d40c83c14040c0c10302a0010038240e4030780600d440c02c6090007030181905250340700440e04255031002d240d841a00c000400c5a0002c1585801074100075042e20a000000e5020303a00814800000410601000c07100d8020480180c001c405000c00c2900058485200b8010b58842d04c84120101c02103011840b51421440d4440800c8140b503c2e10303001600c0c1c6501180306864626000180c514210545801140790340045258a0303142041001c410303000d59032207242040000100380000742d244d4030250407003800e61080c802c2c000d250031213101c042000755001d90000001a0b110301c07240308c1c6880c442000b1b940c00390248641a13085051039a01c00a0440c114400b00344074681400224031004242d208645e0b03984514441001200504081c80c0d018004034000c1c101c5040c41d0400016071781d6100c0e01 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 528215053 1250 528213803 528213809
    0x3040308070f1215050303070f02090f130f020310020316080f06010f030b040e01090f0b0c130303030c0e031903020c030304150c081e0d1a010905060f0c2401060801 72
    0x550101288100560f03000404004500c640780444545000519850520003002031b240920300c8a1012500343c0144400840c01418526201851208018031043c60341500c0d404590b1040b0002c54a200900010385007454180d25036851034030003c04c3c40aa43c3d2040c0d641041403821380c80d0150b4a90710544861014481250240d000c5460300c00310400c030303510a42c00100010304c0144005850080e50340702c0e03030868484a074201c0c1c2841c0314406840c2031020f000c0c04581d00c1035265450a01d80f100c0d4035448a1548418070000b424540c5464844014502030b03000c040c0c0f81c090140840e000c1760945000121054490017065002d40540541325519003400f00c100c40a503481020810351101c0044c000f240c2c01000c14030141c403884028403505800061040d291030700040d0b500c0c0459250403026a069040314500310f0001e010311041140200c0d540d8010f191001100d0085640a450b01c1d000b00d4a01c18a1082080700c0c0c030340f8040c006102303541002e0400c48015006030480800d09070381e02c804054400321400c0c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 528216303 1250 528215053 528215057
    0xa090201120e15090d08090a0807030c020d0b0f070f0e060a0c03140a0f0e1806090c040e100e09030a09030b0a020408101a0409020f1e060301060503040308070f 70
    0x512544510140c64008022a01d080700c11250448820189096038500a513041c803c9034005103520ba28542e409404690030104a0b006400c002d8416941c05400707100b4244000e0921440c88541810355407100303031900445801000746180ca14003680c5207107035041c007112140d010480c2c0b11581c043c40c6201d0305812000b00c0024000d107181900c3c4001c20794000c01418012410407903480c441e0655111000050030b80c03000a911603c220108451026002841848209000e0740c1206180f000d0100006100c42d04842c0640e04d84886440b1010018840e200d5600411004086030f03062004481000c5c0d41d2504950215812148640b5113882c4180c481c0701d90012040092451502403012454103610240c0011140034010300d041d0340d40b644141090003d00d041212259502c2030400c82c00f80039618009000300468081262400c10303800079402c0c0340034071326250041006000540400c5040e2149c0381420800414540d01c0e90b80d035820040a5500c112000c07000503103000041800c182c000d445100e01c1030110707 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 528217553 1250 528216303 528216317
    0xa09110d031e090f03062a0203090f090415050702010b1e18190506030a0b090c180c0a0503090115080d110307030503191407122019050403050102040f030203060a090201 74
    0x59241e06c0b01920301200a01c4c40d040010805603805100c84a9080321402c61b074020b50b440b950340e04108007030f11904031400390080340c01d503040000041754401084801219134800240c40d88680400300c0c0104040d074255a001040c40c04140f100901c484121100308000b110070503009112800250f1041c1001c0d120390100507011682c02007081c0054002640c0140050300321140c08403c0c0e100c0740217402e4150350501e440d0704012303030968890502e0307901242c507408140d00d204c10500303013102e140e492307403203500042d038100300703000c800701d80c52440030b40000100841c003000078451705484241140e11030140400b1840807a0307289406040e601c501000b514180c64150726401e040d40d0320002c24503500c030101b03c0c408070402c1d651028420034032a01d12110340164000d5480d03607a20301c0c1d075844a0040700e44282000c803400041001803c0390002e02c01c2258461640d000840c80a50b10f1840d0694860140d42c000a01b1540003082c0840c00203016522207040303138000c604480d101c0d15112000001c0320102c0f10041d00086071 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 528218803 1250 528217553 528217559
    0x807120b0105030f0a0f0525030b090a0c060f1101090501020301080f07080705040203040f05070b0315040207120c030203070501061e050d0309050f030c130e0607020d02060a09110d031e090f 83
    0x3d0f4440c81c154580600282c03040340040c00042c200604864801a014100b060009d10600206038103003540401c8a2004043c0440740743c0f20a507112140384550381c20041c801a50001c0b55208407520214484420300034083e8440300d14009020b0f420034010a0300c0c9209541c000c50b2140030024009007200d8020001c3c005041c201028440030f54401402a1910aa0f803500c550015808005d0701c4010900300d40d0054490510b1090300e0704c0e003450201013500c540e00500400010440341d1065648059142c145007401400900c4c01764118011800080c0840d4078050700011400c0b4401c80d90325003100c01d00d00c001031090300c8100700442034078000005400220f029009000b24185118071607003000000b0700310303100d11541c900050440c040300d403400300c00a034951258941701a0700300460741e0082002d0000d05462441303403000960302c5200800c14070340c1c4d541700c2d50840d013417000240c01c40100c1c035806001c03d030388c0c0402030801620301c6940915051641408885450416200d80078801c1922003c444003044186 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 528220053 1250 528218803 528218813
    0x13062415090503030c060a15081e1207050d170c09120f1911030304050306040b04030309060c17090106050d030c110402040314060906010513020c070807120b0105030f0a 74
    0x280c0d0354118014001072071804a425901080030b4691100c03080014040c0f40b920010b00303401d0761100700c651300d6074030b6540206000e4a000891240c090100b0b00c1c0589900c14102002c4d64540001040b0080d440c80c800503000043c40b40c04204401003440d1525550300c15a02081c500b4180003045030903141c48032042c03022040d9440d000c480610681c003000120f078070880c3c11140c8241400407151200003c02000b02001042141401498001e43c008030040c50800e4500000b10b6203034080280000c001042842c001010103010b580a010400e400c91404c221410b0b488501900048a51183e011507009080004100381414000c038015900044c1c1440c8645915a5080d03589030508030301205c409014490505d45070311244054802140200141010114090103103418101c01420380700f800d82210380107015030303107a0b180401d141c0540f8580060f0f5807010310015500f071000d243c124149034040c0c14800a10041c44141040600b406a41a0455640e8440c00c25030342d400b030b41002480c550044c0c0717201008030b8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 528221303 1250 528220053 528220079
    0xb010f090e0c0f12120f0405010305130c03021504030516030b162a0602161704140f040e070e06130b0d02060a02160612140609040204180605130624 65
    0xf1400c14101c1d0030205c800160705070309410807905444a0704000c00d0070401c641e41170007001d030000307002601b00c80800c88035111004e540b01c4500002c1c0c041d8a2041d0b0100000c2c5030340701190020b44e0080180d540d40c0319044803850b500001440152241c0035a000841d007034242400003264100790355100d8900d0030004d401002403034030720111401c60f040b84039070b00c3c04003143c12800107000b5100c0c10703090801d040e0801e1811000c10740344d0b041100354101b030901040c0300c642c50030301100c02151412696548922680b0380020068091208607810030700540c0c1c800030354800c060742180e018074403c8403610443c1662202c0c0604036030030840b1f0707103602c007021480d05400350030300d2401410b859800d44140e03031010030400c0f85032284100d04d6101c1d800040052408094101080c85680e1031116031050090103424564000381d42c1c41006400a40700d03641d105070003082d142c20481d174207410070390101c014045417405241807542c0c5000880161001828009072000510000c41084102c01c078045100e40558280301d0f2001d141c0c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 528222553 1250 528221303 528221329
    0x51f032004090501060f080702070902091203180406141302090402120c0d060e0f0612030904090804050f0a031e05070b040305010c0e0411250b010f090e0c0f 69
    0x112414919a180818440280060310b01d00d0400720f001d51402400908151411607240c041040100030b20200545c0404c03143d040341c585013070240e140e10001d0001000303200e8a60040741213200c00103002d40380d5403400b5161003034087c3c100c4080080316510f403810b95200b10a141e085030706c0034607803101c1c0f80944181d1f409400444000ba0006003400c0c1c4100900300a408192060b8100c65404142c03441380803094003590018201c0f9030144140790800031000701c00184040c0c14181f0982509000c085e02960820642d414000004c00030301c82c0425609010b8010b41c0305020341030003441c1ea55040c5900707040a075031100c202c0b40d01000c0340c1c41240c05846040e5611401400450303550050180c0042c0f9000581d000e040030b1802400001140c04140760040c0000012000f030f079000d54100440d0013001c4031010261510030104801861844001c11981d11407044080001401903c00c10300100359918503034280360541b00c440f80704100c411400945241d80c0c21040684540c01212040707610700d0390508214030601 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 528223803 1250 528222553 528222581
    0x20f010e073b0c0c100903093c030c0e01081e07030501091203140601081303030608030d021c020f031311030a060c030b0a23031e0703020901051f03 65
    0x701d54950b205184402e4299a00d6444000c0440d281c401c502c3c01740500d4641d81d0f4010010460700c655960050942c0000d841030070740708418060001c03691800390ba02c440795103020b03032080705a440e01c0d050a84c603105800d0100350340130400c031000030480003000400b940c10307240001d004111103101141281000070401c190707020756000343c60002000920901a13405d1030780c458200318442c01007000000f070445d56000c6000e00960b00100c1408820f03600a200c45030480c000150142d900b03c154201030340546078a901c01c15044c440043d0f00442c2540740d0740078001c0e84144610b200401124075981c10140e0080b040c0165001c1e41c2000403460144054006401d00e500c00c8080a0000034458006810055540016030303146446038509415554140706009c5c00c08002c44150111505207401a039004203040d500b480a04541c0c0380d2840c540da801c002904000c00c4542c413850307400c0b520a000070349900803440124080c4034941c00106131890003601d0800346003c41121a840390b06960f20450141500380b02e0948 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 528225053 1250 528223803 528223889
    0x909060604090e06060f03010b0f060c1603082a1c0306090c110606011103270d150b01050703050d050a1e0518120a0f0e090106020f010e07 61
    0x40c0c0d29403580507035103c0e0403400c0060b20080c07500c0b00900c400300401c0c13003106100340d03d0720010b100242d552030749642055005840c020744485041c40004c0c07502c20351801010a070380d0071940000c10001d080700204400d8920031980b1400020b80800141c00e1607681c505521250002d40d5200349100300000803640004092402260069894003190701f281c844601c040e0000d024400442850042045820340051007032034000040c00845007560740300c0c0102540c58807040801140151082e6005104030b40c00c040080c4080010400341c58000c1d031340c4050b64540c20543d400c01480038081d42c0550309890303050350540c84203440c110280002d81c1c000e0500804c4050420342c2c03012104143c00604500044404114ad4002a107042c6040401250092100720708455405a4203540c440301c0198180d618000351030600c0d0001e0032804105440c41c0d06010582a00480c40c5000050955400031710855095991002002240b0600c010148c4031502c501810080001c036201c00180320300c5005100607058001c0c84070b24 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 528226303 1250 528225053 528225059
    0x80f030712050424050d05011206060501090501090608090f19060c020c010918060b0406030204180908090d06021c091b0e15010201150f050901140a03080d021b0105090f030f0909060604 81
    0x180490780e00327030001d0b0750a161007600e40c0c04100030f621900c004ac01c800d0a10140d11880d00740000c1296801e07002d24010452214023081000c02d0400070100c001441d034050300c001c0e4881050b215105455004140c03440c0c0d09160740c1812071400070403201d0b6100d0042c3d5506071158103114288a451102400d0900655034403000002c0a03042c0790060b1001e4245030303a0145c1d94501c1c0c01c5407203d12007602d049000c4078504e842d0f04840000c012004035540d41200340c4004018107443d003020002030060440001c0e80790251201090002400d9001e4052103115198042002c80f0409040300b0b11400c1e4021070700b08000301400b09446104640041414184c1480081410b02d9640554050300680d0341c0006480d078500c1105000c02d150400007075000d801111f428080210390b00703000032003410083c0300241000c2c800280000400d4030b540c046030050f0303504021204034194131040e46802844100e4000d00180200004030030201004401c6884180c2c4440c0c24a041c4040c030000c020314083d025080c036a014104001c00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 528227553 1250 528226303 528226327
    0x5040602130f0f030b1312021e0105061c1b03030816031a1201181b06020604030c03360504061706010923070207090f0c02061f080f03071205042405 65
    0x80d600740445034050001000941d01c28880109e1528015100f80d0500c0c00704001c984a921000342c100300c1a80e2500480fa080c2d0820b04002c02c1c0a00c10208001010f41002c400e2640100c102c5008080000d8078148070355202504a0450318034110000b5004c81c800800c10103803411100e2103502d4081400002441c3c4011051060394003680141183e19038609003034560720802d0703080a88024422400500030320710b0b00e968014981c0456006c01000d10041076501c0c0010869040091640700d1345004110b00b05a0000d01900181128400d09104506080340070448103030605000a4611046004060b1030b401c15900e0400781c402500900500000302c0c0c41011403002ca07000540c0030301c280740c01410400f400e051140e01921200c4a102d800c0e5810030398440b191650000d0030591000c040c1c0010040759015802000801e101a070140d200d40c89610558040303000b000c40204242031081e081a8201c0120000950fa9401644030b540e411910b03007040110842c07082c40b400410601c240c41c105140c03038141340b05 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 528228803 1250 528227553 528227573
    0x507030c061e0b120a080a110c040c0c05010f06120b13120804051207020907050c010e0d02070609050a0f0e091903030b030c240703030e0105040602130f0f030b13 71
    0x4401c0d407140e03d0b40c1401040c0d0038845404101d110200c005803456810545560069100b41901842080704103500703010100c40900a140840c680140180001100358030000c0107000341c1c0d44107846c00d5180c80f004402d81c102c0c0e444ac4104a44840102c00520402a2112003141200808800405c044401c2650020b0407000440c4011003030b98035040450301342424124580744540300d07089000c1000304004005039071000e14040d0b0004440c9840343d80d81c46580505405428551011f440d54840d0801c80140b1079000314040341918815940c00310b590769100208104002d051080801d20030144a00b48100001e03005aa544440300f8800c84040081200341c02c000d011b840541600000e0b5985000d034446d2030240552482c0c92403c88043c918070040d41052003401c4c0303000035449010640001c00780101402a00007210358100c1d01d00801c61454a41441000796018886202004a801d000490041c05214110046e00c07140e8050b00801425035490110540003d04504101c0b10000755810000380071900b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 528230053 1250 528228803 528228851
    0x30106020607030b0a1a090d081b06041109062101061e15051e0706150506090108151215100b040605090105070602040b030411010e030f0a0b060103090c0608100e0105010507030c06 79
    0x29aa2b5540181132001d854007840300c0c0e1640c01c1030b00b12005000100e8070400000038582d608490700c40355521030000051a005070001a9682000c0e1449008a081c0040d84100d00b1200c10400c000803000c5a00d8256608107900d0044c4440880710142400c0b40c64822030241941c81a001e4030a54421242d1350030707070100d40041004413041c54a03141e045074181810940d520041100303491160415030010006440080e008020403482c65225403000b049030744e01c03c5c550b500c1003811021b03a071002c01c0c54080003512070800c803140030600c002c2c203400080b00c01e58201114100d0711079644a904140742203004407003030b40c48900c05480030340d020700020a814040c0c2000354011441400400f1a200d401d10000d0100120924000d11035003148100e20103041020a001c4074282d0700041a406603514440181e0040503000c801819500c12803c0100c1e401e5003001d003050103a6040d0601e808215991404846e07043d2090240c240011001d008440001f0f004003804070196100f200089808941c280c000091745c04200 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 528231303 1250 528230053 528230063
    0x30109020a090503340e06091b0d02071208040302120f07021003090309090501081e0f0d0c0b01150509091306020d0b13050129090a0b030106020607030b0a1a090d 71
    0x300d0003030798003448441407005c05980b01e9440c4032241c2c6040710085107103038000c2181d805101c5000000301050301260080056846114240c0c1d19910300c121450025000884100ca0321402c452107055450b000e01c407100e124650540c01031001d250a030405484c00c0d0071203410205c0008040c014040117030b581c0aa40151024650750014210f52076042c0140749441d48d174804640145041d0052052a0ec0410f06000001c0340d03c508503000316080c1170461034540380e141c640d166801061074540b00d00354070440b105541c034000c055800141e40c80d10000c9041d08044144100403071001c1000c41420b0030121141c66000070140100350303540e12652500f6060764050500300d6207941d942c42da164142d107841c0350480083c11007503100704000d41c1028640c0d05c110b030b4a1940703082001103611403a1507004140e81240d50003070b0080c0003180010758480e00303004c0350f800a0180c0c0001d4042e042c00903d90a11910400034030640c01480700c041c00d860309402c6000f0455404c5102c907000720400030906681c80b0807002e41e03000c138811 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 528232553 1250 528231303 528231343
    0x160507030f050c0a030c05100513030506010602120c0d080405030c010e030301060f020a0507060318080d0203072c06030901090519020f0117070e04180308090d14030109020a090503 79
    0xa03151250611105030040e6115031201c0d501400880d03103207004c480c25181f05403210304241310110019103040c0101a072026030080807490110402c070300418924100d03852074003118582d0040c1d1340c500d20b290080c0c42d0162039581c400e1a01809051141c4040754015005070180c901e1b02d9400a810307400d6a81c00740018a15620000c0104003440e03203c1110040c841c828400b422501c1902c0e42c8994452065100e008100742c1c03034542030160320031800d0405c08030744e5002165607171780c020b5000084043d400c110380d5000802c0c25100c0c62807007e0001443d41e08a01421040e041182400304104200303034101400e0b4281c20365070b50141000081040020094001c4034101c10141c44040313204100c80e8828142149041001403200440100c44480600380c2042d11410712101142168000c2801400199040544116260b2a6406050b0000750250080154074140c074103000802d1400e8460109845182103119005c000404c4444800c3d405007845802c01c2c60110707241c0ea541c17000a4035251040100c0d08001c012 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 528233803 1250 528232553 528232583
    0xf100b0a0b18060d0f0c082d0a0518160602010b01050319050408090301060807050a0807080d05030a1104060f030e120702091008120a08012702090f0a062a1716050703 73
    0x101d001c101a400355041d5440d0580323994840d61030302c004014250410a0b41c43e580400c1161001c2d190303074074160301008110765003e10100950103d4941c01d104800143d46816000d1105520130b4080b00c0c454402004401c040384203aa03800c80042000420580d05401c0900120840f59402c2c01750000030310300d900040850030306060070042c5c800c0d107940c0260078070750140e641000b40460119010540903441c0c14190303200c0c0e03030b03404c108400341c4500000c08410300400503004c03a140e038210b88484800b80541d0740c02c110f04030303048915a60b214041010041d42c500203022050042c940b60b400130350300c1190700083c1d40304503a6a4280c0c0303240c00c030a83d6420000c0c04e808a01064140d1b40580424011f0007180c141800d0529a8552107107054107001c0701c00701d810740000e5014070310b1311614010380a005014103288005940c03080024412120351800303404183d5121450350300007100103584a0499000140a4110700121a01c5849030740441820011406170640103804900203006100c02140103100011251131 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 528235053 1250 528233803 528233821
    0x15021308010605061321061e1503020303030610030f0203010303020a0201110a0b010b2208010c0306060302090f0d0c0b030c07030915080c03090f100b0a0b18060d0f0c08 74
    0x4440c0c00240c00307104c05106250800208290400c01c44180584030114020b072030b4000240e4080525001d03042038180181da03c03000980344041aa0035034200010005203507100301200e1303400c1c850f10000e5495401840464514505800f640c044441c56041c0007581c01208200c0c8000da8009034410350240e000707075920006558006010200d89411b800c05044002d107282c0c3c4105001c4410b004074011044042650100d00c0a0061464800300741021840c9200b035665440d54040c2c0107400308900028113244d0000303180c3e400f07070080e1809941d005020528080420b014401e011010210551704a07080460001b15000300000640c0203441c8200c40a50310709083c00c0160492140742d200c2040c00804031115421503902c800c2e019044802c208550f075881d01c400740313610302c3c00d8110b8640035180c0c00b903406800349920040c2d0000e1407410003a50700d00c210310341d200c01110482c00761580708882010043c0240381189490001011010307180d0400103080103a01445900700da000c003260901144200b02881907100c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 528236303 1250 528235053 528235061
    0x60b01020724021917160615082104090e01061a0414100512040c1d01051807080a021e030c030a060503010204060249170103030c020d1502130801 64
    0xa400309940b1603100d0306030b852001702c50b10b8820500e00604045008005121503411810b8000d400160034400b00d1032040c1c64005c400500e114000080c49030619010204452105814225200c10a041c0c1050300d04502900a8a07504960700c0c020355a42201241d0755580d10300031149003a000800c0d80d10360f81001f000e19010002040310318802d00e00402c9142c1d040303620604682078404c0200105403661039601d481c05050102d1781142e81c2509050b0030103101c0721003141c1c220381264800c48480c52282070301d000b84108658207481800024450000042814909070010300c000114003880c0810310000e0002d55080f0b4000b41c0d440c000c041c0d0b0020503c0f1207006503010350406420114002c514180c542880695245000c076890864a03010b2124a45403540c41c21910b10003c4011940d09030038411070080901c220050340c01003000c03915602c0d00300b185200c0034104a0580c2e606440e12320744450240c0030003403e801c00307082c102d545551282100001c46558005800b12407490104008841c1c10b284c0c46909407 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 528237410 1107 528236303 528236323
    0x60e010e12030703080c0310050d0311150412030515130e0d0c0b01081903032705010c030b060f04140a0306020a080402120a03020a060b0102072402 65
    0x100c0300032000f00b903c58400e9482c24203036900d4200c03813406400259900450308089010500180c1000e601c001d03010b5001e410462000c8040b0786289180030b800000040000a040062000b00101031401140f0700029003005d0025141503031201e040884035601441c4241414450440200500d9020104003841d05040c0c0d50200a05d00340504030700d504900458807270003040b000050041c004510404484940000c00c1400b40c8591021000b800000700c3e1104102c14074001102d0a40118003c030200501c00d000106001c02c0c100700142c02c450285011a0045004000d240c042d504000308a4081c7d40c1c40b110081c0150031044003003001c8002d90f4000514041c13000034a88816038100e00451312803031003214003041091340344540503240e0074800001400369110020700c80000c1c5890f04445244441071040b40e0745036564104007107403080f40b4900101800600580c603034007240d05001c400c1b00 = true := by decide +kernel

theorem cover : BRFrame.Cov 528057553 528237410 := by
  have h0 := BRFrame.cov_init 528057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 528057553 ≤ n) (h2 : n < 528237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
