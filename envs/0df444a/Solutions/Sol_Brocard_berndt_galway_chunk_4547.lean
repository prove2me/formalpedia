-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4547
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:58:36.887979+00:00
-- url     : https://prove2.me/submissions/09b36e08-58ea-42ba-b0dd-05922b431b18

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 817625899 ≤ n < 817805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 817627149 1250 817625899 817625909
    0x1009050a0b0702100c030c020606010305090304060c050307080703050703090b090a031113060b0918061309150c121d0a03030f39050a0e060304152f0c07 67
    0x18074001402241c001c21010071281c3c000c080801c000c41c440c1400400800150b103070304c00180a0140811507e40c440d01070640103403a1180034510701468000203a03402c3c10003241c2214540000d00481c00805d00c01005056a18065100c0650321900303894010015030058000407003165040c003400700c0341d44a40381c1d010203690344400105561041c40e00011840030100c090003100c0d80c108100490010216009861304034020f83e414a151402c1c00f00007203511001f100c103550041480880c90103010241d400103c1c03024040c2c0030706500070000c03042003004d0380c00c00780107140810f040001085038001d591180c0030000c1ca907686445107011303410784d481e512543d91a40c040d0800d604c4010450b54455503138400504445c24080c108070301040c4040a00c45401d00c0466a00e426404100e40360356203005800700c60100c00250340d11880d001c405020030074550005842614914a101c1310702d0500400d9204064010880c0b0392070f00d00c0c0c414041c2d8403400307800a0b440141c00120041c000710f4009000028004140c80c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 817628399 1250 817627149 817627163
    0x9060f1f08180d14040305010203073915021312171204020d0519060f0b01181205010b060f070212071406031b030f0711060f0708100504021b1009050a 66
    0x44c4d190503141980c0a075030409411540700100f4058140d400000c0c00950780c00040c95500100c061828907001606c0c0105545d4082c0130300351a04000440c8200740606496000000500f4950003010211500c0d11640044855500306c140600c103201642c0240700100d16540c85462400c5890384103a0f01c2c038030020700001d0280a4001d111004c00109216100d5003540101112044d25054100035000c1d20366004100d209514050825805510030b00c1900c41c1c200012449943e030390b00d00135003003e6144507018143c846550f240302c103043c3c03030341c5100091150b128640d1110b501c1c0e00e514010012505196076031142c0a620010040007031903d403d82c0c0f07003000803080311100c0e02da5070784006a0300309210300001000004000030400000d000388180e507500810840d43c4004408a94118140c0d640d40309450400350800c0035000158054812241c1a43c444900c94040d1903a9580360003088c160b0b04400e900c1c2d640c0d502401001040f40704d003008a0704061100c0f100a000c5410682c41701d64690303035140c03c040c00d0f030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 817629649 1250 817628399 817628417
    0x90e04030903050f010b040e01020306090615090406060806100305070207050d030507060203010e10060305010302010e040507021e061501020c061818090a03030f021809060f1f08180d 80
    0xc54050450a40219000010307980d0000e0f64803511402480c44d12101d0344258600404094403032014400d0742d00c145405450a80d0715118107007000481c03a10b05040099200d4100111680b64846010f030400821480d15840510b040101c200404608150a010101345c500010040030950006a04040303480a454582c0b0881c0e0509044035540306909000e1b08242c00040001451403031a0803180c030455065044600c12512a60100c068810a00c0041d00064451110880b9864240e00c0140c0100107801141c0101d171300104007000b2040d107011030a00070340201c0200304034820b10b0314140382e6000091019003010f2031000c0000f102401080500e00c0007010112100610340c44011500b24045180c4041e10741d14508542c00c0d50b55409031400441c0040c0c20190210403014242c001d69800001e500344421500c0042c2c418058415001803c030790b880107505d410302417142c4400b400b42030030f81e200c0c1582d02c08100b13070b80c10b02501d52000a82a1179140c9030042600da60a000410703445211a0306142007011 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 817630899 1250 817629649 817629653
    0x50a020708011d01060608010b0306042705060405100e03040e040c0b18030d141e1e070515060310020901090b0a050904050f13020409021c30090e04 65
    0x54a500e81c1c0140c0c0d41c030761910342d075050101a40041e2a00c16103005000f030040c0c07603d0380d40032120302c0c03800c0c0b103601040c0c0310a102003006490142c0011040384c0705064002d492015407140008101125503003a110b1750064828042030203402d001201d9610380504061090411024455a0364403d078070800701d501d0599004201040003443c94100144806800c00b901c4603042c9400c01116266514410712071b00c15801a040b80c54040d266a00c24407503403000746030034640c03490302d49203604c030300e01041e0007a1580800c104040550b40010351011100380072005a1100d6080c1b40c45440c002ca180c5070302d4075680c003480400480c3d5030f0006070010203611408015032070300103030300040e10140390940140c0d40c401408100601318560040103002d003010100c03018000354890b400400000402035801c90309000180411034003608054003c5615a8800f070220505040b20315208038940c91030721421134017101440c0120600b1541001c00085645000b0304003000e000102d180540b00c618184540300001c1240b0f400941 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 817632149 1250 817630899 817630903
    0x103050402130c02030d1a0904020618060d09020a05040509030f16150f2d020a0212040308090a0e07050711030c09010311030f460b04020405090616050a02 68
    0x403084106030240300069503004013a440b90400c100415031103180605150040c844544400d0040074050311900d0181ca6075000e00c02154880c46428010340e030500ca240d41036840300401040346042c1a140060340c401240b04118411365107510462140e4204424440c040318007001311507074401d06080312940c88920700c920310488901440090180e030008009100d002155030000011003103049030802c80e0f506825400500c2c003034512030383d8104807000c0c1c00c10302009286500034819001d03580100d405800140c3e040102503800f5030412900d08502081110f0b403030421402d044043d02d281c9007a00c88500d00003800520502815201030459050342c8150b412940302030007a43d5070500d000c0c0050190352b842c0c0c1030a42c92507074004e03500b60081c492005e5a004589010071344803120054a400100c00e40340710705099803512154407545040c07000c00e00341d5500000307c0300da0804030103101d6070381509146032a004010841e28020205491354200d9801c000648905a6041c6002d02d01401d0054a55070070705001c034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 817633399 1250 817632149 817632169
    0x30e0f010c171f0b180616050706142505250f030b0c0d0204050d050c030d08360f0705090105031507052b0f0b09150103050402 56
    0x41165282903407035a50982d000446035251140c000389580c590310782c40300100d403222180400c030b201d00749524800d0025040203001022018030000f4a201658010070010b4029407003003509090709041c46440204101c01401604001c0071182400102c000c0081658000f03842500c02c446500d01019000d00c0310280700c00d401c01c154640010880d420300060302c00d00740d403224054100c1d80307a250440d440003403030801004c0a00300792a84450b2182081c3c40344005000503402501a175030f8915002d100c0450b458403510305804401d4055001401c9410225062505008191540c0000c0100d01c10030800f03941c414440c24500c45c1445080700b940001180710f04905040002507910131405030100200c0c0ca840000390900035128100e0b03500701140d0380c410070580c2c0c400841720a00c140304007080000d0782d00e600400141806440654a010046550144a102c050314100f46100030396910303000910034030701e5449031394203000e41500e0a0185003404141c414000b4090043c440c101512a400079045468a047e60 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 817634649 1250 817633399 817633423
    0xc0a0c08040e04060f0c0f0e040603050d021605040c050406080907261504050601030b0405160303080708090c0102073b01080d09050915190f080114090c01030e 70
    0x540c90719101d6920100c045070581e800d9030054100080c0071540c01040c801c2807000741d82e640307900a0500721550107171103044240d203a4581c0b107640c640c800404618213104c011140c800d075502400fa4031152541d4507005d02541e8004900692502542c4018242c00801302d03010303903c80d424401000d03a100800281351401035080030064009290b4040ca00300c80540952000e008008151501c0e40d91149000140d2170701210050019440040100085540d60035000d42140c0241c0c01d03102d4035441044070080b1062150300c21070010f04200100009c040c0e010b125960010a0240601204800400007c0d44da00c0d01d40070b002030078070003406440302828810308a44010001302a001b00241040c2040c00b0180109218001241c041c030303200d01010902c0340f10642e003500c400030200680e544841c08095040c074401d40c940c0740c000d656603c041c4904a016410500242505119210b20a04044d921400d44040c042004814064442480380c2207802048401c1004803e181c00107051581020407440c09181d1412 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 817635899 1250 817634649 817634663
    0x80c01120e1e0106060806180c040e0c09100e1e061c020a03050606040812030604290a151205060a0e0703060e0f13023709110307080c0a0c 61
    0x71188110204070000e5004040b08402004840d40d140700680e0068400c80790035074072008a0b0b8441003010240f80c50a07801109140000341040d480c0c06220394a9001661000191a0081041c1c0c00c1403802040341022247c5030310f05240c2810103800850314215544108404040f50f00380503181a440b2001a0784500b20444100c0c402c1104805d00c0702c0c000d6100e1032003240040e04090029850b4140582258102c1c1c2550000380107607108030303482c9810303504040c04269100ba22904110000444002d88141c00200f001c80c64494006403000c2104992143d4001d842c07555400d052641400d41240fa80d05116030104d6020503241d407007a000500c102c561380c2224000409500a00c510b040d41603101d1000e40d00903030380f848410344900c030384585158411030702c00d0340d00b00780f2100e940010308084110000191b5001100308440c100c0d01c40d00200821002c042202400c011403080140380d8240c0580081188a04441483c60404004c001c1480c0030061042100d44000a2300101c0c0780d01c100c0c07070b00c1240c903000f9075 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 817637149 1250 817635899 817635913
    0x21032e0612050705040f03110621060307150504050d02030f010e0d0e01050f0304060216082b091a040f06050c041706280e030706090b01060306080c01120e 68
    0x101a1001d06610744141c1080c0c038002c00514841e0080044034140c07020540880b84140c03450b40c0d45803181804900680c0c205000b880304100c03000e820030241c5628029000706140070300d8641c003407601d071902e95846203501c411000c6400403115042411201501c8080d9100c0046400c103001091600c0c88280039445250b02e820b0400c42c550074080350b89890480107968240046030310200464080c01007007007400310702004001087c0007540c2c0d58014501c502c4040c000304010140c0b0780b51500c0e80c1c0c00008a10400c080074410b404410600c6034078210b80381c55005401c12101a0390744a1014103821495207210109103500440c052009589550401d95405038051006241058104440da0440d1141c10308200002c1c14100c41a0000704401c6c0c41022140c0107540440c04c0300403e00521605074980940041e9501c0d0f0b5044200e1043c801802258015500441c2000e140c2c500203a0120059012504251402030103000759000810356001c050300034a0401c6083c030700f0f0a0008010009058084c0051080d21 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 817638399 1250 817637149 817637159
    0x1a031002030105031905061909140d03060f0f0509090a0501150513230c070204060e0711030408060a1e0e060421051c0216110321032e 59
    0x2400440c1a5001542a85e03240615108403a94900051800510755040800010b00400a10842100752502c0d6040840d0a15280d101d10504501c81c8010901035002080e21641b5650180541401481041e0b0f4200b8540d24205651801035542d005040c4a414031401041c1405030410142040580100080004194540078070307143d080544180c0c0d00900c119a030500126a8038483c1170040d010070004000800340c00704e4200342030407005202607540441444244056225480b80070003500703001d02e0001c1282003e10016000d4501292039980c0381e402008248414079003c1003240e00b1507444c542c046501d45050b1418949107035085901101d003490b28035005940c0500040850080e405440108505406050341581c04910100020f020400030400b41541c5441700f00c015000f01c0001d0001070034000340448c56142032410b00c10a464003a21405080c0091400b0b019aa88100361240b00142c104210f0030300314090301000308451040c601c0b031070407507031849002c2c000406504d40806440c51038035103032 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 817639649 1250 817638399 817638401
    0x71a070c03080d15060804030c023102040f050303042102150a05030a0b091506030604020f0406020d110102090d0b060307031e05071e050d03120203010306020903010b030115091a0310 80
    0x420144413183e40e5448000800b5401002d0003401a901942c400004043d15001c0c040070344030a0002100040e10301841c0d10346010140c035018a29290703418007503074403440c10020b880c0d5203a01ea0483c51182d08104010003250002003002c0802c03da0480044605d00c05500003e11a1071400703060211706000000c01f070100c0c07640000298403845602004000712034480051141390142118100182c102468100311700b4601071018607440b24004001520b490307200c00d40100190020340c000409a0310000b071038100260407030700c0308480340b0b43e40c0001c508200312040003505503080140080c0c14441c080300866a03688040c00b019019540140b442079801260401100300c0c00380129007980c0c1800f40384004030340b40c2610100c1c801e440e0707806d540b140e820900b04010024217490481084052046220301c10f20036140d10300245000394083d590040e103a515807402c3c1400c2d11203d4101500c0384e490111418590348408210307009440c0e01c40c030000745101040e078440c1040386e100310300c16601d40708041d0032a400980d2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 817640899 1250 817639649 817639661
    0x915030228080a0603150e1e0105040b010902030709140d020d030e120714060c0f0f030909152409060301030b011a07080d2c0618071a070c03080d 64
    0x902c1d0b03a40c80e415511200301808490b1540402030102011900300541002c00d90444502c8070012000c0d2500d8400e494401003944c0c103c000403c0059440700c2c204000d02000e41200c0340108540c0300c0543c03841c0390440006101c00d905000d000e5200c03d90400340002516444030038801580e0140000e0744d01e01c00340c18082c201ca9054414148203a0000e10f140b95502070105180045800c200980304071010080104113280e00007400030b0320503104401c480d91a680c0704000c2d004651040074095961041c556060120201c8014100d0200c00306034030055032941c842190b909090043c0e403140000800050b08084c0c014455402c40f2640f101010002005109030640014101c680d840040e110513000589070012034051008060202442440208221080d541114201c840390300004505400c030b0807101c040d038011503500300d88030794041c80401040b1001d86429079a043e401200401e84240f03000000040b10101c6c01c1a06440c1d074000c9003550410039190405005140e100c0d5003952100e02c041c9595001b020 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 817642149 1250 817640899 817640977
    0x9030c08220b070305040504091b0e09010510060f20010f020904060e0c040902070f0c0909060609050112030c2d030206130308040f2105040e1609150302 67
    0x1c0d034600008030b82c5a100c044600c6140d25495042c141031030403007040300910f4603000135284100820208440d0055107503610000d0b14801d0b10302421410040c54160031910000d211b0840c1403c041d0040c800c00390400c903100302c0e949841c90030044d25015a403400501090502121850390300708031150182c0c4c0304070b4002d40081c00d001d0350200710382503a6030320700291203209403500c400d1503108000904c5501d02e01d4005045c000d0041c00503291b90700c401da541103070381c9000b030380b03d10481030f40d80030b040c000c109031405a039009180f09101400a941800d0019201d500c400a004050000e80000c050420401e0488a0f10f8a40c582c080c1200040d0744c0140032214020845048006014200024200000010284010319010340c2c9104482d9101c4d034034103104408030f040a6403e0402c83c401a010000c80400050011540b0f56a00b80c8071458125000381e4900094000b5001d144807887c00e5003035036400841d03c0c2c01c9035498550100034600454060b0003c0c801e0380b100303010002252461561011101d000241210 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 817643399 1250 817642149 817642207
    0x140a0216080a0c0b0a1413030309020a0b04031b0612020c0c0301180b18031c020c0d090906060e0630100317130b030703180b040b0f070f0309030c08 65
    0x142c1d0360b0414000f11005030004e20400c11003000821071f80f0b41c0242e8080c00d09031107414006030302c0b42c440d00043c80b081e00b030b940140c0b0124400242802000420f14225504042d0581d01ca01040c0c10050042c0510610483c24128958041200300c0050000c00040c80c400a000e00200281c2400c10b14101e14818010390036070b50f000c60140801e0152200d8904210720401e00005107040c0202403450f081c0300400c0e080944543c175020300901e4445d100c1405240305c80da2140d00c030100300320300d03100d00700c4140d4007142e1203041841070712801840d42d920752030708aa02e080c8422003501d40404144056802d551800081800044100400c100d0380800d4901554140c0c0d009505041c900b1300005211401c502c03a4981e001c1107410b040c1c1d420002150100040d5070800240d050118030704440340807001400d040000282c400c1507c0c08240014418041c01d1107411440d030040061191502031006804241514002406c150b5210b04403410f06110302d0040ca0083d90003064255248500030031569040c881c42580c40d806 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 817644649 1250 817643399 817643401
    0xf09060209010e240904020f0c0c010e03010603081b01140406020c1902030a300207051206010303050337090b073e030406091404140a0216080a0c0b 65
    0x1602d440c07004200714001c13a1a8142d401c00c071900c0c282000360005401a60800d03020700000030881c18000c0540070347e0407401c00034040e445002e03000601095042c45402c0c0241d242600503c0401d0450080302d403c11041650102041108480c0754010070340f2808003150071059100348020809150024000481c20030b0450f400e8810541002f0b9140c2c1600b0002949030740b004150000045451034404a001030714212071000071800c0340400d0040c01c0341d01443c4010780003481c0500007403501281c5441740c8a134510084c00198111750b0302034154840540809862400000004203d002140c3d00021003128000070b0f24030031141d046100040c1081140c100c9600c210807000404851007118861258004409120046148205400c040499658141c0030200404040b460a20707010001000280113a0f40c5030100d0320714140e01910810300000c01d2911590500146c0364544c10340030764640c1c1110301d5401c0140e07103624400602140080c40b1780300400549010a8403c1040d411441c50003c6c14000c090130f9043d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 817645899 1250 817644649 817644677
    0x12050718021303030e042012090c0109030305130b0f0711030d02301303030206010902162a08100c140a0f050c060109050613021c02030a0f0906020901 66
    0x141d00412407010302007101002c042000c28403d102020f220301c00600009919030410410003100141c410060f0490b050006020f1b05004003411100e500c002d150000e080301c4c1084400091840c201403001904100010502c0a941d0040b00105801441840f5100e5a12307540c814008006400014040d07c008006110003120390801241c61048011141e018048c3c2c1900342c8014040950b41001a42d034104d014410b801400e0000c0006142c1c0078410001c0058551451030f00a24001c0160458103860b801842200c210110414401030102d910143c450801c2806080742214103034081003d01024450b900d0004401c907011460101000404c071050180b40103800064918142d04401032000080c00c2040e074115070702c81c294100d10041145040c40c6800a2070030410f00c0c0c002d007a0096500345950f002030000c00d00d08080c841e4124042d144040d410442180049014035448000d00d100fa2038001000400c05e03155030348a606206502d4208104d800800c2c200500207401034408070340490030b00241101 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 817647149 1250 817645899 817645901
    0x4091e05071709011107050a050622020d1a0a0c09061404030204200c0f0c0109381201080105010603060302131113170c091b1312050718 60
    0x4411641525401c81046800c400d208850000a08600f010755a4040c03004881c03034484001d016080c020401401240010705119084c510040c0c0400b10724030318400311507140941c0f01d81d11454260102c0c0c01407114292030500541651440c0000102c4880c04803c206490085a20040002c841c960311030347e10301c2d1120020ba0b640c080803480010840c03400e010400040c07400e030b0410098511030355a40c203c2948402d0210195030030a0300c500c40c081d00049075401c1c1044003007094854005c800d20384011600d1504038600b04606c000c80000b22010020804180700444083c081e00c500c07240304942d1660303482041e010095607030080c00366504a50805000180350340c030a015440a80fa001070508400c0344040c40060014600c0070f030400d4411806000c110310f403003201000980180178102d0b6024078803503010609810721041c45000707440742003000280b02103018080c0105003141c2d0b00002c61660f84440c0800c0d40c54412660780542e4001036201003140c02c22502040031000c94186114504801c209042030b80 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 817648399 1250 817647149 817647151
    0x19170d11032a0f09030c090c0d0c02030a0525120203070b0a0e0d080a090812012904050d050307080c030901021605010206040308060d02120d02240105060a050f04091e05 74
    0x100b8501440f00c200265103980040c40301100050498280c451010007003403104004580f00c4188030400b14202e001035081d80500c0f81010080e101075450181c0804002c0d2240c0070301e00c2c0500d40ca02d40390403402c03140720340421700034512a00116004040e4242c0c450081d9290300c0703070340100c074043e043c900820542c1403140038207800920b02c41702801c2803c2000c6001c642ca040002c143e00328143d103c501200205618500074101c0c0440e402188040b07604203490302c3c050b11000096410843c15101046a8060707503c0140d4041d160110342030708601c034085c10300c0c46c0745014820002c0c0000a0025a02d403501000200404c89818203800759401c0510b80205403658108600c82c1601681002e00020700007449844e04d41d0344144000c0c20000f1040c1c0c290041452040041204001035005024418145404000070b08070101c00301103003010f2118081c5001c0c10b980703041c484d85018003008507011103143e0051055600c4c10860101036501d9079640c59544000d01300117407014000d001413140421030710b40c09000e85 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 817649649 1250 817648399 817648471
    0x90b0310051b040602010f061215020a050405090a09020102060615071b080d0c020a0b1c051b030f0103020f101b0203030c0f10050919170d1103 63
    0x60000e4802040000e400350800a04464540c540c480400307060050100103003019120307035800054554a1114130000700c41a540041c8403001c0504450030005607080d2201d50119114480540c4ad41030041d401e407118010341c0c00c4540d2080c690750800c0b510181640c88403d00f28004d80c2110320a45130760b401e00c042d4200c01c40800c00014000c00c45940030401c06107080c4144c051816041e03d0550b540d400590500055a1210000a44110000080d0314240d45d180e40076200303007aa0945805030b00c3c4d9803245448206442d001e8030b1900d03480040c074101d01d05100e1310b00219540e800aa42c910306000e2854001000740822445141d20f04145405820801c408840c440040e031074010390b0005001450140c4850342c0300807a0b040c03004000902030003200f40800402e0500301002000b500f540c0500300f1007600d00c010441c10341e99101c1c0341c120303090550b9880e81d01c0b002a00074240d4a462041c0300703110071a6128a40081807600c1c1005030810380303442c0e242d00642c803464140c81074110000018031034000300c00300c01c064 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 817650899 1250 817649649 817649653
    0xb0d02010212071704030501090507050603071b050c040203043c020f0f2d0607030c15240e070f0e0f041e1b17070c050102090a0308090a090b03 63
    0x6500440302c081c002040d840d805140d4064010b5000745601000780d00640040319a40d45a9030705004016080007024080d00307045805606500e80108000c2c8010810742c071200e00c44410303103620414401d00788401d100c845070140042d50340386411705200203e5420381e0020700b039841c084032905500405c006048011000d00b03241d1190043c04540821641d02040f108031544010006440102c0b0b640d01d242c000c2d20031004480d09950405002d084142c841021089280180810896800003c0d40402c6010012f58484202c1030308041e0843c1000c020411451022444100c3d4029401024800601c00c8200d070946280501c8964816404480009001c2c031281c020941c089600320b5946800f000c040b107418030281002074002e0604100d02d008156900104204a5940005d9808000446a58002030049060400c0071003000401485840c40c010a81010800c880404004010702034048540ca0140104040e20050b101e06040003260300495805106c2c0490300c0001030000c1c1e56000d20020020b000700 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 817652149 1250 817650899 817650913
    0x1c0b12031215060c1b040b03370804120c060e0d06020901110303010909050601080f030a1202071203060f090e1203060f0306010308040906410d0b0603010b0d020102 72
    0x7046148580d074900c2d0140c2c41901403107007103034039907007080782c40305914800060b00b00a0580740e00348000c840034802034500a070010300d080031055481070507102d04a00466142140180304000c0880207030700c0e0200090107050001000145030082c1170440e003025004505090740c0755030300d0405968246500d039000f17030803040021200022071150360140c01d50075018100b600c2221006460380741907500036040007035043c1e5140414024000200f0006024020b138400900d0000310381100d4aa40b0701589410904000700b08684805c00c0d80340360162003080758002d00050f20030700c5041d4080c0241141d4040c610061031114400911081140101b0b08104800c1000e0300b80c581044c084000685d0004084c5504a860607a44540341d4900b004070034001c5000780585034655080c100400e068583c0d660008144450380c0098400540700c43d0340001702e140300900444d610a02c4440d0f51190f0201c0104030940c0300a402c1110340038044a80040c4d441050118020099070301e05000304621092030b048081d0059000072 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 817653399 1250 817652149 817652161
    0x80609091c03060b0f07060b010302090117070c021008071112090105070204090b010b030a05090c100804030306180911030304060c0201050f070f0f1b1a0706021c0b120312 75
    0x24840164a089103404200f030303500d509420605a2091460115040001030254184050317403140e2030301c5071800d2a0640c6000c0404000031300340101030143d602c0e9082d00c0c4020881280c01181480307001c1d03501070408c1000d12107900c000f80c00300720129011004140c030b440c0d01c0c0c8000103011503010003001030082c0081c00c0c4060305004523a01d030401d8104a030401ea43c0c01c05000441d50745075405000b001100c0b040c60382c901d091003868066640c0a0324060440d80900c80300f00c5c15039034504401d08401c040d85000c404541d501d040c11405444594802c0f0700001124441907204800c81c0c0090400c58044c0c072015142d80000014151340340b00b0b920071100001c030f0741c40144c0015031140d802048114000b4074624204a01615042602c80344400c0440c2e203a00300218000401803d0391071020505c1c88034401500d10740c90845014140408400b0004480c1e070000303a80803c0140f030740e054441e0780d0204090b01c0608bd100454800003440c00b03215442c030a0305410340c00140d400d000401c880c0d03d0b290800c0ba0b0300443e1180 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 817654649 1250 817653399 817653433
    0x305040b0c0705060f03060a0f0803090d0201031407020105061008010e0109020f040314030a030f0b090c0c07030516091d121b01051e1003031704050f0f060708060909 73
    0x7041445145006040c00003600f5621400584049a10750b0502d81d580d0030041c04001c0c0020081d40901c00040d2030120421200802005036034008506550320310704002a480124000c0071240f804103200c02404007844203042d4150b00040c41004107640318a403842c20082e0565040400341704000b01401c1b158014400000e0315000f07403198107c1c203a07040b402d007a126500e0301e4012040c40507014842d800802d049003c250325006031507000303c850f0400c110840901c400704190080c010a46000f903000060b001720003400800c100c600440d000402c1c1c685032440030043c0141c851251040420060401110f00082d661410140785410001002440380c074001541405541d0040c0050700e494100c00c201d00036103c0c1d000e01030320780705024019100d80390f0242ca454000e140180900040544000d0780c00a03c0002d030004240031605201c550b00d10b58076034503454071030720f0b0606030050890140640d8213041c41c0303003200249a078020301981c1c0b100801d0b56904410b0250114040b10100b00702c1d400b00004030540841 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 817655899 1250 817654649 817654657
    0x1171f14090123030f01050906060d0b040f0813060503060916080714040e090a1205040f0e0606040317071a040f080325020a0b060402031b0318011104060206070c0305040b 75
    0x68054640f80031811440064103240e460852041165100d03002c001a07098240310240e40000e044a1440c4100b50a07100d62812440051005010000d020035075414814284107407007001c91002c00900105885441c0102030b03030010b8480e140545612030204450b640b03d821940102100340c1c1d903840311540ea10b1402c40f1581c041c480a140898400c10010030107601022015100307001031802800a810580350182d200000c03401c400080000501003800300b800780340040d404944111000f44225226900003400d80d1085901c0100301604a810003050b40820030090040c0d60300a00036014092041a0041480c030011100206074042492203640020030100c00b5540022800208503c0d00410040825411710000341e804003507440a0000c40030411580111030380618165411b50450030002040850107415a03c401e2003500080001407101065035041141742c5100f070002d1010051f0b84003d107240340c2c41400f8150050142c3e00000d200300c0d020f45003800450768103503511807030b0601d4145200147d801c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 817657149 1250 817655899 817655939
    0x90e0c070b130b071707020f0d0c02010e0607120801081f0e010b030604140f15060d0f1713091a010503060301060f08070905010806070207031101171f140901 69
    0x5030080c020000700e41d04a28491050889480d03140c40301c0d207a1411700b9a80b0a0080410701107500404445220740700102e52500c0d0660a401c00790203149036840180d521a8000c4421030304100e01085907805c1c0107920204a001c03281945548076540d8030b400d4456150000d03e40c000c207180201c03402a250403d030603400301ca1080c0b10f180001880301842c0c0000707070070200305a400b82c9403007000d40f008042c1c0d83c030140304400c0c600242c60300034074a40740c6110101b00c10460082c0040e105900b41911303c4d00384118071010307802460740105c640542d050307c0000840c0b50307001920850f2526030000d10101d99611300e4410410307516415880e40ca855003240004581c02d61006003002e4142d501c0d110005480540f502c007420191000c40e025000d601d0900254030b04039101640311801c1507206005000b42c454001c5081d006523600096020fa51290000041e122102c0348091a10440991400c1040c103000c0341003003610100040d004030034960b03540c2103034002a400e1803d020754021604c1e00100701c0303508001d00b0344080e00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 817658399 1250 817657149 817657171
    0x7050304060e01090b060310090f0209060d051e010605010903031d190b211b0a030204230f060421054e0406030c12020a02030a090e0c070b 61
    0x10182c180b6903094074200310045400c0040041882902c1c9420f00070140740c0c0c450154108203050031620760510790085900064003524204010846a1300d07481102c4505640000c1110340c0188461031121102401d00d4817015a540f03041e402003000d40c802c0c1280ca003140d0301aa01d403040c0f00c1c010554460a980c4020344254446a401d034260340c44002d8000907c000d04080324115102d00440c000c80700d2610300c18041e000161004000c001304030303c4040003507000320704114185850300d0145c0825002841030b60040d82d030031000c1141a40c2010028000e144c8400400d41d81b00b40c4010f103050510049004a000d92001c880c400380954040c1c099150035405c0090080c001c607a03594040e03e03005108980440d01c078088000a00d0b140c141207080d40400a415680e00f0790019049054003080d10003940980c0c0a01010140c8070401e004140303100e4184080302e4520194215955901c40001a6980c0d116022150104000e00400500d0700e00020b6050311800040d487d503483c01b5081c0d55141c1940c40002c01080b854 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 817659649 1250 817658399 817658411
    0xe030c0a1226060925050406030609051e04080403061107060e010e0c120304150305010302100f0509010323070906030f090c14060d060801360209060102030403051002090a1d0705030406 81
    0x981041d4644049145842d140d5568980c10032380010250740164108a100e28107060a100341048041001405010800c0400581d42c41302e11700b800e80e40c82958001343c5020300b070040d02e105080350700d401003508500c40c4100300009409200154207031011090031701115002641c40108508140c0b40c910003c0304210103a80c507194407402c0304400040ca108034180002e684030014000c50400088488081a40d030a0800c20f0341c1003860024014415540340904054441d600e90700000500404c1c2148186140380c07103c43c03441d000c0c030300801c00400d6105010000781403010840700e510f80c92141c02c04498001c2076100601d4182881c100d1901c0c05140e0007500850100100d0a020b8090300c10207028060780703400840c90240030384110341f1190f0104000340400c200840c0d000c0f40401c82e07101500d511907065035031444507614080180e0850107103910180443c0204409102030244a0340102480d000441d0480103007629400c0c0c01840303001512030140601c0b0300c4c0c008101401d000703201075070744148110000300319 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 817660899 1250 817659649 817659691
    0x9160302062a01050702010b0627040b030d0c150605060d02180a0306060612050118150b0c0f0d020c0303040608060402070804061206050603130201030e030c0a12260609 74
    0x45524801d0680601c3c0d56810510015540c2801090784d1144225a6142007000d042240078003244c0e034400840745090300d218080242d448942003000c54800c010b041d03c0903140e01500c040d10301c0e00445801c5850805c800c000036440c0c011445407500b9a240a05868102803516102100030342c8018607402101c2c1242c0e450500c3c1d6541d8080400c040c1d440f0725004602c80d841c014001c0d0801e08820120b080542c2403900500181d0f11803880e29650b07080c14a004510000310b032202c42601c015641108405040002e42e481ca842e00011704080403c003c00c0460321510f01c0607904903103030450f0100c0a5450307001003004000b4079109404881d00719000034001840c0080d80c0d500c1d211b40d5070088c1d00000c041007081c00c0800074010f41c0c0c440c02008200964140e85076180421241d094504110402814180d45a5407000045400c00580710780780d110b64122800c0c050076040110030b148502c821080080c080740404840b5a07240103a00f541c085d4110f802c403907292254400c00c4100000200128199241d0041040c8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 817662149 1250 817660899 817660957
    0x170c1606140c04030b0c2506060b0f040e09060105091f0503060708040605060307030c12031814030f010209010207091d06010b04060912050a11010c140705090916030206 74
    0x8010a5070b00100da540340d280d031800c6860711200408080d00040b0506c1031596503040344080f6540c035000e42402c0392010115161503002001c8175007210501120100d1048880540c0600400a0346c0c49001c032041c4d00ea40312500103648080034024240c102550a01090f62901070007903008040064141c440d00c150349270004289007044c100e9618001071205014401403012a00c81c05030007902c254041c00303d00342540c131410040800d501c158400c400c814a03140c4189481002d2480703a0346d100c01c9021464550300c41400c05040d00302c4000512a00412600c0c4406102c14800c803110703220117030090704c00700785070200c10002000b44a50103225810303802c1c1c0007004007905000c2c05020300251003849440c1e03418000014050043ca070003000c0c03640c00301d03041c0e03401203580025503040c0329902c49040c542d0801000012a4420510035001744000d46168141040b501c01145081c01d48034140d5401e4001d5940d10382450b65030540c040300c01910b02071241c0500150409030001c00300f40c030f284415098039128003001b1503 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 817663399 1250 817662149 817662151
    0xa0b09010510111903180e040f08030c120a0b041118041104030609030807020c0d052a031f142206020f070c171516030624170c160614 59
    0x8000a83c0c4925450804c000c0a00b2000641080a242c1c8103502e01a50381011503e0303005005050ac042c040000f40245104004903000b182c1c21503003882c964240710840308047c00090310300910460908a156030301c0000301007512104400410030650446030081480f00034800810b030304021302e80030000800840d5043c01000525442a542c0c0030a525002078002d041c00300c030910440c85415a054005c01186000403800c028014a1040403803841d0144040c050203125000c41607014001c6406000518444414025500481107001c0c01200400c103d02d10580c40110703000c0b1682080b2050703609813002c0b9042c402850a102e8880185444a41e0000300402d400500c005c541c02b001025040c0501401c2d060f8040c0022aa040180b020301c10704220040008802407030303401d0a484080d4460b142a10a0b00a1001818a15041150680700c810b4007203400ba4864600c0d0041003242c210341c0d1103000360042a40c030a00c0c003015800c2c24000030780620a424043e5039000c4e182d131916071040c020700c0b00f2207402132 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 817664649 1250 817663399 817663403
    0xe18040803160918020d0608060c03010612090210110a02060c07141215090c09040c09050618130804150809060703050405060c0c0f10050a0b090105101119 68
    0x60312494440c40c1030344400b0480c06650704024070318800b08840c4041848100340c040d1500700245c0c07200302c000c0c15040200f00d5035114001278031602081c4100f0503083c00066050fa401ca40e107591162903603003001c0f419a500008025041000304bd011491144100d01688e5031002d0541603501c01009600029401e401c955811741e110740080000300020041e20703002c41040401030342e003894401d207200c1c103460325980c00190341c4074040420703c00035401007020b21500c0b91400008020b899182002e0420a0309400c00d8051500701c41d240c1000f00322a46080d0107154201c82150f101c6904981e1814580200002000030856030000f00340008141a00c2900b80741c005103076240d03115501071900a41d541e2800b04c1c0501650103040c031781010b002c04070306e010030059400600542c845640c0c04460311114540f41d0701c8101d042c5103000b01040784888040b182c0017580906002001030140c40801000c0201c4c0d000300788035203a17001400012504202d4080d62079030010000c0101a1030701235a6000240070151030030981 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 817665899 1250 817664649 817664663
    0x20c130c051b030a0f08010317030c0c15011a07050d0e060913200313020609010e030102071a0105010f0203090d0f050d0201021e030c030f041509110a061e0e1804 71
    0x3d0b5982042e40000d420404900c5c0b0b00d002001545941c49904c1500043d0900e00518400040001c1580701c800081310540f240e14800c94404030280e10440c20460801e0146041440302801d804180030707640415a14880e402001600c64219411420360300c407403000c04100d8020b4000d008103400c541d0b4500d00d6000403c050040031074031226003049003071419081d442c4801791b5102413046c80380c4520b0340d1131049940d80c0e05440c01035613082d1030b02c0140c88ea20031070300c021a89507000040c85030401001c05810420100f03540b14454203644c132030340190740d0290f840480b040168028891103002c1d28007813100c04030041c021440300c040000d10361100f03420412600030380780150703400042c88088081003045203510051560046401d40c00d002004071803e22028001c00b603480300a03008502444422540c034030039900c02ca9001c000450048c40c04580203224140028416006450006442c5000c0c445070302c0200c0342030403039101010181d5429100c080c585102582c00c035039502c4541c0c81c0306502e603e855001d1402041 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 817667149 1250 817665899 817665907
    0x1203070b04121e180906150f0f0f0309110303040f080c0a030f0305071103070620010e0a0803280204090c110d050c030d020307080412020c130c051b03 66
    0x9205644080d0004000b0800106012074600307008451080d81098a03107240011808072140398803514645990060a5a146004000034207403280240c0000407000302d44a481141c00d00c841c040d100614010110f00104000ea401d280e0304c3c03417195015004c580d100d005104030209141c400701c0d146411640140110801e07221090106103c03c004140e40100203c03032246c210341c1555610701c50400b40c0c81004044c4072004c24040e04004803103240c10300c0d10700c0c050101c6880036643c040081c0204408e42550f80070755080900100544018000c403031239014220001c110714192a6a0700e42075a1006005954038a02d60410220000c520b00100410b184107840250721a414000340f03e0403180c40b42c0f40b880c18041d940103a050300b0900481d8412000c401401c000c0d03102c0f594201e945003148a420050700302144000b08000c80160400301c2c1500507030180020506888207003030b0903a51003204800c00c40c2e1140241102d1901c8444a03080100c1c2542103181c19410300907149400c680000134501e00c0c00e141c1d04003117 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 817668399 1250 817667149 817667153
    0x109121703040b0402091b1e1b070f0501030203012115050108010515010201020a0806010807051c1401082a06190903120e2103040e01090605040501060c050c0f1203070b04 75
    0x14903040c2d0000001c0c40784442c82c224142d640d40851091010111001480d00401c0323030001d6074503080ea001040c0640f0080741586084078400e44a620710301910f400b02c16584004a4a54030a209803816503101d081e03002240d2030f0f00c0456500700e9061443c110740d50360f119104d150101c260707409000c1c001c0c5a40e0700041101e042c80340c1c0241007098503200c00ca0440e841442140c4109a0191403550058020700348070070b607512445811900740c400c04003104000300c0340010281c2c01c5e003040e40c80541c2030100d07003d0b03284040e40c84804d1661103151030b150340710303074030006030341104010320303130306404007202400425481c0740061403803460f0202d111072414000840d036540e10130802d00c030f100851403108508614000117804400070001c2c03007a0110b000c2d0226080403082c041b605000d01001103070090261200414540e42c2d503060040050241030290754001c50078070000103003550003441d40001c016400000340111110402c1401508000103007000d511401c4007124000881044c0001e10540c0d000303c0c0900364a24140c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 817669649 1250 817668399 817668409
    0x204050a0b0a090b0a050d0e1006030305091306051f0314010e15010302031012061d03041d070c08030411062a0c15070303020408010c0509041401050109121703040b0402 74
    0x70303441810040000c010321850aa4440116200e416111000041e50b10023104070502e4094040403800400340b40081c040300303241c0c00030080d188401d0211051000040c042608a003a51800d202e13154001d001420601c444001c1c5012900c000680c500e000100d21072180460f003541e0708203070310142d4120400800d0160034988070120500c84402820154554242001c4075020b40d15240b10390540401022194401c10802790800c00b502400f000c140b101c60070051400940701c1d0311500c140304030b030fa02c0088111559049180d030713284544540d454030000308003551110075150380010412141c1c41d0040103400304503a107140c060000c2046101004460b460485900b07451031041005080c0142d1201038000e51551728180c541407802d5404040360384401d603624040d0040e0103150000d0480c0c0d4242409940015403100103444604002c0300c00340101e40f203070080c1d0401004203000301d07030004201d54018000003103c80455940c4510402c0d00c4009007503c40b40b1a0816001a00d04448281d001d1003800b06600d44 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 817670899 1250 817669649 817669667
    0x9030304060f2c01120e01060905010f061e0309030e090106020106050109080c030607030c02210a0816080a0213120809031606050d0b120a06061a070507090e010204050a0b0a 76
    0x5941080300d00b01c800c40b1103c80e180c90601541410003640031340b07040b90300090f5040101c011070084000e01480c1d0f1181640400b916003401008940c02141100244803845030215811004240120b054116003d040c1140a02119101a000c0c001401c50850580c0c03030b0306404600800d0f6950000508900b4900010125a49948440980d520a1084011554010410036003011940c1000a80c0f000b02c804186d04045810b48003041404604e002599010941801030203000e00a40d1403c041e90b90381e60b0046403500100c039018001070310341c20002e000040640c2c020a202040d14100c0d12019a4030311442e0000009440101c1c1c10390400300320241c035130504000c1c002a64000c1e840d150015030a1140040070303402080801400c15031106031a800c261103481500e01840101da0907229a5501c504114010b400c50340f150000c02824480c0c1511300160101c10345124541c40005014010300d4a41c2c00b5000e08061000d80100d55420013000a40740c0c1c0c7c04103913074003c1c80350740201ca8803005000d034003620f0b40403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 817672149 1250 817670899 817670927
    0x7060b100216330c030f0804111908191502040e0c070f120c050c04062711190f0201142202120102070501061e060809010209030304060f 60
    0x444120004100300c1d991411405644603d03214070502c20340c0e1440012509a4030040002a080c41c402c000d50b580e034816850720005003e034848405646032640304031901d500488001d012001269a050020320f070512503d40c441c0501c3c09040040754651031450300348650051003590310610b00c08480e0400c545040d0b25842c00c60500004c40c2401d140502c0c200350040c0042c2004040000000c2e0b06082240c401c000342c1c01e00b5040b109144565919280c0501240381d04201a50107102e01112004d56280c2801118181d4950f5030800d04480304500f41c0d1146501c1c43d41c080080740381c440525080d25034032000900005a4034803412500d00b424014050140b105101041c0f0440e41001c0e46c605048004082140e0010b1218241d480c00c15000345110b00d0a56882c24004e41c003c800001d000e01c0010150041c240031360040008010444d41c400d86a02c40c840c56140e503c1c2030900c0d206c001c03c10b6602945106900107040c00015191100b0000000e0071076005070003007030110324640001d4110652000b01c00306012 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 817673399 1250 817672149 817672153
    0x151205010605090d1a0411040515030309040213031a011508060a05010c050129040b18071107081510060206060f090a0f090f1119230607060b1002 64
    0x25051041c000c00e5440740c51074440c0110384c5030f248201007091007525a184545241c0d071243e2181003d203442d02d9039455040c985c520403030801000c19100d21140321164900c90000707008500d0240e01109200182d00050303070211280e40c0f0a8000000310b85040c810301400c0a4400305a1840d60504c41085000302040000d201003010b4203040141944030300c01c44000ba20401d00300316a0940300c91914501500c2407034904450301c21401e024111039100c0640704095210112000e1102542c1c40c0144601241203458612205c228600810016801005000c036180190b41c10703200460f80780c51610303140405891190405000c1081000800301c0701d8954107019001da48098030240c00c1c01400200b13001a24801e0902c09e03e030b964041103410745698080aa126019203050101c0011810450780030246408280c624074803a0301200000d1401000b8090780500c0c001504001d2400c104204084100740800012400c0d0800040f140c69520f0350080c2c410079104003004070f0080a40c40902c034110034003d103050195 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 817674649 1250 817673399 817673401
    0x20310060f080108120f0f0a020609010c05120f092a0108130203030d0c05040906060e0a080303071d0d0f050c0114210c070c0f0e0601090f14030f0106151205 69
    0x5440451858911005e8400007078440842e40504420303441684240d6202c9040001c1d1421b1142d00441d4051007125850020454100948003e8456110340e43c1c4230300c14941203c00007400780611008450700b04040a0030ae400c6404145807152004140081c107a5043d400b1140710f003615a0300106455001603100510401300c24641c1c0466901e000c2d40482603040c40d2070b60300c4041907602ca44141ca0040c01440b0080c0566560b44d6405080c42c1407152470340c1e0013250f20400116000d44008112070160304d07540d55402407990702007030b6100440c6203016050703444900080b2510200d00d40d040411020b0380608003820015407040b0015110414400c0c6181c5101e0f418085140d80d07070807407031955042c890b085040d440c01d944c4508120007280704041c40141f04200001000c10203140c100103c0d000e40340341c00c90f0280d96440700401036448420a100d101c529420030380003840b03600b1004841146503d00072b811198210a0b800b000c5081d03802c5500130401c00d80c011348a0b956032650102c04a4455440c002c0e08001c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 817675899 1250 817674649 817674659
    0x5010b25110306070504030512032a07020301020a0e090609040b07270b04031502040b0f070204020d110c070b190e0a0b0307020d200a0201030f020d020310060f0801 72
    0x49480000020000090325a1010038015111040080120001c0989440340341c0b260f00030b88590094081591284640d04904030446a03040c11a0300880207003181c080703140f00d4100e41d03903040c90380700400b614813460a00640d4010b0300d0034005050765440b16140c0c1004402c01c181840416a001072a45100b030312000b040c000401ca0781401180c0149003071500c00d10081c103440b034a000c15407035020758010340b582e09200044c5602100000e88140c074426030000300880174448004003a40518092200212000c000c10310707403d04000d00505000744082c0003d428400c0441d03840c02101c0c00c5001941c098500001c3e12820884207000c91005006c100394040c0c01c2a03d40d81700f418042d0010300114084c002c1460051500b5664a0f403100c0051803e0405207640e85070140009480780400308000011440b0b00480d170034001c12496030021900744c000c004191241044d00110003404d411000718000f107500300445400d0b02c5060000354854040940031003201c81ca800401858030445105071010003e040d001445 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 817677149 1250 817675899 817675927
    0x32a060c020d0c200a03080c15010b1606110d06050102060a060303141318091b06121104080a050105090c0409080304060509120403141608070e04110603010e0a05010b 73
    0x450070782008000c0c0307000e0060242460450045400194051170320800001040b203040c00800100d82041c0548080e86181c2c4103440d040c400a00440300308080034405041c900c8075820011341294003500c40854004460341c40c100c543c1c0c0c080c101c07802d00076841c0c510500946d601000b02c1500240c802400308441c900e19203009002c04014504070f90294400030314981030207412040e41c409810030750032030100850b54410791401000321841c115601540a80e0060b0f0440040e03101d00120303410f80d02c0d016030300401406034000030b0500c403521030b032010700c1400003044880040140003403146c8540300000d81401d095610754546840c006540384100d003003942072030009400809590300540d1040c800305040d1a04c0d8400b60810342c0720407400b80d09500200300041401840201c1500c010002da0036141d582201400103031829015008520260b4403c0e00104084084132807507070b6100c0d005580c2c01855240442c00210b080e030003039011400482d140424003642e03080c1c622982c4e0040c500304d01b0a500e40810340000304 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 817678399 1250 817677149 817677167
    0x3090111030c030901030e070504050c18040b1f031b0908071403120a052101061209030e011d030102031806070c0f03052208030a020c0616020d032a060c020d 69
    0x217810591178a4050807660740c2080303100c0182000410078811803911700c2a8075a117802618036282c10540d500b50404440c200b40c0300382c0140c1600030740200060b460030f0860309000642000e071042056901d11070005070a02d1204e142040003115030b17400540c907140091261402c2c2c3ca07030b081694105001a4001d03240e503000149901c9002c5d1085010340ca03001e10000c00e0b101809520f279580d42150340e1001c40c2015401c001c01c2503060b01c556445a1650701c148400e070fa0704660440a0007000304005400c2d0780010340c003400401071445014822180441c0d40000428266081a40d122541284e060240700c451481400407650060315032500207410045a00d5010000003840801f50921800148400802801d120120700203014845010445d60703445c80d8683d56944801040070041c02510400d81192500100325410310a039224070b034282c03500a400702306030303118560b400700e013444840c035144003008821050032480d020602050b002c401200c3e050120580722142c04078011074000404038900280c103d0545 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 817679649 1250 817678399 817678417
    0x190201060506030414280606060806010804150621030f110d0f03090f03020a02040b062106040207020904050d1209150b060f040b030a0e03090109030303051003020d0503090111030c03 80
    0x8100c174a07040300c1250600f00205002441c1119441403004014aa10a0300900a1040d08104001552031108480ca1340c010340740380e40080c1e0400042000708003c0d01d1315001d040c0100f5400145c3e07640c0c641c07100e0f208031a030300703101829511034012820515800044a001c121840c1c1424130241290725985915040f51502c10010721521080c1d541079980b10b0b0340040d085551000c40844480160b06011b503413100d860307c04074451030800c030300c449503400c0c050300b550408030700180c01220326242401c10500400d001410240c200303609010074005a80c0300800c1d14003c60154001c0e00541030b040b140200300266444c5003a080c82c1c101800900003900c40c5100003000c016084000417062030395000101c0b944540f00303502000d030a0101d0b01140c500040c200850203041e030b0200800c80b0005642c0c1207500e0303019090110f80490350300102000400d00940245034009580c00320800c09589079400521821402501950709910108222074a5600000b0fa403542d100c90748000d50400c00d02c18052540c0344190b10103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 817680899 1250 817679649 817679663
    0x307170c19060f060b0f1204021801030b0a0c03140601110c090a0c1206030203030909101a0a020d02070f05010e01120c031b030218151b01021902010605060304 70
    0x10464200900744003606500c0340084410740307503003114204400500303c80d40070000c0007032a00343c0009074850074104560300c01210a0a4504052251084000c0402d00400581c0c100030348403500440300b00b200f540c41d03020b036102d13030b02007007070350a0101d1a0b00403102102d0f036801c00c0c9860702031440c044207025600558000000d1038000701c2248060401804c05a03042410381e0010041400d1048211040e0000d810902603540c0e103003e0440300d4400c20094402c144800794154104104240c41406d1000e542580150510802d0350603071f0b9035082d698000c4250b54003c02c0c1e50000411700000055062090b002d134032403988010966981010901251680c4600c1031a06010a13041022450b0740220140c4030005005541008260140c000282c042d00311503454250100c0c080105a180324020302c2542c081449885034000d00b80e00764001e003e00070490f80d181c070402c49014450031502c41e4103054400764420860001684a0714854040c0e0220021036800c8815641402c00501c4244c44000a0701c1e403058008507 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 817682149 1250 817680899 817680907
    0x9120513141309112412060604080f010c1202030603060106050307021f090b06060a1e0e1921080702132406082203030b040b03010f1d030717 62
    0x100150004104240c0710107080c3c00c00c0b1407842070042c00003200f001c0900030707140484c050030054240003061549007070b00440c00000b0f202c41e9200c0581451855407046006d0030003450161034510503450141000400a03040c0e45030000760040d50b510104284000c80c4465040d403c505100c00000d8450105001d018104200840005c03c0c061003040491603081d00705201c40362240c00d41c440c1c84050400d1140540d010031600700031400758101300c41241c00381511607075440c120824030000c0f40c64028010100804101c0e4010714001c3c190b81d03079181018000b011280b040e1202c3c0c54100c5c1c88100c1c041c035041030340108044505110100710900b00b11070030140c0c11120046041c64001c1e0f200c0007481040a040100c40b11016822148003940c0358042c1924540d03103d4000d9945c60390411940840c039140c82008005446900d2030009000360080541140c0080000c00c003940c031440800c1c01c46e01440460b0315119140c9103126800c0214400c40c40c0486c15000195140c0456030312541d100030854809072003c00d01c001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 817683399 1250 817682149 817682189
    0x60b0a080a02040b0d02032203020a12180e1906060518040e0a0b04030215060f090702070e0c04090e0a05030328060b0702010315050a170c060a020109120513 69
    0x2e4100c2c0c0103016a40d883c503032610020f4003440300940003102c480d6051807110240791001e0900045000f1502d9050340149600e8200341d96480d0047d00c0c10400005014089441c1c070040540c0202c03c00c003400c8901c3c01003000d0724207034000c0020000140e806620403072400405003c0240c0c0182190b1080b0106002e0340022100d08000c01c00030003840c04c505901c0c2c010b601c491001c000b994003505000d10300940c2141c000201c03002580300f802c14140d4009601c12000c00b900b240c1ca06084450035444a0680107603000743d0742e26000358184a030101c407260322090b80045c00340005001f601c0780d5038040c00c106004020542541d541e46a40c0e00c009000c54440070042001480d518020810182d003049240c6010301140382e0714000a80c4c240c01c0034400b2804a414140804580c05480c41036004444005111008a51902420807002c000c40d05804a81d40550188504103460303c6009120b0081a64000141507a140c100b001000c0d250801c1c000400000708140799080c020014000d0548200c2072045142d18245 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 817684649 1250 817683399 817683401
    0x60206070e030c0406090e070e010b0301060c150c0206070f2a020a120609060509060601020a062f040306061d1b120708010e060411030f090703150f0609060b0a080a 72
    0x3d210340d981c005e040a901160300d0200e40c21901d510629202251b2600e40c0381d51295016410900951425003024001004510f20030249016124020441c1841c031005161144080c0c4030500d01c2c01c0003582c400d0f800d005000768040b01d00c1750413207424600100720103020512001c804550121800c080c942040c56042950b070b039684214001c00300002e10b4015500c2614004000e001c1c1c01e102502c0c00c13441c0c840003442c94900401c1680c4100c8050340900701004240e91010018040601c2d089184600c40b440054031104540e5001d85203100260459180d80c9185008426506c0540002c0010106600e1850181231144140c5030480a404400000c1001803181e00c0e100380240f001c4400040000014440104e8114010301c0c10b0f64141411104a81c0d510b209101c155801c00096004c851410000134940741d0700204200c0d0040502c1d01505c84042d41c903114412504801ca038040300441e41c0d004131418204881c4a070a006144c3e15105208103071800c2d4000c1d14034040d034002d01c001d200405000a00390102c07 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 817685899 1250 817684649 817684663
    0x507090c0e1210050a02041d040c150504030b0c040302180702031e0d060e0115030908040e0f1e060607330605090912090d110d080a0e0a060206070e03 66
    0x1410426450800d952481d5840c1c035003805403804940b034038002c500340420900850f03099801ea08c0015074041c445841090048000400540f1401010791012600c5448109085800c1500e5a00c094990741141048100301c8405442600b40c0e180401040005850390322002004c1c0804a0840401c0d9480c01010380c103604c00c0c5c1c14100c010a003442e0803c141e122424000e44585400c2d800708006580d10b555a600b82c40c0000e00940c1c0403c1c108080716a1098441e0700441840c2e0700c20700d03046041a03615071480743c0c2c110099070f4900c143d40b6054100000031440719410003c8440407100b1180398106000460910b00c510b401c0903202d55001c1c003803800028104500340d1100d64040030340c1803026103990400c6004001500540d0712414441000c56040800083c010a00040401c44945800400c42c104503030145051012110742002440088650f80c4011407103250394020940303c1c0c0e031a0004840200345d100305005183c4034801c800024030030756600180e01e42d0300c41140c1c2810300c40e00c0b40500c0064034202c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 817687149 1250 817685899 817685927
    0x703050d05041a0604090c0902090411030405010506011418060304020d050a0b0a14010f1509030b150a060203120a020315030f030403050d090b0d0b04090803091c0201090507090c 78
    0x41007005000c100314800c1a403440f00d1040e05083c40d090740302e020400c820f8401d0110040c0034100360f00720920500c2240c1d0300410f0401002080081c40700c0b24140b0128040d00100c034203a5650f5910b4007004117550300000e81074102d484942070f240c50402c0ca006003030201036888003024001d0700040001400c54031105d4920328450b4003c41145c0d40d624162a08d00442e100c00c0303035040e1100341040c45d40d0399110070b5010494103031031200b00b8080380c1e1424000303807000c03a6644010f14010840c400320008007249048032114000c04005400c2c02c0c0910121091100c03d6085038403003801c40d4810010300d840680204032698106216000c0565252640b454004540b10f0040c5e21a030315000c0c58851300400301000004204a9201d402929810003040105403032006203840303498803e010070840b818040010794070000080310000e05c0042c0540030340d25080e005810440f00844643d0000303822b820040d20040c1480407144080c8000c1c4203240d10382c0d071030a480b509944600c0780c145c0d0712500324086080c000c1c580220310304 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 817688399 1250 817687149 817687151
    0x2428020d110304052a0d1401090b0108010603170301060507170c030c0604020f090103030503040b071e0f17100b090414070203070308090a120f0c06020406050a020721080703050d 78
    0x20510f8101651501090030301502200c0c0100c15140d103411551170b1001415400500045c181400c64403061103d0441025412107956104c182000150003150a00d001e030181c2d05c000a190f5040d481c01da6441000c126090499040c248010410240d01604454540750300c038070314a108a003c00c125000d14019600002801d00010602242643c40040c81038401d50084940d100d46103240700a2209030301083c0009400544104000f501080c14040d003650000035525040380e0154003520782e039219405015880d0700203414845407541590b0300461310000800048414005405d203e15051039401452140084e01c0b034010854401c20b42c0c80390300003025104030380440c0e0201c1c6040d1900075101d501940044001c00d0300c441c04030380c030b0802c002034940c0f0f039590150042607089c411800c1a90b4483c400c030809801c003c0e10840c140001040350014000808150b200c1d00c1d255011503801030304103290354100b0f81071655040c88c0804101e540301e844808050b008008542c0d25121414100c40c1e510511040f0740307203d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 817689649 1250 817688399 817688401
    0xa020915040b0d02011e12050c0a12060501020601060f02150705031e0412030203180a08040801061703041406040f081005060402070c1e0302032428020d1103 69
    0x515152a181408a001180c003001250310003001c0244250340454080d0005100301e81c1b551103009002c041d0528555141030841e10910b1030540c5006a0303000b00d911080200d8046103005038035401c06480300341c0c000c2e110800e00140f41401c0000b03547c1c400504c40c1404000c01d026480d18503d000744000544001034103d014035503d8014406480c60b44103503183e4501121940c050101c010030001d010340580c1c1d014907080304104508100718041d41015180ca24041009035a100000b0000c01c41e02d0780d4603100e8814a61268035088981d42100c1803503001c40802500600c10040002010040324151043c11805d240301c43c5101021401a010703903001840f444202c20780100352240b00060035000d01441180038032155036001c090000f40d010b03039800201545843c0e102440404800c680010420f500e4800100e4126500e400083c9800b43c0f6000c00218915400c40c01c1c180705c44444480e43d03000a1258520010041410030071f0740001031040c1c7c0307007516580030819402c03800d0303c4c1d0025005454509042526 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 817690899 1250 817689649 817689661
    0xd0e06130f050117070e090402060c010f050a180201080112170309030c073302010e03160215130e06010909090b06280e0c13060206090f0304180b030a0209 68
    0x1000381940209408070703a5181c1c101c41c0444d00c40e208070344608160350744c07492405024000d103d050751003d00200ea011106000400100c1c0c424890711000ca041c2c4540030506080400d07031041181c1074400c21f43c0c00368043c5000040541d800914181c11100303d40029060290b450411183c0540015a103091440c000401d202c2c0e00c010000c09401ca41100d442662006a61940341135000305503164490a2001c40710081401c4218801202e0180440c0d400081586140c000086065a00c51401d40342178030358034001c480640c00d114065820700045a01c5961400d86114a0340344004c615200b00007d94001c0000218aa48034034a40c0006259040c000d012102c407515006a642d039007101c2260281d00c28003050f03011900501400e00001c81c580321043c4e441410b04103400b4440078002d00120b03641c60104425061100410070450060099a015000034181126401d04240003001341c0c1d104c940c0b05100500505000746190307070010701c000400145030034002e8046814001e162602941c07046040c1c0030080 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 817692149 1250 817690899 817690919
    0x921070302010f1a01120b0a09090605060a081e0a0203030a090905060a1809061d0c1305330405011401030c050c03040e06130204060507060b010e01020d0e0613 70
    0x809403081c0c000340700f010302c0e81d56060708650540450a00d1141e0030702d08010f981d40103004854031780c420072202064205840010411144199000e14116541c404081d018045540304e00c2d90401401c8078001c0503035107010503140c0d80b2444d44120904000000d60021040b1000300080d201e007903400340aa07610b9080707125002d044210107203e968400d50810300041c84030f2170b000740010142c0750b00c69488401050200c42010042c02c0004c1e041f9803040e0303a071510900001e0a090071100040206c002040c0040c03040c8240060303600d40c3d8030300c1c448090800c001c0c40003440a10842c21000443e241ea5400c05220104c448640c0907210849a900030b4545800440d140a4182c001c00e544182070301e0904c851002c4c0301c4211802e210788601e104150704140801e00016003804d0740d46420003401001c000501d46c1d5a039903a0104e80c41030303001001251002422008000c0785019801c0040004d0910741001742d401c10020351906401c00c070500c1004008060192541ea454003900d0014115403200304815880300704c408 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 817693399 1250 817692149 817692157
    0x804030306050405070c231c0f0503040b060f0604172a0102071e24090f0302030c13151e050a15050c150a0b0a081b06030921 55
    0xa400281800e80110b5030f03081070b004143c01100a6500e05007664455181d102c141020960407142551000c3c0311340e50b44800800c40040c0c01040c4e842030f200421000745001d014101016540c20500c0401d00c10030000c2008050f900e40d00840c1a14640241c081c0380d130001c4e11a10480d0040229861465503040795440c0000d03611142c20310820f035414100b886003c4007058140f00d886020300607840b0b607801317000429007a101080c091f00300c103180441c5141ca92040b600d945420110030100f40d655a00a0f10703500f6800312003c070082c5400f081d98101d80b400c540100f0b88903880d00781114050040070074840c1008447e54000212083d0300c0c910003000589542d92440d078000b03c20b001c1035903518005c501152500d0f01401d141c08543e82220717481e0388074004c9081a0b07455000341c000c4420328011803c0d40b045a04242c02500d10402480d20001802c025000400c0884803260b00714003030a40c0011070400c110700b0b01007241040d4400845070070340c036540d0f540d0f00076280c4094004007501104e040d40c030042c83d0340101c0000e0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 817694649 1250 817693399 817693403
    0x60c0c030c0e0f09031e13030f081306090b040905040c0302090901060f15020307031b0c0b0901020f073602040314120a02151f0e060406060309020303030a15080a030804 74
    0xa9203e584031501803558030300460481548075001041c0c4809a628240c00a2100224010860f0341007a0740c0c1e229411600407180e0191110480011140d040407110800039015000310308007400e40314200f80b00a0b060f805503006803103840355500301240501c00d44c00070074001140c0c010584e20b9a40791440646000e8000c40c03003884c4400300c410b00046003410545000048481c00c503401541040103d8400722905804100e120006543d1a44148003041d01450380344d014000316070b100d030f0b03680b40004002460301c040c94403081b906410004013408581c0071540d29940108074940300040741008120304034800c1300940c081900080c400600001003040c08a050031804520f80185d62400314201410005480ac0300d131040016003201c00c08984024944c4015500320841a40c01882c540f80b12809102504250700242c020344410810020180707850b0059a019148514080c042c824241d404655a4000940400d2505803035000010324009000c00140052280c0001c4985005041c10040c01c460b03000d07034003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 817695899 1250 817694649 817694671
    0x206070c03030b030a03200c0f04111207180e36010f05010801050130081b0106080609011103010b09060903030f07060609050403020d0f1209050609060f010e01060c0c030c0e 76
    0x70081303544001261500c2001000741149650f49e11003010072004000d403100c925400c81050082c849030502000086108025948600c61441042d5084207a043c1103a400412441601d10800041810402100300382c406d030b0040e540c01c001041d05010308007840e9140c81a407158601039540b4030199290304218101c03685000200026622000003009160b030000406c94840483e00d800c0070050405140520310500814505081035903030000d010807400000c5811700960b4449405010000c0144070b61034012103120004c101c02c2e0f40420b00d9042c00c0c00140b103940703283e420124042c41c054a551040343d0f48100000c0035256201c8549848120750b802072541610101d14000004c13031000540c1c4281e500954154008241c4c1c801040f1040f560380001e03591000c05c11215103042c4411031b40a004042e5001e01c108080d0002c1e00e4808000d9181c403400900700d480000001c0b0040120840c003d014a040d519546801000c000d02c90030280d83c00d80032503000030003100e8034240000e400e83d034000c0d16601030203000da0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 817697149 1250 817695899 817695947
    0x30030a08041112190609021804020a06050313140c090c04060f0201020906030115030609050a0c0e03010903350a050610030614060702041b1107060f0206070c03030b030a03 75
    0x180020851800e552580c10343c081c160a1a1010b0400041c078440345c850200401c0c2004180e01180391002440040c8580d00741e01c1f005c0c0401c5107445280c11014084074604181145002501640546082c04010740403a40c01302c0f030800321032130030300c10309800e48000703480381042c0e040c1107071500719540c0a03101b15800601ca02d42c000e901c03940306000f1500d139640c00030074141c11070f401c0c02d1a580702c02141d0801c5d202070541d52a0002451a032600505104103100300380000ca04144100281402c2c0500c001c50b4400e900d0800384500103a00440d22503103444000315002c80b001070b0b448180d103141000c09800d01007100010100090300b8440c2c1c00051150205035901c4c40c100c101d04c00c06801307680c800d0084540d95005105140b815041a00c003034272600f400240301255480f01c424441a400c01c0c8040803a0000302c62903044103c1d46c000b004a80c00400e2030b490003260301000705400a44483c0c0291140003080441441281410f120b84c04c16107031840001c0c15280c108165107000b4001300f80c15044aa00e45180d10 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 817698399 1250 817697149 817697183
    0x70c0317010803040311220507030b01090807170f01050f01150305070e09130f1a060a0e010b0702180709050306150607141203010b09030105060406030230030a0804 72
    0x946031604940c8024000d42c280760650352103010b058003000c0165040202180c11507040500c07202040411458420000f59030b0500820040c2a52035040c41c540c140207401740108140700c0001051421a80600c1781c20305c2281c2c0c3d1420b5103081442107a0103015540c01c000c240a44074600700d0a03503040742d040d81c4c0a0504410004016001e85804440000105084101c140c03c07a09261744010ba00800d180084400307000c290b0386407894201c03229407d4650a0406420b440502c5200c454160810000c9079000d18052904c00c1c040c082000500a00481f0800031680c0001c40d1100300c083c80301007045070030703a2602e40b1700000700419031001031040c2c1c0c0c803a102d48800f1666101d2145049108543d002e48a1031502c610307130f15207868506044c3d040c83e00a106010780341710019507100180d17021304228403c1550360380c41c00d0109400c0d14009086e4a104e14603003101000160f4482090049100034854008601480300c07000f01021480440d104400740000203915214039400000c451003984140c0f003071801c0310154 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 817699649 1250 817698399 817698437
    0xd1101080a050618040c35011b03111614010c030213060809070e0c03100b18041a030106090c08160f05031506040605041712030121020306070c03 64
    0x7070300c1c41604011080400c0d204e089481c584541d2041c0170303501401246a40d40320f1341b8800d460034840041e000c480000d56860314541e615682c495404840c00034032030120440219070020120162810601d552040524207202104060300c044800341c05004154109070304040d0140c10021006042c554a400c0344000c07124000c0c03081d40e4004e0015482c03443c10318200a000d462082c13010745804002c1c8195540003031080503c01f40207100ba00000c01c210780320704004040f1020242190130401d22000240803494440e084450741707940b6044101c501003408034900842ca08003181c10080c05405500b0414007007140300080e00503600c070301496074071001c0a40d981420780d203445088030200c40c00960103000002c1d140c0d10031400b45400902e002d203080013001d00400012100d034815480b00002c42e801081c1000694840c200c01528151a2800341881e124040c031401c0c894401406040504217007000340b19010b0001c040100758440d80501155018100401c1c00390944e9402c1c001100015545007641e868203482d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 817700899 1250 817699649 817699651
    0xf03080a090b01050f0105090a2402010c02190303090b07180b040b0f0c0f011a0a17061b0f03010f030b0c04030503070201361401020a080909090109020d1101080a05 72
    0x8640341c000b99081c0010400f0503241550124100813040c041c4903059554840d188006203146400156004140c441d41e60b01c6001d0f01c2c0a04056926104140400b55000704030912584025040000c80d42e0441c60240c0041800681c05003031800c5500c10004d000350030040000d001100d85440d0890345a82d0015070000b4070032401400840c402c241b041c1d401c4940144c01030300d11005440150792000000c0c0307480900310790103c0004000b2043c07580d20104142801c4a44001812503040c540c0003040440c0482070741d9880c00b800d003401aa0b500402034181c0301d40380054401c950388940f0001c1da00e5a40d81c80c1d501d18009140010740d101e013500004100c80803250350440c0c00f2030342d000c1e019600300003c0b600155002400300000790380e21008441e00d0721807031558603280400410b94414640c8080c1c01e0414038030009001c0c19140703055500400440020441c00d40550362410411504a401680d8002e459809001004402500044003001e040c1c20800030341d207290b07000c03182a65000030b26500c0e541000b042e607074 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 817702149 1250 817700899 817700903
    0x714010605060414060f210118090b06090c1b07080c040603030c0305030604020412140706030c090306050c04050a2909010503150109080609030409201c0f090f03080a09 74
    0x50130b8800c1c54060610001415012245942d180c1c189218141c00722046c14810281c64020080d1000600c080c0e110f1140421281d100c60b502084550f501d07507903010011a004c1e280611035014100003130100240501100e950410401001c00308046900d26076541d6603c0c3e000b081154082d0949088140c1824841d640440c0e40540c0c4015624032181c9050341e442d8000760000c0c5c1c200d0740070040444d9018011042c4a0050f20400e400b040d52120b13252000e0808080c4e8200342d0406040200725202e040e4400c01c2c042c00d594200200140a46409081a103248240d910131904080c0c0060005410610030098881408102e250741e00d9203400c3d0301d24195203102d03000348240800c00900114455824200304180e620606042c909091500c078030025250803800c0310808007d0340001002c3c080c0b004c0a0041a03a60505403524410074010a9050805401504184aa10603080c2e51403801240307250003410301c100307007003008121141090500d1340d0061388810341900400c1055002c50050b09840c07240041041d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 817703399 1250 817702149 817702169
    0x613290901180e070c060509120a0f03021207021e01020c0a060209030a0f0b15030609030d240306060f060503040203070b0a020a1b05030705061809041707140106050604 74
    0x1140810064072214000141018206000b031004200100b0458143d070203a01c280d1186000e04c4c170315241840c00d64034020b107040c0c0a074012040800c20310142c0029110841d14600702031a440800c00422002070150321450b07500c0e84450781c05d0100694020811040491000200705104100d001c0d04500340d00c20340c0b83c0b0703404c140c0c0282c04a902082183e806058000001801e5520710a86074441040390b003085070055514550b050240034a4020700d41d200243e42c1c5007a40034255034034003100740c592030b4050440407244164803645071191008462540c1103458102c01f0840c0b80380340d142e051400007800385000d0b07400b80b4007a00e04089844c0740681d013924421039000b0028850281442d810800c6a0002e6403d9801d5100741c075015000074035200008170a80070849007000c0c0d039074540020186803a5a40d408103000395010840450b07a001d03c0496240c9103041075403150b103191100d140403903c4d6424100c1c244c4404a01182c01c404000b040001891030b008898000d001d1652201c082201902c203030b1182c00600 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 817704649 1250 817703399 817703407
    0x606020f0f190c170c1002010c0e060306060f030702030c190b0604090c0503011119030203040f060506011b080306010e1504090e03130609061d0609040504050c061329 73
    0xb21030492407590040c0c0c424124020142ea4640312203218650031810f500540e04803600c06134140c01d240c4c00000f078115030f0781700a11482c07401803806404403e4102e40c680c0038220001c00100b0f26101c1408039100e00d00c44000c1c2c2aa01c0c50025002900c035081a00540d026000d40c46042c4010b0400307100640c415508003408400a4503808100002030000c01402c481d4210800f200082c2a0340a220311100340c0c0d0280800f43d59644248000c20325100501806030526205000f0300010801c0c981008009075880320740041c20351580b8005840380540b01d007040360303400412801e00d0200007005010b540140030a0b00c81c0b0801c00350940c00c004401100f03801c56040d80400348400c200c0550190030802c2d0300d00020b8160f0786400710f04080310459603410342000020a410000c100061070b80640d10f4803001c4002442e40c00740c0400000040d405108200710a480b403030325a000700b42403020501c200e8860140007130009a84030050f0341006040c4c0d880e841250a00c00760b440204840b195001500303100d0b0795410495a20b8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 817705899 1250 817704649 817704673
    0x4060311060d0b030123090f060103030f0e031204030203060f040210032406050c0f0d02030406141c05060a120506070f05040905040501060f0b16031b06050a0606020f0f 74
    0x92600b0500e2150701143e110b182c07150150f02d0a1107121901400f03c102c2c9102600d200c07044042c90b8401401600486d840700100c0540c0003000300784681500d40c549840c0c41d1034888a0b4040b28108440114250305026800e9201c1269a80b400100101c030710039002d81e80c040c6c1d45c04124038060001182e0182d00450240900c1c28218480c0d401122884a00034000c2111b03003e0a040c489100569003200c4040f907400940c1d0801c05400b0800380c0300100c0b042004140ca51000d0400944902403485088107119410340c0d000301e4000e0030410b0390000c0c0c080f02440b004c3c405e085a44280600001d0380c58500035122100003080051100040741c42d070a0f042002043c480d180d403442203034483c0f031118881c000c1083c24080071070741c0303c001d0103000d014500075400420100e0611129007080d40855101c3e010b032010070480e5109003a007152001403000d81600b400060380c90322090700003007482c800170002c140a03c0d0404111501f09268421802e8425aa08403580008a0a10160344900064a008155100c0808082 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 817707149 1250 817705899 817705909
    0xb0d0c051920030c0f01061a0a14301b030f1305060f0403090509060904030305100b041e0501030e0a060b0102010f0c02010e061f0b070f0c03030f0e04060311 69
    0x50850a810b0000001c00c0d04103500350850700141900c2c41c81e40c001500d0344041080134011140900461100b80040c41138441c03940840384140c1310920180030f000c43c58007288194200650758160448400e06c0d1010801290078100704041c04003d030144940c9101084241c071024450002c05440054040e1540d102c0c80880214010000d0000e40d501c40b01800f150001882446402d014180030f60714858141014a0003500d14115500610b00458081041081964a00d0405600290141000102d035215851145107862094124629001e00010005590407020890000c4a111076629461403a283c1d0011010340b1703c80030100040b6071100c0000c0c4c0110301c0603408008400d03414000090380d50327135205405081d100b2001d141030143c2d640303007100365500a040c0039040d40136041120402980d1000b0780c1455290040e40103080d0141070205031401046145429030b68000d8100e41010306c103607600c4c80c0c01003100705104442d10000d80742140b200011b05207805000c0c1940c1d4841d070101582004001446 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 817708399 1250 817707149 817707167
    0x806010e01050c0c042a031b0e03010902150a02100207030c150f050a06031101031416020a0f0c150201020903030a030c050d0e0d0e0a0e13050a06060b0d0c0519 70
    0xa5214084c044103110981da07948100a04485201e4045003840120000b02c513101950307805410605040c80e210f01340000140e41002c89804240c10034650010401e40468010109194000e4004000c440106045005080584103d885070b03400c03945890000c5414074103034050111f0003400700303102060030400200100d002e0b41d03034880c092800080ca0f405100c0103006650054980804003580c0d800248240220606480c0d4502c2c4203003428030080703600642c08003001500034085224682c1c500311020086100b44038101506810a00421076856542015000035007540b090504000031070940001b414018003d8640c01c51006019500b403990100307095000e010b0381c103a05030030040100b109204d0324100b4441c0c0008108008000d001010296a01802c2c0c1001f9003511481002d405c0410842d81000402040c1d00501500c5c00c030b00781140910b8280c2c0740c100c03000e000070501c41c1801c6001c18034007503140141000d440140c4051010000c0d0801c1984c40d8411444180440d01f105c1900d04020b81c0102240 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 817709649 1250 817708399 817708417
    0x31b0909030d0903030204050108131a06062701110a0f03200a051b060702030a0f0602190e0a0906030b1503070b07081804140712060302090c0c0601060806010e0105 72
    0x600d141c03400040b4410200c80c00804101d0200303a0200d424049540c4c811841e40d41b00e40c007800d943c20442c2c06a01c40124540105007030241c0c0600080c0003500580f5a4402e49080010048401101c407414880754850034001c008154002407226a280300b41c08000200b0300000c3c3c0e0001805203011100e0349080303900b280e40c03d1158440070501c215110703501c103040050610790b501840142c82c0049904021405000c1038903801446010244061405030350301090040070706a005404201c58082440d00e103010340030344050f00c20400c3e440030100042d1508102481c08484088403001d0b07403580c40e40e4110084a4990001518211008001680c00e07500a0701c0390055010040841d0030340740c0d99110345049988120812125030802181c480c112419482950701c0d040c1080710184809001d04820310448403005202104010400b454100301903441c2d444803000d141c001c0c000700c01900d802c0f03000302c6c01640080361000d03d07485030000021f48180700b400e031180a542d05a5940c09508000001140c03650400064 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 817710899 1250 817709649 817709653
    0x91401020708250c06170c0906040504050405071a04080c010804080712020f01020c03090103060506041d040f020d030804030206070f0206130203030d02161209030222020c1b040b031b0909 82
    0x3400003141485a41400615a5a95030f0403520203003c48000c401b070f000b401000d00c0312424000c018003039641d00700f51426200b007036400203010794590909a180c002981e1000c040740681c90300d07130134000b100e40c401041070f140c5500c104c80703040402d04011540c004003220080d1810710300b40040d10009910808030014002e40e481203548250900914608a81c442052a2026400001c4081455806000b003000038031046aa660906152005404100421b141e82086250201000a0801c19070015003856240c01401d140940d00007890b0207800b10200f5030b070680152007039a000a41c2c40340305201d40580c02c8415405050a41c942c042130040d094001130080361f0500050106150124081c40a41108204041100d050701c0031410418107110754012aa410020106e0b001c0c0003585070700c92003156840c0703817071110705c80a001501030200900440c0000101070081c103200c21000d02e401c0e120882507610071941004150341c24010150740d48071020340d14101e81c0f10458008000d29000010f00c0e072150b41001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 817712149 1250 817710899 817710967
    0x40f14010503010b09061905190905090109052701060504060b0c0a02061b0303040b0402090903120121020306070306062006060415051012110a02060610050418091401020708 76
    0x407c840c480c02a108020002500108604041044c652000c078080c18080c10204407650400c40421104201400380c5050b89444001044005042100d41e0400038a020b01000c00a6441e041841c040d040f54171680d440b440c101400498243d014504940030100d02100034080003890b41e0912006070803114080a0b1184800c611141003001030000b9445244110b03400341d070f41e00d01441005107400c000b62102080345d105100701c2403051181c201d4030381510b10705105400c40035a00e035110318030040340d014001e4040c001c4005006803284c01d50003080076962951141559111600c660601c16407a5180109071036208034046642818103900500b1503a04518003240030607181c07004568284031000e200302c0000c0c4610ba44040e18141d61190340011040640003910740310100c040256a01809811a840358030300e2091440864007030740807100205181001220703d9841c0b6100c1c24000c0c03405802c140d45800104091088409040c400c440380350f58441c2d0342c28100480350440907810f002c000508192030700410 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 817713399 1250 817712149 817712167
    0xb0c030717220605091507091a1309050709050f0a0311040b041409011103100303050310031704060201150303021e010906050a021903060b040603230c040f14010503010b0906 76
    0xb100301c00d8524040c0d03801144078288064140d14119084140e00d484011a406000c4815480400c1c88225041304c002d90000d40c211901c81d2006201d072108030058140d1388500050a08110340055104a2140c0c8940c600d1540ea00c0034000184c0700c50034038075486028124280001090708005560041d4054000288035402e01d0100701102e03088030440f01e00340412000c02442010900480ea80143c003010020f0842c149403521041030481c0340801001e1040100002d01440803a4001134002e681000016515086080a0021075441800744030015402c2240700701558040c0703c1d001088075450f034028a0300710b2079940c1c65001040e00441140840d504c03140c20001103030450141d117000e0b41107484016a03868100d0280180c06525904443c24141008810030a048139101134400301c3d4000d050100b00000c101c90961203480d4a5007407201007103511400d2183e01c42c11080a031084d908045a80a26a62203001d92501d90030301e0102240021402c000504c0122414809071111070300240c5100d0803d0001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 817714649 1250 817713399 817713451
    0x1b0a0503040b1e07020a030f02040b040507091d010e06040b12060c030a060905042612090a0204050708090303161110290f0f01020a0503040f030b0c030717 68
    0x1a40c0300c0c000b50940442d0103924840c580507290396803072030049000d1030704070b50b64045049400c0610010b8407901080000b50103545954020b050701400050040116103005040509005501c0c0100404400200c0d083c2d01007001041117541a1003091700d0501007903841d001040044c0c41003401044c0c201d0843c00125154040420410b4051502001e04a441c0d20b00103025004690250f03010401c110304140500002c80d44060395448100c80390711203499410103404e41c42d8118419010301d10141030750202048540000840d107000614070844081c8140d494105040b03480c46015507a02c40380742c10400c045045107082d07241e18022005c180c01d200d00400403c40c1401d06107178900d890b5111a90321040040361010481112000c81250148801c003a03000b0030021070301181040c01d12600484485c030325600960700070004280e103142d10208580d030701d0f9101e28194807004011701c01210400030170404107940703031a008243e034441c1400d81c0e120750048954510410344203201038035041510740070103100c101903241 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 817715899 1250 817714649 817714657
    0x614061c0c021e1f0b0d0f06110d06050f0109080714030a1505090115060203090f1c0503070b060411090607150e0a1502181002010b0d030f0206070807051b0a0503 71
    0xc120040d1a13000102608900c2030228200b43e004d69034600f03c50041c42d99110500301c40083e03003200882000703015600d0047c00030900031001c40071855020a031030451141c55041035050300c00a858548600300d20744015950302d181805061104c1e001708100b0302c4040701c1c04d000c0500c0860010211240c03c142915041801d410884c90a00803c0e11001000745140090240203880b2038240c124507082860508025120b000e4901803134450103420740e02003625651740c045030401300c0c4030500e00c1002c50b003645001c9a403a1310010084031003602c038400186488c68507200c0c035010b19034003110042c070f400d004000b000416400003c04035164134214003681c002d119113100314466001420001e280d81c902c03605100700801400a000c4441900401400c42d0000d4518402c082001c0141e40a852449007010140e0240c1380704014030750400808540c0c5414540e1004440e205200746e902a1252501e620400b1a070a0b50b045886001146082140c6807d0859032400071134401d0100040d030f1141c40c2695a014150f45c8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 817717149 1250 817715899 817715953
    0x30b040612031e1b0303110a0c0b090303100e0c16050717070b0d020922021306031a0613030f05010c1e0c03031109060304060614061c0c02 61
    0xc1603055000c101900000b000300484035000c280402c62800400c0102031180300c4108841c00d00d141c500090826000c0c0d00034403000701180700340c7c644031490520300400114403800203403a1091103001080904101000f202c0c09100a240148000c40c209103003803145032400b1340134141d040000c01c09602581ca8401d25082e000e84620090f06186d8540055140000c1910425150320340103031404000c100c14040840c0e0a03501032007805a02c2d0791782c0390002503008009020380c80c03004101a81e0408404866401402c40f00b040c8200c0c00011615404114200d88284503404070024800030381810b03d1908501401c034464450745140b540d540c0700d94811014025404045481303030b455140004407a50081c20301c0344205d05210624841a462540041c441103440074080c2c2416034654460302d80d00c240000712942d20101405d002e0392801c0500d000401400c0900c294449a444c0700d51209183c41c0c00030072540840c096906400d00704a81f0f640d10001001040c5401056100c3c00d00c60b003070a03403000d640070505a4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 817718399 1250 817717149 817717169
    0x301020a020d260609040f0b090c0a090203010e0703110408120c01050601080903070f0303111b010605090126071e06080c0a120b0307170a02040f1109010c03030b0406 73
    0x30b00c0e007110150012070840c1d0703042a84070003240601c58001041c0d985691003403080354954a5a01d4505100c1c0d10f6503400748002e014801410700300b2014420020315400c110f0740690309950300039a5065180202c0c002130150070903181404001c03075040c610a42048070025009901d0518059440100910b030846411041e4003505011520345400002841115032020003801c09049034178000000644074403950b0401000700010095910916200c0c0c0e000c600c5031050404400d684025080d510b2401c1c448a44400625608101c008549410480042c3e4100d50202d101c61120040c0c69110301e40b84100d000d102d20b042d1182e084c0018840c03071201140101c030440032020101c030505084004047c207100500c08505505e04104083c030b140d074400394000c07240300454000100c1d1510100041c0c2001401e44c808032003084e412190784444c03000401d4220f641031085804101603400d500b602c80555082507040c101014003803007144055400ac84200000e42d20074070317000070420044070010b0300b00c4001d500000384807 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 817719649 1250 817718399 817718413
    0x5011e0605090c1207080c040305061005130c2102090a060c170406050f09030a140601081b030309120703060501230102060603061501140d1b050c0d030207110301020a02 74
    0xd00b02640c615803c0390298400354600b1003840004030b4048000b0780554200b040103800669510740001c152000356a00c0000d49100c0d0510040d00540d150b82405141d1040020329110418a0f4003841400c503011b107640c0740d410304d44062800d040700f94817210200750031081d001c000940281d500d41520401800054a960500416a0a14425138a19450307080010301040009110854005050f200651003841e0810740da91168004241448600b20380100b601480c10a011060600442c000f41610040c1c001c0341c0ca4102c02c2a605000078645c1004950140c004000c01000c03130030207180c82014143c54404035502143d983c2d503000221070090748800c0c0034110480c040200049041061910341400b4030081c0b1032824200c0001c1d4403080050902c07444102045030720345e0720f81d00580b0015100106030070780a4030303400f141d40070070094801080d6802d1041e0040407800c44070b03030240e0709841d510204080103040d1401d4480c016802076218040540700b4440c0d0f8803000390035550900040c4010032195000c1c00300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 817720899 1250 817719649 817719659
    0x70906060f08100b09060c1b120106050a0b0a052802120a1b03020c040e010e070b0403200d020a1805010506040b09041812020616030515040905011e06 66
    0x4610074903401c00c04000e111410300c0581400d01007000305403070303075031520607503c1c20000b0003d0b58034444c1c441603002c1809010040001c0500605080c10380c8482525100307503160040610078200c460318001e49600881003442404951013000107895020614181240307000e42d40e0303d110302d0205110b50505200b0081c10410304000b80e040c02504d0141d907404c0c84441c14480152400391502c6e013111500c050440d85034503658149031007040000e540c80c2c0c001d403007003200f02c03c480c070f40300c0c0688016190f884a40c414001d00040001d6142c080f64100d0303401200118143e89198001010b900103c001d0981c0070940003215800341c2d4401c10601c0080031080071802036100c500102030160f804c1607111500c20380d02030100700101e08000e0122410484201c80019082407c03008209108211220152108008038a42c1020980000c0d000d4000c461491905659404108048040e00d004407900c101c01800001aa00d0034103040c0c00400c0e40c5440303000081501c28202126440c408d0017030f14000886038440301c08000d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 817722149 1250 817720899 817720907
    0x50115030c1415070f120509030f060105090f04060e03120f0f0103230102040e0f071d010207031e050a030503070e040e0607140c0102041811090108070e040e07090606 73
    0x1006000c03840401544510b1076000840c2001c81c5030900e119094000788a500b0403a41d02c4610403016403100703101e42905003a2078014102d0f0020010076000c2c0c400c240c0da13441c1584000400d241250310040000c0b000c0d942e41d00c80b480c40c00d00054003c0f25030940b944014032040c44240f0251400610a9142541c0d5241c00c0482031015000900380c03180441c2d0010041c40405c040b1440d480c0403094000610035514800541030f8028483c55001c420900521030611080796082c1b91079a015915660340c03040340d440c041c055171a400c044a0034a03030150303200e08402c10009046403018002c850b1488120380e034000090303e5039030902c9003080342180025400410420301c00e40124a6402125041d0380c04c0003500b201d51115a0341c2c05001d40800140b0001d02c0f81040c01102038030803034048190140c004c2d910f4680d200880b01d0742d403e0028040207941d003484445c68071401e80b00305560050030305a4800c0314a40716454180c400c411020403113908540c65803001c1c007581c0300c00c00241004018001000070384034a0428014 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 817723399 1250 817722149 817722173
    0xc0f1e030e0906090705180616050d1b020f1c03110f0a050a080c07030507080604020420090f01030e24160816030f060902070312050912130305011503 66
    0x142c89003103840c061002c0c60301c404e98a190310102d00e08140d0f540340011100071040c8540c80d00201d41c482c40c000794911012251840c883c080324482c03070854041881060b4191001c0600d805180d6516540c01c81200140c03810034070041c03003d03030007500c3c144502401c04501001c002c0c082ca004d80c040b038038000744015100c50422508641c440d1403000b0b020001950382e50f41c1e0301d45140c2203028046c0400801d01a100d0b403014440c4130700443d03001044600c400c0c0d40e60240c64423402d04603400d13407080346010701c0c0c0e50001a1402d100c52200c400200c10300d29000b9528100902c040c03401c1011410141d64040d04051503a0411291300c47c488601d01c01140d1446241c0c80007200c010080c001045207000c90b95440300203401c807803a640c0000304c080800e9100040058210001d06418039608006400d00000060440c0903a00611038607000b03943d044603628049403c02c0079120241c0f032080e01c6500500003090f880f028040540315031220f480309802059540d459403030940b90102c07072005020b44000c2d4108100725810f0302c51 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 817724649 1250 817723399 817723427
    0xc1009031701090b0a0f1a071a090f06060f0607120e0402030c0c1c0c3e01021b011b060207050a0b2202013615020106050d120c0f1e03 59
    0x1c41400347c204903018544d00d4801404100c04440850310504011140d0fa0304030240040c6400c0c4125450030701001907481200004c4a40c0c0d034001c0c00003245441c02c002846550b602c9024051614000303040e587d4005400c7d8903145081009180c1003000e0086c0d986000660007640084103d1307454000e00d90b030302410000002c0e00041400038045010410350340160710450b2140d0842c100f020b54201c00c02c0c0303911402c1581000a2400d000020303030060100129407204005060070390848480b08000142c0884e004d0001c2420360216103010140074044003c0101c00c03c049100d40c40160401401d5614a4a010200241141d07040300c841d00704a801c2c2c10701403561020b20307008400c905030308049800207480d40d07030480044108a020143c1410500c403603080541000c003182010312920542d6030080ca458100100794540041d420648002018902400704880403900254851410101008141c40d50050050200c4445800240030ba011502c612a944407091501246074020045454010309103a0b2221003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 817725899 1250 817724649 817724669
    0x2030a11010f061502240f06010903060c0203180303030708010b0d0b06072a150c0305300c04180b0f0a090903030506121009022d150c1009031701090b0a 67
    0x2c56180c00c8804600d00d87c0200041090940d0740d1201c03801203c0084943e0005040e00341010341c0c0482c10340d4008010159490300c1c80004030286174500405449100588458000a080c4801030000b070344c8400c01030041070303201500080c141d8281c401140c032640140e50300380c0d540c0082013000050f44180350313aa8240c2030301ca0381c400c2c03000c40d05060b00c016113903001520010401c03172011700710000c05010704122054420201400d5050100120060075148540ca0000200b92040b0700443e01e80c040b000156026900d015656460204c0300550080041c00384100d810b9002d4000154010b04d81c8580c580c80000d41502000841ca1020906000d000e441000d40000d0003184054a40105840e010031508070366080c400012840d55224000250700c001c82122000302542a40421000c0700034001c00051440000c1d115004206408180385c5c480b030040b0315980b01e017a00301c01108240c80241c3e9004108091207800c080410880d11803034074040c1c54090704031614030f5640b1034690100d46002010b403030050285d004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 817727149 1250 817725899 817725943
    0x71502250b041e050904080903120a020d032703022107020f0108060411040f0303020613050d05030a020c030a030f0f0608100209030f0f061608040302030a11010f061502 74
    0x3418072402d100e5446480e00c400c0c0c00055007290304401c1049207004000c0104200740320b040c0790070700b01c84070303440090b69030b00c21701c20f5258140188401c10240c034580d4485030007810302c03200104819400780081217040c8200400380c40141c0041d08460151001d6a80a68010308001c1100121203400e03000030008108210070602645005a545000c84c003280c03007080c68000145d490704000303d000381c00c0c1079a075080d9014012a001c244906e29004840c01c8174020b0382113809503110505550f00c403522882000d03000307401c882115610701d40248005c6401034181000145080d2151880c0d500315044040d10800007a1141009504900c0a00900e42c4039188002c00300001c40c581030100381d580d29880510240c464000c90030040c42d54050202040d01413881c41074a00241c3c02c50381140d10f6101c100c54071102c0c000c03a00d185400c2c840c820206288500d906400851415007445000c2d40e24284c600b010a10564a07030b03003100d03204400740c00f174003000300012200b810031544800c80190400c50203680d60100e8007100750f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 817728399 1250 817727149 817727159
    0x20c12090a0b0f031b09150a12050919080c030c0a020a0905090c100509091005150301270216050f06090c0a15181d10051e0307150225 59
    0x3d0122a044071110030080e80103007424021007206d0040640c500e07403000c2c484091110341c41c0020002c0c0303c00c0d03540e03903105907075151040841421038000355580100e40e80b021104055611000c0110f207030a501030500941844084480b42d407940e4024103041c0c51640080e0303480021428007200c903074050602c590081c440e03440e10000d2240e0715080000001e20407102c00340000c01480c002c0c2c080350038108016029000904d080c00b6000d0003001d0621030385001da11003003075400c0401045000d690694100c18130020b59060400c070140050100069020301c4079908110a4032072440b25125400c81910860140803841c10600d1700310709104008180c40d5554110940000785070759031801a00036140c45407600340c12030b03903594000c40b2228252486541444c50140012030901c107840291b840000e03110020042c9517440c0b01d498007140341180700b15600503203004182c0d40c3c4001542e6205889036406800c980c0c906954189041e03a0080740e8810f00050380100d000b00c0524440c903040245041c80e0843d40242d824548 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 817729649 1250 817728399 817728427
    0xf09181e0709090f1b030c17040201050f18040b03010501050f1203040e0117010b040209090447011406041203030b031e060709050a090c03020c12090a0b 67
    0x40840c0554040c044400182040d0150b100c10015081d182c40800c000d00031840c3d480002d1241c2101c9500a0440042c0c40c42090700c80e00558000e4106503039602e0829000c05482c0130302540207801281408001c0c0624100c41280c0000781c881161145d07001c00c7c0c0bd85406080c48100d8150680041c040d0741400014481a102c01900b400450401d4400c40103a5016038400f60450042e604030910729082c24000040428074030261400b0140044001c01142e0043c40402080b84034002c1c01c2e0390098202d000040200e1044440c0c4600c441e0103e0391805405c00015030548403c20781011040280c100000c8000c48490484a15016200d000b090140c070903600000541507028501c1500312502d80b8003004802c05110390000149280d0240c211840380000940703d41c03035550b02d9240010103120b480c0c00110700c50b01c80d001080884501910400100341840d1940000d0000510580b0525800304894001142c08000c0c40440384000314006488407150410402c000ca01075000a80c0c1036018008080544c5074 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 817730899 1250 817729649 817729681
    0x616050d1b0c110a0b190e060409051e01030515040305070b3603030a090203101b12200c01140a0203041a09030d020714030309150a0926040b0f0918 65
    0x9452042c11404900d2501700c405004804a10350408c00104001840d40b105401460060b2240111142c07130149000900046c01000d21014000fa8030601c1035080c50a045214650414000d10f050740ca4002c0ca6241c4815450b401e5800244241d0500006994074900000c8010741003800c025034400003034103d034142c2c0d0728000070f401094020303030754a000d0f404c541d03080061158000503480b0a00c1002401d0380805410081488004040340700c0400708a5209103070f100d6006100803110691001c544e850f60400041c0d0450f040000b115943c07210038103804402d03c16683e110b140e0740e260159403881e0034909224203152416004102c1c1e4624018090f0202d0b01009413036010408040058030b07200c1c00d080000d6038082d40e0301038a559010000602c4061040030605083c511010300e8001620388a004041d002c41d00f880340f001e00076400c0032616006841c099043c0c602ca03c5210640941010b4a4600a99032684501c292001c03620340000c0d028554103081d034101d4507144442800400d149888110a400c5043d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 817732149 1250 817730899 817730917
    0x1170114060405101e030c080402130b0d030f08060103020c0d2001020412020a06020c090c030c0405090a09060c1b020118091e0b040605060706021c020a18080616050d1b0c110a0b 78
    0x44181c81c04800085a58014410340800800c0c218904c3700506028040d2071403640090006004280050304a500038000c82e007080c80d00c8002004070510180e41291079031400113940382083c00811810342c086000340054006442c0c944986002d0076158810840b1505081d0320160035500880603c030300d903170b84404005501c08204040680d803a5101c2c035000406204e2500081e90080000f0103001020680750b01240e00e540c0f00d08030401c155072038540300fa03a203c1e4002e19620701e2001e915959000551150420081c40508030010b00003140c0c0f0b5a44841c01e860b19000a070020800d8205020319000650041c1c0307103100c50540e010060141488003003000c9100d100d001900060f000a1111000300c11010828841c3d01e40d08402c41d280c00001c900101807508070080101c00001c0d802e004100110b011449034040c501205101160b1140e200c0d00362669008041000d0100e59103840390800c0b1981010308105c0e81c0b42c0d9907600784020055241400101040c07c05403070092007031100600442e24030900b20b810550b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 817733399 1250 817732149 817732159
    0x309060c050a0c060509011205060604061d0301061202090a11030a1112070504080d02072d030507030807060513030e06030c040f09090605010501170114060405101e030c080402 77
    0x5030803414401c0c60019030200c01402408101800180194040050309100c002603032407442162900d0070220554400303a400b20b5200074104010440c00b0700802004002240b0702800c81000c0071101e0000707085640310b910101108448041c07403070451500f0f40c02aa407142074810300b00310310004600041a2401b004001c540343c507546009040c0c42001000c10380b440040c4145030140700b131501420041c126049403041070014070074005030903407040c00844d400c03003580c6070742c500880c0b119280441441040c20034803e003900c08281c1040400403d00030721584000d5401040c585907904141d1404400310744004280b4091010a141c004000a90003208025152000c0390815103989030746000005903ca80e61103c540c0c5c500c030140010b00d088c2d050b007010302c2480c0101010015a030780c90005440c4401810260b681d0119040e0040c0006442110494401c140c0900202d06050310349010071650b906a82c0c507240071500442d010f88004040c91100c4841014070716051058071600100034111500c003800c000c0c425 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 817734649 1250 817733399 817733417
    0xb0f0603153621070f080919030308100617060d051903030e06060f093105030304060b01020f07092a27051305040303141021030906 58
    0xc01809440904100c1c11550500b01210b028600740e40d40840e141079218040c0b00361000450b41e9001c029604081d401614051220707407582da03212840d611130302c00d40d40c2c0020030380d074440701c01c3c03030814140c1000c0d5100b9224074450b07041c10040315405c0101d5a00042c00c000300c0308201001581441d40e140e801140540d4801c0c01c0c1817992800604101c1468080303000e9118400705081410b5064110001c2c4a40c42ca05898050702c9450a00c103e01c046d260040f5000500321000c01c61098104c0d10045030329201c00c01d0035506e00074001c030400321018505008d45403130b4030110502041c401359218103020002c00740001e14001000c81c02a030b4950f0303001d1144070101583c403140d44003c03050340d002c00a00741080291060300e1100201c0d01800b01602c2611081c243d0880703401407041554018410401d0322801420490184079211201c0042e21000b0411010161a2800fa01e20b403242002800d015800c00310b0280340003803e00a829075100503000d43c4d604c0440f01b600514010941041250080e00c9407460301e1004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 817735899 1250 817734649 817734691
    0x20304080d0b2e0809030906030105010c11150315030703110f01031e1509050717090c2e0201050f0105190308030c03010f060f09060f18030b0f060315 66
    0x100514104940f4454200300800340203a01812001403602c1202e8071101604d40718034209039075a00a9001c0103801000070001072080390702504a420b0010b208860070a1803464440201d0010076203082d01043d030b03080200c1071140c0c00c00d4100a0740ca82410a030b004201c1e05296458402084a103e513989028990740c010004041e4840c5c2c221801900c81021050400c1003070b0f107400001009040c01d0100c0d117105030360001ca6881854054903001c0c0d0b40070b5488014114046003440000e01000c3c01c80303c0144142c108281c03c0e620380e20b4801324150480c10021075014002c1c9042c03240940081407050469240404005460422014440c10b44405840400003003900601015014071a600302a0410001004011014030008015030584079804000780c84117603100402d071050b1910307828120104da100f500a20080740b0810b4003054044481ca090b107210f000e602c5109000040720380041e01c400c0203000800c801d820300e40c40d107690413210039401030800ca0314403080e07100078410143c00540f22500c41601452 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 817737149 1250 817735899 817735909
    0x21003020c0f0111030a050708070507120e040e0f0d0c031e020a1401050a0c0903022d130b0a050a030c06080403180e06010f0f050f0702040f020427020304080d0b 71
    0x540000c4142c02042814607050788400d071303a001101e0004005082c0000151000c0c41741501c03901504403604e6081c10324016a035035814495996080004220300c41043d01c00b15500c030f0085204026144010340b10516140d80800c1c01c007441c2c3ca111409001c1e0340d408000020b42c0c0541075024010410090000d440d68281080b810079903c28400762036030007407103008100381006600c50780c0a240d900360b04214180550b00f0a44003400c035440701075130101c4201c605102100307442d000c5007a040083d145c0c0000d194441310000343c00e98007400d12901090b5481c140e0317500a0409001500144c041142da0103c100d18594880c00d9000382405003004002411003c1000c0600a0303011500c24502580035104003511084c3d46e1240b404104c40c4540014212401004c001d03004565107440e288865030746900d801000390103402c042c0c2c040101282c0055440044181000c00c41c030141010f404400406150714507213008000c403030042100583d0320248100700f07100024200e00221988150118001320b8515041400a0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 817738399 1250 817737149 817737163
    0x51b0d02070b1b01020f04081515040e0a05030d0606091e05010c0f0c030803150d031d13110a140901020c1e090103061b05040e01031e15020a1704021003020c 69
    0x110780d560001c81c0c0482c440d0003d1014000b41d0323110004603114100300d60205080d59400750740c1120380c040d40c540c0b00344a90406070420400b05403c103080b1030031002d003541c42c00e240d60302520241d104241da81ea41800701e20307403244142004050440c141146100c0c241c503403d00d070707000a00c00c0c14180040010058100b240501040780130075000101c1c421180d50303e00303218607668011513841c803041d103070000d10410314a004041c4440c07881c0c0640d54120449454a13a014040400102c0b413540003084180c107000303c841501444001c062051111074030707240c00d140301800e02d41c003c0c149403141050920201903e070741d0000d540c07801c1c9002203d102546482840c3c0200c40380e05841e01c140d41080940c00080240304950300211020304810f10f071130000004094084a4900483c0100e003190502b101c01000440c01840300140b0401c40070b10a5605040d899481c2c01e1503001c03ca0039446140d401040c15013090360003403840007040224600901d1545440d40c0041d0454420800c542d060550101d400c07854840100310744 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 817739649 1250 817738399 817738447
    0x10506150c160906090c0201090b04020402160209090312130317100b0c0106060e010c0f0f1a010f15031e1512240905030406030203060103090f03051b0d02070b 70
    0xa000d0203515020f582020703000e28094102114101a00c90030709901c14803891841c59008880383e28540c480b50b0800010358414510b40800d244031020780005a90703403185031409545403100842e0b48544664141800080043c0302004042c1400e00c0320001c01d4006000e00328001076025507502941d151420030406002c1c1c2d40000f4003c16000c20038101e0310b82d055010300c003034075103d031034a200801f21b64004580c24084004000c04c12526901141300040005079140701980c420007400e00c41c04404d10912b105003900360b101e040003180d460400c0107400707002414203140c400246002d00c5490380203c80070f614096159405001155204105024100c080c60128050154a82000140c3c602030070f054418820810350310408152803d8071481c11421361088810180d48031014504203460924250300a4100a2920b0f05264440d524800000d121901020001e40b0036102e26490708416443c0c2c585116825201111790740c0002c00804005800190080444450401e050341d03900c4070307840503640c015602403c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 817740899 1250 817739649 817739683
    0x5031f09050414010606050403020f040b12030706050714030114030f06010b0a090801060f030f1a010603020c06180615061b07080f030906040509151002030a03060602010506150c 78
    0x1000c9808002600031501590003030b0303c00c0906400c25060f0900300c402c3d5100b01c00c0441c404120401c010f00784512a4000590000e100082c9064071101060b8002c041d07041244650b000042c0403800c2182c1d40c41895008082858401061800f8018101c81c500c4107000700040ca801410311078039559410400c642c554441c1030709941955a4801c1000065000078002e00e0106104000104511905104007c05c0b110852a01c083e16499921501d0307240703103a000c0036110401440030700000c070340341c10603144d0013007203656801603603400b0b4580202d05050001e454090904030300f40c1089681c0da40003c0854024110492032419030719407100250303181c42984056031440110070109070f11900c010511200300c85410f019030303441000030080c40b51648540c940040c1d118800340420300c081c4c2400c056a9034000360010030b405041c55441d000980243d007480080c401070f44002107400d810303540b6001d441300414050000744600c0c03d01d42c000030000950440c02400b00b440c007243c140d030f5003082001624032803821424 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 817742149 1250 817740899 817740961
    0xf0f020d0e060702040e0d090f0e04020a03060507021c020c151216031d0106212d02060d090201090503030a020712020f09040308010306200313171803010b06190503 72
    0x10180800250703105503190310800070320004ac1c640150220f644106e5004204440d26411a0f407180e004110250800c01148a03000005100c10384000704450403000c00c0c1c004100041d1800c0c2008140d100310310a00c0c0355400c00780102d0008000300c4070030a420540800c4c9030440340341c101e0821001004c00e0328218405091080300d0050f80c00d4103601ca10142e03034540481d47c51800d248004c0144060182100030820150135441003104002464009058101204080894040b40d000540c3c6a0004900f1000c496900e1040710215a00300d62180c1c01854180d004d1410401600b0029407036100354483c2090b07989160151104540d24064500300e840001000040d25062074200104011400d003c116862480e2a240d00007986080240c00099901e842089d071450742c62000384e02c3c002c168103904558407441d41e2000c10444900340c024014032603481e80381ea010124014100f50a41c5c0602d5446802243c080001084400b00d980d20b100a58080d400e041d642ea03110400c5030400c03c541001c8000c42d0704d0b1002 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 817743399 1250 817742149 817742173
    0x9070804201021291008041b05060f03100f3203010507080906061903140703080315011205090304062712061d1f02040e04030f0f020d0e060702040e 65
    0x18070711281c00403030448106150030a001c1c40402d03002805c9007004540d4610000c2c5c001080c10091382942c02c414210286000e640b040031400d03070381010248003010180030042000392880405000000d1102900a46d0298580200c0b444d10300d945026204103400d500c00501c2313030403401d80b107102d801c0c1c0d001400800c61740c03422030801841000d0a5030803c0d014024000032809503d009845014a1244040740118091440e070307403a07054544844002030a401503541c000040390104e00914802c8203d0004480840072180005145800490101100c14a8641444003641d4000305407003c2d40c0172820301042d400b04914a034040040340e190741c50780c4080440c0c408902c107602015044003481c49400240032a0110508510428410100a503030591185e400361940380c270101c840f03000040014400624194981c1070b200d417685030481c0c094000c903411030074130910701303038007040c1614141140e101408070107502c0c4000400c0c800c1100d0b95207105420104040d819960345070700030b44544d29480308071030080100d4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 817744649 1250 817743399 817743431
    0x90b03070b0403050f070b07122607020105060a1a0901031d010207110a0909021305060a0302150408120313030f031103150405070509030303040b1509070804201021 72
    0x444103001183c006c58400050300400301c4183c5189540c009007403400d079412000c040f20007404014074400b003031851800c1150251611115076026040540c004101031a00c0e4050102d9458203900000041d00d01f4105501440c4142095034481002413801184281418080380c410300e40d9240501e4507548002070031420440080200b0000080640307103e12116910441c09080301ea19030380283d005075813120070032031800f465484030b9842f210040280f024240c8036004240c0d440400d861145c0110340024041c0f2419404004480300841c00303c010a20710b150011417901092004403005040c011484100304403a4020b802c504014240701001e1b503121300d00307240c0091264011206071402903191201050809104108641d002000980210310f50303226542c417503001d060000e140f403c00c0030850070340c00c410781d03102c695050184150344d540000600346810012030f0000c0c00c90740005c0b41074406050410507221020074064000040c10013085465880c103030880042507110782e00f2481894010300403180440 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 817745899 1250 817744649 817744663
    0x1a191a0c060906070206011409040f0303020415050405090f0601090303080a140a0c090b0c0d2015070e0409020114130b300f01050603220c150c02060301090b03070b040305 75
    0x2145d003101c0969a0b1622102850a024124550440ca40c24005000324510422468103a403292500503d4141c2d41c4034202240b030b45013400d80c400a00002000c05c1146007221109801c0000d024031a40d2901380600081d003101c0d1984001814006241c0000314031840c0e070750110040f610180e103124890314002140c00c004010850300100070507420720010404c0c10a000a55100342c0da5103000741003070080c0943c03c0da20a07500400d142c140709070b64078461003510703000d1000e114003503840c1641186a0a054002802529400078050301803403525096002603a80444803840440319070203140c1d03569225800520207a8055001034040b880002903030503040341c098900101d1040841c0d04c0341c0009800c403107107092500f025151042010305100c018030452810000450b0082000c02d0340180b040341021801c0d80041c040c04040c0c40510322807070104100b8031400c0d0820112401840d026841958560005440340410b0281d428561f80c2c401031480d6139181001102c02a01180840c1c1c0c0d1941c0c3c5d0b034980180d0f1245 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 817747149 1250 817745899 817745911
    0x40f020102100e1207050708070605030f1305030a0302030c3a0e0601030303020918250c02211f020307030b060c030406120906020d1a191a0c060906 65
    0x100312034102110b0031040c03065494024845000d803044d400f1a0100f10b2150f007050b038050381c46016010001590b60b404004010003800c8a44400c0d480c2d00e0841d803640b895410040c6440540c80c0c1272414140007507800f004644508880b07080068481c1c5a941c40b050180c081c3d080b16600540c082100c42c00b061072049129a00c01e0b803a50080d28100340d4519024003610011184013070b4650104c0014000240079802501101c940581510300451130821164003142050b00d00301d2070450080b0180e01d50918a44148400b02550305185040c83c078250b02141c4407048241c091440e108124040018041c030502940d2400781d21010421114840c8040d17420096005840030b80100703103020b1b0200c0690030010142e4040507070a001950525103000c406031445d003498012805041c2c2d4641d42d51000402e148003400307000c02e0800001805403100800d40c0b0020910443d5584a141d21071441c460b411083c084040c10f54110400c003481150700900584c0180c040c044001d9064011402001412040065030500c034007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 817748399 1250 817747149 817747153
    0x604050c040606080c03040f080d020c071202010c060b040e0109060b0a05040e060106110c0603042a1413090f0528080f090f130c1206050f0d0f0b040f020102 69
    0xa03600c10104001c0700e40a10405000c41c00c048001781800b0080f5000c0d65115028505415000c0c0280d5500000c0c9d42c0178004210f42958049082401d03000c04100507400b40c900313058805016583e640018081245071280108519121001e4084584842c0c011815007002e05000b844081c4403890064090300000b00705a0280c14051300015051800d405407806a04021005d02800d900340103049840d41c0414542154038030070b40880d0502074a0307100045111318040c0103100d603400d0340484450b40319a03160b81c0000803880002d0b010b0100e08034800030aa0400001c540040d003a0040900c0107014100143d009480909906400c1041c41008101002c043c80e480c17078210031100711719086081c61900c503000a480500240200413136919800001e100c2c8150082c01d445c51640000001503d0026050048074440e84a14217010b040e43c0041098482c04030314402404001d04142c0810004541050b2283c450440340440ca018000201002c003117043d0803008074011890a0704210080681d055002c038014 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 817749649 1250 817748399 817748413
    0xb0a0207051203120103030f050c0a031707020d0504170703050a1103160303140c0c0a030302100b09090a03080705071a040312021801030b0f040f0c08060d0b06190e0702060405 77
    0xc8008400c0300c6143c044c0c00321076420350b400e64a08843c0d0b00e81400d210000d01c40d040007400720001e000c204c0104601d220750394079150903a14590803803014074058803030015075012001d900060398000d401e441c285d65a04a0002c000410041d26610f01681a40090100c0c02180038030307000c4c40390707000c0f50060035501502107620494000d90200d41443c4035220144c00901078072001c40484211000400919041008070380b40c10030101c0c005500d00c50203070701c200d016074004244e02c0c440704401c1c0259040000112124030140c0b5050002a44428140000500700100040001c1c0600c1c00303181907483c542e030070a060842101085074114110b20041e1010b5021540a0918041b2010180211074411010f410060f00e0707001070300015005412800e002c50740c0801d0444c10401e0a07202c602c2903450342030f030964001c01c40d803507600710160041e075010700124001c0001c1071070800403642c64010300c0c0d00240142c41c406458201c10340d13442c043c000785402c207030541c1c03070081c043c0001e039980010024000c0b03014400740c40742 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 817750899 1250 817749649 817749679
    0xc1f09060e1c110a1b03050f0f190201090504020f0c0f030406020c0d02060904050606040801110702041a01091e051003022110261507080f100b0904060b0a020705 71
    0x3c900d0724280d804400c0e0300c0781c01c1c03840008400550307402040c48000310060486859039102410b0009055041c1c1003039201c1400840d0184040111030941c0c02e00702c52035a4229030300c5c2c00003440c140b00390003044d014035000200d0440003200070b81110201072403401551074034103205e08040d0301c80d40309200f820700500c240300d00d02c40d8030710700341c003408060650051026103800c59402c1032101800d8001c104a9011005000020f9055001e0103030740301c2001e244580130743d204003074410001112080603600c05403101061200d403159070888902d8060318440044003001c4103100c044e03a050800c2940041c0d0304819842c443c0380741d0a4064001c0c0542c1c425802680311141c1e07042c003021311001c030101c42001c1c1e000741e04da00405c54903207100403c05180700c40001548121003144c141d01d00e814030003041443e00c2003c00c0c04010701c19500c014141c0d0804903a80c0026101e0070b0010074011083c441d40585a030800e0001405c000d03994466101100800340000c980d900c4240d03071070010307448151a12549000301403404505030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 817752149 1250 817750899 817750907
    0x7020102040f2d060c060e0a050d0813020d0b0a05090a0305040b0f04030b0108030301060f020f030a03231503211801051308060105150c1f09060e1c 65
    0x82e40c01c80400384400b646812010728005403c0d41d60000b0001d15001c011652110030b09034000070b0036881d00c507000160020310b4580100c8034010b41d1070074550886240c00c0c001450124081001012a00d400701d40742d150f0100c44007291a082500960180280d18040c040012000301c262150a50601c00c1003642d8a0250712034807411061f030000e00003841040144003810340e1002400400b0084010981400e4030b1f55140c2909a400380c1051310140c2c1302000403c401a032024401c50006154400703071020240c0e110740d1035540e01400c0d040c2004d054403890300c868407100360840440809000c0809030f40904116102002401c000d5230b01c10702078020023800070b1010041d0740840c24020074200740d480c40c1c5400c005002d8103c000240e0814100603040050001c80c00391640c00307401400d801405040a54500300c02c0082564940000801c811014030010313403c508040340c1c0d41d40070790b8070200d0b0719a120f808032480740c0203081d104401002e01c1d180c890148900e0900182c000100d80c5803480e40035070300301a204203072 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 817753399 1250 817752149 817752157
    0x2010807030b15031803130f05031216081603080a0605060a080f0a09050d0801050102060a0515090627040507120b0a0b0d06050c0706110a0c080906130b1207020102 72
    0xb0b50000c1d500d464815000d903c140c02180c0c03006140d00e40181d00352082100f1801d591150b0710512842001900922914000303940c4d45008207822002020010100c50915016010b4a9801c114800002d4120300900500d0000c46002d48900c9000b02d100740c0191401400c0c0d0001600c04000c1e051500d2f02c0400c1e40e00f010001c44825105a4441c002c20b40d5600c0d10703c0e00c07544802072040e41e4990700c07090f410000400403c80950401c240361103082c1c445d0f0501c1c000a1400034001d040540050404003480780301c030b04103c041c428034541940c60001e1961004045400c0b481100030b46140816840e440c4180301941c04607850280e0711a2003a113007110356401001c0840c42240c44064280c0e01c0031400318403044070716480070b6201c04020301114075000082d00d0f040101c030021540c003056030200140d200c0030803030302c1d100c0c070034481007080001c0d0b0800040140c01072494820041c01468104002840c2110744c6d81d007010f07034651101a840c4c0150240c1c4480d44030a40390000006001c4000744540801c8981e40180299 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 817754649 1250 817753399 817753421
    0xc0216062c010e061b0f031909050f091e0a0609144c050913120e0d050a050c1009060c080a11100c0905040e0d080606040b12040201080703 61
    0x900c0910a4504011640e030040041c80c17450004101c200c00103031421301440d00440e00c80d1010303545541032050042d100503403444040040003200d500c144a25076580e0038107003c00c0d9068038007003401d680f592580244420304035412441f000580f010045484a82c1d0484826540800b40500840c1c3c2003c5c45d005401105071204905464085d010a2046519003100200549082450700861500da42c080c10450039400303421100d40180d240a0000d4200341e804075030001802c2c0c00403994813009072600c0c01e40e840c00c074104404114407184840003990f208203606444a820400b625030b4020140f03070150f078813007801c3c40942c05244144003c0c55440d0050069000715000d03500c800380c0c0d0b4100c039920380003154081d41008092042d206c900010303c00c4100101002c01e40c411b00000342d9000c4011000e49151f101354499881a400e01111812040d40481d803404404203505200c6a81e4490100042d514000c64100544d094800700c3d01483c940108190303280201e0003a21192a980c4580c8000c0f0159401c0c01d40d4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 817755899 1250 817754649 817754657
    0x80610050f01050f0d02090117040f06051f0b030a0c21020721030c0e030f100c031e0203041e120c03021e0604020a090216060c0216062c01 61
    0x100300364203080d240e8010a020514001345080401100a92503802002e401444a5404035445110303580100c900c000da2182069407805924190750703030780762010018200801003500c603c04121502c03c42d40303003105030b500700c403429030b240075140c10300c110f0581c0007207072805940790804100420f0305008105883d07000b10074009410040e50560240e00196101e120110313410b00240d8001300321402c0b54810103580d446940d07004104a103206100900d003400d8414070300e02c40d401c881a444990100055901ca603c0e041c0f150201d54400c1c0400154010001640d000104880036109034544440550045208610070075401c0c800e544400341100301d207100290001d0008081d00d034503035002405135110306943d611910484966a00c100c40229041c050800011110351041d42404114680100c084025000a07101142041a04c9400d00d0707029074101000b03008070317540346141c002041c401d000084c80034a0415101000c00d60341c10004040088225802e2240c0d207040510300251104510600108881651 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 817757149 1250 817755899 817755931
    0xa0507090e071509170d0320040e0c070501061706010602150f130c090b01081302030606121c0c030f0e101d0907030e07150909021803120a02070806 65
    0x550110203c0d0250030744050149079140003590941001c840d002003115480542180020058050159021290800403501106100401031450001910100c40701c0950b40da90301e03110004c050b0102d00c1030710703c0a0069400c1100100700300d009082c0010304a002002125050383e680d20007241c8a01d0002000c1c84074405513001314041c4a400140c2a4108440800f940142680b55480203011203042d0b00c4080c0c0d10743c890300741210a43e00070001540c400301892442d00211581e500183d00e403100100074a110b042500a1201070190800149119017001030006600a0360003002522110020404a0009003805200c0c00301d00d114503544081c00c3e4010f0f100407854045007000391084140c12038041014000c0400c028069a210240307140980780940703001600900130914181004001c0c4c00c80300413007043d011104503650b8881c4148089400c002d00058440f00402d0032007114502130b12000382c0c58820328846003001c0310710800614541d400c2d43c0031290303450703621040d054450070102c8001c254010759072 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 817758399 1250 817757149 817757159
    0x170115050f0a050d1401051008130305070f0b070305101205070b030703090503030114010905060a0210050c16030e040f141503031611090a0207020d03111e0a0507090e07 74
    0x2030261110505900381241881908100e0608aa841030001792000200100401035410516148942c0050b180740101d201d18102c00e01c002c03006c140c0640202048000201c050a00c031120300c000b08031552209074400d550030a107000a000c0c000a8a400e18201c5880a0011309510740c62146083c09a0205c0a4410340303242020141c55a00014000c2c0145515282c1d0040054820302c000c60203004000280d48000c0f01c804001048550070ba08421302840d810080c4d540590f400190400c29004140004200382e5213641e00c0303c40a004203001e9900c030204500d500000c0680207900203404045c20f590170000c480440c010b00054803200600c5265011840010400c1fa02d0644080c942c408000b030122481c2c52052081c044041480100582c1c0d466505851f0841a151500c03c040d00000d01e40401e5091080341d0700014503000084030020248149080d050205003014001d002d00c410604114550200c40702c0d0210340c0304c402c828021110350140c00408168007030244140d2840e0203050001302504c42c141 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 817759649 1250 817758399 817758427
    0x40b0108070c031d180108010b0607151a130209040c02061302091e01080307062909060f04050108030c0f0f0a0b071103030403030c110105011a0a051917011505 70
    0x54030081c442c11a409140b0440b43c0c44256514400c014080050f04007585801d00c01400c40c0c00c01c5000341cac802c090400c285c0300421044011290740d090101c1e0009000503101d090190100604540150015001d030040501c0f80305942c003500405a00b501e040c0020700c2052012130301d842085a40e0182096000c1002003d4200403401540c805080d0741e2882d49045405031f01a10340c84241c1c0100807540c00003940e00d080101034000d11000000300c82500b00040e1011b12041040d040f10f86215004411040004116603078041301003000da03101410030005542c55200d0f241e2268400020070b8030520400792080c09000e000101c1b600d22518100250100b2001d41e910f103c5000e00141052041120845411002103414801103004600c0307628002241d2501603800b40006981c08450800c03030745071100411404000e000002c0a04001c102c7c442da58003070400064a0382c1c02101424241e000c01075542d501581d8011244083c040012030034010140e0382c6200d0f81200c802c0d41510207000401c1807012052072000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 817760899 1250 817759649 817759667
    0x12030315010e030f0f07090603200f04050412180305070b0f0705010c051215090a020c030708040915080303071205060a050303280302040b09090601140c0c040b0108070c03 75
    0x14942414506070003800280303400d50180355940e164209030080700700d0840170401107000f080f2a01f024402d07a803541d2180207212480c0140000d04e0040050402c619517188110220052303001001002142001c1c03c0c88101c13406200180c1c4003049080003242c0c4500c00c2500d0007000c6079401f2005216050801401521a800c0450310401c080c000344440310014100b03020360100021107607103181d11341108840a411540000d8543c00c0e001541b894401c2c5103807a040b20f12a031000307415401681d45c0e401c4201c00ca16612a240000c2d2039401c0104011908038000d41019280d5001c1d1483e590402d51070b10b645030344034030060b1140b070007040300c0400b40f81040c400343c1c0043d94420001484a021169a040428210340c0041007092007441d100100c03445140e0915419807510500b0325003141828205030031260b541c801d540c0750034401c800c150001402a032081030384031080080c0030441c030b0f1500002100380303540c1e4100d0b00300144514145603c1800c035510801c1ca841c802c1c01d580c1d0b11844c0100d40783e00d00b80c4507126 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 817762149 1250 817760899 817760941
    0xb0603010306150b0706021c06030209040209061f09050a09020301050a030f1704080f25030204051f03030c03090e06090a23100305071a03070f110118030e120303 71
    0x10b11460b00150400c0c2031000717042564080c0d0700140e6200301c144400c0c040051300c8550310f845246000400c0c4050f03240d4007000790b4010b50560307540c1c20702e4542c180000c41c54001c0b144001d43c00400104e020201c076900100320360071500107540b80e0102540360481a000c2e800240142c40d00110785000c104041103644480904035030244401042e07058014800d041c07181c0c06600036407000d030302ca0328400c1d100840c1080b030101120441550988040d48a28202c0444c80692102034032441d02d034004071f044000081c3c2d03410b50040000740d80c0c030801c640e40d280c060400303054008140c0228100c6540001d81d5404140060b1083c40014107681055980d2006400200300e5000c88c0c4c07a421480e00e80c4807032440b954080c011300401c1103070105403c182c5180f170581d2030540d50f6000740b080d4580780f6489000c0c000c851401d0700d030002c510313040808260041842c21211380700b5403003074003100c0d40c00c1c8000d2014040200100c024494020742d0346480c10044c50b01442082035807c92081c400350310400008440b16400100e048aa80b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 817763399 1250 817762149 817762181
    0xe12120f0903060c0702090f0105031e030904090f020a0e070905010c030e0d060e1e03091c0b010906031104050412030b030a02090907060f17012903040b090c01030b0603010306 77
    0x1c5140310100e49890b0302210120808400010302c6000d614000c40402e03885940c80741d050b1495810103000c20f480f4815042030880800c0800c201b503500c1d8000303005594803400050410402e0030500d05280c00c02c040717034010590003503844210104180300c3d000c03c10742c400c0c412034440014131442c141c011550301505120590810110759260983ca985034511082003030701038080400c40041c03d4541c07074104040e0907c2c0d0b19040b442142d80011020010050f80d0030307280200c614810585905150341e613440d40445000b01003001d81c3c00082140d02d02580b1030002e83c2c0c00390012035401250741c42800f00b00c80c8169009840f8400c85080031407410700c41d030844102100301800751001403259a010800140c000c0e56071007081d401400051109a80c04494440301c0100380c5003040c0018032802d8000d24201041c003c403400d01c1c22a080302510a002d503460424210307131341d0007515624a07203803c100c0e0120106482c0880c4d9070080313040c2c5000c591710078040e144070100010a900c0c550303482c0d070365240c004004952200d0456 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 817764649 1250 817763399 817763407
    0x100302040b12060a0807050306061302070c08061501030614090703020f070606050907020a0b130503161101080601050c0d111204030f060506012f28030e12120f 70
    0x4540e0341d030103004058040096003410b4140001003101014940c0c004079a1544078480030440d5680019219070016815134090080080d1602904060b11a104014001070f29990000990070000600581f15172040c1c01088010030150004500f5100c4a225641104172015801050352424040780742d000a55810010729001c0007640106564102000640e20641d61307110030000b42c109010b12951100c0c252000c2c2c503c5001580d04c3d4585080082e104000540c400b91a41040000400849440101c6004a1500c102c000c3c540303422004100f400450010b8240004140c1550050056a0980d0251000b0b44549107202c80200c44842c147d81015040744180d0402403004444500244061801120b00b6030710301f101410301d139054070302c0a0065410450303008002c90408015039a407100c5d22440c0c0c11407a40c0f1045840502d4509024800e400f922801e0203402100c01500000702c880d4514429201c0c00042080303a800c004500081041e105601c2c0c00203070601200c405540024240d03034401260180c10 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 817765899 1250 817764649 817764659
    0xa030c03090b01060c031812080a020109081206040c08061f0e0a030803010f0e10030f231b0f091b0c01020d05180d0207062313051008090c10030204 65
    0x2d0318004e03072000c00440c20008008090540c89520f083d010501540250081440c044901d602d035100c90101400c0d1460110b01c45080510070340111f121280c005d22a03945a01c08a0701620180708261440d5114a03d084075496080740200c00251084100410403450111828040f0141c50540101036041040307440c038520040e607036400d088001e14061241c264980d0b04090400181c04910380280040e20b000c1c500b0012101d014a84000a03654030641141c0d43c480d403880d124048500080e0344482007107060f00b000070b0860300000d55161860745802c0c0804049040c40c188082c40d24002020354000000f030000440e9680704480c15540e10301410049403030942495411030032604110008407500d40c4070002c1c803441c510006800a004644840504450a6030890103599040c05104140c14030188020303403074220091050520405404606156491701074030f00c110b8a02c001805601e03c00c0d0030080b44000c0e1240f0690050f4400c0b94080024109a010b900070050041e04224002c02056020040820 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 817767149 1250 817765899 817765913
    0x801540213020304020f0a0f030f2102100510240203070b33060a031a030304121a090601060c02061908060f03031809060409060207050a1b030201050a030c0309 70
    0x40300d5480071000684a003411320400c04800c070050092441919030410501010b4070040340c1c24200d030f900c01c0c070401c4034005914007030040e03801798808030111258a09642007034580202d00350415004c0b4540c200800d5503405c407481e103159814010741c044144c825600c2a400c1c44210014110081c8500442c1d040c07130603559a109080b0703412103110304c01c5502510b109850300300a003429012503800c00360040d81c20034580701041c0f0701d0203000440400c05031114001c1404813104400d84181d0507000e410389550f2500e810429100c46002c04088408a65038040420f00510306540f032401a901c6401070452646000c03001c4540000501040e07034820350400030f00d046012229495084500c2503140c5940614002d0100007440c9504118140640c1080008800a40002950382080309084403103080030b4a800010030000c207a11304000300854400909417091100010f81d07100514800c1c00204400d81c00c000516491403220310009000c180140201c0015a00907080b1041e400c08900d400100c41c19540c580310 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 817768399 1250 817767149 817767169
    0x5010606300e24010602030301050f0105071a0c040303120b0d0201110705190312020c010f0c050c06070602030118090f020402071103060a020a0f05090d0f1b08015402 73
    0x1565111000c010f4062025030701402d004107110b0002d50b00395803400340420500c884102004d03040120000d55101049681c0f00c200d1050868250340c002949406120902e1b1580503000c19000300350600d40210400c0880d000d95009284050103070b440ca1222a8015180540190001c0c0030f140141c01c0c000c2003030f0300c501c0e00c00c15100160040d4090020301e1800c003000e44060303414815007150080501405c181c0d81000000c20b102180d85072a0380300044508099080039149641545e1000300040d8000038000180c01640c10f1f12550041c051031400d4520304101200c0d0603003402851484941596409480c0550213000306501038800c24440540440000b42042c208581d684030859010614461603035000c10195031815282c10258600341c03030617002401103070007400010140142c0040400c1001090f5415081221901201e909030310384a0341250701902c8508400401707100f1441290351b40380f080c50841c000f4003030300010f0700404221011143c1c480782a251072900440101c202e241005031500f12803d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 817769649 1250 817768399 817768423
    0xb0a171b0f1c0c030632040e0a0b06030c0d0f030503150303130906170307140102160c0608070f08072a0501050612060c0f0304060603170705010606300e 67
    0xa480c3c002641c010f01210503a03000b0102c861a90444101845510183c410079090700052070192004e10200060103082c13100300c00031440c000c80b000041041400d801642c000c1004030269001e29030f02c101400304008940b01c001d80202e010106a0300441c1c0140010f6400054180c420040250394501003451940001007100404841c4070b010007100c1403510682018010000b00711207032510016880340e5900507036201a248010b41250040040d209504030744102400c1810b500d400020350400c2003034038081d0320821000c1040701c000120464410f00c0783c0e050040d80d40d10f0b0300c0c0690302d500004030b034a0701c2c0c036280b005807604030f17003a064402d80f206451403070b2030380e2141c0008203243c544501800301410354030360890905d030302c010305002c404840348003910241c84103100d8181c0c480d5079504011000d8010f5610160100003801d2141c0c860341000d01c0141359090040d4028000c00c2d94452040b0740c0c010140e100200c1081c2411414194450906c00a01c034002150300e000c2030036010f00a03104c1c1448101800303 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 817770899 1250 817769649 817769651
    0x110f03041a2a0c070b091c1a06030c100305040c0801110a1107120305030406090f080414032e0e030d020a090902041202040908130b0a171b0f1c 63
    0xa0303041c40041c0c20b2044610040b104032003500340000425119a102410b005007600003002041ca00610b440314100008a24143c0026074030424142c200b4090003000300105407902114200025107505002440385107602002d00945400458641e048005001c00342007110003002c681400580ca07042401119000f0107041e03400d980e12000400c020305101c00d0300300b604080ba00302d5007003040080c000140e059241c9415003802690307561036180401c024182d084000300f88040b541c85100c01c3c07040c80310250003550510840e401306440d0400815135208140c8940c0400407031b92100520080340b1a13500c5040c81c00400a0200350303241c2c04050242550060713041e88000a6010440701d642652058003400145001c0340111f2400f81009904161040c6060020b8002d941380c1e070400003040190740844010a01c2d8400450a290b11051826000c0c0d0226145800160014407000c480450902d125402401c1038801541400c1005076052070355007041c4591801c1c01818001900139081e1746070400031000f51524 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 817772149 1250 817770899 817770931
    0x6030603030e063610090302091f090903090918050a110418061a0111100213080d090e100503100b0301061a03191b12020919090b04110f03041a 63
    0x4c144101c2451140c142410002c010070100b0150700c2d400a000d4205005003200250303170700c80d030000401080c41e5512444a40b842c3c980301100f403591002048094900c965814011043d05e03014109400041c003102034050340004441000054402003030441000300a840410030200f030403c224001d080303000c0c0550b8040d80351031542d00c2080288140e400060300900744801c140c68031a14140e91030280e5121040300607800154019810403507134400780202078075000c603090b200003d0b034002c0c48524280700f80c0c0652600200416111024003440c80162007000c0d00501c5550044900c2c040507040303641c0840e0f090f55a452010540600d40341441c107040349000f0042c1d42da0704191010b980c04095041d962038400307140803003a0a4100c1c003a00100d07411451890150740c95a40e589140c00244942c4261035880204002c84102844292140100b224000401003022500304030a000546189441844500c0310800500c11800c0e0110091508107010f040340c0e034003080021010b00c0f1404000d5920300080c0b45510 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 817773399 1250 817772149 817772257
    0x1115190f0b12030c03040303080405030d1b0905061602010e040e01020307050408101a0f0a090609090510230c0403050102071119030302030307121503030302120106030603030e06 78
    0xa400b4000c411902401140781030913071440d0340c0d2280510700004003049203040110341406020029100454122a030410054000694482d001c00c4800741b40750102d014407100044614003030302a42c81105204140c1c80e00b01d50150700450b5207007612100301c0d82c081d40e940100720710000240b010710b1007100c2540b00c05541e1030030140910324050707403e40c66982c0c0904140d04556200161045800005003d44910054141d440d002032041402d0350414511149042d10000c0c0b0b8101c20340055259600131000d448500e10303880188d4003650802c051413606815044400f0000785410001c0c0c5500c4841e0490301c5003020748035034425003660302c000b0060b1761500c08400501c806203040300342040000482c00059150b2451654065204c0c040200140107102645000703081e12030300781c1c01c102171a56481d8031304441c054907440e000c0d0094110504011408050070000300f40140240f14500550750175446000c185e030091000c110490340625030500d20412a140d4840741d000003110105000c04003c0c80301404c0c08064 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 817774649 1250 817773399 817773409
    0x102030d0c0201140f01081b0103090210020706091211010f1107140a09051006050c0c15030108010501290d0e0a0c18091a04050a0f0503030a06061115190f0b 69
    0x5015020512500001040030240019240840d8403403c420223581e60040001071740100403403c0042d400c10b541800b45401c265000c03480d50241d81c1c644e280ca400c010b868280401840440450003000507070b000b41034500641c0107100c0200c15407010324000ca1141c0780d2104050a03e041030b8403007011070b2052058820305251000540c3e0181c2404101000b42d4a00002d0f810024620f0703206030b5007441000034015100000c14401d4050000000d04060003041c01c503040c085469109204280c41540390078004241070340301d07444082407986442151100074802e048034005aa20201140c11150703501c90501c110b010090105e22840b034020707000301030b400346400c4541d89040c0007031503480400c91400021100295082070420310074034030f11013550844ea40c0e519125281905038030b0040d150001141155080100c000011031140c0111403061098039554002541c1c03041e0000075841c8260044d100120002008480640e4040380c81e2048030798020340504030740125000d0084007201540c84900c105014282 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 817775899 1250 817774649 817774651
    0x10b090114090610030e01020a0c02330a020703140c01121b0509030c060f0307170103080901030e0c09070201061a07081e0c03030a020306030f060603100b0102030d0c020114 76
    0x200c050722107030701119100020a035102c000c100030700c1036120840d5501d0040c4254070914401c4031181c000c5503125840d0102415403009608220f00c0303400798401c12480e441402a030100701020400707011b03070003407003040d0362000b1340d00900c080d542144921000000414034000c154414401d4100241482d8151600010b1040140e6051044164240480644035174219045074103140ea00f1320303115440d0b41910000074200b0141c2c200407036016102107030307201842040340001c5004049648580811550042c2c4000350f0007424070019201074000e0201c84000c1d4000c0d0003100c070550104e815100150028400590242001c0d503c40d07006030356806050090710000740c1400d0050130b03040c000e60300701b10159a500445100d40b801030100700b00d144403803038008081e24041d240c501e0052802d0300d13142d1420032440b6000b5041151207911a00c10340100301030000001c03554038010100600900745400c242980f12001e010501e000c41c1c11840b040101c08100031203442643c00c1340d043c0c1c2d0b0011510b481c3c0728104601e2102c0c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 817777149 1250 817775899 817775909
    0xf120801051320090f0307030303140916050d1511030a0c17061017010e041e02101b0c0e100e0123010c02090a050601120e0312130206070302010b0901 66
    0x720303240d070120440d40700c03500c00c000d0701003580f200315668407100c008603100c076941d039500310b406201d42030001c0201a01508001e00c1240f09843c5510143d444020300c60b560002d9091071400d030f404034030081c409030404c01400700003030307010740c4002040150405001c0e04032901d440c030314004070f2000700c02e100111304240502030348507a00303141a40f040003c20b03c00c4481400302501c0d007840340003170001070903c0394058014140f2201e60300320f11483c503694900c10940b40c410100c0f41140c8031010040d113001e81c00390041c580340410760050a09215003d6664080d20f0700d5aa40800700144040301503c0e00018a9041075079010b0b00c5980b034240001c0c209521954580c02881e0000702c50712010303100600c4031961a403402803e00d0610000700701501480030040ea04000c2121010707401c22130581c10040561261303000745000341340aa0350164003e1040320003c0466040c4c45408020350410450100e4440d4004442c1d6048030801d003001c1406480c2d0707070014501c0d506c03680c0c044000d030b51141071001c0240f41c115038641c0108 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 817778399 1250 817777149 817777151
    0x1b17010c0807050414101e020a03030f02043f1104050f1b1309110703080906130803040501020d140a14010e0f0a0e120706051f120f1208010513 63
    0x181404017008200001030112030144210700c803040c100c02e2060030700d0394024080c1d1410f0014400c1d00c00000b074560082071002e03170100e82080c0b003030314064401c0e00c01c43c2c089a42d901041014429440208010704000740001c01440c01101c0d8408800040b8540705100d25200e801403150100d052828041035600041c44014881c41100800c0307a6075002090030704400b510305010540d217520300d410750107987c0d10b190060103540d440e21329040c010040101c014521240252620401991000ca5603655131408441075a91106400814400152003d003d140c106200d4800582815440e540da20b04a617092020100084901c1050081e554454171900c82c03254402c810804040d03041540c01030b14800d000e0428283c0c08640350015145014540c00595140050402c0d20f0024409041c1c1d1f40c3d60350030030744003580c80c84e141602007800c02c00890990301d0000980d01c0c20a0f000d503d458880035002c8185207041c3c072a2a802042540041c070000c0c01d010201c440c079180c5031410f504003c20f112140840d55440d410741 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 817779649 1250 817778399 817778407
    0x6060801200a02060402061b0604080304022103091011060a0615020a02010f05222702071e0804030b101a070201090515070b0f01060323041b17010c080705 68
    0x10b1a40890203503400b940641d2420703910001160002142043d849010f0030078012035050004010341580250300490084900d07101c845911044a001050020545811644104115040d0341000c80640000803000d040402c848070441c04210b0400c1c1c1d0440e480c04203a6070f5040140001801c01000d221124028030040c080340d2a02c1e80060501003c02c401d0009200f00446c0c21490ba0302682100d022040015441d021100d03580c0700b69441e641d00486045091880504021501101500c01d83d9000c80c0c1040702c030381d101071034034181c00300d8511024010b03545110200404004a00925059806413648861040e4201d1a01c4d00800e80903949800040c0c090f80d041103414090b030383c0076114606540040f030319110184500c0c2e030003a11910800d68003c01c00080d510401c42c107000703402c11081c1201c5194405000b03a248140c404401e100304550740303110202d503480208000c103004580b05411154500e108d4184c098582507060188891144030344403a13034544001207102984020100d030000c2c82800c00341c0c14 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 817780899 1250 817779649 817779667
    0x180f141b0f03150a15020a02030607021504020d140f030c0d09060e09280e07080a08030703050a060b07060c021605060708070501150f030515040b0613090606080120 72
    0x4502c0064041102902c9104080569590311001e03500103221080c500d0040d981140e40180d151b20020307009074404e002e40c5000030911400490704011103412404c4d10201941c2d590708102220401c1c003001e88111001d0034520000c41820011111202d26003c005c548030340c102504280341c402228014000c000e44030004121483e044500d4a5020307204540440301692011220200036440d058003080e001569105440070317000e142c1c4841c0300190344406440b00d007500c4644440c2d944280940041c0060810400250780c01c0c880e50006802458480b03002c91140e50f12946145242c02a43d400c1c2c2e8096500c0c42d0000c401034040001c0f40c8800400c00c02c400741039152400003100c6008030500a000d42c500000c5100c10840b0a500c030380b120207641e40200f60307190b84402441d80514902c0c0021a201d20844500b005108100101d05106540c84124050700f555400148100c00c96403c042006140d10f4010700e90018005006140140c01d0714800043e034034101030400320448011000c00e18102008001c0c50341d07 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 817782149 1250 817780899 817780927
    0x219080412021c031a15090301050a020403021503040c0323100c270308130602070602010902030a24090305032e1a0c0102030a020307140a09180f141b 66
    0x242205031824005400b1245445c2407072030926150039280e0001009003070740540742c04000500f015980980c002c001c5503503081c00b0381040788290f00002c2d501c564500b0703244607044075160003168801d114040d0394110f5641e9940b0041558103207101e02c0b1907903200d00c6003000c11036010007020f810000010002e002003208988045c182020b50b07500d20101504840c2004804a0890360001c029a80070080e1039440c224910310702c84005003802001e006000c0c5060009041cac0c414000d40c039119070010b0241602801326502c0301d40c0140310781310755905980e40010a1108600794810403440c2402034a484d40e80f482c1c400020020440c01102c22254007189203082211414010b400c0419660344600e1210a80982119084940140c1020184940c00001000041d41c6c094001e035000c2d6003591250052502030804000c494040d8080300400240000f004000c507072685603055684075580040000c51056401c002c40a0b20180340318401d554121000340b00c0341817070705640b448103c9041390390f05e030408690100c040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 817783399 1250 817782149 817782193
    0x6010c0b070503100e010b1308060c03061c060c0f02010606051e09010c050d090f0e090331030506150901030515040501060504020d0507110c010203040513021908041202 74
    0x80c00b00b01021000405865590085801406445407400303400e40c0e44e40500491903101420358108040103110000e12400002680713801032690415a50850b41ca240034030891049001400020011900084000c034000b44120b104988866455520841c1d2400700039080d034405034044020800200320320280c2005080c1c05074041d095040c40b40d0740d20044000129001d8901c0c0e80080e056008143c1001c400a0700300540108450002c0900d18a0f15030b03c0e00ba540c80d03101c0031200038405070410415000001c81c442c0410300ca0b024505900e18014900d52004d0580f850250000c80b600d602c0b0b201800b403103000300400c01616110480d0b01202a6045030750351a01c07001c0700524015001034010204040080c03c0d040b480c060040503000719145c118036040e44c4040d0106560010100b418401300440454010802c0c2c034200310306070011441c00b071900d000c0c0710203541e4420559040075070a00041040380007a466407039041d9441d40e9600c03024105810030b01d0840000c4c05c000802d551140c44401c1b40100020007003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 817784649 1250 817783399 817783411
    0x2406033002102003010e010e1006050a050307021e010c0e0607030522030614250503061e0901030807031d0a030212030705070806100905010e010e090a05100b0906010c0b 74
    0x4100c540b09004596541c1d05041c0108030a43d2003c0000b080c00266100d2040c12642c441f6072094140e240d0a03146009034059000e542c00080e401c04c28280b4050041d0000d54002003244101da0342e98561094042003507c075841c5141459445034801400399501000d600080a0103e07a42480c029180d40c01401d5441020041040000000002406251214595401990442414007040030103400840c0e2041044414150305001e030a00781c00003a059071406002c151031910350500d551aa034040100c01800c0f0000640c0880031070580d0000da80711032010138000c500c21414561500254030380038000401e0000c84c050001c1d940c0002e8400c91351603010710707000c4070b80545d00c0030700c4100da22100c241548150000501141b00b49040040e21a038001001d912501052041e20003e54a80e166082611005e104046001c2107010040c0804880c00946a401049000072141f0b454095603801d410407080c000031429456542c9200e08080c10010320a41e4080e4091074501e0b6110442e65650381c1c0348002801d1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 817785899 1250 817784649 817784651
    0x6090c0513140a030602030717010e28241518030620031e10180b0105131203080f0403020303180c1509100516240603300210 55
    0x141802c5911244000c801941c1c10040c19940d0780b13400000a03103007140100c0d0390076555800c10000a0380704042c040843c0030718001303000d100f01d00e84d2900c00c000f858000e96881d50003480e82c0740e40000381c014a1420164008601c6941c29000350b281110030f0711901d20780903100d000e00c40404c0104002c02440d01c100025242d0008000a807280c00c410044241020554240c0241800000f84202242c5a5000c21070400104044100076070300c44548098803002449411079089075951004d030000c040f030308604a0703080107151850812816010480381081d240d40700c43d55010403400240d043c10360041016a100b80f1504646489091035540295288001001d040b24488141440140f41c0010301c90710185408c01401050308108550082e9030740d43c8108005841405e4100b5902001c3c2d00071025030f5a1443c900c0c102950b400c04c076448121400c000030700c01502d4a00618034102503402e0511400014500511083c41010480c080c12034040b0103070344480c0d001002200f80e9803800340c1e0000e61203881c8018008 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 817787149 1250 817785899 817785929
    0x1101020604210e09040b04060525080603030c030304080409050106023705030a0e090604060609031205040911032208040b0c031b0d090905070c230a050106090c0513 72
    0x4802c0b00c0703c2501c41e100c0d60f84401041c052106126108005a002c0d80c040c40c4100300c7c0f070301d5001c0c070f034415645d00c1a4800e80058000031003404980c090034405a1005010701640c2c5000400407203642940d100322012140c50f90086000e00440c4c24078480c41c1d001d444035000074150101d80229445101d4400380c3d1305140000100035a4126126403440300881c40d500030700316a2515070502c4003404c9110344201c0d1a02500103900020070305c1c5402c2c0521800c858441d2a0100c0490841d10f40d04d00703d000745039003203091000c100000901107040d445442151007406528036102c5c18040f00890b540803441441d12241090136038018041200d0b102198111f40c04074940303039a10b07a0342110050460282c1441e124044510004140a020380441c500450140c0c60340c880d11496165040c0508490007a100c0c400000c10904840e0001502d51001a201106010424a00090110342c4600c0d00b24a03031021106651128020080b180860186c1d070030a203028213161b03042c50014642403014070010b02c907048061070446 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 817788399 1250 817787149 817787213
    0xa090507020313030302011a010e0f040506031606020a14011a06130512070303080f0f011a071e021f02060c071b0f03020f0a03020306040b0604271101020604 69
    0x11141c50b10032810103c1c030031070303507900b40070f402400c50022400b8030034500440e0b01102c0d0b00c00c00e40102894001041008106030150900008000081c85250980324034250426030145015500b4001c10700755000b80003d481a01e0500c410403a0034070080001d071b05014054000900e48214062900c209440d05e50310307502e04480341c42103035041e5445680c10025214071200c5190020494034107685c002c4d140e081d4a03440b141c0c1c9071061040b00315144210b401c84a801444012964540d005d180100205c8250400019445001240c585298010504050414007000310b04200342c0881c0c00585d00b03e50103854244401c0c01030b4541e48010b0244481003c0002d40c1000c10403507616400a4962081398000110703100c0b46e1242c018100d41c00700b64495038611a03807005516250214505480c2c2c00350207802e0540700c60f44d03551441c40020f048254040c0c1c581c001e604509030481c0420710041c003100306400c000e43e10f80c10311401405030044032504541020041201041c618440b1065420400f0601d210341500c2d8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 817789649 1250 817788399 817788403
    0x6030c1603121e050702070f0308090a09050f04060b030708150421090f050a0b0403240e03090f120d0f0302040b16030215061c050712060c0f020c0a09050702 69
    0x107010012540c5402d9121050748000503c031012490211410812900c40300000d9076249040e00ca041102440000240700059620010300590900940030700f9220b5101e00c0b0316010ba45040711458020300640d010002801028010003000340015005803804600340502282c458400801c6080740040c00f030302040400240c2045d407002c0c00f0034207003000307a40014860000e0581503140724114990812140108280c6071a0001c0e10072643c00f43c143ea840c1510703580d01c03407914500d0905198020961455410000ca00c1da0103400600c4c092040079641d00c070301d4103007007121410080c4001d50281c00300d00c03e005021603000a0328260101c050620703000d00303c0481000c0340688119044031015035008288809000b1442c0700c0b00c07412511039001e407070780b00340e02240301c01c01c89008807161980425003000210003c5d000140d040c40141c091801d5400711a1104400e0106000b914400c5a8180c1d491070107220300ca42c400d41d401a02d20312403000e080d0b880070000020f4020386950251700c0340981e42c0c401141c1c040e802 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 817790899 1250 817789649 817789667
    0x81b0301060516080a110f0708070608090307050601060207051804080f030c0d09050607141602120a02030312180303130803060103140906040320070e0406180f0c0506030c1603 77
    0x4040b00243d034903021000001c120b041407281b080c1041c450800b4800ca120000320307044080c0c0d00d85800a04000741f61050460382094003070b0503803140d0700007082202d02046d4288041030281101c0c4e001840c0c4d42d071415051002c01580103c2c44140d401d009018400003407240c83c2120080c00005800c591651500703800901a44a01080307000441d181030b801000f0800c001c0740301c3e40b10746850b840d4900342e84542c86500c4000e00c25810a08903071420014030340014584042d110301003020071b1b411111142c5d05a804207155a21a480e165080003010040041d00c0c402400640c0300743d0801400f940c00c60511010300003080c16000b030020300b03c40011000808592107644580f48500c1801640e502c82d0030302050f219210030040d141540001d14841141846021107050b04800f15060700007020031900d4100681c001c213201820882c0c0c803986925110000e6903424507044845401800d00040c1c041e100c0c0307090032117080b007a0700107409464144200001c00c24004281c500083d02e108031800d03281c1040c40d0486070085 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 817792149 1250 817790899 817790903
    0x6030402040203040611210a0e0c210f0102091002070819080904020708090405010e0c07060e0f030f0c062a03090a05060712180b072d080403081b0301060516 69
    0x4004141d12040c0800d003000002140c007e05248000d54481040b00320946108048000550780f04500c41382490030102e01d1600e008410a0169603141e0144001d0345c01d00b018002c25903216034021030a09000d240044585207000c0e1540001d000c400d02d00014141c545010300c41c1d200c002240600d50605028001d4101c0c1c21b1a40000c104541d2000c0c00e21380f10105400420350720703008a16000011465008241c10035000b02500207605043c1031041d0303140005002d415185500380c1c0100c8540307288468003000680030510b88020a00d4a07002c00d14000c0e0f103401d00090005618140318040c4050010000c210883e0358650014502da0740e6036100040ca10341510004028050700c6440b040101e10385d40400f4981c51540004c0003170005901a0145820340c00288001800a40d001c0021401050280300305d0080704103800c0701c8002005107a05010350001b60058050080741174801080b08040c0c1c0b04020035440061600403007600c0c414880e0a2029000500a42040c0300f000285400141d901d40c001d005032603 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 817793399 1250 817792149 817792181
    0x51614040f0608040b0f0f0a0b0d0204050f040b0a111602011806121d060a05060a2d09090c0306020c1e010c1e020d03090c23031b060304020402030406 66
    0x9075882c00024a41c6204076829144001160042001c80210551031402040c600710b1303481c4240c403942c2d040802402c9510019a018242c01e80450040e1590301070a481500d400c0c10491651400c1e060000043d50300400c203012a9241018101044031000c003503c500f0398149031803c81c000034a1005940021000095404200c0890000190142e1082048a050b9901d95050084c1d100d0a054000041d112603401ca200c0d40000303001418210b076030340c030003a400540100b2000200b5034942c480c82a4903140b408114400e03454202c0c4107543c4041c8800000102000b910401140ba169242c1c121040d10a000040c00d42d500024100c2e14284200300031140200600100000558400100303402095003e40fa40045240600000422900a008102040455005021480c03c600800ca00400c0b10040031100d01a0031038011890700d0104209c0142800314400381201d46028004051416545624420311040c4024030b000702c0d500e40030140d0f40c02c42d605460241c0c50742c81d1407400401400301c90703080c605d00f0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 817794649 1250 817793399 817793429
    0x1203190e0c030c012c030712031e0e0105030612030d020a0c020f0a0f0b250503030f0c0a05221a03071206030c23041d0c0405161404 58
    0x400d10118254210074811400c03255402c19900c0156000405201c1803c2d98440174405d041a00003803841c0c2c5801104018140c03000c450f103840414458402198081d40010304600b0002100c0c2401e9070a2004014903080440b4405000f00000b00309110045c0a103004100c490141a0500010000c0d03846018400400795181e120f00c0310018241c1680f204142e00c02d43d64038150700142d08140d84c801003580c01007a0054420307800c00b611184507a12130002130442c7c2c080c402070944081190131041d01d020703100c4c0b80030b0f55a0303051422810700102000703841007501c0c040400003c1201904901114209021840000c2d403040d091100107407803940c81c0e8851007040101c4202c40203660014002144100c84035164200070301d401320107600031111075010080100c0e904500511560101c8105944040d05182c40d080d01d601105000c1016910002400d804410421105100d41a0184010203442005131020030103894503512030075001c07401e444980301b8081c041e5002d0945c400000e08580142c2030101081d160 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 817795899 1250 817794649 817794671
    0x516050d060f152c01111501030b04201f0908030a022113271103480f07080909090318150c0106030b04020f03070305120319 55
    0x261469540303c0344001140c2c000e55080306400c459101c64089080300b4081c1606800c3c80040d102410096030000044c410b00d80032242c3d0b1002020064040c601c0b0f00c1c907801b002e0500b403400d10403001c0203031038903c400801201085c1a50b122188650514010282651460410101c055594005903004140c40b40070005050382243e40000380800785142c6004003210080012540c04902e016402c95100c0180340c80c0d104000b140c401240c040c1410024a2034051065907010280e000c07120340c0340c0b080c85081008000c0100c000092a2051000030749081d00c0600740e580040140c038041c404040c0301041c00e07420b02c1d0184e04c8030091029114485502001140d40f500107040c0408641c1005082c1442801d02000203910610040191900d90410401c1a442c00780114208500c202c0c102d01000491f0348180002c440081c0709010340c42c021805405241c00d503081c0b81c010f2103410144001658001d030712040c401c01c001140000c0a40008120786802030701c0751a02189460b900c0004034a0072501c03803c0c01c04643d9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 817797149 1250 817795899 817795919
    0xe010c02061f09110a200d050d06081609110a0c060f06050303070804090c0f0816050c19110609130509030d0509010b0f0307260c0411070309090516050d060f 69
    0x24a0f000644ca515021040c0070084040c0907071599811b452940200d421204418003c101410009103090030114003a615511064548080185001c2401c03905100400085901c1d10545601e4244079840901d400d00030316000d03020040f5038030000e010560782c004000c1d00c03c0c40e6138041809802c004060740d950302514204443d19402c14068461554941a80c10710080d004200c0090030741c0c256201c140b810b03660305e00c1c584c0b61040c0c50001081800703000c000c100c0c480034081c4a990154002d603407400e01e4107a03450502c0c248488804032042d001c1c1004000682c151f6813410900595400c981c0808207490355000119401e60007090301852115003803906200c0a0103064009010041003a243c0295121f0f0403030030140e43c2c030701d544100e4280082e1076a00c034030000c0e2402400301000070300208880d03500d6030007070104080301c01d0259644074904010614900709644100013000400c40e00070280a40d04040045003180c03c0c00f5881c02060100c009541054500c4580081c00101400714828005a03a0303101815 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 817798399 1250 817797149 817797157
    0x12110a0f0311060a14091f020703050f070b070209130812010608070c020604090b0102031204030e09010f0f0e040303150602010b01022b08090a0606180e010c02061f0911 74
    0x203460406044111001d41003c03016201e100c0030075628501c104c0d461401152103a400300c034406070044000901c00c0705150001c01d4480308008140d0050280c2c5140d82040c9040001c0186188050340102d4800c210315200f07201941c500c25011200780e07402d5100c01e84504c0840d118041c3c000d0131900701003040c0d4403101082c00228102c4040d9205c01346030740d0300c80e82c04032480609840002d601c0780c0d080c031040c40300c40c0c19648080d10b200c006004032481c020400c0540004130404071130407400102504420f41080c200440143c0c01030031450a549011400c100c9103034811203041c068159140080700000d41403600c6a000146022034220070f048807107440d2240240a0504103e00074054030179510810399003c04c03042c95645410840324201010401c154003111b0302d01019100d54068815088100040b034103a2040c40b00400040243d5244e4030902681a0700b5690480100440c07070345000880a41a40c020810582c041c8e1070440707150b440742c8105003000d50040d0702d07005401d00c18034040103250031005690080c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 817799649 1250 817798399 817798403
    0x10903050d1b231b010606090e040804060e06070204020a031a010c050c0405151c0515091e1006090213050301050606070b06041815150b0412110a0f03 66
    0x280b01c0c4195000244040e48210102c0c140050344040d46558403a503107071501840b003110b00310b1030380c40c01d901040b81c61603032041680058541e03551104208102c5030000c15560082284001d00c2030380c2e1400f0b0f2500304841c004c0344121020f114903600000c407596104802c546509600a0003151504007004000703000302008402c3c2074000710844081e003580d40c0103100050005a0080c000c0a208030060107200107064060141803c90148a42c4140d03103541d69144403940310b21442711004000c5039818010306d0300c102125404450b041c20014801303030ba94040340c400d00300040302c82d4420340c0f00c52004420b880c00601d05003100402c0e10300040428844656001818441100405440d0641e211010942219001da501d154001c4040089500040d5400c10196100350000e01c0001d0100306020340001414100008850700400c40084401d914154402c00404a0f00b580c05c07045400c1c1080c3c0303076002510803070140d2040f1802503845031041054140108503610300252104402d20b940e00441000d0001c1d0f4001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 817800899 1250 817799649 817799651
    0xe01091a030708070e030307061503081621171005190608010b0c06132405040201030c021605011808161d040503090f1c051b01030504050c04110c010903050d 69
    0x2050a145c420680c40f0560704006020b14582400c2d680c4500c014030b01003850400400f104034000020800f5100074000400440e40da20080002170301d481131100a1244070031034030010404181024644c4803036088520015822492500d0311030761008400104180e2010f40d105080f00c1d0744603001c100d6100050200d0718103480d404560b1f6213030b29550003c0d020328200f846e00d0754080304c0011020401310803444000d41c02210001400354140c14803012103d035030030303002d03504540f100140f10843d41d046c0301e054040c4c00707188054079850782a00c200c1c80e22036a040c81482e040040d4001080c500000d42007a5200800010b400c440e025403003001d60100c030310014400d90a502d09804501268102d001251030310417035005010f5031604081d001080310501d00481d0f01c1d078002030303045c8907140c030401d02d0362882004602510003441861498075210308981d240c1d00c06a810103050000740000260001003a11041a0440d00030078419050710082038540034281d000c42640d82808580424103401400510b12a550054 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 817802149 1250 817800899 817800901
    0x1d0304090c1b03050a110d05070b0a051303140d1409060702070602060f07030908070308100801090f060c0c020a03030e03152205070b04030c170f030a0e01091a030708 73
    0x110540b800d14001074000702141e210081600001d1182d07000f07010700052810040080f0040c0c800c05450021104000b0000c608002404014019090786042c2e014001c80c80c140058502416084068400350100500f80f1004a8884014010100a88141d40e0381140108100d6103810301401120b2415a05c4414a01a840108804903c04a0114180e81302c940044c0131903150150312429078440107015504060361342e5429000038a10b030006201c42c03030080e80c5580c2a81000104103244003503640c8041016850050f0307010004428190508005400c244006007420300310b03101703a440c880c503000002c0d07009264540210401d41c00038240b0050f44000d03012943c0100e28a52030305445101515481d00f407042c0500c042100d509028041d146030751050044e2031138143c0c3d40c0c0c3e602e40a908660000c441d000392420090111040a44111100000c51801003210700e01e110341071a140d00c1000c41450800c054209550302c16402190804010b280c0c903c2d04046440071176a010801c0e4206684180010754510 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 817803399 1250 817802149 817802171
    0x309090901090203060f092a030c101202070c030209010e0711031e07060f020a050c330903120f07030e151305012c12040e1503011d030409 61
    0x48510740b81c5581c040e00514031038071542c07054130b5040c0005081c07015501c100700d154483c0b1145200482603c40e040040c3c00b100c0b548410815050801c840c1c5018040d000e01d082d2015501d50100c01050040c175030a00c01a5102d400f410250510b5041e0780010790041c0344280001488800e21014501c100e1059503200514824108515240d118140c0b003a1003514104200040c852901002440864840c440015001e01c48554100c281d0b007146462002041011500b01410b1909000307002909904030444081d04000700701001b4001c882400442000c1020340004030700c3c81040003100d0280000d014000d032289050300381c1d0344508100321040c0c0000ba0038183c2e40f0528072b40004151803810380c001c04004a507038514260f031814901201e0241c1d40c075074896209500f03038441c913080c0d4152101c8990351444010000c801c21071078213070f819030125580f41082100f044040c500c622103030b0708400b4909001e40354a41c020002070140266803154255030360010000600c0000000040048070701c160303002e1154031104 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 817804649 1250 817803399 817803401
    0xf0603260304110603061309111002150c13081213051020100e0a120206010e06010e040b19030b0a022703160b041a040605090d05010216050309090901 66
    0x60324000d1003d40e02d41022040e0345854000346a1052001d03005030b01c401070382d078040c0302959007800301610801d1203404440f0290401c040249803a0070a0b000802c1080b842e0b0400400901004101c0c100c0c00f140032540c4064289103c42200040004008446a018550390254006d5001018088044009140000e81d608001d00303000903040c12500c07028001c0e401800000e1287c00d680e83d40038004d000d6407103000c006984610a1030b2a541300200240042d03400e9242542d2170040b0b41490b01c00b5980607078010803a030a40b0000a5501c0720342031811189980340d00300030a0107000400310b840d03404a01401c03010640303054a980c0a003128061210b000050300c440c1031200484c407580d03d10480c140c1061000c00683d00c0a08842d80440a000d41205c40b02e1042c08006045c244107904008411440007904000c0300c0100b080c51030117400780300740480c80d09141c40006881d031310440711203c2c0030f1401015007000384032003907065981040564004480c1c404951408685950040100521803900440821280901 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 817805755 1106 817804649 817804651
    0x4061116120c0b01120203100608100c03050603070311060d020301170c041b182303070e0f01180f020f030915190209040f06032603 58
    0x49841c14641e0301826880e541c0801000100b4000443c0540d29220b04417521580e00d0b09540c44184042810300b988003804000041c07a00800144000000c5111502d841c0603840820805940f2842030b01158015a00c2e581c041d444a04d003440001d2601551b60b80ea010018105414040100c075080c0030781e0b000340c115001801c110f4201c288102c1c810845e0112441089500b404800450120b03540c2c51165018218100800c2c01c20281c2e1301c09a99507080701908000c03003d01004e0440716106107006182c04030a82c080d102d050740001d03a0b8010521920b0041c00c0b9544101c0f416403800801107108101d021a030043c25030307940700f04800510a84010400b003440340381c0140e26460203951a9050400b4510109100300b104010403550045081010340d030480070002c0103840d084c03030102041c002d10080400c0556a450200c01205015150300750701049400c00140f061401107009000c2c4003804 = true := by decide +kernel

theorem cover : BRFrame.Cov 817625899 817805755 := by
  have h0 := BRFrame.cov_init 817625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 817625899 ≤ n) (h2 : n < 817805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
