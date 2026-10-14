-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1082
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:09:37.583388+00:00
-- url     : https://prove2.me/submissions/4a03789d-146e-4272-9f66-b25497caad19

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 194424460 ≤ n < 194604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 194425710 1250 194424460 194424463
    0x3051b2106150102100e0c0109060c0203030703081905010909021002030a143004020a0806010f051003020909040c0905070e06070206070503040305250e0903030604200f0d1508 77
    0x19848a40307054503100d1a80c0e0140103d01d0024202c5080c02261b1805a100300390610006482c900000240d07683c4408a485107800c44004e20615002901640140a00030029010f0030139554002c4811040412003001c3d591200155142a07000c0c4000075544c0d14100c1c1541005100b00152400c2400110700d0120981c00041c1900c0505a112480030004240210725401c40c035070880c07034013801c001c0c10390883c490a540b0b0201c00c441964100e2248984000014030400b000c91181c2c1210b040c25501c1602d1880c1800707104982d0b014406040c04c2550030050b400840e9218150940035900038082500040c0c01c08260500f107030b80c040d2a0b042481501050301c1403658481c01226546541075904948404d041d26040745140210340005049005400c2c0307402c030128081e1031181400f000c0d500b000c00d01c240d40b2241d0402e906801e48880f0b519410070400550f072402e040d0045004e54514980039a40104010000441a0080041c0442c4900c7c002000c00900c8070601680b02d0b2284150017440b11b162900c403005 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 194426960 1250 194425710 194425723
    0x60c0f030e0102030903010e0309030c030d1d040f06060302091201150519080f0303040510090c0306150308041202090907050a03121803060c1206031e060603051b21 72
    0x20300300403980981c401564400d0050340e0300303204041e000b072142c1419030310001d07102d401c001410740c081e1061908103e03040c540000c245c140390340031f91260f02408070f250f040301e01c20902c0d03080180d4000703403a14000078084049102d918003d00c0d15640c010b072103c8452081007007014081003e0765040c0c4c1003981e11200b8200c4298820110340c405c4808031222000129030710300042c1c50307500c2560240103106c41d40c10a418040021841036110380c0584107480b00c3d22444000300c0740d10f070304040d0900c501042d06000003043ca41c414425042002c00c2690255580e5032403242580c000d421400d194041003c1c10021070900880103900b00034507a003c0c2000d0b5081401203100500b040c44090104c41802000903002400754405034540c12120400e845040c0d2a8180000a0300c02a411342000034202b1200e104d818010f0700c958801c0d2688000e005c80020300280004070310309140305080d0780d50380d40c80000000141c02003120701404003460000448001c0900204420f542c0d0022070460000c041021412180c000443c24 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 194428210 1250 194426960 194426963
    0xb070804110103021e0313030906080f011a0c01110405120105010810020708070501060308070308070e090103061505130506030f0f1c14070b090d0e010e06032d010f060c0f 75
    0x68540c1140c1403003807000340c5d4401401c010000004140200a0030040c20201524065155003c045585080881d5011303002c607002822001104014800030078492585030029000d44491030808891410755030840318200e4003083c0790000007404205900b01802c0c0078062a51007002004190f26012202d0f84610b8100c1d11800106c1d80040c0090400051000f0384807503e40040003004880c1e141c1c6412945035010600940210342100d00041c5840d1103641d000000c2880a0071200e0300e6444c681d10704020b460084800f501814007540e000c02c075034072051009120450640740200c0c1078100b150525041020668003550142c01004075521800b0700014203070b800000c126000009680c0c2040110f03000800144541d6000500140c807a0911070208610340c0140c048600780e0311000d01c0581c055500810304c1511030f01003218030b0b403120018540b01001d1540f001440f40b641412a451440c038031105208060402e022814920050040c0f94a83d000d0001070140ca0800100c100015240c240b54800317517000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 194429460 1250 194428210 194428217
    0xe040204020310031a0405060604020a020d080a020408030c07180204120803100b07030c0b0702010b030a0209180703050d02010605010e010905040c020703080c030409140115050d060815040b0708041101 88
    0x309208000f044800002590000054241e400d61060f00c1e40300040c0558050340c2c544280004108607182c944200d41d0f014825800411240780c00070002c0d0b480090081400d00c206da030034080091513441c180000c22841c06604041d10005051006503c0182c1e43d04607102e444d544184014424040000046042d09801ca280c4503141d588003e4500d02c202d042d0741080d0003040e004180b100c10182c0086030210003d1184071ba0070165610304604a00300c80107003900d5549580240000f0015042c15911550480c100011600015564849562401e1620351041340c81e40e10000400c1902030342803103481c02600d001d02e00625028860301c0000c00451480c020b880c40f0b5030f84c8c7c0e20050310041c0200500801142d00640064945c04101001600c0790494481c0d299910304284911004014580c45c5034183ea5113004002c01c1000910700c02c41e00c1350081c4005100c82c0d44e4600b030205d180c400801c1041515040181011a146064503214802600141003003052112020500000500d801c1e02070703208040a00c0d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 194430710 1250 194429460 194429467
    0x30302070b07030e19050d080304020424090207020d0609030206060102250b0c0c0310020904060b070b22140a1a041a0907030b09030d06120c05010305100305060709050a0503070e04020402 82
    0x260014000c0d05c140d11090340200000ba1080800500d03801135885240219402c102d110300212003289401140441004010199102031040c041580d025200450000e010030004485641d111130484003103003000c0c2d0240e8007200402409681c104900005207145c1c6543c00c140100f46403111003e8410b501070486044404a04140c4503101001000c200321801400c9a50550400200500961026460501442c140703000450700c55910b40171100425441a07201109030740d10407145040103180070410503056005548040407445540d400c402250520001c4d10030712509190640d03c0200003900c4c0c02c0c008079240100f2011a40d8819003a025201c0b40d080481c050365030f4000641460b034541c10091107200042c05000c5885c0c8000098000704010310020862140c0354a4000e00320700805500030200d0251000920007548a80c101a07009010315640f48000f9480b5612141040d01c2125090005001014100302900d42840c0a4000308401c5d005030940504110040c49504801400a0700440d0000b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 194431960 1250 194430710 194430739
    0x302060c0f0c1005010906050402070209191e0e0601060906020616050c0a080904060b041802070501020405040f02090406051525050f070305060705160209070e0415030302070b07030e 80
    0x81e04841e0450601c009403400c2a840d40e6201c0000d100a0007020500b034604603012030507017401d10849101a400030200e4083c0e5540c241c2c10a0032000501c0f4400f80240c44640d191890700781e0510585601a040c41c001c5407846640c8200e61070820164000c404102d6042e60803c03646030081255600f0400604207001403d10b060000d880c03d200e02007900c0c0907171062180d0081400100b0b40a05a600c100b2a42031018a80e9406d4601d480d0046020b41041000782845148c201400c40d40100b08045c401c5001508199032040013a04030340a5070001010950000f4000c042c0d45007030310032032000d0071046070900d5811303d134406226101c0c054000b202d00c04441240031a050440000c514030768540c5e210045904103140f5440d22a00d400940c072080ba084d109000108100501030019100c49089004030703641012610703001c01440c032074081c081c001070184013805601c042c1c03128060b090340c40c83d406407130101c094903601d8024a0300f103170f541c014500080140310300c9001a0744a00913001004045400e8580f0f00700e00b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 194433210 1250 194431960 194431987
    0xc05060c2d07080706020304170705040204030c03061b020316031403010603021914090f0d02090405010e0d180311012001050106120b010915050d0905070519030302060c 74
    0x401c654801000d2580141c0341da81c800c000034100d02899140262442659142c207071590702c0d02d203030182502507001804103020b86060440a00052175001d0100d85203240d07180080f80c01c9a11030b800c280c400e14410074090090001c5070160b0400500b1200c1408444c400e5424000e449010380d2030b0402003680c0c44a00f02003454481d208110a8040d94007160b075481d60340b4100580207511180290045036203c07501d860556008000d031029200025084c689005012810001c804921583c0154030402800c24000076880324140c00744901d02c240000520380801d10196460500c4a007002c004110096802c02203400d1405581000c07207500c0b02812104400120050720641068400007c0e0300401040b4070703880310015000303d81200c545448000d040d0001482c12130668151600c4079010600c20070f002c20142d40c190f505407540c423680d883d1a60078160900d461205480002c00c0039102d5034480102480b652800b51f15010701130500903400340c105843c69034040d4071510b0081942010a5004c590304441070403 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 194434460 1250 194433210 194433223
    0x1701020c1902090f070c030804170a0306030b1302010c110d1a0601090b0f2a0304080619051303030902010c06050106170f0118111219050a090c05060c 66
    0x111006581072a0382200007600c0d0403000310740c240d01c40c10b4000c0c080382c8003401c808115801120741b80d88a40c01241992400e48208001034003c48400070154020840d200c84800900542803c541d00410350b40e245040441c2c1d090030141c480c880f641041c030216030044c1e80115007126038513403083c030040480000c40c00141c00c444000001900710203118102100804212961030710448090700e600c4600398845401e4540c0d0b003d10310f560107004c0000c1040000340200d02c5510740003030401058441024135069652400c3d030304141c1c4141201e5000b44144003443e91059680503031141145c400b040326140068020b406454011805024103a40f44010801c3da442404002071807900100c00b4801560b46940080c462054203402008a010440c041007560f20480c0d03140b412135680c00c20201841c407000542500130072100b224001c0c0e088003042104044030b03000c24510b11906020920000c8040c06112910075500300131300110382240b50002280c000340600d02c031070003511400e4511540707030b528100704c0a2400c80b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 194435710 1250 194434460 194434477
    0x17030d0c11070521151008060f070509030a080c0a030809010b0102030405060a121d06090d0504060e06091305060909030f0d0b01030212041103010b01020106150503060d120305041109060a170102 85
    0x38451141160845e0202d4103401103500c0c0f0407018000d079442c0c07441a02d811003a1014a400301051000c500c40a00c11000360200d200000e0596260008980d0781c035000e0303032158407200036a4010418034000d164000c2c3d120341d44404a00c0081c0071000107200001e44900c114011a4171a01000c0703000d42030148100101a0007031000b04040144c0d200d90035905540d00c12584035406103104800c001481d0100200f4003006c800c459888840c00d1a0a0480603280041d2441c6016004202030000c00c20554800201c440350452006000030030781414000e006050400414954680d40100401800302c9200d0b4101e80301c0c1803000000080c9800303104012006840b0740c00f22150b01c0c4030b041007440f092028034001103c54040031402003200c913280c07800683c01e0302d02c00d106151705a485221003800640c0500021136112000401640e10907080e50340d45080b042c03890444500007a175600410042080810340e4108080040307540907214a080400510b218000307001d0466806081c0095030ba202e00250160780000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 194436960 1250 194435710 194435713
    0xd02030c1306021513150b0d050102030f090f0610090203060103020405100201051501140d0c1b030f121b121b0206060a090204030f120917030d0c11070521 68
    0x12035076044003e43d1844d140508101c805031394004160901c41100d4070200d01c582c00005610394000d208004001054640400c1c1d4118015569103400a0320a100a5105190101a07048241440006c440c50182141282e602a90188080c4211105030308040403c4900405d40075a07240d0b190401207000c2d00603a800542c2294090b00000308403034043d00301c24400c0c02c000410484a64001e401120901c02a81e11024850302c00c0000210112403a04264030603030700c2d03081030b00061401c0039a58482a04181c400c0e400611100c0030003403041d50000c1440348556030f0071824004428a80308904003001c11907508014008038903d110700380e0440d5007090f40c4808001002090f80313901c1c0200a51200c0c0119003040c401e10300000041100d900c14429617090380c0d088480d5450690b40c5a490b407070b00c3d251000c0d0078014044070020004040c100345a10904084125002d036498021400c0010242c5609041102c10f1040660084140e00000101c030021640119092a40002d00f0f0703500d00750104010040303e419 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 194438210 1250 194436960 194436997
    0x1d04020a170f060a02090d02040f020f04180513081207020723010201060512070e150303040906090b030a1106070228080f0d05070305070809040504030323010b0d02030c 74
    0xc408160802e40c42804000d440055840b142003404074414400041d074071520114800b009410070b50700802d2a015203020040c503180741043c590065420a5100050300c07050103184d0004122103000741358108000c0c80c1242c150b01c0a03941c840a19011f00310a42421070740000c002403002d84204024402000e800840d1100500d441d0381a45c0c40002e02d14000b4055801d00500083c14100f40c4260598808640041d01070a030800032490f0718103402a1072414145010f0810b0805030390305100030702c024102180c000400d2840c0030090815107148525043c400d801043d14603000c1241d0303500710300d00400700315001d0f03075034004174030000d211a00d4844094400c425045490740d08000c0341e540c02400e682030300080318101001e960400e65605800c0314400300241090020200090240d00501880381c40348504034101800742000c2012a0421501540025150b500e070440f200080e80c000f112455004030700f0343e050b60500e804604a84512140c3d41940390780080064000400c00c1b080d40c01c12003104042c02070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 194439460 1250 194438210 194438249
    0x15010b1c090c08070f0503060115120c02100624030203190515190308190e130911060c210c060705130e0115030c030e030d02070b01060305011d04020a 66
    0x42c2502c0c0307406400400c0c42840d5010440724880240002210001001000540c2c02c00d001418001d18840c030030014000a40d0900081c03c6190142c0010145a179000b04050902400c500d01511003d502c201d0983c6880c08203012400c50801c4002d42050380c6080240e81d81c0c881d03840b01c4500640410346078003480c1c07404082c070581c44d08005250071401000c580300442c0000c260210700404468ac440140204010031050500440c1c1103107140c8850200e0030b1111074128031101150800c0d440303844c800041690b5a00d04e034100291901607103a032107405d945143c10000c58000701607490508410f03040481c1e42e582c5503900b10b03180c24400c0300c480c0c1c0151019660242001c45c07014000342c004802c51040409160804241c80c40642c0245041b038502003004100741000c0c3d10306038010321201a451040544480340300c0d160580c1000140140c04e8101d0006a42e074055080c41cac405e028042e0411401c0500f882c0041000e00c0d9072142c1c0414a0080c40500021a1518030004001010316440341144008005a521 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 194440710 1250 194439460 194439473
    0x402060405150d0506010806062506090b0a0f0e0a030e3c040b09060105030a06090513150506060405120a02031203061206040309180b060301240215010b1c09 69
    0x402280f45070070a020f5074464a0041d07403803071000c580725500034409004414542d04c101c0d041c6450f822072804d924011588030784800381580c0d46e00009903941460182409140c003114480d110203141c03908801c004120b00b05000d0743e05c0340340808000e404c121141242503815a9800704200314100c010302164014169480d0002800c1c2c034020305460b046c2c02c0250b80202038103050041032202d1900a106050b2039a903500195000d4001030b1040354442e07554540400d03840031a214440c000c007400d210b20507010701d1500e4030b041e48095045444014900303110a004440e10741100382c40a40c1c0c002c4035403e9841007081140e0340750000403480a50b040c030402900e6416003000340c0c003d40c080d030002d690751000144178400032075941c18142c5d0024001001c1e02410010341400091413800502c20720804103031041c0032000180280c01c20b80190b0007441c105500c00a0f5240c01800c80342c5040483e0014001d03241c9d5800c0007580e0403205100701c0034507541c00074410340081c0e4030002850440304400810019a04a0709054 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 194441960 1250 194440710 194440717
    0x20f040807051003050906010306093e0301020f03010909031e08070306050d0f150b0a0f090c08092107050115090b0a121101030603050f0f060708090312040206040515 73
    0x10f40038881560400c0705051284c002e0503c07503070701000100b0859281d562a070008100031070041e01c2d080100f46140d41a03c0d9001c60381c035a110744121415084e020b1008410a800b0601140a4420382c8100a544c818200c20f40940303044440c82400020820070500f4250391000841c03403401001d40d071941040c11401d411404035030040d00559010400c0079211800d201c003c80d0320031401752000302c0400200340020010206180c11500545001c140e00c0946008075000b880d0350f42180c925202011800e0042c07500620540382400e0782864201c0381380c244141c40701d880b41c289a541c441c2c1044141508592000c0c20000ca81c4011350002c02040b0f407210740c4d240c0d1008400326025402c4503034142400c0d48587d10f410b8000b10f00b81d9811050b035049a521f96640d4032900c0d0482c0d2000d5050580703808001011030000e000e8910f0801c888409003002803800c2000c01d0900c03100170062814880761005105035030b100002641c11201c24014041c20a8072240000781483c0220f81c000c0e0b80c0142024400da04091088025 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 194443210 1250 194441960 194441969
    0x10801020a03200d05071803060b1002030301035c040615050705010b04050903130819031d060d0e0708060106210f0219020f070302061903020f040807 66
    0x812003201c031040c22100071200140390b8600f0310310a03c002c02a840440d409190071402d2030401c1402401c0801c0704501d104406c0c1e009445082d0340d0020407400c0d0514000f40701e01102544082c500e158190760340c61200480f240303402c00c10350b01d00f090003000040d003e0742183c0e43e400011140900c0407207640c8074008070305005a038800100e803016034071450500303240c001e1038140c454621208110318035080048446800210040d9000d64031400c41c444151180d100b601e0042102c02b000c1c50ba5182d506003090a0708103c1d80c061029680405014103140400c070000940e12130303251400820442205139544462180319000c2c581c4440001082d07611035403117034040ca02e64120f0f0011ba841c110359600f03c0d07544402c400d00c42c40011444a10307001048802c515074404d68070764a00c40001d45400c071085860100e81010b4030340b1a40300400058a101c140d010400a000030300044020401542941c1c0466080d0140e100c82448490852440c50b00c894040d405648210880721011034440359100f4513259200c00703030f00c80c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 194444460 1250 194443210 194443217
    0x80c190312120f0c022e0213091a012606041e0c020303010f090e250b22050f0f12190b010f050604121b050909010f0f0e060114011403010801020a 64
    0xc0303554500e01c11281920b9030340508190701c0c1506c050000014040d600a002e800f0200903485004944001a0f05c0f030402c014401245482000c5514070015040741c01d442144400c00d284000c8480710204000c0025911100c103640c04541410b0790091940340000700604207000d9400c000301d991155038000040d504a0700341c60000c40b2f045903220301d5003084950350980ea44a50300b1008000800768000817a180900c9603001c0d6120030107035103104480054000801e60f20900100710504000d94034000d046034042c280c01c41d103078442d040040c0700143e4080150500c1d00d01454592049007211581400b0451560074004039000a400d107510304100340100c240144c0c0c0309001d14903000f05040c140001910259503118840a2004489440c3c242031164204000c040c00030042d031010074280c40c1c50001c45e02810407040007040501520b0205000e84400390b071022a40c0746800c86c0e41c42c0b4440001065070444076265841340c4004c15400c01218001c203030b8400080c0c5400000000038120105500070a014042c998 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 194445710 1250 194444460 194444473
    0x41203020403050705060a0c121e0e0102060406050901060f0602010e010e06040b01060503090309041d0c040b01050f0c010f0e0714010504150e0f030d0306080c190312120f0c02 77
    0x4015000c81c01680030260079603026400500203070503c80700500f21108182441d461300301d1240d0703980c150b118040b074042001500308818011408040d002d54121030410342801c1240420000c0000d41d40c04004001501203a2a1404500070400a6006101825a8541500003680c4880c0040d01801138010442e24940c6050400e80d855031021821074082c9501030000740099107010012907007600080c041007458003080141c0c2031a40c0d242d100b00b0b010407203208454078110150310340ea00d050803407010f00c0502450404034081d0443e1791110441e07901c00b080000c0c103901c854801c1015401480e0303440d0140740030307450040540310900380050580704852459000d0110083e144004668a0160780f00d94410301c59400003032180c0c503014049140c003090024004403018209440061f00e441451052440400d43c1c3d4101400306180c00e10024507501c0301603420000d603440807411070004803c00c1c8400751a40c0c1035041070100040c880d500c00d040c0740c81c12150510100a045c801c2c07600070700002e03160703101510460 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 194446960 1250 194445710 194445743
    0x50a0803180108040606080a0f021f050904020f0705010504030503061e09060d140703120905030106140105091503010308040e01091a040b0102030d0203100e071823130504 75
    0x1264500e401d501101c1450012034070040d40c0720580608200c031199169000030402d00020002d20031007a004000c08070710300b65540180515020105544482111000b008610254210040b03030480c080540f0b0050340c603a9500f49100c3c41d0b02503814024046d5080c04144810305a000d40658040c038411624850b2603d00c40803504214201c045c005504034038900300080c003074034243c4403580e882400354144010038001025514203180079500304441149542007c0d1000c60b502c009203402514040e402044071a08100c10350b0301c5080f0009c0000e042040000390500661100c200c00e410a240c0440c9143e140d507101c3c94420095042401003101c01c0060f8130000503650024040c40222101c1000f6808000c010740003031101a0001185260640c4010001441e82c8802440194800c600750101892030340e090286c00b40c104000500314200b0440b41e803d07400341e5402107000d0501102c00fa00d5000c1c0c1c0c890313a802c4100a05000c00076600368840d580308004640000130760803280c895407040496100c540c185 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 194448210 1250 194446960 194446963
    0x14010905031314061219020f21010602150103020607050304120302010e151e040203071a03040b0105010f0503010b090a0f0308210c0429130317070305160606080303010807050a08 78
    0x2041811000000c560000c1942101180200d039071b00881400e01518110400001d0000c5500c806801c1801c0b1990000a01044460030801409000188080c0c25240b1407100fa400e8048010300000c0d200d03035400035025003004410412a001494050b9540100302d010303007001b074003d14041030012401e005401d00b40152000c1428014031440d0750b903405a800398407200c02e0040e1440000c0080f40c051090300d8010442d180c10f034043c0d4260200d496851a83c07840d10f490a618804e00c181e001070705000d02445040306581d0800d0130759054501170004280c50342e5061000034031509a50f0300500c0713846e11a520100c1802603040090604031060300304002c2203c00031100060b4444115a5403c17007403030500050100301c02c181401e403d01e0040b02003242c0104440c0042440c2c0d548814181c592600c40b0240030005c108442c0801490b903510035234406d00f00412a10050214429080440032407805055001e04004055225001418085003180d0b12981c60740b0b00183c1e200c1c03043c01264840d500e10b140000d0007100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 194449460 1250 194448210 194448217
    0x40506010f0b070f020d080d020c010b12060402270a1d0d0f030c031d060405060f070c03030b0105120a1505030c0a03030509060d050903092106041401090503131406 72
    0xb9280000c1c5030240e03645030084402d4403448100e034003158080503140802d1068018140500710240c0c010313640c401c1c0085075821171301d110b121903001d0300303540c1d181181c40e8001141559201c0e8041c0c400c44a12070151035440c049807107028094003020800418400481101e904c0b4401c0e00201440071804d0003917100c00c580d42c2e124030807020000200d46440d5080214440d0b007012045a10f103042c04100003c0700b03400d084c410242038403d410540d104204110910100b0403c181d0000e2211504400e24144850010300c0e280d0280405014142c80f0075041206901c81d8040310102c09004d100c00f600b504000c179035440a00203c0700b42c4002c0d42030403d008034031840c021900900c680320080c00e09109501e590341c240d506400584150b6030058040c8490524030045024a41c4a115000080d654600311441009002003040e015005407203066184410903090001d41e45030481d82209804250000c0004424050320074040c00034034500000c1000381a0304130034820203082d160b41170311070170340000d804050011902 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 194450710 1250 194449460 194449469
    0x60818012306010e090105060f0d0e010c080714090609010e04020d0c0207080c030718020702220c05030402090a050912070f12020303070203030a150e0c0702040f060f230a0e040506010f 81
    0x30041707004011915001004100300f0850044803420011241156030864101d41101d804694541555584081d404420154095040c1c10f2042066016103094038150148032132041c0901c178000352101d003503801000800810080100250350b5000715034906806005455241c0c3c0240c46060008100c159020822020039030010f07008048540ca0000b141220b0000b200658442d00e600700070103001740c0c480c060700118002c0b9401d4040030b051b41c9480304008640d420710003501000414000c2c0401030ba24007181a4001241c0e0038081080c1e21440c4185042490540740004e852000103940c0040141c460100300820f801124607801e041080e1205903100d22040b030f007050041c0c004100160600d072640d0701c000303030043d2031900d1400802d458210003026400c041d2181c55030741d07402080b104110f2420340103800d080e0b21020010b0005518100139080c600c1460702901d400079450001d0000014070045c01884005002004140400d1703842d034120508250945090300d02d4022000041440c9407100c01260445 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 194451960 1250 194450710 194450719
    0x309092306060c12090d050d020601080c030c1302030601020c06041509050405070c0f03020a0b01090204080f010e03091e06040605030f09010b030604030f050d110c1603050304060818012306010e 85
    0x3074040c24440c4c051903201107807030b40d0f00207055600400810f20030030000c1b00020b0240c00603c40795050071032142c904504090058800d50219040c0700b119100c1060f210345d020301580000d40c42ea112400142d0074617a41a0300c20344c00c54408178002580a28480d918100361243c0d44408004513114418402502c0c001c43d0414040b484910303080000544039210718075a01d000348140c561500040da2403c00c0d40602b0303489a03812940104050041c44000d111002c2d212025900800181e448203031090384a0142810042c03140f000045907450608079400007080106004218a0341d90740c4078031300a001500184d035920020349000c40054589074052007212101d80004006107a503580d540c1d800ca88039064410710204000c0240150f4100007c01c1c05030780b039070101ea1001d40386c40c0c0d0860340f1040e00e0f001d440e42c586018580c60300810408280c02100302c1b002d4540c030389410b103a5170f0f441d0000022050003804641000b0b601e8800c1c05403a080c00324404040d00580c040029034031381c030f82400440351303c151000d6080c1d02 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 194453210 1250 194451960 194451973
    0x1e030f04020d0c0801020a020714090910180f0c15091404020a12020703030c020c03070608010e060301090c06030b1f052a12030a0501090c1b0309092306060c 69
    0x1d4603200341d000c04210f10030450403c109032075451990030380e0882c40c505000769102c03400910416044004129505400380c0c1c01035818031313200c80001e5507401812030006405d99100141034880e0342c010000e00441e500300c00d84505241071803604601c0c0d04503d110b42c00b56051490000d00300329103c0d17190241201c4485411420956038081000000d611244214040c400b050b031410414035054000f400784513000b9100052907400aa0b0068104001c0701c500611903004080280034098000c000641903e0500c401060f00d40d460301c2c040f030b0041884c603074040e0240d8031480340050580d5158009203039050b019600900150850200148503845140e00c0a011450901400c20300c45484c09048506846400d000c07481e103144550002e051200070054100c50160001c10400c01020340d005160040c003280000304010b002040c0014010450182d0824000c3c2c01c5a07580c005040c40369200502403d211003081082d0320700000d4503c1e19a241c18002001010f007200002c0c1ca81c9001003d4030446440c2e20090401c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 194454460 1250 194453210 194453213
    0xe211516020a0309090c021f09050607030e0a0f020303040b0c070807121e061409011d03120412050408060a02090f011404120c030b090a0b09060405030708032a1e030f04 74
    0x19029451b014011445a00d403580c06000240444680c50062a0000a540c1a441c1045403d03c00d0041124081c1401c001074002c50311000036540b90a15000351410300b0705092440000d05501c900d9010b5076010201140f0031043d03407000310b0080b08413070090040310f151543e40d04004071284503400d0090819a156000c02d690203089030b000c0c55486114210000780c049110204d10500c1c18140e80c4844203a548400d400c0300043c6032016100c11811120085082150280c800c481c0c115006000030300c20f00c001c80340300500502400559003e0114001a41c200c3c0c54201103220080d0040041d49104a01075a0b0058155000e8100c40080343c40800384a8a06402d140d80c4c129001482c000885030854a41ca000011800b1004014001c2c0700860142401c0006400d10040d400c80107440880d00350086800e10000800000803500c545900c415066241d580b03085555000200684c4420b21500c203000321940020f0308903000b00600284403003101c070103415042d181c0c10a0701044541088034007415011a0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 194455710 1250 194454460 194454479
    0x30d091212020313090203011e030f0323030403021609380a031a09160608060105040e090c01080c0405010212090f0a030606050406050609010e211516020a0309 70
    0x2452501a0046a142114044c541215034016501000482d5400300040c002d49001c6540c10740080010f40043c15001e0075901c9950b100a0a08070084c1805140710098480f111001242e03001a100c5030115070b12450b00c0c0c24081d4a9000e4a16413040300e004040c0041031130340d802c2c494100044030202c001405000e200680c412000134000313201c004000c071702e043c1c0701403503550300f00781c0c00603603c1480c40c481000b505200e94401014040c04c480c426800c03001a40517100800d40300f50045440d1842c0c030b0350158903100010703241880303140c104941d0080c081080007075500c070011f1003107500c03507080e0b0f01c0b0100303a510703031842c07a5690045009642c0142c01c204020000403a1017405840441c0000309206c22101340e1900203004600d80c2e41c421101c1350b485100c104000e103481e00c240001400300b036411a2070429807070002003900d103200000904ca1003c06000d4001003207082d02200207007000c00129004488102e04640c0001c8040300d002d0004c82011070b80307041d65440410b144281962586490f0152400c020307084 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 194456960 1250 194455710 194455733
    0x309011d0301022d040b07120909050a09030807020601120b040c1d04110603100603020c1c020307020405011703030c0a270501030b09040b0a02160f060605030d0912 72
    0x1200008428151905681c0a1008042500d4002c01034620000c0c02d01007141150040c2d5400c080031441480100320f00400d000c2260350703195000150240d004c40122056886000c0360300500702c20307458113003000b5100364543d000c1a112802616050855601c1070340490b07841209020b0041440b20004541000507406c131500b80d0041d1248044225050311403810507903c4505401c00c100c0105d802d0240300900200a88100c105081943d1b203a20703502e084600d06140340c00c10702c50300d020103900244041e41000d09021315517050380d101d01c07a0b012680645c0d500030b6407a082428184d201e580b5040000403190a400e0314074a407200184003075801c5696024030b10145400c5000008144080402e03c0560002d4114407810440e0b00d0b60a41c0b01490300b0140014102c405503400c0e540a4031015040c80003262000740c0040e40407203580809603841c000341d11401c410f8a001740300204603d00b11038a0f0003c01c0a80d402180540e4004d03000ca0b079242e440900216a443c2c501d00c03801c00e80795140c1c4c0340f0078041589030481 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 194458210 1250 194456960 194456987
    0x80409020c030c01020d1b020f1f0b0a0806100506070f0303020f070507060503010612290f03010501090f0c09060e0402090a0b070507090b1027050603010806040507050402030405030901 81
    0x50740c0c10f00c04841c07489030984c0e101d0600d110143e503031b036903203080855001030300001074000c0c40c401404009801c0564503618402e80800d0000c225900b02000341191258114003a2400050304004009a075070304015900c65003540c802202c2c030701c0c0d02d8000c161401d20000380c402e441d40042c000c1460050a0f1800d400a5011060400c04072504101c50070101e141045420014506691115a20340c0351003c014041050790115200712401c00104034680c5200788003064a21054030018010f42c2410400540038072001102150503500b050b00024007600f03030340d0011442080501052225220302070f021180d50140e401900c02103022a191000e8a007007a0340904002c81d0003070542c03840c0760303100d8804032066004000101c4071580001c07801e00c4083d42500804140340c60540d06008a4601c01101408226080008070350a40342c40307060661042807052003900514002c3d046a50300e5071510051921410103d0702a107481c403507503a0004a40c2000d01c00c51307205640102c041c6041c40c041c10011585560340401 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 194459460 1250 194458210 194458213
    0x60903050c0601030803071b0f240c0203030414030a02070905061302120405100513020409050124030b011e09021b0d020109020118030803011e03061404031b080409020c 74
    0x8906a044401c000c2d140c0a140070301102a245d24041c1d4000300300d1500c000c81c040c02611ba2002c0138000501c080105e03090340b60703c032441408034107038501040c4a0181e44803030040040c0c20054107655039a0084025400356020701e003c903804400c68400c00e82e90740b00707980c10744006900c00382c800c20249801da440349030040030040c02c0d030840da9000030070351059030000da08141c0308042140c28081001002c00607a52564243da1050225190140514004080744c03080a80150744070345800c001c001c02036011405808008800440c0d000a03030080c0140202d2030302085904141540010581c10300d002590050040c1d000095032400e810560b525001e9002180f403034075014180c0c8507200042d6405d201e58555003960707500000d00440180001008810041002064203809500c144040b07000c0740100ca042d80c884540404a0032007010780300920010390b0340060481840c1c02c080240d1a045c100784c19003e14000e68031901b81080142e00c0162480300d5007401000c803103081100304204425600a028603402030310 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 194460710 1250 194459460 194459467
    0xc040302030102370e120304030b160f08010806060d050c041d0111030c0a1b050a080301060e091014040f061e270b060c0d080108010b01020a0c0306090305 68
    0x901090076600000c240110140c1d5401d6100d403a03000b9614681c00c0207413104504c0c1c030385a031007880103400301150801080c0a00c025001554816000300200c80c01560b1018020071185000001d0010700607500600000092190a014151a100708072050584500740054009500c0f2a01000040c0d448840219040d000d44103000040b9030f00c0d44508103c03d0070804209161000d43e1100354210381078103c142e540c1500520a200040c1e911a090761950991410014800c18080427101c554510201c030060103407064040798002c01a105000d107040307620649030b001608003003001300072202c14125411004468041020010000390500400313600b140540002f91024890910400362501d6800c1140f022518002141003c030b203039500c110041a204520a00d02d151000b28450000c0d6081d640721040e5440d00060012952428100c600320303410507040320794034240c1510161021500f44180f2565502c2c10101041070750001c9084483c095202005564140c03c40d5220002003604e003c040c1e04011703050 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 194461960 1250 194460710 194460713
    0xf081527090601090b03010e0c0616080a180f0b030a050403120c17070f120207020a0e0a0c111908162301150b040b0307030b0301050106030b010e04060b030f0c0403 72
    0x4566000d00081d0000c0d00d601e40c1404140010784500380c440078001c0c0c2c904131000030790b60408900058842d00844646540e8600030141d224821110140500410800500240c150360021381d540d0001a0508401e04030551341d5001c0b50348250607100382c0004200403c000b813003042c0c4079402554418881c0c00c00d0180e50244400c80011101301d15a0080420710b1001c0c10360060b00c5000642c1d074001518079000002180d191380040a141040490000b4540c020880310215520070b40004040d0201640c000c000340b90500141c00582101d1070380c4408668cc070b0341c1c0c840e15028003048080b1416a000c0807a41012210343d1142442d5000c1d0072004410101c4036a00000510500d080c1240d0000c01c2c18541c0160712901152800c6624011035480c0100d03078080200500340d01c000c1610210748209000e00d490755250320080d0003400c254840d2a525520349000450990342660010403044402c0c2e03280805c1442c80d5050004644650080d02004d20301400000c0001e040ca02c00300b648590020100d40c10507a59 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 194463210 1250 194461960 194462029
    0x1020106080f07081b030c0d030507020607030c12090b0f090f03030408032703070902090102010f1407020708030702092e09060e06031f021b061003030f0815 69
    0x60003101042e0010302041101d56002c008011000321810441d090702d0170481d00084e9613400c0c50051600642c01c4520702400d05020384d040e01c29054018180c6a9180c407140340013030130f032076a45200701c40542c1c410426070700480c45120808290758140c00014a02360010180c06403a410a04a0b1544814040c008160640f4244064030040000400554849440602000a4116000a007030002e41041c00111250781c000864a0850310900f0700143d4502c24040100d016103a1883c90403203803820034600c55a8022150314107441416141c1c00c2d516840d890303000302ea03168031071058041e61202d415804607807030350305000d0440300704840c8030804150b85c07140407000c01d0544440e83c403c280640d40c1d00c10801c00d03020010042c60b80300204401a1044280b041440907100a0300c06480c40015408075050400c2080c01404842c0c900c403200c22908189458182a040c00d251030004034000741301c0b003140089090003103100c00d001d028414192101c1146a00038062030b21a40d0913200309020014413000c0300d1000307 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 194464460 1250 194463210 194463223
    0x3050703051b0118120618030905030118020d060213080f0c040b010c2001050d1518090b1909080a0c05060601080108031b0708030307231e090102010608 67
    0x21810140000700207403001120a00c0200302282c1c1400700c004ca003042200000300004050390400320315104404d00ba406c02100501d0b4210380d507080c142d2803036040414190890800001c91b041140280b1031200000001180a100880e00a40046160381498001100e03a0003070140c40030100b070044541c0d0f9540520b030385411101260050190800380c801112410503004100b242c8a080c200b240c9001241d580c1e103088240b41c0706813038103a9500c1400d00e00840c1c0c8142c04807020b00d88042803e11160110242d9020030340080c0c81071400c00c8800151413814454980039200c800d540114009003282c0e40e002c3c1c0f1100c2c2015040c0d4007608544d6841c0201d000840304400340440d41490b5032002c20212152806502e0b2038800352a15052101400040120a6000048030700c8140141c2c00b6110b00c0f1040307100c0c0b41c0380c0840d9802041c05408080100150541d02910030014a40034189a102e0120001c1d84001d1500c07504401402081d120480000030341d00c1c0c0c01c0144080034041c400024941c0e80c1e410300310305008 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 194465710 1250 194464460 194464463
    0x30c1e03050706050708060607062406050a120c0e0909031c020909090114130206071208090615150306010c02041a010215060a0501110a08040801050a0c020d080c0f0403050703 77
    0x240040360007003c2c4601031141650210171828104075074180000029128040c00700018032180c2c0b40c0c2131340040e0407010030301d40f0b20000c80e00003000f986130b84581004d4a660000c500042c0041d00202d40ba81c514141402907945069490b1107440020100106000c85543c004104210780d01c406c01c04104195160030714ad4504030002c4100684440505003008100c150282c5607490726070410500028602050034010740001504030450b41000c46880800d0407070080710805012145902001c00c05a45c0011001e80310300786080070358001da40c48224000d40c00507500d005540009420812407040c0b0311000c0116040841418092242c0700c20341c2c001419910b0348001f850020311317041c09011965804000c10320300704030a0001d0700f00e589020000301d1209109d5114480c10000f480380260030343c1c2024007900032100c0d0080e40450340c464030b901545010340070a503540a411481c00a0101d41c2510100391032801014903920040e49444e81e030b00d1081560800d4041c029108000c010001c0098002c200c00001103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 194466960 1250 194465710 194465717
    0x410102040f06080613020a0207180e0d02160e0709080d0c060b01030b06090f061902071a070b0f041b18050604020301050109060305090316050a0c06090b0403030c1e03 73
    0x481c1804050303402014507038850000d01c45402c081c0101603660400e80120a00d80749001030300c0704074050b412464000c50380c1c4480e1000d02e001c501044081da403500040000e42111040b1400039a521104907580c2550000c841144c650501d014021080c09841003508100d141c500030060075202ea514505000f294000b40000c28a80503401041004a026251150801342004c01c008010800031500612403035031018400ca1403507504002a54a54041e1440b03c1c80a0780310070208200031101035900e0344e007401520081c442007500b092b03240c1035007421105210392102213444d181d1600310080c0c01c001c0010b40103c0b09500c2030383c1003003441c042913816040101000b034001e2038a1542442c108048030005809680500d00410062160766003226a1604a0704545000960355844014060550240100181c00010050030308418042c2c00641620392901908404050703907035801c405d4900081c14030032a41031036014030041010174002d5128084840c090385a050625054a00c80c50346481001403c4011 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 194468210 1250 194466960 194466967
    0x10903080c0f0111030601050403060213030804030b01030c0b03041e03090302032d01020a080c16081603120e061503030d060801051009020309030301360c0318410102 73
    0x31450900072500e044c1c4c8400e8400d451410034100007400c2e485603000141081741c0002e0003890f103044140b00c1500454006803a00d0300e4949038030f00182010f00a10040c0c800e07019525020400b0000075084900440d445000300380c003264141008580e2908400040e418004d4051000025031028040040c81e140da80c6c481d081e00116200014503105d152070045030251303206000c1c001c1100c0d00440074940207410701c03410759102d014081e804d04100401c905d009080e0000440e5030304c00c890301e02c1c1c2040304452194464000e151800c09201003218400404003005900100110f49501e144030136030794501002401780c900c0d04040c2091501940d0703055000e405569510400c0064140c03442c8c2c001e1000d049c442d541035140d8204207800b559240418003800c0388110784d12400f04040100c0919050b8400c02c070507051940301032400c1014004004d14038007403012038141800348102d0790840194001181e030040704007500d041500c49411074607e441f03080742200f41001a04041c043c1c40c20420405d00241e002c00580d4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 194469460 1250 194468210 194468233
    0x90a021b010f180b0a0e2b08060105070506012912010f050d030e0105031306090b25050f0714070305100c2a08090604060305160203090603040f02010903080c 69
    0x100d4040c103e001d298600003940e00c000080e030f82e414698100c80d0003100400c1203e0031410341800c0442d0013602c40784040f1082c000700d401c40180340040040140c95207074800c442d40e03040c0042d5028460350b0001805504040300500c0308103505542d010a166604c4125003071514a03104049555001c8164002c84d40c0700c92004211051440b00030101406003610000d030303809000e0381d01600a04003039601030b05121011000440042e071151140d0ce4060b00030105000a80b041d0400303d0b60b010040e51815180071700e240342c440e90050104030b6020300e06056501e1515200c03040030360b012540c110f000115101080384e0705818035207500700170305400b41d07000d00003802c2c1602d800c40e4164121614128903605109010280110b104c140c40f6100c0303000346d030307a0007440c684410b01d2806101034070424030310950150000c100801d0050380356000a1040e14180390180d03801c1c0362240b05a90741c0c010f00050b603611000800000e40014601401031904070300c1130400c400025241e5481c0c190f1a0821025a19140d104580c07070361 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 194470710 1250 194469460 194469491
    0x503091903060507050c0618030d06170d0f050a0c0807020925020c1e030f010f0204061103070507050d1403030708071b0203060105041a0d1a0903130302090a021b01 72
    0x1900070300f050404d5491b12201c000080c0d00e4002c02490031100610b0700c0f00044400e035081c001c94400d00070344d80341001a1600c44800d85003a840099804845203e035241d690b14240c0600589950880c81da1205030900b010401c04132481c0300c80f2541124400000e2011030010b0300c4a10405019500004807002c0c1448070128140307100d41c2c550300303020840d804000000055280c0900003c2c40c1d00102031807008107882e00c0082490302e07640504181042d80380009117441c104195018200791a0155103400300c07113000b6141143e481c041d481c406490b40d0401c03a0b00b00060f240491500503041d105500030080181c003200c4050841d00704543c4540403c0485080200071680604510484c0b111451000408029500480d9944205000d02c45c00786940c0c0b40100991040c40001070900240103000c400c1800c000d00d4140d041031103c070440f038520110035011512002010007a42c01800a0340440501585541c00f000004800902072b000160fa00300005822001c0040e442452000c4900c004030350101108600e0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 194471960 1250 194470710 194470721
    0x1209120f0d081308070f03021e1b030a0506060f13020a200303040b0a05100f18050c03010e130303140a050f070c03020a23060f043309050309190306 65
    0x140c1000d981c000104000b40480d4152a000d90f04080031803007078002c6c0d103000d034541190a0180da860810b00340083c41c0722900000c03800c0c64048800301d00c500c0c0c0740c440c0080c983d4901d0310f0303070340101560413032000100d460030801d45540803840018000070001d581214020201e074448200791000845c10320007140f4050202865903c0303030901000840c5585000c3e1505c1d9200f00000d00820302c0981c40d90041400d03c2a07880b0048042c0201d030600481c05075948454480001c502c0003201c1d003c606010001c0d2032080d121080e079040703c0030002041510398407100001c0b40b40d0000c042c1141403555a0b000f401d00e1040008809120b441104070010301c23400c001078091040300c4020205810015039005220000c0d5001c41c006d4a0740f41e12030f9807114000944910051f103c13007103040c4420700c0e20038001040321004110009a00480c003501201e0756442c0315010444981001c4441c0450704500c0383d019603014a0b1503886000e01c05d0090302a02d046c110000f002032444d2110b031054a018403e2460280180807441c13280 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 194473210 1250 194471960 194471971
    0x80406021207030c030e06041a0904050604020c070e0903120f040215040b09040203060a05060705100501050316031202012004051305100e070219082106031209120f0d08 74
    0x500b070040540c0c1c000d0425100400090401c2040c401c035905640340c00d01513401420300e484c00222990402d905940e525040902510721460604003c1b6880e0b040903c2190445441540600903050620204a62840d005850205188420000b242004030f801201c80d005045003a40502c1a08290042060450848580c0c2c045c40c0d904100c00c01100c0700308401c5071100c83d81643d0168481c0c3d201000940110020380c023003900511f000984004100d004202c207846d0902001c001c0283da600e4005069680207220b1000740c1109000c903080c00030a40b0014000b45e5520940300115803410082103d115241c84c503031941d00000008075040c0014502001040b02d10706101e8000c2046260103180b0720001c144520401f440b8a443d03201081d8100e1082c809035030190040740924602e11521b1400c5070855100c00f091f010042c032032220440614200c0c09499000e103200074001d2600d030389420104900c5502c01d00005038000c41c00f0789241c14014091101c01184006240a00040700d820340014104a50041c007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 194474460 1250 194473210 194473243
    0x507210f091401030905010b090405070f141e040906091b0915030f0201110718052505210a0e01110c0d050703030605040f060f2705040807020d08040602 67
    0x806020760311024040c2c2d800641c0034600800c00d141c460a10b140106525070229400c84039100c2008140074000510b1000c9454007202061074695130303080003000c4c4540801442e80b2801c1512046594166501410400701c0c00a01c0019461f07115aa100121500e01108076107918520302580b082d4482040312400801d404c9006100d281d11141c845d080c0310410780001410340c261041c4140941e4411000c00d0204c1d0302c0b000880d40c030341c0c2c2c0381c0003062680000e40381503259071410803000901c044022241e8005480c0310703c885110b500071201d400d44d141c1d0480100307800c8004c0c1d88100c000303170082c00f0796140380100040040020486d100d42000d900391040e40c081141200d10811180789101000a01907030700e116149802c1e600d03944a4138048025080c0365201e15881070400c81e03110145006a4440c03400c07500b1000400704895540d5034004100000a50841001c04403036129400700c140301c1e0000795201e40304089030b903d401481c0c0e00040700e034040003000350b40d00040410b0a0105503010840c80038148003c41 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 194475710 1250 194474460 194474477
    0xc030f0b060408071503061806050406090204050612040227091005010e0a0f020f030702011508010c050d05100504020304050d080708060904030e010e03120706060b09060306100507210f 81
    0xf001e19a82c801c80d01c1a90707003600060510711109882036200c41d02801d958041e240905601c43e9001c4080c3c0703941c0c01568442e500d44000080c1b080c1c4a40f007210201e030005080e46040c800d48200303583c3d007524010400d0382c21400154540c0305138a6a00c03098600040c00040c03014075424018034040c03408608880547c3c08070314180041c815070300d01c100501d0340440c3c003c1000c540d0101070040d500190140204d00604040d0200030f01c0002501034024044411400500c3e443c89540e4000040c207a0b10202d0b006400b05400300320301280040d842d042a80d000c045289c484420503a078802160407a4000c0382d007a038042c5c103c80115020980c1c4414525041135091804e403c85060880000c3c4100707902408c020188018505000020390240442c20342a080080545202000303000c50a00594000c503000c03250365182407000306122040f00e0940d601340304017a00c044d0469550700e0900840001c2840c00300240001844404009901c0000300c060302101c2203c04c5c80b080b2040e1201406480205200b4002d101044 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 194476960 1250 194475710 194475719
    0x1120e030c1e0f0c060d0b03070f18050601050d0905250f060908030a2d03021809090c0d020307030f0c0f06051204020405060a0329060d05060c18040c030f0b0604 71
    0x50507808501307080780d40c40d544030201711107000207106045c80030740c0600803008000f844110ba0034000048805441005101c0c071180b02c502c03030844008550031030228409100201d07141c050703a44540451407150088a282e40c5c103a11144400d05d05d45c400003003204105000902000c154010103400034184c03404d2043c80541080f04280d124040e929860b001c00100d404001e00c1d84a13507510b0030000c1540e41c0240200841c080030002e010b5402354002c19650044129060001c7c2000b00d4698802c0b84040080c1c07030007078024401c010b00c100c0b20b00003da07850b109800c4040086500d00030008004c521410128030420b203000308642d6080026070101c070520105006158132000ea50080b1544641e04860008040c0d42c3c40c0001101548503410240450254806241100c0300e5802e0300c0d44410702883d5424010741d5030204000724140b440340000d11580007203001c58202107a58000d03240c2d00100c4c0c10001b44803880c04000c202115840072190b00083d443d910030600d801c2c0e9520400040d0b0380300b40d890703500e0203092 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 194478210 1250 194476960 194476963
    0x8010311010c02060706230615040512120c030403030807031a0918030708040f080601050a0308030c0f0d1b08130209090109120804050d0207060e01120e030c1e0f 71
    0x800c80303254144001214903000315a02c03103003150b03103081c0e02c04020014a90701c42103210611050445003645001c546000c034202c0e2406c01c80c21402e0315030401840d0b20705400c19007030089800015070030030003520843c0082a00d002c1403502070910140c0b07a500547d19185503003001440900d000e8120b005061800888100b07401c603007010742944000558103881d4545070703599840b81c4407003484503400c0705000c04180b0100700902e400c01002282c005028041e40941c4951005844070303c01e11400f5031040f01028200002180f41014650007100302c80b0640c00d158080c0e110103aa03074400344074001213030340e03450a210011802203a8440142940c0c1307061070349071a00d1401e05161000004003c1d101d041d0500c000750510350309400450300d1551010350300314000991500a016103c0682c1c1c110b845000324440c05240f140b00003a500b085a40302c0d65002111184400151180d40c1c0c020344810900b07450304d02020544c4400c00c001c0c004c01e5041001495129a0f01d042800b40550070b2001070b841d500501400d4644590 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 194479460 1250 194478210 194478233
    0x2150105060a0f0c060204060e090c12070c11060301060504080d020c062706070516060804051005061801080607030e010b0a0b030c160807060c08131401020706050907050a06080103 79
    0x42c07905005403c403129407800c1d1a503140e01c5134003c081500018020400b940d2000414518001c16180c109003a1180803902c0700a0181c01860303044800d420b000680130500c100c0660715118001d1400045242d0440302052042c0d1090b0410800301c0c1c000031b0b042180c000300b0002c1084240f514405003216035103c90020340d0a00c500032880042d104850104501c0c9058400c07110085d01e4001e0505950b0406498990b8894948c20740707240c2c80c0c88200400103801070042d983d491007540c1c4031010344248689909584001c02010b0001d580100047e42094906451050902e01810100b401040c41d0300c0c0c1580005c042c0c4121034500301c07440c0d0411841ca1500d031a4480c1140555001030b0321141c881c1c1d035000128443d4020400f50b031040700540343c0c441044c448000000c10065010340d4040c4160800d0000646100d0025201580080001c0200707030302203890808190b55444048001524000950716040e003510b80507030f074522150300980000c00c204d2074020002001441c41d4104200b480d0300d10b4591407281d15 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 194480710 1250 194479460 194479477
    0x16030201110304050d0c090e0303040b01030b0406111819061403090a0f060911041b0c0201050d060f0e06040501030305041a0715020a0905030f070b1c0507050a0215010506 75
    0x448a40c040c1c1e824400780169000303040003400490021000b410540d042d1102c6204007081c151a00c8180d0540b05404000c59120b55013161907491103034610b40d00c0c2e000c038a0b0010000d845040d5a200703003505400a50f00107109094007800b0400c01c2003100390030840c107c070410302222132041020108000b002d070403c030400e079080a840d4440c1d80f242d507045450b50804040d4030300184460f140c00100020081c031a0f1050b441c850142c02100415001c1c4800c0c00101c40c41e0510401000c1f580400d03168801d4450304800040741e206141c640d09200030a51390707905969058000229640c50803009102c04901c0c0b14206900a10880c1c3c1841a94507503280980b06100e039000c0c0311404035101032078191420801041b00c0101c1d83c89012000043c0016403424000d40154201200044890702d000800f440e001900a445144003000303003451300e14004d030a08603648401c0301e04500302c07038503001d881c0b030303400c1c01d101d81480f841441e103070b80d65202c0c1202c400032301f007034058603403040010151300050110351280700c00e80d07a012 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 194481960 1250 194480710 194480717
    0xe010e040506031204032306151c080d06031707020f09070e060d0c030f1a1003060302060d02040302030f060f01030803091e0106080f0a0809040b0a0906090c1116030201 74
    0x1510303010007003070400144d60210f1545640004001040281444e101c12001c40c5001e0700300841400b2141c4180c076050207982480f0000e91600c03000c00f90b450040b4044a90f54031701c1020020140c02079460810345e4108140d00316400d981c03500c0410501054030380301940c1c801d408203983c0c80c1c010580c1c0000c1e00074941102d07150207144900c000401d03990007800307004440e100c02010076403140c0700c0c01d50700c1014000c004450710009091501030a20440d0304d02070350100176004400940304c10f54038018003440c2d080e000d035000e08250301d595000001d80c803540d000304060032041101583c3d650442c0103041c071b440010050088142e001c141003000d0031802c00055815030b80c2c000e40b030613a00d40b030758042e0030b00d0002c0243e184810014008010300038035405510400031160f0620580d00c03012a1760300340980350208004040d003503150800c400070311031420341e20200c91010007c1020040380e071120408022a4040c0d00300400003991000c1000388160003296038a804070140000705036003415000d00f5081942135101c000d052 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 194483210 1250 194481960 194481971
    0xc220e030f03041b0501080906040605070c020a0308070605100b040b0d020720090703020a05090904030c1202010b240d0b01050c012408010c091e0302060406120c0e010e04 75
    0x4918061044501090684002988038105030420306030f1181601c0f540c502001110340700003419405214140e10400c1050003801c2141c1c2c0c0e0341c0300c00010b04401419201003000c0b50301214011ba4407112604007131806040c5281d2541d9052920408441018206055080019000700003060600003190240c41d0800080c54850307400740f4003c0043d002d4454010f00f92404024002000c0c588212100c04005080300ca502035521020001d404138071904468800240301084440740c603080030140313150014881d103030413044c0f5032241c2c0b100f1303030b195295042040060b5140c80702840c1c0c9107003d800c100c502e000740c00d14122003100d031004907002d1841042c1400c0c070142d80f20b900840413a8000c0c03003955000399404d0002e00040218001c4034cc80440f6007c0c5211034074030159400b040402c014894007100302c0250b00d500f41110b0a00a1142c081040b00c0d00003000450101008001a110200a000281070365124214a200e100041006071454070f041c060030880da000300b046150307038445180c1c5503404099400284 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 194484460 1250 194483210 194483231
    0x3030405121e040e061003050c040509061215160f0e0405270c090c0301030b041b030c060302030115020d0207090908164715091005030c22 61
    0x7003040c20702c0300c008040e0105001450500c0c82c0103852042001311000400300c070000300d05408803441524803800701c1c94180024861818000e21035904200000d040244800c00032a0241c80c0501d205191800f1512803030610500703c0000222811220351801c040c6900516031100418030403071f0351055032081da11800400d004010b0314020003b880a17041e00c0d140c80d4980700920503514102c00b090750780100400d00000310201c0c0d5a00c1030305d0503207510014100c00c030b88854444101b44000030381d00720580c0d4044940007000840c0b02021100030581920003603200d6241c0b5850080210302c1c16404c1d029034100e00c220b103031100d0f03010a00c0000c2c0d80a0907000140c2c04040e0070203215900642e443e260140078500e941c0030a100108825510094070030b40d0603800d00c0007541603603542402d41c42c4401585151004458081c0b2800c2038042d61141c0101002995460200000703012080f060b81c450340341a502e000203001030f0074107221040a0a00549210600c2949640d01001410036108103840075a594410740c0c1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 194485710 1250 194484460 194484487
    0x3120a0209030d0e010207120f02091914060a080109051c1202030c04091b02030a1b0b0f090706020102040b07080d0618060e1806070c0507120f1101020303040512 71
    0x740321030405402c403910805082c60280c0a05500d02c5080e015200310300000410408081850708a0742d0711981400c0201c01d9175082c410303040c00143c203019058202e12101c1103032440900c503403040c0e10401c0f80c0980090070080c040c40214505074000b80740c564180380790400410400900b400c10045c0d410503043c98001003101c11618118222030054580c1e0001003440ba0796426840070b407080d10303a005420005542001b0405030a20481e087c00700240c0c0080c013034130341024010000050f036070100c00c08604003040310b035640e00b0410808940c02c0400100d10030a120b101603040004002a040d01e0008516007404c5c00502015806004d200820010000500c2001e410050300100002c101030f00020034101002502d0702c0291800f40100c4201011003400100c00c00110030402a540c0a014042c0c0844d44910707500b00d98603905081c040e40d0300c0c82400f60004040c0b55141c440801c041c0604610112109949040d41d0141709440d49141154414410f11011410114403c18400c00d80382c03115035a0664003141d81c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 194486960 1250 194485710 194485717
    0x9071b0b0c0922111606020904020708160302060a06140f12070b0c01151d060d08030c091f0806010804140304180f0903050301090f020d05040305070c06020a020303120a02 75
    0x450f0400070100040744a0244140040c0d00c0d2403043c0710a200607a40c040c0d203044a4040c45041344108268210820041046540144190b050140015141100c2600d401607660f0000481121078031100300e01102707142e0b05100c810f800c8002188180040c0d0724041600d68010b6075025081d00c40e010004001c0741a540c2e004015080c407507100705503000e481da076000d841c4158014401241c0c85508108090319402031100c0101c042d00d15801c010310319500c6208030444d140074003c0c09181c02100422910000c2403a0901841c0300b09100782d00a80c1da11a240c2c117100d0740501e407054600030740c10408a1241c0d429042004281d10413402c1c40c0c58116030390303a4100074030301c002121812542c50000050200d4000d5500d030800c8150742d11081d080c03181214020a4004695a01401a001134001d0005000903095604a002e80403880d083c094204011900144100c0340182d60131404581d0001c2c4c41e20402c041070225400621690011f02801003481d00803c0c1c40384585031018143d0040d040018406150b1681074 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 194488210 1250 194486960 194486977
    0xf050f01091a18090706030e03030c090103020d090b010f0801020327032209110a080403050f070c0f140d030f0305040f080a0914190302060c0c0d0b040209071b0b0c 72
    0x1460b060700e52502d00c80d43e10440c00da0740b80301c042c02090008580c2c24040d0280c184680d9481c0003c51955460760001a400d41001059038100754080241d080ca0440341c0c0119203155010f5a44950194948580d401012901d0361010707265034014020800025440a05150b48612340405181e0307203040b400c0301c14103604c5000031200511828841003203002d00f00554503803e540c0702c0c0c03008110502810080c0c08045c020b00703c0c1840024070640005000034800c030f01410320032984290280c1091482da840d688444440d400c203191811116208002e0402c0f03641c0d04643d202070503200c00d00e00e002c40d900c0091403000c901000b2030070326450706c02150801010711104030040390030259070b07519010024402802004103100b91004003c0d100503203403403841c026403d40078114003a03041038001c0b0310b075a00344021a0401c40308180c150145215046460f103c05131900d041e40c0c810018001c1914142c810003e601038094251400c0090f101c5810400b51002c00481c81815006042042d50350741c2c16011800a03c55940c0c1c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 194489460 1250 194488210 194488219
    0x304150e060f07033905010f06120c0e0720070506070809040501050114040915150c14010504020a140d05030a050705060f06060301150909091103010f050f01091a 71
    0x109218441207450141c00404d00c42d5039804031a0b21719401064201d4020380c001110f01c3d101000c00c10342d5002c205043c52056200e200046481280003505030108d07000d0394130844e046a00a0125020010300d21a003102420108040e14164104004014100c45403214014518002c01d0495820710808207c0000180700c014510b5540b00307901c0c5050400c80d0048070700b0740d02580c1040700200d1658050303d401345d880881c2ca0340050030a4517240060002c1e100c503044409100301701c0000400c903201c80c07960034080001240c40308002000c10b0310700075100b0b001020210751f00764940024000180e4414002c503003203c14010611344503621900000fa08102c1701c001c014207030300c40041c0c82042070b50000b010302981c4d80980142d0719155a1a4822014860304554183e40040100014001000c180f00c80c2140152149801c042e07050f1100900c0013200d00300382c420b0710740ca02d5650300055140b80074010010034104002d01440b103070034545c00480180c6018007074030540684940a5404100402c001c05c00c44000061 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 194490710 1250 194489460 194489467
    0x2130c090b03071b0c051201060510050f160503130602010b01080c09031f1b0201060302030622050a030201090c1707090e030d060902093d0903120809010b120304150e06 74
    0x3500001c8980c03544106c80c00740c024204003000b440c0b0107100e00400c4440c040c1510710b000e951100c00721450742c801c103080d031086c00081c060300080c8138a610055010510520045940303c603001a5040881850b81c0a9021a81400040300b0141d9000e04019041054003400d15141c0a9103030010f0b091000c0084540110b90103a0310710070140f0160b403c551410065215180d00c0000e810104030b0aa80749400003942540c03050012032048220680c81400c0d840800c6803a0400052950f206e074100000701000b6030050391541044800d220035412008000d03c040d030402d1940425030040705449070310a10880460030f41d02c2c0300038070701d001042c01290400258000200035054032084004029041241410b00403100e60114018200000341c40e07820718690485400052144988940c0040182042941c01c00441110020010b4030888280000c2d02e8542c950045074901080c0c42421500f10080031807103103903804011310004a000c411681503540e400701030018204000703000da40c081107686100740c100340c001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 194491960 1250 194490710 194490713
    0x1140f0d0b15011404050109030809061b151602060a200d090501110304080f091c030e01030e0723040b0d0c18020f0414040b040204090902130c090b03071b 68
    0x11210b0414032200341c84034214940c2001540b45640228052a8045144035400340b020885c0b20740900f02e184001010645030072640c0c680e0540e222a1442e01c201591300072100484015056a506640144603010781d407a468a0f400e0000c0d65504007600c1442c05550f035401411b4049800d18007078a8031034405105179511141c004401008060460f01583d06528200000c4502c404800860380541e42010042d4204150010404540e500c41030007907501680c60041c0c00d0f40240041201d1580038040e460b40c131045100800050250740c041c24045803150070020341070059020610300070071001c00094110940b4910380d0082801460003200890f0720070182c051304ea04002c0040c11075000d032a101c0c11140f501c0d40c42c00310510181d01422019000a8000b4001400400b040c00c0c2e48916204000303201207018803410010404aa1094002c0d12400f910750b2074500960402068100703904e080d15800b00702241140800804404890142d805810400004603200a00c50769000c5400c0484400c0801c41940d507 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 194493210 1250 194491960 194491981
    0x160204091416170a1b0906090902040c02060402030d0516050a0f030f020c0f2b080315011e0c02010c0501020301080303270718090602030907050103050c0301140f0d0b 73
    0x203000441c050b901d01400c0200780c0c0415240d003804a02c0d03e8000611100e10181e07104080711260310b041d85005981107500103035802e040d008003001807c4100300040c0d1011280103100a80d03240c802001e055500040c248001a1000902081e0248041c6010b40e00c0300f500352040400050b074000040c180d8801c0c04003172000c1c04805542190030610903200c00c0c0201c08a4041644c42d100b1071084035a011802e200c07100c0c4141000020071203414051500941b01e0310104503080014007a050f4299204c40d404030030004d00b825100c03550710b2480403d007851442645480660344018540c0b280090800c10076000410441e4024070442c0001c03a400002551a9a150603030269070350000c075005442c00e84140700002c0301c0c11100d44110a6000808040c0c03a9960408003044600400640700405007560703001c4450110b0814809107000d04001400b5100703072442e041c00141952006411546005001c100410064242240c81c848803c0f09580070340c1050030080018030031011444014069021030002c11040000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 194494460 1250 194493210 194493223
    0xf0702120f0106080d08040605040305091c02010210060513150e0403050c07050f0904121103070308040c061b12030908070b0907170304050f0a09110418111602040914 73
    0x41078000300045662100f1490350b0b000ca146005001c11154400b26001c66510781010340e1041c0070341806403400800764041040c0d40722a80f6084148a00e00030000211760303060110300314420030070105020040c00d00c400640b0741600b80c00e0811100e40e543d00340e0000c08504090940041c08000d070851480e03e01810054500d500055113000e40307010300c410210b0715140c11b5190140000c005440307840d00d999540c1d590701e00c980001e1440801d001943d8003041c2c28440400007040d03075601c070b41d039004024103281c64001c01640d11500002d080c0035559120344000c03501580e0312200d039500320b00c81741400b0322521825001094207102c041c0c80038000090781001e001011300d0150141c3c8104084071811a510b00410320071148040301c14280c2c2d0420401000740b071901106081d00f1703150003070120520a9480000204990303c2044d0900e1440f40854100210064927818a22640c0c0002c41484a01000c44603080540b05070103840d8880c00c004c05101003591140d0b4400a0700b0740e846402c0902c1e40b45c0382904960b43d000c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 194495710 1250 194494460 194494483
    0x100c080a060504050f0601050705010e0d0f020c060405060a080c07021f08090c0603070f050c0304030308010f080d09060c2f0301180c06080405100204090603060b060715020f070212 79
    0x20700303200d00010705080c148141e5114600f0380b8140001030301ea800c011600f0b03503c4044150744640d21490f00700c503010b80511810960081c0307078075030101142e02034401908080f880b805980c07051005000411407500c0f0002100c0072540c0c075190010407a0399a030b03550025801080d001a400041ca000741c0d101d03030041361b4028074142c45503480303001c1d007070303540b065407030358841c004e60324950480c90a00200310b0440c014a65034030b81c24241d0900310300780080c5040481c9550081d13441075001071503040040000440040820b0060200d90014000790800804080c01841e03241c0b09500030050012203003001c1c4012000300c503110130f5140807440503607038941880b401800c40040d4018840c1d4130300341025648556001e4001a015484440078164910f80002501e000f08018000d4545000d0401e13403607028100c030301c000e00c0038003081c1c1000913015042d030818004070303040204428007803001005100c0105074548442003801111000c090b03920071720307440f4240c5280190302009404c200a10348149024901080000c1e0a1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 194496960 1250 194495710 194495731
    0x1902031e010b0711060306040603141506030a0b0103082a010e0c19050904050a050304080f16060203090f01121404060f050103150b1906050a080f0603031b100c08 71
    0x9980741c1040b8080c0e4458548000c00551002c2901e0b4864100f14000c0c6070702910080002584954039103400301c55190a051007041d50b0043d1001c0780c1103040428940f45c001a041d001881361150740c0da905080c0032010300001d00012800724000e0030b41452812141215903880892104401c0303001c03c01d40c0649440340c0340014170f01030092821524141480081101901606000082480e1a06102401c24017800a0392540500b61140b00450000c10040c0020b1002c0302c028041d01d2400b00d0170354144051100c0074a138906100c0303030030400d083e4000700769070854104881c0700c0c0c5003111000c0141c0d07100381074803080b140700c0f4144180c122001c2e6120030624800d60003410f050010700d0b408a460310840c0c00074040142280082c1d05c2503034030a01e45600c01a000745000e000100440b945040c8649582d0040e80180d001900000790f001d0b405a02c022503a4200442e032282101c2c0742000700010740c413070040f800c0c0051075580340e941d10b0300c040c0002c0101c4406150920410818051540c0d03004040510442c3c0f0910300 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 194498210 1250 194496960 194497021
    0x41d0604150b0607060f02090406030807060e0115140d02090c1e09030a0b0a02040506040e09011d2e0c081f120803090a0b0c0306030d03090b010e190203 67
    0x1c10140103003204004002c0c800c41c5410030942d280700060450704183d400059003400103c00f107403100e00c9940051030092813295210615890554141c031241c241c8404144d0604131130041e0354810881c404140e805002c42900c12083c4940131901458003a00c019510900c45000d1109000d00322000701200d0802c1903015805020303510340c101562107040030300e50301684400024400300b0650401035070011003205d03002d032401d49d864001070760a8016802c01c1039440e4140c01400240c00091244000340c1d15404001c81903402d0315000c0d0f1f078481022000051815060201c241203610107030b42149201804c1030301c2008040c0a000d0001c0c450305c0101c03220901c00b01200141c03600f440007401740340100c60a0030710390000c01c00e00c1d070381d02151070b080544030305054070480e615200042c0d886000584102408080780d40c0764038000041518000c0040c00c02c805140c40c051024000c2a042e00f041419102a1024606292600545540d030801ca0b40064070f82c0b28804004d00c180c030458591811440100000107842 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 194499460 1250 194498210 194498243
    0x302221118010206060a03060c09120804051c0b0c0c030d0f0b010801080f0304090b0a12030206040618030c0204090c0e1608070e061e091c020316120f02041d0604 71
    0x2d4480e01074170116405400c45400b080001c1e0b082c0c211000c0d40009160816055503244c84a9541c480da052088402460104040c0154100502d10140104030029295034111070382e01d4460345801c0240025032010000114078900f894200112009113598040400c820b0412901e9a002051102c4d001b50003d1509c1000140c030000000e90542001056005185405e01e0b100d200710003040100340982d0000320304080040c244100b105a410640e002e40c001e8500c03031800303141100494003040081e040d0545410700d800f001c00c1e0300941107170100354161400141140682021070000e4040c0d40009001d80c2c801007044105e000c0011000d0b0b0540380c03a100c1d49141c2d03c42703080550720400d030001a150401014002c020700b01c540004009850741d01d9404846c600402c0c0400b04180640a44162031040e01c41e20200301141030800c00d006c41107010742640c0d26440d062811066500f680c0a00180041112042c44010340d5103d42c0000803102c0c850360448103180349090860303240c0a0440c0c0640304041d81e29003480 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 194500710 1250 194499460 194499463
    0x30c04020a1b1a091c2610051005071209060e060a03060308190e060406020d110106080a0f020f030105040302032a071e09090b0103022211180102 64
    0x5100d00704503214518050407010540200044880e000d441c110f51101803400010b650900440c05a0040381c00340041a010341907441260f80b8a8802108024610780c514034510402500162488418010741c4010b4943c074005c00b64500058200340c0d80710400d42c5482460325000340c010094103101d02c1d0442e4104107540c400740c0304c000a6100d45004914446200007440c5041d00c002d0045800310b00b0009186ca44a444021580d086144501c11820602081c3d03200035400c100e8032450940d0032a12a450326050100007903c9000d034035801424810160710180114900790030a1010708220700032074124070450306010014600c8008164055865084030000605042c041c0c0c0c0e1080f90107400952504201e00e00c00114071040c08041c4c1c0c000305a48a0f520075082060102500902401801c0100c0440c0c0d010a07803080601940542e0300a45010400400140348101081c11641c049170130814000780cd00c451140300344031000c90816030346070480040111100700c0280c00a03501003070300c8004040a400040e0f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 194501960 1250 194500710 194500717
    0x9010206070c020a0e060612090105070e030601240504080307050706031410150215010b1207022e33080106060503041506030b010306020403110f10030b01200a02030c0402 75
    0x2030740005454500b0300515400314217a54100001524035072821501d0700d0000c1c802d0700d00341c42c1c19400b40d44a40c2032007295588103400229500044014218035450070601d100c1c200203002c031038010402d440200c200d0650080080d10000c10003071050b6a81c2e04034900c0d1158480d5214040c80011030301c0c002c480300d80921071121007803003601d41c0303406402182d04044106001510751906401144507070301541604010164030300340204200201d090b26107454200c169816a0010900030441d44466244505880c004200d5020035254545480c00100b00d2185000a802c84410112034914070a43d01c2e183c4549400e0488284c0140b846a40c06040e02c8058071400d0341d00622850300012810320109000c5144484bc1c1002c03048002000945180e40f9074443c40e0034039099100343c800c5a4086820414490324416510803c00100d07150001e400e01140080c4a55482c80812020181d88070107001581e40981150110520001039160000b03074040c01c01580c1e0041c0141c22400385c003c0907180300d160706040c001d8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 194503210 1250 194501960 194501963
    0x30c0d11070b06010e0f040c02070e0604090f1707060c0c02040c110d140c010908190311030c070c050901090f1107110904060f150608181218100509010206070c 70
    0x202c0b60907140c6070011174280c8451700303a055110380d4a54213903c0c5a0b031907200380c2280202c1d0303401070070641d4500181c00d00d00c440700400c5d2034061414100c5200c000303a08c0345040b0742c8041d072101135000c1c548624104800c190142d4940117140c10715002c44040e51a07000005400101c0c4210f400740314590a02c00b007111a1403500386109102d40c005030142110034058000c000350072a580501a00300b5140903101c50a5030f885240c00e07a071030360002072040d021110308801100d8601090405000b00103d4088421a5100045c021003406801207043c004000440c4100001014020302014145d44c4a10030f91000b02011461072442034604801ca0041e54525000d43d817400340c0003141c1c444205d01c2ca400740880c0703d00c024811660240e0f01d80d002074a10103188070b10208104000c00041303040e814507001525414001c2c014a09030b028606220300c5161000540100c8100040d40c019102c41030240c6c00c031094071603016100d42c80104046c0d0a0403681e031040103490000400d0b42216120b0312221801c2d206514034160 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 194504460 1250 194503210 194503223
    0x70305061305010207020306070503040c15020606010e03010f0e0705030d18050f01090906120b09011404060f0608070b031e01031203020f0d1a0f061c150b030c0d1107 73
    0x281400703a03941070155005002c0c0c0000751410049500090410800311075a10205c1c40c040184814050541a0440174000e081101e0000031320601e4080d58a00b0000d080c2c40c1082100181c0043c551000c0d00b10034486024102e05114071402c07104026162009401f0b1240070f0300c0742c0745084060601c200c1d41003400d000101201051103052034180304c184104911000d060085c49080051815070b644a6280100121181c0c10300406135481e2804a42c40090b0500e007103681460b1802d49011101e10416410070b51000000800031007100490b0040d0604c5e50245e00240140315000130000b81050066110302002c2491100b500242860b0001c0c15a003804007a1494005203c6007200354020307801071003100c0e801e01d03199040c00010341180054511100c0c0780d05580031b400c1d09200d402c1c101014550300d404003c8901038200f4030302c0c0e10900c00e1880700003140014175860349000001400d6004001c030280451071402581d80c54898030500c415403210002e01505454001020003c0c8042c4c001e580c8210b070b00c8070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 194505710 1250 194504460 194504473
    0x3031c0c0f090e2a0901021203040b06040504050111040806060315040b04030f140403030e0102010c0206130b0c09040903050304110105070c0e09010b060d0606020105060d0515091203100e09070305 86
    0x1064500000000704504d8907030030500c55020300e8003102e03c41e0004d082c021601c060765888a0500090422940d034500619014040c0140000549500c2005030b1042060f1000075040c0c0e504d00300036004d00213044101c0088000004c0c04500c0b040041007040c80f400080d0115903c00103c071005c21b01100c4200c03806403444900b40f0214002034821465101580f074585400c2520b52440455040d542e4029841240882c182d2590b65401c4e503028051a80400c6550000d40744510342400300c00317000980844000e1800d0580c00c0003e22352010501568100342014000b0028201c0d40d15024002d03500648050340da0722180800e8440641c4101300719045540c1c040d40c2c08143d0f618000c504140c218000e000ca40465407203c51420494541c1c40c05403204015200003c69180e00d000c0010b0b084800190103180100503806600003c90000035001c41180c40c0d09000e14040e690f2404100d00740b04815020b0003404400006000d4440540c40c00e40c020f0311103031002c0c0740042e11810000303942c07618035120007002604980c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 194506960 1250 194505710 194505719
    0x509060f060f07030e0a0e0103021201050c03070c080d240801020414040c030b0907180605040f140d0c0906060e04050906010e100b030405070906080f03070f08070203031c0c0f09 78
    0x30000d403c0c20f07880b9040110b02141a840000d5855401e0703001591203440038801001581342c00180d400039980014020415404d010803c0340316840000c0544040c042d0f074550390020040d160049a40080441d034003084081c0c01d040381c040e1800305c1c031251804622281d150210301c0b10010320888003112242c02c0041d450201c00c00500c03000c0d0000710400014155aa182c541040c0c903803400c01441483c940d6244001c5600d84842c400c0f0104250304000200007080c031040c48072200b40380c240070998841c400c02080d1783c8220b10004501484404004040f621090740000340c403d4184c00220070b0303402a848104a144440080c00202d410490395000b06030f0143c4010801855120a0039400007030f6040320422160300c400905406a0054070202c4c1e2603444884104042c00d031a01c1500c000e003a0003800350180c42c1080ca807840e071b0f9019070040649114009880b01c0204195030045400d0140c2c0a0182c9071600c0c807003159001d0302604031080c402c1003402c0180c1002c0c11842660384200c1c16100da20b851422a041 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 194508210 1250 194506960 194506987
    0x1020f1903180305011802090109090b0a020c0708030408100b010e130903020705150c0d021c050c010b13051005120a06020f090607050601030311060106210b060406090509060f06 78
    0x281c00c0d0072404407502c5003001c030220340c080c05251015068146503001603a072900c10f05c000c1650507800207546518090510000501c50705106400c072060280140c0c4562113600d07410308100071039001c083d140c0300c0042c00080000300031520400245522808000f50701603800159a4200000c0200c1d40c040c020440310000150b1075407066401c0ca00901c1100c08154540c40440c0c2d549a400c0c0030385000c3c450116070900d044a081200901412492000d070000b41900c0608003a824004d2401e00140400440c000b10061400d50008110a0f0f0080202c42144105004003005180980700040b4182a4150203d4581010798164441045040c028014940c0a449181c000e401c840c0a0703094100301001110071945d03913079021f01030080c062001b40c01154075504c0c018118030030701c000388049a003001e00108050758102005070f18807074250a100184224540b01400100340c40c40f2800c0c0d00181c040b401091460f0321407441b409032039050764086001d48900d4100704808148058103603000350200200e5035140d10 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 194509460 1250 194508210 194508227
    0x1b07030c03091e0302030115050f060a2a061d120c01110318280b0705130602010608011d060c0a110a0f0b070507030e15070b01090204030201020f1903 66
    0x80c589a201551101060801881094501c180f006600b140c24401d600c0c0a201d5120381e4920300403c2d01c0e00902e003002040ca1882c030300480078429280461110070160142c0e8000c2c1500360b40c61143e060304565580040c907090310110b01541e0562030b161034803a154000c4044107c00101c0c0d0001000e03d0700160840207000d07400a07150000d5952181c1481d144800790001442c022040058111200542c526074181f512035248110080320030180000c4071911861094440103540040c02c000c91070340c07024001e0b40c1a216400740a60307000500b55000415560652052042c0e4840c200203100740981c0d160003150b403883d07440c8656656080207001c01d00b045280001004110281d00780009985c80c0509903d00342803d4841c280c8409001c0440e8000300183e241540754050501e090403403d180c0c0e45d8400038075022401c150a401020004030700902641e28000b510000c41d0300c80c8641c2c0030756854010a00107908a444124058451300820a000202c08107410b0380c0818021040c1105c19117a480484009a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 194510710 1250 194509460 194509463
    0x304061a01022e0905101803050d090c030510050402100c0b24060a11150c03060d111c05120c100902010309020603070518060913021822051b07030c 65
    0x101609601844200f54021072180c14081c9000d040020800081e04007550340d00c078030802520000c2d80303100000039003100603208000a041d100007040481450050b103880040d0700003400301e2042c2c04e80028040150b400c600e100700c0c030a598584150640c080140d52074264400024800190035000905000d03030b580301c14124401508414218000ca4804074505078042807482d00024000c0300e54044040d0200031541c0b202101c086122520b02d0b000c2010704640c080a050144903038071403ca16028041444200c1c211180000c00c83c00318800422149441c4200c4414111424026800d820101001c010191400d914900c40907000e000342d8000d041000300b41003041241819940c038080400343e01e48002a51107020242c440c95684d145d0001103d25220f46c0214280c4601c104000019841d116030300e80703200f41c605141c00540c485a012070707113807941211076007080d80184204010710781140c65107104c2c0d190104110002c1007103072504074200390480840018805a18010090000000d204140041e2481d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 194511960 1250 194510710 194510773
    0x51c060b04171b061903090c141c030e010c14060a020c1606051e0903060906011a03040b040312150602030901170609131505010306020304061a0102 65
    0x546a1003504100e400a0704081900710100c100c00c200328808010410041036030302000700c190405100050707024802e000d4217004105170104007180741406a00109007080c1c0c8901d2a04905031607082060488d0703511440c10b803080e28038062031414406c40a00000100360141d8a41e106510070000540d40540351440071208122404812601d20105120040c02840b0014016a480c1c403288015860140c01c1b1316443c0c4a000718040811441e5009011a403102e003030f00070154085c4442d00c191500501880e450b40d41c0500940d410041ca03d1004191541a100c080e1612000f074061060150704070300040350010900903208012502082c020388a01d4680100014013003441869140c00164a4050360b002d0b002507400801e070201c0c10740e0070000e01402c40d02040a440c0380352911500082c0100800380207039201a50b6001101c040c415204004814004414814081540d60340380940096000322029103000e4074203d03a0300c12110440c0c4403501038160590003002ca04442c00f40c4103140c00078015120400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 194513210 1250 194511960 194511971
    0xe040f1703040303050a06060206250207050d060b0307170c041e020a0201060509330f03060712050f06100e010207080a0503070c0b030c0a0f0918050618010501051c 72
    0x400c80c00c40250300c0765100c0e60340442c0906040d080c900c1580c02a80003076087d500241c00300140e41510401c1e80319021035032a20307030701d030fa00011500340d0521704590441c0c0d40184070181e043c1c0c10300980341c100313a080360f00990480d20210764468000c01c01d402c1c1090300d02d0080c7c2000d1000702c000c0c6044e411a448400e104240f4101029040c03006104a82c4100c0140b00941d4440d0340030403241c60911001a4040d290010441340307403081740c0c062074440e1030a4040000381002010207166540f20300e01500c0c064200030f404c856183c20032082c0944295041c030403484c1c0e10360401e03000500c40d800419039103002e01e2015004450f0200c003940c003521800055542503046100349640004c0c001410001b01403898080c0307001d59900c0105003031002d08002c05401c41d05004c0c0040041c842c4480c4050308880041d905450042c151880743d401c2129607442c180c0c000168a48040b10307000c03850740f85070702c2907000e4130040325482c184c0d502c0b42d140603800603000d21403240400e105000d1441c400d00c0005500c1c0c0003400b0703060b00040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 194514460 1250 194513210 194513243
    0x51608040909060b030705010305060a06081003020a0e160f0c0f02040e060c040302130c021c020307060c091701050105030d120b1002010213090504050a020d1b06050901030f060e040f 80
    0x450300c8900080d206603031500202c03034130390400380b210324054442844c0c03c3c850340c5800d101164140d0b40750b104038000c112203180002c100304080000781e4080d41c2e0041c000c102d0665108660213078000c041c1d8094001d101025480d403015801070002c4840d0680c16210925055026214a0000c2c948200280e03003080d11907480041c030b0384013806114440c240b207a506d00c0e1518150300600000089000e42d410040e031404c6059041c40c0c0e00042c503654002d104144038040c0d002c0800080707085000350b40008103100c0c10512041040381e04a6181c41c1607800b0580806490380501d81001d090b54400c4c4203064154014003a2641201e1040070700b40001c1004031408544e41e500c80700800ca2a0402902d8000140d50120341c11024413416150703a001042140342c00d101605040c0c41d03103030304c903401d80c0c000a1046440041520800008690544202010903084550781e640c1d9213000d40131b0390100c602240003e142210324020241d50344200400d851070040203045d43e07503a40d07030f51113000c61802c081542e41c40c0b0ba2540000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 194515710 1250 194514460 194514479
    0xc06060801020307030c030b0f0d050a0605040b070f05070b07080709120c050a08072103030b1c02030d0311030109110919090c030c023c030319020a05160804 69
    0x4009164800c00181d4038605550014200d0b403040d5400d004060620061a2669540c4456160001c01c100c400010800151411514002e05040010800d0b03041c601048144912140c54038420b51281d01c1e60443d200d00501300311428880c0c00c0e4010038180405000c1074400740301d008815804945401c00800d1540c07035010f000d041d004c4042d0120b6901c0c1c1608800d224508000755540700800500e4000c0001f9030500307901e000e0b000007150a010304030301d07001107102c24140300f60004d103003810001d01002190040328075607220400798080d05078001d00c50740c6c0322f8681f02c0e4803c0c0320384402d240c981031a590030341e42003c040c0c40c084c0120b6400c01101c0312052101060540ea46c0c0140720a1080c0b81000d0591980380682c11000da4038804140020300d8600f03840302603056004608000119541c82901400d000d22281c00346000c140109030003d20200c40c3c0000c100c10000200a40c003c1c0c2d0b0b62085400303540070849a442c1640304818034200060780600a4450b8240082d040d1a8654403d5003000d090a4940d00d141 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 194516960 1250 194515710 194515721
    0xf060f0a030c05040c020c03030403060f02160302010f0506030f0d110114011e05030d20120a020d031d0d08090c09040303020703030f060e060d1e0804051801030b0a0c0c06 75
    0x140c6480c250302c0410060303403600c0e00c1910240311407030004e400300b0040c46000075100c0c0150f120103810349448403070380301001c4160360460b0002d00200c080740c40741080904009000300790350419490210310340b1000c2421391500140c100707401807440340140614078403d081101d00c0c0900d28000120340d03485000c211241d4142180c190b0180001d00c941401c00c090301002c19280c1d09099003d540a500139485218000754000c90080600d60242d0030000a02044210640b501e502c071500403400d408085405140d036640820307619042d4905170781c148030002e05a960b0409000d034806d4103007240d5005441807144140030300183c50384822400c1c01d8a24440c107031004100410001c07101140005d90024030441099018480c1c4a1f40e80c1c15980c0411a8505003d460505080042c0100c1d215401c0008803d0400c01c0582c60440c0220040e06090910855481c04410981050042a1148031503a16402020030881400c6040700e80100c02000c0302d884643c103c03001480304404001c10003202c82c11140118100d4000e2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 194518210 1250 194516960 194516963
    0x203010615120218040908070203010603060c03200d0513050f0319050910050c01060519150206190b01200604030e0103060501020a02090c0702120c041d060f060f0a03 73
    0x4401d6050581005145406003240c0c0440a4414050740c0000040038012502c01e4070301703880c0051410a03070300f80402c0c14013440d4002581907082000100c100a030131340108140d07200d152814841c008820300380c4101c0014080d04a07041403401c0c403420b401c1e160340f50081c81d00b01c01500005084c031000c42d154a400c02e04e0424400d01c0c0743d4000144103c8103403034001440c0c0100f083c1e103000d0b4280000b40d400610700b81c5503040310b101088008a900b429900081d44444001c1a00408201840a005450800e0340030140325080744100f20855103010b907400402c0c02440343e071000901151403151942c030300000300f4800120304d042111258811510050070a4002c0c000a1060024000b41c500751030018842c101507481c86041504011041109980019107049802d50448041400f503848285003103d41c06264000b0f50b000002c0400c00d404d040f0003080503502c0d1481610300380034071101d0182407080c01c0f1000c1c0300c18005030301c130710001103001c1400005160000c800608802c2444440000540c0d420000e410 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 194519460 1250 194518210 194518229
    0x504030302091e090c040312080408040f06020a21050f0f040506040909020406140a18020c0601060507150c080103020904020109032405150303030106050c0106081e0d090b0a0e0d02030106 82
    0x607040194500031130b500c4e0b4045118040315142c582180e0351080443e80000e80501070001d0344001c40d0070010210107031000b415000401903809541c0f02c500070b40c2c90a048074251280318010f40c500c84041e00e424a00c1c806002c0380d803a034510304109e1400e01080342e84101c60780800c1c1042444041010b80d2641c0c0104000d0510440c0804e03201c03010300412046070b600b03600c200c00c02c031030001040d01b95446441a0703900f101c8075103007800c40b0107104918440191040120091540c010b6500100d002504000a041210300450b10341d0304021071103d02404a5907035850100100d11000010401481c0004001340d0041c410705d0014440ea540e51749400310b91005024203182d07407a25904502c03030101a40b0556500501c4550b240140b540c8607000b10b51030788010300a0004021000403002100c020940040c1d00900d00780c400c56114121151082c01d401004a2494118bc00b61003030b0305010622501c424815120041441407410300000003c0e1082c91702e50f105150800030118049016903828850140100b40b00c1e503 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 194520710 1250 194519460 194519509
    0x403050109030f031521030509040603030c0506071704060905030910080613020f12070c150c08010b0c1c120e06060306130510090213021b01180213050403030209 71
    0x950203800d803500c21044002c0c0b2490700d8020091114940d901e8440401b01141c0c5170108651420308481620810301156045424002c00004040d030000b0f14404135402907040c1c0d03049440e0b50004950114003002c0d091203000d581d101250120f40141e000f140345921500c2200d01e087c0c11440440e1881183c0c2c0380c2580440c95030f004000080c101101c0f100c0740090038480440c907050003005582e400e4050701010150001006000411880c021110033702042e4000b1403c0c01d4900c050b10740c0d04007500c183c13101e181c00180c0c00000015105074072003c0d110003c81ca01d01400a000c0d40c0c003c00c03841145142d0700b0f2400c00001148005004035244100301200d400b04011302064642030b4241071800c1d0700544845c50195811284001150001c50348900d9100020700115078070201d400001d82546050401c241b98074800680b1954413078407803045054104000000b80034050a4146299001100f107001a4010f0240813840304420380503400030750700c2882400c0060074407420a0208085065201c0b680360302c000c019 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 194521960 1250 194520710 194520737
    0x30604020c10061e050604031e0b010b090109050411120a0b060c01090204060503070515030c0f0a0206090c030c01050f0904060308120718150c03210911090c040509070302040305010903 81
    0x2441ca0f04007101c5054040d2a81358a001c000c0ba50510807032001604c411202c4108411026507401700003001ca8000f034040c8195616070050840035482580721034003103407400b0720001d010f0400740545101500c0b804c3e60300d400c02c0c1c00c0c030808800454004094020300d69685180a07003d03503540b4040c00300612204000181c0710014414402141c40a40002c0d100e907004143c01c01056031000c0e0051050317125210b12545070340340c80300c5401e0103000b0181448490b00b40410396218080c0c0c00550244500e00c86000c1380c1c003647e8890141034598040040d40c500144040111041e00d03c02c1c000140b815990203040020815500d40350050550408a45040c54407001018440c0c4268011815041142c585107014242807800d03401008240c00b809003441804020128501414060a01c9050b020342c90040c7c011844401c0c2e03032030ba008044080301150103003403e01c00900342c4d00380002140d2050030b0b0b101005180a003044104426141c000784800b0400d502084040000390081c002c02d842a4880c0d01c07102007040c4a03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 194523210 1250 194521960 194521979
    0x509042316170102041202010c03090b0d02281407020d050601060302031b040807091a040e0601090e03070809150d0903021b03150a05060a120804030b0f09070308030604020c1006 78
    0x205020b03201c0e0b83c0144801e00810300c8001c3d002d081154242030024403c1d030301d0300c0d00f0703200078040d98440004040302042c0c1d034580b440140c0003852403070f04143d400d020703c8009065090081d0001c6844500240d40a401c20342c1e8085460300420744140001c0103658040b019555551078000c00340c0080c2f00082c0c002c41030088a1517001d05840312000d44100040c20281080b14081d1f50702d0441c8981c07580380b43c480d8444500c500018100c1c07810f849000d0710900c0203200c408000d56642c0303428443e0500303e030701d440013803444044003100b0349403a9a13001c0c1f042e42c6413008900c100941000b1503481e080901c0002c0007414061076052288544951003600a00090518261036403e801c041c5484035000360011030324403a24a40c9644250b500c01060040041c460b1100b0001c21407405942d0080c40426011011400521840d140176100b180e204006420303055480094030000310301d00b0b98000005a2207001c0078000501b0700c1002c2c541c05040503000505207614071043c00c2c58051640740ca60703805660ba11060108588 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 194524460 1250 194523210 194523239
    0x8010e010507020d021c111c09080102040e0c0309151501031a06120702011506091a0909011202030c36070e0d060b03012c070509042316 60
    0x10341d0004d0030000d8403c01c4041c0d02d503514068589019202a8108480c103030045003000e800210b104103c40d5030300008008484c403001050404408940264000640f50005008440aa800349400101c264540044c06005500301030b003294250b010305070a96480c00c0300d1007180b80c0718051120f1024080c4c10140005000c0790152401900c10018281c00d1001c1da071181011615100ea09054546503503030303511400c9006290345200d084280010010001e0f2065021107048160b900c4054500a03c1200181c0f12169210b082c0c80287c0043c5004010018007001c28100d02c41240064183d5500751004000a400d426200484603d0355220501d100720102c603501c000505c60320404240000c904044d4000b501c04041d03126014481c008409400c0308001c0705400403c2001009002480300521480500940d800070400c103101c035184c10102d91903071550004025049602c0945030318055110342c1c13204e4440c2c410141105d07800f48500e5500e000d41210800000c448400c0a01c003501c1f150b414404400c030b0055 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 194525710 1250 194524460 194524471
    0xd091404051303050a0c0c09021209030405030a031206050405010b0a020c040902060d20040603020901021009170708071a0a180512090d0b09070315020a0f120207020a08010e0105 78
    0x10300d001c040145030b407030140340b4142054040c00c1c625102c0403480c10071075138900880341c000c00468880a001400c0b5886402403d01c070038044407449110758988c1d289590b240514490954180e102804035408280241940c802c40d88070781001241d22070b01c80c00801c09a840a901141c0781d071000040c058442039052080c051031180858043c00440c1e86900026241e004540383c10315400d940b1003140000c2c0c509040c3e4041c84001d000100e64850f40d031608058000d4000031403660240c0100c07460703001c4007052440f4405400341d200005c84100c82c412048101e21350801d00080324003120802c0010041442402c040807021502c0c4030502c4240380941840060310301200c0308000220f00610080c0c0010707030100d80500c200314942e20142c1c0311072949002615041c445a0050701d0140d0b66400e1180c54039000c10104161703030051118a80e0002e030080717144101d11801070b8100c0010b1036049042c0010f0303c00d011075101035410381000740c1400e1494000130100c160952014102d695101100c68507040d082c0181503200 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 194526960 1250 194525710 194525719
    0x17010602030306130f0207020d0803040c081501090f0603081209191707051c0e0f0603010b03061201240e0105120d0e0303120c09011215031103010e0d0914 68
    0x42c200381d00407401200d84180130300040754640c80340c2d5466000f0380d8161a601034005184403001030303032030400f10b50660041c0c40c00d0f9540c8545243c0404c8840000070741003e08a20320a01e003441da031a0409043c02043c40d842c00005d01901c0d40400004141c07003d000d0a244030021002000605182c40e545141407a480c4170900d0202c1c0c503400a2307000c10310703102c43c1070441c0418494207070351800c00713142c800d0601a481d0b0580c072030f045500442a521a9010984441490007600d4401c5100102030030032590f8002440341c0c0242e00d204000098060900344225440f10340700c94004540e050104403038141000d00124091310140900c1c900700989101c800e8000d0040009682c0321000c8030114455a481c0c80407000702105000c120703d001c40709d688040048458050035841240c00f541007a00104405034030280750580000d40220450300701010728421111442d090100c00c0181510f540d5418800d994030840e01e0750f05540c2e818240310005c2c024000f03581049090755500300c0040c2003000f20040b411064880c00d019 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 194528210 1250 194526960 194526967
    0x30b0408130f050a0b070f060e030c060109020f0414130518190215162102010e060708130203030c030301060315120b0c0334090911070204110d0c1701060203 69
    0x503a101c0c0c4c4214001d4991602c2056070307034546030030420320790041c11100800040c5000c00001c128100030000e4521b4861503c15a0482e903030729101076040e400781d50f0b441486e050080008000710303a0f1482d03120540345400b410340c145040106010008540341181c903d458000005041c8003c80e00600c00c60010b030300384e4047d45550040c0d54021035803045086e0031242c001d0700c4c00030b140301c1e181400c04c0c2102400341d4800d100041c000b10000c4d8802c200d100e10300b6031002541c200320f00320515a0380825000c1c8603100300ea540d0710040d075a0198010030b1010001c4141d80600003000702d81210f4000f40020340c043e2076540c0780852501c0f282c1c02035280f04203c40e0320405081c1c4400e14540006400301c21050781040000c444d503078803a10b52103105c40c0700d802d4500b030000c0805c580c6058821020004a8100980c0c101502e801d00440d507140703601401e548542c440312408810420203130f0b005150950101c1d080355029002d2604040e40a034920084801c0d0742c1c4800b020030340c4e0008030605e05000515142c050049480a0343c01c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 194529460 1250 194528210 194528219
    0x61804081801020f0f0a060506040504021003020a03090c032d0809060d180516082b030204050a0e0108011d0303060103110c030417010b060a020a03080907030b0408130f 74
    0x40d401150304209168040c40d81c050540d80c0700b0001e0350403102018041d6840130001c441d5466650024100845a55080c0360018041c0d16280c40360600c00ea40203050062104040301d0224025480855401c040c95a80c1000e28003050003101810003640c460340c03403114040c0e640c5512007032100d0910581e1460b0800d010741d41d80018070000558074407050541e6590780f03410b034100d5000040c241c8100d80202c030300445060f25091020004640c02100380000e00120505c0d181c0d40b4103600c60070141c00a04030041c20a100d01900c298103440355031005e0080c0340040c01c0c40d4807040001d000741c02c140d11801106000800602041c1003e100300d62404490261008804003842261512070200616490515a940e13040240030b1402204540080100000b5650340b07e07160b8402041c000c9400f80034001540c6007030051150390800200b11030300802c0e990002c21400d6600d81d812590f80c6401094000d69000b042e20000000f4000c10556010340e124410054483c0610520001042c3d2107511a140c0d0b107107021800c11 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 194530710 1250 194529460 194529473
    0x90301140c0403380f01081b0603130b161206060f050901031b020a140a050a0b10081c0f18050d050111220b130b03072303061804 57
    0x508070fa5000c010704c880303103010382e00080d24214100349040050350008100008031010001c0729100b501103d124101c240d0700e401c00c2942d5aa0f216080b050481c00070044003280d442d02e000a50345c88822500c0282c01d441c4140d0343d02c11601c0c002c1ea21080714640c92040301d000650015041c000d040960601000554600200180340020303802035142442400103c50405910907002001c025032003c00400041c038055100950325101340406803014540070049503c5403101040e0742d09110f410600a18403a00c15403110900c80b07902074921145015a1040041e05440a0000c00750019520120280c0c08040305d10243c01d0040054505042002400112000c2d810344034010007507460a07134141000c0004c0e890f01c24010600820343c9a002e00f00422415000400c2d03400c030654102d8007651740c00c0d030789942e00541c00b00f03402084d0f4040900ca0181500f0700c60040d111001d1a4058001d2a0005030340c000f0807032404002140380401e01d05221300000304021400e1404243c1031303d00410850b41740614090300ca40 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 194531960 1250 194530710 194530717
    0x303120207150209011107240311030105060c030c240105060703120e2404062307050901091e0f05030f0303040f1b0602010608060c160201030c140708090301140c 71
    0xe04070b480d0b003c030b007216842e40303d000c0001500181c2001c40d90311a85480a8040f03001c4404140c0e020038031403410110440b8480d00400410b4080454400e0550f403e2204102694003c2030a0707840900c0305020014814100700700c240d00040001c242541c0601c03c441400c40036131016002035006940400445002a90041000540b1340803880009900c8410141c101e0802c0801c4a0204208030400804019184c4050030f150160f481030304100400c62003800000e03080d47c0c08194941500d444100000ca503c0d0185000380310040d01494107583c84c0c3e469061a10100a140d90304038040c41008400303100c0440032074105806088120000d00010109220281c0c0c0c030700c4000c10042c0f01f40091030301e0030704000c02004220000c0ca2040d003062074254a60900900810b0540b03d040183e01c68540071441c0065200219030003c40c22114515861a054005402510b10280349004200f83d498030030764440564406040355a00c2415901e685d958680c00301400e60303000001005001c0d001c9418050001050307000c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 194533210 1250 194531960 194531993
    0x506040204050705160c15030501030c0e0402031005010909020a060318020609030304170f10060308030403080405160603020a23090d08070f0b01060216060207180902060a08010303120207 82
    0x4506030783c0d80d0404507141d02400c0468a0040b03000d68009041048075442c80c8151a40302420358098400b0210450039190284000352490000350001d000004000000c554024000f800702c601030928513003c0e204484090b88004507047d07642e604001140350018006008100302d02c1c0502524000039003012028003459402840f072030001460f6200ca03101130060700e0041046541404032046000c4110340c98103000b04031080107002c3e000840c0b03115011440703100c066a8105e040b040c2036540f50b907000d50750648041c100f0b076460b125041450201d04c6648441501030303c1550780168581c02000c1c005820124a103110000e4540c00c0900340d00c4032440101a86c2340803030100c0e0b05c20708180c81410411054400e00c83c01410166900045209016050a1940c1280e403641c0c02c4602d00510142c07400c43c2da650034080c02006810182007040b00e0000d08c12045508440c100000820501c039600003050303688041050310209055000405c21b01d41c116206400c4211030610551170100c480da1440d0711521240c86 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 194534460 1250 194533210 194533219
    0x30904020a1101051f0b07031e0509030f0313080619111204031d0906010c140c1309140a03020d05070c030f05151506070209060619050a020c0d05060402 67
    0x1c0814086108494021901403554000c0041e428a1081c0c056405200b816404640b0440e190000b20001c0540031070300415056aa0750303480103861507081400740764408448041050920060845907000c0c40001c880c00703ca14010740d6190302e01524140b1800c0107502034005600103004002e0b039078503024000e1255030100400040c0c00000c01c882007004e800f41000032040d58001d10b00308030415030007943c00c956a810500050130494070100400090741e01c12030340300d40001c0406005000103000346132040080d1080b4401d885d0b1614030300c07000c00c8603074440042030910b541d00c03400302e0003d001d250400203c5881c41000605007082003628083d549008075250310b4208a400282d00b814031100c1e1190f01c020b1035120b00041c105081d81d050450391002c1c0703030151140c0200c0200c0400c035a0b29000c20300c5a44218003401c0d1a00f02030f169002c100e404540108640e80007030041000352039916607602c01e50120003142c0c403455201c84490000074501648040a140034203680090a00030900008010340e02c140d0456 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 194535710 1250 194534460 194534467
    0x30a1409071e080c09041712010501021903022d12070b0106021612030909020f0705060121020d05010f09030804060507020303040f060f06090f09030327080313020901120203190503090402 82
    0x29119110070b8100d810300c21f01d074a001c40c12004000c107030300800341284c2003642241da4451007040031050822906000802603030007115030820721002617400b81c402c17a80e0100c8440c01d5000d07910b91941800d500b00c1403c552000d0010364041040120a001800f6217442e02c0200203030b14030b40324002c203030710713880d000314010103000d140f03400c040522500c03085020b81b0500c501551a40c10b00001490650000d880842d500d0254000208034400f400c86960b141d024a8001801303d00c4a5801340705542c1014101906c00d95201c51a42601d1580c50184a02d0248680c0e641c5249281908000084860180040085400810070305c00403a0350f107664004040d0f002880003600f00c0e4520f6500d00180410780c801d40440d824261038a030612078a03444a44154000d46041c40b65103000c48400c0300a00c4101b082e0700714a11030003201d40c040f0300500059030748544055030b2400f41c0b40041d000120844402d82c8160f0980707100030049001c41c02c0c2404505041c1c0030301d100c203501c0322020380e481644a0103842d940c0344c01980d001c03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 194536960 1250 194535710 194535713
    0xf06090a0b0406030c05100e030709020a02070305190b07020607020a020405090109020a030501061508060d030e06040e0f0a0f020928090e06150a0b040506030a1409071e080c0904 78
    0xa0303100c1044404024010080155a81340002c0d1115943c82850302c80c1e0504400941510300508c444039803030400074050640f40c3d09254a4030020b401c8650104114403c200002c000200d041108114940d101d084052a100c218907000d0200000100020110741092050100c0e00f40c000500c2503030300d6030458001c142da6507102c071720300c0c0101511a0060741c44480036000206115040d8000e2060f030300340c3d08002c2c0303130006c45141c255266002070b6510340d0844509030301c1c600481d01c100f0010f001d054004004074a019500c90780e9485072141078644280c0629144148603c07012940303d4641c492480003010742c1085000d40000c0c0000c5d0000d2544082c0203444100e20400c0d00000604001070010b00300104940440c43d510241d5542040701c3d5480c02094001400b415071424009000407601d2048144c1d02d8076080400341f04031504007401504040d510b800e1095055484444468440c5208400500380320b40f4203030300c2241d1205ca40d8801200000454000c1c0a00076000c200b944024000f0303501d02030a40c455 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 194538210 1250 194536960 194536981
    0xc081f05040f080a0f0809010b0609090a0e0d0908070e040206070209041106211f2d12020301050a11040605070f081b0d030c080610020703060f06030611030f0609 71
    0x1030b0200204040c1e40092076501a6400a80c0d0319480c64a1340d03101400e80d542c5410084c05c0703a07014841c6690100050290307080c0751030294000e0303600c00c4065101007006090610f80a141ca408080e1100100e46d11510500c1000030070032401000342154040c11404c3e062503000300d401846200c0005c1d008901d600c0003d418000e281c0b450070505407010340160b40d00c4001c46a000301400240180e5042010720350045003e0650309507151100c0c61000ea400d211039890040007018500801c030702042c60085410a0b801c64511100030440100310b121060780c0d15910920416013140c400621107260340742780604500040c120642a501902e4517420310701d0759503829003808564480e01000003000c445e0700090f210005840b031180a2a000004011180000103a140c240c080d1207a5040100000703580c1800152207140400e00075040d0100d40c010f55203125181e442d000f05581c020030b4100107c50300d6420800403c4002d00c00d0301c4072105489066400d6090441e0b90754124400641703180e204200071300101d03654101 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 194539460 1250 194538210 194538233
    0x909010b0d0b10091a030903032202060a08090f0703030e0d080d18170c03091507050d2703050303070f1202030a05010e06042307020709050901090c081f0504 69
    0x10040415810b10700e00c00b0010204e0600d8050502500612000c2c240e0044180040c4c0c0c0c01580e019010310b080d5136900341c03070104030720702501c401c1084880d501c1c0d00d10160300c500c002000c90640c0d40d030740e16241c0d192180025151103201c001501860340040c0040012a510200c214040c080c00c640c610044521402c0003009400b40c81c0154600c20b2508034001000340c881030007203000c01e2080d0024020b4410034401d40350540584840d082c05074008100c484940d11301b030008102c040c00c546407958182500c5d601c07440d181020b02c201100205085550315045089030b02a01501c04a040100c01040c03400d69440d00e031030340005440c000c2071102405290b41c4160040b100900c4d80b180a0a04644a1a00c121320742c002d0700c005e204e1245000110303000301d81c541c20b1a005000801001084034002110b850403440d04c2d862008207140114098400041281e403054041c6a004d074143d00c0c00403400d410a410b015589111303580c0500140d03030068a00c1c1d4464115410903211040f03140c030000900d6525410540250300 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 194540710 1250 194539460 194539481
    0x71511010e0d02190804050904020d0b070f08062205130f0c050f04060506030423031803100507080f0702070308071514150f030c0406060807140909010b0d 68
    0x1400c00e5a6455040c00008600c0b1000c41e0640c02c480b40300a0368049125244103004000e0301c09841000706002c0c07400c0c4200700c941c0140c07000d402484200803a0300d82078490007056a000b80082d0341c0e400400c1559520441c0c1541101c0e08680070300684400e40b10750380e0311402210091079000c0d110000209600c441c8500a101c075504460031010346070040c40c142c00d20400d04c0c0140c41c0302e5000014080d149052030320032030301a103d0140c152840c5450315100c003d030902d030000300840c140c11104030001c0421814400b90100380811800300101289034020142011070a0f4a10650b10745400104590f05a1020b6200e030091801103003046140c9813408102d0070240f80381c10103041600000307400c3c3e0811017950001c0d180c101c188a410013100c2d040c0500c3c0c1180175001c1c1c0e00c0d0501d800400030003008502d4041500c00f030300280201103440580d07955002c030b0280c07042c580c004e8020951307507010000c0d07080d040321380c496907102d40640c41ca14184000300001c03100c10040c0502c1c400a9404202c00480355000e030311896805 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 194541960 1250 194540710 194540713
    0x40f020306040f060606030b0a060e030c062a060402091303110d05030105030c030a02060f091207080102040501020d080105030607080a090c18060e1b0c16181d071511 73
    0x240b82508010500c0501031000b102c0c0513240a43c00280c0070301c244a0040240001401c545a90340307442c204441c07100301da5013041d03810b0060301400c62240e81d6a00080040c0d0005030380c004111a0035100054000310700040e410480d0b0002d50030000103a84442d09940e008000071400400f035155401c088a20454002c1d40004038450380d0556103407190807070041c60498208500b100c220710600d0042c1500d40b003c482c4000c2d0485400d001c000c032502c1c1d540b009406082070141001c02c1d00f5840303c140e249810b03019889102103950020b01030100b540e0500c101105103070b03941040c6409515202c0400e41d1014001c11140c100994240420011643da40102440c030380c002c0d441c02446526004810f01c29040740045040151400c0400542e00340714410b81441001002e1610600c41d000a1003080079500500e40111540502d501000411076152101d40151084c50800740384800c006040000705d0301c5820b54070700d400a00301c0401d42600b500040f218140ea0851030300707002d0000354180c2500c42c0c0305942c2d01350006 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 194543210 1250 194541960 194541973
    0x607080c0703052512050a06110d02120720031c0f0e06090712050309041802060d02070b130b0a0b0307051005030f2518181401050303040518040f0203 66
    0x15842680d004108450100a04c0a203940f680d02c5110705c404440001c0283d08905440030100d0071580c4a40000380c42e140c440c618103551003507020200e0b40800202c1241c98040301c140110750740d00c03406007444051500c904400e00c51603001c49a50303e00440440500f001d4000c81c0760901d400264102c1c0c5801400503005006109100c2e03a4035071285070131121000c96101e41b500000e020151802680c00c021740103000f035403914400800b0300014005030ba400012035086420030b000180c41c0c000007000d410f01000001a140c0d4105e2405d850406006807020600e1074500d9924004100039540300e94006500d41c0000800710261004242003103440d0348443c3d4041c000c10200040c840d0024000c603c190028420b46240740d9808034181e001e1130800510385a8201c0300d0105030080c5024091400d01c0441101d440c0800035541c50174050395401c07010980c040241c07544030368a2500307074821500e40581011006542401d0900e0003040d40c0500154107000b01450400204007800407084143d407001d0780180c01c2e61003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 194544460 1250 194543210 194543233
    0x302030f0c2b0903031b0203060108070821040612290102011d0a022e0e0f0d0201050d0209040902100e090f04050c0622031104060b090607080c070305 66
    0x8450070140700104280b010b0480703090b00c0c000e406210201003480c0b62554240ba50540d101141c0489480d240c03481c4c1c1c2c8490000d1040540da08006d614001c3c4007200007800c010703051008450405280340b0344244034140511030f28504080c1d11060303d043e079000340341c802702000d020a03001016007000c0c400c01480085a00c1320382c517041d0803460002d994040c01c4c1c000f40120038100c500a01c02c000600c030b0100107508403640801c01854500c8401c09240748c121341c4609103182c0b40744507004950201a80b40d0104080655001c5e10303051101c00001c400c401105d010700c0907103035500003070a640f080c40c0030201059400142150199100c1d8418601c080d00174020380e03280c0300c247c000600700c501c9076000144110130950000d022103081000705032082c1d40c0302000d02034a00170030083c4031664010440141078407424000248584508000c001c0095009000c9064190942c009000c1280c1098000d214500820040f500c411788849007180c0201d6030240d521950340103641003035800c1540c00d07007001b0054040e9007010030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 194545710 1250 194544460 194544463
    0x6031a0d060501091508070e0c0f0406090f08060f0c1b03040f1409070f0e01120903180911070807030302040b0d0f050708090d030b010212070b0108010f020304030512040302030f0c 79
    0x1d041e1028203000304001e250701c85d015003003015640f0581c082c6520080f01800010340200c00b05030000513914244d41000e010200b1840290410b8202c0000590080c0007040002070b000e60800040502e0805081d07a405c1c441c58074082624020412025502d00059112140c1d925841e01d00e6200304890560b600c0e65103400c1941c0c0d44e5443c510565588a6120f20085564501540701c54054006a100d04050054800c0300741d0300d0361007002c030050500080c1002041819100d00070501094807907038601e505100ca019110151001c6900315107580c40c41c0149240b143c000d544110f48840da0441409503d0b000071b460100d01a20070b40c0c01103101aa008103040304110754503007000e51400d242e00001d00c03a80e9520303a002c132a114000c83e04003410b948050b08500300e0600a41c0302c10404401803060345d02014680da00b61800d82d120350400c80320380b10f82d58010044088280f050040105140303905601d1814161401880b0b401130008031500010740b900880d003014000c00c12105049007042034641c03036030190304805 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 194546960 1250 194545710 194545721
    0x70818061c0f1a0108010612091e060f0b031f02044209091505030105160816200102090a1401080f060603010b070507031506061d03030406031a0d06 65
    0x485a00d0411403801031070102c4843c020440344044e910308400d80c0c80c0820859042c2081f01e50025015590b14410002c01d40000c2207002e140d0302c80c40c0402e00c01c81a0b1401604845c0000403802d000c5181c0392500072281c0d00440c3c02075140803420000d007818a11003103003038020711959001c0c000c9061466084403015200310705c4500250444407002141c20319840c6052083c0e80c0074180403002442101003481511000da10000141500341100c0511540b100c01083c2190001c0d00e1140b00c020f5008000051154420209903000050314444401d04040440c0079145007558240054240c2009800c42c5214100354140d17080c0e03020090070100031541c0c80342400103030b4444945090000b0300c100300069801c900200c00c3c82c010304001e481e261540c0c1c605020f003c0b05030000f0a04896600913501e00002044500e101a001c0c1c500c40c100000e1020310340b12001c0c6c01991420b03d201640c140000121005035004810780d011140e0605001c546248103024903a94031114080d5203502189400400d001d00210703600a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 194548210 1250 194546960 194546981
    0x10f020301030f032d050304030c02041526030301030f0510111b031303150f0603060f05090d0e01050d060b0d0e0d180b0a02160305061b070818061c 65
    0x1740042d0107100d0101c0901403c4000e000c10944000000c1d51384002d200750021507025000c0c2c40d0502414180b54002400e44101d0700002c0000440c00c00280500031071280c0c202006071003121121015030500980d142c8a0205100103000c03202e510242000b844028882d5401c80c02e02040100001500c0c00f05c0301078182c001c041c54040008110034542035915001040f1104501d4025640f003e981c070f50303039a40282700e201701a5514441d81315513940e080d034842c1c6d000b4207002e548181c40100c0c901020f00310503821a035005022000980c45120030000e070300d401c0f001c120300d185002c0c80d261741d03286000c09200000c1e040641c0034403004440020b843d803076111198040350741507010800382d4071500d540d100221442c019012903880d0607001e84400b0008001c0c604000c00030b40780d0318010b42d10105c41001c04585c8100c9507910a54054203c2c1c020000400d00140040d4210702d2680086800c0c51a1603c5820076030140d159541e1494a1429844286941e52415540041d241583c0c9040c0000300c1100c2c1805010100036 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 194549460 1250 194548210 194548217
    0x50604080a03260412030608030a030203090c010206040f0f11090405030d0506040e070e2203090807050103020703141b0105070309110d051f20030f0609100512010f020301030f03 78
    0xd4400f495040d502070804850811020000c585403a11801e40b54a107003580003040c15910710000607099401e0002d0144200c50f901c0041c2c0f240741c01c05c2c0c40c0e0308024015001034115000340c1c040000003104854030562841c0c10039030403419603807981f07400300f483c054560000d58400d0085c02080100304001009011079041c400e0140302a4650000340001c1c1ca640d03100c0308681d0f400030310382404001c4c010f50343c080e80b0080c8101c110510b40c0b40034060900000100b00b0a8001035003001007405450380030000704c4010242842e0440c0f4107416902d0003005030740684040414108009102c986064040319803003032480c02d900081042e400c001002500a01d00444225030002017000d80c032680e4a494a00e0440694110300641102d48600c1210643c0c042140100e03400c050359202821940f552030681d00320600c580c01c0301682d50f401e080c1d41c021820400100302c14841c421440411031a55070301e0f0302c41e0341161801d807500b031412b40308c0316005805450a481c5d00000b40f44080000000d00400344015041c042c06a207 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 194550710 1250 194549460 194549477
    0x50313030213050105061b0102040e040c06080114030316031e051e0715021b060705071e020a05061e0304081207020303090a0f080d050a0c08070e03061609050604080a03 74
    0x191540143c50b024807031035a01090038448201103c840316030520889124100041c5040d4541c0d440d04504401a101030302c070b0080c840f000b8008142c00c1001c1d180276203526410007100e032691a00180c0d591064041072100c900001040030304040c002e00e840300c0605102d5441040e170b4000c952005100d5009150800c03071108503c1060440310060302c04548095030401c0c600244403041340880c40280d8081242242c1c00c450400148140c01414002c95000d01c4655451a58410260400f8200d50b01c40c03210f0403269001c800b0b85400103035100e50381c2c40c048031800d540d00b940f500031105503411000189aa907014005000003003008010201004018101403400725100b00c0e11002c0040343d681c0802c580400b025403010f4004030103d03001d5140c0d4041c8030b10490244c5d160082402c0c2040c143c440644904182a403078015261040c0d030042107040e80f2201c10314140c650400c4400001c1d0381c440014120660720076a240d42c9a14003445100c038000548806000995920b0390391200030340d075505003c0147c0000751500c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 194551960 1250 194550710 194550739
    0x50a0e071514030615030f09061005240f040303020c0a060306030b22020d030c03020c030303090d0e03070302060a0c17090a06030e150106020a021804030207120305070503130302 78
    0x9800c0c8140200d0307070342e949552080012164070316039840035214981c030281c11501400100351540c000d511404d54285511220704060071054901000a00080d0003c0b6040100380031036120340700c02c1d04243c403201d958010315585803600e40d9800d20514045001c4c0c90000500441030580004106110580a442c14240300b40d442070110212181c5001c028010035020740803403010803402140d5001d11a0094500003082819800121070100140c022000f04039084010b40a06405114a0844000c29000b0350b1451401c504180e440b20340000f5140c040c049400d41c02c3c107030f6480c1000f540b0013865028014076961140312501406011030001d00716a440030aa00385905071512030269084154090040c4041504006080d800b81001214291083c8140410050a100c005a009009018540240c802000180144402c0c00d44001801d03440c3c090041c1404000fa600050500c22140510070607440d6111a15044503c1d114002000c4c005102c00705107500200040c0ca2484200ca10840300900b03200b408 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 194553210 1250 194551960 194551979
    0x302180c0313030e041805010c03050c03061201110a090e0109060308040e06010210050a0617120304030305060d0b070f1e1e030608010504060605030d02191113050a0e07 74
    0x12969600018024404291815440854900c0360352003400e199001c0010705000c201211b201c2010340d03c42d400c2101440042c060b00b07109102d400302e03840c0380a10071490202c01e81d917000e110103407a180c001c10403d174a0307001102080d84010b0609200100741c0303585074140c0310010a1b411803402100880042200005854003041c8a05000c4076804010941010700d8500d08140c507507001040f4034154060003481038451529441003d104a854500010704a4106100e5010400c1c0d8401c00d0040ca40c000600030384495401000d403030f4080c0e4546000b184681e61940424000140058002c00c170b03a00d001c060014107600520000020412075482d0044076a11151303400109109500800200d80b4410080c1102c020b00600050300524904000c9146036031407041500316801103405890701350383d5260602207072074244500414003030548010884a024040918a1051180030007400d0001101012055854054501d907080300c0d030007400c10443c42c005d2050b0011f01000308900102c0d001d400d1021860090 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 194554460 1250 194553210 194553259
    0x30f0d052203020c040f06080f0f1614090a09020303071208070f0f120608190c0509010b040e071806030504030e0102030f0406110a05030426060408030c0711030708070302 75
    0xc25500429a01421130180401440017416144020742c4481010a0035017040280c100150b0300500240141460780c41200d00789140c51031540b002d004107140400285040040790680383c00221000700d601d80b142141c0400030004c411000790180000b054003400e001e08041c09000701411030301d0710251075650890407500b081c0f903070003450082955010062042071007403036121110b540c0610001166a03c503c201407074090061820500c800c180c160700003c00c8500400c200050100795901c00f0309504000c01c0403c0744c0202d00072242d51010010026442510134268500454000c5140c02e9855031910070042c0a400704407130603404100c00c0901c0007042d5100001302e41100130342603101030505003041000c030350780c81441320b80f024244101041800800d000b03200400c014104241d002c0340850131002c0d183c035421070300b81c0d11114a0b08000d08000114950004890f4858265503005913282110f1070000344405d84030410640601c2480741c00700d9a00800200e050031f032402107418084404090410300034842 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 194555710 1250 194554460 194554463
    0x13060203040302150705010e1e010e0f0a1203270302010b031f09020a090e060108070b040b07060b060c0a03050d0e0c100806150c010507120207170c030f0d0522 70
    0x40b4044000304c8418180b00c003401040b4441c0b400420095064506503142010000014000c15028602420190300c2403003034003000750904014100c0038144088a544a030b80854010344a81445020a00c2440c0310360302c2940740c0d002804e400c80d5011347c5d1261f044980300440340f0481c0550f00e08410703010b0601e0700044180120031060380c44075694034841072100181c8600310b822600a541d08002044a586e82e00544101c17641000c020142d5625180710a841d20f03409510000d6081c100300014401c040c8114201c5000700e0b0009000f003071070304107880862254841da4007440c10702d0080303200110416034044000c001100c0c80b1a0240482c06070000e520740c40781751010245078855801d00001d220140a110681d40c4403000420f5148a03084c01c01280400741e0140c0c07042c00d50340c0d54400803c8120754221002e40d5602c124120304504100090365503034035074a505080030ba00c400000c16a02d40341c420400403540139000e20720243c0c1c0c851012001d05000303450103850700b001000010110081d6a0900244bc2c202d00d03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 194556960 1250 194555710 194555719
    0x70809010822020f0303070501050c0706060b03040f080a140a020703051612171605010c2318031c03090c09050609010303050702030703120e01080f0603030d15030c060513060203040302 81
    0x40b080c0e82c20080c0070380c2c41c1444150540000d200c103a0104a082c443c06108500c2d1459040d9518964580307034080f80c0c03d40d0041c50300f80b1414801c0c000404c603a03c00c100c498645c0188550707075868110b00107440c08440d20143c00812a40080e5110700558041512800c0700e1190045901641040d40c6118590855009201c401401200c0e40404203020040f90700203a801030b9140d03413500c00050f9101056480c00d410644080c0c0d100c500207500a50720110362400c11b590070048000d0104103d00706182e0b03210300214144988000c4c44900071f607079000c1c060394040007115909440003444a14000c1c010b80b212010590700c924070035000082c1030950380107141c49020000c00c0c8040603800c0d40d03000d80351030308a10400e030b8140c03140090100008440b40d060f204903040f035071030314050b05015000041c82e5003c003c12203007000c100746062003c01d8070b0000564101000d02c20300420900c1340c0030342c84209181c059001506694183c00c0010303d1940010017000c0312101c1c065003206131512550b09994900c0340e844000e410 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 194558210 1250 194556960 194557021
    0x1d060604060e0927030703020d180302091503030a02010605150c030306011b06060e0f1e01060c03020f120705121204060b1206090309011b02100807090b0708090108 72
    0x12403804541c0d15a00c0000780c818042000d004d40d00c0036042001652008040f544000780306001d05404001c511140d811038608840004441c0410040c06049440024090b0754550041442070a0711003d18480001c060b040302c1d02d4024428009000c0d21191103803a0003031001e502c80940001c10742c402c031801d110041002310302d580c84160044401e080700c0040c00d41d60310307000c2d0010800684e15004a030003c101038412903c40d03041030681d003824842c02805100b02e5240c0180112101102048581d044841904000c5041d00c1103050070b07030a248504d50b01d100e2600401e01241100b0191201400110303010340c003200c841c484070716a886014030400840ca440c80280f5000a0006183c0785c000340300549001c0c298490440150380c10358a4a4415540702e4050340002c0b40ca61b200e540c1c04280c1e10b0103107980c0400b45460700640d8001c940c0031003c0d81c02482c2044000000100302c60700840c0400010000f10310b200303640d0030417810b10082a800c480c2074a40082e8040010454140420103007107013104084110140307 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 194559460 1250 194558210 194558237
    0x30d0905011106060a1e0312030b0f1c24050906070908030a14090f0603040c05010809030a05030c0901110f03030624030a0b12070b0c0f01020705060708040606030c1d06060406 77
    0x100548440503000c107501c6c1810000c800520684640300781c5181c1614003050048a5504024612a6000c0c002c0d0141203200342a00a005850f42c0f90103405404c0240c0070006d02c0207552445190300f0155040d41e41905010a0102c0c0444c0010110720a0310180e8452001e1610303104800e40728401d0001c0c68002030201d81c143c140c0300008500602d40118000e004e2551102c3ca900451450f800031103058401c242c0165080106581203030260342c2c40a800c17005985420300101015120307000107818803041034000b0801c50801d9025004961005a03518101c8140081c1000c085940b94811a80680141d0100081e401e10034882c004c505001554422064110303076500820a0041044490311a40036a21420f0803401100c02c2c0724007000f500c0000841e543d9510840c405d14078012000755a440c41c0d80c41040030303602007039000c242d2a030400d100d89450103035070b141c608000d0b002c0d040c40c0d00043d00c0c6906011001641c103001c40325031090001c0460401c8d5140d81c84204202080c02540301c0c03240402c2c124030b43c060 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 194560710 1250 194559460 194559479
    0x604050a180e0f280b07020c0102010c11190606030203070b03070f020604210201091b03030201060b0f040320040f021210080d0c080408030703020c030708010b0619030b030d0905011106060a 83
    0x8007124403c2c00c84801c4e07040782c0b500c0710084400c0c1d81d1035000d600301c003101f01c14550b428000c0d403c80b810541805d92045c0e407400a11541c1d0030f0f2612000c480d401d0480480c0080006035000f40c0001e40d0002e040701c041c1900d410220155500035a142d502081d034480c5ca00810600210300780d4170131038001d082d041e02d62036082c0145808201d5000040215540c03124a080051641e0505050307050b420388900e4074a90541c40d01a007110003e802240103002c05200c40c00c05035a804007100c0070390b5030040b030a013403441c680d03c0e4a126440740c401000740e205040c001020b201c141c05038003800302500003c9401d20a5100c3c800080c0d81c105c2c071030164810642104015582e80c0b030048441079402445869914546170741c4803031560542e0800d080850058120703a15580c284c7c641044003201a042030b0000300018081700b00003e0140c401e6001155002400300e04000500d07009600903040c410001e402d460760400d00300c500401050345400785c18089110960350640f42580040c040c1e07c075882c0600405038403400c102101 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 194561960 1250 194560710 194560753
    0xb0f0a05010312051812010c110102070506070e1c060203040c050f280f0b0405150c1b04110a32030c03060d02060d0e0114240604050a180e0f 62
    0x989800c17076512941c41c19460b0044c015245021010000845881c180c0008088171000c00205e0350b268014407010003c02c1c070201d051a001410f508002d00e0451050010a08000420030060000c07070149010405002070340d0011446a0b1150104c40e41381900d0f4406c024100240c181000c1c0c220801c14031a28042c094540c0c120304816415841806c0c060350b5000500601c000c54000f01000e080105040045060030384290105509800c4418241202d140041d07580d96030f00448000001c20f4150800540e868a038440c1400d81b880074150f0340e492200e08000b07405040e483d40007100f6160318000341c0e140b003001c10741c51303080340018480d10520f907454802405405410141000b54800300a444460050382c60000600071030542c1c44001c144002c84030306c100d08442802c80031440340c41085041114043c0e041c0d0511411800d11005419411002d41c0412030500035074101c0b5400c81950040468a84c0303031040000211140c024050000081c102e5045444540c1070340e41408030b502081c002d44036103403d01c044 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 194563210 1250 194561960 194561977
    0x615020a06050c1c09060e0a05060c091302040e06131107020d0804080304120b07080f06010809010b151b0706050415022a0102060702150a0c020f0a0b0f0a0501031205 73
    0x78507041042c5104030004050740201e02000d960340c5d841c151020010b26003d42a84118254086c1c0720415081e180e964035840c00a150381491280040d580107503984688043c41c0d00c10049200319121901c9201046011805465151081c020a1080c0c1c00100d05801450750032140e0018007400d01d0301583c00c0c0826034404200c1101c900030f0030312000c81e030721004002510041c100d10446002182c400d062001107460094411403c0040140c10040094003111001c0e40224082c60a410305a54810082d4010042c1d8070f8041c2d44854109036200c05031005401038080c403292008109041912000707201d42e104920300c111004035206020030002c1030054500c0c4509640341e070050b504511a2209003482007048a804003403520300004071807115590400020764401e4113030000b440c03e204d2076410486469001440c03aa10386407107540545006109015000b180c0c1682011100b45eaa00c529100321083e00481c4c13450b10260100f00014841e01c21801050b04881d00003100445140880c54126030a6015011 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 194564460 1250 194563210 194563231
    0x150f0702040204030f060c090e04030203040b0c030d1b0201060801020301140d020a030506040c090c0e150901090f080d030506011404051c0213050106090b18040e0f03030a0b01030615020a0605 84
    0x8160107404a540305c511490740000d42c020352440150840d086500f2480c0c00c06c044108200000e50000126000d8600202200f034481558040661842c420174085107142d80c188001d41009041c181c0b6000603c00d2550020300c842505da800041c201d00003403080114021601410306283d040500d0f080b074000b8006840d40074540e489450302031814030181c8048601c583c00780760070000c065080c822070b04040074a160900584080c94001051f0081008070540c41a2001910101980c007401c1003e000f05100c1c42c6003c04e2554074007103140c03030307503c5900f80c5000b003802d1000089a9610407440c001d540c0701c4100e400340c1403504240510415540c003000120b00c070003d010075400960350b4a42c0b2252289410000030503150b0400f900102000100d43c00304d603001030240420f1182180613003d003007000d6015070b80002d0515102200c1c5286c481d0340f605201d11800000b007032221101080d00a2420028280c80070305c1100e60700d180090701e001a0114602c01a000906991300003032054200d00e410003000782 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 194565710 1250 194564460 194564467
    0x3010c1d01021507020a120903080a032a03020304060605031504080c101b0207050a05010e0603090322030501050708070c14102409020705151e13050c150f07020402 72
    0xe41090780001c01303894040240e800b680b200710410a01e04040b08000e180380ca048002245195a00b0280e4003802440b0401d0640303030822003071001061808400070a000310b0b000c0c080d4a5000741e01600951055400b07540c502d06003a008030703490030001007480b40d000300210707288410b56070354035100b0303079608140c0b072505050161502c15401d410362401202c0c0040c6000e01800005001210040e1070000b80303600c03030740c06101c0d0700c41c04100750703138019080d09003a0b88145c549580d00e1b41d880220b18203621506901103118a000802c4103980301070039014500f603d02c070f44001c001c01d8603280d0064682d000e0803a8031000041c01000c4e003200151001048140554071102100c902c50712040060055503110000034841c2070074a03030b00300e2007542c1e4080f0500003003107540421840d0203040d0310b55603210705a031400f070146410b900d000300b84043c1c0801c2c120b00c03c5441c2071408107201d00b00500454100f4624900036203041c402c0c42034031081c034036002da03003034541b0080d10003501c0c9000400051901150459402070340d000340e091 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 194566960 1250 194565710 194565733
    0x1110c030105160305150114091215010f080a020618180c22140108040507090509010203071707080a0507230c061b03010302040203040606181a03010c1d0102 69
    0x2d00803a40149541d10314803090011400004007243d00050041c1204044170179280d040766000790000442c06400170000360366102d0000402d107200b900d04959851031044044600c0250841030003581070b204c071204450012607503440015612000108043e6000d01c04008101c820308042400c0302402c14068a81074030003440794602038001d00221907800c80c00f070300003500c0403854410384241000160b00c09104452030381040032a80e526010240228148400880801c061140400a1000412201d401804207180044405010307400940380980465500744600385450f50740701e06d80d842a92079030b07602c084c103580300c14504014050103010001400000c038070440c9000c08d11b0809510a080e000101c5641c0c940507a04145010784c018a0907003c0c1098140ca44c0c40d484104080300e04407901241c0150b00c0e5222414040000d1050364044048008980c1e08401062140c0d04100507240e491003504a41c4c5071940141401d991480340794600080d4041c204000a405240250a0000040c4119441c1007a80c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 194568210 1250 194566960 194566963
    0x801050910051018060906080f0a1b02030a03060f181d0109030504030506010b0f181507110a0f050a03170705012d06030309060305090a0204020a0309060b0d020604030201110c03 78
    0x40d030f1800d100003070300082a600355a610740e506070000c0150340780c4111020714100300281031010161502c00e08085000104200040980200c5840c980c40c01e582c03066440c0a1601a590794492869040442c0c1090030020f00f1200c4214a1012200d91140203607a9005901100004041c65080780345540c66680c507030461410240b08201119100e0344910390b44500f5402d1980c5040070507803003001d207082e007040502c540340644810340b024101041d1240910003c0000010300354140390310088440d0704049081f005206910800c200c00701002d503616200c0c60b4803804e02d00c2140d800350041642001d000c910410002d4080300c901c03510b0b10340b01ea074501d003003104541c0c80c14252484407004210000100c2c010500c1110240031540c0341c0c5046540030842c075031640c4d40140a65080b1710036807091507651300004103081c0e8180021041d05034002c0046540c5d0f03030900400b40040c10400c205880d45031812840481034102801603402060f0024000c0b41001d26643c01110028000c1402c0002e50041140300380880d00c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 194569460 1250 194568210 194568229
    0x309080d0315080304140618090709140108060105091c020d1a09010c080609070512070503090709060b040308030709030501090b0114010305061503090102040f08030a0f020d080105091005 82
    0x19641c000c41d1104a075200300c115801c0395040b40d40705800030130080142003010394000d0710714541601c41640340c86003241c18a044c0c640400030141c20600300c20400161903070201c0124283c50070042500202041030004440350fa0303013101e106004c04d8040081000b071340b402107040074412111049017031660940e940801c00d2030003040030441d840000c0e095038000c0b00f041d40c981103500808507002082001e0b11039400170486180035003854041e0b0f4444004c070788810720401c11500841031464542480341000b0340000c160354000c0f900e540d20b03802140000f08903c0c20300e00991040b10070501105081c1402e42c0c5070007045a0000d4051024048004070003c00180280241030b809802451501211361412601024400e091143e1034101880d010030001c9a13902d21055144519000b1f07600c544960750440100c0c020300c260b8200d000d10b41002200000c10450000003046607403041d80c2c800c4c0989104140a03666184c030307004800080303808000140624203058005c02d500040c102001800b45546c0c401042c00083e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 194570710 1250 194569460 194569483
    0x16140f012f070609080a15020306010314042001090e0a050612150403090608040f120212070605160302040f1a0904022706090a06080a0b030d200304050108040f030908 73
    0x4010342c00c10410070740c0084c504002081400d0103024045903503900c8034116200007403180f02c4507601001080f4143d00c01e50001c020710f10312400041d81410107080c15028900c03070010020f1001022410000e040d4401c0c40d8035001c9a1182030841e5003510b840e810780e07000d060b0080080b034002503210010030070740c0b00400c950081c50000301c08405031800e00b81002010403902e074010000740441078007408001103840007210310703240d0443c013200c0401404140c02c900300f0055414480c5916008141c140c10f011241d409503014108880454003445400e40c025002d0740240c0c032500442503094501040035071511001040100a448111498900c600001504a0700000310f10841d40d0346030a244e0701c49074545005d4000110f4120380b0316090982c50400540c808107680212030800546101248140100703801c5600c11a43c01001c0e00d14510755200c00030050b80b10148540008181880195101a0040704032400d690069540128555954460307040f0540c220034120b00300041e00c0d500151011701407100c1c29185 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 194571960 1250 194570710 194570713
    0x40912080a0501060f050a0c02030a080c030903011802010801120305090a03080301080d110613080706020f07020102061003170c101b030b06180409020303040906060216140f012f 78
    0x50401100c0c007000c452058004100740510301000b40c010540180648240301014a040c2101c2d4925101184c10503540320b200401c0c021005c80c1682c3c3c2642c001c0064280c2c54030540003081001d100204103681c4c4211940c011380070554030710061062818100d04400703514001d00700315142070b0511020079840c83d0031784c0c030648604030040b006210352030003400048084c6000d45058903071a400701030140d4403010080d102c0703440d24041c2c03240c020800441d0001d407111190044411519803051440b412800d0340140400c0b801801100c002582d41d2080345002401c0d42e40020184c00720029040d4003210030f030f1003c240f0313000c0e41c032905c0710145c480c03074050054407240e001340d84181c0c1050300c3c0004040e065a0580d40c00501c151700c148400f440711480a09000c040a908540110703400c80c05001203070035071140741c00c0340c2650b0f8103043c0081130b0780c3d0700010401e441054000c01c1c00242959407845520001340b10a10552001e00c405002c0d61030342c880c100c6198030515014800c000000e0000190190045040316503103103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 194573210 1250 194571960 194571977
    0x140f04030605011517071b050609151b090d020405100302030f030703051c06050607260921100e0f06010816030303020c010b0402040605030916140f040912 68
    0x40280c640107543c010907071120100c0030b15003182000303803c4041c18103500484001c101d000a0720140324500c0071240342c1c40500000711024040c00c1c15902ca000c00c890b140280e11890380c0c07003030002080803c414803400015400560022081c0000035070360784890821603200f015000000302583d0b03182304190041b0030384440c0c0021140355105142c2020b83c55165010260400d1054001080c2c0060071940c4400079840400010131448000100405031a00301c20b8010001007600070402007803400c002c03840e01c3c00c2100e01416035030f14001401c007072144421181e004080003514113202d4605060194180d06004140d0350030496020040085230703105081082142c1c082d4030906140d00d014011103014001000180085000407420303c5007580c0c452100074109075000501c0420741d80290700c003903803108000348195921a42c41800601d5604259982d010901944114440a100460040c000c035600c074000c0031141804602009102b25038141c00c01d40058032080788500064020a034442000f1164a400e0f45 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 194574460 1250 194573210 194573213
    0x903020d14030d060b070507080f190c2d05150a0e0a050405101e050307170f070f080d020604121b0b270c01090504090302010b03070623090a0902030403140f0403 71
    0x161231002d078032501c040d8014804000c40604c2c04a400341400c251380710a9510208a4980540c0c2e18520b58041c080700d8080c8030340002d007280013140248070700d80c0b00c101c50a181500d81080101c444104001020a04410000c1c04039550041000c1540c03948020f015090b42e030754560224041d14412142540131001115081c8000b41d21005841203110010100d41c0c011030500300460340e540b01c603004510020050071484015150100300e520814096001a15029a81c424240421700c82601618402d1300a0300c00e004800c9100155091044d9040418601d051683e0362082c0c1d541403c8220700b102e0880240741c2600030aa01c00d0207580107074800303c0c44851100e020014112030314464403202c0d200c7d0b007240040000c117070703400780c82c14064502c210360008441140c6d20f0184d0041804028542c0c160240c1e04000540542020200fa00115010818000c1c1403049218881c9c900c115000fa6034080907080090200302602e5020715407040c03007400c3c107007030400ba40510b51540b43c1040d1101746001200280031300 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 194575710 1250 194574460 194574463
    0xc0c0703150f0e0a0b06060f121b0c0d050309010603020402221a04031e0506040b01030204060b0a080c070311070b0c0106090c0c0204050411061204120903020d14030d060b0705 77
    0xe81c01c0c0020b01c00300500b9420900c9191102c2000078003405403a4031402140b2240d40d100c3c216036280d40b05080107940d40c4803c40d000d11000d2030807680420012450309419030340d1510003044500d40c080e10405086082441101555107070806040b80d000c80d03582d03400110058403039200420100100740100e0103608003011100042c000c95030044da844400040900c0d030310109201c00d940641e03038441e0101e824450a41c1c0041360215005202802500c58801440705001407a08040e050782e00954041c0215038403144a98110b02c03601000782c0020390702600040c610b804010107445201d2003898060100307816065000e1400703800d0341109044160014699840030700074810000100500d200521103201d518901800c0e42c1032001e8040c0c0242d869500040411000c1d090b0031032008030041003640c464540d0001064001c0c000c580c121450f0302c0c0003050344c0030326024101d15001c4950080044031008a9030340e401c0c400042c8110254242d00c014000745040205a008480191055410399a15001e01c0d0500c107 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 194576960 1250 194575710 194575721
    0x9040c0f0303080604052215090f08030901050903030105010f0e121509010e0105070905120f0f0d030b0f150c16060e01030f150b091305070207060906170403080c0c070315 75
    0x190901030014078078241b820584816201234000f60203c5074491060f1610000d41400c03140202440c4445548000b042003040c003071030103a0010002040b4a5413140c020359540d00c420300400380840c40b10700041c080503108403003201e01301030050400201605151907041c54603c80152080305900d01c0c03020000381d02001d204c1c419600d04e03410000c1c045800c04007009070030000d20b80200e0340980c0740d6a03200c6c010082d04000d501c10240c010000c803100180b0009009449a0b407caa0403c0000e0502c0d0144000e032514407600b0091000044c40e500e5051104001081d6035448001c00c3c080f43d0054100d00c0c40d41580212003840205101c0e00c0304140b4880d044001030403942243e9884884514000e49044400c0c841041070701030751800898199140050800a0104000012140714442c10a070030000c0c010b0380880c01600729261900d60540645d107940040e1403205600d0b030101040d803603180002d8046803040d0711050300b1482c8404070307900c0e0156000207141881542c0e00f06a60003c1070201c040e05a000d14402d1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 194578210 1250 194576960 194576971
    0x18020306062715191401030b030f15150402031006110f06040516060825020f030310050a0b03070503040f21091811070206090102010222140d030e09040c0f030308060405 74
    0x401e804d8207040305400041d41c0c1000c01410036640700420041501e041084c1114080c4038403c44075600e58503c0c042102140c01c591100c0d10b41c1d1600341490b07240c141402901e0042162110000b036081c2032080840d25004c14540d40c2480d84602c421620301d0302003e000c614010350080b0098038184003a1102140011440c3c0e020f131081105050400200c4c0c4c4d903000ca0400a540c594250152038070440b00100c0c6003007281c44141103074cc00000103102c00560300391588811900c007510013680d2070b5a9517a02c14104d01089800c400415010000034000460170100001941e200300c1c4100e03408001d11000d41c212040c030f03500e02c00118804007014800e03d08925003051000c0c49803c2d0500c120801201c0e88100b5020f0000001c1c056030010480d58450b0303000307405860308151940442c410165000140e42e00f200b0692090343c3c1c10030110040010542003d40c88114003a406841e1003043d07200000501c424028020800d0b11070010b90480030031407106000321034000710700950301d082039410408208400c81d203000d0031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 194579460 1250 194578210 194578249
    0x50306180a0308190f061404090f030809030f04030605071e020d11100e0307060b1e190b03090313080304060f2106030c06020118020306062715 63
    0x461481510300003804640154545012121a2503090341c054801412465514846090070502a0200841e80c048002c55115404041b0380300390240070300c011600a0680545a9940741e070918012a00a00000b80c0004a840407246042109a41040c1c1038000ba00308403070250302c540170b003c105640400d6080703020703d40c0604100c0308500307290043d503544000341e228800e20030407004810b22110709000b107000c04240c41506101004000342510b4492f0300461049540074039040a0105034200f1401103648040d5012a00c0c0080d0340000400400304603580f044180d140d40008042400514500514050b9500c0d00045490302900c1d155902c24407800e401511a55000303010400c0f00b55800780a03184000e03400d0404020300f02c1e00c012802c1d080c5080030104007045003444400002c1048d942d900b42c007100d00680c0200000002d02d0800211900220f001075031591190012800c64903101c0c007690801d0040b0140034a0708055100390030081e540845080c895411181c07000105401d0810a420480e908000d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 194580710 1250 194579460 194579491
    0x2030103150e10271217060a060c141006090b030a08030a0b1c151d0c0f2202040603140c030403180b18040e0a020906090c0f0c0304050306 61
    0x481e51603a0700c03100380c031006078070762100401c400c0d0701d13988281c010394824600d000740080f1499080050740103400e1840d80f0000780d1500421903000d107800c0740d014081c11004002c216954680507080b40c0041c28070714186c03000f6980350204040003200304040c001c070b2400d440000c1401032510040ca422200001c540600030707040f205400300041d580300112540401000070000c1c0b51504000490201e508a0406100030403d04904100f03112082c2e8058941000218040c082800d40000064003d02403490300e060b1503101080100c114a0080c00c0d40c0d503c0c010260800003030101c0101f000c45070750b0305508046074031540020280300b5580d040c05000070601031403003000900c1c1424104d800481c0300080c405820131103d120403408480044850300b004000031480c0390340740d01c2400d42c0740501c8405107100328840c40c0b07000d0f6000e0180c031000c207a410625400520405c02d6540356000e005e0034a00c020038000342648200900300d61001c0c418050034075254100020b548503030400c0d0a062070303c2da01824100da034103201c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 194581960 1250 194580710 194580731
    0x7031101020c0d02150403050609100b0103090201020a0609050c03071d010906060519032003070e24090303040f170601060905130f11030a090b010b0f030601110309040f0203010315 79
    0x3001d00a103e58145c2c1c04100d0140c03000b81d001c4a60184e600014901d016075030a0102d01c000026108a011442c10401c01080d5403500064045807246038001340560400b10410021494583c40401e43c6030045040d91024402d2000190400d000c5411103600e00907503842140464a541402d1405051840c4003005810b080201c040d00034000e00720b4001c42015005a00302040707209070468090681c484150100300d802101c004160740d0000c0340c3e0040090300522102c00b9514007040740c0944e9900d402c4001000d410801150000c0f03500120b009505448108400a2000c828103150001800c0301e901c18602000e03208505070030f054060f03000104210b4142c0080c021035449100b5040301d650441d00019140c6802c105079005800b0704d960144800303101104100405005800598145100741003c80e0f4a81c1c9450035607025008840b200003a054050000400d00d50241c00c0c11070803070004900b201c0c02c0a070702c1c00000d020790702920b500d00c849075004001002088000681c01c1c0d49019600340c140801c4c03606 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 194583210 1250 194581960 194581969
    0x60c0312020f031b070f0b060306160e010f0e0a060201140c03160e0f0901080c01141213050a06090528050c0f0402040e0103050a030f0507120c030306150207031101020c 74
    0x500390701355103003000c0302c40c2e03004c4140340088900a55020488903084c210340c1c01e100316045800c450b02030290044600140300c0c0456207031852079403d580d8a66481030110341d0011291440d951a154061020701c02c80a14995030354030311040101100d600105048210f020510410040508100c40860b4240b0500154043c160703000c0c0101c008620f000b843c10762043d400603000e100a05032081d00030b001000082031400022030010000c0c4401c1e00c030080601c020125150700d51049502c0000c5840d0020041015101540d0076000003600031000c54070280c5c070a0700c0d0b44040381c0c17000d0030071600d6902090030384840014034090b03402e54a1450f6a003c03c4c000d02901d40c1130f100c0d80c4d0609003078030501b4203d4262281d40d90390f506540142c208070314006010f40c3c4038a403840d0740d072120103010307008540c10010300b11996103d0000c90b00f034a68031411107a00c01c1074604c0241c0349464003180403014141ca40002040c9904003c1440d0ba60207010342c0206010b5145081244282c150440703414115005040154002e403034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 194584460 1250 194583210 194583217
    0x4060e1501030605040c090906090b0c0403080915040b0a02010506011403091c11010906061a0306060d0902010c0602070b48040911041805060d02131401060c0312020f 73
    0x1001030021410f640c8901d0200e406d01c500303400c03501c4182c1c900b80b01d0106208169200c040c07064411510500345440b0503601c501240078511000700800ca04104401030b13030500340300a00110b425415002d05007500d0318004843d41d00550413140050303550360304200c583e40c1d010b44030440c0d01468145aa00e141800c00c1400c0d194140014040352000426090280c0b4600c16040d082d850003034180208105100c0f89407101c05400c2a11480000306918028900540503c1c412030b4002c0c10020300003072800030051080740240082c84000d9060121000d2082c02041c0705000a198051188451154600c0c0c07800c2c42902d01c12048101401083c0350b010407140055080154503135591100303416015116001120000313512607030300841c180d2400c204100b540e1408030000340040d28100c1e09580c0e100c1c2c150950f194116402120740c16480b206902c9200094200468686e00717031a0f046a010400000381d40103501402400e9004000141c85401c20005055200c01e0fa03066405401900754941112892560180d01 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 194585710 1250 194584460 194584463
    0x110d03020a08060d110901080304030303050c03090a02100306180204210507060e03250e150f090406090b040b071404080d1107180615030209010906030e010b120604060e150103 77
    0x88003194482e0038000c00c95400345568200500d114250b41c1c423003500c40d031070750003522044001c6410203012403604040407007a6440361000c20003c00c00310340c080c1c08101a9031a140b51030000e0581c3e41c1c4002c110342c01045d07603841c00b000f0028000342c1d54919084039030010783c040807070008006030454000400201c2c049079600454126107460b000615100000a04140c14201c0800c0e12500d21009452040000d9507410b080317510340da00c616a071760f4607200283c1c0d1200110786071540c8621400104101464890080e80e04180100c00c00100c07401300e45d88207200640159802d4458510001c100311180d5400100d1100001c0341c00307502400c0501e400c040954440740d101604061000d066840d034440c200421980d4010105107940c0760143c10880a01e4000340717081c0c042d01c068812511861142c5c00c1c000c0c02103c148407010380d142142640b900ea402ca00500c500007441500d552078802a080340d61305d01180103003040c42240640340c103041174505007044525252082282e0b400404001c2d01d620041e401c95070442c0e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 194586960 1250 194585710 194585719
    0x605091f0902090402090d06050603010e0f0a060228030b091305030301090506010c05250506040303081302030705030a081b0105071710030c080c030f1603020402090f0907110d03020a0806 82
    0xc3c4041c0300050041d0041244107a0000740e8181000300703100494010318040c40c026002044a41c58542d045a00c503062000f03a40b1070f03a0b00c80c210742000105c2d140d0040807101046810400212a01804014607404c0d10640500080e190350660400d45480031a0b0354200c1d00b40d0390103006e540300756501c05459000511614070303d1540d46000404a902034081ca034121035002041c0e85009850041103020355842d00004542490f0040c0d0205240c2000011601581e4060f1120001c03030703984620b03059100e000c040089805002d00700340028582c504110b640b181f18030540351991a0b411000c2e60203043c0710140e5000c1c0203681072409002d003050300b008450f1108103980c8001241c1c0e9442c04c101c0c03581d465446d48010503212003000000340032007020800c1e40c00100c041342501d0b40100e0407201959640c45102c4003031049464078070100014075099006056511b0080e04c0c6000c40e01d006000140390b03802c2220b081c004981030340301410401000b482502c41402c40d40c101107081c10304034107000341960f8008141e24001d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 194588210 1250 194586960 194586967
    0xf010207030305251b050301050f0f090a0813090b040218090c0f0f0a030c0c031b0201030f0f0519061503090f060906020a020705010c0b0412110a060605091f0902 71
    0x7010050f40b000e107035400300d01c0d011203e01d400910700b82035150360640d5503404051200d05c001c00c20340340601419016004594404500352114030400120b12009003c59425128242c1c0d80000a241c0c03401400d042105045000c00091a10130a841a07030a450200f074881c0e031042011046030840985c040080c0c000580f80c6814039503800203070304c049210705242080303403040c00f042104160036010010200c541e020740c1c0500c00c0300d100b220300b42c8080703101c6030300100468645421413086070000039100785c54500514000c90089404404002103900c1c0300c10b0b0300c0c0465112010404003009003011101c4580b44403c080124a00d003070100f101c4560ba0f03146480405888581c40310600c03080c11070142e80c0d150422000c116265003490104000d600400c00c0340098003c0490026040d030081c800c2100c5103801029070a00e0b40e440d075030f640d07080098400b41c08041c00310b240380303000ba6603104100030f040c0070740300340000208181040100319651034010903150f10814070104d845500300c0e071000300b40e0031240203d4003d600c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 194589460 1250 194588210 194588227
    0x901031805070e1b0403080403021c05060703050c0d060e06030706090608150a1814181b0402070b1828060c0203040914060f090103021c030e0907110c0f010207030305 73
    0x181091301e01d502c0a40760001080100500c17130700701c1c01001101e10850340100b0800203582008801005500044c2445c3c03c024001075009010742c0209900540300200c042c9400580b05c0031601302d94650300002e10200c40d06007008941e0604122600c0544018200035a40303e1400300020441840140348079212010b4401040640c1c031142040d0b0043c200501ca000722035601144c205005000714100044843e0b01c4c1e50104200c0011985844005002c0340c0181c042c50034865204d080f1081001d9a0395005a42007000c030002c2040f003411035024480c5041e4007840401c0d000d07035640c50b24600640792250540f1034080301040c024814280001c030307540040041441c614a010603819400b803a0300480d4558104004000320460407811540700300003c0b950b20080145074414032440c00700902000390403100c005e0340da181c5144801c07620380125200e0b240c041d00001212002c190500d42c1940d0f207070003003041200c60480382305082c03140700c150740d1040e10319800803005200001d40e0340044d440090b041c06000a07003841d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 194590710 1250 194589460 194589481
    0x51015050702090108010506040c03150e1005060318010b040b011706030a12030b0102160302060f0310030503040905091b0303042705010f051302030c070209180d050901031805070e 79
    0x81510381c0080c5000030f1582c2d9013070544d01a00088070300310300c6146484c1d140400b10b4080d1243d000905015404c0b042d42609045661601d00e02c00b51884e00714036808880000c059403038000440c4109201e0425012060030020283e0030b6030b1842c00b81c2c40c855030078100851030350390b03011080c0590040c8400c6180700507210100480e00b007100026000c0c2074005100c07801c40c1510f0700758101c01c885030001c0e4201da000624903a0f01403049101c42c00700030752201040240c8090b540d120300245402c048030100407074090b5aa50740e05c61540d032195005411140e110010443c00d0b04040c44003030070040d8041030700ca03680384220000a4491040c0e01a021400310004074803503a4100501c0c081038407243c030b01010880341d610341a0700380940242d48140c0c0c2c46054810929011000345000341c2c2d0054004100d9242060140c0d402c0120401004080c000d200e00700c00c400c08001581001074440460081e154655070381d90810004055131500030344444000011a201c800103100010400304841c00c4020003042a00d9000a04 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 194591960 1250 194590710 194590717
    0x150606030406180f03090f09021c24080a020f0d020328020301141006020d020a02010e01030b04021c110403050a11190f1d040807030e0310140402030c010305101505 72
    0x2400038a4204e03141d008141d004118801070f901c0355600001c0707050b0b0714440e8038168410000d80501110180860402000880c0c20604140300b148400b400e070020040780410801d8016805040f0580c4030032000401e60034a030b004404180741c262011429036006030003181d0782d000c2031605c50102070010b40705000b800701e070701000b40b03201c41e40203000380484008220a58a11002562242d6802d003048400040090000500c01c504030340a8000e03080300b070166001520101d000610300350504d074881c0e826040c0c42c3d03651310043c0003000104613501c1c401c41001c500341c1c003181c10020030216901420442840425000034104080035805186031540e00d03114408038003a001568850300b00400100c0c4089100d010790182c42e002e48180c0f02c0540c089160350000c1c2d0810341c1d030540d4041d05c010000c2101c4004648210001c2000c07200203000c0f10341d414400d01140d0111600680c40b42200e030005810f001c110310302408070200400c000d03e42801070b0304000442c103400c0388003486000b6000c03000444203583c040c0610142d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 194593210 1250 194591960 194591963
    0xf0a06080709090203100c0804080d0f020c030d0c02030a0203120c0d060b18010206071205071709070302010e09040c0b0c0a05010c0518030604150b0f040f0603030215060603040618 79
    0x544141c0e6035241c403a40d02034040800102d02c40d00514a504a141c10705d84141c600c0c40f50503681b51406a182d6840748000c980c0101d141483c1e150b141c001c00e4410720460300084c12030074052002541c0d40c07100c00d00f80781e0072a814418988115001084030300c1a4603400415200380001e4400c0040403a01c9031a062111403049590f600103580c14a107001882c41d8422000c0e12000580c860880c0c3c070b03c1c02e21001281c4620084540502080280000306840c0000381d11060744004181020322048002160415100d442207a0540d0140d014030014000c55901c6030740c5000c190003c1e20f01c4a4181090b030b4902c0d00c262250300501150a80100365104161380030004418640d030050002c01144d085158005c0c0a980400380c0d90885524419161041e4200003030304910a94002e1381807822500c80381602d102411070b9664103644804c410010b054240d0310762040400b41140003100140b01071441c60007904014264003040d805680d040c1c00c000094a07140101d9500940c0034800040703030300d4035000d14403901c200e0400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 194594460 1250 194593210 194593213
    0x1009080a141b06040b10030b070804020102030702090405030a0201111204021210050f01030b011d0a0b0d0c08010c0905010207030507030b041707110a1403030d150302030a06060e100b030f0a0608 85
    0x1100c0b88030000306000380154050052140903503030b184500c6c808400c0300d200040081c21460b0002e10824400c103891600329205206691030480c2c81d4001a641312005d4a095070702c1e4100180c1848055024820751031110451483c10341481c601118000d414a0028400f0340190090b194201e144a018048041403846800040021382000c401051041c0c40034001140c1140c604800802d41d075041d105540303d15009047c891000340d55150310100500904084540c009020401280005501e40d8070f000260182c03000000784140e10f2070005003500c019910407815508100010710101b00041509416650003a0202030940c85920300398091022072044600d28140100310781e4100403840e91680c40710030084078610400d40d00e40007103030202101500110341c59481000080d00c4456280c02500f001036801310101041981c03500404d04180c4015022030310207603524010f0180c00390b030385549900461803802c412802c07401c20000c4002440042d0400d120141e081c0000344090450b500048080c211540 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 194595710 1250 194594460 194594497
    0x905070e07030617070510050c06280603060218012307050309090103030c020103060b1314060f0f070308100501050406050c0f0318031203090a120e03030310030201021009080a14 78
    0xa681c1d00c9004034082d847c42084c100f034000343d0b128441d400303450f980c44245000d0041d03500c903803007030340d110340546512030300c0d0515201820904102036100b440000c6000d01000350366014035001b09840d18601020302c1e4180401840c036000900e8107601d81030118000309800c1a40e0301c240b41002855170040a0700254040d003c4000841015800000f49003010302c00c0e00c0601540344c9072101801a402000103c400701d0240003020801000d180e8100d41428078080e01c0107161100e86600e0740541e86c4080f03281082494001a090105603202c0f0803140d102824500d000b002604180c0000c21794443e908c1603500b0880045003450400300203000c0d40c01e07081c2100007260b503502d00040d05041c410018500e2248a40a003070f80d1100a040b48030202c81c400d000620190060380700c07554031600450310000311001000940314500c0904d40b0100300842c040c0c1e900078047c00501e0325620009281c030419070718580c8900c0c1001d401d800042c2011064454090140c208003130401d6550500c10030034054800c9003000e1a00b02d5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 194596960 1250 194595710 194595749
    0x2181f0c030c1104054f020f040207060504050d08070512220309090b0603010b0a2106030b0a0b0d1203051302060301031b0807060f1b1a0114040905070e070306 70
    0x60b012030b00b081b810b0703154960042404841145084080222100001c50384c03403e60b240c84849200846640d48024070b0b641c090724210000c10201c0e0421101102c58981e00c0c800e0100b880401c00000e4046102407500c019589032041d001800b80c02030749400807202c40d40e20003040c40485c404142800070008032409d04800406418010601901031243c3e884051a0843d9041c09083c01c0c1d00700c80c180c4440c04401c6107440076200c8115104094403000c2c3c420880540c400c090800300c40c5c0220002540150300c00a99402c01143d0074003251a44040144140c113041903800000d0f0801e1100c107030190302400c0003e626590380e00500c2542c500410001d500c000000004001c1000c5020180b8480c64000c0582040640310030055950304481d000c0c00c000309458000000320284120100303403d0389090b881c20900c003595540d0707007038080031600c0740d501c00b20358000010321101410300950002d52004444c20b220480b456211592500441e0007000752180c001000a99881d000703401520040030351101e07003181665030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 194598210 1250 194596960 194596981
    0x619020105070801051005030115141605060f130f0819090801050c030c070b060301020d0c0519090b09011128050c010815010f020f0102181f0c030c110405 68
    0x2c54038030020910075400880e19003480e1b052030388441c500c1e444c2c8500c1d51b42001017001401c80134030019801c0119280300003c10341c1c144005401c980702c2d50301450445000f14a045814940011300041003160260b08000c6000004605d10031425001002c0c40380c0b4240f142171204d0b9034401d400185506403484085000000d034030440d4601110171480003040b05455102210030744e448103584c9210b005809000034070100388011109600000010001031428940c21001c030f054800c18480b042c08900c0c081204001c064840600301d200107020328101d500355080140d402000d000313001c0c0203410440003d0f8903201d518002c102d03016410320014007400d03100c108a0742c044000040071000300d5960080c4040c4030b28030b501407040305011303e03a10700c0034945a0742d16400444203030541009540840c440d642c07030901100001c0c4002c2420b0503001d0220840d08100d04140b250480d01100354224003041d40025614540d8082c41c0b041ca015458907244030214003d0a0241401400307020641d4407924000500c52661314 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 194599460 1250 194598210 194598221
    0xc091f050d060902070201171021030e010e1302070c0504020c071d0702071403031603030b030708120f03040201170c0406031b020c12010212010e0411060a09120206190201 75
    0x10726200611502d0748580e2180280c3c0030303108001b4003007010743c91280c1c507a01c1d068050345d40c03007140c081e01010352585d10603c85510017a20102c6c46840d01c4003401d807106050b40a0a1811900000c1c20b00c8607107020088085555650110310314000d044d03005c1203034030411081c0c0e00014014140200150748078420021704544803c603502c5003440140068110b5018000c100e41d11910441c410b802030041640760140104400403002c05e51036160000b00142c10107404111090200c1c14042e66000920015100506190134500e41021078a903000100340b85e000040d503811580e020b00c5542d6159200c2c0c80d6032006850000000001e0f5400c1e250020821540310481005402140c03880d64091006078034144150a540300d80c602d8900050f00014082103150409030030100e41b144042000525051040341d02c051a00d03420380000100f61151402d010a12860000061800030100c501515002400c0c2c405000c1d540c0318480d590390030420440c03400c103541d207030b8080d00c00c5405110740d1045a1042807000034000c14 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 194600710 1250 194599460 194599477
    0xa120213090b0109031a0c0706020d0b03061305071809080f031608090a020409110a03030806030c03060106050307030e100c020c1e031e070306140a0606030c080c091f05 74
    0x51502c041c01010350b11885224046076040a020500880740c0d0300c600a41c90030050110a004800704110800500c40b4402090180e14041000441c1420a0205400e06102a000d0b0b561190ba16002c0e0000c140d0118000e02150b041c00d01080302d40c6440a50200540707001d10b009403032000c0118502105030360341002103200e0001295141c00c00504510261000c082c02c0d02da005032075005000800041c10b181e40204c004038041d02200390f02e102540c0000d900003d040c0c2003100000c0e0060b05000c40c9040170400c507040341004601400b015810320200600c139001c0100041c2c2010388486031024160b106000383c80d40081006810b20810769803801c00ba58442d41d041071640154412811201840e2440c000c0f0040040000c025000000a2107002c0300d8101c000148a50940a00c28000000604034031618104403d14003000c1c89030705e4500d1241c4100c4500b81d014500b03044c10140700d0b1081e5588541c6450303000a4200005841e0300901012960903040c2c2c0c0103840c0c4c1c0481090000c003060303400002518009 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 194601960 1250 194600710 194600729
    0x3030a021608030301031101030b18010f080601093b0d030b0907030629090306070305060108070203090a210b0a02040503071205060c0c12040e070e0d0302060106050a120213 76
    0x20b5481ca151556031009200242c5103100602d42c000040d0301c29045448140b1004021920800656401c2c12008030217901c2105003050300141007080d20002c1c05030354010440d2200420110141d542135090303a841d6150b00300d0b5603101e442b281e5060407404040b07440c5400340300c030100c4900702108803025008166224445116151100010360464402d014101c181c41c1e0b07203500ca41243c14044500e0800380d0076059032034541c8000b444442116182009080c1c4644515500841c0c2428a5400506441806400c6d4400c5410810a015154807821800d90032581c3d030100a004000c405000d0300d8403610202001000300d00351406100000c40301d134015000b0340354202d0a54071065a1001c03143c042c4108548010a290000c90016603034580c41c001034080100703406d0595120f4043d0420f0012240e0041d08180b00d0314001b8014001d10940c05100c1a10810742910403004030b000c161800796981e0814402c120030842c00040d00000b8500c6075112142c05034205038190f468400400d00140ea00c41d090003455101d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 194603210 1250 194601960 194602003
    0xd05100e010e040c09110403050f03071106030f010612180b01050109090e071202040e030a030f0f0b031c020f0a050624090109020d06050a03030509030d020d12021803030a02 76
    0x4002208050b14040c43c4c3c0300300b140040740e16090701e0714041d0040202450ba10007041c4130020204c0e00900ca1240e0004072240a940d540105140299903c2003080011f07016001c24410011449001200c1c2c0f419a503642c200614140510340a48016199110b5184c00000e41d85941c3c40070861054092416201c00b621001000c98446d0395034011203424080c17080155002c00f60030840b1300b0342d40501083c020700103070001c0740c1c6240c0da82c20945564001000503001994540303450490714864030455805551441d81441220305510020703550307c00303003031800301c83c0940d030304030f10480d14000c1040d103085d61a030001352100b01e140c5040403030720b0f8841107e2840385105681940305900340422551300909000400c0d400c860303401d21003140001c3d000082d0284c1040d03aa81e07400710f03181da5074036801c0b00154070955425660300b110b10107150800369000d14040030341d402078015045542c0c0000414064803210f03007005071241e0704c1401c0b41c1003400d0000d5006805010020341a600700c1c0d4003103010000c615140200340329 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 194604316 1106 194603210 194603219
    0xa1203020610140109151715121c0c050120091c030206150a0b03010b07030923090a0e1f0608010209090a020903030d05100e01 56
    0x941c1c0706600308005002406003000243c00007040142015540900183c00f0320070600540c1401ca40607145606458422003185400d140b401d00c10303401a0078003e1401a0003900c0311240c0d0701070003803048201e642400000e1a410001c400030761000030708081210441e0220320650003100c665403103000c6688005401c05000881310030321f044a50b03880501e00c0810098582c00c88807541c007004000c3d020700110390042950f51303200030b100e002c0000190300a00010302d2100c007030b0440c14405c5000301c004500c082c880c3d80640112440ba0b11107805550325420504110b0031000c41c03100d900458410000d20030700300780c040c080d00b000c2000404900d0b6004401c5550500c081110441030006d1400603114500324107019074402006064003c5250006a001042c81c0050050003081c0131900050040056141002250198441c03110100054200349030302042c002c0141c8600018400d100c0d00104 = true := by decide +kernel

theorem cover : BRFrame.Cov 194424460 194604316 := by
  have h0 := BRFrame.cov_init 194424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 194424460 ≤ n) (h2 : n < 194604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
