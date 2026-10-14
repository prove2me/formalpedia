-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2100
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:39:03.554794+00:00
-- url     : https://prove2.me/submissions/5c6effc9-bbde-4f3f-ba6d-2c3829f63608

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 377517985 ≤ n < 377697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 377519235 1250 377517985 377517989
    0x3270103020f0702010c050a080c0a110301060308041e08060a0605011b0b01050f0a0305030f120106020f0337080114040515060a1b0b1806090c1003060803030109060509130309 77
    0x40008075500201004400c008e405000384c0c104d800b203a201e2828000301d5a444580c03d400311648030049030101e90f10300f0140600002d0380d80c042e0140d0b04290800c14591024111601d403c1c00d400007030312000503018401d120050181818400c00b00b8542e00f058000750801e4841e10040800d13810604403400442c4005017202d0648800300d6070542c50001c0000001d0364025590000381050000003868442c01080100400b05d000b0190101a02a80e03510307410790300c030000e0b000800000d810400500d07403110311001040c4000040382020944000b41c1e08040d080300c1ca803030080000400c0301ca41c01032240400c01400360840c2c0008a8050040b4074001c05140b07248019400c0e014000c01c008150300380e1450213a2030302d2120b842d040700400070301d11a0b4107004160140c19201100641903010074140b1061f4045101403060740010001d001700741403201440700e44003110070003104140c1d41d1b40e4080b580180900c001c600030460442c1c00700d0028145800c20151020280000315054003d60340d05000981104080c42 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 377520485 1250 377519235 377519237
    0x807110f0c21060c0d140705181c0302010f050109020405011e0314090d030b010c031e1b0308091207030801210804080f0606010201052a0c03270103020f070201 70
    0x4118180d01d924000d21400440e00100c01d4043c0d40200315200c0d580750b001d0210904406402d0042c880518160480c807401640d060000450410919801d0a0080d03414406403502400701180845900f090746514041e03800c0850040c0d444400f040da283d03250340505070140441c0003003189414a040c0c0003a1804808050001030050420402840c01d070003903002c402004400071a5000030310f05264a59141c00920001030042403420044c0500c552041c4c0703c0c10780403070b4551900c080c40c80d94070b50800e9800d00c2c2c45118000300001d09820800d00a58240c83c80c119510079260359915041c03e64003a4102540c040040b00e44100c140800004039901005050442d17042c0107400c1c40a10b0b80d6803200c000c06400b840e01901c2c00781c0003d4002407917407000428031800850381d000c1c1d03407054641c0c41c01203099a0095032030070a4280c071217880240c92400c0c02607010000000c40030f082d20f40120144210304580140423840c90340b41c260002d404441004a01884041d4002d01e421460b10800c0303260710003140603035080a8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 377521735 1250 377520485 377520499
    0x10908190c09020406020f0d0e010914040902100f020712030807080702010207050d050304020405130b0a0b060c1501170708070603050402130501030c09110903060f090a0b04030807110f0c 82
    0x8051101c81c03074005000d0000ba5030155038a40d242c0c1c001070b51f00d0560301d1014019204144224445034410000603009a105039289012549000301d90001110b29030300a0758401d90380c3c281d850041c0d07030f20301c0001d44c4074443d40c80b030f4003655500200281c101022640607007058903203000c00c030b00080d9200031416440121402c1190194541d000101d00900a04070010050300c1084d8901078000c0d0080c0107988581c0c82224140090350ba044150038450601410041c41c1004a01c04a00766000d41c2d00300281c680c2c005016141081c1049030780902e086200010203403031a41040060081000302c80d00c103481c45031540b00410a03d450a40915903416045c03081004050750b8102240855075a01c107034510f81c1040c3c0c070040c0906e5859090405d50700c0709901c611a81c075464651504041580340c800d0b41c0e11140000e000d803c0550700c2c407a82c0c11084100074040202070107130940032000500703080c01c210700481c00b07561143c1e40340c81c1401d17000e45245200a8101540e902030b03a40864403000010b94110104416034100d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 377522985 1250 377521735 377521783
    0x8070207030503120a290105090102030f031305190305180f0402070c050906010c0c0527130b07030203240406080f0609010c080702071a0d0606030203070806010908 72
    0x1242032569a820080560000090641d448010306011600442c9030307510070040b01e9104080a0317080500060410118074842445004543c02540074102612041c0181d80c07412012000c08003072076004403100d05241e00201130210074408100002b842402c0005d8090040ca80c441d2800f07019070042c0d0003010000e60701c0c12001c42c0c0da03880344451074001100242c400d648902c001c0c07402d40c010348010701800340200a00c1001660030342c410071496604d43d4001f031003000118101001d001050000030003000114070700c0242420f4028050701c001d071003604442000c2d0740c82c400c903151400c800040580712904143c014001d1140316040280485080010612601c1800c2280700105000c0d0800754040702907402105102c2e640c8241c007146240c42085139200030422500d48030000d8844c06019500c0d41c0041e8413440c0180100b01601a40245400c81030340c03a9424001c5580780361080e0350454011000180d0080103201069800c40310082c0c010400342030490700142028091555000160511880544a0051 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 377524235 1250 377522985 377522987
    0x20a020a1e170309030d02070b040b031305030c03190306030803010e0a0b031b09010b0406050405010503040f02130c1e0203030604020f040e070905030d020106080c040c020f07140f09010509070807 86
    0xa10700c02002440b06004061151018a0703440b904503640f814082d001304001144981d1000c100340d0150388801c002142464102101d04aa0741c100521407500d1040c286c03c110041841040500b903d0040500216036645400c003d9507800f4a00c561484181420f080b42400010b210f90190303030642d808000110b01a5555001240203801a140502e401d40280e104203841c0c0c80103903007080e0b5000403e80310602507036030718a48000e03244039900c12280010000d0005000d00e40c4100c00440d04103020301600c0c44511a00d80000c0c004001c00c081d91207a44da900c2904a0829800c410910f101881c43c072003460440500e00c00c080e45a220080c0824465035000a0445100d1010410f4a000e40780140d81a00039240004001d8a0500c485c05800e00c60302c19945619030091050213084160388134030001d000071801410510001c0c2c84481c03903050a500030b035841040e05803402c014650041804110891503451b6040501180349412010300740100035800050049803118103403190001c8061034941e080740e0351204 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 377525485 1250 377524235 377524289
    0xd230d0903020f0313030326040b160806030a020103090314040b0310140f040f09060204090f052a1303061503060c050c0a141501060c050114010602100e0106120302030403060c020a020a 81
    0x10184980e10200308c00d000c00d200c0b10804862150400407400d44540042c2d80081d20107441c00c580d59641540f08980c0c000055100350041020284203080074007000040103d901c121380c0141c1c0018100d048003004220000c40c98840d820003d00002e1440d040b040001000b041c001501d401030240655120000912013002d640c4c01000d400707410200840d11192180c0000e8003070006c0c800d071b514556040c078012aaa0381d0684896250f44c006011780150001000c00032105540c02c082ca00390415a210300340000030500c0d80c01441128142161407958141c1540340210448554481100c04c10205011001e4084030010341c2114554001c20500d03600d148841003240307401d0214021094550b0841e00000308184c000c100700c01c500d40305000902c01c08841c00a9014440c000740700c0c10005900c41500b99040181c0c0d0b60018298440d0301001149642c0c480e0000c1c40c1034041c00400b10010303170000400704103005551007000b03200542c9201402012829400046080550307000d444a4164100300000038144480 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 377526735 1250 377525485 377525537
    0x5030d11070801060602070504060f080613110402030114010816020714060705010c180504050415180203010c20060c030c0f09030d1116080d230d0903020f03130303 72
    0x2c00207104050319040c00948a100318440d4a00035402c0800105030701e42400307000c005607000200203061075501c811011100805005003580e414007181c0c000070a903140e900007140a000701c2006e0b085908001400182a00d84c000d18554440c031450200c40384195012400000b201c0e80c44848540180c100d80010b49140705900c001483e1750729207158191100d800400480e8410761601a1009455030381d805c1c40107440044400800c5c280718021811100303009030f07100c000b00c1100603201e4074194003640c0c04603085443e00c0c086070004c00c140c01d50307410f441d0206003500050701c070016010303180310704000a0445481c0809440c0401a24001c40c0c2240c4045145058440640f8014200d807550312042801800700940c503c0440c2c054054461018100d07941e0384403281c200c03202080200519940e900007215200d48642010602c113510f51907680074582400058012039810140000b803042603442d01034036201c1c02c60007091903600288070400c50b0402050907042106d0301800d19018818803220307400c145010709 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 377527985 1250 377526735 377526749
    0x409110607110306010b0c030306060a1809021c06030f031b0615032904110f03070b0904051014220f090201030506030a020d021c122705030d1107 64
    0x803070700d0400c0c040ea076900e0980400c1c0c01d07000d681d10369032240c2c02516a84582c000841c07080c2c0c400c001103150f500b07180c00100740d141c0c1149440080220680003000300c4100700d42c0591060f036004a5903107048c3e2520402c4040d40d18400c1401c120080c40c6079240c5a00c010b01400160902403440ea210051080c1c5001c00c502c2c0c6035121100300004e440d6844e0030155040e59000c01d907529001c4103241821000000141e0169100844542c41290741e5940d03000042d0f0701480301150001c0c19805204020340f000c0180d0310151020f506c00580b20288075091100701c4100620400000351080390400141451200a459000d81901c1c800300b18404181c0c8141620694011107a80300d1a2007000c0200450550001004038400d0342d050129032221000c040d6a181d54410295100066042c0d40e401464103031a011146002d50b02c0802c8013000644030101504101d03400c40300415030741c2c01c4d42140040d4030a2100b500380b404045e660251800e0101195454150a2240c000e01540010307142100c181004a10028812 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 377529235 1250 377527985 377527987
    0x8030901110703080f0109020a051b070503012306100f2a03080f0106021c0c050f0303190f020f07060905010b0a0b1c051e04080405090112051908030604091106 70
    0x803d19005111410494001d0600581000007149161403802110700d50700311583e07814101610003824208280c0126000d00c00c500c01e0000c0044d1a850a01425503940040c1e601c040b4068091082e1400085000780310b544030b05014032808070455040032001800d01c3c2c039032901400f15280708503106d10500064178000350f01d04c2040450000c16500900c45482400c2000ca0042966a68041a81e40341d41c0007101c011980e0f0f9001401114500c510b40b115117036405541114089c02c842c40c07039182140d0042d00c3c1114128034000100070341072000d0040c41d205008040d01145414000c03400f10005014a520040c1141d40f034000c02014803070709400544400358018071445032245d986094454a41c8003035900503444e0151400c21501a6042c800c282c410420f1401c00ba001aa052281d0480c1a100400856412074180b0000c1902e840d00300c2c010740a4083c0800390b0010308200e0802c80d18107256208187d211221a810070000655407a0039203070403178030070369011074014510305e0448407540454500f6900254 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 377530485 1250 377529235 377529247
    0x6052d0616030e030f0717070902030f041406070c061109090f06040c0207080706050c0f03040b0406031404030e0907030603050609060411030f060411210a05160509040803090111 78
    0x484065141d1810b200c1c1e140d586418072141c09068a4140d0302a01c1d0045070008001000034608a0f1110744140038200143e40d2266210b9110104980065608080c450300c403000700f10402810b41300440c00b00c1c0c2180c0042c4505d20306401c0003440c541207d103000300340540700c0458280f1400d814040d116213500040410885292041c6041c0094900301c2e88180f1684c00c3c880b070105003d00206191041e04c000c007015102c100d0030031000352641c4d800307902440458441d072003560340c3d500014000741c4081e096407046150303510324220000707040d030f0390f5058620428003190080c800041e40021354074404403029030300d074000d0b0f9440b18000e80c0100203030f41c1302524500810080140d0000041241803103070b803007040c0d2201a541d041c0b05159440740031032450800b80d1b2005000c100860003541042958620090014281c00d082d10803c04460000c01c074071103950f5200110280800030103010020000b070a900f60300003074034a041c0009600344005000030308200c2001010400071071080d0007200f0f651080d2607e15503152 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 377531735 1250 377530485 377530507
    0x71509030f030e0f0a0b0904050c0403020a14090703060605030a110d021b07240c06150306090b0708190e030909010f06020f0a0b060f01020a0b240406052d06 69
    0x1030030801c150351051005034050103281c40c140c81600d041d80d446c0000b89040c0b4030103000388402010050860010100140000401640c0340480c28001c3c1a03820694007040128070300307220f451a800381c416801d2500b0510f0034040558000156a4030020028011602c04800d40700c2503d64820f030b8440c2440340303000060001d610b40344c0c00c40c40c13070440c03c1c0101100d04141d81d802c40440c1c4031401d99161203682041c500082c1c403103403103030140c094440e0080c4800aa0390003140da0550004102d0390080720400e8407140c2d440d0512090050155000519050510301454040d11802d55108446c04086c00c055642c1d1815506410400c29030b8801752010708031405c0355864070f00c4191009540d1103260014441c5442240d86490701181c5040d1450b030151070141143c40b1b1908001c40e030b920010300241103204900108010803407280d40a07008102e4410f40140d0700f42c103468a4561821010b400501850038003d0030000390311034000441c45801d0601e89400000d821060105402460070003290b401a00895050810 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 377532985 1250 377531735 377531747
    0x2001020406090b090901030b0a06180509010c030c020303010b070804051009052b060207061e06170307050a230307060b1c0b06010f020313090902010e12071509030f03 73
    0x1880082c0c8034005410365842441c081e82c0321348480640c100981900400000b8484a0110f4015002d03410200712252540c01001401c8000a5000103554a07001444038000080c8503051000125180600030082e409001170359030303c0180300e0080c0780880040c1c51001d1291030000c0d00c000c0c1000502c5120f4902c2c400070000c002d02070901840348207884203078501d920030a6401c03650100d0340ca21550b804038401c1d681c48803402508071b4042550200d4440400080a04981965400342400e00c200042c0c02d50070103050210b400240406400554001c204060100d013002403400042540806a103801c41c68010a2500c40032002c1050501da1001044170300401a07150030180c82d80034140c07004410210b13000c041d01c00b10481510050950740c047d501103644d13948100c144106a4801c0e00441c0c1ca0300b1001c60000d441481303c0d80c0b120114907920748058046681c403f11290304200300302c07400d02d5294540c119040e29000103100c3c0e403910038a415401420107000d60802d6000f140c000b881c281d280551030a000d004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 377534235 1250 377532985 377532989
    0x310140a111606020904060b12011502031216090503121210061709011e06031202030307050a031e0c12110c07050f0a0e19051e04020d0320010204 64
    0x10160400786440005a644015a07a90386481078104005081a8852800a5101d0711445400c19140d80001c554488a01c0080c41e22500102e0344002c0740d0701d009011110604040000400c5400401c44c03181d00700320390300410350415030f00c1000c80d10700440c540741079500c5040c90b40320235014012041075501440c0c1520240c0b4508042143c1003800d50f80d070707000058002100340118804204001500c0c60900007100b103c60380141c6031000001c0441b44841c1c5400700c5400704ad07201c05030300e8880f1800c0c0b0401151300d503011a0308429000442c01c50130414406041b40c012070780e000003056980c580e404c011301101038000e1a000e0025900304611860401c004120f080b41c828500d441e542031411203003058032110111506070030b60078094a0041e003000104681010380d03d515950220444070003007080395401c600d09001d110520712903109070300c1005040c0c09441c80108804081541c103411501c0c0007030a00c0005521550481d001070b5401c1d614a030681e4610031002000d806400d5424480e8442c450550050003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 377535485 1250 377534235 377534251
    0x213030218071101061203361802041202091902030703020301030b130b22120201020c070609050f10050715150f08031e07060912080a050411010806031014 68
    0x503c00700d4908020382640e0a41c82403668100c101d60703451303000c64411020880b103c1101c030715045070344d6070100c0300f1021a03054041281c10040050010005560721021841601c4a0b5200940c2060703d06145680ca00200100281c0218083c9002a403000b0f0710354144020040240707021500da0a000f44002c00940013401b04691119440021540781c075440500780e41003030b9001c100200c4aa83e2403d040300c5071202d284040904100d4050302c3c100091110001151000c055400140ca0300c000064081c940740d0300e50302040501500791824440b030788070030400d441c42e1802585c808038030315024042203031070f842442d030302030002c15128071503101117800c40e080104a02c6c200920040903548400010380c0e00071081c0301e8102c603648200a0707a182403040c100c1460180c400494a20b017000f42c581c403a00107507030014904943d480c1a0800c540380c0305421041c440d401a21103481000b0310320b8541d8524510160003510141440f054900041d003568040004010520140d41c00780242451841801256441074440f21 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 377536735 1250 377535485 377535497
    0x31217070201021c0e07050909100b09090709020a050f120712140f1305030a030506010306090b030a03031a0604090209120d0912020102150903070507090507050904021303021807 78
    0x100c0403031050082e52819481c05880382410990284040c00a01c0f80341008400c81c000ca07100000c1e80e41e15a12014481c0c80d0300c3d006400d6501c104c9084004031411030004900c50b43c2502c0a020b0f4081e000151142640c1c46403500503640c1c00e2058045e41d0b68020b140c03041e00d40040000703058107080c94203684540208403c1d100d80844003642111042540c0001c00d140088401c0d804c0000c0c0b03505681c03400f0503008400c1d00b410f08000001901c404c1e00710f5000c0101032020076120801d04c0080e5a03d07101e04e00c000c24030b000041240140b05030000c0d88411140030044c0425469071303c1e0000120020600a00c6039400410099480303540d0b0083c80040d40182c648181303d0800c80c0c400c500c607080041020724000120b03a0702c0c4070304c00e0f040096034000300310125402c1c0d045204695054031a25003090710503000e100c940d4004c3d515503e40d460520700d001c82641000244e54244000e000500e500582038550b01c0008603000341e151a00402030713050440e61540040e50003458103280e4020300c0001c100140c05002c1503a564 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 377537985 1250 377536735 377536741
    0x330b0103110a141e0c06040507050d080301090f0e01060611070509090309010f0c0204051e0a14060d030201020f040b030433090302160b1b0118110109031217 69
    0x1d41e03041c00340380724100216242c02419001c440e500c400418400e6020f90381c00c42e0f46150301000e203225810213542c2c200150700180038003050000801c00c1c40300903d02101c80e41203225076035403040c01c140810300c2070084844c4c9509030303125004030790b41000c0d4107407030180004c0040e941e940000900000c1501200000742c01400c00105442c280111140d202e040000000d51400c0700c0b0000442e00050440124010055844540070040e503d600071a4058242c0200c0d2002010720b03001c5003409407001a0030b12071403514200c803121040000000d01c69212400b11008130500c919400c1c160301a11031803015401c850380c00100882c0040d048000b45020702e008a0030203c80c02804903070444940300c0303980400f081304400074081001c4a00b03600100b0005e8400c2c03040d03814086082400f600300b40525007010215034000b0501e103680e010a2040c5000c81c032815030003032103c01c0084070684036400301e00e2809440f03503413403c91443c81e90f4080c0340058001c6a1000c5000f08900c07007060001d010990100c0c1e080140c41200000c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 377539235 1250 377537985 377538011
    0x7020d02090702010c090801020f09150f1c050603240c07050609010c0e030708060c030c040e090601050301051003170f040b0a030605010216060e011808031c0f0603050a330b0103 78
    0x24ac4d815003030045100ca2620215000b0004503980d4001c800c03508000c108040310707080450700040c01c0c3d403207a2940c000c4c6603000b0740300d070b004142d5400400c0b250090340440c03160200300045221841c402c15000401c2c0100b921902600c0290744901ea0000d4850b00c510024010b03040c2c015440030b000b44071650749000000040d501019112083e51091130340355809640400d0f100c90b811402540c200010541041c94035070744800c40c0c181c49a04588030101600402c0042000f07041c01c1c01140d501c50501054410124295038414a403c0d01403000607481400c0801c8950b203140c0f05000311000740400010580c3c880e06800002070180c186805924010302131110000d1403003900504450a40c1c00584401c1c240070b094800450b10819174641d03d0342081e00d2250700042d803850900080103a40d034510500d51010703058408620564002e940300606907454403000b080030aa003c5114071840b540b2901240c2c0e0090303017000716200c001d0100e50200040101060041507403603168483d0b11100b10a803000d122121118030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 377540485 1250 377539235 377539237
    0x50c030303070801180b1c0309090506180a0b04020304140d02010501060f03020921162c070908060f0f090d090513020f04030f0209250507020d02090702010c09080102 73
    0x250305020450043c018040b062821a0408292201c80d0002500544c19000140203a0f03404a00d65400b503454070b102018540d02c440580090105040d0030f00503410040d01041420b0043e0302c1322485034100c1c00c0811482071417604400401a401802035459081c0b900f005041d10f0351720039005500c0d10034040d84400c4540180211412145141c565904400c0800c809902a61000c80c0f6503030301150305084035280c1e410807024034500750300c100014880c2c126181c40c0095010019001403030340d004816005d495490b042006c81c0700e00e994032000450903458420045c0c509420a810440c10750161000b003241220915044910034950040070014a40f06c82e42440d0700c0c0c1c000340f8000e00009000c24070600c05424010071a0031903101c03080005280c841030791411000360700250000c441d1031030800b10460a40c54038600068004030728040324440c00f0480d0049402840c401d8001c0e2060000c0420408155541c00c5400c00c01290040c050b042145020017000b4000d09001070910040b450702c0c0804509480c0500c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 377541735 1250 377540485 377540491
    0x23070e150303090f12070303020d1215031113020309100b1801050f010903060615021501060210050c04121112190609082502010f080708041b081603050c030303 70
    0x5400786142075241004e1140003075941c1041500501e007514111404c51040003000d000754000e602400100d104a00001c040d003500042d81c0d400d031400c03d44401c00c2c0011036174810080f6a8041c402601840494000c0384844e40300c00b000c00c0741c80d1320110412003104004103017800410024442040784105000030000031007000105164920380c220014082c900b04a01004542d0303005050010002c0c0d40c279070b6900d054400503003000c0a10283c1008500d00b040d01085011850507107414403611540c1071010003952501c490304d10000d01511400802e0202805104a03030103030a4140583c0a00d0a490174022008003080321014003806c240300c08001150804200403000c3c520441080c50988030b242c4580d00981f0003407000b42c42c06c0c803040141c410005200e000e0903260101c1203903141c41000840c000034083c0c03001040e00000707000000d002c01a8103940100300b0741d402a44000d400c031007054039407a04c803902e107101c0d0032a0045101c3c0101c4903502c8010800010101e031701c24800c440c14483c82c0010b03d900c0c0d001c19 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 377542985 1250 377541735 377541739
    0x70f171212060f180a05040321090203160b030a0506010e06160b0609010605071106040e0403081e2206090c120b010504020403030c031b0b010906030311010603110d23070e15 76
    0x1040361707a0700c640c114542140c020700c1c05840b45a290450501d210141190803901c05503958082421030078203200c03441030101400d00300004c403442e00c6081440ca1000808500a0035030f1390300007901a030b009040180c107415024000320b0b12220318a0302a03011806650040d22121360b90f0001800c140380001d003150582c4c0440d030b036060503c040b9648940b801c807440700c8038a900003010f1001140c03111082c9220751056002e5600c40b10b0364100702d0b01c01c0c511424481c00803544101d0440c2007015000075200d1a42c510a81859071030039038205170906a00a1548450007480382c5c60302c00c0c0006030041d0f60100038861600400400e040f6980e144200412407045200c0240400c03c02c4101d00c021070f01500340710342e0200001ca502c0203030520541e10180072076826040082881c0d5130b6081841071591000d202c4031054520b1000b000b1150a6843c0d21400d40a00c42c9143d00c1598080610740030000c441d8400742480e07609401c21180751800340303240b1b529070503640140c1d0b504140b41d400103001c40020407210300d141480 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 377544235 1250 377542985 377543029
    0x60e030f1c03060503030a0906110606010f08070203280e18131b06020a030e0102010b0d06050903040f170d230702040905030a0c1103070f171212060f 66
    0x445142001c14010340c0408091654480c80000c1e80e45040c001401d81002e6a0f407034075525424043c000d88204105021300b10598004800c114142c0d0f00150f4009202105083c030100c81e1383d4400049256108060901c211204940503899040c14100c2d03882c0010740c0d0640710540319658002c03e000590390350001d0f80748803004803004154ad1110b0311a0124107940201119001d15140034a4070403000030b43d90005005a2040181005166100c150b1041440091009204550b5550300113000700c07002510161215655002040c00d1080c1001210010701703040360f131266450390b00c2c01d4080c0311404181a0380c20307c7c0100c04090311074602c100300d009c2c40e644d00b0303001040b05820308602080c80b98001103412a00035640c0d00362100411400c1000d0a4811031650780e00e521641d840c54012246610b2444682c000d512802d8140461003c0d540c64400361030044101c02140d007100c0b010b031860410703800f50b5001400b1b0f0002c3e240302e0260f402c445062140400307803102c06502c1e60326030611820712420611001c0c0e40034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 377545485 1250 377544235 377544253
    0x21f02070e040201020703140601180501050303030403031e061d010e09030304110f150c010b101b0f0c0b0d060b0403020a0e0405120301140108010b09091602190b01060e030f 76
    0x81c28555650300140180b04690410b40c40755500c0706225088900c492455000c240100701c01c0e0800020031258507811001400154174010110303a0340e0001401c01400d15031903180203040c4128980a82c1030903901c910b010300110390b99084245421080b00c0c041801d0038400ca00128074001d04c030b000785018804a1004502e15542c1d43c541304a404145035009501140c1c0809a140e640c0d22101c1400589161013481555100420070303407800c460108034011702803500c00d003a00e0a1244c108000d045d14100040c1c031008114514130300101648011074005204401c404804150040c0c50f2010b0008142c0200082000c1a240c06144086c0d0045d0f200007544410f1703011061007a000072a41060704103105104558481d1003010744040c4581098010034900000070480010542e400138034a40104961102c04d481c101e440008142d40076401022007a400001400d00100140308118050381c0042204180c0202c0038a4682002c410b80280304d00e1000400b6042074008a18001c6139040200401d0310091400366 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 377546735 1250 377545485 377545499
    0x1501030c05011809060902180f0f0103020702041112040302070e150622060e03010c0305040c260d020601090c0206071d03070906080105071b0b040b0c190309021f0207 73
    0x3410796070342007108244041c0d0006903000e8602172403015200035480903840b0b0503108040401e510b5064a0345104140c601a04e42454031644900f00c4514030a21340540c6e00d0010740003040c05804004c01162041c140020041006d8500703070341c20b03801280320b6800e4845850303640d10350501b9040242d40c01000d1301e0f0082c00d5074401c0e00d03001b0700900c80c0c07104030080c0030600a01240a80c010250781e42c04400800e200501c260114035080c4035035413240030b19003402c2140d41000c0d140d0244100e104c0c0110141080c1035080210b00c40581d4408041242e4100c0464111645882000707498400a1180b02d1800b410080c80e110514008620244210495031361310a10a49001282d40078200400b056509801515400f04165050f03001e0f1101a081c010b00101d040d0514620044c40c040c5113141148045a450500c500081d60b0b45203100c0d00190030480a00143d1100302c1c86540f140b003500c5103496603040403203140c004070ba059000f40c036060303000300c40c42c44090440c040041c0e0150f0031800f030b100c010703044108140116 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 377547985 1250 377546735 377546747
    0x702120f190218040506040b07050c190f051f060902030708070309020a05100216060c02030703080903010b06040929012a0b0f0a0f020a0c0b040f1709031501030c0501 73
    0x41d8001024840341d400614811250208242c030185c445030048000c0106011503001d4032a0000050710340186008448805107844001c50b031150058080078000c1c420070300c915042c800b0307940c541101c2955402d807018400c810b9403000700c0c5240030b042e030f00309000020303074448510a40b4814202074a4a02c81a600e01004400078002840100d9222080721804a0b0603200c41c0c00b030030001d0206400a001c241400d05080e0b1f611200c0d07600c201c0030410b441c2007190040c0c0700401c1c0301003180c0d0701090080d200c00c050b10000380076220070000e441d04030401040014070200c030b0f6004202c1c6c240e0902046c3c600d14856901c01940454811007036408502c95021810060302c80c040380803c100f10380e041600c41340341e50303039074440350500c0c05d480911445ca84034080c0031200300144110a4135a41c1d010003140f038462540c0000d4600810000040d0054105400040c2480711011507a505c03107030320810742c1025900d4006600080d801a101e171501a10400000303541580c520580c0d54142c0350000c003000380651400d4011521 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 377549235 1250 377547985 377548033
    0x10503090a05190507080106050d02090702011b05090906091b0a020c18011a090117071806020607021612020f1516140109030819140c0702120f 63
    0x141d200c0d40805001041c01401404884000d00ca003254100c0300c9070400038608412a040024507034500041000319641e06040d44005640c103460070070079030341c4040003030b40100980c229001000c00b0a074401c59682d80c1c008002d00c407140d03040b6070314030031910344d442808400d440031a80d1015060b00c00350315800c9030720042c0180440e0242c3c0e104941e100718020011400c0407812100d44c1030719a074140c0060000801d40142d25503c241c1d000483c0342000541e00000304410765080000d8a03002c0002c002c500320710720404800c608111920940b06460743d5919000790b40b403400300d40d04030060061540034007000e10b0150450044030328003c651048585030340c00304008606030020603940180840d07210224405460050f004008680c0d00f0755440307c07164144480e02d44140c83e205401640f402242074002500000b01f16040195406448400180300c074840340140340340d12040351086414410440080c1040c002040d01c40d200b52210715800110900841c2c1d074918001584a05421030707140b8407181c40c254072203151 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 377550485 1250 377549235 377549251
    0x9070f0f1d04090b04051203090c090a23041707020a170a02270a0b0603070f02030c01020c030c0c01020a030504091a0a06020a02041506271706040507060905010509010503 75
    0x31100c071401c40020202c0e4115001100c1014981c4100000e01a00344a1030752007410701c1e00203500c1c51501105d0b2a032030700c5882035020300c10000300c00031a0000c40580c0c001551125200107900c1190541e226002034824100c500320741c01c400f0740d0024030251100f2816640180c0d13000c2c1000305428200f80c00050302c40c90402825410344650400900541c0c1d5582c02d00040505280c04082c80b21400ca066048032032004080a4580c0d0030443c803000d16403142021a03a0000e40c40c605003010007600e070004c81c150301c00c1912102d40c039030020603242203291011008101d10840300c4102e41c004864a40166181c00320008007a0210700c0c2403008000034103807a046036440302103007880c4144d00021180010706025664000f480140e120070011340c2107040c280310304800300c0319000d92500c8040c1b615100900d4586811100366107910b460352994240010b03500d00c40c0291a109113488a103070380502c2c11981d40c200c03c54054410f403058880015034140540c05083c142d41c0e044c0d4846241008081c01544d4544c0003070f200b60 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 377551735 1250 377550485 377550527
    0x705010e01120f111305010912020409020409050f071e030201081b1309020d200901030b0f030604030c0c0f03121b0f031d0406120b09070e010e010509070f0f 69
    0x103c2402c10b1181508400303511000e980c40d001850400e00b0364200c00d801c0103040c40350300303107040c0890010100240642d9a04903400f01d01120180302017405000c0c156002803180c80380c0d00b005d07202d4000205403d0103880c1040545103607001c2d1b41580c503d5484040c880680414a2500031031107440311521110303000740e41410341c0c620b402c68a40700e00350620500d61060a00703541c0400c112a041050f4041c00c89070b002c098003000705040c01110400780e98454203d03001d05055640c402e95580c0d450f1104800f42615000301541c00d2440e040c2000f4041c41140d40d811036450481c03003400314007980c812640a080d00c0d02301c0b00e440c0000018075070940e061410344820304040203464078100000780081d40e00d140081d1095407844091022884140e112000610341c0c80e100d90b04101f402d111000c10740402003032041c1c02c070411020580740c40c03040e1805d0403099008000b030300300068008515928902d0034103040b101c040d00ca0b18010751706c2903c201c4140c4000fa00040009028400001105110f10f1403000034850b102c002c8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 377552985 1250 377551735 377551751
    0x50d0e0106030f14190b1801150e1f03110913030c06110705010f060e01090603031b0602090307030b1905070c120915020a021509010206011e09061e05030705010e0112 73
    0x41c007032100824408a4204c24001c081011f60803509481c040311404903c02488035419004005000340c00300c0c02102c22500f1520000303822201c1c103144241d004240107005104803034807401d182041c0c006265420780925920408074401044048910005640642d10503e8075860703952640d001e0405400740d0b1f01480c00a01001c40801c80a00c296106003500354000950285012148003524a0507400708025503d0700a08001003a00300c1e041411691444602c00d00f024044d151002c020300400703502c541c1510500f2804010040c24842c3c5034003c4c55015808644600e13129081070039100304a4032100081c1000d50048001914000020f0944100781001a070781900c0304074266000e0303140100350300103902080491095084c200b03800118504202c0480b0320f0034a40f5000131b5561031040c4100da1004002890b40314442180c006224060701c48030000f807107003940e0707840d00c01f8200c505821140a0780c0105034001546140008104c400c4500685810304540115001543d4001d449820010320031703194542 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 377554235 1250 377552985 377553013
    0x3003040512060a0b091b030c160f030318151d0609011a0607051f0f0603080306041b0806061305150301080d05030f0103020f0d050105010303050d0e0106030f14 70
    0x200054802800c1c0c01070015150401945040d0303100b10f4121405000f281e01030188500c10300021604114024414698036201c011032481988284503041b0000700d101c41460b8100104d900448007038900030b035428085903c149840040c41002d410000302114a59407003e131410f940b0b038010180205c1c4084203100102d09802015040c03500c00c540c011a0759544800301000903420324000398a0b15800d50b0340c80e04000304c41d555140d542222188841c1041506083c51b079522803940c06c10314612650210070f0040c1540d81ca02081c003a002500c4451241e400c205a8685850b40c0c50341c500400c2006944024168031100144425036200b141d1440079420f50311000309141d11000c0c065022580030710229541c80d854060300b6402c00008258820411104000b800851403070501c00d80d040d81d0301243c0860302e020508002075104502e18400400650170b100002042c150850068030424035007038070500c640745070003505c5803c0b1032311404003c007255409041c40010512190a02e40c03082420001c0320088000d4042d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 377555485 1250 377554235 377554249
    0x50402010e040504080406021506060a08040c150906080703450b0109140106080121120c1101050723030f030a020c10050c0909040501020405190302090630030405 71
    0xc0d090300d403045c0008040154540c1003080d401100384a1501c2e180c941801400038040d4441c18805c042000b90740400b04003440740d81e002d05801403261400c5140c0d000c1030040d000e0804030b164420361001c10000c01c000750515000780521001c01070305101c100700d080915002815200101c0c69986100100740402c461221100d10710111210300a111a803015894484c15105444030310104104420041004124070303078000c020a03040d43d42c5042d4401c9012242c000c903003440d118002d03020380603c43c607000706d080302600039500d45003c0340a180803020400b0620300550b00d521810000514000180f440c0300d4040790704201c111200c260745000d9070700d0540c4200680b642e90f002500d0795030380c9590000703449100368801c0020760704c51302c0500302c14000341c504225101e0660080c101ca050142074982e00280030080c0030350443e80a404000d1104030220141c80800071000c420740012400bc44007600800c0342c03468401d80c41011340106e0103224400d400b0300703074141d4038589042c0c5000a4910007480041199070710740e8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 377556735 1250 377555485 377555491
    0x507120f0b030606040905030304240c03090c0f0803041412010608280c050f0a052809050606030402010c0602070804141011060c09031504031e0f12050402010e0405 72
    0x4801041c80820722080500b00800074003030034410b5103030a914000064001c004d0300d90080d000254040200140b200112440b050401c500341c0c1d0600d81001130841503050b034810074059001d03800c1c2410503621092018502c4046000307185040d4000d00c41040121a5428481e0b40700101520000000024520080c291040754011001c0c0380c110020112114486801c0c42a1004811800c08100c40301c9844e0f01c1c581082d1405594040e000c000b11209480e103c544122004184c080d0010680e0003000003c1c0b502c0602407507240342094105180000c3d8124903000f2036010b844020135591450f160740d801910b4450304900104d41440c0c0074023440010640900207000200f0781d04d41e8102290044e94100071501c43c420084006016200707070320740300a20b40010aa40d002038009441681c420308640001d140102001ca0b0920b182208010001007503400f100d400480c0b105a031031049000c0001805031202c0580d8203c8800291186e01c01e8044028660003898200d801810130b05c0444501c2c50114042c1ca43c00c07 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 377557985 1250 377556735 377556761
    0x503060108010b1005120403050d02070b010305100b031c0e03120a03060303030e1b010509030f0a050312061e010507031101051e09070308030604020702010e0d0308061f080a050712 79
    0x1d224480f54608110068140c60b0200345051307494141003c00500b003040028201030100140490b4030410f02849604943c06141c0084151b9107960b03607440c2407541d442002d03404440c40b9080c110700107100d04000410300d5a0400002907040700700c018540448600c1c40041d5542c0d170500c40c1c0020081580c00d0340001701100c0141d03545c081060703402d600700503040d2a900c0c5c071a8030885c0d0005c480100c90048513140c800d40310809203016569080c14000013854a03079607001014490094030070400400c0000801050740d10702e21884210346540700700030070058620104540c3c941d0715001d880156558845c10041c1200e500c80e040c42013903031652000036801c48034200e5440003600d502e64075101045541c2c00c1c280380d004012400a1100d039003190b403044d54a0001926003805981c000c5248811a0700418880c001c0c00c001806c0410594501e0030300078203014043e50701f64015604103000d02e1034007682300320003000c142450f1181b40322511809003110003003400505207020840f4848150303220f50707403501071105142c440c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 377559235 1250 377557985 377557991
    0xd030216060c050319030b1012060801020c15040303060e070c0c08063913031b141e120106060207080d0c0b07030209060d020d0b09190b0a050306010801 67
    0xc10462045000141c01000c18004034141102c0024400070071038149a02d5241d03c1c101a40400c1c10580241c10450390b0598010111260045007036440f440c1e0781ca0745803546d4418400c10741c1e610f014500702c0c421085402416004240c899090b013980c044002d4000d4440c1c540054032540d910401e503000c0400f502e001d400144109524001d20944204000c007070178015000d4807040c10115980d50b1a1485000427150f81c00c810710130b580c842e40240d0a820340720900c2d11140c60707507180f1040400309062014001220440901c1600044e0180880701c07002c1603940e00000700b801050300e102007102004107805044076250164490090b030307468040606031801520b034004156541800c1c1c0103030412030f00e50050700c82030713006a507018150350780300e915000c8440c0c1010070020b00782ca0f104801c0f00a886414001500403000088045150b1143d9004211103800080100408000841007084003903056503825504c003100303480001e14100b2640035040055004010311415661000030a00380303071090744002d10b80e941d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 377560485 1250 377559235 377559253
    0xd0209010312050403330510050d02031f02041701090b0c0d090606090225020306010b0f04081b09070e0f09090304031a0a06060516081602031c120204030b0c0c0c0d0302 74
    0x6d1500910900f103443da40c8180603501c4c1081450076400058480d141c840e211100c0344105544051103640007a5011064080300601c0c0d504103c8082d6016200d04c100402080610303030080c400620903030706210350042e4241c0c416102c0c030107031120b55003100701d15006480e61807501000252003845904c00400b0740b98809602d842c245a4028424224030301200e811101a40320320b801030f43d010996505540019143e251a01284614a01c1d075010b180c11000341489100300380385100c1e2011014650300c4204540207860307036480000445400070480051034002036120700b0303407038145801d503402c03544505101c084034140340d502c0d100c00f0715030440480302c0031a15000106001508083d030203148040d150500340031346030401d41120101018034070039024019650105018550708203031002d14150756001400c44003072400100128040c032007000b0303919003c0707080d1000700249005c041c026201100c1e0445001b510b143c0e11042c00c6a201d60081c1c0c01012540540c0050a2180d40c7d4943e400c03410074083c1e401014151 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 377561735 1250 377560485 377560553
    0x5060309060f060303070b04020607050f06070203190906050a0c050c031509060a0c140c12030f0f0612030706090203010f0e060a0c0503150d020118170c0d0209010312050403 76
    0xf401207030280d00208903d4020412a031084e940142c1c1c10f031060342d9a1200d90078014140000c00c141c0c020203010382024004102e900102400c3d00007172642400142041800e0140c0e244c080912508021910902c804588240039601e4806180d0051007a0f94000003003400090074081d80124003809181d02d0010301c0b4020400700062540501c03841c000704026909074802070400503a10391039540c009400984013000031024414035902c10202d0401d00d0300ca00303080005025001c8110703801034400c0c1c6040b00203510ba14050342008905240d441c099481c2c2112a00c03800c000c1c0003600350590305592906800681e0b00ca15218192003524200041c02c1a428a8903001c0700340c40310750304100108503050081c40f04c841c60301d0140c00c258807000c5519284048061005036054a11600780c0d400d8410003400014100034148803507903800030101c0a40c0d40360032000c03082000c590320100001c0d40201c2000d0060000400c550b481e40900c2d1441e04080b402e0030b80d81d40c0c0d050700d160485d0403420705102d0301c6402d081c004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 377562985 1250 377561735 377561761
    0x10c1a070323010305070b0d0605220f0605130c0504150207050a061d0d0f020d0b0a0e07030819021204030507030b010b09150a050f1204030e06030708060d0204060506030906 76
    0x200701c20020b50146524540342c4569071215030140c2604810009003248030000c1d82d600c50401410041d01c80301c902c40c80400da101c40100700f0141548182d05209070341d41103060605c110004c1d614000c16400c19802c0c4070319104001d0070202041c0c4107000e000c00c800300e1402482064094900d840798001d01c0c46a041800784241c401182d030100c41030001c0c00d0304d41200e0010a00444507408015103800c00518481d0902400e4440c00d882c000e90403035511804001880003200d052803082c070304404140040f14640b0f801ea65222810f00c006441d0500034000c0c181e004074420032406c2e030544948102d501420005800051551080d8403c88a41d03114800800402000075991801440800381c2c480c10712a954010641d13040001032040c80c810300000317520140c03901403004c0d070b5403c11403000c40342d490381c1c42109004082041550150046500581c50403414504142224410000d640d00c444003900c510041c00040a86541c041341e1003502d52401141c10345502014503c5010101e00034072640c14064407001c02 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 377564235 1250 377562985 377563031
    0x301090503030103031418010c020a091a03010518030315010c050712230c0409080d11090901080c211507030c0806100e091302030111070b0a0911010c1a0703 69
    0x280c2c6c00709000513410b0303140003010742050701020b0070049048481440016a20500798001fa0a80d9192900b0341d45070844203142040344101c00e1300200304c140c964420b0000c01d6406c1407907640e0194410000212a5612203049052070a8107040550714102e03988c1d566030800c1e2040e04107a6164480b464041c0500141300000c440c0c03130301c0e130b921054042c0c0e00c2403020b02c0e01c562402810901881e00d07522010100120315044802c10040080f0801c04800d10300d0305103100b80c1c400082c092241030000004258540e01162030032482a00520038407400c1c025034007011600c40c1c40c1c01030320143d0140011840803442500c1419120f11700710358000a403a1194140504000070181c0b00310300402d41503101d00324094000b0a201c074603550454003032002d0b46d01c0c1c00c5140c00c00012001c0c000e4055083c01e500d0140001204080d143c940e03c10104c0000c19611480820100c030307581c0030050405071582c049243c40354005d5510781d410900440c50082d0110b01d561003c01d1032401030324030344000fa603902c14115010450b0b0b960110 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 377565485 1250 377564235 377564267
    0x307051c0c0e0915100207060e0411070b04060f020a09060f0e01051c060f081c082a0c01060f17010219031d0d030f0608060702070b18030109050303010303 68
    0x104581c03520500501500842190b42e0241040700045120700b00c0130039841c0c1c1c03c000000c126942d0f511828100a4030313440d0314440e950101d151850f5006040c9001d02a0701684034000d201301e03090007441d8503400340460f0701400c2a2440703695055130340c074050f0440c00203000c0c1c01c005880ea1507003545003403001031008008030078441c2040400c0d20352001c83d1780e00008072903101030401052803500401c0c281140c01000564003a5035020500b0600041c40c0c0c0740450002080c0104007015000380c00324800644403407504541441d200c2c1552042c0e0880e000811069042240007440018102141a00c0c8142140c610350400c02d642d003004201008400038039210300c1c5c2e4404000c8020b41c10700003405071002003a1141c880d140141078481e110700303640828401481c04000301c0001110703071044017880003600800c2035481e4110264202400032074180c0000881e03134040d424681c01005070380d00c0c181b24107a11b0b420511070a5003151000300c0f040c00030f940900071452402d020344061030b6254275603d0003a11028041c00001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 377566735 1250 377565485 377565491
    0x12010e06130203100b0d0f181101050d0f0524180609060105130b040f12030f030c0e0a0f08100b011409010507140607140c120906040801020307051c 65
    0x111040d1076100c01c00c4003103818030701c0c003580ba074407050791840113888a60407030f5207405000f0030460104480c0790404001d90040c2036041002d17004001d40501e40f90605103000e032404014510a59282d4450f8009000740003040400141c0040c8604112007951020740300210b91081c01d1151403052051401c00c12052882100c4440c001c54500b10720228662004040c40c2c42070015800080c0c1c264052001c8441146800031800402901c070410ac082a40040c01034000c00b1300c1d4848040b9044c5002d0703455080c140c1d0140c54441c0303440b10341c0348103e002c0c2846011190130081f170741c1c80d02a0661a2403980001801803110388114013801c1c000c10510304081d00a08224160412002d82c4141c1d82204584a5407002c01448603598500000140c4181c807031804000d28003080c0f0241003c03410309c0451554042c1d1100c3ea603040c10507010070404001802074100030030807034124100500d401c0b4025070040c165460082c11a50074143e0300e42c511400c90300121201004030380d00150741032800044c510b042059040c3d0309070030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 377567985 1250 377566735 377566741
    0x30106090902070203010f0e0a050c0307030308150109050a23060f0301030209041e0308010302010f0305040c1205010914150903120601080613060f29310b12010e 71
    0x203000c8401031085015059001441c001551020340280651500902c828001d41005600c419079030002030500782c40d64080c1440311681071034040761503400c40ba05a078900000c3d46510b1400300c0134544000f51b85043c02a8000005a1a00c40f140c0710740080c100e640030115660020242d80143c100c80c00c000070320454003041280d01d508082e005480c107581d01601c0c00e40d900d65036843c01e06a80c6600c070b04103c01807000800558105940b101440d41aa0720030380c0c2e400c2c2d812507a07400c2034040d00c0042c0c40050a40c17030b88070414071007400d80382507486d11a401540042050340b05602c460b084540c42c1c0100030440c1e00f00109040003241031500440c0c101311010000c0d4580310b601800c8440c40c080183c070380d904206140010848130390310b0409107080c0d43c4410720201b002c0c503511070100c40d54841c280b155450092601112403104441d000c481d841112201c040c061820800340000204501075103100320441c01c81800d161603a68800350410007070800d614100d43d0312416801c1000b03880310160f020781c00754181c400070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 377569235 1250 377567985 377567987
    0x6030b0a030f06180602130906051903120203090402070507090c0504120b04060b060a030e0c0103020c061f0e0a051e33060f071e0f0305181003020909010b030106 71
    0xc180b404640022001984078030140c4240c03c0000140406040c0304d001050076019103092045001c111860000c0030400c0c507a0301d03010300481e20303281400418001050501000401e6698814005143c02031040e80d10308841c4000003000c91b044580300f035a050f4040201480000005c0c0700d1049080d0150903d1802c3c207261100e40203904840c2c000041ca0081c2e98000300d0104981c980245c08030010081c2500e0301c0d004c00c020010010012405207500390310400d4418110ba50181c800c4400103c0250094011a5100f04102c900444140f0300741d560800d104400141c90300c0d0100445000c0d024020000c1100e040441c06074a03a403c2c0d503411403024003160341c107012203254a804001242100403401c8032a50194080c0b40c0c44441040c1c01858202c440010f0101308081e0040040007200d2148a203914400700c6c1000c1c1c203a441e0350429000b071482c011710a01002083c003030b00103050150b0fa8200c0d02d50060525402040148210a0b040408242c01050001c0340340750a07411103014160f000070303150543d890050 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 377570485 1250 377569235 377569253
    0x10e0c0d02030615012010240b1b1516090b1801181d180c06030c090a3309150302090907050408100b06030414010e0f0706030b0a03 58
    0x3c1c001003031041540b50489034019101038600402e0710071911868400e2015a42d1160b84800e41981c1f01c41c03421004070001204061000314050400c68025411818580031081c181d208101d2881981c801d0b104480c99000300704184e03881c50310804508200740c149106182c03104c03d045c00703282c1d05000c0c9240301800741404280c03e8450403c00c08600d442807440b40b20040e01e400c1024100509009aa0140842c1802010003004140c10010f5041040c0da5a410412991484502070741001e42e085826071071090310304500615004104a110035140c0340c80c00c0c00184414140764860001c01054000c1c2c28107000918151600000141d69024504420030200400070744203030051810345140e020f0902c03101b40c03180d410f6803202600070302a4022400c0c0044080c000d50018401c42580f881520403445074013007940141030180c00c010701890b0840d191541c91000035058921084d0b002d66030795039080c003881b00030850401c2441e030000c080c141407401c0990041c19030b44680122802000d22640400004120031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 377571735 1250 377570485 377570491
    0x7150213060f05280e04060303030507260a050c0c010903170901020315090a02070501020c0a0501060b0a020d0c1e0b07180f090e0316050d09090b22020f0c010e0c0d020306 75
    0x242044400b0b070540070341642c4c4202d00540051b00549054404803c260b01903211501034012515403459100e01900c83d030116802d044000d038072a028900106c3c040c40030942000d07030030480840740307a810050850113035400c4416443c41500020141c0a0700010240407150990300410700400035407035494012036403820005c1c2c2d14405809240510001441c801c85903054805d502d80c020002c2d50350301d80c1c0000540c0d079581a400d0582d180c2d443d0804c00580c44040c5000c5901e4038146401400e559001100107990300140350105807007048120b003e6141c0c91405140c2e09207107034410707100b22449061609000345a900d01d40800d0b00b12110288003402030b01c04406085080710904e04000c607100910031202410340c043e080001c0b8200e05c0111100c402c019000c1481604506242d0b20100b4107960b8800d043e058802c00c0d00b0064103c420740c0898607008100d45007145480b100d091000d49402000090b000595220b201c50b0710701a555101c260030720800c280150160100c00b01c82c069030062060b0002a100e103406 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 377572985 1250 377571735 377571787
    0x6210903190512150f10030f0218100903150903030207020a0b0d0e0304050a1211030d02250e0c0a030e03040603020705011b0824131b020a1707150213060f05 69
    0x71b03421025219400c041d0303601c200780368103548a07801c0081500d8800c00805c1203074458402517800d6800340740b2a1486c4d00480e6040b2502030b070025020100b4500401200000f9001c00d502001018003585039a6103140041003800549540d03078101c041c044049814600203070035150070030401009669180b08880081d03c041c05080c0c3c010358441e240841000c8052290140c060040d00b07500801c0580100d160040c0c03d001c080070440324103e000306281d00701224000c0002c034044000100329001ca1a5002e031402c015941800591080d40a0225103180c010360301c03040003c3d0700012030740d0420400380240c010090015194944a004640029091502c01400440b01030421032140c0751000800005400584000e899040a0344003049044060032020900c80d80c119101c510a04409100091030004690401051000b00c00c3e4000c900526512843e0180d44003014034032440900c10940c4006c1843e42c10104890f04082e1510a0260000d04410a0207050040901c180105500c01d010b980c00a1100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 377574235 1250 377572985 377572999
    0x2011104060f09080609060405060702070807360519180305030613060303050a0906020a020f0915220605011b0b040c15020d090506210903190512150f 66
    0x24401161403020075030020a4170702c42c00061000d40d00010030050300a5024100ba1a8540d0781c140040c0c0ea0345026100d40d6159511a05c402c215a00400700d05011560751420342d41071034492031039080c03083c0e08201d07011424513a0312000c1c0890000d0541c00a288012500e000784401c01840c54040814400440c01400b8003000200050813aa10320803926030301070003401d0420a04d038890400a09070340001c001000421404a07000c19003d000142c078a0745185e008200e00340d00f81c40d4500788054003901410454856215100c1d140c8181d0311000c22040140c8100302500c161281a0551802d85110794005418031241000f004c080410b81c0c0d00308410290003001c106e4050315503281001c145202d0303a1003a9005000b146101d916150b001c100c11000604503550081740d207031620704001e02441019010880e55814001185c01840b050b00328940c402495001d490404041e03c0702100c20f0603199482c2d4000a000240c8060f0741d060f002c49660b084400b81d0040c04543c103070340d004503105500c0c4a90031849120 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 377575485 1250 377574235 377574257
    0x3151302040e070e0114151c02040504090f020411030105030d0e06091005030f090615090a110a090303020d0c1505060a030c12030809060408070311070b0711010f0201110406 76
    0x2940c0c2c1084840001550803101d44584d03c0c0c60000780b0700300030b020701c0c0c1c00f014141ca208004c91500e1040c50359140782d07007a641803406036844e442050b4101d982c03004821180e003d110021f440e43d200d01c03603a5541801448905002c04443c410417080b80d000b480a070404030002d100620240e1000541404c242070720303003003103c81040004000380d010300411000b00c0c0c0c005404041ca0f0540350b4064061030040c10101c01c07990b143d45504420a854490450700c0340e192000101591506203001a03c06800c6410a00e0003d078282c1c0114240c0c02651100490b00003240c0c1e542000c20030503a0410004000c42c50340d00e001481e443e402c0d521100c1e0740c1d40408503802016281c102040c219660009054011980f04080c500b01d541e0720341c1112450140810103030085140240001c50b9548003090891003107901c251103c6c034051059605540d21010388a90029501c220070000c516417400000402c0003038000c0050310401d00481d00010700741c0b03614440d19411139061058210400030094160f4040d25004c0c100002c100c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 377576735 1250 377575485 377575489
    0x5060a110304170d0c0803070327230105040503030a0218040f0e07050f090a0507050423120f070b0d020705010f020c0c060f0406030c1b120e03151302 66
    0x4540400d03151168000010700003251a8580c00b01490300040d0003d4034081e40b03d40c001950800800040039207141010400181610302c241c0c1302000d142d134554032008920f50005980e0f4030741c2044007403c80c0c058913403d1401c18002590f02c6040c021680002c000c3c041450aa40c600d074590201030300c3c1d1314900b42c002c14082d041c0a2401c98101c50208083d1003001540034481100c0d001d0030320302d0080c2c031007070040903800b00d05424008004011240d020b48400d80c16150721030f55130b0040c4002444181000024400440c40d95004901503914151000142000e000310340b0400007568007919000516034080203003007040c25004100e140840d95001c2c00c4944485003011000044e1280b00e038010869482c01c41c041c0701c0c030b09856010304004806002150713400c10307d100038019181f00300f442818411005101c1041031505c2a08001e00300e03604e924080308411280403048001c51105d85013103603d10030025000e803a0b540c1c803ca610300501c008a005010382c840f9414100071492028001a120400e0f002d031000540d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 377577985 1250 377576735 377576747
    0x609022b0305030a3c151e031e0b010e0108060402040f0b0d05061b04080a0605040303060506120906071e11120a1e0504141c0501060b04060215010e0105060a 69
    0xd40d00038490b0102001100131904c8200c0100740c01172a5908810701c4200c101205110f03004480c1600314200099a06148412001c04002d00d44128a80c0350a20007000060b045801402c540e01c0c06046459000864941300042d80c00503000805525240c000400522900051041d04070384c0503140081d00d007075900420009041d95070204d907000032100c95000100440014218400c000c0123027005030b035002010003b0403a101d1449805015440707528a44041840380c6d02054019200f4100004e0702541c44000c20301d207400c60341c481c0b60109904800c21941040c280301d07141d0300c083c0d0f0b03180c00240c0303409409501c510154142c0014042040030320520a0303402c1d08101103210140900d030031307540390340400b90000d08500308103450002c803c4260400b91100c03070242041d50169a0782120068062007650140308114003440540002d035400c020014001c11000c0c41020003401e0b170081010f40d05d908141c006841d20402280b4600303080318031001003203056050b1010074151001111415921803001c0422254 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 377579235 1250 377577985 377578001
    0x140a020603011401030b030a21020f0105011d06040506150a1106090703020118050307090e011b020601290a05031902120601080f090d0e0a120609022b0305030a 70
    0xc50400000856586590040d2403480305090340d003446044245024580c0300c402a150050003450303500c07622442d428401d10550000d04192044951000889460034251a000e03803003502c80c18024901104031104059050354000f50545052005080000100d414040e50441e40b601d07151002c0b60f043ca080740300e00f250301d03180071421003200c1da2410100078058845401e440101e002c074910000f046404da44c030025500484200401601e0b4941c40c3c001c03400c015102d013080d41880380d581c1e100500081c1c644c0740b8482c2c020500c0c1e07500404966050401c0c001d803030020117120701c14010f186c00c5e80d06111802c1c41d086032800003441c90405c0d10303600d1b90402c04007024030740d507420440107001044d6152480d0349001d0301d40c1314000907618184c06441c0c0c10700240010200341d51202051304109610403010b401185440701108001c0d2114041a03610030880040c005805411201d131034484079000203626040440a402c0c000c2c520300703c03c50440d54402400e41d0b20010300000d091140202c001541c105507039006081d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 377580485 1250 377579235 377579239
    0xa02061b0405150c15010b03060d060b03030a020703110d02060702040c2a0204050c070302060402040b0f030708010e010b040204050108011a19050d152102040222080c040b0904140a02 80
    0x50f128000038000c20305900b02c240115001d111700342e10048002400700b40f4074101c2e40300070111491500c88d8000c1c40768032214440309459258603810080140d442c00c20092100840c158060a5070300d041d49020718003a00c155000e5841840d89120300d00240e0754002c212030072a54110350001d04241802d00988038020b00c9480e80da00000d6030300c050040200030403a803040c61482214100034541d0341e285003400c1401407c102074016403207107001070300504045e44044280c000c01891840e001d4041c000091400c250764000d1020703a5116030206190ba0001d01403a04a618115070075030a040c10500000c103500c40520030b1289104079001801103545100b41112480d003181a1050f4040014080150040e400000701c040c1192401d40501030f03c42611201c0030540d410092990070180400d42da038070940f01241010399000740e0800031300c00c1800b0284003103403a070401800301f41401440c0030400d5041c14851040a80220308081d25401d20355501150389070b00952001000100d100c0d000e03050380c40d020902d03000035 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 377581735 1250 377580485 377580499
    0x90312110927010803040e0c0a0c0b060f1003061e1a0a2a0b0a05010302030615010212030103030206060907090b030a092102010203100b1e09031501120c060201020a02061b0405 77
    0x124030703940c0105c0204103440b014410301790140c480d81d910803401c1c419580100b00081e40c000c0d14600240c4403410003608080000c00311000380490400180b480041c1c03860b82e1010030b99074142000111000d04d104105104400035080580c0e00d01b51030b803c500c0405612071109000002296400c440c0140000c001b00c491038101882003101075011082e140c02d1602c0103640d1312a040f40028609009401707114107813540500074020702c1d204c0d0f030f402d1024640703a000d18034103501619003402e000c28844c201a41c000c0d0300a07801081c481c1000c1b001d000002d80c010382281e08101d8080c2c42802240030b800101c0c0e030025200100041c0480762401c24030b5224180440c000507403500c80b00c06142259054001e0740c040c03107030100c2030140c0d2a82e0701c002904500c00c660f00321224510b580a110191040d0f080a0810083e0190a8074501c0210840d00340d07442d10260040b000722004440c14405118072140b0711006040d050008500d810302d60750004e9696500244480003c44588040a03404103d100a8030300524003c1c01c48 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 377582985 1250 377581735 377581739
    0x1170103050321070c0b0c090d110901050904050a0b06010908010f0f360309050603040305030a050f07080f092d010f051303121104080109031211092701 67
    0x75449503c640e18242d0b81601020100381c502c0345018400d8004c40d550b45071030014090796903405210b80710040180f500071130184460714654680b401d00d10030040c4540014a00703640b0300c0d03007084440c141c10703001140210b25803810000010b4000580e1000250040c038001c90558600700120f03010a0240c001c204a5420b0200c50307148601c00d500280919404044140495405803521a10000c18505ca03244440b807a25503c031212032071076135030740912030081ca804401544c1f0b03400424166841a00c003280001c03000401c2014141452043e960040450700711071900b420710b000020441c03100600340c5660103801c02d02289160310104200c1c079120311120036450603142c090f403000450100600001005500303200b030709010702c4050b00c165031207040251000d0302880b01d161411110079010300360b007005160380c1d4880007515075207500c080c1c00100345e00f600120301c900052030010000d11358000102952414040c00040b0610180240e4100710340c1560700c1e00b8241030803030940340d405a0304640a40900090400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 377584235 1250 377582985 377582993
    0x50c0304081b0c06070b06120c030a08031008070602030307021009022b02042c03041a0d0e0a06091406060f01031a040e0f15010819020607050105150a0f05090a050601170103 76
    0xc03c0744248808c40300b01604000751280251100e0001c09100d40c107400c00351b4400700140d000c4010715040402d0720b03480c0c08640e494451440c41c01210350440005640040101300030315604210600400580c15424890321200f580410900030610103004401d1034140f002507049050419224009074004000307114100305842c0005000244242126500b03804050342a0340c18000001c5504549200c2a80749600382040ac9607c0960040503d00c0c481907207984118138521820440d8042c00390284800041000491406079250041075a00184a41200c4100282e83d500e00300040c0300d152003824046076404028000c07250424540307000356481407800b080e034808100001010001500b10808662031812000c40c40200b14109104030405a84840361042d5904450444094024405803149003840a0b6954207402c0d00d20071103540402c21034500c410004ca1415828040007000600940c0000c1b43c24107000ca0580a0010800010f190b1170f80f002c94030507441444007030b450080e628481000ba5840b403034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 377585485 1250 377584235 377584253
    0x919090c05030d021c18090e1005070c0c0302131d0706030c0207121509150c26060f0a120b091b0612041b0801060801050c0304081b0c0607 61
    0x740c00d0003485071200511415000090f40411003010030703002c10403004500400c440041429124441091000d01d0009101e52280280c00500e84858003624032040034400742011201c1c010000e00c20811941071102c0400c40542082013542d4041d42c00603d043e244a0105014102000d04c2081c140c01c000102224003c01003251010313584165003d20240c480c414040782d42d07030124080c41500c1740c0b603941c1c803000081c400101201403400392000030880d500c0170344030b01c0200391289030829421903c50300d00444090307000900020400300c180859107203002c4008410b001c0d40c0c0c014540c5014607040c0e405902d841d0f9606051400804800444560300b031554540544007540940b01c1c0c0c03c0611514101000460b40000500600d41e0064191801d050303405e45900c07800b42001e0415151031915a45040c07002c0c10042042002c1d0500380000b09980386041c140d942120350003845000511814028813001400d503404688901c0100b00c22a03030415050302c602030a01030441c00040c0c0c801c200054450800c20001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 377586735 1250 377585485 377585489
    0x5030f0703060501060e06030c030403020a12020a021002120a18150c0c08010504080702061c1d070b0a05040513060803030f01090b010207031e0f0803040309080f0307110919090c 78
    0x51410b2043d640d8904054540b1445a500d0a43c0090103100260710710303200301301440d401802841101c01112003a00c44540c0f0042103200307000143c01224059081d0305041585044503240351004011550b00b04e42c0f80d031981d00a0148810420004c0014888800c0d0038400c08805000000348100482c004280060160405003400b03c614280c500e400045489040c45013500c50f80e0000d81051920306650f017001166405544c0955610740f031a060040b650182d48a6101c8110810141d010759210945185250920a80c0b04030b031002010000341c4c00455124060b00c00300c40060320721860070b03c01c100800000e090660817021310b80c0300100070094104131f4000803d0403600d09503004c2108600f050300498903000c0600002e405810481105440b00840040031005680100070880e919101580c40354a15441910250005541541c05101208003848445001440000110310344880340d5130300704901300c5000040d0b10401c80000001c103c5d00a03001e1400c4040401c440c0cc100781c06d0a8a080c181c086400c0c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 377587985 1250 377586735 377586743
    0x10605130b0f03060f0103090c170c12190c08010e1b0102031e0f040b18010207080601030506040b0411030a12030501121e0f120906030b180711030405030f0703 70
    0x90001060007410381100c46944070454400e10b10750701ea40512040d084101400c40c1003690759210040803400703500030100038054912609062402040c0043d1030032000d85000c40c40381030303a03484002100703500007904079400103000390f217100c01c07030060514519100660f4064401542482068000c510700828a090050385040b403071145040718800490780c0c0d0040942070b800c0c0924480ea442c0c0c14043c0f45000e888400c0765a0103003454030391a000480601d401007603103101d03042182c0454103020340c1c040c050407000d800c00c80010802c07585145c4038281d84250203031000c1c00000080c0301003814803040508003049414041d04855500030589042a5440c28039030131030001915000000c90501c0064441d00c070310b240c01a0220b604109480b08600008803c0017044401c1d002400024001619034081808080d44d6510b8809100d1300d0403d000e02940e138008103407440b41c0010f464110520036542e001581004580c40c10079004a01e540310301b840e610541d0840c0754188282c50703284000910008002e420b40380301d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 377589235 1250 377587985 377588017
    0xf2409180206030f073e030c010213030b0c250c0f18150f06110309101107090b010804032f0703050c0a030807150212010b09090f150409020604030605010605 69
    0x4250201e840004442c010700c99001b40760302045505a090512044001407040d0549280c480d4100000b400caa1050444000f1004421010001d00202100da164030158030b0b0003a5140c0001c400c083c14814442d0400009440007091040f01801024000d920140041d000490211501c40807082000f103440340e4040c40d6241801c21300210f02201941c14001c5030400001030900d039003810f04c02d0382e1404140c44000341c603100170301c4002411b9543d82e105820b1301c12140c90300d0303440041d8103c081d81402e00c290400c0c10064201b517490132440e42c1c0403088580c0250103242c070030300303800840c1e507040350f000b46a4500c15a03114a0103500359502c80e021500c001242d200e10b0860703006500901c24400451601d2102500740c0d1414031016020902504e101002c00d23004100041c42c1400303582400d4120700003a0442c0e03042c4140400c1503c51820300441c000d0304920180280c0c0840d1800030b0201d504c034510748500a0041da19011003204540780c000550340550b6102c1c205000c2c544c0c491074003d000d900708030182179010380 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 377590485 1250 377589235 377589257
    0x30207120c03021b010c080307030207120c0b060603041103070303020c330a18060207030b061c060e0705030a06020703080f1e060a0503010c030f2409180206030f07 72
    0x809480590790103903054024050701000d107090507440c1ca4118450906221400140e0341c001491040210b10803072841e28010303101c034403c0c10a15200002c5805c4002480307000c20540300841d403840d44466004804560590340c0c0e585606d07142e400180c001481c0303500340c8102040441015004560740103018002d40340100080040000400045015000d002e10031420280204040090714020080070110b403e18400268a41c041d5940c10340640d401100160044a0240100f1002c501d0190304400c0456210040c6001c0011605010829140040c1200d540d003242d40b020f05c1042c028080140130040071384689001904214000e50f1184104074006081c40700014402045da02d1018000c2e1401900d05004986c06540e40302c100307a001d00095031091880c580042d055500340501c000900c11944e0226010301a060310301c007a030300c1407088101c0c50f0400360303a000b17120081d03c00403c048030818078010501c00c07a00030072500c0755238100c10060b412645c00010005100741c480c400780d010f801c043d40c4d9500c0d000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 377591735 1250 377590485 377590487
    0x9060a0504050a050118091a090a0f050d1202040b0a110f010609141b0d0f060b0406050c0d0806031f1d0706090b0906030f100512151003022407020a0603020712 70
    0x7d600707541c00a084901c461034034038078501d04490306944021200200c80d411203041c2c85802c4a00d00c50348080340e055103c20b0380d0304c08055015280b084038080005c0d00f50700346801c1c940d0f1080e490281d0140c070404c11000d0340d00100040803c000c0b49101c04c58110017000401d40b1404114068100700712240c84481d548004207070700483c9000010150102c4003045820001102e85d0003024000c50004061090344500000c90a0441c0000034401007141d51100c5035249841d007002c60504191013035100130b01c600c100400621340c801140001001131011b424054287d0040401d2000b00b80003c018020082c200304c80840c50040014030070162005030310390020301c1d6a254041d5071144542c1480a4000c50148081140113035100c4400d50060705c0007a02018040e111808070b80d054021400b144200c0d4811000108580074130350721590400321122100213807a0550700401d000d603440f5118100c0316a800010700028511460584e221154011f02d8031440e1542c0c4e5500a0103034202c011b080d01c0d00e0b4031014241e00d00c2c03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 377592985 1250 377591735 377591741
    0xe0618191b02150a0902030d080f09010b0108070c051213050306010905100b0a0c020d0b1e01030203031b160303020105060901050d050705060901030e070f15080103030e09060a0504050a050118 84
    0x240207682c003c0c2201100400d1881180d100902600e5510352521160b400580e002c0c07081100e0041281d9600007145024001101c183e0170160281c1043c0e450b00d2504041e6990059000340c1c003000302d0402d04551440762a2441c83d02d8010562800c0d410400b04581c50901e04526444081f40c0d000c4007100c00300e9072a607a2820031510f05485007283c110600c1001c202c010710030800341021070061b0401c0712150b0300640100b440c0c2e01300007400f01c56502061042186100c80340703084144c01c0380c400c140f900c205d41c11903020a94030b1040101b42c2501d0041d04803110b0310000100250100c01c585142d20000c201d503245000b81c00780c00c06803045482684018004615810050b001c0e52000d0380240040c4201c5161006200959105a09550401d46c47c2c0400340c4e020741007040010003c0072000d131090b0304240307014005180011500c007000104882803004002082e070003d001c040c2540d085400c00750f6925948000b400c02e003481d03402290091305250800c00303042c50b00e5110a04940c5081c803000084010f00d8158011 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 377594235 1250 377592985 377593031
    0xa0209160915030e3004050105070212010b061b10090203031608160f0606080313030b0c040e0403030b0102100e03040e150402070b0118150e061819 65
    0x40d02816041140340c50401c2d01882d914241e0500103542c0350003095550130040c4200006490745c640c9045904088480c4400d90800900d90500a05050a1000091640c802e00303030080d00c1a0502c410180040c042940f1004200500030300c00c603a1280f603004542200010103400020074081d0b10300e0450440514054040c0b01c0751700a0140d46000848542014000c8804400341d51035541481003941c00b41c000952400200c0c001d407a00458081a45030981c142d50300c1b41c1260106401c1400100c3c82d401c080e042500560b0307801070b80b8075099519040f040d00c290188d540310306042400c3c0e800384418103070143e00c902080030003a401c3d60012070080290b001910003844c080041540304000c1003004d2101a048035400103401d4910b07081c2d8072103036800241640c1040c841690071440b104010003001c3c810003003031500c400741c07403000b40280f001c4000f48512000c0d60740724a400041545001403115034404540c48039103020551f1002e85403c001001032203005218403c2c0304403502d4902080c50800030050300c0c100c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 377595485 1250 377594235 377594237
    0x3080603010b090403030903021011040807050a06050405060304051002070812070807080114040b03032808041505040f050f0d0e010305150409030909050106020624130b010203040f080a020916 84
    0x201c04d88441d0740840040948010540c1140200d10a00b042d007102070040c1e0b81204418030a40d40c075a070900c0c404c1c90524046903c0349118880c2008100030740354200c0195003c07590102c403015184c1d80d031402c14905152202c00c4164106100003900ca0800501c00042c100c409078100020341ca80d80c1e2070006444401c02078801340c01041891004200e440000300c40b000b04102c015001160880506000c2440c58202441c03240385000c0c00c4000091108200603900021216450500418100380c2c40c1c1e10804c01d0340c0c00402c1c8200343ca4030002002d100c1c14501110001d60701070b0856100040441ca001d85803524107580070002207005072402c1c0c80758440d00409000f00c044000d07801e43c0714211810080100185c20040b4103000c2044d0b0002107403266481203074002c2c01d858019144900d4035400710b0b01c0741030f40d03c5409440d1413140000c000c41354403211300440c801d8074142400500d0b12038000040c1d1540c0629480101305614140c0c0126000101090f044960340c82074610720f080d501c3d084a40e07030b80d005851072218 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 377596735 1250 377595485 377595499
    0xd0b060903100e071d090c010216060c03050f0c011e090c052e05040905011508060906060c1e1e060403140f041403070501050a02150903042103080603010b 68
    0x7622811a0780300074460490f00003100c000320b50f20000313568030344d000c103903a007007010b0070380017002085142800b070003090305002d2014007203c80010071800340f003000e40d000c3c0108000010441d003081600038405c031142d15510114280e12061403600c0d0300d000e01820b80842c610b00c40900c1911300c501686005a0581550100d1610f041d5800d001c1842864600c40c1990001c445540e100380c0b005503903018030350280c4644caa682942e070350305101e001c10a584060b4030140c101c140559269592550080f14142c00c90400c9515602e207480e8040007940038007a14416031007030300516010400f40c1e0340709040d0340503001c1440161110075010242c3c2c104500c02e02058010180c00940c00100082d10464119800c8204118610b00304a01c403804161039130000e4024034481c040d054620001840d040103004014002442c20302c2c078040c80f850740203458102d8240341d21440c0b031211001c41e0b00c000d011700950b40070700003552a0045201c080e8400c043c955000715002c2d17000c03c41180118100c0d003010b000e610894280070b8000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 377597985 1250 377596735 377596753
    0x60c020411070b0f07110303010f0306020c0a080d0204141f1407060c03061805010f090213030510140f0601090311040e0a0309060f0503190e10060b0d0b060903 70
    0x4800070303000803401c0048000d000c0065800281000c0880c60041016005560645ca8003841c050302c0d907001c0b22103511280c0c3c8103000420802d041c3e6019102901d50103807000d40c40711074900a5138608a0444801080e802c40804c41a03a41541c1d0b034003810446800f11914031010079540280101e054030109515180b0310070190305030347e0600440b8881c54010104054600e090700da030701c8103411101026482000070b5124001040041601410000302421300c4000700265450007204090060692088209240e004521450442b002001d82002150002d0070740305c40700502c1c4058070043c2004440d8000201c503540c041401a070078620700710300c0342d00f040c0c4480615604584a5260030f4a52260039030f07105886440d55000000103000340c9c940d0520a07111521000d05140b00900402c101d500588200223050040269201c0219400c000220081000060094900c201d0754145005400d01f00002400c10000099a00a46000300000c16615004001030441c4008004003886a01015941136000f603100d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 377599235 1250 377597985 377597989
    0x8090603060310090501020414040e0a060b0d020901080606040507050c03040e1003080a020c030607180510140412051501030b0a0b0a0510020a06061502030f220b0d060807060c02 78
    0x103642011005045482c0201007032a508152841500304032a143d4010400b00702040c1d014881c5c03140c4c10401c40d4113200d8130b41c0240085644400800000d46100d0b200c00441e203858485440b02c05896801422080c2e1641e180c01d45999191400e03145540603501d00b5000942c0d4510074801d0711400480344024510700791500200c484196405404000c080b01ca04030300000007000000281819042c40e0080c02408003100c04050a1940042c0150213008010030003410500c9024280c4007a10002c54000b01c00e290b4522040710402e8900311001030071800002d020800296105000040502c035030102e03503d419030704245000324070080c84000c09010103000803071524021500b100722103134405032480e0502681d41002403248000c0748075003009a0008400c41080c820325015000203804258080749032815101c600960fa0302caa14002a403045010039840c03200e007815580c084640d0299540f1807102070f15100032091a500941c0e42602d6103207041c1d4009181400822346d5000c075403181e1070b03034a002445502 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 377600485 1250 377599235 377599237
    0x1080607081503030d02070b1b1903020c01020c010203010e01031712070c06110a0f1d0a060c06201218070506070311070311032e0e011503200409080906 67
    0x2d906034140018030801c0031040c0c40d031000d0400103000d0140403a59041c61400740c6c1c0d00c19401c00364a21810400c11100b03180049144003403010f27207004d1800513594008407107c0e40c028000c0301c0342080d00d940000b00004801c226a4170b410f06a9008007031304101a1001c503254007c1d841502c001c0c4110441507400102c10502510b142100705e0301950003c14500d0124801154541c00304c40746002041e038400d550310109902c0845050300741440803036a6800111070001038500c0c00c083c8100310800207202c1c1d10314100701070703904854a43c04100485031603882c0d02d070300e8408141d00982800781d00840801c0002e02c00d04814200040301c0301f009000781c68001c0c24942409103e5000742025400d0000b0f42d20700000741c0604104040086001e000c1020b0400500350415040c0354800214034203400f00100340c10240c40c1428050b8140c545201c00000b50082400e51a5000d011803542484c2c20000c1403c00100344220303079040d011034010380c0c061008028410810001143c69400014007980c03418007504485080c444 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 377601735 1250 377600485 377600521
    0x20d0c1101140c0a05032205060706050c0d090f0201110d2708060f04060c170a0b13020304050604060501080109051c020106050d03051908190b150a03060e0108060708 73
    0x40702c1c55140c1101203a15614204514a088549038400111110b5210403406440600d078100003c06200615090028013280a40b120141501d503444010510000c201012a003041c604a9014018051281050220601c10b0a403d0380841c10550070000c00000101c0d40c0c011160302c030b46542c00c1501c1107040a00d030080e12007400090b0103011901c0480c42c0c481c1001807600c038041d00c3c58144210b20742458004c05868941d0013050030b001206402c10918012100d48590080184034000b4214448000091081c1810303066004407900c00800d200a200b808103429100b14010002400740b40d9031815054200c0d9041c20005c0c2441d0002800c2c044011a9015288514141d1748008a5103684501c001003208003403110407404103000242113508610075180c504240c64880c2403804c502d141540c01e0a12000050b682404680d64608030b60405541d42e1481c11016601e42d21381503280c40340040301500520003070090301c0110060304000280102c0c009140341c4036408641d600c0035161038091041c4810420b40e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 377602985 1250 377601735 377601767
    0xc0d120b04020c0a110a0b0a0825200c030a14010b10050403060510120f03030603080417011d0a0308091f0504140606011409150706050601020d0c1101 66
    0x500c0480c516039107600140c41d0107002c0304040c1c40a00d0303031860845209a0301c001703824090400040c0400401c9440d90a6890700c900508040b003480d61030000c49202110313800906000414452010865641c0c8180c0c14000c03002c11550581010504108542d070b60605036584903499800034030400d00065802c0d50001c42a01d40303a00110300342200c2c20009040d80c000d209c0000c0080e5001c941001032140e107008030354000c1c10030444c1100361418100c00304088007211001a141c41700311803151042501c40d0788803070002c542002002e40ca0382c0c0c80300c0c2100c000c02d03680c600303020407036007020b0030007001c000001501140b40c61342000a00070860580c1d07040d98107140082522800303009151403010480c140b02040c18501030340030400240d5107007901d004d480100b4500100880b65011600700041d60340c02451200310743c449a20043c1c2c8804002001903072070140c404010710104004030703410017003001d1034000034040d0400340c083c0c0300842848582190f0968011102074803a09140081105650090030802009041 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 377604235 1250 377602985 377602991
    0x1f0c0804080f060603060a0b0a050d02010512010e0a0c020304050a1e09050103081b1b0111010216061d0307030c0b040201052502010906020a0503030c09030304030c08030a140c0d12 79
    0xd40c1e40304509290342030b115020340350407440c2048418542804010340c0101030310710400c105034400b00414000c3c0f0007070081d41d00940110143d41c06681c02203094035900c01040000b1100d0f07684130511958040030949114080a041a05941000380040306440907500003034258100b07145427020320b615080201c1100b61070140702d81004191007880303014a0f40618001c3d061181d485800790a41c0d040c030508090740e01d19540003080310075904407058410100044092824005000302011b04074024803401c1444d0039048460f0703203640d0420006802078050551341c0303a110a841002c0221503920b034411440c1c01030000d0680b03032170000040c0b14007503030f650070600614013142000e031a40f804401c54079152031010303585e114100303451045690060b15180a0010b074405004502c0a40ea0f800e69030340400f43c090440b400d80841c2d0707001c0710b440c00c0051342c004680201d40d0b00381e141d80d03d03101c05889034008000d1034001090401703030030305c40d04820086a140f0482c220041c43c5010060030110703141e448280e076207404e641d2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 377605485 1250 377604235 377604239
    0x6070c050f03040305100f021908070e12030324120705040f110a110a0602040e04060506041107150b060a05031803160f060f02030a0b09010e090601060c03020a08030106110c1f0c0804 80
    0x2703035034101d8a0f190303440d52115800e003820064600100c0704c02c031500c2042e03c07031214100e01d0400310550b030b0415510a995009541203080ca040285480399016070007800c00c48910100350300014001c4120765040e00e003004080c80e0303441401c090f41c100d1065038002050030800d15011a20645404010071024001e4619480080e9108000c1e41d01643c000601003c440c0107000c03c0c8681c900c50540c2106040790104403c012200c08000b0600601c240074101c425488ca50499844c41504603268411006082d6a40d034044008060032940058910b0705044183c040e01d400c5040740081250700721000800c00810744401c5507280d850074224150704607001525012858620b2070180003450007010108008110340b2070110a106032104142d202c07402407e50f44007480004980880c1c0c103030544a6600c0c1c10001d84445003402c0e40380403440300000306182400400007840382d03400707003100d00a4003000c000c0d00c20080b5000304100282c0400d5101040b0200103611101403180661610031415124041c240d00707080d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 377606735 1250 377605485 377605507
    0x609030b041b0905010503150411060d090821010617161808250f0312140a02150f040201020d030b0d0614160521130506070c050f03040305100f02 64
    0x71079020640c0c10340c0351350060040b482c1c28080046101801c61080d0f09070700e80f540710886042d442c4145540030700000034003041085059006507162a0308040da80f80d40f014100d40004512034865407000d00000e0302c0303001241d414811001032101c611241500c1040fa103440000c60b442300303207104680c2c09000c42000d60815600580d10190010700c9500040c0500024280c51b5845040c480c00740e0a01e10480d051090041c60389542440055942042c401202240c2d403071410741d000107480506d203480c4440854020700c002e50025180c0e0600070700d600da10000c1e0319030050361103800a0a030740c000e0241c2c01654041006c0c1c2e109a21900356050001c000b031200e10519241c03401100c900840e4030762800c00000801c01306299a000c105000482842c00c1494186100d448581490000b41c2900c540d4080d10042080c0250080d107000d81d031034000c41919024108a540904500348034a82207510b800780c100c041000002c04415a000c507604030b005001035003407490500004000c3c007000a400e065003800000342d10 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 377607985 1250 377606735 377606783
    0x11070203160302130b09040f11031b10030b010f030c022d190f080705030906040b0a02060106081302010804051207051b030313060318051204090b040203010609030b04 73
    0x14501c4941d8200059080d0300510901d00d40e0400800c000e01d0500c2c042d80903e0b1140c1d0107161344940c01c44240c2554510b540b03803200c0344030091500ca07036151180080508128400d13200b04500020221805011064090307019826074402c184d019022500074506c100e025030290300032401080984c416100b405441e560101007000c0901503441c9203000e81120520740341420886900c0061020040700100f44403079444100c191041c541c014850703080803c1701401c00000304156841c0d404020100c54031246c844d599001c9a0b00f0200c90040140719076000000e03d10b0059050a0203441005055503c4044903001903418090241007111184581a8010400720440003c1c00041e07110740050303c121101400c0000844140e2020103129400422017100c80b0803501d280d0008035211418003041120b441c42e05460304140c4943e010305a4082e001d01d084000740c80100610a944180c901040302c4503400741408102d00090003008082074103c002800425a440d0580340c0c003601ca4440d8002c01d0381641d038405c4503 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 377609235 1250 377607985 377608003
    0x314010f031103150a0f1a0603010b0f1314010f0903081605031b03090306181e010f061e090203060d080c0a051606090905070e0f0f030307080307082811070203 70
    0x921980c6e00060b0606c100180110941e14000c0018036a03000a9040017076450306c018418141d803040c0020380001011941025180d14001403940954219600d000487c040c4140342c4034980001c4010200300c5186d802070f040181525003040c4410300b022074113000f80e001500901d505135820321090100b20320400100c80b10280750b412074070155844142100905240c141c002e040303007425140300b0360309011031040007070821111440c0854601190340310111340307401440c100c25100d00d060309004d40810170800c00006a4101c00d0508240041e5030303079600301c10040380025a54158040201c102820124280c84050700b1201555010340d0360302c5000f83e032050314114450217420303140070030041e00700200c0da00240d940000b800c0c5114284128a0040001041050341660700b612031440178206030926155003042012494015040740e41c4d0b082c2c20b0512566940003205c1e010000341001e0009420146076046448803410b1a021403415090803099032405000b000360040c440c1c0700d081c1f00f00c42c00b682d020045645 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 377610485 1250 377609235 377609251
    0x10e28020912070915051f0302210a06030b07030603051207020a1d0103050c0103021c05100b0d05010e091606080601050f070807050606060a020c0d0c08060f070314010f03110315 78
    0x10352104641c0c111001c800f1680e100c075124043c80c150200f4900c1d0341c48881f2804e4165840d0060359a9401c5c0e030300f0920708003030048286000d10a041001184421540807005482c0070344141c9041d50b442e80011000c0e61070b6400300034096000001c5030a49890000050b24203e4802040140703555120406400381c000601080b00e8070220540042060120a00c02c1e1981d5400c01e1030b0551a2074100d0441200d20004020203102981d614000540381504c42d40522014103104000247d81c4d503119100c1202401c2c0038005c044140382c607640401d080340c80024040a00602d050f15880005250420a603443c04000381071506207c01001880d40e842c00020003000c00521a1620a8407480c441c10078502d0404004d1a4501588080140081d89500010b00e40300104080787c403a82074040350b240115481e120307030340300851902c01c01c030138031140c5906820480c1c419015640d08109800b10700310700c600c130f03400d0a1050300e90340041c3c4007080c00441c0244100030000c10000e021514000d600c107652103040314040714811 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 377611735 1250 377610485 377610491
    0x20c1204030618020a0b0306010e12010f0501080d09180e03072f03071206092024120403030b191a040f0509041b0e010e280209120709 59
    0x701c10409103100d020b0801e841e205074400107420560101d00c4074034040c043c0e02a150008000141c150307105070308174030b06800c01900c609000e044a0880318083d251002585002d40e04000005c07034803100020720008800803a50b100340981e450507100904c0c0380f50031540c4150154455001b5800c1c80c800b04000e00d9418882d00440000095000e400700105401204400000300450030307250301540c000401d5000e43d000d00e0f881c00100c2402c1c0c03418600030300b85808010189100c030316140c2030380303552121125031405064401c5a4450300e0100e9144004540240c5007500c1c400c14060710700300c01042c01d4415400741c400d043c0010600001000600056a00710452040c0030040000380104070805040540c908401908181405d040c002c0400000cad0b514042d6a008184400014007846220000041c4006400e42099401070321554107401d0b5034000d02074402c604d100d031804500c02907c1000e0717800e0b00f40d402c19580c10a203801c0e100c44501035400760580d1740d0f01c030710a240640c69400c41403200d40001c2481030000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 377612985 1250 377611735 377611739
    0x1012030906030c0503100b181305070207080a0308041106070605100f090905032d040803030403031a0d030e0103151e0e0601023a021006090b0121020c1204 68
    0x2020b641e00f034489941048410b100340409403404400d560250303401d4100b007a882d00ca10501683c1403c5c0d100c91030941c491807035102e18850805680c407207800740501340d00342c5903d984c80c0d5412598502c009000200050f6802c00094007040420a004602c0c140040c4220710f040d2036526030b5820344070180d86108043c40c5c07a1004000c101460180e04004150282041c0304001c0301d900e8194507401010f10300090401c0c540e0f00e407c90540b0720025640568003100d2070342d0b10342d91110b11a550b40c0d0000c44007100400c1c5420a06481d48820a00c4035240e050000d0000c0000c46071b80c0d030b044074203901400e40c0b2410b0646038500740c1440e21442d07903240003400c0352040d010003050506a8420740c01c0000d0f800b014404080f10184855a40d000c80c42050ba000c0d8400c86610854188100d880c0d0b0045452448005141c180c000748035565003c00d490300341c2c41a000303050110544400c0144100c43c6500404e0b400300e10241102d80d036415130b02409000304800002d0041c2040c000002e1035081803014041c141a4100c00982 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 377614235 1250 377612985 377612987
    0x18180602300106050406110a0804080604050705041803110a12020a031701082a090a09030e1915020106031403071401050115030905011b03020c07060815091012030906 73
    0x50303814280d0300312114007100d500d0000042c1c01d074450f07030098100700401400045082401004241580e540c4082c3c610740c0e541c0c3e00c00c001c1303454140580d01201d0350302401c580020180780c07070b000e1852800302070001c2030040213056400b66848003244001045d00d014940101e40070601070325512030110340540150402200f5490b0050092204a42079060751140381c0040c00610340c001504198014103560803d4808540402004403100d07000c0002c1c0d01440410800c0007158044e00880042442030325001149801c03441045071492902180e1141c07200070080c03c0281d1907030088403c44002c0c041c00001086a02c1c1c1c0c5070b0001d0606184464071300d50b44000381c41c20400c00310041a50440c08100020041941001190728001d420303000d0240415407103035821000d0050030b5000401d00250a186c8a00b002502d240c0600650003a4907404000e00800900140301402140101e03c00c0741c501c040c0c03002d01e500a40800c1a00ba40151013030003201c1055101161800c05000050003590082c2c5030700384031500c3d1440c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 377615485 1250 377614235 377614297
    0xe0109020a080d0e01020627070305030a030b01110109110f040204090f0603031106010e13081207031b0c0b04140703080a08060406091e0903020f0118110a18180602 72
    0x40340c14111f5200c00d0402c0360461042441d404040300d010b074800202c000b01c0044524200150700003802c02d000000317217110043c2e05644038440d00c0a0a813a14080d542d085c14640c1c2c22614a0000900b02000410484140d458040012040b020009000506140e00c030010340080700d850040110006a031100300740145078010401410040d080c1004240640c18046100b21407500500a1138050311a0f464140411100005944038504840070341c0e034003458551401005070201e03a581c0c3c640000000585036102e031150819448003078000b41844502d49a42d540c010044880360640300280c0039060000c00050903010090103000d481d80e440c8195406d1000810046a80c6944020700c024a025407847e001001325412803070300e440e0964000344000190905a00b007480c2150550880c0d440c00301e802441c2d01c0c1d21110002c400e1301070b0201c02506110b60b014880400762601502401490464603043c4620042e000460b0b04071810303000902c04040c2e692110141d0b080490082140800e9028585461000d9a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 377616735 1250 377615485 377615507
    0x20c1204080d030504030509062a07081504050708070b1308030412020d020f101112030f13030903050a0308160806060306060a03090b010902030115050903070501030e0109020a080d 79
    0x4064a00c0e0500c1e00082a56a442c000340590030316032100c00141c00c0c180030f401070b0791400700050b00d2260f46a020800b805214040020140c074501211400c1032880c0c000024940e042d9000a00140032100f0f5a090341e00024100078000c8520348a6074401140750174050182100a02d4003240742d13030300d484608170601801d4a8a8105a500d0b500070f000c10003015194100040400fa0180c2c1d00f020300c8d102d00d0000c56805505441c890f90804054007034050919441480a585802040107032020b02c2d221401842c254071007510032a030110f44010116100c443c100b20403c44081c800d04118290640d25590f060134415644000d9021a10603820008290b08842e44042560030604d42140503150410020708640000380080e4021440032a1501c01c0a000758480700946402c41003400d21036944030003400295100340290090031510040030212907001c0c8013602c58242d802006060040d007004011402850f64010420156494400c1c030805a140c0d900c00c800034246407806400b60ba500c59230060b00105d150 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 377617985 1250 377616735 377616763
    0x2012040f0605090a03020603060105070c081f0204031a07091e0f08032106030a050604050c01030b030d020601051e060d060e0709060503010e071e020d020c010c081b0709020c01020c 79
    0x400c501c1c031580d0341310380c1c0c0301040d0790b4101c400304e4690700c80c940100c40718021008010701d2010498804581514000f502d01610540c002403d2143e981e1200081c0030b034001c601c001030000302a2f0040c00b1030040303880585c030341c450041c2c07500c2c007007490307842d243c40030403003103040c60440c40c0e4441100c1405550a00d0112002a0030020021460001041c25407180d954401c125800710510381da001c102141d400b80b0250511340c0d000001c0310060300b01818078545981c4100c070200d010134600401c100c598240454541940e41c010b03000740c80366030703e01014402030303555034004400d02c1201062032488598800300640030361460038070006100e03801d0450442d50080c01919040500000c403d040007c03503803084c210380c15240301d4942002240c84405054a200c0c40e0702d419240302288400038020040d0b40080c003d02c1d414080e40c21903a01103031610054900c510f01100142c0303203110030080f0000ea080170f900d02d41141203103002103d91041d43c0306203400891300096400d0040d0f940000c0c4a00c10f441c01007114038003620803 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 377619235 1250 377617985 377617987
    0xa0614010b0a08060d0c0f0612060e060303030f071223010b180111010225050705061908100e0702070e091c0c17191e02030a2012040f0605 61
    0x52081c0070b8500180108040d200c5c400d00d045610401101100400042404000c0c0c00c9031f15407604006003070203c41441d54070340760340790000000f03c030000c84260a010304400340c0039510b1a01c0320300206600803002400307541807110140c5582c150704014440c621603451075140301b01100d6242c008051400b807040c0c0c40b64a0380c010612418100e02d111700c2a0011100c401d00300421048400100940039002c2d4440760030348541a00601d081903446071003070124862049091f03031401c0f5103d40400c007181c0076005204034503001a00900036814080c5800c1c507003000714040c038448110380d501121296941c045500da8010f030011001000a5110312008030340141954014003c3d501c0b21340340f503140359450304441c3d500f04400600c680050181c0001007010080200c85100c0e9036610804002003000282c00c4460002030001c02c0b490050f000b406003210030f0610580c00303035241040e108421180c001d485c1104c0d10f2603424a0580000c01582044444c0860310700f0b000840d00c0c0c070300d405190400385055500600900c10 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 377620485 1250 377619235 377619247
    0xf06080a050106140913061707090608030a210501062609060c0a0912050a021005070b24090a09050f070f09020f040306090b0609070c0206070210110a0614010b 70
    0x44c10002d00c4c2e004110f08420180c40c4e0102c0c00c0040c0d00d03003c1440d18000f070280b502c02d01207808408059240701d2500100c04503500103680b54014402c40c3d107240b06910190b0000e104d01d81c0120b110b02c0300303240d10303528041c8a00c00b209141401001141d80a0b4031090224041c0c80344100b6044003010500765030303400441d00e020f061901200c210744500005103076510101c00001d44840d03160152044002405185041c2c0d51441d40910700141e84203003501c5d05034030402140000d465014800c4040740d0f4429070104101c406c0b5201c000405c8000085105d0746031a4075018100300040f926083c07201d034410340548201140082060070b18504200000c00b03605807035089164240010aca1a00517031040311100303c0e0040e078824800d4054240340c02103070401000b40d810000000280494500b9040c06501c0441d200c00030303501e4082044e1034650038103000a42006041c03110f0005464010030401e201580d60410303022403074841140c1818840b00c4031048070740c81d80e039511044412221000036409040380381e411510b410 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 377621735 1250 377620485 377620487
    0xc1b0303050d091b18060e0105030d110331080105010506071103070314010507021c0905090606040905010b040602010b03011a370501080a0c090302091803040f06080a050106 76
    0x1c810200c2d0304400d6038031014000c042001500840081074810450b4080c1e20b40c0390440c0c100090a000d00b210205c504021002c00c0b00e218440384981260001070042480c2c0d001301d0340548440310f9459140c080f030301041c0031940b0044810701c0c42c0c9480c1c0000c000a52030300c0000426400d07080d00507400c21900d40c1e00d80740043c0101d0300d800c0c0485483c9a004007040304051840d40010380b8003541da4000030141c280784021120b90900542001d802144960251490800c14904901c0359140f211071800000f080c81004101600702080403d82200001e03100a143c00c4c0c039005008159502a4800c0300141740002c1c08100050f030a21850382d15940480c02071180c0c20611104078050b5030002039091188000514959130582890181104285e248800e9000803040014190012107140310301030100e408040010602c60180c4107039048047c094a0b001d904608540900909140040520304c14950185190070703118010009440280008504c840b00582080d2000b407074010701412010030182028010b00070742d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 377622985 1250 377621735 377621737
    0x1e0308220e160c080c01092d03020601060f020c12030a02060916050906040f1113050a05030a0311030d1505360c070f05060610111005070e040c0c1b030305 68
    0x48000340b501610b50206410401c1d072501c45c540181034190b103803a2011040004074210b0408071b40b05190900d2440c03403100d500c95110024090020011f0304540d00500019001d01891610911030788121075040c03140401081c108900307910300040c298408142c40d910700703030304220240d4051825406452100302001d05484035085502420713100d01520000155691120f600c211045405007005000700041000242c0c0c9550042c1940c1b060006680780c0401d96007030a40080d02220382c09401007405a03d181c034200caa45441204440e014001007002124105481c0942c5210400800010842a20340008c0000040404038032030b100071140c0c0c205d03d880000c2c10000c000d03c0c5912041c81422540c660052007810b226907940200700102c1c84400314280100040c080b0303c030f104152030b45100c0000d9010180e840781500340f500c0d0342c0c95010600041c0c0c40c10b5a42c2110742c1000762800d041c0c1040311007000060580d00d040030306400180205010301c0c1402019280001070340d03003a54a0f4007106003152401041 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 377624235 1250 377622985 377623021
    0x602060402040b01171003020f15030f13021305010801050115051801020c060c0c0411091f0926070f0b040506070f0b01080a050d090501091e0308220e 66
    0x2c00c0341d650aa400042c0d02401102d00d661192020500071843c04401100160840340801da02800c0082c00b1080c0d18107102c40c03912260000065003e013586d41e02003000381100c000030302e00e1300540c91810304200140c45684200d41c1003081140c01050546c1400380d032a08442059200c1e1003618285d0040e0703690b03203412004440801310700c4d1280c3d075600c056540041c2c0c82c15104406194121200180f03900c1c02d8000031030703030143d0040112414002d004c0a11603034903945c018000c42030f5006003840804440c1a83e074010301a410f401c641800c4100980ea0a010080403140714101c401d90440d40007c0c901400c0e0070700080340038241b041e00015205040100a840f00d01803800340d81d0144100280060902135100180840340d03074000d80d141e4a075a1511409074940d94600801c070756611820345402016802240354000ba198107944020b922f0b45401d1880f0b40b5201c600044000c040f41c10b5070f02001240340706c001008540814030b504c8500b8800c0000b60300407507005502062680300e05e4014003003100446040184 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 377625485 1250 377624235 377624239
    0x415110a02090a090c050303040605090a090c0e10091206091a04050d0e190305071d060904060911130518010204081009080d0c0c0201080f071202031317220602060402 73
    0x50718480c00d00c5e20000d00009034022540c148000b1500083d807a41c000c000f0000c0e010252440860741d40e85c0e101a005550811003141c0110300c1208150149081c2018100d0070142c0340d250844807155501c4440c00c0c540500c031000d5404a4654040e41e0a20041c54217170032a004c42c00e04510702501d0586c40301c40c0c0706c08a1203805000c0206010002d001552144c469041140d4910301d02001130303a4034900039503160554400e52800400d0300f6081007080c02440e009071f2142c40c4c060701c0c030303507175580c40e6070b101c03001407070001c0303084461000484041c0070700c0e01d40202a805e1070100d00d41c0040d050900c295040760416150f01504450380c010170081c02403c2000c1410300e001c2503080c3c80481c0d800d26514120a0f2401041c0103005a6032030800038102d4240d108248000c80c40c000e80380d0501c9a110642560a98803046582401103482c42000003d62a400da000b1540b1038100c00c07041c4284034082d41c035998020b08050b4a10080980880c03c1540310780624140e0360b140c2103d4448182c214584500a0344405008002034 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 377626735 1250 377625485 377625491
    0x1806010806041d06010b030a06060c110f01050d0510090609181205040e0f0a05070504030807241a0f060c0d0e031006080109030210110706050a020903030415110a02090a 74
    0x1035070038000546000f0b420b010920980d9015078680d400d1102942040740c03800108c9003403640002d20340f40a1061141025000103004451180800c140122507840d5403482e8104502049030803c01505031103501e004920315004110711500c1d020714401522010340000748042e140507114044038020070b0742c5010042c1c0c020200d003152202c10071b069505d80550381c0810400440700c1d04000c0c0102c90b00071807600c128421f100400c071949820004490318000c90000410954040010314085103880302e01c1c0461030a82500d00c80c0c3d4030300401c41c441c152480c0c40410b00201188846503c0989004840c1680c291029202d6505044c400c103d5217a580a800d49204140001411800b0141c0c9050001504043c4a08810300680d5a9030701c1060003040313003440036001401820041c2078490700c10f011329405070710b2140c045820002c141c2c6624000f010007803d00c041041c2d003000784440a807401e2010300020070006135800c046800561001c0c00e10410071101e04100e41080310324400603600c0000d99500581a90800 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 377627985 1250 377626735 377626751
    0x230f0601050d051003020409050604060c02030a0c240e010e0712111e0307230405270c0a03030e090109020a1416050708030a030e01050c042c01060509180601080604 72
    0x81e031390301900d80c2001e074000c0e003810f4904080c403074001500c07800b440c0300341c80c104a80998100103d03241e01404076560005840380340c0c4040032542402883d08102401b0801c1c013080107a00d141c08048800c000c4000110307075119240121550424042c020052619040e00e410000e03030f50b0f43d28010f108500d91207511400500c4048099001c880c02030300b8900304041c00702c5420a4881c1c400203507214404900c80c42c00c80092441c048242424003800b4014081400040006080716207100e41c207030070f402c442c1e04140c868801c40144650f60386144500950094803400003000ca444144000424160450301c00180104640343d541d075444800c09842d0b4400d000000d4490113918807020301115007004c050280c1c4610748003c1480364000c030041c002c0c01c4294400300f05404440160509076507040b2014007003524140400c0043d141c0c204009550a041415104415940150804a141710a8116900080c00416a1441403e00d034002c1d0408203051400340d0810320300040020305200000302040e000b140c440c0c0302c1c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 377629235 1250 377627985 377628001
    0xd0803041a0405010f0c030b0f100c1b080105010f03050309060306040e0a060b040c0207050a03080a2607020705060426030c030706050406060e0103031b15230f0601050d05 75
    0x500201c051050103480300c2410541441e5003c0d0140a4541401c1450310f4280201c550180c800c50800140c0030746064030001d908410403001551852005052081c0d03880007400040003801000c2a0750704000840300403a0070501d036142107410507040401c00c03c0c0c00320004e01c003064000060340e1131050304962040d5a9601c000104018000e4010507125601c10205070030204035240d000006030841c107807010170251140d01000c03a519103040c41441d42101c0a00c0f0f050001c10390210017004150014203001c20224001c0090b06c0300c04009000c030243d00c4000d0428014401c1c2e041c0134402c02800201d170054206401c2200307104034150f45a4462880c610220081a03198000384180c600100c1e1941c1525110462070404a001e007000320780c02c840d410b19003607000c900c4c0c01c142000c460580c1e415a54480009040306a0710900d0360754001c069480d800c80300d8660414030741602401c41ca00c0d144403070308690f20b030112400442100001d4150510b0301510f10402c016070f6404001e489966a03400d81c0429180c41d6036607 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 377630485 1250 377629235 377629253
    0x301030b0a0b060a03090201030f060506250c060815060414010c020406030501021309050105030f030a0f0201020403020a1508090f0c010e041107060222080a021002010e06012702090d080304 83
    0x5202c58000300c011584000d5580c05901c603142041c000c3c1c8080c04603c0d0b1207030b10b00c0111145030180c2584800305020340340d00d840910307040d4400401d0a85400082858641f5051070255581d840400011640c6040020325044410494038400c03041e50302604250a004612503513a02072000541084849801103040d940c1d00d411a10056400000840d920b4100d00c003126115840ca00031030944604100c00040d2a060006da032a410040b498061420044c6001040712401c1c10264100d046640900010001da516001020014182d0104040c00c07000040b0024003103000c02004d8045c070303401001d03903105890004120304024040900c0c048040c201c00c94005001007502561320040040c000ca40c040400620307600400000b110703121940c3c0e8a481c00015030154400310f00030381c1e0719034100c25082c1005041141c80798105500c00e00010810790744d2040002e140040980c0700c40c9104248008401d81500862007011031504590820f515015803640403078041c3c4903844008088000001c0020140b0030a58 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 377631735 1250 377630485 377630501
    0x60c061905100302090c1e09040e150f0402241902031315020f070e0603160b07030302031902071b170304230303030702010605100c0b160e1c11030703080301030b0a 72
    0x5491246078001f40d1016035985d040901c805014614004070007806200c00905000030140003012802159902c1c8880b841401002d001203800c0070082007521441d203900c4d1038400b501810903280a4a03200c5c1c0c5496401280340020401e01036400c2004a4001029900d28900c19a40c070000708840d03610b5000e100300c2c41d100c42110920610700488070302149681041e81c000d401508110202e0365035030010540e90000030380c98451850402c4003001000002806a0065640814044502041c514454003000705a9001c03210071070303000300c90102103046240030301d913020082e041c161000d00005a00442030343d601d10440c022058030040805a0300f0503040a640003403002d0300041d042d40d86038182100c0190103011280181c0b48184041d18400f04ca440c03041188040b03050300401c8081e0b090301c2d103800261a03108481d80304010051036081131680354442e00b0344401c04140709010300c202e00d0182c0c140510310201c041c114134401d4000308005c00c04640c85038107403410350fa0040c050340d1041c0c6440f41c090300104000307 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 377632985 1250 377631735 377631757
    0x30b0111010c110f070806130602040f1e0b03092d0d050409110f04141315030b061c020618090a0606080f060a0909080405060c061905100302090c 64
    0x49900309030b0a40d807204124083d035404104440ca554542e808407522004907014003005030707004200240300a601e600074501c000303000d07140051425031100316030320704900180c00452903030b8445050200b5280c03443d052000280a030140c1c56040d0b04215007041c0d110522100c00c07504514980040340d0060f8403036004000b9465035802124118000440b0242441d0800e1080807140b078070b04481d1348240c1c480308048541c0000c4113516249018201583d40c0e4412410000c002c1d08402c0c071084500180041c7d1081d500c4580360507044111543c910b150101400c00020216030284503070308014504210481b5410261903812504203403548281e9085d000711680150f085948248a81e00380145801c0da0351000041d6442c544e41d0f11030f80d943d14079140d802524140c800c2a0801c110481c04c0024140716071081ca62140b240b205d0381e1a0030b54480005407290010340501003140c21503810301100790f48544201d4503a45480740c0c00c0c4503c0c5040e80400b10b0b0700340c2074800a070180c2c62107800580ca006020081310307066015 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 377634235 1250 377632985 377632991
    0x1d06090d03120e0a1a09060402090426090f150f1b1c08070809060703021806071a06180109020d090209091c020c060415020a020607050d08070507080901030b011101 72
    0x11403583c950390310a140040d107100103002d10394401c00c0094049180b050302558020486504d4a07400d10244035070040094401c6154800c2d0f040d0b00d401c01010f66801c0c038101e41216900c1d14044410841e11a05925041d071092201607064001000701d5010b4804c5501001107075902c4059110b03812000c101e2008858801d0300603080216100700c0400c0c4480f015190640c1d41803865541c2d030600f0782e0010801d0741c021269621200000d0342440c46500148a500846418400b1001182003c00c485800900d000c40302c000d0703108440440c400111090903440142160401c090303c40c210717561007200d081800b410b91055000108007518680d280c205100301c55002c1e041c10500d01e0400c401c103469500040c4c0c0e080c6400706020905258600c0014507966015000b40340c42c0c94a49452001c84c2e540c0e5400c02814190702500f0144000f60f65800090724515000c1d4010f4407950481e00401070261200510400c14030405201c1500403078008420341e45004428200012001c010740b0059800c0d8001410b48800e642c2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 377635485 1250 377634235 377634251
    0x6030c06080411090c07020d05031e070506070e0a09020d06030b071106010603020c0c010e1507030819110f03130b0c120604020f0a0c0f06050709061d06090d0312 71
    0x30344400c840d40301d640520b1444500840b43d0080041142e81502c80452516052000c0380151501c240428400e502c0350040340e1410703201c0045000d02d00c1c1151264000b004020600c281449814850540d0110092030303c50f00d01e10240780003c00010050042c50b07685039000c5070045082910754000c0001c0c1d5001418005c0a10f0000e1004152000041e03924100f030013920000103100b400b0780240c404c150140f42c0640742d0a80c11000445181d000d410503103a2264940c414940540701c0708008003281c902aa036004418602401086074025904003c41107040c6800e1040424143c0101036941ca84330841d9420741d02e440d4201038265101c0c00c120040d042184120500540e030500d4802030004112483c800149a542c80040004900603558100c4e8611010415240801e106804041005200d02d002e01c035009248d031030b107004540045038180301269070100103002c2e16030060903410801c2c040c1d54a5050a0382141e000c40c866010b800801801a8000c43c5000205030060942c185a004103c0042092036 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 377636735 1250 377635485 377635487
    0x1020a09120c032018161d0402031503160f0b0307051b07080705060702090604022b020301030201091202100e0402090d050601061419080a0b1207050f0409031d0406030c06 75
    0x1210038070a00c92149526a105201403110109120b1000c2a4144108106c02c0c0c1040d01c0c41c00070003850507094001e828100303116903160b1000d1405420040c1c410f440001000003450b03d0b10304c0340080008815507000c5e080000181c48030a900540e034172a080c2a80343d4885c42c0050341c0c58000c0407050030404400d801a0b89011800050120841d8140130450344000e44c0d400c1408898460250081c1d0000d80c52400128681044c1c0c00601ea109018412203160001003031810f0841050065070041d4a50000010400e540e44015030901034402c00302001c0200c6600d40c0000c0c01030f41d000a0001c284940700201c00182d030345960588000c082c029024000100b020310b0840d40341c8109005020100301c820b40c069003100700d03040544070340d0821050700050011409030150760410000b0101040036840d1290610517440d01441310100081500c010320307005047c942048030382401020500d004500c6c00c0380c0b50001c80c0d4030440ba652620f2049209480a80000c000f00b0302400060b0406802003403007110006140b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 377637985 1250 377636735 377636783
    0x605030a1a01151d0f03060a2c030702100e06221502070b0d0f06030b0415020906070605100305030f12060105040b03070f030f052701020a09120c03 65
    0x1201401d20814210381e03c03681c4802084450f03020b160005003031101903007509407a510300390a00803001802081d6490408000900c0c08404890046a15880c0c4514075680d1214001007a0340350382c150701810407100d01c8030032580d9a001b40c0601a2042d00240c00a0b0061401007504000704000605500c0e540c0b01022000c0342583c81c0032056200307560b0f80d4400001d008418145904407050a40d003c0d00005103071041d4a0825003100154900003596851114044100c3d0b1080f1b000440c403d01d10188a03181c5420800d02c1c01e1340342c01c00b15048900402070180a03996103000c07a0700c89030340700c3c0002460f5212003407a04030000c62504028aa8400051185204c10701400602a03441d00c64290122550710701c00115040c3c0900d100340c4500d0300050010440c001d00401600f90300c0443c51400044640403165500c5c04e07954203880e0001c1c003e0b4509140b411052003904180310301e03a11140254903050050740010812111072241ca81160b0b00d18100700c0c104014140710100039900302c905044d02c00360500c030416034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 377639235 1250 377637985 377638013
    0x1214150108061c0807050c0409060c021501031e030c050139050d0e0a020a0609090612050a080901110303010815010501030c020d030c0909110306040b0a0803031302040605030a 77
    0x30502000c005a001e203800d03001d9001c0300d020b40c0c1001045598030356401413660416030040381c4500031140e109102e07840b0740c440c0d480c10600400c804079240b802d050b806400d1010b200521100030109000600c040781d40c00f80d460045804030300c8240c004a4103400c0444114120440040165003403640280131803e0706e10102d62000501041e44481c12800c00f5201c42c1845052118030100d102806000d8180752564005000104464283c41001c06031b90f000690b00c0314150052000303e40703132045c14003080750b0610502313000c0c200000074070404501c16180c0a54035010000300034000b80c0e0024510a040c0d11076600c81401c85220b0044a0301d958440e01d14a403a00000718042115005220000800b988240608040c500b66500a010ba40d800200101c0107043c00c00608030500000010002c1d03068024441c0c20301c420603840c3d00700d48070b0070458100030a4440052503144039a020040602ca10f030008022070350014400305070040310300400e1002c00c010f8400c5a2020385d00d405002000802d21400640c0703556 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 377640485 1250 377639235 377639237
    0xf060a051006080103030219020a030803040b07030501050a050a0504020d02120a021c0522110d11030601081c0305151518010525020a0e090f0c030705010f12141501 72
    0x510740741c81e40c1c01128072040910014006a0052a00212070381d0b0340c00c03410700310f140040c0143c2041d80d100e44034002c0950050390100e4500c0200b00800c0801641844bc0601518046030050a900e20300000500701c2c1e5100e0107001d1007180d000030340d590350014a50488810444410500c8101e24000600314000e4100c1002c078280030404016505016103148501886107200302079900d6080030400c00002e04011030601164540b1050092480c2680c0307403411074451030b11900e20075109201c64070506040004c1a4050410342d2b0004840b01c0161038440c049280c0c041c0d5038130300000e00ea6141d0a680700841031a1241d0f07a007040c502040f14803011a0000100300002d103000940413044c5603c4011100c6206029010740b0001c1e881c00302011109800d040300344494001425654800d031141c2e144010b44405035803124095015581c00310100c10180040980c0b14001c074040c0a070350f481d20002030301026000744004100301c44d424080c40d1a60f150b030300c8020100040c40c1d0511381c514100100310155250038000740c0c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 377641735 1250 377640485 377640511
    0x70501111c0c060b061303080c07090510300b1b071520090d032715030509100e030d14070e04060311040b0a080f030307030e060f0412020f060a05 64
    0x1070b48030301748041143c141c1101c200f41c00807581d145441e80003007034220040404081c007580780f00140f036100902800d4007610790461440011460302907a07001d03020b40e2040c84c542e825a6061a00710b80c0089040302c5d140c198200c40c45800c03950b04c400902c0c00c00c1c1000c510680c481d00c0d003c68001c0620282d02c1c014421080800c0040210901d5800d942c084030109242a104442d0100582c03490350034401e1b50188424401e0400680403103103899000c0c81c0008400c0198014000d6a070304024106803051507a000d41000e040400072070406d9691b1644070340142403200c032000d40340c11200006900801c211003003885078003c20030900902000703001c1d29542c00c0c0c40c1000012014800f480c10351400744109011698003005014545220341c044c040a40b03000d900c89035100141c91740000d40d61f4024003080c0ea00c40e650001840d40c0307142c01d140103001c5075a4001103059643c404010003200a814680c559001038110070007103901006507404a2801405450b50f40d07181c000c507401c0c0980e0b11a245c11003806074503100400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 377642985 1250 377641735 377641751
    0x60216060203030411040f090209090c011403070926030c010e01241406070212010b091522020d15030203010e030703090e091908190e03070501111c0c06 67
    0x100d9803400107880280043c1e00300000e0403c82c6c5019030013200070580704180401c0b41c1381c06400080d01d8020444001105410040019035290391205e0740000703d40801c4002130039401e1800c401040140d10b4001e40300c0350300701000400340d01c0750102003085d6080200001c0300d960754035801e2424003070185518081702a60070110002c3c29012004444102d030728034000f20b1002c0034a4a2113901505160400054210350100400409038845608515181050100100c2e4819401003032103c1d1032801880c0c40720410b02c20300c18000e00d555100c0250a0170701200c07a0b001181a82026400c000c1c49181c028041081ca45407251034405501c15184007120b00803030080001e143c09690039034491140d407070002e000401081043c801c90204840d040e401807999412100380c2c00070040f0007600c01da81014150360280d40401c10b4084001a28080d0200c0364171841e290903088101400300356244107038040c890611000343c200580507441080584161114000c881d00100e07072120014044264001c01521940e0030480380b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 377644235 1250 377642985 377642987
    0x7030305010e07050d0b060c15090606040506090601031d0105090106050108010e01030b0c0a02030c01020708070b0a0b030709020d09020a03110a080313030602070302011530050c240406021606 84
    0xa0b0070311614850b03c40516103105c0c03000b40c0c00149004401e0651000c414405150b15500401500c210208056260517241c24540c00f203078517009005050b14400c1d4140005c02c00710f51120410140c0001f802e0802080780b040328404506000000c0d948520a58070303142c01c011a041c4150003110481b80300380c0b5003c0240e601d40d115100c0740b03d0300340000b4007035800342004501c5401302580207000c03084084c81070781c0c10700b5040382040d07083e03a00540e4140e50050020840d10244445c0f50045071704003800000c2003014254880202c1c1e11009103100e140525940407c00350108074070b42e008640001d03802020701d90300f29240e01d080030701119000301250142140d440080740700d036400021140f05d04030090b003203000c0307502c4c698618001e54050101102195228142d100d41d051812181e072000e0003926200c08114402d0580c1104050052068000b8000b403948151002c1280815407502680096449000403202c2700c10301406110050031040c0003440c0098009400b41d40401c84580390660170064202e07940d51208 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 377645485 1250 377644235 377644259
    0x1e0d090501080c03070806060d0f05191401030602160204020c0708120c07031b0b190e1e09040206130915060903021818010204121e150506010e040207080703030501 72
    0x28103d60b030741c0020400710700c4044c01410b04990240c401040d00c5e02c0c8c81c2c0c04551b05d6065589009003040000e4658050044911041a06010f582c1508030204090400040b41d1801200c1c103100c050240c40c0d00250410b203d400c5104048100754001e84259a25450741d4003d50b1344151030b2003201d2140c040c00241d680c007401d145049541d85030700d103401401c4131403d5450f0404600404001d010545220b050001035000e840006002071400c00340710400c4422030040040c02d071000c981d5a030351007a141c81128078015051180300c1c00b0b2030fa1041c3c4904d042c9950340d1005c0f401c14814403018103032414105400168641054108282c0b00d010301c3c0e4074904041c1d070b812090765880e10a0000a522403100008920344240036510140d200744c900001e81da140001c0500d150072039100350003d04000c0414007150003484442c1a140252440c487d009940b4081c0c44e4407540750320700781c00c02c1c0324500750340362800f00d0301c107130310543c00350551b1000100115070380c418a24052401e81c3c080002100402d0614000044a0f081d82c5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 377646735 1250 377645485 377645491
    0xe151e0108031e13060305060102070e011a07050a0b090304140301051302040b0409170405090903040b0a180e0a0504120305061e04060b040e0f0c0406050f03091e0d09050108 76
    0x250003581810f03181401001102d039100104102da4a0134040340c0c0c0d00390b00710301c0b01c480240250349000401c0d0800c00002030510000360459503600c1201b800400c079070304202503a149010782c2800d1448d00c60145103041410900d0b01d6001504441d050b005000c0f01d864040300500807182c501e038411013503a0a40e0149800d0310800c40b124036204180c88550340c0036044c590007070600c0300c100802c00641d44685a880c4808940107140c1c00300d031100049000d11041c2044143e594001a41c00000c0d42880d260180d000c43d02e1284074200401c211503042c40e80c49116981c1088801b40040c443c4082c201d140504840c402828115001d5903140c80151070303802541d0003445414040e8501401840000450740c0803001d0712a8440700345a0402d13a00c103400103020150324064009000310740240112070810602e492245a0054444400f0364020001000000e8005c2c04442c4101052b4082c01e850ba0303100c001e0907003045900c00484000b44002c41081c4500100444d00e540c0b400204c1e16103080701f40d201c4e0b0045510100c11 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 377647985 1250 377646735 377646749
    0x105030f0402040209030109060507030c09080a030f090305030c011a010c0506180312090309031638070c17070f0b070c12050c031e030d0e010e151e01 66
    0x410104004510039060305a0280c009040076203480407aa002c28211a03410343d082c1d54243d91081030085441e03041c0a1140410460328205000f1411b08580544500405400074244007940000002150144500c04001d640050560382c0300c007a1084100e000e01400c032035260b0484461400e00800d907005680130140190044001c041a40d6001140c956515022120b0b041c240300500c00b0454408a105806104114240256031100e612109152801d000603801c244881d941d658144000301c2c50403030280911071206940c039118a09042e01c2201c445406104604452000560300d0601103000880011117100c01c00301410710805089045d11821720380140c03840c1404150040201038002c00203840b4039402080000107665035005001e8051040f00011104d9401403c803141e054a03081c4441510f030554480d00c0106020440700041e103c0c030034015030503034040e910049542600300c00d600c01a01c0c1030640e8200c9015490398801012030200c1203411848810100344d0248540d0f050078900384c100d52203 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 377649235 1250 377647985 377647987
    0x180d0f0503061207080a050304031b030506040b0c120711060a151a0d02280801030221010603021018080304050a150507020d0602090f090402012309041b0801080109020105 75
    0x3440b0100826098040300402c0b85206060010400b074405001c81c400542c45040215910380c5107207403011190b00205003031103d14000c07500030000301c3d00120317526034400d501c8454880c03180d5941e64884518092005185000421281040040342c1c00c50310f120000020300c400c640440d0f880d81940c40c1a100f0b003c40784101e19680f01001c000e06402071666800b16113600c41641d080c41c0f030a5006504036080318440102d4030201e401419092654032804610301c04940c031300540d0a6045070040790480003040302c9556403a09916464288480030350010000c1e5900401d03800d0742c642c0055000f02403843c1003100700c503148215000015a07000c00001c6500310703800601410502071030070120a00443c1c03c2513070701013800810000000141e0f070b482c641840c2a4440e64005883d030f07070a58180401e141250005d0340c064003450342030101503a00629080345c21a8901c1000c0d003910010f01c41c0030f8050003201032080c0c1090a141d20340170b5a8a4051803040540460b540c0d2254680e030b5204040e090760001c070b10103800b040c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 377650485 1250 377649235 377649241
    0x130209150f01051b03031302130902010e0904080909090c100801030c17030d02030a1d16030602090f0d060603021005040b12180a0b091905030d091109180d0f0503 71
    0x40180f010b80039450309428440c14004409203040d0469000b250700a10010b64480818118a401c0c6444454160515801c11800c06103600291000d9400449144100c1506000404212042084425a0101030324460650614561260b91030190f08d040a203c2c003034450411070020302c200500e9049030340000700468918038000084081200d801103003030582c0400c03c0720030f4800c800c80c00210f0040105010000d0304066140e0882017644114095034440d401401b8007803050b46a03014000f0a80b82c0040e80181d54080c494000b40d001c075024944980c1150860301110300340a13455001600720f90013540c0e40034034000308900484003885076004201070f81c3c80030301900034050400150303194084051000b0014400a680140d85809400141296028480020070400190a100f00305080e208006445121884c1c1d90360b480d1640035036000346e8100d9a4840100342405080270400f010480301a040c0541c505018000d00009030401c0521000da01c1010070018a2512030505101000060f64819095807 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 377651735 1250 377650485 377650487
    0xf0a0e0312100b120c0c2805101e110903070b12090c06070602070f140115050405071209060f110d05070507200d0501020c0d08090c0a03120302070b130209150f01 71
    0x1800c81d120004a52013500791074610b1f00f6541440307001142100343d0541040d1498070b801072a0009201810801070b045c08094814000101d101030740c81140b0b0a07001c40c0510071031003040c2c0d45028070b5807142e40c148640c1d40006400118100107140080103540c81241ca0f41e10039450355603c40c2c8915406402c144104920804600350b0b074041c100c1d05100d0100d004580500da12001100c02905440f07207072603550b40b81301011070640c440f040340c000c003401e4405000d03134540000013030590b0f4001c20000300c5494444a2079410412140d000b080340807450402040004140c030340c04d403115000101d130569881c5c90400418001405001500c0109510847c0201e60b4502c101c0c0440c0544c501e0701c102034001c4882c0860000242c1c0c280090281c4068000c010180190b00040051842102900c29403294010159012040c0c907600740d100c0540e40c002540c02c01c1100c044004400a01c80e40702c0180549140d1020b11062486107134614403d14021a030918030341d180c46641120100345480010360207040005014070715 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 377652985 1250 377651735 377651737
    0x3070503040606260c0d020105040b0a110307111c20120a061a0105120f0702070b0705030405131505010e18090c100c0302060f0a0e0312100b120c 64
    0x450b110311000705006648020b4400308035615003140190311516545495401003c1091540c101822540d0800c003001503000a48984100d020b540c0101000003410882079016002d02d0140201903c00c40390303221118104008030713440080d16180310b50f2068820001c21000c00700092141500304d03240509400600080c40703241c0841c2c0c1c65840d008415801d034040842010700400c09854010748000c252081c034500f16580341e5412800d0b450500c03005000071240358100c1010594004411000743d4029110044182e04e04200d0394883c11a400700099050200b0001002400071164240e034017009485551818106480740f42a80000703505500c10100080c1d0b200d0108420a50340140c20010f051000b0f072000b207050031003122020690b621169104c1034605051100494141c01031500390f0280301036075402074448502a0840908403d000b002c21220301072a800907c10359158001c0b659035514172018510140c02c1120390507003403000c4280004190314544111060b07461300300d01c009110b03600c41c6400b05003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 377654235 1250 377652985 377652991
    0x408062d0705030c16081309060b07031b020d0b0a02041a0406120b010909020c15151804081603030f0b0a0b0901030515040204030f1103010c08010308030403110d0309110a080303070503 81
    0xc401480d8115001b041120004040c081c2c81422940d41c00d60402960790b00b07440e6140c3c8220742d661001c00280010076072004100002e4226024040301c2c1c200e240c00000c0c0e09403a041405041071001c9000e008280c002ca50050040340e0040f000000c9070ba40342c41500c0018011440b074500810300e8411b5040811440f07038802d041080d0305050402140f500e907042441241c0240f1001000360307012781048500415611210780c0d03c03450701510110742510707080100304414034003162a2150081040464104000b00c0e0558030301c500404210021010b1908004018000b05c00b00500310b149032840794a1075040c400154402d4644200c04180751081d03c20044000304001404660310340301d642c2107002c5070b64407400104015070280c42d000c00c0d558601d0401d0034041c00c2d40345007981709038904020091f01507004040c4c1760440f50851181c1d602c95450303040513141500c186000350135600510070121100350b01031740810b04082c000d0040c0d400203003448090100184080c020440039030703c1880041c140c14800c03070055134 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 377655485 1250 377654235 377654257
    0x9090507031407050901090821030a06080d1e080106052703030c030406080a09050703060b01170a060f0812091002190b060f030114040213020408062d0705030c 70
    0x15030301e0030030078411608610540c2e010f0006080020504280e41c1d0090854001c0c202c5500948405100c4807610100b48680d800003041c1054080002400f40310300c0da03c0940108070a2059a114207007240c03004000000c8100001003031980074204e0356589100740c0d100d5058072074a0300d0b62807a26015100312b080700d1800302c0c4031000d243d04031041c0f4642ea88040c409480713060821401151600d0400c1805000c4000050440e0b40c02458088800041840001c5040c1200c4d0001000581c8000c07050040340d40e07207031200f104100860490b040c005000140d90200c0102d59640301da603e44c0315104d0107403548442e1142120002c0750010703c190784240c0f8103003104441103207560044900106c00038600c1c1c80c01c0d0301400c4054a00390010802c0001e00d041170041d060503003004034001c000380d601c03503003440c200e025010340003a0050910040b00f0031020700c01d0341102e01400a140444600345414005c10f000020350002c100c4099000503100d08030301762209003160041009403911825a0741c0c0c0310840a542e001051006 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 377656735 1250 377655485 377655491
    0x7031406060313020a081513052802281e1401110f0304060e0a03030c030c020f0a0306200c070e0c0d0501140a140a05120703080c0604050601150909050703 68
    0x1030b80c0c0c5e80c01240040c1a0000681a60445140060700045006100f098495140c2115200289001c0766110342091107101900c4404922002e14100080708039000f50010303000007440a540c001e90744052030700700c2c0c26110890403a8640c241d29400c400111028601e00e0b28440050040079030104449060b2030701031400340c8094100c1500c443c9010404900b013011a040020305200390342c1e2040103900030b2030b0f080e29410f000360306c1d6940017081101d0100d0007070108401515180c04542c1c0b400040000000002c0401c4005a102d08109000b42414502c00c0d50340b10b5000e510b26205000030050b98182500200600503aa00c4c1002518449100034490b0000420400a1b0045940d50303201d854003900311409040200d000c13040610000c441c090f0092088202109292405907990620f82c2041d52010389080c20f4120071240e03924a8031000f600004c1c00c1c40d102056442181d9000a0341d0b0380700710700030002c49029990310031803011500380101a8000107010400c0c240901d00d081e030880d070f030046040c0c0307000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 377657985 1250 377656735 377656771
    0x7050a020d08040e010e071d03011b0908010f0908190c0605131101020a11130e0703030201200a0906030209010c0f030801060311030f01210c0b070b070314060603 71
    0x80c501c80d00c00c1004071180800480c0520043c0400054903000d41415040c5c22101d040103900680351030000c4641d50a8035440243e4402240c031b00f03410500a0038507840030203445110300403015002400b14040d01d6020361074407915041c801051b0040100898226122500d030031030340d0f07654810010940c1d0301c2c0c10904c00e02031250b400050403482028842c941c40b14075981012860b00d402d1990b0441c3c1880c0c241190b00959080020400c1c20303000c2003070360a04440d00300121101803140e201414a41520550314003419400005254041d0040b03c0e8400c0b40c06221036a409180c14070400318000c802503d000075a55400901005019a004100b05041410400c030007a529950391030000c040d28000300e0005626100401585825001d228440c1c546041028250301e0108a003003c0d44030144120f407140011404a400c5841810260711360681d0440411000c036522200600d80e241d200d82000c0301d4850383c1000103130a40744241b25502410340c00c090498100d482d40c0d4100205a0070107092482010001140 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 377659235 1250 377657985 377657989
    0x604140d0b01090209100c0507140a0302090a020405040e030403120c15090309060f0f0e13060b0d020301030218010b0a0e060904060e040501200715060b0a030905010c03150b07050a02 80
    0x5854020032240f4005640c44104400380320005090400340340a0040e044038000c00610040f810805a030800000ca101ca801c5580021314401da09a0029411107a400d00b848040610750300100181c401c03d03142031104d0b5107031101003a0b4070700c00c501c00076040e85005118040050320030664045114090064854500454044182200e80c6050101c010904401007008240d4120300f0103402d02082d030170602821418110081d08500c1d5441c01c031f5200b0b12841000031982b000c0303076100304050411850741d151100d20f020750100081d4000e000c01e910076a04408400010b05d50040c40505807003c040c1300343e0030072410150036607080d0341d607508551f0300c11014091080b181c1c90351301c51030004200241c86510541454206242100c0101c107100301ea506850306034000c44401c24040304c0366640c0c0301d080f4041d204480b1040d14010449a0804000202c0000d15102002d525070403c2e440640604003c2105c1e010420b4103500302c41e4025081f02150a031b5481c100081010342000d0078405002c1e00a0790003413951680 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 377660485 1250 377659235 377659253
    0x30506040b040204060c02010e0a120b060316060f0210050420041407051309020708070b1f0f030203060a14010501050c01023a02071509110a0323010603020604140d 72
    0x203080090f8000507100190740c2c9c440e8143e11700b03127010754180e034905050103071040d45c420006d41c0240c071491842000c40c440303890820003408011260569101c000f41c455500a0182000040400052080a28a19007200c2e6880345038081c03a8818000202280b405184906c054034044046070300960350b2110745403d40803121814418555951401d980f10362680c02c000c05000b490304811080c1c4c1c4180521000940c01c8011296500d4106c40c1108040d510510f809000c0c2440d0b8255013800c500c08200003400d03004002c404000e03284201c064032815036561207040221050514001c0070f01c0d110100401481d4014030040100300d0400d0009443c00b5000914905a090411103001500394081d0145c0d800103106040c0c04544400100c05520300303a200d4448900709a807a0b800307a54556074490035941040003000b680d1072031020103408116055624188a901c6c075a000c1c1e00d94030801e507034006001400f4410310840c01502d030300a1600782400c1c02d2030032900d640701c5240c05a80d08003c0030900a004140400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 377661735 1250 377660485 377660489
    0x209090309040c20030717070f080d0914031204080f040b040f05040b03030307120b0406081504031d0303192f0106060504050d060b040b12030c06060d0210030506040b040204 76
    0x1440d94000713070201008100344107110414240c12078005000c080c00080203039035440881800100c0c1151180014100b1001d0081440c40007001007000161150580c4043d401c01d41034036006403002040e010540179202d840c0d02c107410031ba000c80c0d100c0a00290000741c402e40035141c5003048603c660f080540343c14565078254040e8100c0901c2816001080000b49001d000c1c01110070402e9000d1429800d041c42c0c050700306407051200359506920307000800d8141d00c4036404171000b02249000c844000300d045c410404c00940c02d0f6030640c00503442d224140060007942c00c07092600440600250f141081050704480c5d0340c0d10b003002c02010040c80b074803400d000684074102e98021140d03000c00c41c1e07030390134404071106e084a00b85d902240034030605100401142d40c0b11500c102405401c00b00110300c43c03e400c0d0006000704840c0504079400380b040c044551220000101400005000d502210683d88460f810080b01a04e0303843e009501c05c0c0000210723f4001d11903045280c0110f0060804100000341c0d100280c2a604a6 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 377662985 1250 377661735 377661737
    0x606011103191701080312071223040204050f01080a081809101d01050a0510090801061413110304030507030e0616060c08070e010c03020709140108060114010c0209090309040c 77
    0x181c90f400c03036059011001e2500500e02500214502107400d9070b400131400004203044e01b0320101c1e6117090070a00e00c2d504146010030000f0701c84c80d80b0314050741085001500a4500360b0040f880d00d4001024409034076070150507a0040713001444240d00300e60700c00120781e200c40b102e1449172040c01410344594856216041c000c82c0c83c0c5594003c05400c1c000744050342402d006040482107401e400421168a45d1907030103080d81c2082e03501002102e89400c00b82c88040c0039a00200107036103000400642a003115049882580045540f100100d541ca105202035800200e00c2c0c4200312010004a40013a005000502c2010321904000b0b60b200000d00010b02540c108411007902d000d400501d034002c1100e10301c5074100521890900076010304013540d0003003601001164041c1844445031000c0203150081120307400a0683c0c0c08240030f0038900d02004401b002d800e22801c4402e2280e040041148202001c0b251340c0440e060307582611054854007004400000074000c3d03080ca002c20401c9482d50740395405010321360030a0b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 377664235 1250 377662985 377662997
    0x30506010e1311130e2505031b0d0c080a08090117070f080901020d06030f0201030c020d080606090a08010f090c0815041103030f04060c020a05040905060601110319 72
    0x340c00c0545041e04001458480344404140c0b5040014aa46040c0165034005449141307001103400494070017403030003c81a8038203218420700945400b80d40381c01070302e0b8a178075654829046581c0e0f0040c1503035103490780301940c01c050464035100c070281007000002950901460001d0221651144031900300070080b0070507034146000003900034465030001b2042d8041a007008540d0403610f010b51004080d280c504280f40c04000311007003c52400c18007501640e048055000c4d0400030b10f940c07854400d05220002800321b0229082c803178800103403800894100e5040256868005007580c403c82004035640c403030203980d540701c042000c0105488009203d00b001c403a840305400601380c2843c1c10020014043da50105003a50700c200741510f500078004422940299020f80c1030071080e06001c1c00030b8158040c0902c015841c0002040000751a40e1107095910074900907284009403075120400c0c03005545841101a085a0000003c10059440742e2001507000729180144c0c3c2c20801e035100300340420420b40d45c0d50ba0000b03030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 377665485 1250 377664235 377664239
    0x9010203010f1d0403140405120c10170117010612150501050a12030503060d080715060603051b130f0f0509010503010b0315040305090312040e1602120f120103050601 73
    0x841d580103907001e403100c40031a0443c808a0401480c19003401130000f41004011480c500c1c49040700c0040d2805001d00900441e1407825000303095640b83d0007126070b18441e0702541c000450450055250101008851340604a541c2c20b000e50081e02010404000400f590f0b680000103186c2d401e01d100c0f0315102e204490940003000550549800e40d81d042c4c0210788a0f1a0040d030400414001c1e4107690412580b6091260f2681d680400086140b08a1a000380c840d100018040081100c145048120030614140401125403604d8084045450456074107410384101c0b0300d01c806140d0b5540103072101079241c80c01d800085840711403006080704954444c0200e1000504203000c289010395019004d0042074000300818690500001d698081c0d603000721404014002c0890140361040003121000000603040b551241d800e1108482154084e1080c02a0340040c80080741d40080e43c4109500480c4440d0f005021b2012642001e545650004040181c018010414a00c00180400445008501802c00381800f58 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 377666735 1250 377665485 377665499
    0x3a0203071b05101806140f0c160807080607121b0e03010c08060d0204180b04030807090b0c060c0f0d09050604020a051f0f030b0d050105011701110904020a090e0901020301 75
    0x124408141018415016256413070740520110300d00460f0520b140417040e94081c145201c00301c2c07080c80215810010006040c4a1058001652000054050f14110700c0c040c0e070ba2043e661940868010340031950403030300c042076945200322241800742c00079010014065400d030352240785007144488000c001c01e0904171400118682031084824404290500e15442d280c900005080a0b0074101c00a124541d102400541400720154001039198800c3c0f10504a08207803c010700120001c840f0900003401007000450081096030a0355405007400c401000c0d50340f5516440300300c81c0c002d00c00010003a1030034400304080f82038900985070b08030b0042c8040e142600301401031048a0301c4a400c046c1c058902101c0d1405409030034181d000010361945840b046c5500c103054200d002d0072601c24083d5024071440070701000d1141c19440b250403600c5c0b01d03112507201e10380d600d01c2c3c03400c1c0e54601c81e00300c031450000c0c00489180d050a8004094840c0585001d0824603201c1c0c01107188204180c1e80030369a0fa501000621400c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 377667985 1250 377666735 377666749
    0x161202072102040f110706020c0712080304030c110d0c030b07092405040504050c0912011a1915021e0705150d09060608010b033a0203071b05 62
    0xa000024010780e0940348291001e4403800812600900840e81c1d410000702d07500c103a03880f03543c0c031000c049551541d59013681441070194005c00d080c607086010300040010030054824682c20610b03400350486041d42da03580c40030f666690f00e011040c0c80c0d1800300d03d00784084d0f03030f54802d00130a00c03480b909030078120909504241c0c134120001486071040c810307025401c2c08489501d00410800f608825080ca00740502d01c4011119030081d5401550400e06110922400c1804c00c006400108000c1e203641c0803140c000d0005500b83c031000341a40001c2001c61900c0c840718100300724104091003081a1222a05a6801e54450f80008030b1054200507040128034440c1c410312140e85900314040c40c03004000d0369082c400003e0514503174440c000d4414500007502c024080444e0094110990420800c1040d1940c902140d03029114900341203219000e0400607904403c00421100034105071030a00600c00090403104016404070050741009522045c480d0800145c07608440140304520100000449440e00341030224ec = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 377669235 1250 377667985 377667989
    0x2150a030f050c030408070311160905061909110c0615030d050309060c25210512151507030e0f01170c0a050702030a0b0402240904090816120207 64
    0x401c40c1888184400040d800090303940042d00a90159503518007894292415011503528400d9401141c12141d0403140d403015110880f41c6451007405255a07580812050f19203480c81380d1032400c0415001c0c4410407640d40250401c02207410918500861141b080c0c1c5008411201c440b40103059002245040c1001e100c210b11141641c1007030350460610304c140586800e03000b040c000100070080342c1d01c40682d441140d1403001c1907a41c55840080c2c042410f0207070b081c60f58400c0120350301d4480e0300c00e103032400d01ca0011145c0c42002861902c0c1c1a481d024642812102d5540c820f80c0c1c0201110052881001c5040040c0b00d000c3c881e4a540340a0f18804049c881000f881340501360602c03508800303103150409103001c05540b0000516689a89060b00101a1041c0c014184003940510035030b090f2a040154911405028134000c664410313892880900e48aa603482542000701c1320300062007082c0342410300b40c001001041c1314489441c00c156000000000d0f412007100b0641c1c02c49010301440d00303150b4040c488100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 377670485 1250 377669235 377669261
    0x80f0403050f121c06182703021c020a1703010501080f04050a1b0b0408010e06010902270406030614061003050601091e17070f0b0304110d020d02150a03 67
    0x446003c0c03c600b0b00e1410f018103080080d00407a01a152008001030b030f40004080d24941501141c2409003010b44001069020356142c070b5402c07446440c0e00c5000b4589000c2c58400c7d03040d801800c06148800f90f0080b580c03c0342c1408000d51107152882c000040500c07030f51040400d20f80c1c01e07a944079031400d000101050409000c02c2030000e4039405000c04581d0100300804460341048145154503054801c01d4403007142580302600480000c600400c641e101908444030301c26000d421903a090340c84408601c103c0c8100c185100c8480c11101d80403e104100c4020301c0020b440040c000a4400c0e541d49505003502d0a04296580000a80c0200201450020000c90440406d8a03040003a482c0010002c2c040004500a03032201015100c884c84400d90900711f0f80001d040041d040032310400130204038a9a8014600841101c58401c0c01c012841c28189130a503449181c110314141c041d044400d0a200c404c5002e0b582c2640c02c08501c034030040158403503411850b11b45403d488410307502c42070a0300050440f400c014401c2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 377671735 1250 377670485 377670493
    0x5070510051302091801050a020703033b030c0a0b0a15050a1404020d020c01061a03041211160f14090907030b09160608040c0605120c0d0603080f0403050f 68
    0x1010034640284007150380b80e0b040e2601405511062030540d0040f0310245a0038981d070a0404208601e0001e8010301411846a1002d101a08412810200c1229001400d110300c8011440c50740848030034203101c00d524410001924686080c1601c81400c2241e50311055601740c400c03105005508e260707489080743d042d82c8580e00340388490401d400281107d10521a0100c0815164440c015540c1e4641c119080e80c440300800f1561518990b150342c0c068661231007075800416500c001d000280e1004801c880c401e80d4441c0d44008010403855050740c0d030301c0d5461002515407080c3c44d031a65140c4485142ca5000d041d410314070b1040b0518011740b000d8417044001a0714021050f890511031291000540481601c1e80f00105240c00e03503501003140d03d000307104512061140d180201c00215980c00039403850045014268220740d45440b1002600d0911901200c1041c2c0302e07640c4001740259103403202601c0010044200854016500d4807542d40e290002e101c07001965500080070820850704000541005040c00c0241c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 377672985 1250 377671735 377671741
    0xc090504030c06050a0f06120605071812030909150905160207030b0606160c050102100e0a120210020f0c01061e0b0706020405060309010f05010503011b0c06020405040c0507051005 79
    0x41103002d548a0041400340c4a5011860301c400c3c5c0d82001111841081d010003200e944d40141c103050074017012065803450300e46008a05001d10404c141c05141e20448920100103103412101c0f8100c80c2821410f40801c49025400300d9000c510b80940c01350a8040204400c0703242c10120780c88102c41014042c0950781d500b095440120b1500400c05a080340e80020216045a5445010600f5842400e10300c45a405480000d0300802190b030040f031042c0c80080c0d007280c0c80180409101c0c81140ea46001101041d4450f00a14001404000304d40140e0585841070340c004a5400030b40000f03076080907618103031200d00410100404031007440b40c1e074024495454010049600e4150403a40c2003030700c0c001d500d06e20200003410024044a81c045400501c1c01a002d00e6803881e1075205070780246100b4642940c43e500780f0340006141d01e01401948056121040841c0b1001081c0205907940c48040c1c1049480340c1d000d103c006080e558034458006500a640c80d040e40d51440f5141403800c1c00c003141031101e0014a0034080c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 377674235 1250 377672985 377672987
    0xb0f0402101b060e16081c0c0f020d03020f030414090a0204031a07030b0307151806090b0a0201060e04030206040b0108120d0221070e0f0a08101d06130c09050403 71
    0x120240e02d904407000068002011411500340803020030390f461150089500003943d00c50000b540121042d0002101c007120754506012240d090405001424846881031060050720303103014100c0d1514401e0040310b1641c03076000840750661304298080051031700703204d01c04009402c221780d405602050103a8218a0b003030540d5140c950786070b44c2d01604064400010b0005404034044e07403084034101001000c8400f01079540a405203074040c00d5100500140c401c00c40c0000000d47c5408039001d54482d61501c001003400c00302041081d4100380d400200315922103c0010b610b1800286081c0554007076409000d088ca810704058400d00c1b01030744020000d50020b0038a481e103403404407c0d298401000440035964a0319010034500100080020200c565180410b101c90300350400d07104c805043c4203503110762521404404102d8040c4851203200090b8000740d5040f0b1a044041d404072440003203a5039524010716003080060f150040071100c0132211012001c02e1410310180a550b4402022042030910051411780d074 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 377675485 1250 377674235 377674277
    0xb01180801050a0f140a090302030403060911012c060901090f030507170d08011a0c0607020a0302100207110409061503030815090403020c120c030a1a0702010203060a0b0c01090b0f040210 82
    0x241010300b5561f031100b40c04240c402d100301c4000350341110042c0450f98850922004075100e0f500300c0ca02180103202c0c0e40c1c000030f00e007040b1140f1440450943c4c0000041c1c1c1024040303154003072480c81e410421004004074248a80c02c0d4000040c500440c01481500d04005580c6004514803c903005d0036032201203004031803940005032a05540307000e1800c0280300356400c0320700400e0080000303a2005005032010000110350000e46400194003036400c5804409108840c0e20491003455000307030480c81000d013452101d0506400c0130042c1c0b8410140000c0629519594003100315aa40086001540180512048d21800d150f0020805002c940c090000c1c103150384e01a554010f9500c500340074524000b00441004818001818581409000d9550f640810b1400f05044404c01c50002510790440740031910302881407007a0380c80741c10302805408200b07081c03421820f52030308064100d440303a41d01e660030480001c03000710038a0f014500701020940c06041600c10000c8a03100a00c5106c2082421240201c034042c1d006 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 377676735 1250 377675485 377675491
    0xf120c1009060f02281e05030603030909010e01090e0106060503040f11090106090603110a0f1107050616060c1d0d020a0302030f0304031203020c100b01180801050a0f14 74
    0x2000c0011001020300d401c0000d04004030b440c03504640b000c21402c80b141a1060315004002c82c0c820302d09920300c0207040640b00404e683c034120b521101d404590201d01c1e4014001990000e030002d00310b03400d10400c00b002804480702600844100c4106c0001007000c11000d01480713000002040080c4107050802400504d280030003400548083c080c5201c031810300c0065494451506c1c0c2c05461140c2640c0c584402411200c640d2003440d000034601100d41000301e06d104169020114959940d246002c0d51080481c1d0a181c207019101140c020701100146666481c0700a000000c2d080c0c03260b004138506410480f0440703c1d41c03c4484144850100b00000300407a081d0080480202201c00c05420074890000c01c1e00f00300a504003e4161090000483d48a03600002400c102ca11400c000f2640e034058440480980c047d0040008255002d202414005021908158002001850001200395071607051b0000720301684d104110b540d40d502c043c007050b603910303000722060411244018881c003181c80a01440c012802 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 377677985 1250 377676735 377676763
    0xc08060c0a0503190f0e0615030703050c06030705040801020301151716050d0605060403140d0c050c101b0303060533160f0b09061303020318060c010c020f120c 70
    0x540c07884500c1c181141d01c95441308582176130030400d0b441410a00351769036005903a50103074504808035000d0640303400144901500e51080191081124110610682c2d4102030103050500c00148804186201d00344007840c02000c44030f2010909a4085d0000741260429040800170501100f04000d85ea02003401d030748090100ca4589640e0310545942c200c8010480e681200c0c0e030018002400205028000490700c141050003000d0361103000c02c110b01500c1712030074160010f2070341e0048a043c034240c1c41c20050091002c013190070109070344801c3c3c401200034100401c1c3d049012941d2050244828244880c02d403030800d0341045a0f049001402c0c00904036111400b80500c45002d0015000b0f941d116003980c408c412940c4a401a060a00c3c60700d4100d10010080300da03495213102d42400204644030b031801d48e034100e98050b0051807400001011850611159041550304254104899464980309101d80652082e03664051f108078004100c2d090700b0403100040d0003000030403d02403401d00300c1c80403030032100002031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 377679235 1250 377677985 377678011
    0x31428030b1903150902130f0b0d030f080f070504230402040326030f070c140303070513121e03020705150414040e0c010e0303070605040c08060c0a0503 67
    0x4000045000c1d20081018a80003001102d520009020850b00401580e01c900300c00050321100c2100d400450300310b0100030b54861181d02411030340d1103ca50141c4508540c401c008031f540c10303a800203e030711040300000850000740b440300520781d00b1b42e22812460300070080b4030b80f0b180141000d881c01401d9000d54051120400c103203003100c03d00030300d031000e007200e00c014080c1065441e0750381d9046c02924810a4185047c083d0740c05414983c004401c482201e01c42d4801c0d080d140d68030f8032068030490303c4010710841161001c940307004021444200b000914801d02d8079030340b00c40e5a211203101142c101020395210700f20705041021400009082c01c51105041c07180d610038041c0300140f509080745070030750650050380c100074400c3d081640110300c0e00051013510645214030742c00d255031105000440314544451070140c0c200c580829030b07941c0f09210710940941e0060880341003c207103071a800d080b29000e84040715034440f5a03004110848043c4241644030203140c404a0509140f080003401900c0010801c0401d098 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 377680485 1250 377679235 377679307
    0x5060a05040f09050402031203040302060a1e06080c184609060605010f09050f0d06050a050109051e07120603050a0506010302040b060403170a02030c06090a0314 71
    0x4411410303100245964000020b0700c03a070f600001c60040c0b00a441c01c1e0b00901480d884c40b80155040030880e8003803640b55000b081d00b580c2c0c894081004282c0300c642c1000280618040718085000360290700d02400d92000508400c0d000803003048a00c040005c106648140442c00704100c908104a0315515000040074588210540d0200d0443c40d0110385020303058880c00c21030228000c18a540281909881600200034690700d801c0159142032840c680c00000419940080c800c501b0114a60041144094512110b01a4a6452000b03a5400302c4c1c191540320340d40d000402180043d8080d16402264a92510035140c207034040c12401000000d001e041030001c0c0e50f44480c4130b030300540e0010009507042019525440894902162200001c1c482a0308c00c50078028110300600d81601100c017102c0c2d004019043d16401424807041c55001940c500c01540424003003684100d0050008034400c03070340140508001c0d001454003500d02100700711000c403888d41c2403200001d2400c040d801f0207900104611503485183e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 377681735 1250 377680485 377680487
    0x12030c11030705180f0f150114090406060810050109050105030c0c0a08070803160206060604140a030f0c030c12020f010813051b0a08150412090f140102061f05060a 72
    0x2062035000a070080d0115060708000c0d103038002c0d254064504140898a81d407602070858007010740558090301f012070304441d2400c00750301a0a10010545480d508a4103101951002130216070b0280e0140010804c0c0604125404040c5001e840180500342041c0021906000000700240001000803100910008034400013100401410b140d076503022202039a5451145450211904151000d50b070801d802550135902c03a00104046220f0343e80070b817456080903c3c02304c1d17290041207801d403641e812010080e004004941c0041051075658010241250030310314502e0b040104010030703440f06a51107245114140142d4504000820f2410246801c0c417940e1100016515444031a0200525621030b0512014001c1995610402d031030740111a0020040d95071041c071910380c0b81100d5446504c50759040050300280039460a00108016480c00f14244e0780c8407072103214051241d812031000070302d45102d402e41e1980d040003620740c001314810400007032800704039000901507400c2c001d5a20921000c80e42640103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 377682985 1250 377681735 377681743
    0x418020408010203010b0714070503030d0c140a030902130908040b0703051606050a0605010207050a06080c1b010b040b0d020d0b06040b13060f0e10060c0f150f050112030c1103 77
    0x5002070500031562965103039401402c640c411a0b040300c0044040030202a41c1d580416107404565015000c0c6150200c601140c100928840116006004003400c440c031003e03c20002802c00700700141c900241000307090041224240311501c1c0300c0c21080c18100494001040c100070b4404480100140e039441c0c15042c6025500360107803040304403e20300726040400c02c1c050315400031405001400030400c0600e89071001240c0fa5882c501603550003c02c2654200f00e00381c800d022155100d0481c3c1d450328280750315200803d0f83c3c45914040c07561260345821081c0351900c1d052261038000c990032245c15803801b8a550109601e040501c47c040c00341c05d40c4c000029106d1700c131600104840c050040c42e51000801040810000740624001c1c1c00001900540103d038031585001414015101019002e9003d071400004695890034150210b40c01c820040c2c2d0040029044c0001024001e90f503040450780c0c44656240384211003059100684120b0198451000b20f50800c0700c1040442c0c00101d000382069015001c207180c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 377684235 1250 377682985 377682989
    0x30a0c020a050306190b030309010503150f060406020610052b080409021201030605090309010c0f0f0c080c01230d0b06040f08060901050c041d040201020a05190302101104180204 78
    0x40c0148800c00507038000d585a51803017516071725410803a1401c1c0300c3c2815945e0041c104028040303031b42000411041e8054000a40305610020003032034442803040c010904c10b40055126502691104050150f1a20f01d090104060801a9035250400c1c1c004c04000e0312980c0e1401c4400d80111041c2808030034003070244200d078050140c0100a40d0f854120000080010f10709110030f5034030901e0000400d55200d408021aa44864141d44060b003180d80354403080d0b904099940b00311410341c4a09642c00c00100545074403c02004900041c080300381c07010002502403002c0b900501c85098181011802460400b02074038101110b0342c900107460034020020403154032850304042e400c0d828100c00003d4000c1d0000789244110b1340e05c4000c0c0055100c170440a00940101d001d640030003110540000115404e034843c440d0710500510445014a0f01d540303507107051082682e4013990303000800104405141d01003080d04000c445100307003001641e00e03101e2188540d020380d0040713030b440034040400d1554a000e5030301a140 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 377685485 1250 377684235 377684239
    0x11030f0702070f080307050f06070c08031302090406060501020d020f06011e030f050105090d0905060a0f1205090d0e0328020d060218040515090612070801090b0105150c030a0c020a05 80
    0x60f61512a80029503035003145e00121034600c074503040340403042c0000c5105401400380da140c1024104243c0e07260703c6190001030490040000c44010b500160b40c81150340760059020303600004c0c0150600c000281040c03030b040020400d55011191120402c0d4000850904442143d20b9880d000b88520b00c900d040c0d1001c5d540041d0095458000c080c003409819441140102c01c031a00700c40400d0500081550020030f0351188547c8524280943e60116000300001c25040034180380a0b45425461814402120000e8801e95019030084209201c0070340c11010742c22207180100d00130300f0324010040940010929007010009150503044800045444501201811a0340b110095451b0b01e488540d880800035056540382c4183c1c10140400c40d500c074403843c00e011829014005142c143d89a10a00c600000e103181058500d100307140c4000ba54030400c0c801e00b682e0701e100390704400c0a035141c081048803d15408010040b000c404100d28a00080000100e80000c0b60900f410303042d40b281c500001e4000302c02944025 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 377686735 1250 377685485 377685509
    0x1206011b08030a15080703211b0501060501080705130909170a110705010c03080f2203030b030c030303160e010909110316021b0402220e0f090111030f070207 69
    0xb62008844e0004c00c0307800e0301d8801240a071503446540d5a541c3e006484090b0202003442030441542400c2d221800306440c0600b0184090301070094807941c10742c9620420740c2d240c1d40d100c1040c0400e681c08050305420043e0703440c2c00317404c0c0491700c0707105a04102107100b118031640d601c001c42020400150203009040d03405450094880700f1052001c0c0c1441c119007071400c0e00780034007240414290301401421220b9601950f980240d69140d1010352129a40504a00040302d40c1000c0000c000e1002d100502d122842640d000c5404542401410b20b0940d100c86114402d400170f10821400203400c802d5103503100824a007024801240f003005a407040002e8015500d00d5080012244800110100843c0034000790000c0041030680d406e01280c0346c01d480ca105008140e858414840145016000741000800000a103032440d0350944030700348081178030fa0002844012a008000c0104d501c40d5070143c0c4014071100030b00c0030840c1101655040d12005003281300e05908600030452081c42005004041c3c51019480 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 377687985 1250 377686735 377686741
    0x10271502030c0c12070f030e041d0307030206150f0607080f04030f15201b060f040b0903071101120209180610030605091503030c07180509031206011b0803 68
    0x81010b41c40b10072803c101d840b80d030180d00070f00180c05041321100f94001510075600141660121800c103140040380758065200c0001404480040c0a41c500d11039200c0c0003140d50302e0341071802a042113402448003840313016100d092080c644a1a0129a84d10030486406130740b0b01d0b480c5071000c00f600403200d94840d081d030302250110800401030401c204c0f49000f00c0b2401c0070090a41c00100540740c0c5c08400441100490501b03441c407054031030180000b0540c02e5100c151404a05001134070b090022509990400703c180180300c18401d28200203038012501d807020f5032502000d9124050000ea01c0c2041e01c3c1040390032641c0c440551602d0b411303076850001c02041940c0400e010225800e80d00002e0300c440344149040c8851504490003841000c003211806007940b406903072648401c010f01d144486a69070103020400001510400074410b85010f000100e41040403020b441c01d1003021078000502410407a48204502e80500340e01c08881c6910102c246862194003070900d0090800d900e0901c00140652000320078 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 377689235 1250 377687985 377688001
    0x1c0903051c0b0a051e0418081314010f0203070305070804030f0b06120f0a020d061506210903080406051018021b0c0d080c030f0a0e031027150203 64
    0x1024020340c2100c0082e20f250700da50070030201c01c4190740e130f002c48182e40380c0d401036040c1429007000c03068000f1040d41c412444000d8907401400e601450a998060f001001d0602c0f00b07841745240c00200700000c2c07811501281c040d200103540d900ca100e2014041c0980442ca000030009104111006035620014002070f03d00a840c0031502c00d41c081ea0224421406d52011020079600016000f5901958000610b018109138081c40000c00c8495030917541c440c1c48020140500d0240d4101d0001044a0b07603c03010340415440901e407100c5031500381001c44a003010800c00119074041d00151704250049d02c006116202d501140182000d0f581c810004140c2088004076200c1c05a40500340072142201d4030081c81c00e4044c0440d031100700540503503511030b2410100002203003800d0043c220f901034660841e40313040000f180110140c0c109400701d0000983d0050f03038103202d0809200408039181c60318414450400d0314454a6142d01011151101c400945d440041c14881e034405600150840e1704400c541d40d051040c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 377690485 1250 377689235 377689241
    0x71724070909110d0b030a06050f040507080604080a0e0103060f0b0d0b030105010803070f030302040e10051002010e0c10021005010603050619061403270706020d02031c0903051c 78
    0x3031903001040000c540081c940e0914000c08a441c00410b0750245014407a907200c1006000182d1090f80500c110315030f1380d00103406841100d025154a0141020f21301e4545800382ca044800d8016404070303001130b02072100007115801502d80900702c0341068017020300c0000040380144542d41c400c06032807641190000b481031010b001044c2c4080504401d02180e10440149400e9030002e1140381d1312a8010400c00000c90807414800000c14403918000d89020b070303078207036403c40d1682c203a58a054520350404204060f2900074400310052403070340003e0100181c0c02e4942502c0e00740a0000303034042c00200c20034240251003807041c3c1181078800a0108120358581c800140100380c01c445060044022284c00c00307403402ca011010044401c0d660700c0c0781c000041e44801c141c1542000e4442d0010361a515824200714151441030300340c000750301004000c01440c11700c0c000d240050264201c0195081088004440750f005100c400d105c400d01c81001c034202c04c1500d030494041c41030029200e43c55203000c3c0b02e540c130814960 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 377691735 1250 377690485 377690491
    0x18141e0315060f180a06120804060318060f020307110a02032d010501080a02040e0307080304020d0f050a030c210806061305030f070504140601080f151e09090f071724 73
    0x801b0010a501c6104641c0a0201e402c0c01822058092004000c81c51080e0828071741c10400703641c0403814200c01d58544040c0d0300d2003541220041e03000b204100c00031b54421401c0426100c139100410810130642c01103078840c4641d000340365200c02058510780c2c100c040c14000d07131518032030307200200700569540064545036140c85a089120301c0c00e0010342502448004203880160790044c04040c07541d02d655082002c2d000c0982811154a140000c0400109600b8096501d680b40a0788600c83c2008036450140f0b138800191100c510341c2c00c60402180d88843d8004010780e408070003540d0301591480403030011181841583d008e15814801d461400795694000304450b021540c007645c0c18000b812001185c0c21544404890403400188008005250141211503590b00144401c034070900d4001e051000c0789901c2d9814400341d1108007200401405070614041069201c4200400740928001ca85203050b00d40c80c6a02c1911029200c0328254804400107002d000794400780c4c0e02540108605241c04801c0d000c00232 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 377692985 1250 377691735 377691751
    0x308010f05180112020310020a081806100b070f02120730030f1e0507110406060c0803042108041b0305030904020a18141e0315060f18 59
    0xd44000111800c0c10701c40100a00204a240e1075503a00b06000c00c9440150440c00340e9144c41103001401205819100038007100900d41e0350034600c2e14101c01564200301e140303080d115866103d041000250900381110704d080d1241c200080d070340d0f000c10b41000d880c0d0300f80b8040b010758007005110840c089124006520b80403920042d59002000103002e400c501c8010000300f00c03100484d0302c0180d02002a00c11381101c07404000c18140740340c0c00ea410000081c215042a003103400401c0340003500030305120b0070040c1001c0301c04046409204a5080080007802c040048000600c0381b04040041001c1200000308807002c0700410850b25100301440c20000e00c41c60050340c0c20303034941e1919071880b802c5030450308484040d01e801a0056141c07480d0300341440001e51100080c80100045d1441441c040c4c580303601080000c1401081045c0e40740c152008005940c503550300c4100481c600781c07520a05c19100403844c1c2c000c0803126201d0340d4190b591000403c92002e140e00d884c641c0b02c440a848003156186041c0e40d98000c0e205 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 377694235 1250 377692985 377693009
    0xf0703120902100f02100c03150e0c041202030304030f031205010806041101050307032c16180209010512041506060e0d060c14040909050c040b101119030801 69
    0xe18904000c8a16100020790400441c2840160140c02800c0350001c0102d40d00c12550140707030346100b56046800f05c0444c60002500d030180814502c40141c84800503020007c035a04c2c2d2420045a00c24152080748159040c2c01c03405c4224034190758050080e0380c01560003034811003c03500c5900c2c8c02015210703c80c0c04c07024564640030001c24031100c000b50140c032869006100c0c092010b611001501c0507007001704040d0400d5220403072080080140b4403080d160704841c14480020005a44449042000e460b0001500c4503102c482000604c021703143c84d00c040b00c42000010303901c07680d5500480d0b5620514070b558100e01507150910003008090040702500c0301418408010064503144200c8803011400491588100741100800101d0041d5104401c1031045051020048030003140710501c0e500135621130380c81d00e43c0d10120741040c840180a50904100d0840d030400c0240ca084000650340c0d0203444d0f004040251501c024070540008221191a10540c02103c452050b020300e0b0081005d0005d004041001c40 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 377695485 1250 377694235 377694257
    0x6031b030b24010810050d0807060c050906030114040f09080c0f0f0c010503090a02031906050c030709090c14040b040f08010b092208070804090c110c1c080f0703 71
    0x11060005190941e410103164002d071489500442c1e14020280841002c2881a50005950b03a181a000c1ea035440c810030b0b4046d103c400c18103015044404841c664024044100300d00951561450101da05482d642400e0103e0080070343d01240003444203459080352246022070744018410520042c10288030028125003192809081060319601c0100214000c0d501c14070101510390b0040020319404400c0314101c5130780c50980e0f00002c0c941680a091841e84107900f60694003480418068144d0248503d600d4074914107003a076004241d01e950703110316580d450f5150290040c06220300d12090541180c0500a5150b03a10b0b4110a502940702e441025151884400001501c7d903043c001d0051958000308400e0050340c41801c503401aa603111411001c1111114840d00051a0803000d0084180603203280c98603241030a266404585403181c0020134801c02c9a000c8a14000000d80c040d1960019210401c01c4c02095204c81000d0700109030041c004180850020070310b619004c0581070300c5000f69242c07010a8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 377696735 1250 377695485 377695501
    0x3010e01110d021e0f0310060801080a06050a0209090a0b18060a030807022e11030304260d060312081f2106051f080102040e0a05060406031b030b 64
    0xa520010280c40042060010b03881c0c1104070707400342940700c030751000c4040300f03416007054001e2503445900007034543c45002c81800001500741c0c0c04c1c03070082c10190910b03042075418488082e94415174580014155604c0e0340020343c40e02803580642d1032140c0050400a0541844104000644203095505020302c5410101002d22100288400e000300d102400340408507085440b0300780c4652001e0004e90300620110711090402101d0300d031340684d80b90742c041c2c800900c500303c1074000c000340514035507425981d00c20310a0202003850290000f46044442001920184401a25000700e020340d6401d01c1d01c82c3d20b814800400d0084800200c240240b003542d6641c05907842c5080348000c00010894010031205034a4180a442c2d65142074100001e200d40800d06540d0203a0f8848090795005c9445d002e00d620380850781d411070b001076060038018100c501d0083d8142402e02203681d990001c010a800b0103651250042046504c8a0b444103010b16002690810a40c021503a071006000c542c0c0300c111000140c10380011499 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 377697841 1106 377696735 377696741
    0x31103010b0304021309150b0301060b12090c04090c0e0a02070204020c010c0801080303060d0b040f0203062403010c050d0507140307030b010e120601031e2003010e01 73
    0xa45000c1c818044441081c41c0c8100e84a42046c003080000303824114861044010840002501e09000c00006c0c050035455201e03694443d000501c80309c941510f425424490000c0000b00e0700c680c54003a00b03120844a8800c0301178901c0040c448140f084248a5a15642010b8803032405410600d598001904a80c89a07100380800da40d00c1c051900048e81114006004000201c0558154501900401c1a0894000f0000c12038074890f0006010042d0200400164a80190856582d4039004c0c1c20006645144000d03860b281d064000d0040c418030b014000d048406059907140780c180001004c00401400340a440603040c09401481210200d5400002c1c62155805903004a0b03254440d9001500d0036424104840c010500e800441c45109000141e090459501c402e00b8941c01801c0c0c552401001d410000c0113101c152141c011151540303490a11054400d0214020400c18000000302802c03 = true := by decide +kernel

theorem cover : BRFrame.Cov 377517985 377697841 := by
  have h0 := BRFrame.cov_init 377517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 377517985 ≤ n) (h2 : n < 377697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
