-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4389
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:27:37.828083+00:00
-- url     : https://prove2.me/submissions/b03702de-be37-43ba-858c-adcd195024a9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 789208633 ≤ n < 789388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 789209883 1250 789208633 789208649
    0x10303111e030703090b3f100311090c07110307170a0309050a140118090207210f020714030c0607241a01030903051903021902010b100513210c1e0902090406 69
    0x4182340c03402405d45004070500080721020190004400709040400015104111241c030a9103004420340302c0203103807100400300a925100d803031404a0110910500d50b036088400200911401c441c0345005091002a03800c001c3c0a201d03020420071842c8100e056210781ca62003800c01c034180f003d24824601400120303412901da0580000703513000400904920100958201c290000c5c412162250304031002040900c2c45401a03004880901003090041281c1c2c4c0242001400c0740c0302084e032040810320a422503401668035480710415a00c08000141c4540d02c0c010a001e02000a989030780d805408a03806c5503289810980d03905114402c05010384d04640289d01007500700c81100f0306c1c4450080295000f1220001e41000145684204a0050140d00035840d4002c000c00341101c0e10310402c46450b08100c04540c1c40448404000500c020303d01c54034040195141440560221181040d100082681d44980355401c180d1150b160f00d012030001c95021344905034005640c0b4400e05000030060314681d00001c1c5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 789211133 1250 789209883 789210007
    0xb040e0c0d050f2b021f0209122a01081e07120906150501110a02091f030c030209010b030910050603010f230a02030c03010303111e030703090b 63
    0x14501914440c1c9504c0100c04c0b49200e01d0364031040c80e04036200c8902000400d02c5a035680c000001141c0d0039000745c0002280075050009030030700e41a03c0f0303180120030141100b11141c03e43c07044284600d003049002e00d2840c2030030000c00e6070034810741300c0c80b03074028400716616000030030b4003c114a039100701038007883c503100c008051110400c00e0404c5001445000b00441c2c5903028420001020350047c0c4500b100509c548001e06103000d85502401140c610040c0b4080d41a0900500300c01a0005022008051402803038034586013810761044c08020710040e00030080365030007070007005400d0320001071011400b20f051001080c0c0351200c5010a014140407214242000e06080400700c06548400540c1c5010028100380802c0d6250079130020102c1c80152104100078500300014000b103402000300032940303428542203404400c01852a0160b030660070001d60b41c0e076040021000f00341503110707a0030005041c12a601500d064800c2c95240120810080040d10034046c0000800c02d103020348407449125041510f00c02c07 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 789212383 1250 789211133 789211153
    0x9031507200114150a05130b0a080601171203010909030207170c011202071a1009090b06190501080117011103090a14060103020607060b061b010f0b040e0c0d050f 71
    0x54040c001211a0810f660a404001459829406042c0080b140050f0156220070b04010620168185441c45000d00355100e5045000c16201e90a52400900e10303140503201550500005000c1d9203030190f0713000c4884e40400146c41d803900b00704048a0450303800203030005018003189010303403c0140b55804800300b044c003c414001e0b449400701c0c1d0682545030036622040d00c0000c8580400c00c038060107202804c00329070320328583c800680800740c107604018002e401d12080c0303136500424801d480c1414001c445054122003840600d080498024040654a0910344002070406c40000c120040500c07582c00c42d04c03015a002c242500c0c0a501168210f000d400d070039596850010a401d944002c500022641314118030000c10002e400030a40c0d5042e47e60082046190804c551180c0004e01b2144a040e40d2001c0200a19050142031042003221150b22400215000c041c0d102400304607504006c44c51300660500c0c00c00201340700040341e55034000c001101e815032114540e0408134600f800c040380c4d0000314425410704ca = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 789213633 1250 789212383 789212447
    0x60d0f05030a0906050c060a0b0d06060f03060c080622020d141b1201090c120c031a03070f15020a14030306090a02040501021e010b03030706020909070509031507 71
    0x2c01041c1150f44a503602103649081c12505c51040f5800007413681c01c080302251800b18160445114500002c21090901c450703a140d40c001c481c829070108445041050b010401c020060117100d12b15051400c02d11043d142c580081a24200598803450392607440f580c42c01d0607040d441c3e05030b03080c50400d0303074003000800b40710314800503982d200750740ca02041210201a10403d01c40c02084a20380e003008401070034280d1a20804102818143c030941007132103070340d0344801c104580c0c0388107142d141841d9a60105421180c0c10303418603000080c4c80d90700d0080d00b00c01c45c14001a0181c502c2001210308c401040180c1030101c5e0400c81c100122540000d054200080184002d050008091030241400315207580c45500c90040381d00c22032140344901c40c0035030001d1020f01400004000d1300021601c0700d80020424504580019081d80c0c0328031030484c0d100b5808034031141a42402c80d9001c0e8030203441c1c2040b0f4513000401d4000b070b07510b4019084221312200e034000060340c40e13442030000680300144440c5039a040745005200c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 789214883 1250 789213633 789213637
    0x2120d09051e031e1209031c0204080a030e06040806040c031202010c0e0105130b1c0b0a030512030a02040e07052502010e010c06021b0703031d18060d0f0503 69
    0x3614580b0a0b045a030002e01c030482441410000c2001c001c500d0926454160200c607400c492940541d070b0300a2124054281202c1441440f48968802441d51a50305d4001c0040500f5003c40c40810306106010504c9083c000040443c1c54a806040c1228030080040c006040c0e803007541c01820080c080e40b4140000c0245100c3c081044e00d01c40c0c00c41040f06000d00108238200c0709014851300008099a49020540d4061002000703103041d6200c03e0300d407083e11400039080652000102800902c4070801e00c010091032031290b04501c08044452403007180c5942c0319242e8840405d00c07030503442e80c00000454243c90070b07681260010404003c2001d04d0b46042039000e421500100e0a080100741280c44055000f4181c6031800380b03480e416110b400701c042820b0b0045555592031740089500d40e60810480302007518001505254241c075070000c00d8158110715000f0131440a901305800c0180000f420842d2a40c0e41350001c4168408002280300581d0b1030300c000940c6594101c80c0a494031644581c2d0505000000c00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 789216133 1250 789214883 789214901
    0x1050f0103031d150d1506030212150d050609060717010308120c120703091e050607080a1d2d0606010c0f060906140105060901051c060308190206070305010b07110102120d 75
    0x3005241082d50b41f9025810303407250f040c0400410410302c00164841d034481c03079a0350240c20041c2c036508242d28995111494148281c030b40418030303840a420841010350015014000070002140c1d1400c1c0d502d140d850100a003e008440d181c02d1901500040c13940341d268060760048021000e4200d26400d0482015000700602103007038076804240a0311549150981c030300020442d6101c2c00400700e5030780320003086601481c00b40c001a00c0d01d4883c03441c88802c2900b540151403e00e9101d0280134a580c0c1c450300340c100c0304800c011459034080e01c520980e140c0940881c0059000764282880c50b81d203446460603004a9405590042500c1c0c5400c0c0000309115007a07000c3c2c0d00c09021018090010303625002007100502840e0350b0680020000c01440310174014400070209088140080800c5060705ea503111403490f00901c903000212540c0c07030944500075a040000c0c5410103c0d40c2402c20203035040403080707a518883c58901a2004007210100c02490f40700300694070124031441036507030303c0d648034652030b90203080411 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 789217383 1250 789216133 789216161
    0xd0812010e09161d0411060d0e061e01120203031201150f1b03050c07030b0f0405010b04090209010312090e09030c152802040503150901050f0103031d150d 68
    0x395107091164501d00481040d10050311205903e0000242c2641303150000038003c45422034482d4981c0c440b40ca45201070003551001d500b010401d002468001454990010801d0341d6003500b0041e00f601c3c0e00e50f2580110f0540c2c06080002d0349100d03142c004607103548102c16044080c200030500002d000b0342c1c010341e00146404190303114031802c4000b5004907a204060560440c80d10030740c0c2da1541c0000d00580c01014030b05000b03000c0d00c6582e0394035100d0301e1042e00125072a81240e010700007008208102842040c4508104172020400382c48a070b00400d1200005000c01466010710100f00c0d02c4c034500915030700340104560242d1100b02e00d8595401520380e0440f0500814510508000a480780100480c3c24803580000c041d02d801020213118440d508024900c015a526508100204003520180010003ea048800301d28400e418030781d0055084510051a0301e1011042e48014400258480c0080140303150744c1500c410015101400181ca142ea1407214203808000010102c075400e4040d040002d018070f500c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 789218633 1250 789217383 789217393
    0x70210030603120f02031909120c05280501050322050d0f02010612030f050c07030c0f060509030604060213081504050d02031903050a0612060b0306070507020f0d0812010e09 76
    0x2010b0a448103041c0d00b103100c4c0560020b0201c000a400801c2c1001000009803504200a607070300c41c004815540c03415015501701581003000e001d14100300710402030b02d000b8501221030302c0d400b078205031020180c070780281810003800001040c180c0002d520080c0c4110f130f021800203201a071a103001c1c0da591481081d4000400c8083e020200f4190043c41040100c4114a42140c2c03030841d10b035021200520841002000d002061000174442003042040c08081e42c410422440c1c0142040700b28941c0500c42c0d80460308001d020441d4010320744010505a400076403006002d61109031800c05c0450f284025005028a80306041050300303170652002d2024040e80c0070b0b00640341c020340c1c4584101d0316403107282c011800c2241030070b00c2c0d511503c0c4aa84007941c809904c0c1000100103403034071590b0b440a0440c442c240d030301c26110060f00c04282b405100a030382002d40e9003011482d2030442c2c1d0100d0050200c0c008000d00c9501409142d1060041c80c4045032054186a40c201c8020340e119803800000b000c00341c402403040d12403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 789219883 1250 789218633 789218663
    0xf080a150e180c0604140d060204080601140102100209060a0e0a12060b10030b0102150a18050a15020301060e0405090a0f030203030115020a02090c0a02070807080d080f01210503070210030603 84
    0x40340003200c0507103280d882807100c154007a0047c02403e400309807080318210350801c0005884201800442e01a00b18000140d50b50540130b40020725000c4451005000036104000b089915511070341140c07180403460910854010300c0000007048220968000314596030000096410007009500c21403100f00111400c46080c07401800441c1110704d80020240503030300410700d402201401e80d181030360110360f042e0302255009100106001103a89810111001d0307114a1020003001030b0541118a600800c5008504542c034090006195120900082d40696640e80c086100008284002c002c0903030080942d80c0d4441d52441c0003540d03648244903040c895000781950001c2140b000c078108525503001070445d00d1039122004100c2481d80310200d01d00c01d621079513100284e000000e00c000401030400d00050076000d458508040c100c40704c001c01c020002e5841d103006010070040030401000000341880e140400c0000752510f14654440c0d400040e62081854008414440c0d154201406407442028134140d1048 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 789221133 1250 789219883 789219889
    0x1104121130060603060c030c090319060539041a040e0c04060804021221030106020c041104030b04080f180a061809050601180f0f060f080a150e180c 65
    0xc010359511341d01d070b0005400f03e003041080c180956041508215103a16040450b00040d18091044148072042d00c3c40c1000030051041c24030481ea400010316600d0700400c061291841411a0251449880100c4025405c4944a00a000c0c3e41c040e0281c0e9040c078404068480c901c07080740e0080c2c820440116a18800507010001c040305a0301107078034540304c059041d22640c0c01c00c0159500040320f0364440c0b04031f50621006200700d80c070300c0d00028240424990340e541403140090030070200d0003400740180e003400d520284451000044404403600040c501d52141ca9904e4606918070403031404d50b540c880081841540c550070080c48100d100780c1200d03072a440541e2030406655405154850419441e6028010060745120340c00a942c4481c0514081d00d07985004074a0218a10641d0407041c00b8100030701d8141f04640f002034192001e40114100a507143c80c04a40044c240c0c00300400d801106600c134811041c02101c045440c80c050804034000145d9840c10201040c0f20b400b40da4401c81d8184100708a0001a007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 789222383 1250 789221133 789221143
    0x72304030803010806102106020f070203010c0305090d030605090402040e010615031a09061806150a030b04110412060c0c020d14280602031305030313050601091104121130 75
    0x400f14096000707c0e0350303158451030001d4108201058903048104040001030303030700703100e00c64900149480000760341c201542c240749040b60b020922003d043c0750034003c1c0440d990301e18241d5881a4115408100000f00000b02400f424141d401a800112001c0300400c103a50107400c1b418440410100200c2901051010410190170030313121300b600100030003800f52541442c41c030f441c0c0e0311080c090044074040203900c45520391980030240741c500090ba15802400207140601808440c00c100444c0380e030405c0d0410f085c5042c40c1c00311000c001e181658951603100114001c004001c40c0540042c90801c802e5a40d08085456044085140d04a03002d40f00360a41c03034840c0345e0403c105107458400b04c5102104182d031100020360019018800c410004d80203800042d504000440c401e092540e40510301c0d540c1e5182c80c0389826010f8103c0b101007410010689608205c44040c3c43c125903090070503103110f41f800d050103621000d440000503004000d0319001041200407010006495400c00e400080e65078020060301c1d00c2c0e17 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 789223633 1250 789222383 789222419
    0xc24040b15090703020c07081204030c050a08030901082e060315030c061b0f0f1203050603030306091905100510020a0209070507031803050606130507230403080301080610 75
    0x2c00601e4010a88591203a809054080303d400b003100d1005455802072450080380c21000c881a01e07000405200300b250541303030003006180c15100050524100b00701d490703c070700900d031045040014010000711350f0582e03140100c503000710900e00411180091402513078000c0442c01454007117802c0c1041e0511f070004800e1840c04803501b103401043c00d5414100c08440071042508943e0044001e46000c80100703d0116014101d01d03c00c0054002804480c6020300401c0888207904003418581810070060f07440100850342e020104840011281d0786080311401704d55800c500b280d0826140004001d5903000526102042e900f0441c2c11110b45140c2400803603a503140400d00940011500021038105c1d40180003514510b8800e0601d2103a005046130407080a44540d44140c1300c9a00400a000842c00c02c690300c02040106c4042c14481860b01d100301a0044245520106002510201c00b03440d03100c117481554091580200ca59550756912000c50340d03500700c10703034002003811040e0320002080140082c9217030740 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 789224883 1250 789223633 789223639
    0x8071202190b19050c04081501030f29090105040b01050d02010c12050c03071209090203041101140c190213021e07060b10050a11160b0c24040b15 64
    0x54a5a0396490308110000c1c0880d0680c0038031585083c19861240102403041c04d07503214483e240c52070030b201d16140c040751a081d40c01491b560001440842e00807000c940105801c202850061100c25040364203500300f24907000c004d0380d001320a0001101c0c064010500490007000c008031142d032030b1820803402c02d2000d80000c0c04601c1481c0310700009103030200c1450980203242000b07400c1210800c0440d09681c00320720205c4603480701703104002145401003414000b0741f542030001c500318a0310b1f65030343c40801c80f08841340d41800700240481c038400c40c2c6102121044a200410789048084100c02c2007400b80b9102401c83c03060f11007450503404c145051017652008514445408045072103500049000d80c08000f0036120750f600d0f19940c10300c0d901c80ca100d00000c0030f015941c032a034500e05010f0003003000400c0b0740c03008000d401040c076002d0000b002c07146030010b4070704410071260f81c2c4600c40629898080a40e500b10081330040c6001c070102c800b840c20042c031441c094016205030303982e54852410981e20703028000794 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 789226133 1250 789224883 789224923
    0xf160f020915030c040e010905060108031b0303151201091509060633020a06150824521106191d1f02120a0e120708071202 54
    0x11240b4140d044a15801b05550000501c00ca2980310700d400c00e4000d800c00d04081d0310025412a034400c0850945114690340c0000d075080d4148100c07410783c0d00d5441c00d10706214096030504060022000e42c40740090310740c0410b642008250f08505034001d4810034000b03a91003840d1031000542c0c095404500080100c4500100007520041000d401043c0c10b041103400847c07007007401800018080b8032419034506c900c07010042140d1303e000c0d0300510300342d00c0c101c030310700e071884401403005800c2140c003041c035002504d004100214170f81e18140400311850030b20180f242d0039440c003040045480900c0e4681808100d03440d440300021070041c01662040d12902c01c1c03114a0340081c00041110b80301601d5000204a400700209a29041d00340d00c1e1006000d0b446c90030081d400c03040340b0010305e600f456050603003110380c0401541444080440b40c0d00e400d00007008060b4140d10307003103000340000d01400f11940840900d4101c0d5191880c0307080100d50b41e04050300803109158a540348481d05030000600ca1520071b40c0c2c5206807 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 789227383 1250 789226133 789226153
    0xf0627140406200a03090c120308070518150403020307060c05060114060705031912140609071b050a0614040f0f14010905161512020f160f02091503 65
    0x40a084041d40c10f03181510761410710400c020002031085034095a4046030204c85810716004100050703105081410920240c440000e0f00305040c0750380f081c0380c0e04000d500c2d421425040c4510301d61130781c1c00d550300040b018401005c0300502d0b4042d0059900030760885000980340c1206590b05020010080c1c0164401c200400c0502c190001c3d003c0258405003080d4241070b250380d109440c1d03401000c659104074440002c0c0d800003035802040c032604a00881c01c1400303104440c040f1b10788003110160405016546030000641c881e4001d00c3c5030b10b05240300c0705000001d03c1381411314036214440c145084a105051a01d1400703513400711b00e03c0c0e078041e0780c100f04001c842c07060669485241c8a2402c0c4221030743d99020300300110b400405c1c030034920080e0285015116080c201581d070703904441580c10003c2c0801007071403508040c1d6402244e5560080b5184001651003094031031012250180005c1444801a0002c0390000c10801c119000d0b08140300341d4601016446280400381081500d4a040790907921180b090 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 789228633 1250 789227383 789227393
    0x608120324061204140105070f0f0c1a160908070501120203070c0204020c010e0c180705031f060509120109260705061e090606010f030e010f06271404 66
    0x650340500000c0115103040140d611002d014041140c00b910840c03205c041c419250f4000380501a400b40f0b19190a203000c1e0080103002d041001600f005100b0004d801c01130750100b284d0400540c24181c200341422001d4070307254001c8400e4095049500d00040c11a01c00055494000105034044c0c950584030189130600440741d550007504005c18150410400b020141c025840740c1c4001e2030190062000030540d40134904880c0d00e000c02254800e801042482d045144c116544a0b170103400c00d5580c50865940c3d00c440500e50309041c1c80c220480c14021a99034002106c981080040107400b20980703020001110704c0103070300c1c01c032421100c02425421070031800740401814080c01c03401055540907618200411921080d140c0341084a8100402550251a0a0000c01c012459a001044400a04080c5408400240310003051304e001c1c0207258039104a941600002c0d0049000c201800200b04522640d030050540c82101e801d943c542820320207800b00f40c1e02e19190250880341200010030050310345942d17480f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 789229883 1250 789228633 789228691
    0x603150a1809290f151e0a06050405030309040b0310021602100c0308161202030c040f050a180b040207140c131406060705190f0b160c030f0e100306081203 68
    0x600034003101d41c1040003800e46c0d21000071100701d490503d6000c0c0350791030007810310401814681102c81403140c1800f042085950000484445510681e40841c40796020000700c0c0c50421a011000d0b0310300e0002c58800c1c0b0542492000c503014034000c413603160020203801002e4030007281c1d0038400b0b0001080d440c0041c940c04491110381e1000942840c0644501d0340b2024036070100e8000392628050034200250801c0507401200061001c0d00040300c18903032492070700317954103840c00c244061134075407540310841c00480ea03440c5c1d41603806898000540d801214241440c4544443d8846050781c4540518180c040c1081c91341c0c4160002c0340150300205030580c40d070804100701c40d0018101110648150704501500d50704e8071003152541031051010b000340d182540b60007209440300a1080702c40c50441c03008610f41540c4007413048412030701130030301320007444402c0350032211800000000d58111204000414000d9419030000084078142c6007aa10009640301c29203000b0320003034070346204402141514401c01001c0c560 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 789231133 1250 789229883 789229891
    0x201020a02280306020d0e070803030a0b061b0303041202190b04050102040b0c0703052503020d0507051e041a01020312090c100f030c0207050603150a1809290f 70
    0x4821864010b80b0401c4040d0030740d440e00102c91082e004a4000c20000040c010142c4045008020300030160410000941d6070200800d601032a0f40c90b010a00030f203480d00b00c1225642c0003003203170f184489034408521554070b500030350302290f042d00804020000d207440440d100303400341c2d00c445221045000503164070740c05400240099076255820400000c4040803000101000e01340d03040544051855800c002c0e003044414030340041d50b14282c000081c280a1682600401e8a9045030440e075000030604280c1c3c607102464100035046080c055002082c081d43d0310030307244a02c1003107034240030078224600c0001404040c04542405070740103015032845140705442d0640d0001d050011900c001c116040040c600c074400303030020800704e2151101d80c64229498002d00c541c0b200e5500051410902d4040421900d10006103120014420400094000c1d13075000200030080101e0304246152010b400840801003001e542c089070282901c200100e482c107074452511207200c050805d00d130419130300c46080030745181c0010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 789232383 1250 789231133 789231169
    0x303030204030302210f070813060c2918010b04060306050105150705030f0c1c050a0305150d02060901020f030d1a0319080930060a060f030f050c090405010212060d0201020a02 77
    0x70041009d4901d200c200100100040c5e41e4070801c1661500340070194094008401c0c0301c804180300c2c0c100041101e611280e0f0080481541d03200341096030342da218014240809103552060510500205104480e00210705940c0c046462403480c0e1103800a20340c0a00c20241c0040180d00103104a043c410803c1000d8800e05070003000395107081e04140059000c11036074503220350100d603010a98170400c0c2d51620406070b2008002d043c420b078045c44040016030003280120006d119400001d060441c9910034030010300891500011070703860b0054500100301038000c491501d06440c1e66555090021300c0d0004402040641400c50f140300d040080d114400641e1020381003035040810408041d21007094004105600b0192002d030001203000c00071154200740380030301290078807414100e05100d00e010b0101560200c0358400701010760103256103803c03400c14064100c0c1c40d6018013400c08101c24424190020315400d1000c0e10381c0c481e46d90794035041001c082601c0801a0040c0e100041403801130428110f4080c6524100b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 789233633 1250 789232383 789232387
    0x4200130060302090403030516030b01020606150408010c05041401020a080d0b060f0d02030a0506010207060207260706050d0c030203010b03041211010e0a05011a280801060303030204030302210f0708 87
    0x3c0d0082142d0b042e0030f0320300f10b001079030350400c000307050008107031740041440145400d1001c0070150000039a03401c8003600607441003040c20003c6c0310340d03400c0e14110f9008014080080c46881c1000c0e00c068000d42081c0305600c0b6104146444002642c4042000007a9540c403155039418200050f090380c0080c007503807444075001307103082107040e041d642000041c212a42000001607624941031032a0f4060300d80240c0100d05644c4031400501c002c54011441006460100c040d81c00e13180001c11000c0040c010350031100a560044550210362594044003e108001d80803400344180152181c08404900c400d119038211454207001203000100784090001c0d04001c6403504002040302d01c40b0f07a0742100d051810306a5aa841039032010200b040c03c0c020040609000134406514007420380110b1500e0707821401840d22400e901020103460941e50b11020060210074000f00259a168034015000750b025010540243c440d00c659900120301036940d15501640c0743c0d100c2c50815a00015040342070b040410300322094802 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 789234883 1250 789233633 789233639
    0x503100f09020301031e03080a24060509010f14030c09031c0306080d03050603030702040e07030f2619051c02030412111b090415050420013006 63
    0x2a92803440241040c4140103030340b949980b03042c0b10415185100078a40321105d0b0814400f0070340164401d644640707a140080395104d000024808540010000001540722001000c98000e600201401c10044281c0f2000c0ca000d02c0000189c4815141200c004580d010800014030110341a8010f40300f41c05c800380449400010b031102c5c406100300c021141100099440108202d0b1364400c2101e80c40000146c1001c0101381000800b094480c03040c60006401a500c4840a40c00c130f81003041884000c2d07804c25412030103801c07a450250080040b00b03000680700402c9103410380030702c400b540c2200d418001103c500c59030f44482100903980382d0000840400828002070404c0d85003070f1240025032040c0e2082c202c2c2000e91502c030a0203084414100b41c90036480c1d1284155070140300d001e0020202007041203e008000341d4031440c1948120518400c2c01210f942054107010800005002411480e603050060180c522001001181d01c2d01c2000d400e0004145844610381d00d0411200490709502e2060a01081c0d69413 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 789236133 1250 789234883 789234899
    0x11130e010e010b0112150e090a02030f0a0309061407121124090607091e05040f0f051501200c030a0507030303060b160201050a20010b0102060c0c0607050310 69
    0x1003207a452500c00e94440000e42855a4084950416564070240c200300380c404071500c090a508060007107103a83e24060b00401d4401c00200300040310f00c1c0d80142102c8010b00140e00042e124079000f20100c0204100e09030200da000d028494245cad40404003a1110b040140c035850b10070b1720408006110f030900204007407888120405100103081160090300104070403014200c4104848401402c0901c40d4010308240070b480d5500540340e604a50205040490521003440c40078056903580c1c1c0700300d60161a0120340d0312440c60b990030004016103400b0007048590b07161500d0b05603230070b01c20034110700281002c1c08104034803030500e5005400111000403500e1903020380d4042403908104541c103031110340c45005e08104041e85402010050b1540e1040c5070309189001e5190340c00032200030380c020705010001c501000018032400304400c01101c2010031200458101032514005c00440d11340d540140030b05000034440100e400c0c1240e148120031b03001015180c2e2008412620b41c2c102818014407007010000009080d6 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 789237383 1250 789236133 789236141
    0x4030c0204060e0115090b181003020c0307060605030115060e100908070b03041202010c1d0105072f09060f0f132a0c02030d1805040e03030a150311130e01 68
    0x612218181715088441101400702d000b194000ca00280c002c108190400d0b14000d030510303e40f0000c3e0380c02c401705015000194040d0142020200c1c0d148000704d41c103002e2005542290b0201e61094000f00700e501c101e05420350380c0503124010301007c00c2c03094803001400c0c18802d409032001202803802c00b2441c0e848d41c40140c00d040e056481180c0c0311402000340428400010b84110070400c00b40020890017003031038009420410503d8400707001c0c0c080c2d80e02c0b843c421b034027800490341e0865106500b14501d0072001d01c58182c1d52555100841c400c080c1c4010300d259414007144081c01150010b02c1c07030a018910100700a2225501202c03550890404006400e4003880d074002e5440b10300c1d55464149248100b0815400320812801c140020040f811a00d84050303100807820742412042e03442c1405031030a0454800c2042c8071035522032303a00a403801c0880d040d4150b000c0003131405901201001d10400e1040842081c805c240c60201502255824010740e5240c6009101d2400c440780d03181000c07441e0710500000900311 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 789238633 1250 789237383 789237389
    0xf040504020f151c05040b101d0c12240a0b0405090919050d081b030f0702010615020109110904020a0b071a0403021f020406210b03030304151104030b04030c0204060e01 74
    0x105417140140800c000420300d0050b8000b500c02c180480040c078005401001e04003009100321b612403090041039140440d10b0869909000300710034208241842d10500440c0d000170000c0d2141d80080303106c151060b19021600004031001606641d0405080c1400c01c000004082e11140441c40341c40c504007103800084a02c401c86038028000b070140044003001c090724a00c0d00404c241c80c200c054003481d410324204581507030f0300310b212002e80c042a580c8118090b4014141c64100801222158104000c240e0b8150003c0702041d11400003070001d40e0300c0d0018403854080c191002544050034078030500101c2c1c446800340c1080d82c040c18000c13a4034405185848040c080507501600160004e90400304400854400c940000760f907110114034052078098000e2a00001500c211442c04180401505012030342e00003204500300101507a940381880c0c602000e80c400c07011014001c2c4d0b0f00307050761070b10002e071700409a800300c80d000800d140300c07907859a0301180c160040d468100c0e80103603981408540c0c003640101c41c0e801b03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 789239883 1250 789238633 789238687
    0xa06110102161a0a0b1507030311030a0e070b090a0608131e021c020108070c14160e0a1509092406060e060306030a02090415050c090f040504020f15 65
    0x8070020300c041070000d40c03802032a0307110490804c101e1417110388414190542c003540000c04691140e001c0c1c03070124040c1c15a580c00087e100004014060030141e40e90013140e0500e00d85003110242030b500c0500728118020240803e40c001800c140401c4064081c100c40c543c0132243c81c00c0951105032654501d020004240b080c59034125000991030114103000c0c590a2031000211130f01c80701c0e103807a030b4002820480010480010400d2540c4000c041100c4001c168040c0b903201001c2e100b10f0b80350072020610350084d620800c5080450703c0c0124130800854440c000050700c2119080112030304080302c00000d40700c00102182d90040d05408000001200300c1d0030124002c0c042c0c4046440d620f082401002039074088161840341c0360410600c04c5035580020200425035041d00c0c4140942d4440c2040d40c0d9007484811640d80300c0741064100080c41c00402e0090404a40444600c0c030080c0307010f4180070440c0e02c102d40c000e400c03040181c80030149207031112800c10760380c0e000d19040e45800c1544a00c80b0803a0540e0400c110 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 789241133 1250 789239883 789239903
    0xd1b090903020102090901360e120a02160308071707060c08010609051207150e12060603120f030708180f0601030b0f04050624041103040516050a0611010216 69
    0x1031700386401c9030103500510380c110481021041d40341342c080c14041200d105a0158070060074440805055401c042c2168040300300f6984a450203410a00e116030006140d0030041c040c0b098543d05e61403c01d03020000390f03504140d84900f00840342d503603010005071440b44021084014080e26000903039a00882003000700755501c43e6001d51600b02c014001c4081d507000548a0740001d10350503032003c8001180c10032520503492790016000100c005990309041c1c3c20300715806c68955021708010542c0024214013900302a41201c100c1e003680720104401c1d01610140040500c802c00110742c450340719010781e540000203c001c0e00708940c8481021072501c1000c6014501c0b42d0050b00042086c0201e0044082d072114280e044a411392603d540c6d0b0303684503c0f00800d802078545060f15034102c1400ba2010814440002070400c00281d480c0507440d6419810868080301c6910901e0403003c1080086e0018204070780e4041d2290055a041c0305003500c4030b43d0b20314940034a03594207200c0d42560058a0b66400003160147d88050 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 789242383 1250 789241133 789241147
    0x1f08010e0606030c01170c040909050a05121201030b07020709050117010b1503010618090c0504440a0b0a06030309090b0607020103020906070c0b0d14060d1b090903020102 75
    0xd800d04030300a00080c800e40240300145480d903004001c0051003000c0001003400740d5900c1c510007140d80555007001080a00c0c00910508000b0700252008480d401030341100c00c103541201c04195140308103145199054264070040000502c00f054140d0030078078900640d044140c03078400e80c3c4120f5030240d006109001086081d005103400038814820301c41d005803541d1130803204d006841051440184030b0107007004031420001d080081c0940c000d90141c14080c2c0705100c040b445400052640e0801d0003642d103c084000b580da900c4101c1d8401840c07030071801400c01b00b000014203440640362446040025850f0080c58000c2002441070244140b0684506100159140c00d50600502800301038000c568803a281507050b890903982c40e41610051582443d0240c1d40d26000340101e040c0e0f0082041c010401490b90340301050146842c405000084007412080100b11281c0705c151105031410b880c40c98000d60480c155802250a14450b4035008110b201c3d00e4610690310b40c0c00070219007000c841900140d5001c00c00c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 789243633 1250 789242383 789242411
    0x30f060b030d022a10080c0c030a0c12051305040506060706231b0d0c09030b040f021203180405152701060f1b1509060b10110d081f0801 60
    0xb40c46240409104d0f805004500400e04051034020050305100e0628005034001544504440c0c0c0040c5c4501640d855075245440074101c90303407064044888103070070840c9540f040e01c500c0c160741c02c00d00e0204102402900d0700c01408010640980415003001c0100000c1c000306500b80500c240d9040390041c091011b681e01e6002066044000d041c2051800a610100ca18800100140c0780000c1d2018000621060b404c5c0c0c0c2903c40170140d034402450440c4010070001400849032050b50428007e81e0b055852000700306030b86489114800f13a062075141840300316240c0d4146580302c554040d0702070314050206007400000070380301202e030180d40140240102481c0ca5840c8407410346030042c4494101a1440d500d1041c0c0607001c0782c014940c074115120411009001d2012040c4290001c81d240e00041094240a00740720001c0c01e02000c1e50317401a18049105000f0b14840d2101e04030079181c05010704500c640340325046980358806070041d0203e03c0d81042c401120007112040c4001428000700028a40c2050a00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 789244883 1250 789243633 789243673
    0x4020f040b130c050d0f0b01090807051c0219080a030e01081005060d090615060311040608071d03070b0307030507030b010806010f18031a010b03060109030f060b030d02 74
    0x5030145080007100c41c40e9071202030096000168018000c103202d684150100c58a00825111001c51820b051a1055001c91503108040010b420380c0c0300c046082e141d800e804e82d0361381d0300d1194680048202c540e201c028200a20f1803840035200901e03800200700d0212800d010f0360444d802030901e50700446000c104058000061202021007803d00803258980a0304124405241d0700c101d41c000c0074005403194000800383c0c0400880d1f036109000304900c00c400c9200140c000300c0345c004c1d0000300e0714101ea2030a010095605542c00c4600d40d6440c001f0b01d0390b0706c0070204c9001072000c0207401204000001d8082540d014019940503085c8019496101e1411b618014141d45014110b8400c2c145440030054090b60320045084d40400c0a013844007a00c01d69800c111000e410021107444c0c050030210000c07041159803280250a0420042101c102d030340c850140c004681302c02c0e1782d0940414141042040041c803d110f100320f400f40183c00000c0d016040b00d020030f09006d0081c01c0c0c04c00503008103424408016100740 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 789246133 1250 789244883 789244909
    0x4090c02010606180509070f030e151b040b0301060302130b0f09010e100206010302010f1214060316060203042702070b0405010e07050d02040203270313061b110301020d060308030402 80
    0x400001c29142c1780c0400c90104002d456001002440c0c961000e002c1c1c02900045040240d20b41210311588a0300b4894045100a072079074070000311003c0c2003440740103108083d142500d13030354443c03186140d213000c201784c0003944084002e020141000f03600288110394000904081116400c0050703646801200051840c0710100e519071184001b4031010380e0480c0e00040f4103054039420f0920001101d0702c2c00082e180c494000b1030701c0c3c000a04101442481a0200c1540d902928040e400c43d03d1a0880000030015200c2d24061440181d00c00d200030840d640c0301c86282407034008000f520020348400284603106903400362100b654030085034000d000c00c1100900c16a607514a1b140e016003603260a081c0012480312645130064070517130300400400c0e408100c480586070840440303590384480007001c3d441d550f143c2c0c01c103441d040269002c240c4000b5940717001d0300c80742d400403581140b00d050501c450742e80c126070391096504280c0c0641d030920075041c81c1d222620071703140a540508205610b91900d0301c1000b1400001103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 789247383 1250 789246133 789246167
    0x19050108010f180921020a060c02070302030a030c29040512130b0c0309040e0f30070611031503071d1305120a030614030c0102030415030204090c02010606 68
    0x102c003000040d441c4215400400c18020000c1524002c0d0b080a45c16400c5550320581c00e240550303031001d405d58002846c00760040c4100c60901003100d0304141070f03845501502c8007030b405410410503c80081d12030100803022612420101c0450b0070103c000011020001034108504c03c003843c10b100c2884420000d01800c00003126101e440c0200034144c0310380d40c5800380f05688052001040320594541c0920a40f107060034054010410741d5015580c059403080340801600c070381d02503440100c28441e1180c000800b2400200c220704560002d030345803128298000b92041d214580c2c4e92400140d44a5210700960007086d922840d00402c0940104260510400b540158246c101c007801640030901290358245d4012038134100c08288a140e402e000341451450980b10251550006030700102c1605680080705031051a0858141502c1210625689007044841c1a000d0fa00070b1000f0854a002c108091001f502245005801d1039541d01241d419550803110410142c0d4480d8010b00c215036104051070500541d003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 789248633 1250 789247383 789247409
    0x1031401050106090b0c07180203011d0603210915090111030405030d05070203121204211202130e010b1e03070e090406140f040c050f06030a0504020d021905010801 72
    0x40809010450706200307085c2404c4021800803602002400248001c0400c5c9400103144120301300460000d600034080c0308410b021050390107298940381080b45120f6140034004000030b1400b11198001100100003842204004200c0c25075280c4403105070207807120442e00c4072503d8684d500009031001d610340040142035841071004000d83c0e900003a2114031041e4900742a0f6840d007003130022030b06045010381c02c0d0701c501c100001c2c0354039800c1480703102c94030845c080c204190103d0015480681c02c0b1440009450005250081106880000b5402825500d040803406041141c1d20307141082d04490907031000a084c40b020071050017440b010207025009201d40259546145070005c000390581c15400c461900415200c0c001038100f003540d522041060f000c40c60302d0000c174039147c0c2d10140c0d13240d13040350300f16101400340100050310305210400c1c1c07000c440003c0000341956140803428006010080050382c3c040d5005c6201d00243c0c460600311703050280d841c00441ca185041130005040e04206034840a150008 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 789249883 1250 789248633 789248639
    0x120e0d031403100f080f01060e0906180c040c0c1e0206040315060f0b0a090602211629090312071206091802011202040b0307050a0c060212010314010501 67
    0x80807040d900c0d11440340300000d44940f15462118203920441c3c110128819844034080740641001884803400d008180c020b00041d0340700c54130100c40303090645032240d0300d0344140c01007002150040492400007800108480149008000207825a240c01d2030400203c0e18140c140e20510141690800306c0c81040c012460088000d03a0125005108030712018144088405c800c0326294015040b0400401000000e0710059880f9103456041341e00c840880e9001c9070390700d0400a00c060000c602d0301a08200d200d04514a1450300285018540c41481418545a08a0701100014406d481c008090011130381d5000d1462a090003ca03582401c081c016070390f154401e1214600620000d0704d015440b114614040070109040c40340c041c00b4081541081d080241810410000e40300d0100036503003030314001d1380c2d01c008483c031080c00d80040748140d016003070350613800700300140019028900030305544c029480c241c0001c400d00e84030340341242c000d0304070074100c0b00c04000100180110b0071494600c2da52003030020402945 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 789251133 1250 789249883 789249887
    0x170114160302041a0301061701081f02040504050f011d090307122303070e19050d08121e06030105070207060e0109030f060c080c0a0516060f09120e0d03 67
    0x20080840404515446000c100c0030300c41d4040d900203100c0324680081c03410b1400c2003031006400074014040040c09410b18507080e000c5c0d40001d20b04854a110203031001300c8849042c0581e81040d48010b4a01c1d0b034003044001243c0c5c80310709c80c0610488020b40007000c5541048500008413040312414590a24042c040c0010141301004807500e10b54041804954200d20020a456503001d40901c00d9400d40c0f01880307203241c41c000d98001c42c821941c41c1d42d01048003900c42d00300040f0b5000a001080307502074000c4c040c000d6080032448402d4050007018070508195030b80f010b00c60b1170441154001401400d41c01c060400001c90342e4002d0308544210000c1c802da103040c0400a6481c0071a00c2170004000c00409045066401200e8040c041d58021441407058070305801c150700a0100345c14000000348000e00001c203a600454151001d050265076140d2a2010766134208000003091a0140da8050795000c548000210500c11007044d5403007a0302100707443e2595400540b4074440555842e004401a4101000180d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 789252383 1250 789251133 789251171
    0xf220803070308010608220b0708180c1002030c0a050102180d022427090c04150e0f06071b0b09060702091b0a0903110103091a040f0b101701 62
    0x40c20713450049031543da0410402000c0040c02c03a415524401f00070420305010741003c409210b0303a0300d80c54041c200d8a40d030703545075410914824020f405420407014056039250004441141c03003030a104407401d020503095043d0410032180400c5031643e500198540058880502d10302c00031408485100e0402003a401042142e200220401c44080040100c028400f49440c1541c820801603107a40c01020030010086800347e003081c2a003842070346c41c031001404038110001100d090b1100b11442041d0782c44040300640798218000001e5a101c030101d0303407803145a103d0700040d10b40b050069000507005d180c0303092105100349180e00590030f0204100204900c40e20380320222a4186d0b815100c0001980d1184180850002c00080d803a01d6030318001041842079a01043c08801c6d6406a0003001080040030010340c02c6406440c0000d0a1f120014601c850f07280300c01c1201ca030300034004d00c081216458582e58a900d95402100c04107500d075031110f820b0001c520510401240070001c4002080000c100002c0d1007001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 789253633 1250 789252383 789252389
    0xf140904030c02400504030e2106070c11011d15070c1d0a09030f0c08090301090c0906060c080d05060112050a0506040e03030f0402060d020f22080307030801 69
    0x40411482c8a4046485400e541c0f03506640c01140052200c0d04000c240031401a0084411514070307a1510202800ca900c0c4260740c0102d47c141c4810070410b410409006069003511880062400e4000c8084030400c814845d09200709550742c0c46282c014524a40b6222120034411a10704000010145038100e811010481d0607685084544c488039002695189030207101b1041d00515200d182800040c2410f4104176a1051398400001c1a90b80e9580c5108882280c06040307000c0c0000e80500200c80311a0b02400c4500b0400c1d0060302c0345407901803e01d01003400d44001d0402120300030a548400c000100091003064080e159a00e402c01c070240040d102c50000b03000c5c603d0800c2c030f11070351000441c066a000f1601c3d4100f964a6070014800ca28000303943c0c3e001041d003203900c0f50046040c808004e24420010040724850600da0000300c456413907540a005542c0c0080c0203000400d5030800030000c1090640c405044080200c5462000b0220411003812100344140e2060405503c248024800203070081320b480c0c15 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 789254883 1250 789253633 789253637
    0x1b020a0501050c0106050a170f061513111305040c0912080901020a05070b04090b060403080a030506040f0227090f01140307051012050f160c0c1508010f14090403 71
    0x10f40001003007950040c00c6a512050b4004910440014020003903c4000120540d500580e03e5a810f0450a1605c68200721820001d240c071140e64020f0f2494404c03c802108491140000f41064030f00b100521642d100c0c248015031216018030402803481c0c1401440d19a414500d402e5100c40d14000c001010881c0720b04006103182000300b5030003500e9208220344410150840c0443d403506596189030b030800e038080c0c05202c0c00c440c18203843d10401c2c142482110b00326030740404524648600410214000d1502401d21680903882d602c184108200b5400580081072025030500c002101200c244510800482c0120b40648a164200040b620700f08131814112141800d0303260310542483c1c002401c04803141c00081d40b0141c401d0401213229400445202d142960803004c00035900c03039045424105500b03c408600c0100b5200c0d49602c498424504140782c94803902e68150055203e900010611a883c2d45610024100100401980000120540040405800f1415650306900104807590001400901 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 789256133 1250 789254883 789254887
    0x101a060c12040e04060b060a0e010305060d0b010b2512080705040504050a0e160509010504020d0b0405151903030c120c12180e0c030109090c030812071b020a050105 72
    0x30600041c0812518001100611940c6075210480700411490598068603410b00c0c04a4000341390a064080315460081074030b602403e07d640c5401180a460000e04c2e29401c242034111440019042e40d8126010303113500c00b070a41d1a03c0d401d42c504454130700200c0266820014107aa9000428101c400014150001d450018010b980e0a601580e0910440d0301c070980140c50141080340c00c041550020400300000019156050100d901f402061185801180d13401580040100326034905a4014103544425800c08070703103403001c040081e084030380c101e451030107403070810007440c80c90300c4d1920101e0001d0001e0a0410241d50030f5441c020400c0d502d400004001c0c4c000300802002070781c0141280060380794040251786004a54032001048000300322005a40b074076024401149004e01030603090322541400400761f046070f18010200c03018005002080e5444e2450803008408141c1c52001843d04510781d1041c2c0da4541045074009107048001203010000b92621210400145d80e0150710204a6000f403a0050b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 789257383 1250 789256133 789256147
    0x31b011d1c0512070c240816030906060306060905060613140402160f0b010510021203070e15040501090b0a0e010c050f150108010e060708131e0311101a06 68
    0x507150808101d0303d2003001030041126000c02003c50000001d40c3d19000c00c0c07000703036a4030050761070318566503084050200e003440000552050600003016640c5185141c007150504060316440c04543c01c1e900207845864840e1424020003d060003483c3c0c00c030400b87d13051458000728480d0320500425901403882e05034200092480e140ea20358041c0d542d80c040e0034821051800092424a4081b00c0b2440200d40641001c400094107240181303064841a00d25009003500721214036641b0410ba0008000c0ea09001c400e103203691032500e864003002040782855417480c1e9920b052200140468040b075100e040c4e4030004100c0c11540e15031180d245d081000081c03c00e035a410703145180490500086120300e202610984903910340130200b20620074100c1d213828000308012074442000988500040f00c10801017142c640202c0d2458080b402e00800160190400090400003038000d003256644031748040c0c00080f414440c21030030b62424410f401c050305060728100700c00001c0f07051920003441c481450b1441144049110 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 789258633 1250 789257383 789257393
    0x60504030c02040203090c0a06030e07062d0203030a060b090f061e1617070b010312090e0a051618060c060902040903020a030f080f01090203070e031b011d1c 69
    0x1c859203070300070425034a925000900555540e0740c09a19031040c1c1e043c00300000d1586c0a8400c00d0b601d04080400b81c051203040460645450255142503880c5045414540500c04c0000038082d020202e00d07405543d0724100b2000c400d0684486821808064404000200c1d080c0d072003542d05414088152400c580f540051740c3d99601c3c03900d91130000c9907680030000300b13081500e03102103d40c4505440f034041d041c1b040c001d1400e00d200c1c031f0040560051a114001c0e0040c4003088005804807240d072040d1610384150340c0c8481c042c0d59030150a48820072159210010300c40000454058107007c20380034500411064040d84501000c500244620418444118080b00501a9680050b10140e40151003404585070600c0c00a58502c04601f09400198105400d40840b0f44111503950044950510100603a401c00b24004001d6101408450038050340090b68010350b1400d0201e0f8000c03d03550030401d504110350600143c8503141103009140001040e1603840c4196075100c9000004000c0c8940b80c150b0741d40c4920745 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 789259883 1250 789258633 789258647
    0x7080d0503280f0b10050403020603010303112506121e020918040c05181905060103020903060925060203030408070305040f09020c070909020607110a05061b0d1b06050403 75
    0x400c000305418000c3c0d803200708040e500168040d5a0503140e08072229040c46007211b0500031400000c0d03014000b0001080802d105001d1084491b03100825211061001000d515424140d0007610613074111409040145a4011500c1001c80e804400144160f61108080c00c01d09400035500700e511540c041000d8401c1d803202490301c3c01c0c24045491110003410281000091b0103050b00c03603140310300c0380302061b581c8180d2254001da01a100310351414080000c0400641c025110041034141010740c20302c203040640d541085900e00400341704000c2c3c10034403031030580220402c035260004413940150920411800340c3c00811a940180c00c03180080d1280d00510741120070b4480d0350300c456441c0384041404120980d070350380180b00a141c0c1001300c942060750303000c0d04804d40d141500040c0d0f200400b8030a00c00800d0300414160b5150000810303504000707440c0c900040c9d80380c004400304614046902c042050483c0c1c03c01c0383c070f1141c5030182001d036001d0751280c1c0c10042d44905140024001601c540c0800e04050140703107 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 789261133 1250 789259883 789259951
    0x2100b0f0433050f0105090114030402011716200d051c0c091403060c070f0203010e19020102070e040b190e061801051e0c07020f0d0c030507080d0503 66
    0x18542d91580d07401044407040800740105480b462a51034184d065602038002c50b00e110006031540040b5a1800025401d03641005006a05000c1001650140150f0380505030307114201d200e900c201211603201000b0f00c4183c04440100360601d14850740c07050410002540440664a890700a958490340b269405c0d8501062080609081c2000c00c5400d6441e0846408030540e04008000b00d5a40003940030035941d46410380b4002c403054010000440131605036902c0104580c0090008a00c0c200c0140200f032410610010749804480304141d010110f42c1e0600c003100c014542031611481904103501c920403140800340c58010b4019003611000101c0c4880c1d04580b2407003060b1800d4901038513110098201c1c140000c003008695500e0000062450090000d0080751101e0718000d050300c036550700420540070b601c1210281e900c4001c0101d400c0042e075840035107908151003102c0c448040c901c0c614100e4545000307900706515a40100c16101c820700c0e4444240d075841180d042d2950608504040e4090030308030409 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 789262383 1250 789261133 789261191
    0x8060f0c0f1c0e011413150c0c150b040e030705070501050a09030501050147090102033601020319030b0a0510080f0a090305070f02030312090d02100b0f04 68
    0xf485018403001d06610801414400d040e00c5550350343e50004000c240c403013108008284202d100e1031030088403202d900801d521111420b00c800341c40c0c03143d21201c803411100341044003003685070413444d061403c150241d00000c20428006504000d46541d606071540840d001d6541040400b045091015200314407107802950004002c21595844062100c0c844030824040000ca100c000d4180011400c24400080700826416882400103404202c076401d96004c410102c2c1180f00c03e000003040b555195000001d800d00410400400c005500c1c1201c8030391100d485914150340041c04075140d000c03080551140300142529001034804000c0e030008890700190780003240c000b03052004c0b48001a802c500510700414152100050030b030f0322586101c0a9aa0030b0700004c002610500c81c241c001181c250740510300601c000d041d40d0400350f403030f180500d0842c03007110200e2465004141d01c2a5507501400400c42d00a503016041c410740b680d201c08a8404108565201e0285039944145100e0b50070021010440c002c82c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 789263633 1250 789262383 789262391
    0x305190f051f0e01050603480c0a02150c0f070812090a0603090204021303030e13060b0703030e0304080322050108010b1c0b0310090b060d12180f0e0108060f0c0f1c 72
    0xf82102c810300c0c524400900188c2104004d004040d0360003e000e0b100c4e018901c4000f0008604280d00b44000c2700603503c0c04806040e0244250781c600c600c18002203041d0900c03180100311091030200d107a41344c180c60740862111042d0400000e4030644591700070509903134250901045041d602c0c40443d00034428142e03000b8200e48a50404005c00d81d00c0b000718104034004582c1001030980004801040301c50510803032138182010070000303000074042e41005560001510980381400d95441c00c1a00303650144100000e003c000e6001e00040074881c200031000340c0001e2030424080c1d0705000c900d10291003112445410403021788100e8001d2811508003441d003030350160a80d000750011a00c004060880c1410844806000c40d00082c2c0c03504002d00114080358200c0e0700625030f21a10300044c1c0c0c0b44884080789076054021400041422050100c3c0007008024490001c0004c2d03241808a41c10101d01410040c80944130000707001010000600780d42c010303600b0344403ca50b03c90314003183e04c100001e0303807404401003410 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 789264883 1250 789263633 789263701
    0x30219060209040e01050f07030b0f100f08010b0c030313082101050f0301110306040203130b040309231008091f14060613060305190f051f0e01050603 66
    0x45500a0304080b00103a030207001c0c100034095014203070b9004513010580040303600005480a4801d401c40c00d011070f405045200d14106140100c0e100c020b2440205006c0b420064421454551120129005142c4500300c0c0d824440d504240a440388005084106000c15103ca107900703124460b401c861040200044261141108558400c5030f15400d06c5524458a881790422020307007018051030041031403903540685160746400c00c00c002500041c158041d00780a041c5007030001070001100c280a80e000b52580c82d522450b1000c105011641c8681d201201240c0301900e6841e5280c00310301d11000c414a00300b86200f903a0384070003245072440f0140301804401d00c440054101401c29401403502650385510307000075944200512155101d044969007001016a004200b0107100790302981d0460000e810080400444c001c0440c1507842d0049168080341c0da034424040700354852844a600711005045c02003900d46020182c1030306140510503d4002da90010026100011000c04e0744a8441c0d004528480041 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 789266133 1250 789264883 789264893
    0x40204090f05161d0d0c0b0f070606140609040903050d02040902040807060203030606120702010f0e030903010506150d051b0c03071a010f1503110a3612030219 70
    0xd0544400c2e0140340781d8560f01105500c0f8150780302a0b0000c40c140901401e42001c01d004071020200d40a9030489100344011504402c0c0da002000c000103e1040282c5030502400c00c0b6084806039400755401c203c2d20202001c45032240e405851a00008940c0014a07650f58201030b50144124500c80e0b045a100007004204501caa40c083c0050706e2480303040303450a5440304401d84c2c0d24403043d40e00d160303c000140300d40c50107404c0c17003104250311044074070000c120341c0b60703950b0301400b65540401c0c000c000c1d810109010441c1d040901c241039108004450250a54811030780c503a00e144960343c030151a582d00c40f40014100c2c110403a46200c07041040f80400e6958242c1c141441d2030b41c1100e1002c0b40d01c207000e41100d44240c2806004141a1200584221005460b142e1380c280d04410366042c8409060329100c5d4501510080805458013403440e84a00b00b20708484400201610380070303070019514080100004046030315044044050310300c078089a21016055003002c3c0c4c03501e040018501135010b0820302e0441000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 789267383 1250 789266133 789266141
    0x106020a1a060a03020d03180603020315010914010302070c030221060901063209190c110a120212040803180301091101080a09050106232d040204090f 66
    0x607010704800781944401c404280c981a0701900d11a030701403400f140c00c1c005890120310380241e643c032a05108604140e02843d40c14903003410703407000e030220358048100301c12041825914205001d092a04220490034101e012602400e40f40f096810550301040030410424102d078404091034004003020051200d06a9080202120074100100c9004100200741d400d0014043c61043d161100306040540140c107854040344500005c2503000c0344421407180840d6281d03d07541c14083e04ad06603c5060201034401d45505581c0c1c94265042044a007007031604404c50082401d2103003940c020540c440600d48000202c1c41c1c06101c511020300e529001a0000f11041c000004180040d44072034010650020b050405080301e03d0802c01400c8036100f03040075602c1c1d40c40b540e1010f03840304201e00c0004e01c41c42d040d2911400c42d030741500807000a681c09041c450040c1906401c1043e10402122418601400c02200703402100800c40c01a195854030b8040181a40d86d0360151000b030500c4050410038078a0406150000e4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 789268633 1250 789267383 789267403
    0x702091f05090c03010923090109170f071e080a02100606080f0a0e030c0f0a0b1302061204020f090a0504030909110f130503010606020303150612040605130b010602 72
    0x1003060320000716400d10700c1545100300600d01c01681941c0c6410710940142603904145000300b400144106103c0300a107200e00d000c1c448400000030309a119140c14483c0340c0c640036010303032178403c1031000b000380000700c03011984c0d0301d688503044540c407240207882e0301030b80760a0f500300620400b4045524401e0590020f080c90410180ba003043c0b10300c6550380d00c10383da900010340d148001c11220100003103007000c8940010003505541c80c203e84c5820000e100082c00c180307241d20301c0f1450340c018109901c00d00c80c0b0140f01c42e030000c90952603d24200250341c0024001e00c50607804170510680c84001505643d1503030300103101110040c1030080d1514000c11a58003c020865049010403000c44001c035420801c1c0c480d0081d01e2407009625880d100a811100070b11750081015012190f40002e004640b5841c203014401c0208000d400554407424060380403101e00b4580350190340036074024001c0d0500030350b81d000010b070015000340c400034603a110f1441090f074441c1048030182203021000700000d6070710382c00604000c113 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 789269883 1250 789268633 789268681
    0x11060a050c0c0915010305040f05120c0708030f070212070e04060207020301051e0615070807030908120903071809051509010e0601030521130e0403030f0b09011703070209 75
    0x241004402040f074003040c19141500c4640100c007004041354065030003560424010928100080c40541d03901c2d142c012401c0c0008803100010400700c040740300410245000c0e00510004d9801e140e502002c00f84e4500998170060711070b03000403c0036402c1c160180611400350088032410f84062409050000195022601c02ca010791300e003600080d500108110a0045032280c010825003a483d054208841c5000f45c01c5100600f8108100c110700094446004000c450720035101c61030028548080a42050720304814801403103005c00aa196559010a00105503604010070101c50360641205000800042e00005c000e48a0702d000421034a0000480070702c2400188001d00c440d4107040a001d454084c00e11000300304d64451010112030218059000508030040c103141c82c244550501c241e6506000b0f5880041b00d142c4075410700081c0f65060140103000b07080c3c8802804655010000710700c13110414442c0010380201035041003141002402101d460580003407002d001401c0113402e03000761510030218106 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 789271133 1250 789269883 789269893
    0x705120307030c060c050f07050606040605030703120f0c050d020a02030d03091a15130c02150f0612030d0e01050a06091119020a0c080604020907021903050711060a050c 74
    0x101005002046075032250341039807070a8000708a0303076964010b4000d2203224000c0c4030042c405040001821005425860300900080417213007002020704c0700b2904c95410082c043c3e00809014030100311059190041c2c503449113060785006c510744108541600a00b900104035018072004000025030004150720014000c50550705501c190840c1a01202d40101008001070000c16112107114480c0022a50080c04007a4881e209400380d8009604400340f10705111b1516564600c840100707034100f00c04070100044983c145000e00f0f284119600c00c01c40180300a100342d42d040019440c1c010140152450b41c560a2414460190446011406002e085481c815003625201d0000f134110303094002d0072003410003001421701e0000f004032401b80c0002c070701c02d01000398411917402c1c1001410003907140000340364501c0641824100740c810006204005020001154400050401d10300003072503000c030850360f05052a5548135407900d04400001e5034111030540c0240702041d0080140e40002c020800020646c050b15 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 789272383 1250 789271133 789271159
    0x3142401050306010c0f0204020f0c101107110405090a061a04050a0b0906010c060e0a1119050a12051509070602120711010503060414010303030b030c04110d24080705 73
    0x41d402e0100300c56450001d0302c1c541002e00801c9102c55144403040c000740c405407900000c0104c00b400c5074802084840b003540450203c2c40f40800610403e8004000d40d00c120b480c1c410b09858001c0f401d042c80356603e110303903511408201000410819007015a0780943c082c0000d5241e00b000c04054161341e20002d014038102000104000024460121000c100520034001e584640004484d09101c0316401c545440e51880d036200ca07917170200304140e8424400c000c00c0e00003c1688041c03010080b0141031107121240b40820074052540c8262049065450030b100500000120741021840c010a47c810014941842c07014400002408285042541d03002d40840301541d24480741000c944c81048d01c0503007407402c45101c5142d40d41c070a000031030300400300a00102c0c0713080900001c042040000c0e0700440100399684c0d000311071410180320003564000100e400700046920304400ca4401e111b038044190003103586840c20028059003091005810880c240038150583d01c508140340d6448003802140c3c81001008560 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 789273633 1250 789272383 789272387
    0x6210f0714030a1e0501141b12060f030102070b04260a09181d010506120a0b0f1015050720011b0507080d0c1e080f070303142401 57
    0x1102000d0002c0d00074000c800c80360703e51404200228a269102050500e04940415001d0240130600b2000101e08201e5060581c65810f00b0102c5000a10104100b4086105240f03000594658061403c0c0d03584e40420b08003d0000b4024414a03000514500154090209000702522411100350b240503040301090400c404165460203400204400210342c01004e102c07020320310323109401e40b22042c100880c12400381008009031071100c3c4c010000e9030307640303400300400340c80c0801c10360180391204009840c41c0320700c40d12900380c94800180840101b022540208002a140244400044c001a00114407000003114001c006c1d40c000e08040d103112a003510114030021080480c0f0a001c5016140c1d40e0b011000850345440ba030f4100c42c010344031030040c1c04000515803020b1141c036046014651320b00c400744500c0d15020403051042203d41c103e0080c0703c0441800254035004032030000b03030720000701c81d240c0e02107207411030190110040700302c2c040191806204003c00c00038400d402d5100d0211480c10030168081c01 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 789274883 1250 789273633 789273659
    0x11e020405090f0c071b050a06020d09061e0302030c070204050c030405010506030114010501200708100e1903050f2b05160503010603020d020d0504121103120604020306210f07 77
    0x69090300030304128581c0001e401b0138a2148680800e00c80c0c605032a03030b40c400500c1c10030311035101402507000100072420303107540501c007440030704603a040c449088100007051401c0307160070b1003607507003410381c000040366440c928a0103440650364014414422450081caa4004540050780c0c2151590300b40804a407891506010300415000b8106034945143e20701001128803866100c0702942c0c81c0420304000c030040384103002d250060312040b4001e1150f050484010f50440707490b6503441f1103980160085032194002c004801080c980c0611745252540780d40311100307105200f50701c9500c0c03200a051002104258151a8051094441903420825a0744228212030810f42004000b030004104100502006000368090403040320311001c010304004100d140c500844005032016154400809500d030400345c3d01034044002d0703010a0300036506114120900820032038001d01200d1043e034020000480a4036107824029008040c5807010392540c1d940c01c0c01c2d6440d11054a01034016014085000c1101c5002041c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 789276133 1250 789274883 789274891
    0x70306030206070201030f180b011815120c0e010e0f1e0103060c0504031e02030d02210d0e010c0e0907052502190e15010305040f020909011e020405090f 67
    0x43c03900300c441d40110010103011074007070061f5135915176080c6002e1000d14400c0307041d48641c105111703a5060024040014001481540780c0c2ca080c109590184003191404900b2540900482840d20b0014640301c2e05071b0740681c03c02160034a07100000240407402c03040150003403030030620f8200c040c0c80304e0b800913650403041c50115020303a017150010400110300d6400f0800b149003502d032884c1030980307a9841010458907582a88114034240c8260b80641c5018001c106c031444c0030303000401241d21051f0803a0b8140b000080c0b2094903550208046041e84032603000781d10a4107500000b0041d184d8425805003241400c03108140c05554030900141400340240121954480683e078098050388400b00051403809c64440101c0e04041103450500c2c1a0000241d644c000d081504c900d40d03201d00d04003501110b0b001450800a041500384400d000114141d128205145501582c40c02e17240d0790354241184c05022405c84074010781134903080381c4074001c000d6806032040d01d02c01c036130820517070b1034002240c034604400340d07 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 789277383 1250 789276133 789276139
    0x9060d08030424021611040f020a020f0f0106030b0c03090a060c110114070207090b0a0305030301061205090c010f27080114011e15030b03031306020f06102102040615080703060302 79
    0x156071707070020880c200745160300b000d0004c00c0440d0b6112002400d0047e03800405e0047c0250b801046040d01a1b0310910002d0352032120100208103003841d64580c09102500130300700185905000005c905040400e100803a24190400c41c2480305034680c510042001249032031142165107803082c0003024060003125a80034440c29402401d0050404414100034080845c0b6143e1040b8036540000015500380040c6008000d20349517180c0101202001c1c10696100a168010035001140c031080140c0c0c00041c90300540c091441d084088180c1c1e15900da000c0e00d8404111480c1c12004200040c0e802815008000d07110010031031040180d0f80c1d8180d2000c258500c0030440600300408100740300040070401500d0100c0c0742840e01254030240e50000c241150300220f8a1005800c1076a400e0107425010070500c00310140c1c0c0c00c02070102d80380290f500f004549460048054038081d264082641c2c60748a11019181c50300100200540c81c0d82d40715041003d5099400c15010030504800100014000d100d10000c903500a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 789278633 1250 789277383 789277417
    0xc0203093303040c0b070302071202131103061008240d080301140f030a21180b0a0e01020a0804050f0a0e090c011d01020c09060d0803042402 62
    0x4101000781c4442a18a20306506140075103249084940c802185203500007407032866a00e09090800b00780c030300205d80040c00980e10030071441c030000f603001803408100c40c51070b4190030407685144005203801c03c201c1c032007650b99810050a1020b0303080a8000b0340c000d04084070580404009114241e406802c22280c0d6403540b05962200030120000146410365164000c0460369561070300c1d0740b4124070790402c0c6c001c94800c1d400d05440141c00e040280d02600140350450081010007403a554401403661a400d0341c032151440101c525a5407800b5065200446111070f819101290b100c006605940d003080001d6000074980d02c41a4606500106000c1d004580201d142d0b4640307428002070010203400e030f0b16165041410440f00068041000e003006014201d20b40107442e40c1d60410740014070350006828440c03800a080c007903482ea40d0382c0001f0650b100c0710050310100055a00c1d40b0024131451509140601036860001c00c00042000c0d03003981c1d0762003400d1750a554010a0134007004008900402844036809960 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 789279883 1250 789278633 789278647
    0x60e0f010603030212132310090509040f020a121a01060801030506130c18200f040512030c12040f06020a080a080901060512010c020c040b030d121b08010510030c0203 73
    0xf25402444000042d500100f15a9501c2110742216506180c900c551144038482180d054138040c00c0071310380080540f401000072070078100002c2e00182f0141000b07100010128841045403220000303080201104039444411500a09012200409079201c0b0b0120001da0000803541d1402604028140d0b500440144010769507118540d02d241c001300c04c1601c803004502800100c0391101100340142c40ca50220102e80d00b4408844909003000a41252501030700900c00d080400c02441c054030200c41e01100c94180c10300036003440038110f01c1191044025800385081d080c0100301c12400038411200e2041c4400d441ca951904100e803a40703590040241500410420b50001c9845540f6141d0890348440001600c203030b9510010343c214164140002859440740c280640c415014016049032801c25141070011001040000e1749418185203404280030301c0074500000b1075955406034401030744442803d0402c4e208003401800b0403000748507051064042a09405481e07201e40602200c2c2140c1da0000d50401d10 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 789281133 1250 789279883 789279913
    0xa1406070507021c0f081b0d1d0402070c06080108070e060108180c09010f1a090604090225062702030601032004021210060f0c0206091c060e0f0106030302 68
    0x40046000d100310762400b410b000400e01c0845c0304404a03104401710b85d502c11240102100e441032246500c0e00e142c001114084000350400100790b44005c55048002400b505540014002d000d42c0300007410f140380039500403891a800c02095810303140210201c402d450765500030000003101c1200c1d124001410a030118401c032084182890201c141032080c2c0b21850b40b030002180702c443c0264000107906003404401c000341014001010f55404011400070b1804d07000340003040f00744c41248126014141c0c001083c0c180d5441c011803204031b0301402c00c07441c180c400560515201409403403021f2440a03030044001050a10040360061b2001c0d409030140200f0b070f1071900d81030310307003240c0140e06480c10041043c501e0b1164ad40e44003c2034102400d481c00c40003800e10302450b1010020039000801400020f40310110320580100020b01225812100141d0322401e83d000b040e024004480008100442d10001400300b082c2ea811035100b45031344104507014035064000c0d880c26a08144030240c00358211684808480d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 789282383 1250 789281133 789281149
    0xa02070e06060f22090b030a0b0a060e100614030601200f0a0305120906071d040906020c0c01031109100503041110020604050d03050103230a140a140607050702 70
    0x44402800c00e418070084000706162030703001894021044c0340c049011100341d04481400c002400c9410010080b40390100d010035a104404030003d4503440c590700025685405c0b0790841e101034283d025010029050002c60b405210f0907602644020807455400c0c407042c1d4290324152071041c803050f501c625000d0010420078030311003846101d03070708240100f00c1c8481c4042001c02c03000b405580301e9904c1c9982c03880c01080001c01158042c0941c6555005141440100380e4040c11802202d14031000140390200e07540001401804a404003d100d00d001040015003044042249182c0380b90a833020f0080301807901c03401e001d91103006595a88030b840c401007281c1c00e0740320300061540140710300500c0d0020b084500004d585007800e01da0f40bd00680c458810001041428401c0c6064407095040910040d411a81c03000c1c000c041c89009004403003042e40b2100090013080159a03601904481082e180145100001c0d0316441c170120305480074842e5941000608100140c55482240140e03070f06420003a9a90030000c0d03036 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 789283633 1250 789282383 789282391
    0x50721020609040906151706060102030a1101150f1412100c0302070f061508010b0105070303090305121816030c0501140d05150f0d0f031407060e03070203010b060a02070e 75
    0xc1641c0300540c130005201c61050081c40e1031400101c00e02c10745008090199000b18200038902030300b1034028085a030f60004141d900d161001e0070403010640d40c4110b0030f4018044110041c0194024050010f0b10a1410300400240c400c4441d0551541e640041800112881c00c898441e10703900c01800c959000020342d00a88050009180151424286803103569070040c400710b0584440e40c1d210000e1449842031a0301200071324224000340009101200081c1c050301803410082c0c00d150300c80d44068105441502105c9100c140c84410303480d0341c2001c461300d00a411f41c400000201c2c5c03280134070070110355488010100c04c880e4030840c401111400d02c00115004056507040400504041c00f003000030161034020f080c400d1190010710020880200200400c0c51049810180504d0301d1148401c08100c4800c50084503a0f09400c0004000c0749040107034125200e00035014002c0e900d40b04092481003030110042c00018001c40090207c0c580100401007203210b00d400d40c1c1c000d6404000c00f0004041c540311610f42c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 789284883 1250 789283633 789283639
    0x5180d2f0406030804240801091a100909110403081b0f0307030305090607211d070806040b3405090901140411180613030f0f050721020609 61
    0x15108056010030207075070b01500200c440075800300d01802507a94286c07120040b55900e0b034202d031b840150044090054001801040e10454946154103800014051070b0013000c5000f40102401d00b440240080000d0113900417028118145801403a81695a80039207090304d400002e458a842280500103905010404a0203400e0251408090607104c00b8405007006030b000c0d48001c1200c0c0b4110310203504019006004400307100700b0171400316101c2c80e034210003903140b895040001355486402100010041d00e00ba002e0040348510040801c801d140440c9241c042e910603840c55103203454038810120350b40d907482840400e0320010440700700070700c2c07201200e5122501b46040c0b4031700d00700e00c0d4404248410390903044548218540303583c1d6500c0b070500344521841011104030090401d401c910300c02440d6aa139100d034510a81d00410130360082d1410614039030046a100c2c44445070301c191441c220110000484041d0b500340207035840040c403c030407010307141900e404140000b20000c1841e0b00300308090304000001e9030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 789286133 1250 789284883 789284963
    0x71205090310050c220b070c0608100f14210d0801051503040b04030507050304150e030721020a050409030f26040b041b0f080f030715020702190605180d 67
    0x4022440d50000c7c00b0117402032003204040d48c10a10003500000d005012140300324545101000ba08008407004e1080c1e030702d4520101840c1c4460400500300540324051031600f00c1c0803450b00c44c03500000013001d6641c10082e44850203261f0740e80040040c26020080080e900817402c00000700040c80d140c00071a800b81c0710b400c0c501d040640c25100d05107550480c2d00100308403271082d02d030074030707482d402c40d0020f48551070890084c04482c3c1000c251408030101003801c1c070b18525800020101710340ea0343c4001405000060070030807044c1c00c60b003402010301c101c4221030742c04203855291241c00b00c3c00074a10b028001682403803901c0140c4856894810401c001401a00d40da42519002c01e80d603c0f40303038603c9004240781400c84200c10b00b01860141090070440c500035541d441041010005058081d44039810311060000503183c42d1640041342140c0c11025646115140021000c265590450003404c02d940583c2a07040c6850040400c1c0491b03162203100103010384070318545681c1f81c02c0d070043c0319100700103030340510314 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 789287383 1250 789286133 789286139
    0x7050a050303090c010e092a0f0f070227011a0906030403180512060a090201031512031d030c100207090c090e0916030f0602071205090310050c22 64
    0x2400c1d5082903a1618298003e114000100d41e4042c29aa80d10502125015418106070098480f900b80228520487c8911030f01000c1c00b119560060700c0001c046001420782d220b40300444030030036074040c0c90124030510403603c0c0ca52580c210061003001449040740d0f0001241d09026602e40c02881402c0f810500d1802005020041d440d940095400340740720340c8411441340d5a848215080804a401c210300600b80e2001e855485840050326a0f088000b105002a40d07000600040300940380700841002080d00f10040001c00ca0001c0d506100c0440c003d607504200300e2521458607495400001c00c0a606520a5800030f54500d4030750000c00702c0350700500440b0400c59980300104140d801d06486180400d014410401c4600c6408003002d03842240c0401074184140c00d041c2f1441340e100d16000150010000c81c0450303042100ea5411100c40381c0c3c00c00c1038007812880c030300710040041d4000504280203005078007016440050a0087c82d024282d1810340e41e0501c24034100ea07107400c1200c0096a00410780310b139000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 789288633 1250 789287383 789287393
    0x1d060d031805041a010806060316030e03040503070b273f0a0201110703120f17010909051006300611130f06120c0e0a090b10081b07050a 60
    0x14200c400c2840c0c10f4481c08466403c009458844018045405408c08004000b1440109e1082110040f000d05000500e84400300c1005d1039070085e504202c4d01846030702c00201e5005000c5001d4000c02c0d00c0540040700c010076650000360b00050000219030044a203a60340c80d2501d0b01c02c04d00d6401b40e1050a28840da0140940c20040c2803144d40c04000d145030041c03409001513580c0280e202803800d042c040140113051840d0348501c8159480b10030b9030100040f03943c1c9882c2076880b492103200401092080d41c541d5503181c1d05c5800003040d5074802100d05200d841e60340c1503101c00b107000b050202c07000700c3c8079500340c2852000341e1b10711031140c242e051030030400004c034000024000d8031075070341a0b02c1c01440554075504048050035200800c2c1c2c01004c41c41d940040200841a400030140310707404903042c80031903020011042074a40140300d8a603194850f08410005c284c1045ca40d0080180f20000c4070503080a00481c2e0069858940646002d220b48544e0407403240348017031800040c003d0a11900481f075686440e0746403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 789289883 1250 789288633 789288641
    0x2f0d0e010f0f020d060b0301030b0406090f050f0d09080d09180617010f051305060106050a030204091e06170309150f12060f0f1804060b0a030c1d060d03180504 70
    0x100c41e8419400300c1c40907111850b52141178050320524610920350b5044d0b40b642860610020001401c00d51207603030300002c0205100f0601c400561020403100102114030710031f42c48201c0592240f0020307441000028030b107000003a94000ca400103446190100b03041c004418188429090b4240711540c64903000240010103071441c0d081d03580101c2c00040d41c446d4000a00c01135a40250030400c6920407602c000c00410004a4143d04441d03180c00d00d5940c442a000c0140c0c013a0040d9400001043d140c1001035800c030030629165805105046c00801490344c603a4032801706004115124000f070307402400b4078440c904010841d0113041d002d82500701c0c02e00c10030614804141d8003482c000c2414070020000e1018a060100358138044d200d0407030f030341d441e90038152001c20103031080041c00c1d80030610b49002241c103200c02503204d03444000003e8240403c0d070ba228102817031484298402c00050028076580042c140c080c0c03110903401004000c1101944010b01d484c1110241c4940d1000b0f07524041c1c1140019a80d0344500c2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 789291133 1250 789289883 789289901
    0x3180c0a06080f010f0f0b0a0315030303020307140c0a0209060a0b040611070f0303050f03151c0c05040513030807050903160302100c03090b0a212f0d0e010f 69
    0x910b420040c580080e00700d0380104107a20100d5803015100c001d0040002c600c1038901030350544008140c4031100540102c02505007284882c8101000c088040203241d49900118850355541e254030411601c207460f40d091a214a000a20036a003007042d184006140c11501c998100c0c4000b007181d54007035126140b2001d80c1d80603a0108010541c00203050551240c14000c940c020803201080000305446c503180544544034001031116142400400a00050742840c071030401224040e0181d861030000352412040071403842020394202c14001d00008007071070305e07009440c8034441810801c0341074610b5540540f030f0018003500100034400180190030064404011030043d035441c014403c1e03080b501d103006000e03a26105001907800c000c000c440f0480400d030803100300412a0103060b00b0302d9545009440c101c40115100142203c032011800202002492a4014003c11044070f600c01040742038a410401d88026581d049500d1030300203210155615607039510070b9803a03c0c1400000300b90041404900300840e0381c002 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 789292383 1250 789291133 789291137
    0x60e0303090406120203060109050408042d09050106030f230601120905030a030507050a0e1504050d0602030402040606091202040518100e0f010603080d0917032a030c03180c0a06 78
    0x401c81c003580340800047e4010030000340d080015080c03035142d001061003a070040003840c400b0890980140e545241004104400d01e54a00c60340d80e40344c4001c01c02400c001c1c07041600003820881d0402d48000d0a10558826100c241c12501c02e41203400c424000415004003424184040d512014940d4001c500454201501c10009941e6400180401038203c40c0e0140000701000005e100b0a54507941050350041d560070200c1c2e41001d54000c00c403040a0380c0c459a0000d982101e50300c04d0302070401c10181c000e140614401c40d800e2001325100d640440700c1d0b890600c00c1e0800624000065405410f1550125811a04280005610103880904a440c00c00c1490080800a64804200956034418000809110002c1e0005c1c00f02d41d00e540c80c2c4600174042c204d008110240d40c0c0140e43d040140d0386071031180752800034000e140c41c2d18085c00e052001000240c5401c22103200e00c0c10030500940b245033141c2c803408400304694210f4654220313006e50b18070704d00c08002d0300b81305415012481d5134a4a000b640201425 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 789293633 1250 789292383 789292409
    0x70506010b03070332100b0d0f0f090503040314070b0703021b0109050307330f08070201020a09090e0c09240303030702070308180402070f020108060a030c060e0303090406 75
    0x10f504000e04a4084140071a15080420100040d00781031000d01c1e1030102007500c0110007a2a0024011a0807030f042c2e108264584001440e94210305c015080046103a401140070890b15452000d003a09488220400401c160410030003880010309080d580710040d0604800c85e24000d44848011806078045e042c03d502603440386801c030741d0700c2c0700b4681c8600da170076400c0c60302d14181481c11002c260358518038000c10140d50301d9041d0290380c0c0e5081c00121001a03500f5002c1c000d07041207e4901415402240404600003811500000c0040d80140225840d4481a5907a8044a80f60802400050605809900a03030242a40b072040a50700c80001c580211011220850704241e80104c90300e64500201c060340c0250018020051300d079801042c660100c039004094580c0d12a0354100e484c0920822030b0041c0e90040c1b0102d211810b105440c1100c003000d51007070300c1300c0c0466240e00040005166451000400e04102628107000d103034030440f2502003081c0058103c9041151000003c1d06642982d081440d47c4c40013 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 789294883 1250 789293633 789293641
    0x30405150109061e0e1b120106080f0723071a0f19091707031116090b03030306130c020a0209010314010c1706090402010c08030f0114030c01021b010302070506010b03 73
    0xc031202e010705041d812610b14440c6217000311200b0031a0b801009008041180242c045645400600315034103031100300303450200c544c2c542d076000d03000c28015661410805003950004850b980594601d842d0f020106150f610341e0b001076101402aa030107074204941c6500a0340011103110341d04440c45001c1c44c40c1c0c980c504079503d4100306654183d4049034204488509102e424400301d4081c003844190821090030b042d0f07960001d4142a10410207601864103e48608050703421404a41e040d00000c1c0d50f80b079101489070754100c804055480c041528419440310b0f2144001d4400311160340083c01c445840d00644055a4030ba4000400c3c0803003d0303005440703030042e4901e04070113104280f080c0321b00203000c2d0800e0b00c403002074500701890441004184034003a814100c086801d682c01181c1050301d040d41700c40e0703c035620314101d0340c400060383c1c0030701c182a0394410001440d0708134500851110079990041c2d00502d524840b911003030640d04000b204035418541d0810807100440c1d0184a414080d00000040c00e80d00c0c20 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 789296133 1250 789294883 789294899
    0x210c0c030313032714062a06061813060f0f092904060b0303091017090303060114030a0b041107030219021011010f020a09050a0510090b03040515010906 67
    0xb0306441400b5000a5150200d04e5042580440c08107450341000510394000a140c0455802c1c881d2403d1441402180c031518040b03c640440d02c0000c00c0844026954a80c9035074007801490f80c00c0200d41c20091000d103000460f071405414880c48241d000e1040490b01c076a4000c105000c883d00c0d00c801140c40d6441e4070004041c00030301c41c204000b24521843e0100958010404010310310f0000e4001403c8c1794a403a10350309a07039020802c2d1510800c0c001c0c007207003146007032620103041d03010140030300100c1041c12800500942000300540c0c0c410181070b1690f5011603084503142405500050115400603a501c00c9042503864911032080f54a20380c240b640d07907401e05410041d00d07183da00709042542c008000641e03401601c50b045d1250b03050303440c1e00b04104d046032840003030340c0580707514440303a001c2900c08100036070059808500102200e005594040b4115103800500c00014070744800c0d80003280000344100072a4002800955000b40140261403210a101054a13607646081e800040780680b42c0d001481129 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 789297383 1250 789296133 789296147
    0x140c09091605041e15050c0d03060324061206150803041404020313201005030c0307080c1909180e100c030608032805210c0c03031303 59
    0x181c141c00c01d850a0601841c00802d42d126078001c21000d40038040c000c1940d11400741550001d009401c05543e070808030040010529000b1080343e001c00d01c5060f5180707048600034413072071098030707006240e500c10f011100c041616503002c040c0464032055520030700041c400c440f0040003040710b403061801103403030710843c1b03620140d0103079642240243c1c4d00108002c001c4140c3c001c000c1d106012096401589a98418185c0645d02d1460030307001e085050078444003031a1800380ca10580a099044860a4030144640011035140c0021a88a011840b0800208030380314000c00030140e101912401191405048000e14056a03a0380034503600400c03c0500180000c140050000110740046041000303091504100c1aa40e2205445104c0d03a00395241c004103401da05c02c3d00582c1c06410810100e9558869030210300c014628a0782070002d01e040201c8203c02c429100d0001c442e88002400d0130019241c00350031421007150302c00b51101001ca0340402980c018200103002035031080b140d401044004200070701b000380c010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 789298633 1250 789297383 789297391
    0x3090c03060f0f100e1305061b0319020c10050a0632011202040305100f050c0d0b06070c170d020303070f2006010e040c090204050d02060304020301140c0909 69
    0x40c0d00040d00b00580e626003140c190394810b001002c0d002868869000300345040d60160421a03ca950610030411380612030510f600c46580b04000700d8000b955590812580d40141a00c4203800c000200041102003400120840884003454401498604480c03c6140741401184040325034940324800c01100e030070b251051100402202c101c400800900b001050841686075001d00008c088071107200301240d2140b5418a845e0112100840d615a184c0c1010381c0d803401c008200040c2c8500b806001034000880d4007a03207000303030b5402142c03509100c5110610005440c3c8d11710800e412075001e01c0403202180f1040e85050062241500c040c000031040704109040502070204079007554020014031040c0c0740c0c33000e01000c060b120f900e4658050a201d44081e100306960212050a07442050000701342d5406a0343caa0303010714880d0300201c900c2991481c504050380170364811150701600b07050514000d0f0501c074000b15402840200009545205080d13026604202a5084000110046101c46c0c15042c05c0e8480344d00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 789299883 1250 789298633 789298639
    0x41701020f041206060f060509060703090509070c1707020a0b0715060b03040209090a11010c02060702060a090f0f08060105040921050a1101020c0705060c0a150203160c0209281103090c 81
    0x149810442c020b419032080d045400d008800002c0c2f0344c0140b5104a00710005071a00802d1000107040000000b400004c41003030642e0260415240ca4484840140480d05807560281c4610784031490302803482d1361038001a2080e16030305600d40e201e13004026980305240142a205070141d443e414140180303c00250b005280c0c049030f41c0841c0000f00420718400d18454102300034a001003c2d43d0f064400300b10b090040e10300083d040703607000c07441c5030007130342c1189a20003640c151009035078600b655064030855140c004d00c00c41c030b055003242006000605103500600712440c0262aa07510380c041c0c840c003d1102c5903c41010f02c0001d200880d140c1081688000c00025010681c8002c0d804c2c40580e00c2401d854000b01d01c40d143c840d01002580104070f1000340030040d8120b410100182070b06c1c904000b10000b0f54801c4902c400ca41c0540c03480d0511190161210344800d9030040c2001242c1d60f560141020003000c110a0303215584051943c0b801d100382d080c054000000c0c44828010380b2814640d034600e103080d5a43c3c0130544 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 789301133 1250 789299883 789299909
    0x10309020904120c080d0b040b031519020f1603021209132c0c09180303070e010912150b100c03270e07140906041701020f04120606 58
    0x250756507006168000350000441d5640c900142c0c0305460490150400401c10345002c03540e0303c40341c0c0181d4001c0d0003019041d10b041c000b408109007003644030754500c0c031a03014190b910008034041c003003e860200740103c44524010320b402e81a40c03420344543c00001981c00c17050752405100c420107a05001c50500c0c2e4004100b42810042c145001401c9022056a100c403e541c1e98550f51204503062040701e440f0344c0500000004980220a0154884040d841001d005505540c0400c80994264450130031400d41e100280d821515880c1c0210741030444c5c3c0d1003603030401c94609400f29805250340c101129151040142800e60800c1040a505540d01a688244a0800d1000e004252504001d0b00c100e107030b50603c0c140030100a8406c1c2c0440d00c49a0120b101c1c41c103081d01002080d600d40b01800c4034051301d0349440f03101a074405008041141e1141d1003403140c0204061004108103000c416140206c083e052001606040b19441860041d8216a0020b050322020602c02800d020315403107101c0203480441c0c2009 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 789302383 1250 789301133 789301151
    0x100b010504081b03010f09053403020103150e01062106080613080403080703080906150a0b0c1c081014030705130b0909030a0e1210020703050f160309050103 69
    0x69107a1422410380e0058038403604a0000b213075820350114001e0788001d0020031800c000d6040103a90b4081d02c9a841c2c0700258140180c905281580000c8503c19031381c0d102c80c6c0f4803141190b00441c0038000403140c803040d00c00c11440100d00d40c1d01c540070755800703800c069540250410489001d4070010010807002401103161a0052003108804940300380c0c04250050262035000705850030410620440c0c0c405060341c103020501c0401c141d03010a4450003540b80b03104840340d603100c2c11142103414001c4100c070382d4002001403042003c0070390407010b014440c06010940300c001007455401d91000941c1d8002600141b40c40c0700f0089002102450000a0200c11550244803007000c400310b035461031940a02c03071184400c07210003001c00100307401000c00e1040c00741051080d400c12400150752500002049804100600340c161024108100c00c3c52403c1c451000400346c00e000c02000c10025480707500240d0401404206040700417041000400c01c513403041104421685850070000d04150b13036508004e041500b490094 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 789303633 1250 789302383 789302399
    0xb040e0d112103010b130902130f1e0303111204030f03080705030405060f1803190305060301090b04020d030903020307060831033504060b0307080a0803041b08100b010504 75
    0x241c0c0c103417101035101a6079005a4020141070364480c0c0c0c400041d0b80d000088801072600038003402000c807804582801000390b101ca80d60101800d181541d40301111b880d00ac108042842910060b801c1244803090b90740c1c42c1400c41d13810325142d0082e001a941803004560702400c040d032042e0303a00e038400c04c4c91810a08505050796919181c10b0003a2004001e41a51804a810306060600c610750b89516001103d036502c00e0403040c03840500c1110403a002191030b0900045142c00c040c0180162542c1c0a0801030555482d42e007000325032500101e00358108030081c00084010f890800c609401342800380c8070310301c4a150044200b82c12051806110318261901d07901c2105075031040070000e044541c90b082c080408c5050007041e0a20703000e01d582101200e0a2a01070f40500d854120a050086020380e40521210805405043d03561b0358a124000c619400421100c02088600014680007442007200d16004036481c1107182540340382d50130400c0d10b900038402090b0882154865420000020308100341880d143c5602c17 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 789304883 1250 789303633 789303637
    0x2021070f0c0305190809010608030a30090b0a050c0403030804030f120507090f080307030206190b060304030e0102010e0a08090d050f01020d0903090803090604090b040e0d1121 77
    0x12900c24060411089001c1500503410307211142c03401c0040c1d410400019500a081c070509481d9003c40b5442d105010418503004005c0b6001d030310041c0ca5902540840109522980203d20232040c00c54000c03022808a150803406050400d0307000307858240d0641005d48180c81203038800390a00200c13180801041000980102602d40e000b900340c20100d00050101c08292440a540c8940d140d101c2d29017420404416080500c10f07042c1e80105c10720791061038071088070a03600c1c8031304100900940c1c001340000c1d150341c0742c1d01350140c8082d04194020130804030000205001c0d82041e1006c50114800907400011540c0c24401c0307150040d4260300401c8242c445e1748401d4924852920b041c1e0245c40820b4140003882030810021081841c40c10085503585990f1203804010b21140c40c085001858890001032955800403d0b0b84d81c22100824151030f00385411128801030500303440c001e820940750311180b20960720621013000984200d46072251051101140203003000026a00d4039440000c07800781c000348580c4001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 789306133 1250 789304883 789304907
    0x1f06050c070918051504230114010305010519060f0b0901090e04030207033e010e0d050f0d08091902040905031206150a0c08031e070f02150705180103202107 69
    0x4c8500841f001990501e000d4845260800440c45a1400000c00c00c08154440d62003400e03800b2524800201340340540c000d5079490300c00e0201c003182001041c00400e44400c0149200f80b01410b18500030340d50f07513401014a282c1103900340d0140c1c100c2072080050110140f40e10004900600c0c03105500204150a04408505101e040c03031010310b03036140c0c0c5200364001d01d600380c0e1450000f001c254041c0684c0c50604d40d14940c4071042d080306d014500d10b4401003401b03255040d000b01b542001030310f001e0510460b00408545050002e0780e21580b074035445c4c80401c20510003402100e4110601740700c6490550240608401e03442035099520808011113510145c2c09021600c9040c0c0c402602556501c0720b041d0f1594182d05d2204001c440604441030020903604412180110309254094602c504082005d07a109044100c400e480414410007603100d039a540103844840d445014100011003544100c1e5070301881d40141c2080d03503010400a100480a03030400c1203e03410b810703680ca00f03211a203404007000f006102c05103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 789307383 1250 789306133 789306173
    0x615090b0a030510050a0906090c17040f032607030c14040e0411060c0a03260a0207031814030c0a120b1b0d050f1f06050c070918051504 60
    0x8004a0b00164041c416a03000f450300400c0b00c620740c1d1f15016030000038001841141d100910b4643c600d01ca032401400e003201100a1200405040d40d2940ca403407200b420010012000c00515051000c3e400c206a014080411007140c1110a0303480c02c82e00180448141c81c000d81300b072003055000d01c00c0d40d844510881d8150f0f0188050fa01b529116441c04460466003c803180341c0c80000494802110100003403040811800f03541d1300f0a040c0514682244089018440700140b0300c00140001c010001940040081a100f07103803070000c1441c031011002580c10035400030030a82c60b121301d1043c540d103403c00c01032801e5501101d0190107146002c00e00101c8100b61400240b15800b181c0001350b02007000944014010388031654955162843c5100d0001443d04a0341503060068100c0803450f0300120154002c070b1165221654078031241040002d503295004822821702520440301c012656000d90300030840c800c0604280480700882d9403405904000c05407400000c01081d401c10080418410891210904988 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 789308633 1250 789307383 789307391
    0x204020d0b030f2a060d0f02090a120b06060a0215190e0609190245060904110a180c1e05161505040b0f01080327031507030615090b0a03 60
    0x38001081c5ea9004c1e18181203181850040089540e10194006107480b000071103520111540b5040015019844a00082c00890f00100011034a050610090410740d607580105c5181c2c0d0b0340386c5183c11341ea100807501d5540c5e00e190607542c400c0300e4649001d02c1c0c1103040400094410761900760ba51594070f007210101a04040542c8800c03205649841c01304400240303144007407200c1d0358100001701d43c0100000782c005294030300c41c1d2403d92100c220b45c004640500401840d044003521641c031108480001c15200036031045040c0000a401684904654403290706800045a1800d00c0d160140480d00700c00c6000e8070741d003000b0001c0c5030b0350b030b40c458111281e0070300f80c0c8020b091000490402000c541110440440b1080c80c003000d210500c901443c404e0710544000b007040d0416030300d825103140c984c000d442c4d4038000864188156100c6442da951850602d140150450380e4800000390080284003080d10a040865074690060054900d00850015491030600700000e48030324081641c1202d206007000f6400705599 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 789309883 1250 789308633 789308713
    0x10021902180106030c170408031b090d050a02040c0e0306010e1b07060e0709060f0504091707081e070b04080a09080f1614030a0b130204020d0b030f 65
    0x1030007812203650308904003146242d60b16080041c0051115002c0c01010540d1b00800701c001507203e8400c0c40c0b20325401046142540c507548014004010b0b041a901c0d039009081c00403060640320030b00c00d04013050060000b0301c07040d116170060000315134608443c40104074516030240031756280011941d04440342040b030040c16070307240c4400c007181981c004084d0810070800140300050014541044200303c0c0b600064036045503490390704030110303195441882c840d030503101000c100624096205003c05401408065800510b180003aa00c5034042d14085400d00c1d0040340031203107900c45188004441a10008051500d0001e44506010b084000d00003000040300240c0580c02c00d205004080c02000d02000321100b0300050003610b5103501c1c001e119000c0035501403600180d51003c85c0420241c900c80540904102185501c54140c0001d000f4030390200030701c246c9070440068940748002e0103c540701001c0001c2c500150b40406080c800c07150000c540c81e80c80590005c400118600c102001000311a0303419640400c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 789311133 1250 789309883 789309889
    0x60306130503120103030e1201150b0d09080a08090d02030c0606212e05041e0201021204030b01140607030801140d0b0a050a060b04060c022e020a03080610021902 71
    0x460b80c00382100d540740f8503000204058000e140c841741580100c4819081c20f20302030480e400c031500c49241500481d0301c06820130065514030004c01c5290b440101c04140f4203500c1c3c0f01c2040301d910400035a400240000c0400042c283e00b808083c000c0d020a201861401c424825183d0f03444a0240002d8821507032072420045ca203900440e0568091320510540d0310b01c9007440c10039100a807041410381e00008160310101014901da124040c810340e4020b0f003500c52510381c40c0300b6449041351000101e040d40f040201500c580c0007039102802c021881600300115541c104007842d1495584050500c0c000c60081c4050310019030001c15140c155110240802200c1341010005030f00c2e4050f4000282034406841e0074080000c131240c0200e0711844055100384841aa1a98540706610592050000007031030b0840303107401441c140608882034201c2070511501b60070b8010744404907400350392501c0056801101c18000301504001c655506c0041181c07000180e600c110070181d215500d9040178424070b01100d5210303003155 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 789312383 1250 789311133 789311137
    0x10f140a080118030e01020a020603040f230109020102120a05090d052e1109030d0e0406180207110f1302071403040f14030307200a050301020c0109060509010203060306130503 77
    0x21641e00078003601d1440643c42c0300ea504458000c1d00000c2c0550300c074295550002801d462165406400301c1d195645e0354842e0140c00023109000c49244d40a400000301216503404600720202c0804000910b0b1035451001a01d40202805000e03180542807240c6000360f50004255994803000751a001c40d40c600916100d42044800220100442408180389004007803410f0141048201810200034980003410301c5601401070080680c0d02d80d001da00058001c500c580c03844004180c02402c0415815129241c22184002d450300340c0000690100da99014895401ca030203143d6901075032001c003c45c0841d00402e01c0904008180341d00c198001951604111030301c3c00c5090304200000580c0d4681c4c0e1507481026100071584111403440007550707030091442c41c0205c00c4440340c652051412003168a4800b4880c1c00040000321242d2080c00f9800008d00d6840030b00041c00b1281060f000015848090314001c0c0440304080c10840b456032051081100369200015203c1e000840e0708980500c0e02001c0c07510314030314 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 789313633 1250 789312383 789312389
    0x60e0c040f0905010605091303110c0319030e04112508120412021f0c051e03060a090b10052805091302071208090a06060b030915010f140a 61
    0x80c0c5020105400715107281d204600181c03260f0300074828a40d450041200140094031282c560003650404000000d0140015a481c010800d040c0d81d440e6482070f0000b030500050165801401d00c64949500c00c041c0d12a070054100481141c04103d00080b8100501d070134014105000c091a0f09203041d587c031b80c4c81d2011440241a88007412582d640c4d00450001014001500c2c03c8a081ea84075481e410b105001140c5092035042c1c4048002d58500c40343c2c5080054160408040b0038400308000c2c2042040150b081d09203068480c0745020764a04110b020700c4404d00966100d4030301c0c13500d8522251000d990f1206003800c01c4010382340c13540d202c84580c00444612440d40640c1c000700041c640f402c408291f00030028000c0b281c021a0781e94000c920303440c6205c05a10400b28020606014015000044c60050705c11940080760b460480c2c40c5007070503a4821007210703007941101c0030b28034000c010400180e00811240e911a015007403010307501c3d4500304003814844100c0c0500f134028284c0344c2d0f01e0004e0381c46215081e401 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 789314883 1250 789313633 789313639
    0x6030c080915070f110f0115050904150203040c05031b1212030412031506020f07060804050307031d0301060905180708030d0b15161103210d02090301110c06090c0607060e0c 76
    0x1000a0001d40341c7c0244804500071001103040240001c2510300018040e00c207d4008000340044110080d0741002540300410841c0e03010050b640118060702d0811211403201d0401c40303450300100304801041424000025026840e40c402911000d00251001c00d50303420030344c009801103040c00101801d402802d651029448070701d2012400091807540000e061504503d40790540d41460340350907045038204000ca178041c041c0d5204100080001303120703024003004c020408c80210441c59860340020300b942c01c0c41e403010070140e071a80140058038084241c01400c07649004010b004452400051030745074052240007010a03a601d40d808e100b5601d0f240b42100300e01e0144030320a5a10103580d9644503e0900000c0103540010b0418041340701e41c240010074982c40a070043c02c124002c943c100a06440f64802401008101e40030700c151900790f2000d000349091b00c0c1411107a161903000e403884440c60200c00810320a00c95001442d101e400c2d0320348000310b943c16178000f00c012803900000240c40f454800003403c0c641d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 789316133 1250 789314883 789314893
    0x4080f161b0b0903031617210705090a031e02060c010209090c072a030204050f090f0d09090c031107030e0306070504060f0503060d1515050f03032a0706030c080915070f11 75
    0x1c03491140001c41074112407424600c021a103c449c2d003190b050040d00c00680e00f0040140041c404a070700d1041e07041101201810040c20b8000550100e14150040700f0386100070307900172641503014a03104031020741c0000e030888194100807841c0c560002c5100d298003403c04841e05442c2d00410200700c0d010b100301464000c0c01c01c1c862402d1800403640c0024003110b0340503c0e8003030401034124180010030040310006c0c03030740e4500c0c58140c142903903407000b4281e4102d002c0034035546030801418642040c0250854900070b4680008030158401498200031000340745004020003040240b00c501d400c0346000c0c40d1045d540c40d0440d220750ba03010224000180214014100d1000405000e0f0601c0058201d82100968004c0a020955480052001c8200440004c03640b60b00103000ca104040d14106409000c0107121420b200308600721050281403801a82001000903140c1d14240c45050700200125082070841c4010b08400711940c0120800c094090450810400c203d5280e500d07032803041da0f030b2100702035040341614 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 789317383 1250 789316133 789316147
    0x6181806090c01081312030e0a14100501120807081b0f06011e06020c060c070b040e1b09011709072d0f0501050304080f161b0b0903031617 61
    0x25074070b004402000d400515244002440d011854496494284c3c0c80205052030040800054010744800a44442144918156000810b4000700d0002e08000320402400304000010105826075105030400e660700b070348030418207000030106401c440302070303400411440e2209000c07649030242120486034a24a48640c507460704101c040411543e0480c1d10f513060a8940030303411066442c00d010248180b00140c0c0003c080c003850303414484010440002035505a41f5041d48a0249a0050f001038100c640e02c02c4030034003000b10b03c0410034001c02503280040c004904140020300000e01c184010001c40394032000e50404a801180100b118074080d0000601602c81400003004081e1032200c903080040041c00752000019040780b9040c2c454007a110706940e22491a40c850b1220512603021030300709448600c0030058260511074005240071100e01ca00038020540031030103080010b00344035400031000c01c4001c11080400366400411601208156480910b0100341030030014800c82c2011455020048005004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 789318633 1250 789317383 789317401
    0xd0b0402040b03090f0607020a0215040e0c0a02010605041416030608010c0509030606040c090b03090708030d0e0c041b030b0a030606030803040c0e010f12051c03021b0606181806 78
    0x3844c8903038803032022240d000315a1504555181c1c4c044e42c804004d0781040b55148054100b981051100170b0440240c20300d042e586411784044850201c0e035035040400c001c901039902c1d03035081c010a401410115414417003000c44880010480780080e2003031b5007110156500c0840c3e03601a410000080075040c000b0890340c0500d0b01d01500030351090000c0c500c82e014145c0090443e281a1040c204d01c2d40c03071a59840a420b082c80c0000ba20f513407010b00004054805e4180c0020001410030007820740c40030381040031030007544c0c0c40402d0b1718100d2034510f2948944e0031301c443d511401040307280f04c1c012011646008501048003c01084c41942c0c41e130005486681000d5010081c00000801540154440c60114114580d50700400b40115800e02511502c0c40c1845001c110314030310343d803a40c5801800f9400f994030000a408440d0b061007080f4455074007003070700412880d04480140c0080a200074135003014054034a492800039500108481c91407030541c0780840401c0c4110807400781c030210450340300106c4a00d82010150 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 789319883 1250 789318633 789318637
    0x703200306040f02040806060607050f1b010f0f0e0f01171e0c072006120907030c08010b031e12040b04030b061005070f1e1a0a0905070b0d0b0402040b 66
    0x941d500603424005076a8040c2602c2c0300316000c65883c20050145a16050204200b582c4220380c00e940d00e101c0c1c840c15007810ba2060154080c1010f6240500d44407a610000241c00b004114000c8020300c04150441c0c00d00b01c2d000410b040805804507985103c0c030b015180180c0b80324080072910035080240004003c000400c031820304d4000d02c40c400259200e580e5032188c01e20507108200c0700a150f01c007100002074099504201032405800010003050030003001c5070f003080c0d040204407030f281055800304004109000e51140e02101500034074000f48890302d0700720046503407600400361045c0040c0c6094441c000da4207041c000c1d04800311801d00103590707866840c094062250032034003003945c0014606020601030319111480300901201a01c6841c03d14485032942600e0010803241a81d0f011443c01074101c0110103000c0b00c44050703200701d0303c0c13a082e0f01e4082c80e80e04c05e03080c000b840020388500d411001e4001c00c0000071950115180c140260382e403102c00700514406030440001da990407030b00209012541d1034000c00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 789321133 1250 789319883 789319891
    0x20111011d06100503073602091914192106060501081303051b0607050c0f010507021e010f090303060e070c020901090b0a03201807090e07032003 64
    0x1003250041c3d1500307103500c81c0d500e15600c503107603042e8811802005107901d6110001804800209001d1a1516681d00030b251007200700d01f8105403690000d150300d001e18140309040e0001c1e2090300700d0792225040294107555039428000b0140300701003030044000c11807880c0000078041e103800c020441c1c803803441d8510b0504246140f4000c0740e00760300b00b89000c52954803c070034803486104401130f041c1d14980903403070940d4246c4c084000025124450012205040c1d420840d07140540510760f00c2c0d69440c400d61308194100322480030340c440c441e4141000c0c41007182d80001d08882004603043c0110700c0201d0303407600a0060011446003021282418030003024582c05601036070132104c4900b00b10070295540801110950120f800082d881561000180504203459009841c6108090000c8250300c3d12911140d5044480c0101c40000805080f242c0800381410201282a452003400030683e6090107a00548420003600444000c0ca80700400035600038404d800c564047c8210508102c0d00419a21a40d01c3c82d40c0221 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 789322383 1250 789321133 789321191
    0x5091b1c050d091203080c0c03070c08070906091e05060a08060702070302011d131806020343050706110706050907080d050d0c020718020c010b011b0303050402011101 73
    0xc0f00050240500c0d1100d158640d45039036015084c0d81d5031021003e2a811560240e04a848244010800035030344d00c08007005401c90f0401040b040e1310707003d1071b503050300d603141c1008002909110780010b0b2054000f00700c4010104403400420169110300105c0c0c44034102e23501080c220300c0b45200b0301c0406a000300d07114003924005e0707885980001000c9954203244072107070040c0d9008850030b822405500c0e140d81c059544c0c10500c000861410000380c0741c180607a082518007440000154103130402112808110801000450041260140d0f200c0070258103002180d5111080c4080000c0032420010194404052a40c4a02c080ba0703d41e001e6080070001000110380718031161250321b102142c811000550540520300b145d954a00d803151214426000e00343c00030805040d44a01803010030407001c103501c1129020640180140c4840343d0702c40d5682511a400941c40c140106c50800d0009240c0c2c0c0c9640d90030994140c20042916200c1d480102e82c031000d20002094a0b51034003092070008200e1aa158060441d0a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 789323633 1250 789322383 789322397
    0x609070c21120902010c0213020d02040905012103080117010906050103050c01080109050c2a1c0e010c020a091802100903111f080c0906040b0406030f05091b1c050d 72
    0x100c00042c21124441c8004c0e01091480c0031300030040c54001c10100b2100d00001000d400d0251039220041039030480d401c01d40c40e07c0d8036040140002861a0107601603900220b000314503001c104d0301c0103037488006000700800203841c1e040d0481141c4094000052283e8031100802441d1f07942d041094568200da01c10a0005000c000006200c891500590703000e0040760352040d03e8003c0302c01c188900b1200908001190058284200080d00c0c07090000c080c0085039292602201d80b840e03d8001c0060252155041c10302c01078019110141c0c5901c9601000d03601980d00015003580c2c80003402c2003d203015030000b540f02c07001c0035039900f88a500c0407606c412a03125500b10207550040b501001424403c0140d0314046201e400e020000e864420702503581c10404180e0020300d00b0001d40c012801038ec0c0305030030241e002040050200060741c1d261240f203001c0c070300c014000c200d070b41000340c1c400f03890740f1814000c440048100b00444541d0b83c0c400c1201ca040d04a0707000c0e03580181c185460704c251100c246c0110040480c4403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 789324883 1250 789323633 789323657
    0x509220605220302071418010f05030d0f020604080703020c100504080114040b04110111031908010b0307171e040507150809070911040e090601090e01060503060609070c21 75
    0x1100c2c074a202850703455000f808103942015403042c40d99580040f40d5078041c808400b4943c01e01d52141d0b0a038040d06048203070195041c101000e040c640050b10382c0302000c0003002c4482c4a01541c0c081000d43e0400e0780501a56034032012424124039044904007016072081c0f2082100e004290004010400c49036070304000d1103080e0183d004030818480072140035000c68000c100040001300144080320b44000141445001140080302813480d5421101004140c9800c0c1c46805030420b40050000d40184101c000035440e40c980030000030a44d440380414203852180f0000420340001035510b1458a44070440800181446d00d418040e40c2c1c1d00d4540302d016103103001c2110380a550340c410000503100e48501c0f0000c0100900d448556402400c890b07114610510702400080780070f003c0800d51a0040d0b1000d8000c0c41c42e035040405400413249008002c00c4e00c0da140c0b06040025441c04100c180e400351040324058142d0740ca0300b60030380d001001e84000a00c404407890500c445203c18480c1d2030701c0005140e50b500b650440c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 789326133 1250 789324883 789324931
    0xe0c03100e0307080f0c0609010506010e0d050a1401060519140a032003010b0616020a0501020705030d0e13110a080a05011d04380603010c08010509220605 68
    0x2010610781100c0b60010000d110100d88160020700d0100d845980c0702e0300e0030310813055407410300c0382c241e070b00e0180c40c2d440d00c003401043e41e4844502c242c2c003d0304480c4290008507569421350744820145004001d2111821b814910900a41c810001044c0145c21030244140d5041140c11880d0307680510310b041081d5007040c000a00740001d001003501d901240c0b14204901a4184c03502d804910000154103642b1080000b440f5210000036150f40900c040e01070ba00c444a500c100904121039801050440d8809402040705503000580b018801005040c40c034031628004011608079840b40c11070840c001c0c1040c1120001e03e80e88401043c0c84186c0c1e43d121340b9541c80e402e030440309543c002c2c460301000004409079004101d4682da0103035000340c81000954081c08550301d00390f4034030581703102d15003500c13841c000c2c1e04849924010080c0c3d888103048008000355000c1d40030103011400180134280c041c0c00700d08000f40c0c001e900402a02d5034034000948495210106160443c05407904855041441d010064907080c0342d4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 789327383 1250 789326133 789326141
    0x7020102060c04050a170703080a0507021f0f0c03030902090c121b040b030a0b120106080d020a020603040f020111030c030d06050d03080a0203130c0b0703030e0303090c090a020705010e0c0310 84
    0x1440017400002c4a6281031446070901800b0300d0701c449580a40440003000985000040c0394041c119190349489403402e004211448990b40204050702c201ca59040c0d2031242d01c03140418400c0200d0405115404850034101d00a14001c0070094100c0c0c842014040c0e00000c14000d0842d20702c2c0403c03481e00380e5031802e000740c481c140440241413088006000038000c180c61040075540c000395182000031180c84030000203d18000c100d0705604541d540b1281480a000c05004181800701d950004025000b515030200c0c049100c000c101800d034a10303140d400300443e8861091600b000e21802c0c126034031610f207592601c4d140e510454281030380902e0102c0001c0d4a08006100c171000310f4240c1c4440e5442e5139403d50a2002c0c0d032008244450341500c06a103980066496440300c1c01a0590002154a404072498042c084480d4103854214503030090081140c90840040c0d66031580c0e0017940c201c1440d4841d4103506010b4020244020525402c01c012402030303c00004500500c080100c044813140fa503c0c0271503030200e07 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 789328633 1250 789327383 789327389
    0x316050f0a0f03080c091c02030c0604060c1101170703020d0b010f080f06040b0a080f1002030c030a1e0207060c08010902250804120f110604050105030402120a02041107020102060c04 80
    0x150241c8555000840d00130a0007a03808000e00350254505421b2000290940e80c034980c1801490b080a03030450254202088111200740c002d50b0740c00d02c0d16051680140001188240003484142d00072808074560b40305100045922542c00c01c510046d080011014020390003006880756a00d180582c581c50941c80360042c81d60312409500e6200c0305032260548800694001000c80b50840e8071007901c04040e071140d64801c03005082e0f090107007204208014910b4204038040040005c07540c014402d0040b4613a042c4101c0fa00140000e20024642c00b80ca10383d40055580e0003c5155054401301d569002d214648d04481c180b26200d949020540e84c0781e03c2c0c900c00b28000c156800c13044180040303804800f1000281071102c81405040058107280d03551441110030b0904000440315143c0c0c4060840422095116513600c41004864a5082c00c1c10807000074854000100068400d0aa29003056989031040c010303003510607005802440404600a125501035100c4c0b40124014410321000500034902c4c5020350b015 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 789329883 1250 789328633 789328643
    0x1502010506010f03021305030d050d05010e04031407050c0a0e07111204090e0a02030123010918030e0402190203030105011b0b0c0306010216140a06030b09040311010e0316050f0a 78
    0xf0b005850114000d411410030000140e40305000807940b9030b4100140351a1400039642d8030f50360131800a604060342d1040c0d1003108034400700380c28040000d0f040b000e55092200d420144585034003150411621300003800c04150f800c9101c00e00d011421984005805200b201582c41d030082c0320900f1600a666111900c8a101c000d01c000c2c8014030102607203130020040240c440b8211000341d40c143e00000e08444400480282060320300e6140141402c2c0c0d80031050050651010400c4401596150501c0750500800d00070100940130341c2443c8995a1a41680c04007000c0301c8805011501c0c9000283d40c0b0340c4280a800d02144002d200282000c00300c0d0a031740c4080303074403680c241e0303081c2c503585083e108540002c1c081605500401a007205008000b0420074010680b503042c00601c001c00006100e03080c103241c0c0120003050704010011000b51506194070b031700594180350050345022519405801410070041c60f98032400700103220025064400c080310141030140c400c0d102401e07100307000c40ea40c4d10069a80140 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 789331133 1250 789329883 789329897
    0xc03030807020d1709150a0b010806030d080118060803130609050d08040b1e12040b0f09030319110a05041e1224050c030a1d1002161a01150201050601 66
    0x2e20108100c41c1d003038125040714110f854608000618004101b03003203078600301c00c0d55640d03078204a941e80644034136048072095025001010142c44010680b240502a460044540c084451410083d56000c1c0004200c0c900035a5200c068842c0310305034a0a2034400c0341d0000b910311002203618500503510505140c1d11038a00f03482c051410001d00100c1d00003104008446101000800c0340c440c071b142c02040541c50304114048286017a2074020305100c80504442d06030503401041203800d0000104a9812030000915000040100303198640500203084990098100200c0ca070034409400101900945c0e062140c1d4007101c60525000da01070030260b00c03904a60781c0c0041000804a00c640e0306030212004561054520385024501230410360304140c41d102082d29000040255541d043d220304000c88003030100d016840c4503120121561040c1d9021054840d950010300c80d22030200b880b01c1c1c044034076400000445403120801070314600c61424802d03154025281c0d0355007035540d8410b100d194031845050b150700c8 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 789332383 1250 789331133 789331157
    0xf121502031003032a0b09060144121e0c03070201120204080a140d1d0609220e0f150708060303070611130f1a1c06030c03030807020d 59
    0x143e1420078028085d42c48600d034003188022a20034014840464011138503c00316051a5400600e06901640620000000810300c4980450290003100020707000340c00e0400410602c042015910040700040c08442c402c2d102e1040810240501401407a8500c00c6040c000061002c000001c0c4e2090807240f03020780e0400c1090310b00540c02048100c200c544202d00050401d030311a02e50303902d07003280c005050700e00311070a00b81283d05940c20002007006009a18000204042421100030203081480e0030320720540d008500f07503100b600e481c0803803e061004076403900289003000310545e008126020403071955000388280513000302c0340082c0401103040c0041c50f85020b030b42c076070314201c1d08070001401c0715505001c1002102d001c1421030103400c1400515601c0d155584c0d40388644110001916070045100035503e1804120100e002c40c0307841d2000740d64055855035191030b024003454503090090400b014070b1500c0004010b011300503040f101540d11079102c07a6010740382c1c0002a0398520b0702e50850341c00103034020500 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 789333633 1250 789332383 789332387
    0xc02010b060408060a18080c0102030610180603020a14030f150a150f110303040506010504050123040c050c160914090c0d0323070c0b0c0d0f090f12150203100303 71
    0x10030140d506c0d03800c410184d00316550f19210994413490002181d0b0b900403007413110b10324081042c0107240b0351a0511088d00c948030590000800f41d40e03c0b030318061513804922100d00c98042d019105144410382d60281da00d10b03048104401c1c0007001c0e143d07071070720900000f24120142040398403d0261001a001158014200d510448080000030307031749400c00000c410003181e4140c00f04040c5014610800280c051907041c0350030303c0210f41c8168041c00104a111440041843e40407406441f0f9960a82d8003240424103100d0549442c070a4840c0348096105095000080760054081c04c82600d00c200e03424000115440c0140004900542d83c409170b540008400885601d040b80c03102d006e40c2c1c40790a140711040d031003140850152428440c00c050050780000c41070b0400051079021000341102e8918203041184925030242d0310510705440c80140700d00e1b40440241c2600401801e8010070403000c3c44116641c079461004403504031410103d801c03103100c103100c0044240c43c0c0280c9202c0c0c00d26010711a005459500e013 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 789334883 1250 789333633 789333641
    0x813050d0b040b070e150a0810050f0f0402040312050406020606010c02010e010f17070c1a101205030f0301240815130e0618160b07020607060b0904060c02010b060408060a 75
    0x13812060114481100e060344d15140000031890120f041e885031900403110000c7d10041d8024503500740020380b02c406014a40e190082d090090700262090f058001c50074001c68000e1223150400743c1030b0f40114640c000300f40d50090040c42034650b5a800c0e11130549a0b41c00660fa1750103184d40003404181c40d1701004280b035100324440a03039200c151038050130440c04401007a5900c0e20a41d11140021052198481403000f042e140110910030500c5000c480d00d014000d0b9004224140140300381401070441d140c0522400b04160f448101010018996a50b901c01c20244000f00101080802042c80b950740075000d4000c0654901c240c0701c02e42c0d90751500124030100046114260494602e20360344400e03510364002d04003c0d0318031a50305a082c1c0a0328840c1a4074691401c0000e501c1920813900094080c01200d601d0341c141c078242d5a0585102d901c0e620a8941080542055004c2540040003001088203100542d000b15268460540080006103000c109001c8103118034051010705038015004a20b0402c81540 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 789336133 1250 789334883 789334891
    0x50616031b08070b04081306021606020f070b0310030b01120c080c09010603020c010204031e0201030509070f0515040806071701082d0a05030c0a110607030c02040905190813050d0b040b 81
    0x400c42d8600f61640b0076012611f101c0b0307003210300103074000030000c003503820002c2100d80980028002440c05000780c5880c9641c94025008000b0510030110108101c2480728000d840659031001c480c000640c0c5030000706107000e01c000320075100c5920240000640310301c0810790020541c0e01400d241011385c24004141c0195015603040382c0c0c0e0359401c010000101e605007044860340c40302403903224059801030000400791400070b000c920702500074442c2007200c85040d01c8103004961080e240800a150542e4429119016070343c00000700d0701814081001059001c4802c44080c00241e1542403140d88850000760340e110030303245001000c8080781c02414039001a1140000c0c080d900401c9440249059541e00d080d50044d820030102a801100780400b0440c2580485403600001c2c2d0350309041800a48000b0889041180e002e4001c603a02c070708010900ca01804249003029103585401c00906143c508107a1540c000c0118814864240d08082510b00d400b0b08007400b03079500300c503541950b031b201c0c0c3d00c0c4c203444442c0141c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 789337383 1250 789336133 789336143
    0x150a140f03360307020310060e010e0403050708181203041d1512100f0b0117041103031602040b03070609170a0b0a0c0216050a1e050616031b08070b04 66
    0x610307044a0742c40d28040d58030098042d04069501d0311607501c145460142000a4051003030b0030054148180d450321044c1504495140d098140b09407180d0a060b942882041d4020302694000644421262050115000b2092080d0380e2002495148469207480e40100d000e1001c0303516000d4155480360101080468210801c207a103a069032180d4000200102c0861105050b284c2081c1c83c100e00000151017070020784022120180082214000000e10000004040109812809002c10700b448040c0c07034504034501d00582103d0f500c05445a18035044410884124400c82c1001c12081c0642004580e000c02c0b60250b451392490320382800b041200103400182004210303c150a8200d0100d58441c41042c000d02100c800043c1c01c440e48403000741402d1894041c0711003070503441c40c02c0001e516070504500840c1d17904241000400038000d28a2080481c1c0d0b80401d9010030041100c0e14202c104145240c14548251036045200c3d0a5901980c00111780d0800580310000521000d000300d0308603800140e20600c10 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 789338633 1250 789337383 789337441
    0x1051b0a020c18010521120a0c060c21020c06150310020d05150303072406080a0b0106020d090f050f040b0d0f0c060e030a12090302150a140f03 63
    0x8580411052503860f6000708010030000300420450801c4c1029039160b82d12880c1d09091401d83c060240d130384802c41c00c0c40f0320b28140000340c0210002d02c2108426213843c0d20901c24410002c0c080c80080220610207400710203880001103184403c2498400c54001034442800f503c032175554036074180f00c060710920b5290341500a202000481d141302c0d00c02480c5040c480800010300c0d00389407038412804054103c5090083e401004200003041e45c2c180e04900780b160f00c2d5040ca0020300100c00500c080c01131070340480240c0c852007501784200010149802c2c142d920584c22201c9c4a04040411900740406108503020307035103003207030601c4142403c4240c3c641c1c101c03002e08040390541a40c004201d0b0810304050680d03c00a402940108010060b00070b040180700307500c0c10b0705d4510309801c0041d454861400005140d0600729100030390407801000c03510001c64004100c950040640588007203d80e0200006400241c210103100144c1e1a41c0740544050007140001c1d1400c640e560b03845040c00861842c046464100c42d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 789339883 1250 789338633 789338653
    0xf02040e100609060b071a04020604050a080a120314010902180607060b01111f0e0705030118060b19090507030e0714090f0103120516080403060b1201051b0a02 70
    0x204020303480070009650004901c0d00c2d09002e02c003120440e42000c441d201040150f480030500d03510010501f00814144000d85071106d100080c19842158040380d046140c02d44000341c4c0c0c40380031500c84049401a2041c1c001c07402c3c41102101100c144100450b0038114503c018040030521303a000e0f000ca54060088888041c106400203103480d004080115039080d01c3d80d80c0016a964046c40e025071100c80800281406840d001c04550f42c110301c1021001c1003503840a89020044042092400409000d0004c01602c5070000da8200450f41d100c00603207465080220491103400c1c4140714030804030301600700b4541c880c21725039050054040504040201034449502c0c450b000c2d4140441e00041c090b45910895800a00c0c040c0110103c006011030700d541c50007030042011981e0715100c1c014081544c60055641c0b01c40d588030550702800514060104980400c0100c00c0000355070040a0780c070381c101c030000200584003440340d003a2023040351600e0328846a10721100b04624250040d2500b2450790050701d6900c0c2d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 789341133 1250 789339883 789339911
    0xa2402030d06030b01091b080c0703020c04020403030816020f0c040c0e09010e07110303010b0a050307050d111b0c030a1106040503010911010e030d09030f030c050102131809030206040f0204 83
    0x940d410035070701c2d04c0300b08004018a004a00c41d4121040c20440c01c80d03007081044c5000740850f0720040002d4907240d000030342201018400d0140c000100f000400440d21030703483e824001d02000003280d83c01e03120368150420760711481c00041c0c80e1580c210658000c226490282e000d2001130195036811109112440e202101c1c16580c944040d4041c004860440c4418039007001d00130542c8401804045041d00100014094803c5000448560b0521414401c0e070343d46607041c040b5810701c142a5001c120300c0c40d01c184c00c0c0c0111110401403041d2209805071041340c003a41c52005860703d04500d041c5030301d81c0c40400d401e00058054240b605600000500d054101540c0b10003003400d50700100e504031000c111440140100e980c000314100c280100c10b0340100301c0d5458102024041e401c4900000d0481004181540101807090081c040710540c4440255161030000200302c200078818084d10a1603503160080c00f807048240e104132090707240c0580c0100714a403035503200c0511011442100343d801075152448400200 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 789342383 1250 789341133 789341141
    0x3110f0307120b041a0d050c212a090642071205030c21090607210b0402070c1203020715081f0e0a09020f0a2402030d 52
    0x2400e5215000b1504041e500841120a4450302510440c501a0000c5c1404000a0903c40b1200140c41d248840c80040c10311501e4400110607460748001c0c9000300424406005005401c2d200d03c07401103c0520402c583c4a1840100340340980d503089841034900401461b081c20701503005074015014980c0c0700c00d00420b014a0704800e169840c40c00b04554503410b54104403244d50001c848550450301d0400c07410b56503840120b41340c4048141044008004540d04e035203420119120440100c00c84009041d00034004200c013081144d00400902541c000284414020b0710600111180300621002080c1c0d00f10b080c6e0018007111a2441c0c0183c0c0c01d00c50240051280d404c010060944480048294006490024542440d5421202000b10821507180040740c0228140342c110304850900021010001c00046403442036a01002c400e210a0f0103010450446e030744456030007402601c181405100103003e1211554452003030720f0401d2440c43d0340312480d420844c5020900300003031050340d191181c25507560040d5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 789343633 1250 789342383 789342391
    0x1031413110402070807020d1a1015030501050a05040911090a0b10020c0d030c020f0306010620211b0307030801060f02011a060309030f031504061d060103110f03 71
    0x101008440400070700080c4004252a4402101e05524100d45a6a4900e07180503800000740a5544610301034200007081d4038480382e210f031300303004054507140103940c4400c0d040c036a100301c1c6450f9004000382c0d074045220340155410b0f00d8001c0d105100f010300e018103000082042c410150355688009400d04090743c1c5040180d40181c583c00c1010505954140400c81c0c00c1c0c044c8140d803420743d80103104034040350721030600c0c90030035a800d420070854404150000c100c0e92507124460341c1c0d250190b400082038668100200078010748402442412400d440541b00d961501d4520882d04c2500c44a80d019820448050040c581d48061442d0440d9004216240300d203136800c0190210082042e0704018898994420b02d58144290588024807000c5500d410316020341102c0000d00e40900d41c000b0014900c0d000c00c00890320450044021107980389003c8440b80460000000c03a2440b4a00f000000034130348100c0d10f42015011068111210701e0f803640380c0154010040610310320f81e502d9092204240c04050325000c0c0d442 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 789344883 1250 789343633 789343651
    0x906060518070903020405040201050910120501060504060c081305030703030f080a090819140408010506100201051b0706060302090702370b04060b04090f0b010906061d010314 77
    0x55003400d00300052035940041c94050341e01c01004100c20035a20207451000c4a805603800903d40d00c550004884034401c40c010980c1008820444000c1d1503408000614040c0403002d00700110b90301c40c401150780d885240f160b030001414126014010503801c41c000c204408480304050f105640d14400300b4209002c0b50700c1a00032a9001f40340c030900ca07811844c0c50707500c08440081045006029a1254203078001e41d000450445c1a490342541514040c11598511803a40d05581d83c40e20303a100d41d040c2c040d080484036180160007100d84203800a0050180754000c3c1400040f11440003694240303078245411500042e43c10311b44608000025841d080d82c1c02d40030307070069406481d0035141420242c204071921041000a04c40c26452158106500514030320b0321640b00000e101140c4817800c251000d09020020540d01030314040c030001c02c00210410000400e442001d409046a0361040d011046924510460001c16503503c180781181c1c1000c0401804100d05040000700b5417504425210008402c80d50115 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 789346133 1250 789344883 789344891
    0x1208132d06020601060c06200c1f02090105121003060204030305030a05070f0503060402160b090a02190608040b060d12030e10090804030803181903120b090423010906 73
    0x9601921000d025020780000d000a00d07065140c030800400c0100e070900c0141c40c0079070340d0300d681514078090078a50b0a00c00b03842c1207468465540310000e80d11000b00891140f11407480b91100a0411107500070394024030416180d05051646a592520014800400614a518843c000030001410a1010740003a500a5039400e4407450814118011150b010306060240a014402d012034258071000310b84d44008260b5001da107c1d6001d400149c80d00344103200c02000f44242030b0400690260015112a0103802100e940020b258114940310049030580900c1d00000c0007080058042514580c1d20340c1c002c8000b408041200000f62036011104c81c07507403000300c0025180d41e00c1c40e04520b41003041d84001c412a4000300503a805980e82d1124600c81c0d48070007400c181011001405150721002005034480d940e00556261401d40e8500f5105a0000f02085010543c5e220410011001e103104000035020050005c020f80d4485403983c0b4403040207080c201401c1100d10008040030002030280605161156002213 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 789347383 1250 789346133 789346199
    0x9090f020a0905030624042a08070809030d2a02071701140a0c180b09041d0a06050606040f0807052e230403030507020901080304120813 60
    0x14070b2000540d01442c4a58405420302400361103480000b00010151203e6401d40c08245004c0303400b4002c03044000c00c00b038404903000c10b041083c10998001a002c6651110110380e01c18006a8024805640c203800981c410b1001058094a0390700c0350016403100d058401c42c0b210744a41d1404901c0a84405c28016048174000303f001102800314001c900000038001c0c883c0d01940307020103815941c000c080c402a40d803108102d986081c000c1403180074144114151004d00794480c1c0d044952603110105c0c00b40124544440b94070701503100c88040040c001c6401c050004c1c0c4440d23031112800303400f02600a5030310403c100000204034180c003001400500d025405051142d140c101005568820300012600303c11145110741c0c60f026128101e80c00c1c0c1407083c10156150600c44108030f01403242c0b152411084030300018088203260300702020f00b40951007210031070b443d681c0b00c1c085581c50380214480d041040c054010400c000420b140044e111040481b084000120382d0303922603540c2c60f0407100d920180441c1401c0d4132 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 789348633 1250 789347383 789347387
    0xc0409110901020c011b0b04080c0a03091a070809060a0e030105270c0307031e171b0a020919140f16030b060906030a0e01060303050d1404080313020109090f020a 71
    0x2c100c1c84d02420b20008100d0348440a02d40712018101c02000c11042c40002410003a900044d41e0365a2661412658455801d14000d050760034075006494038049107010001443e400e16046600b501d0f030154460f400c00d0440001d001d42c60300b1180c0100140f01c1401000c5219803405d2040c3c81c810740144080159491070361080002c0c2d0303100d081540f08150004d03500c2c014180c6001031114122907115540071002154804811040c3d00442001001c48000442c280103141e0040d001e0302411000416a0198000301580e00341e45071643c400094000741490700040d2000160310700b14407007080280001c5080c0b40c08248007510380000300c0e40380c00c400003000d0030b000c0f088070010301050f1140b0403400c042103401c000d1700002c1c03040d00800802c81c0c41400001f00003551241c0c1500701680103484400284585a203034600034011381c10460b8110390140c501001442c404480c3c2880d24055a00710203698070303540342c0e5450800e002c1c2d1031070400d034180060325400082c084000c0c4030f0000c21010301e00005880e510100b01c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 789349883 1250 789348633 789348643
    0xa21020414011802040819020102120304030f11061536010303030b0a06050d27030e1914040902190e010e060d1e020312120118020c0a0b0c040911090102 67
    0x303c0819031061006201d0300ca400604000a03003500492040d80751601d100407440d020703040b61813050120011091000f0950031240301003048406840f241202c50750901941c2d0354010858080e000011040c0c0c223010707241007110107903245012952905c42e0110341c164010050741c074650300d50300c6804184030040052541c903202d61040703020700729583d0b4490303480d0a4000b4001d008281c14901d0807170f6260111650521511010180c51420f1500e1114090150401401031108400d00c0ca00803941c0d080c7c0c07000040b61b20b400301400d03502c4542465020204050601c4020b007502a400c0744c02028144031410394500c404003280c020501b01c01c0c2c006e02581000c81502c4d083ca4040c00e00c0b030244407440d01c2c61002443c0d041000c14040806040408140042e000003407404422130342c410900d000008030980c8255103840468142c60301c0e421007080503175947d10200b08900c900d03000e60708690420071030400011241c90599422116496020741026110940c0744200c40100744e02a040341000190194070b0350701444 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 789351133 1250 789349883 789349919
    0x1a0a05040903020312060f040906021903020a0f0c080c060f0912070209060d02040f0f1d0f0a120203090604170c03070b030c070c12050105010305070b090a2102041401 73
    0x18003800702039020741c2c01960303030702811840340c590450300400a041a110801510408180104240301e02e2000d802d1031f100960180f8440100400d20503034070036500780a4001c885042d0000c1d0381c1c420528a45080c00c5411601c10442103502074030802043c898000c0810061f401049410070100e56418450b0800d8902620804103002c02a070a000c48405031b6100c0981550050058503485810352092002400420103070f040b0310100f600c2c0440c09001152103a01c408207840240b0050444c01248030401ca030b443c01c9a04041b0f4941c0d0090414000080d81c00181c507240803514012242004680b0300002c4842c1c000d034000030000e0340307454201081c010040000d030403e084190301070a801410104c885490b848001c0421030304100000e1007204002a00d030f000d070020050328100a402c00350618101d4042d0000384070a455603c00c0f4180800c0103c800c030112400200300629045c0118902464625200582c0841060f002c044005002c0940c40724040c08850000180f040c181c1d45d81001b0581031000d075552 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 789352383 1250 789351133 789351139
    0x1020709060e07030b04020d09060c12050906040201140c010c02030304151404030e06090d1a0705190804031b050d080903070f02040b061b1605041a01030e101a0a05 72
    0x220801c403804110a440783c1203625440d02043e00c03d205400300380a44a041c5120001e149030502030401d00146a10200c60300c041ca544448d20064840c1d00700040d10800c2d035801016400400201d40158000c10510b040390340028222801c014141d0501c40c21100728400c601e0141e00000104020001514031050b401c45014100300206110180c0038031002d000180002c01f070180004400109036100406d41c0d2907030350001c00c50307440c500c420329183c08002030704810131001000240125403000c3c024025500d540902513600640310a00a004a038207020160007038090107851031440c1c0d6004132000b000103074540240c0c000c00754000010001000c03241c009003449100e0300144201e100080084070100c2000b43c04031408101507070725100280c07191080c0d100c0c2c04040c0007840031241902201007414100c09690003601c01140c1d03541d10030b01c02600c25031600704000c6e042508184101d0b6001c5d40c81038060f0810001150031000002c6e4801c1d080340d4403446000710350940302002d00303001c0c90070205a074007425080d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 789353633 1250 789352383 789352391
    0x30d09020109050a064d01270203010f02091327050c01020c1c02060f1201150201140402060d150504020c03300c16020307060906020d0e1e03161401020709 68
    0x204001e40021a03900c00b034046c401410001c642c001c80c250800841c0c800d1003d0035401d08080000e9024509007000300481c000d50802a402c4d01072a140e03c20f442034128050701610000c0d40004024001700340000d0a01c0c640444c2c07000c0301c0016402c42402880307052040c00204200007008001a28100444206502c503c48030401c0f9484586950101100e0a40c16a12140c03524034810401c1e515020303400504150350201c5c000041ca48251408843c5506c40940080000340f52028851020010455019401c910704000c01001480c2592100c00043c00c59101030400f141c5403c0001c0034ac1c0d0000501c90943da20110304072140c5c400c520343c10701e0101c14113510308080f440c0350443c6e03404210707008224250100000ca00c0e5070b803580c40c880d03c0440e026401400e0314102602c482000d0800703045402040010310030319018612090082c150340460400082204150000c5c108010400103a500b960315010700401c1c0700d07812482040328415010f044207100e00b2202076402c800080c030b000e14962080d4006414 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 789354883 1250 789353633 789353717
    0x501091503050c04020d06030f08030402150306100c0f15020931181401090c080f07030b0705040e0c030105040c0503190b0609060307031d0f030d09020109050a06 71
    0x10010342403043c454141e5001d80c9070f45501e050100108145e500244c00284d60115580801c002c001c01980b240e8400c548000c02955020301448050004851203500041180354480c1c049008841c1104124880c844a0070144c0c410358a9480c00c1e8900d940072800ba940210300f041e400c6c41e080c407206002a150586003e9903820709039900b01c2e01e03080b5080083e2015522481e941c5e200402307140c41c050580d00400d64500040c042c0500034000c1c4145501900d08640b000004103a500707010a02180c00740c6c044008024003402d6445070540f121010b045102440010880024543c4412001d40d10804400400d41d0b1658503103018030054920501d0800700f00001002085030760705101440c0f8200c440888400200e65502e40301241d00b03442002600e582c4840c01004000103140d254114555141c0c40f01c002483ca086840f001e5542d030080003112200300c0d042408910301c80034850b48070340000d5005143c0a01d04036030768400300348180d555810400019400d0340f500038885082c0e100701c0918140420002010802c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 789356133 1250 789354883 789354893
    0x41107030912111c0302010c030603112812050f12190207120b06041515050319092a050a03020f030109060c02150a060807050907140d0501091503 64
    0x550180c40b07400d103105541c0c0d50500c120403241912401010741818648000e4006840454501d254101d00640c00c0410380203405100c1d025603c03c07a5030140c100c00c22084032200704284c032440958000e8100242c110441103203d0721444480c01448211002c183c82240760134154107159451410b900c1c154409050400c12401d041e0440d10018200c130321150110320901402c0b4113083d600e6110004104050000320103000440f56001e0040e4400ca50800440c40303400213004039070a180c420503a00916912812050340d010314010350b444400440c54050750f0442001c01e000711481c8210a86910758807080703e000c1d01c0f002801003a182d8118000c040c846920b0031000454510139400300901442e080c1c0645000c0351000d42110104030b9100806200c2d410104400035911920010700d882d501249101003a20368010b40314034016603020308003801c42d150070401480356052001e0801d81c1001219612185105d521401425400060010100e031651401c1c44c204180d07406514400d80f940645001000015 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 789357383 1250 789356133 789356147
    0x8060403050d140f0609130809060d090b130c060203071112010b180603010c111c05130f0905150108012304020705030901030e0304030b070c2f04110703 67
    0xaa041c078040c0e6403410b45031038a0019091910244240c0003205050054050810700050310840c2d0598012040d65101c0014407203141135814054075217102000310700c03028100140240903000c0d080304003041d141129604e071100d501c41110944010100c08004100300000c038002c0034002c0c2111f200540c00d041d00c540b2402c00302070218007114030850030022840c5041c0000e400501c03c4583c02018690712204101a09240b498100d1701c42d4803039443d0078180c100181c0030340008040e0442c800001d0491400071414461003095044414080c0304c0c0600c00340450140b00a002800350001406010070146005220002e0711805850017400c0040c0e9191040166442444c460440da080b0107040e40f0314280700f040c1c5801044407001250031a00001d0740f0002c1c4440000200220f14007a44d0801041c08a2002e003030701c0740142d01005028034031050204400500c84c041240e19640290620802d080e1a088443d03181d55840d0030f03036460130100c0002400180713002c0c8a860281c94490440910f0540c5da5074000f0102 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 789358633 1250 789357383 789357391
    0x9012408100f0b10030605031c1e05040e0c121320010905121b060f07140c041d0d03110901030509070b030906040c1e06050c0109051e160806 62
    0x65070b51584890345502c5140c00c0341c022a0006403513002c126440800050181010b8040e041c00ba204240b034130b0084805003414000750381000d56406074201c0b013800310303454000f038018210410000b00340b101041c22119401403e02030b045668000e6510b6031140720444000000410b00340101c01c0c2e1881c100c1c086a010241c40d81c2000140e00d030080d40c41c0c441401a01d01007001c1d0050303500b0504140340a4403000d000a100081a09038003403050740c2a41950422030380e40300b04019101c8010050010400141580c4074084c5c0c0c6005600546d0110110a0080ac049030460b810320700f1b2203440703c1c1000091440c14068040020210700d000e10800652218100704e6205244005040540c3d507170000ea028002840300101500404854507502d04007044120303600d03d0140d0f010388443d00c45036400290103c0e144807483c0e002386900c44501009180100c19a40c641007603a00e86c0c441c0d521011500001081130000320301000d1205d00d00032052581c1d10040c1d15206c0c00220100060704590014400d0b0000043c14a0344 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 789359883 1250 789358633 789358663
    0x806010b120601090e0108010c02100903090b0705281202010902090126070605030f13030c0201080414120d0b01030b030703020f0d0602040801050a0c050a08040b090106030b09012408 80
    0x200c2e02c80070012222140745512100c0085074410012039001030642041117100c045900b01c070b00000d004117090b0100e5414510060110381c00305410850f83c482d24003d0303c2014041c0003076401291003803031a60002e800c01800750040c00b610407410410010b840b41003411024481c4002c0000e006954086021a0818028420800e40360464070788404010000503104198500944e0025a17881801400d02d81007680c180d0010305c00180010b983c190f544403441012509641d4011585116400569164401a1003036030440c140c214004a040e50410103004038211048a40d07948500c058111002c840c06404042d04050a04440300411742c1d00080c8001580e4040780c60311061406480041d1501403c03c0c00100f8250010800061454040d0300540c450355480f10300f40308541800c2000c540320703c105462b02e000b046121011a0108100f03410303a56001d0004400051601e480c1c0c2c6034031003801c6049a440c01a82e4603441180d044074506012460700c0690402c500b0a01414580c0058442010811100c5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 789361133 1250 789359883 789359917
    0x90b0a02090f0906060f0f0403050616020a081b0d080a0b0f090402040c02150f07170412081b0409060f08071a0a0215070c031d01050f0f070203010c180806010b 70
    0x40658174001218003440c0805140c913501d00c8900100d0b68690881c0c4810340d8036000340f41c00a86000103030b00c0200c14980560707005e400d25200030fa0314115907410841075000d2b1144091001000603c0070050804403881d00d0311001130034a0142c0c0c004050341d0707046200d0b40c007601614441d0080354036000255500583e04803001302c0d4245203044100d14001510031003002140700740051290b05052581c110780100381c1030740d520b84078070082d440c01428044241d0380102032200100e05c0c081000d11503000705030040e08081011a4680d144d035001e40d496001508400b11007592141c1c2000400c002102d80002090014040c0c8802460030040ba59104199800300850020000d02c41460713038804c0c0240ca101d0320110403101e546050401c0300030b041401400044000c20301c4280c009500d5800c80d01d45195404050303594078035140d080318450b40702c0d070000b003007043d0000401e00004c00140c3d800e0041c0980e018103580c0d20b11619034280310b880514902c547c010141504220018007402072030f4400c40b12007280e1500402 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 789362383 1250 789361133 789361141
    0x2010e0312030f07120203070e0f180106090f14150d09082b0b300102120421020c0f03030c060703051611250b0706090b0a02090f09 58
    0x2810704140000740000e9010000c100503040c1240d4000e54010100e5641d8145500000d80c600c004034072043c0c03442d5011030406540e2040c039207807090071700459980242102d03419080906403444071100a0700300d1001706241c440c007800390000f6280124002c1c200a10a0010711481501050151034402d443d0000210001210800070b062600800c0010303030b01890b15680e4400c140149a6030500f2404808880070402410200d44807040c054031216034070040c000088906800041c0c02442250302c8800000c808214450101040a1018051060000014103034520b01850100f1400900507440240000d0030f20400c0c100950000d9400b0031604140e0305440360000e1000041d1a5025a03240c1442c035103d403400b001009030340764000b40e0103099288a45212040e01000c241c4d0000780011500c0003561020325500b4040d0f8500680e03842c2d00718900f01030b21101c0e8a414800c4040d500500096070010340703e080c50400c02c040780b81003941c0681549411400d10759620002550b1440c0119003e00c03460000d0046 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 789363633 1250 789362383 789362389
    0x90a06050c0a05121c050f0a0203130506090703050f030f030a094e080609130f0506070909050105060a0f030605180103051504021f03110f03090709061202010e 70
    0x2201001e41c1110844004104000c80c02c04e00e580404561040d20502e5a0040c03050349060180c81d004115059803042140c1d02c0038075040023500300410381d404054003c0d4203003001c43c40c248207940c02019000083d00b03501c1e04509225150050801440713034035034010030602d081e600f50801529081041d020010445c40554200100042140004940941814080713104900e0051105008100d011642d212120207040c0c14600d41545070701c80c02d404603580c0300014240d4a0a02c0700d1943c003604a8040c1c20800e04242c42d601e12050058208542d40d5000005110b80103820600d184020031501005000b1981401c000c900e80f1301030030480c00e00380911450b05100041c041d0700980302030403024203c0b902c0303103021525490100400384015921030140d003c008009841000180e44a0354004d05181860f000c40d00321000c08255078140941051f9030740c440784d05401c484400405a12070700e901001d0316802c180c82c1103810700642e940008105460004200400c0b5100303801f03003000b10380900741120020014404 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 789364883 1250 789363633 789363643
    0x902010509060c060f010f0f0302210601030f150213030f0201210b150a0824030a1a06040e0d0c061b020d081e040f020d02030a0c0614090a06050c 64
    0x85140d11840110b83ea94030010000351031032103041800014001031b42c0c0c6007102e460a458500400100401940c1300380b002d42045142d1204420203100c148818211120140e420300710203800c216040c0304208150001d01140c0b002c0c03183c0444080a0031840e1444c44802c1e400b10003400d00c0000c00d0b041b42159160103582c000e44031100100d000740019a201a426081c03c0000c02000c1d841c030380b0410180480701a5141c0f00e00650b600d011198842009945402003100750220765012464a2140e03048000f403503a0b101440464545885458120107031030b2001c041c0440440c005110b81e0046180c2205000c0c0e481000440d0b100102480c1003004110b04c0b01e04111303001d0901a1800385040540311041207000d0780c000303403140d424041580c032004103407503c2c040ca1000d00b98840001d5110b0440c080410301240654600101e401d1004000042081c0154046800c0c9041403405403a6090001d80802c5400e410400e100e17110031100b1401440c1000d1900010b16624071400340100300207000c10080c4280008007d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 789366133 1250 789364883 789364897
    0xb0702010809150703060503070902070c0e091618050606070b01090218031501090c0906020c0112020c0a0f021f0203030a0c031805010f0f050601021e0304090608060109051303050d09020105 83
    0x9003c141c0381c40c04500c098054690751190364080e11030041c000545400d43d00c00e5648603176021a842c1509454100907441c26400038010712018041d01e06600c107034441420442000b08247d201141001d10691108405c40b08001d00041c002e44040051500207400c0c034400905540c010b0400586900e07440c1001030004042d010819018412241c03440d000d0f00048403828125040703003030148640301c8900401c4035000c00c2481408056440601b01b000590b0080390b002c4440010031600500b48400003042c41d1402c0040d02041d6641e900200711281542420381920496403001105090715201040d0b000f9541d22000f416172041e16a02c9080c540382a12036000601904401840c1b09500300450805500074200c66081da003005181803100c103081286070007000e10400c01600507000e001303000c041c5c881140c42d80c56a00c6a040c04100004078034902188109005000342c50300401071581010f44041c11203030054059035003954041581e80019a100c01207070040030456402290310519403005031814000c4407 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 789367383 1250 789366133 789366163
    0x32c030102070309300b0c0d06060e0102010f020406051b0319020616030b06040b07052b0806060403230f060c0307020c0109030b072a050c190b0702010809 68
    0x303060380034154004014004d80c0c0040400703544150842c0405e2003500701450031a900c20010f40241e41c041b5105060169101d515494018504601042c044007101c203a600000041100d8841080030f65a0902c6850120911140110700e0513050072030180842c040c0e40602c5062640c0200982000c1c2d10610680714500c00c1c00444005c0740300407071406521850121401400c0a0184c01c9036495248640200150307840081c02681c07816040c2907003450780740e001560585051040c103010198000c02415801c50007601e034204c0c68004101490000c1c81484068122446040184010307c081410901d10354126500790303071a00440d41c00380c00d01c14289045404100424000c0c1801c01c90214003e000840c407500c503540c251804520841c4c01900c0b07130103190001a020494440026441c01d004081a18501400d06642d03500c4616515030814920744056044649801c070450b551410f04108060b00381b40301d1012614202c05e1b040500b02c079540d01421303001038100011a0b01052015106010001c5500d1500e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 789368633 1250 789367383 789367387
    0x2a0f0408010219080f0402010801210f03090503070812040b2203110405073b0901030614092e02040e0a0b0901050402070515060609030d0210110403032c030102 70
    0x140f6244651100e400800ca000c5601c0d0400284000c1c91001400e1090744c0c140c440905503402c1800580d080d03c0810250105c5070841f142c1c880c04242400040c0090a2003941e03a0301c0e00b03504040c145400c04c10070ba48881d40c190304c031643c03001e00b005034a820384040c0d41741c8850040d100c0d04c01000348107580801c20210318011401400200c1031144104120400200681e014002c603203403190120395206468a1608000c00300440c1c1e5044801c4c10050f002c60301d4500500305141059000c0000c407450000e034000c40e000c542d29600341c2800911501d805034003541c400d028103210401ea040e02c0c9000c4180f4120000b0082c0800e18045040c0c6844e030580300541401c011020030782c42c280c2002d600800f010700034544a6040040006501d10381402100d48141c3e004015219000a440120300c00d00e0000c5e003203640c00801440308000d0703034900700400700c101c444642c000c15161200800302d60032100060181d0541510812051010035008140700c00206035454048040f2a111800c0e041525810b02c081640747d400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 789369883 1250 789368633 789368647
    0x41103090105011e05010509011809020406080f010e04080307050d14010b0d060801022115090907030c05010e0604260f0312010b0301031a07030f06030c0e2a0f04080102 74
    0x56001505075004e01516244411000c0c071112003d001a202d0381e400140200409589548a00a05006400103c0c0b000f10440d49803407041d01683c009402104c0010958020070854060701100716004200060710003100f41041d131a101039900c8020314100600c180062411010000d45e03005c001c840b0b81c030340b00c06801d65071558800107a070303030210340408801810200c2c040b40414043c42202d40050b01c2c800c40c290030f103a0f0a680442c810000078002d1b00c600080b205000d40e1a1504682c07280f194840501800c259400c0d442e00c20130034030303064000070304104000144542584600302118242c80340c00c09c1241c2c2400445a865403081e91403030740507041e4000c03458040c5000b0000000303029212030f160031840071030ba04d5008034074230380c0000d10003d802016440c2c03008800035414104c03685c02c54003510300800d00d60500c054032415604541c1c011203959241d040200065080503e0302c0d60040c1c0001c1080007640b04151618601a00c4119440c101e92000900c0c0c0c0781c2400300d2003c403001016404020754640030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 789371133 1250 789369883 789369901
    0x21e070503060c120f09190312020a1701090203060603060d110a06090810150306181403070308070309020f011103160c1e0305070b0f0d020c010e0c0301090c030809041103 75
    0x40800b14040f14904041171041005c00f104c0c1d8800c0b10000b00800d013504031000301c8071451079820000d40a0001d00e40210000440d240001c011588498840404001241c0c4025204580581c0040c491920500c188441650786008072600500f0407a004564402141801c120403442c040f42c80340e00a425100c0000c050343c00c14904c40840342c1030002e41701b02c60600d03071303446041e00d9000800d000710389090b4a040c0005004c0e80e1002480581413094440700c048659211348010b46a8070040040341c0c400f0644400f01903000c0d130825407005c890320301449000d110b0350200e5181189562820b042c407186031039800b02050200213480c007014800110381d642d50740c1c505041260100e580583e0a41c4180c0541843c01d22480081e1075049070340c010010500146490495000390700440c0d108203102c201002f010000b032004e8000f422611b204d0400010700c2002c40c0e0011880c2a80070b03803802d8040c0c1d04008003003010681c04400d01003280d400c1120701e640c41c50075800240003003902405041e4070034404020310407048 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 789372383 1250 789371133 789371137
    0x1a1002071526090133052e020a3f030b03030d02090307060503060d06020d0204170f0d2a06180b0f0f160c020a030606120b010905040201021e070503060c 67
    0x94445641041c2c0070300c101c240419201c004100885e03040c80000400507401c01c003001c40d00c02c0500c0c220300d00d00c060340030022007262145581b031800164841c4010005000f075249074000000c0c00301141c1500f90503410700d40510022520714520000c40210400007145001b0703008030362400d100030140d03603895441202c0e82c0c00942001a000f40a441031542c040303180c5002c3c40850b4003070341c8024596440801d0b81d0780d90602030b500045208942030707000d0000040e00181040885841c07211ba02c0505415202c0d01000741c074103210039940d80100410008405120401d089001041d500710030083c0311880c07828109075020300404408001d01510b6100c3c080c0030700511006080c0110307081314000c6815201e05036610b541070710a68a40315041d0034042c00f184800c0c01000c10420703040c8060120601149d503525840103c96103980420701c80d03013200380c03d07204000b000d188560160500110400680c2020b4000079542c0e070b0071720b03804c081084c0301614024500e40d04011800040000504031680c40c0b030100030210140e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 789373633 1250 789372383 789372401
    0x305032101080a022101150308030405010c182306070c0518092e060b0901091d0c090a080d02011a010c11150d1a10020715260901 57
    0x2068010000709403424040b448983c003940040080c1e4030207a50b80c4028618003c9170f04c14040d150760794541c42c14882445841e0b4002580111803441d100d14180c2031070382c00d641030030707000b441044810524801004110340100301a1034541c40e8241d1074108002c8400184c601c0d215a0715405140425580104080211207400742c4105403080d1b900494101e000102c90141a03469000a80001300c140c10a10450440c00003961100105500903840200001049440760340003112031002c0095103084558100200c140240000c0c914040c00b4110400c88051408002e007111001c44000589841590f64003000c20300a0b11216050315070444131540e0203070007031030754040601d5450002a820710003507000e000c0004441e504103e04003942912101005419084140705400342e000502900b402e5036400d10a03511001d42040c0c820030440940d00c10441041c881c580c0722421503000b2203051141030035074031a120400015003010468032003140da020012440407070641400340040020454a070205401030100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 789374883 1250 789373633 789373687
    0xc2c01090c0e2202030c0418051f0f090e011b031e1109040507050d361a04051f02180a0f0302090a0902042f120a15030503 54
    0x1107000b020188201110400f521500d8882c401e5640142480a600216484028410043e2402e41c0750080349099100008607040f400741e40e5410007943c03048003511000c203c00e00c10554100b4902e03005c3c0500215080380111499180c840e1035040e510b14007501715240d0015890305411081c0f014090090041000350101e421a0034a0b00596443d0b640c00e2007141410b02400c102280752400c540144005000050f04110400200f04040221540a40318800007070f0f42c5001071558121811f040c0741600d0940b50f02c003601d10121500b0500006642e04648207003444042d04000403503803103080441c2410001c0150b07030143d081c000f030380b400b000c0e60340e9004159a22500201d0030317104140078140074042d600741c011844010511003060000d843d00e11041070f8480310f440c00c04550724629034081016500c40c1d542090b114142200d10122400404615132060070541c90f80909104c1400310340302541c040506000340c00c650398641c90003403018003c44540510f4102040320303039403610b02d600955a100e150888500d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 789376133 1250 789374883 789374897
    0x51e0f0d0c02010f0507020118080706111914031c060e090a0321020702040c030915290d0b2a030f0c0c1612030e030a0c2c01090c 57
    0x4003860041c410203030741580607501e0042005118409885681c442c000584c180031503c03101094500400350140050000200a00403107894404083d0440c0700c1c800419015410810b0780201145920340c0084a40742c001103c0c01c80051001d01003411740c4603a4280014003130f07003000e4001d14800190080011901041d210004546e81d01c996103460b2546a10000c000407155000300441c911449103a143c948843d41005103015260f90003c2e00703d40c038046101d00881e880d40c43c441c0038404050b4400d4249550060f00b0b001d01072807500c1703152240c0000801c54011107048640f149454407000c1400c0c4015a1080da03001d070710b082c607951105031a19080c44020101da0220f944450700041603007968001c031081c80340100651650080b0340f100741c001211424061082b200190f548031500b140100040c8064418007079038015504004058803040328105009034000c3e04030400003000800c09070308603581642d09805003072200004460b54500300745481d130030340968000403641001e5030340010702c4032900d51a100c2c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 789377383 1250 789376133 789376153
    0xf090f0d1208011a0c07090e070b0d05041a01080606041d0303420d050a020a0b041d04031b02130603110901060e0607060b010e090109050a1a0f0d051e0f 67
    0x100b0141714040752400d0130f0700a104200001000364202094070003061083d108056101c210703080843d08401c41c40401d5645443c14130051001069492841d084481d001300855810001055510322000d49414041c654130401c504082002c2540305084524140c03c0da0703600d04240c40130300680710b01d24016403802c0c1e482a8201c219110303040d0022910b01d0140c213881b601c0c414030804000714802c0c44a004d5686004065010300180c1c0c032124204090b02c06001ca891701c40e41008148040d18800154a480c141001c0c414400404d811200b2040c800040107240304141c611803010038013548034042400f030600e003011008001c00503a200440c041c000162103c00c0540c0e0f88030400c03038031a00301404807500440c040000c6804180079401c404007036481810140275221001c07001c203850300d000340e001a240d0ba55034000e0000d064a1070007540020310401030761410502c400000240d03016440d943c0390f449908004003010804c40140100501c82d00d20011100300800e900c41404d44484c03010411024038014840f6913 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 789378633 1250 789377383 789377429
    0x40e06040621060b03120f031801200d0605040e010905060f07080106050318070f05120a020609011211120906160806012d1d060f090f0d120801 63
    0x806090381590340b84441490035901d8182c000c00700688030903058000c030940010051480e0f80100314010301d070007a0039660b01e40380020030048818050740c00016410210b0214500c160502c0706c02000b444800007690344c0c0701010507a4000e21069102d19045420001345416000741903000303031700c2d80b4000e10a0b61b0300ba0783c1d655001510313200100c440d4000304a425005000c1a44948044c65003c0c01c1c0c6802005046408d9405601c0e00d03134241e0107030284002d021001c2c00303035041410501c1c1140c0d032560000d000f2032400d0b500151507030003000240f5040041200c030381351001d1500d070082130030035081250143c1e580c1011000344440319022542d405840c8100c0c00403c0941e60b00c0035000c0e074a5802c1c4e03991708944e9105c100c011100005080c003004174455180701130840300700e0501034401c0108180e44078011a40f100d101031111000c400d030080b9204017018080014903070940c00c01c40d00011000c640d0b200400b000600040c00d42803188002910a1504803d5604110b03007104ca0b02d03050302d102510b6604101e0009170f072 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 789379883 1250 789378633 789378659
    0x13020a0603021c05100b0c0f010912090501050711090606092805030a0807060c050403230706030b1e03030403051209041116060507030b1002100b0303042d0506040e060406 75
    0x2179802606101004100030400c0c0f00140040c05241402d40b00c8454440c8440790030b494005000780d454011090001000c1c58100c9401e0004080a08110342441525151080f0040c00980c0d034030b008020705000101700e503503040c00301d0721150001401003440349500e1456444500c04545810102d48038850040341a150014102c4ea001e03a100a15034906001070351100f0180102c0340ca83c000b407110605c4080001580a071030002c8001e041c1032041c0d5100c45030300b202c0e4605100d940c00901814a0400b1009164955909001201705400c40e0070501d82c1031a00402c0c40c0d44200c0e4030183c11805581c40984e030f10340703000d4020800706108030340500c200340e07401c10040158401c1100d40c072102e031841034000740090501d0b01715691010f59428002403051000f0041413082440140303400058000c03641060320982148294680b01006400031030400703040803102e401c035030382140d400c3d038405400703c031a413070720f0035801c82200003802c4042d00b01621540d540441286d1a00300b5500203100f01c0c2005000b060b401c0c40c901e4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 789381133 1250 789379883 789379891
    0x90c0306140a1503111209250501091707031703010f060201060f0e151309051501050d031d030318030f0a02060405121905030a320313020a0603021c05 66
    0xf07421040000c40d9200f80c0c02801c20034102c112003101030000740700024110380e101e8460000e14001d02608440102c3d10700c1c0480fa140300100d0301010500050100342d91044850040c0c1d03401c41c8901c003491030464022403401200e07078030003820f04204c0001c0310410529a07000d03604035070091803102c0140352100307801d9090310800d00078070b000358104081c204500e2003100059030b00254914003580100d40300b8800308442d400b2140c0d4588240d40c540300b2090802c901040000844502e11401c90059418100000d00c81818484080c003004044000303049031400c850303800342d0303070343c100508496940300c1070840d042d000b4201a00461003406080c00f80f4401207004506401c04a80c002d080a140c903007000308002c0d080803240c00c250038070721070b01e5a44e00101e00c0c0d174100754200718003400003580c8032800314000908403052011000b00c01c6006000c04501c45001403040d680da42c45030b5041c40d40740d956a03d095403030081c0b1800d0195101410000000325150594010440407103c504841c160001740d001060a40e6000e032 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 789382383 1250 789381133 789381149
    0x2030607020f06151c03090f09090804120213090308040b010b0a090b0c0705060301030c090e031c050a0b0913030e06070309050402031f0305010c2c100207090c0306140a 74
    0x8002402d125a1160b1928034100003020840b0000c002107110f410701c54240806c030003248000d41e007803014480e858800401044407440901901825a0312000103010b079101e41c4041c00748455401c811952903140c10000103801c00c0701040128540c1c2402020138405075820341b040c80c5560000700b5425517101c01c459516031a40c1b41c0840d214a81010880c190780076054420950090110106259440000440c000d6014252165442e8100510101200c4641400b82010760082192495854001200c00314400342c401c1e0006203030b90b401e4810300140400c030003910751183d811030801c040304d00c0c0180140c41060199850003500040101403040d64410b01780054045121260104041c0c070f0180c000b10b031f01207250821103407180d00d00d078060184211190403c031001d0b511003291070403041d8054031813290402c503d60600c40e4407004002104000c81e48006450040700c582c4400e0890a0003008402e0081402c0c0c1d0080080203000300d0004c00074911401484252030100c21040c4103468840443c03c140c0b50a2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 789383633 1250 789382383 789382393
    0xe03121506210a020d06080a120807090627080604030905151c0b04050c18011b120c051c11030909071209050a0f02030d0c050606060d020c071202030607020f 69
    0x101c05510320640c0300038a012070042c1c00300010345e12601e040c0625401090a440207000d18036503454030401c6080801c0300401002084010088095404941181201e6503800c2900341003159405039901e41013240e001701d100c10b00c500c0740040d002c3e03000a0b05510907030081e43c0c2c00072656203560400032001d102200041390203c0a100d080d007042180048180b009100400c0000c0703e1a085001c1000c3d02e034100d40c2d41c1c5101c14082025503000411002c0c80c0f07090042442c0a440141640000c0c940058450034098200c06c1c40f60043d1524a0061140c1c1e94442d07001003c90b035000900e40101002c08100c9030f40c0000062840b8800d00102000101b07403501054002d00c0042540c2c0c1d01b103002c5a450380b524125941090b200c10450001c900180280d0105501814003112884010300505240ca01441e8a010820503044e00c1b0b1030200b000403411175000201144c0190f61110340c6007410002e0b0264190f0307101c69000e4a480084c20125951890482a1090382595034550790100c01340c4e02d494550828000300c1e00700d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 789384883 1250 789383633 789383677
    0x51c1803260702030a0308011e0e0c160f060501170307051e0a0b0103030302130e061e0103060905010f080c100c06200a020f011821030e03121506 64
    0x55285003074103480050081801e00300c071900080d00d0250989020340c0803421071030040c4005c0520444c2134550310210310300c030f1100070b15000c0c95660b079107001044081210300104003010712501c280302d5403900580018103031298030120b04000c0000c103c20300c01c45000c102c104025990002c0040305485183e900303c0c005e00b103001c040d10185202d0701080c5405265902841c0f03090310004200394a0340340a140641c3c1c0040c0c8556075404010700301e402507048095405410030400c4041c2e9280c65006108151000700c15a141c0c585000603005403d850b00300204890402001266850840300000c003183c99a508881c440181c110034482000c05003400303030b80000c0e050000c0d000407403601d81100508502c0d070543c104e60800e0310303002c1c5803145c1c0010141000603000400300e40c0d1043d07800d004142290f000a41885c84c000030301e544110310030039042c2c86401e40462907458011194005c0c2d004c03010340ca0603882601d0342c50913030f030340c100305503200c116604036400040c2c1050811509104040c4c0b01d0395800ca165010f850300d8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 789386133 1250 789384883 789384923
    0x10020703081b011805030715050105030a060c0306050d0302010e120a0503040f150507030207030305070e060a1103040915031b0f0e0612160302030709050f07080c0403051c1803 77
    0x1030b01e2004031580b5902c50307422039410701540303003200a41c40c0640090b6071609402c2c5480c003440c8800324103a0200c0e07410f060041c802c565012542c8800c1a50000340021403c15410055018180f641d01c86c03540544110820307002d264064000000d10400c480c251120b501841c100c586c0031b4060707401c07204005032040c00010b00003103d5881025005008500e15501111010307006802d071041195010300182e00461502d0070113425004080c0c2040700340c281410b00741d5179100480c506010700d60200080005103401101440014801c550140548070f5060200b1403041384002e0401006200071615845000c107401801581694450305417100c0603689400c162400f4052180e081020701410391000c003002c440103d03054100008a00c0306c041c0e81900c95064950b004150a05030940e008254003420541041a180c25104c0c1443c1e102845040031425910b90710b41d0400c0780d020305e800040003442121800342040c0303c00c0c0c021129504450741ea00098000311402900500d0a5102c0201040030006403008200 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 789387383 1250 789386133 789386167
    0x10507051606060806010306020c0c03060603030313060b0d0302071a040f1a120907050f01020a0206090d1403030a02030a0b010201020c0606130902030102030a0e0d260c040e07030b1002070308 84
    0xd4020303400400c3d2661140c9000b400c1a00a910071205907a00160350528107600b4030a120b500c2034110040c004610f001c8000c07907102d2200070301c900070301e61010843e20200010341d8000c0700390140140061407102a40d143c0650380380ea060043e1040c1280701d456a11382c42c86400300310381c25140c100c0030f00c0904502c0d1140e060500340c0280c0c0200028034003402302c5055150600c041c18406c28034400280718941c502410320003652021a44107045400c00640d41000da11904110380c40e4400548135040b4411142c2000300410014658151140c00000284452070001d50082c2d40120540300c800c01c21040040010387c02c070710901d00b480103260808400103499140ca104c8603844d0f2019140003044001c015070019007240c0c8215844400148d840c6584402d0840800002124102030b0030040d50a1640f0280040034040c044e0030044800b0040f800036036200c0c5840140c84c0100408c0544145a0800d1038010303001c4c001c2c01c200c0c14000d61856102000c4079100013455000c603500b000b07205213004d4007051040000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 789388489 1106 789387383 789387427
    0x9010609060503011403030417010203060102011107030c141006030303020304060b060903070b030613230703110f070507030c1229010e06040b041b08010801050705 72
    0x719001811a4103540000c00e441840645c03c00001c0c2c0381d44a0342d0092002d08103004014400513134150003540c0030b110300360024881e0703110315600060703580281e902c0900010700f416406000700305a00c4494001e0804c1200342c032840e07035030310304810b05450703a540c03040700000d07800000c000600c0f0309481011309610048981c3da1034104178800296580130b0038010f40d59030302da001002c07a0311541c50101c50020485510020300004800d034210b1444120504104900c0141c00703030000350341d98420710a0300d51000080400d54101181c1c0480f40e4641d410002c82201e0342e200d100004004101030f4070a01c4000e0558550b000d401c01d885280160f003000403002400006c640c0c07168124140020f0a40c1281948c0c1120320700c6215558240005020f05010890140c2083c42d0004100a1105251100000c80c0700358841241c0c40c1d0380d6030304079401c03100c017200c030980091801c0c030a405c2c0c0e0788680d030741d4004a = true := by decide +kernel

theorem cover : BRFrame.Cov 789208633 789388489 := by
  have h0 := BRFrame.cov_init 789208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 789208633 ≤ n) (h2 : n < 789388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
