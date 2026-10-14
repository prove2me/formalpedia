-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3637
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:14:49.391923+00:00
-- url     : https://prove2.me/submissions/b867cbb2-c343-4ff0-8397-59ee65a827ac

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 653956834 ≤ n < 654136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 653958084 1250 653956834 653956837
    0xb1f1710081e06070f0903050609011a1012020f12010f030c092901090906060e030115081c020a0f0b04060b0f06040e09070b1201210c050118030204060b 67
    0x101400c80c40b807907001400c07403400098400760588041c00108490b64450318112a08218501080b00700500d03400300000080040114030301a101503400807a08031a42000841012500c1da5203e21031441c60341c14004007500503004122840040b00056503441c0405240103003413049060741d80e8440e0f03154000040100c0038800090030350703115411449095540d039140e0700944c0d603d100117651124809061b49105130040441c07100140040c1051140642d88411940880361140c1c082008100301611318400d5103000c3c45122012401d1000c2d0004890400401c1683e40c02481003a400d00e102e00c030310041041c1d0007000326004141e480004204034001c0361918502402e0161001c96840c0d04040b000789840c41c001407002209070010b1f2030281402c2c5003000b51a484000908020454000c0360780124a030705140b40280004481002ea05030a9454034004190740e245000c0840907001001c00d0f1304001516184880049510910780035501d1000d0711140b02c00c0300082c0e40001c1d44240352050003d1490900d40 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 653959334 1250 653958084 653958089
    0xa0b0a020f03090a05060d060806010803070203070911040b0706090609081b060408090618031204061b0b0c0903010e0f01060f0503071223011109040506040b1f1710 72
    0x60903984000038010080d80d4900860f0079a913031101c00b4100030310040c20300c0300c080c00c21080f44450202e0305903a6841c0f4a41404400e0700900216040000c485040d4282000f040b0010a0000d40410110840b0340d95031600d40524000d08034240e20024819080c00025001040000d400490821040c0003074505000070342d00c0b0001d040707129146855200680349001c1034130341c4690740295a103480c081c01082048461380c4030701858000042100182c01250b20208a554514541c0444c41035075241820380250640310050344003030225802d0840040010042c11150740c000f18680001500c6844140010b8098150409400c05034401d85680f044000e0054010b0f104882c2e1002c0c1880303c064580041c15202c560324060034080c1c40385c26201c1030003d01c5000e08028250719019603140e06100c299007050a443c2080241542a5008205039410346010310840390420341c101c504110800600c808244010100d03210b00182c0082d80c601d2865181c0180280c00180e002d00100038064078003245481904078150 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 653960584 1250 653959334 653959337
    0x5030f090103050a1404021203071b09050c0f090d0606030204090b0a0b0607020919090c030b0709090612060e03091c2d1b0e07050c0607030b1c020a050a0b0a 69
    0x201080c0c00e0903061082e1784041d10440c0010030a941c45809000e000e0a08001040c003a00c4100310980c04030700300300320b1905402d00c0c1d140002034082c6004109400d03114007829060050408001400d500c2c0c05000840b0041d10003500c1d03205a101403401c00c08010100b5500c080d400030300f046030340c04c10002d00c8003005200d042180010000c11a1000c24042d06010300c980085d0045610400b2810810011900c1903018000d550041030909140d500c010b10307007200754421524948a5000c0c803008070b80000700710005d014108000c12009145c0700300301e0302030030301404083c000c1e40d039802c00c10901202c00c1c4211200414080c1c04040b0010241d10000b41c00c0c0c4d00309000b610000390014400a041701c58104220070306410080703a040c0e902e107c3e128001d11002405104d03a10148411001401c511403002c200c0c4215000e0b02c03030944400301c2c0000241132800042c10001014641680400c040c0d80712000d0044290b0010240f190040d028070115041108942040d6485481c105001800700080e50051104c0d140c1c0307 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 653961834 1250 653960584 653960591
    0x409140403020706090b0706050408040902040315050a110f07030905030f0703140105040c030b0a06080a0309150e10052a0604031d090105120102070c0e0106170f0c1605030f090103 79
    0x21a20100c070180160301641041c06c0c0304200311404501030303130042c90300070340504103441c54695210068800c0764010b9004440c200b0710b83c07250072002c0c0b02500c0390541c005244201031000c070300c5d14080c104561040e22000441920045a494141881802894003400e0b01500715641aa07120302c040341c4c1c510035440300315804412040c0a0714040b0042c01014040d80c1c0c441d10707d038611b07030079980d60414214004055401c9503136243c400180c424820449680c9141c083d031611100141017030540810403541d1504030050001c01200701145481308800f00842440b1f5241c6241c4070641100207a00d03111160441200c4240c1040300740e001c0d0280810300c94004e511a4a411017000b603074048080c0d58109a800281e0301441c1400100407500f00070b10f02d1443d080140c000189801600d039224401686513404c442c521400c25001409680e80100800005071031000b440202413624421484c0008001490020342c2d205c040742100610041d0b8003000c180c0b690020a03641c40c0c1c150780ca84c01c0380710b42213401c62900080c02d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 653963084 1250 653961834 653961839
    0x60e06120f16050a06020708120c1528091104020d060f0f06021606020c01050304170711010210270521030a0b010309050303040f031107180c2a020604091404030207 72
    0x1840f000f15108100a4891550076007927640d42d680180410355503501a880003d0368580b0358128440c411b0407990b00c40e9089090846080c4000380034046034140003841c08010700007141c0614091003200d5000c9401580c2c0307074004090300d0060441a031107071110700354181e00861041030015841040e034801364220341210400e403413603405c075401e54410040560420500d10f56503501c2000215401800b984035000541d43c40c10380c480b0254044441a2200820700130243d0b003030f40c0d050001203d000da00380424045c24003074051b000d068a08030b40c1d00210701c0c8040c200802c208003051003500c5042c00b400701c2202070b010a0020192807544112541c0406514140b0003c08135170203485103541242e0404001c1d0708566aa1342e4a411140810314240c0c2402400c209010265100f0000300303000d0820800c0d400082a0b9800702c50341030f1085c80c04038005000c1000c015445990007002c3c00304115449240017001000d960010032407600c11608554201400c0c41944001c17105031441c44c5005506c00d50803940040d9 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 653964334 1250 653963084 653963087
    0x40506040903140315060f090301150612020705070e040803090f0604030f031a130902040506063a06032009090303010b0a0e18010513060e06120f16050a06 68
    0xa4111a0080c04101c07420404440d00c0105000fa6500000300b442004074600170900042c200c0d0080502031343c02820024144242d42020701074208005c1c0400c02005a09051a50240400f07045c8141481c00c1035010030f007642841004c01a40c0000e102100c00c09000703007414184450f066008880c607000031310400c20020550340700000c1c201d100d203030140e4a4550146104808074003030807901c6002200c1211000702c5081584e1440c0c1c5c01d4001d5043c041c000501101e0740d106100907988001d01c8148102c90a00100300c0340d00c206006130000c07010440c80b0210003184040c3c0c2d04000c0142082d030007102c0e89410300100822010440c0c50503000c41280d14451400c4131201004140e000031560f8595070f03002800100190f60164015005003000c9041080384944240c0106580180700501e003241000d0320b00c01000342c0c1c100001d100d03014018160b800c2c488141070045103442070718003a1a442c01406d002880c0114681d06110341c100c52165034095403410700720b155002c01884254050280310780b01369038000030007030f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 653965584 1250 653964334 653964341
    0x302041a041d012411060f010f1e0504020f04090515121621021305010e010b0a050f031003020d1211031e130e07230427270204050604 59
    0x25928000003422890a5448804110710808104ca00b07220040b00d107032030000428013000d480383c1200c108141c940d61400b04a4541c0c2031142c2c3c4408170044d420795205c800f4114060890381a108180e40140e6601c8d94090074070454442c81d440841118501400d101e0305502c011100e01505408580c1c802607612840840c1d0748660410584c4212003220050400c010940845004840204050014141794450300810301300351300110303000800d950b40e0006000551741d074480e4502500c01c1d002e0a900300b00114401814900c64945041500d040100000725081d442c118014065036024000e181214464500811640031400281010030500503051800420000a480301c1030743c5003d01c6202c176449813005030b40f00c2d0b20214621f00e0084000101045a0000d040d03154001d480320758540c46440608031071045128051a9501c850100c00c0004120442103c074255103550241b0f108214442091401d040042c01c0c5040d0b42c0070807903c0340e40503060a2000c4499007880da4020358060019588071410170049 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 653966834 1250 653965584 653965589
    0x604090911090112150b060702040b0a0b0a020c030d020303040c03030809210901030506150405090406020c1c0e03060f01052e050a080109091a0c07020925020c0306070f0302041a041d01 81
    0x1281c117100500150ac0c060708a1650444090300340003040751140713605130859108125000140c3d001c41600c1c50b140c20200048214400148061070860a0660316596000058030000e0100071036075002c14100c49045c42440c0c160000c00c4103441c80c5130520043c102140d003121a80340d010a01d0200001d40c0c0d4100399100c1007080d0142c1520526041c1003004022130a40050815122140d00340041000c00e24100300c20060000ca10040664400092034000c00d5982c68204460280e0810000d2000307401d8481c0030103040d2801101e65501e08980e0f0782e0f240c924005240e9111044500303d41c0740500741c0340c0040041c00e901c803c070b075215001c5030780f64201c400070381d084168001c20482c14001d0782040c01d40310001c2190407004842806d0310b0319040341c0000381820421385000c4020a000d0003840e40152120166125203141c0c0d0000e070124040384000039854103c002c03d00400d0101460800389411720036412540545200070ba031480c9007559860b200003e8116000d088145151003000f45030300c03035070038640904 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 653968084 1250 653966834 653966839
    0x2010905042708090909030a050301150c060908040801110f042c0901021b06040f1b0b0f030714160627060c09060e0604090911090112150b 61
    0x81450541880001c0100e0188141007080c00c1c4a245540c0441c0319003105824010a003c41d12480500204511004c0103030803004180d00800150b20f0041d00481600c3c115050300311004108150b2100903110000c09490013890b00f0b24040504c406c01122101410035035600744001c0151000240c0c4044451141c41d100014a0006110401400d00c0c07200c52500e214041c0e94001c0158000c55940c20401e580c10b030303100c96559402143c0c04e0f0381074440e40034621030360240c1d200401143c103082e16190714207444160701600303100c16010780c00d050b00800b18070100104011401070380d88103e03100c0300721a540c00070340b8000001900801341841c0f6000c000191800e200145804c0a84c542555071160000d04680030395002d5034000100d030700b0085003010342c0f4805541c0114408200c1c0c4203c01d0000b0540b800c00d80141003400719031f0301070140c9074132a50143c4080d103103604e5000520b003c00f8100740d51102202c050840d07110b0031100020460030042a056102e2034480c02d01d44080055000d420416550040c80d100e4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 653969334 1250 653968084 653968097
    0x40b011401051c02090103150906140109260c060a0306030b010b0c0721020405010b070311011b1107170a03031a060a050901110102030709050316050609090417070b0a05130201 77
    0x100183c03a54010b20440005040c0080c90840780d5010365400c4515502c4500301598501c0c0821080c1140c112110240300c0901e40780c20309031306000e40c0400c155610807008403508684141401900d408000b0460074080041031151202c500d010014060078090004440401d085000012009264000d07140a4011513018041f101e0411040080e1208541d43c800c22001078400a180582c030323103219050190082e0a1016a9244542005840c810341e04403404405d0380342032400c0c80300c2080c040030803042450b41d2404407820700c44032002620341005a0410303400051080c06142500800083c0501d50620030380b418840e10201c1000043e622001060303160f004030003000b035040824070a070028040780005060041d030402110012900b240c008548060102d801200180850302c0d0402400c0d11080f480f510501c0c0607414800414058081d80c1071150060841c1800301d0100301c2010107019425054241d1182c4404103410010b0b20030b076094620341c42c004d1800012940230f071025500d0b241500d406840f0300 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 653970584 1250 653969334 653969377
    0xc13090e060f090304030b181603020108060f12030406210e070509091c08071202041206090c0b0d0524150a020c04020418050c03071d0105040302030303040b01140105 73
    0x1454950040540d00f60340404c0101100044d401d01d80c0324040c9003202800220b04620035401850b00c40030802500741e00b00083e00400042c0c1c1e100d60015440007013a00c20303401040c141d00204003242d0360018540ba290201040c0031405503407104c41c00a10741c52003104040d4412050450604440102c122408641c0240c0418480d9040c1140c4858102c80e2610803910503070a0000c10b1420000c440085070001400c280601c451035910524080b4200c40e40401145820b2409000804401841500902180d11441c410041c0306840c100040140b42e02003505598040081000c4028032040303e50400c981601b40c440242008000c606000004001d0180703408484000043c403641c0c1c022810500851240d03046200082d1500d0010b00300074009c01036086801880b8840f070105643c0b0081c080b410700c0006104000300107034400d030882c824845030303452034040000c0f0a004a5013171280d604065050b2000000344030030417155024450403908620b050071400005040115a107210b402000f821078040d21a14 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 653971834 1250 653970584 653970601
    0x5010b03100e180a03030b030609030423030f0a0803011d060603070315050a03080319050c0a03240b0702040b030706120209040b0901060203030a05070f050a03050712050c13090e06 79
    0x9558005900c00c0c000c00405a4001c030451500c0c00700d90f0105c3c0000c0c0c90302601d42203400c0802c0580e82000024010b10708090800c5030306441c6403480380e00c008486140c45443e1031203850030712009079080304a6094404030121030410585a900a10910042c020f0510345681d200c50740309a07250154030000d0440740345880700401200500703d441c440c20323109020480009902d556005000c00217510442c600ca41b00c0c0b030051104049500300c1c04030f07100d1907800c28040140c456850300444200c0c001d1820002026940f803040d100900340c11030b24500503003e4450010514040b801301a01046208680c280b10f00c44480e0103254031040144150701c04214200041034109070285c01902500e9000340c00043c5411100d400500b8000302a400040903800000502c501c5c400180030f10380d0f0000ca141010304009585040013071031446000d001d80b0401d6521408285158450000300c0c04ae20000a020300580c01d10301c0b200b0b0059800b40a4003104028290000540e402141c003030b00086113550f00c0542416920710f40c4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 653973084 1250 653971834 653971859
    0x15030f210f08150f090108010606080c090d17040b16051c0206060f18070c020307060903050a02150c0d0f090f0b0301090b01020304030503070c0e010503060417180d080a020105010b0310 81
    0x50f0b48004d04034548241600d41c0c101d0140280500d40000c20b1051400c10003405841028103410b013920410804c8d0b10781030301e5603001a0302c1c0541c080d02c02e207403050a00038400c2c90742c042c42d0001104100d0001c0c0d00b8034403c044410080b00e150140d000d55454800250001442c200e03d8607040d4096007060002480c1c502d098800c2c02c1c840e800142200c00e50100b01c14016100040880d100e5000c940100842c40560a0404c280c60282601e800e140d10312a045440f0a60b407001d0f03000c8001e10501c2588403030b4444884c2d850940d00f42000c1d03038040320340d00507061030040d03c10b0310004000310009420140004000030000e40c000201d480345500d1074510707400d01a03c83d016108011242d8154401040000300103401040144143c50184600c000102c4c00c0180207040c0e41c40691115120b13034080400d1202080e502038135840d421200d40350081d42c641400344010070410414000a500c65210009001400000380090031811080d07402000140c0e2542583c5001c0d002c02c0d41e2200b1001e0001c10309201003608c40b107 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 653974334 1250 653973084 653973121
    0x309090e1b060c0a0609031106010602150c071a04060c0e060304110303071505090d030504051c021603051b01020a0812060a050904200102010b06090415030f210f08 72
    0x2e209500d0031000425991400d06951012038049a4a041083c01c4c1130b404071400190100c0e00d00078056030b500d40a8002e581e000c0d80e514906800396060007245a82010f0801c965820754040402c0980d00c0007030490701c200d510111001da0340203042281c40e00706588981d48043c004000208107500715140c0780c03901400003401d901c03c0b580510007001400c001c15840f65400c0398004003600c010886181a61800f400c0c450007002640c1894200014007001072404150a58440061040442e83d030858150492a148002003040d1045059110100c203000380491401425002c1a80c3c0c000804c941000482c3c0d03403124541c0c00b5042a0003809000000c0744c00c0c0c00c46540100004191000d51130b102e00020350380328403c0d0b030110741c140b03000040040000504000052242d000340001c0048040703060101c0d4180c810214100e216503900c2941548044040c0980d0001e56000340c0003007170314a554070f003001101c48401c0b011601e502144020f0702c0c13224416001101c0b0010b030359494151039280d428031140051400ac = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 653975584 1250 653974334 653974339
    0xe0c101407060f050f040501060618050f0a0f08150f09150c0f0415030e0a0804121401180b100f060f02030d0e1b04090f031b1b030309090e1b 62
    0x300c41e0f0100b52401ca008250082c004100002d078035003071614110703003100d03c164400d205202e45c201445481030080d81e6100110740065405480207020781d400078100104640000c10000c9429101058000d400038038121400384075078003101d240d15850044107400d2012500740c03140350302440200c002001e410901c035402054003404181040d81c0300c0100074003600079030064540864191004005c2d16454007031b94490000c50030103072050040a4541c8002ca101d10701404102d02d01e404410002c01c40b030341d020041c4100001e0300810882c0030b205150007070030501032010f880659112001c12120f40300c0d00380260172100030f9080c811035649842030550350011186904801c1d80828003c008000d182405441c8090541744060014070305210102c0403d50715070515680241c1c6410202070001c2c001007120640302c2d4140c01e183c85051a51a80044c005a003418000c00081c4082c812000c0351082000c00070a1303d210b5101d8080c0940c4440040045400390100d4512070361040c64500000c8402c49140c0c80c0b0084013 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 653976834 1250 653975584 653975591
    0x30a090f12030b220903020708010e061605190e01090306021201031109190c031d070305101e0e0703140105070e01051c1a0402180f030115060324030302010e0c10140706 74
    0x271061403d0071505000d01c220000d0300139000300408034206842241896000c3d0600ca400e184601c0240d1030841c1c0207401c61001d10030f154001c0400350313009101c02001541d20000641d80e0740440031804501010030700c01100c44014451342012907285c01442d19128080c0400b0200401345068038000180c0700809018060590314000b00380ca0400c1f4080f25518007c810300100841484c51038030f2454006540d9100141da0700d0901e080c460703101154101040300708503000205000d4030b280c074030f1410071485520042c1a044140300e10b9404403410341000e44100c04030781740e03030403d1800d480065074280f05248056011100f001c028641501d66544401044501c50089503240105c0b0307804a001c0341c0c01001da032601300c1d2020303111010502d002c0b0080c0000507001e034024807100d4031400321402c0b0280c00703011300410b043c2c5840806004501c3c0d401c070181c0d0307840e810307010410040c1d888c10043d000f010010003c03e1180a4200441d2040c00c21410f443c24882c241d0350381e0705940d003020020081c9508025803c0f50b00321345 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 653978084 1250 653976834 653976839
    0xb1002070e040f081603050306010908070b0403170d06080a0506010f0e0402060319050907030501110f040b0f0903071413050103120f0c021215130b0c030a090f12030b2209030207 78
    0x20340d1200c81012071098841f03e0b9179081c2280003402d00c503065805440c00e580465130078095069540e0239102101d61000e484d8502c804200c0f0002c1c024021014064000c1c0e20b810340004400300001140b040d468060820b4480d20b9072503040c242c1180507140140d141c0080f0020224005080100085512408042040030050b01c048000816208180c400c1115070344040f10500502500b849905103910f410a1910720b80400d1640820840c0106c3c8507000c1100c2c0c02081003001c26003024200c44890200805507244142c0340d000d180da0558035821158003890704018000306442807485800d05032a04200584005001d02000310340c07407490b246154003004166141400141c90b42c41c0c8000b5070701d40c480301416040c015034000d4074201c10010b1408074401c01c0c10303900c50082190104041e0700f03d0800d02c401c41d62580d031902000050818030344020402801400f540c42480883c01000900d07a00c03954042c00881c1c404410030815142e40501b0340c50034004031101c3d0036072803115800030009030720030700640e8103803507 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 653979334 1250 653978084 653978107
    0x307050307122c070e190902032415030c01090b0a0e09040b06030c180601030513080c1501050f060306130b0a0305011b030203010305150c1c0b1002070e040f08 70
    0x300b10141152200d8110f0403001070240c010310072040a82100000d0050314502407000c1c0c04000c0000180000c1d5542e01c4050b0340a54038107108071180b081d00709211082410311000c076203100e0041110f0810348510303514413a12091401241000900c10f050b9520a0194201686640c5507880726003c141071040b503155040d03580d2582d00425100d2402681440481d1a00e0300078036040816909600e8410004100c6441c0c030505000c182c0c5400400c20301c0c000034a940c0f200c2d5080070200c03942c1400313401e620300030450300800000041c8001e408200c17941103040300d0b42d0b28806d103c4200700e81200c0caa03101d5014800a5100d0400828102e17001c0420440810145420400310b4481c02c02900305aa41e65122080078201500016000c0c0c1c11000920b81140f55601d551601601c908029040c20080015400800e01e4010390308280c90b40c1e02c804600c10b1700301d10505c0607090300400c0d050444a0141c00d030f00545082480c00817801c001103c3c8030b0704503008640c0d01d55a4125420170403441c21565520b0074002260b051 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 653980584 1250 653979334 653979371
    0x3090a1a07150b0d0f06061203201002070f0203070b2a01060f0e0115080f07030c03110406110f0303091507050f0a03020304020103050603060402060d1104080a030203120705030705030712 82
    0x81c00f58003c040d0a40c02414248140c8207e86c00c58081e441092040000096010807103280d0f00103100f00d800c0380b0104d011070041c1400b030b140c0d81c60403132035001081c00c106120902180302c5a543c400c078111140c3c10b5403205903608500a201d0b0380c80e4144030340f9040c8400e64403d9001108406040d0b80002001d5480ea110300400d43d11a41109140c6c440040041c0900700030b01e01c50f85004c030780d181840300c85403406440320b10040070020b007400308158070703070048039940b600903084003c05800306000e0765100d03601c07004001c0c000368400c0306805d420300c00c00080044985000c41140d0156215101420205102c01c51002075010007a000a0800004000001c03500c401303400503001d8a015603a000d40c0c0c23420540001429940c0190903148a90000300902005a03503500c100c4071070101e43c1030080340b04500300c40c3c4000b040c0150340c403459660103028242010540d01000030000711482e084015519102d00100f1a40e60000f02c0b9200c020031010404a840140078041c00020500c0c04600841d02c0c200032451030085 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 653981834 1250 653980584 653980609
    0xa050a14070f0c140f16050d02120c1302180607051c110102030a0b1002011b0f14040e1605030f061507121814011b0c0506040803090a1a07150b 63
    0x7070350800d80040f00c1e401000d000742c4001341b44c88605a540503080900182865a04c0e01c1e00a100c1d07000701a5440d42000140a0030000c03080060000503040c1080d0102d10103948184803985030715881d14103003003030343c40c1c48015121003036002030050910180d00b070015044a42407414481c10703c2070028110314151001d000a5214100d41100414080c400c030040c0441308120455450540e410410249032000024403021003200007480e24610701d00003000181e0b58080030300d0f001b403c030130000580420340f038481d0602c02c3c0c003d407001e5000c07110140e10505c045030f440c00306603040e42c940b550381313804284945400402250480c454131b0445250a040d66219460380040c00b41b050042018040d540c100d20303840103810310003010040d0140c03a00056140008001510000c20b99103402c500351000c074248108108174101820014140350360b51070b16410003c0c2e9a80010001500c148070036000803403100e00340303521829090441017106007482ca01c7d58400000c510908800032043c0c0d40c40c0c0c1d03840b425135503a4800e04036 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 653983084 1250 653981834 653981873
    0x190b130b0a06090615171f030506100e04080f03190f0912030203010602030a050708090316140604030b0403080a14010f050a080d0507020d0f0c09050a050a14070f0c 72
    0xb100c0d80f5201034a01591040c0e40b05401d980055407156400343c0e0815030b04030188400c42030003059a1f896080d03600f40c2160080d12a4051003074988080200036000442d903002d080b000d801c2c424525583c2d010100d50100032200246201000e00030030030f0400c80007000e150441003608000b50f2170317001414014102c1d0341c200e1800c01040d884850307032414072a540481b075107004401d01e0309500c0c0d0342c1046e0b80079540c0e204001d010404c01000107402410322002d00103807a0214070080c1034450940d82240000d0b0840c00c03901070038100d0b1030020710060040c9090411a0226680912180083d95903034034251071072240200310303950083e02d403c2d07079030074050140401e18040e1101c0205000102d00380010b0006e0022117401002e82c591000c0784126485030814180d401c01da0381114072028100180c80d02181c0c210000100401c901e184010225100d0700940101e441105916000c06c600d5a46811031022395490380020025240360740040344000d40301c1c81744003880d681c060810180c403040654036031010610558060f00c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 653984334 1250 653983084 653983091
    0x120804030312180f11030c01020616091a040609090b30010606110c01171315020c0607030e06060f21031603090501080c0d05070905060703030c020f190b130b0a 70
    0x1804c0264102a17560055070603402024802442c100107951a2800f52020168400100f10520b19501ca074582001408401ca049003c40e101c0918100313150300700d0b00030030340418000c41c40031600181c14480c01c0100f4200600041010017150004803d11701d51840003001d1110302110103498500c00d0003200d0080c4071641da4031107008228880a0708103d50441c5880c10484040b0704801102500000d291300000c0a0340782da80281c941f8900b0018528000c0c218000c41c90003c10800551100420310307030720901003138a051003184a802d05643c0c80e03007412105075a0010440034429070b01d00788540380c4014400ea100707002a800c81500c400f5032441c1c1002c0391640000c0b500325400d10805601c0b100d0b210083c0700070709002c030301803c0c190382c8500e0034007514003001c0e0300c0340d5500c0004038220f10a0200030002e04019020a41e12122401c005000c0c0190bd4001d07405446440c1e55a000034a00244c691191800d400d041c80d018845a510350a040d60b010340030f01e0124441040400c045144060401d0040d941d05e00d000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 653985584 1250 653984334 653984363
    0x2060c070e01060c0b0c0f120709080607030c021b030705040212180c01081504180305120f16050c0703050d09140a050105030402040b030f10020a02010612080403031218 74
    0x101580c1e80580006040000d00c00666000502c081c1507641c0140e01b19546980f40c05403072038488098081e0034002244a44200c0c18031002035045088942a90f84036010f5078165a50503c0c2503007521440c00c4401c0040c1d010042c115654020109502000705000342a80d50f51582d580009041e44c11405c00c1e000c01407254020b10400382b462744851408101e015020700b8a122020380041c190750030003007444101604001c03001201c2d550b03da00020080c805500c032407904400505005113980c00c014800d90f600890040428040c010740340803244100300305008550b0003101003c080311030790082140e004a6124000000c030003e5028449255043d419903a46c8030f60f0341c030300507103000f074022010400da004802100d0140116640001120f62103a019140030580d1443e1a0100f45050001e001600e81030084040d00590340a0340e800910041085074000d22007940c64445100c401c5050301c030018502c607010441040024000e1070105034040c40b050f4000f0380b4003108020071041c00c0c1c0342c6008449096a40d00311 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 653986834 1250 653985584 653985599
    0x1030c11060c09091e060d061b0504030201170105030d0e0d0b2d06030c0405060303070c24141e12042d020d0204050a0b060d060905061c03030506040902060c07 70
    0x4d15402034640d0b400e48075035080180125610700014014500494a906901c2d0a020041d00500100c6248468441401a1b02080206680c000d8001203001031000307a01e10b8070011180c80c000d4147c1e40700a016006802103504180c9208907000c1445400c140408d4058010a100e40d00c8148a55044080709003c81c48002c6481040d902c058201e520740c0030400140300030794a0000ea03411107101e0540d40010300d0f0b2102d000092850080c800010700901d800c42c0d0225003018002c4891400040310081c2c402c80100b043c005a0303144061048000640a05020080e1020705002e9410f0400c0c1c1c3c042e1515142c0321000440b20300c0c20703004550669480b00742a9407210800f00e02101da0020b0006100350700a00340301340e070000b60806503513103010303100b81e031203001003a801d080c50307842044a040e005108079900d1044c3c4031800301410991080102c128640b80c000340980c02d043d01e004000b070311101000500c004090340d040d00109070207000550010342c4c0e40c0f101c00041c4c44030341c000e0a8011080b80107000c070602e000b10 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 653988084 1250 653986834 653986849
    0x51e090a0b0d06141806072001230618270f03070c09020c061308041203080114030f150709030b0432100f022a100c090501030c11060c09 60
    0x207451800d41403010340f49419020170800e41051507807600d00070711002003c000c52514808d50202c0d505518244c0d84c03c080c040410342c054808102140002d40e0b40d90b9040030050442c4000c10608001e18000b40090320381c03000000c41d041c41e00c9203101118424428000f01c0307450071902c80180803966000284036000e00406105080041800b60400d5141102e54071505071200d00c09010501c01079201c40c545e00400c2514001c2c2c80c051310b141d012041006c283c0c0c0c02e00504e00c5100b882091980c900311800780e03109003808240700c000c180414000304554032140b101000c0f40da4004003040c040128050022000901c4607014500a501070082001d03030003445640e4048603a03600c3c800001003001c0c030000291603040410401c7c5240c6c822440090314509980c1540c6c0a4812101c442548000f00750b92007280841c18404030a604090b0421501da540f16944048100c4040705056800308882203020007566100342c202d414807403218503100500c0101c0d00e009610707002040c0c03800300b00e030302002c244401d15081035030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 653989334 1250 653988084 653988091
    0x80a0507050606040203252703060e060108070b1818041110080c071704060302040f0605041406030a090f060e0d08060901030b0907031a10051e090a0b0d0614 69
    0x890451070740c01c101c96100d461100e401024041f81d4104022031240a000340c000d03000c00c0c141e666041190621105120240c1d0340c41d40011144070703240640010440c80c0028501d416500050300426805084c542810300f260846454a55036111622000c14591580042ca090b00e40001440c010641841d01e00840d0322000f003400b450040c0709600c0e1540c400d9a11000650f040f164035005c480d0380d11583c2c00e2107122500c441c1c141c03c01100001a000502c44d61507401003003140c044005980d141515550101c8980c0b140e44100d20000122007040c0c416850004021500311548100c0003545006964520000b0100800d065950f550344981400c18020180a8406103541502d800e0b1828035000c0001600c0c6481800050010403080700051203500c810010390000e1a0442800701068054401c0c4151541e0122180e40144c070524074002401d0400b11050070040c0c011024141500d600002881018400100700702070301ca4640c50040320603107860000001c1c2e5401141c001c180052909080c4102100c044e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 653990584 1250 653989334 653989339
    0x1305030607020a06050c04081f0507090e060103110903010c030b0901050418060e1203090105010f12081c02220302040e240402033301050a12020d0f080a0507050606 72
    0x140d0400002950204040d4602548418001500d407210b806c500c80b02e0042c1d1704131404a104199004130900c2d010050501508208001408a0b40d900c907401c903081c0b4103e02c90103428055500101b4000d42c080d03080000781c2071021002a0424500000007800d60f1181c00c1480007007582c0750440390041c1400070b1024054074041c4c81c01d10640c03184400f00f1070a01e0076050b01400710359031100305d099108810b20050b0045040c520086807242810000380b40200002c0c0700340002c01444200008881240c0b41c50060101c0d00002c82c2420401840401e80e445d400e91038804809039400c01620b140041807184007101442c00e4016011118294410b203c00c43d8081c0704016030a0f8010100200300124410f5028a8080301181b0015203480340d1000c84e02d003035034000d1011a00d58807414231400410000300c4110341500414440303107050342e950b000d20400c0702240c0285462503d0031112030700941800307500d030800b66201e1403800000160a85464806030000c030b0070034001542c006001014040100301075604207404 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 653991834 1250 653990584 653990593
    0xd02071a041b06020312090c030f060703060e013501020c0307060b06030c0f1305040f09120c0b071103040504060806060109060527040f05090d0f0c110105071401060803130503 77
    0xb0048041d645c0c2c06000741c070000048200c0005001103030188800101e942006d0103c80e80c6825414845032101e00455040c40020300d09040041c9200c90350715054100d95040622481142460401529003210030200e04401103440355000d000d40350900c014030132880d22801954231010f40d4502070b402e0343c01e0401c1c41d034401d540a00c14400d0901e5103904860b1240006294070f130340c2f401200140034840919a100f141e209241003004030080c0c883ea0041001d4500c546000350605060f40800d03075054080d50300113019005024001181c4500501c03060000c14103113000c5904040c1d98800003010b80360640c001c140f06400038002d010603035801c0681f12028000608109040c40b104c10651080d00c410341044408120010b40001000d44459102100304800c03050184140d00e0070f0b00c0c0107941d40d095076240c1e0b00045ca01038416100030b80300d03445032076600d80d00071506c1c000d40120030011100d0f030f00698400e0f07400c00d10041c01410203480034031694000306485d9025507214028440d205243d00742551055000390003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 653993084 1250 653991834 653991839
    0x192303030f060409150203010e040c0b070b0a0203070c080c010c0e060c100b1c11030c0103180605220c051509010203070210110d0201051602010b10050d02071a041b 72
    0x141500210350111043c1c4001401216905004412022000420202c20b01c000300103e0364498402005108a0240f11185140d540c1c0390b584c8082445000c8002e40350014210100f805402c480e002960898114640b028000e485501c0d50210f0768090809140b441c0c0d9906440710070300e03400100500c2d42b100c00b16400c0e4100300140000076218541c0e4070f981c0c1c500c0c6030b5030040c0007160740c2c4007400e030342d071400181d51440c00740440b52130700f0248110b02d0301c2018801e103c1d402107a0800d601c00c2c050b09414208454051041c0380302079a504c00940800b50003051025106103404540d1110920100c444a003d00408505245440706000303844104030303200340c0030a60400c0900c90301e980000885017020b42c1600d485101c58201c41080320020043ca41d44103260140350104480247d05400c002d00544002a80380b03070319002130405a003200c400b2034000d80c2140c0c0c3c40040c240414060005098403902e254005803801c8142d644030710028003829494a1104003040a000a102c000b41c10349070316103550400300845c01e0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 653994334 1250 653993084 653993101
    0x70b01080c01050412152408061021050607090e011e030b130204021606150503120a030209060a0c0506060d0b06191206021e090d0b0919230303 63
    0x30440c020101e100c10f43c0c4040b01d003005480072103c00103100306c0208201100e904880f05030303c00e41c4600b110356082c04454000c0ba4501c400301c0c0d0a80202520b0490700b58244c039041c6605050700d4003c8007261804462452800030840c00e0040c50320030030107692140e0130b4a003000394290003413204bc2c000d40100d40000411034031060890003902e06680c0c008502d003040b40e45610119044076031100380250400d001080001681500118614800d80304060921448000f04034413901001d4502ca4aa03042e03120030b25072810800d000004126641d50703490003628040d0840c01280c202d51124407090000b401d10a8410180227060101503001482115100391041003078513500003501d405030405102e10307240c086810b941d00a004a0034000c081c1402c0c2580d118200e03043c05c074001d4000050719000780740e11030401041542c810046031071680006045e00d40b0400f440c0c640030464080103040c443d2910501a0b010700e040e481c40c1207015401e00c40e86010500c074811039a42000120b415400029a074001d100744410358 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 653995584 1250 653994334 653994337
    0x605180f0a0b03010b100201020c0118120e01350c1603110703050609161e12020406180b040c0207030201081317190f0507020d0204050408040911070b01080c0105 71
    0x28508500104031841120000384c0148041031025078051584000e00e90895019000341c04c100d80608004c0000c5800c110722901e01d0262124010500c00340403103110030490044d401458210018036101c01c50792800300c01e4800d484182c00c0e101c041250ba0001d988800224101d115a0041c261440c0300d0070101c041090303a126642000d0024117005101c0c401a0100804010502c01560000101c0c1c00780d0138209002078403500d081200300c5100981c50310224068840c800d8800310640454410300065207000e00403102260b14101c221f81c06501c5800c005140b00403c90603081007080f4140006081c2c1c00d900800c02100d4030304507580150f401909040000d80e0700050f40c4c0380e01450240c4482500c0c2c00d03e24109030740341105841070446200104195505a561201a5501c09040d44904d000003504040a60301070180042c020344c0312072003045407001410141c01c040d030090b104c1d050683c2000d4580c0e00c0401600c0403046100086000424484c05121940303000900501042019244079103503200001c045 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 653996834 1250 653995584 653995591
    0xc021f08040f0305191d51030108010b010f1e14180112060506090906060f0a1106090312060d03020c040609020a0e0603060d03110c0a03140609010b09180f010504060605180f 76
    0x2014202d0700c0320990803001c007240c0610391400c24042d11011f05040c0055a15042800307010740030741c41c101004039a54090540b84100b02a240c803145d080740c0030a031030910032a00700d00b0f07200c040180342c0000501045891001c0c0c040e89075060700789001039030721400050955612b240c800b2001c07414901c0070800d68a840c021640f503400151018407540d6950300c0402c03410b00c1106c00005000c0340c0090248a01580240f10089800c0f40d83c0031f0314110b840b6032148650b6800343c100190000c1146001042c46850711007800614940700340161500085da49000500300c40466101e41e8405400081c50205680c2c024000d44011034112041400e50a00c03402146200c81c640500605114503c148010618001c0080302c00900c4010a4801466180e203495001a0045107900c00390b4890b1001194a403501805078049640e005000c800c6c6d0781e503e04192200b241c1241c46141183d00469408614080c000c0c02000c0c82607000300d5010038620710307040501540345100c540710460b490412080c4a182a100203401c0d41 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 653998084 1250 653996834 653996899
    0x304120f0f12090f0c15031a0d050a150c090501140306040b06160807020f06071208060411030a0b0315101806050306070c021f08040f0305191d 63
    0x142c407440800d8210080141101c05418007818400b40020000c00d00304420903540d49801d1140e4140c8031810980c1a204507100d52440b000720000c0700102828074840685c0c100340510100c074400d01040e00c2d81e403811f0b400a0909000f4a8076003290a03d22604001c00d100242400c1c600b500e801511000c9103241c6010241000f0b10a50302d40c00030711003036074440094803940c000c500c1c5000a1000c03203180034040b0340c0c00258200e0080d4060b121070030151030f052054541440c0c000405c00b0350710418a6040350504001040c83e0b1740107540700507c2c4122903003e009140b08400c0044002400e01002040520704101d08240d206641c03c6001040707150f0a000b2014000c0302c2e0050000349840e040c5c121504040d020b03c1e0032180e0035100d150b040116283d400000010f120b802602d000c0381c05011501c1c50310380000017a42050101d100800460002001984505101c60207413a1150800700f06030303010180507241510034400207040889400c0c0d10304500e020a56100c40840c1c1c24080340200c40200e80080c010100c1015 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 653999334 1250 653998084 653998097
    0x2c18060405010614040b1e0a0903150b030a2a030b100504061d0702010609050a0f06090209011704050a050d0503070908010605091f030503030106090305010b040c05190e06040b0304120f0f 82
    0x11000b0a044000034480381f2070140880d2940e0b031300f54008044c442144400d8400c0100031038081c900d0800c920031362005a00240150008410688980d86609a401038508001540c45e00b02011401c00c000a54091441002061018180f001542c07011040d240c0205200c0c07460404100468007015182d48a003282c1c6c24403800095030b98000507401070910341e00c00c42e00d0f14185403c101101034150f100184180358504200046a1548080130032405411078150124000821807032000c2c1e002e030340856016200d4011a140081c00342d03121410300d50884510804644040300380300586802c82200406011848000c04c096490940001c0810300701034035078510301c00311407030182000c0101840c601c040c50f04442103e5595954440081007403045201c00c0e9071f554a0070034007182e40d140c0303030003884109182683c0e0036003410030282c030001c1950340001000060100f08180100252550030240004040d400c10894992420b0304000400032091401c0b0340c10030401c020481425030b0045194050a0064507144 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 654000584 1250 653999334 653999347
    0xa06140306132004050f190e420912070201170a0e070602060604062909030a17031e09060c0f0d15060e060301062c18060405010614040b 60
    0x40c003030003074259010354202d414a41045215004190600e010354800007d10719160840021402200c0501d8511507503504082c585c00f04500003113046461030301d28410b07268803814006c020544040741400a44400844040801c03040803000c2c854642800c102c007080515210040e80000c003900034102c850f43c01c40c01d42c3c4010a00d0041302c0c2d482903011010340d501711089aa2075a502039038922003200e0b8a80b00301c1c100343d8003040803010f039040814642c00c5100f0443c02d110181c1e029009070303004402265018441c0c00320250210780e0b203101c7c6440054a14140c1a44e07420651a61000d0400441002820044150500241100010f20300303600c0307034081c2c21301c907103861410711890348a12900840d0002641084040ea03071a00c0c0f4a00b19604903509030b15208102c50024081c8149030000344186404516a5035501d5a420030840c1d076403c0762100c8401041e200c400003000114040d403c54182c0005d01905401c000e8135003054400c15000d41a1801d00302c0708100307800c280c001144998024400300c0e00307007c1100d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 654001834 1250 654000584 654000623
    0x106030c030e1515040c1704021c0b0601120501030b180f010e03030f091204060f12020304030c02042007020402090d0209132010081b030a0614030613 66
    0x50014811400581d0000c0e03920f00b000e42d42001050b1010101e4040700720300303180d4504c1d0500c5100c8142c801c1d030b200c10000e0304260030200c0951100078000d0381c1215100c502c8104428581d450441c4141c419945c02c10700341010000141a03503483d2564280711441c0000510109400701c0090303604c890407a10180c040103c02c580b00e400e268001d0458071289d820300400a603808804809540b00705160762070910a0381c0c138805440d40d2401d150b400100b49a00820080c8113880c801d28a101d811a024184070340b45d5140b00c1951400c0340d1088174181c00040411210b0340c110b01e0f090041c0510b00c2e008074076441901d9048a0303001490312403560020321440d4006050310b11a215001d10075402d940081c45110249012110740305009103039901118501d4004203010000355120740c500740c0ea100c01070f240d5a40c0c1624580140c541e00c0700940848004d440180070300d06c400803000002c61140d82c42c1d100105141d0f207402d5419901000c095035881c4660807407010030010321156022400c1c10b5400010b501e1141488800 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 654003084 1250 654001834 654001841
    0x5060706060f0f05040b2e050c0607051b01050c0306120f010c030b1c0312090602090910061103180907170403030507090506030601080a0c1103071b060c0b0106030c03 73
    0x990b1000302c203100042c880744881462412210300355002d1001020081c10001c0900b001c42d81d20b0b01c0040780b0204140d540380304007402554030019091540c5000c4040702018a041000c86041d0002140080c0c002d0b05816814880144042c041000344841d00342401c2d00c0d200c502008010a01900e6201461030261104200c408554810f55000708422940340700000d014000345400329020700304154020880a03030321102e0404040d011b03520401d4180804040038090940c018080c0d841c44e40034040342610340e6818119500403060040d2101f00700c2d00d4001c01800b01d021310014541d69800a1001408040f2451000b41c1c00113401c0328516402d40d5074241c00d6848901c145d9250440b0f20f0558108010590550701c4513000d203515845440140ba40c0e1010401c0c41d00c4100c03003007400620902c0210305461095041180c0c2079019040c040061500716050510b140c01201c01520308480c0e11200900d03802481d00100046c001a14080f0f4001c110394440c3d029110041c440d070380c201a90b4118a40c0a14407035032 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 654004334 1250 654003084 654003089
    0x10513060522120303110c0709090606080d0806030706030e0703020d03090e040602090405010e010302131a030d05130906440303040308010501021606140403050601030302030307110a0c0506070606 86
    0x40d038000741a120940707100c3c03250303c40074101c001c607107061210050312040383c0c2964002d10002d40208051820a5a542c0251042c800e0850302147c650070f0201d00106c0502024602514036510561189402802c040c44d00c5540e522031024545030500c2038603200400304045041c2c0e5010b42d214600502903190480721582075500c0403c4420096007844104101138004007001130007114140002e03601c80320754501484007880000d501c840010b40300500200706400c456590341c50b0a032211240c1c140640441c0c200340f41e026840000500024110100c480001c400c080608000c080c1040ba0340e041203511011700062140d00740c142c01906000b07100f03000da0a01210342d40c0176902161109010031400b003d40d03d800030703181240490844400070032a94800248a030412241d03040e040384192170a241914803030b4640b819070300707042d03002c000c00700200340d08000c1c03a4000d41c469401580d0780c1c5421000207041d140e8a4040601c260024080400401c10303446150f015580c3c03c40b001a070350305143c40d02d0001040c05a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 654005584 1250 654004334 654004387
    0xc03051e10090e0d110303012720071a01030201020c011112041503050619090f0605030d08070219020603041e0501110d060501090803160f05010207050109110105130605 74
    0x203c0100241404200301c3c83c26200c544071020043c4882c0c45076500c0c1d0109008101107910f403503120351890207403464aa401c044080e40c0000304201102200100c901c007141c5400c1c00d08100007240020800c80300c44c203c6c142a10500c8010043d41144d000035104c4105244103410850312000c16071407c1c20600c04d00d0078040010101a90340d50756103c4580d0a00904c1c21424042407404000480900f0500c0c50701000d4007070820100300c403904101c0280010700304a5104004243c4d00c04001c10f40d500e00708100c481442c00c40e217600440b840c0c4010028170700317545540381c0c030031680c000194940162205d1003a20340059010701c0400785040078444111a81d51401c501515079030138030303400008000082d0002c0515511120091103c55125001903c1300c00480c030a41d003442c1d20400c115041441030342d81c0b1880846c86850f00b034003c0101c0d41c54583c02d9802c00d000594445c0d544402c0300e02041a0b0003440703414242c0a0074a10305102c1d00c199031140708141e600c1140144100040c00c02074840e440341c2c0300620404003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 654006834 1250 654005584 654005591
    0x513060f0f02190611130b03041e0503030402130e06070306060801090c090905090102070f1a060904020d170408151006020307020901031101090f0e0402040c03051e1009 74
    0x12800000d050003100110800030030400d441c00c80c1100d00c0440d55003035280c8420200b0182c282e8556070315008116032185049202070900c00b110001c641c1c05040360062058641c502c3c1c0724109818160500b036105d036140c0b410b00715890754070b0740081d5001c01900c1e84550100c840031140c003c04c04000c1c0142041803d0390000717002e0701007000040e0749c150340300f1404e0310144e9445070710607a02c424101d011107050003d0711300403401c17554041185500c0c540285903c07028110001d41030030b0041d99050401e1642e02740c00c6400d00f0fa0000246920f00b45013030120b42c001c4088408100d1801c0c141c0100324044038219024240600d0125000161001e03401110020100c4404450340c500d4004403c2002c0c3c07100390740d003031200d000030140040d03041c1c4000180da81054000f07144141c90f920f503a9038010008122480315040c0540000c00003580740309508400300800c41800150403d240900c108011601c0014142090601e04403d002480d83c3d0b00d40301071500c000b11641d240c40364440e00781e1104c2c0308100d58800040c8504 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 654008084 1250 654006834 654006839
    0x1c020f0715020c10050105030a0b04061107030f080c0a05030406091103100f05010503060705041707050a1401021e1b011107092007120c060b04110a090503010218100513 74
    0x7916030080c580f42161005032090315540c0140751082c3e544c00c2c4034507a4190301080011001c00c90403c800ca07001403090b400025014410005210260000f9505602089901c60410b148a40003c0c420ba031000705000e84910303040300d03200003074004d001c090405098942c0d580d082c2005c000000800c0000000018100c4807503400c0d0302c001d100609520003528000750306110000030181000280706010f0505d9071101403c142c10800825a02c0c480c0080d28078041c0f082410000c0c0540307403106040e0251100e408141180144403001928151658014034280302003030300100c0c150b032400300b8500585140748200c086080e68840040710b82c2c00b40b0300070a580c140600329001864809640c003403048003000084a1a00346030078a00c1030b07000c1c0130b00c0034060040710b10742505d1306426201d1000c0e0b03480e00b88550400220648107101013030440348102c0a26029000000b9004d043c6070308100140010003046000354940f10f154401904411001802c00303004d072030001e161030745950041080c2c84040e0003051804403020f0707 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 654009334 1250 654008084 654008123
    0x90b0a0b0f040605030c0402090a030804030309140603190c0207030206030117060105010f0503041b0803121503030a020c1905151903020406021e030f0a0206011a1c020f07 75
    0x2048261030710a0044024580050074980240720031280018044c14000701d02d4800d00010390311010381c041e40306c10305500110008600300c010b400610300a95400002c9070414101e070401c01c58810000341b00701d109204012800702060a0001c42428491001c100c01c1d4504100342e141c5189908000d41c410b40200002c80d81c0d4011140032884410303c0c0040307034090f982e15401501d864400c1200180016130800c0001c5c00320f500c0d404804c00b164403181c5075425550b84e9108041c21a0007890070ba480c85100030062000101380c0c90350030041c10000300c0185280000154000c0d40d1044603840c07070390089122103401e07041403501c80e07031440086c0b101070304440c070780b100c4c00035240307042da224810030301410300704100b08a0400d04c0b0b40309a909650694004203a4403100e4041d100d003484410802c070391240300c00c03c007000c0e102e840d01d00a49085080c507001031906505103030b00c0980384141d040504200706810f1200d0710721480d80b541c51400d01c1400000041c1d0707a58008480f20001d11071050090102070003107601e040d180 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 654010584 1250 654009334 654009341
    0x7060c050c19290a02030c070f030c1202031303150f020c0715030605060304030305130c090c09080109230703020a2c0105010e1309061103061f0507030c0303090b0a 72
    0x114407030000d0803d44140c05001105041c0c40b40010312440c0d0b03109001030100c1c0095030045400003440a945030401640795100c01c00301611000407000603030ba0000c60003c0010000c0ca01c44940100d0014605101680c40c9440c510001840041c01d0008004e9240701c519400b603100d00305494005070199980d2291245503940c83c9807900c00c4041c9014590807199030700d4401d1240074184c6200900740c0f07185450310b4508401408000e02880304600101782020b001410554083c80106080e010224903040c0c0c0344800341510b07295520000380790b4100740038280080e2440d00c1c900c00700e40c580310150800352401a503407440c02c1c0b11500003d4004846803000f00f035060b200115101280381e5030296100350107500f070300c50800210070701c1a180030666880d252402ca151a02c480040c07900009000180c1d20420f44494083c8c0351884d0f0020080c0000205000160401c0d81d480355000e01c5030390800c40c6401d14050000d001d4403e440001e000c02070f22520071420544250005244940c10800040c1c0e1400d1100c5c502008 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 654011834 1250 654010584 654010633
    0x70c240504170906040e0c1309150b13060c03110d09090b030a02030d0e0d1a090105070504030302070b070309271503050c060702030c031b0102061b07060c050c 70
    0x140300c22a4007030b050501c9050112840d41402070181c600385442c1094020440c0005450003684400a002905100b02da1407904002001907200200d09924414107500001d0074681244810395810001d0703906905151100300c00300e030040c0c5451400100310b400c4c11101c00103241c101072482e0195141d4007040d40d030302a918509036145603008120b0104100c0800d9601c000c960390094054000140a606e2140140340e4141001800341c81601d11400c0d0359125040c00c488244154840c900390f40138015804024800d282d0301840c1030415914260075034801941c1c4139603d00c01c844c03800000056200c00c05102d826240000c007488410802d00d44044526407040f01101c0109200d8145801103600000c0c1e8a2154102142c0d0460050541c10722100c06105d01d43d030010206981501ca00c600c441010303242000810809030304003240d500c1c070f080c405000900b004d6020f402c05c03046a032101a500c140180c000d04981d04241c0c00781c00014041003043c0207032200d0003030012103941802890b41c016811818414210b15 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 654013084 1250 654011834 654011843
    0x9010501080d0905100e0102120f070605010b0c0601090207020d0c060804020f010201021e0310080a120306050604051302071b08030d0f02030f01030807060603061d010b0108010608070c240504 84
    0x303898500000448603c40544a01a030000ca48100403501c41d0140140d42c0d00c1070313010305c152151508070340c41c0400c460b0b2050503910390045e000a1355806024041c8a828050f01c15824440c4c0b811307070003000036951410b06000e00b9140950015481c82196124244e6607140c50b48000200c4645585040183c070320314080310140c0c09002c0042031003000d50300c10302c01c82c1c868102e8019090220400100880b54036000105454140e1051030404601c038002004500f400d54443e04000c048a0014280282514025488103001d000e081c00300f40010390741c500350a818203c1110005032501e210b400c1c031107980c0001e4400c43e6500c058032000482d040001000916810300e00c840e0a01007c90314444030740807444102c0700d040c0b00c0940d550041c000640741d10b0080c040c0c103005000100700203803252142000c03542d1030302c8d0801d0824050742c0743d0807040300300707018010714507100b420012000d614041d006403001c040109075404003c003180d4503404012108502e249102a856401d240e5040440004001000162070566 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 654014334 1250 654013084 654013093
    0x211501030627081611040e0d09080a1e110901030c0602010b181b0f0414100e10051e0f09090105030a030219080408010e0a0215041412150901050108 65
    0x4a80a440740d424041d4540c0080241d1030844007a903070344140c1340310340c134101d460206140d100c90ba85d5a0f02d00030b241c038840c0648040e20000101e000b019000d09010b5111240c140c01442c0050007007440600b038641110182030004269412a2038241c001180078103100e64400070020010040c4120f1110040c01c0e5020783c0c000300a11140c0004200c00a603c06240c2541d00e5011000a0010303036550154000d490380c0c000400f800d0204140c910046600541c001c81d164408080c4a00d502d0700d004d22030342584441c2403c000301581c81010110b2404000e850803541030200005960340b49076a140c0200700031190002c546520342040580710503260303109070a500d100f84101c0300040707000d1802145c200394603541600241101e0100e01400901840021310507290124140000078043c5003c2c01002c1401d0000c42c050043d12542d48108400c2c0c0c1e0110300100c2543c2000d00042c002121000717011401000f0845c0c40c1d10021071420001440c019440d65101c9034600034506200340c2000540165069404580944 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 654015584 1250 654014334 654014381
    0x3010c020a2a0311010201020f031e06010c0b071d120a06060b16120c1a0906090c220f06121509170c071502070f0e062115010306 57
    0x210b03281c0041d00184407420603810b5041000a1a40107001050a8103000150038900c031840d00120380d0304102e4000201060303210103141e07050150850039900034800d080a0015045d1600d4104920074002c100100b40b001da002c20f0a070000824a0b1060003030310051034000120064549240c5841d0864001c03510f20703052400124001403240259000040c00f07020107076480215448002c003252400a81d1014040200b00d00c1340032400c1c03d40d0112210130980150b91107030a00203089413502c08010541c1040781c03c05000040e8681d161420264a0b4003000c14250781d0064402001008110a58034024103528001d40005c0c0f40c4458065a82000d000c1c0703000641641907100343d0010360f0000360300180040ca9401f102c200610b07024001d040003d10b124101c40c0c100307484001200b80c111010000c070b000341c1d100704401c00200c110061100d02410030b4650909480c01c0c56404910340400d074101c0c03401440c0c0000c40140c1001130802075450700d01c003191050015075960b070400000810300c0e00000c3c10556440c102a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 654016834 1250 654015584 654015623
    0x902130204062d0c0f0303110a031b02010606141b150916060c0605180d08150f0609040e03220f06081b0d0905060a050711060f0109021803010c020a 65
    0x2645086400398490034003007400341d5124a105e4035043d80c105c2c20705650f80142800001e1250103030880031680d4a000401848482500d8400540d84100c132045a060201c14044140c1c44800c1408148180c500b454541d50585400700c10056860512000340c0305030020042e0750300c0f91011b481c1c083c0d050035003611450002c440d00e182d665240780c0034580c04183e0803030300c02d4001032003a07201c1940440c0111840300040e101d0307079017070303007400c03620600032000078071150620403091003040441a50940803a4150320000521000c0340141c0102200e952060b5600c1c003d001040100740308440e000e901b580103643d668062454407100c4284107008104846250350340c00f10b059401030640340d026004081004a13400c96030341800140b40c0c030000101060b26103595200700080c0e010400f060080300140000b142c281740c144001040c1c8561002403518582c011002d020308002950109030644071a058003507500d070100c6010402c0b200101c12107581540c684032200316003a41c0802d600602c1c51180342506101c0185481 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 654018084 1250 654016834 654016907
    0x5070f0c0b010501050a0509060316261906170f060109140a090302100914010c05040308031302041b0c11030705030d031e05012303060403080a090213020406 69
    0x14020103a486920060000790301507009814009001d1807c1440c10103c5000b00d409a007040c0c4640c00c0f0100082d03110071016400c01d01540f2400c250744240d414582400d28094400c0e00c0183c0010b051004032403804020040d039030809070161400d20b100031000842c110038a543e500c42c0c0c4810385068010403001042c4803450340660000580000301134580c58407041c888000500034948102c0c03e521504461403005003003800380000789401401d0f50480d07004d103820003d0139940722450000030000100070030720004a00d10203581d000b20707080c0819000980e662021400400e14484000c0500304000d6910a0003644070107400c1d5214410408480001d0492080c5945c80c003485c01026403540155002c20362a501c84d034000480c40e4441600142120449201d040860350f0030b0300004035a405286504882c1c0070349460040c0c01c04025002001c9901d880d840040030314001074180140035407100c641005651344c4c02c2585164010003801159602d95072030018000508102c1c4818811080807042c1003400302204 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 654019334 1250 654018084 654018107
    0x40213083f0901110d020a200307030f0807060911030d1d060c031303050a03020d050307090b09011106070315050f030a17040b0f120a02070c030b06030102090306090105070f 76
    0x44840e4071001ca0704070540420b0b008140781d41d042040203c407488042c3c1c0708000c1807185001c81e80280c07905010a040a00e48441d503d00340e0107400200715200e1300203841c005a41c0301101d81100b042010400c0510b03007944140700b0000090103031414070b44003070b05101188460401c2c0740b82c11004c884076889000425619540c00d03142c040101003202a091481782004001440d0307220701d200c00e5038901100310443d07600c00d80c40c50300140d03019403200c1d06050405404001c45411040c55060241c21482c080704002e0291403140180900000042900c60090b401000c0c0304000026580981d4200c0c500100b000b0014008040e45680c4403007041c800041c5418000307051404c413403014001c2d0000301c80c142c64044400d030f40d082811403c030030208000644030806401a0442102c814140f0b13560380d000031401017880c10080c00718054284100a003400041d02d10b0300000031281d1250f1101002c0d4bc1301c40000b0700a0148004941e0180a2141005506081076201038070070050b1f602d503494002c4810404484612288 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 654020584 1250 654019334 654019423
    0x606030604021002011410050901060822060603081c0609060302090f150607080d0b1c200604031104060801020310120f0f051b10050a050904021308 65
    0xd00454058102404001c0c4141924000070031200c8445d80241700780601206c0b045147c6802d00c100340a60320b4680500ca0060a441c030701052681841020324041c41441c03d01d91100101900a81007048107d40008005540000d802e81d10740d510030b5a00d2134100078288013801e54501d8680040790030a0548100d40c10780342c002e810b4901175600d0712045244034101500d10315003070b6910142035529541c1c0788001d00c030a41c4100c49083d207613022108143d05440c1e5081e0801d10590b184040103001034405c02000f0011500480000c0b400c842000054040680324490180c200000282c04010300c22805049454a503080c0c40030080740d6680d4038068200c0c001541e9201010300e40d05000c02002180f1780c0c800c0252070003070300443c148a80750b95901340303101c260090448154008514200b5268900400044901000e8030038a904a05840c0000d200d4400c40e50314900b03000f0003060709032494403580c3c1a2104490488801d80001e9140c100c090b59401c9001d12200040d1001c112020710706000304034134100c02d90362 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 654021834 1250 654020584 654020593
    0x120c0210020708070b0306030c10050a0f0e090703020703120e01021c0203100e071214040203010b0904030926010f0509160e0105130b040c08010f170c01030e03040b07080912060603 79
    0x405d0124000d90f800689156498072602225001550741c0a02403a0040c076a40c0301c0944d0b4078694840a82107800c0442d920050205d0040041101d8998481280d1720208034503005940702079500c1c00b9140103001d0b24481200307603d058501c003600c1c070055000f8075071400c02c081c0304960180d9102a00003030784012904c2a140c0645000c040020f401c14108150308400241080060301c502c00d4441012100480c050100c002d540c4801d000540c00d00307202d07c01c40007100ba9a0540d50b8640307914050003020031403041c030b0062520300300213165203841085031000880403240240584107032946645c010742001d5441d100e1034040c614042080300c00c680d051004481031130000c2c050710780c40c0204011300758071f900100d08405611001d846500365030300e1245000e10b0203641c03100080c0d541000c4107218602181e802504e1545a05001166076540000c0c26034040c40c3d0920380442c0e050040307400c1c80d08500959204808001d0049520b0041240e02e070090030054109a0308080b0388000c2140141e954801500c185805400c03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 654023084 1250 654021834 654021839
    0x211e0606180307030503070f17180f18010b0307090609060918141003051002180d020a050d0303020408010c031404030806041805010914010e0601170a120c021002070807 74
    0x140c01c280d0034403182006090b01c2c0600d640303884a5041d980310314000c480450031800075004006c103940c24003038001d003680515420440d50300140328900d000320300050b101e0000702c16841c00556443c0310480d070343c0c0c0703401c000d13001e240d41d44d81c0705d0031415002540c6510100714071460114196119890140441c0d41941e51b0f01002c070701e0000c601d040c08165040506141e42c540700c0102c400745403d5481030040401c0d03400821040e1460070414200301070f5660b41d03210302d801002203000d44030700003180d190082002c0312202150421840010030442d9a42d1060f60080c44010800c0207044d05075029000301c40081009015402d9541011000c40d4038442000304900134490100e00480e1144801e568000e0010f000055190307490000d0003c4410310a030110740c00ea445004c40c0c0b04010b01001402030f6200b02c14024480249038100c403e171034501c14090014031290441000301180320070002a030080b070700100d09000f40384811400821115180d203041c3d015100740b203aa036010b03910024411086a4102d00502803c50 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 654024334 1250 654023084 654023107
    0x3100903020d03200c0a12030626010e01090c090c0504050d1b031b0603060b0c1203130b040b06010e030f030405060901090503010c0c0c09020901140f211e0606 70
    0x2224103440d480e13284030545031505807610b070018903210b280b002c000c15440249241110304004500509420103051000c200200c038036255040c810305a40499030030440c0400603d0500412624551161035800d040c500c20500541c0c01740c0b00d05550410703805104001552000703403098410b87c41408c3d0001d158120000c01f26411a01c90381c1c1c81810000d9400e95156039031200001003202c0880305041080036041040781640520418000f003600c0144541008018170b42d041c1c8409207050b11860703910000001074202c80d03444c02403403c6158403002080702e030309050070000c001280031200b1038040b9030b03100c0340244a4500083c1c442031000d1110300a514003410304050141a8101401c0381c3d042c0924200c01041e103603020b00403400d24042940c1c800c8800c5689091000c0c455415601c80c00030580304206285160342e021880e10700003040c221889603566240030080030300c0e108504486c5c00c072881010070960100d249829540c0907200b1000301e00d40c0004090010062400c007a81e881e54001c8007009500082c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 654025584 1250 654024334 654024341
    0x30a090b1605071218260a05030f09130608010f05060904050a060b060f0415080c0403080304170706090b0406051f3c050301140603060a0f0f1a03100903020d03 70
    0x303020610b082c1d410040c6080705c80101d0591070f0401303122020307109801003011140c490f20b041c104205000400e201c00c8540c0300c0b152a4402c3e2660070380d200600080c4c101c1c00740c440901d050300c1e0b08000c400400009603100c491a008044400700100c045050402007902c1c1e182c10346000d0302175500032000c3c2c200080c00c2d5486400800300c00c00c4c440e410210034003035021203102c003002400082c41c01103807541d140d840c8030000038030703d59004000342403601e41840288041290641641d90040c0d10010122900030311403001c00b170500545800620484c00c22810400701f203612810b450082e0721400090007161100303040307002c1542501c0306602d54440380301c008004030111488141c00e14200702001a050021050a0204d081c1e440603203100885521141044035080134801c4644907880740001401c40d047c144c000945943c80980281d0003e503c68243e90705c54406079004000b542a5100100200254460920f10700b170200700078248a4003841800108201543c010070003400e0b455800340884013089101076008 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 654026834 1250 654025584 654025613
    0x110f03060904231b010f052d0c1c0306140d1505100e01060206040c0909050c090901090308010b07110105030a02041e031202010b2101090206030a090b160507 69
    0x110031683d80722012071001c00c060300c41074032030041c003400545020903ca049560183d52003141000550310031824103030b91002c16600382c00b07803100f0f00c90748a41484c649507070441c0c501d0070490030100000a1040645c900020401994080d008512642081c240c005400b1501c06120782101100c8804000c0820701d0101b00c4412520300c60000e60080d449050812030444504803000131050310540c0c3c0501c2000310780c15230b950040c00c192000b05020302c2c1556039031000300c40d2886030b0001c140e1200fa003a01042014001c10b940070a01070000e020511f0035903806400790511003002c0d004500c01c000045030f041c40340c2c4201c8c3c2c0380c00d40015001940072041c6004403420350000307110504980c3e00303001c04a94501000701d001400110311804040c80760a60900c001d50b0208050100250382c5407850840c0d00340c903803011030345a000842508558001e5048400303400741c4502c6c42e00075030050001003080010120f650107031501030b01074480480f03d6540e81b00003240520041e40d40c00c02141041c002d030f10003d507032095800613 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 654028084 1250 654026834 654026843
    0x4050d020a1e0501080123010f1b0602030115031512080c0303040f0b060402070302072928050a05071b0e070c031209080d230405010e01110f03060904 66
    0x700300c0d90701c18400680d9880200c0700040d00d90032840c10006036a0121100f409003c081d011344459504103010204805902800d41d414407a80050384440301c0d0044080b8801c50030400d20202e1a110f9610340f400081d03009018001459082e46c40e003401d03403407092262034180c1c50440040e50311542801c0c1e242600075051203045464503001c00052501100a10245028a01c0398540300c20005840c030306980c1003c0300825460246105015101c0440c0c0e00003201000c0f00e40100c560542d07080c3d464130b14005e4640b140c015501000001900071050300590b88000d040c5e031354803494440b1008204000310741500c10a00034000180382448005c002c1034038000104d2282b015400729205d519a5030504c01480303101160b00f04007013480003502409242d0420000e5050039004001040307080b0340c03550303501c449000e10b110074401c0e41d07902d10561080c0c51b6024406606164554440d81c00d42c036184c07400f180a440701c20b07144006542004c134001d02a006120947d840d494020181070700f1aa41c940900030411070040040d00e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 654029334 1250 654028084 654028099
    0x29030d0203041a03060a120609050705040e0c09060613060e030d030e03120604020d0903170603030405010f0309020402160803040302100b060720040c27210c0e010f0e06031204050d02 80
    0x401d030200d1f45a10304803e11a01000c16515160b041aa007403c003e03234003075070003a4141281501c1d000c80101d0fa5489584040740e4081007502c40801040442c0035210101a001c2148030000c1941a080b02d0103035101c183c101c003100ea226840d50030840c1507881344808441142e20501520851081521026074407401c00350006007428140c7c0c01810582c2d00919068012900c1c5c035a94840394890880300799030094007900114909450480020501746820a0386810107642e92626011135890342c04464082c0b0000d01820b02c02c454508040c01d01d5401510210058407445500d40c1001401e40502d8421500042895050480540750a4a824a00388460211040c5084016442d940368800c1d000300705002d0750b481c860b940800302e0070083c0c60811580e4000c40540c0d40070411400380244100b61150781c291a82d1031510313007145094002c4206503040b04001212640000c54405410300e154011640c092038550040d440b01403d00d03890301c0902e1480b05d8184020002407090381002c02034107030b14a05c09403200c0d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 654030584 1250 654029334 654029339
    0x50301120816030f0e0114031b07080310060215010617060607060f06050f0d0f171c140612060a110c0609010207030801060912060b0429030d0203041a03060a 69
    0x341e00e600304003000c42c04113a4100000651560100c0c911242c00d000b82082d106e040002040c10b01d050000800c50100c2e11084400d094040c0c2d80703c1c0989149903030014110b03840b820006100b40d203a10300e070b00078400180300e1044203408000c1161300084c100d4120340c451500c4441740060b0080301d002d008008a070072000c00c111300b10005900303104030764141501610000d0310a007028100051a064040070030f115640036407214000c01d40c1655284c000d07a5001e80701207e80520301304241e999010301c041030750210744131070703201400000a038000d200c4400441c03103480384594a0404104020148101c0b5003032503400003000542480c955401b6042840c40380c1803207401e2119415900e4603080040f00c80c48001d0b50042034004c1056000921f50b8058074050501c180d4150a004400c02d841c01c1c940e030094403458407905d2400c2161aa58403a508803d80c1c0c3c4050002d00d141140308200c00002c1e812042e01a01c9400100701c42240b010043d203040d28540980460040391003410314039142c00107441d80d90301c8641102c00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 654031834 1250 654030584 654030607
    0x20403020315060306061c0f0f20010e030a03090e0402030a0f082a030a180807080715080c0d09020402090603010920030106020a02090603190b0a05100b09012f0109051c0503011208 79
    0x5400c00b07550003010ac5400c0c80c40f6040010302c00449025424080d5225008076000260400c1c00d000c180c0e90b14400a14055503075000003841c18540300e10240107001d90000010900644d107000308482d42a0030040e840b03174074116000840b0200d4038110560039800c140926014144102c2e85214010f0300c654501d00103540701c50140b82030100c5075100c080c56510214081040c24482500118040c0c2a030400032498504040041d1a500c00da20190349110307511442c640c02c542e1130740e0540c0d842c0c43c000b8010a40300c0da12a107010005003c05e0388000c8646c042c02c85003c000b10502400c40341170360519800f4160a08a945c01d0103540d40b000703000154540220a01506161401c000c5280c92500641020b051414250490f1040781d00241810301c02c540d170040306100750f400f00421506440820f10b000540580764410139244081c0e003584010300c01ca80e080b8034200840c0150810141c042c0038000707a80c15a4062100b95410502810760100820024401042082c0e51000503c88403805902d6080c54000711510 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 654033084 1250 654031834 654031853
    0x903020d02010f09082a060a020616020102071208041e080d0902030a06020706230705090907020118060605310e0f06070f031103060109150201020403020315060306061c0f0f 76
    0x82d001c4900040c490a4113211b0880395004820340c2e010b83d070b02443c06040c000000c0d02c6440c000c00ca84049109100420030b03070740c401d40c100e5507041d4209080302c4400d910600d0040400e18141c80698030114000e10301c01140140c00911446150b00c586150b29280c011140c0001400f00d4050a80e41805042c4a44000c501580000c1c9002c0d03203ea2070000ea0032140004450600c03100103142407401c05500208080603030000100c400b1124220f810b41d0319035030b03540d4089025041d005a90407490030164024800c00c2410741003042030301c108454280600060420042181401035000340707038001030b41c151004c00380a03a400f503031000540c07005650217030a000b11081e11b0704409171440c03000070f0503103500c40d03081daa07040c4140041d800445852615500706040000c003041c15602a00f0007480a415155203d0350003541140c0007103a0140a031a1610760000d0707420152001256202d00034052080020407500d131800051801100041c0c112070300c002c403030325803288907404507100305e80184800c105140881ca490781c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 654034334 1250 654033084 654033103
    0x7111203010b07020a0f081506062104020a060e090112030309020901060e2b12090812040306050601031b050c03070b010b07210215360c010903020d02010f0908 70
    0x4190783d903103081500c14895048090341c0f1028025003070710303000d209105020880b514402d5000c9400e0700a0f44035600024810b2190b040c18020311489a4901c0d50324401158100740b05500845030441007075030341c1e101035400c0c080c400381d45503021035001e005024540031600140f1140c3d0281c9400941498903030701040460a082c0c00201c04217591000b4030786a4600441d19624014042e00c08050407106010201031910300d4280081c000f11348250250b8416104e0414040113010000440f20303480300c035202c90000b55101c1c1c0030076981c1034100000110594020301960118280090380c0c01c66050841e08120303003d03001621100258002000b0316000308005c2c11055020740f0054034615512002880c10111201d5039680d2401c2100c134031081c0360a015004281c0644e070914071050314101d941c40141c1c031030812090f80c40c2c0c4010500756405d04240200320a00741003000b001c10013107400c0d00c81ea81c0010349504a0303a200080d80321a40701240b40065104504d8050007001c1414001c07a6282c480c2d170801c0c200001072 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 654035584 1250 654034334 654034349
    0x30c030408030d0b040c0516050c0a060c05060615030c0f0d0207111201060e010b09010201060308070503070c17060a021803070602100b0a030c050d051c020c1002010e060711120301 79
    0x2183c40b40300004540f29401e141e0000312410851500300d070101410601824103100c1c2000115080c2105103c003d00110741700107802000c01010a8581340050600c00780c000041d1004e1242d800081e1381800c100e4509071041181405503401c69a412040c842980d210380700d010300081c41071003860b441106c40d001034080e0311b110f610203003c0b00d25040b050061803500c0001c000c0d500d85c1441410403441282e00350b05410746004944007540c8840d04001030f4050a05540001e089039000662001841004030103411207510413290b00041c80c1d607400c0c80800c4004c241c030301c101458001902044864240d54018000d44040c03000302125400c1110000342800c450307920803805604103d00b140541c02407031103a2601808100e903802042804c41c2c8605070350301d2103030141c1400b4071442e030030440a01074204600d1100514020580e02d0b454010b00009440c0c800e00c4200310301883c14902c1070907070b040c010300405c15104803103030062000d42d60701c400481c0c140e444030110740b00c01c1c081d480003207000d002c80070300850107003d08 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 654036834 1250 654035584 654035587
    0x50907091a1222060b180c0c07080706050a03020304020a1710110c0c0d03090e100504060e060d0b1f140a06171308120a0b01020f070f0611030c03040803 67
    0x4034580b20008090040840c407040e400842d084924103074110f10482c6080d00008000385028502000c05e034001800c0307249115001c0108104a0510352070002060240d4240003520303065130b40c0301740d070f10b56a080c2402032602080d4280300408181e446580034503845400140704552843da0345603440140101c0c51401c41c1643c001400c180a03100142c080c000e541850b064541e0b00d410a00c48005442d0b024891640707108904481500040c1441401f40001400024000d0101c50908090449100c0c0c014072500e4010340c00c3c40000030705c0785a403140d03ca102c1c1d0b4000c0d01030202e88046654008015100820802e00b2041c2c0000c6802501184c15007000542402c05840342442041c404204107448207030301040820028400c0075110142920318540c00859440c0071051101b91464940124083c0010000b08401d040302001160329454000e208131003420313002c0c1d444404041e0062904c4030301d10b0040529603240001d0401030700384294060404d0044030800d99041010070400542035a1080e441041c15a10 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 654038084 1250 654036834 654036847
    0x10209010305101202010809010e06090a03020c03060c03010326030a06211a0a0603120804110a1a070206070f050c12010501031101120b03100f11070804050907091a 72
    0x20188a8540c200080007a00c51100d03180c0721601c3d240d806004c1d4020304001008011401d64442500964043c0c140e0303d049e10384a00e401c403120342c1c0d10301c01c2171010f074018400e1120316802d504010802030300400d44001a645103071708540720040d41c40700c202d000c10801d65411a6071009554441c01945c0140025200820b01c42e20304880a90745060111200841d0002c2d100b01d2800a080d2010110003880a2904100c0d10741e01d40014200800d2141e1020f0030210441c1c1896a4042c0e0042e0710501c070318801c0300d10b070760400380e40e100303200100009009841050065165803044450000094406a031004041034940000e554130050010411041100d280d1b011100664291030841001c42003448190000c01c00ca625648890420010f00e400076818024519000000d0742015040350012204c09011102080e41032241c40380145031204800540d24542045824000c0c0310f81e040b0750003135400122050405003403c00700300014401034020360900002110010340c0c80400500e08540402070391002c1e8480c031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 654039334 1250 654038084 654038087
    0x411120115290d0506150708031608040f022803080301150c05100b06191e0c08040b03070513080a0203060f040201082716031e0b0109180204090501020901 68
    0x2103031030528081c10203040c0700701c0181d00c82c60301c02d07110340030094030b4081442d440721000f1075040005400d90380207861001507410180034103c401503014081e2904000308a09800e60100c8030944145d40082c100581402102d016140160400d000d007003103070b002c140d201202029000074100055004690100001c00108440c8040f2541c1c081842c0070350800703030304044041c0c0e0361a44400c09000c004941940d207185051264407000b0586510f42824282e00c2c0c52100d25020181c04455009100031000803031180310382400384104410750245501044442c1094201150203080e500f00030003603c200b14080c00141c800f001e845502400400000c4007402c40851035005041c00c1010045c141075907200e45209200c0143d900044403039008a10241d500020410400c9440480c603403440b00b507119204002814001c0441d69801c201140e01c6804e9808906401d030300c05005c1d0941c1e0880c050482c200900040140324110340004480c02405240000d548210b903002904481c04003009442c2070f035000c112010310f0b5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 654040584 1250 654039334 654039359
    0x801090c09110301232706010509030d030b03030705030a0f02100506090f040f0813050112051b0c010e0601060c2a060c0201050415051e030702060411120115 69
    0x102040748003406903141c0041d0b500403030710061040c400e52800d0b04e86550303000003122656054210303005010313100c0401c40c2c10025a28011605034480d80c1241c0d0300c013041c070f59070003941142d030907800103400340c052400c41000a03002025003070003040c3c06010030080b01c00024410301c014861441c0c46e455030103014400050003480c00440c401402009032400302401919500e6030949680184c5200510f040759580c0c0c80c1c040701400314900d00800a80f00400c600c0b46500304d818450081d01d04c2a40c602001200350704a0000744c40042c0e8100c003c01c2003c0001c9942c07185240018503a24581000108421282101551600384241e21850000b007800e0010700c10400741048007101000e2940340320500c60004800c00402e034056100e28818407441880380400c40e40502c007643e0041c02c032000e2001d08032200d10030280c00c1d0342c8420015050750b001041151502c8002d4810b49000c0c0549034000d000744d50741c0b6940c014015a234000981c0d070103041740c02607890b8000240034000c1501d940604e0341c808185003c0194100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 654041834 1250 654040584 654040589
    0x3191d04050135030d140709050616020d0b09100e010b0603060f030a08121005010203120c160203060a0207050c06070302071503020d05090f010e03160204021b3406120905010b0301060801090c 84
    0x200310400104200c0b50354ad820564043c0710041d045001c03056603d100003450b00c504118006c109031450070401401081c00f288108244451800a02c4644c00d2090820b00301c40d620460282d000f031052020a03079a041c04002c05811990282c2241c03018241e40c0c80d40d640a42020200b1860304100c136040003107030102503041d80000c0c10280011428842c0c04014000407120080001000c1c0c40301103010004403a034400c00c1e124050300682907603d91b0410441d440069170016a0a07210f82c41451300500349818164115008580c156000c0c00c0031a04046808078a80101e207241002c0503024804405048035510a40d17000c0c0d00e0b244002c05c89034400f00201c07030942c1c0c10105c048581c0d40082c8402c62041c03480012440080b40e04440040c0d03640b0403800300d01500e50081c0859000c030320494103403d882c2e45c5107c455051021283c1003060231240c5042c0400c5c8103c169000350b80004030807030032103044411030b070304188034503849400040790f840503000100c1d0031206590f000b030380c49a4440c0d071144180702260100102 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 654043084 1250 654041834 654041837
    0x102070b0a1d0f1e0901050604030818040b0a080d080606031b160f0c14030c0d110a0e15130e031b03191d04050135030d1407 55
    0x4154103a10302034000800e51195100b0340d103100a041850303588a00700c902c1c0c5030714001c0024446a00c0074400c40100c0c20b8000307800d809019440c001150925060b010364040b290301000d1a40b529100c0c003012560807402d0030415030060b0303c0c0c40228000f666115500000f4104c40001030022822000000b025030001814060007500c0c104240212407022100c40c080e03001c0c0c0c1c034075115a43e4155000030041d0303045884001e800d0b8950b1207010001c025001d51130030308451030023440d000c09400708410141ca440762741450b1070344442d0302d50114000881c90711003543d040740000c100201641d9944480c0070006021a641064181000d208012038500743c05207030002d10100c44100704040c007510601342e80340701e14584540c0c600c65102007a0001c10040040752800004102a83e2072015104000303490400084030410034021408104a047c0c24035125160480c1e108140000c680c47c61200005254403410031040b004001c0e8000d1203040110410042c8003115807048000740500307020b00c0c14400501c1c06040c010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 654044334 1250 654043084 654043087
    0x1e090206041509030c0807080609010c080105130e011e15050f010c0503040918020406050102160b0c1203011203020c031207062a110616170402060405031203060102070b 74
    0x240e2900c10a50307054030a4620b103103a0ba92401801038a40042c80d03440104604420840814044c90100380002180c1400c400c42d621501d40e0045e00c2d099403800c00c60000016443c00041080d4601800041402819480e00080094807030b41103d0a40b41c0c02444145541124141148620b441d032107401c00409190136025046400d000c00591064103500c0c0344c7c0d0404c0901541d640c00c0c0310041c01110020620136008001180c888503004080d00300034201079200d2131604000284a50010486070b070461480c0b480190040d04080c02400a5006440052003500c00c0080401503512418003c501030b01800070181a065060b00d0300919110f104007000d806900685d60603940111810182e6842030382c0f00c00007203002c040c05140400105c01c08034000300242130503200c19040640080c20f1001c1c010b001410358040d580c811003c5c000300c22100b1806d1000441103411010b1024a4401e070a4000b0701c01003600d0300c1c0c04d41d12400030745003800b980d20032459842c000050003250743c0c0400040f401040c0c0300c4002c6 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 654045584 1250 654044334 654044351
    0x50a090b030307060c030b0a0807030506010906061e1e0206190b030307030503090a060528020901050423030703030518011d06071103161701020408190302120d1e 71
    0xe034490043c9140201503545608014a425000717400c8940c4005002e088000c0650795001c286a44d100300748010303615030241400215001c08103020b18000d44840307460350000100b000c00c84a264001c14990b0400300601a801c04244e070103480d142204241551380100340340e043c03c80845d0700100714082c20940c40e601c0c0021140036a01c6c007000303440445030141803086d120341d07450814a04041d07004100814071440c010400c00a0b503050300d03c0f0707407000110030030071b07002c0840c0c00c60f06108030b104508400f070214009110030041940010051287c010010a410501940ca40040391074481c040d041200400c1001c0b0b904158002103103107001001209281a82442000e440780b05540740f442050140100320014090b42481085520000c40d5440541107980d050b040004001220425000d40a400701111901121070f040500a850a0b81c0344000940303a951240100f00c01204c0155a04400354043c20361407110408107400030b4162080401c5003c10200c40903464800c0754a0b2070034002155918001c81d2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 654046834 1250 654045584 654045589
    0x30304081c180902250b01290d02250305030414010912120f051006030504033c021501051e0909010605040501061e36050a090b 56
    0x3410350290003410801051404004480c2c035007000074464244401100001501d101c02e80c01407801038002c1001c040d45910900c1c030003007038294041c40581103c41150060200030491480d00c148880d035089001040c0d044550701a14907007105c01c0c1000d40e1980498004a020240350350107860107050305885115072000c0e80c0107400b6010240c4050300c00d11021032107844c0840c0960000701c1694104040c1e180e5961034800040c1040080b0340d50300b19590418200c1e45440002e4002d560240402d070781080005800c1c500110001c0a0042050b010042c80044500070b000d40c0c181c1a414408410030f5610b01202501c816241c4044c21000010071940f2803000203030300c601d010201605440b4115020502d508010606984041c642c004040c2d005a10600f8404c200340c0543c001400c84605070360500040c0e9a6081c00e8800035a40d088034071040007000d02140c2110300c40c405240001e45203a00340402500700080407040d1450f00a400d01c0c41211444c0207215903e0111100d00040061074402d04ca1400088003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 654048084 1250 654046834 654046843
    0x3020d1a0f180c0304030917070f0503072303070e13050111040e073f05010f0b0a0c1e0318050402030c25140a061a0f0d0302121902010b03030408 64
    0x4030343c29048021001c82c042604c0b81100388005c0c59040216008400d01ea080c42d5212840c40c070036400c40c07942d0003500081c3c2e810b01151503022140c10703c1c84098225141043c0365420040c840c0790580c036018140700411850058480d8602480042080003103440c8180341644c00c4a05c20b55081d4018201440304004c0400750015159104505261044e0a1501d00182941701141e0807000041e00350440c0140765035071034807504c540340382006810610081c2d81e10030f6044207084040c0160f044401c010441c000c100c0b0b001b00c0b03154404620491140e203a030f805031500000c07a2201b2500480004109929035907280c070500c50700c04041d0408403801c40c65801c003400766201e10700c140752480311003010520070081c3c0201d8141d40c42607000c2d004194404400350389c0181d280c4070900c0c2c04080ba5007a00d80002d040f4644010140ca4442c0c0c84050425610000350204001e9801c1e01407a080f4110300c20400c80c6801956170201510702c4880b906d0300c064280316000400b80c255245810418029031041c001005100380006 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 654049334 1250 654048084 654048091
    0x11120601120608010c05070c0509101a0903030d0b03012004060f020f0a030f1106040c03020906040f0906020307020c01020c090c031003060e071a0315090703020d1a0f18 74
    0x3403550140e00440c0110002d42801c0d8020070b900e501c0c0c1001031161a401c00b00510703946104107106105a9115020840c080720152603180d210003140c10103004104184c81510405a80030180e06d0410851600113031859210340d011756601520384188020034102409001035424604030580710354000e071502d2080724020344c802c0000700100043c0000c9003500a000e104c18032100d100c10b8132601c07041802d016042940c186107200c009111284680d103185404101c60380595800002101c036107155800704401000042d100c0c90f402643e032500400da0031a24031803031300300d180308001c0944c6034035200c40c02900f070000780080e02d03040d9000300c00380071280d9a4410300d1907407001c49881103584076141c50701c51a40d4045240c0005010701c0c6002036010304040c4c0000c0d40c400301c50480183d80340c101903c034003034503d0703000a0700e40500d11010b002c0025050f02c0d080c580e15a00c0343c840c0c6001410042c90070405816240458140b0103980001c458084150511140c2e41c014a0f5051b17900c10480ca00341090481e5884005 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 654050584 1250 654049334 654049337
    0xf0608030a0e15160f03021e0703020d0809040c090317040e0a05131217010b070f0201030f150b030105090105090405060f0907150201140601030e0a02010c0f0b0103030507030311120601 81
    0x401003c41076140e842c05640c0c038682070001003010b6901130320b40340700c0b1810314220075005071240c0300c41240944a0051301a0300c84000402603c1d016107560b0a12940b044640002c85010b1400e00840b030081d01c0300d00c01e155040181d40d032002d03850f81c5582886811118551000a0402400c120034072140c04130900850300b180c002c1070700041994075101d65101c80288000000c00d002100703032140d21031540c0040c07401890410319004003041d907a210303aa0350191041400c02402c010400070f810000d90b000e40d2007201c00031403181011440c480c644c4460140d01e4940d41210b16504030101c018003c50030000c201a0140038155281d44150a241d02c6e160b9903a500280064401c00f000400101d03040303001e1196200401880d228000160f40c3d00b10701901034810728000c1c1001c00003400000e9090341c440e0040040010242015201e01c8485400440c0c42400c50442a00e50703c040e00580800681c2070100340307000758025035415454400c13a02d0020191940c16000e03c0c034466040c8120303e071011080380704a801103402d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 654051834 1250 654050584 654050599
    0x5031510080703030c1e0308070503070908012903011a060a210219140d0c0e10050c120408030d09030315030507060e0102010212130c08100f0608030a0e 67
    0xe502040d0300100107508502201d0080900000c1015001910341000c14490f54040e40240d01001101e10760400807100a40040c100c0000b04054030700840083d60004841e1805003092030303e41c0385e15825562003440101c5074507c2031681d1400f40c039021100c103035030407001c030300a204500460030340000043d4082c0c0c060340705080029000040714015201e40e11002055012169101c411100c244000e401426081c3c108102d070b001c5d0100c01c10300c14202d45000e008a107116a040010a0030300b00010f001c000e6540040c0903c001152a02d070b0b6840c221780701810400d030740c1c3e00c5d82c0e101c140c07480a0806041884d800161901800240491a0007005841c05541398800000d060405c0d820110081c00f01d49041d400e4a401815010050041c0451380e00c096806940320151070034400b1004a0807072203210801580e41c0890400b00d0341820b19003101e810a0342c05104090b0f00380c1d440b11a5241007002c2901c011071915079680717808580072420b0151600a0102c40003840c1402814400a40385000424105204090 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 654053084 1250 654051834 654051841
    0x3090a030e06250204050c091e1503091606080408040b070f1a0a06170304031b03080c03030901050115021507031805030c011a1f03020712210501050315 67
    0x11154140d0343c0140890b150020301140c0a401c0d80410240020b0582c0540c4c20040001d1103480010211241044050190b459601e40e01102c52065000a8929540151060405204004040c014501882d0342d80060461b0601c407080990300307e0380a61060050000040070040030461000550b07048070100c02c80c0d96581d0500e443c110076210a02c001c010501031105011a040303503050006070748140740005040011a40321302e5030042a000007100074805600c100720500000f011241c020b5003050300b60302c507000ca0340d40300e503190419a000342d014800d042d800401088120002400f5250040c000744a54054050141c01e00070340310111460561040c0b0170800110310400d102e640a0348080e0300707503104c4128440c0580303003041d02c0303034081c0e03240e00180d600f0409924104201c0700d8003e41115002070072504c42150700a9042c1d02641842407000c1419800e12410000c05e4490b00224401000c90b0b4400e000b0100380d25030540c0c02c40320791003400400b03854103006105079200001c10107107260003040c06c45110755 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 654054334 1250 654053084 654053089
    0x21f150b0d0b0904060c02010f0b0609130207020301050708040605060906060f0309070b04140a0519060804060f050f0603100c0e0d0203030405060a050a140309070b07030c0f0302030c100203090a030e 87
    0x46519112500100d43d081000305000840e4031818140076150b0080c0800406101030030152002b11200300d900078010000c00c412464070508501d00c40b061603030050300b0701c94150002400c5a108490314404a03629004000c100922885215445442150740c003041d82002000714072a80501d0100c1000c0080001c007042e0031841c100a18401008040405980c498903860202003154500a039540100d0700b140300402ca610b0320181e11000c072858030b503414008510b08041190b0481001e03000765000c035559207100c0d00243c0301e405041e1041711502d80c20912420301c401854136000c081c40000d15401d00d4a1302a1504c16403228100040c03500444003455a94410f00003c1c1c154801d0f41c2c4500d600400000d05104010f40120152005c08510b40b54061803050031004080315100c225a1210b0328cc2120b48240101c0519002400c034040c0030381303040b42c05050180c1d14014410071362081500540c1c030200311450822410880864041382c03100c015425400c01c42e0003203940d6200b020008080c40062814100c2c0354 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 654055584 1250 654054334 654054341
    0x130f02011107030302030406020f071404020f0409060312121404020121020d051f030b04150b180a0e1b090a0e1009030e04090213050a0209040c021f150b0d 68
    0x340d00c0714191408a5500d140107542c0b5801403140d2800b50140846580c450140031880781c040301d003d0120030024048100c2000000d40c401d075414141114107100101c1e040725188141809144102d03c0c0a40096151001525034420303927001040342400c001d2000f800741828600d054100b642070910114800c522180052140000800c028803e480850714802c441440d404c00f90088803066039000540d52142120700344280f260101134009421074020400041c030120b120303001015070200004500000c2400a800480b40710b8485030f103111814107204041041e4801c2c0e0b413a0105600042000030003e03900a44540c40342c00910744100c015400241d00041c042c2c0040995000349010703108020859071080d00106007210b030a60000e1fa07030740c44550080c02c1c44c0c4a0345407083c0e00100203410310307034601042c0c801a09008100440d01c41d005c1c40000704d075440e24000d100c0d0411080c5c000e0425440091112071002400881100c819810056082301e45502200340c0d000b91030074030712510703900c48400401c040038 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 654056834 1250 654055584 654055607
    0x70f0206160503072001050406080c090406080102030a061712090d050a0c0608060904080405040209031e03071b06090302090408040f0314160f050d030201061a0909010806130f0201 79
    0x10186210a0301d040040200080048620680c40c40c00450508841000d08550300e03c5a240800c10070801800024040c0780381c280d1240001c1051842c141040e8007060507601190702134400f036900070051100d02c001c10f02800002e466103460400766801c05d40300385c030b58400c004035141b600100002091400340c2c0360901c400c0001c4c1e400c00110b6031240e41c64942142d49410901c00c840005041d0f20210750289400ca0119000c1c0c6c0c1c2012f00503090504250800000354041c2161503810b10074002011150b0060307412080c1f1100300c0001854507400b5504043d000c040b0f403a80e01042c00150002c003844016045150402038a40513100c1a07940c1c0c1d070b14a0001241c1c81a80c11940c10a04d2140000040040400021990342205419988121070b40960b109090300346020b1801e56a08442d01130105086c030640e00160039020740700200c0c1041d035a081c0050007810f500d201c80303203d1300001403060050400071141030050912200814882c1342c0590200712031051038400500c0f200c800d11280095a2242102004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 654058084 1250 654056834 654056857
    0x9021c1e0c24020601090e0c1009051003021309050619270506030d140f03010b09010306060203040e0609060d0b271f0e1e011e060605070f0206 63
    0x200c9865074204441d000007140b0811400500298500380d04a204510891000080f40c004000310b07400c02041030080c00034042c011200344280c100c800356a0f5611403c07900c2414494966810240c18941805200030710b040e009001c0c54010802002140b641220b55422210110b5001589849000005400d101c502143c5000c0f180103000200d03084640c03404042c200441640440e01329410381c030300d0005403901203030101d905801c40402070b0710190081489404a80c11540514076001113450000500c1d00280c03c120080100070410920650f051701c2410080c068500040d81802e1030072501d1202c142d0000c0c8087d0142d0b5501000c6062074544604a0509075400059440b00d0710300820902c64000800500c0100c04d100c00310302d10562000414030800c4c0c001d58204a00701600c0d14860003014080d0307000264024400c0000510b1207402818000700584440c1c8000300b1540d0005001c0b1031400300e20111450414640303c01040455000000c0b00c9031250303c2400c00380842c04074000102140580c06a120 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 654059334 1250 654058084 654058133
    0x513030c11041b050d06050108090a2607030207080f030403050d0c0f29010f15030b060c24010e010e191104090618020304050303061c120309110409021c 67
    0x884043d040400703041700110f80101000a81d503110011181c0110036200051240c014040c0d902c082041113150205072007070403140704242c1b009680b003040f072544072080c25001a000aa028041c2d07003030900000c03403400c40c0d10340258145800c0d81ca03aa5203031202403820405005141c0460020081d0500710350314590341014250b20469018114bc524521800d14040c40040c103190001c01c2201a040900c03080d180340903030020b04001a29000e500401402085541c000c00901280c0c40c80e00c410031050381140740c40e1300411640c5154010884d203050040c1c2200c0030400740c81c0014000a40000c28155200103180e04448480900110050090040040007030503103100190104e09a0358980105044400c506100c0f80d01c0c091078407008080340415100141203800030404982c0d070307107058801402180103039210f4a55103545955041002e075202d4100202003600c3d0543c60050100c00009529448bc040d0303018007010220340c0c0015180c100c3e444855560705440d03803001c81400b48802071902d154803404d0141 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 654060584 1250 654059334 654059381
    0x18100503240d11030c03010c1e170903071203050906191508060115090e04020906030f01020a200c18070504081b040506010513090203060d02061201090513030c1104 72
    0x50f14210351100d000e40c040d00c01c0144001103803d051040c1080ca54640d80c80701c8600c03501c1d28504c1d820070072964603c01005540c0740089507010148070f58070301410034100216030b40d0000c0c0c0340100c408141c0320608000d0501e0074040041c4218049009a8003c801d00092000c00100307900c110000c0107001032010903540320800c0400d4034034001440d641a110b00012200940c050208200d5001d50a80a5143d003413581e00081030040c02c020403855000329009058655046d4031399501d50883e0880a000b2000824143c00010000d80d00030b00c00350300c00752000292020404c1a07022031440ea490105646c00400355000240360180704809441c094940c090030b55241c0c00059800204060740607000b58400c03031500000c07600a602410440d000300c1000c440200c441380c0750001300c10003900001d120a81050368182c007400142d844500a20610510580308203880d414100c00e0000c81c1d030010801a078000300030601001080c4c001c04500800d50788003003c241136007100000308026280130f056039000c203c0012040c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 654061834 1250 654060584 654060593
    0x90c03040308070512070e032e0b010c120201090201030b0a051c02210c0405010b191b060203040305070b0f0112061a0d0c140a03020a030204050603011409010218100503240d 76
    0xc410860004804807210803007003204039042094900b89e4842c00c18803100c000c4840e2482a0030042d01002d0504120004025a48400340c0141c090501140141d40d254502400c660700352141c4d090203d4241e80c1c1c42ca81d0b81c00e020210b00c2202c955075540d0084101840494115030b1107a096020b0300c5040c900b48000c412a407134180c3e95a00c1c101d080d5512450a282c0041840d114000c155040f1400d2240b50135020000002c00703985594078800180c403441e60000c4000d021071800d00055009a01c20380e241951120941050611900c000c1d0101010024210040000030380d80071102e0511034101c500000c02c1e40e0a00d000349600c02e130000245070000c0300107613a58240281ca106100c01c82ea0403416019000300320900f04500c03041180070003580140300000a0000d0b080c10707807002d80e0040000d80000b0790111181500001e00000315043c0c00e0396900080c0784e403280301181d4400c1c00206410746403e1a070384400362001d0020b000082400d180241a800600d1a102440514010464015001308120152800c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 654063084 1250 654061834 654061847
    0xa0801020d1d0c1005071b0e1f030507050f0f0411031801050103031e0216140307060206040b0402041e02190801080a030f0f030b03011103010f05090c0304030807051207 74
    0x60004400301e21800080c2081d0000c1504210050014004513001c250384c0b00035692600611000d55070040080303090f8000500142c800d2010b400c0b90104030800e403070030400c10345445d1605441d4055010300c00608100242d40058800c3c1925000c44000042507109000324a480b4008200640e000d402c200040e90700b0f42e100700085020388100004044080d0040010300d080c1c440a20000340000e0490180743d00340301407114100d50800e07151055401200c1d40004002d24108103811031a440e034000e000e44d040519041182c3d00080034940050292032519480d42c44860310b00070006406603449104604000a004c1c8596840c5907003900c085403941c00f40300c00c2031142c207601c6400308003003801c0c0c100211304110000340c071221aa0b070658031701c0c0c3c44144014003183c150b1426640700c0b0a05440e50000c030219a802e014112175116224030982d00c80d03140007081944031000f60f00c0300c2e000e40c0c0080240450f040004045a5100d605401c1c24241c03032321088401c581d18441c0807000040c04402c80280600c442d88081c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 654064334 1250 654063084 654063101
    0x90f0204050606030f0c13090c09080106150206011a092e0801030f0201121e1a01030204030f1209030c08030315040c0e1504092d0c080708060a0801020d 67
    0x450401c036075582e64003440074620081c4d80d02100c545050001958480c1075600400c40c540e95100c10703220666907101c6200039905468503020105440c110f003800311140910030f4000070500650ba400148400040107500d030507040c0200b403650b422002201c0300640c1d01c0c034111858500060804000b085080a804086032500c07040300501d01c0404031810045880b1351052810317a070300300c80c54041c1042e0342c0e0700540c0e220100c0d080c00445c850700e680c02d16801045002d0041d0b0180316980d000700b140c410806042001000102450381070610500081c0049000c040c03031400c407076511a009a40807159a1401c0d64050403d80c030050100040c2000414035035400300c040c50155800c0c41662074994040d80401c4161001a40ea0800141c4072405100c803625048040c140403009031140300340381580350303d0024280c802c6103014507026202806103ea9031442c11a040243d07404190080100f101d0b0000010180f42000c0c00503001c0001050208055954a44007440100100d000031940c1c0c076642c8007194040c0c010380 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 654065584 1250 654064334 654064339
    0x91f050403050d0c1518060519050f1005060304030e0307090e010c210c2601050108090a020102030714030c100501090c0c051e031201030b160f020705100c06090f02 72
    0x8009600f014000c4e2489000541d01c48800811900c0d02e1140314005d00d204403070355005514a1a40c00c02050a038440c1074041c0300002c1c01100e0f0b8560b040c02c03101c01d03580301401d07140d40c2c44180700800094a040d1086c160640300d00f10380403540c0c0d440340d080489a131164000c5588e0700d401100400540c90020750300c0170304d000e80c1020081c4561601244c0071340320664041200300f031450300d10a00e010842d0850784010410052801c10a00400750f0848004100c1c1c24906208103000822006010719038201c031005a11240400013440c0103501540002e449014281000700268071504190051020038801c0e9681120314404503540310380200000800341c54207215513001a86005005038899101b003032200900c58000d0000e1854040d61807c031440118820500301e0280400d0103891f00c842c140542030340c000c50050366854a54201008072506140c03001c0d000505002d10005e0101480e5004602c20b01124803c440e40c2c00c3e08540c00c50261074445a8100041c201807074111103c0801c1905240d0b041d601e03000703 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 654066834 1250 654065584 654065593
    0x207080f072d0902090301330e0c0a0c060b0d0f0309050102010e030f030411280905070f0807051e0d150621060b040308190e15091f05040305 62
    0x60144500002c580d0700200c1c481d480009200344041031690f001060440c40107000080c01c1040700310b0034600c0400240500f1035400e04030000c51142c03660703d069400900303400400c07200c440c18a40d000451b00d07c03d20a07440140044501040180300031680720100501014100e580140c0e40c504e41400e01d00109001140466540500414603520521641c000d688540b0015850440048a0030040703820040c4103c1e0700d902078040c07192440d03e81011000c1d0030308181d070300600d04840d8034410003c8840b80f0b03006820001d152000300000243d00540c00b4103500f9807420905020348400d00c049829100e001d0101b03032000d10282c0141c000c010110300500140898a404019800004125101012091044000288031b031001078450300c8407041d00112800d07603140000707000e6a68561000e110b4005030310586941d00d01282202031090441c6c0108410b5201d4038110740b1102581000451586d000d900322420223101250304400368441c4c0d2454156404500c10545181401290003001940607000842d494002c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 654068084 1250 654066834 654066869
    0xc0f010507030822030e041b020a02090a020c1609050108060f0a020a0c081611060c06071b0c0b09010e0a030c06120b060c0705032b12090f060b0a0e040f0303020a0207080f07 76
    0x5603580709400d42072307030703406041129442c0d02003090014010b060404001c0d03080217074048101003000f01ea525032031039580b8050b0081c13030a81c00c0300c21904146d112421a4114508114602c800240c03140e50000c554100107841d07040e111070407203262100140081c100040090500303003c01c10b8140355101144208a200c61200020040c04418021084811419072080010418440c0110003003400782c6005100c00c040941c41d9118107c0d243c0700c6070300000c030348400003500c1ca80700c0d6881010011000010b07a1400d03030307040c650341e1900030f16205442541704201c0341884a002400340e80d000102112002440d0313945407542000240c1d102c0c0780074800c1510170320410300c1c441038064414403610808030202610486801d25044142c0b9031088020002104503651600c0a0005c0e90041940740d06500039840020003010503402e211040800c2c0e0040040d0820781020403000030b2540079203800d400e62514015031644072101c0140d20300344481d000303d11a40110140b00940c00c1000a45400300c032a06c2d07900f01c18914 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 654069334 1250 654068084 654068111
    0xa17031b040b0702010f1e1706011d13020f070b07031805100b010917011b140d0b0a030c151d011d01111603050c0f010507030822030e04 60
    0x801c621401520301c000f4441480558041c41445a00316a2070614a03030f0881e48141d9441c3c5d000e0214078407404686180307440c04000000d581c0e140c1c0d1103102801d00307111031101d0f10442d03202070f118042800c0c42070000181001001c03520f60145c542404040c0540c035100c460310710740203d100c40203e403480001ba01d002182044031094101c0d07156515005000b500000c840002054040c1210b6088a13040c003c81400001d964100e2010107449c215a40d0000901085d2544c3c4608410302e43c501c0501c100449004668205142c200031a403040a80d0240002c60b403888501190168005a00c040c0444011610000b0f01075020350101350b4420669490441034440c0818111800c00c80c0000540000c0540b03411482c6040706001613040b400c0141008412034484620343c1d85880080e18282e44009450881042000300400a100341030004035140c803c0003142c18002001d80c01040c4010b020031401d50086001304001300c000f0f10f202c41c0140340100c0d41003100d0030090054280b040c4030310700491501c44109900d2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 654070584 1250 654069334 654069337
    0xf06060105040b0c010209120a0b060f101101150f18150e0a09020a2702041d041703040f1a010308030604110405040c08010807140d03050c0a17031b 65
    0x11601616401d0a140c1041408150b54124002e210650b642c03c109a01d0140d8582e0503101c22505c0443c0103240360b95040c5098034000001500b814015404820742c07942d5580c4046d51000b11021600c0c001e002c02c0d01e403d945a02624090f140b516013040c0307035140810564a00300b260300590300c148484800c4820285007044c02c9480700241c1d02c3d80400360040034814642e403041015000950410081081c05640c6c0001c0c3d805406070380301c10b81c0b0710440038141550203842800503105022906046040c42d10303012604078901c060784000007406441c040098108800810346102d003d540600f00340e140e10300f03481c0183e040b0701e83c08010f4624094a01500020380c01500380141640d03400040141140c40d50720034000a44400c1180c04e0b1241d00905c408105900c0d0b0f4031850360b00d00480d60700d0283c0ca500d02004c043c10074010781c1002d1a90000c101c6d22403516110300f02d00c4103400f589490f11940d100c0714110f800c1d00744054a0ba0041441d0802c005076030f04000d480010714014034540041d45944d1040804a0429 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 654071834 1250 654070584 654070591
    0x6031b1d090a06090302101a1e090117100501060509040f0c090302040b040209180403030b19030b04020d0b0702010501151b17130938040e030d060603020c0f06 70
    0x80d80300c040080b00080071608a100942c0c428011991140700c980410825501c10444129062003911041d010610705280030035040980b020180e045c505030000400e066080c140075000944401e107140141482040020b800e00c444d8000d0f0030003c079610790400601c50341c8100c40062241d418030107038121942041c0b0030100e2603130060300c0d45011a8950b41c280409800708480903075100e6400d128120041d140d081d200400c40f480c2c40004007480c5072501e07025003110400d0f008180968175075070025046104039881d100683c0d401509000c0b0340d54031407001408044000d400103121041c00818041e00b190150002e5059651036842c0e400b0301410880101c4950310090111956200f0894a071004075a00c7c030f0342280741c400342e64402072510603181c10180c14411a60b010b005542e83d11941181d4104040c1e0a07040008030031056000511040080000f0008145101a02c115941c900700c007c02c50081084850740140010288102a5a00d401500a410501c1b00e0200d5003e10f60720340c81400c0d00807170910b10 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 654073084 1250 654071834 654071851
    0x71508091b0a180902041107021311090a060c0b0610021f06030812040c05030309060304150e0105090304030c090216080f070b1503010b01031a100306031b1d 69
    0x9041401c03100419182628501c0d01d4015078010310202d40c0c0000c1148036100402c103030401180d59282c600c14802200c10a41d120310b6402018484100141d641c0da40d24194038042c01c0010503070380341e03035210030703000e440380c0f108181c2d104d01d14038000910b15070400000015240070304d069402c0366540c01c0c1840600004502d901c00181c104400d104104283c00d550140c03e84006600028021380360303619105103601815410740c90f04020b408000c100015180c14601914095004c2c40c01c264495001c03511034040948000c3c0001248000010246001d034081a280401d200c0203114a0400f8120325072a58402c0c041547d800310802c401050810b81802141c404030030b51a4440344a000b02e403140910381d00004a6864002c03010000b070350100f43c03600038590084040e51804c5c43e508107250100360840f00c07002c4006041c14107106048015074a21000c2c1c2d100a041070764450000d0312500000c0b001080c0c9500020079600071060001c82c1c400a00c000007068404147c0920401b440c020b5104a030044102c80801 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 654074334 1250 654073084 654073093
    0x3040f301103070b01030809091e0604090f061104150503100308030405160906051309051f090510050703051b031b0904020307020d090b040b04121103060907150809 72
    0x144954880c010784031089550005503810801e641d90742c00004a0284e10035562804086410081c1c0e107000d902160b0042c4002c3e99414054400f8000792020b404003d2485100c2c41c1da84102400b4007842d50506403055070f2001c0108400c4052280c183c840b238200340610030311005070410940800c1e006104a0f4020b0456903c0441d085145588280680d4030040086445000c0c850918055140c040c1d95070000d44007042d80840c810307050409210811100c809100421400d0840010100d6004180d81d188001d100c04030040e01443c0c145030340c0180c22a118024018401c81c1c496089100c1c81380d2001c2d00440041d03a080c407594807034660007410000003612100400301e080010a2000d480d880f8071500c500492403415050046400010741241c000311411400758004080740c150b070690280803600604600c2e12000d0a04e81001203407000380c025409000307541c00300800148240800105968031400b0010708880d0180750080c286520b5001901c1900990720b00710b00c2c0380c500c0030b00896600b8802d0746c8005c000d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 654075584 1250 654074334 654074423
    0x9051b0913031404140310021801271d0906060907050d150e09010e07151d0d150606020120090d0c080a03140313022403040f 55
    0x240c00101540700031014860801c2c0310020060b54180504001d02046607108845030300c040901d4113149141504061803881000300020360081e00c104403c0c00c1c80286441003c0303802303c0c0d2042c042a0080c2000300503203095440e00040404040340f4400c4035000070411701150740c5030b142141d5034440301a100035602100c001c0000c1e081c0b6100c1c0b0080c1c042198032540c0030070004c0c2001a42085c40100c2d0304411351699402081090f001c4090080102400d62003000307143c0185440003179241d03500384005100c10415140c401c100095061160740f1500c820003440fa00c2d1142d0f481c44c102c2040300032010800e81b03ea0405100181950044c4036090390030500c2a10341a000d4800ca0a8050307a500440b01143e201c1c0304541500c0220b9080000403014143c0c0704014201040241005042c40c1610302c04618040000c00070800314406101c44410055410368608a07a00c600202c506d072410311048036080314070404400c0006201cee04410010800380101d084030030742c031018800081490104403800501c1202c12092 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 654076834 1250 654075584 654075601
    0x5032a071a070c0b0a05070308070801030302190804092f0c0309010e040905010e0102180a05030d201c080106030b0a1e081c020c01111b0a1809051b09 66
    0x80c5003443c0315000b00303404540c545401e1909900011240701c001540440c80404140c0c1000029403c5038017070414446940c0b450390000e5640d0403d54141408413002800681000f1004c0e081d20040c0010000610400511112043c40c2480007c1c0d4038101591940c00d0306100705039001122151516400a545000d11207001501d100c001d080080340c05c651380380302e4600880c500388115903d8800d00d000241c2e890a020403914180c1241c401403510410b5400c0007000959000200c0340420105400c0c20a030002c8003414041d00c00c108418100401d00880b400c1e4030300e02000081101512900e41c40d50f0090b41d8a45030220200c0d04846982c98101110340000e0101d512640d0050280009003401140341da616200c0d02410420603030b0a003069034140303001760030340641c061141c94008442840e01e00c6512001ba01000c1d9140209407105500c0b605490380c1030410b032503003410701c000781035031182d410288512591503c00400b030b102000d0342d040c0940384014151030b50f00210880940001045c02c039144e100d0510 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 654078084 1250 654076834 654076837
    0x10903032c060a030b0406090204060206061207031b1d010806060f03070803040621140403030e121209010507030c09051c020904050313060c210c05032a071a 69
    0x8005001c009205050030741542c80078014840201c10355004244011300d0f200f400151207243c0c124500c100d00520051080542c0040c100750b01004c1128900311a004d09060903040007003542000d00321508403034440ea00ea90003581444220b909103100300385e1034441c0d131025070030860013030003a03003121f070442e0012038154502007040f00c0c000c150013810340d0190750f43d5001591566002d684070b040841e075810070001007560040c410424140c0c821000741301240c2c0081007031001c8007008000070245952400741e44103a8008000b001000303240c40b0301d030680d00c5811500c0130711402000c0f1200541503081000051029100e13010f06410700b20300340c0326000d0746410541003240801e4400b0300c041a503c03070303111180056034603148494001c40c003800140d540c074210482041886e085c2508000144001c0f015400005540210348111603009202e07044031191a43e11b0032141000c10201c068658440410882e0282d520508905400030582c0f1240040c0158001d1107912030546100e020048080c11000d014010740250 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 654079334 1250 654078084 654078137
    0xf1005060a18060e010635010308030a0207020402070807050f0a020f060c010f02030a09051b0919180302160807180c02070308040e0628050411090d061a01090303 71
    0x1001260640e00d400c1308207003101090b0312144c00a980c2800d0013605110715440c690000580700716030080140c00a04003406010103210050030000000001082c1d00f9503a4196654182c4c000e00942da90100f6080c45007064004c0d10068645020301c403240d81d81c0480018030305e001143d02034290320034202182d04010140e005a40c21070303419502d03859002c90f42c00b00c0d44003c40c4281d15041700040c0c0c0c44200d052140c40c0c50301180c08015100000000c80d2000c0e941c0003400c4c2d500484121010340300c00214003285015040381a90700d0125601c00c58100101070300842c29074849400d80100c00420780d45d40b00165a04c01c218810440c41002c564540c100a16240c1c0003100b07031150360300442c0c10312580d0f90785604103a0700031340c80410b980303040000303104e454680046080b911030815000c40c601d04540d6031780c0d401d226540b03100d01445907680340c540d600511100400d031a440705000306200c3c051f0940d0b042a074090304205106480004248070505615801080c080050301c0e0540e8074080d5802001d1010b815101101 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 654080584 1250 654079334 654079379
    0xa03080a0e12070312080118180204020a0809010b100806040903090b0325080105060912100609060e1f03030c15050411031b0d030e0d050304080f1005060a 68
    0x120359689464441e050002d188855004080c0c40e4503500b001d40803a134211000d20204000f2000400c035880c1e402c801d03110a000c07403220000c0d8000c02240300c00b403510b089030402904640040b81c51a016a000142103104103042c034000d1006650306820803058103000c0d1540d00104280c04003280641c20150312219506100b820401c9030740c2d88400940b4040e410490391159100c560f40b00301d0600c51840409041c0c40c11050400004650510001600030302071482610300074200b0340502e101c0c10f1030400c884110321105020420410752112001ca02419460041d4006042000b0108503840c2c110180c1e1001c101c402400c0c4802d681c15a6170481d80500038240c01e0b286085083c8000400000f00c2c070819008038852444461840404001c1c541000241e1151000d1030700039001000141d00c401a28184490345841c182003401d0342c01c030004d9010080c17044007070424070000c90041007540c40050390b58644024403040301e107400746007404c5d50180c0700201c0b440b58120001103001c2260b120860032281410488 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 654081834 1250 654080584 654080597
    0x2030d230108030324101d101218020d0b0702070306050703050906070c0b15060c1002070c2903070302120403020706181a030402011412040b01050904020a03080a 71
    0x2500c02840400c0070703000040d150308000103001c0c1540400000c0d1488405440c022001e94032002d0000b241c04006d51070340c8040c041415801030311449000008600c545006160481c20401e0000c000c0120745c241100e06000f2349000404000700c801521001d440e50360040843c0f03c50050707543c61400250000e072082083d48200c40b030200000b461406420b1094143c0d070f500080c00e03d48000b8091825101401da80b050105403000d01010a15200324158001607000300c0140307410462020a17210311407030b41c0810301d9005510000d00100507540040c0301e12405558110119512140d450072070a1904083ca8000380c507030b800f0768454241003005564040a1400d005060003580c46121002c00c004807801c42c01600114020f00045030030034801440450000500c1c0c28050405044080c50000030603070b10789585000c4005011684a60102c00c4680920014903032182a00b1a180440c201c0c00d076012100442091700110f02d50038442c00d2984680d4005180d800450702e181c4400c3c0099012001d140c007080304 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 654083084 1250 654081834 654081881
    0x901090312030b10030c0c0b0916080d08060111070e0709090f09050d02010b0609151611030d0e1804151805010f020301030f110105211501090602030d 66
    0x11104200007110040d41c0380441c0d800320003010000070211071001c5109151400c01c4682e15140c1c400d00c0000e0103030748a8420351064488d00c050510b0010441e0440314508034002d00030460101c00f2614241824050f181d500c065180c0100650f003905116503201040c0d40319400820207450380300c1515401c100b01d42000e10043e034179050110306950b650030b4961940740d1160000c4042250401100d514001544001c000e200300e1440000c182e0311400411a10a040d0b0711070758503d10744403a0031a501c150301090000705001c05031400184203520303021991700ca4094010349507081c5000718030000e00a140104001c3d500040b18400c05045031019006035075950000315103c0310040244a02c40d8401e040c8882803030b02201c0c2c0e150481c02d49038200d1040302c9241c0107000410000710840c40345130307415a01c5951103000c00b4840c00101c0e001c0c0203003a4005082d0f051118226014001ea240803402846000c00300e0040d50030040c01541c81070050710842c0e005900c10068a00d699842d5032149106010303ca56003812500c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 654084334 1250 654083084 654083093
    0x10e03030408250f0b010b160615090c080a060803030403141b240606070b060622140909060106051b0f031201180c0f0309060216080405010906020f0a0809010903 71
    0x20740f030202154a0b070740c0240341506001080440f139006215426100c0c3c0350001030540c968400061901c01010692a081ca80c01c028100707030305c032001409500208003d0000c807010020071644080e00c030640001d00d82080401c1c4403401004403032045406803140d1400301c15003064400c00b43e01c00000e51100c12120003000108040601110b01d542e8141400002c00301e408441103034421102510081c07040404206000000b034401504603400072003180c1c0e094991043d800e240c1404811310039400710f8120340d40f902060703040c15107a0000e0603010079244285070b0368844210aa8030002070280002207402400191038184034840300007036491300a41600c660880021059185401c607011101443c844140140074803500c00004168008000d1b230305203c0d0340c00c4c20f01d000e0800001c03200d04004154a48001a040c00300b141c044489980d40061348400c080d40d98148110142c209014250000f000c1c01e00c00035400e84001155200c1407146805081916001e0f80ca000c034039805150310a0500030042000130100c0d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 654085584 1250 654084334 654084397
    0x31e070c02030d02010f14090a03030b0a09050a050f0703090506040b060604090510090c050708043507050f040902010e06030615042d0b0a031104080304030510060602010e03030408 79
    0xc210135000400c5000c1038000030b50648980c683c1d42c4a080b10742c0010850366140c001a0080010713050304000501401180204854030315a82044030118140b07814403000b22010360050b44038008924000406490390740c0c0480c284e40c841d22002e001544004003003404100341d42106604000010300961074030b0781e60100507069907005c6815604540018400300819100ba02403850b00fa019403804c81c0c68000c05680c2d02c60680034900039641101000840c441c1004e14440c00b100350781040100c5c407100413040c008811b992f142c85005082c01f81c280c580ca08500c40c00c0034045c120183d46d0584030209034528001c2800240c0c0c0009007901c3e0f0003c0b25000041000d003102c4000c00241100180c07420030111035110340d19030090300080ba00c520010003101002240980d0b0159038800102e40f0b404140344040740002e011074001c1e84c02c11010b80c00000740c0041008000203051118103900c240130300500359240f100f64201c03100d80013a6000c039041040002c002500d10070040810340649034030706003c44401c081c0c10060 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 654086834 1250 654085584 654085603
    0x42018010302040b06072a0302040912090e0c040303030b03031918080d050315120d0c031413120501021608071b150f020c130207020a080102031e070c0203 68
    0x214144100600950406004072850b0b10025107185182ca407443d651340d09400d0b0160a9296400e5510741d44074282d282e1401c25a00454009200307020703009881c24000314101c5202c0079400410a198030009081400000b001d10840c41e407001242814070795107040d0054010709003441e9060108010109044941031201092080c46036144a2015400314100010903c02e4201195a40c000881241c40070340c041c5c110380d405520885e103443c40682c45000703d80842051302040d16140598510b0074401d6900c500c0005082c0d01a60302c00ca42881d0f40065403046204100700c4170800c2e2400a420b00021519a5003400b0b018032640c00185424024003414215040214088480c0c0c50009a92014000c1c910b410000e0b0122407040704100728079129140041c02c005218220034402000c0c500f2000b58000e102c075140d20007000d00703401540080034a076940203610620040703200e400b00980115091701c05100740d038451490111a1b4101030700440c040c181800d00109101e041115281c400c40042c4c1301444031451 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 654088084 1250 654086834 654086869
    0x11030f0f0c0f0105042003160b0a03060f080c0409240209010f02062707080304080606011112030a020d0b0301091b080f10020706020f0c030c15010506030420 69
    0x3154030035001c0e2182080056486445142e0401d014403001c01e00741050300103408a09040c40145610b4880400e040041c0c002000c109400020800a0b40031059030007402c0c0e85040d954100034440d158000011a07076854083c0452591010b801c81d00c0a04041e4040d80000b400341017035103c084e07a448002290b4505d98102020056000305042c0c01650b0488075604c0411003500250000d4500f4050301c694004076040721139500c199244900c0c45207403052101740040c042e07400c103517650340351030300b141540e240d0341a191180010983c81d40c1c2038080d80301041034402c01301240011440d544440c029400139400c00044083c5840d0b0b505207404683e602449056485849607203180014401501261010301c11039100780b210303400c0070111b50840800892180c0c00108103103801a260f00317550418000031f014100740c0d0990f400c030009400d80d50740d03030010203001c800c03122104803a0720041420741048040d100b84200d41e04205c0900101d000560812101045041d01100a481b00031700400000e9459400c6080d200 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 654089334 1250 654088084 654088087
    0x1401022802010513080307080703020c030c06150607080a0809030909130b09120d090f1205042d090f1b030207050f010b01080403231b0d030c0f11030f0f 67
    0x10342940c080c01881d81c01443d0081409101c2484d4944100074800103001000b0856018009141d030790007541512402c0d82c0c0c080442e901c8540c0c04cc022581c56000313889041e840c07440c40e280d90340d186c034141003114110b0398000b6a15090445a050646aa0001415007078031404107001d41c0180751910307840980300e005485840d103a58115801d100034040009001c4600d0740d040305204504000500d000c130b542000c81a103001505500c94100300020240e4040014404a4100750604265900a000c1c10954001e0f034802d03a9801c80d9220b003100010a00c0d29a6010f6981945003040000c0b9580c2c8080c506a00d14030001c00c03400d03040c03a8804500525015410040795000c601c9400b84041080802001d01e900402000805640c0002802e000b0000304003c041065030104814205031003801c1c030480e50743d02e0001c1c980b41e000700300f1203202d40c410008201642c0d10444014891082c802e02070f100158942da121002001c1700d00c10125644c05205080190358401040a40c501030404401042070306041c03800c05 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 654090584 1250 654089334 654089407
    0xc01050f16090e1f08010207060207120c0b01050105030414010f0c030c0201051e04051603060c0f0305040f1403040b0f040e01081612031101050709090507020d020a140102 75
    0x1e14101d038090060360420903844400d204100c4003c4a564100060b4030318200074180c10f290f0009420390a400c40301445d400842c40000300545030300034000c034a10400300842000034281c0212044200d224018000d0354541004001719400762005507040780c00b44030802d03107442c1644045800e40d0b1500280c008074651b6000120381042d454070500c55403014520003400b990a14030031810b0100000907141c80d003000e540740880e0821000b000f80d0b10070030018403104080d4964a081c00c200404240d56018041a10034184c80783e844d20a03c40d0714411039200401440c0c2000fa500d4144035041c142d000b0340c8003031004100100701c1c40c1c20031016051075004520f100c0e540f03504044802c00b0440040c0d0160845070b00c807808142d55800100c0300f030429600003140310030180895040440f030740d0b02107007a01803440d482c00c2c0520051652203101d00b8242e5440c020b0501c030300d8552007000c0707a0b5071841483d220016001240c03c3c0000910114940390740e0b044290015040c41d520003d01e01d800a8484040ba01c4050714403c4e4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 654091834 1250 654090584 654090601
    0x204021b070812070c0b0a05090a0b030106120c08040b072c150405030a1203020906030a0504020a060e03031c0e0f0f07060e01050702100c150617030721050c01050f 72
    0x540b031007101210801030800105594060760045140111841d080f03000c47c80e8441d03244140c05030b03002c11000a0504000640e03607084c4501c103600c01e005d4900011f081d20400710b24801c0b90701030280925090342d100e04590765651502e01c50004060703c0c00081009285100100300c0c0040b003124442c0a00071190342c0540c0140702040b603140d000103016140c64806020400c203541e00450790510b4107070031440111200c50090b0044000380318038900310340d100e1000b00078000e6104640c0c0c0079500c1f0314030030f840200800351204801e9406140100140713901d644104100d80d41413507010b0200021a180403000303c1c05a100e402c3c25424000f2450103503a05900800300b10f08101c0c000c02c0700d02c008001504000303040324680c80000704207100310100070b40a04450000280303203d1103141e800101c0340d04401107069001c1345405460103000c0301c0c81201c4410421400c0c408140ba0040101c3d03484951140101000080c40e003450700103081c00510300c0c2c1c1071100902c251040c070340c2c082c0221449484580709480d020b1030540c0300f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 654093084 1250 654091834 654091843
    0x30b04050c0d05060a06140307020f03181201110a0e0d0c0905100e07080103030c14010603030518220506150c0a031b021e0301020f040b0408190507050d0204021b0708 73
    0x8440c0c817543c000141000070540040c03440548400d000b44580d640e03070380c03450103910b4031510f08041140b0340300028464800340000544107001e0704040716640f500f0060b00c400d49003030b035580603903140015204004111181d8010196119205000740003a401c440460710f80c0720600c0001c1d44550f00740b076298020012081c4c5680042c2e80600303d007000c07400d010309040400414444050200405110111440d40103001408040c4034540414800a00220b62280750041c0f00b80c00548070a690040d8050200c1d03000e01c5e110b0100d81001d00011039200700c0d03560021240c0f0107000c018190390b800900002e0f0042c010442d00c0010011610000e00801090a95240c020603c102e443c03289605110341031210703401a41e68002da0b140e1144c0b038a1000818840c140d000034028820a001003650402c0010001448540b640141088035511815940030314896641d01c04031600c81c002c010308a4008030418410307843d0024013030700464000b90005041409041c0411316003848140031000680c0228000c00c4103050400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 654094334 1250 654093084 654093091
    0xc050108100b030a3603030c02032704140408070b0f011202011d0307030303060f05032d070b03090a0c0501030b13180204110a1b030905060a030b04050c0d05 69
    0x450310700d001071520100c00c60038007020b003018020944074141c0038045c100c1c03885441001e5211403203010b0807844240c603000d480301c40c01e681117010a0030b24100c41f003c9400802640c01e84e0b000d00442183c1d00b0083c0000e13a006042d44100c01da40555940ca00d43c403006805503256110b1840b03811002c0c0e0f110200d0401c842d43c0c0400910a10101c241200140441c101c1c0491090100d41c0c20308102c1803002c2d00d02d0801c9010984801410b400d8810400d00106055140c2c03c504101e0b0a0498034142d542e444006040d101c1c6e80008992011641240c00c0f0210308060b40440034054800c1001c1c2c0d000c103511010301d144203a0081d04c20b480207600c24142c100912030111b005c4801488242070802c4086940c501088048814842c0c00201c941c1d143c410b03441c0b40c0400c01d0010602a40103108000881806611380015004554104001200079800007000102c0650942c002c54042d2110002285050100030043c0d02c0b481c0d8080805458601080060301e840c0502070107012050710344ea80310300341f64100130225000203 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 654095584 1250 654094334 654094351
    0x13180609050c0403300305150402220e010311010f021c0509090a05152101050403030c08130c0b0a41091f1107030f0209010902070b0718030503070c050108 68
    0x144607215a003180f1001d172455415550a001c03496075680707120916442007181c3c54642050000450941c240400b00c0d00540e01000d01b41003064054440c0c409000c9100e00340002000071045150104203580184565010b45603644129492103600015801c4401c4816106a012420100340d0030440d00e4007641c00c80d4040c8006d0000c01051a00400b1203881d4a02c100c2214080c0c04c18840500c640303441c0e07054080152028600030300c440c1c1440c0c50700800808401e05c060300001d03080350124500b500162003010015400840ca441400e05109200d10713980e000c00c0d03512040c403107a240c15898000720890400100180e13480c00340310848015940090b000d20841d000c9691a4003081048010b40c0c070704c0b00c04142c207408401003215032001c01506881180c1d1311110001140300c2c1404c00000c012010031030816152081e00e108450340d076581c2c003120070303401280c50007410001a800012280751042601004103c040100c030040039a498840e1411a840741100340c0b00094031087c24055541c01507507854101d50003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 654096834 1250 654095584 654095633
    0x60e0907030b0a051201020c0102041d060102060403020607030c030b130507030605030102090109092007050c010207170a0b0c1306050c0c0a08060c030a06031709040f0213180609050c0403 82
    0xb01c1c0001e0451201070090500c00c0b26010f0154a01107001d42c140c4060300040b000031136450303403200c10000381651800100520403c80200285e000d500c00b00d8810f00950741a0005c1065441d01d40040d0007070500d8408003000c1650711a00c006039980c91400000c2d40402071800041d46040100c002000d440e0b164000601aa00400032050749990024000007210400c101c0000c0902ca40b616814074440c60011035100050b011440d1000e214021400d02d030880da0980813591a203590b03600200c456001004102d8050300031190300b0021800703610b10b540c3d0200002c4881032500484c403030410722001c0c0342d07005040052004204c0c402e0b000410040e080c40c4140072185107003041d25001d1481d039070b00c00007851a18803820200108482150390780015002d9a40800c05245991208071a1510380d0803c41441d8440d07400d000104000c2c607064401c481d6a1032464200e00c454606002070442803200341002d18034a1a900c90000541d00d4440c0b04080c000c89540c04400e680c1c7c1d2441c10039480c3d0207200101400c14118 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 654098084 1250 654096834 654096851
    0xa08070e0c072a171e21120601020601030816111203070c141f0c050d170708040203190203030706090c050a0803040f120204090510050a060b0903070e09070906060e090703 75
    0x200280d17518032420780b400040101d20009641e941010781c0151940012040d44c9075041c001401800a88481209481c0d051800da69200049a0b12002844050803201007000b80203038030601d142c684401c09000c0e4071800110001a0301180604912100110035500701042d001c08124000391070000030301401614a0b41117801600188400881c00e54480106070010000d608041c001c810201002da000402c2d0f4082a01017503001d002c81146502c2d031440c901c484800142050300410b08140101c0d0090000c210102d1100407003034250440d2941668144818011a00002d020740108034200c0d01c0384080c00296854602844908000d0380c01c0b01c41e664206200510040c002d00c3c13800421134400341810040401d0900102d40140f0040700050043d0107820341e525030b290b0752a000301c1d004400c2c4440400c040365480240320740c5401901507440e0b068000030b4003040000180ea04140c2c00c0403900f8140c41c2103517a20090364084500d140c3c000408614500941e04091a0501c4120340c40f40c00c60a06226414 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 654099334 1250 654098084 654098129
    0x809121b0f240703120c020c19090204120b010b19030504020114180102070602030c060c0a090e240103050f060d030302040911040f050a08070e0c072a 66
    0xd0060038040d0003646441003100c11580d5080301d005004080c000c42035510450094405101d512915050740070800c0d0b00121501442c0a00c5007404024056003d44440480341007042111400500017503d900c3d8820340100c2c0a042c51310050005040c0101c001d030311011035242c08400c0d590b05034000f003115001408544100d8620fa0310a07030010800340740006095980b480160303069400c10480040d502c6000c80e20324510001a0342d80300b0316040c240c00300c8940e15070316003040303a803480340e6425042d80341c0144001c140315440c0140034040c00011400c1080c2c09039181c15402900c880f04a50301c040319009408a40c00c009812280041180002e180c02e0201d80b804208003190840081c202030300516a60302c0030000e152181d410395010704980d0005000b00500d0f00e0007645c3c103400500a02c141c170808144001054036100740110112040207020303109075441c0407803680310310200804807900300c00c0030403885000940c01c950120f8030803c01100084500d080d21048001d040054001184c4140c160000c4001340 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 654100584 1250 654099334 654099373
    0x13090f23040602070206042304060e1009020c1c05030103030311070c05010e03160f061205041e03140403060501061808061303171005030d0203040e0a091e080912 71
    0x76402a4000d80d40703c0c001c0c4042801403160760300003088852800081504551030148040b0402d60441d000d201c400e0b2070361001c00c8402d0054a5056016150340300c100548905600507280000020058464102609e13581030600ea1805400c0000100008014001c164141c802c10360341c614002c0a960070030b140c50303840e84016061801198107204c41d008007103040359401c0051010b42c0f281d80c801c0c2400d19550f481d010070080d00703a0049201289030100070003400034070752041601c16031b044583c9103c0341d560b01d4040868044550825010090b031400c5001c00c501000303004100441c41241d00150542c5001c0e4000d0000c1c50a40301c00b10b46012040703041100f840c00103135060b04204008601c0c16600c0f110310302a5040ca1080d58005040403a10082080f1000448640000c40b50294103455564041c104200c4c0ca03403043c6d020f6450707a01e80c80310104000c03414a038440702403184141c1240d81080014081c1c03064508a41d40c00300d0b001c20b00003500c01840e01b0102082c0d0b9014005500070000c070400c02c1a100e540 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 654101834 1250 654100584 654100591
    0x1611030f120406021608040602010c0534060608060a06080c01020c100c0209010e01140612041b030605091608070506040509130f210e032113090f23 65
    0x516014010070b0600901e036044031407440462030140031826a07454030075a250881d102c0c0002651901304015440c901580480e42c2c00d03090180016082e1005c6020280080008002051740390124101c410011345107100301c5002e0300c070070002000540303450b02c210003d44042d0b411500180d00b00c0c18180f919640c00103000760b51000200e4084900f1200080101e40c515200940650f00c9800600006070081407a0b2410381a6141c04006402456840051120503c02c0f402c01b0308a86000000040209a2f0041880641581040507110540e034903120700094910603a4028800d80114242e44a01099000d200d40185608009002000c2c0340c203002880a01580c401e06000b15100310000c0c24070340303c0510b045051944072389840d1072115241001c09010203241c0d811160000c2c28841c0098190040740c903103241c00002402400d50324132011040c00314154801c1400110f0100740103070007003110000c9024000d42001c840004407040303c1d10005041e107100454004210618840d40300300d42880901d05a032 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 654103084 1250 654101834 654101857
    0x503041d0a181a190204030c050306130c06111f0c0207050415060804020402191d0d12050703020f0706021f06050604051e06030a2c0c1003141611030f 66
    0x2484d0359082c1001d101010700d2500714450520010f404000c0081004540003651420b40c06c40c6c0f02a1354690002c040d0815030700c070242601c0c1c80c1a0040000903c6134555941030404081034079a0844082620440e5448988025134007a440324032000285504110800040400b16800c6c059010790390303002c40719420380b0301031081000100d0001805548a5404171082950380b482d8000303842d0400c8100420054031144070468204003503115080c81e141202d409004c4607080014449284402c92040d90b0603405200d003201035003d080d03024401c846084c416000140b485402420070000031080d0a0303000344640d000301c80601d190100610898807000d0559003510300907207003244c040e52198180d0807005040d20501d90302410010030058030f0315482d00100402403900242010b5061032480440c0002c14116690080340e0040082500500e4201064240211241400248940d0741c1c600724401d05c1c4100c1c0c0f102d503990422201c0c04181503110344079603410440c8101650800d42c04032408002403203500504e60 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 654104334 1250 654103084 654103133
    0x2041802040c0206070f0c0f1407060807050c0d05030711010617010c03051308220612060512150a09020612060102060f040305030109020708091c03020f01090b010506070503041d0a18 80
    0x2040000c3d03c02e07680032081d0027000040c03082200780b002a507030700c4a03401103000150f181408240c000f4054800c1e2400d003c03100c0d001e0b1004961540d01218507800c002d03d101c0130010f0030307501c1d6035100f00c080c440c200c00b42c18481048551061f03040886402e41d404890800200b40c0f9140400945000c10504841d13031f90342c00004a07581d0030860202c804800410320448248140a06d00021f03c00c0c0c0026290f003200c84102418020b041e525810030002640c050480030403034200c2c1090035040c41030400c0380c5601402d61070000450300013170707004a100390304102070020340c0200c66400e1200071740e01040641d500944240c40408207140c50350780101940410320818000580200c1c01808000d0301c8019594205005842252441030012171380d2034103406840300b507026000f42d00c0400405ea20600911484a0700f241040409901e02018403000d075100c2d550544260109010201c5e50190101407104081724240080c20310b8201500f0710002c5419965080400c216001050000507090000035820f5180386400d28 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 654105584 1250 654104334 654104357
    0x15091603020705030d0c0906030908030601140d0e07050a2405030402010c06091109010806010b2a0114040b06060a08061306031e062004030212030702041802040c0206070f 75
    0x168082e0003607074401000c900001c03c04440040503640110050071103661030340703041e03642d6500682c00c40c0c218282c090f08402c41003000502950040c2036403841c6c05032150003035242c580b100c81024116090b28410040580280b8070810282c81d0014602d8054510008103899141502d45c0d03d0318440d8101d09a40c0174400e01000003400e5a0040041d10340303641d0091002d000c1c0d41c0d0946800c0c0d4030886124046403007044440c0010510b00f100040c124181c1da030301442d02d0300d0a0300c010800b8152115020215070680346284c01241c0c100d10038002c030307841c2800d001c1190950f41024030700041a0200145818040c1c002400a0502c4940c4140705940041d000d8810701e10b910540610500030b0b01c415000680346d00741c2c0406015034112402c003a120100d006060810a1507a034030409110b08000302c03808607000c4070038001030000d460600c2c1301c030300014003050449161041e5640811b095880801e03600500140804120b010341c101404ac0c0703881034005101822041ca4215000780a2589600c400f408010510004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 654106834 1250 654105584 654105587
    0x1a04050d030512010e0a0e07061d04092324010302090a14071808060c09060c150c040306060509040b04110f0303070b0a0e0609030a1803120201090308150916 69
    0x40300d04040d500c0c403c1403015a103d0800000010b0140c900400551070207503540915a40820701906550075691070842c9107000b02204000c16030701c000e400707078803541e03a042d00030028004044600802d0300c110748407112040303074250250800c1d007103d4802d20541018040c14010342400117040d41520340c11605170b1425214140b2040041840303a4203c0888108031090010140d0020740303181080242414040c8020349482c020794591600396001d42c2c41e4501480340d580b00c1e14010000c1c1c40d204040b042100d5992645601d00d805010b020360344001034003030019040c0140301c0180900c40240600f5103881009061960703c41020b1480280082d01d80c0c0c0d2018400c4c00a90f48058070340446050007402c0300d0b2520301a050a5000719003c1c0c2e4007a26240c035013090729404241c0031400c40c1c4a0062a000742d41410b401300c0055801071901900441454902100800003490130700c51041511426800010155840d18010b032a040b405071030414203901d0000b0412071541d42d40c489540c440b10f94407140d6103110300c0381d00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 654108084 1250 654106834 654106837
    0x504030804210b040312060f080a0b06010e0a1d070e01020a060e0304080102070b10060c08070b071823092206021e070c050f01050904090c05041b091a04050d0305 71
    0x428698812090005241e41b083c048420f68034280c40c01c0040c55a102c4040e50301e4249441000c9040d080000c240c0040b5501895a43d407100c0f06041c410b07003080e040340008890410540055610840840c0e840d01d14010701880f91703601c000503040440c0114481c50000c0c0d91280c07200310042806440c5c00c00010300b00c0f0284180e07001800350800954640d552450a04000f600071908680065a00d0f0000034401e80b06400c2824040d0f00702100360b1400b1460b456101d40b40000404030000d0060004401c04c1031840c0e00d888100400c3c414142030480c40c1c100810702e03031244c40411303018403444400f424840015440c40081c04810514003100e03203a400a460142d001c1d010b030750000d051f00f050307401c010441b008190340203201107403080c0c4a28084641307c0080120101d100344603140040c0040c8984440c0b410b155020701c00340da008004c02400c090b610f90001d4141d0b030144611041408030340d43c00c0400380348c1221258010f413400c3c59515002c265800702e50031450090b80b2410b03108243c00c1e0112028903010300c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 654109334 1250 654108084 654108149
    0xe0d02090406090b010821160b0a09080a0503091b0303041e0b0703020a0201170106050f0a23180d0803150607080a030515121507020c18010f05010504030804 69
    0x7400d08120340e51100c00503190b4454412600c910380060701503440d226207c0f800c07074540d940700c030050a0003034040e61507115070100c006100e03070046a034031008200070602c120040c0280041d9a0343c0c15079285082002a41020024490550320002c40e440c180043d54000c410740b81954583c0f5140304954004031925400b01109900c54400c03c2c07800104c0c8028150b0100740345010324004e0b00c0741420a00c508440c0243e880c42403003000b0001c0d02c00d0202a03288244c9100800c50342c204c038a80300b200320040300002d2042c01040c0411001e1780d500020035100c0314401701006041d01c542201c035180c0d261a5922802c0c50303440014100750340c80310801d00610a070364030003050780e000c207800072240c54849054100c050700420050340e0b000c03503245015a0140b031501e010802031900480180c0070b0448121a00b000c0980d20101505060950280170681c1c03c00f500d401c080310040035901420100c955243c00301d88911094250442c03410058100010302c00b0078142e40440313046404650610b17001080c00000e0108142249 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 654110584 1250 654109334 654109343
    0x110f01020307061d070605031012020d1217070504081509070312020a06050604090302101e021303140109020607120e06030a0e01050a0b1003110405060c1c0e0d0209040609 75
    0x3440f512100c810050006142442c400c02c0715003090f02d400040c0d84901084036200321007401403005025a40780c240d05040100d01c0900000315060f330711380d41d00c10760040e12289080010703036954105417000803005496401900f076081c10352610741040c5810f602c0d5071004048115614103c1c001c10400201040310500850300b003d0008500461140e00075224005103809554150414000c2126403505200300403007554150020150070710303071301d607036102a188004000d150b42d20042d61f81c1500c02294001885903405106a00c6c44050651422681e01044601301c0170140e8980700003200181c8640341140c100f59000116403404c10a1158200d980310a600710441e082400031051100300c41c0950021030440d245a07009010700d07a41c1c00342002c21500b40880b4075a016001c41d011480e03460080e4810f40c0300103031003129103250644840101d006070b4000c40d5201841c4e882a80803146103071611034418106200e51604842000741d61740065a400302d40302c000391080c2e4102c0042001c00245e5440302c0c0201d03070310 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 654111834 1250 654110584 654110591
    0x6050109050409170f0a0210050f2413060303120501060912081603080604140f190f1103011505092d0a082121190f0204170307110f0102030706 63
    0x1145e40725200e84c01c0b20180c40098801c840d00113038030b00c4050048a1050f144000908000c0c0c0d00c041008100342282c0041885490400e503c1d0f04c0240c46514000c07041e00c0c012032010a80074078601d0000d00300249150300c158402c0c58a00144000c036449116441164006210345100703940504000d002441150780b01007252503221020b508050300600c10030720800003107a0030450341a014402e01140c0e003080722403000c0c074000c81002583e229404150341d102c5a400340d100141c0354800d28207140460722082c14204071414040010001c0101c00170240460090500c0c01604041c400c1022908010407485400185000b2201c20040d003942c9400d100d44480740201524480c940e01c02620741c5400409070803c68401c6150740c40c1d0303c5141d1a000302d1f246039210044003210284880c0c458030900d030010b800c12888c40300c6840e1402c082e82090088088501c545000141e03170f1450b0000035000b40a44000820294200348140d40c041848100741c1501c02606690103130b43c4811103130040303040d8070a284c03008050525 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 654113084 1250 654111834 654111847
    0x711030f04030b1008010c270803041205010b0a0317160609120f11031b070b04060f0e100206040b060a0902070606140103050405062e060c150605010905040917 70
    0xf8458107150003811a000a088982c1c1c55075001e500340c40c100c10088020940112103a81c000864064071251404220740c0c0070380141d02c41d0f00c114213650081d0f100039810407045480c841841401e12441054071812140702004600d15030360301851102c2040b40840d02c00002c10783c0303030a40c840e080c1303400f00c0f007584007204228054031858a01509110310810b5400034030540c64181a0a002c0d07111040c044518400860a00803034200c0c0c3d051040c0817000d01ca440d406034020015004440c44050809881d081d00c0750481c1100d04a0010b094034158003440b88982051a103620200b60080f0720960031540110b0701e400c01d03990380c0d00815440003082d0300207481070f0310000343e070801d00655a026a0035034400f445440320300c1e080e9400460540f00c00f9580a003444d0007110200c2c11001040314040c0741581d2513110760141040c062442840440b465200c0808520030b1455401000807000c400c0361b0140001100b000310301d00740000280004424007502d8081d5998203459028810f80c04440b0603110900e00200e41d4504 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 654114334 1250 654113084 654113093
    0x309030d050c0a02070506090a09022512020f03040b04092408010f0b0a03020307170109021c050c0111060a0209121204050901090b0303030403081504050f19060e0711030f0403 77
    0x42c403c1000c07100500030504042803915140d0112641e1000003400d040c0020f082c004130400950100c0d0620120450031181100c03403000d101000003409000d00285400140c2c01800070342008001e81c10101603410821081c0150034203c002e88050315007010000034060b021984422005540078264600000c00c41d00c00920510305400a80d511003900c075051082017010410310246049602000b50b25400c480c40078801c0c400c0c0d042407801914074400000c50403100c103401062065070354610031000c035002064180c040c040d0401200380d08003000e28065107140083c6041e20b40324100030f40202546500058000070340d50369608990015906201540c00e590031098143c041907126114050141041c003000003103030010ba2195180c0c085000e000781d440e6984503607040f56101b00040490074155440c2c41103581c90385581c841c0700c1c4218140002803100c1d0901070b4448117030020115400d20300b603017050801c2c01b8901e50199010740204190610240021480d0a91411030240c1200c4040c8040c02217070002c02d01 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 654115584 1250 654114334 654114337
    0x20316090e0c060403060b010c060509061b03040b0711070b130e0612060106030f060b03042d05120a0c170a03060f0815090313030803160207030c03080309030d050c 72
    0x200c0c0c85650801403841484106915845540d8010354040401d00c010004103580341c001022240c0c4c1490540260701450f6104021180c080e01d000c00250b00c20801c2100c080c0d20410040109101040030f0750851409644031403900344010201c04c2044583c0120302130406040040602400100c05074949038444010221030394a41d9202e680344003405940483c00e241071010740803606101101c0a09040d80c01c045080d0082c060700d050910655039610b100045649014002e14012841a10345003e5000c2101a800120002407981c1050b18201402d810014000050300c606504584c41207a803501d8450341d041d6042c00c40c80f180505404021100b14803140c2c810001420309504a803400c0007050384405e0701d4a01a81030f0701442e43d1a9102c0e40d03a50200501a04c03c0a9100d108402103d28108460821030b001c042c140e8802c455015003c800c1c80450b100c18050003910800e9407008101c0c1c1491916510f030407148a201c0505145000000b141c4100310510031940050401d001c1800142001e040d0400300c0d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 654116834 1250 654115584 654115589
    0x130b0d03020606100503070909020a020a02131b05040f03111c0f2109091805010e071805040305090105071401050c0306040e01050601120b0d021503010f06020303070c060902010309020316 82
    0x1e13121016484507160084096034014065a61540806401d00406c9070003940201b009405600c13405259400680e1000241c12100100c501c003c560740c405489c1803980120b0001214007449400d2009001c014400c503420741c1242c1c1c11034001000040a00086200110418407580c5458180c11640081c064010801d4402d20310803500004450005249181480c2c0f00300e10410000d04e403a40e0411040300c00750007075603103604080b105000c1c180590f07a4090071541000c4607561f598105200400030340c1660b825941e9860242c2d4401c1c01985000e0fa00280123209415405051050100d00401400180103000c013010312000c0080181e4188a6010081600202c43c1144501d041905a414901040c06800c2c0108410385445d03503001e901c0410f00c005892040c8072541c00203190014072001d17a0303544041d081170703015910f2041d070b4950514809903003c0899410050071b41d44208240000039038403401c0f082030190030150002c0c2c180aa840101e001d0720140340013030340c54800c052441c0c3c986800041440308 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 654118084 1250 654116834 654116839
    0x617010b03120702010903020904050f0a06060f080a0b011203050403050f07180e0a1103100f0501090e0d05090609040f0c0807030e010606050702092703040f060914130b0d03020606 79
    0x190004400003120303561081060017400034000c06802c10050810280741a081445481580d500700141078040e0302d003258041d019103105465600070440b000200300814007406c19007001d02500d03045505d841d00200c01c10700c2070101d512814646401410300c1481600c2c041c0d540001610f0340f651391412029590344550140706d00c0400b1052030f00340f0702640c4e48181e601c2514024040d00e02440d00751900f940d01440b40e0905e54142c02284041ca045484602c03604072044842c010020785941098207200855418148200d03455100280f00c1c0803a0b13411000780c074030b081d5080740c03d90382d5009000c01090103888807502c00d00d201d9040400c06820b00b03401c4075640f40b00d00030503941088803916080c038060983d40c4621032040807400800111015082c0790442551041032407040104c100c00521000040c02d03403c0003403a80c9508003040900180d007080790204010105407800c400400c5c2803030202c0090500d5840014031030b00d100204008030101c140c10800b0740d0720000b800b80c500b080460a000e521550200c80326403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 654119334 1250 654118084 654118093
    0x203031b0f160614040503060a09140d02010501030c0902030403020615010905120d030f020412030809161508070504060813032f0c040c0e100207051003020705060f07050a050d0617010b03 82
    0x8254481d0000707580481b0300007402043c0c191a0480a00010180e1801c29140f1040412030380111800405c0b1100040c6155800010700c0e601d141480c03202500d83e030300080c185034010002e00022a0340019143c0d0030075512200d141d144041d03440107a0700780341d40d03501143c0c001c14840d4030b46290410104500b400031a841c0c80600c0101003a001d55422449280188500e0320b0a02c01e82d400440d10880c04154043c40d0380c0c04564030090208001918180190310002c02c20454520081c4070580c003040c41034202146050030b40c10981000f00c0900b2000700103080c00b12500b0416810424140300d2001c3c20700710340d620540b481080001080b103c0410740d08001018041c802e4500703142040c1081c1c421560141d0b2940c0e156101d13113202508100e2616a85146403003180f01350340c000328043e940c0c000480080080354600686c0d1300000e140c140e0a158000348030504001170041004180ca0f0064111608442145012175940c0141c4007484020505900b02603800701592290301c2c0e20b004154403001d40c1c0c11085080302d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 654120584 1250 654119334 654119357
    0x1a04090f05090c0a030c060e0105070218010305280210170a020c0d0e0303030708131406040b090607020a06110409110a030605100e10050909040b011a04030203031b0f1606 75
    0x131100c0102444010010b180c140001c1124503c03544400300c0c0010145000c91402d10309800040131f001c00c4003920042400c50740010020031070304110002d1180000004c55403c00c6c0300b030b810134503e0961a840070b07004016000c2d00382da50b140f013428802d80c260044c0150260504081031084003e400040380c0140310710a40d0b840039440c0e8011070b004818500024019440c540c0c400608441500c000b510381101400326805160001e65026000e031281a00e0500408883c901818580c1c40d41c0009041c07401d454100c0c40a000c82c941d400f20b0081d4042da001117000c142000003010031300031481142e100369280f07881c040150342c14101c42030040008142658060210f1a11402000b10700160340801001080310310000110b242022010b0050095907401c0040c24207041d003021a51101d0112400c603181d040000c0140b050f40f620141c0e113000e1480c11200c1301d0030103040d540442d50764440c0c905803211000c851020210400000c11017046503071010b0060300c071045c1c035403407400345180c909010340c8004c60185c00c0311 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 654121834 1250 654120584 654120589
    0xc080901020f1e0c0307050102070c05061207030504111c05150c19020c13020d060906081e070f30020a0b090a031e0323041a04090f05090c 61
    0x9848951281c4030501e4030f0100d0355489010740403521404903490a506000d135001046050019140f101e01520000da980d40084c030f0f020f0406061500082d03c244020312090070300c1c0b1303078070030b10b441d8442c0b018140040e25450740d04048182201040d1556405440c40c107180c0c03400d40103620a080014860001c445c1c01c50f503400080880c0d00c1080340c56607020710044c0010810b001144440720145c03036030f50064501c8114614045500061601201ba02050b0000b400105504d018441c54004180300341c0e041003103900307010000d61940043c030704802c1344c0c12641903841d500700404c4c041c100060400c0e040b0042042d540c0c0203100170360b10503140752503141021000203812507140202900304840e8003c0c81c0144142c10004492010f8101225007070308080c0d01070340400024005038035829240480c241a44a080e401d00d0010000301010f04140e4550888407824101030a040007034030709039170819004201c0c44500c1c61000b101c41c05643d1010000d2418000300040314007a40c0d201c0340c010250341c025540c010030407005 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 654123084 1250 654121834 654121837
    0x10b03190312020c031204140d090902073f020109020105090103050a02120c181912051504030e0a0e060904060b190311040b1206040609060b03010f0c08090102 70
    0x180c42886000e84500800001c0c8110590019210305150060400c101e103c5641e02d182c0002c1300b1121045d0801b403d00c024814000c50507508000d66000402e1881c5a0303c000800c00b0b1114030948030541c0e00131400c0707020894282c540100b04e0340a0380b100014114030142c10402144001a9100d0704541847d403822250f1042c0070b250605034041e16601d01d8100380070011001801c006120100060b400e001d101e0920a084c1503483c010301008040c147c503128213130403803507e64969003481c505c281b103240003564149020101c940110313002e400c070300310700000c09050190402a0440300b0301c6180e02520300304410940c00c0860b540010000340d4103528065220300301d0703030560390b0156011030b07100741e00c800014001359180d0400004280054841440c4071310071b225005100710590411203003c00d00a030790448600709071003581030b600c2d8211a106902040d48a4035a1200700c00781001c0d00d01501d8400200601c501c60300004179541e00074000b00800c0e000c01031424020f022940034103002a03000350102d08030100500 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 654124334 1250 654123084 654123103
    0x9010f1b0806061309150e010f24170f150109141e0307080f0115050a060f021221010603020306131802120304060909090b0a0f06050a1403010b03 64
    0x855407101c42c1c44035010016140c01c089190b1004805811020908012500030f41407461404145d40e4032050402c0701500c05c2010580040c20200d918040412441000760940c00420f07040440080d03000140c030104640181200b44c00705805640c2000303000345016607c80392442012a800c040390200e03104001107968001c0c52240d900075403094182003410345805140b184540004c51085c3d10785841440200c0e043c018168030801c015003242c81018150b5200303009400e8800314483c58164030b58241000070307440f003982d801058100b00400000d28040c81c0204607180814841d02c0c00075440c0c1c00500c080c210030074a45526443d52592140001a01c24004d0094031b0140400078410300c1084120612400104000140515941c020302d602c3e41c00740c2c50b81c1c0d0b0b10558607841c0602850380c0d2030416030041c0c1000a2680301c0c0b0041407600c141800440c01040d041c5401c4915070708042500c5003116820301c083d01c0641c00846d8001d01d1248000f8014810040805484805400a10001c00080300b010f4541d5040c6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 654125584 1250 654124334 654124337
    0x303090b0f0307210f0b04050105030604230106050604090b010e090f16020a06050907030c0e010612021c060f090c08090a030503040f0c09050411100e04050603011409010f1b 76
    0x20b0011550241c020740b582110700e28400e4071013200598a444140c1500c40785510054007954480070702110741410300905026280a400410180c140382c1d955088565064001d1221802050840c605194081d00400c004100042c210303902c480d26030031030700000e0041c004110301181030360840c2441800c000c00034a200764041409190540e5400c40c0598032540703146000800c601a03000000c0000c0e54030302c60301b4000c00e40304005165207410341c0340128405015400c04120f8803003043c0104400307680115031080300140742e0b00c0582c40340c505520700c07124011644000908035003000000300d002c8040c0c1204100702c03641c04e5010701030089051401d48003040243d94100f1b0b5074200c104c403180428010401150054400c40d583c096401550719081820301c4603800181d2459100c1d018002030041c4281e084241400480b0b420300c04040001c00504440e189404890140b074442c1c0020740d03070383e5003940851660081283d804046141141e10755000f00102001e00000b24034103500d6129141d4a001000f4447e240c6 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 654126834 1250 654125584 654125587
    0x8010b10050d11040b0301030203010b0d08091c02031c030f02090109170a140d1d0306060d08040b0d0b090901090807060902040b10020c0f03161a040b0a090303090b0f 73
    0x1000d80440d00d5030701103003001e10031075101c079508103959001d01d00501c01400101200390302c03035045104040c25503454009079440317140d01d0220500070403611001c03074554030001c030780c041c4001c1c40c81c882c1d80000c070308079800295041c00f50182d00c043c5001120000e0380d0242036030b54208801301030030800c0c0c0304900a86001c98000303000b8441c2030040e5181c1007a42640118004100c03084000190303500e1861500414410340c043d00050018824076801240400c0c0010208965a000a0355070b404247c0c0e40c1c0006240612805410340ca08003400b480a04982c0a80580c20110380d584541c018100042c05d40010f8040c041d441000c0010102030040c41a04016540a82d9a518101294075002d000e02000181640e0140c0d96004d503148503903404e0a02a08940c00741c01601c55188204c041101d50040c04400c58029000450407040c44540340741e410b8141c403480c1844092221940d105503440340916000815036020005401060641007201c01c41164800e0395268001c94482e20802941e020301c18032140f41d40c00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 654128084 1250 654126834 654126859
    0x3150415090e03040e04080c1603020904060f0615031d060403020a030503100503070608090606043e040801050108060a060f0b0d14010603150806040206070803130609030206070908010b 81
    0x190002580500b10340122824940c6600700301d40c0d540b10036582101c40d680000f600ca020f68400384403030090004030300c2c1c0c80358510380786401140074000c0060000317120381c4d81d907400c1c01c10341c20701c917402600a400e19109100c0e0300c1c44e11281c041d000b04003100810030007203000b40303528440050001d0150300c642d40c10750141614001968054075540c0020b02885003213040140c01040c07649003000944001d2501e030390784030600e04000030303080d040c00c1c0003801c80303401142010000c80101400c499550300130781078142405803803800100800b5146441000480301c40000180c00142c0180c1500064181d074503001c00e495003074403101c4200c4101c3e0994030450680386002c404c100480c41150028001c0405000c4011a1a80c6440c005c8100c0305801d81002001c2035407650328240e8800c158040e00080c1042c2001070445003441c2c0c0005030240205240180f2000001002500c0702150703098408185510a00c24401c903900d500d00a0b45810741103c401000454551000541507014020400c5034800500410b40216 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 654129334 1250 654128084 654128099
    0x191503020703090b0a031d0607020703031202070204020304060905010b01050313060507170f01060f0203070209040605070507080301080f19031b21180603020f0f07111002010203150415 81
    0x100722400540c10b0000d02c400029001402c0b8000705171085580e41d00294656074030805800a0a145480c008554091020001c955030001075420540b030301410b00c11628440c140c1c00802901c62780c040250018000b00603c0100322058001400191045e4004e12800c22114011280313404200c4814081c040c000c600100815511b030300c947c0e0000b61614000300308100c3e0780303025584c845043c2d82e0032208809500041003450750041c2d05024503031a91014610f0501c550f00018941c07140034001621142c0c4d10004140c21500403c00c4030b500d10360090186d5241d60390350203a9500c42d40c900c3d0165005010720300a507102042104205080d540c0e05840b00f1001246c0e110549409680141040329030303440111025400d80e08101441d0031040c019500c81c50403c14098003034500f81e10b140e02c440140360051002d0003075004240140c0c2c40b035100726505651605040e040095600d410420025001f0941481c0700d401c01e030741034000b54804e101c00340c0c0e5210707400c1026040c40103c602501440c0700700b5401403424420702 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 654130584 1250 654129334 654129337
    0x30c0f0d0c031d0a05100804021f0512250c1506030818150d060f0f0b04051302130902072003030d0f0615080714040506030c090301150f0519150302 65
    0x4806441084400d03128401b152480203c0010b04000c180a401004114a4000308075582013814104e06410482c4010b0040d01078000d0055204203c420140000e413071103001d10382654290700048000c0300204020001424a00440101781d4104101c00054500034074103019080860780c0c85052640303010160020580c0866104001c1035000c00c10b940c010480381c0c200c401804c070101c80828002180352402c1254460fa81d0164010a0b40b00051107041000060301d0080d282142c20568010300c0e81a06c44884200910504816140d064480348010601c1a0140d014140f064480c41006140341a0400d071111000720801109070b00d03038000c21403001030f8946038101094403001101c0224410307440f114074001d00841040090700040c0c80b98100084c03036500446480200c0d51654409282905250105040d4030008143c02c04801c1d000460003010745095222000200206013111030854442070106201440e03481040e210783c2c02040d413010f40e1443c001e0320000721403804045003200340c4094401e9000c1e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 654131834 1250 654130584 654130637
    0x30906090b090f030a0c08101406030703021c0c0303030f050603030702130b180112050618071401050f030f0108010c170a0906020c0607050d06120b13060e030c0f0d0c03 74
    0x9030090920240006e422081380d800900300003405050240c004500342c07011517074905001e200300002d41051000a8501080c0c03902501c0c0c058590000020310740084002800c0941402004420880400407c0c1503041e030003076080304410503081c80319032030f584201a07490240d035902a5000401030a0364100032400e0740003024400019003000701810180c404402d040348240d002019100c51343c6c820404004080c841581e02542d0035000c1800010084445075513410280a01c20508810681000c4e540c2c1c010fa003902c401c903501c003100603a2441e120504144211003031140c1103042d800c2544c0d000342c9600803d08440541501c1c00461030b5503441c803120a001c3c1040700701c25142c5603070800c20440c1d40031062044a21955560311526502d111300808402200e0403540b24a5903914440c60210016400b41c541d503030801e0b190010030914007081d0070041c00400006c08141c4051200081c1c1d01103850380030a0300381882c45248243c80f0b020040c40740c16200b41031803480050018a0499038a0f040000e00d8240804 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 654133084 1250 654131834 654131839
    0x307062d09080d02010b0306060a0b042903040f1721040c0e010e04170a051219051614090d0807060f0c030504061a010e062503080103030906090b090f 66
    0x101c0700e5881041a003060004081e00d00141d46910005083e41001c216864016809543c1044040d2405d9880d2405007c2d81c003882c0014544500800c202c0e04402d84400c98244410240031b5490038070b0300c0c000c20900700f0b00104444000da10303103444000c0500305066841d001e54018003030481c40c0c043c0c0d000d00651100103100701c1e07120f041e034100400d580000300d501502a207080070043c210350038a4100000404010a108602c0c40810810105643e6000381500c54880c1e440500120584540ca6060080244a20f43c0110700d481c1c001001414a90044c0240c40300c416034944140c03200301c1cac00c42c07042c0500c2180c5100c0d8005225840e5100000c00d942e00420740140540070000d044140364416105541c20107109900003500d9906101c284001ca101301242140706150290781199100000b0309a420a218490710a10010603c00660802d114602c0c010701c0d240980c0410240399843d011740380800030f0206800080401d80e01154440c081c0d0340700410348071003803103c80c104032804c41086900045000a580c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 654134334 1250 654133084 654133097
    0x280b0a020f0a123b010206010b0f07080714010c0302180102061e041416030c06020a0302060a020f040b030f040303154e030806041e09050106050d0807020307062d 71
    0x1890900e8480c11984c9400900c50150000c2c503030300c00028908032041e001005e0655007085400303000d0700e60004690b9400d5118400b240c482d88181401d45a507103102002c00351550038076040310f00302c3d0b505900030075262641500800442a0034801207903140800c07071b006600d08022a0720051009104185154400e00c03810111542c0c899101002e820003a04280c0407030507121030076044c4104100d022800340030301140e200804505c41c040d01c0007035a03650050b11412201e607002a204020b00c51042c1158080d103007050352150f890030410007403401c0d00d000f16000d0300000c3c502040d0b61320f03e52007609924210ba00307401c0e00075a0b80c105915040c0218502491408685850150303403980e540c3e00c40500100c1000300304600c06e01c0340803810054403540300203000e40d11442c940702003007126404019103007200a2003603800141c0c0c5102c038a8828010821504829800780046a0b000c0400c03c0c144000e004c014030035410742e01030301d5580070180d0b020349070031800340d11481c1d2032441c01101c0b801c2c2400750f20a00380300d4a00396 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 654135584 1250 654134334 654134387
    0x4020706111207080a051603050603071203020304140d020d110a0f0b0c0d03020a09141206010b04080706020a08030601050904110c0a0519020609280b0a020f0a12 71
    0x7444564000500c855201e01160204040241c2180380541e000407054002c5c801c600e00401c6e00d00051040c00200801e240e6194045a15610100100c401808910513034007060b1100d828080e540b130300f0611a08102500d60041413209080800a150032158064010300701d4010942d9444201d1408a000c103400c01d8103543c001821016841c50b0100501c2c50070240340c2d4034030702603001031f0420107145154018540100070340d01d1500d41c403101c040d00700d414444a110300081d0b1030700050994052500e100c203072441444008107070402c81c4001072080300c6010003103800041d034a913001d98039298034200c05448000b00b40000744065000e034005047c010310041000036070820303482d00e15150380c211026442d00d40c0c5c03120301c030328003045010040b5010344000c030081541103036410345c0042c95a200313500016000700d8407000b1000c480c034107100d403541c0c4c151004500405190b880e0000011290001280070005106180300b2448181c008104211101d030002c41e0705440088544041d00d980d121082825034602d8030003482c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 654136690 1106 654135584 654135611
    0x2010c020f0d050c0109140708150702031209011506030b04060618052b0f020f09070903080306120a05070806100e1506190e030709091104020706 64
    0x11660710041440401c0c01b400d074480d4001c00711445406017080d280000300b0450103a0706000e04540700720020f264800e07035244007a14a1009a0010880224400820900c40381e01c5940c041c0081080c00c0c0308041d814501120380c1c09040001d07a00c1075258803a02d02030182c0802010f841c03400e540c02c0c4901049100f0f0044080c0f03e00d920400d400c541c6078402c13003e0344480da200c990342e0600c0184041603500b041c0444a41d40d800482c818030032000b05110038504640114003d0406030340c0e03482d8050440d65052070640c0082d180c554060000742c1d407608010300800c50040502c1c410000703024000d140c0822036241410203880d2031842c2e03082500600a24070078042280c0d00c105520b03415844000c0701804154540310b440d00e00e010b4640303a034110108507500240c031214125810b400303d8582a0350340170a1021100030000003010b0302c4051070714840307a1a06401411000d0701592000820a0b405240d = true := by decide +kernel

theorem cover : BRFrame.Cov 653956834 654136690 := by
  have h0 := BRFrame.cov_init 653956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 653956834 ≤ n) (h2 : n < 654136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
