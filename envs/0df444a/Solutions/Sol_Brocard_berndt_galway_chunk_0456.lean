-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0456
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:54:37.08422+00:00
-- url     : https://prove2.me/submissions/146ddbd6-59db-4458-b612-639a09b6417b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 81834533 ≤ n < 82014389 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 81835783 1250 81834533 81834551
    0x10501090219020a03050304060908040308030a050f010501020706080402150f07052503150c120e0609060c090a03060c03090807080a08010f05061606090b0124171501030b0301 77
    0xd0000d40c402c6005454040c2d0000191041034004a0003008403034240e00c07403174516034039a41c41100412928404503441070040c0030210100d0380d140e0145100d00842540041c9030f04000c0d10098600b58144d000d49c0c115442080c0520025a0091781d42ea01700e5815140c0d00841c0780100e000d00c1d4507002d88256110301100200e240c07030902c10001030039000d101000080b030300d100c1585001d1191294841c0800f404240300028203840006265001e030b0641d0002d4030300f0704182941c4501a00c00c0d5403050308200790b40c1c0d102005022550703070103124041e081110001c146140c034410703401103681301083d84006404555901c80a1202c0c500903040a000302c2d501c0300c3c00c183c4d20185031a00d60550340003407425000269000001150109050703480305c040d100010310044c00c207095280c2c8881d501a010104032031080e260344843d00001c4019100f03e02a02d0072005081e01d601c0300d41306004814900015040801c4a5200703c080d0f00d10714100350781d4003e01e44201142000c0200340040e0060800c9040e110703095840c09000c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 81837033 1250 81835783 81835799
    0x9040503090d350417011506180815160c080703090e060a0b04050d0602090a090e061501200c12010c1211030105190b070b0a0507020102030405120912010501 69
    0x140c00c0c00070b000541000d21141545102601c001d01031403041084904100134442c800b5442105a030840c0c100002082d0607c01450001c041c0741181d0020020807551044041c1c650441d2054001909100c0024204458140b40456107884060401014401043d20004081c6d102c0c54454101c59042000e5541e1450545402090b4090300e110701c04c1c4c3e184080021400310319050390410202c46c1d021240c0c0c0d00303150a0004108442c009841c007140d0343c0d41d0030004107040d52580c11922000f0140850b00290186144440b141440310003860451803d100800900f02681c0154440440d034841107100018448407a019901d0001c0c3c2e1038045900a001c01200e018022054000744000c180d00d550702d8140d03a072004000815540000310344544000d00380018411400c11070100e0a50581e00c1c0d00da01d40b8940d90345603a21136640028000d07141036840b04100b0841f88001d0242540212462008514500e0710351115030f15040368104ad02c80c41c1c140068980300998031b0303003000f103500404071008210070350b560545 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 81838283 1250 81837033 81837053
    0x4081308060411010f030506030703120509040e0c04060807030314070314120603070b0408120f040302150405011407020306180c0301020406021b010c050319140a0c140f0c09040503090d 81
    0xc5680014032004440401c5d6200b4020b2901494000e8010140b003030031952281445e00484685c04100300041c01200010b5590340541001d14030342d080600340880750f91040c00300341c80d115085840d81c4c0d8000c1d181000040e61144183d41030030305030304a0586410040c44d0440e50504201c14503012842c0101341d0441c0c4850024038540035903411000c85100741c1c2d4034040c1040c1e60060b172044245541000140b2048004000003d055800402c0c041a103803940301c5d40010072501c00074440c0410751101040c00d0043c0d507080b025245601d1043c81d0700c2c03410050f89a0019030f03203020040c1083c449802c0728444454401003040b862440d094002c00039503c460f00c0b0b01000b940c4240c5c104080e00346856940c8101d40c0d0354041c1e1000040103030400007451410600c540c145d041e98140043c610200400c42002d4030708044240b01400070745109a9038032034417103414209680045d185150703140c003980112214941c41d07076002810300001e4030156148086903a89003030050450003816481c07a00040f45800b510200210061 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 81839533 1250 81838283 81838313
    0x9030203270301050a0c050f070c03050f0f0606010804020d110f0a12051011030402091806070807020c0f101b0605070e18010815091f02090307120209040813080604 72
    0x3c0200fa45d920f404081030f03422034001500429010081c51900860b644010043d0318003030041c0310256039803959080d01d80b80003c81c2d64880c0c3d0f08986201655200c2c1445010f0700724009107040c013140d0400740c00048520340c581078020301d60250059028043c0c1c03921501400300880003404040402c1c5d84140300e1030280d0f00410304403000c0c051740100c000ba010b0300b8801e149052400d024030900b566110743c2404403584000c5c155003001c0440482d41c00272601c0800c4840d00c12440b56882f1707000d504106002910741b9621605135449032132a521500c84503281c9114407041d56200f46040d81c00c12103841106481200d2001c03029101034106800c2291313040d0008141400154280c450f035220320301d90000024401020b024124a070f41000b01000c144905e9040c032150010800001e460410103800c21014003c04176a0f51200c4140d0045001c40f40c07441c080c4803500085c800e8059407000c40089a00180203140024401000d00300003044014804418041c090040d2611000b2140c80e42054201004c81c100130301 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 81840783 1250 81839533 81839539
    0x20903010c05040b040509040203030408030703020703030906020c09071404050d11010f0c11130b0405040606030201090801060605090907020f030a0c02090c18010c1103010c05040906080613060903020327 89
    0x186044400c0b40b2541c2140c003101c0c41c103070f0541d08090038481000605c00b00540103907410301c018040400c0d041c0f0309100905540d407203a00180091455450083d041e40c4143e17000c0015500010003035203498940640003540030035a49850903030380e08100c0b10ba00f6640034541099812050100c1040100300c1068220b517003140098a40310f03074481700e05d042200c050b00e80340700090644000301522101030030044507500341071031099008610b40340107401103000c44204840688e15951148810000e65030000c200c040034000c0c5000a011041c103100c001341c000d11a4640c802e018a8552002503502d43c0b003441250641c20608043e070350744100688009000100400e01030380314400c21408189881c1c183c0f02205c1e50320344041131603254100c103400196120700000c0404e0718209028080103542e6602841287c0b000141078881d280c80d6400d102506044800c00c3e08804921303401342e81484205134051b1103150307100d42c1c00b4801040c0d90700070740740490030743c058146c0020462216040c1c92422500c00b0f070394042088000d03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 81842033 1250 81840783 81840791
    0x60b0c1e0105010312081b0706140c03060102071208071406090c030307020f060a090902040f08010f020c060402060a170f0106030e0105040c090f020702060309010510080a033c020102090301 83
    0x240100c0e800c0310420700c0024000c0b440b00411104081c00341c81c078554004078649500c840c01c030a28041410680c0f110404549150759160f07444180c0e030b0021001908443c20341c0c525421031403d1070011f03680f0603480c05210103c425101994080080810032109801c0e1720001d034030b04101c0740c01c60f06690703040305691411450040c914402050304000041d0f414003a00201000c2403800e420042c0502c40e1702000880c020440d403403401044000d43d900080008101448202c1d1025240c180030600312400f410701000c145004002c0c5034002c40d000100d1740c0d00070341c0450303049564602581090760281140c1c4c081071a61030604003003054042204203424121451381e10140280b41004c04440c1c00c8560031100101450707030305e2006011440480e440390500b94100c1c4001881c1005580000d810740d0000c5a100034540c1d12034040116045139121008002c0540303c0050040d0507040e900a046001c900720f1004070201140c3c84500d107d41041c80d180322038210234458844000d4070803c028080e500040841d0b00075070074 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 81843283 1250 81842033 81842083
    0xc0105040c080307020a0e070c02030d090501020111070506060f011106010806180f07090e0102090d0c0302040b1905010302090a0e0403020c19080307110411120f0a0504110d0204060b0c 81
    0x120444484c0e9900030500520759041c400900c661000c05081c0c00208014002a080140c030300300b040b1310003e8906d460380803000d03180c10002829034010a143c044c00b0502840504c00080000584e03542262080343c030b0b20400040b10300100c84441520040100702d210b50000040d10100100b003a42c0030380704c22404140c520010305e41043e0340d40031704140c683d01640000310401c00d1800d2035001602e014400400580b0f84030710180020946481d1010a559040c940d003020000c5142500c00c0f548001c005a40040584c1c81d65262040c584019101c0c250625400040710340b841e9480740385c4000641000c1000310403d0a1908000b0b44d00c021480c68240200400c01c80040c2400e11144000221020180118548405a0b8801c0b042c0911080000d03001510380c81e10040c841000c401a08241783c03820044401c0d490f100303611075005980035005000052420301404081144140d0321031031564191040fa07800529440401d0003081c0c076a02140328040041111607100310003041000701c4000b281030018070060 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 81844533 1250 81843283 81843299
    0x2406060909020901051206060c01020c0705100c08030727060201090b06040b2b080406080a060506120402010309050a0503180901151b110418021c031409040e030c0105040c 75
    0xc02c045801d80400c0d010300c0344c02088481c080e06c840e031014000c1d10712810408040006070070b81e0811000020140c00c000028002820101e090b207400d40c04918240402c1180358491440310b11000e0186010003c912180d004c4616081643c1400d4500400c80340b50080da548030024000d10307460404880035040c000c04200286018041d00c1408071005002d0041499442e1139000000c2421804000c01001c1c0c901c0100400c04190207040101290303164a40d461038001c0e0f0700c80c1115410380205105050030b04c110030b030b216002e0025a52203076080c00c0000320051107041952400041c0700d8020030b907201c0020700300741c040000d9050b03100181c010fa0703480c0010b980b10040703090011081c03103468001800005140c01d01700b0800c03c01e10500c80c012400040440f00f04804203094071030b81c0641c504007800a03140c0c0c00850802034011450b034405c61050b000baa4004d550028070580c1d00032080e900c540320106207a4001e6455900c040031007003003041143c4d52140b1803d01d85019000c211001c2e21141000000014515 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 81845783 1250 81844533 81844537
    0x108040503030c160c030303200711010e01170703020a0314090604020f0d06050411150306090109020a020106090510080d05040b09040c030b03150f1b040b07240606090902 75
    0x16400030245045988090400e000b540044c4800e0100200c1c05003004045448441a08044d50183d03901080c0c081123070141c9408000c050100c40b2440c0d0f41080039101103100c002c01d6038040842443d151000402d0040102c4904199960910786400300001b4464019010f50050148504588003800741d54180003902c151924200c42805564000d20001070052600a203927404540000f003d22400070603e0b120700301101c004540469420042c1039180e5030078607003a10348040101e0002e040d03e1a51a001010414021041c4640300f20590017260184845000303411410141c07034086000c004514107050420841051440b8080107802040c0c01d02c280240701360b0840b001e8840d5400b0f40c40c07420084e003003840b0051440f07150800c20581d4421403038007103590a00c54440002c4081091078a0350a014a611203403210241c0006003000d0340b0940c0c041c40c4da250300140d5048030741800401e9100c0c005814a2103004001c107140420311483c680301caa004104982c440c00c25555140c4d038100e080d9880340e040764128 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 81847033 1250 81845783 81845791
    0x40302030c040506041104091a0603011d091c051306020102031308090a170102030f0f070f0c1a010602030c060610121d011d160303080c0c19030302030a0b0108 70
    0x140e08a44072180365410325801250708004c024000017200b280d650900c80132a04a03821000105484c0d803000301012000c0b4064014071501291100e24552611042507064482c0003064194220404e0015169090a101540003e0103500c2c4550035601ca402c0c00a289030312543e505e032460130440202048582c0305109691141d980405154224000342d02c44000e950000904213600c003d0401003c6a60507001240c160201c100200140c2c0380e052040b0f000c840520002e000c00d00402001040008441c2e20813105541c115203410004240c0400e401e1441f49903d04040c94140c40701e500000096040d07000004101d40901d0105854054440740d041100106d0401c207010002220240e0b40c081c1c0c1d00265100301002140140c800c24180068400c103425034407200103808080d0280c02b06400c040c0b10034400c00d40480b0615803490140350460744d02922400700640403515040c00840c060007070003c200041c1c000c1c010b07050b800d5181c1c3e2409241c01006036100700c03588190306080c090001c02550043d0012401 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 81848283 1250 81847033 81847039
    0x9150f0a09050f1606140307020c13090c0f060305060d02010f140705060c0301030203101103012102090c09030c180a02070f0816030e010309030c02010503060402070f0807050105010608090706181e0812040302 91
    0x441812b00108049800d246000c0750482e5034a00007a400a494000c0060003440c1c1480c030085442e00e00750f409801c44800030f084600603048181e040300142ea00c28001c0040311402c2c1825141c4d81100241c040d01802100c000400700d1190401740219480883d01841c1224070860482d01c0b4000150b1200302030f1403101d00d0a00107030b1000e0006100a04405c0020344a0003404420b00035402c6d460740004085d09000c0d00e0b414401440050483c01030f05040c00302006510080d02e0390100220803180741c6019a40090041000a0740800c80d1020080d510b070050346e00680084500307845043d103208071110800145003c03004610075030791208031540a40508002e03150903854941d0303101d8594006544581c0028001e9511940c2001510700084408000315440c6020f8403415490f070419142c41c43c00c4810607049a002c0c0000201004146800000d15609564140c5410516000ca0801d0401c20229980001e200c04c50608201210002140300302812291014200c4851703c03152003082c090b6100b68040690 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 81849533 1250 81848283 81848293
    0x70806070f111009060606050a1205130804060806010314011d071202070f0b0903090603160c02100509040b0108062b08040303020609150f0a09050f160614030702 71
    0x1985000e1003890015115a090800110050300384403400c09030043d50052010369030351000810300501d481400c003d0b1405040c014500325201c10040c00041507001d14000160301d400024801800c00c020b5041c91a5000c606191580d8035170201070003607001240c0b1240040d141c10344040b02410003076000c5040320758070400198003400d44d09140710323f030100400b58418040c80f4400321003003605a01c0101007180c010105030326100018541012801005003200300250300512000c8041c1e030fa100304580e000400012035025880c40002e059035403501401d00a90702401c500003080039150400018050380500303c0d800c10405410300015241d890b8183d604a0301320302000c0007503003184016410200d00694181600b0090569951003840d00c2d40321741c10440040c1c1043d8240400b00900300074a0f41403400141c280f0b0740501c1d08640031000003030020302d01c0000c2030310344041c00c0a10030705001a56802c1001c0c000d079114403030400301d0000c205002e881104002413005440d50803a060701c2c0d050360300800d082e074040c103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 81850783 1250 81849533 81849541
    0x90a030504170c0306150103060f0509061e040908040504140c03060d060908070302070602060106020f030702060708090a0f0503120310270c030501090506010201090507060302030711070e0612070806 87
    0x41416000c0c0303000031090348180141c40c0c596503810483c01b48544203002e02d000d0810352000004040e070b600d03035000000d503858149060099580f94500b080c0c0c0800252841034813071030313501c00c000c031400ba0380c804460b0030514080c150414048030100400c192101070760140100c0c1f8410480b2510824100e9503480030000900100c0c8c503c1c0741c4040c21070141c60081d40d0100711004c031030301c49034115070012034100d02590040008004094052140c503004260307034006420f490810301c007207684a01c50500000d00c00c0341d001541c8000c200c44502270791008070000e00080901da0f16401c4900c282e00860040d2407003480781100b4805091051012a889822010b9006440514081d4101c804140c1310003c280706804800c0c08004c0240c00f0310030300e071003000c1d9640c0c085035551411001104450014103140e0469050601d44c1c40403444c006009801c95000e072a00594990b1980011529245000076040980c0241400010310300900d0240303502410089450100c001103403030550b9a42c50070740c070480f469038020b40002 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 81852033 1250 81850783 81850799
    0xa020d030e010e030c03031812030402040213170a0b10140904020102030403120f1803050a030f0216060c0606060504080d030b0402090907080403022a0402030a020d02071505090a030504 81
    0x241e0110200a000411039444020000d821500803c034140c106034004020010300c041c24050103000200404050811000c2001910095110092019000f20340001d1210316510107820302c01c00800f000d407031440205450300005078584046003c00c1d1880c800c8840414018201440700400311000040e032460801080303005d000003920001c02c20781c1940001c0c400003002c2540240601c0e03028031140d0f1241c0155a00c04006030003400122030304142d20b6140310b400c1c0000340340002c000800d1501410568054111602c04030300d004034200b080d60005c40c160b00002501c68100413214000740c4a00000e0091320303142c0c2011200341c05544601c9000f54042e6035910303c0180291b01c180c840a10140c4094608050880855058801595980009030303030101004149030f814000044081074801144c080e1091074840303a045500c1e0904031a201390ba0002c040b8503a407800da030441d840118010300a40d1070303180504280c00300c4095413010350307540313810040040c100b4400403d00c02c02c1d807070341a22a107040c0341c205040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 81853283 1250 81852033 81852041
    0x1109010507060f02130b0301030b01080615040f090215070611130509040c030b010e0919031d18150306100605040902030411090a020a020f010e19051c0801090605060a020d03 76
    0x3c0008040d420070074031244165501c0141c02606d041180b055503075255252413030203075805034410505500038506200e4008000c00b0003c0c405807089401284111594000100408a041c0002d40c03217807880c4a02080014035202170300c22107025840401030700100a1245611340f15108034900603070441442402949407002a007600a80034070b038113100c0700d074403035440084040c1c00b80c100d908040c80410030003034961000c0080c10a11042500591051101580c01034003e844050070810303600c2045e041d1a60684501e59049042000442d0401d003e003840c0d201d1061100300d00864034064000c1c940003c85010059a41e50101c3d00c4907581ca9242914151094000303400250081343c0340b050a041003110303a40c54000060150a100c0401a9150044580680b5200c10b20042200710b9051a16003809000040b844114503c0344000105400c082032400d1030030201e203041220119288030104c0701c40640d120011034140c942180040029603195030400070075000703c014032401a1321840f0003481072031007508 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 81854533 1250 81853283 81853301
    0x181b0a06030b1f2c0a0b2b020c0307080a0806062d0f0a030522020d02060a0309080a0801051c2f04140a14090304060c0c120803040303110901050706 65
    0x2078124400403440040c00040440d02031540352452103c0321304000c030315101c5070b5600101502d0400d20b00d014035035150b0308000c55180368a000890b8245c80ba640c4411813980440b0355030f60140007920b603a088075103090301c03560704241b9a100000390710354001061414079404440182c08e101a6102d6400b42641e003080d0007010010320480c07494418044114080d0841c00900b1000010361070110300341c600107982c3c09581c841d1101d9080e0000402588002588a210b03240c2c0349160180c4031980c4e9100c051000390041d0000050003003e10f800050b45002190f4003400721810b8074812100e90381105105040d04582518100c07025051172940aa07038000c070101c5c08000d080c483c00c0001c0d003240e62035129000404440040e01d1034480d240080d0204990201540302e208a9911014034080c041e0528420155407070055014800a00000888ac54140312000c0d410f480104800c0546200060700ca1502040710380060f207044020904042c010022603003450203407071418a040e55030a050501d192150000f40031809 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 81855783 1250 81854533 81854537
    0x906150c0109080307050d0c0201060513020906040302060c030d0c051315140406090f150905150d0203041101020d0206090d0c0c090609020a0f020d020a0b181b0a06030b1f 75
    0x324942c000108400041c1d4850103080c0c5903151980342d44510241a518030080c50411649002e8051000e50364064450300c54002e070800060301e40c1e0b04000483e050b84501d8101a502c101c01190a4aa0002c000b00805251441260034000c4409502040c3c907640210b08800303806442d1480180400038480d031595503c864245004001c022040c0c00d1440c90307a00680015002441508050010405447ea944010440381861550495080400611003041c0d4002e1502ca00100954035500c140c081c401c0c4e400442031880215900e00f0b292070004152a1807480e09400b500400341c42444040c004900b1034458042d010141c14540102c220441c7c4c110500c03403044901d0780c500e901c04100d4822034881d842c080e00c840350740144d90344c20541e0f01a1052100442e41400c642c842022142c6641d0b0103d842d01c25160f0100e00c20034280ca4040c843d4008040040706078036148501e2429003401ca54000300c60300c808071305480c03902c0c034207480301d404506450032540102d81080401d1108074004040b101c4c41008440030f4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 81857033 1250 81855783 81855791
    0xa030b042405010611031218030d1a010e010309151d06040c2402120306180a06051309030215041b0b130603050114040c09050a0b03090c0906150c01 65
    0x240d208810024260000301030041e902d100503c100c0380c00188010100d11600c000b50308200c03d401100118001c010724120705c44407034410031641100f04000b0307201280081c010030721030195401ea140442c8850952034500003450390a550810754040d00c51000183d400a42054201d60344071103002c0603082554080900c2034120041140d000710510500b4055407142503400c40c660720f040f80b00700b41043c0303c0008030a24603150707500b20b000503000610a07502070f002c0300300c0c1c68503660f61400080252a8904500602005035002c008483c01540d0000c002d45004658450b004454000300c0d10403280343d940d00a000d0b074052050401e00300c102c1804bc9610074410120750210302003100d46650b1078003c0341e001d4604400c01040612104200c0551030000d130007107140401140d0316001d070214505038041001c0f4043c13580d034400d00440034480d2803c18080c04c000b5041c005c0e8290385100c0c00309a544100d555071514051440758501720300e02340840302e0261800412801801685041d040720329800141c00044642da2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 81858283 1250 81857033 81857063
    0x51507032f060a0f0c020601090b1909020c390f06070b04050c09040b01150215070504080c030607080103141c03090605090609060a0915060305010c140403020a030b04 73
    0x1440d14a2100092084003810690515224420a1326904c004090025091031083d501150b030019485044511900010400c17206c4440840ca00c050001055440c0940c0d42e40c0120380030b61190014400d08000c0d808944044000000c00c25406d00c0100701c1d122070418800f0f5002e020b0400e180c0728074064200818580d001d403099400101c1c5a40b210b8002c5612007a600e0410060203824800c100c1c420744192100401c0d807800350794602c108081400707409401001c2181000c40c0701d1007044048810a103030f1540c1d02e0541454240903089800902c1400000d10030803500e0710f500c2c20003083c1c031402842a9203500c0800d03400c0d40d03035410000d034100d041c0030028401c1441a0080044520b01d40840c3d00b043d0b103001548240504041c02900c0c5d0040c260f0310035600c413000380261100001003103584030a281c84c001440c190349142015640c011902158956814003a010090220640c400080742c0203603110400301040c1d0185107182e6028501c0080c0d80b25030354903001c201142d00100d0240e4418445c1c0308404400f18 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 81859533 1250 81858283 81858347
    0x15090f0604090e0d090305031209010b090702063702030601020f03030a0c080901140115020a0c08030a020609070608130305040e04060509010e011404020d06140405010f050105150703 80
    0x240c0d000301c2c203690300c43c01c03d422656010f001c43c40314050740f80341619035541940c943d19540d105149081d0080e412040010301408000c0d401140c090000921152a40c280f1200003540d0b800d003a1201000c0412180042c00e4a40c02d9050401c080710b611401e8921009091410000a41000702800c3c1540981150308801c0401400114400e000c0440001030f04a40550010040c0304001c000e4031003603241080b1210403280c111145c50440d540290109400c00400600b2824940c440000a107505030025010403c250084080c1906401d540c0c2181d0070f650300c5500c1d4a6030340e01144249000300d1500d00c0807800d015640070602200c03900908265240c51b90b5842c0607450543c04840a0314196603d45c28004510400c0c003a001c0c3c845104d500030701000303100701104142e440001d072000b8881c0d60380c40c482204201054000d03481c070b024240744030422840e140c20120f01910034031a1380038105181500101d1207250500003500075800030900c49043c4002640c00f41c80c0059030f5001c800d2000b400400f1400444 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 81860783 1250 81859533 81859537
    0x405041a0405030a020127200a080303010312030204051005091f030b0a080106060e010c060b03010606050d060608130305130e1504060f050d0b0711150f060a0515090f06 74
    0x20b4030490081d50f84012585000f42155400a51018200b08202440300100c207400c01150a450300409080f46a50040c2d480445002403042c00f260480c410340000030f0a00b00201c0030714100c0e4054660941e030085a040224100d11507809440e5110b5100e0344000361491250000e0040c403500600b034810000a01701170307014003c1c1c1c1c5400f8000000d4075481c20080a042a003c0300c0c0007860b4000003031001d24140701021f006060040e94450402c14442d0501090022a81201e48003680103802002425241c400041840c1c0c041d0705200201818040c0004e6458032510740e50784a110503980c88070481c0c0359541d044500380c0c806010003219a0b0b124074042140440600180d00444502140300030300030b0800148015190b60b580407460449000a08215545890303100c03090b1243d0017000340c0c3c003175030300c010054a15008608104465200c0d00d641020800101501c07203011b17801c4100c2c95152a43e8200030401e1010403405401d420425042445148140c100d0240a9000c0d000380b481612141c0320000c20301c0745d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 81862033 1250 81860783 81860791
    0x60d1e0503042402070e0109020a02030421020a0b0a051204030203070b1009060803040b0f0a050c07060306140f1320030f070810060e090a0609140a0e0a0c050405041a 73
    0xd4540c840300c3d000f101100c0c0548840305002400907110881c41c2070058201c280301442040c01e06030700007460b0380c81c052090003103901071700c48901413100d003054800102e902c0080b2480300b280100c1018801103402c41f024010f88002c1c1480703950b0300d4602881c1e0030f902c00b83c482020b40110194842800f2100000b122520400d20501300e05540c09940b505e017011407020b980e02580301c82810b400c108014485216040111071a81100c030b08c4c00d6685d01da4240c001c903904d00c0b1380c40a04603d40500c800124480f541504100d04503143c07062003126000b101070030816280c0ca00042582d01100d5524a035103440d82035004006d001d0b170040208400d01d00344103041d0700fa13640102c840800103e038031410840c010f90000046c907001181c5801c9820000e04140016003142d0100d06030ac0c2c0319400c12400644101c005410003001f03480040414810a2443d4101d118603040944204860f1814a5812444140c0000f482c12001e90400400c0798644d2900061000a101c054000c2e104c4003c1d03000110038020040c0e08040c02 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 81863283 1250 81862033 81862049
    0xd03020a02040f0b1818030a09030204110c0d030e010e01060303021509060c0a08040602091203070c27090f020301020a09080c100f0813060c090306050a0203060d1e050304 75
    0xa140c0c40c4100000c40d10304650b01c00d242450046503a5198035504240200c615082c516442a5268129002c0200400740742c041203504c03002402c540c01c568000b4842d011039100399014080c1c20740030400314031307103003c0c0e4802404e0700c2d40a00040e01d80b041c030980080d0a9801c00800015026121b254018250f5a07260001c0c4c025a2224100c0c902c103900303984604d540100c10f200a0700c007a0412400104651103119049401c0001135008a400d01c00940e04481031440c0050003100c004039010111512a0031032a001d440c4815000030004207040c2d070044a4403c401480d90000301c00021414000003019890f03001e95481000c00004c00050b00d091008048282c4581c0b581b01c081031518201516001144c05c0301c0c0e003c0c00b034056240c032650f504002003860001c040d0812000947d82d80505d1141d05140003800741440d403c0a41d213041082d0044010170950340191410301c20f550320f080c43c500c10703440181e8080340c1000140e24401e01284150b554201c0d42d11200c1000490095947c0742c10b851134002c0c0d005601 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 81864533 1250 81863283 81863293
    0x2d040302090112080307051c06061707020f0c01030e010b0418021009030203030906030a20041809080f0306130f0b0a090b01020c120a0602030a0606030c050f16020a03020d0302 77
    0x40d4544003003582c0c0104841c6800c8900c41c034213a03a4400301c0307000140829050010125241419035000c441c2501040c8810200300f211554456008012000540e203010300d5030a1000401c0d29030703201052514015410000400155029000450081258000030849550317250030310b100603900d0b806010014803c4400c61303c02107849004000354203551a1050301401811042040140c41c080146c030b100300b108071060f03900d0365203522100018101c00c00b614250707a00c50080d42021108090301400c244d40c0c58062001c000e51002c21884103d0742c5806000d084034401380014100381d405040190f80c03004000d00308070300420784c400c9020243d034079020182c00e00b181c9030020001e841c01d101c00303114000e0080502c14000c0310b4075480040c0d00c07004c00c00754840c0100d40c00102c206070359100300080403401d0340c8020115603c0c0b500000300c000070840d03030068030300007070402003e035480b2803040d819a10b003035080185662902100f5882102d2080d582ca1003281c20000064000005d60b45460010387c03218041d4002c0c1c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 81865783 1250 81864533 81864539
    0x10201060b030f06010212070c0306110c0a03030e2401090c02280204050a050408030f100b0d02030108070f0501050a0327060203070212130504020f0705010608150c0406142d04 77
    0x6800d1507da44109042190140803240103e03c03442900b504032600300400041c0d500e400c400b40c60140c81864040319807807040140c88010140c0c1544000a0140c5010660300c001c0711121617401112950590880c000c0f915100504c4030300e0b020fa000410300c0c00e150044504245040d0300c0c109107040243c44088080d210030700c0da00150f00f0305004ea6a442a1031400410441c07910382c1e511030b200d00000c1e1030344c00d00014100024954007980d4000f60b000c1c0000c0701045d03858bc0d140281c1c1801079882400340004030b01440c040019995020080c010603030702c1c16165030f810661500c00c1200105803e4100c840940341041c444548007a1081a4500c25806410056503c1ca00700700e02038502010f4116450400004008400b080c0e0480019041941c2d811a00984c1d07540c0d00151f00140c0d402030407005800c40d413a00a00140200700021164108401558542e0f1250b5803030021240c035000e20b10400c1c0c00b00b01c03030400030450356001c000100318500c0e20b14440ea4600c060150146000c003a800300244c40c604c0c000a080c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 81867033 1250 81865783 81865787
    0x2b02011d040c1215060c11040605030105010b220305030f07030c080a031a090606040603090c090212040209130b0601030c110a0b01140409050a08070807170d0c080603060103030806010201060b030f0601 88
    0x1d055620100a5131104140c40d0550050480b4031b030001c00f03032118400c1d00702c00e82655540c1d0000300042000070000c0c025561640503440320ac1e8808261180e1020740702c0c00307880c40b085082440318222030304039002c3c1d03091070000383d450071485e40264811070810446081d01000111031001800400d802c96034001050100440001074116000d41150300c00e0380c041e001c05c13000b5503c2c00d00b01c034181d450620b0b010940840900d0081c102d04650b4000a2030b44d030000c11402d40107007621203418400c174022242820742d03072180d07072040c0300380399120402800d02c40b00000000c900d9402034011b4002120070380341c14160098840e980c241000303c81e0000322411f01500c8010040004044200443c50008440030004800039a59643e50f41c5841e90300141509800314540701881503440c142c804258103d045d080d078444494500d044071381e00c11441102c010780b4081100145611644076030b440f4400150051100d030b402c0d0340b0282c3e083c250050a0724110b64031000e003c51206000400f0790b0042548d4600712095003804800 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 81868283 1250 81867033 81867041
    0x201020d0b030c24090301020711100c2a0302030f0a030e0a0b040e0916060503060901090905060601030e03131e080a0b010e0402031504030e2b02011d040c12 69
    0xa624800da102c5486a5410307070321045524980b01d01c1001200d600c0041d20310044c84d0b4050b001c0300701d41c10752000c5142400d100444186d0720010204682d10003100080c130b0400e8660800b1400003604500ba000320021a54001000000003940151031961030150740e0303400a441c0280101e070054040d001600c60000700354100d6a498104002101d0700b0102c2c0e41072429107085401580b181601c0c0c400850301042c141c0e20180000f11103c80c1d1400603400b000d0721a0006441075009503030003401032100b81c4c0001042086480f40c0e031101035108020f003016490301c0004501900c0c1400320401c2c180001c101e1882e1a0020800d03440c010708002d550740c0380000e00d0701e00c183c42c010002d42c049480354100004201c00a500051402d0541b406240205001d859034008240750910509803411059210400c0c0400d0580202c030420304150200c8590100782c0d5803e00b031140310281540008011113440c68440c0042d800342c0c0d01030164002510b0280003400c603510014041d40d10329030024021034001002d0850281d400c1c05 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 81869533 1250 81868283 81868301
    0x110606060405011b020a080f070e090613020105090117011502072408090a0209040605150f0a060c030320031909030c02130f240608010e0411031009030201020d 70
    0x4080c0e05140c41d0000103010443c401d001c000c0b444070305240c08411503035103991000282480f0710460390307443e22203c0704076642c00351400344124110032a030001d5515640010f0741d907c64081e00d500303007010390f0243c0d00660f4150480c3c2c100906004c9414000e500070003c060019008000c181c8a01d10031100030031019040c2032082c0c02040604100e05040c00302050a80800e00b24007885142a2805944203180c00d41080401240254000d201c08140810301c009a080f450003a0361000c00030341003806e9842009083c01403400c20f585c1041c190f07102001010302a44040a030340e8000d050103d1901c203011454500b000e020303621012010000310522030301c025480e01071040400081c0c010421013100c3d440282c100065090300070b120301140420041342e60410740200301c4246c0b4024003840055140d140c040c019160246601c06104801140002c0003442000407d04036507030300440f0041034039540c4941c455424540003594042c426402412014841742c07164920315130080c1d00068980034596203080c20703180100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 81870783 1250 81869533 81869539
    0x30d110403021e01051b012003060102060c0a020c06160c05011106010909020d05010e0d2304050907020a050d02100506040203091c03060f120b0a0c12020a12020307110606 75
    0x1000c1800141c4648080c40c2c900b0103100b001032032240c080b1004070340520689002c1d440f00c402503511820490b03415000514401d20441540b019400001008a07039404101d561300d0040c0e015201290702d1170501802014800614815116000305400218100c1d900506c01459004051030090050102c00955140542800d1800d084103603102c01c0f2035542c441c41806200743c0740e40e07540444d004651305d82c0e4840204961000c020300c00607965080301f9803242d500c0c1e00088081040648914140f11340384490610031501c0c40c44480c1410704002c00d200c40942d00810080962146035420350101c0c03001c01c466088400c266006203440c0c4503c0c1c0780e640589601400b5180164018400d0004078074010460761001000f00c003d040038940c0444040f00606290351003132500c03400340140441c04510b900d00b0005440e000301e05080150b190080500126940120303ca8001800d0f060007208000d0581c00500b80500d0728071300486102c0303800401c1d600701e031f1007910203002066228000c03103031120080c08990743c0304d1411 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 81872033 1250 81870783 81870787
    0x804030b01080606131a12060702070e06281a0417010c0527090108010b0111060714031003080f04080f0a0c140d060203040f0b09010605010905101709030d11 69
    0x71101003900d014801440010060b1115046c5115200c030342250f028807040101a507540603540e440f816128107050301e040b03006000300718001c100603c0d1060318170300401300900120713810614040396205206141880203c00e10402d40009000d00785005400c1070343c981175420954881c40c14074041140d0a24105403112a41480340d080707516908002541c03c1c4241c0910b12071010351103000c0801c40042050702c0f4130b5008101c0c400103d0014015031200507045c0c0280c90795400500000ca4250b994281290007400007948141d00c1007860928002554001d860016030b80030b99604c03940d07204c42e181c100c1c01040211842c049400c0125040811025840c0e00b001c0018150705803640e123401096008600880c20706c03a011410740105030701d40740091000c068000100b1074480c180791808103081850750380191500d001a20220300301c54410702c00c8030300b12841611411185413400040c4280c007038070100950148108180461466001d60503a248200c1001c0043c41d0f8448590300c00300b0480e110610075042c1c3c4202 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 81873283 1250 81872033 81872041
    0x408090909060c030a0b04092114030903040303230d090b06180105010809070f1404050108060705071106070b0906040203060106050a0504050f03030403020a090911100c03200a0804030b010806 84
    0x83c641c200c9410034680800804c000440c0d80209010305041640242a078040182140018010300700b90745400105a0f600d42d800440600401b86500054581148d0758004001c00c00019026185004031b21001000c0341800c55003000484110b1b800803110240c409890b042003104020603007903401c1c2d01c03260440c1d10a0300c003600b180100c01212014003c090500c401200410311240c4204500d000615410b0508554a034075200c40c10004005494854020760403c40041030203100420f43c544605050703641d03e428503055844005600840940ca5508210200068004520b1040500b4030420000780200520304052045c10714010301688041c0c00c01105001007201154000210303030440e441113428a0044d502500040d0462045500c02540290119000a40782810381c00080300180100d842c0003030365600000b800f00305060000078400242440c50114001307801561038403100408040c03034140a903161300380c00d454122101019682c2d1500480d0400400c11707040010360140000c0c201800ca1410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 81874533 1250 81873283 81873301
    0x210110604020d11271503030307030207031704030e100e0a1215061e0501051602060d0605100518030703020319050c03070f06080a060e06060d020c06040809090906 72
    0x2034003a00080c4500032032402d8006000712401c1036441080001c0028500044007400d4241419404400382101d8030400005455800340c0118000141406400b41d0314503a103000040f80213501c0075030f007142400f081203c6180403c4120356480d1041340b080d03c5895000b485107040103d0002410300b030740c08000382210f8822035501c440200c44111649040304e4440c401c03680c5016180150002d0341c0d0101145000000030380c0303030341c0b000c00c4145c10301d040106900306580303400044440f4807603030300c6040907a0000440c9400605202000b4412081111000540c040d00c40c030000c2c02251000d080e1400007032020507001c00c4003003030804410322204220010400c091950b804241ca81c03441005284440594920400070312100703000410b16204001c0540301125126211181114218003404002890039400204d507021030b4412350b0306a6012a4501c1d205586d4a410044e03107a00061109001c1d82e000d000d86d00c5078200c10091070307000d2032040b0301d1551980d10346d8040c40b50700940140300d464540e0280003881003c00c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 81875783 1250 81874533 81874543
    0x90203010b09010807090207030519090e0f01061b0812010602100f1506080601120e0a0b010918140307050619230604050a090206030a091106090a090b04060b0301090504021011 77
    0x6d84401000d078a030b00c0c0d00c0c2400e0310980140a4482c40e2298401e0580e80c0c03413940300c8000400c1c2c0c2c030f500500c0c03d86030302c91507408880e40e03609016141c0420391380d80e00060424690314104c101184030740c8900b407078400c10340c80741600740130203a01c040050703449404280601c5070140070b00801000480030800041860401082202517240f04034824880c074400418020b0f4842c810350952000010000d008045482228683da0f90341d003503058801042a03070011404121a010f120620304000c0311000c0160101e481e4000c419100c0c01c0341e29010311003044210300046040c010148240c85c4550441030ba5004a0550030550303c04507005418251f148001089106851104541100c0c007901c00051075035074000240000d0a07244801782d070282000c820440c1360b000b0b50b00000f911503c104d248600c0125550300b030200c83d000b103142550780030b5a004814040701d90b055003d440c3d0403100410200f46166504d031040c04941c800c1c1c20482ca0f494a6108200642c00c00a1050300c00158a00c0c003900507100109900d40c0320 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 81877033 1250 81875783 81875789
    0x71416020f0103061d0105012c13020c0d0216060804030903241a1311070308040c09090503040e09060c07060b03150718050d050607050a0309050d03090203010b09010807 74
    0x801924141d040c0c0c9034480c0c0d016001612507614115680c041400c155104200d0910a250000d000400c2c1210405075152020308055185007010700300245030010005002c1c07519805800b016824490300544c1041000589405502c0b030b00039004442c0203003088941d880c025004141441004801c1c007001a40c844103d104998100d800d604008002c074840c070038100c3c0c20039240720300300d400d000784200d500401940e030903000070f0111442008500038030007140c25556102d9440c04144010320856010a009000c075940c401e10440b00d1720700150301c60b40301000300d4071041c00c180c4056101140c03e0100c0d030944000d01d50801800c0b0700421207854106000a06032180c180e006181542362508040580c80030041003e46048a00c007500340341c5000c0e000202165501c010b80a44241d0ba808001140d0901c0c01214503c82d030400080d0030342d503446070307416695548100000000c1691343c0b200701f00462010b02c01d00c440c084240d43c02141c0c101c560f004050070b50300400e6240d4404e2995400400400d800094002e0072 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 81878283 1250 81877033 81877039
    0x715081909060207110111010c02061503100608030405030d03021303080a0309050a081e0903060403050307180305010203040b01050301020a0c110f040203011e0b18190306021207141602 81
    0x500040055050041c00d655035000300b90a0021400d602005402c85101c02c6408007a13981044140303801401500780d815540b007040150f0400720108846800d01e10100d032031040060111a0441100c1c0c4c40141102c0311540501983d1704041410b00640c85c0c240704014107581c5518080d8240303030341903038529a030f0142448000d00d00303140020040a11030081d000303000141c1d00308042e1005140c441c01d0007000c40d40403a1900600c01d01041c079040c01031401c001558103155011707004101d40e541d6603605541551015104030280010a400d80000703110b50390520000d98858400544c981c10103203441031500074180c122038420b9006020740650507034400400d4070929000001030511100500225018401a003011500a8000400401c0c2c8c0180c6a19804401c036591810001040c0d507000c0d10303011401810000c0c440b100c02004d80030941d1600141c5540c010720f5104c1c0c071140c1c05550b50350b030808076401302981c000d10719042020040b0b215084180e4000b14000c801d280761900c8086c0c2d04c50303000c42c1004103000348 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 81879533 1250 81878283 81878311
    0x19110117130204110307120c0203040815100f0602101b02100f020c010c02010e0c0405010303080103060509030418050412090b120c090a030f05100b0609010305090c0418020102071508 80
    0x10030341d5101c1c0c01c8030030a0751301d850390340382c0e0303414024070007001820b807404c40303650380c600780007000124910000031602110030110180800d001300604544030081c025000001c4800f59850108020066407601401080150000c0013424034071034100341900d42c00c01c04050210107402c16071000c280c011904602020b050200020340800e4908940000e004070140445d45610f004c4114002d02d03015072199168181d4901101da5104050003000103841d024000140002c0255004200050164001c2504090404144c1c3d05254998141c21122111444a030a02c1900c50341800240080e00c0207900140c000703458200d01d524242900c03c8403500c03c0100c6104107441c0640010040140790090703600750100202600007080d6682002104003e0340b440c150340034014022a0222403920b8451120100030242001c1e090400800040d4000c02000301404074600400400807070942d0390344289401c8803031a200305000746030395000080c50042e054204649042412501c04000b64120341e1950703000751800c000d94 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 81880783 1250 81879533 81879571
    0x414031206040f2a1101020315010513091404110904050c06070c03080a02071701060612050405030d0e100b030c030304050922031211191803020319110117 68
    0x401000464012000314125540212407019413075107141c100f0601d65541c41850340303d580c1c103900300c1c8802c0c0d5100005c914803c01c81c82c02940580c1c00740c080303111500104e52449545007244401d469180595641e09828030341080304000180302c0036544401e0648001905190640c0c0d030315520342401951600c62540414000c08028071062841c010b107034040b0741c0c00d4803543c5842c4040c0d0307990b20307600600000b050f0303029000e14050814403400044034200d65a00c540110a04140b00c01400040c00071341d014001040720400b042000d0180100416170740c4000c24481032400400401c0b1812094140d200c0e8124030700740741b026a40003003510103840c82101c9251135500e544183e054102c08600b030314648200e103903008000b0726810545107031000142d01d40607c096941024240301c0c4e841b85030f070300581e20020000903148082c41502c10703000040d020200e07003005c140c076500081d1500c111080301c00c40b240c3c00d070300c3c001c41000551104400302c071200303007824415007141e202c4040707408100600300e10344070481e05060 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 81882033 1250 81880783 81880811
    0xc0311040f020f090f0d030f120f05040c03030905040603030903060507050c100902031b060d1d030408010204051302070b010e0403120207050d090806010b090616080c06041403120604 80
    0x22000740e0701101195502c002c1808920680c010b440110312442084269440b1803d0082030450819403546c0c5038800341c4101e80082d2000708040403001000c0d0350f180416a100c0300e0300d21540e4003d60151740f00b0005a880e51500402821150300114011400e080b41000000c0e007040090303040e2640504086010782d20741ca0b0031281e5010701034402d030840c03003424407040c40d010156101c0c0e06140d000394180c550b4007034191072540218011003030b02d6030006005c104154000708107a210314410400c03501206046161700c41c50034503581084d0804942e607540050100041c1c500301c2c8540e422085c035140298104061a00d600310030400511038950145040c00000e41050b114408400703000d18a44011501e402090510b19600d450344241c00020504500c1d011070007400c0000e030340b8103c0d910303540200d06d0205040144062900a0055228003507105640302002a0300940604480c00050700103054501e42420305000c001c44550164003550010842a01c1c0003018061040c0e0040b03056401041c0ea040349062 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 81883283 1250 81882033 81882041
    0x60602070326031e010504050402011e0908030d0e010f06050a050603040602161211060433060b09010212040501080705031812041401050412170c060c03010504180c031104 75
    0x40e58003600400000c02014607a840c808a515103102c04d8072603003680e240c0c3d040c0011540150f40181c007040c3c2c52020005101107481000032035521914110034000d50341c070b40407480c503001080b2885240e9100c10304c0ca40014000d1140c902904545802400700e0707842c16000c01d20316003039070103501d006040001c0051b0510805030100ca040130f500780f06100ca01c40f054103200c0d040c4011500140005141c00709081c82d61030001840ca401a1381040701405c02c1c0c47c2e50f0002c0d49091020b01c40c01c0d6007422418082520f0040c0034850600100000c1c130850340d4a80da01c500090030040c030180d420440e100705010a00869a1000d0425030001450420540d03030b413500c09003c5c04000706030034080e525110f102c0c40c14000c004404040c10882e04840800e0b441711084000644960259001e580d542401240210340030035810248291110310f44500a40360008250415003042c004840f005120400040100890304141c030410384084000b250782400910159100010300440e40300252240d01054059441e0b40c3e00c42d40 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 81884533 1250 81883283 81883343
    0x8160305120c1b0c0a09180512070201020f030712030507030b1c02010810050607080703030e030a03050108190b070f020102091206040b06031507050703020c120a0c090606020703 78
    0x51a820700b49007016000a03240e1010280f00c20010755003e024000000000328a0442500180083c0481e414803e0460040041016450381242800c4100011440510003440f00500d02d58040d6591001800064501000402c203010207502c00c014010115801c0444240c072a51645030205191f118039004501900c0e284603c1940302e2003076040a010325540c0e020020705280b007a00d4104842e40d644141d03400c0340300148200c0350401010410a00003403405001080c04138424100054079004102d00c103460358101d1412030780400e6940c00184842642005503110618038400c1c0300060709580d6a44505010001d4400780c2807007408030441900390b000390183c1d10303552005080e058000d100c1043c1d99aa0b4941503c00fa01e0121410300070031a603084c08a0031400d0007480c11142a56030312003000403500d95004850a07411030141c21080d001035607580210003202c1c0000e1005180f45c01003070402202084595001c0c81d252880c0c52820002c0540101d80081204e403c07120100d00c4000c102007800800d890340c9 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 81885783 1250 81884533 81884557
    0xc030815130903030c0806030717070902160302060105040b100315152f03040e040303020705030304030305060415140d0302030403050f0303181605220504061b030908160305 76
    0x101d00c05090010591007078920900070381d4140412041c41e00d06881140d0160f4030640c15422201040c00601c0c1c07458400c1129074469812960300c96969403038003040340c01100b40c00c04416501111a014141d040121901501d400c0f101048026030203c0010311559020214000b8551141e940c19030095035080004000c02005079201a50802c40c1c4000f01803402000d000d42c0c1c07103540a4109041c50324040fa809030300100e04801145040d003052444001500300034411410107408101c00c1000600900196010358481d8401081c20f0401c14100415500403180d44e480c00441100c04119142440d213071010000740598500d150301801f0304080f8114030907030304003074414411408009148c020000095203d00000c01f9550710142030044659120034150100350080c5844181c10700c000e150881601c0300e07841103480103c2c8142c550a003440c041e10004c071801c1c3c840641c0e0b86490034030303000408a030020702011881e040001605c151b0f6414903034024402d16040c201c0c008040101098014400c94064420702 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 81887033 1250 81885783 81885799
    0x4031106010b0f120a18060b100e0d11030f070612060501080402030c010509010e090f0105030f1609020d18110a12020a09090201050c060103050307200603040f020102030904020a0809060c04060c030815 88
    0x7506003030703016240851405003c2d011804600354650b00c0ad0400c850964401000514100361036221350380c502980c14840380e4035020343c01c00709075504400c00c440c81c01085c030340c0c5807011204041900501159010340c03140f818000315104000040ea004120030041050034201540c0f0f40c10f01c100100c0356241d420003010b400001c3c09050000718010005200c0c100c4604904460b601245603074510784030903030b01d502903038130025042c418400000a500540b0f0035a0300000b0008240c822003d541d0b515800c403d10984920080c580c01290700d08014aa20000d06154844480036010076400720365212814440c00c1c203066900c03840ca1003160700c40c4040b034845610410456036903503100c1c01c02036201e0384100c0d0201c440f105020314540100a03c03042100d8018001040203085594030345400e001030361881c100b01d04500042000307a0240c1e84a1001e00313030010080e5908a4545407480380c182c90440042d007083c0541ca8144010000c0d144d1020384448040d500d440d0040b001c1c0c8070425000c03844251600e00603440154 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 81888283 1250 81887033 81887081
    0x403060f060503010c08010e061305010603051602030f1218030c030a030507170705070c0e1303110106030807020607060b0a0e1504090308160e040504031106010b0f120a 74
    0x15504020049025000c0c00c00a240d920001c15080b960481c04d40700120f40b940340104082c1d2070012403254018400340c110541000403150420856409030000400b003559801444800d144003d036580541d8598001141b9080c0740c840444814000c411504000800240c00507841444407000e565200d080e07041180d842f42c10701001f080d00d0b41c02ca4003440c80000d00d410009000c851040c8080705040e0940e003800d1400340c80b203c4c41140c56a0080400b514100e00c03805000940c83c3c03070310075000c1c801c81036104000ba03000180e20f001000a00f4010b55001941c3c10820144040390715602250442941251000c0d0f40e40f40c5864407170007400215502652021900c0340004604d040c40314003d1003500f1520f08114a14a02c40400088840c002d4001e8002080308000807100402d81d8184a107000c5076052110310316203030700001001d50748115070482c000741140c2060b00c0805010844140503042d245445030900000007d00c2045004583d000d85903214118046101c900c0b0541c082254601c00950300480300712 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 81889533 1250 81888283 81888293
    0x304030c060224070c03050c060106030605100305040b011e0905010801050a0612030207061101020408070308220614090a092a09030b0402040b010e06040608010e0c03010b0901080415020403 83
    0x39103441030401502950404840a0244640908440080601c0b404403a1980340e0110b407100b440700822801d1000400c52803110881c2040707054004c11082c0d0300883c6050070a8207210501f40c0008185090500340018040012405103410b070664424100f110407242204000302c07515400b07076008021580c030b0000081541030703040d0403192103500000b200340083c1e81d403900c0d00d42885041034006001030300000c209109030fa20031b25241380c410010200141c20107440d802c0280c00c1074851740c4121002640011040840c404081341c4100507401d0400303580d00d461800001400901c12150031060000000450300066510200c6680240c600d080c0c04200304280c44299240c101035030a607a9a01e10540509441014420584407095942c0900c0180d2580c56036400d00c4080c14046000d0f5050000c0c511041400781c80e0340340500b004008994450354554540800060068401340044c40c0b2480308000511040320b401007215404607080c60892600da9881c1000204088401003076071f45103000140c00402d0107 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 81890783 1250 81889533 81889553
    0xa0b0c03040f050d080a0e061e0405030d0516140106030b07020607030b060306010903020103020c100c1e09050607150e0304080304060801080a0b06150702030111041d010b1803030903030403 83
    0x40b1032040003010306864000704070244880990040902600b009441006c03803248405038079181703016014500701003c418201c0c138204032035505100c0740f5601080801607803504220b215609a900c1c10424600352040050720400c00c5034034005400e002c40c00384503156041e400d50120005503080704880c809400c0850009444010944102c40041c8c10500d072106241b51070300840f4000c010503150f10483d5442d6500550107508007900701f041c580154010300d00b1140c43c5015204040209a80303001e41d40c10300030120108001023880309800c0080c668818810340d101c86046990b000c4e082483e4075150702d0340d0382207903014004002e8194058040800c0010f80044008094000d90342c860302ca656040e03072500c120580d03440205a000e080c40c0e15420111790242406e0b00c1c600c003003002c4615054640840c43d004a0700351501003c2011050200003410005002c00e61b03054800d02030060440d83c015454400c0c03c40b03450007a5030501540002c0e4141494059404000319603080e03002030241c90300e55a40e070402c00c4280c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 81892033 1250 81890783 81890789
    0x30e0402190f17061c08030703020703140304020603010308070f050d020607030608011103061014031014040525030603050708060a0605010804031d06071406042303030a05060a0b0c0304 81
    0x1c50052035040307407030078003070089007000c440180f114400907580c003420403528640d1054030a6460f2054a5103601203280d240007140715242907200940e45041c28078000301b5503030b8108200c1c40c08203824024000140d440c2e00071a0b046903004081140c45a0907800c050f241c5040140000300b01d8842c180e10030382d0700380d004161640715142d03d032030411020b6525400e0718261907160b04000c159031000c02c005150b520f440c40c501c41040609142110342110004e001c842c0692090701c3c002c1c5200e9821004001c1c0d141c010200180004041d1014000c0e401e100307000741c120ba0091070420025a21403185592514460f81c0400001c3d0f42120407200000c1e51102d10544404050780c1e41d20f0002e04125001c0750319405007860721700503603040c4d030340c010400f601813111001c0d540918015944044104213410100702c10108002c04022504054090307803d0070b2070214068842c900f241080c0740181004004141c1001c4280c07a40400505030224142e5282000036030f100c105500015010f41c4041001c0a1030f00001000c7e00035 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 81893283 1250 81892033 81892037
    0x307030207060813030804080a09030512070c06050c0d0309050c0d111e010203030c13090f14060109050a09270311060f04020d150e07090f050606120112030e040219 72
    0x12944909448220500c0641c10141c003146e140004180098410300081020003601d203080c022468695440c00d0914209501c00b00840402044040910140040160041001d41815443c100f4103500d040d8680100c24210b40a15580e001400140141404070301100072004080c0e108901640c039022054004240125004901a007810018081004600c48000405030000c41c00c0d80d0b1251112100e5512807920301140ca5000003001980260901440409100e1504d020038421000110b810340071000810140c100f14200b24200030301d407074104155050360880e072000301c0e00c00a0b9019900c0800322104a401c4009050083c0c0d4041c50750024900d21218682001e5512903258405080503800303054078003075032011140c0d1b01000003031010031204200a00d010300c049099019440300e942072240d1580400a1544c41c2c810020804200d84515913026004640d4142042030105224580c403005000d000d041c0901c400c40301c07091600449100c4d410410080065554540702005583d8001e03100c60103c0c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 81894533 1250 81893283 81893297
    0x30f0606030c03140603190f0611030f1b0d090302030c06150916021005040302010e0a1410180609030207030c090c08060301020309100c090503150702071e1214030703020706 76
    0x5042c40c181141d150003418001c0c0249840c0402107030140c1e540d820100110303480420070238900d00143c1c03540200b07800e4000c0184550344910b46141c4080400c01c000340b955002c02c42c64420020702d16000303010f40300814503014000030746610600c1c0c207134514414a5000c1d0311034801c40e0f00b080402c6a00f02441e17a5aa40c094030302102586400020084071031649420b000942c102010f2800182000d9020316401806440081402184c01d00c0722410020350741026146901c41d409000c80b801820080a072604515210410548162001002c0341e0140c90800814481c0c4681036481810b100704240f030701854005c400c49002540e1009010014030200c1c2c21070010603028400626240740620a0304e00c11b00015003e4402e01072034407042401842003128040c18002400c1c8045a2070301c041121030481156100040d42d1401d2006010385800b90aa10880e5020401240c3c08034400f8402c0c80d440032a003410035094900d588600c0c050350b411008200c00070b6544408604442490350000700c0d4400c443c615140c0e56 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 81895783 1250 81894533 81894551
    0x827010e0c011409040504020402070605090616090b191e1809020a08060d0201140705060406110301032604150e1005160201050904110705070609081b01050901030f0606030c03 77
    0x143d0b040581000c0015120300512102c041d80c24140c00c1700398824402480185400c94694031601122401d89100e50f841c0c5c0300504108078003039560410b0715017492900302001011b18204003090300744581c2c0c0003000300c0b54041844644035805400109981004d2503a144848002c1c640010100082400701000031444071900084112041c42150032640c100d540b02c4906646030340c140f02a005498100328108207044018402070700d41e80003e0420580b0035005880035040c030381002c40c00d54825101010041c0d0b810001000007922444004000f94a905c0003071382e002c5280c5140780042e0159a0005d206c042280e40b00c0c1c0380c01c5a00105151020900300c40440f11000415000c650742d0003041180b4410802c6440201c002d58015000307002d0701c200082000c24000c00c24840820950400d080840702c0c0c0d44150300a100b1141c00201240c003410007640100400c0008240116111090b0240b05040c00000915624680d05c0790704048201d4501140a214003a81c0301c00080061510f07428250000345040c80034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 81897033 1250 81895783 81895787
    0x8040b10050108070507020f0301050114150f030711011b050304030206070309030e010e0a1707050315090601030b04020616050c010233060105130602012702030a030827010e0c01 78
    0xa44107480c0e06030358001080d0303034100782a00c1a600800040c1d80c0060403840d0f52030940e40c00d000d018081d000d90102a80d50610314800d000b000f40c1542201660020300b8040c9200c43c0301c4510540f6480340180c0b42001d00b40d20400b40c01401802c01c02144496161050034000b2200d4001e4021405035201e036003142c5140d0307610b240850403075031280d4004002515407010f0482030343c0300c0c2e40102c241030002070034245500e81d40c00b404014041d5071501c080300b54000100400c802d142c188a0300407100f440340480c400030315101610f1038540005000c004c0a072100040072409640380e0ba426110b1581007003284180004280c1041da980daa1485403460040c481c00d84542600c00c40a03d141d00491120808030b9180008420203008102c0c0052440d41081024020600a0521a68000014180e075000041c3e41c6054422035020b000103104c00d00c46041010444100584000410b081c440d5054a4441955111f0403141c41c1c6c440c0b222140c00804202d01410492040010344c000280100d000e000c40d210b00c1491401 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 81898283 1250 81897033 81897061
    0x8030a1b0614040c1509030303020a02010f02030115020c0303040315090305090d0303050a0c0c02150a02010e07060e010207050916030b01021e01060e160f0e0301290a080c030304030f0602040f030308040b 89
    0x6103000151021b5030820000340290040c1c03144240303500011a441d009401690200e8009070300801c03540c00c4000040105036010302c6458041081507000c0d40c503090441d21084c009003001030b10650703c07664034010b940500d44070740141c800804000740011500d58481c01c6c0140a000103440d500e80aa00d0429080c51450141304020241c507405880000724200c441c640345150b0300410102d1781507541715000c0492515081c0900030190003591190020003550b24002071900c80c1e143c000380d0162001c5401d1018405001e030910110b80310601d8049610f80da405d0040b41000e20444401c8001100e124000c50381c5030041d0002010345106080800c00355850003840c040c1c0884c16255140811224032520b003070b4a03c10050002111400740011520a103000b000a030b0481c1440320f81c0c800410300054544840c03800a440c0700041c50340710002c00c0e403020b505001030748901c242d10000b0300c010340030b008680401c00140c05032401045408444c00c0403540d03a040103040c1207000c9400701e030b14018110005090803480c0d91 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 81899533 1250 81898283 81898319
    0x5040605030d0309020d02060309030409060b03071b0c0306021b0f060c120907030507141e01080105130605040c03022a0c120f06091b01030608030a1b0614040c 70
    0x410b6082c0d4528001e5008221000c0240e812001040c1c2050150312600001d5000b804c060700111303503903031072715034071400f1540580c20035164031f4010414811001d0780180051024480e16003002d40c00142460003802035140d6600c0208054008184400040006258220150202c10944989903071042d0801d86403d000c681940380d5142c1402454412024508415885040e9004a4070803070341701c1d1906403134007086a001c04d0441c031040c2185041401e0040e2002080e05010464030602181c0d440041c00c03840050080600460880413035030031701c80c52508040024180604100910010700780f00034080c0d80085c0c2c41d2400f829058145407c1c0c2da00380c04400454840c554060410aaa1117080045020583d80925405d101d120110265048107102c102e00400c40c10b002171144680795002280012417102c030050505291403401c2080c50700c003000300c1b007a1124034544194509413411a428861007214005400645002010351035002c60001e03080c040c6028880340001030b0717502d00d440644107030900 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 81900783 1250 81899533 81899539
    0xb0a03080d020310120b04110108040c0303030c14070b04020f0901420e030709020c0c0405040812011203140309030d050406060515040509070302191b080f07050705040605 75
    0x410032107075000320750245401200700359000f200e1030b50320320041e00d00c02007144081d034070070740c0e41014442003010042c50100350303180078242100e5078a03042e02d42a008812510014051546500c0b0700d080740e40c8a02034640320044c41d513800a4032854182844103440908540407401082a68011038031450240001c074121002e51240d030042c1096192000070420025200016403604001e100722108038441510a8101003640c6150f210160441054a0095168040c4901c02e104000f8001800d03c0881c081c42e1000c42641d01040c40c1e00c5600c1c2280651040440281c2c00349001c0700003103509480500d4000d04503009507a5041c0c24118400c11840d00c0c40240c0d8080c600380d200b0000040110b903503800080c1d020b4010840015610383d201c0100b000d02d641000260754441000801b4007841c40d1110031a60420010700d400c40c10f203001808800c0044d41c0e10000101440301c3d071742c0440c4065000303403c1c03407004550292819455510100320510b40f50010007044030240a03500c400318941c1010321031042113807002 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 81902033 1250 81900783 81900787
    0x306240a090f0806011a0d0f0f02090a0b0306030a060914070b0a030c0912060b0123070209100f051201020c07090209030d02010c080703020906040819050f0105040302070306020a1b11040b0a0308 85
    0x6c000c0031304a5601050030500d245890b40b22000f03103048184101003028071981001b6a036603c081c41005a1514a60002c9d10030181c1842070101507100024080c800d65800781000445000600389860700b03501d0966035440c2d5201d000800700d407407505c11028000201054900303002d02488040140e500065500a0700704142c255408480402c034583c12640740d40c1e0040c1484c00000c81030307441c022540480708400181c010340001c0c100045003081c80c031055009030000d0f1580380365810001400700700324013841411300c9182d6145a149150300c080d4100c0d6899000c0c542158039060751038814402940040c91542d10034010b4a00102c0c843c0d0044c012494504500e9441001e142c0c0e03100f1080e0000e410008241da005001031001103003407134040080742d035517604400308081500e43c0c0d4540356281010851a030b05550f414074080c440040c1c1c0001d021811303603510101c003507110411070700212014168030940c40078801001c49101c040c8000d44e1480302207604151410f0150603002d1081c08100e0556100040c400181 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 81903283 1250 81902033 81902069
    0x5100303090819080f070f051c0309050c040b18040606050f04050906180a05060f010905011205030403080a030e010507110d0e0a03021003060b07111e060306240a090f080601 76
    0x11070010100d40d10119405410403965890b000000b181f0700c01d0488465001d0620000e03144403802c20004256118603040c041d84106a90700340d154000c028030079005030348401c100307901e9660b4210701103880102c00240000a2505041c4100603041d41d220300f50144208845981140c2028003c680c81010142c00504550721003040c200c01e066004110a071003402101e1040300094814880280107200201403000340d9410601e4500407500103034440c400c4030074102081d100107803001c0140c5080701d400000e9543c84160829043d40078003034250054440323501c0c0ca010000c0c13442d003101d02c542c40440580203d4a081c4021041581d0512401000617881049400f0800051030468000c10100c50035203408941c0359525461881c40c1c0e08540400c64421645072000c1d06603050040340442640e1981050b0104404400045040e0344000f0f040036014841080341c0340241c0101e004e0f40c407203903c24107a030a6070320300ca4040010007a13440b6000c0e04122074030740880026045400a0194166407031000140c0c40581 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 81904533 1250 81903283 81903293
    0x30b0a14061e0f03030904020708030906060103090f150b121b06030105031b060705031603030e010c0801030b04061104061d120303011502100513050f1b0d0507050405100303090819 79
    0x101d1400c00f6503141c8070400404215072178078009003800d544240443d81d02da040502c0c40906010303000300311504143c50005000301142c443d0800783c0046401c20400030407249101e003400054a1540c240c40d40100c00104e00718242400001d001c400d0340c0b00800707030a040e1903032101001000d1100b8480c007a031651001c1c0100b281e648040e60710324a0040010491450308441c2da030f9107030442d000440204101c2054032412400d0542501518515100f440f001708101083c041c0080d102035410301003e0005101c0c3c4002174100f1100d5480b2000890346640c42507103441d901d08004218001d00c24520328000c050508182c01c80c100350440340302d1030311098081c0d8196800d100754200300004144d041c50840c420410500244c401e10301c11240603041c200c80180901885050041c608072040002092a40c403000004041a030440c804401464048840c042ea020035800c0007880c0c00202d4101036071041c50716050241400441030002e00304ca200342c42d48100103540704003d42d101c1c548140b0388880c941c54060b440d80010703 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 81905783 1250 81904533 81904549
    0x6030606060d1416020f0a050d03091a0a23010b030c090102100c08010303140a0207180902180402031e03120403090b03180f0c031207030306030b0a14061e 68
    0x2600d000000121100201c03c00980080d0595030304c05119050130301118002e40c107000c2200c1089014000b000031078190303a112603444801d031518000700740d507410b591401c201c813400030440c5014280e8601040750401c00c014000400202c10042059068102c03803d05064540101034121000e02c40994256030700ea8805135032a5100c000c0315030450003104031900508549104007146180c113941c45000541c1985405804a031036101c05482a2005001c070100841e07000a024040c3c400050444107141103840540c805810032002c001d50140780914550540c0743e00464031841103008030121200500d88070140640b8030100c00203e5960340080081c55044a1115165500f20b88a460290899683c0c0c00242d0070940064420010404a5803420b04082108001521082c00351002a0070710300040400241e035116140207070442400003140c0c071003d050290344107400a64024581ea0784520b41112040001c14820403a102c80c1c1c882c0c1c4003c5011800d04041024403840d2169001d001c203000e03002000802 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 81907033 1250 81905783 81905797
    0x3010c030f0b01020d02151003080412060c0306080d113406090b0f030408070804030807060b010810050d05010608160f0605071e020328020114070803041b120818090603060606 77
    0x1110230100000250a0300014001400703e0307268042500740c14605001541e1401036018200760404c0e00a00205d00301103041079050b0003a090906e1200c0108000d1814520a40d0342d656280441e001d015a1208104039441d080341e8200b0008114261560402e03980341e922400380d50f031004018028031680e059001c0040d50414041c001550408007955210f4a081e8806c0d001258601004510381c020010360380107851b110300d000d00b0100710518141460b0a84c0103800e1107910720034070551000741d080c01004c2d88030001810a5005407032091203103800700c0004082034444d04154410400303001034070300d10900035122002e82c01100b2582c2035003107041c003030b100700b040070300030790f80342c040e000910b190418040c510590304c41c0300201418200c1c81c6800050404a405000654903407810001100058110004c40f58059400351060301c1021701034182042c840715540010000d4203070035541906126217000640085a8080d408a420303035117682c18000040429074400d0f815901c604040341407072400b00041d20403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 81908283 1250 81907033 81907051
    0xe0406020f071208090a0818040906050f01180203130204020a1701030309050301110316030513050d090f080a020d060e030d0f06030c1a07030e010e03010c030f0b01020d0215 76
    0x2400522506804075a01521085903169080310803607401c6500404032a0f0f20841e400d000e000c0c105500c2c1c8518410b03128100b80c500c0108800e510303581d45903440d50302caa103100360440c01c04c0001e483c5c624900d13040b0340000c1c060034000301c02c068140000e17581d0b9030003200d200d100100d1200ba0030f024641d00f84800b17074120f0003040301801115184400e000a40100260085000c1d540318114685030005150031a00315902c031001e40d040030004c000554120041c0211881a42c0c81d0010b01e0750380f00c0d030340030440c80318040c00202103000c1c42c080001d8203940701d00b0410581d0710b19808180103980d00c26040d03540e919443c034000c2d040f0740d820b441c074004111070741c2c0030100115490090301d1a03c1d44040f442402c96035100d803d240c18a680d94030a200b801030441046014003000090302809000742c00f007d83c040d000d5404002c1c10070000c010f10144c5a4425000100381d01781c0900203019040036108e003d806080000079803240c02d89441e46610039903200140c015580880e0340c001d8905030310310115294810300c0003001701d05 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 81909533 1250 81908283 81908287
    0x9021c0c030f031205090a0c12050718060e0f060a06110a0b0c13091e0b0109090e0309040203091b01020c0604140a05030a1b06170105010c0f06061205071d010e040602 73
    0x20003c840c5c01424810b80120000e000b5544d01c07840c14500c0030400d030b08648210044031448100050700010714000740c40600307010442c4031490003800400f4007200c0e0800d80502e0340403c24000b91180842100d40248401c0310010f00f100c1e1181c0c0216440c840b0040501c03080d40c45030714410040340d018405150456032414001c3d10304403001840d10708501180d84604140c030350380d4820300a6000958408129031142140c10b0203207480c410b00090061b196800350440c4a940d0300e13541d5a40d00030030412203c2444000d80155201e181c03d1910648480c4d0a00c072180d501403840301034201641c404034003100e04a000078100303820a03081130341e640c400b203100803112600b009800302d003c911035074204144900144601031419007000c8002d038060403500c103a0300180502041c244840b0103180703011809419100e027840d00980e40081c50500301841c500c01c51020b4506da1600d08045003060f8400c0130103110382d010b035084801031a99205240b00d00084003040341c0c4aa00040d0044c085031900c034000c0e581242c002d0344098 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 81910783 1250 81909533 81909557
    0x11090402030717070c051203070806060c1903080412140d020c071d09070f0503070302040e0a06090b01052103070f05070305010e01050106030509010209010c080d0e03030a09021c0c030f03 82
    0xc064800d055520201080d61760102c003007000b104001c6074800041c01901d260550401d028040d00501000d0581031044d270000c1102d00e00ca00c0108000f505503c146030018614a0b01c60034090803074032054405568401d03416000c40415801002c1a80d165000c0100c2d248c0f5007070710a01254025009041c081da0103020f03003070380000ca405c10304c4040c141060000311000c0c55400c1c18615280340080c08c2d03000200001e4503001c02c20460b40d01195140499070140d40109000c034030f13040313418108100c02c80b00500071407615005000384144690740b203040c0c0c0d0f019100740c42d500280c5030b8610300a002c28520056070f9881001660300240d0415002084148030350125642c1545983c1c4450a4690b059072820081e99a60010040e10b07605005003034020441e00021490302c0a0311f00001c01e41c09102c00c019007641c00020360b8609605035944644007007540f090035a03840703091180d1448040c01a512042e8428102d0680c2c045282804904a00f00f0300c0d0f011181c08525444c41e682d10004550940c0c055061004500c0c40fc = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 81912033 1250 81910783 81910817
    0x302070b061309021f200a08030411030a150501080c0901091805030a0806040506010c0f030809030f220e100303080405010906022d0f0f0306060d060608040b060301110904020307 78
    0x444485845d2003076007504641c00481c01400042c102d612114400401c4e41074040c5440040b910503006a040725480303035a503131b0780d0401d10403850701c0707100c074a4261103031200301c03400c0c0410300014015608500b4000d01032a607031103071150340e00e0032060081e560001e06c08004020043c0e03150320042c6c80044040740c4006d400c00c19101c2a00316000042103901040c0300307204111103803030280b0501c2c2d4000001d007004c0e05810100d45a046c040359524100400b0301104601281c140c0c00304106440300100301a404554407500d007004c0d2041c0c1e60600c00c10004505000e100400e90701c0f010203169224403143c0480c2104146140c41c101c1d40d502c0c001d84240c076a5540d0307000311404203170741c1d0000b040301c400401008020400c01180350005075841d20700c45944514140045241c0344c41c880c0481d5420344015903a55220b17100c035800a401845241180114146049000500382d50094403180c403480c002c1c01c0d46041c40da00c1e034041c1802d8a01c8e0703180e4021001c3c1d040140140c00d180940c044c5800c00385507e01a90107070501d01c4c00c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 81913283 1250 81912033 81912049
    0x6050a06170109090b0402060a0e1903050f010912051e0f12060d020306130c051305100b07030804030c1104060b0315040b0f0d020d0602030a02040f060302070b06130902 74
    0xc80000303607104214004100055503071500522903100104540b5410b919010110040070704002d2145074001a000b1003a4032500000401c1c0e24010803204101e850710f450695a681240700482d00d50140007a9021390305810300c1030400c2c031508000904c1e903982d40d81e40101c036590300c82503c030f51020b68000d00c8803020641801c090030510b03406214080c0d8900703481d40c20b45000b40b00213220b2403082c0ba80c84103800040c2c4010401c04e402100385007150703540401c50300d4410003615440c6c0256801102e0720a00808144c3c03941c1055015003050040042480e85603281000342e80303e42900940414039800104001038482c4c00c000034000c2c0900d110b03005011824000400b07480c0d266210a80204000c000d004d2280380c582505c00c480c030011a001c0001420b2040440d09455204c440e01c3e2081c07107030b40c0c2920159141c9480d86511541d002c0c80465032803503c07030917140c002d411038010031044101c400004100d0900920807518401c0c0c010700c00b1702d825500c0c042008070058008102007580f50300c0d4115000142c4400030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 81914533 1250 81913283 81913289
    0x1a0c0304030507030c0e15270901050f0c0a050307050f0d020703090807062c040e0703061b0305071209020609030703030305010515040609030303051f0e0702010f0b010207120606050a 80
    0x2019112803032550410a500390220703080300012910503010b000741581207910701a8180001c0c0c98100d100450231942c4104052000c185c0409129407804009020324190b000d24450b05d003529207503205803590003400e1028011010184003049040000c82c03400c0d8014006881e0011110191524106030b41d02c80c941a40c020400c21804160b070b54400380810013090101300c000d06403600c0d004400707800c500311540c4421001c03107840070b540c03e070181080e00c03e44843d0850b40c0078401c080c080b181519507d14014000300b400003060300f2140f1141c2c0d40388c210944039000710b40c040c0203681d55078400c1d405088104c00003002404001c83c0c2c440410455540d054038103115030f40c000c0d4002d45001840750300d040c05100c48661038401c2c0181078601000148000754002d62401c0540b505880c0005980d41c1e420540240400b6041d40304042200c0e01c10b00291111101020314403884c481c5d8000c0c490200e084601100344c0c0d04d200700560141e00310460901440c1c0300c1d200c3c01e000c0980070301008641c059484011600305203040e0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 81915783 1250 81914533 81914543
    0x50d0513170d051803070b090106030c15090501021c0f090f090c090902070305040b130e040c0302030c09060f060a0201060e091e0c0109091a10080a0b030a0209011a0c030403 76
    0x8600d01d0b000e80141d00c07071241e00095600903c0000b00421500d1612441081001412802c801000c1240450254000c7c2c001e554442c14101400340c8450b48590000003c425210000c1c10507407002c240ca5201043d081100d002100a15001070450401074071a5103000345032004021811100081121600b044071004000000d4001405c18607048010a08550340d0070070072407240100003082c0080c1d03101d0112421104039200300c0d62907002520440b51030103d6a4007944043c3c034803105010070b0109990404e012241b00305d088034610b11040b41801b607081022240d05a000f4401e0745070100509011000345001065803000040b015211020850520030680302000d00768000c80d5030040c0903810609440d0b071050004000d1500391003110000b003c182060203680c07501c07a00d40980c2d8100380720401b0348541c102030003001440c076440010001071101108440700e81100341410280300c0e0764140481c040050640142441c1500c0e070a003640514802018954805049810000aa0300200510203000030354840c1c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 81917033 1250 81915783 81915787
    0x1205071707020d1a011502063706080c1329010e0a03050a0215071101050a121a090a0204060c0609020a1a04030605070e030c0f01020f01020f1306030606050d051317 72
    0x8a01c0b546403200b06c11610301907500103810301c085042044500220f5200e0303a1141b4000f00c0d00d0205040da00d043e0f101880c4840e500b046004682008007140c24140e4510640d051744c00c08080c5241c66050762202800c94000c600451a2b004002549d00807440c051034040c1451080a2101d1011919403540c6a10944298020207480001c51810121035481a60071340c180c50304080b415140c85c40d11000040c03440c0d050020000d028200503010300303000d020083e071074502004481034400c04ca180c46007500f48035500c10b0160200081c81c240c5c0c03c0c404d50381502c4441d60741259050f00c3d613441800030300081805030b030b0115803180005102500702010848810688141c50b40311840c40c036203141a10409000700062048400444000303440010700c00209a4040ba0340c10309105499005030304203006c08015020300d50000400d540c0480e0980b0042c0a6034100c1c0b10110034a0b036840d0803c50445456020740c0e400a20200506006140b403504566040102c1445016141d1f1041d42c6080c6c001050075000d0b6601400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 81918283 1250 81917033 81917039
    0xd1103010f0506060301141306030b06042405040222170f01090b1f030c06030c09120b0f1e070c031b02010f050705070806040606031205071707020d1a01 67
    0x280514051100310300d8061041c0e00b043c0000031654001400340e500c0c000303680c2144090581e105640342c1031810752840d0812000c0e490303050107894803204076803ca0089040481346004000002c1b240000c0c40000750000c0071250602c400c11000c0d5000d0080008803c420504030786211107245d11600040071200c00d50005480d10003402410705244c0301490b08940d140250b00c40114403d00200c940c4804410301c41c3c0c002115507404180c2036800c640001e001100901c9004c07038a1501940320a550f60b10a40701e941000da5140c040b00c04940c44044001c140c182e80318040351504211501580e0064201d0120000854028000c2c002c5c1001c11030780040051300c1c0405802c05d15400c5501d000340119180190700c807180c02e98002a040a0282c2d81c40c400700903000403481c050010500251014000c6282521842c0c01c06091100103010baa00063354030000c007000fa0030100313004000f1901502c0d440001001e50340752818403c5000d40201030141c0e0403000065018001903050a89520209002c1d00d5840792941 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 81919533 1250 81918283 81918289
    0x20406080f0c03060405040618060507090506040f060804020d05030706062303070608090a0b040c0603050906150402071109070c0b060a0803180102011407030516050405130b01030b0d11 81
    0xc030261414400300005000d201400390350404a9038000e00664010640d80c440b1b10b00100140407030140c42d646403010030540b000300244c1c0e17080035014030720329a100c0c0f0380e1640300d1040000c0b902c16071240e000010780f40001040814000c100d42d5a026000402c0550410b0f01c6840c0c050035603000c1002282c02c0380d51850b0600c110505841d4080c01c214034029190714101c0120042966903000d8000c100900090000007194200104400d2080c140d1002c3c14411601341854203041c44012402075102182c10708000030360300c00c0001940b42c41445004400004502e03120b00340720003584604016600310446000380b020607103c3c0c034031140c00340c449541c60411000040c00c00c0b281c4494040c01d5548030b02e04603102000f00b00b500009441e02552540b2050a003591702800503401800343c4c0c0c041d030190304100c0003005002a003580c04240b10746045600029490701c581012a0503206a020700340e0310218400c03825004514650020061030303418140040c1da54941000135606109401c400c07522117041881c0412181 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 81920783 1250 81919533 81919547
    0x203161a0705040312030b1201111903090b01031b0f060203031806070903060203130203011b09060806130504050f010e0a02010e0f090f070306050603100e360703080d020406 76
    0xca5803030040e09183c115038401c5e49008a000d03c2004044e102c00f01803c0b956107010306d80c060710700034800800c2000c440003d114416009003650f0340d0321518805407810010301a000d41c00742603600660918032607003155250106003541405040c0040d04052011071150300c103070010390281940d50025a12460a20509000300c103200322500c8180d003001c8280038040c0e403c1801d0000f176030740c000f2000d84c40b03644034107598130b009511000c007a501d0b60038103802c2240810800a900365440c5d490f640c3d07461a5444490603549184207807a080e40092120300075050400c0c46074040d60f0058815002c1d6100b4480041b100360a548503034014203000d402505c001d038115130300b0011080c000e05055034580385107244da200007550700100901d01070701100b82d0340002e08001d01c2039200c80050a0000c00480e1281080d44548420107040d02858800341e155a010603108084071006881c0d40c03000030070307600321070004980340c0000540c00680c003112445104400b00000700098050400341314602c0c40180c41d240340a400404203 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 81922033 1250 81920783 81920791
    0x1060311100914060703050d06090c1e09210501060f080f060108060a090507150e04050a0b090c0d06050604030803070305070f020c010807050f03040605040308150109050f010203161a 80
    0x2c403142c1034041100001d07618110000020440e8007603200d448a04081d90144224090b201d00c2da0310702440442c030707040703030350300807030310340010307076201900c41d2000b800b211000c00d0b101400c0c1707000c21070710b8004114144404a501314108141925a1440300d607a5039001d00391b0340c0f240c00888246030f4400040c828144100000740b0003e1040008050a51406100c1902c0b29405000500755546540e0541c09001040020340d00518080c02d030140e070a800283c1c01403c1c128424240381c8900c1c100000b0550fa0707a00c80c0100514140e00406158198480d801025060f03030002041790099500e81800040399030f600030140c0019402303500c0481d500d1811540040459030024a807106210b2013481c407407289980001d190351081005e081a01c0c4036141c445040d110f034091608010041c910010400040204a8100358051440785e107070f001e03c5446e00755205480c0540340301042d002a0303010310200950725200b40050000c690600540c4c1c07428140840c9101110079a403810703500034410103805c0031900200170206070700c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 81923283 1250 81922033 81922037
    0xd050403110d0801051203042d1202031f060503032a01050c041503020405090a090b0106021906090c0e0405062e060e0a210506150a03080a03020c0106031110 69
    0x1030007102c02028003181c03810701500d13004030303141c0303a10710600c0c042003040790b0140007d02c204008c1e0302c3d40c0c500010344070b00070089603070035611b00c0a0002440014500c0c441c002c10341d005000e4035032440e005506240645400d0001c01100740c40d48400603143c0c07010f100a2a81c808032005c010300046a481c40086411f0504d014030a181c1c0c546401c2102c032540070300a03102601e42d404d18512800304500400c0380680942d4001c2c3e07034000e083c88144a003640700c0740d102c41c2416100d510300111580c0e0741c10042e0b031510310107418660b0940d0841801000100f444d03011251151080c2c0182c070302d4588801c202c42902a04444c2160154009003c0c884140303040e000402c1280649204c0d00b561805046840121304801d105500500405120400c01c5903100b80404020b031070842d06440000103800134410781c4a1041d2000d8809005c0c03400851440d07011501c510306280409000003943c1c6146903103903000e541c000c0c03007000201642444143c2d41c0040038000c44004502460340010394071410310030025014940154041 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 81924533 1250 81923283 81923293
    0xa170a081003080307080403020c0a06050705060a06050915040609050c0909090304060e010f170a050a0609060807030b0403170406060501030e0319030509070914070f0f02060c030a09080d05040311 86
    0x1d0719240459912142500c0d001b10385d515503180070780c41c01c43c1c103000281c0d100601000104185034028082d24807035004504031500c0ba15400c5606c41201e5842c09411740103007101001410311814134940b4031030340b14050300c0000c00d00d03a558512070450740305544282000100042491041c585541a01e41002c84840518a0b040c40c00034050001d1413904080b905025030580070b15142c501804042106481e6444000e040745482d0800d03c0081800b102c006004600d0580d010450700e1041c420001034030301c02d5005014990464071000441c1500034003c0301080b0750180f24001e0400809105400303180700b2100810b8450800f000503089e928801c00c0b251407940b007440070111403405602d42c00d0000300c040c200000d041e16100761803400c05d2415044441d0140c10a105e00c0c44500030a081c6d1171140700780b0b45d90421a05400b0b90111841b001c0880c0403001603000c00042a411440c2400860f04482140e1002540214690303540c4801e401000c0202031150f911820031041c10b0300221400100b2040201402c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 81925783 1250 81924533 81924539
    0x1080c100905040b040209090406090204061401080f0c0c0a030302070201080a090b1302030c1005070512030903040e070c020a0b030609070503010503190203251e03110907020a170a0810 81
    0x10001c5080b403040c2e900c03803500c4800049054803198111154074101500004080c40d141c10300d40b010300440341e41240203510780000050101d02c000300c00010400305035208000d81c1c4441990b10540c41c4050102121440104400044440c0170000401058401d4601584401140c0009004000014241c107403140c10044582c0000c2c1ca50401664001c0d03141d2812449070080c0d0000c00c4c0b82035054400b01340c1007002000c14804042c1c0044c09032001d544500212411046800f540b802035000907502c0a1580d0310500c4140440e42c0c4140c2800d0388005189051080100c03245c0000d0760710a0303142d2024001c681d0010503c1010b040007130341c980d44420103050652855141c00013103592414048440d0100d0300c20811424110754044c410850a44c080800d800c081540d100510720b0303146518420035a03040c0341407401c150341c845009900350850703030090041c14600c022032003845130b0400000d0200302140115247d42001540c00440c44480314401250203031505407040000d81800406000200700c07a41d1001c0c20 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 81927033 1250 81925783 81925787
    0x70911070212121c050a140402010f0323010e07080108030d180204110417010e030306011b02130c090b091309140601080d0813050715050c100501080c10 67
    0x5034101981561104001601040854201184107604070440000002e4604151a8480f8503100b80c142c2220108402c2c0c44044403581103440c20760345044142d0b109000030700598002c1458042c44045404d011460303107480d00e00a20400303100d05000001c600514014000c907050989402c0e40440c6c9402d01001e00c1d414180350603a03030f008800a03aa020750715042080310000e0000b15801801c1c0e0b01030014425140d9000c54001c1e6a002030054446411403d14023200a8005008100c207402a80c005589180c07102070045420390303202c50340c07a090600322006c04c1c0300603110380004151742d601c4100001013860b28828014a0704420f540840d46800c018803004101f5607507101b10a4451840c0140011018050f15000440b02c0c251040d0316164011180001507000d40030aa800c9800d00540e00c001d8142ea0320a072003941010300d000c02802c164042d4400b40551540b0200e4605610440d00341075041c003907031101551a014107d02c44c055200d403200010445034404100140003014103c5441441039584000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 81928283 1250 81927033 81927037
    0x30e1038031509010608030408012313060b011710150f0212030a09080a0e10030501080c0108040203010b0a230301050c0d051306060308070c0b03070203040b0c010e0d02060108070911 80
    0x650700a458031000414100700f800d40c4844024401c1d242501d032140c0d5a880d003a40203001c032070310320140703402503005840c80710341c00703500075445500014130684c03000c8803d0300c4000090040924090601003501d00307045080d00e40f5190706100b103112003104000c80d4244054078a6445142054100380000c104903c1d114540205501d40b04040308200982c682d510600c000000c4c00110801415511001862507415a0300030826040342a003a2060310031aa01400d0480031203901744a140307441d8001081200305984555640380e00180024000300351001610300150805003194050041a41d2249121040d52101a650b180c00030b0100c00801003490004100c8560b4411038410003402542c40c000109040301e00650381c0704a40c1c00c9102040620740300c1c980034010303034020041903500c03452100f000206110704408407480340900c1d90107907080510b0010250501d400c10100c15107195241d405c10754400078108580c290608140d4020201540340044030b606040703c130782080c02514140158440d0140300401 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 81929533 1250 81928283 81928303
    0x21c0b03100b1e0a0e010e0a0b06070c03020d020307050402030a0207061811010c140303070302030106180b04090b040204120605071407031403090f0d030507030b0102010b0907030e103803 82
    0x2264582007490f4100050b04418541c010040500d0014001b0030a410b00b0115584255440d050030040600210b01304141ca018042c0001d10b02406204180014101025055140e81c80503003118583c640390b4000405036041150094031040d0b010640005100c100d00030032a088810307962024500a882d1259942d81000b00c900754144440d08161200700000711403103038081c89049043c3c0340c41e800c208034018080d500030300c588030002d00903030720490708181da124452044440545005140c83c4c0342c501540040d01601000c070b40c5c0720342d0234000091030b11b0100c00c494403020312400e00081c0d1480d200c90040e0594810341c518101c0c16609100d84c50000340c01512002942e001800215280d544000605140082c6001000018000c100800c842d0580503007101e03000c0ca0842d141030000380c82c2e010049089841808c146a48000d440000c00c01c094000e611840c0340084060031b40300c504013405d0070282520800c21201e01c45140f1401d52240e202400958003610310210030310b04041200b241d001940e140b800301 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 81930783 1250 81929533 81929569
    0x103020f1e0706020307090303030507021f0506030307020a0902040f1703032202120105040507060f0e040902210c18060d1209050a17061602060103030f0201021c0b03100b 75
    0x501a850328801100550342d00036800384065503203141074030b0010599065807000314007090501010071022400070581c0325441310719000c1c01c4018076040501c0c01c050306c005008150540810090301d130240e101c60100310060403180300003503696442c1c0084070747c440600394042c2d00c40410500c2504c003e48404002c5907041400025402c05030000d03c0040c180004108800039403180c00d90300300e01000c00741900600d11850090b402c1e207800d0795440074181e400ea10b03003050a40c002240c07145224a14a013651100181a001500b00900c010768809e44440717084900a011109900ca030f900c8407418a012900c01c191407813000411001820018081111002000e800811410104103911440b5203e44c100c1401481e0052004500b5607403070644000751820035801d240e2174061200040c01508017034050091071071007940289002da10b141c0b011038200208144580031035408000c000c5100d100304603006007841100c200011401c803004105882c1490300ba1001110b60704118500030b460762800280b000444280c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 81932033 1250 81930783 81930817
    0xa0c05040e060f04020705010c12020f040e13050f150a1404061d0601060903020913030c020108040302070f0b0415020105010308040b0d18030201050f07020f0a15020903010501230103020f 82
    0x14548020b9240641d1304544045028018444150840d407110086030301e0300d0341e854124002c02002c0c1c1c4a44d000c44140751200304000c20800c000d0a0005500600030314900c5100510b503611f00d070034a1020702070407401368840007d141103000744101e900c0d082480780c0401c0040040d1048069040040100b010f800c4643c0c1d42640840c10f4100719610010214550a541c4c42c3d68544001510000441c0001d81c000e070250070020318080012103140440c290140c0342d410359542da03035004443c0194001c00403802c41c0101c1d140005c00610010714000079012601c0480d0b10f4a043c944588001081000e01d8011a030515004001007000d0740200c03019104006961030792111902e4060000e0300065002c0a150394840e0415414154190700040c0034104040d072040c0b0070340f5021740c12079513180c1d4441e41d050b05801c20a900740004003c065203040303003c01c018001d07003000c4108001030300f100c50907407207844402000508511440035040c070680035441c003401d017107041c24484858040d02d4011988404814004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 81933283 1250 81932033 81932041
    0x1f0207060f050c0703120e060702090402061b0102120f0901020310050907020106080f0c1504030b0a0203040f020301050f040b010f0f18020405030d0512010b07050a03030b191d0a0c05040e 82
    0x1141088900040d440400c84c0c0880ba660300d402c018a0f004120a0400601000000c0301a854150102d461061300103001c0f2055440e250204900c035880401820306800c4164180207554101380090000c00d00600d000041600c1c0c45540319040c1c01d0001c2000725603910410070809104a46d144010641c0e6007650821031a07030303c000007a4010080703600b01550b10301c503039550115044400a40c41c4a4048155810030401003211000c4900340658040100030060010005490300111b0b0301959020340140400d0b10420b41e1307900480d0031184160780242c0702e1390405c000c202c10f02540d07042ca20300400118015964051800c1c03d40c07050109030307004601034854041d11404d0f0000e0b03507030141e40240c84001e007520007072901454054402d512850b280c910905156000144400b8000103a4210310781040240c03c40b1031381503908500074401c1a00259005003411500c2150784069000400904070311076040c02d56034244080444040002081c6113951400c0c0146010555802425030f41107440598140c072254031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 81934533 1250 81933283 81933287
    0x603100b190905060406080304051305130f050c041a01020d0804050304030804080d0e030a020112020d091202030d0e06010501020c2b03090314060c030c090d02030a030903021f0207060f 81
    0x6038040c01e0303105450007640041040001688524000c4904039010041c8903902e51440341c603070140f480382c15030040160b516010034496035001194404980302d0080e02e1050305c0e1f074070540c4103414408240c596601c0086000382c43d081c203116a801c0051400c40e0f004c00c00a064000035611044e62014200700000b100210b0200882001502c020350b07070083d030441d200c0d82c03105410303035603004280c195500042500d4003904650502081c0e0251050701a502e003481c10070940c55110182d4803011140c82c510382d0340c100f4000401c40c1c101c40480805000d901031691400701f2006403098a000d40034442468008800401c0160b07000070301110b2201c4190f4030740d40d18041c2c040b5001c2e507080703001200044144400b1104010185c0c03102070441600d128022820185901300200d658440080342c00090381718003000030403040b041000141c0010307800100100004007940d0701181c00c040104030704a0115003c001c0910031031030140707640003603501c003100d22155040081c00300035601d070203522500b000d020001c142c4e40310710740c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 81935783 1250 81934533 81934549
    0x15081903170702251404090503120a0510090e0d08060a09090302060610081005061606090605010e01050904050c060a140307120c03020a0c02060c07170d02070605030603100b 76
    0x255462068820070320740842c010b03403101c00c0e500410300e24810350780300f15036000d07809a4443e0aa550280141c014001000305220040100c1e40c0d0681d19848140b0031405a2070104060701d1042c0520308002c1054108421a1542455240c110756601428009604100030380080c07400c25070f02c00b510f000d40f916100c3c2004180e29800c02e070001149a403d0001c0a4181500054240d01502040d28500d031010f0303003280d044803603820545500c03812007450780c410803072450b0203005450710050200000308104400e42c0c0b80d0302182c030707986411079086440310300401924240786072190041000780c0e000401c91409941d15500c0f00321940c4c00380c0c07180d1004282541a244100201d81c80c440210a14960301c1c1068840035100000019504050f079040054100480303201f03000740c4913001030944551501c06446c0c0d080284903000300129910340c0c8203050000030624260350700841c1c07050291003d40715400d60b0b440002d04084560b000707002404402c205102440c1c80c00207411400f903400ca04009503002084001440da4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 81937033 1250 81935783 81935807
    0x30c020306070306150306060c15110c16270e03071e0c05030d0c030309060e011118030303040c030f0f150b18010501051209010b0303070309060315081903 68
    0x51042004100ca0700790584d00c000d065410f8a140c210f81140d518004400355080c5005280014117540308110008107034406103008054180b00103e0b8410082011041740d40001410219a81c0301c441c038000800c003802d401e100602011382908031104001003c01400c111012690550680c1d00c04060700440410700c103440101e039001e04801d24a2003400400140d01c207a1490507601f030b200355080001c0302d1900245c1015540342a4540314400f01c059107007500101030f81002901c000c0d03140d100944200f0340038400e42c030903a02041441c0b40c0340d80207000344001c48a80e004609001303520400130711000c240540081011280e1203220703a820410b1a01e07190052760f5a07401d0040c4004005048485c0780c03420354000e142244421359000960100c26102062021800c1c410306011500401210401c410751668040d0b00c141da10001050441c10350012a00d540c1c00654142c0000300032840900409a242c020103c1039542c2c11400c0e46128217003c4181d4035034007260a034004084041d50807408241c0500c04c95865 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 81938283 1250 81937033 81937039
    0x80616080a09020301020f0d0f0b03100f0f050412020706090e010b0c030702150c010e0303060f24030c07061b091707050402040e0703180803010303180504020703030b011b08030f04030c02 82
    0x32401020034031521030300418043d00c242410704279002c600c5100741c4951800c90100500410b100e604241c1c4400c0203007040404241c203075483d0300300e510f464012400b0380341c02640f00e0841d03140602da40c1c010090901d0300c0380c1c10a10402c000d4041c100503895035203003001d064400c5011059501c100118115186103e0031400a4201c04401410442c3c01b00060160802e100440001d00c07a0307096501880b0f440c2d104c2211410743c414110380781201103090503a2204400203608041c849074954144000503590401c84006401d2031000621008010701c80c0510851008002c0c48207403182d0b00c075040505010380b039000e100441d000110802c50040c008200c0c1c5401043c0151045640b503460b80000c0d01c074540200d901802203410411441c031300d280382c0c19a0a1886801c0b50807070b0f00350307400d69070300312941d14080300107000700c1c50305030404074559a4520003407006031301c640c0300080d4807050300c0009415580d10103401400300e60640d800d040468040310840358000e00d0341040800d1130703503513250942c1c0d400020031000c2c2d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 81939533 1250 81938283 81938287
    0x20108102114070605120903041703031e0c091201020405040e07030b06100c060c0203040b0c0d02060601080714030c0706141506070c171002031f080616080a0902030102 74
    0x70040711000041454580205220040b1000b02c680c62076403421a0302c070f4440010010440c04240554081071140c2040c40c007802d581c6007d545482080e01d00c0d440249040c3d50390800014040581c095042000c2e4581088003910031794504024614524050610001d0040200307851003a4012001e5046030003818000b0010020408115041b568509036404200e41c030b5002d41c000f003a03091800009203201342c0020f54035101400c4c9030b980c0303141c090001950f1403825440309000106000103c8405828000302200060100070a4075900030325200c0c02900003418400e15038107018815500801820505000600c034681d00d8545182c850b4030b40c410f0581c054001d51900ea02d100c40729800d2240c1e13602406d4106070444150740e4890400009216031440101300e844110701c00c0240c84a242201c510000208050f41c1c40c5250010f0030a083c0d910454051b03401a040e0703032018512500b25500180905100c2c402001c0c0b070b1418085c4074000e100c00c5c0084009100d508000610500c0341030b00300c01c00c003550141c0255 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 81940783 1250 81939533 81939569
    0x2030609070503120f160302071503020702040b040506060f1b19050f0d090501080a140a2711090603100e1506030c010e1507050a05060601080606030f010302010810 72
    0x1503215281030180030710900031103804510b0f04940100345d07021079003001e0f50f2500d0160701c908486801e09207881c04406500940c01c0010714525076091004403034509840150b55144584104411205001071051065150000f40000794507604261035036200107001c0d040d07540b110745068411400b6400542c00b907510480d5850800d40c021a10604903192141c0122129010400c0525072030b82c5007107041d0400642a83c0c000c100541c41548a0364100c00349840000d807040021491280d04c40b411510038001d9038440889400020040c0760440c03031300045080e508202c20f096620303081032402d03821415200781154004034246070f40234000d441c0800e2000000704004100446c070581c03a081c1c01026188006094000a007203802c01107003100c48000705a543c103a0b070070f4002003003044400c0c0004180d8180f460a103d45030001c4c0301040200c01c401c0c001e000420592516100040c0b424100030501c5000e42c6061081c04000d60341010101d05590342400e007212907685012403860f5110807903000a60079240c00d180c40c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 81942033 1250 81940783 81940801
    0x504240204080a050d08090a030c0813090f0b130b010918060510090504060b0c061f0504020c10050121060e010f02041401080604050c090103110c030309060a050112021008060d020306 80
    0xc5c030000540d403503aa4203690f03048105a01c52045003400b0b008202001005000144a04000c180160840312400f02c040d44660034001202c45070100118103541c5c0344c88000180c600468031105104203d42c050001341007540000708064407921820300c0701d181e0b19035400c0400c551074000ba0302814000d08040300003641d010004021660510405000358608400410712001d80700c200c845440096005003943c0d254440070301c020060041509903400190300c2c000c1085e40d2540014104400307074100803d0034000a45503001140c3d0189c5c00b2400201d100040c50403a183c920b00b00044082e0403400000d40c1c100e07000420b6001d0214184e50050b16440003a01040d4240111240a0f0f40c00c070a80e80d010003039507180180000c8030026180c00e00c24120500480d0059071203074002200b5070003d100001c1c10184031004071491900169682086070308901d0400003c03001911901d4010600480040d40000c41c640220b075010755001a04420002c490b07002400c55142c642c4c0b000364156001d8101c542d589400060 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 81943283 1250 81942033 81942043
    0x100c090f050303070803071815020109050f06090a031d130c170906060f0f04020703021c0512010b0901031404050606011d1e0a080607020106050f040504240204080a05 73
    0x3805584140240c0210785802d00006807400c2c20f5002e00524a162601801940c0f4481c507210703503902683c0d200c80041a520100703c0602801e144540001c41d4200b07172440c256080205652900a040d44800d041000e075010006004091a03014107200800207041d01c2c4517950a001d803403985401080035000618422215070049600400b555034011084143c1c080710b05584d0016518030103594000408283d091500203405901c45070b00a005815116994001c01d04ac0e0304643c10073b8000da000314040c6000021a40c1e0f4031800e170595442d20070301d810b00142c958040c012040c041c00c40b0301c400c0440c401380584d0007540314041d185e105a0540c10a8a402c0c50242c0e52a0b5040382d4650014044c001e9854013071401c0380e035801d110741006080c0c091078031784005040c1d1008078080c0c0840e03100c000d48000041c0d100f401d1103554040c10181e400820301e50304010a2040f072101200109000e940307024104400310b8070402a1102031108002482036420280091401a000340d4201e03180f40e01809104200300040062 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 81944533 1250 81943283 81943289
    0x7050c21070b06010c02011211040806090105060109060203040320120f0109020307050f0901170307080c010c0f050c03030a090302010b03070b1806031909051014070206010e06150705100c09 83
    0x10200002d80e54840044131203510420303009012465100f03400f4110f80940d0008448a085910003500381a9900c500c50b1a00e58203540302c00e150795480c000e121403941e001403614007801c0d8070300095103070625550311800c261840001034501b01802a060160643d80c820482d0360b2511001c00300d403a1004140c81d064001c00c0c0c1c4e106d08031321a01c95501e00140a050040394071454035802080c05c403991386406d002000545511034005058003040081000260286019117034558002c0c0001400004542000d4074542b096120304090100910600300e442c00c00004480e4001c21513040400e0184003440e05034090710810340b950b6814012500040cc2c4241e28401425541801c4844003511502c46014003000d07210030b9500301c8100071035412400145520740c10a1140381d10841c1200c09015070140c00714219021980d130341a01c44e1840003800813a60b41048641c0c09001c001e0a4544141080c000141e8900940402272404800108410702403110034000f10b5000c00c101c540a001700c1424030001404003400f40 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 81945783 1250 81944533 81944543
    0x103062c0106030e0705130b1809070b030408180102070b0307020c010207050402070506040f240506030c010e011b0c0305010e0c10050705030a0e0d0c09020d1802030607050c2107 78
    0x100000410314442c0c000c0000c0e04d09860b001d840c40c54144014808260400c4030031800c8280c4910b640d1000e503d5061814180c580d294401c0c0501d810701e40a09800d02801b5440304030a9242070080c0302c04260890200d5920710014a04243c50783c441000603400c003c9194403015044201000b004111f40c3c0108400455074402d80c25122241d0700c610403c0102e005c1c0f920301a22a80c8258001400203640b00c54188004d8000c40c0d103180c030050303100048401c04170040e040d00c114940300d000340b001c02d050801c6850594071007420300850781c02600c40020139000c46609943d82c0480780720440f1040c801400f449001868010000f4002c001e541120325035201c1004e0f800d40d009240900140300b410740708405948245030f10001640ca480c4a22100300c0d201485044100e61084e01c01078640c00113210000382c000206581000136131220503085118040784c0740d2105448441607040381000c0141d502194403035008481c1c3c10400e454641c2401120b00c3c200c0c0300042c12000340100c0d1071900110a8a0002c0c0c61003911031 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 81947033 1250 81945783 81945869
    0x50403030203150a15141b0a030e09060906010f0513030b010602070b130b0304032606120115030807050712110405240f031006030c1403010e100506010306 68
    0x105060100d00032a600c07a02c144904810300c018940341c412800c82820396154010a407c02038982124030211203440c00c0d40340140e10030380108081513086400c444c5640401c4442060038075000d00411140704005145504111309242a002854051001d0700c02140c0340040c400006610fa1600000000013805210054072480400081454948007100c0b00d0010001404292620340b0140003200e82010340100c0601c50102c0f80721815101544c208100c12149140a04d0b02c3c1c140001444113030300010b10000c0b1541d044c46000c1600d43c08142c1d038a01241d03230207607900390386904a041c482e060504940048692000d01083c041c184140902c07500440300c0b044504000a4a8400500752513074049200143c09510107522824185071102c20080c3c551006410b8400e80000b010781c0b41c00700c81d003582085a8040d01c01e401409500c0b5144203040700c3c00c5041d00200200e050071a5a0f03a17650341300602c00e8120710785030000251641d20a402c0b800c000c0c40101c0c4000c2c500c034060b403030540159581040c0c0b140c0207040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 81948283 1250 81947033 81947071
    0x26070f02090c0f180a09020c010c03050601090b040311150a05040303120b0a0312020109080a0f0905090609010b03040f080a0309110108041101050a030b101e18140102010e01050403030203 82
    0x90710440780b0106184200f207160156034240c81c1125000030131620ba00034a00940040e601456000601304120100b0001a20401100d4003408880005d485503040240100007442003d000d5811101a40e40060070306840140d01c1000442290185801c602d0380d034070100320040e000741c0100190040d02d1003a01d400400250f0f04400c042294180c1c44141e521203043d1030304202040508041810741c1e210b0744008182da021903220030004cd0702c060002000114140031049180c0c0c1d002200b5409820102e852111504101c2c0010b500424180102c150865001000c02c042010306400b03484804e5000ea5030b07a4403610490000340081c03058110550703164102805110341c81d8401e1810318815a031001c42240d44100d120011599030304030802c143c06155480c0344103c800e40e00d11040c04c684803103030340d0703410410307588040b03080c0d00c006840d0402000d005500c080c41540056850491040c3c54000080c00c0301d1190080040380580401849504e480d460b00c020310040c180d154004510031820010b8031403407400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 81949533 1250 81948283 81948301
    0x807060806030304030803093f0304081e0d06030602130905040b0f1005040612020102011506020705271008011b12052508040c0b031326070f0209 64
    0x30304942156041e0010081400019802c00103103070045844005c0341c0215094901103003101000003030441c03d54600c40035002d4541c80f40e50040e980b03d100d403141541542401d5a503404035003c0c8a00d90b08440000f1195400d40c440b0035019601e024400301414370009689080c000e000390301843d038040b08010040c8011520b036505000e0b640c0220f50000c0b00540b01c0c0e4496001c481000c0d8007501e6402e8000300384c07100181540d2103010b51000390401c54801a840045440060300b120341d1078802003804200e01908000c4c098010400c1c504a4605503100041000e00306044288165074240001c0d52401484c00c0c404113900300b5908d2026950134100030807001c01d500c0e40c20f62a0701c2040fa00200021859003220911a0300c503000700c2c0e08442c041c1d50511441071503151002c0c40015041c0709030000b1b0104010001842031040c200401440500b20240c510304000c80703d181070011611000c2d02c8030600490004c910341d0401c1d11201c18043c510078036900c034907441c940320741303540c1c00100c0507031040d42c80310f0204450351 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 81950783 1250 81949533 81949547
    0x2010b04090201170705040504090b180a03170603030f0309030702040e0102090d060e07080d0c05070608190203180601120b09010c090e041e030921021e040608011104080706 76
    0x1d4051316107015104940040d0745140344010440c80c10000184000101910b59000e1895504d12417a4180c1d89071810480c1641098081c0441e40410340c0000410004260081c2e00c200038410003846079032080e0380c0c2001081c0740d441248010042208000100301140c00084050309402c2c0c421603003444800e01103400d05090340201c1d600e5950190b55290399400085e402d9011054510100d0300752860341c0d6590040a0515021105000c007203070302c914600e82000000d01c00100540f205051410440c1007801c542e00007503c2c16019040002d50000100304c4035002c0e808005d14070001001203c0e02c07581c46201108180d200d4140c1183c2c00407400011410f425010701509024410075541d40394054503014094890100c00b0f0801c0c0d0740782d0030700d03071502081e481c048200e02140384c00307500c41c0b01c0b0b050300d0003a010652500c0d0414140e400708840d9030003801644c070308601c00441d400e120014806200148005001042e80d984143c00300c2d03281540c510802803200000e80304650034002560901c0760b072400c00f65405 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 81952033 1250 81950783 81950801
    0x42304050408090d020f030a060b0a0e0708061201020c0729040803030a0c05070501050a090b0702010e0c01051809041a01060503100e04030e18330f011b0303050702010b04 75
    0x220b014000075010342419540b0301c9107240000d0414080405100209040c6140c12005813504c50315000c4020711820102c61041c001d0a41d100900c0b081c0c500140010103004001c4c01a511443d2607034913100216400b501500c60041307500c01038420050b0b03541c002006000700391348103c115490111032000881c215005940440d1901009586150743d00044400100006414041407103810700c450300101d4000d00c0f580d40704806034040014010503a0614012848005203a0411a030501c600d8101c1c41c04041030400044d803003802d140792156071410300c0c0c15243c5a407424072500000e00400b044180204102c2d03130940c0300c4011560003400d0342c0f2044119140d200c121660103e40b409520304110072440c160500ea802406490a003090925090020703144002c500d2840120700069418415982c2c5804007480303426054090103850022516050302000d1000219a03104039103001d04200c06901840c05a6440c0b5904691140c3c040868540580100800c0d0746042c019841e0003004005800d03c0c0c4112052 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 81953283 1250 81952033 81952043
    0x50102060411190608040302100b010c11040f020a0215010f0b07080c070906090f0606020d0e060702030f0109030f0215251e0201021c2007050307080423040504 70
    0x295911a10345688207408403103459000f200205010054003004140640500b40942c0e50030380341e0615050091030040c2190070802d42519001003040b00b603810042c100030140c0c4c44005600501e000d070000074002c21440d072814101d1400040c03d00510b607804034070580104685040d05001da602c8207424040404907008844100604000c542c01007000f480203018080c6008081780e010f59103030002c500c141c503984e41c0a82d81c45600c401818445070310ba809594098941480100b4141100a500070800102c3c56030040c02110b00103800001d5403803e010948070081c001c0024000081c43d450000e007a08030000701800107000b40e207400684030b03003070f0400305001e01480c01d80800049600d14a22101008024095090080e0003414214540402e104081c40b64030715000103889141561942c5207504030000000c450621b04440c070f451030104101822001c03641c44020549444452801c80d245119206020307040e042c010134006508030107440c22201300300c0e003072030058980e001940502055550503580100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 81954533 1250 81953283 81953293
    0x203030304020114040503010903090320060d0b010909020a08010e0123040518060709090612020a0b03060105040906180b1207050f030307060609020a08090a15050c0d1e05060406050102 81
    0x8003541c40340c000a00641001c413070301850540c0d240002421116901d00403808074200c0310b810000e2020840c014100c280c03001100480200350040014a14400e203070b2040070392030f0760b440b1007400c50740b0521a5030080c020580c400c41d501c186400303001e848028244074100002e641c000011685401000c0031b84850003010404400040d102002c10019020040c0001101c2240440004081d03904000080c0521619101d01401c03904010000082c1c80302908440011050b40b2802c2005031140741304032040301c0d0455019502c949603940100d41fa0f1003542d11807551541010408280c105407405046800c6040b61030030444071641400303001e040030407144810f441c1e400c44e40b0204018141902d0440440400074180d031b1802c501941d90000b00c80c410380021318200ea000c13074010070300703038008024039003222000e40284864000f03540c60607074081e000710008014540b240e0110326100003050507114020340444c0b0500c0803082d0740c000199104407598000380000d08140c04512141090300c03543c1e09444040e40035107 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 81955783 1250 81954533 81954541
    0x606010804080f0a110d0306050d0204090309050a0803120105010801031509170a02030705010e0703120f02071502010203040b010b04080705090603100203071d060f1920010617030702030303 83
    0x145100e14018000d41d82c03108100800048500c038640245601d8003a81c45411140224900c21483c1c000030545032814146011410f115a07a240c0580c028001e0b412100480ca0102c24501290a1200c2d83e0260b608070043c040080360340580030020342651444d600c41082e070b980c1c0c0c0324011107107131000f840080c05102e42c0260354103120702c85401400c1c8050117006001408202d000418cc4158441a03200740140c002180106c108602809822610305072100203065182c1036440b81d40811490017025400d12900d00e000c1185a4020b00c03500000f401c034540e003201040045040a4080c0d402114100d9071440c02c1d00001c604d114145042d01c05072040d96000380601810320041c03244420010300b8036549441b0312a118164102d10740001d41c4182070582d01d4410b803000b160b600440c80e42002540e944903030000c4c05500d2420489005071111068143e100c0301804d000080c00380c1d91820585c0a0602c05251544108880b1805400c8103088410082c0c1250300154040c51fa01d860b4010b4207402541504200086 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 81957033 1250 81955783 81955787
    0x60621050c031f030210110f0a0201050318070f0e09060601021c030209010507020a12021e130b010512040602040f0f03020d0803040c090509011b02010209013204290c060601 76
    0x11981c0a0b880510180a9840c4e40001e598098050f140c8000a0a0a1f4603122801c0d8240300b5402116014001020080003035030002c4c0c0340f0701000b400000303802d03503401d940341000c9410442c81008102c000d41803074900f91500c2514410301c204440c51100c6c0d00c250408540d40354030000e10a40940c0c061000d040c10012040740c120041d51000b50010b041180c28070010700980d403100d540c00000c242007154082030207240e01c10701080d90001d001c203901c0841c1d0003c85c602e20392900c2218102d96404024000781004072080107a415008860740366030420982c00030001084941c0d4001c0c410754548141609000d641c0d085400420000707070200a4000407021034800c0020076850146400901c6031065592064440d803400f8121034085400d1003031603449040b141118000b20f003038503960284d01c0c070081d4030b8840c031080040d141c5204117101110561120070001c101820000c51803410701001d00d09141c2d1560740d007100500310320800c680c010005082c01c5100c00724404100c01c850001c0320020141c03c050740c0e00001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 81958283 1250 81957033 81957061
    0x201031406032d030c0706020705010c030507022b030e0103060503160902090609030a030206010f05060301080c01140f1204020f0904120309020d0f08030403090f060c020402070510060621050c03 85
    0x703104501c1000354164010304801340098004090003074010420246040c0c0000c0c50070100303501c06418802414540008203a1107402c44580d43e40646802101c0202190004605d840c1c514040e0031845941c1140310400d580100700c0501500f090f80c051091540f10030800d5214806c100c030882183e560484104000c1c10a0b40103030599900060030981000f0b071210100c0d00345012681c044006800c888014808220080b00300c001622040d240141158141000581c0da0660209031034103010040a5011815190004aa6035001e0903c000341e221001100c600c4400c0809075022032003046008108000c604040030000c4c480c90b000008412148900f000503001000c0c10720080e6040366010a1402c04511004141a41c8620030071b1065624981800c008000c0d0b0000d4102c0710703202101090800420f42d01c02c04103c0d00540468006130345003210714000d441c04080103034240002d41405800149540c00c200c0c0100c00d40d0451445028202c3e074074510404542040307940106010303081c00411010f65a0f281 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 81959533 1250 81958283 81958333
    0x3090c1c0506090a03170c0a030f06030c1203030b031b091306020f0904050601020c03030a0f0e030601090e0f030c071a0d110d0e031204080f071707020103140603 71
    0x105a50680c10325880c1e0700d04090741120400040d51001da407110405a03c00c4820401e0724014120388560b0425642c00c1c0d0140c818100324008046d12021b0080c0114181d5015a00541d400442a494181e5034008050b55075000c44007071340400c0c90303d40092840c0c100421401405c1001504000321404000204201d6210182202d82412282001c44000415074401401444504074969449200807020001584c0c0028942c034115004044041e45e03540b0000180c130090555400e0400000349024000c0b01d401d40c1300c640040c0e00d442408000200d100b038036442078131031071680c0c025200e102c1c42e03224460340d4a201744036038204e150380030750410010300000036a010032600c40f800e6800e181c110314240f00d0094078005606108504e0b00000c1c0b1804620080c4151001c182e9440051410a40d50004c4441c0c4660010300142c1001400583e00d8042c100c040110350109a201e0b00c425589040c1c0507a406260b00035644c00ca0200e850102402c401c0801c9580180c030411004008210034400c0340309071031544050075 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 81960783 1250 81959533 81959569
    0x60e0d0f02151e1314030301030b06030c011d0d06060909050c0a0e0703020d11070c06020715021e03091207090b060415030c02010b101e110706110703200a080303090c 73
    0x149081000030081030f0001251700141005540f25415820150400e4401800d000c4c46644801480c001070791f008041c0030449840044400c45480304100403d404e80d8400d40000e00080c41c0c4030021070b407482d40742d20441c1340d1030041c1c048076500d0107480c080c080e016826008008101c80039800083c0e56034802e80042000e54182e510100e010b803a900404091134104460854481015181c10310117103604122840003070080300c180d64881703000b203400a507c07a0707040c0e82045034806064018400c41e017810030440c0c4114001409103c40c1541a05841d500c828050254240540c14511585241d1a1200550781541c0c0607120390b1000350349065094005044100e105400d55403140020000c81d96082250349414010343c68402400b2421340000702c0100554124005128007071680da8507000707001039140155107560400c0c1d2103061880003028548401544000c040010f044c00d180180b03003d00b404415082001d0701c0110f89580c81d048026200d0204076100c1c82ca5600440380505607142c000540c040c440200 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 81962033 1250 81960783 81960811
    0x601030612080a03110306010507060b0f030a051c021507030209011404060f030b030a03091a04080105070504030203010b101b1502041409090613080304060e0d0f02151e 74
    0x18281e5403120a40905081d5408840829001d01c100d4150044032802c0883d0b01105240d071070034500107006030040320805085155104110180c903140e1b08058201484000d0031500341100da0f240441c2d40b810110f00f0320902039151002c20308124000138013944034201107141c000c102c1d500d0660031802504a400402d041019006491100035a0940204094026540c511107a9801140003a058076100c1103018042e5000203490720100364485e020700103482d005110714074044071700d0704180440d004640044150354039184c280a50f00380c20200400842c0e1003500240030b5000200c0070050b0388950714084c0004213105a040b0100006d01c3d124a0410b2407254090b070300401a1011050102c0e0059000900c0c03401c0c2c12030040003141b80c004c02d4164007108100c01040c3c5450281c03907140e060014124000c00500011000ca000c2202a030008840d200890341120782002104e007000300f80100340b40d18031016000d020407030350404100c8010640f1071880e201c6450a4042a44041c124a40c402800c3d83c4070790b002 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 81963283 1250 81962033 81962039
    0x21060411010c0c0e0a11040e13080d0227100e0105030a0906050114040b060301030f020904140a12031506020601050f030a1b030c09060e04020103050a110c030301081603020a090506010306 82
    0x25148040541302012466909283c0001e48104850446003141d500120a00c030420652030300240c0140e008404100d0031018001074506120140502c410518405001141d94200300042120000d0a4802c90005051040381c4200380984528460583c0e40040c07040f00c41a28907501900003150040490b10380016000c03420b4891800f00c031804e0708504404100324058144520702402521440d04e4121001883e5514685d2541501c0390304c500000d000e64101000503003401508942c414420070300d64140c4a2101c01854941e2103095068200c0780424605119a5410540d034800c4c20259003480c2c00030015079090000b082002030305600704a605118403010100000c0e607607220004055117502906a41d541545444c184090040d0003811440e46400810003450508000046c2c00580a00740018181c8503c003141c8003822075902504a1044000f44120b00040004010350407116024144d4064103038808024040b11514803000c2e500000c0702c581800400780315401580c1201e41414005070f490340d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 81964533 1250 81963283 81963293
    0x50403020c1f14040807080c100306180b13090b0f0f01050f0105030901020708040f0614070c03060e010e070b070b011a0f030c09030a0602070b0a052404020d020309030921060411010c 80
    0x8281c1e0400896900b0404540c000c6080c021051000285074ac00c0c01d01c03000307080015103000601004500c01c28a512003408021035158541c2c8110210001181400910440d0500d00c0140c82c068a04201003810040007581c0c03900641c010364182c8000038029808480d142004440d9900003601c00100c9550030042880004c010300000c0004069071501d0418280c508039002e0b0000700301c1694044132107803c01501d80080c903149180400e4a61010000664203a01c00c011401032401c801114802d00c16031340301041c00c01e0300d10041d250880c865084403140d41c1e00c1d0b00812013103903480c00d080ca254200601061200e21503001c0510750140591003000d0408692100192400141600503108680d00149281c00d01904055603039010000110921030381c101480040780300c0880840d10441c84402441e81c0aa40c0d50b907404035140c020800354155143c3c1045036080352a98040f10400388200c1400e1111254085a035058020304141c00e00900010354490320f0f1080400d4240e203043d41003043d8a01c59000040d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 81965783 1250 81964533 81964543
    0x3030318011b0908161a07031809022703030409050c070b070e0109080c0d060f02090a03060204050406050108040812040c05060307030f0c02030711060f1c050403020c1f140408 77
    0x16140d561400f0510340307400480ba080410400146086400101c0c0602486440b02030304159210f8601c0490381d541020f01381100c541c184001c00405824150100064500c95034001d84610720304070043c0c61120a81c40c0a80401c481050300484e05a00103200822549070309500c44c075800644032501350325200c00d60f51611042e110071201342c0040f40d03c00614040f01d581c000058409450000c0042181600c20350000782805041100140020307107409254801b16540d8041d0b54140d0009001c40c642c998907850303e100039401c6406410b001d54a0554000b030303151b11502407030380603035081031013140f03001c1020000c04c81800000703206940d101d0b0300810000d070944070b40006600c10901303550000f80c1803d0643c03101c0c1c03d0350300440318003085500171301c100c03030200e81c092107448034000040700e40c1c0355600000c109a6155003d1160f1001d41f10303080303030b61007240100a81c00580c0308034401c0d4242c1e400b0465010800c0340c2c501d101c1c00e030f00204204075500e2034101e6004d401c004802d11140520141460740c0c2e02d601d03d20384 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 81967033 1250 81965783 81965831
    0x20c06010302151e0d0c030b01270f06120b0301020913050a140103061a030637092405010e0c0c010902060c0c04140103020105071b030503040f030308150303031801 72
    0x400800200004040940e2060210000280c1fa06001c0c000420000030580c4020001041894000651183d590046001910014903480f200024815914140030f07040d4412040d001c01c00504245c401006881e0610842e108114000c020580b40d0103006800001004024000128075556941480140f4152081035000b10310410380031498040fa8501c18000c2e84d0060781c8603010f0761254041c880700a4079010751510910503103507140c81400c00f09a45028103602014416499444d21002d88280599001c0c1c14a5202143d200e0268191480c8000000c44009104103240c0d03038500008211b4141c03020004000b806254000403424003201e40009141764000e40c0581c925921020100000d8281801140600c0404d003040a00302d62554001a2640c841c545005000c2c200c102c080c00b603038482c150428000343d50010204c0b9260394540d014001506e201b40025004180b07414001040c6842d80c103081105460301401075400c68a481c02e43c540c2d982130b004954000d5541ba40300810551045a40f40001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 81968283 1250 81967033 81967087
    0x117030d090b041401150501030207020f151201080d1d06090a060806100504050904080c250303030b0303130303030b061b03042c0619030206031503010609020c0601030215 75
    0x6076083c80d01d00004c10100c0c0b01c54048951341000040c080081844c078024017140e90070f0070056503600d841c0c40000d8040010207250f03a40400382c602e10b00308410428000d40003555240c01084840d90701d4007210f0382d40e0714101c0369100000d2143c14207080c000003491420480000e0282416080c02000e0700000c2030740005030800300000d00c00604004051a00c0c40787c3c0d5007007150070308100740b4007410400454400000108058003007100090380e0b500b9000200440c054100300410039858000150b4040c86ca001c907e41b00c203800180c10b001c82050780780380100854001124003848401614615030f801d070050b01c89643d16a50011090001203d22001c2e0a2940801496035000d150b41c0c1d410401d01000300c1040c92001505624020303140355910281e055500e8200404441c1501951902001d01d020313243c2a400003500a60080300307008100b001c0c6125541c285a04400a201c2d10345c031000d000c4c080340520301c460640342d03000e14010009030401542080160b0741240705280340162513411049400c00d5002c01c00c0e0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 81969533 1250 81968283 81968303
    0xf0d020a0f0e010e0d26120901140603030a0c080c07030c0e0f0606040b092b031d03030703050315060403140705010306030804090b030c040c030c0206010b0406080117030d09 76
    0x812550300c403a0442c0002c0302420b0209401200e580420000076403610001c4c02c03001e00c0c0d0303071340400c40310141c1100345125002c0c4032041c0c1c1d403010409a40c9041074152655000c81d0b081000d00c3d03060300200180c2034413504000d030017181041c1c50b100085030701c0304548000b42c524284c100b01c0c0d00d403502800d0140310040d5000703980e0b0b00d019a01e05100803e007628001d0443c2d600c01420300611100742d450004603411200d0307641d1441c0d110454180060f83c50308480c4819540e40781d0081c100141e00c494211200c40c0c00340641c480c0c502e09045c0c60540c4028040310300407181e15030010011140040d0240f0081c680099029041c59041c0c6590f81c04500030b41d0054000703580c075005183c0c20900505003044000e01500c000c1c0380500c031452440da40c803403190107075019840d02142c407000f074080c0680f030800c284070b04031400400900031300d0160000507000700b60002041005028280010500301d220104840c100c6026a0325104560b2800311140b00c00c01e50044000b400d8001000340d240010050b00940a0f258010300342c0039 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 81970783 1250 81969533 81969557
    0x6120105090a0516050d020d1121010509061b070303090c03050a050f0c060f03060103090b150f0111071a0408011e0b01170f1005032b0c0b010b0f0d020a 67
    0x13440c1029104100c1d542c5a00800240300700c2d2541c000071080141d055641c1d03000f843ea14907000c3d400c03802010f440368005030102c035181d40c0140e41a11038800c001d1090020001e40d110351802079200c1504032003150f0003e00601304107003400030b00002010403034041d02e80000c400329541c0d500e110588541e0700540781544480b8014041c000148030034001c1407a2440103111040740400810f804d40100043c44542e03c0000c0300140f0340746d02981213103c2455004030080850f01d066203039012003030001aa034501174140c4440003c49075008401241070b007038809000700701c400d2418030100e142038481000060704040502c0006020f075402d0140701d0311a01d020001a0400d6203100085c400c8400582901e41040600c4005010842205054941203440703010404030b02e540307030740900c3d8145485030f00c15500f52181d441c1d0001d208040c9100d042d620a0f0040340c040410154410407510351200c50000f406030080301004000012420f13004152040720550381905106001c8009400c982005408a010650f0f0403655 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 81972033 1250 81970783 81970793
    0x110103050f070807080403051605070e1b160c0816051903080a080601090515090f0d120305040204090c1202010809030a050a1404030506010b070b010503121206120105090a 75
    0x2060780072034520340d903000c289401400202100b501a0141d800d1104450103e01410301c540215007401c0513000c001c04c5807012500c0c003613a5a0802d0701c1806e5201d61210041420600440000b036040d0042050450501c520000c0d40c072a202c1121074104c170074001090000620030003e10446156110703111600c00d4a901c0d20007880885a4111918411200c4c3c2082c1400000e180c5000da480c944058a0001d1003076a54100503100b00029800545d03102d03108552440745d1000d13507801841242001e80e4030000b40b605070014000e42e9910303c0001003036201e01e150700707405c901c0c482d03803000b0b40c498002031011440b80c25a03111101800038942020758010070403460b040a550700300c0040d54100c40a03400441c43c015407101c0c020a18010b101d040f10801000c00c5e65442480302d1102540e0240d40c122041c1c44042d40c3d11605d0b2410756101c2003040b01d8800d250400098103103008182100c0c02503441425070304c0c0c0300c0e002c0341d0300d207180c2401044141c1c003103860082c150005909204244c0304904034002004001400c0c280 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 81973283 1250 81972033 81972041
    0x6130e01170a02010c060903030b0616031202070f021507021305090f0a020306011a0702030303010801060e09010b01020709091a0702100b0306061503100e0708040201090504091208060307050d110103 87
    0x1211842d4010041080141d0780000594001c0343c0203040003e51a2040c83c04801800000c0f5400e58031203070100e010002000c2e114492059903101340c07601c6900301c031502c111105a0003181c0e4017424440380c0d03408540c00740c1081e10192180d94990312009240c81c600b07a000500c06007000c4881b4088550341e600b000300e8075800308082c200340c1032110020044800650300003561284140a2440b0b01002c01c00312480c1140032a0642e0100c50380203007a41d03207075a101d0654600800c0140704660b2500c42c40c0e03010407400d540610805032143c82c184d0161001c1c5003000030b40405042041e1080f20712506404c10710b4028036030f11680750f00503451a4054002000d007910b1440030b888110000600c603802020a0101940d01c0d4180c4070a0300620364850741d200d0b0755600d4441d00b0148141d10a000300c2e4400701c108104248d02c9800070b03200c2d034400d803604c01c0c8003515007042c00102c0341010401402845105203440040c0d000d620210b0748010014100d4210503200d03001b003036582d5071100040750005640e0b012a81e0b2581c15000d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 81974533 1250 81973283 81973319
    0x715080f040213022505121201230d03030b1302040506030f0601020f1c02070e0f1504060503120301050a080a03080a05040302151e09061603020906130e01 68
    0x580520541014014032148000250000340b1a030030800240041100640580e0fa2084058040c1c2c10000ca401c5859450381c11361150440d00c9000f413202001d140d48070002076072040c0100e40c8464031180e08258460500c00d03e41000e081d03038022180600740c030320380e0390102d5142414480d0340e0125243c21603005109260303800708207500070a40140401d02c03203a142c080c240c95000344910140d542c1a100d0400617030400d42d40d003142004a00514140341e030507440d00d0907103448411142e8202c80007146e071144a4143e0840507034180c6035040c1c00d01e001c14130b080c444146421401308010b000103040d0b43d482000174909400081030b00b10180010004000d10720b002c02000000300700ca03501a1149403110740d401012848000c02d10000b090781c5a0108007898400c00c0800c20140040c00e0f00003103810401c1a054003072a0402c05861418105000990300c0c0c400891541d000303101d000480c9000c40e8030100140c001c0d4015040c540e40110060009219140020310204010400f2122161a039410b240940c0c80c1c0480d0300c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 81975783 1250 81974533 81974537
    0x2010201090b011e1719110a0b0403050f060609040f0218070e1c020d0803040606030f080304050c0a0e01060e01020f07090207020316050102030a050d1407120f090c0501030507021203090715 83
    0x80e04d031350758601c046510120146c0004c3c4410502c41549088525004410380980c0c000b0740345800030841d400c44038004c02c1600e00500850341c1c5050100c1c2c8130340e5a0402200e00c6608030031203401050000346641301c540b000c60310051420b0320300d0200b0044032214a0007103c0c207400040c0ca84608030b090703082c03183c410b070020100014000d21070802500407030000c400c0402c00400c4404000000b90511689034401d102456014800f401c1042d807500f0007043c5a041500c041d2283c1c0108003009581e494101111030450342d500000c14145ea18015064648080d1000840c1c1580560100600e52402c00d20a02c0058190b1107030041c0c03074525500501d4900100420580b400c0703124182c0a0096030f0300081034881000c03142c60b00d00d031782e540e56030300c40c1000d000c2001e02001c021640ba400d0010603030300400606d80058a20344100b24206140200030306550308400c014040c2c4180380000d10a030b501c03039008540e22070000c0c011100340315680c0d0f20034440c960040b140c42400d40c10000303080c8414504403584d030141107064 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 81977033 1250 81975783 81975809
    0x41b0806040b040b1f081005151509060d02040e0403020606030a050c1c02030d030c081f0b091206070509010f0f1d0a0f03110306010e09030a030902010201090b011e 72
    0x1d035403000000b02c40600050143e61103070001500340010790103001100055501e10b40000359654002503a030741b1103009070305007903414000000c26509440f1950ba090060080c95881d01c1480c00f1032100c0e01ea0301c1750b03038042c0d04404204464500e500c21400200014103074080c03c60171a18243c1030090400d60041c001301c0c800d400120380c12020071000120786101510865000e40f2006403001541410900d03001c4c029018012200b8015076550150301c1100c440c0d0050302c901e80c0070350741d050a06c000355003103088145e41c48591110503c2503540c1080544490a005050402d001240c1c00845141960031150100009c1c0d000503445000c2d603110312150004c00090070074103903447c83c0f100080d060b45c131032501c10110260b950020a00780e944d80b02c4020001c1006100e0241d910fa202e04190f0f410416281d00f4034040d02c200ea0000034848001d4034028450300c0f410b00a941804500401140070f000c2c5104260f04644d00c0d60100f0010a100c200c800c0c0c007c0c568803c0b00000306000d0281001ca400e850350080541c440c41c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 81978283 1250 81977033 81977041
    0xf1a150a05070303150e090f16060203070f081e0304060c0504050a0b0304170c0c1504030506060613050301060e0702011a0a09020a05040e01030804030507080303040c090903021005041b0806 83
    0xc01e040e24201e0782c1c91306010444002e842c503070982640d81c0303a0150801c0200729050041185020441192046115059625011380140152011000341c440c0400581c03040200744041034008101504a601c20480d103880c1165400c40f8094000d6030300c0081200880002c244800c100d414420703800d2190090510030308051400700001c00580061080307004d031400c00070001d000c019040c038401c0b2404682d04020741d19908034803c51941c0301c3c50000c105001c0c82e40e03003801c180ca402e400d0741a5400c40341c3c00380c010407480d5900800e01c451500000d03c841d41c9000b00c607401044a5500380100d201901e01c09801e40128500f0a000070709403084a2004042d003450b010b004030464694445180503114083c601695440c1d0904003200d0b1303403045a00280034800448004000c0010b0b1000a10403207001e0800c90b01300343e440e44400398403031000743c1c2c00816090921808000d420460382000382124000d00580d01c150018a6243c401d4901c200c0c0e04070703003080d98064158114002c005a40c000740800c00018565454 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 81979533 1250 81978283 81978287
    0x706030917030606070c0e06100804051209030312010306020901080c03040c0302091317071b06090618081603060510031a0411030a05030d0c0e010c060504060f1a150a 73
    0x80c60100742030014000800105a078540c82d084440705a0b1050040e401305550300c1e502d503c6038205a4807941f042c00c4502c1c45d8084980f05280c02405650448050003407031901c42503804955100d0141c41c0d426000a104805a140204d5440c2e802180030780030141c0e4806001000610080c1e00500c1011043c00a00038000802c00500500c41540d0307055400c400c0944401100400c0e03451546001003034843c4c2c1d1054144401000070180c05003910401d51000c00ca0038200d81050059410b00544001580002080213524841ca94017803055104040c080a0310391600251428400200d000501108025004200f003058038802c5a511642c1100420f55950855484500e607507a14018043c81d4090070000c10300340719602c0d207c0e0b5075030407009003100c25200091400b580c80c0d80040f69005001c44c03170301c0c0741c2108003030080340320860740b0405a44200c0c01100350307519035001302130140c0b0a450159413040f848481c2c240e40e10420042c0b40c0d2485075181811501030402c0724003a00e014010b401c0c80d00522421030754035 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 81980783 1250 81979533 81979553
    0x40519060e01080a0b030703051b01020703021c0305070605091f020f160c05120f0c010305010b03040303050a0f0c030212010515070b1302060313020f090601050d0f1b080907060309 79
    0x140034a003e07000c54481d0f008036005403980104040d81401400000420070000007812030b41514000a5190180314010040e40c58120620010f504002c26840c40d040c814400b50100f50144d00c64181141440c03010345803141255002c4441a03815030107200c01d01c0400c0d1500a8161558011b000709500d8000390441c0a9668003a041200c400c01d2800290740040007100004140581070251038401500c82e850149035850b01401c588420601400f41e400282e54840d0160324180c5803a001480c1c43d41d2036982e812801404010301c0318181540d00c403030441d061072582c041d071400300c0220390340075884501c8131189039098a03060f4801c0e07100315101c60800a11403859000d41b408580c00200810309595410340c44d481a0f5541c0300e00030f51080001081290200c0c1d83c24051111600aa65400c08144031200f84802c200c000d5401c140418400e000803d11400541c100f401d80c50201c943c007060400010a44030010300d0400e84100210b0714900030098107010801404004000e0351600744a2000f13952038140b404 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 81982033 1250 81980783 81980807
    0xb0405150403060207050d08090a050a0206090301090615050102100501050904061508012406050a1d120604060606030e1920060c010b0906030102120a090f0203030d0204051906 77
    0x40c0c0e45581041960344041401d0740d0046401410540d03a0308000e2420f16181d501003d075000220324800f022400035080090030903070461380310008040c0f070103a40c2c013005000c0d04040070180d8190b40354a96140007447c0741c0a408110131107039090b04100740c2000d0000e400e0002c20b0b015030008510b40b0004000681c2c515502a41050f0045000203078140b8900302850501250b0300050000d60800100700c3d0380380c1c400c40841e04541c80140d04100c1040e155802119984901c14080000901c0c0681068001035406030014440c41d008101404000355640114203140d400c8809544250390740d2002c00216030140540651700d28108080d01c0321140c050182d40145160700d4010740f40900c0804006c0013400c440030f440d605040020800c546401d19038011602a2000b01c0f00c0601441402d400b1851390308050080d595a440c906010320740542d05c0b000710000400400e08140d4040074055400c00240c2c03802d01c0140400c1840c101e01695a03410642480050084045803603440080700c0c008108803a0301c2000303400b00c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 81983283 1250 81982033 81982039
    0xc1b08090102070e01180f05040803060f03030408120316030c0915090b07050d020c0105090d06180b0f0106080603070b12070c05030a120b040e030702060c0a120f08060405010b0405 79
    0xc0d240390a0040b4540101c540140c40032010540011401c8005141e203024100e40414042c011502c00e000c1020640c2c07002c1d075009044039024000700b80c0514200c20710000c03e84d400b4007103a0401c0e40d660310b04e5103821404032384c04500820010070301c101d400c841504c0c013030780070000c2c10140b102890712000242402054411100007000f0403050001e61071288084400803c8007460b0f182c2c07968482d0400701d88540781c440100016100b490071004181d40110207032a000c40d4010880c00d000ca80f29242d05000e0305800554101d401d0b84a64081300140650446d140103d58009088000d0341c1072400260900c080682140d11991041d24200140603241d000c55805000b204042805234495101c1a40c5803603000310020300601000c2000303c2e080398841d401c4204080044810711020f8a0b081c01d100444440b480482502c3d0020000340c005410100300a042c0700030713a0030898075508a00d44036960700000f0a903032080000c08500110144680c4101819000300d0121001c025552402c40c80469501c614410761f40 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 81984533 1250 81983283 81983287
    0xa02061c0b040b0a0506131a0a020d030507140703020106030506040f0203060a09080f160c150306050d120c2303120f1905070e03120a0f0207030506040609020406091805010c1b08 78
    0xa05030382038001f8030041460102c61441c00201c0c50b00c1a42a40140d510140103114001c189108a44030303008490051b83c1c0c50715130482d6502a0b64060b4416400184c05500759921483c0c000000b41d41008000d01c21405086d0080c1d118905104040c1030a0700500014460b03403c0a00fa140494025000c8070080600154180e0751a80a1a9000c0801c0a0114040e11681d0610f10005a20160b400301282c18029aa01001000c0d1160100300c900440070303001800c2c0840d107100c403103400b50080c032000c0c142d94010038059481900c191b11402d20314080140d0b03510950000b00701a0490715210f104e01c1c0e0004e10502202203a032400c40009100208401007040d070081e102d40108140500400b41c0401c82800074054034400e005203031000519a0250070588000f444080c90f8100191010918005595014018003c01c3d101c40d110303d4041c0c8070b00305007603911541d58500000daa0300f840c8a101d100c0f902014025003a0402410581e01319000d01ca03074041440b80001e02c0684241c80d480e040f40c001680181529 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 81985783 1250 81984533 81984547
    0xd0e0603130f05062d01120c0f06030204030303060b09011d01140a090e011a0a03020d020d0903020a050c0906220207061d071d1303020a02061c0b040b0a0506 69
    0x1c0c400c2000c242016002031600c001d40d80a01a000c40e8180c0f00704040c000c1d0140081c01c03a05c2520b910280101c0b518030075540d180042c00044c008900208065006485035003181c0d442d065821140b20b2aa84900d0100b03038001410805c054150003560002c2c015100100c2c104000d000c0081d00b900600e0540c0640c80c4840500700041d680518808014014400324090710b401d54140d020b848240c030760042c1031411210300000188100124100824410a464910704090718001d064010750401712465501940038420400004840e120703142819000340c0c010f01010b0103a0405a042040b8225020301032804941006229194640031206d494601c0080216050014641c0f9009000300d5038010140360802d0329249042c400e2119004000d40764409541c10315030380720490400a0300e46030f1642c0c1031004050000d050007401d506103101440c0079006440421130b0590000e031050b400311101c4090440ca4503020031540c0100d1180c051229001e640030400d400b2040001a10b0700e04038400e5911641c0001a11 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 81987033 1250 81985783 81985801
    0x3041202010f06090207020312090102330a06170610060509040609060e01030b0f07020c04050619060216140f09041502070303200918070c140303040c0501020d0e0603 73
    0x3000300071003107840401400741c07180130b250061350007000268401d203c0c10a0100042c40d0080494800ca24141c0003040b01c0740400800940c030500c0c1d00300c0c13050780d03060035030019a804944901951240e1502d1000251884c1000c81803581c03811030030510000f0303a00420030041c60780030400c059400d03121641011506d90800d1000140a0302d0243c0141a0b80343c18041c00040380c0548411260603244a54042a0155070b0703111101500d030002c540e0040181e108e450303da001401e165100c0e90308150042d0a00c5003880c40c42d4021100d0749615030082005038861640c15039185500c050300e03c05804031032002d124a0012800180400901954007441200003401050401030300114560b83d410f42108107540752545801c0107801498502062002e80c0800700c0915400c0000d10203c503001c0e0f00c01004110300e5540510000440300000784800107108168002c02d0105409500d0030031150f41140c000c5070b0341d00c0c080c504906000159402a07065521a40e04440015003104000c002d0350401c1e2907680c2c490b6141842 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 81988283 1250 81987033 81987041
    0x7090509091e03070218070806042a09150e0303031605070512030103030806040605031e030c0f16060302130b0904090c09020304030305060f030309010e030c090c03040c060206010b0304120201 84
    0x840081e04030050b034014003182d0100c00b5180c010f000320f403030407100c04070f154504800c02c100302e0360070000414540c0029602d1406600110040b01c4032415186030040f0310740004104684034841c8000b20380724400411000f0010602003d80c1c002d41e150202e60358024030b012950740c0c00007070800d10007440d201112420b440e1280003961039464211007114883e412051082065520a00081c0c00040306400051890304240c098001124405002002c1031007244030945ca400c2c2c002e11014500340000c01103004021010007814440c40c041c1c0d0050700e21103600b2200c001d01112141c0c000701c14540181f007030101c0b841c4041d03100f204451004850380d9440303c000002a00510040d0380090101100c2c2801284003050b5034043c503c01c0d40300342c07020003030340e1150b2003088641805605c4465040e8410000f051065104200745240c494000d4101d451092120f00080d00000007200c2e500a1004088100014801c201400030000c3c1510b002034806541400c000c101e20344070040001c4e004028201101203c54400d40c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 81989533 1250 81988283 81988303
    0x150303090f041a03150406060812180d061a0310050403080615190905010f0216051311161a06030a14030c060a020306040c0e060a08060604030b0406021c050709050909 73
    0x19210482d08a054626900e8021b0341c0a44805141c40004101c80f41d0010f20b001a10b01803506007030810503224401808a506500c640b600002c0036040840000d01d0340c002c0c001403080d0806581152104041803505d088001c02c00d44007142c5c28841030002203a00003000c0391300810107680303030551000050726500852103909034204040001504d044000799000d150b600541c0c0c0240c4e1070000781210170030201d03a590760369210552440955541045071749005007080340a403405a0001c10080280300e990201904004861102c401c8604807500402c400d498915044420800e014021030034240c0119540f1010581c00801c010a2004085820301041090b10b0511004608a615600d411b00c250f40285d0070a0f200e1070300490500705140003040c011504c0c1111440c0c050500c03420005001c00889404c44050245034106208000100101c1e072159215441103010b10b8001d6600d10003029201c1001c02e0b81c180583c1268a44000d011419510030b246100f242c0c421180903990380c607454001424202400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 81990783 1250 81989533 81989539
    0x16031412070302060a0b0d150b03070305030f040312090b0d050705070503030702070312170c03040201090e041208010f05180901181407060e01080a0f0207150203150303090f041a 78
    0x410004100b6900150007407003280e5002051090418220510008001c01540200301400c95400618800510b40c07204001500050407240311696070380310541503900c00c44500316545000141401409120100700c9a00c10092030300c107181d240b52000409690146039020038035a80c03501c01042103075109106586490ba0020141c950380c0c140a800a95200610300c01142c1c2e08400c55001207040d800341c0c14001050b9607102c4050740a80d43c66a01c10955400100124140320000001007001c14542d8a590f208c0c41c40b4200005200701d00120240100070140d102505404070383c00d00340580d4448007a003480845a5a0345d07280d00b0f40f074a00e4203034007416100000806150380e990001041c041c4c4441c5503e641c11b640c805484206455280c110307209622640c2c200c0c049044c2c01d0108079103001c2684088107903040310b0300060a08416540f520341c0d45608041540d11140c001c000c2c007090007900c6901d441c0c8003008800a514002c26000030942c14081c08030388502c40c80d034072150032020220114504003456401 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 81992033 1250 81990783 81990787
    0x5010b0604080c0915010207030f02120607021e010c090e0406060b0d1d0105010e0112030c06020a05090316030201020607030e01060e0112030807030c051e1207020106090e16031412 79
    0xa00c006075450444040c0f0b503115840500100341584e4030108243e4044006a000d0100e00c0c1c11505c501201c1514802308076003001d02e030b06100c440502c0a20140e8010515940a04181354170b0401c8444c8602a209540c1842e0b450032342c040c95020b800c80400d80c201c4000c2c0e85c0804481d078031800e1400081c0600d41c8080710f002e1000842540c8201c091340004420188915071041d04c42074199481d080b20b00074003545050048080060050604110902011521030715107240e003005035569000aa8010b21044030200300045009542403805001e2a410f00c48020b40880080c3e2650300003d60311b03c40600f0990074140ea80a401068240a40005000c0c1c81210001d40e11942e6030040b401c0003251078030054002900480200700c00c64031034083d103400940103036102420038049441c0060044c081103001071400000304090414103102c40002880f50841d034000003201480c0c508000d003620f420400b910116084074244240a4245040351019241c0010703c11130201480140c0c1403501c0218103014070740004c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 81993283 1250 81992033 81992039
    0xb030c04060f0501180302060904021c1a0a0603140a0b01090503070b0703110a0c03150209120a0501060803090102120c0115031b2309090c0d03030203100608010f0b0705010b0604 78
    0x100b484a282160303c20703a07800c4014160490f004503455181d000003940a0000c01584150346400e030007805141d024000b0002d5016000101030701203a40800c03a043d100111032120b0074461800e4849a4010072890a0a1040d050f2800065241400050010b01d10702d580b00c40c4074400da40b140d2025030140001400300c400c0306032070317040c410b10981120604030b00090a00c0f1100590b20300220f03880800603489091250f1090840e81ca8610002400c40c0d082c1286d1350a00c00886d0694400c4408440c00040300040c12510030320b0304029080d0b5400e83c2050784d0940c0304012103d03643e680010070354000c00e00d5200d101d4039000d410b2503030350140c90f540241017a400c00ca4540403041c0f06211201c500d502c0030303810040300101e80e1510811004101481035405032200d1a0f507941203410500c417441d50000803103040d07403903c070001000100c8000c0d10200540010b54044200580e402c0441d0001c40941000d04103c2010345c9031500d030b6040c500f598091004c00303c1001c10a4020000250040260042d004180c240c43d151 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 81994533 1250 81993283 81993299
    0x60d02191802130b07030804170702040207141005010f1202040f050c0a0e040c0906030906060e07020c0315091c0203161208060409031d010219080403050f0c03060403030b030c0406 79
    0x3e840b5101c212180b0009111001d04d02150103c0c0c2c1e00d501c0702c508555882d100c9070140368080d140c1c00e0091078200541401640c4a1009240d0b4a100c0c44101540c217000d92851440c01d88040340c0b21072480e15080051001c4540041c091302102c20040407818014818070126002d41807404201d421182072400344902104d00401a14215040796129840c0b1480d000c1040280c1e415000d50b440481c036040418021648a070b0003009019000b240d011600e01d64505030703070b000101d00311501030040c3c1187c41c24007010700e4188295a80d803e0b8854036400318ac00c240003030036140c02d070117884000460301002c0d500d6000f5000b84151225140c0c1481c01c114007a15504003e80d82e4403589030000005038842c0d001070f0640c9040d20901000c1d0b601a5200155862140ea81d01c18080c9100d10040c19803140c1805412800340d07000040e8032441c890b0141c192141d1961410502d006070300300c0e4004103078010200280184c1c40c000348440d80700c0e0305464003049a02e01c074030200c3c0c21f04070001c9040b5045810840e02040c030310 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 81995783 1250 81994533 81994537
    0x308070908071809020901031110030908030601030e0307020307030303020306120c030d0f0c17031602060712020904020d02070c03020a06020607020d120603120801030506060f010519020304050613061205060d02191802 95
    0x1034015101502c2ba4a8104070440444220050082c4251014004601d541d40320340d010030f03c0792031500122403900c80150006071602034240d20071400260004200002d50034400b03072080030815403400400f10700b9020b00001e0345450070b115a00e1304201003040d03202e05951084e10a02c422640102208040000d041c101803040d6004941c0001016141041c0d00001c0348002195489600030b950703013815242a82e0500c5010790b112800f0710354416002c0c004810700412510040072118400d0301e41011103855031052007401e031243c3d07004a0564202000b0006529004038050001d1400c0c0e1a0140c06088034441460041c0015040a80706082400d01d506400d03070005103a034140d80c0924120b5090340d45043c20450b90400b0f102c10640003c00a1003402c8600c81c060018030744110807030041d41e0429846201260b40354100014050444410503410443c0c4c072303007003c3c44079101c0c203401d8010b0141e071600402003880d050300800024007659030f20600d81218220100601c01a001000308110129400504c18001c0c1d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 81997033 1250 81995783 81995813
    0x1050102060f06030d121e06080106090506090a02030a090f060b01030b0a180e0c0d0f060e0303060f060c1f0903020c1804080309030c03040909030807090807180902090103 75
    0x5403044901140614018200c81441524000c000308170100c00380d0421580c507a0f072005400b5450f625905844440e1244020801c6c2140726808001481e0303107400025030039106980d0025611a00d80018400c468450118042c0d11882695001d03980c1d0301c80f1400c1d4802040c501801400401c008109241004015041400c083c0c0d001d87e828001c0d840b1520820201c0c005500c111030b050107901c48840700403141c031f404c0200c81000742004d4175001c403500c50100340040e5800a0494010140128290030426248511404015a04000c6040d0b103800d0000c521481d069020061040101007940c0324424000c00043c0000c03c6001c0000040b680c102140f4005000660422400340c003132040c8110041c1010444070302000c00b501607403040d94903503444900b10703a4005444040d503804208400c1d6001c20003000100020007050300b0000c1c54848a0030020966000580600104100082c0800c84004000344401c191404164402c8101e498581ca0314001c0c50a4440290040c4c100381c000418020224403950780 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 81998283 1250 81997033 81997037
    0x70606060e09060604050409031124070801061b050f0a0b060301060504050411040e0a0503130611030a090605030903071e050105060117070f0e130b0102010f0603020f040906060e07020303010501 85
    0x181c0c1a0000801c22100c204a82490b00312105020402070f03454a900720300c3c246030180c1040b4042c580030090560906050b804400d0a0b2a0100702046e104030300d8220155012140c1d2a017240c0075410808002e01c05a4ad49540070313000c0c000b5130380c8082881014006006604121421501d4918440c84c0401c0c080c00110b464601c207520707000c030000c0c590030207000b134510640d8480544061105030800f00401880e441d80701c0040c520400c081000007035410401024a1030801c0d5084400314649040203144841c60f01c6140200c0d08280111502e4a4001803448181c3c0c605080c039a8030799803a001d400340b840c000c14001410040411905101505054688405650142c0c00078070850351001c0043d10b8404031a03502da840c42d111900081c441b0341c40340c002001c0f510007614044007440205030004d03041000314008504e0303c40d41c07414074001c2507070240301d0b410720210004024014180380d0340006070341c1003a84c0010f070b00a50700c03140392008016081d8080400713800b200d54450300c54102901e0082d07498009004680c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 81999533 1250 81998283 81998297
    0x1b0c06220206030402190b0a08040c06090b0304030c080910110106090527010b06070302010e0c09060d11060c0304030524010e01090e0c04180c05060703140705070302030307060606 79
    0x1400c042400d10348190181c020b81081e140d900c444e401d00500d94403402e4001110941c814011481114200007040210349680d600c910b50708060405148110096021205014a400d81000084c0198003900da00c1505400c001c0e10700006400c1c003d110303105c0d084801f5401304400d011010a103400c40d082c2d069603480500200f00d501d4880282c6000c81e0400d903640f203110290307404c141c0740c0d9030b01508108100401d20030001c520018100003103943d40e00112000c802603511000c2c0d481002e902000003000810341281c01081070300b40701012642c400c0d03256030080d12818845840701081d880d10400c40c1c614140e10700c01c40f41e54580c2d0307041c000c0c0c80f00464022007100b480400c2200300c1606168040c14183c070742204c0640d40302d910707201c008001041c00c04100f4030f40c1d002d41c1031403c0380b50780e49100e4813016228032850050a944a8a49156501e9a640080d88152010310070351703000c20b601a420f4000c4101c02c40c1186e40c2d520f00d0b42401d03841c1c0142648000c1d0b05110005150003004400d0300b1150855015481d004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 82000783 1250 81999533 81999571
    0x90510090e0a0507021207140a060f0b0d110d05010e070e040512030c04050904110a0e060f01020127080409110409050a1a01140702040501030b060f01050a0206040b1b0c06 75
    0x200c1070319000d13101300c00140e01101004040740c0c0c101c0024407440f44030710000c032100c4000b00c81c10f07420301c1410b800070703100c41c1d030f80c0c0c1d004803a9002c460003030560b0000201c1c1c6c6888101c0e52640d9200d070039814203d18500964000d44110200102540807190101c0c06604551820b075403584004100c0c1000c807011078860007400e11100c444200d14080d0f900406420114500f000c1c1002d060040721034004006641e6210844001380781501ca41e82d888010300110f00080140e031401d8828004540795055040f411685401403000c5140e000c2d001c1804025001b03000d8143e034200350b040150b507a000e00c0c0c20480b1007510b03000c00c00e5040b129401c0107000300d4560820038442c43ea0349000060482ea11030b2039011549112500c4032407950720840712016480a000102070903c96240c0101c1c007164001d810413a038201e00f01e03003800202e28100c4200d010304e5000340f0303099103404030002001b074407044090030040c0b08940c040d0110340640102e902c1210410a500c142548890b58131062540d01c20060b5990400c0c01c1c3c00c0d0081c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 82002033 1250 82000783 82000801
    0xf070e0103030203070f230d031a010806040b06040302030d0207090501061704030e03070b0a03090b010b040305030711130504030e0901080102030702030f0c010b09040326060109060c0201090510090e 87
    0x2141200c0d015000b0b142001e0b11510341c0d40c0f061485520465044030700c0c0e8500d070843e01c001d8071401c2480001c0b0008060440701e104010302280d003041d85d0185882c412604280e8960b038810141079004806440c003045180f040340200d1524020740e0402541030040754295403400d9400601d44040721021007081c0180d99035600151005c0a03501000c070a0b40448100141c08a400b0345411004880c2c080d080f2041c155480e81040300603003011044000103511085072101740100012034901408401d15518902441c40c0d1b00c1903a03d2184d100002c040c0e204045819925079a00c2d1612a51070700a88018041172606180040c2007a11060040303104400d6040046020201442524442c00d95a00258034008104031141860380103003075002d04c95074955a2a6001d601e1359071800e80901d10a441d80e525042d14440c102034108200c2c110b000249010408028150780e1001410b4129450303420702903800401c9000403101440070b50400e0390040440180c10307190907070101050013203a40034800d544a03520f900b20b41d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 82003283 1250 82002033 82002059
    0x150f220b070503100b03010b0a080f10120807230d030b21070302102001090206070b070c061d0d0504030f120909050a09151509050907030b090f07 64
    0x4060080c40c56a000980c0082c00352005540211001482c40011682d4140c000d019030b2003604040c02d40c1d040411304112140c3c0102d03a164211000e5582d00c11980307813100c0202001d2206209105201e040f81700c0710070510441000325056150001c04036500300050341c242036130721500e0482d03003171291084480621010340b0903c2400b0308128010b008440c0d0581d8803810404901608040080c03030700503408004016603480318161402a21a260301c010010852812450904408050301ea264102200c000040e81c51804541460303521070003141c140c0d02d40b2641243c0d1100c04101c014660303032605508010342422038a4035101d5094900c1110384040d622101150280201e101c0100094900e03c501000907410581d07681c8000418600403211960b600c283c0070941c2c03419540b100c05290345460302400d01400e1100c40018502c1c2c144103100d00c220190414003803440d0b40c46410340c2d03d503849001c00c04108007070050500458000e86e621000e41000740d510f54445403840c1c0805403901c0798000c00a224500380c00d03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 82004533 1250 82003283 82003351
    0x819120201140612030c100506030c01080106090b0a110f010b0907050c06220209040309031502030106120b150c011401080f100c0507020904050f060709050a0b0c150f 73
    0x8864022911100f040c01084225071000f0070341c0340014400c3c0344003130004200074000d030002c0c41e2021a0b02d007030400605040501702000f40b03040040001c01030000d43d4020045000f00c5920b071100079541e0203000c01c2141d0b0071600580750b422500404050707809142054019840d444012100301905440c5d042081d075661060b19a8001c543d001400001c04800000f03000c030a11500001c10b00e56070003080d40c0016060242107900310042604141c051041c00f044126503080840314000031440c55041501c003811004606540300700d80fa4985151303040e00e03141c0c024030b9284080c035034442544420501e000a8060003044044003002d01d04840002080880001d40d2442401d00e03c000d0003a0b50004202d05010380198441c41e02804020081040143c1302c840009104901480c09049000c52802400303090a5020380403004104030807000b03001680c0ca000401c1d0850725040007c95946071f074082202d05000ca1281c02140b40c40f680000c0201943d8450302591241d503c00c00000700c07000005d203511041d103180b50 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 82005783 1250 82004533 82004561
    0x105090a0512010b0402040305100501052d030a051014090a170a090f15081003051c091802040314120a0507020f031c020d020106080a1205040819120201 67
    0x22804001d141030048000d1941804140003042982d20303000800d0982c0d11a9204450b5580034000c074420041c8503214003800f40ca02110001218400302003a10700b80000800f514170241e660190440d0503940410882c9805a030100650b03901aa049080300010043d41000e682034000560004110030f00c04988144116800740810300c642c071b41d00d011001c803a01b1400c820402e000700200302080d0036201210312030060500d4582c907410a80303c9000241612000382c100b0010309036003e000c0c030014a02082d90394160181500d108403020007a2802c03a89610564800034480043c800c050380c215140e60020401e50303000310065607a503282d92070302e81d03600e12250030303c90b60b40034003440038442c80d80c03060004244050006005900841c24040000c2c24101c81010a0002215141618200b0b80c2c0500c400c100c540d01030300003000150702d0070046a4840c2400c2c400104203c141d40400e94880c0e004d10155000303031103170702c1c00c46940c890480c4030000060001007059407400c245154200075a48140a4050304940394 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 82007033 1250 82005783 82005799
    0x102030c0a030e0303040b070503030114011b170f070b01031103070e06010507020a050303030a29090a0504030201020c060c34120306120b040606060e03060f0403031416020c010509 79
    0xd610102c88403007150f004260f040c001040000b0700340c0d9207000030f0b084407402180a580c1d25454107490b005548050200235060200110000c4a62201041d10343c0103103070009100d54840ca02612180504c3c0f2411108840301d50001c00c1100c1031009807014181624030600200035455201c2c0e003090f94880c2a407042d45001181c0c8000161194407502c00b401c0c145101410492141e034071480002d0954004a4540c0903c56544008511881d0040c0c03c40040b05030100d0040c0b068941d6801044c2c590000400d00d0000680717038800314007058803d5044230b01c00910035040d0303101400c10706128003036903201350304802c0004400c11000c6180004452100d00411009072400810100766440b6a0340c1c488003508101855503420300040c01c1139443d110b80f0b15003440b403100d10340d807071415190907811120319400c01e50410241a10305031075514001002030700b000030300203541c51581d41c902d8100c0141007420010642030100c101400601c0c42c01201d40c55000c4070710303000e5654220361900112260301842d6106e07035100d401 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 82008283 1250 82007033 82007053
    0x40b01030b061905040e070f02060105100203041406040509070f080a06050f0d0203120309210703020c0d050f10020903100b0f0d0303060801110703020d0f0c0b25050c010b0102030c 79
    0x900c2e001010503d24100301d800c0681c1d40d003912040240841d51400441d0f01090900c9076140e0510480e030243c441100c48128480010700020b41ea805580192f00000312103a101d00e0b2161707149004c0e600104001000c000c7d00d4900390300c004100400182281000ca00d0080106004910320300884054450152041c6803140603002040840c00100000382d030140500741c03c41803911960401036126a203604014204801c00300d010071034182e00ba100942c420f010074410040041e80c040f401c5405002d0480322003020366014100f00b82881107800013410180f0402107003000001554000d402c03c404218140c0d004800d4a410710000c0d40c80d004102ca81c007030301503060200c4921305203e00841b5a4000c2c070300021119100c51040e401c442c1e0305582085040004a8100d00b019810000d2040e4100c96140c628044030321114060220039140c0c400514040707448000480d0951950360110254182c5078120001c0c0d00c2c640c5000c1c00035440203440f01801d5082035042c0c50303194000400ca44a40729030074010042600 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 82009533 1250 82008283 82008307
    0x3091506040207050a030e03070503060405030406140f030118050a090b1b041d060a15020d0c020f06030a060f0605070206030402040902010c0803040b07030f09020f12030d1802040b01030b06 83
    0x4150541c01079080c4500004501d0070458452003901c60b4031100d950351181400c262501e90158091403007640564108000a08007001b1780301182d0352030600704001c200c00718401c000350180b0711100d41305040c0400006011190503151085c2c0c0c54403c4010421510f903804108240c45420030050140f4994401140c0b040f007103548407601c88145c200109041c6915600044548940c000d2410150142d03c01885a107103840f1032004001c103410011000c00101c2032402a4a4050512002003400710707c43c1d40e00c0079500c0c0c0ca045040d5190000b803540b42c3d00d00d40340c2e814400600849c02090844205030710045001c500620449090640060035641181d54990811002d0300052038102d04002181090100007903a000103140150f01c03c800c40500c520384030400500702d8810300a0090214204149940075850300428095120380c1a14002c1c5107180480b0a58030f07520440c2401c1d0f007464504611108502080e29065602c540308550034409144140011010f03295800c444a500030b40c20400780514407 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 82010783 1250 82009533 82009573
    0x2206060903080a0f0e031f0506030304060c030509040912050315010203040518061801060804050d02070b030105090405010e030307020f070e01061e0908060c0a020f3705030406030209150309 83
    0x1d440785400c01038100401701007801c0101050140400c00542c4842d114500d00d075029441d408401500211b0806141140017410303440d000c040681440390010780111903480740d4100448060300004400c0c1d0305501510001c0c02c60b8812039008800019240580b07c980d803002c01220100c07000100715101d203c0801c405481e031500c02414059008007103046444502042032041e44c000d2505898032840b515007070900c40c0c1084c10030350302c8608540110782c05000d0003035140d003601d0540344141c888509035640c0c0e140280c01085603451407086488080700f040386c1154006001c4001d14400c80c00d5030301082c0d861082c4080c0034000c5c0580004900640c0480d003c260a501c405915102d0300d00c0c000020f01e0b5210b140724202030003528181001c420020303038101d12940402601d865074110170f00400340801d0b0080c00781510f5031013010201e09903942c00c441e4280420090040150a0b070008180d90303586603948400b400a5001d10002070088464441030107103a05010103491040c00010040c003090700e011202e00c2c1802c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 82012033 1250 82010783 82010807
    0x110a031203020d0b0a060504180212070807020a0209040506012c0a02130e0705070c060206040210051806030907030519110906060f0720030a1a060d022206060903080a 73
    0x183e5614811510030b59114039050303000b0280c40d1034450b034403420240800c4c3d09d2060200c5c4400424010400340440580605465030312150740c0c500400280c071030744801c07400c0c243d003103402030351156103282844244803000c24900d040f81c000ca1a2548504102c22071107180c205a5548800d04144013000590414002c0c1c005101b4001e03090481c0142684503000c8401546003600c0345000110086468801c0010341500c080280005000030561860150300081c98111409298010094041b62401540004042c1340d40c0e4601c0042c11240c9070b152107a078907682c07807407540310907a200d1080214110000c00800f001800e941e404c80c0301c41c107640501d10b00380b0401070005040c807038104000300704000003c644c440251480c544648802c1008403000004d096031031842d505298400e030800c05a00001401d9842400c42d02c4000d5000302199039111030000d00700ca02c0e030700c1029422202068066080c0607442107603450007440d54504119180d29004100d5603001c141c00004c04e4031100300301403054140181140400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 82013283 1250 82012033 82012057
    0xa030b040c08060f150d020303090d2d02180714070804050a0803070201090b0a0c150603050a0c030c080a0b1f17151b03010302130b03011503110a03120302 68
    0x8059640e40401d860208116181d0742c24080704405c4c44004610a03081240c88582100e001034507a034141c000903100e2280d0200103108031824518001080355000c203145050305001c9110340700c204a024400c0286000d204224483c000201c00c03030b43d20702c510008081c010f80e003642e41c210545c24501c154000d140c7c0865000d0342c00200a000004076513071008007002c040c14008018580b910840d00c000741c50004540c001c0e04501d8400e201c5454480e90210301d01c203d0940024078101d00103030402ca80401000fa40c0c201a240e4015035081409220018442200f203900c5114a6280e240d80c45690503115071982000034034903e20200425080c001201055481d41046107218402c556540b6142680f1302545426459580269040300b41070500035150715849407004025050340075072000c00070305c64401404002d1007001c014114031100b128951054045100240003009980c2019005104842c887c0c8000c0b0381c0e902140f01c131105941030100382c40085a0384001006040728148105402a421442d007c0075 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 82014389 1106 82013283 82013303
    0x320060c0a0c030e13021c050601080f09190308070e040e0715050f13050f010e01020601090e0c13050604060b0408060f06040905011401060206070306050a030b04 71
    0xc0c0c0358410b141c6001500c44070b24040d941d03006460205508005459010500381c07210f54010040aa41c401d04000c1b003102d204803880035508c046550034001024007000ca0700300d19501b040c060300803074150182d44003426a0300c2102482807034035005400185030f1009000f1465000b25210b801c1900c11b450902c00010501c1090355500c5da035105c0c444028000b5441000480c0c8500f065901c04585413075155560076261b80c50300100c52441c02901c2c450305031103400c40c00540c010502d03150440c2041e0080c2c1280e80c60040c00b40c00400118000d544180114056564155100d20070460a03202c200c00016107801d1110500c800c0340d03410b42200c0e8090000b00000d000d4880002081d507807203d4909a400c82903614070010502409060700001e041d503003407501e25a4042440044141610501da0031104e02c3d0344da5003000c5095900b0303407141c282c002000071000e001107014042e040c0c0d4014001c991110b = true := by decide +kernel

theorem cover : BRFrame.Cov 81834533 82014389 := by
  have h0 := BRFrame.cov_init 81834533
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81834533 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 81834533 ≤ n) (h2 : n < 82014389) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
