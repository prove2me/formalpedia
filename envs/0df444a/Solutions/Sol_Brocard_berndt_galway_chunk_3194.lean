-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3194
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:56:49.362899+00:00
-- url     : https://prove2.me/submissions/b07ab50d-9e66-46a0-b28b-a3ec2e2b6dc4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 574280575 ≤ n < 574460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 574281825 1250 574280575 574280617
    0x4030318050d0518010c0506010608070507150501060e10020a030813060c03050402010f170c0d0e0f061012030e040f02370e091f26010e0303011a 64
    0x9081000d6070340b802c4080390000070341210700e411401c0b24106696003428015599a0329858a550340c80301401410140b118280c0443c220310302410680e41d64941c00040c0d268a04122140301000e020203102e20030226500c441c842c03070145884070001c0d44106281c2c0c01001c0741e0394a0740b03003211a000d028240c45003c81e4100c1041d00412907038080c03179004024680300410b080c2818400104002c40f074007c0c5004214409280c3d4805070340b282c9155422449620549803195a226a094000d01103600320030910310038200040364940c0302281080c843d5040c0c0c0c02d01445941c1d01c1c40441070308504d00a008000814503a003010a900d402e61200200500030301c00181044030110b4a0030b124a65003010421504008489501960500c1c544034144c000c07510b0504500d0300c05c080070402444d8060419400080d0381000240c012050058080052480c4460051480003084607944054a003000800303080d401c088a1003180703d400011641213403402a008415050303d500c1c4985190032000071415001c07414204 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 574283075 1250 574281825 574281833
    0xc051b010309020414100e0108070612060902220f0f091d060118110a0504061101020705120909060405010302060904091a0924011203080c0d09080d110306060304030318 74
    0x5402c069581400e90610300d810000398a506da800f056110b2064817401c1001440004004203a41080300c0c101d040c2945115a10707c011800f8100c540c00c038100701071011035000b20021940411503030520034450f4100c6596202c030888c1c01c10340800d0084444c02c00313083d4420049401c1c0340d0300003400300820000450181000980305414040203038424427075503000019440e010251440345072040551782c881d0b40e140015a402c050418001e62060606104524210f171541340030a404480310640d010f815038485165030018a00789800411049005412810005446081030b10400d4141d0341c0007400c041c14944c80b1810480903148403201103c0030400d40c00c4200c2c00b40884240e82d4040c070822070240c06203a01d101e0351200d107080180408056100000010094400070000220590380c041c40c080c1c07800d81d44d400c5400d02c1440707000d07c1183ca1500e4211120b040c4481c4101401074140b05c010107120070844442d24208a000943d4070651100041022400080c080d5005800c11050030301c00e140310340b2107615 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 574284325 1250 574283075 574283081
    0xf03042409051f0203011508040302070b0c340506031b070501020910020d0906261e060a031e032001091110020307031d040c020a120c051b0103090204 66
    0x801100c0030380c450103120020708084480030f00c1008a046045080d50b1425951440a1a0001d0503c050000d04404074003494401c2c44420080d1101c00c00300b9540b0020101c4503a41c80346551603001d2015040c4002d4900c5030003084c289120b08141c1e00c03241c61085d00700f0b01004460b60024080c1c50503000310382034040100ca0030001401003540203000040c0c44640c01005d000707001020344c03c445d00b15000030181e5940706401103034060541c0c40038175020142c51100000d000c25412084010200d8082c1e4004002c0003025081e2079401400b0084060089629040c0074440c03e0a980c0c0401007030001c2e52010650350081c407985803d1054020f290802c0800312085100720502510502401d41da5110a002d406101c925020350085201c00d807907900781803002000c001c1d00c1e80034400d0000c0402c025203250401c8405858144800c024004008022440003c070006c2d50310094840100c0326800c0c0b101d020700c945805511001045504080a0080d0074040d082c0049280b03503180b50380b8103041d610078001000d80c4441c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 574285575 1250 574284325 574284341
    0xc0510050a0e0f0a1a24010c140607120c09050d020f220b03070617060301060b191b0503071506030b0a050f06030d020c01031107060228050f030424 65
    0x2406490782c0c044c01c0c02c00c0407211104030f007181000c40458085c0800041d110307074100c2c500445014a12000c0c2d00c00ca0040b2814107600c00081c0030400b91003010000700101252441c05200f064842c0000105070504c19419526241d191101103458103108004500304261b086203400c1c4010a0315600522200008018070080d400c44845e9407120310003240709492910881340c00040840c01829500c1c905080148100c0c07805c4441e5450354100400704445440c00d41140000c2c00d259110552119140400b000d00d00d958400c80c40c1c005800d8001400d0345603144100300da201078200c405140b1f0034030307544c032170068654080b442601c3c0d5998825002001c01e0f01c04400d44e0103400140004101410300001040507240041c09491084e04101021040c65400044000f880c071001e09010900310380d80c00c52408136004201018145500000b9050aa21035108410384807244410008880340541c00007103603a8050030010203148c400c00c00c04640440c2641c100c4a0b0f480360f4000c0505210600030b005030007910161 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 574286825 1250 574285575 574285603
    0x6030c151808011506020a11120a020d08090102010b01080c0f0703090b0a05190e0a18020405120a0201030e031306080613140103020103050112080d0504060e0d0810060c0510050a0e 79
    0x5048042c2e15084c4011130100200a98030041008144030345604d031440c81c50352440340c841c004030303038000e007092000340110402c03543c000745030007804007a03420204d41c1584074112090040d4170388641a4030703035030288408178000c0702c0390041c40d800c00e0a615070701c14140e0710809055007400710760135001422400103001410f00172507556520351588505182d49520100300250f5406020459100c202c294841ca0303103034001c850001d41d00e00030b88009069500000d00c0307031703820042d040340390f615000104503000550b042c0d40714400c0e41c0400042510080664072400340689020b02d000e0f40040403c000c030310501129800c428020448a441c840461204084801c2840603180e02040a0700400035580c00d4490140144882c8100c4456000aa070f103600c3c480c400c08800d0311059a603040402c0c14400740e540812084281502292800080b07940040c042c0c003411100c444075804580c90114074584507803c0380160394cc0c040008c041d1440c0105845c8080c01c4003d08681866a6654404007400005c0103000c14000c00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 574288075 1250 574286825 574286831
    0xa090b0702030d06171908040b1b1b03060f07170403030e01060b161e02040203090307111806011d1e030c03030705030906072f010f0306030c15180801 66
    0x680b512400342e031050f5004140852a017040c101801e940801c1c100100d80400a602e40c160354546044c11050040350000d00b8000070104581030000030841208001ca039a800c21a0014500100350000485a04140c2074051b042103001ca1202c51001c00050340102142c102144080e07030f01c074038840414030200d0301a00080e8580d03400801c100700a214001c0503180e1170701c0203031501f02c481030480d42c0d074800b440c0020210720314402d510003404140207142e0030059000b4010b650303070708200402603600d4001c1442030350030311000507040882d450800b01035a100401056541020365815005440b040520014440309100d9401d140d800faa031507901d2001c031203880c1444448004001c2c001e061424503607240d0180681d00070030200c008904000309503440f03000101c1d4241d40c0c0d945680b402654120340c10140d04803a1003043c09081288003600c007070784070405082e6140380790003006c680214155003843c40050700b41403101109100b01e08000b90125124034150801d50704441c0c01001c100d041d0045580002000c2c1d41d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 574289325 1250 574288075 574288087
    0x5090103021810051509010807020a030e010c1506030305040828060c0e040c02011a03061306050613060b1905090a14061b0a0203070501140a051e07050c0f0a030f06050a090b070203 79
    0x3812000745232700b144142c0b0003448a86100e60b405884800c080440a060080003a1a0410000703800d040303408526070076809001c100e6583c07801a001e500304d8000c11400340540c1000140500000c48502c0001300d40407180e43e0780702c90503118040202605e40c0c1c00c3d020411130301b035207503c01d81b164060b80904282a500014501014001c004c00640480d0007142c440c1d00105c0900504c404408424000030350032200014158403a2400580041c080100c00b45525042070230003c2e5456415010746055001c0d00c1c21000445071801088405115626400d80d002254020900141b15203120394552180c002e0310306440c0c002488255119142030540700c0d4003d5101c00e03c0d45085040c00e00c444001044207003010100c11032001124251806245e40d03050400c04041000c0b4400042a00c0039503201e24844013542c3d803850f890802c40d8442d40ca6242c0a40500d04452081000e4101031411a0843e6084010410010700c00e03a24100a464003500340c0300c6164440c000f0300086a480380c90280205810380086035980 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 574290575 1250 574289325 574289327
    0x1e1b0105162001050f030406020d0b0a1205060105010507121d060c010b1309020a060c02030a020603011503050903040f03172a010b0301022104050a05011b090509010302181005150901 80
    0x5851003a01d1030400c9814000b40c503172450090309494101da800b01002d6200d050120311900105400b08019611105c8850002045c001040c491903000f0301a409803030341603032144015111846201d81c014103010351140081301251207a600c982d4000714010310104400c0c0c0c4900024155042041191138595544000042d240f03080584681c82e2001c1410910055080d600050808403a5114030380c01c0c022040000e400310364060020f40d0701d55500802d280d4a030f50b11006068030b5205140c0e800c1d0b0200385488085040080008203960894010300200d104c00b80c15581c1d1403041d0704000e0889520b2140030300c0240d100c00b200301d51040000f4401c60408800c907a007a0041425214142c5049029034410000389040100030386600980b0b54036651440d0a030b444500e1b149160805000001e070655191400401d00440060f82d50f110301682903642202241d2684208800407034203100095002000c007201169280a84065a80c402c0d00380b800440302039524000303e6084900c1d1184c610400c0c100107403c00c03881d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 574291825 1250 574290575 574290623
    0x8070f0905010303090e0c0c060a060e1e012907050303101e0302101b061a22110c010204030b0403120203042a0f030c06021e1b010516 59
    0x201030000003400254950748020306100e6a9010340111070501c4000200c194030a41e0072a2030120305039080307880a1030120302c1800100602c0c05002c00b901c0c5d142022807880d40240d0a584000c00f0810a0300360503902e001c0c84085000e00b03c0050380758013040d10030414507956000e009011460b0180b0301940d036a00c2d250401c1c04060444e0f402c8529500d5042c41e000c1cad9203088008440c07041e240d044e2600d86a0781d0107040c0030b0300c44580e40300b180440300070600048002c00c4225001041c01c41e9a4030321061150140307500b08985c8646a0341401c40601d013442e030a01310b202c2e0a40220760341d200b40000181c039213820319600074260b0b0b002c0c0c0c00961b6410712942c1030004042e8054410925455011021411400c1c20342d00c0031208407100d81d0070390221840340003101c407150403022007a004016200c0d036901c03140e94a01e413000b505c0a4903c107400150144070200c039911b00b41b001410340100e400e540070f480f030392000900e00b500415407114058104075090045040d842000b00440c01480d0003034000d803445100707046400b804 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 574293075 1250 574291825 574291829
    0x40306050f07050c07140f040504060c02010b010e0d02100c0803010303480303020409090303200a0c082a0109050c04020903030a05210f040309050406060915021608070f 74
    0xf004420048008803440108256007610425080c840c18030700c03040700240c4104c9460f4240e81d803180c5440d080c04100026640082255509500207210180705d1300c00555042c640718500030780218032007074440014588041805d00e0050b40b401c0942c500c1e0400e450b445580c1e042600304801103000001c101c521403207401c0c0c0035072240000402407400c1030b00780040b0100b4405090b41d00b0440100403604501090b0107901541c0191907004070411a503140d84c10018060101f900742da60a6124920200c210414140220386030013107144c85504a1000c01e80c4c615050750b00c5480039400750801e9002c441600f40019214aa40c400300c0d100129900d18141052401d00c0d01d0300d900c3d40d100751710421841c04161001710a44112a00504003a52155180201c545402c803003201c2541180b5584e008004400f2882460b650045000e56900392a854650040c4000c80e64a4001c5001103024000101b0400c074044403124000603d608c140c4410b0301c808500c0545803e0103800803003144d04001c0050091000850500300 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 574294325 1250 574293075 574293077
    0x31308030901050a050306030c120c0112180f03020307020612012409170f150f100506032d0c0a0f03051308071b060c060f2c12040306050f07 62
    0x40780100d40380003e006407145050500c14001c01000052150342c0c24819501125000782c42a03045411308100d05444010f079420340e078013140031030030b010800e07000522401c00340c4403540605022548203901c0b406030800c28920700301e003144400c01c0400d0050f00d42d5405814080b100c019183c0c802c2d41002115142c0300781030081e41425202e4200b0800c0c031941d03ca643c0408031545002c694650700106c42209082c50a1182c01000b98420307008803140001401c03095501c5455010396603142c0b03444841c4000c0e5180420301c0350b598085000e2002c83c0120392000041103851581c00b26400d0800c0344d02449050305001117810f090034050100e43c0c003132440d8202d141c0301001251481c04020616114415903404401c24002070400c10b80402c04008001e910340090a8036641440d0b0402c2e40e0781d441c440103110002c0400c2c100c503003c2c180924031103560114000c25001d0715407010001e07030100e00c0704410301070100c101b1514416403140706840b06842c0b0310900104040c6001d40f8005c5a1072503c40c0122044110280c0100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 574295575 1250 574294325 574294327
    0x6090801020a02070e1308040b31050f041d010603211403060a24022b080919060905010b010e01080f15040c02010b0f060901120f0e060903130803 64
    0x10b40c496408a02e8400b62000c141118a0984843c07031003ca4042402c14001c11800d00014003107000184e2002134120501d4454017903403a59516480300880180c1d0303d0401c4c0c45002c03078407001e02182c44c1524816455032809040010b162003000c005140013250102104085d075500ca80a10501100c2d41c40400c0312100c181585142c0c142d181ca000b0900310b80900030030322001000c0003044281e0b96490425006012103d0201d0320080c2d4648448813281d2100d2005026200b200c0d40500594003410300c8205400c0807007940b141c20349a8240c2660740820041003091a40a003078a00350200c503a10a208080710300540000030940245e1800a0841d003012100a0600074400307107040c0a41c0c0d002d07007880e40c00103030b04406902a40710a901c400b41c0f5588050801e034464140090190788076415841040382039011030303095074078080290620803107102e00341d907071070000b5840c25002e003201c0342c242c00140300414100030004000d00405032089c1800421b480c04d070701035000000c0c81c2140407a8010306802914110b0091 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 574296825 1250 574295575 574295587
    0x41211010302090d14031306090816150309020a1806030c0b12180a0b1806160e061606230702060903090904020f030a210912020402030c0717040609080102 68
    0x152909603807413009003c1106101d0b001d440300d1080c41500c20303800403e40394480720f98680b034001e49050b0b59800703140e14900c510046651507020183c1580102d91303038400501d05071401010300714050311510f081a40c03c8140004006801440704114a0013a14407407400181305040d890002d5051585500c224030883c0c051086a103400d5085020f2034010b400f0048600800800311041030605210000c00b800c0001080308100740078080701140c9046846500544119a07662441c2c04203030109a0b40c0e4600180e41c00d05401d0080c1003280c028000900300c14842030712110780b0707135034941030f2440e400d144056900108004048001c0041c03001c0d402c414140082c210070710300510300c0b42c3e8034003035a01d03003903c260b00900124040d500c5954030295140c01c090240c0d910103041d0708041c100c1d11b2448081c06043d900c2a9064402036103d04c40031015100144405c20070b101058080001a410242c003035450302000704151340004115801d40b40203c0040000300d0b4540e071078003402420154950381b0111069004000d1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 574298075 1250 574296825 574296829
    0x20d03061e05010825020307170313021309080d06060e010c0503030604020d0b0301021902070504110319110a0e030c0a0e040213020904110c210a030f090804121101030209 75
    0x40407050314028a440d8500e652211708120740644140b501a4030340100b400d40302d640303541c0800200f001c1406180c40b242100000745a0850510048400a4148410305c1d41100117107010300301c107181d07030b0b41655000c202d080c2e2a89075170140b0740c00014816619a510f2904000b2182c11480400030b0713800c24200340310482d529844a540f43e00c001070a083c032480d800140725001c00c4055003c0742404002800071074940900030590344040642c045014094812000000746078a010f00901c010101002007040c2140c0312800303000c3c04d5075074041560b480ea41d1160010247d110a0002624001081ea9100745402d07050605150500c410080d0250007041c15100902584140c580310076000365040c1c41400b680500081400c3c0280107102d0ba05034032609107120103800c28003c02c0606450080601036402d0203c1e680c80b400100803220b030f0b52002c0c1c140c4c2440404c2485000f584003803040800820041a25603299591f009654041c1d000070b013403094030350f480005009810f000100b07010310a003011403a001c0e040c00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 574299325 1250 574298075 574298129
    0x60305030406052101080109020a05190315061a071b0e0106110a0c09090203070f060e132a023c010b13050603330414070303020d0306 59
    0xb546050110010724091a220051144a40c07441408044405940c40e681c400303003c0e00c040601030f4450301c10400089880d241820401604c00c5080c981804d4491841c1d8604100c07007a5081071020866031007100042c111446400780442046180c40c02d643e480b010b150076241400b00e195400e8108243c000c040c00b041c4100e401c00e80c190340850034030074404000a003c243c40d0001a07600202035a1550100140303262075a00312092076032003201584d200d1520b03113206120441c043d10800000035260940c045047c18109202d591640e0031900c081140400c040d0076041c031815003400c4c00e03050000c080e03c284a082c4d06100801c0102c0c200380082d02245000746250340290014a201c42d20b4115032842282507a01c2540414000c650103000c0d100682c40104601d801400c00304d608501a01510710340b07503010034100f0444000d4004003241d20722181d00d281c903a450388200081045960b4801100b82200d105410400c503402184242c0c02054402d8056000800b56010741d130007001c00000520b4a0108000c0000c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 574300575 1250 574299325 574299329
    0x806160801140409120e030c120604060b180411010801090b01140a0207080a050708190f0b06040b03100f18261903020408060f0c191e030b030c040603050304 69
    0x800e802d00200020001800500b440b040081554281682111103660070440c00c01c444502107080e41d1080c064001840185d01c0382003070010f50368000700c00007000100c031a841812a100c010340355514440001500043c65001a5400d40b9000da0180d5000d2556038412140703409013080344000e11040014600207803801e10f00030b180440c0c1445c0410200d81107482003110000402c0d100d8100c84c0309004a0400030340b100b8060003041c255011b204400c1e0211020004808401030340502c1c2c0704441c0c000c0c0d8546206200c009404a64055141c0c81003510380d50302001500320f5a403054400003540c1c0911a1027004035100d00c0c01c0c03070341348201c007080180102e000c6100c6203615200d1000c080e9140d4040702a40e00c41c0d441540c00003074650a10340c100340b2480364994041c0c41910701010844040351112000103900940c1184c0205511108201007421211304030040e170f000524034281001842c494443c00740700079411404000000e83e0710402c0003010310b02040581001713202643c04200301401d540f1040d072640704138 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 574301825 1250 574300575 574300589
    0x406020c04092a03060e010b030d120902060301060e03011406060702010323040b0a181e060b0429100507170c031c050901110d090201050c01050c040806160801 70
    0x205180707001e02c0010003900d240048065000d680b6520490b1071010003c8150005035202403800c48400d511007414030903020b410320014010825000100c40480e00c501c7c03440c0c110a002a1500610001600c4810296028007201c1e03d500600c090b56406240c02c44500d880f40383c0c0b4090701c010622a103912020200c400050f0286000314801c4062580d200c400a0380c44251341100c2c17038080c01c100031300003004445401661024030502c058520351088040760002e50401405920006003803518004081090108046c0703e403102064400c0101d001804603000c50b2403c0a84034622400741520940d0240344504140f002c55201c01c605d405403800918500a00c00000d013410303251044002c407520f9000507640060912001c681d0b4809c098031180e108010640490130a450510340404c81d03106c0c041c0603c60807607031340114242c1005000502c080c060320854a0582c1030010411446402e0030f000c0c01024414280002c80340c2c0e40e50700e040543e62400000404450200d4450641001e4459001840c02c0c1141d0745 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 574303075 1250 574301825 574301831
    0xf080a02070c080d020102120702010e060601030e010b0d0501150803040e0f090a0506090109120c0f0b070309020303071406101208070204022a07060908033009010906050a020406020c04 81
    0x141c0b50140002c040c0303410008103840341c010251001541500200703240041c055810200781c0341c0381d02c181c0c2640d4038941c0f801082e40022000500c1c551091340083c111900307050000c00c1e061340060100b451400c81803400c0e1142d0b5129031300441080c44c800c420b0001807060300b008501d482c1c90000e81052040c0d003e06a0484103203a20301080c85004100149076410f50001c0640d20241040c12646000b020300300004c440d4100d8680480940a0240d00c0d0621402d402800130111400f8503503c403045e192008209409055a070384174000941c80401c045c11200b0710541100b03010f490340c10300a515102004100c8002c006c0b040740c0c28401c503407521100000c05a03218060948034442880050068000c0c0c140c118080c0e01144000503160050114068100744441c040e540c1030703502c0f10401c1310440801e01030301034958010400d82c507000c075506104003401c0c221003507000048106d41e800070200341c0c0300b5245048284c0d162482603041c8401803040035081b40210804601d071a11b8110b01a441d00c103c000802d120715030b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 574304325 1250 574303075 574303087
    0x50705072415230a080d17310c120c0905180703080702030304050d200102010c0215042a1401020309011e0e060408072309011e08030f030603010c0f080a02 68
    0x4d0300c00c851009404041c090314801c80404800800e0004000b80902d004ca074582e020a08103d0021409480c01e240790411020105030154580000320b02d00c0c108803884030351900d00252216207002001c7c4828400c69854005e6072600c0c906400351003014048001d4050501918070310783e01c000441c441101d40c0046050b80360313034640c00000d05600840c0c1c445d42d00a00e0301c007100c00801c000013600b030407020650b8044040100058004900303d1b04040d0901025a1021060300c540e415032048076a0310611440c50340f0003c42019541c20841660454054104043e014051080e9a08a810310800820a01c000c50a00c41d0641c0003e1003800f0700c4a651080c0000115100801741c0318a440304400310000d0003081c1d0b650703611003a19035034410074403a614540704000d1880741c0d0380502400320022036100419035a02642050514404010414170130715044000e254005003206042c07010701600000207010310303201d18045061509403000d181620302040010f808501c51a40c000d40b2668200b031f072320000142c0f212 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 574305575 1250 574304325 574304329
    0x9010c091a09010c1104050109020909070311030a0f02040b0703020a12050a140307030e0a03081f0506070303180605040b060907030510210813030311031c05070507241523 75
    0x16071038440391758210b400d01c400881e51582a400800c81908155034201040da00e4030002c5044a0204001500c0f0902c20004501a5565078000510b8040d034600014542680ca00048025521929040b0056000410a282800a04001c80311050301604000c1d00e00360100000900b01c242a40080c0c0848402001152100c0c0c820350225104c950341c0c000300c420204076414007418148045505511121001d1000d083d59030750074040800711900034082609210345550107401030500e226680d81c116800c0002540461001c1c01000d01880c00b550f0040954217082040c8541020300800b15000d141c141024010003105294004c0c1c1110b09034010306060003401c1c452984914141b14010308056804609656210070a10714201240c1c0300780c4400260310b0f18107408540304c0c0111044022460910301d014079070308049410041e031110442c50045d02d80003082d594698003020301403035000d50059000240c1c07031040f010311900b01d60808080070505950700c0c00343d60440c0503c0381c5614000c5422079443c070380c00e66 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 574306825 1250 574305575 574305593
    0x708030c0a091e1509080309060f07150504060f050c0a03050613020a02060f060a0e041b12120f09050a031712090a0c09020310050607050703020909010c091a09010c 72
    0x2528001da8400b5203c050701d841010440d00b0b40c09520084400703000400001400764a020341218414000780d802c09242c803040018540001c03031200c4000030100002d81c006546007010495040c2070490000300d0307041904101044411410082c3e1446103070800380004032078040141c0d101007400f840c001c1603903514000800d103020402815100b4550021580305100c54012a0a501c540d0070300100a540d0740d1440104095500c26100d81d100041902001c43c0200e04907045d910306c1c0b0310120b00d960554a139038004124180031b0000341a103c490100800444040c0d011544e1a00343d00c0916001c10503a0406000a071400d40910004044042404140003500503900c2a2030294601c911142c00318a84180e10907280c01055078202c9103540b0300303c004071392101d092007560f025403440803a11000e01d044c003040c04819800601e09403032501c41c2e0000007005903100101a40f0401640e400414040c0702e949018100d4001c0342c00c01d94400c01c1148412074a86031302c106556054109203400301c01d80240382004109 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 574308075 1250 574306825 574306829
    0x150b0406091109090603060f01030b0c040b0a091d0f1305011503060c140c0d0305040503070203101d0601081c050d06060e1509010206040305090f1e090c0708030c0a09 73
    0x80d9081140071428220b2010241c0001507042c1c500361040d40ea00c00c01c060300c450007120607000c2d10f203580d0f00503c0854040311000354405850341c91145400d0306e400c82ca403442d81026187c0c100080b8201c1e0705002400c840340c040c0d04c1d450040c0035192000d040c040c8141a081e000200708040c0d6050040080040c42070035000752103049441070240455a4403410404040c080c0c4000c0940460b6448012000410900044030100840100600201d20398490210040e2102401c03c1d95070384400d00c000c10250390709200c071040d4090343d0040080d4650b451540985034076041c0d520400c20b80c0210004201c040c001240785201c0c5050241c002542d08441e40c010b4230300d4058501044007081c9840b0f4003007503071030700060b5a94003501c0488a01008180e4080c00f110381e4402c4549182c0107070011004100000c2c010b502070404607030000e03c45d45101c00c1c450045000d983c29903950240c030f80d130182c051118a040c843c1810f0b8000c280c11a516180103520b80b2141c80c1448040d101d8044144002991050903208280c0400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 574309325 1250 574308075 574308089
    0x40b0a0e04050706140309061f030b0f0a050106020f0c101e0306031a0402010e01080720030403060c020d1d0d020924010e0d06020c010f051003030305010b07150b0406 73
    0x940c0381810305041c0da43e99010302424000c2100c00303009180c40c0c48214292032081003540002c040c00c0d55801100d028000c0034261040460300c0700407012001a020f20740e220301c030f104001303010303440386c6044884041602c40681c800d0043d074104450204205801041c6880e0a040564490440104003e002c540c41c0e060b03160102c8c2e0710300b18080da5180043d40364101000b03c9004014200c10b06c0c5007280500c5140c402660000c4c0841c002c0303031003070440e5401200420f90061150600180400441c5044e60f00d0503034400003013245410001e41441080b1652092485803a054030060801500d80d4102034400e9540c101d000c0c04951000100c0800d9944402e40726003c030f42c1c00381031103d060400210043c401003503030b01503c20b809821203800c0c4440d4450a84d03568071050050540c0405030181d29080002e41c842000c2c0d0410b5503c40307400d02046181030103064095003154080516032451420020300b00d46041e0400250240304010301c1000c10400d42d5140340d21139a942c000944180510f000400410550703010396 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 574310575 1250 574309325 574309349
    0x140310240602150604020f0d0507020c040204080109051009081b160b0d0b0411040614070c030f23060a0e0115030b0114040b100c050708060108010615031a040b0a 71
    0x4a2401e0703021641c1c0d10012043c8400880c41d498090030802079001c0e0000000c1c0e030719018000c00a40c40c4498010942202c00c90050301c0484024001043c01d990280c0c01c40f4580303a4441d007415003008010040711282d800d8110007004580015590b8003d1031084000d01c58a4a4104222480390013041c881c4190700142044860401c681c1c8240d60080c980001402840081c9850b0400c0340605084c0644205981c6102d00d65290034103000c02680c103d00114441d003c016010300036400040d00811085001e14052464400340502030b01e021a0341d0b81c0442809480942c5080d01b01107444400254290041c1c2d1032040814031010070750102e801480c009007070340d208030b403c50b500005104d88007028178180c55880400d09244007112050109403554090f01540081c00920b41580c0c10b0b2186c4031026600e441074041c3c0d50707055515141c0c18a0304a013030304122103a9540e0441080b400507410144844d08855080900c51640c04900035000303000c0d092000c5000380e449404040351541e920003002c0140110030420 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 574311825 1250 574310575 574310579
    0x20d051006080115052707030e06100911070b152b0c050a0b070f050f030406020c011d0105030a0507180f1502010612151e050403030614031024 63
    0x2070281804038683e440c00c400f41500495a801d00111b00707500d104c4e500803d07807442c1d01e8122040f101d2020041052040603540da00c003c11020003400154020744840801c2890b80707003004030b203100301c800150f14100710303074070401141c8001011170031219030018450341209441c0b1038a40208207094503c0290f03038500a01c540305085018142100200468028108100720740d440d0b005000c2c62005d14041c0d0810f010b400d020440c0024001007818500c144a042550488000b034003455103140c015070002c41c096004030b07188500950f402120002504c41c1c42202048040580002070054800a0b01c8101e0158690b030004d085140a10110f200d0819160182c0710001e690300c1c8559076064072801b0364064910305090b03030440d05105002c0c0c1c0007952011501100d11003002c0e9910054020140f4200c0c0f695902c440e403a00e801e4502564042c40c2c4800c3c040c0c0403c4614041c90014103d03600364001d101001ca001d065140c664800080300a003501c0103040c00240090303100c10810030070301c1e151003e180b410602040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 574313075 1250 574311825 574311839
    0xf0302031209011a01090f17010605090108060f0906011a031f080a0302070b03010e16030b04020310080f010e060a150503030a050c07090207030f080408070c0e1803090a03020d051006 80
    0x4620100480f04d110041c207010001180c0300c40b041d1007209108000280280444101a03030681c0c0c100380d4040c00016003580c0e42e00031401d0441c090b444059680c00c032500708070031b03a182241d5181c2d210071010060080c030341c10480d101e0340803820849146001c240100004035603000b8444000032444420000481c070680c2d4500f0947d407421101000c4006000c0c502c0c1c000b80105504090304c0c180d0315000c43c02c007034580d80c550801d400115401e600004041c0c5502170b40896865510040d4050341c499403404400e1400d20050528007031440407103240980c036004e90b80c00c1d1b451020901ca42c00c414040c2d00401c42100094840302c6201060300501e0303040c040040c40d4003401c0d40000051220428803003c1e0b03001c05a0f604207001c00c0340034048000d404141d48407001c4200341d1044140a520038800c0d1007843c24003d513900d6400e002c40254100e203003009061410b010302200810109184c3e81807480c025441c1c42c4c10000840c034582c3c140d102c001d0145660041d094100272080c44100c12080c000319080050540d9118 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 574314325 1250 574313075 574313081
    0x31e0a05071814010c080f0d02070201110303060d320102130e07050403030c0c0e040507050f0307051302090406420c1101120e0a020306070801120f030203120901 71
    0x658100816a000440390a075080940304000f1100d420181c050702500a00040d074170000c80400440342043c00300590101c0705160405072005e8407444800603210405880058410075504048000e1a4010700400c21207070f680354040408a80e021001941410010f40e00c0d014000c03015848845c1201d450b00c2034410742c68150b0141148404000c80314130b01581c2c60140020500081e01c0141c0002e004110610129000c0d000eaa66507034881c00612041650380d0004c3c401514055400300c1d1640c008400c10040f1f40b900b00783c0401c1220084000e00310366403400002829000d5840c8035500255008210246d01b80da5030f03802240100300d11284255018035041d441c1c8031405040d14064040042c602c0c2d42c2ca00d02c1000481d617510001191079180000845440d540b0324518402c1c2c0e100e0412460040c595480c14032409224414600c60006184096140c0704150030031a00a00c07410420080034010048405d00d08813850201d500207410b542c40708003909080342903114030000300380c14185207000c1c00700c0040154 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 574315575 1250 574314325 574314331
    0x30106180501090b090a021606051e011a040501030e01060e0c130602060c030f060d120320160b040f021e0906010c0b07030b060d0504030302031b090d0602031e0a05 72
    0x4a020030107a83c84002c203600b240c0280c0700c9160030000d00000178081c001e0300e030300818031b540306c403001c42000d003107190303240c0c0f041d01e00c201c40c804959601c400440290602d00750700c0a02404245880e0b0000410711000316500d40a50300c03505040648411011800c82002c0d0300060141882d00708164840c548810308407a284e01c1600140d0b4110041140060480e03c04103c150095060303118140c9161100b450740601d69802401c082d9008440c034440c2400510360403030141c0c240b1100c0c1c6010038182c440c06045034500008109548d180d036020000c40740141a14410001001c1d8007125015586d200c60a201f80c3c42104c402c002500300b03001e10140824603000740c1025501c494111501101a0350b1200110303442d80307041d4001030030300808201080090f806074001d0401c84001404145c00d16403031443d9001070785d00c1900c0a03004a0f6000040c0140416400c003180c00710300307000410929043c440e201103489a00700d80c0000d0903c0d540400802c40a62440692000c1944d400404528a05003944c0c001300600e070039 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 574316825 1250 574315575 574315619
    0x6030b0117060d0308040203010e01050a1b0e0f0111030c123610022422050604061d0a050c0f0d24020f04151b0506060d020609030106 59
    0x40032038448100e1808449a100d10400f030700f5800c3e05070b5255802d840940010700120382c10b5407241d07101c03280350a0034840c1c43c0c450031070304401060011080d01e0303104011b90103029003010040d1041000c0c0346900c0313860304940c0d940c6d828a4600310a0080c08112801c500070000381c1c040038000ca00c00300c00b07a802040d025140109404034418070300481988030000c9440000e85400000c41c40e00300c651501d00d040001c4005a04883c01031380c45008035444410301b01c8036840103c000441d07503041070000110740c50040b400c071000d001e80c0c1c4448000c569103485035101001000108220f44414004e079203104c8200000d00e01001c1e804c1140c00360300451809507102c00045122a0264000d4100400c140ca0f214100582c010340180350694003400384605d030403038081c400c0b01c1c41e925683c0030060100340ea62a03400a0004215452101010810f4080010108842c1204852003404003c0d240d102042011400070f8000f581240d54200e8040c151001c41e1950080000c6507505518198000030034041000c40c0364481615 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 574318075 1250 574316825 574316837
    0x70c030209010609030c0906150c0501271e021c030c0b010305060a0b060301050a1e030206160b07020111180a050907050d0f0c0203030106051606020310090506040b030c06090a03080406030b01 84
    0x61f2452942182c01ea03105600030042c04107403000c0c1d04c500480d0354204032400f45001107090200040d4080c1203030b9004441000740017058030810b0503c80480c0e41010081a01241c0c880943d0098001500b03580050360f20381c5004400b14069010940182485420541d100c54a268a580e480c1825030700c4034800c5904004550038145488082e180c048210b078103039a401403100b40c0f15820900310b562540c0301c1070080c0620030315006000c40541d0307400c0040e1002c140c0801c8900d50090151401400b00080580190f05684c1010303c0b44024421400650740c442d18181340c01a40f9006030750010384040380781c0d44200d420101c1101401801d650040042414402850b02405112410b801c0d4400321506030380e507400103070014001070207410f1044000f400020080d0140340c500b15065110300707080341d0040d5000040d140a122082060741218015036910a400f00c0c0d040010301d10b02d5022039243d50f44044914803c00c800203841e030160740c5d8981d04030080e40d00b02c4030140e100d60710703040068014a0341903203440c04282 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 574319325 1250 574318075 574318079
    0x60106051c0612140d051b010f020f130905311202030d0c02060124091806051e0306160216080c0a08240703090b040b040c080307050a08070c030209010609030c 70
    0x150000c0c441c518610713543d4500d440c1c07d410300e1150880e404101607040e815521080b0f01610000c8500262220139078444c4070540d00e20852a03451243c100c0ba6001d9020b40e03040200300800030880d240342c014030000440031007140d0b180748900f10744a07007a115401000c2e4040c01d22807103032940d400805010101120f0030104115110718074180c1c0da590003482800641c025800b880c07600100510b00401112105040882041c0c0e00ca16448845206c0c500d0180003143d40c9007020030513850400c0d1085440c02e43c403c006101800c3d03000c0840d446640040140546d001120303072110003240300300461720f108100084001c0400d910b6289807038607107507100f490704d209144402000c0b0f070300c5602188521501d000e100580e640308403d82c80303404003440700030120000e041e62205500b001c00c00ba003024a110b10310900105185240a00d01403a400300507801945c027a41c02440824005180020941403a40c1c000c610a5140c181514040c60b8580f00350b04001d400800e03907800003980030340040d00a01900d03c24522070101903 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 574320575 1250 574319325 574319363
    0x13090308240603040206090d0803160906110d0305101d01090f0509060f061c030f080108070f03020607060e0f0303150d02010c23010c0e040b1002060106051c0612 71
    0x1d942045055100404001080c01803501c107008010404010b04807410b551403a4803810303040c0c1c00c01c848130015002032101c2d00200b19406049580a0121401c0003e18401308518240d604d040c0034081c501410340d10001f0031106084030940b0340007422076102c418002c0e080e02c101d4014840086c82142891420301d54141c46103100790180c0f40c0b00e411240c004120076640c103006a000321101801c110f4010507803c02440d50f9100145ea04103603035000781c40e07a82643c800d801d8001c01e08d410591004005800001040c8034405a0000420031260105d4101e0f482d03240b1390409a00401e080203051171548074896923031071403100c0880590300c1800418030440000c80348000b80050012000c00c001c0c00908580c0c1c82d01b00040802c00100982d403c000340328843d003203803940f601c0d08461443d58a1004208a400202c90f07514080c042c0180c408010b40c0e014540e071044d84006540c6480600454080c04408a0400c029425030401d480b001081c500f000d000141c1d40380f443d1805141c410f0b10034ac48000042070490007107 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 574321825 1250 574320575 574320631
    0x315120c0b0304030c121b030807020c2d120712030f1d120c040c08090c03010908190c1712010e040f0209150d0b0901140f06010c0213090308 62
    0x910741680310b0301c2c04081c1507600d812841c241c407107a07001030080c050314081c803004040c07c60010f180e203c0d48800c40c003410401030291500e03448507940c80c4114102007102a0801c3c3d04c14018054042040301c09104c404180000f0318107034114540b91100703103c0e10b1300c00103031440c03650328a0307000d03501a849080c0700c0d041a40c012074074440c915104910070341511218841c1c0e82003404260a8490a91007654030700890f250000e003d4403480044040050504001e00030303a1801403120000100302180200800c4005690f0007003540140c40061038030700c2100404510490241600060465010b402800100010300d110071311504441c4070500003481490011408030440c900c9240500d41020000314001001d03400c001100400615001d510b102c2e6000302070241e1508820341001b64454010a81e00f0b203050351105084400020301c60b240d881134002441104c081c034814103604034500b0720300090819410f001040c900360300f020700e0801e000e00e000340c04000d140d030014107140600000c0100c042e914800c250f0038024 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 574323075 1250 574321825 574321831
    0x81902030a09050607060906050f06010210020a08130206040f0e0106080709210206090a06022802091f0b0a0f1d1003020711040912080a050c030106030c0315120c0b03 73
    0x400d0b9615820321203481c014024050062295501060020850383d42c0410f823070043e103203a20341410030310600c0b26541e0184070400c41c0700094542107040020b03071500200041300203020601401d2248440c01b017991030b00e40031100038017200c01c0000002c9694108030000150244101030000d2040c10110b40054450f42d1000100c960705100000c803c2840311541d1a98041c40c6000c0368080002c22824060b0b440d0020341e44010b1030030350050032010000c1c500200a15a041c00b2113010000001452801070342e964094641108480f48441714600700c410f58400000055008988249000b088802036940e20030403a80020303409544101040310041c00c0c00d100244d640001c0c0f98070820640000c40300034800e078003400303a460080c0580d0741c00340003038000b150480d100c03084140c5603e01d05818103404950002c200a411003060401080903240480c44141031340810f004d500c081584800499180f28440c0d0000980d103050000801e03460759030340d003d985450f0202c4a01b1030b01041444000a150403512003901d00c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 574324325 1250 574323075 574323077
    0x40902120d200d3c0903060609110301060503091614190b03060409030c200a1203021002030402010513151d060a111c0e0411030411040b01090e04081902030a 69
    0x780f4540601c18209000040c4031040c1041402e820f0030090328400c4a2000c13601d030710741e100d594949040d4142841030340d200e03811140303070282400e8800710401306000403241100c165140954503034486100003410400d1103840c02c00800b14425020591110a0306482c00c0044110703510b504c5450260031145800f181c511951188080030300000c3c1d01414607401001e4a94480d20f17281c0301003a480d61f00c1c1410401c0142080c2200c50010340c0300ca5a0f8100030b00e40030054840f4880d6001d401c100303a90022340c0c44a4203144a505140c001c8045000c40e400340060310f084611200101820b01e48501f60319941c2c0c0c808150000005002c460060119080c00c0200003180b1000741c2854500001180e080d141b124060700c105a182c81040e0241d0170340c4054000117078543c8010f03036a5071240c1c14282c01704030943d950144010f4030310408000b4800000d500d40d4140030410000c3c0d8011555901c0100142c03a07003980340d4801c2c05e00408000800c002c10039504e006110021110384034407403001120b103080b41d9074000c94104d84 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 574325575 1250 574324325 574324337
    0xf040b04050f01181401020304031b05042a030c0302070b070e03010c030207260c120301050a0e093406120e06040c030602030a0b04060303051b061005040902120d200d 73
    0x480303101205e40c1c2c0f000321804107004030303490640d0344e542e035150400500c04105060307440120180024a810b0140840f03003511407030300c0d4108851614029080c0c213108a01e01e41490764800c003031a0190302a4066501003504810512110310308202c000d80a0030035503105034440c0d464100d50302c2210380248295100343c0d4108015071030588613680848240460305605d8038080005108400c5603440400620300403000450403251654034200a00c0314110094101200c0d00501d50104601c19500043d00e0907031042194560f0014191490011815003041480c034440503554440440c11a4000c02144c100b01000582040f280c924060720780d0702c1d040241d0300104480c0a02000b000490700b6a0080d5170001103118000074502103e00001c2c1c102d50040e032044010980200743d02201400035603030f00b00c0c0c2003a018090009031411110350b10f018000c0c0d004144c810303940c515400c001d644900c4141e206084070001129101d492000002d03000c044404042136011090041c0728410340341c040780c6000042c012707071600 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 574326825 1250 574325575 574325579
    0x30c080f01080a020d080c07230a0324090c26031e0c07081b1801080d03020d0615031407051606090201020c10180503070f0504050c0f040b04050f0118 66
    0x417118500700c20030340314a0818403000360103140a20450005106000441d032200c403403d000b0620007045c107407195210f041c20764070800119103e0029404004e050406000081419000000003410a9035020b44bc00701c501c2004108070000c0500e5030581c40411640444050341d07000f01555910400e9507664000c0000ca102903009c5103954060300313070f505c400401c0d03490312616035460a1400c59104c0812499103581c0d40d40e1603480c10003120f0340e04c0c04006100984003940c10550307030640e2861001d54080405a0020794465041c140b94891000390405041207500300340382c0d0340c0c018042e003242d90300800400404400b0501d940c3c00746040350495401440c1c001718134442625000001c0170341e10400d9055001b460b0001c40c00d5601d184480800c46c816840e64007440f0015040661907030f4981c1c0107107001e40e0000c502881044284080c42046643c00c49001c100707076070f41c02032000d05805030038000c07a1404004200401e002010802820036100d083e0b42000da0003095000440e0044140840000d0b80b50b00c1c2141 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 574328075 1250 574326825 574326829
    0xf0402130f1a1e060304030909091110050a021b03030f0c01020c070b070c031b030f0b0411100c0807051906060306050a0515040f181b060203030f0f07030b040903030c080f01080a02 79
    0xe140d101f80a4141070b400ca598807409981a5034a10703100310b07440d18548101c1106440e10f070310789144407409440c101d404d04515910207982c0e000b401c0300c8032007207014640e081d000b00da400b002181c02030f01c054565140c58800080e4002d0107500543c46075a91400340a201013944090f030025203015507004404690400d1540e04d40030401c03840805a035a09001c000c2004c8045805042441201e910070402000c1c64585410704901c80b441207144039100d001012920740d0150f5008992511407600165030719038804a6140c5149130503040304400c080c01032140c4000782031100303a5100000f1240030b080240710f0780d9683e40003001290300450b10304140c00d11040b11105a400c050780309034840c490a9900180d066850030325000402c041d58800c6908248105154500a0001c04802c0040405000450943c18134000106010341e0007411a03080042c00c40004101720b1283c0c1041c1d0000102900412180042d4140100540101980d92003c90016000300d15103d0440750664101d0307070014064100c0d15010340c2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 574329325 1250 574328075 574328077
    0xe0105030a2001091208070204050a0e1e01020c06040302071802161b0b13090e01050603030a080406060f0e011d1501030c0c1b29030f0402130f1a1e06 66
    0xb88840c100451188042203907400d42610045040c001c4004c15180c103c00d204020540344014040100e81741812040814801c6c0010301c80c9084940d045008560074002e5481802070041210880652040c541403206064010404009544003400e00304154028032224000b0b0f48243d50a00603104070011016000c2080d113001011280117150303e25180650b902d0030941d2503041500e90402e100f0010b03504102c4407030729104908452040e000284890315243c00041e0302c034041c000322034090007000c40004040040d60350203d0003070000304828003283c42e190460108203160901803400812001d4012103221100c800c0d426210f00b0050202e06014500c510044007d8500840f00000b03000d0301030800000159044660b41d8201144140c001c0070610b0861075035903210020031140140c1003851400000c2d004a9003c80364818061404086a6140d51001c079411448503800c0500c0203180205094080c013880d08568000c02c42d1000240c030200300c0f4403c1042d0500303240302403111003441030224900340c28900 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 574330575 1250 574329325 574329383
    0x10501050307230a112113171f09020a06110c060c0a0506061c06050c0d0f06090507090b030412030603022106180a02130b040f060e0105030a 62
    0x128040003d076800115028000d4490310401c0250725001c00c122010607800b581c0180c0e11410076000b0400b0300aa00b1945000384200c0c60502009000050745c0c07241d006454500000038062400100401d101d80325905440c0c41c2491656540900044980c5c030306031302c0d640118038540d45c0080088101600c3c000e001e0740c40e94511081080c45024100400c45299160000b0b040002c0840c0c014012103021490540d04002005203001d10543e00307282c4580e0b9042e0319507001080707030b607010100291581b1030807a443c5007401400c4491410500701083c44601d0285a00300c0c0d011503c5044050000f42c4501c081070729803940d5805550028501440040d01088031420314401000040c140040c04544940210790526145c2d103276090120301250442e2482d60040001325071040803240e84007880d856040504d6100c0c0781486000e445810410b110703002c0c3c1e07440d6034008011030700d0042040040103004215040506100e2068000020320100002540d042c0883c590701700d294004c152a1201c00c0e00031056849034044 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 574331825 1250 574330575 574330577
    0x80609270715090f060203030723070b0a02090f03070602030706180f0f05070503010b0d1b09060807180905070e041a4807020f030a11030d17010501050307 68
    0x9404005001e80000515070140809030350b4204102d0304000104c95502c449511071000c6610820803c480c9030390140d03125100c52103104440003501c4020700c0402690055841c045d19000c4d108040c001c1020b200d500900d001082502c1184810f4031440815848800c544100400b58004028200005880348c8c056980c0b07403000315441d114180c440c4c4030301000c240304010440d90740c911418980c05010003000910000e1404500038042007680a01141003d20801001803c0e0420700060f03604035403144000a01414000504211056076950705541e103003124403446100c005207400f00c0e884031000740240700580740c1010041000d40c2c0b4104200c0040000184180e6214000b0030542d0080c20241d4584d0f401140c401c002d2040c5011101c11844001d07402140042c00108413054078544c50303618401401120380c480f840b513602d070300190022444085025456030ba050082d41c04500c10010101035000c01074a00340c9c100d41e200c0d48500fa05845801c41018a0401704500300010007480d031044008540c003002c2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 574333075 1250 574331825 574331833
    0x708130c030602030a020309060a0605030c010818010f0b10050412080903070308122d04031d130c030b0105040b09040b22060825050f0114030106020601050108060927 73
    0x1d07984600c0101c0c0c105075a010f810a40000522201503001c20080e0b40000c83c0a40400c240341c82d04c400a03a443c114000301d14107002170400003035601c404420f104201602d074000240300c40d10444812a00070003010f107441d4460b49041041c2640c0c58461810744094610036000c080030b40c0d000c1e4440141681000000650505c00c558005c400140303003c000c0e100c1098000941c40b12420b01ca14004400704da008000c062428200307900803007014402150f10341054250901d103401c400034607200c9003003030740e104051504000096248a05048140d200c584508440d035010884803058400443e1648610300c5142000b11061241600c2c526260b4029130202c1c200a14a40e581030305d0b0050040c00511398214a0300f140e58411f820054007009000420154640c003102c0c24035019404081002074116004160040d0025050500729900a41c9a0010b00c54407920b0760f5100e40c0d42d444025070b5203209024542c009a10040401d101d414040700c424055650401c0c80b500c0c840e00f1703e00860342508180703140900c503c5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 574334325 1250 574333075 574333079
    0xf080405030d05030105030d08040519060e0f0a0501140c07110f0d0803070905010809070e090313081b150a050a180f0303030e0d020c151306260708130c 67
    0x280c10051070b80d804803552601500c941c9400308150411081640c0a014417080b0020040050750100f03019041c0c0030034a20b8808081c04901b0130200030540c50311210094450403544210480700010071581440c402c0c130007484910481d0b848408640410348030559003160a00c001400074410000948508070060001c603503201ca10000102c07684540fa2050302c0c541c000009203c805d07a1f100302c0c00c4010707100030300345000c90f0b091601d00c090307444940e88100b8411442c203001040030702c60140304455040d031000e80c82c03425003511400751035140c1700e0f41c2180340184c0b0001030035000c15060001c0c40104909200748100d00340203c002c401c0c0c8041d40207411510402100000440b05600241c65540141c00f6801002240500750b103005070440c0e03d910310359100c0d0390004a8416007658001500c2079100000d807100040442006501c41c241d0051818030507844050382c80104201d6417005200203030890fa500c41c44807010302a00e040f425008181d516030f00242504000601d1060a0b04925080c1e40c45151003440440d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 574335575 1250 574334325 574334329
    0x30e01020d020c0c030a1707030509040f020901081b0409021b070e16170408460518010e010207030f050607090f060e0d06021908040213060e01030f080405 68
    0x41e10440d001440d040c0d000c95411082081040381d45003508007980208003004441d1aa82c903000c00421209410400c00501003040600c0340d010f0310425540504103104506a16285801a4000d004410300040c00b4400090142080e0302e1003403184c41410000714601400c080c1403c3c041d40c010000d0740703003c0030310041280e0705090400c03554000b050340c01000c0d042424060115000401d0030403a0b602044030200c0c0c4140044000c0403d0b941043e4060706807a902c1c00c4171401080301200503043c0320b800c00512203580c000070114401c00f8612140110b001d05e000d40340144c0694040c042d038a0b1705200c1c5860b44200043d154020a40342000800500441d0001d40c2d0701c0c2d035580e40381b4041c180c0846075500150b06206c44680c10800d6030018000020b0511328580c00c08500408004210070014803416082450b4030070b000181d4119003040505e154010008032059401074500c4505481c100d0080042041c0036596105912601d42541c40d00740480c3c80d582d10310b440d01094000c00301c01c00c3da41a4401c0100050903 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 574336825 1250 574335575 574335577
    0xb010917010c030e0c01120c0e060705070303031805060612120403050124052b02120607020606120d0804050304080312150907092312030c190c0e0403030e0102 70
    0xc2168240045411500703154001c080c1c1d07450030040045944152000c416680e0000c4d11100c0d40720058200042d400000d0074110703560250128200d811200001b0201e00b2710101161640135a40242c40a0110701c500300d200c2d144241c041100903000d5005500850b146290054424250038040703812609415417200d58046a94409d41c0111226950f038988564011800e440000e1071501e62a8801d1301c9515000c045003020051b085c40d20125107030100d031210040519004000c005402401040c19031a1600810380c0c1ca540594805003d8411000064094a41144d100d40e075010b414003e0800e1099900d000c0d40c94100241041307845010900020803040004c1026040c40e0078440d01035250390070196510942200c1c02000c4901075058542001135454106008004546010011450005100c0f03e4540301e5400c55100990000c0c2001003681c6e02e000010140c802c42c1d24a506980081c10641440d803120b03020000014001ea80111007042400081d9040c1680240170381800714100850880090072 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 574338075 1250 574336825 574336859
    0xf030d060306050606030106090e070c06020d0501091d0304210b070c0c06030509190f02030609030a030608210f120708041406131209231507030c060b0109 68
    0x49640d555904009208842c00b0b1680c024000f5200300d840c6504180d0000c182104a001d41c0340614001800700701e0700f40c4642d2111072902e400050840d1100541400c40014120a1090900c07480c20000c41c0c01034021002090021010141c00440c1382c28540701d40030030b019590903240711445170240c0d400004510f0300529248a1110760340c803450710a01510702807045d0300705500900101860030007005801e52002034031100010b41d82b000c0e24100707201c5192461000307100c403100039010300941d8144203a0410010203811110001c3e1014007030315840d184500d9950002c40d80861385201c0c076050704d40ca400304140003042c2c2c4000501c006031a00d0048400036801240a13038540300010341d104108000d000c441d03015a10020100406803002d410070010141e118103821001a1020b20300032000d2550300c0c024640e0301c0023131030340d44070f0078895000b4400c01e40b035034800c00e200c2d080c01a4025200700e01d8005d86c0c5011940199070540741c0d107641d04400d4072940c0050894008007410710010140100b80c4004218075454 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 574339325 1250 574338075 574338097
    0x10171009050109050103020301050c0a1d120a0c0905060301020f041404060503030c0309011403040b0f09280615030506070c020303250302010b150405040509011b05042306030103140f03 81
    0x14141d45144141400c480001300be030030401500b8028580070035440360300c202084941e04a003200d4403140100042ca00f40c91202c0401c1a4410b51209904100c1c0c844282402c2324020401000300c0c3d541d00d0241400d03486890850011104104030a05c186194a07285481140c8050310008100d40c451021a19692040d5042c0400d54400300318003002e5030340b0881d01091044040c1d000e81c19400e06540b034020720100540030750828841500012002101003184980b40c110103c0414042c0303480031aa031120f411508011340d640d41c02e14489801c0301400c68844003c07240c2c0000142540c0d41c07079190842c0c0703003041c41404981c1400100802140d04040071b8400044503e00d10140349a041c040c90040e08448041d41a68002d06070418140d00c4041000c040c0e40c203c62050b500420690707225901203005000d0720b1400c030444103c0b01d08200310343c6e50100c060b2059407501c0a0581140d00140800040b030743d490300c21950301080030001400051800c0030a41ca0300490b503030880340b10b001c1c06251182103800c6611100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 574340575 1250 574339325 574339331
    0x1e0c0f061506040b030a09111f120501140108040f0512180409050c0f0301060807030f020a09022514150603070506090d0f21030203011410171009050109 67
    0x200320441c45581d480840d00986480d240020882e03644c08001c10f070042c03071070795200d00c4018060040340c042100a030040114600303035804424240d8020003200d1480c0002c1e940705403036404070210312030503041c0c030301e010311143c4000215001150412401001143e80602c2d020101000039010040d981c00c00030a801c0c00350306e490540000b9281980f9003805584030350f040407520360200d031021500307458000041c0c4007019520300d07001c0071a025010b00d500c025003d200d444400014891019030070203540e4401c90f03d4048241e5100d101c1d100364001c40911408032000000e81400e02200d05e01d01034a0340f40300b07500d03404859801c00b500710b0400c0d00c054402c03c25039414602b0801c0c2403909100c42d10240408a07455410142075074003149501801d6500200305051802030fa030f05003c2075400640c40b901b41c420118070801c00c9004010040d4000303104080310118400d0103010240f81940003200d40d1540c40d91041c00105401040c1d15580ca809000c0e80030184011001203858101406640d020b01180d00e004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 574341825 1250 574340575 574340581
    0xc0604120825030c030905030408010f0c090f0b03040c090c0915091d04210f08070914130605030109030e030c030a02010909020f040914061f051e0c0f06 67
    0x242641000601e5244a020b801c002c4010319002a6851406007600d854001000c03500c10605030020303c40c072a0081d041d884003083c00198002e05401403c2c91802c0e051f070900c05120b04050a03203140105005a0000000001d0f007802900000e1000d15072141c003030320050149a542d1580413003243c0b41d080c00c88000801c0b2110500207448066550708d0400380501e40700d0303045803078411440c441c501c20700680740840b020800031030103000c406400e40b09512742c01c80280c0e40d4904111006803c05002c14010070101d02d04e035000a03007071406002c0613011900b40354600790a0807411004c0240802074a003250400c10355509000c5100c3e102481001e03009403003034407244000c400f200e007014078007804440e003580b19a00c02045c0c900183d074084d400c80202c80c030f01c800150711142c481070300c68800c3c001e0790401155070f848c0800c006103240c18800c4903809030a080c0d0314454222240d840800a400c58a0441408a1410800b4540d0341038510b07501c0907030310000d0f10b10904008000c10001d0900c0a12200060180e02044c14 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 574343075 1250 574341825 574341827
    0x20f0a0809060f07020706030203040809041e051f090b030a170c120f1c021606091103011b0c1b06091e03020d0212030d110d06090207080301090b03030c060412 70
    0x24040e0880811083c4030400d140820000b9a00d08172030040c6020142c022000c40d080200c5102620721f4034000500620450b030390381d003503c80340280d00c0719040881810700d004140c603011040c1401c0a11441e1009258440b1b003010381450190200308600c0e82c0610030a00e446010030785946141d0498904204804c0d036034420715001a1811040ba0704100e03012130100040042c00c42c101048814018440c0210721003409698150402400751707a0310f900d041100b40f0216410000541c2c400702d207143c4140c52145500d0360500515080310b150100300701e0f030f403020300d0320011300c2c640114240d541c290b100310303002949480d00c90145030031100c0da5071041c804039440303110902040010444410401d201c4080f445201480c64002820a41420601902a103400354082c0031203e001d02c01c658001c1c1400300309011800e03026804050681c000100155003a00d00341012800001500880c0d41c0c06400220701c6007503034245880c0e0001410070585c01d0768184801c0140301d021070300902019200d40d00406440e4000c003441e9034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 574344325 1250 574343075 574343083
    0x3090c010302090306040221062d060307060e030a1703090d11070e0c0c01020a0f14270d0b0403030608060c040602100c0e0d15060b030610050706020f0a0809 69
    0x18500d05040c014007803c1d800f80c50009400d0350140d01210280c115141117440e00000310b03000218049103004201c02c002541e0074039100d1613684400d05480c0c2403025a00580c00b4141c1c1015100f03d40e16421800041100c1481826580c1c0103d90080550f070002045550b0003603d0305031039020b104a4100401044070101d0f082c403540c01e070b111142c1042c000b07102445c5880d6480c1c2c080d034000d442c040d80241000c0f821401c8002d0907140a09050300085640d8100700c4806000240c01c424140000741e40e8505002e0311144a405440e1075200f1900120310014101c1201d84c00d0125400c1314a8100c4422550030000c65a01c180090289000341c0700040d0b401e00f003004040c2064402400d500e0000700400c4200680c1c1d07800a01c81500074108817001500c2c00480c1405c9032032080c1d8082c0c690303100c6d01c4c42c8041070901c560740ba0380c00010b294600e404c0205690390f50421915000031503e180d440a80009240c3d0150700030320080116600c10b540042c60150742002d40c4680390010b0303c25900184c0a60308200703190100300 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 574345575 1250 574344325 574344343
    0x181d010e0a0902030a0b0c04090c0503040c08070b0706090203010f060b1306030203040f1101021501170f07050105071407182702061e040b0a030e1b01021018060603080309 75
    0x100103120b0554290042075a5801510004210b0f446100001d90300004c1e641c1030f580584101d001c123109040d20356000411581090702e0035500f16040c040e00003080607000445104070340e6200c134601d04140d01c03071715407900500410000760f8240d500c603028200c10840f94800e82c030152200d5212141c03600241d81349030807103045a81010341030510400920000c14540c5206841c0c66074080401c0161001e00d000403406c1c40c5e00381c10050440300c1140c1c000700c0c0c10501c00c214600b0b14100101200e01089680102c56528411881814045030041007480045090005207240c2e85400c0e004640c902036070b07941c1c00d2211071070203031465820035030728410107450302d424116a04089a0390007a09044802d03030703000102c1900c5100180d900548000240c8003402e800401543c0041048030351700c3da15005940c0002c0c001c0d260b1030080c0205401000c4401c04991079440543c041c01ca010384c0104010550304080d900100280a00c2c121800c1245000c0000501c5600501d800f03144103180094a81c104a00007901e454441 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 574346825 1250 574345575 574345591
    0x8060a2304020108040825200a0b0d02030c0c071214060f0a0b040b0607050a0308090a170904110a020c0120060627040b0f0f0103030f181d010e 63
    0x804244000b40c0e0f48a1003554000d604900c01d5a52241c0305209146860810700305070104020418281d401d2141c040360092000d201d20591403150813102c0100201c001440c041c0025600041c4070180c181c1d001540910b5010001d58540c43c5000500403010b854600baa5001000d0050344001c1001006070000a013043d504100004041c10306207280c0e80781030300b20004c00440700b041e961b040b88066035549400501c40b1110150446d9920310050900e07540342c0541c402d040c2d01240c000c0d40400c1401c040083d540c2005600a64a40c08030b14901e100174420340e02200750560721039210318079440124a0b8100400c02080710b03400401503003510200141007036400340c642056015803005207000390100071036141da10070f40c101c8a00b001070085030800707110280580003400322104440100420003409140715401240781c84c031401900e40e158840124515424000100020401401064121301a24003007004080717000080803480d481d0b00504c0d401c030007602c142c2450650807000400c80d40d8144600c41ea0012a4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 574348075 1250 574346825 574346891
    0x50a030f080c031612060b12011208030a0203090c12011406040204080c04230117010501090c0903062a02070611072d05090106030b120c012708060a 65
    0x401c2c071042810b400018000d115810310103061000c454400d04204140400076501048a1038030b40a03007075460b41048142da001c6200c030030004211107207440405030316940c2c0001c60a2035543c1b0140c01034041c1d007000e17200100c80d01c03030fa014900465458070001c0310842c00e80b000004124080c0e91120401c0c0c070003e40541d0050303104100070310002d200840c9480c0d03159400d650100d4100e103082103c45000320044105003880c00d644001051400d12120b030b0a00c201c440b50000d010791307602c0e002c00d0710469902c0b000010226035001310400c0000c0b80d0350800f0410b040c90682e40044100010a407801c8030f0645001e02c1c0068110302c40c01e12a59812407100e0101038030100061094506180c00c80112459640c40d000e08180b5080d132482d050013000ca403c1c00034210241000c4004e59585002601521800341428071a1500f08213020390b03000000364188844034140d544680302242501050a907401580001048548904010a03140420001e25008195264001030010250250340c8561400c1040d42000003032 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 574349325 1250 574348075 574348081
    0xb0f21090c0a05090604091b060201060503060a0216150f11031e0412050c0f0a060f0b0f030703030e0105070b101707060503150f090a050601031508060a050a06080a050a030f08 77
    0x744d44201e1a484501075030001181d080609021000d40c01030403148940485002003c07e501c1d5041d00280c0446a0540c02c40e800394560070700c04010381c000c24a40c28407600000b00d42030003048408101600c0d60300700c0c035170014000038160ba0307a41c02e60340e1480c03110703500180c000b0511001e20100c0c030021041020340c4c00705183c28113180e40c42c450301001c50003411081000100d920780e42c210003400444100003c00045806c402c04925000014202c050342030040b040c946100170b5118107001c00c20a01483e0b000b4040c20140d03044d5a819213542c50f042540c44d04004003480307640005102d103183c5e94054081c4d803000009281c0b510042c294290344044441030250413050307040002c00d8012060b80c0d0080520781c140014800080c0c00720f840c03202c411130003c1e0712039100e205010155140798004d81c000d0100f03036030030310142c0340d8000c507802011014815182c1e90380c00100011042c0070b19510070740e00f10005090200f641652046414a0541c0e680e0064440e900a900e1080c20190011021503142255040840070b44c5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 574350575 1250 574349325 574349329
    0xc01380105031305010e15090706030203040201050d090348030c2409060e12042106020702120303180601060f0f030e0304060905010201180506010b0f21090c0a05 71
    0x400098030007070000f0440000d02c0b040000030f420000c070401c0c0c00c0b4121503640841100181d50307100c0a84056002c0d010303085001c142c4602c03d00844c0d10070354042c3c59003480c1c500301c82c0c8a0001001684020740c1001214004c0103040030035035890305650a500100600f80440912001000d0600d0344201052070f8010a21500000d42068103100d0060704410b200b0b07503491010226600e0120041f104080c2c80c0d00d010b1040080024603403182c100d610303c000403108080302842c0d0100603407080d40503a088003c58440c00124440e0420100405d0600c5102e0150920005901081800e62051603480c884d4201000b0020700300c101400145c0200d601500819941d490140080c0c0702201c041904800c0003112100e80c0c22480c02600801501c444040c01c0381d0369a903440c1d000400c040c00b00d02903e4015420001c0921804c0b2440d803000642503007000103451141d2130002e2623004c82c0e0006c0c62010f0080c0c01800708801c0a00c40c0c200346440b04420b002c0c080d1451034810819401c2640402010744582c00d80789040c4025 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 574351825 1250 574350575 574350577
    0x1302010306051c02130b0d080d0c09030203120c010e1501060206070903021e010e0d05071404050411010f020f030d05100816060305070302121e0106091206110c01380105 74
    0x1568042c5d500382520844c14041c10090143e44035503d803c5043c41305410108581c020007003042e074290b80010010b480c4140000c96a40180b880060341c142e00c03440601c40c00c00c608070001d00c40203031544000902d1501c01c81919080200f0000f400c40305510401c0104580394051040b1039001c0703840d140100000781181c0c0014000c081580180605116880c11314504d64050400e5002c07030f40c4000c0c8003180c007014900e0641c3d40c821040c042d4000030110741900ba9074604190080500a0364460005914401f0040045a41d811589040c0003140324030300284441c140240020590b04031002004a40f038070700f400200c00c600e82e081d8000703180e5500c50744540d01c001895208240640c1d0085c0b4012a0a441d0480c003100a8051000748240761580041844040c1072494151041650f41c6013000856a03620b42013542c41019920441c800011190307412400200340754021050745c04007a40791403c4c540382c1800c080c00c4806103440400403804c6203a0180a1280e162000b042c05104425003149850340b002c002006 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 574353075 1250 574351825 574351879
    0x151507170316080408161103100e0a0204050c1201080d1803030f2f0a0b0f010305060c0c070b1b10180206070510090503030a150614070303060b03130201030605 70
    0x1c020980000c141009101c5080b1ba0613288060042e80e441c1c0c030303030f41070500c08115400729440c03180c03280c4050b8080c0100e140c00b941140304400310141c16245d07500e80078000540401454417014603420003003a0320300d0415500d00c80c088d042c150014481c1031903144016003401129070061031740018035401000080da0144294100d405a45030801604418103810244070900101c07a20400600e43c01c2280c103941c0008400c660030780039000840c2d5a1326491160f0994420a00000d007041e00884005002c1c0c0c2850401407141001400c110345009036200e641010603001225040603c5004480d1440001000c05c110003148800304020400d803070503110b822640140b08500240502004292203042c01014084800c8602c50482d00748941ca10901e080c544a610423601c0c01d40580c41c105031004c000780c1c981803503429502980c07543c0c00c078001ca0180b266600d80103190101c04140d11100046017403602c48010314050f030402898501207c2d000e01c0050269951b542085000d0408400c000b1001c40d000c85000310 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 574354325 1250 574353075 574353077
    0x60503030f040312020715021b060c0a0f050c130c120e0601140315011202180103051509030c120910181202120706050d0509011b08151507170316 64
    0xc034211520a9090440c194040006001f520000c2070b01310b034003c41c1a072007404a600c03400092201c4c0c942085094060740d80704000c070358012504080040c0043c86041045070107030080b60300803030044001a000e9082e0b0a150007010b511003900e447d005c0e8209400d91344100a0000c00c1c08003c2c200d80031150f5610301480b80c451580211080c00c0c03010344082c080450100c2c14204140c02c6503840d40007481101c510010124000c00910680c40d102406100310107050780c0c0c1c801c001d85040b801c091900300380940c02801c0b00080e03020030000b41c20049000c102d801d40000d0f03030f0340c90591204010002c0020401c8001d80d0b000c1482072001080301c4610540c03026900380d0350701c4400644c000800c0d0011130343c1e103450180100d020b4414030401040c0715400c032010301069021030078140305641e5a050220b00303a503e044110b840c1c441540945030381090043c490954020303030b200e4034481000801000500401104900300d000040c2c006211030500001805d020be001c001441d40628500f0300f0320740c040f122404113010344 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 574355575 1250 574354325 574354343
    0x1506080f040b070903020301050f0f06010f02030403080310080303040c0915050108180327040c140a0815030111071202060603070614371404380c01060503030f0403 72
    0x1940030f03400344560350003668014000304010700d000300030303520691700a550444811008a000611310342c0f044820520061103a03001d135007494034542e5401c4283d0800340034101000d01e4440d0100e0840b02c00c1016511440c0070b08001d0044500e000003802c1202da084100340100e0010305002d00c126600b02151640004c091054400400903052241b03003103008821450020044080c804908403000341d044440581c001ca6041041d60f010003c151201d0220011000640ea4240b0610740124001c140c1c25520000c0c0b0050340c40041c4400c8000780c211a0f95444080c4111408030f541c105006a41c005011028414002880503041803800641d490607036108013030402c5210050310000403084402d4130311a40c406000403029121078090a010709124070b9240021419101c00965003502c03540c5c1580c403108803c0085840e15042820240001820a0070400c024104d600c3c104404a5102e0601c1111003104214548820881c8500703400c2d1030150303100c0d070300c00d62083c80504403c0100c0303412141202c0d8090503003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 574356825 1250 574355575 574355581
    0x2090f0c04180f1508060907031101050306010e030106060c030305090f0303040b1f0b04091b050301140406080613260d0c0221030a110f0d0915060305011506080f040b 73
    0x10b020f803a045000900c540d0605800e1000d8000590108040e10141e0b020748403160703a42c0c0d10082e039440d03040c03002a001c5030350240041843e5000b80e00440c0c0200061414240c00d094481c003003400d4071400d503c100b00245151450700e06141d454413540c0e801003043d40252040c00200110142d4038040548050708241440d03010030600500c032036400c2c0341c444c1c818454034040b40c1d840500c052603800901c070350011241803450080254540801c01440c220030713911a18116400d24082d403002004a800700d940103a6518008078021404021a0f403003040004cac100034501d5a189400f01c04074024910080d20f8181200b001c0c2040c4400105607007005480d0240020f0140c44d000c4101e1030401c079a80c800003060345001c24030b0740c81c1c0090740081d4031a1503007000074845030501d0003a40c034035880780303035980803002c001880742d000100280d40022001d10f000701102842294a4a000740840c0c4940e4411580c1382c2d96446440d42002c196a0f081c0c004004a080042c2c031450119001e40500c80c000f80014a140c3e010400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 574358075 1250 574356825 574356869
    0x6050a03020108250210110702030a0b0604020c0712030f0503091005270d092c07050c070f051009061e0318030504170304120b09030706021602090f0c04 67
    0x1d0604c5915040102c2884841080d00170f52108080340740c40e06402c0c140303650800b1f5807600a048a04260f809070040c8010340c069204c94002d844084d10440c0d015408100c0641005800c01410000e02510445078044000310b18001d40011070080300130083c807a0a00c20083d4005001ca0112001c1c40500008030740340e03850702681810388816001d59000010000186070006c00001070407507122a0503110f034485c040d201c4080c00c4003ca00e525107020581040c60b6442c183c940c00c400c409402c983d10f42000c60401401c000450300384001a0000d00e0380040d482d008111519101c10340a51203005820940491428039000400c0c20911001e0501480410705082000c1032203580505196989084811076087c460b2030001c040e5486442034103100e180d4442c0c0d000c04030801004881c203d85034855a10382180322642d400f16034070380060000005000a0260f040404ca0900080901c114210401034140c0721501c100b010140003d4003012500030000108171002c10080c0480e010b0740c16020f0641d03a6949060f403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 574359325 1250 574358075 574358101
    0x30f0c070204050403080f0a020f1605011503050a0302060708060f0618030d05040513142719050d0c170d060f03110901241d04050c04150306050a03020108 68
    0x350094000c1c0c0b801c401c110602d0b0784024590f0080c0e060011500300d40d21030310011b000703a0085101804020300100864243d0388400700780c0890031032244001003000c1c011000e2010400050f42e0042d01c0799044501d40f07804066051100360b40c08080c5051188043c200310b804106000c2e00309510f03500034800080d002d07114074680c41046940c0720000f42142c1e408421400002c041750003d02c00c9501401400c1d08450b860042409120100301d0000003280060b038415030000320f801550900c4101c01800e0b1402140c080d18180000e16855600321002c19146013989400d43c40c0014442e407820800141c07051007000110107100305100036100c640002d4460348180080d000600321a030100c4001e4141002c00410420020701e911113440c02180c003600c95030b82e2000c4440c902c42c020190440480310500805003074030300503403d00802500c040d005480c5042008041022950b040e106030b40e09840c0810100103604000d40355140b00d00315440c00380022807030603000c50580d5206020013030620510b08005400c5084400d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 574360575 1250 574359325 574359337
    0x30c030c06140a021308070302060702150403050f0c0f030f070b2116030510030807020d0c0e10050f0d02030616140a0503090c040b031902030f0a2411030f0c 69
    0x1c481e0215410200c15240013980301c0700400d09000104e21740044d09020104180301244e03005401d4901e000389076402c000841d03403204581d081c0c840d01800003101103001040445030460409004143c86c03a40182000080016000d0480c480e502595452022080201c1d40d682103595071040103071145040040c8010900140c0b07503134030b440421032702084840c9c46000041c0111240c9624104900d032510201e40b1301d03c0415010142c4164010046c0708010306090b401c528156000302c4030782d441e00741c907141010700700300c002e0b03410300d51800001c0410320035480d10803280702604104880d000c60740160745d1301080d107a000003130a604803c0000327a14884503030b0080c80001295500c0784000c40e901d1030f09200103010381e00150368488031485591007406140c1410300c284410f01c10010010a101001940250307110301036100204e8050040c0e11102c00319440070040114254462261041c010601900300e41150b03006808200344135040c00000d00e9800340c414200ca81000c60380d84000310329a00c01100c00320600c190 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 574361825 1250 574360575 574360601
    0x1030e0d05041e0e1b09091e0109020c1216020a1503060509012103030603020a08010c03050618181903080121052e06030b01150507030c030c06 63
    0x203004501038055001000300161840b100700c041c9400070f031600940580110340643c5041c0c810090100307000f2079143c1404448040c48010f090300d4800a200403842116003945d1902c1e104401e03000720b020382c007407615910340544403130402142444040d50b1040d554080d40900c80c005210005840180c40c4404a81e03240314580181c2040641685c0f1400304220000c400d003114000380c1f502c0c6000c00c0d02d00d08403a1890482c0c0c00c80e0901c04180359910351134440f080840c0002c0701815503890001006840f91304040e8020502000001206400490040c041c3d40b0b009085907c25444510b1211030030110303541d043d0700401c81022030078401d5400420507150115408504111440c085698000c141d8030644480c140c68004078241185101c10480d4070745d01d0f6030b0b04030003440c1e41c2040348000c07a01607002e0740701c5a910032152201d046100c118050314086409541083d5a60100b0700c0050110b01201e00083c0700c6081e040ca0100d18101c03580d20000c018400e0208000d041220503660b92041c000d40c0e4011605070815 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 574363075 1250 574361825 574361833
    0x402030f0604020105220b1809160504270608010c14030606160c0306140411031501152309040c0c0b0105060708092e03111209340b04150e01030e 64
    0x181c0f54202005554219001c0c4270b039801e000018090004ea90304e800826a0380c1c1c5a40b810a4140044001110740441503505500c0c0840c0080403c1c0016000b07450040c0f82c55800000c0355118181c0003012520140c10000a00c5810401c3c4001601c600d8112405c010611a10b070285031800c3c030b00302884900740e070f2000c2c041e1803c0c81340b951440700e03901980038040c03441a40c070a00003040180034581c880403601c150201d281e0f40c01d030040005c1c121800d0b2036104440d50349030040d40c20281d1070700f00d54101d9200c03484628901c0702207956405420207201c0c4030340c1e101417400c040010051683d9400411700050050a00070314010a0203c02c00c01c0b010183c0702e2030b0000070450710720441c4030352841302031040c840f03210114090500d41215480340a0b01c036409a0303454026040c4d190607100780c1100301e00c0c8405402d901075841000114010180748191100f0702c44904690b00d54800360b115040364112060b030b00b022640010401040051b18a80560780c8036046450a04005207240d90700142c0040108862a00301801 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 574364325 1250 574363075 574363087
    0x1020102120c04091a0d0b0406110c0303040b060402070c031218121232130e01080c010f0c03031509020307050a110106080d1b080a03050402030f0604020105220b 71
    0x40c4100c0508103a400c403134801c01194080c80c0c002c025000100c85143d41110413841520089505080b40f00d610074000e80c80460400324a600f000d030309a0184041c114981c002000340710030025540001504000e044406500703100280d240d0b0080c50710b0303e21000345042d03030003200c2c0711940e801100340b019a0183c01c0005209180e8614400210980304401160281140b03d07496003203034024040a203400203840061207024181041c0380c42d14081319290521800c00901048404210300840d00000d800c6207007410365a545895690781c0741500c0034082c7c1d030502c850b401c502024980d00044561210303400d491f0114a403542d4903a0100e21000940021000c60b00000030024050b802c68001d0407148407650301c40040c01d6880780e2050886006000d9004d84e500188a0114141e02c0b40c605500c03800f000030480c008600c0c3c030365689000d0b580304906410129445800b003002f0b500d01405035400c0a00100040c1c1107525207940000d02600c1440002798070000e91105100704901401000070260001100241d5540c07 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 574365575 1250 574364325 574364341
    0xb0a050c0f030a14160e01021605040207060f02031303170106020d031109180603070515070201050903030c0709090228091109030601091a1503070503070c020d03080103030201061e050402090102010212 88
    0x42c2004091742c0c0480c50000b14030086500c00107084003054140c1d09030205940c14403013000081d501070082520829141e20024889643d50b200840c028212001030003402c0308146000303080c1403c90342294444203c00001008030a4004c9802c0f54450024500020304c481c80b540c415195010f5811042d4100b070109841d00c1300800c05e1a94103001e08411000c030381180d959070b001c120680404070041c10301100d06000708001540a000500b0701a4030050940f401c100410801520380101640b000c0c0c070340c50f1503030410004c0d42001240001c07000b2541940c03081d0f12440d0195400050020b1007110543c071b0392056244c042811620954102000080550742c1c0b84d42d41d038103414050440300300c10206204540004540b50300d4925986008404c3c440035207419603403824402c1d64a604003d01e68024040d0144126006a44003a041c060300c621a486110071941035047c0242101c1e12604814150300b200c268810001070585052000c8440480d40981c1d6000200c0040340a8083d4000c408080356120082c02454 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 574366825 1250 574365575 574365601
    0x30705011d060a1709280f080c1f02040905010902070206030609040c0f030303140901060e0c0913062402010605181902030c0a121a04180b130b0a050c0f030a14 70
    0xd0306e01d80c80f03441e80460f80044034516000090f001428002c00d6007411000a083ca405480700b9201c1c401910202011000c03ca01040364001d58a01c0c900d500003810311007010144140c0e805004103800c1182094a141c0c0030034620300c00a440184602d0b0350000103010404040c1c90343e0090440c6c07007100c4007400d5691401030058102d000d071200e15070805d6400104989014850402156400c40e4200d480341c40d0543d04d040345038412011039030030981c2c20151540700360541c0520f80c01000c800d00302c40d05004059050700c00c0e0210626940046904009042000c0e61b941c8481c489490561100c0b60031035151050621914070040f096118038030300200030420244c2ea444050100c800c0ca0380c81d0103003806075410102e01190804111440c2c4900142240030a07800e065110204440c1030381d0130440ca4081613120b2080c400012036014030f07001c00a0101c8002c110000b400ea0744c01c04103a003000e01643c2403d000300c0d00540603052050004c102e0200001e4240605500300040300000c01c51354070b5150509500c51599 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 574368075 1250 574366825 574366843
    0x120a1502040503120c0d080703020c030703090303080f060906040c111005100801050f0a020f0919210f111f02061819140c090f06030705011d060a1709 66
    0x424001d0700c0c000b1513071080310000c9501548000c2c0260908070482c03c815200d40c40003415100415a00788080b8000b05010401854440c0c000e403160a005461854010042d460003002c2d00c4680c404075080c0012601d42d45035990308418120360209240011780382c01c032041c800b40c8244000741d04c16a008001c01000592029000b440d00c000355800550300c45144070b00f80c907400e66003035174204c2d20300e00003501c29079007a40a4039580918904240c40c21010000281200c88000d42040701c19114500070010201004011480d242500c0300f200b40c076a0725a03d880e4006a28032001400d0701c8108100061150b691020b400d40c84001c261040900030400c050080d0348600442d150304811030101050404424001070300c441c40c501040840c0240403280c1ea44003070340750b8480406041842890004c17410fa94031480c4487c401d80104240c82e0f8903140c41d000709403804580394003075414480110807069030f2002141c50580080300545085540d01041801210b01608990900803000346000a200344c030140400c07242c5c8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 574369325 1250 574368075 574368079
    0x10b181302150a0905100c0219090905010501050916080c0702121002070605060f0f010e150d0e010c0302071713030209092a0a030605090106080307050703060c0305070905120a15020405 81
    0x2851907250710500c040c40e0590124100420750747e449420043c61300c2c0505c01c07005206584100012a920a807000644124001c00c0700c1c140d44078401840786052004d0020340c40903044102850302c001c1c85a010700245005401c05440303140c009011025500c5041d01c05078601c04420480350030200362044000203402c1414201ea0b054205400301e5407034600032100844030000180000840068500151444070b802c04046410010800b05000b90781d41d200003405d42d84801e20390110b0324030140300240d42104c0e150484141414410700415000c07820120880404c1080c8001156503600c110090045074102a84001d51000da010b0030005580c0300851003010040741013495440c1d5920092103050100f400171480c0740c1103a50b417002000404c8454004c0741e0004460800098040d807110245404c0d9031102000340c2e80c1d0760007603108008100f03441c4103001c041d503c0c1d403404100906103540000c090308124410148a05c840360303250040f518081c00040c0c9400e42c412810074140c00120b8296002e5046841203034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 574370575 1250 574369325 574369337
    0x120b0a03241119030c03090507080c03060609010f12030306080102041d060405090d120e010507020d09080c031f0e060106081012021f14040b03010314010b181302150a 73
    0x1141008002c815140e469580c4419280c03258442102100140128450f200405846d42d01d1000446c60500c01c000141c0800c50240c07040301c0171036087c140703002006409940030345400300040000001f2055414169200b40c50404416107840c20b044001c2c00442c5c02040301544000780009801d000c485001d0718854415031060300340c0e6282000c010440e40103c40e40015500080c0c43d01e0000342c0309640c145611400740000051000c10040a40c1c01c4800032030340030000da88252041054507400c56a140300811403000200700c4c01c0d9860002c80e0b2a14401c03440d054801303068090001005449070041050000803070300310790442d03946101c0181841703815220300102c0d042c03944021480c000c0d800030324090346030090050380701103181c4640c1e5491621140348007003c211860100d1002d880901c0020401044009251626541181800070102c800c4a0403000580e00d04154038249854084841c41c006001c482c2d41041d983c0c0d0550088145601041c0c02940701040d40001710100a2120181034000c9088d5264 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 574371825 1250 574370575 574370591
    0x726100b07050a12210b030c2b0201090b03101a040303090e0c19031436031606061502010c091a0d05070e03010c02030a120b0a0324 58
    0x450051003030a0029007140c0000d090300b004208807006200d884d030f04d079140880c850b00707030401d804c02c5002c0d1642d0360140c0240c4030350300e42c032907407804100011307840004580d0050754034400d00c04643d1a10420b03421317480c40d02c11100050296070045260034000c00d2112040d540d02d290803940c810160540c0d008084181d800ca003c8100e85442e40c03001d6a060f02e0340341e100c2c000014209801c403441100000c000e00040c16040212070780e22580c0103071704644550262404a06d0340215109441003000c000d105000303441c29580360a401a1044034110804c80b104844440c44520850340a401c510640d5844001c181c00c03c0b100c0307001c01581d684004115428540c040b441d460045204034242c6006851000020b5840c03c03061100701c0900811501002d10300007042c2c5411406000e103401ea400446034440413a80403c0c441d221814280109d0070107050300c1c07000e1407411140c1c0c18040d004060010301c00d901c0c0760fa06c2c40c03211001d49442125902442d08544542e809108148401b0704481480c1c1d010b4802504140e0300c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 574373075 1250 574371825 574371839
    0x7030c120503010605091e030a0302060a0f0513030509010c0b13060e01020c0303160215010612051b1602040908072609030307020607060b091006021b030312072610 72
    0x1030703d0580303100b6070390709207080000d10402144894002e08800e00c3d2428140c080c4195804001d0303401c40c1e0f48603401501c0e552a0102d006011200c010b10048c1c80281408100008800d51b90f0144841540c5418400c0e21107140f00700480700781c1603580d00245598002818440c01000d0340818200391803007051300b4000ba2154144541c2030340142c4000c0c9840d0f500c2032010035224080000c840c500303028184100d4440c1c0d1256040000003220a074400004035082c5a5201520302a60281a500a1070a2003071201e28141d80c40c91405c6100c1e4003900079401a10300050811981c42e5004a041c5079084048161110300d54140714232140d01359411045281d0400044200f80c00c091402d403450300c1030040107182010301035024049168003410003254130300c0d43c0e0100c05405a8490800341d000d18404031000502c141000006464801d41d91400c1940d00c25800c0350417528be400000315140c2445640242e100c0351500242901c2d02a41c080d103030900c0c1d03004191800c1484550b0450188910385220740c1120280d990300c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 574374325 1250 574373075 574373077
    0xc051b010e0f03191b0605011e1212211d06010501020f060403140d0903171b0706110f0304080d1103090604030810080d08160801081b0d020607030c1205 67
    0xd009031181404c0303480c2c00e15a4042c0c0e12079001c02e8884c440e14031450015a4444044071003d802403510804000000c0080c0704c030400080002e0b14501304480d040d02196201c0420a2280d40801020002107018000e56051201109520111208020312100d030501c0c0501039816107455905546200b03500c00003c09600c00991259681e00040242019440e1038030101c620304054a07818201503403c02144038080c250f03100e0065414040d6445280c0c8110f02c2d80441140071005d040490002180700714500302c3c5158508980c0ca1940c05800014003041050b5407421602590151280c000c202104000500c0a148000c1c04541c110b1041040309075070704802c5801c0c902040c0e80010035540114006800a8001c5c440550085510114600038645c5c64030004e1811020428400002e0b0500061140d40c0105461403845241c103410035102d198140410550f5551352071011812110030701042e101540c54881c0c0d41800145c01811090b624802410050818a8507403400c84003208000c7d012105648210 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 574375575 1250 574374325 574374337
    0x12050c03010f180b18060111120a05070f02090f0906010e042f031e010506060304050d05030411060d020301051e0f010c020f04020c1507050a020d030c051b010e0f03 72
    0x641c2801c0c2034108142c842d050740c10f5070004024255a800e00d00a103a0790810002040401d51000c051107241aa000500c0051075400000f00c0e54840c1103c2c41c4140300c01000d440c421081442c00303540341d003035a003000c00e075105140304085d410401d08014440e1440754950039520402010084907a166a90500040300400448010f000410740042502d0300440380c0404041c41c03040d40d10300d00310040014002a017004200041244000e80c8c1c2425500c400e00c00307014095010303500b101c041e815842d0076180c09484441101621042000c000002001c001381c0c41a1f1242d500070140c481a1a46244829074009620a005036031090380e81010700e28106a150010712504c41d4041c00c040a5001204010b40f00d1141d0070b01c040b640124490090007107074a0394400342103420f9170302c001044540d44210042003000c901030021020400d0812006040c150001103c4421201358a40000d809180704d10446140c000d24403185c181c1d04c22204003010401054006400d5140031405803007180501d02802d80e0f8033300c112 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 574376825 1250 574375575 574375589
    0x30603070e0a020c0609100b04090804050d05030c123606030c121f0e07141c0c03050a11040e01090e0118031d180a0f0b1012050c0301 59
    0x800320900404031448416a04000368075805410011000541420014201d48605507031340722001025040c3e44a000b0b0521864007610100200b000c3e03078075001c081c0e00c92405954001d10080d00c850003000000c0084401d80c01100040c1c9040703902852514080d80d120401070b0400004c030f5140ba018412103e80310f010721000140401419020f014213110903500000e00c01075006000b031109a84000690080b0380c407403030040040c080580070f10032013440c643c21903030003009181d242441040301c0550031202c907000610801c1d0040d5210411103c03032040c2e20715500c40e90035281d400d020ba1031814a4154003c130340100c080c690f0a0028848914900805d07004c1da01c0b4150a0790301030030040000844e240c2c0049000c1509100204010b0240000b009140c1030299040f80042c8000c100c5007400c0d4001e045032441d0090848000c0c4254405203c00c12a200d0040c080e140c64a0303440b10b004a410541d40d0104441d00380213005040440e031441c0001d403a41d05e20441e512483c50402000843c0c00982008407810b807542 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 574378075 1250 574376825 574376833
    0x70f030806030d0f05070f0c080706050415080405060f060418030c17160b090106031a01080d1e080709050301050a0b03071202011403070c1b170d080105010c0611030108061b030603 79
    0x80792200c19850541f0b500903101c1161811001c246041c0c01d0165101900054030385030f82d01d071721303200031a0b4184e207075070851300c2c100a80300c3d0510001920100b60075800c540205190310041e241e4100040c001c080c008003113250200ca01075000201030b000a40500c0c00303070164418400580b491240024680724411550000705c1c909001c10000a049903088c6400520320800000c01507125690325401c05a800b17880c680d80c0940b800100280300003003000420480c00c6180c8100c000002d0060f0300f020140c100e820350244542c0000149405118030303501402000020020f20140c200300c10074100030300307000382d202e0701902482101007003a20403051709110581d8181d441c0280d43e071400c0c5a000301074001034000300030040036003600c03c0800c4200c00c10340e810f43c41814011000034a04507101c0000741010f1a4111036801c01e20202100541000f451811200c0c2030134120620b4400c0d01d040c1c001800c00c20006406418040008134401800082c110320480e010344540081d1402c02c0c800422900040b80c4942e850341c4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 574379325 1250 574378075 574378087
    0x5090a05100c02030d091b151e050c060f060f120304151418090a0902151e0315011808191a1302040501120f0204090206070f030806030d0f05 62
    0xe8141e000c0e09030b03519944192420242518208010345080d01d6041c0c03010f5054209540c5203036880c683c200000c101d40c0031508107248607000064007411171641900c0001d035112640c00002406001108d00f02c44044003520307443c1c81c00010300b4800110075074140e070141c170105404445504221822214030b039031901c000c6090a00d8442d083c00d408182c540d0140420040700709190040074000f01510380440490000b003030580c0060240000e820cc01003030010001e041c5140000907840e0004500385c100c0e02071aa0030340d600062510b030b032030780906000d0000d42030100104001c1a04129103140300721040c240ea40054580702d0150100f90381e480c6008095441d0420852034000404500f904580c29101d441030a000310280729030b40141c150115081d60f00441d541c1c00c41d00440c0350a00c1868050b0600e181304485119590311480d511442c0381c0b000038000c90f66190380c0802d542d02d91058481c07a507440720f1002429246450000d10740c41007a602d2038041e11412000c0410b4500070940e1440300350b803a030384041c1001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 574380575 1250 574379325 574379353
    0x5070207230a030b01030326011202040b190f03060e03030609072a11040b04060b070308040c0923090c0d080d06030c0b0c15011d0405070e0a0c020105090a05 69
    0x7418403101240e00c01805000040052001c1d084180254041d0b1620341d0b02644901e032240116200b4a171044004803110010310890640d4182035503c030390181c41c002014002d040100c0c02000c518142d00c6c11000d034203100000d1199054140341c2c1075a220b00001d0003105529541c181e40ca000544101340d028200c840051001441388001120103410341e06980c60043c1ca074200b4541300d00085506843e04031500441c1d80341800e0501a0000f0000113550801150b45000311001071409a50001010050328102142c20301070740c040081c02a00f0011010089074080300c00d18590342a00c1003400080c160a074001490741200450080110240985180303c001d0855540ca0015030001500b0074086644040c04008100024401c4000d42485c6032802da540352480d12940c42d140314030030070045140c2e10000501c2003440c0a6151144240155246591600c0b246031142c20002590800e1a030903201c0403c011440c2801d070040540c46010b60003c00c0f00c0e4507802240da89400202001a100f41e0118100307020340f03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 574381825 1250 574380575 574380629
    0x60308190c06090b0601081e01090c0203040317030118051b030406021b1612150c1b03020307031e081b1b0703170a090b1b100f05070207 60
    0x340c905140094810907180c1c1c8140c12a000ea910a0300c08034812420022156040200c07039801129030017043c4404102d001c0e004044c428140038425250f501c1d880c40902d014001c0060360051640032100c80509402c004144003190800d1048410348260b440c212044c9842a1240318000e00c61420078020028105910300301d039034400303481200c2c2ca5608001e0b4815000307884550394400c9044a000d0948500c11540c3c00c00e8140c3e490300050b4079500d0038516a400600321303050341c4943d40c515000c0450304001960080c3da140941d505031880c14491031440c0020190301200420341c89100351034080440e840e0400d0750492142c10502da0b00402d81450202c0c1e03441c84140b44548002d9030007400945851010780d064680c601c107161023f5043c1e40615428410030400040c10604c80e24600951414010307000c000424001b001d00c200710007811700103028501c514600c00d202d544000c1070b402b159490f208240d10ba10003880c0300c0c0304000c0014a0003021819142c400b043c000100e8000c8680090b18a942d11924607036 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 574383075 1250 574381825 574381867
    0x507050d15020705060106020c0102010e032a070308040510050a02030319230402090921070203030d0c0c150c09170c03010603050a0b0108150711010b03010204081b04060308 76
    0x11140e49109056800e01c940010291640b00e1001303400f040d4980301d03010717241c1000b4100c2a4190b90410712001020600002524180310041c828103011003c41102c2910078900040d80b02c1c400c0c020f02501100b0b1000150082044070b0003543c070522030b101c1420040f039260085044010040c0c008202080b5004c0ca0000c14020120700c1410001d00710541015900452050100149190742c040c0108415840d001d400329500074a0a0050214040112040c1001b01a004040310007007401095820039510100140c0d4600b2414940401017264082070292200b080d0180403501c105180303440c080d05090034068854046906d40707580c01030500b02110145003000300c806100040c03080c4442a55665000d0066600642c042e8000d03049461082c10001c05403041604800d41340c0d842000f2031b6401a0a13025800c2d40040c2901c0c24400010b818820503026020012405900d98004a400301e204000460f085080e224014004049030000348140420740780d80d40300c09071406401303001250030300200c1404015 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 574384325 1250 574383075 574383083
    0x30203031f030309090b19090e0114010e0403050313060203040605091e06010b07020616030e120105060102060a0207030e030a03020d0f081306270b16020a051b180f100e040507050d 79
    0x302c48644018411f8103403e034443d400141d119540614140ca081c414a0800720500c03111290320760521303880215201020308000c003000030000029002d4241c1842d2002c400307074481d40c207540d281000d007030200c0988810f4421032940e00400d0f503c0144d1008080d4004070405070300c00980b071503a05c1c158a0340302c0c64000d80da0a98100204000d400c506206d03020a00356514805d4981d485a06c84c410180f0001c0000720b009407a042e0316113024482181c2e00003402981c0100754076000350f600c8085290032500c541c1c040074035982601c01c0b81140030406030080381145041c401e0b907451065180d040d501c201c5004d801503400c07400c031451507017100d404280c1341e41003036a803c89207400004080f450002003040d032640000701590301001a505012403c100f00c5401e44840e58184001d000113012a22216111a848403100f0119000c119911020752200c2d0242c5041c40d807550206000c0d4941017002c00c071110030442d0040300b100b4071036001180b402c5c01c1402c1540039a400c44001e2184508100a025031100c14901c00e903 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 574385575 1250 574384325 574384339
    0x906010c061109090a06060201270b040303020c0316111c0b040f150e100207050c0f041806020c0601050a0803040b0d0f18110a180504110409030203031f030309090b 72
    0x1a41c039403a803800c4d090280d481d5840000d2817a10303200d40242190310f1114490317000086858001c5039050510740901d402c41d08121035502680f910314040d8020b1050781e0b05545a4040401e0000d4451007804481070b03210300983c82200d850348440300300084901ca0b2020700403100c41d1034087c5408a0200358041e5803140c4544241c06000c909921138500881d07600542100c0305440b800429504841400040d000348038600007941014456601c540d11900c51030701c0140511180307564255a6591138000f03280c440007141d1103800b07131809801c0500195000007810141da1185600014a034240454501e0484d00c6600182d820a410040da80126610400390030103430300e0f151140080243d4403407050411115030741411144403407480c80e10800ca50300d8114280c0c45602080b07000c02c000740680c0c00c01001d550400350000740c2551685020a800b1401c0342140da046483c220480c1c0405400200030345c0903903041011044489030200548071040c43c50700001307001491601e4100110062500a00c2201d54002d00e03035 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 574386825 1250 574385575 574385587
    0xc070303021c1d0d170106120621020a050315010b070305040305191a0c0a030207050a050d11060a0c050d02072a090b0901050a03121407120e0906010c0611 68
    0x408140e40714000400c280280d410090340681030100480501c540f098140f0380061142e03c185050150414807d404c00c0c0803005085845510706684001c0c09000422600416010b0355220000d0000f200c50040340940490140411545400200072aa4a00642d04441581c0c00d09034803414a4120800403418880140404800200144a80007140d5081032229581c3c404908210210300344c002c0c440400107111301c06100c051217020301104c0814060b42400342ea54012854075030f03e00b1241a001074254061000215003096110247d0982d181c90881280c40030f03150050310400301d41030311b8480c8011410030042a0704148460b00078100e914061903041e00e00d020036029106a44540404a290380000c164060000c68101d11824000003402d4800b002076604140100c0d50700d10003400050104610201031203c014031a040a44a00014410041d115403451500080007007840103540c0115040380c95003c0c49040441010b8805c4e44142e56070046810071342c89110050803940c8105584c00420441 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 574388075 1250 574386825 574386877
    0x5030a0f0e0901092304050a020f1e1c05150a0e030301060c02130902040f0c122310050307150906050306130905030409020a021510080d051309110a170c07030302 71
    0x45d0b644202d000b1000fa044d04c0c0800c1c410403481e6100301c114584170324140e401034130195a40c60160030b0400015500c14019002c02e01008070406c3c104140100144158101c46402000115120f8081c0c514044c0034000c100350088010307241d010074002d844c0001c20300002d000152400c0c0100d500c8003014150f0001c3c01001c5500401c003030300c140040c0c80c04115207601e640e450030b5600080e00e20b01d000038a0303020401074090101162001d842d042001c0100201c40010400c1c0744005100f8000400d4000c0446044d56660702002c40c91400002c018030100f180e003200003030424001c0c021244144030082c40a2804001840700c80010300b12800c0c20780d4507110502010030000c030284014021464541c00600d00c50018021a41c00900001c107030000c0081901c50403c80e8040000c4c04444013245800c0c4aa124445520407460107429030740625400ba0601314494018501d100c000c00c440c000c95034609075094278040840364001400e44405440c908104800c00120380700364098940180d0540e80038025140c0d140b0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 574389325 1250 574388075 574388141
    0x2040b100309030e030601050f01052208060a0e06010b0f0a02010906060f0f23060c0a0f03090305060a05011401030905010207060207050f0d140306280305030a0f0e090109 75
    0x803400d0100c0ea0318000101415000070551038a00703c100d0040c00150705020101e1031140f20401d0a9040c401c01080705880d88200c65040c080b14123124880755480c640d20040e103a9900f40581c0ca11002900c1c11178071098010011840758142c0d01455003003032520781c004e9480002a409041c101c000c5560300c00c00c0c1400503100d405140010242c50300a00540d900301056034a80001ca980300380103510074280240d0a0141c95120713085103040482e07040341c603404800c40705420543c0c62440101040480342c460410150002050404d90f80182e0442d61940d503502910012600203010700511040e0403808040198070039003200c004140b20380009030400c0754595070310b8240e0f00981c00c21034058014500c8040081000c00090182928914000401070480d40c41203c072071001400345406010b255440e901544940340301c218040c03800c003c650a007181e483c100f60b80c59401141e030b0f4000158030402e0714820207104039424140044c00a00a40380d5900c2e096000004007002c0c0c0d1400c12030b01c50301c1840349180d20003007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 574390575 1250 574389325 574389349
    0xe10020a060e0309040e03070209011707090c021e060f0a1a04020706020c06091f090f23010b0f0102062a040609050103050c0309030910030e0706030e0c0307180902040b 74
    0x2c8000c41d12210500c040100b50344503c0603c043c3c50307005000000250381c0e0035840504580886500030031108095806a0070103010303030805d14009003404c07106200d5590000d560004110181000464200240d00c90381d2100380036295a40d0310300c0c40340c0105801c10300c0c41d40b0410380d8844940d03113415000c054101042c240d0300000c10640b440343e808142000362081c24040940e100361a00301402c10b601e8454501652605050326a4000641e584101070400040240304011590400400d50340402d40c07040c907120020308480c4a041c04d50804035204801d040a41e0303a480744820503005003a05685203429400600c400b40c4000300601c1c03001400581c44011100104043e1020395214605030303003000c00150075510090124542ea40d010003c011803403c022065130360050080720782c104075154011084001e40350030710020306503000b0f03500c0c0041d40c1074041e4044510300041c4000e4801c8101140d08140d11101d941c461840300510741d40040405107440d500c41b25803248010800240c0d0a10b50010583c1c0082031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 574391825 1250 574390575 574390601
    0x3020c0109140615090c0705010626070501110a06090204060b03040b010915060c0305070c03021f02071208070f03180f0503101a01120b04181a0103030e10020a06 71
    0x8402d500b494206101c3c40d40d000061542e55426000780c00d01249440000038401c03104642c3c081a400c041240a400590040031940d0b480300342da03121400c03072070821084840c20101710303c10340100041e107500840420340e01d4050100982004d44080c0c175410060082072104990055036221701080e242c4551000d1400385000d9070b0401069030405e20b2810840c1e61115045c3c0d00c1d00d42840080288a0380141076411496051a009440d40740c135142501c0316113042c0d08002c1d0710901c8a541c1c81403890520210906101041e4204c681c000d030380e41100c03100301c107000300e0140161030300b004200c1c0494884039102c10624400e280a032954500365403074004141c050b40041480159000302000703546020003540f00382a4440c40c08002c60118004510701203592100d80e581481a030000c5840910010ba2145010400140060080e030342120a2800416010300013116444c1115900480c0c0c050000c19242c140c96054a030400d282e00c45c4801c1090044c9102600700c04c600c00c0d1800c40c400a0a680650b400c2c0c1040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 574393075 1250 574391825 574391843
    0x1b031e0304121b12031b0521040c09051e07081b13060e030a080f03010303180b0306010e06070203010c0903172703010b090403050306040b04020a020a0b0703020c0109 73
    0x1003481d10b804501840712200d410070074455510a240b80101e50b4000150350301c0008101001103112042d030261402842c01401c801e2403c0c1103e070403d4220000741503590203144812001d0001d290031260b00603060320050f00303000e5403400500070100d4030340c0400d42040c100c1c01829105400140c1022013400c0445850001032490021b104102c00c01da1200c1940d0000c1ca1a200e007003003a400001a803142242c480c0204102c144910407c190700d007404280e1040d41c0040c40c00743d40d21286592068070303900a03c8200c001520b4241030500021541503000c0a07200301d801e000786107454000044650502d00c48403c2d502c40d408000d88001a5024464080100880c3e201d4440705031a40c10125a400c034528100b684130340301084580c070308030300200e0f032550317603801c1400d100001090000100b0300626030184c0d403d41141010091105050304440654424501120203001d2a68a0f1040c4002da0241480c402c0250384040f481d01e0003c0c0c00500f605038491142e00d4011b080185044151303094908414040e00c440c29 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 574394325 1250 574393075 574393081
    0x207020901030f150903080f0a1107050102120115020d03020d06090509010f0c0807022109090c04150504050f01083105120903070303050307090f260a081b031e03 71
    0x1aa0b213240007001c100d6130004002122250314080c0602c0001080e14854607207070400200314110692140340a1980c01c1c0c102c42e00c0e8626460314a0003035110480501001603c0d42c000225030f00e400440641d0b140c850742c0a060452420001903010b07400100c001140183c507200041035100e07891085900ca81d00140011544454000c01a821204641260402c1060071010011820740001d00d000112040c0901000d0720104c440100466026107040303a94032034410400c0c00340314010200034000341c0d030140f0850a1650001c0e84141c505109903c07034150800302070281e07070141d58041d0021070740c00b08407108001c0b50f140c025080030208801c03e10039450409210300300d440600100b000010b01c4202448081881c005280c0300180d0345140603c0000e04120001000800043c13040c205080205440c00c040070005485450015082e400c000410240e00e152034414201120f000509500680d0040c408030304d040380181d42007210102090940a80d44020050100701903520f000c01c82d014401c1e80c2400b501c0707007 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 574395575 1250 574394325 574394333
    0xa030c03022e0e12011a150403291003050d0528020708120f04090b030f030c010b0108070503071409010c08030c0a030608070305120a0c020301050414010c0906050405130207020901030f 81
    0x6505880b02808580c900081e40c108540304c48030021001c501104d8045040600040f007026520036274200501c44006281420b08501d4070564450b10214054583c42075070351411100038249000b444040c1080d0310500030081420301400040c080b60b213907224a1441c02c00f4036814942800343c0f0140301001a40410420860b000d818440708040d58080800c203450100e0708001201e80d8003c5004962106548501c23031002560100f0400c0500044041503d40721002d9940040c0280990351000380032480704400202e01901c1541203900c120486c0d22064510009220001c5030380c1c000064ac6e5042c00750006e404000300b001c0034007652161105288050f80c4000140c1c0040c281d601552003106942c0c0b1a486c140300165020444c1c2c030344103141248460720b9441110741210320030304252010350903510b000244000d00c20030300e0003000c1803143c000083c400002c000e6001c684000c02d922400001445c1400184483e15191144481035070045070050b003404401c0e00015902003080c0d004036903000290304424100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 574396825 1250 574395575 574395589
    0x4110603042d0f02060c01090f060e0d0e030312060102070f0305280201020a030f051603050306010215011d19020a0c03030b040204150e1201050c0705010b0a030c03022e0e 75
    0x101161482c0c0161a2116540c070010440703500d4000b88545d40c0400c0500c26210250b02030f42806400a00030300d4182c1281c1006c000800d10171041c1c1a09008d400348042d1160300580c054000528040e008500d00028220000141c0c1805040a411800b1f1510009089554400f80e00044c0d4080c0003d0060403007000440c00d03600024144040b010b000d40c01403100980c0c0c0104003001030681506080154001c00d080480e001e00c9064035003c80a600410014185a070000182d845085d00b0b03000c07030f90400180c0000741c002c1c0109104665807800e0007005034880d01042040c0d43c1e00000c011022003529814954031209070307001140803c001445042c0a40140741d0305018002030784109480c01c610701802c01102c03008411140c4080018130a41d42c814000071349800d0006041e4110f410001c010b903080610000c2c0351030b80040380c1691198248000c1c0800e43c6004e09500d01240e9000c1c600050641c80c580c01e20203401c0d10107800500d19800c821b0034482500728255020400245070344e40501030503840c4108418 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 574398075 1250 574396825 574396883
    0x60c02030a091703030c130b130320031f09290f01180207080909090102031902040e01050904050f011505041d0c0f0604051c0b010605120c030411060304 67
    0xf500010214001c0c042000c400c49400945540846954034501e40f9121351104095200d16860348001601064940d40422041d064a01c18118440e5211502040c0403400d100303100c40607415048410b20100c1600517407d140500c0183d20320200f40d0389820f45441204d107620046291040000740c5014910541c0c0d850400d5000c0d841d0003445100d5414444001c06403101c0c505022a115030004049060040f001d096411945c801052440c00c0d00d040c400582c040e40042c1d80031460b5038540c0e140c10850380700c2c0c0d0080e1800d4462071084483c0300c0e840c00b820032504000203401a6510302451b0580a04039000380aa80310382d501200c0e441500a1a2100788400c58454803074801040c074882103403110b0144045440d118103101101d59491001001d40011200e109030f61102d640520b5034001036908100c01110400554003440f20b102c0c203686d0300e1009035854414981503494410983c4000365131445150b0103150024000c404009260346601e01184d00381c0c2c0240c80603030700710200c2c900010784110207890b2920 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 574399325 1250 574398075 574398089
    0x2070308091c0c0c0324050a09020603060f1206130201020606010c051b01180e160318030c110406090e06160e120c090115020708030f03060f010309060c02030a09 71
    0x50428000500104070b440d690350220100052940c02070144038094620b18041d50300b10300e0406096130340b14200d80c041011940d502c0300c0d0b00e0411001400c3e070100c0f4440c0515013500504000d2455480c40300300b0044409840b0415070110000824040644040100c54401c022240410100000900000e4030f00b2000600c00c604214084480354002800811401c2224031440050440c1111390001a900303410070701ca11182459400600003406480e4a07000340c0a241d0880c210800001c00910072400d461101c07100399206004060304000003840740c40c0c501074480c0242d2040f01400382100000d01900c42507804940e05944030102007200010a214140c3c002c1e1001341d4150300301c0440703074004d040780c1c0b8001d085500c10b90718081e80d2024482d041c003d000000d200100701588030760b15505000e0f0188914041c50380144036600740854ac1608c000111030803000e0340c9086505641d161010410307040c085508290415495449420004500303010300001a9a46d0300a59182c040320b29000f00400300b241c3c0011 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 574400575 1250 574399325 574399333
    0x602010b0f0612070c020303210f0405120f0c010c0c150501080d050c0c0405180d090501080415090606030309081501030f120219060c0305090d020d030203150a090207030809 76
    0x6040d680380d02c120303150340710b99003541c1480b07554040c0196a18130f101140039405000000b800411142003c44480c0422001039040306d56440e02c01400340b4803507048070014107580c01540042e90012141c8003a054002c2d110726171a14261600e848542503d003500ca515001c144654007070810400e0f008045107411280d0b00080080e58500384031030740d5807110642641c1c00d00000150590a240c0d0034010030051020140c82400075041c54501041d0b0441e40d295059140e0092041c0703180d0040c8561003550440e041650790305000c1d1650307100c2d900d40d084150030146d82ea540d00c181000000b9524001c040045011740c49007c04031707244c0300ea07146c1861100712580c05100d45501c014400a0fa800d0051145a90080345400704182000d00980c80c100116026052410303089030004100708064210010812103030b40c0501c03403500c8596841d0307078074070a101060700503030460354036202650700c81c0c0c2c09180d001c09507511900142407080301060900e48140c201c0301d0050340005904040c19007012203542c0007040350b4018 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 574401825 1250 574400575 574400599
    0x18010e03180f011e1106010e0109140f07050a0504150c03180b0319060302060d02030717040201050904090c17030c070503031312170d090c0e10060809190302070602010b 74
    0x200030220501820403080b13052001d54441500c5201d041c840a01c0c0c5000726502540c50b540c2224440b1801d11402400a040000c00e1494100c51107065003d400d40c1d1700e244099448425090f00c094204860140400105020008442c0380401c50311400c11240d440d074802000650900801c40c4210100c408011180b4610401c0f0315041d600880f60700500060b045840c00003446418005400300f42d001942c0003001141403505640c2950066004000d907480e610300e10404400c2268803400105c402170301081d010b00075814142440d401400c0c445200b010310007003054907042c8000032001448041c201503840801c00142d1031400300180d4014010032001141456082e10f0701d00071210340350040c4403100c5080341c0d002007005007082d030390382c1011403024032a501d603081e4150701d10080c5900c08040c0c425855100380091180800c1441d1800f804000400b085040d05018040e1242c41d07000e004010305104901c004042c0d040c0394142c1080d450700c41e5003e0440103142010003801c1d50090307210380d48610000004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 574403075 1250 574401825 574401827
    0x3d0c0c090c090b040812070c0e040b0a051501050304020103150504060602030a030f022a150c030f0604110a0302090d05121c02030606120903071401060f06021203040b18010e03180f01 80
    0x4146c404411080c650b0350303440c0d20340091004000c3c1d01480c107900c842c0003408104050543c200f445091000010040303940c50a449100d83d40450044501003882000032801551094000c4032100011840000b2800d6685000c2f50031141150710020050700040358015050360b141c016400c698213103007003d50a1400c483c540303a14014000c9200341c00c030400e541c04d22108080038003030a520180d1100b420082850b003c003500b000342d401207850b985d0b0041c58200069080c0340901c11841001003150903242000d24040d001d50003503005092150703016010b4403e0100190041084114100b68004656118014100d02c00428450803140545443c0140204421915904141e860711180121101c0c1aa01c50061707944c10b511078108040c0c09241c04250341c99a07820305411141c1110b01a4500e48149070391480200d8403040c0e41e802e00c400801042022074081103003d84155005a111060b091003034040551302c2c1d08640805400300b440c2e40000c02d000c492486040c91980c001c00b02501e10381d80c41455000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 574404325 1250 574403075 574403083
    0xc06040e01120309030516062007060e0a2705061507080f0f0a0f021204050a05090903160c05191512020c030a0c023d0c0c090c090b0408 60
    0x1c1a0b07180040a440006052003103241000454204064401d1403020880103031800215008580c081841360313010300101e810503400d15182c400d001021f801600d0800000b254150306928400c0c0e030240840002280450080b65172016201c1507a80900303940003407490300c0c02695002800a1f200d00d07030346e0100040b143c02040442d40f095910100803503444145006000841c05042160035103550042125200c058001d020b81103504810f0f001c81e1900c640102406580d0710450007000d0b0401c545030700c03c0200381007500801d500801d1800a40f41050500441c0d548841c1c00400151003030900ca070820811030810140c0c440110030b4039442c41d16901e09000d42c0da01c0c0d440040c40c1e0403081010301a041c038005035031541550090102c42007925656590320703000070b144038101c01c0141c0c481c58546030b905d40c42c00d952007a000785046a090346030410204120b071041e0790b050722101340803d02c0318603264140054264001c2c10007038401c8040010b4041304115006001c1d40c015084886000020042031101d21b0f4009 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 574405575 1250 574404325 574404329
    0x3190b0913030207151809180f0204090501150f080604080909040c0b03091006150e01110a02150711090405031b1c02012901080403030911030a0507080c06040e01 71
    0xc00c180d5404207580b070103c0c03401d64958452102c3d45a40c80a441c040d80d4091040940d5146150340020320076211002041111076143c1c00c0c0c24003040c205c0c8004001075440201041c5d66000900001c0c01c00c4450b01d8060a42d0010150301501f0190001e0a014040441900e40081d0010000810040c60300f9903416525104000000f48143c4d03205c4001000c228661100303d0107894024001034480c00d0010382d1030340d1740302524464408581010400b1680d00305146045032194065030f107001c0400c0d402c5006403505116252101514045c0003a1f20025840e40d144400c41d076006401750a607903941c6414900c80c00409410141d1003074028200380004550300100740d0300003541c10390030800284000f40180c0e00c0c00160f201d407032090400c0c4202c1d8044154041d030000b80307820b810200000c1c8000d0340c00c00da001291400c4601da03000c00c521001041c0803130f10a41c480540030f803065028000d0341d0302c203000013071406000c0d60003100c3c1980005024403641c042844140c07005402500c0c4103081c5030502d00b8001042d0014 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 574406825 1250 574405575 574405591
    0x2041407200109120c02121f06300507240e0f010905132a020f030406050d0b040e1005071b080304023c0f06070b0f040303020904020f03190b09 63
    0x100086d9903810754011859000c503821203100612505001d070100151429004005207850800a000c5907a10411100c00258900141049460000000d0f02b20007521041e40c10f0712a100c030102d400e0302c80c4e051100701d031150f012008041c3c4a2825009040403031400815000d480740d01240140d036600956204180c520446511060409501c2c0900040460804030041c000e80d00c0c111000d80218144440c4083d0125400d40d44c04a000c0404036550313215511170480025810803c500386858264800051800c0c020f2010507030410003400c1f80d1030441c1034001080311696034014031070820b401110300003052310041c0030200101600c0e140c010240c00001c10103809203d030394498801c00e420150121921203040003203000c600050110303080c0c0051002c01600d0092564900d80e41d07040c900b50054900980e40886e401100d640c1d041c4200030401405481202415001e2001650aa0b0741d800903200c42e20042c1c250359180d01c1c041701c0c07090f0511121409a040c1900d00818009951a000c0c0c01c59440350003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 574408075 1250 574406825 574406837
    0x6060603060806161e03021804020316030207030306030b01080d08010501020106061b0f1a0a0506041e0902030c0303031501020c060421080f030414061609120204140720010912 77
    0xe001d8007943c4461840c02c1003040d17803c2c102c08500126805a0252a00790b5107142c2040600700d41100380800c80c4800d03036481c01030300d9030180c01c1c605444c0320346c0040c05054420b14020034495901c2d958000c40070000c5e0400041a08001a09201940e110480c0c90060509200a102e80340c0390440c0036203070041c0060b500e021006210306e11170030701c401c5603c1000e80030350207180d0b20f500e41c1d07044868008805040d40c2d100c1d50b407030501c07010801a15145c00b422280b85000d0800b058901c484864003001400500ba040780c0500074080014529a01400a103104151640840d1500c21642c0002424072100100071071243e00f0900c030600c0100120807034000300c80c0b401c03800614510383c0c80c01c20001c01c0c0107201c80c0404800c0004100405c1291030088640400812003c40c1c2003511289598009852040300d18800030700d00c0701e010052806600c9200d600c0354000303440040c1c128400201c1b18030690742100c0d80b80108202c0004035044440682030306901c0c03c6000020411080c141e0f94802c0d50455a0700e40380e04000b8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 574409325 1250 574408075 574408111
    0x1e03090c1518080c1002121b100f0209010e0303031311060d020a0c111f050307050d230f0403020c04021804050f07110f060a09061b08010306060603060806 68
    0x10240e1070aa20b50007039041e804408656800403166542c0030800014007810710a40b03040c240900016132501143c40e54004541090003102202e460700380c541000031400d00c10451a946500d01c180318640d9101c3ca504000740c1c0e9440001c0001d82002440040320707001307520030020071000b20702c9540c040b40d503140d03c01c1241d100200c06900040890207422844415144000b034580a00364012640c4840284103400900010344600200004c3c4800b10012285034111020071081261050b401181c1c404e034103080c00784c00c00da58923465100301c3d0140344031040854000b020001001364800b2509a014400032054403081c546540e000791900030640055024507000301d41030070000105920a42e0340340c0060810003040c03500c40d03001d1002081c00d07181d49d004185440d00c1440031140108902d90b0030b00c0b00b0f03c01070440340c031000d034140b004019004064840594410310042501190038041c201c0120075500c40c00c0c59419410010100c500d80e600c01d205261414000304401e450228005512010441c400c011410f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 574410575 1250 574409325 574409327
    0x1209010524210f01020d05010911120603031303080c0c0402160b070509270c040503070618090905030c010506100903020906030a120f0e0f03060606070804151e03090c15 74
    0x410001e003000c80c54002c003ca110a00c007415405480c074009162420f010590ba5060010104c0e080141c0101083c0f0f010000e084101c09000586070708440050112464000902d1100004a001746c0003160756020018501e04c580c181040042e804076021a001c520b445900800404034040c441c0300103083c1080c45002402e0140038005407460400090400200c640b441c0080901c9800a040c054850701072400214281c100040107a60035518050018201d03541017840540c0c00700d600144003181082c0308040420800028020b408001703114a0046072103040c440c071060300350b0740000c010900502d2801003924240340d002014008490301a90740d00e0702c9846800109050401914002d040041d0f8204e040700e080d64401c84003003c10b20300d503a40d142d01d40d81900410019041c0c804401d070781030784000e001c030b4214902440104202845040001d141c00d540c0c0d14185004c01000500c0408201100c0003101406000c0c1890000303200d0700d2404010b00c60281e911b00078115181d0080201c0120178003510b103595 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 574411825 1250 574410575 574410619
    0x209160503012123150603031b030f0a090501140c0d0f18060905011112030114010c0f05061005032a032401090e030c030715111209010524 61
    0xa9900f0000c4481020151104d4910411881072030b050f2501c1400c1401456030030300301c1000c1c002c440050143d8906407454449904910304246021524003003040b8100d10041c09000504020105880f40c1c09050302c2c00001610307004040303050fa20044000c01c0491098100854820400502401c01c171101e0890240d00f101d5503031421003040c072651038043c40400c03041e070041ea407d011200300b40c0e1200705d246011500e158449103891081d541c01503080c4018007004041c810108940c60381071600800c0d1102c030343c51b07a111004a054003541c81d42c01c402c0c14040800c1c41000c0da10050003050b00105002c003102075800c60000d0b00541146a0070300030813941c1c0c4859809104034152804c0c1d841a820000c0c110100300420b2500030321038003c13000d1800321156003071180402038a29000d80034000d10b05200a80d1160f82824074401380141040c1d54503041e40452107000405400c04698107400948540382c003600301401c6900242c04031080a5104055804014641d40f8200303065105488144403a00d564000b0000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 574413075 1250 574411825 574411889
    0x2190f020418060504060906050c12060f030a02030a0c090f0209100e040b040914060709060914010302041d0a0b030c03030d1104030602030f2d0609090c1507020916050301 75
    0x1e80c42c1840184011b1040a400003188140240420400b980301e801840100340314410590400d02d640c10300050581c82c1c8041a10740c07016025055800301e60b40c0d640081c0c20301e9445901140c809072400f000f401074440600c10703d24520010203084bc90b003690040094031061012420104100a0001e501304588a9400000e803e00000e4800c1c0400c0805160031030380980041c10180641c1306180000d034a280c41201d200c5c0071591281c48074030031a82080c400004039601c20b40d807a03042c142c007040300250040c4520301201100c01c50300303e90400e078100313004148166100c501000f0321079070000d0940002980c003c02155252141407800003030715004d0f48101c2045000b90792002d0803440c40801040b001c06007000c0c500d0b2164201d09054200381c4030391208030f085d03030111011980030f170101c0c0e40000d6928180246a590800c801104540001d035085000410710210100710513100b09001c00e40c0c01c01c600f040c4d04401d800c0f01420081d888096000b0368018224001442185524a000900c0d00c01341e1403c0900d62342 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 574414325 1250 574413075 574413083
    0x130c020f1b0415050f060711030604060c170403050414030c0303070302030a1214010303110c310b030c06130e0f0415020702030d050309071d0702190f020418 69
    0x104060041c92001c1884514664407070140c0d061a40101d08100b02c1c0c0a908141d80d0018441c440380b00e0036005129039500f2900c404c41c5d003200000d00c5018155010001c5a108a10485021842c1c40d5458402400c2c001d14080c042042d8070900b0030302001940001c00e0320191407a43e1351900c02c000c05500082c0c0303440c1820b0015505030000081140504d035001c00280301a05103a214680615014620b2908448020b200d01540314101401840081d104400c07080d10f24040c041142e01c00030111001651340c0500103034600d014070301c6800c0285e10341511948440c0c42400003008120b0340c54902c001c40d8072b90b244440014421880000e1812900107400c1190024010700d140a22040c9041040c400003480192000d03a00d92070b4508044444082da402100c12460303020780501030070904080240da46800184c0104200c1c012a40041030013a107824083c048a500c51241651a0621050107400c204c02c040303041150840c2d0800310001720f201400c84544096060310006581d41d0060755a50404c420707001e00070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 574415575 1250 574414325 574414333
    0x5100306020403060614061314041113080c010224100312030f1103011206090203030c0a081315050313061103011706010b091e0d020616060b01020309130c020f 70
    0x3c001c0c0151507000d0402d40d40a450542c1c4500e2001d0708002d903601600380001205881ca01c800d119178214446d0014000384040c00200d03a02185150a4a0b07940180d1a0703055030b00b080000420664504001d0b603400c804003030000d00b2201d00c0d42d1800c44190300000003481006102030010484520000d04088021500301003440310704400f400005000e40071114003c03110f1420440c07214401c130086e000301c904a030a0440d036038201e1202561400d02a00c09144160307070502052041002d440c900b4800000c0382846141241c2d076600210707401e10200341d410703044100006150514140160340010071a90850341006c403240c1620745500c0e200025000402050b13102c280080000a01e04480480d03401842039068161440c0e6a02c0315404041d902031450856400310301e00080700581d01c5808080d84601402906c101804030154011074450307840b110200c3c0c21030b4a55010722080c046c45224010a200091000c0c614000381e200000e60b40ea40000b40c3d08214644d6030042110183c020004044a80e01071400d403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 574416825 1250 574415575 574415579
    0x5182d0105070c0b0a1a0f03010f0509100f050c041208130b12151c0303090507060819020a02030319090b04060e0d0306080d0c030c080708030403031b0c06051003060204 74
    0x402c1a40d0700c01c4112804980b40c00442c20a01146c0115041c2d403507044104100d001034041001025003c0e44540c5805541c1d90420300070340381a41c00341500c43e80f0903000410300b0120003580401218401402d00d62514506418010145000011141100e52040c4080001800c6003002da049d4403c04014104000003441c0c000b07400b0014001404201a10316401582039480f42d0751030040c104082c2c0d0480e4004d00070441003460100c00da0300225128001c0c500041d00154039914030f4503281641d00484049000f030700c1040b18199814200201e695170440c41941016212503020350340b4000a00946803000d002400d41c6909170460380140200d0303400c04503900250420741008001012034250351403950046001d090481030003405400200d850300001800d03a00003008089803c0c1820030421020410900514000304045401400e03005000340801035036400c044c9009001c40310081103010122052952120b0516041011a200300d500010082140e42da24081c03800d0725105900000d00e018400b00d00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 574418075 1250 574416825 574416827
    0x105040b04060806011205070905281403010e030a0210270f1b030803010302061b07060f0f03092012010f0207140f03071106040b041805182d010507 65
    0xd075500402c4c003030301e0714540158040000700c01d0381e10032240000442c04a1008200c10b0510440b07000803120800c01e1a11000031140f25060419441c3d030124064241802c0070444901d420311030b516442e01d00d0001985000145d00b8003a44034100d03410701c1613142d55a00c4041c807200500303c41d109140300d10595a042091070b00d1812400c80c0344401d40c15503d0a001405e600b01c118004009038017941d40110b07105003541c1c40d640c201310413944040350801122810b03403440e2184034002c00010001e0001a00c44c5800d840020400078100780c01240e01100700350030032a100010441e1410b0007100844124603003500741ea01c4a002c5103040c0040014120290700e4410a4a0a009141d0142c0004c0d0f224903c041602407900c005181d5801e4110b040320361036001000620001801c003500d440d81958090195400e1681c0c0312482c60198005a03c031206003400d240000000e401e05100b000d9110800e0401c690b140300344030071a90b40e9400b035824900c0c09082c005100d1a01e40703c490034140029240d8030000e000a1070030301c078 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 574419325 1250 574418075 574418087
    0x150f02210a0509010b0319110306090d080a020406080610140307230306330304120f021204090c2003040303120b06300703051009090809010e0105040b0406 68
    0x500318001c50724240110300a0181030003101c8900d0001001005c00c240c411049070a5500000f904a500320100a14900d058505000a504c96100d50010b0128080d120708041c12000e0002d00140001384108014422240c1140c10b064200100342e504441403041e0b08800c0c0d8038083c0d034241100864002104000b0240d82c0b00303403c8502c0c80031500c183e80309042d080c07020304a00d002c20f617030036580507010140894600000c2ea110300000c0004118160240c003103004923240c10f500603501510103a03180c0b054654295041000c1801011062000701b0702d80300480507a00c810b002d1406000092500c07913500c094171501c0b0304c0741c0000300206002401e030301340311031810799560b5801848103c2c0410042005c009001b140c501c1401480c41000d441286000c92120f80d40726108088551403012052440e14168506201c4e14403070f1060045840c0003600d400c00701c61404a00c80d4a510103038816082c607150000180c0c0c0c0e0010303521604020f0074089045084000140c9842c043d641040500510110340050020741c006 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 574420575 1250 574419325 574419331
    0x510050310150b0f191d190e0712060b041a0406050d090f1a2e0b030703060308120a0f0501120b220b0105100903150f0221 54
    0x50480ea00c061042294005031220401402620811a0002c03c180c2d90f49000806650000c920380ba031901c21811006880c2c0020f110300d980000303004c0c00e03818103001020760729502d10780d4003121000c805000400e011980d1801d21b0054210920b084004107540718080c1400071901031811109000e1640c50310504401908a4030803024402e08160403034100e038003414101c80a40c0d0081e136840707241a610203001009010b40a00c01c80342442850a04004191420074013540014011a4407160b400c008203040701170728100711a050f045143c0f680c4440071034840c04840c800c8648102d00952a6642c03210290001c2045500c0984000d800040386200480008800c0748200320301102000682095500e040c1141c0090040d00b0516510410040c080b40c00a020682d000005203400d1a02650705159410305207240c0e20708a0b00f960440d4010301191620042c1f441e2909500d14007001c0c05d41c40d41e15451a0000c1100300d174843c2d907642d030f000072190000c150115024070100d401019258500030320700c110005411 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 574421825 1250 574420575 574420579
    0x50604260316050c10030e07090e121206040501090b220605060f0421020a030305180604150e0904030516080d06030b0601020c1f0e011e02012004030201090b0c030d051005 75
    0xc5e2014010740070b4030419582ca14408000c2914505008005000786503c22200c100e501c26104107045d035956500003050040107410452200d400c0000500055541c11307000010480c0c11300e02c100c0041d880b0204014000fa40721140404034100ea4200312004050745c0d0805a0001000605001a01000300080c400c0b203442c50704040209410406c41c0c1920000110029030100c4100703020004207104d06d000d071400d034000b40d1000c855004803400080186c0d02a601205062200445201e03006400081201c00110b003036800030b83c50710306660005e10310f11642d00000c0301e00c00c07180441020f000115060310381042c84a403003001140d41304e0924807a04002103400758018400e00b01400f0080c00c10183c0c3c0414004100603100302c407003080c1c1064071803800040343c960402026000c1301b034950100d1486a034018103207400002d400c040c0701c0c03000d110002c1c03002032348038404c40200401c00061b60300140c1d440c2107a540103101c54652240c005018258454124500c080d1801c200901038180c070358404d82401c0b2001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 574423075 1250 574421825 574421839
    0x210201021c050403080601120209031b010f0512040609140307060603020a170601090b220e070f030c090c0c0b16090f0b1801020304080303010807050a050604260316050c 74
    0x1c440d005694084034000c0000e6805800310b41994020500f503800c0f1014a8000350504480f200401e19001050a61005031030b800e010202c01e030758114041050140152400e40c0c6040110248010704960103000140025902d0f06031b4130500a8a402014000c20000f0990b641e0781d00e14107001d0082c00030303400103910403583c4c0c640000343c11900c040c40d860920716800240c44660310307000500c0c0c0100049011240c0080311000e41100c0d000c151101180c01003100a00041c4105101305c0451414400c1c0c1c01010701c0f850603020038000f14601076908400c480d048140481c290707240100031035040c03c00300c000070b02c10b2070744a040c41802200090032000c40142e80ea51002c00541d50184420107085034443c4a14030300041012160b40d20602c1e21945085030180101c91400d03903030b00001792540e84240d0144945400120b820302c107070310b071011030080104012160a81003608000011850b04c02c401c20310105035400e9081c0e64480c01c0184183d5800001c515100542e1810390b052060320f0740e602a04861140e10 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 574424325 1250 574423075 574423117
    0x53310050a02030910020c1005042c04030c050c06040b18030111190201090f050c1e0a05040e03120c1903063215041d1308070c03051b01261321020102 66
    0x1c40c084100b0be071006010500031503612123413000d4840107080304050314540518101c0c041c00e510b421005100810b8800781c8541c0e00e4510030382000c45411454001d902c030380d04000014801c00c02800a0f0b40d51550541c400c44000040700d001607006000e11040204461801a10308051010105040801203001d03a400240914400d0080403601c03e4030701090f0748a41c0c081707010300242c00c055201030000c1d108003003220301d0840c01000301d20254100325044490190002201101e0310309001c0341d11250000b40c10280001400d03d102140107a808007545144442c50290001110b0480a1820b50004000c0c0c07071981009442c01248410b40d125000e11908408002a0800094692001c051213210380d2103200d20012280d60b190b250a5100d840c00340d42c00b4003c1c00c404001b160b4180601003d01c10072100a0022842c0c280000d03220152069603a0140ca80980300c004c00810490141340c1d01c5440c024010b01482034a00d081c1005404146020000c51701d8640c0d050b036069015801416041080060b032020342e0703 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 574425575 1250 574424325 574424369
    0x1030506150d02070c030203101b080906041403071b060e010c11010804020303130e01031a0403091703130e1e0118053310050a02030910020c100504 65
    0x403144280e01c6003010000c01140310340000907400751040d248a201303400b001907601d400091820491403031501c045c0c0c1c1e41d40e00011019440c40014411400766060001a038640a6102034481c0c0000304040d1941802500c035080030402801140c40036980820445c1d05842e03260100501951180200300208090140c2340f003166018202c50866540d211030254030300703204a0011079245401038803c03600761005202c045041d030416003491000e0300f107400c5c20301c0300fa602d14200505403100c51480c0c0043d500810040c0030200340d00c031060710152061251001e54001d030494616196226000141400c60001440410402c0144062741e0040c1d00d4902e502040d900d02c0a40014000d07020300c112800e00200343d442a0092175280c1255034081028980d907004503940420b1040ea050031914140840310000420802c41d00e4400d0807804a000145040c07410130f803800d04065900c8c401c0210399441469620005e0707100d584204a0803000b040080d1450009016058001d04503407c00d0060314040d410615034443c001c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 574426825 1250 574425575 574425589
    0x51603090e07110105150f040b0f311119022103160302040b0a0315030b0c03040b1012030c0c0306062c190f090203061e010e0105060703080c09030106060e01030506 72
    0x21b58003d080e81c503212401d40030880100b100d607000580011815010040340d50340d0502803a1021100c0401c403e00f0070380300c550400b0342100ca10700445c400e0316180b808100c0300c4400054a420281c1c00c50b014009041010090380303454050004030004071040483d680000c03000c07501441c080e02902542e07a84800c1540c070f064040c4e0095000340d42c040c2d030b0b091241020140c0300703402c081385501c4003c0308281c003e0f03140e444411032101e085801c00c1103808008284402c110b50084910f500c45c5824191840c070b203080503c0c1c0c406200020001074100a205500c0c041404008070030003000359800142001019503a000c0724038003c0d40c48115524076501c2075500c07115044202c070010300c200c3e5811080c002d0500014061401080400c2c9182045640c6011303036001620301300845801a140700070088c1b00d4010403500d0f84070440050300580c40d400c00e8140100b181da00c0300e04c05d4030140c030790508210803942d070707030310b141200354019458910750643c240f40e00041d00d00e0b00f001d0700d52040071080e0b9051281c3d0307072800d00740011 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 574428075 1250 574426825 574426861
    0x220803031b1c09030507150b030606060903011b1806020f150c160303020417070e0609070512013b04030f110a14011b051603090e07110105 61
    0x111050303400c45110444400080001c1e050040b0742c0c040003a5000403200c1141c1c018403080b4041000000d240091202903518030136141141d02091090400a001180e11400c0107070615005000105074a40c4503603080d040600c880001c291b49031a05410707640300a0000701d40c01c01e5004d000f8594000400d40d0351020544000015003e07000308003c00800012003002c900052034040083c100380f08030703a80c403003c034400d001d0401c0c040e80e800b42c2c95500304041340c91258104000000d00d0351012604021802c40501c4c0c9591101c0300f01e40004580e9030710041a41e9074414900c920402800711b030700114140b40142c030700815941036410244035450302c111442c001030141c000c1114150ba10140000c002274425450646440c006192402c155028103040614113100360300f0454110310380711444020a8800d219401c0c0a4a13840682d0601d03101c0040080c085110b2020b180540c801d80a5001041c14015045100101039080c07809502e413500e0345004103001c0c00606000115401c00000c141e458140e4030240007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 574429325 1250 574428075 574428091
    0x6020a17090c190801230108011415010302041715060409030e0d080f041205010e03090d030e0f0d0b061e0a060305180d0207030515070c0809030c0622080303 69
    0x2100d202c1c01800c009112040881c000034074541c01c400411507000c28041c0240824081000c0d403c500342104000d8450001600410340a07850300b860b0743d036154402402c15801c800c1d06416890001c8007140100c0c0603118580104c0c1d000301c1f2240b00c0c581d0381038001a41c078549007801600000141c40e620200000c0c0d4040304000b4001540010140a9a14007810813017030781e03803154054a191540c005642e40d000d4125034400c01c05408a0394012050000078080c01e8440c3c40054003551a18004038000341c000c3c440054050200701d800043c00050f603c6000c0005e03418000246144612002413420340c7c11080d080f1a5540940c01d007101450801084141e103d48191b0000d023800386c02c6040007411402000c00605208085152600c180000b03070081c809807001c2c8000782d0240c6505811410700a1602c074503e40e0000a043d451404c00c509142c4c014540c03403045500800d4555541d40d4080040d03d0a009a4061503002c600000c21404486031134040110308402080601c007195500c0383d5170380d10f0780421500d1003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 574430575 1250 574429325 574429333
    0x90909020904080315130905071d01120f05060a09031106060919180506040c081207060b06090a1e06080105030c010f140c0a0605010909020d0311120706020a1709 71
    0xb0303000802c0000070750b5000c41c0854509848241c02e10014501280c00e140303014800b6a105800340911005000380c0000c2c00004a075058911401122840f44d6081445200c559400c00d01d00b55080195a9501c6416142c000085640034101440766000600322404101c003c40c49450710722a103403001180c00d61007604000d260511030741d41c0c0c2004014003000501000e400c29621000450b010b50700c03596405c6010301400062180c0c2c80c1c1403500e803201a0194118028a50204100903042401e1904880c4d0705640150f000c41d80c90800000f04034603024181e10701d42c3c8969072410109500d144035885040088805c003104050680d03c10040d40c00010a008841e0990050092840715500500031038450804a00c0c003501034100e8007111001c80d42115561001d15002a03107000c061100500505000d0454180100601c248036400510701264214004041c4183c04c52520302c022028000b046090084100059451141386400002940080d5141c40482c441982c2400802e03c130742420b5115080b088014 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 574431825 1250 574430575 574430581
    0x1c031413030801060818010608030a0e06030103200604090f0f0b181807050d03030509070f050d0605100b0708042405160215120912030c0706050a060b0a09060909090209 74
    0x105c410315002000060180c64146c43e4000d100000d00ca124000c0c90032340d026503240c0f0000c0200419003526101140c1c41035209000500100c4c8000200c0101441d4044044408029460100d400d03406142d1080d1001807411851081190854004601c3c9101e10003007041150f0b52403042000460720b00c00c28441c2140303108006041800280002403186810f01c085032030455a4100049401501102c2107002a440e5070a1117103030182042a980900885200010b0480c24200814060181c500003e00110780f20b0b40412451165404010050030002043c00d03650340c02c5003014403030f69000e481098104901c2a0740c099423549040f1884904022641c4c0c3e2528003071502c030788100c03c0c1020f014143c0e40503100d90550b10014124100602060340200c0c0310fa4560310b460000f0f42c1c1050310340c40d405c6081e02000c00800c0703900e04410045601940e4813060001c0c107615002c000070010849504070040c8584005070344d940d210707000b0f0304003012245c050f50b599036490741b170b128500145c81c4454070082d0040194004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 574433075 1250 574431825 574431827
    0x10050405070e0903043807020d02091314032a010213030c090e0609030a030f0e07060302191407060c180311041406030a141c03141303080106 62
    0x5400038040d9044600c072546404441c2e40d85a01690380640f02e81c0005000c01c60031070002c800b0b821801418180074103821001c8103850694030401c090782c042c0c503000910101159140010895460740141c03201485107011610010542440b540c152001980001615024040002103c401030586012171100d40c1c3c220080c00031a1042c00c0200c5401e5409026131400b1981c105541170080d40181c0198009900e0400c2190464003040e00b05000340d002081008240341c00041190b403110403502d0b00044010416403110300815243c00d2141041c09003800001e541d0764503402400e000340141c00c02d81c81441e0480702c1511120704003440c0d800d9010041c000d04020030740703c0d405601e05002031309002c0564400420046004a041d800c21100c05000341c010f6461400e10b03100e9141c580d0480e05c8509000d08042000980e00d81301400010090380b20300100c0d808207041030160a0040040b0300000b017016110300d0029000e05000c104d0044d02800a500148042a81c0b4004102503901034403140981c0c2d0810300c1c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 574434325 1250 574433075 574433081
    0x2030d0f0c05060f060103060608040b04080903210702120a0b010504050a060509100810090b01050904080f070b010e070e06070b0a021b1c030203010e01141809160501090810 76
    0x900c040c02141c501d9480801e1080c40b089200f00e801084401d00761400c10300160032911960024003c00a840301008002010703400443d0b000340d004168191a07d40e0700700001d140001a00c407810341408001880b1000b0311240018140d11482120b21550440321031180e00c0c0c3d03030402050050400c20444004100504080e8032050f00710407645404521a512000031031000c0200384c031380e450a907443c0c081c1000341e05000d2040b031801c2c0303d00c041d06000804d02503e0348074a010042c0a49880380300c140000c6000c01005000300c0d030000d0074005442e51103d0150400080c076180c02d103c1c803201c44020100141e0349a21a0301402030950005003450f0070300c0041c1d1201010310380f00800e5580d0050b1300304018a503122031884144607608100004014607500038441c1111a003220700a0801d00d4014030042c0000400c900c00c070343c156180c0303c0d036a10110800d500020500850303541c0d21000c006110090100e034400c0804e080072444400034141c0326080e9100700440c2c60180900c581d00d580d070889031a0311892810760b0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 574435575 1250 574434325 574434347
    0x6090f061f0e03070f12021e030106030f06060f0b0a0c03171008010f090203070b18040203010b070501051308031f080105070201020307110d051603030e0604060f150302030d 76
    0xd03003103080341120a2244040074003410921004034203051101030301803400704401303000303000301c2d08940541d646001854801c0900c242c600034400c02802c2c600c2404081c1000600f518180d0041c006c1c483c032a681e0904059078a00e05d5000d840f2107045c010085141c010210700c007003c941d140c014280ca0004800b008550b074419440d4100c0401c072080c4d0b4004071483e15443c1c043d01685c01a04c08184991034101c0c1142111480681c0d072561905105c040405641d0109401c0119401d41e00138a079a80042c0e0502c00380d405100c54441c0d0f126101100109040e0510b81c0130742004c0d80708500801041d281e151b103c101010035660020182d860410005a6007501e410009695400302c01502c2d0500340c482d40c1031800d40b5403c030340d0304d00140c3d0301008000700c296204140594071070f01d0002401c44070740110b0300200507100714000155078884245d07080003098820b0341b2a404143c0034409170b46081c00d0500e001006440b00801e0001a0390400075081c01b40c4007074001c04802c50b0390060003081c080c0120341090311021002 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 574436825 1250 574435575 574435579
    0x41103030d050720010509030703230d0605090603032d07060e0d0207050117010b1308030c0105190e0a020d020f1903030813030f2a080909090606090f06 67
    0xd205445484019000d12030255183da01c1e0085603454809440201603c0101420241c3e030401052000400005c0304a600e5075800d031508005460f0358001c0602c4000c1d441400c842880400150700e80706445960216040d02d104440b00b90103a100e00c401c140c0c0d640180d042010148401161a82d40d1180c00300e1036601510100c41d1444c1010103640740e080440d28411102002e540003030b11a641403550601c10240600b00909040f0100220406088014181409540c100c11400101d01e405a10550303800c1d0001c2c0108000c50740c3d0380590f01811806000281c07900001e0301d651071510407580110380a07a54008549000801116405800308480d240c100c0b1016078000c40e01085405854031948000703410940c030391802f11142d51031442c00420f20040286103248801444000c040001d42c0703c448106880341c1c6181c02c0f81c8aa50f80c0e4152403184c64001c500b01c4080c07118600e020100205100a00702501d400ca8100c16903990340202592289400c03a045903202e10001c0006c2c0b50401440782c656041000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 574438075 1250 574436825 574436827
    0xa0f0e060d0501180507020a06020d060512011b030c020d1b020d0819030506010903061d07090b0a081605130906060b040509070905150702010c06050a051807060804110303 75
    0x80880858025446003008084460315980148401000100ca00340e0f10031030200c04024518058400a40313803008100001d2400d60001000240f10a00d81c12800190500900d031140c1040e445410038000c00b690010201075100303404040c48000d000388a20200110a0b40141a40f142038030310498043c0661f14030f6090700c3c1d0303024003e5005607c8100f044c0da1401d22691700c4503925011150302010500c1c2a40744641014184000c101c0142d900007001c1048a500c01000b007000811004078400788840c2d000700b0845d52180c801c002a80480702d81105074018010350704c480d625500c0d155a141c485070200c12010031141c20b58003c00c0182442005201e07440c18040d0300284852041d540c040a80d442e9500050f00d55002003000d00c01c074a03004000540041960034100000b0345048003044025425504022150300042010410b59003c1c29003014120341c0018108a00d00e0500050030040009461202e02403050455000d0780c1d02001585405440300c503150001c15980b5981c8400340c01e02000550342d05400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 574439325 1250 574438075 574438097
    0xf0225091b080c070c0b07030e0d03260f04030f110109031d04290d0506131202150f04150f0501470408120c0706090b0a0f 54
    0x19580305141160315804070001240c4651907008208074000741888044840800c44007000a49024002080ba100314408070f85840c03c500b81134402c202c600540b99009418400355008042e804030552641e5200b00e0300d10742d03000b4610044507101e036008880301071418400c440401d0201c0c0c01010320811046207483e00b081c0b8500400d0354a030a442c00d000044010603c1c0181107204040007000c2d1414181c010384080100b42d01d8450180141d42000092113415640c122a103074164603000e0340b650005811000700d03071300c0e41081c400c081c0360011640015a605003840800f81d51a51003c274841464100e40d21390000582c0711410a0481840094000c40b0842218a00381c1c002e40c0080c0100c1806800440b80051950325119400d403081c080801624400304202e1400a06800d00c8664040360750f00d9803454500c0c10103811040c0d0305078416500241c4103441030000c1c10392250a034800070006e00a440c01a40c41450f9180402e4078030340014055400ca24006000c414105c61003031700240400c110501e40442040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 574440575 1250 574439325 574439339
    0x603050307020f27071d1c020102120f0c0c030c01020303180309040f02030925090f0b0916021002090d08090a0b040f08240c0c0a06020a050c010b010f0225 68
    0xf00e030340450800d1300d201050402035a260000802c0340e8525040041c5c00f01b050000e4005204c0e2203007502025581d411443c82e50f800d40e4802c0124040d8540703aa40c03410b965503508000c0b04241d4004200d4802188282a20580d1604010503d40d11034901130f00110304580b5581c070101c1c02c07003c5800704804184802e00504030a0b80c1c42d40906154650007038070060f501d05007141214100858503010010002e1804840880c400403a400382080b175400400000d000108c1c10803030809000d480c24030703a500c103021505124010702c0d184810070b5000d05540803a4107490309914844c0507409004403480e070000c00c902c1d039000400c22581c0100600e1200808030707008191240d001070480c1e040354004040c80600300100340081e0104001c03a10100e000a410300c0c0010359070724200c6901440051035606459000b00d00e1540c101c1c01001800320b8203510100543d2100c442d010300621907080600880c0030b56082c07004210700d95014034845100d10041da4060f04007152a0703058080c401601c0d206e0480700e041c01c440005021 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 574441825 1250 574440575 574440619
    0x606040c0c151b05090315010b0315010e03011a2107030303051f06020c190305060c09010c0501020406170a0519020f070609050a060c09081f0204080a030806030f010603050307020f 79
    0xa0340f01e840721a2104560824580340000040200b0040807015005200000c0c124040d82e03804284100b409012001c0d03000122081d036640c440c216095801c0c440980515100080c13034040c9010207880d84450710041000c4600072502100f400d02c0e55030020745080c80440c0c0705c1c2c0c11485d400b060b17a103c1082143e203480c5a040c100c0307540368480130040e080785104500781d250060140d070002100044031310003c1c0c21521082d460300c07030103003c0c1c078040040084e641290340d00941076190410740101c0210f4031266034400160105c4150b80222120717008040000d070f0454813034410580242403402c2c00403001d00075200181c000f94010300d840340c18144203000c8072000070b10078001e51032010b20903405410310204901e02002900e065080d2401801280101404608400505141604109860703419042c08030300c3d501d0300902c05c91300200701c2800341d96000e85c1030582021410b1700460042d0119074940c08003440c014201c8195010060a43c1c00c10803195003d031421801c00c04804030000d00303080d600c4501d40f81d20180 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 574443075 1250 574441825 574441871
    0x5070f03090e18190302100b0a0509010305010510050d05060615090d051e030304020d03181a1918090b060904050f04030f030c0507060f110301080309030606040c0c15 73
    0x400800e040c03a01c0d0302c0f49024800d8018011203904e0b03410b2940c0d10380d03401940350098900319000f1180e4444210400342d42d8801d20400514014142c14001d503140e040c003501800b01181cbc2e499001c0c3c0440d00019950414000302c04625030488081d058071f4980104014a5051514203008095400c3c0036141341e96a070301201e4104e040c8910014100c104402c00700b1003241001030000149a0070510400016031100c1202e003806070b038107241401c1101d171502c10141e400a1b040d00b08265442c400040b160001d000c0000403d21000c608190010b90702d81e0440848209840740d03401c3c00d0031115641c003044840b8080d0400c43c075401004003490300703008200c4003003070403600110351150501c0c090348180000e05801612407409412249000c0c42001d1481102406611880c040107240d15980d024209014030350b603010140503902600032659039699480b802d65240c01100c1464407902030382c40803a060f1701e845d209c2e401c5c003200a40c403690422903080c0c0303413008000c840050001c810b40d11a61142c0d055138902000c612 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 574444325 1250 574443075 574443091
    0xc140f1c021909210201050a0203121005011112180a080102030a0c090b0f040e041a15010215060901050613033813060b030c191401080705070f03090e 66
    0x802c01e0482c0001016400c40d0303406040001c1364075002400d80300080200d1003d10340c080c02c01550b25618048103d00c1c62007500f0300c4a1040107110144180052054000301c2115002d0723035402e0409012489440c1c2f9144007803108800c1c85030402c1400c552601118824a00401c01043e14070381d00d0307680304614203903030040380c24540c4903580d01c01d0002621380015000c1d000c0d00b42003841c81d041610980c0301c00d40700d1203a8006c1440078884440041c04100f00803003503240e80075072084003c0c014201040c50b06000e00c00ca800c100d000d4010070b03580306494140104103e218080003010840303140d01c4d0505100103039200445100005502c42004004141100d08074000326040c4801a40b0b00344481d2490b50034920030400c13800260b0303903003014000b500408a1034070540d20f410400010340d00001d00700003440d01500200f070a030800e010046100b02030100040d00021100000d091840b520070203401150750711300403070701c0c000413070342c140b03c0103010400801c6c0b5500b48d2031190410502960301c0f04c00640c0204c404540c006 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 574445575 1250 574444325 574444357
    0x130f06060603050106020d050307052b0506091807030b07140a0c0c1a0901030b032a100f0503010b0705070e0a0902181302061806030403020a0302010c140f1c02 70
    0xe95140c41070134014182480988040801108014582d01c000341060f010000d01041c4405000c40c1810940681d08801c42461841642d421040e4054002120110320602c8031000048103000050000d0000307100c400c024141040c159030ba80040001c015105408000c4480340741003020314908020007040200d5141c80c40e01c0c038110701d0900b00d4041107030080400f003020070b1441480080c4080c1500c3c0036407402d00b00030402680200100f031425440841c1c1c8030550b0107006854000300c204800c144240f00e000c0e521002204049d501c10795150242001400004000300010444a51a00090078415105a0544150313030b98031840a15203000554482820940d291449030840c40c058981c4080380c1d08851550b003113841d20b4548040003405100313001e070281c43c00160ba0501030b850300d440b03201c1c04480100404e032030b030400c0e0030000c0d602c0300d0380d07a000c9000d5843c1040554045014000c1001400d4181c03403a1481d06075403c5845c0c0e4150414661010148059079440c808a80c0c0f0b07001400c07400501b900c0754 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 574446825 1250 574445575 574445579
    0x62703050708100207080904051e0c0405040e0d170a020903060f01060f180b0705010b100513081902040c11250f0308120c220e06090f0609130f0606 65
    0xb181080d10490146180b18030401007580082c100601342e40c0c028004540000706a501c86180c0e55540c0410802140b0090b0781c1020000007285800207002911001d5400f040210611600e05a4500c0300b01c00010201c1c840d83c2c00d9200ea80ca0540ba400c2c0c0c81550291302504102c0300c90302107440c00c5400d55040c444a501140180002c903401012610000e056107840405440201c1d0b011802c1d5115000d001c0580d500014410280b2509400c03a0036501d07805003040d180003d04c0d0100818980000d204000c0007902c4c0c1c3e10002e90b105c40002c131622030f2022200c2c03007103a0f4034041d4200070050448110351014404401c040681450080c480312058a200c00c0e0078804500309102039021000583d04117900038500104144003281e020401e0300d010083c07040041c2555150780b88410f1150107901d0000c04621100003031848409075241c80802160413996031205551200002c0008078130048a1170100c20054000140700c5240601003c2d070840e03502110200c0001680e220380c4284202070105444040d202e0000b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 574448075 1250 574446825 574446839
    0xb070504090608101109011707020f1e0c010804080307030b04060902070f020a06110c04020a050f0f0d050a02032406210103020315040c0e15060706090204050c03010f0627030507 78
    0x754502005c07584030801e00c2d100400d00080c040300c000c0ca00d20480203000701c00003a00c042c0204802c1c0341d60203a1200311801010124500d0f0604041e1421441351070007540c4c01c651322540654401030007a64041b00c254103541d01e00b1400c83c020000018295407054030f801d000a4100c7d03203403000f808080e0240101c4102000d00d0300500060b0240741d0700510400c9982c0300e222a0740036000c10b074540c210700e0031103015030795200c9414100c8030340c040e0322401c60694500291400f08000701900425210301601800d025a56540b0340c02e0040380012a60710007825034501103220340780002c091901c1003d0005000c0303403d1026006010040d441814180e440c1c50145900600542c60b0400c078820a400044923400c440c0d00c0c141e60358091004480c89001204071004002c94981460600c805580c1400603140396120411070402c0400340c00081410380c0510314040206450b46100c03002c03039041c2c0e40007408400c5003d10741402202c900c000041e408001105441000300c0b04295005240f00450146000340300490800744 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 574449325 1250 574448075 574448081
    0x90e160e0601140f07020105031003022107090c12240909020315091c0201090206130e160e010f0201090803090616020312040b041a04320a0b07050409060810 69
    0x10000c2d106031041c030481c2144d411200071508aa94280b0b40152203491700441408440d03042c1c0c000030344c0450607140c80001b20161007000300c06080701c00221044031f50b551007100b01711107201e0882d600044054841d0040313140b440e0001601c00046501701d51480000c0c0e69410011946908001826034941110702e0a51408001204001002003265096818050401d998600041c045041c580707505100c0308031070900039441000080d80150610365034503850b02c000ea02003102c1c1e01520301000481d90116400070903400005e60380480075101c01001d282200d005403100120b01d00b00d1000c41d9260719208001400c85c0c0c1c061801400000300510075405c011402c59203003401080b00c02c00310340c002d11220b040380d584130540581280c0c011240c1400e030f4446042c502e000601882184450f131445c602488100312035641340081800f02064060081e41c0c208120780f600b00384282c0c0080c5141c5c1b02800d401d0120300b54602c200c2c3c04c40c8450074098540b135581d10080d800c1d208030354804945900000c040700d00800c6180 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 574450575 1250 574449325 574449347
    0x6031902062817091e1608100509010902090a0e070f090903080702030310090506120105040506010816050a14060c0f010f05060d08031b0903030c010506120307050601090e160e0601 79
    0xd1003c0c2c00a181000520b6502d0528044070800340d04860540340104100748190480c0104007a20301c5c2e8816180d45425030707120741d401d040440c1c407031900001500149040c0f04031500d20b580108281565200c89180e803000c0c10040064060502402d50006500c515030328045008001c0508081610391080c1400790a078100241503000303540041041106100c00c00c811a0203598071000001480d88810380810000e05280e08112000e600c4d0006001c28400c000410604940c80001200c41e00c20f03002001d818084880d2280701d400907150502801040d0f15000401e40c0c0c0721015042608080d10506664a0071741101d007a080240d6454600300c0584c0c0040c01355aa00c0002520500403807116665030440a1000520070009e14a980c2040c8100010920072158031040041c00c4a8950242a4026000b403c040ea821482900040200e40f038650002c02030380e10300358008000c0d02d581da00e07005054000d0001c1e072294810764043c100c01725142413707000d203041c082e2a030100f0708546450070f0b40016020b80010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 574451825 1250 574450575 574450607
    0x605121c0305061f0c081c0c02030a021518070b03070801050109060f030509160902090a05030606010503220507260106180902130203040807031403060319020628 71
    0x3042000545902c1610321300d40a02440110508841e104115500104202c0c0104480000078041189048601410382a81e880000401601005081c00d907034070b1096a0440e0050380083c0511114840003030485070707000e205070f5401c1d24001c45a085503406c10241e0f4000300710310303103000c0140240720f5401a1411b001d40800c2c20701d02c250f41d00707000c800717401000b502c00b0302c2c0704040d00c5100054091905105500b40000e404d2510a640c0da15010130002940100305c100707000f0a1a800005410324001500700d000344010703100c03185140c8808507000b150b54812b061010801c45928000320000e2001c12202004003c01c8094404078040c8109a0b500400f0940401d420742c2e04002083c001d2100d500d00204035155034030400036440e0322910103c2d0b01004000718100c2681c1c030110401c014410403100808288c0d100e65280341018240001842441c0800d030b843c6901a4030540ca20445100400d450314245800207151a041c1801520074415992064103448da1106401c8800c82d416500407020601c09022 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 574453075 1250 574451825 574451831
    0x6070207030305030a05041119090c020105010f0e04170d0f0501080a121206080a0b06030d090312030908160302071406070512030c130306060f0e01060e0d03030605121c03 75
    0x1d192070050060002a1014460590300c60100e020040902c0c060451004043c00003201400608108868030000c1d00c01c150341c01e410b00c651032844920600c240780c161542c507048142e515040c031072800d4011f08018803c4410680d01c030102d198039100d0300d010709003940038100e020445041422540d0141e07007060b404207030b196010b80c055600081d20600000c40d041420b1800528030659a400134002d04210760210f94507014200b03d11050058cc04d40e11849075405400f11002d0715440d0b1070882d225905484068100c05102102c0c81c0140d21a4000d41d00c4240141d00341c50402c0c900540c545001800024200d016a01c040810021a0b4070020808603000080b0b0302d0b181400f140f5295143c640d8042c064590f50700c0800400103034078500400030396075a08401c0f008850710b80e89034078181c801410940281c0c41980003200340040d04050030001c441c1a2409a52209809491101407004c0e09440603400c03014952904008140d64849260710a02003480300010040720a180100c0b43c9010340514107082050700f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 574454325 1250 574453075 574453079
    0x30706050c0d030f060f03050f0106081609020711060d0c09060201020c0c010806032b0315270e0d020309150a0c02010f1e09090b040614121608010e06070207 69
    0x1c40814500000031050901082c50100b080c1c0c07100040c44250000010590f284902005000001410320100400900208466912402c04559461004440c0c080b0031040041c1444000695005421410300c00c801044615030804000307013154000c0030081314220740d80c0015804e8182d2000c004001001140001c510b410184000641c58156041e840d03411300c500392001c03031415101004450903075841442c0f14860403400b20b9010351103800440b400750019090404c00d00c6211041540314049540030300030502e01714642800c1008515540c49a07000540d07851591407078040c0c0a00039800040115400303559100c540303204104006540100c000302d80803082c03001040d42034000c44220b080a40908200780386c210700d8001140d910341c15420307654103804028140c40e0480d8008800c04143e03a54800305011581da843e0521044503600e10541c0440c0100071941142070618840c0804040120002c0c2e07003064000c00040301c4280c08940c48444140e42d1074543d0b480450041c0030300b9421100a2000c0d280043c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 574455575 1250 574454325 574454347
    0x52d0402010e0613031205090907260604090203070306020d110f030c0f070813050f030d0e10090f08030a0306151e050403050d020a0c0b04120f02030f030f0903070605 73
    0x642c00c9410a8010000024661040304201616070b0007181d0080840500c00e1002000509982150300c03543d00408e10701000c40c0ea09070040c28400c40d1540d2004190084440d005000369003103001904260700240d0b01d8201d04056101403082c0009180a8140540c3c0c41040d2000e190495848561210081c9414001640c10480046c2265001501a20740c29110011450b0780c0d20f0304c0c81603540041c01b0210004103c250543d030804004c088800485006032a01d18010031300d40c035054a00e6080e40010b507001c41d80c04440c50007000410507500c2511f040d48d0450f41301d0068848101c0550072604840d031020500d0716280b035050040f6405803040402074890b81840e40005406a11a0300910b494140b1012003035610310712800a45008540000880307240550520000e51550498001039900720000d2001081990b011021182111450f099500b034465050302c034501440780400089a142c0030b00240c10346a0202000504001081105581ea03602c10580030145003251a60141040c4242030000e00294 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 574456825 1250 574455575 574455587
    0x507080f01021e03041106070506090607031a09070e180609070f0912020d080706090303050705090d02060f1207050406020f150720010f0e0114060a05010f0210052d040201 75
    0x110074003243e02c0d85a84035481c0c100540019421100d0b007010340400c008043c85000030b581406502050140d5806445a80003141030f5607100c6001071603518240354131301450806030100313540504e00e40f43c40780400c0090800220b11303075400301500407107842d80c0040c03142a280640001b80c2284d2907003086144008803410141c42e14560344180a090211114032000f03640302c500c145a0415030000e1010381d189540e1501c0d000415009400380d0001c0c0c81c2c0400203250901400880d07950440c020003585030402d01d40e0170400341d40d21016948800c0542032100840ca10500e01c441382c080c078901e072501500c3c0c0c0d04003200289050003034a8070154561203000c51091202c00c02c0c22454000d080d626149003c141c0005180d2149080d0b020740d04010340c40c1c04840c070890b0015030300503a0b06070360a80007404180c80901034080720b1581603500c40c2e44521410070030452980640f2950040c04c9041c019201e191a0380d03c01c1340c086690465007011207a0410314a48007412950b21203260100c4d0450004211b810941c0000b010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 574458075 1250 574456825 574456867
    0x50c090105180709051809100b0a090905120304050d080703050106090909020d0507150e03120d09140a0807120302180f01090f12050607080f0415180507080f0102 71
    0x2d02d803141000308800078800d908a0010f444d0141541b44200c0c205c00c2c6007880c2036403c5807104c010f80a201d008851001c0320b0702030307240b0780d18001b85131710340041c182400c07000182007034001210507100b10340309010004c1d111806940304600402c06001c4217088120050400c19000340000300b010300e03280041c405e45401404800c01d4459000300010745644030301c0070442d54080028060814414620006074101d00030b4000c0b960b000d10303640d030001d81e0140c03501032603621603103050301d10721904c0e090250741801c070781d207900c1858440d02640c00b8030b81c1400e40540f41c03030400807101d40c01e945141002400700140070810070b0b0949038840364a0114540002c451402c47c010341c0388502c0070300c1408180f0050030140e125406980c050108010200b4a207691100c07040303440301c00b1190031143c50241c0ca0000d5103007401200e025200342001070510055030744035981d00c0880a180d08401400c035549480421541e20ae40d80200c0c40544a940101001400c0c000b009240202050365150241c0c010000b8801100b035034180c1c061 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 574459325 1250 574458075 574458109
    0x31a011d101202060706050412030606020102040b180d020d03030f05060f0f130213080a1403120a0f090b0c0306030601080c010e301605040c141305100c050c090105 72
    0x40c0b02c8110300c0021007510030500090461400c0405000c14440590421030001003280c404020182e41c82c2da0a0f420b0740614030464054600a002442100c1602c2c0c0d00080c103224000d199038280d54096000402c0c0612405095000a42d24000300117810039500c82c0640014045852104400700c0100040d9040c110421041c01031102030908100d1583c550151482800c0c1010384000c959111154103071342d9240900181c441c009080c0780441c10150203c1182c00e0316940b60a00400d503a0b8503004000508943d45200c4101c4e90368100440114404081240c0901e0300b82146640d00d041c003e007014034101040c1c1021500c4d030000c40000c0c14070b80c2c102050314442607003a28507070b00714130040000c501a154080185805142e81010807c3c8080e0046000000c2108851058001c40e4880050004880034000c1c0f40c00400c50103072026060307850003805481c80360318001d034003c101c0d03480c1d0002c02c0107500c00b9449100032595103600c0c0001c004060004121046003505e61044a43c58040042c00315801305090361 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 574460431 1106 574459325 574459349
    0xf13061517101502070909060515030607020304150c060c0206010510090509070302090d060c080a1a03030706051806011d0a0e071707031a011d10 64
    0x6400b0746110041e5822031810980c40f801d10112600700c0303400354440c030300001031000c0c00c90045015403482600c011602c0d00300320203041c1260081c00f80c004e109400030300130801808e030300205880407a100c2040303000f840c1181b42c40a4500580e00d0300043c00d001d007000b1910103402c0d0005491812180c00f581c5005000c007a400c41100c50b44058003c20780c0c80300180c1d0105020510030340151290001c020302c614400d110559981c0304481c80c241c049800308003003408002c15080c07280300e03c03440540144040080c1c210086d0000352203100d030340d0700140801e64541c045104001107802010388202500104c0395207507111144105885102c2d0031341900c003d842000a001c00969000b000c1c0d1080100e402442d469003444103400c07040c112941503e00d181304090002020581080074030f4040c03900b0891074092541000b84c50319040216030720782d007404031104080c00341d0b01e070280c124001101c10040d040 = true := by decide +kernel

theorem cover : BRFrame.Cov 574280575 574460431 := by
  have h0 := BRFrame.cov_init 574280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 574280575 ≤ n) (h2 : n < 574460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
