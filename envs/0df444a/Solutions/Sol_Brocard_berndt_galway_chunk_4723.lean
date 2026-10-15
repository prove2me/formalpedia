-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4723
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:31:38.787989+00:00
-- url     : https://prove2.me/submissions/38b5b051-ce18-40b7-82a6-07601df406b4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 849280575 ≤ n < 849460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 849281825 1250 849280575 849280609
    0xb0f03010503150106020303010e1003061e0b040221060f1206100909080f0703020715020a0b011e0e130c060c0201021c02031b030c0304060c0c0e1b0a0e 67
    0x2200400a51508100003a6070504400302c01001d5450028003954038001030141d80a010007100000c7e01c0810030b040d191000f19001801800300140c054001c104141c05824180103860034500c80680c503041600072103a02d5105c1000a00c2c0042d400b43d005034000b18050b1007568089022030740c20559950b40300b003038030503060346002a04050601d004280d02608145e0b100e9800541090391007804900300005948020481c00d082d60382d2812985001c0b818040540c01070801d514150310840405a40040d91012551284640507410b9899450f060806039080c6195003040d15808428409071401d0250302e40c004100d01c08222841940d941c421810380115048440001c40d00c2540406640e030420404088150381c0720525060780070024001d41341d03c540c110f45120f078110405c40c0b5070709032010800c03034040c25689400d90341c0f11a1104001072a4240141c2e00b41d8004101002c0402e442c81d080a5041c082c20355480ca40e0350520b130140d0350380855004080c2c10014426229014034442e2502c800d4134000ee810 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 849283075 1250 849281825 849281827
    0x1418040f02130807090504030906080403051e1305011b021c05010e10050f070f1803200f0603010803070b0c04090c02010e060916090e01020f04180c030216020f06040b0f 74
    0x8007000203141ca0113543c41000014144000e00001c650002c072524180e90072407401400710364890906a5592040240068020303025154a00c00590000c0c0a84914072008501540440d6250b004550045442c0200c66005820301040e000624080840c041c8000c80b49d00c0e03061800d4480e442d801d00316040f003c4d24495640249100f810021400e21070301340d01c00756400941c661428590f00c000c0c86000c00504200c18410044209541c0e018862541130095904c0344516455400c005002401c03c0c1401d40d0307041c080c1d000340d40c0e0345965103002c0013564142c94035a8001c1d0b080903140d4980b42a00301d8007070210440d43c171042201258201c07041c0a001c2a4050f250000316010b02901151890008010070003161900a400c07003800000b02c2c1102c810848000d0138010030300503d50500b440c0280b00b41c01014015480000f0002010b054241c00043ca20042c501d04100405080b041070303040c1d203c0e10b19042010a10461036a0041c94410600c03032591502038206401e0944555406015a00c41c121030100100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 849284325 1250 849283075 849283079
    0x60d0236010e090c030a0e011104080a02090a020f0f0f250c0f0617060303190c03030c170105130605060d022701020d0f02010b220b011418040f0213 65
    0x40c015600110204050b00c8900703c3e0b14180648a42038080500340d0b140c001e07294050250100025008050092001c8401541c2d40c0d980300100c5035079050350101280110300c2180020320501d514801d4520520300703c15018501500307200c074510654040840c202c60f02500b403007022070090202c0300c00e442840c0200ea00b6030b80710202c1d00b840e0720407009507440010142400c110502c01d0319030241040301c0b804001e0880e500c0b9a01c64500190440c00340c6a000d09125440e4401115281d600c80794960895000352030412001a90482c11684042d86c11203a601050405004000d030b424220031100c4507000310754000036101c2c1c807400081c4050303024940ea1004140c0204500010001240810b146c20880c030307090002108043c40045c1d01c410b8101d0280c001d11021070010740907071b07000390810380392000b0041c408030200e1643e44540710070b4080300740803005e4186440004142035001d4194201c1e100b04100f039050821071012224410081d12440700c64202c1c3e00c580140c01e04102d6400a0201040780044041d0003c0c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 849285575 1250 849284325 849284327
    0xd05210d0f060302030706030b120f010b090a09030c080f1c05011d09070909020d080a022d151506041206050c0708030a0507030b1905120705060d023601 67
    0x5888001240c1d5920300d40041040140d400103442c60444030380c2e08006c45e400620310000340c440000344500780c441b401303905408514001b047d4466403011808481d10350094841c13030741000468011220003400b0411030705402010800480c003400540e86c0094450f403a00304901e080a498084211000700c1d0152282c00601900c0c280340164000a040c0e9511011f00303141100443c0d5440f42684290b03010715075559900029511200c0c55840600c3d0017a00003a5070b02d1a0304e400a50703036001ca585401c4402c4001c0d08004101201011603011041910000d01e0b070801140d404001c1c03108080c00c0c00074006401110989980c80744c00160004002c50010001d00038103030b00700303807040d12401442e8400f40306040000c540029a00c0c1306683d002a41e2440004072580c1e9040700b640100961300d07025501290074040703071400725009940501941c1e025508d00d00c400043c0c20200f6510301c124005c065000d0400d0000e1242d103181c0d036010b8a0540813075840015001c0304800c0c5601c4d000b4040d80c0105421903006c031010595 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 849286825 1250 849285575 849285581
    0xf060d1b0515120c0306010203090303071a01090b0f041e090f0b090304150318080d0e100b060714010b0613060207050306070509013006030b090613020d05210d 70
    0x102c000c40c0d403030300501007120061800c0040c0745002501d030200208019900c200240c0d800c041c40541101c0d621101418031090050004c0001c41580304600c0001c1039110a502502a0350400a400e0700709545000d0f080201070100780d40c00800c01e001100040c3c03d41e0032240103045509008454548050a1500303161040c0c17280101100b19583c401c000400c070f4407003148400700d42c0310000c1c43d0015054a84804c1c0102d0040307652005091110082001d11414605612140c41d4900c03030301c229241081c01489480a452542202c20b034402818005080410050307281300328260540f500000b03414444c40d00048154105143c00c5100b02c0f80d00d042804a00e404002400242100314004c1c0074030724003900010414815085418100402022203c11045030f420324050305007044119900c010311036040c00385c01800075100545008002d000880d5410a021032200c0c010460307030002c1420301c1001d400303006040443d00d400700d41c0d902c58010941080507031071405022040b200030242d6680c5d009031160500b5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 849288075 1250 849286825 849286849
    0x6060306050319170309030708030705041701050103030e13060b03040b190b060301053003190e0a03021009240e01110d0e15211803030f060d1b05 64
    0x3d40c484012000012400c1ca841101c03101055401030343d666a9000403c5055004400c00180701000100500c4540b41d0014050020b403041208520340d04103000000900b070b542c080c407015020907a444504800d03410040e081c1c1e002c0c00704e441000b24580d91303035001c0c903040c5070700c03c0710f056800101c07190512581e90700d462180d0032441c8200c4401d110704010b20001a00c50711041c03041c0c0748980120243e50030102541c244840304030b500111600c181d00c008103c6251030b54400d008040c04004846850b0407484c2c00340c001c0c51101c14000d0202e100660a503428002c0300713107980a40405010602c8000291600e2186800c1100c1011184a90241901c124041c0600c2c1d1820f10700c90501c080740908442910340010000048034062030000d40003058000440c080c3e0705104440c1e00300550000340f5401c800080a00390892a00b028079441107030759018403011840d02c415070b500455420400c0480d482003143c1c0342c2290880401403174580345450b243e0b102003054408250b40740e6017602a0108002e5407520036460aa = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 849289325 1250 849288075 849288103
    0x5060601110604080f090a1502060f0709060c0221060a1506030606051c0e0d020312060105030c0a111609050906010b03060d030c0f050d051b010903050d0209010e04060603060503 78
    0x652410b09a0f00c4d01c180e030007a0440b132900e00c4008181c0740c80ca83e50f1020100300426040c1480b2080603414a0002d498a02c2281c00480041c891004112080d00c221550422240c80ea0303903449205560f0360810490481220000010482c41040440c1841c0244810340c041c400c036040c0040c40703a6130690303001810a00e03944070200b071501c0c0c58000c11034a50000704486040c480301b00b04010040c071802104004112500e4001c116100b4892000b40480d0004000d00c3d10901c10045405a690340400442c0d05200482c2c5010300344406000c080b590a000b802c0c1003d542850384242c40c0d509081052030020040d0960010400c99260403d2100b03088050204a0141c41c03d1001f00e0720f1072a00901003551180a03031801400c0080d03801c2d40d5000d020840d0100d18030654010141ca1130f601c2061700c0107209400042c2c511150b415049802e0006290522401074116415180e00b41010f81c1800f02e5402500031500c110305026104601802c81d680d544181ca010304a680c81c00100c040c142801d0510f0b089200c20345407 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 849290575 1250 849289325 849289333
    0x602030409061d0429070e030712080a140904020a050406110a021509040204050415030302070e06090406050604230108071d060405070c2906040218040213050901030506060111 77
    0xc3d18201d040c4203a154040c1d000040c840c0d2010300282000800c80ca15419600d81c42c0740c00b0180909954404110306014804a08960000ea2134451007420448004001414008200025989103000740101041005104030540c2040069404076090740d1081c03c01d40700140c1c0008040c0300c0d10b0f41240411001403000d800800e401f0b4465070109810b5040070189c0100d00300e001c61041c0e05952550100c601800000c1d000b030166082d0800c1c140c40f85401400220b01500940c0b2001c20501103e510452180100401d06001d0380c81c0e6488150042c04050101a003158031441c00310040c0780c5100e074562400c0d80014200e00d0f0b80d13140c9075040b030603d1401c1d0450103045400b0f2100c1e4146081f0381c0c00e215040328044400041684138218151010300d005000207003811240d072140b18a0000032800c22000102d00781c07910401d990350408010881c40340400b5401d041694030010741990401d98050291f40d0640c5010300202600c5100040c40d81000740d0003215103038004410051b071940e201d503d907140124608020 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 849291825 1250 849290575 849290609
    0xa0c020d0c08130b0403060603020f10080f10120b01090b010c0512181f2d031e0e071e180507050d051e090601080705060c07080304060203040906 64
    0x410000c401d00c0d01074042c08000c120303e0126640181400d0051002d2801c0c59602d90341da1074200c000c3d0a051105034842c03041d691003140355042074524111070b0041c40e5100680c0d80c4d00c14a000c0c1c5100030251160356884000d000104025086015298585010f420401c2c5070758544041c1c1d00075141c0b0420703020704004d0702c4603d05c030016000050800026500101041d1121480d0201e00140b891a90a0690080e18400108180358880340210308401156031014800c00c0410240070210765074018a0904510745110410b080e807082e0f03c107940031072901001c10703a40046099a0001c0c1d940d6600c1813403032034004013000c00181c0013004070581082101178400c00754514100c142002d91413065000640700d40c40f5000070700030a1084048070005003400508014504100500032900c28003c2142e107010504640861003003000012603034104e800841c010481c0c141080203109294000c1000c80300f5500c14003001248a00c0d0500145c40501410b034020340d00c03039103451820000d0b590554003659204c00c0c29014 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 849293075 1250 849291825 849291827
    0x10908030702041d070303090e070801030c050d11060f0a031803020604080a090b04030605070806091603020d0b0a09050f0f0702030901030c051c05270d080402011b05060a0c020d 78
    0xc0d140c041c1c1d0125000203494036015820090005800c00d4440c0750702848034040101600149280705070b0700407440c4035040d5524003a068821510a0002400018a4000800c00e43c40c7c80d402030307980b26225100342110047c0c20030201c1d8064000801d03030484a20040707500350065070315108134030014094148464404565440203912400d020300043e0941000240b0401034500410300d1a0080a100814030395031b6a8078100b0500414041d02c800740021205004a040c074600074081d00d00600c207142c815400c102140c003061b070080d800f5002d8440e883d5100c42500d0003641d1f444d00c0d15401058420804070741450b00f98a00b0901240042100c0c244108134800e0150702030780042510700e121000c0c01c00094029181e401a903e40c0150064400c1c0c180c0007489201190805400060140c103c01c0c2c107481c0c052903540152500e80c2d2540401856650044080e0701d082442260050741050041c1084041013038034180c8800312140000c03064032503501c808140304004c511845034041d4500c5c284042d0600e00300c4010 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 849294325 1250 849293075 849293077
    0xe0411042303070f0306060e010b0a020d2a0c0f0501020a05030a0c020d05061806160518010311120402100507111201020c100e100209090117010b0d03021b01090803 72
    0x1c0010841c009040c034040c15102005094090005030001072401c3e40e680c50000e010b040c560190004420700000005010f48260040e550846a2500a04400c600910b07003180d901e43d4a440e070303640c0c0c460503100700d41064280c903100c248070600404009008034103200074540da01c060f03580310904552040d07560303102003040071080d01e009882c2c0d031401c25110764031800014065008a1030140050082c0000e00c900c40300d41c80d0103024100d2201d0306940a541d1130031008020307591444c030b0716804510f00708540404100b10500f0400c107004141000908806003580909442e001840c58030b070404564001c0c0015031410356903907003070a4120f140c25850400f041c0d9450441c445008415401042c1010200912110a4059a104030740c1403040b21003601e64800c040b8007500089803000c40d0750241100ca0034800c507080c001c8409110024245185a0340380080c64054014048001ea80035560b90791441c8640e030360003800030f08280c0030741d0042c1010017204280190311107250690a05100c607803c42042000800300c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 849295575 1250 849294325 849294359
    0x1e020a081606091403030f01060e06041e360203161d04020c21030121030c0f0f29060609120727021602210d0e041104 52
    0x104442103440c403180b50900203442c03d0b8500502145010310003601300700c4000040c510541ca08000820325980e03c0c0415122042e1200e551a04060204800d21280c0c52809000340c426105250601510341c0d205941c50205c10a07440028080e040a18103500142500d076420070f158081c00c000311700c1c5007080346848024240010a01d001c1c8881070034010341e0071030007030900c15014802610547d642c1000300c4082c1d4540c404841030400c18210b40034042c0004c4d1090003540e044c1d0304a106c1c82038100c0c21a002c0b14a580184132405c804000c1400f0315040082c2c800d0b440c0e110007601c10030103000112024500280a400c6140d18071501c40d040c640c0408941242c006140e030041c000303842c03040c1c1d15003891000c5605607921501240e018455044000307481034966008003c504503442c000905024807036110000e038400c9032402d0b10800d032010040000743c980603010792000701d24000170742103081101040d40d042000100c1001c0100e540100c611145051500966020303041c0842c06500d480e00703000701c8040581c456 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 849296825 1250 849295575 849295597
    0xf0c130b030a140303060a06020604050303040204090c0f03150b0103090506060f060906040b0a020d0f0c0b07170a05040c091404080d061a090a0906080d1d0607031e020a08 75
    0x30034440311580c6050007140c2400350000d4032544154040c01e03000303070b80f80e200703486050103098074140c00640f441c0b000c5038842c000d560100186241d03403a5502084040e00042c00243c0300d0040306600003e800342101e50850046105041d404e05045840c0c0b208405ca52519804605041c208414500050700208140d41c2c41441203400800492103400400c2e00ca01074500c01d42d8000783c0025002c958151180003030b1081d04410703030880d2100c41204000b2030302c1010714010000440c8101c1507080c0080c89900001d071307201c003182c40c200e41c5000032902a50b20454060320010341c8540d9610a001c2404210850303413000d081004c8040c04800b0b5808404444200014400303440043c02160031516115103400030030081001001c59203101c0c14188000280d54000b40c1154801c0d102c2c510f00061007880c074024102140e145001505041e90001c0d816070380060580007840c0d402c4100c0c19008030a548507805032218900030703036a00d46004049190f1040030314021340907000f994080401c030380000790b44000301c1d0030103040303 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 849298075 1250 849296825 849296831
    0x9271602100f0204120503120622200a030b01170903161119090612020913021f0f1205060a050d170f210712090215040b0c0f0c13 57
    0x2961010002130180790840142c404003e80c144043c41070002c081c01d484030b210229814245c42e103004100411446021104229296681004041c910b5500a505ca2801c0c07860000d00b03140a900240c22550001400d9404241e944084d2401c65901c44007400b080090151806001c1c2405841c841e034900a0020000c4100c00e001c0d1201d0402084041082da1000c01030b002102917140c1400300b052840c624068940321503d460307030000d030020752210740da11083d030080d203008280e80720721801c01084c0c6041c0d08180e80025900c003031160783d0281c54400901107280b543d0b401035141804c046c014891611041d0a1000c0c600b0304041c86880c3c0c0d1214201c2d800c0710300c111b4000b8404038040c80e081c0c0c4070f4103c10071041c0c04460046440079005e442c0500801e0f0403590300c1414480803140009501c40300e2010340749800040c041d030181c4000c2001070391029241c90300003002c0000644868001c0314007a031140e000310038a80001b281090f00c00c2420089041c40310f103050050003c4c5049080401c000581c0010958140b0303403 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 849299325 1250 849298075 849298091
    0xc05030d0e031e032d13210e01030f05010e061011070b0304140f060a050a092a170a020d03090509041a0907051f050927160210 56
    0x402c004541a0716050039140325103d544440010064104444511510034010580140c0000c942030460005d824102c500ca01c0d91541e01d108510700e0304405048031442c1d0030b450b1107181881100b0a4051212030f07541d400034a080b0032000102542c6010b0340444020b400c100044c0040c50050886590020060302c2c02904c12408510840e805d1044c2094110f242c040c01788042003100181006503c034a0081c20702020941451501c50b035182c04000b091110764001c000070070001c1c44150030207600020410400319140c4100d45810b4200e40160749420800c0d191042d0401c810070070000340d4401003540314000d4100c16036240c0e40780c1c1c8030030200074020700c1400c08140c41820075014818402c040c103000b400310130040c50070745400c2007460110b560030498020f5400014480140c0062060243d0ba405810100c40a0041e20b14008480c44100404140481400300c807441f83c0342c8070541e16000e040d03c0e0071450900414486c1022035403003d1321816642d4901141c451300c0c2030b000035641e14540025100012240c5c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 849300575 1250 849299325 849299351
    0x9090c0a1b05240c03070809010f0204060201060e131509051005190f0606021f060905040f14030a0509102001090b0604061a0d060909060603120c05030d 67
    0xc070384007540340c00d442404004601445000240b43c5055800704100300381400301e80c0c1d10803580060465030109100b40800000381542e1140350720f160404d441e0000419070000c4000c000b4242d8015030404d20050f9590341c401c0100c8000309071481d8200e4100c1242c107900491070748511700404c0b03c4507070903401c4540310408401000380030821050f4002c64244100030764242180002c412000080f030209a041c02c080502d562403002d84219002c89550350000c2518207240f8120004680c2d03d01d140e804c00e00d642e0000003868030503c0c001c0705c0c8914898020103c0c5411949450090003070f440c00c0b81d80f6140d000307110201c0070580140c00c84d08a890101d85003155142404e030700701c50402c012810400040805900c004080c00150011003141e4031448201c00c650791003601340000c860607031007640840c01000300c112a80c05c04260050081e0800706001103246030311904110309440b42c24004031105c80d503a860400600001504440c241e81a9107003004661010781c840036038034000d956503210050740e210f00400c000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 849301825 1250 849300575 849300587
    0x4021e180a0902041502010c0e120717010b0109140303090d080c1b040606020105192301081f02070c0512010902040f0c080105010203030903041406271509090c0a 71
    0x31a5008012512098850102c003010f50058410510b4107140d100f040e60388140180a030304001483c271340d15607500e81c10340c000304002aa6601a070040f5405642c6010030889014940e001c003180c6241d002150043d20040010018000c540c4980043c00001c03011b00c54039a00881122056081117942102416036418080305600c1144a4200e5500c21984017046840c69410324540302e110403502080641e55940c002d900340e40d01140c1c5a9420749481c05080280c902c1c45d400034070f1940f4140b41d20b0f03070501e042600030b0b000d000082c0c004001c158007030342c01000301000e1a40540c02802000304290b00703011040e91410074480b45809482d01ca0010015044400c2d1025444100035680052050082c103441d50040c0c0c00914158103500005400031002040c01e5000100f05d0340111a400000c41c80e287c5040405400c95410600351035000104204401a81c0b0100741c1406001035807d1202076800844c81c1080707000c070b503241680c08030203405004c10002a500c001c43e999110450f0b510700b503038440c01100120b0384 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 849303075 1250 849301825 849301867
    0x9050301020a021b0a03030509060d02041a0d0c03022a1f02030a06150815040603080304080a020c0108010b0a03020304260304060f0b0f0f150c1b04021e 67
    0x10341c80032840c0841c0075400500c541c007061000011646a03c41d04090000300ca429010240c0422000c21900030241000c00050920040201c0014100b41c1c031801703015032842d80311600c40c041c4500400d800c500d402840c440c908208019060031451f08002144007820309030b01030f403640d40c0c020740012814443c540034040c0031a088243c1024961060f810803003007009420079a8030300146c80c9001c002051080040a04200e907108a88580910350f8070904d043c1c512464001119420580380d0131b0010000300e401e009140924859648103032280c07580c2800a02c0c048922404604000b4440010000505208101c46e0200c0c1e1518015941c1d07600d5080100340c07502055801111500d1180360010610316081c05135004910540c81842541c111209044c2034480e03441500744d0055004d11042150318040e80f40700c40e1844003403d0f02c410b82074900c070b9080d00303904980200300158014800761140940c0e0800441203107030040341c003141032400007413130510700310002685074505036000540c208a0615210318007007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 849304325 1250 849303075 849303079
    0x6091005010c0c0825050306060d02131401030f02041401030c06110c0307120b0a0203040804050609030a0203063d0915031e0308012403020a0c2f01080c0405010503070905 75
    0x1c09028104040214102c00e02c100079034501700c035400494107140100c0d0541c024100181144000d4415408000941d44054910a0082d6454400d0002980301072105402180661082107266015005200c192111400300d10008a0b81c000184001180351031080240c0d0701e00d1401e15800711000a405280020809815501d4813440c28002076440c1c0304449155518401c40b1795482c25124401c80e20240d0006072001065201e084c04140090305002016100315480141160201c009540120b070610707500b51811404006903030111142c0103030346814255031906680800c40100701803581d004401e4460b001d12a015a00d6401030406014800a00740c040d50700003400a403140d0783e0b00250005125890320480103d583c50000144681d44040b44d44400c0c924507909000c1c140c0f00344001c50095000e00150414402d034400944042040d0100d44141540c0705544c521500344824598800440048242410807030482c0401c0f94440c102c030251012030710203091140e02e82c1c03075910040d940d004294020075 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 849305575 1250 849304325 849304333
    0x3060c03100e041110020d08011206020723010b0109030b041101020a021017010b1801080402061611130c1205060612070e0f01111513080a1706091005010c0c08 70
    0x3130002d824556240442c00b01c401c03c0f10a090004140c2c0c403000310a02e00404684403c4c010020148564079008106119107401850401240d50300d004498200003507559840c1c2040082910705000d01c0340700400074007400c201c810146959078103030344410000c000800610040c5018421a4000c001c1508510b900822030410580700450081c03110104031462440544203400004080c0120300803501d44011615031114480b09060054500702d1000e07008a81204041180d5150091080c5056900b18841d098168181d550f450401807405002c41482c100f075840c02400542043c2c0100c491100e1081108000c2400e1341c4039030000300300380503c0c0c441c11000940d40040250096000322901c01c41c490483e00c41d818403900c0c0d001100c04420714000c0c04d050707500090821800404900e16184e100c26003024034400e191f0342c0d64072a2415000b85440d480070031610850500303100e4051181c2d5921600c1664460154500201000020880e41c4503c5e070502580c202d00324103000300308003400c020301103a008607 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 849306825 1250 849305575 849305581
    0x60801060608190915021810050d0614091801020c1507081b032418071b0c0b0d0e06070908120309031207051303290603060c03100e 58
    0x1510140d000c40d8506038460284140c1c2d20f00c0e014911507400d83d9034102407a042240e5080d200b0000030b62040382d0009102c100f46c20849290f40e40d5849181c1c580c0000d40c1c0340c07030b1610300200b00442980d009800c0f003403800410720100d120039141e40b43c0280d48851860f002d0308422180b82c139000d00a00c41c1c0000011640100301486003800c2000c4002c600422440ea0740c000741e070b03032180c0c1d80c180310242c2445540c3c0080c008101061030400d007035002c032600000070518008080e0500c0c00040010300d21102d40d00c7c1600c013000401c0655038002c020324001c1004e2650007030b60188160380ba4192191103004e000110740c40499214510420340c0d00041551200e4402c90307a080c10164005007012100c1e20510701c0600c281c07100c4111141441c0d003a03a0040c0e440400542c20003913000c01c00f1004200080c0036404010303003809107406078000340100d00c000758002c05c0caa040203540803d54108528480c0014280b10211106001c42030b20b0001300164409001d4100340c0d140e8840b155054100704082d0b02c649144d200d5603042c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 849308075 1250 849306825 849306827
    0xa0813090c03060f050409050a0201050306030c1c05010c0507170a0309020918010e0313051005070213020d110403030f08040c15050301050f010e090429070507020a05220e010608010606 81
    0x103d04141d5624604038121159100e041105546012400400d5a0060f540361b1005501480165030030010082c241c5da014141500801c1c01a924140d1303990140319100c02510a00c1403c1c425104121600e180c1140f42c110951111042080c00412103000081d00103110420300e44a640a1002c007a4010454440390910f450504050200d00c0a0390009520b4403020380c1907120b000084603589000591034142035071a1100300001016001a072509110041102e080181e070f47c0c040c210782d1580400c40060b101e9105100390320403a048030440d00f406550030041880840d810074508980100503140440440d6520301c0d000880410950002294000d5020311000a641102c040d6040c2e07170040d940d9001c1c00c1914401102c00f81204408143c110351600041400310b60f0700c900b41941d00382401601d8282048204106885080440d400ca00140700468524214580b407080d0300003c090403280060542e1030300801c04200700740c0035089044140e80717005101c0450400c1d0400c60040016000030024159141c034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 849309325 1250 849308075 849308081
    0x10608120723101401061d0301060308120103030e0f0d140c06040f030506130209070c11030313051305040b130611070302030a090801110a0e010e091005030d030e0a0813090c03 77
    0x911044080e041010403040404c252007650704941880d51400352001d084003400040c203001001d00c2e40c055407141408404100410003c0007143c0d00702e01d85200d958074500307000b000070b4038200c0020300c68481d4500d49a1660f8032580141e00703ea42000c4c220400740ca1018515107010652002203412000101e4000307916080e01c60305008590099040d25441d0f40c44405900c0b8440340c110000358001107000c0807900241c404c50500c1c1c0114801e103d20312284942400182c9550403c008440044080c940240020b0510110410140820342e205010303500f4644e0b100c031084800100610413989440315201d003071100d26081850400b00c00380c0d102d0b80c1e03140c0d035040003512540301c68900800304115100000c0d280c1014414549203000040f00181051603549040341c1c2883c01280d160304000700c86e0080c2c4010f5507150101030203100e407004000841b82c0344c0400d06007800b010401711401d2500c3e015124a2415020812040702075002040d41e545483c1200105050546a0018184a40b5040c40550240e4140d4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 849310575 1250 849309325 849309343
    0xd02310c030b01110a061104090501031b0503010e100b0d02090a0501050f060406120f0204080f011b05120606030601170903030a06210f1e050109020a050102010608120723 75
    0x9074042c8400000c800040d14580072481c3c6100ba80c1d400001d0784e80114a055008044030318000c641d09190a03501c10511060302c000380c0065803e07203d106520320241c0300c1000315000078403068000740100401148882c1c2c42d0050b0300d0150903410740b1070709100350558411004c62000c503070041c9104580e042540100e00103100074000c59004400030018845070380f50903800d540c1201c0300c0b603a5944c003100310702d030300000a00f0400403070300c051903028400458080c201b4411841041c254100010341c055031001410302982080e078103103041c014104000040f015034907100c03a84c080c80031364510ba03698444d100100c500702420032900000c603a078a020b1000180012004500400644030144126610750340c644e0206040c5083e10b90141d0613810031040010300600c1c684181c070b80160300340c00310b41e0071032900a0710101140708102d4407655100d100004526240711905c1c0030b04002e1008114050a050340ca944e1b882343d50040a03ca0b100110f004400c00461250b141c2002d071041d070350000303002c0b02054410342e184101 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 849311825 1250 849310575 849310577
    0x1413050405071110020a0e060a2606030a061e020403120e1f030b120105010f090f050c040509090a050d0c050d110316140a080301030b090c0d02310c 65
    0x202011501d902e10441c0c0800b18034070300300c0250420500c4c1031800002035008603a18424440d26002d50201e641c1c60b0001f41600c1c82098a49041c1c071355580300c0342102c0f0701c502040b0154441040d0700344840783d14005214990643c4c829800900315107010310780d01d000b400402c10075403d80c0c00002c002c003c1040140152052140a0700c0380c403040c0d4140c204102115036222085031a80120745086020684a504600e032060300142c146215140c07007510460a40d03030240c0200b148504141801c0200b540700703101d80c06e01130541da10300b04150f080c40e09420300707c2d1085110b25446202d01c080484c140c4c0c0d0f407d02c01041401d9120301161403824100c2c1c00540000e500020a940c41d0107500040668180502440795504000d4400740d0310b01a058040c1460f002c1c1e005105a40e03008901114071005d5100308400003400340215002903e03507155260001c40c007880141002055000303e4420801030f100d1401407400d003075048800302c030425082035650842c0c80580c400504860018541c510908107541d011090110305 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 849313075 1250 849311825 849311831
    0x5041802120a0507090c0228020406030305040807060c0803040204090318030b0403110c0a031202070b0301090f110c03040612091505041e1502070809190e010501171614130504 77
    0x5c4c4109210440d40c0d00f11600b40035801a0645221441000c84104070366481c01110320740c0d5103e01d4000c1011561160400c80120b40002014011035100708031138002410a0714022008480070768034004c40d80400351009002b075440f15046420540900d1100155036845c1061034001c55903810801080801500c041d008541081605a0740281c04548110b1003d00603001070109480c40e0f9801007440140c0c1802003c60041e00c1c004119030030407000560013010031f03100200d50310b03400007460401c43e01c40c40388031042a0003c12561f82420804815201100c80c1404c040120070710810642c00540b5220600820700380c0814004044130f62154404c9003d140101d0440ba03040c840b80c150f485001c004040b0140c03c0c0030780900c102180034442d400030300070684610303035581c140800000803404c640d03a8032080c00e009003850720040c025500e500c008180108401d280400810314055031328000741201810031490f054814010407140d9001d1403119940340d420140d02562003404a40d14407040006001c0c113441541 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 849314325 1250 849313075 849313079
    0x1d061012170405190e1b030f1b0408010b09010b0723160303030c0809190b04022b1a010b040504020d240e0a0212073002070302100c0905041802120a0507 67
    0x580412022584842054000c0c6142c4403144152300001005001388001074040d031001d01380c0d10329100078100521601002041040e0000b003084203080d0160440d0f0722804041c4680000310340c1030b150740580d82e03111117142000c3c0d2801d81d031a5400c100342200703041843c1244110000c00c055241e4820014103100d60340c5c828840e100c81d00707c1130315a1911a40f44000b04039220010011441514040b43c200788020300008a402012944900a458100c504038903d404840424180100c1149000c01150f04282c0c00c1010f43c10030445881601883c0551409164042403900042c1c4455010b20b0380300c6009215091140c8181d000d480c00810b580c080d00107c80d100201044440e9001d0003603810000004031200e0380d070740ea83c00044400c00b90212840300d08424210703203500c0510a03004460384c0c0d003c0406025a459585080280c5400e265208001000e4500003992521030381c49100d032010b0310ba040743c02241c454510f501c801290f41c50341c400650305c07030580650325101400002e610794000d4480c805541e9030355 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 849315575 1250 849314325 849314341
    0x10213140f01021c05040f0815070e090103110d0506191116081e070605061e130f020c0304080318060301030807020d0f05011d061012170405190e 64
    0x1c656074a02e000d80e2046a0007aa501e40b00d003401c800015413498a14203241d0388811482402080e030303200c01c80079046900c4202d1021403800903c6d90044190404400d1041c6070408205c10850500c0f001e848010702c0740321400a41d441018000703010303411100f00c030250704010b038002a4140084a80c243c403946002c16145942e019101a218021001511415500007035203403100d443e48a65642c8001c1264040e02e15450714098015008050164000150525140003800260001d01e003c110040400120110050ba100320741c41e819881c0c640d0300070865089050b20000a400781c0303040340c451400003180c00300c0c000c030300080502050062985090f158828400a00085120a0201070031001c42000b03607501505100583d500b01922565142c001e0754956242c450858101c2e0504040400c607070584900c50202c100000c5801c1030070003980084480c9080c0c030001048a00c09030080810004410150040b480130040c0c0b001000302030500e41002c0054492101646800d015515101e682c04000c92144 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 849316825 1250 849315575 849315589
    0xb06131d1b03070608190207020603190f0204051f1e02242e0b03240301182603010b03161409010c06061802040801051b2a01021314 58
    0xb13510580b190006500d9100713050442c502810035445005400f00240e00058481c4c03001180300347d40d11040014600b0084520704140c420515060445038014081802940c1ea2440b03440e0320303840c400b080e841340804486010f035804a03d800074110b031125000d103500400c03500454110f070950801c0661060110300b03500d44070000300040d900b401042500d545034804200040a424403404100d0f446881d040d641e80404c0420b42d0702c1251a00c0080c0200e80c01503226255131041101000402c034024402c003402822100380010900b0313030150002c07036003010344003039035006c03e210344a14900c070700c0e900d0345d250386403540c101c1d1503070054503200c0800c46881098500c0e584102090010a200032480c00c1c84d003603400c0300440300741215000555000343c2e20705000581c403540840003001102d6924015071103a15000c4407500310b560040c010860440312085407203203000200102e5072000c4001c5144c401d880c900c20640480c80d0001d1a0001d615840083c4808503104400280d8040700c2c81800c1c000c1c4040c012200348400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 849318075 1250 849316825 849316829
    0xf060303080417040f230d1205070606050904120914090703020f0c0a200a0e3403050a060510080123150a09120b06131d1b0307 56
    0x500300c0c00201d0000743c0004468a100681000c0c02e60070180c5440400c0e08112244d4021002c0d03481c171000020b08801c08203440100d2540c111911800c0c403a807034407403200c609228141075040240000e51203040090b180e100318040c1401074144c0407140341178500065807182240081c0041402d40b240056909a030660544042c503016109401544175842d041d4081e40040980301c0d2491814003140c1240740f03003008150b4100740100c0a05002c00000e0300f0000482d0111010113005290100d0180542c00080040c560409202d00c03100307082c14070460f040b01940392511201c10003038240070b02d2560413561582007103025000c2c0b0281041511307910420449082215001000855502300042002074513440f41c1c01c11095082150000300e03a05a00010154150010701d04076110000c6040d044a90303000c0104405090b05815840e0140c000b030b180c0602d0220000c20151086050f07000b060003038115a0000c40e06042451364031554800c528544585401c05000300d204000503440001205160018421701 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 849319325 1250 849318075 849318077
    0xe0604080405040b01052209060f08070b07020406050d1b05060a0c0f0606080a2603040302030417010b040f02090102010e0d09030b150603040b10140618010e03031303060f060303 78
    0x881d01c0d00e44403e0002030460380041c2414030106105030580b0500040c10003036120110031300601580d041c00e0040d011165242c000c85503400340e800b418014840000340c80e0303060b10f807100344281c0c8507a254800103002d401c0a40207030350012480c0500b5803c000313100ba07040c114201903c1e034012042d070312401808000d009a2a41c0030000301500c080c00b001c50b0886004030032041c0070300070114001e034135078848620f06140c48c40c04844d040700c00000000c9180700780e22801402040e449000d031035401c10741ca00a60ba030045004404003410761800e001c24903802544290901d030700c00380007404490070007003084000b50081d2f8489409542000600c1c03840500c00304280780d18803102c1d00d8101c0034030f0454a034803646a0008048001d285040320120003550364034006188180c0c82801303440c0c0c440c9081464008a05100c1c2d20001480c10651000355590b9202c500350795030341d10390210011081c101c07040107e51074000724403080c3d014000050500e5050000c5005881641c2c0510380500014040840c0c610494103907110140c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 849320575 1250 849319325 849319327
    0x1407050d021e01091208330315090c10180b0711090c03160302071a01080d05030c122a04090c0c022b050d03050f06060a0906030b0301020d1e0e060408 66
    0x3c40c1c280903074030300c54000703845002e90710754001602d904c440311130300044001000d541d20b00000302d4946410054004543d15841e00001c9c10304003200c4403541d805800c82044e00c0f40e012900450103452040900280c3c0040340c602a100195031070564444503440540300f84c4000b05120039800c05400e000015600580003030000b0340c030710354590300a02154044880d142040503000c01a80020494101a2081c5080c66084c0144254503050403680381c4001c1c00314070014410b0601c10480c0c0030110a094407858038202c5110012076a44805100f106041d000101002001c07000c04c003c2c50003000300c0580142d0312059130411003560000026101c0074000107000f0350202841100300303009032109020710040c0c2da000904082c01070565aa0b58102018850031000088d51001000300f0040070041a94001009a0b4200e1502801c031000a113036100f14042d007c1410380b02d006070665070314250704864040c0040e1354108441070b07800140100c501c3c080a00422100c3c10701048002e40742e00403514902a5500120329 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 849321825 1250 849320575 849320603
    0x70b0f070909020a11030d05010905012301050702010c020904051506011d0f04020417010507020601061b14031303050105090601050406080d080606040b0c2d07061407050d021e0109 79
    0x400c2c00b03940800483c9041060850920303507090010805440401d0030010041850360400240a0440d5416407000300010742c2d481101c0301c034104400c995081044280b03800c6903564854001620b0750300c1c903003100940008240c0300304820320002044016103e9460300c0890b1894864500441e0307084142c0001c241080202841035039145084407807840180310141002d420143c0d101d03000702010050b01900495039450b0b504000d8015418010303a0b01620301420513152060081010358440c0b90030000040c0018224131803031045600400c16109140303035903003040f05c0d01510392404030302800341941e01d40300620032070307001146030700d0180240e038265100704c0000d00c21007818080856220310050405900207404100100380c1c2c0c40c901d4010140a40d40100a1508021078901000761480024298080b00108414070f100542e01080c8001120010f16084260100008a40c01c0b44d00c00c0180042c16031017102d2000700d090b80c01080c9940d46c9128010301c0d40c0803c3c2d0550f840e600717035000410011301c050101c07202 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 849323075 1250 849321825 849321839
    0xb070311040b1c0b0a0522110304050a0308070302120408030601020a060e071409090a081806071212050421050c0604030c120f020717031204030203030619030c092708070b0f0709 78
    0xc05041f1441180891031080140c4000ca0031750041e02c040d2002e40012545400b8540c111402e590482c0c03003880c0452400040d003c400c25103400180004140890010100314160700c00c1004070000b540100c4104401c081c3c0034116075482c452442414a40e10001c618180c0e14503080031124400d004450180102ca5100e03a40c0311115030048004075030a828060390305005803140c07406009168811004465142008000500740c112400844080e5500f0042048002800300314280a0541450810691084265002d807014020403c0364031030340c8144010841410b83c08890300000c140242d503480462000b400d0210f8081140b5516180941c0c0700342405c000c10031402084080d0010b003c030a0728140145440080c101c0709d0140c1d82900164070100c1032000500d0441c01e4000c040041d04034445d41245180d8407049910385910410075450f40d1103518500b0002903007140d11000440c0c02400c45509803510b8030800d1a00104070030344400c4940400100103a50000c0c0040c000c1185440c2c0e0680c842c40e00c51 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 849324325 1250 849323075 849323119
    0x40b0607020f0a0803030108150112230c040207060203180f03031f0302040c0e0f0d051c0306030f050a030201320a060b0c01020d0e0303040b070311040b1c0b0a05 71
    0x1000c250030110700500041c444d54144050f501034803150000d0302e4a8100240c0c0104140c006070008001d1b6902c100d821000104080d80044e60402010a0417441c0b0614280c034500740041d010041e41c0150000070321808011055000758810000c1413000d140310088480982c0e9540301c50080c8085030780c03080001c02c4213800f0141d141c6041e0800050580b41043c4c03240d02040507a001804074001084a078001401c1e01d160100708601c42400945e821a110700580d241e00b984ca240403882180040e00e582540100e0034425007201019680201030003c16221900d0300c41d5480001c0141600103510744008120100c1f80e94171400000704c0b07101041c10550307404080107854180040c0000f48807555a440c00a113000d0031102404465189000040c1c550070200400d0095071122103000006800802c20440052003032210550800c015160000300e00540c0d400c08003480c450340d040502608000319020f05803040d10a00a8800c050021040c022a5071110602004248902409603c914041c031040000058a1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 849325575 1250 849324325 849324349
    0x241e1c061413060f0b040e0f010b032d0c030a150f0501030b0103020907111006140303072a030f080405120706080a0b06130f0e0907080d052d0405040b040b060702 71
    0x44c400200111904001000c41d008000c11800d16003164010340d01100d4203114030b505241040d80600400d03240740c0b000040c080040310203c0ca5000004030060b181d07460030010a10490006011140701c074015060810641e4034000505401908210100c071a0384194050030b41241d5228032441c0243e4215802c0129030b810040c840b00030462012000718411004000c0c0c0241d8021400001515604042c6001f41507031140b0710041c082d50041090380c00182d0001d4081c54191444c4116601403900d805014000501941c8060084a005814401400303408001001160000c5810030038a40d2402c07251510781c00b0910800700800d12040001d11104516044045080d000500c580c2c60b00b0402d248042c111012030b044481c11801060091060350b010402c450741014000d0010005145030411403581d03003421a10302c50402ca8085145121100c9000d400c14490281c0c080e00e081c01c02510711a072105812500c66940720303e082000810301c0b0700305886032500d0000050150703443c1065503001d00c040c2c01009 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 849326825 1250 849325575 849325601
    0x1005030309100c0b180d0224180f100c170a1a0406090609140907033c03091401050f0903070b03040b060108241e1c06141306 55
    0x403c400007521400d4150700c03800e45600303140c00c40068080b00625200b803810400080d540041083c042c041c84101c9000c002409076035482c2915910340070b0660180300c0251649a041c41203d14069145402059016941038940010450115444c1d01103a07a1024100b21101601100300442c50b444031136042461704040300301c41c03109500340010205080780c3d8190300500c03c0d15a182d0092003503040c240280c10646038070104848981c00c08030700c42c40c5c5a003050300c401024072035080700c9190888a0220b8170a08800c101d042004400f034651158900b000841c1011400248813490100d514050f07031b2002000804180c0d1068240740400303000c000c1c554885004070f81e040c40f800c040010001d01030030096100c2c52140108270b0450922070005805000090320242c48541c8103126000049a03000c0c0f039104d8680304a80d580d6603011918a030b40f03040400c2d6a00c0c2d5030444800d400c071903560585c0c060f512100c5c80c4941c0c810840e01401c50070707209603032005076040d0351807282040c458004141560000c14540e010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 849328075 1250 849326825 849326837
    0xa051e040803181c0c0507060c05060c0d0f0e060609010f080c01050d0605220506040203040f08030601090512031b0f0705010f090509070908010c08060108070f021e010212100503030910 81
    0x10801d4486200441421000005031884041741c0400c1000e10412008107140d09280f508078007141d554645991005202006600c0d02241e804024001500402e0034503400460400480c480003003020344070203080320914081c1840c8000000c1d0b05807560301c040d0132129407030b0190808400b1903004441e164404844c40501c0760322800d0106603552401d050b584541503507030307800c020000180040010b55074014180c903c160300c10310402c00416000c51542c298264481001552542c1e01801a20105120340129400000212050540c40000402030039200940b500003030400346000f058941c1c0301158030f07482101e5080030b00100255401400550540d103454207202030101d4032100801c0320454100d81d94800a490f005040100810a20524860f80803d192003505846c000300081d107545005000d20040196040c0d02c03014680c400c0c405c820109112402d803c1c12145000d4086000c7d400c6422035441544207103007c02c007004035510003d030842d84083c000d14102a018400c119504401e0340c1640b0501c18 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 849329325 1250 849328075 849328093
    0x90d0206090324090705011b03120903020615060301050d0308090717030403031403071706210d1b110108040c0b22060201060302090a050604090b0a051e04080318 71
    0x180601c44101110702103d4180c0340720f410f014425044400107000b0a0094100710030500446c0d9110030160f0350002d445104d00b0454403180b5080b030f20203182c001e0707041203185050491020107a01003041c0740a1035001a510b07481507221303010050180b100384145540070551000d03420029028680c95035002e01d0701d40980b201c19075100040c100c261f2a420000b02c55402c001014401c0681041112811070140e012003401c40c5014103000d080110001011020820000d00042c0c0d030b99200d01c1c6600ac00458418594410070486581c42d9a5042c1380c0c2820020404072076094501c030707a04e02d288440751504584094580500080195480e800280050305c840440d20b40100c0e0302e2240500600a8444810300c08024400000c4d111f019460241c2004085904103181040980e0312829100d81041501c071000400d500c0c0c03080010010000c50100600c0070840900b0040712000d103030702c82803158412800510428400c410900b0340c9003400c803002011084c061001c2950408000ca028040a11981c11a03280507 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 849330575 1250 849329325 849329329
    0x506091c060b062803091113020d0c0c1703040b15010e121006080c03030f0d0b10050d05010603200a1403011511030705030a0c151a041a06090d020609 66
    0x36000b0601c075001201d1a61000d0901c019203442e5441441680ca0101b00300c450507903610290044c505609413007448041c0205002c2e64450b41140c0411604420400552036400c60103030100c160540103031401852609045c9a420800341280d22803580b1a90b801001c2d62075183c031645280182184a04011074200780d4901609d40d20f1401441482503c0203040084181070a00d0554100303820021058100540b0001562800025030703101c100100320071030f155440110100010021060bd841e8444208165074044603003003070003001e1442100006200c240c0e2501d070140c0c00da0326040c41e103090104d11082e00c09204030000c0702504080b001490108000fa420781200c5c0502d410a13000740b401c04811114040340c1701d0b0008801c94985034000c000d1414007880b5201e40da200e001e04030085041c040c81c22080c1c420072040c4003694689409200c4104404060401c5143c118541d00c03040e03c0c0518544025261811000d10b0503e100304d00c000c3c1310030b241409070030600c016840c0c2418201e030000400d100340d4100d5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 849331825 1250 849330575 849330577
    0x506040e0103150f0f02370e01120501090516050307050702090a0b2808160b03181b0411130b0a0c0b0a0504060b19061b1202060a060506091c060b06 65
    0x105e400c3c10300c05a1141d295801029080c100d40c68010602c9802100b928002c50701050100c41c8000d0508081003a08180801038440e400c00c2c0f85004c000510b4540082041401c0f6400540100001034040f1403100c220074040e2aa03102c1501c84c48003180c1c090114000504e001c00025500031071820002c0740d0b16880c0d02c041413030b85264a403c00c40307440c14180b040c440c1c0f070013030410303c002001c0d0000100000300600b802484503040f03500039050700050010000d5110346c01e102c0d05180b591000c00c1102c0c070201c002d00c9030100351391191142030701c20703030501805481c008101401d80341c644540b080308000300303480d010040c90240c1c007401c403560a014241103440041801941d0161040482d00c00203c1d0031f00e0649800070884a91141c02c0344a070f10340c0c9002c2c01484807141082d009851312400e102042d10449100c0107144188840e00510020356280b92040290b07010500364060340303401c00c091060340d845000304070305401412107142d0402e00b044514401d00c2980c840c9014000e0080100140286040c03000c1033907 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 849333075 1250 849331825 849331841
    0xa020a050c0a031d0d0c180605030f0c0901150e0f01111002072904031101110f07030906050319090c030c0803030f070314180c10030608070506040e0103150f 69
    0x1041c90350307495001c0313002d02008584070f00b40c0481d80d80c001d0700d005070b680c81045912409401c403128599108144c82001540c00500a4400102202c1d2440d09076411199545071400c480ea0050103c58000070b40306080004880c20032005031144454205403006100c0c294000010043c10132903c00d07040341183e1003d0000700c403000d04001e40569503046030304090810407080707166058440d441616103900104110919a0080d6052402202504030b10031018054201c200340382c41084000546a082003118400410721a031198840c0c46016564041c151200e0004540480355002c012084038080d104a50114410381d00c16104c9001885d00c0b40c071050841440d036001000d0360b50001052044180c54081c84940c0442c591500f03110342a064983c00c146800007904118800d04490100d01021005200401da0507101030801c0a003e80c610303a004003d0100d80c8600301c141e026021000c50f05060072011501a600e04c8218400c0991856031f640b030040c00e00b0708c00103603481c0c1d0b80c50f01048114160b004d0040d03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 849334325 1250 849333075 849333077
    0x11b06062301020f0303010305150411031b01031d120c07080105010611060f070903120309060c09060306060c020a0303140f0c03120106031e2301081608060f0a020a050c0a03 76
    0x440016078000191924410464241e0142d1052004100180000a00440100340421940095116480e06d01c80c032082005040e036060255403008060701e2030009080c41d40c00424ad0702030008645903440303080d00240c01213104401d608030303209a41c04207015a00400303540502400300c805441e035a4081c982125420703086100007400421122400c24405c0100a0304400501d1145080c0d0820407405804480031b880001e01c41c0d1044807804009a029500c80d171412a044076080c80300020a40e0000c0c01d98007a4014580824901500416600d114091610030594040c02c006405800d50701c0c1a5280119441450401542000841004034828015041e00c14441004503114034680b840402c04002c140c0000041503c1c0c0403000c0480305140164002c2540030f0200002d08810207071402c01c10382000910405030203082c1c000000c03020400211003404101c032603646003035942ca824aa645070003058030254004d0300c1c01408152580c4903603000b098582c80c6410894a005504046a82001c41e904410341c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 849335575 1250 849334325 849334379
    0xf080703030f020d08061504030b07030e071d04080306042705120a0c030c02040605041a1c0c03110a030b010b0901020f120706021b0f0706031a011b0606 67
    0x420550800030700320b5200b001e8006072805400c01d07070000300040801440c1324030400c1180f0040340785400c205c1c1210061900120801900c0c604070001501800030078250036a6845031050008420f407002c10040d500399119101c100254466807543e494a800c05407525078860b41d03881d28003040c075112440341e011649800441111842e1541001810090320440004581c03108000c00399210354010390710551507906003040c500310610f80c0017107030040c20a608100d4206180c40d15083da1119911003401d103001ccc08691490b0780c0c224205a6520f40c5480f11002811804a0441880040c00d1107062071074201002d411480c52941d0303a210b500d941c080a0b40110b00b814000100c41d105542d0510131150301c00140c60003007484092621031701a030703849045d0001c0c3c0f00b19400310308480108202c0d000c00810410342021240c1e0442c808410544a0149200b103001017803805901e0fa09000c28001504240031051711707088060404030f00072000303502040300c046404d10741d0707010b01280d00c00f400e0b481103050080b070380300764 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 849336825 1250 849335575 849335579
    0x31b0c031612110a0b040308070e030d050912010c0509090a0e19050c01090509180c040213210213020f0d1d070806011406160501060617131101180f0807 67
    0x28004584000c44075010f600700280e0b80700070480c45c2007002e07002a03151426014964540078102c60031107413003400d00d50501a80014074442d03680100a0801135100b00c81d02200401103000c118200c034030718003504002c07900c00c0c0700c540c8d164605010300302da104580240c046003021460a030107040c1900b00c0c0412007041c20000c4c00c2014407034104040d0094190030f00345076951500b4100040d04120340202842c8400ba4010750b034141e811820f1265501b1f620000d081551900001c0d42c80c3c0c0c000c90400d0150048410406410b000100707000480c0000345c90300036103203183c0701003804180d101950040018194150003040031a03c1070215105e1a010b10758100510b151a000a0183c40d0030320001b035006c004140d000314014042d00340300c00c0081c94809000c41e0016660307408802c58003141c448214000c2c14551034101c0001d034641c0c102e00510b040020301c84091405035181d40140300000c0100d80b02400141c00e08a8548070b55015079174400c00d8000391458181301c903503a01c141c00310080e4039802207a0140c101d0302007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 849338075 1250 849336825 849336827
    0x40f141f030609200306360f15090d0e0402090402040302061201053d110709060f24030b0609030a1a0901021e0703141b0c06031b0c031612 61
    0xc50300513030908502824440c00c0100c3d0b812680207100c4101d000c0920800c2c000d8181c203043c040140040c0854100342c4440b80e100004158840c282c0d505507020190200300002c0700e030784010030002c03442c1003d40c0320900203514410601000f500460049500a5805c020100150b071703d40014180f03070791032031121180642c103060510000b9800d22613041c0c1078003410101d500390300100310306031442d04002c180c000036a94070b041720458a41407101c1e80401f03180940c0c0710203c1c0080c0e2582040050340c00030044035682c103035541d10a0409038104c10580d100c0480041340e90032154881e400044501c0c1c402807806041010000009060925120707007140c03001c403901908050078030000351059011543e08021401d001012080202c88140c084140039580c000240324010940141176180d1017000c00203005458502010300400c030f00140d560504894803600d011009507140800842c0c2c891040d07021150260314041402c0400c40d080300d60810b0683c0070a2101c20070011740c1070306282c55203000b5624403010100040c4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 849339325 1250 849338075 849338123
    0x30e0c0a0326160f02032b030605060a09090c12020a051309060509061210061202090a060803090f13021201050a0801020405011407020f0a060509040f141f030609 71
    0xca03100307111402e010141400020f10091194503070000741c1114590040e100003410618810400c10300905d07072900c014a0f0725000502a400d4240355142000815103440c00c00c521401351490050000b00307805014003c1c6100754014100030b101034201440380041900c2c806059030460a4140002640440c0300c08941600c0c00701000140502c00c803c00813281401c000c141d025200503d41f900a0040041c1d4030340b00300d010800242030011150003042050340320420508100e10b0402c080c0c1c85004003074041580a169445501d080360600c03001145801e12800034051109401e40460342d05c000d00000c040000c500d14001481e183d404000c00700b00c0f03581071404002080002d900f0012503a031040c0814002640c000389442c40d00744541d462035890f1076240c4005902e0380c00414155401400c8440005100d58008010780301c1c0d4401180c0c1800910410440740781280c2d003403511480b01131040307808035072400407031210f4903040b26000282000003500c4e41c540314203580780085d0403150300b83d805c17001c128807000044c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 849340575 1250 849339325 849339383
    0x506041b09050c160c120c0302040e150a0c05040306060b0a0f1b060f020d0f0603031b0c17162706050607031d0406030317160f030e0c0a03 61
    0x4000c00c41401e11609150603401401c003c50028810344002000784142180f40200510042864001000240c50818840449823008070302803130500012402041380820803401582000340f000c0c1c4240e540c41c00d17070030140c001008074509000b410031022010440300d000c3c407005001d02c141d00a03900c03144104002e201613402d1180c141040350149100b001307050760501a00500c0c0d000140805c181040103541c030005d03c51800040c1c1b10310700d4010355404210640c0c1012048074040e40b500d00700c41c00d143e800d42d4000c60300040004c03c507040d5504140014001c00381c1103d2108180811100304000c2d0148149614100350808203d22180082c03005850100c03007030300038800c03500c17140600001d072420300031890f0b80c001c205008003031044200081d0036588000f41c0044084600400601440c1d5070b906000c1c1103003104840065070800e88600082d00030300c04003801410845256991000044520301c101e008007600994100e040c050b490029845584862150010354080e03502c004041100b0300803612010400c1c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 849341825 1250 849340575 849340589
    0x506040c08030a0206010b0f1b011e0e1e0c0a1d06041a0603040f0c0b18100807050c0a06050c03090607020c01091703040803070f020a08120d0b030a0506041b 69
    0x4004498945501250b12411901104421f070b880da10072595980d1240038108156a2a1480c24900c82406405402c0705100c000c8054000e98002d10a483c150b0580700310365204182607004018003203107000200c201e104000300450594400702c00800000b1051030140e80b00e0101c146c820003c84004e1500d98030b01e0364001c0d00460782000690a00304140030088840003200380f0452000c00080d06002000440300481a8050b44a4941640301d150320309564222a0440c050800001c401300309600300720300c040c20481c5594641f04000e5030382c1c1100f241c00303500070f540c01066401007420302c800007580d80c0540c600a6588088a81e164a85000182e14026000386110211340c043c601030352090742c02501d00815281d0038480d000c0d13a50b100c0c40e178007803541c03086500504042c4400541d95040c44003c0103001003141c800c460884880d556000e006a445240303040450f8070490030810992080c8096114002c0300c600a020384080310025150710f030500300112029590a40c01d8000c00d01c40d4005407002d40301400d0a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 849343075 1250 849341825 849341827
    0xc120602161410050f0a2703021018150b06190503060f010309030c080d15260a1a0411061605010528050903120405030a090e040b060d0611070506040c0803 68
    0x40410100700038a800b901400c0b4039644c1f500901c501c20006140030f60040d081e4107034034007403d0076460300035a1506030700c0c00c4200ca14606010241342090782c0450300c40c015000511003032034103d4200d07000010084202c0440d88498104403480c186171648029501c1c0500301e480381a1a40341c41c0e014030100905002c201c50405150844020020b41c001c0c401d8540c01e40c0111800361030b9a10350140200508440c1d14411b80101f800d01e00044c0ca60792241040190b055403007425000400e05425203540310744002c0c00501c2d44525450168141410040555005020b1055400105d20b01c1d008200182c1c42803000f01104c00703031000c940007400800d005454211403041e84d00204400c4c42824070014520307480314942450344503004204110020415600100300c0b6551500082c1031529200d55203501040030701002c600b840034009000c80089260394030032900102c2030102c0c2e554001c00c000000c9540841110019694182040c5850105000d03050862203280100720f1410541805403071081154440340300342e40 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 849344325 1250 849343075 849343081
    0x30507060c02092a16020f0136030209090a020f030d020705010804020604090c180608060a06210513110607170706180b070e0d0c12060216141005 64
    0x11602d906a612006240909030700e224200000e0403154000c0b1400668a41301145410400b200600c041c840144200c1d606000628031000659820811101000322815101c4044900c0b004100b0020440412100c0454406880798001403840d442034035880c4981e4008190354085060008542c220484110010182a14074146c000d41d1008240103d604000342600410110b4545030b0564010b8000c1c090180b103400e581c0c441c010003104405808280704000c0400009880e07024a034003600400d0040c0c0700c051000c0c14440203442996407229412448480401c00700300501c1c40b4803805014074462120b0055811150a11082090400c14501c0c4140c10404c140800a51344506002600300b45040041d100c07000e03420304400031300035240846883d00100d84001d04012404c0940c0b0300c200600c2d182c8003c04ac1d905000d1065104034000c0c0140081213805040c040c1032032070740b0300300100c2e440781307002510f000c2c05442c80a0a4840f1110300301d4400aa42c100400070074000d100c041b1014410a0003081146 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 849345575 1250 849344325 849344329
    0x90115030c0b0a180308030f0a090308160c05010501150f0e06041e150e1e090c030c0d0e010204050907020d05090f01030b06030f01210206030a0c0e031501030507060c02 74
    0x10110b4460050041000146007a100380038450081d42501e221103a0606140d4030704004141d40e0003224481400300d41e100005141c41e04522034849030355090b03510400f01742c0c0c0c0c03901c100701c00f01c0c1c0150365078003485a000480d10024000340200c9018003400144071a00c500c8000001c2c00696900e4190024071201a082048540740d80055401b299081032400070780101d1070003424044001a0807046401c10010000741403981c2240d491901564140c0d944d981000d00b151201c83c0c03804400d9080381c2e002503c400414501141d48018640000700408030901d0f0a9440c0040800c40c0e0341d6001008850350041010006403601c44c0e615940700c2001c0c000b40c070503408071050040c2036105408c0030074868051b458112140d42d100b50301055100038080c205a50f0b90511010500c855842441041d24905c5045c0c482001c00c01110078080c24623030f0217000701742180c48500c2c0d903201a080325074900c0c003000031204000d405550100085407800100c1c0a140c0340c2541181400d07414110141c12060620040da09950016 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 849346825 1250 849345575 849345593
    0x30a03060819110f0406150207030b0c0f180a080a14010c030606020613080f040b0c06180d030228051201080a030c0f03020c06040b040503010612020303120c0706090b09011503 77
    0x20f1104403040d04203401e0701400240105895003080b4080700d120085a03080c0d0741c00149800659000e401c50390055582d540c04200544280b40c1100d061140c01d2140f500c001c0300d00134480b01b0b100030080815108a403600040c901d04003c0400940c1e10320f03803003003404840c52030a20410703036080503529040c0880c03410148041d640d800050146070741450420310b0201403000090695140c280003000803540c07140c1e44d50003444c05800040104009018200200d00c0300d1042c420702d01c0900d850a0094007a03c08180c409030000d402803442d2080542c041d4800c2d20000c07100104143c41000389844041e19400d00b50854403407004140c200410540c0301402036800320f5000906040c0b401e034811900e214580840ca001c0b41400c0000c82540e4003ca40450081017142c80d400141c0283c4030250002c024490340c5002c07800a442181602a4264104104103103181c11191040741c1d1000c84911800d10384a425602c480860301c03458000e445100b00350090003a1064280500c15045a00c01c540d121514159121a0f00c2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 849348075 1250 849346825 849346853
    0xe130b13050106030b0c0c1006031101110109020a0b0c061018021803060a0e0d050f030402040e0715030516050324041d0a02040b01090f050105160203030a03060819 72
    0x40c0201036441401008000d4110902840d0702000710700302030034445e0f03452009800c00004040280103202c56122558510700c84d88040300d400450325201c4098100054405002d04061085c295417101c003070f0405a2284500c203401402c10700004c1b543e4682910026003050310180c00b5101c2040c0411040005100b0000528144d05030f8500040c1d645542a9440d500411004411034141c024401004000380803903000b0230380142e03000280e03000e003142d85004441d03500c0b80701a8200c10003000c0c404180035080903446810034003200c000702c44203691912800d00c011488c4c01190030001791100100081d8101d8003080c0308840490382001402c0d0309000d101c10107241250480101c4026070303609580100d55464001d45981c109170501c8507071b00c4403910700042d02c484000c0b0ec1680503600f000440030032540b190007404111103030000c00e84001400c00004550300d40c0139003680c4a41c881900b420f100940c0c1c05000810b42e8008a45000072030914042e8007a051140812840c0040010b5101583c04101200d40a102c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 849349325 1250 849348075 849348091
    0x303090a1409010b1306030c050403060c080601110c06040b0711030601091e090305091e06070602040f06080720100203090c040606020c031e03070f08041703090a030303091410060e130b 81
    0x2d108203143c40d044609e405164000303081da604006204901640200c1058020a802c1e80d40702d2008501c1c0c0010350f500d01900c910b10343c011030b04000c01c00800c08210301410110f03220315004a644d00f01c1c0d03000649000320031303001900c0580d9211002504500706d4080100700000468040c0300313106d4243c030050501d000b100340d82e03800390314280c145042414459942c9041500c0041815440e2a000d04180e0700a402501902030088a0508003241c190f004002c040c0c810441540d4080c3d517021380b021059208507000300810342d140305041540040c0c080340d0010703601c9011000010211700741351104200c00d480c00d560050302990003400001d41a61408603e00b050703c1c001c160750381c07920444034010074070794460520060315981e8441100c0c0d0420052800030001c070358901c00d80302c004080030091640c0700c0c03040d0b105003a03000411100400000b406900304245040c010344a2511503914103100c1c500f080d04142101d201550b03154424800407081c1800302e0b0308500c9448003405403c0381c55940d00030888014000f02 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 849350575 1250 849349325 849349331
    0x906120207151a04180f080705070503120703271e0905090a050f06010803041403031908010923060f22061508041208060303090a1409010b130603 64
    0x1c0240032403840c4486030300801903010000c4407001030800d9880d5482100681c801d0341400c0e441200c60640300001c01015410031101d8443c580f80b0794a40382642c0c400682141c95000703400c40020155402d011001240d1526420701d82c0c2d6117064030b80203040390724041100c030708807000009500002030401402030503074945031855106480004040d0075444800d42c001200f803410001080b80d007040101d401c407101842101160608510f8030031850f1155424001c100469005101c20040d004040d040060328000c040d0950f40360044c101300b0f854801c1a40002d0601042c8041d00402609000f849822400180d4603a61804420b41d190140d52807800901071030321a007451140d070b45003990f40e0001d134a00300d8445155040000c041e018400702805080c41880b121258040c0c92a00e4140108140c134403c1c0e90081c444809006800030545407101c01404158152009020946261b01e8080d0300304c02070f000d1044000a2080108108500042c05800c410f00d014002d0204007191624004400180c0d001400c002c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 849351825 1250 849350575 849350587
    0x1205101701090203070f14010903030f1d09071d150d090618050a06050f0705070311030c0a050f070b0a090608040f1e02010f050423180c0d0c09061202 66
    0x20381c0502081c0e030029515001c0c0d800c00181c0440045030200440b5130030134501003070314074050043d182000380303100141c0031a54550103640454818900c4000816503074450581e8410240003140c60b40e81e0407030340d030004159020384120070550a50002004402c00b156000c00c44858800c0000f0356000d45515440000d44400c001000c11800b904501011101007600240c48410303400c009039114a010310640b4041c3c50000032a80110211494510400903515420310f0004c03641c3c0c08541e003007450004400c980c042404000107004051000c1c40c6480e008030000c009c0000310618080c10500260b020448598082100801c41500505038004650640c100041c0c0384e40c59091802102c030074040700604900401c40c0054601a4000c1850302040c000e0f0703510200440e0050003aa4103219078020076181e16490b018081901c0d40030b0f0f80c441d5a208010b41026014180403c4009010206650780c048080001c550f00c090904030b0702c60905c6001851905080103031070500701a2940e4017801080f40411703000219 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 849353075 1250 849351825 849351869
    0x117130305031009240f030206040e06030a0b3c0f180d0c030806041a10050906070308011701091502161a1f031a070c14060601120510 59
    0xa810013070070090b1080c0305000d45104114a2a14101101600000c1130f14003c030b04070b03004020780350a5a50107440540b9281c140b00c0c0c40f44500000811070740c0e0500c980c41c25140001c2400c056a402850034480950b081d04403403c20300d000d404041c5041085c59010501048a0760420002d16000f40307008640803004c1c1c4400e207402c040c2c10b610041001c420300c100e446413405140c1c450000701d401d6010350741e0201c00307890311402c103c1610300151440c461a40b4040d003414140c80c01500c4400e11046c00d00b011890402d5500100c4c00ca034110f0380b815000308001d1401000640603000c854141e0000c81d100070001034a4a5072003030710710010704010a1107540c0c08590000d16030700d42c03828808001d40190070302d01800c00904a45c5079100e41144d0102d01e001c3c060442c040c4d5411009441801c0d05e501c4080719180e954041d0250f9113020000308220100b00200c281c040205902c441e80307071300c13250041014003100e251040005d04421002411100500d00d04400c010000041803410001d5910100300d0b1842d000607084 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 849354325 1250 849353075 849353101
    0x207051903181503060608130303021c0f02090111030a0c060c0509030312060a06020a030203030408091906050d0c1106040f02130f050402030706020f0d05030c120c09011713030503 79
    0xd903800042c6034542c000702c1c0058860031207080007400c5641c140181d5481d4802100c80003030a0b0341580400b600c80d010003000034069005400840307095030080b0b0408583d0780c60307441a5507020450810b1580c1c001801111544d0068040741ea41c00070b41c004500d4101c5072940145003071200c25014140c01ea660506609a601c194103d450b210b20040889480e10643e09041019032020b40d50f503441000d40183c0040c00c00c0c0085030352010980c00d50043e44c11581e641d21041c805510003102d00350b0040030000140f01c4c8260283d4010302030401503a600351120200c2442c1002c45214240c4032042c071400c05000a40341e50001040340d40281d201c100d42000814a201080c5003c081e030b1159a122800c0070750107134400b89541c0c0017034801e600031422240007a80d111026038546840c19154100368005048188440d0302903402507401072102ca40003468050515010300d142c00c0292000103000030002030340d00c401d607888841300f040c0c1080c070f8041d0802428100d42d00346001e0110000281886000700000e40f003524452 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 849355575 1250 849354325 849354347
    0xc150c010b120c0f0f060a03180c06180e0130200a091109010507030c06150501030b09090712020103091208010612050705181903030917010207051903 66
    0x341040c421881d058804075182e03101080789600444c2400603041c0c9525208000304c0484a014110301c0c9401d0b001107086015000150561001c00048001c0d01d0009003c0d880d0b1200070001543c50f060316902d81c0342c40102e0b20301181d0082e40c0c10742da0380c4010320405002c208001032070182009600204200c070341e0700b58000c105072500904202e0f40212580e41505140300000400d04086136504c1c0b007a522040d8101c11070b240d4084548441c001406661078a5004070014079505000c0d003005901141e072603071a042503800c25005001d207611010f40410031365030035000e10103a900e0201d906081d11b1825480031a40c5171240d1052100c40c4821042070400d6900a92245c6d640daa0001000e000d055403814020f41203070000e00c9108001019591490400d200f1071059174000c1e05203560b46803403c0b105850302d05040485502e40c07070b8009950b60703406143d10916110700c0021840b2380c030303680d04c600d2403c0d001403418010900d044034564010040070700001e4000c601000200321544544528035181d0804a81d481e03030700 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 849356825 1250 849355575 849355579
    0x507030509280b0a090e09100518010204090f0507170606180901090c020d110c01050a111b040e0703080d0f110a02030d06061103192c03010605030c150c010b 69
    0x111002086494552001340b041c0005516111511541e42c0784d48081e078101283c5d116000d0704103201d0203c0741040d0750446a080081c01e440e03c5c0c892011a15001e003240e22070380c0507042d078960701c14200e181c1603034500407254080c443c2e050a4040380d100d1400610014030060049110394800113820a44400075100d018400d403002c0c003014003668440308000010b1040c2c58017000584544a50100c00724440caa00100809183d000342812403600b100544041c0c20441941040c07004050100c0742c244010811005a070601014041ca1755000101f0302045070081001120136410804080c800f15008504a52102c20040790000d803552200088e04000c19090001c07200c0c81070001a90569240c0c000040d00e054110725400300403840d030701c04007075444408120395000160000d00c100c0b0000c0d900892420007032000c41c20310340700c6603034458140c4050b03140b8080c40805120070396040c0451750a0911401010b4823043c1c0007001c8940c0004000740d841c0d88450307801866484009004108004207400c00a040840 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 849358075 1250 849356825 849356899
    0xd11030f18031204030804030314160302010c0f05030723090a030302031b15060d0c0f080a030201050903040b090d030e0310020c0c0a180e010b1207080d0507030509 72
    0x5045a54851810074a1402d01c68800c00560f074584840c01401c0380c040742d90081e2100d03e810302d544d4081e203c10302c5012100802680502c10441190342e0079400000030761085d03000240000d001c01000c0c10349c0305001501e030308112043c07040100700740d040411919090051500451041c0d07100071030490340e1007100380c1684c0209054000008254000000e0060b0810740c4c03040e046005407030888a07030754a46145d428194681c4860204000f030501c00c07141140d045c00b40c21102d0845484640b0508510b00c1684919100d0b0700171100ea2061550a20415421090000c0907514162601c00c0000c02c80c024683c5051103020507a03040810503000b0541140c0202026040c0c0e0005411b4010f598020340081c0140002d03402007801c1040145440c10103082034803c0401c543e8040c000b00c0107100c009090180e030b03c81c03031503588a2481c0055036400c0101c50400d0b001c1001061118244600107041c0310086036403909000052040ca00042e803c20252841030005441c8240c500b0030100380c2000145c100c000d92020851 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 849359325 1250 849358075 849358087
    0x30106231b0618030702010804060f05090c10030501050a061b0b07031a040b034b0d140405100e062107020c15070501060b0d0504060605120d11030f 65
    0x7480d81c0d02616500408016114956100161241100c00401c0000d03a182c100b001000c2c010341c000d0000c10b40040c041c8000260740049411054101c580689020820b980b162503c4541c900d4803264080d01003e4520341400f83d0f503d0000840c0c030040c00c9000710380c00e01586481700100c01030100e0310f22001e160440f58030b01c424108003030090010100b80c513014141104a1400b80300c1400c2c0350242404041015008143c1da1010f424014400fa0703c0e6805a0005142c518800704608002c960709a4119409280e003440c8030b00003180340e880c00502c9001d010901c082c4240c41e460010030241920111707681070f0b40c60358a0034101c480842c1c90105601880f5030100e0003080030301c0840303d0110a0410804100301840d501d80310a402640d40d00180030030240d0140c1c12002e6005008082e1014141243c80303017002007195501c4490a036840d401803003480c500b90b40c0d46c030200300603c4458020400107003020344160301c102c00655016030b122035200300240c0138064a40101014410100300b21030145205a01068840e1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 849360575 1250 849359325 849359347
    0xd02100305060a120b0f07050c100531030302030a02070218040c091116050c0409031206060504121b0b0301090f0b031902220501152303010623 63
    0x11041d904036000300030660b00414107555081c6007130b083c10b40009280146603a03c3c80c000c201150014440400c12109001c0448808003c010308814008907030b0012a081c60424020f090640340881000c03026105032100135042d00c02c0c80070003c3c049406141c0541d5960314440340001a10400900035084000319030f11710a880e440104860046104000c1600c80301d81d036540b03c005445040c0e0204008480400c8083c1d610f07850070104062080c0300d00191802021451b0001e011a4030304981a00030500098250b2218002403080d50050044c07418583d00b007501340030075012070003c0b58000800c02c0202082d01c8420001003840c1200610020201340d030b40f9a110214003015000304441014524202098040a80390106920115550007042c00c0c21007800b903020041c41c0c440c000382108000c45040346d00c8024040501580340a4192101c00d01c0840380c2081000b00119041861040d4501d410705c03032120399806580859045550914010090b0404440f04111280780000241c08055001070546150 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 849361825 1250 849360575 849360581
    0x1c0305090337020a060c21031e020a0c0204050a0f0e01020a0e0f0312030408121f090c120c091211010e0a0617190e010f0b0604080a110d021003 63
    0x1154095016071090402d6000d60850305071680d50080d0b01040c1c0309001e100262080384c5600420740103400c0d8a20f41d000c07100d02c11000791203a11401c0c6c0041d8a031203061034a802560306940d04000f04100c00c518000c40c0c844003c2042e080c106000b4070481d25800410728840c0c0ca50882c1c42c05944a00040003803821401240c2c2c002e500c0a02040003061800d00114036500d0014010070340d1840c00740181541440200d11120158001041141d004c40203104100000754072040e10b5208000d4801041480020f00889501100300740c0c2c0450b0000b401c1c5250340344ea030356112005100c044c8000c50013140c01c8076806015152078074941c001c3c00010f04103000781da041c00003100802140309030a0301c0702158400b41100f402310500e038600540b0007003212603d44544d8040c2070b20a040c1d1045175210280d00c0c0845040e901d00a8450600b11062316030744601c6814641652449601c001900894000b8030301454148140c0d1100341c0001c000e055020504100c08203511201d1160400c60740c000c0444c41c2410a80c0390250003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 849363075 1250 849361825 849361873
    0x80105041a06031f08120d0f0e250b09060a111009080301030210080c03040f02010c23150702070e0c0403020402030f160314010e090a0206131e051c03050903 69
    0x81061204001170038140840ca034290307080d17282c1c1298909244400c403000580f503a01d2854450665415220b1030b407080500042e000e50780c0341c000760045043d12030012603e60201e504414940d040401881c0c24070740d038402c100c2c1c0d01f12005080000031689018011800c280c00081c0100d0164280800481000088802941645d108803441c01410300304c24001c0360704490448107880d807194204003080119400540421000b031052500300a56101d039980d000c088000300301030004149143e1503044010b00c0901240860344c3e120070211545103000b010095031001c0501c15042114042130101c1c482000540071280074540141c4195541e00740113902154030030044400e005070f036441c03840c050302d214440c0c0034080f1880701588442d1030070790170f2510b6003880c00b0000d0440c56440c4949641240140c88a0001d041450540401e220fa0075240071703c1e600c0c000c19004445843e400c90000148550f2340c82c190b01c110942040010140c0c21061464191400c4c4108519a603040c4217051b009200407800c0610035030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 849364325 1250 849363075 849363121
    0x16390801150f0509100f0617070c0201020d030f180503070c12080910020c030609010522120311040b070c0504180507060f03110d05040506010b0a080105041a0603 71
    0x200c007000600e02800d041425001d460851600c0910410080c0341000030550804c08501000800c5540e035601035219031080d620030008a1012950b42140c3c1441002044c0e001d1210b080040c4075500d1640000c0d2940d1501502505142c0d58000e9801c071203966503c6400400f1540217810b10704c88182c02c01e6a0703203400070300040300c072409914000702d0202101e45d8041c0680d0340c0701001e20304180001c0104002d04100e81820300c00c601c20100d8040302c0b640d0811549000d50070450000403181041800d140c0c0400244581096481003502e00c0000222522303a44220601a81f8000400c0c0d800700001c17035090301c1030b580f12000001000c02e0220070321649400300c40131a98100c1d41001090000c401d100b80c120707030405020b04150000c0808000c05401046107a906000074600040d41c09580300b130024103900005403030743c0499910701c100401c2280800005014003142072060f4200703100c0100003030581405002d220300a0342c6440c10600300c2481681c070b05000344c0300148010f4a03458100b020840140300114402 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 849365575 1250 849364325 849364331
    0x21052407020304081b06090603040c030b150102030f0705191203050a0c0f08070306050a080105160c052e0e150a020f0405040b12010903091403010216390801 69
    0x9140c040c00003084408981060001c4c10700165403000102022140c0300d82c82d9007000007004460606c1da146001540710354820001c1440301403c50800c07120048004000c24042003403151580c03003e070707000020740d038000401a031500d03551345542ca001402c01380c4040c40200c1030226021a00100128500d45426500d116901000300d6a2881d56480a0741c2d6541d0a00000c01c0300060030117004e81c403130418164041c000e0709011401c00c0d61840407600840702c9511a4506035515414000f844c11a8004400404041e1504c10440303038690f00c505494421403250301d0001500501d500800e21421202c000400d8903111040045030105054192118030616814120001c2000000d12b02e502c075101790b07070b414031039004410300740b50500d0144002080041c1100b50700008110741c001c2000c0c000d028043c201d61007680e50b045690b24191003012501086100c1130701c2a401804102914107400403041031054114030132620510503200000140c1418a4003214000208580c2e4642d41c0c440c880b12600b2610007000030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 849366825 1250 849365575 849365581
    0x60702150a0825080112170a12150f0e07020f011104140108070f0302090d02030a060207034d06010e2707050d1502070c03150b0a210524 60
    0x14500c0c3c405075441c03040200d03280000612514484e0001401c0f000c0c814000403818160b424159000740d084051440c0004480521049d013112850242d179401d40144104500b040381490b0b01c00c0d00541803401244949a80c6a000503080761080100c2042c4502d244001c2040c8180345e984074000da0f025003d46190010a03461395011544a120b4580c03048002e690f40d01910701d000c8004802a62000704a40d0b48070000030351100c090b0b030b024050701c12001d200d40d04c010798441c003501c2c0140440c00401d034180358600f903003514084694840b0502074600c050440009000f880311100310b9a03600c1c1081d010300b0f401d2040000200d4501c403c0e40ca0b403402031500c03c1b0340714211542a0f6030350b500d9405022800b91507400505040020342410450f065619200d4421860700d0b001c42c0c52024201d0b005240242c40080c0325500030000c0c40010032851403204d20301d010911580c122400400c0c00802c05119007007041d0740fa0320200000701c041000c148d0300d065018064440c8044403088520103085a0070b000102200d1074008 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 849368075 1250 849366825 849366871
    0x30103021c050d0503150909030d1b05070816060914100c020715140c07060e0f060703080402010e0607210905011b170a02011b030204060e060702150a08 67
    0x9440700380e60140003000496840e0b0011200d540019102d0550302405040d40d074440c5d07850852861003010b410b0001d41d22040c0301c3d4012400d40c0c036410041d004614a012505014950020403100c440b0b4200d400c0030740c0c641c1c0340c4c002c54060700070380b00e00a030042e4a0b158400382000384190030a103003c0c2c00c07082250002007004028004490210b0014005a803244d042000340c003129000d054001070a5007440c4e040c0c6240c154035600954031003602c0008030340150200707029450b0000d00c40f0003810030565030031444a1280021a8643c451040003030706106201c2e000404583c495918154800c1c405050b80c0d40320b520a140280e42d03841d0815034240034903114003501000340d114010751401c0320070507500ea01c620600381c050800725415140043d90a09035140410a2071086a0014450501c4980c000203c0c0b0905200348080300c14908600c1d0105401044200950381e1b101c04100803402044510550f100c00e90b00c0003031b2880f0003c0702034694440c40800c02c250f2160300500c510388600c0c1101100c103100041065 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 849369325 1250 849368075 849368119
    0x60515040f021b0309131107051903021b18060406380f0f0708191d0a0303051c1b0e0901080a230c0a0b131d0117030d0f0203010302 58
    0x80e4086d0892104100c1542040da240c000c40c8010450301c4005161011b2a180c2500301600820349510080d4008560002c040d4104078400b1002504131842c90300810440015948112007040d000c8402060000300e075440d41c82d540001c0c01401c1d070840c40100d5804041440f00c07803006508180e4404040b101483c070395541800c04079000103c0c207881080c544088444240c80e55000701100303637900c040c140030082000515103100c2d010305160f40c44207440c1d00050521052078618803c03031180641b005900400000360440260342c0d0160344131481d82c9121051002c42c0d00141200640740e100d500500154071403980d00708098080c0340100360f4008005030b880d0502103a40b5a01c12400031300340902020707401c003515150305040c0710b40b0340001d040d01c90300468400044c180b410140c1003507010900004082010100c0040752000030901c0c84008013803140c001c5204026a141441900328045115400d0800075505104840e040d8000090070064a00e64289004c020341007400100c0c041ca0a0040099942c80012 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 849370575 1250 849369325 849369337
    0x2040e0f1c1b1e0f0605060f010216050405180307080a1404082e0203040b0906090c0f100917011b140306010c1103010c0c0c06080c0403060515040f021b03 68
    0x1442541c2c2c0110030395104507642044100b00420041c3c407103035080018821a540481c0305000e10310205071810300f0010400d01c100950402ea056510008240304020710f00241d103411100101c40001d4103968000002d0380000340b50b1840b4409020014510b010000102d016001040544d500c3d006105040c100c0480300303105901034800700f58003003881c1300b1032107214101c0c44000800e4118500c3c0f50198008941040e60400d03103040b41c4100101003017261030b11080140c50350004c0380c14010500d0305102c0000c03a000c0351107c142035000351008800c41c010a8001c1c031000c2c1c010320300d10350442d80c80d504919086000308058103011140d128030815042c5803510403960343c50300c4020041801c0c44c50711240300542d00141d02100c103c402d007000d180c190b10300d945c0078481c0303841c602619140c0112071080c034940410b00020315080b001c00c0c0300c116801e00c042c4003407200a44040d240c2c02400001e07103072655101103288000018443d0b5202e420800819201e4000740c0203010f0204000000f145c0042c84681001e403a40100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 849371825 1250 849370575 849370607
    0x6050c031e07021e0c240403020120060412021c05040b07020a0509011d0105150702100314070905100207050f06090a05130b1003110f030402040e0f1c 66
    0x282409406031405641c003950050582d0040703581c0e440318024450500303c103410a80b8010307088802601c0c075034145046248001801d0081c10b851b00c0041c420b03203401078040e60101a0400018924245004003005e918516640c003000c12210107142526064650b1116010030400500454240041400f0700380645030400b1215201c00e0b0809041107906c0d0000d4002900070380e804002c0510010b00d40c6c4030051120701a003802c8072400410300001c0e8800078800410b900c0140100703d06540f1101d241c3e02581603503650b5504030b90106084c00c1c224811005000c00100111400c4200e000340b0955603000600f074003c444040c1c400c000e0309a2015001e036125007645c85555004160780001e03041e80d152180c0284811a40145418052511070300841c00c00f80c01030019040465560b036000e038081c94000c0d00480900003d160500028158003121101c07801402041c00c0d03241d1010000c1070841d581c0390800040c03110314804172000c6030a25074210707507038210104403181e11100b690001c0342c2c200d10984852074804e05c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 849373075 1250 849371825 849371851
    0x304020609091e0a0b0f0607020d0f020a211203150e090f0709060f05062506090f0b0a0b040603080405060a2d02071202010c12020c150706050c03 64
    0x10909014811400900000b42503005580c20107019083c0c0f8021805015100070000b0040602c80070b12920f03040c0075402038030440d0280b0010006a03588200c2218a6501074042e03084401316101040110145800250110000415621004500c9080710010030f000700364001e61400c00c000e007a41164110240881107a242860611003011504d0009400502c0d0100715100e42c00741d0303840350341840816003040c07020b1502e901c42000b10440d1f1094020280108459043ca461000440503440b4003901c2c6032506400340c106c401000f80505a07014040c7c250304418641001e50722440c0130f80701b804044941c0351107981380c800c80300b405080c507100e0007050f01c0e800303130882e443c05003000100319854015002000c1000203200741800900c151440e19682680011030841d043c2c0c02c1140068103240e0280c0146c00c024040007900343c00b40c3e070f1107010842010b400454501850014440c205c0c01d04140b4240e00d0740060030552561034000780b2000521100e409000c04120580b180c0c20700108a100503540c0c5006220 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 849374325 1250 849373075 849373087
    0xf0906060d03020309041410080102030709061d0402030103030201090c150509040f061e0f091e15080102210901051303180f030c0e130c0b072910060503040206 70
    0x30302041d41ca41442c000d0040301d00b80856100042c0503038040c9044c6100149030341040c48518004c0d040d0721006001d09a00075400d6140c0928004c000010034031130401005030641403807800c0d0814500919486038003174070540d40c0c1c0d0386a00f4060f01a00c1d401c10219000101c400380010441450810343c854105150744103490202114204030190004002c41d00e042e0342e90f1003000450142c40440d03070302220612480082454908000d4009800070303030744130080050912030071010319200b0300d030345020544469500158050b120096254401040d80100610703602c001503e0f143c0920628a25020400312811059182d660895446c207981080c3c6120301c800705060303000d000184c05440a8503000c02d41c0351084003901c0d03031458241004aa164403d940d601c00440080c4812020140070704e034050120f41018034941816656912003000300e2040c602c41d0b82c2c001c030343c0c2402c0080e800181b0402d003800b0406110b403a88005d82810f8408401e442510704455030b030100041d41d81c09001035a201d55001861241440e13 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 849375575 1250 849374325 849374329
    0x20912162c040b040b090604020d0b070309240e0313090e0f070b1c0b010c060510170d08071d1306030f050c0a05010e090a0b03010e1b090f090606 64
    0x80140e030580040315001c07407001c208500078103140034441d03801210079107941d00701828101403c850203408a00c40c1c0d00300c50200005600e4a031103410050381e0100481d05aa039408008500400d14404000d00300c1025609003010900801e100c10300d2640045400c10125090150090b681d00c500350314003104404074a82041200c1e50344d8003000c41010041e0070f949a08a001c42d00074201500340c0c00c44140c0742404110b02c0c1070494a88510790409a4500c8204254881c0000103824a4620f80008200580340c0d400102d6040c4400403900c000c0441025501d81c001c000402962503840801c0801700048100c0005490b403403040d140b00106001d100d80d14400c0130a540140041d44541d41c0030948102d0310784070000001028525851000c034003c00c003825034119400c040241101450b440541001030380040c010555840c40da01a41145804100040d4143d03502c0c04213024107604054170b9854006c915104990500040240c101d1a008503240c1081381da074014003000800d4159421380099006200007070381d134 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 849376825 1250 849375575 849375599
    0x20606040902040b0a060f080c0901020a020d1104090317091f020a020a020913020f040b061206030c030303100e0703090f151103010f211a0705090a0902091216 70
    0x41c034000303000410444504004108148203940c46400040e1401d180c0607141075103d100e494000c3c40030600c5074900300d14000000c0d84c540012001a00c0b84003070720b4109040140103841ca50f01010090814802c400d050304010b070484000b10844081400000001010b43c4404103041400380c0c04221411115161000300c84c00a4002408041c01d611896031003101580c0c40f40c030400e204070b20203020f08107000b20610501c0009041220b8071401141001c1185c003c6a4680e02501c10044600d680100e4907a03070344c00001d1420f00068080c6815000c0007091003c0101d4018040d01590b040c92011101e1b911507540440449103040c2014012008141c002c5e00082d501c1101100c02c180031034008152100304402c0d1400543c030070ba100d500c481c1302c442000c01000305500300703490b035003001421100486902626611000000b502007510503801090004000e5070140060f1050008040d0040910684520904000707502c603078076444c0704007081d003032101040700001460f00d5090384070010342c40a9441c0800381c2c2e400b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 849378075 1250 849376825 849376841
    0x142e03030c12022e150302150c100e0102130e060303030f180105250206010b070b07050715050403030b10021005090708120307030606080c09011b080d0902010e010f02060604 76
    0x1180580c51104c0302548621100700c2a059030448030034110301d5105081c0089070005a5141055404c000701040075039146a844480300604002c1d0035034480c4a1107420b800d10a030304005050b000d20340340707113143c0303040b01540940403a5512084400b002c039207684140d00704000444e80c09900d54000c0000503100300321642116040001d21074a07240800d590342500342901c0e0b08440d0441c01049030415001280508a880390340700d54140054046541480008180b40c858804c0180032030300114045400c02d8814012200006e03080342548070340d8a050303070001c400741c01c00751026070000e401c0081d81181340c50a0482034890705070b10380050030001303402d1120708083c200051051300d84e130050aa00140c007010501c04e004010911103405680c030300c4c04003400340846400382c211404004444c0e0421074000300c100120f0f09001802d00740340c011105110b4640108042c403045c01400c0040c042200d02c6100c44c15000943ca070b5200740c80d44440108001c004581c01c0100e0074138000185d100e00042065801c0a50010340 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 849379325 1250 849378075 849378077
    0x2040906021225050a02100c0203070b010306150e07080f071b03020a0b0c03040c06051606060312030c05031e15040c080906011401090308030604142e03030c12 70
    0x418650b109000410700c0900300c800200608a12819800595902180d11026040e03824803c1c2802092480250356030316020564408031350300c403403110b0050b000f01b05907001d0a41c031803840d84403981c4a207040c401600354001030610350301011401003801d1a0b001076003880384550b82e035801d6079952641c000800720a4060260410301080b418240914502c106030440a503000ba0001d144082c440e140805240720010420010058140305120019200100e060100c50291130460380ba0460f41000481007644204010328251800d040001000014002012042d285450070440c1c04183e0a05948034401202c10104101c0e4601c244d4840d48040d081c1d00b6001280700d181e050204200c41c0101c3d04450750040100c0100310058200100540100041809400c0b0410244222403400c00040c1800d4000d0000816542d804000100691560361200c0805002e00240300f11504109248040c80b6810b0500c481001989254034000c0450f120f00080c100d80d07156541005a81080d01c515503401494155030b0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 849380575 1250 849379325 849379327
    0x106030b40030c0215040b091c0308130c05030601060c050c010c0c1a07150b210d030e030d0f0c09060306150e1503070327170a1106010f0501030e07030f0204090602 72
    0x417001103089000d840508130600d545581c1e10790203401c00500d0b00b61140325040001c00c50040b0000241c1c0007110940124a070050820191400e16154591040c540c1101e5058800c4500010f40e155028408559960003102a181013034070b500011106c051290740041e154202d409d1301004083d41058440c400626440c08403820300d1410791301c48442032207122003805256196404240549070007040c4140c164030100c0818201043c4640c2d0503202c9640700321180500d41e8a1030f50110001085c4200d4001c1e10400070208840015685c07034500238144008c050000402c010030100d072041c001e20680b419100460034116112807040300c222199400c144490383c00405284a0720300840c80980650b0085c00203482c080b030002d148c0c0c00000300e118024242448880341e8422400040349c901c0c403ca100101c20200d403260788400880050b9070352092403042d02050f00c00c1c000000b400700601072202c000e42d00240c2c0c0a0054059503c2c025555840c180806414400e00c1100d01005280a038041c1800e0380c400e59006d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 849381825 1250 849380575 849380599
    0xa06050a0b210f030f090f090f0f061c032111090f0a051504150e090601110c0d03022505060f03070e06070b060111071401110106030b40030c02 63
    0x40c80c1990050304c1d0b80301c1d60b1a801b1800b50070a14028210b008505016a41c403885480e0080043e04070320fa01610080c12256000017003040c0da22042403407105031b0082e850f0042000c40924008000000c1c003c0601241d4000015101481203180180307021000e04041031070400e103141082004a05036414925441095844e0009150302c80340011003e84004990b55915a032412001c04c6500d40501151801c006c54444450034540d24440a681c00c40360a10700900070103030b140c004600c1c010b1113540f01036101c00049003039007c00d5400141448440f034503440003400840b07002404c40c1444441d0090310ba22200034014100c0c1c0740a00d40c09147d00a02514203500901070810125800341d1200c1800d80d10f81910808000c0c0c0d0f0350b082810700e503c0030b04950040044a24041c811000d210800920714100450445064804078094200002841d00200807840d2030600b060900c00d080b410151b50a0480340d44101040e00c54800140d185120000032486102c84603070790380448440c2c4001c08226406200b072489 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 849383075 1250 849381825 849381853
    0x603050c040e193209010609060b0a02011a01120e01060503060c04090b0d03022808041203020c0d020a05040207030c020414100b03070801060e0105071a0a0f0b0a14130c020a06050a0b21 81
    0xc40004100552b0b0440e030311500c0d050001d0947c1d8030124085401d1240403242c40140e44d00c030120850b130012101300040c8070314a03da81e00d8098409079100a5140c4511018405822029401007084818aa004000e25030703c4100340b0000d0140c2e00c00140150b00015005030710001c180c0104480c99031000b0403114100c000d40e40354451908107412194001c0e544500303440030035404100d8408066000c65280b007454445e5800214405200d0148034040e54010038207030304240c040c1c0200c4100d142e004000744244d0394071101013143c0c480111500003141364125400508128880e00303d034059443d07503460300c95580c20b010007a1050b5070544180c7e41040780c20400365012072500d010451480104000084003030420004250135107000c0100b1340747d15847c3c0504441c40e46ea822000f5000c42d24881800001e107421031000900010f200a4203590303586c100540500078960120724035800c0c91003a4020041c2d82c442922183c11198901c08054228840210749101c0c01c0001c54180c085180e000100c1d4965103503011 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 849384325 1250 849383075 849383081
    0xf03040c080a03090e01080604120e030309040531050316020d140105010e070f08060918030c01020408011104030f0201180f08010e0d080c040603050c040e193209010609 74
    0x441a030000d01c22900c140010a01548091b0040c1445001011603003400e8450b0b2440a000d11512420300400565014098809000b0345044041c0140108942c0c07030100741840c50b58044003800c4000400380c002440d0000701c203400d00c90019402400940c140321401e1a40c0701100380440707003668000d40c6095404c0c0020144507045002c0314001c0c00100d0654581000c00001c0c14020300841d0900003a0010107200c01e9010306d031154000c0c1c046400c00002e4485043c2c4064041554a000384d44d8000000d400840205c150002c0045a003070000802000000360b6200202c1d019030301004003d00703000300e0084007542c4501024845030a6401d00811407030f503190401c2011030801c0c0d100c0483c503510707400301c0341301e0f500c051161603c0c409240c104903180d440c00c032010307152501c6140100701c04c1c50760300c10201e5a271210507000c0e10090154034030303045050b0a09e11403410217620084144190320381000081000205102843d4618001c603d948810f5011104c0071207000800c000c00007000c0d5940c4850000d01c0d824180 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 849385575 1250 849384325 849384343
    0xf0706051512030f07060f090503070c0311041a040902120d1706041422060515090a06031106370906050a02030711040905060103060b120a080f03040c08 67
    0x482500c01100e440820302c110050605840c44160308284002214100c00c2c50442d20180c0c1d2041e400554908101120030040420000203041c45c480451000300308100b8032500015a070082059801e20851441044242d540701c0300d0480c90440c2e0064061428103103504060311380d41c03004007010704481e9500390192411800b2503280c400240c4490902070400c1140c00c400b0713040b0005540600c615072540da1b000134007030000b03400841103003110078505070303c2c940c0c0701800a0100d0340a4000d100c181408980c0600810101e90094800c481d82008511040c14030311559088070f6010345580314580f00d1400b00b00f113541000b4132403c03024403541104140b40102c8000c500304500c0c440c031800c0041c5c0000d800100111700540180003404820401d11201a40003c20380d800254400004201c81c1d00e40008100a001c150000500c036108240000c0200805c6030001d10303a202040d103402a400712003d42c0141d0b00e1030365540203010700e00d00f0411a0032b0072110710015031f8418009c00100100d640d48000c907518003c441 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 849386825 1250 849385575 849385591
    0x30512090d2d0c06091703041203050c121209160902130503010e0102030108060c070b2d15031207020a0308030c041a0c1c020616180801090506090303040803010b0f070605 75
    0x1000d018031001d90001030741700190900d40a8509080014001d07503039280300f2801008078200b96441c51008142c85a011034034003000c0c240c01d07140896140d03540e07140b240c1c00500000d51964003c1d00043c90203500080ea60960422400a5a511500e082d0b689002540300c4a0001d690402c2080d021032103440c2406000310f001050b00c00142e40350f04d0065107a04088010704403a0650004006100c04509501c0c030b2075801c11280540581c5000400501000c809542c0300311403200326160041203501c400b45015004000f406030141c0d4202a015018605188180d4900a500c0344c6010014000f248114000c0d56000035100e21241c9005d844461101c0314007640203030841c00305400a19000ca000013406050407141e5208006d43e8240b1507001c01a4884270001c252585a4500c00305080c0083d10400c800017120380d55003902d2004c01e4032114258081c00c80000280c072184694400320b500840300008403840f03150044001170035a4206114070015a00030300e03408000140501c41e913000700c1c2d283d10405001d200b04c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 849388075 1250 849386825 849386843
    0xd0606020708010b0a05090703022203050c0f0a0617090106080f0303241f02070906120302120a0801031203020915070b0618061027030512090d2d 64
    0x14200b031070350a48450501c142d000e21222801000b0980b103100b00035801450345c0c1005a1100e0360782200752801000006070080031281c1560000611002080803070700800c00b03540002809520300c0900001402030711504001441142a44030000b96091046130040c0600c400401c143c4e0340c403910103150144644440c24190000014015480007800c0d4440c0e00041c075044200406008800044207203400341d00440700341c44000030b0401c4041c0b0034440500580000c8100f040003070785880403221224204002100544102c0d80340b007a00340c50031819520fa8103042d65400c6656801d5a450350b001c4943d06050700145a0244000350b51030782d42040700d00b0021020141c2c1c44d00d424003414907030090a40605100d00903000040d0300034051100429035980a8015200e510385c0b000c00d8141258912040c1195403c03c4640e8601c0e400c610451a51000480340180c08035200a40365828114040c03141020301035201060000c0c0000150000301e101880b010382032070090031450410794104d4000c07880d107070441d03001c0f003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 849389325 1250 849388075 849388079
    0x130203210301150e01050f07020f04050103031d0d0209071404030b0c0a092102010302090303071e11010f0807080a0e030a0e04051303090302061e0c0307060513081e0d06060207 77
    0x241080241142c1d80646070a04161300000c0018015205282900400c0300f80090200155204c01010100204028108010715a034038107004004413000340d039140700c004030100700c010645466605505400d4004080c500c007030320760907401c1c1c4500034403403148020b6a200340400004101007a022b02e119000824000b50794051a140080001c0500c0e0014954040b011100b0f1b1918036081c598244000c1c0d081c00c0040c0d80b038451100180c594090548018a000705541802d00d5044882e0140701413140b140c001c824200100c40b00550b03180d2143c14101c03000031815000030718020f20401c15581c029460a0700002c0000440300ca030350555110b5614000801c1e49010703641e10034101881a20360200c0d04c0c0e050200381c00110f950003030504140c0d00c0041d10131400071a5041e01038000108841c0c901c04081c0034a661040141201516604409415200702e45800001000d1600568501e81c01355170081d100c03031500d08040020065000c00003444c040d941d4082c8104600c04582d40b00f1500600a160000d2211034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 849390575 1250 849389325 849389339
    0x3020a020306010f060203161407140909030306090c031f030308100801020306011b05071d04110616030521010609180902180411130b01020118030503130203210301 72
    0x40b9040c0d000b220110150441003106503408401d444650b9102e000b206d05103200c509080c2d034030f90451840c40295010f2002c3c002080c03c0341001c3c03030945400035242032005a445800c01926030000311195a0404c5011001a4540c40108010360b81702480d60601181481503041101c1c0c1c542c510b030000c80118a84e8014441d071840c401074a40004c001c41300080d4a03602c0c210300000c0042010000700004440510284410020188170140243c6007aa000305100c1c20084100e00b40309001b91001e50341c1c0d01c0c60010140c1c080c101201240d9000c8446030400090746401d07a4121102d600c05100c904400c0c400c0846102c1d030480307207626140207041c83ea4a10341d45a04205404060000315180035040518040c0014016100c41c04055034071140c04009004594a0741845941c0604800d149580f00c80516115003081e0030303c0c0e01020007068280e008112120940004503040d0a82c42409008a4410b00016000d0f05070b5043c41d0a01c40e01c0030703050342c18030521a660b120104001d41e40b21301e0b46400100c0148402 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 849391825 1250 849390575 849390583
    0xc0308100f03080c06060301051b09132a030501052b050a11030c010206090a0206030c0c0f0106030b0702161a09060f0403032304450c0c0c09090512040303020a0203 72
    0x1200c0120009c02c044d00740300310070201e401481d12a0085409001c65002d083d90350741d400c01980d605070040188008224142c005000085c000011141c03051002c00e44a6400d10a200d1b250580304050800c0904001c043e1600440c11901c00f00180d0558030300c50400001030090003a00700c110320030241880748c15034000416040c1000c42d4a02411540010204080c5400004080e10401c0d01554038a6880c0c861340a07200c03051280807032100c2148550014003801480550050040300d014016480d210303101e00c2c1003261207030080b400c841483c140c40030b018000500c10f031541c101d22a8501c2c08681c40d0000e00e10106015800c5001c01a002003000319042003410703000b04006406035041c400c108107070400c031400785480740a14042d5800c0e4401d01580140da070b10300340f40d102c106074000c00039420304c1040e00c1c0b682d00b64040c1984144da10702d500303004000500b28041c0014514a903440300340090040e0503c40400c00805000c64152141e00c03441071841c608510303100080c0003450003503000d8498140c00340141883c7c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 849393075 1250 849391825 849391831
    0x9090f1e05070311180904050c100f08100e04110303090d060219030207050303070806030a0c080d0f03110706050901110c0f06240103050402010e04050901020d0e0d0c0308100f03080c06 81
    0x10050410014080c01c52100d0b11700414441203078040b11903100d60414502d0103a00d00250350700300c0700201a0205541d00b1007030300e4424070400e1780c4a001b41e0345e40841018146d82c00d8480c50003942044404500000d60408141c801044043d041301d00f010301303400000700031100c500300a4982e55400141984021458011500503060906007903203020f0b0660b949a560340f000506c4801003000c0b44010600c4c9035414016510303d141c1003e01c0c50060750701d616a0986881000030343c54081805400008040341c02401825000550100c0e09401c010894841d50094100100300460701e5680700301d0303a03180206d0f140260a96028030350040c00c0c041c0c011086946451001f800c8040d01d901c0b0380c0c441c1d0300b41490324296030405d04800e1a01080c50f40700c510040e030b5180b0220b044268000c1c00d02c010854640c0055014042c8035030b039900c007403000c26050a00d0076100c000803209400003815600c1c081010a00801000d508900f03800042c0d00070b0755984200030100b44c801e0b0403c9401c0440003643d261700380c20401089030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 849394325 1250 849393075 849393101
    0x1602100c0932222901020c01080a0207050f03031005090a110301090c0e04050f09190c06050f040f0f2d06030c180e010f080d09090f1e050703 62
    0x400c07640301e000b04210304a0580c2086124526034402c80b140e0000c8144818120008000305001000e0100c111002c404a00920401d80803c0185804459840021890074070401a19210034680b80c1c03e441101030350000a0954041c420610080b0190604000039841210030040d031507003240c2090704001c0f0f00030707003c1c042080041c14a6406c81004050720b013101c0c11030b00a10000242e09000c00d0040e11544002e1800c01c1c0d01038907010402032100d04240360301d4070030100e42c0243e49034000c2d031180025603400b2914000d008411003a80510545010307100400080700c100d8606421705540c2c0701013545000c06034002c3d0300d554017044010008031904034001d4214080c1d44d403850343d00c2c0a400e524085141d800744621401c0513100c921001d0300d14096004083c80040c800f180c01c5603507443e0140c0e2414201e0030301c0341800c2d81110010016241300c001c242c120b2a840f0315501e00c5000c62809070248041c00e00d28200c0c900c060340d01c0078800e4004d0049130891350703585898503000c00d2500e08900302904a503869403c1032 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 849395575 1250 849394325 849394379
    0x506240d142d09071e080303040f021c150203040614040f0501061403032223030d050a020615010e060309010b01080703020a0c06020d090501020c030c010f0b091602100c09 75
    0xb0a081c04042488029503070302005c03025094224000403080c40c0342d10b1744000c610b070100009001c18008403200101109009132440e04d590000120808600321401c80f001d0011424040d4801e04000315400039500315001e0300307003c610325444900c003042e401c2c01503800b243d545c41d4500030001000820f000782c4005052130003284184d084800017283e00ca01c60032031039008801d030080e090440d03080740b0b400e08409401d090302551441c1c8040f500c4200340c080c0b2411180d20034801e050311012141e116a0031a07003209516800303440726842c1c07120f10800e4400c800303039800c2c14402040c40200407131b10703403402451088c00854000306600f0a14000502072030005000c08003018010054075501031382007441d12006d240e00000041c0d494000ca4040c030000e199408008040c1d500001c2d98480d00705000000e40590b050507402001903420384100c0030103c0c1d2034403d905400401040c00941e003041c01c02300405005c2e01d180140c0360910b048902001c2202c0b100801000481c0031084207119500a58509207009ca01c416030310 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 849396825 1250 849395575 849395581
    0xa02060603120f07060e24010f060e0904050c03010906020d05060901050a0b0f071e02190e16050d06171006080303060402031e07020703060506240d142d 67
    0x221814400c1c0980500f1041c0001018030402c10240d024019569165007900c44038004454050350410850305641000e50100300003040700804400c60034105c0e01581c50300501300e01d20130144541c00c000204180c6450042d4407904100f61028010f000000d0f10a01c0300698980079080500119000501254016410710f001440b03e5194100c1c20400e072080490800d8441483c1040517195204c0c41030001c1c44903125503a035032045080d42d444001810f100b1144e051274030ba0b401d0302c0f007444014240f00d071000e8541c201e00880c9002ea40f1b0240415415546d14000d0301e4800c90345034003002c0d03518503440a4090010340d441804072180c01c2c403801010043c030513414404d1900d402002c550368000a002584555800004180d020501d900c0c039110078000d0310918103213840c025401940350201444281d50060420000907038520b405059803c084291071490401d009243d20701c00301da80c01a103900c002059031a40b0341103185c031185540340d110b26202100e1050203038901c143d03540c5da1034807051080d008004840034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 849398075 1250 849396825 849396853
    0x926070c0608040b0f060f130f0608060405100207030318110a05030d0507060c0905030607020705030d0509091308270f01020a020307151214090d020c0d0201080c0f040602030a02060603 81
    0x10081d0808640d41a90080e40c44400010303100464007d4100d0f03201844203044980c0300c0300c6401c07000c0244242081002119a5000702d00d443d9a0200e03801021600310354011131f40031a4541c09400000d001c4d00d0005400030ba01000101d14104400e0142d0700c01c1d0100c1207659041c0380580011b4080d040503000380c10140d0104001078014003420b02d0085c01c0b42d8035203802c1c3c28818031501c400c47c01402c009007128001d00b0003082c0070f5140c0c141802214041d008038400440024041c8046550310040901450019170392089101848051000200c07031800c070400209180e40c001050261440b511183c46a190315403920030000c0100f60b001260b819508140c0711000503950118483e0110f85200c05104114612004101c41c4082039034045c040030b918041d1000030040e40748074038511403000d4100326803d40803002c1d07090744e440308441825980140024960001075101d50010f5400c6400540c0035424020a800001420780154001c000140c1c40030a019a450364104000c5401c101c098014202241d20410 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 849399325 1250 849398075 849398093
    0x907051303080304050a0204020a091e0302060f0a0e030f01020904140c031918060b21070527090c0108010b040e13050307050115050a08010608100926070c060804 71
    0x20002d45014404400141402014420401d0b0990700400440d038400c1013000183c201b4a19014074615520340321a5904c00f030441d40304100660b600100198101880080301d51000c1d44043c01102c100003508080800039141003000344007540c0044005605e4140440500080b503074810714410600320b190701072001e04c1e80e424085907007185100d1691102034004076881d5000d402c1d01004002c5101c1121203000511590707034400d0b0100203040766010105400c0002d0b9540f07400b14000044010b0704014001c0045141c40880c9002001248011020b250f0301b2284c11017030352100b00c560f01d51907040750303008007113540e1310907082c1713001d068203284981c00c20382132065807041c801c0010480210120341080708018004100160b40d480c0b60700c40003d01c0001d000010401d0700f20700c0c03889800d010754818103020420304018055507054901c408010847c1c24907901045020b04451802a038090084103145007103000003040f600700100b0b440c101d556490ba011700d440c402c3d50003154403010400907440d0900c000118982 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 849400575 1250 849399325 849399329
    0x10e0601080d021b0d17120f010e0105040b0112150f030507090b030f1b01050910020d02160608130f1218120b0402012a0b060907090503070303030e150106020c09070513 74
    0x602d0355102d06e85883c3c1440300c42c2c41510f55407880301c42c4007810441c541248114060603510041c1100607140d80e64014071051700c01c0101103502007180c0014143c0c142880303a1101002424071340f000c55520303640e640072100000c0076800a44036900b2403201440034440350302501c690f0400580003014010303084843d40361506040305003000400c8480100c0d000c140c2c407a0f07082c0c900700000280585c2c0360740700c2c200c400f170b5840b2080e0440c18054024405080610300c0d071101c01c00101c0390b00d615032030129034a081d600900a881d409048030907864940ac600041341d29040c4903008060350b07171500c00a2070640f20010300c0d0500039500c0355041d8086407104000240c2d000f400c241d000741c0e0a003400c5040042c0c4512000d840d025060101c80c030120002002e00c07e001000d8541030103041d061f0b130740d040c09071502001203a90400340d00886070103501c50581000003a200c0e500c03218054080405a46185401401c0d102034030f0380c20fa00800c0180d01031003c00c1c60a00d04415515001007950500f41e1800d840e034414450400ca4038 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 849401825 1250 849400575 849400583
    0xc01020319020709110a0207092706181a09031806030a0b03160303030b030d05040b130e13150b101d0604060305010f09060521010e0601080d021b0d 65
    0x80c841d2500c10b00800010010740240802800700ca4449444003200c1e0700000440700061150440000d030203072580c81014881e80200c030305001580550010507214001ca00e004a65242d0b4814910182012000d40907010700d12a4503607070020540c40d032f246010300c03102401c01c140300d4208203c2090b007a55140d4076900c403800e0540e421912980e524003880003c1002c4088c4079014026140c0000750380d03c5c01c0c440b900c2a20300c6038030200302d89031090f02410781d50007103141d145010440802061021000210203011180c0542e054210315540f1480d15142c07a400545628041d203c400e14481d080107a0303085602c2d98911400c0c0308200480107040001c48000c40030350404140040034a5800b8400804000510401c0000d0b0000f5035482d070301e1750014014003091058125501c110b1902180e4204180a12000c9960042481c000303800000104083c614840e044a200c540d6201e41609952105200450081050401818010078400806424812540981c0e002840e02e0505080c480e61100100e81007103402c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 849403075 1250 849401825 849401857
    0x15010f0203090904050708011104080d08060d0f060b10051201030839011104060806040b0d21020f010c080a11040b04150e0a0b121504020d14090c010203 67
    0x8408180d0451195000309030f00040164200300070b0082c0040c2d841d0403913899000030000743c0307401e00805000e0b00650140d0019034000c8420b0098a5101c1c4401d90780ac40801171030b12060302c400d541d991105d01c2d140c200449865488162002c3c1d1490000110390b0405404e003007061900c501c010520040e000c05010052a803900400c1155030b00c2c50b070502a4030b20120907580803804032a01401c0d261401c603c4050800d1560030a080074960007804001d48003110010f8480074466128101080080c00d020b0303040701d4100c2344d50342c440c0c40170544a83c079000100304e115942e60032000046d00001d090144c040c1c01001582e0529611041d410303401100e0550003078a8100010343e415030062034140c41d1050368094a10b10070041004240858003082c0c001003501580c46001503d011032083c014003100302d1055140340041400080c03502c2d0186a602d0758011811040c5c100c0b00070400e8006000c03a00311944003a0642e40c0e40440c0d40c48800b604900941010840000f40086291b44e00000e681e8400c840414a80c901 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 849404325 1250 849403075 849403097
    0x31a01080c1b0316061508030c07091109040f02070204141b0c070914190c050301050105070311060a1a030118151104121203060602210d0509030a02060f1501 69
    0x10910549114200c1302240c3d140320724003410680003800d01842600429950940300040c2c50000000301c4054880c40c801800103289000781100051040d0407100000200404c1900d07460b0b81c542c0f28442400014000040c0c0780c0800d03006100031160318111042a13010a20144068200c840004401d2281c41d0754816588036103146855060551765070081e0582800c2020602e881003011508070300c81c0350003081081021001d440340000b075449100000021440c10401070019522681c0109143c0b40a400c09065034030102c240715181000803140100c2c85a81c82805d6110140c0b4a1030307580909000700d000340714941245064001ca58041c03a80142140e07060240b000c1d0762020b64004241e6903150790141604c541c2d4030141c619000a0420084500f14101038282d4081402440f13004140ca0195000385602007280e05c028024900322902c0c200808824082006603111a0098921031003100c0055a15013070b9100700a45807200c05020701d94200311010030050344540360902c5aa40c030030b0910302406555 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 849405575 1250 849404325 849404377
    0x503060d140307080714070e1302041d010c0f031103010519080a11040612150c1206120203060c0a08040602070c0e090703030905030313090515060a031a01080c 70
    0x1805544101c01c0601011643c41c091108580250118601034458550461210810740d5294030351401851b4142c24800d0226401d17942c0350030782035560392000c1c0c00051a07010700e03401e06040c030aa018852032640c0d11008082102c95100800e90122691801c00744800d2401e070714920014001401400c3c0211105a2003802c1c4014180036900100480c10603184070380340300d080403600460000b0350079000b80d041c0701c00001c007103000c0c20802c0c1200b40c00109401617481111050703000b0b0600f2281410400055480c100d11441071031240e0750007091100b219100202e9188145820104000c0001c2000503060081c29119508881783c2c0e0f5015500c80b1006a0702d00aa140c0603030031542075040242030403103881c10403082007030018004050302d0003500d4494490340c0c0e49003015668031aa80310004101007030001007081d0095a0445030300421540c04080718004c01d54003042c50390f00a9510000029202c0d11112800d045181401141035030a1a001e00145070021005d2041c0c84ac3c0c40c2000d01502c6140c8a101d46a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 849406825 1250 849405575 849405593
    0xe0301062d1707030b0609060102031204061b170f070207031b0308120915070c1401090807120f0201051e060a1a070c12031b14030304080d05160503060d 67
    0x2d80620030b20766003039540000e801c50760f400f0680001c580c0c0b5103004000c03070b0a9190107201180706100580c0218900000680300c1c0840c1c241c06001260307200e48900f0058209980300c405000000b2081e43c0d250440071361755520b001488800f1300814010100c6000303001e0000d5003c60500f01b542c1d00030405403040188440e49a0f814542c41d400500138100100301e01711203100c651120b9001e07900803012039a6000010700340da400c0ca082583d582e000700e00c0c0324900c000002c40d10005d0200012245000141141c079a03101d008590f4044c00c011140c0000e0100b10000240d0410183c0b6136400080c80200b00d280362040307d005080b25142010342d646118000000d2280d0b540101c03c00184c000505c080c001c0f10014074082c0a00d410071003085602d0411107001049030f00f89402c442c850326405070f032003c0109265500c1c11684c411485000e41c0d05c01114403980c0d405040030030027140224820520b05a583d141d2500d64012104090b010035100301c0c21002503010396503c4030613039403c00402c41d041e50f01c1401c1454110b00c6 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 849408075 1250 849406825 849406829
    0x8250807090b0409091101020601140d02030114010902070c08060108070b07110a09150905040f08300610022a030f0703061a060f070f0f060911010e0301062d 69
    0x10440c00080114040e0101d42011612a02c81d006d1560880c0448006a03220f101c240541c204045c800d9249040910701a105400482d00180c0005840791441c0c16140d2804801d81065210b281c0000d01c100410100c21103410003012580040c00c41075040c840d8842d1198010f20600c020483c02107080e0050014240e0342110784900100800c8503140e407044404013504a802c001104504840400281e032003aa001e41d61049a015840c03588034010307903032100c1c07854000001c036140c0307801c02c0150500f29050203803000214105416020700786250a0007004014042a0b500310219000f400b0703031402c0340960981c4030007800d1074104d140c0300350064080401c0c80c100d0038403816023907446450382c00018010b1940c0701400308085c040c441c83c1420840b40511007544030701c900510039001d00b0003500020404180302003046520960305000600503a44510085d20031000082c3c0d41c000030388507840d41030341e00b24081080166080d80248079003440c11854030045402081c921780644000c0d60781c3c10034401c8800220340 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 849409325 1250 849408075 849408089
    0x8040509220f05010e011e09031b080304060f0b0d02010c05010e10020c0606012a11060d1a01030e030a0e03030c01051009050601050424030920010825080709 69
    0x8200699080c0b01c02d501c1c100356030a840035440c1801d8a200791704103000303050b45864444280d800074546c22086000411600300e040c1c0410040444824481141c0031100c5c441d140100000d03901c0b81043d007001300403120150300c01c0551034501840c204081e1640494840e803103409080c04540392956013030407405024002081035980c0111800301c1a0030140d68082c000c00510074045903c0356940c81d005413100355040401c82b2800f8400241400c0080c1c601d440c456410344689036040304400108089011600807a4880b91151389030035034440010702d40c17603400402182c00d2a091201d1b101d0042c9680d2203201d6003249030308020445103028090740301041103540c0b14840030005c0115140101d07000d039880d8964051200500c0c02c0101203410b961140781034406071030003102c0095201603e00405039268811842403400e0544400c0032202291610f05850482100711041a0362140c0c038400040c0000700040051410384680008440758040407984a85000300a00703041040b03031160107090724400c0d09548440 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 849410575 1250 849409325 849409381
    0x150b010e04240b0a03050901090305040b030a1b0e1206060a0b0702040e10060503070f06050f031807030303050106030f02180d031106250507150519020705070f0b040308040509 77
    0x2a1100c0100000d0001c044d459034200000d448030100325090b102031100c00390001d00c090100340f05000600d0700458105000000c002620446c002e8680240c040d400c0400e004149521100315082c2000c00110289208100140c0028500340001540e03000c45409400c01007000801c01d0011511a64081c0200103001c03800c0f40c410310408242c0c0340c05801580105802802840c0340022007048405020040e40c0007900e40504002001048045c1900002c0c41e040d032081050459440c0c0700002d01801026500a0f44d02080560500c00050151441c1d2080304c0c1f0494410000382e0f40365560f10100c845110400c98401701d074400241400c550040001d03070010b441c7d010780000e11500c200b01c0c009281001c0f583c1e8040c1c050110100300144c0d840e024089014106d0088160030f0f4010b040c031540701d1070388008060700c4008550f15190349c22040341c2066200300c413558085082402060610103120000f850f0000040b894a400c0d80e07a1085203001c1e030706c907a41c0030740300000120380d07a50f00848d80920f100303c52000c01 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 849411825 1250 849410575 849410579
    0x3020a0509090112050d050a05120601030605100c05010b01051606020903070b0c15060d0210030519020703050315030d0f141603080402040b0907090501200f0a150b010e0424 76
    0x4c11081000903c00c98a0780710790165240c01c503000f14240c8a00e040191180340c1420f440350415200341d4001804d076410583c0c1c0d6500440e0076aa004242040d040c19070b5108e14850381c1500d0301600f19903c03c051030307050040601803005100c5001440a40c4140d10080268803a4408000300b0f00d40006a00070017031140000c180702400312400142c0c501042c22448170003085803182e006201c442a40600069041014824400d034018000d410107070b00a241d080c80010030f0302d4003c850038101d03000680c080700025800414007245c0007145d112400c031480f0440c0074000d6007080c54400760080841802450900030241b01c00c8400301c02032004d03981c2d0310150340c44424a040c1d6a20700106804001c0710120310851400d00d44100078244003070160312610040d29907205490514006494803000b811611090000c2d40b50300c1c0046020a218001c004080d45006014040c0c161030b00900000030042c1d6001100d11300746104945a0348025060310648042d10001070f500c004040b00340c641210f03614075070b22030b4501c2040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 849413075 1250 849411825 849411839
    0xf1209030a021203040b0f04030207080d09031b050d1b0504110a20060a0b0f04180c08060c09010c0609050f03040609121a09030d0c0207240f03020a05090901 69
    0x140800d0400b6402d40d10314400c0500c01003110300040c0c9019042a4000d00098141904030b40980c0c4c025003c2d00483d0010796940c458545013001d4a602c940000d02e6001c400c20400105981c18080307030300c1054031860744506250208103903c0420750050310080d1462145040c83e41c401202001a22001e40144000085080041019030200d0a208000f42510000c007482c0401f11a02100c500b0172940903001984400c03c11130b020340300c142881c6a1014640c0b08031501030703465110380c04c000400707521756003107107540c2c0c0c00e0544c1680c005910200d019040841000610701c0c1d1a400c440c00075a003400c1030704443d07500e0b0415000a11031080001d159124000583d040d4100000151040750495503580c101030340c6801d000102180a820024031048582c219024a10315001606030700601c685c04490a001490380740301e0554043d0342420000da00300103014020341d54810400c05000c1300441101d0389003098904004c10344490300ca1140101507012600c440c901d48103404a03108100000d051056950311400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 849414325 1250 849413075 849413077
    0x2100c05250503070b160f050d05030708180a0b09010b090f09010c0516170403060510180e0307020f010e030604060207020f0612130206040906140a2411070906090207030e030c060d020f120903 84
    0x1103181c08070740400006054031115941c40ec034100c030000b000d4190000e47c3d07560030410701c1e07020340008101d54035000408402c1e1109902039120304220405207260b402c0140307409085413000c50340e2408114040220300c0140c9141d40540c90b446500440321103202030038003142c81a9010f26007005250f242018140304402d070312001c00c40d05407050241c0c46041c4030605140c03407045031210b4120754526001480000094540501d40016465042c107042d500621540c0000e4100401281c04684d00c945c0407070401c06505081d010101611425100305181c00240902c000c001c8000410034000300c0142c0040030300315254101520300034016110706014281c1c40301110b100a1042442240c015100e1500000301283c010940001100740c031100c1039000c0013841c401721303580803800101c1d507400d101d81d001c0010844e045102e030030001c4c01d1440c00117842d580c0d1840c00411000009030403d00c01d0380941007441d0300c4d03543d0904503110050310003801692480000d614040034060048654540c0300d03100c04214020360048 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 849415575 1250 849414325 849414331
    0x409080325020f1b04060b1b010506011409060d090605070917030426030f0a0c11030d08010501050c0f0109030c0b2202100c05250503070b160f050d0503 67
    0x380800c03922007441c0300c2207a64900140200324030758440320120b003028010900300c0c1c1d4450030240000c6110740c0c0f2950500d00d682c0c05140c0928031034242d9000800040020310500340c00c01d5091800350b4000052160b4080280514001c00f80f0412000405800d015099444415040c0c0e0060051145241c1703910060304004691044001d0003042040b038402d2240702104031410303a4540003003210a01e01402d0714100c00c04031002070390203a1100304242484000050050003000c80c050b0b490a0300c1c80301c1c03442c0800076020f0410300f0ba03021307611050034444404e400040c0241919000c0c40c00d992240c100f502c0315403410010710b0355080c19510340395102c1e06240c0d01c120000b5010303002d00300865054071007003174919810040c540140c04505407120840010304c3c100c5000c410450b160300d0020205100741d00c0303060a00c4044a0b0319028040c2509240c0c03070200101a0441c01080b0031005001c00c0d038a030100303c000da03104440841c8003404441c001e4004004801050380c4003a5041011501044005d51020301554816 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 849416825 1250 849415575 849415621
    0xc080c010e0f09040b04020d05030309011a040c0207150e0406080607030506010f0807050d06180501051309150f0905030319050a060305030901110705060d1d161404090803 75
    0x4105100940d0405800d034608242c000b809008007560380792070300d0382c140c038015000b00e034004000b80200000ca401040a51300403444140001404541c81010680c22110001c199004909143d000071075150049011012501c869840c0880400081d908807818900d45004542c010719004022612090000b025485540719072070030040c0c1d40f542d000540300b00e000c0481240c0007400b1140040c0780a48030300702901c201e500448000c58410340b141c0300e040d0005079584842c10300303a0792800108180d1400d40814030412104220402c00301c041e544074408006280b08510009030740719415402c0c45542c0c4e40c000d4040d1038101c03081e80d460b0300345202d2103000480010b1210210340e040c400031030341c2c0e004c0c144260b000312544580110715020042e00152580c40300000a00c505000f01d410029540e11004000e06010f610507000140c400b444075845110350310702c035501686a900c40522680c1190004c220340b0159180c448880a289030364400140103400500002880074502200388042c55459201c1e08060300b080c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 849418075 1250 849416825 849416837
    0x1c301d070603020301120f050a0b010305010506091f060309170408071403030a0e01120609060b130806010602030f070512072d110f03071203110f010207030e0f04090c080c01 76
    0x61840c040b02039020030300581d00103900d4540d2400001e041c0d001007040c003d10800c16150303c0001a05c6603005030070700364400d48850b5143c90811000d4505014500d80c040c2e80902c1c1c3c002a0311040380303140850505401698185035a070030000d4107010301d903000d038541281c3c504d001958031a190314401b6203621081c400c079041034800c081a0b41c0140780200c00d48a007446140c0e1490500c0d903481004590044412440d184825520350011540316258005d480c0603003082001c00b41c2e550340352101a071006a80d035101529640001006004241c0d02104403078031401c4100ea825100c80c51420151305000074a0b1070601c07200c0e0f0000d5503204002c03071320500d01c0040c1001010380c00e04024003600c0030014030801e0b0f0009c004c0707178400f03440114900c4c10070403a02d440b041c06000c42d000707141c0309c209070460040c0e110300c190302007140411400c0085008008509103000324400030760a100140d58050300d00243c02c111903226164905d1060260b444a038040428540c0082c1201c01059a520b580707130b225945050840d0010711 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 849419325 1250 849418075 849418079
    0x1182301121a0f010c020d03020106150509090f18070608041109100504020c0c0301140a0b0d050a03120f0207030903020907020a021e040e1e1c301d07 66
    0x1d6031245485160740060541002c404140420840c051105100303030500200c0726155015880d10705545140c14801d400004005040810b0415052203201016041000402c00d2258075124000300a1304040300c44698949616600d50482d2000c00c05001845140b00705100010b60790303804034000e4000c83c0600b0300c030454000120280110341c0d5044814284062000b001004181011360042ca08416400300751055031180ca1300190035901360585082c1795a00702810b2181c0440d05115550895a04807500031090b8820b99071151201102500502403080f10001e000341002c1a03005a207000e4502d40e4110354401403444c010f001942203000903402001c9600c000b0b00001d0000407400b0000d0703001442075154000c03400c0b1014440200d4648a60041d490700f1213000b81c0c44041000c800c41c201406a00031000810040c060b1600c00703660b14400c0901c0840c00c1044080350000b1401c4442c003903074820300c04101c81101891200119004c44231400034907140381504031180000601140612040648038030301e03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 849420575 1250 849419325 849419357
    0x504080c0a11100c1124040b0d0f0b0319030516120f11030f1c05190e01061404050702070302120d08090607270506030117060601020604030e01182301 66
    0x8a00c180d000303101c903803d50382004051501d40740290b06c158401104202080300040c40c011142c205904c0a0302c0b140c004500c04604107258010148d070500580000c010f070740e601c03000080d40d6034591001010f50b00c1d20243d040003403510501c00c40343c1c501d170301008415841003946046020700c68006a403000250b011f02c0c54040e458420034070b0b81c0d00304c21204000c43c00c1010540e00501a03a00c001a21805102e81c0700030304075481c1c254003916116860100d001c500c13119850130f0090a0714440c1010b0300999140100a01a4201c81c01104070640c6082e2000161a41c030314006030303e4025a500003a512448240500710700080c0014800100301190380c4816007910303040c11160390307200309440900218102c040b440200c000780131210b500742c0c82c6400c41464100e81e941d01069946d4801e800040c0d103640c0340c039000c400f40c0404016443d04100c0a200a10b40c0e450310740c8008210f03040340620300e4100b00040681603180350416900c00d0107002003280101818055001c40c815a46540c4c01c0b0f50301040b2054030b084811 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 849421825 1250 849420575 849420587
    0x411060a0503180c0f1210060f080d05160314090901090c020d08100501111911101d06030c0705010e0a020306010602161503020c010e010b03060c04080a060504080c0a1110 75
    0x10320005000117204036418000c101800081000d038454030b1080380c89030102c006403401108003c0a0b829a0b103a212810100900c0c248600c0e080d000003070103010401e00e5651000c01c00400301c0c5a8140c40c050f407060b080c0c0415840b440c0701c0d00c00425441a038000020031100401c0c1d101d804142c045400300c13061601c0d2403a0549101104555011a28590b1202000035500910380040c05090040950b0790300000302c5025080c0c0e98140c0d10036034440d00005444065800c1c100d190f01403101c16403e0818000d40110b854051400c52015101d00400b4040045110b80030b040d01a554159030080003400071460400d09540e0f1000e001409038070900c1604000520a4000b2900038120107680c0e0300089110b0400c00c1c8880d50701004622001056400c11080c03c212800788200000395000100104032400610105450108051302c04c109560080108021840001503d00343c001e07404080461940e0f518240200749000c3d008194400340981d212000422420030b0410070485000c45005000a407000811111 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 849423075 1250 849421825 849421843
    0x210051b1905190509031515010c051f020c010c0e01050304080a1713031e02030d05040606120b0a06090219030902220605040506030d0c0b0411060a050318 68
    0xa036a00422112a41940300810900e40c1d030741c50300b062840d162043c10700a03850a402c4200390000f801c082014a1146810711003110904003c0588100c50704040e01440e55100704d05905d14107100400c0da400d8100326042c84000b00201c0d0b42c85008441d40c01215000c0040c3d400042000308a5180c107121b2204180500f104050208040e5981401e6544650340c01e0404e41c05001d100041c09600c100c4c003002400554000742c8540104c0c181852000130504c3c018005072043d808848540d021800004c1c51140e000040e250400071180c4041129200e03820000c004000308d4200d04403c2000013500340510010010060051040403810003030341e0395412404c41240903c140c29400280d01c44c2c15030032031178480d41041c03121038001416050181d8840300300100454113041240143c0c0c0c1c55540411091500c0d01c0741c65402401030340a00001c00032400700070603840300c3e04402041d184480c004101406404040e800f50300720080c020039661000c0e01c01c0500540c1044070808003c50f040c69040080d05800700300208 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 849424325 1250 849423075 849423121
    0x9050406090c0f0c062912060f16120f0903020d09050f0d080904090501060f17031e0c010c08010918170318031207110312011203050705010c021005 65
    0x20141c0d040f50040341c5003019580d060311415100c01b50305101d50480d203003c40801600c80c034505201e00180b020303c04a016004111031658200804000b000d80d0b01d400030503072002102c0941c2103a102c25900c140e030f03152010124507100d68684040b00b10b10010680c465001c0300d0181c0c00702c40c00003031840411210580e190050a800607480c80000c0c1c828104075034402911441000c81c1ca013094220300210701204c5000070140c419a4583c030301045100403140d4424064491080070240300680724880d15070301d1288107000da50020020f0003614541541348159a0010403190007032141200d1031000414403502030086038621441c05c9204048038084803d88803009031312010811121894140034903641d00001d00b00309494203861f921000030b010900080609640401287d20300382080c41004204030704020503542103501c108540c00c41a8284440641116424000c07240c68a016180c100d49601508000400e1582050b0035206400e40108010344040b2401d00100180c4c0ea5000c803005004400940c0f5075 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 849425575 1250 849424325 849424337
    0x250507030c15021914060a0b0a1a250f1a0705041d040524150103090b041103030706020409021206041808160c0b07150902210a1209050406090c 63
    0x40c0c2c820028a84e4a0580c0c001d20402403140700845142e410141c0072030355000642ea88010051162421200602c0500f2001400d565a210085281c0e1114461030030324400001c8505d1110705e1100130013016407191a40401030301d100d01300c2850945d0000001111803c0e10860010018507001e202d0703400c0d281142e8410a25000c0c0186181460752034000c007900c05d03121401340003080342c090f40c0c0c81001450070414540701c1e2a41850031060119101c01004801410141045c00302030100c1c4200d81040d07041030704180f0442159013200002413440c07040d0000108107030b0000c100000d407001d4035806451501844d0001200f15510309040000300d03028242c40c01d078440d0192003800041004000a0243c1c0311084020003c5040c044e01d0384901f032402c82e40b00448504000611070300700716501001042c9500030250038040d0b03120950004019000c030045d41c080040e4404809080700d0001c20045000a0b04000004070f28114620300811030012030248500803400d0031800941d00b0700d1440b0b10b010441c410307900c803 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 849426825 1250 849425575 849425593
    0x606091f09060f0c061e021b070e15121005040809011706310e0309130b10080402040212010311011b0512132c010e100506250507030c1502 61
    0x5400101090a0606d802d40c0c1400c0e0030856202c482d20081c141403001d80d01c00d03080503014000301c40c64800b00e0740107007000180d41004e1250102e00c405241c0500d280c201e0384803080c0100074034918503024400b01d0b1040742030300380418081030008000c000d082c0b680d802e90b6003105001d41060200e50780c00d8203030340441e0094188413194500194106020f00c07000da004498802161051b80110103071103000e59050034640000501d8080c0d450950004030a20703103113210901415000380300144140103880180c000f40701500c00040c00710365aa0f41150f07840702d201d0903103000c65616400c000e0002840c502d00107020640c2d030021a0900290044072072000b550003401441c001002e10001c483c0341e000044100b25000102e40003050b2501c002035040c5045010a211006c1c01842ca403c545100300c0c1071713026070383c903240c2c20060107404600348401c0402d9510035114141e41c2c901c403158013180e2180d9000c040c40240180d5088600300600403030040101d034051440120455140c6da00b0301400f41c08190104003580c480190 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 849428075 1250 849426825 849426833
    0xf040209070e030303180d0804051506010c02180910020f030103260403030315050d150c0e10030e010b09070f0c050102210403090b041d0606091f09060f0c 68
    0x105501c0603252910741c0d254980840800c2c619042a5a090510921820300074040d8a0801404e004038140d4a049802410151a001d480741c80c5440079005034102c4c00c000840c9070f4002d120484110383e014190030441e04943d1400754003141e09031400b0780c0c1801414511201c682c5070f8001d55841c850b0100c00c030f502d16483c65485110000c00a940b0450100c03100c0e9140c402c210a03079003c0d0000358029180410304200080420011191607007256108121600e220b4010450b48503102d1760004000030b0028007030240b00f00030b03500d62025602c90f82d40028261070000c003056264200d07410300301e182c50013406803d5800040052041c411607001001441104c0c075014011301c180241c0d0307a0703103004000062810600b00034800072f641c804002120740a45500c20312081590040d0000020050002c86900305418030b90500f0b21001c0003000a1611300c20303040410440c0c0d44070030840340c0e0094010891150300c88101c01c150314a500c074160750400b003059080000350b082d004245010321501340c2da0301d030820019540e82e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 849429325 1250 849428075 849428089
    0x206010b040b091503042102071d071818050609041a070c052d011401050103020c1501300b1909060606021e0708060c0f12040309150201050f0402 64
    0x22140d0005040d24a41c0340204c508004600a034040d03116095155a800c0e443c4100c061101e0081086600c101804c0040b003200020310301c096401e0041d400140c0d207624000700d50121196500b00c900c1040410002160200700c3e65511050200f59418402d582da10001c01c9510802114098848a101c0e400205900c080f00042d940c40500ca0810985280031a2100e518040c0100490134810010305c011808000d120b9502e030045400c1c0c1c0c0c0090201080c90060004419018801d190501d500800d0210b04a0b4090008203803031650000e0071492581d40d9103690b402c04050245c03844040200754450070070b2364125103000851540100704a04e0588441806210381060f00d00205080c0b9503d1100b0400103080380a14001801c0036030007081003d00b181080003101c04480c8111200b5401004104424071010414540c011140002c0c03507180c0307020f003200b10720a201e5200d4210714100d151007080b00b010f403c0340c0c210040e901403001c90f00b02552000e030164200c1d80d0070703103036100081d11080002c0d0043c03030144 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 849430575 1250 849429325 849429337
    0x3090a06050903071a0106030b1c11013c1b020108070e04050f010314150411060c1c030f050603031b031b0a020906030a08030408180d080703020d0206010b040b 70
    0x122850304000d41c0fa0a08030103403240170456445461070041003001d6040c0108a1030a000710307060b10344c1c05110710400101d81d0103240c0060243d5138941c60034059a008403000400b00c080d102d00f815901c101c001c5400054a407428981080d081c807407810402286c4603900e40e0b000d102c850000c80300703059203e400540704208024086c800700101001c2600864582d80148c41c0078241c4103500c81990350552505c00041480440e00104c140d10101040c5d0044c1d00b680e840a40040d0031040300c02242c5c12960100d800c40c41020b1603008548260b22418021380240d00c540403880105580c00c01018200c3c0b4000c506440c0165056641640117200712301010010500c0c0310b081c5155002124500352003100301452800c6080700789411034102140b52429410156411035004004a0103005600302603503d540407404094000781c0301000204809100d142c1c00c640081140c0c0006061190851943ca070510390703075005202c2240180150b00b00c208546000280c00c0341610429032a0354203141c01c1c609100744c01c1d0001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 849431825 1250 849430575 849430591
    0x7030f020d020a050901020c151803030705031612050f0a110c0406080706031d071707030204140a1505330d0603141c032a0906031103090a0605 63
    0x20002080d4400d80d42c802480b00d00c03040e4031883c0d12042c1100029081001c1580b409024281c0d0354240e030b4450107490300310313400c4c1549c91a40440303140b030340c501080c0746000d1204001c04c9484006240c80c241c24101c4500e520040c424404102c0007107140400311010b004902480d211aa414044034180030700035030020500026a1301220500c0e01d004000505441030f035842580c0e60381054505100099250050300c0d0b00200c0b0440d4800e14140c02200d0a42d10041c45c416140300b00c881c42c540984003e0140f00f14801150003d005000c00c181c4030f070280640c00d009485642070140350505541c4c400120262180071a00020141c001402894045e407400d1404036142c2d0000c441860004403a00b00d0f03100141c10018214000003414604501d4400c1c24100341d41100360300c5601038800d040300305a4201404000403d24030300407800c0401405060701000b814507600040010044400000e40d0b130090b840c0049803915942400000b4541e100c0b03200c5884160748a1046811030803505010480942116400c5a84 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 849433075 1250 849431825 849431827
    0x2205150601020a06061701060f050607060c1403010608010509092406030109081b0f070b03071d10030c1215030210110604050c010806180a05040602041710061d07030f02 74
    0x20359032104c003200c1550700302000000c3d04107005080d8100904c1010054080c50f050700d00305038107040c0000c1e16070060707c400800e55604c1d20f5012185511418050300c80c4800c2002c15a1203586032600038001400074050b150041c00684001407035040005680318200c0d0b481e4210003240c0c50703032003251011164001c080513055929903034060009800c41005003410b55100c20045a5982003419450400215542030072956201e050280040b40901c0c0071a50401d0306170820742202083e128080d0000040506640e9014008403490712955805401c5407100c484950340314198008641c6240e02140c04842040c02030410300c440034001800c060303a6951000d640ca042032129001540851440c0c007030211402c4600c1d4009a84d4071030556000000c0c5600544111408800388034040c1c2002c102d118000c4c10f0305c00884d20b450201d0103001041c0d04690181a020220002100c201c90200741d9582c0c2003144204014070b42040043c4100e0103c400340800c0c083c2c007000089030380750f0030740850203040d405101c01c3c16254 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 849434325 1250 849433075 849433093
    0x5040809030a0c15030c0215070e0d0605041703010b0f0f0405120f011b0c11040b0411090a080613021905030304030c03050f010b1507030903080d05220515060102 71
    0x240070021240d6892083c800c2c12540b03070822071051001c0f10001c02c048141030801c4815503d03035801251580354140c6c0c0b10480420750f62840c1c42101c004a2046c0f003190401c9000c100c24061150580003244141e01038040d8200404602d0080c140c1ea200900c18000d90007010300410501480410081000c03040d00c0c1460341c240b9032520002030b680202480d030035009034008a0009101c50081c01030f007400c1d80c1003c401011602500c14050007036001107000400c441590024001c01d03070b4036903115070b00e50b99015100700800c200700d02c14102658013000c2014071807800e17004001240400000c26910520f02d2002604141280d9030070b01074a180c441e80a00e070740000d5100081080d40342080504011400381000010492560402c2420144107440d03084070740c1d04103460346030706441c1d12041c4505e6070110300c941d56035540141021601d1529a400040204100140d540302c4180b8540015004080d4003000f441c01840d503c801c0b0001c00350001c0300070542c0c1c10410660b0301c1c2d82048030801ea40050103005036403c2d88 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 849435575 1250 849434325 849434329
    0xc0206090f280c17120406020c010f0c0b01060306050f0901030c3803040b070c0f0b0a0b0409060e070f1d04110306160233060a0f0f05010320030a05040809 68
    0x62440d00101d44030706100b402c540e06004108410580035121041c1c1034036107402e047d4000d44894400c24880e05010200d0350b01140d0b580704809001c0d080350071288011503940c40e8100100a411030b03109051003220683e480410b030b8507044907000d048030340c8031046001d410301d4880550070340d00003100400b407c482044185401d06d070100d01025640c1083c60002566490a0b00d0007404a0b60090300c50005c00c415003d6140c0061081a24032006a4201000034410b07a00d0609846c040c1c000200c40c55006400d003210f02c0204489501b0041550703841d2029200324984030000394031503000b01e2080b074421506603510b520101114500c031a401c01e0164032208400e40c00032000c07038640349007514021a06200900c00e03442c003942c148001c0980800c0561700e44410040381c0075202d002030b092148402d00c12800c1011a203d0b40d54218a0380c0188580c1c803402c0804c03070340c40c2d210b880702540c2c1b4402c2c1b44c08a420551442c0d25041800180c006114110411600395201d085200008100c01041155100f2040205070f91503 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 849436825 1250 849435575 849435593
    0x90f1803020a020a0e040b0613200408150c1b0c04060605070b07020c010c02041a0a0e09070e06150c0c15040503010e0616180909060c0206090f28 64
    0x125000350020680312545105021036402c5a41c07040f4001082c450038400003803030007021140c00203001c99880e84600c0000c048200100340600450b200f4048101c1c44003074203803a52000d04201d0360840240d8010614100e451420003004036a4940807400c20030100700f41052000c2c3e021008101441100c3d800d400c0000444e04480064000740c001c00d40c082100020459204d68003544030225101506608400c40c002a11000804100030720864850400c07000c001560003030602002d00040c40c100800781c0d00c140500035000e00740c4003c1542d00613072034041018240a0b94207406100080d00f0002c0c0707032071140c003000101d800c02003040c01180a1040420765541d40e100e403810074000070403540da41d903618100803d421101211032007a6190000d40c1040025500381190392004506814000f000c5260510150201c1010380c02c1203503920b00d820485018400590b0240c541d411254086808035110111240d80d10b200c2402011502c0d031107203240e9200d046004000c144942c040e5440c0080300c034459035072f010103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 849438075 1250 849436825 849436871
    0x8160c12031b0f1b050a050118020306090607021002071103060c0405120c0d110d0501051306060618140109030f050307050d0c0b01050f0f030d170c04060504090f 71
    0x40e848012000030b034a0011903050035141c050a002c0c00340310041c00c01402c90b0707000800001c581c0002148030010301400303001409480d40d10800130019100c0300103c0a91020312800b00764001c1c414400000c0384070500140c1c5500801454000344042214604804040d40c8002011902e80317200f000c410005403010442680580013000d110b076110390a042c2032001850551500da20300d0740c04486c0c000116100e01080703000068008a000f01a00d100d400450701e06150054014842d40c80d1070700700801c842060524150103441044180001350340c03448210350303509015015071240d55039094200607002c0c01142c01403c012060401c100000d40e251580921500104e1080d541a000064441d04005050200380c40c0380c945030034040e40680464560542d450b07014028640204099545281e481d5101d8000c0d604002c1d0040c1155180301500e1401490101030f69290680740d100c2d00c011031440a1074100b81d070150381c501d07640c04d0305003440c01c2d1144000e011390000950349a80e5a1000280c0c0c2c0803d042c00400d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 849439325 1250 849438075 849438077
    0x11e0b04270c0f1103041811070b010b0c0d0509060904240603020304050d0305100b070204141807060f0210150e0103140d020106030305120432061608160c12 69
    0x10501ea061002d1310100d60a0740c00c00c51500108020300c80012040702d031490700c0c07104440024024510300b0080c61345104900001e0079001c510000081c0044101d0001c0402940c0c2c00181c80328029480001c0d6824008d84d00348913030150050180030f500f07003031540c002ca01c14440c050220f050302e45211401580c81d10541c000d480041c3d000401c01c400c8c02403c03c82044c04d240c0e140380c00c0185107400d00b004c0c00e0001450051f450094400140181990344030f8000c142e400ad81d10700309884506110903040c40d6035034000200450380c01b0341c2d80002181f138042c0f00085038040e42500940b01c1c100c001c101600003004040c6c0c4942c100164650041906800c10b083c85020750700c00d0f014034030419107111b8020f24080b0295051411603040c2401400000d0b4064103441099180c046840c03d1515146011401041d40c4845c40211030b0003022001c0035417141040c0041d65034001d90907104107460780550f80501440800d01c0802080c415004125190005920342e460240c161515911900b1243c4e202d00082076500340300341c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 849440575 1250 849439325 849439337
    0x60203010b071b08071206022206120902090c131e0503150103210e030d0e0f0a0518071e0c02120319080c040308040b03011e0b04270c 59
    0x100a030380f10841c06000c4502824401903032501403502c0c1d90303030500e00414102c1d0300414110380400544c5e40607600c01a0140e41a0b41000c480403100d450100107a1140000090b02180c0004000c07503180b1074016021740180c204441966842d000186ca030384038000415100149100c00540340d01380741982d010310390450100ea4a194900b000b01403030601058480c43d03802d06182c00402c00660641e0000440100522002c50820b030302c688240c030300b02d005030050758040c002e000354480340550065000100010444040f0709100007181842803100e80b6005564212009000050492001c2d402c0b00e6801500c0340761910f40404d022407012102d10a0740418030110350440c544004501d40007000481010b00d250085041c0184d0071584084403200c1d0307a526061001e214081040b882841040b45e01454025a00075030355a507a1040c2c000720b0b442442200305516180d0041c0c110342c07034007442041c1280c100080d40d81c00d15060400b40964400700c5d04c0c0c10360b1034030444410781c9841e62460060f01000300d0192159 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 849441825 1250 849440575 849440587
    0x703050603072313140f07210608060906180a05070b0f1e04030b01060c0b1b041a030a050106030b060f1c051806070e0a0e0a060e0c18030c060a030b040603060203010b 73
    0xe480f0340340307010b04075140f01b0802a0402450b036601043d09244655048405660303c45080c8105000346141d03000f00185000d0032081120355030000a545000304a400441c03c1d200c920f48041d1070b101d000c004c80c018a640c0042100304000e00d014005230080d256600102854010700e01d0001c03000d051820851180c0f004040307806c00c2400035890101d4010180c908203402c10021668402084a42c01018280102c003820b142c0301c2d103442080140d03406031011100480244c0000344615000e608103d6004010b82d041400120350144a80641002ea05016243c24189100364280062035000114030000c0404d5412680034008100d02456020f0030314200c0030090303005900702980c00e120f03009100b0020300216001d0690310313455602c100021649151596402c540b40e00d0054009072040d80c0c0300704440c101d44014450400740c0781c0d00610f92076544400003490035052001389615a8440440a5840f0b0b100b0300089034010300a41001c8440d220042c00011004d44036603e2030120b03042070b040005061000314030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 849443075 1250 849441825 849441851
    0x4061203030c02030f040905090a021518150a1d0415080d0306180c02191109070903110915191d010e0402041d01090b0a050703050603072313 62
    0xb045088a200d1001d9443c2410200841e10b86220f28420800c406e0340d00d03000140004414040003100d0b9070f0081040014a4000200804039040440840030301c0c0040c0354000362074038003c0009034141d00119252070502c0700103039080d207030390849003500c030b900c89003103403c5580c5a0b9030391090780070005100e02d0340c1040c2810140c0c202d00c0c2c0307508840c148082c580751036014818a0b4070801440d4044010000c08a00348803401030403411f0001c101e1200500c51407840141c001c00903040d00b0760310048015a5070040a81d14010300f103400301c1d594400900352241c2c684070301c030181c200f035005103501803000d02c550103a4139000e44c040b40d044800d0541001d0500744214060120f40c00f1482440440750702034118249650400c488000d140d000608005c2c2319650310b410700380d0600d800c165080c809540d6030000f00120205403c01d00c100803c21a100001980f0306800202403900901c65540505800f800400103603041403180c000002c1c507440a46502044603800094981d100703c49000c46180318a0f0215007180c44240e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 849444325 1250 849443075 849443081
    0x30309030318050703021201060314070608071407030810260606032b260a0b040c0219050f030a0519051905030c0702100c03020606090118050a06050406120303 70
    0x10307181e164010b41464002040e000501c0506a0f601101d10076409408103070050700414072640000c0418200000c0744500d07020200310481140d10f640c840c442107a4841740111020724141c2000b01c00e0440c10310901c070100e03201e00c1c1e00e0303a400600c0000315548503441e00144210510800700340398031584104c001106210040c007450b5048082640201660700c3e5260303043d40360300c1092020042041c0019545c138442482060400c04c80005404081c2181d082c075860081448412a0f0a150142c14070041e01240e080a20030600c2d00c04040d8040d01e000d000708900e01140c04181c4000b902c1c40e228142d40301e40380d40b074240002c001c0b0710380d507880340c9640d02c3e000700c900300408004e0000842480014001c0a0700320814900c106020401480c22a66982e2401a8a5450300540700060740044150709440803040c2c0100c6c0c180031082c06034088442c1070741d51000700610070714240920121030b02c1418111881c0007541c1c04c0300e60000d00402012a010341c40c0c1e0007103400c41e07070350754041c1c00500981c1076100b00b4103070188 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 849445575 1250 849444325 849444341
    0x12060c050d0504260310180912080a110f160609080c0a05071e0501080702070801061202040b04200d0608010912080109060f0b09121f0c0203040311010804021c0303090303 75
    0x1c0419003540740100711b0440c078811038412240c80b00c03e80402048200c0c03040d0b1000391401d62003594510710701e50032400101800740848030a02d40d41d15000c92070024449806c02d03280c1240051451170b01e0024810340b14409807070341e005c04503078983c0c032501d04000080030040a081d180c68100010301c0e40314182e0811501c1c244103a40006a1300c401c4510303280c108500401010162442801c02d04042c0e15402422498007202c0e034040c103142d502e4120301040a03001da2540281c460300071036091103240c4100003040101d403400d02040c4208942c1905200d01117140340042c00b0b061043c014000380055071380851600f9203c080e4000c4648608521a5822071604021450f02514011034200013160070201f01e030440010f075005030a9900c101080311416540e50184c5081c40010010a5807000744040403070710001245082d15107509814101125038140c4000269411030350004001098000b2080c019202c405015000741e030003454982e0b941300150710700003d6015492081e81c000461981c20300740241120215 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 849446825 1250 849445575 849445643
    0xf060803032a0313021201020c03120a0c0c11010c06051501030513050c0f0a0308130503190203060a1512141005010b070b09192a12060c050d0504 64
    0x1c0c00d41c521440512400e072940560404d05840f2500464000196102d4520a03480440e44c000110b0005200000c0041c00003590071241209640d211040143e050b100a6071050300040d0607040c3c0540030a5400380340c54040d4006041c030360b1420f000342e00c0300001c1d610201e84549030f006111140c09c0342540d00d031290300ea0000e40c0540c6903150032071607a681900c0d507219546040c440c038400300104855580710a13074600195403010903d0342d540e403401c201d05c4440c0702c1c03485014800d0284008050000b9070100280c0402a401009091140d0354060310700010301e1050403560f01c988200c08040b480141c0b40104a0300940a90213602c42042c0f680717080361503c84241181c0840c3d41c1000c0040003c4200401a0350a907a40103204006999441501c02e00d4403008550301340d48138004800d0841486800000b00c0c64100845078503802e12810751a6942c40c07801ca0348200c0ca455050b82c4296000f1030801d9101c0140b003541440c0a620700b848510310001690303025902501c8020491f10001c015144000082c000c140749 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 849448075 1250 849446825 849446881
    0x1080d03060806010611010f0c020c0307050a08100e100501030507030b06190b07110927031306120e0d0e1e03030a0302070501150603091704031205070201030f06080303 74
    0xe04950b941c0b01d0718103104617018000074400080c0089029001030f644a01e01c0b20007000401243c0000030343e10695106100d000303005d00710002c2078034202303544014107a560100081c0f0000519492240043c030215250708184e029500203841c3e40402c0b8040e01c1e0080d07009400034450309080d42429800960042c0030300b4403410105021160b100c7c0795524013402c031898907132500c1d00d0f004141440c003442c1c940c9a030220f80c000b02010400c001d203030290403001400301040710007040070b4004001641c0d0b0780c81113241c2894013115100301081420300c5400f81600c4d01c1203001c000721b050003410201503c0c280d4103641582c042a945649459a0304001e1558040060039030140c0c0f022403c201c0100fa268880e0000560030141c0000d070720700c1400000d4010010401a0361101c034840b40d50b50300000c2c001c10403d03c04650010480e0189401c80806805440549400018803031880e411000c094902d0740c0100e504905040e10f60740e0299610089228081c02440f55502540d030384e150100c5602d0b84242d034400c7c0c0c3d80511f01 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 849449325 1250 849448075 849448079
    0x8101d0109020306061204060f0e0a020312090a03060f021908040f020411040b22060f02100f0f02032e03031e030905060c042408072706020601080d0306 67
    0x8100041504580a5450042e5207481c0c9102043d21845540d605c208810345030740501c404c000590303100c4540d0b80b845010810620f030400d80113984480380302e90040c1d89903000d485c4404800c0001030090066203001400c0c000181d540f0340c0c49505880b052121005070356404039251101d40b0300024120788406080c0341030856840d1964415065140100c40030b400b55907a2221560000c18040450700034041e0b12809907145c440c565120384c06d0340d0003c02c1681d0700c1d0700205c40002d202c030f005030310102e81354070213030040d0a07805039034600301000f400c0b821001102591103da0314000f07116103200860244031001d825800b40b503800941c0c058400310f00307d09111681048001080800e071f1042c2e420014070407444a500d2030703074984e1104502424030300703001400c5405440244030350355060000403c100c6040c0d001c400d0003e400b2403480010102d01c01d0718040410404800030b041a4800c40c0d860400c41c400e881d40b59414640250010300f00f404540000b005a80810014840c0c100f042260034504030407440c041c040d0034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 849450575 1250 849449325 849449369
    0xf0201020d0c1e020103020d020c1b1005033103053114030f060f01090e0d050f0702180a0903021b101112030a02030f130309140f100810 60
    0x580190701c581d08440c0100107050131603119804a0356452041c90080d0b458403006d40c03065885030030210940c0100d10f841c0a4041039410004000040c05101e602c98a042d07a8450304e0882003100403044808040703545a595004180340703c0d55440c00c01f40242c1e605600c54045a00c081e1601600052800d006041058031110701040b0045180945d0081159908164141c4000c6481c110107400000d01c0790040c8010404000c94203a4002c0c12100d400c1000c0c001c5d480c483c5450380d181c5808055000c00600100b118450b0300c81d54400401e072552015081c4110441801031444545034281c074071441c92526020b195051541c1080264005034945040b1503511400e400001c040c44204a8000c00f84540280e005030304040031302c15480040d1400d0100350703a81c600b02260300000e50007100c00c10440c00002001c03c0ba18400c9000001c215a41074440f800c4150400b42c5802e200c82505140e160b010408108001803030315111007001c0400765a0301e4072141c9090002a003810380c0b445130400110a0308880e00a60b643c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 849451825 1250 849450575 849450593
    0x81f1e06060809062206020d1d15070801030b040809031213050102160509100b0307020106090f0203060a1703040b1b0c0303030709030b0604060306090f231e15040f0201020d0c 77
    0x440200400c0c3d400780c190b8901b42c1c02a0080e04101c514031454000510940d180e035510804041e414001994480781d99882d40c80364121003600c0103070002d14a0001400020b62180420390407600402805041c440c410000a28012444004403150200031031000d0f00c00d100f514801000d04400d0003d40030b18802240ca070f40146e54107102c1c0a00c070b03001840c042480b14103071010080180101d80881ca5686c50607240c060b0217003006120b1b612095180041007040c0000074400c0c1c80c002c45006000e144a14507008211085030140000d08850303000030007000808040480042c00000004241c00300308400f59074100b03080048500e03610340603410800c100001550b02940310401e0760b50120410865032900750102d401042c6540009001c0d500d410002003c0c05550741503141c0c070740d1040040741d401b940c48130111801315029641291142d4444034030001030303900711505401c030140880c2c212081450740d022030040200003510162201d1007607041c0340c0d0035541d050001200e81b02c244c0c1040d1703021112540e60103c60b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 849453075 1250 849451825 849451861
    0x90a06060522080d111005070e040b1203040f0512030301050907120618020c010c26040f0614220809040c2c09010f081f1e0606080906 59
    0x1140b812880b1030600e22000301801c2018100e0501210080701400e0005000d0715040300054880b8844c410350b50b05024a40d000d000d20034042d56031120f500c07c03020000c0c000070b40302c0c00352001ea1000207041d41c0341d0078038410000380c0000c0c104403203200b22403464041030002055403840c00c845035810800043c4216201c4014a580080d03052074070a41610b105003200006003c1078100c852040ea80d0b03507a0300300805864000d880c0100005008210901c0d000800b502c1c00b10501920700c44080301c4451805034089444a1107038014020340300c1ea422059190703540e0044440143c1042c4110144800b0321051180c0e0a40f01c2c0051056512100420000e507199800e0a010b8502c03401e220741d45490303400e4401c0d07100b140031060300c1c64400260600c40740981d414442c00301071001300340e005107061000010807203034180000084034080ea01409c10184860128500100c06500e440c0f809038031107911640c001150040541d104009a0000580505143d001041510050003000043e40690140301348102400c203154030b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 849454325 1250 849453075 849453097
    0x180103061703270d030807020f070e06130b03070f03170313121b050304080f0a0f03050903031b010912030207050d031a06030a0e06010b0a21090501020c0c090a060605 73
    0x100c4200e0320f666411007480c00844640c2294403c2903100c201500703c00380d64002e103003d4017940c0e043c44441c24a599035920501c20f0500c4100070001007092800c00d20181011540c03015800b0641400020100e0314241c0107034001d6601d011008020401e00003e1308101c040c14400c1d0f100c2616509210001d8806014140c4010b44866103420010044034000e4850211412084100b041c45810703604146840e80c105104400c2e690041c110401d003d640d0201e025038000e6403020984003540480e460490782c542050851581500c4104100d0300c9040e030f40404403e01030384803400842d80183c9441c101c03c42a45e80f4640c4020b06006002c10000074801140b00c40d041c5000c3d140008104101005031580050908819900900b0001c240a42200745030000510044c64508030f0b030071a41d898046c4212440b5002c0386000240140342c0d000382c005444078003c2c11803051030202062000701c03138440b142281d000e00c10100c1680c0c8001d01d0032000c0c0c00d26015056100c80b4401c0200300252070301c80050120b104240a0034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 849455575 1250 849454325 849454357
    0x3090604080a3018150209010e12010c0f030b010f030f06270b03120706090809090a0b040c02071203030b120a03111002130326180103061703 62
    0x2004051040c400b01e446003a452004031180340200100400d01c038040d00e011005a4104185014031550310132000029a61140300c90415420b154414802908a1168141088038a0428a500c0c1e5100a44520f030204d828000084c8500380c000050091422075100f1404e0508081074680e250b0f0708658030018150850134003140080f02050050000c0c0440d42010850400c03e2800c50003c2403529a18255020a05820880fa541900030141c0d55510391f0704805d00050200030003800207000f500b100302c2d040c3c4030304151402c046240c4001000310f1030071205a040a5036601c080c1165151501030688005501d001034030b4001d0502e508129031001c070420180c10306894a099070403d0b100d140d0a5110016940183c480d449807500d0000c0c41031212680d0f4017103a101d60082c0c0c051050345032003114000d081d49009043c0d581d146603203403811000150740c0070305140100502c0c0260404200c00410551012aa01f000e102e400c4400240441d803254012a0001075001100e041d156000800c03119458441280c007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 849456825 1250 849455575 849455587
    0x81507050a180b091c021c050c030a06020c0c0907020d031a030a0c050a06110309011209021201240e01090b0a0f120201030f050f060103020f09042f0309060408 70
    0x80e0781c01c12404080d01142c80d252400000c40c00401406000d45442c04ca0700881c0b9030b98021400c50100c40e0441d400380d400303e07003208804070441380441c464021902c01c10540e82c0c00319007103000a050004801c82958a00d07000905410184024403800c0040103084415000e941007403940250b41c3c15030400c0f10f90526a07540300000d4485043d0214420803540201101c0742c6482c50705d00717941404214403071a8000c0e04c41d0341e0045206806141810074450341e2000440c1032010007001150500f111032011118950303110950b80c09030f285c1110078560710001d840041602035900340d4500403c403101a0f04480c03c2c001c00303000e11249003882c881c2411200d045c2e0020400c80c91042c0015090749440e0710148400e07001044c00a64500448501011070f4004d890070041041c03641c9044055460445098a1503010000003070015800380e0b010300b2511940d00c403186c0c00c201c0c8410110b000c4030303502c80c800107141c00b40100443c0c440c01c80b4016004a03031841048a400c505084118950744c88001d80000d0440e003000c41c135 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 849458075 1250 849456825 849456827
    0x51b0c121305150a0206011205030f071e060c080117190816120e0409021c06061a04080105070201090f0803060d170a030f02270a1a13081507050a 64
    0xc1c10000e054028441078241041c040707800e1890703020310110f0025015441c000900d208500a07580400790b00080914070b0460851542035265101d10b1003181e4003010587c1020b00070500c0c402407000203208a80000b0000351900002e445260140c0c40828460700350400303003408081c00710715608161362842590a0006103450501110700448007800b158020055507041400070340b41c83c2d944a6081a228050905800c00030b220035551501c10180d004010150380e0346100501e41c025261080c0191000100315881d110350021031400c0040305c1c80c0741c004c00b00302804207410a206180d04100030b400200300c80020b030f94490480c041c44404c0600b2068010000810503281c911508103a1a8003004100309000e240341420013039001038402c070340064a4400b4100703519170688219001800c581c814a058600120068213021070009201900a80f413420300241080f01c4500880e000b560243c074041d150f030341c5c000c4010318481043d80800c80e990301c5020300b0f032f12070342e682c80d441c80d04038245140840e51381c519020 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 849459325 1250 849458075 849458107
    0x52101140418050d0c12230901020f0f010f11090904080a0507120c1406010e131e030203250c09180b150103060f0f0b0901020a080d051b0c12 62
    0x1c000b41681c050740c0444019694407105c0c4910043c810480c00d50310b1908074900712049001a10207002800f000344c8640d2007103a100303002d4400c1180c1407045540100000c0e142c0c9081c2010079480010581d1180d401c111401d4890040c1c2d82d242c0040c0c8040e17070900440e200011640d0502800261424500040d00840b040c130440c112140c06400104030b9610000f0080000c5c9281e161260640324030000c500071040100000c80e00d241220030020001c089034075205401d0044c50041041102d0406c0701031408001070450442c001d440c0c0e4080d030055520743c509e03c6401c078103607042211b005000d040c90300071a600280b035000d940025200903075130004851009280004540b24820009004105c0d070200b04030811800c1e04151004800a0343c050107180c6e901c1088541d66a0580107400c81445c644400b404503180303000c041c00c49410144116081140706489080e1983c1c01011011070b4242c03600e0401003050105030383c05000507a008055407074000e540d04113035112080c9962030380c0820b0700044d0400940740129 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 849460431 1106 849459325 849459371
    0xc040f06020a03121e0501030b07091d0c1605030d200403020901050f0307180209100f021e280209060405130b1f060521011404 56
    0x60009019026118148258030f151750700e180c01055050051a0003035009442c1100306041040c0014800303600b9401103c4104007942e8070705540c08408044640c8910411045601c6a6242d03414000b2300510f10340c0541903110115281e1200000e0b40d02c40000324060480001c880c02c400000c03140640a14840a5444907800f00100303e00c3c105100c2ea2006480700406642d030342074503111034011004010304a6000c0f41e5002c00c02e806207080040d50030700140640d0070821101090365100035503458040040c00c010981428026100c10810000d4451403c1d080b40580701d460104184002c1804580c0c1c000da00c2401140042005400c0603c503940c0210240308034501c10340c0e100d03117a020400070b001e031113480540605001d40040043e8040c0c5c6001500060350344030ba844100d400c000802c045810b40e190b501e90141d100400039038070141d051480544c8182c0e0081013040041d0508101c040c00c0f9 = true := by decide +kernel

theorem cover : BRFrame.Cov 849280575 849460431 := by
  have h0 := BRFrame.cov_init 849280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 849280575 ≤ n) (h2 : n < 849460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
