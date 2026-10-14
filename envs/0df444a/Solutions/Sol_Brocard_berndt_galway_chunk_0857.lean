-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0857
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:12:08.658144+00:00
-- url     : https://prove2.me/submissions/1def94a1-75d7-483a-893e-a30dc1819ff2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 153956834 ≤ n < 154136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 153958084 1250 153956834 153956837
    0xc040f14011d0a0503070603060311010509010507120201060513020c0106050405162f030c010e03160f0203121c06080a0b04080f04081207230601141201060f1a0901 72
    0x180b501c0303241c902c105030358100c4401c0e0340e00005080d00040e854506001100040c01e26072000519a80346040440c5c140000515441c10014100400c842ca40c0e00001036810241e004a002491404440c00980c0101140c1e04050f0740001d944000582c41606034008080010400000b400b03c40d90310010b00081d140141c03441c50182083c0d0342c42c82c100500c1781c0d40306c0c21080c131012644003a085050400404003420000300c0011303074000260503221f0301d80c24052401c1e071004c0c140c011441d0480c500224031794242803900c0288000901900e2800b959402c00c445800c5901c1400025662075503e80da408071001005034202c40c041c203015001902c001c010440c070381c1d002d030052180380282c0d0301c0d6a501d0b40d65038809201d0010001082c0400300300c0520401622401c8421100000c0e51000075007440300300b4280c200610300782461417015550704070002040050442c0d03000e03e0300501030000d46000540400b01118040a958a0b0080000d8a01c1915160f01e0031034685180d880c92241c14048114000d10420b42102e0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 153959334 1250 153958084 153958097
    0x1502210103020919270302150609160201091b0f05010c05060c0f0409020f031b07170c01020c0303091501050607050304061b14010501170c090105060307020309090c040f1401 76
    0x108540c020b4142502006407010740000d8035012600c5d0b0807913082490070344251008040582008142e010404002920000d4410314080e28001000484821005020100d600d0104030002040c6000350000510568480c241c1c1c2e074160b0600720760783d004044c18070540003118950303a0005015400b4500115000d600b1001402c0271782c0e14403000c50303156840011007204000d010440000d440d4114806408008180328046070350341410640325503404001103a020500400b0092100003850040080784c400c403111902d183c0f200400581c540c0240108600d00c03a01c0c6c007000080020110300820707920780d40a40302a85000f075903281d0040c440c0c02c0c05115401401c9070300402041c13140350f01800e10548441090911491261030aa49000340e480b401c12841415a45410051000801c588141600000100000e00c111804c40d4000313414031a040c45400e0107000000081520107100b44115a03009001400510250900c50044001c42d40648a55482002c06100c00b040c213918800303580388501416911003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 153960584 1250 153959334 153959341
    0x1c050a0f1112070c1502040e0f07050a080903040504020d02030a050912040e090a170a0f0e0f0103020f09030307051506010903020a17010f2c01050402030a0f050a15022101030209 78
    0x556510000d0046002d02c0301c50390360f00c000580426040603440d00b0985c0056140c2d440c10344401440c60025142c90a0488040104901e00e580042500c6521485150080d03c83e01c131408002c1c1180b0440e044183c0050002a403c5818681500194003a00503080100240d5a8540c1d00e5501c8201c0280081d17441d54040000b0400014524000c90b00403840c0d809981c60504241d44202c0441c0407040804010840030450041064200e02264031825690402da822000b80c007000580c0c203241c040310f04c0d051503800f04008800c14809030503100d10740c00c0036080b40c3e178031142c5042a03039032014880b08401e0078010b114006505c6506c103d40c40300840742e003e0107002d9000c0c200b03101d0503d035624030443c420b181d6503200c0301080014110b010b10018424000c28892054480509440c8043e420210341062a0304040c140b2005031000541c402c4a181c0240e60405401c40c0d03450b0250803d00d2111020703102490690443d100b444c0d10750300420480d81404030781141215030710100c4030010024440030754070001c0d61001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 153961834 1250 153960584 153960607
    0x203070b250c0902030a0f051b0a1815090e0a1104030b0603010207021810061e080709090606030212060f010c030e010e0a030b01030303050c040b09151c050a0f11 71
    0x100c0074a184a50300c0101c2e0301c0c0d20341c80c082c42241c00031150081c1a6407141c2110484840620584d600031b00d8100b6081d291040d1807400f5003c600c280311000040140741c681105018402103801809400410039040b00d00300c245d40d0041141d05280111600c0401c0d940100b51140707168803554400a05164032141000d1464885414130080144001d4065400f0000800160396003504c1000d103c1220003824214149504c601e0051035403a00032070244030201c400c0d0901c80016041b00351000c0348038600380289503625801141c968003242d21280585041100201c0c1d80da406030042c09806089070101400c980c0c1b040200412031019049180c00f01e10700c02889800f0074030400034080e03480c01c10705003131a90120003030200b485c0c078400b544295401c44010300140708156040c014035810055850041d8202030410044449034803825a14900c120100304404942480c02419500c00c400c0341031800b07070161152044e0201030301045402904e05450415075440500320751240d02200c2041110b8541440c054003213 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 153963084 1250 153961834 153961897
    0xc0d05090409140a0302240402040b06120405030c120403080306010807030b0315010e0a200d09060e060601030c140a0e0a090216060c021504032105090a0203070b 71
    0x815001501c402d030010110344006840d01a0941000083c0764042e07250900074280410243d1640269480034807800f030021035802e0700f5802580452700054040c060340c0c00100c091140c440d906120400c07030710400040c41804130142284030300300707020b46032400c003903080d03008881c411400028407034901480415044c0d48101055940030685040000f03400f0610800a0710780490000f508404003e20001445421216005580c122000c94001e0042640503400310f02c4074030011060801c204000b01c1c191001c283c064003d1440707a50049400c010400c0882001a1551340c200c48190110381008005060b8900c50000d801c0482d40149030b1604200c0349031000c0b40c004114810007607201005020100300d00d0004e20041c19010500c019011a5000034601682550740c2e000c4041e00395000480304118040500b030316150302940c18681171800e003030004c412075489850500c010030024502410844025400a120304030140210225007e69907503252410051080c85140d41504a0054489413443c0b181c03030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 153964334 1250 153963084 153963097
    0xa1704151a1201020919030816083006010801030b180106050414010609090218060c1006060906021b100e152205010c05060c030a150801060801050702030c0d05 70
    0x3820008004000188280c00c100701504120b075400100c01c6140c1c82d010350b06c4184451100304140181c0c1c5151076010650180c4088001600f0040002c44108500c42088034240b40e00c5000f0341121000320b4034078010f100c5c4004043d14001244202003801c0390300484009040326408540e442080d5500c0d03d80c842080140c82c0e41c84019900c1e41000701c3e9a955500840f000c0c0300408810090760343c54124000c00810310b5611100a141c030410070407440c41600340280d081e0460650b002a0380d4805800d91524010144000b075a2961510303001241c1c660340045554100c60f0745500f02c80d544400401591101c00081c014640d10441c400c0c1290349060054903070841703480004008043c1c018a5a02e101c035203a00074424114098a01c6881000144000010802600d82882c182c00d2440c07040c1e8506d51b40b001d002d406040f84090100c0003070743c0c0d040340d50410315900c0b054020340c2003925a00e040b102c1c0640000d000d9001d041d42004006003041d4800400d40e01d400d580c880040c04c0c403c070250401d951a50100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 153965584 1250 153964334 153964361
    0x50c0f0307120b060108130b01030209060109032f040c0c0b04080c031903140903180f0409060504060608060402150c0705040c0f0305150f2e050a170415 67
    0xca0001d0081003036244040c0242c00f03003801519074601940010585a0028010452528504000070128485005240c152603043d03940e2035498443d440180c8050b03040d6480100f0101e1035101907144100c001c50340e28021400c10355200d042500403801c000540e00e0841e11400011100d01041c00452020161542c1042c0251681440e182da106245400c1d0b42c014041604191440c100409059905210300b524501c0b0005140080d41001d50301d15460740b00743c15800c00007034903041c2d4a45142e5107452032518030800051080000c0200da192100142100f19816180c0520f4044009440c0c8400b0484030711488d0f006181c034595030910786032000e0913000610658a24800c00d940070407140c42d141304002c0e14103640d482e504c1c23040400a00080a0700c8008102c0c80441038081040f442c0c913202c0c9120401584000c603460501103807040071491b50700c036480c40141a80040403405882f2190000300074100c1a00074ae8079940309184110305032401c003006031001082000d0300c074151101c2424039803004d1003c2c0340a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 153966834 1250 153965584 153965593
    0x1205281e08070b01080f070e060d030e0406090f11131a04030501051302031e100207110a24080403020a030e04090c0f0906061107050d05120c0d0318050c0f03 69
    0x95141c000c46608512421107a00303040c240103102c0e10034100b00d031204001183d002030046904143c280340310803501800342801303100c0c8000b410081600400242522401c040c00402c00941d60320041005800811f1003c00c400d890060002c2d41d290884044514200e400c901001450b86462004010b1240c0048203c0c0105030910001c80015400c1c0161401903110090303000c2424503038010107041160462070076840c0c2d560800c2c29102900003081c454103035299804016218480c905048010b8040ca01103294071070b4204402180403414400c4640c0300303c40035440d055020410110540d01c08900303071000740141c0d00c11801c0340b000900c02d030400400c11501400c0410001011f688020028905800c50f040c1000784241c140304003c028800d51000302001e01c0c04002140c40c000c08943c40b02e200e0b01901c0d00403514212840f081c4042081a80800b00c0d001510750f41c0c40d02c41031442900e0b214004001400a030800004088d041c461400d001400354100c005440c0d035802c000200441072515400c1755406002d03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 153968084 1250 153966834 153966893
    0xf0c05010c02010b010e040209010e12010609021b0c030609030306091306050403120b010309080403020904060b0607031d0a030201050909071110090209010e0c0d020906070c120528 79
    0x70701941d901014150000300b16070740220009402d50308411030581c01030344107000c03c280c1c40ea03121a50b441504020384141c0400b5600e01c2265016020540018010500000e040c1c0d0411156019150858100c04282c901000e00c0b00101504c07250240c5207034a96500500100d1303420f103032a050194000740d10b85120036201c0310030b54403107050f1241145c0a40204d00c00415480301036200b070199020580782440c2c01c00840301319030b4906005001d04d0101138000c04940e00081c003040310070340c002c0c01c403604003c0200791200c4c21481c0040c2807080d0450f1060000003024071403486410515080c605807075050315024100340040080c000c40ca00000c10309403c02015848024080c1c0040c40041c50303000781c00c100407804402d18014030036006070680c005040d0244034400c201c60000c0781c0c4252241c64004050260755000103c000900a00074103034050640750401a0001d942c656200f40d06108621400969004a41c0b140d0000340020084010340c0b0b0b00060b0f000d4036030016200a030500c41c1d0b00074101800e2610716 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 153969334 1250 153968084 153968093
    0x20a080c090a0f060f0e0a0518060d06110703180b0a1b150f0b030c01050304260a120f0e0304090b06070b0406020909010e06030304060e061c06050406120c05010f0c 72
    0x784564412808218217102200156a00455001c041482942e02c884031524081c00724024408080c0d036a41c0400445012a80c96170710f400c14013010941001040c4410300d030a40b002001507012074000c401061555201030340031110640100100c6002040b1076041000220003511000c1200c0c01d504000c0348040d0200f40024007074680780c101c652030b0308000181d10466402a10031241092041071299001c2030ba0210940e901400300c1e9032055100300c2c3c8a20507a0b9000c480c1c054840c0011001d02c8590f0040752003952507902520000600413880800d1200c01c4007071002078222441c3c0e400705034030b54104100074000c10460b6000312030704200141107145091540e07100e00401e00003d50301210516000110b00d8002c0c41c0c40c0400714050b022a04803580e0608000000940e20b00c02c2e481a10140000703080d03a100169108025a1046030070b40c0ea5034894205049480c0c5c001b0b00300c03400740318881d43c0340c02004104e510408160010595004d00c030714a00700d0402005580e5008407000340400c10003e03269540018 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 153970584 1250 153969334 153969359
    0x91504031115070519181403030c01050906070f0305060a050613080105040807060b03160317040308180a1d0a05090c0612060312090315070201020f071b09020a080c090a 74
    0x183c0160b0f40d415292010045904850415070f1901c10810142615001c406110601c13000f04a949820107610a00b10600119040d4020383c800444507500e481300b085001d88002c41c8092041c2c4040e07a440071401d425482c20340c05c03103d003925529000240c9490074003a6040410060014880d02c40400c900d41c0e927034142075825182d049074220f9844030003040410403c41c43e1701036002800000c5002c3d060f07101c60a14140121000c5200103403002c80710a402d03d4555803030b60102c6000e5a084a035055450b0145020000f69146c5201c0c01e80c081d50b0300c12000200110001203403040c000030241d14a40a80b034410b1514040c09020b40b440b00c55004100b001310040d91444000d1038030002c0e1420105052604070101070614030200d12a0140410400103100c059078045008540303025a460f0302285500c3c0c01e0b00490081c080c80c2d8083d441e0201c001900070520680d151715840011a1007480b90040c0c0c0c4404100d4141d00511400c44041600c1c900855007084588024042d024000b402a1006540d41c1c1c1000855 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 153971834 1250 153970584 153970591
    0x30c1803080909181216080d0b090907051e1203040e010612060b09060c150112052401030b090a0b01091409010c0e13021303060b09091504031115 64
    0x80a0002980282d909180c100144d00401004a00b10110032080000d41c03500032040b10b03030300e000c5000038540703042041840c0341d40007050700228440e441e0703600312030407800411020082c01c0c800e50310b00000403000b078000115141910001f40107800180040e40c5601281c03141c207042c80f41c3c841e440341c840c0b481c507a10070000b500080c4880e002100b841c2d4907003c4003520120800350090312540c1058000d00c81b0540300d0f4211080d003003040d11030075920400032603410b0510150300140c51a049001c030000030b00350f0680b1800ca00300f40c0038000340d07070035002105000890244a8510090340d0718081c0c00400100e8550034007107920040f0300c425507003c42219a10000f00003401d0b046410171316581c46200c9954400c5c2d2156541c0844003000801202c030221038058202a49441c40c0c9108003081d2941c4034442000390156460348003024149044d1039117920f499005402a0098240111050741c00607044120000c4c000c01e841d00300441e00003c0e52110348003182e265071881842446482200050041110fa01c00301d07030310 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 153973084 1250 153971834 153971843
    0x90f030303040624030b01030f140d030c03060806190b0310020a02031206060c0a11040f020d020c0105220303020a11030c0c09010801110d0b04060522050105060a0e01030c1803 77
    0xd9000790307881241c4c0f10480241d90740e040002082801d2001500b07403c91103040d40c0d000b04040c640d952481c40c18039002070303150b140000c040c010320322010001501078008140c01001038030306100c220703110b84986590705c42c116540c0301540c50150001100020303580c000104d14030040d040d10a00d011560080041c1c0e44600b01280040c0d000044d00203c40081145580d044901141c0082c9807030700c0d40c114143c1d03d0303401c008082d05034050681292025030f43c40d07012044080f0103040540d262668041460002c2d001410b440b80b095080c240081d1842e4030140548003482514548200d001c5450b40303044000303412001170402402006030000542d100700304041d04010b08407200030011a0b0702d4105015145806900102e103a07070401400b6681084800b06803020700c1c0700c41c54000f80f07071400880040c000d040c0c254046a00b101101c500d10b850603800050707181300c03100c461405105c2640d03520184000d6103d8000c134440040c0300c800032500c0c82d6220350081080789200e842c2c0b40110000341c1c40700b4186080300c8d500c02c40c0c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 153974334 1250 153973084 153973091
    0x1020f031005030c0409080a110f0703050a0b0709050a030f0204020d05090d0212090303040608090a02060304051501060f05091c06020406020a0201030e0307020f061309060605041d011a090f0303030406 88
    0x586000c10000d100c840c4151780034000b03910740b0b5950034201d02800c0210010f22221040000030390208000d00a000304001e002c8500440d03880c01d020ba203501103002d059404504401c0021402c0e40240010011108040c102c0000e031851512a03180d4010106e204990040d000c100b001002c441c503018060140641c100900031007008400064500304010180c5041440240048517060344c010040c0e1341210b0340c1e810061450b90320b609000e401d0580072107000354072203004014030061000018180c224010850380c0d42890347d80700d141c00d840c52103403000503000061007042501824104100c031002c20014000c00090903c0c0542e44090903600260051001a40901d055205541e41401340040e42010702015518100d49034002c500791150014010340501800036200340d900003050f850744000c100034042002441e8a17203000800684c0140b040d9440a038030050108040403056481c10f040b40c10902c1000750f08241c014000282e0303041170b6600f80c1c0c001001a0f119100d51000c1c002907200e14030035580007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 153975584 1250 153974334 153974339
    0xe07060e030c040606051611120105060901060e0907540b04030305070f0606080105010e0a2f070f06060302090c07051b04181a010b090f1201020f0310 66
    0x62600000c004030b00c0c8503500300b85003048542d402004641e520070640c0100c4a035242c46e0304000d110740d01402c49680c0c000184a144280407001075103d540242004c480561480e41d90b08001c2b42c0c0301c0d59100f004e59003d004a40440e12603070040e14860040344d0800c41441c0410801c2034980304140d26140741541c10808414070315040f55540084a090407201c6000003222820f104ad04040da020b1400b0040c188a00062104140a00050b070320700080d034441070501c0070a858902c03142c06801d080c86010042600080440c1041200e40240d81140da400e0000c11940d000e0310107860300d05503c002d1038002c003403010000e04001c01c4040407400030040c09800d0125025282d4410f00c29201001001444002010b0282000049010400305840b004056110310300201c3d600001d03000348011540401062004000d0504000420102c03c401540a82088409a0340d80000400d0380c0b00c0c40401c550700c1107401411100c20f14050344800c40a404001c001404c000d07800c40914643d501c1500c403241c0954942c0800c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 153976834 1250 153975584 153975589
    0x313020907171012020f0f060304062304030e01030c14040b0310080102040617040303020d1802040c03061d0a0603060c050705210720060a0e03070e0705040e0a0e07060e 74
    0xc007a00044500304030340c030440c540b000d44c0a00e043c285000070711610680044803130659801441e034400c150020b009654904107450013400801002e100b0882e01070701c008601040790483c0411900c070300d8160310f070080700100700c0300118010025104003200344445c100780d00050000c400c02901c040c0502c00303401c03036490a0010030b00b194482554040542e0342e004000601005500c22001e104410405001d40150b403202d150582c06801003240700c0900c0d61510b00310b8031030120480c842c0410540203540800c40311809032400ca050b910540600d01c2c14078500195124040c035028911a8000042c02c00015225103e07680d51066030484c440b000d0001720045204030500400f80003c1103000c80d11400400100410703d20b6202a0180d42c4001d020500d6850240e5250a000d200350000d07100d00520250317446414040242569691a01060107841742d0314010620b9170088092901502103a1035442c102864590304031103c80000f0944c25038144ca60b902050100e03000c01034480901201d85542e03401d542d90308103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 153978084 1250 153976834 153976877
    0x50106090510140303040b0f0f0c120316031109010c1104020a08040b1303080c0a020a1406010603060b0c03030408030910060602031b010c0806040c030b090f04021c080f0313020907 79
    0x3d580b00350820441085402c1c0150122550349065001c4d882c2c5842c10780c00d001c0d82c140034403a003000e0980607030301ea8203100b400d03004011407250303504e0104003c485152603c1141141e0440f84108441034042004400300c0d1b000d0f1030090502e5102c1d080d00e15101036008042400d0307820203001ca5011404100c00d100070000d5541c207403903001c00b00e103855200d0b140b840d407030007450b182c0d01401003441c055000414101803817003403050086240d00f20003e003242e08a40c000c540d82d070b8030007407003200c0c0001c0ca000d0700400d504c0300100842c1c8110414000542c00d649868070f030300a280c1c1c009446903419104180000040c503225004000c02403844c1d4010316241d0300000d1520f000000e2030b042500940c1d161544007450290400300030381d0081000d0700c0015158100150540007410400640c662003070505042045224070341b68414803883c403e486440040c090440000c003032420303000c0010304036001803005001c00007a0b07002039940481810700d102c9540c40260049034000d041540d02c0f000084c07100980703c2c00000c0ba00d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 153979334 1250 153978084 153978119
    0x150a03060c080105120c01081b0a080601080a230a061d06010f0806310e030c19080a08060406050d0302011a1009030303021b0601080a11010c031b050106090510 70
    0x240c04d170312603d10304540c0c1915209000b6072281881803480228100d102183c40c1450108090040e140c4d075130b40740c070ba00138015642c21201070340010400400160300110a0003688151264a072411206480216031034a1094000700158001c1d47c1e25400050342881075120641d000c0754007034000c111400d00130001030044000c1e10400c024445500c06114854641c40d0100c2034000d140401d10160204151041d40001f4001d282d1f800510b04003511014844004001070020503501c1c4125403500d5490340118000c1040d0b0790020300806014010f1700039450041580641c840ca00030000107089448000007082c080d0b5000e002c2d00181e5540f00300c09a81030342d10031001614101160036840c0c498549500420740445800021308054001c030b200400d2000c283e051030701c5403281c0401c0d1001d40d070711291040d41d1201c2d088010b880003003031f50302286800c1d4001c0c83e442c40c1098041e6210304c1a010106032202540c4410001107440759624003000852445501c1014041c101190184a10929010b0300d1407140c030145 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 153980584 1250 153979334 153979339
    0xf0f0b030412051c1b180e0f09070806010e010306180c060f030209090f16091202010f020f10051f0e060d05071a07030807020309031005150a03060c080105 68
    0x1001480301081a0400c2e010000da42860150381e0b410800b0910a03507081c00400d00d11202d130401e40b0503084042c9486040e006294996110000465034881d101489103040c03155042881e40140454900d03e143c60320282d1107043c1c0030403541c0d120b40da22030003072410909a00000e559201c02c80140204001801aa4110b400d2000d15000c4591541c0740c203940c0701081e208078800e02040600c4a079405009406a03104110f0042412000d072404507130501c803a400071135808a480a12184680400d4000c04081054400c04d03040c001024046600555040396003807151000d43c031601c000081c000e02c041014180b440680d00010403542060103100494036800340c8034403405001c3c44401d0010040409429921200c210f0345125220280c0c01e1a03418a07041d9008407020b0109040c030b00040851400041c00340c1d621a950b402c07115039882604030703100d014004000b6072540048648009016080d00800c5d00424180d540d001e0740082c4038000f40340d68210b60700c00c41d03003e0307107442d1003e039070603045260240100403d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 153981834 1250 153980584 153980587
    0xe01090305161502031c050a14040c15050c0703080d0603050d020a030f030608060c0d0209030f15061f1404080a030e090a0b010c0f03090b07060509070503030c072702040f0f0b 77
    0x2400011010201b0900d100d52000e69282e0006031604555040000403011901020166060900300200d00030094000c0080e907400c01c80180502e24030403022074803044003032006050890700355640c441280c0c0c8401100c0c610706840c0c010200101d44207010403e51840f0f182c00420001c0140d2070058000b00e80c1c1d0381c0d5901030500d0500300b0041c03400c1c00b2807070543c048241c0303414560310003010140c5002405007060343c03078062044040c0c108503d00c0010b6022030f212816203540e10720740e03101d03c100309031030800c400003660790005001420407041c001c014000060a40c2c410007428031303880c2c14520f40303031091488068000612241001100f400c4c851003207078210203140004d119403441000080d01710000070318018100001040c08906251064100d0340150800c040207035598440c130700741a0003600707090703542405600810360001601d10f80082281c00e000e9010003c0c19181b0710345010011801200f4120900004210300111a940224030040c0050b01e000c450520b412800d2078211a0040d07201d41000d001e0000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 153983084 1250 153981834 153981847
    0x10b0f0103060b18040204171e0c01050d0533090a021603050a0201020c070b04210203100b011404030c061121031315050a0e060c0a0e0109030516150203 67
    0xf02004544411141982c20a81c10003184007081c028481d40c4e100416503a001d022885007a000410603281e0710001444034596406403045060321404a00d0400740460800c1050050206090b08181d40c40405d00200900504212018900851380d00e000d500044a0003108030381c45140a88a0b1342c1c00c650038100846c00d01403504c0d4009041c03102001c000c1c0901c20040b442081d82e0307101750111350070b08000c1404c0c0d83d03032940c0e16540403002c7d13009401040c491405d2105a600026615503e0f10f00c0307260001c0050102415810440009040e000d00540c10800901d4140a00d80b160074000d1006600c01d81481c0801480c200c2c0003400a0500c002041d801d07002506e44418800034024603a00034680402d6450380ea8403200c2a0340d0300805010360082440500c0b20310195a000e1f141e20452152880101c28000207044a180c41d807110300440d41401c03108424042d1b04c26062285140d0342d000345040c18203900c4962262622443c100203411a03030560703040d1242c1030000f20018810440d04803d240000d504106 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 153984334 1250 153983084 153983099
    0x1020a120b1c240911010c030906080c09090130032c0306090c010e0303070f0f0c050312040311060c06040303050a0209040e0303040c0b07020a03030503150909010b0f010306 76
    0x2100c1401101c8903004020a008000e103d6548030018101c0c054a071080d2a0a28005404201000d03204100015440410b95004070b8005a070300742c0c541d90303c07441981040f0046d0b56802000e000d01d03040040178401880c09884812629029000d450a042c00341101241d502072800c065820103845140000c0b61480040e40040081907075044561000c6800c0241c0140e2900180c450810b013030b418442c21003840070140003c10700032030480082c1c1c2c841c046040003806040d542e02c1980c1005001c40c490b0342881010070180b84003821640d2086a48a0346035030341c1c40000c2d2410034a076035207481d003e00004d0100104000007001035444103007950541d0420f0700d4600d9590300c5a00040018060544890006051303000039412110070345402002000303250000500143d6940084904503503100007810080380103040c0302c05845039183d00510007803034181940da049a0f140c0018060307556059508269841035036800d01001d210348200c1c2c0c00058809001c004001340c00c42c5d0150001d042c0b624110003480b0300c4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 153985584 1250 153984334 153984349
    0xf1005030106030507230910050c0307020607050304030f0804090f0c142101090e1005010503120a051c020d0b04110d0e030c0d0306290a08180a0501020a120b 69
    0x102c40c14140000c43d5a01c0d0081510704110003241b20080100280c00c584400c1280409410106420703141d4510581d80f50740251064030501800c184190f0007800380c1380040c07501200400741140b02e4815a410107940c1d07502d4800e14101800304951541b80401c080c08500840c0c0300302c1c82450b84007002800b0b03010020f000a04602030131190085411000614420115101c10000c1e424030080489150550b03510646840100000f18500426000d070f0004403c5000040c00703924107a03140140a002c1203440a0310090b4550b01401841003841418041c0302c40e15440d1040c0c6010701c022076200543c2e1080e000801c03804a402c0d142505125034130308600d04040000310ba0a03211014000d5000092064522007020705e14000c03041c840446201d60318106e411141e00da00300d101204d10261a18a17140c00b44c410001c070304a11080c0c0807401c24000c1c4442c80c2403078400d2426070f822003501d500054002880c0407102d41865201030041d05c443c1e4000035a10380b00c0c1d03885180411801da10010070007800d0030b603138005940c2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 153986834 1250 153985584 153985589
    0x10b090406091109010b19030e1905120307020a060b010201020313060b0307080a0606030b0c2b0609020706060311010e03060112080c0d020a020109090203070503070c1e03030207020f10050301 84
    0x70340d503841c2c0b640e1040080b0f9080000110200510041e85583d44918071075103580003409080e40c900c10b40380a400d2203070003030003900042943e440103010400190b401d15860340e548030703400751402d10400242401c58400e420086010340029030260620b00614103081003035a9500d1109811a8410001c01035020107440740c07500745607803121001c201c808880f00020329141568100048500a82c100c5a08000d41070b0320520807a8170480032803100d0382e912121030085028805486403548009a445809c0c540420b004451680100d18001605500e44400404980142c00c045401d80d0342d880e814010f000001b001d10810500920348110420010800710f61214418801d0b0400c11420201d29400c114044090354108195101149c1c1c01501f810402595240c241d40c00340e01290882101180300e0303020b402164407512043d1641c1d465604c0c1c10400329000b0210035000e072105000480d581111026030b48002203058002d0b0740168075240306004116600311030f2080c01d4031400030352410b044000d4101007520f04 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 153988084 1250 153986834 153986843
    0x20c01120b0310020706060b03011a160c06051e0a090b07050304171501140913050c0405010f090501090204060206010554010e28020c060711010b0904 66
    0xa000e0311440301501030980303203000c0740d031600401c884140d84007010380c050440140519020700c120350b92005144454842030154050710342c40300030740045034080e88008101d0181010610003698496840c0c08124074a6a003000001900c00200c0c45000c17a0f1180402d01307a0803020343c8032481d069015030701074030400080c8196a42994007150072000d120017801901c00074402516010170312054040541e4507806800c3c11200382e04a40e80020070340ca0b00710b03816481d0b58003001d07001a190344c459200401000c0000071003103030303188a00d56070b000042c2c40e80d014050080440f40500038001d42001c610100390741050b00080c00241c03062008020031940054258112582554650301885400d40c0001819541102022040516541039011903070074031074014070540401c007a200a281018080410b01200b0b2040c3c58a10781070070302080c000e024080040340311420581d0f41008001d078010603042680c01069500029800c0b900800c05602d800c59081a00212540c000708042c1442c034000542091000c0c00140 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 153989334 1250 153988084 153988097
    0x30c0118060b030c062704020c0102090a06030c080a110d1b020c0f03061f030f0b04110d020a03060b011106010905010303110a1e08220f0b0f0301030f0c17030904110a020c01 76
    0x683d40030b41b040d40d4400c62405081503580d600c880021702c3c041e51021082130300501e0744410005150b442803281780c07849401590744046a4440b42d000d1030280c18203146040380704600f00003e100c030405d81e01c01d07002003401d01259420f10700c48104010781402c1080d840a03004055030740c5100c0b4a95404076095900140c40f0002c0c40c0c0d01103015695416140c007580009011448000d04001840400102188035030300c04d440c8a030440f4460307014080b5a01d60440000d401020f60071003440003803825080948c042c00d062500d100c07170381c810050840c07501c5030a80c08801d600d9500c8006005244d8854a00341024242c0c1004102c00c1095540340d1215207010303001900926852245070f030801520310221740c0c035109200004240422420740801c1e40384450b01c12034600a0700f29500045030b950300000c0c0d5003106060840c003405c40c0c1ca5611040d41440c3d09410480b070343e5045c81408107600c4100d4503074001c0314400c54001c549800000d4240300031113000d8003042c0203008080c010600f0040d40001d02e81120002841c059 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 153990584 1250 153989334 153989377
    0x506013005011407020105370509010b0409061a040b0a0909050307082106030d050406050f040905101701020310030206070212030309030711090103050a020111030c0118060b030c06 79
    0x140c01003c2070f02c1d00ca80000781603c1801041a415002640201580c0151841007150500030780d0b412400b8000c2c000842981d4900741c10000c0d495031020f5404100c180001c99904603c20014003207030340c610402c4400507501c20310a0845507c41071240d030081e0b01681c04000641d504030000d101210588610036840342c6901d5110b0030400280140c40520b68061516030300c0304203401c0000710110005941c426454551b80c00250306180028101c81f1410403034942031700d0705080440c2101c0c154000100e41802190070400007a1078020342c0310340380c811f0380e400c22809001d5041a8100c58400d80e1485640502da0050050145031488071401c1011170350f0403106640d456040d840840d10440445a04241c2c500021080240ca05001301c000c094980c810401700140d0f9482c1400c002d070326802800060002d03403143d00040300550258580361490306c0c80ca01181e040c040a90000703803e48000349106244600c21709801d03000c02005004081124904034082c010090480f80812454010188080b030b8004040c00070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 153991834 1250 153990584 153990593
    0x40305040308070303020d02030a0c080709060815040b0d03030c020d090305100504021305010f0f06030e101112011e05060306090703050c040305060f0412020f1906230405060130 78
    0x111607441c807c00c0c4041d9120f24080754000000d1103101c5201002c1040c40000400c55807040000c00f003902c1300d83d140c0c50500c1d11a07030b9010004010480000f500b096850b0a02165641c81c2410042a9442607030301017025407210070000c1c18810018441400c1c003900300f60a100151001c503c8040101014000142c00e0b510b40c000034140300c1120655101d138a00c0c0c2000402c00240d6524450290350240304840451940d9807811011503100c2c00300114641c0046002108071242604202000e6603003080160409450b10030f00806180e00780d10038420030810b002c001d11081c80b9110342c103000b030104503000341c00e518000300410711000380100140c0030180d60f600045e220f0742c04007050f00e001d1a04078044420914160301086078990060b642604c0f14031100408034020f910002e00c00710865220700190000180c50417080c0d0080140c000110350382525100c80c19015026100b6821034040d00072061012824103042042c102074040c1c00c40405103444240041807801d100c0c48a0070719075a0800c48005410f0719080 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 153993084 1250 153991834 153991837
    0x70317040609020d0f061113230a09020408011503030c1101120e010504150e0a080f121302040c0e0a0605031024020c01020724120c030e070e04030504030807030302 72
    0x2e00950000c1c1c0030544000348403031602c046401d20b205200821642c411603145040c180110b0324640295440440c0510a10f080d18513001800c1c03016840401c9080d001c100092040d0303815403c11582e0315400b250820850200740500150092102d80c52088241561001405000300e90b1002d024809044086041c41c1d20030500c20140002031a810094800340c098054040c01050ba42035500000f03040500c50000680d10030fa648024604000301a00c0000d540d4050341d5030040e20904400d40c2040c440e001442c903c00039000d21814a20121580141040c03040000f200c2c000d0382000d0420041c11908511910f80024190544d29039040690703ca03600c0e0900a4174210700d580005000a000d14110180c0007040a01e8a11114080c0c003a104101800343c01240c0c3c840c8640305580c00d0080140840c10711441280314a802d204180c90850901e904840c807201c20380e212080040c2c00a81c0d143ea00c0780032401c05022480c054103010900c85100c3c2441d407030003011030041d8080544031401c00642c01c01014025130 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 153994334 1250 153993084 153993101
    0x140703020613030303050a0608150a0b030307141905031b0f01020403030201150905070503040b0a0e0615210d03020f07050d0c02040f020a0c0b07020c180106090b0703170406 76
    0x7030120780c0c1c411010b402040250b03828402100824102408504c458880b80605000e0700c1a1100901a81e1406007164401d440050104d0800940d1018646a04e860500040225502415004030441e0311420485d10340f40381c9000e0b100100210180d010700040c00442100c2201c280e0054400303988414bc00454100358048550102035840000c00204040d0190407409062064012042c0c0315940c038070402065820403102440052400c00001d000a10f00b0030000707070060030000f00000e140809046d60b0340b412134207450200c800181ba00c04c040301c81c03800c1d05074500f04100040c120310f250703003070342103102e0f9070355421078164050607004100d000c0010300c1c00040d03072411500700b02283d80311200c07884050031508030b1318026030240d0304110340134000d80c4c1640200d40c4c110080769a29020442c858441000f101405400c00301140101e4164220b150b80d020201c61024802d032404038601e52608030050441a469801540030810912000000c69008051540d0b40100ca08074908d840d03aa83c40d0100c000c00802 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 153995584 1250 153994334 153994339
    0x507050a05122d0703060f060b0c0d0f0c0204020d0b130207030c0206070611030c030402010e04060305030922020c061905040201050a05070303060504020f0c01050106022e060b03040b0411010503040305040314070302 94
    0x1350400414840d0710f40098140c81511101004082d40390403500071988170307a0084034855403001d200301c5100781c4a00040320850304140351030351100d10035500060a0768044940010a10748602608049241a0121310120b2008510451a003c001d41d4003a01e802c0b140500a44903120110725003003030110300e41050b844842c454650035500c0c600002142900d0f04280e5050380020078086200c001800c051062100381c9412100560030503412104000001d24102032110240ca0320b03c3d52010070807213a001800c101d508100c0500394914140314011800481c441d40d001d20141171000b0b100161742c0040840c2c000d0601c1c2c0c03421564441035030509801a05165001503000f82c40000d5907a51400b520700a0282104020001c0c8001c1e642c40008030703940c01000e001118203040e408045c20118080b40140480201070b000f0124403540d07201d446030340303d400485059981d410540200410480079801010001c0c03800d00f4491f0541c106030320010118003c0c0e001c010008404400800b00340035040160500543c0d00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 153996834 1250 153995584 153995593
    0x1809010e0702150709050d02040e0304080a11040209010801120c030219030212070e0c0903070504061202030d14030604091a04050d020c0418110112090507050a05122d 73
    0x44030a031442544007211044010f000e89044100d0040074402910b02860715550b0b9045590f0401c02005100010750354201d038002da54541c013030b1460303506101400040c440300019001e40182030030100d501144403000544114030401641d00c5a0b03800003419170540c0c20800c00309803030f48603078a000407072035039290400796001c003d80c0807500582c040743d5025001da1f403003520a81256240c4200143d601d803028010000c40e440020000351a10104030040d00117054010116a0042c0d91000440e0885503a504000a500b01041c1c1d4038041d03040c01c01c41c08580341c0c1c0300c2c07503c8603100c1f100f181005524003000e171202c1c0c032458840300750360180180c1c602c0700131148001c0c5140b449541403a10306240c4d02c08880b0350340409805162007082c42c5282a21070149003165400385001d80b10031039030320032010700071240115062040141088512140d54828000c0c01440f40c4001d10135181041e080080300030940e8030051240500300c240644108001c500e18481841040c6950030300c9610415032031202c01c0500740a02c00384507 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 153998084 1250 153996834 153996839
    0x30403052104060c050a09151205010e09210405011d030d0f0f030b030606060714070b12010504050c0d0e011e0501090507020d08040b09010204030c03060b01020c010e0a060302180901 80
    0x3400c01681c0900d100c2c1e4030802c1301e807030360700029503450103450251404148030010410a9000d5000c401804e16070303d20301442c00d582c900f90000f0840c0c20a030800420f8011500401001c20f074100001c1c0710480302c00800d441039a462002c504500d20803405401c1c10011160000380400000340c509802c0603400409481d001030341d14400901c0c0ac0755103110000000ca0300c200c0598250701a2140820340c48024001c1c0c1519600d070000d0240350351100d81e0480351086601080000407070248503138800741840700449036440c03032021b1030002c1c001010380109100b940b83c141030149020030181110010103159902061480d0346001d014010704251b01000d00b21100c4400b41c2c1003c0a09501403816220303c040308101039180c0c100100d80d0f4241840454001c650b401d40440d022070180c51103294000000700c00986007035203036540d80d0340304840da034822645e06842e10700001d46903030188070f480c0100c402841d01200486000300091610822441540b090643c0080c2440c103911310034103901c01c0403001400402e81540e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 153999334 1250 153998084 153998137
    0x19030303090b100b091504030507061206140a031b0906060e180903090d061803030c030b0108041110050904050114180403090e09031303140d0e060703030203040305 72
    0x210800c1c04480c181c0c0c03800002050810791010341019141c250124505018280c010b10801010496600014a10500001001820821001d000f0b004d080c0c2c3c500f11301e030f024140e4041c00e84076035421401202142c03054001d00764480da00b05108590700701c1301c40d1150412004480c85007012507007000d4600c500b44130000c01d0454110b100c114441ca4240e4200d03400e25446402c0341c5e0f601009490700b020a03041007114480c10b180141101c02c0f41c40c0118400941c5001003840ca1301007140044007140861348a01200340764582510a0104015081c01c24a1151405694901c4020600f40d245407140d01e40074050007880c0c0c400c4080d10700180003d0020809540c568000350030f40b003a0009c01a206440f4000e20300c0c404121200e1184c01103606884950580e0708001c81c408000b00000c045000c144401d0210229901c01001c5801c002c1d070241d02e030712a44282c880442400d000c010710b221428428442d0040690341c880204880203180c0600e001a240c1c4c8481c074007128607108940032240700c0c8225072081c07401c20 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 154000584 1250 153999334 153999341
    0x4170d11090307060c050c0105030c0c0a0b04120c050a06050a1e060302120d1409060c01090b040204380303071b05010e090c070b0603101a0a0b0c031819030303 70
    0x110402c404031152144e6904007100c00c41d14000d002411030700520075290143d401040038540042c0c00004050400c0c0d00680061704e040b918400649290882005020510080c8907075000c61000c0780c9465114251291a000d94401d1040d10040c601030340d9900051112030151f200100d1f540110200794600008100104058100d03804203912031200800c03807460318040055600f0940300382c0d80300d0804105100070304c815150015501035801520400c444600703002c0a10404001501c0788000c40c0e424146030050104442c4039103403032503801d12203141d10100199019990187d2071120900120075010312404241103004484000300200d000111000b4010780420704802550310a9840d51840c040620401a00c40820780b030300e00e000301007041602c0102d40130785101e55204078040c003140d110801041400049a44054000c44c80b80c020743d407031480902c0d0070400c1c0002004000100d80c207200480310800d032a88a0068010305000d40a2040665603c46c8140e500501c6081802c0f1100701d5940d04000c0e026 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 154001834 1250 154000584 154000597
    0xe100507020a0b0a0807050a02190f060609021608090324011e05010c14071a0c0f03071124210618161403091e0102070b04170d11 57
    0x1a20300564007241c20503443c01510f074020455510a03c040c1c403a800e003a00d8580c040d0511204600030742a0082da0303400003141d91030005220f055034000801c4d8904010003120a95081031406034010400320425580c44a00d820003250040301d65640c45030340c60002480d000807028002c800c440030b202c64900802103a550380381280c003a4200d101070b4049514143c81100214024940425002c100030804503040810414010400300304480343d8035225094000340c1c10a0350755802c64054001140350551205101c014400c1c1c048030011800c1480aa0322041c607440e00300086c2c0e008a4542a070280381460007841c10141c1c48a06000503600c8079644460401025030410140d0399802c1000800c01c42c0c1040d5240021409940304165200d0700c1c0d65099440c1846018a01c10030030001268100180958500440c01805000d000b000040100c5c15400c042000c0000d0300c0c0590b0f44148803a40108100c6000340d40c2c03055116a085100807035804410a060243c0c1c0441c00200745880c5000d45880d010b407008000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 154003084 1250 154001834 154001839
    0x30e01090209281815020c010e0d1803110402070309150207090c0c030c14010605120c031603081206010c0f050109210e04270606140a03030e100e10050702 68
    0x211503c00494003415960b0b1000d480d1040091054140d01080b00d510003984c0ca01550f41c000351411000440c683c0c00c0d80e885005ca16a10703003000513070041441d0404901010301a140046d6814146951900078961410b8800d40340183e400103500010180b0035000d0303030003415400a003010203591052000359034410074010303002418034002504201c540961107400881e580b6036140384140c4c0e415910005540094501071060b9074035400f0106166840c03000030303d07180303034283d00501d81c19200300c041510f00150a440e82007065800f50062010071950801c4030303c070301410305480b00e15846410040300c058442c2072000c0e202c02d40c112102400c11070306410428880c0e026950010403400d01c032650507141d00300d80b43c599000c903d90540c40002d50800d030b00300144245150004100c12110780403c0d03510141c0381c00046079050380c2c681045c0400d940c03807246080f046c4401d8460300352150451b68068041490321420700c0c80b415031040d041d8511031103860788c80c070f174941c0140204540707100703100000c0c02e203400440c0d00300d2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 154004334 1250 154003084 154003141
    0x6050a060c020306010b090f0d05160e0405120408070915050a08010f05010618030f0510090c08191a041401290303030f010e071119060b010806010f030e01090209 71
    0x240050b413810aa940d16600140523100b4009000100000c12000000441e40c0d4020000c03001000300502003a4030041070501180c840707915080c60581d0401a000300440102001840140301004c400604070040e034070304c0c1e80001901d083c3e03010301c00740703501041c3d000a500ca220403001082c2c408064000710a80035074102c091020740d8841d90196102c03140225200112503440e0000c1021501d41501c1c041c1c018001c2e000c1d00c018900e603000c070350250780d175000050b80c9204004008200101d0b0400813142d8490310800101000d194075580d8080c00121100c10036400b00058010400b80301200480b1f1098201c15002000310440c0400c40150762103628071203d084503182c09220301c0c1c41c1800300440303200d4100854000b819030b00f0705c00f81c00c4201202034903240800c00980b07469503200404001204d004008a104000320194516005040c0c071581a2410f04100d1100107104c0c040c0d800c01c0400090f01d2081c140840d010342c000c8860303030041240340b034003035070010402d000d02c020f080c5004407240c0300740390500c0f651 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 154005584 1250 154004334 154004339
    0xe060a0302090415050105091318030c020909030901080f06061605010606030b0406050d0f1703010618060c1a0705070203010207080307030e07211a090f06010602010b0108130606050a060c02030601 86
    0x394102c003d034807170580881c2041140300c50524001024100345035074080c000502c0045001804401c0106060407030101c0c0202e072008065183c20080703164050512401546420000da0009103a0b4801501750f0001044a2000c21143d0f0750b1141030382c00c0020174800000c000402400c0c40c41c041c0c892807082201181c5070516a030001e080070300030030f42941d4000e0a402c1c00030b041030341d444502451004c020b4420002c0c994009001c1c3c25203000442c000c10320307a500c0660003855140f00380c000da60650f0220b803c1c49900a50ba0340000c005000c102d4903211400c5002029a84170041583c00b8419420b0003541548005141020421000051070017000780d0782d0100a940320300e0340000c2d501c201c90b019103084010102251310341e010941598041007031054000b03180740480741018203503d0005a0703120ba4141c1000380c210b2411841089100c0c0140b1440c0f0080c40140300d00707000a00101c0010305450784100601c14040305010698000100802c2c02915116415584010007445100c00c56022031013802401d000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 154006834 1250 154005584 154005611
    0x31a07110106080312040524040c0902191808030c030c0601050d0201050414010311040311100509010c022e11010c020d08010506031008070603020d1b08010302100e060a03020904 78
    0x51100350f400402c000c0d49042e0f40f601c0140c0041100400c110398610404803801c1c8038541c0b0f90f001e90070b0450076002c05000c508007890401f1003003015821a2640380e06c1484004ac0e96450101a500c109403203003085015581d40c0e0940c118841d1454114a04900c400031360300e4002030000000303010039400b11041c1c40e180d9880f0410429448010a00a40020340c10b1006004039070300d41d8007804002405060004000c21042103103481504580d2060750040140c3d41e900010342001401c8010450140c50203d00d481d0742840060040602c00750041d00503a1780300c6000382068416070324098000922031034000329003010700c80186444032401ca48440e6500b030144800701e980c00040d40d58660901c3c0d03118499541c2c00c0805024254000074800c44540c5101540024600420f102c40b0000d0211980e004da6070b030030160000f10988900f02d00c116184410300c85141521a44a00864190790b8101c071110f0844611035022109000071020a5a03c03080001da0101c24a030142c2c01001c20031010358080c00b030200c030301ca030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 154008084 1250 154006834 154006841
    0x90b03010e01020c030a09051f2a0b040204180210141204120210020301061d0f0a090f0b091e0403050c060717010b0306010c060c02010905070b0903120304110409020109031a071101 79
    0x1270f40440305940c00ea00b9103e009800c860015160000c9a500b4031541142c000c50f40e03030301c43c00140d510700c100b4014802541014010b02d40051082e140724914200541d0202e80c13075030450410b0780c042080404641c90b420066070304075802c120350100164034070f0901d810302942d000b4004407800054404c0040702c00d500c61070360003544e04039080d41d110649105003000caa0441200c4445041d41d000c4144800c0804903919808410702500d0030075000582461f010380031008640e41008882d00c124000c0c0c0c00c01900d100d40c88208810030648019500640e00c0714641515140142100e081242c051042001021075100c1440302e0701e240c803420144116642d030b1614032034610055030304a0019250300e9800d408240135400c0700241c1300561000180781c1d081c503180e590802e88250017460854000140f4601d061801b0003406510b0b4629440b09491800e1583d6801421303440031011600039070b180d2441d102561300600c1060010742e000700c940c0700c00e51400180c2e84540c913001c48004001c101640d1109030b10420510 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 154009334 1250 154008084 154008109
    0x309031815040905070504090914010b040e07090c1404030f02030c09060108150102031c02040302040e011b0e030102040f0b0310080d090e1012230102070c090b03010e01020c030a0905 80
    0x81c900d2410b82070210030005042d0082030034003402801c200002d500310880c4903984541d401504d0543d01888018001e0b401d6840c4a10b050344101c0c105075080c0415075011401c901251a6454001401c80c0054001d850440b8000c00b801e89810020034000b003404125800c0c50744444c404c030141c1c0c1340145034000f082038542003907944a00044041d070004419080b0365030705801810301401200d04010500300c4444c0c542001c10491460180c0101701081142005d004942c0c2c040d00c00002071125002c2407030041080340d5841030072004c000d003200c0e403012292000c0d81290b010300038045190900f5034076000745090030fa2060300c0d2403440820448000404004c042200004d01d112540c558007101d01d041c070342c1c45040b5800b030b08000d0540d4001c01c00103540c1d51401d00f015a100c0c481d0310b901c191314040302e43d00001f82006c020788c2d04842e4010441480010085003100d01038980300f110010360800610301290041c1908055610158800101d55424100001c060564801c0c5a6501d400264982050000d0040480d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 154010584 1250 154009334 154009369
    0x302010c0503011d070c1e143d090624030203070504020d0608011b1d01050412150603060209030d030204050303070816170a08181f060b03090318 64
    0x90100088100026041d401076100e141600c09006c56454113200d19044520800c440d40111b0307136450400000050003c0e01840100107000c07803c01440d02038901800811580001000c1440090340003403c504145c046658035920800072440b082c81c00000a11110b00c0981c45514850341c2d29541d05031010341d40c1d0590f64003030080c0540a180c8410f01001e504803000803034402d03840740400311303041000340700d03100b00c1288a003001c02824842c0300000d400504088188610348901c51120006640c02c842242c0864158030120b21880203681004824112044040100141800000000d04c03180b9000307000b01c60030446c2074581c8090251000d0b000c078030503842030700c0d0107070000e100d9440400c404001074104400e990302621188121a601c070402190300211090b01400003140000714154460724a0354800d00c2c241241c0c141c0f40c40901c040741cac0c03181d5900360350307000000603280c0d20072070009504400c004001080c101c0d900d0b400d10009103a100e802400003500000c1800c500000391f880e10500342d81050011 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 154011834 1250 154010584 154010609
    0x60a05131203020d1823031905030406060e0a0b0f04090c05090a0e060a021815160602040503030403080c0c0607230a02060a030203040507080d051b070b040f030302010c050301 77
    0x1201d0301034002c1c0d04801c0741144515650151a0703a034008180102429620030203038540e491200d00407800410140840c40b12640c2d00030f0203441a04040c6030304031510400c0d5410201d4403544c3d41d00d45003001c0d045681007021003480c4c20041c0200a9501e800c01d0503180f2044855112070000e21b4140011149605409041070202450801050403d40b086542240e09000c000c034000e048015200c0c0391600a031460010309a000a04190070303c0a0441241000390031140b00040740c3c16801480d1a6020380d0781710001403561081003008104140d8119002840040c050340d40301c1e90703242071260082c1c002402e01c44160007508044d007010b203004030440744e18981c880c0c0b4040d10201004442240e644568980074118812a05128050398620029015404082c3c1d005640c038079180c50568200b003c02d9010340030551164000b005000c1e041070940e980070300c00803a00444565030045907440e280712035101c03a803411800200420140b1380020317240160380c0a600207200780d1031440c000b203600d48000d200ea10040b888 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 154013084 1250 154011834 154011863
    0x809070915210501022b0203010b07240507051b03041a072f0310110901031503020604080d08010e090307080a020307020a0b03100b0f0a08040c0e0702060a0513 70
    0x1108841c42e451210501030b00d032002066540c00d42240c1c0300f20212003841810717151104a9a000e000d002007013850856096003107500d0885c4121140c050003e0041001141203141c3c59521001e07507402d6258190054107001c18140301c40c0140c80ca620510200d44072241844070304145190000803581201e1030034811071281080e5503846040e0b500410800c954960505e0b20454482e00c032007103840107992740340c00140c0401c1a070108241ca03003e85d403940d468901d41002042d1044410110546159660a0801185588502005010319034071908025071110000c10041280300d0000348101140b100d50b02e0342405a6218103009861020031100400103031b10411105c00010240e0010704505406801200d05041403640080c1c0c02c124950024001c000002c010045540e0042c040b800080241c1c1c0c085516107041e18400321407030b00c20545c0c0307401808111400324040003184070b0300b0700040c46061110781807030505031030003521000c099441604940c100008100c50700c05684a0f00c079a280e204147c11034611 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 154014334 1250 154013084 154013099
    0x2090a0b09011e120b01081302060f0d06120b13050c190b07050f0c0f010c1e050d02030702010f11031801050421050d050306091b070609030809070915 66
    0x1489400740d203040020004482d02d00c2c0011030303604440c0f2001501d8400100c405950414200d42e0a42880340c10001b00800f0b004200d0621a5000d00094043d1a06541d0710f4030000e10f002c5520800c521400c940d45040c00c0000c071360007220750000f06503108140c1d42603c1e486034000004d00c044100005021500003003c140d3346880c00680b401e49030b142820300d011100795200301000245d00b06003c20b80e90b58203c690305407164141070040540c507480c22101603103a1480b09000030415a4039200c010019650258894060f58181d080305050542c0201160602078070044002c0d106d4000540c106c2c08541c4416031020080d0045a41d00d20701d0350010300a60400011281e07800404082e00101030502c00d01304000b040080d00b81d0f154045d09a4802028114681c0d03600d40b40f890222010256010000140140400380d0740c4c0e42811a0499985120000780d0342409042846920500b0401425186050309590415400c0b4400c40c0c801c10303106080d61280c50799a01c080c8103564a6900c0c611504840a009210740c5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 154015584 1250 154014334 154014337
    0x612011d0103052e0912030f11090f13050709170102031b070f0213090510050417070512040e010608060102010504151e020406020309120f0c0d03030212151302090a0b 73
    0xc0c581c401e510032140900c5a8800100d07581c135102521030313403200507100b441b65070103010720129003940749002c00200010f0110002680541c80c02d03544140d04010415056035240503006d4140018141d08020f58103041d18060030040080c8204080030b01d0444403114065018420b991140d202c8001440c007030700e6a030402400680c41a03c084035400340c0303103030300c05e015865055680c81400c0e2500e80000e100240f80c10040e2410285100c2d602145040c0400c0100064403085120307007032040484031617114062441c1460070600d2401c03064545000110780043d810749030301d0005049456070f84035000a9254100124244c541c12100900749103030114880301c14002682c002035410340c8440380c40c08201035020003841a030340030303030301503401039101003402106441c0c00c0e4907a104d40703200040204100c6a07048401c584a05019072454459078484800800303260107901210a100c901c180b85140b02d103131640c4000e104803a030004a81c0144130007203030002004540e00c03c881c2e480100a00100c5100c1c85c090485401d07 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 154016834 1250 154015584 154015633
    0x20c060c09030f0d03050702070807080a02220c02010b0a09090f080f1b030307021204030510050a02040504021b0601120503180103020720100309032c0612011d010305 73
    0x94070580c420b2101840007400b10701600d901e643d17004201d6080c076140003440c9c0204e03500092059040b2940801074400000f941602203581650350000c03d030840a0a503a440000d000702d50300e45400c00440c0102c1c10f07419442003900840856440c11b0160311900b492044070203240d001010aa0442c1100001c100440c0c0038000e1030300140c04161401c4c41c51115000304a080d402c4500d4942c0c03000c0240300325582c0500c12007908989210806080c03500e141c891603500c1071140309850030749961f50007040ca0340e560b03901250041d00c0041c2042d07545140c1e1034a80b614a2007a06221450340c01030400201350b898012030b66030700d07894011000314100140042c0b01d001d00a1040b00c2c0341c0c1456401c108400014102010029001a6001034841c49039808014004008000d40800c01014503084103840043e41000f10b000488400d80c003100c1c21240c80303100c004042022144020340c40100481e040c40406001d00406040e1021544640c60f64051051100b01c2c00d600ce000042c219004600325110f40783c1d804008190 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 154018084 1250 154016834 154016839
    0x1030905010f060b0310051c0b07033801030501080706081003020d0b040501050c160b2a090a05060903030403150f0603080405030606030a200a0306050a0618020c060c09 74
    0x56a61400b44480c0c1202d21603400040c0305440802040300d40c42c02d0502020003440e00351201050b5842c01809034001000c0801c0c010300c888040760102d40c01c0d0744241d00080c01c40021705007003001088441410a15002c0360700c207458140f00406400c9800d94864060b00d4102d501000c000c04419040070801c0d00c10080c001d0030400380391001d103030002c090b03619200f00498075070141020740031504060614509440d00106040c01e2510704000e03040c2800d0b0200e10051032550040600c04068a0301d10300c603813402910440c800f02c40c0824006d60403495518000070306803e00211100c41c2215641c9080c0000e50260b00913580d03142c0c0042c070040002c0750100c0f14100120000c15400100c114184c0028421200342c1d0300181ca006402003402d00041c00c00300880341e0030502c00c4000b032491429a590750b030714900710143e017103c15034021106903d0585030341080d140550360010080c0402d00e01a941c000082a05104030003081440140b10800b9040314800c40f4a1007072600302409082e9a42c48c0840706d141d022108030b42c0c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 154019334 1250 154018084 154018091
    0x7030c030f02030c120903030402010e041a09100503010e0609030403030522060f03061413181a0f0601110304140d061e05011e1e08070e091606020c0103090501 70
    0x5101c00d0316100a51251040405181c0c5888841c0032034441d0364401018810203910400c00c2c480984e0704a0740d480413905003114081100310190818441c0052004035140d0401c0009062200c84140d203598482500d83c00d0b0020030400c40c40e040381c140c0c0c0305404c3c3c80510a0380c004001c01c2c80803030f1003040100802c400b01120b101d214400404846400080e55121800246d8a10707001c5502c00d9041c05501c009010228010300020301c0200007480d030300c001e0155a10142e5886d008080082619082c031010b9940119159210f44000340c102218040708550044d1b0000815000845079030040328920103007415140114106424043c4158490b10840c44959002da03407800c08800003030160003400312410240704c07170503034403054030786400c098401c180c20459203c012810b0356150b5000c0071031044100d440542003801c103041121601c666000294100c440749000d49034001c40e180c01401100e80c0204840e1084a04142c04417041c6407094807280103900050700084084204e540c0310350800704a0714002c20000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 154020584 1250 154019334 154019351
    0x3060607051c021006060f1e09230411120f0702121b0601140f06091206010321031505060c010f0203010f080c0f010e0603100302060f1216050307030c03 67
    0x4070302d00340c4420210700603448103104c00883e1460707000b40b800600207401c04151849801801418410640103021446c2840345072600c44980318200c0d4400400c840d50b01c5802ca141c1241603809a01009443d82e80200d05101c0280b1800441c0c000321401000d0202801483c2e45a89d0801d6021500141c842c13411440380d8205100c1300480003005102c01c070040000f44510910000c103003820003805902540035599800d5410f80c85407a00750032094801c400302d44480d5107000510000340c10b003084035001d00300d51013058008810070101c00103801c100695000407888204d01e4403400c03400d03144c850006080740c9442400030040c90a048000c3c140003501c0000200300428480f030003100300d8000b60f00080100d04000c1c8204070710309081c00140e20910301904d450091990020001c2c1c45001c0300380a16000300400000a01c0e0601301c1000040910f6000300700311345d00c8072030310318912064001d040110805007540d40400d03c0140c3c0d04000031345c03014060f110103003035030340f042e0b0f09034024540b80364803c080c1903d41012 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 154021834 1250 154020584 154020613
    0x1409180102030c0408010b12101d010207060603051002090a0b0703031d0d0f0302040f0b070507080a03020102031e06010e010e04060519090606051c021b06040311060604110306060705 80
    0x65403151041540c465100c82c03034a9070507400d487c0315036101402a0018981400d0003100801c40082d41d50301104040351400400e2101c0403942d0b0030001002d650752003c9010000c002c0d182c0c0010b02101d014000300c2d0410318240341c0307600407445070840065104421400070080c3d041d03540c01920400e8004d05000403003499090b400b036000e401d07181f030b02c1347e56030810030302d01c1c60303858104d101445255003e01d411401c00e420800403001300c0809000380c680040c030204040d010000d00700038841c0074010042c02e07a04010001d1602034040e400541f4055610454044103100303201200071014800d000594401e0b031140005401036031284801d9119036006600e9000100f0a0780f0ac00300d05e00d1030b0030b203070480d512442c52426100c14101c50445e00220700f00141005208031a107070141180c121159100001a40c40f000741b8010102c412041010355400c1c0111030810040c0b507044220015120351000c1070314901d40d20003042100b261060070242414403001d0001c02c1c42c0b424010041c0178a00e1082044803003035500c2115 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 154023084 1250 154021834 154021837
    0x2040f091e03030e010b0d0204110c1f180206030403080606041e0302032b1404030605010801021b010501061202180603090f010b010c1109040c150c0614011409180102 73
    0x810103081c040c120709800406a1501c00e80c0030f00d184000c0204008040c20700010000000d04070b010344241c3e100c4e10102e0507400c003801100c20b003145070001c8030300240303002c411100c80350415030b4440303880707494030340345503035200d07202108800075a4010510b070302d07540e1503640c01c1d81c1c10100a054250001401d0001045a0680510f031150b01e845100340c0007000c40ca548101403501ea522404039004501c0342d2030b42103481c140b50035200407058503810040612543e105034064540070701c0e80060035107803c1500024101c80306600509454142000c500c0c2d1000f281c180341d50a8800038403d0b940003c51030280380c6c500d07226a601811140c0001c3d288400b100c11114001000c68005544c0054960080f01031400c9041d02403040b00301c865020700780521845040e44441c0f1480ca9145151802951804001360402000c8084040604010540c0d18064031541800500b50f0720080000c0300c0551510b48610a9178000a1140d8100c50410b032104204501400c14848200d00c0a0641c00c240109604242c0c8040020700 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 154024334 1250 154023084 154023113
    0x308180f03040e102403090203060a090210111009050109050a0812090c01050405060702040e010c0203030702070905010b030a1805010c180e060306220206030115030605031902040f09 80
    0x7941c5a03401d0800c04035945002404030a4070004a91007048030104000586040c080d41c44100601300050500950141ca540e01c002989405030300100140b401c0164040305101d40241e850240c0360403190360640340f0320200410341880354482e680d045045041c030b8208000f024456400441e49041c02d954440c17030300440711001c492440010400d200420980190300d51f01c0704c0083c008004070144000041d000340b10754007449004480c009101c070305541b01c541142c04070514840080145c284034190094580d001079070f0300401406090800981c0864902a40f130603510070000107071464a0b404000c030021b01e9a508450903108100c04241e000c11400e214040d0300800c19114042030000c81d030582c480d800001e400542440c0340c62000e000054400081c0f4a500c01e20007088030010252078090801242c0403c80000e502035000400443c8105201e00b03401d00b103140a840510829407524201515124103041d0050711001050b01d84c00076280c15000700007100d0903458001800c01e034546a4500703007021003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 154025584 1250 154024334 154024363
    0x503031812240718180b0621010302030d181202040e0304080304090f02040311040906020c0106030311010b0306070512150a060c020f0a05060f07020307090905062a030103030818 78
    0x3800700441240c00c0b216961082400e440d081310382504215142c0c00c8090599803680b080303503581c48540b0140c1c0700d0318100e130440601180600c1518040c1c502c048100802400128041d008403502105502d0190000e92800d2003090503023409a414054003008469a91405036413013a2101d80c108102d4030240000c101620810020311354460801025a0698034407d601102130340c4100300800210711089404211840111008a07111209007801ea000e070080c05100c40e03480d480d00100004041e00420b040500d104100000e00003d90f403282007540751401191141c01042007000911501440605542d03400950010301c01000c0b0510700115100b91491f4001001042541c000e281c1580b0b0b0040b00d50340c0b500c0c0c04a941c1d0100c0c031b0070840841c0140c007500075800e07900d40380890f00c00f045640a025080c09008200800c002c850564100b0ba550380606441014803c0d06040c075140080d010740140707500d20a0151442031460b482c554048459910042ca44401c040040c3c4409401440c207105441802014 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 154026834 1250 154025584 154025653
    0x50d230103030801050a06080c031003080408010204030605010801090c0b0d0f050f010e0a06060207151101050f0f0a02070209070f031b05040602070b0306180601090b03010f06090503031812 83
    0x103518025080d20790607040745120b040c6c52002040801ea00030041a4031003100c0c0800c54607074551340748412880c25680c000401700c08002c2030210b0201d07415409042128000c920602590b41d03030348403044c200d540e202d00c042d20000c0700c0c00f030500c003a1710800300405000f100e1150029660911103000001c03a2000c3e0380b13000c0304411013001081f000d44d55450594000368540c108120862a044002e95990214801d903085928080340c2c00b0869801100b100140300c029100a0105141036084104600c0040b5000c1d0b5800703c04402003000e0101510039613200540c06001d4030213603111402c0a80c0ca0090a400600815407180002a07080900005d28a100c1c1e41c0398660546490a041b00641003078403541207a00480010700400c01c5556412203508207443c0421010101c13510f400340100c2d060b110036000107201001c00400080d8529541040700c04441403690749860894561040545074480c440d04103509920350050b0320702038030300b0078000c465400d404000c441500142140c6c4079a0001c0c0410350035106080c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 154028084 1250 154026834 154026839
    0x1504080d11030a021b0102030d1a0109081908030a0f020a0c020a09150504020c01020c0a0c08010507030207030507020918010c080a05060111120f04030c0b030a06051f050d2301 77
    0x104007490780c6400300c40c00055803c1a460010081d40ea90324240601850200a000090380303900a004440b1080d43c0d0384018041c80c2d03441d4404003003500040040d43e001408185000414040200328200f210b901511001003c411688481c802900003624803940c031030740c1c1c0031005404602840107000380c1001c1e4590400c01603040c0100b00c2c3ea020075a018480c61810300800714596400d5246040980700110740050f110461034000c18024010149110014400c000f002d03800c2c0114088040116000030000344140c0d501d1200c1101640100c1078002c021500c148007400051800b1900740b079000c0b1800d0721102045080d03000c070f20b0950300511140310118102800740400300740503000d0198084400c2c21302074111a24800220b0303407000340400303081003404003245601ca405e6109084800440c1c022008200c001d465204e101c04030750040d6107251141d85031040c0003540b81401086020200c400c0150701042d6801181e00b40d03525800141c010703181d00e9555096070308684214649035018902054519495030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 154029334 1250 154028084 154028087
    0x120906070e100c0f0f05010c0503010f061812020f10030b040e030a17090a08030f0901050f15060a0909090c050109240e130606080912040e151504080d 66
    0x3030381c1011040c0a26802252800540e4100880c80a00c40c3e12000b406902d040c5410812148901480000c01c1542005030040156900c0b40296041e210074003541c0e1030311a41c8034410fa5440c5511038141d2200c12083d2820014691848203903046140050045002c2c040c50b40001000e042c4031a45c0200441d45d140ca0701c4109041c030384644a00035102000079417030440d1180000d4414542807107040410310329500000c0000700240718000c0c3e4194410b03801c88d10b0b41014944081d65010860700c2c94041d41c80c140000743d0071024005814000c052030100e88040013003040c00d104403076201003402414000504800030705207406200b0000107034003410542603040d0822000500000e00e540c000e03003030b4044c82c40781000c1ca8600b25442d0344101841d42003090908200b5000700341e012007421036181c4110714000b0000f0b070164014044031b100d080c1500c25100300580d403401000d040e0040f4020004c0002c40200000c0085d18402907008074000014130300403285803480344d030046560080d003014429401a00b0b01c07000d0503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 154030584 1250 154029334 154029347
    0x13020f01210e0f0325080d0203040b040b07031802040f0b0a0807090b0105070309050609010c020918190f110a0312050703030b010509100e120a060b151e070302010212090607 76
    0x1001c035070f4040e6141040301040103507001c03c50419082985050b129220400142c80120b408030b81103004159181c0c5050f080520a03842c00719000d0b100c541d1903c000945980c031038801d2100094038030400b8804d4180c02c3d024840100015080020b038655100300482143e0341d8010720030001c281100c000c102c0c03c0c0c10300f5002c0c02a90070a5003c141401000d020190020783c01c141c8a070256401502ca071515460314000403904100002c80103900400c19a06020311090051224074804000c18100d03264142c030484011f5000020340001380020f100c1c14004000509140d05000c04a0b000410280d4142e0b144c1d01c880c9441d091180d80c030000316000045000405800d40500020401c09003400b82c18802c0c042c011070901c3c1186010041001002c0c0c403182d00715a18114680c001d00303090000c440d0a0015498168001c05210500c1403140040303003441600c42000c5c0e0102e5881980b0800c18100005404007075070b9264000c1030080701035540a10001d0020415441242d22a50100c4010805418062000f4020 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 154031834 1250 154030584 154030603
    0x31503103e03040f020406030803010303032004060c03031823100b10030b0102100f0b13090804030215040503060406020a121a010f0c0512030702100513020f01210e 72
    0xc1e500e0300307a010803021071010162540706800c0591198031040c1d40c40054020000c80d00020440d100100001c428140d1581c4000c0000c1c441c8100c02031464000000c01d1058040d52007401c00041d110030914000070710a411014080c440c4400d00450800c40d0713590708410481c651103544c100983d030400413140c2003040185015409821314100325600c03400780410018480014810203154403920450350b164070802c648420b40005401c100028000d15036014080e004042500744150044410b104c00400c442c414646420380c0000c54501d0145581d00384001002c0b049500c0c0e0580e882804001a9920103120030b610503071240c14016611801300f580900081c2c1c241c0c1007102104d180c00d0912401860480086561350001d082c4601c12400a0000316800090317031800624074002c0380c0612203221204005113000300e15a03000c4e1505007078024610b200b10b6a080703c0340030340050152020300260a01e5019080c40301c006160688102d4494851000300484103c0001b6030307940c0d5010880c4034000180111300c10f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 154033084 1250 154031834 154031921
    0xc0d030f08070e0a0603110c160503010b18180f030d0209090c0304030c0602090a1d0703050c0313150b0409030c0b011215020a0201090215030417040b03150310 70
    0x30b0b5240d2800460751504d0280590820315554000b0024902821070940f20030900c05004c1b6050302009040140c40164103110345c2d0f000307600701078414440b840d00e50040300c40e4203d441d25010159480101400010103c0400307920030303004d840d41803400e074041800204002c94800d24056520080c2c882442107158000b400c2510340d410600c01d00001a5122400485160b0003820150302e9070715078800941c00c0ea420358442c13900e103407070704954003214410000c4891050010f5142080140d42d542041c498601c400c85401000c0701000140000040c0c101e2208a07499050440000c0d510680c02e01140441c1c0182c003060b4049640c0400301c004102c2c6010006015108400e0a40c2c00d00202d5a14941541c92290600c81204d8011074865400d40c0700b584680c0c80b540d0010124181c45800c00201a0f8a40c01510240c4940700113012412030341910900700c0d400c032220a20b0440c9581c0d078000c0c0d95500d149510360100d030705d030003080009003802d40c040c0101c8030650b09181013406220358240c00a0301c2116400b030600c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 154034334 1250 154033084 154033097
    0x9061006021c09081e0c01050906041205030f030f0f0117191e0803101a070602070204090b0901020a02011506170705040b0a0c051504050613050c0d030f0807 69
    0xc660200b18040b28000d810384091000500e04025500f11a06401c100064441c02c901d81c5107480644000d2404134201e18107480b020b0420030011a2184100401660042c2c0b0030071081061070030408060550790700850540782802d241003100c0300c8550050310489801a24503082c0b041c46004840c4050040c180d1060825902040842158448031945035040d400954000711000340004640d1b498403108003a0584404d400880ca8580c0007600180c1791a40c03481098076000c075a64500b009660000480185064141a80707a903468020350302042c0101e8006484400c03c0b000900c1c402141402001d041d800980c80e034491240086c2141d00c5902e40520410200c24104242030f000500081158035020001059590b01c81045d2464401c61340041b4000c00c00060482109501441d883c202912640036207003110026142d481c030004082d1b5024025400002c045a0121032400f050b41f440b500c600b0030344034081c1610340002c1300e0892013901a000700d00100c1c1e907d906e065024511980c803071510708045 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 154035584 1250 154034334 154034339
    0x6080c240c0c030f0102041e061211071a01180603150e1e06010302120a11060c100203010801240806060405040602120403020f012304110f1305090610 66
    0x48180804503500402608800242503503510001e01c80006003a401600716054444805540d5000790700c1445001d540b540a0350006810107010710002003101c2440e03840c0c81d880c20b155000311008061000307509107111010015900040c400400720041c01507079442d031805a614003d054000d1007268500c04ca051440c00d0001d00009007440d150801180240d1800140d4040c3c440343c1d00d01d0400381d0301c400790362540d941001c100c05070300003d00241071f80c2c800d03203032a00c40d003003034140e21981d035008448003c1141004449252045c00c0402c0581544040c0204a0703162040e201e0f440b03800c036442a000110030b41d445000d50b284080c0c903e840550300c124020301a0640e07074545800d803511808081c1c4118810307600c940204d000e006864059444805440b070094909041520340a595450b56020b07400360307035080c1803074044080425841208101c40d0800340d00d64a58030780d6603107009503400759484d9512688100c041c0c6c1c1951554402c6c103030402d900a200245500340f20420300c5c58000d00402c002c00280040c0303002d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 154036834 1250 154035584 154035619
    0x30106021c031e20090a0905090703080d0902031e030a030b010224010e07020312010e0402010509060d0f0c0206010f05060309010f060816050d0c0909050a061112010801111603030204080d0306080c 86
    0x1002c04851f84c10a0001d1340e03486400d4007034208a103a0348060300290300802d038034010028907400a030005100b10121100a0000f50392980f8070717101106050055041407202000b070324000e0700010b00071601481a50300c881a4407452051940b00000d811080e81d00da5801805110a4040a2a0400340e940011420541640c142640c5c0a0050151004964651001c5011a4011420b03104056401480386451f601c41d0b4010000500f0001011561035041411500d0410300105000e4161800d54a140d00e0980c00c000034045240d01c0a44140040d660360305d071a4074035400d14413030507000e00343c0300313001d804101c99181d1040912000754006a1140b80e14008003800604184007000855a03100004901c111701405e1150928410034000303010a0b0800d0f00394180d80f20314a0003401c01840c1140c0070340c1e03da40c03145040c0d030030be41d401e076024201c0403404c2041d03c0022030180034040703015200c2d141c058601521600c2141c00c10005542d604003181d1508802d01c00410148a00080c0360804d580b400e4854410901 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 154038084 1250 154036834 154036849
    0x60c030606080c04030b01060f0c050304060804060b010903050c0616020604081f02040605030121020904050c1c02060307080c0409230a0e06150312120a050c030106021c031e2009 78
    0x90b10043c080007144e0f98610502038040000524bc100090380e80f0b981c1d50b44009003440e58111411074900d4680800303968190b00484064054a42003002029954640d6062010640c020f24014514061310500ba0700103030b482c50003c101409501000d0402040c079200c80b10390100700b0101c00b488050046c4001d0002e0741d480025241107445040c503022403e0b5844050030101082020081e41000c070000c200414000009501184181d042c2d440c86000311101e07020305848034250310020b5101ca410008620380d075102c0c6984980040e684450030b45040d41d207200e40c404503200f607190f80d8200c0c940303078030a24104030a42c40b43c103034000000042800340d16920410917446000082c007440100c8404950f00c1196141044910921141a1b8089584d2291042c5410740b6120032103400340203600700700005186403090b0080d40d04030748454004020908580481c802254110515402050381d14242d50500b500e0391a424040d122400c41c001661203080c0320b0b16110007910204101505004100076001503c800d42d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 154039334 1250 154038084 154038089
    0x30f020406210210201c170105041d060906040515010510080405100f020403021309030c1103010f02070b0405060105040e0c01120f09050f15191503060c030606080c04030b01 76
    0xc030310380314003c9514025503090311070007080b0005d9040c0f61418821814002600c00c001042c81c036201d80d40d90900a412940c64410000c014030300c03640100108410308183e00f02d0b01e451400b0001081c85003e0030005181381480031141415540d00a2080c8024000300b4801484141d008264a1165605203004510403000b8403038038400300724501c40002c00b40203007840210420504080140700c4801c0d01c41904000e034000d0b020683c440c2c0108011607a6420301807050311502039242c0c4812081080c0c92329540022034440c08225055521012010f40c00c031220310003030a4a40c4502e551022600306420b15a01e00101600b215001e6464510071300030143c4001000c08044c402480c1c6a040024169101c1c8040e200480c400c180301401c00d0024400c200b0003107074070014440390710129031850910759865041c03034006498801ca50741440c1080300c80414241c000352180003a02016014280d07a81c3c0e12541100e40002102001036600c1d03200303011665108410719001255074016034101802d41c0c40d1100d500c101031 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 154040584 1250 154039334 154039339
    0xb030105060a1d12010905061e06060318070f0303180e0c0c0c0a030b010501140a05030112030c0f03050306180105100c0515040503180105030709030209090c0604030f0204062102 78
    0x84041c80400f00ca00c1c08403054880040c0031220b00010340045036018240405084805000c0c0c1e1300000d80c200c000014414a4030803410703107500e59844d19424031601d0382c00504000711030304a103000350080e9a4100328160003403000c1304a6a94287c034605004203c0f0602003090120158111010800101c02d142c2e00c07504420205d10640c2e0b80c20001203d14a4180301c4064160001c0d1070020000c103110a654101381203c000707880b801581d003081c1e45c0b44440c0c0e00c031b5400748101240d410320040c0068101c000341e0780b040500ca8241030b091400141c40381c500031803440101320300192001040025504003602174560345060404943c00950400c0001001a441c00b0f80784030820990078203400900000700b0094012800712130702203005007081e0905a4507030b4001c100c90342c2141e000c20398440c8154424000c50348206940d0703440c20325060840e400c1003c0703004090081595882503005811540d0b603001c009000451055681148840d078500c188015112036500c0801c01403a003034500080740082860454009a04 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 154041834 1250 154040584 154040597
    0x1050613050118080106090203012c0c0a030e030c060a0c14090d0611030c090301060f05030309240c07140402030717040326060111071535010f0b030105060a 69
    0x42c07450f90b0308415510804a543c05c0c44800148490306500850580769032000d108181d0f81c40103444400814007200c01d4210070302a40003d001001644060301c0359680c2403402080c014044842c151960300f014040c80c1e2a50000824485000c80610401c029007078030f8200080c20b1200104440e90b41d00401a00c18002e0b014003409404004450303000d0b503a4121110892626801c103c00001580c0d0098803000740070f9840d0800201d0704200003c118402c07103178010f00940c034200590091000d0650700d00c6013158208100d66544800800d44030180c00c0c404036003801003d680d8640b01c0240a10914003003268000ca104105010803da8000c0405020144031100c080701078481d031a040740c45109500c5040724501c8004204100b85d0854040c0c240501000d0341c5440032001d81001e01c0d52110118820040b80301c912128680c4000d026542c40c584c09420070b001c4c480b2542111500c002030301032103094019a54500340c014400364040c151032401400841c4883c3d0308560500001ca171303082c450310702c001062190 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 154043084 1250 154041834 154041857
    0x608071b080702190906090902060403030309020a03061a190e070c0c09060902070203010e010501140d1109010b13090c17090a1407150201090203030d0507020f060717010506130501 79
    0x70380001c803a03500e60f0280007a200c90703050004903210001c0c107018501d805030800100055032512400f920000342d4000301018a040d14640c0c054005185a80d0f0481e0000765018001000c1f0345580302d40d145804062842d05011900b0303c0030400b803001480b189885c41c00c1001c1080c0b2103403045c3c50401c1c2d4403034118107003401030080c607082901c0e25641d958000518641850b078003080c030080c25000707031240c98803c1d4004d004180d13401ca40c0c0740c01d1b00e109014003c000200383c1010b59aa241c21a400d414540c0244000f0007468008000710300705c0359090700289140300d400920b250141100c5404c01c00100701c50310b0104401114150000c2207282809401c0840714466008100700760000c0c005910b055038003000e00c001754140c0c211259290001c9100d121200380c402c0020007078150043c099a00e42d0b070b500602561a1481d400c1c0c1820041c00d02034044801c603c582104400003440800c045801154039446007043c2000f8001e2192030000e05800060181c2418014060000d184003005000e541d02400d041c0010722 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 154044334 1250 154043084 154043093
    0xe1e01032f090a08070603091406090606010e04020d0504050f3a090503011803020706020c010c060e0c06180a1202010807030b03030d02040306090224040303080a02210601090608071b 80
    0x1600080101d0017848400900300380c040d408948168429070134034481003002d1a6031070719040c0407103850300f20b500060300182c469881040440c0c141e5000410043c20208940c40d030038212201100e0440d06540100c0721401c00c40c004100d90641c000402d1250310031008100e01d0a0045107c1001c214005011039041c0880743d07015802d1500600b5020b030003004003203801c0d418101c00d50740c001803d0740075009190700418550310101e0384000c0b8540c1a1981208031145944a01c014406021000b059006802d1a801d0580ea0540100b1000401d082080040100c0d0001c2204448107680700c040c854041d5100304c0b0060340c002c00000d620100900740045c2e400d0051000c00d003180324854091040070710005003c01003240a92104101714000d5800f1031007154080130b2441c61764121296400042014407040001a120318100bd80c01014a207000d070030311140c000000e51a900c43e81e140a10611003204012a82d6486400080240781c0e600c0e065a260405400181c1070700302d02c040400541c24607005050911 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 154045584 1250 154044334 154044349
    0x3010b15031005040c0c1506060c1e080a051207050702010c23030c01020c010e0318130f090602030106020d020c0604150e0a0f06112b0e1e01032f09 65
    0xe03c405003081c0041d528181d40201081002d280888201042c048296003020391845110180c400035107400e11310500c2900d0702d40071140f091440700c06a410175000e81e0b0001e90f0240182070002000d0b151251520015401c20004840081207181049030500c13940015070b03480b40e01800000c0c0c101c0d5250010222074003170b0280081c00526860080c1c800003910400040c01540180b0031a020780d4020040c4901206d0110745038401c0e10701c61101e440189000b01c6080c5407035251415040a00c1d80c0001d0106045400d64040d10030f507000986400b46d020004000c940c2d0107000e5020401c4d10351024041c000450000583c0380e01032030090403016558141f600075083d0240741d0141103240d00800718a00945c0d600c0f000f581c00c0b0180e024801c0017a29028103440005000640c00e044a0b03d02401c1c0600030040304c88000b0310854079a118410001100070040b2035858040100000c00c4840103103c038602e0302c0800140c25507000b00c141442d11485a40101d02c04200824849485000d070f8809640c1c80c1908000584c08 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 154046834 1250 154045584 154045589
    0xb030706030f0213080303180609060604020f1309150b0a09031202010b030f0106090e07150305101e0905150a0e0618070c03021c0f080601030204080f03031503010b150310 75
    0x40304d10f880414580d00010140d4840d05134600203841400310000e0154503400f050740c5292240d40602c0c0841d05914064014066580b120480365003024840f104881c98044613501c8078030318aa8421000021050050148001d4012040075030320f4441c070103400030032201d040c1c440075203032020622610380700500c01e400401c1d03400001804ca40031b080072106114001d141e03070710851240e5440d0094441d0075030710201c0d00f00100c070748102c894010240c840405901400000b04513041842d0300300000718101c010a0810391503892041c580209403401e108140b403c66074054010303c9501075450400580d5503a4280720741c1901c40c0300c801446076480301000700d64503440c810100ca440704001c0d81005515070380b08149404890080d42110012080100703030041c8010803404807400901c1c070241c18058140100b107026000a810f00d4014074099440f94a103081540751501699182c000006000e403040c2641d0240d001c0f410210020841d40108400050b8201c0e04012180580c0c10040300240490b529001c50000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 154048084 1250 154046834 154046857
    0xe01050f0d050c0d0c050a080705061c060e0a0c02010605040b06070f050a080304080a1202070b130c0504050a0209031606021c17010303210b030613051212010314010b030706030f02 79
    0x2000c40c43c5c41c051a0360043c034019a80940360203075000604800002d1070100721400900010703c5c0c24080440721b03588a003030390166005a500c0f4075001a0807807551338203911a1020b408005820620004000d0941d003c0b0307401248079a0502d40d4040c02a07543c0c0049504441c0e2080a15a840b00e81c0e2400f1070614800c01d00182218202000300b00a011a420060030000300343d503600c140c40301c400d440c000304900a0100140c604001a030004100e110740d9014081c81901441041100c10303a40d800240964008498080d035541c1c010800d002241010007000d8081580001d401400900b410b40003599000004442800c02181e11400d0320064019450b44203c10682141800c080d80c42c0e0401a0000d4501e8006c00341e803a0302644100b411446078426080411402409042641c6800811002c1909000c4044c2c0300d134020a000d00c0320040f1000000e0503d4401c803070600104e585507040c400c09940e130110070380c41240d0400e402c00c0a03994012070100151561400c00050751410016400028080d0445009 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 154049334 1250 154048084 154048099
    0x6030c1c0b03060612011b180e040c1202030a02100504081203011508072607090b0c060106050c100e0c0910030b19021b01093f0c02091f0e01050f0d050c 67
    0x303001907000c4d4001520078800055400c0850b500c0400189d42c100448000d801c07413003002414440d920142d120038a81c0760009007100c030664000d40004070b02c92118552500819000942008403404c00d204548410344800c0503a411980b410369140c0740d08070300030580341c2044184800100304900980085a010f1001d031020407e004a807111358007a280140d0740c1c0008076410403c00518141c0003011212251000005001640d20f400e0f0140c0700c030307004202c09112038083c5c0004001c0a40e1284103480b03d51b080c0b50000e003170b0400504140000800e0103005c50f121420403650a01c045111000c5181c0c200f402030103031680484034080f45100030300a11940040c0c0d803840440100d1410415001482458001c00c0036403a040c60311044030107e900c42480407107149940d448458501d035022400c4a1001540707040c0041d504142d0f0340001c00d00d01080b100306c401c0075100054000200e096001d03010127003401403005170f00780d414500012640014415660710608444c4003c030304003d0184046060120041c2000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 154050584 1250 154049334 154049381
    0x2040c020a03020c04020904111309050a0204080c12010204090f060905010b0a020703120203130602060601181d04080405030d020615010c23070e0c04141906050c07030206030c1c0b0306061201 84
    0x8ac0d00c08407903200f81004141030070081095100700b8401c450848055100925a62250700144201e500c0103141c9032035555070a1000240c3d01c44a07000b121002c0c52100c100282c11030821804408544068009968140301440b100241940000707084050700c0d000404640e8004100304228034511a10f51180c00304659408000350003600001d0700c0740113078000d8982c6d602c189060700580c1101841c0d4850300306c90701801551416000d10032100650018003682d0018a8140c2794000700740b400390856101801079200c5820403450403825410001050400d107418480d28060b6258840440c18081060182103540c4a103072001c40001c0144100501540030100f400c1e26040400a445800030300c036100c5803c1020502c04068074003c14030305c014101c942144890282020300031119078101c10188030081c810790340c0c0400507942d030001a501c00c42c0e0f50074119607030310310850500c0219100714103404503890401158142941c0d02107502ca51011054401048018060200e1405400303410080031401800f071060 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 154051834 1250 154050584 154050607
    0x1710110702120a1709120106030503030f010e1003150b10030c090e2202210703060f050402030601050603070306240201060e0c070303020a0302071e02040c020a03020c0402090411 78
    0x40d00155008868004140d1a2000416283c0b018070f40001c1c04201401640c00c0c05803203042c040e214541001e0b11140d000360082c044242100c8668100b51410381c4048100046070389282415409403402d0041c64545082c2420810102074442c040280741f20410300902401c00d8240c0d00860800d80010155104141d82c0d81010700200740410319000061090038000c1101e030034a00003980500b564100c12000d50003480c01c038480c040d240f030000300c0e800f0265503044407032640024a030440c2c1c2c000711005841080d2843c41d040080301c10b07490714401540e05010801001d41e40208049045800559240baa01d41d40e40a08400070000360300800c165884010519800c41140781c20041203403440c1d00204001900d0301503100e034801c0111600390205008221302c50001c1d120360060b04c1550709900f0007600b0704059549030314042208130501c0f80d001191505e990207624050155691a40850026010f90350540c0c9000b91200380b062501c901482e0001061400e5032591340c403072141c0398050180551038486c6000e0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 154053084 1250 154051834 154051837
    0x20d140702060105040b0f1009030f060501080606010903020607061116030203090f0d051c02070f15090e1b03040c0e0f0414070b0403020904031103031302121501171011 74
    0x402500521402c0c0000c500340c1014411005580c4005207013910624070303601048800b5200d116068108072032048004005140c056446010b148101c0c030114071b84d8180103d06c0d2603c00c0042015042080c0801d0030030150701d40500b01c654040c0c20220204d218440003d041d0740b40d1160b40c007000200700805800c10141071340400039020603103080760b0b540c00c21030440c803c00030144034858003e401500050b008040c00088842d46000700300450060300d92266445840d000c035100694003080c0c101c00b010f11104550b03544080e104010f410000079100350341c18914540c90700f203400d001000d000d0140c0080441c041c02031000d034403401008855254511881d10020b420046c034429101100d0a0001d24031080324560082502c1c01503c1c159841e45080030316540800800040151041d01448090b40c5500e41101040c070040d44075000d0380038202d41006140c41070000d010880384410b0001d401001c170444600c90b00003c801d0454101410403d901071800c6441401d001414820549072407500300c0c040c090410000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 154054334 1250 154053084 154053091
    0x3102030d121a06040501050a031e05070206060904030504060309020105040506030103030201060e100501170601110a0c05131401050d14010218040605010c030f030c110f100506010c0302030403080d020d14 89
    0x1d0050200707440700c000004100518071002903020000740070a002d207500c55006019007002a02d00460070003c02550840c80484c3d401d015096580c83d42d0030810034980400c08036801030710946d000002c5240c1510f0040032400307503001d2001010340b150441c500796032242040d10081c0000400c111f07501d50b074a00d00603008000501c600710f0a180307004000303181c564105400d2002c0b902c041e10355603849840d1920510410034000d05660500c1030008046100440800c099082c0350303c5848107c6255040a0400c24602c0420551108080c102420b644004050b2007015044504c1a030b44090542454604840c160101d03590204507903102051410700100c0311841d40044941c1a9000c01c03000c0d490300011102614180720240116091074100c500e46482540300c0600d40f807252800329041040900c207141820038064420f40c0b554011078005090a0080c4221500042c0900308500f10790042e9401035164001ca02c006494001302007500d81c85085141c04440040b03216482c10002c002e90720740d000c10501b0054 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 154055584 1250 154054334 154054367
    0x101704110f13050610020a03020309191203020c0f030703050c13020c0f0705040b0108130f1b090905070e01032310050a0906052406030a090212030a030b093102030d 72
    0x21442c481051b400428410301068042c2c0c042e524000e02c40092025440165841210701c0c3d094001c00102d01c4d600382c4034000d1440c8a50b0140c40d008804008000c4061201c4440c50b11940043c5401c0000420000d8082000001a84c41965800315221480000d0049104825050243c10035000f00300101090b11801d44008507410014003050790011500000b0480d015a64003500c00740317040118031040541c034080c0340318941c0031003448401600f02d100300710142d01c41c0c07802030344034810348003017001c2445688d014041c48420600190b2440d12082421103007000103035280e00302c0042103010314078188540340d43d0808041050115040100007203006048036202915000e01d02004902509000045200100000c1111b40d82e10198002000007590000e025182d806944900f100c0068071002080b901c8990329030080c43d244e200404016050b40c04408880d8031a0342458100000340901070b20b01c40505401201c2d8410911101107d0305901d459003101a40c1442101408010300398412000c01505541 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 154056834 1250 154055584 154055599
    0xb01060206070513090e0a0c290a0c02101803080a08180303070f0509040f1e0204050306070804050f16150e0a0e06010207180b101704110f130506 64
    0x10142c08845901503070703c10074100d0031084000c0001c82c2d42c0b0b410607040c0703e4020003aa508201036a03a40032445080c0c0d8082e00140b003070102021104420010740c0c19101d004415944c1c546070012100502e4025038920080c030859036549100c818620813407841c03407001220031308400020745a0903c0b400701c0e042096500e00298000c40050040d038410001100d500804500a50450321000825661080000c2c1201c040200601c911a0ba0b40e6486c040c80001c028402d0700001c0d10100203416241081c40c8110400d56180100130800090b200014450f920500c585002c0030652a14a41141040001010714920380704007100203810761000c44002e8200c81e10a400001841682141a24090f050710307540360f480a0703005c84c00c11002e400d120280327521240510507030f240c0c942c8800c0d441c000907039004241d440c00c40d031b00d01035190542000040100c40d003d80c2c0c1400129040c511b01a0a11300f1801000100241c069040360843d5403650412800952170042640501d003041e500c2501c01000d0840b80584500d80 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 154058084 1250 154056834 154056841
    0x5040506030c091b2217030304030504031506030503030a0b0a0f050a0506070302010b0d0303060504110909040f0203030f070f2a0e090703150c02060f10030201110f0601030b01060206 80
    0x340014102e4400002500c114082d030303104180540d8064881d265944580d00401c0219550039038105030715521030341180303d600110300382084180b8180c6032005400b200c0d88100305000103c1e8000041e01c00f1240d001c0010301804840e840d05070003403e1070350300c01007152002001340062400f142c1c01004403a1403d0b078000c03035403c1d65042007203108240da208903908102c5d045400c3c440350401e60000c241c064003c0c00007060442c1c0810110b44080601f0f601a00025900c49080c0400d2416000d80c2041c181c1e00300c409410101070a001500107000603000a02d500c0c1c2090a08013191000d0080e20b83d2555404035070ba44480032420071352a000c01c113040450b00e844a185c0c2c209004064509030b40000428039289111050403d000d41a40c01009842c030348a610815070000005222807210518400d500c890200e003922002ca0041d217081c0740a4008072400c2818000c20a503107210046031022640c0910b4030f03014024101240781c1c10488c03202c419003601c1c010b100000c000e20401c003031000c2c104e580796400c643d010398 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 154059334 1250 154058084 154058089
    0x14030f041e39030b0a02120405030a0908011a01180308160c0803040b0a120e19060b010f0e060a180807080f0a050601170c030d080624070b180109060605040506 70
    0x1070b019003120180e80b032030100a00c040381d0710603031503030f8400c110150061510f89840f16500d031f140c400300c1d0121020740c00026042d07585940402154010f00c0240000d100304102400800c0c00648010030719810403021310300700125049503004000085420551541c0d549040300420460746201140685203480b80d0200050f05140000031101260902078481341420400704085842d504108114100607441e100d800079181c030240324080340c00701c403500c44240010541c42c20f0b4080e40d403070250480c14040300d1b0800c41c0380940c010035104600d000407202540c1d19050801e080c1c61401d120b859514401c6101c410201e00010009102030a41c4c3c03011048072907a2291065107540c40350b2910000701a90040f0f80100150000740364a004c025111400380c0c7e1101401d140031900e0024843c504c100011140401c1c0070040c201500014002e410301c1c46600701c1441801042d19a5101e030400045c0708101c41d50000e81840078005401400c03100e00802403000266070700700400541101c1c05650700c91440c3c5008500341c1e1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 154060584 1250 154059334 154059413
    0x10504110403050307020127060e0f040905060403080a060e01080708120403080405130e030304121e090e060f030d081605070b0a110904020a031b14030f041e 69
    0x2260f111004519000141d801101c44508406030b100c4826580240c5000302c2c4000580300300a481c255581000410039041000941458001c10038080c614015622010584c0400c101d948550182401045510b520815000410042d409502d07084252400490601000316400007100d00c01c0044404e03e00ca21004c001c075034486d80c4401000903004001c100610708000e50f51240c0919031000001d180c00c0e50155440c1581c0c002c46003200c0c100244441030bc00326400c4a0700820048101000412040e80d200c800b800e9054540910041202c00c4c8001039200d94800192070a072100c05011356010ba1181030300541510401e840002120340d01c00490600c0038070079015a0009a040750388641181ca0f06030808005006083c51040e00711001c1028214030780700c0e0b000401d00a1000d6400064641c984040d83c0440c034416810315042115510707204100030340355001d680c0c00401c3d441c02c00750251654501150244201c080c5400c0745015032484400f401f89018000f11403204e07248100c0016203107406a0b5485 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 154061834 1250 154060584 154060589
    0x18060905130b0609060301140406060f14070c080d081b07120e0a031b03020906030609070510020c0a0303050301170d1202160f0803090f01060f060e06071401050105041104 75
    0x850045081800d101d4116004503110b100003401091800c0300c40720101d074140d8000d80002e1131400704002d1350000c1d4103152240e60020481481d00d0460b5081440e0014040c5400185405201d080400d0490078005c1e054055002404050110b48020040307080c042c1580400300c9040034001d26a5a2207124210400122205517500480ca00e81e5500707804000d8401000c100011504510b0401d40400012120102c503004251a2440f40340c1d000d25520400c92950001410309000780c0001c2d0501c0384100c0c0c0050342c4000c0d11401c42e1001a6010424012032502c07030350551180d408980b494000060640040c019816103207400054004c01131209034941c1e0f40c0d8245500040000c0d8103000326103030340b040b036030241009807140080c417a048482c2e80c0b1514050801c8000070b4440a20000c184040031804000992a42c0204402070080e90b01c0d010b801c54521080344140414041a0742d11a89103948200840b0070041e8401401101904070703c3c1298000d010034001d0070b000c1c510305420000900c203507030265001c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 154063084 1250 154061834 154061839
    0xa030b121504080d140106120b0103090f08030c07051501061b0b070f03020d1b030b01090e06010e010311120103110607051c0e090f07080a050f04120e030d18060905 72
    0x18142c0b61a90382c00303919480700540c08501d564440c41d04c1c900b400324580490090600e966134144451828132480100c4855805c024103061421014030005900071032501d183e546c10038641c0d51079550342085101707a4454110001c2440c010f280650b2401061255004c1c1600c3d140c0d500c4074a00c40307503003071584d21500c842a40504050b00c1400003800c80c5216440603002c6100c0c900c0c6c09414102988241000e80d101d251401c4203000035207040d01c024035454891241c1d000340034a000b04889142010300300385640060300386410015490502e060b164040d4000303410050070f01c0300603a561a000b00750030400d04001c1c0070480c2c44402c09400c41c00940340c2441580c0d50244c003c0e014000d25902c1001e4902c5a002c082000c80a108204c4031060b002c2e500ca01c0218801e80b1000c1c9804400e14003103100800c200e0303000388503426462921081c0840300d2414503405502c958415101c3c15042e1240c00c043c1c50304810091202d80c144074201c0e00a00807a8000140500a00369242d040c0900352240c005071140342e414017810340c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 154064334 1250 154063084 154063123
    0x305120f041e0c180f1401150e0303041d0403020f01020c07050405100512030309010b0418020f04062301120b0306042303270f01090909020301110a030b12 68
    0x254064010401d406544508403c4501c036986000031459094403403100c201144c0c0c1c5040d280050082d900071403090410130030440c0710560422101e03143c03c1409104050400041ca440081c498900b001160050100c04141d0f80413401140e2045250f0402241d04400602030f540e07403d504414140252201d074003680c009002d40034103101c2030000400340106411000b84030f406001816031500840340070101d22920140d5520314120702c941d802e551542d42110301862824613004012414603088952840c0d04a80d4040c44c0300007040000d0203005150407403410302900c1507206007440c112250286c80941c003030301d1303c407038540400b0010400c69001d85606900350300030000040000c0c2c80400f0151030b400804481d841c3c2d8901030500245150015031303011000f49030a8036030800d01103a806c4401121981200d1400b90820601c000030500c0308544680c0043c5070b143c1d101081195420f4000704043d680e41e14174283c484c12100801400f41c00c1c080d400b240900c0b4000015511042c0c045000c00f9881180209030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 154065584 1250 154064334 154064363
    0x190215060109142b020102070f05150f1b07092d1d0a050601060905100915020c030102030a0c0311190507031b05101a010206010902090f0306040305120f04 68
    0xd0510f08120002d6220403040d400b20b000c0305503250000c40070041c0041388400e450151001901e0f01005401450346031007601403c0145039102486400c0c518031200200d138443c1d0035403c00190034001d007041d00360f81014000740c4203c06500050801c0c02c0302e0710704e070092280000a441141c8030360010b1032410720034110340110110b1103021350041c0114800002d4a00215207015089904000e803010302128907070805e200412500740d009140001901d4200c0c2c9020005a107031001074558140f0780301d070b03603c0c0411021880700c01e1402400862901003020f00295035174544520100002c114032147e52000ca4544000c074a110b001d020242d503000d00d03110070512030440c00c1c148142c84a4000c07c50071420000700c58148a00105403900c140c42040c41040100400b040c40a9040c040c0c1d0039042c980d9201c12088031152200740c0e0b0000300d41d81180c5400c480142d03504d030a0004909483d03035000d007403601481828203000405500c02c0003401f01c0302d82c0b007030050182e4903200c1443c040c150054801426100c07520404 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 154066834 1250 154065584 154065599
    0x904141002070c140f060309030310090c0813020f040c05090a0605040602070b0721050316030c0906080a110c071a070b040318080f0d092103050703030f02190215060109 74
    0x5200d260903009202d170f0f40b02c44203007000400c268401c90fa001c0705504040103124103074041c0c401c1100a070080600074002241200001024260001c000f00380c10880c0454038030654550582d143c1c0c1c6042d000e00180f26440c2d0440340501a0361211202a00a0440000c00210b02d0311a105540582d0f039542d01520703000c1e1501105184540003841c043c0d41c1040c0c80302540b00c0c1c5590640e90f4401d6a42c041e1217480d00c924280c9031317103c031002c1c03402054001c0c581014444944503501000b60320a03100d8034107043c01d02d92156411a070081205210002c44510002007070150300c08009801c800702d90741c01801ea4100708031821040554001c04800800d40802c04001c100040c2c0929415040400d130700080b044600c0c0d55148480c40d01e41201040c0380141c000c03c00c00d1074501c2c0d100000d41c0140000c0020a074040c034414010f810a14000100942001004555201018032a80011130380e46000d4609640b1005005640703580000800d80b014003503c034602c00b0f1000c138907035880700d2481213070b050f1203551010740b51250 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 154068084 1250 154066834 154066859
    0x705010c1202010e19050606041a1c0606080c0a150504051e030105010f050111030702060702040e190809040c030e1e0a0602030a020304260f07030309020904141002070c 74
    0x204402e65485101c51211031038204400064407500109008800d00c1504219040100240100303001c2d600f0140e1998102220301a0343c03419000580e8060b04918002d55001503142203e48010440782c01c1c020001100d800c00121880036000455004450310f41d9005900ba9451b0b507014404042081030008001d40d14000d40f0100d5008400c010a0002e0443c240020342110400d822007400340c40c1c008000d010f03950703020806c20b0b08015000025483c2890940014400f8024008000e114a44803a5001c515000c01d00003c0c1e00403021150380381c8102120305d810b180702c0d0400c02c0300ca03000700e241200a0301300501c40d0207015240c0c1e00801c041e211039401d640c5180007000700d003804e040142c4513041807140060340d1f41c4001c62094105a4006850b411715244c1007840d80c1042040c0c29035010700034500321140404104030b442500320b49154598400c42032400350054800700340065488182c80c4e0800050020181080441460010036100c01015120300d241c200e004138080900440024501880716042c1184c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 154069334 1250 154068084 154068113
    0xd0803090606040516091e0b130f1d160e03030c010606030b0603130308040201141b0d0504060801090207020d0b130c050301111e04050603130b010503060402130b01120507050a0206090705010c 84
    0x10440310b01c0e07100c0300d40248c030ba88401c0c21942203946124040003640007034ad032110301410307060301590303c007143d51801030307490b400050a5014241e0f43c00051035102c50066051040540d4060305580e01c0f11030448041303008140c01c0c130514000c20304240c1c51014a2402004a9110710003081c9481040307002070301c040b6518980180103d041c4114000140c2412100c3c10161211184000c10032251415048840d4181280740c45d0380700c24040144400d000441c0c01c0902d07981074510141d00107031141c020707000091500301002d0024184d040080103110b22440015040d2400900541940b40015a11010b060072260050300303500c03c07001d090040956046440303580000c81c090b00c48401341415162000107006134000e44040a0356010a20320004024200102d18018002140901071501c0c0640114441008030b0a0511440d940d910320050160302403c590444151034140421007031400f02c4024002d90300c049840030140c8689400200c0545001602d00241c800603516901019203e5464a10b10038040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 154070584 1250 154069334 154069379
    0x5150712060b0d02090d150b0a0f1a030406090c18051008030a1107030203010501080616080114042f18030c1c03020f0a030c120318020603060d080309060604051609 72
    0x55600082281c05006440c010b01d01d440000c1c0001231a810040c080300c01b40d2007182c8000030b15000300011105082801c02d9013130f4403a40c10f5a47e98a03403620100916681e0401400007590810202d920222100034400b106980c0c003007040a511001c007160801070300c0d4828190507a008102c540c0001d84207103180b600c0800c1e000122500c0545030f60002c0d080d42d0b4243c11000c000c0d4400010072402d2407031143c2444084081d410400003650400519108a0b560150483d00442c0c468400e042d10484490500301780007003a81500f0041c02c00f42d80c015400354013034142003c10a25500b0780030480d140c0890540c5000000a20041c1600120b00c1480001d09286c0429029400b03401a0b1034443c00c0700703020040e100351195a4038054881c8514190041d24203a40802e41018035058011911000160704024802c5e011941c1d9520380d6560000510701070705041008101620100c10300c520f045001940718040e0404640910540e52076058419500154a01d014005169254104030341404040d4003020701180 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 154071834 1250 154070584 154070599
    0xc020c030705101b060902180411090601050d020a090501020708010204060c15020f0406120617030909040510060609090e0303040305030a02030a06120b0a050702071206050604060305150712060b0d0209 88
    0xa03481382001806046400f81da0300c9440c0d484c000210304d4241c0080456a20481d101a8941484d480e0403003408040e040141c0106501c40201e03a06078050002d8682070150a5000c1d541c0703800307100000b8000400c4d482a580940b18440010031380c00c00600903070302a2851507640181c1c04109446880d200c1c80c40000320060140c4c05c106090094201c680100003814841d203030000c0c090342c81c483c1c1c0b4080724100e40c0403695160300e440804800710300200488900d21011a002e007895151414079504000198610b2040320f0325240001031101d401c0780b074507412611701100400054220045480e200d10080f0340050000701c0400004409080325805107401440b001c03400110740d41c41300001d20045500c1442135440c01d60041c104144030303219016541c0d110103180b028000881c6407030302c403001c0c156950074003c10031074aa100151054a455100d54000c40c0c100003210fa5402c04684219407440042c1c0b00394000440c03840008a40e00c51a0003144102d80385003000c2458001a407803204000d4103d948800e0b800541c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 154073084 1250 154071834 154071857
    0x207020406030f08030f010806150103021305040510030b0a0510030f150f060305010515030d0c030e03060c0408060109051b09010e0a17070909050307030c0c0308070b07030c020c03070510 82
    0x26643c4900ca106403050110954030f0409503000b443c05c80c01607002442c20b030b0003d8200648000d0003403003200140028240035889116486015034203900c1c2d600119002890170003002458440d10814804482c0214410b519030389421000c00c041c0d82080700e0442e088400043c0410010300c50880714400180644148440c18000d2045c110940f60b900b00516011900e8600c14403d0180070721810703400c083d450041d85006007441001c231392202c0ba55102202840a8121044203040c021a40c40c0b060b0207006081c0c40765031030491281c500c1c6800502070301c49148100d8002045c0141f00e0321130300d406002c00f20500c1035101074070040348130030383d1200134441c0c100002c8100190140d200e0400d50300203000c10416542400d104d01100c0391510001380e10070b014960401e1038600c08202c1c007104a0b03c00ca6014030b4410300f00c0f041c505001c409803071107034030080809100048500600064405080c0500842d50b000d200c0c0d10300840080740d540e040e00c2c4086a15800681d0200310303918080207103500c2d210070390510001c140c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 154074334 1250 154073084 154073093
    0x702070b0a09180b0f040b0607020a0305010e0c0a06080408070c09020304050106060809030f120a1103150a171c090b0d0501031104090503041203020118050a02010206010501140d020702040603 84
    0x20021031041020801d40c074010300c030320001c0800c3c43c1c00c1c000c041c2e03400304400424040010403c00366007204a000d1350391919000788035191071048400b015006042c80140581d81e2500c14003d1688041c864028042d00540c0485850000c090804442c103070b50310350605840d151910031165010280440f0420b2034510300042c190401e0000d10301c00e0380594000205240750000142502da001001031503150001c118401c04a01000151045c0340c0c1c05120307a5185a4800404100410b484610500b00721404010005242401da00d2410540c04c29103a400403e9501d010395242c1800d0308144d08005c4d0068400c0342030b40c069903000e846c0c1c2210540740608605603141841c5049034844800d4110342d540b60401031081c07082000522110303a1007a40d04001e0002d560300c815440e1700036030048000c0760710009070807024140300350403d904840407401c801d126036170b240c0350455950b104594100d016002d0040001071540c0070318951881107046008035860442e00d034481070b00950024108903403183d500e010200205 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 154075584 1250 154074334 154074337
    0x108150703051f03030f090e060a060e03010608061003170702130903021f020a03050c07021008040c21050c010305040804090903171e090d051804021b0309010f02240702070b 76
    0x79406500c40e00541d1800c620700411f1034645420000511921b00140140798a560000f801180c0403440c0c5007020781d08000010b0b0150809600c0200144688024040e1b0200f9060040046920880f1240c030380c00e2250048194902a618001c3e500003e00c43c0c8465001303507160401c0041520920641d8800c0e545e04d81c00092084041c440600002c3d40803900103d440d416104a07134111068010480c1070294170381c001843c04001080c6502003004082c04141040f81e0f0301605809014442c61031a4007040b1303101a104e5103161250165040d1044010000386035000c0d00c10b242c001d036000320480d0718142c00d00903404054100020200c0c10424a190728100e404c40c40d4080034014500341ca403481d0303800203500054a4800000d0107a010700e40211000c000e181d50850101c0e464528414150185ca4607840c1c0000c000b405240e6840710008404246043d01680110007040451000d803507020000030300400480c0d0781c842c229070080044048481399800100345122950380140c0ca032045451154645001d484103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 154076834 1250 154075584 154075589
    0x90f0501060e0601171605071509110906040203060904230f010911090f01061407050f010522051e0109080c0a0b061002030d0902010e0d050a0b0108150703051f 70
    0x145030b60401400800d41c0d00c65050700031103034804500784050424074800e0006074041c41c150414003200140b81010000115031900400304800400c20101c007041c06c040003144034080c1058410700500001402924042c8262800b50308043d00f1448035941d19500e824004071440c1c44885082480d110411000c40100520780d4660700850011511510320325191554411f6021040e00c20070320001000321101d404040035045401c5880d20845600c2c5060408119200700100640f23103000d0060100c1d01500150411802190034001d1411b181c3d900c41c60101c50751480c0d0704000d100c2c1d0800340000c44000480c01c441c40e42041d050000050301c48869079003600b07a52007a0700080c0d9a4010300c030a102030204100d0140e074017000550351100142c808090080d1244120350174612259a100c83c0c000135640300d01c600011098000d002c1c030b1a00869428229680c107e5840200c6100c0300d0040089a80c403000f080c070949264120310038066503242c55070281c0191078000c10006014040e9001c41203200101404c0100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 154078084 1250 154076834 154076849
    0x20d0207150b03010603080304110a030f140c0a05060a050715090b0103060b040c0903021020030915040b092101050103030512060306010302031902040603060e0d0f02010c0e04090f050106 82
    0xe8041e203101e011000d540041018610a901d80304040000c1210541140d5000c2c0e4010180000690843c3c001600001c15420280007a12000c0c05d0b94100001103030442640710500007113602603148201003014107481c90003450b401000030700c40000303003a006030040d08405106017486423012490307100160403940403500680303149001c50b0040083c80b14503c1090b8490000f40e405022403401c845018050f480340307110007800368110b0f43c501d040b414402c0c0000c402200180701103410803074203100710f41e9898118070180d501c0760340e40c074000300540e5a403074045030100d44014aa240c00c0c04a0401004441d066803020402d400c004a4528000c4020a1017020b01861103511142c1e241c50304003000c10b81f03004000344018040e900000041c0056a00051209000c848003e042164000f040c40070401600f100c0d031006211500340b141b8030480d4800419038600d682d000d5a12541c80000c0150101c0c240c07501e00c81d1403000304062030303025492400c0940006e80000d01551004140000b160345507070131240598481d54 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 154079334 1250 154078084 154078103
    0x80a0c1407060e0d201204030b060d0b0a05061008090d2d0504090c0c0c0504020d0e01181a070f030c0302070f05010c09121a100e1503011506050a12020d0207 69
    0x120417540519041c200c541900b001841c01c0c000c0d0800c004094812400050000d440c0c0000151595860799101c8203c40da0020300c101c01400c0518400025000c141d540c18030462440c54800d1000d071148d07203400c0c840c41d890340007031241600d10401903400c0002c18108250f52019104c11345058000000c0e01c030301c0d0011316a11039075941c0c80d1101240c12160200b40304810030100d80c0002010801007284801950800c540060b0307030300c1460760703e0b6005000a01007215554200040f0700c001040c4011305207400c0c0d00034200c85010440030440740f0020801216007501103039826040c141058800e0f80300b20605000360400620700702d129200c0810f0001c00200c12a032582d11074030111003076507100c0c41d00c50003458581035043e408840e556980ca00c8840360400403032200b41c040002000b0740528803d040042c81c10fa080240c5c5400c0c1144107585405540303a0540c0258200202d0a203500d0700c443c2200c0450ba4640e440380c3c20181100411286030152200290f0801d40a200d1816044190310007040c4180c403c4207942c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 154080584 1250 154079334 154079357
    0x60103080d06050904021f05091203040305010c030506010206040f0f061407093206130b04081204060807120609050c0c0c09151903050307060b01080a0c1407060e0d 72
    0xd4107844440c2c009a003d25030303010605c0010307200c181803041c00702c00004030036000005800c1c04450500804524075400219072146420180005c00100292070250000b40702480540ca01902624001c0c0d40070b0f03006a1201001401042900ca400c1d10098454800b0b5021214151503640540d41c2488034034003643c1c07890301401011a003210210004040b40019950030f00035207400c0302e4840c992a00351040caa107905034803054544e42e1400720b03010140b02584c81c084854030380600020580050040c401180720b5541c41c907919110003800d031402c07038403542c0c3c481d00e4075541d4a000301e0700b002a180004490684922000c540c0400c60700820f842101a80c40340c40c0c503000139600032454800b02c490a203010b400a84240545c28500380300007100114180c540c04880030380151540196071055001900600020800340d04025903604121500807090ba0380036800e441c5d242e841002c85941940c8031300414031540174488040c60a80140032440d0041400091a104108046007041e8140400100261004110 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 154081834 1250 154080584 154080607
    0x80403200904030302120709030201090b0904090221121206041d011d0c190b0913020301120204061d01090c02010b030f07090507080708240607060e010b0d03120209011106010308 78
    0x6c0c2c1e0b41c40000c03442c042040038a5070300040e048400c0d50050b44100754000030041172907181ca401c1924101e0f1b001c0d101c030300410f000c0d05901048a2500c031601c900c60060450401d1640426000e664654034031030803105040d1942400c000050800803150549500148a0000c1054080c442e0042554100801c0e01c80d8400d120f4a81d42045600000740b4401c504030505400c0180d405007114098910034104980d4854400c80001e5800c08000e1116000c01d000000210b01001501c481131000381c820754080c8106610381d0b11030305c0d0141d1689401d500503411140100f00c200190382107a590440716000020b113195034503000c24100400c4c0d0315801025400000104106041c41c440e00f0750100305850b000b005410070140090201a010b490b6418441c540c40c03507480072284440ea22450340030024803040c1c1d80c8220b4039009024200d40c418a00565103004524a040e090140038440d80f0b40e031540d40c102000900c060200e00940010750800d040104054048496070700402005000e0750143c0c0400f81c07214541300c1d2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 154083084 1250 154081834 154081867
    0xf1b05010212070b090a140705040b0103020f030402040518070b07050f010b0d08030c12070806040e0f070b030c09040e0a0b0a06061e2a0302060f0103080403200904030302 75
    0x5141194031401c1007810700300e00401910f5169600c1403440d0b6468460914103440c01184c800060009521100c0e240483c9500140c12000c03500306450071b00041d13200b90010b504034040c1801c5409c06110400004006140c03651069900129540403c0c0c9500d4141d90f001e80b40c166180c2124205c00340014002050200401408041304c000d203009000010441c004a042101110001000d104005c808540114505420740c1c8909071800d00419462408140081220302c080d01c6860080c0e140001c4540300180210301c004801c40b4050046c62014030f03107049600b40e41e2006180340e450700824000380b600d035511801440b1040c20214028180740714a0304090316101d20203441d0602d00b03850840300b041140d8100c5080c101031040d01450768084001084255960f0b0304c1c8501c9030340c031490480b0000c00507030703045ea401a4441e8081c3e4210b91240e82c40918007480030f9000c1c04042c02011003408100001100d020010510030410444800801041c50114203040d8088d14201e000c00e03004034200040045112 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 154084334 1250 154083084 154083089
    0x801020c0a050c040525050c0a12111203010521030c03030612010c08060402090102102a0822020316090504120c0f02130608031c05130503090103090204090f1b 70
    0x1c80801c46410300706e00c1c1400b0303484142d041204003503140100d941a14040c83c2640d0400100c0c8050780d03410881352400d10944880319011101080714201c059864540004030201c1e00d400441c440c3c1e284cc2d0800c400c0001031400c0e500d03403001202d0448400c3c2240d0000b800034209980411000b15124140f01d006c0007110000b003540c81c0c5a9a1400c00700c0c0c000e0542c0700c1c8800b90006401e44006a841d140400100d050072a28100d06c84050704084042c213000010701c00d1040245089140da1440031602d1100b114116015940308154030030303011405011420010a280300503200404581d001001c10303800710202c440c01d50107014002e64407002c11041c404001815240c0b1032451904445422540c1c0e174458060308040c402a003c2d14041044600500507584140050010201182d44405c110007a100c40182014080141c07a411301e40131525148684801c00ca22a80c440065402c01e218032004400614841000ba81d0141c0c036a95114042070142d096619864003414035040780e10032013a401421606103a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 154085584 1250 154084334 154084339
    0x60408031911060402010c0c050315061e01080f0a0207120e040606030908180a080f030903070f030302100905011104060c020906060f16020d1b080105010b190f090801020c0a050c 78
    0x5084201d1040b03800300b2129401542420441000c072914107000344001900d23000a41c03d88900c0d5041340440014010751445868100c900070314003141c1601428941914409041c04242024041900c01c11113910709540144500001030400c0400c0c0c0300c503a20b22046400070350101d8640504004181410f001e100b020340501e042c180320480390796440709903510a003020700c000d150f00203041940564520407030704001c200100441d1001c1d00f41540c5603880c0e901030000580720344074080000490f00140301c1510110b98254000e80005904000d0000150402c2c800031140e035503840d000d2030480c0890001800c040d0882c2e40d14040540d0003031041c00f81e07428000d04101d10952041c0840b101027074246080b41ca0f05850110440b80519461011400c003207010b01000f046c02203220500c03078124089803403040071a00c903240280700a0b645c6250309510340c480d58915103180c0b0713450320b0b521480d90701684c1c1d0450380380218500101820742e50385602d400c903000700e0503140d400d4100341150007e1010810001141403800c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 154086834 1250 154085584 154085597
    0x8070e0301050f0c09030a0c1e0f06051204030512150120030a0e040b090a020c0706030605010e121e1c110a06050415090803010e01080d0f08060f0604080319 69
    0x100d615007480410040100c55144c00c005001d01c0540ca0610840c480c6039881812017660316107840c0940c03c582c030000b203240d91003000300100148102c2d040c55a08102c070384949416103006140002081c1e83c2000600983c1404810000c000c08025100400da203d204402c5007071410038219400181035040c0c1d42200c141d8808141c1d107080320803c0201c200c1d01512081c0c01c10360502003844001c00c1c0a09401d82540d64012001f004011094646e5001081e2041c5d0303040540e05c401c0c1d00c5105c20b400712400c90180d940020859442d810b054180107007200440ca040345c045541c418032100380900d0072146544c5998046c0c00481c0c003c02503140f0101c10804030b00e42800c080c2051130800b190b103641c5030b082c40c0010341000c3d1a00003203403d212428040c40b820940e01c2006000060440c01c0042041c0e00a02c500320110228500014080320041440010100740d540c403030410609508003147c2460000c0d11941d441070700c440100c0607590310075000b08000d000e0f41c07025503120400e504084601200c000c0d14007050298 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 154088084 1250 154086834 154086841
    0x4030506010308250c050613030503030109050601030b0d110f1206180d140d02070303140106021b040903080a1109060c010f060e06030a03030c120e10200a0c05030c0d08070e030105 79
    0x3405c1c040700141e80044e681c458440c110155003810118075a40050010700001002141003466600068403e00702030303c3c103200440c5d80a051080110360801c0281484500130403101ca1454240315100b01820002c0a003c1000e040039a00d0b400c1c04000da89502198121061180c00c10388240000108140c550030404100c84c5000720500340d0780700e102600c1d400d80390f001811000301360182d480742544045c4042414002d41e100c41c07020756078854540c1d08140c211a12540300c202c910707150281080c9180c0c182d4507401c0b951640c402060103018803c0145e09a20742c00d0001c10308a032114000381888031140000480d200c00e0b02d041000403202c8903000001900c0f6408100041c1d0b440000302000201c3d858900082c0030002d4200071540450307924514103e2900704540c482d42400000307924904074200040c00c02c030a1401e001c3c0c0f1042e0511514420040d50010300c05542d500380547d0a1603031890203101624a800c1110300c011b8117080d103100340c0c10040f07a9810103218030990702554200c0400800e130000c0143d0301307 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 154089334 1250 154088084 154088093
    0x150a0207020a1e06030504020402130803120a0204060c02211f0506040b030d110a0803040b070206280c0504030602120405060f060a03230601090609180f030c03050403050601030825 79
    0x2d83d5004a030203042c0c50780045408c54496070304581031045950b040600385500e803007146032030f613100080401c0035407900f40c0406d20300c040c01d100b16012038800ba00d0700158040d0640c2400304842c0f0f8032181c0d108201081c000019900c8080c0151200008003203030040c1d8501c01d90311440116240602a5030103545083c00d118030540340012460680c1c10241050002010301000f544c0c90220060310060840402009100401a1130100980240401e8003560b119540d405003000603400c9580480000903080c6141c40d43c0c9218a034013800c2810728914000e4a00381d2252a044280c1e840003a03849003e1003481c0400007442401d12009403c00452004103804e0b061603400070b028004140009400c2d140c1041120f20200c5080b40805010b00d4100d003912030543e560f40b29007000381880d105501d030850030002d281c440030614001e42c0d40401c0e400345c100140d0201f2914210b07a002d020040c100e0070300c6020440400410410443c0c00c0c001c0d07101c0d400035603440d003030305060301003883d50400031032920b46007080a000042e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 154090584 1250 154089334 154089389
    0x90f0803030723120f0a14040b0903090607050c182401030204030f03090305010c0c0305030103080a0504030c0e010312080103050307200406060e150c0618150a0207020a 74
    0x2115914050240c080c0710745100e4072420304031003084110f10700003d040c3d1801c642180348030311424898040700d405030759243c0b40100f50388203841c05440a4010000080008601c10483d03600b0070040c004480c2045c0900001c94640da2101e070b01510550b010141d424401e260185400e2451801c20341e400645082c01d0031441c1080c6102da615400354400c242d03124105921980c182d030019070700085c00c81004280c0e820090040c01c000e00040c0e44550070400140196401502420703c00c84d03160f650381d480c603842c41d103894040703070402510300082140810000011800c440484806480701c4590707001c2c15499070ac0c1114020904c6000d10040c032030610010400701d039000c019250903540000021000307000f52080c0446007058100c04a44c02480c115004c10025800103200340c1000040c1c520b00c002203c0d1003444481400b40ba5030100f0651f01c11000500034101c66880c0703841403160700c0202d50140586c0284111012021104621150307404108001903207008580f000052200d100100124803020b4002c9124 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 154091834 1250 154090584 154090591
    0x5010f08070605090d0f08090301050702010218090406110a020d2c13090b010807090e03030c0426060717130827090103060605090a15050d080c010509010606090f080303 74
    0x43c841c011074540031544560b99280081e90340040c006111200034a801a080c1d0440e40c00d160083d0710300340000b610306005100711245850311590300010384d032a400c10041c0d15000280100c03803060b140e454a50003003961038043e1200828070780141000c1d42e44040020101440940c0015400718082980d2110907021036400c3c00d5440181c480c0c510070204810000007901c1d06500040410040100010300541c000c14004141c4800d900c0601440e03ea4546580c1da80c0026a8203050305241044108104c0c00c0c001c0c80080140250b007002c6a01d40d8510312400d06006d002c440f1030010418041c0f0415643c8d02211240342c1c01ba10712907240081c8000754544202d03502401d01070341c0e40d03418262a800c10348400304a07280013142009086001075a107038900720000d40820b1240340e001e0b1410002003905c3c0c2803580200242a030078811035002280c58101080865182d0030030aa039004410001885003030340a0042a11503c100000810038600e0510028488102a0321662020304e5081041c40006408000c40e41c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 154093084 1250 154091834 154091837
    0x2060f011206050c1303060c090504060f09050709121104050c072307030609050c180408181f03050417071124030412180302060306010c0c051203030a05010f080706 72
    0x840760340e41c13400500703544a8400b9251600c104050700208100c12a00803410344ca403903603a1404442d90741c00522064603858081c807424102d00d100140300c803034242c0d070100758440c40300c5c50420056943c034500c100781c50394800e0341a10340d2988034584c00440c0c01c1a00640c0d41100f071100865240c1078090700d80d40c5140501003500384411641c00314074840c50f00301300403040196400500170021000d161408035a40d84801c0080d03802240c103c0340710039240080b0b10625100760f800c40e812515004101154550300000c1d00c2110754000071071004059504100ca0103810010016123000640e4109410044181c0c07001d00411021031000b040628005498840c010780302ca84180c0d05102d0b801c0030f0b1300007103000403003c84840c1e9100c40301008101c00e00c0300c0c000441c0e034101082e80762040c0400181c1d60348031440c4614040a0342203202000813842c6548540400c00290380502500f1310380c0d41c0c42d9400102021094046503100fa400442444207001c07a6210f414010261086102c10091400482d143c031040b181c0715220 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 154094334 1250 154093084 154093091
    0x412090308071b080f070e010e0601020d0f03021c09020114160209040c05030a121d09070503130c06020f010e0606090610020106030501020d0e1b031002091203040e060102060f011206 80
    0x84480c0c0f48100c0c41001d0002c90060710460a405c998107507440415220303054a0800310700000440c500510b600d58060710069018051000c04100c0c155450810002500109a0700b0040c0303180042c10b507041800c901700e0011020400c40d049000061000800c2e807190010150200301c44048402c0d610580f08030168151070180d5035036240c2c10301c0c112540681d8899601805410002401c10110842c10070405205845a5040012154962905140716000749400400f110007040d40140101c019507802884102101031001c50b5941c0d05582d07111340d074061409641310701000c1b0300c000400e0141e051000c0d0403200519682c50003000087d148400644403900882c2200710a0200038404e41020300034541003802507644d1203940148900034403a11070420003a00680485142482c035904c07114465100c01001801a210613084510096001d01084c682c002c0e20500c04110546c0188003600080c07450010a034030514203c000682081d6004202c022441e0000300144940c51003143d40044042d00700c41c002 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 154095584 1250 154094334 154094363
    0x61005040c031107060204030203070605040b0414130606030209010210090206040e130f1b09050405060604020318070e0604060503070810050712050907030c09060b0906090109030206070605041209030807 89
    0x42e40104101e10007852202d600103000020711081d0b400401c105e920079811078440560f111380c2110702d4010340c01140c69504040204000041e000d0004200156000705680c0c4080d40d840d140d6000c84001d540110042500410300d600c0c0745d030301030041450382c0203150340a000542d03072940042c031103118501505c140010f6160108078626100381d500d8003519484031751881c1084071403d0080c801060f0300d0303900441a982c00008980c0c4092070059034002c950140090081d51103010030000603405c0240f010385e900030088280e200c07080b0100b24180c020000c40d0801c01140c10440c05220648016800050103640400e0040110713030b8000030784d040c030070340490800581a110002c3c11682c0c43d0414420520582c140340a1200020000c03e62000300c2c1d00c075041d0600c0e40d640d92102541614072038881d0064950052040d400641803c3c001050131142c140744c0782e590039840b42d00148180d0820301d01545c4203507443d010002080348105203100a1881e60920220580c87d40d07545024034403d4080081070907501e10b640 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 154096834 1250 154095584 154095587
    0x60504061e0501090c111009021f09080106050301020405090c070320010e010c02010c020a02150705120d0c031a04020706090c090f05060a0302090105010807023903061005040c 77
    0x40498001e9070032040000c014000c0c0c020b0402030054040d11840d10814680040c001c0f01c1041500010724041c010a16980c01004000c1ca441c070001c2e60400f048484a14041d403101600c80c07101c20040e1a14035119040c2400207017103880320b07004503010360710404c4140706030b42d19001c800c2c1d4000f60016060303681d4100c2c3d15084441c200b007581c01c9110000d400455006100b811b4100e1804c83da00c9100070801c0185481003207090724850303407038034001d0b801c03060120004d0b0528101c02c084400340196480e103000420f980321880d0900700d01d91070360070041c0404d00014040b014010050302c041286070070f00c400036000110940500710040241d20450b030025007042001038542040700c03100d41006289500340d40e03401140340980002d05021446c0c42c0f41c140058141d242004c14802038a8014203400710380da007400e0064a511002800c00070543c400d103c1c80e00071500740c0b01603154035408048008043e080f2040125800300c2e4810140b20700c40d030020003c11169240c5110684102ca034129000b0640d01600b0b02c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 154098084 1250 154096834 154096841
    0x4051c050405030714130b0907030c030213120b1003050c0f0d0b0f06010315081509070320090a020a0c080d141f0b16021e061b0709020c0a06050406 65
    0x2e0f60180100711000130840080311803170010f480251008080c001c0f681d80640102c0311001e4080d540200700c42d0104031114425840307104400d0b12420014505800480641040c0c84258403840a072004070075a42c04002900c65400d07000f2426040e5107540b10304641e40c40d0f0300e40206c1c0e602580600003190161045948a1214103591904401c18400504280b02c40440c0200c08880d801c0c0442d003409002280c5005c200d484508075004840034040380407500c1c001c10101d001c0035004000a11510f80c0210114980700b000328085800340a000104c0031068080c8060b9600050032401d11038814400c4120b09134005584c1c807191030348201056582d030404a41701c001021840e03010b4949850f04c004105e00d50038561039800202c0000007504058131750310b4103482414400c0c03110b6036810041c2c2c10034010050601d055058407880300252410794410a400105103243c10030a480b40c451700f501000305015032000c2c0110800350080060941c942060202c0417503542c880b4a0000f03007803584d240000350a0202c15403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 154099334 1250 154098084 154098089
    0x103060b0a090c020f0607110303060d02042301090f0605010c15020c03040620060103120806040b1509011706240904020301030302070617010e010b1303060203090304031a04051c0504 80
    0x18100000403d0400c029600d074100e804d51040c42c030414000c51a4140120040c0c403194540c08021442c43e07540c4030074008016001d500803600a51140c201d0308645840c605200c03106019041c011100c3d600d460020f1065610840c2580c040a28009090040e80d0740217810a0301e05130800060484242e040c1c200400034410030024502c5030001041c0414860340c45045615103140101c0110305080705c06c1005501e0b0701003880028180202c004180c540e440c001c0750300703079805240244000340300c800210101e04800700c940e04080d004480014880d44568004082c8050568050241042c5142c2280030880b188089041c4550020051006c0c1410701d2002c0121038002c84050b00c00e43d141d503920310f0041d42e03444e26401031030041042624610f950540c0d51100e24101c072840400315529901e00614101140c2c0205248084d4800f2144040042400c900085015442c42c0e030045613030750f00d1070602201007002c0940e180e5a2000d00303001c0c00007161000807942024011610ba05980100c414400d840d68441c41c0d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 154100584 1250 154099334 154099349
    0x91a152d1807030e0f030f1b030c070f03020414070801060e0d0507081e030306010518030a0516170111090402090a03050d03020711060307090308090a030206040e040c06050a080103060b0a 82
    0x90782045695541604802e1031200c2c1001140c207000131906404d03031240156440440d10b25000d0003084a0201141d080d0081c0381d05080c16079144c9800c9040480c14003415070006110356101e1201001181040d00c41d000360b202110f0213003501c071308140c500144108410f108401c1000301000000c6403c0e40c8018050402e01e43c05011103451a94804c06140c982805074000300010f815103056680e484404001c99218001c1651050300d4000300b000100300c07000c00c1600481d0148030700d003550000288104800b4580d15800c800b294180e518150004108207200c2e844408664105807085501e49202400d88007442c400302c5000d0388450812010401180780b0344c2c005080751046000300803000390542d00410020703003c2c541043c12000e039207082c0195444117607503440008900580070400300c0c4215001d44000030006002745021550394000070301039009504a4154032003e24140810070040b103002c10000c10072410001c0c140302400700d014050040511015001c240c4400f01c07801c090b5500b603400b03800380115 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 154101834 1250 154100584 154100629
    0x120f03060906030b0a0b062b0e0115170f070b07020d02150706050105010c020120100c02030c010606180e060f1f030b0f0d1401091a152d 60
    0x104c0c1000748130401c0c259094a2000d1800c15282c499003000b504660b005070b1090b01154444409820703407900760344600c2d011188141d0b10005245072400a0055240b0040300680a1001504095842d001407104280182c1580c0c44060060440c0c040418000212101c003503240e5142c00c0343e80081036a0b000351604c002d500000d08414010ba1801d150040d00071f203805100b041149a880d500103694503056410003a0101e011045144102840744203084800801a0b007526403200c1c29002280a5500d07100140004d600045208107003141d003403168500520282c80c00d900c0110369800720300e001e2400380c0200b980071210340c4001030b116100d003461905440c070060900090841390700c0d00c0c1345030400d080203044006402d00a202c100303440c1c6400302080004006003850f8a861082d40e420070b10080ea09004c90341c41d501c4030810f4000c541d8040341426800e01c0c5a461160f146410f002901c04040c2c1c01c01050b20603005400381030714050b925049016414110440b5104050810000070040d01014090703440d146003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 154103084 1250 154101834 154101839
    0x806010302130509090c100c0b0a0b0114030709030c1401020f0c06040515040308030f09060f0c0307030c031806050115020102041a030601030b090a0e0d020327010c12030605010e010507120f03060906 87
    0x180000034040303035809271100303c0881d15002b400606407200020600c0c0003074804204030030f840d0b4180c40116006038040c10b0084169a0303a54550006854030b03407011040088070000000c4950f018002c0200729104e50016101140c18040001c00b140101d0040078001e466400c0802c80b0384021030100c44c080c5400030722894892a1841031409203001c1120302c04103d014040215052044024807a401041215085801e6a030341761801c4000b0121800300f4810103031500c00011345513001040504015010704400704d819810704102000c940325400d005d0085a1042100700810320911000f4459860990305032503480d00d030540100c024200c0304007000e41c040400c88c240120802c599000e240320b5841d40d4240d8003013091091081e6107038041c2e5921100b00703411000c6054900c400e10070034400aa08141410b10f940510303030311500b1003c0c0303c46c00c40001180d80d0314800d01141d0381264001c3c00760082448c2051a101c031582e1180c64503812642c8440900c0080071010314202d000390484000740c00300c10001c01c10290b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 154104334 1250 154103084 154103087
    0x140f10230d0603020a06050307020d140915030402120708070603152612091804050a050f010b04050112030518010207080a062c120304230d0806010302130509090c10 72
    0xb1184001ca21a0420201c0001d007540a50309880c8038044a401030711000a03240030544030f40d0400d070400e640a034400c020680c980d42d9007640c01846c9040a83d05552240741031300c103200d0704c00c50b0a820809564000802000b44000001d90f030400d0780c0c1e8a14021801e10500c3e0480d858904054020308801d141140f240b61078100048504600e5a45280132919454001504056a4410300c43d007203400c00c00d100040c06107a0080100d46802501c03c030220b842075105034a0f214140321581e01181c2c00c0e030f5124054944545060b010744e601400c4004144501000a65009000c82c450f05600c0500c03542d043c1c3c0e05440580c000c1c4450b9000342403501c180c810380f020510300880201480c404484841d440e11504000e404a08800300c400c6084d00070003800880403c80c9014155000280100d48480c1c2100340060a4190b5005000d042c4100500600025440d0350b0f02800d2103000411290405105200d0a0f10041441d620402114000e0b03510413400d80743d02094a0910346410800c41d041034200180d0810103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 154105584 1250 154104334 154104341
    0x19030c140307031e09051207080a0b040b101404051f0f0609090b0609120c1801080c0102060f070e030f010510060f02031201090506130c030204140f10230d 68
    0x41d0721a6407091206191311400b03101005500003600001603000d0000e01242c207001c030017105450070382c0c411100d03255502d0070300340d2800742204002c80300415104240310400c8007a041440c1c000d5141c050345040c19083c005440c11411f09a00d40c80e128940f0369010507040e8884095211046100c110b902d848141c84490361010020075200d1500050801c44001600180d58481c415080e10000c2405141c00748030010400c00d00340d1207030074170128019911403966035920540810114500c071005110366600d407081e070340d0070424214141415508814100800c0041c585506130f8000c40d0350401c0c1419507510b2001c60f00e081407040300081d0962802c3d040c024007203c000b85500886809079110f584140754260b040741c0324010700d400915011141801841181ea55400c0103500100182100348020600c444440580d450641c1b04404aa4000303800d21510100c084040f03c0c200050b40c12514a003114000700d610741c50848402001c01581d82c4210496101495880294802d45001d69480d0064130850780002c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 154106834 1250 154105584 154105597
    0xc0d050408071a1509010f1e180623010c1410051509010501020f03040b0a050c0a0f0c0f03050c0405090309130618060312080601020705041e05010e040519030c1403 72
    0x24201d80300700e0346003d18003081e0305ea060b601c0c1c04591650080c5000007008600c02c03840030661410780400e00101d542ca002840090440b01552008903c1a16144800700740b4003003c0745183c03000c03403c004401e20598004420079001d0354031000303024120300d61500d00c8bc200403452201074030640c101014452040409103080700a00710071202c0103056641c03a4010381c7d84040100d140105a003042c001003100c41a0103002c2e00320ad00407410542d181101070401e19090415811040314000ca229105000340318000041c10090072a01e0186150340b030860305c40036a10025219000e215503242d4000504187d003d0040c2c51240b04081c2c032002400713448401c08400713040c1500450f100315200040c03644001c51140125011079130010984228210b00d8241181c001200412542c154440c50100041c0781d1607174401c0c03404042c4030030480103c85070400c041d141030742d1040c0c0c041c1c54500312500c1404080395011032546000200c0b081c00c0741d061700892a0590744c1840a000c0503000d03580c46241d41a070080040000d100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 154108084 1250 154106834 154106851
    0x110706090606060203031312090302061614030f090402070503120c0d0506102c100314010b04080705011b02091509130308161103040f060f080c0d050408071a 69
    0x4043c0c5440080341e803070004603501e04220543c10702040211b40c910000c4910209545442c070071841d101d030042803599215945c0500340c9051230301074034180008110030080700c202c43d44c0030754540f900300d080700509805040241485903500180c0b581c00c0040800482c1da5003801f03580c843c0701070700e803203040507030150014588010b0301c504000c00100d03a841d1150fa071809112180c0c60b620780d103055841000c01c0072459441421008414000031001c0b40d590a00e640050319082d0f5400b107030225650102090950042c1d000344400d0009100a000040010902a00b510030130318101950020401035841c80300e409600107500110302c02c09000e1080503c569803030303060360203036607000c116100d08050180c0c01c0f00d4050041d00003196040825821859400390070742182c52441d00e4080c150310a03200354119802503101d40610a200c0c071041040071f8202850f810019858142003039036240044803c0124402d0402680744203941c2c400080c10448524151100242c00014110b0804200102501441410340e030008 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 154109334 1250 154108084 154108091
    0xf042c1521010e3706020304140604050d0201060602060c0d020a0504091b1d0d062310170601061e0c06051e090304060c020f010908060f1905061c061107060906 70
    0x544080e07480d8000704e0307030400c0da010010308003e40e616030350000d4201601c101c0320801e64102410052104100c440c1c012402040501a0121b800d90041c4c211500f0360b220f14150340100b002c02031080808805d64003031a0002a000d65a407803250300498040c0b10f03580080ca04607240c441c01000c28502c03891058110001d944a1080141a80010008400403010a9507001700090104000a19650041680c030b0f44560360200c1c003280c000e07600c0c41030440c003212524001e20b8154000c1001c42100410640c140b844100600706650500e20002d01c941d121034450320001d10801c808001541c1b003103621030f9040350440010840c070300700380504140e04ca000c1005405e00c2014040414403445000c4101c50455905440c1c1240754001c503400d00c401020b400c3c0c0b40350305106400500140130002841490701c00e5500b00728081c00e030320b03000788011300c2e82030f0b000c0309114011726080800071030340c40f50070301040290100316642602c032485242040142450400840006001003140c10400a5a401081ca01c1f8400c00050 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 154110584 1250 154109334 154109383
    0x812130e0114040c20030c1507020d110c0904060b030601080304060e1c0f0c030b09010b0901030206030402030a1e1703040503120a020f042c1521010e 66
    0x2100c09040a00903210400400030060102d450035900c0303001400b10754108485036084522019012095056090703803650400070301080300503402e105404040c0f014001c0445941131401e402552128510010002c3c003c038400c003651b010408001c00c002d0301c800108000000e1502d03203818400340c071461000134045e10035500040b50041c0007100b510241c460b96580c20700350200740410003220355200022103c80000660250010440d040485c44160703006280e1080c242389076242606610310010720030700f600e903d00404200f40d07946202d003441c110703a0110b80142d1249c50b036000182c1440b400c1c01004101d03018240070311003d002d00150a070380050140b510f0b009a10040780740402030384400c42d0010141e820800c0030650025031003040b107030408408580103091038140520a003107684a60880c0381c200315142d44502c00e11032030014055588000c01000841c07401d250710700b08100c0ba5000c4440380b040080c1a2500b46038032460203c03442c1d07002d90030003d02011024180d129161603900100c0010190741010a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 154111834 1250 154110584 154110599
    0x70614090f03030a0f0209030a0516090203010f03030c080903060103050c0f01050304150915060609090501050402180906030c090c040501090f060c2d03030e0c0a050607020904030306081213 83
    0x40c00e01c0e85040c0040c5146540d1120707118010018070f00302c410b607640c3c00d0050304103503101004900a944d200740001c00ca0481001d6016180c078000b680100412401040140b080314204130000c82120f40c141410744402c2c016141886941c00342105040c1c240c1b05000000051200000781c108034030200b0740b4030380240c60045004680d1840b0448016100e114826152803841c54079501c66010700f802100d076150200034410080081e41c0f081e9001e07e0006020000600000445110340c07401810b04403011440d105515224110300e11031000c0240c4583c00090001c0c020341c40a01a0420300b0100604400d0705180000e10320915030894010203000401c518000301e00020880200c4d4107641d0b00e500c6400060803650790760500c03c40622014040701c00746151545000c06104c80500906120b6100410301c00e02c40b030724292030b002c0051912031046045407801c1046803a440c0c01c43d0402a0181c542010708d40d0f07581010740250400e40d000c01c0380c604c030750715240302d94942d42405000140c0b40000c0c0c940701156039408 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 154113084 1250 154111834 154111843
    0x6040612050319091805060906060405090604050a06090207080c0f01060821070606060f020c040c0c02060c0106050303070f03091a03060d110303030702010905010e010606080f0702100207061409 85
    0x4195034801c01c901d00004040c08940f4025031000c0c9098461035440310b0b1000034842c030911104a0140d01c5105100841c81c0c0b2400d401c0e400807003665401d080c0740c0350000140501002800140c0250b40d00d01c0800c004001640058014089410007036640d01e60a150002d81680441c00600c0769008201d400103494206010380d4007240e1821008041c10042c40384000d85040140e2001c208040c41000040002121801103000078a42601c0d01001c00070b03c42d0020b82402c080d011810302c15442c00300b0042c02560030250100d1039a07010344200c1d0700c07810141d581600406c4250007495052001054580070020240c2d808281a80321341e0b51488800d41c2c0d42e0244078020b40070401c0d80e02c14002800007450728242040405016802548400002070400d408241554030550304000180d4594081d00c081c00001d0140381160586c3c0c100070030240380f81c0600100030000c050440d0502c555901c012035a081e10800c444c1170102d2081600f19551200d510b0650014015018882a456000740000f07141220116 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 154114334 1250 154113084 154113119
    0x50a090b040311060a02030706090308011706090d050f0706060312140403150f021207120e0304051e060705151015082a0c03040311120a030e060d14060406 68
    0x2e8034012203d0200c0200180c030b800144005085101c10301600d801b25019020300000a800390b1101c08265041601a080c0110035032442c1900764017200038040c81c1c1e040014889000b03400e514000e9250010710059082030700c10b240e0080c10302c5090400110070b00c800032030200c01c80b5215803070b06407040303445001100b8180604d01c00a4800021b1004134401ca052513001140690307a02c1000500d009054649403644400a5504a00007403e100150561009600c100c41c032400ba104011810b0130f103400c00107011205407110300c00703030511450000c0300e45031290410741e56010b03405400d44826244c01505003038015000c54602d00080c0390f44800040220103e03144a0750b6145a541c0c1c03608a90b503280100c84001c4072180e0904c0060805031032100940810b002070140004500051a80c1e5403540c02d140fa4081d2541760b804d03100f54819002800000f80c006820000c2307961600305642c0100c0790000040c1c5034011221056840781c117200ca44040d856030410100e1180b0412242000840e4a03080c69018040216 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 154115584 1250 154114334 154114343
    0xf07021203070309030306051207030b0603070305120f2802010c0302090306040f02030f07140a06140316090b0d0e070806010b0f0702030102040503010c020f010c26060d0210050a090b0403 82
    0xc0020400b102d12076000701c1680d6001e402d0124510765201c012501c42581d040b002c00158200e5401401044051004035810840403030045c900f4a0440e1507482c3c50b185102c90304403041400180c240d081c0c201d09c0c0d060301d94140720408a080e4418100540c5c0c41d0100e412481500107528140c84964058064825070740b01040140089c08180c0e01d540c3c43c0b0f40e00883d5030400340d84c540700f000143d101c5400d00700f000001a007814511a058940040300f030080841003900550701380b10025909041070284d16090320303808a0b08044001c0003a480e10000d4511805a40010070005000940c807042c040380f40d000704110a2008088400442d81c5107649603c1d99028022144038000401408a5000b813000181840c14002400185000d03600c0b00020301f101c041e0340740c02d8090b8004000a645801081c8a86405001d690030100e50040003403c50092a404180d01c5129060961000c104140c40d458005844164007034001054000c1546002e400c41c1c0100d07a06c0d60015005c0030001c100c0c0344910302903e040303a911 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 154116834 1250 154115584 154115587
    0x11220509041a1506030c040509011d160e040501150210150504020a030f05010306200c030901030911030a0b190b0d030309020319080702040c0e090106030c0509120102030f070212 78
    0x4009540b61a030b5000360440c000c00c891400a034401c1d648101c02580a4856081810b0307a59280400303000c03000005a0004842c119407611180c055150ba400d419403042c00780207031203d400c04114042d503080c1701404441d50440e141000116503c0010101c4a4690100d0f0b000c85080170034006017007040da400d4407400da07641002c961041041d070409402401e40c40f00039042c0403444e150f809005400701c4100341c0c41960b1043e02c0c0d00c114030240d0140310740039610302d42c880c8040e882c0c1540800c003983d4a1003049800d60425513580b5a150520040c031100c5120700d00010151215144103040150034024141d40007102c0c0c0040f12a042042082c038480d0110320304018249007000d060644060f00107040160050b40c00d8040d1500003002c3c01070340600e210300d051048003c1074841040f4014042112171214411040c0b0480d0349a10307130660348a00c200ca0442e00b00f07183c00328010104050844640c002d80c000c050b000b01c8803030f020391030a001c1900a50701c50141d41500311040c2e41c3d40781040760740c1d2071a660f451501840 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 154118084 1250 154116834 154116863
    0x1503150603031b060109110f070206091c0f060c022107080405030604051c030b0d060510380708030f0c04030c0602030703020706030501050f090405011122050904 71
    0x18100a55031294009040d00d052034407024410903142c40384440040301c0d40040c0010301c1002c0b0303944564141010380408490a10312941c80d00ca1440c407898901074440c0c10007207080d0700c0e140e8898181e14406e15a07040a098508068503019442c202035072030485c1c07000d00381107144072000d100023280b0404241c511381000618010b1a2130502c0b6500605080d10900d60421012643d901d007040715034041c030f21a80007040018070800302e01008500032003441080504040a000070303a50345032246506180c01200000b42d58480c106d84070320314200c3c0c0e404a1000d441c4144241f840c12010208218145146080c4074046503080c2620035552080d078030000c08400c403c4c40400c0d00102081300043d405840071200a00d0a51a42c591f41d0318004254004801640005101c100300756041c801c600040a60f410180455410100010007103ca4904507038000c200342000501841802d404c03184460f40d0100d01203650f1516402c101d81544500400f00f0310400c54100c00141c2c03030410010703580c442c070f4100c401c200c071000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 154119334 1250 154118084 154118113
    0x50103020c030702041d060a0c090302120a12050418110a051b0303041202150c0d0f0204030209090705120c0102030313030e0a090501140d0c06180801090501050109051503 75
    0x10040001d070301c4540300901080c0c0040c1c803580b042858620031451084040500307402c4c210b01d171050052078030070b007541080d600c511015000840300055941c102c0d58041582c00c10200c1620b4484a04000741011084540c40220719402c40c0040041d101c001070203d2244152100c035505482e00749024a500d010104540ca0500e40f1034000381155006640c0300f0310a00724045442840c54000751401d4a00780820003244c8003c607010880300760082e00e06103100c02c076454040c205000314085d80301400540e503151114000c4080d01342c1c1c121b070041d50b80206150180d003058001203075203c1c02405801e016400101c1e190300f50120008054160b0b081c140c0c010f43c0345a84104d48845100b2032208101c040c061030b540e00002696400d441b19002e4603140c01e00040d01d602d0041c0120755082e1030820240558409180b06003c6410b218610054402c03034181002150741c0005442d1241c00e59600612455181031002d20403c1410340001d4102c8581d59005c0c041d40c0c441c2d4038440e04541c04480a15459848400242c2414 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 154120584 1250 154119334 154119337
    0x703231807050d061d060405010228020705041d070807050102071d0408091305040b07090609030c2907060f0b040614090406230610140a03020903160306090309080c0a05010302 77
    0x40d9417052484a83c01c100b80e4405103058015101101d0507500464281050101d401c2660a070004802e440340304003904001c060340b10f816900515004075150110076050101c102c0506900001402c121944d40d035851280c2c5856480303078090300d030060149000c002445034803500000d400c0d10880358010340c20348850365003100e180e0110608507044440210280188a40c40c0700340c078880c2e805403d0748121031a000f0401440c02d41c994201c801888180d01003440030500d43e0907600d06541c1340c2c400e910f0102d01c07542c41350b00c0d41260181040034100c800140507002c1041d290401165106a020144004c0b0010400c0109941d624003a41040c0d004500c0b02c3d450710310307003120403a41041c000d080005052401041d10035002e100750a408020004007001e00c43c072070034220721410746540075207011100341c00c9016074105203100b02480001095008141541c895a0a2003c154032059003034070005011340e246860005410326000a402150b190074000400d600040b0b0201d50304440240001c03062428080103600a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 154121834 1250 154120584 154120601
    0x1a010f0507061b03090501050f090a020d1407150914010e061c0e0304050a0506030c03161205041202011d1207060f06330f080703231807050d06 63
    0x5035444a80300b40b03071950f201c00c08071090809a6804106101c0c0c9040c07113802c1d0791000d010f8030015450b800c01c01124050108126460540c100c8e071a02c1440202e060044400d4452035900200e4000c1c40fa00003081c2500e03180c94007401005072504c124075643c60800c940134448030710f00c0c0f50100760945407005007031401c0401003c0407808204d14030a00500144906d041301c040031082d90190740002018032440c5803107132a4600038442210500d10354607024030504101c0c000901240003142e0b40b0700001403264080c0740020750000d43c0000421840c9018108810340418022600700507510705548203101c0f81541143c21810400c030760051242440c032051085039940401404d80b205c0e030341c44020b8045000d040c052140100944264185001f6805070494070b1f801810b01a42c9103058079040c662101604003aa614000203d800d000c40130396100c00090b8080c00348280d038441403100344804d03071b5910440e0006060007408100216442a0901c46110350350303014500550f54081d21200700b5400044c00303504503100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 154123084 1250 154121834 154121843
    0xf090d080c130312030e01050118111207030543020a140a0308070c0b0402010f030b1906020f010c0206240303070302071d070f0f032304061a010f0507 66
    0x180082c0100c401000c81d8080d0802c035041400b2000e4013440a034507000300540c40c240300008000b42e5140c07420161018270710030f6540c00c1842d140d8070032400440f400400c4c0d419000101d082c09059141020009004140031225000c406c100d02d18405244501d140d06640c403d1400700b80034150b070644401c01001e070300c0003241c03000440c4902c01c110000948480b2101110349003040051208104510740a007110343e00174050400c1009c1d00300440045641c500c0c40d0713a0003540a003464941c607240070400320040c004007014190400b40000c00642000740300304003030003200c3c1d441c1c0c01d039840503074455110b07800c1e64071440288006a101201083c08411200318070580c107150f8001996103002d00201090070754001c04029000760301304040420002031604160742c00c4400c0c22120200c1f6240858001c0c0003541c41d10000400c0040071103022980e103010b03030b000e17259184458200d024038881068004072a02c00c200c9084820342d080c040b09168041d001c43e0386c00c814505c161100f4001c0382c0040c40803a120381240a00b900d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 154124334 1250 154123084 154123087
    0x30307060e0f070602030720060d0b0609090408030a0f0506030d0e060714070807080a031b0204150b090f0a03030801030b100e071119050304090f09020907170f090d080c 74
    0x764240002c0041c0c0c3c0080100d070300035685403a03480c10301a2445000c80700b5440d01e41c107885c1c10705036950748960441c4d90b00643c10000041265001c07011495078000d0b035800d960420325010901082c805554061485400f01d090140b100d40949030b030b08001d484080d20f0041d0954450122107a00368013a81d01c0030320f400340161520f424440e080d15132411024200000c2500c3e038100035000e000300741041c8540c0002c0d054580c01064031f111296001080380b186000c01074070b15a900c0a01c2e004550b101e07000320382074103d007841c00c0003804c0e210445480c140c0d20030206544a003200781c040b01064201070b26103000700d039003540705c0c03d038680c0c44c2d17484920040342c009100740a003480e44c45002c941c401c00f48002d50b02a005690f600401c00383e645032220301d40040450001c600551805440740040c03000000c035004e9400140c030100b19901c200c145034000d03140f603c40080d8044210002c101c2000d5004204213200a49045018032f15203881022229244060700c4c80441c941150301079898050140280c0c50700615a00750f480d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 154125584 1250 154124334 154124353
    0xb16050f0c0111030a02030412080c070b0919030305011409040b0c09120609061009021c0b01030f020c010c18030c05090c04030506070c05160501021e0a0206031306110702030307060e 80
    0x40f800394000c865101c59035a000c020f0100784180c00e8108014980c035400d02700c001d810808461019801440401003260000100161801d00c090003c00c081c0da00360f00580300044a60320307000e805070501f4003071a10300450050902906141079900c141c0907a0f0002d518100a4540b0f020300715495000d0401d9a811420104480080c000104541803050640001030980c90521000064410099038031046800d401441461035017440d844011210a141410010b414900319006034090200d060074010038078070201d48a601e104040d04460101d04140d9580301c22003070140b0350000719989602000e40039604010303061107030341040140d540d040211101518141542e0b5960b09203840422208103000a00039003188042150411580d40042d08032881e42180f10304040000399100002080f1107149100090440c0d103003203040c0803400c0c000340c0281000342d80c1d00d4401403031010502c20181c2250703803501c1c2000b8070084d18041016600c00c0d59000f0055450482e071920b03580040d0441407442880340c000d54429 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 154126834 1250 154125584 154125611
    0x203090a1b050112020309060a1505121e01090f060b06040e0a0f0c2a0c150503010314010b060702091504051303020f06090601031203020c07030f0b16050f0c01 70
    0x300441075005000307801c040c6081200040201055003002c0c01d0f0340d401401408004040402d001d41c1c007120794440020318403241e254141b041c0600307a01198002071040c108141d42d43c00403075107243c1d00440010b001000c8800c400072900301e940340b0f800580300d090007000791000614036820600340410f0007084c0c2d505040d03c3d069017107040e060540d84d508032650f4074680c203881252607004d4208600000d0400300030107444c034080301d07031803080420103001c0110513449160104007100c1140c0000d09154010314400c08144103024100d50700038007007a500d000c220008031100c0c40d014045d0b100300890140038241040311a5090210030f1001034004003194014014000c1140c96500c1124801c4901344050403001d021402c2c080d00341860182601e40c20f4000c0c5040008401c000540c044c11650702212607820a1030104044009020b10032240b401402000070001c2800752102c1800705540c01124012442e8540c00b400390401d400103000c105c0410000e10110070003044110141464048400010540c407250001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 154128084 1250 154126834 154126853
    0x5160204020a0e010f0e1011030d05090a0212120405122e0b0402070f08030702150718060e010c08090d06051f0803030408030f0a18051b0406030c090203090a 69
    0x3400008000240c031070f00c15030384104031071945991030a244901071828004520116039040000041c002c20200500b8140d608000710303121040216002c000c80c0c100031004c40e07260f0b01c0e98242640b103111070094200304020003184801d82140c03d80941d0b0700c2c042c50705007401141545410030900c0303030107121422851001148140c4541100008104082000d840050710846d0900cdd889180038030300c10301c800c100049a8442c0c4890058200e2030072a1207944a5800724039044031120740c4840900c0180a10001e0b9402c0141d224070800d450f214a192107842d550308036040e48e405c50005000a4829007510301065100c1c0c010500258050900403074001e0741e45413642038901c2954007030310040c0c4601d0504000c0e00451007000250080790055803841c02c01e174481a00900000c0c0c00036030041d5000300440c022260581c4440710020002100c1540c440d00b40c2007450b165400002c498000c0010f00207040e040f440c091052030103032680202143c20b064240180b42009420007080d244a503c501c600d041c000c600c1c2c909 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 154129334 1250 154128084 154128097
    0x81513060c0e0907080a0f090f0b041e0c030b060f0f0d17181219031d0901150201060e0105060a050304080405030f0d0e100806040b0a05120a02040b03030c0a030516020402 75
    0x1101e090300f5040c017003c0e103030442da0010447d0b04840d10b007a900d100050034010b4041c1c0c1c3d840e008081f200d02d40d211810100c030380011414810814003000c4d0105000c205030b51a1500840f405481c900801c0d41d519000e2042001240c0c1d591540048602007031800d528183c060050000e01442e95900700440c10001a0000e40c40240000038890110555802c50710b030a54010861181c024090240b2600035101800b07141c50510008007400550aa0b110313090016000d46504110018018043c95940d40c140703c00003201c00c0c002d00c005508168002c1240d900104409040314805490245041e00c940c030f088031150405070085440c440100f200050070754040100401231000c20002d0500b031030b6010009441c140c40030000d00d0003041c40ba45030150440d00412070681c000001c2e0b601182d8290342d4070020300043c1d500c0d0070036684002450000c0000600024200d41c1007482524100901600401010b60f0f034010001d20305d1450784002c02010001f07201e8000340800740c0d0f40d07081c1680ca49180381e000500303903040b10303 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 154130584 1250 154129334 154129337
    0x40206030a0e07140a150503190f050106051803010501060e010f050702180f071b0213090606091b020303060f0103090f170307090519050405060f19081513060c0e0907 73
    0x144c0e44620245440100000140b00060b0070180130002c44401034804e0000400d8981007604482d0704c52040c0380503401003070b56074030040d508112544c0c480102a0454012060081442e1f1040300e504051b8201485024180c4605880e403640c0b8070204401101c0c41c1840c04c82840401100344003460040c1c40c0c90300c0f041c980104500d1660b0192a100a0104544034001d1500c01000011401e00322030300c04004410200c981c044e02c203c0e0241c2503640405010b401d41d064010714052804200264020303244e030015000c849000e0002503202088082241c1d0781c0001d03220701d54050b14400c15071101d58020380c08043c400b4410501c030303040ea803080d40380c204228a044216254403a40001003100b510b9100c1c640e0f038050702c41160918000d0f8105000744000e81d280703000f03440c043d9980d94082031140d65515804c4402c16001410f0850a0449000501c1004030511904d00e42d4490000140a404034600c402031061031408180315a1542c01e40711103000e024548034a50034000884040b2410b80c403448041485180f03107 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 154131834 1250 154130584 154130609
    0x71101050103050d0e0109033f020f01061a04170f030706150504060602031608040b0408030c0c04060b030f0a110304030f11030c07061d0a080a030206060d0803040206030a0e07 77
    0x80307200074100400a090946c10015221400c0c000564400d80701c502c114a01211454022031025142c000a515626410103520ba815040c001d11a030011340c4903103560700c5000034011551745038504c01c0c06032600f03507103520700c1ca105100602c002c500c0c00c145496124100c1c030032181c406840450060440e0722500b01a103865445a50b600e900104003c4190014281036070100880791070000d000391a4010080b5242c80342c081d20710300e5001c1c0704510050310050144200c1072036486540c0d01d1059640d41c02080704404034055142019154a407a201303980c01c8172010000640b65964803424144040c2d4004c0a451001341d40e43d81d05003510700c0410166100d24400d46440c0400c64218401800340c50044907118203070381c000c0181d92070f42e42c07004c50b40c802182c1c0075041040300c1d0041012182d07683c0158000040d0031889051000802581c0081c208280c00c1c0a5000d4a500e41c0b9008280508011005000b40025108001050042c10030308000c1d6072105000311700080300b5288000c1a4240010356006040c880032 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 154133084 1250 154131834 154131853
    0x90f0f090203041a04030f080c042409080d0e181005060c0304120b0414010605150915030406090308011e051002010f0501030c09060b03150103091707060501180c1707110105010305 79
    0x20230800d42c0da0805003000704103060a01d00041e90030845d100b0796403a901d4080b41408800b03882c0c000c2c50f40c3c50203450803a013643c0c030384800c44500030504600c1c481154414803d58010203109070314404c05601a41d64000c60500480c100340c00d00c02d4644c0800c0d84c0003002e01c010040003401e449450b860901702c41c45107048092600741810400745e4502e05c0c0442140b0750349802e20821007503440300001c030790284450a00ca030300c030088440012040f060f0001c156403c503100004000c204042684840c1045119031181d65150f601e590402c04100100201071903034800f013650510035441d100003194803010403403002144168500e00440291542031f4030450710498446005e200c9480345003c1e0002405403004c1071806c0d45021800a01242c281c5d429550625546a11080602120072010030303003d620030728a941d8815061600310014242441411400d100540c00f409000b807160003080180d403084e5445400d280c8814000b11f0003083c01401c103500384514188003042114081c010b03e40254000d40c0070348200c0c117 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 154134334 1250 154133084 154133087
    0x21c030903120e010908060708010e1018050405010c081513060801150302030f0d080408070302031e0322201201060602010f0b0103060806180c12010c090f0f090203041a04030f 77
    0x1707201c2d00050400c0e0041c0781001039207544013400604490040020207466140d1030829942c2c800240c0116200c429661300007050a00c058010a018900c41c000030031440220240c21100323024103a407043d00244240001310b00510b40f00d00403d0130318020a4000a2007641c03041010b003110f21100c02c0c20305101c0b00640820a503c2d081c400c4488041004015000501070b180c0001c00d510f100a20003404001c01080074408c0c98800c000b5a440d550440d210503105503460103414101d80c104440451141c022400e03402240545050f503410078651100241d00e00041c442d12441603106940102d54200341580c5821840d2142406131030300500460f000010034400e0040080d01b0348082000b807a06050408000f040302100000381e5540c4010a110000cc58000b950406400d103036990300000c1e40088003502502c086441940482e41890305074880c2c00c201d40e40e4640342007038401e00380300d42d4080d0040010100f082c14080d800859105200d0003020400c0f640080c01903003070080c161000d60002d100200b80d00c1405 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 154135584 1250 154134334 154134347
    0x7030306090c020f160b09061b12040312050a08040305030406090819030b030a050a020123040e07080901091203090305040b03010e010503070f05090610030b0909010c020d0c021c030903120e01 84
    0x3907205d200010b030083d04048900b42c06104000381c260080c034000880084402088681000078040c1c0c909458020004440300c0300c079a04140016200041120a19404035000e00102c0307482e2085500d851034190760302c0d14240e81a400040c02650f419841e03400745070000d00c000004020303d04e450b90105045240040d4000e08456502c012a4020341c411101c0101040c00003800c051a1542482c00c6124802d05400382a064021008450b01d40c10340440d0104000c11100c2013a40300c0ca1207079942c041e5503030b00c440b02c060a99607181c1c000780100c440e00002d0b43c0c0442c441d402004460b07029046c118501643c50255001c0e55000340d104a034440c81d284014007036407800b03200c048010b20a2024804107d0300703102c00911318081c041c29144c8510307601011180c2c000c0c025003008804102c0101321000c0740c84c080c004503011b00391a01c41301c0014000c41e15000d100900461100d1461038004d0085046615100000c940420b882841981400701e210b4000000860040036404000f446942c0c44045000660025110 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 154136690 1106 154135584 154135603
    0x10050408030a05090f0402130e060f0d2904030f0e01030e0d0806010306060c050304180b0306071107060f0e04050a0f060806012103120207030306090c020f 68
    0x10b900300c40900504d120030b480d402c440d550100100800c80c8221841d4240d01c2c0d9001500380f0583c42d80b45c0c00b241c0d11000203014508185100b400045081c5110300c1c003220300c01404040c43c80074000f00c8030f0300c550888a00b503a070f442c0c50819980141841d6458001641006040400703034856038483d0300b245214020041c04d841111443c450001c3c10840d04680140c003190920360f0000d0003500c01d421440101d904600514101802d1440e105186070304008400019034482c03201601d20f40d410b00000d4040c1201d074803208030850150890a0401071030740d00c403900b4084c290055204075034000c489400003c4003107400103040e964030307400b900003001402e500f8558035143c800081042000014054140c860400c5107282d21840076018480001c100d143c0100040d00083c007906100110b60042c2ca0050306c40c0c100031071455100c1860000700e07480051590700590000341c0072604448140b240003003 = true := by decide +kernel

theorem cover : BRFrame.Cov 153956834 154136690 := by
  have h0 := BRFrame.cov_init 153956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 153956834 ≤ n) (h2 : n < 154136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
