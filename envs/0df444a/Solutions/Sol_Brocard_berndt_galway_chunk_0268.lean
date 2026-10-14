-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0268
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:52:01.215285+00:00
-- url     : https://prove2.me/submissions/46c8580b-349c-4030-ba24-3e358948b1d1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 48021586 ≤ n < 48201442 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 48022836 1250 48021586 48021601
    0x303060308040f06110c100e0a05180601080106050309030703030b061b01020406110109020f01030c05040801020a080a0b010203031303051605030d0905010e030319050406110d0f05010603140c130806 87
    0x440c3c40a684480d141c1c0e1240031140e40c4055640c1d90f50640c442d80c0580341c81440c40344c00d407003054036011081000d80441d6005031580e00040c1100403c1410903100141402000615039012685070f004002c14208940b0b1030405100581d12445000c00c0034090644510001e01140c441d0720495420703401c030000c003031022100100068080e41c80383c4104400540c01c244010750240c03061241000c843d50050901c05101d05800c0150060204600c000c4284a818480021040828001041d244a20740c1d03a5108030300c0c2c01172031141218030750500e040c1154801e100f00032140b00c07000028140d40d0381508103951100e948540c174040981541c00b00420301d010208500e100306800b030300205982803043c0c000784041c048603070750190380c0d000480b070a6240c5088400b00000505880c0d01c03668000d8000c1c200424082c265540300740d8a1740c00310407502d45480c0d4500d441115641e5070b2007a42c0c0034011516080c4000b40b5061047c450814002c6c222640c6da807030008500048a1040303030014002d011440980c0c200303290a03503 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 48024086 1250 48022836 48022859
    0x6020d050a1b020307110301020c0313030209070305191d0118111f0e030a020402030103080319051303200d0203031603050c03160c050115081603050613030306030804 73
    0x100c40318001410716090b500e42c2d5101034030051041110303034011800c1445a031500082d001ca81c43c80395401d075600b003000304902101400117010802408003210324052940c81800119200209082c04061502051028400310124805000f40750410041284c20804c0d00840e803440c0300c1400044150f00e0030800c490f40c111140c040c141020300401091800310403800612a8950001d19055103041b5400c1080d04224003c0100c040b0071000902203802041880e17001c07404980c000e80050b82d031101c002c010801e003001b00000032841c2d4060042e0500c01c03030034890521240c80c20868401400e01c0268484000303162910362182c0e504d03503401070845e040200794000c0a5103da10a4034030040e84809000380403681d0303001b40502d60162400c0120a4a16a5030341481c010b07880c0e440d1a007204104541e40c103000420401d004440f80340a00c11580600c044c900410603103462100307008800399000f18001000400e5011590035404500b083c0d07040c0e806121450300b02c004284541004000310004100810303200c1080 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 48025336 1250 48024086 48024091
    0x6020717130314011a1519030605030c0301060501120902010e060307030b090f2208130b030106031a0d0201081003170304020103050112051e07090513050d080f1308040306020d05 78
    0x10101e4440300c103000c1e48400d00340e61840d010342011014190200129040c920360741c4082d603c6e810031080c18180c4c030000001512040e0104100081d0310341e8802c1c00149414060842d502c0300440c001c1040a1500002900390f50040d40c1103e100c076a121500da0070341e4050328044540f01801000e2070b9684c03511100c007600401d440502c440c06024600005889540303d042c1c540e026501c2c905440300c4200c000c0410700b8070154034003402c0320446001d1240d10b421101c0c1d15003450142070b40003482501c2e9030500c04000c0c100c507144d005485851703001c92400b0310b05407904005d400440c1d4084c40c09459640c0d9600008500358069400100760061101043c03c2905c586c80145014602c01d903428002a640c0364481c11182242d804042c02d5600310b8040d08500f00119040e02d080c0b00030403401d85150590f202c01e81c0085072000c580501e0701005020fa60400c001d0103211224a03400725003011001e5052160184c016404005d01c08071000407000f25200c00c3c0400d070381c2954011070f40a07e0541d610580090b8400150809 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 48026586 1250 48025336 48025343
    0x2070f030e090f0c0f090301021b1c0806060703020102120103080904110304080307121d0601030b0907060f030e03090d0f050705041e020d0605090403050a0908010216060207171303 79
    0x40495000581c6480c840c410b0050715021500c06164132015140780b01607100c211001074555003000708280d992420300141503240355908202c2c032980a490b03841400c0ca02e00500304800594545480c00c40c864104000d150070441c20350704103846103050701e0180e00900c207840840a401c00754900010130400c50b0720080042600503a414000141072020301c5625000c02d8900501181d418000512080c4c071802080c0182010720001281c50300c200c4460344060250b04482d40d4403904210014020b1240e21910f06401c500c1d510018040a0300d40f0000900c000210440030042645980301d418050ba010015100b074400e00804504503d05a03150120b03582c0a0107004807810b0003000c07000501c5180c00e01c950880001c00703100e81c9022040001d480802980103458a141180e41c40d80041403640341e111181e4480c0b4440e840d080c0d03070381c0c180040203000326180354410b02c075682c010000d8801c0c81e81d01d40000801c2c2907204101503203039160707450181104088e800d4003001c4080040b405105545400c01200d00f128007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 48027836 1250 48026586 48026597
    0x10b0111030a1d2e03090b0a0504110913110f0d0210030e070f060f140a0c0f0501110304051c02030702060d18030e010311130308090109090c0305070305060d020915040204080102070f03 81
    0x10180303065013a90350b02503007d01640c0310071000450410f603030b4000c07682c000d1180c081040711041305400510044005e0702e07410704a0084103902800c01005200c000e265080c11206604840d01507000904a812070200c001c0c0907120300100c0c0510b0320302a4010a04c3c0681403010340700e505031642e8101400710b0151190900244001050140d110302501c51008108240c1c0c03c580c0c54038901c010141c8170b0400a20f022078543d00a0052840420021301c1680c45048045007042c4d03807400c150030300078139200c0d044ca2281e04c5611504103400c1d45a07000412500101d0341520120f0325064411202401403a400500041880021400701c0406a1001902d0016007090b241049101c45454500907103004410400305d032412816400d02c081046030015010400c0140342141c0096100c0c1e4840082c1c6072400c3c0210082703a1140180a00650140107541e8442c03070640b04060300059a0f00000c14820003d4a1f41008201c84580501c0c10b4031640c0440d00070b05a680300a6664440a00e000c03041d5080e03080c0180e00042 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 48029086 1250 48027836 48027919
    0x40303090c051008010e1b04080c010e060a0507060c03090b0f0a050705090307090f020408070f0302090711150a0b060406020a051207030c0809010207120b0603010b0111030a1d 77
    0x5000c02c242c1d00320031a6544c802c20560b003003025801c03090320040e00c0345d007101202800782040030000d00000d002904201000c1c02003800340e40000340403035940000c90703485080705001c8200c1c1c0552003029504080c0d00004007240002003445c090f001410705c3c01c1c02800e142030500c204900f507401c594899000e0f60303c91008025503a0f462404586601a05c200540d00d43c100c0c1c901040786000d240c114800040b011840145010ba0721205181f90082e5648006082c00b0000e41c1001945881100c0a92040c4541450f40003880340f4101240c40f04c6507130003106010201600801c0b24a90140c3c01503080f8240a010981c0d81d90301e50310045d40e54802c2e4902160103110b207040300c1a40d4022101950789141d80340c0c0320b941b449807083c5c0d64060590050000b00d070440c41420b0f030008603441052806503086005204208903810100141425101c09107801c5d8140b12032100c0c2c3d10803003d800030464a4010b00e5141c55901d402d580500d1840c00010b080743d4681c8000c45598207944c5e5041e00003045248004100410200e0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 48030336 1250 48029086 48029089
    0xb09030307020c22020316030608060412120b03070605120114030a0803070201140103080406030f11030117071502010213060c0206030f090c03010e01150905040503090607050f010203040303090c05 86
    0xa1004460440c01a00f04800d007009034280100b0f241449400c41d40c2070288004d10381201030882c2c00894071001c20901842d52004032903058480d45018201200c05044146040c3d1504980700041103441e4082080c0c1d000006180542580b0440c2e030a44010265404181e03103e50082650300103005e52144d280c0501c1c000240e2a403c0380070319044650190160800c142c081e00c402c0841d03040200581c055548600c0b803c0001c0d04006500c0c0d001c5c502c507104031500d40b0306041000b400c0350010421082c0c07081ca4550342e904040481d5065a04407110f0042c03405d0200c180c0b500c49030030020280d00a80b5104e03c6011145a4150190060705440709205c12040340c01d07950b810111a03040d036202c0c02030340000040000c0b500c44440410f1465104074008211341551460741d000c0f03821500c0b264401181c42c0d6441c9005001c41d10502c10b05002060349413810b0096007031035207902d9240d11581d91014030076000040c800d81000014400b80301403040040086450746000d007000b5002c1c20085604650094030102c01040b103 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 48031586 1250 48030336 48030343
    0x9060905030406031d0a080307090819061409060c090d08031003110a0e070503070c0816120c020609040c020a17040503010b0409050a03030902010e030304030c0e0c0f0a1b060504030302070b09 84
    0x400051800070865401c051301c520080c3c0d03002404010402050000c04178202d42f04100808016101d0303802c4407044521814202d00716400740649407210740446041c40030b00e501c0003480c190480440060341d640c500717428000030100440e0ba03000401e41c5c03201008001101605d11104011240544400c440c510026810001c6004a6000ea24110b0b481c102c04100300501c03407001707540e001d42c490900c084a5130b459210000d81c0e810500c40540c95085441c000d804024120100c410300c400355041910219240c0c0d40040d070300f8007a414005004075a113040d8102c0c0f10b0320810040204581000c0c9260a051448400d880154414001c40c0d0183d8207004911680e41068800c0d2000d4603040005840341a245a404030042d041e02e01060b0304008019190516a980520040c002148149881d00d00305140c081d840300e508900811103c0740354014007014200024480803a00c0d00101482c24000301d5046481440c42d60b01c21910140409140008000425415a0042c4100b501840410705c0d01d40d110780d8483e80c0c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 48032836 1250 48031586 48031631
    0x6060a06020c090403031107140a030e030606100804170a020a0309150c110a0b1803070e0103050d0f030204090f0b1804050d2d020105040201110106030803060f040906090503040603 79
    0xf00300284000240c08203202c5c0d48900c0360074155031103013450015603407503110320100005c0707001601d500a08030790420140c010074040f030045000e801401c01c03464181d000542d488107554800307060020180c0011304200a0013591800c1005120380c882d1a841c5680009580d007041c05800c40100700420380120b030100c1d420904000d02c103210f540d010401c0b0030350750b1005d81211940e442507400000c030040204500400c0406088030300315a0041000110707c0da0101491700141c0d0340600d0303440780c40c0401803003c1603003c20441000140ca045c030f03170100e00104204030020704c100c1e40030700012803800c03081459590564101e180b90308002c407441400366025800e070f0015a42c1c2558014040d43c0b00d00030b152a190b010358400010b440c18030032020525040740c07100c401041c0140101c540145d640700c041004543e0070201002c20429203000030000b141c2903917960b00319840041c3c00300e81310311315030001c03030a15039500e8114044007039001c2400d01100550b461304540c2c0b50000d00522001c2401c00106100111101d5003202 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 48034086 1250 48032836 48032839
    0xf06032f030c100309050a1104060b070803040f020a1701020304030908032119060b07170304200d061a0a1e03080702060c03030705040305010f0501030b1512010c0206060a06020c 78
    0xc41e18282c508122003500282900c2003032540715400701010690034458004518010303203291a1403195a8100b10450350705170030803801284c050060a010a941d42d043d00c0c0c6c4590701546190300d03002c0500015031f2038010b551204048624034800c8600424064010b1405a032003034a80c64401c0b0303180e0043d075440e4011002820400c1400b644c00700007942048080940080001c000ca00c1c54103807502e88002524841d8004110b00900002c1910030405c00030300321001807203900c5231507086003825901c1c0441c90480c000700b8017000010100140751a070700d070045403080541c4520200182030303201c1c2e03000301843c611005861142900400004142000c1248071034041c031210022503d15045036940d40480c1c000503020f907041324040c0304400c0b00441c100011800b81c1440d0315070356169403031803500e80e0944840301d8144443c00c0c28a401080041e05409032190021140412144601c0000004c101c66501d9001c101c2074541c200030710400c840750086415402003006450b400462601c2720001c0ea510300f400f0311102d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 48035336 1250 48034086 48034093
    0xb03011406010e220e0c0f0604060801090c091715070206060604090203090304030f081c09020a0302010e011206090c120e0607050c0c060706020324100e040f06032f03 73
    0x1142e140c07900d0021101c0081d91044c607410440700d40e050101c2107035179410140c0816800300402c807641c0c3c035103103100c1d210011088030154070700713400e04070024030105041c031490a030180c81e01034000c28140540152006030846030910198488a000d1071a03480d0180d440180400d80031002251440c0d1020580070700c90903000e840700d850649000100d100070340c0010f000412900082c44044001940a1400144280a482c0c11511003c03000308040035202440341240c4041d00d00b000300b8005880d4416020112502401c03c106c10050140050381c080d00207201c110b01c02854800085103240349a40440030303044031a1381d0710614400b00300c0742008450b411854880c2c254000b400003049544120001c0900c02019019500720300e40d0100451080e421804048482940100412003081e481c00d0084a1080a603002c0b01d6000b856000030481c1d50b000e5007110020421102682661919542c10178a40c0b65032500d0b04000507692814464180c2914006020a0510362003100d5100c00d1a10240c0c100400700030080e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 48036586 1250 48035336 48035357
    0x13090b0d051b03010b0306091608011b050c03090405010308040f0603020c280506070305160e0f0402090604121101080f0103030e01050d0e01020c010f1107170f070f060b0301140601 79
    0x807144800d10480b141a8190340340d8a118100384c03002c1c0000f60046008200800c1018000c08158000084a4201d660700d41e00d4040b0511024a160380741c8410501c1e070b0b09090750741e101510001c0c0e0541c81403450301a0042e00701030001040049a03401402114090600325442545610048040e40b04039140301300c55600029450020004c8420a440b01c1c02c0240b08401042c51241daa10b030610004840c5200401e6480302040a81c500f511010100341c00c0d5840d0224848041c0c1e00010743d9203061401c940c4c021540400c1d070410301c1d100d140c100d40140550550309135060480740741c14014403100b00090b03400100250003103802c04c00240c020030b059983c580c0b0350070406116a001120640c100702505204d05032242e032881a03400080c80106030150740680003142601002c0300c8a03090329000c03024170715130303401c1000351801150414564600d030200480245907105404d100b042d080e4040c80d413015181520380701000b810052158401a007000f4160b00034400013401480140034031204035501030205170341845 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 48037836 1250 48036586 48036613
    0x605070807060e0106080f1501060c03050a0807020f0109060207061103011a0304061d011b02030a0512091203130b0a09150e010f05010b04051306060509130e0313090b0d05 75
    0x410200040c042000040490741d0300e071b40a24124a00d52400003681104a0440d404290290014094005802c100e42e202071542d50041c051702c1800909402c1100324404a6a0207209010038104695800b009110715900d40c1010402075014040031200076280c8808282c0540f070481c00eaa040340c0080303080d01c250380039070240340006600c003c00440d8a1580d0b4050090148031121461074108046000000c0155005000c08051070071105120255031080c0580001d1a500200b1142e000c050f10904d6820364031408100d5144c141600311010010102004120940390700d58140d4458034025000303251951250566901100e90b200c8001d4400d0003000346e00310007a40b0700d0300604800c20302d98000040013040c980c0180704464080c0c01802c2c000c040060100701c0c42c5880310181d01c04002203030080108034580034026159205907103155018000031b4080010f20245580080303070301c015102c2920703511165002c90280b105924000d00710101e02d05031411109060000d0503212040e4000c2c0144100c0840b40c2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 48039086 1250 48037836 48037841
    0x3020d0f052104090f0b0a1703040305120913020c06010504090f0c0311030f0303010503070e1306020d0603030311071112121b0c1503010509070311071a01060507080706 74
    0xa000d40715441080010701e5600d4100c1c031002d00584030900d046844034105110303801550300c0c044005032405d003440a1240c0e1903946032403480c02c41c0d00e04041840240580e0712558118002d41e031003e4000d015024441c1941d040400c01000c4c1d41c3c40844141103581005000c05049003c3c07034000700000da002a005200320b080660001181e0b0f806128403030241d030303441c0d942c04218545c540c104642d003070242c03001d00079141001c114640358407000314003650440d03040c2030119036910b14920600e0340c440e8858022401d00189400040c6211350010004d56841e405107a484011700f26038803040340003d04e85080328512600c440c060f103d8a90b030091101107044515001c201402d0f0340b5060b800018002d141480186000001c01480c003c13002c550040919950301c504a07007400c060b11482800748003031689109001c1d03548002c49056687c01ca503580c00d19124058210010543c2c1c2a00100c1054002580300c1030103081e100014840c43c54220b090300301e81c1c8840044a00f806258401052110144682030008050b0f8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 48040336 1250 48039086 48039113
    0x1406011a0922090320031e0705061503070e09031801030f0608070e0603031201031401022a010501060e060904091a01030b0114010305060f130b060a030e0106050a03020d 74
    0x30502c1c41a41c040c0d0b103000d40c014001045812185982e107030b10f64105038002c0b0b0051550403000140e000001664044070f500c0340304a100e2203582c040b0a850719261a107140080c4d035000340e04a021214075144c881810f44040d07003c1991544240300301000064a4100c00c100c00344110450000340d03003000200d4490100c501e15000c2d610b07050589980080c4503041d241c0c82035030000c091310401003c09920700074458017030000c017500c00c0340a038204100d482114601030a4250440ba03000d040070110781c0720501203e00a001d20854483c24500055500038210f10702d240c0c3c0e910030826200208000d9907200c03c00d941052030b500400340c0140080c4038032000c915055000c002118000d00907000c0c07411140040c0c40c040f0109800c00c5900400c2a401031160302d0070041810454802820100541c0c01c120001800001a142e2120312405841100c41d03401c2d4100c2e08a0b90814402910098036418501400b8014220020b02c5602940c607201f00081c10746480305549013200d8014241039030f410150f8403403a0460505 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 48041586 1250 48040336 48040339
    0xf061b07090e010f1104060f0507030e0d030504061205090717010e030a050c1002090f0409020402090414070318120302130b030403090905071706060a090305031201031406011a09 78
    0x54031400140448103000751002c5400030ba00000f030701c0c0100f00500d01140c48448090070b070f01000340000d010701900700b01e08000208860138940e40300c4003246821125901d410941ca0303003102610158a0800d80c0000107001541c0c40360300c3c3e100702071f44041202e004441080721022810b60200d50b08004030300401c0402401c0031204400031a01490010b101840c550201101000003807001501c20340c440700a101300d140e4442454003d40c949600100040c42ea400c00c0c0d16414412079a4115010441d40c0360303411100c2050000c7e000b4000ea891680150640c1d010840b003c0300403900308080400b01c000750305d140f0b5801550010400341b0f2002c405a0442c025048902c050280644038880401c01e0f221900103107100b94826954003a0075410300180f001990000340485050140070180b030580900328031034441c5e100d801682c141d034481d0784009040b51042c15503800600709010001e045185001070404e541e050783c0c014401c444500841303a00c56030340c51509201780c0b654041c84115010a01403a1001042036070310 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 48042836 1250 48041586 48041593
    0x31503083613050903210601170103031211210601110106051c03110f0601030c0b12060d08040f030b090c060304051005060a030c1710020a0509060306040609020c070806060f061b 78
    0x2160000a40e0441010114074401006d5080040e02e603031000d800403e2500014181000b075145a501904812140c0e030038a10054840400a00d07045030344050380d61030101544042101e0401d0710030110542c1083e80c10718001440c02d2200c03410b8407814003446040750380152424070b00c4010403203d0061007100c84002c0302008502c20035464014420408081c00803c607502500007945140740000e48000e0940c0709412030391040c044140850007107032495034407220039111090841524034148000748115006003000d141b16480c040140105048814400ea010750116021104a10104142030100b100e0042495000300c0004502c03071200c0c1c116541208014000d1455070b9100d44c0e1f162401e1409412044410002d81316401202004211410031002d1700c1c4c1c011481d1043d404001480c6204003c004d500400c2c000020606644440d44694028141c820045486045d80c9240c90340743c004510440c000ca1040c1c0010840b54a0520700802d50316800804d074901d4190320b240c01500c1c4110b04017602c200c901 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 48044086 1250 48042836 48042847
    0x10837020d020309100b04061505090109030803070906021e030301031704120602030a0c0804020603010b0a050c0a11030d03150306090f02030609060105010318080a031503083613050903 81
    0x140600240d030042ea064006001d0f17480c500903080301140c3c540b0428500c0742d030402200304603851043e139040c5591203040c94050358818400c00144c9484020390b100422000c400010400d04640c0071500b00181d800300e034269210f200340202d954444540822509005030420030041001a040c0e80a1007481984150401d060035a079550315064501e8011007550007980000402007481640c0c840d0340c0b003c065070300781603500d4141a000f00f44980014083c89074911030000e00800c50900800035a01c807284014103c6614103064540f0286207008110814064483d460b082ca0031207000e809510101d9601c50800b00c1102e183d500c80c0340142040e44419503070341c0f03402c0c5040e4001d601c0620007548100319003401401154501000103040f40d0b80c0d100d0910050340015440d40003c0c29200480380481c44507d00441c1c00b91200c6031130359984803d88c1c00107060000015454a00b604400040f07012407a060300c803082ca0301c03841403030480f4107410600b541b58008411084d103550703030029030710031034000502008907070030036 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 48045336 1250 48044086 48044107
    0xf060f0903050f0102030601080105030609150916030c081507050a1d0402070606050a1401140703140307170a020c0c090c09120609010b01392001083702 67
    0x4404543c0d0070483c0d4001017080283d5070059102801040140c0060000340740940380e0f240c0702d4032841d0490100320b0195001c43c001e440104104101d01c5000c44c0d0080e0b90f19660710340300542075040c1c4200c5000d40904070b0907201a030451072145204a20940b540c0746402610700080300d5154001c001c05800035074041001685031a0341c40608100761203031100007211410802000340715612980120b600782480003584c086c0381d034007156440d004000d10350b40030303280c04540c0b405940101c14290310414200c00802008110750340000240091b102c0c0d1003810030a9102d0441100076446036048a0500380d004400c071112609149070b6042c0d004001c02015070814041400203140d240c0c1c41d0010300450b6002005101d00e00d0028800c1d4401002c1c242003c520300c0b6410901d00c42840d0620360681207201c90610044001e0040a20181840d40e00c0b02c0d20b00d21941514007490820a40d914a80e400a10003600041c070048004501001c030070648400100d14050740c1c90303030244400c006141c503010541c080c044c02004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 48046586 1250 48045336 48045343
    0x209100503070903080a2304050a03140c030607020a0b060904020d120e030d02030d05010b13051504090c03020d0c170c1602130b0118050609090402040b090103030206100501090f060f090305 83
    0x41c04000d41d142d80b440983e00c06c0c0422100c0740d8007c40d580b07414080104120b240d4400c04003004699201000c0344e14516607601840c1030100420f91541c043c007414080040241c0c5c0800e50302007043c4102c9030014036485800a010100c00c00322002074200c200e281c1c000f030118564019000141c0e180345000f201e018240800300e81000540b201d0303800545c0c00800c2d561101c0300c0a01640340544030400065050025000d60ac0e4000c501d544a620b00600e00400b00510ba41c02c101c04403801f81c089407809015540c2d540d840240258082003942c0e50f1545056250300078644505c1e02240301d10040c07040700d0200c1c0c950102c007009640c0540340c2c1d40c0002c506a220708005807035a40c0c4c03104074290340003000034400030080c001400101075200068400d020311402440196030310000d80d84240002d9034070683c0c590381d03407000c00c0c010000781465a5020080300c0c000020181d000030001d03c07805000380c0d01015150340310010b407600481801000d07189500301c5814040c0b14480c102c0724400c43ca2616088024a40e0794540c18117 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 48047836 1250 48046586 48046597
    0x90a0609090e030309060c0c07030f150606050901020a11030106030b09010906060806010b0d05060d0803100f1e030605060d080301031104110405030a060b010e030706020f06060301020910050307090308 88
    0x4100094810410010244118103000070302d00040e52543c9402d012081e121140241000c115400200b030090300707104100200c1c0c002c1c55215091103401221f82c184680d00b0300201c500360002608140d0040b80c00e0b84130301c058a0f42d00e181a001402c900320b450307440381e96032001c01c0000d58256584010001c04603074420f1800380240038542c00014070403007905000080d6102c0d60001416035210b0030041140f01d0301d000440d0b00e030013141040019580c80b12000280003509044c1c024280c50004803d000c0359810500001d8115000d03801030401152b40d841e500c5594602040c03440003080051319080010a409802c86580f010f002400300600304000c1e81c611328903070000c1c1c00035940f02c0754103100311102d800c062041c000254011040541040e26060000e0755410680728014081c50301c80262508590141005030144200101940c0303c5544030b0308020768400110001034030511501c40810b0440c10706100b12148124060549540c0700c80c8444140d80d15131010302281c040001145000002c590104003500 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 48049086 1250 48047836 48047849
    0x103020f0a0305032b2d060308030a050a14070f09150507170c0d170f040804060e12030a032702030d050715020a030c0f0f0e100302132c0106050d0f02090a 68
    0x800d4101b00038018503041d140000c3c183c06617142242c240042000c07101038980c04168401d000c078160341c2d03000c080b0000c1c0048020070340c80e29840340184130105810400e0480040565500e81a031150346269480340c10341c044032084c0100d03000308804008100b582140401c948545046149009000c0c400c503807529101e92401000200004003801644c07482040c1190000421550120030303080035161280d081c03160b0301c0780d1024030006000ca200340e5102c0d60045d5008d42c4c120025079031106a0342a000c0d01901e0705c200301c1188941110360786601a185904400d010607005030007499030000488090b82d00d40d018400680345000880072802c50030400740010301c154912603030045618544850060b2800c90201d40400910840300c0c0c40c186c12079032100c2c4414010307200712600c600c00c0800b910141c0007407003045401c400004411101140e24142080441c0d2105502c1c030b014402d6020502030152030701028054800011000c015042d1050f0164101c0c445428464100624004891000030041c240395400b20 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 48050336 1250 48049086 48049121
    0x160b0703020c060a1709010e0309060c010b0a0306020a0207051504050405040c09050a0f05150306060f12070f0e1b090405041e06051602010614060a05130e0103020f0a0305032b 77
    0x4038101e503281180c018010400074000c231420b03071003161707224015541d5403030140001050303207072047ea030035086110644005000701d400191203041c280b010b036104c00e03420790140c0708400d0001041d0030031a00411103184051042401c05041c4001c01c4042c04010b8000e85011041090100c1c0d100c4083c07060301d0241400d0240081d0f2000011a8841a11070090a002003945031546903111501d0100303503640d02403000c9400d9072031002400c1c000f50382c0d28845121103040d8480c1700008907000c409080c0c0c0f10103541c02001242c02d2503480c51807262482011002c100d2080409100c001e8a9051680185801500c24020445243d0030481110094aa00c40e400da40450700e48041c8922036140003071803c0860340c00d1000344481d9080881c61903c050547d07215601443c80004c684454611a000780c91101d0000917000c49480e5071fa4000342210b040c01c6c0416482284850424a0b0710714000f110709044982c400091400c180c1e022007160b40102d025681d503100c5200500100880c41203600c2070030300c1d00500d407111 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 48051586 1250 48050336 48050357
    0x6280306080d09031509060e01020a0503010f050907020307080a0e0607060209040501090605060403080c01020c0303090a050c010305101214010c02071a04030b0609091903050901020d02160b0703020c060a 89
    0x1503803402d410040e450061012003034050012030042c96600710f03802c1d0035120109040c0840e290141c001c042c40c01602e24507502c08141d00c0c041d01e51000003141218030300c2010110392515842002081c00058882c00b0250b40200050000608403070003406881400b4185018180640c00104005a001d00802c6405d190300080403801803400e40700e2207002d4000340c07204001c4241480b01240c6180b00d81d00003d0121031000c15041040c09094045581140c1d40743e05817500c0341000040c541c0c0d24a6900c1040300c590081d001d42c0045944240300e558868a041201d500380341c0d01c2c0c4560380000d01c0001031305440541903207103a0f0841c441c0074003400a10740155030040103a5450440c031120107225030070020019070010081000400c40a6040940100e0229400c200d162503000c542da1800c08200640c10301140724220786030605800401400b8040001c2e001d481c0f00112640c2c003244c81c0c4410040c2083c4015680b0418800656604064860a81303e40104c41c100d40c4114001381c010b8000c910104006884c40c0603 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 48052836 1250 48051586 48051599
    0x3120403060e070303090611011104080105040201020d05071208091e0d110f03070305030c12010602070510030e060705030a020f032a0c0703030e1305070e1c030e06280306 75
    0x2444090b2214034010300119410b55800401503070041c4900c404011514103134580001c2c080d800103103035803000b050f540e0780c80f50b5a082d01c90203800112405d030302602540481510003401030b0222003100d6071080d00c00ca490303903084070161740244d0050004d02280c410244a201d04102c0d5028071420b40403004000c113042001d07514010211030544450429a400407000444180000070588500c3c6500d400e0ac80e0b100c2d0380d01202000795001e40b262164440003c03400000c0d81c940c001c540346003680c800383c0d9502c612000020050b0162500035011884a6005400165140d8400e6002e543c01400c2800090300d0150428035800340394201381c41200d016040c41154802a20b862194015001c60041d0210700b000135500c5181d0300d42c0e11910000c3d003400300c0c164900550b40c2c0d40250b02184070804840c2002282080700c001400100000c03035150080101a20076542c0e00180c03540ca2108950580e203070500d0b0a81e10742030243c00e4024a1038104088a002d110030001a680901c003c0c0c1c088041c3d8000420758036020303 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 48054086 1250 48052836 48052841
    0x1005220302040c0e0307030605060609060409051e04020906040c120228020f1902040204090903032004151409030a050f160608060409050a0618060608030f03160e0312040306 76
    0x95000c248440d000703200c4d26580307011544c081101d422003000a4156100030210f0014410245000e910800004000c20003010302c1e0f0005015111801c0400c0000b0105d03a949400c224050742d001e5441803c2c400080c0440c039003504142d030400b959143c800c03501780440420000341d1700104030401000310070080b010300304182e01700c1a2481001c548001c05441c10703401051619045844249510040750802410954a0350b0701101c000746090401000f46040c10304000b8000c103111421040c1441511208074203010b01c00e429a01500c2030311140c4032124851490684035200103602d090403024052020004c1c954090100040d91401880500200e03030003600c4190900000c800366a01314914408103200f080d40c03040b01c49900c2403050720001002c12207410014036040c0c031310302d00600032414020b28408a240501004000600c20344080c015a622418990345a008228108960800501c0069003046038401c0e4480304009508080b04454040c1c0301081c2042040703401c4a42c54000028100104074152 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 48055336 1250 48054086 48054101
    0x9080d1d0c010e0907170703061806051c0c08030a0215090304060804080304080705100b10030207112809050f0105090403020a061d06040f0201020601050303040e0105100522030204 79
    0x5001e041d14203102000a000080f08403a00740c010070301c010018600d9805036044035940114142c0c490308903d402600140909014000c4428495291002d032092084c58085d400a03a030004144452120044c070141c44030001c845815a51100c49440010b64000e090000348180c00040c0c0c064081c032002c000302405800000382442e012940200020030090760320554441e000b07540310390701030381d40d4440e4100320055009a82001d0418001c0300310b4555015059809100b0300c0b44103440c8084034050049007070f0100c4c01021001b4020600060080c1d00524100128281101c0000203080c41e410216180c0b2a444250b50000b0b56520341e16800d000c200d901c90071a803801803004036045050744c40e160350003d442d00c410301c00080c507607500d6440c8a602848030f0f0410010201d00e030401c4034a00e00c1c16049c00000410582403e07405030184000105043c10702100300c605494003103000c6581d82e441d110522402c01350064046003082800d00ca403e904401e0041250203040e10346140340b990310700f14010002141c011 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 48056586 1250 48055336 48055391
    0x602060c04030c03290907031401060605030a0b04140405060708010b0a17060619090e09010b1f300506040203060112020d0e0d02030d0c02060c0415020109080d 70
    0x14882040003a40c0d19140d40c0550340d00c0544151002c03c040c405d124083d40e0700104944101c2180d08000401c080007070b80b1000c8074003803030380403403102400b0500380e08a034514065400010f00c100001102e8100c180c1141200d410043c1000800214440060440c100c051b01c0481715a0403c2003032100e43ea90140e0700318003400c4a00b940702d2038081c1e82c0b94090003d0601a10003462801b004d40003603415034a8a05880d811003028444c0744142c0b061070380062485810780a140c1e9424803203030108840c00c00500c200d20103030801524182081124152031000b055807401c10030100420b001e0f00d0310301d0510b83c0b40c50343e440d641005200e5403090255403082d03040d0f0300c00520310f42c0294418010085c1680c0d01c241c445003238800350080103039150031203c9420042e00381909140740038807c1c0402d10500560000061691110146081003000000101243c0b01d103030586022a404509000c14040401d0084c001c01140c0c10b00c1c000028040c4540d59800700c6500400d03031314203203103942d010145000c030810268000034164 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 48057836 1250 48056586 48056611
    0x61d0402130f090624030605041b031508060112060e071404140c03070c0f0602030103080a0906031503142b0306120b040b040f14010b0a050d0209010b1e0d020301060206 74
    0x203105d0405200350341d4000c20fa1007002c11075602503c1030b010f540701001418010f00180045200c0c120411500504803403800006440d04400058010a6035a0300c0f098a40d90301c00380049905e441c449140c0d45001c10b1050720a2a910103602c3c4160008000481c000c003d0f21102d018003a54050030041101d03004941d0100346100c00c400c00ca0907240007003c407503000a06090003100a0000c2c200340410002940b0010000c91000002005000c014405044410342564914540d60786030b5400f00c050314442c41804c01d80d00300000781807000550082c103035540030420340c003155170031003031007002d15a2041080114402c1c48a01281c000c185a451b0003030700007034002810300800218541d554000320080082c4054070044071440810700b000030603600d00a03c0fa40120440102a81000b2464001e1000c00030061017446d100400164504000c505501120703002090350409030710b800400070b02548483d406004a2000d40448241440303184050000112107800040e1650b041400183c60043c0190481c0401c0350b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 48059086 1250 48057836 48057839
    0x106050307080106050c070909050618070b030f040303022b06090e0c0d030c020312030f06090f0a09020a0b0403060501030b06091b0a030b1c0308071107061d0402130f0906 75
    0xb0b070011040c5045800c41d00c1c005a031074103125180790400741941c00124203213003000d8243c1d05002c0001081400740d24080c542d816130510018003150340d1045c07403190980e0800c0c00e000140ba9405000c0580380d1007806414050f1508048480601c0d040d000d00c04100c1c1c2c2503280c25050001c0c10301c070744a9a00036104442e81008501c04c41d924090ba140b81131244184074412002c1582e080600c20104400c1940c2d010b81210301e000304004002c00035400856400c0c02c01a18880007411074070741000c401780030780c071510806402c54a030051240040d081c085420383e00302020303990024203400303140d008000079402281d002400c0c1d4198580790012080c00b0b00318a100d004088103003e0b03007650150f441c5104e41c0780d190146648500b2400182d000e0151070b010141e2001002c020390781e07240103030405001814030a036103d44580c1c0d922a0155a6090300d941c1d204620340c8402800c0c044ac90003000860050160903e54280d030254010014040e079028010b5421089030444007080b46400d160341203005003d54030006d00015 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 48060336 1250 48059086 48059101
    0x80303041b050f090408041a041415040608040203070509181c0e090a06260d170c0a0203190201020c060121151d010b03100203010e04030c0312020d060e01060503 71
    0x30401002044e11404200020900308800001101c004100b044209020784c1030100720800150000c0c402e0250b40720304050388a4003458401c000210b010050f20402d0309003402c003103088401000091040b82c0500c102d401c0840c483d5541c2e420944100e80b89401c022201d00a00581410b02c03000d0700c13800c5846030781c812070118a81d4100c4810703220140305440c80482c50b51048000e070050141a480000c1c81060b0280d121300a000034131450b43c2e9500c070b180840303c1036007849004460200a030285154415003100c041210128075a000300000b0b44544116418103080f00c40c05082d82e5241616000984e50026140c2c10070b031020300115006104080d241c0d9440383c00b4003c940c504d00e000c04001001c4511544910b50340c02d1040d400580750080c40c448110142d415611050b00030f041c03288070244644138110300e44007240e0082c001c0381d048e60304030707900da18890b2103540d82560707404e030086012014000e0907401504045060301c00703007018161305500072603401c0c5001010f01d10f1a1040e00302400f044001c10802c0710310b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 48061586 1250 48060336 48060349
    0x8060a0e12030a0b01051e1207180306020d1e02041d01210c0e0405070e0603010c02030403060e0a1a0105090708060f090903090d0309080705010203160f060b060301080303041b05 78
    0x3c990902061000800004031514440e2849050080020710b2030494882400d6016100e16002100c05000d1a00e40384d00030b480300807035404100c0005c2a400b02c00c2c000514640c02801407018549030126140c0301540d8210441c03d02c5520b071861041d0f010608200108400c900281603040301ca101c42101c1d4104050303485249514600d814940f1450400c0e1f20402c0401260f101c01172465282200d405d091501d03256451351044d2043c1200c40c0d100c0000301d02145018810b009107200a034004603c3c2070b19690703d65001d801340e0751200300140510000f51000c13842810f5000e01031401440d500800750304040400407801c2e030261074001003050714820818281c5510020001e400012190000203039500044075184d482151031090700240380318500e00c105070300026424240c1d80d43c1016105041e0b118401240c0c0c9003d07001101c1d0a0b04c0201e441c400100ba80d0a50b05d01d500d600074500030524018400108541d90300c20707407021005500c00801c01083c00010740380380d504100440d40301c1c0002e61030440003402 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 48062836 1250 48061586 48061591
    0x5040f0b070206040512030903011d0a0b0a060803031603050a090f082a0307020f031203190e01020708070303050a0509100b011b060605090a060b03130f060608060a0e1203 75
    0x103102200081d0101503559900a5500a2030004d1602844854100415440340c1003101454069800c040c5884083c0e5526800c0000390b110a200401140c005515280700000010707006141c5996194008184054148021482042803450640140b1f1014a000b0100d031001086409950310784164580051000d1000c03a00c04da401c512800d4840000c0b1f5620001014621083d4642200082803440c00e240040301a01c84c4038002c8560000c4010b100d81410b40344c9403e04c00d88800c4140c1040040d1038021581c0703428480260388480040e80010036040b190880c1e20402040d10b401d003000c12500209a81070103010762142c883e980c1800941070000200d130b580c10480b0300d034081d041d4540d80300059a9115460034011710700040000c50521007603090613001000280511401a0304450004100065034000c070000c50300000d642d2441e550300d42403030340920240007070226400342c2c55600e2180494894003542c07001d08280e00c0944401c1c1070541c0c2e00c200321003926690794101d400102d90800f80000703902c2900e6 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 48064086 1250 48062836 48062849
    0x303090f150e220b040f090807060e07031a16030207030f05160b0406050108150403050a210207050106050a080c0904060203070c14060403020c010908061501181707050105040f 77
    0x10b45900400004841030382121410711030041140300048410415046030b5007003d400c0c2d40402200d50341100100c1034409114019096190420401000440d1a48204c89c43c5903182e090380d080d40d40382e03074a40030303000d0308e402c0309042403101401400002e03601d03040121000e4815003021842d103d5950b0b0040c005c40711740b06441052050100b2074445240d00340c041c1c00112644401444bc0f546024508140140000e010303007032080c401c8074981804081c1600794a4001c0d90152181d5041a00059048039410552000084510005410b00c00c9000c1c1600151140c14071071800810980d0800d02405142483e5030b03c03a01d155070003120421815140c00704502d402c10307084900913a49559440013907812a42d00b420051800c000c00e0362003124404041404c03809148668240c0700200c916000440700b40780b0314013511280f900100b0108480c206050080601c030901030401c500c0d2281a402c40000055641c4e01200100b00d00012543d0305a0b800d000c20405001d0900340316003402d08115000c04600c035a8028034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 48065336 1250 48064086 48064097
    0x50321040213050601200f01020d06080f2a0303090402030c070302010e070b0a08090a0507030804090f1b08040f0c0602010c0207051504051c020a06030b0405090601080c0d030e10090303090f15 84
    0xb1b040b601400040d1110400b00c000b995035104941c00c0c40c00030b02643c4181c03c0c0c0c1d801040c1c60b0b03100c0340401049450300713005451100441d02c80d02c44a401e009013001184503078540f01c00c20024046407210300245100300843c2061507128030b05070602a0a50b00144100c00d42500a9030703003030042d08802d0317064030b05520051400b07050740e0340c0c2c030181180703400d5986201504e6445030a1000003000030103c01042526010041440540010000032082d9085c0d228441003102c814110700d000a44690b5481d07901600900008510b041c6540f21034102003500e402010050b512080d401e5022a01008480010101505c041c144c111103a0a00c81d00c40c092800f85511035030400e001d015914400c21201d044c260703001080040b1460740c420b0082c00412011155501680c1401c000410701e01e0080b0313002c1d040b41c2c0254003906590800004012616017092011014019601e00b0340d10f85846842083c0e5000c00c180c2c5a8120860960401401c0a00258410007400d05041750034011800c3c2c1c10510010740004e400e12 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 48066586 1250 48065336 48065387
    0x90c0306091009050a0503040b19080103120f02150c0a0311030f06010c030207080609030318010903020c060a0302070b010b21070f050f0408010e161a16050321040213050601 76
    0x4d420518030580c080c040c0d210124002c50010221001004040780c0c80d0301990390b10030104016100c1400921010308005203150800036014001c06402c0180070300e920580b0140d0030040c0a0880c880003c2d40c941032581c8010460303180c00f94240c890f1210800400d03c0d401c3c203500d8441c100c0024144014003a50400c00602c82540400d0700810207540075100302801e41e00a0f1504d0714016aa981003110301e000400a40c2c0221020818180300b030f440001c1e0141e024104860b1030300107111090340441040c50415a003044010041100b6400041c06806041301d41640c3d4020310441901d801c0102454803065013030034003406811500a0045030101030541082d81d02c3d40721020140e04580225030026043d9401c2000000700c1c174078081180341004260f0240d401320152100e00140c004801268000000c0b98104480150108944c481254091041c811a81b6065120041d0803503c044000305600505000080c841185010701d0072081c4000d4402040105140000c0005c001e00d406510b0300a030000d014a0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 48067836 1250 48066586 48066593
    0x90a18020408030c06060108070801080a0b1b040b0304050c090112200d050c01020f011b0c020a05100206010905061806010c020301061a120a0b060f0c01060801060905090c0306091009 80
    0x640e0700074525007003a00c1d10b442000341220348071401200ca503400226101d001800e12400707004c12a042c0c030700e00401030284424a90702c00180070f401504544000c00b00c0c80114030302901c00c1000f00050114202499164106841d0851a00644c00400c43c4900101801400010b440404c0302c41c2c003076081003c0484103501c1c00300c020303440b42c81e510400d504801c400d0030724001d200340040e0340d950003d801e0f400c4030403080440c0c2d81c10b401c880d901c6248141100041042c2d1204920802e11460b0860008041160103a0780c0d41c0001c81d6826a503601c04003603008440104524801d600c107407a84824144d8042c0c8031a2807030340601e54800350040c05d031814030003d0301c9440c0a40d10250311100260a940410000c43e510303407400b80001740c11009081c1144985503000881000a9024000d10404080d1180781808496045c8202c103400c07210380205290343c2c6810004805a00340140e01c000c1000f60b800140a0030800076a508000d0b41e5500103009910040a004459400007030210000101600000d81440c2078034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 48069086 1250 48067836 48067841
    0xa0b100902030a0c0f02010504020307060c02011206060201060e0a0207080a1b0203100204150302120c0703140301090902041a03060c090d02120c01080601080f06060304031407030309021203090a18 86
    0xc006900d11440402004500c0e0107551041940098a4503542045040064200e0076a1011100250160000e400410505002d41d220456080c414140624001c2e0807440c500704a503450f600c48801030b03442c0c400400013001c1c81c090803508818000c0c0b055181002540719004184500e981210805c520b10f0300345c1c1c202c9901020701e1501254001c060720000e11240c0c980d480a500b241c042d090035801d03031192094266003e8800c44140e041d40d6000f10b88a90b442d01c1202c85a504086000c2d4103002050b82c10903840106600118040c0c4101103002444be0a103005100c112280d2003426400d56001c40d0515550b980c000910302da01c12088240250390b051440c000c62051822008003c2d045840c0b2108100c030100e011a00b6481c001003070386c44081941da0340c00110359100b02074441e034441c04241c0021030b02c141404002035a0082c040d04007441556180e00e00c084c503552004006500117586d451000045140c2900340c00d004402510095043c1781d1b142000503070b050024801e103440d500103600715814070380307554 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 48070336 1250 48069086 48069089
    0xb0f0606070510050708150f060f1309061410080f060402040f0311040e010203040317060103090b19050921090a0e0106050d060f150c030311131a0c0a0b10 68
    0x944030300c800f0065460015100a0303c0040100e90300c80006500a08101724402d00032100411042c1640c5a146c284013a03503111500040100608000c84c1140c180c50040041c0102104840010110b01c2c2c40c0ca0240c05038100d0300d1080c440c01c243c1242c10041d680c48103240d600300c00503101c0c6803d81e44134880003c0c003d10440d44103200e40f40240b0000000c0c4003000c27800b2080300405175024403504051840103802c0748400c6800a01041103e5031802002c44490b5a80768031600c1170400203050b11180e01c440000f0401100c00c108880355915013002c050340d05000d2141c00042100042100043e03400036000348001d881090303080408040350842c61981d419070400010300c1101602203141d43c40741001030240e4842d00329501200d01300303000090b003c1ea6a21480c000c4a1681d10007040c1e80440d2030040714040e200020641c205622101e800091000d800300600c0030008040600c07442500e840040d5030403088441d41c00720001c505010703007940e1500c049001060345900482d0070b65269140e00110b524a07525 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 48071586 1250 48070336 48070343
    0xe0d0b0a05091c030e060603120a0f05090301060306060518070905010c05010f020c0303010305070b040302090a0b120706020f0c04110d1d120414060307090504020904020409050c1210030b0f060607 86
    0x2400030180042c3c050b03000003444aa628140c80c51641c82c0800c8c1907441c0314200d101c0e01200300412800d81503910450540c5106016841c1003031030100d02600003400e40b41e60f6002a40c6d85607951504016034580103201d18584503003403600300341600e4542c1000d00b240480b0310406041c4281c00c1020030800100707500900c60703a41210021900c681801400745da50b9082404112981d2081901c08a00480e00c00c003620226a402490081c3ca581c03605000405000c03880349642c1c1119a27402220f0400f20103102030400b4210310f9000300102031005228030b02e886821410507004900e411407134030388a0226421508840559900450902e00c20100b0b081034070b05440c3c0d0481d140c040c0c121200d2103900320600502c200da1420101883d036002c10001c00c01d080c4410b444000105281c2841040303a400c054020b8085884010300040c1410760341c0700048203440041320004a2400d00150140d160158034280b5500100302680c2a056182103a460100c000c80142c148850070303040100049441c1d6450040300e442d03542c03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 48072836 1250 48071586 48071623
    0x2d0809030909040b0106080606180112091505040b010f030f020d080702180907211523041716032703050307050105070201052404020403020a080703030e0d0b0a0509 72
    0xf801e0928540801081c010140000c0101022443c0c914201c410781d107100740c0c03c210b80e800c03228600c001550325011b8100d0501490b5103c40c01000032550560728108000680b02000c0b8061a080c600400c3c2d601050f00100b16400e1050000d2001c80d50140100040c80d5050b980d140c40b2000c1802d00c2c880328024040700070b40c404a54450340b004080c402030240e01500241c0c085030104ca46951002038600e00f080b5140c0140007011041c0b0000c25990601600001c4007150002890005692000c0c449d02e9071341c402c0322114514005100400c00d900b0784040e40c3c050144406814100c01180710b4a180150a401408111207100d038079200120035031204d044070401d4103d6590150f9285012a166003020348152015440e000c0061942c50040c05411700c00c008070441201c00d8500011001c2c10642800c1b52503400c43c0d400d110120050304c502c0c00620103800780c00000c0c032049166143c0103101d0380179544c0d00c90065100721100000140c01402c041e400509500010904d80c0e41e00385118640080404101107008 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 48074086 1250 48072836 48072841
    0x7020d11040516020f1b0f0117010b13080106080d0507081309050a0b0a0501090512010e010c021501080a020a0b0304061803031a011803110a0f03030f2d0809030909 72
    0x440000781004030381015020396066074582c484050319508085a1010540386c500c02c1c4001c0c6182c01d00c210302151205040c01c429114103114840c103250030907040f880c402c60000812000403504892100f00400049000340701035810002519140c10b501e43d900c02c00d2003008158503081012000c103a5a03010210025103507020354401012010f00801c0d10724507085498410400c00a08085002409413401038441d91312107480c040c144984103d2044d00c0261955889044ea000d403082030164440c0300503d5401031100c0c41c86c40c1844021540103a11a0800380c0c0500c03c501c0045c0c40e004981422500c107800c0301d80e12a80c40d800d185001e4040402d0551000111200e0700c420580c06505c03402c41e00d48084421022003908034010b5030200c10799002840c02d2920780b40c040000070003c0c1c000b18160034024051452940e5182000d24490550b90011000304007a0307201c81c140345a00400340700c012400e1509a954001c0d194280c04011080f865014040005400014401a00410403031320241c0700541100d4091 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 48075336 1250 48074086 48074101
    0xd0e090108030a050714060703050402010915080408030601022505011403070e100302040b070c1a090f0418080715050a02030402010e0f0a0f1202040b040c02031204030215040302100506041107020d110405 89
    0x12b0a040b82c0480c04903a1062020504400c4c009030f0820441841c2c82e41c1003551500e45600040b42c00061540d41140704202d11081e405102ca543c85000d03002c10740000160b43e04003030015000e1341c103000540c00000d40c2401001000d0790302007a0340703049841c1500c8612501c604040214040e2040340c00c0000c00c0c03500064404104000c09042d10202d8030350036000e0003400043c085040b030038825041d03031940c130540c1126056200e00e416070280c003e0000a60f00d004102e0320580c1c071a0050f4002e904142c2e514030501100440d22451401201c1c4d000100300350840c554642a1300180c4508450f002d15800703a2440c414101503902c3c0c122401300540340d406a41000180d5802c110301c51320076101012400b85080c4070b02503405040134001d45180c1d14003078010354205403200803090f003038400060081e0304603c0345d950030006080402500c10302440c081c3c1c2c06003100b08100000ba20584030082c0055006903d00881c2c9041c21056006643d03091341e04031040130308008141056205003900c403a590b0b91180c9000c040c030050 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 48076586 1250 48075336 48075341
    0x311030c03090c031f1104030b01080f06090606060d050a1401080a0611030708010b0c0709140a0b0f10031107021903150b03070e0405030c0f0d0e090108030a050714060703 75
    0x82c1c1848812078a40c0f6034060241a225050081100104284458403120185071904200c0229a0001e8034900b426900d0711401c0e0001c81c01c0e07000c003901ba007011410345110003041c45415400400c00c0001d040c181010004940d41d0700c16409440b1200b44e8078001724003d60700030b8000700301c107909055581082e561900000d43c1c42d11038171707075040318840d213081503140700c0700404001c0d24881e1400b86c8a5125603843c00395200d40c80d40c0007000b103403510f0003040808103074545a44204182201f002c851414540384c01800c8408580b001c4031500d200d255031f24030908080c1d0b0342c20b07803180f8254a07501d80450b682c0203101c5402024040d1440082d402030b0a0222483d0032a8402500c2044900800d84081c0b400354503c1560b0807141c01d008002e415801058050020459080c04250094401c0003101d10b0310f540c036854a0b0500c1e01101d00c2e411a904184aa009155403000559220140488061816514090074541d40f807003440c0c1c00740300307210000c41c4400c144a00c000042010046c4081590494540040e00800 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 48077836 1250 48076586 48076591
    0x60d0506010605040920090f030a0b011e050402120a02090a080f010903090f03030f0309020a05120604020312090105091203041203031401120503072d06020d0b06030609040f030311030c03 82
    0x1507451600403401b540c0ca5008010b401004030071600740c1d11700310100080c014401c14144900d134261159101c1c200008079418110f03402400c011f2402106202c0f0100a200b1440c1325030702c694070440c010b2191494211164840030b4201c03604100044e9144107020104010030b1907540315054034020b02c0c6001c0000081034000c5624540319a64500045880703550845198140340000340000d00f4403140b817100785010741e010400d102d00092201224a81e02d10000f03040c4420014101d2079600b0070000d2004605081248580e02d0402a04841c106004400020414049d0800c05032003528490500320001c0018011036000c2d1850f4003008107101b15038100507029100c070781a4120a20504400010121086560741d07000f194030001462a141c03913500c8401100212000102c81b00c00b0041664000c1d100714644500040d210704000340e200c50394aca00381130440300b03020942d1340120001c104111080d0f590300710056200707601c4407943d046500b0606040b8020300107030400d240c0c2c4031000001c1c4080042818003461 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 48079086 1250 48077836 48077849
    0x902040506010906020d030903020304210605370b030a0311070b04230a091a041a030601060815030303010611160e06040209010e0307030f0c0801020c0303060405060d050601060504 79
    0xe2500c0d1000110b0b0200c0c560720500c00141c020400451a280c4030b40c01454416000348122801d00380c490b54030b03101c0c0c030032040030000c98030809221040030030002d400748640c0140a64281140440d200c0d822410740810300d0008041c03072152a009203410400c1e0350150301940c001a04a0741759201d607160140410600c280d0500440c0304403800011080e43c2c1b40100d4090303c500d110700a41035150761000c06c0d116030500d20380a600c80288040812800d01c02d10a80085804d074403401c0d000e029142c0244400c8860b84448070000c01c1c8008480c000f00c1e14000740d101e04440440c0707031102c4959164030101a5480c1380e00e048a506010000002620503446030b07a203010141500180d40c2e83c0c40b60054008420815840f8130014025094002280f40c40c00e64060500c13610107040468404411000003804c1946c190000c0718bc0d010500c0c0035409210244060301c005c4c0007035000861174002c5100ca5150b0742c0c0001030990344281c2e00c03000000c1c0d4640300d0900405e0350503800300444a071035840f0000a081394005000741c6 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 48080336 1250 48079086 48079091
    0x50904090b0f1e010518070c0f060501150903050705280807150201020901020c12030904020403121b0503041401051c0c110c09130503041503062c0f04060f0e01090204 73
    0x100c0c440314525010b04a80004041b035800c102441d40001714814010038040034802d200c2030303050200d40e2130a059440ca52141000107525814001c103501e075a600403101c1010085552414030000d1000100d400c00c3d05d00403181c45251300d40035081c8084220ac0c230030b400c1184240c0c2c0c2c0400a410900007a83c4000d44014400030300c6020700820b8102e00702d00070400712a0040e07000300c02800c09030400c180310101c5a40c0100c03e480c54142d1000200e01070368425802111008510180032741010f50000c1001640700503800e07520300321740c0251649983c90103a402055910a48824071038081d82c011012074170380b0b107508145465090b4508004000420310300c0081e502240c004180320f072110a011032507003003030b8200401884180c2c564401c180d0701d000416000b280c0034803042001140d86001c010306811102181d6030081035085c10b21004215034069130145068105607002c9507900c084481c680e1590114401d41c0c070490556482c2000c5001c0d00318180866900d42c07602c0b190b1000103106412035227034a1b0094809 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 48081586 1250 48080336 48080371
    0x314010608240a1a040b0303091206060f060901080f060d0c06030509070b040b07030e1306081c03050411040c0309020423010e0606030601050a0306030203120306010206090106050907050904090b0f 86
    0x43d10180d8400802443c8038803064008410140307803550041c2240800a001c490403d407142c40443e41582090035500b88690025041102500e49007a4442010703a054544900700500c0c200042e10152000c2c105000c180d001e90000707002034a6840d0064025608000c400000540d44c107405401403030140c84968581c01040d40c0410f0240f04e00301101e040b0344a003403001e46000142e8404071420455540c007583c1c001c641e1002c01c9030440050064001030b084010103040c9012a009400481603002c2c411031003411304010070000464040f00c04860b101074203403001b0880c80038a40046004000301c4000960140c03910315446c200d10280c07410411070100080940f0443e03600c0e9050b01120140845805a00c45410000505a54402e8024040000c0a03040c0890743c99100d90009050444103064003032121000f1082001ca9030b0304002c069004504a0001c2018604000c0492040d510041940045c4007000806401d140ca8582c4040300c1d41d40c20224034041c030304009611100268082d1149412140620103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 48082836 1250 48081586 48081601
    0x60b011d04180f05031201060305090712050319120606020102070f061d030f09041407092610020405010915020c040b120a030f020115030b01031401060824 68
    0x1000411001211000c00030092504000191800ca00b0211158621030403400003d5500c404030428035104101070340d10340304845071004410105134411010542004240a0000c030041151001c1d641c92482004a81c022810100d04d5440744603140c85081d0607119900c14032070f9104840d07802800c4041000d02409507984003ca00341c0c051402c01400a420080d039400006a0176804641132400c0d00c8014000002c02c0c1000604640140c0390500180703800290302c182c0303840d20344a01a2100da11a64225417410b224130000d10134401800303602495414480604445104d040d108086240100122504004500d503800080c0d00140f2070b03a03020500038003010428618000001000b80600c2d4000c2c092821210304010181502c0113009800040440c07100383d480c0010300c40e03810054001d80703600750701948040000703003100d440c071714250001d1481900500c0080c00703582c4140d0450ba048182e0200101d00d1015042c01807807580d01c00b000500c905c0020610031500c11040031403020307400380c00c03d04555580c01c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 48084086 1250 48082836 48082847
    0x60a020f0d0903170307030b0d0501020c0606010518151902010b100906120207110603010e040c08030f0d090204060806092103010e0103080a0e031009050601050f0306040f050f06070903060b01 84
    0x4001c04607418010640c211044c2240590360019592a0101343c944042c0e012808483e801d1905440d60303500007807120055001000041e4125900380f9259282038800480b00e0180000088458031407100f90041170010324402e0300340c401c1d401480b450900d030612244030280c020090301c1c0840d400f4501215804a159002e030148100b2106151580912403019100d008020b521034242201e105400100411042d250310300614083c280c108400340303443c10541449441c40744550700c1414194010012003124084410a40740a2600d0780c1021500d9403141c4001000707400315401c181c005120300800c21021220004880c2100040e40103107120340610485003a805100c02d000c1d000000c1e050200410020380c44800030045000d261803c200c1440140307002a042c200c1c80d40e103533045da946541e8102c013482010f000040c010001124003c020000010100392906001040501460412960b09041c081c0600281c0403c083c010300f682c10520f40014007904520041c001074441074500806194654080c2e07 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 48085336 1250 48084086 48084089
    0x181202040f0504020913051c03020301050906031b0103090206040911071208151203190305060a05010e030a082a03120601031509020c030408010501080102070b10030b06040b0103060302060a020f0d09 87
    0x2c5d01c00c4100e5681c404000309500c4118101300e402c0d205d80c040c14a05c2078114484024224240d03607015940794585420000400b80c013504443c800d0b005400860843d1803055041200b000d02800d01260444c614000035031035000d540c2c40703140c00904004022482c02ca120004080f154454589655541c01c070341000c0758030841c216aa8084060501010700f49482d05915022081d1240d0080303e00c0c100309444070f106103861584410700400c0e16207060040c11300d4800b480001514003880c01da0b40c0f231442d820000342ea804003500050300481c0000390360520300e843d5042d80f81308110440d1580104501d00349155a81c1e600012040710800780a101180c003039803003402010104105020181c00355424151500003c0d805495880350601c420400003a25610070700840d0b0080a0328000107849140505140e00742c0c4000074010030040404072010300000d05544111383c0c0000c0d003903e0010301c1c0622140160014401500007035482440031a0480d40b0943c0000d0005142ca01c1d18140c91034121181425905119076 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 48086586 1250 48085336 48085339
    0x40b03090607090e0f190f0606020d02120313030c080f0703030506060306031b04150303200303090d030b0a0504090f060f0501080c090a0b06030c0705010c020a02010f030507181202040f050402 84
    0x4d910100e0780c0c012000344507a403c00d0b421806001800407a084d0501140ca2904a12520760f450f100d0401c006c54043c085c1c0fa04201031400a0042c0b41649050031f1a18840108900203900082102c3d1040c10701c42c0c80030500c03c503840300c1083c0d0303102c0c20174204200d0303070b0000031040b80001e06010000702c1c503082c0103060b2800798101500511030741002103c12440004000001d580041c0e656200f041054620f140201c011030281d220340c0703a01c00300500b10000c06031070103503801d245906c10020301108000010301c0103001d1125103400601d1850880c0040c03c1d407290303540490791180c00c0c004140144902c6400d40c120092103000200407451031a030f00c440640e442441485169080340f4150f0003035060404a80d644000c03a41c0f070002d003041e2010700040c01034000380d03815100c2040c041030103020014248248200802d480c002441075502e40d60000304100c120b500c03a00b013056159800f042800b0b00886c4041510729245000e20380140d20380c03520384c0c10391503540800e0703100b0341c1032442c1511982040c0c420701e03019070f40 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 48087836 1250 48086586 48086609
    0xf09020a090b120607030606030e010204051008040f150518070810150305010608010e07060e0f01050a0219050c0f0f0904021c1703040b0708091b0a030503040b0309060709 75
    0x14000e6044018001e160a0a401105aa140f101c1461062055600c15042a100003403401d08104008084039058020b00545a104010a214940d5480080d40c140c50240c0b5152074196542d1601021103000d50f0300050000c9800321685d5105116074001d103100300d07111001440d01e01d132511417280e645c01c179511a40f1a1500700e0703155405000c7c00758210aa00c001c801c00030f54100c80d035a41c3c690342104c80070303071024405035981c2c045143c00d03013414045040142224079000c1e1080400d4400281d490680c0100181840303c0028200b51083c000e120804000708610005071003c0c441341440341c0c0318180c450300144541040101380416142416081154104c0581400070940d038540c00d01000b14110450307140f0104d051002d24001560400c0a06c1c222104842d050303842e4105032070b00041806c409401102404030f8101000031215001529003641c00340b92055100400c1d0800c0840c0c0d665102c0c0d040640355000c0001d0204d10000000011400b81c14460201c51050756455000c45600e481070065502020 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 48089086 1250 48087836 48087839
    0x21506060c01090f08070611040303080a1d0115090507090602031b030903060a0603110f0303070b15060f07050d02070303050d020306060412050a020a0905070203070b0c0903010504150f09020a 84
    0x40a0300500100d41c00da10000400801e241c8459040c0020301c00125900c1400003041010055503000c1e0300455a50080000e05060131903801520a5500400122f4000e654002c1c0d0002d6a03c0c0308911943d400b1038500070011469045034916510704c9c2070046800107070905012a024a10a42e001000c842d055405103080c41101802070400300d000c9002950075101c10b0000049075582030002c14014807800000040340c80c610300d441c155400303c1007041841403d8401407130785651808421903450030317486540c00704507507078101720008542003e00c40540c00007808201e00c401000e00400074800d89028100f00c030301d80034220358102c1c0d41c0d6059000050000c2e001f03010809000a940d00a0340d0410002007a10341465165010003280f00e00742002030f5016444418007005604003403940b0030241401c501c05011910341280302940d6031054220003030040e03500e18001121040320310292511210010004c2c131982c185420940c4203440440c0300c042c0718901d0107101d0010403130580300743c0c03201c590702801810700305 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 48090336 1250 48089086 48089089
    0xa03110a0f050f0403060516090e061309050f030309010b01030501080604110112060b0d0209011e050301180b120105100b0901080a0b010509030129011d040903140403050607080601021506 82
    0x5070482010f032400c0820900000c400140140552882074100300485910341c201d510009040e0361040c0d20514151901000b44140c5460380c00404001710381c0c602006c10798190318508145861b80030280244c0c80d01010007132010b602019000141d00384003d030390034000c1d66201c03d003058898400b0b89009080c00e82400c1404c04550140180c810402c0d0b80403000141d02d030340c0f00040b5a0300e0b400982d01000b140c7d40000c002ca91981c00c40c8568806105010b480420300540c040040e01d18807060085561502c5000f541031101800f0780c001c9800c4801c05003000034610a8104020b020b41b00548180d003001c007000c240401c11000713034421350b925007505035074030403540d120101201d000707041403111541005410480d045180c3c4090041c88802000e044801007541e4048001d659240c4902124a040006040805034103400c00100c1501c0c4039000c840002c0d0070304c020f1034190303007041441600021319800450008140036011030400d115102c19126103940380c1c1c0f0900120f0301c0318143c01c108000c006804c004030f01c05 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 48091586 1250 48090336 48090347
    0x302090402030304030f030203040f06080601020c0f0d1703010801061a030601050d0605030d021507050a020703021306030f1103010609020306011b030207090908032502100207020d0b0c0a03110a0f 86
    0x82400541940d01e005d440342c0790301102215012040d409a80b0005e820082884800004001441da501d840402800c10000003529000f90a00240c49000b20081d40e050a40d03c040425180d0f6034030034000f08100721007085980607034000f4411038045501c1d01d130780028010055203415a01d511090280c0d451030b681c0c48010340701d0360413085c90b50086594030b1001080795201001814800c5850742c004100d00010304a8a20048000510b6102004000e00201c01907640001f80130064031340c122841321020224a0700302008104a034005041ca001c9a412802404120008070b110300405900a1000c1500c0e1104041a84819168a40014480e00e001d07221140202046c0641c207100e481620b0200e6a90f4900c607007515a106020380317100e0000014001e0510160114003011282d80c0d10800160040c203002075202c410074006058001c0d000542c0a00310b5507010700a40b0581d50100941c00c2506101c0490203481d0440200800800c0c90008018540c0d901c54003683c0c0c4962165131041a5461604000c42c0c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 48092836 1250 48091586 48091591
    0x10e010b060d0911180f060a08070b180607030c0308060609150702030a0203100b040e060108060c0c03280305251202090a1d0a02071a06190e0117060f01030209 70
    0x4074400e010413507000542e107035146000064965503c510043c1421840042c0403280608050304c0b4441c0110100803100c0d0118400003124080b00006480d000451980b414414201600e19803141000501d8070800d5001403040c0201c600a90315a400c0d0b90b68401448842d20500007455800070402d4030004208844a005140301031014040c0d402d04202c6038082031500000e068041c840076150140c8080c03a06051080019000b0080f004105a514014202d52241d01c06004601c009100041d08155114104221000d020303000415001d000802c2e0b041003080c411052202000a0a02c000300e507507408005041e0214000c040c013281801c1b29922003da54510b071005d200c88945070203110f090103c3d69140102002406e550852111000504d0502000700360000d03c81005948180403a4010400800c120402c43d508000d5032419500d0f0080007038a45035070034103c010307544000d420210b000c00d82d000c0128120703240d00d490813140800b4112060380b105411105816a6000c0d540100050300d0021038064 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 48094086 1250 48092836 48092843
    0x3060105070210030f06230411030403030b01141207080a1a010f030617060a1d030405040b0105070506070e031c0804110103090c0f050907050c190c08010f0e010e010b060d09 76
    0x5e45040c0440c2000656020781c0c0152841d520703045a246244564184000c0c505004039800c000300d041418807180f15000281002c0d080642e110f0702d42d04079034082c058405480c0501e0800a4450009250896010004440c9100041c2e11000031402e084000d00a100c006081071018500c56488203004440920044c10003804054446000041d0724410624800360303c40d140000c3c0000b0b06c1c00d80d000e00b0580e0300500c80801c0244425142050000d004416103064900864010034201034601c0122101d02440002601c18001c2400380440039410a20f00b14031042d06034151039400349161010713540b00c2424079803903000c00d401b280000e0018401950509907844c1c141030000302d20b611070311880b05c0000c454105440f0080025014421441d0041e280c0d42e22844510b445881c00e90483c1ca40c40e11380f000240024542d00b07070f109814080183c6d43e4011800380503c0b80c000c21000d541c1003c2c40c0043c004106d0805a41e51034070309280c3c038000b010700a6000d644d8001d0551844e00141c00d0305800146803111064 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 48095336 1250 48094086 48094091
    0xc121203150906032015041403010906020a03090c050906010504060302090312070503030901060b031e18100b18070905090408070c03060209010e03010606020706050a0203090a080d02070b0306010507021003 90
    0x4070b0015002e01c194805103005010400c00100701400c99200303401d0410b1083e1003491480c011101c403d200e44101d50541e071000c0049103001e0840c0c40031070702501751b0380d00041a4500100380d0302502d6a040d442110014095916407000c3e035a6003092241b24602903c215001030002c0005000c0c2e08d020780c0083c01d030300c00003404035844400d001d0701c4070303080340c1168000321100d4000000384022002c09000b400c5c058000341403264070314109151010b07559003000c08c100d0b800030054800548040484600c400d19680d12801351041c100c0314007271840c01410a04495481541400300c94540031450282c054400c44942e00e8020034141804c040002202c0e00500450b0500002c0119100003880440140c00451042101580310003403180054000542d00034280d00a0780f400008120311907001a2000c1101c40d43e08210781d44a00c58241203045110b1180c10700d421100c59400051002000900b4000c0b0100a81c2a900c0041e1104c14540f4244815182c050015100b400210701610306500610701d81c40c10307802c00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 48096586 1250 48095336 48095339
    0x130203030f0c0c0a0308040e07030510050906060d050f0105030706110a020906030307060603030e01030e0114010302090601030609020403081206100c0209181501030302160e010b0903070b07050303040c12120315 92
    0xe400a1000e4000306d03042200482c04014103055800f4041d0000c81700d040c00d1103145048007424440707105901c9024420340d00400852555110b10040f03030058000000306209a191151107002015020320400d40240b1520000080d00ca20801140141031802005020b0144190b001c1040004018101d203503d80010480103002415510409000314401e44800042c1008100003508442503100820030076410280c40c1c01407a40c24004082c1940e9040390065096141d03200100c001f480e8507000000702c9840000d0120078003900c48094648411050340c259502d42d24402403000030307105aa8150b000c200086008001441e02d00700c0700307a001d44e1084c13200901e0754030801031614000c0442c0d00b980c1e14407160310050043c5136040c010603a003000307503081403204245440900802c00805110300044c14402040d401c4465400380101c0c001080c5030001161103048034203100391030390300550701264400d0340e107940024045000c400381e0140c1038100c101503220500008082c3d000c2c100c1141c0300720607681030007070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 48097836 1250 48096586 48096589
    0xc100e0411040512060402010207060c080307080c0f04080304090f02040e01090e0115060305150603010605040603090503160308100806040c03203105061f0e0d0b040209130203030f0c0c 81
    0x1300d01d81320000070b2465051a0001904025550300a00200109559070102252400d0300300d07600400107241508443e504e508a0148601440c1c101e4140240c00140000d5058400030180c07055491100d13003080000c4442690310300301e104038450b517071102046200421403440654084440c80107140008a50728040060601800324a40c00101c0803a50320000d014500341406003c94841c6001d9900d00d103075506000c0c3c06401d0380a13a10850f0101500d0f000080100300052060301e1034004840c039410008140f03854040d140c03000454041400e507204050006d40c265000400354010758206802890040c1103841d507410001c2c1809000900140300d22a000e03d070744603003803065002e46070504500c40f45516112126612551011162680d504100c18040c0e035981e20001c1c0310340d848180c03a000b40c42100f90740c0c2c152100b00030307131460350303402400f460160043c850460980d502c9184204c506070450740d2000800e103401092030001035007551080c030040c0e5450800720000d00c2180c92000845032030903078400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 48099086 1250 48097836 48097849
    0x1a0309010603080f04031e0b0604180f080c060714070b0c07020a0608090c04060302090c070203100c0305060a080d080411030703050f011a030d050316050408010e07080c100e04110405 80
    0x74004c40036920000d010010b2110000e110094444002003012011200d034855015068018001c54420380c0c0d1900100fa00300c40b540001842140d020003010065021414035007442c0d0000c5590a0f038900881d00024141845040c1c07201440c8041c180d400c1c00e010f07031070b00c0b510700300d6900030094205110100140d00240e641c80948600800c400c0d5160b41d21803401408581c00c08400f082054016400c0401c14401030341c8000510768030507500b1030208c0d1200c4841c00000c1c80c1c04002c964010902d454503d00c00c800c1681904054442d210544505222650710040d155032040740d13880040010b07880310007103000660184401403440000800719580703c0e840e84c4945041c04103841540d00c260307549100c00a1400d900590b00c2d1350003801180074100300d0b1500c10740940740c1d1200925241d200d40c1a008003442d041c0c011000c2d9006001100000c0050344c80c1c0512655980000d40901000d61040321907451051034030744000c528a00740e80d40c42015100304071040c0000781140d0300c01006c5188040c440400c2580304e14 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 48100336 1250 48099086 48099097
    0x120504030203150108010c0c0206030f2e0e010b0301080d0e06040510090905060f0d2d11011101020a0f05070203010e0313030c05030706050910021513061103011a030901060308 77
    0x1c1024075225450b21140e6800c444585030a4024070042134880005a80c0da101072f0790344040040703203219007a034901714040744c201d14802c00404085c0550003c01214680c0d6a4100280d0317550600301c40e0181d17250410042c085c04244100400c0743d200e80110162540f061503000c0c1d1241000d0810350606032514001119070041801c200e00240105200308212182c03401002c0c3c00a800b50790049a0004000c04590340342003070740014007044d141070b0551490446c054005440300108034032044000d0001d20f4200c507842002d0340350303e0000b800c0c02c1a10301908010700c2140c000d2604d0340c0341c0e00d1075482003240584468001543c26a45556500225600c621042c4018040c40005c60001d041403425841d00f4070405401d508140d000b039000d1030b024441c1079003000c02c8031071200c4115039240e047e0b419110202d00c0d2003544025802c44203610300a00402500c0009214900c0e4403800091202c040410b00c440c0150000f40704103140d01800c5540e8a98602c99080216004003240b40089403070307a16030b1603011f02640314 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 48101586 1250 48100336 48100363
    0x60408030a03060909022d030a0f02011e0e100309050f0115170a0f050f07080313080a050604030f020f160518060d02040f0b0d11040c021207120504030203 68
    0x71000c00c101d42c18450340000d040c000000704103004d62a00410034200c2001d14404100000960841c039540d000c80741014549402411070f00c10802c40d103040e41c6400c1c2c0c4207804070b010864061151216160030005206290425035030303a407001d4500341c00c10903ca4a07018004003030640d54218180030450500ca05202011100008a00312a008030600780d6503410b644181050450032001d298080404942c0443c110703000251120012083e04106090003012910b00d1030501c9500b0002403104c0c07010014095a00981d840070340503030366074946540ca820b5111001004c0d604450000380000740100e4841500b50000d104480301040510401c1d850442e800701040034000c8901c0082040e0325040341c80121045509803540124240744001ca81321154505000340718548420905001e041e00f40c1c00b1080204006084850803070700746c2450000764011115460250303003000b0003024002d0000840e034820b0100b101e15075280640a0721107050311030f1300701640d60802004100c00409070b9001c000b0354900004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 48102836 1250 48101586 48101593
    0x5060a0203060607051b010f050705070506030c09040905070e0604020909010302040203070203070f0c0e07030c0f0c0215070c08010f1103040f03031401030605091005060604140a03140a030f080f060d030905060408 93
    0x6c00a001500310240f0181c56401c0081c04c00c00580061404603c440440d10709941d6252640c0792106040924058050481c0e0800e152008520a00c04005a1401150b15008002410361540d00502081e4400e040420b6000446440100018205a03000f03561169580c41540e0500c180e5550301804e00c40d00c25001da58159160f1028000c643d1051141908041d0314101040324907414007001d012a070842d11000140900008450250340300d405660f02e10001c00c8440b02d80e0b03010203151944084000d8082c1009540c41c1070741181460501e0310800c01c0340c2da82001002d04556940d0380b84995420305510480401d51209000101010400b4049003e0751040e940424140781c280300c101d207000341461340c031310b034050a20040c0314043c2c41750401c4400f44c1d00d0484c400845018180080b80c4144440d910044c07540580000300e6044c0c403804111800407510a03a0b42c0e112604603031800b00c420703001c02e4503150056560007000c1001840c060ba5034924052081c14071108056603140060308940080e8000c814541 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 48104086 1250 48102836 48102883
    0x613050409050d0e03030a0c031101110a02010e0712050a080d06030c060305070e010201050402060919120503040303020d051201090b130e01020901230a030b03120a030606030b04050405060a020306060705 89
    0xa802c21010b0001340c00a400550400d12040d40007004032a405c140581170216000301d40d1070f020000e4004c0030441c4010301d42d096440100901c001c1c001c102d800c2480d0001d0140000110f030000000316051801e5410000604c80c03620310381c551490550100e035000c1c0e1003c1da590303000000500c42004510090003e62400209480c00f411301410300c000800e003d6046924103810800181c0c1c1f03203002d5031031088050743d003d2468003040b41c18095440158000800303641841415404000c0004018411b4078071940c29103800011003581900e0b103004030462165045002001800392a1165209007142c8a00134607100f80c02c3c0c59100712070201c0348030751044451030750005840c0c501540c0266000c6102d91355036040a48921b441d140441450158070000401c1684495550f10b065400f00b004080c00b411154000d50f589510800250041036988104004241814810b01c40d92810784141c0b07104680005c05000b503603031002c280000030342c4020f1189034072100c02e028000100e003080045540000140301c00c0703200311 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 48105336 1250 48104086 48104113
    0x21b220906150503010b1305070e031507020f0f0619020708180901060207050616030e13050106030f090f03030c05040b0f040815060a03120c060f020a030f0614061305040905 76
    0x182c0a6400c45802030381401c9602e903054440000340b56840c04080350010b820f464031b00d4111003501c4580d01c01a070600c2990405c4150b0f216040f401400b560144c0c00320343c41c030b00d046013216448100072040801d464000b800083d500c2c2c0310305030151034071041c41100103191031803503a01c5031b045410a10030300004803180b6880620340d051898210740584090300050040525010000e0194428513030059140d080083d00307c42014064480c2c2400940700800c00700310a4005143d130700013050f091088500181c104030050500389090310401600d980c001c030007410924000e45059004c4c100d50b1b0032000822108000001e498031800018000510141da405561985040361451402c0300c005184040d0450100c2130100c1503503070001c0c46085951118808408a0301c0120694081c459010050485401c0201915190f02283c2c0244005007441c0c408021401c4100f02d020112411400303a03504d03a1210414030314a42c501080a84030710b1440c3c000601e405600c40e000305050b00c00c005012a1075034007001200144 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 48106586 1250 48105336 48105371
    0x9010905030609070b0c0f060115020610060f03021c05072001020f22180606020607020a020102060c09060c0a030207030c06050c030a0302070201020a06061410021b220906 75
    0x4120071401403a4505041d01d000d03031190018402d4840c071a10020f00c8020106080c48214182220101034960a42e503400c40030425001d00d0f80030f04010300030740002031942c0a0038034005c01a6802d50b40e54039500361009405134001e5100d144d070208408143d0a8420f0726a000c1d0240600c1405950b0302d0740710450400004421003030f0440c42d4007050340d0051101c3c181c100c11000030341d082910104400544c019002d83c0058820800741c001c516404161140e20340d2510f40d98103c2c8044800030f501704c0c0c0240d035400c203040741c035001140710003401a0041c00100360b0000c100f034060b001e0054001e014034139001080305403034504082c50314124090707006040108144420500000003c00d160b0412514200c54210380036181e104810406042c180d0214a000940e4420028406019486401040b0043c0c4034a07102040d00210201c1c503200f4414810100c0f24a131001c202941848184900440d180011100700044900c0e800756500300d240c150060304400f46100d00038080014020000002e520310100307180c540 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 48107836 1250 48106586 48106589
    0xd0504050c030709110f0a050f03130b0a02031902030601090519140907020706050a0c02180901111809180d0302090306070f1205040201031b02030414030a02011b05010207080c0102090109 82
    0x80d0b52812040d00305c010960b0017112a1015414a425590100c00310162114000e4104035a070200b0040100b1002d58081001605840d005840b554803940c0e84100b00000d80c84101c91001c0034214400d51140e0341ca007036401031f5801c9401410441c0055403940041800a00f41481540e0302803d850b4041010b80e401d04180c100070b090075241462185480b10340a035540581d0311451b0104070000900c000c00e140700310301c004281507000f004540c0c0c1084500d20750849100564040390154a010b181c040300e144100e04a0300a800d100142d050600d210408010840c4001041808400c0003a8030001103000305000302040960303141c40c0103840d000c100061500d0100000c0c04002400480a14050941e402034021040459a4140850703240e4413072004030044d0000da001100300d4990301c0d614055564020019205682d50b83d10307607504030805801010340d50620264068081240610b40006401e100340112000d40c0c010000545400030b40d40d00ea046c143d10002d070105650754042841c60680da4000304440 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 48109086 1250 48107836 48107849
    0x7030e10020106030201020d082502031905130504051306020a090303090b070206030a0c02010603050d050705060a20160506010e0105010f0903031b020d020603100315051302010e01050d0504050c0307 87
    0x1c1104e0855002039990320219100700d0a0144480c00a81019641d1103d031040d40d46141054142e482e00300d80195903a00302c0c0b85020358140002c08100692841942078411b840541c3e102c0c4c12046180006000080c90050200c9900f61503142012300441c490380018007810559544042e121351643c14010840f40040c0c00061052800704100d1015944040c1580c4e084401140c3c0014040031071001a40100b0f40ba500c010301d40d0040100400050340c0050140540034014010f03150355070f40da540d00700b048036460905841c15980c48111402440043c0c00600b00380b850216250200354215102c8600d003020036072042c010034014000502203564050f048288050103070410400359800c55130041c00140c080008540072129803c00c0340190340d14610b9018450f500030344121b640342010704100c074017030040303010568603241d9504041d542c04220b03200703103485582d404400b03195050039030740115100f84c210243c10f0b041210074004054214030038850170f405a4031500c000d00440303502d00185806c00715203030b0052 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 48110336 1250 48109086 48109091
    0x10503060c04051e220606020c1927050c040501120510061b080d05070801080a03080415020d02031006020d030c0207171614180606070f020a0b07030e100201 69
    0x1c220344c0d220703a0710501194480b0301d241c4014080a5001c5403241c0443d003503841caa68000c88000c0340c000071507031041003564002c0c0e081c0d03410a03000c0300c140030715050128812001265141030811501007400f420718844002000d4951014094010190903580280c808102c001800a400c02c440e68021010000d0310400d43d8045c00180b030a0700800c94000301c82d20854003400480c003503000e40200340f5110b002c2c1c00d6900890746a00c60341245007003402050103d40c4d40c40411500340001c40c031900300007003102c0400d906503035501490350303183e031502000e001d041801201d50340c0034881000c007081c1c20300146210306501038080c0d00f1546460f0000340b8104d81d6490803410300d8a41001841480d03804290b103800e40710b90240d03112061545580103860420340b04440c00c052192040003051401c0146022003455201310f84050100209011914201c201641c001c0c1e40414100220707000118140c0780c500700b40d0b000404d0141455580c913826400fa900103501100000c19194141410340303480202480d1030700061008 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 48111586 1250 48110336 48110339
    0xf0105130b0f0402010e060c010f140412030218060703020102090a0b09060412050f0a0506090607032304020a03061107020a1a09210d0e012010020703020a0f0803010503060c04 77
    0x106094104050902c941145895001406590282c1801241c12102070051941e940c172009045000740141c0d0745180a050074800201c19081d00c82c003441c0e00680d0403444242a451000350154000e5211042144021000090810041e92890040c004090003030b0005070b036880d0b1400c10460003e20503006001512020701c46810103072035060581e400e42e0010781d1420303000d01d41c90821a01d00b03a101050712540740b15a5044904200011030b5040c081d10f00e04088403842d441c1c2c244180c0c00d852250701807540d54205d040c001100c0c3c1c580140010340060014014024845d1245c42d40c000351407400d604c146998400045101c11418103a03000e000400c5010000e1050b442003c40416491080c0d070105407107207400b13605203100c440240c051a014a00210201c844d543d00280c00940308140c2c0b141c00a0204030241c070407690603080041403010100400d00a4a01400721040d00002174001c9002582144150319260000414842e15404911300a0030025203d43c0352404041ca000802040b09a603041d09020 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 48112836 1250 48111586 48111593
    0x5010e1e060610120905010f02030c09010807030c0c02010f0e0d08090f010302040b19050c010c020706030f090215031905010b0903011506020c06030402040902040906050a0c030e0a02042406020f010513 88
    0x80e41041c14880c00d0300885e1000050403e140540700e6100302c08210340c0f000081c4a8510818002046410000e880b820301c43e41e1012019801c03210000e0501011a180b1019030f40151301c038100c0340e0710395161420b00340810a5008045507a4042096048403140000a003520003854032000340c1602a000f481d05501e41030405040b2003c0c0d01508024a50000c2d481483c0d900f150701600030346860f84440c100030841e035034081800a542c0d00942c402c600c0400d00c1d14001d00c8035000240244002c2d190040c01440301004010b01c0340e0651744c80144408045018040425501c2c402c501079580203000081e0b03081d0700c420f0301c4404c040c212407002140102c000c43c030f030104120054000c40c203180f0704d4108582e4552280d8aa001181c09442c0e1130000035403062404208108009159001e01d0180102d0341c020004288910380580884062521140c1d4580c0072643d10340040c5002d400030b40e40994031145440b544420120309500301d01d0640c0184000d80c010b00302d10400aa02441801d0380801c0510706202a00d0b844d48 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 48114086 1250 48112836 48112847
    0x509070608012126070b060112020306060a0f03110a0c0b0a0203010602100507050d11030a050901111602030106030209010e070f020d0801031217010b130510080c030405010e1e060610 80
    0xc00040002e25120313040c5940011803c400007100320070b0644141c0e00c41e642e1510a40f055404c86005020070280c801c510030440700c5100760f0740b0902c0080c104c140303088090407040d1001425150010b04040c0c59040200080c032100e0007074481d145054488005040080c42d001d080703502d00901429074180b041c4010800203a00282880851456010016058448080c200c59601c1404400c0c410130382800d20318010a9003080c02184070b202480d500b002161180381160b400e0716030100d01004030b10760a10501d0300e1004d2400c10300c1d041503c0200009010343e81d07a804282070340f10990040490310314500800c0b05440d081143c14865110a2020b8503490b100351801422010060002800c1c40078032449a41545000f120701101a1f5065403042907107603503c0d04e8040741a41301040c06004854030420001d104c1c01c04100c03e11003d881c036100e191265a03081900e8405400003070060b1055901c4c0c15801d10a860140100c80c41020a24020700024010100c12450500c01a116902501049884242496200 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 48115336 1250 48114086 48114149
    0x1809100f230603040f02010f020f0d08091c0905010f09080d0c020306070302090a03080d02120916060503061e0d12020105060405090a0203121e0d0f06060203040b07060b060d050907060801 82
    0x9003000041d59100d01c034202c1c500ac0c056440d82200344101d848810f40f041d0460b8403a88565501c504491110187d04442803800b2040e080742e0340852b600010900041d070240c0a440e216241e40d10f014038101c1d55541c1554a07090321541d004011a0455400b901541420305c4040e61100e11410294a841010008243d400d0300c188800343c01d070f120200b8448401143da070122541064518004030b070500781405001d46030302c01e40c80c8c0c40708102101e040000f1880c0c06001640e11a00004101c000c8004040c0c0a4055410b68042c2455007d98075105070780014024403141c15030280e0301c4d030002513686088000e100031100040c0040803940d1040340003c0c0160380010b81c10506401c9081d040d9120050504c0c1c4203d0301e070302030002180815020451030b094206039130025800c582541800d210181d500c2c40207a84900c12801000408142000640080b07040b540000890709006088140b404a4004800d800c807401a180c100c01070700070440401405900c10465070243c1604500c1c58008240c922008010b004003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 48116586 1250 48115336 48115339
    0xd02091809100903030905060405060f1803040506090102010608100c17041221061202030d09080a08180604030b04120e010e01080a0603021f030c051809100f230603040f02 75
    0x3280d60003c101032098106040b015800011107855040900c2d245403103140441c0c0e1800020010400181c3d40c4150249201c0e0341012200a10300d418100024081590301c042010360542d901c2d03250000741104c0030841e808030261003284c00a0044400580202400d029541c03207198000f04000340004298019120116007406003081c0402000b40d010b9506100c001c40580e0551500d04000080ea041300c6180c1961000d1003182900c41e010940c40c0b06036034850b0329019103607041c0d100e10440b00018401d14014060428441d41c0070110f8402000015460342c1b0075001190020301c054203000800444d955007039074552003818541034039080b55000800c60114209101c1c100060b11000ca041400981d114801440d0058603200c0c1200e4500c0c0226030100d0a21549000a40b8041813a602544100e0035281c2500c041225149052001e0040008240c8054010400c0c80d00034407002606c0b0204c0400c010007420902210f40702d1403949441364403442e07038424559010f400100100702c00031b103039070303101845c0e242c0d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 48117836 1250 48116586 48116591
    0xd0210030b010909050106090515070b0115050d051305010b030c090a0906060906060216080a0f02090c1b0c0316140402070c0e090c0405011707150210020d0209180910 73
    0x75a0040b14000d590358086581d03103181c000003207a40c46c0c0c45001078090344c205030345004803001440702c4680304c3d109900024280058040040c8000040341102c40c0d000c80d4940390841c00c101040550004803141031325242104880904d5010400c00280140c0c1c0e4001c81c00c030094480900002c001c00c081520003409201141e03940c044003000c00c080c9a010304083c0013040c108004d201e032104d002940c1c80d42c40d00c001c105010761000c400650381c0d00008002c00225400307901402841071503400d01c00c250780701400e030003100c0c1c405005030b482c001100e040196100760800014000c0401500a160920450300c40e004072a4140703031024800a50000780880d0000829900160b071422941041c040070b119680002280c94131103014000c0d1000c0016012110315000c890800c056640d8004840c2610004025013030f140d002402c040190849030010041400080d0041d52085c0c40c00030020003c036448080d070503a100d5404100381c0300c1401d01c01c0010300c00d00550742c441c00b1a81060302e107040d030301d0a112a85089958 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 48119086 1250 48117836 48117851
    0xd020606040b180c030601030b0603040302071203050c010510030308070302090d0210050702031b0306070804151d07030303020c10050603070b0f1612020c03011503030c020619110c0d021003 83
    0x110b544014189600c403d03216942e0754103001c40e01c108103610176030303c403800682071440b03103101880c2c110110390140b80d15070010030105181c206c00b4809140c800c002070b001d01174180a0400401c40a004140c858100b00c0c04018001d82141340180a004001d000c9800301881407000300b2164550761610706049030100c921000000b00c6000460742c600c58008002d40600600e1380941c0e12502500d015522201d0032825200c1964074090100e4030b845048501501000c80b0300b503100041070f0340b40c0c0f00e120b9200c2d88503048540700c528492501e2030151594000c07000030f03600140f18034456009109070640009180020301c90b80c00c0020001c3da40c3c1000c1d000d40c5661800020715011705400d0f0070200c0f0603034034102e00301c140300f50518240121490b41400c40720b40940582c4210504030f140602c90400c0300040746c28982013003415034908880c400c04a1a080380c2062042052a0050034442c620340c0d1800280d070350781c40c1e100199000103420881490605406100c00000d0100160b0380c086004102e5845458001000c8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 48120336 1250 48119086 48119089
    0x12020114070c060c031209020f010c050c0a080c0301050a1103070503150d110306090105250201110c011b090b030115030b0a06032004080618030f0a0e0a080d020606040b 74
    0x28420716200034145520418005510758005039081000d6009498042100300d81180000696100d1100254002e8905040d4a1550701450f06101e550740290111034403a582c0c40c011501c180c0d01508240300c250301000d402e4000d840c0074014594410020b2009000001e0a00d14180311400060820414081c01000140004031020142c0c401201d00400b0340c210020181854400c02d8240004103000f0300401c0c00241000005000e440d01803140c01d40b02642c41d001525484030103411800280c000c55417680b40c004150046107010f800140300c50300c0001290412404412a1220403801b00380030700a85101c100105210982502d04455001c07541400c1c19040120450042005041d401c0d03200040a80200301d140d49507100035040c11a165280c07107000c000ba0840d010600952144010741e0b03102e1000140300301000e40c943c5502e50500c1040b45d04029221202e20459000130407241d000816101e488801d0745043c00b000f0300200501400381600841030f0310001c1d100c43d4001c000794061038440030310042a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 48121586 1250 48120336 48120377
    0x91d0c030601060305071b0f0b1807060302090a0801050c09030d0801061e03240609090207020604030f050a020a090213050d0f11030c030a050106090c0f02060f0a020708040902071209120201 83
    0x3083e981107100341d1034078290f281096800284250984809e000030000814295210044032802c100f0900107200c682d25010007240030b90f024220b100d800030549440010b000c0001d009183c0a2641600b0490304c4841074400d0503e00341141c400d103802c000d00c000040003856041400c2d004a6090a5010184d9842452050300a07240885482901060320208404844110000740d81070740e4243c1e650805181d074440c0031074281e010301307880a54090303c208000c0000a0a02c031aa4032010310540503560341c28450740004100750702603031002145903000103541c0c4d100c84051103600d018081c00c0350000f14582c82c94407a4100c01e011142d000b480c40c118003a852030f6a56042040403040ba4004045a00d1002e0503e00b05018110a01c101c402440c140101010001e008910540c0681901c1c0d00801680d921840c07041c4a8a03009012440c10030790030000302010a141030b0080014081140f07000d40d840c5814075141500440303d240c90001c00070650010b014403429661024411a02440c0100c507002031501c0c030111 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 48122836 1250 48121586 48121607
    0x12011a04030b0c090f03070b0f07140a0c0e07080709090207020a030516031106090d031b060c03050405151504020d02090a030303060e0a020309060712020c0601091d0c03060106030507 80
    0x50100d0904109944a0480091048002c21760b2141071002e5504181551500240540c0c840c200d01440041c00348420700b0050000340d03005900501c0e03242803459019040c490510340c10b0303400b0421385d4824400d950492820316000b00040c505071505180000008050710400e0060601503600014100d041d9a0f0340700e440d40246410005984030008241085005903199210895103108014280301e45403500000b5114424000b41550002d600309941c11203c5074440040c2ca44196882d1075580b02242d8148a1010820241d440000d11810309041c094640000c002c0240301049000c2c1c10465041fa04410315241c0c2d0070181c8015842d04201c10358140a07001d480c081540081030b003c0000140740d0315820240849080444010700d5072110412202030744401c5070341c044c880c0d1140020840c1c041c4240170541942c00103440040c10241d0704610b090404d00e023a805a0180390325611180d00201c0503c4801c0081d038610070080440c20034140110b80c40b05414800d0b071b801e041e5600c0000c2c4945028420044 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 48124086 1250 48122836 48122843
    0x5130e150703020306030706030e030306100207031e0c05031902061303020402030415110c0303010509040c030b091e070e040809010306050901030302060912160209060103060801020a09080c0612011a0403 89
    0x280c1c1c90001d10050007900100c40d49882889190340005425001c0d01c11400600d02d2000a54a9580c8007024450100c0c50202c0389411031191480001c0411052082000041c1e1003c0d500803201500d0304000b007100e0b416070840da210350800b40180c0f41603004940d40f06000751741034a005494014034280c0c69150140c507840030f0740090000040000300304000040c015040711074502000000d070030701c0100c50507010791302d10300c3e04562040005002600c0d010f1655070b40a0301c25000c260003c0d4803551410082030f0191524601944401c0c54841c9220055900403c0706454100600d00945810000300c026480a880581030150010351020964403940040c40a0440680140341d5541d60749402543c61404484404160213810203110160845004a401904d08510b10f00302401c0c2c5502000000d00700a07003682d040c95901c000004920001b8000b40143c0340c866140c4440f0a89840310003130404a440011510500e000c110016042107960020350541314000116036101c404a001c81040c0e01c150380018 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 48125336 1250 48124086 48124123
    0x31c0306050d0f05061e0f04060603080a030903081b04030b2e060201050105010513060e0d02090109090c05030703080a080c130f031b0b0a030b01180602060f070905130e 74
    0x1042801402410600064420822039510b03698642c080360644020a07032002d141b41c009400308142000c075151041c1c00a0083c1c5002038410340e280d441a0b159405107010030042510b42a00c1018981c22005960707002c1240b500650b83d0800c109110300d85407149000c020882006007010070700410b031010b8620645407845400340308808400002e1503410605102c0e1500542c02d08001080551241007915108031412202d11354140c1031103c00e841c0c444100c410340d0b80100d40d14411402594814400074002c044d01764000842d00d02c0d9040441c1801c20700d8100b1030095020880400c00a02444102c4030f11803254541022180c03034028046c10640b00d01850f4604042c1d0708039010880da40708003000300c2207034401e0015101181d000c40f1030034400700701c0d481495203ca0003488200080343c081e41000311460014035290710700c0c0b0302d202403003002d040550b00700c2c50059100760f04010700384044994007608000c581c01c0c840081d52800d00051400301000c06101034030b40d280d00113800c2c034000030802081503841441c0345 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 48126586 1250 48125336 48125359
    0x60706060b04080319110d08090a0209011403070909020d17040305060109020307081e01060302090a0b130608130c030f020d1202010902030706090b09040b0d02150c01050105010905031c030605 84
    0x341070362900100031781d8000311441910700203018002c002003c0c0640c03505029041c0942c614009450700d42e03000300101c0d41402500c0151005035618001c0601a0907144591590042201e092500e881001d42280d141c0300e1908920300056a41d9a41c0400c2450380000020f5000c5c0100310b101c80741c2d02803031340020101d210310000412001c455030007a620a00e03181c0d0b601181c41d80c0b016480e100c035400c08115886220045801840418407a400816458001404a84489a45140102c1c4591001d80e0a440070b58080f90188401903006c14200c1d0810034904904055100d60707140e14410703000f02c0c07000030000c80f244200d0b6401c40d10b0382e2220501d11a00120580c0e010110024080d01070b00301354408a03c603006080d0086074803070044409100746c40117807502c01e0410f240032040c4001414205000c2d5840001c004180005a40b88071000320484c0800707840c50f46a50500c0002800e4030410703007289050060fa00420704c41600e0004540800300c0c0c200c008001000c400301d40c213500a0140790000d070b8124004588 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 48127836 1250 48126586 48126599
    0x1403180f0321071205060604120f0204050a0209060421060504031701050907020c1504050402071b0b0412020402070c15021f0c02060402220c0c020f01020c0f060706060b04 75
    0x252880a46040c1c003003454508070840061460400c9910030003090500e80703048103c0c02e00b644403540c0041b0145c0190b18203910347d00d500300400864901201c601c0ca00d20106011800d260280c03079040103c801040d41407001040016500b400b45004145022685102c00761842104060010015070080300c00c1041e0700f03207070500525030002c01c51750004016010b0000030f00c0d03081400c000c03807042d1940c0d03015103da0301da1042044072107d441403484482002c148000318842e5200c1c402002680d10500c09200b407120b02400a4580b1406036104614082051000700591031880322003605840c1c1c100e0700140c0d0317211540303496424049203400c2000f2900b0781840d00c101c003d4000079400450106110301403803000030f0804810a540d011603040700140c001c10081001814a196510440c4000c01c0401c142100114040000c442c0540c1101c000507072820700b41415800c0c043c0390212a61020300c050035603131305c1d180085800841501d043c030b4040d20000940d4000d200c6994001c030040c0c050007192613600d6640700c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 48129086 1250 48127836 48127843
    0x40504090602041d07021b12030409060602061303020a0213090f03050901031505030c090403021515181005130207150506030c0a0e160912050718020a1403180f 70
    0x400306042c1a03131400c0081801d50060341d41c426030440c3c1c0140f032440d00c40d40da80d45070070303040340c04154116500c01062070309644140b000e4400b42407002e8001540720300c0c040000346411809801d42880010034114200030950100700340034520740558040380d8441041115030020403e1850140548000c500c45504140c0d0010082c140c5820907a803d10503580084040c0060040c030340720f00d03641a41302460304002c0341400c10300349600c079010f401a140c0790489280031010740c0e5000c680206111501d0b00c00a425440d00311481d0101903082103124056240040c0382e00c01c2850140a402d2103005001c003000c801c4031040d0110341706e00b81c0c0b2840c4503202d002c4400c0e0700d00182c001511a07034072901403100c82d0100c50904000c0b00003140d090350705140da107885403000c00c10000d84101140c82081400d590101d00d194040c14220861449240101441032404041e82003c0308503124614465004000c1c42c1e83c3c0f103a0048100c0c1d6503150007140d150341d0f901ca030151560340310300c203060039010341c0a400c26502c42c40fa40172 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 48130336 1250 48129086 48129089
    0x6050318030d1e0e0319050c0307050a0309090c0206130809030307031d150a0e0604050d080a08010602030c0703061a030601120c05030a02130b03010e120d0b040b06040b0c0304050409060204 83
    0x2480b44400c80d82983e01056584480c070100103613006001c0324075501400c0d00080b5003410181440341c034100454041900795401040142c4060b401000319104041d806a2405e0043c055441d041205013800d10009464540217045210010f0240251030300f032041c10000c441d202880242126952402442c0251220403100400d9800c0c00003680d4111803814100540b95031040000b189902d010310701282a0391142e03100310001e421000070707c004501601c4105442c00858000c0354401d0300d07051007080042c40c0d41d605820030402c6410920240507a40c10009540c408e50740d1120001c556101c0300046122451083c0d140154140706800001030391a483d111801400c502580b030001c00341c0e0302c400034195128200c5000a40020950b807c3e501206055842101c40031401030011454604400180780703050010042208081c000141d05040c1c00c04502c03a0040b40c0b0826202031040000003000280203014038070032032182d5000020030302c881c0041401128091f002c0144104021900343c00c0c00402500207 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 48131586 1250 48130336 48130361
    0x7090b030c03030a090312090801060906170f0606010e0310050115020721030305060301090b07020f0d030b0d0b0415110706050105180a0b0a03060f0b010201060f030302060106050318030d 82
    0x403007090440e5402c010044840000a90310380c55541445c1d540d030494a50b000720040810030a4100012801140c00e0049200401102c4404100c883c18902200c040c941c1010711341402c0e51016016010380c8001243d5941d0082702428000070500c1480302080c104607840b000802c950b4a000d0020690103503280da040111071240e030031564102d4881902d014030203561a04080d4071144c82c01104002842a000242d20000103000801c005460f951000125003058070000c025821071001c54a03111010405131a001c4e0642c40c0c00e2045500d8000410b5180c0c10081024196410020004080c055401c41005d10b03280501c0b0100800d518400c40715106400c00141120841c0c14080001514581040700c090b1031007018400107441d8480c0c0591000401c200c070315840e0080e124520000225240f442505000610301da400b2480100c6140024210f1303000c2e070014107858840e420b007480400e0380001d00c0c1d070660700d482c24a01c3d9a0340742c1217400c401005030704140d428a48400283c448403010b042e04901c044040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 48132836 1250 48131586 48131593
    0xe061006090f030519030e060304050709051605030a050a0209030a0b040b0705091c0303150b0c06090a030203070f05011103010303110d09060f0e040f060807030c0801050c040302010e010e0307090b03 87
    0x480b003090368140d811610003d040c9912003504a00c90408840c00090034511034200303152014180c1002c20f510350821074044e52513030400a0200005d1155003c6d480c0e1040c00c210080300c040101c038401401e10700000d0071903c0c011f56a54001001d1030507650444481c0c0400400310b0f8002e141130301d41740007101801c48040b00c81260080206030100e0190086e91050b420007088411407003a006c149400c51501014150101611403a480034001c950382640409418000c080c6552440340490084ca4802c02a00200d41584050080b0300404c1d408000d440c0c03080c0c0c0c4001c140c05000c5181c00c080340582480490485540320004c000010141c1080c54800740d18154401e55486000c442d01c02e032056170300703441200c0224900c90030300048188224003141a43d000148009222082081c850f42115481c0e00101540e500030007049c01801810840c4800900486000703024a1030510004a1a03000d1480000d061200072070307038181c1c05d80c0034242010003000083c0460b44115a9100403030054050000c00c039000e0b00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 48134086 1250 48132836 48132839
    0x30f0106030f0612030e03150108010903030b060703050f030c0702040f05180c1f120e0307150b0f0402090301090f260301050d080a02030f0c0706120504020906040506040e06100609 79
    0x120300c3d00071102101d0446000c1e2154024980f0103480d00c01107103003040d0f454041c0c13140c19554200c1c5da40c01e584c06044404000500009245406801c4030302601c0f9a81c8555000c0c8004400030360320500f1180c111400c103026079200d440701600c0030464060f03680001d5119042207254941e0381d840394003a510504000880402c280801c004c0d0640303640075842d2564125501201280014140400c0c10018002c00c1c60a02100700c000c0e62400202c03040102c131900175400004e085014070a401c801191040100b9108107c0c40c00c40c00300003090011091855030140d41c0110300810b00381c0d800e6111003481600000c1031010801d0324034240b1201c558200c40c4100c1440242d010034074010344542524103031103025142e02e07503a409544483c02960003140c0c20100310b11042041ca9080703900c4c80007505103081d00c68014400300d400c01a019102c105900781c1079004da03141400700800f583d900207035581c101c0016107001415480d001d0104000c2c0030051700801c414420341041c000c03070204180b80e4404440c0181c1d01c0c0d00c03505 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 48135336 1250 48134086 48134111
    0x302091306230d020904110a1d01030311190f0309120303060e07030b0d08030406150605030403140a02030915130f1d07090e06010909050403050d150803040e060a0308030f010603 78
    0x1034600540194100c2c17010800180011501c103a10107080c403004100c030300e89541c0c0e01c4400703900e0895005108200c40c0f62000400c101030b0423070b4851080b800c05074080c1080031000781d5194078003502d0311006000740144001103802c2c1401a07030b650000c0c00c041d48188130140000c2c20090041c101501c24640c510a00c04005403205200340b29407082004000c01411140116458200c100e8201034003c0e241aa43d40c00140c17041810300910f40d0003089651a03090b12860301d41400307403001840c2812480b07240400c0000810282d8007004580204400700c2e540740c860106811540058000d001039a452106111000704950b111901c120b011a40380040840941050304882850f40f50141c40f00004540303520000d01c016141e05c0401c1e54041c0d4185018082540d40b19020001d0711010343d8244d000c200d0008001210a029000c0d207904208400d5448100c14508119117130780707100314443d1080342ca011501003051982d507035990400954102c00559100d04001c08401880c03502841a20003091602c0041c1070325 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 48136586 1250 48135336 48135349
    0x71109060105040314010e03071202010b0409110904051f0b030705040b0916020a1a0f090a0c0b0c0106030204020a08010e100f09020c011b020d020c0a080607030209130623 75
    0x152010b95805052030700c0d41d912403099082079000c0e00119522619000003070030007000640400b40c001c5090201450348940d0207030854040d00c1c0001e01a80c20a800b1002003219912042412281511f10004603911420b1607170270100043c008031240e000130180042c0303a0303419030007042c6148011820307900702c956100108000c40b407042c00742a03000385003840052800c0104c222040085129801a01c404021341da8619002400b25101e00180b05070b01e0b401c0c0607080b0303006050b165000c00f03543c008284866294540011551061144c0000e4800c00070f44044c12400a402010055038090f1040d92100018000070301007013024020700d0304003500ca00001d03601f41c00c0040d000c0100e500301e0020015840c1010f5041020354800d0350034043c259203c10074241606a00c1845100e10348455002d0a42e841126000904004501320640d00c203e02d224014024400046410390300107280742001a40c1300703800c401141444c0501058403403600e26000380010710140e0850880813100003500070205080c90030040088 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 48137836 1250 48136586 48136591
    0x1e02030403080901033e090907030207170a080a180320070b030c0304050115180203040602120a090210030207031205090c060c0c0108100b030403030f020423100305010e1303051b0102071109 83
    0x5004c8c65000125900702e0003a0b004010036406242400b0b442845002031031f645500c0b0321500800602c0d40020884254000d21800d001c10100d18001c843c1c0e08400c0d200103040c8040300b504a16100a00d1001740268401000014018020014610348a10300104d14450580088400340d603f0350030312620015005808001e030050351410b0603132003000031049581000a400c010011101aa0300300151000e0032203a41c1c42610542c0e2014010070110864810f011004c050743c044581814018440d00300000d0700482186800856a500010607584d69484185414040740741581c100000052005410402040903c803402d42038851590544070b40041c0c4500490b03911541001007170038004900002d00c20f800c908001040c204015051540310511491040c15132012034881d103d08410300030480c1804100001401d0790703400c040020358506005282003210061280400c43c801845003010540100150b45071109000c00c1c001e06104c014140340d0003540030707840c02c0d5040311402c0c00300c0c82549009440d051 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 48139086 1250 48137836 48137839
    0xa0c020c0102070306020a0212030a0c1206120209060303040312110705030d080a0e07030c060905190e0106050f071a180a08041505040803070804061e02030403080901033e09 76
    0x400f20f140d40c44500080d044055040114050400404002c1c1c3c0000059400380d504000005100c490003140030304100d58028550181c5c5041c110100041c0c6044603d4001c2c1580550302441541d0700e0b400024114031450704018044080e07142d40c00b1269a205014a80c0000402c007201c0700f050316881010f075100d0392044981c00050105000aa44035003680000396048031103800c4400460302ca80d196000002d035604090006138401000300b00c50310b0591140403910f000c02c4409804541486c010314991241402800c05016000031a890981d240000301e504e2a83c00030340c60721040000b00040d096001c0183c4091207580d1079004103032000c590200d003503130299901004491400c0d00d80441c1c14406c20749101c80c002402000d20002845c99414002441000d21450f01c07550740714100388000d800660070000c40303030a4032030324000884020b40010460301a07a0700408220f88a1145c1c070f004070007410000d150380c1005181c1e02039181007240c0503000c9141031440014100444494074503c001503010721444c07179 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 48140336 1250 48139086 48139093
    0x30b030d03020a170901052a0702040506130f021905031512070306021305090115050a0318020d0c03030201050601050a020615060f0a0809161503050a02041802030a0c020c0102 77
    0x201955019a0003008050214148074080e07800c0ea8030483d8030708404407941040d40c5d440f07d003081f1845440780407540c49480d8141c91075a0311249100c60303044c07500540310024040c6e50340310040780d2280c0d5074034030b058240310140000780081c00b00503814030080d4001100c17589141210420381121a4016401c2c2ca105407003642590065400310000c10852002a2034051411700495802001064140c002080300056000074031103481d00d05030500504070300582c440c10701a42400c1c04162015032084c2180c102032214a000f08a8200100c140c15010f14540c10095000740102c489808010148801008580c002d400801069950600544152103583e1549005801c1540064041e202e1440900800d950240200e03003490b45100c07501e6919400841c000b808904a0020400848410821a03045421502c400300d0924600309040d8003a11448403074000707040d201d000103042898190b064800030100082e2a640344140e0200b468025403003507420000346405d00c4c110310442030000030000e2450b40c060307004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 48141586 1250 48140336 48140353
    0x304020904031101020c010b09011a0a0e030c040606020105060a0902030c0708030405100204030b09070f0303090b071505100f0806010609170c100806090901060b0d090501180b010312030b03 83
    0x810080d404014411018032000c00740c2d110f038504013440540440ba440e84000a440c40c1c0c40410840300000c164080c00e14440b40d20015003020300410709a40320503805040a241c084090380000b4102040e014125812a280180001d00305905400090190a0558290030fa40e1f4603410880280c0c4811110140d44d40c0007000100009160a4021580140a123054441e2400c1184803101640d000303500c1034403c1a160414450361200174010300e0001e00d4840c807413070100d914694014040001134480c500b2071315070100e00342d0240a000104003003e0703807900c0420801341c9880d183d52144205280104885002050000300f007032800000d406040c0d50311604c0c4c2c128203901c2d207802f00310304412036040000740d400b03020b84903559034440c0002d03034a5000c0c09840300840d0f40381810a0042165004003545802e0f07061101c200202c3c9900811146521141c2d5000b0407880c0c09401c0072400b4102c102d44a60094021011100500c080000c00e40e041c3c903c00c0c0801c201c0540014800c42c1a983c0308281954140c000110 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 48142836 1250 48141586 48141589
    0x90b09090c1003021201031214091e0d02040c03061e0302130b0109031a01050414130b1008060a05010305011d06010605180d0b040c0909050a02090711060a0207050607030b0105030402 80
    0xa0041050080c500546400800d440170f01064200303030310480b0300704035852065a0264011001c1c1020450040585041c00f54100001c1d040011552070b401e6101303500da2202d00c1b16141d80c514001c482e50050014015031140d02c2c001401000c6610588109000030610390041c032526040b400d04498006108441c1c0b25440c12409000381400da2f0070a0612100c402c0c000001241008203042c00a01905d640c1c0342d0303614140a200c1a02c0102c0b406140745907032081001802d621480340302c6000340d007040004400341d070b41d0203407210022455000b0031a503209403230403c641720700031350000c5059a224200900484008442c444520151070000300c40c2604540b00510000384034401401402d0841d00044020a00340408690103142695040c1c51003d030340c004000c1805592507030310b402002c0d030070820030186001381c583d140c441d10013000003481104c18001044040d846908030351314008050060b6065820601e841c00000d501281003211980120400140031034040c1c85140619107040c0c484a19540c9ca550 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 48144086 1250 48142836 48142849
    0x207061409010201091406010f050109080a030f02010e01020c0105180703082b0504030201141f06080a0207020307060507051204061b06110406030f06080c030a0206160f0309090b09090c 81
    0x1c5120b81107660781d0b4413500200e41c1c070b40401c810705a814000341c0f8241d414210700b1106900c42d80c200340d061042c0f14408000b000d200051041030140c151500740603018035100102d014000400c1403400c00e60002c01c014030041410f500c018014000c090050345600030008055440d00032500c4003810080d000c1c4200022400c4103810042c00e403d880400d0800e50103c0c1c90740c0710131680f05440580041c0e54860b21041d000c0603894403590014210205c0c80d244822000c1741c0c4031148070b1402443e04000e594000f0920060094050b6185141e00400341e0324150740b40e510081c07054224080035902845241100d468083c5403e08407402d41d0090b50340d400301004900340780080d04182c8a01154035999070210048000c201c200617101800c5035030f03004610b44170403242c5c0405594080d0050295034008140c2c590031581c00180016083c0d0341511029156407420080b003054a503030810103008114015031303510801d98024400c005075011031004228502840080c0b2400703440071a003105407948a4540c0c2d0030070b0718018 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 48145336 1250 48144086 48144097
    0x8060619062001090803070e0a0f0501030b0604050402070803190b090c0c150702070810021204030c020d0501090305030f0906060906130e12090a0b03040b1b0c010203070806010f02070614 82
    0x80d0401e0300500442c41402c45142c1181035030b10710000700030f218541c1d52140112409a4044035606007c604058180351000c0e15803203050f051507600c50301c002071504c0b824160750003410010801c40d00d40c01c0c1070501c1d1249900890304030a02540c03840b241c030010300301485850350744100604281100d5580f0080e01001d41c0c00707000511880c0c8210643c9e40d048102c0e017400603200b412903901404100f85800b5505180c1b0515086840485005200c003506c0c10300e110442c15480354051900e4a00e80f0500c1c0041403011185410141c540d50a040740882070680000085005800b219113165142d5980045251a40410b403151075101452801042e41c83ca0f004012401d14404032a00241035100c00f64240d00e05100048409040c00380440c1440080c6800e0544500a04400386030034a1840c0c40d070b40b0300c241c0400040190744042198841980c0d501c0c182401c0c0c55039065000003c40d940e040c24080905508030894500f40020f6034801d01c00e0201d8800b140c0c110031103003151500c0b07403013605801c040403094021 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 48146586 1250 48145336 48145367
    0x503040503251515050121020a1107030f0309050d0201200f0d02070305162414070b09281e0c0b040602010c09060e0609030c0909070806061906 63
    0x22400b450021440e0110503107514000140c0028440150605040b405005980124180820402003281d040c0301c008018040c1c2a90741801699072182e032100703840d42c011900300b200c042d2044490102c01c101850400a1949001c0e40b54400005d950700200041b00171204002070014001130303079400c200003414160003000108031040c0e802c05500a1100c43c61310040c0c1ca43c0341c0040e4003c2e801041400070910107042c0c0c41d2414000400300034104841d09100140407429244401d60152031284500e22448010011208440c0e200d956200e02e401d04001c0244c0c140e130b4008543c0100080b8107116000021800004d02000010380d815080a45510354012594814050420050751a11001a034002001c402628240c08519151403c0a000a085944c2c2180110500001c0c250030b110b01078101806208148007112440e03510007146012a040880350030301650003000c3c0b40c0c2402070820003c05e03000161101142250035640d5400300b004140c8861a110818581016401740035991040403640d080404 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 48147836 1250 48146586 48146647
    0xa050a09080118110306041110030905060a0b040b0406080c010e04020c071716030206030402042a05040501020c15040509061c0318050909060109020915280503040503 73
    0x1d407214120b007502e0b103c6503448070300c6468007642410840024001c1c3c1c0629003e80c010017081c54680d40e1550b0010300f003040c2c0e0b4850540060f414003180e00c642c00c1541141c0c0c1c41002da070007030300300b46020b00080e2041a256a10a33410020704281505183c0700da2401c0310070a00080001c001c00200545d4008000200070b500141c0800c4445030852003004010003d00c42e042074909c48801c446a101d05047c0c80c8854490719a07100305040015a44100550341c000350119400100480e4240c0014071182c0070030401c91081e908210108179040c0c00030041c3c41110001e0b001d9420f03141a6500f00089800c2c1c1112850400a00740400e00181c24010b0015034060000340100d01c1d810902500e2921504000e2030450000702501c4114068511003404180240020b40d4064585d040c0000029224401400369000700ea034042411110350340c0e4400c100b103090040e81a540c0d40c0d40c800141e8402403140d500c40b44024210519810007280f031180040700e1040e90013801441c207141040146000100307900c440c00e06181c5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 48149086 1250 48147836 48147839
    0x902091f0b0306180f01030201080907030f08090a080105090c0109080d02060114060c06010306150f1206090606170708071205070e1b1603090501030b030322030602040b0a0e030109080a050a09 84
    0x420040c0c4c58003c14010710000029859440014200603000b0409209500304500410000c3c07203070042c08030600e912400350341d1510780b01c5001c10004440c50307004218640c209030900010480120701044482804c3c0c0c2c80c85180d80d00c82415030b5440826074001301c01688624010051440c01d03031a07059640708003c10702407030040a40d0f09030745005020b0b001a00c0300c96580411058005079240010014800d00205101c41ca1400010448199400b0406004540c881d140001042803a500c4007010b4185a01060108a440b500c0c00c2e40c0c4d92240c1c02080c40d18402c400004c6800400780341d000500ea68024010001c0900b001208801c400012303094840000c00b48a40c801005405406881c04114100450824a0003824002c01c00441031388000c2c149841d10101071010f45001c42191652425205258220018080b07121450300403944081d00d5030f840880d0100e90f80c80d04000030030003032215030347c0c0d01c1d6118000d2080600300c4600040c01003a94108100008645000d28003420094806080c10103125 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 48150336 1250 48149086 48149119
    0x90d03110102120f0a06060305130b060f03030d021305040e0a0f030306090c050903010c170604091a07030204050916120c0e0301060902040f09020403080f03060303070c08010902091f0b0306 83
    0x31107060f10313500d1101d0f4051041001c04582ca11445009041a10b4107005506103003406442c1118004400b070301c1c00088600258903600d0325019a422034a001d0100d80e550f40c004501d00009400440710508680f0b158200041c15180a010350014240014003802c410b411a98400d240541801c0c011010316444050004007141588641051888a603c41c1e660703e680340001c00d821550310410160604c01e6054050f09502c0000d6201750b0b01540580b0002450203076070801003c1d80038003850604d1246051003c102d91654160094801c0325015900950b50784c450303459035490072200d000c1e10400107000619644181106400c80d40c090449401c2c0010a418003070040380c2511000c0e0410380111360001000c0214400418200c0d00500c8070850840c01c0034116a19940c0702e200f03802c1d041031390340c00103c04160580d81c00e1003181d00c41c035440a2403800059403240707400e018102c0f41200f41d204402c1c040000b000d00301580c10804008075449403c001e501e00309014200302d900041c140d103402024500800601c13 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 48151586 1250 48150336 48150367
    0x507090e040f02130c02060105040c020304050a031a06030703080d05070c0f0f03110c03030f0c01140f0405010f090302030a08040c0b28030b09010e0402010c1520090d03110102 77
    0x70340c0c02028001003598860050100955a06010310710300f528000780b61801a038041071a034190b40b41220007040c039003071b0000c08074918060703600910741c81498540000200070b00341040300806105162002c4442c1d5a0904051f10380e4990321000c5c007600c1c030030010074000c43c01a50000c1d50200781c904042d4210110350300c9220032240d41c41e60481e41e1900c1417541e0b82c28140c114681110700e0852400406a51001c00042903c0b4043d0000892102e072010520954009003908000d0122060045200e1903160800a40356400310035582601d00d54a000303040804d4440302e00440d51495019001585081d500c42021a2101c0c00100305460b80c3c1a499008541c0e040010018448a0040700344014124502d0b8100e80d494000c14450209062600c448e0031443d40b200a186411602d44241c90085035540d030005131100c11010b0001080541008081c2c40720325001d520044002480c0c0c4081c140c0340707000b1100d092503441506075550780002400c00c8480064452050728405604850001d410301040da0380d035010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 48152836 1250 48151586 48151591
    0x50c060f10180c030e0601050102152e0611070501141303050d0306060e030708070b0c03070804170607030e0c13150e0f09030a09060c020d0c0306150b04180507090e 72
    0xc040f52954202c0740c240d40d06001d09803030001100050082545000c0c0080d6454140c20410941c090312a0001204043d00e09004440c55807841400c0c001820440410100e8a82a00a54001c2040c50402c09005440010b410060380c0060310b41d0110540c5000340782c044c68002006443c081c82030080040000b81c0300344100c80d040e0155441c04a8680c0c1000d20140540742c0c000702141c0240d1100100300700780742c3c002441100b20341c0404603c590701c1e045c1c040c206085206000018000348400503000404440140c8000c000102441c00d4650f42d0304e0306042201502d0000061241c40d031f1000008100510309410a8144000f0320040090244c242141000b0008110b0780201112000781c070402004162241d10f183d03000b40108040d51401021020140058234180148001c01560180740c1d1b046444000501e16196000404100c20f20b41c1d80c030b0018040e0035041c4010443c40888280005c4840940e41a41c007507070b801c40b00c42c02100c1c000005010080400500d40c104220100d43c000807000c2c201040c250 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 48154086 1250 48152836 48152879
    0x5030715020903010e0c060a180f060c030806091303080a090c030f0501061a0409110c0a050607030b06070c0504051e010b030405060c0a08060d020a08030c01090210050c060f10 77
    0x5882d4240a01050708444a1995080064200c02d00b00040c0384e80d89011921121001e0414000c0689501038004091116070000070840e0354103000400c0709030300f008440750b20314826034503010b0941c0c80c0024450700c01030070303101d58840d909900448400240681e84540c4d101c0e14981000500e42295100c81c01e0b900e8443d40140d0704018601f0910061040a02640010b40405201e60180d5000c80040c256a80f295208903202c103a95103440105000c041c00c101c2d071502003814200c54080d0240c0c01c2a03a2281001c0d20400040b91078085401c1160900500ba107d1560700300311000e044a00c2c003000d100250030001c1c2102c042052071507503c01c01c030070041100d501030700f00c1c10301071078503407038913281c440d1811001410000d048002400104205940807501c2031740668180c2c2c803801841080e1000c5600442a6000500030740404103050070641015070149074554000c44038a500d655613050152018842c41d81d00241701e412440c002100c4003184a134003604000404105004541d44e20148c054074a00e04582c503 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 48155336 1250 48154086 48154091
    0xc062007060507050a05040e060f10050c0d0f140d230106030506060403020915040e01050115120203040302030301051005190906031d0606040906020d1b0f02070e010b0705030715 78
    0x15001c1c40700d6032189070303445140f43c288503240812464002d8982e000344c0c41360740c1d104040940081d12039102c42544045201c80030b41070600b078080f0782c08090710301d4002070010f840902ca0011010310051280040390b01c01601604c505003050003551003001c00307030300c103d80354a4081c3c0c03100150445071140707452260405d252003000c0b00f038035410548010261100500319510943c403d200910159592a400702d4028101001c40900340c25100041406012161344c0d2080951a010000400d1844c2004800040b80540d44540311644900c280ca02240004d50700600140c0c03052006101d64100b0b0850700c2860340c00c07402d00c01e09100d891000c0c1424040c981414200082035000100320240e058041c901400440b40c91800d0089000310105560310780003000c04d4400c2e5140c110300070521810750b04a440c01c5c410381d0001d005800d0185040112006c04000440010b6410b1007182d50242c40410700030306552204d0007448099103483d940030100e1300003507410382c2c0c035000811010000540000c0318251100d0080e001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 48156586 1250 48155336 48155347
    0x50313030308010e0121110d0803071407081b101a040606030e0c01030c030609060e01140307030506010506090402040905091606050f0405040f0603080a0e100c0809010c0620 76
    0x24840032042e40860426404c010040c40382014098030542c40c40c0c44202c003c1c6c2c403800181081c200c0411035210042d044820001400b083c4006403004500c9188540c03101060345c075143c401082a845145c0c000382410b041801002846401c17420545203241c044001c554580d103840036600100c401c4c103480910b009102101c40002c50805004100060506007030420102c0f058a052548502403c600d1504041e91340100103591402a030040e005007401620420541d516003035556803946c0213014054415500e68400025442d000607418140c80d40900600400e900e0141171140b66000312840903441390b02848041410141442028440c0403018010a146a0724034170005051045030002c0c0c0402c44100100141118550200c03022100d00b6180059590341c5240f00d4801881e081e0002821508009040e690540d8018840360003014200c828281102ca041c000340d988010070807008121960a011044d03c0d90701030550b03810750070700444021843e0301d80301641804620060550000860340800d2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 48157836 1250 48156586 48156593
    0x70b0a020714010c020d0b0712090c0306050f061302181206040c17070b03060d02030703080d0608031806130509010b070b0108070e19090c030606080f0c0f1c05031303 73
    0x140140350700b402e00f410600c81401e074000c1500f0001c1d0f408003902076205407001c1510340d0700c20070220010030303c0445e04111b81e4415180140300090a8401a502e241c240740108020041140a0794040e442c020510100f0070107420400003c1d410140308e440031100f03602c0050134161100800307004481d0700e09003d40124a49468a1415084581c20401c0c01500c0f0110000120400141b00002eaa4200040c192603035200760000308017440340e450007505070051000000c00c20410201507c4074141800040c00015241d54209981e4052161080900c80c04108001d42c2d07410b0420060000d4040c1c001c44502b00764035031000c00c4001c5000e92100301e02c0600002d040092010b0690020302501801d0b01074003c10b46052002511840e000d0121101d06a58a91402c0240c015038441811950710440540765955030b8108040200f0540c412031049010720400c5000c0d180000c070324a00900402401c0c030300c140e00d80606000e00b0185440400040000e0071540740045403041000c1c02d102102d1010010a180c02e624 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 48159086 1250 48157836 48157859
    0x40b0f03070f030c020309010c0f1406190903050f030c0d15080c0d11060a02030c0d0816020c090a0e03070807080a09080a03120c050d0f09031b080d0e070b0a0207 71
    0x1a940e42c201440c00110184c1180e01000301ea17946002480c10780da9540340303401c0544600952101c010b00084a1900d416542c14000c10000c3c1700e901c94007080144020f8900801c400e0b0b8440b1000100000c01c100140c50500e01c2d500061a003104040c5c0d402d60a10240d003d2007422030b03e9080d19040e840e15501e0b0104002c2e41c00300316451040c40191100f004602450303807020400b0f00001999445081c0110320034018910070400c0e0b5041004000480d4410b0f2001140600000c03070648614a59813440201100300d9400000e400034040d0028215050355070360450b03114018051168050b282c1d0004000c04408102c0b0b40002e0002ca0340142821907460308000c01c0640000a250b02c00800d070740180000c84d0200b9004013001845941ea090081240c030032002c0e003100c1e1882207100d0800406d103050215540b55105921030940280710340c494540840d034420280072900640d0b4001080c540d410040050f2000745508894600e22040040b11100c0303845652100c1950440ac80c0d100c01a032204604214000d40d26 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 48160336 1250 48159086 48159107
    0x312060a050402070b04110103110a030c02070e16030e0c15090f04060303020a0305160b040302030309070f050d06020904140f0f0609010e0a0510030c1d0c09010203070f0503040b0f0307 81
    0x4440031484c004e80c940c0d41261062005001505211084d070740e84d4050307400b070b41000110f040f0311808959030310b03c41000034004000130307800d590040c0f150540c041000d40704010b403107002d983e0720000203500900c2c0800480c0a072450004200303403405145418003513611076980b02071094503051122a00c50000c14180300d4844030b01c0c98502e1003681401d004002007034000c1a041c04a43e01880c00560301c101c40d0414498520201b2401842100003504000506034080051402480c01d00c00b5030b030081c0c3e070354800703424028054042c2907880064000e0010010300c4650040100c0d40c0040c00c00301d101134400c0f0340d002c4040b0048900c50188400c4208004154401c0965180d00c081c04031030703404003541044000f5104010007021540c50566035000705031103181e001d19580041d6808a000840c443e11605562200701c00b106200041c104100c0116006003a44401c0e510619410307030045060000c1c41d101c040f404203942d00e0541d414002040013184040c081c100a0100300f075078840e51541d83c14200c10080400c4d080 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 48161586 1250 48160336 48160339
    0x80d23091005130b0f130206070f0b06040905070b1303050607030209100203160602090d0507031b050d0b040602072f0a06030207030e120f0105090106140901030507031e050312060a05 80
    0x240f400d0600060060342d11140c100d80e044484003e5550f0b43c80b504040580706a1002e540402d020600034100099140e50700e541e20f1158a2000c40b685960040c0425900c40c00e00081c03007900206014000700c10094081c01d043d40b07000a0929003150b50780c4405007071410a5842000103500090b40140700d080c60000302001d10076502c015450f140c20340080d886d200c07034058802081540c00059400095590708601c01440782c003c0d040d42c0000765640381000d5000302001555000c80354401c030000e403610380225940d0016410517003503011a0b95035a6550000e50003000d08440d041940500341c1a901c030004450789041b07062403000c010080242c0100701c400b021360b9020314200350040064000080d8040050080c0010030b952021802031135040361414801c003012040003a42c070f0a01001140da405400c00012941304880e4002c50020540a200c81c7c0d041c2400080d02c04e0340078070020000251111a811801c0140c00109900c020560361094110740c80303007040340030702c074005414410a8503042034070350b004110 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 48162836 1250 48161586 48161611
    0x501050a05090f0f1b030f0f090c0a05130608070311031203060d02041509020a0e0a05030102120f1b0c030309012901050c03120903030a050105010309080d23091005 72
    0xc1605041c0b00000c001009000d80780c41340008540000083c500200036068401d2102d900d9143c256150102014120780c0c4845c100d6420300030646950000c6031241c122603000d850355240740c2c1000d00384070014840ea0a580d4115944510004260340c040c06111b000c2d61245010046200c029810145442180791145048002c200144202540c5100054852541c16500412041745001d1020a141859801185907a000061603140345a1101d5400c807081021906500302c26110000d240c00c078010400c03a040d00d54001c0d0b000c58080d101803e00c0c6940f00640b40c0c40070040d0510325034202aa5080025921a90750020051140e10a800e008101c90b002110942d003521452034a034890031042c008050b1810301000169140b00d544041c800c9541e8030b101c280c0150074604100000c20380e603500441d8620324989c036010002c24113612a0291504264000241c1030800805074820340080c0701c0310720300c4c55070201c2c8034442140b1070f81c103035401c148140d40003005032040c01000036540c004c1e034200910702c0e00c6256 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 48164086 1250 48162836 48162841
    0x1050f072c0d030c06050a020d0e01052211060a0c0521040b0f0c010e0a03021002030103020105030414031b01150605040506070303050702030c030c010207031d030606010e0d020909010501050a0509 86
    0x119007210604504508464092000286040c1680d03c0c080500d80503000a00300001c0207200c00c5030360024036a07610382c5101003280e8004000c02c0c500300e4034140d4003940104110f2120741501c6d585030642280307450090340c2e521080c40303c0030300089041d0300284092001c104068001402e002d030500c600700c884c40040c1640c81c2d41e0b6040e5450740b580791003507000301d86c500f08020400380100c468079400e0b0b403c0d4064801c02000600085007007940c0d520030905c0100c005120340c007a401c001c100d4a0003600c0c101e03079060310382c1800c5465035905c40c51883d1040c06c0d42901c0c4d11040c88064008230403818035902050000f0000280b60312210440080401c85400480901404200400483e180c00303040740c481941524000899880b0b00b041203041d481031805000e400d2102003048041c0310300660003000390a00c40d0701c0360480844030401602c0040d4a40418a60641103c0c002030403d5000ba41000001003004002068641850703002030000e207020381d031203901a903482e00107100d01c7c201080a42c01404c4115072250052 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 48165336 1250 48164086 48164147
    0x10902030705041107060e03030a061a071101030b101d0604230a050306101e060c1202190b01050a05010201020306030709090f020d0311070b0c0d030b1201050f07 71
    0x600399442110f01599039014035101c0020208161100c042c0d01820501503074451500c0030b50b4a40042e200b0203c1e0901d06000091002c043c0c00140c911445d441000900b40a401e0b103990300104005400c1720f040c95242c0e101140c0c15a00c00313014602c40c40b07580d02ea00301403048544215140002d070004042c014607080005005c0400d10f02121800c204c10341451b10507500b2840041410394103241d01050f00761095030113000061403c40d02030000e0301c41c0a082840314640010490140100c1441404c02260b07070300d4400004240f40310740400304444c0d940122031082e50800000541c0d040c0b051b6058a000202c240180300c207140021070340c0300a1009100039820b505121001030303100c600c80c2c442d030004240c1da40e12440030062032103140c05040c1c5d0001d02c124681045410050311951002c4201c00241c014a2008142098014181c59030102401c0003013200e1a90910b0507002090014201a8059000e241d1710300310407400d01406110344241d4941000343d0800d01c002810014019581501003a807001a08268 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 48166586 1250 48165336 48165343
    0xe120a080304020d060608100507030c0c15060b03070905090c03220c08060f040201030b0307030b01150504080102040801090309060c02060a0302030403030b1906020f060118020309030408150106030e01090203 91
    0x1600d42200003681d03207450b18030010b802c8580160004080c00c1c1440030016402801291050201d0f185110070300c4240d07030741c400c11030440b2103007140e07070f00420030340c2e8039040100e04145d2021103c10100c0b60002141520b032424913005800c2103d8000014110b51030074030007403c0100700b00f50802c52b003a00d428154180580c0c00e007803a0346800080c4d81c5402154000205000421803004d00230501c80d030a407442410074600000300742404440c240d000c02e060030440089810001100011281c01070b03030821240c1d0070100c500b030190b5201103200080203814000443c04440c02c2c401400203080c0e400c0000348145141c41c1c05013040b80c5035030000061150440034240581c55201c1200c4d1060500d14005903251740c2c6140980060074507906242e00030402c48004007004803106415802d444d03641d0200c48406940501c0503948440074025410080c0c0b00310065402440c454002d581c00194800c203a070f04158940b49030380d180c42ca1504000308e040e0540f400401c82d142d014407440004032003060082c010780300a900802d03903 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 48167836 1250 48166586 48166603
    0x3100302011103040902130f06020d0c03050a0e0a080d0201110703050d050406091a091905070306091a0405030301140609181b1206030610030506041202100e0a030e12 73
    0x6120b00030701c40e65400001441103c0c060710301031404644400c0b91414030f952850450256613001101d01c81c000c282c0c03d00018101c102c03216a0742d541c50300c02e4602e660459064110f049082d041c4102d03008958141e660300d01034a00500150002032611454089001382507645a0319010045482009842d0210350b0220440318a40c00d61139001c142606c42e841c102c8003c012580014000750200e170fa03500c92403c00314a15500510f0410112a12150150f010b9683c51204910007000390307110050402c0003a18a41104501e00c0c02103101d00d40750b0b00340240010b1810011981111580c200100510034140071010261030303c10b05a41040c146070303600e80032039030360769184885281d007181d10320014006901c40c0000c0c0340c04c1c40013440d00329110400d0500c4003540e4442914828070a0258100154881403036940b03001c01c980e0480d006000c1511642c641b40c5174503c030f0303144803070840c004c11022960f1010b180c003030b551043d00c0005c01894102d9007070800822114902d620640320b4441004204010b20002982d01c4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 48169086 1250 48167836 48167839
    0x9180708070305070504051201090b0907060903020f03010b040509030a0f0f0801060806130e0309090612070b07030e21060609090304090b010306080607030504020901080d02030a050702060d090c05030d0503100302 93
    0x10f40d511088030a4030030707011710b0744500e0384444d0b040004586d020064201d01c07200c3e4801d0300350001c151210801c4c1303074650496020f0100040d256100410161034441901d11020a01600002d18411403801050076503004850780401540002030030100b0030ba111403160805180361074203820044000e50000d059841c184981d0081043c0390020075142c0d5118a041440d011507080200320310b04480121680f240c000f041d0080c4240508000180d1f581070000303480343c884251030b01405040d401c0520050361038016241c01c0d0100701c5081c50b0814141c4920030a48103c4a41d07a80101030b034841c0788645071400000070030407806040300c90144004a20b000094600380c1e03c00d141c0c0480c00d0604c0c500101d0040030198480b2810f0720495003845070040c3c00d0350005025500076907000c1007503a01d81082a80d04c4451040392001030348204200e44030184a0000340014902c0104658a4138000750081b0b0240e030181e510580310010844420824ad2604201d2029003401c5800d080e811845e10003031020b050081440041d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 48170336 1250 48169086 48169091
    0x20a051507020118031e030b0303161b090b1302090d03140d0203010b030703050106050a050a1803020306040b1603090b15180f0106090b09030c011103040503070605091807080703 78
    0x645190b00030340001c0c80240c9039084040100010382002054201080400049240c0f07030059115418403034000e94900300701c054000c610708401250b00003416604801d050318421280140340c5904c0c160804400010f005480780403d41c16041800c1000701c84505124034210f52040110000715211004020689501410315944032b0602c0008000d0602c40d024402e603003944000004221114014040c5001e45441d9030100416070301c3c3e0304250307a240f0070491045c012070818001043c81c0d900c1240119114680000da04a400341c0c0c03540401d20306034040d0740844980c926a0100305000b494411080d105402d03a01c0e0a0107550141c0c1c403100030801000d04050210400c03600c01e50700315180c10340304100e0820700c0314148909180c01500343c880d1590071301030742002680291001440c030284005a5801d1080100503100a0708260015154003913a040146c4482c002031000043c9950103001d460001d00040d102c596544545004005045c240704040d4540740a6040500c42407541c41030003c3d510007000e0400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 48171586 1250 48170336 48170341
    0xc03060f091b070c03060c021f050c0d02121506130303111203072d2109060f0f06090501030f080703050c06011409090607020c060708040315060f06020a0515 69
    0x74001c5280b94019000d240c039500007584402c201561a00c03a0450380100d108001020341940205e0b2501402c240b65600b43c521110b420040080d10b41c03045400560840805107010714048262060380c2000c50080a2408000d04000000c0f100c544003040601c0300f210000d01d04140440f8403108088070307002c094200030f080c0101d242d90402c2044019281c81044c5107507612440c0044004204a181c007002c0003004026864110203c582d9007400900490103803211001e2400801c480311030340800300c0c0d034000b1094840040a0104851b4850b03032103205003010340402e071061688951000c2e41c174607921440b030107450309004102260140150080e0150b00003513103507654600c0d050840355801007001c2e1040038040c1c9800003400d03852940c003070540754009461500c11959042001503d6840869040002d40c1120f10040c00303a01d05070004100483c07040e0030080c14a910303a2144140036004a42c0b44101e6a90b61106101843c02900152f006160502c01007859400555829803503a0354401c4007041070981201 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 48172836 1250 48171586 48171601
    0x4090e01020706020c0c0112020304150506031e01060609051801050126070c1202160608070c1b1706010305030d18120f080106030c0503040b090c030f070503060c03060f09 75
    0x465190301d40000003517464078148200c1644820203a0b1929002c6151245160009101402560301c903582041c0148202c0c132203c240c18014082c0100450303850b0140080d03059418801d0040440c4a8402c0b1000060342c50030b000000d0220312260f046548983c22784014420b0700040c000815040d10020b02c0d1150b0303010300741c03040007414600390741d142003c03101146c0401c114690b00084441c401405980303040000000640160307206e4411048440c0a500c20010030f020940c003401e03003d500300640d4541059449900d40b200021181030300150081d1b0001e001e000c000c0b008034200c4100d1446241400f400e01545140c3c0d0b420b90360311031030055204898950540401c000b00f029051015180c010303902c0c4680c01c03000c50000305443c200c0300490340498042c0d0008a03140c0c0c440e2041580d5200252141480c540303454031391200c0c04600402c190740900c5606011101c2c0c1d101030080c1441040c0010040c222039060004150030840d00074502080410140300300401640d5501c01c1c80100700080d41c6d80e6120303458509 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 48174086 1250 48172836 48172841
    0x10e060d0209030a1509060501170a0201030b011107081507030c17061801060e090a0c02030f0904020c0f0706020f0115050f010c020306150a0b07080715090b181009050304090e01 78
    0x10b4590000781e05c03a41c21250160300280c2d62641301b01c204216580c0c868503c2110624100300152045e405200be041c0154003030303404003107148014140310900a02c0b40e80602e160030103a0300321081c0c90f04194200c0c210956004080ca0300941c00b8101401501c0c0340643c014011080004154884203071103010620b2606c40c80e41204045080500c040d90703e6841d254041d280506200145000c0d4510030300113050345005100d036000c540021744c0598074029040312400030700c0d046403203100d500c103a00700100400b0907410481c0c643c0000408000e00080ca00c0d100004e4200714590640a5150b41001d24101f1301039404102c3d1002d66004550412421030858012202c000003110020342511441d428006c0c00b032412203007458040012584c10b1040f540303404503410307140100840100000803c9c400c140006002d000007a10302c075443e950010348007007542c6401445420a03907459883d10311118084801140c140018000c01a504001b1300800143e566901c6d60b03441b0f68070514800326900d24103420022800e4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 48175336 1250 48174086 48174103
    0x7091a010822020603011d07020c010503010501030b040b040203180f03030112080a170f012105060a020319020304080304030e03060f0402040e010e070b0c06010510080402060a0903050607030605010e010e060d020903 94
    0x18181c19200d40e11005904022410047c41c000c42d0f00070742c0005440f840c80000c8a4942c0356069481030309503441c020065010b07010380c5251690154030303031010202640701d81c8043c1d8400c007403030030410200c841d10803003ca081c03106000340e00c46aa04200010300003c00c2e210100081a41e004145641d43e40c0311420840303802140401d1003200c086c82105000c6410340825066058804100360000526a0700080307944800e00c1240040180d045900050031240e401e0340a941d10950b030401070329050140c0e208100480c3d000b114219031100c804014081450b80c403025212920206400403c0c2a040c501103400d030340140244004c2c800c5488000c4000041001e410600c6403018820842d15040d0315560320200541105441c2100c6224500000601c1c0c80c028801c0110a412502d46001c161aa5024403196500203c01c0030188010f200c00000003900401810340710703011503940091520300300000106800700281200d030410106501410b940e95501085807550380e106940160740301d51080c0840d0910340b90 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 48176586 1250 48175336 48175339
    0x20d060e0d0c031806090905130209010609090f1806090201020309030f03040302090906060d0f02040605060f0c010b150a0c050a0b070c150203010f1413050907091a01082202 76
    0xc044120508a4005041d4000103200f91914290102e104d500031142044030301c039680000c1c40f5240c040101e1b480c1544003075000018080781c4e40f6a400305402050b0f9418007030f806000004e414030740030820004035100741c520380a02840140001c01c1d064002c1d45140e01800c0003e4002ca903503d0b2035500710380c020021258943c1c0c016080d0307010038038801c02ca50344980207032109034010b44143c0e00280001001013000340c8107050081003401452540c1d01c0e44054202601400c036041541d8020105039980d4800c050154607280c038030140e5880602d501003d081d0b80c40300da0210300450140242244400491003903680b591042e260442000e9005c1c14200e24040180d103003d015184000309010507903a000f00c2449116000d1400d102400703003141c10440c121b100900c200c0f040700500c0c00051000346144d070690784c203104c0000c11511854441601c00c00403608117450182d02d41c2d00c132840070031080203980540d036140490004414460b0705070000183c0a61001885055000c60445008000e0000d038030625190580 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 48177836 1250 48176586 48176593
    0x50a090906090906050901090506010e04080403061404061805030f0c0109060207050a0308070e0609010503090309031e0c01051e030601050403050a03090609150c1104110c03070303060b0c030403020d060e 89
    0x2038520300e8000905a040c0c05139003081c14000020000e0a0502403030a141c3d500000a21030740c1c1c6040700d05d610703000020700f017220030341e030704000000c0400e03078500541c44001040149a00c0a082614114088490360390203800d800c0040c0c2001c0c0007180012007034035000c140c80d100f0703103544001e48000a4010300c09000020541c6202140701c074240708000802002040c82502c54110f1a111034505883c880388000d04554014400c006140c20380d4410340255400590250071a07081c684400c002078204074440f0114512011200c8200890310010090002c035650f00b801d140d45005800094250340201454403000c160000101007601a40701c1c0b8226402550480305480745080c591a0045c06543d0503ca40000202002c00124440c24120610302410311f064481c4003900307219668540100800b40d641950141c3c8c0c0b4a200d900d580981c200034541c039200e0a000d96529403051034080c00f1101c154000030100d850901c003403244200b00004a42c00d42e901110b41c10f1640da40c6190040141c43d01c04c025410502 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 48179086 1250 48177836 48177839
    0xb0906090406080d180f0b090409020d050a0510111b070f03031d0405010501020a020d020f0a0303030510140d1401020d020d0507090b031303030e0708070e090705040c0c0201050a090906 81
    0x843c0880c51050000e007030b0b503c46000305a518090064604180a91011216109002c0080c40b01203002400c0e50b000c083c102241b00102c40d000103412400240b020784894029415207001c1002c2441500320f24a0140702c1000902040482a10140102da51b40300c1e00e03003003851451040b80d008009020040c4081c900c058280750301ca02c1c00038a868040c190280780c000c52000070049074545801443d05840040e40100407114468003006103180b02e9980a030307000b51743c481c40d1300d100d40c0300c10107000d02460090f180824a400c044142c0350720390b0b6031940000e00089414940c0e030520741c4d07413403080c031010350700700c0d070003070b05c0f800e2484101402446410400d034034181c0b001035a03080115244d00b10070f1183d141920b510600c1c1d0f80d110501e00390b910042388c00e9100b80c00724400d01c200007030003503020380d00030582507084901644d02c0d5480e0b980b0303200e22034116400071a40b0f00200640b240c010000d0340040c0c08181e03000d1002910011003d03202a40d580c90003030502c0300105903450518450705011b00144501e020510445c5d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 48180336 1250 48179086 48179099
    0x10031b030b07052101030209151206070c1e11010c0305090a12020108070c081b0a0501090501090c06050a021c05070c1715040c27090308101d010b0906090406 69
    0x550040741d58401600c1c5840900013021441416203048980142c20554076684a08001d060742440c0c192a541c00701005400380b0440004003c503502c81e14090300c800070b4000d51410280c006400441100c00036040d050b011000282d8200380b2040c5008003070030080414000c514040d101801449109034000b000901c0000f10100c043c100d2200fa24005e8950742c0c15a11501300032189a88d0428003e44800820081c00400c884143c40103640a480b40064030f101c2072040c0e98075400d68484050940e090f81d1100c00c90001e0004405c44840102242d003040751070030340003d0010303486283c1c195280145102042c40c18084601401c102d03041c942e4170100d038900301600c50344054a010841820b461540c0b08150402200e0b1100e6410240900e4011810401d020319002c910503c9140070f084c0e420055880025100000107a802041c1400388281c5600c0c082c1c3c513007012410b151100360340c001034052280700794480c2240502d2030b525040d42d840311030455035414104045507103445501c0400f90064944180040d06 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 48181586 1250 48180336 48180347
    0x51b010c080601080a021603140c0109060b1c05060a0b0f090a0510060302270d0b01090c0807080c030f06060405030313050301050a0c08010603200403080a1710031b030b07 75
    0x82c42c0242c032245a503491344a0900101d014034816100b080e40c10a44a0001c40d014002c02061001c203a1405031401e6074411050f429501009021122243c85142a180310b14044001c42e401562040c04040503200319240c0d0303542c421014020b490450341c0c54500540d5522143e40540c002e441c090003034542420492504002002c0481c0c0c0c0c0e4603800282d41740031905501c01d0084420b000d0524512440c5c10035107075011641710303115150080d400308055540310002545030701e130503009001a060005076400184c0d00605449001410481001640c0040140350001d450075690042d038200c806000d9030341d0b45408250140f0440d00000d038148808100c00c6403410b0401e40381000d44000390024003464540071542c10580b43c05000c03446c04174030001d0051010314440d9120703500410240381170004130500e40820f509190700c9034100341e81d007210000b05518603035000040035503442c0c1051310004da0b03460945007004488849020041c01205400602c6034000e1a45440202441c1c01021104290401c1c0c40301820 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 48182836 1250 48181586 48181591
    0xa080a05130e10032a150206010602121204020121060501030e03030402101d0a030f02031618020a02030c0105150117093d0c09080c0f01051b010c08 65
    0x490500c0c04001003204929a03803054010104004018101402c41d501d008002c80380081c1207408401a2488016001c2c03584401001001402c544911507040c1c210001c8c20042c058000c4019507128074801c80402d00000212041e03074454010000140e142da100403900020ba8021500d1145600c65a4200803003696026508440c400d0b00c00b001032100461401d9280d000841740030394007030040c40c0c4d40c80c00a4010200b4040e8400b03848110700d9910f41d0500003d0098080e600140c626410707601b074550450904004480d43d007000c45024808281c500542000000f0781440d40a20054002c1043e1707017841d00820070b81d80c49000e402c2c0288021716019465244802001c100180007506501c030700300060140394251170007451014007404101c1e03441800303001015605a07166180c03070318142031007500f52180d02255441c41d501840105028008190040620280e500148059000701119039615a10030074001072900087c01e02a840d000003007615054500040144c02c119420500307608034a940c041041407 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 48184086 1250 48182836 48182857
    0xf010503060703140414031905090324130c0e01091b030509070329010e06180403020709050c0c0d0801050405060102030c060417120108210301141207080f0615031f0b030a080a05 78
    0x1200043d00c40d60f00705a009030f2285500c4cc8084101c0031500c010304140c00c45009500401c209046030307039140c0d5004d1204400b60300c00b9803c1603859600c6100e0b09885590440d040d166840c0501c02800e0203071009448801c80d210050035455007482003840c000a03d0080241c0400c0002c00f0802e541e5200300c1c010642008489031031090005412810b0b10320710b000d810600854060307000705625070900000400a010150990b410144280304100500300c0820002049040b15a60800346500d0a0184401d848010b07200e28159001440724101c030402c002421a402038211410800502d42e5000d0352b00711b8440c0390100d1001e10144000441c01c0080060500d10702100c043c1c20300111554909200e0840c00203004880380c8501200366940c2a10b03010348032035416801d01c03095072091a0f80e40a640c0c90b04031b412950342940e4000c0d000700a090f030009078002c80b050b10207030017824484041981240c10111090140d49040c4d5807203c070421541c4003042205003441e808100c407640d89882e1180075015070450611300 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 48185336 1250 48184086 48184093
    0xc0315090e0111040b03010b03040201020106031202100509030a050a03021305040908041404060302152a0a1502040b19020109080a05040302120106030b0109020711090f0105030607031404140319050903 88
    0x82c00c0d0f0481c1c0341103804440c4018545400c0d642059076015450f4400340080c5e04540d200c400210100e803102211f07a104091a400038154640d40e0001242a90801000c41000e90028042802c9050300311084412014807454016a56141c1141301d0702d100119400080d042850308800c0c0003040300e081d00410039140d52102d00078480382c0a01c00c01c400d6685078000290054484852a40060520030282409491011031a20b002007c00b440240f00660840b10001a41c00b41041034184407840107d00d004000b05007095240c642013581180301c0344a0b000070ba070500c0031140c9820030010700c01e50080c0040c5500a8280340e6400301070800803d41e4110380826481240c8900b0280c84448051280004480e48500101c5040c3e19001d000002504070f8807096806080c05007081c140c40d618400d51750f03c14100000b6005c1d00b94107203001d0600c6e114004009006143c5041c2910096035024180150300c2603000328030980300b100d020010b03030450040c216504d905800c9500c000c0d4985030040080c01400405038201e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 48186586 1250 48185336 48185351
    0x40314060105030c090604180507061704020906010e06040e0a021306020d020d0e0f03190515040b0103080901171008010c0201020a0c020f040b09070302090901270c0315090e01 77
    0x8594484800780b1446605612140700d00080d070500d01081076100c180140002109528010031644543c0403140880d80c0e50001071042c480035070868510420101c000010b049203103001e40c003095140a020b010300e0705000c402d100c4070041e81d8405085401820a40100000c10304008104078041e4100600303c6402040100021840c9840000d404089464540c001c00759800800d000391100c0e9a03c0360801c0d0002508030090140d91810041c1c2004101d15100c1c141114074981440e508001800301c00903d03403041c00003130101264911f83c410381940d07001f03030806aa46401030010b0304d0f0038100e09100a010111401009103681114403a4411a40503034000c1c0400b07500007204900b00e1003400180004a0040500c0c1c0c4050300301010f80c0942e6410260000aa20b80b14100203114440120380c2c40f400203800160702041030030081055801440321100d1080f26020540642800442d088511080b8a03500c603003424040b4031907000707125202c80c21425408900c0d00d03480302c10007420843c22200e9940d07080249 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 48187836 1250 48186586 48186623
    0x1309080d0e0c330d020703021f02040305030f0d09150506030d090b041406040830070c090c0306031e020102010615020c06070c0801020d0203040b1305030d0209010c0c0b0403 76
    0x11090b68461a80c41c40c0e8400c00d03203116104803502d01c01e105080180c0300510469130700240501c0241a818082d80080c008080b18040703000c403010a580510503141d005000c10400628000191640300d001529000d0b2910b1560303040b00700400750800003400c6404c0b0703943e034801c40c4251036004500034203041e4180e03079201d110200152464407440c4500c0d030130010308210070800b40c01c00841141900100400719841c0c40d580d003d6140c50b18541003c00d0320841c40100e80b0301c0000300c54080041501c40031040071401c2c403039070342c964000b002d4541c416208800e031203130240750000c0d1095010300c0c00740d03900805e01e201184844c850105c040d400304070302b01e01661801e400496815561071982104ca8016402000c2c041890f80c20300c00c0c2a0404c0383c044407000d00f07659001c40c02d00c2081c005000b48031050711006880e4a882d080c020002180034090509000c0340c80803500104002000311400c01a004601503510314030350700122019810b41c1005000f110690001140c0c503042c690003032084034003402100a5401004a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 48189086 1250 48187836 48187849
    0xf0b09060708071b050f031b010c05120a0e100606030e060114150c060c030415050405060105150906070501050601080105033c011802010909060509061309080d0e0c 72
    0x440d0180802c4500e40080c40f00761088140380f0070964000d8540108105030394906280001100581c005500081500200451017221605e025060035009201c6c030042460042c0c07491040100c17504104c801100003540600c4c481e04041c640540c208101d503000805168180020b1a0f14095080024240000b082000c103000030014181c9280000101e400c4504104000d070761040365015001c44441440760708008a03051140500c03d10b004044503580e4941403500014010300c40d05d80b0044e492802d8184000301344001151070544905444481c00c1400414000d4241d02940350705950110001079032104001042d0440743c040e03102030301d0b107011036601c80c0d04050311141e00c0498040c11440d01c3c0301003080c0303c00100510051040c00b070101c205211a40b1a01030941e0541c0c600c0420049464800d10110f5074004400360041980b02000c00c6050309000004014200141640b03206d0901829400810b0006901ca488141e90001204d90b81e4220191504042d040841c41452680503100c2003810a00302130 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 48190336 1250 48189086 48189091
    0x5100609030b0606070609121706010c03021507021009110f040203010302060f0a050904050c0a080108030a09120c0e0106180608060105030a020a090503030f0408010b030d0f0507050c09040f0b0906 86
    0x74012180da40e510402d018445d00300c03090a44e00c0d1501c801c1004045414005508a211440e6035581079030903588032082c131000300180105040055040c400e9020039808078181035204034a2034010340342e8850410032490300300c0c141c28810300710f4030342000541003195040030041d0b8200300ba51001030b1151100c0420080b40024840a50005400c102c0306c13601d50315110050403541032900f04241410900c102003400c480c411207140121040025034103415640000500307004100c1c02c00214071704628040e004014900c58800c4c10b58485600d0355020400482804400c080c0013098110b40340366a48060082c0050040e0709081e9080881e654081415132041e800b1a201e1141030316000d1468403910100740c000c0d8070001d454001c2290b031400c04507030f541c0c0520040c6444003da02e04251914100868142100c4452a02c184254801014044032036000143c00c8a101040e0a00303944440c007074209a0309000c0c0c614075066120740302404100070805070000d2150080e0144609122690701c40c1d02041c0d0700c00c003d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 48191586 1250 48190336 48190343
    0x80322050307051c0f030306210201021903051b0607110d0c030c020d0b0a05060a05040e0a0f03120905070303030609020a1416061505030606060f2712010510060903 72
    0xc1c28090000b410000390140c06018203d90a40c4e9031092503c4d0707a9840500700d5000c03000030b91195820040e025402103c020100da818600004c28191030380040c4d80c07641d203c480d401116005140840503d07008000b80d441d510146078034100c0402c00c080c082c0d40c50384000c640303440210b20450410341c110103000500320307d4143d082e00d03030328408051601c1c1130714829010301080380d0019010381070500041c012203d8a0040007040c402241030708045081085020030358020798000c0785000318103681580002100d290003600a0b429800c4040b05044c00c0741c2543c0301d4101151540e091400c014100301c40042c0132800c80e0b003c2d9804010721a00c92600c2c0c010707803080302d26040c002510500c105244502c0c20000304072152980c4001c5500340171503a950802d40c0d1606d020840c000c004000100050301302404055840082121a5880e00d2042c941e0501280240b18640802d613030200c18007400040074081565120100401c0e64004158504055000c0c200489424440394800a000075240d8054071011062703a0b0b1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 48192836 1250 48191586 48191593
    0x90d0903120c020402040503010f09170703021507021504050c04050f250302130e010e0c0705030f161e061b05070807020301020904020403120e030a0308011e08070803220503 76
    0x6400c40b500e580e8070b03070107a910550800c40002c107590240310f041d1480e00c0d44800403400e405141081d08000d4000d42d003c610a020802040d00020350200701c002c00d5080281d442d40e6547c0311060200e10b050345a0160050052200041c4401e000740010794000641c001c039000d002594441c0c0d00300c40100ea06a40201c10141908220312011042d00f40548040c80145030060134010404800d48450750704d6409000007007203400050080020b03449850398062200c07201c407483c00341e0942d90300ea40c3e07120720040c80210080c0400c40d00d141d0003c404070640321035009103039a40381390022410500d55000268045690624001115500301c0f40140903000460b202e440f0b8074100140b5464501d00b80d400340401301d038555401c00c800e00340356072a480544061409807440315001d0900c044050104102c62024600c254442241030002035840308000781034070241409003102050f01700300368402003002e420610312805506000300390224004041c244503800b82d0f80d802c1401885601600c821655800703410740640 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 48194086 1250 48192836 48192863
    0xa080408090310050a020a090e04020604270c17060906060307030f0b090a0603030206010602032701030209030604120906090b041412070e100603021602210312090d0903 74
    0x801540c003408069070040c003a0307419401c101074034804840044401000d02c6901040c0840d025a00c000c001c1e000d420307a5803850200e402c2c9a0006a8580541d2003110100d0b81c3c5903460101540e103030720050342c01d80300307006040c40039a822000c0905038002c880920407101035001d0001e9400d28120403c81c1c0034000103014103207584c95002049000c0d241140d02000704a03210040c180c80398807a000060311490b251030001a20f41e04604d4000c0c241761041c0c0c45038046510520084124250f16280c2e03e6844035088104a4140c40900050303020707001e5040c6496150040b18104000e002c03d04051034000d140716590f1410301c40c0c841c40d0603136284009000380b40042c0e800b440f06108001c02c040c0b041c449804020000d03110301c0728140485240401d90342124900804030300070710180b02e048003000340150240741400d5042040040c2d0740c025885000c0f5010f0300c9405459014491513001480c0d509580010005481d80e0b800101c846044543d03042d1914860f52007440481640c0510403010007040d2540b2114201204 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 48195336 1250 48194086 48194093
    0x70210051b070e010303090e0f0712140a0b0a270b03070b071b090902030c01181706040b010501030506031c050904090b060f04020405100302030c0c03030408041404020a0804 76
    0x1074010260302105441400d40c0009902070400011000700340349518180558154540200300300119402080c0d8500400140040006d000001c0c9600101c50302d002075042c50030220400261582e481416000e00b06001840311590b030a800603036000f10150f48074800c203070395584015034039005643c032007894000c1c18040c40c1209005402c0702689480c01070845008a480b441036186d6544418000c0f41c99940341700701150005c0e19017510000030a107244003042201c8180d00400d445040c04015a4100140e03c6501e440300c0740c0d02104200904041c2e0304002c040c41e140c4c001c4503510003081e030301620055082e0000050640c400d0042610540016016000b8040212900c02c4020300040b80001440b40a005103113894413244641030f400c50080041c40450708090b0300780040d410703810744444d018900420090009440b14150541c3d10701d55840d0044c2d880d500c445000f03035503000b15211203030180000010f00c4140241d40c405032003581c07011211a00f5985004082000301c0c07164420500100c0e95050018010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 48196586 1250 48195336 48195347
    0x130302041d0105011d09060105060706051b0c010f0510030c03081b0136080f09010210020f0a090608040b040209060112050f15010206010b090f030a060203010305010606030b0402070210 81
    0x140c00481e0885100180c07207189081d03c009801c032150b000500010802c040310068a450381145512000d401c0e42c1d4103001c081900c0d446a03180240419841e403012a60b04403805803502143c80001e01520344a42c49401258081c0c2180050b64502d241014080f40402958200c4071003100da010703264a1160f4071316601d4042940000100194004509202c2e51041c00f00b0b001d22410034080c100d04003550a550f0381801e2082400003240302d030b6002c0252100c8001a500401c4850070b403403074000142c0f07908400c40100d14040ea0003c4002040380040b91030401c0c12991405010001d2141e107402c084d25032a4602211402c2c0101c801501d8042c01ca000304015090026515402c00c41c18502540d40841942416040d41d00660303688000a0441c41017185d411000210242203800034806000c0310b52402010750320500454603401d1041c02c0c0c10544100c556410030014414951041e8190744941e984d0034000d00030290341c031070703080802c3c2803078100a064940b920071103410341c2d40100241611100e01008923130 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 48197836 1250 48196586 48196601
    0x3011208040801090b010306050903091005090a050d0503040306050c03220305040b12100902090105030f060d05060403030b0319080a140c010e011a01030b03150a020f0412020102010b0613030204 85
    0x11054020080420022030030b000380d8081390700138940940c19500d9403510b0030880d04024600c0600760400e1180840710303607440752100b04440051401c43d84aa02142c000740600005034860390f40303e02e101c100003081260110141040341d0040004100c4d07907541e01f4080d00f251200700c848518120f40000c0201140001030950a41203020742341c0140ac0036116001444603500003d4030807100303038020040103010907034646848080c1550400940c1450103000010f4400d001c0681007801844001e00000c9564941e04a21403c981e002412a1400c3c10325040c040c9c01014040c45480c02805440b0b10a1240030340d582e070082d9500c0e4800500751514041400859515203650441d90300204100700d0103514820901440e40c0510040b00005121521800b9505013480140021810f0600300a02120142d0740460b039000d00c219804440c0d002e43e690504004020320460203c1e500203403001c80c1c0401c0c0e80304da288410810300d2003a0001c1003082c56000800866020303520544040024007802440141056000302c0b5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 48199086 1250 48197836 48197843
    0x80c040b0c0c130e0c010306050f040e0a050109080406080106090b0301090216050d05040504060f080303040206030403020a021003050f0f1501120e0d051e03010e010902090d020d03051e090303030112 87
    0xa4910401c400042e040800c1c40c1418040140c8560040e5910324081c0140e17540d0840908040040a142102240c2015082802c092060740c0e00e0f204220610f0f400d00a00751001e034024001c01510886141640050f0040c3c021200007071100d400125040e401085c5c080e05482d0100c0788075055030711702001400030358030141401c0041214607600c0000280c1c2004801d650311200c1e22210f80b00e034208000d000494240c3da014044490580c5070401400030040116504990192901552940c40703082c2a03192a41d01035009401081a807240307a402074cc035034400340c011003120103090403540303442800d001181401e4032a840d110b0701e58144000c0e158007504031540e006001c81c40102d4211085854103040c041020426004141c00040c01c410303584140001e0254800761500c01400d550400500041c07040050155052140d40002c80c1a980d5481b8540e490040e0360007000c00c0180c0b00356140040c0f00e900120b007186280060f402c18180c000f00c1d0942542c03400e882c060000c5055038078091079010032601d0b126055 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 48200336 1250 48199086 48199093
    0x403030b03161809021003110f0d020403110409150509120706060509010602030a08040b0a1409010b090a0207111504170606011403070e0f030316140607080c040b0c 72
    0x21202500e051041039601481c0400c400301d0b141c5000c45903403050405100c0c9982d61482c1c102000700581e204075440003000803501d13001410050600010724507114003480040b0170380c0c0c040782c031500307500d000e070000c1c82900e100703081101d40c006059040c00280e403604a0028500308215201c0e00e2015a0755001710b03805031020085448a2000da0051403040d804002c0650b1100e481d20f00a0215041042c41c0307500510117440110b1405001c50001022014040c00c014075201314103010685414a5400c04e0814407100140140d0506009100c54024140070617803a004061036400504101214403e43d8102500a00d02c00c0c0462160010011410352852105407042001e010101c1d042c03101001c500540c240d150300600c410304020340054203075009800d05803400c0108004002d40b050707003c20074000d10700081c3c82d4035250000100000381140140e41444ca001c2c04a0f103035100c107104c03c00c1441104131000009542c5143c5588808440c1c0b100f04a40c05649511308100411880c040103000f0f107c0b0086003000d8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 48201442 1106 48200336 48200351
    0x110301050303041a0706140702061506090904050109140a030e041109040207020a0302060a020102120603030309060f0406060806070e0102010e0f0706140915070c0906120b040303 78
    0x5400014250101408100c2994000c5c0d9070300300e0740600c062145030512242c0441049044407400e0040c49940c0224415004440307005030100300c007a05c41032038101104140805400e001d80115059903031141c6c00e50115982502601c041c24a200142c00c2d1030006040040180c00703c555132038481e501c0c0130070380d66400b2014001c9409100d0161130160b00d542c054000140d000b421580065004040042c0c040e03400d6074194003d0007411412910650b154840d50300b490ba5030b0004440d80c0c0031300d0f07100b40c011811548c000801990700c548136107400700e00ba50f11800007908180007035408401180e502c0d003510421b0340e02030098090488410004041090003980402d5403070388944224414440b188010b112000503820403540d5010000c1c2152034490010380c0500e0f0300d5401008152200940c001e8041444000b60056800320f4844c150013038904541900d880030900c0c4060002c40505580f40c1d070 = true := by decide +kernel

theorem cover : BRFrame.Cov 48021586 48201442 := by
  have h0 := BRFrame.cov_init 48021586
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48021586 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 48021586 ≤ n) (h2 : n < 48201442) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
