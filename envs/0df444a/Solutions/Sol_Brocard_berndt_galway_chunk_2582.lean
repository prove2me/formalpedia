-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2582
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:08:36.707852+00:00
-- url     : https://prove2.me/submissions/5385f3a8-0f31-40c3-90d5-123e3ef418d7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 464208633 ≤ n < 464388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 464209883 1250 464208633 464208643
    0x1b041107031e120533060f0c07030503070605041203140703090302031b06011e06050a030f020f030702010209010801090501120f02180150280311040203071707030b03 73
    0xa4410300f030315041e50460502541c8010015181801c5445c11550038400d804201c16125040b180388800c6408501c01a68a41c284002d0b00219040030440c1d407178440354246403000385404c1d103040300e000701d1010201100300e000703000380b01146402240450341d5588000042d0040c04c0042c00803011030008002502c0600200d400d443d200c06902002001598104400d002881c901d0f142c000700c8220090404101284d44541110300002d1540b801003551380b070703800c00f00b4041d0190020381c0c00f60074004810020402c2d4158060a00f00400341c0c0d40d4a407990703985030080308440c42805100c0d010203030300342d44c030340810850555104058400b41c85900110804007023001005c4081c1c100b842c25568202c22181103549110502800742c5004081c03402c4407090391698281c0801420309142e8201100781c00e0a40303a503134910344044e4071a04180c078503a055400f5001803a046407a0200302c0b440c1d00128a5441141464070030b80e4810034168032100c10400c2072150800e00703070000804c0f500801d80c56004c20b030860344091107 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 464211133 1250 464209883 464209891
    0xb090409020301062303071e0312120204060e130b06030123060c030423090f19050906070906050405100c1509050c01090512071e081b041107031e1205 66
    0x281075100c140d05c101054203042c0a6031262080b480001141003000030311100d01002c582c2c1c810f071120540b101906080c4c40007102c000084000c6403020070001038440c7c209801131054101242d000b40404d4101c000d40c412982d0b48000103030851014401441040580c0d070520310b082100d000c840d180c4c540d030000080d01360350003410090050b400101d0708101c21802c1c0c0344500044410456031482806581020030440035004007100d0b01060f100c2d0110b030900da050b40c4c40041080e81911b06111501d090311030746940380402d0b2400000140c42100000300741d445002a182a50340081c04001c2c5120511401c03500d10140c7c1909648040311900f10103030100340352003013000c280e1088014080d2001d10b03c00152a1040c0307944858000c12807491440840170002c14400155007001c1303800018141c056104070440100d5030401e01207446074079840b403070022010708200202d82088400740074140e1501400c03035842c01480300040126031a00e0000d802c0e480c4850f4000740354011841c00502210701080d485c0b050b140166 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 464212383 1250 464211133 464211179
    0x6040b0403050f070512190f081207020610030830011d010b12040209071112040503120901080406020d02090411070b06030d02030f070f0f050d08100b09040902030106 73
    0x443d01c1c0400503418001035005100c11514011410f2404002d143c460301138100e5140b21001560040c0100b051819804c0d15807a0014085500d9103114100f02a650800b0340d480d50152003004005055055101c00c0c07002a240e00030350349410702c4030003802ca8402c01014291004902540030140002c1c004981070319000704034075848030800301000b01040007440301c1030300300b221124004c0200f0018001031950154102d036064820040d2591061400c8440443d0700c400000395014a05401801d845c694001d00180c60044090f20000e504021000d9024071400801d940800d400c0720026000c5044c546c0038102c0a0400300f800b600c0c0c503030344c50005402c076010403849840c050310100341202441030080120b64410000d4005016130b000125001c0d540c0d0154501001c80860000f40d04010000e2400e4020740d16a0f016884029541c1c440c50401d03114520103100c8000a0000c80015101d140c3e4622000300701c0390044a0185401c00340c1c02404098030891200340d07050b44d26114002800036014202c0c00050f1180 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 464213633 1250 464212383 464212393
    0x503030106030606140a0c15050123040501031106030705040b0f030a0c030e1e1c0503180105010f151b0c2903060906011e0207090b031c0e06040b040305 67
    0x8a0809803ca802c0b43c0c000e0000c00c13103402641c40381c0e100280308459020707280b800d05a900c5c001c145400042d5181c00d501d0302d128207041000001c2c0c2600308184510400c000250000300c8100c00b4000d0000315002403102030301c5001216540c8900b41400c100540c0c12110314a049031420f519000504031907840070519000b64030001040010032440ca02c280d00001715285028000c103a15150030540d0f40d10b034002c1868000e001d846c0e2801900c6810401c0000c00240b0b030883e00e4202410400190254004486003004071003c00c095002c941010710445068501203e105d82031103003851040000410741d20756280500c032001182805d07260a1111110308a481071100070002c90402b00b124044030400c542140714a0035a23007954044406d10400d0301c0d4044010b485041c066581c00004881c0c44c0d1700f10604054807040005031208065000c00e801d01580c1c0a18420b120740c900c00d000381030740e41c40c204820329036680c1d00196021085115017602c500c03000b4000c00312070074180c843c4e14003c465842640300300c17603035442 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 464214883 1250 464213633 464213639
    0x3161b061709031c020c01060e10050405060607080f0a030e15090d02011a240703081527040501110c0102041505040b041701090c03060507090b03130f0c1205030301 72
    0x140320351440c0c2c40b0007094051418425010032650704400d00704150029160042542c196001095201c1e000400c20070249141900348000c617502c07166903a02596026030700f40000103855062040c21100403591140c541c0d131a04045440c00381c0c154200e54050070806464981112a04d40c04000701c0b000b1085040c980402d40c2400c14000b0b00d0410000c00d15001c2da414070040c42000034000b0f00c040403001c02550800005000f40720311400028145440da03c404074007144c80d00c14542e2103021107108071840c00030060b401003094100318402c6a03001002100c1004140d11208040000700e04c103811610520011425030340305120155103400004a9a00c281e50104042103190300400c2e5801c0b9014207810940d107064100000c0f894180710390b000310641c13040170f000e0b02d1303240c69001d50090000d1504013000d42004c03a04e034034008000d00810b690b40030000d0a00040840d45411600849001c0d1414090101d0640203550305c000b0114012401a60a00c955800c001016403901442c0c0e160180f00f00061a0340f581 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 464216133 1250 464214883 464214917
    0x14040b09070509131b0c140d08090c03061003060e07230a150c08211306152919090314070b0307032c1b09040503161b06 53
    0x18045581300c06042c02c04c00d04c40160340140721030130107010807441d05141c600c086040c040c0b260888104150160711623242c0745076040c1c0e80410001c0c000c440303103400e407000e5120800415541e11002d4641e1041d984111a04200148895200300885440907041c0c0712480d50303960250380800161081031540c6411812810042c2c5003168901d0003a182c3c03088003000407481c0e40401800e1840c10032000300545c000050500d40c40030b03014801c42d9492811142c14441c0e1501c030032030880b03010006070110f03081402c1580d1070039050700d03000e9400140d0b0200d4034410b40c0040003d0b005141c1024015105024000030800c2100780050307408000084246a115425400e00d58a4a400060315025040c55940c00020041c403010070850200d1360458010302e800320788145112044600c5c500b10326003206421701000d03102c41c0c1a14000c1981d0025000180c0c000c088440d030321040c0407840b54200c0307000f01242c00030403003000d850316040000e0210b02c0c002e00518400303124010400006414a0f0401c0c408a2105210044202 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 464217383 1250 464216133 464216149
    0x70203090a0905040b041b210309090525050f070c2103020a020907030b06070c140307080703061503080d02040e010510080403030e030f0a0509030f0f030414040b09070509 75
    0xb0010100030003252800d601c035a900e0342000b41000340803040c0410381000c0700240390041405001240722107101161044003102d0984680c900c218046012003000007894142403092070311401d0700e0240340e0341246c0442c58040d0b41441506400c010300c001070202c5080400c0003800b504000d842031607000c241608000991884500c0328400382c1c0e131000748291004c0042c0d0b000c6034124440b80d040d6030280c3c082d10760709001e030064815580d0300754019002003800c3c0f080c03101c030000140443d030b43c06502e01d2221240c003081c50b460300d140740280f00c21544807000410000e051944101c44420a0558688031700c0e03266a240342c1298460f00c0028007841e00450203010100c40301d00384500400c8119244e00c04501208800f401d600d40041c4050306250382c50280d1000d0400900403202c0b02c11842e940560f4076503580c0c8020300640c004405242c001d01c54603e0380c070410140084c2200c6560000801541010700d09114420f000003035000080d00141c6981c0034640e1503c43d20050342c010f48180e2101900d8010341d500f482964 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 464218633 1250 464217383 464217389
    0x4031206080a0c05030f12072105030a0e070f17030405041104150914040b030a061104081c05030f090102091c02040f05060f0d06020702090f09070f03050607120b0405070203090a 78
    0x1c1d400c40c00a85824860014003900b01040d80100d46423610418204500002c841741031901c21134049003140c15195602c42d00462080c01c0780710040110071007646e0156034490040c0a089042c00c02284240000302c105121146212000d6049030318040e01c442c003103030546850703541080301708034041000c0c44403a0b45114031a002441c1762820b10681450485020748a82911032180c0c003035940c2d90011807454030305200d035020150b000f0100344203001e2040000c42c0b80d079006120319002e5003d121074510301c0004041e003840d03201c541d55a5203410f41c0c1300c1010306006404042c0c02c0d00d00302e650800c0014920744640d01624194440d46070074450f801c249005120a581c80064642445860b000810151341e640110b241d01228042c1c480340d440b4580c2c1d1034042c00a11480301c01030b60011440c0100050b40381e112074080e03c564210810781707020030740c5d8401e482009203460100400d20340110700090a15486580c811140b19085000400c01c0721107000800e089501c1540c2d04c000580000400b4582810050000c0c402 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 464219883 1250 464218633 464218639
    0x120806090106030e0604020d02010309062903011b1b0c030c0e010504090c1e0504060905010302030f0a0305160804120302011d0d0e090406020702150405030610050d030804031206080a0c05 82
    0x905007280291303585480700100000d21400c2c54603052415644654085c2c0d4115510040070425125401c401200528046955801d402c0520b00020340c1030030180240064460320781047c1418000041c1c2c01c0d01c088804054070038a1404e140790001c00314020300e916000650041045207112410594101c0c40d400c8160440d500a03400e01ea00d80d0005002166080100c40d401281c58100803110b070130120604266500076640141004004901103000d980b08a0481e44210b0441d03540000c001740480d1154a502e40241c0406c00030700c0080c0c1d080307200d0368642c0c50041c0701d000c0b2a458643c64040c05003034440422410340050399655210b40b1b030940221161002041d4544c001c060032044420300030001340a4468417801420508045010451300e034059800c3d05500500400d94864203101100c900d41061048910a10481020034072407508000040305940c006051060f40341c6a50314260795200b00034201303d0400604900e400103551b02c500c6035201030b080246c003a0180300014104442c1124458100c82c1c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 464221133 1250 464219883 464219891
    0x50a05011401200703110415061d01030f0513052e0f0b0d0b100b04030218060d0501020c21030108030306100c06050a0c1206060e01030e030712080609010603 69
    0x4061000100340c05540703000d103010600300c070090700001203010480300328031040e2040d40404000c10005528032503801d01c050703070100109024040c018030710750310f18030518010a015040c000d03100e02082e03001c501000c5040c1000f103220a01c49007200211102228002801d52000d19880200601030144400a082e001280a15041d01e6050307820400c81e03072812001896580d039602c201c1944e00750814858008028107500310f010181c1007c0c0d1a81303a0480300088118510803000c0f40300c030a484140c40580f9000f5110124a41318041c445000780720180c419a84408200c070242d00242c000d000074591513a5a1001c2c054085d0071140f00d0304003d03201940e55110900500041c4203800c0004192940070030301701d54006da40c1c440c0305000d03100d88024034006401e2300d0a010402503c03240340d401241c0500155076a0424116210501f0310855270340340145d50016000c108001c055611a4102501d540d01c3c02055074038040d00d039654816082031104100c00462000d8040082c1440d150300d03068010b12540c24148 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 464222383 1250 464221133 464221139
    0xa031823010920010212040303020f100608030a0e130f020d0c0309020306060d1a09010212060103021e030a0e031303111c120c06020a09050f010c170702270a050a0501 73
    0x820311241070b0050f16181c100c01904400b40c1c402c010754018820302c00c0016944a4407410004d485012030b900c003682502c503581d500e04000f40c60b48140c0085910717210295042108a08007203c8a400341403120340c2c010031180a050f000c81092140c900355040c481c3c00143c0d6050140310340c1d4150354404680300d090600d0142c0500c0513031804604103500010403600301118a519140c000090760851901f0403810340c48800700882c030300055008052104c00d181c1c5245071303a40c602c00114280c2c03255010089240303440d0758603c16000175060140d90017404500e00418803801d0000d00602e9070b009080000302205001004109114071102c140c0a50b407802c3d691204d440b5041000c0c1c00d00080a020020004d134411040848400d00c16400c0a461581c014410340d0303074050500c002454540940100c80c131400440382c1008456029510401101d90700002c10903460349074040c0e03011241c00c4a181a41c00040c207903107541313045803814600f0010304e40007071058100d41405804a802c46100404c0d440c0c40c149804014 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 464223633 1250 464222383 464222393
    0xa0f020115180f0603051b1503060d1122021c02040b040b070812010e060310200708040e0709031a060a2c0c0403020102011a090c0a0318230109 63
    0x160340742000b65001103070069403562108001e0a841e440600240100418110788842400344008000012030301c07505210036020103800380d440b086c1ca08a038002401c411450002e01404401e4805180007000216400806040c0503074040812035010146680010311a8000502040c40c10600120f05c400314102401d20748000f04920070f0f8092020a18800302e10241000254011030b0019520010b0601302c0d56903c0c10070301c242d04003d070703002403003401121004a0407034098401d28003103450070351a0340607109480e20840312690000c0001c2d9091101000007280c07020b0841c0e422402502c29a0318402c4c9185141801c0c00c00942c4200c1c040c521140110a00407103603160b041c008151030364101200c4145c034084825541c140c00c0e586e501c072580b401a008102142004001610489000f84c00a1244103444170060b401d81c0110003405a000200e00701080041c2c403d40e006c0d020641c1e40b800c0004001200e031840d00060141c5040484502090310401c3e44506084680c04107480c480c80700902005229640e4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 464224883 1250 464223633 464223659
    0xe070915061d0a0e0105120604030e01112d1c23190302090f0901080d081803180109140d06111b0a03090806010f03060c0509060a0f020115 61
    0x10340e604004481c02e01030349420705182441c10409000f0240040e030350790b6500501810750248200391040c0d61260007032001c01000710b1200c4c45641c0c5036a921401c800044019600404021540380013407060742d0043c5e05a000303103981c4601c400006520201d02c2c1c8049002c051a03c0e02038408441801c42c2c10b211942010380001a1012410115a148480d1070500b143c0c03160f81c0c05000c40c0d03000402c1d12048400742d019019401801510070550364060701c3c02d4400e00744040c0d000280b2400e105540300014080300c81e481107a4158000d50301d03d03a444490045902210714680140103202d0381d44007103040c10b031065030304041c4800082c8080207072120460342070070010b00c284600c820044c2043d034031503400c0b0014445000031111181c13444a44900d0701c3c1241020b80341c1d40e030005c2d40100e0101c0c803208404102d5030000144141280c2c40200c00110b400c0c00c1d41d8501d0090000304500308280031090001d031001e66540340c003134816800550307101021100032510090a40340541c1c0d8080841070015028003003c130001c15 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 464226133 1250 464224883 464224889
    0x2809080a0803132406050d020d0209070c050304031b050d050613050f070305010501170a0c0902070501090215030703062301050c10090b0f01050102070b0306011d10030e070915 77
    0x1500c0d030307243ea4469148001c440c21281004040081c5010126020380020102c411003031208141045065115418014400e10056000e9402540141080018600441da90b0f42c001031500d4640c1034a491550703294599002500219410802d00341a2400280750f4001603004210840c1c4544c40c07911070741c9400e80c503a48054004100611241c614206100c81084a8003d0a03004003c0301c1415980381416802040217006501051a14078101100860001103c9000503003180781d000040d860829400025071000c101181c4c0c5548440c100b46c05627440704101921403100c0d540e041d40d41c0c541868010100d9044d03070000071007103840c1228a001300d050080141da0404003824082e0b0740e1303d10403080d580350840120700c004000703040480420411845002c801c0c00340308451f240c0c10440c0d0701c500c0103a07100c52541c054480c80780800c2c07000441c030358482e4050550a018620303032481240b400e40d0100d1020220000030f030020940722212000c1c2040e04003c00700c010000c0340001c1041e9440183c1400109080d84 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 464227383 1250 464226133 464226143
    0x7030b0d1223030a0614040905030423060310030203150906060f040e10020405011d09040609080c0703060b010f0e030d03020f04150c030329041a03032809080a 70
    0x1505003001c001c280007560342e51040010b0300940324a0040091000fa0802d0b000e40d0400300c074511a00b40080c1404d000c1c001c11554000080c41c2861308012103d184602d21255024040c9008044008140c0b51400118000d0301000300d214915400c50051500c0c2100078030030300889170310041c20004002c0c0003203016504100d041318006242d03a4200b00060150001c1d40e080b038103a0064105d414900b01d4240d00500407101c2c01c1c0c035a82100c0924070003c1040801c2c4401c000d4020a2a80010300082d200c0d5004484440c4100c111074149451390000503d4020150405c40310155141007840301581c10000d01c420741601d0f4900942000c1e80c1070042034440300120007280c107150300420340c20078044501003035070f020f042d40c1c0d410390386080040d500003458071420f40010f0b4080303440c003c0158400180800724040190450880116003001241030000411000031403501110301d09118540990702440108810b0f031090b0160f034851200c2c0400110000401c0d641e023410301804c000d003001f1011000c01c007010016002 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 464228633 1250 464227383 464227397
    0x9210b040204361b0b0910090e0f060a0803040503071502070806130b0c1213060e01060b030103020307050f0112051b0705030c0c010f0e0603100306050f07030b0d12 72
    0x207001c1d4041081d11040f6241c0d88400c00c44010003610300d1220280c02c10f80030322000c40402209641609408800c1e00444640013003c000c0c441140c200144044248080e514000484075650300b0380544121050f501a0a0a1021401d00545152041c40d00d00900301e07100146141c03d00d0440041e0f5156a90311602c41124030380b18490304484c3c0280200c4005140b6141941c11074986103460126248250001315412200386001c108036113a5a0306030795950601c1c10222110741c8500c13003130b98290216810101d5149480c4ca00581c10a0428084c8074024242003505640702d5040d0320400d81400810742050b4010a100111100c46a03403020040c0b04401468000081e203841e01c108040000300d00d12075145841400244260130080000002c0101804ca0019200003e1a410044901c8607801425a0003d900c0110031402407601500854002922604c5070a11a0f0369607654001e0310000c850745a01c40d8024400c101d10310340c01d4050140d00010840d20804203000c25070720100014081002d020400003d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 464229883 1250 464228633 464228651
    0xe0c04050a0b0405090d0305101d090a05100605120c0d03110703080a050c0c0909030f0c070905040309080f030a0503150402160503090a08071503020309070f030309210b040204 77
    0x9035005428200000d40107000c0c0c0d00d0503117101595002c00d80750700301c0024075140000d00303040e4041e0640010f680803442c2c03201e05c02c00b0300107510600349406028070209000d00d401c1c100000390200700030360720740101e650003203000761420041001b01050340d000c0580c0b5400031021028191b940002e50001642c1c18100302e1101d08559903070754517296003a00002e00c0c20000042c0d074100d80d900300c0081c2115030a031030b040341c414442020a001d90f85005a034030b50303c00d80c030038031680c10203000e10744c00b03800018079140445140603074442941055820544050b03000c59100d000500c03844800340608854000a000210302d0240b90700c0e0001c0a511000301603089110090040744080d035143d404884000b0a401c24491000465041c11501c0c1c1c0d00041e0705c1c42c86420f242100050465000c100700d0103c55484d000500100075000c01500691b00081100340c0c00d00401c90040381a020b000303060b07009180aa034a480400d818001101b08400c401801c521640e40c803094408000365810b808503610581c15980401c480007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 464231133 1250 464229883 464229901
    0x121c02030c0f0303040209060d020d02040f0e12220602030d0b12031809010602120d0c02010b0a230105091e060f07051f0e030d05060d060603120f02010e0c0405 70
    0x1030a1841c00040c02084001d050091001000d54000d0307008880106194aaa0080000010382a90000e4000755840200030140ca020b600c01e9140c1e40211b0804180c00c6855a407803400c050041d010501d0820000c1100d6441d000c14580410f83e40d41c4101241a1042c100000a5601d0040040c030b60b4041e91503058a030000d840304a4060b0031688074400b101d0701e4100c0001c0d443c0d6a40011144140130f205e2690000400780d20000302144034074480c0328490b203050740300f86401002c0c0100603050410341d034803130001c6912901c40c10805402407004145903801e28454030410004600200c2506042040601c900b000f169180300c0c88802c10341480c80140020070329031011846a01500990310180c84001ca4103100b84240403c60b08030040c28500c1000d4800c14907840d40d41100c882c080d4500c001d0380203005990341100e09034841900b007030005050048585880d95428160340031074004840a031210140410b501d038000300b18143c40191030000344615018000340a581d0114684040d104a8503100480e034028 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 464232383 1250 464231133 464231137
    0xd0c08240a15140d0207110109270b12030c0106061e030e070806010b12130f0b0a060302150a020c010c0201143016050301210302030904090b15121c0203 67
    0x350610b0841621801584c0ba5000250020780b03080d2800700b0401402c00c92588036a42c07400548201c0408142000c407a196055100c40c1d41c841c0b80c10445558403505100b6540d0b00c80d400070031041c150b000b1344da01ca811080301829141030303501c40380601c030400c10040507642402404c2d078184049442c00168032a5080300551404e4002c0c2d00401d140d00401002080d086509801032000004070001048151145000b44104419070a0040c0600b511034048000090510070820303080003e100300401c413152241c0020f808229010340350800c200c400502113621580500104440380004d00345804240f04540000e08181d11100001d5541d2000194050400d0315429117500c0c10325030301c4001f03d9106000c0c0c07160110090b00390390f0814610b001c2c1404041d1a881001140e05903100c0460440030000080c4241c2030503101e03248110154001400040c00545480c8500009640030f903980f03030703e136081241c4c2d4240e144d002851070a00803286a4405541c02c00c00144a042d155130f070b140c135407160f0915204200e01314 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 464233633 1250 464232383 464232407
    0x30c0b07020a0f141e100b03070e010603060f062606031e0a03091203090b090d060e06181207140703050d02060702010f02040302100e060d0c08240a15 66
    0x4403036400002c105120400c440090081c1c0c910003140c006900c2c00f0340c05410281c80300c1c44917000b42d0206800003192609034010003120b0300040c0480d08016150b0389070020002090f007023040081e60310308040141e40c1302e6500340c80c018a00ca00b1302c1c189d46032046941c1501c0f0100b415501c040c41c640000841d80c0b070384041091144140c130340c410100060716910407540c0c5a00d110b50081e400686600070209080c040200703161700c0c0360383c15105c510fa4503240ca000f1591a07089502125840b4000540c1c00f40851128064002c1250100d00544490b14107400328000d00d00c0d400c048886140e10032091140d2407800e00013110390241c0c21503003004540d4060444e4901d0003a280d0001000707402104500c0401c6071300003c09601030751340d0b50002d025035140d080220049009601c4042d6004032a0b800504441e4020400b58800440140030a464500b0780500c00c000d071210428914009081e1004101e450310803209900c0038070fa0791100d0040300d042030000003a10346440380142106e2108450400030003078001c0480c1140 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 464234883 1250 464233633 464233643
    0x714040f060203030a0c0921030e0a030807020901140f0f03071a1801080c070308131b05090c1204022101060f03021002010e030406110f0601030b01031707030c0b07020a 74
    0x1805441e600000c2d01d0390801d98841080c1400d0100d40052117018490035001c0e900d0305080200320900c194a40010f5120440e01681404802003159040d030320340d070300b041c4040d41c0036245565a4000038030501c403c0850503071048040e200a10315080300340da03c3c81000c0191802c1100c103000d682951100003410180c280d40440c0180200c0030801030036031405009008a100c203078020040d05803001c001910300300c1c000c841c3e800010404019407030010703028514a5030000084074850303190b440507a603501d40044801600308500e4196032010030030b40ca0810b02c0300b5032100780000000d042500c0106064618000900f00900ca00000d4480304000c03140003a002003601c0d400c1d0020300c40b4540d21284200d60301e085020981c02200c003042c600c00701a00501030102214030b088019480c192400108403502088540910528040c520711840210010810365010710300990f520751035540f45252a609500c400d05000486d50000c1c045440481d4200041203402074001030444440d40e64540d00300d080050030314004007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 464236133 1250 464234883 464234909
    0x106050f09220905070b0a020c010f031404051e0a080d09031206240f02070314030405190602190b01060e010e030d02010c1103130308070215030f090706030212071404 73
    0x4004505078003c0c14105000314290303100a40c5541030020304d0700c520000070303015138800030083c001ca51040d40c14501c03aa40e9403400107400740d070050b041e482c0c01005075010390342544161800d90018450301510003103114400f004001c0304040b580c4542850040301c8600050503601c204003030605005000503c0303801d1703180c0c0b8100305640d1181c01d9010314603544401c1d103090b20700c40111032104a00881c001c081601c41074008140d80b130310750707554012600b400e81c26229490005000015594480d9144501c0c03580441104006d51070406100070700e00070400e0804280c51254484000c0800d0095000e241074426910740601030203440070050f2004c440c1040d94a030144280017a0301c0100d07078194429542c0b05e001c1da540c0c284001c0800e02c196503a024174605411800c1c4080c10810000b01c1e45c90040c03000d82d102030454040080306000344141c982003201c4040e07403810303288108500c6034000c0c062343c4040c00c443d0400318107001e40d1075001e840090000746504140103070b6010362054600c043c030640c0d00501c1c079036031452 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 464237383 1250 464236133 464236189
    0xe011205030c071d07030c08160302092d1f0e040b12010e0132060f0907090305102d060504020d020a14070308040201050a0e09010605090102150106050f09 68
    0x840e1070030038001300d0240e9840d8000822800b074400d00440142081954481425480f5046c554241102d00340b42102030542c00c000010090300c0350409405081840c3d062000a83c0712000200b12547c01d54450502c11050303000070102040f0018000c00c1090214a48090803079400008140201031501019601c00e0301d42c0c02e06840303003005402651032002424000d2062051048110a60091034502981c0c9901c84903602032010001c04d51440d486400284601034074406500868094001135803590001021090107005001c0d0801030821992a0424100300c0c119850105904695144031380740c89903000707018500c140390060303045003001d17050050003150780b42e109050000096000496144c0401e180c51501c4007a06100000d80d0982a050b40392441c4643d01c650045906074048000c6e8000d203c0e2040007607070300792100031803903000e4400c5031119552405414000ba2800c1101201a40405000d20040c000c942e4404240c45204104032407503138a4013510b000091000e0040300800da00d0219642001c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 464238633 1250 464237383 464237399
    0x14010b03041509030207050d1e05060f0114010c0b130203060a0c093002060c010c0c03030e030c0a03080c071a1b16080d060e15010906090e011205030c07 67
    0x1580074611507001d003503251000340c0340e00c02665810400500940c2140004200500f0701c000c0c0312a00510800364403094003441c00f00c0240380400d800e0141c81c0d03548500704100c564030b40302c84418090800d48000c0e00b8684040d43c00209041c107000c800070700da17003202c00209020340005001c04100c10350007004d945040c6000c0744003600070001d04201d240012802c1c080007600828024a6990400501c042e1000548030205200c00e81c20562074101c3e0003d104221350201c041c0f0a1240c400e103040142d42e82c41000d070841c18002c040d110009401c003010f03001040781700c518150000f16007018039807501700010b00e5980c41c40c01c003c01d40551040500203440e0740c02d85c20b414241c032030401880741034440c1e02c81214270003000745401913008503043c1e010035408040d0700a02080c684e201902200c5507281c4045001c0b40c0740d0407010481c903016241c1e58a036403d1175610204640e0400c2089000c2d00c00d038940440d0640c505804103192103018443e0419200300c040581e424044280119843e1504000850f84004d40da5101 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 464239883 1250 464238633 464238637
    0xa121712180105070f050d0527060a0605010908060601030f0e24010e190207080d020a0201091502030603031b010e01061d01090c08060613180e06010e060d1514010b 72
    0x3188a1070b5207403c00003034055016801c0c40e004080b1564466040100106e5080010b01d409030090703003128544044c50800088a17604d50b441714010b00090442418814114019200caa4000e9810f0082c1000b080c02960700004202e50f1054003403034007240603413090030307120000c00d03e03c02400c11601444100788402c4c10f581c0c400d4902c62110300e4074001c1503aaa03110300d16000c0015a079003101960500e0501441910b140c0141c40840d00810f40c051414900c011813008991103030100c0c80c0540d445000038000d01000a60700e9a44c030880c51015440c0d8602000041e8692003080c0d12602910710210300682d070034200350320000e02194108000c104a03521607240301e40c1c0c1540b0b80e42401c10341301108004616442c6034002c1840c1e45585845204207030302d50034204201a0000340308096202c0320803000042c502c524a0841428102d2100009400759200c4440307420054140c0080c480ba0b12100d05100c510b407216121041155006403a035280225210071100280030406480010503110000100f80030102c640 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 464241133 1250 464239883 464239921
    0xf0206041403210307080403020c0d1a06010c020f01030c05070c06030b150a090302090403050c16170703020d11030f030703030b01110c0a090e1015030605060a121712 73
    0x421034010000c0100280d00100080c3c80c080c060800500100340d980b400344180340c2d04980300340186d40d0030801072000301d01807016902041c1c5201b0304074000340d41c5107045800840e030040c500380b0381142d00b240d00fa004240f48103004c2c603c05040507a2800c1841c0824417400503243c50b40e6000c2035007103400c0e6842e80000e0150503072060341e61113840050014000a82103600b140d10b4822980c480c4a00140340d6020042406030042c011b404ac804100451144503205000e189881441b02c0280c071503050031f1550980705031652400031100c65002d45c1e810310159a40499003285e081c0c1c425210103d220501002c41e05221b1103180307134a901c0c40041002c008040c2c254001d0034030f000c030030382e44c092100013401c5c001552810740b1041150004d60320042406400c2132034018641c902d050504480400c804151800110340265900788013015148109104201060050301e4026004483e81011301c2d0070881c44840120703d01c50700034030b81031003440c100b04a00010b9064440b19000002429454580203031614010304910f0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 464242383 1250 464241133 464241139
    0x306020915030112060b04090b070906020705030115050d0f02030616030f02040501050d0506120f10060f0b0409020c010b100305100605030121021503100602010f0501140d0f02060414 80
    0x16800890801c03141c0c0642e41241c2d200040703555642900c1c5c50b14401040080c04d1203410549504c08080800c440c65000b5000326101c0d41c03210841c0b450720900034180701d0075410142c4640d040c44145c1c010000c42d00d080c401500d0b030880b03c4604181c1d1901e040307803d0a001d181d0080d00340c0103803400c000703854500014401c0b13598071030788081c0440003054074044124801c0d40030b81c1d03012a00c00e1140840c0d0100c5944459405840608030030b4a910714a8491460705542d1100c00f6082d502141506501d01510300455004001c01e88804050504101049007640114001c040b13140381c0c04104800805000d401405032640042d00304000c40000040050103044115100c0800320001100044c2041c070520489040380c4001448203040e6100001e404501680388005076840302da0800c20070328102d41c0000079400b13042850745811005182101c06402d480180d5145002c0900c2e0a00402c500000302001c40c02845040ba1411800c914034a0030565000e44000065000300c0c01080100b1400c4c03481d848070b241e4030382c11 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 464243633 1250 464242383 464242399
    0x60a081c300b0a05031e150601080f040f0c060504030203010e0a03020c04020c1011091008040201020607030f0f050411150f0f0306061b0d08090a05120c0a020a03060209 74
    0x5a18250001c00405400e072854103600031850100c081554820000d15000070900a00141c3e0f90707000920344601c4200f5088000d03084200603c902d4400c208060300c00e1200c81550041c0d20781840068500000207101d501e1201501c4c1c006403c1102030b0740d00e102c00c00d074088030320312580c0d4460750f0042aa80050108a01941c41c1510692541000180046003254141d0050003c1030344402800007075040010605810b10450001c0b03581c0358100d00510344031404645030192034400d148104250208848401010301607a0000c1c0b001503640455060703441100c03410049680f111110480c80201a240407003101d0b2407030401403000708021807400c0c40310740c801260b920b95040d81e03210006140744211120169001130401520814451580165134400002000c01e401c00a1400c1c800560114552003501541c01008200e007a06401c078405a82002e5220002c01004040741d94041d81da18160000490b943c2000c551541022001c2040f52211079014105010440d41c91900101035080100c1280c869141 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 464244883 1250 464243633 464243657
    0x1203071e11120c1e0a120b06120303070c021c21021915020915210601020c040b04180501020c0613020d0f08070803010b07020a080d05070605060a081c 66
    0x10101e8080520b000c1c40024001002c1070004010b4100d0750001e088203240c2d4028814051681d810010300d008003048200c10503455001d00e0083d40281000f008540306201b00a0b00710801c44c400415603a1105a46c1004900d0f0031a60000072621801200c009211006a120500400001c4e00780e500760030f2024499503e000f680708109a032034004200007441c1090f42c038144d050110301c00d20000200203011003001403600303e40c170010800010850300618440c440c0015001415036500c8244070f80c0e4000041500000d044c03a800003501c501850004c0c9104903140e071120703038032a561644000210292241004084103003441e0803170207900009c4c124091030164030300044100c040f40300b001507545da00906c1d0b520080385c65a665029062440130584410310203102d0440000c06030401035000e4440f0041c11a1982c039540b0401c80c01500c00d800c82c100c0c2d90401d10500022540180680704007690011011440e5680d1030f0110301c030180a5802850284200343c401301d819414403692890440b00e5030b40d15100005 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 464246133 1250 464244883 464244889
    0xc01140307020a1b150f020c06070f020d060b031c030b0405060303030f0a0b2d03012708070206030a090b07080f0a0b0d020a080102031006080907051203071e11 70
    0x1c0714104056000b10101c400002d0700d014107012160030807040043c485844480800c01e5244070342420000c03601d003480070b03984140c042009640d400401c803103491429185176211181c13220324040c028014070b046038103e410449950040b241803803001c2c088403004041c40546641d0415003200700f00100e440c0c00094440c604260190500c03a503800b5000b98034680358028000d004031801055604800d81d105001200c55440500c0c84104a074000c00203080c4e031102018804501988080c0503200e60316080c8034803101441c403030400201e0a045074032a00f10f1103031410003030348e03910800c140290311101c0081000b200442c15032080101170f00894952466a445810660b0b040d00c0644481c502241001d0001c0c4078444983c0003900301c00c4010b058070802408980c0410f60342c80303042d0000100750b50080200a05d100040c1c4001004021a29101d10141001000706403103820a009090003500580000e01d00d04408200b00c2c0e42083e80401c00040003030480503141000302c0d8165048541c2c9201c00c002c08010b103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 464247383 1250 464246133 464246137
    0x90504200301030b040201021006120b0c18060a091a030a05240904211211040f15170a05190c0e09070e030718230a050613020301080c0114 61
    0x590344a1a54516400c3da03d901c62001c5000b081241144280c07640d010000144c2c1c01108002d2098401001c1c40c91040c0c900341c0c4e40781000401c1d13127811000910454510714081c40070408030000541302180e5800c90301b00101d40c1c501658100f4104c4040403908040740b1340c183e800461280750050780800c01c9440700701144d02c0900c400c2102d012000c2c0c1c0c0140b019050700d00010201e422500c60318400c21400c7c2600c10098000224080c40b50110325090317010000f121050144507112280e80403000e14050070700624103902d03500f50283c03460010003000c41c00e25441c0030301901c080018400a13185091b2412280c0400600303006c039024440c4010054030544006183d024010f1007102a0f1030b004065401c00c1c042c0b06a01c0720082c01e400030006000001047e0f0703181440008041c00d103107100303c000300da081340010003604e0103070240145100780a51010b202e001071a8549400001048000c00c40d51120800594280030000b400c1100a10010001410481c0081d828910000030303211010b0114000030b1111300c81c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 464248633 1250 464247383 464247431
    0x60b040603030906030b06070f0302030c16080d081026010608061315110a09080118030c1410140106080a11041202120a1101020f0610050d03031407090504 68
    0x1080f012201407110b68041d8200000c04400a8509070070b0142c0e0b502e0301c440c40d40d90840150b005d40c000203103504442d0028480078481c204a020260705051a0110a55544c03c0100c2050100040c940204d060b4900c020b070040000c1108801e00f080100c0b1907510154910300c42614003141c0e41c606940003c07940f03400310340f02e80303e064008403d8264801c142c0b24000108200b41c98145c0700c0b543c1e10b032821100140301001d4842d11030300796501858a81454030301030031520414184490500c01e1801c1c180000d50122450004039072100e88214849869a031242c581311031030407a0114030707040c02400c0c010601c0b21400c940c125107055a070901c050701d8071000607080318400e2480790f1000004000621040c0f06000000740701f10720140150300007400303a8011904000da240800c641c00e00305405090069a4100302440510007024060026820002901e01682c81144900c41c0a224425010818140039034400c4e40f0182c0150f959404038541001e00810590403400350610591508643ca43e09803054074880c480 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 464249883 1250 464248633 464248637
    0x8040f031b0e010e04060b120709150f05090601051e0d020315040513020910030804180b090903160c03060e06100f03030e0906060708040807150c201504060903060b04060303 76
    0x751961b85944001d4400c401030301d41c001036203400a50030244100600d030001d00d82210006141e51024900c0b8074001000e501040c000200210705000760b50f2207900c120307040142424180d9403920008000600260701d140105c848100100d190418640c0d036400852245245001000a40c0400020001281c0060703405105440b040102c1c0d100506040300d81d0758102d0203480c600e000c21542d03076660340c580e54800d41100441592207540c0c04407010150040e00c05403003089132440b40a2428100c500d999010705c0480c201000014603c20050040d4003900d000a540c00801c10710454202d40e08040e0380700c0041ea400041c1c850312460001d807564401c031900c41035a50680d26160803184000030000000320140020307600c40c500700003000c00181218003c20040031028003501c4141d03c0c00036012010a51400c4070b1060001c03290200d0005014546101c4410446003044049119190045010b07000c400107440450003000034046072458001c03084500b100c0c401c5409003e0001c00c0c2091109603207a40c440200 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 464251133 1250 464249883 464249909
    0x2010b090708240402070503120f0613020702360f070c030509031e06070e060403171c06060c0213061d0a09050114180609071208040f031b0e01 63
    0x800000300300c03c62603082051401c41d0741005800b070b001408907030043c0021503156000003184941c078280d00c11307919400001917042110514000001c6001a4450044211140e5000500400b10340e03440c041040802840114500c00b1701c030304001220341550f80b0078880461072000d800a6402601030140c244103800a503a91030010200d540c1c01d46542d08045038490307041c094048220800342c104104c1d20011036054004002c50309103988080d0000350b1449950f8002c82c410401800481c0c2d0761100c00b07113624003000301d00d070350780603128401980070307414881406056042a00c001401e51307100c070784401124021030300c8030341808500c402e0104442e418400e421245009040314032644d03591005659100d0101003011485085a689042c21540302c010408981003058050040c1003030711030f10300301c1070400e42d80003040300382001009035903284c58500c1445001ea00c049030f0380c030400c200041954020080444200760840d10781c50613000707407004c0e5083c80f42d465801140000e028090054038604840c3d034130101038 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 464252383 1250 464251133 464251141
    0x31e05030f0904110c0304150201020a0912060b090411010f050c0c01030c11060c0d0e010b03060f0703060b13051f08040b0402040204180507020d0c051917070b0702010b090708 77
    0x20070302d4001d494160ba2042d40c51026100d00703401400200b00c1c03410312030061540c440c100006410384011680c094001c41e80305010000010f50400c0014099602d0345d24148c850460701c3c41c20300054880342a42d40d800001c040d0501081103034951459508000980342d03072440c0c4518100c203c546002c0c0f22003c0405510243d0740d02040e500036400b04040881528020280c141101003040c03500c08191210000c3c0c04000a810004400a101c3c0180c0004503500a1013003e84050000740d50b51b2002e8450b1810462001c04070310f585000e54040001045141260790315000b01714100783c81004680f04090080451410451420103caa00194981d0050300e4080d440c0c0c940c1d0f1158002800020300480c0c11a908110204405c001c0c1451000815046a400700e207038a40010000e04088000386094140f00c940b44075200001e01c049004081264454040c4203400e015042080610840108003040c0c0780e00020b61a05102d8008640b92099552760024404040c4000c1405410a400c032840c00c009401d03807004c5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 464253633 1250 464252383 464252407
    0xc0c05030a02131a0316050901061b0b09010b100909060e060d0f06090c090510050103290604170a06061401142212061a060f0a0507060203040c031e0503 67
    0xb483c07840004404018070502c00b2400301b03140100501148400801242d030422051810f56135050140c4807a15008000b0030150401c440301000b052001080c4079550310006001580c25400700540601c020242c400d669491100540164520301030805014103003080800c0301c0351078040b024000c240240c1441c40c01616a00c41c1c950030361487c002100c00c01c0d1241d401e0404158885c4c0b00c100504121440001c0605145007000424407450b0f01c500e05050510880100304280400082010950b10100000d103010040c0040c040340b10383d4000e886c04103847d0b0b0b02c1e4a00b0790710010704840814424001005260340310511803010800c003608450009121400d0782c0040104034001d009090742c100d0103102043c0d05034480000720b000c1a0850080018600ea4a005000050041c801d601d020a404c242d5591190b00200d06140310f00d007600e004105e000603056003440c1c424412203100c01d401481c11512400c152620205090141c40281c400d035082d40c0724100422003645100000700e9000000f5841d01042d0129 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 464254883 1250 464253633 464253641
    0xc040e0123101205011d09060f011710050109060e0c041a0924030a0b0418020906060705060903040302010e03010b010804110409060207060f180302102a0c0c05030a0213 74
    0x8a1041041d0f00c00002084603050003407074064400000443c1d100c5824168940e071260b002802c100c00b641c013000502c08035021110341c09055601f951823500440700010803003442c01c0203004550001600c0c2c4800000c20310342c1580400161118003c03e15400c1d12000002d5856025602480c1c1260901c0141d182c0300c1c41c4080f0041051000142070b0226409100c80b44005282441c3c043c403450030030020400003060f99611442000c6c2404540420051510b270000401c508440e01000340103103400e201050340c540e91041580c400d26800340071119140303020071105449800603c805ca000c50215004440f582c23406014925045c00706940740343d503030b40e12034455420b203400b12428079401c42e54a403100c0000c21580d00050030302500403800880c1200242142c07908131454080c100003841d4000031414000380d4041807200e40d0f0302c0e49450203d22219800c0c2030034450507a6040d82c0c1d1a4580c8a642c805d1207581060700010461300400d0400000c40d521000e060300c96580c1c0f10002c2d80407008425610f205005544 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 464256133 1250 464254883 464254909
    0x6020705030601080312181b010f14030c09010201110310030c061d19091a09010f0312050315101e0206070203042318040519020609040e01140c040e0123 67
    0x40b011f41078031004011070401110401000007480107440901c4556009603140b0030594403460301601008a0603001140c5010281500522031800141d140e2581c1c401d400189a00c40e4030102c3c0d0b0b540342800003241c4007283c1c60b4801210075544002001070268011b40c6098200c03004801078a43c4e81d641001040380808044078100e1505041180200e101d8010b4854500030140c442c01d03451008000501700021690140d101c4c0164951a08041c0001481840040d054088500701507890b070321400011381110260050701c5421120000c1014802035025001c0303501342032500c510100300d010b088001c03625280c08450302d60150b4000c100400001103800ca00c2064240d401c11034030301c0164040c000170042102c00704800c40c03401e010b03010301082c800c061003001d0001002a60329043c02c80e0740c1e4040360050040141c440d200d15500e400d2a0b900e02e00a40248031710401d45a2050f5561902c040d513540d05401a0040d04c2400701034100104103d040040c0180240455540740f01c0d400c0c0c001010040700d850520 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 464257383 1250 464256133 464256151
    0x111201091d030307050c07052b0c050d0606031101090305061303020a060c0509400b09010e0702010e0109020607081b1006031e0213020313050f030406020705030601080312 75
    0x141c485559001480950300841d1259500d41d03030b913a8000807070303880e00325190820b038840d0612203034a0311b85000520350b40000d800e04100003c1c80d0b40ca5820003d0b41c001c242c1d800160441c0310040300c070701049107591041e0140c0384900217130400f10510f480111202e5800c1d020045c9141e00c0600400d01062104420125551292044502320011070352144280c50418006d000860707408914400f00340b0380354403000500898042c2c0019420040c00e04040c0024907034400880d00304d02c0c00c80e06500b074805a0805c1d0348025014103035043e1075030740b219010040c1d4400c442240042d480d14806162680e01809a80241c0d60005c1c2440d00b4180544c44040c07041c2c0c00822218403101d20200c62109442c024085845094401000000c0cac403441c40c20f0098400c2145d5402005200c80da80031440140d032a406000940c809200d001a241e03500e001d681201e20207141d201a0140c4500001c20701d400d00c0000c0180300380e84107039080d503204603138600a040d6a590207001711341c1e45400501a00308003600d00d0340c0703255003c1540 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 464258633 1250 464257383 464257421
    0x3100303110a0f120f0c030207121419110a0e0a020a02150c0702090f01050d150e07140301061703031302031e010c030c020c06040918080313050111120109 68
    0x55403980d070b564111003012103072104601c075044100c80d0001110417140e40d8500748060140341c2c655009460305031501070b5407005d51280300782c001032240d4480700c1c880320b0440100321200c018202d48040440d010b0040c0c201da0300380741c110f403031241c505040900c2412a1464988081140c0f41e540c0b460019400803010309046109111f81d0391220100f030344070680119010b42c201541c1d81c40381d005010328110300500400314020700c000100000d032140d100848000303412081c0e0f040680c1441a08a0181803120400702c0c4c40e2060b4000441c807000747d0311020340c00c042c0480c000c005c0c241d61503241008100424504030038903041400098242d00001c00d286024500c014140c032108002c1c20317006001401c1d039220701060b40e07643d82c5902c0c00b201c1d018462480c154030940010861000c2d5807000850070704c954000e14031000e4072110008800e024001c604d00c40c030780c1d03c107000769224500200920a42e119066060701c5230340c00d11a003070340c0c3d400756102190300c9206450080c2c540e980c200084540505400f0300c5a134540c0e804 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 464259883 1250 464258633 464258653
    0x4080d0c0f05062706070c080c1006090b0414090604080c0109170c061308030109090c08030309210301140d052b09060509091f0b07030207030303110310030311 70
    0x410b10009110340e400c4d0030755007a00d08100040c680c80240303a021405030b80d4489003d0011759a041440c1c4c200d182c0d484180035665548030750200d400c1a00200305002e0240c201140424404201e4121441640702600c0800882030102000d0340149000d52b0031a120707822060101e03005c1044c0390005c00c2c80003000000800d07042065a01c8a0050465801c500da0800340800c011400e200c05200c01c0b500020715120001100d2a162204051444103120700c00c41d07280c1d5031044d4010000100a404000e02134181030320381b00d162444845885000b540d00da10204035590303403031345c2c102d00ba04011b80e4181d40c014800030040035050070501c00117094074681a501c520600c09028039401c00e1242a04c0403415815140e0308005101c07402408407401a001001403241c1401028002c1d2210500e969104502054078500c1030601012031a0381035168100360094800018100203158000881408a91003075508101811154980400c80c2c0025965a12050480001040864401c00b10b090546030100295404151 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 464261133 1250 464259883 464259893
    0xc03150711150f010e010504020a091502070807080a0210020d0518040b06070c08011d060c030a0605030a0506010e0f04030e01231c1d0312040c092a0504080d0c0f 71
    0x1040380c14000d0f8440c0680140800640d8004650042209070b509605040e12254042c00c403039201e004003d009401d07460800d00c0f00f4030800c21000200801d50950798010b4552075419112051842d00b40d000b1840706244a9140d0310006110303085907169a181401e260f070400420360828010707003d1a50060700c501c0d40304560350b01c1000400c0c5140c03040068100c0a49012502420340303401b5041c00c2c60b01715150000404103040800c030940d101d0030100c3e00355600d036a01011140248929041682c040c03041120f16030401600285a038142da00c4200e00414540d296200c1c0b840c5664121001000950b00d002045400d50084101d1450010b0303402c40741600c0d14061180007211f4201c98281e50300208031940420903902c4501c2501c09001002008416480c421040c85940f4441c003540c60003101090342c0041c3c28448442c0700400509a9181c040c850203030703551211079400c004205140301e49a980103448001c0d5000314110ec3c1100e20200c06880c9140c240401690031400c21042507880e45114010017000072 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 464262383 1250 464261133 464261173
    0x60301061701051005061c050a0f06030f050601051f05131e03020a080303010302090103021210020a0e040b030d080a020a0e150301031e0503030c0703120e0c030c03150711 75
    0x251407000040c051410a5102118403495403116001e00c40402c00030000c0c84c001d00403a81c004880388404034003521a601c03018001d00041c00c001489038900140441040450b41075a0f04081c098401c94406980310030400c010380f000381221300000c1c00c80c0701020703004500540c003924000c04d08140d007103541ea80d00d6040714240350680a0283c422500d0150510071032414603003071030183c1030302002941103605560108011001c1030101900c5091564610070400c041046070f8a01000544c5017076444401145010f090181c0c402a410301c16420405207401c181000600700020091943c0c03101015280c074a511002540074880080810521101580b01c1c0d4881219100101c4c940c000110355035031441c141072100c500c0d48842000031152004c0d294000c12000015203800c41000c0070920b03a150090318041e9a0f03100fa8030314403000207040422425034681c0c08900000b0641042c0d06032203600e60900100b549640d80c42c54038486407042c0b1000314a885101e030411078180c1215008941016000c4407042e038402e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 464263633 1250 464262383 464262419
    0x5041a0c0708031b03040530030708070b090d0f050a180b0304060624030b0103141003060c03090b1302060702120601082b0e0a050a030501021e120f06030106 69
    0x583d000250a980b070303e030f440801e191090501d4014505082c100300000c3c0d500481203c007100c0050301160392080240c01048183c142c1c00180e82103e90b10b030142d00d0040e0807078000700b201356411070642c030010b0700100d004600d9901c0110f565464840724507148409032140c1d00b01040160400c8421080300001d03e060b40d151070043c007292500f00d41c03240741c01e15240d0259956504a0014100c00da108011100101252000c4d211070b10709009c981c90001d10700407401030046140d281200070308201404400320500c40c801050343c0c0200000d100483d42070206506172245094000c0c043e00c80d1000003172403610858401d0b00c4546c8010401803808016800003403002c8003441d0340c10b100b82c00c0480100b248a40c2082003001c0c4403081c8030a040784164880350082c0b221388807000f01c4240211856491002c0d640c841c10b41003e800003c1000600c1a02c1e07044c014002c2d04100500d0303603103c8818040c03e20300346d02001922031400610800c140c8559030403003030040406c0098081d541540d00d5030303000319614160610003021 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 464264883 1250 464263633 464263649
    0x1404090e01050a0f0903020307170906030421030227040e03030403050a1805090c0d090204020a0203180405010503120c0c030105390906070c0305150f150105041a0c07 73
    0x20304200c02c03410110b40703408068013405844c18090a00094011090f181190b402c01e252000c04d941c2c040c0c0304095132003910343c40c1d58454070000800042003032104424881b000114200300249070b400314150100d20880c620a40c1e40045000b800e07090300744100740f0348d00c00140548040f5148602c1280d42d455a041550120040364000c80c0080d00150300404c02c4080c5d0581e03400c100c0801c1e1a05006c104506000382c40b4001c00e01e000655900803052503002904500ea01070700442d5150b0b00000000d450790405000c4180c0d0300d40d4a40660070031324180c082e0382d06903030009028110500f2601d4000407694441500d0b2030043c018207060380301e260703170a00c6010321582c2d03003002e0b20101d03282e009881c41d89036070b0004c900d0020019104007080d01000820079140c0c1a5402d0b5411a9103513114102412410301d00e5000400600c1038a1440c0840715502020034001c003e00c883d0940070f41c0351182d00214201080082c5400a1001e00007004403170940c841d01d400346060484070b54680320b801d0300004d0414206400a1304 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 464266133 1250 464264883 464264891
    0xb0d06020408100501050112051302120106060210090507090e0a0602180a0e04030c0b0907270b060c0d03180203030a0206010305100b011b0204060b040e06030721031404090e01 77
    0x10080c0810f1140c04642c05542c001044036605001c0064010040b02c201441880c0d910b800181c01455200f040d0007a40750001c01031400705800745441401382c07059008881c0140907110b000d00c9504e0160113920900750f4884040c0000a041c404444000e26503203200742154462000300c0804280c40b48028114442d91503020480c9800c2c0c28140200400a903010305a80e002c030104010109502100b800d080b6035000d0170002c040d440e40040945840402d03000039485c0c442c00000b8103a400366404440d51043c05a401c1030100c1c0b03e18cc1c0400801e40210018030a071600540c119041c01d0307100b42c1c45000000307004c0030b40200c00306240c1c0203c1d00c1c6800481d010f00250b48410014414000f082211841400c0800c13424003095086500003000404401408104044001e200c0011942c458100c0c0c07000c0c2c016050b0080c0c4036503490181c0545103005451643c060300071024007042e0303420380d500d0307515200703c11074007124664840f60740458007040505080588100d0500001c1210749141c00781d900007004200c0041 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 464267383 1250 464266133 464266139
    0xf060f020c090f040b04030509030d09091b02070b1c140f0105091b090607050f07031502190f090305010e1b060a020c13061505030702100501051509040b0d060204 71
    0x6440c1c95010010503115090901c104003a2020400e50150300c40d41c0316031400015205d0346800d5400d8080c4480345075042c01445144082564414000c4045032842c1105026040309098000c21111341c89494000580124209204080300200200088011940d6000002400444460450f44200c0b40d1016800f0740d030041c0a0a19a948503903400740c80d085030540b00604146442003128084070090040020003c115010b05079544400d42c4c0e0340b250040180c407402585103c89548403906070108950310300a40c413116440c00c4a600c20360b103c15001000c5200b0207501000c0903219401602176220030000031540100c0080c00c00c0c05401c050b480d040c802044029003050010790b00c0d62421104900030711042c800006465400699004110300586610006c581c0d1504400f010b01a82c0d0406170303e85030000b298508541d030040045102c3d081c541c0c00d4496415075900810140c92080c85181d9000c0321294490000e0050b950042140444c0200001900455400800c40c0308400050503900d45902060030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 464268633 1250 464267383 464267387
    0x1009030206070c06080a050106020c0d02240415080c04030b06030c0d050601081014010501030c200303060108130b01441c0504120606080a0b06040c09050312130f060f 73
    0x1241c1100d00c0a1b028000e81d818510000d69440c1d00401140c0307c1d402c81540d100075503c0d1440c610182072050010527000da0100c1c1c0401503d9401445184660075442c0c110407040b41c800c01c0090b000b2074280d0522407505141d81c5034800390140290a00d80d0500940c1c1c52580c0aa030381103d02c4600b03e10440c054603240d03140464240c00d151100110481003414040300f05210300507641050705440003400c00044681c50300d8003c031042d10b40c50007031a003043c800078091480f00710000040c502c20b23030090761020016607034001007907860001f0010017026071025100610903002100c4849198224610b0b6094100d01818550031140340e0850700e0708105151070004d070000d4201403050649200001100221454041e40018040e106a10400070030105000488017003252540085004200c100e003100c10000caa410b20300e0710031030242d55843c482e03403a280105044034006c501c6d500c1101d60040c05010440660440c0508641c410b04440c0c4103030b42a448042110036484034044054900c541e14101d0f50743c402080 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 464269883 1250 464268633 464268647
    0x90513060b0711091b040905090307171206150a030c0315030308040b06090c030a0c05040506041d15130209060904050403020304060f08240f031002070c231009030206070c06 76
    0x844100005139407540404134500864040f87d040c042c00080640d1881001401c50149510081c40741d21001c10071941e089030300ac09485540314100c580c2c07e140d252401000030b8a110504d4a1284072000c0c0860000d960103a03000200c0c0c1c80b400d00380802c441021100c1e4224491407031300700b2008103485c1801d12080c424004201a4810300540b03209003075041400b04e84005000003040f4001d0961603a1034512464415000c2d40c0c0200000f50016881d00c0d100c111400381c854001c5490b807410b82d00f6100040550300003101c52900c0c00009403050150743c1c102c03801003010790b101000c440d400900c100700e080060303110340c441c1d28400d41c00395000d19146e82c14200b00800101410343d04604129811003230181701c2159883c3c450160403008415826150b107030012070a90058a035040e035140c000c1e0911400c3d1500e543d0018400284102c46070f0300754030744602c070a402078a048000c084018a40f45001c2841d0305056403001003203006414030512080c1c0da540041c1c5030354001032080361010244241008100d0304100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 464271133 1250 464269883 464269891
    0x30903090e010b0c061e01260a0305030603010b030d1b0309080304060306150804050c12010906060806090f0111030f040c091b030b01210f0b03011119080106090513060b071109 77
    0x400c001d8042540c0d0040380b0050018080d1100c0e01508c100c40c032841ca032460034103a2800c1140000d869001d0b0541c10701a1a6400840303050b0301030b50070000b007150686401b00d6110500b240b240c40382d0f040d11070700081c1401c684c8080c5001b241440365004000c140c2131000c01c0034100411903940d0104a2a00301100c81000070305031080b031020300c801703801800000740d00071901540061087d0307980701000f168042414090b000054025020603d80701c004281e1860201e20144110200001c031501180c4402d256800c0303130342ca1034154035a89414000b003004806510071583d006401240106410390700c1d00c2250085a002d007041008007542802c0350603406070107001e003021114003400c3c0201080d1009000c824000b65004441c45021303521011103100d00001e500c4880702c03590140080110b00d1000f001c089a43e8000101c0b40c0002041c070b401c00e00300904c0340942d0303410b8518a40d180a086403900042c40b03070b80005407000c851015110500801d0300c641604c0a45031035030084204100d1984e0300030600c180340c00090 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 464272383 1250 464271133 464271151
    0xc070f0e011a1b160f0b03060f0d140105040201030b0d0201170a061203210606020a1e080a031d01180308090a0c0f0f0b19030903090e010b0c06 63
    0x2450400484544294190444480444006021a401d049803002d4811070280e90003042e01040d141c0703101c00000480000c044102c0c0882c1000b50b03180d1081061880711352242c10316001d02040050780600f4541d060304c6100358064004a000b485070341c1c4030001b4201c650107820f4240e540b07404200079503a050150031000d010a80319200c0070701c1a5000200000000703e5943c240c1c00b03881001c251030580c0d90340040c2c024403a0b03c144184c2450301d8070b8028a800d000c0c2020407000005010040b051000070309c141d400725405070b001000c41001a40d0303806841c0c4222203031900072003600d00981c0c0104080200038510b0640319078002601441076184119840c0c1002c0403101350343c0c5003e01c165509503144103206400703038144c00d00303080d65914201c1551070080d003200001c08491400000003134001504041030169414040c0108100341c4410041c000e5014a02c00002070364081410500801d000c0c0c2d1062030392a002e80381103052952a8920700c4030800007070f844004600d030300140d0100b2450307081c0726460304440c020b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 464273633 1250 464272383 464272409
    0x80d061503050a0b0a0608130516050103050609090d0c080705030a030f1508030a0509040b0a06080f071716030f0c1d0a03020f040b120a05100b06090102101a0303040305030c07 77
    0x4020800340c5c9a180550340600c010304012850384951121241800c5901c03100315500001c43ca0b00401c40501c00744501804241000045441031905001d0303030380b04100000041403a12202c5800b1105406802000d44100c501008107002084003440101b1079066162000710742c0203031b1a00300504581c20783c1c1030f445400e100364505100586010044402c1c1c20302a2910a84866050000400504035003c141d80d2103800c401c0009030b0644c01100701e62041021603000b40d15940e901c44141c0320801c0c084d118548a08400300020101c1407202c42e03424814504c0d1400250161403500c003c0c0071290405854004501c40e2580310201e20f078481c2c0d6680e140841990f049414600e540d01040300c13803140245c0c40d845a80c45d4841401207450b80401d040c00c1c0b585e004d084900044090a0045c1c940301214044d0a042d03088ca01d003410103082c0300007260341d0043e040c5d00500071035030055400ca005201040c4418103034000300c50702c5100c558042015001441c01000503656a2541d11105482c180c8030b584850162551 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 464274883 1250 464273633 464273651
    0x1140105010f210e01050405070906120b0402060a0e09041b0b0414101107030803090d080412030905120c16060905150304081303060903090b030c0702010309080d061503050a 76
    0x4499980e0000b41070b504000f040e0098000216009040700404104440d03107042c08000c20710a0000b820320880d40595420024039840d21500c1070500400c46026204814440103c2c0050a0460061051600514015042a5402000600c008400e03201034030b51403800442d801d01300300700140010040c114680c00360b241a140503403000e980c0c2c6591403d2072040b081c0000030200305010710020b0300c010070005c059a07003040e124507005545401c1a80c0c03541c070074030a080403d00c01c64054440c7c44e02a0760030a60350030000d01c201c1d03801c401500b18201c08403202e0055141988072041910b01800351091608050007407041750124000300d07210700350700000800a60031001c1066468880c0c181c443c03000002341d419500da850703040c4502140300b810300791984800e0040b400020301c4240d5203c00319851180c0d0311041c08982d01d00009181e4082901d24450b1880d08110f454010341c0240c1c0202c503801d1103034175071070b0428180342d002104856440e80280c0654404245001c1655458800c250b841764005c03c007004a0b0030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 464276133 1250 464274883 464274887
    0x604080a1424090f0d0c0c0e0103020f0f030f070b0903010509010c0e09100503120c1c120b040f050408071416060e120a03020f07050f150901051b01140105010f 70
    0x2c2c40030040c445811002d010960190f010300040c030001800340d04a400000203003800818400304070b03605682100c103540011812200c400c2415040725001408d981d48114010708001c000160f00d0744c0280e061042c00720482c41c81e0fa06000340001400e04517003440c3c468403200281130039980c0040c5440350b00d9240041e22440ca45e000401079040c018160b0300d803822503039031101200a038400740c4c102c60b9041c49a40c50924803201c4c2c1800601c01050144245c1d0031404d80d113413091207610704540303205011034100100d060080b4070769408182492001080494039942e8081708400f01c03041650180e030032420004142051100f0004100d9403820710000414040d03500440501042c40c45014800800c010000000c1070343c2e9070f00d5404d1650b00300580641c2c07a0110719140c00380d62800c0c0124050b034140615100001c4924020b815911080800340c40d59141401c1600c106400f50703c081c82c4241805010f0151071422041d400e40c290450806000000d40b2300c1e00111060355004050303001e14100003030840701c116101c0d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 464277383 1250 464276133 464276173
    0x1203040b04060c030c1707060c110c1314040b01090605030f0d0c0f05031303050c030c15030a091b08060c190c0201020705040f020315030307020604180b0604080a14 72
    0x6070b1030301e4003075016126881c2c21107007075040c030001419040c550308109548002840042403428800c074801c001e9110340c140c040c1c03514541d5001501854104031440c110501341510403442540110000061591520007900ca02003410341d0142c5400e000b003801404074069600c260000341c003048000f811049484502155a10b500003640030410407a103c0d00030400c09100d0710021095400b4094a440f4408007400b0010540c041c03000381c4161049007580340700c0303080104540c42c079401c01402c032070790810075028032880c1544050b0030b1980d0a50b13a10101c0300400c103201044100d1110705452810200e14000d034080c5070440c090110584101c08105114455844e2080d00380b6516440c140b10088001a000613801c001c8194030458101c1d0400b6165100e442803a0300451061f140c81d0040c1c4809135484050650383d0180c0000250002420403043c0034029508480c055081050040030030404d0b01040401c2d11398105600010350390b4032030300794241003000c401054600401c61b500100344a804054a601c502c1d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 464278633 1250 464277383 464277389
    0xc090509030307030f06030204140402090a06080d050c160b0c0d020111041509090c0509011701030302030f0d020f04141c021f0203071a01050112020403120305130203060c091203040b04 81
    0x40350f9917a814840480040e08007030021a0020000c128483c088400d0703007000c8908640480c81005082d00050980d5900e100e81c0c410341e0084002003402d441c00071310030744503a884070440c81828841c00400181ca1039a0100c07c00141801e826201e4440c00580c940700d00d8080030425000c15a410562604041b12a1b41c00784e8040b01c5c0c04440004400d02ca0041c180c1700c1101d19000314200780e06040c0e00c0403079242c000006001002007030b038412406c90005035135508044428040100145c00070010624550f0842c8003900d22007000100040c504140d180030499154015841624a103a82040140c1c40c0e02d000305481c1844000310702100001605a40041c43c00c007840103206e001d0a9610655404bd2442041641e4040d40d01ca410804070f001c64030351418140e0424400c0c01c1c000b940c9100402598040b42c000c4d01d040700d80c0524440d00b5841c14000c290094800202044c0748002c00da6059000f40c0c3d4100300b250b0040044040c1683e44040d41e10502140000b20705400e50b071a0b10402c010420750041c4000c480807 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 464279883 1250 464278633 464278637
    0x80a0213020d060b0c070e090606090612030c0d080f041a09101503060e0d0914060909180105060f0609151c06150309020108150a1e030c090509030307 66
    0x981090031034240024040c2c41446000d80b46480f2001c00d001320031600070000008038070122800c150380d80a600f14490000c0700c40d07880301e13005000410b54604128400e19005480240401a000b54ac90080d5165401c040b072030446a51050440d04101908004115002900400d240c01d80b441d2a4882c901d41e84400034402c120034841c4000030302d4110060003035804900722907609002644018004514541ca107000a03140c152402c00344104101c40010f070054001c00c203480e220381c25840c02d40ca546000e101101c05a0708110308002e01c0c1059990301171820b1045441c1200030801d02d000c03145283c2125001800c2c3c1e03002c0c4507080492041c030307901c003002d80e056414111001000720002e00c007641924001d200d2002c1050750b20f07400c0c04c4800644e50700300c40150fa40d207003503262454405c440b0031010b490601030086c1c045a00200401c2d580802c031540b1303040c911805448142c209548102e0300c40845400ca90440000b00c0c1000c0501c04c12000d40b81c038900038803825000307000a0500c0044c15440b44006884141 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 464281133 1250 464279883 464279899
    0xd030c0305090d1a06060304030914060906121501020f0a15020c03070312050f04082a03041203090503030406140a11030711040e0607090b0d0e0d050c1006080a02 71
    0x41501c101c045500b4a00054a000d0740800c4624000c04842040c95100f07050840c8400060340d942402002e603403207030fa0140e035840030036840c10721254501c0183c00106c9801c514200898805920756400801043e0383c8000c031141a80750511a02d914444a041c64030304541014040b040c11410003c2c41000321500001510003100340c0e201032800a1041c040081081d000110f02daa0a0507007080c00c488016a03001401c0c1b1066540d00ba030700c84c030440201e5004040c4201400600700022400c49801c14950305104028031000805c58260700d1900107501103c030400310f4a62890030140e014881c000105010340c005c1d8102810128017400070711aa07102c0b41000c1001250015170544108618400301e03558509903a0382c1c41c0d80e07007008510719944001443c050340c10030380c0c02e90700c1240000d0607510444e01559a8079042d400c0001c030070501c1e80000041d010650719554103402d00401401280c11544498032170701c3d56a13071000742980c14500b580014810b001d1804000300700e44400821017170400c0f030781210300715 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 464282383 1250 464281133 464281157
    0x40b011e0b0d0b1804080715090210050d0b0d110f1203250609030504090c0e18060d0501020309010b1507030918060b030a06061d1c0f080c150a05060d03 67
    0x92000c2d01d500103042c1130340d8a80001e01040c0b000c004001c089890003402c03401000000c1081901c03e648040f44003e4220440d10307603021007544900007502000c5564180401e1801c402c00024100d501012001d65441440c2d4800d070200380343c4056071450004040d00c1314240c441241d103070103403203024030315039034203c00080145500261809402d010b2a181c4c002c1d020404800c0504004045d604540950707102180350403402200c0c60300600a080020360700500d8407594401002c01c0800c403600103808a0f4000c140c2e00840000648280050740c4198100e000014a40000c0070410041c2c40302402c0b00d900301d050400020000c282c2c0203050a0540d00310491a03c2c0c041e40510841c0c0081140f0790000d60248408014018102485c0d0090700803100d1a980380f00700d4413141354800001c6242da01010b81e000c080389160385224071409000700150b9015210121103108940c44403150355028510300c040319046001d644000e0000050711070303000140c806d4100940e10700320000c5200e100481030060184070051a000f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 464283633 1250 464282383 464282389
    0x901090f020702130c09061b20060a0c0210090f03060c0c0b070c03080c04060f0e0f0d1b1508061c1e0203010e150429040b011e0b0d0b 59
    0x160107050380079007a6080401301d0002200148083e40e43c10340044e100b100c000401d10322440c03803010208060a81c000000540b0341d10b503842150354199020300740a01e055440782c26030704c1101414600b01c06480340c0d05440e03424810000b03042240c1442100307200e0755280a11240d002d05000d00103032a41700e14005540b20f40da1500f554180300c1c02c18001d20780745422003003007410340d030089100031710a21075102c401a030380740d03030080b40e20500541c0600400140341d003601940340c078801c015041040c14003811411800042c000843c10351036040005a50310103d03001d1654140003101417501c000d0451901e40c141001380001c00500b80340300038000c507100b0f500c100001d0700c2490342d925800c2520f80d446080581000100d074071070701040c1c541d904140e11170f510b811480b491240d00412130a000b007a4182055991f50f4403940d4104482080034403031003400054025099101d44840700403405203008882e10308156140c02e1401840c1141d56000c008040c908180400000e406002a038424224011020515040312008 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 464284883 1250 464283633 464283637
    0x80c150a050a050d23090c130b0f04060f0e0901090503160821071106010f15050c1002070c05040b090612010e19110a211a0702100507030b0901090f02 66
    0xa904080d2514481d0717001c0004840300000324900e034010001c0c06581d40e08881d41c88580b0086110741040240c022040040d4880c6c3c05101d0740000100b401e981d080103a00820111110342e0410b991b40c02c240302080c0021022541c0031940f001a800c0240f01400c034590b5942d40300c0c0a175800c3d103a041080d001070765040000c001c2c00c2d121010200d03041c1c10110315400c0741204400c0029101480851a138401031104a100411142d0584141c58030f0710f180c80d486c100700d440003041d819039180c0030040140710f070b64134256052000610b002c103505000351b1103a203d401c00f18008289640418032942c40c086005009850340c2010940c000c0741211a400283c03410b018080c05400c0c0940000401c0c00b03111041884ea255500d508003520b4040e10100c5524a240d100f4412800414040c07940528204403c040075080d00142d0070384100c3c411504500780c0e00283d0078000d012242580c81740056040030b05e808002003a5445642e600c1070041c5800e10003815400c0110703203615010b0103540c10780351b100c500c0c400c0c9012680d01 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 464286133 1250 464284883 464284897
    0x275006030a0b0f04051203070f08061302070c05010e0406030c14150a170105012604051c02100b09190c020a12050c010e12160c0806010b0d050a11030f060409120207080c150a050a05 79
    0x806640c0c958a3f450503645c0c1c90414021103010940c6101300c9002ea06141c8103c5048e00e0344040712940050404d444203042010b80140c060341301e181500c0c0c101d90b075030040024081c0c0d0b00382e076207032082003000e042e05100049074141c111790704110040415680d421745007030686540c006203a408481304c1d21035040c03440c28011020708210301852140d1800a1050f80080c100d585030512040800211540d2010451222800d8030b8022078030404400c4407442050380d5000b2110751030340d401100c2e0003000a58039142d4062070b0a030288c2c0803a00c0401e111011100a000740c041d5140094080d280061001081c00810f000c7c03064058a940c0002018400300302d003210284019002ca50100c81c3c0c59a1f503070500c19841ea0040c080c0048080c107010100303200505030302404445018030700400d42180d032034a020031140a4014009035005444648002c040b410329021400030408580c040c0560301d0500d48045c0c40e00006c1040b2900600180003000700d0202c80d2403d07240d0310102803a0003503954914100403641c502aa10b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 464287383 1250 464286133 464286169
    0x20d020114240915010207090905030f1b0105040b01060201051003020120030c01020d0b030708030702031f09061a010207080c0901275006030a0b0f04051203070f0806 73
    0x602440540d244c1a584c01a04080076421102d0a507124005c0500355045540b0080a0390b1050007142d4403008140003401040710072440c4180151900b0f03100c40c3c01d5420a8905a640d00000c10041c07100b41d43c28043d403548640c4002c0b001410703500d5540002d280c3c2005040c04a83d0302d00c56400b10543c1042441254203c0400b80002c0d51280c0412100c40018400c480049109110703021000520220100070765400640040203018403158611030311000b0003040004e4000b00fa52030a200000401c584508014000d0f003a40017a44100594006850701c41c0e00d810084056000001c0140b00eaa101810b450555107004032140b100b0f01103064881c000385151088104450801000800e10001c501100c00300001c005030008642411007603c1421042d1242110030780071a0052241d81928001a800e800000182c102c94230401030b0380301d07507214030402d030703600d2500034030b00c0c81030105200301000800b5010000b41001407550409020142c0100c82c2c58004c44c09100f04400022400e9070b415110015143c2c03e5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 464288633 1250 464287383 464287399
    0x40e0c062a010b031c051e0f0309150108120904090305090a080a0201090f0501050306041e0213080d080603100e01140702030a02010608010b0a120203010b041b020d02011424 76
    0x78500c2107001c0c00d00348040314080c2c03203030040c101e010f005032840721068a20707107448039071a00461340000e403100811303040100c401c0202000150f080c0c01c0601c005610440c002030241031a0f070031440540240c0303401039100a840760b00c19044007201c0b03140141140d0a4680444000031141c8940c68107907114054070543c190711a041000010f5115404104c80811078400d90741c13003502c01e4030742103002c40c1500140500c0740000c0c0140001241c500749540f201071802c8003500c11000301d640e0440078005a81c0f02d01800901a0b201c0305080250308004c009080002c2c155061000c820324000780817070b60703130000710008650325616074084610540d404c0d031094405600c241c40c01c80c01d614041001a5681c0d11002044005600c0d1107400510780f00103104030711200310001c0c0507020b4240360001e046105c41c90903000380c0c2d155503542809070300ca2340d6034891440d035901e041c0610881e00401007006402c200303c80e54000c0c1564100b0743c0508290001b00840d88e07000c500944a1100e070380b007078051090b800c08494034094000d580c13 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 464289883 1250 464288633 464288707
    0x908072319060807180513090b1501090f082d060a0506010e04060503030f0a0302040b0a210603030c0803190903030506151201290403080d050105040e0c06 68
    0x20280301e04040e55241c1d00c0306855915162021541d07581c0c202400d01e4950030303844040c009403400e80031503e64a14002c074081103209154031402c0c1138200076a9a03e448041c0d030003040055580202080d40140300f800f140c217504c94601000e95840d04040200d001d40c1050007800400281d004528901100c4090300440e00c06141500c1c410005241c1514060b012900382140b240f030510389401001d064440180186081c4441c8101084183d004242c01105050b024800891401d03a03040c050196991070303644544803003001c80110740c0031b020003035800301c0040d040c110140007080e005108280301690000540380e0701d03501c490300d081c03010700101203091809013003065000034103900d90842405080304444440c1d100c1c90148442141c0d02c0380044e10141808500010048100c0c444c400340c0403084000e40c2e60f003262145180140c020b03031250300308803054000030a092000c0c403018801c00d80504000d4508000700c149461070b140d17a1f1810801d0307181c894080040ca103480300203141c20108500a44610400310444 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 464291133 1250 464289883 464289919
    0xb03100906140f280b0d12091d01060e011b030806041d1c030608060415180201210209120c040f090804210807120e0109080723 56
    0x450310100c40c03030003041c2d10200b0002801c0c694450300035001140c2418001c110700c461194508521148109100c0d078a02201006031180c0b00f1180e4001c0c8580c06080940440380d002500c20307840d82e00325180c9003010b0078407110048102c0d102241940c0c6c0790304048c08000c0240004851010003801d00032000c500c2555240201604480420f004100842c1e080c0800380c4442c45003091644441110038166002051f044075440c0d2120307550000200519003c0358007502d8080d01031401c0d205940454041e404602c0055900307480e4070501007240305440f030200042005400090540100303850880c1d00003c102c81c81407000c3c84c00d5045a801d03141c0a0207800e466202d07140303e81d0305d558040703000e603004900780717110310100342c03407611602c1902980402071030f003014100030034046104c98800b03004441602d14144e4102254604004c1c10150f44034403884030442c0401d00000b09044500814a814401155014000700001098000a032150b1850a20914a403030490b071100c10a5000300341d401092640780c84104207 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 464292383 1250 464291133 464291141
    0x608100321021e0a06020904020d0c2105101e08010c02300f0a020a08072a060917032208120315010c0203030702040f050910060e0a0b03100906 63
    0x1007916000c0c0c51003904101568920103040380403c0445410039800b43c0001446640503144248000c1c00c0103040441000844007280c1407901d061020170704aa000d40c2a00ca42004001030444020a00344501d0601c00c452100d01e000500800f80000d444110700a0005114002d44004000d00802030001c0000340e00081e443e680f541c0f10040c03551202c0b0742c40104d15071aa5204038260807008000510b00a4181c051140c01c3d04024100c50847c040d80c8c03582c00200d0244e60142c28031074011284045011211194001240d80c014940c01481c5550b4104006880e00606544100e8241c01850341402a40380c55841c25403007891140600301c5034503618401541c4104442d0390070780d41c40740b0407506404603000d016007490100721407040d18032160448100315540704002c000145440070f0101c0342060780700d60002d416542c0201c103422903036036114104291352604100c40d08094104550420210781041c800000d800b10080043c14025220344041001d82c5003084441c02035010424100b081c800c1900d007400180c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 464293633 1250 464292383 464292443
    0xd020a0b0921060c0a0c0507031113050f06090604060b030109020a09060c0f02040c0504120f0c30080c03030703020309070501050405010e040b0109150801080d02010209090106081003 80
    0xc9488410202c1d118411201c00015860030354010034961340e805988918030381c004c0b031600c01040b114840c0303000001c030100610000f442c86012411040d50b170303171000c3c0310685440203940c800e1941441d05000d009030b2a000f081c0e42050003030741c00c1c80d0f082d605c400104000d400c09500030b0303150100002c00024601c00aa0180c5920030b00b90341c5200210b9640d84040307030300e40d03018480070780403c580f1590346005260581c4881d980b651142405420251744c0c0031502c10141c080340094989003020035056007003041c0d10034904003506601182c038240c00751200e1400b10050b20701c54082c12042d0010002e03010f0004541c2902d582c50742d05000c6a2342e0b8640404001d0281d0005e6032216110b10500c680030a0942c000c03c00c2e101501d00c1a5074564218400c5000c02000c0c0035040151030501c400e00300041074514107003034150000125616801034951420946501c1d0410b02c002c00d4085904c14410283c00d581c4100f0032904503103007441e2142c01500c4811207108601e0117640020b014541500345103140202054108103a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 464294883 1250 464293633 464293639
    0x42f1905180103142d0a0b031005010b0403080c0102071e050615010512060111071509050402040b04051528020c0a030c050103020d0b090106020309090a090f03030b0d020a0b09 77
    0x14038072035500154244ca0003d202c040c00c2e143ea8000045e0181002103407050103059503c2ea100c0440c0c1010442c1500580c1038a042e081262201718071354503401c041281e84280700717400104000a41c03400400800314000e50000400c1c1c1140010541480345094045d030f10800d41000344002480800c02000070821f41051084403d8050000043c50218000c41c030300701e1000060b100d0a2800350020514042c44000030082410b0151783c3c00f281c61034103802c00000016241050700c3c0d070490702ca881e5001d000e59246030701080c0b08500401c020310a0240318016101110380c15100030110800510401200740035070b00c00030200c21901644510804004483c6d052050700b5602900c203095046814030000c03551900004d41682c1c0b0b500010003455109038024642d400c034000d40000c04146000028400420a074080001031344045529202450610340d11600420004000c00950b4540d81e900c03880c490740d240c1c0150074182d40d100380e20b056440703034103655400325070013080d98010076204c400d965002d401420510340 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 464296133 1250 464294883 464294917
    0x90501091d0c030d0f1707030c0905040203041104110403081c0b030105040201170c0409061502070b190302070c05030105040b0406051f031e050d0507060b042f1905 72
    0x181c200000c6259144284090040c090107204da01050f0f412880250f1140c0c1044140756185100c0b01d00d03c06402d01031301e550354001c1800ca110307c41c0240015200c0d0841c601c41c9104000340000910000c0c14203115010550700411081d821840340056401f4551020b09044070004001e8031984100c11962110001100104204c2c14050b003458204c1c0c0c000c0320000d02081c44a60140044c241c0c001d00030b03034003040705500f042c40c25448100e9403003620515480036002055207070405a84640512154010345600c0c1c125506008000810060024006125406055000910209000d24401ea50015001c050300078840303414640b070012440c640407202651a42c0c5440d01142081c80c0301c54500c0315600c00c07000305c1c4108500b19140d9400e0303110740c0c0c20070202d004000002c0c40700207072041c02000702180d010307200d10761159501e08042080d2119045154450f600d440150318007140300ca00c00c0805d8108181d0400049150301140410710300c1600641c1c90841c100241c10700d00384d5801801407288400c0304c0d0100e5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 464297383 1250 464296133 464296181
    0x801260615150708120c0f130e06010c03080c09030307060c0206090c01030204080c060d02130f031403042607090f0c1209080319021603111606020706050901020709050109 75
    0x40400c2c00f84201c0100360080c1000b0307080380c1e04010300c18990080580070990b440c0a041c043c00c0400c0341e228071100e4501e0510f654003004100c3e408032407079a000c00207091101402d95640c7d0020300360342000300090154500440d441c603040e2020410794058540c0000b042040c040048006952404100c0756801d03d403045001c4003903035521a000f650101c0380d0400041400581c1d51040103041c1c1c02040b5106600b42d03082c00112280700e81071110380e00606130114240222411818080800b540003141075a65910402007006045d030b04214058810308031210142d80c1d92510804c10f030030303c650342d84203408035802c105180b20754440547c010310051140d038a40d54500f41004c1585030940300716142c007078400101840000e4084203100510301018100c04801890300e401642004034610900c50142c0010f42c0280341c0061214082040c07010105070164102d034424500f000007540ca075024020b1740108a40401c0701c070f038964001c00c060005841d2030b94040c41a9a1a90260320003006204022003405014031034803 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 464298633 1250 464297383 464297419
    0x60d02031618150509041d0f030c0c040b010512010312121e09020607050d0806100309051f0e03161e030903020915130f050709060801260615 62
    0x944010002c200c0b219005601d001450b0000800c114003010a204003080710172000d54842c0300d844a83c00d0312a003860b07114041f40c01814076100010001c2c80c260b60080046410214002500070700e000c500f2500070919100c810300480b2540661983d0100042000c0004000c010001c1d03d0b9078413030151a61109038098441607580242c6070700c280032644242d003003209110740f42016005444c1407800a003c41d03142042d19641d0501c3c0445200c0c5050004550307109210749880c291004980b41c40b0b107458180031541a54443c1502c8201c104214540c030340c020350401d0380044250f000400750542e40c1c400d482e2500040f84665583d480e0543c02120040c10500a41c105030100d00c40c540782c1d464040e500ca0042d9070440d42030202540010300b00080050030700041d00c080d83c1e03c10038002c5801400d50000306000103208000d01c00d8850161801301031248800d010b01600e82d2000c0b605044405850314818149201c00c00307e01030a40c05107140340c0380e0150104010038a2a06148414000e1040d01c141002c40c400e80c6403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 464299883 1250 464298633 464298647
    0x3050a1b0801140103020f0f0903101413031404030506100b03090613021302030a0f06090209011403100321020f0316030c0203100213090501090507020c0d11060d020316 74
    0x3a503030218100708018003030625000e900d81c041e448181801072030003035108070f44015908009540c0300852030001d043c000c10704042c00200b1158005038010721044000e10307d81203508000070b0600302e261000340c00380c0080c9032180e46084a543c0e03000b843d4654954980c1000c80d02c3d210201c41d1481c0100308504001107000c00c0c9002c50348500403001c003620458446c2c5040c145101d44001050f0790001401803608144841440214040c01d801c40e0300040702e2620319005410750740d89a01c0070340c2940c4140081092640c00002080c100701409070340603941d9680f0601c111400107503410217041641c621249400c0004110341410b12412690201c881c0750305d4400c620741d075901c602c510240d0b80d00b045501c8400064003800c1c21086c1584000c00396522000c0d40000c4400304c2c0c0180020100c0c040c1000010401681140720ba01d0250028043c28420381c907000f40c020791703900c15042001d03010b40e0b100800f040500030b94410728200000002c00f01941e41441c109031202030f420582d10007000014400400090728007600d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 464301133 1250 464299883 464299931
    0x1090905010b0408010555020a020f120316030e01060b0301031407060c1e0501050702010f2007020603100b030a020333010818010e03070317010b040506070204090204090303050a 78
    0x5038074150307900040320601807080c03005d0000030402c0503001040302412840e0014009400381f44401611000c04001c001d04d0245030300400602c2c0d800006c0050300404000040b01c2c0e00c40d4400300c900c0600c00c1241c0c0120000d20351050810025445c0c0301000c181380c80524001d5041320301401601800b01c5510b23410507100c0c65684545008a48650404000030f101e00391035a040c034461206445c4100c44548800e825154112500c80c010b0b59074810424100303100e80704008002d00008000d2200e0128035070380d40e246116103000a84540740100c001000c04400c00d0b0420702038000710b11456168100a0301e0a000380d00160740a501034140c4500c03110b0a8440d400c10044000381c3c20485040c1041100015101e07018050804051004003c940344100c40302402045003005c007400040d6030703c0500e030070000d0048101c1c0c440342c0150650304004201c0b0005c03800a44040e1401152842c1da80c10052002500400210000039080b508100382d203000d15805a2003c1e106042500007800700d0a401081f5003a0181000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 464302383 1250 464301133 464301181
    0x705010903030617100c11010c0c0302070816120f0f050607080109271b0803090a060908030a0f0e0d0f020406060509060703050310030812190b0a0306020901090905010b04080105 78
    0x491000c950540c00004c01ca040d11300380b0140b41b407d50310490342034401c46421301c4082030340e1852040415031b04122440080c81c0d607901801c600c601c80480c1e4500c8902c240301d1151405c02030600d41702803192602012400c56802501c156190310540b07091503c4403030840e80c10000c60840c0000241c110f00030301071110300b50f40c00c0080c2a22100d1010800b050180b4a120680b907525102e00e40001260101d4110381c06010100000c40c2c40340403650400c0100180d41c0c000c01e01700b08040d0742c00c005102c40041901e07940000c42c00d0030554103084420440310070501c801030551140c0c0c02c00d40202031001d070340c0050107064020f682c18803083c2d40ba034005075001e00c259000b0681242041045a0100748030b00d015642241d0795081c40302c2c2c0369030f4030740760301c0a036403c0007109000844d402030510226003400019121801e54658050040003a0f000000302c03107078a00d100242800e030700042c002c000c0340c1c40f4100b41c1d4003512116104203c556102c0b03004242c1500036018915056182c1004158040101e09c80301d17413800f03002 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 464303633 1250 464302383 464302393
    0x10f06030c0e041805101e0209010207051002030c03030a061707050a0b0c0712030f080108070503100c1101110d060b0f220314030d050c0a0807030b030a06020705010903030617 77
    0x118091100520501c0b0b01019400000c2ea4020000740d4103201c030003082ca420000c0814003880000111140450840607405d0311881005200c00c12b0b41c002c6501c0d002c445084032040308e80403904034280d045104080101c0041e0100000300202c5449540c4050241c40d42e00b10f034100002014804103586040d0b500400f036024143c00303030420400c0840d00081c0010003146064603685075882e0116403400e1007002d0100e000c0307804045910183c5900c00100790050400c2001040e48074981004a078544032041c0303000000c3e41d114005084080d009220048484081000811503850300500d030030f1a07904003101801c2c00d079007888000240b901c5004103441e904c1c03c5c02070701540383c1080700c0f505180c0d0715601c10012000c10003071200000480e134940303284c10b03091000c0d201030b40c3c0c0c40e1820807100044500c010716a40c07524005100e40c41000b80d2108100c2c0d0b00600500300001d00f5104003001904e80030345518001c0c5850700000d0b002c2c04020041d0050304000e8400e440501c1400d4071041400742c0c000c1d18142c100366079409 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 464304883 1250 464303633 464303657
    0xf090705090901020909010306091a160e011b0f0302100b060d0903031112090606060301082a0a03060608150105032a1804030e0f06040303260f010f06030c 68
    0x104051240c1c0080810b00014640340c10030010880c404826030068904980d6501c5c500c0034060703180c1501901c4901000307501030f0307803520707101100760440101034100400502c1d1a83e0714237030b400b441320040f045004410540080b20103203041401e03075034803030b00440050180d4420031100c005035006080011a00420b840e04004c125a00c68009141001c0150201074a420180c020b1329400380c000c0210004441400d03d41d854045000b0307242c080d0180585006190030001000940008a400342c60380e00c510395621091080c81c40c04030b501c01012032985910404041c400420060942d0050041b2803072502503404103200080c0100144409206071501a00f04038010740c0c82c1c400c0410300d003a60031102c1c80d112003400060004036103205003449048640ea4a0380c007d0200303054001c0c100d2050000111000020442008081036050040707210040a000b0f000d2800c0341d10010301c1024a09242013a6080061441c00591b0744450001c20300c110800c0e00c244290100c0c07200d03c60f0182c2d20f00b484c00d40c0c88200700340c11 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 464306133 1250 464304883 464304889
    0x5040f061a0114090301090803090604210905010e0a09050c120a090203070612020f0f04091425020a02090705040f0f08070e130210030506010e010c050a2603010f030b0f090705 77
    0x44442c0c4d00a40c03556a034248a0001a2444091170003001d0340c1c1c0c010b180c030b850145040c24101c3c00701c110700000000c0450480300f200e076000099200b623480a10301b1640f84916880480c034080e0f841e4110860841c02c0608200b0441c00d1080038024400c00c03403807a000c603601c40400400c11500480400303901508400800c2c40071074004d1300710030307045041040010710b440b4040c0c09060b4240c0000140c2075100000140412841d0f0907800b403095562000031920605041c420070b400782c0f506502c015003040c612500c03038000c4d4440c002d212000036550054035070202898018802071807680240514809401020b10210302066900d07505810340380520010021a414000a1004010010030070284040240c0340d4900686038200e144540411a84012401e414100c00140030030351900420350400441001c8000400c0000a0304800f02c0e40141042210500307480e88501c2100031442c030205804400000054800c3d5404140c03400c0340e0040288442588840d600316141000607070340060142e22140c4240402c1c5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 464307383 1250 464306133 464306137
    0x7050714010207080109080a1e09031e060f020301090501170a03030b0406080a121101021e16021503070306060f05070b0c041d19020c10150905040f061a0114 69
    0xc041401112440342d5280d0303603a800c0d6a01540e040b2528000811045105500031089080d5000100e4201d52920300106000340b044a1901c00600300030246107072040c0c0c41c0c19040090500030b8011200f4400d841504a80c0300107540203105100009140c900002020307004000c0c1d1404440c0502c000c0c1412004c25101140600102003c880e40140d6a610000e42d007002003144041d920310400c0c5148080e807030800003400201c0110703110400399004103c40b1021141000707542d10701d1241e80c14100e450310f55003800281c50610440d8000e401c40f4801d480d201c40e01400001542c8030303800d2030ba424813101d41c8401c2c0844407a409007211001094040c02103a000613004800316274060b40c01c0c500c02c2e003401d40c0d98643e1000c8803283c04c0110988840c600a001d1004c106044a0b010110100803d40c80e10408420140d62281044000011180d6460f0a0b110b0582d541507000c00918140c3d400344081d003001c0c03d02240d01403441e1800c55000b4540010025101c0c1c1c07003d080c0790321000503140c0347c0107490114860342182e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 464308633 1250 464307383 464307419
    0xa110304051e0f0f0109030303090519050708010605010906140a140a0306050315391803100509060112020d0b04030c031b081b0309040e030306010e06070507 69
    0x140018040400d80d5211400001c158000350140350540c06034034018000d42119801c0c3d11030190801c00e14481103070340c1207110101203075811300c0c00041440c0d0604020741890f032802410390080b45002c0511081c03000001d0303444140c84801c0004c000307840da500c0054a103890103120b80d80c0030410b0f903c6048500140705000d0001c0302c0c4582030541820401c100004043d1740b00d80614000720740e403181c00307200b03500b01000384110780f01c440e000000a50802c9a030f01343d0400030061000502c3c889189002190700c803c00c20f00690051000c004589031108688100c91400891841034020320a15681003a61901401030b14003409815001d07094507400e080e403e11492400b981c0598109030124041000100c019582e03a224900940e5101c1b442c2c5401d2030014514682640b000c03080043d40c540c180c02007000700041341c0c0002c1d0b800b010b1075085461144c1e03903401c0d0301445003416401454034030542c02c200004801148941000d0380c4081604c000c1c041088035501540c10301402990001c001030021035004107207a844 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 464309883 1250 464308633 464308667
    0xa0207080702032a04020708160215040b0703030c0305060d15020f0313051203150f010c02100305070f020a05030304060207031403010602030c0105250c03030e0d08090c0d020102030a 80
    0x90680181c0220340350840080341c82e03200c04004090100040d848080458001384201e0381075141c03c1c1243c030f603075074503001e08207042c010000c01102d08411907446408203000522410350300e54075541e45142000040c0c1188005402080c00c2201c5155140d03c244222445400b00078040d003469036943c0c40e8528500181100c20b41c81c030360b007041107030a000324005c00341d485410250b40300d0102d40340314a4003c0c1010300d000000a08000280240048000c8010a03405510780a581204481c2891001282c1101c0c00c1100a0340000000c2010300007958950000da10841c0b6644400484a603000d000b02c1c1d4030310b0051405081504140041000a44103400811075540231345000c60f000740c108000b02001381e1082c2e02c44005603000080e0013103e02d40a028840d030188541c12480050ba80510785090740c4000700c1c10074000c11400344004003c1602a61000001d400b1a20403141e48522038180604108415600400d06100c0e4581214041c5000c1d1800c2405950680c051410000300d940240d540c072200c2401c01f28 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 464311133 1250 464309883 464309887
    0xc0903150905030904020c010e070b0f18040609090f110f0a09050a0b15030a0f060b04090e0f01021801080a0606050f0703020a051902090f071413090606050304050f030901080a020708 80
    0x6142d070b1540041d01c603080300000009909c802d0256000c2c0b40005e50381c041c03041c0c60307020b11040440c00c0300c2801361110018058544662121307010005001064181c00004030649042d001200344020145a40c200510400404012500c5001041858044481d40d294028113280c400e1200322825000305410a9041d20040703815005400014659401110480a044004010043e80c00424041c035450340a48020401819040594614040c80b441c0a00d2001c1ca07254010f00810b0700b0104001a45649184021034441000c240d0003ca0105a402e4080c00a255030002c10308401c80c512852040f510280c444600e0000c0e002c2c850303885504490303000d406500408c10000003003001800b030906440100101450b101c4864810000c0e07841000e804040260400b4003040b00d42c40e00168034007140d5030b405481913140c3c107551482000c4040d1982001c034a150800d080041e040790080041d5018600c250143c42030f044400500300d0760390140210446c005540840450228100c650080c100d50380500c400c0e078 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 464312383 1250 464311133 464311147
    0xf0705160c06020105040b0f0702191e14010c08150f1206150109140d0303050a0213080705013b01031d071802070f0b0c090a06120c090315090503 64
    0x104000107551250016035114010401008944a0043d0b880345448015441e0303424600070003962142801d40f2011140b802640840c1031040301201c281c95010486e540302d03001119403606184540c0c5990300d0304030541c20030b4440007165000c0d100301c0b44180c0803e2800c084114490040094018800100e01c3d00700c48010343d43e005c01c02c401c0c825140314080d502070002c4c08140c22800140003c801303a0103010b4500c0940406042540e50342044511300c1d07094600410641c9030501000002d11483c88541c1da03410a03141c001035614404618101154400d0f02c031403070300710400c00c10164010b400a10418109014030200c0b441c0d050a8926208071510601d8002100d1400100f00000c5059040c0450005d40c000002007202400b4152100400760950b501941001015510a0034141c0c2c41313100100800b0690303000540c540444010b40d054001c0003410941c0e030603030342c542c00385c240804864200c402ca803c0401041304c180c000d01c03e40c011254007090001c226203032152007100805070302004441d280009c10000c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 464313633 1250 464312383 464312393
    0x2100302190905010e090405061b0c1603022b0f05150108011e0c0e0f04110f03071b030e0108090c041a030615030d0f020313030f14060f070516 63
    0x22114844042d1101982c290904001505040104440c14841e40d107010030000040e0f00401c0702600916a60050880a0421400302005000e0140c81140310310908142c9241c4942500403003040300c1c003e4802103409032410002c1c000c201c031551007a100b9280804003400003d0a131407a0000070a00a1058490081e40c0d10644600c095080c1c0c0402d91a13034541f216103000501c1003d0382c80145281a03000c0000c1c8005000140c6403081400783c07144141100040e9412075282c580041c00c190510300403866a414542030200c03041e4100343c880b003000901e203000e0b0300401c12448807080360700303505511201820011a00115410f1130002d1011342e01d4042c150310b150160301c590280d81c10181c030a400303c12206004109040c03034041c00400c0c195a401c82200309543d02d450106050201d00c0c2d0b80c3c50515440d03030444905914610490034038205045240d613000080c0407801010f03204c40b40c0b00780050448030000740000e541c0c54006035441e081e955001400324401d680030b02c1c000e0020f13400b02c8400d0003003080c2c0d0b900c0b0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 464314883 1250 464313633 464313667
    0x2304060902030a1b0909110708030a0203070f0c02010e060906120a05061314070c0302070e0109050a2d05190e0102121006050306131805010c180501080402100302 71
    0x300014003078010040c08544605030048504403640b02c07a451074404c0c81c0e070800a042814920416a04642d50394a00c50003940030307012a50007542100d02185e60741080d00640f0004c1d44200d0301c0700000303000d1182c01c03501203114090031044150169100352081c215681040b84030350140704e00e541d00450030030000030010310040815124142d407100019880c40d01c03a0a004078202d00000000b1651b24001c0700c2011403059000380e1f40c2004091a00700c000080901e001e03454142c86801445422a074100001001c00300e94120904c41c00402c002400040400d00036141300300e0410302d101704060000c056031400b078841507010541c0415910144541c1150146480003100e8400030120f01c0c59400141d040d1003070300c0507800740b500f20302504200d0301c4451410303000400900019118500c05c95900804099081c403a4004080c6002100307907100c040701082c5403d50080680d04001404500b00f0301003002c103100b00d001d5540480b041a11102c0069945508014030106a00c40070b0040c1a0f0034400000f5845155507 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 464316133 1250 464314883 464314889
    0x10080f011b050c0303240603040606082103060d06020d111b0705060f07110a08030a03060e1302040e0f011805011b1d012003180303070c230406 63
    0x59101c103107201660018252000c88080c00010040d4204520000044030360081ca0030301e40c0300300410301c4440d1002c42ca02d40c02c811a48a000030041c4002d0121940c0841c00302c848080855044095681d02d10744040d109210711289518188000740041c1815031182002500c1900700601e030000b9800000115030640c0300b41400301802040c0701500540011980e0340203c0410000d0021500d41400200e41e8807500e4511410b2000c040307255010000c4104da1080c44000060010205076210200c0a80c0c98221024080020342044800612030f01c203090303941d01409100389007a0b8071001e00d40a10000d407445402c13456641c801d25640340e01c840c0d028030031041d040c139160009181211076400c1c6503080d80c4170031500c00f80000d0302c4001061840d0b00840402c00f00801c401c800540d241c240300042e01c1c0040703213610115140c09501d66055440c43c0100081c805004840d000220300341030003081c141c0c3c80c05802c0e8010100201c4060503c904038042d0401d060440540c0764050741c50aa0074081001e44810b54 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 464317383 1250 464316133 464316163
    0x2a0f1e02120d0c021002040e06060706090c0e0a150e1f0e091c02030f18030109020d0602190e03070b1c0204150f03020a0c020f0303071a010807080a080f031008 70
    0x3d0b0b03816012541481140000e03114a1000d45c201410403500a17000000030740000d208140c0050290308101e400c0c0c00c841011600252240089a5901280241c508040b0707542e904040c030b810207400742c01d00c51180c042c058071a0280ba80e11659161307006a000320110160503070360310020003400220b084103000072620603c00031028090a036030704141241d418803500014015500140055410450143d080c4c400c00b8440841f9400103400000110b4010048003078040d4010840641010070700003903030000d02a00e18251030307100d008402c070b000031902c039035540d01c400d40c0c19080032104011043c0f00030060620040550a0065904080760802c8201e80c4580e114120880f80380d1400e54495030055080950003085040c00e62410100c42c0000304500024100244078805210600d141c944042060f140c040303600503030035040e4041c280302c1226a14424801c4200300e100c0c1c10320100e162100400c2600100364403000003030900000c050031a903560001003402d604c1e050303443c400180200c010400000811034003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 464318633 1250 464317383 464317391
    0xc0b0906070c0807030c0e01060e01140c060a140a0603050c15130e0604050c0a080a0c030e0706030e060a0b031002030615041806090605010207030f0f062a0f1e02120d 73
    0x46c6441c1d084611994004c44030052400010841c00b46c1052035034100090918041e0303081c03203142026850f40c1c000c0300039000061090303104109034044142e01c80c8140744410303040c20f52180e88080f40a02528910301008011703820042c00c4070203e0030018182005e030b00b420400c1c1070500402e0007074035103620b00a600080d4112a420248001420701d0300c503054001d40f07103180c0186080d04005018001c000054070a010039581d54042d0505580300b43c2c070000c8400039140903074010903034640d801405004140b020071464014100071501882007841215180d10307000d00600104444406101c0007904000c0609800c05900002003102c0b914540045c4003030655000c800410314140c003849070846040e42c024540852074400c00780516a0009110400c50f81c0c0410008811b00303140c0382186c40440014001001c5a0804416020002c04500c44400c0718508030850103031205d54000803603810328800700041c0070980c40b0390503043c0c422031400001441400340c0121903003210766040c1c0e55001c3e44070801e0003054541e6 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 464319883 1250 464318633 464318639
    0xb030d120b040204030c0512010905010e0a03030f0e1905070f091b02060603070b0d060b07030507020108090105061c1a070f1803170901140a0806040f090c0b0906070c0807 75
    0x507105900d01c07928103440460506081d82c4e2102280c184600401c2c0c41582c00c00302c02608400d09402860090354044004e100721071001d000c00c1c1d642c05100208070040b0382040110798211619120703150b5542080c90081c08008038270150049003400151084d030302e034090102d02051004400840800804034481e001a0710100c0c00c0b40003080341c03003d075040390841d0000b206102da15600001c0510070f85040490b607a985900c11440035000b018213034806030400d6404103504040c503802101410805000380c0700c074401a41c45110769422640e08462155200009440070340c941c0409240c0c001c10740f845034810a44400d02c886036402c681400b10364410019901c24440382d80c056100e1010018890044024017429056a540000311041c8602502c0d040d0008203907440f5507031050b4040d201c2c80004824440e5610301c042d50041202608032480340c00f640c2040c03c011190202031203070801c0b213504080494a40d82c20002c4c0010f09521110855900c40d03014028030b00440ea504224500030450306008220140c6 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 464321133 1250 464319883 464319917
    0x19020114120105120109020306071b06050f09070e070518011205100f05060403050309060a021504050d180b070209060123120c0903061807090e100b040c0203120a0b030d 74
    0x3c0d044d442c0f03c0d00e99050804820050300e00050658124803942402901c1504103102600410810840640f4180c141028852440350405500c4d00a021203c140c0b62000d4507190302400341c00003070b502640019002c1200ca038010456021000100205140c00445001c40d0381d00d91050329010788030304100c28080c180401190703024006040041000b511142d040a156490741626030140550b039a024030000181e0140c0c0c0c910a00149424840500c80081035040c141407a1740d4032142c00002c1070101c0c805510f00c00b0f121232401c41820445808640484c9040c009509100f12505c0107002281070181031a0540c1e448510110010180c01c0440511902c034241c64040b0055903801034004200042e04000d20760a5880104202d83d00c4000c0c98041002192600c046525000c4c00c1e40c0311441207490301104103c01d920103e0800b21008000c503045c0491030041c1c2c01c0004a9151500d8800940d0040110b15101e0620018240d408200300a001032500000e00109081034802d141110000d0020601003013142 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 464322383 1250 464321133 464321149
    0xa150c03150f06120f060602060403022b03020703020c090925030b0c030408040e072d0207060e1908031c090f03050304080919210519020114120105 65
    0x39204100d034608a01c1d10701030301c1200010f030003142c0c10040044d00b000c0a000d204e80010401080d180400c101701d60340e03580300035281d240c1994214014043c8005000000802030f07440f950000451680e00c90301140100141d00a60091100b01c05600503029050010307500c030240c2c0b6100d00d0039a0007402e048150191031000051502d82c1c0c801c900e1420401c1400401c00b41848035a0010807091302039641c0d1620b00340300080340916444821806820400c01c51481d90205080c4801481d80d00c61524125a405e240e80280f020781c0078000050b4401d81081100e9031040080e0080d200c4050082180b0581210616070300c11096080b5503055400044c500950b03162641c2105282c1007003e0003000200100d6903101c80b05a9014000740c2000b2010000c2000d0040820407580c1c60344004000d44081401c002c031032180c810081c800d0a10126a1441000320210101c03940141e60b584800589003003080702132030501111010f00d00740c0c10041c482040301c2d120a00300005027291004000c10725120340c584030420080d4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 464323633 1250 464322383 464322401
    0x12402010e0a0204110f07110f0409050d081315060609050306100317040b1204020f1e0d05070f0b040f14010516030e030a03110607050301030c0303110a150c03 70
    0x1680360100740e644030741020070004031940d411034001c02d00103c01c0c0d581c01402d0103200322050781030100040340f0b8104502c0c401010098141540c0c0c50621403442000c00003240c00e0035002405035048041800a02441401c0e91a40715491312080090b4041907150041119101070240001c1c6940780011700900390080301d9080201411001082185892018943d514032684001004d0f24800d042000e0118070035416103010308220100ca03a1254003841c1942281c1d01c041d0303426401400c4080818801d82024941040000114094032a03115001014049640d00f51070058506004024000c5204605086d40c40001c1c400078500b03603116400c0268450002d07405520000740c010309482002d00c180d17000f10030741d15204141502802203030070f81d0400b998070580d08070107240d140c000c11240000b0150020108201110880d00703c0d0050341c4d0750341c0c0560382c511081c00040c1107010111410000280b14250000d50311580e0030664544904503500e9800c100d1140324010f20294071400e043d442c2c03d915104072511 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 464324883 1250 464323633 464323637
    0x40f140315040f0b0a1404051606022109040b030a050609010c020a03080c0307030f020d0f0b06030408090d030309050109030e010e0315130c23011e0207050111010f050124 75
    0x1e50a0aa50b44962091841c40c000c000c0c800c01390001e90141c0c99a40a4041904100701400740e6240514126132502405110340e5201204103402160540c4001030385c441c4d584220f4900c440c0b485103070600c0c041a8008592980d0701a031910140403254034180411001240b080340207111504003803810703030309481c60003050a007158080c260241c0030a81c0a04c01507000100344801c26580c0c0c507480b81c2200a460000c40d01c20003e80009825490300c0031513440f21070302c80d401c10810050703492403c04111181c442500e01904104052143d40b01915007403030420000c0d0b00c40e040010701000a695982d0940e1051081500854200040340d429560040c10780405814201c0c0030700f414413040c0781250084400503080600c3d207200c0e14401c400700000400c01d10082c2a0b0010307852109400d03103c426142026000d0091300048031018019144086144543c1e2015001d030044c044442c20840119001101d601c4024095920358543c403520040038130400b8013801d1450b0083d0780035505c2c0c50b04464400041041d44007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 464326133 1250 464324883 464324923
    0x9030314131a061206160210020702060702010302090d0c08010f0e010c020703060b01111b040b0a0602030d150b0315040b01090e010312200c1f020d080903040f1403 72
    0xc0050280028410b514150b8540c01c94a80c6072070021400104881a0040b803610400061040c016109a02c0e201428031030b508441900000000c40416406503110003904020140f240c0001503029401030301080308058038032001003005480304280c105082d8445841d6940d21828041100000d0007512410201c1400034810210118002035880c400b6120107000541d0302da03c140311582c85580e10440340b48445c1d0231503444002c030032000c0c1141c4a82d440da0b2442503240420f19030481c20305c00c1d154801c856040e00514144a510940c94000d400d1224003c401e00b220714030081074010300c0402a500941902a0700300c030504188040c40700300e81310400150b041c020f844a00308403050702c6108050549601c15040051031105450559840c032090000109400c0d200d40aa0580c10000410114070038086803d40308051981d56a107420f030242015070030060b0003540201c40000c0c026644107800888032000c403403070507903030f8400880110032503085102800c00b841601ca140c1d01d4100a03000000d0001c0300c4c489 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 464327383 1250 464326133 464326171
    0x151404050a14040f03031b080f06101d0d020d080a0e09060618040b040203090f0c060a090b07020d0516030b0c03070813050322030308180c150c0109030314 68
    0x1040824002d000038041d20b40d00c0b68803001c0522030740245240d03000910002d10304030201c7d60083e024a00c00c840b155007000751000028030a01d84400d0354204600313547c0741d5210300482c10a050054074964031101d40c01402584150005031902d0b01c515008900401303120740c0b1200c544500038881008251018403a00c0e81c1814001e0075640c070400c079000d440c00381c01565611440e0001090240c6100c0105950051010007080700c80d0901081906c0e00144c00001e443c00c03101a082000740a0240540c0340c400a60b2044042c030004141e03038000c0662500084c0144240c0020340d6610349030607110000700d0b204451200c0100100041c62010b5038101441888182c1540344c80a4020002c00000f0300380005055551b4600003803142c10b008031340402c901400010b2850308801c0d54010750004520080b8005607014000901051058090364205d85004003d090000100380401401e16109550007403c164100081c007000f0000344100b103141c51082d100821420071040025814079802451902c0600404101c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 464328633 1250 464327383 464327411
    0xf150901030c060302090114040e09060c0307171302030607021c0e100f1407050105041703151908011404032d03050c190c02030f07050d020402070501151404050a 71
    0x1e02c181e4502d440d0040c0c8840310080101c50140811310780380d00c184000500401c85100d000d080d81e02c25030795081100c0c0036448011440900b484200c0c0c1c5a130014803031002400e8180c2d0900c07140c41d0003070340ba10184841b25680e50002810b0000545146001d6070280701903910070020801851035251090400e81700c0a454400440d203d02d030a002000104071000e0607031142103000d2140e490445482081464985c0690b1401d140248001c2e10196000c07090400b02c0d043c01d00c281411030780700d2018442102220344000050045042405643c200b441c9080040460454024400d0800ca043c10f4441402c00b410142006801d40d500907490b03e034007008401000c903680b44a903c3c20603a08040d4034000906564004110419004840e506442c9843c0209801141644640d031200214021401d5955402d5018103440c0d490b49680b0815420200303048015000d481d259010703003010342c010300011428244d01804001c5502d0f054010b645100d4580da01c158050510f803103003641c0000580ca0401040c1683c50342 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 464329883 1250 464328633 464328653
    0x10507080711030106080712031403090a170d020a02010501050f1f08040c15180803040f05091005090907080d0e091306110409020d1104030809060c0708060f15090103 73
    0x101411650b58011101c1460702c00350321000051120005440c40c40d6151032190000c03510309407040e00069008642440c00c060748204032030245558074000d01240402e9605c41100107041c14080c90703003040501141c02c00500300d0008100800c0141d0000030b556040404008500881484050281641207810300e1071070403520701c011894450741404091651107150981c848909a00807100301c001d150f0326010705641040c81808080921120024400d0b2580d2010356680140d105402c12400b20100030885400c1543c1c0c403541002d50541824912900c44012911080099489071749079070040600300419031044c4058030b8003200302d2a100c0307940f0000c400018107240d0090108140b400807200f048007088010350042c01b198803600c6110791200d50350b10000000b500141031040340103040007104080300c8194021582070f42d500940450401c5021f0041c040250841c00c4410b4007403040d01d00126000408109180c802c0000e100040500d04c4d141404d09004407401c4a6030707010b0544a00188001600c0c00301c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 464331133 1250 464329883 464329897
    0x11040516111c140c07091e11040506071b150f0305040b1504020705010c020616080606030c0f16060902010f030b130f15091a01020a0b010e04060b090f0609010501050708 74
    0x94a800341010301120310f520b522030038504050340d225040d400100394002d03400c800b003c540c04410443c07000035164074941c00c0e07441c0030407032104a00b802c200a000604c4e25101600310306000342c00342c6440064072034149a42007000e8000c0c1006a8080c201c2c414a40d60001c003032452100180b80038800d60516a40d800340b114005003456071102aa9144041e0340c1d00d03180c1c160b0303030b41ca60000b0090010280141002e91101c20507180e1190307400e030000c00c0c0c0402c43e0240c0f04440c002c4d0f0000e05043e1465586101e600c0c07481c0c100381d00c3c03121440700802881460500031414400c005d801810002030104207480094115000104c240301850300f049030a811a6881019100201292440108249030210318240061464004078103504103541c1006c61191b0b120380c4280450303028842e16403e01484d103001a0f0359a08040c10090103020020010f001032204103000c1d5800610403e80483e1802d0440e00103240c04900f01ea4820280d1052010031011345400c6038030600602080c00c0c40b501d080640c1d120500140b003008 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 464332383 1250 464331133 464331137
    0x10903051203180610290301090b010c0503030a0203190c0806040b130e07050a141f120203011e050a1d10030c0314250501030911040516111c 62
    0x210010341e8020300c0e4420a555a60301c2d90039a604c928244900e0140390526001c1d12040e15010140c2d440c0c14807040c1002c007606048000198210703840c01c0d400320080d0030300201980c10454407000900024604001650045150050258480c40c1c103006100c1c3c49441d0700703140c0e40ca00781488080d91440d60020843c0345c01c83c01c00e83e030100700c1c0da20820110795001070840c03a09210b03c0ca00a080000c030307200031071300c8001c0d25000c592050b281070740d030051480f00c6011000002d9210760959541413070b001d800a00300202807040d0030b00c0030404948401140403030300241e016035a0001d040003840700c00d0002281740c070040c00080720780710401420710071585aa50f13242e860019091042e0800314203200610058100190b07030040124035101c0d1245011494107108a22403a524814104c2031050702c100e002007401d17000e4105a8401403e898040111701a048408007512541e40e46500350751651501d000d0745200c0c041c4249100c0d03600062502c01001c001e0140b0324610315800080c00c440c50440120350a00d0000301074 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 464333633 1250 464332383 464332387
    0xa050d02100218090a1b20010905070b030406060f0605030402040e07030b13080c0d020c090a1a092a09031005040807020906030f01090b01051c0f1b0f090902030c0109030512 76
    0x5c114030001c1a076040d001c50103c80c04503041610561100800385003120f44d545800c1008034000f0028288c46c513100008101c0c0c2c001500a100e00307111000070b140e120f8024036002c904a951800c40741e07122517050300b141c400200c00000300015400e042c041d0510061510004020403451615134440d01c0502400c5c0301904240d2400c86010300001c0302c1618080301d4000181c0d2501c9140080c06540c445921900ca400340c0350010001c0c4481c11507102d52200e452406418006101000c3e00b00700d4009001071150310a100c444101c0c1d101071340081c00355441880c402c484140d840c100ea504040c035199a140c409800306003041c04100000b4000b2058580d955030540d180545503d6840c00641081d05d04400758800d9880d06a01c10b00f8400c011816a0403110140d480000c0420070400c0f001042c2c040082c040c00100040c120500014120308a040b06400d04a02e00c2c81b069032a148800821100d070b0340407242c0c158945141e101503140038840120000341c00d08045030071510b0b655070701d40c4992401080400d11000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 464334883 1250 464333633 464333641
    0x2a080105121005010e0a050903030c0a030506130e0a06060b04050105040504020703020a0503031905010f060206150f0d050105090705031903140d05160908010e10090807050a050d0210021809 83
    0x400240c040b20001420038806581c449040130380059003258802152410040402e6405401104881c040c40e400c0440074600b28207000309801a2601428068110b50761503007402c140b2540340b007000c1441420f4005803c4203c11030074010191a0b4a070000811034008020801040c0c1c0c10070f04880407100141d0b0056101e18060030161309215900401611030b001c00020003948545042580000e910911000c000380d0341c039865480c5080c01203004610150340084040f130240e02c0030420314100311400800c254810180b0030040341c5040c07502c5c0c000b01c9441e0b45600038001480c5d010f000c40d0001c0e210030750082150030390070f01d000e10700700061207005418882e050712842525810709044a07903031a402042405140bc0c90f1182580c0c0844003a04071000070520744010400303a0301030140d4654103031804000c10b44590350300946001000d1000d01103882e0141044144002441840105003050052020b0084401005400703410010082d0a05039014070401c9807040c07030041c4101929014409031040e103582ea503 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 464336133 1250 464334883 464334919
    0x60a090e090a141c0e01050f0c120a17060d0c0b030c0f04060903060b0405010302130f0b03100203011a0a4d0c06030606180105120a2a080105 62
    0x103003001810301c0c0c82d40a1108000040001d500101c04d840b1200c07419245a0b14101305c0d1400c4401c40b241d800203608114510312030030407101030040b800100c015203140e0611100c06064580c0655a02c401107580c0903000d62400b03010009242d48140d068a80d011440c20952700c001100e03000703008031003403090084082140c0c0c030b200c101030700d16860f51603000c1c1e070355135859102c040d0a03500d2600c401c8603e241030010799140741c10540141412258003501946c690803000441001800d181d00d041c00125a5030b001c100d8266034108030452811014450040e0341c0e504200801b20203800700401019205000c00201031f080754021880307100c0752420103060000048465060340c07981d440603003400d000803403c0005241cad618022031015040580c0b0f41150043e404000030710196000c12600c071548954288442644103040c0405880300041c14500b0901e881e08003034210141c0ca406981041d4290398454010a00c69641d08589500c0080048079085042c2e10b00c0700140481d10502901d4020100d0108180c0041 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 464337383 1250 464336133 464336143
    0x18060d080a091e030605180a060c0c0b0a1d0a0302030d02090406120b070305161409030a0206040305031e1c0e0c060408010b10030e1207110a0305010507020606060a090e09 75
    0xf0681004007220044250a200402101e0005607645407400340840c040c010050145182c40700000c015080701e520903200d40740104011000c450500051044403c000350b00e2800441c400d00c0024030010300001c03408400344102203c1640c2c2060760344440440404281c0001c1524000d960562001d1707a94050b03100420702500d81d0340d1210840748942044034081107030042110344101601c2e030f0100701c15aa481106c41200c0d800d02e4403100405d01051290b40c40fd01c0d240c000304120640a0116991102564085285684170b41d00c1039899800125528041011050541c0300c210303940301e04a4208034076101e00c1c000601e1038000800303140e640d54501942d50300c8107000410103084003c00346074449a84201d030501034402100c409110b550504066081c2d140240300c0c01c07684245900003004619070340843c82019620108043d601c0d039440d0f0030b000516999400c6040d024505ca10000b080d642000d100180c03a10002501d010701c0791400380601e10b07501d5030103146034044515400a038086c649440300c00341d040c5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 464338633 1250 464337383 464337389
    0x281106041e0609060c020d09050a0603050903120103052b0e0d0204060302030f100b0d0b19020c0111070b0612030901031806020a0306060206010b040308030105040b12070303020c18060d080a09 84
    0xb240c2042d00324014048140c0c0000f01d440800c0d02a01c01070301101d00201c403011401d0240a61120140b5001c1c05a5440b0741c1c40303a03500118a9040340e2a10701810440090100c00341d1040b13486174813440445041601c0307411001e080303518100c4105e12001402c0e02c05005440030058032809148044e8050b81959030b6034014100550b0058292120ba1060b1108507441c0c00d0010440907004c1c3c1000700c0840d40e030030300e449041d800c071780c008041094544491456107007861914003c13040180d0248040326415100380b0074082080b55009010382c2c1e4003428603102c840075000801140c824184803c01c2c00c0481c50100466040302002d2274001207400c18a42d0b90b43c400d100003000640f211b840890500c2001d5003503800341c016181603800311101aaa074810600e042d11840c00014980c8030181f00402c0300c0d040c290080101c6503c000d100132040990006458a0424150300940059011880151031070070900c80300e026042d842050703010329180c01c4000c04c05070102c00e50020021800041c1e15400e1a10036013040b005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 464339883 1250 464338633 464338643
    0xc0602010e07360209031b0f040216121e0309050a1205040b190e0d05070e06061606051021080a1106040602040815091b1302281106041e 60
    0x184440c220304441c005d4004005180c041d100c1d00741074004060141000d00c428a0b002043d208031100c0000500003e500324440450801801450100001c0d001c101c05420244082d0303914501c00c1d9a1490350500c030039220b4a5002070502e4840c410020a00202d501070455800614294042800c0b803030403101880b840d401011005004226240b8043c00000b603020000055596603210306502400c00c188005e0f01c246c000c0c01903000500c10484070112900080d48031034001d01407420044011a003400a500d840c5041b502c0346e07a100100080b14140344c03480701c058081d001c030030140e100d03210403c00400030103144081e107104004034075111524071840000c6800c0140000703895190800346415406500a400352400c1c0d4041c0d030a4070070303104140c0e0a44511540d000c000800e40e0000c0304128031740c0401152180c94121916048442c078114031030004004000700e8900c141403001c140049800000003c01d868410007550554191550800003803d0760400c1d004084260301000000c00802c140c2625803000702 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 464341133 1250 464339883 464339969
    0x100f050f041202040608190b100b03090a0c152a02150d060902031303030c030e07080f060f090c091504060e0f0907060906050901021e0601030c0602010e07 68
    0x80c0c5046070310b0310740ba01c031403082e902413003056291510103441e01d066140d520000184c0c0301c98000803c40b0401c140c1e40000900003032701001501e5240c101d0b200e44c030494000300d85a00c2000b41d0810080764040610080090705018510b0880c810002888103020a120382021062000310495401549074400c0c403080e401002c2100ca02803403007d80d0310030b030800c507c2c0312080d514014002543c44601d0003264481c4001c400380954250a543e400d50046c80c040d184202090f503908d11443d48110104802005410708e603008105071451001c45174901300e07004140940344a00582407009370f040014401080d079008888a8407640d48031415100c0240c8410030240d403143c2042c40000e01a1020515540124100101c420b507940e10fa1059941d41c25040c45100002940c0910030071240784a18040c1413001030510584000700d07a001e10308a00c0041d0130f020329845401940c0100200917808001d000103007854002804041139100040d0303102c401c0c5124251402c6040501e0b00d40e0705202503500c02c0c0100b55100e8100e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 464342383 1250 464341133 464341139
    0x604050a15020903070b071a010b0c0d0302133c170a0210031e09061d070e041101050d020a0f03060503013b1009020102100902100f050f04 61
    0x26614025044241c48040d00e5401c8450400214001c44103507040190060080500e40600317000c5e1b6502c520400d44151000480b144590000404080e0003004180c445984070080d00010508080d404041d40c1c00741031041241c14809801c120a4100b1100c0b2854511000c1d82e010b0042d40000c0d01452203a0159190042c1000046886003d0681980c0b00f41c1c0424900404a00006645004840b40650300000e5455045401c40c42908910052030813200d6030000c0030200fa20380400e8a00c1403400f1035107039494805096003050445203000b8188640030041032028640140400c1d03036003024101408604501001c0080c590260040b23074134030380040e541150f4504d20007100614140c0504013102c00641041c1d40012240740c140aa4400101c0d100d0342404681c5403103148105007600c5078035118490403450401c10150b80103100c112108151000c011508400300c2c030009042072110881c40038102e144c40140805038407040841c98013a13015081a002200c0110030a860500444000316203d100c005008 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 464343633 1250 464342383 464342393
    0xd12020715120b010906120b0102031608030f0c071e020d02060315030c01360f08060f06040c1407050c09071101050a140c1b010501060e12150606070606080604 70
    0x18076810a041241045821801c3d030044402c4090b0340318a000050f00741880409103030091348400e55082050040300d2030400c030401020014511800305454400300401084841d030880094030303900214401c5403030f1514402d030351590a0416902c95080041010701c0844045468080ca0741214a80040000c0d483c2d180018a9010800c0504d00d07144c040e01032201c039400107501a02003c115a200000842041c00d203e041d406810f104240c1d014520700000071001844900440d0440040c01c0120302404162900000861140704080c1009002d1494814204540c541c8090604040c503590820aa035813400c82c204245000507035075200d0740c0003e804060040303a03030f003240101205c103014000074001503941ca142201125180300a0031902c041130341c0010655039803503000380304054681703180100d554880c1c000d041c211403090f04003001040300d40d004039070249011191101d004110308004e298402403181f480608240140c800c50042e04041140000c002e07080c1c21000103450590100d40c1149803600b86 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 464344883 1250 464343633 464343647
    0x3031204051f060510140412020a171c020c0303190e030f1b03011b141c0207140a110f030709091104140709030b070e09040309030b01090b0d12020715 66
    0x3e498403070b4100b800b04080e154020303051821010051b02c11142403501d42020524007141c0e45200b280d01c210540d00101d12814a0074155042c0401000104442065003190111408039200d281056501c400240303c801d6070300000b181c03040865040d90700c07104a90030710150b0301c201120500b5503240c001c08100f4a0421030025010043d2640b0318441044840c03400e0505089804454420b521400200000d4005501440141480b0f0040c0e0681c0c80c42c1045502e0140d00d02000100c00c0317003055800103820418044401d612100600c407080c003900701448540e807402a00303450820400d00400019140b0546a9018050784c030050102d21401d101c0d82e989840e04120710740c0c4403000d9902c628946050f44840e11900e5800301e200b401d043c1c481950860845d2a880c2030702c007000708041300300011400f240c9082d49881c0200c60049219894104500c0d003185841c0ca0507450513001261401d150180c6820203640c2d214030040745030740101460703c0d21401d4036022814203100b80c1042c00d8441d0009070b15000c5030b9004035 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 464346133 1250 464344883 464344889
    0x607180503010c03051f030b061011030a0e01020c04050c0d0506060912030405190501080f0c070c03050a03080f130303090c3201020615040b040605030f0307110a030203031204051f06 80
    0x150a20803651031b1030103050041c10071f00000e844240f5140c001200c5080c504c0849002400c41d06003100743d0100c2502c01451940100620000640c100c40340881c0c03542c04100c45241404200c0b010b01081ca040c62405215005152543c0c1c402c50300c0e8008500b15031100c40071114510401b0f002c070030a0841d03c44001e586c0e54814819240260120201950844010407141c0c0036540c050f580c1043c17035100c07d41804900507018000c17640c00b0800300f04c5000021002c81c5404020b40c4544042c100c40c0ca85810007520901c401040f40108620080c100302c5182d41c00e01182001e01e0f0716040005011b0685e00345000745e00d040360802c0007045e40031600004800385075a0400810f00c00d0b80d00080041c3c41c01001241c4503d0300b070380e81001d20480103180280d103180680202d91651400f40c00040e01c16a82c0c00001d00e001140e900d250129040000e4040601c4098404100d00440554501e00017078959400b00740d80c1e206821402240b51540d1000c6010410240404509600c55901140c3d07a04800c1e043c40005021501c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 464347383 1250 464346133 464346151
    0x4030c0219140406060e06030406020c010204030b160801030b130c0e01090207230a020402091c060213080a020f012105090723090103111516021504080607180503010c0305 75
    0x30b07142000600e054080c1c042604c51594844007540c03907035024002142c00140040b54110780a0041080c900c01c2413000d08011409401d440040d418000600005007a0120b00700d000c0040c0301d4014070200d81c156201c10f80004400410790980b0f8100d08014580d00b0b00c94102c03079500355921000289082e840d4000c7c2550b1401041e01c9030ba000708000c00d560b070400e0000c0d01c0e00c1c8281c01c9000c2120251130103901804556802030001460303280d41d503402d01c1140805c04402c4403941c1d0b01140c595544080e0445913800b900d400402810403da1301d40008002c051001c80c403034104841c0c4000f1150f1890b034a002128120030040c2d0520107424502c0c1d00549a921742d00a442e00d0407840c40c54180d0074203c80c84940003400011b042548039134210348900d03400807001c40781c86e500300ca02c1e05800c1201c484030000811420f8000c0c40c425004140610410615000d2150101c84041c418030040c011940c010660355000342c0310382405480554112003d10240700540e106a605519142c61401d00e031f909600407500c580c180c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 464348633 1250 464347383 464347409
    0x72c010c06060e0f091f0b010c0204020d0603030e0604050d020402031003050706230901081b0f280e210a02090708190204061b02030106090204030804030309080604110904030c0219 79
    0x2583d02c40d0386d20510710040c50005440707540003240c00001c0e0701640140e001031402408003100b41c0c0100d4160b81c4505014011565141020420302d81d00440101100740d04488480c5464138100014070400801390001c0d1156500002291001040c5a01200110b92000070740301442d40d1601c0c09082e407d1041c0000c0401c1306c0080c90b0200c0900380c403085410141c41612075401d1070312058145806215051000320f01c0400030030201d540d40e945240a401f000c503403030000c00000c26000710405107141c40011b201080c000f020090000b5540c64540b032444100045c441600341503800010140783c1651600e000e034209080c0e40910840c9130b44440c0940c42000f000f601c404c0030180107811740017284211b2050200254954440c1107161085c03003085140390340000c0001ca901c079161444601240d2056004a846540c0011b08008164211494000425012003c4c104519280c4c13036201c01b0900c03130003030144202c0310440050101800307003064541c020b80141900364401d041c1202d0780304268042c0544442d035420 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 464349883 1250 464348633 464348641
    0xb06160305071a100b090301093e0f01081b030c07060b010f050f0f0415090602070e0103020a1715090304090e1c0813060e03040509072c010c06060e0f 66
    0x80001130302954201001c0f2a080e8900203107400241c124070403450303040d500c1d50208808100c010f00303000219102e02481080840c041036001c261121000203e07414224682030315503065a680e80d09000c10802800c042c0000c1c1c0d15619040c02440d8840f5602411010101c28004400d404401a0803030a01c9851304200c801c00c0d04005507a03042800044800045040181c01c1d5254025809440d50401c45c0141c0303130900c4d44400c03c2c4600303450070088500c009500d18500b00030300c603810452400140380c00b6440d070040e03506540105083c60046d001e200c016507024081014017840400940c0880702c0b00d90303039100b01ca0600c443d000d51a98054403400404074100003020003d0900840e00503904114110011480c10245900343da02400c004c2c9001c40d508084d11841e008140e481c041d0a40c12440d4801070341c1e483d0301b07200400140c4900504a542001051418461900150101d50540c46114903806000c020018012100c0c40d103201c10041c00c136400d2610018000c280202e000b0f00819551190100701d40d2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 464351133 1250 464349883 464349923
    0xc050c1f06080f0d03110d050f061503070e1e04020d05040c08030c031909050d080a1e05071b120803040209010501020a020102060a05100e070816031503060b0616030507 74
    0x40d0304495071a082c0c02984c014500c40380641e110400d006210720342c25040503280034100d0100c800c11640d01144807068420082589454640071400820303000023a411030800010003000c54401040c59801082c900b04130300480445004660400b00b0000d10944d82c44540301541c5002d00380c15079044440381c6c20b026000ca82000c011080c0c0e0345001c1280000c504141190343c4890100c6490070382d50040c00000c41c4080f50725144c1072516400640118003480c1c1d01c000c50b400041050400280d003200034201600f007141e44030b5108044984482e0000002c000fa00e0082d00d0b01440940103501003102501051400d100b00b0119202461185000b200c090342c0a070307a0360006980f183c4520900900513044a000940910180d601450300070004910400a0036210503420100400584041021444110070010050140c0c50600160f0f4160303e0148425070300e8a04d603161946040c000109100c0d12103212851548850041d140c0885030014104035050660038041d1040c3e000c84010360300640840965030b204d01d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 464352383 1250 464351133 464351143
    0x2040b1c0b010912080706060e090a11090114010c170c0f0f0102090d0b04030c150204090b0f01050301151e080603191e150603061b0305190c050c1f0608 67
    0x24100701c41202131654070354455440e136010307001c200c030030964610b800b04040300000e100300c0c80ac0301c00000a01c84400c0c0390074440042c201e55021640300d00c0941c0011301c000700c8116080c510b0110207080840542a403443c00c05002480d00c80071507212403010840c1110502e00103180700c02000c18a00303032152410384040d030394241c0c850b100c02c5940080b503482c01d85000400b1904030130340c40380c001e15103000a0380c0300b640c4500700c904082c0302c4914a15000b040c05c0c05040000d02c5103032079080741220452641003180d00041d0884c001407103008404000d1a82001071b46004a00d2614030459507010001c10b1070342080003920711081920558002d100c3d80b0703c1020448003060380441c605402030b600c100d6030300040c0c401e14081a00f10741c0c1199440015030035814031a0300c1e4042d00c806544039180200301c40003140f03c1100544a11145101090b04100600c4000c0d0b01e0f0100c0d2178072036000c43c02c0100702d90024000a90f0b00f4800e6030441c10482c41940601d490940110518540a00c02c100702809100d540b060410b41d10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 464353633 1250 464352383 464352389
    0x130609050603060123070803040209010902090d061d0304030510051b040b030402210d080702010902010c0f1e0303021e0a021f2702030c03061e06030102040b1c0b0109 73
    0x2041d070400210b0155801070001c0c0d0b00180311140820641140d4402180d1583c00c1b20900f1619010007009100444c5030025440d405414607131821410a250080002c1c1c074202c1c00d0001034013540d602c24010314060040b40f0100017021501003200da8496403482c015a0306c00c14404900c601074604000304441c024040e5243c2c00804020510508003070500708134072801d600c082c0c8100d82c481c124140040c103154404400040900c2c201d0090510599041800390903108010060300459240c40b4503240180e03007010171460701a80044c00100142c00350301c0c290113190403030b0385090b01141241d034020b020594140c0050840307403240305145503081140c60410b56035001c1c40c1400005a08440541c088a2200340000003020ba038a680105000110b80080b610500050b000e41d100121070b1203501c420b600703003008040c01d042c60903002080c09160401146050400c0e200343c01c02400001004a04685d17425010744000c0d00700001819a1181e103484c2c603800c080000600756000798240744240c041e56019158882c21 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 464354883 1250 464353633 464353639
    0x50912040603020c0102090901090b030601060206100902071a0c07031106010f0605090a0f0f2c0c160501050a0903020c01080c0406052505070302011805060f0d0e0d0513060905 77
    0x38581803820507000394001d011107014a40d400d1001e070000c0e0741c0d4040c645000300b410450008815800d05e09150030903105070404415075105505011003080b0310350f200c000f1298000340c0141c58580b9458140e44418098401601403502041800350000d414001064418800c0d22104100b1641121807a181c46013480381c0302d03200d004d684003040101d0240d0000c1c4542000144036031309180e11654034820000c00b40d00400c40e808501c08090162004564441540718416114500e8070381504c0b565a5400e14004c013826403035400840c200010345010b001d94031140d075101001380902d10348003400300700500091070283d0040c42280206102940034120300c1d4011040401d1241c03505042440c1a80c0a0f40220801e2503c2002004103e41110000d5107140340302d07110302c2c0034242461550000410000028074052404034910804012654458046a141d2028114025101c3c015400c01c10001e00141035181143d004e8140084212603002005208010701245c40384000d5031903d8080320030309081c2c003030b15030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 464356133 1250 464354883 464354887
    0x8060603040204052a0d0c090b0f0a0c151a011704030f091211031608030403021011011b0206100e1b0403050d0801090609050402030a141018020301050912 68
    0x800350500780c2041e0fa00095407246003840303204172410040d03010400b0f51410708140c3c02160901100e08680210003e0505925180c0b2549060900258142c45a42a034031860700c0001042242540070310030b0243c5881c2c00c075001060004480907404007070003a0342580d050714a409550007025600441600d600d032510007000000603034440d5000d0b1240c0421040900c1400300280b80000c1180e542131003203174010303c29207580f00060964000d1501d01030804091040c0c4d43d14401e4180000c03080001603504603501203482041c020a089000e481c4180d01c415181c1c810b500b400c40074040702111aa1200d00100380b43e00701c80107640c0f400e03c0c00850b03c0d0b8500848440350160030204080c090744425510fa003180c0c0070f544510301a940d5888902c2e084071041c20002103a01e04004100b14003080c1701d400010400b1001c24460340c81c0075800280c982e10800b1006000402c403411041000302c0c1082003124080c6200c1c001c220020003800c03d0b1009400c649400c80c441d600300720010307454000c0466240c5c54003510442e214 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 464357383 1250 464356133 464356141
    0x90c050d0f021b030705070f0803030c090d140c090f130b0405030906190906090311090a060f060c020a090216120302070f140d0906050a0f020709052508060603 70
    0x4009407140d203000c0030600d502809440400007583c80b101e010f04105500840d651001440d000d810018290b0080c002c0034540e0780d0402140d00044200d980c810078403490740d642d0742e0500e030000710000781c1220054148181406401c1e220000040d4483d00d410040f140e01100e9520040400f1104504807030082c02c60080d010390600150000a070250010300c56801d0300d052901e16004250b00c1e0300300002c810032803820074491230700583c0c001610b64050b00c020720700312509a06640350f00d40d94601a8030214000e9840a000a0350003580781e00c10005400c60758500f108007640d85500906410419205174410080d01c41c00040c116828801ca6080c201c2c01100c5000f5000b075503e070702456150068542d0b090617001c0081c0e00024800c0310340445450f00c9400e0358294002403d1085151442041100f018800741d5038042c06460741081c10784010131218900b0440390782c840d400490402001d80d0050500904100601c041c0c0c1140203043d40c046080300b01000c03a8101d800200b1075000c2c4050319580e4000b00c0404c081 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 464358633 1250 464357383 464357407
    0x1501061d100e0f0d0b01030b0a0203093f0a031107020a2c090a1a131401020408010614030c010c0c05210f0c190e0a0905011b09060306090c05 62
    0x8140b640200030204100e0b0402100850480711443c5421142d040b80c4100600403c5040d10907d0b40004550804508503c2c0c65000d451f6a00a080c01418039111200d02507a00d820124420b0486000381700c0641c1840c1d2000580b000c0550000d01e59000481c1c1060f07644038002d0158002e4602082c1c00801c4031050a02d803804094450601340303505d03000300b81d010440303d4000340c2100005025181c3c940003440203007002d007408040300c1e100d00da0a00850400c20180650045000e050420b50f9401c944d095004400c20008280248182d0703108044c65406c0c50300016903030500402600c4140000c0d001d0358504201000111114860355070014100c0014003400d2015040004400038a00e0440c1203170100e00da605e00c4c03100c1c074003101c502c90320100c1d40c0250014400e074144084069500006040039600341805c140c0f40c514a100000e0810389890741c1c0d409a4410701c0b0b02500f0106103440610100c2c040707a115514000c04001c101d014000c00310f400c0080000d813008145c0b04001d101c5171142d94140c24000082c8403 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 464359883 1250 464358633 464358647
    0x5070905030c01140c0f03270402040b121906031a06090f13020a1d1e060307090905071e0303180e04030c051f060504050109060b0f07050f1501061d10 66
    0x80d41709030b118140201902030010001484150100341920340d401c0d4003800c00072245000080602e006a00501040140b4040041640c490304012a28403805581d40072603400030601480c0d0b4a05070b14142400042070240703006100c6007800c100f4161000d50b640f05014003800352410b0707a01c030180356070820000c0c4070305123009100240c492004000d0078582e1b0f555014800c500d410a55000e21310041d05050084910b1241e00500c50b540e203101c0080038902e85440000e480d0304c00d40c030440303030f0480d100e02080c07040080611580c0302400d0308203e0030031780c4502d403465002060940c1c04200d002c50281401030180e01c14204002d0225034040040b1001981e941e0780840d080d0340003907030460303441c4036000344210182c0042030084c10304280c40000240700c40c586000c100542e401a0b0080c1040c03454404107101c03001c03404040380c1c881b18503402c401390384200c41d1401518102d03400e0140d95081c007546001200150100c0ca605048450545c0c80000e44000201420620320001800e240c0c880411a0074080c0c0034082d0074 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 464361133 1250 464359883 464359897
    0x120403110a12050a020624060a090b0414180405191a0108010e0c01051305190e0103030f030f051312020f0f0d030e03030129091305070905030c0114 65
    0x107403070035081c1540d507500c50400d440b5003420200c0c0010441101c00341e4100201036004c2c891340090340d1461560986909070203d0f41c46c076079000360320015140c60101c0c041c0311030707a000305000312203070360303610303038811403848207141e0003292610801803403820000c050f10384209540a40c1c0c010028040540d60350108801401071944102c0e18001170404401281e00d038016040c0c001c19031500007081d05032150b8a8a414803000c0201c6074180300d4244459026941c0c1d00c01104c003035460558045071024180d40c144505003030103610451440c2c0c0103030008010594030041714401d0009645081c08442e15002400d001d5402c210740c5e0340000280103040e40c0224010911401e5646600c1c016598000007164806042540c0360418100030b84c0800c5021000540c141301c1e0a03d8141428055810755040212142403a015520301104201404ca01006828407020071507900f404000c2c0000303a03030104980340401800c81121680e0118516500000300740c180800c00c48500300c03059585a11000032034100b0241900301c61 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 464362383 1250 464361133 464361167
    0xc06070c0212030706140717010b0306120703063c0c051b060402091602060c1e07060f0506030111070f0f02060403210c0f0308070c1709090c120403 65
    0x7160325104003200340020151385014040c00314400c00f5160303010040c100c01404034400c00031040d0103400c145040002c2141134402c050800e030b9490b01c441b030004507000b10341c040b4204640241c16001003003003075a50040e04281e10000c0c60100400c0c1d001c800e26415995074029403290110203600340b16054030380d07005200e4480c040c20710030b04213415500d40c9048000c600c490b585243d0700c036800344010b61404900d09540100030100c1c1900101d44400d000b52100b80c05403000a00d800042140014a4200103003ea80514401021915074100c0e08100000e02125485481d00740e142030003091300e500f01801002010017024111920340140760f50342c0469062180700a440402da9059040300503a41e040080000b0b600442d80014140e00c43d1032502080380f01921090140003554100e40e000a001c00d5500c80040d8050412074555030354020251070310036103810001d003503104403800b510036010756001030042e00c1c0c0c065404440c6640ea495542006206668035034001092110001d000248990f064800440b000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 464363633 1250 464362383 464362399
    0x160e0c0a0306030501060b090112090317070c240b01020d0f0e0303040f0e18010905061305160f06030b03070f03020d0c0e070207141f1209080f09030706050c06070c02 73
    0x40e46031300303084880f00d0300521100440022074000079030784903465003e40111000c00300081501642d000d000c0302101c2400d64440c69148001036907150040d1a10002c00d030304203009415080c0c0d001c245104000908061480c810319155150315a94400030ba80e0249500c42d882d0500c00d00c0050a090b14100181c490181e4503100410010408404d0181400c000780303a080d034100c1c3e0b6402c050202d448480c541c0440c42c001a0315029141001c0340c4002511074220114180b00c0462142e6420b06505000c0d400507815260000101c00190460300d01c1e002c0d908031a8581d8003003104a20b80b0003056142c2c20f0702d1281e443d90b00307040c0101b032015240c00403404002d14030840b041218166101d0900340c0540b41100d8030005071708440010171040c203800038030203042c2c18200c50300c840c248940c10307000c1d540e0076443c40b02400304000c100700700f4501041c66003c2d0383e29903040301e03d50340c540d00da0200e0540c0039485490341902030301900100142c034a015505580e0000300c541b0142030780303a580310070031200c2c021080e03000c1e0303489140 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 464364883 1250 464363633 464363639
    0x30f080613090f1a070906120902040e0606030706050a020a14010915050103020f090618040201030b0303220f030f0b0703090b01090b040c1e1d150a02160e0c0a0306 72
    0x15901c942c0c000340d8403520348100003e82c0c6080a40000c07010324080d03d0460211420004103075800717680e03041a640c060800e59000208409580c2c02400c0e000030094000d490020041451200040c0e00c0b486440c2c11400c49440340e4550108481340c1c050080d0810242e40880e42d43c000080a00c08441800c40c540c4000044013615511859144040700c1c040700e60103640e400c010301c00d509100030010410801a95940117070f007004c8020810541820004010001024004c1801c580c0b203500300c1841d081000b07080701d03110842c2103034404804820201d80100d01c80c40c0b5800041c01000642d2480881c0c0e044940050410456100c0c03601d2400f00400c500101581c5400b040d00040141c02c089001c0d03c0644800100c06100380140412184c0014040c0103212204c0da007000c552a03680c0c20625241e1491921805105402403052062101c11140c942d010300021101c21080781c1d9100542400da035a5800c4038816005082448550102ca024844443c2103100000d2800081040200f410201602d400114559 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 464366133 1250 464364883 464364919
    0x90901140c07050c0a15030f0603020307141e0d260a0309050c0d0c1503020d02210705030f01030803220605190b0609150f0a0306061b030f0806 63
    0x1034200c03040c10202001141120074048100710764410180296601c60b049401d1802035521040f849510310308041d110700002042c0391407a0013010096a002d411511855101c08214000306a80c41046000350005400c580042c000c000b0620701c0170f5005400300410b4491a01c54002c45e602c015200c02c4566401d041180020004800034406100310303540c00101000c09107021401d180b000312000340b084003019503820205403001056005c0300c05140d641c4074440c5110714264040d0144612110100f4408244803500090242000c40410105004865183e80d1418240c40c1ca01059031007085040c411001480081c0301c0303200558124420091241400d403d00300801803907040b054080f2031682e01d9805212124504041d20803812800042c1400844010b0001c01d006c4d0007408086482003124170349625820342090111101d9079200e041181d035440f10180f01401070800e0b4812500020742c2041440152039180c04c00c0551b4503419540d10aa407407919408072407562000d400c0d41c2d88509500e40c0b11203001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 464367383 1250 464366133 464366171
    0x38030f0d02060f09030306031002130b07060605030c0d03050d0221072a211808010605011403040209060d0201110115090c050a08040f0807140f0f011505090901 70
    0x40020780c002c00ba03a282452400d60b2100019090941a50003401481042d070390100700f4240d81ca10261005840d0124907000420914040d80650000f013400204507091003165000304040c0d990540032583c0110501e010b2207080700c0c5528001d03000420034002d011040d903080d0002c0812601240741918052000403c1480c0510180c1c1c001011540f402c0e01c0100b640a00d101c01221342c4242e08000c061441c03642c0314002d0130540c0e450b8154814070030109030301d02c044c01036000c40d40490704407900000003602c41030424020039540c0102c50209203490180e11065650b0307021640304030340c05803400070182c1750542405404a80c1d030b1012818080107810700b8080c900e00348581c524401084070981340305480d1115010880d082c40f4a40020172800304106603100d43c001814070b40150303100d0020010900c00c2c2c00c021589004104000705100c05082a24041880004000c1c01213400720090398880003121014074205e0705607590141070b00300c0750a0308200e50b16282c02c0041d80b03d1003020020407803810300c010550420b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 464368633 1250 464367383 464367403
    0x120c0303090609010c090504150806041208090c280308160606080307020607080313060212040203150609010504020703020c032e0203010308040b0d0e010504030e0438030f 75
    0x550000c810000d0481042000340c0d0802c510200800c0508180c50b03000385080c8140c05200d01490326206241109601d441c0490b0003415048240d030074504051820303803121351103401540c000a84010215030550404070384940c8454000300001202e4000709021040010540000d6645582d005030001c04511700b080103045c100c081a1080c582d11006e07141002c112003082d00301e940998018082e400c01a1034010440780990742041c092900c3e0350320a4210702c01c001c00410024502030010031b8600c4901d000510040c01944200c0940e240c02281141c4200d80c1807044901942c0146034800401090420303030b00400c1441c0c001e105940c900d50f05000480d240191005404210102e00d1100c0d603c06908202c2d0b545002d0203484d000d61455155480304640d50240c0d0081000458000514007070b14003165010110016a00c0000d100e180f60030304020f04400aa1078000740600e09111081d42007805645424210b514003c030303052541c202c2c104841220035417924003c0d816202d51030100c0500841001aa50343d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 464369883 1250 464368633 464368657
    0x20418050d091a04080a0f050f0d02070f1707090c02032104060e1c14091008010603050105010302160b0a0b1804061a090609041b06080402180f070804020312 69
    0x240c2c500e4016110304603030550b08040da01110034001804400400310b140b0b2400c940120401d440034125040280c100300313200c0220040d9114404203401c0050300420000304503100c80340c0041d00256140152480c413605240c0a2010783c002c02010710a2800342d80c41500626041d1040300c0c1030103402c2444c1c0000b10703204050840d044120000704800c019044c05811a8140c07640094491045034aa417000762020307100442082c00590f280512650122009507052580010180311405281943c00b900c014005e00500380001e0500c0300225441d400b0f4000c83c0c48000c5842e40044d01c0390f0554503125600d000140220642e56182d0b00c5020716036584012101c0241000c030b803500380c1818249011006c40703018072071604950307100310b03081030b440d07541c10394074503442034041e0b074098520343c0c6034980781e007000c09044a581d036040401034002c58030940c40810503101d91f10a4840d1802c98081c01c0720032480781d0088503800c0850000c0340010f070101e0b2280e00e2490304240301030120348007410a40380d01149500001d00c0004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 464371133 1250 464369883 464369897
    0xe090609071e27030201051603020a15020702040e0624041506120c0309081c090506160212180607030c060204090b1e0a06050a0e0907110f030906030103020418050d 72
    0x403800e0343d02001d00c000505030040e03d9200519590000e001c0d4003481e8100b8540001d00003284080c14028040a078440380c2c0480c3c400140130b110301c2d005009400403d401e900071440c19040c00856180002c11601403a442003280721822081202140c0c11442e0004244e081a15070025000d01c603900406800604041c1c0c440c100c0350703c02410740e40111071030086440c1c00c06d0f003401034101c04200c0c1e07101280c4289400c900740c8641501e5030300b041c4016100c1c0c3d580042081c89480200480380303008107100c400f09041c0381d00351240e000100c10300380380501401251414402c068420055140b505000803c1c24900c01d062014040c031031a00d41e0310032038000740d000382d00407611421400d40360314100d0b0f00300f8a4440d4031a0b0325142d07644200013180c2c020003a03004d00c0050041c002842a000c90242070416100000103028468034a0401001800106a0114080c0a125082004c1c80508000c4103036210040003411550860381b81d602084094041000403500e00100c0d075102c0404547c060040e03400841c1c454541007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 464372383 1250 464371133 464371157
    0x60801030b090606010e010302180d06150b0304053d020a0e03033c031006020c010f080c0d0f140412020a030e09040206090324070e090609071e 63
    0x401c81140050038040c8a070086400c00100340c0c0c0080c16640f82c0003003840d0058803020100170340350000c151501415840058000d54008000c103d070001d841d03508621140c10744050752145204000e003c140c0c1d0003040c40e000030307100040c2810100b01d5211014040f807112200b14006240b46001c0c2e103850104441080e4000070900441608070740300402c00720f000d8008525020b0700305010540303480b00c100d01c0440ca40040106041c1c0c5030701440c4003040d4800901e10303c0d65a040c4011801c0304141240b2070b0300058090080070b0000c540c010010307602c69a0b8141c482d0b503000d9907030f030310f4008283e0f20001e84000320554403040803001e12241d03c032b400104401a0700d20f080905140c20004580240e51005208551140c040340000075030004070004007202c20360700c8205544442c400101980108a1070f180c0520440303541591120449103005d00300c01e00814603040903200c80c41c0c00c68450200d0381c81c468009035201c005c607101d400c2071402198002c0c40307458011017075000700e030501d041c8218140440300040c00d514400c0f = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 464373633 1250 464372383 464372393
    0xe0109050a170c13240302010815010e0612150108060a030b090325020307092c0106030b130c0509060d1b21060509071a07080d02030106080f0609190b04090b0106080103 74
    0x3000c5d6541806005c9101501d1a0700007000030741d000388a441c0007000070f200d06500ea4040c00e031a004841d4028a2280c9451a01ca80d0298802044880d42c40f0074561800c1d8010950043c05000d020340e0010304000b422f141580c481d00c07d48040580180110701c41040258010480200401d80480700d18071010854005801014600f581982000d0300107032628040c42d103600031844518600345003407104d504030b1641a03020a0f00500b0035a10180032046250308000b014031465101800c018403d80c4112034189e129414000000c80440700c680e008402100b4400204010014201421841021b002401a240c0f0b117500300c180407641103e14480807103c80341080101e14080c4036031055900c0d00131f000103440d020803030240d042c4920082d4a64040000e41406010b03800301220a111844401555039517901c000c01481e8007411681c004440c00e14501060345850440031603400740d14045004100303414869800b800400c0031891895025a642a1000000d0a440100390080515444413403603580b660401c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 464374883 1250 464373633 464373671
    0x121b0f17040809031e060105040c0207090c02030a1202070803010b030a0b0a090e01110c0601050f0a03051b01140a0917070906081c0f050a120f0e07060e0109050a170c13 74
    0x10458a52031031021400380c1c0d170000a6420b044910495002c03462072000c000984c2400c040b07402400b40d0034140103c0f0103196800200925642500340d903a01900221449094102d01a000c4020100c080c100010012145484065a040340310712000007400001240090b410803010ba0203908559214109005454030a1103040010484481010324208a8400c00d03a2600414058588521100780000e65186c94500000b0b000d03590180880351005030000055400c0b000b038042407400900000700300c00c801074120065990005550f00d4001e81c05080208001c45804030144030050351150b454001400d071364a0241500078111000035105082c442070112500510405484080c09510765050418950200c21900c0c62501881c100c40e5a10585840c1390240889019403c002c81c00c3c18070840414074040340c00e108649007600c0713100002c80241d0040d10032481d01c0c41a540d10034603840c401c12141c0c0030034000c0c94400700020255000390341ca00c00001c91340d450000405041c180e413a40c0541c40f018540c03031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 464376133 1250 464374883 464374903
    0xe0d0c0906060c021c0809061201050f0604060f120f1e06050405040302031608041d06011106060f060c120a090f050307050f060c0a08030106030c121b0f1704080903 72
    0x1030181c80e44041038020466503011142c3c0b19005c948080004401d106440302038640c10030000708455a19030030401c0191100f6801e020300b80c403910102c60b10700c0c600d207402d8044a003158069104c0d41d40d40c0c00c103030790182d0304500c400c100641560348419100004407024800d45500c01c0d40800c2c0707a084400090880c000325083d1f030b040070307000720718041c24040401e80001c10340f402d820040350500d090400915002c1000e0040da84000f01201c010031000c1c20105e09008080e106120a076100315104101b030b212a95a050140c1c1d529800c06048424131085040540080c5510031025040b60700307010300c641a01845910034030f0190000340e814041405074070501c1014030010700c412001001c0107820000040c6410020030b00c03440c402c000c001000305c4040000d014040007690400c16141e165a554030014000d0301ca0310300050f00044610210301884040303441000140f500070714054240e0400f1110903139150100300707149014461f8108600c9040764031070590f1032107144141d500340d03140e0054000b0305260030403890f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 464377383 1250 464376133 464376137
    0x1f08010605011e03020f0f0703020d02161401030905060703060302010f08090d0509030109020904081902160b030c0f03011d01060206071e0e040f0903080c04080a120e0d0c090606 78
    0x2010400a40e03a02c2841160a030300e103204403e580c03481c0d5030001d078000e00c1031085070802420046102c1c201c4801c0a009003607d40c4c00b80d000d94400c44842d071402ca03141ca20800000107004070f181c6080c80300c07890441055107504010704000a42d07150315181d0340d2034040c088440000194480070b0070700455a20052039010114603042450780c900346140c0c020385802d240a000c03802c06c0701c041000c4990341c0e400d4008081041e005045010319007401d003000c00b8517502c15111059039000201b0541d1000e4800554032458000012018044c2c2d0305044007a102da50020341000c000520910103a070700600700900640c000c1c00b640441001509030740704605420388050f80080151b4100d00c04202c2d03c10341280070441503d2030044007604107540c8050030748a4150030182d40c0c4c0c1052914010600540c0716074408082203000c2e85503820070360360304060554079204502440f036903504000a28400030f2025a4940c04601e21814406203072052035011600311b94400700151024170b5603030740400c12100c2d58481c6001030320b114 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 464378633 1250 464377383 464377391
    0x303050901021005090616080705030a0b0406090504050106031704080a021903020307081038011b0609060e01020f070609030e100c173c07080706060e060907030c11061f0801 76
    0x91201800a00000742090f042c151030b4dc0301d14201c2d0390f40783e016802400303e02000300310354181420168024200c50108841049070f610803101184400c90588049503100c000801103940c1560901c000b020305060040d00791959420b0100043e075082c06841c0280440c00014000800d880f581d0380251000c040d45020194804480700081c100555945003102c0d1805810229440d10318004031010741d031001c0c604c05541e40301d048140811201d504007a0130745000740014080c5002a498107400c478401c9121030b8503d620104104800a072103900825001d5001c0d040481c10402c0800c0800c02d011030400381100007a0301c44c1d015504105500c0034008444030800a440e08241d4200903451109440c441c9210318001c620b900d01c00c00340d44142030b14809880000c5010f0f1102010b2030303c0c07030703054010f000300301e4902c0d040180c04555009504206071103072078002e06450058840c50720940041207407100f000308102ca450400020007004200300d901030000388100340020100b80b0390401000c1d03080e8002550301d07414 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 464379883 1250 464378633 464378641
    0xa0c030f03051b03091f09052a1c0c060f30021b07060e0307150914010509100e030f0a0f031107030f030309060b06070c030305090102100509061608 65
    0x210318020000c009010321550780e256014040c6c58842103800c135080c10740c40c81b20380030131140c02e64000342e803c544540c00300d440c8200c2c24046038503150056403100c9160303c0342c50b055000d186094680d5100a0141140710441207000d500c81c9408032201c0d0300680d000c200e00800340d01e0b40b640d114000190300f480440e80741d4504000c0328440e0b82c0c4c85480c0d0003000d002680104500340305c0c0d1440684402e09090540c100c51105559010140804241e00d00d0140b0a010b042c0001a11494481700796580180700c1d503403050805d00b000c4020010034420414181000010b02803448207440b0403c40342d0701d80345541c84070244038032001c04062404c4403c006621054022481d00800030780c103c810b070381003d54982071101096a1404449261a8080d0320140c01920709103420700505400d54403260311140200c00500115407060306106842c410b283c80101074002c08541040482d1140d000b901203600e051054480381c0c40b14401840030340385c0c2a0350150140c0c06c25820b0155181082c1011840b0100c20b042c010001d03d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 464381133 1250 464379883 464379901
    0x6010c08070f230105060906060d0209180703051e06040f090204180605010603110315030c281a090405150415080c010f080117120703020d091a0a050702060d020a0c030f0305 76
    0x1f070090300d20f40c00347c400840c90800007121601501c1d614040a0802d150490721105a5561810103071800f0011905d0440481c200c1400142c0da40035450904007540d0705a150302080c840109910300083c0a0560350780101030050b0746034051f1910000c1d00b0340c0703610300350360403800c108080720f0040e4066400c0c1894400d014805079141d40030b0701c0e4007130322551444071084011400300381000082e04500b64400b20221881103030119141d400d54444070204070f2880d1044c0c4612030400160003882490351031b08002c5c0320480c010300c2d10740c02641c5e00c04040600c0621003c10b51012170705640c1c00d0000f514016824440510090400300034024600e0000d00e0280c84440c00704034003a01d0b2400600030b121801024140001091038100300319200303c0700c1040300680d115080d0400945030300c80384180d44006401307600c001030f0000284c2c05420281c0f8101412038502031b6030007800c1ea040d07840010103e802c05020701c0b8000e041c41e82c900c043c111081541d00c400d10f541600740303030007021044122040d805142ca00740074800304075 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 464382383 1250 464381133 464381149
    0x10e0d03020f1b06090f070501090504051512010b040f060f12050c06070b01050306070206012d090c050913060803040e0a0e0706091505070b06010c08070f23010506 72
    0x140d080c0141d84036018840d14450b40b240d06000d4100ca401c44640c0e50b400c2c103001407154880c10010096602109070100c40c1900c03000144542400130308000001c1c05240740a40c000e0350080128080064010314280104041c8000d0004c4050035035501c0c0140b05207801c0c14001e82000c1018024104001802c02420420503580350199444655200d00c00e401041001c004074003142600801f09611003403030b0710f0a010851024042e45000303020740707000306120030300011b2054181d80341441808441c1491071040d2111170070514611070716802800780000c1380c50f10352244c940060300c0c99590940d00c20300728013800804203a11408144130751621300100b1900f040030099070240d0702c0000c403407842c54440203800c03c0503069004407d078141c011282d0008020360000281e00c126040c03040441120308280200b524a800bc006014000c2440070000800c61341c840e00f240a0214481c4100c54100452900c4448141408002c22101d41d1032507101e429600c111000320040c15408007009100350f10f44080803e20704 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 464383633 1250 464382383 464382403
    0x130312050c060c1801030203190c0311040803030108060c040f0501081914010e1b1207021e071a04060c02010309140d020c0f03030304031403040f080f07050d02010e 72
    0x88510464086140304004450750522240201c560a0034000b10000b055441103811401c040003c41801d01c03954040c2c000c2e64402d20721030701c03519101c00c0050340800203840e2080c5050200355540b41c158003031100c15800f51019000c00320045480c1d605004034185000005001d05c1c5000b00e05100c02c111201400181360180c98080ca031140c0c458030390002c2c2da0a04003203a82007242c000c1c1041c45002c0310b981104400b038100c1e003a079142c8815036102c00c05544214540300424501400c07040052040b01c0342c040ea9215040303000f603c12a039190b4a0340c0d0740c3c1400b00000b010990610b8006007420071001c09984071200700841290307500c502e4076103800340c041d05000f40000c00a05140e1144001030030301c59486900b42040c407500050703488010030004000c2d2590f1071150270300c0c840d80341030801084a060010950740300c0d59041e16500f090f0180404003004c5500000d00845014a0380a4a080010480c00c00b805880c0050318019444040c2031601608000402401000710780c5810100a00a4000a486224 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 464384883 1250 464383633 464383643
    0x30c011d010509211902030a020601060305010b090919150f0605091e0a0305030c01061d0906130602160c0303020c09101403010e030304110a0e070c0312180b090d051303 74
    0x34000c086400c00c25802080c2040b400b1a805c52000c8114940200c0101044102c0d41d080c3c506603038880f0401d6048850038064400c0f0010b050180c4003a038201003010540080038449a4241c1d00051042c10055030a41010700c00040c50b40c02040001c0081c08809402412490801c1401c01a0080110703022042d2035042c00b000c01040f000310351b21625040740401c091504001500d9440d03603203402c124040e1066202d210071180c071800c0642080e9404400e914010f400340c40142205858000c2c8000700b18030b440d0030a0f50300c030b6406c00081200d00000c241e0109468468010024070f5032075820007900b07140400d40311601641c010010000c03040c0c0c40030030b00001c2e1003285005c10300c00040c0f0000700340100540810248180f00010900040c045a12034440c00c0e10000c40e891042640c6400322145a00c00030303a862000300d00c40c00c0182c1c000034081c240e8500b0310b14190380d00084403852201c044104401c0503105407060b4011001780004076400348401c101992072814014942006c00d0717103071001511b09102c0901 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 464386133 1250 464384883 464384923
    0xf05030703020306041b020303160914040b190f03020901050904020310241d0709140d020d0f060501061209030e0d0609140606010e0111030d0f0b03030c011d010509 72
    0x2015652075115000b0489000506c404424103424003039540c1e40b040e15010303801c005140310a00c2c0b0758842c07103085054481480030340e04e8400b6014203020141c0340d050340155101100400300500c0c0c2666820400040903602da2000321189580103002341c1500680090b80103960b84410080542c60018000000301248840007e0001305030200520b891388403155002d00044001d8001040d80e0b0f007140085158007800011001521500b00c15924610f1341c0c0b142e0000004c400c10800103900e40305035a00751aa0004d49401004501d50740d8840c003030041a40c0032204580d840700107204082d8000b0f8419440c0e006030340f0400c40c480071624090040c01c0300d195501c2c80f0382c464142100800c03407103410801e10303107074006455001c0056001d005901e8003c1106c0740b50016007030200710350107580b281c00d40d0202c00310304101461030700f034407485031034054a101d00e195521151140030707881e22501c0400042c20a24150000000d038081e44c036068061802008412101c282c0c1005e05000c10740341c020801c01e00c0c110100989003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 464387383 1250 464386133 464386141
    0x3010605180109170114090a02030d081003020d0b040605010504020309030f0306061b0a1b030b0c07060e070603090b06030a030905091012030915020d0504140a0e01170d0f050307030203 81
    0x843c0c080c1c464001e00da070820030f04007001510030b05410030980810404003000c02035942c102c825584915055002c1e602d98014a040860f0310301595015412042c5221101c08017503d1360040b1b5030000b141407045891441d03600410061154a06c03411b4050901114194518103002142994078002c008084506903c00004144103a13140003c071041c410300c810040a00c0d108901040fa11903031043c0c000d40300c40040000c2c08001ea580c00070b000701965445080020f460721920028003503a04090b000701e4846564403503900002400304080c80c014543e554012a5003c1c0c21b242188600c107010b403019010b5801102e0b0003000a421000f040705032401980c26004565891007904420603180d4001c240c1c50321180c1d0004e09055002d02c0c82e000b41c0d803c0c810121039035880a51308032b0341c662030240440c0026100344000c0c80600d46090b02c150f030b040780040c1000c010544544120700031440a92040c03085a09402c603580342c456040c0002183c0c08410b0500505070130001002900d24031006144000300740d4000005 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 464388489 1106 464387383 464387387
    0x170f0604020604090c2c10030902090a05370b0f092205100204080708030a051c06080307050d031503080409020c030f0715050705030106051801 63
    0x810303e41032400e062200200504c1824004200b40c000a07000065110701c3c01001c406e085a02c2c44400b441c0c220f040200c00c50000081a091500380051400565100040305500c0400c140000c207080d540c10b5500c403401c4205070304c1d0300819520f015900a100608000c1002c2c503ea9000040125904140403c06c1029020030199441404900001c4403102005e8040748103130214503640740700686546e256801e2041c40301080086543c045010403103070008110a0b80103003400f2002d5031620100d298001e04030720603c2403084a0550100d18031b0362a4a65a1010340101000c7d801e90341c071880f091030b00b252280c0d40c0c1c010000000c0e0a00d429180c0c0c407210100c4400c00c503030f03102c0001803606203490b40503000b07034100214142060009105001105007190300600e0700c03c0c820001c0190154840c52100c0031a04060031190070842c040c0014451940c02408941e5160203003041a4042840c103401 = true := by decide +kernel

theorem cover : BRFrame.Cov 464208633 464388489 := by
  have h0 := BRFrame.cov_init 464208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 464208633 ≤ n) (h2 : n < 464388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
