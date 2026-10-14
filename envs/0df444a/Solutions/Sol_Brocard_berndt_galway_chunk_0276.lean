-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0276
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:54:42.554908+00:00
-- url     : https://prove2.me/submissions/1c9e39d9-7847-40f6-9014-248c4ef5f8f3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 49460435 ≤ n < 49640291 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 49461685 1250 49460435 49460443
    0x121808040b071509030215090c030627010204050f090403020a0b040b0402010f020109020d02040c050c0708150c04030c050904020402040503010c0e030607030605150c12160501060611030a0809010e0718050108 91
    0x50010090b1f8041c3d00000000f00314140015400845182690b208002e01030209061500495407003200d00c80380c01341c0c003900e0f80421103000c5244428000841c00d1504204c0844c10102c0110600e0f40b1406050300014109442004100d00c887e42c00950044141014900030b4410001550101d010460007898055043d02c140f04014000d600181411000f42054080c403000b0a980201d4104016040050300801d101c00c114500040c07421100502500b05211040c00c0080c0d0060941600014101300c10408103841050560a55004444142d281d403118400600203205541c4115095405c043c554004540c0100c01060000c009034196440ca07901c03100c0031003c40b811805003e038800100303041030603210141360140c0090f592410854800041c48001d054981e00001c510528002800c03070745c07104106080c029100100301b1401d1140000810b50481a05da010355480348040042c41c50005046030300940103041801e42c1d5030155100141c98105201c1300c8240c03545041c00c030398100b070000908048006 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 49462935 1250 49461685 49461701
    0xb0907171305030f0f0706150e04060b03030d0903050c07090b0d230a1b0b040e0a05060301090204020301080c040e0a0302030a0f11070e07110c01121808040b0715 71
    0x9040203556500d07240364140141004151001e12041c84040440c2c4c8449009002502c1c046826a403035882c0e526000d001c0c1c0b402050300152034044080c007040b0340321850300b405d9040740c2d0142000c038103040724a0100340f0394004c2501589140d420a02444149a00030000303102281040090710b102c5e41d00c0781741c8001640c410b406a2900324504240300390200f0522130880c07a001c40501c88107140c1050260659142c4944102c050f80c508031310392604286500c600390000c00a043d06c046090a06103443c1e00c1e4003082c0c03c010031074488551241c1c00103480d540c0a5105114041d80104110b442c1e50312490b0050b550504000554051490300e403e014244c0000510071303d00340ea06a000750301d04903440c1d81c200c50f183d9060b400c20041c41012484400c51103030a00c40310000d805143c2c0044241d1400c036030000e00401c1600c0c00d02c25603800111500c1d8260340e012103109d00b01d2001e950007007900d01650201c0c408000154201802c040004036020408403002d00042068502489114070f18910380e070550005c6503994 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 49464185 1250 49462935 49462967
    0x140714061501020319020a020a1e080a05060106110c100e100e0a05010c02120a030c02090718050906030a060e06040c05090c03060d0f120e010906020a03020c2e030b0907 74
    0x380070170800000c0496203034940c16054410b54007102c0c0c040e40480c6c6202e0181e0031010303460303024003c2c480c00b1103150100440100300c40c0d03000741001c002030b071079240d03c0e400103003c2e0728200301c6c80c20100304034030f401000600ca401e0009024079024003803201c4010010348412003e14825610b82034901803461040d01c1480340e43c0401080710300505d01d4140107440e000ea52140482e084031800407044014a010700c50b480316a40a6110010080601d20400c070b07013994010020700c148080300402e0551a5001c0d5040b00507100243c0700020715440f03200c0020302d40149071500401e00c900f08241001400d1010074018041da10881c061100c00344c90f5000c004010724200d881e0542c240c424130003e039062611468614006001310400801000c01c1e1b2682c260402488130342c86e000c164504c450721059680b01103440300400701c92000d80789400269a00a40b03441802c03251911030b071003580c0302c06044500c0f4141c0c0540c0c60b004800c45404035500490240161000c1184d00c3e2080c0b0000d80020f0500b400f1b01c5001e1604014 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 49465435 1250 49464185 49464187
    0x81833070203100f2d06050105040b09010c140a0507050909070b18010e090901020a17150103020708090a060908070602010203100302010c03120507050c0105060307030f02010f1407140615010203 85
    0x11602d10f0400614a1001494515886508041d894510741074044001607403800030500c00e038140c0c800c4005032100e80d0300040c10004104030800081c01c040007036600c0d1030000d01c1c01d44180d070268100a0700302c1e003032004041d05d02c1c05043c400604000002a14404848054500341015038407483c82d00e450304454031403080650010040c01099241b140540c50311640141000e1a8100c1800c1c0455412042140c24980d5698000344074240d098014036840382200d49041c0c1c0b1065844c0caa5041d080715640301032325906040c1c01003001e204120b484400c2d01c0940e00090070480c07503203a80e0740004115803442d208402480c080c0800124103248103000726031241a02000215110345942d004541c012003100d4241c007088419203020261000500425000b04c596941e1661501c6051120710308641001d4030b8035210350700c020350404c00980e4402d064a207039502400c0c2001840c181407015140180d04400513100d001c2c0c009806002c1084540d01350b004da01c40c01044600302c3c0e444503e0a0308030020080c509001d640 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 49466685 1250 49465435 49465453
    0x70302010f02030d0f0203070806030111181807030c080a020c070302010e120105010e0105032b140409050108010203101509050405090106081209030607090f03081833070203 76
    0x101a1620707503107140c10761045074035101039a0600800c40d81c1c1c060380301d50303100d4000003448001075000030b0594000d4070440080010080d03503141d1511130320841300d0031411484900c00e0710003207903280c4800098504030821004090700d04880000c0c010804d102003840880d0001700420f00550041c0700b92029007203144010000c10381160010b44040540c0c0c410107034401844581508040002e000303250090100381d4560350300b941000201410002e0f00381500e01d01803828a2091b200c0e8082d8515810000c079a400c01d240b4018003c0c0c0000100e200c0d0b5004101c003e03080c00e0000600d14415402144107003903085581310070341d4070b91803c2c800c4591259842c00016035091003d02c014039140d80080d410801c1da000006400b96104c40c4582480207a1101c03e04280b0082a07282d00d50a0a0103802e5000c445d86c80e1604010b801c1c0b00301041d030810107000142c40c140e001305400080c10900440940107a000518070f034905403e080b03614800c0b011840903401c0a9140c1c82c1c41c100c1440040c000d48100642c02005807441e91 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 49467935 1250 49466685 49466687
    0x60807080c03010506280918020c03251e06050a14060f0307090c05190f0212070326150906010e010503040f0c03030504060311030105011e020a06060801090507050d030207030201 78
    0x10300184124084500b80d00c06105000d4010f000c1898034606035242d031147c051034044082c843c103290341030078a481d5004211091a803040402151001d03413a901c040490607201d1145510301c0204064000c046440a468800e100090501929400da200b0b030010302040c0d0350f40c5280e0054503e103241040d66541c800cac01062441c038240704801c90070440603080700d840551b2681000c0c203550403c010b82e0045a000070b00c003010259040e03208682c6e8542410600404112000021b40c0c0318800354081c1c105400114a50781010b00c0707880c00b99940d842044c015805d03422a40280400304000b951641700c180341c410007a03181c03420a60401d42c0b250005071540c8182403200001514641e2004004032201c0b900b05243d0030018642c5021000550b0007030740c0d101e80350b0303080840180c02c81d43e0488944c010020f05000402c403683e17001c0b103900e00c0c5140d0708003900c2008002407026403078030031131602c001c0c001030401071302080c0314034154403a18040740681b040341c2c0c41c16640c03400d00890026020780580141c001c0f007000d20145d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 49469185 1250 49467935 49467937
    0x90e0108030703140d140106171e01030210090b030c0c0118030509011b02040204031a0106022d030c010509031c020906090f010908010c02010f0e0d0903110a080f07060807080c03010506 81
    0x10014100c046000041300d000118040b000340c00c48404072740102d10f402496803121960541c00290182c4c071380000070303005007402d01d40700051000900c1003e080d0080700e00c0910441c1b881c4010301d005099076440c0d00f40740746042e1058006400d840310a6281c9075404050074152010480031641540781c043c6441c20000045503111915000e442103003031828094001030701c0d00c0c8000c4c00114090881020004120050512403a4043c0d00800443d07200802c607031080c0303003116151180001c040700c40d0310010b1102107505055008009006049520b09000c01802401c04002000340e1500c042a0610028110841000b00d00900c0f82d0641c0000c0b040c40104054140000b0140c04000c05040925200d0390700e00d041401c1d0f5100d0080240180d443e0000345045034480c0c0100c44000705010302404050a40c4000206240340601c8094141205090b0328901519030040001c0908442400c1c3c442034120800901d50f0b6201a110300030006a4031030008500d140f080e03040758010010203040e00d195034a0981040a2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 49470435 1250 49469185 49469197
    0xd0806030109200406081c0311030108030a031505030105090c010f0306060815031f0f1b1e1b0b0f060109030206070b04020f0d06090506010608090a0209190c090e010803070314 77
    0x1e03940e90010800e0601004040c10b00387c00404201e2288181e024020181c9580854007031b0841414001803000c501b02009030740d140d10961400060b40d040c07010020380f010000c1c1d40500e415510b0b140521007800b0700860601c681420a0b00c0384030303895650035400c07401ca5819126800000318400082030781d143c8103c0c407001415100800b2942505801d02c0c2c4800300d10814090000900c0e80d842d9588411a440e00590340c4003413940003500208541100040c1000962100c8044002c0d2940d9002a00c0d5000c2c0712520405516441c6074041c0100a1902254106080d200d080c1c0c810704181c00100e5541c801c1d5400380a45e5805042d65080c890a0780c0c1e0803a1502c00684100d074040e0000f62004016210080795070783c854060f9201040389841410040e0810b1010f0b0000d0301000545003c01c805820001841c000d80c540c1130700c1c111619610740565061301844140310020490500d5030619640d507020081d10242c500d8604001c4840c0d83ea01300c3e842c0e50b840303030140007800f24599401c0800e44124132070246c00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 49471685 1250 49470435 49470439
    0x3020d092d08030c0708010f1104030605040204060b0408030d1d150414100b040c0f200304081c020f0a020307090509030d060b1e0319020c0f0604050d080603010920 72
    0x200346610b03400c4150564100d1640704c1d955501c442c400300801c1509001d52038590041c840204001e141241c8045c0462145020140c0700e2a10744010500310744442c0e00c42402040b0310348010b40c517640c9078401151241e000176102c040b000d0400c0c1d04000d102210b00900056070000310014240d01a07001a86219160300400550346803a01140401d81c00c801440804450040030780002041d651000030002118081c88100d42000440b04802c5802c68200049262078164a84106100d03a0403039601c078034512443c0c0090f62107019081c4600d15031042d2034140c000040140d000c1c0c1d0070481c007007000340f035680c070b840031005c0c0d815800f141d030801096100b6800140c00c4118801902e00e40140240d08a095526641c03046140c0c4c200010181190f60a0080c00940304282c0480c5903c4d504160350300e04182218011240313400d5a00090340c0f80414003c10403030303c5060828096a025143c0b90401c25207404048202d140810032340d80c0040c1031454180b0640308603a52101801000c1036503802400e0fa8510214009a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 49472935 1250 49471685 49471769
    0x31104111903051801060803040905011d04020609130204030803091207110906180f040507050d020303091e0d050d0e040b100e060c010e0102030a0e030c0307060209060906030f0403020d09 82
    0x1020f040c0c280101400b500e0031f04010740e6154034240000c0300b2100305902010041403a07062101d1841d109400c00340c2c01a804413051a02c03200307240d000a0440018641c902c50603440001d0010412404402440c480d281003025240c2129503101703542c0644c400e14400034038180c1090040180c40c5414449940c1100010344402c01e4180b000e512960b0301d184c26500399080c0b0060008000030030604100c7c003800f608080e00c1040d46003d4903408603907a4000d40380450700c107a0641400860300d09001d221704120a81c0281809089276060070210780b58005051f810f000280740b1a4416005e0030540128640312101031b00b203410181c10407008960b94007410502550024007000300e02c840c41024040c00500040601c001079490800b40039400459041e0041ca0030150030920101070386010100030307241c4503900000c01680e600c130400b000503440e101c0d24450b280c3c424000f0060110300341c00906100d104a1194080b5000301441c0007065901030701078814040da91a003812010f55009020090a100d508141c0110b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 49474185 1250 49472935 49472971
    0x11407050a02040e0a1511090607060b030d0513050301020403150218040e010b010806090402010207061d0d0c0303020105280c020a080304030e011b050c0d0503070c03110411190305 79
    0x16040d105104038205640d4081d01704042441941c2e21000c01600c58504200146e82a42000402c4c40c00303015031842c454078001c2841003d206068000321004440107040c2c80b101110309002070140d4205d80d11080100345e1030b6501203002e0405100b21400d8a4120240c1c03480d01c0074007030700c0d1000b1303610003000080300110b40490f0001c1c58695002e0703440c0c5034a03540004241201c9803400180b018000810307280c4102c0011003404050307600800c000342138426629124030700c401c05200011000509203101c07500300c081c20940005000500c40b014064a00c264000d21550b242c1914010f0600601c40c2d802c1456112440c2c102003815080c3d0000c44d810b0a070740155040c449440d1240c4845400c111025000719503507880182c100e41e401040d071424113005800c10088490940c84a40d501c820742144a070103408441200801d10408109590340c2c581d2150340401c0c1d1030303200d1526460b000e0025265501550030b0002e20302c021f060110a5403540c4103010307880c6d0651001c0404c12800740c07501910f181e8800c1e01940744 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 49475435 1250 49474185 49474189
    0x402070303150f140307030809040c1b030201020316050c0c10020a02061801020106060f120b01050412030306060912021c0311060c030610030b0d02010807030213090e0d090302011407050a02 83
    0x60b03000184280180c000805141564001304401591080ca00c2900803410038400110700509440c2245000d9600056007894600d080e00d040c5040302c602c040550040486108050307054006500ca007502400001c0003480d15942600e081c02012503120458000081190503070030000606801b501e80c51045603950709080d00801c842c3e500004640f6540d69142000c40c600d941c090081400420301803814050b052403410000b48140114503031003888584810071102140e102c0d400b51405000400820b400110403450068014492446040013040340507400217515001a400144000d40240007101c5842100202150311965000102d05210308084402100c0328200602c5110f040d011901640d6420400300b005444000342042c8404c00d07042861030181a110034603e205483d0f130a00b49220992102c45c1c0c1640603005007280710010000c14140000d8225098010440c80c20709002a200a014030036030413100ba441d00d02020b400300e00380f203900007410b0705118000c00389140200b003a034160a1040d40 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 49476685 1250 49475435 49475471
    0x60a091506090209041401030309140d0602030a0209040614100503060301090501090506070314010b09090402130c0903030905030d020d080a02070204021206120606011407050709050c03011d0603030403020402070303 94
    0x200a02d941c08990102c56080501c1035440600d10254050020b601d1540d0060821900f802035403144440d1527140840c58840d81381b00600254408815900c81c540600c003031000b034101e10f03074551141c3d05002d000070755025411800640420058042802c1c102c0884054480741e102a000300d4040d9030780d07031020300414020302c40d410700b0b13500c90400f92140d8149960700806132001c11390204e03000704000004010540c88034045913900300082d14160312903583c1c0c0c000506070741d010200509200342080e0303206c0300507a030042c1748005403480798855040349a1079031b00f030680e0350814440e25000b60340001498041203000740e150940c020a501c40252616440758042400c0e40c01800401340001c2420090006920303040c0800c4107a882405e00800283c42c3c81c0c80001c002c804028800526440001244028400c06029407405404000424409800c200340c0c0c101c40d9520922400008450b6140c2030841e818000301164040c0030002e0055080c14159000c22000790300c150b60843c1807583c0c400c0984203002c80c2c01 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 49477935 1250 49476685 49476689
    0x9010f1106010806040c0e060d02010e0105090409050d12050606040512070305030703020c09090a0309030314070c08030306090702030310061214090106030c0906030f0809120f030711010306050102060a091506 91
    0x143c05810300b0f040a00d1310f442c154001703401045454100c20200601500e402004000c450340920303190080845000c0142c0e0399115150b03069422500740401c880500c8000130f001c9550851542c3c2e0508882039494a0100312801030f503580354008000c00c030401c424940051042c4c503066442041d40d00065490395060301e503030311003502280580c21201204070f2510300780c2d05090b0f202d003000300a014015025074000305460b542d800018188800260300303601800a150980314201e90000318400110b454812940e0740e41c00444a051082202d580001e161501c044150703170181c80010901e860720390800328103582100c15291014215a07880070346000c15005c40b901a400b40c1c070a0000098428203508084072583d09503004018180e003040010000a206041d00a0200341c000f039040340c550318204001141d072021603405824600c05c6030a10300498001200038020b1501c10301e201c010701040c09005600350340041c4201030158101e5000a1020501508440c102501c80d42000e1000d80101d041c1e90200ca0240d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 49479185 1250 49477935 49477949
    0x1206050711160f0b0307020604061a03010609060e0606070206030a05071403131104061404021309050702071d0c04090c090512070513180215040504090b04050d0903050309010f110601 80
    0xc0305003081422550031941000d004a81c1465185180a500280d81c1b508c004d800180056500d101c081013a5605138451103038080000c00074846d807540c801003100070780054000d00805168220200b01c5526294040b50846076014082c81d0543d50b82d8000b039402010020225003e101d04000c1039100440010300451081601c1240c2c0b4140c0001c81c201111300310380c107080050040e850684184000f0300c00da0200305a000c0c0480c1c0159030390185030306400341d44205610401c1803509240911451680201d41d50040d14440c12154a294115071032404013000705840001511710f0803c402c0c408032100d0380081164550724101004003945d92008103180134484941001c054225000c02d021501e005a1405605070f1708503014880c13a42c1c211041e000001d18800b00902c6484000a0240342481c00015903000b050010700400642506080038014000102d6040f2a94014210040900d0780120704050650b03400c1401075041c81c07038207401569081c40c440090b4003405120741c480404144108030440c041c00074 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 49480435 1250 49479185 49479223
    0x503070306030c030c170a02210c0402030a0506100306030804060e010302070f03080106110606030d0e030a0c0603051009020a0206012105010509010b1c05060a020a1e0903030206060402041206050711 87
    0xe4001752040701e0756060080652600310b0103000700581d66509010614a89c031074002c107070210302018030918094214484e02c0e0018004410044007a10a0f0700980c450002030350007140310302c0310303100450481d42c2502000b80001428401031160750310a8041075400c000c1814014540309190711840000004c4440c114000f9074008014011140d00441800c042d91745072005092508200002030349403800307000102d04200342c89090284554080056604141e004200302c1c0b0341c11707101d81000300600022603d590a006e64410b00250b20020361003110302e00d01e05640600020317402c03c4258404464003000181d00c0d80c25291021003c544203104640c0101e008800004d9000309444c2840748640d00c409622441419035481000072400114001c3d03807003003d0f070000680d680030300541500c4401c2a0321540d01c5000c0c0f801008009031760050080029a030003902154526510041000140e2050380501c4869103e407989440003d40d09030410742e00244141803100030004241145460048282d504842c0000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 49481685 1250 49480435 49480439
    0x5070b102d06030e0a0b09030f0705010b010e0607240e030a02010b090c090108040b04050118030e011101020c03091c0203011e0f0902180406090c0807030501050a060f05010503070306030c030c 84
    0x54410301e42402003510b070500740708011207481e40b01e84408042e58060280d200440c00582061024411122a0301c101c842547d00c4d0302240c01c00380c0c001d0115042060115508414101c03182c80d240080d2050580d21414544040180810100c09444924481040d4540300d14880303802400c140054030302400c3d26400083d00d44000070400038603510207009241000010416903195907805101c00754407035000322034491503894610703003a80140941070b8400004081c06040108040d0300c0082a0400fa000344c0e10340c0f1048030310104803400c0b841440d50b2041c45901c108408411414807041c0030005003417205054000840f10740100e420b50303407204c42070762000e40220a0302179000c1c40c0d44180d0722581c180290030803104103d0784c08100d07602030620140803d14200800101081001e80102c0c41443c3e1200e0140c0b000d513903841016503030302e01360701046895508010004080441c41d104440c11596400001c018261034480159400c0e031028001108040d20b40d0004800300b100740321b0303a0b0700031849001d140300218 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 49482935 1250 49481685 49481759
    0x2041112010506160803070512010b0a030b0a0807060c0311030a18171504020d05010c02010507030c08060307030201050f0f180a060512010b0d091406060102150705070b10 75
    0x354140c204070310a0006014071440300007160384c0c0900c0180d001d040c15940c0e4803842010780311030044144100c6c000c0703c6207002054a02640001d0b0401c01c680d52070a00560b80781c4020010980c0071405010030560207030004015851284c0d5416020602074203201d0030a007030310005681103600c0144420040381c65504030411070002809a10018000105110010421000111344403190f602080303400346614404502903549000705482c01d1580701d0001c00140c1040c80b0042c2c040e00f400c1318803c1c08240b801c405403840500902c847c0b8032940005001d002c1d030321700b55401501c01e074001603164000d5140a014004010741b4040080402495a50210035003124200820200e04c460f9004441040400c0c040c2800051403a00306034151020f007802640c5600aa80175000107010340400501101d0000d0820f40b094000031400500401c4280e090b55150701c80781445908070001583e0b60720000b5800c010240100d482c6201c0a600010600b003188403090b503443e00070b4401c204c2c01039054410604441180e0100e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 49484185 1250 49482935 49482967
    0x17030606090405010e06090c040b04060f03020f0c01290906040c020316050c0a09020901020c01030c030b030a030908070b03061f0912080d060602010507020a080702130e0714060322050a020411 84
    0x180321048c6040c6003504200080100e4000d42c803030001440280c6100702165400794040d80c1040d02100309058540c160307080c60f14040c000c2e0752841185c6c2c07940c000003000c61440c0c0649104444002901441954841c60f0034000101045403070324045020a1251a443c0c20083d840d17400007a00a50042c04900d00c040c0800c44102d0080c0d104200350f40c4104611a00ca98010900c0c2c1d603003044c2400d000511014480e800c2e00030f0700325504010791501814440c0c600b05600114020151806041201e40c10b58403940015264071041d9115a4001c010180064400b19024150042000640345c1040ca540d0380e114070040786082c02104883c907480200b02c40c404804144a15402800144002d101c0c0b4109410040e40b108800c40018062880014810096403195007918110200c9640100b0610000d03400c0c0584858050240301c06c40518006c0c3c1030810300d41442035034002d40400d1080142c484907404400071a40c0d0700d44c021603030b40c010507100380b0142c0d40350711a4840300c07804615034580d0b440d8013440305118 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 49485435 1250 49484185 49484191
    0x306050a0203060d02010c0203010f020a051c06080a0f050309030d03020720130f0209060406030e070f030201050d0b030a1a0115022a0105070507140f060717030606090405010e0609 79
    0x103144144200031256079050041d283c0a5020b09101545680034000310703000d40b0b0240f0f1140c640600005650001c5540f020007800240c0841c10b1400702420841225000d4030440d10424425500801e880070214907981d6039200c500c3c1c4160f08603403400c80808046800c120f2403c0c260008a030780030840406110300b5100051400a03401c1c8582e001643c55070000303010605c2d6a116407042590380c05003803000c01c0c2a9048403140d00d001080f403a2142c1e991600107003e0700d42140002c5c0345009081e40000c81142015034041541d9050b1200c6017401004040c903002020303801846039041c4204980c03c1c0100d03508025003407003500b030358000d43c0300c0390704040804248600c440511421075000580c0c111001000390700b000e401104199a420180080000484843c040c3c0700000d42240650300340016000c028a2002403840c206640c4a0b910200840402c029401911009025411718000e13034060307140106c008607844000108194205030240002c24100c90303098101580a00400003841110b00c0c0c0f00aa540e4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 49486685 1250 49485435 49485451
    0x8030301090633020c0306011203030e0d1e0302040302090a06030b070212030a0c02070b03090303040b100501020d110304270e0a02100e01020a08071a1f03030e0d0506040c030605 78
    0x100030050403c0103000d90810040302070754542c401d41490f06248203005c1583c103a08010101d400d156150805100b4002c40b4002c110040f07071408150001c58400819074050801c0e03a40c940050b4184a210014603002582d21b243c0c0c1090b034200004401a610046814020b018145000444600b0b601e850a00c025003d0041c40542d8000c9491400441100040300d0340b050f0640008100700903032100a07841c0c401d141d000404a02000310030080c8175000000031b588280e0146d51401d9880e251040c68080000c0749000c2d0500681208103d10702060154103c0d0798240e08050483e850195164020340210245e452080900c251401d524116002580100080c80103100c01070404429180d000030690b200d2204440c050055820700892568000e200b5585041c0c0c0161400d6038a02c1f0510307042544090400348071550040b444040303081c1c1d040c22480c10b1007880ca90034099040c181581c406580c1c10360055880d82d804031082e40d001001984c00d2000c50300446c410f4400d2081582940b400d442034840040c9100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 49487935 1250 49486685 49486709
    0x606060f0e01020705150f090406060c03030c1704061d010c03090c0e071707090e07110105130201090b09031603060507020d110a030c030e0307030b0612030304050303010b030c070b01080303010906 86
    0x1200d5039403078061586c040a06090340c150b5403034605041b0410f41c002d80103090790051415400141c0c1c0c54019a079010381034442d941c00c100010380e101041d5541001803980b500c1441e070f21000140002d01541c00301c500ca00504850032030b502114562282552a070103903101c0041d4840001104010300b501d1044080d113010007072001c4074a0b20ba440244048400c2c100c09130907a02e05400b0800782802002d881c0040c101c0030728000090310b01070f20082c10342c1d40c0d0700312040c48541c40d0000150021015081a645c900d0b816551103204514189103040325420043d802a0702d030060a03030241a44103d10302c690015442103c002c10705140c141800703410040103005200a000c1c00001000720b00c10082260048507516003040e07065100c5504003103e20588600038103415100d0041c01005001c0e68030a814401c12040b208a0519210100b1131502e902095800a0503940240010311010804a01840d40b14000b049103e0402e40903484030000700c0c80c00e038811045d94000000600285140c0e0141e14094542c4103600 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 49489185 1250 49487935 49487939
    0x20010605030303040305070f0c060c02090106020604110603090f06180106050a0b1c180b060909191707020a03080309010f02041203030f0605060d05090f010606090b030c070606060f0e010207 83
    0x1081c2c90b403100400080420600180c0c40c0100600c2e1001035400503007000f4030140c42a1214000741209000160681c883c44444000040321440011500c4c4a26400b03038400d800074414400340050364001078525406405070300400c5294440400c4a40d100e20083c40c00c0102800b0706c2c0132003d084914175041b5038000d181000e410700020359100c040754864140e166514008260782c1038100020f002074981643c00350b61070051601440648500a03000b0042181d59032000d4403004e80566440c200304407820440c0306a0460302010a1240c102d00c02c0901d102101e0500d0442551f0001d45540703017603002155034290100900c005403209100d41c2030902d0f0855021460603003440e4144845129100300101050340310310104040d910190095002040c0c00f41030b85486d0701225450501800d0300300c41c80c600c0c1d41306e0260b50144a0405000320021515651640f4001c0c0d824406c40b0807480d0710080600c1c0c8000020400c40c1e00050607441004020f0600c2da4400b07001d040303841c1c4010541444100d40d1411548a1641 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 49490435 1250 49489185 49489189
    0xa0209010b0a14030103050c01020d050a140705070b07150507050406121805011a150708040302060c1203010e041a1005011b020301090602071a040506040b1504050720010605 76
    0x4080d0645000030003941c1c8611500c80d04071004024402c4101030841c01000020400400040c0c010b0505003d800b5039005c0b1520700700c101c0c1d03e03000310f0b100140000e10700d0000c880c180345088010a80c50380100c0c06d0f074004640b80c40e800140d61b03008100482d158404046512560314562190760742000305890f00c0b40c64146401402004c148040c1314a407030440d44d0b02150034200c082078180520540e4454024480c40d02440004014590b04511890041001074517108040503001c1c1111400d5a201c18980e00f028110340078402107800441d807400c054452919954060312451002d580204181c8510444da49420319003028282c603400310040311141135506000d03000c900481c0d00d400341d0314286448100e41801c1c4100d1140740410320b00294055107802d03081c000f07010030f540080c014280101c51301000c4541c0e00c0f002400010b42181c0160a5801c403070041400650002001030300007400280c03500f0398001c0311000800310356007038403070001043c01031241383c0500380c1d80c8800894007104040200100303464140 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 49491685 1250 49490435 49490449
    0x91807050a0e0d0b0708090c09040c12020d0b010e06100c02010801031106070c0f06090501020a05060a18051605040f0204030b040803090f060903040602070b0a02030a1101200304140a02 81
    0x24280c0c090104540744039010f500e0301c0700741c14040e541200c520340c024100308402400541c0300703030303181c07075042c0581c140050f00c504100207800d010b6580b00c48050342c03941c07034109040422101e1398001c9034011244101c41700402c0344182660f018010041c0c0340c00795803d1080412507591866000035081c000e80c00c0f80b0381c002d40e810605190440f0342002c42626a0002000054400c8c411084000c160440c1d030b4801080d80700c042c1c03031488142d940d40e4484c80421a122401a07a0304c1c02844402030299100c0b41c002410f5140c0303a00010b4000140c0f51003140e150780150381e014107201445081c84048031019000f000703245858006d000720441c009008600e00380c259140c03411103000040014002500c0000483c524000400039100d4404486050700c260f8104a140c2c4d94583d0300a120b0800184940300001c24031302003610803611001d0807500154904003a0341015100c202003d460400b05542e50f150400300c581c00b034509110780c1c880c0809119600d282902c0c1003002840c1099071144c1c3e66201d818030a0050315611 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 49492935 1250 49491685 49491697
    0x409020d0b180d0c050607020f0604120302040302061b0d080c0a0e06070609140601050103051608060411030a0f1104080a0f080c010c080a0e151501030207050a0809180705 75
    0xa03030000540c0c8100a1201c2400d00900b00001403181e500304100c070303e52000203040000e100b4819295103484010040b82d694403050032581e095084100400c0c00658820b8020794580c2403800c025007003580da900002c4c11508101e85406181040b0326002c010150207000130002c40b0660b0601429070b080c00800300a03035024200c440310500c42c0311407010b41c0170303582c000030f03220181d80c440b00c00c1c804103d151a2240e0310742099401c1c0800c0f84104000070076150302034010300d071280142c5d00000009102c403050031100d1980160115802070768070200d10120101700c000542c400c22804201084a40d082d00c034500813070700613203c1607890b4032041c4000d104210001c14a550303040d4121007800013001e910308000203d03109052602102c1d41ca40401d007101250410340309446403901e080f080241a00d02000191201071201c0411b03648072180c00020401030f0502018440e2603010300d00181008400d54600b840d000c1818400d4a5025000c1502d5401d4070b094010358410750b07600c0c04001e0040c20705c0f07a00070740307136020700c1c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 49494185 1250 49492935 49492943
    0x6120e030906090d0204050a0c0f02010b010203030f04080d05010608090d02070f0b13090903080114040203070807300f06050604030b0601031d030d09030801060201060807120314070309050a050409020d 88
    0xb824040c10741ea8013040070f0255800802c10403103404c2045062001f8010010f00402052185c42c01102c1240180b00b25086030406802461031940c0704e202c01c0b5501980104110349040c003e1084000104580c445c1c94042c00047d160001c1c107040c5401c10b02d2270304500e0000c0008641c001181800310a09589402041b18000390b503e540700c8044001700450712985402080003245001250340905501002c694101d4916002c1030121180013014001648412914032001c5070740b0781c002c124514815030070481440550103510743c403a001860388203011f01c3d9480010b1009a2540c1892180304028401e1b10001c1000b01d500074036040c41c581e1135071300c004e0005000b10b040c1540d03503044000c080514046041d0144c400c3d0141c80d5548844400346c40180706090090b000904950000700340940144606415524548028192340d483c100307098034104c6241004074104070301010803240029802002d40341c21842600c1d41d00c000c6041c4010f201d00141c3c2c50b8080d520450074240500c01689442e00c1c00702c521a04 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 49495435 1250 49494185 49494187
    0x10f080c070f08162607080a050403050d0203030a06050603010305060f06061902071701020408060703020f0403020d120311040f031b030b09150907050d0f0311030d020405040b1005250b0f0106120e030906 89
    0x230600003965940039a0780b025109000d640d8507134103480c0d8044011031156545074dc0800095484105000150009002c000d00310360100c0d021800500c2c900d00c03c41ea1000e80100b405151420441c407100070758000c60600009a0700144c414000e001b640ca03113030001203058100840c142440c1c268903d543d494040c0030001410b60006480c00840c0322102241d001c1c40d00a0603c102c2d03209103103400325500c03a080c2c50b103000107031030000000103d1a007241180c00321004010408402401c5481340c100c194099418580d10000000c000000610141c2080c1e220b284113101414000144138646985071000426111150b00010380500159480d804004600c6070000c40d5884070203880d02d400c1d90b100d0a01e140c44003140c80085102084855150001d1017500d000f40c0f02031095503504001d00c5801da01c81603409010903424031407240c400130b0340c81098041141600f082504401a515103904031401503a40141e04119003006010550304004e65a02c107082c484410003181d91100102a264080d4840c81c5114440c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 49496685 1250 49495435 49495447
    0x31b0f0503150414150709060f03110306060a050930010e0d0f03020c07080c01020c0909060106052206030212070c020102070512070806090c030c010f080c070f0816260708 75
    0xc10801703540350f860991200915414118005040c00c0b102e8412400010744646003101614402e0065030800c0003c0400d060668030b999081101c290030901b41c0d0410010309201c000d4865540b026941840c031105008036000500c0d21228121503405100045007030b038100b00914001900c00034001e44101c13001c5c0351000d515803503480d04401034844c81d28440c0d9188220740e008140b440c40403588000b41c4400340c00315000940c004042c445241c4040303581c10426082003004101c06401000205494580410706007060200d10310040b0781e00740340d904002d0000f540803400d49528210800303042d420004500300210102e190b40e000070340da0b800c18003909020b40d03584281244006010056403015043c00c100b5036144e491321004c241d90b00e0341d4140c60148248161000a64154050500d07404031000b6543d540d107032a52070400d0742101c0c1e8001002100c2c4a201440c252010440e000c2c098120705041a04942c403820345410908002000c1240840d0b81411182c0c058900301001310803224038581c0f060030707a07403034013 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 49497935 1250 49496685 49496723
    0x19050f07050a0311190b0c09030c060703020105040312060305061902090301060803070c1505190e0d08030a0b010201020c1f060503030f120a02030c0708090307031b0f05031504 77
    0x4060303004018814812640712070105508604084c02c51040301d000c481c03c2c0400013140081c0800303510809403031810b03000041a030006028000380b1a4440250440d00b411401e17402183c401da00c11402600141d648000f40700405da840640700c0318604607000e0a200d80750a41d1189515100302a00c69544040c03180d03620068022aa015075041801c0280200912a03440740c0864590340940300031a904403e000001c14054030948204071107070300c00d540e400d04241119605c03540840e1307106040400d2001e80d1400324880d9030782401001d10030380306201d9183c0320700789440c0030400c0e10003940074641564018000280c044100203004000841044003510300d104100380b40e4130080c1415004250103010000b001260b0f0040c02000303203528003e03001d003284142d4403071340100120b000982d0303e1824a00100500408071341d0341c130301034000c81000606441c20180c0d00d503510610030070344080d1840c08848021040102c1c2c0061038030b010042005401520100c440c0140300c02461300010401081c2e501c508804030455 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 49499185 1250 49497935 49497937
    0x1206060304020f031e010b062113120507030e0411030c09060d050705070302150103020a090207060b0a0f060e04090209010506032a0304140d09060e0321030103050105070519050f 78
    0x5440042c042c5d076800a6a440c01e10314030380c4013000b130380f405600b8203401c442070741801c1048845509550361448e15940001000391300581c80500b0a0002d00380c0054408003040342c00c1c48110070408151602aa44c0c545458050004203c0e0040284503038502940d40d0b103814016011280c0c0f1024140159980701213000015a06014685a2688452418082002c002c0e0400c00070141503003c0c0d004c8031114542000d00f144500400d00000390002081102041010040d40140403264414000401c1c0211f00c5400310760000742c1d60344047d60600c64403208028040d0848020702480c0000d0f07605011100e82134000c1340000c0018416a8041c600c0003000940c6403280c112440f000440180b4040c941210b001c1c0e18205075001500c090340c1444203066080045071002804420801581d00c80402c0f4602d4184203580401c0c4001140c1d0701401000500320001d1401c084843e0300c074100740c80041e12541141041421120b0082407030341481030400107000220000c0c0710100a2043c00c1c94003a688035040f002203281 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 49500435 1250 49499185 49499209
    0x81b060c07051009090f050a060509090a0204050c0405040c02070302101701031509121205060109080a230a1b0e07020a06050402010c0b0f0402040515010c0201031d0604050304080c0303120606030402 87
    0x10350b9140c00000207046c00c0c213801540c003c0c540c51100384607041e25841007000c5204190350384001b5600400009006040c04e4210707a92013200d5146907810540d50310081410f0703601c20030b04440160490341c0b080c0114a0420741c1c0368928001403034620500c0c1c1d1144400e03403030b0b85018000a040c2c1c2d02c40c58030000f0007403050b402c400c9000e03901ca0281b08008203c2e88000e4614206030400b4110319090000080d029403181604074210340103040205100061a180da0501e203203c640c0c0740b0700302d0303801d01c41c19000130500704100c516061095071400030120030450000744540c85908407c00480f0114113000c1c2c001e50000d12007546c0c03500f2640005054031a48010382e401c001c80d6900500c60395503107042089078400d03d5031041c4a03078000d550520140d07540151a002141e8101c881c2c0c0d0100d05070390504405540b09901c140940300c500c80d1591014032494150602e801001c88007100c041d070000a09104181e010f00860310004800d9004500f40040480b202811400c02014980101000701c001810355a40040c2070f00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 49501685 1250 49500435 49500449
    0x705010204090c05031005090c220305070810051e0103032703030c030e0103270602090d05010603050708030306150d0b040c0e030106210605091006081b060c07051009 73
    0x2c40320f800c080c07020b0610b8004a84114540c410840005403074205840700c1ca00c41e81901d5030540c50003000c03032600070051015841d4070401d00051000400010400c1206501401603100184160100c80700c4010660381c5c000c10955508051041403071010200700f4040303040d02e81c58103021426202d008004403140d951142051034242c0454400814141c0100610b14003d009640b100700340391090006405880f0711444449400c40701100e0340b8050003908800c000560310420000d417800485500090f9101407428040c0d1b403d0355581c0c810010040c0420450700200a06809981107142032400a6034002103600006400e40c00040c4424410095a0002d40e001c1e100403c2000300c01c0c980c0744001c00107115010038500941c82c0000210f000061a642c45800000341104510504040c0d940e078000340c0342c040d043c018503125007018001840458003912000e0801140104984070840b0398003600346550710307203a0740079080130072401c1c3c0c02e2203001c6913035016143d0540b062182ca10041608840501155200407 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 49502935 1250 49501685 49501691
    0x60902032406090108030306092802041e0807181d0a0b010e0c0c07050d0c0509040602030f0703020a08070804050c0a0305011a040209011d18090c030f0c010e0105070501020409 77
    0x9211001d01003402114280c445050320f0b80c0321000165617102c00d0301c043c2d6214580030000b800c01b80050507482c200c0602c0c1e04015490a02183d2210282e81154210704103041c9120405070550104696900040100500400100c1c0c070302070018640960b4810802c04c507a88410a4100700303210030902480801101c1c0c1147c0403940541880740100354280035009440040700f021482c0d000102c400d44005410010160141a150204002c04000010070440e505e04800a0000381555031041440c031840c0200800340c0c0e2031814a0120b810040c009006400b414418813940c86500d50141c180d9078400e0242c00c00811544841c1081441c26886445103a80b2810b044004800c00c581034002452420842002d0641039101c0b800b0807040c0e000710002d86001500318072500500f18200350608906c51400f8103541c04606864402c07104a81040fa2003115035844910a10701070705080141ca1003c1b414800336084603100c00000a1072003030100600d50402402244c04418082c0070b504480013081c5402c020 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 49504185 1250 49502935 49502983
    0xe011b050903031201090b01030f0b0a180e0313080d020303070c020d050703060218031209030d051b010c0f080f06030d050901020319090314010e03030a05090f010f02041701090f06090203 82
    0x11003d441c0014000d40000e0502b1002554540341e40640c86e09c0140051409070a58101901980c800e00310b0400c0909564441d1000f190300002800201410004180040c000300c0c1000d00c42c1d0315141088003141c00315441002046201a44050024241a41140c100c0b0380c0d00d105091440c41d20040f50005030400d44005201400400c600d00c0c410100d440076800d441040081c03840c3c0c0c1d4801d000303490120780c040c0c10140ea10601e00f0701c01c40061002050105500d01e600c08500c4170340c4c0c2101c9121402c0c401103280d500380815210f402c80344442d404000e07441c1c00c806900c1c0c060b010907120a140150308040c404040781008140e8020b20560340d030b00140f611803010348001c0060040028901e440140c840a441c0c00d801e02d031140f010b000301c0224041c8a801145181c079040c40d0030008100c000c0601042d0701a4000902c1844428000c2a00c08035200302e0150300d031030a00c1790303203c1c40703201c00d01d0001100c0c2c0c5048198400100004400304e010742d04180b00003000b0b0030f5030000ca0f0400302c411003081500d260980d52 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 49505435 1250 49504185 49504199
    0x501210c03021c091e020d12031a060c0a0204020f12040c1a1201030b15030d08190e0c06030408040b040e0a0b0103050f0f040501111305040e011b050903031201 70
    0x180000d075444485824464403420903403011503a44d8040a4081c610791818030a513440000003103000f452001e07180e0b02d616101e070340301d0300c0043c0303290240080060384035101440316003091146c103021881e045619a1400c4920b0982690340c0000c100b0081c0101c2e00824018030b121001c02c25102d0071141041d451749640790901d80050030030103600a12174104d240b00f03d81c0001c50031000a603116540301c42e2101185900710388603406040d20007400178580e00740304c070205840c54030b00740443d6414a0050701d4040301420854240302c00c20044401d507090241c500300031a03500c5d0b400068402d00d84c030b805403685540c036159030501070401e00c501d402c00d0a044d070001030002145203000c3c0c41d0501c02d90b00c3c00020061080c11000460540e10152075006503c140c542c08140b001d228041c40b030340c02c00d2060b40009a100c040365084a503580210200103c0c00c034503503001308045d0500340141c4014900f41e000030070000310004158400065130382c02b50020820042500c50703664404104946030684a400f16802660395060 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 49506685 1250 49505435 49505437
    0x4050607030e030f030901050403110604090c0f09080c03102c071a130b03060d0212010902010806191203020f01050a0902010e04090804060c02060405040501030b040203071406040501210c0302 84
    0x8040c0f80280b04d0b0b10b510f080800c402206950a800f016035449142c1840c40e210508200401c0c00100d42c808403c00c03001406440f00d00c01c0968504151325409090070340104068204100d0f80c1c080382c5650425080682141c4c1c0100e02100c82c1000c003d40051600e0704c40d0141060030810300003101c000c14207481519403000002482c50100c0d40408500040d13103481401028680c010400d0300004030300d00340401e01c00c1b038080301e0140d80c2c0402c1c081c002412086403038001804943c000079130080360380d42d02c01c0c450065592000c1c01b141e0001040ea032001001401a99000a11149220b40e948c90714496074000105071081c00b440e040c2c0c01f556402403280b41001c0d007188000b400e813030f40d040340031420301020307412241068000c450362207402140080c00c1918203a0152440c0e2408007080780e009a0405c40821280d96034842c0324060b50040c2080102894079106051402c59240c200403000c00c0c0e00f0780249555a100d50031281640d8080c41d00300075018501c0d0140d1650b41e03d1100d178001d00c9050080b81100b46500d64 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 49507935 1250 49506685 49506707
    0x3150b041e0f14010c02040b090a1a03030310030201030902031e0304090b040c0206040201030b0d0501020c030c06070206040506040206070c03051c140c070e150612040302010506100503070309080405060703 90
    0x360040706180d4490552524071054401d50740b0f00c5040300440d14043d07000361030310a48180040e00218084d5802c400294103802c007180c00c420003503956820740300e036864410302a080c1000268003d510b10f00740400c0190005e08030b844001d04141e00c07100c10a007152403e002c203a80360000c61001d00e4103100f4845550b80c1705d4105015140c0851315066403e146807901e030048404200b00340d0007800d040e46450700110040e012549405401c040d14480308000a4401d2000341101c0c81100061601c4080c0d019a4505101e40030f000da0007190b206100f0b010100c0c0004c40c201c3d40243c1d04541c1540e881c1305900c4c0859601555900240c041e010750041c41400c100040300c511118000c5030743d500540f045010a54403180211030390043c03030340e0040106000301d020a111064205082c414200a203048003800241c0540c004490b04000c8a07010007440201602402a103400410444c0e5055042c4079a1100808078000140440101500d0f00c0500c0e0038052034000b104c0107800040c0c00c07181d440c401810301501c002540 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 49509185 1250 49507935 49507979
    0x110612100302040b010507030807231b06070305040b13060b0603070c3003050a0207020622150503070509010306170a0507090e0319050c07090608010c031b03150b04 72
    0x2c125134a42c4204220789030581d25031030f094002e032203101c000c40308092210004c0544440400706c00760520000f40c050030130004078220382a05114442e0195060520207409403086c54205018400001c4200003800e90051441e60841c1c00760400d820300002901c072802c46203801c51030000500890b580e00c0b8494003d45805282044c0e1107144801131a010074080c0060041400241c0001d100c07128403a0304030f81c0d00040360307a0015042c90000e800007000c90740640303940d007050b60003100d558001980703060b07401009049802c1003404142c00114040e105120051811040110000f101c1c011a8002c0d0b01260240048950503484420f6195050390b03643c0d02d00005980d60f1244100c0000c1c00425030080341d800c50000005036041c0070310180809805003c500728103050140078081000f90f40401c00c4404014074200c0c0000c41c0300d03403511060b41d08444400c4116030405081c84500107050a0005010902580d02d150000743c42030740b48800020018550011a0840d0000900040c560340801900780c0003541 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 49510435 1250 49509185 49509191
    0x201030b030c030c0d020d02030d0905130209061207030e1203061507050c010c050a1e02010e0904020108041b170307020108010609030b010302041d01051e0a0606050711061210030204 80
    0x10300040659a0904214256040d48402c0083c2d010b400c0c590031142e032891001d800d569034103203036900003030401500a40c25400981444d904121070720b00341158001940d08503004501c4c0c41aa030010071b005216492030303c41c0d950145004030341014441d6101d270400c203d01c1400c0d04d04004426a034019150320694425106403888120300c0395203d000c104640686510000501c0000d000f00300541c0c0c94030000c80d055405014030700f01a40898441640381e0101b48582c5c03808481d8502903c000760244410710121405205900b08110040c0d801007501900141c02c008400c0b81080071503880320b102e03103660b005407044003070360450070300b01410000280508a1003601d441010345e80310b210480e0124641d20020b0a540903141c010005410315038000010907212080903075036001c60019039130079121b068414199200c2d101c618030074000f00c604d01413134000305814000c2c030900d8a001c82c010218010a800601031480081c01d003a559925441129040d00e0444400080c6103070003819032204086070b100607400350341 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 49511685 1250 49510435 49510451
    0x1b0d080601180807050913020306070905030709110307030504080f040b1c0e0304090906020403170c01050907060c030e030a0f080d0b0306060612070c0203100c02010e0705010507030f020102040b1303020103 90
    0x4540d01c075100c03c0e070f4044001400c40310324240c100503000c5c10140c80c0340d85e00d11308070900c00e01584052110900c80d4009807a4261210f00d40000c0c036150180c3da6011066083c60104078020550700c036400c8907001001840d01194544039410445181d124000c88202000c9001600060b440203484c051314240c40003079400900d000a9512450a4a03040c00c000c01c603503002044280102d4074035074002d03a801405000e00500b03061b02c07541c0c0c50b03404a4000c10035803215000851030001c2d10f9424020f140d40600c2c5403029018040c540702000d0400c0100800040034822001c2600701c1c6900c007001200e900640003a81045540d000c1d04040d099948241c11501c51142001ea282e0780c1d5040000342d660080c5002b5100900d0220452503212489001034030341420454280b800001603982000b5003070a03485d282c0d0b000145c005a0310b902034210786403d40881016000f41100300000ea0b000400d0725042c603003505000f040140014001c074024803850304080f0803090046006460030303d078940700c01d003034038400c0c2c80030002c1c10 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 49512935 1250 49511685 49511717
    0x6020106081002120403050d09020a09062c1902190309050d090812030402120f010b030d0c020f0108100b070302010606030507030203040209010b0d0b031c0f08010305060c1b0d080601 80
    0x21250701c804c01204509080130a00192150b030003807044203038a42000801174020303070011f120301c240d030380c44600303450f407103020511a0703030502401ca0001c503505c40240b180b034a0b96018103c0059600030310401450001da4240c0d07a4100d11901100c040440500f140100081004000741c001d02c400502a289482160349002a60b805075007a0800d40e25490014016180c030001d004444c2d500c001c00898201e4440300d100d41c04400f081040d402d041829400201d4010b4580e4141480d00049074031003400c20a00418503000350300c17100b00580c0076072002c0c40e041d2503075034480a18400d58005940171071201100021940c00385a03040d4005000d462955a0a1241d91035500044046c2e020541d0080e40c13010101004010001c104d100401001e949a030000c9107980c3c0d81c50000c2d0410031400c400d02298444000400c0065510100082200c91641841401035040da01c1c0c0d1f6545020040c0b0b001d00080c1c0c0041c50010f0a91017290b076548000403036085403410f15000d04020080306007500c005021a065524041c014 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 49514185 1250 49512935 49512937
    0x71707060503190c0c1e1e0201081602010209030703030503040506010905150f0a0b0d05040b010503070e0c0904090b0403021501090203070c02090a0b0406030f03262e06020106081002 80
    0x201c044081002e110300303443c85100024081c4210450138000300c04284030002d500303450005024020202c03e041410241d0400b10f286c080300c072003000ba0b409000300c079140c0181c5c0c20040c02c940181e41c2d610070218010280301d0590082c0b090052642c0d2522801c5400000c041e8458020343c880c91080c819541d190f42c0e02c0251005960054508030b9078040c0c6440c03000940e08203d43c9440000700c0040c0422080c1e40d0351101200d0769400b40c003504018988810401c41408850501c043c01464103800038030325140b400c60000c00c1340b60007400410500d900016609000d9030303903400081d80380760050200047c6061624020796103400c8006007a0b80c0c500d1000c00011002d03450701c01e40c0e00c03d051648858035030984507400c21580d60700007041001c130a5a54100398200b40c8a51241601942c8a10b42000d61450b0b1070801805091103001039503240c01c0030f0f211012510908141003a0030284d403542d80e4910b107000c5075801e143c2d0001c41c921a03142811040c000144980c2c1504200200c403c1d0b1000d070351451325030842176800c1e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 49515435 1250 49514185 49514191
    0x70f030315031a1314030d06050306060f0d0501110406120b0103091119210b09010203040f11030a0501050f0109061202100f1407080301060806010806030715050705071707060503 78
    0x15103070800c40c0001840b0f1020346820b502510901c400c0d0480001540d0b0101100315104c0e60030599480031a4510114019225a17030240500b10000e042600e40400002c901c410b000301c0f1507000d04030648884082080c25049524201080c80859441d02d0b22074000a00f1440c200c10080c10807410b000d080c0006d075000744203455419401a40c0001c1c60640281800012251640c207098880320242c0d001818442011901120350164410600800b086061100c0000c3c0c003d0700034405a48100103110010341c003e00e03129081680a84c07115144900b640001b800c10040c800050030b65401c4c04100503401f01121030185c103030ba800540401c03013030340c40d01a100ca495181110081d0009407041c408440f0500460030040210710f03c1c58060075940c0c608d44003003095001042c040751a80f40c0400103100080d0455109a40010f003842c000440c0c2c50035400103075035070320184a40851a028480d040a07202d1184007203d0505400008584140e956000000d04250194420900324001c008011420a205804580c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 49516685 1250 49515435 49515443
    0x2030604270303050705070c1511031822180c15120e0f0f06010311010f0c03030902060f0c03030108060105090f010905100e0412020d030c020d05070f0602070f03031503 74
    0x8540c2800d03030b405400800d0003500706414801d0034403098000032003000030036001e021a04403400c1142041200a84503816452920010350402d11100c00100342d0b00700b12050a100c111103079008050075602c01c071552009011f80c50a45400d10300d254980088050306503402510a010700b85007981c2c0c400310714106140142c8903000017280e90000d04006d421a4125a284d0900781d8292000f1144450125182ca02ea502d228007494000b02c5c010804d05c245480c00010110702803c0003001c1c08d0288030000c01101038440700400b81940c0d040b1904c1552104d1003034411580800c4c1529035103c1e0090520741d503e41091040c5840742c802d45001050a0403c0c444050083c400e100d808030007039082c0710b9040c002d8500141400302c254041c400000301c1c0d08070650140d005601924500b0703203142d100f460080c10145018002e006160405840b60921076001820241030085480c00319150b003000c1c40d00390300002d85058080c25480c00490558240480140c000555a119032010000080041d401007141c4c40540b002074 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 49517935 1250 49516685 49516751
    0xd0306140103020c0f010e0a03030b03010b01121a03030d09050c1008010308031302031204050315010303091a0c0109030201050f0f0105030604020603071106090c131b050c03070c080102030604 84
    0xc0294082c1c0c01070709200501c501034588500780005a6403c60300504040d032860361154010006040e0580b060290082003600240110000c003800648014111503000350583d94424000086044000004050100040c103a9a680364101c0f52100035100c3c0702010f031864000c90401d400c082c581181501011409511807075210780c42c5445165554000915070f80f003002c0500a02d5005940500401d038401c1181d40b41640c030b45042a051510700300d641e91208216080040052020940000d20142141d28a1078281003544001141c90006d019480c02d090013982010344202c205034041d04021b00c510360f02c03004114940d9420b00e050700f002400b8425650550040008600581040002558000ca940c281000c6541c402c0d0200d924205084480070f420750045a4690200d180805040d1000e039030050301401b07240308494507810b003c030110414400b440300c0007450344510310301071040c1c40403a60410351410405956100050103580100c0e242c40c49140340c0b4140d102d6036200814000c06543c882d00c0742c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 49519185 1250 49517935 49517969
    0xe01060e1f08070e1008150c0a030902090a0624091a0405180103050708030f0306041d0604050601060930020f040c030e010c05031608070903060509010b030d0306 71
    0x192855001c11030065142809151001c6074800c41080703000010880d84022207858503140d4690180d400181d08a1012034010300c200400341e8084441982d08889004409075441c44e40030000d4004150541c00250440358110810403851115030202040f51043e0b802500900c1302181169583d00400d880d103004110081018030111012440950a01142d101010310309510340300000c131038040b07c1020841c840380c800010320400c1010301a441c02000004011400c02850b40515401804001c1c0000d006981c1c80c140d010801d504521080070505118054030110f050070700300b0540380c99007405480302280c1c150200250043c01300b2990001c940d201e20100480f40401510404030101818007030b03901406812000c0d8045d03545118601c881c00705502c0000324200310f8581c103800d403900b01c0d09100c2071080900400c460002100c500c181c4040061511441545d15514284d8a0b00d01a07000074005503d05010804440e03015402030700081d4088080742c1c10351245075421416507106004081c403102c020030345 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 49520435 1250 49519185 49519201
    0x604090b070f05040f090f06090216020f030a0b0403121104050d030503131509051e0303060111030c010f05071101110a0309060906020a0509090109090201090605160b0405060106030e01060e 83
    0xc2c0c000028141c50301910f0700390741d4242c0c044809207607000180c1980d42c5030410440115103100c1c00c0300a0034005015424000c044141705504200f0403806400f44001c10b101440d0341d5400d014442c085984900002454101070a0003000140c03211003001300c640c50300354030745a054441400d460481e80010080380c40d40c1c1c5280d504840d25040900b0007a1540c070b12029460000d18200c00c00007a9494204000a001c50a4101640340ca03403900e00c81d804100100c801e1a01080b80442120350040c401c0c02c10048400901190a10b94030806d5443d06a552800304030481030705040d000715004605542c0c498001e41d116200c0b0070b080300c1d50f007a50500e00341d07801c010201e200350094100c81d134820700030000007800015070f403206002d07079110130030078800100001111410b5141c82080c2c2400751214050030400080340d54000781a88607240070303900034880081050804c800c0a010141400c9600c00c41d02800340c1041d160103a5224402e004c3c840100703040c04105602c1000c144966002c40e400d04040000903110922 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 49521685 1250 49520435 49520447
    0xe100e01030209040f050114040303022511060f04030602030a020409050a0506100807050f0315040c110712060605180103050c011b02090406020c030c030405041b020a060506030102161a0604090b07 86
    0x1700c1180e265480700725602c045038816440c14410303400b9841c096030b5242c1c030141d034980d90a41105440100c01d0314004100203c1c45403c000b401c9200141c46c0c0e255950381c450a0f0340e4150091b54801025680004101301150700315402030700480305003050a03c42a180c01c1240b105540044405981000c40e100142c3d1130544568620f81e084002d40c1451498040742c030807050802e5104070740040c44550000d200031040e04051184803064002450107091028000070007a403a95118415107c1842000c10002c00348000d603800315000709401010f8a94403001600c000000da1700034401910180100b08085c6070039400b0f09510b120410456000049180d071641c00c0001c0d00c60040d000303941d696800d00000039601c6041004100c04ac0c41d60004585443c40e110403c01510040f40760640307820300b414011030502d03800107188842c00d0380c40034020480751b072600c0c042802401814956400f0012035040041400b0088110070090f00d08040d8142850f82c50105100688104903030007009200e000000885c2a4410b007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 49522935 1250 49521685 49521713
    0xf0902130c030f1401080d020609030403030503071803050c0a090e0703020d15050f01030c050312030f0714030705070605131205070f0b15091f050d0501060e010e100e0103020904 78
    0x3040016400301001c4048040b59407440000d18203031403180046c00b581100704500d20348032030b840c07004240618007407031101d44034001d03484014107110020000c1403a040c02028001c19010101000010702e5a890501556411100030341501810000f040420b040dc3e0f20b0041039584000c01000b06580c034036550900a04a00340003003502d00340d40300d03a821081c250090140900881e800c07031442d2240d5041d41070800c88486c16600c90b070310035400b41d00074008004c0c030603055a9016942981154090362640350a031401c60b65107006810340b19000007000389480e0441d025190f0745010b090100226030318641c1e0700c4445150400045c0010a01d119140052441f0b50000c044040c8039042c1340e01303401496031f50320031078150594050302c0280407100d03003103ca400c090701400d5010200d00640680d0041c400a0760500400d00d006080c0120300740400300b070a00030250801c0000f0b1107140e030003500546c0d43c0d16100290500c00e1320030403004007101000141d54410314444504bc0e80c0c00900c43e0416880e250384100c1000c104c4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 49524185 1250 49522935 49522937
    0xd0c0c170a020c1801030b0a0209130b06070f0b07030606020a0803060f0607050105010f180b011403060d17030108120a0e061b030703020f0d020106060c080d0b030a030207090f0902130c 81
    0x14401d00495850b0580201c51304030690001e000554118900905003d0004009010191050104030242c0e0f50f100c0080c0c0c2002c1c02900300086941300d00d4042011840307008800351480c2058001c00c1b003001002032042d48030b40c0590f07500f002903d4a50108030f80760308201001030f2020034140082030b15890800e50000b0940801440c0301c0c03402302e8a990340c0b07080d00e20980c0f10550281e0a14010440d1a940800980c408407000f441003100c0460400042c00314548a40400c0c6421800310001300300343c881592650250f0382201e400500c0e00c58134cc04e40c00c06540300340103507100703802490070031180032044409480012201d0384484404005c540d007884040c0e0400d80c6403110f03185014441400146d01400101080e42c043e60252135017400d200d0140b490b01d003030064401e0231a032408000b00b00c00c940c011004202c03198499551035546080e00a604041c1c40d030058a25854050011440200b6400240e00d404030351001505010320340040700c1d403004032607002c07001075007154070000c028800c11403075400810800c5075 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 49525435 1250 49524185 49524193
    0xa020c0313090f0b0604030203061b091e0a0f0b03011502011103040302010c09050901050a06050c0c090708040606061407020103020a090e01140f0a03170a03110706020d0c0c170a02 79
    0x24201c1c15074480d6190780c0040401a41d0300c103e00082d09890041c4000c0390030607036a05140900d5940400c2e0359940c01402032041c0d50780721080c450010f01c0201200c040390b000805028280400c4503d0501e40100121650b118103851074002400e00d00c1b030700c6000129851002898150703881e145901c00305460320989a07085560700d10070b101e043e60220f4040c40c00b0300d010380d00020b2421410304e40076240c5000d41c0c200b81d11600c0400010400f6a80d45040c410a542c45440c04644030340b420001c0500e0304210700b0113517600c8501e660402c1021540001c01a1046001309020301c002d560ba490306803449404903c0c1d803806000e081080c00e0155000c1d400a2031001528607081e5800c555038544141031010030f8020128003400c01442c0c8215242403460012075141c11100a40304500d582e80344101d04140d40d00c0d052006c100400c4503000180a58480c5800408080c51940e50b041703c0d143c088001d5000d07401000c8050704d0500c266a01910588206001541c000c0c00600308611200182c3c6a0b9000349502104503c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 49526685 1250 49525435 49525447
    0x915100b030a06090b040902150702040e010c2109051b130f0f0e03040503070302040504080c01050f16022d01020d0e0d02122104020117151f080a020c03 67
    0x900c1005511a1420480c009480f500700200e2106403840e000c441842a41007030400000f584d615911028100300249215640b102075202140281c104000d1104040d440d0180c2c004016410901d0100244002c0c0c4610044203000100c0c20121401d100c001340143e07004030183c4d6100707412a648070f41100c400a100c515040e000494940940e9215a40302d0042502d80340f0304030111185001b8600c1e103c0040e00034606040c20880425a00c2c540c0d1700c0040d22454452011a0520050300b0403038034482c0e07800c0700a00c040c2c90490ba1920b1452000d07039130070403486684100204080d1000c01e8185400080c48003801200d81800601618440c100319440c10a5500304484049001c0510508004204003400b0b005840c41c680c8020b030070280707286054071b00c0c02c00070000c00742850000030402001c2008490f000603580c0343c0f0300040b00d4100301d400d464841030318014140f1114900b2990300e8242e070a400c441a8074161030318218902503594030380410000c1050745002c5064082d03240c015180c1c0081c0581200d003800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 49527935 1250 49526685 49526699
    0x305040201110303040f120507031704080c060c130f05010804021003230105030106090203090a12090f0b07140304080a020418080403030f0206010f03020a1e03061b02070905091510 79
    0x54401ea07000c85210720500515010030142c003c007c600315455040240c2001a1a140901800182104003a0780d0200c2c00c000b8080000d20819070b1402000c40302101d5403441c0c115007508440c2d10500016880c2e49402400013042015070104400b901c0c0103039100105601e0350b500b8003081e203a02282030018503490713604d10300072840c13181040740c90641c3d03042c0b95808a5251409140c2124500e0300410300490040040201086001903481c0d60b03140e02c42646486130b814160b04403040c0d060f50f0480e106010f8001400201c0465140280004131b004064540e100e06800d0320f51030f44c80c880e070711401c11035030030510011015203090750109820541c1901403003400c0407180d840940390f600c1030300102c2c08100e10701e040d08111030381046070f1030240000080140c400c0c0e04540000e15030540c41d1090064420680c4050903210303011003038400080d51b2004041c0106210f1442c141008c50340d41046030018415082c001450951a024203401400b65201501e041d48000031031500005000700f00001e207965980c0001507103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 49529185 1250 49527935 49527937
    0x100c0b1009050f0103020d0219030503030c03070201240501030917030a020a081b0d020f090406061d0108011a160812040209070807120209010e03070312020d0503090d03050402011103 80
    0x60a40030111035101800c01c0003820850340040c0c001e00c800c51912005000588482d00d00e000c1064044403000c107815041c088d0201200d00c1500000c245000200c1844101e100f00c1c0051800307080c081d0000d100c0d8071140010703510280301d5000610b65960a00404109d0b550080d440120300038020040e241c504500c80c10441500e5100b550416080b0394000340358801d8a5101c1595070304001d40401e400413070607404a4202d0103000e448002c40300c2c2c1da400a0740030342d000c00742c07811a000104058010301282d0b5403003402030308510000f60b8100700d081520058400030362003000c1c0d4034140c075042d00314003081405441c030040f00e54101803034200300480036440d9400030807003c03400b130024400c800b51030811341c0c94544140108407030085d02504c1404207000c103001041d0317084000c118000199010040e00c400c001303001214880b032481d0545030580500341002c0148003501c2d50a100303448a580840d00c1c14a0300d56000c89080c40100c4900e449500080560a0207500c03030703040590403600500d170510400c28900000350031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 49530435 1250 49529185 49529191
    0x16020115030f0c053c0d030207050a0f050d15200c011107050309010f020c0a060201020c0106050a0f120f02060301090903020f0303101739041a100c0b 66
    0x649000800394041000703020307082c00501401d170f4818001000203a1503022440780541c83d103085143ca6610b5245d0700e150322690201c0035100811030945c0d014507040217511034081d4020b0502610000f0408940b081b560750b806c1c022208050f143c554081d19036100c2c020b04083c0c1811404d06151070394141009105103413012410a046003403440c0c0c0d00ea0200c1c1005007100e003440b0082c1c49a910034008400401c6001c010350340319080c2800c081268915240c1c040341010105a4010f912080c041d0700850b135030380d0560242c59080c03c220002c00040b80c4034810003406513142e100b02100300113541c400b4841e000d0011402207966100b88800084082190300082c22a0000d80181010b81d81e504a884245681003007018460340c0502d006c0c40c41c50070403e00c001070b04c00e100d014150b8100c40388082d207070f1079a2003000741c0f001000c90b0209200c051591000c4080501c15900800400c1403070040c0104c00510386881408086002d0024802c0c0d407800c1c0310280880c5030181c04403d41800344120f018404502100b13403081c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 49531685 1250 49530435 49530443
    0x608180105010f060e030106051c0204060e070c0b01050a0806070f030f090f050c0f0114090a031202010b010206010816030b06010c1203020c010f0b030601090203190204080601030209060d0b1602011503 88
    0x43c0c0508244004010310b003c201070510aa050260800658030740080030884c0e01e8208401d5548201a4008100940981d030300c0b0051f507041ea10108031283d5413155181ca9680d108624401d002d980c1c038001c00442480070300030480c0d0b981040b00820742c00c84c02140c120900307007040d09010071942c0c1a80c00070030444400000c141c032405020325042040103800c0c4400b2240840889100c00c0f00101e460008003005100e0041c40130f002c40000e62003106035140c00c0f030345005561084a00c5802c1c042204001d01800440200e6030151080e84c002042c43d60000c9101c0b50030b440c12450700c014107455901c4050b400c5d4030103402181448001c019017008908a039101c180c800c0b0841c0c0b8096039039007004000b1030031100d03a000d00b05543d40c54505440d40302c2d500030034890304545036007101517203c0e02e800380020828610200c030051194800030b40010b03034400209134141201e00807103016505a4440091000106401030018050710f20030000503400d09039140310040b811010b01c000683c0c290407020034004000190030230f807 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 49532935 1250 49531685 49531709
    0x216030c03031103030f0c1803120904381513060e01020307080403020d0512030f09010c081501230705150702030a0c0305090114120a0506010513060818010501 70
    0x700034550440c18900444101500075482c502d03201032000029007010300716000540340000c44414680302807050964506008007900c0808510102e000005e5018a00460059092a1040f40d49103c400740d0300c140c01c4141449480400701c1d40e4880c680300c55000c1d004c10b9100c080c103d41448124500c2c0c000d030108201076151006041c0c2041c030301804107031082c05400e04542c03040000500080c3c1580a9030100c0f5815545003002c0f04d50f81c6409424120390b1880c50b0a805008410002001d60b1120194000c0d10b0f40300007007110a0210b081114010800c81e8800141141a021b003107155106a00e89010f021415011000c00400d502c01c03280c17194002001501c0e203500466000b40e4803000340034040c1c3c04c2041c3d80019031508920f04400b61060323000c40300141c140540030446141d00d03401411516240c258194206035110b4000c024230706003040684040100e1854003000400c1540140111003c02c2c45200b0880c3c8a513140c1002160041c00081003030000047c200d4000c42036460900407113010b802055070302 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 49534185 1250 49532935 49532939
    0xf0d0608010b030115290d050c1801181e050301050702010e0c19061409030304030b0712050609180a060e0a0b07050a0509040504021207030501050106110102030f06040504030216030c 80
    0x5130070b441c82c04500d4622001100703002c0100b1070712001c941c030040c4010500610a80c0410f00c550f00c00b40a01500d00c48014141410400703001051401400d000f044800c0c0c2581c2005c0c62001115074199204e01400e022800c0003084c44400314400811039854841140240e10036215800702c3c0c2595130695116001d82c0d120b1170f4401c1450b01c18030182191210585502174400b40711071980c810b0000602c04c3d030302031155286400701c181d031102040b24000c400c09800c40c2e560300da50f85003898105000716510350004400c621003816000072402100d0080324001c00d00c1170203481311101c030304016680c0f40581141e44a03252200d0001422030041d01d440d25881406080e12030500d0800312401d00004000c1c00070402c00308004028070780c0150a07200f04603019200005c95a48600c00f25940941658050300507100c1d0788800403c110301500400d0580e422681d030800000e8807000514240e000554200c18040f04190000c0d96034203081c0d201c2a0720900a00c1124a01512500c801a001c1d0ba00d0300240d521000340759003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 49535435 1250 49534185 49534189
    0x702060a0b030a2f0405060d02010c0c0b12040b09030313020402030c16060506030c0d0c031e02090a050a0605040209090a052205010c080610020d0f05041503050412030c02070303050f0d0608010b 85
    0x3140784c20315043c2c900340010b241001c0021080d40510100a05200c80303266000140013440220740050200c1e128503e60740d01c0704904403200d16800f11000c5400305d09010001d4203880010003034038002da2118040c104d00106590030400a5000107100c240390400c1480070f4140200403801000d0001d0280c03030009500c5c100703002490304290078200c8843c00b607101c101da1000000c1303003c0590411a90045145403501e26a1411510346114520019602140e120140300d00c40c042d981c0024020b2440b18020010140e40700c040c0700c1079001e1464200d51042c1d02c0000280d00178681c0e0000c0b6407007030f40301020b45551240021041c942e0b014807482654517a5640003044140d0350403d9041c0d801c00c408440c1000021281c2000a540300d9854101c04200083c1c0a10080b220340504107581c05000d40340e07401d1a94402e1040d00600908040f601075481c040d0040108400a002c0e22507000303904c0f01036000c0d001c05801c6417416a601d0380b1524004480c008108402c0c010011a0f01c80c00001c1c0c401100007003404001501 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 49536685 1250 49535435 49535513
    0x408090604062601240201110703020d0306080f0d110a080f04030b071d01030f0e0709091e03091e0905040b040b0f0c09040c0903021f020d0203030702060a0b030a 71
    0x80b850f814048001070000c0c6482d0209801c0034140c15170f407143c81400a1104a01400031500c03c0e0410b0700c2d02240081c01c054010071600340a110aa8041159a80d41c00029546503800e00e050a0580c015428103800f0505c5000c548107081c1c02d090484040e100030396036140c51a800700c80c0a0048050214080c0104202400c110f40c00c0200c9141ca10302da500c041204da0808281e01d41d4843c10715a444c0180a410030b11600800d0121200b0001d50b03120640d42c0c102c1d00702601e2100d03404c81c0c03d80349812200c42e8890000c81c064010581540d100900c0c03509143c504800010020310030590f000c465440011500e40902440384110310400c00d0b070b16541028648010303280381c045d101d140000d801c44100003c0d050082c082c5c0d0768500c412200841c0c1c81810700300580e100f0b14142c00c0a500001425412440f403000c0c403810625120f656822140b00c1c60b520b0000b01c1e02da000640d650300040e04200b01040700c40301181c10031103907460700500f0f48a80a00340d03a00d810202084803440140340030130403a480e5170119101 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 49537935 1250 49536685 49536737
    0xf0a0e011502030c0c04020319110c0c0d08040e090307140d2a060f0209030105010b1e070308010e04080f0d051602010207081b0109080703051903060b12040809060406 73
    0x40020741c100524080c902e0303107404107142e20ba80102c1d070100000f00b08d070b141e0032550075203002c989c0410054045080e15001083e4444041c1540720710542c16a03c00c0360801c1c0c0181102503030080700060515007480c1c0050f81241002c7c03d0418030b84401d015080120b9030803405c034074820b0031040080000a500f00405403122030345040e00c015031901c0c1441c02007049204447c4ea80d051740c0c410b400144040c40312640130004d0243c0200107400d07610301030012600c464068001d1005020140d003402c1203400f1002440f10b01d100720340340100002c44507001048942c1b50407034115002485040f00500f04050a024810f094000c2c04100388070b80c0e01c0302d050000aa000c803000d41d401907000c0c4001d502c0d00b15551140d0340d040c4a412145510300c13800c0490000c144c1c0c82980310001c03ca5204000e142d5500380c904001740030380c100a1070000e204801600e11110f290082c0304400c211840310407202d040180c100c5001101c071400030010b031800302e0100090036050b6205001032000c0e10094035840c02a6080c60100e5940070009 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 49539185 1250 49537935 49537937
    0x304050915011d031204140301050a0504020a0603020a05090d060902010e10020318030708072606040b04080702180903040806090d050403120315060908010c08040b0601030b0f0a0e0115 81
    0xd02903042032640d010f12040480c81c3d1030b65100b5841001c800100c1c1c5070401001d034501c41c80001140108945440d1500020707900c0c0114028000c40d01d418402104581c000d4500950040a1441c10003050340a50040d0640350104d0610350300303080c0d0b50340120b05654406e2108803251503841180208542c4c000d500b2080e8240d0681c0c100b9141e42031868007a6607440303000c811f680f0040c1c075105200304c41d6400308002005032401744144d8941680c2d030f08141c1e4a11410341f0420703407103283c00c50a8807078a040014000b84a03641000100d8101d8a5035244e007441035004d10003c0e41c0101c480b0100541c00346c0204200d42c000c2c95918011a5a03520b0859014140f04000e40141c6043d041054a400055130000c1a50180c0740c0020508461000c0c00c01300350b0042400e03800c90302156440e444000340083d0020300c0f00013214a00c800a00c2081030341c00007215422400c9400910305c12010700810119403090780510b04140b8090450865104804009052036003240e021010b0500c441005000800c1c41c84074811040c006 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 49540435 1250 49539185 49539211
    0x21509010f18140a0909060203010503100921170103030206240f010e01020a14060a060e070c080f0702030304090903031b020a0b040c050904030f0306140604050d0201090305030c03040509 82
    0x2c614505511070984690140040380011000c155511020000c00810725860100941405490300001030741091003644c2c440d008044100d900da541c98080c0c2d04100d03034015000c245d01500c910b142c640e004002c09100040220625010f605040ca44200074007950094008014a140441c03504151181510180407105048a00c070140ba4450068502010400b400e114170312580d0200100c0c982500088058554092403810381070410f000318840c0d005170aa4071090080544940c030203044c52006170b038000b00042e13241d400c0101051b0b240b00649100030113100712910707210543c2c0029145400c5134000421113955400c42600300b642500c95000c11146030030704d404003c4001003010352200c40642d00a0000c0c044040060100543c1c0e4450001800005240d4111070803e8200141520a01031104022030310704400454580c1c1206214841d0344801011107203040c1c10042840000099030300c0c1241800740c03c8002200140c070600c040c00780c54203e00019600d482c84e00040200f40c035806002c400352010 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 49541685 1250 49540435 49540457
    0xc0c0b0708030402270106030902090a0c1b050106150201060e06040605010f0e04020706090318060806030a0201030207061b0804121704021903150609050a05010503030a0c0609021509010f 82
    0xa001c15294801c0d01290102d41e1101c1c15104580d42c3da0314458008020104200003217040350305035000382c4280780207a804290715501d102c007031300440d0b9030142001c5c0481d500d55041800c0614011300c051800b4480c80011514540c6c1d05010100d8003d920705100150b51510b03002c4c880702e1150080941c1c0007504440900c003641c130303110000e0301c60450405450204408609440825211601141c0c0c14a038040c00800000843d41802171144032050046542049042e0340001c410b0700c52650035024000080142440403a640c1c0103500951101d02c0c201d50482d225114103d4034410001d501c2d0070b440141d164130045103001e2401e40c68441c51080306006024952500010f40e5603201206a40181e041e242298100c1d4002540034944110b940014842c00c4025030325607411900b6040305003101c0c010702040c8031036220140b1405c25200b09000c0c003a05540305000441c101c510a444010110380920380000e1440d85640100b42a00c1200540f0070240100003981016940d01c9041f41840030450b16000c49450 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 49542935 1250 49541685 49541693
    0x2060d0e0f03070b0f040303180c0e06010923010207170601060909050408040302060c150c0a02150c092e0201090210020307020d02060d020c03070c06030506030d080c1c0c0c0c0b07 79
    0x1d0401340045c56207154450000d0200b44c042c1e0302c00c0b402c03401c80c1e1030f058140364058a0302444210030b600038048050b0104001c200654007402c0b500c030580c0c03c92960061942c4001800d000340901c088a01e074110320801034000f4105e280c1c0300030b62031802c2010018144540c18020301414240303595011351007591525041001103400c400070345041d02d130304541c2c6a07a1040c840d0000c610300346807001c10000100d20749083c007400d5541c110061817070790060340a45048190100c41607807903900450300d41a581108100e46035440c41c142c17251103038204070382c1d01c0d604c000145103411111592482940ba400b42c1e540d03d01560a6180080781400300000e03d2000b0340c54485aa0b001c15003150041c18020300a0302c0100d4104021890394060b00c8034210300f036003202e03161441c45c207044c20240c47c203208880c04240b43c01c0105142d4140450800c41e02c40c2c01d5105d800305500d0310301c03450140764015400b081d0040034405500c0c016a82c94000c2400b03d1045548210f20f002850404c2c0742001115884403032000002c105290000d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 49544185 1250 49542935 49542953
    0x5090f070b0a0503060d02090f0a0e1911041404050a0c0e070e0d110316031103010203060108070c02010c08031e01140d0305070804090e06010807050102060c031501090302060d0e0f0307 81
    0x380b00d0b520f4400e807207450311408a03884101c4620300952102010007000358000001681a02ca00010101404407041e541d4410b501d0310104005030f50040303584400c141c04556440090b5a011501400c00102445c030f0001c0104058401da600b01c840e034122840240600c281c8001c401c1c040d018a0291040e58100240c000d45003000203440710380a0092460004244076126980003800c1c08058192010807000c401144040c118078001114440b18010641b40103050500c00d491099a040c0c4807100940c684001c10380340607036001d000303d040110b144440000502214017450160344407001c1d641c040741d1244e00c00406144140c0050310b0305e021901d44034088c0d0380c550400800f12509810090303500c502d681004600e91182c1d170002c1c042d0b1400c041075035001032000038540d030489410000fa1030565844400490320f5120541e0141600907040c808100441080da00503410060305052030000c007a5241c0c045540c40d0000e00070351000720341d201000c60280c10140141488091000042e43c6007039010b559000203 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 49545435 1250 49544185 49544197
    0x8070212190c06060305010f09050f010203100314211c0507020606042c03090109060203040e010e06030321090705030c061801090f0807151106070503090c0406030605090f070b 77
    0xc00000b48000010301919502c12000345400c2002440030b0904003c0c0c0001a0642800803100380c070036178031847c107100700c1031007517034082d0581040c40541c00b49551600072040e02260111141c0b400768104801b10280d6084032050001c024002c0141c4a401c0c401018a4041c207a1340611003041c2441d0811105e243e01145999202c82c0440b00065030003070303c42c401d1001d501c000305031000b020601c0e1b2403034000756000006000103d03000d0380c402550b0340d21813074201c0c0c0700e00480c03092140300e020950050104010700320401c2ea100001030101ca083c00d82c110b216821000daa00004541720140c5001d00180c55024004080509026002068601a41d00128030540309560721502c1c1c403904008164a240e114610100c000e290604c0c440241e0b5850710405a10345106100302c409046030395028200c2940142101c180001b21200500f40a5071520000e448603400140340090314040d84000514982d5148119006140180c00002c0c207490300d010010f03d8050100c07220807555000140c01c201180c00c10341100c1c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 49546685 1250 49545435 49545437
    0x917060928020414040605090f060109020d0b0415050a080c0d080a0c080c06010608010603050606070209060609130603060f0209030d0f050904090b0601031a0d0201080c0d06060807021219 82
    0x14942190311103041c40504040c0009621030305103004004007540d60030402d80a240500410001c58460303165566588203407503400788540d0800c10040003036003400c1d8050066152218004900e500c80c0c04002011118040c1c4007008044140b0024806410421007403405403010341c0007840b841840c60002003001e41002c60040440500146130340c440f0307103d00400030200c0e91141415132140185038446032100c80074014400018900310001030550b1080c01034038022030300030340850710f02491a0284039880500420154010208000c400c03840c0e200c024406402d483c6044000580c0c40c10342c80c11034140c1c3c1403e4000752138680184030f418095500480c01c54450300040c107100482c40221a02503425010381e007046580f041c58105030346c00780300309d46018510560007640c04010480c4815800416100c62804c0e10307802000500b01c0c08010b500401c1c00640103180a8409418001c03010302e20400c1d6409900070000140d000c41c1405000c1d5010002c03100703201c00000e540c50411100a101a07104082040c4541c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 49547935 1250 49546685 49546723
    0x11103070f0f05120307021501060503060d051c050a0908010510120c090504140c01140406030f0e010603080c060f09060406090305130806060a0803070c17070f0609170609 75
    0x10400303415a0b10707003400e80c400c0603620302018250000880f03400c1103031210050700138aa0100304030302244255a0584e400d0b078843d40d0541e1110400c0c400d4090280c0c808884522883e180900082e00d46c0e518014000895a292542c070300c0b41100040c030300145a13200004d10703810311050100c120b18000207038080d9141542984034000d00d90403c01100485984032601b618681000e100c1405003000c02135140a00130401c82ea0440cbe0441700450300e60301800d01c0e01004020600c810b2180c2c6100740c01c011015000c0e980d02140c003043c7c1461060031a038040c0e10843d01010001280005190700340503080d0700142030b110071035003131801841140c0c80f010f0041004040f20b5a5040620405002d1400ea4242c041013401c8602190344541007683d5500703003511480e12951000c40c002812640000c129801250321868010708203107451032a81c4440701800c1081028000c50001140625590b00124000c00e00c6550b00740c19285480342d0756200320b803220000b0b08190030000401c0381071a0005045404e51071070070080707 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 49549185 1250 49547935 49547963
    0x2070e070f12020706061403061303030e010b130c0e0607080a0e0a0315060302040b042c030405060c0d0807030608060f100b040e041110020d08101503091101110307 72
    0x100d894a42d982400d002c494030100c0c5002c18064030742d01100c142e40034030041071900618081096903c1504440000c511400e4841d9500024440d8101400c01250307000045440024280001c448104070460300600668520075102c0342c682c0255040b1640400352400c900e41100c03915174082510511301450140080c0050b0900e0907215001070b04020358110040451807001c9103100c601070241e0b0301c070583c4103504084c00c03040c0501c0c1a208071030390240c500d00c0f203000c201c03140644c0c2c84011004543c4480d450100b44400900da0b11081d00400301d92010760050300d04403802003005840c00101416030410540f0741403052121b000005405504a42c0141a200345030340d4600e80c810141c421600042c4501c180030038005042e42084504074025489500c04c18882012001444691013002c001240180e0045842010b05030007072240d82e412295218000e481c040e00c8403142c0c010013885480e110700103641c130413008042c00b401a4203a4650442480c01c1e9110800900f01c2e20342e04e00441c80043c00d6a007140c03050b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 49550435 1250 49549185 49549187
    0x60d030203040603020c10020301180501090510030213090b0c071e020d03080a0902060408010207030e060f03070c08090a060c0201080f040b06060f070209010f05010909020a0c1401330602070e070f 86
    0xb641d43c1c4040a0346088d5130380d40e11140c1001da45003040504031807081c10704c00041a03009046c011648590301454440740300c10310b55001c1103d60740344040c00003e0f80b0799403640e5802190215650034851050421640d40c3c0b035515143c090380c0080d44641c850b0484500420440050b603c0c0c961781d40001d0f80500d40030000f629060b9111008003510b0074029844140000c002400305019001381030207a0180d03c82c4000109100b09210b450310612100700c0641c0c3d0304000090941d40038004030303101140120021410100201d001c1280180340350025000b2485495641e0115a40b155803290b1191074060941028240f5644501000c2e00107403890740700303082c04900d00c2984d03c116030690f098540c00806074209542d5075119510400c4890140d18001454000c01069510850003200e802a600c0d9076111200c152546800540103881c2101603115502c800015050480c8043c40302d04175100c40b8004c10103203030000d012807034911043d400101550080141000420101c81140d076000400d4144400b001c800c40f50 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 49551685 1250 49550435 49550443
    0x120804020f0d030207091a1021020c030301050a0b090108312102030c030f0f040506070606060f020c0a05060c0109080f09031605030a1b08010603050a0605060d030203040603020c 78
    0x20710303074122140040020030302d980050300700102c501091003001440c00d0110840b2110f2a031101e200e0b00082d214002648191040404d06065803c1810804401000f00408016648100c0580e10a64800700c01805945000600140101b2907080201d00d084411000a41614001040d0f20034803078029680300800001416481102c2e002d560240011100c0b525000502140c05116000b51502902c0020401400001145c9555090100460410108000302c0c0d1081d440003440c41000306040c040024a902c648014050700c6100b40c001107483c40c1070000040694a00b00c0340706086610015101d611900d80044d40c0c01980e50030348400381c2d40d01603207100e1400361050320402000484001950820404540050b09440c3c4084040d1a5114031210301001844500c4c041d0030791581010b00f80700009601701400c101403044210301f107074600d81d41300c0d1850300311070340d40e441034400340c000e41c06d1142080058440e00d640140100d40707132142e052030f0303441c02903030380c0030b01e016035424103500050340c280c1e09600304 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 49552935 1250 49551685 49551709
    0x1828020f0a03020304060e0307020a0b030705130602030703030f0b130902030313030b071107060e010509010905030706020304140603010b12090c04051006182d030f080301030b010f0312080402 84
    0x40c80055542151440040003948103c80c2070360160300d4036110f0f120284020086601d11500101015992401e05c0314515056002401681c2441000c0004903000b21804e0f915100414654002e140c4a603800d0030050300761804011181d007468603107442211140e940302c2c05484c901a00c5240000c00449030320100c0e2a41c0310313440502410702c1c0e0000d000010040503008081c40344402d03685a00c50301e515007001070b903140c030356001c0d010201c2c081503500002544030320060010140c0c1490203850103a91040400d0074403141d5000b07140107030070010b418007001e250500c40e1986084103450715072456151000401c07050003071052041070800e18801082423414204044211000e00500070002810b00701c881c400708035003911800b00403070f02d11880d03200c84140c031060707170710403501d1401c07201d206100081c5548842c494840e48a6420302940302c40400482c4c8600780d0700407a0307485811811780d254190f043c00461501e059220302110100740c50709200007081409000100021800e20803002c2e210703440000c403066003075 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 49554185 1250 49552935 49552957
    0x409020f09101106070e0621010906060e0307120206070506070507021318080307110712050c0a080304060c02040e100b0405010510050405090a0b10030b182802 70
    0x10680d00049a403410080c140144110780c400700b555804001a6a40460720015000581004001401c118062820440c4646e001030555103000d00d15031036082d41008244082101c10007000c011300c401841e40c07150501412080c24418080007440002035a240c1c42d82c0210071440002454090031501c83c0c50607106081e5020041c1c450500e807490000300b1980040d001a0b00c5400c911101e01d000f0141c1c1c0c42101030500c01c007a05030741b0410443d1030352500740d400a465801006551540010001c400b0b1000c8005000241c1c280010341c1d40505249103003501840b130082c0316103030300300d01040703a2007000040b00c2c02c58201d4244006854643c0c00014000c1c2050301c00301105004041c004284200c49a2100070700c6403007150208031a0b40c86000340846402c1003544400440d808000520480c540114000d80c800702c442c42c04079040c1003d0b0701043c8020321600a2001182c0c4504106171140f40803590300e503001c0e0540040380c005141c031028a45d0042c10394042e18141515820210820004c0c58044902170209 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 49555435 1250 49554185 49554187
    0x40b0a02011b032301080a062703021609021c18060c0305060405010905070905010804151d01270f0f050105070c05011812050a03060f0b120601020c24040902 69
    0x41c15400f8024101046250f5075030620fa42c4600440c000c1460002d05840d007110040144a0660759004000c00781003106424150841e0113104d90b000621903c030344002e219902070460240461580622039821f40c002d104014014010241e10221404d60450030b5455500b02144003041503408408091280402074240343c00c01842079640c1c0e4040d0031007400745400751000c100580e680c1d443d05044030425290300c00040c00303001c02001150310603800582c02034040e851101601001c02008801c50319441d00854a10003004440f0300c80304801c2c452040c0b0345a20244022644661071300711003559403600c02c002d050301e407407013040da090041c00700c0b01904041c3d00100800032410840006001d00d01c3d2450301315034560915601d040071050b500e190f00b03503866015034401e9403590103490644068120307011041c1003503519540040d40101c01d4500c1c0c0020001003034201d66030110314018024404005108078155807103d01c0c0c040003901d4090707134000c684a100541c0440c10202d4101c245c2d5510550344000b0000d40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 49556685 1250 49555435 49555481
    0x21f0c06050a02030f071e050f0d02031005031614120a1a06040e01090c03080919060c02040b03010c020a030513050904050d08060a0f09020702220506030f030f040b0a0201 75
    0x7140d54004c40c018820b207403402a40741d4450b0800c80f500c04150016051007055038412500741390145c40079100300c1904810040c10168140c00c07820417070f007003226480081d041d0108100500d050030711060242803080c0740d014070207a00341045059840883c00d00240203903401c1908014158003803002d000d101354410074440f0386401400b1038221080e01683d05a12561a1443d6542814014811100b2403a44a18107510091031501d500800b60000c405c10758000c036085001940741464510f15201a05d210b44400c3d06100031b074010300c4110f0383d00c0e1640ca07000360301d0003601e20344c002d40028541912030790500d0000c1e90b8903c075203407841c4c0c0b01c90168845500048130302c00b84010041c02154043c103207030301035444200d141c2c3c900e8100402c050903441088641025440e0600c10451580c000300200c60010708500550110180d0039143c3c0701061a6100703559036604140000c9180a208942c903141c1000c000f9804c1001c5451440c4240c03103140300b40d401119000a412100324001e4000f04d01e20040a806645c07518 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 49557935 1250 49556685 49556701
    0xa0302071e0308100303080a051003020d200402040501050d0902011214010e0a060b04090e0c060304060207020405010e16030e010b030d021c0201050106050d050a09020a14090108010504021f0c0605 86
    0x74800d800c00c40200d0181400542c210000e04403290071603806a460a1581c1c854114810040c0b10250128025065505004c13002d03071100f60072088500d00c0303108692580d109100209614406400300780e44118010482080607a90203030585104400c0d038540091203408500c010b07961038441c0302c2c00c015042c0c14004084001070075a0149030480d5450000d00c001b507940d07054001c1c1210410701484400041c00c2c001881815842d03449070550521080c01c0300d8100b0a5000050740c1601300321000c0b5031141e00041d4800441c1130901a4034010000120100c010741808213080100d19450ba10717913400c06a4802e480c1c0f040d003000350000c050340800034080d10105146080029107031036401100815401d21070761a000d0840c814440d40d8120381032503994509044842082d0000386c0030103400624030586818007040960f81d011307080070080440ea80d1100030480004140040220141c0c064096a490701c000c10000d600e9400400a00d12030408015112709070890069500f03c01c0c80d400a80544c0c68003007000164 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 49559185 1250 49557935 49557983
    0xa0e01080c090a06030308010b162001020d0e010207061202090402121e09030403030f1808010204060201060e010e01120c1212030b0f0d0602130512010219170601050a030207 76
    0x1218040c1c802003015035a030f03c0c2010036164140700080c00288450010042103050101500c2d440780303201d486081300051512164030900314090301500750300c10120400d41c90b6804100214a040c56404d101020287c1c50001035180c04e158030440c030500030303044a841030307401039035044502e01e000c000d0007151030b69041450383d40840d904580c112420f0f1012206516020500b007842c511441030b20004620345803c40d901101c0540c1c3c40c6000006018564404021f503406892030381000d00010000140ca841c0392034802420740d100c552062603241d0040c001480840c40c22810281035030035034440d11590704402e1a01c4c0741c3c100907541c08907050741484a20603081041c450f103200d038071024982e01403007035003e15030170811001a900c05d030b250322000c001c190310009001034014004101400341e80e24801591400421080210143c400e0100d960004041685800010550036038101c1c1d0b20303102c948040c241246c024004400f80504d41405004101e0031010340c402c0d0112800c065103c0c4004001c800090f81035094 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 49560435 1250 49559185 49559203
    0xf09090103060b120f0712020d0605190f0605010507080918040b01030512040503100903020f070603020301030615060c060e0a020a09090201021c020a0318080a030203030a1a0109030209060a0e0108 86
    0x10901c1d03010b81c42945001e001076074034842c00c80c00c009000c0c6c1d5850b01111034407a1141c134400320b03003208080c1502004680944186482400120134482c0e10822030035240e8115900c20280d07001d01442c014041c480b07a644030f006d4451196120701e14079500e03500c0c2000103440075410002c084105116804010811032002081030403a80b00d0812110603d03034480301712205008a004e115019801298140f11034441e0303401845000d4003d00658543c1022190441e0500005400c503002007030b00000100200821481141200700d079400c282e90b8140e0a15500610a400c0410054034041e20b403280c40a00200030712a2100d07455000300112801540d502121015000c130341000d90140c028450f4400550303a4204d00c50b004242c5640c0a88280407441d4ac0640b1000b83c03d0310100a202140d4201080d180300030032510840c6800780d001140c90b49401e541e1364003980c00710004030040c56031040c14074000d41d8001c0341000c107490b41207402d001c0c19680e81c004581d89845550005517041c1001c4000036407a0320108440031 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 49561685 1250 49560435 49560439
    0x60f110706110f0f07060b030f0c0307050a030201050304030503190504060b0f0118051201020c0610030b3405160606050411040b041514031006080601030507140f09090103060b 77
    0xb590300d00110314094040c410310320400060401103642c2226511008200c050f1041c040010070542400200e4a0446d028400302e210f64010034000115140c100078000007070030f044a4488a10b81103a000800714000503100606000300400814840b032611003500c04003048208081049203494100304000d486c215805c14020354000c040600154440d48501001d60b54480c000340c0c41d54a0401400224811111105001d540c2801104481da40c01c1c405c250082c10403550300241d060550404080050001c0e001d48480c5110900b02550300003415407445d0001490f0410f014a564420340c260303004c0c403030788a044240c0785400000c44208441944414113881003602c0c1006407026050606005106500402c13140140a101c10804801c4459591154a40d540f6059001d9645130800340c40c250001d441e061034000140d90709000c05c56100b1001c81e4803601c2441c052106003032548020308004100c8050411007880042c5805190303800c101220000017018102c0e003029a542d00304680104441484c081c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 49562935 1250 49561685 49561691
    0x8010504110313031110020d02040503070501021c0e0d12080108070503010614060c0123010305010c0503070e010c0809030304080c1201020702090f0403030b040e010218040c0e0d060f110706 83
    0x4841d84221050720b00c1102d040c0610f0010035265113043d07642e401d0034801900a031050005010440c400350000d0b0220f81c140b44005078440d81008101410006076402003811580000001070305001d81d0350002003200000e00f000e00c02940e41f03401240b031002e0400409000c25801c5404110010780c000d01150490b00c821040d55113040c1c40304109400d032005032090003104000340d8074096052030800000d10146640d000000313411a800c035084402482d030480c0c1c00e84055000401003003800002e004074540c00445141081ca1890117038000b8100d03448030b0504504108482d18450708000d5440101d5030400720003400c89442d283da40041d01c0e0ba82100070070117400355101d80908a8040414020355000b6507005100d40708642e54005540d050310720081080e0205038035010b410510391514800c200041c111036002684c0c44044880003013a43d01d604428a0050b4605400078006a0b40291509035104003103071080c1c034160302414407001505016100721000b41c50601a04030810011005100c52441100700b4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 49564185 1250 49562935 49562951
    0x5070c0801050601090b0c0312070915020102030c030420090c13050a03020105070b07050d0c030209030c090f0a0902030a0203010e0f060109050103080a0806030f0708030406180b0d110d0c08010504 86
    0x14203803001503d00c140407a850103428810f45038180007521520341d810048038240300d08030000c010301400c2580e1140100751103007001d00100d445658944004081d50000758a1410b2001c0c040741d051000a101925202160110b000c5003142001542c201d0300c4024180c03512800d211075030002d1035100e100b60801c881206840040e140c10407079030110890303405271140750904050341c44802c20044000c0106042090406c01d03a14003207681d1095582908071170f42d0058036500080e00741840d2544c0038507401e1003503040c8410081d581d40d1104507154400341041010a0030b40c3c00e0300c0481e20300341040038025455402c00c2c0300c06802c80d00014503d0b52a10404084640b0769903690320032002c80d81c080c000035191103010800c0c00c4011740102403540d0069006000c5400ba0b014103040542000900d4101c025141c000183c03c100b8503a00451008080c180a00d40600852508007400385c648282c01102c0c007260344588410042105420544500f110001c1d4144940507118800502c204005d0040c2c0307118901e02191 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 49565435 1250 49564185 49564199
    0x30f07030503071b081903030b0415061101021219060e070203090103090f14010c11010b0922080c0a030f0e0d0213020f0c030d2313050304030803040305070c 69
    0x2002120340003005985005003c2d1521000036030a418000205015490000740c4a0001c00c00da0399450f0444003002d05001892800505641c1000c072014440c5040c038a1904420201440c80c4080f1585404c0c5081c100c22520601b9019028021030729030b24401c400c081251059a06030807400a4071890300c10481c035074130b40a40c80d00d80310013074640d94016801403140450300e5003c3d91240035168050320441c001b1740380590b152907448450f100c1002c0c075039444e002040d8005400845000041d1a042d00902104101c50042a95070000410300f401c1130007075994000d4403490070100361117565001080340303983e0b48690380500d42d1072510074000c5000942214004200b01c0c800c03590000d45140090200300072007a0360f020012180a103511043c0519030820840d24980400c81c0244440000070002e0f603180c1125116013800c6a45032401c0c0c4110000c2800e8140122100b1200180c0c80310340c181d4034500b200301c3c50400745e00e10700450708010300660b0004103000a158000c5c002e4a0814414101092601d4803004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 49566685 1250 49565435 49565443
    0x6060b0301031a06010c0209040302030a020f0705011d06090414160302130b1b01020a0e0909060907170a0501020d06051e0306010b070501090515061005040f0b070201020109060c030506030f 83
    0x20010307040700403c502407900c1400c09196030340c01400503d001203a440710b5400180804005440c1100541c2c8006003070006142c05006900c0042c1503140a0700031640740c00006404003001441c80c0340c2c41c2e607005141e00c01c10340e124401d0760340300113001d0400c00154000c41c04140810000345e4a03c04640b14600128004030b1080c0203e480310185010714074420791a00321448946d0b000712031240c030004844440f00030328a0091020f01011025942ca141420307000906100b40f2100103131444019402a00c10000c0703115000940f4811070b05408140300503005040d1101c0d05120b0340350002400703940001342c5034140300305540100701581c0007100c0d050040c5000040030708601c403c1402c06a09a00400010007494010501a11600340508004594000280c1d2202d00b030404100034804100345c640240140703030030400d001407107004041c1000d03807400d403e2011902c81d82d85c00748036407000c100340020b0110441e40700790030400101d540580d00303000f24180c0b45805009070000300c5000780a80300307800c118400340380002 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 49567935 1250 49566685 49566689
    0x806090105041703190509070f0e0f010620030703030b010e040e1b0a09021b011107030903080702040e160602010c0509090c07080f0414090a05040209181606030906060b0301 76
    0x203500c4140c0c1501480500f1868000416201c424281801310a1198406000c0c4501c5114210060401c503414034080521404080d008031071131825900c1040b400c0e00341010700c28191500390911403c81d0031103040c0004000340c140c049003c1400f01140d50001c05405401802d0240404d0300e4007190528201c0c240411900d01c402c0103c8558020240710104096070825640344900241c0b801c41d11917103d003085000da83c4000c3e6407030b41c0400404160084c81e1420300c1049030103100f8020300d038a03045003620b001f8103d00c01804080c04d1588000b074518215982d03548884e8144e2042800e403041c0e07d254100c0040c80c5121803140c5405542000c407983d0304617208008035412003100034004440343d2208103c854080e04030160488500c1801c01c903007104041c640d0058001808198583c8001c00215400d02240340c5015141014443c1003606000060f6100c42d000c40d48655002800d00400f081c900340f281c83e100c0c00110203901454100c10102c2c3c00e80e81601300e003140c0c41c06850107000082d0755810701c00041c4424 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 49569185 1250 49567935 49567943
    0x4050907080601081602120a020604020a06050f0708032d0711030f0406031104050901120c0909080a0e0a031b03170408060402010f030b030601090e0c010305010501120c030603051006080609010504 86
    0x70000105c40001510705000340c0c0640e0b1040300d00151280d40307464207660002c9400805603100c10204411031429048040107400303076151981c20720018050020701805410001846003801000242e1100d40b98004000b0800034a18607480d02c2074801004001010140d61490001e10f00494016104000200300c1e01e11501c0c1a803c0c0e03180500d0200128024104040313100c8040500704400215640c0316000c41e40031348243d0b50320701503061a40c50006420820741d84a11002d5040640000219544070705494504c045c1e8140101500018400140819015000108110081080e0401c01c2d107040c00020240c920640205840d9111120220228022031007107912035031204c0300240055109403150606800e65040215104440200090602d8030903085503c030181c0c0d0791301c1c07484000c208118003014483e0a003010000355050000082080b00c1c0b41103501080d0340c60b501012880c911a50041d4025134109041d6864909814200b50182040c4e103e940e416228030b0011a034150810703c2840d00550744 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 49570435 1250 49569185 49569197
    0x140313020a12110415050f03160902031614030610050702030d0f1202121f0b0301090203060a05040b090604050606070b01140306010501090f12030306090f060329040206070c080a0804050907080601 86
    0x2400c0204071007e090f070307207e5907010701a05901d01008031000340c011000e4a0080d40c00340e2a031400b10402031120a84107500b01c100019003600300c030040b910000310398002d078083e0f40348038100780d019200752030714802d080c8002d425100e21800181860760000210101980c1303980c0b80360ba6607001c108100140d00a1490306081c0300c180e0b0021406031101c203001c42e058070003040300c100c00c415560006401c490304240d100c041c40382e8002003000481d14104041e40c0141008031003c100200d01705021403004080280160300076035a40c4041490740d0f03140000d0342e4100d0740c0158244881d685543d00c1032216114021110b0181c811000003044035801107a0003015a0901541d2030310240c50b01443e00f244a1514000342c0906684940104045005000b04078103d000040045005851407401c42e4bc542801504001910300218003003c947c00700c81c6a00d40c016404840c0e241c1c03145664203004290b5241d5610035040c0788105880d5408200a060240c000c440080390f10402c00d81d03803201c060760140e02c21030346207000600d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 49571685 1250 49570435 49570439
    0x105151e01020c06070b10060914010807090803070507030204140601050a0305060d0f030e01020f030a090b1c1d0601060507031b03020c090c0409180201140313020a12110415 76
    0x103480118005011014812034581c00e000401103512503010280039900200b6060401c04803001211110004040e240350641c215071400a0080c030b981400e035403150421170408045081184120907160140042106596480b04103182c1130b90f84212602c42280940e0503c0d11480c40f071058044035a11901068482528220403000120b00500000300102d500c11041034400300403821004119103440d2290b105c220714030403d48000380c50a0001c2e0501090395000f0041343d0b040c81d07403142c280740c201c1c0c01843c0c8007601d0b00c40030342c1303202441442290100144c9161441c00c45040300a0746c0c0d59a0f10302c204a05070794080e42c80f4a0200c5142c4034221001e404074a080680c14036011001e105001c0490203032040c0d44080040c00d000544480c010b4821122030880810140100d10540c4160b0404038166590a42110300950001e03140c1003010301310710f81c076507008800500e070541102d00701c0121990040030f400100e42c40e4800040041030000c826504c10b100c030b602040d914182845005910321840c2203000c480341c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 49572935 1250 49571685 49571719
    0x40207020904020d0c0f0303170a0b03120901020a0605090a020a060201060608152202090103060806011a0f0c0a0f0605240402030a0204080109230d050415030b1f02010515 75
    0x140050801c03601c01c1c5c000680000c00203880e8410101441c801d664680d44988045404416000d018025401c0280b414a800969503000156402043c07103058105403100c2c0550010303424244811405000309003802c04020b045440824503458103482103451240703058540308120300303c0b1598006d04021901e9100441d0490341ca100300751400e07a4000302030009520440034443e8030812042000200a41c01150325076a035a0140a220040c0107114000e01043d0302d000580030643c18040c90b012541d034400264200d503880d002080300e224029680c220781c034429591401003042e00385e500d0140d40740c0b45440085041c801500505c0c5000000c42004551012140301c1000000e5002038640c80c01254200400102410300780900c1200c18000e041c0c4405a044441032800507070300500495849030001441d0034111a04141550706560100756440d61410304018154010310840c0c1c0035590040400c00e68a181d261003080902c642961070f07000b884241c403900c0c0d12304c2034591044010341e0700c0380800c00d09000403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 49574185 1250 49572935 49572949
    0x6080607020a0b310501090201080c0708040b03070c0c030c061808101d010c050d0b0103050403050d02070c0b0c010516020c0109030602090307090603050f06060d030c020f01180605130504020702090402 88
    0x110442036850405003d4003005844c201501c54811100c40c1d44030540203040d503800280321544030301d140e80024640a0503a030742c0400f520540c0680300006d0300c013102080d281407041303030038442103540b040404242c65180c0c00e010102584600c074001c0007a0500703c0c52489000360464a10440d0022001442c403180503491180103801038840000d441e4000182d01031810400b4016110120398075107400d5030f91108825070105550b514507480303050600384000d210009500808940e01030150540050b2202c2007480d00140002482e030010300081c3c00410905062141903101600580042c070880c0000901080181d8880000c00d00c2036010031540c0170304002051281d0006c0207043d00003810307a0345043e03c2d080ba00e000c4074600d030001e0fa51903100d1190041182e208100c01c0740c0001d022143e40003c0c0707031241d800500c45201c040000703000e1f2654650f404002d9000d030320042241c6510020380710105444950050054108224280c01494040400100d0b81400c0c42203c0c007454016280c0200caa4481c0c09100e02 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 49575435 1250 49574185 49574221
    0x501020c0703061a150c150c0408010614010203041205030403080a320306040903031107080405030f03030f1303020c030a030305060f060c1c091d0601030b0402090f0f01020111030a06080607020a0b 86
    0x1b1602640481c034072000c2615280901c91004032000030749031030400c07104a084840c60781203001121b42000703d105031aa0000140c40488040c001d082c511610207107000c03400c6006940c00104155004965006296040b5030000b05103c9802d50400803200610701079003001c0860301c181701d89201d080000c10420f0400e81c01984ea030790700900f001310341c0088250b41c01c00f003640107041c00d850140c4007007028401d602e0248401485149400d000310f0850411100c403007255080908008802d0320102c80450805009100380000f204004040c2e480c0103019040143c003810301111b006202d0019400070a1442c900b01c025500d0007040c8400600c420300000017404242c1c000005414103207d040400000c94501106812400c0c244010f0720803618109200050191480781090703d00c218010702002941d5261301854256480c021600320009075403010042c0c1c01408102036200c0345060000c20440380c00d11640083c0c0894482204443d81652890800c0342c42e030000c0b680c010318100000c00450001150315210403d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 49576685 1250 49575435 49575457
    0x130f020909070825060f02030a03021804020304140d050c060402100e1005120609010302031b0103060b0c0f0c0f0105030a15150215310804030501020c0703061a15 71
    0x14643d119000a4549036a2261508004441e14140420011207403401402014a070a09000400e02101d000e03403207000713407060a03040541c0070030b00201000030600e0809441002500840d0750f400e142c200741c0850407580d201d492541c03041d0f01d0841b100350b00c118100c0355070b540e0740300103400ca40c0c80716800c1100d401c0b207407140c0904111821001c0c8000b541d40710722074030b50b4502c0d03600c5150381c400d002c1c801c18460a10080c1454411001c0000400158034040745c03410880981c4821051140c0c5054010b0f801081300750401000d248010684100100c0c00250740c02c03e0004404c225158000d1403010891080e0070300d402140001e5080c00418480d03140c0750454030301c0711a120005545640c8a05800301c02e0030040414100580c00107200401502282c030f449078121100071000f010490390241461142c514884100c0418001001c84005200581040e10b000c0c5a20100a5540300c505c08e0642d036071840c207070000342c4003a031410400c050320103502e9105102c040b40190580200300c41081c0310b030045422090080e4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 49577935 1250 49576685 49576693
    0x601050403140c09010e0405010e0d0e090a0e0708030c07050307030201090e040302070302031005040209070207150e060409060602070302150903101116051b0105070b010b0a110703060c08130f020909 87
    0x40d5075950310000d80d03000e03002010751b81c0c405240a041581c00d444440e80b800c3c2c1103411a4950084580e48024480300070348040d43d80244640351084003030010a0700c042d83e440c0d00d00071130002180c1d0850100060000445180490381103079101c0c0c0030982c0783c00c000d100090106a40c030030704001c0382004a040641c811b000e40191180740b42d8030740203e402d10102c0120012441e40e0790007008211f1900031009074028090348001c040b070608110007540c807440b044c0055028081c240e082030109581d084115806041d80c0001408840d60f2290b01a40e43c66040c04200c0c07080284a01142a500480069403181f80d4000c0c0201485a280707048140107000c5141100e208403010008803080b04500c0f001e09008030720810081528038580c40c03c45403440d911191300c90400c1001c00c595004075221010050656184514641d034603e00c034002030302c4802400100c0e0859010b0581d0010602c0f1a03a4014150b5600f240c5801c107940e905c105204902500c0d2400040141d2046040703a4054140b070300ca02c0b548061500226 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 49579185 1250 49577935 49577953
    0x1110a0605010b04030c08010504020306180703140106091b09030b0a09020603190608010b0a03120c0c0305010e011508030a03090206040b0d0f0c08040201080f0c040f06030b0103060806060105040314 87
    0x16025100260010899140f000404200f0001c0010142c401480104002c104500701680001c0d00da14010b0181e09011b5085c3c1c0441d680c5590501508004583c4544e2041d0098401050940070f8681d92046241070b03458104140071808001c00d02242c022442d5580c040c609096540c2c10901140217042041c1c25540c0e032040400585400000f107010f02c403140151400c1841c20400d01c010355001d600900b810b6410080e80480c02e4941001c100107480e44044800b84141e218642100d13035030300341c0c40080e00442c1d10b18000024494194000040641980000d0203030340c0040454084a28140c801c110559008100802066100c0e90003014030703c7c40102603034a8190381f007030041c0103500443c4100c0300407550341d07036230310b40210061003185640c0c0d0540c10400840d01e400c1c3c00103048120018518500d21407100002840c46007000c08079030140805841c040401c64903400028018465841d000340030070702d00080842c600c0400550248200c6050751610329050035660740c6076804441c0800f128151041940c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 49580435 1250 49579185 49579193
    0x1207031803030905060a060b0412060e1e010b150a08060111030a0905040513170c1c1116030503030114010c020603041113020405010e040e0f01050f090d0e0303070201110a 75
    0x551424a00954021440d01c0309801c086081c00c001801c007502ca02d1607e50100003611264094504581c445140034884500505003080070304070010001c4d541d03005121000341d01440c40c0e1801c0a0003203141c0c0082250141400034009100e036125690750000d0f20501c5050481c07072160022035403000040c03504007100320f01030700610324640240c0c4c9036802040007a80140314605140c800d10354000c4000b44220b070a101c4903102c0380a00d86252462142443c80024200804075080000380c0c5803583c1d1100703000b602101e00720002c0900c0540c09011b00030b0b008a4400c1301030000ba4044420580340c106c400342d0705c0d41c2d00c0c06080f00039655200301a141801002c80048000d6651403025600c19401800d519043d000a1010803540643c10081400c00310700c140020300142e613000f804145264001d641c00104d1600c1590802c0c40e1122201c410509582018100032400c072191815901510b003440c11030740c90781e61168090b80c3c00ea8403030b44925010761051043c038026601c180e02c98104c10101034195034400d85c540d11 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 49581685 1250 49580435 49580471
    0x120a0c020a0b04080d0e06010b07020f03120304051b030c01020615030a050f030408070b042709080703020d0e0612060d0804080d0201060302030c0a0e130501060b0c0f16030503120703 80
    0x150a40d03403075001084843d40221680684055043c0c0540a0700307066040127408521070048a0f0042c0c0503c122600341d00464900708503c7c0c0076030880e046100c0d00d03440c161500b80d81d203840601014102070000590400c0a0400048144c40348030160080c4c0780c4e540d1443e1401031095860130081d9814072a5400e13400104a0038819089401045409150303150f007007c2c040ca140824039070144411420400040000e00b5000d00070a910386408000d8844c403400320a00742c1d0140540e0f43e800340c000400028035108254002402246020300c40e00e90402c00c48150701007100b9401020101011030344000d0000f5083e24101000c0f0481510441300d840c10542c6403008146071002c016204030150795241000e200b585400c1050411807501103c00021260402a898407204030140480340051490048031040000a401030005800d1103180300341c451600d400e410b950b9100001450000e07015840b484c1840b10490f102c802d0a49400400071032619400000d59420b42d50014282401c00d0396403c040911404100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 49582935 1250 49581685 49581691
    0xd060f020a0203090a06020304030506180109020406140906060306100e0315100303110607120b01110d0201140a14040b040303020c0a0f05011a130903050c160305070803120a0c020a0b 80
    0x203030055480b160b0071005d0003c2c200854008a01f95030080c481040024400105260f100407040f403404c405400091a0f00d000d03109c81c200c025489400d001d0042100810080550142d6400300d414918941360314041c0480e1384425102250030202d0f2110b40c186250140070310301c080e100060101c40c000750410f04910141c5a003032380c111032100003003031040090544c018100b0306110762000160a0074100100068442e03d034100220700003648840540da13150f03001752400410341d6401c00a441d0502020f600c02402841c2c0c00480c8044003034210003140045100f48036407024125603003043d01d00398499888111305000000c00440c03c240c1c08004050008030305002003a03415104080380b07110643c540c0b60107807d54810803201c00041c0001301101400380c1d034080c01a881541150300006420031941022141c510400221100a01c10b00e580e03056003103081078000c0200e80c01102074508840e168031201da02c0c0c2c420390061200d640c002a003ca4485502503111200b0740045004036881100d1503a1541c28943c011 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 49584185 1250 49582935 49582937
    0x302010c0f02031608040b0c0f06010b0c0a0201210504060c110109020604030303020304020d15060306140609010b030606070c0b04090c05031e0a060513091101171609080604080703030c05180d060f020a 88
    0x10200480c0e40036020082b2501424071001c0c0749040030001c1c8041561051544400b0f13042110b9003128490549114001d2000703a64810018080d84c40e06081510107003600d4940c2d840001d02d28107001414050602c5414036442e4020b02162034640fa50710210301a41000e40b0613644225007084c0720300010082148206103aa4900010540a1460800c442141c1d1850300d03981030b8030340004c20050303583d8440030028103445009501584944455000c1170103809000b50042010b180c80302e020030840c11040c00380c01151054002444001201d0741d08541b140829a15120a00a00c4540c0042540004a05640620101d03c001800d541d5036000458000e00280c61140c1b0507902c00e180401d000c88030f58400d14429007802c22482000c0e00c0b503c00c80c40c80e14000d1014010002d03040c0704241c010321550a8034010400b84084403900d0030141884202684400d00c100c022074940341d04100782601881c00d4600d02d40e6130003103001d01c541464080c0b01008e8110401111110364801c0c05411903102803019080120f26 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 49585435 1250 49584185 49584193
    0x906160614010605030405031e0d020a031407021f0e120403030f0306080303090a0201030504050319050d0f110a030e0a06060b090307050904080304080703020a0b040605040302010c0f02031608040b0c 87
    0x501079220211001030308281c080260800400000c11f0000048401080070140d020b07021038000325020401e8001c009a0480e880d0001600407405941034101c0e0094a23140411502140c880e8102070369242110000720316010700d0002c001652050692009030a2080c16041c1c4020117000d0298035400c1d80300307030400c40c0402c0000a044003070795807612510b07015101d000000c614500b008241d50765984001d030402810151120005020020709200b500d0184003040e940c4102d1350703d4240090440c1c3c001c16420000249481030466404446000c0d0600c0595019401ca2410b0304051086001d0990b40a0b03c2c1a10b102d003041e040b00046551140f40c0082c08260442516040b5800c109070070f2640d180e00051041600b4401d00c40440c44136811250842c1c0c0c0440450369495440c030b400e81c1007a09103030b8007819200d50141044140034850b040644540c1c400d500800c200764415506031010400c4c48008001a4801d00120020a00451140d8181c074040e100840c1001da80f07541c01d48007540b0090365810301e500 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 49586685 1250 49585435 49585451
    0x204090c02010f0b13020a05120114090f0402010f0e0105120108010203101703040620060705070b010801050403020619020405060316030507021b0d020d020409050d14040b070809061606 81
    0x280c284220390b000075007501e052045040d0300c00085e0802e09900d0a0181d042ea00081011405014008032118542000c0d04846550ba580b440c51200b41d00070b445050244020b0f0000951000039000c2a42c400da6050b140c160007146240c00c01c440e4900d400300e9017418003c0420100100380030002c400f5000300010710026035640b410b602c10350440203007940403540030b10034098411922203010041c3c6056403d80e01d4428042d02207078581c4403a008054a04440341e021300024091200e0744000108441401404003000c04d0360fa400e0b46500703d4104940c0640142c12043c003043c610b800780300e01c82c418200c8186025041035100c500203011076000340c03030500c1888440d60104103100e0305400761035880003043c0050801c88069428283c840d40c0000b600c40d1048041450329021581e81003e04a40c0c2030700070f00108081d030024a403181c2d980c91107010f2100420780b80012105108680400c4400340c4d88030341002030a0000d56600c00240c2c1d0449a10a9804403040c4880001d0060407581484400e004190100e0802 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 49587935 1250 49586685 49586687
    0x121e0a091203060e060f04060506120a060f1202101101140105030d14160501061505121605120405070b0a080a0501120201090b0c100e010e0105010803070c030b15040204090c 76
    0x8114180c1106141c14410300300301079841034821302e0384040300342c40125504c26100c000130000d19445d000345074000c03c00714440c1c9485800000d030b42d220340c082c003d00b08607085e01d40170000841401031145481c0a43c000302c1610041c1002e0809030212111800d1034600e91407100041400e4a400016820642e002400100f184d40360410400008500754100a410300a18142d820a1403203412000003c03110018800c004001d4250710200003442d10342c2d116000303440e081000501686c08007801c4411100301601141085e9886444802c2c244055150b161801c511401414803c210050042c0c486024003a00001c5101ca10740060004c11100d680344d96903807520350a51030440d00c041e040071070640603024817100140d0300031001d403040c2c80f251030304a51500c400120092800c42d030101070f20400742c10041d1508102105401c03039003a107400c00d40240714507a2103d074400e59170302271310b20058850f0082c54810808214941c0c18590031400003c4171090740b00d4070300046001da9009902c6030341c0072503643e184d9110803 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 49589185 1250 49587935 49587953
    0x91a18010f0509190807051902120606010e19050d0f05060f0c070201050d0e0f0d0201060e04020f040c02101a0103271205070f0b040501050c0c03121e0a09 68
    0x421501ca410425801d185014643c1e5202c1200740c06207108500c1c58441c04d005408054a140b1603000301150302c00d50180c0c0411991003054030f0124002c04e07242c40d600741d84080100c0c40e10310800042e9211480143c102040000d00c41c0350700c0f049044021004000300315621aa062950711501400d50041d03404624546a49844002081225502031950034070410300080c07422102c030342c1d40900e4013070384440300500d000008110381c05440d50144a00c1042a0780c414001c10809881e4140360000c1001740d54801084168031000c039002944030740520060106450076a01c00c081000c46803044030203501d42000300c0401c4070354141182c680600c0c07940c4210500d681c98000e000141c0c400c0d40502306d4540d100c4400c0340c002050b0000080007010b240b04440c0d50b03140f042c002d4a1300d0640004004040100a080c1403140c00b02c00d80e8142c03007950a1500181e1071014250440f00d83da081580250f103080000b072031512205801400600103200b030900c0300d2086a00954119020b001800000510090355250407007003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 49590435 1250 49589185 49589201
    0xa0806150906100c0204020d1d060702070603110904020706060b07030908120720030f0a080304060b030f1b010c02090109020a08070201180303090c030803090d090f0b030109091a1801 80
    0x4150300c3c10381d1151103141d0048004071840d0f81903a02503200c0100c81b003182c1c090302030011030702100d4440ca5540c80b20f80f100020070b42e005a4540d02514509038803604128140e40200c0700780400b040e8100103403140c0741403ea0003050030034000d0000103007103516005103462640c8141c00690001e14000024460b03414103100f20000444c08012140c58040380381e0799291003080402d1171000c4100800c04002c0103481c1400561076003144c1c42c7c144d030104400b0b4034000c59941c00641c0e081e40c00c0d500e0543c0040d0325050000c1c004018441c00d10041040c100800610900403d03405034460402c124104680c0058540151350307406010002c50160f29400700d89001004002c1c0200104116070500d5400b4400012040c03d1422030354162401103107000043c10443d1000025510003020600001301704030840402281450201c0900c0c2d80c0c60014590b40c1565010484d0f190044903201c07a020001007100d11601e501c6541003521903a509214044640780100d007100d02101c41c4684284a003a215005039020b1181c061 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 49591685 1250 49590435 49590439
    0x2071a010f08030406090302010c050c030601060c11040506030c120111070c03060b010306051f050f030412080f060604090f0905010e06100506040f0302040b030f03030103060c32090a0806150906 85
    0x4141303031610700c000307040d45811300c80681400003c01c03203a800e0107401c2c80300c030310014400f42c01c40d010340d6544c1200400d607184a442c1611590740044c014400303031405010742409020010b00420414244804100407002c3c1042c207141159640c890142e0364401030000707008420b00450b1920003003480c600b8000300795122481f240341007601d000300138000c0d6522507a1038400e40304506c0411050303a62554041e01c443c410b10818071900c03140031081008124014000010040c0c26a6500d8103644481c2801c1040301c1007600c441d644071000b4001070104020301d5010b0104030f4640c0038042140007031500e03010300311072458807006820340010040140035890240030704000d11041e501d440c44c1900e4a401c0320010070300f03400024402c0740c44005c0c91a0310b560800039540e1280401003680e540e03507543c1c6031050042100e14401404642440784401617550034098110310103108070740e60207000b1060b01201d449540406c00482e4031902c01d100c0421510002c00c00d151044850b0114500c0020209041000380b050040401d4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 49592935 1250 49591685 49591687
    0x15010602010e060106030c141605010e060c071509021002070906080f030702090402040212010902040302040501061e0c0201051905090f0d0f060f0b0402030403030c03110301052202071a010f0803 85
    0x30304030382c00507095044074042d10740010390b42c82d95a001c507a60407a42c01085602e150114440c0354604002c082d000c0114403d80c004c01403042c0a24180d5255441143d0a44200c10144081030206c1c184d4200713004180c0040c40006506101c9500240b440180d2200e03100c01031344500010b008001c0240304140c0070b4500304008003510010310264136500e01c1041d5000313011b40748c002c02141c01c54490b0340584c0c03032707000314580404415070311092100000c0d0030030b00c4180d124a041400000c2c1c1030b03001c5d00e100300c02008410009180c90542240030780703482c00845001c9040100c204454982d00c0c083c0b0243c4034480c11107a440540d075002c0802003004402150350340303921901c40070103044001035290844026450b80440041641c40c51400080c0007440801055600030340004200004c16905030710000c1c80700707161744081207504a52045604540000d0107602e8102803240c01c44d4030050440d5000f100d21781d0409401503d040302942e119501907841c2807c404001c14800014802e096100070704a000c0e1403040000c0d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 49594185 1250 49592935 49592951
    0x30911150306041413150b04020318100b09040609030905130204030201031b051e09031b01030f060e07050705030c0f062502060109020702040905060916050d0203032a0d021501060201 80
    0x40000002005001020041003106544060050741c1051051f040001d000310f40740e00d0a540d555070242e81c22005940d0a00a4050080713841071316114140c000c040c0507105140c65039a6607103680c0100004d28094041c491000b0340028113070360704100d0f0702c4041c07044000541c540f880d500c0054162810107100c22103a148000420340e190384d01006807504d8030803026014800e9441a50803204034070a45149039058000c90030100154940c14462071540c1c1401ea804001e00e2000110042c1110200c0c001c1c9244156402c010405903841030015000c3d10b40101c0a40307203040f1003a580c841c500203002581e496240c106d00200010740c91000c507065211740114040e00c500d0310101c04001d48512050042000740e0f0b501007203510070b40d103d40c1d1001a1450380001281c0c51070514444a50b62002c180a01d130306403031595803011807203080c0701180d50281030b409070045080180880e8403d95000c011290840c070761641804103048020100f1056640e80c1a5070080d00720198070174002c404101058004406580c141129 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 49595435 1250 49594185 49594201
    0x30614030111030a0203040c080f0102030103110d170a1b050607030c050a020a0215070f11030610050108040b07050f03040602031e040f0b0718080601050a090b0603070309111503060414 81
    0x1284d9010305034030310041e540d036141d28218207481d080da0402656445241c0814220070015401103068030b01403d0300682104501017003180403550400c00070311000c0c441079203035101d000b042c020300003c0d000c90510b8107490303e614611038a0b0070070400058030039902000c140a40503415100d40208560300d0710b4800d2402001c800080d650309a1404028065000e00044411100100b81991601540320411101c40c600e00e0801402e9071140b0001c0f01d10a0196802090400c060401500c08540301a120008c3c85d075501e403a6106440002416041406010064100c0b00411040150310480c8038503001038507800c080c41c0c440b510740340c0b0700c1d050001a500302042c0008107145d1070301191140c3d4416101c9180d0b40d69440201e455803030f00c12035030f410298800070109484801241c901d0503500160350b400090351340d4418a0007601c0f01c250150b5003100301040403410381417081e003240311b101d40180d080071204402000440c6191080c541c090350594004004c0c4641490580205100e8481d501242080350034001c407 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 49596685 1250 49595435 49595437
    0x709030c0e07020705060d0c0e0a08100b0301090c0303050d050f01120803071107082b090b030a020f0a0c0201031410090e011d0a030f11100b040902030607030614030111 74
    0x803085091aa01c0000b000c1910030008100a41405400030b5220070682443c8009000704000030b0b00895545d01c41402c0c14100b4248007800c8a0010004112074458404010006c0c080102a04d815549424101c40400c2544070603c00a500c0f030fa07560b40d62004850318400481303078080d01811034010400b004111403c000784106880710b0300b08402c2035807a00c40c1c11301a5000b050203084140540500ca00002d0070342e9003c2034078900740e0004909000f202c4000f80c41d410b41a03079400310803c08030396417010034410410780401656000c0800b40c001032800a013400a089240c11104d480c80005000c40210b20031568075014203889501540404092410000c1d81c04d82208840c0c018001c01030345c1d031005020340460940049888a061524601440c03a80c640c106440d046103e80c1540805c801d5088084c0c06407003000300e4542e14142401610200710a43d05640180451903d115885616a0854030150341c082c011980919840e0302d00145140c03904e0320300c0c01280b140c4281c003486a41b422404c2d11141a4100c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 49597935 1250 49596685 49596689
    0x605090405060301021b0708010e0307120c0c0801051515070b012102040905010204080c06120f040c0305031306030e03040302030c040504050a0b0103060203070e0f03030703030914190b0709030c 85
    0x4902044942d1a40082030080c02174411410f9100784507600c421307840d44040707084416600003c0c000e0004040c0c0d0001c0c1340c0e0b0380c442c0360310080860411564039410103105160b02050144030711031443c22181c1e40d007045802c0d03c1007030700c62000320714101103002c1d0750345032808140348514190140309041251507100c0d1032010f50144102c2c5040a0010381c0029000c202c03e441e20400c0b907004108005000031818164002d4002d0301400341c1a01c11400c41d40c0440c80d0038800c0c0c0b0b408c201e80008441455489207896110058054411101c0401d9030001200055080c005011798451902c540c00446150510040c182c0c0d49039160654244c104001c02c2c400b40c0c0f004107001c0b038000000d5501107115161460018980105008003410769840140084208a1203070001c50140d4042d03580d5692228210040001081c1d500f4100d03949503004000160000740213410002406000e45d14407043c840610380802d05040764800155540124045c8030790410400070902504092546002c1036410f040d5504c0c0405a0614 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 49599185 1250 49597935 49597939
    0x2120307030230070311130b070209010902030408031303030207060c020c01090501080915180105011d06030102090604170705040e0d030e0f0303010513060f03030306180b010f0309061b02071d01060509 88
    0x384503891600126502150100300c1c2c100d0101300740139640c1034420682d800140082f4408c021260002031030411034001d0702e0103240c000d42c40d5451501d07131544000034405541d100b20306060b024000740000c24543d00c070b111826032103a009041d602e1801400103004400a0304030905000102c0240101c44a0016007052440000400071030315407240f1419a9500b039251800c00c1040d820a00085100c03200340600d041c68010141c0b56072566160b0008050a17405903600d0240c0081040c802000340c182041904500307900c076102550403180e00c840c0482c00b41d4402040c0132400f0f80c000c0024840556240c401d9035484064038015011400c03020103002d45034403043c86024480d080101841841c18544e0340721900400c8124205610300d50359160147c003901403845004000c4840d240100300b400918011080b0110f030513540c0000409400d00c094006000c1c8080a54400e945c0d11041c8200552034003944c0320b803140c3c43d002444001c1c505885650691490090020306140308001002681e4001e0140c178a10301003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 49600435 1250 49599185 49599191
    0x3061002100c09060816050723100203061008100e06032b17090d05030907080304080a050613050a080304080c010f09060609062301021203070302300703 67
    0x140804034a0300402014031464240740c52076214001d5004241007007220810344880c002503849504552103401c950640101051302003010302d0010303131100c021034042d8030410001c070304e4004a44280c2c0e04d011549003041e81c416a0000c02c1c040145130512542000d40454a0710100500d45050050b003c401e4030302c2440012090180880d15554080c07001c1c4258940c100c298606200c16924200303a50040c01d00c601c40850b10b00d180f0445003a41c80ca030114401d50101c4000d00b55014001e5007181c5581c00104036581c2e9024002c0d000c00c041e00103000800003441e00300014180c48241e41003181c100031000e08032035041c80c03115134954006040071840501458000b50003a80ba03a555042c12440c61046e140d00d0074280d480d08003d11924001035100746401c41c0521020403443c1d8403031020b0070031100c250107200c000541441e801d000c20700d88064004000700062054510740700d01040000c001e6002900c100c00400d0b00412180480ea070207072101111034600e4140507541c143e2806048036010b4002c0c03c10070805403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 49601685 1250 49600435 49600459
    0x11205030d0f0b0d030305040210080f0f040503040801060603060e09010b01140c0703141501080102090112180c240801050f01030c020726010b030606060a0f090902030a091103010903050306 83
    0x40b00c0e0f100c0ca200c0e040240500312450120319004004010898080340300e11580328055902a03c60340b0080d01c141d034581c1d1111704945802000c0c824200000384100d416102c10000824424001c0c05078000800f1640c80c04604141040c4000c000c8c20b800424030000d5a00d40158081c550782d000001c4070b5100380c02e1050715501c0072035a1600381001c40641020340442c50039100303409640c500051031481e4101d40c443c6110381d81d80b01c01c0c80b2820b0344240c0c000340b8001510818105e52000f0107900c4001d08010305c264000316a8aa5a6085450307041a03208108441c0010705514210f00c0c0c8041517a1a2825450a11079a40c14032000641c0081a401140d0406559030f806282079402000044041c101c0e1860084061841c7e84130020f910380c1c0720f0f050f410f81c2d50034640b0381000e038180000d20a00500004003501e0a285124104170358440d5030268420400551240004e6203044901c0214094455880040f54055250820090061001c2c206a01981c5041018000310342c0c024166600010202c81c8507a01903 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 49602935 1250 49601685 49601711
    0xa210b0d02090a020405100f030e07060807140d05010618080105100324090602090f030f06010603020a020319020706030c020610091e110301030506090a17030615130e011205030d 78
    0x40216000280c0210385500b01f86d00d240d0f04900a16034502250303600388030380c000c100002515410070303216041c040b070441030205610328000c03401c0002001d008407885040038400e00c0c900c4c3c10344a00707a2107900412415180b459801e6401d140200192441400900c211304004035680143c001034400a032812079540b2015848000e90a40b00113102c600c402e05100d08545070510000962018080500c6030b200c4050750a81d80c240890503001c0191f071603010b08026880d0000c01d401951000704013200b1404200810005164001c0c04841085142c0c2c0c001c10005080440c0a011116810161410341d4001820002d601200c005048150342000c140030ac1d80d00b0070344031607032001c00318246545110707410003844400c0304901d10044c5040728058030031102d2903164015030548a125001010b840d4180b120029900d100b00c41005581208025200c1a21006e4140a42c0c03465003117100010604002d0f60410040340483c448243e0241902004003003c4207816501c09644c1d20521030000c602c1912050080c20704c0d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 49604185 1250 49602935 49602937
    0x70e130201120e011505030c012304080609060912040e06010c060b180906101208090a0b0304050307030e0a050d0311011112010609090b01081513020a210b0d02090a02 73
    0x451068005000d02402ca503c0d203400313030414988000c0050416080015680343c0090907408469040c0c50303550b155000380c40c5040c0c11a00a0b030120034906000c20000980c20010041d01c0d22440340f4001600c2a814007440316810306514000c03400c90088140000e028600e0303255145078010f5030908003542c0c100840e1410f400030308080c0003200d5018140c102090f03004101c00700080c0c400c40c0031906a884940e60409c2c03000390110280078104e10020300080c100c1c00150404000c2601030001059032081c2507031451260f800350300c11a800c07501070b0004a580c404140d004042d80900890451b110b060f80b90402c07000c13510b80501c0c2c52015041103204201d07400151402e501c1600c007607425007a4180e60301400b18189000600030310411000403440030000a0344c01c03080c49079420748001651800469201d4443c4104407080140d1219813010003400c000c40074011900c01001c1100041e110b04542010181200c0c0c10306100003519100241030001d01d040641d5a201c00e241c01d036904550008103a201c4054080007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 49605435 1250 49604185 49604207
    0xe040f02030a0b030c030d090b070f0503041202090a060303021c0e031b090906152e0315060212041a04080706020105040c06030e0d0302180415030b09070e130201 71
    0x22092000041c001454a07a40100c258280141d08881090700b0050034103075180e580701b0341c5400241c4103110500c5981001e4000f09001c5000d80c20345507a0394000e8544508640c03095000d100f40e8145d42d840fa03001c600380b1013400d941c0104030480810000b4616140070b0344410074511038040101545500512050158241c0b0710700c0d8101408454040c841920081c3c00205010012407282280720005007601c4000107a10784103800c0150650020740e0030300140002c40032925445020001081c0c00c3c90340c0344040e03030411040f102c038554020580603410a0001c0c1581d100f60800c0303046400c500c46003180b01d950142220200c3e02801c0c90790001d206501d00422a6001d290815581070007180000185680d054110f24040c6000c0c00d20b00c500580c1e07501c400d6003224400d42103000d20f81c02c015581c140040c0070f039028090041040c0310704a02c026440c0c00050440360900010700310344401610a0041c8180710300355543c0080c6a10040c49a581800038041020740d00402000c001495014101d04591103a520038034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 49606685 1250 49605435 49605461
    0x1090c0506090301060306050c030403021606050a0c0c150801050909030a0c020f030f0304030302010c020c0603150405060105090409050a060f180609150603080c0d030b0f01030506040b0d0f03020105090a0209070e04 94
    0x1541c03c049d5110851030b40b00381c5d0254010720501650280001110300c0c1c200850741c45440743e034a448005c00b030540e507103040c901c0161284800d85100149407c1990000c0c0c464460b03e9032411620740c1000c00300400340001401c10301d05944113100b03d040c16504801d02d8610750341c044800400c03050f8003200082c0382c511030130902e104c01d0102240c004109601504221200d00180e02507880100d100b10a219941c0011900b54440660b05141120340d42819404650095010700d095498145480003080030f031850b641040311309030b20500d0b221003480164402d201c0b5444590100f40103042099092040020301c035240a45001c1c1e65952131420440d818032000c1c04809460403d2104035036038200844607822502000d003541c0500c0c041144501d100b0b10815400780002002c11045c1c04060303004400500d0010a40c0c1d800c10b41ea000310a00c0355a400d0364000c901c3d0b00c50f0380c41e05074504080c94020300350350002d0608045640000650001030341d4028145500404030f141040c050031140300002d000d000445200360f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 49607935 1250 49606685 49606691
    0x50d030c111806040914030f04140d03050405060a030f0510260304060e0409020d06020a0f0503010f0b090d060510080706080f0a0903050c070603050a060801090c0506090301060306 79
    0x1010550400301040c49a409081c0c5210646a103200b032110556104019428400e00307000058510301d000da0104c1011409014400a1000411002c915690100e0311450b4040c90200c1d0030010206440d032003480b407100580d2507002e2020f01d075901a005003e82c0c001c20b03102d040045080d40009102e5442a9002101e452060200e801c0c105080d5500741c941c0c1c017030800030600c0410b0156102e083d14a0420036a003058008516240c1340c001c08884c040c0200c001154000d464281c1080581e5415032200c0c0541c1c041c50303005944203d02c50340544440f00a540300400c0c802c0034070042110070180c60307013039048882004c505a83c1d5081c080000b00c071030342c02460051859103808241314180841c243c5c01000d403204841110700064a42005866040301100c3c43d0070040c411100240300210a900840d8802d48603040c814280700b14961101d0901e00c454118400082d61541044030900d40e902540000700b42c0c00008000080c019201c013a2030282c04d010300ea000d2140040c000a69031025803142c07000f150007140030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 49609185 1250 49607935 49607959
    0x1060309080d06120b09030a08041101021207050d080106090f03020d03090b12060a09020c0a110105040b04170d090b370507051c0c0b0a060e07020f010f0c050d02031005 74
    0x113a000011404041d42c074810441e001540e0300381c0c00411128050380540b503010b0142c0c0c0750b40da129019030300d41800a0440c0528090380403002d00b000c0280c001188580c001d000e61850729030b0000d1001c0d45c142c0c015410010b0030340741000b8000050030000156601a2a20f180300d2680e1700381900c00c00041d40c8262224040011a144035400480085004040c2140c031019140d0341d4041102c26802200044c0700281c000307040d1100001c42415904000c103006051081c101a6510380c115060340141d40925a00440c601d2140100710050118002c21440c5003041d03d0f0f41c0d400d184104c1494000c205480c0d880224001c0100c206030b15000c41082d900045024805401ea42c02000400e103804c00b11080302c5520900014020254000c0c441001000c2c0c0b030340d540c051840d0180c42d15030907a14050419508070340c0d50310340850304410303c034060761040249030010120050300c40a00c0d421078420b203d031207014900d002554001d19910404581c0c070b40c2c84004016840b81c548072111880e43e903c5600003980500740740c0030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 49610435 1250 49609185 49609199
    0x304030507240b01020f01051b0903120f030a110304030f030c0905060a020102250b040201081302041805060a09031b02010e0d05010507121104030b0405030c01050c0c0d09050901060309080d06 84
    0x403d00d1014800c3c1e00341e6458054030301d00c850036600d05464110207011009210140b03419400c000d007560041c000c04803500b107200008411540c0d44420003c18400784000100031210b0160b0081c100900000c8405a20754034058a0050131815020030b400c080548170446020700d20b103d60740e030170050310000781100ea440a01c140c0c00781c002d502081c4428109596540c0026281030709901c040704a6400070b209035110307611035004440d1903000900b04999107a81104034005a2114443d280712401905911040c440c26130601500c5c004004185003101400c1150000c00a54004080c015a84018842a11100c02c620041c2e0f00e058414078244d400c042c03500040014824150820b50051407552103814217804c480001a058460350b103058425034408101c02c100088040ea01a58418007a2060b2800d11611840d8503080d40c1c0b0a9135007040754a8003080400d03424405100e21201c42c1d102e4140141c40c9454500810008041441842d00307041d6100606d1f0148807402040b6402185498000c01c0869203900c6 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 49611685 1250 49610435 49610441
    0x203040906080703020303090613030b090604020a270b03120c0304091104060c030c031403091f0605030604020d020102012406120905101d0709240b030403050724 71
    0x20800c0c0200382841d10002e2140c030086468000e03250058051880c003003844013400219401100480091400340c0c0700017000c07610858440340070b9170b480c03000351847d800c1c1401001094842d540080046086405168920383c04240f00c807200400261800700c4c1d0710100304002401d08041d18408651007400040ca0144c8090204c0204152001b1a00800c200c1107101c9a51903680101e000c3c00c000b2840c120103c00210b80521210003800d4800d14000c180051000607800c40d5403c01d441c96501b6a22010b0381d6202d0340c051418505a080324a1010490b4500d0300380041d6942500ae4000b90003040200300c0d6000b035900c01c1d04010f41c00f070200382c2400f03c00740704070020b8040c4103594401e442c00580c009900c4081c80c90140640150300f500040107001c00716901c40c203540100000b500103480616010000394106009001d032000030064002d00040c00a44140b012480d54082c501c1d1140c908005901400070010310000d6030b40054040c0b800381d0302c6886920f0011119040c405000c0d80301a140d2a041c414901a50 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 49612935 1250 49611685 49611689
    0x40905030403120e0303040605030c0910020a0c050111030a0e030f0303091b010207032301060e01140901090501030c0b030a14010308091306050102031914070308090609030a0203070206030402040b030d020304 91
    0x6940306882030200f010413100500c0301809a80c0c150001c000802c00a4410b402940c1c00c0300c54100d03620300d040c40b48400078a040e51081c1e503d10168005c400b207403060008020600008002c203080205d50f441608000701d40307921445002c3c005101e9007107003402c13050302c003000034400c03090360901102d5803401c0194100340d64a122036036540940180c2c2c28400c00551012940e07a007280c0e03100c4050202000d403040d0b501c135001e03072455640f4101c0d0340e1484005140d102a841141c000d040704502140000181010310201c0d40050300119987c1d400e00c801000054106040401210700802c00c05480e0b80341c98070070101070941c10301d401a41d055000008003e2090ba500144204401180c61150322100c105020302510200d1040a0140c1c105000d074102000ca00c4040d0386200328245848450f4046655064815800c03503007080c0c002030f032002c00f0402921401c0040c103410030400401503051104406e0700a40ea8030542030028025600400450b045407034079040041039a8004043e06c50032510707110002d640b50003038 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 49614185 1250 49612935 49612943
    0xe060f091e0c06031f15050315060930011107020402160506010e061201090c0b1c050f060301060803130506180603070c0c050d03090306020708040b0a020c0109060302030c16020f040905030403 84
    0x158174000755017061605613840e040c2c000e848036400c40d95902544c40301d002140000a4010780c0070800a0420340d10341d140e0781040d03414480b003c064417100035030351900c140c005240111980e00d0500800490600c2c0c1095405507a8100e40c003503a101c440d641d1030300d0700209072075005090b80b0841002054444080c3c40745841054252040034041400301e00003401c0e128100001b078005606c0d800244500e0000740c004004022400282d040c1010004181700c00325030044454113291500c503010f011082c5401e0040d0740c02841140c0040d428102603590a26003554107103d1680320b0a000542031500c5d200900402e2880c0d40014a510386a1510100c081c00510300c540c0c0496417000d120780041000c0c50881c0d42c1c0311013160103580301c1075494116a2031030000e40c0140e07070580304100c06200c001100440e24008203500b000d254003410310b0070680c400140039104c1c10780010b01898018000c00220204c61402c0d51001603416100404441c4140041048002c03950f440503009030a014000090050010040c000c0b08c1c81 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 49615435 1250 49614185 49614241
    0xb070903050d0c0317130f03031d1605040e120304050709060b0307090503070b070605090c04060308041707061b06060803040b0711040b21070e0403030e060f091e0c0603 74
    0x81e400c0541d845c02203480b90b00940c1c02c56000381c0810004410001c0c2c0e14864140040d602020b80320f61112030711702800100140e401164110b041d0260240700c200181402d403030030b00c8101d034003e11441e07d0364814074003965034407008000a018400704000942c01400f107217404015481d2280300002c1194401c5070342002181400c6000030325030400080400484299414090600b810703943d0f000c014240141941075684550034480e003081da51442074100541c41100c01340c1d607584c504541c83c80c141080e5201c044240e0407081c0104081038000e0107090800402000c280780300603080c50080010070442e0050101c0c0e10011401040144034000105462406030000928000300101000140c40f44202400d0300f02030140c01c00e0182070100640321914448500644031401e8903440361040c10300e4200e03000d5000a03120469842c00101c14010b640c0c0013a12445510103d00e05001c68a54405022400050070300444130741d0490340c03105000c0c0303042500c0000c0c2041c0c1d40f410810302c020040081f2407150300032581 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 49616685 1250 49615435 49615457
    0x712030519090e1501050408070b0702011d090705090315010806060a05240f040b07030309141605091807030f1110140706020910080a110403020307030b070903050d0c03 74
    0x1004403031034001c0f2036440740e45040d5030742c801001400b69107100c1c0384a4140b1505100100300314205001100141650302c000e2900c03426503000040207510100310050300c12401e40005a1540ca800b107020b90b22211500b00706a40c1c4d15003601003403a2113020201441c1080d0000c001260603040072a481e80561403c540b0700090545403010440b0b20650200360a1001d142e03480081c0c5001c90041c003605888400d05072090801e691001c2514071507001d0541140003da445010004004294280c00064815440104000a4800760854840c3c0c071340d0041c00c0c07041417070000040110f80d844140c1c081c03450540090f0f451156403443c5c00f4030030783c038601c2003100c0e0a251a1844006c90910382d40320701c3c1071880707959411200d032001008101c003544010820348500d0303001c1040364015254200d0305941800d00b665401c110786421b4003550100c8105084046a030001000f0070009a9070014604040d04d40140210100340c440c001d00b5100c09030168001446400340e002c6d42950290065540750101d80a41c0340d56205d40 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 49617935 1250 49616685 49616687
    0x604020310020f04050d020a0314070e0c0a050a03091103071403070605031003030e0406030204112814090406170d0201050603060103020a0603180212010f0f020304080403030804050712030519 84
    0x1018002c000c180110f0f003030008004603d0301e4003040c45883d001a204220303160704e0752100048804800c0b62000260300c05101048848400401154050f80310020b0380e0900740340220041c01031050340c01c0c6c04c04064440d6290014025607410015160341c004080f84e50a42ea1114400d011065034010544a40984000080c0980c058001c0f60b1040080c0c0700b002802c0350031590280c40d0704010303c5003d41c210f59550404401130b126441590702d80fa0f00c02c650070f42c4840c5070f490b48103d0a00c40b0090050720915070050045c540303070070020342900c10034140e940d551281c1061010a00400060f8131040f18038a80c203050fa821a0004a0309005042c0c0e01d038020300036a910740d03041c1a90b400e000e100080d08401c0da0101084400d201c7d52001d045200b00c2c0241c0d400c24212500000c3e43d20148038144111650368026115404500d84903d07200c90805440a606502d0580c071010300d40e00940c4009400c1c4555840000c040000501881001e0300c0e000c3c1000000c1c801d03900300100076410040f004000040040300011280b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 49619185 1250 49617935 49617937
    0xc1605010302040608060d032f121602010c05010905010606080a0b01030903020c13110d02031603090b0601080403050903010908090a06080f0f0402030a06020c06011a0702150a050c100f14040b0105040b010e0909060402031002 98
    0x202c81cbc2d081000104042e030044500001e02041580c06542c0c3d010301c0c00000c2e00038000c01005011a40c1c07154400d0822011840031034019640150501d8a031140002c0001d401140003000c00100301c602e0368128600c510030700007405503250303a040d00810005100d64a10155400b560190607443c0d01c80e211a040c11105400303c5440c4003016060716484000100250310421000b0343c024420700d0070504013800701020030300791150508c0840c0c8005000c0340b00d42380307410000d40810003000945890384d414202209042c035030031005030175a401c15a4000003e020341d20104006280d641d840801150341c0c0948070074a640b180c0c0c00b13000b400c1075041c0700142c0480c400704030b809844002c1d40081060106400079074106910303034050f030b0040042c004103000c00305101006004c00746145c4540000403c003904d080300c035002200c1c1c448402108141c540300c107003c041030f00c1480c1c007815180700b50340c00140c0e110303c0c0b00140d41c8c5a901c84c0049038401844801c000d40c2043c00b081e9140120b00c264129200314450340740d0001a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 49620435 1250 49619185 49619197
    0x20a08060d0f0f03120c02060108010507030c080606090d0f0602030402100504141e0a060309060c020a08180d06020c010e150c070215070203030c1605010302040608060d032f12 77
    0x6207000b0200160200c1e04100c00d03104a24803a08000300c1c820951080351043d02d803065820800340e0041c8004100410080c064240d001e48249404c1000310042c92014012703400c0601a14041d11001c01e030f49036281c5171040252074654101e00c4840d1400d5035440e000c1d01030361007158102c0c020030751100a451054018070980e0150b64213407141c8400e0461070000d05c41e90030700b054880d002c8101c80621807000794480c4550080035040c241d0b40401c020409042113002d48075240c8001d021503100907500e802064040081c0c40001c80110f021241040ba100006500c1280b0843d000d0009440020560840d60781540160b00c44071038001038480607108001840c00144084840701c00f00e560070805100146041d4050b0802010000c407900e0a046194007c0380c42c5030001561484030b50704c11000d07050700138160400480142400d00e4103616041c10088c004115038030290841d4000c040c598040020580036285c100c1ca20381980040100301050034130120901c81006140000d80c2c0110701401200d011101d0880740 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 49621685 1250 49620435 49620443
    0x1113140a0e01061214090a0201030e06060d0305180301020301122001051803031204050109020307120201050706050601020f1506040b010306051f051201030b040308011706011502160801020a08060d 86
    0xc5a038601001a10213288403000303000d13035541e120003400c24105894101401004500f00400c0340b1102480050b0449061406010250740440d042203400e40d2004001c04040d603140c6000d6444440c0e82006022500141c11000c0d4194000310022070b00120310301c04640d1640c0a646408098a40c8090350200c0103908081d050009000300400d130110050108100205d81019084a24014055506801e60312050728100c606035142d102401c00e62a0402942e000b8004001d0104000d040e180d0001e440e61162903030041c507098503640010301e00d84c0280030030011480400d065030b400744c03038010340c203074030188200d584d1032240d840e081c0c00c1d02c0c0705c1d4442e108000c02e075007014101c0d01c0003502002c500010004015048410040c3c02c004400d0450b4500e04010b000b18400c03004101a81898034000c2c0c00940141c01038010210006a0308509000010307042d41100d015145407644c00500860484c246030106003180c0d042030826030001083d01055006100d41200c0740d4074610103840350741c1040f00305407107850054 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 49622935 1250 49621685 49621709
    0x904050c120114010507150203010806010e0106170601110d0c031101060812030606130e010503190803060d0302100e030c070605090108070e1305040b0a0c1e121113140a 74
    0x2009001c1c9800d424100401c3c1414010f00b00801503598074200001d045440c0201074001c801004030f4202000780c0c0c1d004d0039850406d0003142d8146800180300d42c07180403944040c1400703200420050790160094030340303403980001a100c0700c01000b0300c09020240c950350120001803240b00b0004440c80180704940513987c1c1140034210400c581072101e09540c01c0a07010941c4000c04019003000c07950100701c80c60081008444d801b0b500d43c541400c240c2000800c2c241404940300c92401d042c00140f00100700d941c00388040b00d1403894010203040032843c003010380180030492840c0c507020718841c0c400040a007010400300b50498825944807102180c081c040c00100e00d010824103004140c105020381c00030301e0341840c042c044241c0070f0501410700042d61410303282a11a59a28410b11558a6140c000e01c42850350074180b0810700034240c864414040d8050b503001c410407c3c01d01d181101d00d02582c00c0b040c80d001041804540301d01048490b100d8840c1c03544140c4e803601c19441140300f15420240300b098101e800c0d0f02426 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 49624185 1250 49622935 49622939
    0x11704153b120f0906031e060f010903060c020f0316020906030d020604120c060609060602060f04020a05150d0203010e090f070e07030209030114070905010905180a0908070f080904050c1201 83
    0x5515150800d100d4588103e00500002d00103803984c9024520880500c01d4180c1481d1824464060403040640210301074000411b49089598200c2003000840794040000200c003215880201c1c140100c406400b9418040000d940c402c406409450201860007250ba2884903150241016940c44200d034801016030800343c0040d02140c14540191111200e90800000080c4aa51160103c80369034002d0181646d0300c140034031100340e0402c0320302c1d032010101400d1081820326400142004a9510569100b41a407145440703e80e42d20754262203503d0b81c0b2035810743d02c0356100c5542c14408402103800c5c0c8014801e40c098282418400a0160200d172214245410f141d221800100e0280d031083c8000c9406640350b603001100c940685910920840c1d861b950750b00014201400107180c181540d0119102c1c00406161303042d80e03104030b444181c114520200005001d5024500901903020b0500042c0182c590b0209130418041944002d040c0058103ca08016642d02c1600000080c010003030030903040e42c003403001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 49625435 1250 49624185 49624213
    0x915060906120210020a05070e01030c09020304150f060302060304140105090a150513050d021e01020a0203250203150412050315010806010306080115031a06011704153b 74
    0x21398500d000944107990314442d8135103c0d2403a200d001e0384020050f801900040040c004280c0026000e411000c20951841c03d264540c50361050801340d1300f13441e640d0703a00d800301d480c1035056101400850f0302803c01c40e180d10346424440d10400104028029a50800740003c04d02500440c4804907a0b48c0403088000c080702074a1103e0050100030501c134181c015012020020800400c0382141901d426401401c0c0c890440f640101c41040b2100704a2440c0c0c018411072409a4011082da0b02c0000c070104110541050031400150290701e00e40040d405004d46407900d980c01084c041078034401c9024148501c01d4208800301140e09102c00c655203002664041d2038101c6643c402c101c625048581454045031403030f11110341c82d0071248045820613102c1e011140410800c404404c3c65011003010100d1180c0c01d2a0502c0042c0054801103003da00d0b1002c240d00040801c030003100159400102d0b0342080007080d280c00c02c802c0c0300090101c801d4281419098080f4100701da05400f084d001f030300580c0941213110416039 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 49626685 1250 49625435 49625449
    0x80106080406090501060b03150f06030105010c1b0f08030a03270f050c090112020108011715180a0303020a030e0c21010e0115030b0703020a020d0c050a0609150609061202 75
    0xc104c809540f581c40008181c03040c0c10156000e4040b065480c03400800b40740402c81d4244040d00d0142c040e0601303200401c501d80c1c00c4485009201d4000d5044000a40680903200c041c0010342c01c010480da08079480401c42c4000000500307203015283c0c07030400c141c40b500070451008044000c000c4002000c03640d5800d0000d00503900a8540d58421400c41c2c401c500704400141c0c0c0c1050980299012081045800e4155a80a000380b4010318602c03040303130a1120f618200d075480c0d135040705181400002070004130f49020440f902441548001505444440031039103001006503100860010000b8180340705100a04808505a4840c0000a12498100d04681d410f200100540703401d4410a55031000c241051003828000c007a10b6441c40c5242401260031843c1003030940c0d0002c0c2140c8200b40c0f0500041c08110780006200b505400a41040007080992b1b00e04203161008600b401001207003000d40c81c0b02089241c509841d10300d40e04007024001e00ba140d010401c02c42c1d0840c400c12500e602c0c2480150b0140c200740e8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 49627935 1250 49626685 49626701
    0x8040302010509030313090506031e0a030309030c0b0c1b1506090a090501021b1e060c1b010e01051504020a0207120f0c060e0f0a080a060c020f0d02010615080106080406 74
    0x41d080e60b06120789000d400131b54005580c082d0b13000680301c004114041ca4107016140c88104690b141001c100e00d801d001640e1994203110003401e140d91848a40181030040f041c041032250300c002038011510786407146001d542c000070801c41421002e18010b080f001c40c0420283c1080d0b412411104950b42c1d08410800008800b034620550a555900b0240c0030910a00003840480c80e0300e042e1041741d000380e034600d44c0707030180795010545004542d43d01180c00c2c0d00c0c0824801d8120b5854010030b43c4604c05440000020790b1000c55490f0250f10f004452841270106401561041070650701403071610305448203010584c45002d42e4403005800c41242800b40b02e41d12407616808500800a100c6240e640f5684d01c200070310103402000200d0b0800f07485412925107a400e90789854010b0350551209854802401d66130110000024806034403100c0500d1150b1003084040c44000a900803100c152001c244040e001385001d008104c0d50184a00c1c1d580c5d0b91901603c2124100c0c1c506580ea02859599526840001c0081c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 49629185 1250 49627935 49627939
    0xa110d0b15040b06040902121302090703090201170a0510050a081510030b0c03040b0c120106050d0e011109090108060108120d060b0a1e0206090607050703030603020d0b0108060a02030408040302010509 88
    0x3e00c1d405803a522400d01401c050b201c5010300581e2a002401c2c04075104400800c02c064031868103407840b0050f00d0b8141d609030001701700e04020840322098030040e07502d0885c00601d0038103010424204401c4150310380202e4055803001c004400e01c1c50710746080c44401c50242c000c0b000315030302565201c03502d002521800303540031052045401140e80c0b42d41d905410718034103680e485d051900c0441400b05000100710002e40003010444203903c0d000c4e000c1c071201c042e018140305980610501140700c510004560300300e8075500354079500810021181d008001c1e136980005856034003a100c25000400c090400140ca141616180001032590550301c510b001c03015801210b503042550746643c40008c01d401d01070302402e810840740c2c9a920420350900b06a851503029061034004560062040c0004840080b41e0190864164509a40ea591050909901a00180e44003e4221011041440a100f81c111b03940f4180c4861105556441c0c40da04d6101c2c05030b00043e54045c0141004100410043d80104010084400c1c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 49630435 1250 49629185 49629191
    0xe0109061107030606170f0f0c0d0305120109061a030915072006071205041703090c03070305010b0415080709021308011a0f030703030503010905040501021b0a110d0b1504 75
    0xf00c2e9202000d0f41e0b9154000001003088a00d03510f200c4070706014000562a40300001c0c040942c203456142e55400110000a006800c4000c2120500d4412000c4075003141809403d880d140d60b51300755a0000301109e1080302001107a02d0048402000384008503400765103d10018140c1451007948501601009403040050000010702021007008403241c2c03241221621024048034a08048090302a078804c2510030315444c030f014200400518550181c02940307490001e002d1701c0b0340d600c082c004d1030188002e008950502c51401c0003c08c100054009408240054a05000303c0e05105000e14107416180201c070141d8100310760611480c8010740c05003800407039000d01c80284035a00c207080b41c00c407072403407441c02c4400c030000c0c4045076182441000c5800024095004203900361460710010880d00042c01019803403910390005c10288039003501500d9148880c41c0c8030700000c2c45138101481d5158940d0b4411510b4501a00510031646000d0424805058200b0035050344e5586070162101ca903c0346030b00f625800390b9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 49631685 1250 49630435 49630439
    0x171f0908180103090f0f0507060c1203112203020411030702070902070f0b04030503070914010903020f13020a05030a0c03020a0e0907180801021b0304030f0212010612060501060806010e0109061107 86
    0x1800340b28032005c0750103081c084c5c0b00400300703040160520005030060350a010200911100040400d0340e840240c41041c0780000d03c1802c1c4000052040c4070703030400b4000c031056100a40c201d40180802d40d03011203100b00e42c200850440104a102140000ca4003d40940c204200c01c21000590383c00030068240304201659507910705580d60401034070166015400140080200100207810500c0e40c0081c0001c82401e8030720112030380009224141a000003400350515608100380d45c2c40e01d81812004080304042991a05071111008200d50000c5078066512404c0802d6aa8002d002e88225901307078290b41d942004202c7c09000740700000c000981800c04003c5111011102c00349100a6000944007101c00584d460520000800c0032500101584143c0c3e00f04101c20000102003100324140181d040c3e6424108280460190b0300500712540300303111800c020509801000407540c00301d41a10322680b175401947d00d03610011182c2c8803580003214003060000c407042c07108038054003080b48480008411105516 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 49632935 1250 49631685 49631693
    0x918110301030809090a050f07050d020f0d02030402011202030408070f1103100e0c0103050603030d05091c02070504050c1615061206020d0e060c0a0806010504171f090818010309 78
    0x60300990060700c065102040004d10351400512164204000400c00e00050070031540c0c003000084090030410a004d400940481420410340540707514803c01e800d00d640301d2000c07042d101c001c1d41c07044500320300042c04000d1b14034090050f8426a4025034010b5032003405c2c0029680c0c0c51040c0e5070b032a40f0680b040c1d8030100b091942c2e5941041185042524000041075a492503074032146005d072100c40c5c0c5414141004200190b603180001510340190160790003091948440c0c100b641021507650a005a0364070640341032151680024042c02154019501008284c0e606181e180c02030042c1c0000c1800000403580d14000301c5c1c184d24003c3e00e105d054402c00242c00d903940b921081410000e02c0c040b03031256004a80d0494804040c42100c00305009040902a145440e1100c0e0b200d0f803007184082c00600c552000450b40592046003030303501519451131105001c031440f403a010f5a480d80208446503882a2000300b000000c024001c90f045103521100250800703c0c4e0814104810b000108290b040590b5220260081 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 49634185 1250 49632935 49632937
    0xc16021f0207170a02090c0919030302030304020109090501121209050d1a060a0510030203070306030b04050105090706090f03020607050a0609080a020c060f2a01051906080106030201091811 83
    0x40c65507030000e001c820702d041e00842c1c014074401030410303041d000016a040580c603070340c502c164005910602d07190b941031028006000c1c076079500344189a0055500c0f01204150b0000002c41c0264000d032101144c855803082c200d01520000d001d03060750018109040310014150744e900f42e804c5d07001414100c0391030b620340340866078900412034161502d2204034114202c0c80c3c82c80d202c10360056029036603040900c1c2004007003180940300940e03401c10103600200103a902442a80301c0c1c4d01640c2d03c0035a11456041900b4114040e1109451440160081217000141d9034002d041070070895019403002c81216103103400300711840e000320109407000d00400d01441e000540d1880b95444481c4030388911038481d07459a1000b1726000c1510f29542c043d0b01c00304202d03440c0d54034407020b0f592941c8030525649400c0d600ca00700102d0b07003010003024002c158202000e0204285114280c9200c00d122403004000340780e65401818266425403001a0220310990307018440d081c4024004c48190340300b40c0b030106131290020300700807a07 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 49635435 1250 49634185 49634239
    0x301090803070f140909010e130618020f1909020f0c01090f030f020304050d06050a0e1006061107050907030e0703050a080405040501051914120a05240c1602 69
    0x14501c0c0750324072090b507001864040c51100c500c4206045c038100780c0100e840c04e501030007003203e01c060300e4000440a21280380409440d660100c420300c0b809030500300c524510480c10744202d01c00c0007440001c1c507040c00c20708203486a031003042c0c090085903840c186645000b0b600044690784000410000201403040074014074100c14840c10759402d6060440c24018081c60525501c5000c64008020800c115500d25400400355038001c0b00c0082d0603100c24104400426408032751400038007900b07400076510074556102c6030840d295912400c48007407003c075481d516070005010701d0741c0c0b10300ca031130100780a01d100368031150030300302104210b8186030307200e07110381d0718001e1596401c4440b01c0000805100505041c011980141015250340d00c0c0407200c4100701c00b032110b103405450b08520340c00024106a99802c02c0c500307a1001040261601c3d1452810304a85400d034001c1c90894034100c8100081010308011031080c443e0800d8441241421920204200503121404060740e10046030107004101c0c650010040c1c1c5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 49636685 1250 49635435 49635437
    0x20a210c0807050111060f0118020d14040507060e1e0f0603040b01061407030e012313030507060c030f0f020a080a0e040c110705040b0a08060702070e0f2202030109080307 75
    0x300c078034901000101500505e00011405801101c203000103c1030004541d410746103000c001c00b00302c140b1a41410024010000d000c840706040c0400c034180c0d00280d0707a45d02d02481c054810707200007640b02c401c07d458280740141240c1d0028510102c0140c0c0019044000d02070003801000300141d41080e0340050429081070f1002d69a8410741e2004111161b0000c0c3c03022a0f0341d00c1c000515040c24060780f00074082544c0800f806041c0310500170f084a9258a810031341003d40700106420351240158102000c0d03085007400104c070036100381c020205140e03024100107a00c1ca41d050780c4455070200d0101c411640800d04021300d01c158403982c5400c0000498681c00760588072540d54480a443c1010020082a80c100310694018054107120390035800314040303009420786205407004507007981502d02140e4a420305900c1541c641c0200818003082c10360100340c500413510b495075140200c0e161084501c045d584180c0b4600640000300d002c00e54101d003801d0800408500080c0001007800454807030ba40706030302c200c482c88 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 49637935 1250 49636685 49636693
    0x206070204050f241521090d0e040204030b0c0a05070506071106100303080a110415031401090213051e03100b010909020315010c021201060303200604020a210c08 71
    0xc00c003010711a00401000c08113424501090406038042144807220000c0c2c0b62117403074000b41d28a8080b0201c1c0000a00d9840e9504510a07850220b2107280c540100369482c000286002400030031a1406009032006c1c2c0790030111840300d90312074080e031201ca0390289950800b0b10109011202c00b1075402d0200350f11035005a22641140142c2c0030741d00d810150024040d0b400c100c0040002c0c804a039000c1c2406501245a407000500f0b0740010948007000d001e0381c1d0102080c1c000000080440a0b40340e00300305074100103a50000041d0b40c80c0c2d98494141c0c000d842c10510301503000e10f0100320300e01d4001400e9a9000c1d550641176506c18203140401e0a19a0300e01c1c1e40502561284048109035074844090300044c17030b10750811401d50408d60598012010100640341c10000314210110565841150034140314080c80d008104542d502d240182a40ca00300a20b26401d009941108010400214905104a0f070007440c038403034242000495014070074840d404000b07a507101c9030001c0c0051886d181690203003440c40014 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 49639185 1250 49637935 49637941
    0x606030b010e2503090f12020105010b0a050904050402040b04020d0b030c12100504050312010f0501081302032d0d0507061505090c0d0f06140102070501020303091005040206070204050f 81
    0x100d448920182d1010105410120422031454007000d1181c000c0446a0202c0381c81d807801d54401c40c080e004135403000c1e2483d170743d50b04030408110741080c41030004030841e00248800c2ea40c80201c10190b01800381c0343c1021070020071241c4840d252503030010b0340c014070003840002c4801824012504a8208180b1058501d550702e00030001c0e0b250403c000e0113912000c0750f00900200300c0f5006a40c491200140d4800826241e5000c641004030620507110000404880c40c181503a4560181c0e04011f02d610900d0702140e410000304000201e50500c580c0456000380003401200c0504007103000701302e40402c01200319010001140801d02c01407015500038105a07954030307181c5031213007080c50403200c0c0c5110b41110402c1d0024100180d455000046901403c1300d06101c3d00c074254010250054503019507440840c5180074004101221b880785050441e407003c1c4e00f103880380e58a41006a07964481a107044c21241c2c4130070141c0f1000c2541f40c0100f0750261024107800c5c10440341c0c5d4081415901c00b99a6044060a42020 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 49640291 1106 49639185 49639193
    0x4080409050702060a0b060a050f0c010b060a0c0c0906080c100e030304090c0810260309030d030222050a03170c0a0308060310050c0306010e0319060603 67
    0x305000900e46071078029210141220b01c2d0300d1503460302c00daa1845040a90039104ea050007500c0c2c1914040d89c2c403180c403140741c022194001041d9220741d500e010503100c0d00d001e002d24072a140c0780c201450105141404443c0c156030803030324202e881c0c84002c2041c040d0010300b8a40608017541d08191201b40342c0021510031500c0b08105401d8400013900203400106588521300400441d0364a02e4291118031603020301561900c5101502c07080d45442d115104202d0301d01074280d031085001c413494181c801001c2814001846442d90100354089407444c842c040e440700d50100f107a0071944400520f401c10b80000c0f52401076008c041c0c4135000036042c1546403060502141e203e601c080c81102c0c2407003190301e0000c1100303000701c401b02d02034040c0c03c10b8400e040c0075134041c450042000c1e200c2c507400c55a801f001100c0c2e43d888044c10942c58428600140c001080350310509850381e014039004074181e0b00f9414 = true := by decide +kernel

theorem cover : BRFrame.Cov 49460435 49640291 := by
  have h0 := BRFrame.cov_init 49460435
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49460435 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 49460435 ≤ n) (h2 : n < 49640291) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
