-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5468
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:57:37.050198+00:00
-- url     : https://prove2.me/submissions/015d1457-08b5-426a-aabd-431afd2f7376

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 983273381 ≤ n < 983453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 983274631 1250 983273381 983273411
    0x911120a0501030b090a031d0d02103606050a050f03010b0405010f0c020a05190e04081308070b030112030e0303030405010c0e032803020106030c0e07091d061210 71
    0x140c100c2c0e004044201c40340e00c0741200546c4900b41000018003180c1006903030284d031009400140180c0382c000340f010703034038a42a402080584c008085084009104528a1824100a040f0b00801000340c840203a100300c48040c2000040480c500512007449404031340c8496181c411800c4801d41c41e80614066161b503074410018620390090702603280868031803019031104038425600698240d80041c900d407020340c540000d016060540c03110305400015074100204130504410105070040d4840d10185a880c003514203000d0407424150400c0c956504085010402000020152415100c02201220040d507961800396861084900000e800d0300000c0208002d100040d03011a9016a4948501c1c0b03d11841204060b2500000b80d165280c280b8240d124490003501d400c152501d06110b4000010000c3d225102c200c0000300e56031108030b0b0381c1004010070500079444800c040080204010f060780440d0103c0c65000304420041507140a8000003800d503510b80c2d020001010f15480c3c1c41c05c10407501c98214002 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 983275881 1250 983274631 983274641
    0x90314010209130b0102101109040c020304090e10140f0c03090a0f050a170f070803060f0d1b0e0415020c10111b0a0209010e0921270a0911120a 63
    0x14174090b001e00c0000c0703104200207000300440c004071488641c0c40c1c507680400700300c0200046c1e03500004520061202140140036072142141010001c8018030003070034012100070694001203d00c40000c0340f80b10911680c4040041815040548003a116032a6039400034030502c0e01082c143c01810300700200d180c140910002107a5240080e000b843d100710300303442c01c2d0710f5842640305004541480100c1004441c0209040b40007641d0400030080070032141c074403e10300094074820740c210155072a40180661803000b0142d003000710001c004c422604822881c0c103403a150f0b94912441301102070590009910b90b5041028080d0700c400e260520300400c00c0308003983c290817141d048112048501151205090190000000c00c4044203500030483c01441e03027401d071040317604c0c500508201024460b040504c40451803a0845c03d480550343c8401c07030b40321400b10010b07801d42c0c0b0f400304400c2459813110600d40c18a4949451103400e17034000c007601068503580c131203250449114001c840c203501d945107000c4c043c14081031380203 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 983277131 1250 983275881 983275901
    0xf02090c070b10052202070b0103051609050c0403021203070203070603051b09030a030e010908010f0902041802100807181217031608100b0c0a050d03090309031401020913 75
    0x220406503214a00c260390f040640c004c1c0707035001c1d14802c86010f88a00703414080300020001034001d418040255145c032149442038100316036541000d0844a154020101c9007002080014010321040c18412a00841841180070181c01451080522080110200f0132a41d11542c06012904082d44c0c4881c020000c2c001501d00e003a200c4e483c0540d11062a244c0015a400e0060040203003140c0710141e0703000e480184501c1151814440c1c10312001448044c02c2c400c81d202c1c0c81d410000442c01c0200e41c4104000c03100c07a02e00f10901c40740c110b00c03c0703000340e1a40c40c4c0e141205555030810800a40394100240c1d4004010265010000303041d044c0031a5036903c0030b03004220140704a070b031200380b9031608a801e03800f8001184c2c0c07030000c00a45030901c1d4540d48a10300b907a4104565150300100d00703403034a40e42d41542e407003c40b0b40081c66001c103085100300001040003070031103001403608000000150798010600c8140d840050b00c00d00300c40900081c3c0d03c20139030440300703c030100a00491030142c1c03038025030f0058868508 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 983278381 1250 983277131 983277143
    0x91e1b0705060103050610051e0a0b0403140601050117191803090e0c0c1b061c050f150616020f0409152003040f0c0302030102041205071418040f02090c07 68
    0x2007c111000c1d03414035030b042034560042c8140b8036035041c0c00031000b5403001c0c8240b81e40d0140450f1000501140b0001c024806980221004041c1c8801500070303614142041e40300038100000308086940200c0300982041c1c2040c401c40c00541c0c050a628500340241032000b900403007150603007810804040c3c2203480e0000f01d501c020302c4404d565841031110f020500411144811b2500610740e001f00194075244000c1030b1560080444e414102c1e11000c00190401110a0928a03070741c0d5018007201005000c42240c0c05050100c0c080c04580e04074012502c180a0701c60001c40380080302034543c08654400040f2880801d024104100307210321420403003051140303440780d54403031031400001c80d08421460203204801c190355090a45142c645550345480100c900800352034a0204200c040b0042c0c1d801e00007800284a010502000f220590501904151403980406400c061000040e801610346800225140308103103802c004560780c50800c43d500441c0208000c3d400382c0d8020801c502210068003a001d040d010784 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 983279631 1250 983278381 983278393
    0x901140c1b1c12021005011401020c120304062001021206101b020d050a051204061209020f0603090a06290d0302060f070909090c05010806091e1b070506010305 70
    0x220034000052000100c510302e0161150703818010a400881c400364a500a20484290005c48441141202c02c280c0103081a030600e001314000643e0304100c1c80c400c01d81c04079080070625895400407942d9100d284210428000d0402d14612005804808071074150380a0700255591443c050391005a0001211a24404c41401940b0416071348100e1800c2c0c03c07468440070511005025408210803100c0e0090101c41e90311070030b498100010024410015907071120b200141d1500d09106010304803006003451220941c6c64895200096a07810150309072440c420356660340d607503d0700f410712802c108902c01c0c081c0c0014180036001c02e001600041c6048000b07030200c0c0840742d4188420800c4012580b669020b00140d1058001c0b400d96441040b0705a000030050800d40d102e5136866141005a4554031030540700080c208104000a58100481e240e00400440324914246440e134580c5400c400b6000400d440d16071480c00050846c505429800700102c052403140d41ca640c001d1a10503528070090004071902d000344 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 983280881 1250 983279631 983279683
    0x902041104080c01031d0f060601200615060702030319090f06120c12060609090c031401031b090513020f030705030c01121d0f010e031e0901140c 64
    0x3500c103603020b582c607003406000c009803100c004401900c03e0780100318541c030b980c0c0b1041c001c0040030030050080011400140150b440e002c000034084103861001651100d01c078400b90311040c02e01041c03542e84030481001905071100c0c0780c000b0035181d000c0c0003c020740501c40014142c6d5034904203445507980600c030ba510481d50795114040c4031505052032023540003191940c075204011440710342014904001602e8180540c420b83c001c1d14084c0c40c10b943c410ba020a0034460188841d0440c0d004858003025103060511296641c01545080b403181440081c1c03508107140c60301c00d040e2101d5980c0340018403029805000a041c24000408085107800d01240b003400715403020305207801c0100b620004c41d6002005089805120030064071205c00c01d02d5200841a9900501d41c00012012492050904188014a4007000746003101e8212245100c0b01c0040390700c24801f441848812541c00c1d1402e600381c1c0901502c41d40640c00681d01107800010320080d00d10040b0743c180c00100000746d8800c080e030040a2100c084e0b100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 983282131 1250 983280881 983280911
    0x4031b05040e0304080f150406090213060b04090e010212160903050304090c180302031911040c02011b090b070204110d09060e0712170715230702030a02061501030e030c01090204 78
    0x7da08030980d4516851000801182407640480c00c0c05001524409440c0b00c03060340842210075542114500da1408241805004e03083d1007517013002c02041d0000c41c689610480300100c6604000c200c026004c42d4000740c84146440f9085820095901000700d81d1030700d417516080c0d400f03407654880e403400159403203003280030510344074440300104c0e500a4003a0403052080a210306191024640a8a0f900d03034441070725106881c4c038858859101d4099000280700b10103030400c2e00450101c5590181002041c04e810301240c4d0a1030125691240d04540c0000c409030940c942c1940d500880001b09019403900a0036014002c4c940c00800c5024054425540741a03114440480030408010001d44400702418076242e011444174010311840340141503500c0000300e0702d03102c0000c2d110031690400d04282200c1ca98544c002241c900349401c60304c1400510b04052000400940d030b441c0c000c20b40712640410b103065600f10b90113540803010141d012029207035a0a400516140a0000948120b011358a41900074200e415 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 983283381 1250 983282131 983282143
    0xb01051b0d17070f0f030b0909240c03060120010518060a0c090302040b01030204080a080405041b0f08041407030305040806090102030709030f030513170606031204031b05040e0304080f 81
    0x2099440340316140951483c05c98502024914101c14541d40703103846103c964460500d50b2003403047c8402400421b00320318009620704485c0c408100785492200c1403101d05e4681105a907030100c820319080a00d040e50781005a4030303160b10b1607208044d51801c0d05008050b01410101d5107080a00320444080e1384980300034608540c3c115410f0400650180c41c24801441c280d040400e840c40140f501504042d00c40d005641050b00a06089400032000181000300d41018000d002107249243d40d1030300860080300014240400280c4034404101036040044c042010034002000b900c1c1605c802c03178054a46078500070301203501034040c072103440c41143c000035800d0505000300d900c03441203036580640c041d141d555655080580c520b82242400000e010503202410016244002010b02040d014040c0b00410030a0381000005000c03c1d000342c0000034680e89009100c17003210102c9a2001104a030b11503c01c0300203482510340c0e0045580641042d080c100b02103800000703442661108803e445000c03100d1141d85585d09 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 983284631 1250 983283381 983283391
    0x2100206090a080d0e01020a020703030e010309150216120f0908120f03221505090105010308041a07020619080c070b1504020706090303020c1902090402040b01051b0d17 74
    0x54030812002e000550540080e009000f06510040b81c45c0c1e4080c000b050036a0070900548005a000b44010418107a0001161841901c20b080401003510191030b0341010146135151005250780000b0b0b407502c429108250744082d241c00c410341c030300300d07244510b8000d0500d4500c1c8480c2d00000e004900100c0d4034071010a090000400020380e091825880ca2200c0c0110f030401000c80d1a401c2d409000d08292512000300a95403912504040c02e1344008c001003602154006820300032968501401131000500c407030101c40588503800700c1d5206002592020715003034881c3e1000290000400b048100c40e142c000e0380003d568001c503440d0003074540c1d1000110146c902079094050043c01e164004650702d40003030b1200a0340807034060303c05480c000240d20b5070381c02c3d10901c0004030002a4006490071440d44140a04040301c1c0900c102c2a241c00c80d20b07000a9049440580f0207071040ba511030315248181c0c05402180c41600d8181507065a140d42d00344040d0720b4203c403040b4003000ca80c81c4484030548070b018209140c819 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 983285881 1250 983284631 983284633
    0x1909051801050f1b1201030c05011101021c020c07050409060510150c080a1e201902061305090405010f0b010e0102100c020f0a0b06040608010b01021c031d03070210020609 75
    0x3695401c14500b1800d0000a0705444510042105848880b0045081d50280d0700418000c90700c1449c0c00001081d091603250b925006034410300c846800407070740d140d219414004c140c0015807250a418007190400c070702580700715440342c0341030004000c020064004511640a02c0c0007014501e43d03441242c0d011205081110300010003c03d03c207030000d9948805040c5a401e64035059010700b5495485116188404440c2d10200b540c0762469003a0f000b8a0304811f01068048029246954045a08000440500c000284103103004691280d0440704d0544220080000070030550990526080281c000c0004c4820020401e040500000855014100940c4036040c107034001d00d40c0241820852300100007800601c0114001c07612a41d0401b04100220810140a4850004641865000c020441d01954090021a41880250101680c000c1000728000e0640301c03002d41c030800a40c4d01100109148480b1401420700b488100400741800809800200e1095803050070b2414035450a99850908969051031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 983287131 1250 983285881 983285911
    0xf290109030215070f0f03050705010f200304140718110319020a110d0e0117040804031212060b0904050609060a060e0f03011404031b0809040b190905180105 69
    0xd9483c0e0322005203000c2e03018101c0c0c030444c0c0b6841c0e5104040908080e4042e13002600c041072aa007406021f202ea41c03140b081d018001c0004844c03140c640034800c420041505107000d00440001c00f0301050540342c0006519107030640f800036441d441d540252540c200c2000500341d141450240c0d0b59942c1340200c07802001300c00400e580d80390075179840d5006507101c0038041040054109000500d01020013030400b00a0040d110907900e80b00c040300052540b01005030700072428108009210104007440300b2034040c1c2ea0032002100e00ca440340c25095030340d112203a10501c592442c1844c00a000c1400201911500d40e088600348299103d04041294080d401e4408036400031101e202044258040c0340100c210440c094103860300e0b0068000000d0854004007040d04007814114200020554486204021000d110007010100315194603180780c18002d9028030381c02103a980c100e456550f0303947c40c2c40c8400026100300703141da09034440c20310f0409000159500b0049810070001c000c280792041c001c0c180302d9040c0d00712000c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 983288381 1250 983287131 983287159
    0x6030c0804110d02130e0114040f020f1207060504091803020d030c0e041401081c0509091513061a0c030304020409020a05150403110907020a0f060f2901090302 70
    0x20803003902090ba903000512803038880c01070311400d1983c0f4242c048404002117041801c5510703401e40760001e40c41d214400c0c1000c02c000000712152101c0b521141c0541d0b88141141d529004148500c82e11100c580c0700380706840d00000c48d01d034407070700030425601601814070130340c1442c4191980704c0c960500000d0268011a803081c0035a03210341c0c4841003d400324a0a055102d605001003821103010940c580c1907169280014408003070200140f6140d41c0301c1040040942040d0500107045000743c0703048500c65080c00c1d02041038054002501410740720001c040c00d01914007a0901c80082c070302c0c0e1080e030b1210312040c00800882c0d2103090540b9500403202000d94510342d00c5600704070042c403444104a0b4003510010300032542d0748810015007003a00c0080f540300c0da04c504504000d075800d0300d40b6421a21440c4c401c0304008500740e000c2658102164044003c000750340d4030f03103084ca01812801c501c4419440c980403100c0500c0b15515020f011600301e001044000700c810034011243c246041c0801794000b4100d1810308 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 983289631 1250 983288381 983288393
    0x5030c0316210e0d03030f0f0b03070602070e0a020a0c0b1311061908100306020406020d0905060f12070c1b050a23060f070c090f1a1e030a0b0108030a0906030c0804 72
    0x1601c17031003841c3c0024011000d9161f00f00f20f07a59043e12880307095407904001c0c0035040411545c005421140000c156a91030b0020b2030740c8090008141d002100d4000c40c80025071402284031126143d40409810b5052a0114680b11000c0d030b66001905c010304c440052482a0030450b045642400200001541440540d4816164040081c1c050040c0e0a090100040451401d1001d84040e214541c09800300200580c002461071031560842e5126010400000b1040c508240c2110040c0401d107a804089a4072000144d8981c090038034050401c10292940c0e180c800004803800c415101e04440b44400340d030319402c0c048080c95000d0910000e503204440e1082c024980040a4102440112501440d10f40b480c0e0f030b44450591a41e10041d84651035450b044503002e450700078034403104075001c1100c00d008007000004603400800c10511b05001c1703450786098810f0320244040303000300d9001009c40086595850500752790794020b00380f41001a0b8a22404109588240a2000c41443d16a25583c0d00d4803162030b08 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 983290881 1250 983289631 983289649
    0x501060e0d0c17011d030c0a0b040201020102093609030a0c0f0c0938012006040807110306070e090c040e2a070c0902030405030c0316210e 61
    0x6607000701d940c10000580307045800c40c04403020710303500010981409500014110200710042c1c004071b81c005210401c00c62074002030407100150082c4078102561180c2c00142d009100300c20040350469003000d03201014031004d040c1c0004003000e526a00700d20900070108180010800c1d60b1040c1903400c10059084054810350a0110003400340380705110008080c1d880e1070a081d070a030300c0300e208240c9940041b400400c091410700f5000704c1c220015441200c41c5d03091091965a1404030394140003040300c0407820710366400026201c0d0b994034400c541c0c49040c5402d01c4c5496801c00801201c5541c03d00120b04d46a04005ca449402181c03030b40c54a000700b155600400c444440001c000041000c8144000903490300300d45011805004801d002020002100200001c424a40c05401840c8d100400501000a40c070319404000c0304c0389110010303240d80791454840c1c15803141d442c0310560792201165146140c00d00c05a02d13181c8a1048403080100c201581d10320b803031440210300c140701241101c0c180580c03d0510f1100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 983292131 1250 983290881 983290883
    0x90402150309010b2e0f0e040c1211040b0d180605070f0908160605030a060312020607030f0b010806090703240524030c1605030a1e030501060e0d 64
    0x940361008000056000e403a42007201c40728096911442e5449090808102c8024030560304009083c80000d000d4110703801e00c421240074000c00003050040b441c1c56105008540403824020801d0102d50201d07200100760669450081e101c062800100700d00f01e44a03581201c0450f203251614038140322054001c1c4002b40303688030003050000c0d00741004500181191054a00c5080c19807a0540c00144a4500510300c440c5a08054001c0c0d01500b040d440107003c090121045031000d290003644c0740c1d0350111210240070700340d10080c00304000c0042e025405801045441c80b4005a41d0100658540202d1423015078034100035440c04203841c0c2020450f13501b44951013030352161071030030080ba04106002440c200060321a0a01e9100840403005002500c3c0910014494990200c4010588038a0b0035011045200c060041103824400007428080011441c240c3c0d248aa0804103507600c4484181d8003911104c4070000c0c1d02ca8200040c2c040d0380d11140280325480c181d03102c59071740340d182d0035250301800001516100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 983293381 1250 983292131 983292139
    0x20109020a0905070815090105040917070606060813080d180c03050309041103060a0506130f0905062806050d0e0601091b02060f070305101e050a0603060b0306090402 73
    0x902080503859040c14040146500107000940d4a0010f90042c04504064000748104503c040d50180c00d544030420385046d074104481c0000c00f40c0c03161504030700120b06c80b9036011503054042810300c103101c41c80c1e200c0f0701210650b0716101e00b59903601000a031a2020131800909000090025412501c410384c8082c21850810038500140c80c001e031a07162140350130b5401245da50784002030714030746410103005107049880850506411400d250380041e01e45085401424001c030004600c4030b200703076a0a800403004012104407000c00c280c036003507140041c00b4111241406501d441c0d1404202d150b121514610304084203003101d010710300300744040f2120740c0001d5014240315101c50006c0c819210a0040900038a503407080095046102c030030a443c240c2551000c4001d540140c0100b010a02111207a9607001c0d8591400160940d20100004c00c0b001168008501201c1c07218041c0701e141800e07041c52401d4441c126007600e4a90354422085003910004c0c098a500c0c24420f00c0403500b5420150380041c0c02c41c2c03000b0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 983294631 1250 983293381 983293391
    0x110c0a03120b18150604120b060612090105091207050c3c090f16030923101d070501050c01090602131415090108090106082416140a0201 60
    0x1c0c00900550343d596441c111404201c014000e80c5541c83c0708824403241d0942e031140c1094500400d26042c0c41007500058510458071000641d580e40741c4007111607941260740e900806080120442d402020100c40c0303451684074140c54824841c0c881410380b42c1d80e5078000001c06498080c1010300403001c041155485d074422485101000640d00703c0c40d071681d03003140c2400c58a5944245000c010002c0006861461402c48410a105204000e0180a10f4010700c038140031030594014074010070300120700c0002c0049803600a10b00c42c0711400224003040d5042c0d0081d003d00c50f1401c4060b0103a180d400710f07004d6207030719031110004015039400b54014048090304113000040e03200d085d49842050380d0110701c9003c880d41900106000c80c40002c0d581f204181c1041e10b40c507070b0402d042842e00d1000d2040e4038907031f0305220400001511064094000700081c000c0c08060303420300110180140f003401004007070441c40f111043c0000d03102104c40624030007101da060740c84212810b24108841c20707a0303008029001c215501d403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 983295881 1250 983294631 983294651
    0x81501230f0d061d06060f0108061e04020f0408010e0601050f01110f030406050324090408092101020d0f091104020a09080106080d030c0302070b0412020c0d06050109110c0a0312 78
    0x640f0400b0100328900c4e0f461043c0c408201412420042c00410b002d00c202004a81d0a0f07590364000d8080758424800d403402c408190030840d031503c3c2407202050701640325000040c881c54030b02008002d80b0071070306c103180240000c10800203d59200c2100340181038000c20322569002403584280c0d0055040f58800c070070f54140c480c00300e60181c00c56110790050381c08113800205014404e44407c1c010b195083c0c3c060045420b500710200090812000540080e1040d940030900d4000c030356413407994480124003e08541e40b00c050b01d0100c14040e411208090702624585a10001003e419010b03100c506c0354411012a0007d0300c0200304402900b24440e210200080483d000c207081c0c40910841e1b010701041001401403044c0d03448024103403908001c502d8205030042c44143c00103a10300e0805600203034000040c00e84040e04200403403038000100380c034a0b4802200a1000c041c0700c05039000c0ea059035045101408814400e010703010140c420010405507640c0001080317008a8030606603c40284000840800c580c00d130 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 983297131 1250 983295881 983295893
    0x2030c0108150a17060105030a03120f0f020313020103060f0605090904061d031c02040b09011d03120c0d080f0718030b0108031305190303081f081501230f0d 69
    0xc1e500103554130b00b4080302481c0610010403100380140402c500410031154269401001c0560202c01c600d00300d521261031116041c081d4000f96200c540804046440303140510303c0c0e40030340f00e400d042a80868544500450480c10140248056402c0ca485451410340310405120b010385004106807103050307451040c502409408034007040e006091000950b152803804103142d481c6a110000821183d1040000700091100300d000d075104d010007400d03d841c1e2204412841c00c111003038040f400350f050107441a2030302d01c070990101500300c19004c4003c0700c500c24070004003900d0742c002c2954414001244040080c00c61841801c800081d400b500c003005d4151076480e510006450020b8115407002c0d00042111039240910030a03180091108807a108440c0c203511540740c40b41c4110f03010140c1080204070000f07690b01032010000c2000340000d05041c4850385d5900104d51205081c81c108d040c8a0201400064080300c0880528800c00083d403c0c105140ba0070700400c600ca001c3c0b41c0d40e1700d40100000d0440710100b21 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 983298381 1250 983297131 983297149
    0x9080a1b030b1311030106030b07260702010e010617030319140c030712060302090610020705060d02040e091f0f0b0915010e0d0c03032d0c1502030402030c010815 71
    0x565080003803c2c40c031498103000d1492010700c110b00030b0785010010000b00322000030b1142c21101d84e051516020b00c407a03c1940d03c0311000802a44821803d000b440202c41d070542c8a16410210300008201080c0ca84040c13000d00c800460000b212070f401400030400d142048015098000c0c2c03e400005003030a004151511800d00449114003451800320401c1401a0000c50418100070703001c0c0e003000707480c2c02d60780000c082113005030519000d1800308401c1c1d88134500800401014110080c503450300c402c60007103010702a500c14001c0720784980b44400860740162002800364100354040c40704000340349805041c0c5009024400d0026245130715101c1c00500c9848048400d405050301491500c00717001030000140400025021843c0909a02500c0c080415181c550301c0d0103403641441c0c6441a81620b02c03035450007040d9101000c4c0000580100c2d14441604500c20005c400d12600c0e204407400252555603007240400c81d4040d4054100324284182c9610401c062540001501c01c40445038104c0740104030002d07 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 983299631 1250 983298381 983298391
    0xf160506210c070b1807090b0406030209010b0915040f031e0f150c0e06030f04030314010803130527070516050606030f0a0c1a09061c0c09080a1b030b 66
    0x1002c0042c0b0b2009110f500c0030302a6004000b0444244020030304074009507141d200748134420409589a00c0500d00303554039000310008580083c075080965845000e8590350741e001c00b031060700c10a00c6894410488880c00241d4003101d100d403801c5800380c0e01e5034076800c90115030036102c080c01c101451004000103003985440c20041d1f0003201501c7c04c03504520300100032200c40d20741d80c10500c1414040d0303d050359603a90860341d01c4003030014820f65545591a040c0c025000349110f00607580c000700000710304000000068030480510300e4100b480287d03204140002103010080124a4081e51803454400014001c800350f0401901d00c1c050340f401940c2d4188040d404603110045805800070003d02001c0d140c100030552481c000d4a0192071013aa0a980307003030514000e4030032020940790b408000c040a24100d01500c1c01e4040251006a03a108138521000c04080d40c1240d03215141c0c45c290003030358003508c01c4000701c042c5e071300d000c0c02420904e0058546a405c0202d0090101d20454451004000100385801c1c580c050 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 983300881 1250 983299631 983299651
    0x3020a03122a17012105150405061005090103170a1403090706030e07050d02100311070f0501150602060c160c030605090d050f090621180f16050621 65
    0x10480c030240c01808443e00040e00c4141c02c0305600180880c01e2a940440b1017400300440101840c0800d1920500b0580c06002104100251600b004140304000c185148107007024454015030586070001c00c03c0182d001c0c000980051030f05200018040360744001403800200da03081151660050460761059540101c0740e80c0b0068100300b03410001c854160041600f24000c03100031785556428580800e50811141c10040c6c07040240c003d503c2803c1f8080d40c0944500070103030040c69910380c410304140101e03510102044650351f180821021b0301c58002c0386602e05a83d56580034004903203a2102605480e08000344814043d05204240c0c4001581d05900302c00a51146202117094a040c220303d508142150803504203001e8100706503d8010720304022100b01003000c580040e250f10b0b2204980a00700a026401c1005c61252414041c040000c125849140744840c022a2103003500210380b031b5203545162000c2c0c0840d0581010038000c51601c01c01400c15000c06110505010b400080d20b13014090007680c0a44032 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 983302131 1250 983300881 983300951
    0x504080406110331080f0d0e1503010f03120503040308060609221d0f070e040305070b0411040f09020604030f082208060c0a080f0604020c030d0b0906040903020a0312 73
    0x684030034611800002d0000d03c002c3d091200c030100c8100d0b1111f1020100b41e0420803000c406018075500c0e0440241c40707607901ca003042c0c0c50b581c407202c845821607070a01007510380d0701581c034030040494440c000b140d1140b0351580e100200798540c42d091080d00e0f0054191260311200000e07406400684541d0000103610f0f810401207071980003101162941084050304500540040c09250004100006c0b080115100c039031b0914443d5840e414119800c0c094040e0043c5410302c1c52080c001400300b80f0540340c0c20060f0480e007c016103180d402102041b103074002d00094025006110420100d40584010719009010704003003868002100003011000c20600614414245101c005110841c020001c3c40d61000010480c03614003800440080e060307450041001c00503140d180c0009081d0303103954056803410b4115030102e94403907a4801a02000e48402c04180380100758260000d00d15141c41d000c0c1c81c0380d00d034054014003c0400551411036640003a40701603101c0c292a6040941450005541e000e120392180300034200d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 983303381 1250 983302131 983302207
    0xe03010b121b0406060804032604030309020307050a050a17010e0a1a011e0b090a0305030f090103050a020405151e2107090e010b0901110303040506071205040804061103 74
    0xc1a421038500b0314015442c00409002480c3c0248010741c1050b01810302644c0703045140d58030300084c141c3c100c99904e80c26001007031004158240d004511024070840913242040c0d04d90702803280c0800702e449101d51215981c4010007465085074505003181c680f1070004900295840145850f040c00c0c14030448080c122004511802a15120b4107805001c80e0314003010040713600c285018810300310380910241d2a10000d866032656071000b015100540e07102c01643e40320160264051481c0d080038006c180800e09000020725001b41d54400c0341c044e254014103001041c402e41426108a410050707489882c0001c003d881d6140360f0000c40a040102902d0703c0360314506548044101c48500c01826600500100100a0005414000416040d40c0c04591000d4480d90210012200c12030304d40503e407090300002003400203001d0003180c00f034070400b03a68585020510300b8914020440e0002c8402521140007880240540d0788607442c4416a5004241280e08288000300026040080000f001d84840003101d1014 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 983304631 1250 983303381 983303413
    0x110304030e210c0108090c130e010b0904051b2107060e090709140d08040306142415040815010501081e16180602210a0f0e03010b12 58
    0x440010301265041100032a4580d0b954903d1450340d0620004000007901e030303041000b001280c1c00009140c81b40903c0c18003001401031007403081c4003d040d4200f081c0c1c82e009060980105010302d80c400010f02150480b00303e4070100b140842465a032000c10031102400ca65a54160500c002c0c01e4200a882c00602d00540541710091540c03a09004880600401c407040340c00c9000001103076030080ca400d001600800010720303c01e5049100405209001c2400b00600445500c051800025441d1400003030701da2100c100034000d548a6980c0102580b00c40300034250074450b0f4460342ca040e04103005824a6190510305040c0010302d0088a007100300f0300010407036581c1c0b0290b100c0d0810145030328151071107030300340e00f014180c40300400e1a0580301c0840203025441c0c1c0b01d00081c0c50140450004040790a4a80400075105da01102004400040b0f1051104005042304120b0b8101c180d140c941c0f44610581c003006803108a903030702c00c45074155a40e2440310902d0302c44880403a0071a1000300500b0301554032988036 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 983305881 1250 983304631 983304649
    0xb031812040f0e0c090d08090d0510050108030403051b040f1a1005031012020f06040f06020609060f0f250c0c121a0406090c03082a03031603110304030e 67
    0x203120f4190a0140c40314200b13003103404c004016181c03050f07005854288110f5a120f400c45103a001011b08a001e0144040440c83d610a25080a810321045c2da880c3c17a03403540c0f8040d40c00040c0454014204660300c031265003000d440071600c05071001c126640905000d000f00e40794241104100b10001c82408201d15104001511944a600700241103003000c001c80400c8812a024240000081c08418003d665a41c201c000100000512403035540d42c0322251004520060b2040c032001d840307030394081403030094045006841006a42640000c503601c62110045003c40078110701c140340305150204102c040f545c5454105102e2640300c2c00071a442c6490080242c1e181c5a010001220800d01c14070002030404110040070038150104c1070f815261414514000e1403d640010504021950000208a20340b4090311410208982001d00500300300c132800042e070303034507010240960410000103820900032200c4007509c1c492481e000410360600d500462442d4070540d41a0301043c1c2030b5108140500c1d0040c54 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 983307131 1250 983305881 983305889
    0x50c240712110f0c070e01120c06260712061707050307050f01050703120204270203090d081801020f030907080a12120e0118020a1401090b031812040f 66
    0x402c0400c40190300d070b00039401031450b169002d01c400202e5680243c0308105841c0642140c0c1a00700c9256990781c400071609004240807901c0204443d000101180680f401424684100f0b4405034001880144940411001003108042c0440c1c4104824101e2051140001074080181e2500403c00c40c41c80051612045a00440c401d80c021042440300c0d4403074054240c4455020708101740c07a44000d150075614000440f2802c0c0c0004d10119002a60480c01440c20341d103800d9001c0f0000b01c0d038551011884c140d200c100c454074007e91200300c01001880c032420825500c00208030307c9414071037030b0017111801da92152180e030002c0c650100500840c4042404080003c00840c0010400c000c140d07621b200d00c8295861a4030f0500c20b40441c4200c1d56043d40d0400021684414001c001040050f90707482c20002403034005074018a000e03140811084902e000c00307410b151058503888400c0d45840410b00746584014440c0740d45a04000040c50b210304100b03d808001c0404d08800b0f030b111410000301081c0d00c0c10540c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 983308381 1250 983307131 983307167
    0x61e0c1909050a050f0d170f07210512061e0604061707030c12021e030106231303060203040503090d0b1b190309170f04091103090d050c2407 62
    0x2001d106541d401b00b0001a040d840704400c1c501002c000c10f002c000c2c1c024107a0315584450f000802004101032500703030030803444854011480071054034000301e1741801440d1120303070070407a1400401e00514045035080c0740c020f41c1445030055030042801140850f001684994041900380c0e81f103031113101120b440e01e030340301c00a03290410088180c424020444400303248052440c40c1e0001e507040c5041c00f88180c80c2d80007140d06041c140d495039a0040101100070840400d1200070051000000c55240241101c0722500700001c102d084608548503036009501c0601704440d907200411040e016519030180144105004480d000c1603440d140c0100c0e41c04003114603001050400c00c0101c0c003006505032980f80c071600072901d4006800102881d00303040c0a0340d4481c1c03c03080004040703100c04500030340c20020000d07541081410320141d488075910703000b02c0c001541d200038150044140049902d03c01d60140240701074080c100c407070070010400c50b40501440b1000350b9481c4003500c4104000b45030809951a2401c803098 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 983309631 1250 983308381 983308399
    0x5181203120a09080301051e031b240f180a060908120a0c1e1b050f030102090a050d0f06020c0a11090907031407210b0603061e0c1909050a05 62
    0x2a403011136904c414001c081c42a103850310300003110341d000b00c03514042c1240541100c0101030040d5000c81c5810000c50224071640c40d00b1a86103541241001402140510070101030410541040304003182d08075450300c40e40001c981001d001300d039403901041e000806968444402843c20101da207801d01003100203000e40018100100300400394000d41a0000580102411140452000d4a403100b0800c1040141080b8003541c62141c100242c180c0207070840704100c1c3d18088000c900300a1500303134054003036901da100180c0842080030f420400d0007010094800c400c1a48241403e0f0703520b20403030b002803c043c03032582c0c4130004240804c500301c007110768001000c03142d40f80c40d458007005060f034070403207400024104404040c52080b802d02c00c2212038042c05540d20504034110000d1218000c081e071000055502640840100b2440e007004100980141c204001e801c80e0041100801c950005c400307440001c2c01c0a0422144040c1c40c001c01a0118800d06a0b641d085420324090421108030b246070009445480c0070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 983310881 1250 983309631 983309633
    0xf09060b031e0415090303050619060219110d0c09060504020c1c020f0a030c05070e13030521070e0a09051501081e04080a02071208090105181203120a09 67
    0x40012103014600d810301c00b008550f2503107000b0440101e51410000010706007006030f402c158041d003101d4072859068601c0e184601d0080741c0f0803500c41c0e00340305003005600027510f028452120b051000c803045005980041c1c14a140d60080340d0403030036441e0181d6440040610920403140280101402000708503419400c25000a00790713515a01103030795969040c00c140c5c80114681d8000e00208070401505010343d40c40e08c620781406401980c110740111064058a00c2c081600c02207030506078080d000d0a4100c42081003251303002d81c0c640c0c0c000c0e40080405d28409044030600300b028200c080c4076a18503030b07480c0564203007070b001d2243e40001c6802451145080c07104000a007441c3d080e015003188401d10b449182511050705a18042450010f030720010800380d01000180220040100320f0105964200c2e48450380e035030341c900c1070300000f42e400800c00348003001202810740c464409011014100c01c015905a03064034001001802200059074254002180040344ca0150342d8000e07602c04011030081c40407510f5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 983312131 1250 983310881 983310901
    0xd0e12090607060b091e060909070315060f0609051002010c0503070507020f0306070c0c08120d09150c0e01030e071a21040303050a06051801031203150f09060b03 71
    0x844110314000e10000c5050000d100c4140c100001c2010068400b001a0a100ea402c900305140e0444103008000854007245150034020091071007031070b082014190b21400c0d6600c00c02d040d440c102560b88041d40b1840003203001480c109401d1b004090310b444a0160a00d0181400340001c28524540c0559150060030300300c0301c1d04202240e82c00340140c40c100340e4562003031000402c04805462070f40d070144502c500b007242264010f981021710500031003500521542d50300c411a681d010408880511020a00a40454000300d421903441684070f01c054503600e01c0c412000e6822100c0c000e01c490002400704030401c0180d40c16210340070101c0f5110303016100860800a44615000e40300041d80010703000010000458040e000d0503454044101110300c085080606004010388016101d0541c01c6141039000941441c000140340c0b9600f0002000401d1a8a191075a031401490701c0b810b80c2c203040d224180540501c000250503400741c00b04050883c1300358140403c100c00c0f540c180d040211204001c106103c98020 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 983313381 1250 983312131 983312137
    0x1050709060c120809070305071511030a0e1306090903120e1623030a0c03120306030f0209041403070b01090501170a08070303151d0702010c120504080403020d03050d0e12 75
    0x35107013480d02440d00d030f44100340d1604905500242c458062000b001ca1407041c0c040090012410031342e070301840c007500f805d41186c0360300c248650301020031010765150880d070801c1c14a26529518014000840c250f407103185d642511900c0e84120002503500c0f44400c0c0b000c1c402d2284540c0c1024050041c80c00c4060350034040c00481803801400c010350070280c8682044120341000b07000400002d0103659501300585410000810300e0f01003120004860300c65083c055202c0e10594080303070b401030005001030500d0740034050091400340090322485884088903018074001c1001340b0003903202e42102903066250031103d10899906801c03074000c0d04007020407d41c0070344000a81c01d2140d5003040380300da901c000c2880e0680080c860a102c1c8542e02001303107070006039032006208040d120180c141c4442950758074000200c1c202d6032407000c180041613250508111000c50340d80300b50b6005206603566460b16460b0f4000600c41031400800711700184001401041c1c0c901280101b200a01c0040000c00c80d1811103802070901780 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 983314631 1250 983313381 983313413
    0x80c03010f0c17040813060c03230313230c030c030c090105190909030309020310141f03301e030e012c1e07090b060c0601060201050709060c 62
    0x82446011034140185d020840c1d140031654655956a5540c0711806440c0c0d800300b0758182c011600080744200d040991900103100404095040d5103580e8516081070190f03421100141c0703180c904040d40c110280d400451918981a030038008140c142417010403d86003013555000d01e406900030a005040301d8460418090565404450b0f0f00a422100100034808000592148021a0034048507009150301680f0070117106000381e059a038030140100246080e20310060601039000000400900300140d403000944074480702203450180d040d540d07103c80b03001646000040c90700b91000c4039500140443c1da0302c400d4202d42641805c0d008000748821a1281c00d812000c0c0c83309041d240ea07001c61401600390b222107a031121080108002d004103c1c940c1c94030200109690780310303100c0d07440c440c2c8000111100c00c040b0100041c0003017440c1c905007034022010300304441da00e540241003809166600541400380502a00360380c1d0002600b40750000008005003c00e600020038480c000b0403140c00302c1e0390460b42503588 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 983315881 1250 983314631 983314667
    0x20f0a030507120515010f02210a18090e0d021c081509040f060f1811180f090d03020309150405030c0f07080f070609210c080c03010f0c 60
    0x1a03560310b07005443c145200b00303001d03410510701002c020045902e1008070124880a80c1c89104642d0144030aa81d41d014512003075006150580905139041e148074014170070700d19185042c1110080d0b840f4490041d50490700402a52900c41d009202402c0c0204591000c0480b144010540c1d480011410006c84004c09682c0e0104203141000815084c14103040f01e615241c040c14859441c90f1500b08401d11041842044030304a0030584c8000845069006292551142080e906c2c05201c0c4c1740d03540c4440d001400080382d00140e8039204019a40b110446c0c083c411503c1c0c81c042c5546142a100706400c120b503a0070000107041c41402804184840050a0524841d2010003c2155115410454514040d040c1095464482c200441150f5440030030b91008858400c001c541c010307815003142580750f40c030500480000031032101c0c0400c880410f1107009040c1900b90404222882016240c40003e2000c0da0000c011951043c601c08409043c00d20652100d48402c1000300052003030510002c205c115116906030750 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 983317131 1250 983315881 983315891
    0x402090703050a09020a14091501020717120712140f0403020603100b030a0606110f031c02210103120c050d05070510020d05160804080301120501020d0501081609020f0a03 75
    0x84544e51010010b5900189503102c9182c0c4d4140e00322004000b0700615004074000f6020403040d80c1c000b821110521030580181407514200880041d4002044c80240642d208540300d280520404400910405c0d014140c0d0300c61402070480090091a81e20001d244070550402003200c61742c00310015a01943d6048503d00c1d960340740d060401c2d0510240740c01480b00d2442c00000c1c0070844580d50312040454040d074545059122024295940302d07615484640c00a42081000d84012001300344004080303070f1144001400d015800d6081808010940036400c1e210840c58010b0041c440350341d40c00a0080b807580f8016268050b280d0341e20340c40318110108001400740c00302e50b540070060240305040c0ca09503201d0782103403a150151284800703414280e584110205814550012207440f0744803c5120302d4011207501d2469284c8611202c0c51111007005441955007803102807400b00c0c242c0070340c500901d0807100511a851342841d4541210740c0b203074441010140304000300002d0003564030039114208010309001407 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 983318381 1250 983317131 983317141
    0x504140609010e061c020d021e0a0b03040206071202070b0a02030301030c0509070f0305070c172d070f0206040306140f15010905061612020a030813020108060d020316080a1a040209070305 82
    0x400c61f456100003980980000d01668090070310081c2a22000f2003244c660b8040d50f99141003c2e001c1c40151383c041e4100508101c0070f40884d001300b0303543d0005003017031040f00c0119988545007509508503a6030180146c0000004105020141c9110b501900c0d04a42c800c050f802c01e1100940031800a0310344006140d15031740020a0702e40a080311b2030b94550011240c4104071400411404564026241005a500013110203000d0002240400900c052621207903450f01800b40c880c8680a10801401c91340b1038000c00c00800016074501811000b04810038403c1c2c4035040c0000c00d1020764000030543c1210b051031180e81d02250b030340494224102c071001e1b0b442a03070340e481c0c8900d106a241c50a2002a00d0040c882c080b030540a80e0004001c10118040d503600005e9489034100010200620b2101a001031848808074401d0315200e00110f60480c070007802c41e4905101b00e080e50b5040c01895201020035000720565006025058601101c40d501328100d1b0006413900750b0020f0700c906005005081050740da03c0002e2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 983319631 1250 983318381 983318389
    0x3070f02010209030304090e010c05070305180a03121d1c080c070923010e060a03030e03151003030212071e030c051507170601020c06130504140609010e061c02 70
    0x141c00381e00084c05607590b81d45c03100300600240224089101e2a50718204441c55118451070507204403035450703544c1d1440c105950344106c5102d4100c2c000c29603c81024400040001d04200b0000781583d9981c40d850703042100100c02d0b010780105002c02d64080d0403d0f00c1d02c80c0070120ba598581100b180c1c0803a40d15115284904114a404038940105400c07600d02400501aa031400102e00c107449000d440d41e500f2aa00c8200c508901d04050b10096003000b00b0f19010b00000380100e01e00124034034058201e600d05020840b003402044400c1d1541248004505070038400d241e41400b201c00e00b16584040f04c0d1508045588152000ca0549003030321005044465100401d4461441c2d03120301c981100898901008940100c07148000554003680841c011240c3c4581340c01141c901184110340580241110ad1404018001d881d88111541c4001c045a118041040e070380781d100e0f450649440d000750000914140c018400c0781c0c0c5040e080340f10f07403200c070008220f81603440d000e0114620300305c3c008025540205201007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 983320881 1250 983319631 983319637
    0x9040e010b03030a090e0106030b1311090a090219080408030411150c06070323190212040b01170604050c2106130507170a0b130507030b0421020303070f020102 70
    0x707940e240c0400100040100e901141c002c040d11ba20a00190355a41e8030310098040300e2864049540000d4030740c0caa880540c8165000d00d002c01d03040820140382240b4040041e079030f4042600101c02d02540400c2e41001480c9a03406000440e105003880600703424152602c2c2c82a003c0180000c0c15502d5401c204007080c0c032203070019144640e506c0c581544602a101e0703e90340300e1808039010360000c2c0c40d01c0b100e08006040c4040c29030f01c51941d105d60b08103a40390444682035001c10000c0e4020802c1d000c209103400703984d007001480d00c201d0142040b2402541009090200c081d0400c1c64400182d1011702803101003200403900c050180c2e01100d210680f409a10f001002e68001c3c201e0000c070394056030041203529030080200f07405443c40b90090f07506c2c07580c070b03031415940e80d020614942d851039204c22075090003d0036070510305030000603000c84044c00b12010b0b51580d2900c01d40780c100f200c105034140140010000c00121248518200d000411000c40465000a50301d002c010050b0382045a04d100100d081344c001c4d812 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 983322131 1250 983320881 983320901
    0x9090c18060e151e10121104030305030f01091118040b061602090601030213060e06131d0604090b1f1a0c0609010204060e240703031b0f0509040e01 65
    0x5104039161a043c1000072070f0701e03001828041c08440382259038080035410851480c16008140000038010b03e1002c0b03a1000e10f816070110440da44030301c0d10200715000d0014000075072090351113640e203142c50000308062100c10390066905a040030300d40e00c010090340c4141d039842c05929048400006550f40060701805a121001c0d801800004940d030400b0a00c030f5100101c04d0080c0c8995010342c4818004400301d1140b0a0309425040300e0810900038644510039607a0a01d0006201d14241440d001c90b501007010642d0015410402d8082450244c5260041c0c090f403220048400700b0000550f0346500b1940b4100409854010b43d8854000c9124090703140a04040e005006111080c05c10700314481c40b895010441d100014424140010541601402228150b500e280e03200100161050103000c014041d03064210035a0380d8035461007a100f0010005003488070301039a0046842c0031080f04501480c00b02103d45010080030840c4060950341100403129690380903140080c140d0782000416004141c2812 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 983323381 1250 983322131 983322149
    0x2b1713080d0605090a0504020f01020f0c010e010e12250b03040303091e030503060114091f020708100b010e041415031513021008040302060412050d1805010609090c1806 74
    0x1405503004080d03000c0347c4214426141e04400303114800059030b40d80e0705d2494100c129846141240150b502c12403207c0401c500c1814002c0402004000081e10750801040c102456400b501ca89000030300f1418050102910010401d40400d0910041101a101c01003000c2d040c16184e9000004102d42500701c418080c1e82d00c20b484254801528000300700d40d0081c0d405c3c5001401101c000200c90500008690301030074000c04900c203c27a01c2c440340d00c481c001c810310228154001c1501c0090814000e000d0b401c00c0280c0f0041c0041d00010110003d40031070b0b2a41410381c0514a00715180c05421030787c02d03045400500305038a030303000e078a424030010303251200d17044481424404400622070f50400c00c00c0c4035508148211100b42c1c0c1c0c0d0303070717000021118140f080b600a00140d000340d01040c045405a9031525020202c1d103000b038600180d206090090350340070200e07414140e48100381d440600500380b1800002e481e14180920000070300d500c540d208100d0600079141070400c941c000031315180360b560112000b0145a9 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 983324631 1250 983323381 983323399
    0x703050a050415080702070519050d03050f0409060315050103030e0405060301061e05040509060702061f050406030807150515130b19210312020703022b1713080d0605 73
    0x25000808000045d42c060b0094070440001140b9031500d00901009100f0300156200c1007403500e0200300d0440f030342031019010700000b00107291200201c1d00081010f0840280c01140113440c40c034041da1070380444545007074030034549001400000e03845804040c04900444021840e920b440c0d0000780142040d0f80403c64001b054410748403030b407a0b1905020101c440c1200c0410255075540000e6031194411035101c40184c00a07400a20244c0700c00c1e480070701c01d00140400d140560707101c001103011a184c582041d102220040b480800b0080303501801e000110380910140500c0c2801b250810850315a07000ca00c0c4642c1d80205181407042e000c0e8406c0c0e0484000801c0f200d0385a014000e0319021381c099024500c2001031101e0b540542e00301d00d0603190aa50344c0b46d40c0c0c0824003c03d5410f070000a421a1104504502904a40f5072500108628060540080c001c00030203051800e0301c080e02030384d40260070412202ea8003040024240d0340e000c1c52014143c01960031030362100700d500341500030291a040650b0002c41c4c8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 983325881 1250 983324631 983324669
    0x305181e010612050c01050307031e0e0105070c230102190f170606030a05040f02041a10090305070e0c0d0e0102091513090b03031209010b09100b0703050a0504 70
    0x960944250403228100801500d40c880010550801d1140c1020b00168404056505d081d403054004640c0040a46000241100700300f40c29410801030700050000141c03118650101440c0038880c071904102581029026140b99a07036640130b865030880428a04584520028500d06085d0101e4180c800c20920200300307400c0c80346000d0300200055100e100010b42001d254002041b45e06001c03401030400821031415940c0b00c0f0400400380c0320042086a071048000d08180058031540614042280607c07509241c40c00c01000f0b11581d20300000d982d004200e030140e001c101280300440c0d01025070f2100f618170501641c810b0410807942c0f042c1c00d512265140303401300e50160b481c01035020384a8100300700e86246400070040e0041c440f170302507081d03080c12900414104110700c03000e9900c5424010405003e40b030400b0405035041d00d03034000441d5800070710b946803a010001413501d454007030707406000f882c2c200314407a013043d2200369503000d28100207083c04400500c007410140601c040d00d00038401c01903100f80301004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 983327131 1250 983325881 983325913
    0x111002070f0308060603152101050907091b080c070c051f08240f030715080f07020609150403020717011a12100b06040b0309071a0a080106030518 64
    0x60310000d900045115021603190719101c1700301d1f03008000f650301c1e1850119014040100140c514100343d400207050f02900da10300b180030700a4521a8496001428405240c040c028003520307021580c49841900890b10108020b4000c00c0d09070f0030410920100d5254810380c41c00c05d00060041e0807150b030100c50843e641001c2000b4000c048594851945c4107026502c0745a103402c81c03103e00c07415107c0808100c1c05696014100050142020803008081703034241582e668041c2d01c20001805080c0000307021808120182964076600ca8004031070f84010700c40c03407030290600d45d1900007902040640ea00e94101240a040c420080e0030b015146145040202c40803056405e40284a002651607800d404d907100400c00b858080c0342601c540003030401400350b120800824100a09400c10381e00e030300030030a20000c01d890280d031024501c0f1b080f500006000160a11840039161514900002c400d44030402004d040b0541c4400743d80e04449032400c000c1580c0e00c46050400c011000c040c80d403190b5108085007407440007a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 983328381 1250 983327131 983327153
    0x9070303120b10121e0204030c17030f0d02090405070c0b070e130c0210050a200703050702060a021c05130e060a0e07050c0307050a0303290111100207 66
    0x44a034071404800858100a2426544030201195000c1040720403494070502840a41d61440e04400000425415014964903815000d28242c200c29601141c203000b0403412aa0307410107010704080c24100c030b1080100007a5280b2030380c6510b6109407404140b2480802081d010380d0f41c036100007030007440a4a054100102010000001a6088c0a541020900b040c0c010150104441d6001e021085c41c0f0282401c41800b5140300d8004d03500718480c00104014101c440c0c406ca901a41d403c01d00429420b07401080592203030181c075401202880100801000650400101e82c440755069880300c0e01ca16104d0700c10303400c106040c41e20003a2a6109440c2c4c0c501c0a5000d0b00404060f09410402d0001c651102a500c0c03102c4070444509803c0f040300c90381403040d80c4003141115442810b514205181001c200e985a046401c8214112059400034685808154041c002c3c0b2a88003c91208215900310b00580b103902840e0030414541800306848021a140d2000d02c070b402000301e070f921419580c8403c0b48c0b0b00001025 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 983329631 1250 983328381 983328383
    0x60212192f160902120c1605120915030c07030e060c060a1d03040e0f040f0f080406030501050924030111070804050a06020d021005070c320c0d170d0203090703 70
    0x302c401102044416561080e2400c2458142e0320001c41d54a00007580c403198402158680c603941d031900000009201040706451994190701c5498841400d5030610200c3c040140c1040003641c0148104a0f001c20102c0070380e0f41d42c640600d0214a060314200100740b10b84100b210f88801401004104010081c0300d40001d4407108048601c4084074250818032600c031b000318042d02406075171000215030301d06142c80c2c6184c3c01c0b60161004a58010899441d044c0420520001321451240460100710041d01440f41c9801000180e4980a0602c0c00540324a041c410714007842c81141d01c2e00200821588096101c0310340300358110101603907140c0b00d082c2044581c105108092040d42180000b0490a202080c00399040500750001c0c5215400d5201074809080c00030700103802c128102140c400400c0050b400d091402651208410491515041c41c0c080503004004501c00c5901c8550902070903212004000c805a800943c41c040e8101611040800d6110b18030a14817114004424030a0408010420b44d0840b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 983330881 1250 983329631 983329663
    0x51e0306030708032109030c010c020d021b010c0b090f0102130905060d1e111c03080603070302031f06080f010509070e09060406110919060212192f 65
    0x4a90343e203c183c0d03032403095500103e603034000c4d01404504940d010b000302c1d4000c1e005c03400307407820040f0000700642117a8200c020800142d00c40c9441010030768040c0078101c203c00022300d480303800d0500500041c0c8030740c841d600010003000e1194001854000c003882010300030651071009641d6090b495901c513001c21458010581c4552414011840524003248083e900d168004400169511803c003640c000040c40b52040d1038100d09900f12400070b90341ca114000b4104406aa82c003032104403810024044a0020429070190780920400d1015a0b0002659074881008241c4800fa0140182680c00680b036150300411880c4106210540c0681040d000b403881101c1d80002c4603000d07a5900034101e0420015510781d907043e005038001c9404508940c01070302c0d0004030581c180f454000b51601080001a1500000510440300f2400340407480d030500a407a10300c030030780e8801400c0c41e0a4680703599140c00668050700500107200f010400c45d10030b4a80c8000030760b00240503c400c21020784540d54076200782440100c05 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 983332131 1250 983330881 983330893
    0x32a120212120c070c030f08070b0a0e0a0605060a030c0e1602060103030e1903290705070b0a1d06091c030c0c110f0409030c020f040902010c1101051e030603 69
    0x540c1d403582095036100c0e014894800c0041d100c825584220743d114a2095951101805021022681d41d0b001e18501c0c5102e0302c5095568212402e040021801c05018100014100b140c0d4110b90600001d124200715005440040d45480703440000d100051240c0c4010320004c180400003509240c010a424401c07440d40c6d076408110500c10b1001c0361600d2003404010040361650b2140d1119091a00340c00884140d40350001e10503640300d0f112500c0100d0b444107401d0100d518001c0e030f20800c0380180a000e41000803070900505001c859507030030707050040041800551643d03d035501e8a28270003444981d850810724405850305420681c8086403140307400c40d100002d14043e1020a040c082c824411303100f04050075a40d003200c1d04855990b10000f0030036480d001d580101c7c54902c0458030356440c4251040c2d0351103030300d4152580c3e450f4410b00009a048000040c0710f94035103080e010250340c0081c20408060781c404004076044400c840141c800340907800810300d920305c0240c0840c0112034910f0003140120002c40c21264 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 983333381 1250 983332131 983332153
    0xf06041b0e040507020d0804120e06040312020c0103020310030f02040b060a0507060b0a03020d0b06150a09030b01050a03050c09040516030309062709020c0718140919032a1202 77
    0x3e62080b146c0101c4001400403400a070201d60440401e078400d0603180b402c400142a201c1c001038040d04150016660420310312041e074021034040207400f0030b400b420b003429130652500382030346409104070f44005001040046071580031590345034468000404c004144680f01d0807281d1009000b6000110120f80951501820035040e241040b015003c480d4020202003040030160f448025010014203107a42040c141440000502d07003a00190000700e143d55030b40c1c06002c2c40c3d414890386001040e03014038040c4451940a00114101081c0d83c2e610000540d422081c1e07403510f01d01203142c1040f107454541011082e4034048105030b8403420000460f166a43c1e8030802c4040105141c504043d85040700410310394864003000003d500703401406203c802a000d44125680c0d401e0101c00e41c0030551100100191780d205000c103280a40d0103080d0704100014014a6410401d00c540301d8402d00322280030b400e016180b00003e020703000740804410140c4e03040340c902103020513a20b49152010b000a6a0201502071805641 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 983334631 1250 983333381 983333383
    0xf090102091e0118030b1501090305030a0503130812010e0108010209130c0509030a15051b0a1409120a05100b420306041802090f06041b0e04050702 65
    0x18070014004002c44070030802003800700402c030106410300d0b040c0420700c40010700c010b5030b088141c030095016010480541c9080c944006404030b181c111a414041001000d0004c59030000030707109066400d00708259640c654038012000301c00c20308001811840005000e20403141403600340e60480e9070010002840e641c8914080d0300740d00689409540092494803030101c041000d80040314040c159043c01d0f8940008103020901782501001c080c0c825040d404403c0316004a07600c071f01ba501c080c0c4450380411400007110203511910404103010100281d41079441d14441c040c80444d83c5204000305040f15000c5212000c5071191025041a00e40e03005558a01c4600c003d01c0c01450540800240b0a0000c580c45020609070b002c858040300d01905407510082d600e00109a40700107071408800403094880c030307141b0100415581c00b03c419651208002c01d42d0f0005846041d043da40228000401e0078050b0364440c04240201a861500c5c241ea40d004103000107c2500140d822070034203010f4a00b44056940c0d45416 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 983335881 1250 983334631 983334637
    0x20d0b010807050711010509030d0c050f06010810020309010f2405010e0a0e1e0403080415140109020307030915060f0b070807020603040602041d180106260109020d0b0f090102 77
    0x1200420320030002130380059a4042c880805010504041d400e02c000c41000c603142061501291011600c10800003040c04420070584c04402c44240c0141555030400b04288c1d104c0d080c1c003c2e08088a40c0102c0070403985a002c1d00002110400c2440403c0b0910200507848082c40350404100030b803044030080402ca551007a0f50207032110b44082c1c82000300c91310f00045683c56140042c00a020300c064008841c14040403060824040d5010380e856070310509043c107080000c11150001d0f0341070340340380500c00c1d1054000710201504541002c1c60050702e035619034000307030013600003404001d043c449030b60b2100d2921074242d404201a10070f10780140c081e07603489481004a51140c1381001e024034406000d40c40051a00d9001954460b208440c05401c01c0d41d2110024460101d4401014071005144200194005080855174410440c0300007800554600f03158980c4503911510003811880311117800d08a24002508080c0005a005d8141d10850700c103820b149a0741541034440710300c00d803114000b2606040d414000c3d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 983337131 1250 983335881 983335891
    0x9010b0a06051c051e090c0904060b0f0d03090f06170423070b0a030c1b02010f021f15080f0d0c151d010e01180b09031903020d0b0108 59
    0x24504000341014420b490303c0c0c1210948011001014040ca50810801e00656000d241a44640e9501041e1041c441504550040404c1d1083d440348480c0314059584040403500a40c124078006005800312000c16005640624a2600610b80d0380b40f000030140e00c4203c5d4804c0b140340c0f1542c100c1031612210111142c54100340c22010b6840c41c480410302207080e005110854842d00f031004036512059501090604200341d1266451301d0380401c18120240e09030280c90b86000e06440c00c00d03100030040043c0e010600c00c001c0c0213030400800c4281540d204c0e00030001000c42000a982d0a00d069514404503805054000500811104d13125000618030b040010001d40c15440c0d24050060240e20341d0342200c003000c25a605442d038460390301c440c1181c0d541d6072040101c0d9070115510400a03401041d9090300303542e0100b01c450810303807401c0107a9800310402801c0b2003071541e00c045640b07007549442482501d1401290104401d900101400d8509182c241d401011000c011517418800306401d00d00640d288082260 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 983338381 1250 983337131 983337139
    0x608030c0318010c050f060601120605130902120708070821160c090203072006070c03030e1501080a150b0108190608300304030e0d1e031709010b 64
    0x444114410507084010100c4418904018040e135292141850804866184c04203900540c00f8080c0030b580c402901504650501c000340070301c501e0440400e0056044100d4456020755a100740300c119915020906502540c0c20216805243c44044280d11480c0b244110700c0c140c46010840d100031850000e011030b840d0204080c880c10940d281c0010811030f03045003001c4540f002c41210215600c0c00350710103140250b0b8613036620048141d040103800003800080c0c91350140d641c88a4100a1460b40c40740080040750385c1440c01059844060303440d1817401e085041010300703600300c0b2000803e01460010b465010103000d064800503140b43c4c41c006100b00d6409030300310f6000070b540b03e0008001c03142441108581e0a14007800254042d518841c8900b030407110f9110303840000380c0c031030b4082d80e62884454070031180c2003440390740d861403c082e43c1c007524800c201078031107024190040c107407400e101909400c0c0b01c544c0d120000444456440780360051822900c0149091320006c0403000c1800c1034814403444e5142c181c050 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 983339631 1250 983338381 983338387
    0x405040308061027060e12121602030f0109020310180308190c0519110d0e030f0f0303041406040b0606180402040b09090105010c0309140607050105070f030608030c03 73
    0x4180484486224014014016103541d43c40d6079004c2c1d2030108010b111450240840e039424248000c01e030f040842c1410703104034105100c0700722089000ca10001381211816140340e4840340114085211044500060b5060040070a0807190900640007441254800c41c00da46068003004d076803c04840782d00c50b00e010b4540c401018800007a000c0c0d1501c44e00100d40e51460020610f03140e800d607094441c100820b10000d5000300c0c007000031082e000405903035501703d400c040160394900c60543d5139038121804010104070100780c2d241c8240e00c0038042c40540501e035034143c5020104d683c1060380d49138402d40c0c00700c9074000e401c0e100d040e140c60045540b5002d42d52003001d03a080e944481007003160f1504074410030201402d2001d06020319580703d10090004103404150140c844030003008000464005038001410f001e080c0c6841c038002075020140106440c1507000741c402d05264034004c154640a100030042480d0310b4002405403150308030390b044010800950381031100d50f803900801a224014403020031500d41c018 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 983340881 1250 983339631 983339641
    0x28050309100c0e04020316120905030f1614010605090a020f0304061a190e01090509060c070507030c090b130c0c0201050d0e03031f140a0e151e09060405040308 70
    0x2a0401c0305480310a14008200c1c003183c2000070102d03403064618000500511407484003098001c580d030034500101c80350403c00d10080f070301c03201c2d00c80c80750808d0148240e03800a48801c91450084d40c11443d160420307109070341a11480e0b2040c0c000c200c07600231b442c802e48900c000a021001d42c2e001f00c4250040c403944403030950311183d0703410015214140002c41c0814028900c590591a003001e801c00c280181328888011518140e442e405902e0181c02420545050004010b50b04500160341c41d00401502d00031952a0043e050403810708406805c0100460f00029000418828030b400194650344c08070390b10743ca031580054036501111256580748002c40d220320780110156000e1000f030103420f00742c0d00000c030300703042c031042d410341140c1c8102d40342c694450800c042200387d4007a40303030007001801e2103500603144080314000003070f000607081c800c80c82c100c4005800194084588400d000d244080a018413024041e04210b540003240a00721a901849541001070624580360203007074000e41e0591250503650703d403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 983342131 1250 983340881 983340913
    0x705041802010f17160818060105091b0a1e0914062203050303090d020703080301150e0301052703040506030a0b180907140d02131805010228050309 65
    0x11001d030100c28480d07140008074003290003000c0c071417040c2e80201189001c6000720201400304030001c0e0119022854251090340950000501d00d4151001211038081940d03c100c2c8902145e44070f40a03201c007900c0041403130f61030150840d102525560340c04409d09450b00340084106c84400441c45082d040032088107098060b4109a0010081e02400f000d5860311030b0388040007107481c0c180a074402c07159603100100b0001c064805004000b00a003041c4050440e861860721100c90341e0006005019440c185014816031240c050381ca80310701804080c00901062a094040385010242c17125600d020203800c0000c0c5100b00800b2080f1001c8d60340c0200721030b0458070340c62240c500618411181a80051503040c50760441c10100443d54815442c5100401c040d90030400480150410800d1840c0100900c0c027140c801655601020340c00003040400020340004040c4402e602c581c0c10502c00b421a520008104651009145290540305401c100041070546604411101403008403480d2606800c84440028241d031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 983343381 1250 983342131 983342147
    0x30815030d092d0e07090f0b07021c210f030c0504172406031902031e1908041403031309050a090c1e2c0402150a020f070504180201 58
    0xd49801034541c1401c80c603a407882c5070743c02d5401c50300107581341808204175076074811420310103060703030086521940b0b1070208280c0290140c600000e100c3c078014050301c18100c00c0d88950300403642d0015000c1070b600d540155401d00b00c1100e503840c9000a4146102940e07100d029008036810140107548e546d241c43c1c60300209003096032072018403001a01841d00411495440040c01c10500e00c1d05046240c41ca061100401d86000316813456007480040c110305000140e58003142d440180c2e241c104000d51207400d4904002e041c036031107110003070410045564200c140007255029000f175801070002c51030702600e43d504165513405618918441845030181c03e01651203903170070850300b100d202c0703c0100704000c0503074070b1a5400c0803580040194081942d03916018499815600c2c0040200a0460491030419142035045d07101040050b019200b0f240007003001c41d160064241c5020501010349600d82c420100b0094803041e8108680390349124224001c034051401e44a81e80c01046000340342520b5420550041d150300c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 983344631 1250 983343381 983343419
    0x1080d1404080d0807030e06040807110d05060a09050705090105090711210a0806010f05180105070b0916080f031218070314010f0e0307140f0307030815030d09 70
    0x260007400009075007841000031000807111078036103d8003450418401012500480b02c05821580300e41e0a01010a0070502240d183c180c10001e0207054100006c080b405071042600000c10509c01c0c00d0401260a400d036126560151091060351403032aa00d400b040030f060001e0055590014200c0081900503000c0e810440101e1001c81c00e40d06101601210300f40828035070540c031007001c3c000060b160b041c0d5500c9200c041d401b0b00c2c00d00348491000c0c1203030300060140c02104c92003500c00345010780500b103580c007900940380c0c195400000e122007440d05550301d644510890110400e5501c20010201300b010010038900a5040500300441c1052035044981d4046003000d01350509101c2100d100c000c182000b40403000146014100120904d00d00d14003090844804c0c2030981074031458401c01c0c41c0c0d500380100486280c25041000c6034030200301f1003483c034209009042255100d2100142c080200350f008010b40341700c1d001040d0701c0700c80b4041100500d6100c90381605014001200b03250140711030140890840218 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 983345881 1250 983344631 983344667
    0x30f0604111305240a0e070801051302180f031203010b0c07150e0915090906070e0409020a031101030612110f100e0d0804050a180c09080a15141501030c050301080d 72
    0xc1640c5180540311071005487d8803000500800c014401c07800c05c0c0040c1c04580a020204615011004043c00e5101241c200710501c201c400c08014841607400b04502602100316400803542c95940b65500d804a6020600300111402085000191030b9100d507174010b03288810b40c9585d070340307154075000700300e140341c00100501e103c00364034601d45500d6110946e4a03841015503100130001c44c2441c1700040e20340003010031640d00c41c6092003c0d020060301c610b00ca1404480e40001c44000013104800180c0103000e103a040080350024440600090181c2c40a60a00c200007c0d201c007413030700d44410306019920b5100804500803e10014a01c44e59007082103c400700140181c080c0d9040030388070b00c0010281001a40000d15284040c0d0506031000824030603882010b9403030401803072161508812036101e5003a400c1c05001c95554070040c4092211907007200500c900d5500c0c1e400d03080e03d0f040074140c4500000d0315402d40000d01c0c0034580c4502c940600700b1641a07907a80c500800c071045110108683d1205280310282c10 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 983347131 1250 983345881 983345899
    0x909090501060905090303040327030221030a09031b0303052502150a1103040e070f020a0c030c060201201e0909180f0d120209030f060411130524 64
    0x1403143c03489054002c0d4001c03c065079403410315003002040c0b8a1001d1010200750b40000251710707640760380c010b940121380d8180d64020b0019100e01c41a0943c040d00400c20020f800b0009581a02d81d60010b02107041d81c0c482c040742c40241907200702102180e80f0b00e000040100c0c6041184614000358a10016002815461090340391141580411640c0482150446d440c082c0840c4102c44107401400000c0301c0c4840d1402135042a2078408000341910020781030307905028a9070022481c591082c001c5c0103110742c00c444850340d16a80c9262070003070000305104840040d4640781c07401101011240c203461000300c51004440c2007140342007a150003e441c4004035401d0443c100043c03001030b2540d9011314401d1800002840710022941b4266003840343c2c1001000031a000982001850f42e0429541010034406a100581350741203480480d103818640081010300b88a240104006c00c40900e10340700000100796038241c1010003c2d4114815121300340c80c0c1e198482d07980c81020114404008010944204c01410303028 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 983348381 1250 983347131 983347139
    0x206090615040b0f0307140a0e0c09042c10060b030403090e1909050a0c0816260f0c040b0103110d0f0902180a0b10210f0212090d030b01090909050106 66
    0x40386c014103a010710304c01102c018810141e440d00c1e5091000a103103d138803804803407410841c0000584544030005103c1c03903555003210004543d400010340c007a04c4404102002190140c1c865584601400301019102e060403004542c80240c0400e6a0083d5810340b141c55280d810000c8100c50648024608000c0320040c0d004454060744a008944955014502914003c9080c0c204600350488a4002c15031540c0040c0b8001d858580e84915802154059140352969641a0503418030410400351440c03081e124001120288410211700b80801d000304a504000c0700c860080150107541c040700c42007010710402e106007074044031183c02c04901c03442c40410005010b2042d60016420a054005481039001d03480100500041d0a1042c401040001c5840c0c103012915004010810114404030a000e020801c01e4944a00035a400c4481c0f2000000b0003903403a00c8003400e640c0c0d0300040c2250300c4031103482010740720b10106009101d4090f040c07030180e6414408034108440c040207420003040403161036582d85000a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 983349631 1250 983348381 983348383
    0x2011205090f01180506010f050901090b04061703090a0e0106120f0f020c03040f1d04020609040b060a0f0210020304111e0406030602041e060207051003090b010b0a0206090615040b0f03 81
    0x20f4141060b140704c100c180719241442454404141c0005210320034000c803d000d50fa4403a007a107811030b42f40500225150b84c00d0000305c0c020b0002540041c2c0380003011200008440000f001501017000281c0350511740f81d031303a501c00c00980d000a03c6500003040161110b4140c10007075400490458000c903601040c2890742403a04000c03a440509045000e41002c5030a1000c5120003100100400c07501045444484807030090040000000c0c0001784070342400259a41580c440707420286004d5070052805481d042c3c40b00002c1d120f0f0440d0f54407100103000c1d0200c0d48140c1c0f5240e20036a80119006250102004002400e00c84200c05403001206103101c40c0341c2c41c4140d640c03540100c0300514810320000d611180303098402c4d1249404580b0350004085650410f101c12607000500e402116011114941200b10902c0309800600d01c03100003070561000d220010585007005002048a001541d0884945540b0303500d482d030315040c00361562015007045690392000313450950841000102e008103804c0310001e44c08000303 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 983350881 1250 983349631 983349641
    0x1209051f05031f0807060c0c1203052b0603053702040e030c030406030b0f0402120403030c05040506040b0a080c12040f02060d0c020607021b0d02040f020f16020a0f0302011205090f01 80
    0x56130001301f84c90010010000300f840701d0002480325111101c80c01c007150ba005003490040d80c0d1240058250f1044a031429668003e040040800c00c600c104803403600c074201036885118200015214203130100302003211061000d06c070301656074250040c0840d4803040e401c00019103c261803901d0307a48803d201e48550410240002c00c01010541c6000607908500e200348460f80461040e0325104510500991007011540d103525548140d1620b0002685d0200c00c0e400e035058001c0c1e4120343e1f0450310108001c118524500010046030480d03031165405a642e180e05a803592003408540a5280000700114002810000c8444000d034401032a0509083c0c038400340d2400ca6449213841d600690003207080c330980c0741c4c041c007001e00c0e42e1a10585206407902c1c90008908100381000307000307000359034445030b0007400d45042c0c0c103495031a02000c490b03959501c69802d80c40d101905014050740725200c803844c000b540300c80110700c0340c08581e03046e12441e83c07481c100080709005100007400070027140a030ac8400747d190380d000c0c420 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 983352131 1250 983350881 983350889
    0xc060309070306140f1b1c14060904020a0b0a020307060203070c0308090f0c01140702090408040306140417090f0301050112060f0b0a170a1209051f05031f0807 70
    0x700100d616508061064425046410003010b48201c01d00071a100254401680001b00e10703441880d02c12614032100d02403143d0012003c3e51004c4426042030341c2100e03002103141280000e4042d960303485d250104811001e007540e000b984040241e20810940c136103480034080e9112a0b00550b42018029100c03141a40e20480344140099061a0010f04040d004258560403081d603000403c0c0c8440d1080c08159a001110341881c140700b0600c1e00184e0603011101218000c0e41d01619450160416240082c9990024041280e00ca410600c2842c003200d80c100380b42d0700c1143c2083c0782c1d041020140b162016158010003030503030092690083c40c0c80d0798809000d1035000744900d82c030300c01039540340303090000494110b40c1080740e019080070030403c0703542d0b40cac500440305550024440303194aa507a00181458040550320081901450f0458546078070340140c0364070f045550503104180c070301e5522407900d81002e24089007a0041503050000c80c245850500c02c09100e080c084489007a01c5032601110b51403c01c103a88 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 983353381 1250 983352131 983352133
    0x6040f06120b131d0c1e0a080a050706120b03030703121b022107022b0c09061505030405060408031806130317010f030213062303071401140703020c060309 68
    0x7950139541101c5207030b0400043e4580019240c800050340c002184010b4030303101892107440c10381408815a948440aa00400307086088030a0407800345065600d071451440703540c0201d1301d030340d08200c0381007031501881011440c002c01842c68603500e55002c0e211119842020314510b80d54512804a41942e43d081d5032404600390020100109041e10342034018410588a0815403010f20078280143c803507003a94039815000d40100360182d59840d00b000c070031006807900034040e02448040002e00c454254012400d80790000c00f80300d80c04656090603161880107850041003940454002004141c0e900007450700818003049401c2c100c08600c805616042041c0e489a134002c103098407a00030550410505802c0c43c4000c1e81c002c80ea589040c441d000741c0c407503920021340100d18032001c581d0780c490158070600203486040035405c04c060790f0b5100d206410013000d0215009215242003c503c8a000030500f0511102c140d4400e100700304039090f903042d40d400100c2c00310154420f00e03440e64025a584800380d8444c2074510 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 983354631 1250 983353381 983353391
    0x20105010f050f03060f15091003020a331e1706030c10030902030c040c050d200702010e0a03120503040506010902040e0f04110a080304060e06040f06120b13 69
    0x1100302018481d0356000502c00c0b000301d00201d8590314007094981c2e0100e14040220080e6480090120509040081031580400c02c1c0c130402c0b43c8465041c02c41d10030b5a0080d61500059a192100d94008e200c207402c2d560b504c40c0f00c105c0d0080d514417800e54116007050721458481c2d030318001080d00c8902c01c41e05c00c1c0f8540204070041c40e80f05c2c0411480c2045503020301c0440081208142e54400305000c28142da0b075080802d5103c60b402d80070340d02e081012100a800c050020080103c42c000018419000703054511201410f058214402e100b078400c0c2028450f180004c8140741a10340c1c0d0064030800c40d4000c18680206840c01700002041d000e1a50388000d064507101c1c0b81c2e5030324107460440e081c00016000034455510510080c0013800b41040a2541700c060300943c0d4030507458501b45202100c070342c10300d410303840000810046201c00000c80a0011206c054982203078410050042004070b004a008001d014000d04604104040c4510400c006004265a0010f0544240000300d10302c0050007410000703107920340d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 983355881 1250 983354631 983354639
    0x1140a08030d021b1c081b0a0f02010507020d2a080f1e0307080402060d0914010c0f0815010c03090b030a060510030902090103110a080109110111120403062a02010501 73
    0x900d28514000d10100017501c00a0b400d2a4429101c041224a010800000d4070000e2500c1118148001d440c2000e000408d417182c0c010000100341040801070701006500700004200c0a900000342d04440e000c268403061141c802151000b80c031461082c954005aa500704450f2010804480040c03d041c1e0007030034655501d903209049125010715005100d03501120030820083c64540c000c403019003080d0f040f6045540e40d410728200d42c020b0002100e0142180c22590b030460550f18055000e42214044da450321000d40c890000c042d114000104c682550400442ca12418258417030918214803e103e03080c80240e043e124009045150000c07182d00141c2665520188031501c1c0101040c400840349241c2400718901c10f81c0492050705040c4001007440941d5003080180d5a01c41c9140b0b030180444200801c081c0549086c90000c0407403c040f61408105c070100c4074061000041a00e140e140701800300240390034515175840703000b00b0b40c040e541f20310b441488048003504200f08001074485085540042015414 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 983357131 1250 983355881 983355907
    0x516020d0c0e07090602071206060504021314060a2015070e1305092d1504020a0b071a04061103010e091506100c02030a08040305060703050a021201140a08030d02 71
    0x102400f01d0303052018040041110700d60010f00340f001da40c000c01154400001c940f51800281141da040298018001702c2c01e0041800401c00c41c0d011600c4107105a0309243c410010702126100f0540c4000c00034040c117001100c00125011842116280c0c5400c44c1c10100803001c21452486d400d54805001610a48040381c8600e44000ea40200c0100f5240803c43c500b012110b541d0303141d00b03d00344043d9402d0284111188650b500601400b051510015104003080048400f49008c1088800724411100400c1c041803044055054445031139104000f44903c250b00781c0304c5180c40b040100300b00c6441e5140c0c240550030f00f80c428080c600a05440300306241c6805c004008900f440c0c140074200f01340620704c10400c000e40d9602c1e03414407004503030b50801d0680320ba007070b00200e81030003402c075400b40518500080000c1040f034001107040c410aa9079404001a888544440081c0d11401582c0142d581c40c1000500c4070f181c1d030741000c6074a423200524070300800782e076942d91508580080341d070b56000c00e071f010643c1380c4007042d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 983358381 1250 983357131 983357159
    0xf07060e01060e042a0f0302010201140c030c07080d060b09010e03160b070305040b040605190206010509010b03060d0213020a020c24030c04082a0d0b010302010516020d0c 75
    0xc50000b446200d0a18030003103c0b4a80081002c5c01c05070000705c4100c3c0d580c101005a11183e401c503c46081025120240212000c0c5c0c144001c034010340c41c00d655070a04481030380078103005d141e460381c03180c3c0741d51903264a04503550020070701911246d40c00c2195915513005486003034000c04400e49815165281c450014010b847c0c4a01542d010b90881c007140c00c92a018030701980d060f108440080c0380c5880e107a09003281c035405035800c00051400700003800300e0701c190000d014003c84a000c210034200c1220940b03080342c9a44080c4200d54000300c983d4014040d070000c1c00003565000e0800340c92000302407000e4000400010b410400f2800c0140d0002e40100d92035814072941131052002e448014002d00c4103618041020300301e010607640040040b010841001120b000c0781d00801074001101c0d640003100700c0000407102c1104203000c9404141840f45030608280403c04005900310010300000d80c61600191050743c001110010040304a1040100581d24002c440351424007442c081e8180311309045800b40180 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 983359631 1250 983358381 983358401
    0x31c05090109030c060c03020412080c0115080309100522090e0309060f0703030902031606030b0108090c010f120e070e0703090803280903020d08061912170f0706 71
    0x1034100b141c02004a40c0010030070169584c0001d002071b0080b01c00000320024059500141000044127170700d1418400d854000d0203556007146d0081041d440d03c10a50303101d00da928410011150414802696070380340c8000083c51011242c100707149031203010141c0c0b40e4048900012080924502002071042608520903982090a42001180b03403c280d1000520b0034054849203a50b00440007443d8410907119802061450b58090b048505501c0b4000d508003824040f409002d00191a210030610b0542c400c4900030b000700e41c080041c02141403030200450b4111103442214060104900d10445030300d1a42c0f04000c4010401805890150b0030060000e651040141888040500388066280811030160489401c10f060741000c005d0705070203800f96601054030402e558042d910307144042c0c0900d60007080c0401e5a010350b90740c52100396116010003000340011b01200b414407034546014010701d070030b075000c14140314000c00e003e40d02c0105d900504403c5610411500e0451480812420104049401400542 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 983360881 1250 983359631 983359633
    0xe0c0d0615092c1914240112020d1d0106051c1a07020a0501020f0c0d0c051e03190e0a090207110d0317040b0105150309031812031c0509 60
    0x2e000010120501c1c0c12000c503284421110034008a0b9828034101c00705801a050243c05000e0600c004441e580d213043e04452040e2641b130100012140810100d00454a8000584410b1900401c0f07941038402500184500b4940c01c0d42c1d05480d07c00e0500c0d41c070140c2e040601c9070002092484c108810703c05400c000ea400c011a1f944131036004c0300041c0b15098095242900400c40075520354a0100417858003040319000307411544002a140031040d25580101080d442c2c140441c0d940400204c8126010310683c2c10280c03050308a1490140c200811500c0790300e10382c0b6101c04513407c14820036120250200032041840c04188410032501c4541440c818101c010005000214105403640d200c244a0034025038059100708a000805c1c000c05000b031002000b1340c440c10009085902d064605494210400c0c05194405d03034402590135801e03687c501c1200d1241070540c0145041444140f9814821044038000d41ea110380880400801c01d0410005007100044114040c106042071180543c12030f08098581e04507 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 983362131 1250 983360881 983360909
    0x10510081e07090b06160303060e060603060d0312110c0a03020106080610060e1c06200f0d0504230105060910060c02010e01030f02120603060a050609010e0c0d061509 73
    0x30078045004012503001203804030320071003040700241d000d100760030a0301d03800100b042000c4141070b899407004050b01c0344590b410426445200801c40780b4042141c8203a84402c50141070741c00039101d2101d61100340403285020030510035240300c04a181d04415501c0303615902078400038061690901516000b407010801501150920b44651392080c1c055001d004144902682d9000030340c2c5885600703450420010042001d09070f8a483c0603005000388180007a22100640c5c41c0442001c00701c42160941080302e21807a240021041c034210190100800541e08500f00c143c4c0500180b03503c8070721281071007460307000180314a8604c0801c0420b80c0c004c0c00d1400401d8052005001d15500103810036400c58090804404a00c03c070740049015102047d22100024008142c100782c0c04004084680a030400700d05441c00c50703464641c06000c44108461696118541400401052108130b41035a000240b0b42155880e00181034885003d40d2096401a603120043c80c040280c41a8001d40c0040948901d10103060 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 983363381 1250 983362131 983362183
    0x412031806110d1d060403030c02040b030615040504060608010c020601030317040210030e160b130b030609160c06060f1508010303020606060c01060306181b1508060105090301051008 80
    0x20340d4440400702641803101e403030301310342c0b850103c41d54419035240d000340f1041c1c1d955200c1c41c00808411020780b04a000f5400c0007660302e51480c0200703e07907102e68041c0e103c90441110080400000c1c10026000341e901035030f20440443c2c0103d0138022130803a821a0740040c980c40d451440c0c0104040c80083c0d00801c1c0401d108240001651007241540704040c5901d000b160508041182c54100f40345250b0031465034116075000540000d00c1000391a0325040b016003007550035914900161544422a400c66000c0ca0100c0001d40030280076203590b4010300e061070614400503071580c0e4801203c0c0d0603080380f40c04400100e01003103680e500348002401d03801207152005584d4503503500a0741d103110180c01d4078407480c030104d015265403909520020080d40c10060038040520340e60000546c007030340e44000351441210f82c0e091540074410300079008201c460000790055911050360088410b100040d000504210003005100520782c0c09026480c01165480d118a13000e45c508000310b841d100120012600454107001405 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 983364631 1250 983363381 983363383
    0x8090a08150c031807090522050d0315350a0f020108060f090c091002070f0e06010c050a0311060907050a030803100305030427050c0a0c0206041203180611 68
    0x780d0001c0c1901d214648940b02c540300d440b42040030000704079680c031415000140035021504a10300554440d034900041c1a00b10902400000000074098425807013010321147c5c0620941c4509a0409035441009041d030b15204000039801c0401d062504451324074958032004000148018401ca000b1002808650f04a03902c0300c02000709208040e0501001d000040c1c00c80d120250304c403140001c010624038151406140c1090650000c8220030700501260b8a070040d141d0002608c4421b8a0400c901070500c41d1a099071101d807100010136150406c1000d41c3d4400c005241040f41c00c000603c02d49840154001500a484c034100000b8403401d1035500c1490200050307244c000e8031a090301d402000303a43e603c0c0c3d0341e900c0c882d02404141d40020104e00c80014000740a0502c8015950391407070441c03042a00300104a407400c169035042d00c0e150a200410040c0040f224080d51100f10b5051010b01502c0c103096036820522080940e100c1c0c2503011440400900c1003022442c044040a00f0301400c055000800c80000b207 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 983365881 1250 983364631 983364673
    0x9010b06070212010e1f050c1623030d02040e09071d1005061908150a09020702030a02030604030f0e1e1c062f03090d1125061722060905060408090a08 66
    0x103001c0c200030701040110740a00f8510ad10551341d8000840341d88452075201d00c402503200c0d20401802e41101c2011901041c0085680702c100c070000184d5a011b0300440c8400c16103190042e000780200c806078000002c9548890000d0710340c589183d00d110096250040d0058104207004280001145c04048251a1039485c450288265040d0400040c4c41d003e880c07003c42c1c54a04045000303549403141104102c10141d000d40306500900c007683d1010020310245060060b00c200e032100c69080c06217084c11740308482c03d0541d6044054080c000e42242a11040d0301c0f504c0c2103d410701c00080081c02451110381d10444080a1203074944540d0783d9007413451070405c404a44035004090508100101321a0ba1107200c5c804009030500074080fa000702201c10048100062150854416440809c000c2e03111402c44102103001d10b40b086c0f00b03188041040b1000c0140c0700400ca00700340c00c00c0341c0d09a40e8031190740104038204241880707a81324580299941948004001d001e007415400480c4030740c041300740503003540500d041d1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 983367131 1250 983365881 983365883
    0x4062c07060507052b0906030b09010608130f0506060a060c020a0510090312020304050f06033c190b060408030a0311070204020d0b040509010b06070212010e1f050c16 73
    0x40641c58090b41e01c0c10038117052400041c1c0c5008005c0c10425981210b0720b12214041180e16202d0203481555000c0a070150703100c2c1c035181c86c0d002c0e4150703004110240c000c0324040d5208030b4952408110166990303403121050501c031425a400c2e44250108001c50801c0401301c0003a01c01c0341003900c04211554006281c061441c001c0a028a141880396854640500700ca44065507000b0804002100d441b04025581c0c1c01c2485403511841105616100d24109502101d0040040c0f103249107084030113914a101414922402400000804103210b204403c0842c00c11701070000510011140c4600b50a1202aa440700769400c1c0b04082c104420040120000101c80d4100810304000c90001980303080ca42c014040c0d1840a0f40041c00029101c8408145a1155035000011101003280381c6030401c0c0c0d942211003070a00c494012404103c000b000d4034061059440210903580003250504082090b02d0800a000295040e40e4401c00380e0000c4142617401403503031020707075050b0442c03d0501c1c070034003030500700c4030810 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 983368381 1250 983367131 983367137
    0xa0302091503010917070506011a091210060909020a08030f1602031612061a0f01030e03070606030c0e0c0a0816030f020f071406060f1207080604062c0706 68
    0x2022100d02d4900390040c2c00f50f00d07000350701d00c016a0004e801032039156000c3c4030111101c3c0940000400c507084014120901e41c01c0e024807241c14140d1280520080ba01100d00d110468400c000f10401c0e01c3c0700c50700989000d82445000880e6045580c8188000607401d03400c0714040d50020300a070845244c40342d05481d1603042101045092100c50b00219040003402c060a80e44070850380c5010400c800c00c817142452640c444c5a04110b42d454030720302000203141c41e040f41036101420002c09842517100346c011b41b114584110a89181007456641c100403940c00b039008844861a82c4402c100320801c4280442d800210078100501d000105c1e40000e00700540101803000c54204d01c0c904010709803007940078105081c2e11000440d074551122203401c1d42c4e90018001290001405400c41803446004640740d03001d88009400d40c03000b015090200915440790396600c0380c541c418004009214441001554040c0c0c1c060003000a80c0768504a0508901c443c00f20000311b03884000c0c10700c02d02160005410000c40d03c20b45 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 983369631 1250 983368381 983368411
    0x10c0210050708211f091a090403031d03162307090218040605091506070b07030b01090501020f0706110c1f0e1c0f080c0f0c040b0a030209 61
    0x2400a5440c2d008409024083c0340001c03d40d4032900400e03070441e11622030300c0008025290340d24145100040c10031005d1104c602c50b802400c1000c2d40700b507003040c06240c541f4500452200440301c0854801002100c00303600107600c40001c9081e6050204ea280000500a005145810b2a8034a111040c40d11003c00030101e00300000356448040c040c50a0f070218441407410703103070440d030303102c244401030740140d0720030342c8900b082c82c00007085460148260300c21aa00038202d07500303e955940440d900d4200050071107400c00310400c20301d4000b40310002e01601c14841600c00040079076401d0b0004210350015088241558003141c5458421080003903e001202c0c00342c035054003003401d4040d03a2410300619141880e0801d2050320b242082c0903a1180c680701c6d8003126035503c100c1040800c2002542030200b01074079004401c61f00780b40082176100c0d20f020113240c0a40107280ca0400418409490a82012246402034020b05110042850315001d400c10540341181c0700001a03046800044c0a0400070704980000244a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 983370881 1250 983369631 983369659
    0x9040b0402010f0c0b0f0f060d17070507030c0603020319020421030201060504063b0103080f120c0309010f2c070e090307171e2a0706030e010b010c02 66
    0x14844c0c440920703512803031303061041c01d0540160000c0d60064500603043d8000400085013030030901c00521041d80c00c891044e0319114074901944180d0b004d90016980c500841c600400400e280d010104000d02d8181e0307005076a40b030001d0104041d4002e0320048186503004000401c417419860b400c946c4c940c14218a0641da081d020b241c180d004100382d9110300d4000c1c1c01e12800003071040c020520080707460303411007a41c0208400710402c0282945080c041c000c6000300f400061000c100d005000d0150000c28000052600540c0c1039181c014080c100ca07240c650344000000c004c83c4c0e613000e0141300451000717101e003801030305800c03c04100c6040420744c21442d0b0801480f40b04a0000c0104a00802402d000d4003144140c10418003464407130f4050b9006441d04803081d140010644814401c60320320141c2180005134880400d86581c0050b4001d003016440400703003104240120484032600c5244900c04030050441e54580b90740075082e0750000e0b45105069240c4448040580d801c00d21401c00ca541c1100c41441070554 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 983372131 1250 983370881 983370887
    0x90311010e010e0a060203040302031e0601030305030403050f030c030613200f0412110909070602030405060a050d110a0e061e0f042333090307120602120609040b0402010f 75
    0xb00d640f82952000c081403000602d20b401000410950b4025820341c0d200964020414022110b800150200355004000420201e40b141c3c01540d0818032030701c1e203d03142240d04402e014068009440500c00d00038008140141890280152034003951103e01c1841400c60b080f004c1c0c0180c19040081c03010340400081d0102840000001b00c8000e04182a00605401d40600301b40000c15101c1c024a0b000f9071440c4003240c41044006090742c01c0302c035035a0082d858141400240001900600e01c0c01c42400b1062082d5160060305001e402e550389002c0001d40d860364480280244040b03041103545025500801c91051507400540da2042c0381054694860742d42c03075901c400c050312403090350300004000104c424010390442140c508100c170258215801d440031011420420950320000c9491410004096604194110010050306140c40000e041c0e403100b95444a941383c070b030442a10f088407026400240160146181c610b41034000009a540c40e04901e400d54440e00c403a1806030000e8103100e00800e08504c101d00c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 983373381 1250 983372131 983372147
    0x19200310050d05010507030501080a0809040b0a0302030f0d08010f0b07060902121009020306010f05130b03120c1507030e15100b0408010515011407060e151602060601090311010e01 79
    0x14040e28001c54401541003513070080a00f40e9414001038280340001883c007400141c1c00d503246802c006158a014072001c1004000c203484082a07410000420300080565424020240714980d0000a0440c1034900e04004028440517007080010105480050120428007000d0302d2480f03501080c00598100c41d40001070610440da0000301181c8103a260441e0751a03020741040b80040e01c00da085650903602c80002814900e8280540d07504001140440758000b201608145c0d08100b01805a07030095510b000d08420319400100300c03e0144d40422280d00b114032217180d0840c0d016240d480d00f04031400020910686401e0305101001c0c1000101c00400c0344000a0301045004250440c4000d80e915075450076036002c2d00c070441e81c01c015600b030b0180c004a10750107020100c0514940100040c5000e03040c1e0768010007041e114400415510801095456006540f11010300070030301c00ca5501410450984020b180c82c1d00107028504229001e01c04100007551180f24843d452001d082607070f0703148140070048551103 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 983374631 1250 983373381 983373389
    0x1e01060306290108061813060c26070206070f110a031106100303052a06090c030f031201090f090c0303050c0709050103080417190b19200310 62
    0x149000811070a44202ea5480d03240201c80220924420540500640300c0b91004c5540301d41207249580b09924004250700010f51040a10001d8030f035802003a01c80c0c5003100c0842031020701140c0500c40320392903035170703101d01c0c008915016590100852410510003516420f01414100610801c80d10407140d190107502c9003621503004e40200c07020990340b0708008001c25451412143d10780104804100c5822a0b130354101d040d0f039015201c952400640c07651503c0d0714002108100d44604181006800c0d075032050081600030001d0800404072021400109070422030040c080e4089903004021000303241000c1000581102c10041000035403114030302070031001d8910b4040081c01c404a08002108240e00305d8060200d010048040300c107402d44429110f011a6420f00000d44900c0c401c0c802089040c101c202403044a010100c1601c0d070303001040f210300315113000241048076070580c03800410452141c10300282200c0c0b03080700820700c64000f03001c410300074041211601294500002000516100c03250110200030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 983375881 1250 983374631 983374643
    0x5060a05060f0415120c23090a03110a09050a050411030a030e01030b150d06090b030a030c080c1f020315150d0510080f010e061503030a1206150507120906021e010603 73
    0x20b02421b503001003210f51000c4e40e246451081c000c002e0411241d5400741c603104d51000e402004058259169080d404c44104056584400741c10400309585103107010301401a4001c180100705030501380b4007042c0e420340d00180c0500950103400c4510120f68041c941c0d050307140c4282000941742c03001002050600840409441c80d02c1c00001e040003c000c2164005412a0a011000c0210400c6282015140c2d2003051020380040e951403036120124060400800c1c50500c0241280c21003500300810100c01c20080e9407815280390301004001d44481060340301c002c2e8140032200041480d02c10000050140680390000c0d41340c41d078400008540796011405080504a41c0f000c44180b002024840743c06040b1507100039656020740b1001c2105240030703001040320118020302035410b113001113004680001005404001c06922000c001810300500240c1420f07181d056a907860781d584140c2000300c021440128810208850408200446d90380442c4011014003800000203c01481181d22400b43c1040e81000c1d100d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 983377131 1250 983375881 983375891
    0x9120406050a02161d0c040503070b1b01060f031410020d0f0e15070f0903081201030515090606041107050105131202010c021f02130905060a05060f041512 68
    0x112500700014000e0010b1590846221301d65840b4403043c1e040c4103101d50700a080c440c0640c0002500d80020440d44900d00d00348550819643d00e000a103410715685c043d038000140003c0c144602902d42e803000b034942c03410760000c0c820310f891304907061003a290510002d02441000064031074420014042c0800740041d10006640390070556104034018502c004141c0300310761500e86062003100011401c605400031446421646503140c1c80b0a8a089945082d04030402180010110014290001401d14000f4100e0441440d60562611078a8900300c2510309010300e034400d042100c1840c001814960210341958080b8421310b50714400c0d40f003030080c0d440080a41d4280006c1040010300708100340760640c0184081d40d490009003006038200d4203210140c000681042d0807110140841c1d00340f1030711102c0080001881e102c0c41d41111042c60540e6000100803c0e110000d106c081c0c6842e02c8114050b1904031b07400d41c07820160713020442c0c0d54072503071094680c0d01001b03504054100f4000e401f45c41d00090b40c2001801 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 983378381 1250 983377131 983377139
    0x14070b120c04141e190906080c06030a0513150c1709120d0f0501031401062106111c0b010206010b0a05090d1e060203071b031b290a0f0c090608091204 66
    0x801740f040303003c2d411915140150018032103000240010111501416a40c0b43d901d1301d045120203080024928403a5815010102c80041c40d084600001d108035000001082000444010124404e11020842210504062205111010942c103039201001d110036039507a00c0900340000a03102c04240728425502c1c102c0000148901055a0460155048001c1102c5c540721801040b4580758120f0303504000e41d1030f1004030006003e541c4030020642d1807031041402c04818240800c503620101760615207070394490300400010b5030100100da024011038070380035050900c20f420050490241c40750301407041c111404d08106100c030711018251101034000001380b001c520340c10f24401a500a4442c0c1000810400c1d45400124001000544040e0315507601d0044802c080040c01481c0c1c010389080e44d002d00958216080e6001d4444060201d20700f05040c4080d602c2d00c1c0c09500d040300c04581102ca02d03142001140f101e126409122601070f503640d802d200c002501c1e02d4480514007400f9803015040400700260200f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 983379631 1250 983378381 983378419
    0x6120703060f2702130902030603070506070f1b0503032b0908071b05090703020306040e100b0a0530070b0708040e060a0e0c0714070b120c04141e 64
    0x1c4801c030343c510085000c52150a07034004a1090114003690742100402c18001c108590300250b42255008048810403034a440002d030f000d6008040803148043d45803a12400c100e03011403820031031046480078560086c81c180201781c5074803480c03e04400c0040d0041d01d603a040040804440302044201ca01000f41e001d442c5441c1c0c100d03601c00c120951b40030069203407540312042d02042e02030a880010707010194517203030104281d000c2d40000d090300381d003d5280c1c0303032480d03400d84100b00000700d041c6031100c00300710155418240141c4004035045140602031550400e090242000d050a021201c00c046c510a41d254500155040c0560b039041140b9004001418000b44104c3c60080d00a684041400100355215141002a1540c4a204050701e42c00c0c4080051004020300d0040d20025014041342c000e44030251180e54180061a002a8604080072400300100341c43da42189a120503240502841c0c0342c2011a100e58520b011203045103e070300429800c00354480f00c0d070704140300390402070089a50400f031b006210b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 983380881 1250 983379631 983379659
    0xc03061d030301030213051e10091103061f170c13050105090307150504090213090c020d0c02220c080109150e010302090c0c03030108032706120703060f 67
    0x4003038003480300e92000c01000c1001c011a8101c0358001d20500220301c0804484025000c0103000ca03100c00d4040c40c254004401d0b02880b079201c2c04410349030001c2c4070300700501c8400f1100700d1801265810010710400c41030303031104901d80c8440003003d85080310706421100110b0304640780715194074070f80d1320074000d001b0900d03c40000392400b40c41151241144a85450044400e80148130090368103500484040000f02d10303540240c900d60681340342c828a031586411086082c0c1e48401800401c0e0007841400300046092403049040313040d81803029215503480c0600c0100080201007010740b00d40a080145204a008036000d0352007000c03c0c58044c001441c6001c0d003c1c2402c45d091007000d000909020094494903003103800310042e203281c009440d451740d0840e000c0c800d25410041280f008543d04200152400030100065030080030400d006680c0c40794034102c0740c4d00700b0070901540030804010025060ad89e03a10402a150041d10540c00014541d031103400490162906500a581204a191012809075050b102c1c2c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 983382131 1250 983380881 983380901
    0x3061f0903030815090411040b0d050601050312070c1a1b010902190819060e150109061a030f1515090102160f06050c011506053604090c030c0306 64
    0xe103801c01e0351000d04603110b44001d0350b03005a002600300c0011b00020904240c00300d0901020700700080071070b002c0010501000100200f540d9a0380100c0c01040549070400c503012110074028415418444980c0c3c90080350342c442e0040604195801034040c14002c05c101c1070300c0c10b01c891515410300304440a91050f00800051106a0180f140d4018088030f01d514442c8404c11a00004010228034401c0f020307a00c05451031804c02c68615031aa60700750741400040050002c640000042c0130841e5140004050407074840354070030312200808070100005154030400742c179405038811103412490354440c1089034144025019941e0f00540c44000403004c81c4555025000c9600d0a03000ca5410080c100b9844c0c0e40b2900714803c20b0700c00000c0c5041404034910031b8014040f00040c0a00200d101c124140c5145401103013a04118005207001c01c00d090219080050002d5030030b910040000e00b1083d80f402c20b22040305883c0518051501c41d544c00c0300308200368a00c0c1c40216002003c5401440e00c03031511102814110300 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 983383381 1250 983382131 983382137
    0x20616030302091c1a0c0a0e0109120506060307081621051204050f0603041e05030d020a0c060c110c09090c211c090e0c04180902010f020d120203061f090303 69
    0x40030385d040e0084c0315045000b450b0700801c0c01d007040340f0708204462401082c1c0c17031a07040052600000800f101c10b400399000c00f0f80b05c0c10203840180303012421302d494003885901242c420b5001c03a00410320011501c1d03070360056600b14409040d01c01000c0d425502c150b003000900404903c510b00e1180d50314940c8001810035108200c65039080c0050000c05c00081d07000a4130040c10b41c0c5656500c82c00002c060729511440d40b4410001c2d60704004424105030100e811242c1c040020801760600b41c4100840d9200704070f00612641003807140c410310b14040913550b020b03580c8858001c60612001c507012001c1009195502c44004020013041106408036920400b218608980984251000019220340381081c0600c4443c150f954880c60b0341c500308003002102c00103032880fa01e40e8001c10020600b05103400c24055801040c1001280101c4107100060080c44000d00c0c00c8219008200c1e10075000e54040707144c036810f1402c001301607142d4641d18000741551050003403400aa4848075002a08250081d24050449010791 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 983384631 1250 983383381 983383403
    0x300504020a060315090c140d0603120305090309010804060209041109041409030703081f03082101060c08090609101706040207230a050609010e010b030a020616030302091c 75
    0x3803d0b41540e601c0d850307841902c140410709000c05480366001c00d04460040c83c0c02040c00803121a003141c19404070844040d940e49480b014020b000c40501d0b000c600f08401c0c178003041285802c000c5161030380204405030381001181c1000c00c2c18000301d5019165000c90041003007002e25040190602554003040c5258003d90501c1010009402c10220f521700c60580e06025514002c1d1b00c0c1e13405c807403481009050345900c403040c141a0b42946240c400010186219060156890307504003030080c0047c0c600c681c00200c0c000300c0001030201c0d541c01079034140c490358030803e800c0e00e074090f44c0c00040c00d1740074180303d4a030044030350550041d6440c0c3c0952149002000e81c200018680c40c0c1074140410b9205d0420007a080810030f020265117000c0e035410a4502c105240180c410310b5480c0d03600c550403c0d0f400c0d80d0103405c030781d1954184000d01e442803144200c0e0200807070080a46030034990100d003840c0a414081411355070300500c04c1c0103043c0207404039103c5278070086c00c800e0324620082d040100e9580c2584143c07a00c00100c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 983385881 1250 983384631 983384639
    0x9040c09091d07210803190f02041706011532190e030706051b01090b060307080601030b04020904241b18030222020309030912030712300504020a 64
    0x41c82030130510315240504100f000a840f42c00c0da65201900d055003e00003200e6640e405d031014824040c02015001c070250750f480c50040c1205400740303c00ea002c2d40d2a0051381c010002c1c0302400001000811581c24901848251140401c40400c66101c1d1201903048120303102d880221203400a2201c0d500c00c21201d5003420407640308484032840540b1143d09540700e08070038007030b250050021741000303205a090500900d808842c06804e41d1080031048440100f50b0041c440c9030700d401e01483c80078101502c0202055851602c038884890000b40010340031305084804541802005008607604401646024402e0700b481c059090003004044280c80142110248a06c441403084100a2138044150007900149041d90201304141403203404009078206071004c0000d4013201d90000c1c501c24612400907645407503c0340b00b4014249441003403036450307400422050000907030b020300001b0030b0b400920740080250070384d000c40340c5860000050039900980c1c1c0c0914503030159141c2c1181380700e140f0a071584006142d50f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 983387131 1250 983385881 983385899
    0x110f0d05040c1e05010e040b0d0f030801090e06040b0709150e090c03060f1302130b0d0608030306010f030c170109051f05011407150603050a03091a09040c09091d07 72
    0x95200f4000f401c00d01d15a00300900c0d881742c2060b520500c4002c0c00000c0d0f00c804100000d00640d085c1604540c040c179850350020615800041e5280149503580090080c10a21b00c011750311a48001c20040c990502000410f007280d214a00440c050002d915000b9410405600003401030140c0c0307107035103219102100001e5950300c0b048054902420020f000f4240500b280010004044c80442800090a41c280b00070050900c19142c510000c0410086840e502d9550043c0c403000c0e91100d802c00b0703d1a0340200141311b06664840d40d0501c4464152400258040d0750041c00c55441c0c82074000e00300d0303511640c0b00208110000790702450140115001030703044807020950514444501d031240078082003102c800c024032500140001c01c280744c0f154414801d408200c084000845081b03400c1910030303a000380c0444040541001704407024081c450341d00c615a0444484c1e01580e07100d00c580d410b00503078031a10400b40303035405024010050050948140030210079040c07081040100100e4a2000d440b0341680000c110301 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 983388381 1250 983387131 983387159
    0x801090507090e04020f010210050a0f0e070602151320031006140d150608030912060c09040c1725080f04170d0e2a0310110f0d05040c 59
    0x243c48034141d030700c5801300400c64201d0b4081d2415809002e800c04800000d0303100300c5110b90708100d40014940c00560041c1d0885100d011403c2c1142d00070001800010b40008541d41420802001083c15540c1c85156a81c800741c0040001d140040c1c0e0040400100c848401c0d0914100041d404c45040800e41c00020043d51003d1068128ac0009800d000a8a052a110230900d06008500d0481088250710b0840304496280e0f10003041c0b0b4001083c00300b601e140c03400d40c1400700d01e10640107044600b402c0a81e00207500c03d0382070042c400c03a603541600114500644d039a500781d0450084138489450142d06c810560350851448406540c1e4440381008628043d4003054040c403c00540d8088990300d65031100818224103e02144484041c0f0031090f10030128000e4a05400d040360140c019055900a00944803084004501c40d0302d5403c25450200e4500003401c1c2004040c0b0382020404c55210302c1419840c2c172424603c5401d540000901411180103504a03a02881c8a80359044c0010707510080c3d82c642705 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 983389631 1250 983388381 983388389
    0x406020703032f0c0106050a0e011a0a0e310e06090111160c050904050102040315020c0a0b0c040b0705010e0c040b010203040e0603120c013606200307080109050709 72
    0x9908081140d00150f2000a40481500300000107001500c400c002246d0790000c0d070003444120319440060041c95000c00282c40c13010311684490303040040201000c1c1c65107048410080c00341009079050076401c55107842140c400155200010f86800110081802605215203030842d1882840081085490140b085100c9024503d501d6030404031600403e4601414450065543e8085030b0f81c0465580e4440c2000307030065102d07000044e80c8070701c1c0d45132885c0b283c07140f01410b11503584148115201a0000f00c1c0d038060843c1c4c0028031510b1562031203e03001450140d500300302d07145103004c40e01004005056014003440781822085814942c00c150402080e540700c00c03a0540141c009000402400402007440c5420030402001d486030030040402081140d0082c802040c00360b9101c1c82d883c058550f201c00e20112013081c60611b810950600500401c00d00300764000184829910000d0454184c815039000c41d48090301812140d4a040464004040c44028004e01600500d044040340346039000300040300c125 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 983390881 1250 983389631 983389691
    0x510051c02040f2003070f14070212011515020c030105270a051c030506030a032f0304120219031e030e0306160f08150904080d05040602070303 63
    0xd2255080c440682900000720b00c065440340b032150180440310341355140b43c0801e80c0b901070f10707031034803503002000c001d40c1d404140d043c082e465600e442c200f2005e50440d82066016540012400c405401e000c0c0104181c5000074050400127001040012624510401019440d03086850300010041094201e170400c1c0e500040300d0700c00c0f001c100c4203a2140c1c3e00c6521076445900c1074410940c901e4840700c0c140b803060b200785944280d1111040151136058031030540c000209400401e410036803550050010000c40c0440c208648144c003000b06406060480b400200300311405503030702d440e40d500c55502740b030005201c100c0c85036800d410b20020280710520003108680d00280d851080000c031000d42c440710340b6080816802c00050044000d00f680f07082208c11b01400010f1003003084020707609001007040102c10562000c2240032424003021607030014260b818540c0480340035800ea1264540f0005c0352050355000c488844c05d10f4104018005550702520000d40661018403041801440d000c1c00d907000b081d180080 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 983392131 1250 983390881 983390929
    0x3060402040c1e05040e0901021e031003021201090501050c030c070204020d0216050703020f010c0c051507050a050f1b010503070c0309052d01050a0f05090a1503051005 74
    0x35181581001562030600d05020040c1c1c00504030780c5000020b504000c2011400c0010b080040c6244101030550250b1450300842c20031044075035000360402480408240004040007040c006004070310000e000310390082c220031070404c000300785c03a019182c4007409881d1940303000c0014002e0b85048003140e103c1c010301003a052410b00c0e01c3d0b0803c070082d0040d202408000b030b42404007144410f00c40352105a50750141004040b41491441004469070f00c900d51241003285035480400080c501080f00c8090310307800c44040c0300c80c4004140e03d0503240109000078103540700e020741e0b010a001c008515130021892078001d9641c0c04048504800e840701c2e0060704140000c00410004540e40e105480c812001840f030302e02400380656880014041e0081c0b45144c5645001440c03c14440444840450040c040c080c0dc0503400c0c004501c0c00503041402ca01001c406020340001c1409003641c0741c0c25000003070940c0140c101c0043e851404010000c00040b9003041d04011000800f050b140340c140c81c000388105250303202140b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 983393381 1250 983392131 983392133
    0x51b0d0507171501030614150607061107210206010e0f0c0c0c040614010314011d0406020d060321170109020c1e010c08010f030b0403110f07060806040c0806030604 72
    0x20b403440000200024041d4026110483e0202c090084c029070084c03030f001c100710303540e04c042050703101c0098111000c036490303050810815160001070711400741d0024400169100c0308160b01010f403050355401005519001d40d03980e40c2004440007641d29030400d900f1142960b890304101e500556050b00d20450082844002801c640c0020004011404503d0300ba100e8a0b40440d0100d82640e800342c100d0404d01e240c40407845900d503071500c561b400036500c940901c410303545042ca040f8916008885100042010000003e080c4200e5030100d4450000c032107420010240d0b00c7c2000341c8120704851f001500040d40e81c0c02d118145114049082a200300da243c00c0d14641d00e0010103200035440109401004e0150380c80d00201101c804a01d40c40201d814800810f0781c141e4040014103151050b0000e403420381108001780040340ca896a00d6070f1099250a18100d50307404202040c2c80c0c12800180840c483c030600ea80454041c0c0e0054015000b98020350b03090101c4c000c0502e064480b00800c582a84e0554003d900042c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 983394631 1250 983393381 983393399
    0x71a090307110d020a06030e0c010e1e0612040605040204060509160e03070305011104091128091502010603120201090b0c070f1703040c1413200403051b0d0507 70
    0x7102e0500c01400d008580010b50701090340b82c8803540c030101c046556161103600b10403040c0700101d246403091800303440b000c54040008807a4140d010400b41c0b08001078501e2211500c0305008c842c0351a02481c112040e500d01132800d80050042114101c1c041d07030410100080ca801c2c250740c0a40621050708000041e401140300489010080300c00c066814403c0b6440040030030420311402403080102c0150f00da031513061040d00030545041c0781140c2c605a4040280c144080c0c680580b81500303220b81080802d04000c241c078122050300322740e00b0070544424421910061203805601020489204242081281c5005041a0708950b01440d020300300d200c1e03200000f814081c800e002006024413074041c00d4801980c030b4944168954100c10b052a00302c50020611050001400810009194010100d18046440d0740800c44010100e0f001c1d402198840c00304441b8441056241100c0280800c0a503446a9590070a284e90306018062480e54401c0705c00884481d04100515022260b042001080a10b24080c076076 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 983395881 1250 983394631 983394653
    0x905041119020c120109120801080714030a061b0210050903040e060d2a05030307080d02070c030215041a03070e101b032d081f080105010b071a090307 66
    0x1070382103006035441000c5a40c0c03454840340c0300c84d120070000110f1410518095120b810800f8107074051109101c0100102c0302d001900e03400761000c060084082c0c48010021078074000301d24100070440343c1010a840901c2800b5900302d01d064007141c0c00c17542c083d02459119004c5a01c107039141e4106820030003041c480c14445411803904108090840c007041c0c6540d40350a80440d00d030194040c8030407401a661b500b01120100b006018080c114091840c1c500c85d41e565480d00d116a000b007604444e0007144074000d001c50300030388000441d006080140301008240a14800b41c2c007a020b20b6103808004080c04146c010b400040d40d1080e203103500c0312050303842d02e038041104008c0f400c1403203010890072152002c80b0708414804c010019100e0f0b100c589040703d403c1958000301c001c11504501059241241003105030740070b10699000300041074141c040c3c02d40d05210504d2240d00b41c025040940c03e0000001702603210800800e45913000c0c034202e44009562032180c05612500791080341c00c640c410310040020031890790131 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 983397131 1250 983395881 983395927
    0x203060c0d05070c151a090c09180712110903060901020d0e1605090c0d1a0906090925080f0703050f1b060906270918061801020f0c01020a09050411 65
    0x111408003142200003c03468001150001212344020a041d502c6040c8160071701030508010441138014a00f10a0051080c10b080211012458580040c0100c0c0e4052000b2a41c80030300240c2601c83e10301d062009203010754404412002400d20b8080310307003642140402e40108401c400c0040e010707018070344401c1040085007d41b14420110f401c00108256910b80d120780c50309c09051000800e14142188100010050018105401540c003002040964000812a07261000d01d07075031140c0224600307082103000b80309150040e40482c4601024071034a841d00081d0b8808483c421400c46012486c0483e20310340710b0500c15224403a0741c0e0994044e005600c3c0032005000d03100b0014040a00b0011800c05c02400c0c4000800d0409424080c103100085900f4406412a44a540000810010428183c080e0350707c56000f080d4903032a64260805110244e02901110f10140e0b08114180e19440c000d80385d1030003544400280030102e40040d100180c5400d190184000d0f90154444050a041010100724460101c10306 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 983398381 1250 983397131 983397161
    0xf140d020c03041404201902030f0406031a0a0320010e06070605040312020906040b0d0b03060103031709060606030117010905100603151a0d0f0203060c0d05070c15 72
    0x224088010714100068801090742c542d0411015111009000803242074400d09032403240d207000d015000207600c2e412201008104040307841d08240c000d200700c1c11409490a102007003680050000340310340c0c1c55000382d6201061964038828007868007040045c025203610000b065000c8400781c2a08035904816190000d03c41810a070503400c8103200010100d07031000000b100c20356a980c05106c04e1642c0016a18030f1118204c0045181c02d085000250031030003180705000301c00400051301c0783d4561550b0030203070404202804540c22540c40c0e04e000f03049502ca41100c03500c07040d0610002402c92800042c000d00030741014100924590070166079996102c9618018401036486080f40400114104903d24400104034400544903040d031920b180644109010045034608040b40d05003030790202902901400c40c11940e008a01e40d0520380324042c140301c84400f0b541401244100711807100303100010141005019010011559100001d4541107070b114405848900c401c108001041126846407075404040c10b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 983399631 1250 983398381 983398387
    0x13020c150c160605180703050606100c050d03060e0c030609040816120906030608030405030c010c14010c0c02040b0907080606030a0213080703030f090605090405130f031e0f140d02 79
    0x4034008003403802d034010840e40d03140d481c41040030005000304480b4807410040042c252482c034580707840356a840c2c0074100030711461580c907a2110f05e40c02000b07444409135020080d240f40808009000e001040c1c0d40c451191100341060000300c80030180e8040b24401c103402885410543c0b100e49507152103401295401030244004811480401d030604449059211103949021825090401c001e00341c030703610307071102c803055109100510040d680400c1c84180c0c18828078142022900604200c2d403640711800100c1c00552a2800c5520300319840030003662002e0080d00d052100308100401d10500320002c445c81d0000981c1c29020825030f00d811401190000c00248001d4200501c000c6c80302022040d56201440355403100100b0000c06030007a91403406c0404c01d0030000c0c8842c1c5000360150480c0310f412013480c8103582c1c800c00079112800c01c000d040c035126004210f4090f94a114a4040c004280050070031400c10340f41d50103001d00501c505050703200700c0050340d01c07010546040f00c50051950003010881c00c14603024 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 983400881 1250 983399631 983399647
    0x51203040f0206031003020f01090f0e0714071a0c0702130905010213060e040608010203010f09020c100c0302070204050a05090a02190509160f090605040e040609080f070213020c150c 80
    0xf100207580128141030414400500d14030421405020001d0f00034180300700d080e0104208008880e90790201e900f5240020420347e00d04004842a5032200300ca121100004a225024030440170319010590480500780304841d100e04058140d2030140c00402541b004640c18440d08540d1a42c0188102d544100000350400d600009400408070381c40d04560009141d480c01c14801e0700e410f014000c01424141c1c000c41c5154100541c900207172a880c01341d1102c880c0c0018080b11480020400381030310000265040001d507402090081c065071181d03005911950a100c0810b0380305800e4030503940100101c40c0180213040796a400d010720401d101e2031010107290a0321000420fa1107070400740c2c0c41000c056054444580c00480301400701000d4240c07003010030022681c203000070380c0c00500b21030580301e200f1803806265a0394034050b8050010b81c44001e1280801081c06a42c80c00c1c044050500148215140550341500c01000c03403c82c0600130b40c00155601009031300e07079210341100c0c9954000098104980c5404d140b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 983402131 1250 983400881 983400889
    0x18020a0602030a02150106140f040b0310150228110307081f0b0f0d06020921013e0c010911010e030d121104080a12020601060507051203040f02 63
    0x4652064001d40c000141c1c0000c9650b062081c40700c10340d0802d204140d154180200203003200259628028807200c00981034204019601c203036001030100050a50b43c91404140c800b241a08510428042c0c182c5590101085400441d80c0c04c0e00059100d51000d058503400b4111645c01c010910560f0f0581d0348401c610380c0c5440501821007d07080c03c0000303000e4000300201e103114030501e01c2651100c1c940b40020f00d501c0c6581d08a5000703040042203803100c540c44140d0a002d00240300780c50016901060a820364000b0340c0c0501141032000d98010001c1001150048800603000c61b4142070940340311440380048800d0400f001c004802c011400c2d0070500b4584501704042c00c58040f04425100016403c03951682503900c000d4042d500c1c04103130050b19801c8004100035001185250510044030344401c1c043c0c1d400840c540541d0001d01c0745a00700d80c90491300f4141000c054841020b0000107018a00010806034040c01c102c0d480d841c0e000b40202006113420120400b55000a00116400e2101d1426100540d413 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 983403381 1250 983402131 983402149
    0x2030405060f0903040803070201082e15091818020603100e07030612020f150406120608010902010c0f02030c131d010e210d0204150207050f090a1802 66
    0x44600c00038901030810452050034140c000301400e00542c8200020b100b480b801009440304c1950a080141301500e984445620b510324501030a40540a4910152008154116001c044944200d18041611b41800040b1540b58040c0074099681e1091028a08600d101d0360000000c01641c101d4001c4070302d40f81d400100e69134000e82d1012044604110240050345101d034400350008418207081040c180b625501c80004000220083d00c83e51103c0076420054640300e1a240c1203c100f13403130440e942c507141d400c0608003004000001c0f22181c54200003044030741c8148100b0029a40503110009032044e5680c0e45c00110ba50681e00703d805000c0c07505614229202c0000d4000036403074080c00892000e6250140842d16881d45440c658540e0500c04814003804000ca41458000301440000e05581451100c40c1028458601d250b000c0705c0c40042e000440981c6882c00e010324003a0380d400d5070081684d81e402c011041041034047e035881403401011408a6103946d001d086180817205601e4905405600010b094407 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 983404631 1250 983403381 983403383
    0xb1c1202030c330f0a0c030b09040311010b090c0d05060411040e070905061603390302120d06172109030c04090b09150108030a080705191706010503040302060601050d0f020304 77
    0xa034840082c480c2240c214041c06d1307107013510342c41c04106614042001460041010b80050f041c421400c0900207401000e422200b0030000c0604240100d05001000880ca5448100320070300c801c2c90100492a5440d00303014003031003043d06035041400c041c05c01c1130070030f1016000751017401444114140024680c40e07000240c0a0030400300d00c0c4011903042418040c0c45641142c00d440000003258420010182d032500c032620701000d001d40c03000c180e80c1d031502d001d9207031800c1260100da0040c008986500c80041c2908004140d844040441106040303041100f03030740d43c592500e240802d10b10703000c045481a110202605c0c0c0d840d0014103d40b0f00d614404081421110741c41c4c81a5016000341080080b481d4040040c0080302e004c0c91541d010561500401c0d43e1a40200650349041081c00e90101e2035141c1300e10180c034007554040308000780d0380e0000840904035004003842d1143c4182900001041980a01e0541e0711035a00340d0090040c07641c0c3e240044941d68051618541255594180b00c032081e645440654411 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 983405881 1250 983404631 983404651
    0x70b25050601031a07021f090503120a150b120703060e04060f0b0f0f101808100c050304120f0908010207050601080721030309060b1c1202030c33 64
    0x5541182443d150101c44c50b00c00350780c101806814440c01036070020b03080c0e514040818595419160035002c10000c0d006424010b001c610000c01c07001c441c686c1c0c1b94440d40c054a01c8160410080024145100540e560b501c924140c0400a0100700f01c0c40d003d08004a502031407601c1d001800e02e403555107a00541e08140e4060f200a90307290800384840301303940b052601603e41190305040110901d40025900a03d21004501030240781004010460042d032100e00041403080d000c22815890f01546940c1d80c22802d4901041400c0c0080c080ca000c2c00f0b807007220f010b0780e00015003041218482700e05030b0f03100080f15422000c00c82d0156000070010028401f610010b4841c00c054102540350590403840c03c031140d0810540c403002104176803241c85410001a041d0b80e81420081121540c5052100040c09203d01c0107402c1900e2490203884060300348084100745102d00e07603440501040c600126a2400392144010580e8009100b80b58900080d0401540910302d5490f00d6414520700f082440a0903400d4402e0030712 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 983407131 1250 983405881 983405893
    0x6080d080c181c02040e01110f2505030703030b2709100c17090c0a0e0c0d06060e04050f060901090e0102070f03030b03060a02070c14010c0c0626010305070b2505 71
    0x4610341030007041d040c003e4081c000c0c4201040058602580d02c5442502554100000344d1080c00d00055034142c031003012102b076008500c46407801c00d43e489074400300741100042e103000388c182c0c07031803502d5881c0700c00411651455280301542070179142540c08010b46051807a03c142401e00c0c90b88407843c0a100c18418240e17a88a07100724070580c41072911400642410b881d074006e903480e0355564030f50312003800445034400c4e6541c03101d403079085030020309200d429542c0c0303a140e05005001c0794081d042906018540c00a0b102040b00c5e036a100c005255074502a183c040d231010f245001000584180e42002d0102d08010340014944003071541c0d014160440038500b100403a85a2580070f0452406224156201e01e11401c00e5290000a40e02d0ba5110006c600800c41d05480c0ea40300c0d140144d20401540f040241d101c05203ca00380e031070380c1c2c0c050100380c0d106c0040420704007c0081c2181c00d91070551083c1c101d0390301c60020824141414442c040c260444841814001062180d00403c5181e05240351440c80c0500003a01c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 983408381 1250 983407131 983407133
    0x103020f162004061a070c0806091f0513081c050a05041205252a090507180515070c0e01030b1014221d0106080d080c181c 54
    0x1400148104020303214504d0024100207030300f11103404070030b1940c40710b0300d459640505141c400420780880d0020f002038450b00c01000046075000450001014000b20400c1c51120121104400d48a00311a00103c0d056106007040001d00d4500162039001f50180c805c0d0403030310040381420121001114079020341e1343c640092006001c00d006c001a400c0e041071404518000d406160202e001050080004030081003c0700310051040810580c401a105140e111458140c0702125168100141c010400060b1a16020690a9000744060302d00400120b0400040516010410032031f08024035100d00d003403d0400030040092941407400f006801107071142c68465040d420040140040181010109601c070349051200000031542c1003080700c0c00311010000c00450141d1100007110880024080c03038200295040d483c55180c106250410441d00208221540e49032031139501c003405035908010500c1342020443d03100b201d00003025050006416070f90810178031000709200c0001d000c1d42d041c00c0034200320028 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 983409631 1250 983408381 983408423
    0x30f0a02090a050601050f0d09060f020703020c0a0f1a04080a0b0f0106031103180c04150618030335071d03012a0e030d0801050111060c090103020f16 66
    0x194000e03a016104103ca0301e44000040c10502c00e821080300b03c0784d00410413034140b460b6508003400307559000d0300030b010800c002a8080c000e0b4000500c120054018440940b00c1e900784030411500303e82d8001040d00314176241c0038031311054030194844400000020071011580c600d08000307a083c003c0c8100f01c0c01000786400d00c86600041d2040c0c125100705424004040304100d41d0005036600034142417104d009040301e2902e900d15103040100004c2c0c01c83d0030010043c60400031140800c0881d1459114a2182a00d13030742080442c1c2e1590000402003040e003103200b80002503000c054000740c0c0388840c2000303003041003c4103c43e01c040304440300c200045940480490110100c0007100071844250001d0140c44050400541041414a0503030500fa004140d11314501c2d2103020407404140024050313a0018052820003062500b00340a01750203e6025007880c840322500151403403242c45480c00e030900309803100c00110040c0d4040c080f1180440418880b200520f000c0d80040038000740b050340e94000701c4000403509 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 983410881 1250 983409631 983409649
    0x50a050a17070f02060c0a0b0c030105030c040e1504230706031d0705040c0c0602070b0727151116180605010909020c2b03051b070b15030f0a02 63
    0x2030007003100340610000a0340c1119511101c560446909445014401101e4030f0201d00140c06007079198180c00b41300c8400f00e1030000314143c45043c0c5c192004903c02c50184400d440300014440e405500a8070003d10082d040c41180c3d401911880e1240112490f411079200c3c00802c0002510140d0000c460070040382d42c0520900b40c80640107000c043d07046100c401010780300e01142c41264050780d225500e410030309210301c08454242344d2049046440d582642410001103208a444001188201054580750600e12010314280b440104103250480c1c18481c2c00780010200706181070070b02a614041c1c4a01510512038807840e8500440b541010701d1a00321315030000b4454120b10b014983c5890010b20090b644040000c0985030074040240e41c851911000380e103022810b203125080840e00f940d15845000b0340085030115041c0c103036404e200c0390b02c418804030401c03030150381483d405c00e80c10810100050703000450f10354003803450111220210729680100341040341490840c802e41c1c02c1640c400c41140303040401 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 983412131 1250 983410881 983410913
    0x50606040536090d031125020a090203011a1602060703110c06130501050c03070218010e1605070f05010b030105100806010f05030a150e030a0e03100c0e120a050a050a 73
    0x4010b154180080704944418200003903404041d111400300590742c10b5102204c0b081102001c58103250344184541050b4440e100408a10611209400245140c03480c001d90f0b040c1c0e51441a40b0b09080e900304000680c6900808000c0078a54464000a0241c2e4a0202500d02c9502030b0300c1d4a02d03802002c0c00990300b0990017498840c46507900b03020004420400c42c1c980c2c02503c1003030130078a0f55100324405417451409079402c003e603c282040c80c0d43c0031503016400038504a0704c080300c1140c01505c840c0e00294801540b11840000650305000a0001c07980503c082603045000324000a009049140440d094440031910f44034140c0f5401c0c0d04201c601420003280340101140750050045505060000c5d4a85180503005064a018440282d4620400e0f40c400b14800600300100c950303c003010240a06540a24031800d84a03001d020b404107580d01003030040881a240503074401883c1254502080a1280c10b560900d00c28400c403000c250014404201080701e00e4000c000802d50601c091606560a50507110 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 983413381 1250 983412131 983412229
    0xd1b0f082a100c060f020c100903080c03040206070c03052404120c05030d0516110c01120509101e0615050702060a0e03030a0306090e0102040311040506060405 70
    0x806015a110000010302001904803011609a041010b00325400c4090101c050110f030300e041c4242407208a55030090035903072010400e44007254440c5024404482120b04050003249140c1c0000300043c012400466229100401007402d04075107403141c4107405096081241c1c01c0e4001030003107501c1025031114107a050280c00d015503c9117050782c7d8941034080405407640921030000d26640c100001442510b4040900c9034041049107000786030350b8101150b03c030851010448550f128400428081240c00594806071500030141c2d0381c00051b80300510b0000c040e07840c980510089281c0d40001406183c607070420003141011004c8441100e582195441d174001101460300214054819401c8800e580c20385404484031070721003888810640d85210b0040341d5540c103000010344081c503541c06620100984003181c03820000c503100004654201c0c401c1e80005000d842500c5516242c6d403034a0303042191300000c050a164100799461002c20102500408160103082d80d1443d084c410600d0303001c515103c41c000c81c2c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 983414631 1250 983413381 983413423
    0x4050705062d0c0d0201051b0c19050c150409050f07020706080402030312040f06290f0307080303100e070c021e010905090106050c07230d1b0f08 64
    0x5800c40781020380628241801582801c0d078a0381400b050003e40b40510400425260401c040c004000e000300070071101201d81c82c4250707401c082640d554605880100d07181d01c0081111203c089100c410104900d00115000d21a050000040e501c07003450360b101481c4544d92181e2114280044241a40c03001803802c0090131800e010028031a40c0056441c00300d4206007008034040d00d0351700110b03041d486500c5401d1210900b050510080000e8404990070460142101700040c090f007a071148c1b0a0207548146c1c0c100340d100c0b03100c891030902d85030740b800d07805103001405c840416070b036036080c581184c000311030030707a60b41120000801c039590b10f410241345c0c440340c1342ca84824250120360004403003d04c6000003100441d0b9600900c495039011303030134400241c900207040003465039551400401c40d03403141800c9030860040c03640004451030850030365506440c404d06d91600c0849204140310305900c10590681e02c1d80020175800c8404040d215203003000d401c9035130385d62030420306004160349444402109100124105 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 983415881 1250 983414631 983414647
    0xf0b061201061d0312070b0a0506031c030f0501241b06050405030c070323061608190c2003180402031e0c041e0e01031101030e0d02060405070506 64
    0x644035040c15a882410a1901d0481500d614508594400d9a1030f4041c859070300540d042000f40b101030801e1522aa6420316507a441100074020340388191074442e09640407958031102400180c0d900071078124185000a0041d01c40e98441060b9036084c0c0c441c04002c2c83c041c0ea41c50050350036054424500c061421b014444e503283c010040610b04078020058003041d911030220b0704100091049808148102c0111303a0090749a003040c2c1c1d010040301450010b040040282d80441ca00b01049441c422185034445001c400010f4109494150005004c0c0704195203a0b407060b407600100b845000c3e40c0302200c1e03990b52030a0a4940344010f40c4d419500503003143d907001b40641c2c22000401070341384088010554015890781c80b00c1100c09502400089400307041c4889008001c5413201081c00350007101e901c04c8140c005050381c03055a54501000e4011607900702046c00050020400740b081c0030324080010314000074034480540c9010300340407007120000c0058111100b0f2000b4858100220300280008444a03440d00d884 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 983417131 1250 983415881 983415907
    0x20a030f0c0510140d0605060a0239120c09010314010614030319050c0a1506060c02010f0305100314420613060806040b070e010f0c05070f090f0b06 65
    0x100000b084e048203002a8042428401d904040f0041201074076068071444544006512800501800c200540500b0701c0d0f040b880119003400a608141130012540e00030300302e8140440111103107180005481191070100c0541c0312042114000c60103162044008100004500e0940d440c540c0200384000d00d08081458641d0040100d03403d1490034004465240000c1c14255040c2c001d40b0040e0100f4091020751034180010814401718440c0813000400400b070300e480c010f40d4501d6030000003a00007040c5441241d1070501a600064204200541442507542e0360b540f14500350012040c3e5080781d400a20314031740c030300740d0104030b5541141d80006003000d501625103001e10078620203170a001558188401117409500c03041410152060b00c0d581c00e0103415100c5251650f0b0700016142201d0800007180090203141c400c2d50703101c0c0415816922130184221034003045403d040c10301030946540c0a0600001020114141c9500041c0004000801c464030080c400d101260401d0340d4441c002c0504200c00000101 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 983418381 1250 983417131 983417147
    0x1203060a0501050928031a04080a051e191806050d1a0a03060615020d05032d0702010501050102010e0a0b0406020f070c0f030c0501031a04020d09020a030f0c0510 71
    0xa1802ca034440351100c000440c0386480001400500c000c0160072803182c8980c903450300c2504c0c041c500100c1c0c849a031f00c0030040d0350741040320080c11290040c418981c0356482040206408001c81d00910508480b820160005038442000224000003544200d8070300e5421840150407200c20300d014030052807501c08050043d102d22000602039654a80c011b6001030074107030100300c2015020f489020b40d0b40d101d140840090242d40502c0141004590580201c03a20001d00e044c803000407555118155100d4051038842c52002d142c025041c80060b41c174880421003000c13000c07440317811141d00100d401c0d450f00c8006421503025500b0341c88203401041550300426400001250402c1e8807580050b1368400d4003504080b5401100700003842000070010010b0344480641e80c074819240074101d40e0300c1d5155150015070864181030344a40000314840c40f280c11134502640139041825400c50081903038030741030b40002d09035020380d041124510700d40c14800091000302c4060364007901e4260b4100c5160103400f60044d01550b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 983419631 1250 983418381 983418389
    0xb1303140a1101121d100e03030c070213060b070f0c05060403110607050111030403030f0f050915060a05060d06180207020904121202070b2e090203150d050601081203060a 75
    0x441111411111201c81c1d601800a45e40d0320002d42d00c3c440b040e0803c00b6140c03001c43e40604109402c5c0107402011602c0401128011201c0382002c40c0350a041da400d120300d1069450251021507661080080c1440004c0c0003814042c0c46081c0c281e140e00792030700c2c00110f20100c54000c0d60051070148024030003da405c001c416030700d0908840c1d480c0c98000c00d00d08140500000d00405060060200604c8101905604901074800410740140010000222154211241181c1e00f500b16401050300c542900d00a466854010390302078590f00d484c0da00d44000c103036a035025145502c921507650400b0400e000c18281207025664902d9415490700945400180742c0d500702400280409074800c070700a24035030003080307407404080c08a0819510751025040c42d000c105c3e01151182c0c941704284503061740d111001c251030320701a02c4045c02c00c1c0d041d50a061080009400c0244100001e45441801680650718130440d4441c0380e118000420166060010742814207250218140401c0d0050060060640e1156240c006403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 983420881 1250 983419631 983419637
    0x106060512040507091e06060c0b01030201030914030c070905150603011707030f080307030507140301150e0628030b1c1a07180f081509070b1303140a1101 68
    0x19450b241030140c01c240b410340c0004940c074a01980185001a40e601c2c603c0f0700d582414082040e25030f200003e6602070000003004100803003c44c0140019030007a8490f147c51806009e00411241c8003505042ca594841c2034110501d500400703040101102d6401015801107100c080030075010550340100e1450300060081074100d8414120716500798808015078001035401055000b91400581041e130540e501c1a134001001074100400690443d0140c00c0c06947c40b244218802d155a00e0003508141c41070f0340341207907020001c244d140d41e000c65035882d0142c0328404480010280c84074190011102811092040509140c180b001c1e04916948440d114041711700d80140490402850303207899986141401ca00e500100700b810281f00809a02102140390780102241041c0515298200022a42c1070380c803c20000e90f004100d0300042001200d201da40201c0d081084520382c0d40c548201c5000703070704151500702008800c0041007040c049221800c105865012000e00004e00407600d13501040443d803800c681c18 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 983422131 1250 983420881 983420917
    0x503030f09061608090a240f0e0d060507080627130204020c0c21060105040908040e0c18040e0d0e0a090606170603010b2407062c01060605 61
    0x342e4031030208440c8149542a240e04800d180351a0190160704800200d40c00307074001c49400b0a0103811346c031008058014405a1003510012030800700e40c0010310303100709010000320000000f01503ca8486882000e84220000b191600e407410000b0401440100224440e190b0004e8000102014098240506060b85c215054035581c02c19a2242c48001c1c11009410600c00030f8400079000703010880c1c01a03920700710781d120b01c00d4281c20b000342440300c60b03003140d03040c00c0d0080340c01040a031a0961260207401e00c03840b501424950b588000038002502115441c0e60140000740f141015840c41d000b40070303680412101044000000c0030413980e0343c1d0511911006101c0b80c81c04000c03c6655001c2071301c000b03101c0c640060000c49e880781c1d4010402003003032113a4000202c01c100403c82c05d14040c06800081e1401070103580c584504007440c9450150251604100702000300301100c08200140910309151100902c0003040380c400e2003072058455003210868609034544801030000583c800c00311003100703509070704001d8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 983423381 1250 983422131 983422147
    0x3030c14150420280b090f1c05010507081006090f0905060a05030f0a0611030405030322060515091602190302120d050609160c06020703050c0a111201060503030f 71
    0x22507681c02240b80d03580071010340065880d20742c0e102c0e03480403c42131010000b0340c01d6a8a001d036803000c1c000d0603004d5a110a00213100c0405007840b005103403141180d10380704100c2040a486150840310203441c06030001e81c41000b0005007030400050003004040341d190400980c0e18084503018415031b81d00484401355218004107000303a0303960034643e002e44001419140742100f1184241c0d43d990913010100e418600f01804600400400802d891040e0381040241d89541d0711f0059543c082500e800620440089103e4844c0200e0340750f114aa100d03680c0d2a01e0030400103107004c100458200000d000c0d0340c01c03440101040c0d000d50340c08102900d980a400e201046494207500c0d041e400c1c0030303221800c0c400b41c0307102141908a0201c2500054002d038426075004002d40c913000400c81c41d800d5007003000c4c8042560200c02c0d0001a4141d4001e00845010f8a00241011014291141001c01c921421741d4182c101080040946c54444100d001100e00318000304202072500d000302c1d442c0c4c01840b82556401d00c2c0410800 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 983424631 1250 983423381 983423423
    0x120d080f0901090b0a0c0f030b18070203040b0f0304061d0c040b0f090c04150f14091c060506040b0105071a0402150f0c0705060f2a010603030c141504 66
    0x1400f519071185080d6454030b4001000b03401814034409171800264028103251170382c0d001c0d110b480c001c50303000382070300d800c1480c40f101403c009a001307041041184410400081d1080c0c002c4060204803285010140c2d50342018285202940c03254150713200c800315200b0081524407000035610103005401d0b50045078601c0043c000402c40407803c0412a04042e03c1c5003003140700d50800c401001614032002030f0081440c609031044880d401c525210f9030109000c00f80c41214402070102030040b0340c0e00142011140b10043c0610301c2c00000e801402c86d041c0d0703245c00c1841802d2606014511101d00203103890382c2014400e40307407011141105000c800001e0302e5500410155202c0042c488000304800070101d030b90380c00d41c010700c00c0660700034581158240202d400104103890100211a2099410300c801800c0542c0407007007081c280005400600020011080c451101000b03014242c001d40c025141c11403110b0080c00d000d00302c890301b0094071085802c00074900c145140d00126582e0440d8000a8028100d01c0444c0341c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 983425881 1250 983424631 983424641
    0x60603060d240c0503010806090f1203191e060e0915090c0307080a0b09010603150c02010b030d030c0e030d080c16050601270e070512030706020f09120d080f0901 71
    0x50101410b06244240e1281c004e8003c0d4125410101150f0355036035030b2200c06840308045d4100101c5034002002101c0c0e03d14010000c0c681016410402d003403102c0900d0341610845005540c8a90801c1100104580144491040d00b00034031040c0e00341c0300b151810811a1343c541c002c001c0d074250081038060100e0704958040148034180040a421150010707240c5103400d03520030369803200720740550000c40050411071041c0640030440783e00c00542c100c1c0100b20b141c243c0c007400094140c101190350398131000015030b40070080c41d004a071003910005009840017900408801b8004400c0d03000354408181c003801942e026000c15840b503e904036258861446400e01c01904203081c0001d0054411100082500c0407403010711154841c43c0c005c000e0030140c808680d07005a40d443d8445544070342000323404100c2403d01e06140d0300c0d030b202c2c02c0381076070716142c840c2c1d07200022a0810350313404400100c0801e02e0090760a0180507400030395030400c000c00c0d5aa81500006041c000c009055016848801c0041030702c0180035044 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 983427131 1250 983425881 983425943
    0x10507060f09080403150216030819090813091b0509010c081c0b090624040b0d061d01030b13021f0c051608060103080a09051f020105060603060d 64
    0x502021815040c40f070b11507080340c0000e607182d00381103003d03240c0742e102842280c1180c400f4203020615040951019120304400600805254410419100c5480420300c10f0703039906446005105e49800c00300d400520040469000341c5c42c0c035440e101449408001c00b500d81502c61090b442c025694582d518012540c0c8a00c7c0c103001800309a003c03c03078115010312606081982120b0b8642000071060000070000d1441054850700c4d003151865030303420380d5404032011900e01824003110403440c203642d03207502e51b1042c0d0181c054100386d16500c1c03006000c41c0d1070640749250415106070700903e00754110341720081e003888058025404440c8002c0b46400715269881c420034800c804010f042080c607000030014114500249089680703019810300045110380700341030901910f0355034000340307101d17030841e0303207a800070b03400402507505000894400296a42d00e042140418035000610342c00101001d010107800c0d1003020300203a2244000b0b0042010a40f2b81142c5810b115802c01c80e80425044000c622042d40146104 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 983428381 1250 983427131 983427161
    0x507060515270705040b071713140a050307060f0503150402040603090b0a0c021902041419150b1c0920030f060103080f030406390f02030901050706 65
    0xb8420800b2042c00714080c2080801288912003982d401e842101e942c0b1807402070f012603100900400f004104526540f01400d0343c9044503c1c0307005010f41071003101907551783c05040c84281081503200c05003800c4c00003500815080e00200f00717460901c54080c24800001c1c50080c1084400f10000e040100120070f81003000070b018004540e82d580300c1300c00401618582000f610781642c00404210307610164421000344c0c2016601415100d0380c001d640548445101100780e9010752034001e24865202515011400b485400d4041d0b01080002e070007242c1610350312001642211112041005040402811148090540803070040b0350740e407e5442000501c0400c134094030032550a5120039402c004521010114031044003120310040854401d260b441c2000d010081000800f4420980b0807a5110051034015200b608045900d41c000c002c0b028200c43c0d0340d801b040c1042050002e0281004000348118035a08540c03415000881052501954900c100c0c9001410002c0009005090240551040c580d001c6610 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 983429631 1250 983428381 983428399
    0x504030218180c0a0b0d02040b0315150403120804140106060f0306120f03050313080a0f0909140c0309030c16050405101d04030e09090601031e030507060515 69
    0x2040e54118000200c8107070b49034124290644405420000f1a044000e800515441041d402c25040502507045030030710441094082c04082950411400034512038249210500d80c84c641d40b004022000120f0440748942200420041c40400c4001c0c0d44803162581c00d051a08858445140103460b0107965884104607501c0c00c44082401903110005000003081c55405002594441099002c608010b09005001c19402c106040000e03000c0d2018643c0700d00046d1100400c80b60b0f80c0c903602e15503031002908400088501c001c14510b00d0f0800c61106c003a004105003000321507500d03198071f503034000090041d030096103012001414500742007044880c0305580d0340c01c1c0c40895906400e04840080f4900a15120b0344c11b010021b94007501c000000f5044070300ca0200c1603400d03800c07501000240760303000e0002d40821403000b10032119515240d207020b004d5031804001f80034940c51810319404c420054101048034030f10400e40c43c07011950010039502e07459000710001507c0d465041c008400320300e00c0038000e60094108 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 983430881 1250 983429631 983429659
    0xe010504200c0604020102121318061a030a0f05070e1e15090406080c0a1802071a1609080d0813020907020f0c04050c0d020706200a0e030613030f05040302 68
    0x801c0480c0213a2003038003250726880124802d551140200100540340120044040001c1407902a0b80110030420810000f41d29031034100140144000511501c4410000018085150000e21402d8240c0b00004000c12650820880080c1100c007850405403080e950382c0d0702c1006080c00043e14003460b11004000ba0058410b030b2802d0701c0e85402840d5443d1040f0303d02000081e0954020403d484000401400c00d0586828004948020440550418000c55003400040005502c09000765040b00313908400014a1030301004080c410344450b4000c000304812a1010008080002025039410034242014840c680d180d681d40210b01900282c06980403e1031003d1100c1710ba00821060340d4441c030303c8140c40c1d104403004180400e441068400c41014a0300304072031021840c0c9940500141489001e0102e10040305944404200c440c011154000e58000604140c0c070076001078061046200c00c4d00603101518280300e102c107469128840190600504a106082840c840d40443d00507581c0140300078036000308 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 983432131 1250 983430881 983430883
    0x30711060a0e0609150402090c1210082a1c060525030504021003020d021207020c040b0d0c09020304080708070602030714070f230304140a0e010e010504200c 69
    0x8060b081d41da40c0180400f0480000021400b0307050141c030404044440d4540d90b0a1212202c001026103900c20014851010300007400c0003100d0003031550207840c401207410001c40c0c0f402e00301c0320b40c1d019080808803084843c180b1401c6001c4980300000303c0300c2c120003c000e0800500a550043d03030042c002e41c646410425250100d90000c4131a0100c0d040c00700c2c240205002c140e044450a9801035480360358903a00540c40c510903001020345408503800942040d61010078464405816214500941c01c0000f000d5124200703803058007045202224020038100b0282c40b0400b02c010603015100354141c0020010382441200f800b00c9440c81e50080e9001d5031600b40303090803002508259210300c0010686107030394420142101c251040305411880d1107440380c4c503540e125104a400032190b1450080d10002d0401da0480500250004160700480208900c1601c0108204082c03d0b81010340801201001400078441c40403090341981d1054500007495418420b1040d500030781d0111028585800040f030400c1000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 983433381 1250 983432131 983432141
    0x4021606060f18050a020c06040f05010e010b0f06090d0f0b01030b0703091101120e0a0c081507091a070212030904110a0f23070b0114010201110708030711060a 70
    0x1005000400410352910110380500c0403d10924004048030b508040f010b5200713500c20b07a00720220640052030202104c100c142440021a42911103070075039421070b0b090140c02e0140d40402112700008001888400001880395103045081500800c1c01243d030004544030280e000380d100e0380001c940c260842c42032034080844c642c03d000c01c0350350000300000f00704505c1c024001c200c003555101c818880d0002400004442d01c51240c0d1595914540ba1034203800d190a0030f0050701c40103409101001ca44a0405460a15103559040c0b070a40d6165100200820541d00c4130249050716a02d8007a540078115001c0740d44a103004d07180d80a580409e1420b001404107100200811482030700f0b5070107006846c0b41a8196809024801011001c60310303002c100440684a50485d1072228842840b000c0c0c0c00341210380050054112490850b4800d10703400042c0043c0c5114402480b007260300b48000d1010300c00003420540170303002d8954010701d0300c0f0010000c58031590003500400344d0320060f0001c0350010b10380680801c01800c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 983434631 1250 983433381 983433383
    0xc0301081e10110c0c04110d0504020a0b04080d091d07050c070e010f06080a05010b0f07031b0606030b10030507260d081e04080a0e130507260f0c0307030605040216 72
    0x222171110600d010b82454050f03500041c0c4c21002d2142031813804229070020303140044c800c0341d2002900c0004038144002e08013600c00381003142c000b00b04132541042d003d042c40c140d540100740004c182e80c1035040e10b45082c04100b40d000449280603529541c08e00d00d81d40c906400c0740c0083e1844010390b0008a2031200e1403800c0000c480499850540700d4841c01c031400110740707003030050014004e8100000001c01041d00010322030184a4a00f80280390000d25000e50f881d00c20750300c1220f81c0f5403104010402e110902c0480d6401c071000258444480e869903036150b0307894a480c030030600030124100a0040e07444010001d001845044006d607a0340c4a1012001403038810210f032065111080724000b400000b404190940c03060382c1c4501d603d07281805504e02034485d030040403a5103601184210721040c0c0c3c3e043c03d01450b40590310315150749160141f0b40f8005210501c1c1c0740b810341507500c0d0040030055141c9111040725040300201204d56a05d131221501213001c0c2c522504071a0f001400003404c02080321400304900310301 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 983435881 1250 983434631 983434633
    0x702130912031103070207170309040f0501090e03030112060b180f01032001050403060b0a03080403060c020d08070f08060f1509030c0109050102100b0d0b0901020904050c0301081e10110c 82
    0xf1401c0041c12100c1c1e0200b90348900060b4442401030103070100c0050302d442c0590440040320300300a0300c00005003d85a0305001c101c3c03499201e00040004402d02e0081c0752036070354860069425507040c815240100c400802c005001e03141c031400701040b81e8540140c003800011500d400030344149810780090145500031700c01160300794503100244c5580c0601d04403424031010305070b42c0c451510b031554407100040c00044c4691a80320080e100000002040c1400070401184641c001240500301054068245055040360500703101e0540100000700c2c1d4860440804410142804038641d2a1200464504c03041030079181d4005030b8195042e0522039180c0007a00a461048040320082d040b84030046402026502c1058013603400320901340b48bc140b107500314420400003c0c0642031140265100c81d0303000201942d000390300f83d5000640110030b0500d4099107502c100301015491865142111443c0d41d9072a000b00180080f080300c1c00414482828000c400c1c2c001c103046002c0c8910314200318036091a50000e2061021 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 983437131 1250 983435881 983435891
    0xd1205070b0702240a020408060405150a1e050a0605100309050c0d05030406120e010603060203040b06040603020f15091008070801120b0105040b04090b0709060e0d0209060402070213091203 83
    0x11584005858070540660244d003003101002e4002800200002030302100c0a40c0d020b1002042c12103080200070304c201e004a004113800c0c030b0015801c0428030710142c99140810b013401524440e000c10440c5007024000e007058001040d9540e424441300a0225420083c0d00180b60310410701e100b076054211007035160056090710036002e41da00030424440c00d0030000030281d40050100704a5240100c0056501a04aa43c0030600741142c448040c2107507100d800c100d801e40e9010060000b071110507490950f2045058500300141410364000621101902d03948900c5401d042e8035120104000e04203442c00007401508603064600903210103411181d00711140d40018003054000a0f841521011203004d135500503041c4002c0340d0030b00040c800981444800c03c0e80146e02c4003410340004002e081d07000d105400540c0c4201c94641410802808001d500140c1031241c00d40b0854038016a942c0701403c0d800000440780103a5031010f51001c81d8005503090401e0204910341603201d41801300312a178030741d060410b03a5800c0003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 983438381 1250 983437131 983437141
    0x1e030b030106080304050f060318030a0c0b01050402070201020a12050706050907092316200d0809031206060a180311012606012001110c0c03010b1305060d1205070b 72
    0x1644c0e00a9205542c3e01602801082204e81483c200460700442508030005c000d0700b00c1941c00e0b2840d84002c18450000781c08000c0031040c82104001c450241904840035450051700d500000c2d5a003081c180f010703003959003101c100130b80c041c00303881200c803026440001403140e844c04240c1662100e42500c1810001401c04883c0c090000c2d50b0f210784d0400c0c0b500c11095007141e440d0a140041104449418039042c03140d01035200e404080c111a12450b01d00c5540014001003141a10090600c1c0c00948044510b0f40184441c1e40c1c0c0c5a00303480a16400b1005035201d030f4480301c400c0001c80e44012801c41402d8004141ca40c0881884440794080701d030450280c8030150b04601c0c40309035803134031074007014a41845021840030841540c0719003500401c3c0b1070403140d20b502c0c1c1c400e05880c02c0d0858020000c488218400000d031803240240600185400a500320020407201a00c0800300c0c2d0001080c40a02a070780f40d9410001d20a0b580f001552007000d50040301d0b03050102c40428000d86554000f00040e260001d070880022 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 983439631 1250 983438381 983438383
    0x3090c15050403080f0f1b0c0a12080903161805070c0b0408030a1401060e1906050a210f06031109010f17031e0405091b0304121e030b03010608 63
    0x1000403440c503511140790900c0c5803114801c80e000400e10711000f5000300110000108804080c1549011888100d40420104c07140c41d45480c813000f00072401440040810011445540ca02006281e000603c560f641c0070410000703800e00c003128000c1d00003421400030220749004140078410803410f81441c00c20540d1102a400d503501a104400203043c8608040020001507420002d0364000c601e088002c56010182480c0c00e0310380305c003604804002000d8604000952a04001000591f04001c041404150612000810500c15a07815000340009000803512094003030403c003500b18143e01042050703800702c3c00c0b0900a0304c10781c0700649aa02460b1310100f19454008401c40c100c0f00141441c1e04001c3c0f42480e40600710f04c0c20507032442c880c04148061880302403ca83d141e00c07080c3d03522038840ea8070303400d0104014000002510345500d00031180d0ba400070201c2d0f8207089036082038014186101444040104682c01c012050742a46a06034144031019038a406400004003240b0443c024011161600c1d070785c0e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 983440881 1250 983439631 983439659
    0x309050708060c0703110a0f060c2309040b0102150c04090e0c0d061a0d060501031e1a0a0207230d0309020303180a050603040b040303180302062e0603090c 68
    0x1401c3c0401084600c0000780108811070030907403140c003503c0768130340e041d00d50701c5030191600380941e2600c0e1078691611407694024401c80100c52035000241c00406908901100d0303008070b0803001c2c01640c0d60020b881840c1e00030840d010070325201d105c10008904d405c50341800703150403c1c81098442c4e800d01c0c81d0a506d100004c0b900007004180a080400710f103545898280140c040380031500000300690342e0704d00e1980c13a8401c050751039034042d9601051952441ca80b0f01903900c542d9880c84000000510301c0340004402c00c210540d40a45010f4046203901c038091214000e104206008004451030640020b16001c880d040401001190f0180c90303000c010640c043d0240d422004c0d001b54582c004201c412a4161003e9840c4030414001d442004580d46031804600680c0c0700399015034a03846194100000c065142c0505084e081030368465840c0340c0310554020b562170740c0103030204407078000c0000e070705103149445450300e020b032118015500031055032200003038001c220450707066441a10440e00410036916100b02 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 983442131 1250 983440881 983440891
    0x504050f0f06121521060a090f03050715020706141f091a0312040f0902071109090c0a12060609021801050c01021204110f0414070e15030106030905070806 68
    0x2c0c075480c080d50460000441c030b000401d0020203003101104101ca43c1c54030701c4000740c2d42c03c5045007085036180161641e850880001c020b003103003c0c1012003520002c0c02c040c45858101d50b140c01c0076a11403007140342001860b00f112104101003480455030506002d4690400e82504040352700c6040240c0317440b5020319950303003600200076008003903030010450403a0a50081001403544000d180c0301c3c14400000034141401101a94141580860b080c4600110440c194004050640d003c51a0803800e070303507080ca103a41a0b0301683c460303402407001860031b05080c0700c40c809000b0700600070b40f401604c03100c9000110342050380648030350345450780200e9404034234401c0341c0d0261901b0880e401122400d400454040c0c0c4a404450b88554003840030030b10030b220580d12240114410000c1258207907102c01404031840d903c110441c4a10b05104040e44001814201c0940101061074055a003a0480c4c0c041200d00c86100065003c1200c008000941c40c1d516034000d0f80e41d28413507c1510155aa0790999540d02c4005441d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 983443381 1250 983442131 983442139
    0xb1e04060f0f260f070e0109140f030304030c0e0c0406170a02071703090c03061311030f0105161704030c030e03070f0e060901050a0f0b0a0306170c0a081609051503030a0504050f0f 79
    0x410711000c0f114410201c0e1092000f4003805108ac6007034007080c11500154800c50fa0501d610030148214400f8581f01d41e80040b080301d503e030526180150041c10000c11440d84000000324601040358800030b90116085660000405880c0000b100c058032921750049920142031700406001c21114603011540354010107045a24000566054035038000980c0c2e516a415450703c00c60030000342c40308003800b81070b100d204942103901205402d0280948401a000d1000007002812010800000d400600168600b505440c101c200e074580c041c0441d00d05421a085401141d502c2400000c005900c082014418003095603c40c0d0b103a42d840090000c112010302419961820410080c0803101044c2c002d0b040044041c500807aa507070b6220301400c6c1d101181d072184407a6800c10301d6041050700304282c442004186800c002d104d5072460004a4482000502903034000d070b80c0791004200400002003100940403002130503a031b80da6100000103489075001d44a5035015101c0310300c811801d40340803a5441620344000d4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 983444631 1250 983443381 983443397
    0x2d0a1d0d03060b0c030405120c12070312050325030e030711130605060a05030402010903140c01090e16050c0a0209181c0e060702040905070b1e04060f0f260f070e01 72
    0x508100d4508c2e011013100e000c900c03400e0700c1c8804503a201ea06a03001c140d801e030080d050302400c604151a00204040000c03003440000c200b0b01003603120b00340840c84410700c20354035002001c1403040201d024181c030000c0c610843c4400b25041080c0a4103002d4040300c60703012141c14881100130b100401c01c0c0c0d4010312985501c12014060601c7c1e00380540000c41d4018130515004141d01d440703507600c2d03000041d82d000e0740c0c00c682d000340003003c01542c0000ba00c030090315055281c6202407914290301d005036100021501d007000b0f40411880307aa035404004000005600030f22844251a00b03009900801c02e040c003512030b4030721413094408150306030044417000106151fa1180440c829030028452598000f100403a00030303990b00000700100701c0600a0101800c1245a034603a51001d00c046140341048d90212a084108200000c01801d600000317000040c0c1d0882c1880c6203010300441c0103860351604020000307028403482c0200a0601a8440c0e05071142890840101d69a280e100c0201d41041c8272081582c0490040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 983445881 1250 983444631 983444639
    0x3010b09030613020f060a05040e07030509010b0103090b150a0305010c0203091003110a0813020405090c010e01020c0f040c11010f09020a0b0315060f2502092d0a1d0d03060b0c0304 79
    0x2600081c07610102d04d044c034510b0a92b031504001000081117800300002645d90341480740d22030081c090075681000c2441c040c4103014032500c4094854101410341c0c211414141d00c11030490b294220020000d54000c0001c200355501030201079180d500000d00e151288402d510001809406482524041d1745412421800c0c140c03205c20a860028026014100520340345880c080180c0c0c03240241e91203502044090003a8980c02000034040c290003074200303819900020404180c40d200c19440c0e480b03543d41142d020406081580c4142c1e03130345180030300e4280e65508003100e140e01e51100d9004841028401e030740440e0401ea0302e04900b400d034003040e00e0800248000c107121f0102803610002800c0e940840c103502500d0070091170340d007586500c1c4480203044e02c241102d0b106400e62038021001540b014040345500b400030b60240400305d0a040e008109800c0b202c060380031941403c3d2a034800c40840d5014510592040c0c108401e00341d4072591184202c000130f0910501249040940c1d060701d001c1e4090030011814039043c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 983447131 1250 983445881 983445889
    0x604050d0c020609041b110c18070e0316061412040311030c070e010302030105070801030317041b0e0f0c0a21090611070302070b0f040303032003010b09030613020f 72
    0x2541d0241c2e0301c001c0602410300c03d03586603c200d003e645c1c9805901d2071b00c2604070340042c09000400b00180c82c4c541000c0c50b092041c7e1103014140c000c506e4401c007610480c0e40c609409039144408200d500c0d0701072081000f2450803040d01c40d811001d4400d0b5031a00a021040c01460202c144120000c91084d03018903c04100041d004840c403400c40300000064034100b281906105151490a50001e03035400303001e100400035804d00388601900890340c0c0c070b0320401c90f40c15a24054000c0b01c00710400529402c82900040c107000700c422104203041541000314a04a40d55403500022180582d454606d103a0b03c070700132030b00c3c0c486940e0843d80c49110540f10610301a00b41c0c50921780500101009407030b590b80340c0c50482c0005100388118501811000241512180e86080081c540700d02c50b04034020409042048042140409081d03c1c11241d00d880c0104100300148801c000d10001019002c506000100001c80d020800401030054007006904070355441c0c4e9811103c2c40342c46040000650400700c4040d0854403814 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 983448381 1250 983447131 983447147
    0xc1c05060f090928020f03011a1903020307090203190e0c010309060204090504080705070e0124021c05041e0b070303024b0702090a0c020a0f0f03110604050d 69
    0x40d0803000d569042400014900d40c0036000d81c0c030f0382544d4150000349011441c06500400320789000303030000c101808030300d4150b100c20104e00c0d00c4c003445003004c1948400c000c50300c040c1801c081d590103801e8a400e19551100d43c0060741098900040c00b000601d0f00d150203030070074440d8090208502e070061054007444401503000703084c0034106940f82c2d5001c002c0031800200900503580030702d2107194015542c030510700b00369040c1003142e00020309a03082c07440100190300103c80d034210b174004c2c1d00e140c610701494581001c0c1d18100307140d0b90301c071345071070b601001c40d160300d0342090240003220b080c00400026203242102c0c4101c0503d20b4090b4000c820424003159021900c00d41c0035100092100c0018140001c003000d8083c91a0850302c0110034034040a0010200c0700e000024844000c45180101401c100540c8e00181c884000200b0808009565068429200d4400c2040c04112608090300c1e42000d10607041c14041840000300590214540706003c403003003100040e40a2280d900070011b00020110120304071040e003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 983449631 1250 983448381 983448391
    0x708150f040f0f110a1709120f070501090605091204050102120703020a0c0915150c030c03020c0402360102190c0e07030e070f0f12060e03030c1c05060f09 68
    0x15543c1112040c1141244102030f55014080741c5140c41c1d0201d00d0000700344055000810704150b20b09818003007421400120701c8500303000c154400351241c0891203075030103c0c0140c4c18058441d40c2000580340901480798046801007581302d041d17407600000501c3c03109091040d44601401039019002803e032499111019003200780c403d1054038080c0065448000d0060405d4105020041d40c964030450060a601401e2004002c840156883c007040c2c4407000c0d01c1640c4104010381408058200c00c4c017007600c00e20921100c080020011510b485010490f0300d14040024203050842c038640c0c114003040720041100c0c042d00d1005a0041040c0200f4031000071044a007142c08848d851401840450760403e00c0081d54032500700c6a41c00281010080c04451408260750703c82076480490368018403072020402c7c60710040d00e502144220800d403a500e8148001c010345060221031740804001c1c0400080d018000f00343c0c0c0c00118451015803003008078034008907001a95400e9120414491400391810300001540c0d006d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 983450881 1250 983449631 983449661
    0x1051614150f070305010b0d090311011b09050d0c05060c010e0a2009060a210804120227010e041a010e06031014061203160303050708150f04 62
    0x2060800303818981400076400c03490108140042041051000c01d4007540036400e4030301440380f54540b6600000d81e2140440c40c8010584502040b2306050080c5000051012444001c000d101800816480b400b0701e0448114001004503100080500d04030194602032900700642801940c80c000070000c6960001c910368215540f5425007010742c00090151303d5029004442c07005181e10030104101828071b25a15561048500c0c50a021107503c030f03010064207443e41001840603e02103840c040e25054051000142880d10005003c01c11503200081c1128480c801d803641d014444803a20b024000c0c400d0519914210f002007401004103002019095030000d004001c0301c1c0002604000d45100d405003600600d020000f00310900c02d8030305003040301c00c0e56015005e508002c0e034a4814140b060000300500b15034400c0344200d021049840c01030045680e009a09081c0c0d03c203c0e003862030060301406080761800d0110b60504000b03442c0b280b40440303406e0480001000c80d0150681c0204200042202d481d98100d2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 983452131 1250 983450881 983450903
    0x4090f050118020906010c03020c1e060409140c0406021b0d14010911010f201507020c10090b0d050c0c0f100e030c070b0304061b080420010516 63
    0x10030428440c40d44600103031000b401e011045801403054005000e08414100040280110003181d4085107408010800310350b10711500202c55101c04400c00440465603025034005800101c00358a6402204603030121400d20103140e480341d000c0c80640c040d621924003d608011904800319003040c030000e054160040c00d9a030700d0340c0d041d100c028294040303d044407041c1e9913501d866818091118000f2a064200746018204500e40311030081041090604495900a550030180708404c0c0500c00c00b05140c14980c8104080d00c0d00071070007980c6243c048941c5005890024034015042d2160810105807007070300000d9484c0900d0091964010500145050400304080c040308140301c00c20300000000e042510010169800c010f1400c800301e86950900803d81d6000304001401c80002284200c2103c8011140700d84a65413401c0100c0a800451412500124221541407042740c01201d128040c5018441400c0c0320f140011804ca407500e00c1c180b2041c00300b401440803400c280220752003038805a11503628000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 983453237 1106 983452131 983452133
    0x2130509070906173009041409030307091a18040618091e0b010302010c061104090608060702161412072d05010912031e080a0e030f030604090f 63
    0x705c0c15070f01054500d000c2d0345a902000c4400f070b01c0400d101d902d00e00031117950f03100c1c2d108868000200d6501400800c1c1c001200a20301c55215110000301d2414096000b0007000214081c446a445a1542c1c00030038207060020769120000c4c801e50000c58404054984650b81c0c039020302038080c01c46005941200400d100f62401411681c0a00303100c86d84a0603030810101405e01c41c2c00007038206100040c0002c10700103540c09034045552100c1a5001e986403c03904985854010300b000f407944101060901884030801c0310b942100c00c0c010a82038004101400132030034080c0c290f11401d07031550a02c0c10301c2003422000222503681078850031800d295a09050020b000c00b55140100b5825201c2c2008590406000f850500c1d0000c0f84407060009140d540d40c0000e142c068111641703e445824400410800007002050342c806920480185055559050600008050050302610040d40c0203403090 = true := by decide +kernel

theorem cover : BRFrame.Cov 983273381 983453237 := by
  have h0 := BRFrame.cov_init 983273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 983273381 ≤ n) (h2 : n < 983453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
