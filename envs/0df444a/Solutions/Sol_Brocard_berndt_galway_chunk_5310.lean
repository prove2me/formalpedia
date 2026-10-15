-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5310
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:26:51.974215+00:00
-- url     : https://prove2.me/submissions/e722f2be-45bd-4579-980e-16b6960f9776

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 954856115 ≤ n < 955035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 954857365 1250 954856115 954856129
    0x161418011d0f13020c06040b061c030207060c0203010e06160f0c08030705090f03070e09010b0103050f2a031003030f0323150d050c011b030c0605181005060f 69
    0xd010380c85035080b5000400751030080600ca4007840042c03c05420720184440da02d10340682546c0072952042001c04101487c00c01841a0048001010560b44101541d49002e515501c0314014041042490b07030140044d0b4500f500580341e244040c20071074455140061052a040304062070080010300d100b10040341c4c15103e11194041d040e0003520031842d40c0c440003c150b440d075001031212500a141344250b1291941e0910851004001e0508501910310301061241d00b101c50004070703035040c189001e0034418182402c2103600c2e4031021645180341500c0501d2203400785c40340b80b46081c210041b00041088071a0300b420741c0d130001b102d120ba194100025031107030040e016200007103455100114154441140b06c00030324015500080c1000180720150503210110385616031076602a500e82d800581401255603120101e4002c0d240551242d20f004142550018803e2551a00241961341c0b170b400420030388018213203030600d0703400341000f1213000444100c00d840141ca02101d08030300c2101130405003065400c0900f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 954858615 1250 954857365 954857417
    0x360f050915010309060b1201060e0c0703020a080d02220602060a05010e0411150a09141804110a050907030507020c040e070e09030d050f090601051816141801 69
    0x280001c0d00c00750580110014010322205895081e2a00b016805944680b002c00702441a82c000114107181070210806d2098000303001c0c0707000b150b000c104ca00e010a03408104451001d52020071241d0310b46015101c0340183c001d0700034203100d03400100401900145280300107000c03140c298003503880780c0d91454980e0080f100c0903c074070041015040002400145912030603140718100a0148010a0000461200740d0704010700038004580400002d0240343ca0243c840c441003d811200740541d149000030f00d401c0d02d04003400080018101b001000c2c1c2d141e5841c2116405424041c0a404c501c2c90030000050251109490100150007205400d41c1141014001c444005038004d0042c8040b92604041160100b002010009280028000111022041d00840340207207100045d0202c130b82088280d440c100f260683c8118414000d0f20910344004120703500155105c007105005107542800c007102604c0580b1a0507001c28034800c0040c6100001e201d00c0c0c1461556003080c2c1c0c0f000c03407007141d00380030702e111113125 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 954859865 1250 954858615 954858631
    0x30a1103070f03120906060f03030905030d0c0837110f03090d06021c1d19080a03020702120f1b090103060203071407050703170910360f0509 62
    0x20324000ca010030b018607413440c14410522000180c03400300781c07500030484916802ca025803400d088410030506510603424009008c0480151114248695003c5c200041c9000c0050040c03401140c058030325800c0c4071044429030314000b00f00c1c08440c0207003078070364003600c4c003102c0b560205034001295405a0350004144078410390803001035207070103480d4041080e41c41e4120422170319160204030018030351180c40e12101c0d80105514010407440351490340d07004012490044108640d00c0096042100e1550011a0200b59085001c0aaa4883c6028110085c2c03140510280d0850002d250843c40d5040014181c4040131010068450501d00e11001280300070300e003030201ea4803004000042c00443c04d80d0380150341007109030404560303140d200380d0100e05640021a05a401d50083c40040050003904218000903c00207000c80c1e19008900c0300250580810f41d9042c000c10a4000c20820014030500c8031420040c550300c0350450003000d28a00403180030b1140180318868822420004040c108081d8090051b264 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 954861115 1250 954859865 954859883
    0x103052b0f111006031a090d0905130b0319110609060f0307021e06010816080d08040215071407080105071d060d09052a0f04151502030a110307 63
    0x203100445590300d01c040303031180324007641c1003400c0f00f02518842c0394000c5114510114201034420710700e0b510b680c00200300450581208242e550b980b40c2c8404420140e5804a8400000c0101008002c00400100350a1a003600c41c00e010a5509803070b4404415035288240c40c2082c0da04403107410b110060082104450f0082c5042c482e4002c081e41d654003555001c2c0e9030703204540054148000e5840c1003c0300d400651000d411050061000020910054061419851070011403603c0c0c500b01994039000080c00341d04104180c4007207809c5540344420800100c4114000503240c0b8014140626003d80c0c003202803503a441000e50004041c54107020704c91080d8010f803100c1c1030740340e0185080ae40c04507031b1004190384150304205d41100d1140a110350074070075008000034101c50340200d406580303840c041c00d040540e01c60074023210f0170107982d0f82e000300f14031110689000c250307824140d01014203034445030009900081d81030345116516500002600d03050340c05540e40245907281c54106500c0c3e21950a010f402d50403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 954862365 1250 954861115 954861137
    0x20a090302060c010e011407080a05130b0423070e060901061403130f030504091503080a14070203010c0c0c0902160f050c04050103050f1005150d0206040e0103052b 72
    0x2421901500310f4003000c500100c1c0e43e01071002c0c1942141c0443c0801d0541071f0004044c0f01100340e20180951307208100100401040c242018a030220051507000204401c1a120001d000c11541e1039000f09900c0150106881ba581446006501c40071a4002c0c104904090b90008030540f8040b80d400f030480340240c440120798026a1002541c030b0f8070040210080148026500d40080d442491615030507000c0c1e81c51070f44840c200311000301504c11450034000361080302d120500104012204660300910242403080d0301c04031203190658030b1302030407401960652030448189250b039040003150240c14850320320050740130744840000d412401901d0150308520400c0712410002003d425894440d01e0240c0c048a1202e0078000000341030711001d80044030250000e488800303c2600c00c20002d035220408500a10491401c0c0560441d80001d08c90040e02ca0300c030040c510b074150b494950488024001c81d859130b861543e1039003081c99848016482c00883c90011030326607244404054102c0c14075511564440c0d042c40 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 954863615 1250 954862365 954862369
    0x90d03051614070c0b030a060909051209010c0503270307060903030e040626060a1e0b0a1802040e130b06090a0608030406020a060f0501050102120703030908030721020a090302 77
    0x80b088102c02d40030200014404540000040c000403c50741c3d0fa202c1d0340e0710f8030716043c5050300d417542d0011014508080701c000028a012506c04081d06030b03041e90030b03107800c5642c0040b200f19580450240041c0400100001002c03465182c4119114070141c080d04c40004500c18103503101d8481c403030003000034405030381070000070711a1149498002c0018004644a604c400ca040580c0f211003441a070380c2c80e80c5d0340680d01540b00512040c5d52181ba840010032044004050080340040720300442101c035541c03851000026503602c0000c10141c240b40908640644902c150301c0001d500c07600400382031022580c0019050b06021806e40c0344143d10a0011000d03032203c3c1c0900400c800d0107010740354415166440800c02c1c007420405131004003583c2c0d0003880b02da041418803000301c4900700580101241042c00511559030009900c95000000c200307040e83c1c690315420308030014003a6100003031060310004103002086a11035030720202a0240c225102d881c0144e80a841d08074850081000d01217155503402300054 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 954864865 1250 954863615 954863627
    0x2030d2f010209090c0c07090614130908120708060a0f06180504020f1c051e070c050d0f3e0a05070303171b090d0f0c0e090d030516 58
    0x114100e48005420250110002481454100d4000c50281d8001c0f03044a0004007c0040c00010103403444104102c9080141e81124140c1110f8154010040002c01c1056003c440e40411246a004060181c80e040d0031040c03034000d8a8143c4100001591501c0865113602c3e01c07429100c02c032074000001c03e00315031801d44141d6030b44641d81218000d000c4c2603078000903507441e240010841003540d005c84a55070402c01406500040c8107252010110f4a01810045c603000880b04075810341c00c20702062882c2d950703056400c44042e0300940c0000d00b00d024110361000da480e00702c0109611001d150712001d4103001e00250032210010000d203e117514010900310f41e00c0580702945209002d00c00201500d1200120b910760514252b0700340d00c2100002c84101040040000e400c68558110b18100012012003802183c1448140542c070324082c4110340350004031040000443c1070806441c1c2c420041d400060303035415120152841191015000c0c00340f0b680084c101d44c82480343c00c0c03050300c2001c541042c0b00c0c00c6200448030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 954866115 1250 954864865 954864947
    0x90606021b120a0309080106090203040c0b09060d0f0203010e010605091e031e06060109051008010b181002060414150f0604110408061e04050a02040509031e0702030d 73
    0x10001d6061a0080380c420b2200f40012400394540945031403908906908468003035102c40d10691050090100040416284c80f040b03402c850503094031800c40e60000760681c818190344650a0303141440f8007103d143c25802a504079050400104501c1c0c0e0384110984040c451362046941c00150344520f480301c0031610008102c01c42c6d010701107940010b0801154200e041ca920315038090350b4841000c05c070f41503038007903084e501500080d9403420456209440c080d01100c418041d5400451000c0b510040c0f51801d00d0310429140307001400c0d013403010420700d00079448480c29903098681c10070407500c1d440c02a42c0040c41c6010b28445007e85007080c3e0718a01d803840c48004c040c01440d40300e5292464003400d81c04100c081c00160082d203000c0d2410b41010103c00034516190301004082c03080e48401c0002003400460025100c0307805072008680e81e40e0b51621181544101c01c0014907a820503004400607130341c0c1c2400b802040d07100b601104c1d90700780780e141c00f554461481841d40e1004061860041a407510382060110 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 954867365 1250 954866115 954866119
    0x504020a080426070f050c010f021c120903120f11090405090114041a3301140301060903060b120303060d11030114070f030501051f02030708070c030c090606021b 71
    0x3904031110001ca11540d44020805d80301d82552081d108140002480643c84030882400c02400d01c0b103003410040d449482512040ca20601c8019285410701e000392220500e84e940104e04100002903458050a40000d0b200071014107454980480900805481340503003070380c0510326031070816018504000c0a010024000c01c2d2039501d45070900120801c0004160140c4d02c070f9000340182041c1004070200e45a40101050008242040078200181c550b4060034800744481d035102c2c0a0148820050310313402780c1403510328000100040001119035100ea040030503244176440510001c4109410032200300b10b20701c4c10503103580081010076a00e203001c48007420114458029640582c8881000a0868031000d200d00c4503100900104205103900a80070034000c02c0d40d040402840d410301001c40d05e00c1c03001c0480d514114071640d4210103001e00800503a0074080e800483c00303030386008924244c00001d88a1000b1a4180104e00012035680d10300e00481080c1c5005034014403090140061340111091469201030b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 954868615 1250 954867365 954867413
    0x3080f010612090804030c080105040b071409010c1a0106200703120e1c0b04030806030610030b0c25050c091506090a08060901050907090e06062b0311070504020a0804 73
    0x1b0000d521614404000c18042c1e0002510f440c050a160700c00500003040b180c200403070319204a42c0c420456050740c0c1030301c6080c07070003600e51511442c1c6200b90b02018203000c0c002001c00000061a10350103070314041c0c0140c0c0000707841020203c1c030220542c0c4607503501005241420303145010a54510603002d60410420092006101c0c040101c0400010800e54030140c80c00c040140410050541064010ba081001034009200a00e000c4616682d1241640001800c2102d1000070420010496041c0d43d003101035010301040103204c0c2c502c042011030b2911002c84103805100c000e00071a28084509520805568a500c528801d6402c00c0160039401031481d03e40c807070110f0401040380f407020001e40e4403c00f00400001480d09103540100d26204a136404040150700b0700200c404100c00100d80d03640c010905540039108908a44ca20300304541c0d281002c0e06949440c00c20b4101810352010b00707608101100010794000640700c801b03000a0344203804800340410030b03080104000480100c0185031080b0b030b440400b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 954869865 1250 954868615 954868619
    0x50a0617060c220b0a02010c09050603040323040f0e010806041203090302160306020a0306090b102609030d1b0e0618041e0e070614070501091e03080f010612090804 72
    0x1c026045540e044081c07450f8020171100d41c980c0e024850440300e10700c00e080900f0900c1c0b906001500b40e1100401c0202003090106c0011040b402a110300c141140c07020307081e2520340c0c1d00c0d5544002405841c1c0700324071040800a000040c4d08a021030740500850b00300c0309100c5030301030404058016003034403001101184610001c814078280001c507410080c5102c2c0d0000b40e40c4592810780201518405d420440005180c4a0502c0040e501d8180c2c0089444180c140800044420804488103c150490040000380e00904000a101000c0010f042d000329840081146c52500e400401a01505164110205500050402031403a0220142c100c40e1408002605060042004601500c58144642c5215450802e00d001c200c020f500902d071300e02d0003038401802c01600c3c141c03000b005651b0b020344219904000003120400e02c00d081d00000c03a1250010242141d0106c00c0c114198007880e92a0f0540001d00e484000c9680c0018000c000343c100c0d4403c2d80ca208e400e80200c00094001c000b89241200d20f55420080 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 954871115 1250 954869865 954869917
    0x8033402100216090c02010e010b06030105040c05040807080604120f0906050d020d0c020f012f0918040b0601030c0c021f2708070b03010308070b1810050a0617060c 72
    0x1d40d400790107101303c08a44120306900107030035200c034410f4640c1680d043c045022043d482e0700c802c1d1380c11654200e50106420750040015507561069401c550790174028118045024180002e4882c01188502800f0b01d43c0c02182200b281c9841c111804000050540c8404000790b9104038090906070304005001480d01c2001105401100d0709003c018001da0000303103003004895028411300e160810311401c408034100d006031003419581d2510748580806803020424201c2c076255414004070b86103483e1040c82c550305103401c2409140504660b480d0000e81001e08410034244030b00d00030110141c0c0940a041480d14020140c4030307244550350040100449143c0100d5003140d200480c2d081d0507030600103110200d090800150903c003064018034080a8104010000940000b00b2200d15641018085590b42c9851006101c0700031a030031510a2441052403c0f1448681c42d44618001d41d11910204043c50b2390b1060119400100f0b0f40141c002c2e005040012602442c181c010844118100c00014007803a403046 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 954872365 1250 954871115 954871153
    0x2703080f0c032803060602071715040c0302040f1413290609100e0403030b0a030812060f010f02030d240326070c06051303020a080334021002 62
    0x504085190300702000700f01060550705030854607420610f8140056030070108060b6842c0d07007520800c2254145941c50030002601070028544003082e00c40703809028200343c03d20080c2c0c0801800182c0c0f14514041101d018420b5610079070898454841c042c414550340d2004180708400a1541038030210305c00030314034454804801041a204001401c0341c100f504114091103103025005021100f42c0203e4102840200e1000a480354031603810726001c6216a00e420200d038100106502c0100f19480c0810280050810408041e10030301059451007c2400b000004681c004031101d800400b41c1c1003000085801d030400d4100341091a4104138410700d240744000b0f4001c900c0300c00d60055130301d903990307540c0d0120040305000500c01d1940310003141c80c200551505d0b00300c0300c141e1511800707091020000d03001d03848480c055a00001140c0060941c0070762507039100b2281d2207500c0340b0400e216400100c5160b03040d1700100503041c100d030800b040e00c02d130b420b1986a0030710000c00d10401280b0207500c54040c2c0565669407a83c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 954873615 1250 954872365 954872377
    0x60c030816140f1e040f12060e01060f08100c050414061204050d08090c2d03010501030c05010311180f01050c100c0f2d030b0d0605072703080f0c03 65
    0xf040c910f40e903e00b418645000d140c1100414841d03040304000401c2404109001c54007a40c007407071071002070b101030f82c60100010540081142a15400c000b0005000d00c2c0d8101d0200840c1c001ea000d480d01403400c40403640032180b03030141030300204109200c188850200c00c40d20112605000d40401d1403c2d10502641010b0041280c0c2116503501016842d0030701c82c1e01a031070940055104004181a96500c4000341d8031005000003c0141c0120103c0c098803804171440c42188030700050003c00040d6105c0c208ee00e1280c01e02e0050701d021a0604d0b4240c960340340c0400071281e154030b8520150a50701c0c0030324100300141d01c441d90198100881405241c8001e842070100c407144400c9581c1c0001e001c4000d4002400e8210040340310003d0000c903810b100c00059030781403a070361000035200c40c040c02c8210b407000c164010190121110f4200d0025840310040000d2030f4041400754050b40c80740800c0021b081c00780c501c03190383c000c0d00c40f440c81c091400800000744054040c1c4032004840452604002d495030800386160068 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 954874865 1250 954873615 954873637
    0x180608010915140c0702010e0f0d030f03111312060e0d030501080712030806191e0f05060304051e030d0f15061107050d0f06020a0f09060c03081614 65
    0x2809001c00750039a00c9028200700f541c031001c0d0071a1406201e80ca0745400b480f08040d050002e81c41c1e0080c01680c40000040100400038540380342c00f18241001091b003144403900318042850081841100c804080c281da03816a21001030b04003035402d140603c01110320001044505944808406143c0c100510504207031684540e00000c16601d0000c0240c0740c1038899005104179080c901409021070742c040b0b4425403020003034034a0840031440e5030244800e84220340c490301e00c0c00e118488011015485001413001c0314a9407408a00450f190b00030000700d44420740c0d00500950144640070344850007110103810010382e082c29281000744414190060310200c40c10b1a904583d0b6502d10300d01c21540c4612076000d000c15103440702d1421049032540381d941510740a06032040c1d14815003481000800a00e401c0720950080c030554940016a030041e20000c1e82c0c1d04598080380d08020081758171489548440689501640c42c5066900c40b6030006009564192840d0300308103541241c0c0110424110080c5100c07581 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 954876115 1250 954874865 954874883
    0x90f010e0d14150f041a040209130f0c18060f08030301030201140c060106030b10020c010e040f0914030a0807020d050f220320090103020f01050a02030712090302090f07091806080109 80
    0x1034980310101c403106d82003000c4880710b1a8240805a100e0b80562548902d009428615280c420b0034410391481c13005400070b010410b0302c00b0204140101c43c1030481344090b4840c060012540300d020309040812540168401c651007400100301541c42400c901d800c00c03900781c0900740b500d0800e903191810800709070000302c0802d441e41d8045440e424102103260b4840305a00c00b500c070003d00f50700001c005030f05010138075128a4450380d0742d11a4022030741c09512165072118840104420300700509490340c00c0b076124100840c5410001405150001c140141e03401070300d585441c074046801e07043c4c110302d07082802001501303031b4074042041c0344248c905280f801540c041ca00341000030311030344c0c1100503039030026620a0180640200401c01038440440508000340c0c01d00301a82c83c1c01c140d6104a20b0750103140000b502040030b582c9044582d0303800c4900380c0d0650b4004e179050314056994400031306903500141ca8000004917a0310003000302d01850b1a0030302144403924008503480b0390302c015280c295040f01c0029290444 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 954877365 1250 954876115 954876121
    0x1507080a092112051201090c050c01020304150507021203070302161b030b01060504050a1404090f2405070807080403050c03220f050a03060f0605060f090f010e0d14150f 74
    0x80002100c841101d07140072468881700ca52a030340c541c1010300c2030690300c40d280d242c0d001c1b03010700403000c3c1c3d076440601800854481c900340c1411001c5504205e0306001d030b1440c11307020824181c404101881340000200320300d46181c803024001c90095110003400010b0a6500210324001182d41d9145010411020600360700d00b41941010501ea200c10385c8035405009040000b0016038a840d40754400b201d0305111614003504145c004203000e1310300f1490051003e00c030b8000480c1008810320a048490a0702d240c0e40060605c0d01124008854050b00c0740c0c400302c0c41d0500080d03103182c0b040d1903059226110349019070610000700382007803541e0407254021604481061040108154007000040240100c80e0440121442c100c080342d02107000f4003000e00156103801164080030f0003600a580104805026145e4034540c614003215550410814188a4110700c00100e02640c4a06500701822200424480c06c0032035690715205000c03c1140842d00500070f14020320401c05030100300c13502c903541d183c1c2d0354a01c80ca = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 954878615 1250 954877365 954877373
    0x110703020f0c043b0a081903110f030402040609050c090909070501080c03071404090515010e130e01090b0709080f0706080703050601021009061a1507080a0921 70
    0x2400c481c102c58010b40c5450b03002001c0a0b0500322016441c110510300308104120508441d00300d009080904025200b0900c854040000241c018950200b1662002c862088405000c0f01900c009003c0b143c48090306110080184040c00010760300144000c20000c1d10940d220191402e030342b021a9030310040c54012600c0300d040d0405c590722765804200c02c0048e0200c2c41c280400600301c0d11016080e82034030b89000c0f0008120a005500400000c00740507080e5458961780c0040c400230341011500d009800c9501054801c00d540203800c45500710000419041e90001c851f1480001031580440224880d0749030030a030804a80c0304084603000d01c980faa01d00c0078950529482030f180c84141d0038100c1407070b07200405c01c11131150f00030000c903003210041c0740110741500c0c1d05c03004030719003245041c90038410703480c00380a8400c2082542c024031083d071102a0a040c1c8810040070403c0c0d1440d1000020850f22042040b000020f643c2d05c010140d015150401020141c0c640c8844081401d244914064900e2000e610100b44 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 954879865 1250 954878615 954878623
    0x2130b090f011b290903030a2703080c0d1a0f060a02150421030f0b03011a06092e120612021003020c010f270c03030e04110703020f 58
    0x4070282045803901e0300c03000001001c03c06140c0082c2010302c3c050a4180141602c0e540c5080082d0744a03c0655641000703881e5a0300d943c0159198074840b071800308031000389000c80d546144400c400b0804026050b440d604d0030345025a0080120000140811603800211035a00c00c2c5c800845007150446c000082075400e1100402403440010b202d00c6c0c041c06001042c982c0041c03207040505640c40c149050b038032989042c0c86403412411007000b400d00741b0a51080895419440800404e44401051042c85403881c241422a080c041d0550f48422498105240d02d00f4050010020044054041000b0110070703116015160900042250400e004100c02644036a00c10030480400400f500b003081030340e00d459207165a40b485008000d005070f4020411440d0070b4041d85c15102100380b00c02c000c1c05032031aa0b90803100141404850805c001e1110002000c158100d000c1c0c03083c80a40c0700098018090840e2002c4d81d42c200e804200390703031090b26002c0901800b1042400740c00c81620039001019a0280320300e2311410 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 954881115 1250 954879865 954879889
    0x8220504050901020f030417040b03160e0105040f0e0907150f020c06041202010807172d0f0705030a0204080a030c020906150d0e03120c0301030308070201060506090103020d02130b09 80
    0x102e0b030b00500169020000751000c0f207400c9540001560150310a18a40200f1802103510880c80c840340402001605108000c10661001c0d29070b45050381070440000556050042d030081284041014105000c0c00c018948802c4d00300300c5100c1100e05080d13075200c1c4030103140c12508180e400603d04d50103c4142c550100002455000304807415801c0c1801c05841d0943c0342d9801c20040d04019410022a00060141d03116038400b00d0040009002d514000b840d00d1181003207031400003d800d1b1200c0c80728203020320011707910380144481d501d905003a4895080c111415000584407409540c2d082200045400c1d080112002c1c1501c02d85480360804640d004010807103000401b00e502440c421100c514a40710900202c402c5a4003080d00040c014902a40f00391031360017290001c40d00d22201c641400f0076001032901950480f8829615041c041d40d07190b0701203080e11064411150040d0041c4404a510760084d00078103040d50380180300504042d114038074480301c1015a07002100e01c050002e01101d0500f829607034004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 954882365 1250 954881115 954881131
    0xe1503101e03120309020103090b090f1005090a0210090906030c05010906020309101b0203030304081b030705070e06130c0f0e041109300c040b01030c020307020d0822050405 76
    0x20840d451901d035080c3d241070ba400e40e0020035640380815030441e8082d03400f000c03080d40c21a00411141c5409a000c2d40d0700e6246d001001039601ca8841c2c400040341e5131340107a0b031040d4001c0001c1c007050300d0756900f0322940c240701c48015401d1181854020445000c82c0c42000010b50160000d8a03000d494900090000c0186801000464104204404154841c03c2c045803158080d03181c40103580c000e10100d00200303a48418000c0d4507000000c01e10081c440758801800c0101c5041030344005d603100e411000c1d40e492090000c02440b5801c0f81c0020400350b800384c081c0c0360340481e000c1c180d440c0b5401030000390022500000c200002185220242c901507642c80100307a00c841409a50411410384208014605070040340f040f2071060900c04c5428001840c04102031074240c041903446030645900d045c040d52505004220140520b15109074400319600c40d000713000302c10b0303001c0e00514500704490f000d1000e036400102007641d0310081000702d1f01016001d61041010b80d88246041da0516082c14208400c0e50001390080c8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 954883615 1250 954882365 954882419
    0x11425080c19060b0d051b130c050c0606010503220f0b270607230d09050a11040c05070308040c0e1314060601090611011e0203090c100f0e150310 64
    0x181d80091206d444581480c105829030414400154002302040500e414403400c1c03c0e035046800e038010003d0400100344400390303080b0b80c0e51000115224082104c01d414a1948904280703013812203c8100e4240501880480483e6515500d422030100401e86101507400003821403068049140e00004030380300c01c200c001c0e200a08111000804403d02c00002401c3e0075a8040c28803041e03c1004120382c0c441c0b481d201b040c0055042405c1032920b0303822800c0e0680754a000c440e1016002c3c5014414460a89070b151903507414203100e9107040340c148900502c112144c0d5103c5c1c0c40480c010350000d01c814800c8004251888580308103160100980c1130310300b0290115407141c01884480d030b8100c00d200c8140c40301c03454526004203011511074003408140715200703d20007000107040c2980780d20b600190b01c0f80e90100b04407a04a03026005210b1487d07028400d840004031070400b00c58840348258200100a1001054801c42080d6500c100031168070a4a501c0c840100c103420810400404031480303480d01c50442066 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 954884865 1250 954883615 954883639
    0x90c08010b0d02101b020d0605060907031b0f0c0b09030a02150105030607140f030705090a061b0209090a0204060b090f1005041503060e090a02011425080c19060b 71
    0x441c0009150329a84c00c2030000202c0922076030f8613880c6055420300e400510400b140512401c0c0240200425110b0754001c0e20038a00142d03407140030b801007600c4a440740c039a04110380f411101c00c41d250144c044001c0300b048070f091032000118a00c080d041d07009190000241d6a50565404003a2034000c0c01401545e03c00003100042000395030119010768800c00a00346003094038807201d1490800d10411304544541d20010040c4902700d58080060042c2d81c0707090710440c0c2000d0315464190341c50020030011b0720f00304525026480040c10700312112a041403803101114851440b50740010280d4030150070000a0100c08a0500041d02e4011100804d03148150780d400c6025001c084010310601c06c034084c19040c001400e52034556a072099000c40000d00d00281209042e040104085803695034401c0180d002482102100c01c2500d0b80780d040750642034407500b5050360849000300101003c203101000703843c402c4c0d00b40411420b20300c084c040c03025034100e800202d079403c5c8000d02c1c0250071140c26990543c010f0f5508851 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 954886115 1250 954884865 954884869
    0xa0b120610030915052550090312030402040f09031e050409050727230310022208060f240a0603061a0906160f06090c08010b0d02 57
    0x3c0100079840490b0003041c5d503580c840c450f95082d030303000002001e034008000d248080d1560040007080e60946071b83c0c034100000280c04503070401134100040007030b2044901041003200d903594081c040b00c00400300c01107800c1078000300c0024103004045030082107481002040204528040c441c89190001d0b001003001849402d403001030032502c0c2c4416851322500c00d20307808180d542c003505c16540100f140d02d0080c0203a00e0041e20041090008500c880000362900369030858211035450801d054440d441e14413015a103d610007505030420f14420340381c250040ad2070301c0c0c19510907070000709080304041d400070b03420311000708408442060b01da001d00000d4010200b030008514280075050303004203c0c00240c000c80c207640054410001c0c42140000d80c866850344001070900e4068014004662000901c500429602c3c81c06810034400c1e02440b50340040104194141d145007441140119401400031403c03c641e1f540c0c5200840301e4071401619904000d640030084600c00340a080480300d026240201d13803200b50740c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 954887365 1250 954886115 954886133
    0x2d010608011a190e0703020408060601030b150a090e0106022419020904020c011b020f1c2109060b0a06030c1e023a1e08060a0b1206100309 61
    0x10290b100d140c14440b081c0d00ca48880019201130804484040d01034142036030090005e600922170168240a81000500c0b00c0d8004e10450940340c0020301540c00760480b15803031809907407020f5082000d000200d0400f040d05480b1540490103008543c006050302d40e11801c40304400400108200c0c440101401000000814219500c00c3c0c0c0c80d01500c0907890304c1950300010041c0c000d41103d070b2040d42c038042184c542415080e640e0031002c1c12035000d86001420100599803206440c1808482040d075076190090980e00c900c00d07d00c0801d0351030400b030000d000341040c05c50a80705840401d0b10102d8a8812400c01c6240800a0750028081420200407001e800721001d07002030f040740c0405203802c80c0620b105c0b460600034407511036103d08409011034060000001842040d00152045505ca0b9114604075212402141d4203c00008030030002c80744905410750458040b00c0042a098000e040070500080f24107490018103206c001c1c1800c041c0141c078041040c00342e48a0b501c0402400c044c102000f02000c100092 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 954888615 1250 954887365 954887411
    0xc030c06071502130b120414030f090609030102250b0109050f1302061e1b0c03061f120605090d081003060e070506030c0c06090c1c052d01060801 64
    0xb02580f644c907070700703041005028260b010540d0000005004d07000004081401840303244283c50702405030403400d074030aa0324000e010045078008010003050100c0d18001014211016005002510300941007520b04d481e02e02c2c0c00713002e019550384000c2c41c108004452a1590140c20081d5040000b0318101c044950301d0400a489445150002c095100035510707018221901804440c244850140f640e41071010b056000c1d5080300c1c40c031201d8018500b00c903000400c0c2030481c508014010040c9481f02d24448002d100c4000d004e003808402d1802c0000c0b22141c400b108040c00707010314000907640c07610495550a00b81c070b02c3d015004100c8141d00b000058600c440c08001034a422810020701080c3c1880c0c2146045c0c5130b90803080c0c0c4060301000304071040080c1401440c0c40e001140503210a03440710500f0995030940700360707190360140aa03000d100381140c82028000040740030300c04076007245c141c400102c0d50a00c619210f04580550100c4070074404882405110001c1010740c000b0000b900c0210003e580b40c0302c40e0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 954889865 1250 954888615 954888653
    0x51608030901091209030512040305060c0f0c0d171303080c1c02040f0302030714060d051e0c0a0306080a0233040806062107090c03020c0105090c030c0607 68
    0xc004202901c000358070040000c0d034004204441a40071510140101c2140d110032610381c460700b000d803904245614290340c11607034400018076185c1c44208904503640c006611401b048202403210b45c001081c00c210714600360816442e412402802c0c04079505960f800241601c207403c4e12202844000f981c84120650301c141150240c0d62a41413842506402e10701d40100302820600124020525503245c01030303032045904c218103c0e0441503890421a85140d20561480c2d4420303410b0180000c020b504d500401d510280b03520800100c0700c2c50301c51a2103d0a0241c07840d02c14582c01048040c1035642504c54003001d00480401440341c0c002c1c50380014103444180c003921528840c0a403807618010400c02d03807403d814082c00307c4651960b45885480b41c2d05e00c401c44005200701d0481201241ea24039101041c0e41361a03014000d00201400e0041110150a43c0314500302050740c200243e00101c00c0030f2040501581081c0301801c4295590000c240c5013840c42013125116080821203400042c48030340e845c035841313161 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 954891115 1250 954889865 954889867
    0x503210c011805061e07050d0b011704060603140c0f0409031403010e1014130506010e0d1a1b0d110739141912080a030c051608 56
    0x2280c04114003400e803002c5111400281035600d1420403902040c1648580b0500c0841904203004041d040002070341601c40101142041260384064161600901d61405041c14081e00f20740074011600c0c502c1340208e4086e07481681c1c0301401c2c02080482c008100d40c804c0b401e0024042e589150000500500604031454811980ca0718541c00301030284440c40b0804510b80400b541300d40e52101307808200171003100c51403c00a00c0030004680c2614294900d40c1c5e002c8090603110303c2c0303150260710100800010700018144054600d990344c0301d0b030390180c08558152003001003c5240005988002001802504003211a02c1e1028003400411410054440035403250302e0100343c8080e1001800303414400c5807000350107500c01c0301c600d80d0200344841c0f413061503400045031180140b0174681610080480c0d03014412410038600800b200c80c2c40c0a61560640344148800d111645941d21201d0301c03000d80158044401d0340010660900450b05445a04050700d010300b8058a052040303003c1249400f8100c100602c8260 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 954892365 1250 954891115 954891127
    0x1140a1e0306060923030703030c050c030706050a0f030b030105070504030201030f0c081306060803030f04030e09040c060e0105040914090601141c0609140105150402120105010503070203070f030e0a050321 90
    0x9504c000ea941c010a01406641103c8c1e101d003401031881c1c02da08020f84043c41152004150ba040026050b4211000f0f03580f030b1400c00310003000885803001c5a4a018040645400d0100700f15542031254a00440080d11400d5443d49035100250654140711980c5610ba0701c0c00f902202441d80105070144c0c40a48104501c050b6201807a09800420b0990810601d9100100410860440b22540b49014a02940316001c44038108020040441c0d0200e034002d0209a06040800c01789011340c010310044a41410054285900c6480780c6d8115142072403403000c0e030002300c030a0010044091240c20301401100c000101d035000da1601140f02c000400303420b0070340c01d03c0080d681401d00c10942d0241d4840c076800740c1206004008010b1072406000c09940242045001e26595496441c0c28800c950581310001c3c242e04881c3e03c0c1a0040d80c041e000204540c0a40c041001a100081c0c1443c1d211072400340311f40c94020508244009020114410341c00842c0245c4c804a4214101c4488007000094060403250701c2e030740e0740 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 954893615 1250 954892365 954892409
    0x9060516030f02031e07021507203f030a050403170403080c0c0108011d040209270609011107031704020f03010603050c040e01050f1501140a1e03060609 67
    0x3124044581030611070000c170354018880310a0041c0401402292a4505555020500c2100c0e108017440200440103052003206410105c1c5215074404800620520076403008407400400d0103081000c1104032000000210b07a5908104280344110b10710310025070030031454003000740032445a4000582130301381802801d08009695012a000755a000c0c1056458074884c01c0301c0f696956404403080e010038203081c00490314904030070b4080071041d50080c02c01d03800d40b1190240300c00844060700500c4400c001c0300c500c1d030080c510f103e030058906a801e0002c2c0028581a2145800c4031150ba88502074410200098408294442242681001c044650303042c240c5561000403451315030b50152039015403d0503000014410301041d012030320b0300305680500031200c182e03500750700304c8038110394501c41c00000c10007180c0c601540c40000c05101e901030411079040004031003401200d801c8580030b03500040f245410544170102c83c2040d0300c550050b904080c410541440d00c003900e00070441c082d050100c1c440300c1d0860440 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 954894865 1250 954893615 954893617
    0x15140103082b0f050c0307050d1104050d0506010f05090613020c010603060f060306060b0403020d1214070b011403150612010b04090c051906090e040524060109060516030f0203 77
    0x600d0b8550031180d18182001c4000018140e0a0500048580350000080d0780388804030860340300c1e00d95a540c9515054015032020700034120342682000360942804040b0782615645100ba44c0c07180500b004004a41c9401044655030495422a5008000c1e44c018090141c48036030312503841405444002d82c980c2c1c418050540182483d0380042e203071900340813441c9401c42095104030b0507070313020398818801140c480311022594031451000039007015030034405d10046924483d80c6084d41d03803d864042101301e90350304880030301e4101d08020780b001140d00c0010840300c4e04120702240c4078002a0081d0447c900c01511b44005110000c04c1c07031340142c4449400904002e4290f00010f070341c04004004021121560606c07041300d107158042d05004150340100c16080c1010856003504540341540ca1002d124200160340c444108007510454940c40340d40c003042c8550342c03072044006c5502c0d41c0110002c0720b0300d0701e040010a082c00c41d40c0440103114041143c0003c4420050318114040d400d402d02200f50003100e1000c80c91 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 954896115 1250 954894865 954894907
    0xc2c090109020a0e09040206070602130b0c03030a060e09060a15090515040501060c080a05161e02090717010510020f100e150106020a0335041514010308 67
    0x10204501001084000d296406404410f034190f94144507055880d00380104800c040e10060740c000b0b8140040340002d0a1900104501303030001e000c100640c2e5550031681e8450b00402d46030b000581010040004031503d503c1104007c200700b14051036103060000d03010b80c0324030001d065984402d07207482d01101b507a04882d140c00c000b410030b03e40410a07840c04112402141d80040b910a100b242403900020301c0034030034000d0400080d080041d061511600f0f900540341030307205030122848000c6000c0d03501c0c0481c0101071620303601d81040c00c00d0b001209861040269400c401842036041c000454201e80f13068000d0000e69064440039903855885e5000c0c80300c10382c1b41c100c0003440510a88100c0c41c80441080c0d280d00034100710401c11003195401314a902c04010420f02c01d004000059000c6900b60000c01d00c2011031298100c8800d690000c80c215024103628440714035180e1283c4203426005101c2080122130f640303402040c01c0b0104004001c141987c04050900610000d440e02501140f0340840025200c21088 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 954897365 1250 954896115 954896119
    0x6090f041e02120105091b28020a030201050c0c03072a0f0303110a080a1206090f2301141002070504090309030218060907180513140a0c2c 61
    0x110912012034060f50114000c000c00900d0a800060366040454295005000409803400040302d20903074516550008039005040720707041140e4070342c590054420002d00c119698050300ca10303074850402030b007580c03005030124508070010004d030a0100004426a111103a0000d0700300075104210901c0d018040010450221a0116440010b200103800890a044a100b51107415200314030f114090b8803a04403005c041c0140382c0c00c10290806620950000340ca0780f2440e00002a00e40d11040310348119014001ca111203140d44920401d250201e1241d585c607107500301c1d101903540e581054051000304054950943c090240c003d05140d4090003401560054400900200034083c000c0c1001013040000f484241d0003064680348154100c00052015071188a020f000444152102001120314400c0d0741140c0114081031800410745031786c1c440141c11044600d0b07501013002d003070090203c0c942800242500d45418074041140c1c54140c0c1221b40ea119a90101c071400b102d00e42d400382c03c46405026100055 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 954898615 1250 954897365 954897401
    0x21b0d02120109120809030909130b09010b01090f0528080a120e030f0705102f012a03091505240d03170c0f0c011a0a0506090f04 57
    0x200c4103050541c82840349a0280408a51604207920240c600d81d00546d0300d400a82c01c100042000b13420172003055038000e0401d613080610980c0e1500da56440381416254400980d448040c4401a5a40030b11840f018000d40826000403030b00d40070004100d64007080243c2ca5541c0b0718041722200d041d4070488900140145e60a80304500c80c1490200c00c1034003115044000700300021403a0005041c0024507080001904004040c0d240c03c00c02007180300301d050208441046002c448511031003406140360407006000d40f40c02c00d03003962401c40c0035003940c4059003007200c1101090024441c14034212040d80110750181000102c3c402a401c1c41841c0e61003907541408814101802c2c010a10300303441c4401d44010700700e8158440d8415440820002c0c0020800c007800083e603071003280c2041c07880c590241d501304a110560031328041c40e01c04101c0c1640c001080c542c046075504d40100c0d0424660040006502000301c49180c00c103420407002506500480000c14011201c8040c00c032059101c1364001d41080c80444000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 954899865 1250 954898615 954898639
    0x10e03251a1903020c030a12110c0a020a06020a051203040206040f0608100806010f18020d090803100b1c0f0b04050a060515181003090b07090306050601080601021b0d02 74
    0x20748550b4414454214181801204005154401d00c02d03111a22601000f0b1858901c08103001c4400d00d00041280081c569284940c1e111514604009c000c10000c0307901622415403503004010340c00545600210540d0042c5011200240303001c0b0716191010000a20785031282c4071400442c80c3c1d4019a0800d40c0764003001440401c126810803c40e611403404c03a0b1138403c1858590264984a940a10402c0c81c0c0d0716030454280900301c9500d0400200b51a004030040c00e000c40840703623505440c003500068a02120001c10302c0000c81c14a000c0101401e400101e0500d4100300c641ca0180144071241c092600580e1105e1150090140b90400c103644100108284030314240405100010012807041d540320f00084200c0c84011170030402610003d82e401c4507106d170801052014440a100b140c40480101a41c0358851000038506282d41400f650a03aa900d07018142103183c140100d54002d88114180100c0f01c0c00c000b40c2c0e0fa800280d4491f0841021800c0680c040040085007002c000810001d50200940c450 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 954901115 1250 954899865 954899909
    0x11d032d190e1e06040b07020409080d051602010c0806060901120507020606100c08030103030509030304090606080601080703150302150f1602010f3b03060403080f0105010e0325 78
    0x541d42d0400084a103140109203603c2e80b0404403a020941640105061004110f0307420b00170040c3c80c12078000303071010840501c107070f0710503000b944500100b00000340c3c1d620904c810040c2854250585400b03600080222810f200710250454034020281c42c40307104005070010b071592003140700c008142c03441203061005041c40380300a521130208683c007078000e003a28981d41000c54801ca0300d00b000d030341e0048000c40c0b40da421070310111082d61060940e40e4240c4000c10000881c1c0b50180302d110000c2036261384900c5036040410005083c01006404d00d02058101441042d101940561200485c0e50444510003a5a500742c2021824020040d100d80115000b1a01d0b403422000120101c0f0071074400d0341e603075218405081342a140c900e03140c007030f60b040d0070350145085602030b41d00e44140840e0511120308201c00111480024070f403103c1160200c0004960300705000309600004103107409400d09082c211810804a800b01c0d43d5004a0b903041f900220b9459800c5a0314050844480090b0490541d4202c0381265144 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 954902365 1250 954901115 954901127
    0xe0603010b0d2d09051009030503160c0b090a030801050f1309030e0d211e030b0a0b0301090f06090c0c0807110907200c060f071a09011d032d19 63
    0x700a40c0c43d40241103a410b000021b030b00ca4642c0c1c880d85038403280d045448a4240301410030000e44102d00307100f40b241160b00880d104202c9184184c0f503503402849020100d2500408025040e805075000e0700e8948210000d075518a91030782400e0340d0310240058444030608048580300c0441060719000111319006409100080744201c003040e010b044c02200c2640400412240e80449820074501ca50508100c0c08a0502c0313900300c5489844014088807140341c803221105071652007a448407605a5465080701e52114803400390200904800300704120101052038003502c1c4071700740308004080e00030004203201040500c0410410700e08000e000c0d4020b030314140e1409090114155540c0d020701c0404418018690000208001e00c0d8a000d01160300b0159000004481c81d00700100895211215414050742c00d0444a8010300ca003101c032001283e119072052180380d2008141c018140d0b01d4008115110702c0203402c03220700101118008034907010074441009400c00d80642d51020441c880107007414407003d0b030300c40 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 954903615 1250 954902365 954902381
    0x4030507061b175502061b0409020d022107200a060603032714040515030105160e010504030218090a0b1006080106020c10030b030304240e0603010b0d2d 67
    0x86014138840e24407071550b142e9002c59000c90401a40441d0003d403255284040708481c1d00a802c032620f041917210696801070782c10104980ca10030b540404e450b298000190140803404442d41c0042195092185009250040040300c03580c061000f400c80105c2f4880800000d02c01c0364010404005007a2280380040241900403654481319468504040d42c8081c0f00b66640211003502008607006000c14040c0800f41100505484c080c080c40120340c0b0240e20b0038001e45224600c854009004541c84400c054410314441b2416810800b00b400300b0b10042e111120404004400ca0740000311903038584a480d0300d0b000340c4690041040020b0310074080042801c41d4038000780c0714640c44180c0240c3c1ca41000701da40d040c9012410350301807109010041c00602a501001e14900d01a09883c41d050b01c034280d0008012111848890104010304594040750748106540c501490440d485803a65261801c183c038136004166108520036512030b240310380c40c140c001590b0086540d44150740750407d252000a00100810 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 954904865 1250 954903615 954903727
    0x402030906150a06091406090306070c031e080408180310020304050c040908030f0919080d0e0307021311090405010306020703110f0a0308090a050304030507061b17 72
    0x5404840f80380950f00c1c1d40542c0d40540d13925010314901200282d00307414030420650009020441d4080b651018030810b8841c00c0d0b0b5849182c0c4802991800501c0721074030000d195000c200c1600c04410103940003400d0340e042030700002038984030103c0ca20b0f10104000c0c07068080b07500d803003002c0480030840c44c9034000c0c6104d60300440a035505104004148010303901d45400c010402902000003800c10440340900a400074041d100311000e074010b50502c848ac03010102c80a0300d0812001c5009408080203004985140f2103500240d42084950707404503c55098489000701c525403036000e201480700010060701d2200500038024012960346c3c0c10310038000d5100d5002900010900800b03203260210004d95040c900b03c072100141204009900c2c02c40352101d0282000c0d2990052032206004a001007000d003018500800c00380050a184c020050708850b810b00b16100b50040010f82d01c400708480c100c03110305d98205410321a96440300c2c090320520a00c24030b21920b01c0b0242100500c440707040f000b16070403140141 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 954906115 1250 954904865 954904891
    0x2a160e041209120206070c0801020a030212130f0b07030b0d140f070b180102030c010903050408060114060d2c0106050a06110303060f060c03030a090201080a090507170c0402030906 79
    0x41180102d440342a640a41e5503529901d0b4000c60043c1051802405824091442c01081c141c645503402d003603034891001c500000c1d4002c03418140a4005440040d0001c4089908185582c9150b8a09070000310b40907018007040302150006003000c2c020340002607900c00c01003601c00c0807001ca00c3c0034248606194400c214610a00c0d40e96030200c500000e44009503803a504080e4141005d039914100245149022a4114081480310400d0715000740101c03a81a80300b515403a8039141044006441c240050388100442c05401180034481d4941000700d41c0c0c100c000c02c0000c9015207a0200201c4183c1d03404000258107840d4030018402c103238041d444407080e02c00464500070b85a559400031644000310314501c5205030070030004200741f0b10780b030003030480c1030314018003a0b40c14901078590f142c0c1140c0040b1101c0d9a41500d5002c220119179120b00d15607800400b80c2ca080242c03a640f40c0b501c03907840480740500d420080c40c41d01c00100f500c004001c0d040340b86e40e008005542d00d2a01500c596220b280a541341d01c10310340 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 954907365 1250 954906115 954906143
    0x304030308180a020f01050c0a11041103040f12110f010f050723071a090604050d1b1205160507090f020a020303130312110903060601052a160e04 64
    0x9142c02101c28411002801407034503000395004c001c2c884030040c81d480d040c082c0400c210885c0440c14010072012601448000c1e8600070100c1c103120580c0d400031030502541c03104008000002d00b015000c0e0040c15000100455550000d9406450b80da07101401d503001842400394020341031038150480203420840b5030701400b41e5190300d0300588440824500c900c5101c81d1010340503043c201020f000e031480398042c980d084184081d203040b4998410007600c1c04c4500d80c20800400c000e00c8001c004040031408203191058040c0d08505440394502e04107040200603001100b8004021445401600c0c0f110019082c0c0c803000384a5031a01c281d98409034842e07005568280201d10441c0da241d44282d400c14801d94001c2d62850740c6050150503505441a000c405100c4041000d40e0280714910551a000d8120009079a0340c40c00d18040620300f01004000c181000000c111000c5c0c1c0c002c80d85864085110420030322804039030f10504445c244103051002e8079441113082e07400144a03c00e1030704923019500131007142036404 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 954908615 1250 954907365 954907381
    0x510061403010e010b060f0c03130f0e070207030b0606091513030c120807171c0506091f060309050c13060512010615050705100e0c1c022b0c080304030308 68
    0x80c1c0985c1102c0d44280288500c4480358a070f03030000c100d54140c1906a0b4600200480c01301150342076034002c04000e604e009014015400c411200c180c0101141c002420243c0c61599101d42c0b009006048600426001c02d82001343e0300c5208900c210090701560071038840d0030740345d100303251454588415500c1c01c140e00300c0012500c6850f00303107003401030700400b01610340714254948400f8494510804c4c01c101e0760030044051001c415400008a0b5403040e440031031242810020095200405852155800c0c044180c4d5003400ca01c0c0c40b00c00c01181c026050210700340b032403030030901d0401d60036117489500035042caa21482c0d003213210350001055603004c4404400742140c05000c2d0f400c86900f03000e010305980203e40c807060442d000c0c8002d000d14a11910481d0011100460880165030103280e20141e250700c1a100300505142000520301c00005a01030201c0320350198001803030300700610703110b14007107a652289503030961000b140c0a400d168006811840c0195903c0416a880d841444141d001034403000c0032039062 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 954909865 1250 954908615 954908621
    0x7051e0c0d120302030702070b2a2a010c08030109050106020106151d0a090e060f0a09050a0b07050405031207030f050405090f06010315180e01020c03040e040510061403010e01 77
    0x582e0804400156039541d120194000e500c040d0007001948035000300003914001d200b00030100d14000c1c00c0380201c004204252003800c1c2c13a207010702d450160007000150f81605026441d10241d0340402c0c1c0141d50815240c00141c48442400802500003607000001203404d820b141c12003030403a6900c1e4020001155114461340c1c0c1c02200c685d00d117000441c210f43d00c0c04040c03101104610720440051808601c0c5d075640c1c0d20142102c4d0711041a84441d080001008031314803284407059070000c52000c0511030402180d072080d80b92008540018040b01d10100840c0075580710303000b41c40c007908014040700d403299110601040300303412050089000612082034442014401d00a807412920058840e6919407152210380450703003402808941019501c0c540508002c1901084000401658801030601e0007419213020a4030390503810742c0101d1b07004202800c0c51400000885080310600711420740152518a40282410600708880700031500b802000b24900b94452985255500210300802401d41c10702229402d07 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 954911115 1250 954909865 954909889
    0x40204240207060507060e19060902030c12101d03040e1f150804052a010908010203010b0f03040519080a0818120d060909110a08012f07051e0c 63
    0x64050100d05c000542d19000700000341490f4042e9086c11454080310303d40090080e5080e10984d4481c00c13641d003582005e221950350741c0404e682c942d0404009901c80c0e65121a01c03c0b104003107554030350b01da1080095100701e42406400080960390346030340e00e60030138680a00a0300e1035503a5040d98108040001941c1090740115500e0070220021002d9052003a500004000c109840b107014540115001041804502110490307c04403602d0740c07200000010202101c640184107285e20400060141602050503901c00e5400a52071658a95451400741e0504405d16421521805245014410000c0e5080980040b0602c1d0303480b0171407591800340c10340d0940f00070500c115460704100c0803001649104d000402d00b1044070100403629541e1022103000701d59403044181c80222080882e10f00c6072400824200080ca00034000b440703031021416141c40b00f065607101c0d003102100d20008403c0d1000402042d9200c07544c20400342c80c1442841501074800b0409180d16807403a00400300c243d031040c5004800581 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 954912365 1250 954911115 954911117
    0x130f060c0f080f0706060b13080f0705091f0306052512020307030b03060c04061b11091003121206080a1a1012030302090907030608030913020904020424020706 70
    0x559040e440c1c40d12007060340700301600c900c0e1403c03c200800106045014040040070345c25441c660300c5074140e1441051030000c0c0c1040b02181c01070030b2001c1c0100400508141503c204a40341c211f41d40380c046502d08030040000e008048912103100c0002800390ba64070a92040d541070103045a441418802450090315070303901c00300800d01c3c10001e404064410380c06180c0c03002d00d5090010340301400400103464400111810500300d580042c2c1030100302c0d8060014028800ea424035001000d4007a554103860301e8180103458042d09110000030007110403076031320000468201d04c1110780071090340d00040904120b0302c0c060f03407040c3c1050b400040e400c20014140713030095089003011088a45003102014514400782221903030006802000c0384190901c001000310611075207005a50f504281d0030f004030040004c04100070315142010030000450040101c8040c1c0c5801c44400a4007101c03056004002d009581c1c038036800510101e0003288040c92919420600820810300084400071420200d0391031103d030140c00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 954913615 1250 954912365 954912383
    0x150a020c1002062403070f080106090504150207110603040605070e12121c150603050f010e1303020a0506100501030f0b030c01050c101e05070e01080c070f08130f060c 73
    0x242c070f4200c0c0020401180c0000c0602d12000b44001340020b403502c1c85c2030300900c0304400361820400000e402480f800d0003d14180340c091045140a44802400904140171002c016800113005810014009105030040e41c0040c88561030f07007458241140140411030b62003001c00c400c1842ba100516207608210b144807803010007080c101c20b403010540e105401c20016010802c5d001d03018458110680e000b030f068648001d2030740d060300c20302d030803001002d44402034a40d01a6040b2000140249036050aa581d480011400303d003c0c846c0349868201d00d2708161140240160140d40c0c140704e1b40c4841520a4803c4030000d0b6800d0120303000070000312040362010208150700d03600c4100203503850b50080000e0f225268451040da2015404c44c4840c20545800003902e00680104407400c0c440c0c125244034041d0048030f5451301c0c5491580c410000b03400041d0107480050f0409001c107240003006480300c0e00c501190380c0540444d45520814044210070b450320302031107685541401001c00c1c12481407145031407042d0015001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 954914865 1250 954913615 954913621
    0x21003050609010927121b0302060606090607151a0f0d021c060e0a1a0405060601081909080c190507230402180405161418150a020c100206 61
    0x41402002d0001800314141c084c06010011a400303400303045586409003051000319a251b00f4010b011200f504c0030311031800d030500e1844002c00d50005141d50700c220190340841d039403101007000600c0b81c010204000d004048521048242407000d0700114100180080600401600722f01040129030030105156003058145980001602d001403a540343c40301115a04130b030f090b1094845c403080c1d80316155000055849030743d0a01c20004048004031802c00180080d10307107400d0a50f550780d100c00c8050b20150411000c14081100341c540e40f583c0360b4280307008210411107035502c2d1806a074190410b5403040da03039004208036062903140051000e11120383c000e005d00382c03141c14801c4206402050020441c45104040715210321a15070784028400d808070b1400f0245806200c42c02c05c01070b280001d22840f81982040c200900854101c10040d0560003104074164590aa03404900d05150b60140c05030360041840341c11810034101d410041c490100c3d26400c5e0381540c582d56051240400d001d600840050b4891400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 954916115 1250 954914865 954914879
    0x14220903140c1506010507050303010609050f220c18030b01090e010905031c230906010821071b0f0f050306010e07080603120406031512080f0c030d05040f02100305060901 75
    0x303d0b078800c070141400b41c100803450b01e6052441e0001d80081740412040301061000e4a841000f8801d00701e800c65204030408181c06170352403078114030a600d8801d10f0b2201485194503000340200007984c4501d080b10141e650340c80c1850f1004a000b880342c601c1c698507002c07806002c2003040c010f000c2e096400c1001585401c404144142c0412580801c10308042c1d03940d000452409105040c0c00056200b1805400160406500c05030802e901039000d8044c99006c40302400f020310f5001040301003402c11074031440e20f4070442e081c007002c3c2c0c1e079203800c8803400800c010402007111010a2481d5054800d0503180090480c0ca40c0b05159440a013030041401007041c81000442103407003480c0a69000c03c02605940c09200b0b83c0000807903a1704240c01040100740c454803c01c2403400b1020b0401e0050802010503040d030b20b0b83d83c807500c000780b043d240e800e2065400007822440704002001241c0440080c408100818a000e052a000484401c0d00c1240b06460340c1010300b90303840c0319026a131f004030030080240c6882c1c0d2034001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 954917365 1250 954916115 954916153
    0x213031b0503010906020d0b04270303020d0204080303071d030303040f051905011a010e0a0b07140708010213060c020f1c14010903110a0c14220903140c 67
    0x3141281480a0500440d003a1000c0c0110b40c05203114800240e201d072008404107043e00c0ea20090715000f103140080c01c0b40305600921307141c0905402008410040c0409040843c040d01c14040b060303120078000100004c000da40080150300c5010f00d03581c2c41c0c003880084518030340304030081920076a140e4001c0c800f0a001c40c0000414000e8140300b40c04817200c00c03800001c034020052034204151070995442042c1b40202d091030742c0c50b00350400c091a10042418000300058149240ea014011511001140110030001102400950f10450034102e882c2e031580d805919020358402e0600c5210315504510000740c00e4040c165407000143d0090400004160800900021070100b11602924842e41080f00010488428001000542c07010022502d21079038100601409038924010060f5406011980041180d00445d44140c5e20304c00030fa189900d0140001500c20131035804420400170181800d84812550340c2d1000d0b41c0f65101e03803550003051010500320304450042034445c0c1041d8001c0b05440f50011003850b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 954918615 1250 954917365 954917393
    0x60108211801120903020105060f030111040b0d0b1e100f050a030e100c1707020a05100207030c080a05030f0a20030c040b071a01080a0f0b0907170c13021303 69
    0x2141c0140c0d08046203d940702a1000c031201540940d541e002440030a00f86140c0308491500158000c1c009840d00c03250303121092040b403140d110305280202d200b0790344c400c140d04108256040103084800031400d5072003408452034000c020b607109100f10201b1500f014058402681d080005480b614180300c441681030340030f00705005548a0a019619000108d45031a2213103d070043c1266884940b03450300c250107403181400180c2000700350341c08481c400001400000d0602c204045603c0056120b60140c0f405490420711030030010071082010411b01e49480c2d1100c01f95104181c10f400d81d02c4a5140c1c0c0340c200e0110f0307116252210304403018a5841c03a00401d000c1c011034101c506102c11901e81503540301d8002e01078100900459800160719007414801032000e1125025018080c050305100289a4402d807405034550f0f00286401c0039003002070705001f02031048100400740591250501c05045030302544540442945a1051801d5a69038090000920983c2e508001c8600710035030082c2581c5844000c80204 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 954919865 1250 954918615 954918617
    0x40828171006081b0d0606020c0a080d110304051e03010c0e1c030e0901030c05011421180d02070807060503060a210609061a041503150f0e060108211801 67
    0x40b080302e5543c4d1030b00186210724400100007105c90410344024145456049010b100e00c40b41e08003030080d802d0201d1044801e07211414590304580f40c0200c910b0550250354450f40c1e012021084a070011444500c14500003131044000700700354000380300241d8031240050801500452400c24107142a90801060002d0601a041c002d4650801000084419100740c000300ca214a80343c8082040756000f12004141d5291055500c1c01c0940403105103030200310f02400c800d4081d4402d40800d081c006900c40107440c480000317060b1200c4490408001e55101b580d07100720045840343c1c0c0c1d000250305200c1e0040c0c90044100800e0340105a00d09a0786c0345440d04101c3c48189030004144031500011107034461919003d100f008080341901190500301082c218620f002400342e401c20110496170703c144242c0c01c0a880d482070714814144000d10f5031100900c2240d624060f210f00d407142014219200003a100d040304d5000e4111500c00705040700d400715544140b01e0310b00c0300c10b03424086880c6580c14004400303c02581 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 954921115 1250 954919865 954919891
    0x909110a091a1e09090a0b07050c100209010e040f060311060c0c0907020115080f0c0109050d021224040209060d081e07151e0e0304060804082817100608 67
    0x29050001c0c000c0602a9004001c5906c2072503a4401c02c201d1300001540710707440c0e0411a0421528003040c80c0c07680050450110f181d47d00040c049081c5c4e019000400c15154060b004014030080d9010345801040c003400b09a80740007195041034018540b0b50304840a0428100140140500d9041840194a40074080c1c0007955201c05949a11400001002005045c0b07040108409100048200d0510900c124118100062004248402d440b00c41d1005806c5034140d42c01d5503100c607442916400c00380b4007010803030035503440f00300d80c1d40750180110502e02503402140d0104041d12290308010180c2039840c40100036030307000d02801a02025220750003440180c9481054a020003d80d1055180341c0c061110100740d0340da40806402c100900d811810b40700140c00d0080100c3e840b4504406e6481c042c42c0716803020070050300c1c002820007500b8410b5401c10a14a200c0d40d01003c416054071170141b00c22a19180010501550309d5040c0000c8100d05000d20704040880414600740502107419034002400300418440f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 954922365 1250 954921115 954921169
    0xa11070909050a060b090106081315110c16050d021504051003021b0d02070b0d0f0c05040518012102030307150b030c15090f0a0909110a091a 62
    0x8468054a0201c0d446000540302082c0640380c80e408403044202c046000d034503010014000c0340d400c0480740e03822121460040188407814681550100d10141c0682c0d1807500f84074200c070084024001400541c00800d05999250500001c404410034071845080d40c8604184000c901604106028407141a1060b004510b019201c03808991103803400c100c418002540054503041b00300d0900341038801c0c1d08280000d040f406c1c05100b0025500c24141c060240d10100000d0230240c801e055511150084291238000e200341e17103a4220203081500107104690150b140c2c08803818840d5400c11130b45040e40c441c1020041d104180c114060030380d170640401260181b00400c0281c1c042044401030340e00b160006000803540209400605081100c95808140184c0300305400001002d10103054420742441030b5600000711200a0008109240c25400494254034000c003120038016000740801741000251a03521080f541c50b1441011030f040c14600005603107030319416036694944441043d804d40c0d402d8104056200c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 954923615 1250 954922365 954922379
    0xd120c080f0706050a1b030509012712080106090303050f071a060a0501020c061b0703080a08060103420f060504030b0903040806070f0302070803010902030703110f0a1107 75
    0x41d120311000d031400140403401d101005402c0c040d1591080d010031040c800c81080d0021a25014600161401450703113a00000c5d418680942c440814441741004000300510301070b80542c50b290740d1900542e42d409104450b8201940602c1b0103504032017581d69018007036403860724101ea060f0840b4a007240c5105c4104405804504401807080c52010505404185400c1c400104000b50480e584118159046007404480a5880e041907814640c040d0340c2403c0d0350024408030504089150304010000303500411100120b541c4900414450318007070320108110901c9440700703545142004103081c00c000c0a004042c0e105a0301005000d04c0e082d408294000d616250f14114400c00ca8681000c000184007080400502c144044013540003902c6501030351906080c18034217500c8100090808042c400d081c40a43c4809110358111906507410204032901ca5031680400710283d40281d44881c0021b05100c5054010800070301140c0c005041030510600c2c1200f2008140caa62403d00c100310b8080c000c44000041078 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 954924865 1250 954923615 954923617
    0x7030807020339010c05121005100c050f03130b1806160317010e06061c0219230315060706062606090307020103020f131502100b0d120c08 61
    0x40101ca588021612100c0721444003e01c0110020368540e0408542643c00d079007200403200000c040003002c501d03a58807000080703c06605076001d1508103811045060710b269010078200f107103504c10025125141140c06150380e0300c2c00382c0c121502c07018104203410051010040300600380c4000100609250306806030000d8801d4104841c0028030480e0480584200341d44403000007003401426401c48519410324000c44113401c030040c11503016803070005010f100f000d0701025030f0044600c043d80a40d0b132403103c07003031020104440141c101c0205d0f60000c40300700700000001c250903d40c0b4003090601c6c02c5070344440d0403000c00b903031000d01c05130880c108200540100368107000c3c240c0900350080e90329000c40e0b400310000c00d515402c48600ad030700c1e4000c5004c0c06030100000c401c441140d034091902580302c002c405000344d1a03218802415802152550000403000340c10245145050b64030340035617190710380d601d004400360390780d4140c05580078081c40e05050001e001701d000c1c0c0448048034a80f19100c501c107a521210780d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 954926115 1250 954924865 954924907
    0xb13020d0b0106090611031c02250c0608160f08130c033c061509020307030f0f060602070330080603100c0c061116030e0307060311070308070203 64
    0x20764a103400b0304c20380b0b400c5015807100e81d11000085142c08414040000030741c1c45603000180b419000036060160300110301d540c0102c03480d08140001c0ae0203442c0b820010311907446c41a240031901020024480d071072451200c0b080743c1d5090f11f60038880d400c01c0d00700300d442d91701c003d0018007400018005c000108a03a04c07951f101852040d540d51003012080b03c0080b409032440e5484c0e0f1080d82d0154698000840b85010340f02d00e1310f5120b82c011402001140000100c544903400c1021828808410407121540c10740211040000c0380c0d10800103034541c2100c0b80151078050040701c6c00359000b0281040001c401752101848445c0700600c00d070200014043c0b040c100805000702a000800001c203020f0513180c240011549444041800c100e070140300c030409095003601c0700026040759510f0024000d0090340d40111058650004425103031501a854050000401c115446000b0302c6000b8000c989035001c0c0c441c240254540a4101e402d09103140d5081752440d030010056011400244008884400a1b011040d8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 954927365 1250 954926115 954926117
    0x3050a05071d0126090c0904120f051b060f150f01080a0f05100e0609070f050a2a060506120c1e040908030117060106090b070203010e06040605010f0608040b13020d0b0106 75
    0x82a800e10f905c88600d41201c1200f014426410310082c000058003001c90b046c0c1d200210305041079095800070f000c0c2c45030b00a050035002c0c154901081c04442c0d46c00402c4082c41981d140c04e0300140c688410700907004a2400c607007207541281c01c45c240c0415540c0110b900983c441e107500004161164403181c00c5047e2001620381030f9040080348403d0000194000c0c11585c002c1c015a111512441c00c402c3c002c2c0345006103030030082804400200d4159042c851482c07500200010031031960103040301075440350038140a14054441500d0030003c600e092503d10b0220301c801304144000c014401070790b010000c0000034088004c0c0310341200e041481090311580038588605016400c901d440c0d40c9072000030f00380808000034214041d0410001404031a400031a41400d0b0f41009203d151200e440d48080b0307005141c0300c250602c040c0310381c904020401820b5000141640c842c0400c2e41100781d5142c005543d0310350181c80040c0300040c2180003401c40580c4900d01c82e4140d0006010a05140d07282d10350002c40c05003038000c00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 954928615 1250 954927365 954927437
    0x6031512110307090c0f0c02030c12061b0903060f06120d2c0a031101200601030c08070e071d1008040203160b070807030201270303050a05071d01 64
    0x510b418482c00c802400504024040d6410a0800404404d001e0403a20244050001d040065403010882c0d0b00940030f02070181c00c1000340c2070f6003065845608441400180c0c10110124038241800d1040d42d40c40701015000340080e40300d40e1001c009210000b0100e980101c091100b0711101e02c410003002d0f85e03814482e00c4210410344d11041558cc1c20561100c1c0b404803004864195105880752100c800440e90003120303110000d03080340012101c246d221014200c5204820310080007420010a1b1a412603104150a2040b10303030b140545030321090580b10344052508443c002840080c060004404510f851003074a10b880400800015100da099100701400030300b10604000840c1000c001c4c01203103400034050308040030f00d8a00d00c40103070320500c00c00034680d41001c9081c104044c002d4100103207540c0401e080d10943c10281c409c4090402d080741040d000039040001244603001d0a01c60503020381c48aa40c1d1040000c0418031050002070b00340719440c1000b031011320003540c4841c8030380f0000b05020809811 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 954929865 1250 954928615 954928643
    0x9021b0d230301081c030e0106030b06090a1401171c0e12340918051506060f07020f060d0209210a14070807170607020f0706031512 58
    0x100c0c2032100c5a400c0000741600400041c000000c0006030040f0082c4410321242d61030940c014110040e00280c03102030b840c1e43c200b080200411001030b008500c519001d6444181c0c0b41d0b6240c04e000140c81003654810728500b4400014002034031001000ea400507203e10440b40b00c2c03514612050781c0448842001d00006040030400c080c00e203443c482404258800800421101e080b20301c9814041c43d8820404120b0742e000014600c0c0889032a40110003841c4a5804011800705a00c020504068002003119240141c1c021800a07038a64501940160006456281000c040c1030b08042c0030380c02040c003680d0252254a40c8082a507800d0004c00106948800c05038072494640140290300d580b641001006141800380700e4031414001a03203c03911030300905186c5150310410300780c0c0c3c10080316401c441007034003640c000403a4075807a0490701c103841d11f81803049648696031658120385804812400504982181300700708035491081c7c100248203080140c0150071541e49015281d40c2410041c4d084410b2212a984 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 954931115 1250 954929865 954929897
    0x702030a150e070302012a0210020d0f09061b051c030c031a0609150c0d020c0f03060601090b130e041101080610080c030c04091802030601080c060409021b0d 69
    0x1490000481001c003c01a941c1183d002800b16488810188452805840085034000e10b0041042c0059006888604445031001c4001c0d12200405181e070040f54100210792030f07180c4920004012925550f131084041c031540100c1c1940441610401e40e110f104014040c01000303051a094002c1e41015100007407030324862079014050720802d520303090016010b80035004c02d81d00c0709012075202040444081ca10381c03801842841c1e95004111080002d842a00150447c4580000d03500e00d456204544005208202404150380c07440115038250000f00c140034108490070492001c0c0810201750081aa400343e04d070325043d00403401c1124280c071181000c110070242960001075041c0c00c5002640c0c205540d11114402500a1301c01170040980e010001001031500c40c0024181c80c081c124040c03091111b0000e802d90202480b0b040c181c140d01c24000c00340000f800280010348541c03942c2c030142c456410145415030117802500703d065110024410b110b40c0b8602d04006000f21290002d0684440e0380703614000030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 954932365 1250 954931115 954931121
    0x510060305100c050d0b0303120901090c09020715050403051b0c0907030e030735070b0703380603010605030403030b03060105150307030f0614040e01020304030e150702030a15 77
    0x5241c03503540c1c41d00e50303070100f0154040c007260b99920844502084103e1380101080c13440c4030342890001d01050f000240300c00c008040d08401c1c201c40c054038003c0006503d5007100b004a00c21480c00508600110318152151310310703504000d6029006e81041c60400b01d4824400e00c0c41d403500c412495150700001c00704800ca15059000c0398000c4418075081002500000b03030303640e0380d00c01c0000103003044100c1c08400f000c4410020442c00d00e0000c0c039040c00300d0450042e500740010307001420100d03081e5040100041045109114000465070038801c1c20100c5400c080c207941e108000c1e203506458404944003941c403c0d88821008500a140c15a0780c1703a900d00c0d06040060403145001c0580c0d210b5080140100000d94400d0128110301c1400b1b0305481d46c4e900c94103400e40003060780844d10074045041400000d498800000b020300c0d4514261001e01c16288400d2005080341700072540140450501044007000341420096003000c600015034107450100300d600064600302880b403040720390f04014035541c403038421640 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 954933615 1250 954932365 954932383
    0x2040603020907050c0f06160c2a030218160c0204020c1b18070c0204020f0c01060603150608010e0a02070f060e01020304020f06120708060d021305070f0507081c090510060305 77
    0x1b201802c0c07070b400c0c90240c400f4440f1242c140c80c0104214021030b01c040c0f0100035451a907040c001c111101460f00c4c00b20f0001c61024032448181c6c0f0850001e0b213620034110495450a104034840403404460810100c1c0588210f00d29203401e076040781c0c0c00c1c00112000c00080098002185145544600b032034110000c0149a07030004030442d0070f1040480600c0b42c060b07007200c407000078640e0403540503841340b01e00c1c2024001c1c0c1c015036495404542c20a0400580650198003000071988100440c140054441b170302918052000e124200c1c4000100340043c01511081e0b0240003040d100d0031291058280d00e495100641342c08c4141074000b6580081800300318540182c0070440441300359202030500301e41080e240c41809001340740206102d1b84c3e400044903555180d5407180170a5006200301c891552150700304d00202002c640c0d01000ca0b1598003480d001c0c0b03008406540c8115400500c007458840c15003409402000042c0350074052503182c2c18290300083c800c3c015002c5843c201c220001d1003c5c603504216140031081 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 954934865 1250 954933615 954933643
    0xc01060503060114330d0906140403091e030204021303051002040801060501080114091008150108101107030509130504081206010e030a0605060307050a060801081b010c0f02040603020907050c 84
    0x41c201c1c0030b1034100040034240c0c1e84000410b60f0386c443c0c1d90b8583d050302801311000001c110358502620480f103c2150040d19005034082e69404126076100c4482007100306030342d0f201203107044100c14200014501078004010310b481d58240e040b81c003541c980d00c0d940341900118074038403030720340105083c08843c07007d1007100002c22003441d2500b202c6d40361030150948001e10130030160145200000145051171205144401010118200e80b541c68610000c110a210207010304401c1d03000b062030328a038441e0140101019401c41c0740da200d00c0c24000f0380c0e05072815803220414030b4001d491501c0c10a04c0a65510070540f06601800c00c442d56005c000d021142c461100401050602c00026421404c946001401404450303100d40d000581b6110040003c0ca010007541c04641d010079150004101c5680c050782c064120b07090b11049070b040d110b0900e407042081d2200044140000c4900c1c403000085801c00c80380b1424540003406c0090407503281c3e00420382c0080c044800c103010810010701c0100d080170070000e00c14640b0714 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 954936115 1250 954934865 954934909
    0x30f0212040509060d0b16120b0f13060f030f1101032c0a0b07030b03062d070c06060305060601020c0a082113121401020315060c01060503060114 64
    0x8414010640c000d80c0210350064000300c0004c0c519031202c807944204950050b503041000d20b403043c01c0d800e000f058160b001d80064003c034800002ca058500030040d148100412214010720307020148012000fa107100c154580d1744445000400540d08101c010141d80185529000303104c45007040c503544620709004130304042c070f00b000c14102d40242d8460418040780042411480c0320102540a00c0e050580b08060480b410b074000380b01083e5050f51115280c20026002e1b50001e948175207a12251901a880040b0640803a080c1c45105504510b034071070740f0540310700f02900061070315200e0004442d1640c0003180d00d83c0c40742c014004035680400c25515800710032106616010309103400183c03190794403a002c600049085070032810080c0000145daa80e012000c01e0f003400140d0381c581e402c1090394404000d403071070394081000c030701d02c0d16040c001c40340329540c043c08a01c0710601c620207005903540400c0b59141195a00c0d0808106070b60203022580c001c1002c00c111510411600d800c0200030038401c0014081440c0c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 954937365 1250 954936115 954936133
    0x1d100b0903061902040b2701020d05121b070606090e0d020a02060f120a271a1f030803160512010e100f030317060103020a021f150f03030f02 62
    0xe00090410790101e8010f0000000081401d074182c040d000b41e410212840e000444c034900002e1000180a00440b07807040c0740002c9101c141e005981768600c8480300000210100a0024159910101c2035004520400c1851084010351500060341d00444030440b480b03034076040200904c90003030203500c80c15181d100207440141c0642c8000703561030131000da00a004800124004c800d0001481c1901c2c0c80741d04202481c513080c58603000c400b00914060300d04840c644202c0400044109862540442d5643d102c3e0407960319103d0041000808640141895105004070016024031001015000015841010036507102d04150000050600700b001200c0b08010003070100d00003004045010310704480e034004c04e404058036080744140000c0f00d90b030000072030044400400810990b0103480700b030111140040c46000c0f511958011002d0f4460b0f1306040005900000000c0e5514210381c0010182c20318481001860444401c0c04405132404c5520462103125130140800505411890b5110500b05910140c12541 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 954938615 1250 954937365 954937369
    0x60612120f1b080409180c0e01060507060203061311040f05091006121518050a09020609040e0307060903020c0307090204030b01090f090f060f23130c1d100b09 70
    0x4280103001c04440c0c095501032051100f0102100c1c040e01c0200c00610001480d00759020000c4207841e41201c4501c6816000644d122130518018180c80c003584e01c82c0c3c81c2400b25101e44019420281401ea0b011045400300600624140b00340d42034a400c81a10a032214900062a450507420360b021500070a240c4040000c140d4440d10340c20280d82140c20240b541c00084500c7c41c0040c0390f070380c00d81c490940d240d0502003508200201c40c2140f00026207401e1040d0340c2d8021a440030f441000200a42245040c451087c1524083c7c001404031580d44044030f06000094640e0000c0d5402c841341074000d0f0b00058048007240c01e082c8440c001030103407205d06518092039076440400c480014400c00c0c002079078844030301540d028250030540011341c1102d6442c0704401d0741d0500d41c004011480c3c0c16001940b44c0740308030444080825000303500c6100740071400d00680d9071001207000c001061000325540840481c0100761000c2075030b08403403069205285429540780008680501e54416080072000840500c9040720396 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 954939865 1250 954938615 954938627
    0x314040201110a080a0203180102010e0a0201080601030f14010608070215041709040e060a05130804050d021206010b04210f11040f0c120c0507020a0905040c03060612120f 75
    0x140e420b1030041410300442045608120054030300a221400000740103400c145e0000150000f41c0704a03624200c80240c400041e0300300c820701c00b6081515080300990a01540c011005194085418100410030084450312002240c103000014039246007030100501c14143c0c014440740c0d03c1002400102250980c50445040055004100a207002280a0025280340151066400202d03001d041030110b11102070100c1d031141011120200341c0c518110005842c5d00e41c4800000c950341e005180546458104814496101d040b4a016a007040c0c3c2034072900039814042110500034848115481d403101d06000001200e9407030b01d4408410540c406c00c600021504400b91446855401074205145070f0171000860013810000340d6000c0d880e07160500310501c407504243d080d410381190301401c00c0046400c0c641039916018105029401909000091281c401c590b884282c0040c018100724544a690359900804e451080c0c12040301014403004080c1000b1244180d9201000c550419111218541700c0042407 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 954941115 1250 954939865 954939871
    0x60307141305100206071d01091707030206040e04060c0e13020702040e060a0e06101412121801120b10030b13180c06020601080604020f1f09090c0314 66
    0x82a000007601112100c01800c10700041c1400b8101d041c03a40b0f1208000b03515200102d80403030100b035003901440181034441d1008204d5040c16180d20a071241000c164080801c010b060751041449590350100141c0d5900010b80001d1030150ba4040c940e1030306240020a0701d004079141e80c01d104901390202640d60f0740302100300c2031030006c02c2c3c016140c080900014018010720754240c0481c0c000d0200f4444840b0700c2d604000d04d90402141210400e8403003551071010648035104400e100a0000783c502d0381450501188010b40b04060115180d8101c00d4100708082c0d40002080f000b0030303908042c62070340c65800c00c0700040844a42a0100201c1b00640c003c00c880310081c10170f850405542e0403820034170381d4807814007268042c0925410001603001c0401e00480c002100429158000322250000b00a0301c005400b505964003071024144a40302e45c8e0034040c4088120032501d5001d040e071344c4000b0401e03442c010307805d09040c456640c030301070945032240c1c000898094100da4020035041041c034000f0020001601a0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 954942365 1250 954941115 954941147
    0x30213050f010e0d0c061b080a031d120301060e01020a020f13090f0c06031b0905010f09080d0f0f020307230307170d050a05160c05070503030c0a060605060307 70
    0x240103440c0040f125082900c010030750001200c280d81043c803440e659504140ca4003903c891852503940d4150444c49004030400034160b960800c020790030f0074842c2d000a41c4403002c109805582c0342503001d0982c2808040196400002c1e0048010040c1662124a5460441080c000f8041901b43e68010520744942c004285010b0501c040d140c000c0d50015500c94620182c010f140102d02e0b803403924124000492038882c10b40020304041c01052800141d010210600c0c003d80c442401c80c5151000649110941c49150000e10481c14000256103000780a11990b00e0300d9a540c20300d9110001c04050300200881d41ea0390215401400b4200000d0764208009141401805400c66004c9100c1e54007403861082e24001480410410342d000c525000076805010b4100e01c0c07540c284804da5450030104119201210030b02089410200120381180c05180e6801710703a03014506403030f041501e03040443d1131940702c0c6030680a241e01a03589827062046910988015050032105189181401d980050200c154400444 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 954943615 1250 954942365 954942379
    0x161208030f181618110a0e060f0307021609020a021510080124050306041703071806020c1518190e04030302030906090c100f03060e04050d090603021305 67
    0x81400d451450303425201c80300300b02218002414007150f06900b4483d445489102a014501c0710301207200d80c003844400b2500124503030b0521b00c8010044800420011442e0b40055003005503113010f946a9001714401c041a4000f0b00303a034261286103a6260039213500000c200c600c1403041c42580b0341c0c0444c407001d685114801201b05900c075181204040307021644520059843e281141c01c0070290b54010a0041008a5a4420841c0e644040c50384070402114000d003c80800010511032000c103002641e040b000ca0715003c1d00242c0c181d83d40c00d08407800c036040000964040d0000c1055841d11808040141141e1800b0303034185840180d0000040d0038003940d051240400c401c990818010441c40040204900d151103030b464102800c1c00f900942c07040c0d400d00e40c40c0c0180000111800b0000500e048050700c003520301c100080f002c0504941010101e02c0c110100743c0c59280c0040d0780d04408488600840c0982c0241401c4800b2210140400095500280601d4014400703449051440706481085840507180d40d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 954944865 1250 954943615 954943621
    0x6060a0e0109050306150a0b0c06010e13020909010e010c1d0105070f0b24010807020d0806040f06140324060409030e03101e020412120c080705161208030f 68
    0x5032400b0344103411494040c4994801c0242100700b0901c110a02c403000d6031005080c40e19a08901c2c1d0354414001c40c1c036040d90024004014400d88480c0703440c0c0c010310040016070005810750001d43c0e010340540300254541e445484160482d46c080c492891802c03180d0400102180e44981407143c0d1500c0031000310b05100c0003090040a01034270b03441d040d4007944e1100d0340a901d880c0002c102a050389064401c40c036003c1c40c04103455441d5010700e03d01030007207400f60011714142c00190011580000c008006980194564503c032201a806025480161401354403180d200f008400074140780144484142c0002840b1461080c10081d1110750715130800d60070390300403440d0000c5040030b85144c00d00000f1250144101d220704840340e807965004e0b0030002d0043c2c0f54180b40030303140100d1070306900842c00b60084040d82c20740040e00140410343c1034252032000303003000e102c2400141c0301c2d00d03190340017a0029241900301007000a440c00c14502440b000e0510f07455034600c41c980e20346442030140030007080042441e500c2404 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 954946115 1250 954944865 954944867
    0x21120610021204061d0108010b0909060f0d20040c1704061814070806010501050d022101290f0306040f0e0f030a0305090a02030a02100309150e0607020606060a0e01 72
    0x1501c03152094804100b03540f40e40e54600280a260003030100122204a4542400c3c1036100c1c52450307048410341e0846504010100040060680002d488507501100a2409594984902d0b801d04c0081f4040d40d091180d5032600c01002101c02c46164110740b14500e0079141ca500c0035008800d000c0b400c1250081c140d004e640720f04c1c00d100101590140e800c240e9a444054004200b050040c02c25a0070b50380041c0c1e0002d0f030755032001c15590307803082c080c40303011031814440b00d003885815901404000c1c000361f5003200917081544840d05100001c0c1c00c0301d400d0395004406001a40c140703112603e1f80400540f076103460f12106031401840d40c000500010711807500c81c60304008003030507500003861102501c070540b40c110550108250b0340794060034041021906060015030b200102103004172440d40c000c0c0180100613803950802c241d501c1d00407054010715664180c0c12001c6403803004036810900c0209000290000480d40c183d150560040c0386030215800001080044c2d02c0f04410764111100904000e4280030f50341d80 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 954947365 1250 954946115 954946123
    0x15041502040b1c0e0f0613020a1d091b010509010305060301020d0c020d110f0a06020c100e03121f0902160b131b0602030304030e0d050f2112061002 65
    0x2000412100000c103d03000900504403490040c8044280c003003158450300810561140c20004910255400c41000641c41400d400001c00800d0710051801c40c03a26207507110715810454210001c0c181000c0ca104200703161604011045040503080b0407505d045e51102c00003065031040145a038101a2544042103050700d094059403040081e175a8103011405000d88000e54469442d0400780000d10990f8810b465248080f602000494540010307140d0446186c40303c0000c0d5101744103000c2c561041c1c00a0500b00c850a00c42c00a0b80722403803000e1603550f20105c0e140d82251001034413900c080c02c1c0c0d00751b010b00402c5420300200d044580a0001507201e075500301804003c1c2c0c2c00789201400ea440d6000030846000d840304041d00000e0b1080504da0401c0b44048031220040c1c00134001c160143e8010004540402c0c002d461561981038000c0078480080d006a90b550304003401c42091176030b281e01c0881c4507100c0800b840501401c80e00d400d00d03c0341c00e1510b020300b0b4038088440a481c0301e02441045283c14807461080c8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 954948615 1250 954947365 954947369
    0x10b2b0f0903030b1512060405060105040f14100504321e090a11161704180c020105060a0317040b0f270a0e06010c050f0d0806031504150204 62
    0x90400c800030075402e020300a030400d0001184191851402001401c103a64107132000541c3c013a15041c021382d58142070000034a00a0b0a1506001c03092200140e49d40d15051008054840004c108260703000d000103225001c501c2c54044824004188400e001115468640e070482c801d0819600c1500b8164106012100c1d0b41e0b411002e42000340c00300c40903148604541064900e00d81a03400e08402e41c1d038880384004840010718003514502c82001003a100110041005401074019021841d80e8001d249094650303070312030384c800347e0a06000c603400d200c0a0302911070300599100b540001c0c0b0080c549000001c245c1c1c80b0301e010003405c4200b01da10540150841000b550058004264556565161184040e10b10f0b0000c546800c041c007a440d4104541c40328811081d11405406031011010074284041c4c0800314030003d2003541080b84500b00d106c0803030010040c010700210b189015020700410030400412000c4c0081404e40030b03902440c0c550f8a2420813621147d0300030f40029200348081d21a500d0140a40329903 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 954949865 1250 954948615 954948641
    0x90306060605040f0f0e010e1008030415170108120f0c0a060207020a080703020a05040e0114040b0702010c0507050604080a0912060b040624050a05070209011d010b2b 73
    0x20031808211990402c0040041e180040000c09041d540e0350011800d103145401a8114902204010441c032080c2c1119103401005103029503c6035612226010324503080303584a4403400200080e0b41e034030990012501c0d442c2c038445000382800d942c1080850340d903c8008a9000718a9000003400d00c45440c8404191882d009130358080d01c0c04d102d01810240c010b0341101c0401c1e0700c0b50798080c2c00000c00350b50000d900700c201c81d0701500e4890003a140000300b100610090f40c078610341d95202c5851140c14021b4903046e0344038911030010400503050185009007110811042e81e01440301c10000380c1c012403030005006a01076841800035541c4c104a10b8122260184e0b94048a881800039105000300441d80c0c0082122a20982b03042000a6850300d90010b5604d042280806e0301d081404404907540c0309600a20241d12181061803800455a0214142c2802644603040101420510140c0c0d03504400c10603004000340b0110358145952103030100340c8030314400f030480028007001c41c460808201982209460140d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 954951115 1250 954949865 954949871
    0x50d0e030109140703021519030c122309340e0f16050304030c0f02061c020315032a010219060b0306011502100f060305010e030403120f0816090306 65
    0x81c1e10586541c1d044c2030104070310402071068903100c6080d0f60fa007a9500310070251840000c00c0150b0384207070007c00b062070340b510821030680c005400100940c020322b6260017a426031480200782d0809083c03034044002d080c800c041d412035007a820b520b42512450000700d0103100626032042c00516a01c1040c10304c603900910000c4010b070b08001d109892601018414040c3d2401e280c0003000580c0d00711a14841160000c002c141140341550104c1c070280c1444d030b43c4902c0541514600040008407032380d180c0e441842e01c007510307030000100200c00e550350110002c005000d6006061145100c04031101c80c6155140b10604a03c00e4480c12065170300c02c0125610300d003e000080842e041795404e052014000880c1c1d80c0b402032048200000d80ca40712112501a0f416a95000e024002014602c1c24040d01c80c0140145903940c4613a00400802d4080c8250448040c8240c011603849155180001c400b507400c0590a0501080f8040050610b8010b14402d42c0060762540c2111941c0003003601b511220280d80004d03001a02d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 954952365 1250 954951115 954951143
    0x90f031c02070501172a0c010f06090522030201021204030507061a011e020106180605011b020906090604090501060e100e04080a0c0206041505040311030a050d0e030109 74
    0x260040c02a0100c00d40d80d00351901e96441e10019542da0300f008003400143c9612200003521460003021440c641101120024a9100c0341070354815150018154441c00b83d5451740c442c14600c2851162500a04803440c0500461901502404912402199512420000004102c2094400c2d411108100d80e00c900c000718030308250074000c0140d0040070f811240549400380071404107116080304410359030305a58031004051170360600c413841c3d81020085002c1d5034803100c001c5804105410341d40c60003401403000060b00740c030b45000100000001504805080e411500c50780241c2c07a80d9120a41c02002540c80304826101c100206005061100f0301a240c1d52074400c010880341005811180951803681034441c58588500708101d11040681e4010102c07c82004001a55401116814013440c0001c04050600f0350312208803030906c1c0148240d400164002800740104100150a00a1035078207400800203003801c0d03541d8a542d50784480c2c00c0030600100000d145583c0e42c0941000030201d9014146d41e09100c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 954953615 1250 954952365 954952393
    0x14090f0c130b0a08070338160c020607050102030f0f0c0403290a0c0806100203090f0a0807060906020118050627030f0c0d020a0203150a14010b0a0f03051506090f03 72
    0x3a042000c650440c07890410080d2001547c44604000607a000d1a441c0c954681e440c004003a09882013001060000400070040582d4844c0054031000b40a03100240e40ca03d07000b484050b04030070003866130780b0fa10320380400e00c9030b604112403d89055030b500189030440304003034105000310042c00741444007803049258100a5815040e40000c010f036030042e10f917070100f030700c4200c10000e011260740c00210050303000b0700c920511450603442050061101600340e4546030f480c5d518031800c01a694120002244c1001401c02440c0c0c3d091150316040642042001c010003550f9803555196200540340241e1540c01c591030b60b904903e031742501540145800c007201e555070503003200400d86822206400c0b6040c040c0d840c0d104461030011600b00c80a950060140505404d0704024604046014100d16507040d5102c9081c640d40d14600c580368060146414129110035000c600100145110300c0d00504041c140030520049820180141c450b00342c08994054991034404081811b007442c84510076411310901035800219 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 954954865 1250 954953615 954953633
    0x1d0601180c120c1e020c0d150902100503090f0a03051b16060f020c12070b0a02100c0e030610031e0213050f07110c0a210614090f0c130b0a080703 64
    0x40c40c0c0711611300a140c08219020f9846043d1a040345030402d00d4280b0480c0000c10308454943e4035038490b10001251451034001c103060311f54003849000030138000402c4c0400c10401708143c0c0b0721040380c613000b8170060b40e99a030020403502405802c6d00c020340c0283ca03004a540d005100031031601c8500d0701c840054035514a00100184910b8480d84050f004080c2c82143c5400c1030368201c0d1448804a0041c22118580100b0108903406800700008500801ca010090f1525500070307120030150351b0703492428008404040604040703002d0290941d01e040e00604000041c103a20f448050b500380945510401c14550000c20102c2100089507902240b0300410007408051000203270b401001695141031400c1111100103556510082c1190760000c51308200f00181303000c41a103200c802e404942010802c2d00c85645000c1076814406501a0907005a010030001507420010743e0780707440e40c000c01440002d8400000c01c00e1990300b104004d07d41a100c1a6216043e1221031102e4003c1103c0d00458440c3c554030b0800d4021 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 954956115 1250 954954865 954954887
    0x904050a0b0a1a0402040f12081c0207063e0702091f1a040902090414070f260f04080f0301090603060b0103111b0705060703031d0601180c120c 63
    0x11620340040100c1c113040601c280e030140c0e040e10000e01c40950034102c4051207020500c104440a030020041101112581c03041c1c0c92009070003481c056103528503850650241c440b0082c03144a6010000c04555180d03105401000100741103100e01c000081810100c004584511103020350001046414080341020a103504c6110040300440d01744d60036107402c1c41000c03010035a11000300540c0280700512851401c1e600170802c481c002000000c1c541801c0890700c1a600c0308683d981c0101d024842c01d0150380b0380001050030382c0c0c0c81020382001c141c01c0c00e0380c2003543d80c035019043e001b0001203c8000350810500008075400484e941440d243c40c8e40e91441c4001c050802c1340012600725051665008040d4040c5c029141b520b0804c02260342045617010002c08280710203101d40381544600072001801d42c40d184000c2003060b000341d4011902c1049041e0344d601d5480c000b4500c640540c09600100180702d0740c101c20070580c48101c10003141c00d010200c1c04449002c1d450002500061030800307090304003900001003103e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 954957365 1250 954956115 954956141
    0xd0c142703070e010b0c0c040606030b091503070306050604090803010e180a0308010e04050a140a0b100605120703060801060e070f030b0a050105070501020d0203180601090b030a020904050a0b0a 85
    0x250305200009158461032280304039035104242c0c1006200e000c2c94a005030260b42000b40c01c40b800ba220703207000103041e00c5a03a84180082541e40381002000d09107603421590007100d60303150601c01400000441e64a0348144805802990741e1004101c00e59541d401000400741c004103c0380d2030f943c558180b11040f80d0b0030354482c024821035001c00780310218081011003042e601506d484070940e11f46040414110b400030401c0301c00c1c1c081c0c084148005000116480c0040b0803c10040c0404030340d610f00601c0c5040b000c0d20312509081d010710304002440d8860308443c44c000040703c0e68a92611104070641c0945a6500302c07000c5942400f10100301000505403985c4500c441380e071650315000f250002541120f00d02d0000c3c1e0303048404003805014035400b0340010488180700d1000149070111513181c0e00100d130820768034440b07415100a0f04500329601000154050190480304200341748103040002c1d030f12400680000d028810313080c0024284007052003403051060308181a035006107000840d81000b444142c01c425 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 954958615 1250 954957365 954957427
    0x906010618060305070512010306020a030c020312040305160b041113180305090607051207060b060c06240409111f0912080f0f090103051b0d0c14 64
    0x50241c407450452000d400042440440e05080041c11405000018949000d204080002c5880c03000c00002d480d00841c01414010303151024503000805580074414808119807040c413942c0d60f00060702a140c3d0700141d144c1000741d80c07030400c404070140c0d40c501c80760007400100703520040006001c605c0c2800e80000108952200c4c8500604600c1000c0720741ca10320100c1034040d40000c000000e4040c100604103090000c004600300600c5a0320301c0e2400800002a50034410003050340c200300301ca6401105181c1c0400c0741c0b80f5041601c2c600c612640c0e0a0003e20300045802c16484c046881d0804240c1c0014021740540240009030650030040b041c01d402c0029035014403040c5071a2a6000404074003490124010360300c8401c0d903444c0251000b0280c22001c000d6840c003a00300700e181c200e50260801091903c0900c1109601e40b03076960005822100e0040484404a9141450501038a516402c0721076140c158040003510956050045070040c4d04421304140c0e040b0300203428030029518a10070080007900c58812 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 954959865 1250 954958615 954958619
    0x6180109170a1205040521132706080607030b180106020a151a0121050403020d17012409051e21030f0c0a02030303040b04230715020c0603010e090601 66
    0x203c01110780844016000c3c1d042916200c0c543d02d00702e00c0300a00418400203513401e0030381c00000207070510040d6000528606803200c0c4412040c0c00711a50046174502d00c00100300d0f0901d400c2c0e030182c030750000404020805680e02010340499490383d503200e8000703c6620900080b5038403090060b555001c1c0c1e09058070051148081e0070700e140428010340841c0c01d2001080500c590713480f001980da041c032050041c15001e000420030001c00a0611030548294040d0340208950641c0f10005410f0b0384400c4189a031019942c0014000101401400084198214440103800180b00d004071808105504201d43c8403600c1da80300440e0b800316001402d6108000c490503118403090000254050f0884980d40d50740b07410074407510524400c1706010301400490303c02a01d29844480d40000e0071984219811a030181182c0700f40702c1802181031010844807247c0c10001c0c022020603041c41d0303843c04144036000d05141140c45980c000c91080c080c103110050050940340d102d5031100408442480121600c3c105d42c80b40f2000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 954961115 1250 954959865 954959897
    0x3010b03181b190e09030901080f0421020a050601080c0f0f0a05090915010305060a061d010308030702070b040b0702011e0e0d0204110c0c15040806180109170a 70
    0x40c0c4001c000609898280300c640040900040b03982c05422001035a4840d10f0010b4003a42c01094140b0402c00c0704080d5603120041000034042000140c000307001140d9400420000032001c0d40304a903403804a002d003582c22006000300300e16150058500070464007410b0000103140b100040d83e4454010116680340101031500280b08448c107501100039400240c00d10b0401c400e080032038013030b0b4100c440c020076140317425035105242c2c500000aa2085429601c43d03020005640700c9441400060250f610b80e100340c060300030344900701007070045c00080e140c0034000010030481c0f8000c012100040201000482c1c48a40d12500302c001030704110f800b030b4085024003074a205030041100e40c550343c03803005440d40b2245100c030000380500c4180203070301240c01581e285da02c1c052a10000000c1c00309001c0000c01000c14600c43c2040c000300d00c1c00310141400b203400c00e00051046080c04554181d0000c1d00c0d80140802140c2c0b1100c0c0d50240248080203403242d40c44201d1f4400481c900002421410210b449158003000030043d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 954962365 1250 954961115 954961123
    0x504230a020f121207110904030815060403030c0b0601260f0f070918020d060b03090111041d090a021804120c080d02091908011a0301023c03010b0318 66
    0x4500696005044e08a03085a0002d01034003071a8014007142c2000a120008a091601d050301d080d404107030b6000401070b02051048840c400e44109444080c1458910760300903199510008004185248030070001e100c0e64400c40c202c07401101890f03c20714912514a11348905d180c1c06070717900200c0b2031440e0000b070110300300382a02d280281002e5480800c1685020070b00350b4181c0009400501140d000c111905010360140210000703001841503031542ca04100300c0090850381c40c40c0407003211041c107003c1007010f0403c0000e44170103070720300020000256641d0501541800c600000095200020040002ca101d81504031a07115a00c60456240303052040031042d20050354848006048000030865450803a0064020b45802c1c0c9018001140c03140b08484001b0110300c01d504008040c2e90743c0c0c80240310992920102038040030040d4021407400e8144440d840070901070418403c5800c001c140c1d60301100d40389411031030f00150114040c0da16543c4407145806103503c180d500d007400004043c0b40c8c2c00c5c0c645001c0303 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 954963615 1250 954962365 954962389
    0x210b040e0304031a0405030408031801031a060919050a030b04020901171e1c120c09050618030f0d02010b0f0612010312090513020703091a0301090504230a020f 70
    0x2500e00d8507200c0f10a011134441d00c0c0b000303000311002d010900000500d4041000940306043c0414a0040c007000f20030001030885010725138181e4000d420300030034546070700c40030120703a5540303001d8401d0b51032400e81c00183c540c040b1055010f150004d610003000001d00072959107841c0114800c4a01e00ba46076680c4582d0780300e0070300640054a094101501c034650401c03460300c10442544040c0180d50324902c0503200345c1340401c2280081d40c0442c03d0301140b03442400d800d1181b1184040b40c0c1c1481c1b090300e424080800c0b100d020304401801044164100a075040c0d0f010426504044c0102c800c8814000703181030000e002e41984040e6a004203450054008186000380c1542c40e01c100c60181c441c50b40c0c0c83c5880d00603001140c4d9406a080c002c40c500d010070540c440885149828000c00409661802c041c41c0c000d14910041e804032010358a183c100c811010b00c02c404072811240c09441c003007442e454608120030f064202c03441070510302d4500f22000040d00f102041e510700d02c0f8001c0702c2c400d40c0403010405210f10000c0351 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 954964865 1250 954963615 954963623
    0xe1210061a0c070506070204061d01030215040614091903140c100e091008070b07050d14070b15330306030d0813052e0207080910210b040e030403 64
    0x5400340700b1344c100103000c0c0408078002070003c10299503503e085400f42c803e00c0b000c1410f0441c040014015414180320200c940c0c1505100c6900d07040c58820000c0805004280000705088000b8200d001a62042a6504540c040c0042d180c401a5240782100e59008011034900351402410319043c450b24000c07041c4140c20440352901ca440b010310f08200414440c0061a0040302001d070348010501760b9040003401e000d0151854429690407080c2402441e0020140d03001c800c000a0396060401400900c003035807101d5a00c01c1d01c0c0321640d02e83c45909442c203040c00000c1c0f604000075280310082e500c044840c002011660f11400080e19450102040c0360388011514190503911414481069510070b0b15100d900c07140f030704a00c650640e507a540c1c032411700d11449444c2003e40d00035114140c1d01c0104e06038a0440c030f520140b045140c0119036484039410300450340d80c1881140700c54602c8010703500410120200c4010990050660141d41748440014002c84490038050f030700d80310300078258000c000101c8051740d0300 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 954966115 1250 954964865 954964873
    0x50402030105090f04020d050706020c1f0207031704092a08010f1202010201020c0a08070b0f040b0a110702031c12050f01120212070609051c0309060e1210061a0c 71
    0x5501107848132003030180c8126046030f1600c4080d4049a4103200750400341ca0560301801c4201981c004010511540352082c1401c00f901705503100760b0703540001d001c81c00c0741d0303200403550300203075884e07030b072038546014a500a510283c20b283c2900c2c0179060301c40490404a1114160802c00003c8420482c2c1c0e09409000303011806c003d1076070030300c901005010103116083c4148009032030403c0119003c2c3c1040a02d070300131500c040c1d0100b844006c00948000140e4814100141c0230751519041c1c40f594450030003e400454400d40c1d4502804100340c000c401c44245540103811500ca04020b1020702801000c1980300400141c2e40c2440c0566403481030040500510103007511203485d900341001c3c01c806400005080341d0082e040400c0c19640c1c03009000110003400e540d210b0704052480c202c2804810350800a241d6650219444040002604225284103652407441c12a49902c440307408900c0000b1090a480030910540385c540e50821501e40100080e544000781c00303604a80c1003210802c0601420280d40101c2d00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 954967365 1250 954966115 954966121
    0x1302010807360302040207060219020615100905090421110a06020a0201090b0f06130b100309050304090608060907050111100b01050909071d1e0d061b021605040203010509 75
    0x7a4807129040302040b03982d004200b5030798039070000d01242c0c0414800c903200758003c1000c013282042d58030300c2d0212110b240081d007000d1502401c03801d0664511510346218081400d1000420b5100300f83e40409000701402031070032420141020040c00000d000d4080e40ca8800992100c4201d1203038640e40c4201e19404020203c5100d50368811001c0c2d00101ca607902150340e680070610214002c801031500031001c2c402207071f10508249041c002c03a010f4582e942c5a0260400507001415111303074550034101e251502d400a80d465007860250b05502c1650311a100c002d0502c01c0c00704140c40007041e83c4d800b954268040f1440280e5450054034140013500307050669070040c2e003031100a031489800a010015052600c2d40c03400269800288200c0d01c250f404000180c41540e441e107004d50465001070442c0300031907022a01c8007000540012007010b80d40d0240c01040c00c0039000c0c0420803d5088200101900c040e0105006030700b0390000d5540c4a802000040d88100110004d010b0515208681c10717504060a4051103503 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 954968615 1250 954967365 954967427
    0xf12030903090a2705040305161a090d08010f080607050f070c14010813120c030314042612070305040503070f03081014030601032301051302010807 65
    0x5000200280000c0c00200300c0c401c410790b950303c00c2d107010b00101d030258609018625000f00b03103100400b4011a1507403400c010f000100307401030140c0381021902007102015142070f151813400c01c0d070300210010300d0b048054140f04010300c01280191200d1b41c641d032a40314aa03070350b440c682c10800c50380c03080629681201c000708468500c01c400a00d10440c0f01d26009103018056031340e074008100310b58001c88078811384004513038044d0f0744180990303004000031200c602d50409035150a60b1020392242030000f0721000c0305152041500070341200605507160f00e000c0f1034070301d80350526400c004407140f26104843c2c0c00c00da80c130340040da0a200360742c00c850790840811010364800b1019001480094003d0702c951005000740300c0029000341300d0309603079031180c1d4901a0078101700d604070079082403640054010030154103240000b614002450f40c112504140300303038049040070364100801c200c1400c0c03201d00c6508110400504803141c041040005100b03a0740d0202e9a618508122210181031082a1400180340540d00e445 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 954969865 1250 954968615 954968617
    0x50c0315031905070e01090e0706110c1804060e060702060103060b01111b1201020a0c1b0e0f060907110a0b0a1e0501030614190905071a09040e0f12 65
    0x5010003034125600102c04182c00e04001c00c84003003c445540c04003205002c03010600038410300500802809100380c060700c400858654001d0701504003001703101ca401040c1c3c16000c028000649801800703800300c2122000000c0c1d00400700b2282a545581003101d9461107900000381030b0b10035281c80d40075100c0c590856031100e002e000022151340c1000109400b6404030b8200340b00c2c0400d45001e155400080030550002d2280802d0998079102039a48140711004c1503940000c900303803440c3d0b4444541520700c2d4416640f08044440307a004101092004810040c0e2481800d6800b8000c2030704490001599840c120101c81588542170250301ca034101240e8400000c3c107071005e407a084209000007040e050140c01c1c0200360108003610442c4c109132a20010410b0250740e00c030700049081b000401000c4c0346062101f21300c00050a1120107807181d030380c208150501600307000120207004c01080480c125009402d0301e007910341101480c02d21940c54a0f40281641e8000145018500b88907400740c084042c60312405501 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 954971115 1250 954969865 954969901
    0xe0d08130317090c0405070516080d020714070305100902130507200706081b121b040905010303032a03180b0708040c06030b06071103011b051804050c03 67
    0x9000342000084103a20340b00300d180740710b89a160700030b2200a90a80c2000191840078010f03206202c01008264200c11418110403c1c003030700040040d60b0f030307122070540100903c14110080e01c00300031a82240c8a465020558a040741c0c0074104a5540c50b0503040c001d401c6840c4820000d41c42914003411020701d00f2150071650344290542400c042d902c2007046084c0d01040444004940c03500080c00900c5601e0300044590f801410395125901d804010389840111442a40c103002001d124180c0040c5400e00c11001d00800e0a812016180c4c40325600d280d890041c2c40c0070301040f00407030b0400c18801c180c000d1450307080c10107110040d5410002c01c0c00200070f034028514050703006895100c10f50440c010ad440708170617a005a1031640c0361011440c150801134854032098101004150402c007030710003d81d031380e0002da603171407a006050b03140b04440c8080003a005010300c0300c601c042c0105070340a03103c0541d0404041c220b21010030040035800c82c242010401120000c0b41d030044030380d50901c003040921000000c2001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 954972365 1250 954971115 954971117
    0x40f05130f11130b120711030c1204170a030e1e2710060c03080c07120306030201180b0f130807120c05040902010512090102040909080d0e0d081303 65
    0x155005010100340503105078240100814500050380070910f03082c00708a800910500d043c2506202c0a081c1d00503c2180c0a014041080441c5802403c4464180201d9200d14040d00881c0c0031500d148003041040d410038030804a0000c0d0054042505050100340003140b140d040c0d0301c48502201110402034a441d40840300d45007000d030310051081a881d41c1034490050346110100d82d120200c076031003030f00300d0b040c0007412034283c0d40c000700c0304004064109408480c1030f0742c1414000c0265451104507055406001009003c041c0c81101c0c4140c40b0740c040d8401c105507030003030b03a0b501c18000c0101411548030040d0301c01c01082071010000e0007030b02d9103070708040c1c03041c0c00a52a04800040d647c555452811031035400c803c50440400c60407a08008aa0210741c0003070905882c14803021103140c0000e0321a0040ca9041400558040001141c090007035040303802401c6d558070704100e441c80c00e040a01d21034001c0b50040340b04528082603080c24a6000485400450495503013001954400c91401c0720000c00c010110 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 954973615 1250 954972365 954972371
    0x130605071101020a09030506060a0b0714030d06030f1103120d09060212070801060927050402010c02030106140102060109060506090d030e06120429070c1a070302030f0c040f0513 78
    0x8050507003e0004000441580e030302e2603032450035810b00c00d04092000d490715210f980c4c42c0c0c070108100c40801d01a070350540e80202007408513110500500d41507201c1c1200c107865181c0b40c04004003c10107c24441c148040c0201d454100144d10001815554248048031428182d0140700311701c0d02a9090b080000c095200b100301600b808684100401001016546600403510010062010304e40c82041b00700140004100c00c2001c1503003d807542c000b80580940c0150f000e4840d0001015079018610b001041680a8000c100186c1e8802c030380039035001000030003070040c0111400007442c01032034041e80081e034100615003440e00e4000d400b0850400714449007101801943ca0130074815a4800d0040d01602c0c0e100f54400c0c00902e0249403800150101148070301c0440e090188803090260b49031a00ca501c2040340c02c000280c0c0e0014103100c140e54a01c505aa01d00729411401c1064030f950540285006d20324408010241e900c411469000a000302e01584190284103001001a46014a421015194011000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 954974865 1250 954973615 954973637
    0x507140d0b0709150306030b0114040e0607032004030b010b0714011b030f1407050d0902030f280312050a060b270d0b0c0f0c0d1d060313060507 63
    0x60003482000c482c00800b01e540c41e101000600d0320328291902110540c50104030450456460140700c90060148510030181600034000301c0c0c44550003050710b410a00c3c01c0340e94070303d4650801005800c84140101d11101d4046203c1c640381106015102541d611080c2040541c1c28044000000c0d0003040b01075540c841070b10030741b40b003044084c8140d1258240c070b20015030018070388020113030546441c0004200c120b860200d448680604e29003c0b140c00400c18982150b480c215107101d4009491800e1000c2e50600885440d003200700f50001da0308640752580040814540c21042c078041c00d0326003401000d404a60101c041008514640d80415030148400700000784064a030b204568964000c0d035006908600c01005020a81080801643d07030044100c0f5401807110650381c8002e4000000b400c1420002130200d0011345a07014038065610004180c41180c0384a03050740b10050400308000a6800c0c0d00f203004110a056081040440b80320b40d011031440f060150242e601c1c1c3c80144802008041049140040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 954976115 1250 954974865 954974873
    0x60a0f02070807030905030c06071e142d03070b1f0f03080c010e0601081002090f1008011e060e190e1330050f070c12120c0507140d 58
    0xb80401500039640e48006501b014141898800d240e0a498440c03102441071200180390314800c44045042c0d01d484821082452a2031b00d018080d54485a060b40200c041881407a00104c20702d10081800b10718030314458010707012854480c450081c1c094125409100050040b890101700340c1100d100940b0481009990744030308000041140c0c008440075100040c81c800303440824085c00300300c454560003500a035490400101c1c1d8410f440544d0b201040e4000c10394081ca40d40d120318071080b050b80034040010302034803d02e000301551000d0040c840807501110785440e11513000d0010105448d01501c80e000648400c40802045a12003441c0c030030031110740354011442c24640c0c09030a02440584400040031005894100e018105110004269031404900d8041c40003c2c91001c0005204070304120340c0d03e45464171024107a00c20301c2c001900c0d000e690300000810392110002e0004850040a40029070005404c0880e4040b05003a406003840c0d200f40c400340201081e0b203800d100120001400309840e000507682e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 954977365 1250 954976115 954976117
    0x1e0c01020a05040e06120613260406020d0203090a050105091c380726040c0e07020c0901090b03011415100804030512060609030f2d060a0f020708 64
    0x848400068004201003040c084d2030320390f064110500312600c911030542d9414190f50750b000108054403140340305480c802881500b4510f0249404691080030080d0169208101254003070701c9020010f11070101f11801c11440401520101c040c010422080c041c90100111490340020080c10390006640040b0b50b0400c2c40d0380c0020041e89d1041c00c404070700f0700100d4200c0c580d0b021742080d44103a041ca0340701e45603400c400c072001c1c03a0b5024100d820840b907001e604400c06d184070300081091526003280801840b0902201800d00c2044071002075103e41079541e81c510883c0ca45220124940d00003003644014024407400780c0082071803641c09000010b803c01e041382401001042a1901c038a5840005003600b40ca0400182006090000c2c0c2070009a070f08090380c0060441c41080d00c40a100503880011030810740e00d000850344c502c0c030000d046400c0e030000703d0550741e110400c0c40a1031008217604c215070311200d0310909004000c1000d0704041c00310756940520300c2014182203170001525660070016000000c0c0514 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 954978615 1250 954977365 954977377
    0x7150c08120618072d120e03130b0405101704030e01020c0303120412081e071e02100b090c04050603041119060801050d0f11121f060909081e0c0102 65
    0x143e0340d60b1709030700303444605020b90480e0485002c0008070102e200d40107036000034a02c0c1c1220840100081c04540001825081d4001c510362008850f0705120b0010b2a1014800030f4429075004031413003503c08501c0d0a0540d140d40e130b0500110040000e03540000c0109004603041c50074484180141ca05c03541400e00000d08541c000741c17504c1e040407000f40510090007160321050b42e50f81da0608108816041810308110310003094213032103180074000b1001495040c494001d0158482d441500b840b440b503015038020703461750100d07c5004c548500d844c9001c003003440c1541c0d6940c011002542001d103024203110a11030340d680700810070350b03144402d44002103158860b001480c10824000380c2ca10f0107981000c0c401007845806a04c00d510420540040c3c101040c200e002c0b6001e85580035010030051300c000e82c04903100c0c20b40d800700700e80c2c24054809004102e010942d034104211000c40703020002c0e580c0b102d190078102d9040e110064400c103800d0004484e94040001c0341100c00744c82c07801c2c0e0303428002103922090a9030710030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 954979865 1250 954978615 954978617
    0x12030c032106010c02060d020f04150809120f0f1903090519210c0605040503091504030525090204030f02040c1b17070b040507150c0812061807 63
    0xd045901000718068180040801d0004481c0c0ea05110000038046020224044d100314000190040e041015504503070b0202d903400002c640310b640e078071054104000040d5004007c110050000f030204c0002254400d20f10f1101540d1604140500100322440c2d041b200c0c200c0101c0100b0400c0d581e0707480da00401002040003980e0041548076203490309500b030a45a00418065a54200c00c002c0011b1441040c500200c0d085441c01c42070130200d00d0308592a2104940c00303003a131441d01c0c0910081c02400300c002c0603600c105452000ca120203002c50540c4e00d100724030004d01a60804443ca41d8034006500341c0c1c0d0441d1114240c403404494442d6076010490303200e0b500c00c42d0112590404101103040c1805030310941d911310700b131003920304182c0e603111100070a00325001014149026128004c03841000c05035900b080e04504014010718040c944240e07612100e00400809000c0000c20f005401d11039040c9801103139004128a08005403c0c81c40d079949480600410f90060516940c03640e50520407540c0351103110740e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 954981115 1250 954979865 954979867
    0x30f11070c06020f030306060d0609140906070906080a0c030902150a021b031e101802091605070605040221010b090a020f0a05030c090402041d310212030c03 69
    0x15841c25500380022540308109540008a03951095400403055903449103090312480d9a40381c16505000051000d500207140407031400382c100b0455400c490715240b00307017498003c80b107280d02e4945042d00c00c0f140700e00ca000002803a0f04001055080c1e16004405406003a0501244802050380010041d001c1900c2c0200740210100303031082c901d5410061520740322001c0a80c1046560f1080202e40c440400d1901d10f483c408031208149510301e4100803101c55612500000c1011030701c109000c0201134550f1b0f606922800e004004140d0b0381000100038440350790300d91500d41c5805020703030f2031802404e401003043e81c0c0012081a6011030503e080c0d100404031a00318000140c0d01c01810411080c5007003c2c0107003614074414400400301c408202e048807009203403810030030303126511002c3d0401c0c1032280441568001c1d0000c100064850501800300b9148201400300c1001b907585d007041da104050541003000d5421501c800c10b40b00350301a1914503181d01c0d001505501070100801c54440c03459102c0341a4404542c8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 954982365 1250 954981115 954981127
    0xc040b0a030c0e070f14070b09120c0102090a0515030118060b191107050a260f062d0c0a0c0203151603140c250b010e13020d030f030f11 60
    0x140c0b00301012119106030506c4106071280c8440801c942c000c01000034182404100801d810034010040c2d405550600e001d0540d0310340a40842c0e0b8082d40043e500c0d01d01400180f24007040520380404950007048942c03031210f040d43c0c80d105944182d590f04000010034281d40d048040740d01d203901c10003480500c4e01030800c956915003c42000b040c07201848007410050300944403d00c42681c4070805181150445001030200c048940c09000ca00000305508208603c01e038010780d19125004900d8901c640d145c11940030b41c3d813400d0840c0a001c22410701800c0304810300400010000d2110038082d040c2d908030352800e04040710950380440d19010310070384aa083c4245131010400c44031414005d02c80000c13002d06d001c1c0308140d000c075a45401200d0182102600e0500800d46085000200524001a038240d64800310360040604080d54091070070b001d5402c0e503407580d400103800c420825180c00e5034a58003130300c480640c0e40652002c482034000c038010102010313140d070201000c04c0c0765802007540362124940c809035982 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 954983615 1250 954982365 954982367
    0x1903270320010c242703020105010e150616020909150a0c0903020f0d17120106030603080a200a031e021501061b1e12110c040b0a030c0e07 61
    0x401907a9018104201ca0165100080b40c1452001e8201c441003041a0700c4152038210b10060205581d4040c1c40400003000ca10300355811032207034003000740640c000300b107070341d89401c410742c01c880c2c0443d85094030a000f0b85020700c45040c00d200500c204440c4944001c602c0c80c4550014a2508041e1a1221280e000c46090140581d1100c2160b0b084032086904003c0d442091201405d030414900c0040d21500d0314440441c0162180030241c4900d5502144a2540b002c1c00416150190017000c0b803403400c0001980041403490292085074241da407c44012400c0890300c100072200c080c05c0a1210070310020311804194004000c01058202c0c038429124030f40140441608880450302d500030480c00c5501120440fa40c001142007001d040d00c1e42441c4c016a030300f0103008448102d400e000b0005206e50311203000040d089074005807842060740b117040200c0b211805007001302c0350382c1c03400c1680c1041074002101e081400e14040d44444251903015040010080d52522481c01d150744039804600941c1640e000c00040c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 954984865 1250 954983615 954983663
    0x106050a0f03021e0f0403050a150605010e0618010207180207061a0a1203110d0809060603160501030e1c0e190b0403030807030e0a150e19032703 64
    0x105031a0b107030440c101440c0035520034003400300c2d24280006850000740040303046448000c6401035504641101c00d86441854081c0c01c00040d401443c409518024001c5819031081001340c080d444010111810022102e5900d41a33000494034203041d0310030204001106070302050603e400c40f500782c0005880d01d0450070034009407032a03c1c500303559040d00c0720099083d0b07550b07510301413042c1c0300500d85580904a0314681902d80e02c0384080c2104561088480d404505548408003038401c0c4903a4050340d40ca511a4400d02d95941e07103901c120f1021700c0400c402488954400d85c8550a1440d10100f10b51050380d100c11100524541c840a5000281c2407280711342c0c85042402220f02d0300c142201982e11100d10b00120450240a80d020080402a0000100c2ca44910030303000904d4640681007035410314030305842d00e03010603406140b04440c8541008a411040400400d411807201d0f00b003252400390031030560741128000407c0203803c030060850322880c00d4542c002107074200078621680fa04030340824600300401003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 954986115 1250 954984865 954984887
    0x60501030b061b0703060e16090915180c14030607050c190201260a051003020306131403030703020c120913090606052e0201090803131a0106050a 64
    0x14942008a01100d0b921a9001c0b10b10741d40c80d0280e000410608a802c580c10502e040d40003600c1e607401c10310115850500420010000d46c0031900b0070003855079800818055415a00c009023890f1828214000300c11420b8014010326502e90304071405805156803091108201c0c2d400c800e141c200b00e030107944224101080f401d03800c140c80c0e05202d8203140c14038005a036160100007080c1c00c003250107a10f0008690041e410303045c1d0380003c031038aa10540606d80781c070280c40c14111920840d440c100b10101d030050842003041003d8940240282c03c0940d41c0819840d610006008105d132024004140140004c4052001d14042c0c0850f950160765205100540f920340036030300c034030071140e80c10820510301d541d030704c000c910501c146132040041030360502c0b07090860041145070b003c103801055900412030078000030070f07840e02c110803040c483c5100111351800403401c13900310308002003140c4802c001041e41c00d0011003c007000140303d1002c803030000f01c58001c60341078500282e10180c013041d40401e034130038015000030340d00c50 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 954987365 1250 954986115 954986117
    0x603050c0906030d0f120c050c01050f0114010509060f0c15090601150f0212040f03030311031302090c0408070605041d070509040c090807032301180305030a1b0206010801060501 78
    0xc0900b09600041d03290b148098055041c0100200041e06090146001d4140344a540034200544442110060300da60f115900c082c00c48c1d4030307005c0040d8505400041941c140c0340b81802c2ca91485912400540e42d0b940441000381d4800c00a114985006201e400208070010107000606548c0086250b005000d200288c512125a0840e200500140318070b003440f9076440d000d9140040039990460b10590800224044441c0c9500c2c00190104095a00c10780c44421284240c2e0100610b02c1800c5132181280816034008423503030000d104240251501d100b240340c1080c000c403032451919546041c09441c040c0e9580c03208010500129003041140c45c44c0c0d01c0d60b40c82a16008400c8031602c3c003004010082d02c110084075100b1940c40c400041002e102c0c0000c3e0010b01018403c03125403a071a4140007006081d0900c20a00c030004102030496401d2060145c1000304002c600140c0d0040c5182c0d90503035050300010310510026654109004501a01000351701010071144c0180c621941002a80e90a448081e044030b4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 954988615 1250 954987365 954987379
    0x20706030c023304050c0114070f0b2205010b10020a0b07181809140d081b0c0d0c0c050f03060f041e0311010653010603050c 55
    0x1e04550300032808011014000c10f04a050380303095580c01c1000144030400d41d01a50404040108101e0002192410080309880f200242c203a2051180c0952142000003000c070042245004001183d400d00d05400c90070041400c010780c2c409a082c201a080d0482d420340e406e80d11103041031064188410b0742c03065030780c1900c0503141c0408142c54001c6400405040c02c4201300f002c031a03003c1090a00704d24440604014040e800c5250024800d18000d014408001e99603000c11000381da5600e980020303110364501058440a046944407205c1c800402c0421300d01d00c1101c0f07000c01078070301208014011415226610f85421001c5c10003410010420760007a000a07004c1c98000300e80c2c440c556400200c080d801447e02d01e282d0103035a21860310070f007a045e81000007118840d0315101c410415801c03042c410703081c011000c001c101203651100c145002c9100e10140c0040e0241503804558900c6802c0719010b81d0070b1b220001c15140c02000042d01c0030400000d09001c5031a5980c030030a10030032000340051524084111692 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 954989865 1250 954988615 954988631
    0x40e060105042601020d020d050115110715030f05010902030411030c01090308070206040e132a03060f062c0c091c061404061e051005040c03060509040c030302070603 73
    0xc40e003200d0103c01c2030346242da441c200c400c80c840c00075011140c8003801c0d25404d5480341422102100680401e0040c2800c004809000128a5128414031038800e84800d00410310342d0303c0d00d03c0c84019602c5d07a105940c205070312141104080c0300103003c0c1d68020102824016501c2c58130741090400000000c001d03601c00d40151051048a070307401510348040d00d401c4104c41ea6100c1032807000504038495507200170103844008040100d0040b1444044910310b02800f601c00c030000c0140707501751928140040c120305c4d40114000a01c0807a10399401101001003910303001540c40e0300d42c2c5000d5400b90300341c1c0c3c9000c3ca0b500006600030100c000c000722283c2001c0e15050050600310070b40001032a14007500300000c101810038900c002403000e9500540c0e0498644000d520705030801d410f006e8082c080880300400f0b540d001b0001c082c10300713119204440c86203158410419a09080c0020080984411b00908003016100c4001192558805d080035002c1c610401820f6100d600e90b24019003402e43c0e0b54080b5051620b80411 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 954991115 1250 954989865 954989879
    0x913110a050a0306120c08060f06150918150f0a050a0902030606040b030c0d060602150601050a050d060803040501031506120b13090c0e0612030f09030f0a0305040e06010504 76
    0x66456400e481c1c00c1c0140c0300d1003404000c900500303280e803061142c4c0c0d10107840941444144015030090ba0b40c030105451080c0d65035004120f21030015250550007802003603918810001101c050540510000c0c000003007640d0795640d01425100c180c0f6400c2d000390b001a4040c0c8146084450082040011b94480d40c40c00d15090000d07018480d03a00c22801d545400000158041c0c1c0c41100b2180a003225284a90316030401f01809919a008440401001860b0030000b20348140001781116410703800b8200f8509903a1460011101b0747c0000014505005080c000d502940025009000290031400b0041da2a2840d0400050607107200d20f500c254500700e9200c2c10301c800c1d640701503003c0661400040c0854140210000310351061401d4024410a0f0325002da01c90270407005445010445607200b03032060315622a4010422030f000f44008510080d4030401078041804a0303403002c0c2055070b4008055450f8101c2c2c0141c1c04c0d0a1084071301088000520014003441264111340344507030000400e03e41581040c2c10450 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 954992365 1250 954991115 954991117
    0x109050a1d0402150d2705030a030f061a07060606030605031b0607020405040b0f160203220f080d02060c0301030812040c09021903140903030609040f0803040305091311 74
    0x1c400714040c920440094159100c401d441c0614080580e955603844000c4050000107220f65000c40080303400281481042c0d003861070801c01680d810401031494900141000d50080400e805030b280c105850300e0000502096042c2440e4030812940c0c0103994521030340c038140d03045031210b41024090500c1c01c0e505010b5034a000400700102c0031184460b408006500f0001031090084204c003d41c000d003040c04110400c08082c510f9070182842e4201954991030b0340700c514810b64010404c8030010790040c02141c6400300c0b84c9000c29004d80c0c1d40c6112602c0c04e9110f040251a4400c42d4104501c2da030700400300031003696410016603900c04480540c081c02c1d941036a0740e0300c0c124071500b005030704d0809000d80810f0602c4803800029004080e0010110340d50580d10802004000d5000d9941c0e0201740350400604004204000c9c1c1441640050091172560340d0740e070100120380740043c1061f07031040f44080c950070008592400850099001e5142e86444984e54010824680040042400f40038204040030407000311f100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 954993615 1250 954992365 954992399
    0x10e030301030c17151014030d051608070b0a0e060901201b0105100503101503061d060709090c0e0102060403050901120908040504061e0506091f0e0109050a 69
    0x2500004da09040324001ca840c184201e040070b00180c030308505021105868881203400c5451000382d04081c1406803082640301d01c2202503100100e0401c00454116641c000c280e000e52510480103981071400030f4a940d10090411034000b0b6055955100c14210803400b01700c1c3d9948100b14a00a010070301003064601c04203101c60001000080010480b0381803581401032071919400600d000300604c0c81d100300d008210410b20720645010340540c458440920120f402440d4a01013504003108a2600d1541d418004007041080c1403040d5500300113201085034140301d454095191652454032050914001034101c400c080008801d0007407580c0c006001d641c01086082e0701680500b48562103941200040c0c4031442d030103041240961402c0ca683c020844140003501c01e0f039000340d90401c42d5a40300d0380c0b185840c0d850b90310f00d40314450f40518100000d1514000605031041c01505e06a90718404c0b40541e446054210740c1080821036051112646503030200c54034000b000c04581c0d20341d80910f0041e8100680c07010b9 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 954994865 1250 954993615 954993629
    0x80f0a0201051303300201021e0703020c030a0c0807050f01171b040306052e15020c090a0b100f0e010827031206040204030b1f0b0a03020c010e030301030c 68
    0x1283c90361412070050070010045400280200b510181300303801e40030003c907158099206000f503130311144840d4814420b41e54401340000040382a180f841d5500700042e0094030003141180318001c8442c907152024060500d49601c100307070010140d81040d4040b03003031502a812582c0207802500c40b513080341e03074062480c0d03541500c441d0604000751503116024001010403910720b88100e5000030300004100483c3c0c1301e40c2c404d08500010601c1414409003018840c40034100d846e410075046030f414090a02460381103101e119050049443c5405980041805100102d8070030312010303994000e0038141d09210070142c010124519142403030304c80010000e003407202c5907500385041010b9103000130740000403e1101c004440407140799406040c0700c03246050343c2c0e03030080c0800c1000422020128a150030503000380d03400c0c0c035402803030f48900b40d4880b0004a007000e152840d140740c0e88181c00000545844041c01851002143e50700540d840d040c41c10140d0945941070700486403a4001c000402c0031408048000c1e0595900c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 954996115 1250 954994865 954994867
    0x6020f1b120a0b1501110606090415140103200d0b0c070f2120030a0509061e04060f0c0b0a1e0e0703030801090e07051201060305030c031201080f0a020105 68
    0x30200d88603140240c041030081c410303603c100501102c45410860320480110036680c00192140e148a156101e090944005401080b0f840c080303800144c44030800101241000c0000801041075102c070700900c4070a070300940d406007054481041c403041241c0508580b503001e45184d10414407a0f0380701c00d81010300402810307844202094400400803440b480452194220710391500c00a0b0070b01e07002d4200005042c40d20081035020012509042c090006505042c5000c0d01450421900900660791a4846145158412420090b070010014403240740d2466a06502d8640d488601b020790203400d5810366020407040c040660450000200a84840c0ba400003c090000c100000c600c20003000d51211142d001041c68201105d4407160000000d080d01100c0c001d0741e850889990b90782858003210060124442c0301e810101041c042c5040030b030b22445100f40c0c07007000043c2280d0350b61600340c290b07040201c81041540000031500011824a4aa180584010000341c00c1050f902550590b80300c40c4401c0083c103100c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 954997365 1250 954996115 954996139
    0x1e010801060e0f04091b050307080a080930010b06180411160f030801060507030806100210020408010501080f07061e030b130212070806010c23010204080706020f1b 72
    0x210030441540e160343c09030040c07000c01e100d440c146401d07469408200b0106800514006211718002403640c0403a60001c000d0004d030f4070951034013901c41d03011003501d0303400c000850151031981907144240c098484007400403e440502d1a4895030a4651007203206200d02d6060242c0e40314001142e0380c5404150089174001510114081d10700600e0140c000041180c031000d00454050020800d0002d8a0510075901d110250b070700e4503000c2c0c030603004149000e000903207480005103240c107007003031034454600250045039040c00c41488000b0581e407080d00425a165110b40040200c004100603040c03038000c4035405020400d050403070080450000b00207000c000c608450203a81a140294010426414044c16000c2400300310340c505400307980000ca90500001200001401c5140b0602249015000503595a1801040c075160b00c3c00c2c03080c640e01245022000c41c5800d4842110074030051004124040141400ca464804040e0814850130f0301c0701c1d01d50b004401803190f401001040400b1011040f44c1a0303604007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 954998615 1250 954997365 954997369
    0x1080d031e020f0406020606060310180603060e0d0e030309030a080d0b19080d0c050613020303160f02010f05040602070b031f030803150a0311040e03070b040f021e010801060e 77
    0x41101074508072140c03001451185140f0b01100070030540b143c50302103c2c1a500c2d00e40600c0400d202c04c5800d41401c0040e10018000c80b1044030010700315001d14480494447c0d00c07901d640040f2010000d1007485a448010548035641e00510000c9221304200c01541c10465413402298581c1011030004103400710000b1140e90710a2140d01c004440300002e01680d2895a662290358901e11107405042c5562003003c803116980c80c411807100c81d82c9607000d03001c0c6c525501c640642e00301883c5400d10481e8580070a11446d800c501e11703100e0020200b405403c044c00b101708030780005003402c00000c05c1c4004020b820001070040030307000991042100d21806c0341655a5840c80040700007800101e01101c5400d5043d10b001060201e0900036501406101c4041180f180d03086080106807100c0d8440203081800d0611880c0e02481c0075401102c1044400f07054918010b080d507201d114600d0700b180c044805c1c085084856082d030800d40f400702e03070310241480b0208540d484130002814501d4140b142d4410061404c0035800e884d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 954999865 1250 954998615 954998651
    0x1051c020d0807030503101e0b0307210f1d03120c04080f0106051c0302120f040515040608160818030f0f0d0e030403020607080f09092502010501080d03 67
    0xc1d007060680e600d5143c43e10340149590f0081e0380c03203030900c10603840c0418200e4100d810f01440d113104119801c0740038074105503007006410007484102800400c2d24070342039882400c243c1a141c0504942c2c0014000034000d20001260082f07103031420700407e962006030f001e600000443d8900d0804941d400340640d40d4801d109103601c41c80d0001c506600a8013400c1c5100001500010160744003252419652090fa18507005000d000c0751015006920640c09580310294403c018000c80d210450490700c1c0940b9040030800189241c601c008402d0400581044456070000d007881c0c0245c42c0c503403400900c030700c2d01000070003048c0d0241540095100c261168034000c4800c00460301d54900280659444074006003125080f80c000d0407000c5203444c140018942252000b008503015241d004000c5801c1002d50f80304d0554075008040c150f8241e240030000300c001d55903100140b40c41102c1903c2060403e45220718107040e2528036140560070b681c1018014003507000081000c100050aa141c00203202d000c2403556041 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 955001115 1250 954999865 954999889
    0xb1303140c0309150706113603032206141b1614032b120204050a1202120c0619030603060603080c0d0f090308090f0a06051305040501051c02 62
    0x13100101c050407001d40e0000c03d0140502c00d015110800c0204c1c0d8094005d03090f84261490344080114a48071004004400c50403c240060801c40b580308180844d40030924550000110510200001e005505803480480692020b482c0600d03040410012441022a980c000d2442d40816117922605224819000300000704034806916002480c3c65a20203103134014100060545010b4003440b12480360243c001c4000710301c9d03100c0d03541c140c403c000f0a09104841521610300c2c880c07400e603000c1100003256562484000c0180091104021004455104224041c0b2841c540011190010505000140d4481058440e0100900b40c40c0d8007401e0701c1142240100181d0300014080c40ca0014007006000d010000350610180010480b42030406e50142070b00c8904071564250b0004a83e40024400038a042028043d50007001e41503c0320709111348002102c08403203406c088001b030700225a02c1c8100107024800d20003041e058808000c2541024046184003203190840402c04041c50011011501d4030426070340 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 955002365 1250 955001115 955001119
    0x513021237090b0f09010b01210b0d080a0302040e150a090b0d050307050f010c171b0c1b040c030902010c2d0f0506060103180b041401060807030b1303140c0309 70
    0x3c0c40d850203030001c0c44d0055007030740d0740140d030362802c0f42c0044254001c403480d0030414581c152030310000041c00108400b401c5d20800ba01d0300050a01058000100c000d40034240401c469100541ca80c2e0400d10362091180000303040c03040d40e00400c440c00b01c039600c40341204800d845c102078000c41d5410701480460403c1c13828240c024210702c4000b44210034048041400000544000d00901c80041303c40800c9928000e8a0a64501c0f541e2003400700d461034240060312100c2040100700a8240b12601c0b80345414a00c400341056000907061038500b0651600744101007101030181800c00065095400090100ca20340c00003c09002085100b5a10a8210700d001012004106121303082047c00c2d282144c0900d074a0502142c0612424012802540c081e0041c00110211a0100364403010030761266080210090001d071100f079075800d0f803540d141d4000c0c000e4070050503039030000340b102900d50300c4e020051602c024506005202409000170009501c00d000c0030010000310421501c801150454030704501c80d00d04069 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 955003615 1250 955002365 955002383
    0x5040f06030b040b010309080301060509010c122706020c0f210a1403070f0831080709020307020304181b0c02091806060613051302123709 61
    0x140ca56810340010000c02000d0b00d05100203840100103400362010080024080c507014001070000d14030800250003e0001498040c50003003164032516213940c1041c0442c0d002520341c0301c400c01034074001c0707170f1021050b502d84007810807180c0380ca80029142d0f01e40401d40c0344645001c1da81400e030740c1e440c039010800201c04090030241034641c82c2001d40e90790891050403100c0d9111880f1046c0340c040084242e41140e50031000940c48907840755039111860b481072444c6d200000b20700c00a04107101c000307903071035820041c00307010780ca842400d0803059481d00116600c55010980104100f00f1744640c04425901204c0b40038042c2e45051008000c4003000e80302001c00b045040700800c900b0107044c0d512018042d03403503000b41c4550000381c4a000049524018240801b4100c0d4000c3c40414940c0c01c0620081440b10503006031286000e403180c0000c1c09000c1c041162241d0150040380003140c0b00f90054259070010180a8201e04013104284002c1074140d1030303174040c101c0c8070a824107840b10785980d0b0000b826150f0300229803 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 955004865 1250 955003615 955003619
    0x30a020a060e0a182a0e0f04020c010509010534140c12210f01170a150e1e07060302070614090708010e0a03090e0a0216030302091804080a03050705040f 67
    0x210000b054000c01c4103403051403a00d071744d05e510280780c103a0f01e200b0000355881d1000640100c0600c102450b480307071403e8100c0e40c204042401a002071103254001d1814000100702400d0201c00b422540901200c068440800c42c804024554a511202e04406185081901889880e982901142c1c0074040a800c014064158968040800d4000414a004142c0c0d07c03041c18071320011100550050460b500c0c1980141540180148034070074080780c1d03211189004442189500b5a1270100304072007407a44041c10754440c65442d111140500c6041510035001c40f0360301010221000840d0346d040c0ca40310303080074550300050040038000b49800c0400c2c05000256039100ca070a068440c25560001e9110f0211254a00847c45002d000c001c9201d0031260340698549844504040c0c03542d04494000d01007003c2c00307900300f0081c800d00d840e81e403030816030a00a482c01030715450074006011192100c5d154102c072486c1c20008000001c0c100300203503130700f49441c2e260020346642c23030141c2501c481c82181c001040222542d0b0300 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 955006115 1250 955004865 955004909
    0x6030a090519050601030b0a2906040801020c06010f050904210201060909050c010f110706030b060c0712060b10050a050a0e06130303112d01110403150b030a020a060e0a 74
    0x81170b040368840c3e041c5100680d6001041030860b00303070101e80b03400e40240d8802d426160882d4840c81542da4070080580740b400d565090580c0c22a840b0f00b9800240e500800010001070048000721001800b040d1201c110350700e455a01c507117440300c0d099040b80901e60400b66184a0074403d41c030000c081c01424038200000405820095518200400790301e0000d40703242c402c445898810031907100d1003544040205002d074100a8143c015121040b42c05402917401d00508581c1c00382044050010480400981409469410302e50259000500d4284c0181c0b90041d520941b80d620600b1158900001c0c901191151988481101c0840003d840c4950081c004686007041810750808802100e2007a01c8008072000d046000340c0d02c8032408194640b031210020100e6070700410047ca1400e03907200c08400041c0c01260f01c0c0820340140c1140d0401d40360012441c0f07054040108512a201c0c4407101240100044500d6600040603c404c600500080001e1401d6640c02504c03462202000b820b1a01d090000c01300107488 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 955007365 1250 955006115 955006123
    0x170c03060c071a361006030209060105090342040b0f090a0210210e151918060506060711040b01030f02030a051e0403080718090207110a1406030a09051905 68
    0x440d140e20b011706180c0703040034003103880b4400803a1f071b01510015a541d182e1005449540110340c000d5018040c1040c2004010704e00c0c4030030b101201400c03180c4412035071006880c00d080880d079040c89840365111018440490302c1c6000c1c040d804401001d45400c59542c002c0d00c141002c04140000b504104842e030005141c9810291040b580c4001050420544900d10041000c2d210702007400784458000a5840c81d480c40c80408041d48210305800f41168004244c20250440e219100d0301d160642000440c2c4040100901541e50801e1003150401d08003030b40d50712602c2c855240145610701c82d56880f0340803490f990107900045d0550030300102c115200e00d01101c41c6c8001d404115544102140f41d00742c842003103035900c80b41a0040390540e0781c5040607030b81c048040d1034000b140d071051301c282c0c00d10510000e000521800203090481c03081d182800808070000a06c0360420703840e00600d116000e801206591501c07000150fa0744842820000b1a100d84242001c1e8142084039860390340d1344201e0488002805030020b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 955008615 1250 955007365 955007461
    0x5030a060c0e040915091a0f0703051e06010f14040e22080d020306042a020c03010c020d1d09040503030f0c250507170c03060c071a 58
    0x180b80d9110010020082108448021400030019002d0b55503d514040d10303a1301c20f9041d00d100d442c40000b410744444840c1851403040b02e8030803080f4a414200012a6458005c0390b070007003496a02005128034001d041007180400500c490304000301c0c580001c0e90588140c1c20702c0c4e4401801d0004d07a0343c840e00c43c0c000002d101002c031070007540101000d00030b13815090b1901c8440780c050f0b004072540e8102444202d0401c065840581629030017502e48001c0102c2c00b02e07030401070007000002071003148500c3d401d04029040c240850340581c03299141070801005990041200207200c00300c0d203000c401c0c8400c441a510308448412501e5600400c1c10010081002030010003140504d0914014024542d901242200d09100d05000c22564221407824682d0404041400450285c440c00a0b12540ca03100c1c40b200c40c480744150501840c95100240d007040c507003014000036402c000c801402616101058a440c5001d41c1042c41030b1910304101800074076143d0b503c24000344045140d0690f168862041548000440001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 955009865 1250 955008615 955008617
    0xf050d0c170304030c0b040e04020910091415030105040309170f03030a0c11070501120c02150901020d150302090c1e07080a141e03180f0d090b1e030402040605030a060c 74
    0x1c022038841c0c1c030a0247c800320342ca4001040443d9a9903030074403100000140c81005d46044507440861007500782d020340d002c02030101514600310301d0400e8520210503e003000340c501030f91600c014840420b900c814444140c64800030366440c1c076010041c030a0b00d04010f15060700c007940404810f1104140c1142c001d0448c4d0080c036601c4543c0241100500d6880d1122445841d0102c0c0340c400e02d51300e0700992500a1040140f007401990a04031801c00783c803410030303011500d4070341c26580020201e800c2d034400d00c6200d030140c0b106601c0728801400c5601140407030754064040c01c80c101c00460341000c400300e07020041d0f04c0724120016103500c610080ca4070007842d800050480000c154080380c4003a583d0f842c04107544008101c0500c000c0b004480f10765120b050f87c0098440805403541200e10110460304110701c030842d8003444002e11820b094944001c0c8150032540084100c0c10040188461103e2801c00900e109131070300142d81d81d00e499078400a4028146c0c0c0d4040380d090f00400c0500d5007800f08a0703201641608036 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 955011115 1250 955009865 955009883
    0x60c1e0a0201022802150409090f0b0a06140f0409080705061b030603030d050603010605151b0604030206150a1205100f0209061602120105131502040f050d0c17030403 73
    0x9034003004403800301004d8032544013404496403080503251030321802403d003105042052805440c0c026410030780301191070640d4020386412004003048941304030700d03a1080c01046c041042c0c03404c00c4e030305000e22008861a0f03445000e016101065642c0c0b943c0c030490304207901141841c1d50310100c0ca0050b4450320203d031070100c0240514180c0440340301e21000c42e446540014040e614022495208400500d40640400c3d003640d600c040c04900d0b0740794800507407042e0000b440190b44030100c9140750032946910102442aa400c09400c1c40b0010b85c0000b5a580c10490078494825208403070408104031a4207540041801602c4507484005e000e00411604032980c1100800e02c5483d403039410070400c1e0710407c4001c03034003c0e104208503550000c00c04043d5000c288010042d00e440c0b81c204440a095560076a00020003144007943c01040140444140c04090301180341981440d180c5044848518400d101e4140140c0070701d24000c0410110260150241001030750009800c404a507903a5960b410a0104070b4610302 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 955012365 1250 955011115 955011133
    0x2d0302011b0c02060d150f080f01110405060c0c0d0309050301180c090e1204060f080f040209070c051f0618090506150604180b040f050f0402060c1e0a020102 69
    0x10481d00903069084140d216003000c82c005900303000d1590301010b624214690b88628126546019280d82c1c0010004500070f1032105003484110350a00e121000d80c0202e503850a0507103d007000e1810261021240c007150300319100c0000d196220304119090320020780c041001400101010b41245440007501d0080d4001c20003159044a651000c480302c0c08050608140782d5401c01a40c40741d40c003c601e200c1c400b0307400e0300d12070300085174010f010760480d0f0400004070369070102c903048841c0d01581069014102c030000000a0405402141c40500043e0401d0100000400c0400c24024200101e0300c408042140021112540314060b40c020030413801140300d040c4141c00510305a5505003c0c042106030072201511498603260611a80314900c0c801003900b10405000005d0030400298504020840580e000b00e2011500c10800080750101010200c2c824038001c148000e2002c081a0903500541c16504684e58164255540d0b160080449141d600084400c40c01c0b02c1c1424082a05203085100783c08682a1003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 955013615 1250 955012365 955012391
    0xb1513030f08030a140f27070f080d050a0f051809160318050705041505090a0606030f090b0a050c0904020a0c06051012030c020604170a0203070501090f060c2d030201 73
    0x5500b59503461840e0781e42c0007c20b40c84a030ba4403010048404103101078880c004e003c10f160f824500180d0002d110103284040410020724103001000002c401e61a1991070000020009080f11001d040a041005008100e44000701911031659500040040490f041864061000b0b5240f0300070002c80400241400c0180c5d00348140221011a601c0d030100c05408481d041c00140002444030091030b035600040c00701b00050a4a860b0411030181900e804085141c1d0f040c0440039064529404001e01d41c0352030098034002050f6180d6500e500188403000110721a20b030040c10801d06d0040304410395125200007203c6003000d030407080c8a51401e03c649424030250307030354401b14813035114180b10301650601c03000400340000c2c0c1304101c7c0240346440180001c3c101303038861481d0a1a080000801c0031140d03c4010340c0c40a51074100a148000d20007481c103000100d040117079055101031148901c4050040340c142000130002090010b4880c408102c50b24a25402d003a030300d0302d10f940440c50041e400341d440c0c0604800f43c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 955014865 1250 955013615 955013651
    0xf0303030105061b0a0f14010c02160603020a030e0f0114150f10110304030303051f060e040b0d06050f011a03010305030405121501060206190b1513030f08030a 70
    0x1d410042c0700c2070400c1c81c004e8111320808904034512515008000070b850004040c03820680305140501d6100030445a42c80c003031402c5403c030723502c2d40d01594071500044560303801008603d030a41e28103145c0582c50b12090207058003d0003001e0821002d41c021281c0c00c4600c448154059600280e012103844400c0e110803103a400c0d40c2034040410b40e04582e240c003070340020342008289000c90b00c40d9494031144090380000c401d8119089904100d0001ea1038074140200d41c5034425403418046950b10710304074203928041015002aa141c00000d015a40742c41c00c00303030265100441c0400c8250840010300982c40d007003080051404090242c0c070081d076070420600c0400c00d58141508d050b030360300c4001035103454148401c02608088031440e400302440380b9030002d4010b56801003c2402440c25800615860070802811943c0007943e44003402c2d41440c0042140b400d986a404038440c86104c94880e85c5e0311074007400d1980201c64950409800304a80d41c445008101c0400d008512900450000700300300c0300249004441 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 955016115 1250 955014865 955014869
    0x11b05030c0a0e0d082a0102120703050c070b1609120503090409060605100305150d0f082a1b090705180a050a060302030411100207120305040911090f03030301 70
    0x120081400082c0c000380c01114291000310000b07111924000e02569556280c0d401124405e240581c0c90825000c40c40701503046409883d00003000f5410941c180600003441c400041a0384205078407580802c01450704002140d11054000401a50910f0240e032500d900318144003811000403100d042c000b900541d0b1911034201c0d1607010b0b02852409003800100700141051000c29030b0250381d030340c41c001490340d00c0d54000020310303202e500c020441d0310784007074502c91890080d2100d50040030f2070a9064002603a02d56220305859104a01c01d888044200d800d0510b40849940d18101c0100e0103e150100784c80054060745a1040899001d0b191510f0424005004800e41e2038001068040c00714440801c1c905c41c010500c0c01002d4410304200784c2d1074000400742d40c0710341e2021000c29170000c00e00c0103029880c20ba82280803400e4841e5422000e601c04020342c2d45913680700718080c80e0268610300081610030000c660081c00d90751020310503450042c0c1c15001c40d5000d90542c9200711516560b030a050b01b804815641 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 955017365 1250 955016115 955016131
    0x90606010809060c030606090604060216050906060a030e031204031d01020a0305092403100501090905090703030c050102300a15121a0c0915030c0a030b011808011b0503 74
    0x3c03d6141c103c2c80c81e025800282090742d1046042c011101c1c1a150349001c1c1c40240741ca41e000741504981800200701c2d00840d034000d140100c00407403c0040544402d030849816100c2d620b0002150303455510400d0660250b10100203000505509000a041c0d002c0380c00c5001c88507100385640417585940040e6540c1d441003100901040050018200c20300e050202200904080c10f9a8403440c8800b01b005c0c540c1d503008070381c83c47c80916001010300665070301c0700b004000391070b0f151400c101d2030510b0031080396195810320004080000c80050481044020f40680740fa03005c1c0c09999a01568906038003400c0f210800104002007002900041c244481a0041d40b10362006000c0940c511410003800c02c10b0200c0f925030a0320061803082c061290020f210303c4003841000e1602042d601d60f1082405c22034a1250610a6400d401041c410b20450301d868901303c84041c91103040c001001e5011000583c0c09614000d4154401f80c60100002040d0350706401c81c2d0a407002300701c8041507502c0f140f002691140400e0744c00305 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 955018615 1250 955017365 955017373
    0x207050a031e0c1202031209101a0a030206030c040e010605090111010b0a0506090103060308180a240c0606080a050c0301060f0b0d020a02010e03071a07030c08040b060a05030d08090606010809 84
    0x12020500c41c1300d80501030001c40c416030389000c100010714403c0070802d4521400b00d5104c030b00360b0b04284015220b054601441411440390a05600c4c002550b070541da800013030f00c507201c00400310f824202c03640110b600900354400d44514035a900c2d50040c01c8c941001c5501e601049507031100716604801840703201d44450000b400600e40300c3c104000d0001940048a6603418565511000b00109228001a100c00503001021200e2100000c1c14400c0d140c449504c014036000c0202560008041e41043c50b0784003080601d0301c5590700d03007e81000f002400540e44103030301074002c0c00c0908080c001d0108912040c2c50041d8002d1014a0b60303a04050200710003803043d1454188180031010001980d03400605550045200210b0000168843d09045600080c0102d51903840c071031928480600d01035030746600c0402414108080f41c01c1481c0034000c50760040c03000380400e0030400043c100b55a000602d1016210142c01c94605104a00f00038010001c19150303032920303205680c001141c640c450707002c05203d440341e40090 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 955019865 1250 955018615 955018637
    0x603050c07170c01020412020f010302130605030901140108150f06180402040f0615020d090506483304030c02030a0308180703030f110c040207050a031e 67
    0x1910903440282c8010b00710384000c03c01070304603c07000d00150004d803513001804880c4c00700c944108900015195440c1c0c0c141401841105082d100c02c2c92190110b400760305020f9501d079216004680182075103000e0f80e10b43c0c42500700101d0b80900008100040d26244002401c944d2541c0110420f0664115456a03100e0307904030f0b01d85204400b1000080d00280302034401310300105036001c01d40c2581d086400810100d4041e6802c052059410040c0c640c4020550520b48601420136020688902c160245030405102a02030030400d6140381c1000030030b28042015603c01d40744c2e0304420002e000b80c0542c500010703124402450303040500c2c001d881c2c0030503407942d9007940641c03181d05400b10b048040244143d0511401080107400341e00d050082150300c41c0720340d9900b00645400840440c218000c680c50400c0740d40404000d00c00a80c0095840c8028001070410020ba080e044001504c1c0c105041d1926406c20700200e4140c0030042d0005103407100700c2c440d0f144c5142c04081b5111071500001314120050004440c1424 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 955021115 1250 955019865 955019873
    0x3060f0105040e01060b090d0c0b0a030506130507020c060a05131412010e0705012307080a0813030e04020d02131806120b01030204020f0702040212010311030307200328030305010603050c07 83
    0x300c1c00c4451190728001b80965a4100307140b01b2f504210017400110740c48100704440c51602958165244120010400c40c50518800095603540b5800c0014010400007444040080c018020380304040780150000e03455a488800ca1145001c07985206806507010080303084412034180140c1014075041320080c00c103513203882c00440b5000c07a120301002602e206901c07029015034411008203034242c040d1a8040d91a10700c0c0000034800c2d180140080342e000c0303442001c440000d51126206d003401c4011140541c0b1190548804c000a00c980c001c400c012403004a4009510203003074030f004200300300c543c1c2c04101865460328259450440690024030400d80400103000500e41a40501400d00f000b25000e414800c0f690702060480e8020100c4610810094004000b00488000340c81045041900554103007550303503072604203015052011440c100702c1840a1880ea85081208818440c0303075042c5250344800c0102030764061400c060081c0c0000b41840c0010070007900a0003000e000360400c419141c60243c246e22 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 955022365 1250 955021115 955021129
    0xf0306040603020a0f05012a321f02030f0c0c0307060903080412091802031b04062c010f0e0102070b0d06210b04170903060f0105040e01060b09 63
    0x88540c0595109808400b503102c059818014025850b1400750150500e400984104006d000f04400c860100043c50621080e691300d480741150700c222110b91903018102c02c10408404442c0d112800300c072010010b000300400007106402c10024444040c900c0c4807070b412003406c0e44412102c0f9841615244e02003090031040000502000040b80140c0381030200b80c0d90b803a02900c00040082d00020100024403060088030b100d01841c612681c20602c5001c0d14102c40078842c2040c0c2ca800440c00c07a8040300050b042140e000302c44c0142c12a0030000d07580d42c0d80761035001e00750141e804800c08040030260152071488070b810000d0075402e0f070143c40301908040048007ca92585041d5400c030b0450062010010f100c2d5050005496850b21364500801c0450030703e1048003d440c056500c82c1c81c048030455a500125000700a01904560001d4100c1c074101c0155071b00d452944101b4106940500c581d0040203000002107101c941a20002c88040c8245140d100c4018260350300c40c00307010844102007040342d0861900c15 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 955023615 1250 955022365 955022371
    0x150406020f0307030e240604091704120c080f03070b0939030a0807021516031d0603160e0307081b04050f0115030218030109230d050f03 60
    0x5240985058090607546a054000792600404680c82c1d010701852203900f40901c1216811101d110300c10b5a9811302459403035070700903100d940245d50302d5500605102d12003800f004490f1a00f04001d60750b43d52200200749440000000340c5600540702004149c5020100d09c1c05503001e2050010f504010540d241c000249001401c100e00310b100d0040082c003000001d82c4003100790080c0c0f0041c0c00d84090385c000004010345140c03000700e100c6d030404124240011150025600555010380b006091100d406107008118032035101c0d051b220000d41c601404c10583c0c8a0740c81148158940c21000e40102d251f410320a00f808290b031880403111041d04407120681c400c82100301c11400040458405d01e035282003060520910070300ba21450020400c1c00c21540c02c00d4002c00b40c1203141110040038547c500390008480200880c14001010703000514260000c00d080412200740784010000c01c01403807a460416100e800310f0788a4109000c00000c08540004045500700a18425450fa0391400b240c0c28003d0309664001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 955024865 1250 955023615 955023623
    0x150f1210090912020d02030a140a022d011a0f040c030b210f0a0201050d05040303060b0f030603060a020c10150b041818080702010c060905030c0703170c1504 69
    0x104000041c0c890580c0601c0e007000d4015550001c405450a0009080c010444001029580200a0540040d13403103000204c4841c85407401907212081020300b24100074203825001070143d240020004003401c600102184010038000070800e40a0700700c40c00f0074270070351602440d500000c20380410310a810650000c550f00d0703409140025030442041c000601140502c0115603001c501c80200c0c114044041045421258882c6c004200d0455254002032541c0f00b221080058542c451002c1303000c06003e03800603005802031030386003900d401d0f44415030b0250b81c10841d5030354030910842001ca50100f404d407084a001e0480711011300244100d402401003c0c00c6407030441088141607d00c00500f107807401e4080c002611075200042d03c00007510415405842c2c00202c1c041c154400110044006900c90f0100e6505590a0a01800700185c0c0c3c14003600034108201c0152890100042001c55404082614001d482c89080407204844035a0b81d0b110700c5000310b00c4003a02d0baa10200c0c000c8060901019403503401403003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 955026115 1250 955024865 955024891
    0x717010f0e0604091502070c052e052b14010e060d030c020d080918060d060b0310060f0810061505160804090903120c1e030b090f06150f12 61
    0x56448400208172065900d15465001c2041c40400030901c0b05040240303011a94110007801445034403c074052940b480d1084600202c2e00028004d004909880c610303070015109a4402d00e05a1109644804648204110364600031071640700c103000c802c0c40c90696643c501508290307039400007031010b4100c2c5201d082c0e05200c80203070f4001c01aa1440c085100c0d00d03214080702d42c0c44d440a2402e00200b052490807120560881004020203512041d00ca001c21030b400020100701c80c2a09004030341000700350300c500844141041e00c0402e44040740b9a000c002c03943ca50007210b003e203140345a11001c4490b940200001600005a0701038a244114050000701e0301e9032108580c1d8030140da4910b0025405076005c09400c54613080594241904902c400c09600e001f58400c0c801e121141000901c08940c07101039006882d58810f00007505417081c1d110010801018242d0b1a550820500c1420f4104045400911031070204044087c03040c107403010317034824031498059a810805400028540080b00518841e5061a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 955027365 1250 955026115 955026131
    0x1c0b030c04050c180d0f0b1b0a02150109021305060315060408100c0809100e030408031b1905030301030303020702060715050a0c0810030f02030708010608060717010f0e0604 76
    0x36582c07140501406212201e19034072640c01040c80c03084e01c0c2c1010380c14850006203d88002241e8100e03400b1a0007684406e450504d0307074548090500018507074205206220011a1080c1c605400140085102e00e02003240350460381e980c201002a4400c040c1c2c0641507e10641d002c00c400e040c007101441d0444802d01c038a600c00c0e21035002150464110303034071010b010383c000003050186141c144070315403a84001c1d04d01001c140c81c2000310180d44030350074205204000d50b40d110500b81014188183c81c040c01c0c410095030b50300c124948500c41c2c2c0c42c06101c000a0103004511101031030098a17559042c159901601540c00c503840e40c3c60640c004c0d001858140e070131600800001e400206800e00070089002030086c00202418591803140442d43c80300a0740c014841094140a454040381d1100c0d411654404407002e1454100e20200b42007100c0d41d4001d418660810401050141000c102c1900c60001a9986450b100244030300c0d03984aa02841074000550056000740100d000107211503500030340180020405034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 955028615 1250 955027365 955027369
    0x11116080c0a05030d0c03020702090606071109070f020114010e190902100503040b0a06030507051e041b17010e180c12030901090803090616031704050607080108031c0b030c 76
    0x820b10b0411285500300243c1500340e404940303da40f0f07164803981380031400d201d9030b5030228071005006030001d4404e07440450703000200804025a00701c028800b40c841e00300c2e410520350140c50315481e004c800d0055420544480383c0781000c0d28041c2c0c12101c4081c00e4041b02d0311140b0145054803520141c500105869411400160f116054050304886299441c240d492800e810818000c010207404441c0c610b040031810004103400243c2c800a03035604407607101448825021220a0403130b4541183e801c0341c20b081c64a203444031055040d040c1d001458660f5058280d6920707448c002d12409000d020075820100700840c120304880c65072465494444812224400070200c00104540e030380c40383e08400360f400000e01c2c00865902401d040010103008001714200803039800025154041c0c0340d820554106000501e50074180f103444c40c5210300e4581d4414841038209800e1440d114402103400c140824120000003e8581c0700200b240c0c44801c5d43c605100c0d00103034a48102000e0944c00c04da15501d0311802c03009402e26 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 955029865 1250 955028615 955028623
    0xe150306031603030210050f04050a06110d0f0f1103101211040911011209052815050105010305240d080f0c06010503010e03070804090222030305030601020708011116080c 75
    0x998000d80040403241c021ba0300785401d59800a080e4441c0041c0102888002000012545e988662000001c00d031004104010702c040c1c0541907070342090f03070301341404031051582e154001640c403011400700b07000d04c400340e00f14180c1c244800e44901c0c0404150000c00c21140c000c8815500301c50f0f108101d440d008001c03c0d00000c09036540510700340d451940d1084a105290b820840400f04141203450900c008100d90300d502d91246500c2101001d40941d285405000c40d00140d43c200071154800443d260710a04c10125400414090280e05e02084c5000d0101c0c149440140707407401e2246051004400304500001807000354202d040084071090300510002d02c039140407802030642078018100406c080d40c5400109030a403804e02d00d1014058000300400e030042134071942100d095821200025903661000f00c1d61032100c1840100112015180080120405901c8002940111002d80c2100d551310303105c102103822a680a0320041d0300d90350800c09070545d01c0c0c02195805409004024090601c0c01841085040c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 955031115 1250 955029865 955029869
    0x5061c080909010f06051b030c030a050705060606090607020f12011803120207080a0809030910030f051e01140102010b030a14070b0c0607051612030f0c0e1503060316 73
    0x2140300c010403415454104070050310b005120251340e0780c05070751034482d0182c43e61050482c074001d1820450305010203004100201d6180c502200700f100ea444044140040940e00482412105030282c080415050302c0d11030140d038400c0d0401001e0030b00c3c4c44c21990070082104a14030070290044040791050740444404c1c032440001e10050304181c10341d0400b42c640100007c2c580c22880340c0d040c0c07041c40041c010070308801c1507910b0405242401007440d180d98004600e140240314825500003111140c20013020340c1a00300002d5840601c03400d00a0f901c540d0b2441c1c2c0d000710442c007409108003640f00104101280c0203400011068103000000e08002404082814801c614134255003000001c41d145244142c20802c00d8014000b21139454140f6000d600c3e9142c88810240c101d8003006800b24080c55107904803444243d00c50303441150441600020b4102030003510b4205414000c03181350aa03207080c079900a130040d4044082c000e22054461502c0301d24072406400c0901309503050322542c0c0d4040f114030413411403080 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 955032365 1250 955031115 955031123
    0x9130e0105070e091905071202031e060f030a15020706050a0b18040b13021f0c02010917030304060515030a050f01180b2e0b0c1908070605061c 63
    0x1001e2418640c0680010030501d0580d00944d0000d0030040607000d0704142c00c20000d80c2000c0483e164850344800c48041c141c20380c1e8030031100d100100307020302e010400321040d040130b103103810082903645c403c001c2011255100c1800c54154004010074000984c00c41c20214000c5003d00c001820700c0030035110307003080710002c9558844103681c1d40341500141c41c000c03004ad20b06c1c045820400c249443c03d41c2e980100300002502e01c0d9911901d4202141c2159902c69078240d240c40b1071145014080a0000001c200022005080e808100a1400031407200e0b000011940b11011079001146542c0320bc1c2d54110040200400b05c00b203680c84200ca54620b41d60a10420130880d0040c002050a4442d66107803d007103505185201544100340040700f0002403149201540c4a40c9140c01c007040c1442c04041d950502440c41c0c00d10000c01e5907001e01107480800940603083d00c01a440445412070a0040c0b44003041401c04c901500d071610520003440025081e80100b0703405240502000000c8a42d084452001110108111 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 955033615 1250 955032365 955032371
    0x20d02030604060f05030d080712090b150303040f1a07061b11030a20010f0c0906031d0c060f1c020c060a0c050a030b0f1302030f09011e0209130e01 65
    0x401d00c0d007400352101406044075800140c6103800b00090341c82e40d204400c801231003030400000d40424090100329414003000c04c0184880c0d403091804200c164400c4911001c2e07011001c2401219003400000c0c4c40039030380f00303000d182c00c1d80342070040009100103d43da421081c001b0803c00000018954042c0c42c44d1500c1c21004154480603900c00a44004013810480050750320610207501c98170b0348608500024803a00c0c115080034031107842d011740500820b8641e0004281440e0b002d400ca41d52208130070742225400c0d541000f803060042d40103244407820705403000903607004c268001041d1501100510700c0d034070801000c80c0341241074440420780e09240400d03046119408a20880040400c0c85100d50014100c01c0400407401c1681000d0902e0003001d450130100341d45c41e4407410003a16184504000d07814000c14200450070a41900c0d40039620488c0c1e141c020401c0c0001060406505008005100c4484240b6070b650b207024800c114000d402c0032040c0c907031001e800029022200001c0c42041d00d9150f00e04004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 955034865 1250 955033615 955033621
    0x7030905030618030a08062d15040f03080a02070314010525020703140102040504021204121b0b100e04050c0102070f0f03060b3105011703191101020d0203 68
    0x160500100030100c80c007803080f1511006400d40d0100c12141e0454941c1481c40c42c5441e280702041000c1041824281030320f0f0b140713151358a00b49002152082c9004111a40124181072299810107801140300700620281a01c42c280000f520030b0000d0803040c980b0703104987d015583c9454000e1001d000c19a1000165526020b01c18007440188924010303c2002824245100700e03080029610210352001038900008810090304040c820340440e00242030040043d51601440b400980f9082c00964088a00c0c0380700d1081c28400314040c004035120800728910740750380c50308a5240c01c1000c01c4000d2220160841080d404240a00b841018500490141c001000309089420019103000c0703458020443c1d032800c40e181081240316118550003030700da0011022921144000106448168400324000c480e01d520841140240c0c005000d5881c1103d410310030302481c6d80e5034501d00111100050650660f400400c003a1401c0482c85000c440d010010b4a00004c9603006080d099007247c1042703205003076987e000014 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 955035971 1106 955034865 955034869
    0xf010f0b07030e04111b24040b04030e01020c0405190f110703030e03070f080d140103020f0108090c131e0c0e1003060509010f0603180519140307030905 67
    0x41100301b80310004200342c8900b0044404820321803021040f00800c91501c8401d400341da0010307440c1405403660b481c202e07441714654540a0651248518071411a02c0b1032040a105505002203c1c0e28092854159800c3e544c801582c2c101c5941400c41041c035100d1000100c40c0c01b10340c1030400260700403440c422541180111440a008203d20f80241c405000c3e140740200311070950402d08000914184d20380469940342030002030340104c1e140076450074650040851580218080e02150080c9010500041c11034018504082529445da08210750070303818600307190001c1200f002d0510925804480007080c0319601c0003038901c116900e20300d2100c46402684240054040944003079a44e603101c0103200c09082c41e921a1070006440e00901280542000003040d011075030042c058605c29100400e140503211031080e082d2a070003681c1079800c44000040006101042c0701e034544010481c07402c03003 = true := by decide +kernel

theorem cover : BRFrame.Cov 954856115 955035971 := by
  have h0 := BRFrame.cov_init 954856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 954856115 ≤ n) (h2 : n < 955035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
