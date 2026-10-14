-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1840
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:52:05.876492+00:00
-- url     : https://prove2.me/submissions/e6aee89d-9152-4f27-9779-833b5dd897dc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 330755395 ≤ n < 330935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 330756645 1250 330755395 330755423
    0x200304030918090f0311010608030c07150c050d030b0117040503030612031306110f010615050304020301020702090c0702040e010c0e0d0f02090c0c010c0810120c05030610090e060103 80
    0x340b9200d118403011261000001c1c101d21954840c0c401c208808001e42c0010303114406554607200910405010f0410f840045007002d0802d1901607440b8003a002c1c400b5034000d40803200601c0d50090941e2480c040d88582a11021544c618005004001e000005400141c540d41820740d4001d414000b14000c58001000c0c5103141e031042d040c442149006050003c00388020000031a030b1440801c14000548429541e40311200c0000c0600c40c80c086400580320140d03407400c0010045103692525041403809941450398030381c1e94a0000900a0180c1c00011b0f410541840801030610541c03002480c29a200b11410440000110029400c0301c1d803e403494404036400704030740001071403d04a4800514414200b4016091940d400700e104240284d03020411030002003400880c240080c02502c900150302e18003140d1a10304500d48403042d005c5171040598004900d001071041c4030320000d1400191902604032105d82c18039004020410100d486184846272828220200d00e80300412024101c94110040f038070060 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 330757895 1250 330756645 330756659
    0x703030207030207240e041a011d030604060b120a032102041d070807030902011706060c01110901090f03110405061c050303100618030303020a090b04092003040309 72
    0x1500c6440158151310402a001400c500314400101034008090000811941e18210240c003210f01e00d140244910700f41075005010f2001000c0100ba10402440c1940c422865645d5010118155503c440d816000f8107040005108594004012201047e1144c43c01c2155881c00c603602c402d11100001c0008410b00c442005e200000d90720901e900c80d1a510051620b65100740f008075082808242010354001c2000700f1103059040307259994400f62608003800740580c03a5000030582e00d00f542d408003117084290040382080d2100b0f410384039181222002003040300c01d0982401c010307130000942580000c0c40a600803600e64221607002e01220b07840548034442c620320000300006040000c11250704500c0510400810b240e00324403a442d07481c0144d0181da07403410210514220f4020541081c2d09101c07800307034102ca85071442c140e2a0101d0350503140040e250003044030202d81608003980503042c40d00307011401007503c5465610110710a1680c2c10b1880d1110242d0304401498002294050041070700414100066 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 330759145 1250 330757895 330757897
    0xe0702030a120c200d02011409060106030f020c0d18060201060f1202180f040209010905040308150a080a031e030b060412060b22050702030301051c0f05030a0f030609020301060507030302 82
    0x1101c0c0728109184c803180814140403040c1d03a4450000b01513400f43c500c41d100c668081c4250346200c0c1070590032080501d04802e0a40d40e41006104050070181e0b2600c642d0010300c81c82c0d069864001740c2d4415035490400340d0500414101c0954441a031517408407500040701c1e070051141c40121070a03410212086842c04034030480241d4005411703a0004030360391002001d0005400154402c8074560f00848840c249170050000500e4160030400ca40e91034401804086608064110780c0010244288010510310001040c1c0604650784412107074401c0b071a4200030980c11955055080355000216018104140030032403d503125007940e02c1c0c001c9010402800550480d00030a80d44500542e008aa0141c10401148901040302001e40f02c884800e10080078540c02800760303a40040d128070055040d5414074001514001e050210349917811840c1e6481400c000340d0100241c421038000080c0c0391a20071141c03029121291b14281c07140060f14006c00030031444114030170f6a040e10303019070b103c90400e9403c0d41e0036402 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 330760395 1250 330759145 330759161
    0x414091e0a0804060909060603060308120a060302060a2114160c0b0708040201030e0c0303030601052203030c02090106030504110918011505120106050d1721010e0702030a12 76
    0x15005440701c400104440d0303001000280050380e40c86003150f02c2c1440350011076900388c0280080605280d030402c0402c2c54407003074030a000302c0b404c54070301140c403001040c000501441c0d00c001e401110210703c100c06140c006009115881558000034601a0300c0c000030800c1b602c01541c050f0b0310b907001401042c211303150148140790641050505400020f0541c07100ea0650100701c58100c0005c440a0410045503418003501d20142e1556009000710b40f0800700183d220301006105a04018011608811112100310000a413034a43d85000d010240c59040042c07951410403810303806211082e00000e403081c407078414a0712540d0420014640c91410703200300040c0c080003901c01c07040e8841558007600c03100420711407600040c444166505596180c6000e22a2298181c10750303086a0b450044100180d880301c0b038030490010750258030007a081c00340a240f06441d004801203001340340e0081080c4600d01e1800340a00341610024091080207079501641241d0342d100c0c0741c400d040050070082101409003069002402 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 330761645 1250 330760395 330760453
    0xc08011d0a121b06060f0b030f0604110d1b140304050a0f0c050415091518020f1e09030106050402040b0a031d0a0c03110a080307030c0c170a02041409 66
    0x114150f140c000c103816212414805852032a41c5100401030700f50a050208010403004039800d0030751419019004500300002c001d24040c40e1180860090403038028121036240c58890720400850780114001e004289a002e85080800c0500001820400540c02a13a114a52040c000d00c5c101119985004102100600407603003001c40300f42c007146607a22806a0b0095046040032819500d00e03010300c500695880b42d4450325000b504144c03d004014020100603203203100c855000d40d5504205048038842c0c4181601c3e011b080ca0010b02d2030309491500001441d034024100c1c02800380c15103a03020072041f885248251740003c0c004100030810a4002c0e00a20320303042034102040000482c0c201c2c00b900703101400300200d0382d00a6800b0240708120704004582c0a2040988480300410f00300701d40349503070348213400c0e0180070700c108688103100300400300e46441c3c054000b4035090a4907469804115990b8407048000b01e01c82ca0070041040508040020070358405e40300000204284901c0301440000b4520b10141c50b2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 330762895 1250 330761645 330761657
    0x4050a0b0a0302040510050a1d0a271104090b18070305040609060618051509040b150307060905100305101a0d11090a06020712030e06160c08011d0a12 66
    0x305581d460114050408103502d47d240d640d20414002051440b02d0030740c0c20482d2899170010a030315207a0740d03180300944400d2848203007010b0b50540350503000c0c1c200425a4042c10304001030540116464805003080302e0704040d0901c000074040c020495800001c5c80140c818040440000d2301e100d100741c214a4005001c0c150020f040041615504c0030b0307e2054101d008000d11120a41076960752902c0749a901c44586500903614a40d0080003035454031000c0c0000d008010008040341484101e01181140c0c503070001e04640845030741d0100600900020300c1440d2103180004c0800341c0c0035009005592003202c030304034141d000e42e080004408156540460b4a40e88403c00d01000030480b01d40c1c81035840d6030700e55017800340d25284501c00300400003986800080440d00b2481c0104010a0390000300084294907090600c03800e0008008201c040c09401500301038489100b22890034003030201550340503103030514005d102e00701308848455802d0f9a002956204ca42c44000c0202c0407034540c0025010844042c42c01e0707 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 330764145 1250 330762895 330762899
    0xc080708043801080327090105220e150702010c02060403120b04050112020306060114090d03031107060905010e03040302220209090f220b06040b01090503100212090304050a0b0a030204 81
    0x40b000e504801d8002403407940c0300044040b0846c42c43c500000203001d900d0302464420b019440840c503550410302c00c40740986600d540360700c1d601c200300da028030224030440f40c00c00c00b660a50780080d035204880e01501000c071f80d5210100300154418000c061190000c1c1d00182583e89a5540c101d80c41c03045151600343c220f0343c8510000b02c56640340102402001164007014a000050040604151001d06001d0511802c40104407114900f407003507411000003250198140101400d064004d000100d1242402800020b104400c1094542c400e1450a02410080003208064100ca540e41c1c0328501020358000740c050100314140d001303d504a940e642c991107000d4102158040420307c0744009403020b0140884134010881d002c608480c00012240410500ca007600d2520b489281c840f00d0702802490040d03840d00b83e050901d0740221451002000c000c0c0403a105066119400c0c1c0c0250018a441000900884046000c00d5000000d84041d581c00905510b142d910b40340391945154000707040300092507005d01c00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 330765395 1250 330764145 330764243
    0x170c0316050d0903031b0203010209090406090b06150d022503020a060e03040b04050d022202120c070b01061101060f090e0105130c0501030e030d0204090c08070804 72
    0x24202444200c036805412a600d8030307200e410864000020300420514400420209611441200c0484185180090344c100c4034004603000e841405041d5070403030100c40a10040100c039034002c0b0400c6018628640170364541c041006404001890f00b480c101d00d0900441c0165035456009180000450880d100003022114844000c076812940650241e0020200c400c144030b032500500c1c8421000c180078515250070048100924000d0380030f494040d82c00d148020085440e01c0c20307600a011f80c45058100c5d90b000201300400691320000300c0300040345441010402c0214520305907400703039a100360703c0002a1f0a1410413a8258040c0f0131071215503488402c0080c0c0c181d000c01412015180c820740115041e030310504c3c250b003500c0018011825645814080310041140d000c040010b9450074030b80451038540d200011461030080100b00710841c0c0c400a0000340c10f403041c3c1d0100203001020385407000c15543d0031000f85d800e20030496001d0070310b41501e6100c05090003048000c0480003000760982d0b50030004064 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 330766645 1250 330765395 330765397
    0x61003090605090a0b0a200a020a1b14060c0307110a03290601110703060f0f1505040b01050c0304030605041712060102060901110d0c050c06040605190c020a170c03 72
    0x280c10020384c01422121003401102501035a212407060414440b08900500201050301039540390500f00502088541006200b800707598461038000210f4072540c3d03010641502c2a0703889120b0101d5014400c4503444107401c0180988411108110155040c40700c0d5498880b41e00c828480f500380d100312413940100020305000000c0d52903540c2289525031b00701c0708140c07490010f000035000318103011a021115890b074200080f6002030b40c1c0c0c082c001240c08103000321041d016000300c00202007018200101c2003120b8a000c0d401138120b80003181e003030054615100040d9000d103d1040607450a1b0000c0000b0300104030a5004950850300c144900d4102ca0b0040316100103540003503150078580007a282c18000c2540c0c2c1000341c5030300684604000c02112442c48100d2845101d00c10394010099218100950443d0280c0181c803c450003010507141e140c501032404a0003031a04480070100205082515100508544201010102e0360340050000f04101e4648074984072004034141942c030000c0100c00c2241c88240 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 330767895 1250 330766645 330766651
    0x309031b0a05060a09020d0212010612050c1302070b0c0906090d0b0a06080d090303120e0114070305070525060e01020a021b120607050d0912120f060806061003090605 73
    0x400307411505070314944a4107208028100c800034a050090f450701507520a10902d00d031030307411100700d079019200f100c403d0b01400b400da00005520030006040000d1220116071031321141c2085803000011100035070b646e0200d0040c820f000d8924000c84001035540300d41c0310f000f8008040c00408440c00c0004080028000c0d00440c1c00072140781c40070f5800d00554001600405001d850100d018152540f006c0c04001c1c181c1e0003a10001e02002001c08240316101c070f0307076402141c8207450440203110b00c04080c49440744440080d00c0d4180000e00e44800660f900d0722800c00e40d546804052214a500d05507004050781800c4400400e030303842555501c0da4582c0f00800d20007456104043e4024101d60141c60860441268400d000c40f0301a8030009440c2c0ca00000c045035003540155181051515a441605084003e00d40d2040042c100048280c99980040e04490341c008104a03005050210005c1540c02400b5244103200d0038016500031000b0039403d19050500d4420b0381102e1078000b59400a68441c41c0c02c0d40c1050f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 330769145 1250 330767895 330767947
    0x8030f0d0c030606021b01091805070929070809040e010501080c030a020a0611120409020910020d020c010e121515030607080129030702060702160b0906030903 70
    0x19041500c1a5030301400c0702038110381c10b0801410307140c1a400794880c0f000320310740400c050082d1400c0060340c0c001c0080d400501600c0040040c620034440140700140429500180490110040081c000c4110240146041403034110303103269040c088942403850300b0480b011100b01c0424408051251507074440c04000009060003c0f6241d45005882070074020b1440046000c4d42000d081480583c480203034800072940c0c0d03490602c80100c4079000a40c00c0011401d0104141e000018000890072041c1d0040c0c00c0a00e400c0b540c8600b510144041640d03501c00b005540f2003d0303000b03414052070b1036010710046040440c0141035124550b50b20708080341070a041c4d8030010b40c8180380500303100c0310800c501da03000300b4268240e0080c40c990500c0c020182c8000d10500c40c422001000e440078984034846543c00185e01001440415102d0502160194a802088407200014420015409203034688007e1a8080300e0318180060702c0e00c1410b1050003005e601c0146008000c1c4010030075034084081540311409482c9507 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 330770395 1250 330769145 330769147
    0x5100c170910050604021204020904030201060512160b0403051c180905090105060f0607140a080304120e1f1413030c090b190e13200a0806070e010c050708030f 70
    0x45581d10403c03654042e020300c2c00b940c41842400b11800e40484c601d41c019804607001046540e03989000c03409820035070001c0e034110b80704800c01201400005221044003109141143c81241c80c3d8143c5082409140b1001c2c140781e002013051181444070003d1603010b01210314017440c0c0f40300c001d085980c2940b850743c02030481c282c1d14000c01030144801e201d081d4000c42e04580010005003c400001c01d01e00601030050400441c200034805112401c1141229441d4080d00c05a100c3c03030a418441c07044460411381c80049803021882c0c954515005c1c00d80c003003400d41d040c8150000d9902140446218108a8181014020411080d450b201510003c03034000c51141c0300309080c0900302241007040c1e07805070b56402c0c02001020308001030001903031840d1090704c500011001d840c0e95803121004080c50840c50150a003000084654450400d4201700c0c20341a10032740c0c0003189191380e110019075918003200c10200051400803120b095601c20001900000e008004071241035456260090071640701c10118400020 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 330771645 1250 330770395 330770413
    0x3120903031101060602030f0d180b04050c04050727080f06091c0806010302220602010501090c050903061f08062401021b04020d060e09010902011b05100c1709 70
    0x16002c40c1d00c220031060940244002454018040d560b0302034481003500340c250100d03125055160301d6100b564148503641c42c4030558100380c18800711884055405036561f020b01003c0d1000c41c10680615400765000c1d07640c2c9442418400200c05d094022003501d01d01001d1440000204450104030504003141c0c1d41014080a0034840b01d46880c20804070840548440360008501207a50400d00341c6074003c03002e0030302507560017800d0a81881e8008003903240b212190a0300d000302d01554158401411b80e03051010422181c00c01140694442c010180900d038158012000616600d03509a01c145445445004103880b607600c0b06800360408100321842c250214081560b01c243d080c00b5007980600300c20030700140c02c4c00703843c030004805520100b594541c004da0f00029011143c101c01c3c1d026000424941d4a002c446080c812041070103051007000c143c0c00078070201150300d140740c0c81048920490382c0c00b0700246003d074044001580a010070900c01c800380401ca0804131448000410502e115440c04000b03840700c91 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 330772895 1250 330771645 330771647
    0x4060305100b040e12040b034201030b060915090616050c0d050606011d030a0f0b0a15060807230904060f080a0305090d021c1e02060d050405070312090303 68
    0x21310075424001c00303a80000041424a201d000449041d00d40029925a60b81d8594052441c20140e003003a038561944800c0c0c0000121845166466100000d9010132003075210b041d0046050f100d6411b000c0780d00c076030b080103014a149018800740750560108144681099044000100035800544002510110407401c0d4070810000780f040c3d641070b0300103c90610003141c0544803036a486070000c00701818000c1c0b00f02480d000d800a00301404404100500b100d41e04540e1f491304031100d0b0210300c011103004a49a0101c1c030f031004140a907003043c503400c41140f52414607005044449060280034102030000705028100702c50a003200d9850a441d020b030407503584c0d44086041c4030840b48154460808900c8001040c810712402140d0f140b8960b4040c0b038201e4942c107001000401407451940e0007503014460280c8500c00d06040000740ca0414090f44522076100310014641d04070f01c0303070000002c4d40a4410032032801401620361080e03410030f0240c002c680d9102c3d1242c0e0743d082e8010703124405a01245102d0070030400c01d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 330774145 1250 330772895 330772901
    0xc0b1e1e1215030105220311010c0f030e03040501050a0819050c032706011215060603050405071208070b190e0303091605060d0e15040807110105120a020904060305100b04 75
    0x415040d0300030044d51800301d07503801c0d504941e00c6e4090028528a003007101818030904100041940c02c100800c031075003041c02c0141100b82480e4005000c0380c1800003484940c01c001c400d440031500d043e12070750f1816090803000c580b4001c008104c2488a00010b01c000709140b030600c9503521510300b640b4000d0b41ca0402c048041c855a140c1785140000d00d24000150042c1d103400300d500ca044607902d144814a200e00e41c5800800007164558141e09a86048000a20664142c000394040e40c0103d003940c0150b03868903e18400c1803111480a00182070400500c4001107501e90a55842450200003031a00400316103900e003603d038a1200700d0f00c84d0b030011050210010052040c10b0b042c02c901c0c1c2c40301035118a4400807950074000e088003000860703991400310780e8030041400240f016581c0040c17081181d00c1d1601d402c2130b4070340040f50142d0b505902c80003450001d5024100312040441d010302e1807402d0b9540d15103a44060742c0002c02031a086500d03003400000040c0c040000c6c1100048040d404240310140750240300803 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 330775395 1250 330774145 330774181
    0x60f0402070f020621130201081f0e071709010617070302030c06030901230108100b0616020f13140f01050105120714040605070c0b1e1e12 61
    0x422441040180700103a0050003181d940d60381900c2642e1582c481004c0340f0f00d40c0d885400f400030071004038010406111600c080000c807441c400d807507040440e110404250b00b400380d00203c041e48268402000d0118800d0070040c0e580c4604103180207512175202c1703551152404000e5403990704580d107840f014002260f01034201001c01980000030100d080c91600042d5891410201e00c0d4017900000000c94248002074000e091410014021449040c07090703a80304041500900c20444a40103a00122081100e0382c05050702c144001010b807800c000c142c0001c031030b002401c0c4ca8100d80c0564100006621074a0f07084525414800ca1240055001d40490082c402c409000301041604050080180001e0703030441d09843c00d401300f030203d0790308590701c40c40c05894054054032b120506040201d40041e19a6001c00200300c042d11030114101d80580c1c4054440d901e024001036905030760405003074481c510305000e000d0900d04000a600300c0d003a5011070703003905560f403001c10701c01903070000b5001300006550364100f0204d03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 330776645 1250 330775395 330775399
    0x3060b010806030c0310110903030703090602060906040f1203090b010f2402150a23092505060d0219020a020102061005010e0f010e2206080708030304120203070c080303060f 76
    0x25111301c4200026280c00c0d1040d00111410b0381d944040005041d0841996884c481c06421203a6440e520700303011300751001d64411080180b02d001d00050030f0540108100d4000e56100301508020b1000e580c5040b80018804005001c2541d244000e2000c9440c20407458001c011009007012000e062012420f00302d0b991001e007100300c0030500060340340b40c1d0f80050501c02007441140c0041480d25a00f036404040d051084400c0300d1502c040310845004e0f10807001c078500510441d02214084420081207821500603083c41841c815460481008242003010007065103901a1100516010714034882d9040b240e100345e840d40050f0b00010b00c40085580400100e40c0184950418035501890321000801c4c009a100c1c0c2c95001d4201204890001d902031924400c49039002009003801520f00504241c8034200c400080e25200e040050010f40c1040110701031043e1880d000180d0320703664841d01d03901078141c211042c0c41b00310f200c02c02892001c683c2c0c1d80c0001e0007403c11070014580e42e080c0001005403c0400046542c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 330777895 1250 330776645 330776653
    0x170c030a0b0f06241b0d0e01050f0d1109151801030903091d0f071b230313061808100905031606150b090915060f0403060b01080603 58
    0x100120740003400d5550301c00c0740d400d103081c1181c0d91140440c00380560002d8825100c1c1c1100d48000065803090090314100034018034241d040c5814100c0d00e40d90310000020f030301c0801c4078505440f0055200e10010400c07061040c800c14034083d0135400c10b004803041103d0590100c403000c280c00703034107241240030301c2514515a0401800c040500204c060b041502c0c0c11000e040c10b0366000c007001018010700300f0000074a1030741c900d06203510808099484d50101121070081084500000800071800746003104810220041c81d486402072513651394080c429640e103800040340208c05501c03001c00080004100e0100380ea4264103840f4600704018112920100b0440d4030b01410340c00500440340c001958400e0221110004541d0f14030701c2c2001800c61190040a04604010301c00d101c061004a401c000703400c407a14282001302a0ba1018240041d0140b91a00c0b540700b0008030204401042c448006559114020b01651a110300b640c03a143d51603110b944116407540d01c0f03105070103a80d80c208a92a9001000798058 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 330779145 1250 330777895 330777913
    0x20307020d0c02010c240b0306070e0f0402040512030706060602011a061e0d0603020a12080417151e070c0203071701020403050708030310060302040509071d030106170c03 75
    0xe92500c0e4540803400820105890010640e0301c90001c4500701500200c100046010101400020f00505400c0303a80080c24030018001d03600300080c4461080409544812550004a00300300808010b922901e5100c0e400b8003012406a0300c51003e55026071041c0001d60b5070b10304620304442500c040c0d0f44100c00356450700c0351401900f210b0b220145a10407040b00e103166502e00120412200e51400940a520b07900045154844c5031840e0b4003010903680211229a00d42d66102d030b03581e1100580000041c40034070248402c00036428140c03030350443c0360f80c88425944204440700c00040c84000861380b0b40c80032031014956410a00400d0341c0340c0d030004801d141c9001004990380100f13036640ba039485903225001700e1142c2005100320a5040d10055a44003081da00c0c03a503956800c07565240c0040d03c0c07010594008500004019004e8802c0700e085802c003505441d416070b1411019200d4a030240d4680844c1182d04880c6500c0b96004e1203528040c100807084030b20301c809007564040c6032109100ea403038000d41c041291 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 330780395 1250 330779145 330779147
    0x301150e0c0f04031103100c021e0102031605070f0b04030c121e0806040e07180c08070c110414041401050105060a021e0f10020d05061f03200a08040510020307 70
    0x458044d41d4014400e40f0038403940b0004249050b030540031460419240c828840d4000c0d034041103401c00d480c08000c150b0480450251072900300c1c8019180c80c41d0001000c1c0c500d00c0d506025002606080e80200c0c2c4840403440301c0d0f01e90341c05100080700c0c1100040c40b42520781d01081542c0c3e101c40c5001041d0b1810440b401180c4d44d0b00c40480e10307040884018040c82e80002401641e0340d4004040508039901902c1503e41c0d112927502d03d00c0b002c00d0480c0d4843e414003450203070342c0c0d10400b0300c18850203996440c4298880d454417265108060042c445030019120007051070b01c1000300f580640106d01c030b01c00140310740d64080f545908440c0c0c1a04200d10482c010860400050360010f10000400c0420036280c2400f5070000001c1d20701a00c91901c8161800341040741c2900001c80e42c0941480f0b012030313009002e183d88060802494241c01c0c08404804022107083c928510301c0b0b0380c00300c1700c00c0c0801c60070600020801001401d40303421240300b1b0b80c00241c001040100b0414107112540703100c0743d103d40c190300714100325030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 330781645 1250 330780395 330780397
    0x40605092d0906061c12110c100816020c01050706050a060b0c0a05070602030a090b1312050d030e0d05030703020c1e010b010e0a0b09062803091412090118050301150e0c0f 75
    0x400e100407c071070031070500c040340814032001d402e50a0041491600c80c13203000014103154012101c0444000c41002440d00c002e00114034922402d00580d6018903040b15642c0301802024044c0411007419542c03400807a803405158010050100c912004040440c481e21381240350841580140c0b085400a00075401e0003030f0059141000e80306c0c041880c0703440d4078004405d112000543c1d448102c1180a0390b040320309022006c03412002c4614a96818081d0005840751195901c2807071380c960000803400c000045120f8880c5e8040c129501c15038060b034024059020040703008812140c00313140181d40d42c90041c81103680001d002c0c0e03007002c810750324403104601d41052444680952001580203003c0011070405603d11410301c036011101151040f009164080360007030092941d082d048400340c14054a0a007811400076011a00680c20001c8a01e443c0480740111350490718000847d01c2c2c001414000300e05645c00b0b010b440e0039417103814100080c807858207020600c2c07170070040c00140c2114402c200030020802000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 330782895 1250 330781645 330781673
    0x414010306380111030a08060a080316080918040605070f08010f0905100308071b0b0c071412030c06100510020601140604050612090c040605092d0906061c 68
    0x8449101c0903030b036100060b114040f0649081d005400000754490030582c0003d42c0354000d14040e50340c500d410340c846410340d03500d1141280c25020707030001a4070b9500256040c13000b0640f000c2c0c054411014021100c04020600f1019030b802c41d8099240c10400ca00d40d94029880124a595071030645503070752418443c1c540c205014001c2804082d201c40001d5140c01c1c035824601e0081d40d2040c01c0c83d54406440c103008186007000c01c2202081c841d04d500000b1002d00c460240ea00c041d207050301510f840d510b0400111000f4010182d80703604050581c0860000c001c051011b4680800a90094111441c011180da4614100c0350070681c45000c420709010740e9217500082042c107681d40d902d051850100e0400008405004560019030320850006880001c0c080e05145680150030341400c651b41000306001300811748803140a040e40044801c800140c1b071740044800200152a00030702d06900c218455a60803a14408076440c1000340c0c459820b01c01070b0b0924a40e1807500700c0f440007812205002540c0d6641e00e011280c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 330784145 1250 330782895 330782981
    0xc030b0109032102120d060e060402031e10090f0204170609060a0b01020a200103050a020c0d050304151d0f01060b091002071e050f06040f0b0304110414010306 70
    0x5030b840d9918034020000c0d07004075000a05c03100d845620a008042c042c1180340102e01d201003540001c40c10a0a007070080d60702441590001042c9002e0302084003030302d940b00404c3d01001c4604c0e0703000016426040c0c8117400c1481d0503100f0140e515403d02c88a01c001a10b0031803100d500794000d01c2000480c07000400d5035038100e04150340120300d1900143c0100c0c07170508120f13009440c801c0a001c800d8150440402c207240a40b200f0789051016aa07a00c080340b04a0060520038074540d00060340f06c0600301d10560045511030301c0b0742503070344210701352040710400ca680401c0c1059100820f400c150810210401c0b22000e140c41401c001c2c0308650070304d107500c8018098014420302907941c801d01c41304098000c0c0081c00c0a060406500301c401005a4118015040c003441460b0064422003001d28007814100116001d5920844809052a00c1e0008400955000a2050f0341c9603c402103904960340c2c80380174509041801c070004406550440c1880c10880c2e400c0382c1c100c1c50300d05116420618070003036070055588081c98 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 330785395 1250 330784145 330784193
    0x3030f040303090512042d14010c0f0b0f090f0312061c03020c01031112060d080708030403020a03320d020c01021c060506040e01030618150c030b010903 67
    0x16a00e000c0e409441100340082041c01100c0c002c2003811414000b1301300700c3d01e2018140714800c5080e00f5000030200702e441c0d1f05c0d030310800c4610188038014024500b102054018940780f40480e500c0d80790036181000b810740c02c44a0040c024103000441103481921a04006240c01030b03c036819070b0f011503507928031610380b44076103c103840c0c400500a81d6a2100070f51600c078000305150780e121514a8003d440c1e4104013107041c0071a14004003d000c0340d00550070384201c4c0c03005a481c01000d403100d4041001c4031482203412903e0350810494000015000c0015601a0344070b5001400024050700d805010b502801c841c01c101c9600c0e001601c41040e1840d4584a0015100c030303a480d5940c10614025006441101023081040d03000185611401c402244440d003506078215003000700c0d64884c010000b140c421441009008000b040c0103002040c0154042c400252000a0f0018100781560f10886215250142c0209080d80ca401c00c1440c0764060103411040d144c24640950010306540e1002c00c080c454225210b15070f20 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 330786645 1250 330785395 330785401
    0x120e1806040504111207051c0308010323150915040b040b040819021c0302271c060b01080a0b060a140d0603051f0b2805090117060c0c03030f 62
    0xd610f00b00031003413801901241c455076003610410b03035600c10713071080038014403103401100001c241c10b2400c4914542d043c0d48024140c0d01e951100360418046820244220140d00000310f00d600c0f08000c15004001c811710040842e14040c0c1f14103007081e00c40c1c442136090400b0380040100040071030010691180d0300107a0070f0407e450f14100500c050140210f01c50624280080b4503039001d400103656200034000781d0003030b4403000e00e0355800c5043c1d0085881084040028030070140e4001c1c240c1444031707801e21014082058103050002a600c0c11041000103907801556250265040e5902c075210940c485c4c20314800348103080810002c00c0a0b44190b00b065401c0041064080900c005010100c40014a0000c801d1064540f40d0504544940c4041d0101c81041c0180d151001c451580780901e080d0004010111080744460701001000708110a0112400324001c480c04600340d0340341d064550291212504078078003403040d02041131901c8006402e03045901d80502445481480000480750b1002d464800520191 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 330787895 1250 330786645 330786653
    0x90d05010b060c010207150c08070c1104110a020c03070e070c02040f1a1906020a080307030e0708011a010c0203030d09020307080d03050a050105010816050c0c030a120e1806040504 79
    0x440642074260b48184005030601000d80150083e040325070041c2c1492040e81c035401c40e500300311030180c03e80f03002264408000440c054056030340c0303401c0a4060591950840e036130303400040444000380c000581048000c00ca5002c8154108100002028190014000e80f400c2683d080140d100051800c01000f850480b0603003152503d41150b08400d245d8002884019604056001400c0e01458624000c1d415030b00480c1144601074800c5003210100e4003d804001c07065103c0360b40603070005081c40d05240d151004c42005203c01c000c18001081a20000982d18030071900d400c1901c20b58880340c0341000340070364180c000b694010044422001c3c80110000c2c0074900d0344046410036031254000c04181c010640b95440c0b8540640200f07105031f07601c0e0010069aa00c420041d10f840d5002d4540000d185021917044540d28001e00c01403202d500c88408880e032040c8070800080c5041c48031101120034a011a0110f003182c0e401c800090801001110a50041303482c185200d010f1503c0200428490703515580410240 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 330789145 1250 330787895 330787901
    0xc0d060506031f0902190308030606090d05060928170a14040605030f010b0c0a1104060f030f05010c050a080a0c23070b0a051501180807120c0f0b090d0501 68
    0x183c201455020450038a8a440c00c02070000000a03801205030b01070034000340003e83d00c958142c4e6400940c150841d00c80406005540e08900740040e0440c3e0854824800703d07800f081407511481d09080202000040c0c61f410010140e03c1001c03048030701c43e6040c0403000040000322411914034864400300c0e222244000300b00c8103281e49150740190380e00c0c0010041403481d4448021841191f014070076881590380e4501c820783d030780308001d81c20780325400800800e80002c40100c001d20700708100400200e845600d40c038101034200310983c0116100780d441d40c005d8040060038020a040c011080c2021030030700c3c2c52041d0103481020010302000380d0320390750f1070040b000700e0081c82c0640070458248440c1c1307032000d50f120704281d1070340c00b4000a640070981b4000186250016026080c42200c0900c0110400102d1030015180340011500c8180762084a100102e044801005130400404207510703980001d400d181400303c400542ca0304801034420b4004d070140101000081180c000000c00e0b40c80300c9040c1c04d81d00f4001c4c01 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 330790395 1250 330789145 330789163
    0x20a090324022701020a020a030f02010c12050d0513020d0b0901020d0c11010b191e03020d0b060112060f062706020f0f010b0a0317121003140c0d06050603 68
    0x211074030108110456000441105000b030607540303452000340e18a030f0016079440103000070007075004602c224103000042580c121082d03078601c107041c84074891113665620040c98030500c070075000040010031904608072481c01041d03001642d141c101843c803161340c3c02060f100035070308401074100214400800c114580075811581c15800c40c031720400076407c500c84014480e0764003034080011907007050004c03034191400d0480e9a041ca00c0000c14070341e003145420603540e442e40c5001d09285150504117000000350300c4585a81d0781071441501d0407085840c0030030000d4070858800009141c82450080e05000c00c9228070454010f98000c2c1c2003400300c241c1040090500d418581592070801d5814040010b01180c0000d44440081c01da9010303586502455100d4500301c903040260b180d80040345040410100b01000d04000e149414040e80034038090800c040c00d000074801f03a8440380f2451040b1005c00c14043c815020240c170907a18006001020440000144403454401d03016009039a914080340d080da6080102040d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 330791645 1250 330790395 330790463
    0x109050904080f1c0515011e0206011401091e09060807030804090506131401060f0315030215040f03030903050607080609043c060e0c010507150b040f02030601030b0103020a0903 78
    0x405c13480d041d4501201c1c41058405940820706528079824403121008101d0414080c540c02008a60b207449068000034020416103418010080004580114076030000f03c203c0a104011003401d600e000451030440c0c02c294404100c0e41c100010a00001d040c41d001c40e0101c1c0e1890317001091640355580000c414085c40240040024508210b0308100c072004407009040b521103488075590781084031401da094401c041007510a513841e070502400103183c143c0600c803a00405540305400c0513141c03442400e4400c00d64000f5030100e114440100f0030050f08200f4103501c034151345809451b50400d10041605407901400c0104600c043da18140c442805114410310610303c0c40f903400402c13a80401c00e80034000b18000b0240d0b007650904882041014000030540d081410680d00c051420409480310300b245a20706020b0380e010b0381ca80540d0b001c2d9555600559440c5005d100005980703081203c005030440c3c1e01c01218a05041c014406550103580007042201200e070001620b40310031a418004000803c02545000c2c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 330792895 1250 330791645 330791651
    0x70b15040f09050a0b0f010f03031103041707081014061e03060c1c0603050d0c03120c0e3a11030d0207030c0602061006140702030106140109050904080f1c 68
    0x42400030000b0000c16650040c105030b4211b49841603d012440c0b0300340250300d210a0b90010810010b480b408d024250300700410240d90034980c40344000308000120b404100010341c0a001c062110b0142032103490700600e42d000d406c020034200d003092610010b00040212744114203130b181c10000384d284003900c50309114004094070080d1400c9050007030140c12690b0380c0c041c0640d890f203140160800754407a880c1034980080040042265800044502d41c000c110210304010b0031414907143d02c1e1003801021005d280940711b0081e5060001d05210161036034000200d0f14040d5100e804540f0002a500031a842a0005410071070307444505050706800c0100301e20503018070560540c8407030250301043c003e080d83d2044a03180003496640008903a02c5c40c05881603464114400410482580101e65030201010100d542c0c03820200c0380c1d00001d0868038203520030310340b00c2c10340c009141031582d1100d1100082d003411545c4001a0400e62030350400c0c0d029814001e10319640006001c0b841495085183e094004010818 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 330794145 1250 330792895 330792911
    0x25020f071509090501031502030601120c080f07053903042303030301031e110616120f09030602070c050d1202100203040b070c020a09230606070b15040f 67
    0x5124849070107941a000114000d81c041541915405014126034000754011001821007000c40b000394406880c840c14000b64074488240c405c894090b41580c542e958803114014030700b08000d2051004000c020a042040400070a00c4000305600001d09821000d00c05854002d480c1c62990801030051020202c80d200210f00081c80903100c184100d0390f050070180c0171307c81440c1c14050541d81e000a002c02407000ba03c206402040e41c803589105100b0502600740c0100320140080843d5650303000305480720001c0c0001c0c20750b00034030241401d640681155072074103070001e0101c901d000701840c840e404001c24082e000510b860034041d42003200b1000e0100103001203414002ea18101e0040c0c1040441c1001602410940300c052003500d1003078a10503a0051403010982d51400c000301e0b0b04050031082280d001c4e030b80101c04101c000080c441d51542ea0542c220070590b0401661540e204a280180220700c40d142c20424403000420780a8465004100d081034602c0c0080004002000b9100c031001c122009171600b610303 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 330795395 1250 330794145 330794159
    0x906320c06060f03060c0703120f02030109050609070816050f09060a020a050706051804090f0503030a0204060e190b0c0a0203030712030b04060e1614030915090625020f07 75
    0x501c1d00070301007100c201c00700340d400e40203040d21140c0c00c50355045452406e00142011038003684d183d51582300360102c0003450001c0c02601c2c00c00c81e002a0850207105686a040010343e091030750700c1030b4001d8030b0760900e1348240c6090b03400c0404150403070241c48100540411074206012041e4159881600c2c010100c82d140d113268040207541da901c44030240c49070302c10135400041c0c103809201118903140d0044a6a02441c1d21032007440301504a882044502034000100c02020030307400e0000d54002d401541c030144c0d40300d15000c0300520996511084903c01e80c201d842e032440d5244440909000c0b5103040c51682d0316801d0a101f501d04054a01c00d01a400d8000080e40344200081480c050188440d2602d0800c699640c1006001c126400c50007003040c409103190204030000c4078015581c1c0200040d180c1041c00d24100d03410700303403250000d070740c061410f501040a003e454100807202c940d104c400c10005044520300b4688a14120640d881b07030051000b5400840e20810f8400d014000e20641d501e0101c035102543c03514 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 330796645 1250 330795395 330795403
    0x109022104050a030f09080a06021605061503070501020f0a021c0b1e0705310b070606060809060c040e060a05090711010b120c0603070315060305010302040b010906320c 74
    0x43d00324001144000c40c1180b060161680909949091000b0810552540e903810025400700c2c0035401280611111403000881c2088444c0c030550321901100d14003c142810b05142241e113400043c1550003144440c0030f6808009a203030070303060b01110001c3e480303e035103042e81841090100c1c028003424102c00c10091880c542c403803020000c80e0030000b01b4840c6e50300c8010865043c00b8204c4d04070551420440e203c182034107178050325800c0c009c7d00003040030003031b543d400c60201039440740310200c40c01c035120502003040517000302d50a41d00c1101d0302c010f01110300c0c00342e40700700f42445940540048000700202003081c603258020b03200e01504000d000c81609003081507000d8072201210600004ca5800c1401100c40d909103040403644180d045001003c41c5011801000002e030002469001090341c0d49103e09541c03404201800010406034600088550450042c80152490115110b0501c588507900f04203003680412949840c64206004180e5900b42e40120004942100507494030800d0100e804240c40300040307 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 330797895 1250 330796645 330796663
    0x311010f0f060902271801152010050403050c011505040b03010209240f0307080603070b0a090605030a0209060a21020403020607020904031817060604091106070f0f0b0f061503010902210405 83
    0x240b10756452072036840c44c1500540ba03c5d027010451360400c5901c04400342e410342105404c11322900f01076040910b40c4200b00e08440076100240d034410300da07110401c8242498801c10158034004d500039860820070501091507158203503403c001040c0707900100f5400c2151001a00d025070f2a5806981c0d41e404d001200409201c4181da03418424002c03a84006084050441160500807240e1640071441d031900b0001d9a050700002d00c1001403039002c110400c801e40d1a44c1c000d01201504c0c1d21845901040260720710700d010400c9602c0d12201e0320400003030015039140400d58900b5541200c80b0b03030f0156664030782100e43c0010b000011520f24134a4002090142403030100090800420003101e9040c0d40e0401008140c50000b0f10140907280c2c0700d601c405107810305900821280e4001c144a00019400f50740701d900001111005882900d03403c01448110b501c061000c076004482220304a003c40700481c114903191106209140c1e80d40d81c00104540c509107040480795508500c440710b110306140605181da00c1c0c0c1c41070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 330799145 1250 330797895 330797897
    0x406090914010912050a0c3804030e06030624031503060f01030201030c0c240b04020a1218080c030c15130b040311010f0f06090227180115 61
    0x2208076000984051190340030352078102620000c4c03091490b83c00e4805510080c805010442d441c10b010b03004c91480d006060080520110f24080ca5004c01198524214144608011403034500306110204e60700c5090070042000c1229210f60321384848001885019000180603426410890100c2c2c0a001c070070061442207a044900d0f20055100c0c008041d02d0b1039044030300f4a10345480741c0060001d944254040c04840b03c59042141102070303c4d41f14803507120b071410f42204076880242e400c0514404540201d6102e5901624154248850507001401c421607001c06c2184a03075441c5549006a07202c0c180c100a031581000708a0755600c0e000d29165181d07400415454181d108190425600d60060201684200c24400c51960940c5280c1d644912284010303100f6020031012600b100c00f462403c1c810031034000f6003200009046007031606190140e4010358005071000d44140701680e80d10b2007000c1442e20b00510303054054000003952000422402400007880040007003100049541c0012000a05903060300d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 330800395 1250 330799145 330799163
    0x30409052212110c0a09050603150408040504150308030a0c1e09030506100b0403060e03120901051009290604030b010308031906060c1202010e010e100e01050c07080a0c0204060909 79
    0x101e543d040c2e0740c4050180410390440c0c1a0303402001a40303116030140760050b03402020307a601241505e8207040098020340d02540c00030f00004082005207042c0c820311054038031400040420b44d03d1616950050701008241d40343c1c00c0d03112115940300510460401ca60b411031005504c1c12450f9000001740308076902e0104903540e01c6541701082d181165805500c00701c80a0010942c030307045c21941c46402034034400008000707038402808410b00e01000800c24502ca04600000040c042c9400d581c0413842ca41190b02110b4503034502035000040351411000080c4103074894541c2e283c078020803808281c4c1803189030300142c400c550304000441080300c202c0095000741e000d4170550300240884034200c021941d0b1032003414080740211103000b000460341442c1c018804580e000000d542c904004001c2c0c00e4920100d0190b00c550003d800c00408442607215080a07400c40344000c0001d894000740c8940e140c41540b001074820400032840002c214881d98079103201130740c050030600a043c0d4845686001e050b09000c1206d80e520 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 330801645 1250 330800395 330800417
    0xa060b04050105061b0313030f030f1805041104030f0606060206010906060f0e0415080102030610020325020303071509140303070807050c07031e11090108030409052212 74
    0x2800d40900c1d4180d4500408070303072800c110410341348601010083e074245140420b21074418008000c0115000450040a040d07203c0ca106250080485100711a01030030700c240701c01e44600b60030740c82c80b1a03425a8802c1d44c00013501010400094151300a9610061a41008110301ca0170440103030440e000b00c45044d001c035552a44c03182441030035154103000301d20000d00c074200b144094611902503142c40c0c141c09000003c5802c49030310401d0003952590000e000c40e07900001400828141200e80a403003010602c0910f017052464488072192a02822a07004031320846002e40c4c2c150f5409004480d80343da80300300c0607617038000304141d500d001e44514941030f07480d4042c0501d50034120360b02000b1280710b01c0302c607070351185260f0311503009035565045480d1514151040c16030210020301280f03d0161340d10401da8074494910342600e03202c400e1010b9441d000d8020101c43d030040041d20400400c5c2d0341902c40850010030203a50b507000d01c041d01c0100c001004507003984000c3c1c40741440714020030101c0202d400c0d51030801e580 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 330802895 1250 330801645 330801649
    0x50a0501021e04120b0a02041203030b0102070902040b120924090c01080405030a0320040308070b0603030c100e011b080f0709050a05011101060308030403080906060f0d0803100b0c0a060b 82
    0x1020f94071641c0051107404130305000043c15110b40c40d910020283e00181026150310314103100810141e8204c1c086960b40c13404180c60340c0c0400078540280340e4080158900ba0401c81501010300515100c214069036403008215041c10a1298a82589550343c64000508500804183c50746040e210f80000e405070301074001c82544034007451881203070020000d42c9400310010084009040a00408800e0680e503840240c083c2e03400c0000b4802507004600e029110704113810308400714070b0040c001da48640e2042140640814000c218128030300008040001c0d441d41b949845805007142c12100c001034a084c1206490498200074124002d20200000708202c3c2d49208045d00c00e09100c0c02496440124039404001e250320441c95040380102c05c00020448550725a904101500184d60840104140400300000d100081240c0c1e80d00020448a9030b005403410b0020581d03d0002d804080c00740e42c4004000380d0301203040c1180000602c042800c4540c3c0700c0da00b00c0800d03190100c05004403081414402000d41038 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 330804145 1250 330802895 330802897
    0x130f1b060503041e0c0503070f14061204030c1502040b04140a240917011d0726010b210706090b0405090714040609051003050f0f070903050a0501021e 66
    0x881d0f0003030902d500c0c2400403102000e1201c1060701205d1080600b04040307003a450500c03d05c4020039919110811755400c003010b401070038201504d80e6002d420b05201c0d4a1414108071811900326425007044a1403404170300340302c0309a200207800d032250742d0b0001034002420741010340108116032540a1007020803c90345d0400000804030701c86c41e2401c01c8400308003440510044c40f4981c441c40941803001145039105c01001c2d251011090722901030b5541c441c001c07403901c4600d5007020741c2081031020b01a0302d4180001c01104134148140021130b40c400d1450038400c01425440342c418024001c007a0b42d01907051407080c940d4111081100c03904c9000311000091210700800080003980d100c1850780c0c0c01d02d8100001c1c000c250200504d610308100c40403080f00101d10301070b002131014202d5940c5406800d41441c0031b2100c3c1080c500f00079003c140c901401c105190107125015900040812413070085030f10f5024080303d080346c1c6a00040c0c07840c042e25880600b0000c05500a0658000105848800091940c030200301 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 330805395 1250 330804145 330804151
    0x203090901090e0c010f050d06080c090c0a0504060305041e0f0606050d02061605030403020a29031510110118020901050a050d29040f150b0109050405130f1b060503 72
    0x703c1d448900304c1800b039801015030b420180041d01e0a01c0c02d240044d0040c1064a20903801074000780c220018805c0a410200150745d404420045500d2410043c0038004009100d548254801c05686801082c20403c200e1102d0340d000c0191680010003052a00301414074441342e140031030301c951401c1c5000443e410900701660070795800500c01e80c28414400c1a028401140c030808850f180020000400140d4450207030f000a00000c0c2c2c552075071140c00c40d00e84045400500035082000d01c00340200000c1404080c0d0010341c10100f41c42001c0841000d202c1912440c0d88100381000d29400d00004400000c1c80150036000180201c0d00080b690360fa0302c007409030819a40c0039094100f0101d5403000c000ca0360107940d90780404101420b040544211048a110b450401c1d5411a0b41451108400043c0103840307040d40500c10504c1030400c00e40201310006009400c4a2103550702446c2c0314030014040b5442d0b452035008140e0000d003d14440c200d1480c110000aa62600100003059074800c04981c481c401d2041e244 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 330806645 1250 330805395 330805421
    0x903020607031a2808030c0a031b020d12090b04080a1a010b030c0309120406050a12062103110105010f1e03020a090b121609230a0b0a080d020309090109 67
    0x1001311140c1032542c88003520400036440c2c078442d00c4001400714800c100030b001c072011084c00391142c48040d02d4010030f04821028450f000444405a10b00965103014403c110f4582c0907010685408041d801505c21204a0340000300988000c00e000643e82000300c1c814502500c91100803048102c200140d0a001e9028000c8081000013400000c078041c4803400115086031450084421510005240c1e001650054102000240700851a80c0003203070003450410314041492028010740307040200d0120300358007a45c0e4801e582042e56401c081854018102c00784a800c1100007444650b8440da0002c01c1800c031031040c44401540c6246800001c903189000c41c0543c0c0e4000c045070302c203500e00102c400241203d0f8102c2c540c4401d07400070000c50f091041006245400c43c0270802070744a0318062100c0d0032507003841c1c244007001c4842c0003125902080e10700c182e03030302052918001420010001c08990f030410303542c120100358800c14000c44203464002002d0500000101c07800015680c8441c1d40205403040c50010003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 330807895 1250 330806645 330806659
    0x230a0c1107140f010203070804090b090a0e0a020f190308071a090d180504090b160f0e0405091501030f1509081b010b0411031e0907060c02030705040903020607031a 72
    0x5005403800c4402c0c038440d981c051041b641400002e840d810341c660701c03a50007042c40aa990a00d6003260a000b003015510120481c0100003450605402d240c03075842003400240b0840101070200029a07502000c608203d084c10349403c41c880d04c03442c07c54425441340d40103a440907581d121580c0c403c400c0300c054a214403601c0c0003619190810f21402e580e490800e02c020319160030b0542c80480c4075102d5200360341c1034a00076900f80b01e9500b00f0342101252005009240340030040c1d803090301400c1941010028006542c01d0710002065950b1503000c908040c16032a801c0d961007400d078000000d00c002c154181e01d89030b0050348a140c3e0594030002e50001c64844000c000e26000c400c1c8004c0489018030303c02841500b220000208000707111030009401c4072000c01c0c1d044510359012007841204090200303240905184224100c4060900c24185c40c0d441c0c00390b2007560200f2198240520440d2001e00031040201009081841001c0c180d1402075210402100c1c0c020002c0d142c041d0191000240300c400607d6440040e10720 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 330809145 1250 330807895 330807929
    0x20d020c060109181e05010f0519060f08030f07020310092f0d0303151e14030a0803061912120201050907030819021213030b01170709230a0c1107 64
    0x74608170001034815141c55603140444205404103005292248131000550200c040d03139103506008481094024510001840c54184903400d4000211282caa07070359400769450781031a1002a07c0c01c0c904080502100d030800740d0000401005070700c064005503501d100541880450f02101030381c200c0600030b1541c00040b038054180401d0180e0712001d4a00254a00711007416200c2111404480342c003002e506a107040642c04124444a02c0c80301c0409501c110080d003a0010640c44281060001400c218130076461010005981c0c50f5605d001e000400b0014120100c5d9441410a6280004030200b43c1d800365080c0320004804100c04070b9004180ca5011108d1400c0031030410f540f8100e10340c0049a001036103c1c2854000714041c0340c0740a042c2c100034401500d1207080c11840c3c01c43c2401410f900c4118800c0030400384105825002c2109400d440e00b80c0300010311008484182c4100f4245c8038030285985a08006102c044a241e411602e40c0311a55101c0d40c82041c0100d01c62aa288101d100c0e0301a51582500c01c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 330810395 1250 330809145 330809183
    0xc0717180a14090406052508070f02120304020f1c0305030a06050301022b0b0a091506081e1509040b04230c0d142407050705061504020d020c06010918 66
    0x1e0764001f42e4402e01d1800c1c024034030a102d14a83d10100004011030114410880780c01d034021202070b00400c2910141c1040c410960b4845254080a00024440e0409014001850b1200716958401e0581003c0055484076141000381c032690080d1249200306044c100c0120340703410140200c8603408449100031860004c2044130426041000b041013805988031409203560395a02010320000d4200c0010004040c0031071048801a00722603800407007444080c50420040300080c42040b40014041014a002030b60b40505400e584490310240561201460080c08244640d600c150340c4960b20860448404031080107005009510720346071101c240c0d00c059010b44603805c0080d0301c03045081c0300340003081e001c52090f000309042020000b03501e00c14040c40d110941d100410b100300a0307080740c1d09003070842ca003000946032180c44000081c481061011542d04820b01c645580d4112038070800d01d00c3c41103484c0e94240340340079110b110a101d42e080040c20320202800055060b002d01c2d142c140d004000700c0f101010703445 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 330811645 1250 330810395 330810401
    0xd0c0c02011d0f0d03110c09010b03040f05030d06060c0b071409061602210105070903020109060503060d1202070305120c0309090a020f0d060510030c080c0717180a14090406 76
    0x40303203600312101800303401042d241c1d03100c1041c11300e100b92541850804542c0300c16141c0840003000354030030988400104001d024502c01c880e00190021302c421521021400c105156109946640e11080d02e045000600c2c9948000c3c00131896201d000100d01070b403134009045520400e14032201e030003107000700a9140759241160040a40040c40c1000f21142c1d80c49070000307006002111400301c404880c00080e0800c5030020710171264440790b00d044c91400f45003181c000134580e13001d0703001e200700348035002000c1450380c1d9458158242d6940c0c4018485618011306500035268070007440110360728400c08101c80c08201c0354100391101c04030804011400c04407a8010400c50300c00140c4090340c215420402d0755084c2c4010001055980e441600120760303c0c0c9040e05000e0340d040c84201e42010545000d80d40900c0f030750700c0402a030300a03006d40e10325604e40071503050031304c030300c00800c6400c15110314002030500d21042c600e60310784451102102d01c006429a40d02440380482c5003544e61503801513107100050006101e540c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 330812895 1250 330811645 330811697
    0xc02100b01090504180b0a050f060d02030a12030e1009020303090603061302030c13060e01080703051f0807060305090f03030403030908070506040b0103051b1c1a0a020d0c0c0201 78
    0x1141c1030b0310195440700840c0495603401c541c0c3c1c1e19a4150710440062000030311310150170080e045001c200c2803800865601d00c29202401c5d86100701041c0603200b007550b41c2080b94620040d00000c000404003070208002d4020b000b01d50b0720013070030302401f0f41400c6000307020f108100003650054051840e0000543c00c01c541c3c3d91000340303a0f60384260f51903815400b140440c4090f5104100c00c900655545c9032110307000b0251807040d80018100442d4082c00318441e40d1041d160f0f074004c812820041440d44546d281d040110100f04000030b045401032038000b8880c1740008144003107038400e48007040796880e1507440e030752a081d0011811029510400105001074032a9209105d05800344800d28180300f00ca035510741c01c142050301c2c181e07054600c80300184148002807101c0180c110100314094045150380012801507044c000b027004001540071002010300402000c05142c42c84c282243d4252840d0141070000203401622000103400e19086803206d0b040d001c1d44e40c40f03c000341c050319482e180b000d00c1031900200224031 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 330814145 1250 330812895 330812897
    0xe0303060910080d0306050f09060d0b07022a0907111515060a02060a050a0612060b04020f040f060e01050a080f0403030902040203010f17010902100f0e032b030c02100b01 75
    0x9400000307034040b01070084e1207924440baa008076106241c6410405a00200304985201d00340d110f003400066620041e001540a80c005d40c1540e0035038506070240c4c1808103518402d141800d440d28031200100155223002e0140c00b0488810f0143c1d200c411080341c0d94020001c04551fa503005002013180511144482a801802550464a45003c10380420515049070458a001d64809818030400d1a6107004803079000001d04010001c41c0e14240e40c030405046e203a0300141c5060341d43c1d900306071251981d40441c1e44034190b00c0a41c5a9507640d400b00f0660058081c803a001c005004004038510f2507104004071201c5194680d01c520b12a01c800081c00c1ca080c1025000300c0034540d596407000c4c01a11180081e5000f400c50740f81c41100c8a141880c64000705a99005a140c503074984005400140c0e2102d481014586481c90603070001542004240e0f002030b110b81926525109117a010342a070380c05440e0010b0466401c6560107064a04014143c095595410310080544c00041900503c040b0341d91143c8003076081 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 330815395 1250 330814145 330814171
    0xe0108030f1e04030f0506180706110114010f170a020d030f0203090301090503250f0f030c0501050901060302100e10050c0709110304031e0804060203060d0b0f040c090e03030609 78
    0x78540c1e02c40c1d4140e100e13a00840da41500d2404807001e102c1c0911446900461014902c000f21030000300c095100c4295028420a000415101e072078411001d6003e0405d14141c4044106256181c00310142140c600e441200d03c4510404041d40203210701040440c0d6007503010305504014552590140c8506091131b0400c2c0440c40284a60807041d0340074050400350720b010740090350381e41744548882580c04400c601c249403040e511465100000d10032010030082c4640140024074110030501d0304461840c48001d01400c9076081c40280085190107600c06001c40c0d108403245503000c81d030108251b400040205616520a2199200e110300030300460007000c640980105694400fa00d4810f05011a00312140101a0750408410031081640102d040c1c1c2c01c8182541c5070004500d0317803a00083c01c500c07008000415283d008000315900ea1580448480e0556020070341680a103001812000344050484065441c8508054006114409403080101c2d850455004d1442d680d600303414000902c0d0040e1855040c028 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 330816645 1250 330815395 330815437
    0x12090201030e01091109060102030427060314010204080c010c0503181f03050103020909010624020106050a0b0a03050615040902030c040e0f070215270106030c090f060e0108030f 78
    0x12003031255001131072043d1407240039001c900e001e109900500500340d03419540200300900420300c07046910910b122480d00011503115044000d480504030070f600080401e5010640b1404403801900070b00165002d58045512011700b58004403072080c21800c003d00302c0d410030401003a82041100841c05d9603140505041c1031005403401f803003115941010b1038000290b4500040c421490400c00b15070304405100c00030300c401410420585610b1443c07090389202d0b40300c2e940750410304600030742124000305802480003c12070364800b101c800640c008002e03c00068030703040c0000c4491074840d4510010400c2c2e40000c40c1454101246030340294009441a00c00a00512000a256171110b4843d0b20403400c00c80e504940d400c0842c0d02a16140301d9180501d84035550710200708568595010750301b48405441d45070755452900b840450300520040d00060325501c51080e0204426010360001031403c03c01c904100082031791841c0952601c2c900303006144082d0010041c010504038444090711100c2030403030499007014 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 330817895 1250 330816645 330816671
    0x3030e01091a0406110c1f0e0402030f010e060a060f030b040b0d05010c11191e0b0a02090a120203060411060c0f010504021021020a020c1509030c0109061209020103 72
    0x807200b20500b1400e5000080900c0520340c455503031003600341c0300002031880340203200000d40e190441c248011003525009001e5650981301d50b42c111510b450151045560b414110303440c003040c4100340201041454440301080650600c101420700f12105a50713041c40c40403c841048000d0980440c0d19940251106641c480e40d5841c0402500d80740d10500000658107402c00024010300115044104207030840d02d1a64040302100b595000e803c0ea011404000f070354030b81100c4034446001c48101600d080780c12020024860110382c01410b420400b180e0080da8161313940c10099401d04a0800250181c22160202d000201c0d1003e900b05c41c450000c248a01b040600700e2824544040717040c130103410340c0d100c100340019400c06d0004c0301c0f580303445032070322400082000b6100e8284208002c00444c08580c0026404441c5109001d000a4030000070700c001d858002e40c82000c12242c2100781040d07c00d000c0c0030074081c20b0b0341c02546010102e940701d85070240c014080072000e100070031004409905142e100d4000d0000c1d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 330819145 1250 330817895 330817919
    0x1603020c0a0c0e0403020c0901121101050c060412020c0607030207050402070203030c0d0201090c1409040b06010318080c07060305090618070312050c0c03010606020c0d0f020d0803150d0c03030e0109 87
    0x1518040f200c0101515060900900d40102c080a103030040600038014460260148410940d4a03003010038000d001e1100f0b00100c850344949a202001c0d806140240401c00648a056109160702c030350031142132039107000c204041442282c1d002405a8800f403c03c00050070190003038130241d03000a00350390404e82c200030200d040c6035511015a006075960401001080390a0307403540041d085100d1034650400400d00410b0f002400508081d00c4080c150300042c2e8140c0c480d03001070042c1002c80040b1071a9511070f20744441c0c1d035000b821025003240614070012800610034494a841211590010002600c3c0c90411814003800c1240f0180140543c1c20040b01088101040300030041d210350341c0f55038940007109401d0030005c510107007520076414882e04016075603000969007281c513002c0780d040605008906d000c07200000a9000250884c0d4444104804d000110b0f020758891030190b5030b40c09e041521202003121159540710700502c1581c0000003480424440c1854960540c0c06040c40e60040d9140c1d0344c80c000c8 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 330820395 1250 330819145 330819149
    0x103050f0d0306050f0409150e01020d0b0f1011150c030106020d0801030209062e0e100e0907030e03091f0207050321130b07030201060e0105091603020c0a0c 69
    0x180350311485003004021010407407002421500d240c200102803e01380068514003056562034171580e15002c828041c041e40064441070302070000f4041110190f60030240303000c7c2d040205020506441e1401c900142d06192820b15503240c0000c0141112240c0301c0c0068444181c0654500218424900d2000a010001e60447c4c010200078078010380702e6141103070003403405080c98400300400030a0030040005843e0b0704c02c5135030080000c4401e242e100d0442c0c440000c9624846c3e0035146402034142c1c021a003941c000302c1c43c8241e8081035a1810141c150860300b0f80da05205040129081704005000031074141c4203030301140d1140282029680740c03450b002e0002c1c100d14080410300e0a01c800c4180e041000795010440003000300002c0d8084c02000c60901d601d20855071206107403283d11400001c0004c040e22143c0c03d4800a0100040e085860740840c3c200203008040f2401060320b02c00d40b030400070400d450010640d5104001146000d203210040d0142180a50406680418948211011a00024462509900 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 330821645 1250 330820395 330820403
    0xe0103080c0a06140105090105030307030e01121107061d120313290f011401080415020c03030c09100306030809011d10020a1b1206090312050f090d0f12230103 70
    0x444d9410901088040c0e541a440140b10780c0c0700300030f907000017604140162541354003401c000400c00e40744001c00000d0030103040040645000001c0100c1008400d50090b1518102021201200400705d410181c0d1811401c1038400124802e100080e81d02141e0000c00b48464840c041726080301d03c9001c03130704540010407108046000d917075a013000110105100c4c414010044413407050884038003000040c01821000d0310241040c2414414001c0c0c10a890301222890100a8122581c9180600351036450b50080c600380d40c03142207a4914280310754400e01460003031f00d810181c1c0c942340501040c0150b544e00304241d4034501d5005101c0d032580740e91b9909106080742e1100743e005800c041d0541e141c844040440660080c40f510007500043c0204607600141e0715000740e1054000482d6207403030400381c4450211940d9074428504050411a0340900620241d00900400c41202c0140148120a44101d14400c80f9400000d415008a20004c48203400c2102c225220920350b070000004404400d8900070242c10a031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 330822895 1250 330821645 330821681
    0x31017010f1103070c03081305060c0a0e01020313051314071205130302070b0d0f0903200705061909050409050312070203040f06080603030d1b0311040e0103080c0a06 73
    0x20746951040c0034010b01034010040007440d42c40e01000180105915140260030066454005503d03a208410715508540d007000489016161001c440ca00c09c2e40848800c8001450388035049400c1d50000059611348401c00c8160001103080809004106407082c0101e0b5a0980301c201071402080307079050f21400380080d0707074980202618100300076068840290241101071440402040400c1d40031505400380c44c40f4440099941c0c0365040c86101900078032501c00741051600e86000205504101c3c030030410709040f9100440304a08140f246e403540c03428480c4079080300d8100000440743c410703010900000003503400d0a805454650010030200c0e408908101da042d0700006000720360040e041c50391940031441c1e2005514140c10b00c10b4070703c5000c6542c441e410074484000003003856680c051081d901400705045041002e18004610b00440600b00b410220100f841d00b07400144d9052140219070546001d08484c1200e81d06c0c60382c80010030350040703042d240c550250b9420100082e04074064900ea90203209100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 330824145 1250 330822895 330822911
    0x602070209010609140a0b032d0112021002061506090109090f02071a071b0c05190e010506040815070309020d0c0806060111100e190606090507090b0d0203101701 71
    0xe034145c980741540391107000c52283c100304040c50941201c6d48102020007950984036180490a01c0d8012010624140e4980c00000b03c2c1c0054143c2100300514021110343c0d5030000d0251090340c5458007507034003e11224007681c5601103400c000000300802c42e0185007508a079535556407000700700e40098002e04c108980010300e24040c0b00304600c20101442d19522003480c2403e12150150005002441a83c00180c1060301081800903540c003410041c40c000c0c0080c00200d64038544180e074000c00b809642c881000c0c00c0c00118641c200380c000c0d50b060760000d070b00401e2128140303000d0060f0520020040810581c580c0d072a00011380b07c00d08850311071481200d149400d0303030410848034203201d402032407a4100008000d1600b007034400050040d00f402c1902d035000400740701c0da521b80d80c24080c01e1003e41441c00140009078080103c40d42c050b004031111000300700196229404205d4241e1103521880d624038200307002c0000c00d23218550045400c510322019845505903120030040695010f5404203200e43d6450f071403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 330825395 1250 330824145 330824159
    0x1107050c060c032d04060c020907030e07050108090f0f0d02060703090804090c021519060509010609180b102703080319090b0a0e0f031309090602070209010609 70
    0x800c5040e10101d58150528540842c065a82c0c0904900d044404420541e80c003081840b562101002110115000d5681c588540c0003412a216002c0200e000c0d01140002540062103441030800d01d04440d8003a044407846c2000442b4043c0000d0801c521034051b002c03807142c809000300004482e5106600140c000c0303108950010b8102035000340080705241c180740788000021465001c07241034a0301c40e240001c0f0398030341705000c030f1500c00640071500840703800d200bd003c01c3c080b50741c2c01300c2d5141d1f1183c00140181a203490900000750030a02c1120b000c03484014041c0001050802c0d410002000c0e07110000d0440d00003030015581704a84e021400c080741d980c0c450307445030802007011207116001000350b94480a01d980d848403050707c0018594016042044045003040c034407a00003001c92038214036900038908203c3c011a00401c5101081c0c0100d225404e24004030980204c1a6200842800c940469207890014141c02810383c0c010100d442d07584c2085000e00594075001860b001c0c150a0740c0b00b0000e00e04003c8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 330826645 1250 330825395 330825403
    0x60103030c021e130f14070306051014030f090a211205040507141c05010204090501080f0a021e060304030905120307080313021207090b041b0818070801110705 70
    0x108001d040d00f880c80c1c01c8907445802144190802d03113200040c5000b0f802020400078032150072407a4811110b902405409a0b058000b101a40c20890303600002916001050ba000d1504150840c0000300074400107002e44044010550b00c581e50609960141c00f4686d50413500447c00c00c034908200c20700c030200d00ca0b80c035072004060b101e02407924410041400c0c075450713180d0395800601c20212400c0130184c8007045500c0358941c0884e40c95601d40070700b006250311314196010f90007601409901c0f81c545400080c41c04000100b10402c3e40111014000f00c00583e000d009a4a08280003130741d000c9090450080c43da200c2e10000d501c224042d0392000c0501c0c0c1482d04000b040604000c42900e40d0b4000c1c4458004942c001c0222600712501060b83e070841c900310b1001c070346802c03402d030880e170003e0080200c0000d144030305410892080002301c500300411440c440025600e0115040180006000d420009003c4003210807024521207580d01101d1103d5074400c0d41500b51490010542c031007800c00315003207041000805c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 330827895 1250 330826645 330826669
    0x20d0b090103021324090902040e0a0b0c0c0102090913050c062a0f03072d11061803010204171207051510030501050f010303081005060d020c0708060103030c02 70
    0x300c4103925540741d40c002030803400c0300303c210807410b540c0c5409003e86071441e0410502403404c189080c070540c1d503035080032100800d03810a040c1e004506149001d0f80301400421030000300f80c3c0c031190000303454685140065480d0008000110b0641d8208400d6a40360348222056100d844417034440582d1021520308541492040b4186d240154800e1001d07644901000241500c040c00403455030032403429429129103800c7c0210b00d01d0740a4000003401500b40010340b0102103200c41c100c44400c41d4041079405807543c000403c8000b03400f40340202460900b500d8204000d100d00b14100848100309286140040d0890f807140d0b215030100240c1c1c26050380903400500c298031744d00944855090a1038090386809841d825078801d0030075007408800009420f00e4207461480d02450b000303002004280781015041c408117000303020640100d013030140050300f203503981129a8141ea02c041c1c11181009210383e211300180d08401c140b50320a0090420100d803100c1c0c1040800d0085000f17903504d400b82070050051200140f004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 330829145 1250 330827895 330827899
    0xa080405042f0a020a140a12090f1202041e0c0201060803120601030e030d06030305031005040b0d08030a0e0109081e190c020d060f05010f060302180603090a0510020d0b 74
    0x203070580401206804454010448085180e40e9115003110881c1083c0e10080000c00e0782440c0400d820340c0f4407001800021148c4502c4240401504034602615141214403e0009521a6450030701c00301d56070b40c2004068500c0034001142c00000c0c0d03180d244021008000b0500c855a40365100c2004650901510005042401c0518941200030002a48002e002854981410f0721070182c0c2606100030411141070b030b002ca4008000a507128500142241d001b0f90340c80a9518405c90080340524191180210307201c002050f20354104029502c804450300001c10004982d079503030f0245031703000c0c80a001b90520944101042c82c3c0d1411484c46043c030381c0d16080581512144c1c140054a41300000100d41d003001103c0c0c1c03c1c6010142c80358070005540036041130000300081d04015032104560203981115050714512150180101e8840300c0403070490007a8400c3c19040100914084418185800295084400f040c00e80b030640780315464541c5041c2002d00c2c22981d0a900080d8610750003d00d21800801e1a42 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 330830395 1250 330829145 330829181
    0x3311100905070b0f0d05090304030f05030909011a0304060b1203122205060a0209030c040f0903020d0302190c02030c1801060311030402090601120b19240f0c03030e0a08040504 77
    0x14130b460342e24055059045402a9a1008184d0303918041045e6070080d54850104030300d800e8989803460b00c07a00000019030050010a00101d0384d403801c0d0780c5480070700d80c075501d00c03034119074468603640060400485019000f002c07040014003060700c18802403030011501e07031a401d024140508100f402006540011400d40408001180010004211a5040b5aa094000d601d034409800003d0a10050580055001c0d2601c21030720886500c681100701018001c0c0c003503644581c1145010740c141e12458088002194500e800707200309034001c0b00a8000d003030000d0101d4a68807401804103420080d004003a0407141d10007070041140643c503006070010412544101c9065007441c0d400308010080107005603050114904201c0c4101e8400c4d0312020986c2d02c01032003000b00040b070304010742040110303015440e40c180d580c050000340c102001c10303e03081144480d070302d9400e23064220b80201d0700b010711280304030201910384514854100003040074203e040c0c0200003d941c3c861502040108550b004406a00c000314 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 330831645 1250 330830395 330830407
    0x304061b1707062703020c09070813031809050603160302010f031d011a10050405090402010f0504080102030f01090c0c0c0b0d0207020901080a0c3311100905070b 71
    0x40c03040d00c0090030301192400700d4554203945044000741034410848094281c285108060a088001071200914020307025104840c0d9608244003241c90115403c40108101d003011a01c101c0002c0351580d441030291400b940c1044503100b200d0300403080c0e82e1081d4102a282c0042c09009d1805025480303120355066000e121291035130340043d000f19066640d103000d01d59560312500d4003c1c00581e2134030305000c03c440204540910304800d06441001c0b920401c1c00380440c841020401070166044809680005040001580e19a80111001070b09015100c04000d401d0000168006d4240003460003003130900c52510140d8180188601120001c9082c401004008894400407441500400050303882c0d09a1040d9103080d000706600280c407460000940180d50b4400005100d48007081c035002a82c81180801c015035928a10b04020340198502101c5852002c0315201e0762030140f950b69020444c0072b040415034100e00380c41c000d007040e10b8107007001001a21400d4540030000280035400150040c0841c082c10030b1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 330832895 1250 330831645 330831653
    0x307030309140d210810030c03110127060206100b03060d061104090b12070323101406091f0501110c090705130902030f070c0f080307020304061b 64
    0x503016100340707441148104454103003a15200100680150404013040c030400507a03a01410b1a802441c141e00011070701008280340e0b980c0c145480c0c084070380200d0080c141b1070542c1c903030240f409004503205041c00a03c0d44c48000c0003101c80051003103955105000c2203454a888000b81c00c141c40200340d0b40c001c0002002c20311000d0b0018090780e412140039100120014800c1c6060002844041e070000c11345103010800180c4041d1980204040b01419908020082e0542002903520748540c0402062102154085030789103262803402040201404100c55142d62201e41003002c5400c20411494901c100204014172420040c400c3d507080081c0728014a1105027200308480044158000d00b03040018801540550490030010401c8120f07000b00004040e060404000e80581c4c0000c45006003042c008400052044052003941d00c140e5507040340c0c20240d92031035000c54050008a40440d0096191000d980116180b240914850a01c0d90000c582e150304100c400b13010081d401d96400a00c03050703400c1450001d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 330834145 1250 330832895 330832907
    0x15030d050301031b0503100b01090b130b1804050103140c010207150c020604152f060a111c0510051f03020a09090203040305070605090a030e060c0c1503040201020c03070303 76
    0x4035007011101814141310180180300258907805142d043c4943e198a040703112581c0d00072110f04900762201c1181c95901e0755030309014000c2c00c01607030b04450f90803010480d6031a405c008011500400074000031507544040010110741080e0410369560b0314240c4020010401013000c0014200c09000904c1024038001580401c0003501c8402c10411001849250440d11041c0035500a020003070310b01c40301c20b501c0340ac1c0101060014040454640300740c0401c4402e0501600c0c01c607040e40b202c5030140540e5521081c050020b0301840003040d0b003082c0308004528000b64030480740c4044410b2000040343c0c0303050000e03616076001d45c030380c01c500d00c5080c1090100071b40345800c2d0040b00007047c0a04000d40c481c00346080a844640190344140402c500000401041560040080c80558490382d0100401d4880302000c41d6070314000040240802e40d800112401e1340b078103e0141410141003011143e07080c01120204545001e01c0c131010090711800320900085603014007900f42070410681c01054410300d180c80042c00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 330835395 1250 330834145 330834149
    0x31b05010c11060f3705070309140121052a09271807061409012001061e0b0f0304110406050d050a170c0304090209240315030d050301 59
    0x410300f40001c00301c203003003072000680d42d40d912180b581100c100400703142c078044042c01e007103200c010f01c400300603044120f409107095811064143d611218200c0c244002e603a4031034802444103060180b900d0310364000c1000c2c02041a800181000003003810708081d03007078008446024624084220a101d010310b50f030f422070410f42d65015800c41d9111040302030346030302071030050a000103440d12070380c0c400030050302034a54143c040503c03400320101c03103080340d480b5021101007881580c41010803000f009010965880707019505840402100181c500e1382d010701c0c413942140c01ca644116480b4021140819000c810086250010500000480c2ca8039400e0054220144801040180240c03160343c3d000e80e0300e4886038071803405400c01814103c48200c13141844c9079540744861088950300249045228400001c1c019251a01940c200135400c03d810b014985000e500070344082c68005442c101c1580302c4582d281c0e15000440100c8030708690740e0511008940b564800c05055030b00a80c0200c0006980b81d0b807207011a41 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 330836645 1250 330835395 330835399
    0x1090c09211e02030102190206130308011e091b110307030e01140d06030602030f0a2d151202130605090f270616090e181006031b05010c11 61
    0x100c070490b101c01a401007031110354007a40643c17011402130030f17081024400c04a0310109030211a62540d4a0b900e00301c10300c4e4040300060000e08401c1c0100401d20442a142404440440e26429041c0c0c41e40800011030703601c0c07076002c0c1007105440d501e60842508000e401540c1c5422074084c51070000755840250000400e1241070341001070321a070110054207c0c41c1070f56141d0300f180b9014401d803076580c1050740c0603410a840e8050605088404140d1615003445144240c1c2d62400102c107008070700328010600a200300d0b285001103911a01000201d070580c2585070003403c10100360b800c4280480c010700100902c0e8401c60007080e80307007500c1030000b0340d9180d268a6100807044010350003982d903601c0c3d4410181811050b0001d005681200b141c60000100e5894402da1004403405a140590350045903001440d1050707140d80c042c0714010941c00c221540300141004503007012034910b68142e410460498500d94000c0d00c3d000464403001e22912410101000242024038004074044926212403105211400b0424 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 330837895 1250 330836645 330836663
    0x70812090a08010c09140316061805030105040c03060e06090303010311010905090a090506060105160f0f0209040302060106020106171507121e1121190501090c0921 72
    0x503195541200040c0902002c0d0000e02ca003210b4803d001d007111502d03000d00d00803e403510f6040e5200b8200010071805082004411040e118070780300060350595485000b100301a0b40c501404039054400340a1b0900a44c0302e81690350002d40f03581841411207241501450321900801c050042900e000001e07203065035005000c126015084600503104901c09a11891b00900302500300000d5154039071000711500c0c000e00541c3c0d5555511001100c1d68451400192100c44040e10711001241d4481d00c90100b0520034440380b400d481060b000122221012502100107078040d200621045034203026600c0240300300c0413050030b10b040b0316040d99114070140040c204400d5004000503107007481424072a040c10500d5100304040440100700711079030a0307040400134030f170350400c20b1181c980c00c4040e081740c07070811080440b80700c50b000d182015000900d000d480006c00c602c40903485440c0700800d00c90240244581400044d02c0141c0703900186c03000116a0182c9000d19541350712400c0680206400d840090b44a0121 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 330839145 1250 330837895 330837907
    0x7060e040609050f15040209010c0807020a08071806081204030f051501080a03090e07140313020415090c0804050d11011803050705150c1611030a120f02070812 70
    0x40380c0204001c0d8010580107040c2000c0c0040c0d504000c140e51302800401482d01541d10640003031000f684101c5441e02d001481b14440b00000c0341d101c00c040c1000d42d2000303180700c04555460302054a03014040d004068295211481000c440c08180319000084c00c40c41c02800a400d401c2c030720310f6000d0003144009425480c400004600301300c1c040c0401e4488600c65000c40d401540c550300380903030b6061044000c90100d00c00b11008290050102c0855125a000f40d4440025128800c3d5041c00c41d0030181000e00120a441516030040e52a40070b0700c5403c10414248241d000d15082c07400c010b99800102410501031680140000700d00701080715500c4c0302c05414111104007004942070700600045c54608040619065a58105907014000701602402441142c40121020205641c085829500c0c81e581031820404102c0007002a2043e10196008103078441045401101003400d1100c2010125680c450319441c4201c620f4010f50740c440072001c02e00c010102c1c1800c09104958801c0d11020b86c80c2c1d02200400e074 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 330840395 1250 330839145 330839149
    0x703050c0f010501080309030706090819030507050d080604062304020c0717010507170124090314010c11010b060d0908071209080c011b02010e011107080a15060807060e 74
    0x40e80a000c1608003c200d50341c0c4d2002e50075129044100018070030f00a112002031840d105500751005c0c2c41e80e050142542140e183e9150f400d00301d100000310180001408074501048092044456649054441d21403c0c940ba80800c0304561494201c0003000810542801e400d00c4502105413542009450050362650030202d0700c0e103800310b95032200100d4118107029510a02040d000b04e8040d00d55a00c84000740744540603004121b6600740603a80541c0310b40510b24149015444035240603501d9030410b01850340d1661146201c0448150903d2940e0b0b44941c5c98103071030b540c8035825081e07030381002d402082000718600000300c880c46120482d0701480d031640c0c415024000d5050032078986551107404001100e22241e03020306a00c00603c03c80f0211f010b903400c00103880d4040e0403101c904002c603606d000d242c0d415036030041d184002d150100d20704001000784e8803100d00c2d44c03c0241d080a8420342c0c0091850101d01d00e4044000c5800c844100d0f100c030700b003100400c09510000780e104260351682c2070001f01009a000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 330841645 1250 330840395 330840403
    0x1060510050a030e0709111209151f0e010b18030d0504090b040605100906110a170c100e0c13061a0a170a0c0e040516030b060c03030406050f100b0703050c 68
    0x3c101b441510300070440307101a219000604144442400401f031603542d2401c095110151300407070512084608001407071840c104545523540480300344401c881c9684402242c0c540c007400f42c100301c46ca80c1001a001a2420025100010518085008045000d60701d040209580250310800002d0b81c0c65806144840d52150802d03030180070003030b104150545e10450003c08484103441003002144014114030142000801d001200036040141c0c2c3c60714195290840c015a40850b0001c4a80e0050401c149184582c500892505852560080c0a540078100401c06104011030314807081c2480d00b08204803c20703c410b007102800c4140340659407070700445a4150343c000e1034000302d188500c03071403008c04c405a4029408841038000c503540c0c40c0045900d1405210403207005131000914031504900d030002551081e04000040c0300003030190b50900b02c055481308d25541094600b00e90007a104c0c800c2001103c1322043c260740c4039224140c02410103140c0060602a8859400d02400700038002a0801c04014100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 330842895 1250 330841645 330841649
    0x50903010609020d02121302010e0609030c030a080c010c11070608040510051e0f0f0f1305150711030403110613081e100e06010509100305120301030501060510050a030e07 75
    0x700e055580d00d040c000d020000358010384980090710345610200e280d5100c04c7c406e12400d242c4c181c5034880b5605080c401c1008642160b02d41a51502c92800c7c04c9889407001d1148401c040d12070383c40360f515140080d040d603082d00c01c01413940c0c0402074040913a41c205a4006041300c01c81e80c16040c00d10894840742005810b1038075240c51200c075103080006100c9640003505000000c408511080e0742192110030243c03201503402c1d100341c2c041003803040c086800c524081e42d100d038102030f84440480f07110a6664509041003c0c000d1541c1401e41450100501190003c4042140010b80d102031860581155a02224119908000f81c02441c01160548024100c0c840001c041c18515045810329541d45060300f100b075031480c0e03628209025041d0130300003070000ea0050907000114200600080d03030821040c0031081c0c04c003c03d0400e100c140300300b000000c0750040c80312802030460a4a555983d40c1142410f03401d4500c1d641c800d074041c0201c0c6070381b440b095600c1010384080e010245030100307152a035240c1451800c0015 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 330844145 1250 330842895 330842909
    0x30e060403090f0e012d05030d03052413020a033c05060d020402094c1b0c0e010b04030b0a0501060509150d0501151e09060509030106 59
    0x110040c4014076400000704021510591864204161140c0350b111020a081c410018198503180c041009419510b03848000c0c1c03a410341081201695400c00030b4a002ca0440b44080403a81d110706000f0161041800400d00c84e0f8090f8800c4140100c000201e000300080350401190307590702064030801c880c8260400216402a00e009500600a0000c190003e90042070b0018100c00500070044102119000d40d6200c2c1e20000c004c6280114580c00b400040c0d171100d64443d40c428042804044602d00c1940341460501e24140000c1c40c0c10704019804102d010740c00c906213006903a03402c3c4030b9410ba51203144c11250794030241d0001e01c4040103150224200b0400c0d00b050140145140004c114800928094011a40103180c004d185846145212044960a02034a00054000c10182c882402c00552038001d800074160402e142c0702c0006030780c80444200b81c00408401030755407030381004a036000361071082c0c141038044d03100d8102c99410009003030091240306440c00c2c0080840e1002d003a80c0d00f03500c036100170040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 330845395 1250 330844145 330844153
    0x61b030301030b0702011d190c0b0304061b0518120a06110a020c040207020307150903051002070b070e100f030207080c07051203040f060c0c08030c0109060c020a03020303010312030e 80
    0x16403900c491490000c031503010044d840c10202c644082c00c403c02400d0201044002360070420648141c10303944460003203060718602910740000665103142c80c019031056018601c000385003a00e2100416508020810a504100c17060056019119103400111031514045503411250075449104c0e905001160a01034401840d10350344800e219440401049007034000e41c04e803080303895a181000101e008055010350140d011080034022144698401510700e18542042403800d9a6a07070741d03a10302032205181450180c0c01041007010803003100e06081d0410010305041030310000e018082000b40030b500b441e20040001c060f0402c112980240e0468403c00e401111803950740b10016095640d4181c10702c42c487c05091103000340a284103010007078a055407032040d0445410f034645a801c440c11101070505540c62160031600043e8211b00304002e00201009800118600615007005c0003201c00f11007000056401801501c8006940401103a040d254041c041c00765454400d102180101101c8001143da842 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 330846645 1250 330845395 330845399
    0x160509060d08030a050103020a0b0f03160c1506050f0109050d03030c031b0c0213060608130213020a0e0114040503070308071e0b04290c2b091103070602030306061b030301 75
    0x105580017941070b42c0c02584c2080c0400e60310f0020541c80d00c5140e0152142082c20b101040c1c412060748590032101d0b0301850300741c016400c00c0c3c403148000c40d0003c1000041c0e41c1e641508011a08288107406600c4d0b409003400001240b403c00420809440408014101a070324034500022600942c4041a804d041e0342c80040054031854000d001a218204164401d0388c082c0302e80501d01d405409410b003a107040c3d0751824445d40303501803c0c0c1000714049600301e81c0b1124041c009409940c207031015020050305a601e00b41e5a000020000d420648000c1e07903032000f22402c010074491900d0001315201141d5209800760342d103200d00d04004003201c81c08103000c0700c1e02541c802c401d014059180e1401e4001c0d8081e80c0ca01006020b11003644a41051080e00381c144110b4100004d607041203800058800c0d0140b00c100174080c42c00c111408c00140040114070540c582e40c407000c1c00f06100d03102100105440d8240c00502a2605140019582c0c0c04004c0056201d00b00009914455040c441c0121f2070202c00070046a442c1c0d6 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 330847895 1250 330846645 330846661
    0x30e01060f14030609032107111204061d100e0604050907050909070c1e060f0c030204080c0d020612061f030b13140a05181f0c02160509060d0803 64
    0x1070068400ba91080c4906800f082c4120b8000c000c60f0300c0700c0c11081c4465003811100c006207201c0400204000300f88134020400d089a94020f1010101d07800210041e03c1d038887c10403101800c0c01110f44444100c50002c600c2c009440d444000d14020700f00318506100c3d00e182d080000203074140c030450300415040002c0e002448031881d000005803607500c2c1c04940880341039030381710001c6594406092001d08a03692010740180c05040c2c2e1828009500e004240c0421100c08225804044e20070513a04080040c1d40000d00700050402440b00c5c0070445c404079044a42c4030800d40003d519806180301180400e104d28000c034200d1350301c800006000a2500c0c0850703080300000c04001e0002c1010001b00e6004440c0703494030b08a4402c4a108900b40b4840c12007404400d9282c1d840c2c054014880244541c045284d83c12050075200020040380c01c00c500c0f00b8807a100300842c1b0480a0050714050401c0b41c0c00d40d48003e480c0300c1261003a400081c291001660600503d50356040001c04000000b100501000c0c40001031111413 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 330849145 1250 330847895 330847919
    0x90a110c120c0d180603020307030207020315060a0902120c090402040f090504021c030f0e04020c07080303091002090d140309041107060507020c031906110f13050102061303030e01060f 81
    0x900484059843c0600c810205445004081c1d20009201c422410140035490096014581000a074034006003000c0f0503601291802c01c2801e81c05452021380c100704800c031301d441c41c1e540340502641725096041540104040381362003000340c031054290101080f0300c85c0320746441d81654002c100c80704224108079950103118004180544090340164080f01200f042030725400c0782907058a506035909100c1c0f100c0e1101c00c0f0780440e64803c0640d40207408110304440d844080060401420400016681d241050201103141c10007420f0807a5401c0c0c0184212b116990300c584900159981041c0500002204070200070b0840c842c01240d9a0f05c43d103010a04810407000001901c10700340701e90402c00090b115050140d0355658410b43e00c1d54140d1041c05d42c0c40c4c604c40b0341c12100c00010300c03414000c1140c40f0341c204160150381000c190014035140100e440344040c0b0040d05420000c2100303002411003070905803851444802d615074090141503d660008001d00703002d42c400001060b4044506a070707180c035a181f40d03040c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 330850395 1250 330849145 330849157
    0x1302100504140a0f060516080316031a030a1b0b0d0507020d0e03060612070302040f0b0901090c090b0711030604060605190e39090103050c09090a110c12 67
    0x414101a0054940c1400094507007914444c02c011001145040400c43e01c40d80a60031414170aa036591242d80041c140c4070295004040040c20705c0c00030502100003e003183c86070307841204900185e5441144c5c07034a0128105000a801c4100d4440010b0300e0100d098200807240d00c0b2000b21000094080e460100a0740100c1c0602510341c00d880d592030000c03000701c80848124403841d43c190002400f14101d407824909101c145141c4c407082d200945d9a03030700058201ca00e0315441504054681c0d1040401e860301c4c240d03150240c032481a080000d269090390040514030103000c0d031060388000251250500c49a440700c03080188000b000c480344c52400d0b2421402031f0810f40318840c060001da8110300551000400c1c0d07034007500c031800490080c0341e84100222805080d502ea10020346003200f00440607001e04030404409055076811030039a00c20855000504031a0003d0444141e00000e02070308100f5550099110707000074500314089060915492414510b20421710070b80d141c2d2041c031520f000c041d217401c40a051 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 330851645 1250 330850395 330850409
    0x60309030801060809280c031b0b2b02071e02090702010b0d11120604031106060901050d06050916060206040606050616060f0f1802040b03010e070603051302100504 72
    0x29680e607a03400156140c54060302c5511481e00402c4100c20300e4030502100800d1299013171401c006c03002031515000d141c144103400980f0340c0c2a650342d454000140c20100d00d03000701a1000010f03d416081d1003440003c060030030031031041c07002c504810b00886500344c0698480d01d41104c01c1c1d552000250300060742545241204a015500742c0300003c84160041c4100c00350510060480c4080d074440e6030711600d400f141082101c1e031000903110444581c50b010051540314510a44450308109905440070380f8101005002c0c2d88101151001401a40ca600380c0c041d2081c1d502c074401140030b8a4811041d414541c1c2c2200c0040c640c050940006400384d0700140c454000c900400c0104900c40d02c1d0b6042c030603144079002d064003402c0074182d0403000003001030740903641004044100280000141007001c047d120114040c4401c0c0e0391045410042d85090700c2008003443c0210b000304242041d000c2025209d905c548500360074585d031403000a040c1c04808070a0b44800340e00402840e001007a95001905941060041031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 330852895 1250 330851645 330851657
    0x70f030c1a04030201240e04020d0506010602060a060e0601050a2d0f1106130b0a140c091309111002010209040203100e10120b220c14090c091c0503030106030903 71
    0x2007040e91001c0120709054403601b070316080c50420610740004840035000700d8210095041c43c3c80800c0003401007038040d16a5501504c2c1d14101440d00742c00b502c100e40c00c0b185103c21841c01307008181e030300801101c0302e4041ca81000030061102c500e00a100c0007100c0c035071950390ba40d0314060800d01944040c02c81c610150a44452a1144075020026500c24040b942605411f5000580304042510107030025030207240098045080301110321654103240c2c064a00080e6000041924071003450b080f045e060a080c86103004000c0781495450f0031080c1609503000030f0041c00c07078164105105100b0f40403038507940740190095513242410311424080421f1743c402c880098181d02c002c01c800381c5030300c02410212419480801c0c0c44c07003043c2d2200100b030940a06868408001c5810f004030180036107142e003090a0081d0030019006103019140698605030016182c8907001003010051514504810380d203119509071059804106210041c071607082907090080c0051202000010713140e64550440007400c0d1003a0b03562 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 330854145 1250 330852895 330852911
    0x415030e15010f27050c0d1e0c080601020604060b040f021b19170901110a0b09100c0c1205040512030408150903030403230a02030c070f0b070f030c1a04030201 70
    0x30021300a008890b44580c03020005000e000c0c8a1150007160701301a840328164a080020004842100c0d107543c4010003036070a82280050002e194810b420b109582c6081c45080c918200f00000e480320700007000107050642c4d41a02c981640c8460307000751902414151f00715504c01c0c49a105081d1100c4030301240072148110540c040e043e00c03580010661656000d0b000c8202c04001512540d0190881c406450401240f44114074400708200f00c1c0883c0c107800b46010301e030582403402c4030714202203160004c4a5503e00f03207030749008165484400d15481c41c0c0c10a021136602c01c1e00c0c82044811b440340e07512290340b0102100610201004c080300600c121a084021215182e915a5072149000d2041360728030001c4e0001c0c0300140100b8003421040103020340c0c1c51481c014514030380c210481c6a40215900304016400811280799040041145030082e1070301d00f0000c07420518101580750b0394424000d0051215a05003880000c060181d5031103100503910007000203d800504021940d0182c088406034019820441c0c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 330855395 1250 330854145 330854159
    0x90f100b1c2f0d0b0a0b13060e0d080310151101050a1a0409020307031b08010e0307080a18080a031d0a050a0b070f060f0606021606050415030e15010f 66
    0xc2d0703048002c0000900c2c2e4488a18080b42c00c060f420414034201c0064541c14494510b035601103001000d007000d03580c2242c0301c090411554084070b5158100100b88a14201d1b060380d40d5854a084000743e5038481d00003503581e564a480c02201c0340341c9602c03502040d990326a009074841d412421a802500c00c0c10300800c401d40d00c80d0500e00545405402220882c40c1d4000c450701e080c10190400890300c2c0c006001c6079480765407030b5500c030000102543c01a8004001140c1070100c03150038091500020030160003103080140c252100c40e5540305221108051020080030f1562017140c880e084402030180400f5150107160310304014128020206401c131010b9100004515a403a040501700b094600103800c00c014282410304603405944141001d40d42169004604d10000d14280609034103035155402c04105070f4034080b006440d0000c40c180c0176a1a00f95054103000c03459100d41a030b806c8a0320403408a1880259040940040070440402505402064442c110a83d1011901c80c1207600303041020f4040355035554 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 330856645 1250 330855395 330855431
    0x2030d020d140405100e03010b0d0b100906140405040c080f070303030b12280b10060f020303090c100c0203101d010e120a03060503070f090b01080402090f100b1c 71
    0x4845c0e00c249141909180c19105040d43d0307541040140c000241c603082500011980d4800280c11039a0903074480400202c000440000c500400d00c1150604c03180741841b10303030203818003d100940e00070750b6580006014440050044001482e540080c0e8151083d2014019210304280c0000c3d00801c2c10500001000d043c481080b000506d004c401419405245c0c0824140b100400b400850b000705a619548000c192600f81c0b0a001d40440ea0410380307403030300d01358000c0c08550401082c01c0c190b400034020010403041c007250810900750100d81c10b5141c08044001a1180320611002035010700c584d50306200d07810700e290b1001740d1701c5141104200c0703d1030003150094281c2c0c080b1004aa0346400c11141503040303c00b03c001034040200c050030085a240d0305d860100f490000b0310f90200d051004040c42c20400d40d4030520541141c0e100a203020038992a10750049100108007804e15000d04c0c1c050b9001400d1a07200c00250006001c5103003001d940d03a8503110140c003007040001c1216100700d02c1c1010703807118410302c1c00c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 330857895 1250 330856645 330856649
    0x7020a0801051518060d1104020d0905070b0f37050309010e030a0c24020c15070e09161206060903020a08010606080f0a06090609020414040e1b03030702030d020d1404 73
    0x184d80b0448944c1c4500a02c249800000801c40d400d544180341e641c0140d4450001d002c4454541e000080c032240340d804d01d0743c54601194000d01798074000300400f4412000400c212a5424401310034071f000e00548040300c5c0303128450498000344900c5c0f145079a90096902c2001140100078402c0240002da00504020b41c4a1080e44003400200b446a642c00000598403604507026012402c02e080107440c4e4035030707013505907030183c444041c2c290061200030300801d00c0c80184a42010040c81c04114003580d000c0882d0f104e042c0605400c02c51220828290101d40c468042c5002448044030144071380c5071340742406084a2101e002c1240714180139a03011480c000148101c2c1d040b00d0f030303a540d02c105503224420310030066100580400081500e81c040030440d0030450003044c0081444120050b40c032071802c1801e18500065581140c0704030705010101c104d028000510070303082402c151017421a00c1445c400a807940c898800000d40602450060310452900480e90b0040645076803518021220588072901c000d215074 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 330859145 1250 330857895 330857929
    0x6150b0a0f0318050d0f09080d0302030a0b4501030f170a020c0a05031b010503070e04050f0106020d0513060e04021b070f1e0b09040207020a08010515 66
    0x1880800c400301d01c1007503000c0a1a4081c180082c4070740c00c29680031050004004180c0b6142d1004519410007948140d0700c9090b200989410b014007400c00015684401c0d140e1158030070550080003080104216138002108110003c01032860020609030103d880c421114421f1100e68001c8a29924001e04886621500502c1444e1841d160300710f9442c054072182e120019940d1902e00b001564260500c41e0080414400c07a4000f000311251000c2045a4483c041d04070a00980150341c1181034007203499100d2903881000d0800a40b02d0383d901d2812241c058004041640c4542080140654180e01c08410f034182d030090303800c1d2255444401c03400d4a26101d9540b06a0407401c019104210380e034400d8103501c05000000f040980740c105442003000d4840c0c2c1e91184400a42c0044200700409005864404020070030248110740b1580602c0b420b520720401481605110030001880c1ca03c19510b40d0304441a45032300130452002e064460061500a24045501403501c070424400488c0c5071604207020001800c0d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 330860395 1250 330859145 330859147
    0x914101802040e0705060f0904060f0501020a260406050d05010504050f0a0507140a0e18100b030a020904020a0c06061a030a1505121f020f03010506070305070803010f0306150b 77
    0x61542400010000e032000c01c1c3c1d160045032004640c0780d035440000c02c03651102100c000c1d10340030050108400c407200b581c0081d80d851500d000812207660007143ca00e0482e42c0150804082c4996140094580c9840c0345108040000c001004204140c200c4007415001c2000201004203a885130305110449005075003070515800c00708006141240540c0109611000c03900c0c013407c054041e83c1c0100c4041d00440840070100c1d504203d00103550821802c10700f00c00004081c1d50007103050019040450725054003402c0d4240700f000000402024007034040b1440d8070400340c4110350b9403502c140000c226240e048404c648050400c400090020803100c9034001d1400301d91002440c688400320b01070018400c9481013980905580c0380000c103a665841d000a544055101034502884440864220075508a6001603031030310500014881c05010b1081d24107440d819603c9039500c0071181000d580034001e20342e00500b990b00000010452480c00e80d900f204132440303880103002001d440d102e151196080c0780190044040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 330861645 1250 330860395 330860441
    0x6030705030a12020a0204021204061803091205070b0406050c060106030e0601050f010c0203060a050115170403050906041a18010c0201021015080106151106190207060f091410 77
    0x40c3c1c0c031043d98034040c0c06004903540380049601260603a00300000200c4d4005500042106104203406840d05000711112443c5041d00256000341c81912540102c07800071103200c1e855010401c003001a200504042c0d1000c54865035110710040c04c80c6d2107980411024010f00e8000250a4000c2c081e424a0040f00000b80000d6030800c02441485a444110b0b03030304001d000c1c000c05001d82c42c1405118040c5804140104035581458070403050b40d55480882c008110030303814503d0013004216503040d08540d040c030b002c0342d8032614440014038a004a0b081b440818900071103040002400b00000c00d01c2e40c4101c861020080c10020055400110311100079000d40c20401882001524640c800390b0901030078003c807548151218982e50864080d6000110f002d001201400b40f012740007030780140f50a03c0c0a004003107518007018030b500416211002c1c4800150081b0300002000900d400c940501781513002e081095030301c1824521030500841c8220f01190082070a000788606007401800a00e940d14410040024 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 330862895 1250 330861645 330861653
    0x2210703080f0702190e060a03080403020405070c14061906150c030306120c05040f0c020a080c07032909062806090908040f0b03130f260d0506030705030a 68
    0x152015440a51042d0100f080e0030040c1d44607a2182c1141d01d4410810801ca801d217220081c1050003c0c10741d5108007042c5004100140300003045806499065070003007940d4941780403d6a03c3c08090780000e000044040c1d11524500c00007a00d46d1080f00c40e8070502102c20640f00907102103078240d00410010303558800c54a000a4051400d0310305291003480c001803415a208800418269010022250a4000c91040109141038010f10824074155081045003c00342034004c2d648000385a0010030031113000c99407802021301803010500844c0c00401c0008a00c10914503c160058148003581d0003441240c04510380ba50001480c520031901c01341d0010f00c0d404100e040c5010884080c101103001c0e900c6600c04a90382405010303040d80d852240020a84940c00c200c000c038200341e4181c00c2001001014010801c12b03400c07052501400360f4000d0300040c0000a142407030405100c044d000704d40340c1c2001e10303000300800c40302000503c0c0e060407440c2c081049496050030140ca5131682d01c02c0550640c0509a020045 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 330864145 1250 330862895 330862897
    0x100c080402121501090b0a0b0903030403030f110d05030901140405070506090a030804080a0309080111160f0b04050c0f010216170f0703080d05010501051c0f020d14040221070308 78
    0x300c80100c2101e884041c82e66900403005802d030041c4500d11b8444008203101c1c10164880b8015125003904541130804030030129541c1c0c0103510020381000140074059200740c0c043c65101010890040a481c003440d010304000c0c08503402500c8000c0c0300d40ca080005c00c0600d4207414254051540400601506807400c1c0801c0010703089516071035484028003000000040610000f003000b4100d40000d40b01604039400d016040c01155408002d0170b0b41003540302d4185001540854040202c1610500c10000722800d1440e02c0c1c1710078420040010000c0d50034801801000120f0414054049802117045e036841c0f801242c0b5282c1c04482e285094007081c1050000f81c112030420032411819108541c204941c0e05000b51030102564403e6031a040001100c0a17240b295029030760162030203003400c40c0b404451070b01c85042105001080015240d80b00381c10500b213286c3d0340446000b407043c030fa02403140388021002c1315410042510101c0c8103034440e160b08540b07418442c0c00610140c0180c0c01901c0700c01c0c65500c1d0115a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 330865395 1250 330864145 330864169
    0x330109050f1f030f0f060806070804030806060a120905070317070807120e180901060f0b1614010f0b100309030c080304060605060307030e07050a1404200c0f100c080402 74
    0x1850389403050000941185e10440d80d4041050b00c0204489240c5101b240c201140600311008100795a410400820b0b000a0056005003040d00c00716521045080d00b15106202d222502ca030035030811507180d007400000101941942e0080c1c4981d040280e0207460501d0320703c1b400c01700800c00748040c88110046629880c980390900218109010100428070015020005100d0100e00e54510074042c440e12480900c1000054018190b101201c40e0400103080c40501490142a0347c40001c48548010410002d1041011a0309440280700c01d42d0359980740c034044c101d9442c80b02e0150000020107001240b29000f00030005401d034580c0006030350b01e521207080c5ca510003401a1001510f0345000030b09504c41e000118422511594002500580751021600706421540700ca0710512400109012003680c0034081e0006610880d0005442c072440c20455503071410101c0301c6042c0e2080400da0304075418001c129003070452448402d444403290b40c3da104804444001c202c1d41c000030b805000080c01070600c000341e00d403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 330866645 1250 330865395 330865397
    0xa0f0311070c150f0203090d110109080105070518100903031b08070f050f01050603060604020a110f0c0a06091a0309191415040506040803330109050f1f 67
    0x3260804586400b0441489984580049203a20b1148481c440e80141c800a50700280d10245142c0700045000a5001d034145e84d01030202007921645014a03030181400c64010b09511000b40194030f071900b0080e1031504032070b80341c007000038402d11450400d02d03042d05520f140f090581c031a41111801c41d1011101d0150340901007075152400b000d00000701d8204805001c0c214800c1400c5046c3d2142491308504114040410a07840d038141003e0100390360300410625072100007901c00585030300101a007100c0c00d441807429041c0c0c60003100f4010440701d802090820407000c0036039607035074901c1e980e00c1c044926209502c038203012258480303605c103c100c01282c01182c0010401c02154440513820030103408a40003190121224400945045040d041c10f10550020402119500440d071410382c0b2410780310b000003031004100100000c00694540b80703d10540d1441014130349074400740d0508040074102c0c4014564014042141c4010003d07091811140d10304101750094042c4a000005000b50441858804001c0b4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 330867895 1250 330866645 330866647
    0x30c130b04090501051e03061815010b1914030402150d1508060c0708030c0d1b0507060609020a05090906010302092e0804031b08040b190906050a0f0311 67
    0x50340350306240152028100d0344200080d00d5241400708070a00400510300364200e10031012829450ba408500260301604840160613140c8256540c41d0800b1510420b141104465000101e1340590020103000380341d12280b4680c0b80b03a0b01c8440103a03038640c00d02c2c60400048400700002801402c040040c2c2d800400c451482c40d051095600c1031301c0640304205425280f031a10034004000003c030030071035a81c0007000c034400b96150600a48031a4501d100082c1800c2e070450000807541038401c2d9036845208004101a9005070040540700c00810f203500842c400e4440c00d003400c0c0c3c00314180b1224800c0703d8000c02692600c0d0f281c600c0d510144000050700400440c1490750034003510040b5200d10400b001c0880d2521412a00e554403808200c90103c0c22304030b1601000042070401c00000d03000a001c0c04458100c043d00c5d120103466280c04030301c52145810441ca840000318058014009000c0d0f442105031185d00e9800300303c1e46440003207a06016040c048800910301d804100d031100c0c000e6111002c010040081d507 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 330869145 1250 330867895 330867899
    0x200307020d2604060c05011a010e0105090303040f0308070624090c031409030a021606170408070510020414221107021009060f030203090706030f1401080105011a070503030c13 77
    0xb40d8a03a04030303521190108806207184010003000780309403c0d1081c1205150702c452110b1100080c2200007000c01241401400203000348a0364040042c2c03402400c11a41403030540c0e442e07107400001d80d00400c00454078141840445404610405584036000e03465804100340740e85056608405450110307454001e0503601d101c1005002000b4600d04d2003890090000d6a0f00da07581c178002854407c0b40101c0c03600000c08000e042c040290f00c40c6016000c40d07507040c900d00f0035846500707000d04240f080b8a4018242d20882204800c1c1e29110340180c400c032007000503211204203a040c2840729040782c0c050f00c0b5402103040c90300c1100546642d8400121001c92100b0300d41040d0140c2c1c0420a290020f081c04400300b03003424400c01002d6404201c1c16210102407605600303504000d1099035446030a800740009064444103050203c00e910f5004201c2540380409107060b40d46d50b5403049000b02402c0c01541d0b22006d04c8d141c07040140c950241201d4116030710000a601e16034801c007001126422018500010701000b0302c0c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 330870395 1250 330869145 330869213
    0x9040f09051e070e160c0804092a020f1c0207080f060f060316140f040f0c030b030a0b0a0506010504180f20031b04080706200307020d 59
    0x11441071464081007142e4000d038079070b08140341840c903a001504000c404c00400c0509445043c03501902c000904010f2010381075460306206500442d085544110f1401800e00c3c000706a1440b4100c07081d0f04e00f11300d48054564000100d1711140f60540d088036603801000303112861440c0d0041c01d22040e0743d5206541001c3d8650110a0800401002c2c2d40080d9108100303208001d4040540a50040d80803801004050f8014900340040c070b03518800c00e03400401c1000d42d2a01501e0b020304203222010001d008020b4018900e034404000e04030640d002c0d00192500f00c106005040004c2c4440015800c600d001e1181c0e0384107401900a048010001410040144800641c0f4201002a00660449904e002c02c14a03481030f0958110350b11070300c000c1c00c42c050340d000905148009104a0740c2018440043c10303c074030082102e00c01988140c1e0301c04d100e11700c115580050003e9000c3c070f040040d1203866840000c1c0d01c1d000c1c0079040d9a4041c003d000b0350321900f840c121000041d81c642c00000c10b2048810001c122509100c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 330871645 1250 330870395 330870403
    0x30112020f0303042309130506160201020f03040f1202300918040614010312050a0c2003150405030418090203030406030e06070c03080109090f06020327011109040f0905 74
    0x65550991004460101c2c003494401b490503804501c8102c8042844055154107503030300400380503801d0300840300f008101040e200790115020000546100c0d83d0301e091501e070221440c0c0c0c2069054500a0010310303500c41d41071010030f690048240343c92040c10003082c40000b00f0070a020740d600c80704013a20704014400c0d05455061065505842030440015a1f25080c14640150f0f044201c144130600c0d070180040c00003031031201050050401c0751a05584550160740140d038410444540682280c008103c00002d08840354610b8400c0482034050750030410345d030800c1d00c03040a01654018501d810a22041c82804c1a080701c28500114035100441c481c400b98020a046a01580050780082d844076000d40c1c07109020484c00341c110030146403000ea41609620300812844040c000d507140261903090740410300030541d403801411030704844115581e00b000c3c1c410200011690100e224071024104110a0f800c006229040000825541240c94144a90100402059a00c00c00f00043d80e58502000104030100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 330872895 1250 330871645 330871679
    0x2607030507090504050d14030f040203160e07141c090203070b0705010902010818070e090c0402270a2103031e0b09090a1109040c0e1515030112020f030304 68
    0x2c000502824242019404c0c4141c01d49003d06001c10406078040c109000401c032a442601017465444c1d40c1c50340d1001070300303054050761074000c482e5581d5004282c0d114a4086940101a03d4442004071980c1c00c0103600c50f4020350090064444414090710010703030103500004942c03440201583c801540b03401c01620709810011042c0d40980d500c41508003196044981d40e5005400f800c49109001c2030745512550f6080d160080d64030140315400840c41112007081101e4082c0342c01002992188540e083c0110140480740031481800c032075148584050401100700c0080e01c42551a9202804411580015500048500300d040642e9a00a19101c0d03d1500c010344046042c0c0c00b000c60408880310030400140c1002d00b04151035001a84010f00203103003201c1c980c406032801c0c3c9030380303009a880d07042401070051030358400d080d00f00b20030341000320001e03074407447d180e0b05c0400300c50300d085003081400e8004950000740a110522492074030060054a0040c0709066003040080440386055290302210008040341 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 330874145 1250 330872895 330872909
    0x703140103030c030f05120624120f010b030f0c03220f02010306050603010b0403110f04020c0619020a0807030f0605120304061407120507060902100c0b090105012607030507 76
    0x900f40c01010554000103007890701c152803410a0809007041403403000024050440d83c411207443c80508180d078482c144d42c506215400b05120744488014004c214030300c104a804030801c00c2c1c01c100200d50440881d055038020001c6411010300350f075429506841c03540c000f80c0001016145168400e40c007a07107a803610041c0a00c07400c0d1140c1040c0c03039403001400b47c1d249500000e208603803d1006100c0e040c0824151404c490300076407404100078008010034003004000113001c3e01b082c000101c3d804440b0000642d280102920303c0d002c090840c000303030590100d020300688040010311000c00715903003d120742c002c004d4100d50420f0010b4460382e540b00145500b000035040682c95000414200321898001c0083c21110381114855441d24800d03641e4429000521000d0340c043c08004120002031200c103034012550180c0c050441c085103081000302408940c841c6e8412100a02c6100000303e00c1007041c081d29040792200b101e0440c8490100750520100f1000359100945da1188001c0000414810401e4000900d50 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 330875395 1250 330874145 330874157
    0x405160609090b0102070b09060706060b0c031b0f15071b05010c0e03010e03070602030408070c1d06010c0506060105031b0f0405121207020913020d030e01030614030705040203070314010303 83
    0x6001ca8400558545803c80e505540114108000441d180e01c1210140b120031504141d850b0182e1614500030185900030001e01940412003040006001008214070540707200b110140009414090381d4801c000d010041c90b503041580300c00742c82c500ca0a40603400201604080b0403002c4641503807041c14000a00940305a910740d0409095141c115504000c2800705400900c4641c4070700f0080e039a80e10403000300400d60380d0f000000a0a000781c0e90107407004030b60711061a010342c0d666035107807101e9154800005c5138607013507800200d403440d80900d50303690415a1080113000c0b103546501c0103507500e03040146110075007a0b490b10142d004502150041100c03d00d10400c05440300c1c140806d00c01c5407004412250700396809000b03409801d401c440c0c10340781c507142d04483c031030081e0391500d1a209005503801002504a209508d02000705504a40c182626060030307641088620780d10101000c610b00681c0d074098268201402c07d0085040c03c3c1c00a41d4842c40741e041c00b2070166640411600d42170400d03441074001400c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 330876645 1250 330875395 330875399
    0x912020d0f0f05120702010b060a02010b100e0d03111002160c060903081209150403080a0e030a0903020409050309101205150a14120d2001050408030f0405160609 71
    0x50400c0c40c0d588503191500c0c01980030011144058818403e0398100001c242c3c1310400034910610135003195804440180ca1140c0781c405c10310000c3c3c060100703c0403032403050303900120b41030003640b05000684071154020082e80700744a2589050b1009006190514418000c00c0c404509201c000d0005015540c0e520003040d00d083d009090030303618002190040001c10030960020000714100c0c07000e960820034810000038003900c801540d640b82551180c3e080d801c4901c04001c00040c15040300d495881003500c10ba06008200100f4075407922885298007000c007280111600b8009410154401c03980e0318482c5088a00e05030554001485d0110781c541080c0001e2a0307030614000000301402403030b41100340c01e12200143c40701c1c0c0c40003559020b0729000b50700a1a138940c608881560794001f80396800e002c41015100c81e941c2c0310170300601aa0102c1c01d041034402c030802020b1080c050500c900b038810b9401240c22030464485101513221603074098015a80d40c0b01c0c01d000301d00002a890b62010003030000b40c480c161164 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 330877895 1250 330876645 330876647
    0x31418040501080a26040302030d09050f0a0605160807050109080702120604020907050c012d0b15090d0c0b040b07031209030c06050711060915370912020d 68
    0x60050b046001c07a80c1112030104d0003e0b1154800e9070440800814800340250085d80d810018000c17640082c1d0700d446044c02007040680c00807454025140140c91030b04c9030010340001d0124605d11307803180d100050810030030041e1000124240e031410034401c0701002d18004281c2c440300c3c03c0d2220b42d1001d031010703200020001c08602d4000201180108040080c0105103480e4002400420005164030141702c00098087c00600007035202c0805095801440071190201810711800300c0d00707060b0603070481c5150030480b6030030346080c4420444903a103030002d851030030400740d0500408a580800031201031096480100b81160300d5009040581419560303240c448055040c001c0c920000036000a4900f8541205d05000c01d0748401d8001c54150803c8020483d5140c07040201c44403500041030701401e0180c1c1c014004003c001148201070180c510a00035a20b44544d004000ba0746813002c1e0f030351100e4031040c910b0b42003500c04102c0e10002c45425113000501c0c010382d485583d5404c140445440040c0c000c42c0c044000c1e2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 330879145 1250 330877895 330877901
    0x309010c090312030c1e09080609011109040b4b01050307140d0c02031b0c010807030b04230a110301180b0301091a01061106040305041203141804 64
    0x64441850101e081515589503c8094044203c1003020151503e40d41400c941c00341801aa20b90400b9140c0959001c0400e0010150314260090b103c49006010116120803014010b003a030b02c0c001500101c2c80d00e00c1481c1000001c10842d00c501d50040c044020030001c0d810f1841864015000c1541310001c01d1142c0300c01c1d520a8045040131014035000c803440300842d40d9011060383e92009250030461900001c4000501190150381113100203d41040b00004915601101900215410242c0f824107604c13405256070f1a02d02c2100294001f626410001d103000780300b81c00034007030390401074000103002004400c8183e00c40344d05018031700e49601040a210118080b44986007072060805407290455040c19038103425070101d6140e840038280c4400075112591740030741c0907080703807030344413110740c80e1525608003410301745000744644004601c0c0841500705400c800720b0fa00d4440c80d0300d0f82d1400d2400741800b1142e00b810b41118000e0f020080d03010780d101503580d2040010306440081740120580c202c9074400304816 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 330880395 1250 330879145 330879161
    0x50103180f08041505040b03070806040b3001020a0c120339030c02070b072111100b0a260d0518011b060b030a170306090f2a040801020c0102030901 65
    0x10001c5c204000c0081c0d010102c1079a810540604c0c0c54070740b50b00c2c1c00c8005030103441c1f82880c40d03071f000604e070700c290b4502e0f1540c2340700480742c14914440400000b042e1400c2030823400307522008000310703d031000610000750810600e072440045a0600080000781e079600036003541031002e204000107110100303006041c8070081c41a0500001850103120110b5142d0b0029103035011846030000141d40820010100329400342207500340210004513156492051400803c600c501326510315107030207810104041c070141401190170b00340e40034220a00d034600d80015000c0700506807203420b036124075003141505120030a0201c0340300c40c405944d0301c07515042660603070301065542c5200c09041c8040b10181c0448000b0365840701036a0ba03000540001c0d00c0d4a0f42c00480c0c28200c4a00c1c3c01070409044201100d819412800074500801041d0360550b0710342c0d118903c05408080543d99038001d00c02c100c0c4440b40e0010307980001c82e92203020003403050600c4d50b100c00c09800da030051201c46140ba500482000300002c000d10070180 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 330881645 1250 330880395 330880397
    0x17010f170109031403090c030102190305010f0b031902040e040b07030c021b100e0604030b010911090f0d2619020109020a060c06090b010e07080c0f04050103180f080415 74
    0x102c00341c82e07501421a0b8000e2510440d40c1d0008000218010810f001040c0340c02d034054000d654440800700b10410081d02c1e5114840464500800416244c0d54405203a080d10518181c0c14516110744d222900440a505910415180c0800001c16440306e200c25040c06584079160110040c2008000039090f240f5402c0407200710f6004e03604000000c0750081d50403000c200244d89514000c2c4000804072028100c0b03000041d00400006000001c008000c09014126150003c1c20031040d804040c0a4100d0310904080c181d0050421807001d1151038940c1031603001078030442502810700c003074103ea022182485800d1580c2c02c0c60114400c90001c1600c209011010b01a00c000c10000c03105900041e0345007407074021101046010205c08007007083d180d012400030354203d0001c64081d0317580d80010480e40411a14440010400000718907607079803050645081c880100205030606080800440040c100000002c0c000442e94150b039000c18180c4442c80c190301c0c0140300712a81e07581080808030209000c0301041c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 330882895 1250 330881645 330881651
    0x311010206060405070f050904271106070f11030c03011a040e2103090106231003060e0c0d0204030b04121818020a0302211605090a03030e0117010f1701 67
    0x503a0381c0e84106c48580c13042c42818213584840301500424003c0050800b01400c84001c80104d280f804078444d07a80c035007188103200303211110040b2400c3c0032190107000002421400044012030000c2c80050480610801c06001c65075003104100010b800d450310150200017007040304050180d5401c0c03900400d6900308021000b41603030342520b05a4410f00c01d4070b43c60b8140c402408030218654110a401c518014800394840e00100c08009940d03c000e0181941c400d8425118001c20880d03190080c01960101c8486002c4400103a8821400341160740c8030381c841e4462280c0c2008007200260201d0752940c00390380907981780d03d121210f44030003130b0159025109103440100400000c0000003007400341d41c4900380c4036450140c2c5546d50359078190040c1c0240340800c01c5400d00e0407640d00362000382c1c842207441f440625180540552074010140e4030380c1b088580c0b180d00900c00303a00074170229006402c80000c0000626009014000c03540b11009160403c2c4c006d08400e42055404003d00c0c0c1c10940102d04500e0020020 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 330884145 1250 330882895 330882901
    0x4090c060909060b18010c0312093c120e0307090603050706111009061d0a05100c050d020708160605010504050604020a020a0b060f03030c0705031204051e04020d060311010206060405 80
    0x54170740c3c0c10405054030f0400640001c03900c00c043c07040280704a490404070007449004402c1c640721800500048803090a40561601108140940342481c072010000e0008600d44800c152150103100c100307087c50b00e05124038407030142d5071a00d00700104801032030480c00c0003820302e00f5032510320b083c07189690006c1d08000d4250055160442c001c40d9003000e0320881400010000c0543c134001000c0d10503885070b007140360101401c1c200320590101d0300303189561065003642d0f49a40c0054245048440461150001903003c1c001440701030160b500509600380078070f504a00380300c0045804101c030188190704480146c0c880004010b182400e002c0d240c1c014908940c15410505c0c0100b00070f582c1c0d1644100900881804004566161075003d080c0d15417060150941e0b9903000040f200320b0b0388260f80d208050080c800c0c008868503440c00d260644041d030708002c14100413007501c14078681d0160350385a102503100d9820010840300440d0b0b032094000962013819240300700352034040007a0500c0300c0180424081c500704820 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 330885395 1250 330884145 330884167
    0x11404020a1409041b03050702012919212108040f021503151c0506010b1b190209070801050f012f0601051003060b0306040b04090c060909060b 63
    0xa42c80d0000d007035007126115214140041c0240c0190303c01464426010319404054030382c940c000300d224086d42c0c1c00901404030300303620042440382003000980f44100e10503441d45651601e0348980e5200700706d80c4602d505090721000c2c140c10b041a105400c0300c404114403d420104250078541c110a081010070161402c1c04050002e0715454004000600d0040204800303030442d0789140018040b00c0311103a43c00c0c0c80386030400d10352010441380282e5038401e01c0248414044940200c0c600d400c81036000d00a03043c00c1e480c01e1450303d01b0340c11440ca00221800d105074140c4152408010700c0804282448050b030b03088081c0d0043c0040c0c941c0241c640b9080020b12001804203440d2980402c03000c000031318202c00300310300346600f072914207440313950030500002d018071081d4076017100203440c3e816210219180801c3d20800f0805500b00d850503c20340c86c180c1d00c00d100140703581c03500e507100b030f10f01c0c0c48050008159802c443e502c031100f440c004d0f00500c000c100c81d0a420310a181c4c083c852030000e40801005240f41c0108019 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 330886645 1250 330885395 330885407
    0x6090608070e04090605010306050907050a140103020307140d05040309050415140a030b0f070305070f0c02090c0f0c280201081b0708040b0a0f1718120d05011404020a 73
    0x42604240302c01a00b40310345903150743d4040502c443d0010010030044d42c41e407401c4406090256103103136242c072840b4008130311850040c60750800c40e1160040c0d1603c50301c009006401a41001b00385074144031140346600c9003089240b004101c02d446040c00001e81d46400e2a000d0b1940c085030b08071a000c2d61610801c0552607042182c190705844098080860703881e1310308005a0500c010f034000905c1410910140400d02280b01c110a000c2c19064406100d5560390100440380e911fa9545210001942c14940c40003505001000a803c624241078480c90308030894040c01c1145d00c9080581c805a0128400d51410b215620015180514608501010744035580001708100ae01410f19031a80052030700f80300d0000404011a441c044e4001c0c000c5803036035034030403041115400c904210300220740c8103480d1000030b500c154024400040c0c0015941e10303507141c8a00e5442951017000007503000c3d10500e2607010303100c418000a094220919100403c441d810021814901c501145100d4045e40c01480b00e4982c1681000c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 330887895 1250 330886645 330886651
    0xc0909050606040905010b030706020703050106141c21050304020f0a05030307140316030504080c06031b031503100603150e0c12030d0213091404021003090302010b030d0801030b0106090608 83
    0x12804141c1307032510b007400c0c1d004002d0301050319810b02c50318800181480e000b0404500303c038000d9008112040c0d4514010303100310984031660703070b010291031400c1001e42d081d0b0040c800c9041c0103105d0144200c003066542c0720000d00a005110224201100304421840c1c1400303680d0b10740c401520405107640c40c0030b02081d640d0140b040020038410540c000c00000b1038082054420650407404440755070246814050000d030b110f401401c0d2640601100014581404400c0707901a0030f40c1100004003a00c41007801200e030300007510020500301030000d007010356a010045401e070140540300019010b40fa41c9405441c4500301480103004034109800d0303890340080421001c507064800d94805000c58400c40c2c03824114032610765401203091001c030b020b441d040a4a10f41d1419540e1819082107040c130b0030000e900702600200e070003d5011484505401482e03100740c0198491a05c80c1c000400e4036142140040d050182a1a09000040300300300100184101020a0760040285d420130740c035194100700004240003402 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 330889145 1250 330887895 330887899
    0xd020702030c220b01140f041802030c04030609081b0309040c0311041e0909120306050d02090c0a0e130c020c01050301030b07180801020a021c0302040602060a1112090105040c0909050606 82
    0xd0550608681d006c3c40040540f0041c40c14015500d4120151600158002d80a901210320032448005000034180c802caa001c2d8001d644610704007491561218041d00c011b080841d21182e05210310714440c05280400c0b000c00d40071030003440d07c0d21024010b000403103180004a404160620200104084150080f141074842c003034100d01c01220815506012180e09502098071030f440d0a0b086014810311003691982046156428030406554204010fa5003000c10b4020b5844081c0c90003240c2d85040f21001020140b865041c20300e03461a01c0c2c00011420132024850210003038841e0040000b80794180f08900044c0000d080042c19541103031500c503140b10004010000b0b020000394810000424000c1000040c4100c03002075648903216940203407125030404114114581c20744039171020038000e0084c1d50582e0990307801469582d9608031030320b01400010715100c054950404c0380340030741c514410766203102e680400e001280ba4200343c94550110790741603008800843c6415030400c00980d000c200f00e6041041 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 330890395 1250 330889145 330889151
    0x10f030b01170a11070c03110105030405061816030804080709150b0f070606060e1906120504140a0c03031d060d2406110f0102161203020d020d020702030c22 69
    0x40d15402d0402003014603462145521302041d040d08002c2c41200b280152031150741c02410a814010054840307000c141e8004000350021800120a202040fa44c20050f1004c1000c0380c1002040ca420080b150840381c20640b1014000135050064407000c1006000a203114042000f140c01d4000405c0002d80541c0a100c680b408000b62440c40d002ca09426121926048002000415030301e00014082540082d9154040c2168040901d0f00d189501e01200c2142d025403550341c0b407554a0440d590040100600031942508401440d0a41c0641008030201c4c20303114006041540c1d040d03080242120f00081c00340103040d0240d40c01070005441780003d07101c922440c21400325070103841c000c4405032400c05040b0900200381c00c11000500f05d6001211b00700410b1010103882c45503000c4201a070a07031150400c0b00030b400c000c0b000e5078000140c1030050050b4125940c5001402c2a201c40812416030f400000b200c20900e401145034015440d047c04101c00d1036104541c8851800c1248945d1180d41d808244034601280c0d0b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 330891645 1250 330890395 330890401
    0x50303040308091e040f020304030f020109020609040b030a080c01020c0610290c0a030305160e0a14030f0f0c040c1803031103250303050f040503040b030411041802010f030b0117 78
    0x101d02e104d00350302400018001c0c8241300c025a550070003500111400d6000406105604e81e020740103100d44070004c0d4010384814a01a104810702001d0007040c4107090305441405100404511a4030144c1815500389002695403d5003000d580e24100010b403035080c640c0c1402c40100090030340c43d8011044403000d9401035000810030f80741c9003a540220f440b04182030041c1420503040591590100788a200d134000c080c421240507041c2103507201000005160800b04c0504148010b50000310101c544403c008c003140c51542030010b03c1070800040102c00d481710ba20026484a49242138094280e100d2420710b420b43c821200391401000524003444040c0a005042c0820440b840040c002c071581aa8050404c4580c524035002c081600c070006241507001070715001c082203520400c1c011450003207800c0f00085003020309200c8003040381e0744003a0040703403207141c40840c00c0702c83d85583c0175442030011008001c0c5440b4015000150021031304400d450101482c000890816a8000f4410414503000c541800050f44d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 330892895 1250 330891645 330891679
    0x708030a0806040915060501091208030f04081b0f0d0302030c090f030f011a090f0402030703031206030209010b07030207060306050d1106090402070c0f0e070e0415030c0f060905030304030809 84
    0xc4410100076002503202492401c01740d84079084142103410030390726003081541c0c1d841b80c00d40300c10b0f51450003017100384100041071007802001041d6030041d0040700014680707161208031440c40c103a800300035600c0d40c11000341a420800c062100c1c02d00e654590400f91300d14600208104400c0c4a10300c02684192a520000c20044d103040100f00c21b40700c00d0340000c124a40360204010003947e14045420f11600003800084d00040040c9a02401035901400814040c0e085680a86102203030940e110041c0e96140400400760395040041c6000f440c031010615a50700280c10024108146030300590103060078690f04101c0c40e160550070703c50154014034480300d1201c1407000070b8003510601007003a0f8401c0c004212901403084010110381168014024070504581d1500032076410707081110403001066102d442d441c9213003072540081210300b031281e0701c2c40c3c0c2146c0c40390b440c945010382c00d0708880803814000c48c00340880c6800c80405009031208030000c5052030328668840111b403103400380844c003130a1960f40c000104 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 330894145 1250 330892895 330892901
    0x311100203013f0b0403140d05010816150507033e01090b011202030a060c08060315090c0613170c04050c030613020f0f0309030712020708030a080604 66
    0x90228900159580d503501d1580c01d0400310502c200c0405a0b03036558082d9060441c941c4040b001c0d40f454a410642d030401030315007a2076050f00030802c0e0140007140d48607551248224006003540d440039040010913504108000345055001000408072310b42c2c03000c1c240400206402c5a40924010b8034000383e6504440c80c1c11900000141010812940380b446401c107400e42c0d4015007100d4103c2051413440440d11814850700741c03650034002400d40040980107002d01c1c001e10249a070100e0014040b55400c2c1c41c5540c404040750300b95070311400003400c40c0b4203010700c504d81803000506112a1300310101d41c1c1d0414000003620703002d407070074154842c10001902c0310a1261115440b401484441c06008070204a41c90513500e4643c2107a140b44928900000134500d070754202d040c2c80c041c5801400412a068081d02124000d40c805180002150000d0000030300b00c5610364004c3d07100b051524061070301c82c8424034104122400740803d00c0e081d900440c100b44807075440013060300c1c811083e40c58018465200c800c00710b001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 330895395 1250 330894145 330894163
    0x80f0f07050904050f070e0a0b0a1416110406050a060212090103060302030d020601060210020a02100b01110a1a0f0618071404031412040f03030804110607200607030c0311 75
    0xc1404c1504000700d41030f1100d0f0481c407400f00382d20749030355060210003040802d880d540100d1004110a0141c01e0f48a48030319a000c1d05075415500c5c1d0703450704001001e2581e00c200c80d83c5040340c81c5079802c9080c02860419009041c020802a14a2032480d03050040281d103c8050054404544130f0105090002e41e1107608610021a009410f40d201d001c29640002c0d1211800d008178405446448c500120380341d0b0314803c03540c180e070065001d4071200d103030030b842c01e0041c2c46080480350400c6902004400301180c00e00a12050f60b10600c004168024404294014010700605010490201108000076a20b45014802a640b42e9400000c0581d507000b40c00d64518500f0302d440e41c00c100d00498080104000d40903510341080a08044407802c00300b80b8810b181c1c511030b5000e041040c0f1512002040001c0c0542c2885030000e110741c500211420150010070041d402c000c1e41594a19403000c82288818450b02103e461840142d40c61480c141c85030701c000d03055101c820303001000c011a402c1e980b841c1010034051508 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 330896645 1250 330895395 330895399
    0x40804050d05030a14090a05010809070305010e010204080c032107080c0303010611010f06080309100210241415070f140c01030e030301030c14060d0c020a12080f0f070509 75
    0xc1c0c20045030030880d9603a08080c1c2000f004c505101003080766954458150303806040300034152440141050b00440c0c0c2c25201802c00a00307481130280120000d0b000f07010f0f114503001e08400060320b4526105104e440d11541340002402600f1820840a084006044800e0700b55107100d0a981e03103020b181f400f05094420082640014000400042840e0740d0000d840c80d0411b01c00c80c0240003405400381508110b49a1384140d454680c01040003a0040c1041400b9202c1c14141c1e0061f12288003801c00c0c41c6d01602c0f05040ba038003034101100c0c03122058180ca01034660280101174103480f494990400031409030a01c03a034440840581c0030840104025884810b2000079a00140b0008405d652500013030b40c07561102240e601080c1040482c02d440d10000094038102c0e5005070351000054502000c008541c80c0361f8490362742200041044403145010303401610298415a40240100416402c0400706501141c00d040c082164200c2400504852224050b401181c0100000d4560700d481c5e400f500d480c428909003e03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 330897895 1250 330896645 330896659
    0x30a0504032006010e090c0d030f05070b040c06020f06070507030c020a0803130e0105060c0a110312030115080f13030f09090e07031a10030f0206120901020a031b02100504080405 78
    0x440d690300407401e44d040701d0a01c0b810004544880108503142e5600f200c0864010b4590814800400d20811405880314501d0511601c2c00d10380f5120002300f40812075055401d00611502080f040b54104203a100c08090b107000750040e400e1000b0b00502520560368040c08011002d071242d0b003556100650080249022011280e03a041178030003a0751030340036501c1140200301a40000144ca801c0032011178070350701c0c824005040c8801c0b29a55000707ca041d490a0140c06118640312802c4a507202c1c0011406052400340b10008002e50450003013540c1d10090082c16a01580c0b014003d4a1494080034050036a02d414801c00c170f0064407100311001c502603030000c00004e0070301e05204488000406e6400a4a010399107125900080c00f04a61401c02c003994a12001e01107083d007040420803049a44084500c010314042c5403408006098403415801e99560f01a6540001c10a80c1550948030752000300c0e02c0c2982070381d607101c401580030303465141c02400d407002151a01e00207800c2010000866000d410300030720074 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 330899145 1250 330897895 330897947
    0x3090b030109090203010b150a031a0a180b0102011e05041106220509071413090c20060709152607020601090b031002071a0711070515030a050403 64
    0x368041d20f480f4009038041d5180c103e840000703041105a035602071900d034540c02c2c589451498110b00078414058002c1030b02044c1d081080450395240384500c000d2484040d1751282d040200074860071170344c8142c5e405040d61303d44110420a031101d4252030380610711100000075a5926810820b000311101c211460f4440c2002400300c045002d859040c2c818079040a1160741059101c01c184207030700c203040e0380b0900425090f03010310540d4001540113104514800603009084e60392080d2140079603600350f41c03541c00b01e150715400c202e28101e80301280242c010084020841d5061a040103007101c1214000d800302e2101584d04211628080e454004003000ac4407980020000a0901403041b0b41e4282c0707400d001801441d000250b450020701480590003030040140c0b810034040040e1030000c1d8030084049030081e0680c40c02081030211a0240391087c0c0258030b078110480d22b0140c1960410605401c21441090840c802c1019036200d0b105582d48020402c4002503941c94606043e134800506c500900b062948440c82 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 330900395 1250 330899145 330899159
    0x5010303020d17010509060d020a0306050c0d0c0c020f0906120709060f060207080309100e090a0e0d03110d050402010903080a050a120c0503040b07200604210c0f03090b0301 76
    0x2402d0750300030b240e0f07850380e03000300c106400800c28400030300c140c03a44103200b030010454624004403841d0007a03100600c042042d6559070354500680b80101d070381e5612403c0104440400310a01d0141160111381840c0c000e250240580c00a00040f41404480340114001170010300152141c000030b610000f82c1344211359480745d540c81814054400d0740a5480303c0100020001000b600000e03001007511494000340d4202480c90707050004200a0312200420400090540350b51510764041e0140030b121101300c04600c0c103110744001450300540140e884200342c50148010b00143c100c00c152075506080003c040342075101d50004a030540c038a41c0014014039000280b11400a8200d001400c0e902583d45596405031400b1f000702e022201032400c2803020400c1000040d000800c0030400503481045420120100ba61207141000c88004000304400c03a1307800710f07050006004500c0c4061401c00781c401c8460200a50f40c803001082c4030f200b850300405900881c0954401c2500480f141000342c40440c07019502c940e52800 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 330901645 1250 330900395 330900403
    0x30d030b0f0a1410090b0d02030403090b0703020a0b0606130b131a03090d0806010504030b180115030c0f050307030201050c0c09040b0103030e030706090b090301022110081f09080702040501030302 86
    0x1d00c2c0f044000c4c006900007240100102000c860203a20042c1c10881c120041c20040d41c0024001c03020000b801c07201042008081000c0d20801c0e00990040000381407070f1400d100800c3c009407240b032003180c0070f11985600c900488101410b5a0f22054695102d08680b40d0040d03070540940c001d101840c9080405101c42450364001d1032040d00c02c0c1085650081c20000281c44c0c0380320640e03070140098410030060001c41e004c01d07040c0340c205001d180d1640142440105040c01c654514015004010318400304100740281c1001c1ea10180c6100140c010405141000003580c03014640300c020706000001c02e00b002d030444144420302c50090090051841490b02d07203001e420000d001d000c100c000c0782d480510700c001c81c180001c60200796012501c80c031420b5410003080c3d10032a0010a080c03a403640d003c00000c1ca03022060040b039030a140048541206034105045035550815054202180310742c01002c40800000c402007901340322142c2e0410010740a82c250034034010502c180c0300c029410900b481c0c000410554001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 330902895 1250 330901645 330901679
    0x7050a2705190f052115090d0305010b03130f0f031211090a060f120510030309060f02101e0905010212010611030d18080c0f010510121203020c12130b040302030d030b0f0a 75
    0x10a82d0110f42c8c01c140305034101e601c2801a950910800d20000f40340b14094060501101c3c00380c0481031092201e940c03000310b020342c100022000501144016407150405001c1c0103540f003180e0203214102980e2501141500d40244158010005072003440032040340202402010500f101d0001e0285e881e05000c01c60320300c201840202e000607030b81c3c0700002d01c842c07181403ca560300381154060701c20094804000000b401184c003540801e0792402c2420300b02c4101501c68a451207105200142e250340d003500340c3c118200c00581c0141c051000c02c00401860380004070489070382403040d280015030b1541c031a14442c00303a40b60980c024800c2c00d00250020504100047d0741c20300301e815400071310a958441c0c2c80300b00e014015110781158981d8482070075001904202130801500d0561030014104010740d5826442d24007401008203000e003000540140c0840302c2c0c078000d40940810140c1ca480c0c01d10b15408030759a00307040a120410940d6521070b90000f6030350580d0001c10058010401241103403501684041c1904203 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 330904145 1250 330902895 330902911
    0x13b0d090609061b0b041103160e070903050a0605130206040902090906060c0d05030901020f27040501030b1303020120120105041407050a2705190f052115 68
    0x50400103850f521a1102c44261001d0080d0200c0c0744c1c03036640d030715a04650040c3c001c0796402075a684c4a543c0b61000c0140382000506104070785031051400c58403440c1075074054072490420034800f0b024008604001010380605911030f50014240c2e4a0b0444070286800311180203501940000f0001010702a0390042e069542c0202c544100d01e4031802c04108030b6104114002c40940c1000c0c040d680418080d0020f550b000100100141c03422003c81e044210079400703c8840075000f05c1250f05540030000c103d0303086601000a990401c543c4d415a210414582c40c010b0100500c546440035410805100703400103a605000c403400c6800845aa11240e03549d40c002002c8030388d4100244000194602c1c050040c2041d07800c034121340e010035441e102c1003143c0030b90000d9145818401c000c003d41c40b920068044ce41c51100701100c1c01c0550724106420054442013889950611204403201406240f000402450498000701c41c0d00018142c07036200b00b51004046402401240950b1001601180c50b0807080c0c2d22034011 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 330905395 1250 330904145 330904157
    0x52b021005150103020f090607140d020c18040f0b010321021917040308040b09040f0209310f02180607240b040c0e0102060108013b0d0906 61
    0x36000c952400c44030222028801c0041c10380e18150300354081d50007090b0700750302d4080c000e24110b069000300c0c100381d2000100b03d07141041c403a03107800403100600200b00001e071188003409054a10000250b426804030702403100c90341c42100460104210100b9140801c1d40c8102c1901107503030f5a00702401c001500b181008601c039103103000000340300e00c04070b02007003051200c9011400b102500c2d180c1c540c4400c829100e0346000c032020031000c0080b890142c041c00c01000f960300c00b5a81e9107007940500050383c00d107040d100e00d458010712805034075540d00d400700351440d141c00d0b0150800007030306c0440100181c90200040580c80c9881180c4c00c0c28800ba0300142410301110300341d0b01d0211090001c2c0b01d460310451501401b00c00c6040c0c1010224800da80120b141c4070f44401022500c0041035000500f2500645030680108010395224522540c050000c41c1c01000358400030030506400912002c0d4408a02d0154004031684424000d0781503402802c1c801e001e21100c04880c07070500d00010241950b41c0701e00524001c150 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 330906645 1250 330905395 330905413
    0x9090309090e03070c031509021806010e0a140d21020a020f060a0203030c1e0c06070810080c061b070f0f0f0f170703060519060b0f0304030c052b02 65
    0xc0000b0884001350707800b010303c5801c0c0d490b50f202c01400b6601400c601e502c160716600301c6d001580e200054000c010f10300018401c8541813a00015105489201803a4010f094401d0b0401c110807032150851151402618147e40d00390740351a10740d800c034001c0501c2007680e0384000d0005070250780c0011200c2c8418426504280501c26403020402280280036a0b000160300420008403ca46040042d1082c1c07810024031807070503a0a416420401c0c1c0001801c94400e07032082d002c0040b000c2c1d020030700d1a080150001c41140760303411301e01100e03165210717a24800c0c0607070303070000d070400d0360481d050440003034403a126040c2d40c1345585952018401280900c144100003c0e242e80114040103c1c0340400211201780d241904071928206040850102240760600f1a009000002002c01c07501d0103860300c43e070900c0d072080e80000c084141d980112440ca4000200011003440014840c0d001c880c100c94019406040040f0514000d15003603280000400c1040540d410004150483c82d8061005002c401c0c12602580c03c000c0f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 330907895 1250 330906645 330906671
    0x90605090903070816080403020d1101020606150d0216020901080a050f07080d110319020f010e0a0c06080c0f070b060f0f03070e07140408150714030c030c040909030909 74
    0x10007207190241001a08004000207404c2c080d003101d40251150130047e0602c0d0307980c0c0005060014110042d9201405058814440c0d030741440000c0d403150040350722074201d003519803650b440d030300406680c0c50841da400034441c80c0340725065007101002e6500405200e001d603118844691900040d00044410788507540003c000030402280e104242c450140c001c3c030101016210840b90f92000c0c64520106000402404a1001c144480101540d44076002024094680c0c10300d1400c45105410111040e0041440100042c040381d1070402210b607945426441c507111000103040c00e21414420020b015000510030f010001d4a880c4580319200460703091055502030f20501ca507206c40305150543c5500050381c1030105100300e80038181c0040040c41c103660608181142c003c8140c1c4550071034003942e070000e010201d01c2022102841d5001e905450100b244e00c040450752941d600020300680140b85001c0002000324000c02c043c0c500030003900b070003400700b40c001c0e0030040c1c0000d41c1030280c1c45e61070f414010119000c0c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 330909145 1250 330907895 330907897
    0x50604150201180809100e100f18031e03110a0c030c050411120702010b10020a120e01080a090807060c030b0a091a01111516020f0607170402010216090605090903 71
    0x42da4000030701301d00c0d101c000f80800c001c0c02502100d200c280041350805c041c0d0ba86072805601021009600c4290042ca1162405000c4141d11400c44003102e02048061001a030340302c02620506140403408418441c0500d02512000c00201c0385503410300c00c4c0302510007400800080841164000c02a86221546500174001528100c0c03441450008003040f402a0ba241c03240945540f000541c0300008140b02d0103c0000c2e80c00400710070b800016440f40020800340b2030b0450841c2070411880c18030003201c805640c0003074201880204180c00300ca640f2400e440502c450b4408403114150310410401c0b005a017040090000c0c800403044500a500c240c43c04184400c0390301c90442c4407440b014116400c0d1400d4001180ca2240c042e851903040e000e1a00c500e0b0341c0c00f08610849004070303c01613443c1c40c80301030040d0080ca0808100c5421656500150600003190b8100c010b083c18290000c84441e1150350300c0c00140c0c42d00c804852a0141ca550503e40014196490b911440030f642003103d200d5925211625850344d2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 330910395 1250 330909145 330909191
    0x1709030a0b0a110a090b0d111305010212040305060c0313051504150c02031c0b0301060311130504020f04090302030903071e0b04180b010c0611030402090609101a04050604150201 78
    0x4030b65111170a03c24001013102401855071041400b240c01c05294030101c0247c0c004101c9283d80c245200c0007444290307018017455180b40300480e001c504103813071500d030540e580310081d007000a190340000128442d54284440d240c2a282c0060864050a4000c002210002000c8405407642081e0301604407851601d0b01500d184000c0304c0e80114140381402d40c2524920b00007459101e00d6139500c40b501c0c00b4075202801400015030040450342e14858440c000c0c41040103051003c03004240c034007420000182d0311003d000d0b510701c1d029174002409142a1805900c2c610502030300c40e901d13206500c00052081c2c64031551142711400000c551101d299100c0744c410040c09140a00362100d211752000c0240c9854030790118840100526007015080b03070503140d45040750891075200268a8000080005500740004001d401c0882590f1001c06403820710b20300100b03800c0d04d003d0075403003032510303800d42400241030815180900700c02080382e07a4840d134484010680c0d0101d401311101550070080c000c660b00c1c004010882d8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 330911645 1250 330910395 330910397
    0xa05070f0b211e010b03060916050703030f0207211e020604021002070e0a06032d03111f05010305190302030f0c07030b04050303150f010207031709030a0b0a110a 71
    0x20314203030b10144158581070003041044103002c100004680b0384954441540244100e60600f940d0f0b013008001d0060445c4e00614041440031103c07045400c00b507220b401c4400d5280c040c50001018210400b14601a214000c3c0191600320030211502c200c0d4482125154015801c1e101c540184c40707040c0381e40d40c21403003900c031003030140e0040c400040150500e4011030b107804003544140d8202a4031403a19100390345040d1045900203580f100c09004110450009450312191203081c0c8403c542d0403218a0b0214551481c000c1c2044005070b80302c13080e50020440d010740c1c00e4005409034260007560754048002e00091205a03a00d214a40e213034401548201655072001c0d8141e4055031816024200054043d03000c1074851200d031042420000101d4089000c060207107128002460383ca040404150036038881e102602441040f2801101c1c045a8001a1281c101d981c1b28800014030a012041e4491902595003c260140178440c007007410080707151011480b034924103004000c5000710828800041c001d400101c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 330912895 1250 330911645 330911677
    0x515012007030f08071a01060f172403241005060f0c030d06091b030c091a040803031614070206040905090c0406090501060306060309020307050d140a05070f0b 70
    0x400400c12181202c0602d81c02018210301e00740c000d58a1b1100f898501c0044070751903040c0c2c8014801c642d804904410070740c1003880c040407414100b000741040140701031721100940303032080d690700c48840510856148101004056890010300c0b81080c0340c020000c401341140c0c00070040d001130012500c0c04484806c3e660007901060600901820310b443c0e60f440000c410540c0c0c8004d00c0307000c6450b200b03070103284040d100000f00881c07a551010658803401000c169082e05242c140010b12034090ba0001c3e0b0581196903020508001180784800c3c0c0c8141d1240380c0000718035010000030000b004002095180443c0390300d54a1026100d110705001e1006c0c000c0c03043c029440b007401c00c4200329501d04c0703810003608270070900156446046030384000f804a80c1d0701e80c88500c1e09500c3d01e0040054503018441c40c0f00400e00c42c01c060018614079030029031101c049000e01032244122100714414442c0b0084289c02030101c80040b1010b9840c0d5040581d91440d141c4202d440040b40440c010685941207429102c1d0100504003031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 330914145 1250 330912895 330912899
    0x5090c090105070807050604050709110922020705071d010b040305060f0a0b030a15060504090203030403080a1701030b010503011d0316080910050d0e1504030507060f0515012007 78
    0x45642d0343c40420141d032801030034044040441da05010407400340e0b100e08014071400d450b291901c015116269080310b8002401d1041c485207448039035082200d005900c0c00b4846da600030700100c83c000e0040050140c150300c80c0401c0424007049036124409244c00b41c04100010b40c0c0c0c2c511604000b8401ea020003841c0741c1295003c01c8016003245455a000804201c0104401003101d0210307240ca03404407001d41c1c03030500d082864041031202e44204006828240c45c01d10440f240f94000ca030752849584801820340d1400140000300511034008003d41c4801120481306650303403414802c0c2c2e82042800303820b109501c1c2003aa41c002c8041305c250076860030461005142429a00e41c2d02c0415000e1244082d1342207202004800c00564603e4800952081661078090700c4541c0c4480d0002101c64a104202455100403062040c50002c0550103500c1541742c6851075494449281c0840941103075900d80c191503083c68140701c0004103000b80700340c4c50282070780d17203902c0c898280c0d0001508404103c42a82d55400c901c800f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 330915395 1250 330914145 330914147
    0x13090914210f0d0905030703080106020d140f390105070e041a061918080327040c08040501051b04090e010b060a08180d2f060a05070905090c0901 64
    0x1502021018200c640d09007043d91000710300341d5180300800c80b410b40002a02d5010182c0003004240504100e10051400744a40070010700704068a1800039484540030498920710341e403000403076040c1c3c86444a10380d18440701010440a407070088801c1040c00c00714000544011005200d040d01ca440a951149060300401040c040104018503050040741a40540c10301980c44040c000c1100c0307a4480c90188100210960084c54108002c4588080c020201010030000e200002611000c080c081040d035203d2010b42032040c00c1c1088052001d800034240300a41d034041c0e03004400144180d00440080c0201c0d5548001c03c0d40c07032044c2c03d0206610b50400d0100b400180c03525802010f041800d000000360307821441c0700040c1e4940081030b0400c000f0711001c040102c24221a1050071000b4500d900030006550050b201038180c5030702075011440b862070b210880100c2d5109910035600102e01009480e01d42c1809003584000d0b2804469000120303070303036180c00035031428007821140c8680101700e0014148844040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 330916645 1250 330915395 330915397
    0xc03090609060909151009051003020c0f060702030703080705160308061302030c1305150316120e1e0c03060a02160804140418021e04021309091421 65
    0x2660741c0d0003010500c00500d482e04e40c151454080e000c07144000102142c5601009803040a0035444020001080c0081007a51510009a0101c1100d070401580312118003410038600f0380a2860656140314500904c030421360044014112640240c3d20f03000c10f503689100c251054807490801c01e4686000b80c90600c0400d02c240d40b19074100c500100000400c3d802002e1001c240c1e042a100011100d03000140200e01e050350f41da10307000602080d0742d07416124400452900c0b00c0e010060a2039280301c107a1041c030034590710410000342e154041c20002c0140c1f05809a8496507072900012241040b68030705400c1c2040c500028018221540041c0242074aa6445404801941000d0582c0250405200e0032400254440c00504003030201401c40700c80003100075041100352a008151030800440f400c688201580b25180075071089690515507004c44811880810028403031012083d0f55514110000700703603a032140d00031000c01401842016040c5d1007182c01e0940387d003004007010441d0801da036030b40c00002c05550 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 330917895 1250 330916645 330916657
    0x20303160203040902130e011512021c05070302032410031e0c350420120109021215060904080405030a060b041404050706111603050c030d03020c030906 67
    0x11054030f040c030713540da0b201800380d801c03a005c02100c260101c442400039040400c486401899200c0070f56005a50203000a000c10041c3c01c01c003a000d68000403403281c080381481080d4040712406104000c0381c68824001002900203440300d490780504d030604a0401300c0d036030700101040c0740e00a01c00544003554500950041c2030b480c584043d20700c00f05002c1a1500030034440d10392101c1e650381704d059a200340041c04085440c10f00011860b000300e60078507488001c9401004560045d80550983d5400814805001a00914141c0c280e8400910f041681c01e8110640000c60000e1098410140104100310709a845140c0d1a81c0c51131030480490020318280b8100160740d41290164009601d003d80380c001103414130b21800000e0701c140780c0320304d9aa4802d040034446e072503802c0341301c18031020f080c100f580c0c8160b158141c9110741010001c81c000349942c6a041800100c1207040c501641c1001c00da40d03850300584808000441c43e00c240500d4400c00c0100e030081c021200e406683c0005540740411682c10444a50802 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 330919145 1250 330917895 330917897
    0x30d02030a0c0f0503040314070807080304030311011418121612171e06061305090c040f12030f0906020601060804240f0f02090d020d1b0e100f050102030316 69
    0x442c3c0440c0032810900003840a94080c40c1903025001518601510788090340e8800c0790240c0c02030f00104078260000c002c0c0c0b82920750600d0302000303000e544005640074190000314401c0085104050100110100302e03000130040014094509420941c04240600c0c007a0043c85140c1150518801000801d210030460b00c4903410f050011003010b0351420800310090444442148070b05003038441d00c000e248c60100d683e1180c1d007141d00515000d2418614aa000c1181c46076030301880e8080c02041c40508620290b402821500c0309852580380e45503000107240340c10b0103098020640e110107008550307100710908816207030743c3c1d00104500e03480e22000300d8103018018002d451191450b40352140d20029034501ca901c5c0d404030400032462440300000070048621014405c841c3c10720400103400d150326110081442d0b00c1d011143c0380081c58490030041c0d1098402c4956042d03c0000c50004500880c0307914038203000d90341800011044c0c6807158000034006485006150150b030051001801086000054419030141 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 330920395 1250 330919145 330919163
    0xc170709080615010206060f0d03080a020c1006030605130c03030c050313080d08060a14040f021207020d0306050402070c1202030703290f0609040312090b0a0b030c030d02030a0c 78
    0x140d40a042c2c1414029612011461200079494070503603410420650050001c842010321500c200e000110030f07002c0c0120040903c644540012000c5100381d05480d101c2058905944010111020080c020f284902080398401c1c03402c004906000f14000d2010718143e40a0311031a00b0302e0071074400741d4104c48807001c04c549503c020024a41c0b00e44441d000d0134000c1030307140001c00c00e984580c140509001d00042c20203002e08918a410403038403018000305030203844280e5000a04c3e00c070001c1c1c10406171089058a408800d608818003030300a03400144001c1e100040d5400301b0410387c8a0b0100801c0c0c3c03243e82c0000d08041d203a403506002600081585500d928402021507101ca9540da44102c00142c83c0424071040c6400990400800c5005200c100d600c08d0140345e07410040d1401c07400041c0811405803001d800c001064681058108a03a03001c1c503610380d00700c21549d282c5d241c54110300c400b61006141071802801203500701c11311405c000600840c0707030400390051400c02c40c1001c070403503220304181e000707881c031500b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 330921645 1250 330920395 330920399
    0x1050d02190308120702061501081b0c0102131806050d02150d050907050f09060901150507060e030405040c031a0108090115030501020a0306080a081e1218010b040c170709 75
    0xd0440000c0c82d403200b200400720045e2600b0740380030b410820000c0c4460081031139803622201a80c2d116210590000030f58841d000b41484462194115018880034002c56610000b16090481070b50900c00c1c0848643c0c00c070600c1201c41060b540030a032000d40c41210381248098104a005140140504181110081001c0d00780202d4200f4102520f40556a505070340c3c0005105100d941400720b185013000e04107a8901c0c005080c840040b4100b8041449481c1c1681c181c1100612400e03c6031007180c8200c0e0f003011081c0b2114002584d11500ea40c414441c20f803003145040c3c1c5a0000e98024081d0320444c8155201103009484c0722001904c0030342008029410f80e55032680000c59451403000d804000d98028400161034800c0540080c048a0300f07504641096400a10740100046a081c121034402c50b50034000c83c50100c400c06441c403903005800d50340f01030700441c80820207c42c00141c1d49440c038942c954000d0200e9001001844210356140b011000000e001074480650a07034803106942d0040214a80000069 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 330922895 1250 330921645 330921653
    0x1081614060c1911040209060f07020f0604030606152c011404030f110f09041217070512010905190b030f0706050d0501060914120a021002030406080f01050d021903 72
    0x41208007600083c0c00120340c038070500040710b07200002c41c030040c3e4045151a480c10005046402028007035040b107600003441d2710454641c10f400303203051000a804591900d4980c940b20010740000c3c000c4100b110180c01008031000d11a0980c01000114034804540c0c0000c00c8520b100c00e9a0320f0301d05107042c0580380982445a0110400610055001350b0504070b000401d4078100c10500c80b071a00141c132401d0050b0b0402090ba03144000941c01681c0080c7c00045400d2120b400d039107601e03020802d40c8840c11218108046c1c5a009030051260701c2100f880c485050307803a00d49010840d10b090b80c0100451a48504001d00a00c3c1a403005403440c400808440c0c1d1040342600700e80c58406c10341c01400000308049207010884500740101805020301d81000e04055003001000d022840307000c01c82c01d1081401c1c0361703003038122101404401d040c160050710901c602c290001020f55260b00c54400c2d10001110000000d80c44228140c00c98180e420050500c003096100743c0820540130080d0044001b0782082c010004001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 330924145 1250 330922895 330922903
    0xf0304111f200a020303030112061b050a081e19090b0a20070f0213021e0309070806090a03140f03090109110d0b041b08010f0204030203010501081614060c 68
    0xc912070360380c10030040d041520081c410880300681d800264050103c08005039000300903039054410b10080024000000e003001401740407201d0b1a04614000301e82c0070100c0c554002c006101412140c0c5a000c3c02d41c41f0040003900400d944c4403104400e0b420000800c1d501948041e0141e81c0071f030700c0700700032911000380e460311000c0d0902541c0410583e6914600062814001c000007888008050002400d111080d104d41c10220f44407440240300c0c8078000c91100c3c0300c549a9041c0d6409404464940c0c500050fa100c079440c003a441a6840741c011300c10501c00156000300003650a01c41c40f440300183c45903443e607030b0f001e64034514803000031030607050244416601014018050343c81503100c10f0000c070b6003659905215106d100b11100031030003503040350305000104918114507600690b004060103040d1003003080765140800c0300d170020002542800e103150b202c2410303a00034100fa68002c070000c20160741c0e250003190307a030702071502241c0640070000010443d40300b8440c19442c010001500c1c0b9407401c1640c0d01c2c0d040c28 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 330925395 1250 330924145 330924199
    0x120503070210290307030507090915150f05101d0612090303010513380d0c03060b100f050c210c0d0203040f181812080c0f030411 57
    0x640f000054660b410140082e1400700c4000540c00350032030a0554070340d2501c0c0c0042d4041e98a242d40c80354800000c21091410110b44210903a40400050b038103000001d10801c0c4074411004081e0048a000c078051410304441803d520701134036a000040d503940c0f10004081c0356170560b00d0340143c00740b04446024038181102e510554808015507600d43c146010408490205850f12808618010f11a0f10740b00c002c5002c0d09207004600307030a1600348010103228008018805200b81c014600c0c010107000c1001401d1604140d0b8400c51041c400c0020600a01250024020503c00003c0302d070800b007414140600c000b007101c01a05170588109081d10500d00c1d0401080755942401c0c0000000c1c031041400d0103024441c5110781c1c0f44003540c030700f524214600d80300b00a40d00a465004860300c10701c0340ba0500603030111a810314a0040ca140c2140503040a189540d4038848034004200d40c0c40000700e4241c0c4440450315074558a141490075601c3c1c070780322448110440444180c011150224000d1000c9203040c036051 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 330926645 1250 330925395 330925421
    0x41401081510090305121201030b270a0203010e01050603030f030a0902060f0a0215092e050411090903070b0a0c110f160b030402130203101203030209090106050304120503070210 78
    0x25180c13840c0b0b0151724003591080e104400e80b0080c40010340b4121945e009030b04490300040106181d807a0b507200031010060b0091484030100c1d45440761003d510022038a500d946001310300070070820210200742c9007a61422110741d03030701d604104075107107150012502031a000002e84000042044165012610550028601d00b610403804a14011500e40c100101a04118400c41c440c841e420200146682c0752801c0a4084c45038500207007407203402c0300c0f0030b241040c0054500c070280802d0400341015000903d20001072800744d000200000c140f524008201c07072502da4403462082050342c070252844010541c3c4440d00c0c1c02c000b0624100b0740781da28100880c281c024915005054080d440c4450745022002c1c82d03008010200c010b10030000580d0760b58840c00d0041c0f9010f100540c0da0341c1c0ba02c0e440d016681c1c0c150420304800507007200c1d001c14150300d0ba0140c15100d03005c1d0750300800359032509400e5807107000840340140104501c401d8140f13014401e0300a5900310001d801243e40403d9510f0130031041c0c614944580c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 330927895 1250 330926645 330926657
    0x30709060b09100c050d021006170601090c18030b04020117010b0901030207060b19170a031d01020115031a01050108091e0106170307060c1404061b0b160212041401081510 75
    0x5048c01d80740b4440c001c001e045c2c1a51801d2040d41340079003a5100d0805203e12010b032a960483c2188190207522004260b144101c81894100c1d100d01d00781074030b42001c1d2405d030700045200003221900c8043d2211103068a002804c2d150420150380011000395005401c104c503619196060180b1540f00d03500150710042c070315980c2110031801c3c200000320f03c404a0b607810780281e03c010000c401081d0024042e00140100032000b031450307021034005034098070968000124001c4103640020622801115150320395002203805001c9036681c1c801102c0b01d00003690516101d4001082d8a1400500303010003401c1c00400300700208a990380e5038850f6080004803020100c058100054440400a8502c151151480c1a00f0b2501e56089410b030b090f411b600a0f406000d0500c031080c00c62140c104c032861440501c681e400524090a0f24000311000101010200241c0141c0304d07200003819070000800a880c141c60700f5a500300e00c4c025001004552503900603040c250100e543c65249503081d281c29071408504201070300d0350 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 330929145 1250 330927895 330927913
    0x20130b0408100e12040b03060d0b0906042f01270b0901081303080610030e0607050a0215061324061107140a030b0a0b03010905010b030709060b09100c050d02 69
    0x74152603c081001c0b0450b002800040301a01c4050b06a80584190003141501c941d01d50000c030310107003a13058000d410780003000c04010403580000740b140d100714482e4003051380e400d103070104050b480c1902060803200b9845100d128003941d44145a100c0f1030880940501c401591185015401200c540e080320f8510640020b04841d10f507001740c1541c0d0000c0580144805402d050b8800078904000901098400e00403021410802d501c04d40040003851040c009468042c1403004000e130a55110a00740809030040104812420304e88000143c415040900711007000f1500d0300c0c00d80010040304d400c00d0002d40000403400d10302042d51886001404440c3c4500040070740794420b0b54900b942d45e601c003035902400311098500c035071540024401200c3c0d01079801c180d03984a508400001d4000489025010341c0381c0803c0900748441500441006981641034501054440c40d141d400e0701d1190158401b111020005003625003414100300802002d81d19041301051820fa85050400741040d07020720060b03100c0024 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 330930395 1250 330929145 330929173
    0x1030b040f110a03240510020a080d021306030203070c0b09120705070906170307063305040b040b0a050d0c0803031501020606011e080c0c121c20130b0408 68
    0x26840642d01205500c81111007041007a005002c1d086c001c440c054030705108410b034030600800103084050b86c4002095121401c00c100d080003074000c0342041103400400fa100003030045c0603200b268007658095840007640700e2541c545040750000a0304034050382c415482c03526410131540c0c000c0e05103140f05401500442d481c050200c001d40313040b60003d0100d55244041003c1d401000400c41d0707030140d44918042940038003005100c00d1842007400443c15107046880f014140d80c01046810103841045604200322b90703061041c40100c03221203074042d80004a2040c2440b151070706005082c03410307100e85480343c03080781c42e40d07022800e5800070348401d8200240c00e4400002503805000c0e02c1e501407401c1ca48000704018441e24034002d800881c101ca018030800d46c001c600b09444484c00c94910901c1c40040340c000060003d00408260300245102c0303055801d6645089005980d4040c0b0200c000d40ba0060b80e40c500040c5588268039400313072034245240d10920038002841e20843c2e014000070182000a80715901c0c42d032076 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 330931645 1250 330930395 330930401
    0x203191110030b1306050907080702070b030c0705070812070602070f060e06012124060924091a0120060f060f0d0b07050c030702040509030a110c090601030b040f110a03 74
    0x6442d0003001e0800340144800e13114800110307171040782450227840c0c607124050140c0c10310456402410900000104000c00d880e03000d8010311010313226000320762110b50b440c441d460302d54800400c501c82c6007004000850100d00c594000e000c3d9280101c003611440080e42e61204221080824004025003000300100581d48144503d020a22401c90341c2c119809095603480c10110210030700241491001c40014a800c6400c2d8440c1000e0241c001082200c19010380d040c1e080c3c508010456840b6003e0700b04003052490803402050b1020740814600550b12511500554070f0b1000c401004a42c3c407081c00e0a542044020815580150380d140c001d804c003400c00c1c00922441c64110402d6a010303030007050300c0c440081c074440009540001c0034036089032030301c940c4200c0e2401e40c420780c0c501a5004d804d050134400d402c1000710003402036011a0300e0302c06860160140b11602c0d8141c1202407a405010040041c0655000b0b1300005504d100c001d000080d00c4282c086041c040300c502c2c8640c0c41529001003044000207030148 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 330932895 1250 330931645 330931669
    0x5010f0806010e0604020d090c09021c0e030901030c0c0c1202010e0d03080601030506030c040624020703050a0605060d050f0a0b061207140d050d0203070204060b070203191110030b 79
    0x50150070250304110240908070b40c0684103d00850b80051080b030000321581c081800958030680c03002600e940e40100c10060340000740e00c2d15001030705040c07207070780100799100d06079a8030446800f075810031038038130015001407000c03a41c49010300031580b02c1a00001d0400d400d01015200048201c01100494000102040d101c2c5503901c0c0110040b060328004290040c1c07001f90302c1a403d02e004505681c0e840701103030410f00e540689a0300700d403c049010442e0642c070403006056240f0100b41c19900c420b0b40408a03568201480054090f401894000e400700740c1c03235005994440009080d09072506c402d5030300e680c600359003080c2202154001149480801130600b00c1705402003030843d44070244094440030982c0b50000c612960038490f0201075810780c40d44500300e0b0142d1160f001819606001d036400e60181d2282c1c002d41d41248124034100300410346d200490309489045070080c0080c100d007824611100800202950113440c41126105004015074031075002c15240c1ca5540d4000c11060914401e01c80920004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 330934145 1250 330932895 330932909
    0x30709091503110d080c0a080301080f03040b0d0e0c1002150c092b0f0b16051207081503030307030903080109060311130b0301140105010f020c01020c040b13090605010f 74
    0x10001c20000300b040c02d0b5280704000412541c903007064a052800300354a03c01c400d42c1403190300030b0300c060340c09218040c409181290088000e841400b401c51850380e4403032080d40a90711500000f880512442c0895a000712402d9407000200c1d0f07920b00181c000a0b09001481c3e0000c80103a004d0507101c03100d5800e4181258205c8034085c0d40a007012101e10003e82554081c030314800c040140d1180a28071051024071b946441a00122101400c55650402c107440103800c40b4044482b031180311302080c0c102e1140c030450302408503c5402041c96150308004503000c84018110000c0701402c69049102d40e034090000350301940403a10005070003002450b0203003203208140e00c00100c20f490300000304085054510103400100301115a400c6262031041c4442c000c0c0001c2038070345e40543c601800000d040007007210844c180c4d07500343c940d01c050503070758041281c1d9410b0302207500d030041e003000d908488281013a8004c584807e8005100408040b10210f10741c085031845202a01d01c1d98440f801040140100d86501015080c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 330935251 1106 330934145 330934181
    0xc0c030f0e0f04060e07091a0a110c03010e010e1902060904020a050f040e0711010b030c270c0409060f03030512060f04090f060c03150b0c0705030303070909 69
    0x126110008513501e01c038042523007401001a000c0040c0d11803645031425215a03c1103420307111210418540e80324114900071950b42c28041c40914001c0380c000064000d0501015515084240070105000800c802e010400b51f180c440c00c891001030292070260b640c040c61042142c85105042846902c84808940801c130800f0f8941c9181c042c2940d03aa80780c600030071001100b0b00300d03510802d010340d142e40302c07101402030b5080100399100c0301000311071074449291604000104e2403804407030b040411100021f06000c0f1140034814000608201d4421060741d41c155540601240726505524100450750000102680c1e120001c000702c0300c0025000317005540c06d40c54610f101d0001003034100d4501e420108801881482403007088030760942c40741c07096005481c213030441300b8650040201003c2c82c042c4110100c1d5688042000f1409200c05540b5100228681a200313021160300803090100c10395 = true := by decide +kernel

theorem cover : BRFrame.Cov 330755395 330935251 := by
  have h0 := BRFrame.cov_init 330755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 330755395 ≤ n) (h2 : n < 330935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
