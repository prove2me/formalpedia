-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4251
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:00:36.742212+00:00
-- url     : https://prove2.me/submissions/b44ec5d2-02ee-4f6b-bcd0-ebc87d49441e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 764388489 ≤ n < 764568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 764389739 1250 764388489 764388491
    0x3080a020a020a0b040e2710051b040e040f1713080d1103040911190201050a0e061509090102130f1503110f0705013b03091503070207080d03 62
    0x9038078218a8031881d04006014814007a0341024540b120300c404130386025103290080c5801110320405040742403401d004100c030718400c850100288048000c003c0000b1b4800070311861100b81550917100d501c90854045079900d07460b034051581c65440f118079035450400d041700c0c1d04440d68941d21000043e040038040c80d80821030003901d1a460f10202d58078103802800060f003808400d0b41542020000482a54202c408042e0085800381a94a0181a900c16400b01040c0f5485614149101a90542c06540b00e581e00084c100041c1c01c4008a6965070101264000aa8006800c201060742428804143c0186c1250000b604221002181c1e018548254010481d00184000c0c2000301c1e07134405620024808003801e04101e102c14030080410302d407051401b08034003580001039801c1049000d40c88a500403042c8107014918100b9001c1002c222001c2502907124003c2c450030761901d4001c00300440f013201c800203010b88888a030311106c0303113030581001b40b2181c254003e280000403c00b80600c0b880100840503a8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 764390989 1250 764389739 764389753
    0x20070c03140f010605040e06012c0c030f090a120c1103070605030f070509011707021005010b041e050a050f031005091e1519110d020c120a0e061303080a02 68
    0x50b041d0b084aa442e0300c614400c50802c4aa07404001d030201e0382c541501c842c4800680c80440030a128117a00200900b0f07a8484030008041203071044203100a036006602070880c0343c0d065200c00404559440c00300001034000208500364240181c040c0d110013004520901e100e11290300708400081c20001541c0c090b03004604004108004040000c43c038550010b007c0c1422800c001a200000345107a05c50164150b6042c94007020a413118000c01800c00900761941061190b5a1100c41c0c20b0b00315042445020714124810b50384c3c20048160046500175500c000e02201c0e419031510042204006007414415014005c0d0341d03c05252465502441e44a10024001080300b8111001c20203034410480c1c0040c007035a0005009101141042800b0395000b8021060a420341d55001600800505485134a90344400300098480d259034015006000d000503c41c0c20b1701c45200c000091503016102d20045040010300100c851200c61070b249001e410344100d1546800c090548a503111810365010000390360159000b29 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 764392239 1250 764390989 764391013
    0x111041503050c1603050a050c031b0c01090b090420070b01050a0e07020a3002060a0f060501090b0a09050a090e060108010c1d1804150f20070c0314 65
    0xc05016000903103e180d95140001c0e800703220200075010613000b001c0150005040011030b100b41d050300c2e00d401060064030381c1c80120040810f80d88031649950b41c00e600034006200c0c180d42c0105a810102da0010108501d4180708004010017042020110707589040c040350b80b4554103030700002501c6114412100407146504050030444103550641c44484203008580811070328590200f410f55146a1020400c4500b003074601c07496084a081d966101141078407c9911280c80b1790014030503001d90010001002114143e050260030354099000700f60118001c0b90040045014240003468400c0f551715180403250313120000906045429480702d4039590f01c491620301050414404203006010300c8008004030800040c0240001c1120303010041050402c07422161652551000d0340c5100180041d40402882c0c00c0c680526540011000140032078a0040d501c00c101d510b40c8100d000100c0c80502c1302e07005000c80c4401504503800f00c0000c07520605501d500200081078003d010300c401001c10041c25a1611503 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 764393489 1250 764392239 764392241
    0x30b0c12011e05030c0a3c031a04020906190e1302100903051b06040b0c0d0f02010e06040b1e0a0b18010b041509031e2a0b0c0111041503 60
    0xb903000244650403004103504181c1d600220718045840e281410720160b034030281140d50310401c5c5502680e210480b550401e50400f1042c04140c1502d12a000b2010780601e003032018481d21a00300c9009405c0300707401c000b041d1b01e49080d00150044d0303005d9000b00300e5503a460710103040c0801d105031440302486513142c1c802400c6217002280c0842013a80d074540380841034519203d96941351008a03800c24600d0158800b860240c4800e422940601615a82a030ba600c03208a4a41d0381c5881d210301c540e00044007040100141441800b0f03110340110540d00400254076161115400540081c25005aa5010420b000341c019800c5407498418801180001401e2206506110710030000002d90715000b43c01c41c0c014030074000124160b40542c0c10062108020300000b20080d140c3d82e00c1600090030559105080c03070444d4600203076242d8068855a0390411610850000300c0c0001032240d010045104411018880c0420100290480c01a803070008030f61103003190941e80c01c80d8000d40110701d85048800c40c0d54407003905 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 764394739 1250 764393489 764393549
    0x40b06060a0806060904140915090a080307080a060305061302010f09050a090216020904060209100503060618041d0618030c070b0d06090509010207030806120304030b0c1201 76
    0x2040e60351a1500520741d0300180580340052001d44545804105a03e040c0c849610800c86c00c48280708444650802d0414156507000000441441010540004501403400300303002e4005a800110682075858200c000d4800d43c0d801812081296038400000010a0007040b0540c01242d0070111245068820300004245000d000102e1b414051b000a0400007915107024800444851050050301d4505c002d013a0403108086080c0070354400d0913402840103000a0340c0c010316480e80111602c0400603000c100a40d518001100c032a035000d181031042da40078076000c494546641900800020f107400c1c1c43c0e581401c0c00fa401ea503802015500c81c000b00a0315500e090038402040184400447c1450f81d05103a660f607407111402a00c61a83c00462a040800e103281c1020000d031040c0705003032100d881d041c0d1a190007500000d8090380050403002c00b0034400d007408200b581000c4c9020015500d001c1c01c54a40d18606400540904080e44007041014a04110301c40c1040c081c1c42ca80204c045a046000306480360755503 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 764395989 1250 764394739 764394751
    0x30a0f021620210a240b010c0309050f0a08010c27030804032a030614070810120311030a051b071d07020a0609030905041d100902190e040b 61
    0xb068118a6407603524407000c041c0500c180a04007140f419406941c030f00380f099810000300900c165001c0c2d18440d0b4500d4400d1905018050b8003046000c215030011110483c1901029011231440780c030602003811704403212261000060a50303040203a660414500711407881d502d000014540c0000703210300c0542c050014440c04804074001d00c2c0d150031a12203000341e1140384030050003513401003078241407041300700441d180090000380b0040301142c0d41e05085001c0e065800c508008218210001a8894065010f5600a24a1031501199141010707140c016004426400360705101d1001421b114030007040000b007000721516074070f0b141c440e5000761080c00001c80c0080c030052160400c3c0d200b03101e441e80e503d03c6e850071012007080e502242d0301c0740441682401e2040b00054080781c02c1c003041c0002d00d40c001c65040c2c2100e009440401100680f000070394440040d5040c4130065802c185408589000f00342c009800407030000301607203a00e142d080c0400742000d180b07a11a04518051200f0001400301c1081c00650042c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 764397239 1250 764395989 764396033
    0x608030301081203040219060804020111010c021e010b1c0b07020303250314041a07020d0212090315010806010305120a080a0c0e030d0306090507051905030a0f0216 72
    0x7504240d44075844819100c0f640298440100000d415592111f9881405005d000340500906031902d0b00280250001c403001c0e400300d4400e0b11960000c2c1c0051180c5c0114a00d541e0103002c0c150003244516240c00720468440700c540d901c07600824202d50710900405071001220b140302d030a001c620714081840400c001d10400940d003081c410024010b8200d0034a51901c180c1e404100e02030007040030b0a03070081001c0015842c80d0b00921040004110100081c0c0b5030304603c03d0700101059448820482c1e68001400e0250700581000001c013015490800203400340d01801010384103030011001940e01254001d80c041c2240740d100300010802e211041c001244000402e48610f85490b0039207202400c03140d005001040c4190359105802e0400b803240800030320108005080d65000b8404000041c0070b0701142c050b400c4030314a0034000c202c0090041007140d1400f9080c001c04003204250b00001c1e203c80d000240010300543e1914003459401005200504101c1280100988083c0340381c14811612034442a003a030213a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 764398489 1250 764397239 764397241
    0x427060b040e010303030905030412050312182a040920010302090d110103091202030c0c03061e09070302040c030609050609101403010f0905010c121a0d050f100f06080303 75
    0x10504100c0c030f040d41e030941004224081c817403030018a14807695115181c400020100c40d402c10030003000801c402500f980e01880580c4072031841501c58030306044000502d034003001a005011114601500102035402c3c1c19401d4078851030b0224003079602c0784004490b584844400607510203018840d0030341001003807030110f0a0052100c041084044803940141200c0450300303001040742c1c400d40000305159448100103250f03c000d03500207550ba400240003650a4003c1c01202d00301420002012072090407500102d41d03154804400f060320148000c2c1059005001d010004030150f100c0340242042402c140d580041c04614201c41c02044039000703081306100e68414010b02c0b543e490780401087c00c0c1c0f4040b140c5112100107581c00a801441c0c0d0100750100f0b82d00301420030301401f0040d40301480403520354981c002c62124101c1d106007203a06542040d034102284848904441c240307125402d06007841002100d261080049101345000c0e60380340303440b040a80318201d6800d181c0545c01907000402c02c0700011811 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 764399739 1250 764398489 764398499
    0x30106180e15030f0706110106080f03070605040c030807030810090b010c06020307090f030b06040501050607081602010e180108070803090d060c0e13020306031c0813080427060b04 79
    0x70940e020302070001d1a0102d80802032955001d1003680c0f8020348003000c0300c0d0600d90320394010388200c40281001509503e81fa0340003c010b08007262904000c201c2070080c6103000c15a5455000072b0501510030f0f10304081b01100400050300d100b0007000164042c0d00d65681c186041c0007030103c18070300c03074001901c242d082000a0700280d0b0040a01c2030584e03800900580c50765505641254450035a41c80406014941e8400000713101d155900c1600559081c1c07801c0c803003603032104140840361055110003858881f042000c0c030b44c00410750a106c0001b0b44140341001588481800244c0102e9204000c0e01348845080b004000118007000104010070780c81d40510700b881030150000360710303000814001d40130f551959032070203145116442c80701c00d4000080c075907218540a0203852000750400c490481c082d1051200b050408915010b0320000f0019503541c800150390317440351041000c10340c00300c1111114414480800e91842d5078590050805000301000c54402c4107602c1d4030180e41c07056202e0b1034286020842401 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 764400989 1250 764399739 764399759
    0x31707080d0f33120f12030f0612050f060f190204030b0f0a14011a0f04090612030318080315040f0f09110a080d0c03051c05010915050616030909090803010618 70
    0x3401604120107076021b54120806602902c1e40500300b52140d89004030201700c1080b82d00f02ca1100500074821290034040b41e440c1599294001c0c0e458102c3c0107032000c0007030040c611100c130302d03060b8403102c00c00542815a01d03a102604000252000b42a034000031041000c00c0802d4459049005107091880c3c006500d002c5810b805007042c07103000100101d0004681d01c1000a00e0103c8001b01900c1a00308552541c80c0c1108520341c01c0020220002414a8800d00014400040c1210b205810050f000e145444440320340302150301400b02c4581007a03d030083e500344041c00303100e030b00103c4100b010003080712400d620b09500109030f201d65091007501070540c2804005800182026680304c3c43c102002c0442d0346040643d8503009040341c41b40040100422800c684040e90800ea04848115130188854142d104500380304a11500410360410f00c01d2108a040d43d0f09000d210308400c2c000d08180c8a810748070f0030700c178090324504501641c071958004010004640e00400e0031029040d101e640d02041d50609503015 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 764402239 1250 764400989 764401013
    0xc0905161e090f080114070221070f0f061a19030204090c0308070812010b09100e13061202011b0c0302090703061509031707080d0f3312 60
    0x4200e045400c0d103400060340140d080c1c40140003540a0070803c2d65442d6881c6001c2d00b040c1c50240380c07440040002c160404c1c0001682c0e468501003100c1e038000c1112140b180c0e44d13507421881d000c1d80c41482092040c0040743c0f0009000031024010170010801d0b2150118418030f43e4150b002242c019040740b9005044811300032039940540343c0c1260085070305111410b100d2200341d2180c01c0034102100000703d51041021103c01840d01212150b01010144e0b69641c40c255940a0104440e070003802102076406090310894821a840c0d00080580600071000e8982408880668200100c1c0a141d484002c0640d0382104100350350290034041c2c0e00072643e00e540c2e41074400100380f000a0040011a01180025000e90003032400f0301500c440100101500b410014490343e1a84004c0d0ba81c120003500c0e04900e1303140c650881d2005500208031500d0603000d0101c52008001800441e0032155035503080d52207c2c90f06041d00f401d014500400c8a4000002d581c0c8900007410700e40c040c2d05541e0b0b103041d8010020f11020b01036 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 764403489 1250 764402239 764402267
    0x3030503040b0411030318090c03040f15021614070b0c0709050c071e031106071b060b0301022b02131412010617070b04060206180a060204030c090516 66
    0x10032943c2c48501e000c06160803030091485d41800040351045950300383e089203120080c8101c038010080c5d1640c01d8100780b10711042d070b8058000800f010444020482441a581d80c941105000500c0e02e40d950600c0c1000e42c015000c2102c0b400312400803100303100020041d4202800d4a403001500d0301c2c07013214045648520510a03100d01503120f40006003903001c800182d070001600808103a4960130a030780a007107e0381490070103e0224001d84008000c02c880021f442d440b4200c0e80e02d400c00500c043c0000c1000022403800100c0e600ca80350850002e6546083c00500380c025485a0403602c03004040355050380a490031408004e030130744144152801c896610b0001000c0720112102c440c80780b51850301060309142c0440226405600300303080010040c0b0750000701c01d4800c0c00306059400c0c3c00e403a50000495849140f14400c01a8048400700304210a11861508030b11400b504544141000381d0340d40341640c0041d4010766590040c002d08101e03800d103034000c150748004c0100d020724009424400140c0205608482 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 764404739 1250 764403489 764403503
    0x1050603070921061409061f0501110c030d08160c03080f06010507020904150b03060915090f060718090506010f110a051911011d01030c2715090303050304 68
    0x4421042d03225804854915030080c4090190440e843e8945000c13105c15290500035225420000e140b12114442140010800c601c01c407800518010045407040d5565103100301c00d00410350500400c0d50100110745149145444103501440d1001442e50703404040719040003803140401f03503400026441005240d220500e80c208203015104c4600484550042c5c3d10001d40002000ac20722041c050300a940c461054042030043c004040c2d220207142c0c40e942c041c0c403007a0715030744600d070454082c900c1489a9070388070b80e645c0100c82034035909000752450700e88e042d03850101007400040c4104495010808800251035041010301c80782c10308100003400c1001a50044d0108002001c003d00100810300525a00070341090131180318081a207021542c2c0f40c5607200494001000303213849005940100c4101c1c508800185892400030b400700c00560140c00ca4910107810408106004944414000c1d290000807801d42000803c4508124070080c2010f070300780c040310900161039000c01c0001c1d0301030100c030303407007648000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 764405989 1250 764404739 764404769
    0x30b0f0703180615050613090f0b06070c081009050d210905061503010501030b0109022503021608010b030c13140f09060f010b030f101707030b010506030709 69
    0x1000310300500049542c2d4100b918080c02c44001e005050300035401c001e00c21620715413200d036194101b02e01442008011540400c0f2248100000c88681d803006200052455000c034180014800280c010ba0082400b1204d07941c5490050003a0002000003440851052000f0440c2c25035a0b01c41681d41d003040d6520108001c10350f10804002070591516551910042105015640262500c1b9480d4030701190a0070074030b401c1061541d42440c050090701d041b01c4e00b001584055900b0921000c0203907100a4800280c00c240c00381c0c05030710841c91a8a1603850b03000e81c1c0500a0b00c012188a17950381c000c03982c00440b00381c1c186803940b040c503900400d582c0304065080b0741d5030484030040001716001d054030041c0d100301494000b040091842440c002c261180040c0d000703440c082d9580002c001000c171400c1c0103401604200380f000555100440039140c0d08499203080016212740d035100c0030407104500c40c00300403050b0411001002001a0900c110303014040896071281540780400c1d000300101c02c0e9200350a500c03401c0340c2e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 764407239 1250 764405989 764406001
    0x5150a110a0345090506030102040f031b1d0702010515030706270609081002030c040e06041b021c14071713090603020a05041a060322060c0e0a030b0f 66
    0x20400c081e031030034035490810302c43d9101070300e2443c030b100944070320300410b0b04120008215160600c22542610341c800d00c001c02243c1151580d500c8414000141c041d00b0450110105407a080080000b2000c080a4150000b9283c070050003402d640c0040c0800c00d0004110041080998002c00c4100581e40503140c02c8054490200e95049030102e10411440c41e00b143e140c000c2052030380190420190307541070f0304549400c03502d0521a0120b120848030071690031405d03c401d1091181c0e00c020300d0740007100100042071000040c1c2046030000c404044400241c0c3c41150740d0100c0c40c00303411003058219910304110300c042d0941c00c10074040d882506002885081100c00c1c29204140003015074803102440404100c54903182c14609004081c00d00041c0c3c0700f40380c4010005664a4140200b4040381512429420012094801e0028a800203010360141d00d9024005400502e00c0399000c02009004040c041080311034142c010b00400d002042c454040c003005141030000c10014120a40c10034906a131900072a82d0709 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 764408489 1250 764407239 764407307
    0x9110421170319020c010e060f090601060f170708010e090c031504050a050d020a030909020a021b13020d02040518061f0c0c030f14010b0d0b06060405150a110a03 71
    0x681100f050a101049503100a00154003640c0480c0040080380c01e1f41e00e95107269003a00c101103a8918595004200500405108007007010b400e010783d00741468032008003205035a240300100c48440010300604010071a11283d18411500600310174050400d040300c40c2c2c0820380300c82000005200c11240b450114040240030004125030039008030607640503102c240c200075224200c4540507030002d0380c0b00c01c02003030754070091007150440840c9400920391482c02c4040b03402c0509054200991016035409082c0118035580000c080d004462000103039038a05210030485562a083c400b610421045801c01c101602e860384a00100d807005440e4008162119008890880303002070000c080200500c1d001081103404100c03032a4a51255200c1020444801820f0b4221020b00308082d40c01056071840c1301c0820010f981141d00010043c0215280588600100d0304d01c15401900c140c12050004001030800d9100104150303000a0300c3c003070040d4a42c0d5441c000d0102d090340382c1c442070074618031055198803020 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 764409739 1250 764408489 764408521
    0x10509060d0e0703050105100f032307090903030608060408070206130f0902090108060301050906060613050306091c0c0b0606160611030106030e1c05090a091104211703 74
    0x800400340100d042c0c0c03224454460041e403204403210340c20800800c152851481c0582d080d90b1045155560051850b255404807031a00c00c025a81034001351440400b0400600a05001d010001d01c046400e1102e4600201104d039903501560803904110b080c072000940700421909102e80443d4016140c648a080241c800c0120740d011034050403542c0c00005000c1c00c9500a055004001d0700c40b08042c4c0e803110149401e03180119541c4c03000350003042c001003803072030707c04060b000c50121100b290b280c503616240032070718049c0107480600882c0d1001040c205191118410500e05036494503114031400f000d80d884c150700200140815108842c00704a004036802036480c42c000d1307160049010b20649620b0048505c40b94001e0064000003420302008448a00c4002901c5111068840c00184100c18603002241c103604448201c0e40d002080840c0054040740a010721170046c2402d20b0155a2145070080c42d00340403020160700614000d07914400c8020a02c8400203400344000100300545e01d0303071490003c1c44d910036 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 764410989 1250 764409739 764409757
    0x160e07080403180f0f050607020114130f0803070c0b0f030417090603070c06060603180204090f05100f0b0406051c0201180e0402040f05060a060f050702040609020a08150102070501050906 82
    0x1180f6040001c0c449034050f8100c080701c1d03408130003942c0f854460007801203034801c045010313011400000d402c130402c0f1052401440300c0c8000e40500c000f00c98540d00d11070b150900d00d62007184281e001281d11402d20000b0700915006014081c3c80038030f003203101012000d076070100801c041c04494244610381c84450a00d41103940d241070040840741c0c0c91a00c11400f5141d08000760050340c00c0b43c44d240000c80d000e40a882844c40c034102c00900407948030004e030f00304400f424074864200c0d00040a6081c80d00000c004220703404a803464400081541e500c0c0c112482c04980d00c00110720300c0b41d0b06100d420860f0380c99034429030320030a1070303010415541045400161070404800104001c801d661050000308040240c000e603000d10701c01c07181030101408104e4004140c5406403852940040411010071415020744484203040406003030413402e182c400d0b00000c045401a80c000a80300d5000502241d41551080507184e1000015002c2038032002000b0000351740306110700485060100c001194420340c2c0d526815580214 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 764412239 1250 764410989 764411027
    0x3061e0106050d0f0c020a1a1315020405060304080309211606060515091f052a01110a0e0a0b0d0c09080a06061e03050607142a160e07080403 62
    0x4100c517140299500c40c000c100303030b4240384c6c248100c07900d04110120440c01004140101d0030311400545031a02d00c1d0683c15020107c5c07035401c22001905480e404080d6210341e01401a090f264908028064107142400d052040341800d0740300c0c14182c080e20344003034805c01c603e24203181c0c440310040d10b400001421507800881d400741d00050030070060082c040042c03200d4241580c400720184486400c00700c0e02241d06803201c01180d021b022080341c01000b02c00c4030790360030800703248610608101d489242c21600c040c45550854074000454030040e5070048100c04030910282c0d950043c803440e00c4c0200c219405122000603000e40c4807035003001a03511401021002e0311503413042e034411445c0c40ca050001852584902210104090100070343c00c40a00003800440b50000054032950740c5441e400c45242105181a45080100b44501408400009100c0c84003048a250107020071210552261515844041e0006012040d0348244010500300c4821342e048100390409400c5c6803110b10b410f072443c07680080050008 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 764413489 1250 764412239 764412251
    0xd0506120604230106050f040903090b0a030501090e0f062205030c0a1a150105032205010b030f121204020a0509092d03090906041107060b03061e0106050d0f 69
    0x300060b03000d142110f801091800030b101545100031800c0e9915889030aa002c440688040036500f4103401104441e403091400b10f0403240c4640d01b00545400c01c24000000994560050140865a11440340c000c03006800800e090803000c454030790340b00001015020700344052803a8414408000d90801451130b408010b480e12148910750203661134040c6c00041d20320040134082c01d240801164512030080f483c4101c0358048007074000054815074809468440b101403a01c2c0b042682d40c441249800c0c29622501c00031414a0800c000c25103422929520715000f03070070510303c009a45402c2e03411038412602c1c904402c4226943c3e400018004100c5a01868100c0c4400b030801814160101b0412600c03400019940c8000d0614141356611034200002404594802c105100c003501e4081e00403948020700510104904080c8072420210381c2000c41300b164125114045107032146002d1241c82e50090800360850413100ea03240a0945001041c0310f05e60501030002150b610b40c01079504502c0d03155503094014024 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 764414739 1250 764413489 764413493
    0x11406030d1805030d0e100e01140a050f04090f0608070605040302040e2b0f09030206030a0b0a0302040e030c01140c0306150d0216050f070e150414090c120d050d0506120604 76
    0x1c0030a04500d414410000610050071f00d9000e01d980c202c11000680d90703c0071140c4011030b1100198090444102400424407000030050000350042002d0070b804003000c1100c000b245600d000b030f2004c3c0c0e00a45155013122406100c0c10f03a2000944045036011180401c0c0040120707409030074003a180040490000080b00324082811701c1010040428060742e0312070080c0c0c00004402c598591079800300135030006041007c40c0070140c0e25040040c485200914614116a40b580020101c50740807098101c1904007084804640c8402e00c1142a13040c0420f111044624280701c080225100c01130510b03108000b0b5003ea89e188003005000d40c7e540d0b24003040115500c4403a108005140d0540c0030080354580302d201c00605a00c4404164801292400e40c0d14031510380b40e10316500c2151200610154005603110860042d00300301d00c00147c050088540603058500c440000e01c8003081e80005105240d50240d00b24800ea01da0110441e5030800c00085c000503192503020000f00c541266940714840f40c0700304400c0c001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 764415989 1250 764414739 764414747
    0x8190f022104050603132310020c010e0a060515191a160c0f06050c1515060d240e24060d0c020c01030c02072d090509011406030d1805030d 61
    0x840c080c040c0c1013508007002c10300c0140c55031f02c507006a64465070f080200c0d18000d429942c1c001e090500041000814001a600140b030303e0801000001d13600d5a44034800d0069581e00d1100301d41a0703140980724040e88184024420b46e000040d840742c41c01000c810440340a89044540c01c4c0c54040c880480080d10100d4241490305d400c400501a098018200040014245004104582110070803001030110700e50300d45041c61081c0c00c000c0244814055510211425680300d400810700e0032040400010a0341c00005211484c0131020610300141d500d030101442280ca0505030b443d80f03c920165440c48a20407011450156954180069004500400e0b00212501c40740c104901c0c2015540c00c44450240b258011800d99184614410143e08490001e110807a100b1001c06226400101c4c90305c4503030000840071a400c0d42c00d50100616544e18000e1000c2001c0c01e016140021071915905101c40c00c082001075290741c6480a6003090162110510001000200e0550003e08005040d214600381303011002e0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 764417239 1250 764415989 764416021
    0x2010605040b01051c050406060914040b01080601060507120210020705010f050c160209040602130e0114191401090308040f1d0103081e070f08190f022104050603 71
    0x41c811810702420a0581d44101d041c0c0300c918501000200d00351185000000081801420654401e0b4a81344c020959070124081d5004216941040e4800b92425041c810359007501030300200c034075030408001000101e5202c810ba810007500483d802c404110310300809d910303103000148000c12803400828000d040c00030660200d40003050144090190380d130340c503c0c400c0c082d100d400305682c40304402000100c05400e000c0d140c107034862b10075007006241c50b20155003150389a01991044941e05409001480b01481100c8000b2a8241c141c81181c42c0000d02c0301444078101c8140900800340034441c4140443da07205400d00401150001d160595494541d24040031190160042c44c1c00c50600341c43c140905407100110b54100c0342c100400c581000410302e00e814520760340c081920520301040c0101d030041404000b1543d07406100d07000c00347c1d8640740b06058416040c40416400b050201c020141100c1c0b90b00850009507046094040074030341c40010035010058019a0049600f089011040240100442c0c0c1341c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 764418489 1250 764417239 764417249
    0xd060c020d08010b0d020c0705090c0a020706030e060a09020105120f060f0a0b03010b0a17090d1b0c0608060d05010513020a3017030702010f0609060b0304080721020106 74
    0x40d58540240c001c080d5100402032080c44060b00e4100208800e2001d00da020300b00e41d091300c1043d140c5480e500c000042d00800d06039094401c000002550314005901003140c5001007804d41000c0c4115401102003e8443c8002424a6034185d2507290b400304681c841e80454100d036410010454040c200354200c6421880106d0b85507000d06070007902103020746400e01a04080300c08200c3c040b4a10707820704100807a5900080c4012061003c54241c02c0f403109540011a8480c015900c02458030040c8680e00500710401c0400d080c0e244500d00d04040e01040c400300020b0280c0b560360078444a26100e0f2808541d80110801010f0300035440d04050042c0b4030007810303c140b20280201c6802c1030403a2101000c92000700940001800304078101108001104e0315101c0e18061401450303102003562400413072038076030f610448501006075503500080228507803034800c41001c1c05000c03204002c81810408420520b21014001510003040451408200100c484001004016a98000f084818540c802074041c0040d070040c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 764419739 1250 764418489 764418493
    0x1e200105011a040b030406022206050309103c0204090506030f010c270905010905100e0118110d061728080a02010f1a040b0d020d1509020d060c02 64
    0x42c8040c5024002c250390544000405607469520f5a0b610a8002d6003d00310041d40301243c0340c580a01c1141c03042010300200780b0354581503624941991840d0404d5941484010203c2c41c2010700e8190901810405681100c124a0120321a441c164000c00340c0d258881048407050000401003040131140d00154020718080e412126602d0005141a09807281c0705901c84c0041c00181080045c0e150300104001c4040d00c11502c04101da482c4e551032401e0700d4090700405a10742d1141c040c45461403815070460010040248210007075418000348100041720301e4641c07020f40e5202c0c0c5513031040d6401e510445619604102042003c41d0340c51540d5a4440d2041c15000310a01542d070007026401207a1502855860403004050300f844a00d07a652661134102046880c01c6668641014420783c11511030451400c2038919000d0b50046c1c0d800c00c00081d2501103101078012461102d604006841700c2110303501084e440303aa4032007100d02907280341e00140211a40a903000f080b0528510512005501c0310a000c071295003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 764420989 1250 764419739 764419769
    0x31a04050c0406110127030e0604030b191413110301020a090806070305060d02151c0b030d05091302030c070b0a0c0e1e040e010204170d0e09071e20010501 68
    0x48500d080300c80b6078189240e195003143d1110039100e61306200e41b140d2031003414654816440c036404100d40740c0280d0400c94403c60724100f030144119488401c8c90b44600e07482024008009035111130031015030090a020003142c40d104401d802c0100c0032141003600c0a02a0085444510150005007405418824014540900004120801d12074014503102c1c4601804800300740c40140d00340300100c282e1500622038034000f480b10158041403103080794410f251554000c50340100740c1040500740030003000c8080c00d1002c20008090f45840325003030071030342c01801400180c40e580d80f1700d4040c81a00c035001e002840031941e00200070942c0e00c42d5214501640140c2d55411000d20700b5403d01c1f120400d003d000f05013082c0780c149240110b29054000e801c0854400001609255807802c031000b001091443d500e00c2c5d80c210540030500140d02c098440310220040b50a10220300300148040c1410200351000c0b80005045400c0c8200b0b01d0188240c0180060800b40c42500c010440d10118001c04080c024501085c032003803 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 764422239 1250 764420989 764421017
    0x1d03070201081f051309060504050c01020c01021609020d0204080304080a0308061804020411041e051206010609090f0b06040b0d0e060601050d0f060e0709030b0603061006031a04050c0406 82
    0xd40d007881240d60040d96000d004d04020800c03100f450003240d864030443d100c04441c0001607c07406424010b0f44124010b00500303400c600064244070f035003000c407811503005580000402248811001c100c903d802401a03a4090b4208074001030321503500122490300c000640015800c00011f01c00030f94600036547c803004ca8581c141009007480c03000c60010449045400400e026250a0348100340d40b50a02c8086480c00d6030301c40b50408080e406e0290030300c0b0081b40c3c03d4108000c4c20107840d001e030020001c41c050000c03503041c410090b00302c101902500b64440d070342d00040010389003a503000d8218880e00811050310389a40e01a100c52507400003032946c3e5158140f00703410315a0100017400710b0041c0c005843c1e1a04001554041000604c4003540140140d52100c600049058110700e119024054680e0340d10040c500307504100d0b00e640405001c03d8000c0d03000000f004103042a0b225590150b40701303880d011807800300c0d0002ca03100700401c5039600c82d4014070704010701105c000320400500443e0202d072942c0071030654032 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 764423489 1250 764422239 764422261
    0x60305060a0c0306030f112101020405030c0a080604080319060e01140d021e1f020c01081b0706020a020f06180c0919230708070908060421031d0307020108 68
    0xe80f100401c0707206d0104143c00040c142d209180c0c01c281e8090b05440d03220312600e4140201110f140b50314442c50758005014000c0d400e05101b03207413a40c0e0781a6801c6d0100c902d040d1041d81d07248801800988810401b0000c00d5003176000080389002e44002000500c03900e522101c58901081003807090031910003080e0701002e101d003000701c0c9500b040c580040506d484103066111600307028104406050340040c171003030109190656900442504901d42e4010208042c449002400a900c0a4240103400702c02d41d00c500e40c1240220300312031101d40d00039000740c2c4035222244180c1c40c000c0c14142a08080c0a00400c000c001884243e070780744034201d90000c8421030f81c4010140440c8c1c00069034410100d016100d00580c441d04150005040d40c01c1200900c07801164440040f80300020a0303507404001001304090280ca0742d80034008201a09a4130040d150740e0406130382e1000c00380c2d080d44040001081240c0003490550203540120001e01400b800e4001c21118401d0454880d401034408030b022464070008030310701500d2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 764424739 1250 764423489 764423501
    0x126101d04230a14030d06050a23120604240c0203030a1802060409020d05010512030a0f020115030501020d060b031e090a061802042009011b06060305060a0c03 70
    0x101007408201005000d1040071002e280069941d2446196405000100d03820b14500c4690103500146449420040550040c0c44d016804203205182c092030a104080b09400c86013036807210220070703d00120354200454914030300320003002064003590003000140904c09082010001101044820818030b000c045402c0f5481c40e001a00140d006000051502c1150784c4414040c046406903100803080650003d4142d47c0143c001d201c0e0750f500460f2000f8000d0640c0580350242c4000ca5000e0b407903a60101d0025528060f0305071060411505106180c0e40074003c1d070040040c4104240c0d02c1020b2500c905016010b03502200300301c1c003a80d00c1c1c49000640d107283c403810b072030007445183e40c0600f184442c030700c51a501020241c40841d482c010795014000164003072240078182c02040c1442c5801c1d80313179401004100c0710013a4a16100d5607400c030605407000c1d00326003290310080090800091b007201c60074980f1011484500020309840ca4140c2c04000d0010004009104000910040c803041c000e281080302a070758 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 764425989 1250 764424739 764424743
    0x9030d0216050f0a09110c1603020609060d0e0d0f1b11150903010c0c02010e0103060501080a090606030f0804031e0203070303121b05030108150f04020126101d04 71
    0x34044401d02c0107140051021100810041c00c10500c1c6495600450443d0f581d001c80c18030010001030a0848040c0901003e030382104280e05400241d4516008280188620a04507100743e90004520700072007010b41c4016840c2941008580090912840c0607009498007450200459261044c481c401110101d88466680c0c2c01440c80040321071401c01e108205c0034900300803481030400c2c800280c04d0786092140c20280c40840d6910310703159900340009001b01c1d1142c030010341014103021040c00946d80002403e81c200550440019a8140c541040300003000f90b500020049035102c0017060500c440310001d401500c0c007446d805c81880c00c07802c6000800103d40d0b103000303405822600c81040424062084003040781d000390000718688011112018141d10030210110202d90048010700841904100c02c1d20b60700100c2c03003448910b04040c1c42c0e001c02c11200800003410840950f880307290945074980450440113400034101c0c1e00b414000178441d900e121501500f444403000200b40b00628002c0c90303810707000725 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 764427239 1250 764425989 764426023
    0x80102250c060e13090804030c06030e070614091503040611030114190e0403021e030a0507020f010c0b04060203160e010c0b1005030f0c100509132a0509030d02 70
    0xa8502201500c03003c100c045510f81c0010440400a00c0e802070f402090315a0748035054007a600d5043d4a1b11042d550480d03000070082600c0c00c4400251040001640f000755445824111500140d280704e1000c0352140340200c0f5089016641c4c600390189094021758000c1b441884e051100800404100900740001d00c14021702030128100c041d41070a185181e20714000c6a0a800303043d0a44441070313003807910b81c00e03103048006a00802c646880c0ca01ca444050805c5028540a0352038924003080041041c040c05801038440e1882c82020442c903800303400a825925801001d07001185003034204900203410843ea040d001c2d1801d21070444220703115499811200070141c5078004907110079190080d1f0303060014050b4417800c15035030001c03030107a03010815a40b401003964002c04880c2401828003000183d8041003005208040c82103004030303078403443c20b000c01c149001c1c0e0010794000702101c03400c0d8071100c2600c4014483e01000e0300405c815400001810350301d2040e03040b40c10409400a04a0740c99012030711841c405 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 764428489 1250 764427239 764427263
    0x91a03031c0e10090311101b080c0412050f010b03120706020a09170705010306050f0108040803090712080d0b0a03023007060e03190b010e0402061308010225 69
    0x100d001e0b4009055888088200d90003e203542c00c0c49811100f28442c15000b01d0003a0070500b01110040003510303031205c8220018040420101c07603401d103640c01c0c00348140510802c0c400140708039048500341c4004003032540704d00e0302c08105803d040d5250045142d0202c141d5003040d4040056040004141d0015861413840310300e00484c50315080000e4202c100c0740820400c0c0c01a0000e00c000b8000060184840341d80d000c0e0880c41d00d800009012500244c1c0524000d003941c0d0048060340c0c0e040044154002d23041283c607596590784000e007508268643d00810f103000c0000170268207008010b0042c0424140c282000c001220040d420000114003600c002540450051031100c828049280c00c0c02102d40c943c491041b00d69140c2007000c1c1441c08607004100010a04410120149030405c214500900030007421800b200ca15100c98000e10814080c4422102c80240414115241e88007141c01c2e05602c5024191415160600304e4041d41c40b490800100054001c0003c0e1440003072002095a690311484072815 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 764429739 1250 764428489 764428537
    0x613020c0d030b0f04091110020105091e1603050a0303050c0c0709200705030a021e0309150c250f051f03060b070c18050f070e0613091a0303 62
    0x241986460351030b080b030a680404d07501e58489000300d03800300b4442c03082501290125414844580c09011500c411a03041105020b0710a40204552040b41c4a24030003514262200b0013951400c0c06410300307000505030074803000051003004078404020910950f01032107143c41d0352054103924020040450055003110808102c03d00640d4888444209100c0c180f41031071410000c51516a04500010380d141e03080080c0241c201503040c042c03149200e051161102464001940c0c0030395a00650595a019240340102c0fa038008007104247c806030400c0070120380f20f09500041c05203184038900c080304502041d0800100d400d1118120700c4080d41c102415400000d108624144002c0c2001e032517840c24143e8441c2d000c540600098020000c00b0300521203020410b142103403c0840c0c10f078960020200070301c3c000134014003500d8408260b81050b028505a2119000d86000400d039209180301c180401c0e0341010001003406d81c0350494200110303589054444601584281500e9100c1c2e1913810340d000480f1182411 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 764430989 1250 764429739 764429741
    0xf010807120e280b01080114010b09040b041109100f020a03081f0b071e020a03020d1505090d02071d011e0f09021b010614010f02010905150613020c0d03 67
    0x40d441d010404550144500c109030141c640398145491116503d0a14a0414844410f00b13450050a42600030041c4855042d03555034041018003a02e20285c200040884c003d96898100009000d00200108003202c0c40292545d46d0f0b034884040d0310300454400749002110fa00a0b581d140221200350041c1c50400d00c40d0b5021111000020701d00300c22081480044943d100c00702c42c80b80c02401a05013110b65a55050900c0408001800388441000d00b12520300c0703006848108200086030380c140c54803a039003c0c5c02d117014a44400c01c044c0e2282e01c1407404d01002402000010030702040d244036008d541ca42ea1b214000ea802400000e83e4042e00d02188000401c00c544003204e02d802c00030b0340060b4800300c0303a0b115004800801815440010709075004619452900c84003032428415001540c000c2040d64903108050109410100c022418070181c00001e04400d4000e4200c4000150f010003a0345500301c1c3c8542c2e14403900425200d080c01540310300c11011510311140b08031003840020300001e1280980b4064201c1c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 764432239 1250 764430989 764431001
    0x10c02010c15051b0306010c03030e15040c05240403030c0201090b0304050d03050105190e100f0806040b0c0307091203092601152706050306040308060f01080712 71
    0x904000c951032060012507941903600e1200e020040d0040f03070741d090089840f28082050180c12083c01d2040042c032120382e803c0702c1000d10290b454100480d00d910f05036905030130030b92140c0d2240c0c08031401d9010001006514002d460075901e04440900c03802c041341520341690304454032115400d40c020001400800e000754004905c0034414508101080e868100310011900140c0d001c55481d80565911800c09401d40101400360009540308c40c0307602940b101e804c0e01c0c0e514500c0366011040c29140881c54100c17602d02c400000c1c000c01710070041c20310703552070301c40703554010480f0107580a40c3d40b1030115900d42986030449004030290303900c04644600b40729455000c0c0aa588084040c80010640007a941c0346100806904400a600c440040c0300030b22710850940c1c1c0040b0000b20360303224444c414020b10f030070a4880c8408003401d108040951180508810051220b5040580c1c0b500c90b1310304010401d40d01196851040005a43c051a4103140070015500a0015242e020100c1c01c00254114000c040703a00032 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 764433489 1250 764432239 764432243
    0x1e050d060221040b011703030a0f0e1b0907030b0a211a06090604050c18060409110706200a08100e01080c09010b0306010c080a09091a040506120606010c 67
    0x5142c841070324404a19091030355503195141c02c00100300014040000042030040c102c0c014812900b02c5e003003110a03140d1100500031030040341e0715114040100400d5100590001c80301d011101070440d8030161040600c05203444034880da42d0440051880761080c0502d010706c200103040311139400d05140c03117003000d04043e011300d02c1000340342e0a60b00003046014000461a0f08420241c5050f81001c005119240000400c0203020b24204800d200f500554442100d10a92081545840100703922001544078411903000c01c4a06d401d015400070020320140040060720320800d8104140b401c400c000300b181c82c0041c4005900075000344414030740c03076029401a40d8000613103900d0204498644031a0040d40341d0030307082035010fa4408000b114143c10b03e0b450f00c41c0540601c500030b80c02c5180a00c0000c15803201843c0c02800c0c2c0401207000c4070018010413880000d40765600381484071099055602c171442e000801c1440c0b0550a0002140e40b9080480d0810106403219010b0030080e03454500545411320800b0782 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 764434739 1250 764433489 764433491
    0x60303092315030a0c0c0c09091502030c03010618120f0201051c060915030c0605090a030c0801093005130f090c090807060203040501031e02221e050d06 67
    0xe140165070382d510000e0000b03915141a68072400c12000034800c0b40d1220705050207100a0100300404581c031000200105d0b074000700b01085006d05840c04000119401c3e500c0c041850001c010301416810507400f0714181c0c0c3c0b25540381c441241c03800b00e2199451407540301e01c0060a07251307540800843d40211500365103070f0045c1001b82c0b0300058203081405441c445010108100d640c3c581c107200c0b08040b4064820803502c40b00729000114199202c000f180347c09482010b083c001c0c00101c648990b22010001001943c00140c001e00090343e0388021f9001c0e12105808607041c400c410b51401c070940103841e074507942070340400100b491407400410548495100c4c410310042507265050000302d4019018045000e41076140c400708039050312500280c4488150340207200c00790098a414003540b6030000546003116005d203800f058806007507141400111017059190101d0b800000c1c031464400501e094202c4d104c03401e548403022640d461064050512501e4490b403400d541c00001000223281400c1040240307070003040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 764435989 1250 764434739 764434799
    0x1050703081501141215040204051c050f06090601060905100519090b070503070213050405120711040903050a090b030105010212070204020405030717010615050d360b060406030309 79
    0x1450041500074a002a012000000406c00300088010034081e0515095406505040c00c0800042144c2640d03007000c013003018050b0700341c000e1003400c10071441d0030311842d01518091700300124202c1e21054240601c90201c0d21000300010b01d030400c1b0103000e2009142e5510b035404c04035284809030324a4062034001e020040031b41d4010074000c038410011303d501c510903801596140f54078810303c01c882e0003000c1d0285080d841e040410003c02d0313000c142107040401c50b44142d992440d440c030b40713034003c002035040704d5801500c0d0002400070035811500501281c2407644030a14151b5642c050709010748003d00800340140c0051780c00c4080b20301500003400b25944014005070806484cc00802d06c5c00d2140d900c0b00c3c624085a100b420043c10080c070604c0064900e8030807480d404220707440050810f124060b140c0c0f01099880040c1058082148440446240503044040b1700104100d0b1444050102c0c8600baa00b20800402064103480c0c280300d064105d90b815119036007040d00d403e0b05804114903a0f400c00d54a00509a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 764437239 1250 764435989 764436017
    0x803010608130c080c09060a03050303071b06051503061501021b131505121203040b2203050306040c11070e190e071409061f0c08030c04090b01050703081501 69
    0x106000c0082e1413080000c0003040f18500800641c10009081c5c1c6000f61030034241030011a40110440380c0c0145203046c00703d04485018110b98040504170301c0501980d15181c144030001d040180744252200040b821583c0584130745c02a0700404124071031281c05070307000e00d20012889140036001108001e00030003c0324030248041d202d8084c0c42a6040c0d403008103050030b1003404280750120501f829040600020301c00301d1201d03541d41040b44001740c4041c02d224a01c3d0005105d034069034400107412200350406028110641c0f4010700039800941c2c0b031512460400045240b024420089030b90600c40c9100101002c82c0744c521004180303980035044140b803150210355403c04203514094411f1419845e40149100d510301990754200101944001c0e11078500c41c410b0020540d52600c2e0880124602c0780f81c046000012402034860f9030100100800b0884048100030030300c0d28034000b80045885010040c01004009001115244039261008020803c448040f0b2001d43d05a0313882e181c2400181008051000e0507 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 764438489 1250 764437239 764437253
    0x1206071b0c090b0a061d09062806110a0213050402040b0d110a0b0307050d240e090f030a1413181b09140111120301030b07080601020307080301060813 66
    0x42d410403074105071144403079949418405800c41c020811458984c3da8001c1449500b43c0c400e040c90034443c800d203000400b0030040e40d41d034541c50040c4a0116030320b600c2407003d02c450149100551150030040360191450303d0307003030102240385440c05030300a011802e0341680500d8070000f484094000d980107607440014800c0703522401c8070180b440b030051001801042030342003041072400c015006490914414818015481c0c3c0000580d000b0020103000419102e04546403902c0d6408140100ca80c8502c00b80c40c0007852341c149500c801d000c0c2d4005015039113192a801c01d0301c0e513644500207a8000161461010906840007900900b107000d0645414080a1307942d000003988013100040301e140610f5036400d80c04c2c04002500441c038982c8403e4105045160b02d00721a002a5002c0e008225041c0082d0a11603100901e09024100301141944001500c0e942c403818010007030711017110403a02062885002c201d40d0360000041e40c9003d54003510ba1855a07003880300403261f82c00040d01c1c2004034100401050001480 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 764439739 1250 764438489 764438513
    0x1a04090f0b042f04211a24060c03030402060d0e10020d0e06040b1605040503010c050a170124020c040c05131d0a020a1e0801141206071b 60
    0x80004000b403003d100003801c950a40700b15180c40c120740401c01040010013102812942c032140d080c12030754484460a01c56195202c14845203e02e04c0d19208015020711440303500c844400c1c0f5610340303074114500e60003440424442e44c040040320354410301c0050010710300900100000b2032401008100c105002d20200d280c5401c608846200ea03401140c0c00c024600c00384281c0a00e0461003004048170308003030303c80d0724480348068a2405001c20300081c4d440303503034000d0048030002d21003c1c00030000d4101c150001819a000151080002800c01904030803146034000101d041c2c40e4cd00c190280e10b01f050300c1500c014016054245015801042c2d21500141d4507841042c0521083d40c41e95503030b88859003501c0c101d20046400c80020a40d101c2030304103545101e0903200e607002d2001c20700145d951500c1003065a40100f003040c0d10110890300151210132550199049049139202e8840c0c0302072260f1b1504007d005001a440c24529510603000104a144900600d41624100d0b001c0c5403001c2400742c950341c0f06265 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 764440989 1250 764439739 764439761
    0xc070606091a040c0807080907120b09071509180e0604140705040614090601210c0201050703020307050919052806020a051b0a0e19061a04090f0b04 65
    0x40d84080440d045038003040440580320b82203600308600d0180b080094011400500030508101d54200042c0c01d1000030002c1c10081c1c00360711a0302e8030702a8985402c00c0c2d010002c0f039000c00b160042072000a480e0380558101d10481555440d200d20782402e01d6601151145030380140d0800945407440060f600d8000c0c0703c59070149008110030800285c2c07080c0c0c1a4a0081030b031b8401d0380617502e400802c02100c061090042c0c2e04a500b110704c1c03603680c0c03900b900489a040c40e80d0510354072210b00103c5405400e40795445109651480c0c2c000b400150f43d0340714181e0890000300c5003000400c80c02c01c2820214a8403242c52504200790540c003a40c03290b101d8012480d110b4914207034921161000f130b100c00e41084290740690040c20360b8401040345044513035410307845071844801c40154000040710510117a4841603608045d200b10403004c5102c2c43c04500104c5410314400710000b05524080300850750080300c8003c0c1d4400d0194154107440c0900c0e02034024000c0030b54031058028039a50b008032400e913580754010180005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 764442239 1250 764440989 764440991
    0x614012907080d0509010b063a0c270506090409061b0e090108030901230d020a200c060a0f030209120106062a02040203041b03210908150c07060609 65
    0x210340105002d08540b05074010603c40d010910a400d44000c8044200e18000f010340764551110301c81d01e00d201442611001400f94460030b0031034220f51a54000100607018040001c042a2380be0924402010442c450103000d802c904200701213440c90405402a42103a84550b20000b612000c1c10201190030391110f80c210006100c0d5000c08141d0f241c9115054003511182d00030358a8605118006001c1400b0042a5260511402e500107811820a000d58080c001344050070340d41d42c03c84020090144440402602a1492a05082c1c500b4100015101308684028042070b00d8901c0e5040c003501c611402580a03030400d5001c000403e43c039120301e1030700e900c00340045001251b46d40c245803000d41034849080d458801012000c0302d981c0300d114603a1800c00b200740c042d10016a01e07140ca0410005003400d600c00040300c0140208004100560b00900c00d01000151070701c540a070051843c21201205140b080079100c1d4800d1051070000ca843c01d0b4100e8102d0684850540380203001c0d9500c6081d00d0844d0b100d0400300b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 764443489 1250 764442239 764442241
    0xc03040e040f06241d13080c2401060c030c0308181507030b01050a02030f1e131a070b0402041a0d05070503100e060712020c030d090614012907080d05 66
    0x40043c80c0c0004001c3c1c5041401701440404d510b00c00d155a50f0010100c005180598418006000c00d00007210203140e0a0010355050260700c01a1030101414550f44c26200500840001942485003080d001125030503a19050540180d40301120000d0000d0003062440d48000064242407100304000341d440c0c0050b0580300e086150801000c0c0442d00c40c044101c0c18020100302d10f00449602000300c4014806482800e40c81c1c1540d42241d9042899030311103c081d01e803000402440f450b01c00021542281c805403460703100b00550289100540c050010020f000601c03600c0890b005183c140c002c000001c0c540c100c5499209000030008030020b0f24050b050b1690780024070180302505091101100120030a0024001780d0b0302340401030740e1024001c1100e8108050a03c400350b00d1041c81d011204004010421a41c989650495010040000c1c07803084a005150201c85801e00d2100024a030403602003844820000482000700020081c4450411380c1c0c0c2c0504000e80400074076020040c00195002000000340d07 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 764444739 1250 764443489 764443541
    0x1404020910050a08060906060d03020307031404090c0203070b09070f030b060319030c0b060a0f0b0c010905031b01180b0103080a030f1d0d090e070e03010912030b0a09020c03040e040f06 81
    0x40c07c1c0c0c040c183c180200440740d483c0e0007003600003081742c42403a03051604841440d1340c010003890078019034116052550405030603040086e40040a058907034042c564014080d207803082c00d1590b5240d5481030600c3e203021085d040000c1446480141d80c0800c001e021340f652846541c410751400c082070681200403d51064000003031118600d02a54031202c2664001e540506011205042c03a01622441480c1800020b03100240c00003904907400c0139a10200300c0c1d0301c3c0c4a2a411800b401400f14040301c0311586000c1007a440152116010b00c0e00320303004070a00c265a421901e440c07815503c0140c44005054883c4d01b9101005010f109003002140280da115407000080d013011428002441440020440c070031809008000d40300462a800000506040340220b0185011070b02514560344003030311182d51135440541e115019040440c091504690302c07000f45480f448034000324020100c612000391300a02040c000b2071101c040d0907070080e0041060142c41d030140ea89000540f21300480c600031129520200b801 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 764445989 1250 764444739 764444743
    0x3023f0309150714210c0c130c020f03030c04121a010906060305061905040b030c0301050c040915081c3b33040f0801090c05041404020910050a080609 66
    0x50f003540460041c000c000b2842a14045e01d0450401800038424005103503415201d0400c845c01583c4130140400040e02031503000c43c40105603000980c409806500038080c0b4041d0040100c0b0b109045540010381442e0420705402c0d01e0385001802103c2c401d0365480c4518040a4040e0401d00034a0440d00c0458070720706000700141503e90140035280503443c00120340c25142240c0c0100c1060b01d0007554002043d0328074074002032801c610300c291070ba01940780505002c151120704004000351008428140810f007036501403414030101e80d20403035000e1741140b08032036101040c0304a8400b00120501c0d080c0092034010946600748011940c3c103000042040c9100d141854200c0049502418221146651808002900c407076030b40e1800d140034103808039010031205c00006501914054074400c500c100a0316203e41d4150700074501d012064405080041d0005458a0140035400154a8844038000192626420b001d2454800381c0080b80001c0e880d003011413542c803100b50200c010500000100018140302020314 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 764447239 1250 764445989 764446013
    0xb03100e010b04020909190b190807080a08030c160611070c0e093c060106090e150607060b04111b030705030901121404080403023f03091507 62
    0x2d80680d005100c00f255990310f0002080d880702e44005103038440c510070040d0200800261984640c0000000440b04210030b00740b03200425960001c003128090740d250b05000703a0701d0054090040c0403003820400260200c4c21200504100300b4000d5101f01d0117403071540c03040d094981c6684888049030b80840e54406124040d04418018110070583c000c3d20300741000200d48407520120a242108132040009440e824418011941d070b090700310321040600c401c3e901181e258842807088600144e100a800710380861146a1140100e088890b800901c131800002e011064121803000c0d15210382d285503151041c1c03114041c1c940e907040024807040e510302418103e054412241c207000b2281da070003484080d00041c00001160441003007420020a070240d0702d0a031b1406800640b0b50801c426801106100c100502e6001910540380b0880c0c00102c800318600600c0000b0001d80208500040080c03814641500804c6070800048095400e0f245081c8651002c80c0c0c640501c0d43e00801c04200004cd10000c0c0000c5582d40 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 764448489 1250 764447239 764447261
    0x30a0c1e08041a040321230304031103160309091802060901050f0f07051b030f0703080a030603080f0c010b060705120313060509100e07030b040f060b03100e01 70
    0x1006840c250300c1d01c0640780500e0081e440c881c00011032240c2e070014000300340d8004581c054402d17250302500c000310314003c08640d032615003c68001701440d0f844411003030130f801c035401d00210028159500d40d2000c4034482d4070001d8984250004001040084000c0042c4205803402034403407422030341c54141300c0c2c4206d4040d08440300000303c4540c50180160799400c11941d50a0007460000d8442010b40c0c81d5240e40d1103040903c0541000000d05841004000b144401ca5489030a502c404100c995009042d140c22440101030401d400a2800b4000904504050207411415207000211240c80740d40b24141a80b001100c04290200400d400c0103200d03090040c0340d04120b007947d906081101c241e07106aa10000111407400307441000c00059680c01034000b00ca2100358010100f80254203250203204d40740c04010507003042c05400c00c905242452000140e000889901110508440d6940e4480213003680c0c4565003112a01e484249100c090340e4200b01091500301d1412000918a40c008201030844080f402d203 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 764449739 1250 764448489 764448533
    0xc0f020a02060d0e1f060806150d030305040819080f0a1407030c050f0a1809050603070302010c02060c1c0807020d0e040915061215050c030c0a0e03030a0c 68
    0x20100140c44001c180c402d6511201c50100301d54510008045c10a003101c00720b41d078074800704c03900e008400180e500080e084950309016140700b522100f02e10401c81c12041040760700880ba6914420009100c3d80c05150b11901640748a030400101901d14151190130042d01000036a41c04244089611003003a40d076001035020700100001c6441c1d50f900307150250014900b006140c5d465080c4801640100d00701e0f0700402801070b80c150b0740d0142e038001400050701510090095074002201203001c49543c882c8601500d0000c000700710542c5140d0044445811044081380c10444c140411040c540c8100b2800c050150400c1c54a07000c40c03418100200a000d00422a2085601c0711034100d440d650041c00400c10058241c50100d04100d050818900e41540031000050341c0b49401c2e0001001450420054402482038800103030410302c00c10f910068802c01c0d61120b0500310300300042003d6414680007400012414100703041d201c60180300080c110780000c10154041040503080c1c0080192101d071104509140b901 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 764450989 1250 764449739 764449753
    0xa1202030702150709090203160e0f030319031107030c03021002070c1520030a020f1f0209031006030803040c06110d110304082a1005030604050406090f03030c0f02 72
    0xc4001e542c3c0c3d10800c0f00e40c81e0008024049201580720340c0e101000380406400c15580d909010b83d05100a9141c08030050000c0c0c6503806464052034041602480c058009000f98180382e6002c6405484001d00c5251340e09150340c0d410126500c1c2c01361400f505000307009460f038050224035410040e0400040c0142e086009204008402c0062142c01040003618000170520044003101c10040d0340c1d040c07003001da4500c1d55101e006400c41c0840004000c0030480300f594240da681c0a52008901c4d540c03d42144210400ba40e0740c0c8880108a40d6a400340c021400000d007181c05000d880c180711007c84000e5001607403900c1e0000708101c148107024980343c0050000345000c40c0c0b480d070001d0300d00b034856030715081c0c0808120803100c845411980800940e0043c1102c8025110304005102c03c1000b807800c0c6903801e400d4030f80400c030b000c246441c1c04d00e020407a03041c0f261905495070f074541d0108001460010300032941207a443c211100807440d01c054461a00d03100340c400189000c0c0506018082100810a050466000c10 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 764452239 1250 764450989 764451001
    0x151409010f060c020103020702130912020d05030609090c0d0605071e02100504060615021006090b0d1209230f03070503100203040f02121006090b0109060c020312040b0a120203 77
    0x2001c0a0111400c0e0710380100c1c0301c006880101c000c0e1003400806980300c48a900c000b02039090a07802841c0180c1700d006c944c0c0d03298501070002e1b0f031103a14903864800414010300000301c3c0ca04054208070390040080081e6007098417044009410380088181c00e54085984100f0040250742108800c3c40c01115004850880c0c810100e0007907860240602c2c0070862503c0342d02160801c10b0a1b0007450107041000303000000c1c0b513595880207581d40a08001105090305160740022440c41e58450124400009401c215100d00c0c903446240c6840006042401003206030a40018901306240700c007801081c00e68080316034901c1c0d803020080365201ca501c9151081c0c001400800c07141d40d00045800007100b0503200580c69649500707241420380c0c1051000383d004a443c1d4940204d0810104500d000990005c1041040d540c0711000e2408440200d161140410020300d006d11016008925400ca900c1c4010210f5007820400002c441d19500b00b036002d94514440410100300107604140000034409003e1000c5045182c50 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 764453489 1250 764452239 764452259
    0x60105040b0f100e031f0b0a0317130305030307120c0201050f01061b021c031704030c0602070503130303120605191203090b0a170f06030a11120115140901 68
    0x220254854840250f00c0c101040c001d11300690310000050039202007a00d185050b0f200801001c503140b814500d0700c403403644035103060038902e001d403a085400c6120b0592458900c080c103a000b91581b000a40c0d182d080000060800c20003148180010b0b55191a11204445008103545072500c0c083c0969040c00108070000b40703000b11302c43c11166645400306e40001c0c2a10a003043c50174401019412031500700d4140d4642006c546041d240034425900c1c1104010200b01c0d41e04032400584008000450204880700403c244d078002c1d03d88280214196403802c0d04503030041c660260a90b00c05c8001c02d004070302c0340000c00ca1520035000180015070704c14040c90a811000a4104103034000d140c0501054000801418811202c107809009100761056030341e048440064072580c1408500c2c0014000b407000122003850108816006007400380040055140e40d540d8100c00d1400744003000d401c02d0070410391440402c400d000b082c902815203550500050b0810200200e40c4421112040c051551403004220141070 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 764454739 1250 764453489 764453509
    0x6050a24050906040503060109060611150c03041110020607080703020a1209061e050603010f020c1e010b180a050f010b180607080d0506090106032c0c040e0708060105040b 75
    0x205241c01e41e5140203490016102e4011500203581500c07a000021814600c17a51040d0160749070383d01c038048501825220b184d0741e03004041c1076031742c1048200d0224040c0a42d0502031034015200c0c07040000c481d410b0170086503400d0386003010f403401a0f10240500898580014409403c4802441d041d85480e82034080540143e552980407010301d03558890b4002403080c9603008800d2a042e110064800032103811100010708002d0364614400c0d46800980402000b1901c01c03184c0241900024002e0300e00d580c2c030000661707440e003a101c00c11552940020200344c4c3d2840036041c00d0018040c880100c0c7d080c01c0c01c6041c100c8600501c21a624005c6100501c4100b0342d031815154070100e04020359038402c4d18230f0041403140c00340a00080110b50f0108010340520b003030341c01c0326201316402d0701c07010030580e40d56030f0841c2030310000001400e10b920307000075074041104000030341001203445004803800c4031040808203080f19000721a180e0680c110500c14881e822082c8880760040c00115028410032502a00180c62285 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 764455989 1250 764454739 764454809
    0xc06040b070912110d0c06050408070905070e01050904111b0c0d030c0b04050f0105070c0506070309031d040b2e020c151c0c03060810200702030f070906050a 69
    0x2111310f60044840d665650035460181e4013103010f0400d1680c0f050064181d4100d0300401407103000d640004640d9690300d20903503204003c50703902c80401660341070043d20594031240c20581c1054135240380d051004200c5005105650001d2410703414040c0e048086403c0981c0150464031960304110f075400800d40c84484d990712280c1042c44c0080301d48492820604e8140c00400c0e182865082008200d05641c00001c41302c18175010b002030302c40303a568502044046980c5045c004020a4180c203440b189c1001892405602c074101610000340d02c440760b00020509103510380c0103101e003469024004041c850040b400c1c120004c00f40000d000081e90031002a41c48440400c950b51507220220b081e11000001d9594a4201d0b85003030420054644c48010080291003203014800d03480c4aa00f000d050108460b119124850840e103030000320008011003030340425807041c0c43c03d99252003010188107800c80c048c40304000811580c0c7d00000c1540c80c000038000308141c950303c42d030122808490380c0340d9032612411189840c04 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 764457239 1250 764455989 764456003
    0x601180302030a03032c0703150b100e150d0207060c090311010305041a040f0318120b0718090b0f060f07030806010207081e0616050a05030402010909020c06040b070912 74
    0x10a40040048045a2501c644140441c406c05552090700340030a0510560b409400605d42c80404c10340207400352042e0402c42c40d004400c3c0300100040720310880a140328000001c201308500d00c00000194016040907210601e42540000d089040007414429214511030341c1c01c00a40c0700b4910380340c0d50708a08440b0001030625842e01c0029040040444884a58a04500c440c6ca1039042a041001d403244501404901281035460103c0c0c480d400307002030104071046503800942c000e10710390301e0114103000603007460b0074441c0da10800b09044100c02c0c40e07400544244800013a810741201c042000840038070000070f0082a04014a00030102202c0c03c9840d10b03601410000d4031511030400403868241c1c16405806140254120000030405d1110f8800c80711200c42c085130f0a0ba10365200840c40c443d00d040c1d04102042080240100c454001d07005140e100f40141484101c00e0307501d2110038140e07440010f40758440e07002602000108101110010b81000040c9800c50000e820840c94603988800d40c4009480c41e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 764458489 1250 764457239 764457251
    0x3091c05120c070b090102030402130509030702150405060325030b01080f130519030e0306010b1207050c01060902370c050a0c1202030f0a11040c020a050a0b0601180302030a0303 78
    0x1209002c08942e803c55000392070700e155240007007031a8000d4009642c1240300f00c1c45881c070108080703003502807107000b05158005146003203490340c2040201d075a5081c0e500c1d00303a002484001010303a02c13400a18824010386031800304a240d803901c191800306424a144040c50301d410018002a64001c40255120710301d01d85840171030715071904101424202043c010481c0c410342c3c420f8030501140c0385038817032051721948a80361540f032020101512902c2c240904441500d040c0801e80141000ba412690031045030300b0007030718003050094020700790781480d04a800e00d03d4001842489040c00e10312500d100d402c0b11040402014410124a201420035521010821210a1014080c850180a800d1081da401542850704686d90b2810030302c0040040c20580c400d004005444106010110701e914886074400340c4c0c8a400384d810000c0100600a601c3c88508510590a2071400580b0400882481d680240070310f002c9480c0c0f40f0001481b031403114194924444100340c1c100016200001c000f20f6056042c00e02040c8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 764459739 1250 764458489 764458501
    0x30712021306030f0e010c0525050a020105070f0b0103120e0607020a031103010213090c020c060a020703170c0d03140604021c051308030f01030215090108071809020d0203091c0512 79
    0x90030705c10598000e254078050701c1820003078020004003680c09015100c190504219400391440b00c407003110241481d088101300500640c81003000304012440b9030b008000d030791040d490380203601009800860320310710140450481160410006051070904030b41e01450142e2617804182104280c1c0b0006040e60540310741c4c451141e13429016541a8030401c0000c1d0801652240a04050700d02d244d160800340c09040c12003140ca051100440714403901540080c003103e0301c2c56885038a00c07040708450006006003440507440c480020300000901c241c2d59907000c6244802c0d44082402c03107901404680c400d91040104103a0446071070000f1641c81210180011a03a8130040c8881c502c3c5056039005001e054000100403030320415440c02816a4000d0b034001600b2840500200050f1003074981d80c5000c078a1140000d21418410420006151080300b0000740c01c6560308001030a030b811004048400503008000c200c1000300410450904840b44804a9002000e010740a4120700c104030100c0e114007488400110 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 764460989 1250 764459739 764459741
    0x506070f140f03041e0b180103110d0f0b09070c140709020c1c1b060513020316051203041a0c0c1309140c03060601120f060b030712021306030f 63
    0x70801e5000c00d07034024206020005480780d0050040c28240340f5105064a14031940c5404c000980b190745807001d1504216000480628061640950401da21016001c2d0300e640304101030309541c80d101c1004200b02c5100f0141c6e1341a568521100f5000e202d6100c01c02c881258404d00019410344c00484003480035501001c0142810110b800020100e4000607044845c0ba2001600400c00044440185004000701100302c8180520444050b0342c2031005c40c1c130001041040c1c0c0115045040c940c103141c0c0d681c0030b55001c04c2c145039980c400813403402410f60b0101b20138202203501d000c2061850000d10700e080c2c10603808803214072414152000d0b0f007001003107146400c4000c0080140c0c10740c00030318440324400800101800340203e08421110b201107001c98854900740092141c0103080700402030f0406950301c0d001101c2c0c06d00302c180410151a01c03100d4400c1e59514a1203080050b20301c2522042d520b18040001a040c83e0b01d01304c10b05941e42c81040013000b0740303a00e40e410100b1340d2050314020038500500d900d420 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 764462239 1250 764460989 764461013
    0x70c05030a0f17180d0e1003050a0207060e01020306040605010302211b03041b0611060606090a050a0b090306070c0b010537140102010b0306060603090a0818040f060506070f 76
    0x3e4050070300e84180940400c00000d00b585600c88242120030700d00c0603501c2154800e40382480b641d00403000e0051800c44900a80000754040f042040c0142002440d0702c070441544c82c00585035440707035030010070b021407420035003d908050303c0207080c103500c0c00000d0b418000d400e104000e0500c03511251030b00072501201c01c0801c3d2504011000315550386038146400d1544031001c66a4480b07003001008100007603058001c215042a00c1843d00241086556140510080c2c2e8000200e1561101d03504030701203446d41d1482c0c0740202030075022030070b1a120328014041c5403070280003902020501120414141c0001c6c2080042c5043d20301c00e990360502c60304208114150308507a842c09155544c0e10f11120900d0940000c10401110029402c642800080034010782c00c0320342c0c0e64041605508140001609824540e00071138210012500b215035046440d01c0f15101074001840020006d080c8075200c0b8021711b01400b8080c00304d41c0368801003010a01d0000040e0541c800e02000901900d0414042c200303006900d2140 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 764463489 1250 764462239 764462267
    0x1c0210050c0616021501030320030915040801060501050304022d040203040317060a0b0a0c020a03021002071a2701090504110a02060a050745030b070c05030a0f 70
    0x1c0c0c2c050f00f400030540103085550b410000051155042c0141711410b00301003681240d41648460703922020304200d1041d19040800c5251403440100609200c1d52a0041040c00001c159141d80d92142d003002411307825111907a02c8141006003d2042c000966980f800b4400c0c0a06800c05c03584055501465a1030400460b90340c00e54481e02c084100401d2540144011080304062400d0449030740e40c071420048441c2c064003c0085c049028824818098010314600d283c0b0390004002d4950b290313990380003031f00749c7c1181c054140041e082004200301c040c060024140780f00c0040310b40d00d41804211801880090707680300c041003204111014004a50740510b081d00042c00b8090801d002d4400c0c221070042c4103030b2212100500511441c4005201c00b80c0300c1c0b24103402021541d0300c04600d4410302c4451100d0054282c000c400071101c0200480e011207000000030003040d500c4c071000840f02e2440c20b21000c01e40d0000c06410610004048241c000b410101c11100d51040d181004a00e5807507110044400c6001d0100d9 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 764464739 1250 764463489 764463493
    0x80a030c03062c0901061a0a021504030e190b0c1c020d02030906282105060901120218090a0c050303132d120204060501020d02191e061a1c0210050c 65
    0x41419a00007d01c02404800c80c1d40e002c0300c20420950b00313480c0301030500f02c5016001a481c20418503131450031490030904982d000391111030f215200d24104010b54010362039031100340e11000d42400781001d5110000c1c43e0003035a0000d40030299590102940300d1098901092244100050091002c1107184c4404102c0100303994001c90511844000f0340301c142da07400c241920b200202040500890680a154441c000141112456910b0246075a191070540807040340d01000404000305241007048a092103000d94038024a0020401d017403085491041c0d070801c90180d00200a840c0c80071500084080403038010043d104a80c14154500c82d040d110000341400c20403d0b10ba1000070b0200e07424880c83e442c070307008580030072442e507840300107907503501c02644154003581001c00c0800b00d2050788000e00410b01e0045404000500c02d90006560061202c00101c55843d6603082080307080200131481d000029080c3d4046002a501c0c828200e401400d040009120b0700c80036801055135031003041038030151006074007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 764465989 1250 764464739 764464769
    0x51308120a0207150c020c0a03020d0b07020114040b010302010806040c020309010818100902041104060f0c0503070b010b030703201b07050303070f11030604020d060216080a030c03062c090106 84
    0x9100043e121710f0000000621650025a506140815480c000c4980c001c10041c2c048110b541c8181c030203400102080c047d956103404080701c039030000100c640315034402c2000102d550b0561001501d502c034050301040c000d9141411130321607150008116518074001342040f110a9842040342c1c104945915080c81807800350740001210309000341c1060007124802c440601c1250131000040e00030780a240b1034080007456513000860340a00803101e181819000c0c2c0b06491070a031103612001840c1c071080e4003441e9049000004c00200130307403503c40c2e040d40004003140300310396000c042104042c9024268003030010448070080382d01b0a203410403000b002480c02406480e1038401d182409500300349260003d95030b43c0340e1400360000314940400c3c01c0344540d500514a901d00441501c03094025000145116080749241c807020b00440c209001034456441c49541c045900c0d80030b0240102660701561143c0c9040407080e506500f040045403100391038001c40c0b100484e8966500c0c400a02428483d4032046002e50041 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 764467239 1250 764465989 764466023
    0x50d0e1608010e1c080c0f0c15060415050a060528030b1206070207120501020d06090507030f1103060409150c05040314030703120e030d0509070603051308120a0207 72
    0x3400200390949042e064a00303c48010707282d0b04851351441c0c001000141c003400040c41021114007d0950805800e00c1e031401c2c21451030305c052600c42c12135402031068510104008541c40c1c107019218841d420141310369486450301000c120081001c1c09420140f281c00b0030740c0740d00c1001c2d81040c0340360002c000b40c1d840b210720b50440d40500184610250140900c401c018080201c01000410501914095008114440c5084030f10780d83ca1180e10011200c95400300f000c142840e15a029500152110300e90000f05030420f04400b600300c071040302c4c071401d025041401164a15001c6000d42e03034000740558002c2012842440d003100240401c40360140b990380b0703003080c0b503020070750150140080c0c030311480c034a07454401c507490400c0c1c0c1d9005501001300091601d00c0d000170321304500d0700032081c9002480308032410001d03c154000155201180d00b1001940702400800071247d040c084c01d500400d0590141881d14815210440d03144559095461952400801701d06040010b0b4121540d00c0e41000d0a40208600f01c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 764468489 1250 764467239 764467241
    0x61e100e0915030f0d05090402030c0c0102030f0105010e0f0303091c020d0803100b09030c0d0312290603310209071710121103010207080c03040e0a0507050d0e160801 73
    0x300a03d0207881444051130210100155485110081d41c8600f82048890710800000e03520040040b0f44e0080240b00c0c120200509001440c0201a82c503c07812841d8103043c001402042076000803482203041d02d00d0080b541c1c030301108851155005a409442581401c15014540f00d02c8030341c000e4100092104d00c0041c800528065401a00b03c0740c009010103030b6402043c041405aa01039550580014640801a01d891580040701d94803038144003080016040a880884c0c009101c0300c5190b89640c07a5901c2d1002120039003486081303003110910304508011417203051050300b20368111218140850320103140340e075004410490740c0d4020240c841511304150020450b54419400c4072604070400042070b40e4255400c441d1b401d076000040c4d990b081c1c0000c0e840300003080b0b20403894070760155030801c1640003060020b00201000a55100210340d101e241000300c0c502c012000b0414041c0610703000510491030b83c05811101d562a03401c00c003103488180c0f0030301c560800d0020540120000701e459000a044401 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 764469739 1250 764468489 764468521
    0x60207030312020901091e0b040b1e0406050702090a0f020f07030e1e100509030d0207050306012c09012d0c090510210c0e09061e100e09 60
    0x120395225504102ea0302d4010083c0d00034600c040d4081003c4401c180312449005581c64900522480040c041940d1803000c100690b100340c119206508000403405052180803641301144403d050031a07191620748440204607016082009100d03400c0140072420710030b516040340b10f8411070954119543c04e440c1c00780150a50010b003040f4040348330469000307014984001da03001d00740d149403081400000007104014070ba1102902140502c00107000403c026101005045560170703040c4c000f410130301d0900040514194059125020b910240040c090400895800c2c0309001070407120b000b00380e0303181c0300c1c1e0781c90140c0700c24403030050300c0d20a03a2403000c0c81c0d00c6007041200601011110401440d2a4035100300da4190f0180509500310901c0610303000d15605c541c411a0070712100324480459425035a074440c0a03192489200e400184e001d2160015510f401040c2580180c0107d51203042c02030303180c150b1110014044002071141c1c9450302590b03191401080032218820000b844010f0300d1404844248810311 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 764470989 1250 764469739 764469743
    0x201030608010c0f03050606041e030302121801031112040303090c06031118041503060c0801060824150f03010801050a0b0901121e0b0f06190b0702060403050706020703 74
    0xc00d140c000100800c061044020001c410ba41d5a084516080720680180c44081d05984e0000c604100005101100045d0030884024600c4184613441c81c50400034985652904052080007081022441c1181030038102e0243c42c81c20708000c160011030040b038210754010340605a0031514128200420103034158044100340f84105840d40310561154400c4044a00c40034203c01007000800200d03202189070f08588048107401040840d80e160030f4000c0c2c07504124a980700310380c1540c84034a1080c5290f00100f9840c054000c41c90844810f10744401c1c081000d201c00e05401e8000c07501d900421143e81c03110000422100002c51042c0e070f40b0071080a1076180c0760700900c520613103540303406c1c00b103080b41e144c40c017404160b16002816000301e6428454401d0400001110448100d040c401990041c04e2140240105182c001e0081c04014a031995110060181c0280030a100c1c00c0301c1c0c05080c04490020701c216040c0c0d07651301012901c80b107051000c1495442550406031240c8a0b101002030403503030000d40041907078 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 764472239 1250 764470989 764470991
    0xc060e01030c0201020906071e020a03080a09080606060301090f0e01020f040317161401090f0f0308060114030a0b01200604150e19111e030c060403050c0906060706050c0403020103 79
    0x5114100403405c0703004128003540d010404009810200c2e000680780f44489510b441c0034280044640d0000e900c45c1100d5200b180d10003400303d040a50550009050802846c01c440a01228038040000680500c014091403401c40d41e1030481c54111600e5a0051038140089002150b8551005101d0405a0020b10013190b8404504a0700c004084d40b54041c1c5096040401c00c104414840741d40355511003021783c0703050305950740e0b4002e075001286507802e00b6082c46004100c1020440002c1c14000c200240041081741844034620344a0310040b600d03001c590f484507043c500041c2c1c03029030900407202d540c02014005220070046085844a1a0205080b401240b00300d600f100648a038802c07020648050244104050f041741d20519104c1041007108843c00380b2134100000e80701d01c407800080c10001c4150743c022008142400d000d5075030504000342c10812208440c0a1305140c555500d581e0380c4c000082845000300e5890b4045a40c940b940170236603003540e034401c409100b14600008110720325089803000ba8000303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 764473489 1250 764472239 764472251
    0xc0c1608070801150302010e180c09120a03080420190806060d05070308161b030b0a0b1e030703020d030210060506180114040503032a030c0703110a030c060e0103 71
    0x140c014440c4c081c1d07101c018203d00c050b00349950010740b0f0310b0000748002a000241c1c411240659980c1070b81070703031050749091180b6480303e00140074007500f001554081000c0b5400804031a010a070081e1045500c160f00808000341c00203011f101c1e007010f80759155179980100105802c8912141e000300400c060340c02c29400c82d80c07140c2c0c59204200240c410881d001c0c040307410045041c00400e504030000c01c400c0e0fa000d4000c01c095601c40e512846800861035404040a64a6106200b00603030203900340d4001e03a1701502408503d14440000310910721420400000a50440035011030341c80c180070380801150000d00e02d4039030500c14100a500c400405811a088a1903c14040381c03d1400c1020b40d01d04100c99030a00c0076450080e0015503003244189140e101c000e105100000300c5544c100b004002c001c3d04004000c8014020032248400c40f01100707034146007a0818000f00c2103c03000003490030b0031130b40c1040340180817040c1c40010801074a099000070702103800d80302003c079541d900104c002c203001c6400c0e80c00300b041e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 764474739 1250 764473489 764473499
    0x21080f120402190b03180304050d06090201140a050d0f1113210b0c03070903020402040f03110d320a030822031e020f0a1b08120406080c0c160807 64
    0x10090f2600400e031844200780003151036081190b00e00c188448040040301e25007520340d000600d007039034001c1c000c40d040380c3c0360b1002008650b40100074a00c0304408540300d90501000301c80c0607155014200f000d0750059035a411241080c10305810000b0800c81e055030161b520040c0940d5054650410300138119406071202600341c1c0941022a41034002e90090700741d41441d2288510404694805043c81c010000b107102c001c400b5984600c02040280008080c25606070702e94509103a54030b900024151055103100700c114086aa0500c00c845400d44002d000c1000c20540c611390100000c0b10700400e5480d1144001d5802050f421020780750187c2030b10441e10384c003040002c4d94107003d0f01000c14001c0c001003006041c40e40424003815125004021070055902c00d032030790402285040d614410549001c803030000c14544003c4488210400340c65400042e00c603c9100704518401480307588100c1003005522170004100701a450199a01418950287c511654280780b1350041d070b041e603010340040c50280e4880051 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 764475989 1250 764474739 764474779
    0xf0708040e150108070c0204090b090d020c06310b030916140f0907090e101e1d0a230a050c040819020307080303100807060921080f120402 61
    0x8007400142c2d581d103c117a403800402c491012030700e1022600706403a4902c540005608040c81403281c01d400c00101030800760884020302c0c25500003a00e80c0a00000c01400310300070701e40040450464002c1d81c0514445141c050405950800c60380310541100010050008007440450200521408084074800f6a900da5103015442c80c02d41d04115880782109142c01c41600340160350b01d0348840513040155809588820284240f80c0c2140c494030648104201800300002c0c071144500b4000c02c0c100c9480c84207061440c0c1101c603180e8200d00d181440000400940e114480fa001003121400480c28821403510420a4140c202001c0d102d2400003418400042ca240d00180e00395021100224010624242c0c8480301d4601c0070000c4034180e03014001d0b0400441c08003c01c00c01140500f60841210f10f500386000794403410319146070026820010824420403580d005140d040403c02e55854880c5e541034482d207096000d9225100780c41c86103030008074500c4560000744a20318852402038499004c07074941d5400d401 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 764477239 1250 764475989 764476021
    0x60b04050a02030114122a15031303031e0c080a361e031106100b0f030603150c04030b09070b041703071b1e050303041a0f0708040e 58
    0x4205c2c1600403440707914211002c801070342402d2042c0c0e030414800314a0180d4601078000e0f8450301e04040002d58061b0300380001071000c0c40c1d84100b81d250440c101116007840b0181942409410540c1315108400092154120130f100700655907410060741c040c1c0400070305a00c030f0858030341c1c0c2c0395860143d01c042d1014401d1415814240c0510103003c4c1c210300092211420307501c2800990b03605020508003801c4841018000198030f0180c2c44007031448802c3c10711145000030003015000a1480e80404000150455003500d005000e890941d0392240e4030750001c130303150001300e62900141c24254014000822494030050043e280076002145141d0f442d0f1100d44d5a54031a1f100d181c14410b820001000703949414000d6105040b6080c00b07403494003203261668404c4140800004100800e030010821182a800c4203982c159103c095840131101d10304400241c481c003551055940c1c80340010500f011040794102180c1140700c42c19080354a0300042d040030108c54000b40581103c0c1c8800314041040035085003001 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 764478489 1250 764477239 764477249
    0x9080d0c1203050c09040f0230070c080313240b040e0c18130c030308220c06080a021215190b1606060b030403020c014a0607060b04050a020301 63
    0x682c501815602071000a00210300d100740c847e0713401e0107400d40304001c1d0862103102440c103242c00e022070801001c860b05805c10160006041c4116000d9040c0022180c0080c0d960161984c0e03107404c9451307d98102840c8445620900000c801011403903001d4040a42c0c0c0101b040c40810368080041c0621000340da6a0791540070303000365003c0b5520038905100e52414441d268021801140c05088a21a035038201000303009410440205102404200c0080c60380c1d065900c1c3c01600c0c2410450103179060326000c2510000340288402c101080d07000989101f401d80441d121050002201c02e80381c41c0403611076007240402d202036441101881900b0000c55060119002554408400300f1320300904003401d5018a6800d607001c4881d0341d121600040e100c243c0c500954880ea0194014241519109000401000720f40400c0145600f03244082044000311003942020300380c0c6024100f1800000b28882882c00c003442014650000b40005c04104000d101c1e004201c1080307044d24140865254100c1e0031090340003d000e0307 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 764479739 1250 764478489 764478511
    0x4060f0b01110a0b090a020303130513060302060315030f0f1609020309070b09040b13020a121a01050d1b0f02062a0901090306063206030c0a09080d0c120305 69
    0x800041084da98120790401140c0c030443c4c08002c3d49501090964003e00c00d089484550f0010410503410b00d0305201c1e84002c841002000400e04503400036885000140100040c9140c036003045225440812100b82103441f0801118a403907140c41d0044c7e40c03030205102405141014100c00184c841083c001d40340149000f101500f103450070a01690860740004811550094468810708800d07125440140c0e10001c2a25000da135441d4504405800b0755281a164040c09140810702d5101c002c101c50303c801001c0091a00d296aa04d90340011006001c0601114020196903034001190942100304813207101125004d03900c0f00d503540105000001030704104c10008000a20f009440401750400600c1d1003041418040c01d00c80d05c81d00d074003080b56480c0e0010f004900b41c42c205280f0300b40300710070080d40c0031300c04041103941c1d03080450200d0120b001c050300050501001098140035240202d031480094071142c8102ea56443e00100c000704509401c140c103503540c00c201e1552004c000c0c4a0701441d132060b259694 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 764480989 1250 764479739 764479753
    0xf0801060b13030209090a0803010b0306120705060d09060207140616020607020d050703110d0306090b040219110a141b03010b010206040201080910090819021b0607060b060304060f0b0111 82
    0x280510032170300a081c500d25014426186000800b0040a940600701a00c3d0b07a60b2246084024082c0090a440100c01242e020007001c12a5035691001c468020401201c0032800e03070b081740b5090000e4028043c0040c841c11110400000351140054010f01c104036103038000000448103d801d98445006560010051300032101d0f01e0b0341f0038042d0006001e020310924000d140034203110303000e0b0700b0000c02c42c19500029849020400c4003000c140070b40804084100c6003180350401c070228030184003035280044028050001d5050740440c209102d034154940d0010f12640b070005020b1561919511888918411301ca103109001d1014181407092010152040c2c00404050b05d0703036001560501e42c0240711f000e96100d0700902080c013900070301482c04501c1c0703d00242612040c40c1411203414045401d40c0e10110f41c01090000c0c1f8168100c100a46100c00555082d9601c2c5140e00b8900060a03030f8507892034024000109010070042245d001e11241110010704000c4a414900111509120368002c440240d00c200c03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 764482239 1250 764480989 764480993
    0x9020a1703040b09280e0108010c120b010203042117030136060b19030c120b040209100c0b0105090601022d070b030f06010c031202220f0801060b1303 66
    0x9802084800030052500454500c4c2e070741d001c0b011401d44c3e42a001ca204140170b041001c03018408101e40940102c01c000d10070b80c0c070361040082821030708070503040380c0b00e4071106030918a900900441300036001250200850f2a80703e0600c01032f00160100072a01036460040800c41404800196410f8828401e41055500e07528098a100400120f0402560203e4a00100d080d610103110301e10050001607a4a621100d1b50381600091860b1865605c0c1818140680d0940c100c2d882410100c0207e900440001c110210101140003805030248003030f08010325440030101079400004003420248240403410041e030700c840c10721600503000c3d501c0c00d01581c8142d00308031030406000804166201c4414010000441d485265480e1080580c003542c40c1940000c01c1c000200c2404204c1030344040b080c2444240d0320200d80c2c00034002c21168140c0d038000c030360100b514010440728400c50f0044249002006d4081600e40b0b0107042c158507039115046c803640c6041c00000d10040b041082e902e0650406006080700c521b55 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 764483489 1250 764482239 764482259
    0x2060703050a1205010f140f01080103020d0302031908010519060818011104060305040201180f0b03150307081b091510050c06090c0405060108090a060f0204050301020c0109020a170304 81
    0x60206424025844554480303a42c061040900070f1580c461030030501b034030741151000440c21b0304d0300340380c00f8400183c070035404c59070007898540c1102c0c5e054821892540d85400c04074158016036850542c1e040801402e044010340c0034180c3c9040e02e90490382c2040409508110b0500802c540c45108049000b26000840818207050000780842030500003043e0f0761610404081c0c2c0342e0180e0440c10129940b901400259644600444520040f18030440380aa050040911882e00d05100701032400c400000002c0a5100c51210b005e00d150010301110041364a034440c4139169111a14421582044090a402d884c545408840d00802c905840360001c07981c9602031050201e0180029001d004081200c00c00c400d03410000d040c407841440001d81031101c424010002a940c000d082c06040060440500142b6030f004a900c441701a4080e000058004801421030302074010b6501840d4907510100c0c41c2c054807207041d04840d5106200300e9211540360786070402203101c1626a10b0041a07680144001d00c440049 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 764484739 1250 764483489 764483497
    0x60f060f012d05090d06150e0103030e0609010c0203062707050604151b14010f0614042d061412071701020d050103050c040b1c0227160207050406030206070305 70
    0xc00d01e001d610f001340700c00101d10f048800090032600c0030b50700e0002c040003181941506018205400c0c1503202545503440080140d100c0f060102d00c50389000456041981c05414494070643d4040c2c15961a8649281006104260901070010084146800c110540000f050810903101c00a20145c00d283c00e011884141903564039010081c011440b45c03000041c20324101110049120f6581c10f012948a04051070a61b900380880321000360601c941840703801941d115404010006039000101222030020500720b818004201034090040b501d14920700308200d401420940b08400c404e0052600400c01f44480415a034425807800d40140c0002d1000028031058008000d40c1040050f0038084101d0150045900a90046580d80c0c4400d4031490a41414092079000001c112000412002d40c040140b20040003600024803e14144814051000c20261070b0203103048440d001d03800500c2d22400450708081c14001e524058410001c0c009828a440c1c020314003a00d5015107200e04102132658142c40b82d0304 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 764485989 1250 764484739 764484827
    0xb0a110c1b06041a0310120b07050d060b0c150907030206090909012a02010b09060f04230a0c091401090e15120607090e0c0703110f060f060f01 63
    0xf040009006944040b00b07602007a250030b8801d03036031306124815044080c6660f0110b00c450391a0f402d25000724021101e103d03400a0380d801d0203903031885020809401400284c1000340906c2e40401d00d8055044001404c00b000b59108205805540b10b0a0280d55288480e10000b58001c808114451142c00c080d00615003108201c0004540c622845c901c0c89600c00941000640d400c91003115150032950901036032405500a4a40d100c141c1820404207a00b1600d040c4864000d644030410740c0072440f90303490700803a800038203c08000c0c1403e00800b0040a41035401e54a8002002002d01003503034211003129150200c170503114130340400d18010210381082e900400c501d81c03004907400b19a91075200c5800c42091001c00a0241007180351850b1f000d05542982d420440d510b102040400c074079643c0c0081114201609810700803c41d01d200c3e03d400e0320f00100000d8003019409000240300421140e44621405444c0444800750319000e50b1004650f48124131000b20540c8041102450100b1415105103400c90 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 764487239 1250 764485989 764485999
    0x506041101020f01090b1e06090414101104030b0606030f04030e010c0503070b0f0112030504031b050a0902090405070e0603060f12030f0d061e0b0d15030b0a110c1b 72
    0x80d503d00340d00c40c00c44d00c1100c425100c24480104005240c91000308001c2c004082c5165041a0b0a242c4040b558810703000b1310081000840d1b401e1503034810000c00c510b00c000b20b802c9906002c01855200709a40e140c12910080390300c1c603001404601c1900d8003500341e9224003502c5042c03d400f940c2e0340e2070031100716408010407818000d0a1112401142c0c0500007013001740e001e032120001c54142265081c1501e0300c1640280c0f41004543d13640400240d12000f00c600302ca400c10712800321032148440744003040040798402a480600141700042c4007146802504541200b280c0030003030b9a80f0240240c9881501c2002e65502160400c005200c500d051905510204005426808842ca02c00c89041c61980a280d648001d104080342501410181c4d0261502400304e1491800081c5030718a040b114002d05e80c0140c0c600400301103003060650031a9880500004100e4442e282c0c000c0d901e080240c09103c042c0c0e1440d403400d0403d1007604902c080c61045030910342c150002002c46c101d07080304c030006083e11941e80507440 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 764488489 1250 764487239 764487253
    0x70b06060d141005010906210608030301030f1a04020924030d030f050c090d031b3305100b0a1707020d0f08150f0d0609030905150403050604110102 65
    0x1805a48665020b015416000c0040c40c18018004240803183d94032003410070004a005000e602e61003009216101c07601c20880714211100103401014040c25040304001d0b110120000003440b52039000c800d60305006440309a2503198a642c8051070400c12034005e50000400c82c0804d04140e6060744d1380318210903520300250f0320315900740020b0811507400340b0000044e88406090032190f5661091a401c1801244140d16001c0081c2c003003102c00c00120703070103018007402c08103031501000303d12602c44003280d00511081c0034409000400f60055480c2d160382030180910342081030b41c41c4492242d03074010f03101000202d0301c0a15049000440b5400075005400b0400c0d501080017a540d400001c3c0c900076000307500506000c0e007080000512105d1008180d5003044083e00621410003545601d41400310000d81e8a0561300ba007074404611405005840103000900d8081404d0616500560030b03410390700704552000b009051070448102a009500000c3d00541185000c00c00166410303109129411042c01601e9007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 764489739 1250 764488489 764488507
    0x18180c0f0d050102071a19090f0204200d0f05010e07200a0c0b0301031a160f090e240a0f1e0f06030e0d0314070f05190e0a09020a05070b0606 62
    0x6c11031002aa00c09840203110900c44c4070344501c01d164a0180080b04200880911303a15610030300b089a0f8800b84c041c1da0781320304aa0801e079204202d080071240000c4203640ea00b841d502201c0c0105001c83e82801454501000820300c0c2ca015481c0d80d000d5107150b9160110303840b0030462a503162004203005022440380350300c80f4000440301208034009144004d8425101c0d0f1544c1040021806031581114034002088208103400a4080180d20107040a2034a4a0700e04800381e01956021500c0e0450091810b621041000c54410380d02084084000041c000c070130391080a0a21400501c10301078594001e401e540c05000b85502c03410100103007820301c50f079054065951120010281d11030380166001079125000364045801c100092428465070386030070810380e1a010b10010445030044c00c560208150740c0e0401c240248074030160b420100308002041c0d09146104009401c084e1100d071118051640340e04005681e415610a450840070682c4640d45040c20a5948601c0c41000410003684182d0130710138251 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 764490989 1250 764489739 764489753
    0x40f03080910060609081603020a0e0c040911031f06050d0218060a0c050c090f0103080d0f151e1d0a090c030807110d0309050402090f18180c0f0d05010207 68
    0x38501178403582e01c3c20381051191801c004800070040c1d84101558010001621014030700000c0b103040030320074112a22001a0507610b4812940041c940c10b0500210841d000032410003580944070004046c1210100c0003855841c1d00514030a610115400f40301411000d407168008040c0102640300401c91300000200080b2560001c20340d20f000038420340844401c0100410000c580807208641d00b02d218907045041000e680d00500000340040c40110300b1121080e0742c4d03000740e007149155103000d12500c0c1144407504100300140c807840c40024002e81c0c0c0c0300d4003615042d00702000e9030b1005207400b200c0002140400c0d036600003e0312401900307503140d4a00740403c7d41400284041c0d40315a000301c1e0b64600e42e050081c1001400038401d885440c400c100d8000007178000407480200c44090f540982c94115410000b10f0b007402c00070702c070f030781101101c00450b8078029401c5086201d19a8450080c1e540002c0403021a40c51140c9907160303070061882d164640d0070b454007022462108d44503a001626002440d03448107 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 764492239 1250 764490989 764491001
    0x201050105100f11030a0306031e020f0d020418061b08040f030f0909050c0a0e120a1e02030f0c031203070e0603040c0305010c080604110a05030c090f030a03050c15040f03080910 78
    0x11b40007990b20340701401004251031108010f020300301d0880c1c2080801d03400240c01c1e00610b40c0810300c114001d120050854689800c102501401303c005005040c485048c180d0141000741c6802c1d07120710450003220001806080000d010341d030044a40c0c2c0a643c3d20341e80507521020310020b05401d000d400180011a041c84e801002d21a144402d160fe88819070301601400c1c0b0071003251042d12480660a00300c00070b03a030000b50b004400b60818404020320301c0e2800320302c692881000c0c019400d40503d0700d50583c0420006214504802c2c29400c0b01c00c1c01d4000350400f8054007041c2c80c480000340e40d8031030440e01460104055600705000d140d0a100c02ca54035660707542115807a03003840c00460f18510401515140034800c02c0710350041c0e0290b4921304100b40c1d200a00302c0c0b000501c0c60000c44c1022035005019100c408408140217005401c41b00303501d0b071604001c1c01039081289010082d1251402590140031440c80040c010b42d8000c0f00c031070a4015554007501c1e400b800800716401403048420f441c0060761321380608 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 764493489 1250 764492239 764492257
    0x110403020310090501470303041d06010309120804081c05100506040f050d0507050603090a0b01090615081905180609010e071509080d0e03010b010201050105100f1103 73
    0x50410294505a425954180e4802140d181d602c1040d480c0821000c00303424806c622a00540b038440d900401d0014800384200c0d0f0150144004540401e000d811203030b40c0500410204822240c550380d03140110265000040300404a810142142c00c03140e004040407900940300307020300c0c0c0c104070300c07041030000b80d40300c45c126894003a4035001030080c3c1d1034050354800050301054440e5442c05052020488140b160740c4942c03402601e00252440a1107414000c510141400402d4107a490400e050110765510800f81d0584540c22001c000103401101e900c15441103c090501003a251748548405841313030540105002c011944504442c1e82d0440103200c0d0031704c06ca12900c0800000c00e88102031a28008000307084002e40d80c54441c0003401080300003400d00031a401c0a2980b1007001d01c90b60201c5403e0519407151f8000d100303010720300420940101c0c00450700c0300294020040b614010004900741c40c428440c03107420003042c400001c0e21078400c525000072440d290030105200240e03010340701c0c03842d4400080 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 764494739 1250 764493489 764493491
    0x72303010e06030109030207060e061b012a2f0a03050a020d0305060306041106040e15280b0903010204030b190513080405010807140313050c01020106030b0a110403020310 75
    0x107000c0900ea090409401c01c0c82503000300200354080d07502035901c2d845130251509000d01b4074440003155492008a03001c00700381c850b60100504909a42c18043d040c000500580940840164482d1110340040000642d08598070821946a0054022241d90720030214011b860a000081c4161840c1004412081d071720907500c013644d41d602110000d00700010070801100b01350034103050000c2130f54001440c0d40c009400c0400c0c0320180061700d0016501c1e1250b42e20000744003020800701b100c42e8804050b0401e01342d40c01d0310301559590141754032000780c9450302c2c9240c0000348803800c01c1c0840d06404c40603040c0c40d50023500061400d52241c0b2204c015800c12074051181c172601c01480e41400302540104c3e500700b503040c5021400300c40142e803804103602403806902e04203c0c00c00c0000b850b071132103810140c1c00d1040d07001405589007408007040d102008840011b44080c0b1416a003510350354814450304040b02d811000305513a40d1100488a800780c01c612003841c041c07450520020000d0380c0e0522550303103040400c0300 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 764495989 1250 764494739 764494741
    0x1201020c0a03080c04080714040222033c032c18010815070302040e0c0712050a12020915040626010324111b011d03070803072303 57
    0x380041c0443c5000f4185101c10505002c104164031000920000781d454890f5040f48541150300030500034001d520307440c6820714000442604940c142201141600d000c0c4941d00e040b0b03604c40d07010303e140d45010061072035848101c801005002c8288144404c0c4103100b4036001510b1040202d100e09100000d00404401c140500c00c150011b2900715100d003800d84030b40c00b00105661420341041e8643c0600c50f07081c00e511000c040001d1000340710754100d601400c0140124001420300041c0e0b0a004d4004000031160200d1400960085600407015100a0382c0d140d66001c8600d03240b00d4011000c3d410034014190001c08130700400201035404005000603101035500e034445182181c011001010300c00703c41d10102c4800100500200d00000c0801c0311141890140000001182403420b000303003614980c0040e030b50000308008113810f910185021880d41c0c0c81000340a030203080c0600b800420340d1071f03a265006030700800a00000601e004003465202c64541440105c40d80c403071036156004500480e03100d8030800000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 764497239 1250 764495989 764495993
    0x60a0c0306090b06071e17030601031a0a211a1e0613180f0b1602011a1002120d0207060c0503151e04090b06041d1b1201020c0a 56
    0x21044500400c2c0803034080c880b072000c100104810b40305442001d405541d40d000910300d480d5081c00b9070300311542e010703415900307100100c0a98403103034001703440b41400242014a223001c8103c3c243c0d140039000c14020701071001d603840e203441048600c16480034440548490008000850190f0380411828842c102882e5054071381801520b41c45420040200c801000034410b02c0303140d4440015214004107001800540100800b10901c2204050034005000350a5201c200007000444c1c42842d0088006003810001e21501120903403c0e5034140ea034898099081269103500d0703181c03001c4114100300140c0144d03965240010805207442c0d00448030400041e400046e00b000300441c520502c0c0c9074805505e0641e0850401c000c000181c210f0203140c2910230003040000480e00c19880717034603840f4803000420410000d4214600042d08140c1200c0841c03080c1d1070107103000c038040340c586450303615080110050315089c005030f00609040c0049a1030f2035003250280003140c0b0001024401400346000350380c01030841e80d0040c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 764498489 1250 764497239 764497241
    0x303121b050a180e070e03030c0709020901091809061503050307020607060204031e0521090f041e090c1d04060e15130c09020a050a1d09010f080d020613020d0311060a0c03 75
    0x2500c159401f0394400c1250a840c00e802040440a407080000056590101c240048840c0056504074004480e6000396400076a40356a10200072036114640911812180e131408401d030b10303411301c800b51094104001050043c80c04070000c0503114410304006040c0340e22502e031896052514525a0400250001c0010611400b081b0481034500f86c8090300e417040610045d50242d5005420074a030240c40c040100e4243c0c0c0d030701d43e00300d88820121450041c60710107a0f490f1890151181c0c1000791980e01050601148000626010b0312854030b0094072800d094a071551104000d01028040c02c81502940d018007410010001c1181d0203184c8601c2c4000050999081280680355281d208101c03181c070420101c000b02c0c0d081002d43e90749800d18280308074114451007036401d002c588040d50f2940501481d00108042460056010940e8103003001c07640745040a402c240d80e42c00303094409080301c0d03408c02110001490803d0807000b525100e0310b0280d2a520f03c4d501c24614041e030a644003142d036a100c24124241d6a41 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 764499739 1250 764498489 764498507
    0x40f0c0203181e01231c0614030d050c0102041203120f0507120e010f02070812100f090b01050904050a020a020f0a023a06060303121b050a180e07 64
    0x4112210b14805401001000652000070600d44c1403248561008a65820005241c0011104040e800307545203440089400c01807400304184068501e04500030480500481807060803200240c0102100320900b403080d03a0b13903001004c84100c1903400300804a49690120703000d0040318806c0c1c464400d0501c490012400780d4803405a42c0240c90302e4981000142c40e4400c907800c0c0090086031001400800820b00f0501511105175140703d220700000d080720800c0400402000f1040d0340380060150368444000344030484040784901001c0c02022807007400a403010354881001400c050400c0f510b0424640d02050030380b00e084036005040c2d5404900b4001c1190180001c2d0006120f180241242442c1540054000d0f115000c007001114420b048040701484035a1040f807100c510200c2030f040e454100d00d04000038003194001280012441441e4400003400b82c0913029030080c110345c12910400340a542221240c11481051003005100007541c160300d554260300c00041c280c01001381e14a440c10362009032813003030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 764500989 1250 764499739 764499787
    0x30403112b02060307230307032f0f16060f0e012a09030f0c140619142b0506010c0f170f0c030a0f09060c11040f0c0203 53
    0x100d11030341100507400858a14070129411985a5140d4a45617001c031484608800f101518801c1d00e41055440722058014610400301d40d541070003d59845869191030501905142103c102c04640d00702205800f0406003410000321030100d8144104a15841640c07081d03220281d503030b541e0741c1c0604440f80039a07014034900044c9420003403000104964069115500c1000c01810700da1000c14800d01d40e500ca03d0751038004540005400500415908120b91503c0c034611529100001c403103002c10003030410805a03203021406c2d040105040c00d0b0b00e0b500b550107040030045020780c0e000800640d910a2144006641130081da180c1112a401000300110200c8802400f050b0510a0000c040c200091120416026141c0d0080c17120718409484c0010004a000c4d202290101c1c9202045694040c40004082c0c0281c01c3c4030b03540c640b0f1110389a1816174501c13105000340000a80b290301d01d42c010441d03413018426801805400015200003040350201152041005080140c0001404007400b0076042c0c00102400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 764502239 1250 764500989 764501029
    0x5061b120f1b0f1804060801110a03050901090b070305152101140c030117070504050a091e020603180a12020a050607080c04060f0e090103051c08040c06180803040311 73
    0x2c4043c0449041d004400841c007072406000c1e00000c1684903500044000c0c00103000070f02041c6c400c030581010343c1c0c0101d5040e00000349000e0004001b8032050142541e802d41159607060303030b922459403c034041c140c000c000c000300b03031046ca0314540c140d2902c620880170f400c3d40150000c840b0b039141983c4e600f51100b040003040c80c0c1050400340b10218000d103086a04403198608422141d8058600c010b050440c558005603215280008002d07140d100d40c0c000195040c07050111740240742000911036100c1301c0300140a50000801c5c400144500d56140408688171040d030100c1c1e54040581da19440e01d030b0000101400160041c204d00810000100845d075040550303070601401524240d03040c4100e50042e1300c06c00f410480b1007040c01c01d00c60b005407140c091110010305089203640e101e0074155606c2c030a1007001303000344008400c48441903208018140c080c0d0781c0607100b0700985181c0342003112031003108100c02d003401190610005014034200010001940301e0962440302d03001c0340c002c01650b202103800c104610 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 764503489 1250 764502239 764502247
    0x10b030d020706021e0601051c08030705030618130615050604090c1e1403040f080d06150c02060316090b1b01060b0f190e1009050f0102030705061b120f1b 68
    0x90b17012032010b055403c02d94070ba1200b21a01c8014850700c800c48500545540d03c000248a030041c2d01c04000c5101c0c4005a58107002a81c4510740052a00c100301d0320440c1c24101190702e03000103030094012a4040f00c9103030448900340d48520001d04141c1c0160300c09004e80b540c5032880242141c01400b030080c3c06404202e06144400c0280c1e0160842c03002e101e082098030320000008080052001100c07140c030707401505052b01d5821a402880c000c05090161400c40ea0704490700d200340d0343c484d0840000c82507014014a0071511074050851009400c09000c80501030500b0001c14185003050250800d0350300c25210300c5e201001445241d0840b2200c0d00011f061005c02c0180044091000044403001204106245842000c61400300c1c1c20b40402d8034002e07840360207a050b03460080d0740496004207850040b61010a0100c031040103980d680724090340100345402000000d08a00d100d0320100d0815144554044e25151703801042410800c030844606201e02c0d48681400804019007035131040714a441d582ca6494 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 764504739 1250 764503489 764503543
    0xf07080c031c080c0a030f020c0f060a02040f0302061602222f09040f06090608120301140d030e0306160f0f05030c0901020a021c021201022a010b030d02070602 70
    0x8000c5009002c407030131010000301350410380d10036880300401100a8008644401051410319120680740385a21458400d0310007048900310b05108990072180e80c4414203014518550a1000076088890046941c9078250310040243e04d643c03c40040c0003480510350010880316151500c225040c441090b05044202141520602a800340703030f00c0140084411243c40303054440005002d4a00d100003401a9403d00c0c00005204845401001c2962030110540d1181c50082c0615183d41c0024401e0312840280c0f6032408025003000e10408003c079000349804e40241141c13402203403400b98241d0b4010a02d004103140d5540559001980398400d000b189811002846880001804c601001c5c0c075441c0d4440b0000307414041c982c003c00c051103150f0382c0544080300c56541c803041a80035030701190007170740107103e040340400b020340040c0701b21a0380706900250070001152090280203081c01c07102c0c1c500819966194007184e1980d08100d01c0b190317000d0715801804035600b0480300904241c481103910681e5441442e003001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 764505989 1250 764504739 764504747
    0x9090c0406120906090c0801050a0f05060d03080903130b03010303090909032003040504050103050c0f0d080322020619120b0f090903040e0f01030309061704020f030f07080c031c 78
    0x7440782802c001086011090802500400c41884000d1024002e075500090505042d004144103c0304004104001072440704d86c4810f03a40d0891701c16030b00021440710480004d0103182c1c095000804001140c0c2850404907000710142c62170b40000c0d00d810404001001003551125108001e040032040a1080c0c1d0400c0e5005052403009003880c4d10404a0045c402c440b0940405c142c07001060010014011075960342480e035180c04074491180d0080070321800113481c1d030034041c1208038420b900c41c210300d140d070740c502d41642441c9440001e442400740c039070000c080140e59030001400c1003180840804600314410702014041400c0700502030710450400100180340c0d5a40200111300003000d885484060351481c0c031480c01c0d40b04e248c101d40407515006080c40914407445407401e0503203204e5101c41c20031944542d001ea1346132070854400d001c0d00b00f20100241c0182000c0801008180c030117000c6132403500900d00600d0600c0301c2d603017000c5401c1d406000509801d00d401c105071009280c3e0020800f51008108074014 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 764507239 1250 764505989 764506007
    0xe010519140f09040c0e0d12020c0628170a0507020a0f1209170a0b0408090910030309050415060f03110a03091e021f05160c0e090105060f100212070809090c0406 71
    0x9400360b50230140e24102e00e4024062002c46103401444180c0c1c4040d0f1140c0d504442c00002c49144072000345800d90008280100c00405502040007240140c54ae0f400b2451009004020114421401035040d04c500045034440d0091002d803003000307540a4811030f82c0b001800d004d03d613409001000d234041440d4800600100703080c40f40c075400800c05c1c1c4055803103041c09042c3c0c0c0b003000e582d55041900d92b420805440c4c0350710f04440036039100b50388140c1c1683d41c036001c00041d942c1e0850066190055804100090b9024942601c5585440d04011800c4800c80c072503003007c0d42001174268042500e0301403110801c1a0f501110000d13822000c010344c0d007000c46130049003003802c5100c86103100c00301903001080c1d070f5402501910020120400d600c003d5800a240110400c0c00c3c0c0d11481100030318441c08911070407810b0203410b2003190089d12103510345004004002e0908507021290040d801010885c41004030101c009000c2d140c01038048680d522608005e001c01000002c0079502c8a00044c802481003036400a268 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 764508489 1250 764507239 764507243
    0x9060e0601021b151c0605030d050304151e0606020f0127080a120204030f061103071403060612010b04080f070b0d05041e030c050601060e010519140f09040c0e0d 71
    0x201c402044c5120655043c850400b1500d0100b240d0131403851071060f66080101556000d038207544441222030002c0c1c400740403e40f4020070804e45550300300100d0032190b02280410aa444500b0904900e40b400c2c035049441c1d82d0007800040c0c009185901800c802402035040d400400301112055240c6468051031251500300018054000081e120003c51701c10032104241c0890404219a00d5581b4500018024554402281c04600b840420030084050605403032040c134058540b40300c1e84020441c45a03e40e803000340400d621100070310015241207a0200c200c0d010740b800c24116590385051044040c07421451642210701d13a846000240440c01d94202500c00801e015a8040750b291180d242042c40226900c0e401c00c210711121956405055000448440c07460013042a10b075141d13260501111902c0d081c102980c041801008901800841003581c10020102172920032804055007241500c560f1001d11203010b2504041031120341c0d490103215000800369242440d000f005003101c0440c2c01c0000030300700 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 764509739 1250 764508489 764508499
    0x30806060f180307240206070903020d020918010f0e1903120f110705060a05060411120c09030d020a030f05040e010b0d0f06060c110409050319140409060e0601021b 72
    0x3260712649041041c0707130103071100c01c900d50400b004140400312001d0035410481e0041c40ba50010424003402040d0386002d594025140c80c04680b540d80901c9240c06015181c0e00700048104401c180c9200288114280144c0f1700102180c0c001c90340c82014500900500002415a051040a00003076000710742e0383c0b0740302d01d201070100750004501c0d01d8a00909400c21880c03105000040d02200700100030400d10710840041d001007100303869400c184030440310018501c0115590812902d02e481e110300100c142e029054522003840c042410004c00d042071324030141b80000d6844580d034801019006880240031450300c0c40e1040c20310703180480914205c0380601ca407850000c40045c030722084480540200c00086003045013070100d196105d200034900c00d20312105484c0501d440360038409a01d000e0181319080d68011000351308090a110300018075040300a6800240311f08585031906030054a00584014100c805000403694641100c00c400204002c05660464009282c0f841c2280b503100c007003040ca0328080d10 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 764510989 1250 764509739 764509777
    0x2d080f150411060325030b0306070e0609061308100c0f0c02180906061c021008060604080a050c12190303020c03040806010f0303030c050a05120a180f030806060f 71
    0x104012016410802c043c3c028000000f00054840303809085003071a0305040c0000907000004c4c0b4128111074801c0340b120781c140c0000d00820205482501d130b080d03a489000304450302c2d00020500184050b4841201428403509164040004401c02d11404442d6040028140003440700d004005045502451f501703000d0043c0c0c140d440701035450724903a04410b901420300560680c1440c0186654a0500b2a10941f20b4206c50b20208201c940010702c0383e0322745038003500c0c0b81c4015042e408140c60041c0300400d10764004000780400240c0e454204000d020315402a006846c5040c0c0c0340040c0a8044515600c94201d40e09c0070030400c0f410302d0301003480c2c644260186801138640030000c420710708501c41c80d8800d045c1d07032085c1000803410043c00a0010202d0340309482c20060f0f81030240c3d059949010700c14a680129006118000c4c0780014030404540c810365650380024821502103050380801c2e030030481955050002e10b4000201a00100707115000301d000c60f026070909180410008080c03054a80c24202c8002c0c87c1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 764512239 1250 764510989 764510993
    0xc090f091814070e060a0e0c0306010216030308010e010b040b18040209040903020f010f0e030703210504060207020f090112060b240703020705061809102d080f1504 72
    0x1440d80080e5101440d107110310000c0403020383d100312070b00030104115502804900246808000c0c10304075000c5600e481c0140e40d880054803801e4100401d15415401030282104e80c0320810501c10f00036500c41c0d244c2940a50401204110b82c40050b005243c610b5401c00090091042c2101660b2400500c00e02400c3c2d40802c52000c540a40104020309410a0421000601b055004981c5201507160300c03000704041da05200c6001e0035256806c02801858000b0070665020030b2058180725038524950000e403000c201c0e404c206c10121041100c00ba10380b5607010406d08110310b0460400c0507050f80480d2051342d19410004040e0920803035000003030160707649404d801c0c03461302d4020032403022000341640111101c1001c06080481d5000f8202140103001e041408103081c5894004e49019100c010766070304128107003c0c107200c081c03400904030f5040c0c9140c29034005280e0103040c032851115a42014080031000b40150307040303545051908100c7c0300d90449101000c5401c40042c01040c030540140311400d075078850b8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 764513489 1250 764512239 764512271
    0x9062c04091109010902120a0614130e19030e031f091e11120a0b18010f151e0b0322060905030301260703170f120402040c090f09 57
    0x44900300d8020f0040400012080310641c060500180400c50780c031580e50b2070340001012070b0702d5401104c0c1c02c0c0d0400a01850171b810801c2c0c00500c85018000f001540380003260100386007003c2d00300000c468200da621100c0c20903034406c1c84111080d906500401d00c04a40f076203e0701a1048201c401a6410303504c800c08028403000088004041c48a440c1280c50812507080142003009480e00290240c00103114511000c1c03000610810040c1d0420059016902c43e00004c42d41303012280001c2c1e00f42e41d00e80a00b80281c418520800584c400270104552919252078040b2000005480d48419025044c0c001001030040718802c1340d5211245440245687c54a1120f40700420010728020b0b01c0740e07113046001c10070800004006d5058842e09062002000070020002c0010390b0948940451074111920800006603806811081c51020800c520308080380341040b28116041320390b0960304a400c11041c8401e504240c410016040113030f05e4400c2e0744908000201e40400f40a2040c0c80c00f0507502c448018440d201 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 764514739 1250 764513489 764513513
    0x150909020721020709112a030702152205090108011806091a010b07150b0102031903110c03120c04051026011805090105060112180f0309062c0409 64
    0x601e01c03041101203c1d1010b0b9810380e410000047e00360010300c0c0b910b242c00030003841041800305a03103070081d4038005080d0309201c40d10500a44c800032158040c005104920b003008143e802c40d0b00741410710701d0351910303180404c0754450060780b0444543c0d1400320001c0d030801000c84180480742c1c1010000c5402003c0c0e00c1d0021084001514810004a05c9000840d0030140c2400911009010340c541c034011000025281e401c55032134445d4280541d01c2044201c0700c0400b441c028042c0d00d00c26045c000f6802c40816420040d982c000d00d44241c443c3c100241c80140c1400048190b504100d25100e0700e070600e41000c01044000a907810610240301d01c006c2002120421815211000d020f40301190780c4650b5134120301e1207114080540039042604010005606103014841d640c822401650303064400f00c15800540000c2084140070701010144046d2a40411381000004030f032039111766075100c00146880b00c002e0540c002d2180b11041e03529284910408105a40d400000481040318002207500d5603141c91504020 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 764515989 1250 764514739 764514749
    0xc011b080a0504090b031504020f041d0a020a0801050108150a0b1003020403060f0915020d09080f04050109060c0206190c0212010209030d090305060a11070c1509090207210207 77
    0x4001036140e0060b9844070240c41260186030051050345440010541c0700da4140307480b1014506078000007005403034890035803070300c568000d0000622488851890a80341030403d950000c540e0101c03c060046042074010200200715a1000304100d504100031180c0b078420380c0c002410202020408903621030070540c80b05d1f1083c407004003e810f0404c0103000180194200b884140e884501d40421404071002034007942185d503601154160200700c0f000d009000940182980303400881e5569010310025100000420300c02107001200c5031101e02e8103000500720411034110004000042c0200b00041c1c0780c51050b03807140b4078680e20078801d1004c940011144420080d50195004a52030403044c0d0710072041d40101100764041c0c040d01d85015400c44184d035840002e201c01400c5078404000154100c62030ba11001030102c010560700c2c9000c00681f26807040361607541003445c5840c108010368800302c1d00f01c0c5030b54000780310302031703007981003203c2502e400f00c0c0a200c400c0c01004602c1031004842c81c1620a01c5000b01406e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 764517239 1250 764515989 764516003
    0x7030c02061b0a1712062b0b01080c12430312020a02031b010e090103050106060e09070c0f03050c0d021b0402040b0d020f0405121b01050406020c011b 66
    0x307519001d1107556025156003943d07413501514040301c500544804980300c803202d4440e01c0325035481d2a400d010840b03024440d925080d080c8002c046003401071503003080902a0141d0360045855051448943c10102460300c0d0034410840e0002800381c0c881d001c04d101004907004a140103410002245005880040c14034401110005021801103110803403842e03002c0e2409007070300000c540e207664002c0e80e640381d40d504080c0d40f581c000c2c40321002c5048840d030805290401071400c2002c030007404011a0b41d11030285c000302c071140d44404c0144074595000d00d501e1404101218098000c3c241200082c00390502d400d00a0030341c451484905080c0b500990031a551b6030024022107030030060401e4001d48406e0556083e02111800180c075004628242c000d036010740d00d00c40c1001c0c0c600240400088002c0d40442e0b49190500d10038400010350b950750300d400c1c8420f00044005030035180d0740e0354a64480b11100300c00c95814001b09100912802d5800508154040000c0c05c0913a09184110f9007070000c1091002c0050500c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 764518489 1250 764517239 764517277
    0x1b090203041407270510091803020105070309020913032706112b09080118030215010b0a0e040e030307030b0109061121070b012d0b07030c0206 63
    0x3181c44242ca80320b990014041e1041c007510b0b501950b0000c8801007115280e0201260000c42902c469408075800110041800d40c02d55524030000c0103881d101044c10000d02a11f22805042c10780a00840c2e0740180145000c1160108a40c0000c40f410300280c00c0c0c107040c01196048004040c0240702200d6548000d540b854001d03048002c9450080d102802100c0005d42e008a441410000001d0801c41444408a000c07014500012038504400c02c581c031000300f04140413400044081c001e01ca4125403402c0400e40c202200d60504010740361a18402e4a21031007811540108191120207040e02c268013503918150120000910004001e0102008218424040081030125480d09913224011500083e00e89101d060381d12102690121451407005115400c0110784020f81601032110b40b10170320400807000e040c80d00075140c03a036542009070840c0740311707c005400c201378010000c03c0101c086684101c130100a541450643c81700d60041c000300a044c800b01c080b02008545c0c440054603048000c3d110f0107d24 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 764519739 1250 764518489 764518493
    0x21080f120a05160503130308040f0f05060f180a060e030708120702070503160504091712010e15030703080f04080303070816050a1b150f0b0a050f010207031b09020304 73
    0x81a080c1c40810325094543d62020f00603004809480c42030031009250505903a49441c16144040018411503010068003112000915000c0400c1c2c5035030b015070002c08061034850501140b5050203008140d01800c4071140610442c000266411007551050300801c0100303000340714031b185005a540040c0aa80c000c04d080000c0300742c942c0d6151003180c55a00301c0f035190399102d040c07544500481c2000002d0b07440c07030401400581000d400c00121544943c02d401d524107800700000c400c0360080d8403c4850420304000400c90300c0543c1d906940c2203840499400301540b8503d0002c2c0d80ca509501c0020620307140492207421410030031095900424500742901e03603e14007a44014142c00d000c907203604003d14410540c183c8280b05000b80c0d602442d668a41e0205800d140750210b2164010340c104503007010449015565545841c014008000310700000403801c034600740d0422a5460072038001034002c00d410b0f0300c80c4c5101d0b030b4000ba00e80116600115070462000e0050080c00c1c04244030317001414030398000020300c01 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 764520989 1250 764519739 764519741
    0x3030e030a181a032a12070f0206060303120c07020a0308030717010f03030c02040f0222050d030906050a1101020301030b0609090d14090102030d0606081021080f120a 73
    0x441042c6000003059a92116410b584003400d1407400b001008040c40029540400071035120008841810010300394160108004d83d640c1c001c54090059034401c5080c0880281c003c05403050603102ca0000d001d280c0790110111390340340914101d04400b9810040031a0b90301e0202e00480b6881c030380103003c040c03910b07450f418848600d41c8152850000511030486c130340000c0038202c2503541a04c0007010303e41049442c0d61011955120a0007003a40d00954520000601444501c0201380901e5008034001c10020115003240c03c2680650103d40a07404610f00c08000903840540032040c0e5000e410141d448120603001111215000e03681c0741e41d41d605c000004028000c6846025108200448084403240d440d402a240c44880c5c0e0301840010414a403401303a2034508038000740211600602c100e0f4203043c0e050144c80195080b50780441c2c0403500e000c060140401410200002070403455902c039040079900251114141c81c090000342c03401d0000706205900302c051104135814001450040419818a080004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 764522239 1250 764520989 764521007
    0x9150507080a060b0d0207150f0c1b15090516031113020901141809100e0606130b090d06020c01060f060201110301120204090203100507030b09040b04030c03030e030a 73
    0xa00840d00d07000020340d019030140103007401c0d03c05408040c0d06080c80fa041c10000303500040c00c221002d070a1005d401d01886414400c080e1403d0400101090410803804090099000c000064030b004100c0c595a5001c9100495484418042810005124682e034200513041002401107000111455075000090012066403110f504c3d00c1224089803034115026210101e100d144002030210301c0c4007000b0181264614040c000047c1140300300c00c4c501110350001407148500303c40c05d00044900d0041840700440a003021035019800f50b90483c82c01e408116000c006068038811300c0c001d40b0703000500d1b0606486244e2094801580f00310290b40721049006101e01a25084c0a60b038000713400e00c280051202c0c0705000f00e0078001032040b4403900e186d007800d481c440244d170701c800c0170390b0400e48440308a0300685041000e01c110010031000061130382031259000382a1aa4a51044c0c4650780f03080034000881d02007061190429418202078070440401c0c038080e00903040a20700500305010120700e050501d50059020 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 764523489 1250 764522239 764522251
    0x180c1305010e13030c0308220f05150c0d09110607030f020c040614060c010e070f030b130b010e090a0b0c090306010b030c070206070314040303030608010c0c08090f04091505 76
    0x10100503074443c19601510500100c001e000503107a01c0e00381d004a4010601283c0000b1130301203a268040038400b03c0c41d072034840b000040325280e8190103544188002842040c41146007190404003d040030110f4550340c1c001c0c1403d601ea56913a0b60454020490802500c624012014007860b4a5a441d0b05014001129020828025020300c09804c800303072603e071041740241c0d20403071210342c0c0900c03d00c0140051a0040306100310550b5880110406084040040000814416041c41c11a0f800c40c6003240b10104040d1405603041034042703111001906900200741501c1e001d6080703081c142d03200e07c42246807003080100540349164074020700110072100070007016151410390460301d1907644c03092507110034803040703840740078000c010b10160005140c404014201503002e072030401145503800808605070741c02540100c0220b0342d81c0341c0c2001044c2080c0110000310015040001402e40c50b6292540316201d0000440d108000c80c41e400c000d03564503544160000c03a04103807040702c04e40b2401a20402070200740e8003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 764524739 1250 764523489 764523509
    0x315050411010e09070c0201090f0902040521070e070c02090403080105041404050727020a2a05100b030313080a0c080703050d1412070201092009180c130501 69
    0x548181c1d500804541188803005408003040c0d0f6205d1800322440b40c00c00d03c00703d040100c010000260309036034500d000c0182600c600300580ea0f82c0362008001ca684540b80742002000a440101c080540380031030003104483c02c4102c0300308030b0b40c2c51003c101c480012500c0d00942c045001c2c014841815441a42c0030b059501c191800c202000d01503040a041e14011100200b40da80b00740c00074885100c1d84492420300810703880140d1303500c011010003102a130b00b08501450000300b9003100710032107944010014a440b02106100c03008040141c840607117800d030700c1e00060201600c405003104292002c00c222850340ca03000c010340c9200d90315900ca0396100d012000040d00c2d05503040ba000b03c4d4111010401d00101c0e5403010040c001c0000b405030a0f10038005030754506c503c0707510510144103642e00c02644140720301d1007540005801b40f0b10745407440e40c0d03500344002d501c003609810007007842c61b803142004035420103038001401062240048100e481c0c404401c142507000b05c2060141022140b041e04282d0580e40c1c0000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 764525989 1250 764524739 764524763
    0xf0c0f0f1804110f090622140310050f130311070e0417040501050a03050c2809080105070f030917070f0b06010203092d15040602011107050c0907020703150504 70
    0x410140c00f50306020700300168200b1400f100c071b00d0090010300200141c560721103c400d0126580000300c1da0258084414004540301904043c0360901112000d003841c154108218100100b00000b0b00304001e00711129082e02410250616001e150541000e90030002155082507c1d8031110743e0300002075400300c6882c80303114031104001000400b914140c96042c0e540e41d0a0402c2020220080e0001508540c2800c10402403170f000aa401a1000c1814400c44c00459044d805400014040cdd08650301045d003d0349003006111035540e020481c070368044654038012503005c010303080000c9803201c0300100010074500000c0705810010403c0040f24000e003c2d544200300380e07440c48010380e1248121031810b84d00008080078282e03e0889084c843c4e03180704480d1810000302c1c0985002c01c490440300c2c4500b6204400114040010315424001e04186c01c40e601075950901195960725561103504588a500c20030b9158001803040d8402c00048000399000740d0024425030006c5440310041c441910242c812104100c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 764527239 1250 764525989 764526011
    0xd060504090b0f0415060e060f03010515010e01021501090608150103080706051f03030e041d03030402060a050c070b120108010b010c1104090212010506090f0f0c0f0f1804 75
    0x4070404580325000b0707042c1c0b90035503603032403030520245801081143c12842c0c14030492030b5903003988100009462601d9544649091100400c00214a807201c1c2a00c00ea0600e402c000482c07a17035908040820000782442c4074440c030b410006038100590170b00f018501c92202d80c000580b6901c941c10100445820750150f40d000035865000e410040e10274040030300265030400070038000074143d901c816800b9418071a1540b06813144007512226129035801a00042c032040302000d11403520b032181030100444281220150350300b8038503907a164000100040d01c603041c04600c201441d80514202c400380000481a5115181c0310000c002c616000403044d021140541800801c146070705200d41030b00c09405031103002c2000c00d50395031148c0c002007107110341c0d81064541d030b89640140c072080c00e1074030143c50400001c20075103003050601c40c10741401030240030b031140340405024486c000140a540c100201000d0a591002141044103107441a940f43c0203030308800040c00c1d084400700b4501f159580d02e08441c1803006804031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 764528489 1250 764527239 764527241
    0x1031d0a21021b040605060d05040c090605030705061b07080706030c030e1b030304080d120e0c010f05031b030718080601060f080406180503030a060506031909030c1202030d060504 79
    0x1041ca5200564860b8004005601062669011a00c2d0040001c81c0c80354890002c60841d400000c21070b00b4076a00c1e03505000411500e5070381c00700600144032041211500d014002070faa902c01d0311596015840010784044111a0040140308a8103e04211500281c0e20f10680d603840c04244141c40c0040d01d0000703100101e0703200e8010740055444580081c9204002039920341d0f0009442c1c280103905210800000aa2203001c0c0100040c01c01d00703031924412126548503a0054517654055802c00307401801500200341c3c0c111000030002006031410645035950700151121400001c0003004103074801004000066034010000c00c800001d041001b100581e580c803900707030350360b00a000b04000700d002c0040440d10b1901c02c0020075403080c0242004100045594580e0400130107a81007a0f541c1c2e0000801c018900c0482c1c05024001d03d4207460080c40e40c5403015940b0f1030102d5480c1ba08140c1500c0b41004420b0503c207092072345078541c106c1140580594550170180d501e42c04070000d0103036039082400016076031030300e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 764529739 1250 764528489 764528543
    0x40c050c1501060e10023f03010f0303050c0109020402030c07060e06040b06131b02011d0c06040b0304060912081b0f030406020c101410050913060b01031d0a 69
    0x40e12480d59000c1355100f0407174a040c00c800302c642184a061640c11100c510080018201031200c900345019003034584039058000740c6112803407841c071001c10040110062200440301220b4040c50040d032034005510303490f40940700418010303500c64000300501842c0b250f0900100f00140c0f01f12001c102c540014890b040d200d07001144c014001520faa8009251814a00030f182d442c8440301c040002c2066280c822151010414609800180c0d5100942e0a4644200554200c01d9840d20010301481c0300310b000080d00c034403907070003421880300c0b0100c0803904003c01c03a004982000d90101c480310183c03071a800d00421101044400440700c41003001102d0010a4050807a0304004d484803c0600c0c65a65171a250080e40c00b28038209510701c200003503100300e0301d1688030340d00540c0020000d5802c10b0900081c00300464103141c1007d07100d0051001448504080544044402c41d403016021807804001c0d001030f0003e015461031098500015207810315010f00c08a00050218403550544203416858601d103049066 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 764530989 1250 764529739 764529749
    0xb0708040b0f300708092a012a0f240b0306010506280905100906032a1817061b1c0e0a08070803090606040c05120411040c050c1501 58
    0x1000300401c074005d2040b5291070780b040000c412030380032240600035007000b42184c254018418000b058071941c150384c01030440745820400c4c5407200380840786d45840350403400d8503500200700301c50410241080018043e601c41144520020110b071134030a42d003080c0e018041a036045031207400744100101c0e062604070250740c202503081c0000002d170728611381c502e0784918484030144140808450002003942e00c1d48040491650981d440007404c600c2e001014069030982c1c1c030300842c4d80d0818030380552107600742e100c4002c81300e030a807134490480c3c00184170b109804001900700318404441d64007100341c14580000c613280544e842d0312882d00c010007040120051409030501404032244043c18103000484643c018038599245001602c400341c80c20340c1c60511a030312019086800c40e002000700701030010207000403540014151b9041c056442c660750000c146100300c2d0080036070b100d1b00c0030101e0184a2503030052108a6001307042084080c1040b00b01601c00e0f0003c054a40c680d2140640c0c601c522060903650380d040369 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 764532239 1250 764530989 764531077
    0x1701090f0606050f04170c1f030c0804080306040c090e07050403111c0209190218211015120c180b1c02041506090f0b030c040b0708040b0f 61
    0x1420107446248031b070341c1300c0d109000b0f520580c059851903980e454640305d200741c54402c89085104040c41c006d01500d9501554900348005801004046400c030000c4a0f80100b08072000103e9049c9581d0544110740181c000c440c42050f46d41c104a06260007000510980c1d0013000c01c401c080d03034000d04000383d04551044044840c0708400c1144010305020804a401036100350510301501008084041241c001c2e60400501d0751035400480e0a50521020500d141081069906a4545002c0f14103549100320078686480c81e5540340b14107410a825200c1c0310142c81e1411214a01542c03a041c240d1b00d5035a180200f8046400e01c0781600c148107000d1082d0490b04501401030503030f038030f0101d42080c0b41802d0705006903081074440d900f00c034500e20301c0c6480ca405804075484075602d0908204004a8404040d000804031707400800a20605030070203000e40b000c80d01c001915640d1a1003c0c9440d9903540540e42c441c654243c0085440720480c0e907480c01614024506955016509540c101c50040312410307141810149 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 764533489 1250 764532239 764532247
    0x4170601082122091112040308070201090503120f0c03040f080706090f15050109091a0c040302030f06151005030f040c17100c0215070804031701090f0606050f 70
    0x480c9040c504803442c91003036802c2600302108440c40072180601d03403984901c410b1502c80d0a02040d00d080c46503491140f0000907450810401201113401c012000c1e10181c240324101c2c0000719074500c00d4021200c000c0d48102645d45030301040811400401d0103884030042d040b21507001441d0309118509907403045402586aa607440855100c140c0e95a0180206a40103501d40604078042941e01d041071b10000d12030302a000d0361a40d22000c4004881c41a008003502c523060035001c0c00030920802e1042c202c15450942e02d4aa521345101c4100c035072146900c003d4041c0a0303040ca8410068000c54040d110780c00024610101c101070303608200444040008540c0071501c1403000c0f5694004001b000780d0b0091003400d6103071540e5111051101d9441c1c5100156159520900000c5100c1d0b4280c0248941f822581c001032070440310f0342c0149003800c20700401c14800c0025541c001410306118040c424a0078007034008071042542c5810511014006500e000071a01d424810700041c1c00744610f04503004048012011810 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 764534739 1250 764533489 764533513
    0x80402030a0308041b0b45040b15070b06060304030807030203190e01150914010312051c0914120a03020d02070b0106050714030909070305060303120702030417060108 73
    0x24208003800c2030381c185c01c0c0f0000d03091404aa40c42100c0140250320b41c40b5403078080005100034100101e2081d00440920058000324000d06150768249160220751058503c20f021808100201a44840140d0180f2001c001041415007040200b8400d802642d40d0740050b030b1800140039052006903801400220300100088545100f6805581c20101201c000380195a200c14400262504d2003100c1034641d41d94010030318699507890280000f046070b940c0a0004030402d845404407840144409007842003200011a0303124425811294014800508150f080142a61040040007024030440e8203600b140001c83c022100043c0d003503100c1c241e0340d0b03000345080344d480412006904101c0701140103a80030300200000900c007001c0c040c060011603551503180c59842c10400c499174414420400680c05c1040584841d440b04442070358040c1c41d0b81404101030f143c103400319255110301b0040403a41c0700c0003414442e150764003100038001c49080059522070126401c034840d40316a800e02c5110445e46c00f00061040c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 764535989 1250 764534739 764534747
    0x3030703260106020303070f020a0212030322081902071a03041101030209090105040e1207060506010201060f03080403020402091c0c0302041d1c05040807080f120304050a1b0f03060b030706080402030a03 89
    0x11403203192040d41d00c402402d90201ccc1010001840300800d0780c101000300035441d108112a4203880c10441711451342c041e80d030303120701d2000d1203940503030118200840d0203041c205000f000707014000c000c0498101140a00190109116001034030201c68501a40b2610003941d8402c0c002c1d2118060000c107041c42f44c1e4605001c200c014100034a0380201c90150000500f52202c100300981030940c040d0b5400302e0945060030009003103800c980c00a41c80e00007150003e1022804401c146c1d03060380e505460059942c015440041c69660f4940807000011a0000e10340c42007001e004070340303021a40b003a1001e1080141c00d0f078002c210402410100c20301540b000d15130007281c480801c4405940c1810781085071070140c84120541c20050705804c5520301e58003803c450507890100b0444404c0e0a12101542030643c180355403100d4492800c56000340150300701c88080011101030040400c02000c1408210000c1541c9260460107001500541c521038040c4440005035a4011801240700f150300034041c4c00110343c6a039084d1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 764537239 1250 764535989 764536007
    0x110f0d0e12070605100e07020303011503090c090b0a050108060607030309080d060e070807020a172113060f0c210b041805010c020d02031c0207020303070326010602030307 75
    0x40e9072041501e14031000c001d110041c0072581c051000410146448004803503403403215844071556003110020002c03a181e020003501d066510140440002c003001520450240461440c0a0301d905a81100090075100c0c80d4010a050b00003510010b41003640e8a0042d622184111449030f0011000c000c0f0100203032103070340688003552040550b1030404010080306421564590046d481e2100c2100a000722140c1010001ea44041c00744000e100c068541e43d9103e582416410300c0e40000700c0045a00b0505650407802418205c0240c1011020780c5000300e03400c0000d5507204400d541c01031030804402120009800b401a003224542c8800054002500c400c0b5108000010b0304440650740e001350160550f22409090001018105601c2220300b145c1002030031141505500b50941d4040c0300c90b400403c4d00441034440c2980d82e02c800808685072004800041c4c45021030003907050100040e440c0400d50018034054605001592040c0440c01c0100722002c94542070007510701607402030000074940c2e44109088 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 764538489 1250 764537239 764537261
    0xf0304060e03070b040905013221150610050c0a110d14060a0b040c090b0a09240e09010308040915091b08100609030206070606150207050103110f0d 65
    0x1034a066a41e13801c0d4003000d400680080100903119401000020402d14000d03d00030403068200000108004c202d510602c9030201c0f5070f0052207042c01c0d0b0305c01802c0030135844890040c0305082da102210050b2504282c04000c65900b881400881e0241020710f1289080d0741c1c05600880007419400030030748413102ca00c1c8210480c940c0c0412000d002800140500d001c0822030880ba0b030082800f070402c5a94401903400c9058030030b0240307280c500305d003409551004464007100c004a0f071040c0d4880307800104591042250300020f83c01a86017181c2c501524440940469403d00d65807480d103840810310401542040c03c0c44082e240e1a402e03c410321009055501c421a20342c10440d01520290b55807072501c003900c8100140300a40b40c2c40c10300030050340c1e8001d100e10f54020b2010100c803c0c07007420100b010380400003602010340207000c0482c17071178100b11283d03116070301500c01c44881038a440c00780380c0020741d00c0645005485c0024140720743c041102a11034240d849040048101c28100306050350b844008010300041 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 764539739 1250 764538489 764538493
    0x1e020102120c07030f0503041a1206040f0b040212160302040305030406030b03010603060e0d030e190b1005150a022e0207050114151203090d1e05100c0305090f0304060e03 75
    0x2002002400c200610345c4003500c9000034540361885c1c544071080001010b1000c4c04120300c10031644025003483d20710913074007902c103e40c00a650481012120010400c2d4409540c000788002101d014420411707101c3c5208140e03240c80340c1000001e48100300d0a0707002d517100080c041d5000340310030300c0402d001c1d810a000d500409000004c4541d902d84601090301d10000580354075812030b031091074032564140290081c5208040003032461400581941840c0000b1800103080d40310b080005c03c00c91804045054000e1400405540007400000039083c029404105130b48054480c0c2c40c510706010100540741c0d44505982020300d410f031550341214102951090504941c15581d6917610705002800454a50149030200c0c240184070030610b0911079241c10024480c02141c1c002d2008160507031340c4d40c040c44d03003050b800450102450b46540d10190124409500104540036810103080360315245e0703000c01d262208942d03050001e030b1280b41c07030320707071201021003c0d0001500704000c10b12010380503424840f80c031200501 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 764540989 1250 764539739 764539753
    0x8072604060519020a0c090c030204030b18061003110108060118060201051f03081608120403120f054f0501050c0a170a0e191e020102120c 61
    0x41006040d5029030040400b00300c0c086014010501c400f00720101d4440540001e14900d0810789441d241d2492501c1380406094441000c614000d2003038054500640d841413007a84981070a01a201282e0003164250910f40704c1d8000041e91300450030f5801084035000303105690040d88000045402c3d80e8018802c40c1441030628080840e0418090302d940200542d0380000303001c0c08c0c041ca1840000300055440e000d0b40031300b501e0500200c0c130107008860041c1c2c242c1d0140301c41c1082511b0700184c14040c00e10368104001242003000300381a084413a145002215050410000090f44c44c80821104165440a0130b10740e180c0104500040340c450609610244040400624490718021b03414246a00c410940d154070082c040420030609028907034001220b04901c0d414201d601000900c041c03020510325541138450781c0494403004096000c0203070601c3d02c07030a031500042d210102c2c81602041420407901e50843c4900144000c980070050760140e68140e02503c0701c603129042048041d0404e682204850003546 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 764542239 1250 764540989 764541053
    0x406080615030406020f1911121e03040f02030304120209060402041401120b030a1b0e07080a0b2d09090106060f0c1e120206060604060f0c2609040b0d0807 68
    0x407101c803400d1f131469aa8000038181003101c00d050048080c25100c11a105010110042404000641c5040082c00c80c2545a541700d04100d50b0403001c1050180d00750000160120700c1014800a00c021180207982e1000303507480d494240300482c8624400c44030440060201654907611a004482d10862010408100c0304002c01c002814400325580454100c000c1200c0080c088810800400050041c000070300d560b441c0c507140c007030070000c40103240004803030f41c80c0309151180d980c2941d800395000710306810340c569000b113000e00801c21034050121440f070b200400002d14036410502440c0190391003540c464001070039000f8140d940407105a011034900001c1000f01c0b644d00820b8030010b408501034000380c080a220198007074100751000e080d036401040e0421050001c282c20103100c4000001e645441800050780303052840ca46104c000d103402c03641c0700c8584d04500c5840302d80c0180002140071070b010050342c0070802c200203040b108060000c01d909001c1c850f079004103c01441d07403995980d240b4814070101d4802c0f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 764543489 1250 764542239 764542267
    0x10b09040b1504050118030317040c15050301031406043201020d0c080112110d03050d060b0c01060603020306090a1509020a05130b120a111e0406080615030406020f 72
    0x940ca2540030b0800104080215692244401c0d800038040c0307011805450850300c1c002d10501c4414078035aa22202d0501180c200084d01100d100185002e1003d24612925a000200183d20a02c81072b200120f5101034a50141d03804502c45005690210900c07204805484040d035403000c45040c1040500b10030703030303048a9100e006e00007800d0742c803001c080c00502c400b0080000f81010f44181c2098400008180740040028250040c0307540a03081250070341e103260113514045030746100c0c00c0b42140e081c83c01d000f0300180c001072100180c0880006c0c0743c024400140c0b10201101240400c4070183d900608860210340000e89030341c00015115000764031403001c1038072491400141e83c0302c90b20b0781c0000b440002c0d241c80050901070501014080e00d0796803901d0481c0c014200c2600407400f03070807900c0e82940c411344a1410300011040b12188051101044000400500701c1c0744280c21920440011942ea2800203100307103080f134044000c90603038041039030668880d030f281c141c0290002824405403a0003002804420059 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 764544739 1250 764543489 764543509
    0x1a10110106090c031b0807030f090f03020c01021e0c0f0105070c0608011809021f02011503030c061d1905030405090a050702011d0312040507030c0b0307030b03070b03010b09040b 78
    0x10442d000c98140c0090030010201c481445143c07039202e48410208200ca9441a04950001c0761417402203800591510382c2801490800c00c01801c03030309056a544c4c2003507000314010075400000d03001d50f40e030440c148070400c0755083e9039590550540c2000015141501d00150160445101894154107009080c0d0340c0c2c0c5503650442c4c003e10041005840104244201c401e0200403a191084044c00061101e60101ba5110340e80c00010b0308456002c0b8410b1041ca1003580081d418412000212082365030b642009030003007400150030780f0018100b051001c50a0b041507240d007140c1c2c01071802803511020301084001d80c001c0601003110580003c01001803035a82d410bc80f45d00445c580c1e040010541001c0b41c0203800c42e11304203400b281122880510510001000c4161100c07030220312482c0302c040d5641d252403405d00715140c100400a0380c10403800302e40e00305540040c42c41100f403600c007007003490342c103004140d030360b00591041d4041d002040005012564a240150800e2840540042100c8030210700082514003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 764545989 1250 764544739 764544749
    0x30c070501020f07110613170109050601140315150112020903010213080c010804030516060209060d1d060907180b040e0606011b0804060f0212180a05041a10110106 72
    0x10003c140714052065005d0140c0d0840310441d800c62800c0c1d00206054180f401034030803181852203040703801c0503000b002c2d0090400c00340d01c202a1402c641e11440c80e9041440e500c42014040d100d503000345603030484404c134404c0c0560402c440409650440c2c9004482c52141c40c3d060100041c0c0901020700d0ba620b007400640702c1e1110781c01e840e400540c1002005440d003400714543c0f1b410400d0400500008c80c1d00301048411903401e4940c11640c00700c0d00c0c1003200181c41003898054100e0400980c1d8811318045500229900d03502143d4050305003007918846039900c00644010305143c120794010401c02c405011007a442030060100400c0f4103525200050881d0504d0416440c0780d00a54100805503030321141d2140c1c0d20003041100440e650f13242c0c442c1e124500a5004840503c0301c2e4209154190b4002c0018211080e4800c0420340d07984407001e00c4a51004407102c499005565416000c903180c41c2074000c141c0144010300018a4041808080102d1f240c01c0c000440140482c0b0f4000703542214080c014200549 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 764547239 1250 764545989 764546017
    0x3050f0a021005161e080706060504061d0c0a03060e0f1f080a0b07020c060d020405010e040c050d0923070f1203020703031d1f08100515030c07050102 66
    0x58400c1c01405148102c0a000c401044000c00244c11a015414001a08507401c154405907034110200b004034942034418016003048001305094040001541003401500d4046c0ca050191a03078882c80e00100341c0c1a0000141c120b6054000660010304803005462480740714580454450b07036030000318584c404140e4048000b100420200804003104491044204c00507034616014145460603030781c0c651030040d41c010610414800440c201034401c00156104942c0105038640c2c401c07c0402c4d0380029401840f07458007041d00e030001c01d182c0d86000d10443e03640f0300700c0f900e400703140048408102d4000d1031003000807101008100c00242007522158608030040102c40002d00040d800c10b07600c0e14000b02d1720b03402083c0c2208508500d00c00a070f40440e03040116a49402d03c0311010714101401094510782208854004491200304004010100c0310101c1840c0551100031454480c001d0b10b072001e85213801116042001e4062400d107201c030b6840155440800c90403840e0034200e107951030031b0030790b80951071980c500 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 764548489 1250 764547239 764547253
    0x10b100c0606050a0b040501050c0715090905090102030126101e110a051c0204030f0b15010806091b130306150608010807050d030e09090d030f020903070b1303050f 72
    0x4081c414003002d001c0496088800a1038070100174858030641c001c6504111000c103654003110000c1082c0300180c81e9145c0d04403a01100050000c1400e0100d2041255443c18000815444c550602c01c42e41680c000c82080284260907150ba054100183e032804c5000344291801500b03a20000e109909003207244500a01480c2e203422034401c00e548045442c009180400c00c40b001e1348540003002c90326600c0e181c0c40407841c64010700c1a40d030000e006590014101c140da05121700100810310500741d129003d41c84001d070b0000c00005c0111400c44086403440d40107944000801c0081c0c04420150b1001d201a4075410f11b0300c004080c001207030b24030540c01203c0454654100640c20380c480d00701807001d00500d10700381c0200c4d0700d4408101d648074800c0c4243d90140d50802d09180078140b00e91303c00c40b070340c840180c0816201d00300214003941c0c603490030560100091a101c01c4030f03140c140e14001c480014900800600400d8100b4030740b40d8803a17000030b00400344001c401c0e01c0000015800d014211185c0d0448000d80361b0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 764549739 1250 764548489 764548493
    0x1104091e1e0e061e1803070c0e0a0507390c090606020d12110702040507091a0a120c03061505030601200d0804080d02040e0907290903010b100c 63
    0xb80c2d0000054100180c2010007007240306070003070101d522443c1c003031982c810207500c407501a036841d0f881d102c8806659000005030350051000511001c01180c80c2d03a40c40704c4c0d8030341d1200c290300211a0152180030004818000d0030500d00c8a40c0e09400c210810707660411841c5071401c050058803000318208071005030760110f082081c00705620030340004103990f001030803094444c80001031406506420208a040c0d8171100701c501700c0030010a49040c40d9000e0010006420161009002140d0a104070540c09400403041400c15503200f040d101d05401c02c4c0c030b4100e01c045c15145080090070054040f0303000c1503540c103030002d404074604038141103000050719103035a81e0408000052030b0350100c1d0050340c0b103555100c5e41a501504002010030030400c41c0c1c50402215141d9182c120001d01c40c0b5011107180c02e0000c18085401914001c5103801030402004561105079203554031406690b18a00c1d8904007008501042a025200002007101310801000019490107d0002074a0392040881c0c1100013001c03102c41d401 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 764550989 1250 764549739 764549741
    0x3020c090c0403213c050f071112010603031d0a0b0f070515011d09010504051906090b0c0d0e01050f1602010609060806070f031104091e1e 61
    0x307007089029804515041c2075482d0880203642000e0368150446000c000003008512900301340714a251188180d56141124240341095500076081515104418a0741d00301c038940100304aa001c40030f0f900181d42040c0d42c42c0c4544030300c1400d07118607035007150611841d03440d280720030701c2000c01540c8a9100c12003d50030300a100c0c07001e000f1043e00305000d448041814000e240d604800d980249542c4d04c5035039500c4045241c03071418102030380720107004030403d100003048401c00a00f9551582c207000810303900e580d80c1d04246500f680c6d4240c6010705150005d0904140c401202c60300c0d01c914a029a9020880c00180ea44116400d94200d40c10041c2c0080420820307000041401010790410300c3c3c00c02407055040000005440e01d10107000201c05010580c43c1c86002c0707000307411020003001610801c001860751240415112a4115a5480001c0003007424424241c0603105030010b030720300c08486609090514144d1002014007181c9403c10013484640048549003e01030a402c1c41d034040c130018a10074401003140 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 764552239 1250 764550989 764550991
    0x1a09100c0e0603280c0e0414040f14060f01090c0c020f04020d0f020d020c0d022e06080d03060f09090b0402280803091912060e1903020c09 61
    0x9980e052104650503164441d03102100698122810360740ca07119035803003004000d000940c02d0a00b41e040c240b80c6a070440b20707901c01c03001c0c0c8006031140b4041900000800040b20070300c0640c07030001d9148170040340108048004513103d0340e02c1042084003042c4294002898202c1c1290402c08900c51000140154005400382c08440d01003414208072420a0364000782044040099080c040c940c0418030100c00011504200303000542c6d42802c42d038540140b0001000b81d84920420b41c018420710308540709803807000901520501e00750038695100d44041c0140f20ba1805807401c42c208950711b940e4045020030041c80198240e500944001490504c2c0c107010001c1c100466005800c01458500402c01080340c0301401c5900c183c0c121f075580381c10138000c0118080688800058401c00344100d50109490030000000c0c461240200c80098a040601c0141801400e550107071800e0213504030300050008880380c000f250300f0208a410f0750044982902d081c0c00c10b8030403032001e50040e0300510114115040a00d00a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 764553489 1250 764552239 764552263
    0x170106080c06070201021f20070b010e01030807030c150501061d091e04170a211e1805010c1709010605151809100302040c021b0f010c1a09 61
    0x2c07820a003003900040d45800380b071140b600e0107a400e440f10b8030004546d688508a0000c0d040c030001b042c000404443d1456070084601224a020070b88004590200c11101940c100d95002d04490f141c4042903a080b910f00a00f2071080b11681c60762407040214001d1070050303074040e003e0b503540e41c00c0d0301c2d18a075011007118032079182c154090403405090080345040e030400c007100003088800580040d01d075480c011035644030819210301d502e900895100700315a1b00400003100d2000071203a2116451444042008403801200b0040311030300008108034800380700b40c01401070b094103021840504229900d800b400e42e1005540c0e5000200b12a20768859100400146504a94418000c0111700d0900c2c1c04541180400c0452031040b020104071190304d142c41c544c0703455102c04041c1030314455040000130000c2c080d8040c003089105504020415905a200040002244174103482400d4030150b00380c1072011403454540511304001b0100c3c4000040b507000303d844001d8500c5100d4151452910458150a05005000c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 764554739 1250 764553489 764553499
    0x80304021f080114120a0302010509160b2a0a0b091e0c0906060409020d020306010f08060907110c04111b212a0a030306060216090207030306170106080c 67
    0x2a40c04841c1d03102c00207905440b61502d0605460409000040e903200c2a121070550074403801030341804050781074003c18000c041c41c0003103480304004410120006001030040d000d0140c1d09101048115048041c10300d583c4141141d9009e0802c1161001424a260100d00340d52411610050008210080100c0d000300c640030080d00b1001c040200c039035a16090401034051003100c8000c04940c1c582c0d606000c80f8000d2120110441d9100001c03410b00b0041e41084032000c1c0850b200440111125010740d0070a4400d22000300102041c0e521301d8000c0e0380e092114880fa100b2481219401a2103403540c3c41070324044080181c88c1034845000341011000000c2c00208003806422030042c001f814442e0452107406001025100340c0c0720142e0300303514410840780d4080d14200d80c8145030001b170400000325059a0441c040d64050200d1a100c5005a99503000c0d80548082a042c614003044181c5940d8040c09000c1c1c400d00e0003198903581e82d40144000e40c9650078945660359100d00410000c40c2c10000f4231550381c02919 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 764555989 1250 764554739 764554789
    0x501140f030703020405070215010e010807051027080f0109020f18040f0f060c2318011107120b010e070f050904020903070b0406051b012016080708030402 68
    0xc0842c0d2220320781e10000340a01e84510205904500a00c29415509001c4601d0251036940310440034280340288038802c00e50140c0d65012550b410030181864074046c69494001908184988a46100107031050086600070450300104500b0300920200400f1a0480000b1510040720b00401400c801d941d40114803807009200c0d014800702804e407080754030a41100030700711002c0060400c41941c009000300103200c50f00d001c1c4007031074541d0072850303074609440f899001d0192003a01010b181c5c101d10a5000401078000d001440c01600e41c13207000d50300c0c01020701e5400c0c0e0b040c41d035655011a841c000034803822503d4070302c8c04006021291114510f030768013080514201c065075450480151452090a400030b002d5030300000c0c2d054a41c1c8041203810000c10703014124a80d269a1001c000340705803c100c0d001c258215200c403104142074814015051035401c01648641600c1b17800c0281d0015512081202c40d011031805c2c0d0001c0800d000b24007400c0054019070056a41c1d00d050701c100944400340400304aa40c2044071 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 764557239 1250 764555989 764556019
    0xc15060409020f1512010f090b01090e1605070b070206041b0b0301060c050c120d02012a08100e011503060902030403090b1b1204032d08090109080f01050114 69
    0x808200302d4540d055034090b04c00e90a08000e07507558410080710341c01782c05032540001100b84400c5002001c0314020303841040000802c600440300e1450138031400301008a4440401c00507521030781501e29540c802c0c10020b00d007642591740c155415004480b404050307000203040106015030754120202003468050038100c01c9041490581c064003041c00b1702070030072002014070000c00200f000301e141014002001450030510500045030790b5032000505400550030000740585445458443c3e40b100c100000095002c071900620899118000414003009a02440c80020f0f4043c0c182c40100c0c00780500038121400f00b0881c0102500741c8640f58031107001148100304100209510034010015900c5880350f01d07688094440b101904644e2214441d51b4a0044c02c8452241e800c0da00d004000303c03032003001d58201400d000c042449000b42c0d6082d0744054800c0405a030310000320310703400810303811a050519656450b101e4001c01d10b0311400348140b1031242c0d9500d00501c0450076401d92247c1a440465400c0d500903600 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 764558489 1250 764557239 764557249
    0x1603051908040603020f0c0109060605130c090902070c170d0212030601050a0e03010b0324060f0117040201031409030304050c040204050612041a0412140a05220b0c1506040902 77
    0x5407050f00e080540c04108421b0140c070140882d081407114400902c5140b1140c10b1150050003d8441c180c4190070070540c0307404001c2c0b140130344100c104240d12425a80c82c94000c080c000303580140811100045030460200350310007903a00010501494800030706080e8030300040a8900100780802c40b001201c1030007089520780e4880101c4440c80007e140911610802c40c0110f400b6005c0d503196582d05003c1c0c4080b083c1c4800c3c507000c060040c081450507480b81901c1e43d8062000100c228006680050707a038580b5440904104070840d9003062041c580041c0480850711124032020b421307a0b041c8220f8100000703000500000300010b21407003100316011440c0a1802c0c001541a1081608440031480b0000000c1c040c800c6c08410b0742c1c0da070150444001c4182c607052505c076808566004027003011900c24540c98000941650a030360304ac1d1059290607150642d2603402a000c03129414480b04c100c00c0c05e050210b100f040100150044c1c0041400604a081e00c100d50000c0d1080e0003040f0900440c0350850131000340e41c82d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 764559739 1250 764558489 764558497
    0x70c0e070e0d14120a020102180603010501020a0b09120a050c10060e011502010f0c021612030905042c100c17070806030a06240b1201060503060102030c1603051908 72
    0x102060241c5040030600b503c82c201164490300b000404004944106940e07010b4001340050114400c0c003400c1401140100100d90100f8010300c1c0c0140e010341c0c51600003c240c080b080e41c111304040100c43e903c0c1c078000760100140d44907520300c030001140811401ea084100300504075008503510b00038400203040030180010344030140f258002080c50a400365107018004e6100c030042e10340d030310400e001c80b8030943c1c4040d5a41b48010035846851000d44030002e41851075000304048503525642c1e50030442c0c904002c0102801c003694030a500d04150510055041c0d5840a8117a5100300c0348001d84a0701e0040c4a2913811200e48099150a004070400d801c0100840c43c4140c550226542c2010005a01c464000c2450b000800b000204504e140c01c08030104000411020500440003200081c0b000742c0b60380d4808001c0c022940010100541c90005018544c000c00155038444411b1046038241224144602e01c0c0440350514003000442050040c82030100a21003640003102d900307500d014005060755100c5413071007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 764560989 1250 764559739 764559743
    0x1c0e09130b0a0204030b0c0405090708010e040201050d02090402130f08010e0a1514070327120f0e0402130801050a110a030b1c0506180c10030506040209030102070c0e070e0d 76
    0x407440c0000341425802d6810344000e103803c2907441c0124940b041000b001075005001c0d2510448685000500c403620440e8940c5c1a90740240001c0c1894445900540c1c66030490760300001441d0f02405100e11540b02c520181c41d880c0d00034414204068504100e0f021901119000040c0c5d0b40d05110250b03c0c998030006641c111030b03901452341c41d071400c9103490410003004030090f4810103280d07330014058000e6268005114202c600e8406a80084685001501442421200924807022429042d810a00401180d0365030001c40c00c1085d040402ca200180407030b4450841210500301c80441800050f000344a099403002080c1020400d1301c1c00034401c0c0610b80070f44803000040585902c4000305030784031004110441c1c1403405048840884501c1c0c683c0d1151000c5412020b1881c803580c03601d0801000080550382540042c4c014800074100d5201140a0711b00100b0251b0000d80030881d0130b0f180e803400d2005100d00c0f80640540c003e01401e0680d4410140b030050b001c001001080c08102d03c555680005a2000d19 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 764562239 1250 764560989 764561003
    0x5120f13081207300c0b071d04020a02010b120102042c011a0702090a1d070f17010b1002030a0807080105090c0d09020d0c08070b0c030415111c0e0913 66
    0x200ca9041415034080c41095481c1101314142a407505130081c1001100c80d01c00c404040d0300795660b03007007155180b04203400e003001030b0703900c00702d440c800d00b880d50041c102d458551002180c920302c0c01c0045a4401c3c2c10310040d1040d80e500080030807040707081d1b00075221030003825540d07070510680d05100003603802018050032000c0c0a4229003640c90403c102c00b140e000f50b0780901045401c0c0b40c02140b0600a21301c812134808542e80e50302801c5031808001c5445003d40340300e1081440d810313041c4030f5040304603403101c1410901c665035a10301c03419507503801002042c0c015096009581d164040400107015044c00340001c000c2c020340d44018001f03a513030134804681c0103051444660306c0f0441d21030b4a002400340050003071340040907824a041480756048012060311181400c403601c1c0c954420302c03c5128803e5a40e2420590020310061003041c6850004a80c00042071a00780c94558044614a041c401c9035500102c84c043e40820710500950861030401160204865400f154580707646807680149032414014110 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 764563489 1250 764562239 764562263
    0xa0c0504110c1225030c1109060d030f11060414010c1b02060904022811151314070e0114060a080a0c120f0501030b150102120705120f13081207 63
    0x401c4542e80012a44041440b0044070495410041c1c920318881e802580c44080c510941f080e98180a10f081c2d0003910050819295440d0584049807038079099502041041141600c010071600200180c5000d203004a0140c00b203120f2410b652400c40d40141c03148002c3c49a040720101c9400b40d81407014000940643c0c41684d00c101102c0080d0007171040e910111404c0021520382002100f903a81082c145048c6c6845005000c03103140d4189940350300d0140c0038440001014005003000302c248241c00c1182d4401c1403110100c92108407020305003040703904401c40303410342c040040124040703072443c0740c800100544045c1d2501205800003040c00100a1000c0e4142d601c851b00d0321401031142803107610508040d9400c02420380c3c010007201c040e1800703100554580304076002003110052405d003d001030b5041600102034820092000840b29080b0350400d880900074000c3c16099200303010000d1040d007660f503100c4c0d1f42d030b0980414004258012500f014400d5400041e40c01050384250088640041d0021031404c80d1b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 764564739 1250 764563489 764563507
    0x81c1e140a091104181a062b0f050d0810030b04081305030d09080105180a150f051509100b0d020f0c010c0306170f0706030c0c050a0c0504110c12 64
    0x110403941150f107410a00e040c00000c070200724002c900ca09244640155804c21080074403201819500380d0341d0f0b03540301c041c020385c1008030013501001d8030040295461550b5003007182d4072000c47c03011151509079003a40090001120082e030126503503502c0b910030a0aa6102e60071920349440703440b4010402083e00200007003045848401226210083c1710083c04c03580c8002c1500300080c1281c1c02c40c45405019820000442c045004003030b40d011101c000707000141000c584640350301c0c1d4824400d403102c0d40c0d0b10382d071442c5000400d03140e80030300c51241d100b9111070200401554144000303c40000d0109030b91900e10300c004d03c02407000e00c00701c84101d2442c40005d6200d9000070b416a0300c620070300b80700c005690310b003421004080307826802420896140c01d03803141c00302c00780b40c0840707032181445503400c545d81d00524014400c0078041d50140481c803543e46811014110341d9a1824549106008156031410100e0f00c104402d00d098021400342401c15440c250800e5a0107030204d076100e501070981034802c00081040e5403 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 764565989 1250 764564739 764564753
    0x1206180b0103050d110111120c130b0a0908060f060f0102030408161505040602150a060e072a051f091502190809060f04081c1e140a09 59
    0x146540210a880840d65649801595500701c00c0c0c0c00d0021503c1c0b5039804000d804188146007411010719400fa24000c030503103600164550003088120b04480c00d00c40c0b00140c1030140c146034042d1105c07441c0180d0b62462100c0c0541003181d5a4040301441d40002d080040f6002100d0060f41c0140c8280c031104c1c000302034140140e045000b181c20208551041690b0070784900003038270640007100e170000c0150f900c070068510110342d203204030b00034480540e120143e140e00070640031001580c80300840c1000175070302c1c0e20b80320401035004080d00c2d4080010380322500c1c0500322001c41f1030b16051100300c901020b804203641c0d0b951a150040d4056960b401e62000c011078411100a80102c10f45551001440d14159000f962031002034101c002d6415030021b083d0000c070369a0f0300486c50207028902000c02410300b039032514503002441c03200604c100c80b032500c24015a15a212480b551f40203000481c0390219503030611203d0580607035038040d203007441c00d820521036221020911096980001c0305040100e42101c8074203000b4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 764567239 1250 764565989 764566031
    0x705090601211d060a0501080604051e07091a031e0a03080901140709060f0924020f01060b04050411030c0715150f180519150e0a0b030d02071206 64
    0x20307810b52035454032000703c102191051041c0b0400c103040200c2c0e40c03950001642e03000c084800600c5a40900245031a080180341c110744111413060440340103030786600c03503070064407821032800e0303c690500c00c107860030b514042c44101100100c04251100c121010f292032030742c0301c00c800030180030b0000d071001190004c9801e4202c86e500b4800d042c113074170490800d00c0005140300713074074440c080c006101240501aa42e1050190030f040382c900c8003c2c0e00481130b0148420361400d503120756510a51041440300c84200c8020700800b4020801a001d064482d46000305110035101c0088040803142e60070010024a030703200f1001d545040d600510f080044400e036100b40c02c0103180914480a0005540000003806002c1d16000c40c02c1d80c1d410036913610880d08500b110001c0c1c41d0159240d00c01c082460007403404005284d4099400c8110014002070602d176114102c03100c562083d59810314003a00c48031410418102080044480c00407880100212454500b485402c5580d0740c40042c0f8084d118a42e07940d4401c3c5002d500 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 764568345 1106 764567239 764567261
    0x1b160b0a090e130611180d0203030d02030613090b070f030c020a030f140c030a0e030708150a0609020c0a060b181f0b030403020106050102070509060121 67
    0x4507030400c038000c0c45a62042d0f031206040300490b04900411210f4121a2001c03681c41a004102c03030412804124401d0140c00c51070743c26401030301c0000c110f4405442c890320060326610303034038001096250020b5000003074508245041d014030045044248c00b81d4019114443d41500d13208080d825905040007400250700109001e038080785c0030711500042c01c02c481c81d0108800d03400c1700d1035500c0c90b00302d2000b4650301e03800400d4000001d60054070303030341d175985003100140030300c61401615036902c035800c0c41d90070104240000814607851441d004000079200ca40d10035901c4400e180410303175a402c0c20030810b981c5c0724140300d01c07045241070000010542c20003000c0008196980c440c141070743c5e42140b600c5180780d00310920340041c0c0140807030080c41c000c610941c008982140b5182c002490324856800c020b10030341d25601400020307038200009120105028090b00180300c5090b900c0002005041c40f1 = true := by decide +kernel

theorem cover : BRFrame.Cov 764388489 764568345 := by
  have h0 := BRFrame.cov_init 764388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 764388489 ≤ n) (h2 : n < 764568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
