-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3486
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:48:24.831988+00:00
-- url     : https://prove2.me/submissions/b1bf97de-99ef-4109-a210-ecb6aec81310

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 626798561 ≤ n < 626978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 626799811 1250 626798561 626798587
    0x2030c1b040f0204050d020d020a090608070303120b01020d03020a091e0e1e0604093801050105040f0e06040b180f0c0a0e010c030e13020c060a0c12050a06170102 71
    0x3266901c0b885105000400482d02d48180320302c0841e6040b035401c400b101030343c07000540080303094022101c0d091078070401080c11400002e070705050720b0103034560411202041d522038003a940d8101c3d200f40142c000002c01780c1c4c403034001e030007070680c540721410700342d01e025214035200400701d01d00058029400381494080002000c003100160b00301428110700c40c0c1140c000c04e41640440c1014084a000d10b50358800302c01031000303401000e903c446a50b8110040200456000c1c07041d0405150911802e10902000041c29070055084408451649412680d900d24100404002942c020040c0760803035200c060314a2545d40e005600d4928910580741d500341401d210341c0d0036940d4500148110354805c8200320000c8400c4d00002d50400002c000d1070030341c001f0141c40c6800c80313140480c2e40d041c9401c2101140b003180540d055030042c1601010740300c1100c81e565140400c2d039081d00d20004000c00400c001180e8082110459000070354840c50748203022810b1603840700301100307612050005d642d40e0b0b5408104581c0d0028 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 626801061 1250 626799811 626799821
    0x30f020106170a060c090602190204021315032a0503100504150305060105090c0403060504020a08010c0e040b0f090f07110312010914150103091103070914160f050a02030c1b04 77
    0xd5030380b1b0f255400504010002c0c0d600c8000c44038070b03244a00c01d4140351045640d280c0440340040d110000000f91582c0c1c3d8040030362a118400920000301c2d0a0030801a403040c0c0c2040307a030f00c01200807000440b0842d00d01030282c9141d0b10140003a1a03040c0001404941b540751130240c20041e480340840710b80c0b15861800c16500b0114180c001c24420403c11043c0309a058400b41a1015a60001c000050a448601c0002d81c1c8940951190140c0c0d400e00341c0c2c501020380c100038080b40b41031090340d090140b2041d803010841901e2070700c000598440386117004540c1c030400d00c4081581c840c42d9400c0001e031082200c61290f1035500580718001081143e60010f1210440758010004440804500d205c02e1341440038141c10803090b401c01c0641016074814910083c01501c02d03c221140030054141c400c0c050711280c00d00060000c24080030351001007070000c101c130f00100c8542002070009560b03444030381c05150a4102c0b51a4007015003003003148824002d9071201001409010060480f95a01455000c0000c3c10f10068407 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 626802311 1250 626801061 626801081
    0xc090a0b090102280506010303050d0b0102010506061210081237080a06030606121101110a11010507120206090601090608031c09080d0903170112030f020106170a06 72
    0x400d028955990b40c00113200764074809101c0003240b020b01141109018a00c0e81c40014040b0b201c1d1400010926070884014120160002014030400036940016070a8032025203041d038008000700715a124403c00720303041517000b1340d2075000c1d041000c0e950030070f035441d08c0307100d588003000100f00203060306512054051a1170a84a0128404900c0c001c00005a002c18007158804c0c003482200e10004001d4940e561007400510707170080301045007a44a0341e40c0c0b054008500021500c18003800070000e01580180210a40700c00c0e05e5004144c40085603481d080c81c000a4107101c1c1c10b0241c00d005170000070303015605949161505500510a84c0b07010540340303152180c10382c014030300d4628003101885260404022144811004940c140f808140b10b60f03080004c1c8190903020b0160300022850211040880d0043c01d02e45004e50344100324007600044404010790284205810000a1415040000d02400528020707040500002403140c1d070b00d006601758400c800100c5035160700100c8c1d441080002a1060380521 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 626803561 1250 626802311 626802329
    0x6151903020a0e0d1203331d0f15130504080705060105060a090e0c040f060804110118290406030b0a0b03040b071b020d060209120109020307060f1101050c090a 70
    0x400a20749803440c17017007000410141011f48031482000210441040e0502c1800d640c0c4055007000d513a82c00c1c3d0700d0110143d000d80f42c030301c62151001541103130780b2078031035801921032000c13000503911503070160003400b03042039101504042c10f80550000c0c6403107481081e11440c01658215540d14040c5407403820080141c0101d0310992041c4401440154001e03403400c01e440d41d03003001680c2510749541600050081e64040070088a088601048165102141e54001c40c419240200c0d5400303041e005540410f0002d90240408045000070450151502c0291000c002030840040d8150810400282654020740102000c01e440d0343c10b0040390700302100d0100081401560300c0b0b0450074580d40b28444036902400c60304c10824000c000141030781c1641c8000c03c64940c020005c20720181c0340e00e4554007075000b003080c80c0d1040030f29901410243c05c041c00b6000d0750740e900401034144203090000070b441c1111300301101d604008110030194442c00c800d11502e801900d03075040c03d40c0c44414090400480c040c40b60032200803 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 626804811 1250 626803561 626803579
    0x5011401260c0d120f0302030615090d0c270b0901052107091a0d030e190f030602030109050702030c060f06060c030313150c0806151903020a0e 63
    0x401081e4000da00802501101002a24034407440010701c2e103041040c1242d800001070031040100105400709080c0b805054075004c062510040c1e068040f4001210441d40050450400000b03100c803104c010180e59800504210381c0003003e480c3c03d01140c40d00c0d004051859403000c80300d9450184204d007050aa0110307542030040007040f9003c42d002c0241803081a001d01091030520030068101100c40c4580d90300c0304200c07140d02c0d5480a280000d000c10030803900c050340c0c000614403800e08009032700c0d11314160140c541c0070482d0b90f03030801d20481c1c808030001100c008070300040c0410a22259801c140040d401208056200e5042c185400100d41d000707042802550f2040120300004900400d05551014407204c0c0341d001a529000460011310450040103840d01002041040c64031002890f03040007402a031107203107003440c04841d0384100e800f507420a00c0451601400515181740221b042c07a00c001800900500307000c0660880c12070070031640f0114000c2600410440d419660000740000103070000c0341c803240 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 626806061 1250 626804811 626804819
    0xb0a02010c030e21070203010b03030324010e06180f04020406020105041e0b1308190816080702120d06080715170f01090b0a080d02160e090706110c031905011401 71
    0x1070813540b61440c04400d4902240b81c000b9503800794094212802c0c06004c1e6956481d080c5044a40c1c5040141c5980b44001d40f030301c0e50002544203007014040c902000d48100d1800840c1203003c01c08006030440030b680194504191040c5443d940003610040c60180c00104081c00c00d0701d812034a91031f01408594441c0b003001a0180030903071030f05640d0380000c8010001e2200110030f041100c420722400d1a82c0070100740e80301402e40820782c40304603103104412000c0000e01803100b00c0021100c011040c3c0b40d100059000c2400c040400d8110b00040401c407940d40b200207001c0d603940c0da846003055090343c000042c04500513102d46d54507800c2211402c1c0955040003080c158541002d984215410601841c01c04c60340e608a500316903294981c4070405403501004980c80340042c040b0083d600c220b5900c1d8880e200065550003d501010040803c0c01030100d0005045c40c103082c040229007180d640800c041c1a841590f2000c030322031300c090010404d045c290441c202140e507000d003445401d42d1032041c0c0d01d94400c1d0392180100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 626807311 1250 626806061 626806093
    0xe0606060a080a06050406031a0610081503070f06051c02070b0714071a0105010f02010b090609090a0803010f0302011d0918011d01051e040c1203090b0a02010c030e 72
    0x91003041e0506054056480b07005112000b4412608059005450710038088244031001003903150645829100e0541a61307104140160305403c0e1035854045020b81c008103d030b80a600300d10001040002c0d0072512442da5510002a41550a40c0301c0f40c0480e80008054010071034171300041501e05d2500c8029807134003590742c1d610080c071440206002d0801034800030607400b111a4030300f2501600c4e00240b401032243c040d0071802c11080d00c203100302400b183d014104041c1e114018051201c122000900608581e6206c80900c0000c040040c0100c40364061905d2060020321414041c5019103000750030713481020b00b10b10002d01034400c80c0504443c1c1408c24141021295244a40b0681c4021110003041d00d0300c20408400d030150801a0000384104080a1354540202c015402988168082021100d40340f25001c42c45032a40ca06603000b07440811034140a1016241007451304101d03074800d10340580c501d580c4d08400c103030381d400c66104a00140d442d120b2582c64568103009000c440c400100281008030000c4c00b0790 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 626808561 1250 626807311 626807317
    0x60a0c02060c12150d080715051e0103060209041b090510030501180c0306050d030c021f1704050c0a0e07020f0102310e1801050f062209020604080304090e060606 71
    0x8100506088880c13004907480d1440c814001da1351040c0259140c0c0b80624003607001e500340116403c0701901e0280083d10f80402110020744206204002070f585034210b85407100031b944080c0403940c2150301c583c2c000e0a82449402122450180c9503a100301c0ca80c04c2008200030602007500700c0c1c1c200341c01d000c010711030310703000300c91480d008010080001140042c851050303024207030302e07809240d010407689007000074107422106140e0785034800c1b034401d50130080301c0e11070f05a8030340748140714000240d103110701005140c0142c400a80250140040364255030401f00041c4000159800ca0749e801600c01c424044801d40410000040d0030601c002035040c5640e2001e06007500d0340c800341c40c01d0001010003903603144c100078006000c05400c40c03032820b080324a400d0780d01c2e00d02d940440800b117034075600c4e010000d0651001500b2481c003408005004c0c03480c2c0c1d4520204a07144d92102c41d00094000ea030b8200050041c0e40710f40090008146c0140a0342d111490480280c04039102114504030b55003000c000c110680d601c038011 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 626809811 1250 626808561 626808571
    0xc060305071d01090504240b040b040b0304060f0207060207060b0d03020c13020f040602060915040c170c04060e07020d02060103020d231207060b01050909040809010c05060a0c02060c12 81
    0x500c0c14000112004030391040680e17100a400c030f450070400002c1c52482d1400c10701a500602d05000c2c4881e51000102182d1182c1c0c031074104202d8003488103000070b184410085800502881e00454145402c46181d401c9910400d0100e8065500150b86010010f0500954800e00c02c00ca410354910500d548000c0e48407001c802a452040c48140f07100100e66140d82d0580307140040c602040c589032516041c02030b540744000e81d280741844c441c5101c080034804560003054802c6a10210035201c2c0b510700008031100c3c00d4100e035051803d00450708880440d498621a100050280507030280040c1000c09005c0c1c10f1012424070072046400480050000d61a40c9015046c0709074010f1020b0f9400107444000c3e801e044590003002441d00482e2000a0180701c054041d0003102e010781002c03c070180b0b0850041d1140d1058020240d081140340300005c3c081031011001c1c05d6010418185501001e1490b03841c981030540445480041c2a516000054901e41c10030149601198041000b840c3c1401c00e02108080000104 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 626811061 1250 626809811 626809847
    0x15090a050405060121090c120c0e060105040504150f0b0703080c030402030a0c06090305011413030c0510090602031f0b0d05090111030c030708091606030b0324040c06030507 76
    0x20103e419039106600815118407070705a448480e4015101d240090070141000340c4012041250200314030750f010380c406d2522a88a174096174001d20b8505442d1009000801282c1400b0081c4030005032030301d881c003d02e1407486400704140c60003800e084412282c2c0a407a0001c0e210b4820621041c40042c0d0802411500725280450180d1079a84520000c0d1034a080001d0081c08480c0070000000d603907403c404c03520166840f600080c03007079103243d03075200c1c002200417903180c1d003070701c4003c005500402e01032108000303118015000e0b40c00d01810044a030f810780d0b6001d5812a0104c0c0d000041044800490000d51540d940c42c2c3ca159200c2c51504050007000d0003290402c0c040c041e078900c0407075547d103001d500010302d550342070030565200e10300410b034221140c00031180c0300e011485280000c1d220481c0480d0b0200003d105a039404e8000382170030070413001081a5a50300746c141c451f40c262400000000c60340c0c290071078a02c221921fa540341514010755020304d15801202890300349400d0001658120141c202c0d4080c0ba40 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 626812311 1250 626811061 626811071
    0x100b1806091908060a05100312110303070f23070b09100507111501051c051501150906020a020108011401031e020901020f0f152706010515090a0504 65
    0x200003404920558480d40d03402409000040b08031501480b41c40100c0c0d2001c0d040d10322a41c0e885030080281c81c011598070006883d0244140002040c1c441500312181c1680340442d102c146441a041c0703103034000d03108100401d920b4400d44e101554860300c5503000491014484500d203100c04400c3c007003405146401044100075038005152180c0410007031071520034030a007c0c80b0ad0b091085024020100300ca2203c0c0792401000304000100040510040c101e590181041840752807240d10408402001c0700f08441e07038000c045915101e601015065406004010b00e00c05141405910280074521503901c10300c207640204a01d10050b07a00406441d04444c0118140e620300041000101d0050403140c01c5100b01101014241d00404226070260403004800e0702261031202080d21040d07901c0102c1c0c10394480c11340c800403014070801c2007210455001040d2090101800f90800c00e80b485544028541038610740c44600100141e00d454030300c64401d59000d000307861524210300082000c1c1030560040318010342d152 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 626813561 1250 626812311 626812357
    0x3021c02012f0f0a03091104021303080a020703051c081008060c070618140c2b0c05090a02070512091c051908070b1503031b030d020309030d05100b 65
    0x503021610801901c0300d0151340d0f81003580e00030b002000024001c4e10806e41d4411101541d080034403c64654440d00550001d86615642e00c01c441c80d40041e18820031809102c10000004a0412200b02d001382c507820609104040e205008000050080079041e0100c0c00a000700300885000c5400341d00316041c48403056031500c0f81d003081400317040c0394040e607512012000101814040b0350a41c00f9800503150041c0e400c0d5181003030406c88042d08243c020b401418055a00f030808400380354001602504c100a29100544e03a100010022402210500540e940004030842003007000c0c410000c4800c20019070743e05100c0d000c8049040160380340240308007100202454010f0184c208040c9018200c64003075000b408002d0314006049822400c000c40d001401400814010114401c02c080c0e902c40c0640118181041000e05076a0b000c609801c100d0f042c00b007008843c0b0703248c08600085110f1004e49006543d258981c905141c110b42c8001c001c250351a0100000380f040002c41c008688540906100e000f5040504e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 626814811 1250 626813561 626813651
    0x312060f0e071107080c221803080604050103080715110c031b070e0c0307110a080a11060637080105070f0e0312032203021c0201 57
    0x1198200300038891050100140e080c00e6000018800c001503903072a0007000c480855980d4603005800784020300c1e0802080303000030342420074030034109070220200c0369000413011412204983d122158100580101400f000034582c01a550715008201036904211039859a101e085035401442401405616940c901c00311205107900142d00303071540d500346941d44441d080080350340c2e540800260407036213205070015801c1d000b0216038881151080300220000e640e42800d8400107600080c00c40007400050101c48850460030856140c071769100d4007416a0f100a058000340085012018010b4150b2000081200070b03182c81c440490000342041184035490250035400d50f09225518a1821441510074000f904441c150843d9005210035120a101440507050455096010310080c0d900340d40200050590708500b100210341c07041c541c0342c107070a03202c2013240d214941e070008501c103400580c0514440280d004003506480b4030903807580003c000401d00070b000f40d40c04041070b8400000c05010690a00e0460301 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 626816061 1250 626814811 626814821
    0x30403021506010339050c0601060c02152d16110319050604060509030f0412020402040b03130203010c02010c120c020703080c070f0b0a12110c12071104060609030312 73
    0x1181c103010307490a0b121010001c3c1d0f207290307140c0b10b0500c500c1700e0105048a006008913040f03640f0b07450240170140e00389901510324007001e4030102e810014520103039507928079020160002d8910084d0600e45035a00c81590800c2c41000390030014040c004200121004100081c04036180b0350040c04c5a19100b59000024203103440c880102c0101d4502890348001c210703000c83d5041c80b03544219070402c13a949980d83d440b59223002d60084043d04140401050061040705c045244895100070710140c6010b4845246010541058400004d05d94101c0807007802c5180038000c81040d110b661000300305640b10303030b2002070410030800300303003142c25075210711003005144244400d001458110b2002c940d0b443c0c46032401e03661241c6520421080c1c2070f140c4000b25403d5005000ca800440ca40d540f02c1c4e40007252000d0207002850416400040c0041c00c1040c8013000d034052005a6210441ca104a5200d00b01410050b070b1499480d081e09110b2031425005201c40390700454180c05590309813802e540f03410810114200201 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 626817311 1250 626816061 626816081
    0x3030b040e0a03210b0303071401021603170609100b0c01020909072007060804080a030f0e030c0601170a120c08280f0801091a0409050607090b0304030215060103 71
    0x20142ea0660403d0541100b0350902c00311200040c0780011121a40e040200d56120849990580041000c0300200b180c407506560070400c1000014a441200e403000c1c407403c0325103982100031480340a2100b81207400c2040e6242c0c0960161028101c2d4600090f5445851f902030189980115000c200703030408010950641d54080000340c810700c002d040c01c110180c900d0b500201c0c2d65861a0351052000f03902c0c1c20103d1550b0454206403246074050311240c0d520015604825011000c140c0d4800c9040702c01c80f0640924404900158041c580d101c0036201808d003420310507004000c1c007004001000424a000003174207458103402c8507191000c00c1003a80101c0e8441103a0f07001601d0303200041038440140d0340080ea48069084002d522258000381004150fa40c41d07002201c16022a41d24801002940419003200002e1000e01c0b11400074400b1400001c0c2c100c0340380800a841e50391110040282c883d40040c070500180c0040c085070350451410780c0d002580c84410007824500940c004c000b00d2507607400307600240e8071a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 626818561 1250 626817311 626817313
    0x100c05030910030603050d140a03090201180f060f0c050c06070f0f0b06090105040b0918160f050907020f120702011b140d052d04030c0f05040b01030b0d03030b040e 72
    0xc000408010003608560101b40d500e170040c0c000107890b06016035220001c10180d560760a0130801e400d0380580040044143c1039040c0020028003201c20a12010090050324540030108404c50404400030700e40d4141550203010300982440c2031012400001c1d60761110301c0300711003d0396282194600b998030a01d14072001484030344409115020402040305a40c41202c0a4454201c0c1c0c0c0e98880c1000207030740070032040580001a4401055040440c0c01481981c0803060044840e0b81c0c80028219904284561200c03011010062091255150241001e9040341061008041c403010301c103000d50b00c5810107000c540107880005070325000c40e40100803180805e14801c0c0c40c1d62034010355003840040420714540c00000e6020301c20840c101356000e0790644032041044e80162400d42b0154070f114074061102c648001c13400341c041c0000000900c103445004080e0843c86c64428107503162806001c02d2307405040c405030605041c0707400400c00d030301c034a03030707096007458240c500401c0a050380303408a80244103d404690071 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 626819811 1250 626818561 626818579
    0xa0317210c0904050f0c070204200c1e0a0201020303011401030b13021309021305010c02031002031003030207060507080a03091401060b090f030c0105120a140f07080a0b100c050309 79
    0x20420104040c003000c20b810341d01400565100301125140c5441250002002403062201e03202505007a0322030140101c0d91a1003598004401b03404181c150001000c5031001c0d0300c118011409440082030102d111000c0b46c00401a15401b640043d40307901050045840140e04800e58072240da119410420f840c04d4003800c1c401100d52440780040181d40042120310340c1c1c2414100010f00d400b424421120540d013403c1c0d07806070060420f001150f200e40103800c01c1e6414460212001207150043c0300441c000c82c8a44a5000c00134998980039041112542c0701409100080c02a1804a058082207031501800342ca00050411000c2ca04550217040f00c6480d0b5545620300702010685a40c40c900500141e98103c84004207080240c0030543c0d80d80c1803079041d5001a40034000260411000b070900313a080020700c0b10104905031402002414218102c46500240d000c031001d100009420800d0550003101b9030340c06005e01140000400d0701e0421004050b810050300c03d00c0300003440414400d443c1e50401c0242400b003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 626821061 1250 626819811 626819821
    0x702030c130b2205061509060c150114010906020d09210609060203060a09110f0a110303070905010f180e07020703140105090706050703020703060225060f0b0a031721 73
    0x203903c40c503070141181000c0c41c1c4004a041881c0170b0440c0311044800a036000e103895000400d00025801a10210b0802d1140071122400c1c00f0503800a41c1c003804a968a03007040100304c5000500d00307591075001c50155003100c00b841c58029071000403034055440d05640505441004500036225907280d000103840c6a02d4000c0100030000980c004500406048030000c1001c0e8940c140c007000c48841c1600743d102c1500070080b030034001101d40050604803402d0f0034611000c1d0441e840a40c29917204441241c0080c142c008148010b68105009000c8032a0f24034010550401c4caa10032001c0031042e000e12840d00300d1000002c0c071420b20070420b10014552000140001c1c00c0c004103843d0107068282c0702c8640b1742c09015404201a44a041176a0140343c00d580180a010b1550f100c100007540841404a6035510881002c143e0051121101c020280326000000716401b00b42c0c00d200448910410f240d06c50f403101c0320300300f0102e02030191511071141600b88290760f42001103101c0780c00d0002e03050603002d00065442000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 626822311 1250 626821061 626821099
    0xb040905041e0501141501020a0b0702071203030c08101415192f060a051e07080601110d0e0105090604030c080a060e0d0507030e010e0316050f03030702030c130b 71
    0xb00ca000005c0c540d12040c1d01c441061442c5051940700060040e840792000402140d0803414058004035180162454192224003020200c2600039066010a403541005180d155000c800aa40900c412500e070540505100840c25400b1210380901d100700000d0f00d4004a19418a0031120718444c03040c55042244031a0034081d01d40d120302407207151246040c40d5801c5007440051001608203403018090041c0742c0c0c940080070f0080c007003c0c22100070382e91044000d4142c0c0c03e0001c240303405040305840f054624500400010b00341540980c10640c01c0e0011501d02041d2904001711a686400900300151660070a60102e0002d01450740050480001e5100004100c04041400c81007075001f4403003441034040300b038107940c2d440c111002c1550024504105031004244250610480c40d80145000030b40301c88000002440c04009500410034441c0c104130070440780c03400c0308008260304001e034050b604100e01038000039158925408490700440c04552040303c04a03c0d6130051074400b400a00f00d154200320a0304070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 626823561 1250 626822311 626822321
    0x109050613170d2f070611061828062a050c060c0901030f0e031305091303140403060f1406010309020f011d030109050319090b040905041e0501 63
    0x1c02c0c2c070107400d0303000d071156020101d210700f242c1c1d149440b8032050921184040d200586141c140c241008000190381c0380c4440c040c0203c2000307007016030742c2d1102d0061812240d42030070f10140c8210030303000110244035500840442d0400513200d600800a5141e0403442c04401c0c164130703d80000307201d1480d00c200f10102c2032184182110b010451491600f00341c64400040c2c0701440340700d17400080341c1c2c010000100500c00c8200140381c0300006141c0400c040c5200c1c00d000080d00c4d1088041b4065400110300302c121445102882001448102c07200304041c104408142508258803402070b080100d0b460701180c075821080708480c02035900c850100030b000c0384480505c0041030900c42d564514108500819482c0d0f2090041e41c10958006000c1c44800c40c00000645105550b004803100c00c0190100e000c1180c0d50a200d010440c034065000b03190707a1003690b00100943c402d003c1d002800d01007600d0b0103011400c68802550161900311030000365944850800410400d03980784d02a60700942500c0d0710b01002019000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 626824811 1250 626823561 626823569
    0x3060e1e01050417030903030a051b070506040210050a05040506280f120903050d1d160911120a0218060417010c26040c030f0b0709080102180402090109050613 70
    0x142c003001c000100749043c803d1000f42c0d0341b501260310510120303140002652145400c519050040000c083c40c4001f0a2070a400515043d80d054000e0410042941040b100e180882c00f55450098680305007100c001d00207000e5402114080d03900400c000341d80381070342c5441081d0001700d4076450142c031100c0c0600504400701018500d00107000580b000282c041e00c3d0098200c803660503203c20781091141c403910f6004005003001c50b20844449041e100c00410705000141c102c4400d903c0d0341e180c4071b0500c1c40030001d6424900c444a15030b1303010400c0c80c0e1003401d202d02594001010600c0075903203440d00c500f80b203220301038800c85960280002030006040b02240f00e01080c2c00080500a01150070148400d84012104141003901c5195006101d002d0a05611610350b020780b10394101c03804075440e6181c01c016030b02654011101d8403070150510800e03580242e5504010005100254a0a100031450389843d81c641c2c078440340030f150007180040c11a805815604007501c0b0141c100c80c1c580c0c7c40764880c41c00303141003442 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 626826061 1250 626824811 626824823
    0x60103140705061608070c0f090605010327030f020a20011806050f0d020c070e04020901140102070e0703180c060e0402070b060d050a0f0606090c05120103060e1e010504 74
    0x8400034071403d09100b81c0e41549800c508140e1480d40da92074211140c1d02800c0c0440e580252008049003501d4001400005004031100c0010405d0405001400f05c500503400c0007841e1030054441e82e290407042102841031a85843d04180c8900d4544050f450303c0b082c4400100940607110350800a00362010342d058900100b42d0743c00d810b180200345000780c14813083c020707000015810444858203444600052951a803800e81c018a041064800d4504092003600600e2901e00888140025890400300c8240500800c00c52303084a03004580010303503592141e110300449a801c1a00241105d40268019400c4410780f030410300000b00b01c0d14202c07034400042d000f040d0114020190200780c41c2032620a55040d60382c05038000ba001c3d00c1d03403020024401c41d9980201c480c2c0c0b04d00003071000000c3e0b0782c80c2c42c0000d042c1710325004586141045940025180c81124103001c014050000400c0c810352664118116a04120001640d60805010034101b600000c3c01000b18034814008102d4084150300a92086000300 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 626827311 1250 626826061 626826073
    0x80f0703261603141506070203010207050d110321040c1d07140405010503040206090a08031303150903020303040f06061a0c0d0e0303120903070b090309040b0103180b0c0c06010314 79
    0xa02c20740454080a42c80c070444070756400060f80c100c09062a030003120b83d00a042e10308104141d0700190aa900c0b40070100d600b90400c1f540d040c074490f0003d80f07185690b00144055800c20701c00e1841d80c0c51070780c03e545c07035000013498070750220302444421002c2d44080c0504c0d01d5400f00d520100030810040c0802a43c0c800d00040780200d003d55054009002e490580d0340580d181840d54a5640800c06d0030f4100a4141d079200c0d44240c2d0000b0084000c200420036511040c9030200b00ba480c505200403103005110010805078146090030000136400b004490f40180d008008a54524860800c18004d00c030a4001000840c10200e008004481c132001030911a83c0c00b4049814a0391074520444110342d0f08030845800d6842440080c00201d0a00303001548071140c0d01c01c8030705102c3c7c261030302008000c050b9188030045d00001243c100c01d0030b080c050070302144801c1c241408200d02a0031201d80070b2104160143c581407808000c6041a61400119820004001c04a8003503503101e0a042c0318111032504507140c54400c030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 626828561 1250 626827311 626827351
    0x90b0d030f090302180403020c270c0d0516030c02060c090607050c040608030903061303020a080c100f0b0f030601030804120c050d03090f0f061e03020d091110030504080f070326 78
    0xa12103da40b0001e035100cad880707485a01c2c040c0340300d032110001d088201c5c0704500348007000c02131b01c0e20700c030380d521490f1100e03607400e803000150401070300b140c0e006901c0701c003150011800c124042c801c0300e0480f4028034003070b1202e5545116506150f4280307040c400d407455009003410000958500b000006e8500307c0c60440545030580c035071040710812401e61280003000341c0c00c64008000810042c0c40a84401c00c40c0c0c0d01030b0341c0e210301c1c00c80c0c49108983d213002c2182c0c0d4259850101c6207080c14900e01601d10401e0640041c20359504641b11407106010701d20912001e9071100703000c08200001490030342c0040001030031051800c9000d01e40901071030303000d008a24040440000000d18070481134440c00855005481c2e010b14040180303205010b20204000c96400c0c15002c02000380e2a10aa1183c5601c0c503000d05c1c90310541107131180c100700e010304001d445042014204020702012500e81c10480340780089940000382d40f040685410760300082c99000002800c511000154000c24a0845c90745c864a2580b04103100d03e199 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 626829811 1250 626828561 626828569
    0x1e0b040902030d0c03020a060908070b09150c0a030b03071404141603020a030b180f0c040807090203100e0a060305010c0503150f060d060807050a090b0d030f090302180403020c 77
    0x15200003035810b03400324500f029464012100115442c1c002d1054802d00411902c40c84283d0301c1e0075004a47c00b100010703010007030000c5901c01a402c000480040d004038026044401c03804400074210240b01c400c001045180035001e0780c48115003034806400d440d0300c641e50303c14100101041c0c2e0503003070055080c8803100c1040c00f290104140300e888200800e8a14010751031084000b034001101c00c9041c10342c1c803410b4004c05c2e40e070003503520389403440481e14070001e25201541c0e1984440280059249640c184802d200302c901c04110101511904800140c83c0c1d61483c031001c000c500c4560190200d4240181848540c0c0340540001e030659000300e0091003d00000802151148412140c1d40644010125043c65070302e403110350490600c5c0010b003518141520248514111882c550029015a1008004001174103207220000000c1501800c1004000c487d4008125040d541c440000d0402124094050b045070003040000095900601540505404000000b1f1043c0081c0d07026000f502c607066600c142850 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 626831061 1250 626829811 626829821
    0x4510020309210f161406040c06030c142505070311030307022803060c12060e13030f03090f11180103080a0518030f070303180b09010c0302010902041e0b04 68
    0x10001d8030751400c03441d40f40f66001d80d0860350268001a200c01010340c00b096403000c800780c05d51521401391070f1905103403030034107101001940421706041c2011600c2100c50b0f0000c10000003020b41280441d1b4a424000c90360310880b105c007600b0f20b501520a00048280080061003d0030749225583c0a581c1e8684203080540c0c901030154000d51001c48240420000303602c1c4400c1c80f090b00820120304445039181d03582c1d401911000414a40018140d090000c6005210b020b15001800300384640707c1141408540c04070200041000541481803000c04541c00d184070f94011032034aa040f411410345203880d4070f008400715500840a1b0f21915400503c810344a0b00003241d1390403680e024400b1442c00580c11800e80b03054015100710398030086079003480c0c6619282800800352260b841400b134021181075140140403041da2410b89459069040c00620921041c1c00c05c481c0c0e01c1600b404c21006258807490100d0145c4001c0380000d402900301405411528100100885020303144c09050004011000078881194 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 626832311 1250 626831061 626831113
    0x40302130b0a0b07050c130e010c09080c0d02010216030606150302130608100308040305030a092106111c0507110a02030709020f1902030d054510020309 67
    0x2d11070300c90400c03040700d80708020804540705030242c030380e0f03000b038500099000c08010242d0852a6280e11802000190a201e60f40d44007a660802d107400c1d40c200140d0a64941c0740c0a003c50103207520072030140c103680c0204204281c0d0110743c0c20340c0c0c11154481c40e250001d00111310444250f06c12079142c1e140203e009000f960b0040302d130503490051451406a0440350028003810302c00401c188010088080f600001c01440518014030055680d60144003000f0182d91840d84400000c20540340d8020760340035074002e024815508088041055001d202d50b180c0a48164410f144c10111800100c48105c001d9800240c4900c542d52200d00c042496400c210380c9410a40344021b625030000ca4040c40ba017071080e40a40103296030346110508003501c51440114050508955801580c4003160207411132155024543d03018414240404440c030356440e0000e03000301640d0722868110f044828800780c2888110f207040d02c40e4028802c41e10f00c060011140002540f003591038440501802c00c81c042d800581041c0f00c1448 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 626833561 1250 626832311 626832319
    0x141f0603090317071e020304050f0306040c0311040f0207060c080f0c0406030213030221010c1707080a09050706030e07080f0312090114041101081003020f010309051c05040302130b 79
    0xc140041c008610743c003001450702041c445c050f0b0343d150701041c041c5410444450b00360021a52103040c0801c0002050710418454403980c000e40801002030907980c2c020080b43e40c030812070171640f01050000341c0030b0b000440c0629404c2e880400c1c074a080c0b00c4a034120044c1e5135025204c1005903240e262440c1500101210703040c4080404010030000b69100b03034000c1800344041c4c2584110280c070b036800501e0b00e10028500345030320240d50010014256003881201280d00240c01c1002c00403c84c2c2040d451520002001c080c14480c51900007001c0d02d0540d00000c9045600c001910081034076058003030000c100d11079184515200e020004641d8001c00180304096040000007141410202142c410070711070300904070f16003952107840d00048501541e800350300503403243d034200c1c02c2e00c0c05880004104a070010b250106c000b4801e04204050303290910701700307810503007864003007007411840c01c00343d00d03180e0040e12802c1001507901205e692a580311000e0030640c0c0c422241c520007481d80441003000e54015120139a80 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 626834811 1250 626833561 626833577
    0xa2c070e0403320a180b0406020102030f0a06120b04052d0d020307020d121103030103200105070c09150506040e06030f0307050c010507060908030f060a081f0e01141f06030903 77
    0x114174040c0b800c41c005c0b0b070061443e0a1150f41c90340c3c015181c64110f6400440540e40103c2403000e2521201070040e80100201000c2040302c0c9080401c107041c8820b4400070301076803885804601880000e0048640709240b00d40144808103d4044400299540c110020740310301820030030340b0305d8a02c00720440d072040380c0040c12200d08034502c0e00c3d440f42241100c1140303001e001e154403010a0009042c000707540214042d0003034014203160b400302c00c040c280010302601d0420004001c0840021a24501101945c0e900400010b10030301d80701c6024420001a0001a445078012900182e1701600c00500ca00c40c1c90180c003510100c00d5500101640c902881d200201150410500c3d26100e500c600060b080b041d00500000c20389400b42e8450740c41ca9030055995880d422101e2007009001d0038032072090b2008101c800002c3c049482d41d0804000081400401e280d01c56490b003458001001c802d401c0010b41440004c446550360030411144950f0f000003000b0300300101165000000e045000e4440c10200a416440345a0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 626836061 1250 626834811 626834827
    0x51c06152d06090518070e13020405010201052518080307140c0a03231912022a090613060b0d1803050702130e070803120a2c070e040332 60
    0xc4d01741005001ea000c004074803101c0002c0d0755603101c220741034541c003440040c0d0760f07400c1c01d000a0949200800c0c002210003400c2c4d01c00b0000350a0166072401c1c4200703143c50703030340862803a441300d4403141c8551064104d0301c408074002c010f204e55001d48180c070202040845880a0340c8a0a12400d11a54030000c0c00380d40440503404428145045200764844803032080d98000d0ba65100d09059000d680f18003030340d504044040e140e0741590100002c280a5007100041405014401c882824484400c2c442c2070094007420b0204035280c4480b41441c100002c2058144401512034055072550342001c030003031300503e00b06000710f00c866840b005000081501541d9072480c00d001c940921190000052801d21401ea448c160054a03001c1400340c01e020b000700301c0c00f440c1d44000003410700003814005400b01551342e02c0d00d15a554401000750705480400b014181400c101003010b1480ca04140d9268008001c4078540020401050b6000d1661160b0b2410459001e600c94044c80700055181524842c0035000031041141d01 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 626837311 1250 626836061 626836099
    0x1050903270603160806010810090c02030c0d030c02160e0c0f071401020d0b030f1902030f1b0a0603050615030901060b0403080310051c06152d060905 66
    0x4255005074082020030400c1200208206034801c6030865800c5201c00c080090603944504140d800401c04d10b044862402c2822869140003020b10a18449030f95404030712112030300034010380e1800380c42c180c180c030460452054094050030200c864400103002d105c500101c1c0d03200302075003074069490f030308451403542d5940b4402c21280e900c6803c1b49244000148000340024501c07001000c40488000f0016854010401c02030060720710000202e4070941089c890301d40c0b024400600c880e694030070020141c508045a002007428114900130900e40e900445c07900c000318103510001b1400206e420b890408100b9a038030300890840d641600c885600410003286081e103268410051a0006c6d01c0f4800010495600c03040c03071041707510682c000c840d030b940c010003001041c080c203048510042200f690a03000000191a181c2036110741950b004011075038695000c010801c0c00e281d003a019180c0f160160343c220300000c401d079091032103081025400355943c0401090962003410180100e9002030f00300d000d141c078242d10403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 626838561 1250 626837311 626837347
    0x803030411060405030109110f0a03021c11030f1501121109040318061205010e010b040e0705040e010b0304020310110904020c10050711010b0a06050315010c0c0b13050301050903 78
    0x660311001c14400428103660a201f2005c0084c0306d20301c44002e080401050001d00400c0d4484248240d090200400260300d03544615072204055141e0703030500c00d8461501906103501d540e9000d03054414000999011500003070086141d081001400c003da03a40c82c440f80c1349500d54064002c10035060040d00380394134102900d149030010710a040c9034003045803405e960280118607500040c00200144950f201250301131240f04c0c007600c49541105001d41c140b4900c951a4812407240c1d0385204074031800641000d1059042c0c4000e0302c04950f210019503074400d1034589503081540e00303920901500400040b00c1c4a00c0c0300700d14185500c2c81c000b5003800b865070200802501b2060400800303018032020401a50b80303d2080da44107000c1034880d00c42e102d03010111a400c4440340140c060081c101b0f07650500000c0d030045e05032a48200e0501300b43c3c04803000000100c5140e00356890041050000c0314002c2110398480000d0102d40746243c40384d05406640302c1c10142a00c4041d500c410880d0001c010301c5070307909407550b01 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 626839811 1250 626838561 626838593
    0xc0306200d09021201050a0b0f0607051f110a050702030613030813081309020a140313082215020d0c15020f1b0a03260c0a02070305010e030c0d0908030304 68
    0x7180d40d41300840e8019600b0b644088802d1030060343c0d1000c10348118508108660060b100540b03c043c10548503940307040d6607902d240e0b0440980e9146203542e502000141d08054844101005126110059072a019049411041b0101c0c880c1c014400010a0b4107020120a04015015a80c042d840d403140c500c404201030200d54141c0d0001002c0013100e10000083c1c0b100c0c6c000b030200c8040140d0b40c1640090041c0286020040300d030840000b001441050100c1403c101d0915400c100d03400e540c2c0c8440b0000c400000a0044803940401c04003400268100d026540d1245440103034080d80d1080340301c05001c40309055a090f00400d1342c07032908a1400c001c000c80e0f002d07201c10700511468618004000c04040904404044819542c2d405101d00801300b5134020880f0b1010820012810003040c02c20000b0800070000501c00c9440c920041641c40c51940b0812a103001503820074020009501c07045103c640b2a030040000c09000d1007041111a9518418800182141d0382c02c00590300f56160b0359201c40800200005e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 626841061 1250 626839811 626839819
    0x70839060c0313120c0b0f09100c12021b031504060b01092409060306080c010f021614040b030303010503061602010914061803180d020307030b01030c0306200d0902 72
    0x11420b061400083d400000e0580c9011040d132102c49842c0006031511103410a900202052121003e004d1040b4203072203c000044401e5180000013500132581424680c2d0040c0034650440c92903484141c0204000d10000c41003c207080c1001804000e00d0381d9044800c4003078910340802d40000303000c00c100e40e0204a4050701494200310f0b590f540c1c0c440b5801020341e0410041c00d4010a0903c0b282150480c950034014046420b0600c09549000324a07911291213000a605200c1d022000b600c180c3d1007804000c071010171450103105003c1e10391070030390284100f83d1082c1d40500c0c900f0b00720300500d00d800400d5a040301d6004009240540d510f02080d9103503210401c946066640f0307007450500080104003001046c2016900400141c41c10380010401c4442e0300c405200d0b160804c01082c56441440704540080718402c0e6843d2004c52840e101091a08241c1c1d80060802e003000000441040355105c00300c0c081b40e008120610840500100340c402280030341e05009100b840400082e64100329a400680000380010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 626842311 1250 626841061 626841067
    0x5010e04110316080702070303080c0304031e0309230c011b0804240809120a090b190906030203070801050f220e071424040305070839060c03 62
    0x1840803607403600282c074604142000c0e2200746400a501c141c0c00d581c06446131006020b100c2c9142c4000d85404c13006070006401400c00000a41854001c11005a141920a10040e40d40d0300a07070b0002c0081c1249041150070002607040c0c0105041c42c0321200c0b02c55a004805000c44080302801550001e005802440300c040602041c107020809038405400181010b2104000c00e40e00d07100b00d26030910780791740c10714188039005041c842500c00006004001e101b03145907143e038420429009880d00c031401d40c04074403d903100188991a603521007400c00d00c140c46a4235020600ca40356074050f0103a0004a0b005c2001810010040003a4500320002c400c41c2200607040501540d00ca02c0c03070f01d41c00d05441000c400e45503251000070080302d03020440c080c000d242c080c010144041001c0001004180b400030f1a204034244000c5c101100084102101d0046603c00c0c1141e41d865981c41061b903c0c0c113607141c50503110200d41207480110f02c0c0e520151580c405001d45200124100e002d007089120380107140041c11610040c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 626843561 1250 626842311 626842331
    0xe0409150c110a06060501200c0108060604081c030c0207060c02040c1710030b0903040617060f120f0c0405040f0609032604140a050303010e1308041d06031605010e04 73
    0x5003c00b520a5000700b20108001e0b042600141c0307045055410300c2170700071940138510711240022030710300303040013003440e29000b2901e07500002203c0c0c0c044d6800401940c0070303a6020701c1e4811941030144885204c607403001e0001408205c02682c40381c2c42d40c07080d10081825880c00c0303001807900b50301403141c0510381c1c100f5110031000c2d8080d0b10070a00b421a8122008003402e1010310521091a0000ba40525003100030f603e00383c200240100105211071110580c06090342c085500350f6526581d151001c200500a210514002c0840301d954244100e030405440c0030703000d003031510707820a80521840759401c50301c920051005079441200409607000240c3c01c10843c00c0c5d44141a8420507211504103162156031815800c3ca4105031800c001e00443c41c40d442c0d4428485203001502c0841502d04444455528524564520030721181451183c6401401008000f43c041141e2800001c64024900303040d400c04205c2c3d4480c0141a9519200484200c1034140301c003041240758452014010619005070020850741c0348 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 626844811 1250 626843561 626843563
    0x10303140a02030427150503100e010f020f030a0b011407030f0201060e0106181508040209040c091e0c0207050a09020c0307020303040b0c0d05030f0403050a1b060506010e0409150c11 80
    0x30917810011110b807640002c50f20b0706900502c00080300c03040c00003906929000c0007079038462036407092200032500c428207015505002e601c1a84405007041065503146c440310101c21160b802203414038441480d01d1400c0b50380b54441d09182d00c0002c140c1031443c0c80d00f080c42d203080d030301440c02061010456482d200041080c6840c0e05210b8003c09071901c8480c189910026215800b04c3c080c0c00402040541404030034407a60f00502458100f901500c200c1a82c1e2141d080410301e64001e0741295030030600705414052110342c4441d00303002c5601d0511040041038000c010417600d8608074800d16a2014a04009107e0070142e0f40c0180701885112007201d10b0045141d004c02d055400039809056a590f000c0350380510203906209450101c0c5c46171500038654034090a14001840c000ba2002c0c040210120390170704154020050070b2112a00b1191600038a00d491802201a003c2225200e000a5061b400c03804542054000ca004081d48080001001103404400701c00600c80c84590b0410401114026511000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 626846061 1250 626844811 626844839
    0x615030503030a0c390602032d0f06010518090f010305061621091b0503190f1e0c0303020606041a010203030a050a02090312040914010303140a020304 66
    0x1210300301841d207902e00450880f044500e101c0d01c00c001d000312001c042d8840c0300c402400d0b030348000920440b48040d22607180784003424189000d00034102c0b403000092006041e1068190081c101040a0807985024440400706148505440d6140351583c1800420303000e40c003a401030030b10420000243d400c42e00203200062419681501d90024500703c5100500c14000c3c1808a42c0e806040350b100320401c0713000228005e000c0500c003041c42a80b80c910300610802c102e0250010754040d508000b01d035040340e01740d100f2070400f2070151044078801d124080c540301c2d02d40003880727020031116000400400650029180c0c00f0a040e0b10341c00035004803851071200d900189030f10b00104003441c000c0d0b00800c0030380381c840240030132510801101040b401440010082c0340e80e0020450307a0202d07041700c020400d600c0d07015504010b8003d40031038075494040d00e821500104c904c030300a4800c0720405242442608041d46184150304402c0c000030b000203c1d030380d010804120904005040c03070003640c03040700d16007a0340fa2000306003e0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 626847311 1250 626846061 626846063
    0x6111b1f080603010e01050403050d050703020906030a020d1a0121020c0f0a0b092a1207090212010e010515030c0f0d06050f030106080616020f07080703020111010204030302070909061503 82
    0x5a000801e02c0002c2c00e00340b055841400004000300300c10304040d01c02400034018040c0740d205032501c540c001140036100e50140c840c5080080c14181c3c8908000c2040700103504203c080c0c10882d0f1a192102c6910040c510f145581004107031075109185808a84803021209042184100700d074080106013110343d82081039005601c442c40292a40c420f4601d0092140c00d40500b100c50039601c114034100c0c1a000d55411084290b0300440890200850f038004039481d0800c651881000b401640707400282018035800909520f2000304006009030780b103008a0003c14000c0c05141e41028106850801d8811403600071b58029010086c41401c0400e02485488180d0052010f80c0e0281d441c0c810420a604000b0790154840004900920080f400e12042c0303a0303508401071500c40054001804100424000c0c044128503d1159041e40d6840f9160342045035220021701c0100c0c005001240403c051400620984080c4ca178541d018004a900d0041010080c00d002c40083d14a03e694100c1060803244450f1618021 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 626848561 1250 626847311 626847317
    0x1a131d16030c090614012015090c0105041406070201050715021801050304151a060d14060105070b0114150309060105093403150f08010606111b1f 64
    0x81d0940c42c1c07000810490b80c2c0149039080c1070140500c8014100900812000d00a281c13500e41c52281c2001c032a460181d422000b02940542c0410b411851004d40340113100c0e2140c44100c840e00c003426001121240304922602050404400c0030ae2503a14000b4010040540140342690500080382c5034020100c89100c1d001e10703181d5000400d0310f0b0f1a2920a50541c0c14582400c0c01800d514103500e6800b40140c0d1544052884d540d00c0801c5080c040b40d8444500c10303d000602250307103440b01190f030400142522801d22048801d1040014060340c8210304941e52079900000e81c8840340d02c0c10072a03c01c02a0052140390b803101c3e540804d441e1410580000e18801c0844400801695140c2010b10080000c041e0240e004104040d41c0c0d640c019101d640c4142c0f030000c08402813a21401052000c40c010701e01403881c401c000f00c4d110700004200c124003101d981030711f00d00c9008012072540d96905569034001a001024a90081030380701c6542e0700000c0e0780204811010380203003111488a840e1070700c0301540b00911008 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 626849811 1250 626848561 626848603
    0x2030702100e060d050405030d0e0304080c100504030b0709210b0f090a2a170c01090e0601080403030e07300816060e0d050307031a131d 60
    0x6501d070500a54000041c0e50800d00c0c504000350300440c01c948190010011182c0c2c50f1400b260800c0020001c490141040110030403c003150103400680f268013522034800c0512500c0502003840c60803565012400e192929001d1910b850b558031000030f44001000c01050009007500007a41c1d08094084032650794441e88100003d038074a10308a9106200500030036004540d00080200f03d002c00100307142d00356000000f00d0720110400c900c860854502c0b00d040351050740e02c50b05c002000e00d000b80882807007107458015901105480d00045420145d18412408081041400328034254082d500300754125000b85004200590342d8005d2526010485d80b0280140c0c7c00c480080e41c607000722000306900102e21001e99400c006807620381c41e210380619040c4c018480400c0071383c4030400c03c02d030b4842d880344c04044054941101d000c0c0000303002c0b0f41003101c0c0348010900300b00031071480607c2d581a41c03810b03400040c00c00300300074017041a01c4014205a2080401d11280fa043c8030011041003025820400c0d200f809801 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 626851061 1250 626849811 626849813
    0x110307141c0516020607020a0e070206010b030c07140c100e01020706020f0a1b090c020a02120606030601140105131e0b12040615030807140c1824090106020307 70
    0x441c0c101c0c40c62200000140c40240c1c9140164004116001c1600d644454031040000380001022440f0f600002076005208080009000c0503030300c1c42601c13413056074003030f101541e9072281c8411040c801110b83c0c40890808003e810000740b54a030154801400c804100d4035501c01c8900840c02c4102000c03a004003180d20340d02181c2c03c541e8100a81c40c00f420f014400307000c10084036400a035a61003680c02c001c0090714400720310315600c0c0000202c103004081c481d03014480407103402d80107525149200d1007079000d0303d6881842c030341c10301d000103100d80903c901030010041b5a2074105690b50a4003620310450410504001c0c61030070310980200c0c10054225000071406010304541c10804550165200c4c1d0103032a818840c2d000c005086140c4280e101c2c0e08400c0101e0840c900845244044030b01d44c00c01040703120040b030b40708140f05104181203a40c545001c1101c40c6a00c5400802c0300b001c4a9944d0300c00344000f030f480084c280b10204194603014074646122107090206490001d16002d0003604050300586c00401e5001c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 626852311 1250 626851061 626851063
    0x512100909050c10090803030406180c030602091009050f0103110c0a110f0904151a04051f090e0705040209120106180501060e0603012304050703150803040806130311030714 76
    0x1111413107410503190079840d150500d071702ca00008002914642d664102c2180b100140103210b4101503020401c44540b40d22490103000075046080d206000e255030038585000380703001e22400029550010b0407010207020100c01100684107280b1110340c01c050510036052640c0c801c208403801c1c584194128400e24500030309020445005001d55440381202c0810b11010a0000003c8551140b0700c44000c14a2a100203440c4400c4007c0441140c100c2d203480c040000d1080700c0c1d075012001242081760800015591010001078031643c150005190f0003e2204202516059008080e8110041d2544054048a03002c0b507003100c0300c3cbe070303c201007124001c0c51745002ea600c0c1c0d21a1b41d015120030b051284e1a140040c0205a0502050044a02040a070f031000710060202c442c20000f00e04006000f448036290000340107000c0d01d156602c0502c2220030b02801302d0000b07404019102a141041c000b864555144810032103041c6009106905002c0130000b12001c1031000c1c801407001c18052a00c9800c0302c021581a2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 626853561 1250 626852311 626852329
    0xf0d0b0303160b070512040c0e06030106031106090a0e091513050c09091c030c18031101031d030301080c0a090c020c06181207060f0f0512100909050c 66
    0x6544a90800c21000b80c4000e4030680d100341807604219403034031030f65500e0700070381e424403030110b100c901084407000301310801014908500a48081000c02c1c082906e5203c14036003610440d00006000300085021507032a820504090841208024816007010383c8e00c996540002d10240c0d00804c198125a1060f403030003055a075002d400000000d1421501d010549a460b12101111120fa01c5000d680c004165071007802c00c5040100c180380041100300110384030016005144414034900491603083c89960903102250004046030b410010080c2d0090450700110010300310a0795100030300050b002d03141c0c8002010030203076000c0d203c0c0c0d000a000c1e2905000401482e081c40780d20800c10030b801e03c403400f048194082440c0544901c2070315010307280c82455403000b251a00e040900c40c0c1010014001c0d0b82c0300c2d100001d0710400c440c2e2507100c1040e056803904048500c2090600c0c4000800c004102c106e28103c50800800d41c400c681c58081802c1c140c0740c50701c480960301c140c503081d0f555030f001c9090040285019080 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 626854811 1250 626853561 626853581
    0x503070308060a03120e120303070f0905030f10090503040b04060f08280b01050c0114010e011406070f0c0e0a050402090106021b0405130b18010b041a09070c0204020f0d 74
    0x440f032070540ca180da490720200685004441040154448a0308546805014204090b002d4068a03240e00c1d207080010140440281071000140c2514000601820701003402499030641d000600000040e851900001e0568100100d44511040100146101c0d066000c0d20107000ca5035250403440304030308001818040301401d18a03034000c0c2202221024056030101000041d0008030200b00101d8010040c0c41c04c0c02011040c0849500300403a04400581e400c4005040c0c9070302d030301900c102d40d0701c80c50344560106403400c4c00c5030028410804000415050460328942e107200b000c4100c000f40c0c8034802036200300002d031821021186c81d0004d0208500d00002c2c494054160b07840104402600005022020100d1107e414012651040840c0c01107c0c0c01020442050300034a21141600780782100101d00d5491074207100c4a03502e0040421000d01d86401030213070202a141d04032242e042c441e0104036040c0c0000e080c01061040622008006880314005440784140b0b15040c40e484140911800043d00c4035110 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 626856061 1250 626854811 626854819
    0x801180b010e010c020103150b0c061305060c2b0614040902090c07140102070b040201020d0c08030406020a120f0b04111c02131d040303110a021b0406050d050307030806 74
    0x1060303648a03644010b00c256004402d10b083ea0005000e07000582c01403001c0131798503201c000400c80104140b40400b0003040216450800c98803a559003001c40541c0c408803440042c550b42118010500c9d4441c844040d1141601c0310302801001030001d1010381c140b1008075502c1d501540c0781c540c104008402e0703081c030ba00414004e035800e101c034030b59950018511420091011001c0c110200700c50013486001320110039580b9540000710745e12611814280340700d510448040b80144034030942000102e2003001042d03c00c0e031780004080e095407299540c410107500070040404c1001100c0445014585043c002d40c00170080340c1c000002e00a208000740000d5070807441d0203081100c410040c2c01d5200050002c03c00b6076403290314005860b408002211b400c166510381c450044642c90b98491101c0511030280c0f1402a482500d00300411000840340c10004d025540b0a80c2c05a01720078400c0304101d0740203000a00ca0780008200250300b68840d00010140d541d025400d031004e5101080700020180c001c0c20b250b0300118115 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 626857311 1250 626856061 626856071
    0x27140411040504120513030c03050a06110a020d0305070509030d09060815090a020706060e1927020108071b14060105040e03040b070204150b090a060503091915020703080118 76
    0x1344410454842034101d880c200800015803100345658442c2c03100146500c0400c0d810400e0750303810329070307a1800394031010b03240c8034038006080158095003c200c811020300e50700580440c2648460643c02404006c1200702400001c104010f2165418070841c00046141d448100b244c5c0e040c0302d401481007000030710802c03500d00b104c5112840b80c1d9030440f101c0d0344411510405662100c9500c5c1c100b018202e00c1c0e0103512103000d80018030044041d04081c06070100103d44042190024140d02d5150341119a42039800141460300b1501c095441480069444426420850103962071100c8140c66050500c20a564580101d000306c8000d10003070004600504046405202c81c054040f14103441c0e02c83c6100e454100b043c0025034200715180d40c1c00c4003101203214011140b90329555114042c60758041c5c564103128102c04040803403024043d80940307002b80e041800070b03c00110b2000c514100f10014031010703a001d0306000000c29041113b800102819442581e881d0465450070314501c1c0c2c1040c0848040759118280 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 626858561 1250 626857311 626857313
    0x10b0a0f03050603280503340209010303030b030c0a151e170709150909050703141501020a02060a0908060711030703050a03022a0d051327140411040504 67
    0x80c5c1680d481c1a80100400c0c2e034020504400780880c00040080c0035000200b01c1e17403170042c01040e4124100d5850200d024a415000b141c06603024400a40290300030381540061001c64480d81c000c06c1c0c101d002070b0880721002c80100000f00000c00710b6200198103540c0900b484c50300e69110741c8008504544080d10300d92a510f108014140b400c1c456405508901d072000051049071082030058001c03c082d6422114038504e0b010300406038641c6026034410710381880041015548244201c02407a00505030030103698481e103d6810380340081c0041d00e81103200da40c10b0380c00586c0e240c10090504160301e440f1111a035182403400c50414074003e00410034030109034a4503250f5680030048a11084d41841d0203a503402c08500290024003032080309191039032401a00e040000000028007034400c13400000c90b08020b0251404075500d03c240804494542d50b00103040000c1da01000300130390006941c0044c7d0723101c42c00c800f40030000c561101180d07500c0c0c2075041d0284024070550340762202502000b034071300341312618007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 626859811 1250 626858561 626858563
    0x21150f03030a050a09030b0f0703061502070512010f05010e0402180702030904020a0c0b040f150e0319200304060e0d03083702120a020702131e05010b0a0f03050603 72
    0x582d1145a003400780004614144501c43c03081080910752148207810746062a481d01d107003441048070000c0129241600228042034800c45500958001d03034000c05034682040180803203c5c030700681e440003541d21a04a11040f11650103103a010b8150320f40341111f0717440e10380100108c800d5205c41c10f0340c0ca030000205000055501004890750100180e0340903a031400092011181072903840800341000c01c140b401d01080000e1100c00302d161138001c210307628500440000d224200c9003800d00514055004001104820b0880301301c081d044003040c2400d00c0c03c55400f10200c0f400200310a064031803500001014131145030000e580d4940000141e450401e07003042d0ba50081c0030003101401c40320405400c0e07200c507428155034100c00003812500d4156811805201032104001e90003140840380e000100a00052180710103109a8070517580040c0041000ca0011042d07200501025030382c04068403844003d02c8100200303004090080c120003c00680d24961023000503c10044e0070205070805082c541031000d1954 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 626861061 1250 626859811 626859817
    0x12060312190c15060306020a021c0f0c06060510120e01061d04022b051b0121020403061d24061002030c010e070f121203090821150f0303 60
    0x1c2682802440002079052000c1003000140543c2c0d01c5904004000c810007850f40c010341010710140e021120314686e00003010132044020080080000d002402c02985180300d03807e10350125014400000d10561503401041c407000a92442c0008601ea0443c500081d610307610801800c1210365000700820707400c04c1000e401041c102c111200f01060315001003001d650b2100d40c1c00001045401206224040304000a461890306070026640340c01103440f00741416150041c540350000c016550001c5409118080c031080180c0341200e4840642e09000c003100141117440740e01420204010f10a14804008902500c1c0800c01c030390500248202a84100090140143c40341e00014200c1d0702c03200d20250f11104a10b18001c144c011462503080641202e540d0304d002c2036040960312209000b60740d05403210a81d880188040030300420407100d0b0050302c07508030f110b07501a4111900c150140703850103d01030042910600c405c0c0340c0c0502d440841d0309024802c100c00400407140c51054401c03888003c0d0403c00203840e40 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 626862311 1250 626861061 626861107
    0x90607030c03152402030309060406150b0d0906050604090f0303110913060501030b030d1b03140d0e010c030e0a020625060b0f060301050d02210312060312 68
    0x40d201c90807807034128020380040021041c0c50360b00d4520300b0b41c1c80444491480501401080460f11002e81c074059500c08001c5a21980c01c0e07500511058440780d4408004200c10f01e5040421000d0f540003148150083d0001e00003040090760101e00c4508604040048030320241c0040e1240340f400c40008000f4502c500310700d002d943c1504002603041540f0240d00322611035044116444000c0e2400500c81f10242d90160060310000e980030020a22b00e0b00030306a40d00c2107038862001282a18001040b8030100d500310b003400f94464688203100c1000855410466000380b20040800754860024600e101d4003441521120701032480c0601004940700d4074942c603880c40007000390051030002500d41804484d14200304036410b104a00541d81682414040e00a0070b81070805481505407003000d032418902141500d06841000b4162071100160354204441002c2c2140420107180b101d58006940740e00a1000c1e11410807918842152450030104140c203103910f014075501c03141d5042c06443c0c01d4210b9504428000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 626863561 1250 626862311 626862317
    0x20c0a0e0105210102040825050d02240f0d0b03061006051b0703020a1509060e09150d0203010f150e04030e01050304060b0301020a0c020910080606010507081e040e0a05090607 77
    0xf10202c400d95030302a1240e81c02010203845a11180d84406d0040d50b10048190807042d40e6684081d1110f04110407800c528401079800b40b42001101c000f45070492610380d115241c1d00ba5076280100c1d195024080d500701c18400c1032059510706016680341002d12810740d10844102007074401d10b0514101404600035811403202844e13402c0e1724040070417800c00281c000303076800500c0c42003490352750b25080250302151700d45200040d2446000161280c003030182e10303a00c0880200150541d0303407801c243e6006070b9455090700394400191049140961003e00c00c841200301ea229011490f4840c109003111140c109074000041d0b10641010040465800060141000000d180c02a5a40c8840c10100013800351588040d0341544009030005450741c0001c07600780d1446c03094540080e280d9074a240d071000d0045910941f07029420140014459620480040148a04c6005901d0a10440841c01c0d802510543c000b090f40105c0050140003101aa41500d40d0110130894180602c1c5403951900745c0340c0c41d01410107018 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 626864811 1250 626863561 626863609
    0x2502030c100203092b0e040608102405010207030201050304020102010b130e21030f0714040605040e0106020f07051009090f0e011805152e1701060503120903160303020c0a0e0105 78
    0x46c50351140c015000034940301c411100c1508095880300e00501d684500151942001d41c882c428200300c0303490046c21103030140c0103010500d146800554895100400490444d50f0b031304140559669000b660498910340508006a919510005039107070000c0c091002c00c0c03d00c00c0e0170004240700801c20850f0f90240058603001d44c0d940710810700380d40c07502800f281152400c1e404280403074059800005070044602c0070202000c541d036641e038207030703141e80660a003407645401610061299040c580f50b10788108100d450540e8032203554000010886038a407a442f42410744426002d0000e00c000d0142a034a020302a00b409040082a51041d81c1c805010f260318008050040000d01a5048030b1501d03c0040c224418074940500130080c0300d01165181e010380c5007001c0c03d044503108030402c1480341c0000d0740c40c0034009080c801e00104000d0f00c1a0020b18065034142300340590a4910340d20740c107000c80118030071380062450b5040300b800c222109040e44c0000d4a821182c2004100070f5a60900b80c0254080019070004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 626866061 1250 626864811 626864837
    0x20d120c0209040f02040b0105120a20041d0a06051f1e080613021806030c040504061e0e130b0709170703020909062502030c100203092b 60
    0x41003100c003a03001c0d600500030000c00041c00f00400c41010b11a108590411090540200541e998000c50100b10031000d20b0100041e0a020030781d00111004003064444032040c649030103a00381c0c03680280c02001200100c80b490301c80050117498410b412105080f0240003103810b0002144240301c0c0d428000403036204031084103155034092440c0200c40300b005521a180d2004d00c40c40174103013001c15038a2602400700f801c50346039001c0341442030b1205c80e050610030b144844444000c010b010f800150112190407400c200008040d07545100f5039000f450010007600d06481c0c1c103110483c000c0e0301a4040a2540020010443c2d420340541e421070000350b00c1305803050251641d103012120b84195407c041410300b500002c06114082c00203885003180e20071100d05202c3e9440162040d110141501c40c65011124030080d01d0b91391624000d00c035090b41d050310403282030101c403100292409100182103001180d000041c003100090500041c0c1c006280d04c21031900c113200c041c640b080761004505e05401000200301c4280 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 626867311 1250 626866061 626866067
    0x6051c1e170301030209090c0a120512030103050115140102070509071106070806041503020f0f120601060507030e0d111c14010f0b01021f0c050c03130302120307020d12 74
    0x1482550011040000c074403a00016480300d07482070006078801c0c0304030000540e2460000030705200e504006001c2c0030350300d440d002c1961060185000700311080e01401d42858042140080554001c0d030007000040340507801b20100506aaa80d9008039801c1421200c0300c001c582d800041c102f00302c03001030361a1003141c3e40d9208211046021441140d100740152814850602c0c1e201c09c1c00c0380100c0b0200e80c00c1000d58010b0b200700080c40c10300c0c0310003504403000155050091500c2d40c184a075014003c0c01a070140e82211849509048090708403101081c00843c00506240c0e0000d0400519101030740c051030000c0842e102c0514420081040504c28a0481048401c038500a144a25110f40c0b0206100b20b00002001d0135028110910400c0110f500e0409080c000e5840003805000000c84010302110403040c0c41244009042158404018014200034000c51203004000502106005c40070b9038052030300b9807040100e1a0b4404a80c05107a91041c84110b001d80d03500700603108e402c1d60060024000a500344026 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 626868561 1250 626867311 626867363
    0x70605030601140a032c07030f0303110309070812030f13050309030106180b03150a020306370902030c0f070f0203060403050301090b0a14040f110412050106051c 71
    0x46041403001180038511181c05d0f8010389100c0c40080441c44002041e01d50045140d05c541c50009055030102500b0000b088000070181c030841c3c060300c0e003c1200750044c001001d280c0d00c15600d02c40355a10048040013587e0040c402071182c8000c1610f4140745003130803c1a250b203038202a03c8000d0506036042c503c41048000c10413140801c801070002d0014503034a1074109aa8441b928588910f281000c1c44041c5a18000c00e500e0f50b40c9000c2c181500e01c1e82c440104403002500010040d9420400e42c140f508038420002c121409071840e41080024a0350084900b10b00811166005040311801402031040500710741040d156030425514860740c035041039040004d40144600ca0294042c000d41c4148030a26a00000540c141c802c0514240501305d1000b040c801e144241d41700700c42c04840110190b400a01d0a90044c80d0840e0110001040b0103001113203041c103591003684066207050440c6400c1007000002e0040e000108000c9a0f00102c140e0043e482810240380010010011030907104581c0d400c440805d08 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 626869811 1250 626868561 626868587
    0x80c06120f13140708010b0a030305030c070c030b010e040201170405061b1309020403170c030703031a131a09090a080f040909030201020a0e0f0a09052e050f030d02070605030601 78
    0x8944444210f0071101c81d200c01c0203000707221055003441146011400d00703001c808200c1354580e481604d15a12a04056081e070090402100c0c0540031040000100f202e201034540a04643c042c80e800b5401d0a20003d49a0f8081c2c01454450b088410208004614041442644000c80c2d9014150320412125129633501ca994950303510741c41c901d140032071013044680c040c0c03090300e1180c94203c18400051030007403142d01482040c030000b984100f00707102c000f0f882900000350301c03410030900b000c08030f0309800052854076001d0351707100444c0d81d00c42c91907180d02c0070042a07226511082d01c10f0390590400c0521261103c1c03403e400500704450014060380e0081414045400910f211340c002c1240360b1561400038041e5211011b9940080c4a5405002562a107040c40c0c04180038020408100b140c2341454007005010010304802d5000444050210040032695209031140c84c101d00382e007925070a090811680c1408000d1060007584405290200c442e0002800003e40f1403d0070400c4d01d90b41c07000c004841d2000c0b1821 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 626871061 1250 626869811 626869823
    0x90c1403031c090209100e19060e0403020d180506030a020322140706050408030a0e03070f0605040e130302063606040c0b0a05090d1713080c06120f13 66
    0x307000b5004071002d0380402001482101c4a10094458007001c1d680c02d1080c1c02141c2d03203010038001162115040c0556880054880400070408503540c0308845092481107505a016801401d8906806540401a0008071010000d40e00d60310f0300f00b0004c10348900004140f104042d5001020130303c00107124401030030000c240e03214a10811038915058034103014102100300b161040041c081215405882541c0503504000000c6084c2412640d048502c1310a07046455014015000081071404101c21030002402c07007501d980d6039a5140400781400c949008007081c80d641c0040c40d0080000750702250340c41d003100c00c0c3c030109138035801c00c8020711002c040420080d849503e442c801d681d81100000c20224072442c0034189402550380d03201110782ca54401c0000043c0001e800300700c00e480b5841d182c0c10580743d103800b880b003400b46a5910750b41c601c00c2d54054031a18003480d140391404c0003d0001004540c3c12030704259000c604040d0070444003050341328017910350011406101e001680706200741ca1142c074440d8203e0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 626872311 1250 626871061 626871097
    0xc022d100f0e15040f1a120408070c0b130812030405070501141632100e030c03040b071e11040b03190b090c03061e190e011e090c140303 60
    0xd0b00e4100754103100c1c400d040c016004824013a4110061070251038545101e03001e40c047d6690f0355560032050307034800c2d001114104180c050103d0301c8940103029105040c602400741c801a81402d0000303180101e0a4900038041c0e20820030031001500c0820081c080312401c0c2020000e0703104180242d03225008540030702c0710180003601900c00740310f0400c0100001c0b0051780400c103040365115160310346150004490741e400c1c0e48000104035107410380d540f042590011581c16030741050b11118100f400c2d54459480340032088c10101d000d41c18403000082180b03c400d5140455a01041c65654480e50320020007500781c41140c0e52031003588151000e03c0880804025540e445030745001d6464400c1140c0300c10743d1808544d10958180d00d265040000d001800707141d00c0703180094501002d60a0741c041901c02030800741103003c4c0c44442810607000380100c2c01581003400001c40d0b1000c0c40070780b020040340110f50380c0e00348508104425012034000c0407585c4c01c1c0d400080300c245d40401580b012900d94418000d1040c1e01403918 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 626873561 1250 626872311 626872319
    0x30602030f04020f04051501180504090b040605071b1b03020303030f16020703030c0f02010e15041a090d02090a02041a191412070c022d100f0e1504 65
    0x48001c0750311903442215080300000c041d4007400111001152401144105084905001d42c01000b815a09140e03c1c000100102d46420208056a141d070714200c8800340d855043c030080120034010982d1001083c039005c0c400007001080352040b01012240542951003400c0c2109244468103e41c40145070050200c135640e04260b40a181c05202c1100c20b49142c1243c09100c2c0d881e01e101003503280840c0d8050b551407500c42c100b40c41c1c07000300d180700c1881281800211007c640890f10340b4000c52030400ca000702034949232031800c4100320028084c501c5160780500200804031080e40c9209400e44242d40540d0000e00b0380d40c1d500c02900007446182c022100790714920383c981803003113112401440400020519003030150211842681c00c090301d41e00403401c1820a015540800052010b07407584903900b89400000c40041d86c0104065803001c960800804140d428003125110065038402c100e800c0980e804d02052400c403070000d200340601802a03040041c441440e100503a144491642003103031000030a80da96940d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 626874811 1250 626873561 626873581
    0x605070804140c0a2d0308070c06090308070323030c070c14220f0f0207061b051c09020303042c060d03050a1701140315010311150403060203 62
    0xc4404542d815260039198003000c40104966415080280202c030302c0ca17041030b03222541ca0b05071540300344115183c61001008480d82503500c10045018102140d81c440301420603428540290300b00f041070102c0540100001000501103880840e01850003da98045440c4806054640118141c0e50140040148000c010111004008840c402c0080c024155600c00702e402051102c1d4011a44c4018950401019400e000348449801d070009500041d82d101e0050600040300c0c0000c0103103d1386580401c0400c2008202c0c4918850090305c00f40085508181c00c000a005200e45880100e0300d16003d21003240841032900081c40c01980101981d4542e5141c1031441188a030503480c0811038034084031202840d040c1e8102c02c900540c40a844080603840603101940ca42c0d1000b0101c204000300750707965100210709004060302920400d01420041c01c8100c080525010011482d800301c048410b0041001a2034a10202c8080c0d030103481485030641d52210b0b2428500a652004d0002d030300000400c400c00315 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 626876061 1250 626874811 626874827
    0xa0f0b040506093d030506150c03190e0a08030c101d0a0f0c0e07320c0706110c0108220f030206091612060f0e10050108120a09060c0201020703060507 66
    0xa9440c44c880c03d10041d071203045003501d0702070b500d5907009912052502c2c490341caa8401000103220704400c40c0d01d8100040600c1020b22601c03400e00b400030700c6c01c04030060245030420000d4001c1c2803440096041c1079402c50070503204c5489240400c5560b03030303500d00c401c171259030049080072407458003040d21513140300d605080440c41c4154404894100356920042020031404208030b0280c0282e46c2e410480e502511036a40c030100411407111002c1241161400d120251003000f420109a0507001e4080545801c90103040c070105000030150580209400b1026660311258032036100030055417441c10300c0d540381440c0080306403448000c0c1484001100e40c0c01416000164503000d103014404942c03031035980d501045080003442c020500c18801003410300001c90f8030307500100300c0403004100c0000d03191ba481c2e169130f217001800251850901d407100c00400649074180301c00900a803555809500c1e04510510007011a1030900902c800c0c4400070300503c3c107591080210101031b5510041c10041402d1100014014203 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 626877311 1250 626876061 626876149
    0x40e060f040b030f0a110102210d0b04020301090902030d0906050904022a06070206060108070507030f020c031b0a0e010e0103140c04050f15010c080d180512090a0f0b04050609 77
    0x20241511035442d5510010320726180d100c2843d21010305002120717407149c0030342c4a800640b2000d5100c044003543c965940c4025070007082e4800c2d000401d5100c510525050040000300c00d01030100c610410014590810211820b0541c00c03180160b503a07050f100c0c40200f0000940c40c40070223466410000064071340c0080c4c0140100595021114143d482000468200c2003c580480c00104c0030f08c02d90300001c0c045e10161041c10030340d0041d9a080510000860700d8001d82084003520009070941345a03c505000b0304007030141649002c85542c0350705055070820240010f1000410350205040c401315460414062180c0403d8018810720060803e0340402080318010b43d003000280380c110030100050340c02103400141159100d040c1c60700301913440803880d00600041c240e48940b0000c507925000051302c14007003203684100081c1165100d2500c14103000e0380d000d190b040014110404141881803400300800d0380d084801c1101c4155450b088400403820300307140c040b102d014103c03540c51718100f182c1456196482e4a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 626878561 1250 626877311 626877323
    0xb0406120309052b2009090d17010f050d0510020c060103031b0c030311030408060115020c030a05060c0a03020705030c06060f0d021503060a0317040515040e060f040b030f0a 76
    0x1380d8081024103200604004a00d400b01c078942c500c5500207404030b00e40140420200c10003109000800d000b058402c03104550b04183c6420501c03814143d2034200003144000f41c00b91040c0c180c15818900918940d982030300900740320341c0401c2050310801408210590144010010030741d110101201c8481d5580000e00003100401c4800c40d88041c00150f2103460440c450f040b648000b40c1d07603e181c5054a0000f4440d804c032201d4001000082050041004074034000c2c202151002000d144018000382008a08000b46110b5004090600080703140000d20035002103201c500c2d940e80e04940c40058000780b0640ca00140709010104162001d004041600343c80b034101528007a02c1c2d28401c1c802c00460b8240303800020340c00075408500c000c024800e0005554040000750906501c03540785d444100044524030030011000704002800d102508040c41844130f40010002424145810304582600d107110040002c2d01650012103e91080d5a80350040d418441e00a0309840305042c0c54099252180140c610a44031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 626879811 1250 626878561 626878579
    0xf0206130803042d0311160506190302090d03080708070e030a0b0a020705011d1006030809061806030a0603110a0e0708091c0c020916120b040612030905 67
    0x811903036800c66292041c1c0c01900649140c0d15a65030410013007020494459144514030400341c024190b000d04200c040c0070341c5515104040200c4201e1a0212061051000141510040056841c4c40b400c0c0c3e00d07900903816aa203000b548004040f0002d00402800c1603100038654411000d06400140082c021402a500c00745140c2e155101a59a003c114185a406520a24000c0c005c15480040160071500c070305005454041e55440c1e0f50309440700c025201c2c80d407801a1442d0024900308000c641c0e02c5043d51081032100500d1500c4285080c0200150340703001e120000703002501302e03440c1c1164090547e0000d14a81d10b0341092052075000b07005e9800211812100d649a0909038640303102c000302281d90070710780352540740e49035842152240c0300940211440d108181032b034a181d1164500d5089005910740d943c075440003460041046a00014000a90081b0507031030790a0b0540e8086046105440f05000104a1407a2140400c004000a6028903440400601c1c80300405078800304223800c45d10102c44e4440c2d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 626881061 1250 626879811 626879821
    0x190b0a050a271707080723060403060c411c0b030d09050303090118090207120305060612040201080c041a07022d0d021f122405040515100f0206 63
    0x1942c4c1c2c12502820691b44e001d28410043c0300f1072507542c80000480e090300350925808035804100c007030b0801d40080b101c150311b49a400c11429446030760340301c000d4206141031032040c022520328000004100300c580508407000e0f4000f1910350035030341190003918641f01860385503252900000003c0400b55503451003402505081c82d5002e20640082082c0c5100502442c503040001c001580c1050100b100f100c9011202c00e4001100e000510142c80d40c140141c0ca0b8299190103c10000d0484500408180c45050700703200500b40901e40a40f0941e1255082c00c1c040c446403102c0300703541c0d90b50255a0100d0260182e0b804a00e9540c03035854041c0c01954820388a01c0f80703403641031990008200e9071000c0d00406240184480b01c03180342292004104174000f41a100100e00b141e49002109215080c900c2d0200380c0d039286040d4030764203520642c050b409620054413161118000d003d1407a41040c46598480c5840c0d1001c600100341d068580e20340010300030018040041a1100a090340101c111550054014640020 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 626882311 1250 626881061 626881063
    0x60315030d09082e0c0e03030f0301030312051302091f0305011a04020705030a050304111201050f090106180203190e07060801090501060903140c0301020f09190b0a050a2717 76
    0x1d014400b131095040101c400c410000020b0072080d0310f940401211585d02481514140000d009030a5464420350740e960560802512010792424094000c03031400003000505244010400034542e4100c80040b41e540b55241803001e9080766108402711041815000010000f0540c881210802030032515964400400f041004a004403100076005801c2003180c254124415001103600503c41c01c02d43e03400746290070100711224540e0004e81e01c141c0d9210103104841c041d291206a1214040c0002e01c403903070811550320302054440924031602c0750040080b480541c01e42006070b0b4605400c80c0300304600d0303c09050480c0c1c0c4045520070400840c0100700003050140d40d501819040c1d8016490b50b8807043d1941c1c0c5c440300b10441d2410910f0550007440e0300b902080d5020f0006041246499104039142c4040f80100480f00e980807070b0a1618001800c401c00c404101c180645001450a003003c07034a520003003d05945941000c0c40030926000d85a002140780740707003024500f0540d010301c130345005130512081c0c041d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 626883561 1250 626882311 626882353
    0xc0603060f0d03050c0105040c080609010b0a1e080118140303060904142401060906020c031b030703050a080d0c08040c05060a0e0d05010c021c0e060315030d0908 71
    0x2440d000390201d04003004a042140042410310f100b0710b0444e181815440c00c031400c480003914100c0f800783d2002010080c4190400c500307500f003502213008210b1316003680006500c107050303480cc40c42507130b01d02240541280302c210090710081c100640207004c554180444501444411074045461002c480520b9850309000800c3e45c2c460782c2d02400c041e465489907142c000c04415941e1141c07256104001c5808410f08049100340c20814500741644070550414101038614a12500a0403c55010782c04588680d84d001651505400354100528540180840800d041a425400203000b61142c890050100035001c3c00504818003000c00800028100c0c42c003c85000f0310981e0003400f00d0005580a0281d071620300014203584485007403c0d42010b1891000c221500d0540c1c506440c5030351340d078491411003901480303a64040788641d581c1c685003044e180c8005d007140358143c08483c020715012000079028111624280100c0c50014103d85615482d1100204020600c1c02144500e0007808400e2032140c050b0058 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 626884811 1250 626883561 626883571
    0xb0a180b0c1c0e060702120a02190218041b0902030114090a0213060e03100c051603030f02040e090705090123040902150406031406060d0b030a0b13050c0603 69
    0x1021145846046001c50142c01000741d4070104501e400030000c2c0d9040303a200c0c0c101c5484681c0054403140c034001c54003908002c50224003800303822003084001400d980c045070141050700680545001016a80049507540c0c00c403100411868000409110a00c941c82d0041048586a90300d00003c0135115003a00007640000c0c1f0a0400145049a40b401d25103017010913035602c1003c00c00c005040c940f41040100b607040c80380d8070040c081a00040b010f111418144280036103200014424009000c0c00b030700080c064400d40200c501c0903026a2070303039000c05119810900b16640100300554641d0f4a60300d4130b20340d00c0c0303007910b144942d4410305000141c8c03800c05071201030480d811030307001016243e00c1810981903501c08410301139016564440c4280142d64560603150086a030b9040c56031150f08005024088684c201559030102600004010b00750b5190001c64901d8449890041900755407140400d1810a150310000d00345c031884020010541651120304000d24003a0f0101c410080812302400700d40e11080d29 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 626886061 1250 626884811 626884823
    0x304141c02060307140307030218030c0a0b220f1806080322030b04080a08100b0f0f09040f0e28080901090b1630031e090b0a18 56
    0x440c0c50058544003001e140d1000413420030014401c0300c00d00c460385582c011540000030035404102c11107407145a1444115080f004e17030042a42180d4180040d141035018401d40c680f001c40052100101d50604861040c2d0b1255004817500f001d449001c00e041007400c9004109403103400b030b021190b00c4089405080304664954010b185446250078116000140741e02d0b5403e06072542e040000300140700d41503064030640c001c0c9000381e00c6036250000180b0148015100386c1c0f46a03a4210b09008c1d4455107405c44001130001d5440c103a49407000d03222a507140c0214900079a11078a010750202a40702d468202d507080c482850180c4410603000013540040031700c015140a402e2180044403400250050002c0c10b4000d4141000c02100384e96280403102d983c00010b407070341130068042800c0c082000c007590b2940c5030030088003c1f0311450040c00e0201a600a44421082010389074690780d04d801c008900d00800c0a07040382c0c024805c1416030304181c10820402d0310b500f00e040380350664107544038405020340207850758894 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 626887311 1250 626886061 626886109
    0x60e040504120e0a050312070c0b070b01050f040b1c0605010b2b0912050c0c0402210a0608030703320708130b1602030f01020c03070b09031209030414 66
    0xb070011525441c2c5280304a4010f0000c80e00030406550401c5101c0d500c05284c4c1200f1307666161454490629540740e4842404130205020f00400a45156806410740368143d03080a455990380c80014042c001c88042c160b080030700e00c4000d8100b1030003078880c822040c0c0125030520459030f03200a07110003480303000d141984410b00c040c0c3c82d54105080401d4018071045031400400d900c030302600c85e01c0c01c450054428202140f0001001070803220240715507601c0b04000c9400b1420584031502c03c070110396a4821110640c00314000154072040250f0200e0050450913049989902481c640509540c800f0030031b130900000d00360442244001d410300e0515042101c100940d0910106070341d850001d400c1820001c1c0908060b01011480c01d1012020b0400e16660029101e09033036a0300600d403d08464100d90b00d010390041005000c134060004c01c0302c0c0116802040c6041c81c1c0d8030b0f040090300754003c1a82e03142c3c4444030a0144042007c0000140c41138407240807100b8020210b002c1044000c0010b5a40280001c50032 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 626888561 1250 626887311 626887343
    0x30903020f0c0f01050309010e0111181005030105040203040c09020a050c0f0109110d1e060b010e03150115030e010c050403020a140310020a300f29030f0102070606060e040504 77
    0x105d02440e00440c1c942d002180038202c0050650070368008464100e00c5820105454103109083d0461031520001650342e070b100386d10000d400601320710050041f41d00070743d0000f022400300309040002d20001e2044810031500d40040b810b004241d9486034207004d44a100b21740303107a581d0010600c60009030235800b12254006e1000407003401107000c510702080e9194907030b0684a20000326011001c080f95807090000182c41c120300e0b03001609140756400d2440c041c4d4020b40a0b03041c0000703001e0310036064555007456010406401441180600b030b650000000c1da5007400808420640c00c2406801900d200302c1d0000755641e150b9020f40509034105041c0383c0c1c0350340006c507940b03080900c90740204010003242c5010303e0456500300c00ca0844100c02e100f1420141608242c26a00c0e8400780b0031407048111100c014400c404018146004402c803455000695030a9001e403460940c1c0c0802980d0002c0801350000d640324201c5051090003402280304100110300c00554500c400d00c2c285c401c9038446d0754424411200d100036 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 626889811 1250 626888561 626888567
    0x18160612061202093d06020c030a060f021c06080f030a0c030c02010912150c030606120b062101060813020102030304030c05071e080c010207051003020313080a030903020f0c0f01 78
    0x10141489100b440d51040c12841c40d01c441045041204400707508100c00d2103420285e44030f101043c1d10000454224940101030b0f0341e40441d20051842c1c0080c0d02107555074004100307030004d05c500c403420746000640600d110013a60241c0c0211044840c0401621000c041340d00b41161284120303039900c0300241c2105d90020004e03000740100001c1d180180743c0f0101e115207901d0b00b000b1503010342106541e14138403040c90a40b0b22005005200110180b85400c2c13104500e03150000c1c0c81c0d5500740c0da150f6078194071880006a5500d40c402580c07500682022441c0c403515243d40903039107001080c01400001141d80c0005159198082200040a0380c10381c000c40c80c40e41c0c0ea440403207000c039022000b1125805100b000040d402c5104081c080e40c140c801a02e5106549454041803a000c2d0002c0554155004030400704803640d5910026004602141005643ea40d101408030781d8160303002400401c52400401c1088407254076034400c00c5518407903000c6414900c00c0c1c5e101c69507070b0707403009803070b00d0b84440a01140c000b6948 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 626891061 1250 626889811 626889829
    0x40f1217030613050903070b0408090f030f19050c04110711030109020d06090f0501020f090a1712160f03050a030b04050f01061b02060307080709060f0207090518160612061202 77
    0x1170007403e0780d0400350f80d55180140080306550a4840d81d07000304951401d460280b0100b603440d5002c6000300100003255034200d499103c443d408000000f19054644188141404000301c1c5000c0288200702d00c41c0380300907600640d04511015518032103852660f0300c083c10140f154000583d00202140c010402c00d41d140702c050003944104075820715240440c1d01c0040c05c2400500307801003280148039200c0704400d00380004150181d124420089000e001e1131810100032409682c51409404203603524420b920b1000841c80c2030600081103d40ba00e0300c1401815800b00180803c072460380c0c0c0030300504800784100001d503142030b18010420200c14004012240c0915406406540040390688010240e0307000600103400440d8a1400301d201c031400c20a0302d41e03211b0b041384041d00315802c180b14002103062000356684e81502421821a80c2e920100e0704442d00c00e581c030112070341c280d02143d18440340ca03420407031040c000e440b03101d0200710f5009500c14003034101c0c040c01041d030304829182c0440110079020800e00ca8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 626892311 1250 626891061 626891071
    0x70216060203041814010f05030d0306120605040302070b0d0221041106030603070f030b102c060a03020d06140c04080a060b1908010605010f08090d0c08040f121703061305 75
    0x81e40d1070010000c082d8880e45c10078020a01040240c0d8428900f20602d4140019800e150040524040c0b007803021240c441e00c03c14189800076030001d1956164907090b8070b81100b6400101da0442c001c604008446284d40090880e009a0710100c0301c003040c07914106004501c20f4074014020b180003804c003507040c10000040c0d58014002021240d640c0d540b03880501900d0000e420644000c500442081010005183c0c0d24009040781e0710340300c82c0859401c04402810290801c0c440c0c5102c5c1e40300215003a69610207141b005141c00806613060f141607460039000038480314600b0f00284407518005070b0801d1003c02038400304c1d0182000360a80552076036030301000384041420300740d0040b0b042000041903004641e01c1c0c40a03120503070002500e14200702c0054042038144804804009001b002c02c01c01140120b601c00445609042c607804d64502031070241428062908030200b034055010300007421440745400754065078080c002506403a400c0d50b501c0480340c802102c0315030f00410000801d5001004a074030080d800 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 626893561 1250 626892311 626892359
    0x9040213050406112208030f040b0703140c0a060c020304050d030809190b040b060405010317070f291b03011a040305100603110a060e0f18070807021606020304 70
    0x13100b0007000000d035170b04441d4440b2000004c2608503081240a01e030490301601241c4025410034460982c840e22612860140040000c00480c0c2013003014012544102c0d803c021040380c6441c6c0380c10081c800c6e9180f60002d0203030340d01424421050442400030080300c09075000940f07d418124019141a11181d901801d00b00240c4111481c0c11800b040c034400d074a070081d1007080c410341282480d003442c1c5210301000e0500740c45185040010000580d403900200101d0115504441e03c401050815201031204248041d04608500d10b50220b841d0030410441000844000c010300d15466400c0707203580c1070580041165141da004c000500040135041c62000600c1515003003545071031303100d0b82c80900700003a035031824034a103444000a01c2000f500368256040800103a070b00850003498880d0040924021041c8640101120801400152949035141d80318aa80e64001642070410140041c07a140c0205e40359401406401d80c1c0c0b141e030342d00c2030003008205c500582c011414241000c1803000e50402c484e070841c40d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 626894811 1250 626893561 626893571
    0xd03020c12060403080c0906120910060308131d0105010c21050d0506100c020108060414240a0e011a0c100902010e0111030708030a0207080d050a0b09040213050406 72
    0x12655501d07201c1189040107006005103040070314010300340010240c1951103c800511903402e040d02d0f0841602d0f03403420010458076498803441d102d1410006041d031140401800c240011040c001148024004500c2000c0c2140c4941d03a10402e00c034810981d643d00d004c0007604800100f02c02c1d881748084400c2e0320301171207100c107400c04c20b48480c43c18828010005804540d002c15500000c9101d8491954480b009a84115084002441c0145100d0803190000c2c14051113002003911512141c0c01094500540200c140313250406440b4614040e040c0c100e02a09249a480d4000c146d0404089110031a113240a4180a590805402100d4003100d031000341203c64043c014210481010403041801e1540503c0c000360501141c00010440c004c400d008074180480080a00012540001100c4080d0380040149450b9150078400346c029124860000d00190800709940c14440070350740c055030144110303110070130001013000140404150200c07400b0b54009001313001c80800e5040d1b0b42103039a0061080b44000341d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 626896061 1250 626894811 626894833
    0x2a080306060309030f220b07030804060c021009080c1b1e13061e0f1a0d150329060114030a0e010501080c0301110f0f0f0403050118061b0503060d0302 66
    0x2603000095510365000707010411ba0840100201c240c0041c10b0364030310440c6404002c2d180903000b45d038052710040003191340d4051900b05600c00c1c0501c0c1410303042c3e6902446184110304003882540c1140111180d580101480d200c0c005a0040c0f00d113001d00f4001d817010011401032103c3c085a00c841c1010641c014445980c14041d62065115803000f40c088200c2000202e403161240c5c480c407019a40240003010780002003031040d1101c50104d40049900d00281d69921040750756150041d10341000d01e440c0900e0800000320400002c203a26501c0d0280d01c405070030300d080c00344a030103217030350816940c05022800945014940c00604c00044d603001c0e03003042001c40d03423046c0007141c3c50071110241d1058807d60041c440e600303001d1a0a000e443d0300c150142840505100c17003506101c4031481031f074240d9402414000b03494080c182c1d030a420b403002560420002c200c1d0510408031a04810385c0c081d0100c0f8428900100540d1800346c01a2144d00d40381941e82d001c0c150741d120ba0034080e400300d815030b09609522810203004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 626897311 1250 626896061 626896087
    0x60c0f0f0c0e0f13150b0d05030310051504050a1a09090c0d1103220201020f1204030201093f050a0f05060105010c0f030503040305040909032a08030606030903 70
    0x203802804910000d0030246015203d030a89404007824510680980d0310581002c59004440145807000000d40003401c545134000080b2414100103004119000203c10010503079108441101242d2040d10360b51204507410500c45e03000d228900420b54000104902400526041c511003116900076198651500101d58000340da107100840358008100300c00a0300c040c108016000302101e18a4201e009401c60420342400305200500f00103111b4903e43c1400301c8003c0d68401c01000071b25034080820744d04510100e100c09a66a071180c04180c0c003103076604000250800c159148402c83d003814140d001411545103c40480c44840c685a0288151000c0320400200d5010b0203449602440703002d0070b50500c2820724200b418034205074416410b02c0b841005441c0030480c20310b00b0300e0199500d880c2c5960707a6a10781c90b083d03c1c2ca010380e81240c40300c10310f803041d141d08254100713646403900010358002404940c858159a8114424031000501039801030000c01c60f0342c24240090354100012000366404c0446000307101e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 626898561 1250 626897311 626897333
    0xb030109050a02010f17060d081b0706171e04021513031407030b160203041511070b09060a0c0503040306022808010b0702060307020a170d05090106060c0f0f 69
    0x20344039a000009907108641e00719038501000175403410104040345e41c0c9041502c0b8050000c3c0440d00540c0c4414442d810003400c0012103440300c0384101d00034991700130200d0056441007603024040106242040a512041d03d00d50301d184100b017981c01f480c5401d078070354254000c0342c80042c0040b60803140000c005410402e07220060b02440c1c084100c0340110301d285050407c44810302d0564030391aa0001c00c02030000c244003c1d0025441498040451505440550103d14501c5075602408000305a941926030b62036205030b543c1d41c1000000f04582070b0795161500e8103100d204e0894450380c81038042000030100d0b4000c00f0900c8005c0e002c0c0060741e0409542c0d803540f078144ea101541c0ca44012a40a56480344144c207005018103009880c41e20629a60511101411500c6940301c04ae10401011000841ca948208a9903883c1940302c0391380540c0d46284604140349402540080319020f040100180c401d0005200c1c003c00c0360f04a51380c4814941c1180c6900c45009140b8105480b12101d00075981c020400280007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 626899811 1250 626898561 626898563
    0x1e030c060515030c0a05030d0c0f1b050f030c0a062d05072009010306050a0e15060a090b030d050a0216140103051e060913020d061d060408120a0b030109 67
    0x1e100d2500380c500040504150513440300a1089500c028144210340f00040c05011010706810002c0c44c1c44a9803c00303400100070103000802d000b00704028a0303031750a40e2640c1102141c40598501c41441d0087c4105616010f11818441c0c0010078000200700c014425182d20024141c5503c5600d0210307400440540b0200d00c2880b51004598006440410099810301c40d009200090b0041c0168007100750003e210b40406100180003a5101c00200348101030a0303002d00b079012a040e04030341c5d004000f200d10440382c410403292144100c02c503190004120300701c1e024440745000300074040c003481c0c1062103050380c003500416080c0c01144a00080809480d003241456000352104841700017403242440001015194014140c00a981c02448408e54030203c00b01d9150300b143c41140c0f040784a035105a101c426001c0c403000040c1d48000303500c0364401444400d5100801c40014000f008400c40ca52407405651020141c400030401c090400030030400409115410303400002820000c00c0c8001ea500010303080d07410f0504 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 626901061 1250 626899811 626899831
    0xf130b130903080c12011203140a09090e0c150a050c12031906260f2a090405120c1231050d1106070611130e041e030c0605 54
    0x500302051503040348909030f014041304821441c10301c035000000003200e0180b2803011380049940c00c2c1000c160099401809005400e25401c2d2504003100c0028583c1038507110b04141b0600d07001c08444030680c08540c1c0d901450b000380c020440080c0ca8a101c90099002c400b05004121052200045011040c004018010f00141981d500c034181450039400c1003803466409000355180001c100304500c020001303420030401c0c0450803074000d08a076030307400d00b0112440c921501c0c41c0160420b00c642d40b08045038651540e000c11619105410f510414007c03c50011340f0081d00551141801c6c0105020000003020a01c841500380c0d642031140c2c1c18204035980001c1070032003080c004240c40200b0500c0907201c0d0805841004c0764606150321f0880480c0300806041c2029020350102c030b0b119203c0b40c451a00700c4490315801074007088140401d040c000c503a0f421001c400b821041d1781100c0069003000002800c2c0c01560441c00c40002c024a0320307070704000e4046001084003401141c3c146540031507028400c081c0f160000304 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 626902311 1250 626901061 626901071
    0x2a0105040807110103053706060c061a01170a06030507030b070f0201090809130212012705010b1605150f011d040f0b060a120606031a060f130b13 64
    0x11400d440b030f03121000c41150400d4a49410000012451240443c1d8649000c460942d504000701882e001e1141a8030590300e018140b80c000580c00741d01065a1404a0040600b0800d141075001031a10080409405c58002452039007a0440310200c021150b030031000b01c41001031090b540f03660f20b6051000390380c01a00c2104000f010070503119040840a40c11080c00d2001704182101c60b0707221a10f40c060100554000e2061003010b04050703596038100c0f01920b0078140300403029a0340707021403910211200c0c03918000110740c914074000a030050007014140c0d2510a0643e0800c40e0804c0c0045820490381801e4540e442060032018190510402c5603004246885000c26503605100662a40740f9071101809002a502c81c1084003041040340d80a44650384030700c81c40d4154446000251031622107070400305002035a00c85403003c0007001c1c1d101100b200d118500041400b6019100c0020250301100e02da1b422a000340050b04039072908406005005020110015006210720041545250300c812400d1815941d2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 626903561 1250 626902311 626902313
    0x3070303050135150405030a030c08090607050d0609090303060e07020d080a0f0617010213050f060a0c0201030f060b030a0506041b0e06040302060c0606090c0a02032a0105040807 78
    0x540100c90143c0038914010360810744030b003c148076520b403060042000e440e403152240034812090068851402910b0703240d0074281803904010340ca0b41d02142055012030710309140c1e41d86890203286000d02c14500c0002030040c0d940c0304082035841d94001c4803d010859640c0d00042426040d903c501c0b92001c0c000e940c00240d890400610350b0904501401101c1954410245558255400140e0740e40c010b10b00800416582042206500540702a400400400fa19050f000040010560141c405045c000c0794903082c0d40da89400f031280b00011800625080340301085000c25680c0221200b411080c8185030008042d1203e015041c2107810580140c640f45500000f8001c1c650381e80d001c0c071900580121030800a605690814184202a510f080014481103168010b00c0e6600c0c3c805071401950080c100c19a1000ea0004950b1164030803541c85101d041c2c09004281d00c00503503400e40300d5811258000354900410f40c0c000b0002e214041301c8a80714180e213404841e030507203403c0c003c460003244074a51a0382c8a10309 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 626904811 1250 626903561 626903567
    0x9020a02060a06050102070807031103073606060903060c2718020a08010e0403050408061518010315270809090717040b090a050601150e0303130e220302030703 70
    0x2e070f50b04c00c80c11940049014401c00300c0c04a8800d0840e0380c441c4251a40c001d040c000300c0d00304540c7e58003a07804c00100000485004040e0141c1150000f06114550b4009501d454501d04071041d5019050000700309010178800130380c455106410f40011410030070449000d60030460011721144200355034020207104104070890340b10551240e1001c1e0b180095042100e4000700030b044950500ca06109180da90340400d080c0741c01034040ba400340c1080d01c2500e07013526203c400a003100c208843c8a0b8050b16100c1e5540440d00843c80b48181030b6a80140126202644200d02d000502401442000c03119030720b40b1828811840c0e0001084e11921803604151105089002c00080c914000c1141d414800d0200c8441d8007460410801d6511552011802080781c860612043c030348411b810004099108010000c2010400d42441300310700b1150340c0d9265110201c1c40c05040d00d9000701d010034003040b8103910003480124124980d0b82d91081e82c445404030012120003c40d5135441c4902d1003600503810006605044c194 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 626906061 1250 626904811 626904821
    0x109061e0c030b0607032312060f12151b030f150a0602030a1b020d0c050406061418060906030109060f06090602300d14150d0f030909020a02060a 64
    0x34070b0404000402c80300b4041051031140507002002c1105d20344032041c40032006000f401c3d49186401801d40ca030016100060b40740d07c01a10410b00c1205081c002150914141c01c170352010080c1407020301480074285648961503000902651a0b02101c0310503c1400040b180c0614848c50b50201c00058170b080c54007041004000703003080e4600800c00350405204560700003040300e0080c510b0f0720300140c0301026600d21030594442107000940c00b9400c03e1a81051000351210001034880445003005259982ca82c1510990500c40c0c024042190034024021940101441c1d004075100142c41c0f540341031740c110005880ca52090b003201c14510786c3c68901f401050801c0c00d01c04050304c1c0500f024141c0c9030a080029580d4404070f400c90300c0b0300d071440b50a041a101650405031102201380002900c03101f05403680c3c0301500003482c000c100c220300100040d0f680c032145403c1f0b0109220140ca91481d081450701c42c0c00404a494030305600f0b01918000c0096104810303c000c001b0781403c0d5010b02014145400c001060b51 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 626907311 1250 626906061 626906081
    0xa0c02040525050307030b1c020316060c200306040b07020607090506040b0c07050a0909110a031101050c010e030a092105061302150301120c0e04050304030204090201020109061e 78
    0x1031010314502c0e00c19022030b6403032200d107a0415603140d80d01c00d1002c0700541300600099810208080584040e0580082d82e640214400c5050b140c01b44c032807055904400141d882018002a407444400300070a0394094040c5100c202550240c40d80c00400001c40e140c4801990116140511402080460781d410b0141303580140039440c00c007a03a1752504000a00c2030166008901580c000000c404510090401c20340780100340180642f200241ea8410100080080e900f080c0c0f11547e840c0905040c501c1c11041d02e909403075020481d600c2c441d1101c001140c42d03800800d260b00c0b02d507583c4e0b450104201010406012101c0c010303592102003a0034a141300c0c0d0464a18004102d1140c41640d0318400540042b90403984681c2c00d0008824007003041c00000c035406542c4032101880e80b0004008039808183d00c07030812a642c060813242181c1680c400780c02140d4041194050003d820501c0244010702e0290800b1020500510010640080c181c5480b0b0480f4044507101c40015045070b095446d440c0b140c05084214 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 626908561 1250 626907311 626907331
    0x302040c08010807140102100e0a02130f18170a02030708130302040c030b130e0717010507090b0c0a03080601030906020d09021005071a0702070f0e04021e0d23030a0c020405 76
    0x85e10400020f982c0350b0405001210183d16084c2c81c9445103c01c03c0108111a00107020240310031250045900500400010303c0f0355a05060022081d040180040e4140a9206001054100104000b40c009810580f4040114082000f2403804039001d8030203023516130362a60440c0007440c42c0d0b20403c001c5904602d0680c05140c200002c2144695801e880005901c4000318080740007440060007904108668001e010100300c0c80005840c1c40c801544468881c0c5546e484091089031504440000d6009100c200500d6900611109000a1180c40c2940e0800418100823541c5030080c1d0303403232050307030070004440603040d60701c0341e0340815483c012420300302c170b000c403400c0c198500941c17074651941c03038a40d070180c02c07407541076440205620620800c120300c000c2c40758a280c40152900d0b00741983c2860001d48050303221b01c801c4011501018451141400f200c0c2c3c0007070611803075484a07520fa0305240904800c1c3d120041c10740e1480140003c0900c010a640d0095542c2c0070703c00281c41c8104000c40fa00030348170f4209 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 626909811 1250 626908561 626908589
    0x81b1005100b070f08041e050301201b010b22050106030213030f08070515191e0e0705091009050a140403051b070e04060c0f0f0e01090302040c08010807 67
    0x720b0581501200c1da40d03500100c0381c01c004491414011050311499003e2011a00300502e1881c1c46000f05050b001503601c102c00a0000c7ea9181e050f0804460000c4c03c6c075030303409200300039280c048102c006200d00c90709000000402d03d80c0480d070009002005550303055800081948020f445032007180f00f50360140045040440c20040003038034a00701c0300305600005009000d40070910091215050a42d041d29500c0011552903444e1070041e594001d90036142000358451002d4803c91480303032401540700010b258840c80f2003d0441200080180450a00c0c00190b800b500c0008584c903210320f8030b4640f040c081d100300c800c0581c5c5840c29460444800600501140303181042810a00d443c10703041c20382142e00740c07030700c00d841d01100d0300d00700108080303c1e00c904030b240f250700c4002605001001482d0b101e40d010b01c904001c540d5101c00f0603a0380e0f103045000310b000245c140607103140c0180110142008a18189000482c2607140d6002c04c045403003800c4141d01107091000100002c5104210b100045c1041e038800e900 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 626911061 1250 626909811 626909819
    0x5070318060c031b15090503090a03080912010b0108060108130f080a0f031e05040c18050411010509090105060f0f0313261206042304031d030316081b100510 69
    0x7507804000d05c07128030701a15000c00c42c003840420002e803501e003080106840745590756480c00c150a030313028500b45c90140c00c540714000a03041d410b08c5054100c54040c0c403181080d43c0c1d2407004489000004041d14070500d40c110180c1c0101781010074505a5501c54008195100070843d4080e00e440c00e000110402c142c04c1120868101d014032403240c201551a030300c00325058907580740003000900c8031380000d0341c3c1208240082982030015000303140201d0081040c18454440080111424826942c00b0fa4004030707113400404c41c0d41461801032481120341c3c048542050541304040700641c0c0140c1c3c41080d0824010316540520141385981070004001103548401c05024920b500c0c03580c06a8070901400c4056071001403407944030394104407940110844198104500c040600e000e92b041950190000360144800c0b154205444c5100411840c005000710b0030500f40083d0700101c06100841100d02c404144100c1c00640c1549415074500040200036020102c88800c410040340c90081010044c1290580100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 626912311 1250 626911061 626911073
    0x9060509070905060a051f0519080f0a050103020f0d151d0c0604031205030c0f030717012c0408042103110c0d081803070f050405061e0105070318060c031b 68
    0x13034441074107c0505070090000f501d450088608498803509400354468440340d101503040d208101101c42c0e0501500d560680030100c03002404025080310101d501c1d01d900d89003048107243c03001c2c480d105c86014041490881c81c290f0b0444c00f034030301011089041d2070504010034883c059203d1025200c26003418515180c0f8517821543d900010107000001000c600b42c00c2d200e20451703141140041c0c161f0744e00d003015200140090584015100402e0003070001003030382402402c2c40c44000c11200300304000203a0030301f040b92074000050000c41c0c880000308000242491a051501d40d05d1002656800009006c1c0c10042d11000f85200300c6046604550002e00ba15a5840001541e8540045205843e40c40700050b01c00e074050b02100140d4103100d501720005040d041540b106007552016102803000c0d0b183d80c0c00b0b000162512001120b904404a611840154850409441d45601030b02d040c02030000c0d035110f00019601181c012a002a40c10303e001e20074150081003441c5040000071a03404542001d490301 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 626913561 1250 626912311 626912329
    0x1080f0606122e0c1125050409061b050306150d0f1a01030b09040807080f0f0f210f070f0306080102180a0b03010608160309060509070905060a05 64
    0x810310034a040d194414040300204107207900c01441101c404040035040d010b08400000d40c01c22801d8080c2002c402c0b00c0c2e11171003442d1201c03062007414001d001090800c4055024071004004100003217542c0c2000091666450050741465030003080e001885021901c1c1c01c003140e4094144240500004005002d005d480310f00b07031011000044480c458607640d80225a40140c58039408182c4043d042403495103910407115068000700409880c20042d01c201c001c24014134810803100036240500900c02203010691902c000c180111891a030300303203440c0090701d2580080e0414183d106480703401080088030f482d040c0c004840301081e20300a41303110740750031700e100d0406502c010315810030003240b00c000003040c501940088005e80311071402552510489803100c442060081c1c1440c0c81080340301c0c40054814034a8007180e0503940700b035031350320202d91b25807013400120340c0d0041c207c404250303654181001050b11881542d01400180c00544030307192401d021030050310000b400c018030580c90b03110100305e5903540e0110 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 626914811 1250 626913561 626913571
    0x2121b041505031e0f100f0f090b01030e030309070f0f0e061203040510020c1318060915090305030a1406060702130b190314070b0f0310090608010b0901080f06 70
    0xb046660365a0314005079800c10741e407102d80c0d840c201c42805110f014004601c40f00e03c07484250781c0c0003c07440c6e174604901d241c0045034400e04d0000e00290400307120014094202c6001c0803410305000c1592030400007444c0c6554421920700401e43c101e10410b1080d031022240343d10040481a070842800c0d400c008080c1c3c044d00014154500c18284014001c04180c1d0900c00d03500280300040c40e07010080007480b406900c40340c0c41002030744543c40910141501d078419128038985491038003c90340c00030525130384000c005c242c403440607150002c14040d07a8281c48041e004000d01c56120f0795509440c0e0510a108006490b800315081c1211130b0b401d001c0101c1d54640600341d6003407030307011030b45404c0310480400010f005018030094240c02c02c0918500c4051245600855002c4911415401c5840b40002e81003e8032442c69000d4815410381c00c01070b08070b41c54041c41c080c5400c80746007101c048105a803980b0002c2202c059600c0038900ea5101e905001c114a8905007050043c94030b1005007a80f00d0941c0b80c241e46500340245 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 626916061 1250 626914811 626914817
    0x120d1b0e0907030f0608010c0806041b050a02010608100e0c2b020d02030607080f090601052d04060f05011d06030109020325020c0a082b110102121b0415 67
    0x3001071030b0b003803080e0010076100710740240c200281a01c5015290183c8070240002d00800d2502c0c0202e50141454412503c0416801e01c254003003101c441c0c000c0380d40b0751003c003c1c0c508541d00c0d92004039074202c041c488c003480e011410000180c015011400d071800c0001c1a05481d10607600351055500041d55080d400702d0f10b54054130340c6484c91100303200140840300b824102a400d4410801008281600320507050700ad60596040e4070500e640c0c58020701d6441301c090040d2500111403080c0c10a1100c20b05440068190034000c8181012140f00d02041c100c0d20154002c005c80c120a00c402c2205580058283c81a030707034607071000c0000080d5040070800500c810311580d07007000c0c2d00100180c1941d600341e01000c20905140c0010198041c10380c0001d646100d03031580c031442848410f80005000b00005603c08031020044c265032a00350010403107400c28400c40c083c041c02c2c00941d040091070144288010240c4210004d0369031414100b204918814500d1135100c03800c1040d0401082c007034031416540c1400c000100d86 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 626917311 1250 626916061 626916079
    0x90909051f02070b1003111c06150e040b060907181208040807030b0a0606050405030606010c0302010e0706081503010203010b04141309080a0e040b30120d1b0e 70
    0x2001c050000c0c4038554001d803030b000b2200107201080c00d0800426007224000c840348000703c3d007203804010720000c0008041110200e4500750000003012500858540e2171070710000814130360b44281c04104200c08403400c44118400070100b1007207140c141e5285400289a20b099240000714010744280403c00b80559030f200700381001884104400c400440c0d000d440f64400342d070307440d50342ea00c2e000710940c0d0259a801055070510174081100e921a40680b8100d840c0200109011f454640c015143c190903050263700311b549035041c01140d540104260b000a00300c6580d1240145000038006004090301d9550612076401080100b0403108800282d50990300f00300e500720410016140000e9000340d11109a4042500741110201070181c071401500b5030410540b201085844d000c41040100c5918003840f070b5000d649000108003001061840c000d44424000044101d002c03840e041a01d0200c00b130481030b2180c940026083c1d80300d54140903500400c1d40c0301c02c41d0701e450706221342c01400b9800e0088035103009040b01 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 626918561 1250 626917311 626917363
    0xa0c030c05160609140301020f040303030e1e030a03140601091512090809040e0111030a09030e060c1c022103060f12060915130303050606120901060609090905 70
    0x1440380d41c0340812075940d071040c51035450002510141c01da21a40842d401709180b5540e1909060003200e011100102030b80345890308554054000300080000c06205c0d00c9442988140b402c0c2d8000d01010446501d001940c590659080080030b4075207000385c58100812510074040c8a0f40c01203076580a0f1401074180c0740f01402c542204452026022030344130034083c200240fa0080c03003281001071402801c191000d100200040b6000ba0980e5100719040c0001c0004100260207034042c0e9000090751071103444c5c03508851046200084464001d480f4901c0e01e070f001188400202c440c84118140f03861401c0c00540140c4070400c0180705a5070101804a40c04100000001c0d020b607030b1200309068904004091000c0c00d00004c5009944500489001401d40300d040e4110754018a8011040c0c4203c080c80c2c40700200400e0350740d0032406400060000e0750401c000307000c48809076450011052041030715034000114149040401003520316583d02070000a403903d11000082017003c51050f440140d00880e0740464414 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 626919811 1250 626918561 626918563
    0x150e0c070f1104050108210918010906050f0d03020a1209080d02011505010c0203031602010c230105070e13090c0504060b04080106051203041206090b01060c03020d0201020a0c030c05 80
    0x5040d50082010780c0052505042011010319040140c1c800e803020866030303898082d056611100b00070305822601203241000e1000c0141c0000b01009000580340c8101d103442c644411810b00020b8101e01c081944a190a21040c10807a030076155004044030080014929500d020f5212804c85501030a5440c7c01003103036906074018190a0018600481241c0d040c56280f54001d000300402106201c8801070300c1c10005181d80b0503140384d10360b542c000b00a1460018800840d042490092400300d052114001c2c0c48030205105070300e0b03880e00e030b00d00350b1181001c41c8e4040505030840300c000300910140f011907054040c05444005240f400740825810004112013a8208112500f4071039100652040c205480480e07202581000f500844e20000024800c4544540421900012400701144940d0050004110303012616245804040c0180d80000380c40310141c4429904000903000342011606100c0b4040802d681045100d2072a80144021800c1188000004218070440e00c00942000140c429010a103c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 626921061 1250 626919811 626919817
    0x9200f0d0b0a031e02030c101202030a1b0c03090e01121e0506130c14060a051c020a17070801082d010c0f02100203040c21020301090305040513150e0c 66
    0x1c2c105444c507845441031092030703202d5211404220300a00400040d11018101130325180541d8400b0b44960102c0b000c03105280c0c00075000240f0080c1016200c80c00308418070741b09511451a29080c0c0c1c5e030b2058402c054140941241e00c60783c061300ca032001c1d01004124101132440d82c00015640940c0c11100951071441ca0204002402d80c09001401548188a21281691071185c0706611461748080f4140d5180c280c000305600d40e114203504840d007001200d080e01d204500030500c0f1401c40c100c10310701c81c0d500d116480032600080712200101c0d028452000a049442c90180d0b44010b0601d441203407036042c5444240c80700c196501c4030345201f40c29116440503602c02034400e0f140034602002000030090700c19009046810380c0074000050300450801080c11000d5000700c03840340da0000008040c05281640305140080a04401480c00d030142d0a40001641d082c00382d0f40500d80a0b54505496a080c1000c2119003018001d020800e44d1401c0c0d54190400700c5110910115150100b0048150740d401402541c40c0c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 626922311 1250 626921061 626921063
    0x3240103140f101b030506090403080601020a08030708070305090102070201170a0b0612070905090f01050f180a05061e0d060b2e0e0108010602210c010609200f0d0b0a03 74
    0xc003a800d02c80c52581680c0e03000040c8514000c90080644d44060710560444100780c48864100003c000001c000c01d000d4a04645c0296044c412100301138450b0b1a041265002501e100b40010392480c14041003682c03600807a50800c05441c02146082500d0b030000e4056811445080b09414500340040c1905605900000e042d02000d018181c0d81c000b88903030b404040c803041b142c180100d111013074003059a0810322407040c400d45d002e4034a011141d09040410281e03071400e600340c560082c00d07d003100185e400d40d0071740c0a00920700458040780071b0030585c013080800901a2418402d0203146a80c1d08015604d02080f5818a078001070000b43e460072140100e0034802040c10014113402040c02c06540c01541c2510240880b80760340e41d1101e80515100045651060030b01c654001a4403040417000140b00c980302a458602c1051641071800d450117171140d094030003507408500020780e141071030084042608180c1e030110380301c1a1607a1130907110135140e1301c15014401c001c082c1141c0d1007030398000c503803540d419041c091 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 626923561 1250 626922311 626922313
    0xc0b040c0b04141203041a07050c150703094b0803071704030b0109022a01090302070902040b0a080403030b091302120601030804050d110d1103240103140f 68
    0x503c0c2c85907200382c080c82a81c02e01da07001c0c40c0081d41040c401c030740120541c6c003510354526401003008500706d06100f858100080c159010b01451940348400c1c0d948640d9181c5110078000243d4981c507041c20040c0c81d518069101d4028015404119001d5402181d50002c14440795414140310006c141c282a03108610101003c0003d03409000c0454a0b03a000406401024843c22060b80001c0980d00918040c0c0207038800105500925801440542c000d070300504260420341c6000f8a891801c881d00070042000030490510b5030355142c480809150381880203202601c8080d505525140ca40b00c00c14070188500c004172810030402c10045820140719410050a402000f00b4a07045420704030344031100e460250008034440d030b44a101001c0004008103102d4101c0350003261322401c140c6428184130f80344010810444132f9100b038254581070b56840c41c0605d880b090068040100c070b041c03804141460440c2a114202c0080c3c4000440759828400700c2c035103810740ea80003a180404040d600c0505d45044071104415800e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 626924811 1250 626923561 626923567
    0x19030507170609070f03111306091506050f03011e080d0e1309020a030206091c2009250c05010e0c01031104080c0910081209030106050a05010c0b040c0b 67
    0x10340050754440841d050360036400d540c49074991410540e41c8000c0f6100d14449000c00900c200003184a80e100b41036040c501405440403103405810320070460b48950070000186a4030b040d181d6400d6000344001000d00b8407800d006103080f11070040f212a50105100d110305111111030345204041540b00000c0080c20b49034100c0ea400b40b2610806007034810780c0094280035103011890452400c61a0151511054010381400ba800d03003982c0038450190f00a42c038203a00004100b600d0b00140e031003a400800d030180519032010240c19000c01c5003004040003620184140b0000040c0040002510300712140310070030304016180030510080a035580701141501508a500e0316001c0355030050045441c19801d4000d1341c0811182e81c411120145a002d14012000540c1c00314081d14441c0c1840410b954210780030b079044400440c2e031404624580f000542940c1164080031625001c641024010080608011100c03a0801400c0000080c0104038805002d0021548040400c0c1408613200d81c1202a201800000d0b40d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 626926061 1250 626924811 626924819
    0x60c010903080610051b0c030a0606030204110309030406050705160905040b0601030507142203030504140604031e210c051216031101020903100516020a03050919030507 74
    0x8000d040200303040d80442c08034400201c030792410103000310f10807005460351801c0048030412522900501d141c5c810b6039204000c003c40c0c071a5401c00a900c1c50a2088001164050852040c802507800c40400c0f962203d0051041c0980100003000303640544400e407502545840c52800d010345803d05440c0010310700110a900411800940e0b040780344203500542c2c0f495082d803111f00045003140d10460300351000801d92005103034560106001414424000c90b49194011451a40303600c248501d1b0f40200e020410000d001c22000c1d1044002c02070b03d140496800e0b09151071915101c07501007801c0c0ba01d1480e415450b454004010700e00802007030240340005141c544039401c020161143c61182c0043d0380c14070031050b81c88001101d031740c1140e031085400321810f544a8401e41d020b40320074555114000030365409001d031440d1924204416015546400408112030402000c055041e1101d81401001c42d00088a41c00110740c01404070766041e0720a4803070a00b41c0049110345200180a600f005040c0e01030500001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 626927311 1250 626926061 626926063
    0xb0a0905060909060403050d09020a091d070803072d06051005041a1c050709050a021b0d0c02060c030409051e07170f0a0b27090a110f010e060c 63
    0x28400e4105030342c80b0b9060784600c5070582e919a004c0714000c0c005507003044800074070402034000310101440600302030072142e107407014403040c0e490880c0c000b40c050581d9240c00021520401150000b4409900510300e4404c403503c40303c07100d15055448043c0402e0501c81c05080304500b000c08101c094002c0410091410000b400000b40151441458411820811780c0c80d4010341c414078050208000808005000030089103481c0d0103103041a0075034032401003401c001042c002c103005262085121090040e9238904403046280a4090003004040380e41c40309902a000c0c80e007008000340701c1074044513402e88540c0344020f001e1640c480d40d0045012355007070106104400d101110814800a60030b9403d1005944000007111100c840b0b540f0741e40096528000b05d0800710009603035039082070a468000c624004007002040740030900c102010a802c00ca0008101b0151041140c01d0b00003a5a80203002e02c401607499000b9503d8004003414030441c0d82d21104204c1c0c0c0c0c084e4000e031540c42d502806c0e968860481061903 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 626928561 1250 626927311 626927321
    0x8060d02040212010801111c05130f0c151e080606041203021e010e0304150306030c1e0603051b13080706180b1606091403030109021b0102030103020102030406120b0a09 74
    0x41441c6d03081500d4100c0c1c0c22401003c0e10600c10605030b001480141d05502c210182c1805032400081112800ca000c011401294040c5c2c49140201140c0c20307058a4125446409050140d000080007807010a146004460200c40301c2e0800b9075181410b010344801e00020300d2881030782e10289980e40e41c4070070701b07080640210b9074400c0d070303050140313407a0b0303d940c10806060a1300d8004804040a82003040305010081d0380c10300038030704140c4034500080c0350f135102d940b080c801070f806130021034101541da14034041e1184c0321201c1c079000c2c04081c5401d00041c188404594088000d450492030041d00200c2c8450f00d40d011074421500030000301d01203c400941d904409003064200c250583c44001441c540840c02003004022561414500001074005100341d858140003070101d017004544000d00d1840c0c0801e4403501704040c40c003030000a0f00050707440319500000307140c0c422040203420003a4018401080580e8001c000e450850310b0600b01001c0c00c1420b03480810082c80a00500d9500c0303500c3c4480454646025801 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 626929811 1250 626928561 626928569
    0x303090d020103150e0a0c12020f0a050304030311031008010b010306061407032d11030f09120c04050a0515030f070e2203122301091107050613031806090608060d0204021201 76
    0x441e08c1000001007518240d119064021b451490204111645a44140021541315000e8075000039120351490508a09070f2043e50002c1008140c810244540c0000b27115048505009080401103180303403080107070030b028440d0051078544401146da00d0526001b44c04583c00ca0980244407402418104000e0311080006568540043c118040714845504008100c8543c032540c040d140b8100250789041209001540051220301e000d8061170007030b01d49a900695000e40321514001c00c0c0c901c0d220140d580361f1030503402d4440c0300c0c0e0300c1503418100700800481d01d00b054480b40400803103540d868043c1c00c404a80b21804000c251213054843d002030550110300700807441c8a003035042c402c624030103104141680c0e140864258010034840100455001640010b00310603900310041d0600015840706400c090080740c40007030702d045808414081580c03105100c103120705100080004141070443c0140074070141d0207013105000c00b820101d00f0395500c0b40501210340d58014001e5684582d01c14021501b2034080c41 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 626931061 1250 626929811 626929817
    0x14011407050301060806190506030a14090703110607032307020114040e13060e01090b09060105030a030507030503150a090f0b040e0d032c0d08060303090d020103150e0a0c 75
    0x80428052880380c41140e048031955616118282c54413820801800511039402d40710101e0810000742c1d40d180c00c40611b01c55030140c4030004500d800b02028086000c401800340000d0b401c201c50910026014400f0003081040a44030755440c0c0f41c2a150580e80c5280c2d901e41d148061380c45c000031540c602c80c00c2000b0060036100fa03840f50350790446103070745c40c010707000301c0c000c10f8243c5610400080600d00700320055140d0754081c42c2c012801e06c04055001e402c40720001420395a40d0702ca2420069402000c0041030f004190036002009550660384004013140210f050040400000201180900f4082c2c02010120b04000708400741c0705650b031929400810b01540d00c010303c0303410500c4071515450503201351443c039070440e005041902c81c1c645044005240e100e400d44a80d48100c1c00301d004810f004040030302102c04100c001c19000c004444090866a4010060344c840e0b40200902c02c0d6680720f50400b40203055080c03c1c0440e02112715612840100303000c1d004028068200020008000320f160000c20155156407 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 626932311 1250 626931061 626931101
    0xf090907061e08040b0406091205180315040206030c040302220c0801030506060123040b0703110304030c1a0c120921030a0e012106150e15030a02071401 67
    0x2ca900402c1c1c11424000410782c0c00d0000b4000c208060300301c942c00340c03054800140344411503940110241c04451414002180425520407045e06500141c90741d2904400600c61099400d00140c8400401007000340146030220208504604000a880107182d004060981d003816103404000d40d00b286481e482071a0341082103c00806d0700503003c0030f05803078010020b01159502d8000654655643c40340310608800b541d0789050315071941d1800b9001038620701c0e46032680c8442e5810010408405030080c003c1c41d420411041002880242015045460341c86028250304001c030248070f1030707001c0c28091003402e00038001741c001e07802c0341400106807602084940d4941500d0301106515049103002c0300804961041144060341801442d8900100070145031801d44030103101080201040012200c0b4000c1c0c0d29030b401480720f200b000c19044000640d91900d04d030350305c1e144000544032a5040600b442c2e100340000104001c50392940443c0e031400e030400c036a114800d01c1e441c1d03502d00a03c52004180700043c000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 626933561 1250 626932311 626932337
    0x7050a080a2f12100501021e030415050d180209102d0302120a03020c010e010507170d2c160608060a051203180319030e0f09090706 58
    0x78401c02c075040941d821140074001c0d842480d8010010101a1041c94101c1801041c80700307441c410301c5a1050842d06401204140303058000b82c5007481680142504242c805d9030981c0004002050301c0451707040542c800e0150015110640c2c851048103c852402800d0002c400600040a0401407120b40300399220503050b075858001c0414075400d070154800d0041201c000d00c0e00452a041000311040074110f80c0480c0a949600103080d0015129513070b07105030000d0001d0b90a154040c080d28135415020300308240c2c8240080700080092045582c001c01c070300107103103005403200d0411040e6004504400001c0040000a80d00c910041d640007100307580f10705400700030020700c20000c42c1000000022100a40116092180690b04c00340c00600140d0440b101c90300001d041c3e0780b21201e424408106a000e9581e1760180e140c2c000d48814808180d9020b54440c0040304600c10000f5050028250503103800b5a88961640000c0c9900284140c2c19500c85821f5091140041020524000b1180c4c5030320b80c94162928 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 626934811 1250 626933561 626933581
    0xf16051f12052802180415050a030317090a0f02130f05090115140919110d0207230d0f0c06090804050109090501080a0602250516090e1209030a080307050a08 69
    0x118252a4040380d00717080c1c01075075401d040e0800b842030300311401e0503000b45488102041c0b40c2d08081c2d00c15000682a24581e0704100001820240c2119a4102401d0100f00c1d41c0c81e0344110820039100240540c6d00384103607801041581d404a1150106c90100740303d81d007400400f0344d028107601d101030703030780b248100c00f0010300040002c0320036000c900c000d42070482954901a15410b414281c0b40c40017070150722860504111608a001003443c0d0703454000060300d4202c05e0402c0c40c5100c880448003000749040400010b02c1d42c600103410090034003589440c400c441851101102c002c1001e9500400e1142010b40600400114101410540d03a00f0b1b41c034184800d035600d8405040d100c0a00c0740c0b8400e9000307400c1d01404590190002c0c01980120485440f0f8106a5081c0c1c000c40e008441c000e840301d400c038109007000e125940c3c0d1560300805020b07900303002120440c20110b80325010310091400d49040003c9052280d00c0620401c0d1205401c482415200d14007042e001d0140c0d4484800280017400c2200050301c8202 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 626936061 1250 626934811 626934817
    0x1012020d051801381c0803010f09091505090a080d090b1f0b090d0f0c0302010305060d02280f060302120c0c03090f04060f080f16051f12052802 63
    0x2c080d140084da10102030f001c4000d1641801c0e00290000d504410403020310303c10035120000f061142d04059925850207907002642d06290304041351880c2008a008081520b11070006150003900c1c0c0c0c0028151600501d680c0340500c2d924000341001c0002c200c50355055050341c084050075020382c0c003581c0030340e5410503080044001c200403003142079210341061062120010103840c0d050f2003e01040c00c00100d5448030200c2d070750521021201050200002c0c000c55916000d01d542141c0151f52610302861154002031024940c0d0b00400d800704114003505112441c4140b404008000e040c1400103003c0d25414020041e601c850610740c00d8150f00004141c003402c04100300c401c05a5864043c1d4184205c0d14200f01c0d1402c000940b0036881500c40744080303514155100c0800007400c041000300301480d403c0b42c1042c02c3c981d8168210f00400800c1c40200500d03181d00003904a08000418000c031100450f11050750b04000880e103400145280c8410013010303111001e6000304070f000e888111070550120340694000c1c1d00c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 626937311 1250 626936061 626936111
    0x120703080712020c150d1b2001020d0e060a050601090e01060516060f0c03050c12010303082211030c040507090b1e0a050a0912021012020d051801 64
    0x40d41003105601050030541c1c494800e410703034410395003404103001c002003241c802c50300003c2c5106400078000508072a1885403407081481c40c40c03810720642900302e010703000701c000e40f1820385c008d02200700c2140031050a5040310b05079040c4079402c1040701e0403541825900c0c4c40c22942880c04070f2410001c0303044d80d8001d00003801200d40410b9016035580c2012404c0f182d50300705440c41c03030720031021454010000c1e0890140d402511240b580018140080d9034008041e50400f41401030210410400c00099040e440c03059419613806007040421519031410840c41030f01007040b07074041c1524040000040048204800c02441012022108030044080411085800640d1040c000c1640910204a84008607019041d56420b82c01e10349500031050b210181e15a00050500001410025030706a0f00e54001600701c01507c4059410b1240c110144d0210f03138210101e41c801418003c0342c11408061024940480d01c6504040409014508040b808000c009407440c007040015420700f00320b40580e01100d403c490040c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 626938561 1250 626937311 626937323
    0x6080c100c1a06030d0903120e0f1002030c190c03030309020a03060f14070206060a061b0b010e0f09031c11160501090203010e0307050c130e03040b1c0b090a1a0a080c120703 76
    0x10701c6202381c00e9030700300b02c0c040d411904840b80b10b10180f4165100040380300010301c581c024580e00d1105105441c1003000b050031f20305007881c4c519000404581c1055940056070b03072604000490140e540009001c1d41410780c00140031034141091442c03d100c65030041428001964611000c5480740c81042e41c45910498440e90411f1040c00c081100d1032141050040c484603000d0511204400364a174018201d80c2600582800c4c458642800309540c0520100e540c001182c001940c200000ea401030000743c1003420b01d00c100e4035154002403401000003803c40702c4c0601e01c40300c0400654000d14095005c0c0040c1c600582c860b52809455100707012020045411055009010300104401103017008801d560005251052503510102d0710904282080108003a101c0034400d551144484c860142050320380e01d05003110a8200501c880c8103480702d15505400a0010f8404500705076000560f6400b4001c200e9a168403c041d00c00c002000b20303012030b00c1019124151011a0480c4c0c03107a1034203641c0c84092000501d4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 626939811 1250 626938561 626938583
    0x30a080403080c12280c021c06021c14070206040b01092d0b01080609100303051c02041e060314010905150306010f0509130201020d050f0909010b0a110106080c100c1a06030d0903 78
    0x2525101c04100e90049d116800050414000f040c1680300359410f10004115540d0b541c0c504080746040d02c401a511080c548020955450725075911440d404042c0b04880400b40c89489400040390542160803001c1e01444e19100b940030082d5404d0050710801c4540c42c080741c445008107520f81841e0802c075108192101c4440c04507450b6130390464640e4040441f03410300d004603504141d1088840d000a0004007482d4a03c00801040d0920b0101901500d61083d010315182c1400f111034500043c2410341150300b00b510004143c0e54400443d20001800075190f40d16008072000070a810603401c03075100a40e00c05540e0804941d07550003208140f11104075020b03000da03012080520f00c55200344001d115444556100034140000c4e1008100300220072f0300070400c0c800010981c2c0e400c181d07100c4441c1050304a808000e015861034904819100e800b0214114066610003c0000417a405548034441566102c02c0c0d010780010407034841941000c044d14054428021040900e2200d071040420710280c035040300315140 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 626941061 1250 626939811 626939839
    0x6070f1407081209040204091802100e010816020a050105070503090717071202060403081813050f040b090a0b0a020405010e09012114031b0c030a080403080c12280c02 73
    0x1d180d0001c10308985d000d0b130200000701d000e0115015106103812007600541c0044400e2040109480001148800b048441d0700903040c40da0f07101080d5604903684440e03140004c04454801c03801d15a410f50b0141c2903600304400e10414550020082d4464120700741075900540e2942d034503140000005600c580e6551200000f40a800300155803013003510710090045203440e03603e5403400380580101d035942c00a0403110b1517880550820707013190f900d01c40d2410400c12080c944104648101e040183c40944420720610000714400c0041042c5079200da008024100741d031400400320006907026000e140d0004d40d07071106202042c104500082c0c141d642c4442031160040160701300302450548028242d0300405840c0803404241c9090000741550104501d281d10a1841c00c00d1051500702e40104842c002e1f880310306840d0118410209450584c0c5e40700d00e2060f03590940170b0311245408150800f01a90000004900e6402240706500a004210051100201d9417034040180e4030640407400c0650401203000c0c60340 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 626942311 1250 626941061 626941093
    0x902030c071b050102150105030604110112090b2505030703020d0603080c012018060702040f050c07030305100e0a0f06030803101404050c0f03040c030206070f140708 73
    0x140e40062600d5105040240c15141c0c40402052240246911542040140920b5038148404003207882c1c402142d00d0300c1d525280100f036070b4000041019000c00d000c071100142c180c0c4180c0300e150210142d0750307051280341424107121403505c80075600c507420300741d00c0c1401806505c0c070f41080706800203d60311401e003199116001500130394040c1280d02c2a195651001200240880d00641804404000000b481c1101d0586403034030030548800b40c6044400034400e07401c0b50861817501c000da44800f81c40d0f0386e45a83d058804200900580494404014200703070400c028002c4a0000d00480e50107a601030056840b4040c070844070084c00d00440d080141d81c8400546980341c1307904503a04c9100040800115141d8030344400c50310383c0094442c1c2070a0509040c08100d0340009415100c81c6441c125020007007400e0001001c0c18038440e03020080161400400050103100080241c1e600031074010b00103582e07940582c6000f5500300342c00c81c001c03100129840c06244419000050005c15111040e0003010100440346c028 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 626943561 1250 626942311 626942317
    0xc03010504050618070f0b040806180d0c0326091504030e06070f050706180b1c0b19080a02120a050c09090f0a080a0e0303030408090f040207021809070b0f040902 71
    0x242d0300a11038454000fa00346c007403079000f100802c04811290303251418a0110f60800c8006804100e680c140b240842410300d2010400c0007148005090401141d42203140543d04030f00890742d0080e03980f0071a0605480c2400c281c80c502d01c595018029104055000b59400d10555010340d40600001c3c8130084420742030134600020b0001c07030300900448101114581ea11849c1005540000000401d0f600081c1c80e84061020124082c03c50b03440c019080003150007149289004803580620b80540310721a000760390f01c030141e00f4030155189403c48038030380780c68115a035a6250034002c00c80c024140d54001c0400b84001081c1034403d16801409800525650170811010240103420802e8074064481d49002040041204e99641c500c64a5801e4540c03030a00c40c090443c554049038903010780c10800401c00000c8581c81111507200c41150060742907018140424024062504002c2d00204110041d071008a1004685481403c40d0b4041b50800f50700c40d8283c0b040350007402d05c113859502c424081440352548580103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 626944811 1250 626943561 626943601
    0x507030615080c0103390915020c04241e1409041b05030d09030c0605090d0f050a0602120406050a0b0616020325060e0603061003090c030c15020c030105040506 70
    0x510074400e9210044815403526004280c2c1e86c0d504500e00b4021003a08960766038001c082140c41d142e403642c1400b201075140c43c0d1500b1200d20442d9600086d002480c06c44400c022061101101c0841c0b15031500000441240701a8510444080080000403001c0e10900c00004018000e0440c0c84180c989076203000e0700715459000c2000e480741c50b500c04075107904d00700b040d1503000c40c250b078919821525608100c2c4070b0002c1504004100002005801c8040d100c540d80100301c240c3c012500305644509091403070401d02c0484005001d03e00000300d01402c48440d24083e400307240a8101040540c80b0311155804a999941202c0e801c00320521410610000008980c03462a00140c01d6030224142842e040c0e9641032120140b50204840d01c0c01485495446840d85610903421380b80b0602c0d60270200001002c14080041c03030340805854004803010814031003038000007907920000d59000f054030380b4444030b1080c003e2400e01b0010b00c6001750b41c480320b103014043c040c05160000f000d081c003522803480d0844441e51440d5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 626946061 1250 626944811 626944841
    0x1060f06030f09030e1c080c030a031107050a020108091606090302030c030f0c010c150609022502030604060e010b040504050c040c02031e0a020a17210403020709051b070507030615080c0103 83
    0xd80000450440d40040038612903542c05140d54ac0c2e00c0c0c440103000c41d40210102c86242c84144080d07800282c2c00241e09415507024201031400d9130703c00c580c5900e04507025038181252541c00c0b43c00124a6081070081060342c0c0308505441e03880d110300084c1036a039100d44003034036004c2d03000a81c0784100c0c1d4002c41850b88624020300310549100e10102561094541a1784200807903540000d0710b100751040050401ca42500d011030110020121f500040d0303403481c3c0500058a00742d1360308043c0a40305800d601406414001400c1441580303000d04240380c031b85218000c500d00440c2414452aa402d10220484420106442c0416800b6044007410092608411702c8079040d407081c19200c50126941c0b13940d4141607200c00d00d074140d0380d440c0d0940e0b0f100c8040a00e00e40944202620050000117038011a0a5090b2007040c000000d982e550030b42c7d41449602c05420701e910034680000c560084c094003013440800d90b8001d050921070850590b100c404406030034401c5025640251495044662083d004070401400c124 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 626947311 1250 626946061 626946109
    0xf070e010e0306010e15030d050316030f1410081207081e04031119141315060309110603010b16020a0515031603020a0c02120f01060f06030f09030e 65
    0x20301103483c2600a801c04444e01401c00200711403441c80c03800341503d04900350060241c08403541c001819500000e40000385c08403400c5104c02070248641d0210001c0c442100e8107200072900644c0d25000210141e46030400700a0b0b40c6808038080702c1c0043d203820100450f042851414a140d180c140302900110f111006085054400840805060018001071030182c001d01c000d28480804021000e0880070740c05552079a0b5100c01c104044500c0d1100007520303801d40b54107007a2803011200305d0003028445034041c0400d001803000324403254076900c40c0031318030f10840c2d848012034104003c00055000034800e02d408807004208920b0410301c0f540018105c644060312340340511f80c44200182e0b20440c0c1c00c2c2c280c01a4140070003002040c0c004411460740f1342c0340350f080442c41c001d9014001010407254110190183d0340422122400c00d00c03c01980d86807641c403074020001d064076000414031002103446000002401c0900d02212240c9904c07505401540c9134682c204910081e105002107465480b112039200d032a21 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 626948561 1250 626947311 626947337
    0x50112111c0b06120f1b0f0112020304061d0d0329010f030e0615040b0a030312020711190f0608010608040308132102010617060403200d03060612050f070e01 69
    0x2000519008031035007000d4400c0001c06040c030044410305410300c0b8842c0640850b04811f99070010713020f02802d182001301507901d507200c0c101080904030314180a0b001d0200202854a0a00045110785180a495a00b440300d05484c0d41c00c0200c0444401c0f60306171607840744051a1a541c09601240b012200302d040215001c01464459030408808441c3c041c00c620070441c4460203803800e0b10030602845c03400c440f1146c1d96820760301e0041442c182e000402000c150b00082c0c141c20701000003500c0c501c0d6400144a4003042c1d945041d01c5203406520301c686500c50703104175070114000340102c521b18103840e595501e100d50365039191401c0700c109001401d803010100d542c80ca1b079008a806520422210403a642e00d107000c60100450080c00c581d0540c0c400c91000005a00084c0f0b01c000c00320300182c02c250580342103030307400f203000c482002c1d0300c070645e500c000c070f240f04101001e02140d4264205d00200d4415403030b0742c01071511252462003501d00c02c40e4003a038aa0300000002c0c0d04180141e140c110252410302d800c0388030b1414 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 626949811 1250 626948561 626948563
    0x142a071208031b0315280b18031903030b04090b250201150308070501140a0b03070b030601120c020309040f0e0d0302090604061b0204050112111c0b0612 67
    0x205006440081002007001000740700c1011449903c5801d100b0140745150205440c40d00c07540d201c0b03000348240212000c3d070701601c40c0380300140481c1040d01d1500001d260b444954910507403205010205c20840c1c591106064500840c1c1d60300f034a0815101c1d41114034159401300c0080c4003018290358480d54414626010030940580305114180e2040012640d09210128407688003c684800c401c40e030405911102200c441c2e40c80404895210746d089440300b038a03240480c054125404a08103151520b020000c800000740c0002030403035410f605460069842d408403034940d200c100c6189002c00c0e40c0e807564800410340307684500050b0032144150790030303c00018002401c0d100c800c40114800f03922024141c9061701e040c40070003824100d900f0110b103420300d10310200303184d0300503813003001d05004824842280d98050100750399441580100104260740e19800001c40e00052108161034908085014501c1e500702040c40281d400500b00c3e008054078241c0c2d0340c0e90348101008050a4009825403c0350501e044 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 626951061 1250 626949811 626949839
    0xf060c16180506030706030902150309030a12060503070b130e090d031107080f0306121f050903070c180608030d140609010e13050f0f07051306261c030c142a07 70
    0x1100303400b440c0d88050003b030050407410b612a155000d1440c0c40f07410400c9680c0018000111110710000710f0300e452000300451a40045a413110681c541034504102c800180410310030028601510700704000700359107030f400c81140641c200041007104104002507240041714041d5070b004c44014050038500e9007041c003880c1040480e605014040410080e04000c41d5084c0c041c40d03900070740080045003021482d847e1881622240d120f19002502d503200281024036140c0c000f00041d184207421203030b0b503400b0f1010203402040041e8001c1424402c5c0c07000308000d1b242044406041361410026100107071540303528042d4612503500122817900c20510071904901083c001c02d9501044440076244007850070050042c03103014810f54080b03280c9000003d00c4201c80c00380c0d1000c41030407681c1c40949d43d1400903140c80d00d014444100c90003180c140000c4661387d503a058018808505045e81e5042e140445c0034079218031801840c000820801e0700032004002001030f031141c0c01140e4220412140c80c1035545281801c822 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 626952311 1250 626951061 626951071
    0x30133110a0f0b06040b0915101701080d03060501030b0f090c070f080301081e100c05040308072d02060d02070317070c060b0f01020c0f060c161805060307060309021503 74
    0x742d2010014149403038800c00c800c0c000c09030b071f4845940c0f6144081441144210b0070891142080b0480000300610031000c480d040002c25030042d03080d503180c001035035075041c2c140000c100181c1403400205071540f00340a10a00c070318000c0c0c201c0c1c1c641e00ba90402c2180e0b072000248284880302041c403c0c5808a880c8500040005008030011a625410026107500344000d42e114289031315018020f0b410710407000109500d2200c00c4070400075403840310440480303480c812540054100c40700407820310180b200d80f82c02c00d1841d5010355480b400c1305083da403a40742c042d0070001c03020394408024451059003c00c16001866882d100e0714009041a10300c522521484c0c0003501d1134000120351040e500204220f44c4034030354500c2d2044070590502c0f5407602c0001c1d9140104060640503c008403540300007038580c1c0c42910102d001500585240f03480c00e81800b15900700310320811110b25100300e03407201044410b02c85c10340100d0014010b809541d0030044154082d01c42c0c040220313009800340010102107030711900038501031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 626953561 1250 626952311 626952323
    0x151d060a11010e071208030606070b0703020c0d0f0c2a0b030103060c091a09130f0c02150f010509090f0601030309240207060c060902030604030203030133110a0f 71
    0x900d200c0740e5941e0840d0b000c1c50400c2c15aa1000c2002d2003c2c400302c4c0341c0c510466034405025503076550b40c04007007070040c042e610b0000c15400c0d10100384194260190094003d00459a080b1000308450942c229441d1100c25108404034400740203840111f1111480100414140c08660342e10111650568031010140d50050101c0b10000c0010710030040c0c01d0081c954206010b1801100807424a002c030140c2003d1801a0004080c0c0045c1c0c0614a8075807500184511104150801191144280600140c103401c40b4410050003801d05080c0c840084000d203d0142410220042c4103a00780f0041c0400c4401c058802441807150a4a6024000c02040001e02a5100e80d880d8485580307070415088105143c2945080c07011072081002c0320495001480404a84040c600480300004078100310f801042c95060194060107008100800d040c0c00000035412180001e5002c1403c0303201102140c0070340714003142d510b10740202d052101c070a5440f60364209070042188003034810745105171781c1e59900d441c5004800c07100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 626954811 1250 626953561 626953577
    0x19030e10090c0f03081207030f050c130b0310030f08120106020705011214060906060d05100302120d020d0c082205010908150c07050a0c0801050907050a151d060a 71
    0x2c12002500080081c540b9a081d806440d0441e60f41155a0281c1300200032050b01a00000d94550301c640c020340c9508805400c100002c0c00d20940b450f03150303445020104080c05070114001003012422040764454000c08541070600c40c1145e1320301c00c207622111010751328030300148000303032001d034003034070300b9402403220350001c0101d00d10b014009490004020860210303149001c002003107a8030342e902491303482642240c00d030400d96220000110340b80120003010001501d0720342005200c10707540c0500e00c00d40380216010740103201c1000d1407030350302d1240c014040700681244031000203441c019140e11030194860b228242c2407410070240b11000c581428071b003641005a01c0410880c1d940c01410312006004548061f15017070780c031140141c4600001901152070b02c10001220002c2c40001d0041c01d048952098581001e1607950760b05502800701074500311442d000d0103400141b2890441c2910044840c00e80c08416100f501c0c0d401034400f80030002c10302e18261703050204401c45542d40c40081800c032890f9110010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 626956061 1250 626954811 626954813
    0x11030907050a120506360309131509050604110d0515090c040b0f040803030c0301140402070f080702040e01150e0912190513090e06070206010b19030e1009 68
    0x160380941640028482c030b660f20b0210b80821030220340140d010846516049954902e240b2400d800000b40181044041c3d03c608120a0344501000802840e40b04549682402c03442c680207800b08c81c0e1030306092a803190386c58410041c0f4a915004503130700c840010000144100031601c07196569200e068000034444c0c2c1c450400441000c994888a1450703c04d882034000c916254190b40071038482d60041915025012507181c1d004050982140e01504c0f0751010f49031242004a8a500c80c0e420030f01403a190301140c00300502c200e0520344240c42c46142c1100303100180751450b840303802460703008220590300280c859403410480c12090042981d0220054140e60100e0701d001c014901c0104c0143c1510440c1d0003108902680f11008030641e4035800480c12050b40702001000203541620983d41610358440307030f4400004002c000c90344071a56602410042c4d400301cad030780c6102c102c0c0c44500074040c103485c03041d00340999410901a150507100108032402c001408401c9122040d2820181d003d14036001a01c0e03046901c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 626957311 1250 626956061 626956069
    0x20319050a090c050d050c030d021e030a0203040e070e10020708011103040b28060b0304031d0a1a070b0f06270106033602030601060906050d020d1103090705 69
    0x69000340140000c02c00002d103591558075103610752060b03502c1040304110890a00c10705001c4500c040c000207086034a03495807400c01a4407800754210b8840c1c45090040e155802500200c00c4600918407035004d13518103401c0800303004140c040902004200042c0005002c1240c58a4600040b208c6442e00104401c6190000c5076003590306080380541103000a0060000103446141c96507040302500700e80049006a003070b4000c50400500c81c086100c0f50034440002a0900c00c80c00650145000380e550b43d09184410034101100c0d40e220880c0781d040740e07881c1030410810304110324030b02604402102e031034501800c646030510190b01c01d8800b01860b018070700a01c02c40d460410030090f00c090014299043c001c00201031030f580d17468144185000d05817034800d0341d4417076100104035800e12207508102090703e1010f6081d1088400c002c0008a01030300c1508000308581e80120010302c1180d0583d603403039180040060541029401100d80b10243e640c482c40004a14110700015501c115007040003440901c1c034100c100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 626958561 1250 626957311 626957321
    0x3110405045007031404031d09090316021f120501050306060a03030c0206122811091c0f08070c060e15090f150a020105010806090a030809030904020319 67
    0xc412010008030303003440748885030a40c1d109450305503042c44110b0765070f03004150090040e4540840008141c20100004c258200030300500e154490615010000c1600080c814042c5060300c400c0c410341c0c0184a0500311142120b0b006a07524400317041686210030880840008485408814000c240280f0b01c032041c0002501c942d50040000f00e000b440d6a040c035102292010540380030160070401d00d603580d8425911081c1c1110300f030806148280d5203514050100c0104030901720400d40e100c25803426084503a02d6540105881481c05103d05403601400408001a03401c02020400c40503501100c01c40110384410100c0140a00030900d5641d02c4041d0f107822074202c03070710303410250134800c40c0f603030044440d210b8400720b0310103a50704a00d80da641d002c404001551411001085980400301c0d0030509252002407004e03102c001c00c00c0d00288003e907242e0400c1c82e20b0f928102c2c1c030041301c2e07403025503402c002c41c0c45030708825001900764043c0d0b0b161642140c0858143c1c4c0c02212680320b010032000000b122030230780d0720034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 626959811 1250 626958561 626958641
    0x70e060604030b130311060c0a170108070b09150a0503040c0b0f030c0d0f0f020d0e120313080d11041d070c02060c12190806150a0311040504 62
    0x4603500e4a4210390b0b03041d01100380680f4041c0da002c1d0340400041014001d002416503030182c01c00300c4032a03150810403040b2940c4030100050002d00310041616010044220b45410703945140054008141040c01010712038228000c55580601d0061958001452400c007c104541d110350751307103590b850079007080c16551030154804291080e0030802c1d07110f981a9402540d410440d1844902d68031002140258080e06940703905d80f070031038a04aa41c0da459040d907401401c8902d02968140021449903c00d55200ea10140300489540b0040001a21000d06060700d0564144605039032400d042c02c20703043c3c0041301e15811031410a00c200103018000090208854010403211041032905c0d4902030500a01403884401c000b03000c0c03d40411091183d0303009002680c2040090b80c80c0d01d80301c2c00303011464540508412400c03004206000e021441e5820b14110600ac003514404c099490300460a070214000c1c1251260a42c01c80700900c0003060303594950007182c00710b0b0fa000120740140540c4140f0314050700e40d581c80c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 626961061 1250 626959811 626959819
    0x108030a1e030e0d0305190209010e0904020a030c06050a031506120b0a052e02010203060d11040b09040305130501092607090203090f06010510090e060a0f08070e06 72
    0xc4148881940052030149040100d440035403500c101c0d05007036001d014410190b20b12809091840e22406515038800c6100e10840600200e8410000c41c84000b240714900106000407004160320249041054040d81c0161015010b107200ba5030300c1d110300b0103c2d202030300400c00103040001c4c407049241e07240c050400c0340c0902c0200c0c28001890504060851840c0d95001c3e105540c884044240668460303000d1802004060040d0744008021100c503031020149004031080c21030804560305406105100366480303002c01500651a590058860700c0c203105680e50724541c403540300c481c10b800b545c8400c038526024501c29105c1d20386803080d810016004801a40100d4108001a001000031b21001010002803d0001c0180c40c0c07072400301d0358070780c1c244550b0f43c004034040d41c00007091141706032000031000803c250400c282c40090340ca0300100000c41c1d100c5554400000c0428030207100c1d14464164064204000810016100d0354801d032004c202c45981d840303440030f600555402c200140595480c560700c050222 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 626962311 1250 626961061 626961067
    0x90616020c09011e09060906061701030c2304090605040614090c0d03020c030a08040f0e0c030103081b0d031d0a0b04030503060a0b042309101502010230010803 70
    0x3804541c0140c1e0502c00d0303441c44080c0301d811600142a50351301101a04582c9810320901d40c41c0c0340740801a200d1849128000f4007032006082c0740844607541c02e0b040e40d50000c030b42d2446078589060010742c109200a4188421000b6100b03880b84c0c5c1d514071030880524440c24000c940b40c43d050600c0411510440c00384440d240b80d400800c01045008a5405000d050854411070548200d0504a1501034040318a90f0140b188041080501070004094030844040b442c80155250302e070684140081b2080e2040303504540d007800140002580d0401030942d0054441080070000c0e0117030021490710f421020b100e004241d40d03c0c0040028000c281c199405080c035040180200821640e40d40007075203005002a04011b000b101085207a82c4820880000709585200c0a0f01ca68845110000c1c92004288407070440315242900005410498001d0b441030040100340030082c1d1510400d00e140c000d04160001c1195030821000c100c0b00562100b0100000c032080c0c528040c1903140000f01d41d041c2c0183c100b0683c5034018 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 626963561 1250 626962311 626962333
    0x8100911030c030703031404080118020306010b0a0210020d1b090e0a02090105071b0e0c0a0305010906030f06110405060c06010302102a03020703020d05030903070b0a0f030b0d02040509061602 84
    0x103100c41c01c0301d906d454010440d03041c400350f4400303078041c41d00b0050f00c55003040000220040c04c92108010640201c050b5140c590381c6030000d103201c0c40340c00103800150300301024410307469420ba40a00035410220324041803130450076035040c64a00c40110040041000074005020086044da019a400000c84c0000c6260692080000e03100c0d028200c401407901685461440c0ea004500001000829004c00c1d5041e140c1410018520349070010810071340002d00c0c02c00001035407010303401200200c0707401011180700d003000b80d160480035000b40c00c00c0110140c410000050103844490041c8002c00c05880504210750641c81040151140010014108102403500803500c81061b2445102d50821440e1000c11858500d801e90a058041e0310203503021a5150340071061003804001070031190011001d440e1641c3d12614080c1071401542945030014503819100d0a500d4025400a0607061004003001000780050f800681903c00c1203c80e5042d5400181c14003203150b01500340307011075007200e0001d030000e0444 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 626964811 1250 626963561 626963563
    0x9060e1918020d0503041208191e030c0e0901121103010c0921081314090408040b0f07051903021006030528060906050709120b0a0b01050408100911030c03 68
    0x41c40750103486551110100e504100e0100102d40c000c02d4803202c1e4210080c400d042c084071541024020361380c00c0fa20783e1450200d0070f05c918030060460207840803004004450110440c000c003c640c05005c0ac0c8070849000d5000c940d9401a154004d0054407440c2c20800780740e01d450648a00f540c04c81e68041c0e8104034041c081990032a603001c05441c440e0b2140043c60240c3c840543c0d2680e4510000791650100003041240d800044850409550580c10001792404585003440110841210050721a41c0c051009200c03a550b80c00c02800100340100d00c0609069130703511010b007000050006441d02d6090035000508068046c0890140b100b800703c802c009241c41d641350181c450700396421030700c011420050b0380508403c0808030607401581202c0204810b0744585080d100610055440c070020a803094000034a140c058106012180d07800841507815413500210140034102d4003c210b81804018032010900c0d2808001121030305450010102e004009420241c034150484200d66001e504456030302c03585620 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 626966061 1250 626964811 626964851
    0x8010f06150e010c080f0403060c02030c06190b03070807082802010323130204270b070905100e0103051e0f04031e1713050a08030a020409060e19 64
    0x10480c1002d8082c46114001220060107052005142590119014081040100c042d20540307101e000300704111501088140e81c1d070300442000c1e0699a00000001d10300720742e07509460340f2007401940f002c50b00141e1600003c1c204402d81c0c0210309180e1041000f0030424100300543c0390381c10344140d940d01e000700e41286580811070603084042d05240d02c40c0e12441c0c000149444812004201003580c44060038114102075014410b20342c145d1240c0c0c24031103141580d040b002c45000c244010815400c010508540d01c0d40b240c041c4c024105024028603103400030380f41c0c55446901d01880310907944c8c1601c0040350340001d0b0890354060408081e00003110094058207600c85005600110200c1c500380a030b1b51140b600316100341d62447c851342500030b20144220303500e070400302505030240f140c40c00415660381c4101c034004c612240e500203096075102088201c017286082004540006900c13401500e4180c07188000800d0312120fa010422030804542080707140190726500308056404254188503041c000900c3e0004c0311 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 626967311 1250 626966061 626966099
    0x5010504090c05130303030b0117060109090504060605040c050403170304031218050f030901080a0e060705030a0f091101020606030703080f090a2d0909170c0a020409050708010f06 79
    0x582c1d100e1141440d14064001da40d01c54100d900407a9410751a0301c0d00401800707010090320301150b004100000b0103c00711040c103100e9036069681c280d159291803c0c040c050a80500161380700c0b6680c05e40031503035448a00882101c940c2c1034880e66615441c501c0d00c802c0f04440e02225901000c0180140b200181d4003010202025501030408070b10441204521041070700e969400600a200d03c603202d007498403002c406800301c3e0700309803501c0e49250b4070680000e00b91610038089200540086c80002c0c4007602610183d41c102554100000e0b180c0c400c28010381c01c0354103811007a1070480400304120569a0304112981d400401900507050891441d643d080d22805404200348076018086854500c9480701c80c520001440c181005182011f2129102400440224895000740b03100b4000410b400c4114000e184400d64002e03061510010482c80200e016081b2a03c064203a000303010044003d41c1da14015040014001d0004e401024a40265503003180d000c032607185642c50600f08100422909064001c41b00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 626968561 1250 626967311 626967329
    0x152411030a181d181504140706051c020c250905010b07020a03021c1704090b03160509071101020a020105060f010c0507051c0c06120c090b0a030e030d020c0c03010b0a05010504 77
    0x16010f14000306081c500c40c0700c45040c510485c03a00b040180301c1902c070810100c601180544880d45d480da9030490391440b030a00040481200c03c0ea06a030064030070fa000f414001086002e480c1104100070442800c0c01207090501c0348400809024018800301c1d1240500400070152644c0c40c001340769001c41e102d03030309512010b807180f00c100382c00d0b442d801003a62354049015445506c41c0c02039100e0800b0341e90745400c6409505401340c6041141d440700c0c00d001a006c1c41c0c414004940800c00c0b850602088403102c4000c04000401c4005800300841804c00d0014103480e6015030008a04c5261010034450b4541418503a58100300390b003000741d80450300c0450010141ea10a030b4224141c45040400c0509507686528000c0000004200000b8110342c07000140032882da0903002441407034094001214501d840b80980c002d0100304001c4150f02d00d0003584040c00196101c0d040e6400d000d840710b1800d04a800c040841080c5400c6030891903107034a420b00c41c140c07030b100b0100c41c120406810600003c201e070059024074002 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 626969811 1250 626968561 626968591
    0x643030e060924040b162003060c0c01020403061419110702042c1f051e06012718021612050705060709050301152411030a181d 56
    0x1d6404042c2c00ca03800b50000608a40d91034915540c6403009140505060712940724600c01f100d44a200f001e0483c400f080c0050042c075480c1c5448800c00304551100f45c8104a40d0350030440040002d565000b41d00f07403003420900405d100e203412071480d02035140e03404a01c9201c0d454101801c0b400c080500542e0a540c1d0151000900c0181c5402c0d032200e0307404a50b04410101d10115610407901c8400540c0b0241100c1000c00e541c0409641034510042c0c5030140e821805106c0c03201040211014502d0040768054814941b04040c40c000740c0b40180300003602c9000722215415000e0034070800a28003d03507041012030030b03011490140d6034118a00c038030703120341d01c020651f441803074440a041c4d00c610f0982d00e15070781101c01e03181503081084000e0402000761040e64001d50074040c2e04103078200401071490845041c10f00444005a000540c8036240401094180a00c1000e46094005100801c06804032a1041d218041422010107010b00307140c00070340c004d02c0324241c1e13050103032040d00c80a0b01e07090304510300c03104040c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 626971061 1250 626969811 626969869
    0x2031b131d1e09121e0f0405100509090a0b0d1b080c0307080d030209060d060806061c0c0501121e02040f0f03050a080d0b03010203040615060e0643030e0609 69
    0x224403240e50200c0c008100c00851707007a09081455008200300d448c1228460400642084152140e006101800381d1101400f000030341d1160b515040844946801000346100b04420b640303100c169650180c058a01413507006044c086e10500300540402c240046004040561400052035039500d1001c510b0030406401040754880c903100c5006841264035031401c10301134075880e040a81e42d1013030100d840b90b06ca500224136510784618000c0902c14050f401902e20000a0706080040d60003a04d0941c00d0407056035260307290980905810484000300c41000c201503035851620702400e41d00880e94000300182c072495241040003a400284003000140d020040e46d032074a03181850a00240101d09280e501540008104410049298404003814007a10042e0a1286c2c882c9400c80380c4800711060603410540030002d8281c01c0801248a11003a08400912a00000141c43d030300301c14450321700300030348110308940010304150304102c25204030b00007a100c450801c01280d00003010100d41030340000403843c41345400b00c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 626972311 1250 626971061 626971087
    0x90306150f10020109050105010b030c030414102409062601110706051807050a0902030408070639081810110d0b030102031b131d1e0912 60
    0x2030442140142403003000641c1040280c007174030101d00c1c115000d52911001049072002d410550b402010781c1d00c20181166999070300c002994260400352950b0384184080e0075100780e99030240344140f80c80d510032104003c0c126555400d40ca405c58002c203600509003031007408480c181180c1c01001f41400c0300f10f40c0e450030780c0e60300140c010030b5081c1144d0a02d00f40010110300f403101035000386000b8000301440c3c08800170100c526544070740d10340c00b8050744802c5138141008802040e4000c0c68020740668000c0346003403020742c0ca100c1100c071540310028200070391803402c0008805840c54500d03000000a84000848032108008141030802800064150b0046d4860b0840c0e1504015103412405180c00411241004410000c01c40d00202041c803c03407820401811014201802603d02803000c28120f0f0ba1404811420103006070030009910f1840c8030303101c01c00035180340d9440c12031400110a0440540a00f8241a0700101d040640786a112203840b07081802010f24000511340600c640c0700c09070b17540742c0b42b020000c9 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 626973561 1250 626972311 626972329
    0x9090c040801050f010503160b0d0908090904050a03020f031213032c041a032e0501060c0311061611070503031c0506030615040903030902060c01090c0b09030615 71
    0x145095031030070302000403001c090340c40e84d8181c9104a0494020841d000011400035265015030048404d0030700000230300340003c0d00070040c914445c40026050581400c00f0410b409000c17201030b5895405244403005054051000d900c6070003403074002e9031600740780010384c01003150054002d801811880e83c0c80402e05100700389050b1900084480c3c2d004070403030351002006040418038124031880c40c0c0ba000d515a900a103007030b11550785015001c2d0502c2020f41a140340300708840c2c1c00e0b090221040e502c486c6040d00e07a5100305e80c003810742030b03c138803542580303505000304003031400500424964071010030b1022540080841813141989071908840400e5440707203150401090707034440e580501c408160702c0c4200940e01c1c0911644218200104629034030401096543c0b502555190358842003490644058200307500841c0e241402030501040351f0620780e021990070741c089043e56145940d50000c080400c0b0404c55140002c050414105040c50700a0001941725640582a003000d055820071100180e25103600b0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 626974811 1250 626973561 626973569
    0x1e0402010c0f1112030a0e0d02062b200d0b03100e0c0306100605030703020706020f04120203070b0405010f1d190e0705040609120c17100b1509090c04 66
    0x4001c0c2c0340c550391615500300800307480618419094116075140d04000007080d0f130707207940c3c195450484d45040326050003101002581c040c3d0300600d08108142c801606601001c0d002c00f504400f8046c586000b00f41d030011902c500140c0081d559103505112020801c03902914188000303800c4c0082d0580c00d10340021b241800c20203100d000380341441c460703202844c0e01082d00234220310306130251480c0c0d0f502d00c41c0829050406005034404240c0c24404280510f1003640507154052081038018940803a61500c00380e950459400441c0141c42c0e503d1000440c142400600002c00d0320440031401c150030b100000c2c0c441c1150700014410445080700115100c404d101140c81c5103800600012074800751400800c00b0780000c1c0c092540c14102d580d000c50b0780248994111000c075282991114040da0801c40c418081486004098079650010000802d00d0341c805211595190b130120f00400f40290280c1c03600d4265aa00207006206000d500c801010450f6a1011240030a0707003201c880e60300b5922801024220301032500 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 626976061 1250 626974811 626974823
    0xa05060319110904050a05060d150204081f0b0409121103090d031115060112091b06050406022a040c051e070b060303091e010318060c03050c031e0402010c 68
    0x404014402d034001c00804540c5400d130703402d100540d210b020f030030309945083d1000b0350040d420050201c04100c2451401d800100c5d0340300058507050303a40c2e001074640700600c0c440340440d640c41190380304441024801c40e216201c09945c2030040d02c1064540520031181c01d881c1c9000c1c42400500e420f4010802c4c02185c5840c4002801c0c4d4400c41c5140c200180700001d80503444d0f080340305000d401003100d01d030a1041403040030169900305503000c03410642c03400f0b80b0b01c241e4100d41c080552560700e000821840440c6000e00499a107158580f46007110007403418030840b086000010f0240104490001803103803034183c5040030750300480c0f0320303180d030310b04460602c55044980f0f00305070309404480250003400e008007030950088000d1502600c540081640340d204043c00b542d400300504140e800144d101d00495110721a0504000802c2c078880301c0b1185c18014503180c01c442542d0f0324070a00384019050311407a60000800500c030f07421840e028100900d048421105445803007500344c0003501b160700c1500c000e020036074040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 626977311 1250 626976061 626976071
    0x81305062a18040e0601140607030314070806040f020406141b06010f050306070503090a06090c170303010e1b070f0c170d0f030c020a1e1208150f0a05060319 69
    0x181003552020b032540c0d6880d10a40c10900c0340301c00480300040881c1030700d2501001c00e404d0b804550800c9000d90020b07804500781034555484000d004032a4001c035201c3e20840e1034003001c1c1d203450400c20040340c54407013243c22042e2040c0810300400703610601854904144400a5507501c4440c00f8581051000300203501d1079120709000031070000806405441255820b6040f141141c0325003809441c54001200e600c0300c1503119210310008211a43c01100e030460003400389aa505444050707144c201c4114440d051806d40c00040100441101440c08580c0420707a03035010549080042090074092041010203086040022050800c0c00b40c80700b2420024128002054441610220300c00d45400d465103880021442400c131600c016801303030040c00380100340e6501030041107005946400c004a2205105201101caa80500000a2803200000d00012850311120142d261024103040c419400042c0c40d07008101102e900c402c20340b90109100b06039a41154a25101e5462020740075043d4110a90032002500300 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 626978417 1106 626977311 626977327
    0x504060804231b0118050603070c050c2d041119020f0109110a06020a03080412210e0d0903050318010c0605090c01081305062a 56
    0x1458011018004007110b6161090f4984060b2070010300c611041419a0800d0812406503020200c001071541807102158036800050001018441d460b40031a040110501c000c4c03104001c007420212034002005088044200c04c808220b004401c080503162440c105409815030051048107a1490b00075002c010103141400841c80d142140140c07131850480d5042802521300050160000f03090815002c000c101d411036035a4040400e41d0b004030441400240c109500b02d9010740c0011440c4160425010182c80c124450145503000700f4500351000114209540304e01841106801168040c48080c00c00380d0300c1b4602030101610320381c803d10521100d4115091520703440101071600c0a05000150b440d070701903c00035079017480c65801002d9094219640b0402aa0380213101070240c21103c2c0298940f95119140a02001003080044484121443e54940c00032005056240c0e1140d88100ad = true := by decide +kernel

theorem cover : BRFrame.Cov 626798561 626978417 := by
  have h0 := BRFrame.cov_init 626798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 626798561 ≤ n) (h2 : n < 626978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
