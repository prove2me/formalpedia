-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5377
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:40:24.582435+00:00
-- url     : https://prove2.me/submissions/c433a5ff-2be6-4684-b0b0-e462fccdf4f3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 966906474 ≤ n < 967086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 966907724 1250 966906474 966906491
    0x150a0509061602150a0f0b1206010b0f0c030a0e0118081902062b1119120209060d02070606241206170309010915140c03070f030f0e03060106080a 64
    0x81c8103c1d00c07035138543c01000040345000c140c028080e01d441320b441d14501d4500200c3c0c030020f16040c203503428a4022800240810b03820104055890b80c00903e000e102048103019074404400100000e110700c0d40c81d5903460401316400800036140700350850700c00d404140c3d0068184511400002d01100c00c02c000f040d84e18141c003440c00803c81074421805407184421240c6d410740040315200303014956100171503c040006884055500503c2c0c082c4002c0c1554600402030703461020740c45031084e200f003c25810001881c03d814400007030402d51025074900100c50300403d1400c240b00c018803d450061681130b8100d16840d02442405200040403281c002c1400400301000c00c81c4002c0e60f0141c0050b220a852640d405000c40d150250789400a805072400100110400b164014803142e811441514035141d1201d06029038045800c0c0307421040441c242440184807110104540440d0810f0503030094441c04210200090b00600c05105c082c0b0150096203e44010003030b10b030b84861229031010000710300050020 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 966908974 1250 966907724 966907727
    0x50603152206060906020c04050118020a120203090d03110c060c0d0b180115090f06030b03010902030d081603180201030b1c08040609050a031106070f080c150a05090616 74
    0x4600c414041d41c69072402e1004612030f50007081c4e00060f5030a0f502164000010a42000151003003405640382d417020b41144a503811403180c020700072080417420101800e2131001820030498004a030b600010764003035507403c6141c0d5054810800c0d2000e9050329240360458110b0902c2d921803010b8144013600100240c50340704143d031030b4003036045c41c080284507412004042c020000350f203c080c010144051158103902c0352060003852500203d441c90352101078000d14018040d80100401602d144d01552101010300050f90b09005640400b421516100d500f41820502d030b0280f103d850141105142c60301d06d2500701020b01224900010b40d0901e40401c0941c07840c9c0104100c0c4003600520b907541c41940074128100070700750001d00143d41050b91140c5a00b5920020040100303c103100241601071888000c0c0d41c1c60508600034440240030340241d00104460360ba64900c1d692042c0310000e0540c00c80d08002118841881546801180c1c00704140000e0034075a4013140c4451004d0000c01480c5030b085500b24540703 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 966910224 1250 966908974 966909019
    0xb040305030c0c37020a032a180b01051305310504050607090e0c030901020405030d090e01060f1d0103060b0a02010b0a0b04060804080c07031e05060105060315 70
    0x12005004e441a00e110440c1303218884040b4100c40d00e0705078080c06040c1694105201070040c180d002402c0e082102d2440e00c40c200c80c115402c103048006228104e500114202e0a6400c00c01428266102030b83e6041e00c01a10080324002220b00b1b0400200b08440c05003000d03500c45420a0391002c0362610306240710900e4441859002074100c4801d90561190b90f403075008940d019902c01c6002c0d00513524169a6114120f0b00018940654030205003a0307404540042200c4010b503600600d000c00040c9050b03298070005e07107484000700036140004d1f02c1c0001070040400900302c060041900e8102642c81da20280b00242a01402003811400f5440f1925000d400360302c030b900000d0041600b501c007180d0768040d140009002c0e0140c10125409014190784c00142212100201c07401c03503605039200895a11142d030384070001da0102250215a1003400c0c400320100f104032801d6950b51746621000032505142d890464180b400c142d00041c0b09010a10421440b61194aa81104501e003150140701a00360b505128418 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 966911474 1250 966910224 966910237
    0x40b28062111270f04020415030f140f090d050a0f1d1302090306090d020c0d0309180903030b030a05070501030b062701090b13350102250b040305030c 66
    0x8a003155000030741c1007050724104503200f0a50f5040c0f5a00701e9402032206a03c1180320742d18105241a9000741101c1c42039101d003007600315003080800c441c500c00c4090725803d2804e6a403804120303008010310806239020800380c0b14542e994201a800e001c207556015100c1303082c948040d800d110010400e60700d61500040140c1280c6d070000c01c81d20310355101c040c1c884020341002c4c050bd4002e1080c1c0c404a4010500058000113900e4039900030002c81c0054004e1007440000041c04406100c03c0d0b100209250f070744500c031015040101e880018614006080040541d410781c0540c070302a801c20955903000c11008550481516000c1c00c020075950100302c04140d0b035101e60a050030031f800303003094818904025101715020207102640c406d0b044548034402600e092041c1419506501d8903141c007001001a103051036640e540243c9041104500c0354802c0e4100c0e82d000750084191039500141c10f1415641e000502107030001d100c1401e15910300980d60b401e44807000600b02909004010002520001c0d4006c116082d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 966912724 1250 966911474 966911497
    0x11b0f082107030507020721020409020a08070303020c010e090601080a020a090806090a02010215010b071712090a0c060c0507090b0301150f060833040b28062111 71
    0x214070b0700c0c0d040200240400e40d40000140164040000d030801c0240c00e10300c400c048a01c103c510500c05070708000050403d0310301240c0089100800081e015024824480194000d070040e200c80d0750500700040c42c01c580d40c1c0c071980c03044071850203021850b684168065801590700c040141c2c2e400904005a0308031000b81c1c0241120300c0b4000800c100c400c008500c0c1d186a174401c2e002c886a6210b805020f03069403400740a4901c8481090160502103012855000d403c01c510380341161a21090040190f0700a400b19101401c80c1c0c4050f00c80c00410801000d14401040c45240541203802c3c0c40d5240d9803500503034440e0504040e11040c0d0800240e17800c0d84090f40041316a1303021620165078400803c086040c42c424240401c103490b000880210486104540e8512104400302802c8200c000080810343c80c0d10480f81c00c46d55425402d64507899210051024000b121240e10b01554040910790000b0142d0300008200a603013a854006c1c03400d001c00c0080c4401c40c0890104203120088004110740c082c401c035020 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 966913974 1250 966912724 966912787
    0x9061a070212162903070813030c020a0326090d060933060621050a15080a050705041803230f03010905060a050a0b0a140c010506011b0f08 61
    0x5003200c020382d881c1d03200c5131502d03402e000c40410b404e0103060038001117510701301040c01800043c460681203004501070a100b4107000001030410340110b56030010f103810850320605000400100350303850441c09803410280b0307001c1614040301d50002ca080610050401002d464440a0b003030100040c031504100d160054402d07401c605000ac016881098404418801c402807600a000c56464843c070100c3e8006a07004142006044040c4410001490700420240480e541d410368080f507925a446840010074500d002410301032034a080090030070840e41e120f94803481c230b0400341180c058002882072142582500f8882c1d0b4080807044100d07082c441241540310805000104800c002c030502d000366051f10b945540030085030303940106003c001c000c1409415070002900c41e041062240020090101180a241407041c5888840c020b0304076821035403160440d40d440314108071165920207105144c5288982841044214644a41140201c1a580500941c40000d100000d0721442d10146401c40d151505c082d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 966915224 1250 966913974 966913979
    0xb220803030a14070c0c0608190510090e0705150703141207080c0a090b0d090507090504110a031a0c0f030709050f030f0c040f0b06030106030609061a07021216 70
    0xc0c0020001106003845580f140b0020441403845205155110356210310031a00c3c082c10900d00f60f4560200403d915540c14004500307003120882802a28014103201c07603004030341030520f00c2e000155600f403a201c400b283d11880c0200103554811004240c84040c810300741d0740c0c5030700b682002c42c0c6407480322004131070303a41c6c0001e03041c40110756804041c0e128098950390b1203a5a00e4001c10300966220f480c1c0440000380701008148086244500140b040c01e11120001a049005a91306414020381e5400304902c035644500300810710000300070148000000b1680340281c1402c694446028140d88a00026a10b103a00001a0418845021219a010040c801c076483e4031348003100500e408614062140284414072120b031160a0004170905802003800c0034021075512241800004c2c4400c0080c0300300c3ca03446000e034180d0343d04c0b05002180030344690355021a4150420440c441543d03010307408a01d1b14640703a5400c075000e00b0510705407a00d6a03411240c500d44036004081302407a0010b201071010300c204105800 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 966916474 1250 966915224 966915241
    0x2d0317090306011806210209090c0d03120c0c17030a020d02070b0405010e0c010207050d110a150305150f0d03090b0d0c0e09040c0303110a0501020d0507030b04060b22080303 76
    0x14035400442c4c00e8030920100d03031180c0c50014116255901c02d00030b6290740508800514100202c254002159070803204d802d01003400049204d0340d0080c0940c0440e0100760384240007070341c40c040c840c807035070071402e0091103a25a43d6410213908500e40102d101c00b080480407440c40c03000c1c0d404a610381503420000355150b50041c2403c543c00d0100390f4085499620b0994900d441c11008680716841520507000707410207526010078482004108001100d4003d894110039000c0d41e0781d407920801170044403100d800340b80819a000740845030054943c0c09441022028900c2580c1c41c0840c1080110054034070407042225480d00351044419900310750003626000c14514002807450b80060074049042e80c400700340015060610400c41c8040c0d44c041d0070026210014000720b80907003070851600010b0002c541c0701190984030103003280c000d00c07080c0710941e860310280402c043d4140107500140300d085804029851500f41d1030a00b9100c0d0191f40d50b0403011011000142050700e035502801003090f24180c0c1c1d50303071410845 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 966917724 1250 966916474 966916499
    0xc23030d060918080412030c0203030a020f0601170a080a121a0411031b031f0305010b0906013e150609090f060a02030a02040510092d031709030601 65
    0x10b000d181c1031800e242c00341c01d0820464460078064000c2c5a240c81c003800e00c020385094078004c1e107059041c480c10410050040e1801c000401c49004540d0181040d8104040250704001d01a808400075121a8641c1c420111000c030706040b40d15402031506a070383c00000350550b8100c0e99460303009009031a04025990090401d010100c41040481d0100880354410f0141100ba000540d8802603047c1c4c1c0d03490802e10320500070300441c1c10070383d24540101e0b0148002d8000001e05400d0304112090b075151000b15005050910a1942151090800090007108080c00c22152030342a048050a501030f401c49002500007807141c84441c0c01c072034060b201040b071000c40c10100700a040c4d400c03d0040c1e12100004a100c02d011500790078150791003010f00500e4403642400d0010307400c007034645180b01d9801c1000080c00d594400501c984501d030780d2282d00106240c024080c150311070380c00008040111404040320340303036110012801038039444205100e2001080070352042d14003407032410702e800d8801c150012488200210 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 966918974 1250 966917724 966917729
    0xb0606131503090c0f0b070b040501020418060303121b0f090f061e020705010503012c011502060a020c1e030d021c0c0201060f0302091b0409140f070c23030d06 70
    0x1c4c0c50100307a44d55509080204102d44140c02020340288030710750010700341d0301c45560007601880025050030f0702d41010b40c6c1d2a240d03150480403a15511442001051381100c244600a82060790800c01d0848034068601182d01c1d031048001080945401c2c03132aa207010360b10780e902800c40000400060754480201405500b8220703003130084107103103040b01550307036100003000c0c4143c0300b041e900d450441c1d2131301800c07440c25092000e998001d0b0f40117403200c40079003021079145170003040d11941d044010450780801030300717140000c1c1c00499075a00402415a4942d80000c103040c580c02c10403080c4d4810b03d16010400d046000f001e01c0d84501d24000140c0305031104604802402c0007444003010480480819416400c85030715120702c50265550702010409443d1800c1000e07800b08006007000130812010700c420301c2540c8640c00c09d419942d502c0c0407140148c11151703205035014610302d02900b95400e10800203403601d2444903004181d60040440c60110059600b025004d0380300c2c110460351a103e00002000140c80f650 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 966920224 1250 966918974 966918983
    0x4050709210c050d2d051203070f0305010e060f190608100602011e0c0e0a0b1b03091f0903120c021305070c140309090f150d0b060613150309 62
    0x2580b0200f114500900a0000c440d8000013441080502600c0c40c00c0c2100a80d200d85288803403528581d001caa010700405036600d400d1b1182c603a482c500035102415800e103d03807200e0101403400d40140004000000c400c3e0308010112a9440603074245000a1001c0740c481c40d200898050300342000600340c1c0c01400c00c0e0b00616120301c484024030b0716420220300f01e9408049800341c1e4025205507203640311995015614440b00c0e89001034006e0542e9000c0390b502d6800d50f11242d14904006041840248801a1680d048241d200070b10301d042c552000048440e600f5046160302c04110b000d00d14940c6004e581840d0007580d00c001c00340300200240c1d80141052402c034100381e0007060410240924140b00307220713191050a45817503102000300540c5414460490f261050040c901c8100a040c42650340e091001c1e100350480040c5901d545005603078000d41814888400740201c0c01e22030b4040c0005d00b141030850340210281d5034030b51541401207844503940c0c0c82c0c0d800015400042d107251012b81b5450340010010174002c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 966921474 1250 966920224 966920243
    0xd1b09240501020f0a0f030c080c06090708010213140d050d120f0c021506030709060905010312051207300207030e0f210102120c0a0207050a050607020405070921 71
    0x41d0001a61221500c2c0519452500000c1044c000100318030313401214140a850402d907540305136600c038840c80d80302c1c0700e02c0d00ca150701c40da08200e40714030200016005804000020740c180001803104600314042400b50007281d5041c0704517070381c40307480d10b9480076103260300b040c1200d00c1201240000344c000000042c05484690520120030f031000394a000701c0c40e212201c0e5005001034124020380e8251188081c0c82568140290003000400c940b50780a000c0c00b81c510100e0000c1c15501d1880c10b5140360846a0320742c0103010007480210581404000055400410b41c00e000500e0910440703c07000a00e588070403254855401c00091408940315030140140500c079842c1e142d190740c1e950007000f5800c01000400782d400f4800d2000d0381006204180580281c0c030400d8000740c20000d5440c440c1c0b4404800326022110105d020031101059030f810042e420042030190b07003004001e814240403810718401c0038800382c011629900800d60307035803154850300010310700c10340544492103042d5228143d00c80c0069040d6a42c180 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 966922724 1250 966921474 966921479
    0xc120303110702060a0f030b0307060f02101a1c0602072901030b0c0f090901150930050316230c03030304061805030403060c120b0d1b0924 61
    0x10300c03004072081c8940084c0b07903034181a04000100c03010702000060608060311442c5800d050380342041480003038403d0f91201c443d91011100300a1a08244483c210b0300360b410060198071002008800000c00c44003603491401140390340346007520f1310001060082c1a1032000035248140b094550a84030542405000d49060825030701a1f030140641c00c0c00043d09005084c2c0200741000d000400402101583e544200c0c18801182c0008028080c00d9000e090a0071284443e642245d0340011084040d045c615103541503101c040c41d181e4000007034245090201c2c1e1040c880f140c08e003c020402d0b01c07801002c104203450341d001a803912800442416601100401d034074020760058100201c0c441d40c0989010b8011401e654139074840202600d1032a44000c0a1100754a100010401c1400108040c6001703a4020862001c07070100107190b10b25900d041400c10303181641c0d03400b0a40d01c804036040c0554010f101c1e10600d09448250440181182d40894801445d004d0201115a0189403a56510f050500034200302507 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 966923974 1250 966922724 966922751
    0xc0a0909020102060a0203100833040b07140d1a10030606021914030f091305040f020d11190807081f150e040f171603050906070c120303 60
    0x1035103400000e000d03800c001c001071101e00c26580a55404112900710b9035000750b036850f15500b0100d807a482100d0075244450310240ea40300ba080441c200960340c544c0d80f412840d01e82c1b541d944a8401034071034410040007a440c4085880c0e40000e96015240401e001c00c224000c541c0e03200b588240c8009400d024143d00c40010f1010340c043d2041b0700c220b03800c0f034015140700d080d2034003009011002d042c0101d64a030001490f00c1d814220820140a401d000d41104580c1c40050900b00f0044016500c0405081e41c1803404200010b49903826889920742d0540d000c10f5018807500d48120510444403006030041c0716444044569009000c004084900b41d80a031b900007512000c00548600354002485c03080c1c1484104203017071444a600c04414079201d00b209184150310350760b02c440b200360300342c0d4181c603220002100c110a03c410800da00003007090f0306000d140341510845048a0700f41003000c0c0501444004607802410b503c0c0d00b022968001d60002aa812043c0ca80000005d20f007603210302940080d00c2d00c00d50f680d014 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 966925224 1250 966923974 966923981
    0x14010e0114010806040204090203070224070e0103020a030920011d0a0302010c050709090305030f090601060e01050c0c1338090a140c090319201f020c0a09 68
    0x72100d0495400c08000c0c114015a0390300800780009801035802c010014000d10140301460048503940d010702401461600d044243d904070150344c51520411609100f4000d4001c4800307006000c00b820050f071240c8460f502600240a040006400c4549407030500703949d044024040d80852000340c80e5485c40d07040c1100700450b0764001d81000794100010340002e002540c0515005520300348180229030900d41c03101c0014050321802d10086004c10400300c14000d52002000c4480d900903103007002841290f14041d4000c1034401c80502c2141070010010300e036800d00d031050000003080c0c08007a044250f555910140d803030042444901500801008540c00540701c42c05440501481c40c0c0000e684961181400400000e9203000e00a12211641c840703603041880d490800c1c140c0324001500d0143e45603140c6005250510840200c41d2101202c0d1206a4000500c41103850f01518800f612840a5980c5400481c2e168503865603003801c1c510540001c00c140030303400540c03c10761420607241000c14958410ba4041036 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 966926474 1250 966925224 966925229
    0xc0206010e0601050c120408160602030313140a2f090412031109040f091104142403030f070c0608131202070f120b0114091303020a08030a14010e01 65
    0x20109040301180310ba602c500c0140c16201e0200c0142e80703046040e14002c4811b40d01561040c001c6030020603100410103c00e99421009005d80e0000d5407440c50075000d0980035420301d040040600031110601c17401d0390010002c250080e5805030140f00d85140000c0c5081c01c2101801154400c2d281c80c2d280c3c400e244c01c0950b4594000c03603020303480980700c1c1e03c6c0d10b406a01030300403883c0404c021003040c00003070900c0d50f07076005403e0510500c180c00248844103080a03145441c062800a01460078903006002000d0484050743e84090020071b00e01d5109004070b400840078101c420125031521021408100005c80380e00104421031042c0a46840d1556400d8282d807407100441e0050306406440c0c034030303101191107807200c024810002d20690f02c40702d840e04e440d41e0180000da0031480802000302403241c1003180354238800303014040031421200004085800204000401818000955561001102014000c000356004141d125a440d5101e24058841400820b1200742c10301041c83d580000103204100004400d05 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 966927724 1250 966926474 966926489
    0x3c030918090203100b18070c03021b03070303140d0c05221a071b15020609010e03070f060f05011202030d0f080a0c0c0606030c080d0207050a05090a02070204050705030a0c020601 78
    0x116139040341d1010000c220054155070808540903401e030260040141c03003072080e4051345880c450314600d403c1c024940f40741020440d20400403851034558030f83c1c000036840101da9040c641641481500c48000c02c080c080d80c2c01100711541080485054150440007408000000249589242701580420384001480b44503c00f42e001400f01d0030310743c2c841c40100808a140c05a2280c400d5011000609241c0784102d6114840304800c07030724030658440c6d0601c4000d030072216020080c085100d41010083e203d00c0f500c0c1c0c005003002280c0340b2100400400d500004860300391550208071940c1e4418400980308007440040b8468066413424411548c010300000c0d440e1025983d52041c103030380b2540800e005009113420b00c0b042c40203211192000038010b00901d000703940324030700200e000c900c0e1201d46842e1040c20190341065400c01d40081c0090f07113501d000701040303600c100c07011038464440c100c0003c000d228003d00030350000c1c20b1000300803500f50041d000750700400e002c003c10000f41d0400d040403a11403000380118103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 966928974 1250 966927724 966927733
    0x903170a050d0b060c0601140f09011a03090f031c050f070804020907020f1603020f060f03241e010807050f0f03220b06010e0d3c030918090203 63
    0x104608450303000c501803034801380c031480c50030101e5540107161510992140d03001008980c24507803103003000481010040f40c1a24490b03155410070f0301452074016400d0300002d070b403100400010b0000c1010014070010030391101c2603a43e2044801e035030310200c603808174a01106904002c04242c078024081009841454140d03201c0200f52903035070030071100e40f101802410451107990765035a00080c0a100c07040d01c20001258110840c0e2852040c020000d041c0b903074203441024107104200380c00352200304481c2d00c00e0440c0e403520000c01280380c0200d03030300d0800006035030403006944141c1c40021035400050790001c0e0980714a40d80e5a5401c0301140c052103802c6c04a00d90103018040c1c14104e01c1d20700701a40d0003038550482c1048120f982400d0203000d148100c8103442070350629041c0115960403040c030300b524250607190b815405000382c4842301003202003450818504a201c1c5440e241e940340d40600440b00039072600e02042c000d03075410014007040280c054401c51111400c1e1a42c001e00091150420340d507809009070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 966930224 1250 966928974 966928987
    0x207230d060b060406050c0601080309060a0c06110d09060605060319020f0714100e0109120e030708010e030901120b030a02220f091b0f1701020403120903170a05 71
    0x149000c040204503070300d540740d0b078406455a8400c0082c00142031613948240d01c814003500c0b038501d840b5040c0c0c44400340f90030030000a02e15883d00710850b4064801428403422428091a00b03c00038040414440e01c1048003003811140c9107600d41100c80c280307020390301c284445519602000200c3c803040d186004040400c0d03c80b1208a43e20360040c005885a5008540c01e011081c3c4411040c0c80e00940420040d8104031011180c0c03429911401d148080904000c11000c403040e0b50b11104841502a040c041c05249a00d40d0310a0390100000b030043e241c010003e204650207040c8143d80c0b5003001c001c10380030450b0514030080210740c07441504104080200107024882c0701da000d1144c83c0c20610280c03106d441d10615685002503140c002d03c03034050740c01c2800054603503260800491410000a0a60190030100d908100007415440c101065402410125007000d0940d580c450083c401c07984000c200400094041145907003005141c400c40c0c0c0140341e101002c0041d8840c1c0001c620a51030440c01085048c07080 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 966931474 1250 966930224 966930229
    0x609031e0806032a0a080d14040b0904020d0e0d050a0912080d02130f03050303060411130e0a020d1505030d0504150e012c2403192a020723 61
    0x30b030601c012a0b180000c1e00e408010070030170000e6400091007030703008080c0c00761001d61024001100c0880004054201414443d0300341080c403800030001d208940109002140e0001540541010b16440c4100c0b942d0303954a40300600141c101201080c040703500c0c44000124410300c589030148890384922114030300000c0c20b45690082d000b001001b100b181d00408041081c5803002c02c50400345010710000c43e1a85031450820040d15840b00014902c402e06204410303002e1410010981941d6040001c511a9514081450000c0c0500c00f66040e0140c1130542c06c01040c883c401007401902c00030303010303103a800784a10030588a40c4168812603d1102c0c43e03d00711002a841103900703040089051410303881ca42d00324106082005c450304228003d10b840070301203c5540ca090500300c946054902c05040c048403080501014a020050492881f01020a0003400c554401d600c296900c24640c0c102d203c241b0403c444521408094407070200140c0703e02c03070f00414030000043d03140d82e01d2480250030350f2041001805 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 966932724 1250 966931474 966931513
    0x5180a0b070c120801030b130312111303243e03160207060e010f03200309030c010509060f010b0a031d0c010905120604021207030609031e080603 64
    0x1114080120014029000410300310b400f84030348003141d80c2c07141c40c2e5045041c460a0303940060a8154650384038100100000d800142858056024910008130384449501e40e0700319203d0700e2609900141050404801c206c1c20400140e01d8000013004150441042883c00080f24405001c03035960320b0014490010301000c0c41c286002c060054aa90150012100016149a0010303240c40c2d003840c9800b20000a02c81d4100100e0008105034606800390090090001e40925490411202055102c02d0b00b4582d001c0e204000d40400c1150014031a43c920705030b00d01c00e03100c0e00480700c20745142d402d0401082410000151a6014401d02ea903016034507440c02c0c40c07801540e0300261182080c940c070b403840c92154000e100c6669500d504075402400f01c602901c000140001c8054100340d2007420075400c011aa4400041e086901660685030840c15000c1d1856403441d00c60300754402030405c0c1c24011200d00701540001041c1d0054140014142900c4622030b058a2400c801c540040d0158000301800c1c40303131452200c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 966933974 1250 966932724 966932731
    0x70f12030e010f0b1c0b18120a0203070b18030d0b030c032d1b1504090510090f2a050c011a030d08090703080904020d050709030605180a0b 61
    0x100010300c0005202072a003960724041e81e40c0304072a40c6890a00e05400e001082c5080c40c400020090741d12074003660b5551013110050710400e00710203040700e00840c190f03081011600d00913001462940310004010000d40c5d95001d031070100c482451100205800104a030201c4100450210146040c4825269210002c04030b400c00180e052081c0b6440c440c881d2810b00141000c0021541c500c3e040c1080d10361146201442c080b0742451640c0300c1c4000003242503419445030060402102d002c41c0c02c6d4006003007a548c0380169000f501140c0d00d09030910814409080010040390420307082800001d000054560807501c044090104100c03049440240c04001d50101581850250401504299503040c5680c210384400e000d4241c50548a100b00c0491701d03042109041e005c0755464401020310309070b50250740b141c4e40e40c4001011481b0103d91410305a807a6010b48082a0300c00f0f504004503c1d1201004110840e41e100a0710030500d080c010440b443c40b80440b04803034614040080103040c3c41c130754600d0312091005 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 966935224 1250 966933974 966933977
    0x14060c0d0902061209060103020f030307050c0d020a0f08100510030209070e011101020f04081b0102070b0c070905090c04060b1908090c0901032406060c14150106020a0303060b070f12 80
    0x10031488070303529994113001e8050244000103009540c1188107110055800c0590144250300a10a80b0001900080d000c054440281d508010783c010602c0815818202a008400c0060202c42c000c200c0c25000503081c8036803c1081c500703024070b03110a03e02d00719034262030202a410050307260000d0404c5008100300400c070401032404034151840340509a0882c1c1200d107410114041c0001e08001600003084001c1440149a518017200c0012600207559031015214881d4200030100f002583d8003003d01a1300c00404402c03100307011b2031404009660322810a41d5081d8811480d00b0004078035400b079101030354070707014049030388000e1180801c0703080c0c80074035004054050500c00c10248066648074a60180e00851240c070700310000c00800c60f07002d83c9011101c1c1620703840314500601003040f150f1001800b24016040f03003855043e00c0074402075030300304804041c04510340d00b07500000042c8554000707860078180c0c0c020788c1e007040340c1611028001d03050711407803c0152140b0004c2982d400441c168149060281546 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 966936474 1250 966935224 966935227
    0xa1e030f1b0f12030818010f061e0806010e131a040209070f05030112020d120c03110a0206070602070501020d06030c08011d0601060e0d05060127020306011d0d17040314060c0d090206 80
    0x62541b03017030a580d520303002080b803291504410007141c0070503210301c0482c1c2980701d8446402810702015a41d918414415406404008404140111000c40c43c0348186a00302c1c4200491044551482e6060301068034124092044200051402071140b0004596078801e43e4405203940d1030240101c4d020700e82d000d400ea9002031010003541c00a00c0c03801c2a0451150b15407901a070341c5440d400d010309414201204000141c02c401d8bc031400699a040c02c50b14160362010b270058652805007003207802401414003502c849031403c803011050003101ca000d202103e440f07200078042c114000c812030300581034074406481d03103500c11401441070038018001888090005007400b000b030300403a03c1c1c4c94a40304007030f8000c505e05161040c0c9001c803041c6c1142c414004407840076044d499420a0070000b80042030400715007400d40341405802580380d47d440b200c460001e4200c03800d0044840600c010301c5040d0700600c011144083c05a2a1011186d40420303482d1046515a0451f42400900f42500c40075190421003240d000340c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 966937724 1250 966936474 966936511
    0xa091a10090b1902070501091d0a020f1c1b021e0a120806180103050604020d02031006030b100501020604030c2004020301060c03080a0b0a1e030f1b0f120308 69
    0x5848010300054102d00f4a1620500001e2401a0420469030407140c1080b000320340078041050740301c984401080300d4601341032040e522030040000a0003944c81101020328002052241424030160320746514802000c20001442034400c0030845807103003c80d01026801a03680d600f002c518102110800d02d01400c2621280d40803640d41c2034100040180c0d200110748414248003107410281d001c4101803c039550305254550540d2505592004000c000902c2501d424001c4011514280310b80180c01c420601c003401640c2e26490000510381d02120364184034015407000194640c40021003a010303d401d6242c822001c5ca80c4d80302d0080b060030005034902d0201c40640d90768483d40700d0f0310045000381003581c1c6d2440b0b200651318000b04046c0b009448040340750705001c030720902543c45865280481c1c41081c009039520f941d145140c1d115103216407000e004e000b0708060a2040c081c10f0b4507007441d881e42200c0042c07845611011081e003001064002c860080c94085041c0c03000074040d00800d504844021782c0520704c0344 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 966938974 1250 966937724 966937739
    0x1303140f070f1208010315020315030111040513091a041e0b0f070906080105010302130f0306091a0903032e0f080c040b06090f150f04050a091a1009 65
    0x9011190442da041100c1420394103006074000d003122040c0c01c0740b80003401545961160680c13261001000c03170404d54008041503403003040a040081000d4050000e000c241c20005881495070414410076000e90170381340c0c914125158510420300d01c294098500b000b0b035644515000803898005004a860820a41221040d161110742200c41e883c45001c805032145040300f1024841d04010340240c081c40f022003018030a8980106103c1c0c10f44800780380c01a1501c800a160004440350b0b82d2143c2c0100c000010040305114503a00702d80611409030182c0307400d513580c2001d004800d01044a07001a15042400485d0640c1c0748610301d0540e03000c032001150b001c007109000030b004009a992140c5d480001850f020011608107104800707480710101c4003004207415101c046103141c8180d0350000d10800b102c24032003a41d0303603450503201071500419100c551951540e440d80031840c5c1c0306004803885030340c00c80d1300018281051f00030041e00d032044090441c600c0c200481030000b150292041e082c09c1c0030a8410125001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 966940224 1250 966938974 966938977
    0x9090608030a082805041502070b06090702030d05011403010c0810030b04230606010f020a030c1202010230060604051807020f190b0c0301080a0809130f020901171303140f 75
    0x8004030340001707158142132610485800540014488290041c030007100441ca42400d05a40030005541d010b170aa03643d902c0803030952180c400100c014a01e4540081580111540c2018010700c05500030410034142c4401034070507480442d181d200e5040b88010a01c001211840386c00c0d001440f0751040807c0d0b8000c2c0c0c9020130003070303c0b425007003105a1000c0d041040a40e44501d0888500d0080d00292540300c18548000300303802045880034115071038900c20100350030710035411940300c0b0140186900d4503905e48900001c0341c50482c403000340b981d00040045071076031900d20100c1d800c803a0024440380e540c6034104c1501d004a900102000d040d4014910f41d4400c5c2c120034030904060b6801c012046440b44014a0000c0c01a600600010040d074018001806190b0f0000b5103a004950000f02180d00c3e090349000048003c1e4808501c15031882c242802a400c056458001e4404004240c0381d5101d902041d03a001000003004a50410401d00191600b1005c03c2c090083c010384200c52007c014a080e4280030074121a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 966941474 1250 966940224 966940291
    0xc060406050d050a05150105031905040506090601080111030412110304090204080f0c01140309010605060406120f2f070b090d0f11030301090e030c010f0c09090608030a08 75
    0x21a0380000c241c01000711500c03c00d584520303440c40030089803d1001c0d64081d0611560500d5040c0200007001c030b441d00f00207903a80401404060000d00c030324a041e2034041c1d00c40c2e10503030300380e185813056030004140c21406001d49034262681084031425a595516040a2106c010302c2420510a0003501040400307814001032016000e8400003581c2c80d407070516403600d001a102d1180710700760448403908050740e078810003000c805e64481380d030356440c1d451b401c000382e00600c004d0380b0807036020780b0000740010503d030460003d4000411100c1c0800c6003031601d29000003510320041d1a4001038600c80d070207691841242580000410004090301d0500d00f00da075440d49560030566203074006601125004035665030014034413140046a281000342c80298205c00e5950780010b0040b0400d071529840c002000b501e003001600d05080c0500020301070744401103d40d90003807807034030900d0000445069021030041054040ca20032130f00c210300110700e030824000d41111a01c0000d0640c00380454040280c90701c4000020386080c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 966942724 1250 966941474 966941477
    0xb0c070f1406070908011406150d090303050a0507030c0f0807050d15080607020d0c08090d06050a09140a0807060e03192703150c0e060d05092b0e030c060406 69
    0x2c0340c24841c00140c920380316680041c080b070381050801c0e03184546003102d1940000d420b0344d5280080c1d0074152440e5080c05088001c102543c5020000401e0660503000507002d445c200d1000c01003902d41036811400d07200782c9a02080401d20558a207503801f80301c2c0c01c00755401030803490440e06000d8030520140035919a041407503860300c2040002d0000352028032a442d0032031002c0c00142410498254050400201e040b00501304202c00710704e01d07080346c43d0345135015082540b001040103140f60a081706801010707a107405581140f9400c028a132114000189290416003003662a0300b03020880d0303076510140c0310100c85244540004d1040604600c81c00050303080490103922000d5102501c00008103a000f04c2d031000803081c0500d1003041010441c500302c424070740a50040007040042807030070280c070420f225030304064021400144d801c3c000491a84400d000301102016a070255014081c0035100d4085c50a41a012002c810b100407007860207061800c604580180c02e80b8142117080b000503281e0341007175128a0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 966943974 1250 966942724 966942733
    0x3061a0d030c08040f0e040b0a02030f0118110f0309060a05090c120f030417010b010f1d010c020a1d01050414131a0106030c03180c060e0103110708090910030b0c070f14 74
    0x80001d0384102903480400c4c0b0002b18158540040040200d0106110b80b080d03150301300d000008850f0b21600100c0c10300c088041c0c02541d805803601003591684c011100b4407928080c14012510b0100c07a8040c0d10300401810005000882c0a8010019070480118801359a40304003504143c4c41c0c03d0502c0504000c00c0074940304d6104080400842d2300751403145c481c2a0402082078020741885420941d00e000c150000f003102c0f0119200c031801600c040a021070081c3d8405001100010101d44441d040c80381c4450441e940d2400e641d07544148010383d003c03078a040c2107000c4440c0000710808681d48224001c6401070718070409659050562108248007a040b01d030009840740c80582d1000d40600400c82d084030705140300521210a0b4036484401000e500a990400c544004c180700240e1081d006045c94242201885944847c6443c2405c0e0030713440030200300c0c01603041c3c10000c1e43c40741c080394102040700d07042004604940d548181c0083d555002110417a103010900480300d01149600b80d90f0b074180d802c50300062 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 966945224 1250 966943974 966943981
    0x18150905071a0a05070813080c1003060b0f090d0f03020a1a06010804060506040b060f130b040e010513090506090a140723010201060e04080403061a0d030c08040f0e 72
    0x40c104001d54100001021081c10003540b904076000498015540a240080c1c8810061415030f80d07600c02d0300c590342c403d1805081d0104d60050040b82c44a0000380c2200c45043e0305040f20001d400b6299644180b0f0104642840740d00030381d105034001066209001011031354440e21aa5910140e20b01c0d0340000e400680c800701e0804204520070b90410390b01801d0000030441441c10200007441c03420020801040a62140089001a1a5a0080c260078170000b85030070b498030340e21000304e5003d07009804080b88000c20780d9000200b240e540b00444098520021042d481a803c01040c0601804052038003400255520225000324000344030b581c0c040d0a10300050300e044032060902c40c0c0a201180c242d2419600f10081c00c010114889124040c9661110b0001c8400c03000640141d0041030180d01070510805003500304030030850300d4001001680c0c4117880800c003859240e50856500400316040320b412600210714031021a00404003c40c50520a10a0034a019110036241400b0f001e00d0b803101d203908003280c050 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 966946474 1250 966945224 966945233
    0x70e0306060d0f0201320c07090902060a0c0503091c020103111c110903010e060a0e16181d01020703030f1a01051b0607080402031507050904181509 65
    0x1580d000071084a0755607001c04182c482c1d840040c44100c0003410700054405807207a401d5045400f48000c5103444420241c40c4160742c540840c0e0340818502070a5000703940c8041100704151186000040d000340140d4108441c0c080d042d07d4650980b20140c6e6548001e05c10303008a41d440d00d01f8000c03650110800143c0c0c003001480050192584200324410b28201032142c0c4000090340c44540c14012800c24010610910380100c0d10254401e41070700b0342d055400d0801042da8a80b00040e4603004c2e0541000810007214144a002d441d40070701054021201ca4118081240ca03103400301803460a6101600052141008001c404d400c0d00c040d0202c5030903940109144043c507405210346803602031441c1080c00600710302550f00f16507a84084015052150124440704ca01c40380b41c24041700c0e03050b0801114118107206c000600038081c103c0c0d0481c0b19200d81d210a261104115440c00e001e451180c48003410702c6510f404000150280008694aa004140124010920751140703485e00c0210010b0028004440c0d040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 966947724 1250 966946474 966946483
    0xa050f1305210901120c0e0d08120c07031701060c030e0f030a0605010513060f06051c0f2a0210020d0b03100606170705120c120f07030e0c0f040b03070509070e03 71
    0x144917020900d0800c0f940f16082c0c022080240b024021520602030a24501c3c2c482d0343c5024648500c10000702d21000c000700354030040010b00b9550300a850704aa00440d00c03254404c100001d0250f48005080459a080003038016510903a10080003400441c2052840d4082490010303061019107a035602e03840100103608207500010f0340c2c00b40391841844102c2c00e00102180c1032001d841120200080000c0c250300b014a018030300f03491903c80c1c4030b05008035154071101a01424240c0b1800d110080444800c0c0e1400404028280703900c1c48980141900d03201c07000b03500000790090000e0124064840500300c201d903070140861121880300050000741d5504044d00109020601d8808003002c44100003400001908102603d606c01500f04222941d5551404020800d0150f030310825a01e055800911030042050300c1c0d114402c191566080101d407540e600301c0381e660706203400301035000700112a031013003241019005505024806000c55180341d070344034003140c4510401c40b113000002d00042e0007100035203070034070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 966948974 1250 966947724 966947747
    0x601030e101505041119140403060501030204140421020f010e1c0c02010212031306060305010219030506010e0d0c030b1003061107081633050a050f1305210901 70
    0x21810410170724040340311400c5210b0210b2211002102155084c1041d01c00d286c414401c041d6080800d4646680c0d1400901404080c00124410b0303003006090882030000c81c40b0140300320341000401c00a0200c601e868a03054000706500400c41c043c00402042c3c204090091414400b007500042400d0700f080168010034010005842081081c03d54100300540c4e4002248074428207049007043e80e80e1107800c000900e41400d1407000b00303158104800003040c480194054079610fa01c1220491500038052021021694201c1c0c0b0140410400007850328241030140906004a1003030041724982a102d44540f050000d0440d4900405074400800340104003d0340140e00b00d10441e003050740e04150741ca42e251f00c0d0902803032541402054071310418500380304203640700581c2c0d1817a0f101c902c542d0201c40c9a4035211410480c041c80c0c1510b0909011070780d20403241c454603201710320724885e4540c2615500081c4408044003101920140302d110001006040741401d51142620803074035840d955500d120014002683d40d8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 966950224 1250 966948974 966948979
    0xa02032e140f061b0f07060905010338010e0306151512070c030507140d090b0304080405010809071d0103230607050f0f040b07140703050c090601030e101505 69
    0x41d100b0348280e03c0d82e0b400e50b40c0c20603202d00c0802c1000010180c00c0d203840b0f0741e0350b00c040c00383c41266800942d40d40c1110018080d20401c3e0f8090140d41044400c40340051118059404c941c040c2000b0003420700801e20303016005500503d0034609461162000078503094050703500c47d610010550a416140c0f030401c101c05211080003045074144610000d0402a110000b01540240881180d81c1d00415100e20219080942d004030301005002d41400304a640300e102203505800310321740d40008122100f404040e240314580c082c600c1854181003000454038403601801070785c110300c11208042050503880707110705864030341702c01581e0096155003002800c1003150002466011a204035041401c40c0102e5096841080c0e410140d5549030f4000341c0c9070503407191076a1400c0a14000c1004230358001e280300249840f0740200383c3e41d0000e003240d07a0300a8071400d1070701c07000700294040c080c00344040c145060f200c2c3d8844014103001415480804000f410001407190f6018000e98483c500c9481c180081901c03070203030a00b03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 966951474 1250 966950224 966950239
    0xc0a020d151d100b060705060411130e0319170a021c0b01020a0f1401020c0a0203070f0b0304030c0204060506030c0a08070905030304091d1903090812030a02032e14 72
    0x1919006034441c888903e0f9440754540700c003403c001d00d4070f4000031228810703070201c110741d00e501c0c107428a590b54200305841c243c844c00100141c800c0c00032050041001c1030710781c0c1c0042e5282074100c9800c401001d0010410206000381d000d0341801d05004140000c0c8107071040c0c4405070350350350404107500b0615000d200ca01c04031450895044140c2c2d03400620202c8450303001c020789038190300030300301408103520480c4008942e6000040030b42001201047e1041828400d504480f1304a881c0d00131201204141e000d619000304044c0001030210b4495450010380b28000f40c00019040e8450001c0784036544120f5070f070314510000161801910b940041a254403145514048440a0805c00000d8881c0324900c41d07681c8a540700c0e01504c0b43c034000003041049a06a26003120722101d60030609040c540f40b8003505a004c14000c03880020102c1c0b020442007007103c03c1c940c406245545e6102d03114000d40020780142c40c28020201034010700c0000304d01030a03012001c10701c4040703614502540303200b01a5040790f60501444d0b0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 966952724 1250 966951474 966951521
    0x30614010303140f3112030e030a030203091c080307080613060f060f11060f09061005092206050103081305010c02130207170d0c11060415020c0a020d15 67
    0x112103065032040795505407181000f11001714078034030846801001c0c120340c2884890000d01c500442c0d0300b1070309052180c0c035150407012a44e000c140e1510741c4074802401507042044409610b00c2c140c210b085204c850850303800d001480503105c8854a400803a0340038017050001c007d0181c0ad248c03075408880e00ea80c40c440b090054509200f8074001030000e1b0b00c1078000703103c81a240b0900050103101c00c090b5045100c0201c6015103420301c480e15080e4030541e1020524007882020031000c1c801c1d001d910302a120003609010751a260031503500c0c0110b86401c501e45660040e050710030002031003402020300a5006078100c0b911104507068a054004840e44a030b4140440ca10400300180c88002031446403904c04480183c840c00349040c08466484009410390000e6800541d0f4841400f403070b408141102003640c1c07040e841003501140300c0e540396019203001d040b03440e854806c41048039040d0002e000100d07171030082e188510003560115844c00840d52003226202e902c8540720b07662800e1441810b025401101045100c001e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 966953974 1250 966952724 966952747
    0xa080d060e0a090c14010c080d050a050f0115121b03090201020f0708070b0c0a0c0902210103080d050403030b220f05010f0e07091a0c120a091e03061401030314 70
    0x11440e22802428030220040500942e001f840031038035154000ea80319580710118000207000303100482c3c02e299004d103008049108858220100360603a038415458030036048880c503050350440900c00b9080c0d2296100c005410f100344800d0040020f600c2c0984010865050328400a802e05640c2017800140307520021041025038000116903007120103c0000e039517507040032407500d810240089006802180b84031000034a40075154010515008103449901d2032040440c02903018142c20300c00940380307943c14041c0249006ca19400701d90800e01c40c0c14001002c19a03940842c0100d60628042c04612025a6840c5642100d50081a080c0048898104000e60409219580002d894041d031603246900d00001003002d4040d01c007140c0036240540420302400392080e03090f05980d11140d410310041c0114199080e6000e0003400baa00d04803440e844104041d8180300440c0890b80580c403040074a1000e105000011540500c11000f030510b00c0c2840702129815401c000c0e0035400c0c900c0c84090701c61004c00401c40800f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 966955224 1250 966953974 966953993
    0xf04090501051005040c021e070509010305161a180112050c1b0303100618050316140a0e060415151106090a02100507021305010816050105030f0103030309050a080d060e0a09 76
    0x8460780e40d080c01e400040410042c42c9c255650001078004500200100500400280d8800e0f00141c42140d00c1817a52103410000115580044550140c40c1c103005000070302e240d80c120381d04800d00c10324090440c64442000e241c185c4000750707540b1820020000c6d0074140b0101001c80c800300c1500640096156080ca03001240c6401051701c208002c0001074211628026504140c40004040007411507844905103400307800c100c4d4452007401a00b1442d1010445c0509044001404641c541d000c400b503c0d680e030b1004c6c4006480904a902203000980c40017242c4017891880448181000d69a00a290700b030291800b0300e000c0c4060200f042a0b8040d56042c030040c1d80b2290504103443c0d541c500340c0d80b50080b91003c6920040c400e0680944282030100100b0240301c0040c1c42803859004000c00103c030380e41c5600540b507031310060301e002450b502140e0060001c64082d0304040c1401d440741d812184d5450007510303285401d801c001b02e130075a910384400301041074200c500d0005410500003c030800948074540e0710302ca0304 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 966956474 1250 966955224 966955243
    0x2301050904020a090204080c0f0f0f01050c1203040b0717090a24020304030c020a050103060b0d021b03070516061707120605040204060e03100522020f04090501051005040c02 76
    0x40c0e00342030001800c5440b900a143d00501c40784400b552180e40b94070310507440c0c402c85501381340106200d101840c4d1030b03c0c122203818865000a000c0c11008030340040115400d0b07110030036001c1140300701080d100784c0d605080010751069000d01c10382c00715030415403c01000989030181c01303044040c034070052260402012a0481c14264040d008802d80c540840c401081001d4450601c00920300c00f10410041c1608002100e145038400c43e0990801925000150101c8240780a07407082d07000280102032140704250300400d400d00e103081d41140780300c8040e0041813969101c004122041d802c812a0311403081c40603900c6201074035041c00d080c004007520201a55884000400712010041003881d003c8030801298014070240001410555845840baa0054059079001c81518040e109640083c504a45071784a4540103911742c52220fa0303018135041012040c00980072007640d2114508050001d00d40d46c5201e080415803003100049101d18104002d10100c2406900a6014906000f4a0441c599010801086 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 966957724 1250 966956474 966956479
    0x15110301060c051507080402030d051606150b0f07110a060507030c110907051b060717150a090902031011043c240c081813050a230105 59
    0x12054000d0503c2440c020004c0d8100480c04280810300900b20f03804001c6c5842280280c0440345070b00c80900c401c807018803d402d003013181c0c0602d0240d07441c002003941d00b0007007100305408250b00141c1c1d02c4038a8070016502010241070800340c005051030401c00048091a160f0f08100c03480c1803174034541140074200b4800e02c10024100b01705400503000700304060111009802d005401c906040c039107800044c207564000003100c580c1d40142e60f16441c50f020000b48407445005130b6912091041408007d008600502600303858408081490141103a200e42c02614000c140c1d414000c100d00a090060509040c65846141036042c20440c60404d03607407180f41100c089400c0c00c180b00049150381051130000825011030005001080c3c032076003915480000d5400c0035140c40c80300001d540123081240c0302c0c185806a00d0030011401080d003282c04100500c2c050489203108440840b80f0f10b82910004000c3c0c5c802140141607941e03580c003844110b100364451440f008040650000c442c0450708941040140140300300c03403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 966958974 1250 966957724 966957737
    0x30504020a03080f0712020102091207050307060305090708011a01030b040207030e091317030402010801120b0109020d0e0d390605180d0e0f01171b0c03070507031511030106 76
    0x1c8801c001080fa00d40d143c00c02c05146c1300c4c040b18000223000c3d60100096501c10200b00741103100340e0794045041070441d00010700511032180703000c0702070b00500b130b00400824442c041c408001500080a00400551320a40c0c10a43c0c0309580c9100090304a40b00010300602803403060160700b00094120201512220040b98222110f50312a00c00e10080c03280b40d1702c000d224030b0140b00418401c4070b0b50805540514402d884466141c1e8860038031880f8081c48035000781c407c0b5071a4004001d010705681c0208410358000401262800f40c40b483d491810143d000844000790b159440c01200c446140350042d03001c0e80d035034a40303110100340c000c04280036400c040c0050440c2d81d4910224170b040b9480c45420004c002180c060380d0018940391409020300444010103030040910b0604089190700c5441c00d40b10800f050300c80c205940d1500c1003440c080d1314440d0314151082d082000f1a074030440c010006031440e06d1041c0000c058550a40c9000c91100301550f0541809600780030035400307041c4c0400c06480c152240e074038028 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 966960224 1250 966958974 966958987
    0x313062a11030111030109051602030a0c062703080703110d0209030109170c0606030105220302160f0503011a090103031b0f030537121d1606030504020a0308 69
    0x40180e03041c4a2560340c198a40400b101c00c031008070b00a14100c0f04807003806c001d40e40e6004a00a11030f001c4807000c00c0103030010010801c0140c002c141e42d071007480c0034140c005010181c40755000903000500e0400f680008500c1e01c683c08040e0b102501d035074420a185403e010544101c08103450900403031112864190300407441c0205038409510100c0f9058000501044103020300b00324aa50307038020f1101c108103001c0c0400049a90030140106c9000300b01c0c45e040d0382c0a0300f100600000001c2c054600840450107451100c1300031400d81400321014028101c0c200b50080e1914040600316001ea086d8a0000314490145411940d2203076045c0741142e070917040c001204034010004123400c42e0a000010071003d86002d22005260780b000c050300e2540342107521a1943d081900f2078001c110502c040110100310201b80c00d0b2a0684142000c56100420710341c041180034050b00e203403181041c10100811543c0c0f01c0f01e5428426009514802d00031302c180d0030200003e08050300840c003950f4071400050214140052030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 966961474 1250 966960224 966960233
    0xa06030b060d0510060603090312060e34030515030a0803041103030d06120b0f060307061d040603120e0603010315020a0c0203030c0d03060506040e0f040c03050f0313062a 75
    0x401c0c4c40018010000c000c41c54541030050000c0c50702840682c00109c060314255180b440c648100c01c2900c201e80030a210941d148801c88201503614181c9200710030b005445042e9054400c060540c11150325100030030350389407002120200d100c296070814407d41c840087c100c0132445460032a5000368002c1000c08030f03c04a8000300f4a5446070312030561100345030910006011380f03609810711700301c0d204000010702501c1c0c120141c81100704c00d8412130b034180c204840c20032000d4015128403015010f103502c1040d04400c0900081c04644855005880304656903500c40152580301d203607840503090880d250f80c210350450303e43c250300c01f4038a11010011940001d070480c51601030868620055402800c40b40d03a00062910326482d086050400f40200341441340100706450b1070300075034094402c01d00c580400741d40d0391000344590722400303841580c0c003203880703607011000c14400c0c4280240460110011542c40c052040301e600025151f03402001000304809000103646034181c03040441200303503080c151503034989050 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 966962724 1250 966961474 966961483
    0x90c030c0e090603070512010f0c112e060803030a0e01021c2a0e030c011b031b08130e0a0b010c030f14041e05062a1c0c0203060a06030b060d05 63
    0x1c00c951141e00e21480001d001415003140c0f8000001270f0051040035249002650b20f0321104441d05134a0700320302d50412500380c0940c4130070406071041e21001c454080c1014024203d44290304170b14003640000040000c490490301429082d801030380000c502d059100c800380d040f22400c80c3e015014036501e82407500b0b9121801444954800d070f0b900c2042c40b075002c903c070010385169000050345003c4d0141c070302400210360040f00000c4500c000a000d0058441c1d440d03034101c1c1c42c40400e140540501d0280d8100c0c0d070100e4031030006048200c442140030040d02d0705000d00310004040040034818014205550810166407080d00c80c05110f501d82032402e0b03400c000d41c8046c2d8411603206070480e05450041070020f103030301c420105610596881c071848181241c69a0601c03405200d94082551444226200711181060403440728400c400400c0a480410540f0484045141c840c041c0c002c00041003080040194901408801e0b00418401e00c200b0042d031460f65001500728000b0515031054515550010902c80c0910 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 966963974 1250 966962724 966962729
    0x16030903051603061503210504090c031e06030c030609021c0c14010216060e0607050f0601030317090a080a02010b0904050a121706040f020702060a09090c030c0e09060307 75
    0x1015940305540001d034040d000c40803440f003550312038100301c01009410007400c003440503640c0203e42143d1b420b541d114629207058690110008104041100180b800c10398840c503004540c940c3d030080750001c00c08000d4103052006420002e0010700d411070400c00103801c0950710040701e60020340811680c8041c00011034002c00d10050f403401140180d41c030002c000324001c43d441a944c0e0002d2a518070b0038458012a5100310744103145c2c02c2d5404207141400150700906a035500000b0041820340342812596807142880005c1840c02c0c40f80d440740b401802016000002402c480703400c038015040c076150095041d981c485080f103020b041c0500004080405510030340018501d901c01910706003442c00c09240842c0d0354410400d0944000580045104007d48240440c4101040048001c002c42c0c84034805c01c80140401d444001e8105c1c2c0c00c006010068840750090240c0510b2034480180c030a1801d105a000d4408151890040500d40344040140b250409111525904166a074440326550540443c1c5003242d0b54 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 966965224 1250 966963974 966963983
    0x90a030c06061d0601110316200d03030209030706030b0d1b270b0306310605180d080c07060905010b120307030215060906010804030e040f020a08010b040302010516030903 75
    0x10b140f50f1038250080d001c00d001d0070302030342c44104c83c0e4207096015447e401500d00c0740c40c06001c411008404501440b1070000507281da20f00c420b444943c10000101a0b040075001100442d40100d6460a58901030040c0002800c4508040c090031410000081d51402c5410008001551803901c05030b11004a50000000c0c00351304a481a000c0c003051840300411102da050381900b03e0a014504000c2d007400300c1c20344d00030341602d401c000711035072002c40b81ea0410605141076906030308181e00420129909000d41303070080c6000c1913804000786201030001c0c2440008942001400510014041011031110845d003140e500000002040011485c2050140c038a48880540c8000034407003190041c0c10100c01443d4540c400d808440610100702c1c00e140030400308071032441d80200d070200000c0255000d40c080301e9209109290a4501c02042c100003400c4440001c0300c0030000354042511606503800400040c0940f100030a11800d052455000800610618400d400d030841001404420103000e9051030001d503610 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 966966474 1250 966965224 966965249
    0xc02100606020102090301050123060304050a02030d0c15060b16080f0307180e0907050d080c0106062705090402060c2a0a0501030e0a06022a0a050c09090a030c0606 72
    0x741c11009010b900200c4200b17120b035207050300015594000c0031440d81e852185046180342c100c83c05080102d250401030040c1c0381c60143c051280b0060350140220640c103070442d00c8110020a050424640c001c0140c8100030038613180c030000f80304e1011484140d40c01c2428a058039441d96001e03107030211071030040740d40750b0f50b000002000b0322000c00c2c1c21120380c06148040040803548180d84900c1140f8200c410360305d060443d088003c003844a0304040544a40380340c007803064186000f160070308c40783c211242940b00710000360540341240f03a408050510312040c80c0080200a821034105400030715000300282c8002d114910004921078041c80c207106106000c414041c0c42400030300084101142c10086c00b01c9240b10b484015000b0a40d90b000344118586200c0d0b40006110341402680d40500075401038000001c80c0503241d07071054000c22072240c408a60701500000d0070004c3c0d01890b225181041158019108100000403c00710000000301c074008503405190100c0c13103010600308840100510f4201c69004081c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 966967724 1250 966966474 966966479
    0x20f1c020409060b03190b0a020d06180501090f0204060915090806010e06011e1b0510020c030c06161421071116050a0e06060904140103050c06040501120c021006 71
    0x4950018201316425400e4401c1035058841d80031006100240040c1000112000310f03040003929806041200c2c0c00a10006025840b140d01c000c82100c44d00c0643c6d1419168030050060b5180390088103050740b0000130550406003407c2002d032428145006003501c0f01007080403064640d1080703402c1c41c001c10000e410b90706656101e1640300200b5070103c801c02c0c0842c885024000c260900b480701c0300c1d107400c10360b682c072641d4074141450034803a4409900180d8003131091944040007000395200030000c502d40c0d01f00540d034481041e070780a03040c148002c15019800301c020324006c49090b04a0038052501513054116070b500c0d151882c2201e1004606a5211003511204003040031503a04103910060062800c402c480301e80000c82c00000810340180125034000501c08010060382c1d41205c00903400c80c01c01404942003411030070200f0111694898920501d003401d40040090120611102c9252141500e200f0320305410140080d01070260318030b4418816a6626400507800e00c2800b40401c50841c083d400e00c4003d6 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 966968974 1250 966967724 966967733
    0x90612071812030e011206030506130201120209090105131401030f0605091f0218130519051612090506190f090c0314150f0708090604020f1c020409 65
    0x1a225040c4140001c001d0740454038445103401c000555a260340c40407443e1000100460340a45d1152000402548034440403000030710601c0041c0c440c40b882d00c54084104501e000041c00380c1c0f00a15110b1010b44100900111611405155819a03c05981c001c03a502c20b003181405c0285a46484540d4026a900c008010449183c0041d42110300030b22042c49980c03070301c41a958071482e11503141428001d100c051504148e5058002e84031035282e4484c40c5072010340306030108050410300d1410a486036074810401074807841400d400131600502280130011464403403c40000700444085d2141404021481c1d6220405141c10080d0310561203001c3d41c1c49030030704054007682c0c1001c03000c62041c03c900f4940b8148981ea01845590222504104540f454034596225805d4428606005a0480c0514000d000b080001c500d6940d001c2c03940281600510318010200034455040074042050507040f06080c000984c7d070318030a035280c1800c1240c4e01d8500c1c604100030300461486c0088002e4115050100d84070a00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 966970224 1250 966968974 966968987
    0x206040e0901090b1f050112060e0a0605010908030309060708060d061a01030b04180b0c040b0307090f0f0e34110d02060601020a0318050409061509050907030809061207 74
    0x144a0016030304c43d512100b04e10510700e00c45076100030341244001c0080205610503900d03041c41410610000420ba03031100d00d00441c0c1d000c00c070703250703d40c0507200c8204000715640902d0540040808402640c04c43c2403c060103515130030003601d200104480c50000c1410350342d03001d41100000c0c0e406981004038035840068840744240071074807a40481d1074030324840100e081500640c3d4848001000548680c0d40b255120003151a0141107900080010700011940460000c000c0d402004680c80d00d182030303480c201c601075466840d504518511a402c1c4c204000c10f0740020307622a004041801c0384003a54a020b000d604d1114452100c0200a1183c2040302400d550040c41492400d02041c0c00c0d10300d9801049801c1e0307600c990541c0c4650040e8882e400c0701000c24840ea002c100c0800040100464103540d0300001425543c5884064804940e6001d240010030300c8140600000c00c036009050104e4070381008840d84031a210300c00035010000005000b003d55880c0000c803000400b4602000100b81070188000b001c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 966971474 1250 966970224 966970241
    0x91404060501050f0102070303030203092d010f0204150e01110d090314013305090f01060210090203070b0915030a020421020303191707021609270206040e0901 70
    0x50300e40070011a2a0810340c9429900c4503040c0c00130700c4035030310b1540d04400a60000740344100c14040e001c504a4111403042920242407900d04004030059a46140e403801c43d03003d271070307400b1450741b041104103e11450054a0088440d80c0d00300000c002c520080140d401e00309012120280e402a4225891000d820105203020369014154201c601c04150300f071103080380c101292070901010b0315407640c81c0c489024541c4a41c2c102c02a0100417485a8547c045600541d05441e0359500c0161803005204030760741007107001c510041104040c059041d16030086034541c802c0303005902e8554400210483c550701c8020341d07001e2151803003c1043c1e0347e03d054041d0344000d40090242c1140280b06408190003824140e41100c20280c0081c0a14038000030407108041e04a205031001040c400e005195808900180c00814442c82c0c040d00605101a0240488584c0104c00d4001d000414540314008400503164491342070760f010407185034501090103000141d0705010710340c045c801420040041001d52001901700c0400e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 966972724 1250 966971474 966971483
    0x6060e060708090d020a0e0a0f1a0a0303030f060e13062004090902010e0603090109020f011809020306060c0d020a06142a0d09030801081203010303090e060a091404 72
    0x800190000c0002510032000d000e06100c0d01400003a140746070088003020841d200600740301c2c24035560034050b821a0700c111151864540e40320301501c1c2800044c050701c802e16285106500b103d000560000780c1e070000b140005401c0581c0c1340c2000321000c03c141d018a01904006421250b10b282a00c2d40440c1194040e80c100d9800341858252060115404204502c00000c080001e05082c00c290400e0010f008a44003641040b5002065641d5a1030300b500440c0181d800000200740544070340140035810f0f08860740d8604005c5810501c139214a050200394069464454025030f83e61650740006100e409440300c00c1d071080c0991580e050545800080544034076104040900465010b480380c3e05816000301c0c0c48030115200c280caa10528241113140b0781010030107000391400c0000010b20710f4201c0d000d440007200800c0c1204018001e40d5030805c0606026241e0764a400c0ca1581942d4005040807900d00c9401410344500c0f0208286607201520280070b4501e0a0f400c11507945158940c0b10b034280103503000e84 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 966973974 1250 966972724 966972737
    0x41d030c100c0c060b041401140f0105030705070f05160e010f0e0c1606110f090a1523041d160f0503010b18030a0302031b0a052e0f0606 60
    0x300325161405514180b0809855640d4008800c0d120040545041d200e00740e409030740c0340140c083c040c04000440340600036144e8800d44035400c403400c0c030091101c4510305a0500009004000d54030b40e020f02183c4441e64060107040481250b0303e809031400c0307006451040d07009010600801d40c0400104007a049402c41c9605900e250b44d101d9101407000c005a0360b0084c260b07020401c200c4e128400403030203101c183c41968005031052000b9580d198a400c080340030040c01c100012f4000507880c140d001350002c0e05032403100961524007ca40135240108a0222900e1024446a0b100601089805480c0280342c2600320266118410310004000201202e007529008119010464513501c42d03101d8820200641d220b0914603420000340818030f8110303042d0b40d40e02070f0105c03203150310b1900c050040e400070a1280c2c0040d030b2505408107080c3c1c0203101e000801280c6034402c002c8440400c9000500001030851022070304d000555200000c43e41c00d82401e07400100c5401e20341c2c1084200c29503404101150020f50300e46 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 966975224 1250 966973974 966973993
    0x40b1e130903051c0606020703060c0e1f03270204050414011e05090c0a06030b04090203011a092a0702010c060c0e150a0e04051e010e061504050618041d030c 69
    0xc0c805c03500d26001c0d01005070300150b41880052400d5000c03202100d618203115503690880800071b140100e40ca21141000300d40c103420307030000c140c0500400e12039164034420500142030412131203103030700010f00010b823185031071704007080902484001008081b08408001c2c4041040581c00340a034400c0b469050002c035203030000040041d240071511441c48c0400906a01034503141c028110088c041e40c000300e581c442e039500d45d440010b950903c60000034181e04140041810f0254080200c0080024140b0041100440c01114002000c001d035002e4484a180540c2e00c81b501e50004a072100b00c141001045d031490300c00b00c0301c0156000300f0321709000d01007101c22482c04a004212030189008107a800e40204181844042d65894207401069001c1060406c0e6840d40c10011000a0004000e922094555040e0300500c40c803420026201840005d880201901d020b24000105040c0e109440c5808900ca884c41d1000485996a800102e0300230705080c030344035441e144040440e45951001401c0007440c0f080b1804e1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 966976474 1250 966975224 966975277
    0x10e0105010813030e0a08150a1a01021f0f2a050906090904050a050109081b16180f020406090e0a0c022107080d09050c040b1e13090305 60
    0x903d00c200c00300c80d0600e0520303095584c1030350244c2c0d01c425160f6006c1c950110102e04035408214000c09000c840082c5411410312820030401ca80d0084001201080407007462181c590f000034500c3e8035400440410301d140baa088907030200030219507880c00e5550382084440741d0050342400e101494402d0380200705030001313080e00381611140308040e40c154111a040c03201c8410751801101d0194090f0003102070715041c1c6078036030f682c508503504203404981070340d030204036280d10032401c0742000484d03034040d40204500c084c40c003204585c0190621440d91007210009103c0d8403034849400404c6007202c4807805544a94075a200900b1581681c00f40d142c1d01840c01d00000c1c01024a400ba142d41002c280d000341500c0015071104120380e14030700c0d030100082003007000420009810080105020000c0143c0000c2030541c52902c14100000445086e20584c102a1501d41545c0c8559030440c226030b0580000c20b00319030f0040428450384800c50700c00ca0081c03400c00c4840525800c80000d18184001000e20252000350070340 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 966977724 1250 966976474 966976487
    0x114070914011d060a1b1b08071a0a020307062d06031e02010203160605222121050a0b100c021c02041518020c03033c010e010501 57
    0x410007001041016003c040c0c1042e500500c001940c51030030400c1c0c50b003c590210b0b5400301e9042c1c00c0b24100100b807030011590902c1850300c0040c0285002401c4240d150441d102c000c1c296114040d0844180003d981c41c1d074900800840c1c920301d510075428040c22218403034046800010170912961400c1503105d0940e501918410710040d01d41c0400840500190148845020240c40c0ca00b00d0541c80200481e0940c500e544040705025449000301151038500851f903044c00314030241407260000d07894448203000404504919100c3c0070703107411500c0c40316200501200e00300c024001c0400e40f0003400d40c003ca00b010003901710710b128070035041040c04812100e201b0b110224150541d0311000841903d068801450040300000000401440e00042e10340a900060100c61a2200d840381e00300c124541048131340c4411106403521101d0702c5c01142400c030301d9195603440303100082c00005203c1894200d0114285406040c0740311403042040144d80e50710502c035004809502380201140c201e130034030001600750b11030701 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 966978974 1250 966977724 966977747
    0xb1801240c1221060305011407020c10020c0d05010b0a050303040e0a0c050714010203040605092406060f0c0d14070c030305092202280804020909011407091401 70
    0x50300d2245099080e211829903a425101c204100b0100c02450312903180c3ca0216201ca1840c88000000c41030b203075150541c02c60310016400440c1100d501d040140260700413443c040140d500b514101c8444424100c201e0070100c001c82c031580d20100c1413000e0410700005600084070480c05039840300c0e010762a030042558a01903417050b0020505540c00081c13180c6500d411208883e449414407a00b0300d030b5690740341c01e040302c0521710a481c1e0340c0d40481040203201c038501400b6000503d94016081850503495007900c003019035084034802000072008602c1a4aa0b08207c80e00c0d512004059516042d07000d40c80303502d078030040b11900002401000c0248036010f400d030444121650004420403858a1903900303036916002200c02035030090503030001030350b0f03404190a421052078804c0340069071203040a004001da41042c104070480010100c103a040803a03000700226410540480d030091890f500c6c0c1c11710b5400b400c1d040408030308004869092041c59034020b020ba0060742c100421041e410345a02700111995180709 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 966980224 1250 966978974 966978977
    0x90c0a090e161d030a080c19051c17040f030807020102030f0a091b0f091109030a0b090a1208010e28021e040b0d050108030f07080d0b180124 62
    0x10b20074201d0080c040c0c00b05940c40302c038002c220f500d80c0d031201000a0412015000941c0e0100c000201d1080d800014800c5044407502c606403901c00008a854190303a500003105d04000c00300520241d1500d46004610300c001c05102140001d8042c43d09150045522242079011404262a00041840700c0d0040c02034034401e003200c00301c3c00526503516103901c1c09091840000e4800300f141c00003880c104103022942c10050091006036140040c9007403403000844d035000c0f017000d403030510503c0000e090b40d80c04038032503201c65003040c0e606000d034607240481c42c2007078101080203086a0642034020042d50300003004504031000c000080080d940c0b40d0341c5250b1580842821800a4071817052600d5100d001680035141c01c805041250b0348107001c0201043c225032140c0c0000300780312808a0001c2c0c0580f041e0182c40d025002c3c0101840c10800744108135082e600a01b4030080c6055000300d0130700c20038100c40d80001081880141051003035650000380d080d00c10400c0c003030000100c02e0110581014140c1900d02d0000052070b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 966981474 1250 966980224 966980251
    0xe0114130204050408071a100801060506091314070c2d0212100e1b0d12142a060906070c0206180a030359090c0a090e 52
    0x207542084002e0200130720451709580e05111000224240c1a9240340003407076940c010390542403d0782110780c9940750b07500000742c60781458170501c05a00ca00003a180214030950f20180100e00d4400800d002c0c040c0c1d120441c041d655520100092254401d01108050303010b085811040d503840032000d04030040012604940d0310784030141100604000050403200e0100b081910742c0341400c00b1a0906840308501090819401100f41c0d900c080e20f241320034031483c4011160003559085513569003038881e44014010007030042c1c00401b41c00428248088482c0340125003940c2c41c0c9680c0069418480003001241101148142c400090040c0d00000344640280c00381d032241c158024542d402c100260b4420f095450103c0403000e00d2202584907400030b107002c0e40c07003500c1d20189122400b25404440302c144401345003140c0c1c101380c1c10364460744502a4030a041940e034040400308203080003c01c46091000303804e0703401008160410800005680103095880e00c6035503942e80e13003a40e41c41545001d07801621003200745000e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 966982724 1250 966981474 966981511
    0x2040e01060804050c0901120201020f030a020705090403020102040906270c1d0a1505031e01050108010302010c0212101a0409021c1407060c0b0c4003060e0114 70
    0x4440c2980d100c3d20880448240700b2a210210303500740401c1c1d001e01c0860048c0c6d03c00c64115030301441030349000110b0800440c14440040c0c4002e65070720407403240302d028850726004501414401c5d011180038089003a024007485980310f04c41007940d80029000300d4980c0c604800740410003400d00034220743c082d940e40c906d05080c14143c21b03400d0800400c008607500034013014001a8101d04d84040725000d80d42a100e00740c03246002c54071490300c02c110b494008075800c0300703200510031a0f03081000581980d40a1070104203154252010a120b1020213992071024403030306000400c8194903400c0340d0722211001501100c2405040103010964019903c000e501400015218a0407034400440c51501802103040800c010302074140b540c2000700f26048503000440c038080400c2400a41029150400040c4031114075002c908581c03140c0c0b00150384c403848072030a0701040d100f0640180140a5001000e440c40c07624100da60303450840700401104030111515401e2000c100c0d6851413442c1d036244688001d1000040810 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 966983974 1250 966982724 966982727
    0xe010905040e061909051b010e10021203043207050604031e0f08041d01060905061611060a050c0709060b03041103010626011d07061d10120f02040e0106 67
    0x408101008800aa91700c1001012900421910325041481080d081c031728007132603000500140300c00801c03a00400c1081400f440050740010480b046030200260b0303540700d0b121031420418040b0300c442562180001c040001c1a0411444942000b548030102240e00f469036034828410350b4002c6200180480c0380101e40c0c00d0740801482030070b120851150102d103c050001e0b94880700c85030004d070480000286801451162125540400c3e80500601c1c208017003110700d07000014000b44207082c441c1d8440740400040008104104001e402d01c894003d01080c0c83d6607640c0001030460308001100101440340c0100050f8103034051062105031a483c0440b1451030360b80341c54108640c16a40c0d4466059942d4540003d800000b44510000011410070003881d49110192014296200c410f020500c04448450342c4414160005404003218164180b4446025061484030b03908000b210125401200652302002c02035070044035820140700d07045082000d00044000c01040303014600400d500c4014820041c030205 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 966985224 1250 966983974 966984001
    0x501140f03070e0f0708060301050f010506070f061a24040303110f030a171005011b0201021c0809060f010b09011110061403010c0512040308071205070e010905040e06 73
    0xc85014048455507a60340c030301d403038210303404032120550300b8040e030203010025901803589600070400300c0003403102d428088800d11a002040c030030769200310780002d82030041043d50074a00210311f80140c01001740c03501a900c0705115020f0b03081a0b500c074608840c036100203006079400302c89858680510041c1800e06545d0165003481e0440b010031614480e055000e1f80000c4104018000301d06560707505034411101103078224000d00050300696406d00148001d00259a018103c0424036842c04984401d80c011400142c0c2802c4440e04407001005201450907807240d00300134076074040c0b00c403402103030282d55802228000e81c0c8000c1c059031081031010010901d6640c03140034200c59000e88142074505460000c031443c2c7c01c60748a94045046490011102c1c1001e207000c1c030911103254020b003803861a020b2100702c807504000d001000242406020004603450b41d1250843c0414102d00a504009a050991026240c40800101203001481d11100800c01c0e00b0240135480c07036056403800924042d1900740020060 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 966986474 1250 966985224 966985249
    0x80d020f120f310b09090703020d090213140718091109030a0f0c0602010b010e120c0d0b160908060f070315140a0506040509010b07060b181801050114 66
    0x40840c14030801c68003210034540d00601643c403d000008145840c050a0403004031680000c640c21014024070303001d6210043c3d00395200f03803103240050303a51203a042800f008100c0140080d400551098a20b24501025031149031407240203c071016241d0382e0702e141200c1c0203036004800648258018810424050503800c00712002c801c031081a0f041450382d078013003440c043e0101d10a680744040100f10905204041c0c86090140200e4402480000300c04400030f81080e041e074900900940d19078800c46c407250800e104929814078004c160b800c821506080c001c400d000305407141d0b21003a211080201c000d40c01101440c003107034112006030006a881840500030741000921030414036445501f40440041110443c50150980d110141c0300b45d0f131800e05000ca4860a500054060700c0104414089580e416001e541104c0c01e50080daa0b444105140c00000380a207020580e41142e107a18041c2c0c0c50948a0701c280d44071b07440a040d1003031070300701a413001c03404d0f2542032180c0441d000d031604501c4250304240030400c40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 966987724 1250 966986474 966986497
    0x70c12030605120d03050a1a1e03030f040914010501081303020f0d021f0e03070f2f040507020c0112110403140f06070201020705060a1802030610080d020f12 69
    0x810954400116202143c801c98910b0260041d0b1420000e0301d4061240d181c020740107120070411500c1c0700640c01209207182108510031926010007040740c83c01a550343c07444010180c256500c945242e070f09481d140e04140a000111814903001c20360050b00041c41604899050b964200076454540c46602000701481080c1c04500600b05600c82e84102003002410105440d40201550304105e502519000d03840075000d654907003002d807080304150b170003c1994400340c2c00c00b480e10071000c001d1400a1129142117804041180424455603c008182104000d603180544052040d60f45000040b600d070140001701c00d001c5800b41000c0180ea84840d4400a40740505d100031616040c0c0f40e03154009420001400c90125600c800702c2c4180340c8000b0f01c10140c002d8032500096050514590b161030303e4010041454402941c1c0f001980c850f088800c1e0281810741d0081d00342e43e81c0d810103070b03d00e040c48021809100c129200f404070101d0f5951002915001410b40c43c0c0280c00780b01c40d184c070402c040e80e0117026a040d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 966988974 1250 966987724 966987731
    0x103080306060d090516080f03190210050106090303031b08010b160f06020c0705100210050601090b0a09140f03030904201803060106210c1404180f05070c1203 70
    0x3c00902c0c480c4194100540a04010541251081d44806441d09142c202e1001a001007200d116010b41c000141d42860881803020706035104410001c901d86a46068002c0c0c4003804c01d000040e803250081e1001c000d50740241d07030078010203800d2340c10300909650004031080011080401000348000c090050074400007202c01401c550b462a484981484105240990300b159001a40c07480341c801c202700120007854161000c0c17484000114000c0e454440c40c3c1c1034000a95262400902d050380b10344000b1020b440142c050503201c01c0540c01c000e00c0013506000d80031100c045403420342d48500d801c50680c003032140c0042c000c602d07180c1040244005400c0c2c8030a81d13503029828000070060041e182e0058801c00c42c0b12880108008240c20030180b800c1c1c2c0603405403081c071041c9129496004907a2107120f0703a08104400102d41c032103021400300c07400f030b5044080d03401003800801c0114200790008840149184007280038001500b4001c61030003103c00645082000c0f40b05103030051f002032041c038413400d0181c10508000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 966990224 1250 966988974 966988987
    0x3011214190c050906040603080d0504111c0c060302040503100f090b130611070f0605181f0e0304080c090c090301050f04021903030e06071b0608010807080a0308010308030606 77
    0x844001c90705103000c07144422000001d02c00781c2081070016a0080003180c0501041c0d145858072056407003020184048252108000307801d0182c10f0b41d000c100c40320090910580e0780083d2035134002040b58030f0700450b00d00d01c0380000017502520134000e40e030030350320010b02a001e18110095040c00500b401800d030184c00d5111940c0d4008100111091407254103440f441000c0040300c1e00d041822100e02501110310041c0902808010680c1d0714446088560702140004803600d807414030000602e0b42c6850300c2c00900c40c1102030303211a400c00e1a50820000815414461109a40c00c11380e143d014038050420070742d112104009031803402200072a0413001d10320729140382c00f144401007401e550701146c140c41d050035584144011400c00b001c4904940a2034030303401581c1400c55a00034000d01c4640711076445440003280480601141880c0c3c00002d15102c4068081107543d0117001e030000200744a41e04060048420015008101003042240d0740d40c56581c2100d280e08568401c2a81d4101034100740e0090b00902c01d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 966991474 1250 966990224 966990253
    0x10806060a020f030d0c1107030804030b041109090d090803070206071209080312150d0b07120b1906020d11060a0504080d0f1410060806100c021c03090b03011214 71
    0x421000717003035410100d070074501503c019100c40d00c1c40b581450f25901544c8200042a500019281501d0740700c140c0d80c0d000d460310b090040700041c5000450381e000841030240300f1010030002d417240d40210b80d5201d503d4519a03850446450380200e810194001d8010080040020580340903001100220706143c582540c440d14082c3c13542d001400f542401940d20310511800e42c0a42c00e21f00d55010049921406000d101c0d0b80c5d426507201c002d810a8140805005135940070070380c940060350781d40c1c8080c0c000c040b5603024000e9811000254800d9101501070745004030080c61098211400c00c2401c107004081c1600c5801e220402420010001d8a54407001d10140ea1281182d02036a0303121201d076035000c204a0004074403589029000b8080488280600c00b0401810781c00850042c1d03c5001102c0c5d11a004003481c0c1c03340c0d07000100c140000d40c0440102c0b0840c0400a01a460b0042a40a030b521011015203030045c5e020303a48403c0c09608402a1311034195000125000351080c0e58a50307440994840c01f003151103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 966992724 1250 966991474 966991477
    0x1b13090b040f0308060f0d0b0405250e060d030503012310050c0f1903121103070f0e010504060804020907090905240904020d02090901110a0302190e010806060a020f03 73
    0x102110036081d0010900280350348100d04c44d400600c1140c511400290400019441807000b01005000d8440390000406000f001d07c41d421101f85c0b00347c81c0d148120003100710380c0328081046c058a104100441c02190103030500c0004101d41c00d0b07040c2c03038680c0b03140d0030301994441911076280d0484078400703a2450001c007901c82890002004c045515515111080c3c0e401150a1020508950b0520703480402040e022001543d50101e01c540c02d41401220088004c01140191103010749808582500100b44000f4076400b101c084102c120362360350712a00e800711000449441c4146d100c0c03240003902c0c2e2000714000d49440c052071604100707035040070300c820359440c10144d0a403001110188402c0c7d003030048180c1c030003225404c0c9101010341102c0c100780500d003d900242840e010154060700074030b0204c0000e05048400d5020396609001c0004082d00c4d060b00b0348008010b980000d40301c1458054821030307005c0240c01001d091a0a92058507070840940e202003c0c400203800c40e9044000310f1080c07100c0c56106840c00d00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 966993974 1250 966992724 966992731
    0x1050d050a1205040303081620030d02161a01080a021002010207050a12020c090c1603050408070801060f0905070f03050a06050d0803011e1406090414100f05031b13090b 74
    0x11920f54440c0d146090141c4440c03802030450800013013182419090961101500503100c2c84000640c81e94100501400c1c610300800c42c2c42c400443c4001003ea26802111081000e01489001da40304110703006041e0341d00c1801c00f84204030319980039851100061030030015075828200c1a200043c28810651115031814541110076920100c03c3c00040800c80c0c0e050041c110080d6080e10710018600749503d0010f410311501b10a1559029036130103610425101d4011503008145c0d40e0201e502440d16554694001d080354840d10507100c07a03802c8009850781d514011148160016114184114010b04003a8041c0170700800031002c1540e105d6010603140d50f28a0f4480c10700e07000d915801d8481d17040003900207444008a002c0b0813403440c41102040103c0010107032945d5802d0503562961541c0c1c1640c0820040c100030510000c0301d549001c1008422140083c82c6421196400d4803014002c0e514024591079460a240000d02c102041070821824284003e40c40102501c03480c000070141101d440e0050780207804d5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 966995224 1250 966993974 966993977
    0x51806090d0c030507050d03020618032205130902062b060308030f0a090f0f020613080c10030c0912050c0423093c010f090b010803040e01050d050a12 66
    0x55200f442030207000c0101e04082e20301940c3e43c08800c0c0300e0340c401a40d1064018029072240c40b480c00d1032500d0301400d0003510140303142180c03030980302c080c2c02d5a490001e4007240034041c007490304500081030a078200d004080301d641d00039000901d44442489800c0c001c2c0d4040c61040c5192403011107100d0201e2a910030321000350700030710110703441e42040040d8000300c50014100c0c1082900b0202e002e40440c85000310000000da01141c43c0c54018840d02c0440e0b2640944945492250f41c80b8000064140010aa2960750340049451500310441c400e4141d0031151101c0b201c500150b5101414800341c1211003148040c03c0c060070456003248400310004058503009403207030500d90f04441e4281110217080d00004c2e0422540b07409041409643d1000c1d42d8207581e00c4c0329100c92845902c0100140000d00401e61440ca54280001e002d4a10b0640c0c10b80017a06d0364943c2110084060b000000e42000040161010303980c1e5000e401000e64a400d040000340800c1004c29202c0340280103640300001c0e9090b6110b141d85059 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 966996474 1250 966995224 966995243
    0xa08010603030215040230010213030212210c01291c030c0b04021201050108030c120f030c070c0b2101050102031602130e03070f21051806090d 63
    0x7140381c0242049a41a02d950214008406100040c0c0c0d504a00c0f19610807241c2e41020311840c02c0003a441c802280701d0b4058510f5200054840d118101100c1c01d4050742e00031b0710f01c903060001740b00020355917003400d04d90140781c89103410500000d01c0e2004010303c2d06842c0301c07001144514040d00395404401c030b0060704503541c882e9403108400300d0034030214000303e00c1001803000c0c4210b400d0b61070160088107030680c002c1c0f9042a803000030702150388401144607060450b0008200d03a6842e03403404d607541e510040161450f071103266080c00201242c94215600c0f848148d40f4141951200d03880c1d194143c101e000100d90f04440610007148604803080906190385420b50240412141c698100707083c1e00301a00810304540040105840041c498a800048103605841540c03c905025010b030b4010294010b0a800b00c1c0000554242401604490072140034051030100903210120851280381840b0801c84001144c8180302e081d40102c510700885550000c080e00603031030003031140001004040c81c841c044902549 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 966997724 1250 966996474 966996479
    0x50105010b030f13210c140607030509010e1903200303010302100309020603060118050a06020a0501230f101502100b030c0a050616060203070c1403070f030305150a080106 75
    0x40c0300200d030401c0c1800c2e03502a04c00c0c0c45403078a0800c0905507440c030700c40010300030203200001d208039001268680c03c01d60b904103400f1030065081d04c4ea1000d50382400001c0c1080c005c900307408018880c0c4075034025014014000340c3d04501d03044118509050080c1c0c244001607010f40104c59a046090040e03000c00c0d005540c3d41e60440c07042003844d20550380c3e1901050304c1c1c03003c1c0800686a403002c6030b81003c42424000d9002e1150310030807610031010380040307412500020000944c1c98002032036502c0144210024401c003405060704500c10360042903070001050903140883c1c022407460342095044402480030159142e01d40071020f50045c0840b0011005910003003c0140301e810303d200c1c482d02d060080300a401280340c8480011700d05507050103004d12441001800c1d898600501c10303190121540520150349918280c0400707003941901890540b100e003103078120065010804000c03030b17102a80c4000f4205030180706460880017050300405400c1501d051303a001c006a0b540321900000200800303000441c0590 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 966998974 1250 966997724 966997741
    0x130e100f0f0509061e042409020a091401290f1204080306010f09081e0a0c06081e0106051222141203061305040f06020f1b030a1e0507050105010b03 65
    0x2e0000358841500038400d000c00200c04251a80e804030710382c403c42d4200100c04047c5001484008402507001c1c0104800040c070358400d40002039980780e40c4610450907a83c40318002d0740e4a0200c2200c00002c2c014000c00220340c50a40064031400e6407410840d4140408043c1c88051550280c0341511304400c040204425580e00441c500e40e090740700d10309031204d03a180142c11551003c400585800d29800d80c1c0c40d4401035a000c100f4840341c81d0300301c1d0b0080f400c16074400b4003070450b004c203559510b0040540c990030040000070302e080504031006903440600e0580303a00d070342d50300407035002e00b406481004c44103480036220301c56004484d041d070060844007002c04104203118038042c92083e288445c0e50051080021076a90100c03600003518640b4000f01d16699941b03400315088a404038009c014601c04600005c015695401034406241c3d949100c9a22985000000345d1300d000c0c0301c0e400f000081c0700201c40c10011480100141c0c0e03881c0c140c18007508101c21076a0790f5007500c000360404107c0e91804001c00c01d405 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 967000224 1250 966998974 966999001
    0xd090302150a09030b090f010f0509010b01081b09130c0f0216050d06050a0605130c0201060608040b062b06021809010608040b0907050607060b130e100f0f050906 71
    0x189414441c0d41c0c074101d48660042c000d4840e6200160541e211600050301d0003100303200b49040f030280c00000300003640c11600c10b8002000f055031a41015880e2a03024100707540a40c400500405412030340201ea00740002c044440e83d0b00001c200d81e003020300c07442420b10ba0055400f0b060001030440e00d071448001443d0030002d01d8440c000210880300103103040c0400c40c54442c1c1d01d00d860340540150011a007690740d000c041020703086039072055030040780d6000003114a65095100340d00507403660b402031000540d150b80c00c4821030002d880c081c010010b01d0b00070403101d1400c2070007811402c1036100304070345031412070030944010044407809517029500010b80c0310480c2324044900e00e00e0501200c40b1319035941000300041428800400c014040e02c2424081503541204000c20401400000e0110b50707117032178600d003140107041c00d101c01c0b40c000c1000c260024041843d5010700240a10004000e0602080c20004800603049040c46010180d0307582000c4000c11269004161060341c4100060045092882040904 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 967001474 1250 967000224 967000249
    0xe1203030118090f0515040b0108060c250206040b0403170723010b031e06060d11130b121e15011202030c0d0506150136080d090302 58
    0x681041005000c6109500c030701c0c00c4100c26204000038403450501c2d01d1200007418450242c0544030702c0080000c01100341d4480c610580c0308500b0102c03140d82e69011a542c403501a40c0c0380c1207101082c0052483c000c821a507104140b00070004204442d49a5004541d465029801ca1340d00c0340c100103420b0041c0031206203c0c0300d0305800496400d00d002440d0315500210407210345007c424141c100300088070310b60709410070320104000030103440c03246c0d01903c20507558200010785031195005010004001d4904004200303040c60b00071001030001400d41e000c00c509803080c1d4070690f80080e0b84c1e1410000f580ca40c04100f0002d0510080144503502c4004a040e0304001c82c1c0c0c4011841c0d40c0840025a4001008a00b6a04441c6400c201003213283c100d01c002418412456403180d0000b0420340340d0070901000090b8140502c00a20001041542c00d00044480e80c211290070b88200c6454070b1442a89507113000303100c1201e10720382c2000d40b034070762a07a855505041c41880f01c0000281701c1d40d414002e40c50a240308004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 967002724 1250 967001474 967001509
    0x3060a203a11250b07140d060b09091e010501080901200711090417030a020d0507020723010c0b1f03050309010305010512100b01050c030a031508030703020718060b0a0e 74
    0x43d4031880741d8540041c40700050100041080411850222020700300948650100080c400d01030a619642e03862142c0d00181c10261181108002140368690304c0e091050006031234524210180c1e0821006580b42c0e9070150400701c5543d80c03814031200301c00740b24102c0101000c42c224201e647c0e091a040c8215103241260031f007481000300c8414440018404800b04140080c0000304540340e59400003076038000e016864524103030310700300000c001e02103501084510a4408404100006501c4200e00007e080041d044040c0811513024669000c00d0310300d25215032125850381466141896088405080c0220b1740c41180e055201040c51019036030103009041c0501002d0710081a00708081d00345a039240700d502c000300211540c42c46c030380045034131940407194050140300890750b88544201d0024020b007080081100f4a00f500c5002081c00000402141c0c505c50305540100348042c20b01c0070261a030100e140c1c43d50f0310135640e1000025920400c1c4040c1081d030410741c941c0281c0707005038404d120040c01100507540 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 967003974 1250 967002724 967002787
    0x10e120705030105160f03090c15050c1b060f030a1d030a0f0813020402030912210a0504020a1e0302040606110f120f090f03060a203a11 60
    0x806083e032090b400b50b003610346c1d07150215a400081c05c080c0c10501543e000303148030040041c5502e0f00c19800400401c041820141110541e41541c18000039050001c01c029030b100b001041110324040700c813005036400c2682100000303005030000300c40d000403021042c0d2502c2e060f000400c004442d1034118001c0c0c40200c4590038520b80b41d10300400c110341620300343d0800921503903020010424044040040a4044003a010503594a0b82d58008008841e8125205d4500301c500000000e102e404035402140c2c0501c0c3c0c0501122174550810000c0c5080c1206101218000401600000007594aa01501c0020001919086400c418007400e160401c6078049414800c5c0d07002c5809049800c4081c0202c070201c00c3c04c03500b055101d0060078002080004a0102c00f0343c14070038181400a00e0a083c0d01c10400f08500040f103940550b88040f1b0704a0b00d01445181c042c01c207001000c82e981d4084d90a081c00f1032481d10098030012948420840c00031141c00890b40c103144500840c01c98911898801f56442c08403091340c840 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 967005224 1250 967003974 967004011
    0x2070603050f070309030522300807020607290108031303031b0501290a0b0306010f11030c010c020d050c060a020901030b280902160b06010e120705030105 68
    0x520b840c40028205804260340c880745002450b1003101991028904950b200070700c0b884028440300142e04500030b10542181c1e218180461941000010031503481c4034515413800700132a12030700c5183c1c20590081e0380102041003510001410106c040e910002c110041c5000c2c80030450700002c0c4038070143c00ac0383d10355004002e02d80001e03800103011021290301d071400d00c0c41444042c402c030300f183c81356020081096091051540b4030184201403660050420008200c17514840d00402c000039000b4403c8107403038036007000807a0b8194810160800c11010724100031050110602400c0d10f15400340d880031100365524004260301d183c0c140401114a68689400360030a032403a003101d915400e01070440c001d4160b00081d020050713402504580d803840c00007080494540d44001c0040c488800814403d600b2101070100460f003412140309640f41d1410300800d00f80c18008690360304407200f2020301801d050000c0884a00e00c0e03951180038858880c00b41401900001e458002403600b940c802401040e04074a00c940030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 967006474 1250 967005224 967005241
    0x9030a020d0c08011823070f180c02161e0b12090d031a09090a080403080c010f15090b040e03030c0405041d25030c090207020f04090503031317040e04030207060305 72
    0x20078410340714201b4070380c9400c048040142d1500800d580500b1006802c0307600040c0c4082140022010310022000a11015424501c00c90b260400411040d03008500b0a0090102c81c2c9507608904c0309210320f468603030400e038882c00000c1060708120003814040c81c8040c2001003050040c481c030150030350641014040e00288202d9050310078903010b0254020584c81000032401041000402e07440ca801800859543d07450f4140310300c295000f844040219800c14050420729202ca200300080c17031256030500d002c240d003044501401ba0400d00302e017989c0315491740184510100d042c802540144460f201d019556031601b0240700540d21295001200c0c9803420581e80052800820030395819071980402501035021a00c001c03108900a0b00701078816404d104c000306040c180c65004088244c001c98201c210003591108100564150080c0180943c10034004652080b10081c41c2965591042001c0154940c440001d01101d41195002046840c420001d101c00e1507014400c18000d00058601402580b03000c151 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 967007724 1250 967006474 967006493
    0x10506130c09030210030e072403020325030e010b010302030408043005280510020d23011403191509020d030c050607030c0207030809030a020d0c080118 67
    0xc24008a615248164100c0d8800c1c0803075000303154000c1044110b07104542001740144054030802240340320308139021410750010f40581c2c20148001a0a0810030360800080700650400b41541240d11500c2c2000d1003070440384919280380c00310b02c1d03030006071480301d2016403800d5406c2112805d061620400c18400800c1100c802c4070107a4030440c445260303140015007203205040d818003602a070440345a6400c401c1100104200340c0c61032000f0b01061000020000e054880030040c640240158414045011442e5164010304181150107100042c03880074550b00482210100c00010384981c007040051040b03002d20341d07100825100540040c541030300400701d0480351051200000c0c0c0010182d186150000d5030641011440e81e5000d40411010401c030302d0007803d0201d050b141102c05010350b100140c6054401d00c07555641d00100c0e0300802c40c1519648174050194054080d254041c0228507841000d84c81e0142c14103042441068440303451841c02904500310307101d50030040440d0b8000f00400001c50070848 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 967008974 1250 967007724 967007749
    0xf0605010f090506131d10240f090504020a0210051b0708070816080a140a09060509131407020c01031a012d020a05010614060a050714030f0c0d02010506 67
    0x1600c245c2d5410b0400d030b0360000b5820390b9121040300381040364074042c1c500d04851010702a480e00c0c0031500283d51601020150003d25107000c43c0614243c40104541d14070503801c0041042c0340d401c00c0140580c44002183c180d0b0f0107980c0200150b840b00d000720305501070305d02c166903020b603007040c0342030016001a844400c00e104005003c3e1a8407404103c1e0000e00c00c5800c121509180441001c03450075650b490941c0003a00202800300101c1d582c9076120b4010005102145c10380c07406030361480681414441c06407600d0300401c00c0036800001200501030740c406284a11001c1c05444520015130303140000307000f031070450611013003410182401004a840d2524443d0b61480035801d0901240c07a00c1600d2000c40001e00d90031120004120000da00c0b0703005600810684c0c20540100020b002c89511510301e400c00101640714581c01500801c02590300c0c91055010f494028070030b11224010017010220185540c0200410081c010000074680d0142c2d0401c2080803c07000b4071780000d000d01e1801d540082c85052028 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 967010224 1250 967008974 967008979
    0x30605300d08070503090c03010c0309022d04110706020406020114090307200613090506010908010501050307030807052a040507080f04151e050f1b0a0509150c010f0605010f0905 78
    0x1700101c0c0d01d119051003011551040a8000c000e411152034006020309640c000aa0041c40408040c005500e0b4820f10000011501d00300f01101a241c2402d100040900031b4160602c2c040502807000000c43c1c1c0d000038001000d0960000c9201050b5400c807944000c00984044040d40c42005442c0004076681c0c441c2c0750111040c0694007144451801091852050300d60b5a0225a400316000c00e6010460344400c1c014030003a0780d140302441e10307418010700300ca400f8001c480d0f150340722110801c0050940401001c40910450a42d0b907107098a0841c00d150f02080b503e003004a41c1c065045c2007c03400c151003110351103141c524050002e0305114000c00d40005001c1c0028051401744800389000d01644e42048000901e82c119100c1084001100040249010b036806079004100c82302249102c030101684111a445546070700c0d20b04dc00703910f0190360315880018071a40020036800c50b903911000103030291100348104800812481603c0001e130084035565080541880b00d10460810030990000300b100c20b941e0207 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 967011474 1250 967010224 967010227
    0x9080f12010b3103020405070908010501061106161709010507030f0c2313090203040c050301050709230907020c0102011407140c0f010203090706020c040b0f040c030605300d080705 79
    0x520161a40740c03c015000603401074101030078032216580c08001c0702e0881d072030a03000b0807050743c9030013040780c80380e0400c58411005d40c1700c040481c10b02600c0100d42c800960003410050300300388440d4540305254600b12071019599540303100f081030042c4c15000d00040d801081030104101c58032400c000d40820566410f0181a0b4047c0d051054080740240c229040c0b200300c0c5040303c0c0d16a9461221001950080b1402c81e6071141050780002d19080c14081d140c010101515400c02050030036a450b4909803c60403680c05000c5111461001038803014642c0e03015403100d0f40078010105200001a0a4402084840701c010310302d04200300c04258000450483c220307a0480d200c3e59000310080c0b10307242604469100865500c00024004848000100c4404480703944d02a144514100020802124070109a140e0803000b001001d082a20b07055001043c0d0002030f044c00205552250b01140e010104078900302c03041d0802039488410103808560140010300100001c0601c1e02200b14000c014400242102041c07000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 967012724 1250 967011474 967011547
    0x1b041a0d0b120109140106060504121109040804090b09042a0314060405120901021b18240d20030703081303030801060c0c03120309080f12010b 63
    0x5141d0001005814010008801e8001d00301a0900802075507200316181080c07020501e201c40018004d201c100d4540d916810708061501e540c54928a401480840351104848040041551044ca509014078015a030340c079160781c244a294000c69600c901c40d80c0c8540c1a40d0100b0001444010784040b807142448040038040304070500e50200c2d4106034000800c114000c0340c45074014280012082c4c40380340928125014010b02400d8105540700308036840d4010703000155081001401001380401495000c1c2c0725110903c0100075800f041c0b403080d00c00700d030044181c80c501c41c0011801500706985807803c9941260a40d410b40d00c180300c89035034440010300000c00a450b03003096035041c0014401550810300580e5100080405415400841c0c0802c0b070100e04c0c040c0002c03401910948079071000e680d010803170b03924903130071a00c0d000401c0e21900010000c158a50080d500000d1005014240f003004030380d92a1388840f0400c000b0074102d84160440001c0d100d052104615188810106c00760000d00c0c0c0075003507580310 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 967013974 1250 967012724 967012747
    0x14060717090f130b030c09010f05010f112b030b0d1403040b0408010c261b1b0c030c030c13050a0902062107140a18030c0305061b041a 59
    0x1402d208410b6101e4000402d40c02c003440a50010031254604074143e400d000b840c0c01c20004281c200780140c000062003883c040c011940200d640070b01e115002d080c151310381003409114a10300079a8031417074000561790012119810302d441129003102001802d092144504150200d01c880500120250a004840c00b1400c0541800e0040324043c1018941441e5100d4a0b0725100f4040e24084a6140000d03e0410320510000c00c0403040706100202c4101985264503000036406a4040145100c03c0c42c100030032a4111074402000902c0c0d01118040c0580075507401c03c0700701810541c01054081c003070b8110300c1141c401580d80d100d19a1200c00718200004803612049031a0f001030100b5071000350060400100e90000481c49042800000e5200c010401c8941c3c80c56012598140301490039100c2c1079040c05481d940500403086650145040d18203191156a42d446801c0d800307019600c2031301c55030005014020101d0071400d140011880d81e00c056440c0a190040058048920161907003030880e000c900c264481 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 967015224 1250 967013974 967013989
    0xa05162102070e060303030402090109020711100e12060705030408070609080a0905041803050d0c11070b1b0f150411040504051c0804021008060d050f0102041406071709 74
    0x1461410400255841040c1010795a01c1a50195100c10310780f5400103240b40c42c00004591040f5409081c486460f46051040b1000e90040384084a010088240e086002d49031410300e1b0044d03a01030342c3c604000c040002d050140364075107816494000c0d00107500300030a0130b4100c41280d800550002e809680c0e00f1081c240440108200d039001040e21a000594014555114080406507502120104240c201310f540940d0502c100f41001030101d1020b100030050040e10b0f612921162079141010703410309102c9042c0c9403e10042c0d4000c2c0c0c0c100301010660f0034050b92034030321680b0910282e600a1101814000d50f1a54400a00500c8601503005400080402c00140034031000c9074409001409107041610b0410340361411080300309110036031543ea02d03040d144030342c0c009030103142c014001621442c4180001c50b69044010b0039142c001c001503600b02c1c00100100000c2188040e03c000042c2c8a41c24010450800d810000d5010b204040c20302c4a02c1c0828100d803110001020751800f42591002c031040802d010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 967016474 1250 967015224 967015253
    0x7150b030f010f15051e0109170127030e09060a0e180c01080705030103240203040c0501020c01031e0c030e0a050706090f0e2823060405040b0a020f091f020c04020a0516 74
    0x20300f070b87d4410800480150044041800c2e02f074203a100d4101d0600a20380d4480c0360480260000750440341040e09402d10346003243c3c0100c4050480c0c02c48648900e943d0100035815074041c003442e011990105060341c424441501882d809103007031042410440c20041950206000181c0032180015544d000da00380ba040d00484289102e80c255180c2c80d00381010f08452203244502c9004d805080342c60b2250350700c030384581d0380b01c0101c186650701c048030702c45051350041821000c1041815602d900e40c0e090b1100401081c081ca42c4284028455142418001404c903001940a100008801842840b11040c82081d1903802000d0703019210240b0340d41e001044540c0004040c06c49440d107860701902d821822904444201c103224420182d0640f100d6040c001201c00440c0c01401c0282c204000c25008001600203080200c56800050308210395640000c212003800c05940e941241d007074510198054052159036021042207a0460828840080107011481100d40840e1510b42c2c4c0f80601040001801d2400c48 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 967017724 1250 967016474 967016489
    0x170915010303020309041103071b080f0f030a060605040b16110a080703050c09072a0b0f04110301090309150203120103141b010507150b030f010f15051e0109 69
    0xd594905029482e40c0c03064000074080c508040107542c0703208410301100c2c00f640055841e486142008080d12411042800007111228010000c1d010107500b0b1001410421b10b400580c1c582c0c80c2400c1c1480000c03140c80ea40036030244103050204000350103880d0252040301031044c061142e0a03d161611a055095008840360702c00c094020100312080300141e0182034074440d8044845451081c4200710180700704640d24000600c4003129400c100c030300068a90098411800414200c0040b9a82c0e0b200250040303401341b5814080100308014000d620308281900709058000300907008a5072001001d414081c010040c10140488002290620802c00c8581265100741c00784c0711542c40e854402c0c225815800c0c40740240c4a00011401820340e90b000703905400405031901c9142100c0c0755918a800350a0600d202c283e41e681d0284501e2540b42400307001c1541e4140b4000140d00c0c1c1003590014119004c9008105d800e1003200403e00454480c0c40030b00e180302c801e52495203039072003448004079000d0100380c00c03081 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 967018974 1250 967017724 967017763
    0x20409110a0b03100914010504150b030a0902151305060901050403050321010503030f030114010537050f0904020c01091a040308061f0c0203010b0316051903031709 72
    0x103110800c2c41c069402007904d01003600c48159115414000e03141c545c2000d51044140d5401080302d841d29500800811101ca40b210246603518032030600c8541045a1003400c0d0341d01c50010320210714140c020210301c2c9405076181c07801c0802c80000101c1c3c1950f107004203800307100c00154070f80319a801402503400071a4400c00322683c0d030f40d0303811022048420b1000c640403688401000410213280100943e290022200308240c19686007144040b000040381c0c00080c18402d08111101201d1903000f107200301008c6d140e1400744030304944100c2d0640030f5586801041003010a004c151020700c5001c040b14500f44040340c0140c0c40707101000e0240e00401a03904003c00182c2103052a807a50b8403001945841503019454418041e91030105100b4030019000312070103800c141d03070403920302a401100f280da0b1990014000140d18080c540c0800c0c42d12000403902e82003807403e99010072641c0760103026500412130700d031079480e00c2038074641c0c0c09000d070f1400d00350302442001da21001a020391800c00c511002c1152808030702 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 967020224 1250 967018974 967018979
    0x1d060403080d0f050c0d0504020a15081608010807032d15060905060109030b1003050f071a070b0c0d020904111b1c20030c070f0819020409110a 63
    0x70300003640034940b0081110304000c3c0900319507100d80f00d4284140395aa00103840c00003500003000003881c000340201d034050211000400e00261858060100c3d5400f6110440c40d410b0000308034007a8101200d03450200302c0100014840a47c000c10f611080740d40c00840d4280481c0303501c00d0040c00c3c4503800540080c1b0300300d002c601d4040c45901c1801924210f03012404001498603101c0c0c640c25203004072070150216049a004200064144041a070310885103124a00c980b5140d03501d041c02e04580403400c080a6000b880140115801040311100309045420b0441c03409410303595401e10700078001c16000c05010041440f10311100b150301164030142d0020300070000c03101048201c0130f0b04e4100e21282101c01e498611a000d03c508006600c425001d0b001010410f081c004803c00c0380e01044850794080c02c0002d90103250038240d020009005191103401c0a4115282400c666071484120759004a02650002030004800ca07914000c0e03166450b010344000c2259011801c120301c01069100b51140c005c3c10a8500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 967021474 1250 967020224 967020233
    0x2120705070509011202150325020106080c091608060310021201260c090c0c060f041b0f18021b10110901021f0e0706050705070e090309011d060403 65
    0x30301d4241c40c01100c40f04100e98840381245c40502e40644000e4020317460102e12184400014013071503000008e032042c0300d00c50003003a2500032030010201e007800150791141402c5c002141d05100c000307481007041e00c1020341403405107020b96240455101d094144442000460b00300e0702c09002940500c05805015035842030041c09208189409201e549900a4281045c106400d0005103940d400103c0200520034401c040b010403000302c0018104000742c103c200003401d2102c40500100d03111755804210101d0300e2409080c94841006049095000b0140e01d1400344080120025110140d800301042d940e4129441c0915000910075610340d804401010070301407555001c0040c0c0c2004c0800e65590620040706140807200c0e160140d02240c902607000100052207003850321056000c100c502610104000340d0b5503502c2c60800415070040800100c0008011042c4801045141c0050040a40c0f84000c3d203031140f6040d44034050006124100009400c08131103200780c030300d2128285e078002000702c4e40d1580d50703240 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 967022724 1250 967021474 967021483
    0x60f04150e0106170402030a020f0310060803042603160201020309090c09101d0108060a0515040e0723031305160810050708011703130303030b040b0f1c0302120705 72
    0x207200300007640c00c4c445048800c0f01021607401140d02130020035041010758200040000c6d0b41211517014880c100b0142101003050080c00d004003030001c0036594aa0502c44010064420b5941403000004484107025038020008210f80c2101d105c000c0b204050710341440100c1c194420f91f44105d9014103c5024030000303001d86001041d81260072140b01600c1c80c043c000a8544413100c174010704020402840030001c40d405400c1c250b80c8031400400c1d021500d601d0b840029a103140d00c81094580c2d820110303007403103800d810340c0800341c00030341600b8000c1100c01114071000d04c560040c03401c4808500f001c0301080a52102d0059400000e500000742c900d50000803031f000101079600d100b192141e1040c2000c402d400d2030b6500c96140111034558032000168204072001201c1540a44011003510081200519101121103404061803180d5004244005648100000d83d80400035151082909851905007543c40c4095100e260104c2002c0002c117851301d0a0513402d2480380c0c005501e9494001400c8800c1140206 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 967023974 1250 967022724 967022729
    0x18141c0e09100b031f0308130e0f04020603040609050c3a110105070c0812091f081b0405030f070611030a080105010c060f1401030c050409020108060f04150e01 70
    0x1e40d400440d40d109030209004038001d01c50350011903c04c2000c02c15480080c440060015540c842c034000c09541d940c3d622600d44d000c03428481d180c0c10322040c20300001b07925480c03d41e041443c1c04840040c0f0b08198000500e90b100241c001000c0540d5004080b040001c00d104880700071030b00600d5030000c00d0303502c0448814403040030001d9440c40d03080e80300a0409422868500f0319203030000b0540e2001c080b408010341d540e80c0920070644105813031103c0081d0702c401c104038080c0d0f610003481c4903a407550700007414012a83c43d003000400e00002e1030f11004412035484540c2c1035104507280c80e0340100c40d0b00000d680c129031151b60082c54050051390700e140d941ca107001507843c3c1190307400c0d0f40c5c1c01400c050045040e1b40328011442c01c50001045040101320395031003000c1d0012590302401c00000d24802c0031800c00100d03080030388800221040040100140008d043c500402048240e40c14449503645a000920403034004150a200e0003070004019940d848030362201242c0f02c1c0310400f15241646800740c10040101c2403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 967025224 1250 967023974 967023979
    0x2060910050a0b0616063605070506030103051005070c122109050304031106090a063009030e0603070c0f0c0e0903030405010c022107150606120e0118141c0e 69
    0x24818504c10400c20079210b400c1702c480583d4007c10300b42d28040c2010700c1204140d440b8402d00001154a0b80c1303850055000314491001401c6841460810740240c0708020143c5040c0191110f00b900491085d0070b06a441d44514a0843e101011226002c410349521000101011307290080c0300b02003100000081043e40d0242c40103800000c000402c00565100d08100c0e59000808198108000d500451011410302002100307186848102100c1c00c01854001540800260700c819142082c560000744203100100203499891079440c040b44050700019a9410040000480589400c10310a0781c0d603054000d08072103503c1c01c116080000c4842d0b07480d00150740c2035507154603005200c66514000603149941c4041940c442c11040b2610022660343c0d00076100c190b46604400d10150b0344c000442c8110005016039882c0c030708101c441091028102e5401448000581c1e150030904504003400e031130000005a40312400084030402452080e041804c0601c2c2c0544103d03040102c20942034103e1808403542405 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 967026474 1250 967025224 967025231
    0x270f10060f080d0c030e042d060e0c0747070804060515030619150509011a0d1503020f240c01090218010305070602060910050a0b061606 60
    0x640c40c040c03607081c20900ca4801c0d59031100100c016030324041d568405455000b07042141900c3c222501090607100444842c001101290084150078110b401108552600110041281d2030900c03106249108010b8054048400040307155403c01002c0d030036010391400c49545402500c400604042e887c001c000301c903441c24040d82250000703240840c0d07001c940320f20540e503108000350701d9a031100d800806014041045d1581110048000c6403020041c49000302c5c0c2c4089100d1921140002c00c0048400558062102d820103080400081c1e59050b0854152407540f413012440b0841d50340101c07a5441011086580d41e0300f88407040800c1747c24110320784200e074001c1d82c124903041c003584104a08040c0008540b00521762003007142d225490585c1c003410382d031a2003000000b031100c050380005000c41d1180720a0782400f0200c0005208019003400144014504c90006103120708203108150f85a0b02e40f0005071402650b1800001da4094481d00040780540001e80426603e006940d5071801c401625030003958454103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 967027724 1250 967026474 967026479
    0x1e02040305031207021207060507091203020f0606040b090f250503090106060c08120414030d050a24232205150609090606070b090f01060e04020603270f1006 69
    0x1c03070342c1d030b5000032420b1480b480c7c4803182d9a48001880083d000c541005000e01022840703003510305e050040d02c5c1c04ae80081c400b14588000b040c3c90001c00520085c0281d00b808115502500c81700038444c3c000c010811082c1c1d5550340d05400390000d4809039200c4d0f0780a00d001814501940e0010021341c01142460005d0240c82e813210740a9990900d0303003800601400003002081c00ca500020380640c1c101d4420341c3c10030034150400041030303e55042403514454031680c500030700c40228941c0c40383c21452501c440a82407400008440b1181c411a00c0c403868281c3d144c00ca041080b81c3c0f07001650310310352002c010103428040158000b8128030350042c0c49040b00700da1600d80820b80b80d40000000c010086c8000344060f01c2c2602e21803d0181c0804058200d0f034122406101c00d1001992815100d8494404000203083c441d1500407103a00355607441d806422750603020018000541c403085c0449600010655414004108d505000d0000000a440d1a41d45000d0300d030740b60044a50101d00070580220f604c20501c040e43c0c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 967028974 1250 967027724 967027727
    0xb0f060304141507140702040603020301020f1b0109020a03140c0a1203110f0c220204030b040b100b16030e030a03030219030203010b0409051306090c030218070e041e02040305031207 80
    0x200f055540c034010524003000c41d540507414000402c1031030b00c0940007299540d034990101c2c0c00da811486081028100100700c0c500640d1030001c0c441910100f940c002e0002c02513580200340301e080d0501000c0e00b010030100702003c46250030000803c04200250001015a50324209908240002a8210300007902e40305041c000c1000082d0900810704c4201c0a8080259013000300b101c109815030042068082c2d000d0f031004100428409000154040c0507a40c0103450b0900e0301c600c0c2070000501c20b42c1240086803040c429aa00c1406641c12881c1145071003a031a1114103042d01d0504441104a50610030341105104059258015180000c860200f000307444540d4802a007c0c1d001c240917a0041c0c80e002e020821181c122a040140c1181d000072110100c1440390710780300141d510414040e07034440600c2008104500b0900d0f0304aaa03100380c1c40400c000c2d0300781220000c1000007044080c40c807940d1900500e0340ca50328551010802096000d030210b58035a5207203441e41e02da400c100445000d034640c0d200041d6216 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 967030224 1250 967028974 967029013
    0x604030203090112150b2d03060a12030e04360606050d0807300518090f0a05150d06150e0402060d0e010b0a06110607030605030d030b0f06030414 64
    0x1c01905d10102106040900c0285550445001130061180c0c01d8084014000da0050f840441c0c03443c0409a5603a14010302886070440d070700d41c8460400850b1302c40c00e00201c1d6010000c42c4640a084501240601c04a51010806d1250103001025503645009000f416100b0300d41d1901058443c180c103000103640c070003c00990401d00040500047d804005080014004d440760840c1030281002502440e18202d480192410b070072078035080418800151000c92940f030031007160324520100d075088807500d000303240c0d208504405040c031100329485034081910000c3c00c0c1450a10f00d9000740c1140041402414640003803c81d5111015000c03441c0800860903500f40848030f880b55030080c1620b45003c600380075180040c41c00403500781c5107560325400100d1580d190000c050041003035a94040380d07241c00034802424041c001e443e25003410f142900400083c0c4010940c038200749007500f00024149601030104684003420021140d02c50301c000101300c208200402072440c2c001328081150403990f4981c02c0c90904 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 967031474 1250 967030224 967030241
    0x3050a020c0706211b0305010819110321181f0c05160303030509010c080603070b0a05040306020f0a020601080c0604270f020307030c02150a05180604030203090112 72
    0x5600030010501186028001c1c40c00100c15000d07000313012510305a060002c45d92000344101441e44101501c99045034580605400342c03407060041c0051070041c0035840c40040e590000200045030700b02d00034500e80d40a000d140460911001c1c2c21f581181203422990003035010002c10303584403203034040c2c02500741400700790b81c1c2003000007540b50000a40344803030035070340f051040200700c441e0702c6008e4580303444e0f0b031800548a00071486030300e02081d2030a000c8400340c02d41711102d510078100034503681000040c0e580082c0c0740b01220003d0707454550390f0422050444041c440d03600080d0000b800024001c0c407681003440202640000c96095504598850311281e4460381480041544030380700f0300040c040303411041020707089c0d02c1014890801079082d803000801615042d801d079000d9907131f000c420480026007501804121118a01c0502540b40e0301170443c2c007000700c014250200c41e0307955100203201074102450300240d811017802200d055181c00c0c50700071b6586d0b114000d00b60020b41c9101d4117600c000840d0242824 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 967032724 1250 967031474 967031497
    0x1b0e0a0609290712030f0e0c013024050303130911120906010602010608070612020a02010e0a110102390301150e040203070602122b0608060703050a02 66
    0x1d10040040b00d21805010400200e05480e0100b100d0000074407450380e600340c0706039980c80101d601160b0300c001030102c81240646e059107400400c000c0e03000d40c0c2d200342d8808120400d050480075094080d1280419403030101c02110322145800f0381d0321410900da020340720405944150b142c42c026110710a040c0c6030b0107845803400500d2202c140900c4103030b41c50b4111011050718610158100102e00e0280c450410007540d421302290803401c018051554207014480207081d9172002402d4080c03034080e008080800da510665500340e4049030885d003941c800c1d040542100404412119035070514100011b003126852481405840f0b102c10441100d040d00b988141d2a0791b0303003444480e00d00b0083d45100e18080e4420300003941556241c80b80442510140140c2020b010142c040041c24542072040c146000c42580141c01550700c12003030985d006045404580c0d03201d103202d080750385103c3e141580b03000410401c4441ca10503800d040c004912000c0026801d8840d8403165818811916042d00ea281248100707040c100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 967033974 1250 967032724 967032749
    0x150a0c0807110603070518041a09090f03040b030a060602120708030a140c042606041202070503030301061106100810110f030f01031716020907031b0e0a0609 69
    0xc105a140a4003000d030040c0310000e000301d02c0310001400c03540700f12a200f01085003c903c8808890100c890881034800641341007064011207185d507072003950203030301c524850301803e800913040490900ca00850795040c18101c946941d21100e41c140180c00403079040280030f140c180001182c1e40300090340b01f428107401c4035483c03034240103440c2d41c06070fa80002d195a2400d512203a19246021814074028481c12203408a161100e0800e003408088030000e00302c4204843c070b085000f03200081c0114400d034015a001301c280285503500001681030141d1584450743c135000100000400d1900840500391360f22030282660420342c1e0b5800390360b40c19000d900032101198842c035601085071000364060240070344c021000500300010300c0c03031118440d8800c6a500e100e00c40e0714801041004840e20740e98030590b00040b0f5080c1070035001c40c2016800081d034080648207440840c04140424003e600594948140003152001c965035020058401c0c00300c040c1032400341c2441c0100280c40c0307104c0d860b0b0f90191510840c420 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 967035224 1250 967033974 967033997
    0xa1503060c1707020f21030c0c0712031806052701030906020c0a020a17120307050702041805070b0a09050d020609132405061603030f0911150a 63
    0x9800030160301c4041814400c2010141c0040094601c5542c420b00142c1c0c0242842100703d84c65904082d294041e00314003c03451900a5151042c0710281ca80c016a4440b1031511480c6082000f0714081d290341c00382032900b1b0107900740741c01d05600c507801021210700800380701c280e01c1c0d0380d910032240d6200701c0480c52203d42201070134101022809081a00841c1705140c04104240c8680300c082c104e03070120011a8040e0300c2101f481d4218141592507030004c1c00e1400d6442101608a811107803260604914400715404c00000690744501801c1a0b07900290042c00401203121003112044801d10486801c0e5001d1040200000f0b80078161400c4030600140b65a4100c885860601032000d1200c0000080f07a002105001010741740e03d4803068905141c14a12011540c203e2500d010311030f403615602c1c82c80041c020840107000c11b40f55a0103c0326100151240200341c1003d42c2000c400404400c2c3c0d100b0000390400c80703200306210b403001c410050340d4000c42d80c1814540c11400c0c1c016080c426444914042549034400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 967036474 1250 967035224 967035233
    0x12030304020906030c030d110f0c130f1830020c0d1412120a0204050a05270c04081c0206160201150e0108010e0c130f090f08030405060a1503 62
    0x30b041d044080681220100e07004840001e0600b4443d034111000102190541d807000c0108001c0190740c042040080c24004048501203a007142c1d0480c08054100d45410081100200c250702002e003040c451181705000080c9880c0c52011100502440c000c911008041140001c00d10700416064200d242c00030900000684244145038034070000c140c4425103013050b03080b0010020300c48183d041e069000010703501c0060382081503c1c040041c1c4000d14042c41840b007401541c542071001c40c183c4004030b882400104c142e03c01102400c1841d000d2001646800041c05900888000580150313440d010540d03402549010703000602071041490440141c0c071820114409200c10410b0180d41a06407001003800401c1603c240c6450041c2d80c0201c0d0841814401080b002c3e400f0311401c0f00c414400e6014104902503032b000240c50020020030292010303941c400b080e03508000303a4001c008065104c0030469404500703061804484d0030440d0300f5581405608005104050b02d80310b0740b0072074001c860480c010b0764199142c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 967037724 1250 967036474 967036489
    0x5040f0e0d0e1e13110304030f080c0304081b0f010204055401061e03140609060612100501090e0c0a05090109032a0f23060403081204050c1203030402 66
    0x101c1a401c002c80340d1450581a14a0003240241d0005c8050b07a50b80c1d003050325004100000a441540c10468284e0900413410f0241d13046075000ba411081e041e44400e04894003109040b5105003e116610902e00008410801900a001100c41c2150b1180b01c5400c1c030300088007019440c80c041c0c1041840c121801210340009040348060054580c90400c100e110701d0592500704400f80c20200100c4c3c0100d40c40c0c41c0b5070711002d146e500309642625091110030300b00c100060b14440003501140c85203811000094558580009441c200b841e00c6000311628140304400052240b590f006450028460707110105103030036a01803c601818084094a14240c1c903e50101c4103904880801410403040403000030108010108080d0000c4540001813803540e1329038501201d01a0f075501511080111000070008a02c4160110210143d18001d00d801c240d01c2900246441c4116040108514800b00e00d524903070802142651145200d681203809090a0070308101c0350940c0d0700c06c0e141d4140e10400002e001414000c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 967038974 1250 967037724 967037779
    0x227010801050c04060507200d050705090106050c030901030519060914070906080103080304020d0213024f03050f0607180506220803030711070914011e05040f0e0d0e 73
    0x8c00812034004001070b180340300d200020f4810380c2c0070000074880340c41c100c01030703030b0050841d070609515041c40901c15549a009600c141c40c141907640d40010303139035801e0700030548030a803090070200700c4a030721010b1a400070003090080040c1c003c02c290006145900880d03540040d07407a2500c0e0302016a195503180c1005071700c01002280c00010f8111003400584039401e001c0c08170910130601586030328040c2007614030391185511907101c60fa80c511009010700702002600c041400340580724082950300c5d41d414003602c1d60304d0340300070113500c0b51144580514034041012030240181d0343c0d40c0d001c0c5d224042e4000c030804602d4042c5a600100070801460110421039a0312a240d0120030507403c9180d4651500d4115041155000d020401c2c010b030603171010030140914409004402c80801c14070707200000c4074600f403c0501440b030403a0310700b24444140028001046000300001003013808100c03002c980300b5000d46088440d01b40350b0301c545da402d240101d0250039111820300700230b0030b24a007040461b41404594800b00303 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 967040224 1250 967038974 967039013
    0x60c160b03060904150b06070c090f1104050103390206010b03090303070503131b06091215090c080d0e10050c100218092406040e0a090227010801050c04060507 70
    0xc85c0d12606c9a210440909891401166203050203468800c00d4000c0d503070902504158545003145100b610303290001030b942039078030030701c1c000403401d24100c1d1404c40316201213911104e4215034240c0301e20050311510708032061141c6500f03461990b40e07110703004010740c0815610f410b0359402c107100048031a03205801650380f041d080b1380b01d800340c0d002d96181c0851141c04c05040c51200c00418405110654022420100412001141300740040d00d07612070386a414140312020342880d890390091030a100365091194090900030040e104078408a4001410030005480494091500178009241c0103000d42e054440580c249000380c0300c1c4030080320510303000b5480750031904039078046c000c0940b4954070703002c5403144203400e410102c4103d02c0b0528403000008958400d1140300e082c04000900c20440100a07564000d9030400010420013801d1001900000303c54401301c0c801d02c0c90021401501d044226624101d42003603000301f1207510780040101440c481c6006c0d01000c90740400606001840350200d440020052 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 967041474 1250 967040224 967040231
    0x1409070c020d2307052704081605030a0f02010b01032a0504182a09170715120b041a0603100816030605060301050402220605060c160b0306090415 64
    0x50a03811140420303d04001c126580301c5841070010741825076910400c15040384806030818480742e0351000307000300140010007801e4081407604480c0c6400c903004074043c0d80700c0141c17615840304040040400c082c03074003240d0056003410040c0d243da5010b80f1455184003070b00f002c00c1c1e1030b4011401c0b29104251031541c2c0c00e000c0245c2003000140c801180300109101820048020490030311079000c2040d003003102002003401c900e4814500092640100d4400100e030704013403140c1c5d07805003180200c40c1030406039030242c9951044113106111096203c074143c01d0350714401500300004e180880c180412a803401144004d0500f255507001d071103280540181d07500c0034400f054103424540b516811400c0c641007461502e40c0759100ea03014000c0260900a843d07000c40140d0080203285400e80004103000e080040207144480741001c0042040244d8100b1005020050280d075960705200c101035075070303201110b00d5180c2d920b203522001c56070070300c2e441c01c40703001d442c00a020040c44e80701d80d11400132043d04690340302e51203075a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 967042724 1250 967041474 967041503
    0x924040b04150617150c12040305040906090204090f09081e071703040317060906040b0409020d03081503012013080a030306030b010509251b0602041409070c020d 71
    0x9003402008040d290079000c1c42604954031a40925140c803017807144142c104220100601d411710041a03078200b1000551004007600c50b42401c1ea103511658016024441c2080400306000340181c00510450303080c3c0f401045040100924401160f0502c0c4008100da1420080c09049494a00b81c401c00403007038002a62420300140e54aa00485607040c1c00f20035450041f0800c0141600304540e14080e89000203490018038000d000110341d200002c00c414450b694275019005103840b15440030f403980780c0c0a8185031521a0303608004d0701e07091040392004e0b41c00d692410811305608060145035a80000320407003420040c40d000c031003159074215490ba8810058060b01c0001c070300c0d104000c4c005566000761000105181141804141c1c5030058024a02038507403601400314464110750314000344600c0c0140076035002076894044540c035412114803600340351645400300500c275482d070080046404203082100f60700d0b0350109114240381e0444600011070160107548026040000c150400d0303a1003400b100030001c5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 967043974 1250 967042724 967042763
    0x5060921070305150112020112060306053105070e09010207020a140a1403250b0406031d0a03081308040e1905011e0605090303040f0e0924040b04 64
    0xc9003250006140d50254004000b8000203118812030300550313a0509040398140744240301840c600f01402410824040304100d50808154800c0e401b0355402a014405400c010064846006e8510304004a01d85c0002d070100030403403611092845143d103d00942400c030302e4224000040000280310107000c0d5000c00c5000d0043e9143d0321140007410543d0740483c110040c0314288a00e0007050b0300840e01030010b225555502d03550001c0c10380713200200c0403641410b40d40109000e0b8149160b503071048481440c0420081402c50301034002000c40c188a00c001800c500c40e114050303035980300e810805008500100003180d80c00300d000004030000d034007642c240c0349403030f54a140e00242c01c1c0b404c40301000e0b00814468003820621150080c180100300c902c1181d02c0c42c4200410401540704548500340920100190551103518180706403401018040c01c0904403a070340c0c0c6000c440707100c0101d50030642c0d80220314000c02c10400010380400441a11040660f8030785d901d585401020a000c1c4c03082c0c41025003086900b1104 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 967045224 1250 967043974 967044019
    0x8031e09062707090e0114090304031104091104020a0c1b050102060a1a010c051504060b03010e0a02060d020a03090b04061e1515030216080a020c120a03080c040803030f01060e011107050609 83
    0xa10188e4000c503607070703440e5042074414070307041c5850345104070b08021005000c505200508000b10504580041c0c2c5c5001640d0261910f5034800d01c02080c44800c12202c3e130401140f06c41d4101100c0081c0c09407403460742d030111440200d0348294404c1c8048001d81441e280b19511911030303002610312031002c980c52040d544030014010801111300703c0e080b0f0340303ca4564100303060a001d0113101c00c01440080511400740e0340001c0c00c50045c0d008016070a0750124100c031441e403103500255412600400c800c10a800c03c3e0800601900886810823004165207081e046001c280d40708500d0100d14240c3d4112451f828100c1820004815000401c2010f40900666100c03c0e40e0788a02c12000e40310b010030664032202d800000e421300040072500d501c2040c11076002c3e03010210105030040039541c50700d06415990359640c1520070300d00694000701c6d014030010081124080003501200e040c0d40309501c3e03004a440c3d14400440b004441001050702c3e5401846c1c0405c414202a00500940310000f803017440044484500d03035202 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 967046474 1250 967045224 967045231
    0xd0e0307060807120f05342601030f0501060e04030c0210050408011817040e0f04050a0f030207060e0901060203072d150510030f08031e09062707090e0114 68
    0x5046c0d684042c040ca0002a0200c51903059645981d80450301040c225102100608481d4209124031103416401501e03015582400051010100c40120358507410008032403125454126070540c602140030807002614a64540b142d035045e655551006001e0b400e1021410100007a4003e0207424400031030041d400f8040c9140d14416001415200000e81c00d00d4050a400c401071a8000c607400c22042c08494240011541c1c000260140301d1820703200c500d000344c5031140101e0041c00441460103020101540400d00d0401c40300d071540c1c0e0150500b8040c00b00040030000b84504005640100000000100d015881d102c841301030320007440d20000f00c1340141c07243c80c0004004482d040004860118202d64510509811030751052004e00203504583d0742141d40420011301402ea600d0100c000b98054144d60369010410038000c1d80358a450508036021a0f640d5000e03030782c0303002c180e010003044c404000301c0c028110160440c400061400300d1500e407003440241002a10b6041da0754a070b0b50315510006921a44602 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 967047724 1250 967046474 967046501
    0x30c140619020c03180d0606270b09040201110a1b06180b0f03090a080f0d1407080114060f070c0f08030702060304030e0117010e06030d0e030706080712 67
    0x106160079034080d52488081848154641e10510100c0c03903c03280002500d20414410305c50a1480c5c00d010000703407100c1d041c05c0c0000e01c1d007410b0090200304102809060451a28041900240c0000300c143d0f1100b560b4501c60102d030040e000300001005913100b0226246c40d4004041039400001d0161034205a200658544410148106c20200012607200710000050710b41a40303a880400e00b001c1c0703440300358810360302d00c02c45d00741000c0b02150140740107110702241c05034071440c1e81c0e941c2d101c1071140090b507030058409500e0f880e10b03040c03103a15101c010500310f9201c0c0c01150b607008002d07803c0403009622400c3e013019541d000742c0305000340142869103100034402c480c0501090350a00e4030b00301c21100c01482940040c0051340041c4450780050315010305136034205515041003214200440012500005204c10300f01017040400c00000c0e40608090300103000d03a8091303050f1400402c2d0b0a0054a2400c1c20030002c0750140c1c07140d1010440503114000c001d400c09918a40034206081e00801d440589583c180c225a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 967048974 1250 967047724 967047733
    0x326010303110f0109052e0c021516090506031005040207150c0507030207180b1c050607090b04090902060f0c0705010f03111605010b0303070b0609010b030c03070507030c14 76
    0xa1200803c0102c0448419200a22a80c481e40c0d4440762540c0404005641d0f450f042503260103081d09500c040003000c884100208a00b14904000940d100326103080c20078208105030100300080d00c00038001c115807607141c4031100000c1c6000103120466000401e0041d10041c400408106903966000078004d4901507403400e48044800c003031a60407920442c3e00300040c4a070400c9668006900403500d802102c15a140c004620340034405000d02400b850850254490341c60396403902c40e02c4508039425000d81c0110100c0d0792a079182c01081d02d802c03025008200749003105100822181c2865004007040b684007030700840c00e0560b0513503030260b10f4000200d000800e8000701d0082c0f00650748122100c1ca26042c91a040c0000b680d1325600e01128407610258803c01070184280909001d001d41022845800140440741d480d03e8505040d00c28080c19183c0501c0b4a8072030380000b610000300310a690013903c0075081d103855510b4420741900c2503400031a04406100c103502c011004900b003101303c0440401a1000380 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 967050224 1250 967048974 967048997
    0x1602131109030f0a0f060209041b0f080601050306150f09041b020105061e01081f1806050301090809100905030604080c0c0d121209120203190905030303040326010303 73
    0x10b00f8a041c0501a10055000e10a03140105540002518031103400800042c0c4e60002000030901428841174440b001400c96580d62042e654805100805002244e07114442a2218001141d0510040e02c0d40c81c1d02c20b55500560911002e80300007130451204000100703241004d00c101040903650f507004611031950030810168500ca8083c01056401101110b0407010383c0da94030f6861003440d01410490341003254000000c1c0100d800010781801c0140700c813501900c155501c903845034040c1e010041d04070700d035401c02100003400c1c20305000380004507500c0800c0c5810b00155505108030048606202410032405280c0001c441d101440b12070300480c040e0054658034152940000e2034085110101401540301400f0480407560140e25600200c0c0903103001d0381202600d2500101504188001808070b42407844200e011540000040000310340044c0d4410680c03403042029540d0040c80c0c450303180c06400c1040001c002a11484203604444414041030309000030950744a0030103542600701320013007001d11810 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 967051474 1250 967050224 967050229
    0x1018030305120a050403082404050f0a0c0903020d030f02031b0a030306140307060f210606020607050316051b06040f21020a06020918041a0a0e031602131109 69
    0x40e241e110f01510f00030b00c80d03424281e40041403d980100001c42010034000102c1c024148002940010100100309100781e041072105000d40d40760a44400050514284004030100d01070a4040c040b03980013409941603c403d51000e54007444854145070440c08208001400c0b0012144007038007000b9a00300a100e0105c0d01c0c40e000c0c045032407941020224001d448400b004955002541380c064540e41c1c40e0204500350941400c1c1d4118205031001c9d141821061403000b010341607544000304a515540c00c03185103032500d88013034805102c151013103542002d0714a0384882450240d001804142195041d4212184001d0f01d440d007001d005403030032242c0b04071071564403050052123907601c1c00c1000b03261200800c134041800d000e07640380340c0818014050b035004035074a041555100b000c6240085141181035035450f1600c1c020614078002d03081c031a4144100d40114844210b0392160a459070142030085144c400104442d110101072045c040368030940c880c60b0442142d1140c01074400b039070040000c0c00c0d25480b00108 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 967052724 1250 967051474 967051507
    0x6070803091006050f040e031c090b070305060d060903260a0606110d0e0a050d0b01170c0a050909070801020c0331030209040f0f080306010f0c111018030305 69
    0x282c01030819000f48440d664503105070301e420300e088034005150300050041c1d5065011758826940b81c0d582c100c201c4a420350107508680341041c03085c0c07801103655a074244150200d03071040d1141501f00c0940c250340c0d030001d103159104100d031344d0084c10200460380002c8956420380701741e505e21810603503600f82072049070104c0d401504080c0c050350038114002071400300c0081e600e001c0b04000c0b5007004403616080b28503449000a03000686405400044500c40c1ca08061481400c00e100d010140c1004907240c00b0040310200c0c080c000140014259480d2624001c2040420100a8032098203802441030014028034240f00074100d0008480140d41c40e04004261540905092114000200a40302201900d1224810401d00380c031350440d0000071548560900031049a507c0000401c0f4084600121040c03103e05005103100d035200b66039240784004101011141c0201044004110070070340d40d651007407403816400500f81c040042c40c0c10200300700580d4003000540310562096010070300009a00c40039009052 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 967053974 1250 967052724 967052743
    0x60703061514180a090c0302070c060305040206090103090320160b04030c21080c060a050c0702301906060e1605250303050105031606050906031003020607080309 71
    0xc1000e0b01c2c01c6540c0044aa0b842030307682552840000141c2e100943d910410204007800c2c2c0c1d50401c00503641d60180c040c0081d4031052080d59880030684000507418420300801388211f9001d044207041404507c010340c090241080201c0c280311560503030103042c85042c808142400c152030002e1050005480c5000745000e0260800c2484403000c00040c004601080c040c1c908a9070007005c5400a0440400c0703d141010420390018072900000a4044400c02d0010300c00d07000303040c1040304120135103a0018130203a602c6030b03540080d08a13101150f0f021451910306c0070000c3c41c40c0c5001c178614101c44005246030030400411910902802120b0108040c80030070300c1084042c01510100c1c9815041000440d040900c40b40100810000c00242c8840d10300c030000c5050018580f001003824980401e8a00070380070702024003510b4004c0c8900c41e40100341620810030b0408071103030741d129246040001c2091007410340c0020860080309103012000401a140c4000400c1d0301801018541e0300c1c1d0038160750b903508041006 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 967055224 1250 967053974 967053977
    0x5090a051012032f030f0a0e0a05090406090314070c152c0604091404151b0e030309090405030d1808031602010b03101e02030106091206020c0607030615 67
    0xc191100003c0c0d00542c81441c0c49002c2a604030318802d461554040e0740350b82c04128001030001280800401650304007034581d81d10310380c40e1548901d5100c41841311045c5523118443d44000b41902150120b950790340011703521400703840e2840c8403607880d9410403c3da9101380310444046171012410002664000c0a0702d41e054024a44001002d518840a20380e85611030040c56802c00f18200c241444d035645000c980040c14038910900c801911000b00c00009070f411103040c0c1e02c0c5001015400141032941c8641030b003c541c03980b00c40c1b0000d8031400040311030b03900680d18990540b00810081d4040d03959030b0700c00ca100d94407402c0103540c0d404980180780103513103401341080010045030080100160901c02075a9001c176600c1c0c2c070742103070342c0403464128058030b1080c0c0280c0d0503010345142c6a165401c10f801000340712003400c0510035400041240c8408034407091068000151044030140800910313010480140d6014034401350a0414541c541ca0616100392001ca02196555001f002440d10f012490840031706036 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 967056474 1250 967055224 967055249
    0x501030f02120c0309010f0c110d0906050a0e030f0f010b0112050c070b0603010902040e03220e040609151515030209010c080309120409020a0801230d020a05090a0510 73
    0x2946048902e001001c0c0114041c01808400901116800d5011288040d1034101c03d000380310992401403d0f0344100180254140524884144141d004403c0c207400c480042d40d401c0d01d02030384004100c82c19802440010b5042c007545540303107011003081100845a5000c032000051608030a00007410741885100380018141c00d1404025545c4030000540c1c0801d0b80201c9401020b0f51000c001900405a03803000a500900d05044008620400009401c4001c0b040e20403421901ca10303100402c01c103030181718500000a42c440020000f900c42d4002c51400790ac501c0406403088400201c800c11703107590320103542800c1500a410030140510800c40d0405511506085241140c0800001d0184c0e40f07000002e016010004049604600100841d81800140c1c0c0c810360740701e036250701c5814041e6100c6107142c000501d0260022a60510280340b019101552480b0203039040400301c10312085001031407003030f0782c803840380c601c0020103444410b0160f1080301185800540c925009900211100d00c030307080240d441c2d56 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 967057724 1250 967056474 967056487
    0x212070f09060e010302120702150a09050c12071a070335041b18061d0414190312060b040605041a0c0a0b04140313060318020a08070501030f02 63
    0x2000510030003900c01501d0201c0526000d18010f8010b8407c80c1420501341d60840104030000b64042070b0100703c0744110b80c201015407103188100003a5070703911102034184d41001403400b265190510786800146140700944100c1980c0d000d00c6800c040344510301111404000680004065100640b14210b11940c0c00c40c03081660002030100c0d02c446144030b01001c0c4590f203008a4103010303455010040e034440b140000181c4030f0f00c4102032481c10342510b00d52102d05003410004681d0342240001103118609084144180380c5c4d0380d032642e2001c00008bc1440e2020b014210707103140e1b80080091800c00d400d0080e00c1da02c0110542150380341c111803066200104c503601c180000e0028540c000110b40803150600c0541c804142c0c43c09600d9094820515404040d201daa8480f00410a10226180c0300d1405411003403509008181c0c495101d10890140c400341803c4440184001e84c0641d2001d400f1a017401d0910a130300d0700aa02250088005401564482c1d01c508010403041d030303050190039140001a4002d40c00d119 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 967058974 1250 967057724 967057727
    0x302150a060b0f0702040609050a061404021216050c0a0b0105030f01050601080613060806010306060e01080c030c012709050a0b0d110d1e080a0908030c0a060e1f0212070f 75
    0x10b010f449040400e0000f090015556250441c60140401100401503400c00e030801d40010281c61054280d0500c0e00500100c0030b1916100b9034a044070304100c244d041c1d9917114800d881003101b2810200c180003080c402c3c0c2e03e0003041000002d0195109003411519075052a040525180c0c40303000e201904d0703052404002a999000d510640c000310103030396412414012540100143c500307034201c0700c138030b1152100000900106820030002c45070840c121038866625a90745c035031a2225038101c15055445401050419480345c01071005880100301510725800b04500581c400c801039a1185c40042c1d2a0000c1c006000d0b160722510442c520304999194900d0b040d0354034001c55505440d9000e104200400d4580f043c000070038003902210f100580a01302100c070b00d15041040f900311041031030009200c4100401c80c81e0f400400c40ba140c01b80080140780540300b43d5160701c00750850000e4081c41d409a04541200d03016145c0342500412005a4090b07181d09089040700c109800041c02c440070081d1018603075040303a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 967060224 1250 967058974 967058977
    0xd03020c010e0607061107170406090e06210f0624040f141807060912111315141807031503150c09092315030a0302150a060b 55
    0x20801e00345540050010760001d01c1d1401442401750400d0304100c0d2030011090318800800c0d03c2c0748076040e1022110386040a5440300d000781d002c0c410104102400c148130b0040080941c1d64071200c01400d2074010032069000b00b00d8841256010000781c0d218100c0c2500c1ca840600020340e21190f03620241501041881c61000300c1c0c0720a00c0d40e1805290f948064100315021a0814040c02c0300117a034031001c40c2044103008a803c010346035001c0329070260707980110703842d0b00c91030b0305000301d407140040902c0e50015912000002030b152041e180d40141c0114502161042900074075203003c0c41048049a090700e4504852100b442403031089100702c4210b40440b00645104d2070781900f1a03074502d0009076800480204100742001c40e080030741440c00b042d0361034500d21000d0301302c039103080b40c035680368403002d1b0381d46652006803492514002401c00032510480c1400d080030703440030743c82142550f08500d200c4520000c41e08040d80428140d00581114041c1480441c15240407608450b58410801085142c060a13000f035 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 967061474 1250 967060224 967060243
    0x9060a05070809031e070e240f0310270b1306110316020c0a0807051e06030a020306120f1e100606092d1203140c060f060d0302 56
    0x6022001c01e0350700c2440701d008141c820100c0090b003190380c03036070305101d00c00000380f07150244401c00e118614001c02c4811456207858080c2c3c040c28030608414090204050a03050a48082c0c0d404c412440b44107045035078104840a09514902c00000d40c03c100714019942d1031008202c49001d481c2c103506100c0c005003042807001c1e442402101e0420081c1c0d00761030054003030110902880c0742c0580c08014000d00e000d403400a41078880441e001c031203084462a00740003100341503110b119143d40150008000908003c0c043e0b80d005c0360326528042c1410701307000002c0e00d950005c2c0d4007091000c1d400300030802036080c012581500c2100200061442c01c80240f00d05660341c2c16080c452a102d0820a01c042c140380040040c0404071491901c184401a12140b00038101c202c80d104c2c0860301003007102c0003120800c148820340254600803c0c0100014100307014100e02c0b01503128224200481020f5030022031010700090401c4180e940081c2416060020106041290150105114242034070f2600300281c0c0001e0080355 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 967062724 1250 967061474 967061477
    0x3090a060c0c0b0414040509010c080c030a0204210201030b03070e160909051e070f051206010e13090c090506060a030e031b07210302070603051b0a020a0b0c09060a 72
    0x14400881c94148100b14056202e045886404100840c0c000391030040c00642d00f009036000c120b19540e40c05981d0907500d4420840020840c03000101e49220900c4001307682c014a04040586025500c2c66852104441c1500014881c1b201e0083c04d0219070345805280c81020b801c8004040039410001c400070b0b0454054501c0300c1c482c08c0c0c0007000454500403032800380104507641d0304020a281603801c0c2c50381206090380610740211110002a981c601410448280800c907548050400c0c0081e05902e00000d005007030141072000f143c040b81104da0b5040d10401d0701189008020841c910b4a281800d410301d8541c1200c0c031624108020005070342c803044284c0d0007460f40e529000c1010400c1818003401e5114103540840002010a400002c40c1e80001d84101121203c1e00e0704e428070f035000e505a409085111000a0040e00118002c110191203504800e80111800b10010340d17031140007882c2c002517440100140c0250700070b0a0394105200141042c19406404249214986000030780016104d1046494000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 967063974 1250 967062724 967062737
    0x3140102030c1c0b0d06020705010606092d0e0408071b03030c0f15150e090f0a141203180c0a0b040b13030507091e0e061501120f050106090803090a06 66
    0x954119844d00700902d105400f40008802041c9410301c007002c1e5100076408e448960800c0380014007580300350301c1601102c045954610310001030300f4001d5540c0818a00c003040750b0130040340104444000c3d48040340250b115850ba169540c0903441c1190941544c26403440d030440310b1000800c040b07900035100303024581d80895407040140a925080442c01400820340401a01c2e0142254240501003000810341d00001010307500741c0d48141c0300300c0d650300d444121400260000b041e070170002101c0a0711040c031050000c05640c00d40c0022402d071406900700301c40d1b01400d0410b000c03a0058980d41884944440202910b24a40e098202003040c4094031586c803809080f1000002c0b0b000701003201294600c0607560141c10764101c2550380f14030380c000e040035450f110119103041564212030901c074820901d25601d90300103010303142c2c1e8103120a0350300c549048010f03050081c24103084860600e18801d20141c134407501e07000a065410701c10001d00042003500450065442008020150781e10f080c2c200b41210500d14001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 967065224 1250 967063974 967064017
    0x5070210060b1218010c030b0102100b06091009121a0609070c12020a080c0703050606190e060d02030307061d0318040207030207080a05010501061b02010f0c0203210403140102030c 79
    0x80381021130074010510305520b0240d0794400c156054001c0024031109a007181c011070250fa5004089406441c00c4642c005e034108890f0005040c141005c040b40c101c103003481e0501039622007480304140b008820440f0705400007032960000040e1a081c40741c10100969000e4020b1401040291071145001030160142039066140d10500e403080000c001400d0340282d000d40c5841d01620103541e1a4a40d010845460040d40000f581078100342100100051250b40c00007509441d00f041440c4584000e0700350b5402800c017070320010150728104003c003405486547c00140c0000783d424210700c20311300252954402c0d00200b010007485006d0743c500c5500c0d510100c0300140c4d41d4400340340c141c0c0361143c142e00030b00003030040b45085810302c00c0c19400f9070304940c46030726180710308030300c00901d10101444810000d02044c08500001d013101d1003081008d01041c401360495003100d2895040c611030715541d17442c21031800d8000405100f0000403d4060b030b0714080080080d81142803000003030b1271a0043c0061030842810bc203412 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 967066474 1250 967065224 967065241
    0xf01061b0c120b0a050a09050d110a0b040b0604060b09010e1e0a23040912030f06080f0705031203042325030624170106150305070210060b12 62
    0x4200428000c8020b0191880b180b0308030304800070450700044107a00c4c4c000007581c20241c80c09804143c40c0d1203170141a05540038002561903240ba010410400c1c07041c010b0105c0004d00d500030b103502071802000d0003200751078007408020070f403903040c1c202020f506003d00c000c20f10360760014072040a00408554007100c50700d0343c2e8003030180101026003c540c84100300d0710004075052500500300452401c1241c003044541c0d40b406010903a0320b5141c00810241e00001d1701d901540c829403109800c02005000032607895507d00c0b81c6403810a2002d209080d03500a06170810030751404101c5c12010000240c20907007140f4154a03049ca000749501c4407400d0b282680c0e113500310649811302c503030344076802490f2003410140c44100c00c140c04a05580000c4803031519181c2400514240c0c5182d03c00a480e46010240e211400c0030302c1e410b142c80d50907a10344150341d05d4074000314014081e80f0114081e81e540d5a000101c2c0c1c580108000c0c0f5041c0418031140c07401303140a109110f151b40d16400c03100a078070362401442443d180c4212 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 967067724 1250 967066474 967066493
    0x2d02090a020a02010f05180708030a080a050604090212010203010f0501031404020f011b030c03120519230c3004080a12140405060711072603070b010504050f01061b 72
    0xc4c842610b10b00410090006680c01302007000902487c1242c00303050711169507560742d11620b9103681c042509480014000c0e8a50b401c660381c40714010b030003c030b403201c02a80800e2020365200d000450a0b50088014010140d010050500a00c004d1900344031084c145801c4080000c80500041c0c0a0034062004d00d481740d0203044031b0b00d0083c02c00710001218860a0800415144003000c089000440f00c82d510400c1c07102c90301030b050250700711442c004c9030561886413500003802412541007146991001050070759152000e11441400c58008c080d56614009402e0000c014217907600e0880891000005008841e40500059026900201c0e031541c0b140408810358040c0300b51440d441450f420811441c8480038138076082c0340070b54414001c0f10411f0300c071410299040200307150510403640c01000d00308220303190138040040d100b00c03c51400040001c02e001c0c403400c6910080040c0c40580807080100f2150034188285580580926044051941030020081000365000d0030b004040002c185800103002d4040c6 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 967068974 1250 967067724 967067741
    0xc0602070303020403020603090303040302010f020307080f06010e04230601110d0e15031303031103071403060a1d0103050f06060d0f020f130e071e06120b0402072d02090a020a0201 79
    0x3480c2c7d680301d10340190160741e25442110101c00550804c1ca030303d6071f01030007070003921300071121500c44461540d41c3c4412052030410040019042204107040d4042030785880c442c0700e465040c000001456038034218503500032b000010b085241000510810381d501e010010030480d01c4500c00e0b00d0811140444000014110204d0400710a84424004140000faa801c580088501c83c0b2070707101409002241040304082d4002180c1c0c04000c542c3e0020a103004021401c02181e1041c0b0080200200c5a2501c03000e0043d89420360440c00da5509800052040c010b00b00a42040007000d10b00408c510300d003a101007205040719590080c00d103156400c04100b19a03070700c6004010410054079404e01c00c10001014030103065022181e40c00d42c09620f002042200c402e04200c4014140503401644a0303180c114110740d0211080a548429035407113110403120341c0c0b580020b09801d4000d04000c1c1e1107045074281f0003c0c41c4401d6000605040050140d0350058a580c04401d511031016800140c0720000c0400503409821040b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 967070224 1250 967068974 967068979
    0x5030903071208061c080f070201020f060106030507080c040b0f0313050109150f0e1c0512100302151e0a030902030303040f0c0602060f0c130302131d0a02010c060207030302040302 79
    0xd41141030741c207a12444051103944105c0750750002030407130b003240e8280405013400944040000c210b9610444150f40040070ba291062048071812440d200c05103050400c280c0180c00003d1315002401907003584400b0142d040382242455030329052501a21803600e1080c0800520400c03404000aa80300500d1948010255040f40c000d110030502072400700301109050351b10218842c41d000401481560920132902c540d05450000c1c04075204034110055040075600d20b283c01c01404001080440c8010352029009880d4032401500c02400e502c108095860800440c1c00ca01009004071303210313a9034a6121303404a400603032401d0758a5200c0300084002c0c02c1c0c030082c0070750944000070a100800c1340540c5010300b9a401200d914900765141c0c2c0e0101c0e103400c826108144500e07101030110b10858a0300004102c64201101040041c2e0340d030350702049030340802c5010304544a503100a22406004101c414150034240000501010a11580040d01640d5038803009410a0f60110300d90382050300032b6040f1806103400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 967071474 1250 967070224 967070243
    0x6020c0616020d03111e0d020a0203062707140f06090108040308091c020604060f0c120b0a0e040809090a0c090303180b0f1e3a0e010218150a0503090307 67
    0x40348070a0141c007103086c1c0300705141c861104001c0c4501d1021840250702036000300501260349130994151500e0b000203001030607010088507080c01c3c41c00108003200003030800c560401d00240e003810400c0529601400c1c5c05001d00d40801410748240e0780030803100c0d405540b505000131241c0300c1658980c501000b000f6281181c031042c144070090f0640014003580700e6442100b01b071080c059460507420a64148262800c00700c1c148181021925145420403020001c01030510f501d40d5a8400962070030782410780c0c0c181d5818800140301c07555400c0004c0e071160704c0204c940c03003800684401d100061580c403280c0b00c00707810020307024040c200988000325071000400050481c030b52070f0302d05a03041c49401e90140d21003d14003000784d054804044040d006607015031040408801040803018602240c0344090021050102200c854144000c84540300304c1c413844050310001601c558407108a000c001c50342c10b50309841a001c400e964540c01c0b2150341290b034990070900c0c2c16900c0303860b01135026185001d03190009045c00d90 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 967072724 1250 967071474 967071493
    0x4030c06020c0114010519061202131d13030e1c0203120a0f02070e011a09090403030213080f0d0e0a08030d090c050415060e062206020c0616020d0311 66
    0xc1504410130640c0004c0c00180240d03640e800b00700da401710303011441410900c50401000401e0266420003c840c05d02d08015141c0034160042c5c4214003003036040b44419207044041801e8606441c0300300e9520860460742c110080f001030303c01400100d2081120351181c0f00e006002203171880800b4040018130f9003d0215000c400310f20301c0d585025040185488001125040b9000400e032000134510f0071162040340f0006141d007014141004441d0841c0b610705e504000300b203001a0f5454054050b80728034042c1e0740050b01c55545c81d44101803000140e00c41d14840d4004603008070080070109412400d03000f1800d0603240050014049000b0b0030890b4440b00c00c502000c07034001c0d0302c5901350300144103142c0b01d20107410500d511041004111501c9261000881c210200f040c0981401200c0010740c0040080c060390400c009500f80711039401100d03c801843c0da00c50030307080080710f8040000000c0f01c48101d450b641030502d003058442c280d5030580c070040e01c6160b81860030340500d8000d6021035100b900c3c40050322500d0301d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 967073974 1250 967072724 967072747
    0x3080f03010303020624060d0608060a15050f0906040b1206070f030f050c0909071e1d030105011a09040f050903130602241f080a1205031e04030c0602 66
    0xc00910094015004503000180106903042246000f84021032064805500440a201c45034021280c06000c1da5500e92000c18000000c0103401e200e10700c030250200d00200b59410490f08010b00d644894012604078080981c6903480d038049a50000f025a0001851516840000c0c1c048820070450300e00e0b4010441030003a403a91121540400c50401d44080c8883e13000b1510711401c81e0303002c0b03038400309940b002d0184000d03070300d000d00000750030442078540701c2e07210340400c0000c1440c02040c00ba110081102c0c00c104203503a080d840401044410120000c00c8958503090104aa050714060300b4000c0000c00945040155501e41c490500707150400003c000c2c903d8030010582c1d82e90300103400d43c00c201800d208001103041c070002c0c08a820104441d0a03000410240c00541200750000d014940c00c02001031354808000540003a80008124500003410b145400303040c5640c0e441d160814440c104501002042003858400a141c961100304040044055031681070071a540641e13074200901d4a4000910245807a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 967075224 1250 967073974 967073977
    0x7170301031a010b070308100801050c0703090b091c081306030509060603010506010e040c0c14031b03070519030c140714010507020a0e0621030a08070c15110403080f 73
    0x300d214040c0d119610500b00c2d00d507240400c0911402d0200001007101d5400244117989260304024102c0f2120b842544030340d40b29080d03400c1180c08074083c040105401c000d0590101204005021903184c1c2443d10300380781c020a01074100e451a140d50f00300a62031310820011564100c613520110240322001440c1c9414000f005028180d03440d0b80c0621495001c1a0b142c6010303c074850040c0c00584070000c3c100005020301c03001d0f1041c24540401d104440d2107110109481020b841312824419000d103580303012244002d81c81100140705c0d00c0c5c481d4000d00000c00010320000b60f482d0380d2024844007807c00001c6180458401c520961f00500c4078441d282c00400542c8002240010703100421030900080a00400455041c001d501d00030754040190f110402070280c40e911078a03004440900070007822400c250344146c1d500c51480c85070840d507000003a00c030500756120180750740054040c81c000c01c074042e46403035804e4134a01c8408261102d950300c2000400304041c503000c0301c0003140e00558907a110380081354405003e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 967076474 1250 967075224 967075229
    0x7062f0d110c01120e030f040e04032d200d021e0d05180d140a060b09361603060b010306080304140d02060403200103050712050a0207170301 62
    0x45608000764035804440840e440102c0ca0040c0c2d1800d1000c813100745080b018059040080c0c071503010030810418000000740051014011201191006040038900103000361050319040312030080ca164540b404421013005608120000d02c1c02c00134020407000030740c0070b02e4000c1017503242c58403450111610481d004035540660300c3c6a840710020418201d07c0c05511203070201c1403900007030401c00030000311001c40d034503907100c9500180c50515010070a0307480c02600901003405240070792049034440200011801260f8001e64180d500e0b00746c03030030404014080240307840c107260b0490307410440040c50b00b041884d224a081d415101201c551006800050180c40b00300c0c081610300701d040011052481d4005d00030a0220b4224a0045240c2450101001003807004051200c1d0710032055609a130159403008094000746028103041d446d1f84008190702a100c41d15203030581d040c03504100070841002d40200b003c910001c0600404941e50760303601c0c0720700c000f071150b01401815455504080c440900318000514107 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 967077724 1250 967076474 967076477
    0x40804120f0b10050105040306110f0a171617070311030c120109060b091c020405010f060305070c0302060601111c03200f090d0305071709040c0903020307062f0d 71
    0x115520f4800b03180340400100d001c1d240c0441c1d000c11080000030600da00001e008903070b4112490070030030f001c041c5202507800b1840310800a901c01c51900401400d103080c07680c0007a8000d016203040b916140014103129003c181b560041d51559000036a0580039401c010446210008400d60740e19000080c403250381c001d20302d82170010f243c520001c00c2c1c48082d031040e103090710707441e0b40c2945c02c1407040000c0041020608400090400c0402840702c012b17120380c01028040c1540c02002034105080003001000c94100800d40020081c0034003aa03000700e5008602103401110030320f0802d08031607000240d2454040c01100308280200050386841c001c41c0d0543c4140e16150307e01c022240111040040b0f040e15000e192030000d40c840d0200718545041c038182d1018a10071f8401e0902c9130070a40c0c41c1d100c1d0580010f5803416406140c0c800960503100c1d02e098460300b1142c080d84e08040c040503082da000f00c0ea460030300c1d000e410180400c0f142d0b400c01000d00d0060103445114048404c04182441c011881d880d412501000750 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 967078974 1250 967077724 967077743
    0x60e151602010e061312120501142b06020307030e12030106030e030307080a0f27021309080909040201031e091e1509030e04060303030515030114070503040804120f 72
    0x600d90011072414002c180301c85e05905203140076212005403680f680d00302814040e1091061699540a000f03003802008030304280e41001005074140b00c18581454581d11400c1400c00929400080e40403030440310340e8011400681301e90780c6500a40060980e40c4001c41c0d103100f07a800310a5800c1d4140001d5050b030b07420f907505200a101466026940c0e0000760780b840046052080000e140e07002d26071050301500c0b40044007084090791034119a030303510040980d40c0d1f454050f0003104015824070003102c03402000203242c1001050a642c403504034900403240460f1103010004046010b5a01c02d030043c0901d1800720841004280c460a40754000300074142040b5200c04001c90307183c00b05c03041d0960140340c040d0000402c0b1908249146004010191064100e0a001b4003850815042d1074a1040700e026504c02d40340003405042c41640c6081c0303984025003181c420b03030410307203815218003213001e01c15003012090a105442c3d88603442e1250b00c40c00350740c1002e40e07000f5208510500b40080901c00c6540386001d0312040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 967080224 1250 967078974 967078991
    0xe010b030c09071b0804171c050901030203060432011509050d03020708010e030414030106140d0f0f150b09060307180623120c010903060e15160201 65
    0x96180c84503061aaa0301c1992400007840e60f42c064240003541c940b461142c5030f6001c45a0783d404c0440d4009800c0042e00c012920342020000404005031a8280c08400007183c00b0103442800038240d10070240110704264000c804100342d0f8469030047c0321489064032136000441007212501c15500380040070140101c0400000042c0d5009130080b1202c100c680e691004081d506007014005120400002282107215245000804207028410210b042c0c1c1c003034026540d11441d0101c00c00c0c0c0d5000706034000b8403a0345008001c104540348106d0800101001f615124901c409500349208016442c0d00f0103480d48000d504e0703c90801441452041c108580c0340c104100389100342e400d101d06c000c003c0303684d40d070540e2103040103100a500003058050350310407020000c500180c9403d0301e540040805102010885c40c90f025042c490720380120103120582218005007880c0040c000000d102001520018001990b189103041a01d0f005000f0320344510059900c060803410011100d4584200754207a41c40154a03002e42e8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 967081474 1250 967080224 967080229
    0x40903051e0a0c0209090c100908070b09030706030b1504060c03080a090f15020f3403020c0f271b0406050913090c030b040204050c091e041107060e010b 67
    0x1598035500365992103802103201c13507080c00025200645000f9440c480c4010340c01d150303901c941d050f15420306940d4400d20754528000b40c482c81c0041c9600301600717402050040b666540c40004109084a1003480c021695006400c04903559414100074000786480000d000b181e10744c0c10100c88250141f0a0ba500340f03e5580768100c000072a150718600030400d56003000d50307402145500c0010180c5540000c001494482080d251403501e80c031100790034200300c14210071404034070b50715082c0a00660346854803104400940c1d0700292180d1081d90102d2003140039040140c141d0b00e46ea41c03c1c41d803c02d21442540a404030142c41200c032440c0072100c006007441c010072144800c81c01d040075101286c00e2512142d01b00f458200c00c00101421002050503410303690b1054201189a5490080085014040764180c038201401804281d030001403d03030301d5512302000b103612180c9842085401d0385014140320b900c1009820002800307003007c290000140c0c44003041582c140061a8402d0f1903030000744000b00b00132180c1409 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 967082724 1250 967081474 967081477
    0xc060c032406040b0d0b04060b0903060412180b130b040b0f030414010612030e0f0d020121050a0b030f070b0f0d02040b04090231050d11040903051e 65
    0x150706944041100a44259600e000d40d4036019180080c4800c2c141601c44265581d59000b514401e10100c0d00d0343c21030507007402c151096402a000316082d0528287c80030012a5641d040600010280c920758940c10729a140f1909100c81072413607003041201da07103a0ba44500b00c0b154100d00c8182104004409001801a00000441d8100ca061200250410b484100241100d400c020006da03103401026011031601c281c01c0c810800542203066540e440b054103400e00400303038001804141e01484e41c1d0340c00119a55034001c0b15050041e42403800002c010505c5400c0c911002090a0ba20303043c074140030600c074120304250004481000150116210112001e08140c0e40c2d000501c01d09102e840100011101000c3c414000c06107a80c110034054500756440c003261031350383d0141c7d20501036a030307011550000d414500f0040001d01d00140e0506103621809074100f4a12426910400340300300982c6410b0810001c0c6480030507400800280104510102401d014281d176021809910100003880034150100c6201c40 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 967083974 1250 967082724 967082731
    0x206091e21010e06071413080f0d0221121909030f020d08151018270504050d030f060e010b0d060e01080322031203140c04030b2a0304080c060c03 64
    0x1510342d00c02d400415040c414940c0083c00082c08007c2840780483c0c4a14200060054800b00400030040c003c4004070007424454000c0e00c1400f48401c1c80c600242c044903202c2a40c4100c106229003000540f02d0803080d64091100e0070400e010f45c0d04205440083c1350300640a100000d0590b020341d81400700501c812544664110350b003100ca0325611076445d207107003030a00c20b034004e0000750700f420100c038560752400d11989412903000351180c80000e085018596036400c9211251640e01e00c041c415030074255102e58607100280d0900041542c0c81244107540182ca4101030020030110442501e603503156140c070034042d484182c03601c0d0301c241007000c000f0760f41001412a904035240c000c09541001c8168103e648052010b01c565100780c02c08040200104608018402000000380c600142007800500125401c0d1001415500b21600510080003c51020404654488800904032501c0d510280346d01441260100300700104a20100400c01002514001820003080101c22104070b41c1c5c5480c4c00b2034040c8000c5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 967085224 1250 967083974 967083977
    0x10c0201020c0304031403040f2d0501020d08040204060f030b0f070207060c030e04060b0f071203060501020c0411070f14010f1a1002010b030f280206091e21010e0607 73
    0x104810008240e1b030440000c600304009055070f241903607072560306800000c6500b0031030012121030340e10000500d400b11150082001c42034a044a14034020010b911019200150020b0203204c500080841d650740d444000901519425404c006450307007090710000200321564640f111001021440b42400054410b0494419540b101a00001030303500300c5003955032030707040741d006a01d5100106442142c44040c0c002c4622a8006c9500c0d1000342c24402e00121100046605240c070780070041c040303a42c1c00f244004600380143c4012520310321400f1005901d200b140c802808103c0c50501c1c0f1020020009104001501d15000070b2090b9107a00307070b080c411180000409240c01d241008202401c1c00d15014003103404416000018071a000b010100c0e050841c035248007010364220f5425440c00d40050a03511010000115030040181d80380c1d400b0403120311a07400d1940c440c451080800c2801d0900910b0790682c8000908481d841001002110a02c01020f00c0042c4042d401e00d410601e040800140c460701c54401c5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 967086330 1106 967085224 967085227
    0xa02070306060b073305150f190902070317040614091204181404030f0f020f0a0f080f0a091d04050a02120f1603060e07060c02090c0412060608010c0201020c03 70
    0xa42c05a124141d840c1140c40c8070710302c2c81c9950042c0c2b1522440142d480c1286d043c255070220315070f529400790745030500c2004100000c40d041050f24a441e0b03034550541e80c495a004a0303d800004403844080c02040c402003205030040c1300d01e0b16030b032054000005140e507441301e200702d251070040700d0907000b040200c65178100e8140e20208410b40d5101a10184c03e030405008070440d103e01c2c0803400034021594403c00301c030510801404686203800400041030340c540c8880005800c403803017446020188240300601c41c049446035000188207541c410043c1a5440480e4200407503c0400c10000d1414407800300e0500380408200030820114074020503c940287c03840c60203109803842e800b00303407140d5003180404000d46500b02240160706641103070f100069039074140350551640903a60029801d8410002420113000241e0f02245c00c2d070f000c40e4000e004040c9425006d03402c1c3c0c410a0144080c1d03500 = true := by decide +kernel

theorem cover : BRFrame.Cov 966906474 967086330 := by
  have h0 := BRFrame.cov_init 966906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 966906474 ≤ n) (h2 : n < 967086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
