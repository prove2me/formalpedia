-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2523
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:57:51.701278+00:00
-- url     : https://prove2.me/submissions/d9263ea9-68d5-4c16-8bcc-7da5d7c92435

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 453597122 ≤ n < 453776978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 453598372 1250 453597122 453597143
    0x703060308070255080703032001020f0d180b010303030509030d090c0501080c0703020c06131701050a0b18040b0604090f1428170c19121e0503090a 65
    0x205245520f5444050740a02c50390780c1841c1d44e042c00e42d9011091050400b6540501030420109120340450025030b40551641c05c81c0c2100c11451500f0390b00000c00c4480320031000101035046091740e21800750081905d8a5840507000c442e250000d218105104c09014103856100149c050f03901030088170301000c520007041109140c2410b0403940003109024a60101d4004400325042c1c0004909070b804040d4140c1c02044614030010a0280d1a0010448420501c185040219401d460342e0b400d00c1c00382201c07100000d00d52030002c0508040d9880c0310a003902034100c481d0300c01081c40c2154000b90707101d0b4010341800c0d0b0301d03254000400c00038082c00c44050091751001c02030804001000642d0076000c50810211003610304116040c0c8a10245001c10703011900181c10500c001601040000ca40700c03600001441c10400c103260310230b0500c18006180350038020f000005c0f004011688121405920080c42c0940c10642038485070042c22600210010a221000c00000e100100c104041012640e121010b8003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 453599622 1250 453598372 453598459
    0x10c030c110a09060305070f0503030313060b0f06030702060f1501022a04020f0a020d020712110301060e07030902120613030c050c18070e0405070e131503120807030603080702 77
    0x31f4a0700c400c0e000c0c015420201d880b000039245400002e803809007441720040c6005407010343e0352400030400f0003105030300054907200c0c00c416a40e41002852103520540c000d04601d00d0070021600d40d10320b00030700614901c0c5030a0b824007c16640000c82400c0c2410340110010030500807002c41058408007169190303c5800014140c088440b100017030000702241c0d40880741c81c0c0c129101c040e6103450480c00f800c00d11204500500000c035591142181080801400001d0a9070b103d0074040d0325544200c9107540440e4840800c0421401c18241d502c00c1c9074201e4010782150700b401100c3c01903c8201d941c014003044000443d4202340003080c4413041c03880200422444101141c002c03003810340c000440d240d0010036104024400e080c186030103028801c00140d0b60b0742034440802000c00c450300ca41d102c0381d00a42079403240101d5107007401d92007100266001d9160100c200d41c001900805004004201800f01802c00c0405c0000418200c01e90b070445504a070103603520030f02032049822070f01108030310011300080c0c0200314 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 453600872 1250 453599622 453599633
    0x305010c03020c070608090d0806122b18050f060c010204030623060a0513090203060408120c0f031302040e06070e0a0f050102030306090a06030218070e010c030c110a090603 76
    0x14030f208850141602c1139582c2d9940e0a80b140341c1d0071203207900650455245003040030310030240e42c1e0380b0840003403c1c0040b484071911000c1c0341c0340780c42046401000401c095060002e581a5031242620005d282007880c0c4003008035020740411507032207858003440101451200540d541f400b61040450b40340c0086494030750381d0034100083d00c0c80140a1026510240b06080c195841015807481000040c194040451401c0c0c2809a083c1540c1016a2010f5031344101c8401a03800303018040c0201e0007030440b641c50b01406041d14019290140144260352002c03c81c0d003001503480400d580c0d10070f07000ca01500109840c1d002060251040008468160183c03404200340030380c100c0c07405d4100c080b068500031000f548503030740450f01529602421340960700c05d100064051404101c1aa4450318a000125070280d4035400301d43c9000c14004400c40c0041d0000800c0b55969000360304410b00e02007480c044143c0c1503103850152598003a8035028154001340d1400404984994000400030085280c04000319592414034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 453602122 1250 453600872 453600877
    0x610050402070302100b31050a0209030307110604090c0206040b090303090d21290906010e04110706060806092b050c070513020408010e0706090b160204050c0904050603150c0c070305010c0302 84
    0x843e921f1480e100214050039024800e5031701c10200500214a080035544407441c1039440c991049900c00800c00010405940c01c5c010850b2544184d00104a241094500456090300c010441a00b5610034820040701e03a00020b4003114454850402031007514510140700d1800000d0b1340c1071010181408250b01d801002504147e40c5081803804c03007007078200c1c282e00700513407001c040e9292030000c1c01052001d8074034030f000d900040442010307010051410711155581429500b280e80182c5583d0807000030000917240500481d021441011080d161500302c0001501126170116a0f132020814040b82041d6000c00030404171000d040300500005c81d164034841090040d60190180b4140355003001100030070500c0c0000c02e003003564070030b4603421141d074180211a16140c20000c0303100403a204c0084580e026071900d11880c1c0c01200c5107031003241c3d214036080c24801590301c082c042c2c134042c2c2c0c8124080c001200b404943c05401400207941565200180c080c2d091800005400c003038180d5103051850009950550300 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 453603372 1250 453602122 453602209
    0x307050304140916050f0a051b071a030919030302070c080d02010e01020405060403032a0b0121051f060f0f08010507050f0d09080f0c0610050402070302100b 69
    0x40f441c0c159502c0d0301c0d02d0f4144001421014021038014401c04454680740805400d004030a032611504200910505080c0d03032940110100081c1c0008005118002402c4150382c444d2044603001481c50a080100e140c1d19a0101d007410214041400c101007010300c280c044070310b101e03004a50041c0494071012420303140e4503440c5400e070240d881c0c40060070303410006000b0354045403401484c2c1414a850f50703d00756200744094051440e00842182c2c1c0e14080303a00803165451150149110300f24035030400b07011070200c0340003507050820f010703140001e2000660001030b16203030b001404c100110b02a50781c000400252009030083d0010264800c0042416403000410301c0071503103c000288055140d114040c0d801e803023500b00c00300c015042001b040e01c0c00071384c5070003240d4803034450058540350a1504032500d0664204030103c03580c4ea0410400d0205d54840001c400e4007801c01102c2c214909200382c1e5000e5500c1c4949400c0e0085141c9560420500da03507511903203134068202d4085a180c40c5c0c00503103100210302c039188 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 453604622 1250 453603372 453603379
    0x60507020c120d0815060c060a05070909090f03140c030412020a0608010305031204170a0302090103060801062105190f05190f0b061203130521070e09030705030414 72
    0xc1e600441900014a070f4a00c00c4113455811068581000011081d81c40c0c80029800140802241490800400c026480303400078680c001200d003070088008101d500c05500100080d030038a0034990110f55500413241340642e2606208002e2500103041101901480d80010b8241c08081000035906480c41303c8100460b208440701030502d41c6030081a074000d4000c1c0000390041c1e02c1407080040c8010040704d4a50058060010320b190000d2011411495038082c008180001c0d8003c980c1d40444c0d6018040c41d03000e020003d0080c4036042c104035600100c1682c00226480110b5005c074881d06010080c469121407860100030003e00b4401c41c10f03c903a00b44c4074280e08a61600c2001e21001e1070003403498181204950042003000c0e6804e40351202c511403500038240b9035000d683e008501f9a4460200014511403c1064581d07984d5460007082210500d45903a911400c0d030030880d26815880350115604041d0b03a298000000151645580c05c2d140d4000d00034014140d100c00240407a84c0224a0403408403603408a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 453605872 1250 453604622 453604639
    0x30703060914090705010c1406130203100e0c130212040804030512030f070324080714150f03101706040b090d0804060c020a0b0f070206070207080304031e060507020c 73
    0x703502c211120b0007180c010b21190440201441290b100e00f00c00c00f81c0354040c0c000c1c1420264001040d030305000e82900c1841e9002c000f04014411802c0c14490010079844d01d090030070074845003140c010b4941c5007141060784158040050b007042d80341e0307907419a105518001e06603091303440c19191180c0c030f0b0750090005407524030070016590960a6031000f22842603110580e400d42980701d518040e0003600724a6960b41042c1d00c1c6e480000e203580c900c004010000c0c8003003001005135a10b0301720b825610001d83c4903403c2c010280034900e05103510091080711201400480c00d50f03669074510601032143c2420fa0402100e400b0104c0d0b03401c191010001c0c041d40650301a180803080c07901c4811f102a914415821400c0c0400e10a0700040e010a01d50352118001040c240182c40100c00140e803109038051044550380040041c8509000c0d945604220956001d1003174001800d10300e083c4120f066036405540b00050100644600e0218840311141c42c0284541c3d00a50910980c102000081d407240b410404450084898 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 453607122 1250 453605872 453605891
    0x140d081306020727110f07030807031b0512180f0d030b0105090d020f010908010c0c050705090903190e060d050a240909060b0603070f0e0102062214030307030609 71
    0x1400c1c166502880b942c4c01c60b031403000040004006845100b2000021082c180034500c85103074170b080140780007886680c45040e0780ca840d000c06003c440d21032072200d00c4020b10900030000d0b250044d04817052031621990070b4030950390346110909070349003288910300c16028070302643e41c503ea000a401041da0240b5202130047c40700c0300700110350500a4461a684c0049080202d401500f80f1140890b00c9040600d025500940c0780c840e00703400d4030507041a81000540724400f41040c81014440d030000b030002169240c5603400c1c08818140c0d80d01544072005a00084066020905030058410b00491a000381217030391a83d031903d551070000d00088607180303000e0303040c00c04541c40c400351021070000280404034003d850a042848030340c000d01d50300c20301302c903d15507030107022501d40c0d60000914401c0c0c0c280d40e01d225800c80241c030001c181c0d40c491034444e410f5512120500c00541d4042c6804070f14422840540002c01003581040c0e540e6a000725290241408004140075035554581c2000090301d1427030009000d0740e5403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 453608372 1250 453607122 453607139
    0x301090c03051009021e030709050909010605090609091513031b0215070507050901030b1e04031b030c020d03020f0d0509060421050d02011406040c09140d0813060207 73
    0x1124403079030703810740c0c1c05003401507032056400f80c0446d01e5071090305081742030720f0360740706c001540242c891002003042c5235010810703441c081c00748642c8002e052000740805071400c1d001c14031240e00604a548194804400519005401c00042c00044500403503030310241444100240c5c1044002d00503800280050800740030b04441800096601d42e002c0c20303210a00d004100400026005804100e80798000d11000144641e80c040303540b8040c42c06154400300f5800c1c8102484000461036010b600e449500408001c0840d40100810303096404440f210380c8204110301d411a0282110320b0020b41c0294105e10b44002d143d03000640d1a5a85006404c545100401c1e0130141c0341405404070b860b41c490001c11084c046e900500303100c84c2c0c00c0400c001a103803048405680d01404d10350400c04c0100141c3d1b6683c03070002c2002c400e4101d42d40150058608104882e40a18028818080c600403039010b1a000306c10804039884641150211942000350b07183c0b1a04401c1060041c48180c0c45200010702c52054081600340 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 453609622 1250 453608372 453608381
    0x702040506100206010e0a140907060318110607030507050105100503070803070831030b0709060813170c0d0e0a0504050705030a090516090b090f0c04270905030301090c03 75
    0xc880c1c00416040e860f05580542ca07401c001d000d041a0f94172406e82301c1525410300c03080342c000c0c15104041c10881d030401000030205d407903542c41001f5190a0140035000b007040400d1b00c010115080d41d10355501e01c6103003001c1d94140b00d00c0300004c102d50310300000c01024140c0d01080f4030941c2c07411401d0301c03400740d511089103070351b4001d030003002c3d0889000b001070304214007500d00441080d4071540841290001004100c1c5407034642c030b603c140c400b111135804010302da80d8004007000103050903003405200ca00f403001a82248500100c00185a20002c0d44060300350b916080c02c1e83c4130b031008001103400c2d40c011444c00800007150702d10003d0058550140200d003506e01741c0191803240d5840d50300e2509680da0b00da20070000e010300103010b440d02d005805c440402c0310082640e034009096200701c08580a01031105004410900900f003c8a0340a1341e0180000004070004690440710940b07040f400100d01140088503103240c412038048001d00d800d00150400a010000e54126030079180d00300b040c00c1441c0000d60030f84 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 453610872 1250 453609622 453609649
    0x31806030f06080d0e240f0403050d08100605030901110310050307091116080f3415090314160b0901020301060f2d05131a07060b13050106050702040506 67
    0x40c900c054044d62402c20507040b46c280034002c001c43c07001d10031110002c610703640500b02d050f9500c000042e09105002d000c000700ca41c10101c030319080340e040c075248041c2e001883c001d0190030304000000001c01e5040e54250000e03000981100e510300d5890508003030300d40c40c9407010700c1039600902840b8800904c002d0603100700b4450000003140d01e45080402503440410121141044440e82810301a4018612031100a04524004d15107007001020940940d01403c4082200e02d89402d25154103801c0000d1550001821002040d0400b1541000500c0c0542c0d140b4012400e1040c0c146010840306440681814001c030503900404418080b0f403118803803a4241c3c40240110004950151a8650a0b0744101d50b91109543e080c50107030401c440340c8002141042a940b1316400081020805100014000e4103400c024100c1490390782c41c200030106440b0707540c0a40180902501ea4460000002c2c0d00d4010131081070f04080a4100107e43c0c540c0c0c3d001c0c10036000260240d000354a0240015064104080700321900b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 453612122 1250 453610872 453610877
    0x103060605120c0306130c02010b0f09060d060e0309040908030406110c0705102604020a0f030c14150304060501140406050105030420040903080f07020622031806030f06080d 76
    0x2075984181c0d40740c3d5540050140d0360046448044043d00504030310500c00b0030310180d800880c000468504015a03501c881609521450406050214941d50703100a14141584010302003500c8112020103030950203200302280c1c009007450204c030100044c5d10019403080d0300c80c0c80200b140c41c06800000d0214010480214041d07881400103005c5ca103000c2c1c2d082c40f10309107546001007060940c04842c2c0e2806080c1c901d05ea03401d99000e4240800c510b0690249809000481c44c0c00e8800c6181d07440e144620300f007501c20440d07212450814420982c031662002c0ba01200800d11483e582d00b014030b0a640104000d2190b001d80310380306088100146030034010b50003110300581d22141180c80e03645030107080400648072040120010340c2c0b142c0042d203030f50040c102224042c1d11024118506034180d03000c0000001d010350115000341c4204a0310181303c001030300c624030780603070b10000d218030a16007078901401000e00f0701040042030300c0000701160b241c0c209041203105000f00b8010710381e454150f256070720b204220b501d01 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 453613372 1250 453612122 453612157
    0xa1e170715053403030506030d02100b0303041d1503010b0a03030302130306051512030307021e0f070f15090e060f1804061508071203141306020c0103060605 69
    0xa007440b074009802948001c80c54400480041e009905490303002c030602d0440701e80203003e04010b150f054841c2540c482401d8028180b4101700d100001e443e0344804c0d005241d4242d952010400d00d407410025100980b1111400380c030a901d444e0b2481855030002c0b5080c80890751842014549410103008040c5015400350801c1029415603030203030007a40040e10a903411100183c40000425102d0080c58050106078080b402c0344c0390054140101180c030048040b000c0c0e0f00403c14068101c2e4000361411001c61020801090b104141864a041500003a0104a030380300d080004290404c030f01002c80c0c00c50709a000083c4007080020400e5400c442c01d0b1060002e440400000103615040600c9144002200200310300002602c0421400054000792026109140d48182c08001d48100b03820001c0034240900082c0006403a124180113150030802d0011b080100c1071402d10050b6400300700f03841c084034820580d002e125403030f5a0029581c40d9210b40450000f41000000298503003c3c4c0102c4040e001e0a03440c1e4603 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 453614622 1250 453613372 453613409
    0x20106090c0809120c060103140a0f0b07030609060807030b0705072a080d020c01180506070c050a0b0403120315030209040b24090105060901090b1c06050f060a08060a1e1707 76
    0x10105007001c001d105010303406005d400a209100c41c40180360cc210405d041c58100000003c2c1159001e8002c002482c0c40e14030244400748000603840102c2340c3c0900800d14a0303540c94001c80d52405800c100030207040c4002c5500009050000c2c00328032403000c4420010280e583c0c0c0654a540d4088410307114003507000035090044551244100301a80204d86500051269030358010412503071108805903170341010003005201e0b07840c000820b64001c01341100740c40d04060540d00e842040d0380415202a051540c0c40410030314001800c1c811000954004007680654945414828110b100442d580403010040558200c0e08401c020603a02c0ba0f05005400d0701156820803040c0a61688001402810b010015a000418440c41801440c4444c42c08003188144100d000106069400a42100b440780c0c801c0c4105c1025625068160344194902d4074010559460b40004190100c42c1d54101c03508420022121168407120411326004480340e05441d042811074590400c0e0f00e03110315008100c2d64074031410055 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 453615872 1250 453614622 453614633
    0x60f011205220c090b0102010204030803160905150915030106020a02060c16081c0318030e04090606060f090e010803040b0a0504051e040b04200a020106090c0809120c060103 76
    0xd502031450021071686000901002d10604460482200c1d1888030000a01404413180140e20400001303000039803d10f400e55960150900004081480c0c0e02c441840d49943c0340d10619003c002814080c002403000283c60b04256969400781000d0360141c030300b03607c0b032221082807441140c1c120340c442c1d0302910000c9200c0e0708101e042d900856aa60f164410a104420054107682138040104150b9006141084442c541000800c0c1e242000e4000d041c42d201e54030100c001300380d1010040540c0f501d0b18101000e1038030001802003c4a00c0e016100510701000802c0710350700300d0940c940f0710909440d2142803595030810034a000409005091050700184810000300401030003902001c03080d420a039080c15115004114143c0d071040000781101404426810142041d12030324100c40c2c01600c01303100c032440031031000d010349400c0382401000c1100000d20342e0015200b948444060310391071105002103003506000422000090b195855680100460b02048003112000c0300d880b032401d040a4104d40e861910750 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 453617122 1250 453615872 453615881
    0x51311010c0807060e0610060302041401030513060501080318062508071b0303030509010c02060105011103130924031104050a06080d02060a050705160605070c0206030f0103020108060f0112 83
    0x44605401c1840fa220001e0f80a000e00e01500c84000010011450101781a5040d86103541c0030300249881004144074400602c40c2082005100382404038440c0c0b13030030300404002c0007243c1d0041c210501c4c0100220342100d01000901111306894440c0002208200c10007856210304034040c1c804000403070207181c0c0c64090b00c0c01900050300a100080c10603195880d01e60070034481c2c0004500012000400b07104050b00741c4150380d0044807980013003003072503020100690740d52410f01855062004040100c1d811020400031114200c00140200c1292545c6903800383c0035011048021078440440120844d248040d8500f5030105c982000803d516644810180401050040e1160900c25119940840d0100c0208100704181149500510281ca00482340100b11a005031064081140800080e001454112800b240c095080300e00080d198403084070030f40e100040c0c104001d402440c0801000700c800000c14605040324000e88460200d40d072080100010724070b000d0581404522a0b54242d0f00070303040b0754007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 453618372 1250 453617122 453617147
    0xb040506250801091113060e040f05060108181f051e0f010b07170408030d0629130503060c270904150e01111b0a03050f16060f09050105131101 63
    0x140b0302d1030300141c48502c0b241071b0a140c0106010600625003180d9900f0141f0031301e13100144490b0308002c1410f158000820282000e01841039800132080b64000000e01030000f5140402030305208003a420000203900050a001ca40c5240200203042c03403079412002d4081c60b01e114801644510300f4903030030086d12841a170419082a9640a45011070041d001203407802040513190400c000c580302c0d0145407148040d500d080c0c11155901110b4080392514092070b2800152915114111940b02d04051b200d41c004800d440d4056603152042030280001d00003000700800307030204110031400402d0826482d1018516440303165a401804e540f001802042c400d00e12a0300c10036101b1404500130103088201801e503800441c1000e181840050266034605494510280117000d04004c3d1906010725100500319004201a01d224540d00054180c980310070400d040c3e02c6594898002c01214a100072007100030110094222003a620748004960689511000000302c3d552011840070780b81144001114500003103007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 453619622 1250 453618372 453618401
    0x60c031b031e0e03013905040603020f0903011406010f030606140a050d050c1801170a050417030403030203041202010b1e01170f040302150c0a030c0c0b04050625080109 74
    0x2c4443c035564081c003c654101c80c504580810010b04c030003440b40c580e1400721200c0303418000d10160f1407160780c0040c1554111415130400684401802c189084144126031304540d242d4a070032806011180c5482207640079410a0f03883c2d1040e42d50110095007220002c0c00340c24003048420007081e03205082a8024040004a032500741e0400400140c4c0000b03682050f1108a05070402185900420b501c103601912042d8091038607030341b10034002070440015000603001e4000c4640307641c00241880041004044045400403007269285040e0400400a42040d5412103207500c40c5108504591700c1400340000740000106410505a10510300e0400c10b500c0c1207510b0705000c03245980c0c1050b40568503c882c840c54141070140011329183c500281016aa40b200c0d0407030040610502241d01d40d00400d640b00400b05060001c3e200c14480000c0d0747d4180c44100040c80c1d509110200700403c003001c2a25400345a050300481f1001009a004019009502010200094400004010100c0d06800501c1c10f0355480 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 453620872 1250 453619622 453619637
    0x3220f2a140423011a0a0e0405060d120201020702040b01030b060306010c0525033815060c0a0b07080c120a020d141614090409110a060c031b031e 64
    0x200f05641d030403804012250744030245100100000c1040003408960120450001894640800c8001d810048048640750080395100005501521003446000d5a9900502007541c14020014028042d6100e000304038065030500040000a50080c0030b4020f540400a10316402c48c2d840da0011070744900e0400301a42e2501c0362003403403030a809140c201ca0680c42c2e050003505555606505202d400c0d500d05850007402c1000b0a019040300c001c4a01280c82900c1c204080c2c46c10b0707500c0c0c0c3e000c100ca078100451000f5602007400201415842800558500c45c0c07803081c660440569925401503c50030022180b521025008001d102500260b49a803940d10060901c0014100000f02e902e8001b103030240e0401d400c10851450620034641c200c9042200034021030300d03000091244003040c030780d010b00a50060500564560464108005442e80b03030180c0c00401401c0042d00e0703035a402008100c1210414103a01050740e142e202110f0069529072000c0403601a15800c24040c90a40401c4264a074940e083e010444507 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 453622122 1250 453620872 453620891
    0x3020f040f0c05090315091c0e06030c040e18030f0c0717060f09030702010207030f020d0f050304150215010501110307060614011d1503220f2a1404 65
    0x40b031045944034201540d590303480d010820241484c1860641006020024807001c0108400d80028940c644411142c00c1c200d003181c0b442e2090710010160a01c0380c0e0302c0038010080002c02100a03003d84101d681e4880c1c4600f01c4d8940f149080d681c54210f00395407016400411500310311100130001050600903c40403500100d64078282c0458680ca0b030004040c103034000d48103004440006034841900010030102540c604421a0f00207581c0d81c3d107601c401401c00f40743c1c204520035940c0b9141500a0290003840b4041100c0091410540307a910502550f020819103040404400f0f200140c0880340c08481c4003d08c40b6a42004015520381c3d0700c1c180018614401000b85800252690189000403c00360f181811312000e00000508003049004400f003014003110a00c9046940b0aa909000d0300301c0c2d010708543d0394490b2035205844802240c0840201201c8070b00400811262041c031804160003142580084c286403011401020b503110001c280380098048180020001182c0d10506403400900004483c0c18 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 453623372 1250 453622122 453622151
    0x405040c030822090c0822020d0303020d0e010606020115030f110a08030c010504121407030806012609160f060e19080a020f010207180b2107060e180103020f04 70
    0x21541c20420284d6101c07080d00c151250040d0203076420814103d45100500a281031080341242c038000040c0c1310f0701321081030400f03040c001c2c0c0c1280d009500802040c03000408035804a1301a00039840303403000661800d1100c00c804240c0b1444039040e80c2c1c0c0f00034100d0201348651290010001c103c01c0e004d9004164400c00038080004200070500001004004621481c0604084041800000001050001c03840c4da002c0c062181c10201c3c1c8206034181481c0d5130540f03902004032881d1918481c0c2e000700c01c201e001c030384050f25103c2c0c00c0588214030185c00c4071540e80ca000d43d13058072601180300388001183d580405028890040a400088020280ca101464a0043c0c00000341c102c450f070003c0f116802c0b804031501075003040c2552190002c020300081601500c0d0941000503030340d8a51004e4800c95584220a00540ea1207a070a01031040004807601c0c4c10b4012a002c81c0c440c4640c0c407401c00404e100940300b8a1a007071505100b54408014816000076070710b075800f8806542c2100008503806644c94800114805 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 453624622 1250 453623372 453623437
    0xb03250506071a1005060d360b0105030d23070b040804030201030f0b0f120c030607020d080106030608190812090c01030c05070c0620030d050a06050405040c0308 71
    0x307020b50f015402c1110320526040035601e01802008181880c02c1c0300f0b000315112002100d0102a400d10005619039200740752000480e14510a120424421105a900c04c440c01121400c80d03030241801032202d90340d80c4205a52881441684008100c08a80d1000740b94200201d02d45041c220100213840d0404590320107022007c01c45040b241d00304041402d100350359240c458503900202c480d4080107480c04401c0000c21064100340100c0c4503024a1289825a80091059071440400602184d8140c1060040a034564200c0f08003407002505603400099101e100340034440c1203a440901034100e084c00d4040c81d0203d07542c2d542054a00b40000c2041404986e500c5074214803806152016104002842c1c0004040e145070038801405c2142c01e022a401083c41820a0700031662241070070031207030114180301c038044004801c2284040c00302240c000c1c411030403500241d120700900c85081040c0307910f910401080700c0d0207030740160511803030340c01c14030002d044240104002b507070a0031002c1040405951640170003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 453625872 1250 453624622 453624637
    0x403030c090e1303081621200309010b090f0a05060a0b0d0f050a0b090f1b0d0519061d0c1b0a20060a0f0504050901270b03250506 57
    0x43e1000000030181580140020b401103140f0486900403d52810014200d030b80c1d0060041c0500c1c130b440c8281e100107006034021584803801d401d10300124001910440c0700c64008441c104002d5082000d04401403510104807889a0440414141c5035200ca00080008080040080350421004500030950810110103003801483d080c4001c5081c2c0e071061070303000585d04d0107480e458126080507070b01540d580d914180c0daa8407500b20f10308101c5a07540e000c203100c4041c80200380200b0400b00011450403048068200601c1101010702c212131203824880607400301c03402845500d84d40403001d07210f505010246102290442420741c001414441c0da46200b18208103080700d01002c50380070301410010001c0c1c01ca0306040c9800320207601c519207101700c001f0420b18490005104100020b04540030b410b20700403001c3d01c014040c0580703c08480d40e12800441400c00c0800b010160040d61030302d000c40440c0b101e005545c4140701c007501401e000240c031803042c03000c0014004412104c1000340004601600c4040c040d0000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 453627122 1250 453625872 453625891
    0x120905130903200d180e090d1e0e0f0f04050a020a0e1c0f0f1a01090e1b0f01020a140c1302090306010b07050c090a0b13140403030c090e 60
    0x419500e0724014060221115034010210105404034050300d4000c50a801000780c54280440300100c0380c104458000d840c6d8212003038840c050b4007400710780d9a000881c2e55006c1f16544440110f40314041e80200d500700184050000202003084411482c00d180103143c48425001d06044425060000007500f13541d411598140c1555012601101b040c3c2c2c442c041005083e01903030480504103110b4084005158002d40107420102e11032540c5040190040c40e001b031942d0400303040d42d0500e0101540d41c018403c2803141100d4903080420b00f08040c0001b080c0840700440e00c9071181030b18540c00c1c2c1402040200c011113241503000b041040c13400b003188550a41c9100b4825009007413200060030410600e1b08a20119201440c4103220b0306040340c5000410342d0640d884d4000c187c0c1c40301c02e28a0316915007c45132448680203d103190501c4650038058000500c007110440b213460884a009000504a4080d0b5006942c2c00503814040f50200703009501210506079140f4118010548540f1b5091a420064481025 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 453628372 1250 453627122 453627131
    0xf04180210020607030b090402060a180803071b05010e0904020f04390908030d09021302180109051203030c03040503070f080c0106140d060c09120b040b0f0f0412090513 74
    0x441a40346c03040d045200022100c0402d03504140d004100365004040304841401b00d1101c1020700c8804074401000102094801c5942d1002d00c0d00d80707410200f0314607601c0c83d07020807071000c00f01d6550f0240c0301c502c1590f903001e050713840c580d40d41780c08009200e0450800640c111340da6404c071402a02c21884482c94089102da480c142410f04601109001104010f4507010002c1c0700d04240000d00c0003004548030349850601c0822564010300004000b03000d41418600c96030310004001c541800403c0e40c60f00104c800341c030b803042c1d02d13503039501844156402c19054010640042000071038120b041400383d60001d01507000c403410b1103042e680300511881490015601983c0106003003142c030000f401140c1c003920314552200d603c45030a00106403a19070100005000545804400c0d0507548a441680010003115590418514050401c90707684802a64162000c100c0c0030009035182032080740c4036000300410310201c091980c0d42d0307c1e415480c11204043c2000c001d02c42d10001096555000703188402d500000b80040c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 453629622 1250 453628372 453628381
    0x4180501090507051009090c1205010801050f181005040f0b040b0f0604020901080105010e03100609150f14090a1416081003080d0f1119020709050103020f041802100206 74
    0x1031900ca43d6600981c07180c0001400e01c3c000d640c1c8001c1903021900310140c0411100c820000a03140041c80282d906003480c0382800000d00441d05401c41c900403c10b540c080c0010fa140c000b080d0301040c0001c10115000e500a40d01c0900c01803680c1d0060754803038010305020300000400c0c0d40e20782c6221415034081e142c0344108402c2c4103104030101c1903160002c104980452410a074800040d101d004140701e4241448403070580311199803001e004000c4015440201004060713110b40b500340c000c00801030400361031145400007080780f0052209660030b07242c909980da0981a6600100b04491500501da0004035440e220b07405150b030b0301c0c0044079004800b01040c503559000341840040c5024401010700f88a44400d04003000880d00380d800303c0b140103ca03400e01040000c000c01c2c411010309141001031424910008071079000c0c000040c810038581c007441d0309984110360350308135840070740301e0a0002035404034005450b15198a40340d4407000300030034140b0904031100345903000180c18049080700140541c22080410 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 453630872 1250 453629622 453629633
    0x50601050310142715010609060804050c040902060c0a03020c0f030d12051f0e06180f13020103110a03051005010516060921050406030f0509030d09020418050109 71
    0x41074050040c0c0b4100540d601c00c0c150340b039201d800504452a0043c0880b84107040c0c0401107203909500c40c450049504084044220104180c2c0034810b00c00040c964041c0402c03080d1182145030301650304a802481d021003041d0402c00106051740301280d008000f0008032580b02d4045c8405001c1ea8040d070041c191071200d540911000c0c0b140c501c0964030079001030624607ca590010324019681c00704a40018899450740c01d242058581082202808040e61000099110350410268480c003002e441020600380e2003c800c00c6c90740703002d8640c11464120300000600d0003200b100a1041c0e5401417601180103642d40001030003a80c8229a5400000d40700e00400075080a000200c20041100386401490480c44010080340d0007844d5000915250701d0300c0c3e12a060140e550310446100e4010341001003012104034024211340e11605c0741402090074143d040c07004c17218a01c02c00c0d1081000d0006140f030f010300903400c41f0041c80300c030300d08a0b4070941da6450500c00c102c02c40100c9401c5441800000b500803c0390402 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 453632122 1250 453630872 453630883
    0x9070810090b100f12061403010c0201060806041221020a110f03160206070501060e10090c0509090a1b0c0b09070b04030b0a020906070f1a09030417010b0d0506010503 73
    0x66a5254104410300040d0b450f00b103e1207846030050310708420300c810341c0b040031900350b07034250815001a4145403020540f1901c4081d0f1803030348102207000300541c541c50001603090f1074080c4107154180d003000c0c00041c041003426410101446e017900e41080c0101910300404400c000300c07140c3c1e080059000c2540ca45d410340200e0810329030301d107000003465586400b0015566074030500d1038501803031500b0001d080441d100c02041d102c42c0e941c4070009000c0b560300d50b01d4808081108036034010050002c9000094880301622a80f200d2030400c1d51250b03d84052042031040c005800b40849144035500c0f14000170482c01c0086c0c1c445440103c2c2c0e1071440d84c00e158140480c1d01c20000d8411030303058010080400a28841c541258101d9a004280701c4440d174031a40c46138000c1c0207a0150a411100008850b402c014201c4090035546100309520b01c03045480c0c00d81098206011100d04a182e44200428450040c2d50143c507030360518520000705044183c980411082d0014003001c80d103641c0700710018171480c50309128 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 453633372 1250 453632122 453632129
    0x20609010905030a0c0809041803080114060301141201050106110708120702150c15161704110d02030717070b18091e0f060405010519030b0c04030209070810 69
    0x9002101041d00c44075200e00c0b42130710010904c20306001e88410014100203940b007031a40140100a4400311098480f07400e1070802c1c040b00020409000822210740c6843d0740c9400b004064425425130303003032032501c0720b840c0c1d0324103415684110b0f070038a0020102001d0046034041d011542c0d5122241c0c11800303219251154030b40101095400841a82040320990819a4070b140d030122620074021503000c0490b20144666a403a2204d802551403481d0460f030041c80c030b140140c1a006241c40d08000340402207908403401004040c021011202080203d079101c01814a082001403103004821b0301680000d10f041e016502842900d42810302e074068461091200314000d10715840c8062401c0d035400a20100714070b031100114030800608010641217201d1505101050300d8114003a9564108101040384585d021a6013134812400d010010846c0c0c280305242c0c034409909504014007450455840c101c001c1001001219140c80034032000025030f07030f48402c0502130f0030b160b01c50500030706052000200c00b185540 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 453634622 1250 453633372 453633391
    0x30909050601030b0d0b071e0c050c060901120b03010b040603140f06092e1806111c0902030309090c030901060f060f1d0a0617010911040509040f0b04030801060206 72
    0x60700c040d40e90700e5461071801401d902c60700202050f40c03101e1b010f5034023070b04100c580c0d2001c0e40044c1d0100c03c4150041410000340b0302a00c02c554185403c5010041680f0801101600140400704251110392903a00300b81c00020740100046404180c26000c50f0499600b98425502529a0268207000680a00040c02c03110b05040107005180741480c0785581da9540c5c401045810003445840d0905403107605000840840107034818003000b0f141c11000940d070360031a0380542e02207250140c01d0403109a0700c03003201c2c21a10305208100704c20003801c5003e170081100d11020f0360907020821148a0310b566211035903104003d00d21409440e810039040060031285190020808031009440610249811440c4540d80b0071507480c00800900e01c1003502e50240109940241e000f08480c8008901d0603080194a41203285a00c92000c1aa0b40c690482094402e0031404100012080009200d681041101d0a5105000c0c543c0112803d0700f981d10b20003101d00803682940007610700c400500440d641800a15000031410 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 453635872 1250 453634622 453634631
    0x105190501050405071e0905041b0f08091f11040605190807021e3901030b06180123211005040c11010e0706230306060d0e060403090905060103 63
    0x100001b070001c0520490080e110003a800301140d50703900ca5090b600141802600500545003074040204010310402107410100311a05020f51900740300700d01091050100c1d80c01040304030580c001e02c604034821110181410358940d92640743c1c24456000400081907241e64a50f5905d03801403200040d0b03003d12130442c0411040009001a680d800180080d043d004e0b1442510158808a0a540b4042d022100000c15400c241c4078010030284141d1101400c48229801800f14900c0340011400c0b0381042101c00d0740300030140107d40c3c03160700c6201642c03501181818407804549540d070740c100802c201e054015019034000030341200404c0390500c41040641640158140710300b4034184488140d01c050140038019a0b075001103140d0070381305007030280b98151844020400200702840d4551510075030300926010400080c4a50411800a610280c41001104d87d00c2d0942d202e900805c407060344510030500e4074540b81c0502080c1e000382444158003441c130940303516130901e10300701425069a4004041c91305040c42d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 453637122 1250 453635872 453635881
    0x3110303070c05190e040b060907020a0b180111070c03110105040b03041401020f130302031501180b011e051201050f1014070804030317091605010806010309050105190501050405 78
    0x2954880d090f03440407202d02c4c101d0070114031191a07a40450780441c602250b040180410b000703404442a024030421b80c0e0342080d6075030b15602aa5201005800200010340b4480014954111001c4107800408010b0000c2540f007542c041c44041500b0400b030580e0342d04030a0030108100051006164aa58000c1c201142800e2401001c10150b010062002d008604c01040004041c082903044074150074400000303988030000c0007011002600c007401b08078044c1c4103c0c5500340303c0080780c0c40200d048640560305a00703001c2c548145500502803225006060081d034091806405540000c2c039030511a150b52419260501c2444040d08180306030f1003540201c000c500044070544030ba00c2c5840c11450030781070025001400d1503401c4124455440b000c1c028000104021007010362101d400300000c10400035075041a125885003a80368040350800c2910417441c07800411255002d00c52099100d207050600080703101d9682c60740750a54030f080300c440c2c0c2080c0f4034014415409155100355805004261001c02c003600c0d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 453638372 1250 453637122 453637133
    0x2112070215061011030f09040b0307260f070e0702010c0e1509030c060301140a08010c050a0c0515040b01211106160606090204170309012709150311030307 68
    0x1020306100c0c0a207400110803c0998000c180100551040d0720490b5a070740e0810340681d0b540e421403050030f8800da080001c8003400f4600090340c4000d0302d2003580d000d002240c1a6900c031022001c012891140c500612a421805200c18082200244204640402c10f03280ca880700034219034840000809100a003054242c0c2d546074203520410300c0c3e80c416040c96450184400092400f010409080c0d4070100000010920b9a25445202c2d00024140c51040c42036848000c610700b680c86060326a0002202886003001c02881400000446c1e401501503d918200f040da07221802c40089038280d42c549440b0004103d000000c1002e5010701d10010110708050015a0300c0c02e646146500d25148910070100700d5584800709105070081c0c4c0340d4003080410a0540e41e01e94103001c3c2d0010302c42c50350301c020421008240d1000c0030003211a441d805940343c00c4a02c01e070341742c00350706107200d504c05555100364414082000e040d1440740c82e4400299001441c0001c2c0385142c044007054480c80300c58001e070001e1000d50300080 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 453639622 1250 453638372 453638413
    0x102313050c0613050306041a090601060c06021605010504030e0102120a0210020a0509030a03080a110c0c01140903030c160611070b07020102100507031a0f010c031121120702 76
    0x80c42141c2c2640e803403d2105403148440466042035070302d405144180400c0045c2e01e683c3c074144003980c4010341459518180d009840d00000d100c0c3d040800c080040724070000ba0143d00801088850640114030000c2c1e50f10f030182115030072641280441c1c40c2510300c1305150b0b010401d0503030826240c1c900a243c00c1e0030680094403031444d880160440303500451048800c500031010f0f54a040360190440c0e4114156040017030500c00241d40d1921840c5c40c144c0c18400c5102000f040302c81404001d0b0040405081c2000116090f51307984a4000300d000c0140300011466a082c40148040c51546000342a584805064201001000d03404030302400403107014101801c0002c01c080701120221091103444030002c4c00142d040840003c0c006816231710340003c2100d8180c040c1d001120400000246c3c4540200b480203101c2e00d8034410740e0721404180c0030074a40000030b01c00c0303c1e6404040d0b000f400b030740c4103a0b40c50b0901031480a402a101100e00d00081240b04c807031504069500c0d40541d503032006100c00c41907e2165145403 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 453640872 1250 453639622 453639643
    0x6150607030513080d0203120c03041e0c030c0f030515042f0a030c090b0a0302030c10051207030203010302030d0207030b070509040e06010e010f0e040809040e10231305 74
    0x40045506a2140854207080e0014801c000c1981c141580d4148001d4688e44114941c2c4190308102c0c0c0031505809034881a28440e81d40a45c294010b00300b4000c041c3c10001802108603100040d03031038048009615a0507042c0203103450500c2c2800c060449c82e01d141428590f81e810110401504100804070303800715014902c000082144d903081c41c03500c01c0800942d000314202d181e00328002500c00030402c440780780107204a44a61301c0c00c20603600e5031030030040440442c1c44060751680c841241040746181100104c40b120b065802e0035450500024280b0703144500403264180400e0b40032004005509084c81900c0c111540d0388042e216050541d030751003021442c060900c0c0d00f0000c0200341c10f08170323854507402070150000010468445603543c5545011881d4240580e58056198a10005d43d03610301c8003d940c0181e501800060400742d03000240001403081d084e6095192298003100e241c0c026440c0f01d107603400d014040003201500d00001c04064114009001240c0da4580c540100b0049100815811240b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 453642122 1250 453640872 453640877
    0x2090103020d0312020a050304020103050f1009050718080102040303300c050f030f0907150206130206040e0c12010b041d070908070807080f0304061b0f060614030615060703 76
    0x58049003000ca440390b002c11302c40c400f254030001d45601c00c0c80e04200614840d40c800d9030300380026654004020300704001580c8101129590035000d101001c100d81107560320800a02c1c112103003187c2c2d4040750a030540b00c2e80c02031109960000c5c0c02e0003495480599049034540c8030071040380e403001d80381e110100c5c54072074008804499a0f4181c082040c40c03003202142da00740c0c0c442000c0b42e224106280b686940d82000d80b41c2d90080c1c441c102e00050094072180c2c0c407600c000c805801600362503444128040c60840444c8080b45e00040402c404a00221080d626900a9803155022074940116000d403003c1b546c4181c00503215003d061004010303400540e1030000441039240d40c2c403021a1031b031240a481c1591940c00c00140d134010944081501c40c00000e8080894000704129400030b900050032940700d204030302a92000404103a6203444041d014034a0a464030311641402e0102c1d0a5070b2101c1040f1030307160300f00d1f03d02d00640300d00351138a41c40c040210b180c010042c107559001800c0c494000800794415820300509 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 453643372 1250 453642122 453642139
    0x40b03060303070b090105072a02012001021b010b03070f05060a0c0c080309040f140718080d051801090605030714040b0f2a0a0807140106062a0209010302 68
    0x40c55202882034603100703680a1289040c030704204960b00d0107030400703d6047c0001104801c001c000e03c0d1043d000e1030100e45000742c40805680d2640c00450300b86031b002c40d0f101c0c0414094649224180303c244000d2103c05020090013002813841403202d0301b510200d00340306101e58040c440a001d16000302c02d07075074203d0f0012942d840e99a84008410f07240c036101c586002d00391010050000035480b00100c0107180005085804010154113907065004480c402842d00907111031460005805c21700510888034036070282e504141c482d9a0b1540840c0c90811b000e02c11100044002c200081000d50b0700c0303856000801e090034601c11050400310000c00a00006090f0b40030484685036096003805610111006440c03000e10b42903a403200d00c1c2c0c500340654001840480140001c001c0002e0402200f440e1300144a041d001810100200d9140d086c02900000780644c0e1030f580300d421003002c55400348903240090040f40c6071f03081a041100c00c0c01c03801414080720380c20043c1460032030b42c005a803000c14582c1500e604070351011 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 453644622 1250 453643372 453643381
    0x908071205150a09060903020d1211030a0c0219120e0607120305070509120a11061201050105030411120f06011403331816140d240609050106080705040b03 68
    0x40138150750100540410b00d00f607410703014181e000c15801000382c07541c5c039401903004c8150111002c803031a80c070b056401ca82043c804503686010903005000c4c40c190b584119501500e81803021184d44011802c100c80360a0680319203402c49400c60070001e000d0703d0448285003011400e45544c64100054001c2100b0581d0750000a0121030207041580c41848000d400e903203290445642a0f583c540528100307a07116012500c3d43c050074a010400c448004072003404d0403c41d40d00c2c100042d030b42508060700c100d99a14030031130a41c2003501c4908031021400290001403000c1e542d00300c03025003403402c10b07042001c01c203113040803569590b00c0010700503400f5021a556008000d42d9645080030002c0c803800e944100d01115030078000b50103000d003c40e5240e00402d41c1540e041c001d5403120206030801c0c0d441072040038044000302d84840c0c036203800c00c007c074075005003400c150703c10600701411540040c07101003028007999820140806200742c81610302425003400c0480c00d90610810161680c0124404d81d981d2000020014 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 453645872 1250 453644622 453644641
    0xd030c0206131701060503030a09060e04060512060a14060307030b06130213080f06010609030f02030a08043c050d03020f060a09031701030201050412060605030d090807120515 77
    0x3a218000e4490140c40c2d843c2d26400b228140b00c41d1410840c04030340c205103000c42c45d4600032003142c0c4003019a03104d20074002d1403e0070941c4c025002c1c020280c0e22507543e40740025180c80b000500781c03000f030191018040d00c5c070301102c200080310600855280141809410440c1d6030304c00182400a0701e400c400c01099940d1900001080c01c214141c02c5442c03580007056600c032800a0040040540e0361140640300d000740404005035403030409204601c00910403a0003080491460210340802c01e00280688054000d542c98040c0141e2165020000d62107603094a0450040200030b5403c00c8120340c0d00b16011a85510b00310008003c00c3d00130325220303103600302c000030406008000c0c0500d02443c0d00700790707000740c601040368400070071010700285c0c0806d1400e451512003210000d10300341620390503140e9905041c00c00d41c00e40b00c4407801d6601102c2458ae5203201050560701005a0280100c160340d603025100c0c01e204010b81401c0d0240d00040141c80c550f903000c000940045580500e1001141e944503403641c407284032 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 453647122 1250 453645872 453645877
    0x6050705030d020d05091504081c021b0d03060e01080a122c0405160c060f140112020a0f0305060a0203040c050d0c0f060504081005070309020a150905010c020d030c0206 74
    0x181040300c0d1000130140030702292074011912905034034055480d00c1c41860051082c06c80c0c00c441c001c10b890030402071200d085800c49800707200303016103047c01804d0140c0d015485405400114039030b802d95000503d4054495418001c0e1f2025102c00b98500c001d5502d81000241d490305035040c01042004118031251500344030b0b01e04401c54001e0500400041e13410003101c03560040c95404460300031070412001400241d01d01c0384204659440e6651050b50b048141c58100c024041c03842100d400703644801e1241404401518507902030f200782480300303801003064810006005050b84c4003d032540d4024408102160300410342607400185441f002da43c950303031881c02101c480d40680007150b00c04100c3c503c1d8030501c81d1a5000b00f040d10043d200c07010040c0d8407103d06490500071845100c2240d4050b02e1510130400440d00b0050308249079081c003180fa03240d60350000c1da0b5500940c1010003040060304810dda02e607449206a0010902800c181103400d2b030b29000f041605642242c040e0a20411000c1d08013192984002c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 453648372 1250 453647122 453647137
    0x50d03110607030c0e0d0f02090903190801210b0103060510050a0617061203070204150509071706060304170913020c010207050f2407020109061407020d08010b040605070503 76
    0x756001ca1408000240003800c42000101c0000d10803c102c210078201102c40c119001e07001243d2804c04907640c0d08028800c1d0000b41000b0842c0401e008282c80d10b49082030000310303c8807d40f18080c0c950706025121686847c2d4134404140c5d41361000881e00405c1030b06080c05c0c1565007094000c40c880d0303100707400e103290004903a0004ea0442d00c5800300103121039002108600c410100b6106138101d0326030b4420003a00b8034204102d03140d250002c1159400501d06a405181030f0901c10040c084802c0d030310400903400e14021101d0402103080f060100601c0c02070214813b900880c221040ca0031801e013030711365070404090f4081d92003002c000060020b0440d038950f00c01d61014202c022023503680311015207910303010b9042448119924030801c2030640101e1800310302c600c0010b041788080c2c0010000c010304080c8103440544848203556a58052101054043c010f080b0b821310311031250516400d061a00910305002042444c0420101c8001800001000c0c2c2c11101269140d151282c0c540c450b03800d04504501c200301 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 453649622 1250 453648372 453648407
    0xc0516050f03030f01030201032f0a0915050721200109052a12060a0207030c0c030503180108280b0607050c010e010206040506011e18270309050d03 65
    0x1080b801c1090742107264181c83c401c0e42c00f0702050f03440b24110ac26011011030f00440b4010b1101c034003880c1102c040c010b440150002d02d05225810b075078001510701811403409400020b00b00291100a0200001c004001901d03140041d45000815607002002c82010712a4000f8282161446c840361200940002d800d20390040e040d03810f914002081da108140d101c003041c0142c0d000c074140a00351450041c410300d1713040500202610407a0f49222103c8029404040704800348100200c801000c220b144010002551060000f5541c0707035112001450720110840900b41001205d608006c0181c00000170b1000103800a8503080c1c5090503000c456010300762484080e5000100420722505000001034100103000c020703224400001540001261078520454010f0310315803000d001000640c60781103024001c008050b1240e400c95481e401e80780035002c1da104002d689551a0026040500b2252a0031100d69a110b072411140305031a40d400380c0002c0c0c480c8a82031045540c40b42c1001458060301e1300680101d202e2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 453650872 1250 453649622 453649627
    0x5180112020d0213060e03150103020f03070b070624050315040510022a070506030103110103090f06020a0905030705030a06050c040504090803100603050c0f1606060f06080a0c0516050f03 82
    0x1013900c901008258854400080d4400440c07000504000c2528401c003116a0750020032a0300710740a00000925135600990984507410b00002c80dc0c0040c4094810203114003404a403442c120080108034580314040d021443d40d401100300160f03900041c0f00244071215203d8404c80d81d8171410128101541040f55261241c0009000c54208900b911050300e281d80441c4078011030620600741c15a503814a000d0b154019400f00010b1022072000c4103441c0e0314107014580801c61007040c3c2c2d0740e6410085403100c11250280c0200702650000d8001d2808000b0782800e8000344801ca2078000000d0392242484806402070f9030b903402180c08101104100c50103003001030014000704c007181c44c01c07011544c011581010000c19000c0c011407118880d0160300d008803013404225040c41d580010004d415440741c0404002400510800b40018146005682c01132454812806010346401400b602010300180305086161825024032001500001030390282031444085902c0240a494075074a13000020143d030850744800f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 453652122 1250 453650872 453650887
    0x1b030703180c060509130b03030406050c030d0c050903190213091e0803090f0105010609061b0614010801141317070c03120f020f0606060904060509090a03030c05180112020d02 77
    0x2000c000d18004000351b0b400064100c1d41d1440c142211040001594140c10810003044400d00c00ea0282c510f041c15001500c1c5007007004440d47d0100c42c0401c401d1404241e000c900da2513945814007520307001041821400110700410307030000d1844901c003400c20b40303021380d81c104850500c00d8150400710915030841c011072100e41036040c1351069420883e01103c061080c44c481c0b461243d418064035048030066110803182a05101003030700c500394101c8440d08501110340720315010600c18000c0000340c0b600300000101039410010407900751031516000400607040041408842035000c01c1c18042d05400c078030b0054203101170045022583c4102840605030250380f54010081c0400c010500050500700d407184280012108002d81c0c45150002c0000c446030050030000c0d0b0b041c200103006081d0a01c00600028059031114009940071800384c2d009034096004440f030b00c04040e01445884070203019420000d040041c2c408000d4031a10661300180e040040184000031045d00540544488000c42c1c00d042d07484010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 453653372 1250 453652122 453652127
    0x12060305031602121504020103020304060b091303030c0201060303120b01030e0f0f06071727010e031801051201030818060712020d05040602030d051806041a1b030703180c06 76
    0x100143d105130322001c0c20422240d4005401251180b48017070381c08080d5100e8005600a4100900c162045a1160b4050b080c1f5034480240324841c000d172130800b110084180c10001c00700d842c2c4080c0c050543e85044020f0001c650411158202011520303400300b401c0042e040106d02403e01d029000c0810310982d0590751050302c001c1114200a40341e6401c6035003a556080c4c040351800741c4415600b070341e44c2c12b003404110300710122003440c1346044081c3c1c0806150b10012249900315090180d00c10020b400118232808120740900c24603080345000d00e041405c00d480d0083c003040d118018400280f82c050009440480418140000842d601e030082005407940124101840c907080c04580c000c00500070540d1070100300c0c0c0a41c0580d0142c540360b900440c1882449000d00b40140405060840d000c0705088030f509120384204505841240b29040400700c02c201130500e000404405410201815541100c0c0c00c0c49150b00e10541754840c102d880c000c5100c80d000040c1c42801d80c2d190101400e00781903ca000318241e034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 453654622 1250 453653372 453653407
    0x18050f1c061e0f2a030603080307170a0c0905091308043b0a0b0a080d2003070b0c0306010c05010608010c1b050a080a090b0d06060e120d1206030503 65
    0x11911071003440f0326031810f1001d2003107503180c82014080401c02d0702c61118400052041c0003c0325454200000c0c425140d0300c3d98052a00708640d08800190603c3c03d01d20030900031400030350024900401445034000c4540c02501c00b02c0c00f409030034051004000001c0003c1a48800c51020700d4000803500d03511078a5202e007a81c50842d40110091403420b040103c8080f840f40c00c000420a4001e10640415840340070620002e030000c038204070f40c0012040700c04100c2080c203210060802d0103075210256508152120100328440010781c07095240c100303004140101c1c035072001c455403109030b850000756a99130300d1006aa80e061007220181c050761030401c000c10000c905500c180d5408085480b802001c1d0480b40e50340d044036a135064024296040308052070001403090014000208842c1442c0110b1501d6000380d00e495008108080349143c0c4500c02004025084016410401826103c0e034601811103440c035030756200c90340d00c010200980703d0952480440143d10040103580c0c4041500c0e03849003420800c45400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 453655872 1250 453654622 453654671
    0x603020109080d12050c0717180901060906080612010c0c0605130512031302060310060e0409080316030b0a0303020109140706020d050c0c0405010308070318050f1c06 73
    0x1404a2201003001c0c80c0c0021941040300742d59441c401900c0c1e4081084011700009030414500050920206000942640c401c540c04640078400c191656106580d0314040c800e44408640181c400c2e6005028007a440003880065844034200100e5079195500800c0c50404514203520070755290260000085030301c1005420340030f001d2401400251668075101030400d20310503005007a135001301540c80c0303200c50b1140038643c02a80a00102c00f8100350380c004c2004c40d030003100d64070018030781c02409002182c0c10080d000c2e048d5a054070300f00408286035a410409200c0580300c4003904880a640001030752003508000c928100c080e042c02c020320395914010b4041d105500f411a085109181010103200d00041c1c2c5204031740f41a07000b4021a50010400c0d01c250384542c402c01424040c08410300d106403514002e0b2402188038a201d20381d10070b114140244110f039214030b240101000e00e4410440e9076a81a00d8082584007140e0050043d055603038030580e201c0145034014112420040510b00c0c074a441e0080c126907 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 453657122 1250 453655872 453655877
    0xc140109030e010302090a1715011503060b09011b050a021e01110f1906020c011b031401060905220e0303060a0f03020604030b130f060b01090f08071e150306030201 72
    0xb80035a0040d0143d00070301d80015000131031001c0c1046254206030391100d181141c4000c0c1d40358104070b400340040600c8260840c450001c03803990010015607040c42244020a5013109035418050364a00007801c440841c0d16154111030100e0011045c0481401000c0d1041d90042c003030b040b0040144000e800c114141e070f0419010410380d20000d58000404114110026000c0010702003603103821000c1408a00415400d890355903090042c940264803d20600800d01205401200089541c0c400141601e0b2134070181241d190403a03004100302c9030442c4084050b1035040b900c1d0b400103006182644012410805070108503400c2c040800e00080c400310046010f8003041d00c2c0a1460b5441e401180030403086032100a404c02d4080004002281d007100700c40307410840a00380301940707405a88071040303047c00d280000d40300103580355860621580c0002c42d810003040b1144403400428502080a6200c01c110302c0384140508480300c00032402859405081c1c040c00c0d9910413402c9540c25507070014010080d0b800220b01 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 453658372 1250 453657122 453657137
    0x170f011a04080604080f040308120609070c020d110102030d06030f12020708101a0904060b0f040b0904020f010e100807090e2511010204030b0604060b0901140304030c14010903 77
    0x50020a990444050302d503480010421038846176904152030707001910042c20400240008400076001c0720041c55502c615448031012801e01104000b00303528044d0154090110450700540141c0b107000c00b80c00400d070481042074402440c680142d0841c403403020580b42c8580350000110811076116640030201d4000c1e041050303a450103500c16a6100311602461010f603000446074a00d6084a41001101016821076601c03280d6403a000300e14240d0f400e440c2226843c1e110b036141710071420b00000a84030040200c0301030201c1842d80303010454130300700540040d00444688146904590262400708400c02010b420011030701c513800700c01000341105030f40c160000382440600045000140c003085000b1044004240d1b8005240000d1904014003070741a1000d20003082c0141c13503504020302c0540002c1d40107100c404020b18006003003700b2608150000d1041c401c0034401c090090343d00c5152883c0103088203540d260b49840d07608054480561525005041c6c851050203440702240c19000495032a1203600e4066 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 453659622 1250 453658372 453658409
    0x60f070c081e0303130507051008180309130b040605091939120612060b0a060806010507080d1b0e040b090c0a0905030d050c07060801030819170f01 65
    0x300c00c101040b0158803564014004a180f17074100c0091040d030309104604858960307a649001c00d00c04001c0d01c40d0903010829820800024030704c03584500216400d00d00c044d40ca0703c86804006110380b50010f8404032420380e18145000f4030f0312160302600140c40c00910100711850060b01204210580680f41c81c00c1600388504607600c02d07a01d01d03014200f60112010000b80000c0c82c0e80c0312444815200b803c034200581c460f05249011403521030000504030005088943c0394150a00c0710030386101902c198044c2a00000802103541d01001c5103800800910b0040d40e61111707401c145400e400380103101800c851606614407140041c501000b9402165a21500203a400303650802088454800e455500130403107400050001e1902c400404c004507441c281107150588840110740b90240d50000c20000c01d8000602c01c0100f4010032004000385071629004400398156a0b8040242c024143d61040c01125004104140c9000343c03540c4207140721400c02c005c01031424030441c5500304c44c28131449103180f01c07900824 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 453660872 1250 453659622 453659653
    0x30c18100603060f050d0201170103050c03070806150d080f0f04090b040203090a02040f0f051603060e01080309100c1a010f06030e031206040b09090106080d030b1c02060f070c08 78
    0x380c1100d03c00813001c100c0c54036080a001348000040c1040741003001031003030381846050868080d80a140140001d050300d1104009041c0380003c642c00600c40c030390095040100d900c0410040c03803c03020301038030001c1c18100d640ca8200c1041c0554101039007102400b080484d40903c42c0c40c05001200d16210f0140300031120f11042c04101d2000b0303140840320b034109600c150050300f444e402422990584042c00640840b1449802e0f08403801500c440c02049081c40d00855402c0d0b0600642c030242c00985035410b80c5500d030200140ea64410205481e00079804811643c8516014030007821500c4e0b0810a188000d030070f03401240041c10006d00030203003620005000854100d201e80325410030064134038010b5240c0000102c05511010303008244076445610b03400f0302c901a80b10b00058a0049868070004154541030555036810900300c0600c8000300340c90095042510b40e900e80d41440340c14122440100d220586002048961050070080104c030000042c0310020030000224110440d4085400d9541d0506101da55 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 453662122 1250 453660872 453660881
    0x216030b040b0c0d06090603050f0c03070e0402060706060e063f010e070321031506050d0e0d11061605120a061a04090c0f020714030c18100603 63
    0x60402649800001c0004980808180e048514038901600b00324015060f0010b0b0754807608904d04451b02e4035010403c0080030004150300c9002030016000400844010030303554489e603c510303400188038102140554482d40d04545110360407031020304c212a00c8100043c6e2150042d00d000380203030403d81c19074030641c0c02c5040c4035449130303e0444d081c400c500e102d118205200300c0341c1c070280240b950b0b102e00c0190041000c0207000b0081d440385088014650100b91803140401020707410300b05060600038442071559a0002c200181c4000c0c1c00c1041d180e05078101c030600100b40c03d00c0e092070f20b07100755400c00e598642c0000c850320341c51151104032030f126503400b0b04495268a01d1618000891414082c15038084030481416602c40301029000444070b60301d80c030007201030301c0c0c8505003120b0000000301808214442d0103a40c0f00e81c5020309101c400c040030404002c1d50b507502c0340303d081004c60b002c87c0d44594596090081514800b00108443d003030a20280c502541c0003004d0f64a05680d8000f110000b0b80103009004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 453663372 1250 453662122 453662129
    0x50303071706300709050a200f03070f030b0901034d1f120c0e030a0201081806041202160303020d0804080d1a0915060412030504080307050606010216 66
    0x1034200d8500400c482c0a940c101c0d040e114076403d03000c2c02c5004215a10070b442240c2c030540d240701004c145540c04089407030400a140391140d00c0400f04010b040e0b0700308090320880c0d80218040c50001c1e981e03140000c02320010040ca0f200142d200060500000510031036507402c90040d03001c0f00c600410101003218a00020682000941040c204014120909001105021180403001c1d00083d100d41d070640c0c20710b00c0d00c1351201380b110100e00c0e0300f0184d10741c50b049072040803190411414050075214580000980d10341020760028100400100003d041c014180340d01c0121107005d0b01211168203007842c22020709004d0381c000000510500c40d0801050070514100401c40707405402030f200c040240c40c1c00b110304100041c000d40b8129410406860050500e01c03c0402001c1103400c104500c01d00c000c02c00204c5c0c240940051000e0011b08100081030359440120340c101e81052403000d201000d14175090315507001c1d03030f800013a03035000214050b810300501103000c0d0b01c501002d900f542c994007402c000c2031031035960601 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 453664622 1250 453663372 453663409
    0xc05160e070c0c171c020307051603050c130e01020a080613050609072601080a0c06080105061204020a0317030403031b080a021815071703131e050303071706 69
    0xd03000c00580d000032044d41250041c120076a10302c03441050302c036803901d41d4200e220401070b400060031009120b42440801c03512489100d042d40300900d1615602d42d17420340003008911030302034203440d02c20308039155103d4004410f10900035501c5904080016107541000c50b80180154410f40d4840000b0740c084c80307032502c80c40d0700810348540740c0c68908040322440028046404121100b10780c031240f602040700b400e40240f40c043c0042c0b1003c90700e0704e4000d40d2010594030000c140b083c00300c018441a17a400c3c0035240425500448d904a56949000040c00c050060340050007500c414004030b05039012030401140b00354042e07142400b0b00c00e0300c160030903801c8010160b20000255030b400815444140c0760002e050b0f0b800c44402240701c480405000400489082001203c004800110a81017200100315150b140c41e41f01300c2c15044d45000302c0300c08000c1503038140003404404800801d03d45c203004541080791140c0c005084980300e1400701c0b80980300000c0c58000900c078038a82c0c00042c0d0342e40b0380300342119a13030a0f10b039 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 453665872 1250 453664622 453664643
    0x6230a09171c1803030e0111091002100609020403022704060b2e09080f070303032304060b01091203120b0a08010e011410150f0c05160e070c 62
    0x7100001d4054100d50310820011030715044480501e9558010309241a0035412529801652860050100e0f8008041089182d040c40c01290484ea00d00301a034003c91340613680e01c03503400b280c000100c1c103000f50b02c2840c1d6026442c0c40c201190700001a800341c0b040c5c85c03095507203e00c0100c06500207914030f13000c1d03a284060110031800003800101150800d08144001030b00c1c80310034208003201381c484840820f201441005405420300107103030f40300340b000005040030070241004503186000592210042e00024007450385070009109080072031400c1c0b0004521951809401d82002d161040183c00c5407800540082c001c0d444c089803901d500c0c7d48102e102a81519a402ca6405105d011405014811600d03039105524010000d02034074203008100441c4160303000001c038441c005400140004029096042102801b4802d0140034080090f005030201603003040e18080700100030880313401c0c40382c050092080c0644040c28400c8500b020f243c40980c2d180d090143d9142d5101031045600300b0840718043c0076801d44 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 453667122 1250 453665872 453665903
    0xc060103021909021207030c09140d0302030903060405070501030f0203060d120207080a0506040b0106050a02060a0f06031205030915100b09040b0303072604230d06230a09 75
    0x11588034610308050809224510b540d46203203d0482e0840c1144002120703040003003041c1c80e0343c584906c10380000181888480103003080c980703000302c0d030103058030074010303080d00f400f03c42814000c0047d00c610000c01004c95440389480e14182c0d442e00341500c038035408a0b081141d00b00c400c0d046402548c0c81444c0140504015804648600840084121011065004031a030101d42c5580500c20a0a514050340090140742072501e4021041e100c140e02c04401c002051220203401980450311582200181001007000e07444000303107070001c00050f480140310344500c034039020b1250b400c100a18481d107981010b5a450011000704e03002030f12001c0f12103042401c0c00980c103119400b0140d0103421800d202500008504280d040405d00e140e00064082c0d61a8006180300c0e84540d41800d580c191788030802c4142c500b0304c0d00c1d140404440f10b00301e011140507490035a4a100c003a845041400038a60381120b02480f00710b0703085c49901c02900c0001c1d000340c8110700c2c140c005505151140a005b01d083e902c0341508144154 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 453668372 1250 453667122 453667129
    0xc120a0615121103100e010e0f04020d0c05030706030c0e030105060616030c0b010906080d02010b131107020a06110f030f12100f0315050a0b030c060a030905150117030c06010302 78
    0x7541d01d401d6119583d944840a44000003e01440c0300b010b0328000444079030b0801d0518909407505070f20140c00b502d0100c042040b0820084411900540d050301c95150a64507031030545030091603600034a400d48554a000034400d43d0641241580012540701d0484a002c030342c05040c2610421213226410490400207a080c4164200411109074000c0c0340080302e00050303a65200140c2c00a074003d603c019125002803194040500c0480e540309114002040310910740c3d0042010420120207004d8010740c1c90301090f00c182140d40c201e440b12a030007419845181d84400d009000d03041e4a9503001d6581c419058083c4000c0d900004881013280d0011001c0d090020203155086507250043c40700402e002032080014048111010510180d80704a0090000440d4982d12a04458004105e50b0909003840071452142e20040f41b02608003030f041d40d220740e85641d0400705501604110700001c10358404c80c0b0500d1103681c14600140c0c160746c0d0f15203400d0204a00d401c0c40d250380c0c0c0940c1c403820101e0341045004000519 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 453669622 1250 453668372 453668387
    0xb0a020a06050115081810060308040f050d0c14060f070c0f062303060f030703060b01030f02070b150301181a0109110427111b190809030102040e0c120a0615 69
    0x1000300003107c46c001c151940344401c0c1c400640c000c8500b50302c00308041c03110401d43c0c241203018201c01e8944101c5440b10b1303122180c8139801c40c807488800c03024100010040e61079078405c40705058401c0c00080d0307940c80580341c425500039043c4a07010488100b0400803072078a10503040306001d540e00c00110160060303003000484942d48050021980200c8142002c0300c15101440390304006d5009001c001121707010080090180c668201d03807082c0c601e00c10000180005d00c50550560094241148010f90400c55008039005107042c0c2c4280910280306041c120402503582c90080840040761000c8a803640e07500d174610280c41c24180c80c80b1618809110611141040403c0c4c1c035041c002c0010160385108680c0140700071541c0d20190000c1c0240005201303030f035410184903500107072501d04000702007403650107100c45a5116480001842d0310070004011000d1756094050b94094440c4168140d440e00303151082c65510341c001c1301d001d030700e02d1003450010b0040ba032607200308411a2040c480000048007441e10880301d88 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 453670872 1250 453669622 453669661
    0xc33220201051602100504031a0c120402040b091311180610090312090509100602100b01030912031d06091c02010915020a0207050904021302070c0b0a020a0605011508 73
    0xf00300d003400c600159682c4d4202089004068583d16682d50540c20700b021a616641105882e03140c808061060060103001122814070f40f1100204140e25144000740c003801100000c45d034011b0100041c402c11454149000100c144901e241c0241e8113807810a124104011040c00703150f01000c1c2d0005409414116011030540203907142201d1095143c0e59800751583c015028440010404081448103040c031001c030a4005180300300c209802e0780340020003951460042c0500c000c09883d81c0d01d006059000343c00820381164001302e0000f856001c0c2d04010f00400d4140c4150009400c0880e07007176002c2c0004241940600c0244014111079040c04218690b001000c1c00c1603411507680f5095072001c518100c1407102c2c285070000c000b581d100d02ca040000e20f08061500014810b840e41400d000044e5a0000745a0f00f40b00100c20168590b030050070300381a01c05003640b040c00328420002c1c40c3c0c4031681d4003054130044548608010000b03662a8200040300420186040d80410a503502155030b814500c00d000ca01d6 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 453672122 1250 453670872 453670897
    0x2010b06250f0f1101080405120d0b0a0801020306180c0a0c020d080c0a030e1503011206061806050418081c0b0301060305101b080403050c3322020105 66
    0x22035101e558480011024a0b816600500440e10860400038604241074280c2d0007482c2440f01e505158840d1501c031130030015040903140001600c2440012950820022050b00030071403584203645040c1503010707500848525100e48000c00312104c000220f0042c43d80920710411b05c0c1d80c1050081d1009543c082e070700701d81c240d91100311103000c031000450200007022a4580180035011403489464082c001d4156400610b21036a64800c00003200820310084ea411240030a0182907081e0890401d40010940d6400c101d6018074a0301417040605020341041007100c0c81130b58108050307010a0010b8a0f6121901c02c01800703100f080014074040c01d1b0324080b000094014210000e041d0200e0000039086030940d51040700c20b5000045e06000e009a10b02c184082d5241080300d11004205c10a0000d188880080c8014144076010404000c1140c1c10811006400541620004c40d5486908001c4990400b8140c01642c141140d00154002600f07060b400100501e9854400c1d2181980d4015112500b103c0c468408 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 453673372 1250 453672122 453672187
    0x405070e06010512190e0d0c02210a0803010e150a09020304020f031c0e030d0903030f051213050f01060f290313030815060405101b0503130602010b06 66
    0xc207040b030340840d500518400307154885c0030030901240000e4507103d441d04821074000525561703103540c05c1880080803990444080405e07820750211310949074080d00c0344821034481d203a8440d0800c1280c1000794141c0d2840c20b41050150780d071400d40808103030f03600a00c40d0003007203113001040a88055005541c01c0748c23005200050026054001c03034030340780f80003005d00e03c04001030b01550120750300010079204000e01a40600088048104003034a1510306200007020050380c0c3c4000c4c1c00f2203200310103071070f404007488901c1031150421402041c0a1100444203072494010b070119010300040502c1a6021905030740c00540130706103400e0119201200001c071f411074008a880c4603040c0b0f6014040114401d0b2541180071203103045504006001040083c02d05080003401c8203050480d0780c500041c3c40444808076059828051100d40407284400b010310b80004042045d00311008006020026003203607441c04007205100769590070100d098984016400c1c1c2c00803820071114200c80900d078540300102d04e46100408 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 453674622 1250 453673372 453673387
    0x1e0c0819121b11010f090b041401021501062a03020606040b010c080d05010f0b070b040209070504030b1003060c0e011b05030702090414060f06010e0415150306030501140405070e060105 81
    0x20304081a601c01103450f05200d2012204039030b08161040c24a503890300d4041c240710f0030401d50110500c01d902441150544942e144090342e8030030001240d98590200307680c415569128405810002c40c1c1e4070010700c480e02c9580110b81d4454003192400c0550f0160300400003501c8480502009012120b10281008072042040010802120003042404125000000c0c10b62501880b403040b031001c1d0700040d00da40310401c52640402c03042600144c105070104e0b442404e0b500d03140030070303590b03407050750300c000c16002469081003040c6514025602c203d90207260140150040641c0403519400420401e03404030b0480011225000c0d01500000030385032040d02101c2c82e21003503400081d03d4240403581190340b9803001c00f200d10400000c2c800c0b5078000c604001521500e00344140045c1507028410b0881e8007c942d5009282c458402c01d41c5200c004052100e00d400e003045220314010040c1599000984096017440b0115000003031041a191003150418003902085040005850741d0f280080c2c03645041000c20302014 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 453675872 1250 453674622 453674657
    0x409050c190f08030903060a0603120e0a3803070207030305160813080d030c05040b0315100c02041506090e1009020307050d1401180213031e0c081912 66
    0xb02c020b02851030007161256001c200b0545441001064603684900300142007000031b04001044180344000c2c00e02c0d01004041802107202d5040310ba101260400600302c51000200400c0d00c050204591400522100780c8030074a40105444180c40e00310041c0d020a8080012920440240c40398842004001c0302e80d03042c41c0c80c2d100c80d9400800a0301c3c0340c040b540204000d010410482d074483d02e001b600b03090100c0119444090300d80d000d24070a800c0070300300000001c2c13100b000703850001140c00740082c105a400f00d135003440100100610b600c00c80c0a1454220340b911041c104640c09803c54907180d07241841d02c0c1c10103c010b0b0702c410015002c8070340d040e41024049980109400503500c100079503501c043d04c482c1c206000c1400e80e0fa11010a10b0032140140040c400e00b600344c0402c800f050621039000d80c0c0c9580c88455400400c2d440d6001030005984920208480101600b02c101e899024018070b001c050b4990440c03903102d48003060040d880000c904485000511540e2159000840d1410a2442e03180d1090760b4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 453677122 1250 453675872 453675899
    0x21306030c080609071a0307021c02061b030105132f070b0c03070c0201051b2b140702010e0f09190c090b070204020304110a0b07060b0409050c19 64
    0x100c0340c04544101c14440308000b0042d5503404440d4000038582c036454184c0101c502c00c828500c18404020000c0024051740c02003001001082010300d411004400c0c23420020b450340416030700315803c91403008581800130000b201703803416a0310003051001c4010001484c80010316003d5660680da040054814070b440d800a40d40480b0201c03003920056440c0180c0c0703880310903140c0040c0b10301d01824081c014042c070a03a00c4546d00f0010303942800d109039140001100f81c0501d8490281810051044007500189c080100070080721180c03c5d0030140d511100005000d031400f0106d030344170784030f40201400141c01562255000d462012409003021802030a200c01080c4c4c144800c580c2c00360400c482d00002074180300c19124000407248203252000090781030a668080c1c511400401070302c50b035004008076050025200d0007414000340180804d41c41952814100215042043c00341c405500c0c0c051010341d2030405003c0c0329040c42d40a00a081340c0c0c0c120104220418444007070181c0084410200811940651035030f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 453678372 1250 453677122 453677129
    0xb0a0f14130b0606070b06090703020d020f09180106020d0e0f100314060108060105040317040503010c0c11040902130905070e0901020408010e0f0624130501150c0816021306 76
    0x40301014060036081c1034002c1040901164000d030000c001c084007048015034000e8010b10100d41c031480076240c0481c210301a000700032440d00c009200007403241d02c12940000601c2800401d4620a0454001d5141180035082c2413040401580040c0f510340c94042c406c0c00c40c2c1d0681080103110010208154000c10b010142002460780403d03514401655204c0e1500c00c101c1e03004c4024605000d56140450008005005a1000414110500606144e90155042a0f401618014000f0071104c0d50b0203070010207000c6400401ea0b908904a800007001f400c20b400703060341c0c4039006001c2020501c0200346200040c95000000e55982c040ca40c80401c10160481081d4081d036000320015880e14145001d1508603049810500d0540c0c0c05404161460040856496888807120704510038482114950750224510354180c80d5100f030b82c516100152608a6000303e040e00c0480881194160106500b660311042c07105010300304040c24403590b00c1e207219400307428032550300c080e00c40303120b512144200d1025030740983c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 453679622 1250 453678372 453678391
    0x4030c0302040f060305120a0306030b0702241003150207050706080610030b0310020310080304060203040e0c03060f1306090504060207060b1c110a0b2706070b0a0f14 73
    0x1020010761038140110116400804801c004e074034a10b641c1d0696032034004400050800f004942151401d00a5200c43c0007581c110300312241c2481c0c10500251946010b0600d4500b04040d00c152004070103002401c0c92141025220f019101e9066848005000c81c503078840b81807007a02040448000340c003d200340c0c0d0061010307448007031160070050200560708aa05810104141c500422a40155070000e40c115010145450042e505d03107130402c0398000102c1c2070300958890b210002d000030340709a0000041040300d074003260a80e500d071615481d400c1e49100a90f48a5403000c1d8456402c4070078506400050000c01c0045e0001034420741c0c41003a207058903c21102030b5000c0c0d070302040a1081c040c0e40d010b41c592210b01190114103080d1f40e00005111084041c0c2c001d4641c03c6800400e00c1c80d40c80e031200380340c05014070700f14840d15040c084940701410300009203085510100d45645603002e08202c002d842d502580701c00031181503a10748590074000c112000881c1400b076201d6420701c42a810410505002e0040f40 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 453680872 1250 453679622 453679643
    0x50d0c02040e030a0c0206163c03120e01021e04030b06190911091305040c0e06060706020c01180c03050c0a0b030103060507112a030a030f050319020403 67
    0x140100422900b020400c1c0c401c1d40c000304680340350b0b2644050f4070758405074100d80403070b11011558041e0070307560b4124200500400c41100c041808140d1607141440340c48008004007040440000040c0030080066002000b05010900d039200c10541904014041e00040e00018149120001200b40320340041c80da40c590f06000003410b0090084100c0b00d2070340008160b400320080242030300c1e00e108242c141d200714030b406075a40d514072100c0400700c41100c5108400420151074499284e000c04010a820b0360102d44c10040460001a040201100c1324031650340101018142145511004040e501800420300195a034020108058010314803100b0082e00950b10140f090b81945400c0d440d0040c0b254420b0711640c2400d00c100402241041180d0550b81d200ca80840e107034484c00c0083d2a68842d224481c00240034880075006822501100840380c41150b251046c036600d50361050603140d40e031422010300003e114150300900180030314021600140090320391a901c5444202031070407a0041d03001110b012a40 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 453682122 1250 453680872 453680897
    0x4051540240c051c0e0d0c0807020a0323011e09031403090618010516030c0302120c0d061d0a20030709090c05090a060806060d110903060907151407050d 67
    0x1904102505000f0710070040c01c2070343d140d0581d076003071b440202004002c00314203c10f04010f0840162030a50b41c1c0500001c4840351240b40c5000e494102904842001c9041d07012662802414010074800d00a01402100c0200c20501c2c21000342028000030b800340304200380142c0005141400440c440d03441c500203080582409402e0480e0040110f56854841e070411082c0202c290f91501e102e512110142000110085200c01c240d0182c000c001c480c5158014840030030806100c0f4030010714803141c1034482000020345500783c1215a400c40401c0003443d00c16040010b820928940c400c900342c0003400070b080e003010072403102c040d0254402c455000c00160141c40800a00945004034544d540840c00c102e4103001c1c404000c107070500c45500c40c03c410446803c000c5a00303a140e681c100c1e551401e4901017400034420b040c040f0b1038150b0103080c1140c0a445150002042007001095000c00c2d00c01d040031480300d451000c0c400321818030700052a4003980408000c03c0000520402101d040340c041900c0300d802e0003c9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 453683372 1250 453682122 453682147
    0x30903060f150306090d05031009020d060303080702031602210a050114010510020d0e0105090303070501020403020a060504080703030c05010b1003241d04051540240c05 74
    0x1da4041c18001c0c1e0100c401e10100c5c010100e41c84126030014a04540c40c1d9884800040340c1c6049a0310800609100040c4c074042e040b801d07080441601c3c02a00c400072240c0b2036a100720703a00e1281c040d920020103000c0783e00c2c400601d0f00032882103900e59400804680010b070302a1080c10407010f00411145c50395034412103d14a400340d41000d0045c00c045803c00400408807d000e07403600d002c0c800e5070301008880f48040041c0d070300400540c0c003074007005001c0380d40b10900e9180c018000c1d40180800da11840803c540010704c1c2d442102180c00366490580030782020b51440d43c06449490381040b044480b0354907218000490703151100041000507880d03801041c02070f040320b03d55503c003128041c0c410050001e420306100701401c1d00c4046000713204c0305121401c81e41e52824541d05000c0391070600c06110a640c81070018148842d11003550816421841c120000ea40101064041c080c04604003000f041184c901c030041160202d208801c0030800e02213100c41d4100300c0c44041110700040803800840c00c0400c68003034420 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 453684622 1250 453683372 453683401
    0x70c05061005060706180506010f06081b04060f050f0f030103060b01030b2d19060f0c050a021005070b0c031e0f0c030601020a1b15050a081503030903060f 68
    0x2080601c100e01c10703400d000c0866414800e20001038041030315507144002c503144007140c0010154005041c5c400551b12500c0512600030030703218510004d81c400c4c0c040f810a600781303800350907601c2c103050002c0d1134285007e0341a00c40b4140b40f4103850078050b050001142a444480040030600254050590b5035810361900004403000142d00d14100752404401e40710a032200c01500086180901418070340c41904e0307041d510054540795403c0e03009400c142c4101e5820503204061030a640b5941c071000500501002c00310b03546c1d85680c0000c2c045038400302035940941071180030000d1146003841d10628201c12511401c0e039440003513440b0700b00e40c440002003041114041181112003540840a00c4103810044c4400201c1d071030103443c0c0d1504031000000b1600c42c3e8004c00c5801e580035444a183c4180504035803090b15940c1992141d00500803a06001021039031060b0100c82c01d59400352200c60242d1600b01c02e080c55450500380c4e1a4240c4000c01010200d95010890710348200800c80d00a5036924010310003902c1711 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 453685872 1250 453684622 453684631
    0x170406030b1221090a050612060111210d110a0207030b0109091109130203061003031b0b0a0905030c0304091a1807030b1305090a020a062a0c0806070c0506 68
    0xc0c0c0010303080c0003011000c0314007460700300f504000550b1240e030400005174160350580d10042d40400001000c1003d1303456100b05c54441c00090b2500d0580c0c03031341501d06c40d0f100e81000440070601c5a0948052440d0070718007000e001020000340700006e5200c0032480d00d00d015444100c00030b001d40d001403000c104101032460500e026294158080c03160040a0740c0b401481100f001c4d01c40d00c81c0d441d200000302008401c0b142403c2c10b07a00102294520308001070710000c00c00e03042c0019000500c6e03c0780361090050b820325480c02a95400a01c8204565542e0f002d01c0003010040f1088400740400c04c0031000389a01040903002809096000040c07034646032106c0303820394096490f0140a1500400c1c4400b01c0010070784c0583e80421a4240860540c0c031401c000780082580e000c080e1001c03440c11080c0080036800064180e0300394800d40d090652552981d8080d144641d10000c40c603a0030f00c06030689032907112001440c0c1c5c095032050030100c0714a074950780d04900300302d401c4403a400081d19000018007400300810082c0c5d000f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 453687122 1250 453685872 453685909
    0x1206050901061802180901030c0e0919110307090e1b120c09070c060f0507020c0f030d050f0d0203070e1c0209061210110d0c0206010807050d170406030b 67
    0x191503c0c00c0c4034110300703940b40c952450f280d021481c1444c800d1807a070316407200d0070000d0540d200f540e101d1420f80744083d003501941c0401080080040d60308000050a0550111820000000b10903584e0314100c0481c1c0c8030b0140ca4160160060010f11101c2c0350046a0b80303240a0720203856541036541c04214507500080006100c2c01440b4442402c81d100810b404048550070f81b1041e405076580c020584078884d01000042100b8982003100e0002d9849500c0030340200c056034296038806000104000000c2000200503a242c0c12035040010f200e8046c0d4000d18081e0804928142031684012444040f07800407a02d0794045001010600020724200020540192044644002c115240e80200d003496800a200d0b60141d8800030120348140001c0040d4004504080018070610640e48401e2500c0d40200c400321031610300b0700541d508003900114040f816a030f100801000105e14100030443c895036600c0302501c01101100a88448601d0840148050861030728041050b90042d014840c450b42c080454129 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 453688372 1250 453687122 453687131
    0x4050a0f0c0c0c030611071403070201080c190f140c0109140a05030301060507020d05030a17090d050909060103020909070206040201021e1f0e0109061a030105010518100f1206050901 80
    0x1608031981ca5040d05d401c4000014540310344042100c0600c20354202910350103100406003903142d0004003c00d1120b02c00e80e9861a01d0311414840900c50141c41d8a0b1503404070030b0300c54280860f04c0740e250366014000f14030300080c0109694803400089e0b0322440007e483e036510380c1d00c1001400540521460550950750003000c04500c40e4892540301e000602400041203800180c00b015540c800720328080c125004425640d17200928500901820308080c14640e042c0c5030200001c03100000420307201caa045a5071285890240f004042140a5800a24041c1455800d20000703034a9243d45c03c0540c450600c940041c84075060500001e0326140300003500b02d800d41d440341d0840b2810302020601054560546404000c08c40301000000c0107400c1501001d0361540c40c058802c0d0a00c01160401441451805181c1108031010300c01c0c5420781d0000d000d555040401d4811035400481c0300710b1103c0e80082121140c41d22641c948000d94000c5426034402d0040f900c0c5854444c0030700c211881001d0304500080001c01 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 453689622 1250 453688372 453688397
    0xf0e09070b0c190201120c05090901090e0304050d150c0206450106080303090c0415060512040507030204050103060504021305280b060412031d0f090a020904050a0f0c 73
    0x1030791412030102c0d070401041c60410440459000d1b110400800140900c01d0000c0720f14580020f2040d040301000c03d01c81c206070000003920f0319040c441c0580740184103010b10728041c184020b00c0020366000c0400c40d2607500c001050b9069070598407036240e170035405034003400c1e003414080d83c9141090342c452003218800c074450b80780b038424120002c94400c62551001c450328007250030b8900f0384e00410060b402200306000000c00c006e8551800324082c500c0c80d004803020070072204440746000d00b04295016920203d6020068010708003d00b02425034481c3c07280c000c49868945a90108080e0b030401c0e401103c11a44031810f1100f10310b080740342d40004181325201040f56150030082a40e2000026141d0800d000c100d2801500d01007d640040b03101c0ca001405139503640f981e41e100e003c081900c080c815400030b882c0b02090828641709404152507180002c108144402d400300070040503201c06040d64100d10350800c1501110703161401b882d4072801c40700e2400503004604109441c2035074004090441000005d040c000b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 453690872 1250 453689622 453689647
    0x6080f0118050402120d0207050a0e15010c051c0201050a0b09060f090c120f0403020d090b030c160f03110c0109210203010b0319170301050607030c030203040f0e09070b 74
    0x240711201440300e01085589030313070000c50a5400b4040d60750b40706018019030304c03115a400186000c00c503102560107000c420b0791071804000324641030310b240c240000f0301c02c40c0c001d15601c41c042d060062409001500c08100008100d62003000c001005580581d4440c800c00c0440842d40c85070f4041d07420142c8961890f4500040040d0314055800080c602c240c1021012500d500c0020f1306071070b42c2540505051010b070a05145a07201d80e502150128010b2241000049000c0e04c21f43c0c040003210380101d00b050440d143c00340001e0f05a0000c0300c040102800f80c49101e400306800c41c01040c002402074440001e0708042c0f5a0050038184001c903d581407010b614400c1002044185003030341c0c012400c2d40c1d90078142039039200181c05040d14410580c1d061088440d0051031b001c5802d2444441b520800349506840102030850310345020922616078045424861b100110380116010310426120340b040d28a07141e2105801103241445420031008808508100104020100491401307040d11043e564102030ba4035226 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 453692122 1250 453690872 453690899
    0xd0e04020909060d0c18090204110c07120609061d0d030b1c08040308030412080f1605031e070504090e01020301031110030605040c0c02181b0a020a020a0f06080f01 72
    0x34680144d02c02c160820074009240903640107007107880c0d8100d0348014040741800160a081a007031340300d03629140c91003116031001d6084606204039100907000180c079102c45880c3c800001603003640e5254640b0b42c1d40000034030900c243c140c00201d498800300c1010108103c2131401440510400c141071508446d0003050340c4299120781030641e10391082c00d407036a90f03207800403481c0202d9000070b00140e4040280f108200780030f043d866800b0791998071841c4640d20aa00388180781025210558502c0c0003240308803c01380300740d0007141e200074400e100b50719030303000a05a0380241104540036000242c02040a022040d19070040c031100005120081d42154115102c0e0009800d240d14014801d18020740d5001010b0301941211000f4940204100401c100342c2c038003d0f1048600410480c41659030342a0550341080007201b99004009449401d1180d240302080c1e503502d684156407010541c45000611030060741c034020304001030454242c0b500b22003460404040c2605401a02c450803038000c030030050098007201b444 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 453693372 1250 453692122 453692131
    0x815010f080c07060f020c010501051c0c05060703020f0a150c090f090914060703051504021216140403140606010504030f030e0a0b03041209081902040e0312090d0e04020909 76
    0x42c2543c880091810304020300d017180c0c9261243d400403c845d1120101075100a048950a807000d4880030074404c0c504800001c034a00041003a2040c1400f8480c5080000107044d00340c1c482e004039203500d25040141071401c1c803426011503460200f054440301c01e81c2c0a0007503000505079410141400750501d003a100340c0416078081e04480656400741030007400400c0c01c000e0407189100041d10b0040c206a800200505011101d026113078880c200380b0325442c01d05100315101d4904c0d0489444942d240c0881050f008801c121201080104100310680328082400c0180000d500c2034801c2070340101522030550502c04010092414003000b03000070030100300100c856030211581494281d44442d481c0c2c00103001c060164114820f10300d00401040b040100e04009020040071540711900e81075542c4003142c1c2d90322044058128420001082c003401418580c00080800a1102c240da042c9501100c0c8a81c02c0102221401d5580e448001e8000340035400c1031024113001d80554080d45007d544d80c0101d00c04040190 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 453694622 1250 453693372 453693391
    0x6010b0306010c080a0302040812090d110427050705030604080403120516140610120b09010f150905060604050901063603151413030302190815010f08 66
    0xa501caa20854082403815070000c115500c40a00d01e100600940250103507040d54802c0d45a4807890300d454100351004050024251409036015a031107240c2902015400ca4005840e0004c040901c10715011100006d100c07150002420280d9003052454035920782e12241c0660004018040851000380c115400d0307940000c9841100070b9000c00c111114411418450045482c4920210402030022684507203110001c080f02ea06455401545407449894403504000d01160700d400c030000740c3d4000e030450740f20340e0b004000604d205008048000740e807034920040d08000b54804090103203403400c0c451142c110a042e51450300701070030500456040c90060041d0003d00c002c3c03c0ea000304422100c0301c4c908031000c818000403001442c2020081d500c82941c041101d4010a1101c6140701c643e551040341c4940c2d005071152156511170044141009610a40a5040580802070143d5403982d4020f85400703003009549010003072520600c00220034244020b403030704101807a0703071901c22a41d00c443c005800c10f8445 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 453695872 1250 453694622 453694627
    0xc0708041e030204050c07050114060102030a031a04090804050306010b0412110f0d05030c1516270e010302040b0111060106110f010f0204150203070309030303050402040e0609060105100509010206010b 88
    0x8041c0803203020300d20741c4020352007400c010800c02c3c00c1d01404013401030316101e03800900407003454001010301c44004850041c01a801840b20404151203070b00304007801ca14014030514a03a803c00041030940d45c4a10081e1054400007a04001505040112070300602d50f51920505180c20803001102040d20801c0183c25000801c054040c2640e0300003400c1c200c2800203003483ca09840e0b6144c001e41340e4010309a000344a026500b41800c48042c541c0850b4450389090500300b14210060000b81d84101007180203401c2e110412a012480c940035a00e10005408100b000d138003035615610402c000c2d0345c5179416140c108500c020307403864110070000d802c5040d56880c0c1068400e2500802c0e0152808840b002c0700c100540c20710700b0448880800c1d034010720945800e20056848101c0511040e0f035648105103000b000103200100400100e8400c0c0d0086420a100a0003c24118050010fa03854400140e407407180c0d603000308004209901d07062038068105045401c0150402504a00103911340320144210120000700 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 453697122 1250 453695872 453695909
    0x61202010228111302070605061e1503070e09010305031306030204030807022202072303210a0912030c03060f1d1306020a081501090e160314090d080c070804 69
    0x1310b0650f0381880070b010b0011501c48150b8180070010300029500701703008040340b0340b49020b25450030f20910212031020b00b915024950008140d00c040d4001071400301000000040310300540d032014211402180504020742c0c8828000301d0381040409194040d07810b03d0300c1001700b040001c039113606032480160101c81c011050758400000002c052519240201c646100094010400c1980c3c03104000002144003400d155007605000d80e940c903c589860408101c0e10810f000c484c4c11481e81400b40d00004c0010045480511079445007e442950ba080d2004a03480718407008201e50702d07101d0240100f2080307414844141c50281c68502e1984000d0030075120300c0c1400c0000d00d00d207002c0c440c11007805074090800c568407070140500600c0440d060301c1107008484a0200d124140d8450f1042e202656283d20907440380c4d4a402d141e00b80400700306241c1c10145611619001128100c0340c50603442050000064036041080c000000c2507884010280b0205075010302511000c58208010382c3c00747c94600c101203c02400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 453698372 1250 453697122 453697129
    0x902131202040f0c0c0b0105030316200d06050a29060906070c030b010302030f0f101a030d080a0b030a11040b060f0c01090201030c020c090c0a050c0106120201022811 73
    0x5140f007510880504000d0140c0030964011503a14249000c0c2640c2c004a9807280101070701ca00c5000d03800c84040c2c00469801000c02c458114488142c1a0b640c590b0384d5245150002c90790b145074105c4181c440650307a4041150b0070300039019400860110104100085d00a80040f07030311000b0f0102c0b81030164001080043c07858452504580c8a2a08500341d0340b246a07a03072515404030602404100d0281c002d801d515a02d500000400050300c00d618001b0300310044902c800381004040400c4d04940710700904414010350788040c004081002c40b0350f692180c0a01d041282c42d400e403148200300c0da002e62701480ca00300100c0d5208c0301604503840100c2e00402c02d11035020005c0e24601821240c1c4080306c000003480103c0c0d000550058420034401c0c2c03001e21409200744810307a241c2281c802440c0c1c000c0da050b00042e92a807100070040503a01c2c8075040060a0045400d103250031500160008503140110001c081d0640d030f0108041540c110f02c450450900260040c4041394a00045200400c0400c14960900c403954 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 453699622 1250 453698372 453698381
    0x7050d06052e021b060a03060b031906080a020d140c032a0d0206030a0905010e0d0320040602100902040212070f0e042912010c0804030801090213120204 67
    0x1800900b050b40085400c07400340880c051508071403440010b6008014045800459131000c02c030a601048020141420244152075002d408142c0c105960350f00040350107122034000d1801a542025881150030104800604450154200007c540c2c440c00440005945107003080c4150307640900300703400d100e0000d04100d113084807840540c2e0380350244400c09402540340d1107400e04c00c0300c0040c06000c040100e600a0101d0140d00c05406500904100700040000d80103401100200b40725000000f803d6420320000b0b030030200b030f004031580001e480b48026442c00d15641403007468000e924170b06a01c0d05290507000f81d40c0781c4048502007006a221003401e4259a12581601c0c46040d4241007111035280118000307040f02070420507071020544c0b40c5142d44407802c05210f4103119904d1860ba10008600500300307240c1c450a5803585031342c003000c2100020780c90302c82030140701c5881480342c40d1040a0700741460054032070f040c160040c004c0319105224014940c20303811f4034076040300c080342100c2e0200c00c6540045400342 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 453700872 1250 453699622 453699629
    0x50109080c01050d2c0601090b2b020a0b0705060c031003031b02130608010f09411f050906190e1218040e0705040e0f06070c1101030507020607050d06 66
    0x5c0340040000040401c02180e4003019144100c183c85050ba218000035003182d02150995410100d808030b4460300c41d10300e040e006a4406140e00d0608841d216500007206182150803010440c1c10202725003003040310802005070040201c08003c0d0940c9046010180c00802d00e220240400400c40d6141d001101030b82040308600341c01030b10311a00b6060909061010300680d01c9401c12940c80e003100400204403d1150941d92644000401d030a44295902d540d40c00820348004070082c0d4070301801a43c2c11041c5110140005074110140000d0510310b03504080488aa2541c03868440c1040300700000608003103207095000c181a040b40500880240110340200800c00980c20144284482c071402180c1e10b102a08507810b0358000c3c810300400d040c090105030385040e65828415400741d0350511040c03519410554882603000120b0300074916030300d5498038208080e151800810844180c107002d120040118608100081c00d06100c5801c040b100250754420013041d40e008c10a0208403840051490b4001c20004c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 453702122 1250 453700872 453700901
    0x7020904140102071a010503240c09030a110918060c031b07050a050601120309051e0d080717030c0a0810091104050301050709050604181806090c050109080c01050d 72
    0x2541118903040d00203c001005c0480201d254070000211861b00080801c6181000d1411420074208a9004400480c000d0004003030f00070144450120386e1002c00c0510303556401104a2000001c2900910000c0703200035164004052000c440c1c070104407800626290494440807245640b5034588000c5440c400219000009100340080c96a0070f100000819014182c018016501503981c0c035400c00101e03406a13a80100810021113041019140601c882040b9a030304151801e130404030701c000140301d44e00044003103031030400c0480d01c60144107110003d1b4141019059100d4a18200344140301c0c8503004e60120304081100810000d824030801c2c28180000f056100d03c1031100300d01caa40c110445401c0341c007409d0300a610300000140c1d498800c0884404030b46000c0c08bc1031801e818900c010914110141039054059142c1031200c040b0b140b48041d010003640115000202c0c00c0f59441c11034094140e0740e0045041110200f014482c148003c29114003000d000d013041961a242e0003c048040e200c0304114400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 453703372 1250 453702122 453702127
    0x602030f0406060602010b31062909010e0d0c08030a02030c060606030f0402010c08120c041502011a19030203010507020c090a18150e0d1e02060c07020904140102 71
    0x1101420000c0c06000c0e51080c0410310606481d441c0882c200d0b070b42e0168035130340618284411801007140f000b1070740e04800c9507071600014801069511095811070f072700800c0d03460015442d000050480010301040208082519842c00c425140024101003020b01030f0f52042d03c4602001c0c082010310030710350008041c04800c1c2c9072150071200010351250440c000c130481500425001850301c3c5090001c0303d2040701035600142807602e03290011030b00081420000c48199808100e04d00d00351500c4042c0c2442462141c40706507440b0308104102164000c1c92440105582c1007540122103200e41c0500034030f8120301036403100d00c140352134030039000f20452075840650154a010140a0025402301d40485440c03021740d040421a00c07103c294104840203000e03d24003012038a50030000140c60459035039110700410304003143c842014841103080c03c20304c80303804c004248004101c90b024020005007411881c1240050400361814a641410600c0395a40080c820780e40000020200b05000d8507580c42c2c041410000c54 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 453704622 1250 453703372 453703381
    0x81b10060905151210020c1006090902010e0915090703021e07020405060d12030207030507020907170703060b160215030c1809011404051b0d0614010c080f1303060203 73
    0x50050400f03481e03080e00b0301c50700c030a24441e5041903e9005580400700d002000100030011410009421804d00c44080340105004082e89140030b001b154040c00c0c1d6100001507056643c4000b50208980c0224940104450400c21160309020f14005000c40019100d41d4446d6a40210442c000c0c494000100300001061507480c0c2c5242149024102580c0709890402407510b509081140b61b04420b140207001f5010207480c13481492007038024244261080c02c1c9181020402d03400144007003011100d940009480e480b25410720741c00c0d00b69458105e01203081c10440301e400e00d4240360341c5e841544680091580d2104120045488540140003204440304030240c40c0d0801c0e4411004580c000c45020701c0b884d8a007440000302d40740402c4e056040f241003218041154090600380700151800505003040482d0740e604c9a02c1c240c0c4014010404d06200042c0012854107100c402d50250201d6051581002800141400010050000c564a203202e0700d40301a1150195040307480d08040a410040143d4000710030711 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 453705872 1250 453704622 453704639
    0x109181e3b0d0e0a0b120c130909060504020312030601020c0105071a1306060509060913061b020a052103190204050604090c02010e150a0903050903010c17090703081b1006 75
    0xf82005411039071800c07a0f07030f40c800b050380c801c1c000c107244500a0380b68100442d21410942005040e04000d40a42e03c41d00c2d5a1001400c08071120610141c5440341c642c0208011449d060020081601c0b07410002419401c4c4100002c0d40c490b040104130341800f9001034040240301080c1d120002035006019580d906182690340d0504d81180000c1c00c55409082210118051402160103841076802811039070f515581d07061405e0591400d042d0035241d0555079401c214100c00c1c0a000317070b0a0380ca899001000f40005910304a80350072103c618691144031401011502d42c085407040f01d4000e00010400040155a008504000e1003150300095010f0000074000a00341c2042e005482001e46580082102d0a0303980c4038591218510769600f035101903003900082049042e50b1006071814020715029040504000c0400d003102d005c180214003282d9480614444000726940307840d88002240090b101c054950b17507603a00d07075000d01a443c0b402d8485a000c1001038030001c002c819001c8172465000c1c4411507840e0f01c00d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 453707122 1250 453705872 453705887
    0x90109050d0c031209030c0605010f140d020f01030b0117150a090e0601030204020a031e02190906020a06050a1107030809010b0d02030307080304020109181e3b0d 71
    0x40303880d0301480c000706807224060203022142d16019203500d0365101040440c04010130078444200c2c10b104c1c0d078070010001301d046442074502820095451554660a02d44002805010010114454004582003500603100c101840740e07084400c2c01c000c100100a03100598035100071030b00f034a032609015020020442c00c0040740350b0005c00242c425040c0caa49860b498001d80c0c0a0300c074080b02550000300100011f003040d034020301c8900303102c0ca0002140d01d1001110140a160301411246080e0042143c0c42c044041d07100412010b0704605001545a28152020b519105032507030107070240d580c40380064885281500318403180d10740c907001940d0700c0d60203141c0900140405d480c0f45001e580b070045841003d0400e9087c0c44506600180210308022896540407110740c0020401c904008100c04005900041100c0c0c250412601580104002e2100c80314224142010072003102c1d01400c2c244103c11005841054540700702c0702d41000c10a6008100b15004641c02e645c81d4400c107031261244515046621001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 453708372 1250 453707122 453707141
    0x1300206030408120915070804031704061104091b05040302010903060f060e0108030a02060916051203040503060106020304090507030b1302030901061503020d0e070803041509051503160903151109030102030901 92
    0x811b45115118008100c0e0304500c1103c008002c6080c0c002ca103e00302000a1205030702a20948000c0365498400302154041e41041c0d1002d501d09482c1c0d24401e00d40702c2c1500750a000e494940c40c11034241450341e00000d02d4800c0c548005807544d80d44a001017503a41503500010060503001b001d15400756521003200307942c0d0380610540801401040d000c00c40707003440426400410f0503045012140282044200708540c8180d610440e49881308010000385d588003401114008c1034240c019640701d518000d144400c0c1c03240208240105858181814095601c041c803001c000060040f005803a540e4072001c107401442c4a03003080701c205503515820311005600d0380050210013108001071020841c104001c81e610000e81c0a0340b60150003d01060259048070245140441494a450307040603070350790013041c2400c901d41c07a80048070310008104183c00302d8544444070002c0711071078032050861030b58440411840c201d1614030b1282d511030141d23101c0c5140b0321054524100f0014021590390909203071060084c0720040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 453709622 1250 453708372 453708403
    0x4030503030123030106050a0605090406051f080108010b0a06271410020601031205032a03011a09010e1c0b090303041e030509090601091805013002060304081209 71
    0x4181c3c280d400c045c0180b10483e20060407480c60542000b40a68058000480c2142c209070385500000784ca0761030041c0317464a0350040b5142007108078840170040c07082d40140c00c200c0c80c0c1da04000d0423003020784403d207242c01180d03c1c40c40e2035580075602c4c03040c41034683c038502906a00020440d2000c034040d4212880110000c404480c14a0a0700c40d0400a903121042444041c0c00340c0f038851121422580184025913100d1030030440c40c580403400c102c0c0314420001441e02180101c3e03010005100c109285540400d100007100d030f485050100740800200882d000840c0d0354020000c0321151920008a08030b5108810b0384043c80384e11034a4400c0d02d0b2940c0781c204607001e0350010404001010498442054030b580340d50143d072041c2c5004004401d2040984010382118104a04044c00103500b01c03100e0500201405041008a442e5140809241e445801190840c0f003c00404210b04054071908442502440e4159070300da27244d40e1241000380315800749440b01c000440e5003004110001c040030559917114502d52 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 453710872 1250 453709622 453709679
    0x8060a0f0b01090501020a020d02150301091a01030e03030a090302011b110105060414150109090e0c0909030f07061a060406020304210b06040e0111181c0b0f0c040305030301 76
    0x10401103d44006030302c965409030b006802880b015041402e000c070206c81c0081c0119015010122005800d540241c1c02000d007a030380d0302e900308800f0032442060208200d0034a0107002c001d001c42e00c0a612448098110100c580d40c409120b020107000390080d1011100800c140504c0d18020a8041c004403400f1102246551030040041e880b480c10b44594038446016240e0030f42580e4803031400300507800c09001d0003410700446040000b400c4c0b00c1401158241c000c0301e00546a04140302061107101c18024180070410340040c042140720601300c5041d500810382007500403e10071100c42c0700d901c4508a0b020309e260418000a4042400358001004104484a904c142004d2004170b488080c640400c65000404500c525030216655203450340201e002c0980e00000001e40c0d548152911025500c40302808a00012081c0000d06514001c0c0ba1078043d40e00c0b120207103920a0030307542d80c0c0035020002030000000c014403a000c541b080181700700b0b4801075036008088a5983d61203550350700e03121008014058100112 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 453712122 1250 453710872 453710891
    0x118090510111b0303070507080705192001080103050c1e100207030b011401020d050c10061410030509060f1308042702160308070507020d150e03250c08060a0f 70
    0x105c1e4412146950b50030300301901691610307061790005405a80ca8802e40e6203c425140010442548040c411600a00300f1598001c610440d22030503111681444031500040010a0010801c40c41c4424115100741c00c50028000004440501300800c0d9089035041c0011907009400043e01000d49000d6046402d1581e1380c1d036040081500c900b2282c9006030050b01f01054040d0040740a045600507440c203883c00348032040d07900001c0b20b8040c1e1102d650260b101800e203080b41418149006500160700c0c00f8440b91a02ccc2c20455650000500341c008040c6808000510001001081da080700d035020381800d80e0b03a41c0e01d4003075030340302c5181a920203104c10407072015000d0f000b494421030b01035280b640b1440f00340c61002c0d142030301c40c03807c000c0c081d00034004208049001030f503c0711201e414080c850b49211041ca4581450309049a0050b000d452032075204001c403086440c5680d5108514940044c00031034002840d20b440d4904941903800300d5564480d4105001000300243c00c000030030300c01e810080051400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 453713372 1250 453712122 453712177
    0x3070b09010501051f03020a170702150a060e0f09031b010b0411090916111e07090b0a090509010209100807080f071706120604080a0e030105011809051011 68
    0xe030000810710701690042071030141c6c0660050032600c0f0050911001c008000156a107180004030791000060b0004418240303d0b1041e002415001005030100300013280c1007041d8039410341d4001c1e200001600000c00041d0b280041002100c200206090241e84001701074031000c4c0c01b0707196050449203d1828004500000040001660b5050500500706070040c2c4841c656a0380d18102c1c0d1000c501005088010042501020803d1010703030b04c0c0307180450402d1001c1c460300900b411002c1d048003d004d8100100781d501c541c0d0b440d00032400d80380b8841001420352a8520350300e0080c803400d41100e03000b0f600c8002c03601005401100d01481444a5165011642c2e01c030010f2000d10401140c83c08007288a1080001074522541039480d84160b004d005240102100d408091501e00200c80c00c031601c540000e0300d407030515400044040d0207030f019002401070b9410071808040103030420041c680c986a0300c024400500008004042543d002d85804000184c0d0b11043d4103401e82c00281c104000e407400f04410161610b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 453714622 1250 453713372 453713389
    0x408070e060607030f0c0803070c0c0b130e0c0d11070210170109110c010908040807080102040302010806011d0d0b01050f19060e060d18060e010209030c0f1203070b0901050105 77
    0x10002c15241c41c01c0c685a800f951030b04000c8259500700070700240880006098140154041c403030036118000c5401b4a0300d84040550720603002890b855400b4041c0c4109909007040c0301c419038081d00c0ba5010581c3e600e42c4a071200380a40002c0300745403401d101104e0182845000101000c03402a40d5030b0401d21407045040e5444030a00c2240302c0b40c12a41c2004003e40d40003640103000750650503851500c1c0c4401c2291190075182408000e81c3c200d0740c001010061300c2420080380313006000300c50095051070301c0d40c1c0001e0300d42040200700a041c0f001042680d440b0401d00718000351411002051565480603504141d20ba20b0303030074003600380503d8900b040e140452034151900c503481003586500c40c80f2241417600486441c0c603189005500800188140b100d060720038020566910043d80aa58000c0c11a080140903524201e0780208181d1040040006544000ca8481001d010a4510501412504000c502d0401d065030b4a80e00b40c0c00013140c0d903410003820f2400b0501610f000d038024400e990f2160100301c3c4c0f06 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 453715872 1250 453714622 453714631
    0xb04060f080a171903140919020f03010b040e1c0f02063402061b12011809120c0b01061d01030c120e0705091f0e0c0706051807060504080c24040b0408070e 68
    0xa000403404a0f00512b0515000000c0d6080a00041094020200860309480030b41c02c440c0d02e0398010102c030203426100701a600040d800e86190805040d000d10101a45540d000380500003d1101024503882d01e004116610924a10781554440245070750700d402501c40e5426900044c8078409118211040c08bc08806e036244001c0c00340341404240d18101025000440c400a000c0195032200310301000300365020000101c0502680721405002c585140c1002c1124058200806100b008803640115104000703030b0380d04940f02820006420641d8030303029109071201d8190704190900749506400c540001040e95003c6400c00e65208049031204040c082c0e480d48001c2e00042c20304814807080102c251040c12054000a02e00c0844d0b10f444210f4686000351281195040c041d100c40d07a1854000700c60070000e0380000c14261519604250a0038402a11115258070040c4180745c0720b507482d50704c2e8001c42c0d021901c0f0088a503050741e64a41d10040004560420300c10410710780503500b000548094191001c9118 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 453717122 1250 453715872 453715903
    0x1050a0c1d090603010902090c07060e0a0b0a09030e130c0909200a09120605010302011d010e15271306030203030901141c0b04060f080a1719031409 65
    0x1c0300000800d0044a01d00204890b525640312204c0102513160b02d0002c0340605510460035030350b140035040c003109403902c1d00c403188950b9016010f02000724007190907080c0c109404840c0441c10350300b10b040c111980e001c0c0b02e941542c01a84501400780040b40351f408103010100b140c898181281e601c10f500d104450300c1e000000c08194005c007481404c01c90501c021f001d44d0150342844030001d500c91110003e0780b00b0340c1c1002c9031503503554001802590f81140a0769070034a0540941c0d40c84016034000280b0420303010750300078052051048001d03500407015050b644035803101d454100e51548280b4080d032800620242090040781710501d5030421040314003d2600b40ca401400030342c6040030100045505500d0b4130b500c1c030940003040c8800071401d0715170340110203200d207240030101d031a82445082004850895102c5900200c100390100a0b08001103150010f1030b401012030465596a035100416500c0b4060301c9003440c810605840d142e26400d03900003890070110000b845130760307520a00d00550303403210300040040 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 453718372 1250 453717122 453717167
    0xc0d110712050c0f030c0c0108010b160809011b210206070206010b0f0405040f0c03060f0821040e07050301060215151003061a04050f01030b0607030302070606030b0901050a0c 77
    0x7146008000038a44034600d141220356284180f8000d03819604090265019078121100000d0250703030001301e007409003440305a042c0c0317401c0401d00d11803084211084020f02e98070000c1504840e5a0103110040d140000c10a0002030b141143d01c0e00402001106104404030780040c1c25a211492001039128445c2140707800038403181c1d013840e80300b0340c00b42c000305607811802c1010400132a0030344450140700100f007142000403c5081c3e984c440a000e2b0345090f0440804000b407000d0400c050040050310510700405a0341600300d040d1034100700c1d455480307290400e04203e41c000040c40b0440354000011030490322a5401c0e81d01080001d401101200c8040d925444c0041c08030498402c103181c40c254000d0081401e06000856035562800380e540b00c80044480c1028000205040000d41003804003000d92101c2460104000302280c1d0004042d401206805010958041001000c0107801e0b48188051030f003261011030f962506010030b40c0030f800102c0c1c0e0410502e04060b10406042d0241c82401c0da040d01c20841140d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 453719622 1250 453718372 453718403
    0x405040e0a03120b0310020c100e191b0305010c110d0504060906200106060201090203010f090203070e040501020708072d030801052205010b0a090806010e0f040f05060c0d1107 77
    0xc0c008440e0303c90742c14040d10650180c00b00d06c620081c110b91003110b025011404408031030b0801c4811804d80d44c6159089100741c201e152040d10211100c0aa02c046800360082004654149003c5690002003007903180c0308400100725000070f02040a03010100440d03911005550003202c3c5401240f0404000c1032032040c00340001b0703001e6401c50f0446140e070143d070319004020403803440c00e65906501c81c1026035554240c0f48250b090030300882d0100007103c807061046000c10f0b0701080e520100d502c210007613400544042010484290101d4900c3c0303030070012943c0c6440389030402a100c126140c910780080c501409904039080714100072404141d805031103400c0d05030b10700001d20000d00b21480b0100d6008200e00c2822004119a00c61203010b001851031645d140d0240d030001400f400c8070350700030503543d9100600402103140314103005640003c4418140c442500c541c42c101d8480b40c640000200300c2d01480c8200a80c0d03c030184080d180c03800030301c001840380311900001c04405101c0c80b080036100d0300c01200010b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 453720872 1250 453719622 453719657
    0x6080a120e100e012105090c0904080d0c02070801090803010512010509060109050c130305030408071a031918060516030b0d060c110a0309080d0e060910140f0405040e0a03 75
    0x9034007588107041c8684010018aa01815510401c84000f2546d94400c00e03c50310420801a480750744500340c492009504054650840900500e2030b10500c503911503426444091083c48818010203003000241300b194403d24064450781c109000c2c56008000d001c4103000c00000c14090280030b180007a003c2c100607400c0100d500060100146404009031040058418031039000d0000b10040d40103034050740e16981270581c42400c2009952060351446040c0c6402c00000800104880d00030b144180c940d84c40d0100c070780002000d0914a140e02c81c0680d003e88414081c000e035600300904c20704004400d03510b6904005400c1e021100e040100d95001041e07004054005060b40d88007100320301e03080c10034052280c1c4540f40a842c00ea2003a43c210001080a0810824914204819603510440303050400340f11000a01081650140c07501c0140f20302c8a201681c1c00c40d81c090613402120750000d45505030703140c04138205442154410311650740200c3ca030401d020500388020500042150f031603503820008031100c5005 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 453722122 1250 453720872 453720887
    0x130807020d03180b03010e06040501061b0203100c110111030106021b03160b0a08090105040b0604021c02031f0905060f060f040b03070f02061b0a180906080a120e10 72
    0x850610030a4608108214840003201c00201214102145c0d00e42c1031403240c0da0320344c1d0301a01c0309000e103090a00500000750042510018411080102c64001c0401c2c00080c1c50b10651b0044d00c0300017807500082c171590f00e5000c143c5190311440000288907501c01100040d029200034400c0700010303084071252781da0002d04036609102d000b000038100c904401c9a403107681101100c641c0302804800000400d0206581c10990459000303030184020021464940c603580c0c01494018080c500c51a4001082c0481c402400ca01c5107030200050021500c9180402a240c48020402d1110844100f20301c0001021032460103610b103e050b000d0710005c11070524405204e05604022042100c00c0810310011030384d068604040d601c034080f5039444c602c146c034000002900f03196014011307200781c50007400e10040050489084502e1440c092030809020000c0656170a50a0001d0704001c4505d410328400150501001880d801c4607070040e400c2c4010009846001d0703911489210304607070040d0111050310502802910b8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 453723372 1250 453722122 453722149
    0x9180204050a06031d190201030e0f0f1f15030210090b130f0e0708040b100e01090603050c0907090b0702130e01140c0a0c0b060d0807081213080702 65
    0x50250809803294002140340c03403503030040000a6600d484140c204000c9044010450315294042d00004d0300c1e2401101501d2031140700a41455195a92801845010402c841c240b02c2d07804141c1d1710035448010002e481d02000c180d4070032629540740040d42441c0e0180314004449060f2112a000b0034515401d100e811420103c030f44052041e8910000389807000c0d90010210400e800480d0440c03242442d0060b41414056003000720000f0070300c02040500ca0b08000c4941e085034000340000744944d01c0c101c081103403c01c00e8024003031051203640001820300d4542c0148040d20300c11415030b07507101d0b1401c00707201030b003007045582d0f400140901c802044560340d43d40044c960740380050690000404403003101400d40d880c1c11030307100050b90345044542326610507218050f0880f13522030f02c0b68941042440000c0400104c0e407000382c004120070000c28031644d10208210205a8003120054841c81e2905042c441500064a0b1100d411414000904550034401050b844244d01100d5a81807108a40920140300003006 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 453724622 1250 453723372 453723419
    0xf08070906170c070816031d100e1207080f06060103051009090501110307051e0913050a0209030a1406071803030807020a0c470706020f040909021f09 66
    0x40ca80100302400d00070100011b000c3d810401c40f107980e243c002c168840083c1b02d8469132100d4041040d4958880c51504960b815a10300703550070139900000140f440000e410f9520a40c070800d000010800340109005100f002484256452941d5800c010340903540103c41c0a00340c0641d240080c02448156403014910900820002626454541490325154402c1d98030310089080425541364050360303441c00c440b103102805000c0b810031001a002c04d110340a07446224800e0f80c1ca8600091202860b9416500003603030060071101c40c3c04080c1080c1c4c0120100180750600b0b4000c504c0040d4003640580342c48200e26440352012445680f0b9600c040703800100150490341180240d00500b80400d4002c94108040c01c0918a841c0c90360000d8203a0b0746162090600e900e500c003655540c079250807080d10403040e9401040c1c0410a903141e4241c030302840244210500e501c803980340480d0105803521141d216840f828400e60f006031380094036104c100000b103980d200c01c800265403610184880c1503500600042c132110340 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 453725872 1250 453724622 453724627
    0x10c030807020307060c090e1b0301060f02100f05240906010309110d03080907080f030702012601120201080f060f0f0f03030309030d0b0d0507060507150c0f08070906170c 75
    0x107a81d40e0703080d9031046e111800001c01e0b440d01402181c81520120b5008500b4811078100c85462820802681c08144907070382c1401210111049664020b02c031504900c038018070104104002400c600b80102021360343e031205410170103000c8540b840300c0710f083c2c0c2d201d110040ca140031560300c400044001e003901000c102c80541d88030541e1109030b16007200486166110783c903059403626010485a1900d9020b0f804203070b90380d02554142c1d014103808401c841c001c580a2034a414508c1d00e144101009010082c00320341d01c103042d18000540002000409079202c0d100740c0c2c9250050b203891007050080c00d81600c2e26503000003482e003100c80307914016a01c10b0b02210b002d881c08501ba5a0507000030704517041122141c8090b0030001e090001c0740d0301d03803043e203e038550b003110a502c000c0b0349070701c1d142c1d0b6900050003a5030901500080c1001804015001d4505a1070488410301460080002c001c00d100883c1c03010b01d0208107490041000d860140104606481c0150f43d11101c02034145a038803607110002c0c100302c0700c0c00c1d800c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 453727122 1250 453725872 453725887
    0x30604020d0507030e16060903060c0921060b100806040905101107020a050a0b0703031a0d080901090504020f09040221091e03042601060906080c01090803040302010c0308070203 78
    0x1e010781c520034103072528009001001340b1103031418180e650034100b980080d44034047c008541c002c68080142c0b90011740c001404039020b103090f1003d00e20f5401c5000201849007042034071031a04c030551748426209610500c000c2210105101301380c0d001c8079603140841d14100004166080513071090003030780d00500c220780c0100c005c2d42210040710498a480400d00c1030000e0040190300303100b00e203c0b00504040c0c1d1040c000c1c510f015042c0c6242c1c01500d40060030181c40b45110890704d00900913000546a0040501d10b0750001880d143d070042d440000c0c40c2c1d02040321311500064615192098541001c00d10360401e24005162040000a60050409581154400c0c8410081031141400180324207141002413401e20b420310040030360803014840303002030340d403081100b48082d0380250200540c0305154100c501102c54504c40c20fa02610040d04552603046c642203000601c401c1c00036076442c0ba00820b0721000c2c0e03281c0c2ca034040d2684a1103035020207804243d560501000191081d10150380c0225144182c9080540 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 453728372 1250 453727122 453727147
    0x712020c1203070507061514010f0e06031603050612070501110102040e090303070210020316110a06140a0606020109020603130218070302120702031603180b041e150203040b03060402 80
    0x403d96040780024004070302841001246d109480d841c08001251134491860940002407040c901e105460401003203c41c0d09024034020010b40c50316540c000d00c0c55403280741101000e0300d801c4800c3c24aa0019003030101090281c10320741501050000c84030040c0550310306110041d1900e001002070502c0e10740d42000700141c400110581c7d0ba00400910024546d2410420f1000b807070008940b4940c0d0801e841001445400045200040400121800e00c9641100500760043c14040c481070301824180c28404501c200d40300c03114030244103101d0945c01f00704103910303480308a003240d12400009403c0301c020404560030b0b0001c801740070b2784288010003c2500d01c20705054004007040598040c000f20f50045902000d07101242e20700c1e039004911788029802c0440f600c2241e036003142078180203400d00195542c0b842c4081030390040f100c041d01140242594a99560280b0a030341d59205d0714441c051036004202141d1401490080b02084403c0d500960616081c82e07491a80b56001030601640203030b0811800c146140c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 453729622 1250 453728372 453728377
    0x1505060403060b030c03070b0304060f0e1027020303030c03060f1806040c050f0d09080d061d09030c0303190f05010303030221060105120402040603020d05060403020f060712020c12 79
    0x40c41030a011450f1403440061524000102003514401e4021080501c0914504000c2d00d52082c1c020002042043c0c003406464010440b8050b10b28560046a000c40c00207111a0824840c680b2401c0084207a00740c4140360800140700340c04000c0d456001000032400098034030b0007468018100524910031403c0400c0001c80030001c1c450514410680f00c000c011003858107104103042c03030b00305040961400d01020700460f401d2150100b034612255860800e28240701404060342d22600f001001042020348460701940b04800701850380002c150004001111500084192541c0e600701030011400c58988104121140c4044c17801c05d401c1030f5541c94040741c01603090103080e001390300070b84005960b800080e4001030070010308208804c10090322818405581d038000103c0c0c3c00c00f0b25100c40c04210f030702d5901c00038000c0c102d917900c00f82d0b0022412160300240000840e10034005d5100381c08a881900806031000c1d21560110b030300d480821580d00b81450360502c0758000b07240400300742041e2824000c0c40c1100e052281c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 453730872 1250 453729622 453729629
    0x6331002060f1312031a04020d020403060b0f01021504030219060b0108280209010318050d170112080d0207060c080718030b0408160f0b0f250315050604 67
    0x5074401c0050101442d401901e041d0816805040d081080d012622862210816401c81c88205035855095800d492401104d5505481c0c00038015591850b1908040c0c0280d04240410345200e40b412680e04513600d05000509102e280603009003503040c160f0880d40d0500a0000c0055040d806102d03c040486101420340800d40761141c203000840d10034000c001824070f40e000700110b09008100c03843c80c002c640b00324900310082e001c40070056900c1e241c03000101c0c0900451031000d100d0312402c1144c10100500482e4640c451000d80c0e8a16540c01158407110140600c203200c1e00f20684140700d00b08010541c414001d0071490181080546032184036030b00c0714115100099900c000820040c00c0c00007040c2c0c0720344400c000c0c03483c00402484250030b6807a0b0080354840540000c04134400064404100a94041000c4866400001004468240b03062070103214800f100c4400d04003041c500050030119034400e100310000440740d0501708200540e40141c0c018a0550341603001035a030104e00196654480d40104081c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 453732122 1250 453730872 453730877
    0xc01090b04120f091a1e03010509060a0b070807170c010b0f15030c0a09051c1505010e19020d1109040e0111190507080304060b090603063310 62
    0x5240c9414403454000034000030070200b02c0110307441c0c03104a81c084c90080c15104010388459031004040b469155611078403408038a40e51082551144424005000d14101d50056480c0c1109a48020403c40071400b2806a0424002c0c1840000301041d1120701610a5070b2190000c8030b01442034944001d00da070804105038555a440304070a4103281000c00340c80c400d04406990050806541d00303204002d0f400024201203410360b0102d08260542d02c1801140c00600014141c2c150200c41c4441ca07169000d000d0a065500b003403000c1c2c14400900d80d07886418102e800c02440c0c2445500c99800ca00c40801030096040c0c200b076024020b1266900c030610400d041c103508401c40f01c0c5e540170786406110039110144860031190345004245c2c2000e511020441d6019482d0f4450000110032420007a20f46000303005028243d91008400c02080101e164403000b0000000c9841441550b549010155074070303401c44056a0480182d01001101c0030700000550300003001031100800140c820020604000f44030070403000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 453733372 1250 453732122 453732143
    0xf0b0901140313030311070c1d1b07080d0e01050114031624050c0d121a130906060302060706050f15010e01202d0a0c0e0403050c0109 59
    0x4560300070305100300066001d00d80600754502094900340e50b03000080c014060640700c0d0141d60008000c481200d08080e1f05c01c4006036041d4940c960840d140d054855280c200c0701c4941c0205005e240a002d000c4c81c3e00740e1002c031481c078040031540c802d1610f4110041c020a841c1e00d620074071192100c2030080394003230301c4078040e8400b0710b80c04e50041500c0c0c502044510782010008013000c3c004054070546c1710f041507894100301c011901894004481c44d11500c51641c0150048081482c416035119007145140042100c041c80309600c1380380420500c54546042c540c0c803451080c54088070313100ca6040f60f0f14160007505c1c000f41031a40ea40108006078000e5034100c0b5115038480820040b010480d2405401c9400080b5003501d0544002c00600061100100360341840006808411101046000004080314805c01d40c0e2500c2c8004005c1c0a080003408011641041f04603010760370100001404a54250008503105940f8035020b040c642142c00075005a0810070304000f407181902c02400798200e1386228070030714207 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 453734622 1250 453733372 453733387
    0x105100e01032c010c14180d050d1701051e010e04060b121e0103030509060d0b031608010e0f070b071a19050c070b070f020f071706180d0f090f0b 64
    0x1400c540911685c2014042000180d0103128000019210b5004070300d5484009446d400c400103c4070550004000d0491181308241182d06601c12144002030401a4103a451030341c0343c800300482e01c80c41c0000042c40080c2113603004015880341070b404802d0f0401070800503199407070b03401e0482c0329440031140140c0ca01c6003405110300c01e009a03895001d21541003208104d95411603078001c2180c450038229620030400452640500901580080f110030402011a05c103403c1ca0044400f0940203841907103580d51810104038017030000130603030103a0024000d000d42f00071030a00300a403815411507141036550211100c0c199035220521068140107007441040c140c454a8601038142c1507580c000c1c18210722000610403007000031a9814150b4124603d400c1c8050854403000e4124078002904000e90303464403030000b0014138030003004001d210340d10551042d50b09540ea0007440300d14045103540d0081059110560004150f0320840c20410703000802d1a02e10702003039440820740c0b01d211903a000814850b000081c400e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 453735872 1250 453734622 453734711
    0x1c180b1b0c0603040b070504180905010f0b100c05070b0f250b06060c1203150a050406050a1e081e0118080313020111030d0c02150105100e0103 63
    0x8464806500c0c00814140d4000408103025002c040c0c40108041402d00104820601500590700641805130340d140b00542948441c0d005451400c074103403525481c2c507081031603c007298050380b00120409815015201110344040301d44650f01c2c40240c0c0c0d240070f41d450201c0d07100f0509000304495400d00c808592111070782c074181442249051820b00304400036004600c0001c281000b056400602200e0076616441d070303100114206141070440f030880c2040001002a200990311070310100620545440d440e07241c5510601003103c1c114003c81d64040c0d00b4180c2009017848a400503116010070b809030202c803980d2101d0103031506007203019211106c100d0400d80008081e09224a0803403000304a0408400300160f211003240e0321001c0c0c0710080c8810003a10400569000d94244a115568481125a41c11301d0310604402000c1c0348003e20300501484800f03212680400314441d068590041607100d40100f4020107640c0186c007039030b40da0305058542c2401c1e1030f48005880c600b01000c1c2101e440b40464119008030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 453737122 1250 453735872 453735907
    0x9030706090e0907060e0d0201110610230a12150e03030f0c161721060a0f06081518090708070b040311040b010c0c0f06120e1c180b 58
    0x26102d140c0c80081304115003640f1045c80a0414030548244000314554001203400c0c07100d0826414561148105004e0f6000e0141c100c5411182d40164240015104014140105140c4081c0f0359100c02c2103441801f03104000b40ba00c1003032510070003061540528490b010000d0301c4032261160410342003c402c011000d00c2074031903240c1c05036114140d107280030300350120260b4007204c422015200c120440d58240850b5404000ca4882c5564854080c225000442d000050008120750041c019080c002d00000d4208410061800381c0d207054444020310b5403940c006c0c0d0520b45034a905c05900103891000410108826200f65010724868005882c0d020f081c91707031032072420142c2d03442444900b40c10081007000c280380e03180c2c8800c1540704850126121500d4801244c0207005000064284c2043c1140062075140c403c0a21046a41584480c00b1300c0070294080b604603049125010900d4000540801400462030079521400010b0b040812820703040b1a04265044001d400000071800002001c0c155100070030003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 453738372 1250 453737122 453737131
    0xf03020c0613080c190c08060606030c03060406120302010b040c0807021009060e06011e08070b04090b010909020c0c030c0306070207181b05030f060405040209010b090609030706090e 80
    0x141589058480961180c1e600e030002e0114a51401c09655401008460700441d00c92207015001c4031003030182d207191251341c940800d100310350061010b000080c4200000c10958420035000341640c0c11903403980b080c01259480240f102e03034040e1341d0b09804180450b400b501100c02600030b03070001030018994020702080f1203844440f001804800003c200900394000740710040800800c6011540240d14500074001d041300340c090120074041d020020658282001c2c0c04802c0d40142a400b0032156500e420036600c035109401120072000040005021051064018200100d01850407890041d03560154908a800860340007200d07401a9610380c030289010401c400c507000044024166506042c00043cad9180780602c241507075841d108140c9030303860096030f0084000c10f1005122654081c2484002402548103e5152480c4020b142c0850141d0910344511403143d0b40c0904007102d00c1c0d080c0007502604c0d40101c00360580c401070810803a030f40e82d181440180002d1031f064869841807030602c1c2904503002c03c01031 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 453739622 1250 453738372 453738377
    0xf0c080106182601090c0e061513031e02090c0309010c02010b130507090807030f060507020606241b15070f051e0403081306021204052206080a050d0f 66
    0x1c043c04010600110098034000d082c60140c40c9150240105015194544010305408080d9078001117070707002c8044007840350308125a0204d22403070b1114624924000c00244052a511001090002424000241030300e007218031003003203040d4099400200c40d9030b01142d80d600888004018881200800d000d00902040e40b8002800031007440341c01710b5406c0780004800d1310074540700e00108188500941c1080c02030b005100a44061548a05203210f91444481d07003280c80798500000104902c0c404648580070303050041c01c2c13075907004003003480e040da554004c1002203101c24200300100740a001e03007030700d2174030911804041c041103d140300110b10443c20007010403050010101d0303d45100b03584802180d00c20070001001c000718140c03484014034a030183c1e410092101400243d01100400e40302024003c0b81c44c25421140c02040000c1e8200250085101349508400a0b00c15102218036070285200130f400d400340700165142d03171080c035503207004004481911241c004054240c46654403425801c4042520b0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 453740872 1250 453739622 453739667
    0x27040b0f0913061b030b0108060915120c0d05011e050c0d020c0c060d0b040e07081506130603031e14040b0a112e11030105010c060f0c080106 62
    0xc1000c24104900105041452103140e001c400c01c01485130f000c0f540f0480c0441d0001885a090200a0000c04100100c9070200302d500307001446c80d1609d0000107204061183c107480c40d5003ca0ba06110400d0380c04003023503506003e0300048900a40b50180c0e02051940208004105800c0d444000307a20541115401d0784204e04100401c420451410115013180101000051344c07400443c81c91403c0c00c65100c903042d80076100140c503400030809900035011a07802200d0401244d00200d282503a80c070003600c0303440880d41260350340038030400e020220b00c0d42c407c0c40034100c0d003107509044240804407801d0303070070450101e81e034103008e907861003e280c3c403514501a031400c00886100c40b85141d6819405a442845085180001c400c07003014856040c903145100c40e80121344202d410080403800340100d150220702d000c81104825a406e0855004050115400702515441c60342814011036000410301d0050f0313115520f484003440111001d00c81c5000ca007440e030780c2b40811541840030042142c84039500441c050100e4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 453742122 1250 453740872 453740899
    0x3030e030307050316030f0c030203060405091f0c020a020a060302130806060105040b0c15010e09100216020f0a150503010501030507110d0509011803080304060509191727040b 77
    0x200f801c413500108000d810b09646030803407200703d000e00390702262080998185038200790040d42603006507004110441e42404203503126501c40c1c1e510301200072404200c4d1012034601c104034407503a011401e41120303441174400f1110a5004188591520344c080c50000340c0c0040c00444901b500c0f0111805094440e004d0f141c103051480008002d0b000702d0081c141c4001e000174044201c00c008105801410f001c0803101495580d40341b10021a42404441c030f407801e170207043c603444017002007482112800f240390300c101c003034400c071030703002c1c081e810540350102c3d50842801034000c20164035101c90121420255a2050703070f25070515000400341e0f0300142c03080e02400451000651059400301c0c6420080c03159107042a1201840c000407101072162051301ca41032903030860040107000c480f90045110b5400780e40d0500850b00c03014403030b5689a514a9420703007840660f2003070000107210b11042101c61200c00c1c0010f402c2220700041039600d21281c049000b4547c10580954500d810a4010828032420480d00764a08120 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 453743372 1250 453742122 453742127
    0x31a091515010f0e0405041406010b070305120a1d0d14040803070605060a0504090b01231c0813060206060109090509030d0e010905030c1b0603012706030501150303030e030307 77
    0x9030381c4601d0b0500010581d04243c0c28400c03d000d0041c59002007090000341000d08040707843c20540c0414407443d010b00300000c114070780283c00f281c44644d4140d850901c0e1600030009608502805003e082003103445107040302e07105d03c01081070500c852043e4003410202d680d809000c0c103900c40c02d0000c03100c540790600c0704000d0610b01005841e00d45800c900c0105403517071080e000071480640c40d009240c1c000d203480030000900c40d080304807a051720a032100324084d050030082c418494910f074a0515510030341c10300e07240c01c00e41c1d000d10081d07414174410100103041c090100844448114680c02ca2801030b40030404202141d82c0c0300c2090350080054050400c41c6080401c0001d4403481952550710805884500008003840c09600040c9040c0c0c1110650303894a1a10074656150041c40840740034050480035207071f18516002d01224101c41d5651070f0705c6000d8102e5103014155900c01a407800410f0340c2c40100201260f0203001d20b000c4ec846480001c0102406d41c517019003124900702c1004075650060040051068 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 453744622 1250 453743372 453743401
    0x31b0501091404090201110303010f0e090615010c0503090a091a011d011b02030703030302270109051c0f06020a141201140d081201030c051e040b030304031a0915 71
    0x302c1500d002c20105918001070b5002100c4040401251200000014035440c0e440107800549054000e0780301c56480d80301a45641e054160f0ba906110000d030420552203600601c1c000c0e510074442d0003500d05003001500000c2111445500c810390701e0340c50300c0341d2610030084480344e1215003109081441c0c1312505524403588125800c0c10940c14801c0c0800914409511050361a84882c1d0040c1110501911392078020040e402000480c0344200904800301e804100c1c0070f0682071807103010394038000d11603d0304040041c400c9a110f420b40c411886403c813000825400d0301030400c01340c040c42001d070396031080c45002007082505655010700000c1c00d201140c40c15049615050458281c03200c0c00c144000d64400151419112000042150f100080c07001040240420403604980c007d4480c851110f80d5801030200f180d14605500250341141261420f035481c05500444410728040e046034101038607030ba200b00e406858211980900b24822080114174042044ad001400001d0081002c0d60308041c4006110039 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 453745872 1250 453744622 453744659
    0x51e010b01030c1701170705150406020114011d0c04170a0308130b01180b12010903020d081e15060406020c041a060a050a030b0918010c03020a050405040e010b0a031b050109 76
    0x411b001c1c10149072401003140b5000b81c2001051a07a041e1030307a004050780e0381d103e441420095424071b10400048410140c50604030380b04940f6141c0240c0c68811007202d00b0a0082c41c0d2084400b0501011541c0d602d0314181a03070b407010240007085014254240a0f000328402030107450303c042e400310688001550190300e1811100c0440c0a04591f40103100ca1001521380c448940e50007104da166121002101508010395842c066026920509181482140c0c151011104a02c0c41c40a0301c41405002c03000d106c0305540038078000d01584080e400c280014005603c55842900141e104401405d06450644a4070402c2c044000d820001052020301003001d42c080d8181c01018810040307049144a4020340190320703105e07401416030560346042200d442c0c0a082080c10110203620302101c8c4c80200e0300030b108480c0031b60040d85416091615020400020700314869a4a813295210590841641c6451080a01440c424003031510310324402c081c040d403042c00d2944101c1c104030001d0f804011888244c0c501c0c5400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 453747122 1250 453745872 453745889
    0x90304140301110309070e06090f04110112021308010e0a021810030f03120c03051b0d060803030c03061503012715031b050a03050c060304051e010b01030c1701 70
    0x40c40014002801484210a0f40128840c004204500303e032000c00d00700309403583c080751035055440e02c41c1401001d410445081d00303e2400750010401041296008000310081450040a004410303504181030f60400e15458420300070400c03080c41000428050001d07102e240200404175203078603800003030204011200b41c042007014440443c00c00d10580035218042e640041034441f11071640c0c500144403120042c0c4881440c0d04d030400c500401c0c1e1081c02030a0089100107003491111064a4900c001039010302030540342203542d03030300000d00c000d014409540f062514050b02a00c92502c4014031840c5900c89900101400d0b0403c01032200c08070000c082401c91a04c000c0b4004e20041603c49a0010000c540e41001d0300002c041d000010040303600e003c0c8070010352025118440556620901c4044050b5000007001078000203119495420322401035603006008104440b01d6007021111800703030900041d503606499454401c1c1011a5802d03015211180384107151180c4c083d014400c803603030240c5060017030411 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 453748372 1250 453747122 453747149
    0x260316030519060303090617060306040b1302040603060b090105060301180213031b03020a09060806040b0717090f06071b02010e040f1805060105060408120c0a1e1406090304 76
    0x76000c1406100c2c080381c0e00051007008956100c0c10f024000000c02e1185000154400340711203c0080e040c41824000c07400034000741026207403a030303940d90144030050a4500580c0c1d00203400c00565154040d200041d40070340b4001410b4600c6105101140340140c04c0316004520400040001d45d0807044a840500300035080143ca0b40800f4804000340b41c3e05d0f50018203804803806c081c44601d041c0c55400380444c0e100b00c842c00c2045039250104801e49160f03100b00c100c01e8000400040100d4a085105580401d1924040740f0110181000d01141030090f14072001d030303500038081d521164200b000466000613082c100042988032890003c50b2010701c1e5a03000b810402c0300740c060502c64a60741c000312109494110309014961000702c000c20007015140058800303101e0341c000016a4200741c0229001da98501c1d01a0040c024500ba403003020364040c80000c040da10400d001c50b40402d0300e010124004030307040b940040300d580c2e20b800e05402c03240c9074071990711031354008406000140c240082200c0c1110034100c540d09 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 453749622 1250 453748372 453748381
    0xd021504050a0209090102090a0f0501120914060c04090f14010312090e0a02071e0b010b0f04030804150e0f030d030f020405030d0f091d01030605040510092603160305 73
    0xb414102600c0000b50083e450300144020000e06401038000c4100603900100410b5591200301d40d545454031815010806602c410f440702c9641d83c1040c0c9416001e036600360540d421508000e031402e081280c1c4c1503020030740030800340a4404180201e6411070400b01d0300340b01d0704442e0b203c100d601d024180700003031280707002c44c0040050360300404a0308020b100d500d51038900303443d2101144000e0342c400c100c11210b400000790101c1c8103568408518200301c2d00a10740003016801c04604c50202e0340324940c404c001003014030000000407403840042020b090844028440f0007403540000d00007103008100305114046070060700249072000504442c4001c0e061802186456074414100028812030300a15054040d000c441c0181c960030600c01047d50712a9a100c0740c800c2c0d51042c2c8200000700c4610703840c0344020024010801301d03449030800c1d6001806107082e84c0d40d1168a900710800c80d150702c1e50403542e903482500d03c40f01455203e00d10703403009510305016515602c0c140c1c0c0480d84410312a8209400c0c55608c10206 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 453750872 1250 453749622 453749633
    0xe0a0b0d060905070630021e0403050307150227040e16062303131425050d0305030c0d1508030c1b01020d030f150b0706050105030d021504 61
    0xc40ca0329810080411050310a4148103442c0d0445005590100d00381c1704442e00b1030400407004041c1d808881605903241041c4441c100b01a61020000c0c0c5541c070100c94a007440c0d000000c001300019032050004640d10300c40c41c5030020840d00068420096984184041c1d1503d01d20040416150450f607200030389144403140024004188400045885114690500c480aa0002d0500c2c0640e15503454581c3c0142070b480004210203c0c0c8404001c1c0c8140510105c1c1c03240c0750b5070b141055101c0c851541c0b0307070302d4984400440c0c0c5030a0365400386c131300d503030b00800b80d00c180c40f0b0b000030300301e0020b044261504581070707155880c05000b070700c80a03119190100c0001036152102c00d44d580000d801c1401402d58051880e40d5090080e682e4020260000c518080c0300550b501603030104844061000040c0c0141c0b000103404a026001031441c4124550100c0c0c840b0001c0e80421018a1038030b014000b0261070a07114102402d040c002c88605070402d40c026808003450400700c9030001060003440700341e400420b00f9565646800d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 453752122 1250 453750872 453750889
    0xc03030f04150207031218021005070303060b0307030504030e060309070323070b1c0b090604050907150201020d05010807030f0b0c090411030f0f01060f181205010b13060e0a0b 77
    0x49092180f0101c0c80004045e406410365140b19640d60040c0110403182000040b860500c160080d4802524000407003c0750044000d4810f0a010b4100000c03d40d64900026480c0e80c803c44080c80001e9689080104040c1c11840c000382110090b41e0650841c50b021070074594420b0f1501015015682c0c04c40380030714012680c070080a0105083d815102000e0f80c0f82884100c580241c010403252010305141444103e2891151041442d402014a0851386481c0c0500004100c050100301c0c5178054180c0225105465810140364040b556000507561002c2552a10455106070004102a084003400304040350904003e00b0466802000b803600320f8403801c40050840c4034804070720790403508050501e40600ba6602c0910710401c68415800415035543c0075109501c4024020840070511691021502511404400341841d4010301090220354481c5035480c0c054011000450f41c5a45408400000c1d09249203140e0404061758018010641000c450b4200002c0c001e0820140b9903503030301c04414558600c0300 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 453753372 1250 453752122 453752153
    0x141624080a150801060e040b0c030402090a0b190305061803190e012303010e161e1b0503181c0209070c1b030209011401080a0b0312030117060703020c03030f04 70
    0x2044111b80d50360070f5145000c022038080e40d11110500001c1d4000089108a0b0302c1150f0044c00914156134800030140100302400585401007003052202160240c000c2c00c401c040c50054001381080d1034255001004817089030024840d40e0414007101d004040d0050420501e55440d0400d00001c06040d00121524580e10f14010b112082200c43c2d600131040a9000b94183d420030368948403580d9564540180c035075265400400019001784114104100c8010001d0580c9034916100c1e04003505420000710111004809030b0b1540c000181d0310714443c0c25120524141c19095611004a200c1846106004503842070003030b001c2c40000380040c00c0340780714017a8040610360000704402801448015051181791502040780500c000760008124401ea018030f4100c002e0b0141d480050a6440303010000c0a064001c9581740c041c81102030403030f03001420202444c040e000900f6030101a01c00701c1d0380e0380d00e040009400c079001d1500c100801d1a42800110850f5032101c1d80d00302600d89500c403850074a200c01362403072 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 453754622 1250 453753372 453753389
    0x6040501320f07051c08040311011d060613050c030408130b0a17011a0d0905010e030705030307030c05030f070f0908100c030b041512141624080a15 65
    0x85030304001815a000d00b01d690700500031140e00d8017036000302d00c000e03100000c10180803070145000500001e220704a958102c42407032001185080342c0d0b8050103100c0503400c0615051b034100f00100107450400640c43c0c0070003401403100384100c1c100100c407081c6034070000e0005441c90300d00045540b14200d11100c00c000800300c606401d96211074501d80204881c040c10400703260700c072440e8000600801c01030880d400d6951001d480e107213440f000307000700001402c510f0402c070343d55501c4240300d5507440d2040c4040c0c003109001c1c0004c4c565a07d0801c900030100c0301080d0300042840390500a01c0000da0841c05a03581c800c0e400d0402c0000d46c44600d00941e50b20360190f01162040c414204020520780304d9801401942c50340340c0301801901c0220302000181c890b24048803120f410f49480400401c00c205c00305c6890306008a4042603496490346210f030a0400c400969140401c440d0300c1002074041d800401c10900240f034240300e0b598400e09100403c5000d003d450140351a1b10f4880b210900072806120100810b05074 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 453755872 1250 453754622 453754627
    0x50307030905160503060a050c03180c0312130806011211030115060909060b070f0f0816060209090606132303030705060f1b04120c171b0604050132 65
    0xf04140d815820342401030324081e00405001c600c410985010b01e60040300090f80d070a08650350822003408504030340d401102c1901c148410000f080d107083c4402c80c03902c2d00000d6200d40d40e000b001107141c41000c161b449402607611600041107483c5c03a90110483d03507a4080340c0b07800c42c082c03a00c0001e805061084111030006001400004080d5000346250b030455081117000d020080da41c0d00407410f240075030003000d040c58445008034000180600e00069845101d43e07815401c021142c06600d0030500084011103580303600040c1c881503850f0800340690f11180407155280380103141141411010300e5849450b095045181201d81e0008503d401c540b07030070b00040c08890b15200e090401c10740d18942075480403012a41507010500030348200403441801c5504000552501e41740044056022000c1502a62071012600300840e0082c5040b040e84081100a002000001c00c0640030329200502d02075094407516040100b004242d800c00c0030a1032034030282240070f10010300780245141320202d05c0750320008030000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 453757122 1250 453755872 453755893
    0x4020c010f090309060201090507120614010b040e1506120406060909060b150702012c0414040b01090506030a020d020f030a030c0b0915150f0901080102040306051e0106050307030905 80
    0x22a40b00c1000140a42e40d9983da803990b80e001603080301c90401c4094035540004a0a00071003016400b10010b90788900400545590300315807144198100780c10132501c442c40043c00b00704125440340c0c0c60741c100d4071003500c0009a02001d07002030081c0c1710711444007001d1241100003805006090784940d000b0f056180d400d000c0b440d05860301800819510300da10b8030452007401855519804031042c0c1e80b4180d4117840302d032034000300303c0170380d50140400610a0402c2801c05003044840d0b20350380103400c0842c0c0a080b210010b81040d2502d102020016004210518035040811005a4000030301103012a01a1802000e003805070001c40c0385200303284e0066805100e4402417000705988034808242e0503005000540702c1d0b13151021502e4450f034058106465129580c2c01013001003c124040e1505070703100910742e404180801011580340c1c9401d9201081603540480d02f0010b0100030f01450f40c0c441c01d40d40420b50300f902d001c6d01ea00c155100c180180b000f006004800605002d01992180072065013210480300103091 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 453758372 1250 453757122 453757151
    0x120703033803060f0103030512130804030b0103120f0230181002010912030c02030d050c0301050321030f06120703061d030306090105011245031205040204020c01 71
    0x50075101d070203849500d00180801c4040349046040c2c81c0d151703403a40d1508200b20b11f40c005442c0701801265124040d01d801100007920000140300031403050034440e41a6246050440e454810800c244003030018000b0503000160b40440da5403000c80344c070171000c58000701503a20b10220a17130030040340300111000200c0304548c03c0030b104142421a002c4901c1040900e24003822426500e45110050541e0083c03002142c01500039000000821000e204683c10001400303211415148155510300325090000014040ba003010720810301000000003c80300c0b19050301030501841d1100074494100d481c13481b03020580725a12803002e054810341110071039040c0d580303a082000042c000e00302c4003800085046003000c0703881004015a84145002849003540e607181c04010740c0c4048504a521400c19aa0000b0038113040035220342c00501c0b111081e540c099030301c010000c2c400340c0e0314910400c423507414401c41180c0069030010041c1c852801c3c90b400410b4644552000c100039010b6007403005080d501302804ea4281c0c4c0d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 453759622 1250 453758372 453758471
    0x106090f0603050120070b071e0e09090d0203070b0604110a09080601090b0f01031a061201050f01092303120a02030735030c0903071509060212070303 66
    0xa0080c1e008000341c040005c3d10101c03266400600c035040714000c1c000400407500c0311008650003406400c10b0600e200c1610420107444209800803000318545c00502c00c1c8505205031180d501402e00e00040071508083e540103903aa0186a00050241c0140da00150950300d03290068036100d82040c0500380c0b40e003001e00e07000d070111040e401134a00a108003c000540c1c510203000c1d207186d0318005440c04921041d10f40045000d003010070845001403004c802c41220540302d280c010800c00304415136405031541000100075008c0c0000c0c600b1030400072091b500b800b906890781d0b81c0c3d9250103542d40305001c0840302c000100c0d040c258003c4000442c1d240c00f14044c507041c0c2d00032004141d240d12903000502c5400480c450030302c00c1100c04c914081490040d8800b09440c4a2207002103411074114008241004620030019140200702e802c15445103045458281c2040d07040000d03c0050710060001c3c1c44507010300d40080c4c030a07000711701d800b07010180c4a1003062040c035281181400c00b007038104035022101c07104040164050 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 453760872 1250 453759622 453759629
    0x9090f06060303040b0f030402010e150903010e120301230405010303090e18030901260a06052b12050c06070203041404051003030c05120a020c010e0d050a02060a020106090f06 77
    0x18094480001c50078035003c0300302c0e8243d940e038501060410002c45241545500000c100700d0501155421038081680e40e80c01c1100700c0c2244080140d80d5464000c10b05d801e641d04503c00840a50210860008000c24601130703e06403600003004201c0c64040c04c244031205440460001e800516050001c03050641c0194085c043d50903c48000c109500d032800c0400300000800c05c0b0912a81007440940141d6100d2840c441d2100f4081c5c42c04200210204002c104a460640d071480009030b480c030702001a03041060080b80c0101660040c1040c11003502d000301803900701079400400741ca0f900b106c0c8006c1c5031700603400e68002644c410100c031094a002c1d00e001e9500da10a020701c101607841d96041c111180351900410f48209180d0740039416051550ba002c1d280315062010440d6140100b1000300d84003124480a0400c1052950040408841040c0090110350100358810302840302c40e901d183c041080000d840e1216030b41901da0998035009004120f004240701e4114090301400c05901c015091011340016080c0d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 453762122 1250 453760872 453760903
    0xe190302070e010e04030206010b030603031b10140910020702131419020c10020c0a05060901140114030309010c061d03031009020306010207091a040203040303051f080a0f0f020909 79
    0xb030340d0b02c41d103920102c0e01c001c880c01401a400381005202c0d5900c98006150041d00140459041401c034000c1041c0001c056080c6400507070180d03a450303060030164042d1194082c0300815401290800582c0a510740c0710740c0304006001e54001405078110b4440a06800003008a18001c104505c00303c401c8200498068500302c0c4000c81c90a115010601c1c0761084407003603000b0b40c005204002c0340e40f50150207900701414101207806240755050109006000301032007100001c00005544449548844400700181c0007410b00404840c9500b103240c80c00800c41d051140c09003013040019000b86030400c064040c00840ba060036034500d24007503080318000090b600550184070100465900ca408100803030204484190040c1d0100b00b0412510303560b40e01156090080c10500d8010075101d07400314083c3c5e4425501200000c0e511401c029001207440c2d13103407110f50b0307840c0520103840e071624110a9881d00028405030004050072141410031440c00c56181c04194080c20180c01071500c40d810036140c2c1580112a1740 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 453763372 1250 453762122 453762149
    0xd0b0a0b0f0a09060201021602090c0c03040303230906070b18070906030201110102160206031f0b030702150106140c030d05070206040201020f15070c110d080c1005060d060e19030207 80
    0x30b44d18010700035105651f82c402100520b0705020780809c015007202405082140350308201002410303409100800185010340c0310f085408011a0000a41c56406c0780c407a4400d86040c440301c1c81c0d59581600300c07501c0a401080d800c155842e040c50000301071010021208440c81303050400204640a6000081140e0003601d40094001c2071000d0b4034283d1103000c0700c00d09260040a440e50052810074013942d0031650340110401030060100c85c102814695800a020750300010041110b0154100400c0c5a0011407055000e06945800c6018210400006030b12034011404120703620035000400c150340441c1000c60043c00341c1d00b841100a074a8000581d026801801f07100b0035405890000500810281c0204140403075a03502c000084030361a4031280100d8401d555515a07808a40d104039900021b68040e0540b60b56864200041c0343c6824500d03401e820003507082c07d0402010741c1d107039004044410b070050408038500380300050940c00d02d544041d0b42c40000201300410320070f0550000b207400c191030742160903d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 453764622 1250 453763372 453763379
    0x14010f050304080a051e03010303020c0f0612010506030c0f030c071707080313030c1b150e0d02040e010605090f1605160f030908030a1206050d080d0b0a0b0f0a09 71
    0x21001d1004880c0a030070004100020102d00784a6002051890040150074001249480d2058050341c004e038025001030b4002c0d21640050b1074808000f0090840c200c9080303283c24075118051500003014801c9920401c008000a4003030b219135400c0f01da001002507141d41d92840c14000104807500010f606840c0890380e41440030b0340710482d83c00c540b0126000495a4190754403069080091080c13072004070100314802c0c00031340004040d00b0842500c50113540c100d004003802c108190744100c05810b00d00d0304204001401494a071200d0303003041150b40d01070b10f01040b450300348004140581380301d500c4950010055810014900a0503180c203000c0d0000040c02801c90080c00c008407424021045d00e000b201580900180005402010b00756010344a4200f041102c0d0383c800c40c030390860700002a040c020443c0d80d10104541c003024401d10014110440b2803d40c28015900c414515004980601c101c0c40d64600281c0f980e80d5503d8600c50041c541440425681c0c8850807072098103070040144000443c82450021 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 453765872 1250 453764622 453764627
    0xa0b040b0d1713240516030c0807170304031202030601270b16020108090d020604020910080109082206140a110604050705190b121f14010f 61
    0x14801990092015201125980780c820315200d0320381050060340c0041000851000701804218010f003400120102e6038800c590319081100c400860000822030204149201c985980c1140c6c0652601440c007400707601414909030080384100080504904c0300b03d40c095209411810055221318032a640b0620a006402c008100740d000694000d404a0400b500300a00c240441c2490402e01c6640072155001d16601c4001c54110f61200008000d401c0d4512070640a40d600218081e07080b400c480c008102d600d1043c0c000030345450001d80020300c41c0c840c01011450240ca004110005085541e00801c1124400d04c1c22643c0341d4407011000c140701010100d00849980424080d0080311466101c00d681441900c00d10001a03008034950403e2108030b82c0610701c80700c81040b540744280c0c410707401070081d01d0170201045250300741081a11400403c2000034000c28044c0f5040d10302070014808a48101e4440c081c4800c0380d290315010b10018051185800940d0b410000e8035183c400e1000c0c0c8601c17002250303c0340304 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 453767122 1250 453765872 453765881
    0xf131710060605120c190224010b19020a140703140609060705211305010b1e0607030c1505040c050609030c0d0501060e010e040501050c07030c061a0a08060a0b04 71
    0x544010810510205010442c2c401c00c0e19449500d405c0355510302040345448a1007204001551401a842507103000c2c0d0083e10051280d10380754001c840d0096039854a000108180700322498100310000c10002c00603a40c0c001c1003c00d0301154080340710502e45041c60501692031049100c1030350150070300395005408010204501e0f0017100390b01c0150103269a0b440050780d1681c04284242c8050020b500c02c580e144c48841500d501804201e144202d8107d19400c1150a403101c1c035507190b10420041400d01c0c0440b0020001d0b000000e425114a034680d52981000d80b0844903507000170700044d00041c014150400706902c050302c128801c21145421a8940c41405101d00601a81d1600740d0b11079801d840c103901d082c0702143c2a01d445500049401034980414038604a001c0e803201d0301e944c603940d0034401008002e000781c0c1c1d4070034030141900342010150344004226249098024200940d1440c000442e0b074400500d48005400280c51401900c1e611000241d5800301160307010b991a06c0c00340000c5251a02e03004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 453768372 1250 453767122 453767129
    0x3010303020a020d17040f050a08030901051605120d2f0f031b13080f0102090f060a020f03031e0121120c0609060501140405010806010b0f13171006 65
    0x405501030039609110300b4883d07005041d00c2c034582c04001d0010940200001300081c00c7e100e1400c181243ca08400d014008a6a40084070540c005000d10f40b404d076409015940300850760840d8542200a5060007400c4c40c10540321b21a03407080001e0107407030203182900054480b5080c0e003011031014200c0074440702071000d100060024280100718048055000f8030107160052440701c2480b00090700200c0d00c0d0b00342d81c005207020031000854001000102e20910404201c041180029440c14a105001800304444200040c9c8250760100d50000d07218030821000c10880108000c50381d403400d003500810a218046504010001625400030401140e04d012001101c1c480d42e000303030700d0349486640c1d40000d4941402540c1c108600c841c0b001c000303d00c043c054815080d010b0702c0b0006035541010780801c134007014181120f0180f814007004100e6200001204d80c11118103071813254446085a40f03907100351081d803400c007654450249010464903d42101c3c6d581141070724044591102e030761125903083c0ea07154030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 453769622 1250 453768372 453768377
    0x902031006080906040b180313031b080c130903020102130308030603010e120702010806010c05070b04150305100b0310030c0b030610260c0d0c03050723180406053303010303 76
    0x380487c8122a24400c40e0511000110580f82807036801102251120100c0e8030903244100000c8880814517810070101000d01429409800340d0049180490400b4110b0a0108111541c2d82d4100302071610030743c140c41c0031700c0300c4280e01000c241c0d47e4101140950001c1d11943d00c81e5190203011000e142c2d0007c1e80400341d0200c140384500700a0b1a800556001000400c03160501040d082e5001c0000d50500a50025240c42d110b41c2c0c0e2101e0400e591800c846092540010502d8a00b81c140124220541344400480c0c154904c01d650325074034000e580611507003680c0f004140c8a964000411603450300b00142d481104162040749056a1410003240e2240361401a034449001404850380003642c4206c055a1003902e2010a03464040c0300c007000b00403141d01e80041c0000035900c1c000d00000a0f070110362509554142034a00c898080b6011821074688035030a14881030ba801d4086280c45d80c1c48075000b000003010028900050001d900c803604041603071544031100c5011074007800c1106d0007140d806907810389416030f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 453770872 1250 453769622 453769643
    0x1d011e050321040302060d02030708060d0206030f0a02040b0d0905160e13050a020d0f0507050609010906030e0f0d021b090f0a0f092102070e0405120f04090203100608090604 76
    0x74200600b802c1c1c00140c01c42810303a010880840942c590f080140030200e10428010307981d05d401400144a900c0c0a01030900c01c0c2c1c080024280076076160340c01d03aa088250855a000a80c887c00030b640c00a10a962004104510100304035a0b040010b81c015020240030b0001e56002c00030100800c224844075000d40a01d14149101151b004024882d8040820b8400c1c1d0440780c55a00701d800054445903950800c50361600c1c00f40349102080418040d1000600e002d4941500b072452610011b85840d070540a00302c00c255687c000000400d20401c0174506040841c0107039405075036044c500948800071941441410441325031404c0150038841e10461040c128010141c0380c0b6112401c0703d0340502a10640c604e40c80c1e49500b00c0c100450070a4840303804844004084803002d11000001030705000c0e0070b51000800750465001c1002003200440e890f406c401c00300300c542e07641e14841001d24106000355041400094400b008010403402c08100c4442551010344891f441d41da03c004d02c4517903600c0215402020312050 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 453772122 1250 453770872 453770893
    0x1091712150307120303110423010e03031b120406090f2306030402030c0a0e07030c1409040c05040b0a02010c0905060a0e060f04030f0f060c02060114010f05041d011e0503 75
    0x8802903007421070702c82d02d00420a40051f2032804001d80054211148a100d0010026512003000c0880b20b2002c8082c00d00c4100e48080c540000e44070b004901c0751a0207080128005400c0b000c041c009009e41d0b00c45110555156916000020010b41d480d0141d200c090070000c50200d58001e49501103580b03c07400d140e040328016004c0c1d0034810547c0000e00102d825114040416903503545031080140500600700c140e009a10300058010281c0b101000c06600b4405409840c1c01c070180810101d80c00040299400b042603816180c04507400d1090f903001501440c00403034280d125a5064224402e81d100d01e80d10140f890b03407620f0400100744607031042c14000c20709100368507a15060a2000c0c0103100002d112503070500707076261581c542454414a048418a5003c031800c8200f1040780301e0180c0100c1684010802981880c1c1c2c0c482e40e004004140b28140101942113582040c890805c640281c586008082d0003410324842c0c40314000d0080c062610003000c20300c8100b840d00181d0060f0011540d0040042504048 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 453773372 1250 453772122 453772139
    0x702190f0605130905090c04051617070e09070f03051b03070806150711040f090b070305061c0515070302180d0204091b031106092101091712150307 65
    0x4460301800e51030140c0c0500050030004c2c1c2c8141c0b0301c60328a15000d400c0250150007000100c030002000300c50710009148940c040103030300c2076a003002c507044000c2852807611000410303644440446641d0750b00c408800f00308041290300400900794043d003034400b03100c16143e410a25007205680c901101c6846010310010709114410f00c80c154000780c01400040b1080c468010607001da0b40f014005464620048940c100181054860704840d52109a82048410310980e20031144a801422000c1056103440208459275074200b0520002e00590300452150348007840e1144d16030740300c0203074002c50403854000a0300d5240603008a0b020002291242c8040d40101400c100f814007407064241d8101d0303074522810b0000b60b05120064524120807282c2001240b852803c0c84032074084c645400c6c060001071240d542d9070340710310031401e1401c111110801d00d454050301c01d13070f80101001e41d0041c2074031580514030045a90f048006140100c8401c022440c030340c0d208001d4008410b8262211b5801d41c0c05550200400c82 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 453774622 1250 453773372 453773377
    0x171501050d062412030908011808071104051e060f0906040e0a05010218130e0a06020d1b05181207290a18060c030206040303150e0a020702190f0605 65
    0x390300c031145000300010f02500301c4032000702d07804c24080c1d40c0d840c00c00e00c1c081c5034110001c80300403c0e449000348807400305a030386000e01100440f0010082c00e00440c80504101440307051002900000d4020002c40ca080448425008840c1445d40f04121348d41001c103e82e8103080314142240c0d00e000d80300c0303582c07600c0328801c0c04000d00c410380b07400481d4025048000c0006000380010035281c0b032100380c1d10b19000c10700d00402003034002400100480b00d02d441804a0810000b05a81f92038542043c2c0c0141c4641c2d000c103821001d00320400e03051000c06109000725268030f4000018000b503441d55683d69200c400c1c40410700ca943c090749400c500040d4031a2a080042d808034507207610310071000e020f501c45209040100020950450f401200202c1c041d1494048240d681c441d44c2c80091203c2d00d810104403400741c070702030349a09000d0400f80c1050344520b41c0c0c9403d142140028401007690f40203d180a2802c0d0080c08001e40041170100c1c8038503600c3e4541d500f25800c01209005480e4a011300f0307481e070345c640501511142d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 453775872 1250 453774622 453774641
    0xd080d020403050f06090d0207121b03020301020d06090c1b0605070c0209041a0c03011508090705100c020a0f0303090b03070903020904150c0f0f05180a171501050d06 73
    0x1603000c110110004400303000d50076200d00e04200900340d0381071890940c0e0401c081000d905c0219402205d0401c100d8210fa11003000b40c0340c001c0b0301d03184009030518800710f15007020340001c0c0d059070000851000101c402c0c1c1c030210480e980250200b01140c00114100c554082d4900082150500c20a003c0003192450380641d40001d40760400440100d52039000c5069500f0071a0162520488880f001c80400b544407040c1e0303448274034561742514560401810807143c1c1000302e1050b0403c1120702c0054140c0b2070400800011344002070008070301c00703c5d4410040006841d0402240034821040c8002070a64805404c40140d96068036402d41d4181000c6070315a5540000302240200b000101c4008096191901000d020b54058950034100d04031502d401c106482070314907080104411402a000d4256100b0802036840d10185082c031fa2300e0070b80381e03507224041303141000055105404400014842040034010040c2c2c0806505039015441542d503070f000c122009128a0b03030003016460180c00041c15551145100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 453776978 1106 453775872 453775897
    0x109060806061f0e0603010b040f05100206070c0807020d03030203070e0f010806061309020a05040303020d020a080304021507061a0f03073605161b020d08 68
    0x544031650090780011146000c40340c0f244503480140c45404000c020f2620795840d850f00d403446038413901c104c03206111031420014031424945030b20211400b042d0094501940c80850981e0340c03030a0300b0300895101208200140060b500c456410346210b0103603900584be403503d80d1014000c80c52500c1c40b2403040c608045114210383c0d006080aa120005481182e04ca80040c0e12240804500d5044692094000314055041540c844083e0007201c2c001d42c01c556201001c481c06981b034030607600015148060420000b8054204103280c004000001042e83c1d29104040d210b25048071030070809107000c4056031011029900e891206501c01c44011000b8148030740c41c0103180ca0407413100c40e412442c95846112018a42200c00150400a04010405001c14980170203418220203080f00803c0c0883c24100300c104581c42c140903030284a60b8003524201c42071f80707240c854200c20b4000d042c21200 = true := by decide +kernel

theorem cover : BRFrame.Cov 453597122 453776978 := by
  have h0 := BRFrame.cov_init 453597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 453597122 ≤ n) (h2 : n < 453776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
