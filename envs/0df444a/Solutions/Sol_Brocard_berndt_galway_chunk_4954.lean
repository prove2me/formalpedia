-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4954
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:16:24.075996+00:00
-- url     : https://prove2.me/submissions/f9dc2990-2b0a-4980-ba43-529a9ef22632

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 890827338 ≤ n < 891007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 890828588 1250 890827338 890827351
    0x130326031519240c0b0c070b0f090d030b13050a0b12010b0319030c0605012616050112060302060304050a05010c050c0714041e091103070b07170f0a0201050f 69
    0x1116401800820004042c12404011500701280010000300d004c461090002070041c01480b500400d10102d0b000000041500500401030090181c6a612000341290420758080880d980a1461820200d009401c950034440d802080c4c182c15082b0403e01c40d0a65408654902000341d560078048180c1c50f1114100c602c00384104000c01084d08108080395803420f83d44503403d40120421603110405101c0c011070041b4980c4600144803550b901d40c5401010742040185558a110081c401321105030000f0f021001103031a18800c40e03e851822005407540541c208034500345c141c0b0b404010001d61241002103024a201c0e07070091030740780d0403400c03c94211841c0244050400808005801021500107002c82c02d0399a101100150a00a01c000400801714409191145008061140c01c14109030340504a07050281c0046459078801004241e03c90440d07000780c504c81c510910400011074000d110700c100018061510901e4240000603070511900254807102c0143c0d11002040400c4090220752a00100c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 890829838 1250 890828588 890828629
    0x90118180c032003010e060418050c09010b0901051209191a010614040b0903010f0f200406052a012408011401030209090a140c0103111303260315 64
    0x1542d1140f56200b41c801031007103810b802070b4003010400310369a07a404001c04c081c00080f41d0140e403515140241c0c441440855080c0700301ba2120000038400a0401290700802d01691054a403001c3c46601004004001e04040b84611852134904021950441c083d905140528850710008195404200b80e000c03050308602c2c1040f501000d11904e007002d00c07060700c050710744030701b0200e450340400ca0100303004000d00d1007260200e030f007840411511041039a00c84c4407541e5004036403080003030794456010ba292155102e00320004038100481005901380800040d000d03224220040d0341c807402c8070215420340d42006050080002d8010203504085c8142440034002c1c80b07480700134000451103140800c9040414840680121940740000708411804d0100b181c00c03d502c84207003585150f61120440c1d440904c01c80c13290100346004803d84912081c078060b1132591141d2190105d490341135666500c10f00d030061046072296803d0a00d003100804c40000070b5442610144000c0654403040410000c8002014042c8907884c2c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 890831088 1250 890829838 890829881
    0x2100b03010c0c031223090606040b0a1724181902040b06130f06030c080114011112040b1806070f1e0206070501021809010605090118180c03 62
    0x5500080070212250f010700b0f0040044480f000040086d180c54a40030a5103a0b5038605815001c00e102c490038060b4941200710342c000d0f82ca0600f404215040000070681c02a0510001c10807104030703102d500030740c2070000c1c10380c3e810034842c1c0d10010a86181c0710048010410940c10491840d042110001c0410050300062a03d80441441101c640103000c03030180c081c1c0e4484042c404140c4449080700d00013415410042652965808240002e0303599006000c002420a013042401a10613420755058802d40e80062034001d95200041d18070030041e40c4030381c4041c00341604403a00c48a4400c0540000c004804a0a5607920701c0ca80c148840c82d4082070f40d52007a00240b0600000c60210702c00581c2e40b03075200c1a4414644545024441840d040c250000d600c090009008400c0080640142c40d81003074440405915454480c03c01c2040002401682d000038014071010b400c0e584144216402c032440c500d00e40070241d0704d4080e00900440003070040600c0903112101d104405500d0f00c03c0141d80424000403002d038 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 890832338 1250 890831088 890831111
    0x309051504060507230d09021e0102010b0f060f0a030908070c0e100b031f05061614010e0a03030f060f0e0702060709050102030417010b04091a09030304021c030e06040602100b0301 79
    0x108024030f0174445094001040e0740c0500c44550340210a8180c000340380c4114180e47c0c1980c40c0504c002060300314019402d0920b106443d0400c00780350035000000402e064202a0302c0440b0100e2074000c00151410035440300d00c10400704808000802c2c920780603007600c1c1c44107818030407050140c40015103401c007070084a2a042000300c4840c4241d903007082d40301500c24601000395500b8049a02660800d544c00440060502148500020040306e0584a041c0100885202040d0f08d0300302c6101e514089a180c001c1200c69000a2080c0e10029402c0d80e040400030320941c03609446082e111054100d00d007026440010f00008940402503183c1c00802703498200d41135030030040000e44a0240303125006520040d2035403034100ba4000e41243c240c038032001c0e10812508200e818203100c00c14640e1400112107190501040401202104681c82960098040c2c001e0008061582d1181500c60380306a04100e4814a0083ca980c0c956008100815655006105425032120058101c545c1d01e8140c0d8800c0c0e01d06801c8488 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 890833588 1250 890832338 890832377
    0x60e1e0d0503010329090309010e0409050d08220b0603010b3109080a0f0f020f0d0c0203160303110106140a05090903390607090509070309051504060507 67
    0x15a50702121011090004e400390110b036071100059405c90b804100100902980004003600c0010f0090382c4004442a92805100485030f40503c0a40036400509409080d1402104095001600d43c0130104446200c0c052811141607007030412a05681190280441c5280034040e00e02c10080440302c5010b070300341440c0f400350700701e100154280c089480c0054250008441d0346c4040c11064101919039611139100e98010a40d20384034070001e0110750301d407405401e420700c00948555000840801440340c101002e6081d00c504100d030074101d905101f800400d2245400c0c001d0048011846070325140250040030b04d142c0d00713464054100c24008e001620f40d1241e03079030380c0b010f000045480503100c01c045038071181c1119040d84103001d40700400030020200c01014100141c00310100700041c1c034840d0280d022a02c174980d00d440d81540e04100090040d81e00b80040d2800444460308041c0c42d04001540071205e40d646810b00340e40070300744001038406000b0803092101a01400307a00c92100e24000d04401921401141c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 890834838 1250 890833588 890833591
    0x5130b030d030c050706090c0503122d160605060a0801140a090c0317070302011a03030a140415050c0105061c0305070203120304060203040309081f0b04020403060e1e0d0503 76
    0x408243e01c854003400d000d80282c080741e603c142c0040d4280850419800c00e001040914450302d40031303100d91a04bc1500240d4070094548100301c104010342c84086040d15a8034100e007218030005d07005410030401c00d2031504444c0780903c0c944620b9010880f031801c1e000f000754001040c1e00081003641800b4901e0f01d80254004c4140c0d201d03030600ca0002d20340390f843c1061102c0180a40000b0079100b0601c51080c2500020409020340768801c3c1d0083c042c01a000186242c2090700c1c41c0000d070598424040508060b002d40c1480100310265032401e0704080d070360340000a608000c895003401141340024071048010080c0113095010b44151900c3c1d8010185c01c10f02e0700440c0c081c0d80041c040000c0491400215038040c00b021000140ca8903100782c9900f0b003070402c50029070003074800f100481c2103000d00041a00020800220041782c002443d50040c1809600102800f03070380c48241d034065820080400000d0140c072801e00f01c04500340091101000d0382c0002c2c01c8007801071101036060307031000180f522010350150489 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 890836088 1250 890834838 890834863
    0xe060102062419031403070501050a0c080424020a1214090706080a020d060311010e0d11120c040203040f121b110d1403030a06060527030a060f0605130b03 68
    0x1140f0a40c4080d1400b88020000d0700010817072414a0a01c140e44c078400406003031401d0181001b0021900c406040d07500703c0712486d40f000080303400c401c009030228212942c5181c3c0d03020170246081c6410380c0540d4070400c0317a2080c020140414941d00c9074945800d414410240340c800c20b0f0702202a141402610980d654a9034803840c0104441038001070450715907a01a1241d20000b4102070000701d40700c1ca441552070440c020031a00058040e540e001d018940705004090264008040203000c9211106000441c001941044d0040c0705004403080252201d03c0114480c80c06082c10841240c100c4c60103010702c10040c0c04d2501042001042d070003841c1c0e51240031107819a4403e08002007060840d0124030490002500500820030111190911160100c01503100388120b800070882a0303103d22040c0d689014045511a10841844102410201d0040215885036000302110006010756032800140c1c0d0b40c11542100c50f03500c481c010803c1d4144400d640a41c064110f509002e00c0c039480c800f0030341d50380074407020 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 890837338 1250 890836088 890836099
    0x9180709270201050d0c0c03080603150a021303200102060f071d300f01060b09040b04090510091104060b070b310c0b0f0a0f0e04060e0601020624 64
    0x21404680c0100202c17541054400402d000c03c40710034001901040c00ca01054021071017150015803180b402148201140b14120304261564886c94040c60084d0020101062141c0c02541c000c001310340e241400c0c0050807074030081820350301c01010009080190213000300c00440b0b4030400748011180c2000140059011542c0d0300800341e1941c0c00000c1800801d0098900d4403201803080051000d4403120010700000520201d8803116091080d103401c81340306110740008564284451205460150481e00340400d0040000c00d14944686a440c14800e800321103200c61aa1480311608009014103041178150040303404010b906e2801d241d04540b84a0328400800318024080001c540c0000c2d5049140c185500c40c00c0c0e403c0d90946000351102400c5080019188000d0781d080000710010001c007102c00201d080f024150600c038001c0c0003500d20800c000041018095a03c0c001c1d40c194072148640c500030024005049101e003030510000e401c0c040080c2c40112030100100300100c28000711142100d03094401d544 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 890838588 1250 890837338 890837411
    0xb0d0b030c0913050328090b18150408030307170604060b040b070c1517010e061f0314160305130818040209040603030201090515040515060301090209180709 69
    0xa1103400c510907003440b0144125440c602c01813200b031540000304204511f444620070192a140041c1650089644c00c050000b884070403010181000400102103000c80c2481e1400d00d40c0b64a00242180c20440e800400a00f03001620401d151a141005400030720030307107082282d541070229a246503c207034014001c0c24400003500c40d0800400402800061042890b00744800c5c81c3e0303241c0141890b2010b5413400c00300c80c0b05000407546031604e01c1201d0254074024100d0340c607103c150744041c224080b90b50a140a2503a151401489641c07000707913061050300710301c04c4440843c1d031200c00a000c41b0805031070580c400301320070560360024014000312540b011002d00c1c500184e03055071000801038420b240c01907070400d0902e240001015015000100c1662040017901c40c60103920090b11804c01f011103024140c0d40c490389507840c60300303410203107140c100c40f015001062a80341c0341c000c5041d600007540e140542100d014221a040001400840094460b0700d0050003240e00b8900000450f0b80074080e0007080058200 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 890839838 1250 890838588 890838593
    0x1e05090604143a0206060d030f0c0c1202090a23100f03060e0124060503040305070f050a020f040e030304110d150f110c10090c0f0b0d0b030c0913 64
    0x400c05040ea0f020907111542c03404204001c0c00300c1243c10244010595804210800f11400420098070400028144c42e118440d1070701c00319900011854034802340020035002c50046090700300e4410161100001200d01f52643d441400036046000f4003890110786000070392412204021a03406e01e100c001d014098050321100d0002d500f00c005a03100384100300303050ba070010030403165410400034070340c40074001c0151100c0c0c00281f00600b0040001c004c5044410b03001805054000c0c030142d40c10600914100d420b102c095074521650104461040e601035001c18441c104500d02201d9404040c241a10203000c0c41c1158051142e0700d0002400041c0007007024200072841e0f0b164003030f0081060341c100c050100858813900841c0c00509040604500c201d0030b00041c0340181c0c1825040b80d10340104407004002c80400c820440b0001d011703040d411191b00c10031100015030711000d0801d0070003038401c1c0308000c1c0d03451174400c415204a078641c1090034002d4000c940c41008035643d00c1407080c0d02004a4201510f00c03005031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 890841088 1250 890839838 890839843
    0x4030c03080c1c05190603030504060c060f020408150a0c051803030c06040c030b0702031303151508030a02012f0a1e03140a050103170d060e09011e0509060414 70
    0x1071501e000004034004488102c3c040d500814012000c4501d05143c808540e14403c099600b5030002801064003040104141407159603180000c3e40034400009600300c2c24900e0400740c1e402135001860f02d510045400e0f40b0a0791601d15075400c03103c9103504018a110102010b01280503205d40340280c0c152000604005072020700480c1d581d9400842612118940383c5070a40b1019a28001901d0341c410030700000e59024000002c075071714510ba10301c147e11905d2940e6110700544040c9d036400d0710f0068580f41059036a032500d844410262690300041e68582e00070420090850b0b043d8607200351404c0d00203081c0b16a42040c0081d90300401c0c0c01c1030407155a1031085e001a00d840e128852181240d0500e0000c4048155069010052110b0700f0302100540c0d44500c240300c01610028003000c4c0c20668640c164150b4101640020444c00001d070303e0100b1015a0740c1403610a000045488a00c10f035150400404203183d21040c000c828803503a00d0403c00d508000c1c0070b180e43c4200091001740a1a1605020706c05003104 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 890842338 1250 890841088 890841097
    0xc010801060c0c08030a110d170f220501020c010f02040b0a030b030316050703150510150e30030a0203032205010f0e0f0c1c020a08070602010b030c060304030c03080c 73
    0x101405c1765078072541410001e2044111ba80140d0b00c6009002108621034400c2d240d000405000b04813103400e945903811414002140500b03072418519040f0410100c1d911440d41451fa81c0f0301035000142c807008162502130948500c401d01c0c99509104020900611a60303006a035204901c5290000ba481e0026001c285544503418074001007105d070060110400000042c1d020503a4441c121900f422040c800114050300c505a424074080b5001c08000d000030707802d44440030780107210392070051060010900420881c9007040c1a46640d400b082c0200c803d0b003241c007142d01c3e550350343c288021450203004190080d26400050b06600c220042d035800e40030894500d00a1801c03080d0084020003215078180144402464400016145801001203003200c600012503103041003c0007400540500c1c101c01c0c2110f10082c5149002c0b0b88c40800b0410119441c40100310070383c040c204980001034510b0413482018505aa8004d035284a001d04100300300003c3d1384130000815041d41410134415546682c03442020a014 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 890843588 1250 890842338 890842349
    0x102011e02030c1b0c0f0904020616170d021e0304020907080613021c0f0b180402040f1b0e0619050d06210b010803030606030f090a05070b03010510020c010801060c0c 73
    0x8a01d04130403014000700c0c1900110038201c0355a1000303000e00d414022007510803240a90700c00300030b20880d09a4440203245501203482010141080c07101d000d0180d480d0341010030f80e400c0c0680e0100b00c450010780414504031400d4420380072181907242c41c2d0f00240d2100d0f401881e403010002c800c0d01244441e145d29440d442034803451702065440e9023000500c40d8070b9588219800a88608141301303011203010a11814459801c00750580e1840c40340f9103254a440280030704102c0e0029651011203484a4140c814040c0c1c07440b12840240328a04144401000d00529400a03803042c2e00030019010b4010740450854138500007420401d41b26103d01d424900240700ca64840302c0300016030440b2054040f803d0700078540ca07030701c20600e41d40740e6600c605034542d60b03010407a411a08890108045400c18500c0c071040b561020703443c0c08460300180720740d5031241400702d598072120b580c000100041c0510b02d0114182c40c01116548010124200f10500090021a0600c140400e00004489034010300c10750004c1c1001a19 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 890844838 1250 890843588 890843617
    0x60a05180d06020d0524100210060e04020901080610090908130602010209040c0c08090603060d120c0209090a02150d02120c03040201141201030308060406320102011e02030c 76
    0x8224203042e4060340c024000208414038040c00911814400c4000c1c50000b4941c80c4000c440c00e10310002d0180c2d0b003e41c01698400e6200301e10000f04106014001c0310041c0030f600440c01401e0900e0302c18000012410780002202b030f0462020012402000e000a070708a8003411300114a81405003403800143c400d01c600c000c45508000d40104a0507015002000480c0095404110b1a0b81801c012140c441c1034110090200204000001551078440081c5403c044024880300421500307a5985006610300e009180100701590007503000d61138144455503119040d0b00c003410805c460303030303000418502c421440f14400002c08601012400400e0307050f601d0103014030000e403c0c242403d105900503908100c3d0101c0c0001c920308a940010950f410030355105401c420810341180e4210303641034890817401441c05422030f95961000542403440d00301001683c404040c121201c44c1c80024181d2000040c0c3c0a04e8156030401e443c03076841c0c403d4404003290440070f4540040e26900c0d1640c4201040c0304d003466020790341 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 890846088 1250 890844838 890844859
    0x1008011406011d031b0a080d08010806010603050408091e0613031202150708040611040306020706060b1e0702060405090711012304030e030c030304090911030c060a0518 74
    0x4000c282141c050328090f00c0300b207034803410300325200c0c0c0030f04004000d242c054202e8807840c00d242540a081ca4a1101e0041624506036110514940740881000503a00056000700c010801c0c0d00051143d24050b041600d1705115034505602c0d00d0030103214607900d69001d0100031152402c654600d0b180907600701002400644d686ca8058032074043c01b4068001514280c6921036035070115400080c151200e200e141d00d405400340d4401c034003518400001002a03861a0b140e031500c44401e02280010000796200c1c0d1001600c034115804c0c06022500c2c01d80200038218820012561160402000c902d030031452120040d542c1c44041c4013040f01d9004660046400c980103005111301c03103801c015840c0d106107400e00200300e403c40c40305a1102000d40800140c1c000c3c031038800403a011071310641c0c684201030f40240403200c0b0007a0901c007091960340311350710250010740d0380d5a00a040008a00403a490130794120001c1008040c1c41c5c0024450f845159020410710a0015080901956244044200c10001480728801 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 890847338 1250 890846088 890846111
    0xf030a140c041706040b01120302070b0406091412121c020d1e0c0801050f010201092003100501050603150d0501020c03030709091e021804050114030106050607080f03100801 76
    0x302d4001d0701a1000d510f0820101c0b03400c0d0880003449500c074a0300215a00000d907e0f10342000e60780440010241d0460080c44400b0a00801203402000240040d0f960074200c2b624290090405064102c027a40c407a9028884590b4003020009460450702001d02c0000d540317019012000d2441003010071803856280c00481c2034101d00303081e03038844003861860b00b0712000b030940e40d049480f044a982148200c045680940144a03504100610b503104080c107000000c0c081b560342d00c03040166407103031403220310940860000c4840d50400344005806040903000c02c1c000c0d9414600040e2081c04000c25070000b0400460300518180e85042c5408403454000c07008558419241410720b0b101e42c000c9502c800800c2461400180d00c170340e0341c81540c0040c00d03c0c220000001c20240d8058020b0744c440382c3c85180007058204010580c1e951846520b00800901e0b65455510b030f1040140345c2529810384c40769109603402d00151740415041400c030391010340e601041c0d542d2650f408806034403c0c1450b1301701003807541c6020080c844 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 890848588 1250 890847338 890847361
    0x1606050c0d06031b0b030405072309130c062d030b090a02040e0f01140f010302040f14090a05070801060507020109180902120d0f0e36060607080f030a14 67
    0x2509004160700e0700c0300c6a117900e002a01d91106aa00900e1503000c030798100050030660881000003400348403015403042000c0700081c4619400c1d5000110000c1482000b002c00409502c480d004001a003022090f850b29102c40417190a1040c110142e58480d1441c001546807080d4080c1c01c4d16103000300300c1d0f08281005030100000b504070f0300540d0a6254001d0109a101d2204003149048a205140a10f90081403c05010f00c510044011701d041c15002d00010070a04815001d15000d8040103010800c00050746007001901d40016200202c0b40d07107403905005102e0303440852141503c082d070522a42e00d0364141f0040310101c0e003640c4114518408086904900b104581040454a000b2900d1180310200c491036280c5680307060891030041500510120302f16401170401044034140209010101411103680003003411001d0349101e40c030303580841e848078560400311a80fa000360003500c402e82465225614006180316100c16074101c81c10120006807200210740202040e6180d80300780030018241450305d0329 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 890849838 1250 890848588 890848613
    0x91917030702030d0b030a021012110c010c27060c080c03040e0702011a0a090902030a1703161403010e041e030207060e150301090b0a03050a050d030e031606050c0d0603 74
    0x40e101c5003001150401781c68005100c00b00140c008211403000c1d001c0d01e4080d1041c0203040440380b0602c1d00c500c100001001410b001e00743c0111034000102d018030340c01700300411180d91032004c00186207854880802d42600401c2000580d5451b003480c1489003628109081e481c0108480740869110018000c6a0417088841a90050901e60024400608010071100503200e0550420340c0102c40c010042240018036007129580500140544a02400b581c80703420041000c1818005425400028840411150360082510101c03030701d40fa030746010701c01855000511042c41001212030b240c1011038248280700c504174070781d460300c14101e20700080d141c0f40280d04c50341e49118580100d061559617004505180d10300fa50750f040401c142c64503580c20113030b5003001002076020464214114400110000e4400c100c680c030340b180a10014110159941c130002c0030b8034400d03800b03514503410900850030421004402d51017101e49c0145c000c2455540c0c084284601d02420076648021410014004284200d550403038 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 890851088 1250 890849838 890849857
    0x604111c0b010906050a12021b01090c142707050c0d0c05160b0403080a03020408070b1c0902031b030c0a06031d07061d0a0f15030e010509191703070203 67
    0x41e8959a83c520382543c040c0551320241c001b15008400c0400911fa659004001689100001d040c408403100420303401c440b0a40000c130780c0341420305004e10030050001802044d12130111204206807080c1d0800200690741c1c005658010403000c80031031440e50180b4299018458520102d4800e80b0004d6001401080c189800369880d00074003001110034502504810300b620b2651a8080c60701e40303159a41e40a981c8080503440405600388000b080c034140074040c2d6070082c00409009901c1c1c4001222003148201d010314100c20140c07406842e180181c030301148142a80341703022004880104d07070300046403c110490502540c403000c040000724150fa0142e1003242e04c50b40c0240c1e01040a05038100b0a5a103200501440c004070b558202000d00101e01103105441030980944040c04481d03481d21005240b0310180c101c0c21a880c4003040c04215071354148510040302c0394030701c000c0c406800d02d540320030740b00d0b040c01c1c002c081c80c0c5040d0480c10081c0000044c60780d107044888003130b1550381d15141d0340003501c84c3c20041d0315 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 890852338 1250 890851088 890851097
    0x207081c141510200105100312090501120e07051c1a01030b011203120f0b0418020609130e0d02010b0114190f200d0221030604111c0b01 60
    0x410020000621059403600d0301410804407a03441c10740580d507851840b8046a210101d0502012602d4000e002e400e008850102001f0003290862605d100420030248e0400e04004541e181040715a034440b084509901d54000c00242c4070880016140c201052034200f60740008603071400c0340c200fa03803200841071141e008100302280c98503d000d04025101c000c0c0300c0641918040310050000c03001c03036001c802d211031081c102840c1541030060101c060700c0c0d14030b44106403656100145046410a03000b04010801d146207465040195580011518060f011910f40202c482044812012003a64882000d15109404840c0c0311710303101c50020301801028542c180003e00484103043c0c680100c800352082000c094408c082d044012107001c9850810b01000742d02009000420703450185035004103e80150100d0b805070403d1011808083c0c900061484445074505040d02d010b05540203140990342c01c8442184c0100341a1542c1c0b0652000d8010a408551400e030102d9103441c14542c10b5001c4211744100b80c0300c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 890853588 1250 890852338 890852341
    0x40c080a1a03030406081905040c03020916301a150f03040f0f080310060f020d020a0b040f02091305070e0603030a0e01121e0e030c0706030207081c14 66
    0x500d8000020380040c0c1d901075100784428801103000749002907025850400703004d00303e040c10400c1815120165403e89503181d03510340a0040d030a00e40d121a501030344403c83c02c5824960341600601d46400e8880b90184920007503040f9400c00d148089070401c5402610b02800b901c402140d02c05014034446500c41c0c4a90340400d089455207194a040c1c41114881503802400c65550361140d601e02010380070300311250442454445c0004481c040558003800340694140509824440c0140503034200ca2160829580718102e04545c2c030341e0008112240d00d07400070a801141c0ca03680741c2070202215410b0029440310f407810804c01d58503680b041080034540900229113102d959040f41d80b00c100e2051b00c045801d074004200c0001e4041c06080301201c9001c5c1858520b01030510300c9000021920551003141e0719400f809401001c5040b079000b103070030308560310f80514074100414800c240d41b2400361054006254020480300240580f01042d211030b1044482c3c0802c0c0c11410030540030003441281d5152008800f00300 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 890854838 1250 890853588 890853611
    0x151504050105010503071809090f050607090f090f06170d020c01080708040b0603100f0b0306011d16021204060908061005090105060d0b451302040902040c080a 70
    0x51641280c1c2c060b1201441c58560050882e0308580c0e0408008104215180004404004c2e210f1031840302d010352440009854140741040c24050083e0014042182103402844019105918a0121951502c001403103a000c0810080502501d91040482c6040d900303010b030400c100481d940d12001c215609542c1c01018502c01501ea001042c4d42c0319000603004800140041c062003485508110020200c07046407860300900030a0f164066000700806d62070398030144290804005450141440ea40c512001c002585001082c0d0000142a0141c0f483c440005030115402407180e1144c3d0810b140c2416a40d540715035016064942c00e220b00c0380c1f1881400d0004024640900002061301c000425071440c591a003000c120180d0440380480c0075690355000b605019039074030320000420461002c200844c010003076000703910a0710482c20220710212a03a25600f408404610b03641d2348418145042e411605c1c1500100d001000e916030f009400c03d1400f10001310554011101900c9440c0300314051010031040f0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 890856088 1250 890854838 890854841
    0x106240c2a08072105032a0c03031806031308040308040e010b0a0c020402090f09090d0807080403080a0c110a2f090c0304030302090a0b0a02281b08151504 68
    0x144100ca0100c0a01180c0d40b0001c1211103803111124090303000c0300d0034007c00080c010000c0001800000c10300c44515940d0b014054284401c130076149089001c0d505140c00180030f4001500e40c0c403003540c46144004000303420f45815403001d00501d504180104e4407981c4a01c1c24050a5100340180011602110000502117640314110351040c907555455503172000f030700d0b800e220207900301c03004c416485201c02d2408907070303620303980c5080780325010340002441a01c546035005013000310050904030821407460100701c080b94011851747d42011040700c1c001150a0340207412070310311042d1203450703e09024400001d01070100310180349184184610a0140d07407050300b64248111144140c10640141a15001400304803503031000c3e691090280c2405032a280425001641c100c6403508120803515000c200036810380e42c10480c09494000c200c908455400d00e07052a480e00141220f0000c040c1d48031118030b20828080500c030b98005180507070442e110030421403503c51004008507a45a0384004000c40c0c0034241c90907 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 890857338 1250 890856088 890856103
    0x2c06040605031f0b030d020109060e01020a050f03041104110c06010501020339191104020306060301140117091e01270c05150d0e0106240c2a08 63
    0x3001000c06a402d00080003c0040360102d0301600d07691104913004035202408100601d00c1d440d4000070b01e050092404c803086805444503509185e2050015071081a086012a10b1060001241580b01c1e170b0384e464901001c1050718034803504030f17083c00c00d0fa80d2882c000b140503010996691341034800f035a8070394004903581e002d95072401c620406a60250108000302c203c1410901c03012461020700004409540ba05d8004194070440d01c5440d040c00c07400901c40508071540c0c40d200122000d62031418018000f0315580818046c000a519681d1200710080e8050080c00c3c8208101c03140b00d041d2842c004132082c0c1c5506003508441c14450400880c0541140184a03e0020000c211120300700c246c1082011542244405402c8446030020200400c0c03541d960120f0020110529400c513039103228205090040e0340002845174400da05001c0107005200040c81c0b000101c0700e075807412140742c000020085070752421100c00076090f80607401030300111040d0311540041d030503c1524410003e503a14001545d5a024 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 890858588 1250 890857338 890857349
    0x27090403020303181e1e0a02010c170918010501020f0a020901030b0907080f0607260118060f1205120c0607140c060a0617030c12132c060406 62
    0x20410014581c521000706400344d200b9014200c600f410600340c482440800402410300319580940341d1403007100807008120349001384000c064810580130780e00180055000100043c800940128114402d06107082031320030019009100c080081c12140d1043c0c0072a001380200c0b070050003025540c000819001524082c1940d000d0032000d410f030300c0c5860740313031144401a151104a00030784400080c0d0040c1081041c5110b00e071302026094a0034220009400c000400d03201245007006100e40160702c20b01071820700e0460320710070211b14041c0245501c1c00c00078209a0000e1091000f110700120f202a02e05602c1d0419501c02c0003255001000c2c207908190034024498100720715400702000811152040d0803400c442d1403100380250909030007950042c1444002c41e02c0115032607641c4030401c4051081d1403000300ca1205000514030740000da40180e0b031030b00074121a80c10b45d0708000400d6112910a00c40d407200a02c0751410b07500170540c24046001d20212a40d103000407404000c0007044841c6000d1192104640 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 890859838 1250 890858588 890858593
    0xb10090e07181715040c0504052d060f06070b060f0d0b011203020a120c03020c0907141c02040b07140d1205060f0907021f0b2202040801022709040302 66
    0x40c604620803c540c0c0045800c6900d9018006688843c20340007074609000d40c2c403581e1100030060402081c8000c0b5078006000e5a004500e02d594124030f02000285100c0006452200d170b50300d82d0300c60000c1152040c3c101c6400d40c00c0f8400040100500405015490180b4000c90307042036807100f4441000b0841c4191000541907440c07000040169810460703c3e94521803080c015607114810a84401c048400940840300110384030410b034104160741406604400e1408940c11800c07400c21084c0145140c00c031a08054402000060541c9060001300c2c542e00c25000c02030040d507445032182903e000c2600a0328040761a4810380301c0ca000b4040300420303102d2480d880c0f6a160450354060000001c040e0001034000340c0c200300c1c003d00c0400380752070f008070703540c8a0401034008250036412911082d0340b0950050b0352580e10307450704007050413581e108500c000c04046020068040407c5038440b01d0001d104581c0f00d0202984000b03460035050001031440204044c003041f045a1030700a0405200c040d110031a0b0040068 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 890861088 1250 890859838 890859887
    0x80f03210132040609020c2a04090215070809010f05041d0a09050d020303060f18040227160f03021602270c070c23130b10090e07 57
    0x2070038003030414600c9544200a000400c040c500208040715096046004100c2c1c000a64895030b6608001c00c0c0f6801c020030022464234140e004039422540300c1c844001d440b45440cac81c1d510303007990340b4030840d1418110764151850f5180b4151514404603408916103d0200e0350001c8400307200c5005a05a030b040350060804890043c482899003450490014007840c440c42c1d54800d580c010903000c000003892245a80c00460703403420300f10200805110604007481c40341008004c84000140542c00340c940044d410ba591403c50444280c81b44500076100362440403071102401008008411a81549a200819100d016204c0c185040c128280d100c1c1004140707400080100d040c0c01800d1800da403210124021002610a11b240340b8100d052100955500560040101d540c2040c4858180a8402070070054a07040c41084448810280110740a044902c50201c0400000d00021a0380207640804c100a010240703690040750054901d20752030041c0d9031108070310000204164019161455104080d1440b503421 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 890862338 1250 890861088 890861129
    0xf100f03120516110f04060305070b09120d0c020f0604060806010c0c05060a0c060e010c020a0305090a1d0906010608010614090f0303040f030b0c18011206080f032101 73
    0x2032821071075a035402c2020400000900910b41c0f009482410701c5640c1420690ba403020411032001c00c0740c00440e20840ca0f2900c104005000055a04100d803010440d032501c5000c5200001e010000f10318800403d4011200d0034108a94801e07200360f0241d208841c1100b00304805014049140118003452011071f58600224200e0340c024000c980d0038600c554034051805448801103076a80d0002e80d00f410118803944072070410040980280510341a56038000c1048225640000755140b000c4c44000d0103014000440c041e032600c0340e0b50504050040965940c1d06800b40c0d143c50130b540c800490307206840b4002e400c00401c40328840c00d080d504840c01561040b5035030040000414083d072103035445603440b0f40c04030b02e41c41140c1c03400e101800c01001c003554410103031880d5081840e01d000d002484155004010001c401030204045260b03a5414400e10303040c855444034145510041695422129880c45400e24221080e040000202512192803505801c2c0c0c015600258205440a00905205480281040d401c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 890863588 1250 890862338 890862353
    0x2120a030b0a0510030f0e16030b13021c060b010825050705060109060302100e090408072603060102010b010e130c1803050319020607091401050d0f02030f100f03 71
    0x303407580c00404003820259100000b42c4003005020346900440d81310780d14034407001414840c404905c00d8050281c03a48010110081c2c5c0a003c0502004140c4501d8501045400c0090300700c0c1c580241d80500201c5000012529943d0705811030710040b20058240030684103503510a015580c0036003110601d10200c180d02c1d1030449024000e90f0012402c0140520412001c5803003004018001c01251000050450650040c4201301040c41c0c8241d0520400f6a60512179445202406520582211810351640054a40a00c1100f81403410250000c2180582550560000002d6011b108260000c02005050318010b40d6410b08003c003a5034070100100c6134031071001040e04140040c1c40d90340b030409600340c80f12000da80c40c840650025922540042140350f84500d48480c0c2d070301c98003d2800246210b107400300f00200815a9401015044e403030700c6100340e51590103201034501010031590140000c01d0000340182c029041224039502d8030520300e010810342d411400c8001c00351800c07264070703c0a4500755242e400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 890864838 1250 890863588 890863601
    0x140c0a1e05011412010f0611070b0307080403120507182c151002031c0b03060714040819120c03020a030e1c0b0f0603061003020d0501020409050c0c0d02120a03 70
    0x30034068042203074460107002213440901900000044005450402200603c0d0742c18480c03d00c00150b10080c0b0910801100c0010f41e03074401158540a50785950307918080f20311154454001e000300d81014184201250058005517103203401d5500305501641e40c400c0244445160702c2c030b14000c451011003800010141090541d807011100e56401d40a2161002040b075100b80007036103134010303040840d06403050781d54210340d1500c20042c079409006481c40080003948440002d08034106110010420107200840581514010f02040b0241c0e131440720402110766030080301d82404c84040a400c204203074498015411200c031607030103a0042844a10664082d11040c050ce0200799101c030715184504001c0c5021154003001c41d10400c4100b400d420590086050603401034030482c0b01390880d03420010131070441600a070480c2d404a45004003c011800c040d0b00910440c0c11001030035050100708064010001c004045141c40b036412035111300b43c003600c120703240c0000001080e80c48004200c1110300700e100ba00b081 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 890866088 1250 890864838 890864867
    0xa0b0102150c040f3f1e05070b0403060506030105040b060f030f01020a0e01030605030a0503040b0f040918052413060b211209091902120405011a030a0f0605090a140c0a1e0501 77
    0x100e01c6c5510356100c0900d8030310740ea4080d041c80c0900150500030003440b80036854110f00254028021414281e85076100c001000740014001c07039003100f03051100e980c04c20000522400950003150340e02ca51501c02085481d0030100c0d54017003424400e000545050000d85000560340010107541402d04101400703110768840d002074581c590040c000855000d002d440f9200c42c140c601120b0a07e44d15142c50414140740c407404508050019119042e61a2200c014440b940030100c006000c43c0303a11b0170b1400030000d01000d60361039041a590b81c4c00f0315078410940801c1c44030300c542e0022140384200310040c044e00c6105030100703d5006200c4901042815080410342d84008502e003001605050041101c03c1007001e0448040e2040d0391112140e9030b0031454140c01c0c08500c54160050426448540c0352710844180e070300001090b46941d900040d00440003400f29140d5a40d1202800e4020858414441e03541c0f400101518420060901c0019010316603e001240c46051010310401132131030f0000565000c800e060380c8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 890867338 1250 890866088 890866133
    0x412031d011e0b060304031d030709051801110408030f090f0303180405072d09082401050603060d1212230a0b0102150c040f3f 56
    0x209034628828060a100d00c06040a500030084a4010b079006503004500d906002e24010424040803030780c440c0f00c500d1810f41700d0082c1c0541c42451804203161102d25480302d4121440c00341071040b06082c42100520700700c5288000d004084500700130800c0ca12072440f460101da0710030400c2d05a96040d80b40035004042e001803905540582450110f8210b81c045040d20411140300406000c07649001d00c03400350011001c0c500740300012103002c81c9a24a001805440031418403004400c200c40e44034014440c090214001a51460424115121800180055140401c0c05c0200010030f86050910980344580c0006214a50b40203868651100c200030002000007040303402006990740280303e00544105041425500350519150400d140c0c100401500c1c0120300c90800301100340503030340010700c141c50b441c8814102e4895152020f43c075100707218552014848154030003001402000c5000944012000c6c0c640d205200404140c51503503c150003030030174246403000007445012803c141a48ca88001d040fa60 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 890868588 1250 890867338 890867381
    0x9150c080406050d060f080304090f200324090105091905070f020709050c0915041505070203010c170c0a03020d150305070b0316050a030b0a0f060e0108041203 70
    0x15803000d10341c415000140440c00003d03c070481c00109205001c010b25220022940352418980400d440784200d00c140005507807a0302d00004c0e21500f940c000030080089500c0122200002c100300c10050b0001c880003150507034280c00706c9005d110828030604545200901030f9825031300386020005140c1006c1d10302000003001000403280113031144900d900542d09602d80c60548910000300070303e428525003155909a0416043c085100044000e440b980c100845413611115404e0704450418000c1d5032040b03500f18038865441c911513070400c00034002c246c002d40003401200b0500f00c05441403e02c202500d6404041c00000504035520310000c3c3c08281d080b4034015203040301100f410800d0320501e5201000300340c4c0e01c00040040010400c0f4207002000e01c100d00c170341185001030f80041d20308541d020440c180b01e0001810044036100754042002000001c0c108076426407580607040140f980e90290300c0205c0d02c6403800c2c415070740c01200105d10641e40450381b421035071500d00f411000b03000b10b0b031a0040200740109 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 890869838 1250 890868588 890868593
    0x50a120e0c03011a0d030302090d0b0c0702120109020d0803070c020607060c020d210b131a01020d03020f07021513030b0709050f01051806040f03031d0a0609150c 71
    0x90449542003420050030449050350425003103401640c100c10401c000c1c038404202c1501c95240301030b60300307415090050b203030310980e000f058031526850f000801820300c080403c80b04d40040c001a01030107009907402501c82266054032822544a550060351008030700e540c080006160b28020740e4498182d103003542d0002c14a5001c1615504480000c95103a502c0b02d41001d6281d50400410360002d00d41d01e0400180c900c911000b000d80c0745860018005a5103403024500a030b10f03403034a10240d542c0007080c1084402104020f40c00b04504010700c05005000b01d6101d004054400c1c000d5880c102c103c114103a2070100a80d003080701c4912030030b442151400003800891a5074075189100c50045000320113140c0b851811070002408402c2c03031313001070744a117101880401c26642e210307081c0c508054182d009404070220702c40c0041c085019542c0001810241300202000701540802d084850707440030504000a140c0d003c04004a014050189400103451074608100b90061000804255440f03410440ca03203805ca034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 890871088 1250 890869838 890869841
    0x3120b12012c0d091206110309150f0c0d0504260a170c04091d010e0705041116030f05070b04060b010f03270503040e010e0103020111010b060a050a12 66
    0x11242001d00c40c1c403541c0c9a800742d908800d400c00310140c00405030580340c90101c1c1c0501071074403502810b450061003c03820810014030307070b012030800005006016106d2800f24020b607564106000c2c141c54180b4100042905000f588078058003e03268909041e00f40201c0c07031001402040020020703608044010108800521614124498403060406d01555080d0a650150018080306909404d0742190401c001d8200c0013207090714107a40c4d5080001c1590300d03840e0981010750368120400302855281c20040d094020303000031310100700c940998082c04840303082c2200454030300801072000c2d0540c020008540009100e48189004d6180383e0501a04210f01910745840034181202c04488072070707594141d15600d41e0400060281c11000e45401e014004003044207450591083c00c100c501284220f42041c1000401c1c41910042d1924a54125081d81e4404600d1440396081c84281e0210300340041803880d5007810700036204444030261402d40340c1081200c00b15580da020507d04010084104d03d07100102d07016 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 890872338 1250 890871088 890871101
    0xf04150305010e15150307021c021f0b0303072a030b0a05010e0709061b0f060212010503030c0a201e0f010302040e06090c0c06010b040303031803120b1201 68
    0x1603940029066041c860058101d0384043c001e0810a6002d800c0d04a07207942e442c005200f500070301e0030140c1d1a61100da800f81c0c500710703510802e403003038221020500d09803582c0040c03103440d00340b00c3c244405045104040c0d04000c58102c1c000c0319405400401114001c14845000482168007000c0c811200714080070000c0c202045a81081354019400010701400d28014010340707014048090810700d9900b840f11000e00301d43c20900c10013051084419419225820548600e481550001283e00fa420060b00d0124000d501401c800c509050120340041540d05000003950099250003004101040b8070751544500055a56400440b9102070100b0480c0d80d1035130f2030000d41c1103c0402e9081001c0c0d480400300008040c00110b140e0400d072042c002003029140d001001c030b8100350706403404010f035194582c255440d0300c03503501040f0390351140c6800090740916100052088901903601003021540307034050280c01c000740c600080c0c005403062103181e00c1c0c2c0280e54001921480014130113541c00742101c65950030f5561 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 890873588 1250 890872338 890872379
    0x6110c030f0c0601150e21011409010c110d030e0a0204060602010b01030f0b100507020d06021303120305010308040e1005090c120c0301030c122f1201060501140f04 72
    0x852840750503030b01040480d014000714500d180c40031091100c0101007001e00c2c1080c601c20340d051200c525a01007070250130240c90103050024000e104100710b00b0307180c00b20103440c0100b4035881d240c025550503104200344890007092402610740c0c0f29420504502600b00e6050404150240369920001695148a0350000301095000801d595000c1c0c00050202c42d00d081781c0c119246c1c14400341780c005595a4901040c20b080ea41401e5480d5016400801e11110300810000e0205200282d1212441034140300c03241128802c3c0181b42c06501700030400c405480302884020941d61043c0018800d0000000e8400d0780801c0c060b00c541249a0b0329800110070000030b48140c0043d601c0060f0800701400d03003910749035011590342e5107940b855241da5201c3c0c9010784544900340445942000950401172071400f5480440846407142c1c40880659020045011900200d00e2180b80c20b40381c0917154440600a080484405846030190310301e802d64046810740c00034490354040e0a0400012030020302c42a200d807000300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 890874838 1250 890873588 890873617
    0x1903060506030f012603161502070b060a0801090b04020d1407090f0f020705251508011403012003060120010911060f0f210a0f0612030c06110c03 64
    0x1494143c0305070003945500c2d00d031000711003804402c0c084444000125038041f00c0306a061900c0280a00b45030307151074600304650001038000110348007488110400d650140504030b40c030100e416501d6041034201d03401c0b44001401150700c00300060140c981125203c100600900c510701380316031801ca249003400f48541102c0c070216541e9480d004003034214421a240c96543c03070300c00c610740a000e4848617501c0030b0080c0341c60b20b5003460841940148209000c03002c014411480c2450407014145006021002d00340600c41c1c485c400b8548502241c41c05015040d202c000007810000700c11961b02c00020517500c014071850500044100e8011101c909a84001171b030b0303100000015046081e403510241d104040c500b801c1c4289010b218442000c1000d9044a4541c0340800e006942c440c40400c803900358403199400440302e04400f1003000704180b40341c1c004004440401d4020004a030700d40101e110a100c40781005000100800c0a070000140326900c1092a18050082c0c54102440c0c0c0341c92500d15031008800c3c04155 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 890876088 1250 890874838 890874841
    0xb0415180303050603121e1306080106180308092803030305060a0b0f04090c0c020604060305181b01081003060501060c1202030928030804061d030d02031903060506030f 74
    0x1030303040c41011341002d811009010550f60319101030009015020209564800c0c2265041c1d151324007108036000d01040364040e61505580e40300141400c00244508004a502d1902c0c402501d80641441c206607170b8031007100c0d0305000742107003031003400405118a038040c10010007625403040082c80305000114440d54022800b854900d040c01070418059201e0104a0010f021a110042d50703002035800f520040a00018210f03150b5008135218440c10390003940186000034007184440e8180c0042d8401c40c4d04c01200000219500e4480d03aa4a022682c403019605681043c901c46602c18003000b90081524010001d41c1a01c035124102101c400ba403040d0003090030004040104001201c1000c4d005010380042c40c100000000400c4201100c00d600740001c220021402c50072403212090b200c05150860f510030341341c1d81c1780d44015000d0460f400140504400b021030a1a491500242c03000c0c141d030196000c2c50a107402c9601004100341e90681c4881810703200e18012505440d002c1c00b03144107544029654146 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 890877338 1250 890876088 890876093
    0x30c140a0c050303130e10121208071404181509050105010219170c210d0e060c1204050a15051005010804030801031220150f040b01030b041518 63
    0x10300d035072544414007070b4005024203030039402040c0c43c40084480903580824541c0c0c031410707141c940c0003281d041020450038010a0006105000200c0860340c0d101d40c8503001c8584400d0802e44103440c96201d6035498a0301084244610310a004128034900500200070880100003a082120382c1c406030003002c1c0107030340c03030300100090b69040112030206500c52140401e4a07aa68491b000540b0550103c0450810009090700e9907100800180750400100700c4110528842c0d00c07040860b039402180003519040c00c02d03c2e040201c1c1f2012540d90b0141e00340035030359468a4014900344184060046c81a50140180214500442d40031502003400b6054101c0c00245498503040030040c0b0311071783d000079041100e07400c200800280c2105901d030540f5080300403034180b00444542290001601c5442d400307840308401e000350241c80d000800307055410044440d4416950342c00140c001c2e0031003c480c01f6142030065001003012844842203260814016640c0401105614621100f070300c811844403117052070011041c005 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 890878588 1250 890877338 890877353
    0x41203020d091802031b071101090503030a0e09040609020303070b061509010c2a1d011e03060905010605090c030603060604021e3702010e0309060d0207030c140a 71
    0x3100d021402c10507801c0d81401403490b4401c0b40e0f0600c0c0b2810700e50000226010a8241c5003840c080039448072000c5d950b076058a0a0050941d809061502043c10004085503602c0d02005036003003404181d456003a04002501080080380300600306842030b5560700c0c0d40c03101603103060006020032806665072131220308081051045c10600c0129280044009029200843c1c1c0d029800180490300700c0303c030030078124030b1148580300505c40d800400c900d02501c10b4001040000f6590116106031030f0031141041d131b03980b40445502c032070482a40304241030340c6080501c0000c1c903030b5014416050003100001403080c1c681c008940300c00b10994600803000808810400c9a2904025442e0310207003d8901b9418401b10f005906074520508800018030700000c03c51009541c0e01003001101103107034045803202e00038000072404240c02001c80d008019400d101440020003000400c8640c5090301414040c03409104502e0b40f0700035001400101c0400c444080f45c10007140c181c1043e071080030300b030700301a00c000e601d20702e000307038 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 890879838 1250 890878588 890878603
    0xe0d0f0317060118182c0606040204080d05030703110a030603120905100e030c100809060f0402010c2d060b01120b09011502070b030703090c0e10090216050304120302 73
    0x1e0420051488841e084c0741c541000d41c013119a43c50490242c082c0c000b0a00c4064081042c103900800c0c0d82480300c1c05902141441c0b5002503c60a00f81c1303080317407120320901c0240e210703600400203113901400c03603240014401d4008590061080c07a0014064100c2c88050303049502001c0c06900081cac490310144240b000c40c2c00d61104108241c02c10701c50040c94003000c104007503035620564050048210540d030281c1c80c14030080396440c02c02012640d41741050180a84040000e8030084040d104450008204185c0624020b0086030140c440390070440003645d9001000380002190381d04020805040050441e04141002c049031150780c02140c0d5a1361040010100d80e0b1151061031302c1418518480ba0549030089000d0640d8141c2401c0c004c40350b0f0303115059191228940c8400e0b440c690000411044550640c4002c460500c66001841880d0b9110030b841d00c2c804c800c0c0c0c0c20400709180c0442c10054001294014004d10301c034a804000e542205443c1c050071500300d9072004d281c18407030480003810140c2c10300804 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 890881088 1250 890879838 890879851
    0x1e0f0b01270b0c2803271e0e04120e0d110d060204030210210b01050702040f140c1e030403080f041e060e1510060f0507200406051507030e0d0f0317 65
    0x201002000c2d10b071b002070134216174442c20140000c00c80d03240c01d41c03010490b0600081d1011850402c4a818039150440c4d02c1c04082c0100400184140f0742c4409500d080e114031862580c0040c104440d03841c8480401520300d054040403145141e00304000001078940c85036840041080c0e885410020854590284038441d0151050038a2490500098101c0c0e0700001942ca80d50340607103002440200f5000d42030000e0680c03444840104c21540100004065444024129801c4944040040c4802016458082c1c001a14024045021080010b11a00b510012213900074000d81c4540c13600e60750030751003030800002d4400035280d90791680c400310316580d0704100031070100b0500710001c1c83e00c0c503001402d81c500300254012402040121400090298410400c4d165200c3d003142204455202000b10070503860301d910300e0140101d0401d10009202e28103100003c12092017026840e150403402c0d03404441412004d11b503283e05c6a1204c800e603010640303412507101700910079180d2111190954194094445004024 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 890882338 1250 890881088 890881127
    0x63c020c040f0221191410060216271a030705030c0916020709060b07151103060d15050903040807120203101e0f0b01270b0c2803 57
    0x701601c04503000000010100e4812032980f505d508819006100180c0030120764141000c4641951031480114107005040e80c801b0105486e541e200142d842e00c9907034200003408a80f1001c200800042c00c8117624118607003e01e42c1071103104060800044425070090350b00c0041c40004004d250307003000c001e40307070186c0402c0b00288409070607480021907002c4002c2005d00030903100710040f940c1600130080c070000b52003011007d00403280c4480c0941a6904280c405540170745520301d83e1215002c01d4840c40c00ca204d4000842441c60303403110140f00a0300f0390b481049034000d603e0404290f6141043c82040d014510520203183e86901c5c021010346800e90360b40003503030040c0c0144006401a580011070743c41d211040e10380428031003142011485440c8065105112250074108420186581c50f40004100c0a09880c2d0344105100c0f2058502d00d2164221040c201b140d0a039828448600150040e10600c907405d0222400c400b20301d40706440f01010b84090030345141486030510101a008031061484140e07041c01c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 890883588 1250 890882338 890882347
    0x9140405030702010f1101060315230402010302160f0f1101021209040c0c1505191512050703021504081203070f030908190504051009063c020c040f02 66
    0x140d1035240e2094440090600c41000c0712540e10600404294240f6003080008004041d92801c04564103494031034920540751805110801c844030070001c10302c00d0440302131109115920343c0d0054009501c0350210240070981a0003080c00a40880358801d0058840e10690a0400152800c1e00d4940c48521405066400114a05442201000980f1030340b0000300c40200d2050200351040d62181d0301204040c00b0000322082e00490181c154201a014600c600248031080c490951521304a9100b100c01003c40d1a0074207007007101c00c0001503200d070b1460080c0300b600c820558a900180c000d00b0090000c903c404400716040200c0700341030089800c00403480c1c0c5854a586407000c801859404000c1188040c19910309c2d0210a10080380240d85510090980c1d98809024044020b0000d401520540e88030343c100811a24011744201402d03000c690b442d440b2450f1300c1000f08802d899000a4141581f000102d400144c50034142d01042d02044a0103500544520741144c414402030703c5041c903a40413076500421 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 890884838 1250 890883588 890883593
    0xc0f0c030d020118061505040204140306010602010c1b140d1d091504020310051e0a0b070215030a0e0709050a0515030c0f0414010e090f0105010e0c1b16091404 70
    0x1340c1083c182c940c015800680d21815014950400885401140c0c1080c4003090114030310b6a00c7c0c0141c0030040045003260061ba07a6844101d0903038140102500000c0c0c000c1c10002e541900041080c40d40700d11440790003050540d203460891500680a41030f000081c04800d884000ea50f20180c140721745007040d5803401203171400e034030f28001041c00344403080c2c000c3d0350000019920a80500c140701c0a40350041c01109030311002400c9460066020082a203c2c50301150f001401840f26011515900e03809408001c100038110712036009a00010001e244882d00e91006a0fa004006e00c00d56002c4c06140b0800605400c00d01e02c0c0c8400c960004121a055603074004201d0f68583d800141c00c080030344d007211002d001401c1200401d020b07258540c003102803400c0c480000320305101c2005035107200784c00c82411200d0003030041c803259090790800e1051301d0510440c8000714400c80e200800821352403800031202c5194420821403d440c11303003407030301c4e0501c910b0840b841840a00e4540c020060400c600d241c80744050705041c0c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 890886088 1250 890884838 890884871
    0x90306070810060f360e19060e0610090b070c0315020901120510030602040e071b03050a031d032a0a050c132a03050a0606080612030c0f0c030d0201 65
    0x9a055164224004107990b800c085c82da2007003006441c03507181010348150307035054110407a84c00390f03103003c22408000b03418101c1d14400e00c80c1104580e06c00c0c901a03400e88541c2c0602185a10f20b036011400c0003001c60b0b01040300e016640082c0300e181c0c81801e20907915842c60030211a41c4480701c0c0f00203900c0740100a01d24403a0703805242e2003414202920000781d80e4690810503c904403007544000e150500124000841c2c4100f85a41e034403a607129121050f458000c1007000d0803c03185040b006020031000d0041000d0140b196010381c00200c82c0c10003036002c940465010b0380c615005541940b17100c001c03000e1002c2c201a40c0d2100520290f140c400101580920341d0f035100e071120310141840c4c0c0075914250480400348101c1e0001c2d0240c5581e01000d4241285c462290301132140c90f00c0701400880d0800b001315454900c20700c6880116990f9907500000b9841c2c0d40d0400008007006140045140710030310120b40710000a11081d201c9112041c01041c40202031028541016020303080f80f015645003007401c01c4041c00b51f = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 890887338 1250 890886088 890886107
    0x220c030206181e010e1c1506121b05030607090317090d050a0203120f040e06151201030501050709031109090f0d020c09090a0534030c240f030f02090306070810060f 72
    0x150703031f414402e0301c000c207100d00401050b44811034188244051500344407a03502c000010400b034260410000781c4401c01c0c1503581d00151215400038200c140e0400c081588158001c0003455125146c6281001c0d120008101d00c12105059403142c00c8034401404614080003102d0601042510680c10010181100900d50003284210783c50410f5000c005907196070b60040c00c811001c50103107080d40310302509100f60090142404115025843d200118071140e009490ba141140e03801047c1000444210f4184110712030f0140c01118148170340154024246c1c0f00b8003201c0340c1d0741010f03070042c08030901a50801034050030203040c0c002241c01120680010403804a00b5a03c58140c500d002c025120b2500ea95000502403c0f29444800c030000d4404001c02072410841002c84a4034805000e01e00c1ca4200d01c1003400e4601c0c1200b801080a0700400540e850003500000380c0032502c0710005041a21074001310303040800c1110a04006098441004039840e80c1ca0b031043c000d0401480d052010341035000010342034855 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 890888588 1250 890887338 890887343
    0x6011101090506090706090807080a02100e09150109061110150b03070207090605010e01021c03110706051609031208040c0b0a0206220c030206181e010e1c 68
    0x80804089800402504031034101c6a0080480d040d601e0040200c81d2903600300d014442c009803401800050580001030a001600c16172000380481d49100d90800610100d10720004040c0202240b18410310350724440c080e44180070b00401d038032803001c2100c0010000c0781d854120a01f403019000d62042100000038200001150032000042e03900840308840141d104154028000841c0000c20818950780c0451130a0032550300102c2807080c182c980340103440c0212020003030307030060f840072805201c141d0302e142c2c04000714001406c0c0029803001c98905181a40d004801c00d903081600e80d410b11240008200780800300600c0c915020342c0a80c11940c8040e00ea4020100200403c00c4010101c2c0a200c0c02d4aa40b100030600c9520050fa2061145800307900c540b821641100c0b00030103a01c0015114482c0764a41c20b401d80e1200c4184e00c3d06045500f0003c0c03680084500c0c4102c0300003141005a0b685410b10044000a410a4005421800040014000c0f0b201ca00f00d1400b5103100c01145540b2180d01c202c2d00841513 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 890889838 1250 890888588 890888597
    0xb040312050f0d0213060807171b282102070206130305010507111b0121091a090d170402040f11040f1403030304140a05030d020c0c0f03060601 63
    0x40caa90044406010300d00a81e20800000190001030040f254020302d45065800050a10301d80d4805d01a1440c4500b2104040070903400c100c1b050b0711403511180550b11000c040c1c140c8603040840f00d06001160469400c5503070f2031901b400e19070000510714a8200a001c3c1c0c0b031070190300744c484e0646402c4400700245c00314003900e60081121011503903030310207480212840083c80c0741d4007a52400c0440c043d10081c1c2c0d40201041c4144002070702d1117000300341501101c47c41d161004102c0043c100440d07042940070304403081c03026050120001a0303124018411032034011400207008100d0300e28036001520000d0400c0341d980d81320030074400301d403500400075401e1103d00002007015035a4600103e0003400103541e0b1074046525042c454468030255a000c0d02c00d6504000c42196440e40350300d810980b4408000b800ea901d80e00500c00a400502140c0000022600c40b03407d550117138072a96176041c40d540000340500404c03500403071113207442002004060400c04045605a03a9440d040c400320352980d0340a80a9810030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 890891088 1250 890889838 890889863
    0x703050127020907051e280912030e03121201093b0d02030309010f061d060a03080f031b160209061203033408070822060b0a050a0b0403 60
    0x350045c1c0c1603450780c1c500c0e0f10b0164040e1002060910403980606020b5110a0f00e501c030380200001101d003006284070305038490f400c9642c18240245a5170307001c8042102085603e80d01110b4a480034424401c0078010302040782d8503030800b02c024401070001600011017151801204180e0f414800c441800d103e00110046190503081003845407081429005d130815611607440f040082c9a030000080d4031402627140200301503840c5070045000d440861181440c080c5010001e12030055000810b190400c0c1c2c010190020f0a54941e20b50040d81c0050391007091500010041102c114135111110380c03807000307445103545841154405030401507980c0710060702076140800004c0680d1200d1140c1c0503001c1c90081226264a810790f250005110780c0481c0f4005248615502503031060400224a01c03441d02c1d0315851400c0c0c0e50841e0450300400028031000305145c412042c00c514022594008034a5030140d103021812545001c18010300d00095480070b4000c00d03850104015005050041d0340650f90700010002c0b04 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 890892338 1250 890891088 890891101
    0xc03050d0c03090203160303080a0b031b04140a06142d0f0409110a0e07051b0307020d031e0f050703110a0210080f07090614070c080f07030501270209 66
    0x20103e0010003901845500c00e0310044440c2030040c0300849204e5074500da40359a40449810588444c24001038040c4d010800319500b440c0c8070040e481e02044041c10014129480c034480485001040e150300003a03d554290a000f030020a489042c0012001c1d0b038440039090729803120810030b060110151401d04229035032480039544004204803c048018410300020055003000604c4044101d005031141c5150b000005400e131990740810f1041e05507444031070070b020564000085848058900703804074082007001800507501c0d2401320680d140650b90344010440b16280800202c0950a00d100c1440078030300481030400c1c0d0040c12110519030505d80065103041d8880341501c0c00c0d84040000750301290941c2e500303084e5a03115013014403903a0710b0341b00080a611121019100c1c103400340038100008844800120b0030880201c021300405209044c03800085a031800d5880c142115110b5050035030300503c43c20030611030240584540321828103080501e0100c001ca401000c0201000028052681c81001911 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 890893588 1250 890892338 890892341
    0x902010c02040606030b031b010507080d11034212010e070830070204020f0d05010602060709140a05120f070602070603064707060c09060c03050d0c03 66
    0xa0254068400d003d090b40310400603001d8503d9201440c0284107100c070408000349185c40501208134181c65041c03802d86941c0740c0d0342a5912154a19240b01d0b00d4050780c1e40c0300c030004401540f0501d5544040c070700c04888621101040024030f82e140c60111507a20303086083d0004802ca4140c2d82ca0100c40d404094410168806d001d0300105000b103503031340640c070310029a440c00404e020048524110803000c14103584894a241200300805002c81d40e03000748a51401400d06900501d007100c002501d183c2045101e520300002e4075070980040e00160058800d00141c150080b0009011f05003004409060083c4100450042103c51040030f1040c80c14803880e4101800c24003202d4000d520300402d03500940d4680e04043d5848129102d00702c00039180030340000309805481c0001d000340401d09200304115000401201855581ea840051b151184580410403444444020000981701d50b901141c038004400b00030345003c00c9135125000784080b811f50040003d900404894203400410b04c0054040c402450860 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 890894838 1250 890893588 890893607
    0x1b0b01090f0e0c0121050f04033002070f0506100f080c1e210c01080709080a170409141e040302030a030e0c0d031101150b07030e1306030c0608010e0c0a03090201 71
    0x14a13807410080c0001f030401c503000c26200b035001e61a8000c01a00700c007440080065011151301ca083d00ea134400d01d000038600d40090030745902400d1024154503850321041d04001d8162296003110b03007550410084030300e80003181c1000b4400c0c14080c5c41102124004202e1003c0e0340075101e070314030403084d0704019203070740d240224030040808844500400303402d420f5642d540d12500200e140800d05902c000381c0c2051144a402c010f54500102410342c804150396143c0e602c081c5020241e0360382c0824400401c19118600c111041d090702e44000500f14100007100300c080061440c0d904100440c0c2108010120340c0010845111202da898005400c070340303000003d400c0064000b10a54060407461054040c15407104040c1d814071401c2c0001c01013020012038189860405104130110300750103001c0000420301441600c000340d20003800c0200384502e08002e0004550302900100c40d000c6d61000c0c1030042d5036100e64024054584110f0403051400c10700301c5030105000d850404400c0580300d03800c1c40c1c02c5900c500703000b4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 890896088 1250 890894838 890894897
    0x9030a02010e04060905010803030103060e06070f0e0a031407030314040b0313050c0d0f050d210e010204050409120f090e1504090b0906181218011b0b01090f0e0c01 72
    0x8001b1940c48421103a100d0b8004e01c0300b43c030400d0620904600040e80401d1442c0a081c0701d80f00c000700010019002e0f1090100352041c150701c05610100003010803c41d1800c009c500c01c005028041c240d085140140c15800300c1d03810820449000c2c001804a08540011250005003c800f400f00b1005180740c02860700201d140080d0700035244003100010008000c0e20601840d20840c2560070940190908a132481040d680c10305410003807002c4c08400e90b050782d01c84600146c901c0c00251074030340c461020405860300c400c8101d88103078000c2510000340303034446c0054084507003034600703000c100f441c016400f10031030b01c007400010382c03191061291402c0703035910f0340214032095200104100754500554800d40b50f032412030f502d5034030f955a40300141030190041a850b00b08031032508207034104100d4030821107283c5d031410280c3d8103112807408010341401d0b000e440001402c1c89200c54030a190304010304174040e0b0f0051a03200c10b6850400300c809041d1000070031001d04600d028a0f24000c1440a05900424080150704a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 890897338 1250 890896088 890896091
    0x70501020409060320030706120e07030503070203070b03010e1506040305101b0c0506040f0c08030409021e0304030c020d1b030f0c0522180209010e180309030a02010e040609 76
    0x2c0301c116980000c000c0340d00540900980d03921071a02400300070810600036501d90011002404401c4c062004282005021103001898001c4410240d01e44010340e0000e88083c0e002149000440c0b03400c10200028010b4544810b08552400c460200124006000d000602d0b450807100c4c1c18a071104007d40d4000c0d03802c04215101c6010b144070400040a44960046050343d40001c80d09546004d0749860601580c0440208142d5450380c56501c000c0e14540d0b4101e03030205030f40c3c40010b80d44800304060801f03000481c42c01030795548501504e4640709802128202d400400780100404203800c2185a003500340c040e20351903411582842d1003c5801e20011006001901000c8080b0500601c0b407c080d407501d100e0702c01d025079240c0350020014401503d184000081b450a441c000e0745090329001402d46c0104d4031f90401a9102540c0000d07400403098000f0b080314041413007085403200110908043c450300750f0020754078000d0300e140800c2c0c803149560401b9051000440d00310300e0b50b480300e5010200500e003c080 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 890898588 1250 890897338 890897347
    0x30f150203070e0a0605040503030409020706020c01090308070906020a03211e1d0c3a030806031501030c06050a050409141b090604440709090506060405090307050102 73
    0x3000f4040c8003440b1480d40c01a88190070200d1158095400c0750140d890050003541802d14104040005e548a0301c021996607800780414a028a824050604411f109131210481440e00010082c1009030b0740c1d00050441d4080f042d1074000c60741054090720107421516001110b07055105075040642034031085040065125150303041c40450f07a03484988900100250210441700004186941d43c1028140c254484035003940c00c0b004040500420b186c4400c8800c03c5100741e43e2070f4141c403080c41000c0b0402c1c0d02040300e400c2081818a81807007095410000c2214a50b035550450302c03544007450700e90241d0018014000741e9214503034090403d0b54001c0806000602c140003141442400c0203005903011003184c072800302056401441a82903034103018010301a42c7c01d2920340f910600c51070100410074060000c80e560a60783c481a515200c2c07840510340e8084504800c2c25005040c6066107941c09550124a003c9401d0300180d4007280b5103411001c21a0040360b680c031048400c0f4114030911200904a620004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 890899838 1250 890898588 890898601
    0x91a04030801060f09080c0d030908070b130b0304051f0905071503050709060e0f010c020904050a030e030a050307060908090918010c030b090f07030b03031206090c090109030f150203 80
    0xc192038140e5401c1d0380c0b001d5803d0008907042c3c0c1c5c00c003c030b4024042d035500014000380c03243c1440584003601702d000e45861805a540e0ba001141040b001d90010228920002600030a030038a070f6048000a00b1020f481d41d00d10701e060303107500c0d440741e40084890104c0c5840901c14074180100e9044020981e4114003503c01c419910b002c0d007480d40c2c45e0401d011021a09240000b2412405101c041c400c807240703501c544a20380324800410184400d01c034640707814812805210310150715040c03d40c034865803041c00184a80b15150401401c42c080003103403107119900002100300001c0c07010003943d6605612407008a820021340c0703400441c502902403c50381007140c5100304480704480954002e001c040345402005142c00d242021420b07140850440c641250f403443c0402c10301c408900b06103500441d549800241802c41c04000f0303045601c421412416070118100b03201140ca80031445c2d40c0c2181440c503c00b4901000c01d000039140504502c0f0190081c1246001c0070182b061000e202c060100c0c00c00f0f400c5550703140c1003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 890901088 1250 890899838 890899847
    0x4060603020d05060d030c03030c14161b140d0501020903030720100801030321061418091905012c150405030d022b09031b03080604091a0403 62
    0x180d010b800d900703083c80c011038410306041194100c11034060b5070311000041e1985060b4081c04200024408002c0c1e06212680d05030703050720107000449030580e60500102c042d42000c40c1c01c007420803101040d1400e40301041208148035149950800c10558219002c41c45d1810b0480c028001e00c2c070010740500002a80c4410005a101031034210107403901c008213180045400d0298120b1240360300c00124420600510220740a1015102140d0305220444800e543c14504a401d80c0e00a9109100c0d94040e80542c1c00b981c6803004125190968003801c8040f28a0300d010ba4590f01c4404042c0010000101511502400029046000b07944c0c2e21218102c0c0300084240c41190180c011070016095019420f003a102c0141450300c0180583e41050043d8113004142e00d100d802980304e130130500e03424440f0380c400c001c5e95408520300941003030005800080b52901800c01400b5296181c880b80d801000c2d07000104002a08480d54a400c0349080d00c0016242c0b08500e8510440c0e540810803000e040e800e00c007080308144e8007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 890902338 1250 890901088 890901097
    0xc0e130b0a060e010c03030e1f0608010b0d0f0311070e0c0a11030304020306070f020f011113081501030305090a120b01091503210c0b010e04020102190515060a050406060302 76
    0x81d102920080c0e6500c8040355161011079810340000c0b100084174011034400c2d0449080400c42100b91007070302496140001e94103007280c1b250416944c0b01d100070000d40c0400e00c58042a50300980e142000e4002d03643d42d15203060390014008051000300c10300150003200030000f280c050007850403a405e0500b8101d407444031580081c0e0920000805090080320300e4807010003602c5c080c2d41c2c0640101082d0722958800c0d10202480e08200c0114400c5540800448000740100071401c08801d60b220f80c1d130b003580049a00400d0068101c55615030184000c5100301079441803040c1102d8140c0b512503141c8000740001400240d45a00624101e5111821013007408000a00d40e41240c5600104102c80da030000b203550000c058500c0080c019448410000c5190454802c400100551a24084c030741c40e00d0130b0307440e850030310002c3c3c10040c00486044100f000b1941c0401840c1510b15555111014159103a6900c0c0c0c0d80c0c40f024901c1300c45101d100301c0031443c162100c00415019000c024010f012850701e50a004009401 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 890903588 1250 890902338 890902361
    0x2070503120f3a0b042f0903011805120c060f06060405133314040207061b0908030f0d0e1203070f08010e0112021002030408010633020304090c0e13 65
    0x36203a000801483e05c0d11410304c4503100315402a07460000c490b803039000088415080440702c8410820150295020300c00c0e5204401a14038408100c03c40f800c0c518507025914500d02a941c0c820040c030241040f0000d5102c2d441075075a000d00c50580d070b0342070218030b10780a0f075844540c001c030081e2912a0710004c0e0707800c140d401c5100e11000c4c3d280824030710642004041441150325188500101c06d10001d01000011803104001401c003500d01000da554000850389070800a0151151240b05140101d500041341c40080010000950030b100d031060825100c2e00c2a40700a60090341e40302d030100e5180c50305210720a0000300c1c0420941c3c481c40c1c001070241c880d103490402440018119000400e00340003005009050f1120300c1680f500c0004a0350900c500380304000d5000e800e505c0207100008003038109000d030b035000d0144001c43e156240300e10f0021898100e203403400402c21686103404006e00325800003d860860340060f83c08118950069416074100f0340100303d01d50400034450030110721250303030780100c2d20624 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 890904838 1250 890903588 890903591
    0x19051801150e100c08090607050c030d0c0302061503100501030c061b080306210610091824020f12102408041a0702010c02070503120f3a 60
    0x4244501c2140c6600507094010f41c071075100c90700c1415492003881ca0003e41841401300e24a42100071002540d81d81062801300d401d680049181d00f43d03800d050251214a0605042c01d0000c506aa50046c1d15800b0052080a5005904201022030756040003007010062020030700f08140d503140c0c142441c4060302d81c0039103070124030150040300703940071340800034400590031065880c1141c8a480c10008a8800103c0652100c1c0d403030080020441024003c031406030040c1002210b41c00d24058003c2c3c2590308601c160301d00e2113180143c2c10007040996221300c1d0100700304084070050f800c1c811441002070144806040004101140c5442022181c98229002d03a0180d050000c50355990008520314903580c40039241c0d2040340580021110b806404980d42103485800701d00c400c4411304085071103001301118a01c00617074541c1c04128005030184460360143c40145c0152448043d618000300c468840c0c20001caa09250004118a80d00040c44203c0e01184115091480b03031800c1600114200f5002d43c803880c80c0c070703 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 890906088 1250 890904838 890904869
    0x160507060e13110903031902060c07020d0201030b1302130305100903090e04031e050306040e071a1605121c02181207210b0f01060e19051801 62
    0x580540341d000c0030540028400690030003a04007031409400c09462504490000344101d000030b40d820710180c4031007025145824000701001000914002000c0c060840c0010200900c20140e00c51403040d041c01502802c000c910b460711f001c0800c0581041d081840b48182c070115085840840c040c1008007200c1c010030880709032108049030398080714800000203010403155801081520705c034096086c0d001d400b0b0b08089142191122710859444141041c50000071400010080c052a0900c95081d00c1e410407030050100c80d04190010407028800c1507551003005000c01c011181d1400480009070140d4050280c2c0c000210b80c00e0301d0240d41d08040703039480d09000341c50002161580d240c426907541110145a00300c041e00c1510a000c56243e024104e25054010a900416205040c441e02842417500ba000358890f45900d0a1045c190b180140401e04004504001000300a51048014030340202c129403607800451a16521044c040c0300b0703805190408040e0241a07043e0340e41150440c100c401800b403600c1c04 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 890907338 1250 890906088 890906099
    0x2010e0303060a0e1504090309090e07080c041806090b0601120506030a0803091e16050a141507120c060f150312050405030a080a02160e0c0702040f02160507 69
    0x907030000300c0b40240c10804a08080200015841001c0d42040e002c80e454405009880045025181c41250580100b5010001000702030458071809070950100005882c125050101d02c07a00c400031038490601c2a0b88401d410345044008609403101d0f10b40c081d20070415070030744d8035180c0006981190020f02280b45180c1d0128030810b10b0084c24401c100c003d014007010301c000d50f114406900083c1195110748640d404402a000b517001d8459150350301d29000b8103180002581d00502c0f01c1641c0c11480c0240100c040030000b68020b201032000248040343c002c100101592240c54840c052034001a01e41070100140c0d5482036000b081d0401202e00036502880744c24003003004a0140c0d51160a00c800c80d4002c51346c1000412949010a900f005a03858041e150650383c1300020306e070900304d07981039542100004c2d10707809840c1c041004010b90440c00040391803407450320106c105500d100802c80780c5d180c100096800c0440d13540b68807290b20790f42c127003c1c11501d401e007a41d82a61620b0981c0002c95151040c0c1402080 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 890908588 1250 890907338 890907343
    0x6090608150405060604051305010f0501031b06080f0a02070b01030f060b330d0606082401020a2010030b090a200c01090c081c090b180a032102010e 65
    0x402c58000d0024081602c4007030030700000302402080703000000203040c20071001403020b004003404003022010116541d41541040a050145a8514111991000e08c100082500701c200c40741d0000890006010580c1c1d110600f00203846400402071070020070b0381c004010800b2a001c06ca44c4140180f008111030702c003c000340002030150f0380780f80d20712078070382c10711111071401c2460040c00f524403c02030182007030394010741c03041501c2e140c3d04060046100042000f01b69156440741103641c83d840c0e0081c00d1182d94400c0041e40b10f6040ca003016014411000401102500340d01408021030360103071400c071144400c0700c8010000c6c403000c08610310480d550030210300d1107509400391031062140000540550b40e4000e00c0c084155004002d10b80c1c1d995285c3e11900003151100120780300501c01d0001030017a90714500012800120044001d009101140c101404452000c00a6071310016001c80704e0622080d1520002c3c81006e91503000500c10110a0800070702c020b1941207400c00d540d0030350001d00c80f001c20041c2054 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 890909838 1250 890908588 890908591
    0x70201050a0603020916140d020901021c0f0c0807050d121a0102031c090203011103070908011a01050705010e0615030f06040f06200a23070209070810090609060815 72
    0x9503c560301c5d9020900400e405140070000c041c1d14200740340400301845da0100036800500a1198a03540810041060350701803080580b00c2001c1da0900c5414051400d004e000ba041d800f080e40208406031408030104092581101c11035a0002d040350340000081c2d4000708000c2c0b54081c40b506060404800d21a07000e0b8814240100ca00141c000c0c600308034071040b4031400f40d4440c2c0c00381d944040c0c58107690005614280316803541c040503e0710142c1c0d01d00d0800c00103441038402d50f0155a15a00d851180c4050820609403044d00340400d2a140e40c3d9007002d802c0550140c6030520303a00205010390310510851482c5200311001001d0260140d80c154000344080700d40740c2000716000303010300c0c000e505528006041c0e5403060000181c104100d945581d00e0400441e4203030028801c41d40803802464020340000c09554521aa209100d185c0e1840c1003819404690441c602030990410300c8070700300120300e010180025210241405a00801007156242c2400e4081e000501c9408564003400c0f4960700d400344010041c5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 890911088 1250 890909838 890909843
    0x60507051e0633010f0e0d2003070f0b030a0f1508010c051206040f06080307080315040c1d0102012310060306080a1b050901120303050c091003090c03021206070201050a0603 76
    0x110404000c0754011340e030215441c4104006c00018020002180e61811140d07140c2a000d0025214200882c1c2d1030490460600c126091180d8894070301004220201d805800990304008111500c0c0d0b1699107402c0041e001c0d01c1208241c0501302140301464041c4100d01400310303507040c8002c1c0310003800c8200644591003079055100d00c000f491130000c0c400f81403a410160030303000344410004080741d0781c20b00e0600310f411031042100c40f82000000e00c12072400a01020b600078500300d90411494004500261800a0b480010083c0b410300507104036a5a00039840083c1c8044100260000910010040e115680080740e904c0442010100c0210340c05201c1e21580d270030381d0b0074000181070400b4a500c0783d90440b11600f04140d0303401d02800340030607183c0740e03014524002c1c9071641160f01107550a160282c2500c0005044c0500c2003010300992040e03540e12036107940c4601c62801e0000c1da207040c5080c03403600c80880e6007020b5040030041c1c0001c40c40d80c000203180c5225122950080015490707480034202624000e1001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 890912338 1250 890911088 890911171
    0x708041709100c05032a0f031c180b01060e0909070302100503090c0a090204150c030504180e0f0705090106080717180703050c030c04090507060507051e06 68
    0x1000c064600888000c0485400781040701c0c105003203480101280d161b5041c03205044c242d8460031030705080c2d0170005000b425011001660420100091511127001c9010b0501c000b80d4960b8450204459a40740101405400204800c04c641e120340c0064400030040400e1805140c2c8180001c040300404500081620390081c417214486902e1141200c0ca81c00140c0340340e130702d801081e66030b030011303925400700e0401803403058005a112440d0500c3e580c4c0700611021000140081802e010f400664040c0c126015113000d9041e1003504100306a04200421002d001030104c0e1107240d902e46982007000804404480e07007200d000060707a80340c2104483c2400259031a1000c55444200800108400e5000c1a4007080c0000381d40c403101034040c0d8080ca000c0302d82d0320a84690300000c114095904052182084000c1c0985090004459590ba12a980d00c002d12503441003000100300c1e94100300d000e00c00394130700c805440c2034100b0301c032024603106803190000d84150918034009807100400c3c622405c0750300b05148203000d1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 890913588 1250 890912338 890912359
    0xe15060f0706270b0406060e1317090d140d050c0303242d06070206041202150415020d030b06070215160606080c010e090a1a090708041709 61
    0x60752009401460700035034a01c064001d01c1c00c0024030390380e0601c00c05402481005a1418175042440499015800c1301c0840113500e41042002c010550915109070750085101395010000d185018a6004811105d507119400d000c0c108103104102000c000b08880c1d00d001e07980f10940e4038109032841e209070840480369030000d000207070035610f07401e1b50b544581c0300200380c50400310000e00024008283c5521002c00b01d80884c401c0e024010594442ca40458070141c3d205403a1501c0f82e0001481d074090b92058400c2c0003410003c1e40210740b65240903a034140c0481181c9521242c50380c003c455600c125404050040c420460030001d014407c1c0500006000080e003074a00c0c1c1030454081c003180142d84441c6500001041046900d00e0090100210903680038000c0095554103086003542040454180d503410040c00d0914202c056480c10250f54011032103003400208030000c41c410700c41c05e4000d0324031154004405020030202035006210284180c0c40340701c50318112908003103a08902c7c0242e10f00a501b1524061 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 890914838 1250 890913588 890913593
    0x1908090618010603080c030c070e090a081c020403120e030c010e0607171b1e070e0901150b031f0e0c09010c050a0501060e13080a270e15060f07 63
    0x50401c1035498484008244a034882e210040c840e480201094a694000111403590100a01070392018144c0d00415403958203041080e075a680716050030151552100240c0701c4090321600c1e40e200b68010314104199101d903580d003801c45103070354140458008903442c1c2c042542145030118045d81c221405071500311030304200405119050b0401003007180d8096045100c02c411580c0c1d003025100a8032078560603c44d0147c0c0d40041410411000c861802d404003044c0c2110308610040707168410764440c80304e124001d90f140300384c3c82d01510707910441004d55907844001041e10752030715004601c610280d52031401100d501e18546030340135205209858041d20680301003200d07080448003c00d07000205140c046050605901c03481c3c02d00600c98000c4415039540c190800025000e01c000300c2d800030b0026102030310207a0310740b100030503880394008060802c00004000c10f400c0c07055440251100002d0302103000e80c0f94448420103001c60341038a8107000501c00c01002c03941031508500322585041109a0385080500d80d6 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 890916088 1250 890914838 890914861
    0x314040b09063304090c170f1203040303020901021207030f03051602120a020c120102190c0f03030b0d080307020f190c0506130e101d0402010818010e0f010219080906 73
    0x143c0c1015442070f00c4041110205031000c0c6100f000e0311402c1c4e00020494500000300f46005a402110b09054020008a410b2019010f06980d07009030107040141c0c0d5000b0013070040f81484031401280c0840000420348805040c1d119600140c541011f8400300301d25104d071a000c3d000e051072030003040c0040e4450711142d840300640714040c202d04a001c0c011154540080c0d0700007036801d069a00800e0300c6a601050500d0620044c20021440007440d0802000500755030f242c1e07900407801c2c0b42014040c1500e40c0c101c20120b840d50f4a1050b4116080000c06480e800c09840094540e241d80044483c5442845100300980240d11661368100c1ea0004d1100d00d15131820081c04004d8014407291012520000000105ca503500b41c001449201007170f0504ac502400e083c00343c4040107002801c40308047c880070801005076003007220650001480255003410300d4030284514090070200c0100ac0982c09444c1c181d20042c2c2054002c1c1c041b00c500d0a0301c030300a00385219000c444070001290940c1e03450703010201003501c04406 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 890917338 1250 890916088 890916181
    0x6080a0201030c21020d0b0103140f040507051512010b0910030b04060801020403050307030207360902060a0201061404020f03011203270e0f1006030c0314040b0906 72
    0x240d09080b200c10324131846240c5a9119042160366054000541c842c0c4994a440303980f451030350900701088403900c0500031200051004003100780e1040ad03a0086421f00c9410004080200f41c010884100f0b05c20007449591160003110341082000d440c00c00214000ca00807081d074118150140480010009045003140500800d0303c169821580d190004a08100c0a000800165004400a560702c1c409481c0003172404815070301039a600717821141da11117000d50801c854080008104996000050056203080043c103409030001d610010000300e00c0c60064041d0050301c11104000801108290a0410f0005034403409100d050907042c10070052148074041c45100010380d000e46010744560654030100c089007100f13403034941c2200d481d4203020004480d02d1035030b06174070040307140700380340b0703a0501080181c000c12450042200f0305440710b61410202e0701c02c1c0e00001e548211140f04903c2d6052904018200001c145c85030101400380c42c002845070034a0546104034040c01c04441c1c4a24000c2c4400c0b000e0000c103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 890918588 1250 890917338 890917361
    0xa02090f0f060f1b0a0302061e10090203060102030d060e061005090f2b0602030610030926090603040c03050f07080705130f020a110f19020d0809030a060506090a06080a020103 77
    0x152800c4a00d1030385403c201c01c40b91541b194004100758245204000c159940c284260a50b03071440208010603024a01d01d800f045582c484000340e103c0e180c2200503802d40c001c05d400b60340307214905000001e40c403508a030a00e001740400c2d14101c1c0407000c030310310803640c0340700311740180e034200c644110043c4140c108118844160354141d0f40700f07034850800d0440300d00c610381240001d8071590b03000300c18809c04e450326220544c8545d20a040401060b001c554403502c002c04420192610850000c56116044817001c00722540460010203080c0c1d24506881e102c0d003011800d02040e1280d11400d801d0301a100070000300c2d207060f210810700130320206181004000d50b90b0001184001d08549a800b103000d00450303400075141c1d1040d1501e0350102c48400103170540c502504080c04100a600c0030a0f1040795031040340404c00302d42e40580c0c8034280f85245040007034407841054074085d0103100d40c2880d0024014254001401854121501a103986804e104401901d030240900045608101d00010066009900c203016810303 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 890919838 1250 890918588 890918617
    0x10e010c022101180503090312360406060c1a040206071e0804081c030c0e04020c070e09030304110a062a0210122a12060902030a02090f0f060f 63
    0x10a01071182c00c1030140d4540c1240e05d9400450340902e14601440040c8036010341403245400c04006070300c42c8041c080009800b880c004000248018000d40440401a200101401c240403c61759403100030300341c5403145016500080320f411480c0310050a282554012a00100004c0c2440180d032500040e10581d40c1c0c880307414907181c02142000400340b030040c000900d40007010306160b15019140300c82049089003480109880e0a03500800d050f00030202101d100d03015030740180c40f5110403000354034068460f00200c1c80c000e217040420142c2e0800000540c4124803600b9030700b29400d0540c0034828a2100742c084d24000c40d10303148030203048410192030b105881c0d444501c3c0410390081134000c16441040c0c8504071000414003c2d46407401ea843e40104105030070b0700a05200c1052290861308031400ca140c0c00c0c0d0b07040040041841e08080415040030004e407007030010031076807401c04001f400c0096110440d60341c084e40c510b5041d24000c0c9400000302c0f03140703800901800c1c038010001401c42c506030b101503032841e06031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 890921088 1250 890919838 890919851
    0x30a12060905010b091e01080a1a0a0807080f030a0c0b0604180302010e0d0801050d020d08070b07030603020f060c06070809011d0a030306050d050a0201080c0d1a010e010c022101 78
    0x65402e00a441c0280160f000303907941c6000d40002c0c01000c41c4c8081000d600644d50060116050741e02030442648007004440005030007007a0380c2401907041c0c0000000781e00a0010308081009e01c0007085107800c40d6042c4044464081120040c05d449000d104108408034038500311600108002480301076100a00810011711036200628521814600510980050b0354840c201020141c0400040007032101c5828442410341c5841c00065180714410b2000307018070a055881410009044190361215038032903031849584c07903c8500100240400c3c402a40b06000b03c80c4242c0310b900b407030011500307500d0098014020590f00c00c1e0003943c40b03600150202e40782c0e40d611500703032190031010745100d1010242c04000d40944011803c000f016602e054000b944520361900c00600052800200ca2140d10750a00b00070303c1e160388016000c039442c0101e0210041090501c0b0442d65180500a040b00320240700740c07a005400c4100c030700110b607c03150b200310094009202c044440c00012084480c0410748681c40004181c2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 890922338 1250 890921088 890921099
    0x7090b010903050a030f02070f03021f020c060409140a02070317060a05040e03130803040608040f0309120b06011211090f060903030406210c0807030203040501060806010f08060c0408030a1206 84
    0x51288200051700020385903001600040d0741803110500030002c0240042501e8156000100f11110000590400d980881802c02d0401e00230b0180700c045040007407655480f5556030140720003034050510702c2c8030421201000111034a24510070740e65001e80558a4120311280340c0c0d05c1c80038606000d01450303480003107904002256942d90084101110b00342c0c3c0a552107200601410a050059410904981d001400281300d40c6500c07014665001d0740007401c020180300c0394102521226000e400030768954a2010019007407045501d661809800203a03611103c01481c03142020481d0704030f500010066004100c002c456141040d401c61030350a000f03068514120b600c4c2c0001c3d00d1944168001404245000c022450400007607000c1050342e6240101440203403422400203103542c80040094007816404008242844000d61005015081540031115596141d0841c4081915148145944c5114140000e03003204e252078295002c40300c6540085080051480c003d591400000c00e101c10410740d11900010b0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 890923588 1250 890922338 890922343
    0x32d03080709082a0f0f060d0e01020a09050f012307020102120d23041109090a02040606180f080c01030507020f1009060506011d0411040e09100b010903030207090b01090305 76
    0x11400d100040d5003203004483c40980744801000300340ca1280c2c0071900c240d4a1740c0c4880d05e80d6480c4003c21607100c2c0c0d55142c0c0c0c00707a0100a00c007003040c5107825840820041d58039900319038028251201115010f401c008410b00446407a122034501c81c40d04541c0c5501d0716228004000540103140c4140140c0d1000a00070f0359000280d004103900218071600c6002c0e0441a0781400c2220803100031103100c0003220b1070640c4480b02c0c0b107240400b001c0e0180d019003000613070f00302d020302c1107140c442d5001f00f0500040c5d03940d9500900508114000c941c000080703140008805071000503010803030348500054015010300c280154001c000051982c010341c0124110010360140500440500b5061400001025000c030b0501d04201c4e800100b00701c1c1407200c0003c0300f03c007850b000c1e14103e1804504480204009104c80e02eaa8150b01880d80440d04001c8890107224010002050a00720162001e908011001000004450100080c4000b03400b6800a03403062080c807070560007850001d203060415110700f59407170341e4061 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 890924838 1250 890923588 890923603
    0x2101090b0f1b0309060f1008010e160f0509011a070222050c0a0c140c10030504060b030a02090c0309341a0d05040c0308030907032d0308070908 63
    0x50384281d4071040015104018881944210a00031540c2c154070300051200c0c2c0d9600c0150000d0400301e000c01c0014900a00401c40034003411034000240710288581c8a1103645101d0307059000711400d627042002c115647c03204000300854000401c41044d50340380c024180c44440501c050008005030820411003d40ca5a1000303104080e42035193b10790f041034800e10340c0200d03400034091400f4080c04200c061203a991003203004500c6034200703c8880a030781020081030320348040d200500c5c0d000070411560500e0740750035501941c0b00320701401c024002041c40108242c3c80303480040c2c00940c020304d00c0012811940c00c407805103a100f214038003162610303100250800d4600b00a85031a0503103141d400e600aa00810400e100310082081c1c1c00c50003541492808003164a001d207040c0400890b94500000381030180c3c05003228000e40d00090080d40c0e034141035030450b49070b07501d9010a5400088001000c203c201c640c0445918000480d180b814205003d44c1e402c84204502070481001c01c01405404140c589040c0702c001e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 890926088 1250 890924838 890924851
    0x807060c05120c12010b0307090f0906060e1c171c0b0f040921050409020c1606050a1e0c06050a0b03160308250507030f03030f09022101090b 62
    0x10b038544561901c954104a4010a9803c0714241480703103220745031032002e1140c15550503c0700d00352660307100d2904665050340c0c0d0340302c000c5150f554032001070712203c107500c00e005135001940c454504a0712041030080c40801610060480003c424000c004140d0400344110507240c5007291920f400c00c0120015159a40304e03c1f5050066a1148000e040f860f000c0a840072202e800d44003802050416252141d851004500a4404410300d034410203416108000b00d0380a040c40c280219156269920740942e20b440300b84040d07031043c40c0d450001c1407203030003039003030f1040d401080d13903440d100c1248695a084e9404032408000c0c144102c41d9500c0c40065541d0048500c2143d070850001a11541e4908052500d8005076080c0c014094a560500108208c401203860349100c070090031201074458070b0401d46046414401804c00d018410f40072003081900741e100c4070458001c2e5020300c012411031801000710b0ba1107401c02540400404041300100c06c2241c1040003000c02e4a00001c3c40641a8950030132a0000b1101c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 890927338 1250 890926088 890926097
    0x1110a050c03041e06171b2d0706051f0605090f0d03030504020406140f06210a060e1605070b041e0804030213020c15060303130801022817040807060c 66
    0x24000554001030070846d291441d02c041c0341e281445012450f840e41081d11030310382520009203404015401451913140d821050200d01490300003120340c15038503006000c0480e440c50030700f0040b0300a08142a949640000c648540746c42a900d8070000342c8042d0f204903030040d0821101141c1c80c1c015070306c000800008502a841c0400d240c94580f041000b12691500104400c8041d0781d01529183c0790300d0000004c4040c10740e1b003242e450a008504141d400d40ca12808804014140304202031481d194100508a60b0403407180c401036280d4165002a9071110b07035139180055420b01890020800b2580c1c120340050003045410031403001200a0780d00058030850a42e00c001c0001010802c500300441c111624240500c821410701d8035010083d07413903042e8460402d03070f044a403601040440e07805200b00c0305101902c820240c9001e60f41d0303100f5030207500540c0da00700b1082c05000c8003607000c1c054010311512200090352180e242d00c0c05103003208501900540180c1d030550041c4014000948148034512400001da01d8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 890928588 1250 890927338 890927399
    0x4170d0f05010603091406070926070602031206010f080c03041a0a0606080a090b0402120c0303031303110c0105030a0c0918150603111b03090406060e1201110a050c0304 74
    0x2031059107801c2e00c0c0c00b2010a40d0022080042041c1d003d100c10013070300c51800c080072a03003000030583c22004181441c8ac1c00304d80241e0400003071080c1c000000344801d5010b0781d0326503159680c00c00190b608601e13481051001c07512040001d08081100b00055600c14420403a0310705400c2100d4168003031002c00c40d80c0e091a42e6440c4418000da23a0800b10386940300c245c03620f0600c41c0d29420740d40e081e1003100140c4028002d2083c00425240c24400b400740c14100c0d000602101d80381d15107840b02d0030f4005038011042e004034520411042082e80c011507041e0003584107844451840e00c901c461403000713040b000705000800c0044000480c4001e14400039607042e5982480204205500200d48142d142c421750168041c1480d2046124100743c0400a444c01100c0ca40941080c01900d0042c66096124600000717620070703d00240840c01c150011480040102c0035183c5021420b04880032900701c0f1040c0818807580003007440702e80c40035445440180421a052001e6904082e695501740101d40c42d805080c01c1444208a17 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 890929838 1250 890928588 890928593
    0xa0f1212050d05090708160b161502030f010510030b150901110303040812010807080a15060522051305060f2a1903110a080a060b04140f03010504170d0f0501060309 72
    0x4140d187c1441c003422a4aa80d40c600071402c07800d44a1141d00c803c4900232006440240441241440b01207480000159503030302c1d09650403012a4400d0080a100e11b800e100c110780c40d188203201783c1148880c090b01e014000008000c09007841d4003e403900c0d5040244020b061600890180007441c040d5126090958a442092095501c200e1058018126507401081e00300303c03500000030351842c0d0f1908a420828105c00340d4101c18040c1c0303030035000540c02401507000810b045284101e085030f00d054200042000e611600744580070150782a0001d0640c1d80000d0105404858412005400c6280c0181989000c1d0582e40f501c3c0010344401c514524a10740464480305642c0303044020084110035107003c001003a80d180029140d80a0107034441c0070031075504005801e1000e01d9100314042c0c103042104c1c41c0c483d5900c40041030074241907903684e8000c6c0380c0d9040c10411400c050040d180540d03413080c1d042040f1014219070f1007607a04644e5585c0b001036220496014910413600c40d40b03001e4101690040b03400c03203550 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 890931088 1250 890929838 890929843
    0x61e020c0907080406020f03130606061b02040e010e1203041a060a03080a030f11220503120f220e090601060f2019020a0f1212050d05090708 62
    0x11000015904140c104040d140c1e900025079901801d5424048207580340e0f410014003d0154020019410710008140a880030280705071761402c46c0314a42c10300501e0303104c010440708540707820f5024100c0c0c4c2e0301700d070040010f1a240d00052000200480000346518500c60382d1850301c00380800300d100300e4500009000c1444290300d030b05007032031060042856540c1000c50100e0250380c407500c405807469501007101c203440d5110b5040b040d1224484c40d4240030001e41c10705100401e40c801d040001c5960700c0009040420031403043c20034100e031401005041500140084500c150f4030041d101e415081042180134042c2b5042003198001c032740001c00c680105818101002520900580f04260356840075004000e06540402c0c41c00c0800ca8a18107402c1000040c0c1d002d80070900c90100078006401001400003564181144041ca664004c07215000740981d076410400701e2105a000310700101050711050008036140c2d0403003012810782c614049161040304180501107071400c0c0c034070f243c561f0817040e020000030104 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 890932338 1250 890931088 890931137
    0x40c111b041112180303071b0614010303050408010b0103060b041a0403060e03090a090920060f0304110405010506040602030f21090724170606070503120702011a06030a0f060f06 78
    0x90034001c46c41d40c1855a000703000228184491480400344c81d00312030070030000f80c0251061607800100000156102e19000d0500c1d00580290846980390016a0900d58828001c1d4800c503000110410f240605210282007804d50b844182424102d0801c0004000354251003840b00a00c04100510b440c0c80e00da03010010000b4050b40440015800c000020001c54102c1400705c0704207251103480300e60345900902081c103a01540c661041414008000c03c0244130100c0c2c0b00406100088804011503078031441004850b00807802003200580c824025903080841100080c002c18840f003601d9000c111407180349514a41c01100c0c0002141c00944080007003448d18003401b41c84100b50307450740200840c03034400280f405800c141c0f903001c4502c01c01d002c80d900b0b4885008454006400005496840502221030100100c00b546c0f540b006601e0301d00540c548218075920301203401e900804151a68652418540c0500540f211500b00700c3c0d551140003030a98003665501000b84501d1310fa40a200c60b0340e0340c3c0d200f10b10b0b01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 890933588 1250 890932338 890932381
    0x305030909060d082713020408120c0a030503090102270f06040b09010509060c0a051f060308040608100e0a0b0901050a03020303040b07050c0a0f05040c111b041112 72
    0x700c80107400201c0c900183c0303170b4500381c4d581d41d00803d91007000c9040110b580307240d0054011490802900c00080103800400a0b94074003400c039030001c0000300c014940341c481d103240303820750350002419440003912540082d0380000103100054104403158840d24044502200c1403400c10803103951140d401d050106902c8507a1000311016401c0c01d26260003a040743c0b003103c601504110001418000c181e4441094480b81500d80d01200e5140c002440c00d540d41380010004413005504003c08a040c19005015030420340798460040ba04061034858140c0300c1d0321000e02180706030b461700880030409540010140e84201d1240c840400c03004818400c1c049240b0040e0085e9003d580324810030310250724000207da007114002e00c050760b5584260304200c2d0600b840424010345c020010400054009050000801606c40c203e504100d11710310400f0075552500740303403507854880d0081c001902802d01c4905001c1091a4040e0000c03900d00706250f0004615030054400199103042c003028000741a80e204d004100508 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 890934838 1250 890933588 890933599
    0x903080d0e0d0206100b1303080c0307231509190302060a0b01030e0a0b06150a211505010e03012007030e060304030c11130e06040b0a09020109030f0615030503090906 73
    0x1080f4200c0007030710302540035038011171100180c041e04100c03261f585040159040300409407034000504e1030235102d50140e041a00d05102d50a842c4844a6401d40780d00614480d0200070b2080680c1c02080b42400d00c03000703008060500034510111146c0c06940b400e07203903451007940584014034143e80d035a0104c0b5000c0400d54101032500c5060844190000b881480751030700200900050743c3c1d920b000400ba001c103581003024186001c10590742c401c0c2c0048880c4215407400142c410745441d0512080700311070038041c402114484522080041d9400740b001c054800801030700119044021610140704c0f2030b442c1c010307084c3c0c1200000300e45081c1036100b240c0303c0808108950302d82c03542c242501c005100d640c102c4809000c1e89494101c0729a50b617183c842d40f4841600040050200e0350003030010980303801d011101600d0201004001558000c1c680c8a124034042d070584036110700c01d0460b12094080261000111400d603594003a100b0300340000350790f0b600207611900c01595100101024011041e4000d401c09000301c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 890936088 1250 890934838 890934841
    0x603060b070c1404092307050f060d0c0315030c1d01080d051602180a050105030d0c06020d0b092505030f0a1a04110d0506031212070903080d0e0d0206 66
    0x10842d03003069007200c2c6800d440920f200385441c00580141541e400003041c0f0b6048081c4058000001c070b8540c8903035450141910f0340e035507650040c4514850180405a4450307010410001c242a241c1d03c42d081b04591454001181080541034100040054200303441c0c0a80303000c0c0401c4603400ca130b01c032001100c60445c0100c4681d450814225900c900d40c3c40d05005003d0041041903403410340c000014500c58000300507000b00b01861010700c0f503081069480700009402d000c0081400e060024088640000540c0e86980b001d802e611036500a400c040110800161a1051022250b07515120540200041d28811642d000341590004810b80c403000458107101041c420400314840306c200965000258017400320700000708244010f9840110a076183d44949040340403031b002403000000e0b1140b80a000020883e9071144c804041c0e85410018003541c210304200100107001c1880d140158003c020743c1040ba01c2c040d102d039940713406500305070703500ea240700d0f80c41c0c0074401c2c2d0386401c110714213a07103910b80041e0160f03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 890937338 1250 890936088 890936093
    0x15030f0c0a060c150603060c02010b1509010c020628080a09170c10060f180b060405270108010c0801091401060f0e09090102070605071403010504110403050d08010603060b07 76
    0x2001440c442d060a2012101c580800d004581000340454681000c007000303c42e4507481d1a200800f18080e598006619003111010b603820810302c4800c2000c4080e2042d81403030003031001180c44804244040741c001c5400d0000c56010309903a8400c8028802100e181d0f41301d000b01e480c000740001c00003491641c0703082c10601c800001c95081301401003042c2107000003650340c1c540145c0c040d29020346a60000c4001d8540500021502034048510090384d0f8207040da5908803451201c0403050725807039414907521100c208010006803518140d01c4030140c40145a003041703080c0e05001001c8001d0240e0280026035180c5160384400390380041041d0141a200030208400090080c070341c403844038140a0001484030a14010002a00070022030032070b46001400d2010918181200c2c0e03010f07400c0700c44201e40960803c0b0110b60038500500d04071106070442c01190741543e29017010400908013100e150009040b0400020010610030b1001c514008203a46800c1001e500d8103400404442740e0342d020485007241400301400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 890938588 1250 890937338 890937349
    0x2071710180c03020409060905030c060f0c07110d0201020a0c0305070509010e070c0605070e0d0c0302100509061e0d020304030c0209010b041809140d020d030c05030402010e10030b0915030f0c 84
    0x3c0c1c90301030f01c0000f00303000c003490020001c0085c0c45014005200104022190340c030b0000d080e610507980d12041a00580701d440210f081d5000e05c5130018400f9000c59503544040c20561703600304920380144101d032042c01164440080001180c0c00c1502c2640104a091003d82045940c0500400d0020400100c41c40c04400080c1072424405000341001d49400104800c684a20110440010024030703440c011502e034074007000c0980c010320080b0301403002e500d14058040d00460a452514070701070106880c00d44401080c883c0501c0d81c880103600440c09116480c450f190910145200740c0c80fa403a07182d60070078240100a4101d4050b400f80203a0b00b401c200c140052002d15880106903403058070045017486491801600741903034440a01d49a116000442202a5000605500f0303000c403618104211021048115010321048034040e02003983d80b0703130306203290600d4510781400c645030385000106501c1003c0000c0320920142c031500411007200d4183c20301c1d440c1c140007482800c900203008203600400c0f800441d2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 890939838 1250 890938588 890938613
    0x1150e010e010c0314181513050105030a0e070b2706040522050a09020111010608070b071509080d061220030703060509011b02031c0c0207171018 64
    0x90400881c240c40c0c804050007013812080540f4110202e030f48039640461070050407041c0028051040d10000915a24080100c7c221202d00b00c80710514240542400c1c019a600d91001d00f607a01c41c0345d40c0d0742c1540c004410911801000d040300c2049070f40ea421048411200d142c660000340100d0351418407800341aa82c0341c8040302c040301e800307a40c0007000400070700b041c80011140c181041421420202001203036070095020803200741c0700b600c2e444030b1040e0300b8200908858030f42c09030824a500c050002d0003586125030107000721501c01c41c214080c284410410b0310035246902001c44e0665404542d8a0b0314003410b000301c1001e01705282240031520026200d074443d49000c049021007c24011100201a4a050202101444d00900c05001c2418002c800900a00348000061002c0e445825085642840442113540d044482c0c0500300421492028020003040900c014170158881c20070006151107010b460f07660147c4842000d810310009841e501e20544d00070800380c1500010401340d9400041c541000075 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 890941088 1250 890939838 890939867
    0x10e181c110307050a111c030e0609040e0a0b04050d050a0e06162913030e04050604150905010e0a0603050d080a090822080f030a0c0203030f0a0801150e01 68
    0x30761030380d50014070341d05600c100c90001d00517004e0340c0c160307405006400c40c40e01c811060a583e07107000183c1c2d80504400c040c583e603100400213640300c040240189091000b92401a0004100149444c441e08045180400c20a070494501001d0303020001440310501c8010031030a207908000c0c0ca0503a29030f038020503481c42258254400e101c007003503201140444545540c02241d11000049103403460412010281c90000400c41d100c2c5610710009030406505095032546681c5038940d040807213600c00c01c00003d0080145426000b0780e80780d026907416a8107034180c80c002d0111840009065040540c010780808009201e4680d41d0b05258041001860000d901e410740080c1e8905400c003501c4951a10f0050080f0450241c0780c83c03c0410018003841c41c49407101c0448801580f000341c02955111001d4684c0c00c0e440500409810901001d00b11500681c0842042840207041e64580340c00f920408006810142903000000c14a4005101420380c801c00040c0050080c142050301c0c80092000902500150045 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 890942338 1250 890941088 890941097
    0x10e15090603070302150d1424130b040e19110a0806040f0c05090a0c0e0910090b061902070302090106080907060f031b0f09120c030803040203030c0303010e181c 71
    0x80745040004181542c54048901f282401034005004040c01c071004290340311003c18500e031124183d2400d020313070a0b65030600090300341607040c40c08400d14001400880d60b02e58200351101d483c0710300c206c02400080d54142021040904551003030030140920030346034842500903450040144505180010501c0d0b1041c1d01c00741032080c4a8035850107448901300c96014a810801510030300001d1070300c941003055a042d4540d41d40c005210584100000326200740c030038070644000c281d02840b2807202030f00b0610740c03000042c140030b20342462020000d0807242c146041c200140c10503070341801149800c0004500610942c039100700e06090142030142c031103078148603da050104031441a107485000e5085031000581c00c40d00010703090000e0401a05a90b0b941d01031000181ca02c00011806840b011140064550022881d11000e4110754880e840c03030348003800607641840140f100290402d0204000c501074205148481c03a00e00740500004075158800c03180c852283c00c64040c03669408003041e036500807c030035443c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 890943588 1250 890942338 890942359
    0x1a0301060b0712090806040305190503060a090e01020903150108010c080c220308031305010501060c050c0405070516120905040b0105030a090311030c150106091a070614010e15090603070302 83
    0x1c00c0c1d40c600e009174042c800a0040e40c0420040c140c0140c05428203403204600c50701c0700c02d1030242c122031030f1100b10751f41a40b00130008014084e03054941e01180c0c2d040b0106000510306642000000d01e4455041500843d282d000c000610560b0400e01403411001043d040c840001c2c10612002c280030b02511459085040450072544107984401504000458200d07403581c0d41c2e030070141460824441d2200303054a49600307002c000a070040c891480c06003082c0d00080900b1a600380780d001c104c003400014102c3c10401005000b48041010050b0701ca03030b0818400c1c861042d40c03000911001c2d020038000d5005a200c0c914002990b503890740c204084030b9011804d4040020284201c0c0b8040c0c48031460941c8400a510000c00c42c040a0807000a600741504400e280e0001c06a036103600880d548455802070a041c040c0022000d08070800c20406489080d1080d0000310707580c00300340686504004242d014840b0b040c2e8003424040704002d005020b100c07508080e104100e4500e04003022a5a455103031000034003a215004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 890944838 1250 890943588 890943623
    0x513090501021b03090f030f0c04020d0b04020a02030403140316062a05072a03080a090312050d0b010806090c07150204080d120e060f06030a14011a0301060b07 70
    0x141255015903000d0f10002c001c6030b12242e004da80390054011140138680d070007020001d602c0c00203640c0c84000942c030000e1803060100c50900010b0b400445010305040d403070340e140c00e186684500103000c01d00020b900464955255003071134000c0e0090140f25094a4000b00000340b07081d00b21010300c120b40c981110000c1000c18171000080001036100b4042a0395440e80e4905000c0380e0707404002061002c0c00340c1c0d01045985124080d0044102c4400c1c00903030030541c14041080068490b1024000200d07003810002c0c0540d540340c035005a01032443c4000c200290000a400c0c005540e0b9104a4a0755807003880c11024074a001c0021900c07980010300120441e81000c070f0346008021000700ca10115001c054030543d1600d590301c41c0c442d60345958080007008201c1107100d940e01440715101e10000048100300801c01c2d61a8800903061016001e4549a058045c030440c51010410dc5500b48070804e20500000440a0182c0c00716240c00a03041186482a410440f08004d035030102d00550744900c1e044166900c520300d010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 890946088 1250 890944838 890944841
    0x60c0201211a0f181611030406090e1f0311130e0d0201050106080f07080403050d020c0f070b1608030a0603050a05010504060c050a081513180c0b03010513090501 71
    0xc0301c00600650506801c1d9400c00001c848110900e030060314800c1c1000c1444003044100c650b0500051080c0c41e000001502d0b20204c1c0601c0141c0240320b00300500c103801d8031280e05003194071940100022451082c001c120081302c2c10707040c0e03506c2008514814084244407800c41100c490500c0045c0c03152641b002004926070394030742420300000800074104494480c0c058929115901200000059440c01340001100740c0550096842210424205800b40d52201c1303080d0781c8004c0c060400d80030004240580745a20302c403407000709180f0410310000d04119403501c0c14507240c201f0030f0300549030000c000e01610150002102c0840d8241e9803003030080740c80e50380e900d002000604041c0c1c0003800c2d07803041c602103105100c41075020b14082c5004035018804840c03103150a8405220700c3c0c03000d00000b10356100161031000310180401c60307440300a181d280d10011001040d000d84801a403480c0a4910f41c6040b1000c003c8141c109400a1070300c0f41c0914250340c5808000f40c11903c0300f078a40682c0c02e4a98200c0030401000307 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 890947338 1250 890946088 890946137
    0x521070f120213140c0a0c080318121306110109020d080c15010f0e0a0f05090d090515031b04090c0522080c1002010b1509031006060c0201 61
    0x200300c4840140d5540080d2120500350105a006a0010401140220f1140a030740c0180d54504200f0480c2e4844038154003980c1d000a601001300011002078000140a0800560041d06420400c181c1d44840000003414011080e00f103012810081040c82c0100703000741b8589003150840d0a103405100404990701d4090305440800944c00101d01c161201000440000341c10300850803800c4680d2074403085600c0c0c0902601380501d41d82d1a85052041254100da030703814940c02460800c000c600901126803940558205a0321840950441020004110f41c03041c025001044120b68110300c00e000f2800280c5184400f524040c845803100c144068168910740844005000d0f05004000c0c0c01080070000b0a00d0f085484130354841e4000c5c24590600c0040f01c0300712020356007044058001d0302148800c2002c0c822003407203040255504c3d00300b150382d956a1042d22051204074100f10940c0c0e03240b800708042c240381d0b40f031441000c418a0084180702070381d801401010306682c2030805c003d074010200c0007814074148 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 890948588 1250 890947338 890947349
    0xe120c030601150206090a020a0312021626060f06040504030c1203060e1e0a051b0d06080d1b0b1e09010c02010c1103030615040b04121506052107 64
    0x1418000040e10f43e85403801d025070343d240e90300303544140d25004901c68954242101c044d500030345045052011a00d40201500c21191074011034a4489080c03c0506c0700504590062900780441d2519849100c00342c1081002140700e01c0181100340344c407400c001405600509201d0003141e44000140c200740c0120782da41c06694108480540c000080c41d00103000c0d091038001c0510781168000802c8072024034600c032504240301c1030001c2c181641c40c001c1c2d040092000a05060300d0003000300902c10412407483c014100214005d10100d4900c0c01c00900d00c0c50314130706000d80c0c801c010428494070030a64401d003030100d0150707200300d6001d06a141c4400c003110030074541440043d4451046d0900402e00300540c0302202c01c60309500240807a00721400c003528840844d20406d007050b0420000079000e40313000d200083d4904580300410303081c9901c42c9201c4600d600160401012142c2c2ca810390018004801c1c000401001005000e010107810400402c1d182026a2420244401405401c0075401d4003800340801416 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 890949838 1250 890948588 890948593
    0x31b0a0e07140c0d02070f0b0d151205010603020411072d060c03051b1305010804020315091029100c21030e0309090c0f0708120f060f010e120c03 64
    0x107468081500c4003131a14200300036100302c1000080b80d076480b81401c803c640d003001e042c0d030411100c89031080203020040c0c0b14940d40401c2c00340c041064408074805050a60281d000014801c0c11441031008a54407a0745016100c0001d02c40c44001030004812030030f205100c200d10500c80a440b03500d214140321340381c0700102a0750811800c0c2c00044d40c1980964030440345910007c2081441d41c0d82288203203d880941d500c20380000d0801d01c495409081001e4201d4400750440f08450210140003d41040a4842e203d50343c0011019080c1d1380b8880c0600030b01080d1100182c90b2402c40003803845101102e9000540c042e80107202c0c14a02d80d030040c80d0900c90660003030840c80030001c80e90500001844910000c10100380360204900d14510000240d803140c0300041c010000940342c81c94121516005240c200c400c03002e08204003400540f01002822241283c41104052070038043c4440c2030800c4010415030080d801d1022008550703078008460185064180c3e8160320068840c40081c2c2080c03401c52500da0140f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 890951088 1250 890949838 890949847
    0x303060d0818060d0207060b1e2101060303030e0d14030f04030e040c091802090a0302060f0706020a021614012708070e06010f0804030e0918060411031b0a0e0714 71
    0x84c41c03282c00420fa42031281000708019051801000840f0b5804e00c8001c480e1103010070512605e05002c070070f00710030480c80d2a00822400c00e01e15014256010340d001200041d4840c01d04041544081041d20384512090400d04007543c12410090514000140108440762852006c41c0615004400c1020f0341440500280a0b51024540182c5040c11621400f1141c098150007101c01070382500c2a10301a80000382100c1c02949076800f0400705070000078241000340801c00001002039030318801098051601d8001e4500c2c104074400b0418400c0d926889503801200c65029400181c3c1e001c503113403c10403070041d4808100c0c41901021034088040d03400c1000940b02e80c131342c0498030729071506c190361041c01e00342d07140c1c0110700360600201d6a6403001d9070000c02041d088140c5d0801803901109040c1d1144a000f010041140c402030700501d024400d4405482d40280c021090f01c443c01c0030300c035081e5004201850b8600420001000c1010001d0340d114007140e90340700c3c201140140d4400c94090380c01815182c522600c6 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 890952338 1250 890951088 890951107
    0xb06031e0a09020616120e06030a0c03020909040f0201140c0c040f0e012918041e062f0421020f0a0f0906050108041a090c0a09090506090303060d081806 67
    0x5240500082d01c00e0b0008561b801685440764100f11002200941514203640380d03d00c0040203024801c40e410185034092007465004e855908007688a940109041c1c44414050f0001411035000c11901c014040020000130243c4440003827642144582518000340c2115002c20074001000c41035050700c0e4a508208203c9064071400361010315025941d0a0f1001d040300c11420044050009480080032050b51000180402c1010741e801901900d0a444211040115600d400440e5036100741004c40608892000000f40340c0e01c040654041c0a608800389418180507003240001104601104040700c103030260411500e5288445044020140c68900003030f407102e0b0688201c1c00709025502c030407071400200040b40d44c401c440c80750196402c42649502c00da03d02d02c00c4255004020058034541c8500703200350f60162104001c880060081c00e03000904114a4a481070034000003400c4421607900500522680e80d03122841401c0301d0354000d02c140d40d500242c404014809101c204c05035402000071414001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 890953588 1250 890952338 890952367
    0x30a020a0306050609090105361e01032d050313061101021903020f07141608010504020a0e091c0c0b01060305040b19020d02030a0f0b06031e0a090206 66
    0x9000d0303994405101d6140c80d5018001c1500a25a01580c40301151004200314144503a50742420b04070f904440e5081c2c407003900c410760481004d0301503e0458100400f04040b400b0344001300e0050b00c560240020044d45140c2300c488958852003859103401c001c18104402500b1022038400e03105601c4010340303484250300c420303200c8030b4421403160601141049502c114810810701c200c07070419074000e900384081019500100e000350407004442c2c20745802000307102e0101d030700010407900c0c04118800038400c4450200500c1503003090b551024001d681800309000059070b5640c0d481068607039600c40450381e41c0d02d26810a16000c0384504511074041c1c0e85910079201c03503000b0303900d106079400f42e061507200e81d981309000c4086600498000c0c0038490f565000c0b5081840401014200c91840c400250a003180281c02e00226442910141e0006030356000200000c100380c011440076130300c11213000b825407910100d82a16a41041c4902441c82107500005003c00c0c0e480e03102251075600a041c05031254082c240700780c1d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 890954838 1250 890953588 890953597
    0xf01090b06100f050f090a0519060306050a18020901020307121e080601120c02070b0a110106090608060a0506010201152c060303180a0902070803040b0603010507050301031115030a02 80
    0x41c05094640741c5151124011207440344440f031595205480c08590850021554004400c069800307d003c002c0003425581d428051900328100c049100ea04514040c2d02908482da0f0f5440540640c3c0380c40030800981d00307124800701c54000b0108001d6500d140d000c0040b801d40c8174000d8000d1521400f5004200003650015414201a603d07400c04903100000d52810360f40c019003101d05a0019852001c40ba8140c03560b90010076504030750b4012618071a450b46100e81c034071340201c0140800103102e058403142c01c0400b4020346c0e0040035184410020708d03040c20091915094010150380e0882d45540108074103920075805050050300e1a941d0380c0129884100341d101089545005158510030a024040c01c0c00c030250303101380500002002145000000e550015489244001441d0720044600c3c002446d01d9041c0010414548144081685e91916143c008140310300030b400c050103070b89013904110a643d000b60450b41503c0c0c0181d00c40040c40b1805000036040074a02003580030544010051000c2d00e100ca03005003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 890956088 1250 890954838 890954851
    0xa05010b030610120203070e0114011b050307030507110607080a0e01080115180521190f170d09030e120606090a021303050a1505010e0421020f01090b 66
    0xa10980c04918109907440000b40d50700a41a4103070300c41007114600480c103108400d44040d0984105650785c41c040c0c203d140e0240d001040c10324100300d034161903691102c00c40803400b0034410210450b4525403217417540c900403d10000d05200e0300051240c00d0041c0070b45030300e01c508001089103980d031000d031415000c2500304d0014240481c0002d4120034103903015100c561f05031070282a4181b20b4264024084507074404079240d0600040080c607002ca415180d0106404a15400154441c082c24400d03070407501d082520341014803010701c03800c498800034040c00c10f409080b07900b041e41c10b960540c454802005034410304402544803803078284660205a04514030340385125040350034130b5101000c00e24171500c82408440d0f040c0d1080da00000100540f04640c05008200440d00034215115100e503a558a40a40b104e400e65003034041c0e40f45410380140c980101da0251a49a55001d10703800c040d41ca22844148a0191200c40b00070009108030b020310805c04413415801c02d81c0203000d4120b690a10f01240c050a4951 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 890957338 1250 890956088 890956091
    0x120e04050906090c0402030a0902180103020a2310030b031e06060a03030e060705012301030b150d15020f1b0114400503030f0714040608130c080a0501 66
    0x74a03220307010400500c0b6004a00c00b42c030700b0000240c1000001d40c0002c1c10841019501c50341c000150302d4902d280458611b03d050842241e50450042082e1b00b1180ea20000c01e44c3d2546004d1003200450014001e00203000f5220040c9448042d80c2c00c0d00a00906803809805205001c2903490b0f03a48418450041d4818803003e860082c0c03508401d101013014140400340c04101c1900107441070f4140f0700b000b0001c4c46c0c045c6d13000040d0791200b1104080007035140010300610400d0300005200740300300710040350741081c03240498011454a14020904c1503d0000014010150389204a9600c01c1150129420a8522049166220744039001084040320354558151507610f07100d03d034000100100021405900031381001549890445090544281c4000e0003128102c076501003a40c0301d400401340d609400384203001840c1c881c6411181c40d044414014a03400421121182282c01c80c1c1c94a002c41d801d550341c074a01490695242c035041401d0400414004041e800c000c10000f032154004a1122242c2e44901c00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 890958588 1250 890957338 890957341
    0x1b051e03131a07140a140303070f02010b010e131b050d15050f130906051303020f0606062203080f1c0e0c0f01030f0501241128120e0405 60
    0x21000310000b031554940b00c10304100324030350200320b4059000315041480c004440c801c0f040d83c0d950340203165420040840e10360000c01480055504100b101188400034070003000b00139000c0d00000d000b0b19408004a000354041e40440403600d41c02c0d0401e8421f41412086040d00c1c41032090028030b03d0780070380c4034441e0040c9800601c1d0f0040d1a221b1002c0308850000b03148500c4c1c5912001044004801c02005c1c45c00d0542d912811030000e10103004561244480108040f0507500900300a402c03e08043c4a0f02c0c2c0ac0d411030b01c10040e003617680c0c500b541c0c0e041010541249240c1001c1c030215106040540014085a4001c01c021110303038401070051072420301400540300000200c42c1c222040d40d2900440b03980c190441704044445003400c188455a4460516012421150020050044034420780080b000302c80c2c16002c01c1c01200c2c4041d01e00e200341c42d080c509042040761203061a520360034401000703514100c482c158806102c1e4601c0e0240c948542240949444148043c00a00040c180e159554002c604080 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 890959838 1250 890958588 890958599
    0x804021f05220503330406060302100305071409030a0f0f060b0904110f06040e040b070e0607030e1207080609030c0105070c02030a02010f120204060c061103071b051e0313 75
    0x300c00003c03201c001d8000d180d0903070040398260008102560880382c011100c00e00300120b401000555010305c0c01130b40001000350075401405041200d8039100424103050a040c0019030351300000034450309100d140e080792a4690400060b080c08842c82c0c000c0c000c000c000d1001401e000302502c6c03042819100c1d0b030b8100002050309080c040f01c0c00080380c014291900544100c0c0d46030500c0d010b0307120b13400001402c0e1071600e600c5041410b5094016182983d80f607a8207010060455081324014880c2c210480c0e144d0304080b00c55030010804030f0340011aa0040064050b0704d00303c41ca04000c04e801030203000e03041e00c1440c41c240880c00d40c0d903040017100d80e80560038100440d89c1d16000d40b115821543c1c000e0041d2035041c095400541d00148072070f050100300090514880c0454042d440580f002d07010300d80d03950b1416603417801c0c81c4d0280c3d940ea80c15103000d41e108209011900e500003a1404500081130304500c1c600c0c042d4188682400840c843c40c9030278030f44c0d8905110000001000524610074518200e658035030302d50 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 890961088 1250 890959838 890959897
    0xc0915070b271e0d02070506030f041b0801150807050a03110607020319110a030b010915050312040302030c0a0b09150f0d092303040512030c030c0303010e15030309010804021f05 78
    0xb80300d1f86401140c200081400c0010020201354401e005000c0c804d0011040351601e070190589500001250350740d00d14007d580302a850403100140a92001840c82da401c00e07002a2400704a4400248003180410681d085070300da540a440c170964005003540c10003440d040c05010158a550000c0f00c0c0d0b044010221455850044600c80c15a03812242d4402245c0c2032040410041041401108031407251a00c00100d594041010f020200c5d4160906a2218954418549807001d0480104d1042030014014001103260780143c82a8280440300d0307270706810020014480a100d0200144814000020b1504518419030411a042449100c9e000a40030540100c40d547e010700d070311020f890f40c104210030420392030109183c2c1d0300e4043c2da10035a03240042c20820b0f01d00c0c56112030851103e94202100401042c1d01c07901046074480003001411086001200c0000e489200b1102014140000240401c01f0354503044000b40f10109202e810260482c4c2d013200180554228483d05c0395010780d0241c1342d04940450 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 890962338 1250 890961088 890961103
    0xc10110d08092820030a051b04020403050d0302030c16080301060e040519050c040e1614040303050304081b0a050606100c02010801140105120c0915070b271e0d02 71
    0x110400c500041c160b1350b00d103040380c07101049892180014910480c0366a5091044454851050000b030101d2201e411a41d0000e030441c0301c01c00d00c02ca10502042001c641e022600343c0740200c40d85001a583c1da039601c2c413613949014483d4134100528412601c54108600500103506840702a00c500502140c04010042030780c00c1155505160145a1540c0c14001c48076001103800c0751a240c1c1070703810261070f08418030145104696400ba0f40d0030902c1c0340014550044100039000f031203081407078070301800c5840191040c8005040182001c0c0001810001c0d80f001c101405800b02000702511a407a405040a0b59188001d4404501c14818030705032500890155941c0754801c2c1c0d0685072118980e10300442074a1080450301c0b12414010104002ca07081400844041e218018109c81903403a116a1000e00501062000c40c0d486503250412450021401072003000e5403000c8415588100c00110300250018100b40c0d003d01070061080e107240341c52070186e51121145543c0c41c40c0032100c4400501c801240ea440c403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 890963588 1250 890962338 890962393
    0x20030a0f06051027080d0206010311030304030c0312020c0406060c050d081902030405010b03251e05060d0e010203010f060e06030c090d03110604030903030f110c10110d0809 76
    0x95855a203001080081c011300303500c20403d11403900d030303031034100b1400e00c0019080800103800002c0144104184405244070035001038000710706081c01c5a840d900004014000a04448941c900030318050b48204440003040401074410b002d99a40c401016291a1082030100e82c1401182c07100079a6070700c07034500240b00e92007076009040740381e800c940203d0084d4406007054420795220315403040203442c1000a40e0712001040029003840031012a064030306002c6422031034640b154640c448102c444021541d006442c81120415965842d1084400040c05400c0c0020000d500100000034211221200441203d00f113450f000b28401030001004050721080300c0f40c0080c00d8061040c3c00050400070b05240301e2501ca400c0030380300c4038040500c441c030b05002103c1c210001010001e06000b0950301c03145030302d200f1203a07050440c0c83c0ba0041c040c2d103464a6028800b1401109042141c0d15050300c00c4440c0c004401d07030103066803c203546107000100807a00c1140c3c8414940f24001240c2d80098044c2e05150b500b54 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 890964838 1250 890963588 890963597
    0x60601031b0f1404032d0201020604110f03060718050102030f0d0506060f0c0d270515120112110102070317030c0d020c1f0902031020030a0f060510 65
    0x39285060b1410560040603400708858142480f619011040040c0042c0d0b0188484620740a03e0300040c03031880c02e80c030501b0301d039007110001d01c040107036000116150441c0e03000740841c18140420001c510700d4004900d9075981441410184980140c01c01c000548000714011405600c0381c0b54401a07a40e40703e00240503d07110010001d4141420081d4850f0380c102e0801415586454028460301000e9040007000c0c003801d8001d64410080e964210501d04642c201049600c9032114091031a1001c480f41403240b2401400910000940030f290301044a000d901d1841c080c4015585446003103030b00005424084604000d80700100e44a03600008540342141d51112607048210300b00712401c0032540019191031401e07501400588038005807070020f80782026000d0018007070b030440c0c02c0c440c802c2d1800584c070512402d49441900340250700c0120310000600d20000020500205034600880e80c06850310b40d41d00f40e09004002d001c03499155820404c0d904081c66400d20000e41c50b2400c014841b809110001e0105 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 890966088 1250 890964838 890964881
    0x80f10080715020a0807060608060a061d040302030c030c060103110402040b03130213050a200f16020d0f080c0601150504051215011214011b1b02180906060103 70
    0x41c50885a01c6100c0e0900340f0681342c4c5541c80b07584207410394001d40c50440f40d581c0c8600050110800c03c00c45164441990107061120b82d19100d0303544c55801803c081400e01481c141c0004003454020003c07101d032042c8900460359500d9207500c000341c8999082c00b08071803800e15200d9881e21460140282c1e000c1d2002805811301d55151100809050003091604a0f0088050309000b0b0000c421880307054850300a0b0030004c0b80c1504011340fa0383d8a140f09084106510906200c00318104d00b40340182c84a031402c41d96500450421800061964441c0040c000d01a20091100c04104480900a803080500c407104030341980c2d0321448440c0441c1480c00105000070024002081240781c25084840c900070001c0c1960140c080000b0b2503180050260230000c6147d840600780010004240500b0412010b00e0000b084100c1c1b144c04000b842c080c02e070a142041003021500c0001070300d421a0804101540100001401a042201206094402c40f6014810f000380070006000e9402070081ca41c40000300459010722 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 890967338 1250 890966088 890966099
    0x30c0b0f09190806160f020706090603090c0e0405010e0f0705031507030207060f0b030f06060d060e0708030304060b130b01080103390f0f1202060306120a03080f100807 74
    0x512412004030410340410500000c0c00c1e10f801d002a0340034046075a00c0081c22140d800c1d0140404408000e090304542c80b501d0100205075001803464140d0b8800e1401146130b07951810120400d004580003c080e800c0345006201c108001544141d290307491450580c0c08461600e00520b48811482c468140c03d40c0000014854560700e95583d542d21048500700182803420313580f1500c0455802100c843c0083c0e9480300d65018614041220320701510100c0c1c000d0180d0f140050202d296410b0b1050300038011a2207401000010382c0c01c0c0f2545021708045001c4076107a1030300313060a00240c004680715a0180032038403014401c0f40c0550103041c1c403901c2e060b1980d040390b03403861b0340d01140a00c185c551a03805000c16221108000260300c02c0400880582c81b03c41211410510b024000014a52041d0740c0c1d07085503501048a180d0901c070784104683c045030849d0300d9554103408a803204e21900d0001405014100104040540204e030703c5010b0010700d01c09250558480c010400580f1090007400201c1c0c0c007041c0100301 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 890968588 1250 890967338 890967349
    0x204030506060a140103110d0903020a1707150c0507080304060f060f06050313050f0f0309031b030a110105040504020a080a0c0f02030f13031a090105060d03140901030b060309010204030c0b0f09 85
    0x41031f48031080c08a00d0400c1480b42a02200ca00c0e2500314010f0b002403941c03034181300c3c401261103500c00c440e0501e98904080c07039035a403000394190003050700030f5500c03002810303cac8070b01030f0080d540e12a8201104660383c0c0780c81e1400000400002000c444400c1c0742450114001c000410210199440c1e43c171268515111003502c806800640da070101c406105642d8924581c80d018010581281d406d03100440c0c9512b20403003003604050b0400c0c80c041e030030150341e02d0b0034445d40d9000403041c10345a0010f148449142841004035040e129540019401600015000031a258403404891191216542c20884071842807070440d090349803d00020016030007403004058080d850401404140b020281d51281c06039281d071009a8203100c0340c8544031720b1b034208041240c80c40d402e000360350740440300f1200c001c4025803d68014140611889100211090100c2c6107141039000e50f115401c0d5100052032241c0341e2070480c1416010b50b1180c04100d4181911100010703050000b8401c2c0d402140c20840c90340d08003500c01c0180030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 890969838 1250 890968588 890968601
    0xc06090918030825030c0e030c01080610020f0304270b10051c060e060102060709181d0f03040515040e060d0203070306180c0518010b1b100204030506060a140103 71
    0x18002d41040001e04010a0b20031841032a29a17140405c46000b007910180400036410790701c6000f23402132842c0409680e402152030390310000454081003c081456000c907d0442d1102a00c5602d200c00500850356100e15000b44006d681c200144224010605c19110182c400d40d00540c1d4201a0042c89803060a0280000e04040007000c6c0130402124507a07000320090714550360150005210805c2406403550f4140589544a181820100c050030b150041811180d04000c030fa4172101c80d6100e00e0104804080c2858003d4010904200c0341c0d000340113881a5200d6025103d5103105a640303251000805d4007400030750382295070504c8900c02a40e60402070240c003000c1d0b07443c2207901d4080e40102100160003031048070840c14250282c0c02c01c00701546004054800150009885648016081d10050000600341c5066908003004245c403255200c484010203400242c0b405618014150a490042c3d40c0b03502800c00c4038000c8003140e441c1d85500080c403851610703500800318003804044c070f070142c90b5000f41c2044 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 890971088 1250 890969838 890969851
    0x110603070e0406031203050c07030207030f142d0c0f04200f03010306060e04150f15030312050a020c0a060908041212120b0a050d140a0c060909180308 66
    0x890801c0c4810700001c00b100c201d50001c0310742e00103251388440030036854441d281c1e110707009130308561600c11030b620301950310585840004c0011240d4040d031030030001454001c81c65007605e002100c01910305660790b8905071000901310080d00004840c2700001c51380028100d450071401030700900703428042d64180b0019005503071300000d840c50b40350b07405400703160800020102481d0010945403607505515161041d20411b601c0800500410b0040c480400d0701c8000701e4200a403036003800607022300320303811640241414034032010319450201d9002042c5900805040351a40c0b007124208525030320b4184031000c0780584400320070b0300c2e4460b02201000615651040c00130714091800c0b00d090a070340d1008403880c800d03100d0f000c46415084c000b041c80314a802025400c18000214000c0c03144100903000b040301040c003417081510030b84044099800344601075810a41d4000004143c411540e82424821140c030518400d40000a080d41800680c00c2c103284140f04040c41440481c0b02080c960f138038111b58262014005 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 890972338 1250 890971088 890971097
    0xd0e01081f081c1d0111010603021e0423010303111204091410060e27090c0307080604031d040e3c070b160501020403260711060307 58
    0x51100d407080100034100a0803a880100384145081d094409460342614145040c0248940104400400d1019079001c2c04000e1a02030040b0754078540c6540588a1a400030350040010b0626240d603296220000c02c0c1108150b070144103104d0441c610034404c80555503000c0c1c01c20720310401400064422078031420000c401c0012110001c0040443c01da03160f00951040702e4107691800b140c0002080c0451603688801407846004c485458014041d040d11500c04500b482803c0c4c0c03000c0360624044003401c00207902c0d250040c40c0511b107051039410b5032710045c03000002c0c4203116000300010344010010303050348225495940d075580704001040d14006003655100107607100b5100e016213030b40031908000d29408445803000d9002c04400004800c108092450520307224010604d4500d010803400113030010450b00081000b0340e852811450902003802c150300000c0c00342d4000600002403000c580c80c1103403108001140016062588104450144a0f01c1402070191040c00b58804840ca00400915480718040c00d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 890973588 1250 890972338 890972371
    0xa0231060f05100806030c06130b0301090501050a0f140420030f150301020a23071502030609061008060d0201020708010903030204080d03021c092402090301050601020d0e0108 77
    0x440105403845a0403084419041c444200410f141401141d1001015818040c40a00b803070320200352581c04e4814158040d000004000420901c03954030741000703117600c40c0c15548a58441c041c5101502c1c1c00e1045034443c0400940c00700304801520100c0c03044800411108140c40c0350081440081c042d02da8a140011350030b0b80e0000007410300b403c01144550406103a803200f6107050301c001e501490013010618040d0784140311803a03d041d000028000c0060743c982410665401c0140800c0310ce2042d00d400030a803c2e80c2c1c9041600d4044903801550042070100d070988065501c40041c000f0807600c141c0000001020304011500350b05114242c09030030341c010700c180c0b1043c82e2220605820b4840c224800c0f00001e03800a81000002c40c14010b00441203a64034003540b500c0c1d0003641d00803409925045822132241d031101c0d2082040851070b40704c20810042400701a41039800304400b8020342040408a002e0750820000a02c650310200d680b40c10070f11280c948265114444004603560b180091091103450340241 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 890974838 1250 890973588 890973679
    0x309140304150c0521190e010c03030f0e12072006040915090c0f0e0d0302060f0c0403060c0908160305060c0a0507080721090612020a0e0904050115080a02 68
    0x1c2071003000a075401706465440c0040a07402d4600d05801c03811504100c9649003110750b0380c1e401404c0342002c50f010300d80400c21220300004500241400003403821180304500c0f4002940355048054129540142510b81070b58100f0060060740f60916108191b000e9401c010038000444030ba40281d1001c0161043d0441103a103072206402244e4500c000b40c00410343c410b1006194990100300c0300c150b64000c0d100c0642900c0301d55000f9542d00b4020740308031082040900020901c0340340d40b040c1c40c0103542112090081580e4200043c10343d0020b0300620050b4040e003101c3d5a03c04010740b1100e81100c3d401401090135030f031012900c5206802035540207082010411604000c540d44030042c0c4940b40c02810707150314502601540c032243c244071081c440f00384000340c481042040d801048000385a003241e01c1c0941e03180d0845804a5151118071040741e844908030b014001071217015442134400711403031510302400b503440d180304503614080110000d520840100880c5c5074010241c80d05000868071440d1494082c4400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 890976088 1250 890974838 890974873
    0x41506060c0807291603060e040b0714030a020a0906020a1502090d020a08070503010506010c1e0c08030c0c030f03070203120901090302030609100f090b0619090c0309140304150c05 79
    0x31044828248001402c1c00800c0d0000c00c441c145c0c4036224181000018500080d11503189030040014209035000702c0041d040754001e00c0e03000100800340c41b1803566031034501c9d4800003d4201103120400102c50710320100302c443c000501c0404480d0040f8900c0e440c1c080e203241000203940f040c003090303410180e80340303407080141c944108101c0a401c1550107048075500b083c003814219480280f010f8100520a00b8ac200030a016568420a0b175040411a442801c41c50810b01e058030801c0d885800c145c07000180b0036280e00c0002c00c14008032a001c4059480042c400d00b50256240100d0801940c160811500b005403590003400400e0b0411701130501c1e200103541c2c0d0f00080d003454030888030454150005a0044145190b5105940c00d07140c0ca4901001091041d464281c904c020041240e4041d901e00140180c1200032031007000c0003001104030601203601010300c000c0c05000c090104481d00c084610311030243e01e00c080160303415100d2100f1940030126a020044410342c48404080c2d071035001c1c003d00781d01e288030341 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 890977338 1250 890976088 890976143
    0x13151113181509020703050f03040b0906011401020d05181503070f08040b01170a05010c0c11180c030a09020d06060608180309010c1514041506060c0807 67
    0x3100d0040340c14504a80c8864854140031103200e050301d0700e107004072180c010780403880540d601581c005884045514007569184542100c010200001204100c100081104114440d0074081c0c15555075036603070140307950300c054404202405a003000d007060011074072417000b034854100f02c00001c80c007011142e008640c683e107400c1d94031000c02c02c00100300701d40d4640010440b80c0c04900d17880c00c0030303031450991031b540c4071210107000d121b005800805036070300c01c00010062890781e990094000c22441ca2450809485006501c104450905108003524460300e040001c20001c50300c940392071710075580c903c0c04c1e4180c154002400c221003240d46081240c007584900d0112440c040c032815002031600c0c18008064020301004200750300d2107168541c031526520340802603d004031028241660f0040007840c082410200c07030810a0407491900d58050342d00078503480280d0141d40602c56950140300358144110640d240c0f0f0140c5008142c8907c2c020300020baa2a005040240c004d0080301a9040c021031400c0c01c0e40305 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 890978588 1250 890977338 890977357
    0x3120504030c140105090d0623160822140a050106050a15020c1c0b1006170108060f04020a081504020a052d0a0e0117070e131511 57
    0x20003040600030028810082805007100e110302d64240b00a40000030010b108000d41e05000320300c3c1c0b50b1744a04009442d0072034546641606d0f0119000d81c80000d0000c1e0380201100c8480009501c104039102407030041a005029074468120329840d0414100c3c283c0308a41c1041e0125042241000011600e0105015036040d1612420000c1505450242000f1880340360b600240b140c1e01d07044102101058001402503c062420f54072600400041e05415074402404d010240041d8540c4c42001680c4050f034109400780c0e4a40d80390820306410320b16042640a001340034a5207540e02400105144c2c291700190150b115200428007072041e5111514142020110304135070105004c5501404210310700031001501030070095450225014940c595480000c0c05200c030307020710014000509580c2d84030001400c010309680c4a640d5450759407100100d10f000e180d0501c01c005170042110116092641102e40c0c0c2c021901c8551042c0d1800705500c0e40403002410410f00e80c00a40e0315040700c0ea41c0700324400079010588 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 890979838 1250 890978588 890978597
    0x605181e180402041527020f220911030415110c0c120d0e040f06050402070510050a0c050901030b030a0b0702030408070b1e0a211d0706270312 63
    0x18a8810310042d07854800017100031810258003800002080c0403042d07149078070307885004046420030308000028869042003012042c40001c50400e841c500201103100b031088510304908035565200014100c0f4080300e083c030309a0404101081c0480d5175890012101716851100007141001b420382d91060364801841d47d076040e04104183c4007140340c6103401941103808400501341c641c1c070410004041d100c8461440b40710300d0f5180c86000f001002580848050000034004568540c51070810f00c0e41c0c1c00c0c9076160705181a041c2000200c0310300c4640601c103d040c0160704c1d460b0030040a80d0041d80505481c40303080c1d40620810540b103010460b034003401401028a500503541e90390501e101d1608040300c5801c40003180d2810401c1c0da0754000181c0c0c80450064481c24402e4969140c58400c84034001d604050440040c580803c5d02a5a4206d074030030381c2600c8004008101d0b00320017800107501c84c03505101c1d403004030304140030b19180c1454000080c9043e101c1310b840c004c2001e80b25990441e0781c0c2c1c481c403941c80018 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 890981088 1250 890979838 890979841
    0x2090913150e0304121112010b030f031c090218180c010c05070e100b0a18080c0108071d040509030307030501050a0f03120e031905070605181e18 64
    0x1040301c5064021030981d100c8240611000340300065500c0c0304510130f104030744160341e4044051142c0c443d40610007010040400307402100f280f45050190071840f0f000c502c6405402d07000d100340540002100c20270214002544491504600030b1801800d1400040c0c1e0003500c0441d11481804e03035015094800c4102c1028010065a003007032880c9401c00c1c6c02d40e201d040c004126480740100d00000307881001c5842c10204241969544986903404511a9000354003054000c81c04100050b0408100d0350303d07456607580400482d03a21903500d40d482041c44641c6000c1151031010507400e43c440d94650b0b465182040c004410401c0d9480401d084440403605009141c0011060045090345402428010402118941d07541e9040000442080c1d405200040000001403020720f03006021790300040140300010281c8020038203549003d03c0030301030398508440c10702601501003a0503029038244d42c2107501041e07004288001a034144090075041400c010210402007081300c820b5030360f081b60b41c030a17004002d040903002d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 890982338 1250 890981088 890981093
    0x1b080c0d08060a051c030c02130b0102100912081807030f0c090902090f040201090504091506080d1d13020f0408011103040b0a0c03090510021b03041508070302090913 73
    0x100d8000340c1141e00c6030f00c2c0b0007010000c1d90307215800d20b00311a4503011030400054840c40c0944141d0842d0200a42102640000340580d905940c01007007800e80030b07000d49022102c4101060115804034a004149002038220b2545072841440340584c007410001032000704c0c20f0456002d51030b1510f542d10482d01e81b8003a50080f010010880800802008000d01c03c0c000010036500194040400800341d85604241000040a40e0300c1411090010100540300300103660990410f11200d60401420b2044c540c10200009041c03000004d05001032855030303440c484000a1840185035010b903400b2103542c45081a855800300c464580700910b4114655164169210304c0d2401403820b42c0c0030202d40c042c0c4c0340c20034020407001c140204a00fa42c0030009160000300c2c03a014140c02d90040070218070107003991007101031a1102c0d030300d644d00400c80c280e0300515542550404568446d0760784114001c3c6524400002401d8001d1800350103142d030400b03900e080c0541800301da500414481c84007143c072510360303643d207240c80d10a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 890983588 1250 890982338 890982347
    0x80108011b230c1f0933090b0f090610180219020a1506030302060106050306120f06092109010503090f0f010920220914010c02010c0c030f1b080c0d 65
    0x2001070514205002c2c1c00c0c1652209100c1441b4203070311301c20400d640c9050804005424481c88080c1c0c1e41c0040170401c1d044a0300b4024544070040302c11741d41c281049404200031000c0043c0481c41050040394100b04a030401c00c1e022070454810011420742602844103410b00c1449007896204500c2a5005110340c001c242403807010100034030a001e83d068a49807050020950101e5154152903050401d01d51340d4441c500405d48107140508442824014040400410600072a00a00a1081000301e03800d04100d10500d8480906e648524211800c040104142e00d50190b40910b61010003d000c1e2001ca0346c01ca04800d003410b03203000003000140d54804031a0b003000079803540700c65401a000d803452a00c113043c4020a038030f400440307401b03054040611804803410390700d50000280b0030380c0401550100509413821300e01800303003012400c1c055401c011107038180c2442120300701582074042d900c1ea00300e260803580a5501440107424400f0414801d0b051101007980301000700700103500200280794a0414020080 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 890984838 1250 890983588 890983633
    0x118120804080301090c050421021e011209020d12020705010f0807050d1d03070819030b030a15060b0301030305070b01050f131a04050108030a080108011b230c 70
    0xd020095040c40081404101581e041d6400800d00207524007005000b41d03858066035100e80c50490b5962004070a000041e03c00f052128070a40360300e408441000342d9a007101c018004040c2c0007452512642c0003e1195070030004240b030020f40403c0d1030a05a8440324099145203142c5030140e80030010030021541d220302c01c5044400d4030301d004085418425001001c5200b1010b100c00da03a6101d800006600f00700c80c5507190b07049204411640d0350015450154550b8200550512480d44401c2910140700d000e809107600c1604010054900e00d00c40781e0710805400507541c1707044680c607520740d004200300c03089a00a40c080c41c0261a4641c64003e6407500c0c8a035103005030080c41c002e20650440e2616602c901c7c50b0341c01a003203584e0340440e0300c0c04c01d9403100b182c0408403049580d000741072900024501c80c01200234070500c06266203940ca20703a00c402c281426141d400d0000d042d25010900c0a6078604d20502c042d9481c04000716084030907011214455486800480d803070600e039040098070300b207200f400342c1044 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 890986088 1250 890984838 890984873
    0x9031501180c0f0c020a0906121506050a12150903031a220c02030903060c070b01060507030e0609040f050405010506120f030304110d0501180303060b19140c0118 71
    0x38032400340c80c000000e02c0b18a03107103920700a01141500301c4003195540d801e007001800e01f542c01000260f5035480003d0741c201c0f0282007920450800ba5508049044c0c0340a0801030354009424001100c0c500807101e022400e12082c02d413455020381d0845004100180950b4108a01075a4049a9806aa26444403c0b44005016803058120390450300c240052583d001d031080c8200c034800a03a0300b5100c5026420751003000f0441d641800782600300100000128007038022603004552501d256a00d90b18292905c1c27181c003d010303000c00c280755030515640c03070b04500500c0815405800880d200b02c00b60030103415035905807002c84803651030328100301440c1401545003211000b050010842c0c070040c14081512448050000750802c101327003d07510069211030b03e1080000c0d40c0322008005410800075120400e80c0d040d00c04500003820f00e44001a15150039066a0070f03600078201034000340c0842c90b81a03070461071003801805c45e0a010b100300700d00004284030b40c42c605603451a03260303168038052900c0c151022501454 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 890987338 1250 890986088 890986091
    0x40b0c0313030302030c040305010e062d131505040303060806060303090d0b2503020a18230a170123040b0f060619020f072c04080903150118 62
    0x400c605001030300084804103405007401640c0b0341741d40b00001c81b0341c410364002400130b600300720390f140c0c202c00001032091094090303040d40e1402c6c4e0dc150100044500c060515030a00800020101c1d1080340100d481d0b10000c0d00c10081d4440343e0000c0c1460100341d80d4100c500340c02003170344d540c02041780301414440c0f99807102c1c0450103945000013460006003c540315002c0900043d0010000500d01e61500308580089030480c006c0b45880302169400501070340c49a05000c1c005401c0031982c0d518001483c48130000c0d100d40004e40050170442c5860210090032185a55034090907904001803003c02c401c082440d40520040017045801c400c000181000c1c1040742c0b0498a2050681040045140f0b410f000d81c100541e03030441030031a01d50000280060241e0407243c44e15940c1207600e40780c0c0540014040d42502c1107081a90320709031307031001c8051801d800d0046c51205e640b4804001c0c256020102d00a607403107442180c0c05410062442c01091034191511013820418004030010300807034480400c801d030501c545400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 890988588 1250 890987338 890987341
    0x61e0a0f15020c03030c2109030a210c0b0601031a0603160305010b03061c06110a121a13020c0a05190318030512030405010f0f0b0f090f130206070812040b0c03 70
    0xc0d203590705c0743c84070040300b4604074280125403c00507500845a12201c010111070700315080381001d9121901c100c00c0300342141101000c110be0b0f01d0185c0c0c00004015004419500c0039541c410064001d0400124148900b481e11580104d06682c1d0300d000c0d60103855001424072500310b150314042c08071401a00800300d100300c01c1c0100401a6140098103a41039030100c41030f000d6424a14100e0007405040713829104007040442c0f0925001d90000201c10009400c15043c4440f101c0b4070040c0c0a00010703d901c0c2c83c2c01852a00340002c802580b6001000300140c2c40044a0505110342c544070300744100a600c0d0810070404082c540241a0300420300c0c071030403181d01203520b0a1071840e660641d480042c141342d050704010110018041c860290b210424001365000c0900c2224484203511006160718a41144103002207080810380e0304211603031034898400401c03c491700c0c2d02c030000c1b440c58460315864100ea00103800c000882c00244420060000c21504003404001030500340340c841e42c0048005d0102c1081113040c030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 890989838 1250 890988588 890988607
    0xb1008060a0b1e070203031921020903300301080a030207170a02090c0403060e0705011407050c091b0f042102030c010819110d0b09061e0a0f15020c0303 67
    0x80051168503c44070825544100e036101190441c056003800d42d490301d900401042000c1d400c03e00303082e80a4807828041c03452080c9203600c1c00881c018501031302d40681c81072891a0b005c3d030b94045d000d03400300040c00314418554481894904a58403d802c00c00040e08980c95841c03c068040000d107000d00003d107401c00342c8201b0604c842c1c0d40c5e2900500042c0c131601e25480420340030a841c0b0201c60185400070b0084c00396681100c10f541d641d1086d846514001030310701250705402c4c0044410b0360304490340038000d0721445282000304907510074058000e516025100c00741560340c030142d41c010020030489014040c1c81324a840d400c5480903814042d135071100009401c1c003000598020a00702001002401c3c0401720b62507451200321036503007109500041c030703160840010440c0202d00103002c0c0c6001c0c0c0d10080c0302084c0d08605104a1510a4a8840e00300c0035000d5041411482e085290404100160201c608259103000e91070f40110130350322040308034a1050144405a50511041160b044140c005614015014 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 890991088 1250 890989838 890989867
    0x18050607110418030f30090c050a0b04030f0203250f05010203040e0106030c1e0e040b4542040c030e07030602091905130b040b1008060a0b 61
    0x10b02200400045201e1060f40303451500340a18100c6c2d4210241e501010070320181401045981b20a5a02e081044800640ea00d4040301c074405807505d09007650304113403565031504490b003034910f02240c3c58000d90100721107865640108040c0080d043d521812542d281c041c0a01401d21950412030464200708410300030380100d941180d04540841c500050b0344420308904030781c110000c448a084080d0041328824840b0740c440140e6601c004219000c1011030b140d01c0c10860004200208400c401d1240c0320464840b004400001900c4030120b000040e0885405004082d014002c540d041c1d21580303014000303000e1064880b040358217404800c1e01d6200f118101082441500075080c4c107940b040e07403640e0f02d034000c0c07911070303000b5041c240560b4045030711042c0c0320714011000c0d402c640ca0f064042d050f14440180c002e000801184100e0f02c01030420410091201c0a10000d08a0440516001500c3d510401c5d516110310801c199100910303a220700083c02c00008000032007440b076104a04200003400342e0318041842 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 890992338 1250 890991088 890991107
    0xa150804030e01112e09020a0312020307080d0903120504050c090702120d0e06060a0e130c150f030c030e06130f120c02030712050309011805060711041803 68
    0x1800c2c80518210349000403070301c010005030640241d0090003412038500856100302c842090040c015940344c0c1c4000d140e82030882e4143d00f806503000c5a50301c005c0022440f00341e8080500034492054900d05810354072800c07495480181c81c4000d26070742e0103000040c0760380210341183c101c8201c0c509000d40d040640340c4d540d5407540d0303c1c109481110204003180c4817600070003400803804000048282ca130f0540a51403402020380f10f00001260050300d00041d03407840c2c15003031041500e043d5111a1081d480e034090061501048100460765500c0080e80498100306c800212140500e6a5a0302960021888001029603203070300190b40600d402c0058841c503007a00032818650054120304c8282c1d91a200c3d090001c3c00f041443c0d40501031807054512141c0750390f80014020400350083d000ca0b84030790b540d9442d07207041ca484c6081c050301719001441000f00035880381c40c4101d2512040c0d00c0c0320100b280c80d171000442c1a4445c8204541117034441a101c0c6050501d03000c3e003550500d01480c4200c14450944015194808 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 890993588 1250 890992338 890992343
    0x11060112032a1b180603020a0b030c040b0f04030804180c030e0c010e030c040203160e0109180216050d0f2705060d0e06040b060909070501050a030b0406030611090a150804 75
    0x3c80d506411086074144140003d108a6007481c00a070071114984c2c0c000c01940c017007640a00b400321404160481c000d41128002c1c81003070051031805184c4504030700c2c203800206045400d66000c00000003c18440d90203400076010385101d400c00c80483c1145e281c22115501070360014941096022000c029020844040c08a400e08049046010000001b400e01240d2103083c0d900c1403001c0144608070442941200c00741c101c94464a00e60000c100040d1681c1803136102c1d00f0348c0000c8040d0f03804000c54079500a04500501d00da4100c02909840e0341e06420109640c2008000a28584909030311984c010744203807000b11258a4655505861940101c0c074440714041c0d6802100d00080e00074030940540e102c0840003140205566003400c1178039022142c0d25080d910988600c1c24100440c002030000f203880006c845050711114540010104244c01806031100c0040d40255240c0001012903442d001e80d003140580d01d8205035a40394450300300111a4050b40040d4006035545031081d1244d0707040000107030005d8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 890994838 1250 890993588 890993603
    0x12031d0c060a020c0d0b180c0f041a090a02180d110405100306060b07121b12022a031218010e060f07060507020106090e071511060112032a 61
    0x2041510507441e022100c41c4c400d17006450314035000d00b80720b90f1440d0700380103004010b0021020400741c4a120b689900000416506c5514001c4103005072030658021220a01048108100003045400017100164120769503504250005000e0071a2003a03101003042e141e1041740d42c4e84840132142c844003000e412881010703001c1c1d43e41e50040742c55280302140a60003540d00c01800e0244546444501c026908003217000c817050189041e680310040d0107001102e00441d060045500b107001c09031625484107c1d1899650154040d910700c2d01011200581c10b01080900c0c010745010500b4141d09241c0361041451203000404418000038008800910640d4000e05d001d00e80700065440c80c00018040d03100b0b5040b0f8000242000441e1070412100e90082c52103104190000c110440c2d0710f440e00e1081e5003460f1160b000c503401001007804041c0038031200c5043c5002c00d1900c0c61403000c807103c400b464a0007c4e00202515070381e41d4000d004165101e40b80c00390311400c00ca001200c0109205850f1a5990414001422070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 890996088 1250 890994838 890994847
    0x50d08120a06080f07030b13020f0103090305190c0506280b031c0e041d15090102070219081006060f030b0103090503160b220206030717010312031d0c06 67
    0x10600d0b50880c8010340340000c2910141e00c1c4010702e0795600d1085100855555421000040360b007403080150071840f68000e050f08410b100120b0044008140c2c01900b00d00b0b00c10103010f08804214456100c2040da0503079200d00c0540c01d594200349140040080020301e018420580f0300141407007040714021482c80c0c141e030201c1c00d14190340010307041c0441d009005131190701d84404100c61b03d07030011004010b008240e8003003044c0c0d84042005420743c6010405040140d102001800401003546456540003155400050500c0441e90004011400b8000d90380490201c00e44140f03d00603003070004c01340b420707901c5400300011880c146c4080e2a48220918150034190748001030b410690007504641d180341e80c041c0659586503010009010f240c1c80d060303800e48a09909000040c109001b851040325000c2c0c045038150b6403031240c0e07400c04ca440d500081070901082100a2228100410798410901840c480c4070710303403155038400d40002d08035114045c081d40807000d06003405c543c0722404281101c100c6800d591042c0c0c1d5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 890997338 1250 890996088 890996101
    0xc121507050d051e0a1104060c020d0602122202010206010e060d0b0109020a0f020102090f120a0b01080a0b060915060d150807030309120b0109050a1103040b04020a050d0812 76
    0xc1e0141000c0080303101e00f060700300a08520884280004105507405544c5944c460500b65001c84501d0300035102c4604040009010460143d104517404a01c0100034017010119552034006030380188011480041d90319007030090b4030b60191810144a0fa0306541c2160703030aa240c0000359118810320030342084d503903018003107070b500c1c0c42e0342c5880c01c0c40d1a0000701c90102941c1d540803c000940c1720070401c100140b0028a000c080720300c10300032a20800801841100300c0d0068104003d4000b104500d00710080c80340c49103039800199560303d602e0003040110044d00002c06c203420b240070f2602c0000c1c5064814545503041101d0301030505881d03008500b0030380e2150f489070248542c400081005005800504101d10000106505d00003606015644255212a011a42d40b280710302441c40304040240380b03549040c0180446221a03000d03660008501c100840c21040da80450304c910750094500b0b440344a0728504002c1503050154081d00207140596941c0d0651406031170340111406503400c1d00101c5c0404a000c2400e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 890998588 1250 890997338 890997347
    0xb060c2d070b18030307110a06030c090b0a050412030810151b020402090a030c1d06010c080702030c101d0109080a1b03053013030201030e10020301170c121507 70
    0x2100040901101e45d1500c0303e087c40c80b0050202005984100131000022504511a001d01100b620003134503403d00700d40c102030409803641c0102c1c00c0201040f005020004000001900d00540c040c000e45900d03049040800d01d007030320a8000c0d049841402805140800b00c0b81d400500c40055159076000241c40c101c2500c000f602034030580200503803010320000080180a8a6002c100450703103003907288070520203020b4500c06605030448003035020494031b543ca50045a1104001d001c2284002d080d82c0200a510780003c0320a042e460014000503103404d5441841d0a000081d50044142428032505403840d000e5016a034482c1050000d140d90003040d80d01020203c0ca011180256a2103c02d6a1f0903072450b103203c000f0358000111014041c984101d09003410001c0c802240c6139656101001580c0500719001900035041401161406200d4882403061607149440551b01915060540c5403403a8003000c0035510304089030002d10300c10340c0100302d1071000b48400204803080b480c6040c1c0014440d075a2000994 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 890999838 1250 890998588 890998627
    0xf060b04060c0f0203030f0405011d01020d08040312140115033309051315050108030a031119120b040605060313081207020d09060f08010b0d0b060c2d070b 68
    0x94262002049951f042003258010704242d49080c3c0c0da0715182c805401d103020f0042c03034803010b46000d81c10400c0790300b8005114150845e406070007410f012101c140c0382400c40085407940850f0392203441d940b00041c4800070042e11400703c00e601919090104465140c1e1054005015102c00c25065403080940340352245105030715001400c0d008000c201c1485c04528084540f51521170482d0840359080c0740b0794040703d40b071060506071000d40008600344008144103070f0050500220f491603401c810b01840d1550340e10348454404d001385560350147d600501481c01c1043d19845030000340302e941041d00074829602c0b800141c0e64050060000700900d0078541c240707a011071146411081d40301e9544070400c41820b80009046c1f01c2e088c1c0a0f6035460095a603a8001c464103840e942d001d00004444100403c94402200b01600c6800324810300010b01c04506400201e107a03124140032100e981105806660030084140300d40c001c1c03c4665015414085020b03852521400c4a00800c0700c100300114640c81c2400a1b83e5651 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 891001088 1250 890999838 890999843
    0x40504410607080601080a060f260f100b04292d100c05060a02042102010503040f050c211c0504030308072a1103300702030a0305030a0f060b04060c0f 66
    0x30310841c2c3c13150001d90200c10b000c03502020404000d501c0b90a40d80000924bc140682444054500c0b81e10750815800a400f26128965104c0d48070303040c018084402000d06402e02c1e0708410354010040662003803182c0c9078468421548020071f030760384c81c4440080f1a1418801d42c00708444440c0c84c3c5499050549101c1418a0040d249201d1035040141d203081c1a4010310070b0300c40340302c101920704882d00003950b950020560002e00140c805e2012500080042d6002d0640c180300e08103030380e038144103a4042001b00210b80091180480e6050700103080c14000d2100341c1c07000740c41001104200740c4078200a4201e01c600d01c002010012502c0000b4241c920942801c2000b014210102c2081d03500700198140038901c103841a1040810840074210b40d290006190804d84000311b92100f69020740c00044141c00940c0240300300c1da001c1003100c3c1006960a20001c0d42c0c040c440d0306c0383e03030310f0b42080104030f81101c1d040459207014501e059800e0000f100d41e1020b440031640145800c40341074442e0301e0304901890544900 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 891002338 1250 891001088 891001109
    0x1107210804080618030a0905091306020a05090108100302030705010c03050d0612030e030c011d010509060a020105090f06011a0a02100c0f2a02040504410607080601080a06 75
    0x81555000810418080c040b49101ea41c410307180d00da8031503200c5c4034002846c404100c1e8900c040009040400d0b5a96000380424a40351607401c0076184c240c280d900010300700c03000840004000c2c40c20340c0c2021000350010b0b8610701103240c86045502007681d800443c080c0d28140300b01c10314001c041500c5a01200c8010450b06014404545c1e6100d0b400710958490004a000c100000d1012039a800d00150410881905940b18111040f94200c103ca5000f0740038a402d040150400000c0e00c03c0d182c03540280304821140d80002000d00c0c12085650078a01c5502e00c04c82c6a80003d00108410703a0003035010300b01038003819840da94070726495900f40e1034907200f100900c491604180c01030540d00d821809a0720b01c00041d4844555140c6a00075002c42c0d4a02c3c0760038000ca00040400c0f500250038070b0b510040d4014851400380a912502008040309224550f0444182d0f618030441c8140310400384964041200f04031005044a0501c0c0c480a00b42c1200284120304121000700015002000b94001c08000c1c544100b8 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 891003588 1250 891002338 891002347
    0x5061513090503070c06020d09170c0306010b0d1107080711221407030207030507080c01060b0c0319080921090d03080114010e130207020109030b07020c090711072108 73
    0x14a0350703ca80041d502070701c1451658100003152400031803860542c9069540f00c1d40828182000b42d101c130180c013007100300b062190701290703495900d04020311800303000041d003100d403600441e01c01602030350140e070608010054140500740c0012034850030398a030181d02c80e205035099110000071030811075071a0705880000c50440700030162400503078004803c807601190640003641d1114403e81c183e05c583e00b4020001003040001d1030100d18210041e2810301f40c0d840002c03c2540d40c40c0140140c5400c40294041c0781c1e040020041003070031038041c1e503060791443c1d801c0510ba00e182061105803280d48100030811040c0851035600551390925080f901c2100c80200288a840380300d080003008486e00b4007844103040100076041c0e40540c0a52100b0000c00e40051074101d940000b1680c0c00069001343c0c2040b8140040d101c0044001035840d0382d032034843c00700740e8000d102c0c01403034100f00b0a2007000a00104140700041701c1c0742c080f0308800305092069406142259500da40d04810418400300701306000b1301460303070105 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 891004838 1250 891003588 891003593
    0x1b031218190608071701150507060605090702031909030c0b0c01090512090102190804060f021002070609301b08030403030e0609010203150108090a060606200a0506151309 75
    0x80c0f096008141950314060140040c900c0d01c5182e8100703009455400d00c6290b404100e003440b8000801c0600c2c451500458a241d40c2c001041070450b040d80d4140c050307000401d6945152015030b401161219403883c05005051960f20340040d45c00460049400c0c21900240e11283d0310b01c02d40045089680c41030403140d0000c4a0b034001b085682080f51258010f000f00d03810344404480c411050035200350406081480c0500d030100940b001502060301c403040d4010480310842c4941607101401c00345001d04008074020300240f40c06444134000300c150340f020011306c400b04084001c2c4031644600001c02410304010408024441c0c800d2070080c04401400e10100004000c100759058104010384510340e0100d0b40b0380d44440070300c9400d1b80004c4480c484524009440c204442d8421040143c000f0120020313954000c80039100c89060f148140c01c010080354140400385900c4541610101c1c10700400000385c40d0146040d030307520741c54001c01b51907011105d182118003403007550342040111300b0303c40882c0200003115091 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 891006088 1250 891004838 891004847
    0x3060e19080c0106080102030609070c0f120c03140313030305150a03080c19050c04110904020a0306061d010c06020a0e030d0e0405100e06010f09090e1b0312181906 72
    0xc90094580d403c102001071030179814020341e0b015080052070f40c0071543c1c0d200b50032602001d440070b007551122480c0c100340700031030070000b070500c0c094010b03030b42e81d1690583c5804c011740301c80380d10405641030070020020022202507048080300ba296052801040c5522460f082126080884988030b51014400d2400010020084000c160021905080e1402c01840290703682d09a00c0500c4060415041954800c41e0361038641d020107162580001d6041c03c0290800110f02241c006c040f2403004a556181d041c8aa96080080d030180e031368001000f034a05601c07080c002400c0a4091304001c00554001c5000c4100314010900d121104002404890309604c0c0304e04010801e9803c680d100c2d0244c0c0c60b020102d24080100b141400c01c3c0d4091050f0402c1c00e0f2114030044454807524001031040103031500c3c01043c0780180d8081c1201180d0401c0040941c0d80361002140c8003080201001c40c86a0b00548101d1301102d10311043d1480e29140308a016081c0da801c4021603084101d5110f4480c040100346000305440341c20 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 891007194 1106 891006088 891006097
    0xc030809010c12030e1209240d1e050105010507020943110102031b070f02150d050a05010b04050f0a1502070e0a0b060403060e1908 58
    0x2d51140c3c03140744894040c110010ba214510556207840c200a000c1e01e10105000701440c050840c0002038160070404140394980c01c28150403030b800c0c0400000d45003030f1400c1c030b001403144001341c125011202d02821040949a4902000803d45d5445002900d14003a4090032008190b215654038030300910966055000100080411040c502c0809000031040360b0660000307400e65041d00c0001d041c01881c0030f0342c9450343e88140100040e088034041d50082c202c02407038101d9a00d03800c5082c04034054007440700c083d4004480c4900c042c855281c1400801070030f01514402c001903103904650303d040da03e00384124030b281d01090109010a1520849084145e4001008101006d83d02d02c025040d40462401c0200543c00030a0100055903000c180308d80d0200c49075071f04000c44c044241c00503003180201d01028000c0e40c0d45008020140004104140103c00c0318443c100c10b40304503151840d500e610 = true := by decide +kernel

theorem cover : BRFrame.Cov 890827338 891007194 := by
  have h0 := BRFrame.cov_init 890827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 890827338 ≤ n) (h2 : n < 891007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
