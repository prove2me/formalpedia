-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5133
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:51:39.72052+00:00
-- url     : https://prove2.me/submissions/ffb9fa57-1e2c-4140-8a53-c839b44adba8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 923021582 ≤ n < 923201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 923022832 1250 923021582 923021587
    0x12030702090c07060e150702191208060105040b03010b030103200a060509030109142b1215080d0207080105090102160b2205030901170f070806040b180906070302 71
    0x540000d0a00800100300194015000442c0c0c1c04000558200105c0c05440500301c9000074060b101030512075004a5484005101e05480016480d0a4910000120b0340102003490940000c0c041282c00b003600074402411701000b004000303103411780980114002e0403c8081c07a40c032541945030044d074400760000a6404014840100c0985a8400408804407503090802d1b69483c0c25043c082030140c00801030103410391024440305842c918011800c130f03001c28100c04814050280800c1644001443d501400380000d05810305085405000e500103041e8922503c003130980b19a40ba500c03e0f00d080c042851040050b04141c004100e044024040d982e00003c860780294182501001118811401740310040c120090f40d001090316882292000d1010288466001c0e00c1c1c04807030300704550b507903129169007030008009d4a040d4020b00300403101240a0031102c1d41c003100c02e03110204110381010000d003080350300c180d07254043c2140d40d545840305403040551441944007032410078282402c00d0002443c403010326004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 923024082 1250 923022832 923022847
    0x12020c01080c18011d0607061a04020703120f021213030206011a0a0e040905070e1609030b040602070c0e0a0c03050f07020316060b040f0504142b0e030d0e1203 70
    0x4041084000d00c10a01c0c100040d450740584000e89005560f5481b0303084000069040e0622019411940d4140300c454004402480c0b900c050200320300c02c101f00940002c40001200d0404417084d0400c0401c01010407002d81440319400504000c94400e45107503941d0201040c04204040d0180b20300c60042480d5030509500400c4041080c01d02d100b8092401c08201036401d006959664650010701e090b50060101c2d076585450701c1d005042410285c400c0c1a0001c1030341c01d210b68440c82494180309903540003542c500e0030745690307a5a50103034000c1642120740c10300d00c1801190000041400134805c2401d2070000c10380f010b00c0704000d411958080d102c3c425607090141003050705a000401c0391185d071402010407080110508185d070017040c0f11039400d0f40c80703810700d08030100c3d040458210a0091340660b1030440825403d40d00304e80d03211520200c2e0001c40c90511689400040710428408003004c4504221080c032806a00090500302c0c41200140410074020b0070186500f840d048a1040041c15001546814603 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 923025332 1250 923024082 923024107
    0xa030914060f150103060e1305100e0a06050a0b030a03050a031406060405060703020f0106180506010c030801051203250501110a14031308070b191a1c12020c01080c 72
    0x4154002001c21400c1c418216417007540300c0402440c4520455006080c2124130292281d0040c2c0196420310030f42d4800c40c1c40c0ca02905c5000032070080700009180000107940e0b28006084c00070f02e081c43d1140e5541d6028030300d8800703000e403400705ca2181d44d60664030b00503510003070120b640300c004620603208807404100c200e841309000c032000e90b0005c0301c40076180c002e2480d080b8904291860380010550800e0b0740042c024589041222134210954002c6c48140c0d01d074801103031b03844499440500001c9120004000b603040403083c12004020b0103066a01c1c1c070550040d1149078071482d074860350400861044401c01e21000384203031010f001e10b142060f4070301990780c2d50040c003002d0702c08060b000b10b070000008581c50020900b1004091940851826144d5002d0300304004595030482ea20b41d8890103582290710780e01302c0703846001100a00b03168070aa2542c003590a002c44034003441604074a03545e0b1902c40c0742c0402e09410550305070448590003040c52905020004006040250840e50f038440305010051041c00e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 923026582 1250 923025332 923025361
    0x50303091005280b06161401060603020a1e030f150905060d0209040b0709120b0f0a0b150d0b0402120106020c1f030c090306110409060b0c12160501020a03091406 71
    0x311101160080004d400102c0900c80d00f2040250000000762000c20083c40b8030300724440700c00d04030003000502d55907030042c0d0aa101ea6000c1c0c01c0010344602c450042103d40140450b0304810700d00d0001401ca0a20340003004455111060543c8010101e504002c03015a83c0150799001c00140c0783c1c03800c06119940031840d8003401900c0103242010340400105164401d5840f540242580181d03007201d6801030501034485071040d100c2208046030580003c0880500d0300400229100240140440f8110b003c0140d0143e040300d8a0060707180e480d54a5032490756241d0000d09540034902d0412021940742102c00391900c0801c0301840d002c2c800b58055445010003400d1100245400780c200031a2400c440b05044a0501464000404d242d02d080386520001a18001030401d9135039222080092a03114460000540070300c1065205c07035408454a01005940500a410081440b90540019100715980c1780d080e03804c001b40c544006540d1b103070000305000120040d00b51400d4030001502d0303c0d003001d06601c03e000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 923027832 1250 923026582 923026651
    0x1060f0902040e010b070816121b0c092d0b1212120c0d110306190803031f031208060427061122080d0503070e0108040609050303091005 60
    0x400020421b02c0600024000300d0740c14405042084034a030340c0a191000c0170904c494905400600c81791404072844040e019946d82c456004448010340614003d00b440142c060444401079000941280c50b52401051203400075000d400710010a1580900c403d00110400c0003422100a0344014042915100307000216807110249070000700140c0d81e6003504480d24403071040c0044400c0e00c0c0c0706c010b2446200b5000a50302955003140d110002400401085d0303d86455409030030041d0b00708201184d0242c490410000da210014090b401c13219640751140f0184000c88034840b80496000e008000c1640750034418869403035061440c07108403080400c502400c40c500004000c107150760b01c3c00464105a4642c065642058400e21840c07213070807400c04001c547c807001e4887d0b04606c0c45000da005a10710b001c1d20607280700307802958940340548014401101d01105c090410340e80c01e542c80903501c0100e5018002140310b0030101004021102c02e003032845084990061200c0a08403100708080310416814041040c42c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 923029082 1250 923027832 923027849
    0x3161703120106030b01110303150405150306180a0c031b1517070216090e010f0203061014040902040303020f1605010c061e2c010506010801150c05070801060f0902040e01 75
    0x41a02450041c0c030100800f47e076443c02c070310021003003000300c00383c0410301c040d01107003500c081c0031a0301d0300503103214082d441b40307401e42d45508560b0001d80401103804039202e1400f440c5003190a01407480d05c820107240c2e0b171a0401e480481001d080e40ca1040034400050700100140c0440e641c0403006881d000382403041c08842e11006c44001030104022078070070010300c1c2010f583e14070120340441c0e03200048801441d400c4c0c0c2c4091343d03500300b40c1c0503059240c16100366485008047c108521501c9400011251031046c5552421001418440403070084a113101401c0614400c1d0014100b9031843d55030a8a060301c0d01072031081200c0c89003010301c01c690380102d00e0710055030700010103d052074014000c0f40b4101541e2081c207076414170302058408100403014200c691056890303c194074003084100c5050980b02d04075501404100d0791801002601c1814000340240769051421401c2c104440e55650708254459002000c56916444140102c038905a515030042c0400305c0214505403414240c2c901801c8140700f100e48 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 923030332 1250 923029082 923029091
    0x12060f1406070c0806090a0309093309020a050306030f0f031c0f090b071b20030a3c150207020a030606080106170d2007050316170312010603 62
    0x2006000f00c1007001402c808400e4071264540f40841d66074414041ca02940019045500040d10913142d06c508c6143c00001450394a0b10500c125962000362a0a01c514103000f80b0b100d0005030440291014081e82100c90344e905980782807143c10907140c41c1040511811507040340310401121040081258001c00c03000138545007064000112500030010a9142491242884401000c100e4815006403181103541c4031201d6030f8001c1180c410700280c465400401ea1820318102d019807003142d6140c032141482c01000c4030302d03040b4165100d403608203081009080e001880040e8a01c03100c0910b1b01c1da2070000100140403810f900a0f111807841010350310545501c150b002801d0010364482444400140d50021000c0c00019650110280206001c0c0715541d40c0211904001240c03082c08240c0b82e4003541e059884d0307012503c10410b0810840901c2c01c00282501c02e8440c000f440e510107000d42e06151940a41c4507800c0e500d081c01c0038245185000301108150070030016900070010b0a10740c103064800700c1c40c0009 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 923031582 1250 923030332 923030347
    0x506090a0b01020f030c01060e0714251b0602010e0102070c1226030a06050402090102030d0b0111101406040c020a0f03030212240a060903080309160612060f1406 71
    0x34203008220044d0400d0b4040010850f401c00f40c1500400216500308480321040d540700f100441e5040e1221600103480382042181c181c6620541c0b51004c14004c40310500c181c2c02e0341d03d0303460001442d0403c0f400c0d80c41000030841040119020700c60342e015a950b0780020341c07911000d5684d03500d0042c0c1600501403011104d140c0380e000d0200f201000420000e00206c14140310400c40c4e0441c00c540c100312a1189020300304a000715290816009a0750000c4043e0002c0d403d048440303406402502d0001040c50400c02444100c20040c0e104100007203207a0115040000d940d42c05818641c02041d005041a008505004480412035030000310117001d00e40042100380d148640f85400c0f8060f00c10034140d810001d400100b030000b01d000c00595150302840e4601c110745001c801c1d41c140511042c00344199404101c0c40502000400d0b00380c0011540001091705880c59107007043c2c9480000813285d04a0b500003400742e03540750030851807407080c44040d1070804090000c0c1d62030102401ba415480c200110b004174001705500 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 923032832 1250 923031582 923031587
    0x60f0f0f11310306050903030108060106050906040632120c090a17010e1b131e0b180a021c0b1e0f0a08100c08090709020c0327040f0506090a0b01 64
    0x50240d6880313502406142440901d850b40c9420a004082460040e40300000e05140280219421400c014004608161520a041e10704100d00e0708a15008250494000c911180140850301401400e2122945812402504c040c120340d000345000040c18003001201242e80d114070401c0100d0700c02d510014190400540840d01400401e801e0461500c01c9402c00a0040383c00071810061000c10740e0301c0e4100d19102d91041c0191030389140d90f0f6004241900a92695960380c2c3c01082e070001e00904558800e83d001021a03071030040c00c4a00300116a07020030750b07e010306a82031002210003502001407040110324400644002d081010800c0f42004141c2d80c402ca07900c0f8104409a014001080086030039a18032481361120100c3c582c284009203050a00c0c0c007e00d00650206001741c4680c0e00800009040181c1c43e070081d0f000101c3e5561510041c084050604046020b000e104c0580c1c20140c3c040019a006203c01c0d241010042590b90f0b00342801c129003501c0e205c100c6940712000a502240400c50700006 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 923034082 1250 923032832 923032927
    0x60303160507090e030306130203040b01030b060a03020d120206010f0e06060912010534080c0703090803190e0405072705040f15050f0307060c060f0f0f11 68
    0x1000c406400c0050b41084521301001840c421402036810301d040c01d000d049807c00303d210031200146003d00031001800405c0720019031a078001c001500c000c440d60b07100e8001801e00383e4001d500711130403414681d0030b03040243d05000c01401030a420346040451401c18103948442c02004022601444000c100d8401d5503035407800601402d80c80e14020001070030b1440c59854031420561218513400d501321030004c0d500b0404d0201b584d41c05420f5403252140e0319121300685003a80314200c29810452800008106c480c4140020101811180340741040100e01d848068100207000c1e060906c96031509013045030040d04408118000c0200c108925614109001e4650142c00a5001260010724222181600070943e43c0010301458076440b66a442584d120204000302003000c09454041d000780340200103207400785610140e4107105140214004010300c0c01031040b0350303d02080d1390126850340910003110105114840c071103844220054035041800c1046100303d807640d840b0380e043d20f8515812400d416000c410 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 923035332 1250 923034082 923034089
    0x1f0e0309040207080702010201200a0c060e19050d21150801050907030b06060307090302011b0b1608090f06010b1e181801150e01021c09080d0503060303160507 70
    0x4119210070f80350612400c0c0e078101e41412800b540c0b910b203000280c1801d08600001c02400c140206203408141c0c08200d80f980c00900d01111141d072541446e00382c01f0000e00078031162416a00450440d820786042c0149080c1d20fa01000341400342927840160514125404890b01e080407100104004405a80001b1801250b82c040e45039540b801c014403103500c9001c10703040c007200d00031102d00d04ea5484201c2044801d10082e2018008551a60020001540182200001e402148071040007140c0d460301c0b0310303046010445e03004020740001940f800c00c5981158051f5000500d82e001400301e0800d044c20180e03215018020500e081030301050a084000081d0101070075603004803040390b02c81d50090251020b000131080005d109200b4004910f0040c005100701a040722035482d6500344800e03c94405640c1e05859008542c11809120602000c20703854034403940306c0c1152a40c40381665031030030080500306004410841c0802c030b0100f0a01c03c107030b03400005842c07050a240c001908540f0b41ca15140e460481d81d82d1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 923036582 1250 923035332 923035339
    0x3020a02030709050703060b040f1a190e0111010b031b0607051009051c020304090f0e06090d0f1407060c050405030601030f0605100b0d0e1f020712021f0e0309 70
    0xb01d0118001c401c0b9000360b801011140c4060105617200d075104250350240c0e018612001945020800c0341c01211010318419408440301549850550b8031041d01c48201c2000d0725000c540303540141b031102c0d68403ca03641c0140b800000204071140d84000000e4540702c01501e41c01030882d9050039218681d50700e03400c076034446900c54110b13101c55070310314140405000d21507001d40340c07402a03840b8065560040c1082e030320260440d41c09103291606104907180104004440600701d41e41c5c0da04060002141041014000c51428008002441e805400180700555100928040051507121604220100c0041d01c5016500c0b500201700201e2000086502d0702440c1d002c0c035414401c00000205010800c0b2070391032014051003050007a50354445562001010314419080180d904001c400002c50907640601000e0400c10f043d501840c5c20b00810b0701c0310384c4a080302c02d9446540014410100450020b0307041620009001030b003260510514a800c4503a1914130501800d80c0328130607486403100a001b1100c2501006 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 923037832 1250 923036582 923036593
    0x30f020c010509120309060112030509040618061406070f050a0c2706240909050a0b031e0c0904060b060304030c06180221101103160c0b06010c03020a0203 68
    0x160019020b864156120491406000f2501c61800d1003241140c4c401c022010040c0403a901c0c105078580ca075074503600b00b07408003d020710405040355034501484004055020720002a80e160517826000c9070b506910800c00c03c100300c0002503442d252031013520187c68010175075030000c00043c1052418490b00d0304004002085401005c0b030f100304a41e9910840180c0c043c2200c1607010110380703030021960359005074411040300d4502c0c0b0700d458040345940d054025043c03804c05607031303960307803c0f5541541d409942ca82d00243c0c88010f5030b17010382003c20081e81c072a84c840068000d4101240e800d5600e0b45245500c4a009070700300d0340000e0505c4000e0700000c8003c0e41c00b4103110b035a445c00d414000d0bc2c01d802224100c2e249411b0450062991100310340060040e40c000301502192065840102c01405011080345041d008040501c4080516441401c07a5080d4140781c446e900e250020b10b080306201000c0d8854240301e0070448402c0070468042c421540081d013030924040303015050605030302d8003142d5080250b061050 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 923039082 1250 923037832 923037847
    0xe0d080c121210060c08030a02120f0a0f02030c030106030b0d140a0303050f040506060405150307090603030e100e09060d0f11091b030f070908030c03040806070314060d03030f02 78
    0x1500900310b9840c60440c80086071180709074807410000328030600c4000707240e40343c450b0301051001000316000303100071100500d0080c080d015a655500110782000c0c0e01c10281d020048070a4041c0604c0780859103403081185140f0305408100c03400e01042c000c5030308140c1d0365003024030242c40341d11141c44025000100d015101c840350201035650105400214002410700002c104283c4030b1188150003a54000080c0c011a030310302041c84000c4c08000d10300032044801244541281d2002d001c424043c0540d400042074840c1035003005000d000002d01114003800b006c14105226503440040e5040c82401152200d1658513290000b403c040c0140f500a01140c1c46072850204020644035000031000b0302b6505030080742e464a9812030442c640000c0905580c00400018007400000010f081e4820f80d9810a0401c0035103c4500902c2c2d41c122440124865100007424030a0320001c00c480d540c8419030345801e010324460f15052001c0c030318000d0a2a0701601a607045c0c041098000d8210804a11104004540b980328 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 923040332 1250 923039082 923039113
    0x90c0e01030c140603041b0512070e0709050d12030908030a0b0a060e060a260112030e04061a0a210f050603010903020a031809020a05091009060e0d080c 67
    0x2000c1c40102c81d000c9140800141101600341e200641a80091605043d5502c60721412001842040c80307001990356598049a01da642c10320300c0b208600010001c224403420b0002c903016001c4050318003030500075054002c100c1c0750b50b13011030030210703d900182c1905800e07901d0009602034120110010406d2102000700070f0909003540c0140d1441d40d080f5a104a0300340d9540040d03403d00d44240c44580c020b44100404994980600d06962000302c40c0b0340703034a800110307840e002c091401d401e8024418842010340c1f000c05040c0e000c40707080c2d2041d5088508100c49454034011f00345039109007080314400b48020903003941d29400b80c9040b14000d88025014107601c0b5190509400900d4090585800c8600c1d040100e001030a0501c0b82110283d41600100b5101e00280c400b80c82200b0340001201d204011041c010651030610300117041091620740b04e0549a4031040c0030050200022001a4100300e505031041000030791013882d46a81c4070f401d0f20700482140280c00d20b01d90078403514020421904ca60060305401c0c0c0c2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 923041582 1250 923040332 923040359
    0x90c0e03010e0a080c030d110304150605090c07020f0402040306141b09041a0904030302041a090a0e040c03061a04060b07150b01050904020f0a032906030703141e01060207061d04090c 80
    0xe214800341c5010340080d0704042f0898034280101a00210340400042c480c01c1d64074010140700740014681700c007003042040042d044e07074080d030001c440300c646a0b01000d51140081c888250814500490b131090720100500164440c040c4402044c82161076100d0f1401030b10018204004105000d46034070068600342c2400b501942c002e210b00106100c070352a500c240508990155108a035008119150061174640b00703050100000d8400e4903105079984000000811604c80d814940001890003411020660300b0802107500c20340c02090305041c101b1101c0000b07081ca02c3ca0307a1418250860005044050400480b0036000304410181c01a200140e0a042185030802402c011500c650341404245a00c2003104261a03860307a04c002e0082d001501d190701e070301d4800083c0d94400390b04e280004030040c0040010702c0150040c0e40002162103004200300018900014050240902d80001e1010515004000b8820714103191682e0210481c1d055080300d6560b0342d000a06c1c1250800b9150310343c540c84405c54034445 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 923042832 1250 923041582 923041591
    0xf0c0515070206071805041505030d08150108040f020d050f0304080f0f0102040501050a0e241e0a0921050703051510030201090e060d0c090c0e03010e0a080c030d1103 73
    0x603c504400111994481e850358454801e0240c0320303000c00f41c40c10050001030007940000302070b901e6088038003040d540c07801c1107803c00350300080d0740d106960f06145070044c03c0d1140340c810b06030410900d40c0400c804038244000c001c50095043d20703080148012810154204003004c501008180000940012a40000908200c403031545600340c030440fa0300c109280b4202d10803071040501160042c02001032060091402c0c8020741d6001e803805100d86100310600c203424040050701003801401190110070210405031303281d0000328814401d0710b04001440c003c1d041d0207581c41407007201c0d010303803841d00302c0050b04000003041150702c10200d076600b030b8480c1340487e100c411800141d158503022400240784400140086403c0300d070182c40340d8802c2810008a0716070303418000e02464010b284103d0150001d500c601b18040100807680f0000b034010b0100300d009110601c0074010511a80c10025540080000810f00202d65070303200340000c0c0c0d101e0040d00c03000c0c107500440390603010301440c025030020002d50b0000218880c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 923044082 1250 923042832 923042837
    0xd0909051e09070b190206100303020604030c1a0a020715050103020a05060d021b070602160320011e030204140103050103080d05130816031709071518230303190f0c051507 75
    0x5648242c1480d23801304c010b10010300143d00160204002c2800303801c02a1489015010700301c02d2044400d010355100c8803d0ba854200540e0009946040c01141060044c1d0303c61001c0040c091545550005400c4007880d0080d02c0c4283d00009440f8000d10980e411100300000303c05260700080e0885090f607031188203d01c0740344d025000d11507290011040c10f030451801d49074000c8041032040350300f115166542441c550382d1818842072a818411440f48c003001c0440e0240d255501680c1d40c0e06100018108000100e041070501d42000d00500004040600365201c80d0002d00b400184c5907116004d5001151410001030640800064444000004c1d507808818603070081d05d585640d24507001c0764501080d0100c0e1320183c0b0b50030100c000e000c060803003003503002003020034a41507002007501e030b4410341c2c10b41a56106403421008819140e11030303801c13208c6040000788120051401c2408403040c0707410a40090001004012400704106c0c401400323059211101500301048036020000414170045501d800c1d9880b402 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 923045332 1250 923044082 923044093
    0x1908031503030708030a0f0e0313030c060c0f08031506031e0c0a0503040308060f03160f09060303090b28050d0b0604140613090e0d0909051e09070b1902 67
    0x305040000460f800c0d03a512003d064550703500c0081240040803170380001c1644035203800c11403a0b50345040000e000c601c5e0802010341080d51841c0303444840d65241e40d008100340031400081101041001c100016100d4002030265603a50f80c01c50801e24840c8040102a8040800b1060000030201465244079030310546040070360700d45074140d88203014050343c210300c1e00056007003000500080c400c00040d0b400880103030041d00450b00300000a4100340000ca20840e5500001000f008454840c090b000014000c0c03c00c01c006107400d54400400c00b60a03030041d010808000616040200c0d8519640100c40042c103007020000294101d00520942c030802024100c10300307202d400030881c078100084a00b1110740c400d4603038803210114240a42e0b500039041c2d039028088005800580314400d4090091841e4150b400b8010303003004154003078040261a0004004249441c04000c0c40250307081701c24812141000359142542c4c0c62410503407230440a42c000c10300c0c03c80007040011a1003855440c43d05420345a07025102c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 923046582 1250 923045332 923045371
    0xa06081c03110f1803010915020d06053c06070b0601020d090f0501111501030b010e09010c050f071e030206070e0910120305160c06030c1107090b03190803 68
    0xb20705001d8055078241c2c1d04010004410710385041c40c0b0f48521841c010b40045541000c0d86c440130f03210910b0742c110341091500018030903070482861141c04c01402048840390080701c00d81d00f40081a000004085000100441248004800d41d02a0034040d05000f80314555640e054508009948004d440032400351050f119a821114003d0400c202503861001c014500c00d445c003001151200d8032042440e80f64060705413200c1d03211182108441c040e41c09a040e41c8403651410078030040101000701850b004d40d1400010300f005560210858100d0f40b616080305880b200141002003440510320f4080c80440c1c000305180c0101030700485ca0038424007076500c0354051004804107214103094112922601d61040100601c604a481700f91111010302a01d41b0a0901405044034442208034900c02d4510006914081015981c10300850b0503007205454150070701026101529520862801205621070b102c00101000b41c4003003009100070301054140000003521410711001c6640152039005c0c0141c40c040224 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 923047832 1250 923046582 923046611
    0x70c2a120201120f0605060c030703092709111207050111011806090309031703150109081c140f0702040b040219140702120d08071b03080a06081c03 65
    0x365036590181c454500c00da8403041e5060041980342042c1000c50f076603a0002c6040d440d528003038400c88450100440d5030340464100a49451115842400c0b0304009881000022040d030070500c0d69025100d8012580c0d80c1d00c0c2c9440a04011070002007604074040528001001c070000401c203045400a0300c90b01010003031202d61a00380c4109400b0007010342c030841560000190240d02400c101c078002d10344072a60300c0d1030b1381e40c0b402e50038804240410420f40201c2030108442c2e40848500e076100702400c000340c0040c0740001c03454548400024110100104504281c0320300d008102d100e06169180e0106a83c460241071207801c1600915016400f651402c82440c000d814a4400c440030200000022034245403a85011079240b8140040d200300c000d014010080180c50b1803540040180c0c90f8400342800c0b500520009043c00030007010001040807e108040082400c40316007020240c15103000e441c04d554542c2000090300150388041003501c100320b4010b640306554a001c0c2c0400400b55001d001c000344207c010b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 923049082 1250 923047832 923047859
    0x50a060e030901020d051c061d0106050909070e13061203020601090614060f1c0f0506150301050f061e190302030c0f090301090f03030f060e0c0909070c2a 68
    0x10640035a019441114405d80100d001e080326000c51055030041040e01716070b60381500d240d64450040e8190206a1103012886e03540c10a02400080c03904504000741400000d250f64009410380b018004c2d50301003c00f460300c40d5052401110703000d0381d082c06030307a03903074802e20f055080502d8060340140196400880e0427151401441c0490744002a405112100d140c104060b80e80a1040580070034010007a02a02003500b03c4210703c2060100000504070f000150f500c01501c600800980c85075401c08805412010039200703581c190354083c1e84c084c192407840804105507106042a03088440700b02034003d004a84090000e040f94404011240100c0010100940a81c0400c0d42d0300360401000b4008035451104d51406041c0c42c100c010000314001e521500d809500201580c02900082d4880c0c0001c45045514062240113208000c1111220729210741030250034040c40d100c0510404005000c00c0481340728060354101140c0003d81c1e1841c1c20461001d95900c054200065025002038035000911071040d00003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 923050332 1250 923049082 923049097
    0xc0d032c0a170d030e0f0d020607080a090b0a020319090b060f01050a090e0622050a0c020c03060402090618010e10050d1a070210090f05011803091211040504050a060e03 74
    0x400b01aa0f003501d0540280a006a4120340c4e0300c99140146403441d000c21001a210340550040d00c0c00d810050300c000c0c4810001051a0350040c204120b010008080710005a4401418030005813241c440c00c0340c3e28120799003100b9a1215030b09040d80742e8103110100031150701403602251140254504080192400c0c01603e07a0700c004030f00a01c50400c01c118900000320303030146004004140941410004840402581490b1410380d6036820801c000306c041d82c03103007051800131400182090f00607200000c1c1d80d2900100002d02980040c4003003440b0351500794400c500030070708031030b10b8207190f85603104055002d20440d0448000c12185000161a040205101f02101d0b00240c01140f07000c0404032415162001070f00d501c0c1144038401c03e07020084858400c01c194030707110b03d0004c2d6601c00a41011400d484a220480c0149040d50000300e0010350001e81c00c0c8219a4082100c8500500340c0c1400a071000540010340d07040b03410a0104800c02c1000320f2040e050320310036402002550001e054556030f0307024030301 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 923051582 1250 923050332 923050379
    0xc0618030f0d0b040606020d0e011e18030204050103150b060a050a05070f0c0f03140102030105061b0f0d09150f120f0e0f030a11030306030c0d032c0a 66
    0x141c110040d2040700184901012000302082111000d00480d08a0b00c49510800060308014041204298031a07805c00c08501c00b481d0083c2c0035003500c6000864005207803101010710000301c0380000c1032844c00300d02c81d0040d0b400a000300995a500e09020420324130903103842d940146882c1030a5010700d40582501d0b144281c4e0b40c2c50f00d00b4030300c0c62070b400d4a842d4044242561865201583c540004400d600d0301d4000d0080e03040401d44c054518507000304641000100410241d0040c80140002d403211801e403081c440041c40b0917041003000620b1241001d2000c01a0380590003448022504942c0101c00b160071100c10400f50b520140d040e60085032008681d0300920000388003907503180103c001c0790300315074510304103c00002600090004240c2c5801c150001041c1c940e000406c10114071600000c01c016003d038084080d520310f1520300006510388013481d02c26403182000c8075104080c1032240e0103a402c0d000102410b0f10203607001044000c0d0720345881015601c6502c600c2c00c0401c02c01c4504840746049500030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 923052832 1250 923051582 923051587
    0xd02101106070f05030a05061c0c08160503060705090a0e09010209150a090504150909050c0a051c0620030907080118030504030210020c030d050a0305071e11010b12030c061803 77
    0x46c8520041c00c0c0150030f040c1c0c400000c0b90181c004c0143e43d02e207811480d21034003807241c0d030901e429045420100d10107020b03641c7d8100040104415100031130661782c401514a4519911a684000507030741300c003150002d0303005070011800c00029400542c000c0200d49412035a0a44080c81001002ca15105001c24a80052204041044581480d40104c21901200642200340e140ca0b08c948000b114241001030724958003805401c11181001c00c24040030300400d890700d440308002c01013060840c0c20201d01c0103100d01e035541d071090300c903000c038900d8500011001210a40e9905000048039983c80321030041c4d012035440c094010b41d0300070007010300360354882e4151030341400d062843d000c000c0d013100b9811010056008140220044e80d80c180180c84110542d5102c0c2a150b030310004000f0101c85004141405114441d68003040301c01098450081e60120b40c50800d420a003003039840b5016211900c000d40d00314615098802d101140400a0076504113001c04580711540d981543c410552000045035034180c004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 923054082 1250 923052832 923052841
    0x506071b080a03091e1506050603010b16111e0909031804020913050c041401020a080d150b1605150709120314181c080d0b0d02101106070f0503 63
    0x390813030401d0700d008a030321484a081510300d03005a400102002c403004505940c0000c6051000d202d10310103400e055a5007800d660402100845620490205117514203a9010030020805400107990094402411a1180c005100820004155401c581d18070551184002908404000065502d68070422030000d81c120780f40414400258410380c540d80d00541e1160303082c000e000c0d86004903030084003250400e036030380d40c601441517148804980300c00b07046420100100000ca00740906480400c50740c14400900c0150214802003070f0301c80d41d44202d412100100e1902c04d4030308906004041d644c0101c0076650404680070910760218801c480c040003151581d0828481c03401c1400040361802d00c281000c03e03036000f0741c2c292112240c20101d00d0604200c0350841c1c1281501740300d0400c4042c10305082e0180400c00103982e42d6030302d5010780c81e0340500c240ea403450310351503c0daa100084c03484c00e1b0300900411340e807420b5031f407000741200b241042c4403003244601c00101301a0341c81440c0840e0710143c00c0d84d50a0450301c8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 923055332 1250 923054082 923054087
    0x20a02100c06111909230f1c0803061801080d05030c2b0e030702010e060307140d020406110304080d0f03020f0a030c0e0613050f18040506071b080a 65
    0x3220410346020f036a55071202c108011000061005045104809680d0305541800070701c5060503802145e18148001035426000c09402c203041040102204d004004001d20f1001c00c5110313600001c2c01c0e00c608055000e040500510500070f5001c0c00d419104101c101d020525001e01120082c812005103501011103003401078402c17800b031074024005d41c0380c0301c1c0740980703000d50b0a540c00d02c51a29880020600038601000c0301440c482c0c610395030300b001e01450070180c0c0ca4002074a20142558a5402640e0001c00104890b20130008440e800c500b882071107131a015001400030094000e03000d49008210b000b9030708440000004203443c1107640203001030801c2601c810040707030703c2c1004c8095034060540900505401c549500003400a160203560001412110900c0007403500001c0c42d0a9402210304000c14521658a0b043c1c0350140c520643d01400540c201c1c20100e402e40030020062210500c250080c4002c110022030071502690035584d0b00704140d01ca880754440540201640209580030801280310a40d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 923056582 1250 923055332 923055347
    0x30a33080a080f030703021b0d030f050c190905030703031d030309030d0c050705220b220b180103050a03090e060a0509090a0b0c0d05010918020112110409021207020a0210 75
    0x702a00e0090f08107140b545200540c11a00c2808c4941070300f01b240d00207140c035030611a0081943c540b40301880075050502e648e012038401e200c2102a4184d110301c02012207402019480c0091901a085800365541d0b401c0080c01c00c0e09042c031006490264982c50041032134000b040d5000c281d402405044200c1400400340d0700d1451005c41110107026440340042c45981d050f58412030a1441d0791083c000c031303881c00b000d00101c44031030380c1040c03040c500f805580469040505450740b03c4141350100150301180c002c001000c00c100c1042e0000a518500004020064003090743c0d1080c03031007511074500598507061481d40b01c0c042120b5641d0043c2060f10300f0482032415203001d40d0000c3c06002a81c0c60150381e600c640c04014400c65000c0c14004d4002031100c0d811040c0c0c460b890042958400802000c15002e130b004000b07101d0403002904008052460250460341c0d940450680381c400f010995583e503841d01240c0c06504a04141c511320f40e00c0d280010341490010400610700d6038001d26500e80311030083c00545428 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 923057832 1250 923056582 923056591
    0x70c05030c012c0301020a080601082505070c0b04090b0909030f030a09030519020f0f0a0c06180801060e060109050f0307090f1514090903071502030a33080a080f03 72
    0x8442149043c2040d28284024480c00050799038443c41880c00600142c84001c000d0403985d068204c102d001c8c502c0c0e031044819010300700b841d880d0140c5d4070403640c1009018607a8540000c545214006000070f007180c203a601016400c1030941e440c81d660340e9010001034580c052801d800d40110300403c0000c2d40783c0c03440d602c4200030b40d1003420f01c5400d01010b03100c104605808001c004c1c000d68042c042c90418010308210264200b90110020540f002e8a541c0310309401155200e911305014140c0c01c044001410041004054a140d01c02007080310341e55240d8210b8544142c401c18049610755a010845007010018424003040150050080b6032030400c50b0301c0180303298442d418215a035180f00c3e0311000c03040b6000f0401880d011020316280200b1000300201c1240141070905141e1003004040001608100f8020380505082d00060f140c3c0e40303442c40b40014221608210311000071400c0c1d0350b040017074a10003411054941c58006903805480d880300c265641c55982d005010340c8028812007111444890046520 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 923059082 1250 923057832 923057897
    0x120402010c0804031203050912041d061f0f1706011e05040b0409020310060e0a090915090302160b0f18180f010315060e0408070201091703070c05030c01 67
    0x40c00c4e90307078541c0c542d040c4616100400081e21a014881180820440c09140255000e6442c0c68a4070f098920380e09070b56502c400326100c5c210328000402ca603498000c500d4801c141d4882210210520302402803000c540280c881d408194805407190031280313a04101071080806031510040e201c0c40515003a6450b18084c1c00f4020084200001729848030740f00090401041e20072400340e101d01b01a4a161000e81c030701d03080902000003d00040c480396a6619080e01200c6008a0014103d01039040200c5a04540b1884c80a0390341070041c120101680040c2940740d00051000d442074180d2034030030340001ea210304c00c140c003207001c030600400b809800c02e11142008000020304048001c482c0b5240c068a00305c040318051180890307500100240f12010000b03282407247d403101003102c2410802c165000c8200540701030903801000c1103040131a4015106107020b0074211043d4040c00c42c0d044241e603680c1d03000200071200742104a0001803181800164421102c00584881600c030f01c0d80c1c208030003d8040810240c20 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 923060332 1250 923059082 923059087
    0x6020714010c030c020f060c0f030406181a07090608071407020d03091503060807210218270303061c06050a0603140a12050f090411040515120402010c08 67
    0x1003500900c142018040641c03408201c0744504440641004240c45600705140c011030108510028020101e400c04c0f02c1e80054981c581c2c507241403240081c11300200101d944a80b010092045c4481490245c0090603d082c1d80300169030303549800c90743c902d603502c00c1e900482c40510200346c005000d5103481e0b05c00c400c881b030000c1c00c102e46500028500c10789000d00742c0125602100600c100016014258810303052410188170381c3d07240c681d045984102911688003c039200c0b8040c40c40d05000c0c460314000860700100540780c100c54948008990700e2003510a00c49244000c0d02c0b2031000da03212010b002206801c40061400d42e41c4603024069095659214041c082041900050006007036124884c000d074000c000006199045150404460300018054170807a404241d0761000100003192030071441a1500d0010384800070703e01520a1409a0341040e5446801c080300b0f5a0408600310280045550407203504000e03001e90183d12a0f180706500d0070406108001e00010059401101c14401c032030f205e58200c51 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 923061582 1250 923060332 923060363
    0x4080a0c0c0e01150f0504061d0603150a051206060409020f06040303021b0414070c03090b1b06130b040b06060708030a05060f060a020304060305040c090606020604060c0e0d060207 79
    0x41c015003150021000758031030200510081c000d021540007900103d05012803a401c410f4009001d40c09207100712010012020b15000002c820700d807000e481d032180944101d03202c1c100f61000d00410051130b5985401840e006d40d002038649401084140d4040c0c141c8040c2c8040c2d1034000500c005090941c0302682c105c3d0111046540c0740d00c410700280020350117039001d000007409040041040d20203461900c0d11036420041c15180d650503410b0b14175000340680c209146404a42e16007500c10440980c045105950041040007072500034460b400b16048505080d121107a40716200700c004400d030440d010741800d084800040005e800d0140664102400070300312810900c1a9036484401d510448250b4043ca4541341480401d050404243c03408200c1260010b0070440e02d258000e6581c0034078031400d4101601c50b0080360901a9494002001d011240340070f00180e80c0383c020103551010251822a050751030001001c00343c40c2f140c6420b5003240b0740100264080c0f0100d49030b4101942140c0001d44500107000d951b80c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 923062832 1250 923061582 923061593
    0x16180b04060e04050a1205040e07030b01030f020d020a091208040b0703020c0904061b1106060409030c05120901170115030230070311120c0a0c0f060f2304080a0c 71
    0x283c820303403007a0f00426002c02e1615010000080d00b56058003030010a120034022040000700305136120046142c0059401034000040740500584c0e11107400c0d062001604920f4000f40c0e80040a40c0c400e01d07100c6103c4039a80b5502c041200070011405460740c4401e101c24803600b074504004180d8a0300a1044902d4034001c000050214001500d04a45040c0c3d101c01e000001011013800b014991f5260611030004010f1300242500d81200424251045076100c11101c105070141d00c1030029a9044000c817000c01003d4110349009601446c01c180c00b05404110310b50003a80c8001d0f901d410b0303407042580e5180110801900798080e42024800042141c0c190000d400c1c078102c018402000d504d100e03007107120241090540913084030407002130400b0150042115818a0340b041201c5034000301035100040da80d003e071140445d072100c10b40070018814054107402c507040c005150401840c841c0d4102c010441c0d0745050742c0d0040140354800c3c0c880d090403245030008000c54140401303020b03091403030704200e000e201c142d41e41d4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 923064082 1250 923062832 923062859
    0x20909121603030b030c03070512030c120a110a030e011b050a051e03070506010e070513060801050f100e090408131e050a120b280e16180b0406 63
    0x401c003a0a00060340790516034580220f03007040070250081c0541c44406004203499100310300529028554030b1714041c0c061402001140e0700031140740b007902c1001ca2010300b50040c0350b10800410740007a0409111001d05140400c8207451158161501b003030518030140103440d100305102c1040a0000031f8501c80020405c140100c040741da00c6500502802e0308000c01f0b8100b0000b0102d00c495031544240a4840010000924181500c03034201680c078540e078542074219068030480102d96001c44040100180094006c24058181d80084031034480d044480b1041c050b0100450380ca4500040d80420400c40d5810116105600540150312080c81e10700d640c1e111080c00d000130340c00030011040b403080c144104824110060090507007150010700c4145016503d6040408812001d080d4203045000300d1100d22041e01c0715050100740006c3c0b0704110b03a125409100034904403003d0050740c010100d1042c00c134000351017140241c035401101900c2d5040080b4494000304610700d0100e402031354581002c680d00410040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 923065332 1250 923064082 923064097
    0x40605060a1d04150501081009081902070e0a050c18010e03010c0909060e0c07080d02090405010b04081608100b0616061d0109030e0409030c15060807080c030a02090912 74
    0x10304020604192921014a1131000d04840003645820b005010400d0042043c18a94500c500c012a558842e4103282c5100d1044112070a2012b440b90000442160007251841c1103841c03003043d0709096134911800c04141c8030200c1d01036080e4002041418003c00c1d40311035281c0b02030410f2419000180180b0302190031a034030f1801090114407410001c2041c0c0b0858000d0801030980c0f43c4c091261424030005440c1c1c180904600104944404070710190540c100b81e054030b1500c14000d00070302c42035a440003090840c0c2d00a00450700280203440401c1c290090b90b42082d402c03589144020302850309940c10240003001d1400b4440e071b2000041000540188290160014946c06004005039a845110414045c022030102c0403a0b41d0341000381000c0843e400105168610380203840201ea10545494100d81c017190201000300525003140c0030b041801000d91082d01942c507104200c40d5142d8444c101c01c0d58440e0031107001c41e80741c1e0000d0060801800d10a0b082900a004542140c1600141e94a40c2d8080d82010b003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 923066582 1250 923065332 923065379
    0x111c02030c0c0d050a060203061318021e010f1101060803030f01050120060103021c0803090a0209011406090d170a02100c050307080a0c050c0a080304060c09050306040605060a 77
    0x28500c0441d44051001401012080b184100e540d09555101901e0b00980040641455404000030b440c6803a0681c5003901f1a050150410154080402030038464000601c181d008070380711080c158000b0010780141d20380610507180d40c1e411f07038a816030498a071b03a034162084200d07541b100000544070104001441c007440e080f083c01d00203503040400040003002d404050f000c100b850341a50040104011503c241503907015038040080000003402e4807801c02403040010105500041040041c40d00411000d04d018170848120700c203a40c0e100c2204c810408030b02400707507000008100107841c61403d05280c01c0542d11488641000f01101c2d1286100c5401c1a56004050f820401a10100f082580b094428501003400c00e2400c504060000500c44100144810030b034980e2503000c494054056401c0c2c032aa85175402c00c07508125058a0000701c84d4106403402c4801d1801c0c041d080d0394150086102d0019294080c00801c45a0744503241c442c05410f001c0c1c0410b8000003103030800328030104010340d2111281d05a4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 923067832 1250 923066582 923066587
    0x30904090f0213330b07080904060e01050f0906130c050304050105092107020112020a05090909010c080f1302100305011d0402030717030412050c09070f05070201111c0203 75
    0x5005001c00c00a210741c0403041241350a00c0e1000c102c600035181c000c0c0b031300c00d21015074520700c90404100d41c007400e40d080b80540e814041849410001c1602c0106440d10b000d40302404059030f2550b40380750405080c003a1940c0600701d400c1d01c5a1604041d0a00396200c00000c01d80d0a4803000e00c0602c2c4100d0342014a40341c0007800002c104414800d00b40181074110030410002c04224540c2c0410160300180c0780342601900000245100a681c41903082c661842c0003034034210364400d54840060400d41c04140c41d00e02601c0501e000640d852012700ca01c2c88034014580360710358150754520440481107401842088070702d90a0a8501c0542c4641403942038030000e076100082c840d41802400d04220314010702d81031107400260208401030b20045400c0f41103c0c2c49a90050301c004084900c80d00354007c1d500850b0115402c08941c00c184070700020040a00c01e016a107a0500341c680d100c0480e8291410844000403c504020480055120b002001054800c81041e034501c1e2010014800001070500c0e034690040c0d001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 923069082 1250 923067832 923067863
    0x40f0314120609041a010e061002011b0c0f0c08010c1d10080c1b030a03060602031e07030e0907030c021212040605090c030a0606060305010617040b040503090409 71
    0x403103801810031150911403824003001c00010340205000802c2d890240c00b001c00071408008441c00901140c42215284a5017507071143c100310680c02c0c0031500d182c0314200e40900d4864050040c452076040c0240c5100500e1801248a02a90f42840e0007070115107511400c2410008500c40700355102c0a081c0440c00400e541154910040092481402d4411050882082c59909a852840300ca00040c45030034011140d5650204405a40c0503000d40b000015250707003c0030032680408401880403011031b8500300031080d20307080101d0741d0b4003a13001c91050011403c800c50741d030b14100c1405006100d101e8a49509551580d4010988401e03041e00c1c040082911100660034a60701072280189014003c4116400c0c40c80c900990300c10100c01520290a0716542d802040c442c1d10148402c010b01030014048807108806841d0240040134244901c20000c1c0c5040008240d40b44683c1030300182c0c1c0f4010024008035140c03516032040031340e00135100f1509844100640c08007034039175000f6040b8041c005d90040890481 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 923070332 1250 923069082 923069087
    0x1092705160918142508070f080703030302090301061a070b060927070f0b030108013c0605041e0b0301020f0301360606020118050303060103020a0512040f03 69
    0x1c1c540248840b542801c080000da440c215000d001e81c0c40c2c012038012109020f2254803818001500e030f50f4400640003060040e01040c0c075070176031030480b44940101d03041e241da900c0c000c01a900c054041d25040d5000103000308003180c4250090114110b006000040159441c0928413101e1118103a40005003c04030303400041c401019070055000b40281c07080385481ca0090030007801c20220414660880c407141200002d411002c00101c005130103460b000d080d803191134a245159035002489000329560a02c01c4240d0f251086410031040c031400340320348142050010400c030003030300300d1203084100e0140d85080001d903035582c6003c0c200e54110300e040d040c0710303040341509031a00760f0300d440b08441c1c080e03030040162404906503001102e044a00c52041d003803810032a08600c071514040c1401880810080015480401c3d01c55404502110b085400802071812080c044c22202e4400580180c0301c0d400620015959500a400501e003401c4e051612614140e14200718601181c1c0c07c5d6415200e50008004490400d40c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 923071582 1250 923070332 923070373
    0x12c0709080f0604050c04020c0109081605060106110c014b08011409090a05011a311a041b0216030b010621090506042901092705 57
    0xb60501501d8146025294a135440002c1c02d00a80203550014414050602c00c1d44000c1c1100c2d4006002903456007028072540d0081800001a00c3d50b005960001501501490300186007201d880064200710390f65030010342d5548209030000d4441c02c901d030a809820441c541c82d1017090703c8503c1c41114071010030b000081c01d10303c280700700409004410005021080ca48540b90380311075011688524590340e004175043c24401003140c000d050f9802c200c4400c00b0394903800c0c01030001180594441090781d090391003912a0100300001c10310905c030041d1044110700403035000381422070080c0e07038810401c110001c0410304070707840d802c528422034a039140040c89482c0c1c1885501760505201c48140045820754a072072006c084180728100501c181d000d980c402d1002c841c848010f00c80c82c00380042210115604040e031702c030320045a00302c0b80e002410402c688841940d800e03401c0160000d12850002e6802d0083e0720004103581550702c800203504005001c1440001900c2580c0301744980081d100040410b022041c052 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 923072832 1250 923071582 923071603
    0x1806240f060207170109020a0b0c0118152c011b020a02061c060e1f0503030a0509010311070501020304150b03070506091c06051003031e08012c070908 66
    0x38904060030840e49900050f40340a590303001e0184410801a40031544c0100040304c80290804040000020008801c1c0c1c00790100640183c02440754802c80b01030114414a9034030003c050715000b5500683c5144154000741da000c9011040c40d60744014007658901c6032041030540c184d84c3c0e454522704911020002d0440c120855980005c0400c60341c01d600040b4203000300c400c503024140c0e80a1400054002c241c200300010b0030302640c1c3e41c1d110f043c114139003a8007980040031407040307402d01840068503090020880c1c0030340e0b499580c0c1c9424200c02d800110040c081d8055024400072060052402080081c4000c5014a12032604c020120412400100503204140380c5144031345c201000400490722140f04581840d60102c94a032140c100134280d0340b2312060301078800b0780414a0b103010400415421110041503074065103404180c4400b01c40c2c40c42c01c8840e210680c1000400c041d0040280d002e80d88040f1911807030541d040c0c80c41c0e20924650007d03245085500ba000100001d9017000302c18000e01401504 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 923074082 1250 923072832 923072849
    0x6120510030b2412060c130905070e09090703020619030603080a03140f01050d11031c05180616030525050d2c060c0f1b0916080109180624 61
    0x42244c0031070850380342e00303000b003a0000340070001684600724981c00310790402408601c001041a4149190700501c0b150b841c0d200c8500580d050000b040003d5000588501200d500506180c40c0070072071802d0304141e201c88205801815100c280200000700c0f6000a4124031740c580c2c1e000a002114849000301e8004081c04010a150082006201c0c3d0344540d24240c88944d00410340005d501850004289048000020058511101c0031203c12007940400186218285540d1003003030800413001300f0102c1c2c42000300700003901641c2d82d024000240210f000d89090201030175008a000e80340c94044612404e036900c11280d5802c148041103410790030046d41d0781805c012510300815580320354003d0400c0c1e4078400d0405d00c2400042041040c0c3c0d1002c07c00c1c950701d40c0c0301009948101d03004100800c00c807011340302158410410788002031041c0141b184440c11504c038650316403100c3e9181c0b01c0e41d007004105c0700fa42caa03003030301c110007290300407800a006a0914010000b06a841d07100744017006110307103001c1d400c4640d5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 923075332 1250 923074082 923074099
    0x16050408070b07231c14070312050a0216110315010b0702090a0e210f0409050f060d0b0c090d02060a0f2c2101140108070f06120510030b24 61
    0x40d0b881c1c000481034400e502500c0c4c0400100d184020580d03d082c0a98a4504030b046d0005041080550160030f0980780e40000c04184a5a15a00391201c26802841a8460603800c0c680d90180403c00d13001e02804132480182c29507034200e02c0f0101c03c1c054080242c120b01e5080d90006110700031401d1103405164411515242080010211040c6503116030754002c0580c5c1018240424009003ca444111000340904441165495a8443d0540301130501203030407400b800c1910300060041e0510740d09000d00c01d6448058108942d5415808110a4003e60100ca80100c1c07030702040001620f400c0001c189800454984068142040c0c80080c22081e10300555003c10f2504c0812244501811000c5400d02c00c0407992084000e0b0034013109040d01300303c8140380140e0b6090803507801700950751200e928140c407643c40951f1041034840d40c101d0407842c000e00c100c000050403003610f4550f421503940030030707000349905503200c0d0165680d484d00d400c520801d4804480c2121580c1d801d104089900a800000d01c806644052 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 923076582 1250 923075332 923075393
    0x308120c0f090d020f2211030105090118110a090315060e06040207060b0a120308070f0e0d05010905010e070f0e040b3d151716050408070b07 62
    0x841c000c035007102d0301903a0507514000441d034812168440101c80603041501e500015044020f0b150f0318100000211450001c14442055000089a0503144007410703192180c0d280804a541303a01940c500b118102e41e880403201d00781a00d8000030104032520b41d907100030090450038038200404000000540041c90304d5002c000c0c510900040e80e0f4000f508640040c0ca1f4131440c10154054845d0341c210030b500c041a0f6501181c025039841c2a040760b2740c0070307a88041080d99948000d40e0a001c03154441c0c400b00b9000c580c650a1403603c900311800a030303c01c0001203842c449640e59242550584d001051158020301d905200c0c4811000541005005514084045042640391034000c602d0152038005481045800034024a040c008e07608103205c0540d0100c0c544d41800c080c0c0701c046003001c1c041d40310141000e1050100140c411400003010f000c4070b00180c0b0240e1106820b40b500610359070b150f1000d10006100020f110344c0140181c5004118500c40b540d62000340d450510b44060f07486a409503030388501030000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 923077832 1250 923076582 923076607
    0x3030a0c0c05100209130f020409180b040f020d0f1101080717010b1b1903021009051e010f0f0608101e1109130209010909063c0308120c 60
    0x15040c0d04003260b0010f0b600c411600105811090904800070042c0c113140147c1210b150590081c4121812007404000d22504910020700000403468040c01c2515541c021a01040480072a00c28207840100a40c405040320b6541c1046100d040009403107010840101d030845581144000b9071107140c91609440041800b8000d902c6042c060061014500010581c5980458801200d403a240818001c94042010390b040b1007801ca908507104500500034000b2010326480c180c010542499480300280071112034050086846c480c04a101d15410764a82c01c5a101c600300034414a40b80303000c07400c0040b442c18101880b652419030f0544803e9145858001d901100e003407100c0e983e4022a52a06020602101e0002400554060001010b80c005004440c01480c410b46600a003420102a00c4138070715035540d0000042140c5480c4038202c00c42e004d40c51403006400c0c08070000000011398100b000d0480d00c601d001100169001d03001254020000901800d001050030003640d0f110702c2d1030481d6450240710101d42c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 923079082 1250 923077832 923077843
    0x506032808030c0f0403050304090c0302031e06032505210304170709020409021210030c060e0a210c150c0627080d0b06030412110a080c03030a0c0c05 66
    0x151214402001082d0209103400481346494503a20b000d0f5200d82e201d040c030940342d50151289910240c03030242c2583d1031034064000d42c2d1083c852490300d03030442141d1b0400b111840701c2c010451a414001c2900183d001045180030320881070404c400c0c0000d2034104003e00803842842c2400803c80d00c800000e4901c00440002242d05641081001c042da58508542f01450220300c1d41101c1c00ca01d00101300840d0b01c60443d406068110310309074088800e510380d8151011105444c0c0406061203806001c2408014040c1d030112109840241c03001409903074505244607035020704441026a070702200300e42401d02241c0c2e682e03c40507180c1030b03903001c41407140c0b548040c0c02c0006d14030004014940f101c00c001403800c40142142c1006801c084280340381c050704c0c60f0040c6141d10144071060030324a001e490b60998180038040e03a00c0359500845140d4004829130059415010f10a0120084c0c494822401c0000d02036030090251f15100300029516070400b6403007c4180c500312039181e000c01820015032004204001036 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 923080332 1250 923079082 923079163
    0xb0f0301060f0207030b010e0601081614031e01030c050f01081501210e0a03090b04050f0d050f07090203070825120b030f242e090c03050603 62
    0x2c01c4000c0501401e010303400e0195540c406840e01c0708401c00007c488001c0a20207118520903641c0195580c0c82141e4800880d0f0701e0801c100000e5114034800c0140e5110a000750341190300c80c80389044e401f50051144a0ba42c4090300120362240e443d181c200701c1804c080300c0c05021403409080107040b038500481440003140d040ca2400d810406512040503030340c1f0706801551200c1d0b10520301448208000c500d8940c1d1101094400c50011710342c404002100b83f5903609075004d513540108081902c96a0703008100d4600707038008080e22030340113034000340c1c2d0076801c07c200e1b44009240181001da102c0c6001c10002e4605078004040d2a042c0192041000c4005000f43c46840c09804a040c41c5280bc9039000791900100a00b86440ea0036204642c886000e01000285020094401800d09501c9030901d40c13103017070845419951200903200031102d103d10303650700503d00c0d00c00c000011025900f00b503607040984155032071080c0d000d02181d99a0244219070909100c00f444015850010302485140043c288152b40b50b00745 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 923081582 1250 923080332 923080337
    0x11203081504021602090601080c040905151c0618020904081804060605070209090c0d12050c03030708090f1c030f11030405070e010609050a050913060e030a090b0f030106 75
    0x2501004144416070686001510444d00d403100d0550788030a1500101c026403140c054000083c0c103a40c804c0441600c5128202d0500c0c0c01c3c40d1074a44400080c24003c0c152020000840d100b1070a40d40320b806100c01001c0070705a2440d051003040c03d00703000300c407131250000d4451458030303094401586071400c1c490341003079004602e503540314079100701c482c07044500c000b5075035210b8200b040000d0300640c0980a005103a000302d4101e40d03a926070420069951009040068010107855044808101c61541602c0707800b000d810402d15107004e01c4c0d00380341542e100712281000301d12903c0074441d080004018000050926a0080c2802c502c1c01ca83c1e04c2908540d2482c40041545869140008403007942103d200346c041443c01c0c548030b08251400a856031414010070916940d82c80c000107030240300d40c15030360454030042c03ea0004241800203001d105240100107584a0440c8800d002c0010142c0c0b00d96445020f0721406591508600d16005220200d1540b0200301c030b90f000c0c001280040725080413241103480a0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 923082832 1250 923081582 923081597
    0x1060c20010c060c082d01030b06011101050a0c090602060f0c1806070506161803020402030a0b060d0b1e0109120311060f0703050c040303120e1c180509011203 70
    0x40c00102c49403185210001c1c040c60520403c0340305160046062805490240780300981c111943c00b03108150307000b4290800001e820480100045420200079030382041040c0340c00c640c0c5070fa84000c16801e680d0296080003a16642d941c0990a0b250b0018411019000e148040c2c003142c01d143c00e60b100d0340b000c040d1000d83d00c1c03040080c90740d00503004e8500c100404040901030a8854074030341412516180111001c0c443d1040e9051210b803041c0c402c1d0701504030003c0e000c4107039040f5401c40d001d01000350030040c6100c074225a01c51043c0c800b9a6440041c1c440c031141542d0109880312010103020001c07021038258800c10380c2508a900040e1307004040d90080d41d030000359510b2628641d05048a5a6401c2001482c0c640107850038016520500c960241c0700f410103413401e10643d102c1400d4590140b141d48000780010f10ba12408640001c40340d080703050704d4111501161520440d50000701131030b03075007900d0900c04600710b0020390328580340f02c1041c100100411a090042580b600c0240240f003c0038000090400928 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 923084082 1250 923082832 923082893
    0x1b0a170c1509011b030b090c0306010203160f0f0b0709091e18080f0c0c0904021005070c050901151805060a051620040b0306090c0d02060f2101060c 65
    0x9504c94110041c68800a8041c4280d1410150041c62041c000b50700400402c000030360078180c8907003100c2c05002c060b4010741c5480201c58041c0c580f1012181c00f200d43c002c09802060100d102201c8a11b562401a848030f80c80b800c0041004d040303202940d200030382d401e0400450700c084071038200c0745006d902d65404011131031004c64010580b14580d008001031254202007003039081c0390600b1001d020261140c60890303603400701d80d00030030403850360443d00203520082202c010b600b194840c0303004e040300520481100b0070f0151600f0019000c00740c260061a1141c00101c00300c41e005511035000c0b00103419101d20141c00300d0902c0d011aa41d8800c10540c442804000500043d110829070284000242c0082e642d41c0801040e4940d081300100c40f240a034401c505001042000c1d25003c6240d07809541c86800502141040400340201000d0054040c0d9206000b402036654000518005200f040d08442c46800240c4241c00c01603ea840181c1001c2d041140b1502c6820020345040300d4480c1c0005404c01c4031912882 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 923085332 1250 923084082 923084101
    0x8070c03050708030c07050f01090f060f0e0a06051501030e06013503041701150e09010921090f44150a090209010306111b0a170c15 58
    0x10b8440c0240822000000c10048401c100d02816582e44a0010740c0d1102c90303102d48070f6080e58201c0002500813000001600c000030740315400100e0b4901e283c103000c2500c2c42c07200101340c2401701420054881507140d900f085001031440000e040003010900781040170900041e046070f80d55405000b8a501440342005480c01911607284a4801d88110062000b02c0d581d45108103849030003500c40c18500c1410001c428a003d00103000b450b0006d41d0140c88000c52915021030103c2c0c110020b8014099550b032240307490045500402c0d444d47d50f881c2804009600c0c280480b0090102c40e90781d1024589903001c0d4028003006402c0b2207a0f1160647c17903880320f0380d01c0b04480765991b002c00700c0140404034198052400c001000001c1486403142074040d80c80202969801421001d0711400c142c000d600c50941ca00520010b040356026184038030f200307003500d81400701314080d4a03a0003000321050501d03a800900640200141007001105841808074418248110004103541c0c0303208040a1308400c103075000000302140d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 923086582 1250 923085332 923085337
    0x1b0106031e0309140f240a0c050c030102120408090f0607060c080606030108070e0901060b041d0109020a09141f0f020c030109050c0d0305040513020a1e08070c0305 72
    0x541108520050800c01040c0c0320008085080c00c8000c6660340d44002403480281e0f55034210001c000d441085ea110125080080c0710350102c46122040780407a80031007404032200044c0000305055152020f003030170b090070110702d40f00d606000c03203100c0da0041007120000007164242c1c9400c01d0b409000d580d103600103080080c4011903044001a008000402e035102402210b4200280d540d660b82c4580e0141c1c0c40309414000c50344002d028420055006400801400804000041d44481108000200603480f03c40d070a055902c01e900900f00710007403200c41d00b91441308182641c01008240c0c801c51034414200d41c0500302e0081d42c0328610032414002c460071816101c104600b000c2810707003450712144e800410f001511181036403290b9001485180c4d151021801d05120b86980e454001c00100403049192007040308010f59030400b141000001e00c4000340030780314540742189000c0404805612071007440e0700100401c8141c0c0040680d005000e40d10700c802038022000c00d80042c401c0c5090041e003643d6050075101032 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 923087832 1250 923086582 923086589
    0x12080a0f09200904080a05130b0c150901060e04080306030a060f020c010c0e090c0a27090b041b050307031103040506010e09030408030a0e0406240e060a051b0106 71
    0x250415005004000ca00a9075956000000781d0035081c14000c0c03001d01070803083c211070080034030204011a90b0b02901850290402d0a0128001d0145588505404503d6000803d11007655400f905c1038078201010401e41c52ba00801d05c0c0001c00045140c11040f41050701c011700003521782c0000201148080e20b00b8410a1220307a0002c80500c143c1a504081100940c4034803a90f110035407078030f0000c0000520a241c80c000300e0000400e0503080d500c40385004521341e480382c02c0d0401800b1314602d2001404024408050003404480c001002152400d655142a203c8041c10244641e1505490100031300485060240300c2004d80b5100d81c89580700c1c10158002d1080760005003d80c000402008200040011254180c0f20240107652aa4a80c00000c941d42d00803030240c60080d42043c4201e90f030f0540300d0b11940e0f0490b04000c0021591581d140015007220800c0e0300300050740d0410341c0303040326801d0b041301798550b00000c1550785924051221000810f680160201800c220f80011030851b41800e003500a4000b5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 923089082 1250 923087832 923087861
    0x30f0715050411030105010b0903060a0f0b10180906050d0303050702010f020d0615170f190c050a0e06130608060607020a080615010306150e12060106260412080a 71
    0x1d6042a060684042c550808882d11a40c20031001003041d40080094900000d4054000c0079251104031083c005400404203c1d41203d80e111101c2215a584001604000c1855291088151004110040c01e00540c1d0040f90980341071180410081c1c0f28100039091080e010301d0002665102e0300012405043c0c40040742c0010390011544403074038281e17039100e40112504e240d10301000000b01c03401a50f2410304004d0301502d0704d000c0c00010750201880200741c1e5000c5a4011040148450b2803199412a01d06140040010f480441d2010b01203402c41c07d04840702400300e0b50079041c1600400000c1500d107823801500c04002e4503902169a0b6110441581c1c0303426401491308108545520076075540741411103010207001a880c40718060ba500910541090310700c0151a1840558440c4060340c075403441c071a2458001c4030341501040d84c0c00c800c0c003019010304080d41e11944001c07101000405c0b0141d80103000090401418140000500181c042e000506410b00b03007054999a0350315036000401c01507200603270 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 923090332 1250 923089082 923089091
    0x10815131d0705010e0306270f010216031b120e1f020d0206010902030105030c090718080705010e041509050705070b040c0317070f03180302180901110a02030f0715 72
    0x40c4800202c0c0c00701c260b80d0b003070780e13081c480108650401d60b03541c0c0300381d0312140207011700da01140d40d48032456242c0c15544200e2040700c00700f000c0c0240b40c03400c903401003005842c0315020303440b20003c1540c4140d080c2d0318081100c20789400c070340c442e8a4035106800005041d006100a8401c2444541c03100702000c0c0c0300c20400c2200003d00180c482002e52594940c0c1c401c1c4005010b050300200d1808000d1080e00d050361005401041084901e5090200c1000003030040814000c8600344240180c2e08920080302620a00020301042c2c3d1800b80003408c40130080444900c0ba03400e10b020094007848880364036040b070f420700701e001c2019118128240c2d410701c12003501415001d00c3ca0200014082050100c0c4d080703030b10520558403024900c8140d000c82d40100200100141ca500b624500130911030359280c1250000e80b840303290801e41d01e034001901c400f0512601c10000700b000c401c20460102c01e2194101c0712003450f0a0f40d26154040100035100c2c4949000d42c1039040010a4240c00d116034801138442c2108620410003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 923091582 1250 923090332 923090381
    0xc16050304030606030b0714090f060f27010e0108220b0a0213170a0f1104090b06041103070221070c14040e010c02190807050703030f0e01081513 64
    0x100941030a0200ba200f106d4a0000f1030100c43c891802c1511007689041070b2030501d600b440410901c0c0c6295210190700210074440c0c007100400180c000c0c000e0034001d074004003841140c3c8000000309100c1000c11030501c400c2e900f0310442e80e600310795895400401d9814041c002c1c0510359100c02d04104800010740b4024040c010440b80040c00d80c0207000d409265200c103651259185800414104c081950520513007241d10f0315030004991074000550144240c07080c04411080c0c00104040f2001140b060b02c03011318020030f128071800e007403096403030890707015180600c0e520305004c01a40c0c41d072242c070900002e1001006030010f042d003120f042e10605980107400d51099992900b051a541d542003541c113105910340306074a07007a25014403441c9440103468025200c13150b25024802184003240c40c00355070300d0400b0404400098030a211400203035100c1d465181c48440c040d4001854070349510452411303c03101c2c505001c03141240c024881040a42100e070752042180340765500000d0300c9501c0e800398500c030b03092001c003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 923092832 1250 923091582 923091593
    0x803031807080c100e030c0301020c0309210d0c0807060507080405060f101e031703071103040810090519120210052a0f030a050402090105010509090c1605030403 71
    0x55420500d80c00c5800080c0c54407095901c6510000940c1d5010740006040c0c0c80182c00389950542244006040c1c2d845c808541c0b010030309982c48084104080c0c0c0001031100e400340307840400d04200515010281200700e0803104019a1511034550180c14801d07400884000c0129142c121400142e02030001e01c540e081c9100050103e200c1034408032118010180011442ca0b0032006030303403244135030110651442c4d140c890b2440e1990038003000c02039210300b03060020000c580801e0203c0b14180512000c40c0e80c92404d038000428070b000c40e0000449a4104000422690f40c00168501110301c011000142c140c01d0b0b847d18503d011541d00c61010400c0381900c807001484200303031b85415881c82c250240d03030002e039100d50004103e031021251115600102e00700202000c07014284c10142c00f443c9244940340180415280b50b081e0001c552170f8169030707140c00030801141404011341740144400c0c2812070401212a000411604d0000e002101c8400c020540481e0144030003504030b45260000141c981da241c403030801 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 923094082 1250 923092832 923092861
    0x50109450f0b0a0518100c050c010204082118060d06170d030e03040602060f0424060515160f08270910050904200604120c080105100b070804080303 65
    0x201d040c0914103030001711342140c20135100f003c0301d00507405011984200d28000000304030004421041007020301c0510341c4500248010800740c4100c42c004d060400c000c88200c0c03210814180d880c2c089105c2408200903580380500c0500c40d006080b03d401b6202e0441e1410b6000600d5240d1010b150200b5009034940c110401107042c40d012001580d00f03000310101c0348200d607501d100f507100380c00047c0d20a20000300440003006c00343d504217100c0c500701b00c1d612084c05541c4031006c8555806000d05641ca00f0104040c2c41c202022540e502c80c1d0402c4079090110380921402c1810300d02c00050f000103401d50214040003180b0049a00d00318640654541d4001c00301003e68001c01c0300107641d4000c030159804105440c01c200c021500b107910003410981150b50784d55400b44548a0204e0fa014a140d003000394070751559a0301c002d04003501c10b500310090311040c07a003403284040807140d0100d54583d1604051000452000d400300d420784449600c3d031381c3e03251043d141c03d00c982d2040f40c1c080d00071400701106215148803100027 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 923095332 1250 923094082 923094091
    0xd081b010507140d05060325150c081801090317070b0a020304170a0e0d0b09010c1d06070c091d071403031c0b0d0501050109450f0b 58
    0xc2040b95a00c840903a012042c00560840400301840001c0081800d90850f981c056030207402d4807001d440d90070b0541644030030700c4003125451101405c140501004812003804044407803600450a04450700c49102900c54030441110070300750744000100503401407004000455100b4080041d600d0300d405114030780d4101720703403c5840703807201804990798502500a0303c0c022500710340801c10381412401c110081344d002d0a03881084c0f00c3e40b03030070000050f980e5080140e00c0c5030240010f0f0182c0e2a000d05200c0c219000d0000000500403040b20100c5100f0030401c81c6000c110095400d01e0ba180c0b03550a0440c06040d983c2e004c0000035042c00b4500c02036410707800c0503c4401055100300e61900e61103d0060f40096580b5006a0f09540288000c0100001103079580e049192000310000d20b1056003130100d010131110034025110b41c0c0d19400100508000c81c45204101e90004c501280c800011300b1000b6030309034481d240c002c844000107941d41000e4161134916241164030648001e01240c0c40d1420311441c0307200301c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 923096582 1250 923095332 923095387
    0x20d05011b050903150402120a06020316020d140d0e070909050c0907020d050f0909180601050406031a0703151404060f0e061221042303060c090d08 65
    0x44100d200c10b401030058600700c2000401038a4210705000e5800d4010340f00030010390340082c40040f40d20704243c1c14407070010344502461016a44e1710705042c0b59400043c0b07070148802154010350444c040c450b4020035090201d60040c43c010b68031a04020b6a00c007030424035180e4403040c0214000000c03030b060185e014103141440b920690b01d6016810f0208101c00d60112001d01c0941c00050840d10214031407001001c9601e80910814105500072010540060080351658503940342c0042400781d1282c1004440c1c01401c0c22541488010300355070328541400b030000080b6014405500110b00b95601913040715000380c00310b40b034143c0095991000405030603001c3d88014007803443c142c40031400d80400c3c1606c200303413100350b0002c0e000c41c0c85440a00198481188100545004060740362030749544000b07621070300e400d0707088246844d40e0a11302250103503210505803110345c907a440031118075a2404191281d1010411003240d80381c4192101003002d10001d2503000780141000190b405000c503a0b5401c0c02c080b903180382c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 923097832 1250 923096582 923096621
    0xb060105270f0303070305042106090515061c0206090d0b04081b010c05031602150117070b041202131b0507060c020606130c03060905041208070f121107020d0501 71
    0xb80516440c1e1049060240004104100600c00e0190744c00031031081c0c60403005ca4910b20b81d80b41e02c81800321110303220102c1e00c507044005810301d0902c0b9813284507040305003114a0b040c0d10811401038100c6000410000f40210b01c08a030160466580d401d0010003140c2040a1410ba842c10b031508803c0b40d44a40c0d0801c12203440d850f0761609003c070501c2604040a45c1c1e840e00d910316107400e04402105400c8034120411841201d0300000c000d8040700e034150007403401c3d0b082c03044210020b950b0300d401c210240c0c004500401042c0003c0046030808414110300c07503015200c0b07140d200180c4203001c0252168624844c000d1681c1d140060382c45a002000700341c043d015400811000320f40203004c0b030300c899065032a03950041144200b2000c80340e00364040d10100040c3c0c03d0004160703507684444010f030380c401c5030306a40040c01c4140105000e07420400d621f03804685071a100c480d680341c010010b0800f918030b103c1f0001040e0380b903503020340102d8154212425a0780080500c3d055504903d4414042d1131980d62a008510f0742 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 923099082 1250 923097832 923097859
    0x5120906040b09060103050604030c05031909230d080319021801110a021f0302130f1a033c0906010501090f0e0f090a140a0c05010c0b040b06010527 65
    0x2c036031581030300d9211f005060680c4070764030111008540450300ba10304d170004110750341880503403901c0c00010341030b140c48002400e807610301c0c44510740c0001940d0190203150a88988084e9981180034a050b540c000d45154403a180c421164400c04221241701c207410f80b0000d11164001c000381c0589192003404d0780c45001202c081915180c940090410080d0880d204461b45034240051140614800f03015207001805d014402079001781811855000b403ca8035042d20080c08014100d2440040001300c805500f442c506100d1034031203561a51030400031007008803004c209030342c8019244080440d00400c9415500b2b003071903090705880c0e150a1040d02c0c0400e00f01200080d84000600d50342c022a6160210540310780c2e1207900d0400350405c004c0c000341c007a0194a001200245000a030300a903c4003907801042070600c0e6141130100610144c001d10706000e5910100c030006082c0340e02d081d5100303901c800c6486407078650380010313076890203004070040c101c3c00380d024808041e04808100388001d074030484402030800c94 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 923100332 1250 923099082 923099101
    0xc031e1e02160f020f1c02210a1704030210030b040509190b0402150c030310081f020c011d10050a02070c120503040810050a0509011b030c05120906040b 67
    0x16071070281e00320805902ca6540840c0300210102c50b1103001030400601884594001107040340a42c3c5070b42c0264180070152804e42c1800300b00d51120b01d50114000c503084440b03402042e0f46a000600c01000c604005283c1300e4044141400e550046d80d010780564021404403001034050a808581b19000b145420700080004600040c0c401039484020146042c1013105d4a40280e00343d0014820ba8014685441d24030700c40a400b030080c0310911102002d0340e00e1f8240082500c0740289c0c258070000741a8054112060b119840e00c840c0e80807000280401079840b041a401c07140540000401312450a6078490401c2064401080500100340225010000e5566000d1a20100e00a05201a00c0220b42c0d0390144603d5480316640407841d40501c00702d0382407640e1992803a15080865030701d2002e0603201c50922101c0741040c01002d4218050200071302c612105002c0e00400c140391903000c0b804040e00c0f040c509004c41d0080040b6010f1f20134006040b006031516101d807681c0e85100b620121040845840060300b40788 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 923101582 1250 923100332 923100337
    0xf0702070b0d0518070e06060f0c0d08090708010b060d020304050f0607020c0102070506030411040c3501050f0d0816051608060c031005101202030406050708011211040c031e1e02 78
    0xd0354900686d226444040921071245c11220b0010360b01d400030440f0b404c0b8650208885d00e03111002c1e07940c49829142108440f8103100c100c0e03200802c030b03a0501c410b000c01940e440007607a4160340360600068407079171542400d0b1719042c5084500103840c014401441070195000c40e107050440400e0b001c1b1009681d40342c0c01d00007984402c50b0003800d6070303d40c00140300036454240c10842c959003480c131f0654204080d8982521000c54200080c1c0304040f1403600c0b46006510401c011030041074110f4030340c9840440640441c2c1146814400101000000110558014046408410959048001c45418600c0c0c2152042c07050401e0044014501c102c1d00000c0c030300712078071040300e03c1020030032448a81146840140b241c926003d4040340103200003e0030030f404504580c406944a90b002d4130000c0348c2c80c100b40d00d010b4040c82042e04500f80414a02e02000042036502500010304030041d180000c00d5903d44408400420700e40200119212880009040540303075900f01c84894405080c00c040c103100042104012403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 923102832 1250 923101582 923101589
    0x131b0e07020f031e0c071410030204061b061e02040807082b050d09060902011e09120c0b03040b100b090a090506040e1212130b0f0702070b0d051807 65
    0x1d0348100954400d034200145212112401440c00600301526601ea840c1081b130316030041402000504007240d214900500f00030342c420254142145410b090060081844204072160018104081c1400741040301a51000900803100000c02103c04141c0840402035400352290390030364410000041180800426098840c590341c6c0c1c0ca5400075913042c94094103407100903248009004050107450095134880c000c0042c61417054000003140701580c400500303035800d040803514152400c0182019450f800081400590b03100060082c101d0701145840340031007209801403585000048240710412a131605030500941c0c0c405030642c0c0c502e40340e81d0006040e000384a00c01e5480824540300b0008a0200c0c1c1c8070f180c001a02801c08158031914801c03941ca0000503c0c0c544812440010f80e501d805511a0651a004803003100d41812100c0703651070740107055101510088905048070007086c10302d4020401c6000034a0301c003c0d2a6100d8028440040040100700d9224902d180c400c0c0c40700f10b91041c007080880a8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 923104082 1250 923102832 923102863
    0xe120705030a0201080c0d06031a3709020d050705090c0a0c38070e0603131112161d0f0a0209220902010e0d1a131b0e0702 54
    0x141e0b26600111034400020704110070402081006002181c17050088501560140018420741e000b81c88000011020080c00301d010280750f032003056280705210703c404030003801081e10580c2508203d80c80c03800400c2d002d02d0080d84450034240402c00c120001c0340d1003007180c3c01111407d05a03030754596901402c0c0700747c1040c1000100d610040e400044c0300070031007842640c40c02d0805280d0340805104030400311040e194000181c0c51080c1004485a400081c000010005403121070850034507141c80d40c40e030741c848500101512030700c80900005441d0645402001a9540304480b60080c1184a007150132856003e44070312000c004038000d01d4030341c1d807254044c080c03540f0200d0142250307250b410300402508840c3e0a2540710308104610620000e0701501c1480d940c00e40280003407030071340d0b0748005809072001380055801035000b2201400172901c200741c3c41e01d009605030701245c0b031540c80002c01c0740034505000000f400356407110008184007419032407200135504600501119500d5603142a6070317840d1280341c0b1542 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 923105332 1250 923104082 923104093
    0x3161815081203040c03020303030406150f030201050d020f1335030904090c0b12060415060206040b07030f050405150c2b090c060f0318020604091e05070e12070503 72
    0xb0300000001154064010b01c0200382d001d4403030340001d003590720683d0f058403440d4903114144800901c0990070001080807030000c1071103034a16170010b0840e004452010040c1e9502140c1e000414061104856003400c1030015030f01c40715203820483e0900f0250740c1c4003041b1800d4410408081035512018100344504403c01941460520f10410001d030624110885d4803000c412400613102150001410f0407181218060300503140010070f00084580c0401c58040c0802e4802040101a80101d0750540181d0440000003142d40c6a090076000b4100d48a1300085182c540000c100504c131010424240c104450311140307540c0d4444120401c10f5016100300b280601a219034603400c03006281c0321621b075850700482d0100e200e1005445481d03600407554070202c080f94601c8000300d103030340c0d051049140041110714000045240d64002c209580624081c4e4031815581d01c0d85075210310039480b41c0d1001c3c170403510014042071400781c10080500313452201c55801640c806040e5461400003140708001c0d00d00103802040c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 923106582 1250 923105332 923105353
    0x5032e180b011202070203070305030d06060e060a1e0e0a0306020702011d031023130b07090e010512010e0105070e13110f0325020c18070c020f0316181508 68
    0x3c0254004202241c3c14801c5200020000e035003400034280400e00c090f0001091460400080c00385c1800f2500300748944400c01c01070120540084241ca03500c14005451b4008510380344080c0d5900c40c1201c0c1e0700d0b030b00c50000f071703030000800029400601201d80f003130ba5810203a510351403180e01840ca000e03025650582001c641007066408540c0301c03203c80013014109a040e030001200b004074440080e11a003540143c140c8402003403000714207885402485502e80441410b10303101c0850b001c07050600030a8882e981c140184a42190250440b801620044c40208858200b0703600c09442c21100e10082d900408215200d542804014400d02030302000c80c1090b546070000c1c142000a040d400108402d40f030ba4840c0c0e040c421081048070003004211030320b07001854407000300e808008140c0d1894031100300040301d80e420442c49550011074540c0d6903034180d40c1034080ca00341000180c1090005d060509024480020020b444840700d9980c1110352600001008208640c41407000801614010070110b03501a00010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 923107832 1250 923106582 923106617
    0x14072102030a1101021f020a17040b0103120c1202070f090e030f0a0306030c120203190f02150d1a0a05040501060504181e0203061e1005032e180b01 65
    0x4a240c1c3e5014410346042d030440c0c0341c4090b000e5604d242ca4511095020900c659425000710784550980c00c81c1d82e4244040c42c1c1559400b04100341400014100f00001034050003050080030f07881c83e02c55102e05400811040030f03100954620903485000d0520310009400a080009446580d010302c140c0c601461400c9680007015202c4d5000d0041d880402d5600c0000001059078108043c01410141c0300a21220900f4010985041140301d610219800422003030000030f03a558103880703e0158161500c44104d000701c4480302c0d050045801c1c0d04ca00c1400e190695400e039034140070100034080100c0d944100ad540ba0000c0c0b004542d024014071000c5034081000340040100e01d0f00d90310103200c45e09004900c030700e110a001500e10036282d0803009040d801100b0302071549824100c0f40010ba510b035602e100302c201c0c504001040da00c0c0510400f0203000d00040030607440802d00308a842c1c1801c408040c40607010101c54010415200f51003100c03407401c014500313140c0700041c030b005000c0460f905039540c01d440700040c1ca41 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 923109082 1250 923107832 923107853
    0x913051b0d2d05030c06070305060f090414032a010204080c13090204021c0f0e03160606050409080310140f0f010309020a0b1305060403050a1e14072102030a 69
    0x100c065401102880c20255480c10181160740b40c4164051500da149000c0700c0351415002030300500906091508002007611a44404540540200c800f80481d845505001020319001650419a8080000c0f11109420340b09596091103828800c0603000000090b000c078200d0046015040064100c0310961155140045001c4c5654403c160006485092580014101c2e403003001c03401440f40707868a03400000310700341c89907100a41c0150001c1c08000110b602240d220704c51a10b9010144060b00c401409206040d03010030040d10002d082041141110304219486410440c0ca8908103207000b0b802143d18014610081d40d1408040c1c8480d0087ca1140700700001c0c503070030540650400d9920088040541d5501c1c4903d00104114440d05c0e0395003020b591140d8650109800c081d015010800041001a00014048010070b420042d103044280c0928803c4110000f40b03007020f041d110346008690000310003c030703003002200d80c0e00301100842c0c00c04002c80c082c066030380c1030003a5140d005400d121000c00e00000c40c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 923110332 1250 923109082 923109113
    0xc0f0a090c120507020c0a090c0e09100801090f0b0c0a0c03051b1f0f110d02070816030503071806081f0807090b10020106051507110913051b0d 63
    0x700702442c103a440000b0022941c04540080c0180d10115030100e4905002e1944000b406c98a2814002440c6010000c3c140c0001a003246025140440008200850407035901e0050302c01c0500900c0212031030709101e5038501c0300502c01c1d62641d41d0b820104480c0765900c1c041311640400d9440f0000b03041e00903142a41c107a00041503056044018190501851030305222581c408800320312021803c1c2001c40000c8122801ca1141165040c40d006032140c241e010301e02512550b0038108000360340c0d0081440e000001d40251900703020055201c2c0c1e825020150030001540c41041140e03a25540c9100d101c612101c116014801d040115a8034404540032174604030803d00050402c2c6080c0c3c0803903640c0c0c0c4c1061700d00034982e44000c81803030b82d0b00e1328040359180800049185e50428402400214280b000223151056030443c0807400010000704801040010303c065044000000c0c585540d80c94010b030541e915009003c0201c0710341c000d140201418191510002c1c00c0060081e000911190700c2c0c0d80c41c403801d140c0901c0d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 923111582 1250 923110332 923110337
    0x2030103122708010e0736020f1603110a1709010306030b070905030f030a0801060f0905060304030903060f38091806090106120b1e1006020c0f0a090c 66
    0x46042c24000c07031110710340014580c1c500001140e0300c0e0311403c1820103e140d0400e5084640c117000f0140d0a191001c101c0035895807072100d1043e02043ca40e49030009108e507220040381d107007000c58250409000407100d00302d5503010b038a6a410030f012401071240c0f50741d0b200c400100301c03403464000601441d40300d101811074154107050004030280c49443d03800d0203040898030b20000540c021403d22960038140220150483d0b144001d50820010020141c03500c0414001e010801155250350000c1034030921111004040142019a6a0916040c01850f03011035001c260380c40c6040401001316028075200301c0c0a224080d0400504000c4c00f41585030304814000800c02e020082030440c69a15903504d4420781c0034100c0d051070b148168205485444c1400c4000744111080e900d0240c0401400800301c81401c0e030180e10041d00704051760b80c40740c0c0016400c02501c00748a6440444204910790000954650507a011a022101c000c660b402c10081d1001c0280c18007a040f01034a9000c03c110301da2034000c0c5120340c100d030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 923112832 1250 923111582 923111627
    0x30303022208030301050315010f030b040f0606080304170a0302071e0306050c0c0105060108010608040f03030e030a0201090c082103090109120504030210050403030f0e15070f11040203010312 84
    0x1000010a80141d0b4006141c1c6402c004010001c51408100b40d01c4184090365101926605d4807030a9003030358846210242c0140c503001c0003c3d0030481003130440c6081940c492810000103845600143e031f00e4006000744007a44c0b01d040035160100b080013403486016039041d4000d000c0507040c40e00c880d00e0400445011a000411642c0204c00609140101441019880c0003140c5030540c1d11201825a00b01428050621a41e40014000148e00104580c0c3c03194001401c2c1425240740d1504500401a141c03d0000501000c5051003242d581900003c440b180268400d141d215215140306458600c03c0c407001400806c200c440300ca0b01107401c800786611035004000007801c00415100c1c042c2a00340e00240b100010000a410300452a103040ca03c49004543d00c0c02d20706242c01c540d4040c00301020107906600b0b10035660700542050341d0340d04403c8110080c10321120f85990040c0f511400342400103a04541e002d1032880140c10701c1c01e091083c0d0341229000b01d0301c41c1710102451415151845031304000868560507 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 923114082 1250 923112832 923112877
    0x3030605060f070219050117091603030215090705240c0123010609032d150e010b0303210c070b100501080a0b01050405040e150a060612090b0103030302 67
    0x40c070700039001c00b9050400169589569104001c0410b40c2d24000700e50b021900e20301070000f40d034403940000103162035000c0301456444084038140760050441041c6d0341014408400710400da40421b2100e030110b034020141599895202807103032510311034061030760001c41c090040d029168030f004040d40c03a9401c0321081460b040c8590000c0d400c2d2031840d01883c040d295400742d00340c04038140b18003190045c101e9150400b03d0b1811960392511030194002e02c2090450f070764414000c00d80c0302050b02215a50310400c0a96980702540c0d208010305451030440100c0d51034404801000e06000c800c462050504e040821004035012110310100c00015220301000c0005008120019503a13910740750107645200344c1d5902903480c0c140010881c01c0c00034050702405041008100301a42c104040e1020b41b0000c40d00461203101c41da5101e490291030f44c400502e524011317000e000c851542944048191022599841e0b0324161200c0d40700300b80c4800d03d400402e030841032001040032034400c0d4050202880d01441c2101115007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 923115332 1250 923114082 923114089
    0x8040305030d050612010b060d09050c040e010c09081209090717040302070f060e0d02040e0a020d0f050f07080d0806010903152c1b0102010e0304061115090c0d03030605 74
    0x1c400380010704950f8a5007032084620300901081d08410080000340950f85184000c2111802000d00040c42a502d442c501c1d0b04000c02030000b0405094017500401442035004d0126000c0e103c45030804000c1401c032500442c0c1480701194400040ea020318400d03103040065400d10450a10062104d020400c11481301d6410204a481c2103000d24040c1e40100100c4d410614030070b00c09845540310009001404400040a0300da10f40c14140381a0101c40008680840c1402603007040705061009501103201038803507042002072240d0301900c80c000d000b10f030880140100142e03030302c12940c011505e10742d1103010841c0c809482524010b90210044c035100c1d00542d5640d9519258180d4101141d06041d121303480742044c030b19131910105070004030b821051008160307092078548400c00548191364010961000d00d01e140d001b5001440a0b140d913004482d642c640c0c500c001042c1506d20240c025007806040c4455840d4103c0900d003034013400310344020341640c4103044100082c2da41c540c00c0072002d040c1ca851000400b0354 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 923116582 1250 923115332 923115337
    0xb072a060c0b0703470f010f0509030709050f0106080c0d150b0c060711010b060909060d0807080a03050601140301120f050102220909030e13111605010e01060806070c0804030503 78
    0x100300100c0d02c41802c1c0107019904003095407409442e8151000f55410217aa6a507040c0c1000c9060700307080c500058020000100d03041e100701010b17180c0501c541400055826007a80c0914070070307011807a00b40d255980314841144c1c0d0060545038000c44500602041158504035489a10502a420000036031143e03255000d12058110711040b0000b60008002c00880036001010500d07054051300c000c1201c001e108000540500a05070854010810400095100c0d00c80c0b140e150302c9990000700264440c0b0300c91404902503801032640200203070508000c208554064400020500d030074460407801d583c00c01141c101151800c02c81594072078440e00400021400c284004c0c44c5c0303904800421152602c03208101d580c1c5515541c40700c25424907000300040801d9101c20340900d19642100c09900400c40b01aa0002810340041010740354480050110641d03800c02c485a203969110340024444401d0030203180e42250f58078482c41c405504080000340c2a5031044c103101e1985440380003600d041a4aa48604d85541c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 923117832 1250 923116582 923116631
    0xa050f2203030e03060609060310090302030c012c0a02010c1104180b010501030b0d200111070801060509060613091d06090703021c0503040b0904060b072a060c0b0703 73
    0x643c000310300d200c0c03800c0c02c0c880ba80c0d0060054038100c0060410310086540c40340f5458555a5890b503a4281d041014400d01c01c4a0244003c64001d00c11910044001d4190140903000543d840688071021101581d02280010030f554058441c00c1c0f142c0400e4582d41c0f401740c000415175602c696285103140488400c0c210601c1000d00031012a06e0a60401c03001400300c418402606200d480038a5030f8000150007540c8810304c1d0784c100c44120402014540050b01c90000c80e20f0380c1d0342c07280140e80c0c000c251030740d0540c0814129082150510126214070042c0803851040c04980c5403031203141d04041c020480c50382c0100003401801d442d083e41c4c20309000415800e12a003590884c2041d00064010825464044a400d00b0b90307482e0701d07040118400954906507284920310507402018004541082035541315403010f40100b2030f210506644075102d160904200b0480d503000802000c000c24085036841001d001e15090780d0190321100d100c0e0049885803800400000e0804c010907071580500208980028178161aa = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 923119082 1250 923117832 923117837
    0x905040212061c050a150e03160c0501212d060e0f0c0412050a0605090105241c06090c0303050c010f050709060f02011b1d060a050f220303 61
    0x40703040c040300704994070f40b2030008a01c01480d00001500850b4001c107444410301c0c2d000a007003c0d114040c102040140022004450780e500001c1807142c48062607207180150144901218210180c4071001074451030041902c1d060010b41000341c800580015602c000303022540c040b06050203a0807030b40c00d02080ca00a8130100e14003911a40f0801081c3c5041456540001c54840c502503d40b41c9981000300a000d54421240312140740e81510301400070070302c020780e00745070480b1051004c0e00e040c07000c0e1406400d094441c0250000c81c1122012181c0d40c42030100200c000080006031500e5507035568102e01051100c098070861340e60500000014101d96090b4010b51298540c0c9899408000b501803c43d6200b0312070b42e031014100410011910703400103103441651443c0c20300a0304150181d400700d00500c0a40315181e800b42103070a020200c80e070881d04070031041c0000702d0207805829071035045c4001c40c0282d80c0450045181404a1146241040c028251100c3c001e009550108841042800c0c08056070b40258003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 923120332 1250 923119082 923119117
    0xf0c2d05061e0c030c070b040c05010e090c04180204050303040303020a1e050a060c030f052526090a08030a0b0f09063105150a06090e061009050402 65
    0x3008418001c1a5004141c002a508004014440710300070880040924480800020015002a4481d07080e100c0c20364102c2e10345c0e506480c2c5441c1020003800b00703024480c04201c1000280ba1603241900c07001d4480d5010040e094180b500e010003040c90390002d900b80c0c00c0c04a40034000454a034600b040a8002980264000c1044070f000e418001c452034005c0302d1101d01e090514440d040464800140541c210342c0c8100001100510076204038010080c800c81c842806051030140090203000100540e6845096090429041403044055034041c0d00c51802450441d01c0d13184207038051104000c880e0b4071031021000c1d105801d403980d031858241d0f03104896807100142e4441000c0c1ca24203008800c1e00f10314106071030240c41402e103034001070802303100c0c178841c8a40b006151301c1c5001012940001c40004182c892030601c00742c10240d00ca90324811901d108140507046040300000d1044c4642d400e0740c202c0d8580010a02aa100c060505c450121174a0303804084c0040301400068a458074030040480b282c00000020 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 923121582 1250 923120332 923120423
    0x2315060a03051c030605030f1b01030207061508010509011811061303080307022e0c030209100801050916090608060402191e110709050915090a11040c0f0c 68
    0x1405c480c055000703280039500c07d00f6080024840024503484881d03650b4101142013545000490103403207600c0000f0507907400e280b0720144044680d50ba200c2074594130002400740f47d41d207038080b80c200e43e0701c1f4621039101c03a4044801e00126080c541704808145002d0016840c210300500340f4401d0b0407042e4001c40340c801c400020440c00c142d05010007440c51607640c1122a4401c1024680101b041c0c018840d8040f09580390b01550589000358110348450b01c0141251004001101015001e41d42c01d201d11801a013102000803c140250640c15240c03040c55120a9103603410024100c2d07404000a01e010b070004d81c2008403507641c0758030108400e00d04414ad030750b03507664880d52540c040c0e11f07003011344e007040074444110055107412801040800c180c07115500000740f11354032150960300d49030100c4e1000b6500603003801809866000031500c201043e00424421103800d031010244400c4407034011014002405540d1030012003441400f140400c0c60103240c900a60001715003452078100c4070011071804920031694140d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 923122832 1250 923121582 923121587
    0xf1c05061014060a18091d010b0906090c0304030c02030604210f021002070c050603090109141507080a140f1f0509040204150e040305072315060a03051c 67
    0x94098607003000c03070550000a0320301043d02d501400d52010b0501c0018010303032040d003240300d401c0c42c01007102d0300d801e000c40c001c0d504100d804114000410a1b041d403d00070009114240391030518000c000280c82443c3d035660b044401200ba03040508200d003044980e46806016036030411030383c0e02550185c2e0500201032101ca12014030703104181c14640038020443d540d0a002900490141e84c580303032118016a030f8440c40d203040300c0c1550755a00115030090012050202c4020b05610811416111341002d07111124003c1c007407690b500c3c040700d07800c00426031900000c03c848d00c260301d901d0300510001008180500f040b018a5001041212030260191444003049002e484c0070380441441181131034159034246c10007002c80e84050005201034080c41d1070b001d100c0310340c0701c02d00e401c5002084c5d2070419403540c2c1803602d0020482e900c451001c1c1ca240c3c1e4083c00d84d4040118141c40190b088482e2001803c800610203120402c0150060100d9806480c1c0080000440c105010f00421900503882c4d440c2e403144d00300c002 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 923124082 1250 923122832 923122861
    0xb0109022502090106080c07020a0b0c0d090b03040210030e0105160806010903020307050603281a2706040609020d050f0703050402220609020a02010f0b1c020f1c0506 73
    0x1c0140c400801c410158036110165415070f20303d0310342044a6943c00084100a00c140d00000750003040c03508000440c0c0c0050070203440e001707107020251880e074201007804651b41d5905015901c0418405c0001c1001482c1c01032021410388514107020500c072500d40d20050840c0c4d0f00703c810301c4003203003426641d60301e10f5030142c0299030080d030900303140c44854199004030f03580c0c0f440e034010a07014200010124064100340803030607084041d5a40c40318420700c1001641c10151a81070250381c0c1e00c000000b0b09620b03501d000e24040c1c0d5103044071050881c1c0c0d1240c446000140050103031030203030055030341d0300c0105d5650710300e000a103a810301c0301c07002141c242080032000e25040c1c0011300400400d03241c141404010b13a520f48080445020407082e00380c14400c103140f1200104940e03130011310040d00c0000d004d8003494040d000b801031307030204400c2000105d0158007031200c011100302c0981d14038010541070703000500c0c180103000d62850010f018107000030440c0300001c0140303000070350036100340e07002d402000302d4041e240e1030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 923125332 1250 923124082 923124127
    0x60e03100e10091a06011e2006130311010218061e03150a0e07090302091008150403020607090e060402070615030c03200906040b2418030105010b04050f0105070b010902 74
    0x82800220126440741d00034070300a01e100000708a240406100d0300780c5980c02452326a401a4280e440c541801d4480c03030300d0b00d51202e40c00c030081074003690100c0c00c4040610a80303030300a0200103080c00740301041c0b007044040d03803201400344c980d1200d0360f0000c1d80d04803800300954031890503240048040c82d20302003084881c400d00d40c010f03040314203440c1c200200030341c0c008508400c60f84c0c140c40740c542e5511102003440380d284498000e0700780ea218203103c4484400402e5a032038010350198080d1503064450b003104846000041c0202d1040c2d80350301c4007180f45424554010301c0383c540104c2c0000707060996000703010070f03d01e0581d0050314043c440c0101807044c003041444042040841190980305141039030081030303c6100041012384110f6840324030b2642600c0c0c070350701c3c43c00e58100c18150400a20154060030303025045000900d034540644c1020008074241486140d06984400216600342440d10341001200d002d0b98000030704102c2e05100810020f1035414203039000c5e10089002507141c801007651a07490b01860030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 923126582 1250 923125332 923125337
    0xc0510021009060c030f180f1713091107170c010e0111030108070e070e0f0409050f0a030e0a0302150a1419081b12070e1201020c07060e03100e10091a0601 68
    0x1f0402c0d002c40c0c09110180581d603004000340200c400904000204a00500d540c08101b000054040a108507510311002515107035034041003070740c100522814140c010110010041841c2c0c0070740c2c540740070641c0080c1009408010011559000b190260341c00c1d9000341001500c6000040014006250140814000341c902c800c1009040e00d058000203200480d520442401003244ca42454034a4440c5d810846e07511f03410504446c0c80c1c91030445150390724142c0410942c0094210303c014507140ca080500072085a03001040d05003a030300701552587c0a940320070000c4d01400020b030494180c0e002c4c028044c0c14840c1d04407001c589281c5008030040c1c01035500500c041c0c0ea1640310b030b04201c5403080d020140d50100c02e00705126109541c80b00410b40b902c0e41680d5006a11030051318076000c2c892815001060740d03c04060948a1495444100b40e5010b403034050402c0e816040345108900e8183c13154800c1c0e4120060100f11041a04889081d50440b1410380046c1c40c151000c1c114440990740b00840b6942140003031 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 923127832 1250 923126582 923126591
    0xb0609240403470618040b040201110303070207180204050d03050c0f03041203030b010c152408190507030213020d0c09081e070f0801020c070b03040c0510021009060c030f 75
    0x1905441c1c40d070b5051440402c120045004106107496006951620550f1020012506d040c1800c2280301182c04030340890020754a4038121410441c00300940c0d000d1505134004114107804c1c203c002440303000ba1055620500c1e070074000054036a807451442084070780247c8a00d561107602000c110b0400003064074400300b40e4020401000016510351804c034009406240000c5c5104331000121a60100362102801d000310003a03030301ca09a0126032042c035203210342c000300d800c10345c840da205000440b0315403040c0790003034000203509a9141e406500105885220304103580d42981c603540010044d0300151101e641087e40032a0303404507480c40c0e1140690344111810300c0da003024540750304165540a841914990300c0909041d00d02403a5082100e04003500b010210800c1c62134484280c03034001c1d000b0140720155441514000150b148510301101d0249800c180c00c1c08103541407409000c1074038101e040d0203046120b1200000d150521910039291000c0c440e0a001c9100c141428005042d42c0b031046941a0301d9140 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 923129082 1250 923127832 923127923
    0x20d4d0303060f10111e070504050f0403081b12041a0402030a02060c070b030c0a02071215050c0405041a0f0f0a030b130507080303010303120b0609240403 68
    0x4000c2d407241185400ca0320078013990020b00046aa842ca81c1c068006984600c2c00e08100b00900d28407001c40d10112141260a205d580e502004107403501a40c15890b0801c1d0580850040f9215070042da0327101c03c050056074280016400107840c43d0340400c07003020400545d042404100b194001d05044040c100300101e1042d41055000291500040709000348141c0c0001000c22110105101041c0180b501d54131643d01c030b245c00500c040d007940c49650710500501510030003180b42c2040c800101c010382d41000d01e0483c0c01d480315260b0802808080c1c400c4141c480140000a00c66481c1c1c050280107060241c550900d07448450140a1144e14034071003984030f00010b1010500700d441e0100640112078003d161111140c541c04004420f1400c1c5440c00ba006014030000422030b0b9070300100841c1200d01c250354800070200c44209040403a095100410751200c0d04100d03d034014131701082c00c40d0041c03607403680500c1620940c00440b451075010764403c4982c08051403040701014117242d01a042044d0b64414042c40240 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 923130332 1250 923129082 923129089
    0x60d1b03050601091b0e010f1101061403010e0303070203070609020411030a02071109010506090603180a050303010f0608040f020d06110c071a0702010c030c08040e071706040c020d4d030306 83
    0x220100c6c40d0400010010070780c0e101c3c0c482d00c0e102a80c040785000030413895450f2002003440c1640c20b4606e40c0a5070800460040b0484004112849989194007460400b0416514580645040f502c1039900580350304400c440044120021400b8107251180180d540c003a40c90300d4000103124440e030500c00c01c04000100120780701d4008494440d00104d912651b030365648c1401382e00404070b5060b2130b0301c54819050428108400000218103807154684500308156560700e080320005401c540007404007400c924040014100044080b038054801d82e00801c3c0e044114074408415004203003003940310f5115040030402c0c0040c090f80d04105a848050344c614119a540019128003000b000003410810725188503018000300b00280c0e07025040301d4032000340e03504010800030036207082c40ca00ea000c00080080840e245240c5441480c0c0c0200c4250090000712031104003e4031603034100a00e00d20080700600b03c10040c0c0d0503580c3c0700b1140c5401c0441445040c2030803016641e4081187c10140d9060b441001804460350303 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 923131582 1250 923130332 923130347
    0x10f060e100906110f070306240f1703121006230f07150c030204030b0c070302060106051b10020c061807050f011e080f1608060d1b03050601091b 64
    0x4500b030030300050000e6501350035031038016440c0d0000d05a016085000c02000314503040240c12000004560380c90003015000c121a40c1694400c0607501c0b02c81850411416120700301c20100c120741201a40d085c907501c5190314000e014111159031258003801c1d400c3c0701040c1c103c1d03c88641404402c01a100ca0703544102002494465407402400400011a00e6410000c20401c0400300c005a817506004c4c60540502c054040e40050008543ca0400900040d644105a03010742c0c00080d0954018007042e40b0b810801c0c1c07520350182085910485012502615005041040301902c04003e040160385a01d2200440c0c180340c00a008844090310b0f60400b030384160b00001d8950706407901201c424a14864410050303d80000490524060f00380c0c550400060039000070038548200c5850303503100c0e429079810f8130820a00b2904081c2c01c0100c0c031a031000c00c842d401c10310503080b0198403408400c500705090354500c0308422155801206c2690055005020640c80d60107030310000c02d01a540007096200c01c42d4080c00c042d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 923132832 1250 923131582 923131589
    0x23030613141f09020c190c03051509010f1e090303061a18030c100809010b0d0f050c010806011205151504080d02070b090118170106090e0a0b0609090f0105010f060e1009 74
    0x144100c0001c410707c840401c81100655000c170849400c112455250000c0c1c8004842103040c95280009000080103907000d401c1000300d181c1007512070b0540401d0720f074008164040042d01016980d040115040d4403090302c2904104500c40c2d0280c642d811a140b1254a0700e000190318081c1e0040c0400c0c0ad040d0b2141580e644c04000c3d9403c0c20308460b550300c40d403640148100c0040710f41c003035591f507910001e01821031a1540901c0c041d905035521790750448010b442003541624040c1c00980224040c0c001c140311039203c06c0d00114a810040e40304c0c0c014200144108200c601000402000003608000c0c4000412280c008181c071030000e03101e0700d450160340e420f8500840700003a06100080941c0501e01c0d94140d6a04090604408556a0400381e0341e44180201074034000c01004524000e4049400e0034001110401c2c0c03540508540442d584042c203214403050042c01c4030403a40300d48070b0035891504003030040398081c0055003107107041c261070940014a40c80c4441d0200740520300c01045495061303840480300003138 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 923134082 1250 923132832 923132863
    0xf0806010512150408120a05010b0f0d0e0d0e01021e10051314071509080721050102120415050f07080c0702130603020123030613141f09020c 62
    0x103106000038000d0400110030310000800881c1e0b0200030401540302d0140c0311b520004008240d0325075503112850200c83c0d081c06400d600007400d0100c00c1e80d5400e000c0050032070401c0000f000c40c01e50603c44a00c0d2030800141c0000c00402c548024242c1c1c0c550b41000100500b0703046da81c41d011113143e407804168a481c2c40e1119124226110b4002035102c40424a4002a00c1d0b4000da80000040180c0c1c12561240c03607074007400110a03480c020784c4100c00e2141144038107a905003c084c3c06a0780c5009641070700c010b000c0074000508080310045a003c10806e2000e8140f4000000b000c40c820316103480c2102c1d03515036034040083d15502d0403040c441c0c2d900411001d00ea0151990030000d009440f01e004003601d50051305c8000750301c43e4495020041441e010307044101224404e80f0740d1003c460425072171405004c001201111441818030029001345809030042000c80003049000030158490140c04106003002c07182400c188201401d0014055009001040240f8440d40c1c02c5041100380c11000e5140d0000c0822030f1203 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 923135332 1250 923134082 923134099
    0x90a03062d27110d03110609070f05032a0a0b0c1f050f0f041e031101050a1b050d0902060406030c020c120c010e03100203072c09010519030215070c0f08060105 70
    0x1014016070600d40701685000487d5040d01d08410203642d504040c0c0030301c8407060f03d404000146810b00080e4410165030215a48450010141c00f041100088000c610f41c001d0215200085e20b402c1c91000709107020703510014002c2c88126001c200c1c0c0c40c154031154000c3d030700e190208200900704420505500b049080c1180c0c007042e1554201503281400090003000b000f045d0304212000c15811800d40302c14992110000e200c0c1d5038861400070211002200c0d00201c0c0c100d140d58040055102d80d000703122100505200003034440c850b4000c1030650300180c000c1d1000c66034501040e00c1564042080241d0704c04e0444460001c1c80d60460501d45800300184e081d4180001c0c20141c4495950a2105599910011000310340740e14095400905450340c11080002c8015000c4440b0000500822160013595019020452507480d05040c040400c01503071520300401003aa17004001603a45600b0018180d500f4944241c0700e111a04100c1400c0035580d22001208171440e50401c418600455030604540c01101c0219 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 923136582 1250 923135332 923135359
    0xb0706050919021e0310020408010506031c11010e10022502061e0f0c07180203010f1a0c0d0f2a170c0d0801030b0c090a03062d2711 58
    0x1300040d0300d0a10350381c1406041410106601554040d0040b036040e00028009034892009040c0c98911480310013541c240101811021140035503100d40055190740c00008400882c00d410a09043c8800102046035400040410031001a564085a05c00142111640c0700d466507001464910620200c940c2c0e142060140c0403034062000f06990304000340c0141565190030414105131540f038103004103000018400c20000001c010380c07003500d0580728004c0303202140c01e040c080844403604201903005541013003086910502403080c04400051007840d00c403500310340f1666001a0040e05580310542207400d1039900c0b55040c0040340c6020602c3c940007801311a0328050301102500c1031280110410381031103580d544820aa40c4441003904036409640701007010785a500184007140308046446910203241801031000ca08981c0c4040c203400d80e21071074000051000c1d22240e212501411880401941e2610900d10451440e00107080003115111003a1013030030160f80c0d01c1c90b00301480d110140551003107a80f69 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 923137832 1250 923136582 923136619
    0x10e01020a0323031009140c180a0306020a0207080712021c020406031e0302010f090201172802040801060906030503030718120b040c240c1505010b070605091902 71
    0x20b82c004400320b00e0283c2d05c1c940464041010201d0340b140030949860b140c1c00e08400c0c1314400c07189014140d02d900c4149007030f00011f0850500b8510890495211000c1c04000002030402c0c130041485c1c00103034010304042c600d0003001b075007440400c2d4040340351400b103402c00d030005994101c070040040307d48040d407020000d00c6002007030003071006402c001c0c04034107101c0b28039031091007805103548801c0c07099000303000160f4007901a03c19680f030064000c0c0841c40c2c0000a4040011600d0040d600090026021400070f5269402c0c0200814000c540c8854645c005424400011300703000717100107040910030a0201c18510ba44042d66840010003210030406800d98100460a50440740740042c64202000c01c2c0c40885420103900c4060140e84c04c9035103011f4910001044201e00f400480ca403802d003044004c070702103060b10603901994400400c03030300b071155101d03010189011442004c0c06001a00c2c2002d440b0555441c104089401c003074814441540900c013004413040300035002c0188030b58192040018054411683d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 923139082 1250 923137832 923137877
    0x30f030a021b030705070506280c150915050705041e050604060e040506030d0f0c02030c0d03021c090b04051e041d0c1f050c120a03020711010e01020a03 67
    0x1074202800b056100c1d089918800005448014054000e60704000e5503401005803921681456458000ca16150707a80714080301c3c44004400002da0502000c03118050750390000342c3c15a003000039030310340e510840c041c280100c8040c04240813420b00800c110909140d44090040d009501c50200e802c0c4000041003ea034a880009000501d00a44040d03190f64030f58002038417011204010070701541c0741500003020352070000740e030040c0c5080940341c0110422440c4000c0b0f407007040034a016030300761145155444c0d1548071a124105d07041e010f580034000c10400a0b0f11403d0800302103c4030810041041c03418044c110820b070841e400c650b81243c0301c0c2d04816403e810711001c19200da200551061914038905040b80d00e03021408001c42c400415150544550020001c6c1e240080c11403042c80003d426600d44128042c20080c607045003540c04544040071046601c01c41c950054480e080002e4000c610203081100c0d0407410803807010242440201c035045240000d50302d2220702009802c01544072a00440c400e41d0888 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 923140332 1250 923139082 923139097
    0x1119080105040b071202180103020912030316021507090e061201020c1b1e0f18040503091e01020a0b070e060d090c05010e06070b1e07080a0617030f030a02 68
    0x1d010078541414400da00c000101c500f000072440e804400811030489108640013801040c1042c1c420000b070350f004400a4014443c074076002402c84240b03440c5003e04002541c4946518025190309941a4000a013440304c040e1040900001d9070042c811500d0300000c5480580b5605011201680d444600113100c01f061034032002519480007910300402c1d28003080c2d42c400c5070039609100600804203014032600982c0c4201503180c505125140600d589000c034080c0d5441503008010b44054084c411584514040079602140c15910016400501d81412410f1160f085101c0500100c00c40881d00080d494950310100140352140420008001c94002c00362908091000b0b0401a02d607032400f90114010a280c40c000d036601001c2c1d2000164542c8601c07020103031004050149802c1c21030f2513a5401c120400507018004a50f8840401d08a4600c0c0d0a040e070302c00c0e040c650321200b650501c0320302a400c880d5560401d6264541461000b0440e1100004507440c80341c0840c1c60b00e60f2a912010b5050090042c0310 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 923141582 1250 923140332 923140349
    0x3190c0c0603050603070501080108120708041505031b0403020603010626011403070f15050a02071802070b1806190e0303010308070c0f03170c010b04050108030c0c0303071119 77
    0x5202294156240e8003c0e0300c1004290101c50089886200556000c6800d100780c40c455801210203484455640b0b028006141c82403022508003610740d421902c0500c460040807000800200400000c0c0c50008180512201c007901068036150440c2c01054642c80140152400d0007108100c00c014980d0720540002c6a1090030f14140c0b5658407007a45100f1403114005281c030a100d00080841e02b0a01004c5c014100d80428407840f05c00c04020780b00380d51503040848003006501030101d0000d083c1d14507115500100c0b001c00070051303a600043c64070b490689009441e10f201121900640442942c0000c0c545800c1a8254180c921803d80b086040015150002c2600098000400004100070b80100a00320407482030301030b249001d480700068051010944405071002c54440220211188104c0045c01c801207810001b08242d00a040840c044e260282d0100507244d200040001000f0414400045035800c00c801862031b0140c1070b100e8602c907540c180c1d0382c1031003114041894000c2c26400480ca800401c04003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 923142832 1250 923141582 923141603
    0x20c1305100b0a0503221a18072402030d0501080601091b0c150b13050702010b091e07050d1a01020c030102130b03072c030d05030c031b0d141506090303190c 69
    0x2940200ca19034240c0d00a0401000c0c0c140c20a1041703804104540ad032452000c8098070a00700712802010841880381010941c0401c1007030704150103e5000c2c950203410703171200074200c1754035042c200011505500c01c07000d09920740c05484901942d20001c4107004a03080729100085003140541c02008001d150800d41c0d0040e810b03070b01c1001c0c000554100c41d116600315002004908920000d200c014442210f02685116028407103d108070066040180c000015140245c03c04042c00b0001044030b52011000004800103142201903607410040316010600980095040c5001c01001c491850682d000e031010305e00e4040002502903100b885004e48600030000c1c90628040c1b840214010b03030010700d85070b501074095030034609002802281128002c54010540b0303440d5030707a111918800c0007003100010908110400005071058030b24000c02d54091003500303007206142440b020104801c120341c0b9400340142000d00c502c0e07007250b5010040e10086100c0d4001d00d44003000b0301104803490b80c500039004040b01e100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 923144082 1250 923142832 923142863
    0x4112715040e1f2309010609180204051b0a1214071d04090210180302150a091202030d08041502031305010b0f1e01020c1305100b0a050322 61
    0x155043d910303c402c403d152800e1603103424442614203407403590498451180714102d24410482c4010b9108844000000f0003030788904250007519100c0001880600071854a0020b41c0750920400d03812541b040c1c0d07c0141e400003054255698003801ca480c605000000880b2070201034a90410750700d852400d400348005140c840f0000d00310800d130b03040d2a0106200ba61204503d8145032045d015030381d0700280310704840341000c20300f100c04106400a0607034003085940c0c00801a21100703080062152003040c0552500b100c03010003418080c0507070050070a21001c2050034003684003c00c9110030f81c0b07803134504907a448d920b90a04c0444076190344041c0c14124030020030007880035240004041d00e144180000c0c45003403944800c0201c02070003a100340c1d602c03040503081035174070b0a03404800e01030108040c01503482c2c0d00e01d0031000480c40565414072220340343d241d02c01c2115a1103002c0c6650040d2540f40481801c10031801402003440c04010000d1514001081d9810003030264603030901b0481c0d500001c5441240309 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 923145332 1250 923144082 923144111
    0x90f070c080f0415140c0604060e0f0109032105190c020f030a0302090a0501030903080127020705070e10030c03111519020115032f180411271504 64
    0x84d0b0a030041c001803d058540c0403408010088440c0c0c008400d00810b81c90326980c5801d0010b2441c1084510fa13072042c19108441c1700b0080c0500d040c041c4c00303604c4204000d000b014688050030000c0322881d14051820040007800c10004a09080221403403d000075020a182401e070301d450640c1d290f0750b17840c0c40041011280154180c00801030340c0c1c420782d038900c40d9507603840041d01512100b2000401003103411005000c1076101200e070301c40300203aa882ca119841d031030040345401c9a02c01c43c800e6801e90081c8001f8412130b0800b0201c40c1c0c00c6078035a61141c1c1c201d8503548030444000510301004100c100d116105104d641d44040706041001d48206005956033100e0300c040350076020030142c0d0400355081c81c45400721403620144440840750482481280800d103100c0103606130361013681403411000d411040f07012684940946607000010706803800000d0902c0e040c404240101e810001d40b00b80104903072101d4000d402110b100440010004441641d19800702d81214111080d880c150402e2030710003031402021 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 923146582 1250 923145332 923145359
    0x10e04030f030b031015050a0f030605010b0405060a0c02030c1503040302011b020c06160f0f03021005160e030a2001080a0e0a1b050a0b0306040b090f070c080f04 71
    0x14030a854100c0341000009064054541c022031031507050b001a50031652840721900030700c03050031202001644640d1101c0c0080c40301000c607045410740d011021010b10404c1000e2084601403c0c642640604191a2034001203c41c4206810141040301040160b421510104400245010020003641c0c10701e051000d402107a400803181500198200400400342c8109a5025803454403940d01034030480c1d2654050014541c84020f00030b030280100c0c00b0580104160656101c403c80c4100000354030082d240c10020b26140c0d0900361495210b1818050040507a2040f00706115011141020900c05605100080c10020780310030241071100d040a0038402c0075403d00861006d104262920881522013201c10403c0f51105000c454655009540e0303500800c210000d440c0420983c0c21180441c2c2d0348820200f0380d004031652100180342004410300c01c8519050041300c0b1818400e0700d014805280034500c00c010000701400303640074046c01850900c148a590001c60394290061880703596502d030740c0c1c404240c682 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 923147832 1250 923146582 923146591
    0x307230904030309050c150307030903110d0203121b0d0f0b1f090f0305070303050c0a0615060e09060f100318050f1207080f0a050408010c020a020f2706030312010e 72
    0x5001b0914041a1482c140d110300d541280440840e41c00c42da83d0803001d400500b034005040e01801080414610a03450401096240c0304095015507115203030a03407002c01d03030200542205848898030703000d8800f40e2014030681d008504904e00100d14190340c042c60b00001c007102c013800340e007041460841000030108680880707001c0040d80d488a413180d07a902050140c4400c030f4040104140c00401003080824818005080e441c5034131803c0d01c180f00c26641d610011200040c440345c002a410403010005250040c07062000700406551300e880b04c3c6000c0300002e010720340c96880544906401103100800602c00e0f40071140f9540800f501a00c003004605009596060b41d1102c1c4543c0d10400c15403000c0000711a0503580c140d64440d20407820050705080091503900704010603020040d040c0070020b0302e002c09010b014000c0c0f89503001390072a00303e240144069048060030084c000c551361440e0b212910248194240344040a2032540c04641b140e10001e4250300c5240040b1810f0b010000003c41c415541d982500e010f07 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 923149082 1250 923147832 923147843
    0x3190e0d0609020909030901140c1207050106150f0c020103050705041d063105130c090b0901090204080d0c14070b0a021504020a0332010b01090506090307230904030309 74
    0x50b59548131000b0b645c7e110b02ca400c00d0004a544068a0481c00d51602411845070184103448401c03103444131000c0d141d00a1302c0c0c00d0b5101c1e9180c0d5010401441000b01040c4038034490302e00030340c03007461000f809070521903643d40007030400d0b0703031640000c0c00c0601c1001a2000360220038101d02c3c0c0786a500c180040c19007002d44019100d00825404203040c41c418046100400c81d030000e400d86d12280c2d454a510082c44000c011040c42420001c0c1840007a41e4126200c004d01607440000a020110b44203224192005820020f18180f0400c020300020070f0024a04114072800d01d030000c4200302d14502200c2e420904402204d407481540c46c041031940781100500083d24442e401c070740c050100e4506030a0140d200380c40194001c400b400d010320115400d0030f017041c40d050b21a203829074001d000004803203920044081040150759101e900c00b8603580c2c00900c9100420044842505102b4010f00103900ea02d10f40c8100c41a24084101c01d0b040040c400604040c2c40500800d4541c1a2a040c01d016018041d0380303004944 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 923150332 1250 923149082 923149099
    0x3080108070509010b0d111c0c020c131e0c090312031503060b040213031b05030a0c090518070801051e040b0106030f0605030a211103190e0d060902 65
    0x20044000541182250801000c070aa240d10300100b17003589900110501c4c600c151039100e000c01100060703001b07108440841c0892440c080c08038000c00100c41c03c00c040c800031904015810f43e41a664090300b4034082c0100c80002442401000c03e403c0740c2600404030301061800c0460384d052468200300c105044074061080303080280c0c4180f41c2142120020070554071071f906039134030901c041041a4030220000d46d01800051401041d11500d0713140c141035510840d61011884808420004004500d070024882500200400303c11030f540c20f104c04072035000d0030344003079074540c00168003084800100301402c0d88201690811501c40d071009018013000ca4610000c22070015081d141d82c031400020501c1541c0000220304243d00b0200b0880c05403a00c0c0c0c0c0c03060b061a0322900d012815950502c60361424074890f503aa18015a030480041051051405042e01030000258a01c1c40c5004044110f525a01c4140805c03a5400440e40702a120303e0054003143e0b030003c01e0707940d02c2d004001441d0301001d1541d00880d40c191 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 923151582 1250 923150332 923150339
    0xc060f020322050612070306050f06090409081e0406080105100e04110409060902030a0f020703140c10020c03030a0b100e010e1f120513080304030f02010e060a020403030801 76
    0x210016040108040164400c2140d151845204040c1c08050510642c40d50340c0241c0c0d941c001001d03030300050f050349101845135050043e1a50148100801404281c510792642c40350000080c001d8002d404405002d0368941188100b0002c0030b00c22030303c00e0b400c2a082103501640038049030083e03800038050381c0040b03141440049100c0c0741282591001e0982a034031090440d65201c140300140031201032054030744205200120b100c3d4034501808000d45a103027401030712032a18102070416103000c01707407a6080d00d02c104400320210b0703442200c01141e90100c54056030703121170780480d841c9451040c1b104184021300c08600d00c41c64020101c010750244a0a08040c41180904820064450b544501c1140403d829030303943c2510754011807001c00c3c0c141d130041070111050890075645110403601f00c50000014040c1c840481082001d111b1190040031a0090440b1400076540304042c41c0310181010342880301c110703604d400302c1e0710075003000100682ca001075581d24100448084040c0d04540000c80c0802e40c04000407 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 923152832 1250 923151582 923151587
    0x3020f150417090f030f0d120b150f0f0403120e040c050d1d010c050919050d060902060c0a240e0c0d020325170613120c0515040c06 58
    0xd0259030010050b2030790328980360141c2a10b030b105601d03158011122140d041482c0c1c0d03040c020b00034810f5064020f84262102414024000940d2000c1041420714140101c140c80d15480c00c9030707410700000b0030001d0303407203c8000c1401342030b02600000c002e502c50f001602104200940d120040c2d20f4040c1e0710b6846188018100700f00542e030f4070006a0000941c103010314100c00926070014100d000440208054030042400c241d8290742000ba001004954000b80c980e595080c242c0d5105508040044c07940540307402c207400610300f00d8030340e280500415203c0034284150341e1518215550b4901e4601156030705401480c054040c000c9030000343d04c5050309500a680e140500340240d00e428450030002c1d11107404500c0800010788a404002d0b038152050001800204c10301790190300d4010860319a07446d07858030b444030040c2c14a910103103081e01504030f5014000030124996070784041c00c0d440190b204013442c5030401122080d0048001503c18071030507011456450303201154900072401100c00c13080050700c603c800d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 923154082 1250 923152832 923152873
    0x1e0602041701020315010305060d020409050d0e060c0a0b07052701030e030915030c1c020d0c050a0c110301020d09031205070f0c2603010b0a090504050c0412081603020f 74
    0x4c825030081d401741030075459840381c0e010365400100181403d210001030b40100f02115903040e0300325504c0d4081b008201226400c002400042342c000c49082d45000d40407801c540d100c0b680c40c04004c1108101402241400d40164143c3d1642c814400c1c0d1102c415440445408802424043d400d0106c1d1034040949904200841202c803021405002c4040c05030000c00180071580c8004c101d05680c0c1c1c0c01b44034068a170b0f801e291200c0a07590300010090f0704c0750303500e4002c0800c440c20040d2010500808001156100d034208240400160300102004220705a0710080303070180c810000304100903850896040304040d00400a10a4503020341410406543c80c0542500c150b02c0205952000c111001c5450001890100d8a007048031030030000b041d0007500708103041a5031b40003a00419401c04000c200e182660b94070616450003840215018055401d00500104451196000d50204061400015018086610210f981d03908890000c050030140c1703424000d480b060710300c650071a18000c003142403040120202d407 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 923155332 1250 923154082 923154091
    0x10b03010b0703120b1c1208151003090204020f04090b0a0825090603080c15011505090a08150414010924150b0a020d021b010c1e06020417010203 64
    0x1c01a241c0311072600c0558010322241e0b42d1400340c60726141410196243c02e04160142c00842c084003400050300c1ca8072001c07841c401e00301c031420015000b0421a010000e44d84503000a034055450907816000440304901401c00744802a410500024105844508100043c0704403908248100044401c403420498400b045124a40003030788a01c40c445241c0440709031000d040711402d10b0140050f90344084400a840c0280d0003034a0307241000c40c5403840d10324144010000d103030700032620300c2d03c56040c101118601c40d40d00c0f03040c00070001301090415140d1581d05d51200540040c008072690103c0709500c40c100903c1c100c03003c40b460007100c2c2c904c1036484014000c2d0b25100d540083c61103441e10b140010050b102242c050084c1d007454030348d481c1e0f01c1559a4070050740d0180c0790103036a40780d03100000403000e807500c0d844079441c0e41194004683e15852480d40c0342000d01e151003d20301120b00010354140591103800b000699403242e0f5a1641075010800d580d030041048904c140d402905011034808414200c4c001100c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 923156582 1250 923155332 923155349
    0x1305010308091905090a0c09030c03050a060506010c03020d0e0a1d0403020f0307030c06050a020f0307020a12020a02090604050a1401060306050a0f0302060909071115060a170a0b09010615020c0405010b0301 90
    0x101191490b00a84c0100c50980101e16004610300c0c2c9d00c0e01ca01c0e0314011181d00642e22600200241e0342445440c0c02941d6101a0030b00b0041d48507041135900a42d11683c0c1c049081c1040f01d9810758404c0c941d2202c1924000b401100754a000c800e0110700c2650280200303460031409445146c10721700380300c100801920710841c0c00d80c0314594100500d0325400c0c09424000d0a08042036800c0000fa00a082c8050140d40684002d41c000c05a9070018541403541683d40e901120030b543c0010341441c010b03a01c800e40180c1c844001d0310f0209103901d49641e024040c04591003044000400d403000844c42d140c0c50b81c4102c00f10382040f2001111700b540c80170001016212400003a42142040002d102c05042a0104541050007464415010404031030a50b050203505a55540500080c2042c4a940d2a02040e9840a00500306c41c644038400c1c0d08844a5030f070755080c000103010041c0700d40090804d4000394070500040c603518189151140c0c02810007510307102c00c076440601c22441c000002c2903050b00041580e0582c0c9410 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 923157832 1250 923156582 923156599
    0x90c010807050d091e08030a0605030115050d0221160f0f0b1305130f0b030f1e0705090c07030329150904180b07020d0903111305010308091905 63
    0x20f0100c503000c1c1280b007800b512602d0003040c45004810316025040f4100d4001c012454480c107001c5906000e84500b070b48500c2c40b9030b040c00300a80103605c564004000729030003260158007002d0184045466954000c0000140c00418140030008402c0401d449031000c0d1062170344031030103448081002542840340120000b00400d08014040c480390440144001c04800a51f40100d07070762000013440c0400c40410500810707031100070300c0ca05240d43d0b0140030180e00e81107000c1e0504010034060359560701c41511598814070340100944512140030310103040a010301a10f864800e150039030400d2202e03406160100c00080c6803c40850400300c03404d8000c1400307654800444403400400080106e640039491180000f00001c0000d01e55640d02c034400c403805c01c4552211026201030300e0400c01341402e4001d241d2401d54000c404c01d0b1220550110303202c1c041d0383c6d0210000c0195041d520119180148441e04d044540389007100100901c034244004c1c14094408544e80b8020100a12440300c228101c1d00c101c50f0040c254 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 923159082 1250 923157832 923157847
    0x2070219150f020312010b1c060e3603090a06030b01022109060c1e070b09060f0706090f0c0602030405060304120c050a061506210e1c020105090c01080705 68
    0x41c0100381e20001d031403040702d050842451910001721020380c410701040c040080c420a915124408103c5000d000820030844140f80c9050701d924850b00401d443c0c440c0140e2058802d4a84040e014601c035481d00078613141c2207104009000d5902c0d4400c5201d0340c807d194491002030114404d00400400003810b9000d04000000c81105908000079145102c1100400b484001c0b015100d04015150074180a4000d110034485c480252040d420110710440f41c94010560030720244030144110741d159442624900d55890201407603107028081e00c88002c00c40c60404800c0070a000100219031045800369400d0343d401a0303902070a07680c0784518130485810080c2480000c0200789610040302400e210f50408100e80b21b10360352040d050002c80081261490b0350f1b40e03889915150b8900c00daa019102c14103048030b4002c0d26140c0643d90b52150b04035002d915854440b4030403a81003d0100398800c0540d6040080c0e0b280020202038081d0500300d9000800344103400d80300c0380541c411a0701c5801007820b52035543c6888ad5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 923160332 1250 923159082 923159087
    0x61202030d030c030b100c2901300305070b01080d1209050c030f0d020f0109020604090e011e022d04170f03120115031514011709010207021915 63
    0x10b29844410600d0b9440302145e10b0354031070031751856040084c1c0d5070f101480c12040ca000c1c0c40b49150328050b1041c03d008181038240242d09482e0030f90644050200c0142c407441658500e5045a02126120610218060360003040603000400303411040e10641552003141c1c0c8880009a07a242ca140545002468028100e100394040d076100341030030ba00520a840d400c2c2c0c0d084010900e0100e08130143d4078540e20910040c20941c3d4140f03d000c005041c088000e00c4848103680015441d80218001e003079026698450401e051182544001c02c00101040d4600b001c0d003038031045e100207400c03000c0c4810300e031007025074040511030301c00952520451842204c00d06140c01d212644c2900d0000030381c0401a88640841800119070820103400c0144c59449107080540c14810303401c9210802254a009040c2015040c3c24a0031034014820242d0f01400d11401507458401d004854900800203076419050162041c03228a0006400802d505402620052024508212800d0308000640b00d595641c0c070070325101050642c07 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 923161582 1250 923160332 923160341
    0xe0f0309040f02090a150207170703150b030a14012d0b01021e010b010e0306060d0809040b54060607050d0c0308010b1305060a03020f03100603061202030d03 69
    0x80c1c01c40e005080200550100c3d280b210340d50082100ea0b003003007940f000c1051f410091200548604c800500f140500514050b0351800c5601005100012041c4049911003e507072055401803c014102e6000c64480d050a2089030448140850294245036488000c19411303502c01d0725541c204050300a48003901e5003031100038004c0105807030441c0103119000d052200c58061480d040d101c40000050780c2c184880025104d841542c022070f0080d00311408100950350350781c0c00b01e0422504003c50325a28140800040d008083c00700985900042e034040d95040c60034002c401e501c1c141840c5500c45400d000c5040000c207140d80c084561000c083c0001030501440b06110880d681262010b404c031410028266582428100424200d00008100303983d1107080c554042801801020821141490481c0081c1e01e0300191416000b6a40900400112009810700c00c0d81141d02e0004541540b176140c0c101480f88141d80b5000384204d000280c00c0c08000702c1c80b4080e40c5044503078554024001c108520800310241c000d007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 923162832 1250 923161582 923161601
    0xe0c12070308180901060309110f03120c07090c02030310060e010e0a0905041a0601021009020f0402042409141309081303021309110108040503070618060e0f030904 72
    0x90142040020002d4031500c00f80908500394444800d540b5650710600003000300c160710900825081640c01008150801e4030018485010b071580080e610010011a2501c6c2c0300341315559a41d80c000a091101d00303400b0446000340c561108003030003003c0c3c03070003030881e583e0006a901640302c2c10b002c0c00070003289002e80b43c002000c00046c1005409541d40500140f4030103000d5201c0841141c481c800c0008002c500d003042082c020314882482283c2c2442c00000b981d40040c0015045065038a407644d40a540e0341070758080305800d0003070040d980c1b80d1726620304001d08080c01c03d9101e480c854500d140340026009940d05408c0e500b0b8103182d40c1040c001441007154984003c1c000069082d81c0e000d401700446d0003440240681840e03055400820b41c994410300071040d4014042408a03483d00028800280c80040c0d00e91010209180c580619212400c0203401d40c42540d800801a138a00710090f140e104503101e40780c1e0000d0050200300041240cbc0c034202c9481e8501703940401e800790010001405a490310b9441480f59 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 923164082 1250 923162832 923162869
    0xb0a2705060423180105130b06300c060d0b09090606220e0d0e180f06040e0319091502030c0d0302030a020d0e030301290f0d180c180e0c 60
    0x4180c26138140501715441504c0d115540045086071384140f00700e480d04c1c103070841000d44501209e00840602e483d000040780079072503025410604855000d03030b0304012803020607400808182c0d4803041030032003000401c1c803802404c1c00340c03050b600000d050900100c1c040d44a01c0000c4d043e80b11450500282c2108214061090f9900340e54a11010100c030000700489200107901d030719005410140c400800001010025070240706d11400d004000c40e044c1300700080d0750001411b40700404d1005055049a0440c003e201c80f0b22002c0e00c6051950025940c424421030407158450003482040e425941c08036200d2007903c0c400b0507154410038a000d0308503c664011588030500758001424080040008415900700050f8002e140c3d2022005002040c2d5052508012115000d8800c64803000f07451141c0e00c0c1c0c094610440303a46180404e00f080e2400490300020001c0917205800e5461300310600c2d20382d855000034000c0300c401550311550045800341c00d10901c61042c60358001003030050240801c104942c5e1000300070136070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 923165332 1250 923164082 923164111
    0x11d070f08072703030801050a1a0f041d150f010804030f0e040903171806072f010c030c02010c1d030a21030b100905040b0a2705060423 60
    0x1540640e543c036681d071480400380000c18844c61820700800801040c2c1141c3e1081c0300d80c0e00308214550200c22103404609485c81190740340c10082058140900481e400400d00303903c100c20111001c1c0c0c007080d00d544501c4621240080b407828031824011030590041041d800300b1144030119000c00c0c012400403400e01c24524000100c4841440402d041d03c00118044011400c2002940c011001d5169041e9100c000301c0d41c0c0d43d60301c1381865070300c0765203810207412001844074004905c600c139041d00c208002212112844008041c08140c8624000c02050020b41700007407614440601c4d4030301c18010748000c5000e5569419070a19405640000c011004151a90501c2200c00c0c02c80041c41ca078400c2c0d1242281880940c903088002c40010f402c0c6c400031030907544120f6400c00f180d1b40c200c3e044036104058590940d0700089408103200840d912601170f40100c1041102149406000302e50340c15160b00c43c1002c15010f0200d81c45840500041c0c4454110a00c1c00244201c030400e1140c0018680c19480021103c0004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 923166582 1250 923165332 923165357
    0x90312093623090c1f020a1208090c0117060f01030905070f17160b0706200d060b04030b0a050628061706030619020d14011d070f0807 59
    0x108651840c40056041d4440150740c442d5400d18108456100c62558042d141444141d4001080e807113103484244112945c82003030900041c803c008030a150781e880103c404540082c803501800d4010100c50a0145100d81701402d01d09510404038403a020703e2076081144261240d0041100c2d0803d9403044504242d0780b640c5804c0460700403c01c2e6402001407545e03d02e0b00c5030805010031003000c0b80b4458001c1d60b0340b20526200b14400b943e07008400325030b000e21a168886c0301d98900703900501000b10b120074884010f50312045640a41e507000b480001d901c4001080380550b91156906a40940e01c00a0100c14a400c00110300600503006030f54044001060f0720312003030030030160790300c1c09c0b9602c48400d0541d0403004c814801c10f60842440745a00c0452504405145421400640d5928005200b01d45501e01d03940321040c4041c140c0c040d82d104030110f810500840309000c6480ca4036000074881c2c86001040311225680b1454170140d1140100c280e5501c002c00c5440411040c2c0f199a005000070003009131402044 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 923167832 1250 923166582 923166689
    0xb16050712081b030a0b030106060203210403050c030d05070e0109050a09020a0507020d060b040f06030209040f03020f0d08041e0b071d1804050f01050c040512011b09031209 76
    0x6601c0380c40170740c00010300051640103150841d59107420440555208102c045404848402d412402c0400f1485806460341e4928007242d0034045c20030f1850451201003244035405845401c660320515060b80e50660007841c8400440300c1d200c052241c59000b030600441400108100d0300140b609440901700189004021381c00b195203400c3c104000d41d4038582d20003502c2c4031460903020340035080c004c004044c000c00d400c2d40c0000301c000a010b40000c101c011020015402c0600034031082d40046050710643d564031031610300c00351103810308031000c9848490000041440003902a010b02e565500004212226070307840d0415a04001c0300d11070302500d60300601c0c44000960ba4a2201c0c2c03102d5025003014145400c10f4a02149411400caa0b4180d040e41050100030701e050010341554120b510845072450800342809113580140302045010303840c0b041c1e91400341b00ba1a00002d282c0100ca125041d16016029103620441d0000f519002e800d203980c3c1240301100009000355090340c1d030400020780000d001d52149040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 923169082 1250 923167832 923167837
    0x309030307050609060a020711040c1205130201141813060810020d140405061512011b11030405031b040b0d1113110a030507110304030b16050712081b 66
    0x40303445901c40030030082c000c401030013050342000e1b4000c0254209101c80d901c221644078a510703054011503482e10204900c61103401c6602c01500144410400e5007414145d00714904000c0909074007194008040e4070f0410f40220440c0c0180d900e4521800c061f605800c100052072840039180d604081d240c000c0803c41d03290500c4503a800600441d401030380c58454100c0542541d1010307010042d0056400108800f20b0300100c3d1450340881c8440340054405218800113174075004928051410b90f10b000c102050400d100301c98881040c405466984040302040c40c0c660b900d10690007503d030181c00c00c0c007841186002940003266400700052010515a04075004900100700140c82900c0d824650051800701e400e0004144641031042101032004592107844000a48901882e82c410965504001440a4441c100d10341c0b03134400700010340e5500c51b038a0030841002c0c841524640254a0181005e504480c0513004a598182e8001c10b2000000c00c20242500d2207070004000040340011080b105c00c200244400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 923170332 1250 923169082 923169097
    0xd0b0a02030a050702031306050d06030b04060903020c1c0f4b020a0b07050f03040e0a0f05091f0e0d1d060319050a0f0203040b06040c050a2003090303 66
    0x2001a26442c0415001c402e0740c4003c1c01031320941d042084450080280c0b400d030301d015662142402075a415000c031070f2400600e000d900140102d1100740a2004110b502d820189540703000340d00321440840514100302c64180850002d155512410221400180c0310082218113240a00001682d842c5210075040c49118400c41b120703600111012540405683c12071190f85101c074146c205c02c00e04086030702140710b40d01240075a0000350000b10b10107041003002c21225040501c91010380b0340319565542c1003000150103889840c052400c000c0c20080c1d04440e4480c4501c1000d2040003002400e01014140e80f81c00f600d035150080d0b9549440009110034000c100020f40740c445a6241c0c2c00c3d24030102c01f8007240030002600648184c0d820030030704c40040c0c4542c0c0d181e03803207a0308030500142a8403035005100041017101c03082035045002004000611400902045c440c03001910107004207121010110355500c545005280841c00002e0a100490b1001040104204100044074900200500001c1c0b03140c20161 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 923171582 1250 923170332 923170351
    0x5071a040c090c09050112180b1506030c07060c0207080d02070e090706020a12030f0c080402031c051c0e03131a0304080403080f090a0f091d0c0904020d0b 68
    0x20203220401c14400c201c10002c00031668100020341c0b607003400904491440c030500e810011080301c03540c00c0360244d074050300d014204549001c840c0d021f03c1c601051202011900b0354080454840301903003508040c0c003102d1107207001d00c210302d1511805541c1c50004152180740c0b0740440c46814800705905104000c81110003210760020101d00380740107198240103400030400480c41e00f018504100003034002402018140d80906100e00c102041d2030100e00602030f02001001145c01c1060019443d6004a1b001340214001d4054400140c908002c141d6960201800c0c100001c86c204000000310010741001e91555011520104e4405103c04044d071031a0401c02406003078950300c20781044410f502e0300c1c1c51040b4807170708441c040c21494561584910340c001e80c80003030554100002c5030316640009204445144100604901400340c450200d80c41c000c406010b2102124640038544400300240c078021092405044001d040a02c184410300802c210013801c1241c0090f000628000000c011103a2580f141000701c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 923172832 1250 923171582 923171633
    0x61b0d120c170705030417191409090a02030a062301030e1513151b08100b04090902120a060509070609030506150a0503031804060902040b0301150507 66
    0x1920030034116010a071000d420302c0a24100c00c03600802082c41107920040728108540c60750b5482c203080d58002d90100c0011303680807000132528004104521140025850350750758600a020070303088140b5511031459160761040035480010f5528280360021039100c11b0070032021400076a1990860041500c69413a20207400c840c080020310f95906120b01030301e154420008003640003441c3c031281038082c0090480846044103041c0103090007802000358400c011800c0d002c001011300050035003a0f8200e100410000102840302203441049100da400054031a1100742c41e00e4180303082e14580c0207241214041307070040034101040700300c5a01445885030540c01900041040c0c545030302c5060800e00103401c44000d0001d050b07003c1c4081240000c1c0103520007a00b802400300002104005042041c02d5440594584000500d00c07626006003045201441e00546040c00150380707605044050380141e018480039004240010041c49568151450516006080040c68034260303403550181c025050320b4001c8a1100d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 923174082 1250 923172832 923172857
    0x80c040c0e0a0605041d070f110a171914040501051b0a0b040b0a0903080c0a020f0d05040f0b0306150307120204030c0510112a030d0e0a08010218061b0d 67
    0x6d4030040542c20360298240343c452070075500141160315220344800403c40810203e03052a4002c1005103070807034103c0c0904040000001c41c114107a401000c45c440100e2041c161000d0450065011030010400081200c0c1814103102c011111074210088000c5100540c480b005c0040034107114a181150081d08056124030701307410214a400c502a08540f000c515056036040465801170b90036400c050b00d0480140e445402c120708030300d00b0420300300c0018180140000c106100b44c00070014001c48002034034039038107181d444501e01442c0c007045a500b5003214612524480404040c0000c1d40d01c0f034440d00b4250015410046020101c0c0c0107a0001c40b00c2c2403419070180b009280c0440d02442d000b010b031400d40760740055560701e9916144a081c0c900c14005c001114003411000021480707110080207011a50181c2c8ad042005008001c80e0b0b541d28003810700d402000c00d008030103000321410309402010001c002c032201c0341132000365070141c1c4422102070780e5414500503001c810300c00c42c2c0070000c0c103684d043ca00d40003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 923175332 1250 923174082 923174099
    0x2011b050703020717120c010213060806130e062d070903021f170703060810060e0c07051b0103181101031104030209061003020f04080d021204080c040c0e0a060504 72
    0x50360704211865082800d1480c4045c0c000115030f02940880211940c40e2481c0c00b01c5d00380a130140850701528100c980c0e40206103158400501441980215911030f065103511701c90404490a01d51400c00c140c000500203011034040d20302c400140e00000800344900003221070a100a20015241880003810f0a0810030540c83c0c805401c0c0c41001c0c40d1080c1075510091090301924444500d08500282843e1000180049001c1e034080c00c01050020183c48078000c01480c488020703d6240200b0492101d018042001400b402007079810007a80000244018100100c408070f082c4400311040d4101510346030301c100c0c0c48540049a180c1c1a01c64580007640ba801040050291140304c00c0700c0c41d034660144005c00240e82c07405103e940000040e18075000402821104038064410b450850300c00c207000060016280d500002c00022902c0103a00395258454041c000c03420300d20403403054000c00d078004516401d140c5820303172150030314000c0c90620400110641c00070450584c0f0f254804404100e01090410950f407 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 923176582 1250 923175332 923175343
    0x13020919050c1c0903050c1603051006060210050406090c03031e05030610050d090804081c02010c0903230708010c0909020a02210903030d0b0f04050103120f02011b05070302 76
    0x111120281000100000780109040f100665546162202000d506040c0204100c031402100e06058407160818840000d42c054002e2200325160310500b42307403624400d40f5108850960703040d40c0c09080f500710040000d0000d0704003d8410380d4010743d1804039074000750b40f004100380154401d4640e580c00c070018098404000c3c0154945c0c0d4180a03082007003044965409000a800610a00303003162140321511321200204072414005140500004010441080020b80105008481051502c003282c24084c124203032000e50300e5510104040100900004609a48250390703a854404044001000074004628215099000c0d2169075914030080c0e045961142aa0300580883c9405600e030020080d8000c0d6035103480c0d000340741e5800d404000803a428500c08111000c590000b8112901c400b25202c0c03a400a1407803054843c8940c1400003102c2040c10107028482c12039420030042d0350009420401500c8102c06050480c0855682d4811904030742c000181e0044020030326550982c8905c0149406403819 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 923177832 1250 923176582 923176591
    0x909013c0501081e1006170f030a050304080c010207061103150a031703072c010e191a0c01140f011703090d06020c010f0506011b0203030306091302091905 68
    0x10308003401072100e8107000801d0030b038100c4134131000c9518641c1d03444403078113040000100151513410000c0c00030700d1030211081e90a080703025006580d1480148210705030741e4030542c804080490b8062000801107401d060140c080b072800351001504c2c1500c84c4d0303038107811981001c0c0104041003010007444040f1000140c1c0108511046d10200000b0381151120104060010003c86d4031800000003d0009441b50010643ea0882c418008035030506911b41c154a9520b0b1640007800144581c2c6c0c0445145881c107013154040849111030b030b14132414108907143e101c10009424215110420103072030380701c000b40308807507150200840c070343c01a003800101c100a07004103a101d8000382d8101a45920001c4010044440000e41140d245200e04407070f24251020340107071840300c3ca41e54a8159a825000000d40116104510999a011540e070100c401100305910540d0040d4140d401440010003508010000300e80013200209601d0180065a00052007428211003003540d0840041030b9140701e03c0d9a02440303401 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 923179082 1250 923177832 923177951
    0x31f0e0a080706020a02070506030c0703020606012c0102030f160203010c110d0e01020703061a010e0a15210216050609060f040f02010309080c010b15090a05090901 72
    0x800681c5416125014200d4050000c1da030018120030814001c11910f4014040a41250b03200c0c9440e28820f08250844501900503000300720000b11958802d4000d41202c1c1e494502243d5030280b49201208181c80d45002c803410340c8001c000c90007400c150034018200003c03584040d00540701c25403040c10300b07640b600d0220b50140000742114200c402c10129040003000501d1404460007810080101e1620040e540050042c0340341125085a1440c4a443d46000380803e8840500840a03078091196401c002d2081c02c0362415000150082a4851b4100a00da1444c1180c401082e01c0c4c0100060104d07400300d80101c8001420104210400c6400d011039a4030100c0c94029050600d03090f407d20400c42c1000308010280f880d0340209508580c000d0340228101e9401c10307441d50711444081c0c82c090003000300c0c03c1c01902c1507100d46028462942000c08071440b10320007900000ca49468242408001d0030041d103041e5440d5265283c00b07200000e00360501c0341c034658a41b00201440001901084603103000c0110990 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 923180332 1250 923179082 923179093
    0x30c0901030e070b031602010b0904030503090d080424021309020c0d05040506040e2e21110906030a060e03030f06040507020d050c1e0307050114190b0609031f0e 71
    0x1d810018010740b40d00c140c648038906c80300324982030201d004020418a00c0da00c8101c2d1401d1106040e8800061031082c0c000d030085400040251209803081340084400814052002e140b00c10701090351205048105041c00e4094200001d03842481c801c0c42350ba421298041d035000c1491490f640d070821154644d440381c3c1c14454036080c14a0007055440c030541c0165111102d03000003040901440107105048250140c01c400e280003081d8446204441d5a0310800718840310a0340303e4242403041c03510300c4c240076620680e240c00490240b0244080000014042a45800758030316210204590f4014009215444005036582c2c1c64488640780c0444006803505002703507c1c00b0100400b0540019000040c05090b05040303417180c4102200c0c1d85044200c1181c4010f201612400714854040000600307035003407081c4002c2c0102240c07456000c841103c211004021481d001d854001d03280944c1c0d005492691780070785054034145655000c00d182084a0340205d0705080d240c000d80d0040c000c0c40c442c0d02d6010024402500703 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 923181582 1250 923180332 923180339
    0x140c0c0a140f030f1e180411092e050a0207150915030f0c0507030c060b0a09020f180d031e12020325020c03280c121506060c0f140102030c0901030e07 66
    0x4665200c06c03074030340f07003d55503d21391504840540400d40e100200002d00510040b069510a241605480c01c03420b84800080c0c04021891405001034400c0180e540e40200440c61030700311075039512400301c98080240122000c5c0852a01040c4403118411502c0e03441c00b040f644410300c1c0100c22640460032180400400b4040e120010354081e01d544081c070b801c102c0110311480c0210015080042c03680c014460130f480058207100030080d40025041111202207d080010042828002c04101d04040103000480e28142590058032403691040200300d2450b1001c0e460111000c100204d900641d1103a04500102280b010111380382c0c1d5480114880340d02c00b6044440d540408a40c1ea150032241c90f210400c0c3c240c080c01400b80c055040c20310a03681080c640700649586505000e449520420152034542031840010140d0110317003ea1021035085958010007403800303803204140d141c0480c50031240f000d0030040450525509002035401440e0000850365074540f80000501129804284c2d0040ca421414041 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 923182832 1250 923181582 923181607
    0x6010f0b0712020f010f1505040605030a12110d0e09090d02070603090609050303070917030307050a0f030e15060111070506040504020901090e0703140c0c0a140f030f1e 74
    0x216440c66120b2082d41c140542e00005a05100201020720510b43ca001c542e0404200240c07c41c04012844869611400d41c588050206490311401366a4056000014400000302c0b403c0307a40c0d000c04407502d80302202a00e0a180d441c00c041030b450252001403090311498019113030160803150400902002800c01504078139029460744100c0c40f0f108141651480307540244035003900100709266209050fa82d8a2400e03200c09000d09105009840300315140b405145810100002100d01540c80c5460740c07402d0040481d0120354001c855041001050b17200c480c2180340d030108001c1200c202c101c15132030481a10341803000515800742c003484691994041001081030780c5a4604480c1600c1056030096511001100142c0380340c21b840e8490000d1807030344010030404030b038142d106000c48602410301c1c00a075100c1003502c60081c05106a40880d9400c9541d178500045d158042c4d90208074001000d4520fa003211640c000d0a40d0421401c240c002040010450f81c0c020b03150310320a0341c3c6803595420314100103942d100c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 923184082 1250 923182832 923182837
    0xb0313020f06040b030c030115020a0f0f06140a090203010b0102011817120f01030326060d0c0b04030317060913030c060b060408010912020c1c08040b031003030206010f0b 75
    0x1900607039400c5032559064880904403000351604d001c582e035403402d180101c0c1d54154000d2103180c50405088201400551000c188031503056040680c100e01d1148684030110f000da503200c02202c11a94402c1600160083d0414440c411092a00c00160b008054014182902c0d030f410011811a490104101c2c503101c2c111400500590b0030140c1c6c0c840300001a000c1100740d05c43c44000c43c03003282c2c10404002026443c04866810380e4800e9a407030041170303002d005032460151b031100490694000640080d0140c2404406040464010b043c061100342e80e0300d005541a62141d0802c2c0d0010300324090481160062803407581e0003440941b00c400003446c0254580c0040c08000d800182080307140403182080c080030780c002c080c11207001080a60b480342daa8800d54000c0c0b24400c421a0380840c3c4900b0b80c000c5500100c1d200011150140418943c82c0d548000c0c0e0000110203001199aa5810322010401c1007408024603c074a01c143d4480040364210306010746003500503070220a881e0808181400103400b208203 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 923185332 1250 923184082 923184121
    0x30221042102060706062c070f051e0a020c04140702120a02160609150e06040909020d1208062b11040914070f08010902030d051c140a060b03 62
    0x5071920303005582c030004000748a801c5020f00f803039003082030102d180c0d420700380010500300b04001e03000c40c1107400c103210880c1c0d080e003114428007103292074103c2c442590181005100c40e04240440b5076001c44c0c94418051641c01500500d0016842035032000c25a00b002e10581c0d4103035000c0200058645803202001f03503500d400075084034156402240b0008054000c0013602d03045081c12451550031500c40100038429042ca2059114160a404c401075516006003202060311f04e02400c403520f05420700c56064041c0002071012a0041d440c0e1a00e0000b103070070914603e4041c44180d890101a082c05410400703a001c0c01003947d040ca4843c825013110071500d5003400300d4100c0c0d03c40d900c20b00891214000a008091008000e8001d150085801140700070108000041d00c100007104c03018039894200c85801c03292000d200a415511182061040c0c038012009044070940c1040126800c0041000c6030041d980f403100303020f0b200c00484082c00203203446c1e4003902d17000c3e102e8031001d5415490214010302200c03c09a5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 923186582 1250 923185332 923185379
    0x141018050c01031e0e061b130501110703050114011406120106180305010504050a0201030c1106041b0b0c0d031a0f040507051e1b0703050a12020c040903022104 70
    0x4000510001e051120500d030715481301000c1145940d0b00d9881c076101d5504540d0804e00605002c8425003142c0b280c4d042e5504140f440066408403400c100065a020001d10340c18242c61103414400000034a090043c1080c2c6070a6511011195161a400600412040390001d1003905d0500c181306030301c00460702c1903044400b0752404100009040c0c10071026441140c1000d84036508240030401407000000d4160307a098800e903820041407400c413200310f901000b8103101243c070b03400520104020900b0828460000c0a91032070040c206503607003070b8500b056032049100c101c15820851450b0342c2150184198044030342003070602a01040c2443c00100c5800c0d0a0060611443d07681000c42d031101d126000382d600e1964900c030360341c000202010214650b904070901001a151b1040000b50110902099810469031b0260013072880301c600356198540d01c076550308a8400c52013148409503a82e640c900032072030304c0c0d406030700a42180c0700026120030b6101c210104481948008020400c038103108071164100052000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 923187832 1250 923186582 923186591
    0x603010c0815130c051210080d030b0616150f0209060f0d060308030a0e0c0402070f0b040609080301150216030312021806030412020f0a0b041707141018050c0103 71
    0x40000d404441210341c1442c8062500035019031050300003001b4a003c1e540d902084c0240c0d600e0500d4024844014041c240040c0c1101d001030458038001d40000400c6100184a0341c1051450f04031001401030b106402e0b51414010280c1a001080c0c6201d000b040e064881030562402d0320a001084961141e010309014400740004c04191803007107503104a001d1a4044410744d504d05210000c8005000b101400d803003035004e54406202d2500c1c181c800c03103940c5948002540c0b4400c82c241c0320441100d90080050f00c0154078ac0e4920000101000d00460190525080200581d00b03990b2000b0f10745a01d0301070502100d003503000103001003500600d03480e0340c182c00c044026070340e00c00d010101881c5071006404150402ca000c81840f08000000d41c80c900408403981c201c985103002101c000f65690035103840502045d28880110300030071003400c80000b94905200714030f481c29107595148002d000c0e41c40041c3d10140c001400580314540b25002d8144405220880090f10002c0c5458550f01c13a912854023a041c035999 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 923189082 1250 923187832 923187871
    0xc020907050702030a1118010f0f0b0921120d020a0801090c140a110106090903020d050f430b0c0703020304090b0d020d05100b1e0f0319060b090603010c08 68
    0x4101f40500c944002d9148000d50b940d640c90f040d000031040e07004035000c207108444003066420610041d29004400180808a030b103850120700160842030442c501c01d5402118011151241c0c0781004110701440c032000160b8410030f090340240a6441070700700a00086c18483c4e14000070b40e00a9a014070742403444403507640c0e2600c01c1300c02d684140a0302044106542054000901d0294550001200a00980a0b208141c004501c00c45040c80340490028042d981480228007110501882c0402031072b08011500f9280b00344101c5000380481c0c40d082020540d0740680c10307010403505882594000c0030110030141450079940e006074883c01140114203525544900c0c40c00c003a526540100c2403282c0103020900184880c1c14003984860303200c0c00c440d580c0c0e41000a401014101000c58002942d902c091020050078480100710728640d01074881c0303505d0721170760f1054960703c0c0040c9090394000b4811a00040c0940c00f660610810302030003420b06e4800c1c4d1604c414000c0c500e0304050300d50b50041055170781c480c00908 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 923190332 1250 923189082 923189089
    0x305031602030c01230f1b1c1e06050402160b1003020d031d0a1214070e100504050903211f0303030f0e1c0f030204080a030c020907050702030a11 64
    0x1662040c805070358208600398603004021805c8000015481040707072440e42d150700c0d0301c001d001025555010b90001083c500e00c41c2622a00290050704600c40c192900d803400f1401c0c01003620b8a001283c2e04049019a024a1011084c80b800c0b0090101f0303101541003100003c42102d10810301507006d07004810880000d01640540758501000e107074020924140d210039411300074030700e01c030106840150902c0c0d003980c6461480d100080000325042a010074486481c2a03850403522034030700201060030b110300c04001c41e4090541c1c1790f803845600d0750080da40c1d00f68607100802c01520000b610210700ba1300104104c1c0d0045581c6001000001502040d0603840d8803401c0031100c4411322203a12040b8401000808070030160b00da0440d24200003210024805278200c005010341b40e181441050441064843d0b000544d07038041c01c0700c2030700c00b100340c18014101659540b0050911107101d204900003180405100214a02603801c2604050246040741c00c10f403003540480d641e2010718102800d11200c0840c1e1980030b41c0d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 923191582 1250 923190332 923190337
    0x10b0303040620060a020a110a0b070f050c0d05130605030c120403021c0305010603061d160c02120a03021504081812010f0605030c010f1211071e02040b0904030503160203 75
    0x243e418115092407030980240c0d8002d400c030440c40702c000345002e001c43d1a00079000590304185508011107040700d840741d80050303c0d1485030301407100a12600344071840c0005001c0c00011440b40b0180c8902da0382e0321401c0314074500c1c09030603006041030180920920040359100c00a440c020200242e882895841c1d604003640350944000780543e40130034003014010840c0d450380013581200c4a50320140005501c460545200c800184207040520242034005034040341c0c004090081c0890608115400001c00d4001c140d107407241040800559106030040c50800d90b04000211403110b5009200901d81029620041117116027401c0300092400008014110390f41d44e00f21103000e40401c402040b4038082c1441c54000740c00c091164601c40e0250760700754840d9500a40109181c440d0743c1e0365900e5030600d501d038240d00038a001002035190840a01039400041c1098003d03080e90100c4425100048182c1e01c100020740b40340b1010640107074031160a000c00a600a030580b6003005c01c05800c040c0d8003400400491850 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 923192832 1250 923191582 923191637
    0x40209030129030105060609030309010c061b02060f010f08190812040f03020f0d0906080c0d11030f280209011707031d0c0a0e04210e1002010b03030406 67
    0xb01115415142110003a140003030200c0c005400070700040d07803400100600e90041038040d039050b400c10480d4928561041500c1e10a241c0308202c0051828410304040c60b80c03c000303c0c00381000d68070040c2800007401c01c0312803990050a607216001d801c2400e06802685440c05007a140c42c01d0501043c0c200c1c1000703071440c182c0704240d403011012101403400707051041104038031030f500760050301070801c10b400e5410000c51141c10b090920349404203517030704e850411035203110b00800000c0c080c1c0703040c806001c07196a41d028000d4503940d08480c05032a41007841350b01c807414034084d2429940c80d44a030414201000da003040064a505001001a00e8296080068941c482c206202c200b400071040c00f00320b0760f0ba400d40d0280e500050070044808107004850030441d9526600c5c1d070015403007000070300100321404e2403031146c0d517004d4490000c40b101c40b80c1c0701c5500414007015048a03004a00360101500d08c42c2000b00380c40c03404080c0b510003400f041101901180d244d12031802084108500c01ca4645941c0041800d0300242 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 923194082 1250 923192832 923192861
    0x3031b150c0405011106151c020310150f06080a020d09050d020714090405100c0219060605010f021506060c01090803010b0403110a0e070813140708120c03030103020402090301 77
    0x651812400d4895142d02a010780c41c0496082c17080c2404506001480910401d00d03034010301c1c000c1c0008000c00008007a808000c4403414910540040162000d10018900710070010020426241d8441c00117468500c5404c0201c05030700203a41003180a41c420403c0e60041e40400380103940716044100f00007d400340d94005040c5104035040d6142e019800104401100ca0001c071118490b0003490401c03c500c0000e4501401941c42542d00c1031701000140c4c80501c0c0301e100e500450300c2090030301c210040848100e038015108281d40d04800c004039604a8a140040400e600c0034008005041c5522009060040d28050040c100450b11020100c02540a40a085d40040701c03580c032507a40e104540f8a0394020b00007101c00c42c022200d44005410302d5100c4000765514000c007605942d0700e09100700d407010802010500304100d130306a03041c041406042c1410058050601602105040c403c5091a2003114210803606410801405207503401c04410780381566812507015070760b4140e110010703014150750035001c002d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 923195332 1250 923194082 923194123
    0xb13050606190302090f0907060908070306050901150902090102070504050405031207050904020d02030603161a0d0213030605061504060c080310030b090f0c040b060403060902040e0d0f17010503031b 87
    0x3d030085100c800038800c5d05403104464205454403403c4424822ba442054441d83c1710106c02c1c400100180c0196030720040c036000009800040e000e0040d00d00b922544208155075000403000e1071940d05100c00c0340075280a580038006420260360b8180c0e40c0c82001481409a2900e4001c2041c9a01c0392085550b841c3d4010401c1d912110181e1030000298800d5417182d20901c142c014142c81ea4260060300001c4804001d4184281c0340401c1c2c44410a61002c41041d102550812503c00d0141e50b4500300000b42d1300a440010751440c01c4000c1c07000d15555001c60700b030001c105110404c01541c1c07040c3e85441c1264071860094907a122034210810980b110b13007008054124403c1001103403000091045904414541114400d807000c40a200440d0003e10b00590845001c00061003c074101c2e810490006102400c00107402001200c20b81c100903100b204000016480182c0201c45a80034840c00400000f00e00d21003055450320000030b50304d206580392100747d80d1041e40b81c5810240144016412300c240300c0040103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 923196582 1250 923195332 923195341
    0x80702182d040305030f070e0d1104051b0d090212013603090605090d050d0807090f05240717070b010806090d14090301180b1305060619030209 63
    0x890100e4032020395150740c0641d841440010600301c268602407a015240d035071842c2c9038140001c0c0b850000818200a0003104400e43c0703030341c3e00c54441c1c1d04900f43c0103510714010b041890007008240c40014104000c0c0d003400501c04408420424100c8070700f0080d1a200103070340301c110b101040d8030007810b404044007540f810740407007081c07500400b24000c0d542c5001400340090245404c10007401402034030260000c1c8030840c1c1030202034000c0c001002940c0740213003c440405a00da40c2d140c03902c01035060400c0001d90903028080d41c990450f004070090201c00344125455400d02000c1740030b5107a0000b008611640c00380c600d0503002510f004070b032100c580100d05401070903011090158140c0c4405011152036103140700004400d000400d0301d500810f000400303003168031140001103c1100350a02d61003010a020000f026850340c0c244600c20304020410003c40751230683d400c00100b60013000300b85d01d400001c07a100c1100083e9000c40d0060380400300b00c1d0160142c8081160b00000700f80c50741c00094000c0000d00500c07 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 923197832 1250 923196582 923196601
    0x206071203060608101e03080c1011071a0a11121e0708070c030311270102030403030503010314151e060a050307170114190c17010308070218 62
    0x184841003268405002c015600c0b80704841c2d481c02100d0380004039604120510075050501c4840c0c4181400c100c403c204640c4035162201e0035484201c045905ea07000c4020200504040d000d0040c2030304459441508007145915068007180030060600020f814070000540740e1902c903030015a4000b4009819a1600054160300100d0380c0e0035950060b003a4011803c8074001a00000b109224400642d00c0c1d50392500c400805070360610781d0f82d42c21002e040d10f503100440c0300e160361009000e164086683c0702106541c02d510008401d003103150381ea8119001084140040794010003244e045a612112642203201300054150070901e030036580241070f000300e20600c1040d122140300da03400444809102d00154661808000a4a8040c480d56804ac4c2120104005c04100401e200b40c0040d2910000300c2c108a10f0191501030800c00c0f034080c1c0040400c0c01c8203403d40021131150403203001341070070103030031030039801c180c84582e0b010520004012200004000341151180d00b942103045e8040340d01009241081307080c2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 923199082 1250 923197832 923197853
    0x80318010c095006160b01050411190c0501060b0301050f030703031e020c0418050d080c0d11130b0408010c2c0a080706030510060806220603020607 65
    0x2c0441d211880c0050302c409007041e0075600524520f00d02c010441e4402d1070124501060400c104089208112140120703039101c2c24028080b40d008240700c0c00c0e07016500c3c54107400c0350b80107130041c5000c0c91a00420640da170701d01c082112001c03001190f41c09519030041d1002c90b1300140c207510050003942013603400a40482080042c6050b5030045914201c0d900001c0140b6944071050301c400380000d5001c203051403103102c01c0c0800416030748035032060b0740d001c2d142030000c14161482641d442d1aa44021300250050010900032030086580c03a18040c402800d000e0075104c22405140035017110a85d9030070701202e041042e482200c04402d00e0944008143e940c4074103044c6a50014411080254200f03d03075040020f210b10010300c0c20001500c4c0f5003080c80480d172420301080c0140b00f07082b81c00180120000c5034019080101070024040d680e408165460034511b071081c68070304c0e03600a006100080040c440d05550b40d640303503000b11000c005107490351105104120042c0100e94030107500100c000600d0014000b80659 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 923200332 1250 923199082 923199089
    0x402030a0311030d38100503070e031c080718060521070810080703020102030f130f180612020102060a0c05130b341b1d0f07110a080318010c09 63
    0x880c400c1060725001700e00180319058000c0d440341303800d003004040d03038091809160440b101b442c26080281108000c2490b085e400060040762a1040c0e2000705100e038041c0d036551384900705150083c40c040c050b01d1941d54055642c041c10b402d10a0200c1c1f210700030000c00c0041d2803906409080c280083c203100f580034040403000c0e118141d082e20030003030100d040300d00052540d08981e0706038001e51924420440f8145540c011038240c0740310385c460000000d2400ea0445c10880505015540c2983d0901116224011103005a00034401e2480000030080940c4e00807411680c003064000300801d43c41c8503d003084070b041c45100c03031050700b28280e05408900203840c103000e802a050070383c9903038128402e201043c280ca00424198140c4204a6080e0040080d5032242d0455403118446924103c2c00d031504101959851511009410042c9100c1000200c11800c01e4494100c200c07800d1003548200b510441a03116149904050000354001000c0703501c440d00048150304030300120000f00b0207428418801000d28500c1e20 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 923201438 1106 923200332 923200391
    0x1c09060204030302100e0706140c0c0301061e17121c02070b0609060a26120f030103140d05071e3002060402030a0311030d 54
    0x30748040c6119402604480d160902c0360702c01c5035801d0300450155800740c802040050f4210405011034400226003c0c0e4403002030701005d14000c0542101501503103491800141103c4040d81c032111140980ca80703010241d501c1d03c003640220030403140c4c80041e401083c4440703441f62005005215410f40c86844600d00e03c80000c606049800c81842034907007050020170044103280144485030701110484034100c00508000542000008010240100003080141d50054020411900c2c8054600e42c42040da1803030007200c42034242c1c20038441120b107124552200d42c0c00600104400300050b0250360b4031805c2c00600d4030b40900e500260440c1007500d0051042040100c1d24002d26141d03102403049241114006112040c3e1800600c48001400c54205038184801a81d011421781c848582500e40351940000640d10a400c501c01c03040c94041a519182036183d404c0450310b079030303100f44000c0c4 = true := by decide +kernel

theorem cover : BRFrame.Cov 923021582 923201438 := by
  have h0 := BRFrame.cov_init 923021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 923021582 ≤ n) (h2 : n < 923201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
