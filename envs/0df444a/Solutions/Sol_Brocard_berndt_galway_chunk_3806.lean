-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3806
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:43:37.807704+00:00
-- url     : https://prove2.me/submissions/d922bcd0-0399-43af-82b0-ab0a17fbd4e1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 684352517 ≤ n < 684532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 684353767 1250 684352517 684352519
    0x80a05070201050903060a05061807020309130b04060e09071e03020f061210030204060602190b0915040c140a06050f0906070b090615030c0a15020f060f0601030b0f01020a020d02 78
    0x3d4200316607100802d00e403110855008070800c0c0c613001806641e00304080181200c42200341c1c907042c17510b0040383c0030b1b41e02d10642880074000e004815440480c00440d5122000303404e4014800d100c190ba81d003500080500080d52003080074050307038034001096207031040c4401e40280c4141003004903e240d9020808a180900c1c0e0850700840c0400809207001c079416407080c8030300001d640e000341d0103003140188001c0b5059a0041070641d408000b000551050034038807038841c1c40d03004410a64507070f43c90000ca418500c3d1010002c5000c3c16032024807042041c8002e90500380c1d0080c040d500b4a081c0b0740d07400c00000d1001b0380720302d402083c420003541c1c0e403440c285c00c011b1a5080018000c0c1c0d140113071170381e0303190710008048a05032600d40104050142c29810242001e03203000d0100d0050602e000800001120b4000a1081a05468107945080f003514020b02144010104203002d1f038a041c0380510002d5410072040790503500103490950040e106103400d501e00e014441040c1c0c000c1603401c081d603090140000d9082401d03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 684355017 1250 684353767 684353777
    0x20f010e0d1e1701080a030f0c03050d1a030d050729010902030408040e0103060b0102100b1503180319020c0105031014041506050703090512060720150601020d0903080a05070201 78
    0x107144600030fa409018001e020490003860400094207009025500001482e802c01003480550307000300794040195940d034400d203800000d5050f038070512001348001c450101c6030980512a5515030b190b070403202030a201401600000c2441c0d5009040f14885240d000c5848601020036005100602d5a41d01541c2d2142c03050745540d1400d41c0710001c5075000d039002d90088030210b4540356060041d580c18851180000901072050107500900000500400d09184400d800c00c034000c000a07942813030100b0320b58116140001901d80d1042d144400340c010311f01c42600c201c05071241e41c00700c0c0c0655115500700e074400c000c80c0700990051428020b0304400b5508481040d5800740d180c0e0502e610402e03481c03000c40000c03d11500c6003030342d400480c43c015103c84095401580b00c1d004000c0c0c0d214107010086011a40901607103410500071400103005041d40036000b0590801d881081c0500003542442d500a80c0203c8090f02107a0055a4220702107034a030300140401448e00c041440604060b078050809003142610505003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 684356267 1250 684355017 684355037
    0xd0f0e101b05030d050f010302031006140f030106051003020c07060c03020c060c010b150a030b06090a0e060d060603150f050702070510050d090503040e0c1608091f020f010e0d1e 78
    0xc400145c500c2614803a40400000d001001107113010415410403c01030740e802c0c80642c0c60400121940030b00c00c18114010b81d1944108100f540d020f6100101424005000c0098100100401030081d00300c40c420110a01c22a00b000c6159070184054884841d8168000d081c0e2f41c4a04080c024150030074034940490390348034640d400c01c940c0d40c1400070007074011264106e9244e41c0450f400505440824000750f0140f1001c00800c0200e07141c43c4078400c04c5d580300031045001901e544000c00c2e954a215180500300d1403410324080108650144c454040c102c501c034013800f00a0b100250b2008840007500c41c1e0380507900c078910401a03401c2c60f0416240c090094200035003011200210001511040c0d401180c0d5500b00007030910a02c207000c2c20795600000d0b1030003c10700f003c250020070008001c030740601a04a000c0802c7c614807940e1411020a04d10000355000450241900340c040d40d14034281600d10002e5007080008146248002440c044150311a9183c15641070079400070540148001c24841c100010191 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 684357517 1250 684356267 684356287
    0xc240708121303080703060305030304080a1106250318110112020a02010504120504080d0305060d080f0705010b0105031005040b040e010606200111040e0907080d0f0e101b0503 77
    0x80144a00b01012603030403241440d10b0000e094000040040041c10702e064014000311750004190303513015078840001556040d4510007a24440603070512811284568000c00041241140100344032214103c6d0600896900b404280c0640780044440e40e080301000c2d00c042c0200f00105216103081d401814501740d041d405001d01c2040c1e0f44802240d4001d07039102c2007800100140d07181380d1a00030581c0d20340b460030142001c002903203078400a858a020543c43c1c401207101c40c1d41c0c40c40a03403880d5900c14141e980e80c04a03464908416000701d0010fa81039484e004400780301e54050800c40303201c1c80e0b0203d20040d101e0308060410004115601d41240c00075900c5d01007007a121002d00c140406003226840b5140c100d803110388005880c814000480c8416410402c20300c40c0c080703070380c401d035001d540345041c5031202c6a550304035892601035564002d0f0024800c90340f0190b00e071500b1209071501990180d9a101c080800c090a10400240b10020000001d20b048402e508020b21055540c04840c411030950340342c0b0700c0da94 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 684358767 1250 684357517 684357547
    0x909131b0b0c060109140f090114070f11010c091e0b070606051e09060d02061210181803051317031206270a140a09050c240708 56
    0x107044085000000940b0606821007000454010524084203010403141c0d101030040010b0054011000103d900c004119180029041402d01c03c1c1c0100c3c802c1036529140500905c800bc0000f0840086041d00e05040d0714920103020f04007418080380c485090840c5040c0e252601d1a5414000d1065212072102c0800d011b003204004000a901904000c58110300b17003010031188105a6807040e411081003910100c0c1c94440c1681d09900a201b00e8071503140085c0c40c0081a098442d152600d00159900e404200b0a503828014210a80e8170181b00da800220110030320078125400c40001070040b1440020350300000c2d205900a021009852403d00040e6503160504002a52035290004094001060203150316a03400a52039000e83c0450314134101005400c09900718640700092881da0550b1240000c0c000720081d000110103000321003501343c0c2450810100c0c1700070075034490304941600554420180078a0b2101d6007008000407044010030920703020784019126800000112031540381480244890400c1c5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 684360017 1250 684358767 684358769
    0x30d1e0e1e040507021b0409020406051809120c10020a02030c070e01030605061f0e011803140c032113090606030b0a090203010b0706050415050414120909131b 70
    0x40740c140a0103201040009480c4020408000c40d40302062070382000340c40d030400c001984800e8400007080845400810054185a0001d54010441c83e5070503000035071440c2c0d414450036990b0300350350035440b405140381141c1c440c1c02c00ca4520b42d441204000c21940b01d43d4000c1407a40481d004803868500f0108030f10b0b0a10100f64415030303441c209a80100180a9107004060f40007074111011003050318025110016401d1084004041003203001001d81964041c4903800400c00300a0b2000e6040fa03500d00d44003c1030202d0580c44042d500030581145110f09001482003a07603d115400c40c0002101c0109900b296048806264408884214000707441401072042201500c0701d0f40c0d001ca51480140180030032000954442403105104000410014407800155013840e0b030f0154000c40d0b96190b40c1084440460000c1140060300d2800c02448108110002500c143c1e4880380d040d95a10100e5411400c0d140c02050640b9420060000002d0800c0c08206c9440034610b1290640100305401801030448420315 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 684361267 1250 684360017 684360049
    0x221010605031509100806071107270509151006020c030307051917190e030a11060a050408161502010b09070e271005090105030a08030903040305120702040b030d1e0e 73
    0x2703941801c0000c00c40522500b0081c000341c85205072404040f0b202d0003140f42d100c250100d00300d6659800700b81d4003034060100f650501a21005122141018818446050000d00c5171601520441000c4012420007005861802e070300036000c2c00c440c80c400d800da600c0100c0303440003c96415184890004c044030104c4090040a070000c0d800b0000407482243c05840032924142c07403807080c0c0c060086140000d000b41211000c0540940f2083d823210403480c022f49681c0030b640c0161009000d00f01c0d005540701d408096a1040b15940d03804030b5851440c00fa07081c1d00700c6284805080d0010004400110014001c21070110b07880310281000d405001c140c805107a042c0d0500601103070400301001440010f800f1408000050181101d5002035949810006a81d0744201c1c080249258804170001e07091500031b00a40300116041016910140360004c3d07500318a83c804c020880c802c17880e06246800301e041c000f0781c111070760025443d1159820000381e003200c1511900ea410f0030401403040102c00991303d8201d42c0354400e00b1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 684362517 1250 684361267 684361277
    0x9031a010617040209010306110403240b33070506070932120307080c0304091107020d02040f0b041505031b030d21022101060503150910080607 63
    0x10500788000d01c0c00d0307410035200c8540404030b4203001c00341c1d6815580303504480d0310440000b10f90001403500040341c0074940c00134001c00052909010540f40d40c401c40c201c03881e06041c040150440132410098030104621502c88002304c015030300c41602143e280c2c8004042d892502a41c20800c0e203130380312407420404031034071800569140800c00610a00d07980c0041004450100d0a110040f2211101c4941010254151080700305025002603450184100c4141c26009001d283d40c40c680c0c001c50a41c0e82d40030344034003c2c520345020f0746210107032546d9040e58040c5034000c1401c0e8500c0742035020407001d1301e40b071480350301d0341540c500c0c1e2098282d5807071050b551014003400250801d00c0c43c3c41c04050400100a0100c162000c3c4482596080e980119211803004140d04140001c01e2480c60076816549905104280040c400103800096032144042c010103002c2030950180c0c1070307803101d0088585020070303510213004003060320103400c080c0f400c03030b2001e54400107014200da110307981e41310028541041620300c040410 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 684363767 1250 684362517 684362519
    0x3040e1303020d0509031009081204050d0e0f0907030c11030417010b03030309070e0406020d1e1b0206010501121e0203060111070303090608180f0d0f0207180c09031a01 74
    0x103405128140d180c0f40c042c02c0450800000f03402294031b9100420044500c15500d01301502004840c0d0b054600128841d8203500092406103440d40d500e840142500012030400a010380140c40c1801018040c804090080105520780d2882076006c0d00c2c4114105050010880f010154202d080001c0e0008080509043ca80c82c1e605070825801c649000b140e91303001c1d420070410000b900000203030b200304644225214002554560410034024001d00646186007030078058410300070403020042843e07084035050200312100540b90a034a0701580b401402025811407030042003290300804078a80c011444000109028000040500c1c4c4001868405108140e01000340680c55138002c0700341c00510f581ea40240416030950700d001c1c00f036408910a200c1004888000038590a0440c2c3c0f00076a0a42c1420440d00d0030018849541d44801050843d803001a1307191108001440c800106001212a01158000c00100800d4194050110104c480090140d035507800400a00000b12641034410135940c516a29 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 684365017 1250 684363767 684363773
    0xe010317181002340323010e010c09120308010504111b06040606081908030601030f090b010e0c04060c020d0c0b030c030415050f1303140d0203010e06191703040e13 72
    0xc441d100c1e90507005032120401c5100c10040d13009200082e130381c002d0141c2c1c042103c41d4104142e044100190312000f542801080380311210150010a240d10b11501d40b2110552030f5110001e40c0441c42c0005000901c1c0b00004200d41d0515600c14042884106400303442c00c80e452440384070307005d03826006d40d126510035001c02c0140481841001e000e0700c2d084010701034060310100e081000100b071850103800d04000201203041e80c0e02075442038440c003401020621018405042c0703005e500e0350920504180107160300000d00503040c54012102038400c1c64841d41132a050940910400c0f08104404480d800101c07000415002000005140b0900a01e0080e55803403615240504400dd1010359880e4001d06007024008510303806030b80782e580000c501c1070340000034005003821a00356220495160b4071341b80000764640c0d02c0c140768004605880101440f500103460382001d10072550a030040011404130000c0d8144240c2035544100112041d2100c112400d107a120300b00d1032813142d0140d03a45a034803c0711104401c20 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 684366267 1250 684365017 684365053
    0x7080a09020f0108362104060e13140601080708070903030507051212010312031a0108090a0605010b090a0806010b03070809150106030218090c090d03020a050a0b100e010317181002 79
    0x80003421000000c03a02c50101000e81144c0241c1c01040140581c00b0002c0110340c2b21002c801d40003441c0342609000d42412080340c4600d01a0544410b800560107000007030000c0e01809003e030048125071ba48000c214075586049545401c9003004031102d00440300240d0010541c04041c040c5c607010110252417a52540c03800d8203000769040d4149080c5401c002995511442225100c80020003e080041c2d1a030b840611250030050070031001071070f007480c1c100082a180144c202a058111066400608a03601c42d074100b503485109110711030441034100002a00b407807042c03209071740005143d401c881400c00d00e00306c1054140801d802050001c0c0d0b0100c0c0c2c00341e0301114150840d030300000aa403002002c0c14010b4110703d461040c4541e0501840640c441142054401c004080080c0d4102c1705840d0400720303500e02401c0303081c0f080e100202c1c50302085101042c480d8042d14294101ca5001c0072401314608400303c890250b820815406000c10062495001182c4802c0d03e4020f1a00d900c0d400703050ae105020702c001c0301c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 684367517 1250 684366267 684366283
    0xf011d070b0406050a050d050901151a03150d0b16140306100e190b04051212090d03030605120a051204060e0d020f12010507080a09020f010836 63
    0x89990111104110728880602160143d03180c07490000c0e074500203000243c8803481802841040d261809003000001d00d01136000340000ca03890040c00c44182c0e030300c040c0b811408020407114076030207d0402c04202c1000071840b00008003040030b481c0100040164a481550950441e102e21203441c070031034440d00c1203901022008460030100400307811400d02002191002e0200704415045c0507000c41111450f0b95111030b1000c00b03c802000c42c502c015180c3c4004c50f03040e000f51080ca4083c14003c5400c400826002c103110300c140c102444603a00300305072101001150090148180c05143e91130300c0200700c03500d5450001c05004003907c001c1041c1140b600c0c00c40d181c00070f0442d00c2c1d9040034090100340300042d0702003849141c0c0401200c00ca2014981c5000140113609030f0600701d540441c402c0e000c85c40c51b0304190861440b83d00c1c240c031007148640d00c6682200a03101650700003035112201200401556002d078204e141c20424004d0040c80028240c0000504984003072050f07084841d400712007269010080080c61 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 684368767 1250 684367517 684367571
    0x41104091b0f0e2404081605060a022e0c0206040318060207060302070c08030307090f050306041e03090b0d0605040b030d2a1b140a030507060e01020f0f01 68
    0x2a0200c0d45025000b0000f0a6240300c4600c503c0c0f200240e40f08284c1c1c0e1844040301d003418185400d0b03907180d0ba90500b566800d10030701c0480a00202100c001014603003442030310300f400c55580150480071040501814208200a4000030701c42c1141103019840d0000d11844c5040f1b0016002040c030340c1000d09000d044109140d00074002c0a21128013800010390100f13200301141c11030308015803034200782e20344006c010320140c0000c11240310110420140c26131003494002101c006421140c00252210181360b00d8140c1190094624410315030b23180c0300090644982c6000d14000d141402c40c0580f01c920b00315050b03008801104645803211414040d83c503081c402c0c0d41300703614200c0041285941002002d020000880392040040c6500e041000702d81c6140c502074814503034059080418400d01d603141c4020300d806805070315000e44d03c290031072016062094170704d0240d80d00a402131201c6031038980c013101c4400524034040d0440c060000509030b20f0b030080005a501f4601a0000b0500410303000c1200e0b1001d542400f41 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 684370017 1250 684368767 684368777
    0x705060403030c170c0405040903030e0a030c02130e03040b070201051e03012115090c030f06050f061002070e0606070b04080c060610050a08130b091005070306050a09050402041104091b 81
    0x102017900680c800300c0d012900e0542e130124120300b8a00b0203800900d050b11440400c0d006000c03000c800c2652154481d85024802c0b68454060803821100c0c4003110b01c001c100c4030407507004120510210101c0c40c00340842620514040d490320104d4501c8d10703188141d1801301c18030b00c40c0200c0103000001481d0300c41070740c0c0c0d81c0f80740c6103007002004c90302d42c10700310488590242c10340c5580700121401d0011007080c3d0400342d50000400103c2c1009403400030010701c800c80d400941900e04078040303100f0785002254810500540d5004040590500c5125040070001410030b9601540800050300042c442d40c4440d0710441c0a540e905c0d0300c5450b0441d140381459802041103101e954031800140d416038111040c1d1301048000d1820509564400846554500745821302078040c4c07505000f0441d450704009800000c0b0008008184017a4458550a4040c1c5216000e895485044458103018000242d80269403084c0001c0020888a148694000580c0d00031341041d08025125030300302c1842d50f0020420100041c05142c0303 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 684371267 1250 684370017 684370021
    0x601030311030f040909020604050306070509130603080307080a06050d0501060509010605130e09072102040b01050901050f030a0207020d030c0308010501090b0405060702031f0603050c18010501080702030705060403030c17 97
    0x20aa00f140300381d0068201003551000340d1401e6413920f005035030241034040c0c00c032141030402030b1018000d070300110417403445100f40c0031400d04020111300032607048036481840d032030550b00c8500e4140e81c480c400030420300308166a03030800030f40d035582c4101d445c2600f40a01c00005845040006019400c00140c0201041c04003c100c081c5100f5a400a800115104940f08640c41d84601407060304142040e40718402040d1030320880c41aaa101c0010781810034800c5400b00b001c2c0d004000190b4050007a8060240403401c144400b003881c50f4501c0041d5400080a43d0062410186600181501030b8099060300010000c0408004141d0850b05641c0901424200741943c4ca140c840b00c81103170310550190341c3c011100070078600c003151001c1100c45180d44082030000d0782c504201003e41c005103141e1005441c01d1094200103080340c2003689505402c3c0310512022000d80e0f0910006641c1950040c0100c03017103201c10480e41000c244280311f01c0d40142e10a90700424448603607003006244c1c80350800c001d4520004101 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 684372517 1250 684371267 684371287
    0x30601080c070c050d111305040b150d05070b0a020d09050607330f0c1e0809030705011e4736010f06181502060103031103 54
    0x440541c0c00000c0d42100e50b61903195103002141c04070b242c2d1001d6040030141890404211360100da210f6580c1041c1c1d07865a01040c07904450f000e5840503203020301110039180101d0071600c4000a0500d110b50050201c4424074480c0c1da9240c60081e0136402002030303a1003c160401c04a9060152044c20b9416141c43e0b00c0850606001481e01e11a144005040020f95880140300c0d44200c04a001000b03884102500501e15002400c4050500702c42c801c8045480c5c5407029480754050151100d1f08404a54003090300c481d00301c01500c24043c007510011892005100c402c0002c1c009002e60050052544103065440310100c0003041038419500380704030310443c92202c240703a0070300305c03110350740e1107080b40c01d1300403044800703020500106d129448601d4126052098480c140322040c044003100c0740c80e400c811080010381c0107001d0b04069007809846c495582004003049214410a1000f07082008894681c94595071910512071700d013601030345800540c101e0700042003407580064480c424813144001840c54031940311 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 684373767 1250 684372517 684372527
    0x6080f01090203041401020a030603060605041a090c070f060c083904050d2a030f0b090c09010e0402030d05130614070b090721020907030b1305070e03070b030601 71
    0x409400700150340400041d05015144204144080340b00008540e90341a400004020300a1b60009407981c034240807001946007050310800048207081d140002d424201041000320700034003c3e00e008441c0e503080c07190901290003200c0b140c52080c41001c2c00101c2c03100305000906410350042030005401c00c01e09600c10b40640e00241141c1229941500d100d041e10162403004840c05580c01180d04642d5400542d030030001c812800309160b1051140030b42000481310300740c0030760104c280030040c03100200c0b02d0010005040040300c550003540882c161307890300340350f8804241c07040c000340d02803c0039041c91424402503040c1400300d805a850315140c940e02d400451034007115640c0c09442010200140100191a03c1c80007005a41c0c50700e0707115158000c00d0038010111551203205000381c5c0d0300540038a0502e0f084100303180201c901c5540c05003400c400c55aa011082c0c004103101c0a405820040c17000d4928030011440c49468070408054a800484801003800c4c03510b04600c5030000c0485400030000d00c10b0340d82c4c0207 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 684375017 1250 684373767 684373769
    0x601121704032004060b1c05160917011e14130209060d05031315140a09060c0819020106180b210a120c1518020603090f07030b070906080f01 62
    0x1250f0b07200366520303c000802c0050201c0c4d40010401d00021038410301c084503924080403000346e071b058244000d0311a8001c03100e09040a00c0040301243d810702e020800c0400d40f9600d0f00131410b12100008010f43c202c00b0700749922586c80c2c0c8044805a030344480000403062403c070280c0000700320744500000c5001e6404210b42d04405418540300e0000001e05108014040089030075080d905455080343c15034580040000c4014885140c0119600010071081800c145064031000102c0e9503801c400700e0310f00f500a5982104182c401d1b00c070355500b0401150f505440c6000d107400e41e01c8641c00090703400e1401c02400d03041c50080d10b03400c00007400d01d03510640d07941c2c0700075100d5140b458440c0c0003000c0002149100303280c0300d11044000d1020b10070032541d80389960000c0802418602804650041c00e444800041c1211500c080d02c020b2602681e01d01d60150034064080d40e84900120102d901c900805602075191011235481100c000c054007042040841c2c1c40001c40380241403034107003140ca1742490001c1800d030140c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 684376267 1250 684375017 684375053
    0x190c181428090804050a120302100b0105090d0b071202181002011b030b010216060203120c0405030102070c050a12080f0a4109060a050d060503060112170403 69
    0x184012190500c0d0381c1d10645166403507190080010020a00c0d040500f0f03040381c0310f5648101107820001a000c807100c056144017603810780c09005200c52581c1c0700401030100b90b5909041000611102c501c98403000c4003180da041c0586950920340c42d0407480240384001611555180b6401800502600603005100c03190848007140d10304600204e05104074010104a4241c0d0680e80300c1c0c0701015001500341c2c0c00850b24410030b909503880c10600b4041400c403186a4800c800059204004110b20103c070441203603004201480004c1c0b900ea1303144006826030700b04c80e90580b15030420a40030007040c9030041451004cc00b500408400c3c84884c1d4580c401180550112907039a04030014956280300d2142906203002041403400c1c11400c80700c1554100c03602581a2103040b001030803000000c01102c4c11068030450707100241031901d8030015820403161500085002211151100c00c0411250390030302416020740308015814003c00d11606160009044103c10101000340030001880803a01c0660320680d00c1d44 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 684377517 1250 684376267 684376291
    0x181c06020903010b0a0b040608090d08070806130501080102120a0c091a0403060204060306050102010e300409050a2c07060804020d1a0603070518060111190c1814 71
    0x21240082405401d8550b004c41e84003800841c04220070001102403c15600d480e9540300c800c0d903c0021455458078807070021004180c1c04030004150078820355a03da404a03014100d46c0c50044405d07074241c20348038280c00400d8107940128817580b130b0400c2c1824040c2d12104450080c071000da00c034a00685400207600603084807410744102c642081000d03204480041d075000c242155110340d100700050041126015980c011750a0000349a51090001141240541d6401c20b00b0a01203501c0140c251724880007000044840081c03100140075001d61080b280b10b0701c0c14400209000d10310603030290070150a181401c124804c11034004034003100000e42d1344140c55040c149000d0301d440d0b500000708420791407072000700170382c01c6038a400c80040390150929006aa0607001c40b102d064031141000090030800702850b4640550200040c1c0941c0b24604690141443c50207032a0720703030b40303200300d260280800c4503080c0c0e2261090301c4c04000118006c108081a403c0c50f003810403040581720503003414190041c040a003491 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 684378767 1250 684377517 684377527
    0x6090f150c030601051e03061305162102042603040f05010305040606090c0f11030f09133e0c030715060f090b090c0304050d03020c1f02181c0602 64
    0x19008100301c0b0f2210b20180e0b1b070306c9031032006c109240d44154401c60b00305000380411000943c80002e140500d41c090034210040c9142d0f01210301c0102c600790551031304810784041508041104000781e100500103003011002c000045441e2140d03021800d20708014000142e40f00b040204040500b40d46898140ca00928001c1039603201c03410280058156600b00c0e4545602c2d04111440481e04410100065500c40d1602d0143d50f42a0405644a00030301003c1940700300c0400800780e4900e0580f8401d00070000d41c2c40700213081140b586405004c031240305443d0710f030000c414104e803680c20fa14140c64242248041c801e54075020060b40d10541b2400b659000400d4401490089c2c080c0e070080750003541c0070b080c4031070103582030560303c00844003d40881c0d00054024424040032440380c5102d0001c6038030958005004226502c03d0b0380c000c5009600c10900440c4034060046441c80c1030f50b41004141d01610362200c00350316480e0310b2240050100c040400b003071080c41f401c810849021035a4002e03072070464000000503251 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 684380017 1250 684378767 684378769
    0x9090f06030307080a08090601050a0513020702060d11040810020304020a060806030f0607020c011202040302090402130b130e0f0d020601150e040203071e05030105090105091e0906090f150c0306 85
    0x2d801580030041200c000810078103541c65000b01d480707201703101900841d0400d0f44e8400c2800301c40c1305039009142d000b0500b000c3c82c50102545800802e005403002c1c0c811031030256405200300454180002c105010400000d082008041c1001040300f41e91592008526500781703507000a50107281482031006000c01e0800083d0035076024001405001c040c0c0056500f1498044402034603480b8202641c1e0201d030080d600144400c01c10310995003620b038003405051090f1030b50307000c00402940c1340d480148034603150740d10054a0f44031024201c0d0742d8000c8100116108111951030f40c104540303114508840d6000b40c045102d4154009070781411034030445900341042d42891000c841c14542030445503002030001090004040d844099800d50415000c0c80302158909003070211440d1200b84103203548448042e006120f0303480c001040320740050365210b442d544154070303901400c20118103d40d280d801d03420040410490740d40501491024040031005445090908048026400005817110151071400303c0000c4e82 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 684381267 1250 684380017 684380023
    0x8040807020a0e062e142107031404020a26190b0108030307120b0a12030924020615030f10020415030509191506082109090f0603 57
    0x581a0050441c0e10650f8803500b00c010107200550f142e50141d40020380035401099400d03030310070440c95268003074404082c0320316044641c0c0d8079601d110360203020b08004883d00845025030500c01003800d090303142c07028602010050f00f01c0d081c00f400256608941420480160764540d01181070359803155010b12625582044588001010350700700045200e82d10403000f51816180800d81a94485c812001182c0c0e200d600094490005841e18004204640c1ca0300d00b07125503c1d041401c110f400503000c020460b42e20240740400c08013110701640415411101031200800541401c9079401d040c0107200b1741600d6078040256160402440a0392051801c80f0340800390f5010300c1760b81901018081103c0c2e900030030b600980b0007580140300700140400140055102940a8011144900c0407100a030080d0011400380d48030030309511104a0383e1485024150010740081d10601010307080c0000141450344048421000303000441801d0030580300d05120302c180765501c1119090b80031180c08a491900c0e00c0d01c41c08285 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 684382517 1250 684381267 684381277
    0xe010210090819090909030e0907020304031703040807080d0c110c010e0f19081005091b09091c020a0605010e1b0708041511150105090a2016051509070303080408 71
    0xb001e41412001d809052380b001310364040703407411500c0d000d20785c0728800d0a80c0e61b8481c41c400142a801d41c072092880001d1554041c5a216000e110661302c5e0070015501c05070154411689881c0440c1c0e81d0483e50425039006150707544000c00c1100400100080c1c100180541003a204483e21444110304000081d443c3c810182d8149186040001c1e02182c4070480b0741d0711840e1941141480d2481c05d0000340014200186002829180d45180d0f05007050420611060902c01000c900803071003800c460080e80700c001c40107242058515400341ca9450010324103070060301c006a0201080c1000c44090200c070f4030f91041002c1e58a120410400c4e510802407402820074003a0380c0c0514001c00543d100305030060f403c418800c0700103118000f0b403542085128100d0b10100403c0c0545508003074000c3c00552112050b0f441030100800c1c4100d02c400c6020203007003145d601d41c014161000c603848083c0301d81c0204075040040e02d01400194203029098900b140301c1c2075460a1610029040006200214082c4400c3c503080350 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 684383767 1250 684382517 684382529
    0x40c12110d06060c02090a060518090f0d0207050102070f15030207031407030513050d0b0c1305030a0c1e0b0a0f0309080c160501030b01020606040507090807060e01021009081909 78
    0x2000155850f14003511560b2a281e040c0c1c0504400740018000600078810842035807002010600c410822070100786c101c4000805481c0e00380b06202c00030b41c00c0e40c82000386070603800d00340d40100407143c1444002820250194041500e60401c050b0074004062400c440350b8401505d45001078450301e15003000c540c01d083c407140304070384210b00180100c24940d0042c010700700703080b61051040d00c440c3d4a4082c8102120a040d010741408410400b10300c0408941d0b006182402d151200f20b90a00d4039600024107042100c4000c4400c540d040d8010810200080100c42d80e11300214000e00d40c840c50041604130302d114210348001040310340054148280c3c02036000f03950341030700900450f455040201e16560350b0801112884046242044000703100c1d07120f4014a0b001e010180d010309150b444203810b11002e04000303000c840c1400a41308020a500002300702000c02051107689085d5012241000a820001c08400c801e89890411003c400856028002c4901c100c04034100340400708900c400851307504000e034100e0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 684385017 1250 684383767 684383771
    0x3090a080301171c0806010e060f041e05120a080304030201060b0408010c0215060d0b06030a02040c0801140a0501090314100c050d050130031e031a040c12110d 70
    0x400c2548030001403240000c1600121342e10b03a00000c0c030103a0480c0184810000003014a000a0241e51040404c081241400b90441e41054001c3d07400d41869013098010181414110070b11400c1202410036034801028250b805020f00091195541c0d11001070640c040c01403403002010a04040c030135480305004080c1c00e1000707922540c441400a0191803000d200c100144680440b03070400c0348054603650702a0a0017000d20303e0003c056a01d4080d551401450307154580509101d03138000d601d0328000c2c04001d0040765980b140035814089240c402d00d04500c0b505000c1d00340c1d0002404a660040002c10035203804c40807004049100b0b100a502e081c03240781d900700030340d81400460041c003908030b400b0b0600451071200a00c46a0f0700c401a1001c08214081450134400280307a0b20300660103c10014080c0500a00d88407110980090882402250309114030002a544124102081c94000305801c2c400004075420300c20141c41ea1030092040d8008a08800e101c0d5580344106c251240035011292045146501 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 684386267 1250 684385017 684385019
    0xb0a02070b1b070f05030f07140409081201060804020a06030905060403110a17031008030720010c1e030e0108040f1b180b0a08120403030f03021b010911100c0803090a080301 76
    0x101341900b00a031040902a00c1000708410f280c036000b00b645000c0d1500300e40e13080f070003030000001c0002401c1581c409480404040245c8546c40c40d850003120301078200358460321414101441400340034605076110071b04240c54107250328005000072030001e40054040c6040c5051011011700d00d801e064204070018155140c14240c0f880c0300e08040d01541c030480185d074408072034955444040da180e04c070b5420002d2602e10400c8000000c2c07003042c04a0401c0e8403040c074080301d480d40160f890680e41201881c0140c4080e1450351503004260340030502e480009020701e070280303a90500783d40381c2e10b43e84074810300204846941e03019042c2c1d90048407110002041d0b1641c0090200c40303c0f01980004100c241d00c1d0382c1c0225112100070070b50260001d1407a0403505903101d9245440c1c40d6032022a000f28003018000d00705602003209041c0d01000701c988208000c40302c80002501d07000351800517004c0a0091540740a072081d8a5010019500065000d110f80e4014421603601d503604040315040138100d5100030048480400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 684387517 1250 684386267 684386279
    0x1204082106030c0411030a020d060e01080304090513020d1211150906100302060a030515060408031c06050312090607060c2006010b0901110f0118020a0b0a02070b1b07 73
    0x2a4890180307406a059403d80b0061000707000582e0240c0705032404010b401c10101e240c3c00165801880b1508540400065594540015000d204000c0e88560b03101d070f01c08a410b005441592040f03523000000105030300403400d1a070380411507490300d2040141152480d052030070300040c06442c00d62420f510740340940304415a0052040e603000000d54480009109110005404c0003495220341d06480d00203200310b0070800f181c04124080d150040210880c0c1200f0040360105440b00c80c0604094031000c000b0b90f448441d0912508080f014076071440900c0b45c1084070820841d100451282c80701d010b035175071540d500c1006001140e414810454010003040c50603982015450340034007107040e5954915411840b90301c02d0b840481e9555020300450002d48002c1007103204075070061010b240c2c0d8480d040e013510540108c80b10a10308407150155210b0a84145c20031280843c9400103100d0090403202040a082030041e103070096946110f801941c0e0102c2c000150f86000400c41d50f440100d01c1c030f07400101c8682c1d07500c606c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 684388767 1250 684387517 684387577
    0x3030307030906060807240201110a120f0b0609100e090a052a0901210501150311070b13080705100b090a0b0906091801141b0f120408 59
    0x4058543e24640708003c5071120000c607203041190a90f03038030325440c524070301c202c4d00c4071907111610101559030350f04182c40d1881c00394015103100c500d5a214606020007000e0008169424130412496007807408482104c00d0342c1310340580f16124400d0300c0c80044002d80c0b900545030340b600352003040e91001580040024409207500308600c0340c00e07284403802032417540520040ca03500410400310341c0e0703503001d01ca9000b07554415041042d4900c228150f0040b90b03c0c18680f082c0442d40c00b07030014007280c00d42c01c00020400b9014082c50690180b0710400d149841219110725141c201e01511246c51007201d2086030303081c065075500341e800180c0c201c030640f9103030541046114020039001d510345010f0880f000002c3e02c00701c0988a0703800b8180d0060714000440c1c1c0c0e03010403c50704ad600180b21847d41d800c01d110030704c0840c44c02d100300c403082032103242a000380d410060b040304072006154469007003c0c00200085840c050070300080d80c10f860500f804440e0551603500c1c0001c8203010302407110100d04800010401900225 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 684390017 1250 684388767 684388781
    0x4020c0c040c0906081b0f070f03090b0c0601090c030b100903020a05221113080a1a07020d0c08040e0f1e28020409140a0c031b0f0c020303030703 64
    0x4890400040300c0310750043d03843d80c09621402c070102e80c5031400503015808840b100138521012440291038590381101d00610b0780c00443c000d4400c0b11280000b481056003220001021302810b100c01401c0c00b003c080c1a60b501c0b0b0701405103034081600c40115680303d40c02600164400e400007012241c00c500c1034080140315007054441a4441d01c0011000986411300c1d0b1148001580e1010000e41e1a519000301400544808000d005000c1c0e000c000d1040c0490b00141640080e05080004d131110001c0380c01d11a00106121341400c0310801220117020303032142c0000b0100700782d42c4542440038164065080c4486d02d4050361380424228803a440c08c110328484078026241c400c817190040c0520750800307048900c2c00c01d101154607810001301464080b10309148160f210180c4050240054900b9031205600d0b02995411041e1106049181051140111003409100c0b202841442c1c108080d41c0e00c1000300840024454404043c440c04000c2c48107004d20443d5a481c40b150060b084950341c2c104042e00600030b02035 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 684391267 1250 684390017 684390019
    0x41b050705060604180303022a031b0303070905010c050709060b04380d02040305010e0a020909190311011506050405030706050c100b060c011113060314010303080a0b04020c0c 77
    0x4010019080d1302d0980b06206040c004500c0d6003851000a960580c001d601a001944650031b114402d41e42d000015400c0d5051502d07020065a2105150b82060030034142d45001c403801900240100252550702c50301c5401203171000d01c3c0040c0980301e9401c03c49d060038469005018114103145021414402c240002e004599202000900f000a10a400560011841c100c5031200d0018050100807070064005000c00000042e00140741551ba40e9409084520f0024100201c0e0000c61b01c1c001545030018078127600116100c06015104080302007152108181c0e580201880800c210742c1003445000d502c0702c0080001c4803801c000c2c141d22181d01800a4005104240c0b192007481c3c0c01080c070611940540b0400c5400c8001070a02c00010a4084d002e8500303000c003140c00240c10712030340c100f45809019804e520482081e81710740c0e52819000113043c400311a0000004d05040c03000b000c0c41221400a07003030442c0d403d4a00310540d42c0340d507901d1300043d02c518114980d101d40081441d0000110119500c5041a4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 684392517 1250 684391267 684391273
    0x90f060c0d151e05060421030516062009030a112d0a050603010e0703110705030a0e090109090c170c0d0b072a170903070e0109060e131113050a0f0501050a120f02041b050705 76
    0x104070021400381c42450b009033b4158004071840c1000038011a001000b500e0010300f0451280301c0070700030002a8503c00c0711446605104841042039050200c14071000d0541556442e20350741c102241c81c000c403207010b41190101641c406440c44c0101c0d0701c00c1602c0903941d00c081680d40d10301e29990010045581c00010a105520010001130a81388a101c1c0201d903550000d01390751990720f40310380c2072488a0040401002c40c0100e00e45101e1660707440c044824403600c910421141420034040040c05582c00001c070740c2c003024440700c2166400000e104072003d40303a803050b070440d10b10048040089190140240941c3c051140c0040881c104600001841c1038a13503491040040e10744d00d0003404c282c03d5056403281041858078400300c0204840f070b001ca00fa01c00c40a8502c41c1c4c4a07001d13952140840b030080320550201c03951a0005a819442070250358010181194801461030800c80405030000c042c100003880403410f801c0603c2107481d00d0300000c000008085041002901100d00136010394040401190640 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 684393767 1250 684392517 684392561
    0xe01030809010f44090f011a0d021909050703060303021005070f0c050106260d0207030213021602030a06090b090f060c0d151e0506042103051606 64
    0x340c41340395401681202602d03040070014444190094925801d40804600c008501e20307290007500b0a481540070781e4155004204403110910041e0031944190341e80c0c03500350031801c41c6180591f0703864144210150119003000c010301500c0702513900103c041c0e000900e424100800c02811503055032145040700e009400fa11140760b844407100c82141d01c11034542c0c010503860310103a903084e41304c1c107542d03500d03180f00781300001d049511594440007035403040c594007043c415406051400103006010140c5009000c0c002071a405085a000035140d640c414100030281d6408103c00d0203014031000b0185c0901d8002c0c06407034054100341005400340813403020aa6018281da00410100711000410004c0c820128000e00241e88407010140a42c0c0d000c10544c501c40d9854400d210328904442c1040402800300488850501c0d01c0003c5050001074242d0250744510010702c010003840399650240e10040000c03011012201e00c0780c0c5000c0d1014001d0b0a80070a184100000780e42c20013519030700080c5504c01d1000304203006c07 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 684395017 1250 684393767 684393797
    0x121002040f0905040b040b07140c0a111008010e10050405010806150d08040501050333030d02070b0403020f030304030c091a0a08030702100212070506190203060612040c0e0103080901 80
    0x20b0390043d107001740b81070000e00000d03020070064890981c01c10b0300e9150038014407040c0c40c00c0c210a500200610145500190448030400000c00c050903c0b207102500d200f04503640d45a8054902d102c144100104c0340f48a10001e140124159145401303014001c10820881d611108503030f5492004440342c01c51456400150b41c03a614080c4a04c8004c164001c070350700e1902e4200801110b2a070009000b014185d40303804812103d03d07006284002d64034a1107441d05501d000404205460445a6580d840654202c03250610001640030700712415290142c3d4022180c1002202291451003280e0000e40540c00c40032010841000301d4000c001a80800520081c641d541c0f0000c22004403001e105035441c07a44104818001810400c403200c10301a901e00507522040368604800c5030ba03a108000860309500880104680300600781910006d40603ca1030450a5161400100310b02d8812180000781040d900000a0204101000440b025000c04603118625507900c0c44d00310320940003443c40ca8003203120300d0008290 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 684396267 1250 684395017 684395021
    0x10c121d030403111305090f1006120b09031e1306022a0a030507140307080604020a033e01020f0a0c180f0c050325021506121002040f09 60
    0x11004900000c1d619003481d60ba920800c020380d0484c1542c10200c5030040341e032580300e1417095038400c1d40c1e680c020340303ea00d2004001c94107040c001c08261800502e00701c800d0028030741440c0d4941c0043c0c1c0c048100030160300c4031400c3e246540240c5600ba1f941c01d06103805410718464503c05007280d8020640c0c0c0301030307154480400360b1b01c6100401440c00031000301406545156403002c5520164074019048c3ea21281e10390300c9031400c09410f0341250340404024100094203003010403440d4000e0a4032800b622880c2882c3c2c4c0001d100207410f11000c2e1416680c0501110403800c41004018419000c620094a11109004030400404032403405809030040c5010203c600a0104044045a5204104c0c904190030250035400c1400741d0480c48404c0782d551007004085044038840d41c0081c03441c03902c92540703d01d070005000c4101c680403092001c4c42c92940d2003903200c640e00040d42c0b01c040e00b244941c0d0340c3c440c1e9030032000c200f8895525000c605188210040d0703208040244e4020410745003240040c0001a4540c003003130341 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 684397517 1250 684396267 684396311
    0xa08300106080601210c0f1404030b0c1b01090f0b0903090102072313050132040911100c120903030c020d06110301090209010306060809030d0c020f010c12 68
    0x702040903034000488640c841d02c2c090200c02500c400c8642d1000255800d04110b45640c07410401140000483c8619580c010b4100603d803104114403515050940d0b03520411043c014122520005011803480c0229004418a20f031078036040c4000c1140011900306041d00e644c02e540181c94188950f8017140b41a24040100d600134003041c1c004000b20781c41c20b4221407009181909040ca541d924114201060380c40c44040c02c1000d600c054040388550500484d90080e8110f6110003048071450b48101c2c0e0704240c0060300c6038403040200d60024100c07a190500c00d10f018415256641c2c0918441d03181d582c103a4101d140380c10ba180c007800c00c10704030b89150081561680e00e5400301070003180c1d013240303400014541090000c01c0d8910503c80810030142e003420000c1c0540080c1c0003a044150082820300c4156030500c1110000e0884c0e18160900e410642c80301501c91080c0003064103425103685910022500070403c22000c190f101c8001c0010000d6004018007214540f028000140d040034400c600712241413408203 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 684398767 1250 684397517 684397529
    0x702010f0f02100e0307051b0a03062423100c0803180d110c010507080d1a15042d0e07180314161a0703020a083001 51
    0x540c40c049001640c2038010381510304114820030400c00040a407900482201d404c0b40001580c40d8501864000d05040503d0561303081d05e11030840c42c070200eaa41d8034682044941060000030a80c11001d00881e52001221010100e4448040c00007490512818000c41080c0070110040007080c08100b000b8102e03002c3c00084000901e0a102d0f10042a403841c02180c000650700c3c1040800c100c094441410040d0103908c0c0030101b0311000b00c11601c0c640a1002082c010302c01d18025141c005555241540b80c01000760003403003103507a04058240d50455160401d0390350401010702c04c141032810451082580300380250001c901e90a107080c000903015020f100204903d040e02008010b0604c00301403098070009040d5800c1080b03c42000345a40d084004030405140205140b1807244600405140f40c44510742200d0300b40d07038140c24100900b4443d150031840306055560000c1d582c01c200d0504a03d401c00c040800341140710002640b03c81034180241d0204080340f07240390700305001c4203000081c102e92024400c00c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 684400017 1250 684398767 684398777
    0x2010315080c0f01050910050406080a0b22231602010e300715110309100f06050a09060303020712032f03180a0906060507060203100e09010902090705070201 69
    0x4166903c0c02c1441d80071040010b151140c03c007000d9400080d40304900c403d5a60105100040500409520064081d4844034100c02030203a11840c90104003000d00d4001d940c04598080300c030191f20300030103400031a5064002500076501441503044914082030a480041920700f180d041180500d0043c0515080301d0380d000b000c0c125040c143c0c0380c0c1444c90b11040b110844124611540505107011342d401810a0b00d0080e42410701c41e48582c11070b86e0071640f00ca0a003c0942030144108452280001880344403041041c3c00443d202080c0c5185002800641c0c0007664807007050000802d14545580c032082c00c8034001c0e070840e0b51003603660b600b4442006020380b0280001d070844403420f00e41a0704120300c03c82c0d154080f904649412003259214250780040d03580d03440d10701900800111514000f03134a10094841702d0b10800405240500140451140b4800100101c1c3c01100060802d4092103c190041c80d40034500301c01440d00c43c1200b40200f085c1e00040340b1641c441c8000c41c15061060084e00c0c081581a110 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 684401267 1250 684400017 684400033
    0x11e081f09151a010f0e131803081509040f120908010609141308030115021e031902060118150302040207083001291603020c0612060121180201031508 66
    0x1d0211101403800f107e1844d6481c2c41c680681c0c1038000e140ea00000e4007943e40c00c490381c1800e201070040060111106442131007643c062001107138034080c00c0c4810740d5211440c0b0008aa03404020358211041e0791115000754a441c000003142d000d2500400b20703010400c101030450b0364842460b21000da003440340c007810070f0005100500001e0000b11080c42c2e0140c2070300440b1044c0030031320a96145091403102025060b040840e03c1c1003920b1040000161040720760014101f1581003414641c0324082c2150f980b20800e0f1030300070a02c084840102940080c64002c1d00c25545c0300760300e062002d8194400e0342d108500c010a80e0380b4554a440c248005103050144c800311500761f9191a028503a8244481346490102183c0880c501201d0415002007914851114064400f03461908001e800e1221345050340340540c40802100354181003d01601c2e07030280d001d00f41040f031081140100020012180c0c2846111441c00080c2d09003100031952400d4024800d0380e041c461aa804011502c00002905c80c0d0b0000e03a20001c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 684402517 1250 684401267 684401269
    0x50a092301140f0a0c1101020a0b0a02070f080a170f0115030c1803060b0a051c0201030c020a321b061c060b03011e081f09151a010f0e 59
    0xb414458150700b0345003814403040403070180f495401002d5041c0071481240842d420480015810900d00c2d20034000b400c040c0704c090b12401c0c1c0c01580207016040b02540003a140b4100003505c5c0c8a0900c1c80e4111421a48540c10300318094030561b4185c03101c03100e501417440041c000c040c605140d181a14040b0400c030105012114041d000341030b40244c0030040c401c60300c1200400b9210071034104002d5009000103d08092803805018000300c0e42d41010b4050a20304401e181000c0c90360700541c521550a02c1c0014403510b030a48200c5c20118161b03401001e15460703d03002c41c40303c0c038401c008003041c0b051154014a8071451440c825a1401050000e40d0921042080c00740b691824201400004400300b142e2000c0800d103e444070b0444d03200d034000f850700010101c01070042d40c1d83d98604501c130004000d200c0301c00c1750401c8440d954540c0b080d1880390701c040380d4640624001155030042140c440d440513126160310f0708001c040c009002c588200703440d1081c4850b100290396114400d464070701080c0b07844004404d94040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 684403767 1250 684402517 684402527
    0xc02060d020d150e09070623120c0705060c041203031d01020d0212010603090206070f02060f0c0c2e030e16030c0929130b0a06050a092301 61
    0x203000c01040d800d000100425215004a502e2980c140c816045580d080051300801d0200151a060007540f2081080c0a440c2d005603091118512000151400b140421196120740c418418101c8000e1021020320a0700b1003d60b01074818140315100351000b940e60184401d2540c0242e208000c500c04440c401000440e02a07480307091402c2214404182c00744c2c180b21040d00303980c413518410900e1540016840c0020a080074254090484c80c07409100781003071500081d08a011f0068080d20502290181204660b11174007122241800c040005444e04006555203483e4580070030003500441c41069001d5100000e00c68500070b254880e4004040e03199034000032002000e0014000c002840f0380740300045403804800c1c07510f008510601e810a04241000a15829545a0a04800c0c0d09031076501001440c40410309229401d08285c95101030101d402c01c1c8600500360311000541c002600c61400714202da4802c0003070610645a0700d560b40f0b041d64580c07002044610310501c0038024001e1144004580d0300c20 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 684405017 1250 684403767 684403777
    0xe010302030907152006060f010f0c06090807120804120c0510020309030318030910050306010c0209040b15090105090103020603130602030f010f0801020c100e010f020c0c03010b0a060c0206 83
    0x3031400c6603c2d268444203200b82c60007020a5001c0030408a401c008240e141a022400b00c00901030003904440c1043c10200d2950001841c2c1c050500400c1d210700304c00140300d40c03401c84d05290411410300088203503040c0240d16910894040d15101481d82c2c5000c08076020f540d03414010340e404803000c0070860469904540e85540302c2c50882d1107010390b032551425410503002a501541407240699945e00300950382138401c51041398039101503001072040e20304680e19084000006502c80c105070366243d80b03100c0122a100340015000398000d03404014030042c80326a406807813089400c49001c425544c5071100f00301542c002440340c3c50f40008072400503c01414680051504801d01020005c5035050b150342d80c0003039800132558001d8415000e0010041900840c90800007406150000c52170900f52003211522a07100d98011001c1580340d40821107000c000f544a000346080100c81152504c03039107030f50b0b82e4640400041c0c2034400e60030b00d1044406850030310342c844201c130407070303281e85140c0c0b240381d42880529041 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 684406267 1250 684405017 684405031
    0x102031c0510030b0c0d061e06031a03030a0e09130b010504090807140a02030601230d0507090f0207060f051e040305090a080d02010e0d090612061203080f07050702010e01030203 78
    0x302c40000000c4c81c0c01e008103016180740502c0c07684074903114182c50115040d136845901c0132074240b1441d2084880036154002564040d240216000040704224542d510340241d00540611000405a001e0b6030301070540629a24200c0f00f51440383c9400075800340100e06184050440e40e2003000404c440c0c130305584060f0440348500e0409007011200e440f080f2980714128a06a00c60308810030fa2001c40c64144141400350040700c03d0f00514034200d400100e0344c031004540742c1d8000c031400290700040c08800c001100c002c0011090502150000c1f0b840a406501302010494441c0d0401e001244484e1283c0644d61040c60200f6014045207010010102c01000140c015801c0c080304100369440c984410a50402a24000004000914001c20020f086403a22024400c090700321614480c1159030002e11002190054a030101c0c200d0082c0404000a01c440e078403d0030f82d01d148e0340e500c604041c3c0003101e60b84120240070a92034a603036040000d4642d84207494009000400b45c0a206004d98081e501464010302 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 684407517 1250 684406267 684406291
    0x150f08030412111807030e060f04030c020102070902031501140703020a02130f0f0c1101050121032604030f09050f040203090a0204050406020d200a050705030c060a090b060102031c05 80
    0x1251400b140000821340e16200ca8111030740208103041d6014000c0048000e0f0101c01842c0e40d20341003800030011100a0402420010403e070f00c01e055a20030010030300600343d0124110364074100704003820620201c0400f00c03404191584204145080d030b000c1a15a025016009008045003070b500b0017104940745601d01c4c000e60381d81c2e84010340c860000e10613007100e180000300000f1040741c4244003a000e1400c1d070a80b9540343e0b060000500950480301c00108408503048a440f824098078902901c0c00451039820044a21003c08180341c4070b10108200c138002c901944a013080e421848500302c6811500d4091660020031541c2d94210a041a42c000e41d03105c420782041c0e0f1001900341e0300083c02d0713401c25282990510b402090610141c06c8600c503808001e268650b42d00702c103109810900300c1c03e0103294660f40c10701c138021504600380b0200340102c407401144c410a6920900d0602d82034001015488401c3c0c0b0802d10380d07000200c00d9400001219030308201c854510341c42007c445541c60181100801d4900c01032 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 684408767 1250 684407517 684407543
    0x1908090f0f15130602040308070308150f09061c0c0f300f0b070909060b070b0c030a02160804080115051e0f310203191a090a150f08030412 61
    0x50744c1072014101552007100703095070300c2c001420000c00918002d0180a01e0b001038001481055032038184c40a42c05c2c000f80c80841488c1c2d18280000c2080c048401c42c0500703849040e99036810405681806000e40b6000220746843c142c40b6900380d03100e41c000d80420b4900308524400202400c0d1001600742c1001c2c440d02020504000769074070b084c50000c0c1900c2a0f404200030717540502268030907018410251a11184507414501c0c580c40300341804101802c0340324034200c000007040800ca40e9030111207201d2400d050210303c822062503c00d2403940076200d2080154a0f000b55901008615441c9004466008001c039040a5140300302946406182000507844403180d20a0019a00e41c42040340c5c003c034001280312094158650121082c0f954811245c41c9035104004000c0c044002c034400380144120541c00144946129048200c40c4001020080e445101101001840302c00e030f1704060031040c5050300036400751386e440e085e000da800920b01980700d40340c000340418010301c9034400c1454190742c0141c22031440300b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 684410017 1250 684408767 684408773
    0x1050d050c13030303140a180b0c07080418050f13020f011101060909020f0d0b180a0c2c040c151803060603050d02070b070210051908090f0f1513 64
    0x211070143d00407404a03484580182c0c1c4003000e07460140d03120b0a1075005020901da100c41301c000802c600c2c3d400800560450011802c02c3c1000e10a0310310650f800508142e445864900543c1c0c00d040700641c00a49500302000a1803490024908078061400e9a0819440780c0b00d0390300304011040102c030040d040200b500c1c41d9915860f02401003000416118100148810040c014000f140d0849030081c0e000f04c0f11068100e0000313840042c215401742140b0f400b4455140c030700e0350380380c204204110042c001e1511150040340b118100b64001e20708640f450800c00011024013090051044200d42c064000740f810074003045880c1e03221109080340703074071850b1042411042200b130b198226429003060350001d64418040c400c20000b00010404130f0804e0000b0000c551400d81c00c6e403000e10507904024040d480d407145090401d40140140c80c6404181d007104d0f199140740c408020301e80d9004462800d030b1071003941e01101060401003072283c560038150002c1c0440107188481800b403800060141140012400c1444001c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 684411267 1250 684410017 684410047
    0x31b090408210a050105180417071b03050601050a08010c1211133804121a0f16050403030e0f01020703080f030f0a06080a02010e03071208040305060a02030601050d050c 74
    0x11a2250f0100058035505120034444650072170041d1404000c13084e000c0c0000324849401584400000c100143e0395020305160880030068080712034106010460004070411802081c2030741070b55816581d000300c05685118050036980700804410209010750800c81d288000e03608284d14401d04222583d28000d20a800ca2415000544c45142404180c0701084103041e080030b074220306c0f011410300704110101050092540381c41188102242e100c40e038509101007000e984841d510840100e01c1401152900b48118200c5035000c403020f01d94650228a82e4401c3e9000b80183c81c1600d0b003698031150390814010601042c0d860060015042d071040020000004142c0e07402444000d584250036038030390400d1280c2003040d400c054140e0441c0c2c1d0404c8410700c022a000282c1c840342580928061089031039590110b824031166800c00c0d0100510000801c040c4400180144200d82c8070328100d6a403641c40c001c402c0120301055a0560004030200914401e44041d50800c94210901c0b4920038680000c5040000f0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 684412517 1250 684411267 684411271
    0x304110a180b10050a021f06030b0a09030e01030606050a0e03030f042c040312020a090b041d10050d0807141506100903121b0c03030509031b09040821 66
    0x1001c281c03180d101c0000307400c20b200140154140350901500300040703014003035191080880c1814aa034503a00706c0001c8140c458020070011034000d44100c1003401e00d900110301a0490071415004290413015a03103655110f845040c1c2250030b00c4c1c1d07640f404c03c4807060045682d108540502135051009200450b01030070b607040104010304502e45401c941c0615031412a0350b1440c1d41e041d600100b100c85d000c00001c00e030050040d42c4003045483c1d00585d60706500c0c500b5240064240c002c1c001d5503a0120b800304000010b8010304203000205a01084181e071a8425210701c0007040c021140c001180d0507054001801004c00f61503840e1207003d8403111002c0002070580303011035100847e54802d07082030600a041c1044006e0403031415140c41c1c4040341a0039621040b8090707c1c406510380400070086005c8503400c2d219005000916801250070308002e0352420014241d800400240b8406c0c01a460708010307d0740d80760050070308100b010300300b49059603403520703a540f01c0e80104a503d4139400700204110b602501120300ba40c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 684413767 1250 684412517 684412559
    0x51c08030114120c030304030f0f050f061e0c090103020a140a080402040f090f0206090a120605010806010b07030f1d0405040f03030b0f060306090c0705030a03050115050f0304110a 79
    0x34803801074003020031100c0b500350400f071400c680196011003078070386010003124103481c0c000b68010904440c07841e100340352103d020b10242c55406100400b55030b408011500c140609910481e44000884442d101c07401c07c481941c281804010400c00c1141650082c0c016260708551030610040c03d4040c1b82c40c0504546c0b02803c03080018040701d0400c02185030078403c4403d40800c0e000b0401c50019540e0700c0b0340c1c17640c82c031282c0030344101404035014007a6600c218070342010f089402c01007030440b0028074001001e010280504c09182c0034080002c590300c60000c0c03da45c141c90305956001c081e0070050384140e890340000040740350b00c0c0b6032002c03203580c035520303103000301c50255200b042501d1600d034280c00d0080884a11010b21481030380040c10800030b50b03895034140c0f5001002250502410f8981c1a0100803d01c0740150080040c000032541003403464151b40f11038100c40c600755003100704100009085a4a118207401844003800a00c0454007041c211800348203000000b4000b908419111001e40e4102c04103001d40d2303 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 684415017 1250 684413767 684413789
    0x30a0f023a1112030403030f0b0d111309060e0d0c020108011505040515090a08010218060c01140c041d0402100e0d060e010c0207050402040302031509100c0807080916051c080301 78
    0x700080547c140710310f00c4021310402c41008940e00500c0010800b500e24030000d0b01403d070b820b0503072040f941d50343d02e00d28250600356420044152039113481030242a5540e0040042d0113042d01b10800c20703002c0e00c0614203241c1d050b0f403029620307070030312800019404c040000306080040600c804541622095284600e00a840d0030654a981c1d9440811190a05980043c0160390051140a190804151025002d40402c13a003007900c80700810045401421141107955040c01080c0038090503804e04802001500c0030400903100e01400341c45494580b000540d4025044189888800041c07031091900c0b8051900062200f03121003142d44a41003918480540641644d5440018102e9260100200c1000740001e031020f60402d071035a00069141d030b0002941002e8100d041c00054a9120107101d10952411481e00821111f441444010501142112944082694107010815664000500404826449805002e40c60510050064803111000907040c0d00f46412150b90001d40520080c60103491301da034003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 684416267 1250 684415017 684415021
    0x4061203050309010b310e030901050903030c0a08031f031502220303050d0b010309051c0207090501030f030e04050609011e030b09151605030a0b0f03030a0f023a111203 74
    0x11b000c2841d00c51a141010500d0314054003000fa1000c81603840821090a015403101ca250000c41d08502c03c1101c1822503000302100b1008100d444405180601d5421403005954150880800030504990002603c40e001c0c2c902c1181c000121900100004040c15541c0c0c0d102507080341c0f15020290b8550011004110301140d51510309249200f0541205406d00c1d09211000c069125142c4845010000d414141c0301c5074030180d03900f0300801103c801000340080400040d0b03034a060052030810382c1801100003c1c103120b0101e5441c5001d005041c020403000703083d100c15905c0c0c5014021030300507024003550080c00d40c000000109801d2001c0520902c0c000000c1c0401440711410254071440040001c0c080314812044071003041e074008256984164407140001c0c001c81c01c440010020900e04d0034284c1d052200294640d076050740b14110042d6101142c0898484d40c051101e41060030100c122422403805000028810016a400020140040d1420002246000d0b50102420302002c05110b449071800001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 684417517 1250 684416267 684416329
    0x8090405071220030606030a021909050906090f18013801022406030c060a0e4e0d08040c120c050d14010e070603060504061203050309010b 61
    0x149080d407843d14074100300202d011260b82c11460101a000500a40e004000102c6e400826812184860400054540da1804500f0002c0100d071190007503a00035203a800c0440c20604020200394000c0c045034078108225036034042e122540c04003486840c0d0840d900c0715003840c8001c0d0312980d100c440f441e001c508072101d01c506d400300500d85e002c0818020b0441d44100b0f2007060344030b4510b1006025400c448507104081d11b41d00c0c0003d2030001c2c4804813540c001400070303043d24000d8102c41c0380289180c040e100f00c00d01c144013084d00c406902200184947c805184681c1544c0410344850b20030400000004010302100b0305050305117031540301c0d0000004210903005004c18400c0014003580100184100f840c007048165a51080e00403061040900902c1d9000b1411304000e854101004800d1b00003000308054091008003960340c108a11408000c00d02d03222022500341018010030051300d030310070300b42c042c12403030b5540485440c0e00048c1340c40c0842d540d4002480c599a02c14094607560209400e0317080200441103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 684418767 1250 684417517 684417521
    0xc16021504080f2107050106031212050901060b0d0207030302070b010b03041a0c16050a1b0906060c1a06010c1b0314011803180e09010e010e061e04080904050712 71
    0x38503d5160364040060380741c1c0e8200380c00130901050810040e00340c0701c40051402d54090131081e08010101165080f80c05a41035100ba000e01d0440710405091145c0d44961186900300c80340d41c001e002100b2410400c00711030885680051000c5403282c0340042c81c001c095240d03009001402c1e000198002000400e01c02400203a0080c41203070b01803c1c4880c001070510140c4da000910400c02c0014200c0024403080c1c0520909018030404079030400006900940301c001d846180200c0ca0140102c0300c2d281203000303d8071520614690075510b920115401134640714420081d50124010324080c100407613030500500240d610180402c4400302041407019207815488c2010310400340902141c001c0e0314000c10751034400391070300d8030307440458150521000191103070105590a890a07000002c000c04a0b2084c4034000b201580618001c060210007045900040640941c8805059898208200b45a285900720f4100080c0702c0d074006208001c403514001040d0081000c2d210100d8144022820406644902e00c6644c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 684420017 1250 684418767 684418783
    0x501031b050604120204090303090807060b010201060b07050a060e03090a06121a09041103030d021b0c040c081618061d040e21040515030a060e0c030c1602150408 71
    0x1200c080f814242400003d214603420b181019111350f44a606010500d4003a6215a001c0358100481c00d07641d140324140900984200d002544c010b44ca894000106140e141c0c096500050340135001e0480c00c01e06880702c0d40a0011480c0c4042e05000420070203240782e403402c07000030082540740c40b034820713040107000b8540840b2050014041440280f140c8220300f40c0d2610003241c0e2003540320159526110244010900c1c600452206000303039032001884140341400d101000514a071118201c41401104100384403d40e002440601d0100e00144c002c1040c3c2820700080076080c0f40c0301e140002c0b5805079600d02e001741c0c81150340315101062151746040c2c58250100c7c150800004185c405000d04e20402c0c10407640c1e0981c0c1c0b10012692203d10b115402030014610482d00188002009043c3e0814140c11b807003001d80c401e450b5046064030f01400004d00360654400e81d4840ca84030902e46085955225240c15558001d140c81d2000401c00c0702c800b0300503070307600ea00603001c0c19a019420b500c807400d04007140e00e41149 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 684421267 1250 684420017 684420019
    0x607110f1804031701030c0303111e070810152304020415031a030d0f030e07030506010e07021603020d03021606080601030f0b0303040308091503150a05120a0201030e030d0501031b05 80
    0x4d400c0180041140c2259000c100c0c0c1d85072030005406001148018240f414411704000707903e61b001450f10030120300003440f100351000d54055072110a00103110500300c640c00038410305c070850000410010780d0780700d85054500381c0740c446102d4112040140084c040b61300c160030400156100300309006030a9451701c00c1111701c01e10484800980b07541c41002a45d20021041c2d52010411802421048184282c006001450404003181c0e500380d12880e019803500024000c8080940c44400000d008520005008180c000e40c000046041c60844d001e1111491100000781c1c20341c0711301544407802071400c2800c07400030080f80e42c81103580c0c101800010183c41e00c1d0401c1ca1003003414412070000590b0088121400c8030789c00041c0d20340d0b420720080400c0d0484400000022500c001004010480e80504090740ca00c2c0b03802c6070f4607026a501c4e0f10800140c0061189020802d9005000000040d40a035012680740b801c80400c5a003448095458641651001d800446035100c1402254035a040d001c0107140c00341c04 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 684422517 1250 684421267 684421307
    0x312060613030b0703061205070e0f0f040b132f040e06060d030c05030c03041412060718051512090304120f06150e1e060607110f180403 60
    0x811919001d02041a07001c040d2070820420007141d5070600a03800f0f82d0003402480c070540307648640303420030641799006032203000c000390f00e41c20014644402101c14684500003e81c0c1c05100c6480300c0e20b4404103144024103106400803d81c00ca5000b0130100745020300c0984032a0301800e500e90440310a512004c0008015501650070246d0740c841217000401d046901c0340c8240e4003a1a0b90f50b003030070201e40c49600944098100d0100203035021360508044000c00a4400030000000510406d000703001100c0640c2c075000c01c00350048030100c8c1e1814820103000c203207274180002a5100d10340314800248202c00040c1840006080011903802d40c0700b0240d20240d00060b01d502031821703c2e18040c841c004803825604020150f00103a041c04d03003002400c0e0b01c5001695010412001074030380343c1003441034104040d5600080065205ca54030300060900040324400c2c0c201401d02400c0108954902e42c680e08120011584032100d5003140c44c46032079140d5082e0038071205001940450420f810007a2004040b040c1c02c119901d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 684423767 1250 684422517 684422527
    0x1a030303070e0d0203030702040207080c06060a030305040311011e090501080610020c060c070905072001090201121505040f052502071701020d0e010b0a1e0e0601021e03120606 77
    0xba00090031030403028060383c455401110500c002415446040d000960086c40850150140070414016005800300e4504403446602e50408006502e601840f0040c0040c80c208024000241c0c400c01c001c01d0b100041c145050a641e000c1500c0c03000006842c10100021060b080400c003a603488441160440c00c10b030f401480d402c400e080001d44031f8004024040c0200c1c000103600c0d408030000c0000710010842d0300d034108903d041242d8000c00d0048000c1d40a0562018101d00e0880c241062103078010280d416116007101840d200400000380010003129102c041a44600081d99100c1c0d0040720310b144c1c0030307040001d101c0c42c104107100038403c5201c982c030f1105182d648140507040d1300024010103544070f00500d4040880b02c0c502050180c8600c00c03900e100d26040428100b00040f0540014401440171104004183d032500b0309200d8002c251644514044a0000100020032040308100d0300108188182c0d201010400c0508412240c0c40030401440d920015038404510110000a03810100444d0810310741 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 684425017 1250 684423767 684423781
    0x2a15060501051602010f110f060f0c0c070e060303040302090a050f090a0b040b060a030f0c2303060a0b1f0c15050f06092505030f01061b0b060f0a091a030303 69
    0x43c6900a009046c0b20000342030126150084901a2109246400301e43c40390008040c050f4503080f064510b081c40100c0074010444c5044d0040650b2468a0402d005000700c81c9858503003060b00c440540390b960140003c00011015880da44152171090b0b107034841c08a030701e052020742d17404a0080200b41c5403450700000030281c001a503000d0710366040340c0c00200f0048951101d07400917140c070780749510050180c102c41020008001c000c030140c00c221511030744421682c0c003940030507440d6200168800d5905400000019000c14130070390040000d944060714070794a1500d00c01805003a00104c01d01800407850145110040002500c3d0039510351180da04148441d05101500700a80500900114800c60704072000a90000c6071070b8440c5128081d800d4500742003041c01c04094110303401a202647c541d03481e00d0000c01c046000302c1c1e60000c2680c001d507021a813000c141d2500c00d035440c0080d14496100382a9a108a080e58556001202030003000c607000403442d441c1c0307481d010f0720100300c040a03000c0e1300300b40104514 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 684426267 1250 684425017 684425047
    0x12240b090907031e020d0b0406121b060e21162102091305010b03060717090109020a05091b0a030b120c0906061303020d0c1502030f0a2a1506050105 65
    0x100c13501c0da4000340c1c55a083c2e42040028012060440f50414038000e40002c21841025400744d0303140c00703200d0300c0107200b0301c0b008040c015070704a001d41d401059554208083da41011103000260501e61070310240000d89010059041030840c040110003100d4082052002c09084c0006082180d5048031101501406a006c07800711070000348030541480b16541e0b030005004080d00710640900c00201503c0c2146001d45010340054100c5004456100c6007100068517408140f00e5400f50f01c1d002401d00b20342528041c00c00c110200b005080d0803d011260b0302c000782c0010040080e10700300c81c1d582c070081640441c1005102814603800702154969002032103c03e0240c0390a016160440019940c03950744100d0443c218608030510b274002500900521004800e011500c01c201041d0390b4074076480116103407242401c0f6a64000e06d04039041c09801044005001030064600030f0186400c40701d07000d48111010495518850a0300013030b1580e0091103400024188948148405000c00f401c2c001c0c200b00020300c400d10 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 684427517 1250 684426267 684426311
    0x4020a0e01062f010608061b04030b0c07021c1109090d0f200a0803010305010c050c030a18030b0901060905060d0c0911070c12020306010909020112240b09090703 71
    0x6403d0144550714618000d03141030828140b01c0ca04001e000856481071003ea807500304031401c0c0e10320108004000c4010a106080b1021603802003003440c460f80f00c0215048143d401608203d81c4801b2071400c2d00c0304840941c2c41c0103003440c080c9120701074040d000c00030300995050051030f1103000c0d04101003a0a5003904800d0a414818071881d101c003040e201c816203150380780440c002405181c030402604004021086000b181a82e12480084c032502644034429511801089001c5105800900005522511811010100d40103a04104503866520b469143d504081a5241c00460351250030900140340315004517600808241c80440d0b4042c03480d2141c1c0001c101a0040c1c811041e04c0d01607188012500f88180d4908641003040013000d2176803174840451880700c06000305c0c0a40980000020160114410b504600e0f030180c4038040c819991000703e000504409401c045e05406000d06540300610408005014140c200030b03c0f55100c1c440380c2048001e4500034800c038201810440502c03004504180c01c01 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 684428767 1250 684427517 684427547
    0x10c0c120804020301023f0702100905070905070507060c083903091c03060e060d0f1b050901080705210c031b100e09070f0201090204050a0504020a0e0106 68
    0x40700e65100c910009001e84034100a410340001c06240392401c1010815865006a15040442c80c441c00803c604020481040f24240c01580182070400382d0441550020031823184104142c410035a101d03e5941d003224829280c28002130404507811003000103500c900f030070716215410301c1d040c0b0b03242c056415544000c01c400c02451106000d0000c0b07e1301050946030300c580401032281e40d174032481c0160b482035460190001958524541c56202e07a0254000e01c11070003641c49213086003025544641c1400440744c00b001c0c0444080580c0f40d01c03000130400140031500700c40d007038084891001385040100203442e28103800c01c07400c913008070500f0001a5108801d031915040c07407014425141e81640983c0c1c0c2000090085981c15001d1000c050320001d0101e41d45c10b148038011030325001408101e10040303800d010825041500004000301107400b45000b20b4100c000c8501902c0081801d6505a02140c15160f05584d0260180d0301c4605006c00c51a10243c0ca034003030090316445c011a580340c4480141107181c0c640c41d0b0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 684430017 1250 684428767 684428777
    0xc0a06110a060c0503270d052b0609060504061401180b0f03010e010909030c03050c0c040212091e1903050f0c0c03120f0d020d06150e03010c0c12 64
    0x415012241444000280703504610100543c1c0c45003d8050b1269204650300c281d05900301e200c4108151200e1000884803007200014004c600340d0810603100c1e40d00121754000811148207981c15000302304c041002003071019500200c0c005240c2500da0064a4190b0049403045080c288180071984681c400c4001d212024645003019030f0040ca014010201c00d600005c0d289540001e00725a0000940001c1d4100c40c504001124170360b07628402c200846000310700c004e001030000303a1a40c1c00701e40b003078001c0c1c00040c50408c1901d404000303003800201240e004a00f8500c0c0c030700c0c40c042003000e8480c0601c000004000316000104078411041d1199841c2d040424148054501d41c00001c410b15100d0410345e030790802014889683c0742c048804441e590217941115034130070300c10f41c0721550b9204185030560760902c2003140514100b2400f1590301d0701035040300352861055a541d100003e445030768000071f01c1051109481d55807401c145403043c5800c1d01c0358000396000b03000d8001207180c00100d025408032030001844c42c02c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 684431267 1250 684430017 684430037
    0x180603020a05030a0f1106090901271a01080712061805150d0b0c09040203042a061409031c0503070f1805060a02160906050316140d08070c1211030c0a06 67
    0x3407c9802802d41198018181c0000400c80c0290180c20610203681030190b1601048444200415140f008054868508480458541d554018282e082c1c1107202404c100b807540300560500390440d4403903071000c04c40c00e80c082022824010148905504004850020091101b18401040d00b52401e210024942c003010000140a00f401d10280d510000d801001075580303061234141103059801d4055082040b01c5109140514504001031100444015486100280c4035420f0f02844c43c6c1c0005001e80d400d03014030100c041c0070a0210915104200301c40d159262a4203048500408001c6102106000e000080300d00d901c02c2d10030407625400301d44080b40c880c0c1d695110140101e00f0b20004d204095014009584081506030341034106005a43e426011600160a46200d4154103100d03841181900c00c0c40d0407003685030f8180314580d8a000e40c001c121040c604252561a11602d42d03a6901481c12001c45003455400c000c08a40340b0009424201c004124600d0194001489071040e031169505200306815 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 684432517 1250 684431267 684431269
    0xa0c1a0910030e01020414041d10091a040c06090603050408040b0d14102c04060c0c1401021e0702150306010905030613060e030a020d0e0604180603020a05030a0f11 72
    0x101c81e40028000307541b00e41e40c03650a4900c00766a0130009108a050070545184102c1c803100c3c0c104403003828001083c05030081e0b000900102901e4200faa0390040c0b1109490310300400b941005d020303038402c1e500356a403a45044070040c07603180c09800100405082a00f840040340000007130780d003628004070409507a1000858410000d100203601202c0e46201c0908000704249408064400c6031a84c25980c040706140701620b50b036100f4881c080640c0c00b510100400c01091082d44408100708090601c40ba100070b45450303e841b066140c07601882d03242e400003541200c0152210007441000390344c1c8241807c140c025400115117039090a603060104401000050446e8842c0e0344c4030004010150946080f410070074203a17103451040c61402c1c1c494a00b00a140c0e01200000821510041980d070b0242007176818000e02102c0c1c070800d00c0743e065070006050102090040b81c282001d00c51072022100060f00c207145105001040070250300080c03098110f050071002164404140c4142d10741d00c0302803034a900702004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 684433767 1250 684432517 684432521
    0x402240a180e0a0902040e120d05060a080f0c010f0c08070b070e0d080309070617070c030309060f1b02030a0207170f0604150f0606090308130302030f0a0c1a091003 72
    0x742c4034200e41c1150340d050102d11140b41d8044a151402900d061044580d10044180d4401d201440701c5d141000801108050070420f80c821604107600900b00b0010320381d10042e0745e12b82100c5840401c0140c00c24101391000350780004081071080954207060128980b41d80b0303034860500482101070059a2881c0001d240f031032040741c4424110030020100f1640d540c40d42050080c0c2c7c1c10490300c175405840780c0e41d40800d0b000e02400305419001c4003074010128654074502c04841c040c0d4a540210706040d1210014000207106000e00185509160307070000b80c41c1503038000200152021410101035400c100b10b00d03402d03a6400725003202520420703407034225800c40c3d08545c0e0b403800010410b030190394081c0100340000c00a80040c0100ca15000071003c4c090740c908500f14004071000d0b482807001080580104200203510103001d008010070880001d41800e40d40c8d004179042612a02113000303582c004160a0040010030b0b040d68010302540710388038003004105968059103210758840c96114800d074070320f04024a44030b5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 684435017 1250 684433767 684433769
    0x2c0f0f070e01030e061e13050d051e1b0607030903230405030a03020105160207060e0103230c03010503190f020120070602010603140604261b03030402240a18 69
    0x4402c80d529841c00c01001d000c45961b0100308121954000040b0340742545122001c03050301e40140250280f0386d220842915290b00680804080c0401a403107010f09000080141071090101402680201c0881c8507550038520001e08440c1414680204d00020950200000f80b1070600707500000d06424034140300b2030040c080caa01055151082135a80300030180e06403c5540589038103c001080c50003810402e80e01d5000b03500810001904541400e10658840d4100c80f480041b0b00300c043d08586241681d120700e01e131044491000c0c109000004100900b001c202c00c0c0314104613144e4182c854019030b55091682c4010100183c1000070242110601151180d1381c1d03c182038409044528807507807900040c0c041c04051106950000743c498255460800100d000340c4070743d5021032120340e40145101030690456428121100f6500140b22a910b0f588840070b4a100101000000316100d1900c2e00c1000201240050520480541c101650070703802c0c0d01a09403010054982011040c00c011800007003410080c0d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 684436267 1250 684435017 684435041
    0x190e0f010c020106060906121d030a020705031e1203090f0304080d0801061d190f060c0b0c190e06090d0305092d040e0102042c0f0f070e0103 62
    0x14024a000145405500c01038070340708950000d03c01c02d0303034402c170948800c0154030405011070681d034051501d250842d400121891080c0000d8014a401c40580605d19045801a10b0142c0d001c040d0601180ca4104040244103083c0c0000e0002140c00c0c0c0e141903200c220300341e0145043d21010003c100481018810540700c1e074602400c40c1c5d1a5035072180d201e5541e6a00d00031075008034103d000041340c21841601c41850031001d011006054000c0d80d010703c003d40d0346660108805a103505004520400c50000c00d0005000035074a40c042001c1c0f50406d010101e601800b04c5000c0403080007800e20740341c1440141e040304580c50034008402c0c45544049041d0f880b415614952080070035180700109504500603016031041514201d1001080401d10541003100b017403404810441481101500c0c43c090300110714075070000c0300250620340c1d540d1411207601d00503034060312080c01940201b491447d11000443c2d03c00700e4a0103082c081d040264503600c010501502d4941000250b040c540ca269020b500030782403180d1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 684437517 1250 684436267 684436273
    0x316020105090607141e0109020d030804050a080f2203051c0908060a06140a0f050f010302210405160f03080d0b09010e180604021c2609010e0612190e 66
    0x3185040304c80c1c07200ca1b01d6403040c1988805c1030036100420014462880310359800707040880a00003645054070404002001285c0320700c541d80d4501d00041c12038000e0489803112000c06510344402d80c4500400716603621400080c1310206c0300410200d000007410b400e0102000105030343c01c44911008541c03030a855000302581c0d20444041c4141108030340d10240482d108031308507034800d101c0725003045420581e0303116440c0400d95412060000780751040e601181560141401813070001000c207442e60030300103980800c0d281c00700b40007004184442401482c214040603c442030f500d03410683c485e80030110b01c0c000940707180000329840911406035071000724120401401504950307520f0106801c0c0c00002c603426030345200d001800d0b2100c06400101e840c05250300074066111007840740311030429011200d80c26100d031402d00c040344400c40c1d010078000c81e66401e44030304c40c3c0c1d885003000300140c02994030f2440d0f540207450800ca0503a46400350301c3c4607900310482403800d91140ea5082e01d29800740618809007a1540 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 684438767 1250 684437517 684437543
    0x70e09031206062206270e06060909040609020306090604080d110c011503020f0402040302010e06030a15060f080f0603100902040b0303041e05030106030b13030c080a0f02010605030316020105090607 87
    0x4211442c84c00701d0305035079107041968801c84000d4200c405404100584501005814040c805001403030950062010f401d4500700300701640050b070340d52410f44056454554440000301541400c0c042d09034003092000c0104641e04042d078a548180c840c2d4908055403958903401413410b0905582111600e0210000a100030120100080d000d40700070300c0101e202c3d5850440360149410a402030764103c94058480c00742c3c410b02d030781c1804090360004120f0f01d002691220050317455010910110040c02e4030b03a5802040f80003410001d03200d41030203807130421905175076010800706950000e104000048607010202d046107162000c1000b900401c00065814000860b0110b00c0541e5507002a19100881e1814100c07240d8901c1070600300ea0142c000a000c600304100003505c11180c00c0c8003950424880d240414440c01d1584a84c1082e0b0825403a07a0000b800d1000b8601c44982c1c240200c002030203084014502e400700d01030740c0040900c49140c00a05000c4081680f8400c0d40d520010341e0342035604050225074007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 684440017 1250 684438767 684438817
    0x10c0c02030304063515010e0a03020d06020408030c0708160e070c0c0b2205040209060304081308030d0b010e0901050112090c09050903040303110d0509131d0f070e0903120606 77
    0x207040119110325000c101c80302014a1984a8a40c8c0c446031000500072452050030b42c0c081c00007032608810180e8440387c082000041002081008004580e4000043e0001030b081c54415414228020185003404c00900800d000c04009605c189030801d885003800c0c82c0744102c91030a10a5100e803a4486e45a00102041c1c060f00c83c40302c02c4420078500c203a061000012a02c03107041104078054074001d941c0049082c000100003400310001030101c2900809268030181d0749094551540d8010020a0800c94440000010658226281c0101010101d0b03823242190f04010001300340074150280014181c2d11a03000078240000c80daa194081e190b071000c280079a01d8083d0200d5540da20512088000414214035102000310202d404600749000303036203513460150b045080150510b1b0249503000441e0707480340c200c3c40b050b409020580302401c10308058284e50b86500c01c001d0603c0910b603c901d075140d80e001c0030070400c2c8501008071007081203820302c2034030316031030b0540815103900592030b42c4c1007140c00307007200d000f02 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 684441267 1250 684440017 684440117
    0x20711100e030f0a20061204050309090a021603030209060d0501080f210a050a0908062e0303083c150103020c1e1002070c08010c0c0203030406 63
    0x5868069049500b40800c2080f9660f03141c1007078001810584c045a28420054608a0902281080244002e0904440541c081c407881025507080302e199200145010241c101020101c7e88540d900c1c40c00c5061690f000c40c0554440c030b10b00001020158000342e02201c5030307114004d1b40e0380078018810030401517840310a400d0750b400c0c8880f0041103a115100401d481c6020683d140039846803913500705401c004641c1c1003034589401442000d414400810000702e10200100300e01417056000315060040104212545030400074610b0300b90085503e04ea9042c0f01013608100040c0d0014100c0460480101940000345003410f58002d80325045265880b013494002400c00c4064000e2550054001d8401c00711030041d07080303100d00c03402842e1a8001109100100d001440200c8207000c07880281c0d8071001c0d007164440100c0e48084021906024012014050f21034244500c080000c0c080c00c10100b154495000280d4034016031140d0020000300001d18400880004070030902c030392542c80141c2c03804460302103030f030b40c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 684442517 1250 684441267 684441287
    0xf050d0f09060b03210304020d060507051804060b041701140103030c060f0912112e060801092103060503150106030513020915190b070510060b03060402071110 70
    0x1c1c1c2e1030508406465a10700072480181d02c111681d4000002c02240140010680000704240d030b000069450f0705010a485001c0c940c4200b0403540c2d595079072082480700c060900414204c01b4011841d01200740b02c502180c0080b2025601501d22040580101484080c050002c44520f030100c2220140000201038001040002d003920500e070a0022602419400048417004c40016107040d41c4020090320060042c810b0140c04200074060314081000072500e03201c0c035170342d400360741003100311800500480d00040e00c104400346c07104600034044030049841d400c0300951070300c082c9421405005885030000b80243e00c0300b8010310700903050300d50071a043d91035403018101c00d20800c00030130304080000740c040c1c40c20314030174043d25030040940035240c030740c288500c015840100010360014101d00d5079159803491491288001e144061140d130b41e5020900e003043c200b400002503580c2050401a051044180c4181030383d078003020641d40181c40343c4003801c0c0081c0e07010f0920000303a000001505d04440c01e0b035001903451 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 684443767 1250 684442517 684442523
    0x317100e0a054501151712031302181e06060414011206140a0b19030c030b0a030506040521070204181a1602030702030604020d0c0e0c03090d0903120f050d0f09 70
    0x1782c8041e03903000603080101850441390015080015464040b00c1924081d40d000404440d1414800c904c1c1e50104812417201c088609440704a20200104c901c0d441d000f140503582c24001c00c201a0400758089641401140200d0040da46100e02010859210360b648034a0158464000e000940d0b8400300c610920f00c0f0380c001d5034003800309032401280100c0d01000710344441d041004500c074403409040c011001401c111130305904158a5283d6400070fa0b660071a594040c0d030241e800350120b030403d860242c0c5040456080c0000d241141c1035401c5c0d401c4004802d0320349181e0160b5020641ca0313007024011900d154070407002484088a0016010050882d4500d940304002d50103030711080c1a00746c40e0503603503030140040080d40b50f840080020014100101542c1220344511117402940d922201c21034468003040380c1140c03008001000300441943c00700310356660080070b0300307040c0803245c15529485564000e04c3c164000b40903c0010850300d07140300700111505600c7d0341c04d080080c50941d000507c0a004075100c20b03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 684445017 1250 684443767 684443801
    0x606040e19150f0305280303050604321f06050f13060c0b0c09061803034005060f09150a0903030801300317100e0a054501 54
    0x19881008424550f1b1038000c0c4803002c0c2620b983c42c1545c045000d4540140419009525514800b0100300c0c80e20f0320312a84c010740c00071906005c21140d040500c002005107901a03103825500d03008020006948030030142c81c1c0600e0100d690f00d1600040c0260b82c4900c04a0124002c0c05510000f81e036544210034805403480344036442d80e96120028898441e000d00e03540c40340d000408111031214901c9002c900300c01d045016090b079042544018100c0803082007603100201c021580303519241803201740961385001c44001c503aa0000d6a00307110201d999402807920605a070440090390b188140d0758910700300c0c101308140620380d50301c07400380d1401003a81c0c02600c000c90209205d0800032580c9452614200e1401d100c25a00c040042c4520340140b1140200c00415001d200700015103009054003846071a00c1505a42c50290940b1710300809003103180c900420300d8800d2407400041c00502c0000c8605890150f54404220300c1103043c09110107001c0c01030031440b01c1082e0080442030700588040d00b00105100e600620b07 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 684446267 1250 684445017 684445033
    0x705120417010c02060109090c0302041104080d030501031101030b0f13021e031b0a051c0603030f0516120905061c06050109060e010f030f02070b010e0606040e19150f0305 75
    0x500c0e802d0303c40f42883c81000d03800c40700041c059120310303502c00005980501202400315540b07402060850b403a81c01c0304002900b00080901961904125000c220030240c5410080d80d8599200d01d0b1041c00302240c110704060300c0726045a216591035100204081c00101782c21030001a0801c1c40000b584608944d980d501d44060000140034908005d9903c1000d0200c4402d0071804000b030b140300c0551018640c4000d101d4148050007140c0405c0b007202c03100610180000508600b1814080c00300b014920310081008002c12510748070000355546006030b507910845100d2038202c500c4058070803a000d07070081600320705c1c007081c1d0400410080503a60001581040108032094641c0300460306850540550404980080304002c0d10754451b90500c5040140d40c980040c0c1000f0300c0c0b04010582c0d02060302520300c100c10a00605c406803000000c140c1184081390a54a01486c0220040e2021001000000c0c4c40709240505a442039035904110900004280240c10315a141c0c41c09c60144801404295654490050303 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 684447517 1250 684446267 684446309
    0xf031510030e030f03180609012325020c0301020f03060a060c0b010e0604061508040309091a01050f0c01140103051212190b2205060414040807060207051204 69
    0x8981800c480645010354501a000313000d200c3c042e0b101400d2840011124038440e08204010301006008000410001c20306e80756040100c0c2c0c201e01745c11444203200215009008803c6070064142c8048002c0d203a91104000d90709205070f040c08d0700e1070595601540001450303503120b00c64400441c8540022142c51030000c0c4c6605086455060902c0000c0000582d100140850702503c0b0120f640114000c10110b425520b40b44080500c9580540c0c96001c41c0c03001051104160300852040d0103010040300400c0002c90b21000c55540114060400d814030034000b0300c114a000119007111092590080280003142c468406c103808604244015281c0b8005e040726100b03121144012202054402d1244500c5515034119185015a91f10001c50720951341382807244142c1c8541d0542095500350206164080082e41d00c01402da900080c1124403c03803900f0b00030702c0f0040c0340666090308550400340d595222074032031034044001c0c442d000001e0f003503114841c0006e0180700200010300545910b00c1e2600c2d41d9030031440b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 684448767 1250 684447517 684447521
    0x1a03120c060c0c0f1009110904170d090f110a0608090715021005090c01021204030f060b06210402040e2a0103060317040f17150c0f03151003 62
    0x4000314054009401046010302e820015064015440099a03480300800e0406450708500982600e0710907180c200d40403d10840078268000041f098560006618280c0e441d84903e228001540e0b04080740880c1d04990036445a103c1c0f000c0913440340109001c80704070f0802480d40244648480d11680110b10081a42403152045038042d012141c024500303241000303840b1030440401d0560750114851180078940c0203d0a000307842c09a4515000351400001c0720300020b00f400c0144048800441003003008000080ea21054a16001c1e0802000691440c0070000a800c0c0d01c140800041d40d9850701d400e60750001000a0030700d02441c42103c081104040c03503030300c00392101000b602e103600c00d0469051410604603820119401c4200500d000609503480b41ea030100296003d141c1c00080010100f4144100000300715943e010b440d0080b0341207115040150340300e40d0f541d20f06180540e940c0300301c400f00b4014005101034076540d8402001080d2030703141031070520345005031080c4002d110f401d60f03401d030b00783ea0390080c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 684450017 1250 684448767 684448777
    0x180f05090d05180609090a061e030201120c0c2310050c07030c020136091e0e010603120206060f04020a02030906030903040504090f060501080d2106091a0312 69
    0xa6110b850414400d00c18118040340c104a80c507801c03120421201006560301c00340307540704240312100098002e0031b11810007280d10b0b1b0301c2c0c0e0750242903446020520160f81c1010504100f040702d1a400f10b080e03258240c08646001140100608180840c6140e006261044030458580f00915003240c80f804804c04070b00d001d603002a24001041d282c2080043c0c0843d1040d01c1c048116030040c10020071060200281d42100a0160a6010301c150500f85501c8018031a50840c03004001c6030708107101d602c940b855401940f10078402c0300b000d4140e480010b004519001e41091340259001985c95003101342003080692180e40403511136104800c0107440070400d207424401c1d9102d01d0100d074015810200c064003406000d0348041c1070b100051105100002d00307581d07940101090603104071581c41c00030060f031402030141d660603080b00c2c00a41107629643c0045520644a506506c100510500300310301240000c0f0041280b604210a0282091948000001028850700f8014400e80840d0585021f0b038160501502030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 684451267 1250 684450017 684450043
    0x3111005040b0a0207051e040b1e090411030102030106030608011d19060b0d050124050108130201050d060803031501020a0b0a022203050a14010c0f030510180f0509 72
    0x20300003480000142e5018081c083c0d403600454800300e440700b00180c4602040d102e50700401c60320f40400401400d02c3d00170b03680d44000031b0f600206141200c12480c0201c00c0500021401860aa00014240800341020710030120024000319900d50f19401c0c000c0141809010303039180d66003403200ca00c814031000000c01c0c00c01640300307014002c02c1d0021007900400001c098800d642c000d4503a04a0700d0150340380c04085031341c584200000a040020104607041c43c0034103d420180e041d155400c10826641c104952562102e43d005080c2003200c201e20042e10180500c03c030818000c0c6c940300001c1189000040110300907040c03c0c2d100301c0c82400780c0004907600d00030b855004100f4441031006c11005140c90b009044808005040b940091503100d4500001081c1b990054401d40c2c000901d4105000030b001050302002e000800903c20404070b9000076068081d400d408404160743c03070001030078984003500c01c0005417180c2e08943c07480106440800010b48840c0700320b00d81491902c4046030342810006060102c16031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 684452517 1250 684451267 684451277
    0x5090c010f03020c0106050a170c12071809060e060702210913020403140604020a150503060f01020c0a0329090706031107150f0605030f281202030301031110 69
    0xa500700440c00303034000b42681c4c080f5640b038140101d110340c0c0700d01069001e8011200c0951a0b60034005031645070003e1162000d004801040b84079503c0100840c0810030740e0b500030540c803414207206069030300900345014081c01e124074180d05100c030030001092060145a05608a44104122000100c82d290703490000761200b600801a0740c0c01e40c2419030b03010850300402030005080591707d40702e80c01c0c4204002a4015960049000c1008501e00360b01528058020305141100d070000c81840507100e880041c01c00380c410024060a480180c0c030800c40c004803010040c18003000b00f641c074540016096140c0800c1c1726440412019030b0304041e90613800e10f229100107070007000e125240490543c010560700100005841081003040003148005001720894503030101c00041c0c04002c41c0c41c90045600d16000148641c0003c5c007100c2c407030480010140b02090204641d683e440804003100700540101120080c080c041482001c11116004400345040740d026644500d1031010200400c07280360b880c0700c2c070080491 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 684453767 1250 684452517 684452537
    0xa080303060321040e2509030b010b0912030f04031109060102060619090c0e01020c010201051b0c07170a0219060c03033b0c0d0809220906060905090c01 67
    0xf0000c40001d040190f21406140b81980781c2503624a8907070201c40d0070b100c030560703021005500000c140c010f082c030020070319084282d1421036031000c1c45c01d101031103116403240300884c190030307a6501c48140c10311803041c21003200d0780c82e0350000030000c00390424070003510500881080c54045040c0b142006104842c140d0140003155a4103041140102c10103000500e07004440b24045840441c922400c03440541a81320a005400c0712800240b504010f40c0507581164104000e11803c43c0c240f00c4443c2c100680c041c8081d8841c50030102842c5880c1442c2d1000b110b8016a10550f0001e080100c2c032a40141d0094606e82e8a01039a0101400d00c051284a9680003540050014011a10a502603140f103540e01c4841c101074251400040036100480c510001c2c20701000a6805208404000c0d52017114015103028080301607a0310340651902518941030f015107880984e1a8064144960000d2405444802040005442e08103400200804d00500100358505804030304080c200081d02c80300071205940c1d0000103 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 684455017 1250 684453767 684453793
    0x90b090904081b070f0e0108011a10020f0307060b040b0a1409060406080109140105100501050702060a030e0d21090f15060f080f1e1504030203070816020a0803030603 73
    0x560025a02c100d01c0f2020034844071404034144102801001c141c07519401280c01d00d0303942902d643c01a0b00420361685050f031181c0400d00c060b1481707042040219250500a0389026090b0305082c071000c0e1444080c00005408002c01213240d01c0b03000d4480301035404001d40001c0381c003402607051050082c6501050440d21001691410b4100315500050203000801c40a0780d6100a0342952054201210300030290034425501a109100d0150703c0610005180c1c0124278090000e002031051102c003a006400026040349024040e40003050b10b007072120121440003c000000034a00380d011407240481c400e00300f419101050050044440d8650400039480305e402c47d503642c041030000f00c6140340003410789800b0f0004880003524041c01c01021140090880600d218131030900b0543c0000380c101110002e542020780315003001540c004000c1003081c941c0015142c034101645580078980c0003e20801c000104400c0790113000022062891080d95028070305034803030341202e80302e01044480300e4040c2d0041d044000c070 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 684456267 1250 684455017 684455033
    0x1d030c0102120d0f0218030d03020a0906080406140c270a050607020d021002010b09090a031709030d0f0207060b090417071119060206100b030106121d010c090b090904 73
    0x211070026040050810141250101686c201401101c100c040c50200120f10342010f2100690702c40b07044ca42140f80c0702d43c040c0c3c042c1414200d4003424040100640c006010824143c2c04040d04c03086c5080850200d14020705510b1490380044551400e26206d144401010307410241218a03c110041c000b85240b03007020700303110142e0840803059078400403086000025884040076180d48010310381c004210320000f1000d1125003180903011010701e920041c0140042a88030325054241448402c00650311348071551040d265002c0c070382c042041c0070301d84400034443c600300d50300422400303100c7e1000740147d0b40c000c0200705000c1d2044501800c001442010060102c03144402170401c10300c10080b0100e404504404120103000d04820401c005940703030014050240c042100741d41c407040c0d0200d1207042500b44510381207603000611030b039003d0154035400300d1034554068010104d0783c19240c43c14000c0c001e03c422405d0280070310003606000b00350120404505032240740112403601102a00b141490741b210f42d18204 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 684457517 1250 684456267 684456277
    0x110d0516050414040903020c091005010e0f031b0105071406040209010801021617040306050f01031e0f02100c02030313140d0206120403090302090c0703090522090809101d030c010212 80
    0xc5010b030100c8c040c95681d5207642903015085801d6807408090511001401e0132410b018914880d00724203400440710394001030510f0f1a0703c0d200310600c02500003d40107070761038011100020700200742c030111020010000035480344283c0c02140e55003816681c0b901d44900300e114840306401e1910428001d003010031403010044000b0a000207034203290030355030f490744421a034040d0b81d814010b8a9040041003840140034556040c07807803040075124088865907131606500c841e424002d004140a80040e0b1010780114040da03a400c0e005800d0b2940c680381d0a41d00c0043d00c1d80c5006030a030040405901c02c0c3c1500740310052462a0b13502800c40703450b00d0440041c10081540040c822000c200100201000503110700c01c119000e0003000100e01d803070701d9491602806d021b1351500001e0040a010800c02030040381c03458115030310108900e001800e009907013481c000c1c3d8800c02005e0307034001d0030f01030185003003940c02038815075601d042c2c0b0068908042c602013019110103013103502e58016130012850350080c03039020009003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 684458767 1250 684457517 684457523
    0x12230a020f0312040e011404060501051c06030f060e0708070b1e040f1205070509040b01030b090a02061903051b03040308070216030b041b0b0f0706110d05160504140409 74
    0x900f690586500c85910360302641000141d032201d880104103210001403580c4941e003080f03a0038006641003000007000d42c0203041108410342401e542141c0b00410720f034491000b540d00007054204001d858181343d40034000103041a0600c1c0b20f1403900203071059001c10f9141c04d590600440b580351152201c0786072070307a100102c84140900010000082d1210380c3e40e46d448001e000c01324013951440428107080e41070003016840307140210070250800000400903c0c0081c1525800743c1114400e07200c1c5000240b03008000240203401a000188040d042ca0303950041c0d515403655658280010ba803080280404034500385504880b4402c188003040000e0700541d001d0f613008500b4812a00d44075070031141614202219842580c038525400b092009200074041d1142d40214607030090042289490b01601141c4900258241c04020104c3c0c0e84040002c10b07000f50052240d280101500c0c0e0024181c440010700341680c45459288040381d040d40c440d40154280c400b182d00d55a418070040c103c0302c0074080a000007003011 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 684460017 1250 684458767 684458773
    0x2311206060e0108060412050307020c041107020406091505040605100c0516030305030412020604150c0e06130608010e130204110c01091a011d0a150302030712230a020f03 75
    0x400e5255882caa03042c0244000c00081495013071900344010300d58005070509003044003c00800030147c0e00040c200e41c1e444030903070f4000f49018035000601d889000b8040b00941c42824014000341594007604404040000701e4807480380a0342d074030200801c41d59144100e50700701c3e504504200c5890b0003203000142e00303801403003520041d5084400e100803c08a5030011030106501000b8082400004102101d410516000820716400c0c682c41c0e03503281d4030701c03060002e51607500c51840411052250307030f401242e04000b520594465549000e4400c614515000302000070380410000240d010309400b05034009c800c0109070510203945a003d11001c3d020442e5540400034081100306851102480342c40181070161030a007a47c4814003001c101000300603800700514241c0c0202a40e10b100100000c0c0e6048801020002080c44900c080e00081c06103541c806507140c0200d5030001414014403001c0401148039661101c020350540c513584011001c9640c0700400742d03005811000c010300b440040c03070b04180f00040c11 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 684461267 1250 684460017 684460019
    0x50301180609061409011e0903171915080606030304051e0f1c03030b060901050d0e0f0d0801030501060f0f0e07030b031e0c030102040812030a06090207060231120606 73
    0x2000641344040e103d01702d07283e55030440a01c1d40d5880c0c070404103084001070400d2000b0040e40e2401058041003e00c2042003203202e44c003080e51040c81039006420800070100c180490301912a9201e000080d51180e10381c1802001c00091080c1b4010007118107840000b0841d00c0c1d00008041d60491020070001040d42201c601e00501501d50b4542c14001c9141c00410034051151310b003480e00405640c0741e208000e00031402404020034586e040002c0c0ca0782e84a42881c002055114000c03658500052084d07540c4450182c0400c194180c3e51010101d03040c3da015800030320103a592500720441e000e00c1441400b881c21100714080c007200946080250300041140b801250004041000074180340ca02071076090305900b90854000894004d004025a01c1004c03402141058034080382c058480c01050300000d04c55600000281080d0340560000000d840b00010031502e503200351030000003c1d44085603020700c0c00d13041d070265a004810107010703130f010440040461400c00d14251600c4000343c4d40c02c40854209803250340c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 684462517 1250 684461267 684461291
    0xc0d05160507090902041a010503070c020f060a03020a1b02212d0c030f0d0c020315040c14191806031406071403100b031e09010c0905030118060906 65
    0x703280040c24203d00c000a010800344100011180c1e0040c001c0c40341b080f07002a448003a87c01505407036100c0207a08140c84200400d20000740141300d5503045a500907004920202016419809031000704016150306100402d6400301c05007400401800030360040528102150300e050701103083d080c020884085560540c0e000710049406404400040c3d6003900c0c080325800010001c21286c2444034042e00070780744444541281c581c5550f0602001801e00008200d42011074404120008103001550b008120900b49407601c10740116640c45003401c1640c640c00b03940140e1510081c0b4040c0c100b115003c01b0840c1e450000504000c01d03504590303880c200c2c1d0b07507400000810b4032078218040c500041000742581e8982980060054501404801c801b035000f0f000300004611240a0001920380b030b980555242d59620070030511580034a00c03829044807903001449011801500076191400d0390f82c44002c81c2035201c500303040c05c03101e80070100f5803034080c48681d600119103240d21008072240544404104451910 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 684463767 1250 684462517 684462523
    0xf0d0905100f14130201111f1a01050703030e0c0d081330060b0406080a0b0f090d0302030406020f030415060902030f060105030601020a0c0b090108010b0c0d051605 72
    0x84190380d00d800c010088072140035503120303101414031240800c021415440c1600c1c56581001480c6490007012181c080301035a00075003806d8075100054040b0340c98504034241c43c1f80382c501c04441c08240c40c1c1c100321170040c0e02001581c0340303580303600103940743d07410580a51400c50160a007540c00780f0843c020903078035000d1501c4101026100ca07000b584140d0792801c15041101d0904015403090880c1441c055001d0380b01407955000c440340c0781c062507501c0810466410318400070151112543d50151905d6000500110045265200da6004900c40d0501c3c3ea19503010301e03441101126022010f4205183d0300341218000d038007441d0024043c40d001030810815a4107032100e5441030324262154601600343e40d0600380140104000382503d00003d50035410303c25184c07202d010002d40040d041c0030307000c000100039900c00c001c2105115041802c2378800d0790f070368012004550181e1016400142e0b000b00105842c50b12034100c55210442c0b20040c50303131103407044040724181c001754203004044c4007264804011950030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 684465017 1250 684463767 684463781
    0x4020d0f0519231f03080f070c080106080c0907052107030b0906060a110a0203070308030f010b090306060103050601031401031110030615182706061d01031d011b02011413080f0d 78
    0x11a5003a0fa0b580300c60f0422000d0960700c1c0c1d01c84855a81020000d00dc107860103e4105048001940c400c1392540300c1340c0e0b05032090702440d038542c200c44100d14048041c0030690607042e4000c8105031010012041c40c1c1d014040c05207002c640054202c0717800c1000303414280c4180c04848241c040807050307a09031803803640001d060014991040d121031201006000c201540030034024010903101007160300c1c02e020b55005c41e0b00c0b0070005045c1d505150b5520001001c0d80d0290708050408003001940481968481c60039440c041c440e07000c1503001d1401d03203440d10807443c081d105d048240c3d0001114640005e200c5c40b400c0315210741d0840700c00d40801392940005920b02022255810345c1c5690140080c880009014030001c590040c0c0c000c00410821103c0d0000c850000420f02c1c62848003882d01294107051590404025010415040c04640c81c10018402e00070300e1208849891019600034080c1000000d805803101c00d081d5000c0e0301c4683d00c0302d414000960382100400c0303001c0801c00801e041c80050301503201154a0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 684466267 1250 684465017 684465037
    0xc0607020601080d020d051303052b0905060714030702060703270b0337090213051b0c21190801080c04020d0f0519231f0308 55
    0x106010245406000300c5016010250044c0150f150918000756903d40082c0004284400000c02101c00e0340d142500502454200044624004584058014a20540325041000717440c9207008292640b14840140403214010300c0e83d81400082d44034a1026840b8440c510034900c42040780d00d00580311071010700356850094603200340360103103001040b942c44a180c04008102d11751100600c0400c40c11019a90081110451045e9540042c21140150240c4051040c0c080c800680424804030b00ca40100760343c06d02c2038808031416141100c00105440c01540d210703640780b0102c9080c3c40f079001543d020302805420807082b00c1007104095600304402c1031001805146140014802801d82c01041d80006003810908d4440c0e0b082d850004600d4a0f0322183c02c40501c81e0fa00050304c204511340d2504a245440c3e1201010005801d0000010318171000b05501c0d80c2d8440c1c10705c10813000d1010240100c41d42c001c1b41005802d40d59848413810307409001034a10302404944114400703c0801d40e084040c041201c1c2c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 684467517 1250 684466267 684466273
    0x60d02090a0906181502070209010918170d0e0d0c0f0314030f040209060906030c100507150203010812161103150412031514060703120516030b0d020121110c 69
    0x28450802a81c122812171051100500402020380180c9880c403015045440342d10b8005250003105201001142c1c5407000a0300c1ea0440e04502c00005026000411304544420402c1100401d0304282c00d480752035003a180804541d8460100c40814000e20520740e131148203203081981c94500d41c0b000c00e10368205540301c200c1003100c3c00c100411803c000844036040031003240c062040e45041000284d8902d90149418062012080007103111801141a034160f0303940030b00364000c1d8204051121000750800d104003903440c812189a51a45003c800451b070355522004030b00e44003e81e81c2c7d1180d201849071a812181c01d44103a100000740c10030900c1c41e06000310b100c0c0c1d00c50104041018402003d0304c0796050154000018100100880c240f004600c0c82d10b85000d4400f9625011a401d00359040d542d01010909668100000c000c1100c1258144141d65002c030f81301000122950414042002e8007004024081441542010310071400f503451500c03c1c4000440c003055810303441c24150f515800210041140394 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 684468767 1250 684467517 684467561
    0x3061a0103050703020309062a040e071b0302071a04050402070309180605060306191703091305010b030a0b120a0f0b0f04020121150605030a0506010503060d02090a0906 74
    0x503a15002e0316070400c80c80e00d002c0d402d600304644260740317a140140040d440107080326480a5003892810020100c0010719840507144c568071b45403d11a81c03c1158008009155114400315a00240700035001003a0140e00800c641824078591580111010400c0c00010405000016199170307140010000107105c1eaa07901503d6103080520352607100d003091030050090402c18144056218242942d50100702214017810340448100600000880c3d41c00001590708c03043d410301c0f0b00400000c0100204141070340d107092034039508807400c021140b085c0104c0407120010008201040402d03000000c0380700c2d008002800380b03551852070514003507441404441510f40040303880180803521100075031003611400c2c94880d40c5460360000300030504050480140451618000c44d074100c40303610605441b0510714040d44038035101c100103001500100d80c0030010742e0410780010b006520a20507070340120000740c40500c2200c01a820405030120050036208002d559180000104c1c0c4140079040310046060701c040c0b040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 684470017 1250 684468767 684468769
    0xc1005010f060507030806041b0c12170601051b07080c121501031b0308040b030405060a0903140a17160206010609060504030b070c050a050304050a05090c0d110403061a 74
    0x9118140e00894501c1c1c01d801040002c41d0300502102c0d03070103900d032030040c085a880c0340000b002003055640c81c500c40c2914002401d44a9003044031011b2144c00341c0c4a24240e080d18070b40499155554080b04104410311601281c039a5000305c01415088600e64003200740c291607030041520308072072a403055500741d11031580381c03400781002004914003034002c202610300a901c1881c40c076031200c1c0610009208600b045400022101100300600c00b560f808001641d89079550700b2032800580003a1801c0e01d640c01241c0110b00390b8909403082c034070000c1c1d154446102820410710f864a058211401002c20711880c0b088180b03035401c0a22096124249511301c0300c01840301400300a140c5803058001400b48642c40760144801c40d0404181e03000c41e030380542c903c03c056844010450320030140d040e004016115001940b810803401101600c2a24800d49040e40001e98810420044500550746e86984503c104151441824203420144a17854244a85454241c0d01e95a40040b90110611703680031000b850211105 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 684471267 1250 684470017 684470021
    0x204150f17060106140409020d0903080f040203060106030b12061312080c0304060902120604060e1011120a0608060a1a090c0a030e16030602070c1d011a0f0c10 70
    0x380c0407140100c41552407082080c0e6031120103015000030301459810303405590030300c202110081d040e4824159114503405880101808a04e40c045000c01c207040300150003424ac000d041449603400a00a201903403130b0060079070040030031000c1160400f0074005904e502c1e032020000180150840c1003440c2e110851400d1aa0400c04403026010400582da0706001416442c5426030b03421903007100b000165200d2034400980788074064408080c95003d000104801d014055002504034981802560030780c030032881c4580300300d8070a420030030340d010020320054a40c0c403030010070241e00030844100000c1198544151030720708a000c82e03444603d95240d50720340c65443d1041e02c59110825055035000c005080005402420b0702640d908401015078034200c1c001100410869030204e505441000c0204540340c1c201440a9800000c007a159500710490001c0c0501c00121103001d8849014081182d59082c42144102c0e034030790a415140242050200b105c0c0c903c0c42d00010480d940044008042d201454845101 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 684472517 1250 684471267 684471269
    0x7091d04060c080103030f080c0706051602011d0d0c23030d060603090f08071b0f0515070b060909010906021b061302091807080703241e180204150f 65
    0x2040f071100010000250401a92400d005107410f2009040c0d98246010025010f004800b42900b81003000b030098401528118003c140707280d9009003d0112100c0c00c20700d4400b51045903c4080d40000d5500c244540715518a1482501c241800d18070400e4a21020003110010340c000711042c1c10006001e003903c41c1900c2450f00900c01e07801c0a00c0480c0782504c4504c5071081c82040641800000120501040308803082511884c904060308000c090308c90358107848420342401a20301400c81020040c1400c9078600c19912a2684400c803201eaa0380d803881845000d01014100502a44d00d40218800040a900140246280004a6480d000e0440040510380030015040034240d4152004840241e00d41200c40345c0d00a102000a0600034a4014031510342042940008124003c80d82c003c81000a1041a9a590411004203003502201d8601c00c00407101d03c080007076440c03c00c2145541d0b12110540040301203038058900d075403046880d034000c0ba098036040e003080e1a8840f80d490007409011110002c9038 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 684473767 1250 684472517 684472541
    0x1b09290f0307260609010306050c0c0a03080106120b0a03060b0607080a030b0f010c0f06020327030307080c040f03020d1e0605040b070309031d0a08030c01061401030b0d060507091d0406 81
    0x100584c1004400b0644508043c000585416129000900c905c0c0a050423500c1400a01040743c03620480d508005000304000e0284600040031201508002d94050040140c811401408450f8107031456170b4050050170081000d1303030041c0e41803003842e0101d00740d50041e01041c41c1a80b404607000c1c07400030410a5000c44a02e03000d043c450f40a9881c804110a0f0142040b0280e0111005039252103000d501c40324201e030700c00040d010301141d900307011140d940413002d1401034600c0c0d19034a04a456146a10b0720324001c0e13004010300c40c240c11074104054500090800e0009000d9069a4141034a01101400f403031641d250a40301140c0700c0c000d100800072039452090340000245001c0141d0201950018400c0052181c1c030721083c0c80344121a540e654610301c046004100d4101100d581d81141003585018000a12441001c1c1600b4003000101c1e500900587c4c00c884401007002c0107084160391540003c0070050700040070069101008100511203810341c448141a40c141c51501d4545440d160b0192030214042d1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 684475017 1250 684473767 684473837
    0xd06110309030d0c030c0f1805040e2407020a0f031b110306060406051e0a0801051e010503030325030605032a0d08040506030c0c070303031b09290f0307 67
    0x40702c10a80c4800f204508130803601e0b0034607429130406c255040d6070000749c00c540c1c0d000e842d050514444c0d40b00000ea8040a610010001002c03202141e504a0700000c2100c1200248e0040d0200800090702c0c040090f80d840c1c4281850409485036070b0920407502d0980340c0889030f03016405143d00c8185410018290300c07010031203042c4052410100841d03c284500c030200103030100c0310450900542c5e01d2207155800340421070020841860002e0745d0f0400002e87c000a919003155060010449060203c101c9105019111360103034466540400000c0c01600c2499013001c0583d0f41101161564050080c105001c0c5001c00c05035044801805508030515003180040c851490076510f5800600c4400a603000c81c3c0d800c5030314540385d030ba82104090682c850418000614010400007204041c0c1590080e50120307240502e5001518900d601035400d01c1c07080c020500d07030182c1640b06c00d19014621284008003511560801c5c00c00200b20700d08895500b05035036080104071904000e00071000800b40018040d1128044 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 684476267 1250 684475017 684475031
    0xd1803021c1b0302070b03040305040e0a02030f04020108064006210203100f021209030304020a03240f0204051017070507031e08010603051302030c0d06110309030d0c03 74
    0x201034804202c40d030030440d800c2d850104140c02d250090040314024060f092425030360746800d160050140d03005004074020248280d0114401d1032071803007620320440d442440300015803190f80040d500c000000300501d83c0080307030122402c2c0c0452100318000c628511600413501c00c0d442c5c0c661542c800d1001c81058100c6600e417040800c2a1000c0d03904e5402104040e94180180520a00119040c29500007454090909000c0d500324591060740c01401c0c502040150520180c4620420513280e21040c0d402a40c01180b040d0240081000c0e00740080068502003640002ea20703d155495064860445d00281400d42c0424200628208041d060301c10114074a0f09400c0800440e80c404110040684494100080402d02c002014061030103090344091110740e01c1101111504018200e4001b401101d0000c1d0501c0003194605c000b800480c03c4055005001e05640000181800300c0982912b0b4140d40b001e449218080104091034000c5001c0d51610340034680c1c0d0010402100282c0e168507545104140c81d00342 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 684477517 1250 684476267 684476323
    0x30b040e0a020a0902070606081f05010608041109060f150d051f0e060a05040608030d0b060f0f0c03132615070e0d080a0201062d0303050a050d180302 66
    0x300f20f41c241c2e4005040103846078100d0911000070030142e00f000915200d260441c0311000d810304100c6862aa0702c0a00340500c1e030302c1342004c071800360058070018001d07011600c9068440c0390500c1e502ea030240780580440100415400081c0c4000c1c1207181c5070800300d6000449502e00c1e00c690040e00c3d0712406810320913050740b8000e920b509000140d4030400106680c0400461403a0761109012801040018018011180c035034860680700d900000c2e2a8507410f1030811084041c1c1880010b5070701c400c0481481c20305003034454403000d481d80c1c010050204940420400d980b00c1c01000841c0b60090f0214108210201090140c460015805000e00a10583c080000448144110b0700020fa0010076440d18003082c1da01c51002c02c1d0072034101400181103200c080381c000303c000d605520000c100c0f4090b110325001c0507000d0200f45c0d03040240b0001072100420600c0203101090040d801031110450702e1800743d10b407504218172081140e411002e982064070b102c010328403d2643c1080210041c0101d103050640b5115059 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 684478767 1250 684477517 684477529
    0x3070b09010e10030b1324050f010c02030a0212010207050706180501030b010c12051c0b0603150a0305060405070e07080f010608070c081914070c030213060503030703030b040e0a02 79
    0x103042440f5540c04803c49140c40d2184c1c0041088603405420000740c2031030031301342001502d04210700140025014648441001c094200756044031341c094000802060018011030380314521b58001d0360144500f007200c0f4010b8507a5a030210b0f428080d0000141c0b01c45562416034240709451380140108084858003d0442030f030500c0d19400c03079a090800088040b4080010b17035240c2c11142c4040c0003580c40120f0344030170300d40100080c002c0501081420782c050a81e00700c146c0440f0303440798026401003001d000080948200c01a800c6140c00c000f4003000103a47d4039a9a24600302044504865030b41140e4002c200c8403002e180301a8104a040c10320010f00c0c68408203155082c3c60502c2014100004000813503031081c05010408026074108a001d5919120400d092410705100204040050580f1001140d07a65410090754025580100c40b101c000d4510303000c000d481c20b41298410243c0b9503408000500b076030f08100030290a4402d440c040b40c2105c03c00100710487c0c03102601b41c04242c0020a1070001a0307100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 684480017 1250 684478767 684478787
    0xc08011104030834030f02060106110a06050a02160c0914220312090b060a060201090305160201090e0f0604060806010b07170409140115051c200406050903070b0901 72
    0x41c00d40a015100403c4c2882101c12034000c0844c00e40c102c00903500c107041d8410f52180a0306296021180c05990300c11003202c01d202c82904004654010f01b200100060068001e42c0d017148a4040240c10a038200010a158020099040f07510300004001080742800602450080b8000d6501400c450324103181440901201d904d20140002d200d41c0e4000c2c105070144034030001d101e003c3c01003007000a01c103141c0f568502d50300b0b54034984154000240014050310500502060035815900c01d8146507410780c84460ba4040000100d06111010700c020401810000c0054856078140310201c4003820043c041c0006c807856904840b529030040801400700d00d00d07001c00ca034441079001c0c0702d41803010b00d004001191b86c01a07400060f845811300101d0506940c454040d02c2c141c1d80241d00818002a00d4142981d0703d2007180070303203803015400d46e5030300f685054103600245010300301d41c400c403a0358220b01403c0212039000f600701d0780100b4404039096035181400c020303443c05089000c000300e01c1c001d1250006000710610b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 684481267 1250 684480017 684480037
    0x12030612060f191112130c0b04051c12081909030306050906010f0e010f0c021e1e09070f02010e0d02031e03010807090b0a080607120b010206060a05011d0d0c080111040308 75
    0x503205c040b0320103008401010394040d4104078001d90304c64454610500d1a4080e00c00e0f648690015440c0c0c00316a814262410103890744030110019448090409030b4555400070148514440790610103003005c00c1901070313515200e1003984c00161040c101400c011841c20003400a0b4100000c4100c528010340e000712030035900309401d080c03502c0054641075048507500801200250000c1c0240c1c000c40f0403261080d04044d04120445100010a003200d108007440070300c0700c013580d80c02105900070803512401900e0000a5091600c004144146141e10551030813120008400043e0300c00146041c1003081d0550b042c00018004014510710352601e00d000d0b03a40c54250081c13201399903a4004d0403d851341c402d403602006040d514207a64a40c070780000c016040c8205104044071141c2480c40702c030440d44c408a0f4441c4110b40080070b10100c40c1c1000300440b0b0824070403c46100c11244031190380c1c1203568000280c0c0d0700178855000d4a15050404024500f0f50720344000301c40d005103050000348001240d90b4190707010112 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 684482517 1250 684481267 684481297
    0x317130b0d020408150703140c0306040507140c1615020c060c0115080318060a0c0f05010e010e030d150807030609170307030902030105010e0912030612060f1911 71
    0x11041c07601ca002842258451501c81c410580d06200301a103450200307104203620b48003004440d48450b6191545001250b84030340c2102c080002900910342503004580100c003070714000203540f25500f0f41c103000b07600804841410354070101c580d054200a510040d0060484490312107101581d0340c001a41c1c036840d000d2002c1c824000460752100c600b00941c0161800b0034840390080204e5030740d0340180c1d120390104010701d40603800c040355600c090400a0440716101c0950783c0d0002468015100c4c40905ca0120004940315500e8881d0b413448042d00340545941188954040e59450081c526034008a6021280d41c10885003050400c002c0944041405011603070890300200310321034140b07050140c40c441c006040c0c00101c008802c7c02025a4544e1141700e0092098000300401c3e62260780035041104212624031709503100d01550700018050708081e5400c503101604031080362620000c03560500b01c08554034984090b00c0c001f00082010407440461343e42030302c100c00300010300c15003c034518103101d07444508000394 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 684483767 1250 684482517 684482527
    0xe16090e0a06020a080f01090605011e09090501060e01080604150303141c021c0506210c1f09120b0708070e030717070605160f02060d14010317130b 65
    0x21800c0c00407452495022200715512000e6141c09401c442060711101c2901c0b5640c1d00120300c5540740d1040005590050711590b013894aa036400c85041010944660100512032078000386840c0c250145502804080e158020401071950006100c144020810f074412810008c20f5601940d03c14085025a40c240c0b900030001d11182c4417090691048844402103081d41a00300047d003405c650107018680440d0110544a01014803501d090b02c005403441d95000c0030380e40302913511142072116544c4942d240d030140c996880311180010342151724005004040601100804000b42c5c0c03001001001e07100403040d0300c48140d61900c070a50f1800c03004200307106100703917600810750b024000c84036803040642c02011a0501038888500900800f202d4030b41081510544030301155260081060324500c0710050403821440c5d51540340d107403945041c20300c180d0308035008014000341c444250140001c0b4a402043c00200c0d0351461504810541001c180c4580005003403001309202000100d07007074111040f801c0701903291 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 684485017 1250 684483767 684483791
    0xf070b060319030801050f031f0b1c0606030b1303050702040b062a0607170c0d020909101802040b031f0b0706060e010f08030f0f071a09010e1609 64
    0x100c2001084402e040d1605600c081c1050783c0300c0d00c024141c810a0350810b804184c1d51007459a40c07104c0d040244072001e02d080f05006e4074081ca5000d640c09510052040099244884a40c010140300320300640340c160303e52400b40107200c0c1c0020380303903042044104000d8011445803070081542c01007140003441551106c44954807030b51148282c0740b200c10090180d0799190120710045181c500f01401c0703421140140c000140700f050051543d44410f802c1100490125a0350519086881c3e0041e0745058404d0740c05d0006000766229a030172144640b4000841841c00c0e41080481e1210b420015440e0780200d00401c003d00031405554103903504049074071040c0303201c3d038240070711040c0c03004503900000d20841f00481c4000900040d49c10074412240301c04088070860340c030b903440d0412445850255011503031080000003171080000703004010b11810308d52074a0a2014540e900201601040e030802e9200e4404410301001c200203102d500c041c021203100400d100340e400551002d501c0c0592050300b031550741e03c103200445 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 684486267 1250 684485017 684485023
    0x203070c031104020409021204140105060a0b0f07080a020307030306090b1305270d08180304050d03030204151106071818060503100c0206011d0f091609020903120f070b0603 76
    0x20302020f040640d11488c010401c035100c035508a806903030384040c415030740795040010302c1482d02544e03000d02005011410720b0303401d01140e4880000303410001d10802c16580800c3d0002c0291480e03002640c0555511a03060400500341c41143e04040d180c145001c003030014a075240f09a0500790000c40e0310106040e83c845003810710040041c0d0210140850f010b07410b5040800100344902c45401944401c80903450745030380182107144404e58200c1c0c5610400c030074402803500074400f02080c0e100b0300e03016103011b0306ca8451611901c4000b4800020034002100720b000d45005015681e8000f00c10324100608000302c040c400310b856018401d00110702d10345d04200c480c0c1001380d08410050310020301100d070b0041c1402c60744c0d0000d1005402038030041c0907080001ca080031a400c1c41c54200c030140200c90030a6210507070b00781d000c1d00002d8410308040c4603074840c20311150001840318000b426941401a00c0f4110501454100140031042c40301d0700c001081440b6102d540c1c4820f840d80329401491142041d92081c011a107 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 684487517 1250 684486267 684486269
    0xd0806030319200c03101e0c0c020405150f04110c060f01030c051014090406080a05071a0702180a180809101d0d2f040b010203070c0311040204 63
    0xc1200e00e00700e1540c4500c1c3c10104004800c91080c000d803198003400e04806488003003030204c242d415000055a85801800c9802c1400700807a5642e00301440900d560078081258441d104660125040000355419071420b0301c10b40b980b06000310614160484540d001030b450720000140503118030759405400000c010f0326400d0f245885400d00440b1110304100442000b411400d10045500c0700000c440801c0c58181451904c44680280e101c80c000450522035004054005050349034216545d2000090291030422014296900400240ca4010704041c1c103d1022045081c1280503100208540d000503100e24692844001d4401c112400c0381e1103580740400070b010300c024071001000e90111101e040c018000000c2a015004549082452415500558401003a104405e66441c21000c0c40030302414810007520b00c075841440349600c06901c2c003c45182d078410400000a0320138112081c000c0381c1c04d0a00c507800c0c000009000550400c0398980d139100d02003501e8040140440c581840f91007858841d901520 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 684488767 1250 684487517 684487537
    0x603040f0339050c0a0609170c0d060f0c080c040308071110120c030605130b01020718020705190b040305160804030f110a0302091b161a0f090d08060303 67
    0x5401030b494007034410140d038001c200355498055004c444c40e09240000004044503820b40f03030303c2c000902e42000d4204110069080f003417940900100c00e02d4550719450f43c6441e282c46030a000078000b030719100c400111399600003100f00740b00e000c800784414026040180c0b81200d0340001ea0f00d80c0c420040c0b44c00319142d00000c0b480360308202c148a014205030b40200040c081d0700091001041450000a0110107a4410788036954100603035aa06040103281c40d00008882d0300180101e4681ca942e55a00b80c174502175491030b0a400c0c5a0124406003008420b21001c0e000c5008131400101502660b01d80d01c1c060400079000500344840000c0c3d07001d40243c0c0b043c98000d010342044d049600d4aa82c0c7c00d0406601c8507024040322844c480712403000c9503140031907401042c1e0b5006800f224850303954480220420f0340e2030041601070f03a010b00620241f02040800300500078407030030560f2012040780c00e008401c450060102c00796250b042e010010034103c0000c00c940c07420400c1c82c02e500340341c40e8140803e0451007840c4800c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 684490017 1250 684488767 684488837
    0xf05010e0c01120b132d020409060f050f060714030a0203190816080903130b04140d0302030304030e010e181501020f0a020d17030f060f0603040f03 65
    0x515640d000440c1500d8140400e0700d400c4000600307846404104c5820820060380030540d0403405003135400701c0e48140642e614140710440c01c0404c00410502d040300c1c43d44500c0303046070002800e10072891180907a4005003030444c00003d1550804000403c44480f40c1d070510300035000401d124041c82072482040c80000380600903295520b0582d08000e40381d40c801c220f1784281c8541c040039070000300d00c1480014840c666015858a91410a00085884101c041c108411500c4244041c5e205892000414001000c0e0701e00569030b43c07031800d1000c005c910300b982001c030f1082c40c00c00c10081c003294020007100c0e440380c2c0c14680301080715410b9005860b14a06500c940746c00a94442038402d0440e002051030f8002c03a00302641e5910190160012651340e50400400700503600880b44950050030034103540d00c1a00c2c030426000c80c1d109640c0305481366507042201c1200d101c0d8403820074440d0030705000c0c111400000f001d032502d919501c2e00352500000513610030001410040e552904a851038000301e03954000e03e40794050303 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 684491267 1250 684490017 684490031
    0xb011a0708220f0e0412120606031a2202030402130207060507031505030307170706091a2a0702030a0c060216092c010f020a170906010f0506070f0501 66
    0x210007000310303102c040d07101d961040ea20003007440580c0b200d40070121130b090142c05260b56250360f14681801401000142808080f90b511643c5500354001c2402030440b41c0c1d0001044544407138201c3c5d80c41d00507020070780682400c1c0403143c060390504104c2c030591043c081016075291901d1010807440706001100d055100c0c0701049010170091580c0185024511b160381c1403280412030286060004480d00c280c551540c010440800002ca00714030001e5205084c10b0900d0400c0b4090702d4000a60309504821900d82c5041c81d032482c86000301d05107003070f0001d91070403003885510a89015082e40b500350302142115081c2c0803132144115941040311031091680940c10028003507580c200a03680701030f00c8810b0154081444004282060030b4070506008401c000003000302c0c0444e01c17038521101c003030220f14450b0654a9803856201c0450750300040107100c1555448543d8880ca08041c0f800c80f4401800b1120b258206600420040e519000d5440c151101190440e680b040b803440c0c0540001613a0000a00c95401c1c624 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 684492517 1250 684491267 684491287
    0x219140d0302190e03030d0c180807032307030308060f0d0b061503040c1e03050604240e0a060c030b04060806061c0c0b07020d2109050301090b011a0708 67
    0x142010358030103c00c114102104000945080d2003128a4a030141e10510030304201501a4204841140460418031001920000444124046508902d2082d84030181c00c1041022038180c2030b5038038010206c010607030031080340d54a880f59034506c009004c101c101c101150403a03842e41003001e41c0320b01c01829140030804a2410689540c000c0300c1c114403e14948110002600024080740c7c031a50703101e4021410b407800d003582440019044000d800244184d10008400104100a0b8501960040c80080300800c030f407580200021708404403500009003000080354011000144000102d5801000031070340c040302900c220020440c2501199019040401c001500c48010a105000d84001e40300740c0038054032240da061100308541c03c02840e5800401c02088680c000e071018006051001381644014040341c2c880d2000070003803110034218441d030b50174694002c0b40c0001503580100400d03002800403850f50b8071800c00c001014070a801f10040c424944600940c01e55044440703941e4403101603610382440d10 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 684493767 1250 684492517 684492521
    0x201141917070212030105060703030617030904320c0904060f0302040b0d080a110a020d03180501030608030f030a0209060304050601030b0604050c07080901020f0f0d030f0c0219140d03 81
    0x3804103803980c5000700858801e52000c108202d0707050b12008801d145901c0c00e8180815a80840300582c101507942b00e001c02c4940f21380d4100c0c0320807801c41c070013145c44014850802040b1903406128460300c12140f60541c1d0484c407500c42d01c0d10034020010075580030365242100d541c3e0380c0c4103036030700154000c0c40e0400100e010024071020009890083d9800c011105400e424001c1200503600042d04002c028482450440c5c85000f0010b020150001604d48001e40c0d079011800004154404501081d4409040340d4444000c59007100204402d28060010501d400d40c599140d10900c00c807044400000000100703948441c0c3c040740c503042c00151120b6a80e14140c24020348400080c00101c0c0e9804806c0c0120f040e510701400303010301804101324130628280300c40e80d440c455940311200785410760284080a0311041c80602421240d4070388803015054900900200804454228003c108001e19040c4040003580d400251045140c03900e4248640b0300403541014200d1400b00c16002420f4840d000080d08429030503 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 684495017 1250 684493767 684493787
    0x3030201050105030d0c150902130209240307030b060c060405010509060c0a080c0922020d0f0240060302040510030e060408030a0f020301030609260702011419 70
    0xa50007000580d0301c0d1001c25171078081700440340c3c00003180c0743e9900c40898805d103d034500544101000089443d0a503010800e00f101550150081a0b40400ca150460034180705003803588030004200781c09420000c03c03100c410b000c007030041c00400d980c8a200e50140d440b240100c03180f10742a80100c600310b281924009019060888540510f4000d0101041c90038034288242c0d41c20f10203e481d0f40d0907582d81c03d072903040c0035005034844a0740114000c0c040180440080400244050031100247e43c079602e207007904054a001c018a040304510401106180d2860109441520321400a5035040b50110b02c414024115036020304518080e480304001801913003640c010700441e003080e28029014840e03002c0a80854440d034405005540044000800160b15800116071110301c00302c0001d10030840924000c100d81007600f00711074580c3c0c0d5101801c10301c064004900c42485820f114080c500951805816a9006600c0300034107001c064991801c0ca6408a820342d07610590304880c0441000c91054010300e40f400b1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 684496267 1250 684495017 684495023
    0x5090a0b131806170321070903120804021e061801030e0304140a0b030702060f04081605060114100c03030c0c0204091515050618030304050603010e0f010806190e0f0d0903 75
    0x400310f100d001384075012003640c4007040030505e281e0311801040102402c0100040c4142e0801188542c0440002c100440711011300c240c1e036903141510303d028414071410794111074201c814a0101d2600c0f1016580d42811540d81440540c132884008003020010303000303411502900c41d5a400082004514003201ca0301c58042c6040031075800940c140d60307521100051006950880040e00329400007400c0c4501c90540d1600180304090f41e1385081120001008950b03032814040700d19030030840c0104841503661407a18011179085078914280c5130416000303422519075050003802c0c1911820000e00d0a4010a068181c082e0050410b12014405240255140001402e201d2204c0c0c0340140c00000c19240c100104181c0300050841c500d800c00380050307080000402c541007a40751104110111f039940310500130b14001c28084818042604240c7d881c0210748005030059461a07000c00d0800078030780c1045410407820f030302c0504006491000120a00e0401107410114071141c072902d03907203400392a0303c40c0c00c2a0807680 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 684497517 1250 684496267 684496289
    0x30405120702090112050f03130927020907091208120f070212161e170901140f0c011d0d08010e06270a0c0f05090a0b131806 55
    0x814460896003070046040194110700c2c0031005001c0312201840c00588039005170100c0d2403840b03451100e203180da4050242c003c280e100700d010030410a4118000c10a03691210070760b112108046240b0140e001a030034401034440e42d640e8001c00d0328640101881800f80c043c040c0b01040c10754050810708150341c403084000c645844a0000901c0031091303409118025242540640640011043c6074056600045400548440521200000a8130f003400d51820071000e0114104100a01d06040d10f856441d2403009045103010000b114460780d002c0049802c0ca01c8014440b5201c402c03502415080380200c00e80d1104a41c64140c40311141007501c0f00c00303106004594102c03440c8841e1319408958031502880703224841500a40821264546240440b44600c07446007030045205c00c8400c40c0c603000d001910104505642e41c0b2000d40e046510000f408070403081820420718215001021032403004c0c092142060b584008140c3c480551420509080100341141141e01244c08103003406000b42111710030320070444 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 684498767 1250 684497517 684497533
    0x150711150a020d260a050601051b010e190b0705180d03080a0e01060308040527040f05101e09060615050903060702010603051020160b011403030a0311160503030405 72
    0x200124460003801300350700e00c0d00c249917101d40b44280050200506100d0511005005012140c520300c05240701d003100c05800440c12890804c0068245010a90600b015094071840c44000c60507000c4030b00d400c5031107858203664500710980e001c0400c1c43c40500c02980140141300300014940d020421034011850100b080041c1001c0c20407044c00c840702e612000b0b1a0344c03400d1100b04214030f060041d01c400e501d0301d2120b008201641180e04584c100084800310340001ca8240c0c40c00c1030100c01c004841c000b40031460200072944040f0f240008600306019141644d0703407210512810072015800040c01040c4a0b1a0641c0300381c41d203140588950086004680a4459600000d04a5205000b120b0860780c011014002100c10003122101505c0c1041540c074039926809072000240408500401908011919616031404036240441c9031000692081c480405401342e41c1c09e245e5001b100b10b4005103224200088c2d081c4006100d410b450040e04006480032602001f000240007002c80210712a6124000740c400ba0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 684500017 1250 684498767 684498797
    0x1e060f010605090f06130b0a091814130203010f0f06051503040f0b0a0219051c06050102030301061115040302070515070807060c1e1d150711150a020d 66
    0x901440d145141d04c0600d103400a441401d181000b0101e408081600d2620641c40744542400c0d41c3c800005100000c00b510410481c2509031304000c0b0458a5040c010300c044130511121101450b0040d19400b0145807448030001195825442103000c40190030080c0002d000c554015402001103215581c0100c40d00c05a0098004000044034802ca6002c880c888541496407103009031b42200403d003007503030707035007082207103500448130301000402503032551015581c0c0603c0652001c01c22503012010485424100300744100d030380202c2035230b054035003515090030302140c0d0082640c6828410180494015552014041415400b041c80c5060798020b445451850b125514030754403d1042d4500640000400c2c03103030800052207504090018031441c81c01e600040d04200f8801400a08035060402040b160814100601c1c22008280e100724030450310b445029810034251b110b24407548400810f88030081c442040b00e07655a040402440d58900c5c0710341c0c1c80e401c5a244c0030b0350b00c00d4000c85a001041ca01130501c00d01c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 684501267 1250 684500017 684500027
    0x5030109121103040e0f010306140405150901020702180930161a0405120a120b0a1701020d110304050c040f020f0f19020105061e01021e060f0106 64
    0x200c25445003890000c0240c1e180c0840707103124407124106842c0401c210010b084c422800c038060082039100000103e5514600d8500d00f00c902d802c1070040300050303400c1000041503010800030401c14940e0026440d503a40c0984243c028030802034021b44c81400315402243c180c0c000380300c1074071401c00304013103802624070b000422826041c4080b031101d828140541e180300d0710111034081e280003604040d50112182e42982d070183d50000d803030654207106c0090001c0000384082000030f5140f121589210b00d00e00310034003500030881d0301380140c08121980c583c60a00345584656020030001d00508901e0b078100380c03451900a001c1d50090817109041410580503040460200e01100d009541c804001e060048410051201030500410409007080e400d2042400c0d10710700c00010300800300c1c2c10054617560940d002c0580100f00440e107280c0116031414040060079100c124041e40c0c40ca60003041c20f4407169042004070300e04564004000200f40040035131844005000607041c2c02521780304281d800581c0c8034841129 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 684502517 1250 684501267 684501281
    0x3041104091707021f02061e0105101407060501170601090c0516050705030118060f1401170307020d0b0f0609161805120609240109020904020714070f050301 69
    0x26a4503240b0060410614024a84248080d00c0c10044049000414650300303036140f2004090b801103410450320404008500140b48000c2e0801070782d0354140408560000611058402846468417502c4010030701c41e0140c034110f81d4482410b1080d980c41e84100394040c41d02421080c40e0348550400862110b8041c002ea0f0350411382941e07261308007118011030617805406003000b50340038001c40a0201ea507803401e0085800031000346001032480351040c80c1c034034215065648035800f40e0b0728080720100d08140c5190030a0444c2d0718071800301c03065060050258154070802d08025032103416407a00c030007002040084184107402041c0e900038156660702c1480003001084070309400b020b80b40c1e10651022402105112000c060307024079070034141d4503070b404100c002c80410103034005c0382e00c050200124150b0030811215030001090001c03d00b40c600881c01e00880c40e040c003405074600c0d00800d989031241c44650580f52240c2d040740740550f015480a01c00c60715050b0324010881d0b1800c41c1d0601140500f01400743c0c0c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 684503767 1250 684502517 684502523
    0x31202070206030f1f0b03160219080703050c070e01090f09030c1221051005031612060b040203190c020f1518070617070e01080403200a080304110409 66
    0x62a640d03031081030020034a0028101144107611161a04c405c803105002c04024040c1420242c0d03070307420500d80000101d000001d44104551003e010900900a40b070444840e5941c4100001d8550001c4e03c4c1c04e486501803950080e40a03c11804002004400501c800341220140142001090041541ea5058a02e841030180101e40e8854950000440c10140009001c40034580508450305c010740ca0b2004072560308030002c081d503e030310038804990f000c00c1094006000c120003c01d40000c445c544455419424459a20600c00d5640c6002c20b21500341c000e83c240c0540240219920324042841184a016460b01f90703048034680356069803414000a4510020100c080040c00c0629a2080d035008000d40140081001002c0c08a4008650800c01a0b04007806640e208d02006880c040040640d00100408035401c0060104014a40c0d0340c0050385150020381524102c2c170a90703000c03244007240d0b021100703542000b841184d000c0024030401e00c001e18000c522440e880141140c8110420040d02d140720f00c05 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 684505017 1250 684503767 684503779
    0x30f15021e09130606051218070305030c07060c030c120318050109050d051c05150607030206180705011409041e09031202040b040b031801020a0903020316240c0507120312020702 78
    0x700458038210b00b1f00c0b03601180000485500010b2150514185400e40c0e20486040e0320102c0d981001036000d000140240c60b0610301896a20020b031002411000c95402c060641409035401ca04414403d81240f4140ca40100c103107248a0200d160560080883e0700f402d803010701078100e01c00195031046d000c0300c076560030b2000118840e00d852003421004041c081d052800c801c0d030b0096134007400c0d11041c0162806501940180400d841c00906080172400380c1c500038080b0341c00c0040c041c4000e0b81c0080717030034804510880015445c0d041050100c0c0080075200264900030141d54404030662890390000c20245100355601100700c501c4008003c160b01490141d40e0760044240002d0080560b000051a40941d0f04d420007010031907100e18860883c1e020300b99000004000340000d00960404101180006803102e640088981c6080c00d040303540e4450284a500b110551000a40c480c0e00c10180700824640000039210400e0741c40c42d080803550070a00301180442e241c603d02d07849031030061090f130743c4003034001d400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 684506267 1250 684505017 684505027
    0x203010f0b0a14030106031e05060c040302031f0e0a05100b01020f0d0806060d1b1e09092c0106090e120a0f05120a0c1107030f15021e0913060605 64
    0x403d041c501010034442c3e05590786140000118010490341100d03460380c0c00024040e1881d0303080c03032403d0074030040040044c214200401c000503100040e6000a0070f05c400c848510080310314040501406641c0c20030032286c03081d620300e1300600c0004100d052040407240800c0050060343d00042e80c44520422a0500c903400102c40300c001c503401a00c0380d6610110040c0360340e01d040c8070034180d001207524800170210074060314940d44d2006a0000000d00803100702a46d4010180541000107141d440c0350b008031140780d92100e030308402ca04080c0c0d203405071001441d10041c07440c2401150780c500130139180c40f50584540c140302c0e003039510070303004035400321540c1744540c0840c80e040204800341c0701d4855001188003003060030042d000904000d09100740c003480c8204030200307119610a80c0102840b03407001403044540c01c100c2c070400000c1e011040c5900740591200c01c10a08821421040000b40182142204002d40142410310b64842d01002000004001c450310607415038403100041c1110301da13010304c3c0e01047c000c00c1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 684507517 1250 684506267 684506279
    0x100504150b0c03090303030c0a0212030c1909091e05010e010503030409201b060a05060a0306050a090f2402040f05061e0d06050f0f0102030406050706270203010f0b0a 73
    0x4051910b50541100d1501d4000c4e80440e195520403a402050740902142160600c4da040c0200505410449801820f60030800340b000c69134418081407030464950712441900b858003c90a0070010200c1001c10409801c0b1000090944000d004510350b0080c5490300101c1d0b1100c1104003e03050303800290041d414541403428140040503c1c03401000c0e8a101a00103034590300e00d00c801050510902000f40c0342030584030726854980f0f00c000c0c14025446042200300101e50321201034441c100c070b4100e032003c03031561950310040c002031082a030302626564400c0c00780b400384080d480018001012030100c0c0c400c4800003c9954040b4090360240d40d200e51017035841000303e4070300300001c2c103012070502a0000001510458154560340204e0b081c81d0242d0315400d08016920b08411085420413040d40c015a1114007000001d40f20b00c100d003d00302c10710001042c841c0130702c61a0741c045a00c056644043d00c2202845001c5400b51303405180301244207601342071403090103080c1c50080c54044074014003508006803d00d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 684508767 1250 684507517 684507539
    0x301e0b120a021c0206030a0615030b030c010e190306050106081305100e030918060a17060402010f090b03070e04050a0c02060105100c170a091e0b09040209030d0810050415 75
    0x10a144240c00fa42c0305001c80503940b048011805600076074030028141d46080b080b480012284041841454030b00101061162004182031401c90001d1070f01d1034107a07480000061510b01038903251400a600300c10b010040015035402241600e1041d1120605544e03a07082380048070040f58801080ba4000e40c5e0034140c000c0440d0003140480b01c1203c00e42e41407070400000b140904001c03000f40d4140034000410b00103a8140740c00650003815104507a145681c484200455171040301800007030401001181e008049403003500c1283c00390a42c510019624184502c2c0101400c0c00c184049214602d0070010a0003c074642c4503180000721f03190060440c980c0b8010400100c40003002c2d0041c00e010343c1c3c1ea5000300007841c0072400b04440608171041c1e61650920f0400070a60303c0640c0100407401503849031400b0f1200f0540c400d030100e039192500f0039038942110021034013038003035031509039090f10904418862145d0828241889201403401100509649804002c2940d40e050080b504060105609000a070810 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 684510017 1250 684508767 684508789
    0x315011215021213060501051c0b0c0c07090906140411010c030e0612010f0b030910020307050f03010902211b0c0a021005040608090607301e0b120a02 66
    0x400001414030000c0d84080070000b0f801c0300c0d03a03c51100030440b2001001030600c95580036010a0340c0a01d42031003605d0220030f00840b04036000d84000c0e481d10005100c810b9200489440051140c25200401d0b515000d02001c0c22000000700c44039410318502c0b0103c8421960814482c641158008104e060100d0064404119480068040220000d40c460851721400300500c9054640c0d145841198500f80d008000300e00250016903824200b00240700d8030500c000f949181a49072a480140e0300d445a0344180c5142c0b082c00c00036452a100031000040481041d0b0281c101c0c019401c2d01d42c10a0440701e4401c122402040700e802070509041103ca030100410440584001c0b1460390440d10580c0094001950340180e8203800d4001802c0042c0034020160f2000006803c0b10202c0028501410402c501030841c4034403810400c8118540c40d00c0780c03290080ca550340e111095178070408001a4030390703c40c4001c03145900c604102e07000b0304240040c5920704040c214041641001405081d40c0344440c0d08000340d20b005 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 684511267 1250 684510017 684510053
    0x1b0d02070c032a080a030827060403080a0e010902030607031e02030a0b120705100c02060d1d010c090b0405010809030706110a09081b040c020102120c0903150112 71
    0x545400440000d5074a80c08002c004040210000110b501040c80035031400944c0101c1d4180d00010030090009400a0046070041e500c241c043c0c100b0320320000420003d040c441041d83c0c5070310464080c8801d05400030b13803040c0202c00112080c801078140110030341c02d80e081c1c00002901940031700300044238540300307612050001e00c0200c694003e40303412400800990b041502c0c00e403503041d80d8580190b011700d41900101c003290b0364000038140d20b515180000d07088000440000f000e2000444d0076100715560700f021101a88409902042520080b11380c40000c540c3c600c0d8031050070741c81d040040e032803940228250400c85888510140c41c203400d200044803902005044200c06100a01001c400249070b80030b1680036441114140d51509403607140280803003042c2e4032070b0000e41c0042403504264034a00070541c200710310507540414244401c4904900a21401c020380e0034108088003070148440d118001000700380406c80c11561450603220803180e00610070f10580c08003081f00c842230070000d030895519103030a00c6 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 684512517 1250 684511267 684511283
    0x8090f030a050d03180c0302040b0f0405040b04052406120114090c0a09050903160203031308070807060509010203180102010906061701110406020d0c0c2c1b0d0207 72
    0x840e1800e20401e208075603a400503400041619031510400640c036200e0902100d240300e1039101e540002803580406400b494440ca00540c13142c031080207140760550040e100308510303c3e060400655100050b0340c1200c0a0007907001600c1511240c2c074120b00d81034040d00c070405064550f901007188001c52405848690b54031041d228072100c462140486c451031011010b00780c0341002400300302500030a500a07110a5140c1002e00860240001c296909140c9503190102503401c1800064a18051950075900c03e018281003c90a280b012440000b00c803c4502242c02d842d0b1202800e5400e4029104400d005a00510088501080a201a0f80019810300001600700d10549480c01030303510b180c0003000c2038404112400c1d070940003441052415a118041c450400d414204000d490b030348602e000ca8201720741c040c0304809205d140c0c0c040300300034080004a44441c0341300c500f203027044000c2a05c407411b01d400b0580000e03034ac0103084802d403084150200e42041c40c0502850f1190000e400295094408074 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 684513767 1250 684512517 684512539
    0x1410110f01090c1503020a0903060c030b060307020a050c0306060d080d0609050709060f020a030e011206090c2d0e0607060b0301050c040f0803040f0504110c010c1d09090a0809 77
    0x5400c1c4512150b2502408550707100c9810000c0c40c910341c042004020b0101441004402459036201e4400e80541c2d030f00500103c1d40d0140903800302d01030f05079899010341c484400402d000407242c0004000760381038441d406540d26441c200c4101525050102c1d115034001613160009000208003d004185510041c840010710310f0702c0c0c000f080b0403101304071124400716010b03060030b20441fa08a2a42841c0680c11c1c4010300344075600b594024034003000310350001d0602138160251032002d00140c000001820907420f003000040340481c00100a020915162035448011000320841d038500401d0300748206030320341c036800e200c0c042c031000744000e50b4000c04046c0d91103641e0b900e50841035a001c0c0150f50043c0c0e40201a95140d604052800714003107425481000c440d881000200a15604401c00c403085960440700000c26541020300703408184030750111039945501c0e01e0503d0880d039400c00703000041020820f40369800c0c89800300920400040aa51a1007298000311082e00080d594000416020130701820b413070590303 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 684515017 1250 684513767 684513793
    0x2019150501060c020a080f0705060904060e04050d170103080a081e0f0f07111213120614150d060c200106210c0e0912070f0c141011 58
    0x15482a049080040d4100700c0d60419407910740c0105c0c01801c002d002070b1100f00340c0145000d59a000c070340708a81c0510300100340340085d0341d107c0c0c2c0035400070301c4684034540c1c40d880c03e45403058940004d10000c0c800301d8201c91010440040c0c0f8102d0034142c81d0b01c0130307940c1e1a103203aa20041d500544010004055800303205242442440c940a103039010302c06d007201e40b400c0c50070456001020544d00a00d01d404001da000e12540310841c00003400c4034000d03c2c043c007850352214412580803545410740c10034201074440309641d03c20000298007904504408e4841c60300a91a0110301d0182c9075a801c17039280d403004c9503100d208045401c0340c0c0040b00b60a840e04001c0b0030112448502d94039403569100521076170f5951201003000410840481d01d100e0710308924408480f000742d45910f401029030085d42c0009071403100180c44e0460801101108141111034141c5417812403034040725866080c0c03c00c075030301c0522190000b0310b5100b4000c0707410203440003481034019087c003070380407502103440044019961250140741e0000c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 684516267 1250 684515017 684515021
    0x602070c180902040f020a020d1b120206070e010e010f03150e0c0901030501050301062904080703120e0306040b01180f020a110d0504060f110a020a090c201915 70
    0xc11521000100306220b90340100000c0b40e80b0b00c2c0e0264170036401000249150356001ca41ca02c5008142c3c10601791012242c0f02c00107550102000060480800141608426400243ca9072154006965a210303030f90708900111402400d02024501151300e8540e03000620740a50043c900c401410a001c02410b0f82d501a084003002064801144911000581302c00c5035074180205809008150000d03c0011718120030f101079600340c0200510100ca01d070001007030010804049134002c140c08000c403441540c0303c0c10540c00d00e00b45d045030900407032000203900f01a8100880c51a116030740154601c0460307031900b0400c415101d242c8030104015a511098101c030f4200174400b0b4001d901d65680d560441003004600d10303243c200c015014000f40841840304200681d4407030251244c1003e107240c0520205c02c00981e00d460446140c00081d8400c415900104d40c540403640022144251995402c810030002040f030000c1c9628002251703c150414080707981d08410059002c04424800c0850480441442c034102d81 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 684517517 1250 684516267 684516299
    0x1f080d08220f0602090f0a0f03020103091a100e09010e1b041104030c090b0d0b0c09040e0303070c11040605150f090607060b01030506010f0e0909031b0f011a0d0602070c 74
    0x1c4141c0c0c040b401d0803e609116952000340701003582e8400240c1e09152300c4140c00d00013440000c0c10191201c400e0000c000c040903480725000111540098070b42801020107041804501030710507480b008000298014205000d2000740560180c082c0041c400c0080140112015076110b940d041038840c00340315480b21048005200444c061544181503900f03040202040d2884010141d10030700e807407680c16000c246400d0385107810851844407180d492806001140140c4010a0080b0080c003011080252854018844407001403140d8a45040c0e03030081010003040358241d010301c50300080e80140c140f1440e10008014480400045d0516040c401e02c1400943c1c598800802247c036070340c03180780d1240075580502500e50000c400b420001501040d40000900f0710410b4030000744202d100b035021450b4518184216010101c4980b05440f00340c031030703d55441c0c0c0d41c40c0241d00700e02c0d950310b084030900d25101e0042155002c2e85000705440b10344035030364403603e01030740028205880c0e105a8101c0060016407610003a1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 684518767 1250 684517517 684517523
    0x30219020c040f050403021504110a03050102031006021b0d1505011712040e06040527070e06060c030318010b031032011a0708031f080d08220f 63
    0x3280000000d414001941c1103055041c1c03c1e2420701d41400000794010030b2181c0c0030840c641c1c0070704250b40d407410960010300203111103d070002c1035842c0120038040190001c0d8407400c10107031100304d5155200700482e81c2d003030000610481154140c03695100da00d00000c0700403105018960030503200c00500114000c0b41d6080e805000342111058114625100034814444500ba81c004230504103440c001d40380310360000043c5000e118a0350f0b200010f201482901044c601c00111100e118659a9414502030341c1c2c04441c080e01c0029086000007503a0b03868000200e6064148082c055800c60700e40091001000032000c01c0c00f00c240d501c80400d030303100e500e00b007140652031084013402040a9a2024039103685040101280b482281100c006482c0c002c0511500341c1103590082000300078180e032100a103040c3c0108100100803040c000180600c24010016810352410f000e4400442d103661001500c1c0d450b94907400c0c0e040492411800129105c0f503507580c2540d80c5010404020b620401036480c5402100e40500132 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 684520017 1250 684518767 684518773
    0x10e030903070e060603040314070606030b090729091f030203010e1305150a02070816020109061e03050612030307030608191e02060f03010b0405032a01080703021902 73
    0x10003949030820200c40200900300c0c510b01103083c40c0c4003080e072501c80100041c080c00f0215036542102807030302e41101c03500e0703800c07072000c106040d00c929000e1042101600e40340703601e01c90f180002ca80b407407520514004c00d44004803824065204400d2080240d001200e400b1f5104020056a110290500c07c40462052055800694941c107265244030482405450410f080030355411840002d0400100005024184680c07030500340c0d20910640064416400001c0c081c503808141c42aa000c004071a1042c2c0030301c00d0700e803403162546031503084a07548400745d49001144508440006014080d030b00c01a0004000b5003140ba0454244414500e103a0041c0c6150300001d5450328208520b484c10300404001e41c2c80400f55071101807094031500584140b418070b80c40c10410b1030902c1300865850b1400c8808031552591141d1301c1c3c0d80e54807940216a0014880c540c028014240b030001c460119000c20b0004241c16100061031840301c1004440d00031000304103105240d0300700070f003141c41c5c851501c4e65400c001182d070003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 684521267 1250 684520017 684520027
    0x3120409020715090f02240c0c0f1c0f050715020a060605030607140f130612050a02070804060e13020d330618050a15170108190311010e03 61
    0x1001140f1a002d4064000302c070726020198001403518803c4520380f0f901100e25800022940803051a481800d082192a50500050030994a90045190154000b003240c0352020200f0203001d00884200d00004410844128051900000d01054403040414041c000322020580c0b5541480349820300c03200440096030100c2048410000c4902905014060540140c020350070a00741c09492421300603034100b07805002158101c81c01c00d4503802d0300e8132030f94030319406810980d0320100645600d130f8407026119520f0038400025403010351402211503045e404889280f0701858400120780310150740810691000401c81543c1d2544424005002e800b80250000100700025812502c022a1840382e51342000c2041000744a01120080d8008212511418052100c02c48000150b080d00e0142c0c110507402114010045811000c6d200540100b41407a01c6202d40483d00302c0b09640010340c2441142490b901100c0b8107610401052950300c83c00e8420b04020703100601040e011400c1d100381090b031040583c00459 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 684522517 1250 684521267 684521273
    0x204180b0f060a0c050a02030a060212010605090a0b09031906022a1504020d080406030209010e180a0c0c02040504110414010e16090e090a111c02040b031204090207 72
    0x11841100c0442180c0c0c4009007407904012401500070a007280052003d169880700a0081c14840c88080340c1d4000c0648544c1c59003490402c00170f42007103941140000d4040004100d40c0d0091040310641c1c0d03001070404050501c0c0c4188880c00d81d1040c080d4a4040c003d0403400400049200201800c142c0f2501003d41c42d4a50740b1141d140c0301041c00e141401703c0b2584200d4911840b0080356000c1080010230400245541c0c500100e114072030801c0004002d9000024000380f22a410781c050203d6100981e11801224484001c00440803510503030b600122240401250900000343e10201030300065003450f803000f42203078001404840c82184c080e10103d44c5550400070074500380c8103e43c03400c0030340d051000c6d4035410824056a00e40340103243c604201c4400708100c031114018629a401040c9003000080d8a2614043c000d40700c101500084854040058181446140c071420380aa030110b01079820100c45a1030b020070000c1c1034401e0300390b03415005501e180103681c1003020003000502907040d0056500c5a581c5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 684523767 1250 684522517 684522521
    0xc01020606010f120c270807050604053a03080906010f0807170a02040c0e1801060e01121d0303010f05100816030e061303110f07050112060504020418 66
    0x100700034100410300c032208004a0b0840d106980110303080030000fa070075540c80c4054500741c02d4004010340341d06107240d00ba80d0307014420100400f91180d030740079900b04036656818000035010b10b0180c0c80c0c2c09148505020941c0ca41d0283c80c0320b072442031040c0260500c248510603a44125000015000106008104040d9034410000d190040c80c1207003c040400b443e005074551039076003034098150400b66402201840032402c02c41000ba40340c0090081082500003007015207942611205c00340600014600e0014501344003810f14100c640d1600c40000344014180110b400300901400031504640d6100c08203060b040c0e0b171364051040c032190401195603504101c6d04000d4081580d008500c0707009000e0702104400d92040d84190404006e02d00182c4909012500b6070141c03480401c0001c00e8400c0c1801c01100180d40500c26800c607000741c0714401c80e50300504100303071905004a418142640309102c100010f505c5206030f281c440002d1a8005100350312880010180d9020360700000200c50040c0ca108601d00c024 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 684525017 1250 684523767 684523771
    0x210c0c09021308070b0703050706020d02040e0a24090b0a0305030a02061b040b0a0c02041808041a160b090304180506040b040c020601060e031f090c0e1005060307200c010206 76
    0xf80c0052400340d02d4041c41c04401e1140d05801030170004041103250401c0743c1501901c104034002507042d5110794480040f61000702c411110704240900f00b0401c003840c1415900d03c1d250600c0c0c508201c507800341c00c00b0410005130201582c000d401031200350000000c00c0741071011b00010f11166001e441079041003a920b083c551001141480c0240081004216020104045410400d06820011400041400020300800342e01c1e10584a201042c40030500f08440d880c001c0c802e407060f2001e03041e03142c1c110100705007850099038401c0100070f01c19028a00032504c071080840d030169411007102c1c070305038039080c480309041b40a4000800240c1c84400f40501d1b481d060089880c02c01065500300316607800303030307900941c3c400d0107104140c1400034449502400362014000e440003503a40200032b0074036010b01e1700441c008044a45054a040101a8000c10000c8200f001b80c0c4c01148a0b00004822605003020841c003680042c0c048001c2c080790290404524500b1042aa090412031026059806540002900301500 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 684526267 1250 684525017 684525029
    0x1d0f0303060a0e0106210f020a0c12030e030421050f0d091d0f07030f020c1005010f03050a0b0a140408030703060b3405011104081603210c0c090213 65
    0x1c000500c51543d204081b03101c100c1c8540c0500c2e10201c002c170003000c01400d880f001c00c82108d0002403100303032140c0c1010000340c130103100b6020115000356942d400c030103ea085003940c28072a04100000c0180d2212001c01c1012a502140c409403540311a81d00d030352500480301d201013115001943c80ca241660441c0071309000b49100e204580d803002c6008009048850700038907007044189414041806544a0341c40300040c443c0c899811560303800b0410440d5903071841d60340340d00e00040c1020000f02e038000503910500102d07607000008111058480d44e600c5140789000b000c440f1203070381e2a00d035071043d000d951414901550040e05038036503c1c1803a22004094445942100d03803041402c01c0700a50600090740704045068a452a100c16040840c0c00390070380c00500c0314050050340c01c283e00040174810507801803046903500c400715004602003070644403001c0c901e0b110103000c2103840c050941080694151030300d8440002d2829075001503d41c2c1d180c9001e0700c1c0681101100a44c0400d04a002641038084d02c405414 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 684527517 1250 684526267 684526289
    0x12090501020c01270503030a09050906102c18040b0609040c0611120d05070f08041e080c010c0807020d110607050f1b0a06061203080a1d0f0303060a 65
    0xd0400103842d082d2140c05003130b185428400d0b01040304000c000380d00c0182400138180ca5035580d10b000c006010710f02a000d91845003c03046c02240b094500f102084090b180d8507203480443e81c2c0488001810084c41b80d0351080962141c60890000f95141c110340388843e840b50346a80710504050509001c1d800b401003010b8002d07039400c0240000301e840c81d84a03000301e80321468145a21035402032954100781d4050102c5200000100b0505c04140ca150405031083c1d40660712142a01e42035902290030f04d1050701d02419460544c01650a0781d00c90307160400180f40144403180c98000c48811090845a0500320301c4001a00c101c1489016039040c001130034942c0003460032044440805207100d44508001c0d00100c00e200b0300107407000d400e41c3c0440a80b8194440040807910b01b400401d240350311010591001c6074120329140c00400c3d01143c0780080e4a0280c0c0507a02c0c0c8019a54507443c10000b01285006040107203c803601c03044003120104600c0d449030318000051a2282800014007090a0b41c80c0c1018007005 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 684528767 1250 684527517 684527533
    0x204030c1823070203071406060f0108010b16080405030f07030309121a04050703020d0f022e0f02010e0d0306231c0201090e01150e03010203060f28031209050102 71
    0x303400342801e0642c011074000041c6540c644110581c514428001c00401605c00e80d20080d04415012418920501003541c0c8054890308090045030740d41024042e8082d070381d42c14880c802e0780090b581c514841c5a0f00c01e85c415490561600c000a1400c480f2088103402c0e640100f2046c0101603000b03060300f0042c6980702021104503015581c01e643d51011039408043c0c004520000340c1400010041c140056401a040c07075005901802d1034084001a10000c0c0d0154450341c500120444030020210b0358600c001005c08280104100220341024000500d1400c45d9201c2c608060030340c4003071108005421040c1c800165581c40c20f00b6085484404e003004511b602c0c0f10201d01103d0f5194080f00301001a111005034200280520040c3c4110341d480d0088854040140b00105070300c9540f82c0e0200e031400300c0e922a5034501725000101400d0b0303c011181c1c2c0ba008008490521441d060094004008091113001c000040c10410072400418049070f00c241d960f2040c90b900c42d8900c0f80c00000b4100544001e00c0548208 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 684530017 1250 684528767 684528791
    0x301020f0901030203061f050a0e2b03111f1805030906030c130b0a020f07150c050c060a020114010801050106050f0703030f0e010c030e160b030907090204030c18 71
    0x107006615415040c10b40000001d45150b88001d4400c9100c16000a2118482c40a0030010078a801894030704000c20280c80310206186480318144070701681111040e045001d00c1d6400c0d00540300c45120481c02e01c810f1903a00e03c200f01052000b149410b50104000507000d04221820056a01807030b402042202c141440c000402c0b800300c01c40c4ca00b0401916160741e00d07254600031560038811489444450800c20b44080381c47c0085070003d101c0300545600719080d40925001c010b4484181e441101540e10500300c02c0c14401e4082c2c102d015480740030b207064551220446000c030f0410352001c108000140d54074074440700c0d04148401d07010301401c0c100000308260340c1002d1014041748034401c07130104d003080081a0b080406202c1d40102172180b880040a0040e0038440c2550740c0a80740d00d4040202003030420b6000b08200400290382d100341a080c14050003083c1ca07003480302d2000c0d8005800400c003805002c0300455461024001000194070540e1803c068625140000302d41803159003600340c00301d05280100e507003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 684531267 1250 684530017 684530047
    0x13090c020d031b050309070f1401110313060f02010209040e030a08011d0109020d0b06070b010f08030f07080d061706070207050d03021005070e130f0b010f0f0804020a05090a0203070e030102 83
    0x158403d80e04141e540d0b030700c4415400d80743c00d060364080c9640302a82000415111342d815543c0320340c14401e80382c40b01d82d54104031012b9224010810140c0d156045020108140c80c418100c6680c01540790000519103070b009000f08040c0c0d820545415415480080c9120b02c040e441420703d8010704c450a003030740001c00c1c0c90101381c8043c03074180300d4082e40580100d600300c2400c1255000380c9880c0801032030169200345a280034200c1355400d104025921140c03407000920b01f8004002c4900c0d03c0a0000c1c81464920143c0c0c1d03020b4075402225140003010350703a880202d03185202c0c6592400d4112454000c04141ca030100b13000b480c01a26801180c0196050681580000d0700004c2c4420032001303400c0003203016502c0c0001165800040c814041d84540e02c0f03110300b4907005080c2e0041e20100140ca0f428814090751400665084108014034030000344512070b201403040c4100803090300a0b20090078581415629000541c5e078180655820745840d900200b4082c08540240c0c1b04c07411f854099000b581020360040d404c3c80c0c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 684532374 1107 684531267 684531311
    0x41a1b0d1119140c0a0201110307020607150f0c0c03110c0301050c04090506060f0405120102071a0105010f080103201c11010906030b210313090c020d03 67
    0x1088049200300c0740c3d20403000d0000e0641c600e03c0c2d401182c40f4168106005c109000c12b010302d40042e55004020a406800341c400c0004a9440f10265030803180160700782e0184525104c100300110b500001100813007600340c00c0c07070601400000c000508085200ca600c95055103410100701003106443d01a1055480c0c400c020000c9e50384035001d214042c41030320b686100020041c8010040b91504840c0103200e00c102070b00241c1041c40a56440310242c4881482e05220100c006c014809940d10122121132003020780b501c0003482d490358442100ca2003450002c0d010011035132800e40c00d1a101c11f00c8500408814040c0240d01c40c4280c100f2514003106510031900140301542c0000d00c0307070320034011503400001c003c0c070f0041c103100700f007451030091071495841503038500060190013002d000b80c006580044c40182d00119120302c10f858001d0a01b0440070562080c107260100c154150080214160 = true := by decide +kernel

theorem cover : BRFrame.Cov 684352517 684532374 := by
  have h0 := BRFrame.cov_init 684352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 684352517 ≤ n) (h2 : n < 684532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
