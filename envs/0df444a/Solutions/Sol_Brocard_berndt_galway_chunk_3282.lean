-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3282
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:12:30.307608+00:00
-- url     : https://prove2.me/submissions/ebc9bb2b-01fe-4514-823a-0e1a60bdc92d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 590107913 ≤ n < 590287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 590109163 1250 590107913 590107933
    0xc0b070215040b0a421502060f0c07020907030c0e04090b090c0301060b04060e0a080a0309031a01050901120c0e10030312050f04260424110c100905180106080f09 71
    0xc10107080600c2811003080011700c03569001801100e440d410b107000e000d83c1008003040640c0c820752044540c09107000e42043d00e0503210382e0004900c0d42d00201141c081c980d4031015280c1040c81000208030a8001800420200c2d80500742802d000703404030b0745910315202d0b01441c082c2a040601904049810f0150320600740f904010003a245680e081a00700e0304600e50390000100d01004010f01d01c00720b402074440140039811420031250358806020b1644c5045416801040151500c3c0d801c50304580d030120b255442e0034958500485048129844240c9a18003c001c0c00641e009000c3d800c0122403081d15499120404c1290100c01d8400c1106c1da0b000090304840014007080602400111f90701024101403c20f2100300b0210326150071a40010110b000c0c1716507400312818500910900e00d040509103845104144440700da5a1b5100700c0c90b0500498100c0c0d9000300c01030084040e24058480180004140d0030410190a6151404d02c601000034500c032002c00ea400343c00ca0440c45c040ca01074405003c40d001c0c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 590110413 1250 590109163 590109251
    0x212090a021c1a01060314010f050105040501030207031b05010b0111070f0e062d010905030606151804050a0c02010b0a030c0605031503030a020c04060906060c0b070215040b0a 77
    0x840002e6490f0803000d40319401d02e1840020f00d90103003500d5200003c01c1400401e6403203030480143c00a40a14038403000a101c0c0c0ea8000c1d09482c00c65400b40382c050f82d210701d14034040b02c05440d002214081c404021240c04104481900400d00d0351500707907076040d19902c941041c03a640e0750180c410101d403402e031400180121007050450503032140001e070048040400460f403450b0490380c003a400070712803000d02c030b2841f81640e4080001002400200c00500c5c00381080000104007089030000d040101c100010b500a441590c4260412285c000030800c0000345041180c0c40003030300888540c1001946820010034a0b86482a00742003a2038001d07102071500344c10500103644983c4040e0001e0078080100c1050340081da01040109040701041d4003802d00e0b941c3d00c00c00e00040e03401c0c0750001e0b294507040c010144525517000c01510840e64015030070b8021902e8440301a030400010496004d02100307404101700901c101c60000c0c500850b90140c04101a081100201c0b280d5003101942000d85022814070365400c1c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 590111663 1250 590110413 590110459
    0xd0903031a0607080c0f0d2a200415080a1b030c060e030703020406030807061b0f05161e0506070f050d05090114011712040b0f030903070606090212090a02 68
    0x10345c1c3d07004441c1d0b21000d1441c030514150342840040001240c1d40041c0803201f4025034000810040050010400640740d96141140c88004200c0032042d20b010b2140d103420360383c58110070406030b008556a00e049407107081d034685544070244140c6807507281e40c2c407180030310500070f0026048036040040001d00d40d003496402c4400c035051009103641880380e00004805a552807003100010f61190903425a281003031b24040c0151410402116091440c9060109400f5044403500f1004041450840d0786c5102c0360402e07080a1450b0580a009400000c41e80d00d6281604d500301d9568501840c00c0f10f0955881c2c0204882c01c0da5203c1440002860611050740103804c40d030000342d00485620004149000c0d902c1500d07440e202d00764451390b400341c000040f900d511b020900003600007040110040c0e142c641814903c203014800c01e40e07031100707031440040021840d44092040e900300301c1e07000500b4009203958119580107500442591a1800108004103008803400920a1070559015055101154000320002d2582d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 590112913 1250 590111663 590111677
    0x30613060207050111040303030b040e1b0109080f0a150c0c020906030a05010e0c0a1a19020f03070c0509160c060b0f060310140102120d0209060403080d0903031a060708 74
    0x2181e0207201e0b000c0065428018580c209010031030054850785103080090a68041d806501c3c0201c0c43c003050002c0b4400041007503210148103450002840c2c10301d0004842140319079018140d1030007811058104102d021503401a803900500380c040741c2c0307110424450210350300959950045440c0a440100504040409640c08040141600d00481082d102d181c01c2d6101d4049107a82500240b60a6044d850011061006040081c5892116228400d020380719841449240c0b44081e03e8621490200ea00c20001c40c0c0c81100140141da454014901d400011841a03001d00362180f091040040c81c80d200310030300c4101810059907480c2040265440c0d0100404134030b03110f16085107000b545045107840e410001c50182c520140005070a5180c6102140c505180c0310850381190070190218030700c02d4124064400c101d00e455401a66101c010000580c980714942c00201880f0b400704d00080c00301c8081c1e0001c50070354001d4506115075031070b21132a840d4400428151650101c13003440800c1c0492540720240940c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 590114163 1250 590112913 590112923
    0x40b040504150e070206271f0e07080c100311070f0503040f0b030105040c080c030c0306030a0c0303051206030f071e030803040b0411030c0108280e032205030613 71
    0x44541c645006100c0f421048540c6005a8031803024003051058001b01520f201d000039590121241205804d00e440c0c141d004c4400e4900002500e00070301c0511140d01010b1120b180000700c8100640e80c00c0c545072a101e20b41405840380018004440a9a000b0b02401d03008010310b0010501c0c2c01110f54aa03800e407901c01d601502c052100340310106042d00f40c0c0803e80003030706d0035a0900b500c2e0f40c9000200010740c1c0c400b642075070411099100303000b20311a020080d0fa03005400070100c6a100e80d0f0314004280381c5507010b10040d00081c1550000014560444024080060384010052040c0d603000d040c03654a29400c40440c400303511240b4200a050905448555070030140c050110009a8a854140e841d80007910103a503c41041c1e4184000c01c1407011140c08074810a60240070b000c003592001802391131004000180680c1303103200c21070340c0413020394501100280002c0e007000451110782d0311503501c0d0810000c100391141321004201503031603000414412a44010004e00c00b03030ba07480d001a507200890260881d4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 590115413 1250 590114163 590114201
    0xf0904031205070c062906030c0d0f0e010507020a020f010f02010209040638030c0a05091003050601110a081b0304211707020d1416030b150105040b040504 68
    0x9890740311805101d004140503503c600ea407401c0d9080ca041103a191044005410401540b0400c00010358415582d50100444209032642e6501c0c0b41e001092003035103da00c0341a86403261129183c184c40d8415044e00c0b400b140200001d580c1c4441c16640d5540d00c110181d07200400c3c1c61900d55640c0300c1ca45400e40f5416500c0094102280c00c80414140d55082e00000852107250195602103000381d440c2c1070902d41100d2051040786941003082c138961001030003290034450b0020754001c445000e0004c13101042000f41501c0d000204001c00100200826102030780020810b945100301c0c0390300000c00802064020000c00e02c0c0202051a910030120300c0f4152008501081c07000048070782c084001c60188030860814808004c64524101620a1030500c05114000041c442e24025864001c000034085900c105680100b0019202c0c19260405d0002d8406d04d200c1d5841e804010049440d84042c003440c000d020508035408948010358450086001c0c0c400c40300800d1004001c00c0c501500000500780c00801000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 590116663 1250 590115413 590115437
    0x80309010e04021614030403052a0d0303091b180b060906131e081c020a110a0b0d1a04020309060f07050409050403020f0c19030611090303040e0703050708060f090403 73
    0x5c484000d5070b0841a84a40001c0350400502c403081c0120f1580402c0c0c200d24807101d80c7c0325008241078455803c0040d00034181854003400b05400381d44030201c5140c000000d0a800a03411100e46a42c8440e4003600d03e0401d40d0950100e850032140c010705881010041c000e03070071b082c1c815082c001c094024882d180880340c9e40480008124a03880100c2603846840403142030b2003400d00e49103c4c5001d046c5440d6280c80322071041d000040c81e42c007150394001c1c0350b440710f4070b101f18045900000300e1142c07032030b0000148482c001803400503e03402940400212075541040b8910140708208100c00c0740800c030380c0420396422010005108004003081c495000c0050b007840c909090310b402400040750310844046001d0b91001d9000044860104601c2c40401400c0712a000c00198001d104801c00065200040c40152120003400c043d88000050340d0304020301a0882c0c2c0c40b42d9541c050014158015990140803a140c02d01144209209602d15489008040d00744203440d10000140403000400800545c200001a5141 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 590117913 1250 590116663 590116673
    0x409060b060408030322030c030809071502070503060901060f031211010207060603051537020c010c0f0503010e040206090f0306010305061f0f0b1b0106120c080309010e040216 77
    0x2410141400d07400840e20b903e0086200c501204091420071b56451b00207903c100000c0d4050301c118405a811725141c0010b13154107107007900d490a6500a5910016401c1c50b2025003680080e00034102d03082102204c5581d15000c03c2c0034201c070424000c07000c44a000e00e60600104082c0369003c0121105460054280307039000d03804ca4226046030104a0300607803151010010301000308010000c0d031034644282034850400076080e801c00080c5100e820140c008030b014100c1c0b061001903001d025607140110943d600e030a5880c50500070300c07013503c404010030441c1c00306080540c4200d054074140c1e02c10380c40841d8241c440360204103068210100655000760200c48251240d01c0038020607008610071002459941090341401003c03405400b035841045407101402c004d42e040e07179072500f4100c0b11401501da40e2100744003041c04200f1181d040310505036007418000a2021001840c42c0d8645008640213903a030b9480c1c142c001c0c0c0700d10036040c0e490b0004c0c800d40003862492405900400351840c03905c11358a40340b022950f807 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 590119163 1250 590117913 590117917
    0xe0609011a040e040605060906030d171008150703050c0a05040302060d0b0415060806010c0b041403070503180102010f0c050307141306030603060f02030405191a01081b0604050a050409060b06 84
    0x2201c1141e2146e06200080c00c01c2540640c000d00214060200400c1120004240c00450103081d04907680e42e00128035040c89a0451a024105c01010340d000804840302d1091005010345961002a15000015451f203402100769145038038190f80f0b51f8034103031a5800704031980e0440c03034407820415910095a41f4a41d10b078400d22004052170310b0780004551a204002d01000401007030503051107640c2c080c48000860740051542c1c0554000400c08100c60a0429140f0350701032410011314521002845c4e1f200f403000015800f04d500001d030f00034407a510200701c04809460715045040c001c00c0c0c050002c0f6420701d005001198401501008071401c1c00c1c0b040c0c84455050085a104030007180d5200d106200b404414020034064081e000c009619608040e56219503680c04448070381544411800c00340c00700890f150302450325200c5998801c03142d5855628050311040920215230582203001030815541c2080020f40701150001400246914508001d00c405450710840880e5a199500241e038026607507400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 590120413 1250 590119163 590119171
    0x607080f0a09061404030f030c020105060609040216050d051b030405150a0c0804180b04110703051602091014040908030a0e0c03060a020a08011a04060507110d03020d090e0609011a040e 81
    0x380b10b55400c040c87ca400381c00c60700d51955220071a4101010405140c68000880340302c10426070300103948000c00c85a150307000b460850000c3c51405240c0440400c20740c0580545a00941c0320308807503d140c030208000303560b88210b11030990000700c2081ea8440c100c108501409155409080c01c0440c1c1c4541d5840007490780c0903420440c64580820021058046148115205c040f07090f038080142d1810190804203501503504000d0400a001601c00031400c18010703101e030b40c1036000e0b045000604048058041d0b400003801207400a0701c12106447c21490180142c103821031b044800e2601d5502c42c480c5200207403580c050101414403804c0d83c01e5890791004c002c0141b02d03038144000160ad0701c02801c8010001c040c183d100200c0c040002a10600d813581040444007210158244140d0714401c40c5000c0300220710081a09501600c01007543c001d140c0c002c54624601501952086580d41d2a2103005150f40f07015681141c004003140014040c88880284540c08010b500490a060070345d11038807801003c600322 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 590121663 1250 590120413 590120417
    0x11707080108010b0d200a09060803040314010921050c06090c010206102103090b0d05150d0b13030c0b0108030c0114161808030f0c0607080f0a0906140403 68
    0x210040000b207000303224811035400c085a02d02d424100711384940c001c2072605142e000d100d2081420240e981c1d5986000c003401044032400030f010040e5241511601e980091106540c408402c840c180325040c818411400c1c01d80c0c0c00501e900c8031081d851200143c562030394950364207226080010001c2a081001824804c00100c0020540300380100c000901381040542040e00c000c600c4035007401104101a500c00120a80c5090211161002c0c18122019091548070a54608001070750485290710340d00202c2c415900503001500701d1400781c050000c481c1403c54041c01114054001c42d002a001c000310516150003850190600c0410362141c8030090000e0f40421000d0340001440e24001c0380030b0240403400785400485400500c0c2080b05180601c40c0c10039004100221003001500034125040c0140151050404607911340110650f094074584c040c08489613648200e500060000e4400e91080b44a8080208604200d84480107454041c10380007800720303825519080d40d400c060042c1051948554042d07 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 590122913 1250 590121663 590121677
    0xc33060120010e120301050d032307060903081b04050603091501120c06020106031e140601090b1c1e0602070b0720012c0123220b0a0b011707 62
    0x1030050070785801301059100388450302c18001000306a6403880c0703010748160541425804c2600714050402041c1c01c40510100e107a00104082e0148003041d80030786000c511949500c0c0391a00e60007241d00c408001c0059101824004102c1071001e030070640003640d0020744040440710b25141d56410314488800c240c100d0300c68900807090b00014012040342ea0030040c00d503400200a01e90660b02e0b50b00c0c01c00d00038201a0440817200281d0000c11040c003807100d040c4641c0005644465031a403150b0030143c601c916a00341719402c0728002e050740800383c070440203040f81d002c0600354810960914900400390401d00580d0110f5080c030620000c18104c02095101d10110355581c0002d0645072165210114001054a020b0780740100c031141c5400e600b4031030b0540c0d620102c9182c440220700d240c41030140002c0040300e00d2020740103003117100d030204140c0c69500980751a40b0b20310403e00d80005208030301d0900200500110704407000f1030a80d5955070701ca6008100b040c58044400d0f0b9140715143c0c8100d00a5603a00001642 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 590124163 1250 590122913 590122931
    0x42a051e041806150e060a120201050904050a0507270e1e070c030305160e12030d0f0213050603090309010507060e011e180206091003020913020c3306012001 69
    0x45507006440400c9505c0c8a904010700800ca0380781c0340e4003404071030700c00b136401e000156030040c0c0644074600c40080060105140c50814030700500070039074850011403031510515102c4840381c0556000c0a59070040415158905000382e80d0008020b8007144a040440440076006a118010340344152515142c42c1d00c07000313480c034005046580003000d0310b4454100da030308104c2c2107a000144410214045401c49c011010091015041d445070b551030300c8200d484c141ca07c1d1109c0d40c1c00d4016240044180c0300000da22a070342c1092081c03d2004494004d0b10783c10070401c0d91030a42c002c4000e00110fa000e0300700012203008008445084849410008000c6510841208480100da00a07980601807907003082e0b61501c603a03400300303441e80181640d0502c0780c800030f52842c8040e8847e50595150340d000400c60302181110f905070100039880700c2c840000c030f4054034821083e0403466040200b0103003070000c11141e08066454031100d207180050a00c038100700c914034107202005400c04a90070303025400d000015130111 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 590125413 1250 590124163 590124191
    0xf090406151821030e120a0c0e06010f140c03090603040503130b0c100e0f06011e081506040f090501020d02040f090b09070c030c0803042a051e041806 66
    0x11079078043c0402102c0c40b0380c00240d040414588414640d810f00342000001c81580000301c810a00030341010080c4076481ca001e0502c05e011040c00219501c0d60002d42c40c40d12504011560302d03580c1e54aa4000c1030110b0780300103140c26031100500c2c1411450054038200020f040c0020000c0d4401c0d00c00740c90382c2d0700110720110b98140c1204104000c014400401e0328207000c038202980c4603541e4540f00c03401c943d036403103802d0200c0006100b410040c02242056504560319840110304007aa140000103208000c88070200320500d00254442c24050300c901955155030300c0000b00805824913038a485d10f01d60301e910000000074024005001d07210f42c0c4200140e250340c01e008103c1401410344d402030300e589081c2400a9850384403090100d0b0070a030790b0300c2c01d146448090b05098454120301440140312140020400040c00003500c0c04c503c0026a0392a80c040d0000011000e401c0c0744641c0c0103555016084c2c44a0100e14943c4042407100080003500101d00d68101250724464110a4001903c8071074450b0b4410340940 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 590126663 1250 590125413 590125457
    0x5071202120a27082104091b020f0d091716060e0f010c080703030207051504060507080109050402101805121006050109030f170f031f05030d050f09040615 68
    0x282400e1031010420304d4014000c0e540c14001d00369506034920b000c0850428100c1400300c5000c0c000142c81408240d600f042c00c1c2d0004034500040e0b00c0140070342050701500403008524080510f803030fa0b0302c5a0803c3d0404400d08518150707446030782c88511030705000780090802d44140070000d000c1c03511008401e00c11401440700812203458241d0401c801e0080940002d140343e0b081d80c2e0b20580503d030050311280c092804c035180c080070488030070360b024660040008000301904914030a03003041c0c0d00e0110590784d4100b0841075600641300250701c003540c02c06001c516031094422081743e1200300b10780d240d01a40c2d14003003281c045003c0b500b09000c1e003264446901014080c040d000040c002840c182d03c942c0d1031a00c8000c6145c00707080005205c00c480300303a0514607825aa0640d50f0600410042a550b4200100b4881d103078090354204c0c04080140c04800207240c178020507001540600c0341c80c0c0510740110305800401650040800d01d40c0159682c2c40403401070403114a1184003240c0d0b48030360340440300e01a02800300c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 590127913 1250 590126663 590126717
    0x6020f030a08010e130507030b1e0402030303062206060e0a061404060c03090902121f0506070b0405120f0703080a110a031a13091109060105071202120a 67
    0xc0c0d0042045501c440d51002980e0304441c490b130815204d80d100e00b207185000c80c404802c0a0054800e200300401442864100107008410000d0300c8803000c54804102c2c0083c02c41185c001e5410780041c000187d00e17091244220152007051a804902c2e82c44401c040c404035207260b0010f0002070200c120090460920610301000f03803c03035080030000140a800b03228a54400c5010350000c1101604210041601a02c204406025081400d6407946501f440384580950103da00500c2c04800c040407040142d000c2d1015401c2e00d0303000e0029460070382d0984035100329403001381007101d0a2240e00160403900c50090094a9400e0b41e501405170303120707014200100003000280210a001d4601409101024401001c03a1480103050801260401c0202c8144041420701384010340c00c546031081e00a44000c15070701c40c424161045404200c41e0801078140038500d01c044403400c0c01304004008a50206000100c840e56124051040700c16000c0280c41c15002a08544142d602003007819620165107859500d00034a2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 590129163 1250 590127913 590127943
    0x21081303060e0319350403030b010f020c010507020d12052206020c2209150c030209151309020a090303090e040b0a0506030a0c0b1908011a030a090506100602 69
    0x2050764100c40d0400120403c07403542c0c1408426800c8000042044c2c40d140da90f02041e00e099504417052410398105072104660850009240c0150419190301801000c0701000710b50b40202000c030344500040d070b80360b8003251003a603100b40460742040c0000c80301500c10440504507035601d529001c0f4104403410190010010451030581c00340c0a06c640c583c00034031055103900441d001040322804d512940c2030205402d0001c030481d400d250075682801a010301c2a000000b02041c100300c0201c0041d000c400f01d0182240b090b0f0711083c03124221008800c103070040c0c004e543d0f11202c42c003141076031a601300e8120b900c82c0080c98046042040308006140e08610b040300100500740201605291594851640841c01044500d030b096540004c18901d813002c000402e40d1550143c016001940c48224007120307900304165140c2d80c903820685d010581489000114100c0b6442c030100e9649107070100804100360070060410f06120795610007400424002c100080c01941c0c402118440c050400070000d0604d01d8846a40007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 590130413 1250 590129163 590129167
    0x11d09070b0306040f0216050a030f092603041e05090c0301052d100207140d050a030c0807150b04050c030c070b100e09060a060807060921081303060e03 67
    0x41c0d00e000300704490780701000b1030340000c41c2c41010111000034000e0b41d04005468010011800c208080085d00844103802912003207201d044034001103508a80c1c40c059261503800455002c0700c000150300a400d0814060b8040e00e0400e911204041c002160706409490000d07501001001181410413405801c40b800c80d1400749198142800314807005180c422121000d0205c41540501c808503640b072008040c4c000b0071114040781980d10096940709140103141001d11101c01c035512600c0c15074052010680d0000140500c0724a81d2015203041a1050043c0c400301ea042004a00041200440b29110451550000382c2c00740301c0740c18041154801000c480103203008005011030411a20f0035107050707a501c0302062485a0f200390944400e1101e950100c4d45a101c0d0206200607a9004220f1310701c5030035800420800503135200f085590b201c1c0248204008070320b18400074840c00b08100b924200f82d33079011058003c60556903440350420b42c4440400c0500028640b8140108030a50261804844c0c0c0c00c00218 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 590131663 1250 590130413 590130419
    0x1f140105100e0411030702010c1706030a080715020301090c03050f01061b0204020c1b100c240b1f0e040207020906040b01020a08030a05010509072c06070506011d0907 73
    0x661015201c600810900c4540c18008030280d450780c00c210303036401c01041d00c0f54481c1001e500280c003801c81d00540d14045800c190728080b005a00e4081d26120b100003e009045418841e10307000295481682305807084c140325040000360004c180001d50080101d540c0008250000c040010210f810161010840c02c05240041011590080c13005150080c00700081c80302080500c0050001c1c480c0300700c003407142e02414040780c02840c8076044c001480c80c41940d01c040d800000e544211020f40c11094000d01c0f2400011036038034190b02d6800300d40200401c2c0000001d165400300e001920a014481c85030a1108101d23402d48155a070103001080b00c0c0c40e05450960034100a64006155084018101c5000f259145c80c00403a9070301c2044403000e40c68211056550b281401e00c0a000546000d0081c5070180181900bc115100d1003440350884c6599401e0b540c801c004038811440003600e0340da00d101c952110f01440302d0b0303020034400d02c0520b00800d001208042142c0b140300701c0d42801d07000108035691a0308860010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 590132913 1250 590131663 590131669
    0x6070f08160f0606381c0501050316120605180f07090c030606020c060703091a0307020607050c0a020d05120a02070e090d02150606070807030324120305070f051f140105 74
    0x1800100f0f9842a030a604980c00045c4210314050b403011541c4070701c0090348050000c1043d03840345068a00c00d0302515002c180d1000404518075036841080311040e030240c110307408243c0c82c0e0301c180d4100031860244111900048105807814080d45080c0c00c15030042c4e04204000c3c80607101380d1070070f41071500b81400306a16004020391528440122203005c0c2d80002148002c0510400ea03900c080c0440d262000c040860500341d10310540c00484c0c8010141c4902c1c400b144200d405101500e01d1030140e0300081c8409111542400030314800c2800886207840303600e0040700b40ca00c1c0040a08001d10255000702019803800b502d000c8504000340c100c012030b8000040c002a000c0d400321f40d94080321889010180c10ba01c604002c00c00501c0340f002c01401e508800b20307181c0304055054200040f04d52a000600c05440343d1100101d0301c0b0812803207007102c1c030f480001c8a54006406003001e00112070245a401102510b0381d00c802e4280382c2e80b0042d03c600c80700485003020f00401c0e50311404049009410780308540750304101c04 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 590134163 1250 590132913 590132969
    0x109050d02061308030324031504060b0102010b03030d0b0913020d030f09091109030d0809071205010e0a03020a021503090d030209030307020d0303050601140906070f08160f0606 78
    0x1001e40216000a0011003200c4200e180d5002003401c03801301c0e07070740c4d02e40000358103464440c00307a0402c40000030084c5801c640c40c0c005803241d4684140d0342e40940c00e4941d07645a00051034011429415952104010030b080d56091000c0c0c094408101000b241c0f40780410200030240d4001002040103801810040000d0384070740c29014480c2c0d900d4100300c80d0400c2001c1c0305803000c194a51080801ea170038050b422180d0204c0a0180950b000203404488810102038070580c0d01c0801140c40c60400e40c0605c2081094150f0013945984440c00b607800003c004103049440b80c205800d000058001d40d001c01c0e8144d046041c44920502d807140344442d01d504600303201001586912498120300101500410307020460780e428811100050350042080c0b0442005203030180140c1412203045012a56040f21034540d240d961080b40e008403401441070340303840c490380d651a0110121000a032000041071180b0b0552003503500c9050202800703103542000241075407501358241c0e10540c20050b41501c002198209560203415 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 590135413 1250 590134163 590134189
    0xf020603060a03080a0201090c09021c0f0f050a0c0207120302060105012d020d02010b030a0c1509081504021509090720012f03040b1902120103080306040605010905 72
    0x21040c0d665269403001031001101c81d00058414280042c400c0d5107103405522140c03449200310700030b0004035a1545803504034020b801070720406103141580200d181e0b14580c051818400b41c1080001c01010a1824504442c03084038044141584d0303900303045c4601d80401c1410014848400310000d20b204665000f0b48030241071094505000e6a2000343c0c803440341e50342c0c8802d00c464012021403030b8100c16040080d80da954032502032002d9480c02c48192282d090106003580c0c0950000e0070b68001d6860440054421540e9004002c10405d26820204268500748070300044412849814801c0f42031a00410440100060040440c03c008002c914000c1d181c0c100030907400708440c1400303441040010042d292240150440c05129482c104085200414140d142d610650700b0f424407100c400c04252100d00a1b01c07050310041d1800c1c0910002950001000c02103e50000d40d113000503003810307010a0030b4601d69500780c000310f6aa00c03000c410441941041c2c41140c0080000f40b800c201e03464940720200300b5404003d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 590136663 1250 590135413 590135419
    0x6110f03090d060c0306090c170c1303140102070615030b0a06050a090b011101020c210c1903121a010314010e010909050712080301170304080304052112130806040f02 73
    0x3c0d201100313000703600c06d04c0202036500090042c1001c50000501d40805030034010140c82c01c0304c000c43c1f02090b665059815000c013850f0201c400c030342551191411640c04000b004820740d000c1120700005405401001ca107901d00c400c24151803400d41c5040e200c4a01e0081c001305403540351034810080369032039411071022600704ac01c00003810304000004841c6119014050072956000103204940d10f50001446120301071480b07158400c484401c011080c1d0740c4168010550b03264400c0503009140301c0800d510404547c4a07051440d40e1411090341141900c51003104081815168001c0e91559605030080301201900200012202d6040c007a541451070018044e040ba6103070f94201d45410018204031003805810000090440703800c240c070300081154400d00a0b00341011400c0c0d503c0d1034800000058500b5107080101840c10a41031105100301c40310400341c1052000d96200513503108203418042c4189100305040c03d540d03204103902100d040d40101d075001c01c0a65004004000c045000b0340d1803150740c29812 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 590137913 1250 590136663 590136671
    0x903090402031e0f070e090609071b1b0e06041b0f03060b1b010b120d0e0a031e0303240306090203011b1101060608090d030f1506110f03090d06 63
    0x9075940140d5410701c008620f50741841c1d090005504458050a1256400c2d50320442d000c400182405010301b0280c80080e00700b6400c10108251500030b5004040c1490b00000e6140100403584400c4400032104080c0c00d4078010651080c0b1440c00c1a1866907800a0241c400344150400134000c03481c1c40c806c1e01030442c204000c0d401800e5106100781c00c140001e040803111261a00000c01c0c240c071401612080c18051503103004484101e83c01e005181410442c0b9000180950152064080c1c81000c0b0383c001c00f6070b0042c1d1201c0d0100c0011f0120f0306a1002c280c081100c0e00003c20203140c094102d91400c1c04250a8800e0055080780d0081441e11900c240c0798001004103112206102083c0542007090541a0b400c203914004405290720202d50420703900d10000a0184660324036003550603440c241e0316100a508480d2031130810302e00a070814010140c0c7c0603000078140180c200c2880010b40329400140c005040341000301595513041000c000403d82c4907014501d0240ca50340007644419036501c1c01440c094a03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 590139163 1250 590137913 590137921
    0x30c140412030e01122d06050907030207030c1e0b0109050114060c1005010602212115041a03060f0c0921120409180201050d0e0c0a2705090309040203 66
    0x841c0340c003490105100c1e001809004034018840d031120501b01000c412056948501a614442602810b4101c0d00060701014403501c2e0b20700214041d510240b000d9003408030039400600000c14800121140804010704150400c003185040d401244060380301e800c0322030400e001400703c407401d42a0064012030407243c1d29642c00c0c070149850300703002e0090071100c52545040000140141c000c5100c0320241081480350310000402c00f540c901c640201204a03c0909841001c0101107103a800e01e2030304462499480c0112994420000d0141c99060f601304c9500d0f8400c01d141da40b00d040400c115604403401081c5401c2d40e140c1140e0f0f01c11140103091546100340b580c0452051118001c26406c11701c0304c1da580603031703803800c8540380000584e0740305100c2c003001d0501d4235642c01c0075200d4900202c9040c550503990303949040c1c48100000040c1209541c2d4031028000d2660082095542d041c03040700610400e00c0e665071400c0340030b40c00c0a00c03180004c0c91114080c01e01041105120000c001c446145808650042c0c40e51a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 590140413 1250 590139163 590139167
    0x18150913110907020712050f03040e06030d03060f0320042a0206010305060606090613090b130c1d0613030501050402032503020d031704060b04180b3103030c140412030e01 75
    0x6040f007862440c501000502142f480c0c00329941a20406040c1e08031008944185403c03412070350b01d40f040013002d4281000c188005421000455800341c0c070f90b041c0d2801d0261020004089076080782c21020045201415008401c80d0384506003416004c50000c0d0000d5851500d420752034183c01440c80b445540d00054031a0030341e60300030a655145101d090b080344a541c490090600400c1d80910b4684500c43c18407071000407106034003039081e0369070081d80e038910f54120b58801e08403061170300309500c0d912040a100d03801e00c4018900c0c020006602400011445003407500505091a1410041300c91003022008521500314009a040c011258150f4480d540136400b410221106003111000c1e0340501d0320b031014001404503640005c1c40e080000c031001c21041c14500d4a4000a0128031300c014007100c50740f0f0016a440e0360400307a2840d0341480f040745c0c581c03100d10f25440e00c0b40a0340b5544210046907840a15240301a0701c10350041001200c1d0400034074040c01c29008250b80101c0680050070030441841c1414564 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 590141663 1250 590140413 590140423
    0x4020d140106020703020312030103110f01090503120711060c03041814010e04050610060e0112091e05010b061c020c010605090a02271815091311090702071205 70
    0x34411840d65099542c4654000352076421900c8246e20a1090010000401d00c500301224102d0380c4c402010020100d1500034003018011100540341031043c4240e0010305510180900000a4000044e40303030f82d101189000303400b9940310300f0214003408060101e00c00000300001280d0603900f28403094080304e00c060700c80744058a24821400e01c14602d9000014150140380041406284505c2c1513131059501c141c202d10750501c4521503000042c1e4143c0d8560041d50040e061413981d040748030008030b0005d0b01516549a02aa4182d1001c3c044070304503009000d1001c01c1c41402c000f64400c41e01d0919052154101d07003082d0703040c01444411103034001140d400094003540b21030001d10300540030004600d4000c102e00001d400215443e40c0c04900d0460f521007a1f0001319814503001c000500101451420040c8030a00304001800d0003800810124659141ea40b80c0414910840e190703100c40c28581e040c1d1400c10b04a2a1200325240148030f40801e11071140d4003c0b5000c000d407400380c0d00340104507401e410454a00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 590142913 1250 590141663 590141681
    0x1e040b030f0a0b10120b2d012a031206030503030a0506120a03031a1804030f051303060f0c05090d021003060b03090d1107081005100b0d050619030503030604020d 71
    0x12104183c80000099004039003550b0545d48000c00300700032180b8000f8000700c041d1954041c010f80583d01488030300c600c2c241c4e584104054041c50f290444203130110003404046980e10f0f03807054448184200300109984010707000700e00824014184006451f555515030b9902002d0300801849031254005401611100c45255401c202c500480d8030071012418080e000340f00a84200514840340092160307903082c460075240c154421000019025907440c2c5048510000f108000780070007074108202c00c400342c14114404040c502800340040e86100081c210700c11100c0341c52100c3d0600c9002c1c07241c040e095541c00e01560f202901900e101d03c0e24809908200c00500c480d40007481c60700008000c1c03007200100080c102c4001d01c180d443e62064103000d07420b00d603036600c0544240f1000794441c2d00c0c007410000a5811903500100071400c074480140d25a0f20001c00c50f0804180b880001e6980c1080100515014016400c22128021041001170541d22902d840740b100130015030040727030000345c1040e14900e90741c018200 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 590144163 1250 590142913 590142919
    0x1a07020105160c2102010206010e060402160318090b060d0b0a1a0d0605030a0203100207031b050105070e100c0201050f040527010e220515010801021e040b030f0a0b 72
    0x504a141030f0309100d0650295204644013545001001c2d886140c0381c14515405070014030050b841c103c030540007500020070f82c40d04640c0900400300c1038040403960002c80c038400c0d202c103141003250301c0350b8040c003041c03a5000084480c01c2060040c05a101d540031620000d9000c10045100b400c80000310f88000b507268001c40c00c205042d0340541c41aa100c4d8041c00d10340b648003505102d601c0c3d0304c81c1010340d60302e011071000e13505820090b10010280060b50080101d640b00b8200742c48242411800c2a038804942d80c8103a40b9030751980d08018100b80e0000d41c940e9850700032103030121803400c149802840000070100c0241400000141c901c04203403000260f03401800002c00e00000c45000025900c0c00c03007420125050004110000440c1403000e00102511807928525200005c02c01203811542e580c0c0f601074182d6003405004400c1c8554400740001c14083c1440c0000507030f13241a41c1d00024410070007249290484c8000703100c00d010194003a411250000b9072440340c50f2041d102c601070301c1c00400d0b08003840340d4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 590145413 1250 590144163 590144197
    0x70c0b090d051b15131e050a1403060901060e070c05030c0102040b0406080c07080306100c06050f010f08070b12090f01020a0c03120b031c050705010911030f071a07020105 75
    0x1089201d8203c00c2c0140703900740c450840700000600c07601824014001007421301e01002d241441208a4004100c00409111004c1c4001c5a602c50204041c40071a410802006a5000305102c881c1400c201c00358100010000820200b840e024411030700703d8014201d00c0070000c80781500d1b01888001c000f40c480310900d18000b1540d071550341941c4002a4058807840e004510480e001500301e40300502075552a6801c224402d10303568908041005a1006000c035605000d94070840350003140c3d0070700c280d51181e000c0b045407202550512498007080b60303080e408040540d00015041c030032070108805a41444498400540140d1902e690541c2400c140d5007807520150f201040440c81181d002695130a1580651101c0c440c0c8000310403211706072010100080c2d01036000300b410000844000403404e00620f0380f40340150800070300c2ea03142c03400d5640041e010b880400d481c9008040d42c0c5800c0c40122181e00d0244018200e41c0d207012900e02002050307a50030140082c8c04945641964011310880780311500110b0300750 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 590146663 1250 590145413 590145433
    0x1a1905060d05150f0f010b2b05040c230d061812080709060e0d020111012d05010909020918030403060f021c18021c020d0f03080606070c0b090d05 64
    0x107a4103d0216031407420f40d01c80c0d10224a01800005801c1d0607190b43c0b0040510b01094060241d04034480b50f21048010294584503110100c00c1e4401c081c0101d11408038043d0b003501d0500a16109041424510181e4260300111011a5204042d02e00c24a9200a011aa440d0450f10040340340c2c5001101401c10300303130102c0c0e1100075540104820310603030303854403642c00540d142d2400300e0303509170210301c0e0710b030441c601164440256014a0180030a000240004501d502180c000343d56075100c5802e05c241682914052018800140c0c0603240c003425541d04100500786068001501500700034086685003207040151072100d08081c41118090b5030440402d1102000d5404039500944c8502c2c0007500c07134001c40600701403a10181c01b600d60140340704a42805c24050a0f003c01a641c20448610b4810003c0200d0b0400183c682803840708085015014050200c1c03410f041c00303407020100070940c92140c801040000000b07900f001c0d81c0815500c00940d080c1d1182c0c185030105a0701014844050312034450b100c511 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 590147913 1250 590146663 590146693
    0x14130908040b0a02060906010b03040f110a060f02010b032e0b10051b0f1c180b0306030d09030521090a08010b01092903040c0906030305071a1905060d05 67
    0x501e01d0f1040c96080f61980d6596003411a00ca020030701410504407001c00104000c00c082c0a8541e240f079005035452030205180c0c0000406803c540d600442c013181c10a01418502a028031655060000603406041c52a196400c000b4000c0110303030344d6029074501c100000c07451039001d42c401d83d041d03480500104042c61000c00007a000b03030050b40c1001d0f044d40108240054950010500c0000c0308440d130000c044800684898540910a4050510422a00c00180c00c90708441c060503030010300b00d660080e562800c164041c981001840344a60061190210703081001400000c1c201c0e0100c90401e1007101000e50030a110a00e52040901095000640d00404600c9a07c194052a080302e0241c9820424981e0754064050040921803000356200d40e802150500002d0706000b50f80c0a40705030b942d01c13a00d0361640803e00c02c80381550401d50000b0303000b103003143c20000040e002c020840075284460140d81341500b80300c02e401100c07040c6d2014280e00da1300803944640315036408201107036000050f159090095600 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 590149163 1250 590147913 590147917
    0x210d03050a0506010f080f180a0b100605031b070305041e0807090c0c0f030e031020070b071202040911030a111201171f0e0f0714130908040b 62
    0x5a103107145040040703080c0e503000302c60b08581125103407a0740b03409070f80f03601900c13500c404001c2c0100c498071036140307070b24035000c030180b1008121510070a03118615040c40d009007031000b04950030042c02d100b4100140a0480c03a103110364444101c00c40fa030903555007440c0c5001ca886001c1c0b076201602203140744c40e41c0700b0100f030313041186020799510a00b100d5107650f0741d0761802d09480c0d9400d0041c0c0441d494004400104005100303511220740a0f080c0704080444030303808241340c60021030900c542030b5500c9095101c0720312100b100d0280b0f221000c4c00c0d182001401d8585490390f0170060582390a000340c4078007104410100d50155401803022400c1002900030700d034a032481c41d520407142c100e08189803010344148a014082035509410b01c0c100c0d41041a0300307024031201603c4400c5589556407080007010440e400400c00f800c600ca036081030010810b028002d240c540351512003002c155a0390040d120602080c190100b10601c24041212901d29408101c6040b8000300384600b03001d4241c1c00001004210380c0c0101c00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 590150413 1250 590149163 590149171
    0x8071b051c02040f110909180604030203040306052d1312030b0a0909210519030b09070c17160210020322060e0906030c030105071e051305210d0305 65
    0x2004e025014111981d141150040205191040b105105600f85070628004880e80801d035a00a178000d07100c8410f80e0303480e000f0f04880840050788006400d00411040e401030304c0e0007038040c40c40f078403c1781d14868600f8008584074140032a80c070740702d50015013220b00c500c108607800c2c1d8025556001e90500040c004015010031300d139017030198400d0070700028034008910500785401e801110071071581c1c1180c4018000010400d503c10708101d0300b0301240140c000d500e4944040721016440c0010141c041905010303040100401290034090074001c0c5230085603100208031159841c2c12903035642c410741400680c05c00134071800042c1d000016404583c910740d8001000300a070245052200208401920b012000700c21640038040c000740300146a0b10840c1010320f130407500311500a0036101e94a209401207421140300310381030b03000201c1c00412201c4000484021a01b821110310f070041c0f801403140c2e400c4900d5561480754901501d5002004000d0340d019454604400001c070058454601d01034800070040e00c0140c1d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 590151663 1250 590150413 590150419
    0x3050a0207080703080a0c020316140f040c08071803050f01060e011203020a06020304031103070c090509010c0e0f03030408071503060b0415080901150b030f09060408071b051c02 78
    0x40004202d101c4001181003c59070f00c6088240351050400013101c1000352503108076010303c64000103103944400b005211000e040c0c80800c948c28000f4450421103440502a03000703015900e42207000b0b44c0d482d03100000561085c13032420641c2d044000181040300b8076265603c082d155005400020380704210640203123003100c4241d5040301007640ca0b9051070303ca00301c040300c0c001d01581c8810741e480000740c4160007569100d0f010341446111544000274541c1564000703041124402e00780107061040440c00d102c0d0f00e03000074282c070003002081c2c03041e00301801c0740300c008502c41d2144038040015040399030204201c03405007021109448090b503503200a28181398031302080c2c40100c0e040241c0400e0042000081d18129012060440b1401904000540e90302e80c01912801c11552660304d040e40c8080c62661103001080300040895a914080c642c0c4800060302821a031a25040341040c08041400764064840042d005008c1a900c0c072401414580c110011784c0c0842d800010622a5101c1e001000107102c480358000e0f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 590152913 1250 590151663 590151673
    0x3060f0609050306150a050d141605030a06051308190e061e0310090c0c1401060e060915040624020c03120706020906030c13060302030c16051903050a02 67
    0x80c500903580c03441540074650301035000303c00040841c49103a03030100e80d802026040300400c40d203507804500544480d4005841c900303c0381e41911716400080141246003c1d004201c52040c0b41820002030b15040c0134200500103a40340d401094000011414928600307503c411000d9580141809000f5103000b0030328054040380384401d48490b00d007002421500c01035502c1031080f684c080c0e202400802a0009007000c00d0070400440b0118840c040c5120b00c3c0c16035040303507c8000401c043d610f00302004060340001c0d0481c1c1d9041074010072413440ca240659401c14802c0390400929541c11640158030084003884d60784c00340c101000080e215410b51511040401000c0c5010500c5000314026680c0700988119640c0542c000c40004d1905c5400d400074200040c0b15900c0540340c02d84150000740c446e00151403201e44a0700010741d2a842d20100c0b00b0920080109040a6055140c04001074030b203400b91020321060010841c5001080100070700018501c4028a260004c42c10054100100a0b030030035807100001d4868 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 590154163 1250 590152913 590152919
    0xf060f030c080a08030604050c130608180313030b0712110a030c02210904110409020408011b050717040801052e0b09041d0703050a15090201120902060c0d03060f 71
    0x40f841094498025203110b1464840c1d405010050000619240450320103129405030b40c00c02c01d2501004107000d99490810f0b003041803051441c0500c444d003a2159034010844908040006001e0f40200e80c1c010803c5140c0740d4460005544c521004a00c00080a20b804d228091582c19400900500d45065404000786540400140da64102801c1714031041e41740d05070360382d2084006d4001044400e03405071000c5243c0b14080303080a056041608005400d50700410184807020f002d202d0002e0611620720705032000d0f600194094a07e10819401420090750403c40ca030705105414225002041c0c168000c1089140201d1581c0035064203940ca2000b440d008506040a042c4a031011401c0d101d105c08101d1902c20300c07030100b10041056041041c56050707100001c0c48141000d1010310000c602a1018003200207240c0307400408007814605001106242c4001180542d9015110100013002200001061031490000035103a000e4400c48503130700e01c5865581b007125039168111038100d40030a00030409d1192 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 590155413 1250 590154163 590154179
    0xa061707170402040906020d1401030b1003150209030705060f12101a0c0a050d1e020d080a09030c20030609030304080906030406060b0f0a080f04021e040f060f030c 72
    0x125071030811100c580880200e0050702d82a4000c5031640e209010045c9004c00c00c00c401c0041d20600244000395100c6c010040092100604c966980502202c2c0702a01c41400c0d59944001010001c002c19001a0701151400d001d860810580000d0070000305829120340000d02a05900c5c4c0c0200c1c069108418020003140e0300303011001c40382c4291441601666111440d03420005001c8d0440c1c41204044d04c03c2e0304507800411400d00500c0411a072656881a1040f6050801e40d884519034202608650191504200c02a8040a282d0700102c4204010894400c10704007143d1101c80c840014111100180107810408003929405040c0303070043d41a40c00643d5040c0103240c4a000880340500001410050410180351441c02154054400d4000040306625110350000f5a08020741c00040410001035900b442500011101c2e80300c2c48000c401e10180c50150301244100101c600d800c0414074482c170100f0b449030703265005892101403420003008425991040542080d4061100382c1d6001610100450018 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 590156663 1250 590155413 590155427
    0x516060b03160812090d0f06060e0f010302010f0e010c050f160806042d05030f0901090510020d0f020709090c060f2c12100603020913020a090209030c0a061707 70
    0x248010b030180202001150b007951583e44445209a1b01c807281d00c0c4403600250300d128060203c80c0c003031000058030318200340749103080100c0a0300140c0900d2160004000607a4002c0800c800f610b82450501010b21074a401603480d80e82c0b0680080c2240252564085a4078000910322140c40b041106081d44039a20b08d051500c680c01a10003a110004000c000e484003842d80d500c5040024142c0d007000e8071414070340c4425040d50400480d402d03a00d100004c0c0c0c59403540c1d01c1450403010f80300413121240b14a9040401039590402010390809016010f248208980d0080c0201001840018810b000f902980d00e411841d21003a1b004460101d01c0705c18004682070720410014030180c0040c00c9480742280316005040c4c3c0720001c1e020080c0d102d85105a02c050074138040c003032039401501c6000c000c202103043d48100816502c0007010501280300e642821009642c584126508946074004010799400366034020906150840003210b400c1a0906400a007050780041d120070384500c2103044c1c0200e17480d07015080b9525 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 590157913 1250 590156663 590156669
    0x18060c010b100c051504050f030f0406091d040b070e0d052b0801140a0f0b0309011b05220b030708160306240320070309150507120516060b0316 63
    0x2540320504a4000780d0017a104260082d014208885103020466000d5103142d2210907540402e41020508004244e000850f1078040d02e4006c05880188500340c088044030030008002034503811006020032100e40c0134405034001c2d540068201c811600b080e003059940d80404200703102203001e07844140d040d490200654140398592545c0c035070416928200d9102000512601c03101c5d44444a84400102002c00304d20240060800d901070701d440c4c0c5402c0202c00d00712402005420b00b80da40030081ca10440e5030180c00c035440c480035030116858800c6079611790071413110307183c0203200c0c20500003040c0302043c1e030420305040c803030344c1c0409410100c0000740c0c43c00c4058456502ca030340c814906c450030300078000551756068070120a0304c1c07070001002000c8045e21100d05440c00805583c84000140d800c0c00d06a00c911030341c014041c2c02c80006810405054001c040f48944503010306031041d840c180c500098840c208590400340440c140e07030280c6420b800d282000b451545529442842810070850340600c1c0a0a4a421 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 590159163 1250 590157913 590157923
    0x3140307020604080a17010e04110a08071a04091802031b060a030203180a0c15090f09020702030a0b16030b090403020604030e040209030312040b010b0c0309010518060c010b100c 78
    0x881c3c40d15035070005a900300c0384601042c401602c0c4d03c0314481041103641802842c90407505806410103048c40e08030100110240c5000d442044028440164006169400c07103414240c1c140b040c183c50075128405000e00d4000e00300340c1c1e007031284d6903141e903039000c203920384060084003511803600444407524600c01e9003070845904004140407243e9014069405582d109000e441055100c80f88481014242054008115001c00b5002810300000781001400d0b850380000381003080186050040d1000c04025078072072002c1140d0001585070840d103090003070994155010f007044819040581525080380c04294521000900d0014a04001c0c9405925140901d4054001d0034042e1a52780307040f24407460b080b080c1d64019800b0421100d40351003c10007420307204a106d400700841c1c1401c2c505066040d1040c0c3c4000032080050200b254030640100032508050003d081440d520b09c901c410142d00003205251142d03205c80041551000040c064000b400d900b40e04441c501250440c4160540d00d048031000b02902c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 590160413 1250 590159163 590159173
    0x5070509060109170a06060f0b0301050d060902060f0408060a0501050907080a06080706120608030901120203130204090b06131e0e160807080c01020102070f03030203040614010803070314030702 85
    0x504000c00d05641040c810700d0851205034072048950b8203800314554049040e070100d551401030080d103100d007601610b400d40b07040c01c100746001c1d1178062902060040ca0301c104d0828113980204502da038015403c80e179014120701c0e15000d0707070401101c0d242c020b44203000e5035000c2c0780f00151800e08144103030743c146d520042c01851181c8850000726406140100b01200080c0d49001c00700e8088003c0006000805036996040720303010514401f0015100250b0102c0d120380d2046c00754a045a03082001c0f00800c510156005841e40d84816151a103501d04040180d04217162818240c01d10401361a103602c50076090b140341a074404003c0d41201103a080410181c24401212054020400540c0156200c2c504010440d120803240f06c2030041e0560455011024507030140b8801c00074040b0920a007031603104240003c40c03c101081d140d000142c004140020101540000081d003007100c160300c80c09803502040000051503071250f40003596a032000a095002ca04035042c0841392403e0750046070300c603103044e40c0500 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 590161663 1250 590160413 590160419
    0x1017012003190902180a0605120a031704030c120203090901030602070b161d0a0315050115051908070210090602030702151920070b0114011806050a120e01050609130507 74
    0x844000000c6d015820480c1c680c0ca0025041d900c02d0f6079059035020b02c202034101d183d22490f018041c64902c0e42d8010034681150108408240c2003505003213456005000032804245031103049085200380320040307030701441c66000402032242d0340c3d01800c40b60307200c0c410041d46503c407620360300c42040c0d0003080800001c0342d0b80301d5001d0b0710f001004891140c0070040e05504560b40c0f41d41d01c1c8000d0703031004e4560001040d03568004001d0124004100e06511140c4d042a6150000c407058241107001c1c000050b006105910b404204054420044403903210300303a903410450502140340040280d48240e40c0440107210b4030300d00031291008940b40901071a0032441003c404591050007002030b02d03440300030811014460094081495514009207011881200d501c0159810401c07104030b8004481446810000c1104600206500c644c07d008141c9000c1d081040d2585200b0310100c0d440d0303401c42d0b42c8003549401d05000e032003020415003051380503132011900a0825a5040c0848041c60103c03140907001c1e03030180c1820 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 590162913 1250 590161663 590161699
    0x403021518040e161818030c060b0a081501030b070207061704021c0c03020a0b0f09120c030106080c041b050d1524030e01051017012003190902 63
    0x8200480320702801d070f80f8513a80100600c82442c460f0780c0101000f02c031000080e803068202d1701c518081c00541c0307480b64400c0d607080e4800400040026400a020700da48a800304165501c03002c0702001440d9100c102ca20380d19085088113500c1d40c007032000311620392109021900250001c10070006441d0141c2d01c420140078540c802115100d005070060307800c020303001409645003200028030740450340290001c0b95100d146205021400041341d00049400c3c42c14804000000e6031001102d540742d4045524544160ba40002e481c01d00c10150503080c1d00d513103000d400043d600000b041506040c0710031901004010014003000c2400348500c9101400550b04004078000408203601500e81c020520f110491603540f07844a0b0b84032542003c04600051840030741d0542040e62501590308850311441c02070060b814031001c1ca080400381c5008819960030004101909040254011280c02c100c00c11141d0410aa0403126403e503442510020324901580c3d917142c04040d2280918603120b64003070841d1045507510901 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 590164163 1250 590162913 590162921
    0xd080901061a251a07030b090402041a101106010b04030f0305031801020a11100b0303030c1b030712080f0c3a0f0e0a0c0504020307050d060308040302151804 69
    0x942c2580801d040040f280c542e400400501401d206544031001c94165500448030740740000d00f210101800c060100459407640151990010340c1a100841c0031100c0301089280c0c50007943c8115001455180321302201d80e884079500b00d10699071401d4802e0750362034400c1d1080074402d9000c0030300103501911948000038812001154000303181540c0b68061900d0306015400d80e07001d105514000f07401003a03603c2c100f180074000700c2c1c105281c90504111002c54031012036200d00005141070480307840800e0207a01c85202d400d4102d031514484081d00d0340d0b00404d00c3c1030003500940c03003041800503008400159034422240380c42809501266290f604040c501c090381100c50f109015140d0145403c07005110b5420341010300c5804d14040c05002142d81450f8000681c100d6018070309080841d400410f880d00401c010440ea842541d105480141c0e690359980e00a0700c0b244540c8810007090745c900f82c4004148402d200252084d02d1003251101e0980899600c40c0805000303103243c1003101c0b12103c44402e100d180a500c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 590165413 1250 590164163 590164177
    0x918100905041205220b041401020a0309060305060301060f15021510120f12080106020f070f0306090c080304090c0f050309061302030f100501030204140705030403140712020d080901061a 82
    0x410504105d5103070303001640313001c02d80c4054031181c408a81403040406100503002804005c0c80102803410203510000e000c010f0742c1c03107503074189a0f035040401c80540f0f0a40200d000762561414048225a561300c030010301a40707000c5402c0045c01540d800c03101e40003c0b41c56881c0980c0f09104089913903400c0c10700c0c4001c0e840900c503003114881091a0801c0014510500d41c118102c040e40311213035290306d00500682080304040a0040a40207000301340019a0844101d509480c0c00480002c0c514506151170100030b54070350401d5840c0e10001ca0300040d10340a58100640c1401d284c0d1b11b04140c4504d03005c3c20364490205032034405440d0030110010701ca0607040041c4c0c101040c00201102d00003100003050034106005445000002a2a0001031081d820980135000400d0f0300ca80c06511103280c201002003190201800003010800046112042c8a00180c00c0d181700b960420f16510f403a403005a0007968505e0304805100c0440d03c102d0010f00e802c4410303c0388a04175010201ca100c003440a1064420140d88045 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 590166663 1250 590165413 590165437
    0x1209061713021c02090906090307170c01020c070906050d08030703181407030b10240309080f04052706010f0302071e1a090307030507030201020918100905041205 71
    0x40c032100301507a0388849200291607007120389440484203005109950340000c042c106c82e6032101d010b0001c10300300002150031864114400303007201c00b07030b0036007012003441201e91054040d0300108581a0803a07021aa81c011100159410400c15a452040c4202c90310400d8015101901c01e0000030502030180e003140319950b11070405110b81040503500d1244500304602031030240c1e4086541441007007501a000c2d50040d144d81d11040b901450310900d041008800a00308100791a254503400c0d515010380c00c04604ca40e4007003080c503120f2404450a4809800c203200302d07449841c40a69014440c085101c407803109900a205000d119a1880d0054441080c03680c54a0200741c0c0c00c11601020030182141030224521060035040d441003d03040c4402d250149001f0444450700d1001480305091000040700c4903260b160400e99200c050700d0406030f00900504082c80e4010504d100c0d0240b01d00038a0f002c40c0d204c0e52003a031190501948405e0341c0c5003100c108880091039101d800809292503405280a40140341c1d00b5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 590167913 1250 590166663 590166691
    0x50403120207050a0f0c0f0b07050709410a09051b01050d05010305060f06121f0e150108120703021513050703150636020903010e0a12090617 62
    0x1952008105c1030f4410301510298503190b014030000300b00001500080c149500c1480c241501d40d2201610346079244229000f50717640e14514094440c0050214507009000d1052000c00c1d0009018840b03405101e10010901c21040c40000b6800000c07441004800c9801c4070007007202c3c0d40f00c00340f03030701005103614440c505110041c0708800301b0190303a001e0b240c06140300c1c501170451424040307002402c280c800f038102c034495811420428016500001e0081498440700280c00f00c440c8404078010080602c09a00d181394040d105070040b022440d43ca01d01c0c100c3e00c00c1021076100303a10f802404281c0e8000c0c0100100141c2102c150902e8280b030200c40141c00c8214500b00000c04d10240e03650618000103503004079140c010013407910010300101d1090200030080c030010703012184c0c100d00080c0c0018800074426110031016101c240e68089055055500112000e0001c002200c0c0d18907900d0790b00d64500508484104c4214402e4280c036110b422503000f26542500d43e00010603800b00d000c501a0350041c8080300710041 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 590169163 1250 590167913 590167933
    0xb07060b01110d0309060c030509030f0307050706090605040b0702070f060c02031009051b0916200f0705240403030c080c01020f09040506030a03022a0a0603050f0a05040312020705 79
    0x14070841e11044091349000800e105d840ca00b0364180c0e6220911581814034000c20400141008802c0380c9a00404142c3d40c0e40e06e960300c6405645a000b154800740846140801290800400d9032046000764040d560b034400316542e0f001c2c120ba03035010600900e10003a6050204100060046038800c0605200800f511080da001d440c2040403100b18032015500c982c44904400c1c4601c50900716280301c8942501c003000640b41c00d4a00440641020184400300a8405901c100451440c0d000280c0000040c098581221a09810595404941c018103116080c0390000c0242c90590740ba401c00f003444210070060130036145071030980c3e500900314030036241301e40e00b00030840008400b88000c100b14060651101d840d82c0c5494180000c46100600c034a0190380078030001c03008642c0010f040203008899000840e903005036210000e0480c0c0342c04c0d0002d900624141d60100b0440d415401952040c1c008410500c480d0341d03465030030000e48005407006404603100c6101c466000301180c00903c2c07138502507421900c000788 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 590170413 1250 590169163 590169197
    0x1150519170115060306060801050d06090b040305031e16050a0c05060f1503060f0402120c0909100c090b07021e060a0f081e0633040302030607090b07060b01 69
    0x30001c0d80030000e03035940e80c1000c94038240c0308240390140c080c526080015a040400160540c4810700900348070b4400842c0290801006400941e00541d2080c491a02810580b801400d6500b0135510b0848820080c40313640f8001d00c100810a2040359a05d903455000500300c0f200351103552060324080708004851401401041c800c022180c01011841d4010700c881c0342008036068403240142c155032082c2c0003107051000303401518410356003194048844043d41220186032903d420000c80c2000c0c0c00c070a4030410024410301c04079a080141c8000c640c1804401007181d021140c2c80d8160081c0300d00e51209101100160802d003070200302c41420000302826203060600040e2403908101ca900d00012903403800802c069038481c0d501034001020700500348042c0111490200051001042e40c0c0c01608240440c6607406403050941740c03e2007541038029a074411030201600325510602003a4045e105220105902c42d1081445204880c103882c0b241d401c02c07885640300b0000e07000c0d09108504020084050081b955 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 590171663 1250 590170413 590170439
    0x71d01121b08060603060a06030803060111010f150f050d0b040b070302130b0702010906110a03050f0f1b01230c0702040603171213020d021314131401150519 69
    0x460030b00010b00b5a403410381308042c50310500074500e00200341049010000210b030f45042e40d81009003402d26000c4120090f1526004003ca514240c1c02503080086012030342582070398071070954040d0500044195194418003040c079510390740003000038103400700240109800071100c0340c024500e0301d005442c003182402030243c001041c1c2c010364a195070024008045607045550342c0700170001414040c12242c4100f615a80351044040080e0511a000646521040c00803040b2810346020306000741d180e004550005008844001c2c40f503840d58a401a0303003030550071902e501d801c11072084140816680d5046051a16070f0814101240c015803035070000300000b1880310140041e00c14244401c3d40714120600c5091116001030204544000c200a8440258880c0f83c6001802030701a00c1b00c4500c2c01000c0342c0d45000341042010f900300c0c103000ca418001c1e04184030080d19106801521000300c40012651002d0882e1400303229921000350444c4100030350b04001d0314803d00d0342c007201c00038400c583d610744038400c41e4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 590172913 1250 590171663 590171669
    0x303080a0b0316080c03062202060f0c010506010f0305160e0f04090b06190b070206030c04080a030504060801050108060d120e1503071713033501030203071d01121b 72
    0x42103c0e440c00e0020b5002007008110103030044000b000a410111541000310600010706c480821106440c0c0d815501c8490455241d400340075015651440c0046ca040d001f40401c1e55040d002070084803843c0307501d43c03180c050103000b640081083d4040b190804000c1c5c603d145415911074002c0d40c0b403c0311002d19a10b80c40348400d02401a1132200783d070f182c901c00f003102880b04415111494136054109201c009802400e070340416038181c03419583d0b0b458028110106000300d40c401c01042c0305000c541e40401d64002c0142080b1030030380d2110400d0703989540055401d444219505030304030303036002c4801c8040340d6840d803c01c01e5044142040f00e02e100490001c0b4078a84400c2140d00c400e54030000911400e07503844004403480307040d0321071280d030f43d81040208018940103141015081002e1160860010b500c14251310116075421000d40741440e6601d0800b2855100900c810303486401281400a00762041340f4001416540300107620700c4583c01d004400f410310803e000152000a03031910124505940340c0c00e18009 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 590174163 1250 590172913 590172943
    0xc0e04060f0e011505060f09040911090c041a12070f050d020f0405030610030819091d040314040f051905090903030a0b06070f2907110f0f06010303080a0b03 69
    0x4d98000307030004c1404840d0b9940658014141000b55400325000c0500307441c80c0490842c1c002c940d004c1c40e81410b079030b000d150405895000cc258002e118140c496500204121560b1110b2a0b81400f940c15004005008000030340d07011500360030010b1940c0348a52081075298a160400604140b450001c010490b00b00c005030103202400014140b0103448c0c108001175100c401e0280480b2000c3c111342d01c44055004a005410b1031548061150340807502a0401401800f040000c0307604856a0481c0f030008044250313005c1e808910300083c08583c0d007148004890a03075100c0c1c40c0c00001c007451b0405004d80c0c00c29110140e5000200d01c00e0202d803d036251150f00e0301425040e0000d44d220304202c08203004503125882074034424582000154001070070009071404664111101c0001c408510340241c071003490060740781c01e00c2004203042040b280c1d0040251000c50b07048030112030308028407203101ca40e1030302401081512540550300420000c0e20614074980d0040340c40ca0003044005003440400c0c50440d8000c0e011007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 590175413 1250 590174163 590174171
    0x130b04140f030a080702061c0c030504060e0607090b0d110304050c01020f1b040203090f01050c0a020705010806090c030c040b0f09090f1320190602070605070c0e04060f0e01 76
    0x418a040c800550750721104602900e2102566501e043d1140b0980e00001d02610020400341d07866601c6030051801015403020030300c0301103440c42c401002010304035011a20280f0b00703a5004442e07600026075501c50340c078546070b0841c42c5040801e58030558010b5006060b60341e450340f0740c204a04100d8030255005034425002082c0500000001a06140c4600c141c0c2c8051b512005120070f0700d22a400600d1007045042d80c006950f906c030181401c1c24185040345808082d800e00f0203100c460f10546000341000301c850f9081d00c2e02141c039240112900001921400c0e84414003038041030306940365500850300280f0102c41c0ca80b82541d20700000c81150050004012100000b0034004002c1c00d1003800c25030311586400070200540741c411040400c0000080003d01a024100d214010b1094400491720710141c00810154035620701d003440207003000c02801100e006000d0140f00148040c0684259201203601040c162081750501410b82c140b030318014401d45295803509401290000c1034070880075001d00d1240041 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 590176663 1250 590175413 590175449
    0x32a0f0c09190905101422030c02091509060f03280b01030b0108011a031e01020f04240f020a030e03100c0f0810060207030b0c0903030307050d11070309030206130b04 73
    0x108a41c011150241d0b03540001b410054412000810f60b191a1801c1181a003148514203003140c0081024000a400065280600c071a204941010300f40028007142c0d012520303075480091004640643d443c03190140d00c40040400304a042035500d00804490b500c0d1101541c500c0c0e29075514403882a40282c1d0301030307190b10060140031000e004400c80b001e40300b00c019030701b600e03420b0200343e4540c0c0006514030b00c240244034055003154290121741c503007055001c1c070340e4236180c07240b980d000f12225803509405404011050039070380f10b0140d141300300c00c601c071600503040f05c50a5071801e40700c040b80c40ca2110b0341401900000081c081c000c0c490b412151000382d407100c2440f00400c80281800d1000760105a543d40b480404000b178540c00103c03201a01e9101c5c90f2000c454503400f4841c85c45001c2c100c1c80310b902d40404000c00a00580c0304001e00b043d205200801d01840c01d03280c0d01c4400e00c3c030800c08050001140c1e1541031000d03080200c01040b40002082e50307055085d80e1a0b403031808640180c2c00c00391446141030425 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 590177913 1250 590176663 590176693
    0x1b0a0912080f03251718070f14040b04050c0913090618031709030f0a03020702030d081f180b0d0c090b0120030d0c0c05032a0f0c09190905 61
    0x380e05071003441d040c041c100d441c00c42800800c035000101070b404010740d00704111b4240c1c0000e0011200501c88000c2c0351340e85a80300c0c0300109003860031042941c0910301d0000e4030036480c03506002e90342c0140d84150000d4a080c10100c01e115603e80c1841c000d419494540c04010b000542c141f02e124915120070507884018070061070020328411041900c420749549030707400e000700d04030044229450070240158250307030f54000308000d9019019044003e51726004a408580b4416005070709148240d03c030403424001c1480c1d41404003c0e00e00ca6005100c1002420345088640030070765404080c140c58014000aa1610700d503540030310f80341541c0c000500d6241ca41080494550b0031408550486c5807000040c800030310440200303a0341c0d02074803054004a50700c1d10072106400340205181c29031241c0080940f9920207104c03030035100c80015003022002000642400a0700c2c100c01040314850090204058100d8000c8041001003804000d011341d00782c6209124202c2d84a84284160907005101e03a01415040d0494408 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 590179163 1250 590177913 590177971
    0x3110a06062c150f150301030c0f0b160c0905041104050903090607110609130c0206060409020906010315090f091a01060f08130b0108061b0a0912080f03 67
    0x350250a000710311112103081ea1001c02c1682c07202c880d0b0403194800c1c440c800021451300307a65401c0c1e60000c80c1c50104461102003800114143c2e805484405051a82c40f072840d048051a48a08929210f090040b0050719200403880b1100703e00400030001516100c0c2d1811088ad8170035902100d00d6000056500c540b82401e0084c15800500380c4003440c20043c4520104d4800e01c118640204180340d8280c1a0407103076a00c20542e144403801410801c0740d02c80019105005010850252000d8441c1c800082c28074039090040c01043c41c3d0280c011340303003610752800641c06400022801b644074180f9038808107035140c285c414812400021107000c01d5011003803c01240c0b00c0740702c40b0803030015103001006020260700605c4e038810040003441c00e900341d5038030040c90100c00c00301d407031004004054090001400360300c00250780b8010301c13007003035416856003104071444c0c29403182d080e00c240821070404c4204644080c0950319006280100c40d0725250018681003141d455004849100201c05803403140705c07601036480c4d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 590180413 1250 590179163 590179199
    0x703020105061e0904080409091b0e0402060d0209040608160e06040b240918070f0c0507120515010e100801020703120f0b0a06050301080d020615010c03110a0606 71
    0x4800714200348601043c030348000407249080c041d840c00c40104042080e00d00c1168010841004200f08000843c5062000d0818031000020201502e040200300148002001c40c0619401400c203482d1040004148029401619010750301035501d010005400c1001c0c40001c0580340c008550015407030603c0d81d81d6001c154003a10550145283c40c89d07400407074030b62600006c0c0c0205239030307072010383c1d00c0c0f400b5586455031151140b025042030034142c140d0075003001404c00d1402503106881e11240c00001038070403100449a0080545554044442001948101110520814014400d50321000c3c0d24096442e5400b1080c0d110f071038182c046004010124a2107540c007030140c9880d1000b503245c420207460050018102c016215465650740c084104412816440f01c845110054041038580740d88803800385c240e4000f44560a014003956070030702d1055202048191140d40d4030140120161364800c011201542c290074110103020700340c910019054400c008810700e40c1d01c0399601284540c1881803010381c0070300c091 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 590181663 1250 590180413 590180419
    0xe2b0c050d080907030606090b0a060315051c0822060504080c060f091c11040c170a14091623090405071d04060b030610090f0f020a05070302010506 65
    0xa6008009100400c034000c00441034684004a5203404912034180410b03903000400c05440d1810000340e0807226013000c0e1a03071a08071100c0c51640c0e0303965003c7c0c00f40d82a003400001042c031b1442007803240b451b110600a03800c05008010098a1003070340d89d005032603409002c213801020b01845c0b00308841651409608013a01c0c00d4903040341441d241000c0c403907032034820141c80c5c0e02c965400b00e0800303d0480d034a4140d62801d10000d000c4901c0000c012603907105001080780c2038401100750140e1a0043c20a4081e820700380000e0394450229081e441600e0302e603070307401030f111a4103c1e0b11504a2700ca03000b59907035014001c60f1100d01601070002c050610004c600d01d16071003408401481800c1c4190240c044206582d048019918012991b440d1b1a1076418030071250444111480c544c003880d0cc100ca41038130746034840d034858501045004903034010184d4074442168581488a11a681800320981c42d401c007250007a40b1000108201000c40d0700e4409036049022642d00040c404144807041c99424000c0b160071040503 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 590182913 1250 590181663 590181677
    0x90105010f030201091a16030509040b041e092315070903120503091c02030702090f06092d071e030e0309210304031103070807120b0603010e2b 63
    0x1980040c1a000c058403039200241c064020301c003240700782d00c002c8441f0408480e81c60407071002c26241c042c000703401c00720070180a80d10b440607009007400c140c400c880340c00e904003003a00c1064030741c0d92181e000380140c0c0f80c0c210b0b400707840c01d180c03981106001d900b100c4000e98404098411000f0f030134000c041c0500000c108401304030200380c0400101d000342e14201d100850324a4416602c2d81c03101c3c041440e00c000302c07010707a882d4140701e071450030102e9021000d00021031089a4407407180d00d5190383c0405150702602c14079071050007000419048418801d04040c0500b040803d80c101182c510640342400c3c07421600e00c008107a045080c00640d030300d070305111450310750507040400030700d0100070049699015203102c06000308290640c0b003c0428207414030b00c54040710b031000c076680c0341e8407440c11811400701516041d009219443c1d010070003100101d0060144c50b8000d40c0000221402c0d00c03002001d4034081c001c9600740d5030741e0a0703500306400103010103880946031990728802c4d25103100c0c04220702d080c001e10f40004c00c080 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 590184163 1250 590182913 590182919
    0x402211002030169060302030a0f0603122303070504030204140405061602030f040b0a030b030d0c03181203020a03021903021002070305120106030b1503010b070f03030b1206090105010f 81
    0x5024000c80f80500700c0d4164005610000199201d2071004182c84002c140c1407413001401d198540c0041d44502c100c440144075944522160200780d4109007c01840103406407510800c09118104c90710504075122000410901d048840c07103c580e01c182c0301100024000a414001d40c2010301455088c03c031510b0301c842540c40d16071210340c1c0301d900103003e50054941c6020444201c030305c2001030b6205408490700d0700366542e03a50455101d007644090150004682000020303607270b41c0f4010502244010290b00c074040409c2d00f82d43d040300e50f0045079280c0284c100c0300040c00300c5c01c500f8100240640c40d102e0740042c0301c488003606010b440c000311a002541010008158040069800306441003018035100300542c443c81c043c42c041d981801190100880c5800c5800002050340e80b5402102040c1c13402c1d6428041c0c9140610f846080340310900400b44c149608101400026070641602c04000e4007901e0001110100c000000c0c2404102140302012a44008240600c0c84001c1c0704190050503003420046c1ca26207 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 590185413 1250 590184163 590184269
    0x60905011e08042415090204290714010b12010b0114091809030a080709060c08090a080d03020c010b09010e06101b21030504022110020301 61
    0x841d110100081140c10000316081007946500035040d54503512411035100c0b00d0004101c014000140d4182040079407100004580c0c0c500d1084070291000e00700780c9801041907804041c3e0090744007036491801c880401c840c0000c00e84001c50300c3c00c809000c40004c100c008084081201c07201000d0701500540e450309140517101d0ba00145d4203100442600701c026284c4c0c0c0e442c400651011800342000040c1e24180d4208481400080018004e8541d1a03c1d0700740541ca49500c1190038640502600c3d020924070f24003540455010340281000141c020030040180e03484841d0a41889a80b80000c1c0110707030041080390130b640081c061a00403603000d55040e03850750b151202d495503104020740054090481c1c15601c0740094031644843c0e000240c900c203604c030f81c1c1005207403040c41c0e00c1480c181d0319108030b082c41c0e400348114468050580660b030002c0c141c046411040c1491100f015001303042c640c03a4455030010b000718082e24009180242035061401c00741c40b640420750408801c83c1d210101d010b0f0448c229000d01c00c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 590186663 1250 590185413 590185457
    0x305190f0905010e0f0d080403050d0203070b190e0f010f0b04050c030103032f0c0901090504050a080a0e030601080d23040320040212010906050f241903050106090501 73
    0x10350074a01100b500d0424808900d005d40001d0046800424001100d8103101c1c06030002d03c101e910800444401c0d0300d02001c102e03100c0c0a040c000074581c03c00714010030b045203100081c014402e507044500040003111811110714064000001c000940d440301c481d0603d4071034510940d0303007010003514203000b0b034504a010315a0350b1005000050070b00898050b03100f65060344c16050003040302d4201c0c1c4007034201407100d00b45d5076610011608030710400e00c7c440040347c0312846000f5280110b9005000b405000076660351103256411142c0541700f0030034030725141c2a0035901003000c1f0b80204500380c05001c40b4040d200d0000c02c1804000f0300000b2040003d034644582c00e107164116001c880d0041c0c40c01c912891303d5100b401c000d9400950841d4090b0010602a0600d1083c1c18654103d8480080400417141c2e20818003110010b0003030039590040e0109600c003070f1003035080c40400114112000302c0749810301095509414400c0c3c1780d2108000303a5104018400550051401c4c40a00000d00300442c1c02c1c003c144852440d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 590187913 1250 590186663 590186669
    0x19020c0a1d0403050f030a0209090a020903061303051e0705011a010801030609050102041a0d0b1c0605100803070f0b0c04051c0507051f020c120c011d030601030305190f09 75
    0x16502030001001e0500c0b0318259902c17101500300586d5217007003058994010f5003110f00400d105111010101e07441100030f1080340c04c000d8019015040d15955941c0280245031500015402e0040c10401017014001114000d00ca54280c1b510036516a902810f0440c03c581d020044003d0401e07103c003a248803680c0144d090740c1140c1d404200441c445010b823402502a015541c801c803415200725039076040000120f401b411080e590002c0401811003171000300400020f05210314507180300385204d40c1d4042036107900116809510454032140440e521450710b441c42e07120500a6410080024911041042c100411074001a4480041e401c09040a0002d40c40822081c04054440a121141000c0003814003400c4000c0100810803921415031407603108282c0f001c004510f00500440c044942d0030b1900ba14207151059900e402840380c20501c00055614448144940014020b8010700103110f68003040001e003c1e501c81c0e81d60503140c9404010701401e291070844043d081c000649294040070703500a65440072 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 590189163 1250 590187913 590187959
    0x20a021203090a05030409061403070506040b0f040305030c0a12080106080105120c0d110a0f0e01140d0b041a0106110a170d0905071d15060d02090619020c0a 69
    0x41da031910480e4616040000c4002030407400041400a00b500240c1e0160782120946007400c215446108200b6850341458056141d000b107060000f444420b03114409400c001064004503460b10f42c40e074030b8051854200e1040e4514a51203540d0100400c4144030b01080c0f001071604284109504000300074114580500032a4044c03084140c001840c4081000000714084001e490000c5107042c1e414410804280303180502e0182190240028603d40300010500c200c0e2202c0c52000e5559003442001c1d40030581c2020441d5001804800c2540031900354125107024900c5211581040b540618a060705c03181c059104005104614640c401c511a01040151117550301401441030403901e0364641955010304c04034503500620b8540b41e035041040004582080d110003000c03a150700e40e0201d950111010040380c84d80c005041d00d880058a50401030088c02001c083c2400160400602e040880c0c1103812a00d081d413120400800c000740d0b0a501442158a00d06050340c81c000f00e076007401d5040301c2da2103041503001e00e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 590190413 1250 590189163 590189167
    0x311060307080c090f041a03061501020c040b010e0a0915050d030807121512050c0f061c09060e0a11041109090c0405090103120305090102160b0a06150c05010f020a0212 74
    0x44282e5442045d0104500002d208104080b6003042d44005940a000110b0117032192001040c000f1210300c7d00c540036038030705074001c0214003040300034031014059404406062200300302498286039a9454400060701c0a0100054400f001c031900c0b02c10032000c1d41c800c41c0141c0c510328468003c40e501008141d4411842e0419140400c45c1400712001000024451109002c0c5001c0108020030581042041140039108403070b40f1038010300c10001c030303558091540d944c8410100441c44001d16400c100d800f03504411500020202d889032070b04420340c2c80480308503807260003241402c020001e072036084003032100c0151001c2025602d00f0075800040d2042420b101d00c540603201c006400d01240800b250046c10001d0a0f41c8800d594038500703a840d50207a003d0000201781488005105410305200f502c0a003042d042c40003200d60450384801e400d070344c0b0140400005603280c908c00b00c0d05074103003550008074033480c0d540c54080250500f003c034212488281151400c500420244201c00d40c00076290501c0066244001d07 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 590191663 1250 590190413 590190427
    0x608010e0f150301020307022d0a0311010f11090117040c12060908130305071a1905070212030903070b120106030b030f0d031a1909150b0d060311060307080c 69
    0x2109502d825019030641c000000c011602e83e0118824000303240000d00d0a01d00c50300c1d6007840011600c9030a111519034040001800401d10540d034540071400c0000c000514000c94029110903100010a01103221000003020117130380d40d00c8007110700c40286004a00c2c00c14101a901c10880128a205055402140300d80301d100b030190780c0d0b129001c01c50b4090f90755551062101c9480c01c415907140700594050080240004200d151800001030044410301111314244880705c0c1403008020794090790382003240038800b910040c1c554035140c0840c1c80e00000156102c1107000d01709407600c07095030030800c140a428001032440c88402410141925400d09010035112503a0340802d107416000008008144110b603000d807185a09580030610f0320404042c10314038021300209000c210f4841e6040350400e000507003000c204440c20380e40320104c0c000c444030700c164a0558608800e80340b81c2003403290385035041d038460040041101186e60280c07294803e40d80382e4190700d8a400040c2c0441c81c020042c002c1c01d840010341d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 590192913 1250 590191663 590191681
    0x90b0312030a05180f030a0302210a061707050102030f0c0c06070b01090c0c0312110415020705091005010c0f0609210e040b0d0f17120406060608010e0f 67
    0x3818645520640d51285400882440a40020b4504403000c0c0388544c2c80c4003008030081103007000d0700400c0740214500300032840110000d60200c111208001c219502160150754140c2c0810f00403801c0302d41c04110f09087c00c06070f4400075004004500a54040141040071366000300503a0212107a24407095210614400c80c90b0a16802e5a0b003d41c1c04000000d0070303001c214451020f14140e4002000411400560000a80d0811168807014001c101c9100800020b031925800c400d05034481c0007003050610743d90324400720b51076002c0071000d009a0010441400781c2d08110b0004caa00c00403221b1021003180c070b04000078015010003400038044031059840030701402050380019000070b0b0301100070300c0d1348417180e0501c803d090760141800000a5100c920780946152038012860840001000032060040650b43c040d014120b0010480d1442c644042e0706003032034030705005450a6a40a511200c0f1450303c0c0c40c21508a4002d50090401c0c800c0030b200500c2001003080b001613000c9116600d00110361617403104 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 590194163 1250 590192913 590192923
    0x6080c0f0a1206120f0f050c0306150f06070c0b0307210e30070201120204030f140115050f040207060c0306140603040f02060f1603092c01090b03 64
    0x200d5034400c000640788440030b0b40240c41140c1158410b00c100442a1584840480203840b400d000d0194201c02020b5000b14014400000c2064460011101e0f900e103d038000c0303420070808491407400c0040b000e007000e9a40c100000300540110003255440c1c90300c407840c2d89840000406000b60030280d1404030005a420b801101d1448480740c6103001012204100c81002000e020207a0b1894454012581d6811000c0c1c000010324a03608400583ca40d203100d41002010707403e401400b81a8100142981001448a40303840200061030141160501d00b244504069400c24404003009586a14011000540c10080c4101d50103813003003100c0084001c080341c000030b00039008022000d40210710b05440c0e0100140c0650003407007151202005002c070b207101c441c200051408110b5018200988050086005107428401418141c04802d801410140840c81c401d00c0c200a80c4412004100d5182c1d0034880301c1c030351045c55083d1141b02e142041140130300000e45660f584043c030684c490349486104401150b41c090103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 590195413 1250 590194163 590194177
    0x507180f06080a11011b1217042a0b070c0504110304050303070315032001030c02010b03121303210210020405100e060d2405060c030403150906050109021206091006080c 74
    0x16440c0600d021410040e8010000e0f842610101d0411b651b4198011030080c1409d00c240e07080301240a1800d280c541303900021141d042d00812401443d000403951101140141002c00e0058010000c280e0038081030204480501140d81168001031040000041001048a900580a1030045041110140c10a00c0341e681da03000101503966003003001680315001d00740380310a92000d0703070180214294581c00760301b06c0e010407081c1c581540000d0302442003002e0a60044c1130002d180d52002c44030075500c1d1207000000c0b0261407000040600c400030a403005504204100c0f007000194000c41c50940703000c0000e82e420b00c00041c10010322403c03604420740340da03400c0e003039400c00480c0344024810401d403080341901d0701c600010416416444a90041858206003003902c1c4a1103100300110702e01800c689541c0c10000e000022041e113143ca80462034000f940078000e0300d0081c01c01e020b015071215440b0079544500300c00144458002c10300ca504010b0b4444005084030102d40b0740f0b0400a0040e20381c100009800d2080340 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 590196663 1250 590195413 590195447
    0x3360807030507200103110307020312090709292223180f01091106180a060504180b01080a330e070f02120a0c0507180f06080a1101 58
    0x1021302003201103c0301c820305190001741c0e020003c18204c01c3c84c00c04140401c0e60f5050059005101100c50344a207550300e130b500b1480080440f0081991211860162284200d100ac10700002c1d04000100d0502e07a030a80101140c12194041c0781e1002c001d4814000906030000b0764620b485540802031003101003140c003101b00c070315444030f496491b1481c15001449503203403a9030b48a100305203a0002e0707410306124000b60310740c0c09820304030000102002c01070241c00118104043c402c412224040c0b56691021090041c0702940f9400e4586141501c00c80c00104a0000364112900788002c0f030055030b80c0041c8003580901807903400200040031615800d1304082010f03103141240c92140041044540384e041010454607400c005c500142d480702412508a0800001100075a001c0c00181c0d00c1c10f100100035125443c602d1500c180c50f44129100d03d85001c0560344089079840384c28241c90500803460040c07400d0204030740001c8c481c580c0740c01402a561000004050811140071403942c009030b114500b964181c40c0c801c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 590197913 1250 590196663 590196683
    0x70f0602070f020d0c0f051801032303030a05060a050f0f01030f091b050906120d080a020c031204050c01020d120506030307050307060b03011a01050901080a1b03360807030507 77
    0x10b00c5d22944120641c016181081115080060289010b86181c3c010075014828000300340d00c0d5559070741915824050140d14511801c10b02d4041c10001c00203103200b041c55032400700341c03428828288000d02c4999041203000350801c080108558480c40306a102210080ca00050810507583c116070040285e002c008220800b800404d945918103200b0380f00641d8400c60f003001161300c0b100c0030012692240c44210b0200d8011060179441c01380030f00c0d102c6030301c2101c8600144c03030102900281810750388480e40e40100045180180010701104000070800b10b5020300042084421141d409010312803a103800440d200e88400c001226030300d0030b006951420b6804822252681c04c03a01d49040034041c8555814000d41c83e1941c2c48402034400c00360080c0400060711541c2ca40440d40380110307107840c401065020324039100e22039250340b24842d440d081000350655a0004080140c2180d4540d01d818845072180100b0050b031090480314045140300d1462544004011b175200700908c1d05071401d00900e84064002d44603 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 590199163 1250 590197913 590197939
    0x7020612070e061b0d0305042f310606090e1807081e01050402010e0108090703171c020a020c0d060e011d060f09100902030a0f050a17070f0602070f02 66
    0x850100b4070f200100c40c4c03094a40f080d90240301241240c804403009418441c40f602100100c509031242401c54401010340481e00d101c1034004100100301d40606a074680c2c000f80805140484500e400f1500389040c1c0b0002d1107002c0c070345180100440c00c5801001c50004600011031403850146c040b40800744e8850b026144001d65844036140c039880100d0750540c0c2400e0f0800c3c03004c4006010701c00d01c0d00c1254142c407904480403aa00c0112030840005010070403034801e03a0b8002c0301141c5116104844941100c0d02d180d50b0b506d5034170103c00449170039001c0c020081d005000520010703030040f51140d02110290341142c202c03030603401d056001e0a510124201030754640141c80d40840c0141400c280b552101070211040c030313110201040101d0001700c40c0c07010a608540b0140009103655049a0601030004049407024a2951038404020034405c0d800c884551010410b0000c000c101905c902900714958400c40c01c00c030060f12060264016428003e1000d640040e81c1010131010040c0d8914080e0054401d80107116 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 590200413 1250 590199163 590199187
    0x10602101505100c060914060121080901200f010c05040e06060c030d020d06150203120402040e030c1506090603060c040b1c09200406060c080903011407050a03050c07020612070e06 79
    0x3034840c7c140864080d0800124011640d0340740780a03100084a28188884115200c0c26800c3d0880e102041c1000300d80b400100c9000e8000104003002100d2070040c0088841004056085504000c0b0f00c00500105020401500041e20b01c056801b4605031803140c0e648040401440c01c40c4143c4003550710003480464440489072031a030080d415a0081802e00e40c000a4090060b81d4038081c648903074410b00011400140181400d0300b0094000e24860112400c0a1f83d8500c0756017414840307500c90750342d945c080d0100710151030414207044e0410720a50241c40a800c1c501c0c00410184510301401000110006800d08010507400e580103060290740c4041000d001603140c50500701207031040791100510881c140c88501d14181c41028200c1e1099140c4200d041c00a0740e03454166045900e8442d4036558489240400385108078001c1c0c400c2d200340e640d096451024101c040d00301c41001d444003810500520a8500580b01d0404664102c00c10361030000255035820f108541c0c4050410449070025000318400c2c6000f0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 590201663 1250 590200413 590200433
    0xc0d08010302101e031e02041e0f06020307031103300a020a0207140301090602070c17010207030e0103020c070f1502190203120f12040803010602101505100c0609 71
    0x80e20884003070794401d003003a0003150030130440302a6001e0070034000d060918684c003030341c080501800e250044e598030159145008040740c000340c2c860546012141080c020500d080c0503100c014107543e420400c05c2c0e608040009541e03015500303005051150750a01416002010420382d004041d9600040c0745a418024401c1d12a1760418001c40c500141c0f400441c01c200c00600075250240307015401040001e140885800b40401d19000301c540656030f40b80d00101051060000b0681c041c0662000c101281c0ba1010544c140100c1000200150344144074090010754011086c088000c024a405611101c01c035208505092030ba51060314031004684000030100c0c17207140c0038081c2240a80a50b0050300f40041030b444002e4482000951603006003102c1014504100041c0c56183c0035252541d080083c9820b07403c05000b0259815110600084010041168100001c030000600f1100502070014041801c182c0c001040c00b480b80b1036842c08a0016020703100341a0396040b1904450140100c01160500c50094 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 590202913 1250 590201663 590201669
    0x20408030301090618060e070c0c0305010f15090908030105131b021b010801080733020c0901090c0c0209060402120f010302270a0f0207120906090906030b1504020c0d0801 75
    0x110b202c03034010401144c01d1b00c03404040300c030704c01a40750256a03240c04c01c07100103500e00812a9051031840010012603401d1184030038540504c1000503c00d80010079001c6481d05a030f201030341482c2864180d6001658003030580f07044500560302c01c04180c00764121030016000d04a8a102c20381003030010540020b03400034800100d80365030500a41c628508000440783c100003405484015400b14004000407080e840a480d8040e00400300c2d110f602c2607800310600054060b204020059004040b012268075141000d68014801244100302002c400f540180040c5014040071348983d2015000500b161a141c04440342c0e000440030802c0d240c64209114281c000d028001030b0300480350844402040c00c8100106d29851002000e001000d98841e64038901401c5910381e4826501c0e002c0c8290400a500150803d039820082d84415070759a080c00001400f0b101250f01c0030160310309140302040481d07075004499402c12220071603501c0742c5207850302050180c410041c19800034071840c4c400300c04113680000400d0503 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 590204163 1250 590202913 590202929
    0x604180302060a150605090f030c0d080307031103131106040f03080705100509100923010e010f0209061c15120c1a0a0c020a05030f03131a0703050703030204080303010906 75
    0x4a00d0070015680d1343c0c41450301501c2e0105608104111541c074100310008411900101240c03c440c0c4001c1c041039200003058022900c2d40004028082e010340c0501031550071a050042403070640c5440e049152050080310000303003801c030181c855401e590b11050300302c50140181c14050b8440d1030b0350345021034041e48a45826951809565010740d4010254090180106186402040d0a01c9819803541c01801140b0b01159214900000d00307441c132004046929102d00b56500010322000140300c6182542c0d84040d07101a420b2040219040d40c0c1c1e60344098032181c13032420b14000d540d03100610f0000018582904011218401ea1a000a510303c2d1844500b044038811030480030001e507501c0402d50002c43c0b1000c0405030150038821295070502c01d00d80c940300385000030140484075507500b0129003070610301060300309140c00008210505410705903005000b0702d4004881c0070340075101c901e024960300a860006041200001e842400c1c94400e8068030b0141032030340d0a60390349594905400c001040e6074412040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 590205413 1250 590204163 590204171
    0xf070f0c02032d011b090e09030c0604140d0806030304090e010212010306060303110c130b1809061501020606031b030709020d06050a05060c07060f140304050a050c1212030604180302060a 82
    0x502d1466540b040d001c000e10036220840064101007d1141202004040e10401d00c13080c8500d0003e02c40820042d03001d140070b0407100320040201c10310541400d0030002c03203900f1300ca2800c09211441c1c80000480d0120340c50303544001a4001c075030041d50301a04ca5a11f504c1c0072100014000700902200d5030029044034404d48030300302e0803400c41d2080d944070200411000c0c0d00071a4184028540c0c0c803e038001c5010814014103004400ba20300e5606031040900341c5100900f54490030800c5415270700c030110040b000c0001d00040000d8609070000907695a50904403169401c507039600c0000d2a1010003001c4054a48040250349070881050b04000500e01885241d00c29031400000113440d080600886100e59140c20213041400d04100301a40c0d0402011003d400b0401000b0001c0c10303250108001c0c1d4020340c40340c0080c0011a180b400d00e203103008041e000c807074495070744580c1448010400083c3c0c0006445c01040c159140d070350f183d001500038114034081440081c082d0b08401d01301030780417880c60312400d20440104 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 590206663 1250 590205413 590205431
    0xc03080903150f07050a050706090303140a0e0c0d0501090b0414010c0509010e040903180f170607050417160b03060112020c031804060f08060703050f070f0c02032d01 73
    0x30010903820f0303814080742c501c680080359000c0e00c280c0c0100030280490a0162400e042c40e50744030111010b8075025400a550f07a21740306030300306240d03c80c5900072031082010320180104a4210b501d401c0000099881200041c2010040000c2074124100454010300c0c401802c0c42e10f8100081e81c015071039001011546410710b10000c290056042d9070348240113079034140d00345181c4407c4c0001400d20b00800c0d818005980142800300150140310b201804540a41c006100d02d006003110b0391038400901020300342c10803001c114800b607021042d034048900035600e100c41451030407075450500b00d141030b034091601a47d52003c07640c00c034030f44015806280c0030384e40d03a0f00d0100300402c003070224050038070801e615400030411085001c0b0b690b2422501700c41c1c010400030304e80703686000313280c030385452a4055000c80c1c21510800041c95050b02c5000c0e885040101c000b109413800c540005c10040c5030155500a000400d04454155102000f1480281417001c810034592203030345c45c0c3d680800c00c070001c00e1951582068150 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 590207913 1250 590206663 590206693
    0xf03050f0103031e110d0c031b020d080a05070204090804260d03021b0703050f0d05030c07061a09090c1302070c0603051801021201050a080a03090b0a020a0c03080903 73
    0x381d040740d03050750300c0e521030300350f44610400f400d4180480c0004008016043c0c61900c002440000021442c540720703924000303914135001d1306080b052007004003450307804041c2c1070150301d035004500c0704981d026072260703134407000400c058405014000c00a50003525080000c000c01043c0401030095035440e440d0300c50409505203410030710b0340340006140d81c25081011850007250094025014007041d42208000c54543e01c080ca500e07082c069403017520264801603a0486011060003071052591981c90705500d14a05000504814411110010903096880d02155220300d00c1c035080d40c98003800106035a00e2800c00d1688aa940c48094107228403ea44840c10a10101d80510031a00865401442d89024529280060380204070050061011920603144002400301c28401012480202d0040b030f4459414101405007507051504403000302e900411003540800d4002503003000310380111500540d5803580d07503012400c00d500c4001c0103182c10000c0402004000522010b001c0001c0d00b82c048400b0070650100d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 590209163 1250 590207913 590207941
    0x5031b251b080c010c06020d0b180f0f090318010309060905060103060501050607020d02040e0c0d0c0f0f080a061a030a0605013f02030321060a08060105060d0506150a0f0305 76
    0x3105000c05c0802180c0d000050141d00039121030381c03005030002a240d00e81804161031105405a01102100504c02c0298504a40304120f4002d1018601403402e03251441c0190780c0c070710603403281c06044c6101d0b07082c0150503846a000000580d1b031000b030a2103074030810310f000c9503214000c0c041290441c1c1404008201814580180c640c041d0700101200d518040340d409000017032075080b01081c124090010880c005450750381030b00c110136110703440020303040c1d02d4182951840b41032904030420501700800b042002c3c0300300180d002051500204d002a000b0104000d091030803090181703140c3c150043c000b00c9418044154040c604a8078440542050086410030428a4048103401d215910700350141c901c0005504601040d09148064100c0707180c110041030b46d2500100b41d55003100084046007c001507824075188607402004503400a0526504020000d01c09010391500e031070005079101d0016650f039540580914111941c2c011003a41d92419420044c04e0143c8c80070000042402d003404103101610a0035 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 590210413 1250 590209163 590209183
    0xc1501140d0609060f0203071e09030b01091a030f01060e0c0717030a0920010f03060b0306040207020409020a090209180705031b090a0b031605031b251b08 68
    0x301c8961051165070302d500c0100708281e0103455081d13403202d82d075401c07000c0380c4000c50140400da21640c1c00c49500015203030550002044c070310108045501d00700006480780e040d0506440b2110804601001103aa10380064600a080c061b850b11991589010a04065015406503400c1225100702c6a440c0098248244517584008104940030307034080200c00780303c80185800280317184000c18683d8032078a5440e6180d00324a242d40d165404450700708507560b0422034810086115041c10b008851038900000454000100a1401036400145240842d5915440408620b82c0107081d040880e8485c1000d2009400c0311381c0c000d008104101c4c1445860000c4c0642c540f151110780c1c0c410303103142c0c1c4014440c014070350b600c0c4141040c1541403080c9a1303641e503820302d06005040d105220a48a00c0c090704a03c66108844200720280304080051014500b1003001c1c080d007907003d8954680d5100e60052011100d518a1000741082d914030044003400c01441001300c2218021111002103040d8491000ea82c540042e80 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 590211663 1250 590210413 590210419
    0x6030f0e0f030d050403120e06180a030c021002120c030903010e1209040f060b18130213050d08120901020c16080303240d060203090607030908070611040b0c150114 72
    0x4060302e01405011340003242c3c0b045c030034503010001103d118006815144400030303c031025041401085a50305d007803d24440b000302c80000408a02c0798540700a4201c0c140708201901903a410003800079807500070480900f5154203204440c0d525103001004540360b0f00b1800c40140f080d420164204c165250000c5d406414a403d542e12524001d007c00030480108000d4a00071811506e400c2d001079080401c1c1d0160154031582440070407203805100030450710080610740c00201510500c180c03e90400c01a0141094920035500c0740320100301824030780c4c600d01500309404803846c4007034200300187c401900501a241b41c00011502241d24113011012031648a00481d0100d900a0000900083d8104a0704000c42100488090224001400303e91a161110780641d003054001044c064054020840260b000566140c01c1007070a1880d620804644101c003006840561102030a21600507114225001008100446540c9011070780120b40c480f12100180404030710640000902d130031540c5a0400100310003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 590212913 1250 590211663 590211667
    0x101e0903120806010c0611030a0c080132030706110d0201020406080f070306030b1515040b0a050f0c1c1205221103070603051006050909040b090f0706030f0e0f03 71
    0x491802c41e01d80d80010b10140c10032080c400341102190551207440e507100510300c00c46903070b071518200311000c1e0380c0052500303000c011848004216000800c0a070f1b143d0041c510b0024241c2011406400112442c1d0306035596241c081c2503400103002c0c0d00002c164011100e03540035600c0702c9111303044c203070300301c1c083d910801000c90241d03000941d19414004403594403c005050008040c1e0710794031412621b00c01103500100756002041621181e00e001d041201c6080e0001805030301c0d16080c0f166030b107480d0080c516a001417150200718846400741c04025200d0700b1345200c0c01c44c0c031044a16001040e00d90740d1401081c000c10307010b50102551b2600d81c080c0f10300c90816100c001c401206030f44210f007c64002e5010031340e0107850040c0300d0649a5428801c00c0c0c003c0819603804078039410042c00a03002c1444a130f01840600c0010400001543c44180c01a0342c400d1300f0440703070081c4d5510108000e090180f200e0b011000c601403543c0110310640c0690203004040c444904c20800c0203801d140c910703900c01208003021501d9000b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 590214163 1250 590212913 590212943
    0x9122118040c0c05070902310608040305070f060b0906010507020f0f012105060406080d020d0c060b040c120b0d080f03100b130305100b0f1e101e0903 66
    0xa03812100c40d0401c6441c2c451040c1d4201c0d10f0f800d0500c1c951b604155a6241c00050014921105255400d580d140d0030038000c40d00320304540444002ca41900c154000d01001200080074035000c2c4007565011a044040c52404a0b51031030401c0c002d01c1802d41c1640b00b00c0410b000301c0e11652007076042d502c2d820b41c09410001c0c414580e00400ca8180c0e07006891604210040603c8410070a1100e000304400701500030225035030400e40c08000030340d003064003d1121a8440d941c2c1d102c00f268009102c0d4000413650401c0d6101c1445810040058400d51442c0b680050400003941d40880c1d100b0158000a000f030b04041204c40265020051072802b06400540f210380244820010000c000d00150b807c448011000c40d042a959006504d864204151805404040e00d808005112048c000443c0e05040792000300950700404000a0b45c00c0b0003400e009015803281501920036851029100c9280b50001701110011002c2000c0104421107080c00c410301c2202c2e2401c00b001c118012450402a254081d980f5039075461 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 590215413 1250 590214163 590214169
    0x1005130201031a061803071203020d05030703020d05010806060405010806060a060503090a1a0403030509010606050409090507080712060b0607080a08100e0103140c0a140d0809122118 80
    0x3094001c1c240e600c00c01100f01d040d46540f104010801000001056000c4407100b2042500b0004c00d644030200410f400c07a1030720006a408940501c0c02d54640c01e0081d1240c1395a00114000d005001c102800b66281000118460400041700c0340709400071142030040381e89400e10a43c5400781510b00c95004004000c00b44505805030005d1a40b18030860105c403c01501a25131528500907241c00c076041e07203803081c148428164035020300b951007064000284107052811000800078031403032141c01300050b6244041c1042007814030002c0001c02c2e50070116a00d03161100030742c0702d11844031001140e200f4a81441e000203810f06e0f0056907803898202c080b09042001984058072030603401000070315031248800780458258003002510703000c0e40c0200b25000b100c0182c0301d00c1d20325045a030380480e803003403480002c200119111410814502c020980d01c40300f406400b03181071102400f030120030641c030844514420200707083c0060303010401350030001001642da0055204481e18424031403c0d1000322504562411541 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 590216663 1250 590215413 590215421
    0x11030403210f30050103260901020d0c060f05090304050406050a0509060f0a0306180c140a090f0e03190207120b0f06180a0e0d0906080a0507050f0c0a05100513020103 73
    0x1070320035902440b0f0321440c0742c9410413208241c100325441908000e509000350b5a108203401c000e800d004100e8501031120001079515804030605004012403000004c0410065400c5401007100d070101c14025420959001903c9401902881d4051450540c000440d0f29041103044100c550140c0011b103103494000038031282c5d2404051075900040f1369000040016241c1c860034102c00860749205410a9052501180d90b12460f40244000c1c1c0c1e4481030468180c3c3c0303080c1030608503042c5080000b401c02d2100100c0020309602c21510065000101d918000b111f603210640900c0340c01d590a640c80551200d4a03101d14035020703a000307011b0f4040c440004000e04081c00d40355822007801402c00b00c40310a50507160128010484405640c43d480700100d0580080800100154001e01d0600d0640d8a080102c000c15485000b4200040542c03240c0100ea038242c000c60846801c2c0004006050740c516580c0c1413203550310348040049401d4403652540071607500462280c03902582600b1071040c244405900110007030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 590217913 1250 590216663 590216717
    0x1c0803060913080703020307110402040e070e04061502030714010507050d0911040603110307090e0a0b15060c07150212072004020c0c011403100e0711030403210f 71
    0x2990b282d0b003a42010803070700005050814400d5004580d11486890248030548000d010309000c4c0340140814014001d0b20110107610034054940551541d4180001501400340e0b40e00510000101c2300d00400031690210050030340a000b000080e856809850f502400c0307550495044001440500246060301865000440303070500640006c011424a040085c00325171042c1c0c411203009400b10000000ca0500b8001c40004103200042003100c841d81c44681c030b4680070790450060003001000001545164800c1c000501d840c4081c09607038458451059030360f56480d10f800754020003103c20306444655803000462031084d0002c0040307a41428404d55800346044002202e08040b9102c1e02c00d01d8084d919a84041c11461f8901c000618440e94100005130640c084101840341c1300d0010002c0081007140c0703074140c1c01110b52030f01e80c235015950344603400c40780c14900e55a15244c9000014000003808048410f0f01111030680042a41281c1c039090141d9800480c7d19080b00403071507841c848034110310840400102 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 590219163 1250 590217913 590217931
    0x7030312020c1915200f0f07120206090a08040603020a02010e060c19090f1a0705030c0d09150c03110f1204030b060909060103020913061401051c08030609 68
    0x41591040d0b031982003070040306880990074a15054001445060000c45002100d560010840c0d219035151900c0000d204080064101c04000389614443c1e9039002103814501e446d405503a2540300c00c2c500843c5110300550034400510525000c40c1803003c01081c1d5a000c203504c420481c0c40c040c940300301680603402540c41d03201995612401462401c6040c0402445000703000f4103503036108005104040d03d05101f4850b08200311144030b060000c0d17203e04100c0400e80c0e01400094034001c140c41c40b9403015204811008105001c04a1400c6030350303000040e03200b50307003506ea1500c01005440b451015107148201e034503900095045084040800d004011410700c148004040e00c45c0c800c00346030482d213000b110720589170400030005810000c1c006449002504044115002049410305c0700c8087da85041c180070103481411403401040881d810711001070040c0e0ba100c1c2043c048081030001d2046c050300c00744a5680641400c09850038017450140d40f1442155006000720b003580c942c6001d02c0f003007500040c00110 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 590220413 1250 590219163 590219167
    0x9031209050910080120090d0512070c1a0304050c0d0309080a051005070c02010f03020f0904050c03102c06030705090907181e020702010e150c1b030703031202 70
    0x240e00e0315942c03030a610900660303141c0981945811580d508403001820200c2c081030031020207586140852007211404481142c000d04500d4807820500c0c1000501c00e01d10032807141c000382c00410009490f4905048074007440d000c14002d00c1200c81071346140b00440303000700503800000ca420741c54501401440c6040303001e0b1030108600e645803c11180b400700d150a0a848a03842407415440200f0180182035000c4482e2508070302426103580003a0040301c05540400c1819000b0620543c01c1c1555000e40e1400580100180031a003080c2d940c3c0541f50f401900c0040d40352406100101d0b00172900c003800201c800351240c8070f100718011108030115058010b090568035000c2e600c0c2c00134a6941d41c84015000345104005030140c0340c94040d201c4039560143e5030a104c45420040b2410300001d001031500d0540c1c03030415016a99100c02d1004903111542000703810382c05082e0104400c14413240c3e0340034003c0035401c407007103610108408080340d000426083c100d5070f055010b80300a00020b4031a920310000b1008840d4058 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 590221663 1250 590220413 590220419
    0x70f050925170610050f251401050a2a021212060a150215060301020702040c080603210a0c0203100e281109060112060b031b03010609031209 62
    0x700e4005065039100c0001d2900c0c0580301404441d0700282e402040881e0380d090840c0d18944050900d00426000c4541000f000c01c5184625601c80b009681310340442d00f2035800861540750850320944000c1100440c1c0d031038200015031144d05845441200803071003240180902c0e040b509202c20300c4004c01c080045025015441032032912a4000d8220504080e00c0c20b1882c0c42c20505200c681c0002d9440220001401c0c402824055000304040d08c4812000002c1005070b603806c00401d02a1082c441d000350441e2502e50b413681100d900c843c183d802000100c06641c840f841603501d01c2c83d58403a00c3e90003200c2410400240c088d15000340c2c50005080c0c40a401d0f00c841b4142990500304903010600a80c0882c0c20500090910307940801801e0b24010000c01113000d03404203a102d940a00c0c850701ca402e03004601d0701003c81c070315070301a294803c980c240c5403c0502c1a2900c1d21481045904140c0d450200d05c0c061180b12800e072100c003c15681078a0681d41c0300e4003050725546412804c01c3c455003181051100819001c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 590222913 1250 590221663 590221711
    0x103090c030f14031207030b0a030b1807060c0312050703140f040b0601030207030e09040203030c0109052a031005060607020a0303021f05060127080d090305070503070f0509 76
    0x40c0011030142c0014100c610040c202001c0c0464001c031002000d0300304001452008a0b0f41e603005800036034503d030024001ea440008202012095040a0164000d480812401040c05003402c11440403800c1903d012035961103041d5031046410324020003245000344684040091580003e6001000303203804240a10340100c0444a24819504108224100400c000511480c4044160000428a008c6241130820344006000c00e60000d401e5201d5640c80740868151354081040d1a040101d820080001066900c0c010b9540d5a40b1107a8440e048a06659860340e015111080450301c10060058140040d21052310001440300401d500d90040c4184400f801580b118502034015510980080c1001d182a0410210320074041c4890311000341000c0412445903400694107449030240403006542000050140c40848855007205040e031041c0000101e00c164801c400d102264020000d44804503100e00525407500214010001c0c61403100310100018106404451b5001c261a40c496410840042d40c1e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 590224163 1250 590222913 590222933
    0x8070c0f05160b18090c0403060207020a1502032a061f0f03240524030c0d0b0f09060f0606070809030f101103041a04210207030308072c010309 63
    0x105804104003c641916043d0341c1c01c000b00d2007031380100d645102e00c1c036110b08600c013a07101c0c90000800c81a0040340010847d10340202d00c070098107030840d22001c8810086c4000b5900d801605d00ca0f21056180da40c004048050f0048150070421a1030180115580c0ca4a04007440903501120260f0074620502c0010030f800700c65882c4000c0c6d8814041899608104400514130a490a03951141e4501d050140320400c502507900e401d0b1082013001380315242040070000303070900c00c02138501078011103000400d500700141c84458510034444c81c0704490f0551145107034160f03203e50032a029110040282c2c041240d030700e044005400442d2040e1080351a01322803c001c00e00300100f000b000345603984000705402901c40580102c010105507240d242d42540390540f00e414036000394407655145220100c010a0510820342d00c4680701002c1c0e013080c10240399800da0001e564001c24802600003400c00c10100341854843e4400c0781c1038801c7c844030680b003034021820013509a500103152038180b40d96501c100b0300040040394 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 590225413 1250 590224163 590224169
    0x1e0506010c1a15010305090d080606070614010305010e0303100303081b070b01080c03120706020a2a030e0f010c02012d05070620070f0221160608070c0f0516 69
    0x2c01e600389403c10b141812461049610424145400d00c000c00a08000004000c04518900d24204020341c580c01b001c9101403103139240c041d08003800c010081d01b1000c03c0c0c41a9504880c4035800820030b030a844c141050301c0e03010075509180342003480d4804001007031140f5481600650403100000b604110000c5038240340e80660011950000000010010201d0501c00000254000c1d409032a0000c40b03101040400d01c25900c001305025408648000f981e0300c1203803030344403e40800041f011168200c118040924031104011000500c07010300190f07150801c1310f8120107d600684603071300c19076095801580c42c0704181e0f908402c5000b40400131391440b08070300e428030703208902510385640d940c0b0182400d1060750030807040000b0b03800e1010301d950070118a01040301c00a0303800171720351858603c2c01c0c0300084010030f5000c01e00b4044c0300f00201c10081250041164006121408c0402034000c0c1d0350102565481012529000883d00312810ba4000c2a124600e030b071051442402602c3c1d607039a540c0710009146080fa0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 590226663 1250 590225413 590225453
    0x120305160c0e040312060e011208030a06030203010e1b01030b06070f020d0c1403061308040e04030c020a1d0907031205070c0e15010908030301080604080703112e1e0506010c 76
    0x244030000104a544a08406803a00341070740500c540c10b01c00c9d403108080da280c10061039140004006010034440b80d00c00c502560b40100244505207001c2d046e6540c80188000c0c1941c905451181c4050f00c0d03001c1d01c03400d110080c02502e800d0400000e61541807591440c80f0090360401c42010822000885021407400905100709520201c01c0c407220600d450b00700020680e00070700d28560040804a10030f0410f0380c0444001d01c1801e0807130394944c6001c8821014540e0025080200040c2c0070400080441e103100303a1254803001c0c0d540e1682e4440503d42d54815a10000d048002c2401c00020042d20030b400501c0071501850180b94080e075140c01c50b6000000c200c6001407c0300702140a600c02d03681c801d61080040446d50000c50655051203141c41c0c03501c00c0540004d1015200180080405001c0c80000f0845000e00055411300d06100d949200c20001240310012007070b500014229100b1514454203000142c092112801c00100d00e94480080c40050405810b20540120110002e5205550360346040030716 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 590227913 1250 590226663 590226677
    0xc0309190602010c0203070507031103100f0203060f04020915090d02130507020f0f073c08190305120a0e07140109060905011e091701020c07120305160c0e0403 70
    0x740090846621290304001c54000304071820100ea800900380d02641d810014202e0010302040000b440c06a07031001880555080a034030441c030320490741c051031141d44255071002143c6000810002284564078056500c0541c00c04400191452540031341001c0c80094016040c1c0c00194000072000f4401d001c5804016440304200300e0880e5050050030541010800148810354660614946540d007502551a104444507204100140f03401c5c00002c040c0d41b1580381509802d0007141e6000d04103503a02558800784582c60041050040c0d182c2900d083c0ca07015502c07641400d41d80c1d83c01c101911000b5180800e02c645800304181030040a0010030002e10041020550300c1f0082e900160101e58103500c0038041c030124a80407c070603600102e0312a60483c0300360500c00c1890585400341c1c0e80c1e034a150401650030b0080e07801404102015402020440c4503c030844075059a0f840d200344000e04100c4006000410500c10380b01030084000a000c44203100d4541007543c04c0d2104540108884100c4060b03000601c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 590229163 1250 590227913 590227919
    0x30f0b1f0b0d0f09020a060e010c0606030605040b2a091f0503310303050618070903030306170d120e150f1005150a1e170a020306010e060c030919 64
    0x2d41c0c400d4064524103603100303215110107038000401605a5104850078842412009141a031089a100070005e42c050401c000240c0c0700e040100040c101200c048805600e100040741e480d1010038021044500c200c2842e80480e0415000310301660032440150303403c50030581e0300440202c41d109401c081c0700c0300707550340c00c0d00c80c90402d04000c0c1000603120310300c00701c4511000000c494810b0345000030040d40c00d414082550703190503012a80002200b6910b45142c000e05080c00442c2c2e6110700c030319040f28080c0d0741c24824240c803140c0c1c1e10803130a04030207140400d81c828007000c03442c1401240c2c41110509081c000080f0349048441160404209040500040d0440d038104206200c2c580001501700c0c110720014041c07241841d003c61141d85050000400307038400070034090b500d14401c2011102134042d4000300e01c044000c55401402e0070703441405081c000545080020b407012245d2081c0ea204040507540e1b0441d550400e024403400360301c140c2d041c220500003040850582d071550562035a01070b0940f807138050700c645 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 590230413 1250 590229163 590229187
    0xa15090507110d0c0201020307111f050d0b01110a020f0d0828030b01090b0d1d06040b060d1a0a0b03031605010b100c11010519030501090510030f0b1f0b 67
    0x1c1488086051001d250041382c0541d034000107a0300c0c80350340703d545040341010010020780d80ca038900441c03001043c0003105091210b41e012010300825400d084007032040d0312111005660880500c1483d2055501070109400503140501603265040409406c2610750038950f140d0f81102d0340085102603209284041d00c1c21210785905217110100e43d989010840c0c01c59030f5000800e144031032701c80c1202045001c500000c0072500d80d1702c24400f5860300d90200b05025420215941ca5803821102507903c168008002415800e2a0034005602079200000d81c0f03065494042c3c0c040da03d24050a1034031256a03880d40d0700c9903901c0c01c0000f48424a0902010710248a00d0b14040782940c03d0002158002d0b912015489005a08000240000340e40142070b103090361615001260980201501c1c40001807076541203464240d05031313100b90f042e00d004003401d124079035400c0100441080e843c0301c020903074103103403c2032070200700c00b00921130700580c0c696070b81040e90162103070000300c548070368010122240d0300083d00c50f2200 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 590231663 1250 590230413 590230423
    0xa0911060417100228020f03120a150303080106051c1e05070201110717090d03080118020414041802060408150a0605060a0c0602071e02011d090a1509050711 69
    0x10040d1044d071414103100e0740308480c42c6861140c00c10800302e14040300c140798000d00c1002581841c038011a42c503001d40340940350b6405002c0e81c4400c09107240c0594403041e4041021000141d0703416803101c00690346401e004455170b61055540420001c8605a040c00ca076803c0d00603030041542082010b03010311010a403071400c944003e400c100075a80f506404556103c0312209135090b0030781195000070b0408058107410f40c1031160043c903941c442d00e010f80705410907404c40000c906990300250a02108405030304408102c1c07207a80151001c100303a2038a00809440d054008480801c4810760001c108402a4007181a9070483e0b00555202d420a82ea151602c1c80c0c0c21072296803003010000305006252400d000304030140301c0c4109820801001c0200c507424418290116100301e42e03c1142c44100500d4103070550907404c400d0404900203030706000c40126092121481e4a08500c00038162903e0303841d07060705040284000c1003102c100840e10f02002135030001d40d2003a103214841ca0303120207002041041c6528184 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 590232913 1250 590231663 590231683
    0x30309100513051807030b0d1707020301021b03070c0803122e06020d180e0117190804140603040b1801140f0403030c0c081207050705010903110705040608060a0911060417 75
    0x64050740d880c1e04080f5600340941c075042c0326002745190742c5182c0c500120f03019104d041a206010141c04031010b10001c00040204059409819132214060300c607940241c4170f21070243c1c02c10072881e480010888190054541400e0080c4105000000d101c88082a0760908415800100584c00601e40500e00c1d80c1c00200800c401c0c0414070f14180180d0504c00c08000c00c20041c0102c143cbc03c0e840e00d00a0102d00c00821a030160103205400b001e0072101c2a15003825107621034081c44a42c2030740c54814444909260741603d0140b82d12040006040d41e0f414190803400507810f60302c29580d0740f2107507000300380e07040107164034000c0c5502d030705444c40352815003405001e4484009400c02040441c90751308004c90140400d0758140740c43c00f18240b200d1740798810300716542e0240d070501034155481d10512200305038001040154607071015050f6903c0c203980304104030032901c076441b40c0f8089401c400c00003500d01c160781d401801c03024400c020501c0c610401402081d5650002d4114200a042d0380400c2c4852007420040c139116 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 590234163 1250 590232913 590232919
    0x20d0e16030b010f03080d0c05120f16050a020307120201112106060702090403080411062101090b01170a0204240905040203100e06030703150f0506030309100513051807030b 76
    0x240a286591b144180d03c140760481058540d240d1040410520a500302c6080055110030400e176410012058624101c0654101040d80c2ca07c9030700a100500402c16502c1c81ca0581d0003031030814007070703468030550364104030400001c42d542c46040c605a04002c2000d848942c07200020400d0030b844111240a10410182009201d28002d000d0300005039181d01d0040d034080ea040c90014100d1301c6901d400c4202c902250482036124401280b951412060800380c900850106105d150503666540e0b00b0320308481064044a0024a90b10340c50200390480240c4542c200c88524001032405d6038030680e420a41940000c90455540060162812168441801d001030070040b542181745003000303000300c2904c0c1e900d031185908029510000540c3ca0b581441041d00941d0000c000480380c42c6400b00800c0101019442804c000d0319050115080e4180001950302c1c60070040c0c00e41c2203002d001401030f10b00350810340c0240321f940c42910703001c00d40d0b8071045001032080040c0c8407080c05030704140c5c1c0050107031070904072400c1c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 590235413 1250 590234163 590234189
    0x7030213050f030618030c070612051503030313080c01020301060915080f01140102010914010c03060611101d0d0e01090914010e0a0b03030301080d090b031504020d0e16030b01 77
    0x1c2940c1d030104005401101e41d202c84150b020032205d145042d40540c01902440340a041c000080154020101072804d034161b403002c00080c2c5d41e003035401200d155104000c9415900c1400010032407001d04455030f242c00c1c02401a01e050603c0c1c0198507007641d1090f00b043c80003868519040161100d610801410b80305281002d88452400444961401805109119000c0b85002d0441c407070740d000390312161159810131105d05100c1c820b50b2581d8003030030222403000700003403401c0d1000600d81c1c45008541c7c0f0321f46500d0090700f8113841c84034419016100c00d4020303601510307500c0c903600c52010003000309068080d10740e02c5002c10710440d40c0001d003a0042640c0640e0b450b90904800070a20b400b076001b4241590003100041201e03480721550b5000074100c1001850701840008004121000c00041e040300e000030300d035549400d113920b508007051640019114141074100091003076106103070503005008451108500010300402951800340b40800b0810384400c0c00c2900c001c14014000f003040d00038058040a0211a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 590236663 1250 590235413 590235439
    0x60108030c030702040c03020913090507080309010e09091903030f0f1a0d060f02070c151b0f051f0209010806191806150f110c091f0308030703021305 66
    0x10381c0b42d00c02e00708000c0c0704569440394110094040d074162410070001914001d984616002c1d0320b0002c2041e41400d440a1140080000381401c5c004101c408043d4180d4802c115046000d041c01280100942096440d018004003001c02e8030401c1c0050003801d001b0341e00440e41c02030500d0700b003040f03071040d040f202c0c0042e080052218041c001000c00007031005080c0c400c03505003515400c10600901c0305508000616000003264028000d124011070240c0366a8400d041031503a8140c019900400d0404e00140700001e42c02c1480085013502c01e070056014000e07029115102102c2d144c0288907100107480c5089142d010600100310b50b400401c0c10303440764090b03540461110140050007803005191148003001d1380c0e500d000705002100b6400401c010f100072140420803449201c3c010b00020f50400c540800180d22090912100d00d001840b108803200c0501740d081c00303484da906041109040c8482d404042e030386030b500020014100300000e512400c3c00360f40050700c40384141c0000490300d40325801503210350101c2d5900c13 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 590237913 1250 590236663 590236687
    0x2060a05131d0412140c0709050603010b09012102030102030a0509211804091203140c0322081b0123010b0a030c0215041a090609070e18061806010803 66
    0x303d800541080c880300040e03500130301c11209100ca034000b49212010104550040c003100156020585136100c90a0010313988240a245c02c880303010081c0b47d0301c03c68003001080780d42c6480c0001e52000270f6400c103000c541c0507a50003003400c0e07034029988003001c95681d40c02c211030800b0034800901c111052110145004d000303e550700120f4022940c0b072043c10146141501500d5990fa40a88002684500c400c0349901c00301c3c2000e00102101035170302c9054844180040c600308140e404492054407107400300610080742500d1030180f0090401d00302c0f0446020403c1d4102074101003500341da440c11000c004241c00c58502c0c4001c003031080d41c0d203c048282050200500003807403040103803114180c1d80d1400041150394a502203150240146c51031551441c0380090005002981030006a002140b0308002d505444000b0015501c160407281c1c0c021607003000d8428000c581a05d02c203107400070083c03140e0f1411480050002400e001068443c0d00088008aa02c0c950b6240140417007801020454040c3d81800211b042d2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 590239163 1250 590237913 590237969
    0x604060909051203060a030f08120702060405030708070807080304060f06060f0801050409030e1305090105011a0a0e130f1b0201020702031b0a090507050c0c0f0102030412060902060a0513 82
    0x40d020740c403c0c0101c0019201e40340d03060024001c5800c059201c1c1080e006007400b000e190b0010318020300e101c00300800195604d00008546c3d0295038440025440c0c906070742c6808600d81c009181c1120403910800407880401d180c00c02842c041c0340601030000d503400d1445040741c02c65046a00000611050f174200c12100ca8100c4640d604541007a180480c80460078a07040340c0045032110f80310707404a0b9050120302c0d22502d9500c9103208a0070007000300103a9803035120310b00c400754980c0303000b00c00541d01301320354250288514a2282401005441c0da00784880c0c09a02c0c00585c0e441c2200f0340d21080c1d07122260603d00c0c2c0690001c1e008055280021443d12825801280d01c07059a080076282440050301c0108072500c804110a0082c848494100080d00302000000c0082c1e000c0700241000b44682e42e8030080710300e05001043d0180034140c008501e403d28001c1c5507490150384100030307124560703100408400350b201c440050040702002c2d03030380c150f60f2038a10072445940341e115045482250802c0401e100c107880ca100c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 590240413 1250 590239163 590239183
    0x1a01080c0d1e0903090311010e0d030f0908072c040506062101060e060f0901150c0204290112020304051b06390c0a050d08040b070b060406090905 64
    0x84085103031181070100c8100c80c4901c4480c890b0701c0d840c048201040c9507000000600780c901c91501c980c241c01d030b0301c40115401c00100c5110342d40704100e01c9480c40041c1c01144550451101c0d0304000da0b40079510f80b2001c1c1000000c0c1c0c880b0b007510390001c40e501d0100080300d080301000d40c0c0d5803460300354904198903215594200141194000c2021a0f401d811441c0141e2240c0f103da4800f80091040b5602c51040d049100c00999041e8040c0ba0b010750441014507103800310a041e54140c001e5a007440d40c0d17034101180d05001028050341c1043e500d0000078030046006600100e10018482029001c41044c00010503903586140c821003c00d10500a1000046d40841d48a201207000300760100c004030380c200094018815500024044e000760700b1007a1000092000e0342c21035991b501c1c8030302000c100c42c4500d541c40e0030310000c50580c82042034000b8066441c01c1d130075a120740c42c003030710300305080c03645449000200f9484108241c4441b9604004c0294600d01400340c0350191454000c188078404180e9904c503074480d101a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 590241663 1250 590240413 590240437
    0x5120c0705030609030f0a0921020a0e13030813061514030f0304051e030d0206041103030a091502011b020a171c0902040e250e070f0f02120d1a01080c 66
    0x382c1c2c581034501c230307824a1000d460002e0b00d4031100500741c9106000210310103c00ca002c0e580c2044001201c440c0090384c01c3c03044007004d144005480003650304444132031005059000a001e101070200c08141c00d48a0340c90801e480c5072003049200c1c28013200f0f401d00c50454131010310a5100040782200140c2c0407007a035084860680300780b2100c458124460900c2030000070843d41505c10000100c28007a40000c8640c0142d018040c960b001c010484103164891050300c0c0840c0c040745040c1d00030002178120907120101d226081c400025103400058108050462020000c0c005a00282d80c8800744010105034050098014000610b4516000c0c24008031000c0c02242030b0865940711584000d5443d207400c0300c41e900101c2802d031110b03030006003190340f45044040806920603e04804c0452240c40e50908140500100d0300e90f84103031620384008942d404d0500d07891004501502003000704c5161540d014000c1034200c1c40300411079030003181001b99216000d00c403003810044c8140900141085810459050041d54 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 590242913 1250 590241663 590241667
    0xc120403020a230414060108010b0c0c09090a050109030809071508070807120204230d02010206220b040305090405091513021f2a11130905120c0705030609030f 70
    0x300c43c40b608200600c88801c0c3c2c2050070040da01d80e02d40268a54684a00800d88401e049a6200e03200d070354650080345e0030b00c00158003211404801d850000284c66011243c03608aa1f4420000da03901400e480401e9022404942c1c04028486401014089000544649901c07144003c4001d04024042800a015441840410300210300701c10300c0380340a5405074101c95801e541da15519008959200501484240d0070050035410788903c0c40c0049114032450740590080c040c5841e03c4030a4050030f80e801c15000c550056903e401000140041901c42c4164080e40b2401d841e21400818003040d20340c0180b55039187d0300a0030700141418200802550004c45c40f6244998a0341c242c40401c41d105907251140039000000c61101014540c001c0c0c11fa82c008090005d56256542c03035401011882621000083c04074008914051b05800c080705058003650b00741e8004984d46003180c0307805080c0080e114421103182000119452410410031010004040c160010000c61903d000d485489000340c0c06694020140 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 590244163 1250 590242913 590242949
    0x8011502030a2601060918020918070504081606141306050c0f01021b0c1030020313020a0f1202060d0b0604090e01050a0212040609140f01020c120403020a 68
    0x202030f11401c450001503402c041d61161030140084003107200d0301960307100c1c00140341c075540114000c2d105580c0c07000c0c061000c0007028080c01c4000c40c0c8020210010003a041c480020301e40c80800445640e450103803540c80d035043c10007400415844640440581d0900c0c1000484003210700e048180342215030a00d0550b4a906041c4c03045070402118058181d22580045400512100308007010f000c00b818003002c07200707250420300a010200e82c0380300d1920b0116000d50f828548005109554142b02d0000b81102c503402700c440d0340220100e8100341c841451002c0e2002c900702c02c5050880b4504050403100c40202002450130603400380b480300c8100e0090048a010800000790489508255020039000b40b40544954803803c032000145500800b02e00e0540c240740206004c681303d84211404038015249405644c0e940e070b1a000b0180064944c1114880406101c4410a001c01d000310034400c10381c400050b907107860145405d80350080040c0400c441c00010001000103035210b58030601241c42144000200ca00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 590245413 1250 590244163 590244197
    0x180f12030b060703031a030a080a0503130209010b130b090607060e01090c032604060804020f0a0306050106030213140603180a0f06090311070f053307020108011502030a 74
    0x1e03104505a00010080307404070406805400100c000f08120501c107010b4050344007050742c0c8124072480507040b641d04110107001184104c0085a0000c042c271204e00b002d2020f079010806c110002d90040c06203450100d80f00380c2c40000c4015032001007801d940c10074140300c110000124a4440d42c0c00003020344d0354566810320608070039000560384c685c11560200400755641404070001c41c80322103c48801201d80107d11240390100180c0b01518104e58902a99070b441e5424445034800e00d500ca280d0101c400f1900100180f0b09002e05c4c0d002c2c000366913001d42c0320345606c01e19502000d00340c0c00c01148001c01e8003000701a40c54a0b02520382c410030710341e0001e07502c01c0946940f9050010820000e00380090410b400f01c203000300b540043c2c02c4c05101e0341d542d02155500c504510349903003990280c1c002201c0100420003440c0b0b00802815004590742209501e40848040c2d00d441f031a040f010340e5908004013040d2401590b8101c0030711801000104440c880584410310300a46a10901c810501400321000404030212 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 590246663 1250 590245413 590245421
    0x807050a12060602151e0106050c0109061104080712080906092209020108010602010e06071d030604060603110105070c1802070b0a0e01150e0f1522180f1203 69
    0x20750500301007080320b4403210000d4460002d070b042101210424004158200015007a07124221281c044258099007081000c442640c407511240c103403592612070b1400841c400b4411190754070b1240c00b00583d035174070301142103041400c40d50060382684002c1c01082c012440010440d03840980450701550b45583c01e100041016181558844c0805d0300c400da4118024082c1d4085a43c56000741c07907001132a82e90b40000c0742600e81608282d0526080000410704c114090404030a43d00400310b103030b6400340500400b0a24086044030140c0d8400d840c1c64040003440904040812668402c2c6403141c40c248040e03c1c4ea0f06100101c1c825107121031540c10312290f50a03c0d40c1c4c16550310591140b0080e00ca030030314000380c4001c0c015590369203009510f0420440f0071403101803103031400c658000b0280041c0b41d0301c040c0074200b200ca0080415030314103603c8400110503901d031400c0d000e40303054481548501805011310f060407100b5411050860040c01601392001c14118020a880d02c1d500408103900c241700018210050 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 590247913 1250 590246663 590246687
    0xb0f0103031101061421030c01020a1806170408160b1b090904080c0c150309010e012c011b02070617130816020a081e240702030408160504050601030c0807050a 70
    0x85e00011902d0303123240c2c0301900141601542d07075440f0755800c100d480c4012240720302c42c450480401c031607040c010071408281122a40c030a0003a04024104042d0480c407241055441d4822950250000d04001403c4a0a4410720034420000096814070105202050407144050400f0303020a20124480d0399681040080c42c050707043c094030212400400c179204420b00d40061ba48169254281442d0a4903103005125032558608610080714040c0910090f264040700c1180030306410f0f540340e100703043c040340030700c4c5c0344840410895004003c11890040001c1010a121840c0e10001c1d91010511800d180070311007100a0b26007240041d40e48038800c500030702c0c0e0900c50b5030000350000d210410009260001080031035007403800c003040403d0151303500c00c0140c071203140840c03040101e1400c001c9022403091013020664480c25600444e4685501c85174036901d4044004010580007120b40010712107414140501e68100d00c1c00e0078148000385003401e0280c41000001d102c0c500700b00f0041241400349103e4146d0040c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 590249163 1250 590247913 590247979
    0x60501170f0c03091204091b032d0905010504050a051b010e01141b0706030c0e0d06180602070c091a01080c0c1e01020d0c051309050406090b0f01030311010614 70
    0x91541c7d2449102e02170500003525400d10000c40084441c814004e01484042c610b0440030281080359900501120001d00241e042c50f465440b040ca40001d04248181030050f030203503004280c40200e9281007850007201080f031483e41c1c45510602e81550f40c11070404840c400003401c101644100c07d1b030fc00c6141d4001e11144070440084e2000c1ea0122541c042040c4040d946d4a51b01130103800c402c5001034070b500f00b02e60200e68100802401c01c0010680541c40140107840284440044075102e407500001c0c0c0e006140141c50003501540b0401019130540308680c00208803424034040e26030340300d001804681000303000d44103188000406140d009404d00c1444400d0040da004a02c61051002d075141c000c0d04448607101c5480e00d0000b82c6145180620f055812480706070040c03004060030120100c02800001d44100c031402c1d202c25029000480c461040762040007200c00d014001d62460400a00e1200c0000e00c1400f04d07490800180702301d0408001c007038000350007902c04560034512000c04d040c00348440c0a00307110b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 590250413 1250 590249163 590249167
    0x30919030b0703053d1d06040218130b0f040e0d030905190b19020f0d0c03140f090c01110307140304080105100806150609010c03030f050a060501170f0c030912 70
    0x3908017410806006000c03204540e00300281d494000c1c0c075660406010f0400c8441003070303d000440ca40f6064004100c0c0000a940a200032210744d0f0104d5070800810801901c60b03030712a595404941800342d0f07503041040d001c41341803001075210410360f9120214000000c0c00c00d629203c03c441030100c00c02900410201c0701400605581d02400c00d4245021f096500c2c03903040ca82c0e2250119100b582d4001c0d601c40c0003c801100e0315004812150400034854244001d0038191582c0d0065284a42c802ca05403150780031b408911414071380320100034240348401c150103044c4086c80700407421001c00082514002079101000308440e040310f1141354550b02450780550b003190300713201c208803502c0d81c80c9444204035800c14044038640d8071900010803d18101d03810040e0040c1c410b1000000940c8170780070b40380c0d0050090800240e0700c3c0d58512a0350944004689280005486850411065074040e060305088450500300400e6810011107903c0c081a020300512000d82d0b002c004204d4001741801021051110b90081eaa = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 590251663 1250 590250413 590250481
    0x13030605041a07110c0901050a2706090f14010e151219020108090c0108070509131a030d0305040f06050429070801170d110109050a05030919030b070305 67
    0xe02c07001d044c0409410742d00603656058030360706103070492130705890005154010003030405032803a601d051045858101202c0c810113540c1100d08502c2954043c0c00640c0002c00c038012619018000e840341c07240383c0300707031f44000b6401040400400d05c5181c0c3c1103400d50842c544104031039000500d43c0f02070030347da0800c54090100d50100a500c100710340c9410600c00c1c0c0301c241d199580ea8920a4032070110000213130114005400044040344500010084d1400c001d155419040c280c0c4c017150300b1901142c00c0c040c012891020400e083d032600700401c0c0c00c820b685240500103450660740b1104800126540280901d031110003160401c05180c01c41e00004454044802540020b500c90f4010404159069030107e4203d000220b5041c501c10159503e140660b0300420341592a803404403511421940840855540d6100c0d80d000074038288081d003001d60180c001583c50302d8003502045801016208201c0900784000420030000d150540c84e2940500107080001d0140d90744540c44039590740c0458900c5a22002030b40c00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 590252913 1250 590251663 590251667
    0x3020a1214091e030a0813230c0a06140d02071502030106031b020c1e0d03020c0406050a0501080a0510030b0c18030303060d02191e15020313030605041a07 68
    0x2442c07003480940101d40c0341e0301a0b4280ca2681e04010312038950b040d0400c11044031030500600c400c9030010b540203940440c2c0201521500b404640900104181d8510448021f2900340104291103040e14210303030a0707210ba8900400076086200500c4540008900030030718030222001641503604a980240c0d41064044105201c03a0080d802405444003191801044c0480001c2044100f41a8500d640042840c10740d00e6003080121040d5040080c2d1504106081d08400c1e02c0c0c0111084000f17200b0340040900d160444104801d84100707801041c0910341c104420040c503a4019549504000e0360f00000441d511014a5501c0d08046a0030250028005405100010f98000020800c0c40c4203042202031017644007040607120b1100341c84d065409035900f0040c0000d441c0880194860303e0705010980d11541d52044141340c41d030052007030003034045061b4004100c2c2850008004400110920196162080400f000304401c0341a00020b03050303a82e0340b4009001c0004c0c3d850603200c0484200100510340c5442100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 590254163 1250 590252913 590252951
    0x40615110a0c090e0a0203030c0102120115090308031015091e050a17160f050901060903030f050f0d060e01140910351c050310030303020a12 62
    0x10500048400c8158408038101280070380400368401444080c1502e0309400001400c82403500c086640540041c201c0141e8007040105011454200051780311260207107911000081607200031050740c3d001d00c0b103499160f40404610240d942c8060b0550700d03511801400e800d800b02c80d402165040c1462411340c0701d0180c10030140d00840f400c0a42d11080c3c2d0205003d500d003584400c2c8283c81d0425800320049c08031070b40505059071a07680e0746c000c41e08801540c2c840f200211083d2b510042e01150603010600041c10004c01c410b000d0306841c28044002499a0b40003004041041206820048003140302d2142d80b0104003202c8000f4030300c0809225840d01c031800c88086800030300c14440030000e502110002410300740c025512070711542c10200100d903e86091a411410005d0526002d4022500d40c80e01910180000300122501e4a00824142c421a2407007005020042d4407542806802d01c2004014072001201a0075a98589405600c441400070150385500410304009121810505002c950003589c40d1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 590255413 1250 590254163 590254199
    0x2120d06030c05040209310510031101021207170403050a032007080303010b0a03020f07051b0409050606010f09080106060e101b3003050402030c030607090905090c0406 74
    0x44041a15940d400c1084220b200b114012a0030070b00d048500c020300e0130040552494018400012515440f0300040307c0100e5a00325941c545030715814400340140126194216200003080c0010605000480300d8584103000e95100100311003480f440325038a00d0001d80a9030001c40c0e02104486055840d45800b80c0a90307003003040e41c280071505a5400a0844001401c00f00711200480554038690a005d0044c070554401e40c042c0c0181602000020581807181c002000002d0103078014001c000301060300c03500c06902038051144a00d003810190001705070081940c2d500041c003400d2509501c1141101a07604441c240d1052045518214001900315040411000407541c125502c00801c1049482039540401840064402014030200c00001410240c0490302000310381004107000d061000c007407150320011448000019881d1802d200031800d0070040c009102c00200d018018a16101c5402840418140314801800d9151b10201e4100c0c4418403440c80352a4000c3d10034803503540c03213942000d40ea45202e0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 590256663 1250 590255413 590255423
    0xc010207050c09010b180406170616170610030f0f0c081303020616110303040804091b02100c05041d160801080c010c02120703110f0105091f02120d0603 67
    0x20403400d40701c0c903003000d030f40d4160744010600c582444c00e0325090440751074131100030710b4206503501030200e62030019407080b0346040060300c01001d10f803400b1502e002d0700fa1614484142404014075100160900c61600c80f903004000b5900307484041303a91070040b000f500745441c41c0c0030060b00d0814244203150103500405450394040e01c03901c500e03884298682440d200c58240c061b006030051400b207009030220510130120382c80c0034a003159882030220b030f90b01d065a106aa048400800000302080030304202d0181001c494603c010381c00d0a0018040d0103501c07400301c04e603410045552500301512140c02002568041d000301c0c2020040d090700b102c400d804062042c1c0d9000307100044240322001d09445000350358141da0b110350240c21210746640054804100d0300c0c90490340042c0d84002c0f08400031040281da00214050760800c1d9a03000d0060038810308502e01050303d41080403c00402d4500c0d16a000c00d490103808035092a10b81180e070f0382d4100e0500319100010310a90300006059801c4168a0708004143c0e8020 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 590257913 1250 590256663 590256673
    0x3030a06061d010f02031e0307030506030c0a030308060a0b0c07091811190e0a0504140d020a020d05070e0c0702040f18230102040906080c010801180c02010b04020c01020705 76
    0x40e820540d4900800b503081c028403007200d45489119445146460902211801100d04007410103007089010104410381200710000801042150f5a05004042c1c000c20150054004415414042002c0d0f10180c017000c0c0a00a101c004a1055141c18041c1d2004000300d0f43c580d0380300d0725401e200e02e85a55040c400e0703101e610b081c200c401001009a0006054940e8000200302d500c0440100f0b0000c1c11b10520322401c8541100302000079580000c4aa0074071517504640000b07640d18041c6080d98014805110b041441d612040d100907c0d0b0740c00160300014160100c50100f540035042c5840c5181c0282900700c246c282c5000003c2c4040103580381c004d400054400c40b802d02104148400c0c103401c603042850321b00c548100200704000421150004c01c491003138601d00e1160800c0400c3c09a80c203a80c448da1000c100304e6910601001405010302040b5240c11003442d01944651424002510b8a8a1841580c3d5125564001d4624442c000d5102c14400000074009646030030500200600039008900203a03054092 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 590259163 1250 590257913 590257919
    0x2040509060103140a0c050f03090a0308100b0a0e04021e070b0c191d030f030c10111c1503140c09090d030e01060f030602070309090b130b0310050903030a06 69
    0x90060444d480600f550010556803105811406084180c2241c0c1c24440304211130b130101041180154818106100200166000c1c1d14002f0502c4d80010300f2a0303074480c200ea40070301200b403c500484544076524503040036101c2160000900030710581c001c1d07510b10f90032a40b0022503004580e000c2c141f182e00401304100b02d81c0d0f5642c1001c03c00c2c4145043c2d50150740c180f4000d8a80d56005107407014100000241c0c00130103042d01c0010030314011813445c8035552607002007a5030f40701000030032958a04c4044d07448280002120300501c95400e008803140c407102d0a1a800302c160301130300d49500511170003900c010308080715a40c0b410f1203081d1b01d415049014141c010460b02003c02e00b400f5031000d009240b0302c0c0042c6000d00001004a0081c6198490300a00d952120000580884d4503400200a103001c1c460042e5541e0103458094501445548215050b50a04415004991742c1c888000c1d03031440703411030110380234200e40006400d20034003151108610b4640401c1c040c000c85c000015510540070a2030030020380f51 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 590260413 1250 590259163 590259167
    0x7090503070609050612040317040305043003050a050c0102041806080a030903110a12081812061b2701020c030c13020708070816050c1807030b0102030418020405090601 74
    0xc01c2c021390350000e50070080c86030540404003001d0b41c007038060310b08080210800c0f07142c0b50b40c040040d18103030001a00331400b4401390311480041064000c41d0440705e282000c140006c6122a2011800a0b00340200402d00a60b80340c081c1080320040b6040c90000c40d521074450170b180e00440c8004030b0449642c2d182071400700e00301000150180d41540c0540314882064034540c1c54000d50b0300800d402580003c54004001180f4100840303200c2090f10458109440d0581e80448078a0840c0081090344503205075000d8061500e4041241500017800c0c6003000541104a1000f10280c030400c0845651201d206140fa003284c040116080c00d0340c00300b60300741c0d030b03104081e9404c0643d58a440d041c0e065010004204200c511901c69004000e00c91142412a05001c0c0f15201d400c1d1540160a211414030105110700007088814080302d46a244212100c800d80c81a8400440c848800240310005059070f410740030865138000c2080e20010100d176504410361444503484c850294010f031245e01d01076021200070070b05641c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 590261663 1250 590260413 590260427
    0x30408160302010f02041202040b0a05091816080f1501150e0f0312030a0b0604030807200a06030903020c0d110105031f030b092109040c1205070905030706 68
    0x5400000140c24541200540d980c0504118012001d641d69503802c404445150700203000205955541d41100c50000c1c01070005032001c940050388188518030f000d001641e10b0107001908081000d01d0200304203140c142d014546180661804102103184100140c0303600700060a4603005001c0c002e450341c49500ba9180b0507604801c1c000d1009500500c0c0442890358421301d0440781d000c80050820000080c3c240200c0c0c1441c01c001c0c40300551210010030499a2642c0d0f0040494602064620514103032541c1c4480c1554020742030000c2110320b0180c1d2040c1e150412904601000358010b00160381180d440301c0240c002e140c20741d0210003601840c0c040c100f10b46404038120901c7c40d000440001403000c075000440c3c181c1e10092100c81d000c0c3c0b0040020030003451000d20140954031512003080107080c2011000d2a1054a80f8200b9071a001940c2024a41c13102e0310039500305400a84001c149003820b4401641e40b04c00030000c1307100303181c90b280c00c01007030644c05500c0d2003c56600703034142c404140c2c07500c1d411030314a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 590262913 1250 590261663 590261671
    0xf150504020a0503070507151109011803051f11030108010219020a1502090619110f01050f0703110c06040303021e031009050603030d0207080d0b0a0e0f070c082712071a120a090308010b03 82
    0x5070800100e140190b8511504c7c3d50980e8860781c2d0004510340e014300030607150b0300280c0203060703070743c4d80421001d8604030000f003650281000c5000a000d840483d5807441d0441c65400562451140c0100e0140c149440300000c1e61010001115130180c1030280d00e0000303100d1fa8088480003a140706850002044e110b043c0300300d85c02200c10300c0ca07141c0a5503401c8815005801030b45000410b2071820440070442c1002842414001c3d80720340e901583d6242d41c3e42c0030b19942003102803071250030441001408403500c80200b0542c1100c05003030700450f00359150b600103802c60003012b002c8207203503000003481070401100c0c82c01801d41050b000d5007080505040e00a003c0740c0801c50045210b01f443d440003080b001200c01244030392100e800d1801800d0a12103580d0520760341c10038152501440701c00642032108074240e926030350f4090401d6a0101c002c00424188907034500082c42400b52241220020078800e010300000c407034039986603258140d0b41303080c54111300000f015110030070750000b0f0b00302001003541c0d40c5140440f401 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 590264163 1250 590262913 590262923
    0x70f1d0108150303071703010e0f13110a0b0703030b09012103080a060b0d0509010c05030615130308120a0b0609090412120f150504020a0503070507151109011803 71
    0x40d0342e07600595102240070269140e05210a01c205400186441840030303918010003405500c075450200e00562240001e0890414010064100540300c1c010042d654211a0414003004008080e1030214441055942103c1e1500074009543c03c14141c2542285058000c25102600700f60382c1c074000c208005040e002e852000061480d03014000ca44144d06840d003010030350800150b520f0f540c68000703002d64484039682c0d103030310b84400c01c00821220078401e2000308035031030521615514001001451403801d80d00c02c0010a0004030f1050b052100c80c504c15000346030300c0001c0d1650388101f42510a0202d800700c03041d80300c05003841c00300100c0c0d0800605582c80c02c000034141d00c0c41078440b940c03403003110341041c0d15a004002c500c81d00c210301c21003070380a000f0640400c22000a0303d49429502c040c079008058000c0360240d030040004641e265800b5003141c3c0d0005043c6459603d07851103292140340040c0c0310503421a140d00300684904201d48010040580d207a091321902200840c2c01c0c0694174180c1c0038400030342 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 590265413 1250 590264163 590264177
    0x13020411340209070c0c150e0301050603060106021e100203100e010b07020f0915100f0221040605130f0810060509041203111c1b180504090218070f1d01 67
    0x100d01400b5170380b1600e1884c41000c03913080d02c603140c3c0d5031082d074001c41c1100c400c00611a6000039026040a103d600c3d0000c20580207400340c0d41c100344010790398544c0e004c1c1d062130300560b14201040b09901841000b414864120f4203554070700f800d0207000c501c00428000d5031581e00d202400042c0c1c0d40c0800b03003100c0205901030040800315000004101c14650000c0c0014003028440342030a0460380d80f4041e4031003d086540f5038030340303400001400070b203890b0b03008400c00c00c0c41501e0340743c3e10000000071080d00c084424502d015950b50700c0459241c940c0440b03e070b1003040c0300034a4401c041850140441c643d104600d60800070000c40b135440040141c51041640c0c0074000004100800503c58426000790300e81000381d60455143c0340300050000e00103a01d005041c15100c2ea10700491059521402440e0708071a50382c40c20082d10780035000400007141251103820b1080e9640d503545400c64503031040c0810f0406948030204441d20380544041d0018200c2042000001d02a4052446903040f40118444983c810782d0303402 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 590266663 1250 590265413 590265421
    0x6040c1511060c0a0903050d0c050105060f011202030714040905070e040225050102090604091505030f1504050c060c060610180b0711030a0c0306050603070e13020411340209 76
    0x5101903001101c0c0b5020800c10721700210105e0410010303100c920b9010b03a02d584207200c0f581000303800c444001c0c101030312035240c001219089031b0344908030800301e0707c41e082d0050780c1c2c3e10707203038015501d130281400d10f1403840c04045030004001240e0751003035101e08440c4c1c491261038014481004101c0c460841c0d1050032070304414a8200b005c0001c022050854400e0000610b454100c00c0043c406400c0390740b142003000e44802c44500e4548007600c510006160035401064035600142546440e103c010184050907500840000c00303000b13040082983c20340780a4807031951411100780c0c807601c40b40100c400a010700c032503801500c000f51060054414040e075901e103000000f070500c00055095030214200343c5c0c0c50815030002020942e0b00340880078130b0f10b10841003107026a1844c6002c0080c2c0b1030040800e80700f074110840c01c00064115043c125031040003800141c02240c11803001034000e25003030f605220402c8010804a0250800524030144913815040a0b114080300b980003060044000c07030001e4000d60084045 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 590267913 1250 590266663 590266681
    0x807110a1a09070f08011d03040f031205070b1006170c2a0706030905070e011401050705030d0c02210c0d080612030d021c05060315060607020306040c151106 69
    0xda000b500e040141c5a003a5520306150140f80d1040d008150785965601d000d80401c8021010141c4082c104806541490f10f8004407240f40c40e842d10028052001400c0c110f07607050300c0f40040354071307d42d03020503a403003541401e165a44910040303024803404644803540c0300c000c900103560014401c003000c1da17845203418407031500703074034002c2d42c05140d580c1c50a507010032142001d07401c1c010f001c044c0c0000d55002814804c3c40c1000d918181040d4031007421452040010f01c41c0702d85288084014000a080881d80e440503490708030f19512848003a41025441c015014044171750105d05200b0030f15005124034038103805030404c203a040c483d00582c01c0180c1d0000e020400c070320340142c558991045000380b40c0542e6040c45011603095038000c8031a1044640c0c001050100060450145c800490a5120030840740c40c01d040800d039101501800b02481d803008070000754642d9141421105250703030180503160309051a140054032008180952a840e8900e03d94040d9044c3c8150400e80c0c40099031030040441d0345441c294 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 590269163 1250 590267913 590267963
    0x17070209060414070e0109210501060501050a0c02042316030b03010e0703061505030a06020d0c0516030804080918010320150c0723030106061112130e070807110a 71
    0x80d9411f1080e80c0c00009011240a0888004d4410303900300c20040901b0361901900b1580c1036000903041c0700c0144850b04980742d002900301411a4140c40c00101315010719210340c261509003400c088480c141030200059543c540c01100c04011168a003400f900d5020b40816080e1809802e00e645641c0c030007081000841c43ca60450348030001c0b030f0840c0c07030100c68a03940424148154103c0c265141600001d014019441c584a4541030640900e441c508080c1007928840e440c1a10480c00303810408a000820140200502103e004441c0109580c1c03094501c00d220300e55030b0f4401d00c03042d9465202c081d40440003280381d102810072a40020424072500e079900180d07910390b821819085600740315030784003c10380c80103070b00c10001c5129001c46021401003101c0704050a466032500b0a10401c01550300c206284000041c0c46c04045150149658840c02c080181c2c502d411102c1d84500c040340b075001c05101900c1d400240042c064113040da102c1801c41904442d590f9100101e4070300400044080d40721440709200c0000c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 590270413 1250 590269163 590269187
    0xc090405060f0612040302070602060402061b2d1b0603240405010e04110102010c0806010c0807020303040b12010e011203030c1e02160e011802090d1707020906041407 73
    0xc02e030710001d0001c0b00403440030380140c130900d011803d6450902040c180c0400c4030340d00030140e40c0f006058031300d0240d02250b114040d2280360401c08002112010402c2d40500038844032a900303240c48000c2a503248160800031070310a202c8055801100c0c102d5504032403180026420010280c03481e4a55140d03032004c4510440410402000d134011140901c10341d9960703000b03050007030088403040010340c01d1904141c00e03034000861f01e10f41903a2408031a616120b4101510a5008a0908103c02c1d0170001c1d007403802c424030030110000c4d450f0000280c04078a040031705020b006004104446450542c0c1c076200c23283c0500c1400e000d101d2000030509003101c0003034400c0c0c10600c5040708514180740710a42d0411262440c2c942000d058016800c90005942e0405610421100816034120756404551410241c8014001200c5454614075000501c44906454400d00041e030f09030301c440d0042c0e02400030308060030039070072540d0200e1284141802007103213403901d0700030110a21141c00c100c09481e2203210094506402d001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 590271663 1250 590270413 590270419
    0x30b062a030d090b0403030518060106030e0307020607060608060108030a0c1205160b0123010813080c060c07060f0204083d0b0a09090302060c1813090512030c09040506 74
    0x20038911409441c3c01600000c1d41314030900c2859050a14014080d900010b018400112505aa988501c140026800d044500c1405c5c00501d082c54805101d080d4814048007a4000c0c000241c42c004014550b40070780300f1200c5241c10b45e20b0b5070b600c0700d50031a1644160303800580040d8101415101042601c0d2800c20302244604001e4940100c1c0759409041080781032060760440b400c040108010940c1c2e40c0400c4003854000703480c0804104980001e801c641010784044c26135030001101004100150044440d20800170003200c10308d10b4080301c0c4035699406603004540700c5047c410f88480d410954002da5007600d070b41c0c8003e046000e171b6140e904000c45044c0c8009441c62621004800c0042900c0300810705120b00003100030421b4000d02e030a01040d40856403080303403114075002d0030308082907003ca03410350451100e00381c19684400143c500384803040f140c14111b40c4680d1200080b041610305900c5120880e1081060310701468100034018041d0000315002d25107a00d00700301c0c1e080f0516081e40181c0d4002001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 590272913 1250 590271663 590271667
    0x60e060d080f09220f05011223070312020c0303130504020a020a08040b0a030b03120712030e0d090510170c0a020a08070309170a02011b02030109020d05030a030b062a03 74
    0x90a02841d941907000f2000115000800030784e43e40c06030000000d01c1070300a100c203515007000b20950001862026001c4400a09203450800c0c024006a001c2d400c034004440700f00b0307142e05214440e5118100c000e0054811245030440c10f04001c41a2070860751041e4100903510300c0c00090001070350148140800b14010284c261000400900140003c0d01044c0200c03510b85820000160460b05079080d20761095221119584090450100b1075008036030000343d03250710241c009819005005400074203100d50141c183e100300100c2d80404880d0440f00f04456030541000440001c0d00c1c45040c486121100d803490f04001128540d1510051580d400c9510403140718a0454941005035005002c2c02c400244880408114407c1c4030b2000c1c0110480280103082c030200d251340041c005e042c4080f214004030700880344502c11741d41c4c00c2d44880745e0b07031703070082c1004070110b8680c900162640d10039003099012134034003600150181403001c2544c600a0b070740c0e8580703036140c02c0d155150300171040c0402c024941d5202c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 590274163 1250 590272913 590272927
    0x6010e0f0f042d03020f010e070308030a09021507030206190e120f13080c01020115180527060f01060e030309040921030929060904110d0b040501060e060d080f 70
    0x4001d1916550003640030b011b0a00b124200142502d0039080400d80c20f5100e1281400031a02c14000c503900400840b4001420000070f00c08285612080c1d8100840d0410226140090503000b040b15031203401441044401107924581400880e590b0003240b031001e511240880d2a0200b0000003000001d070540049402d01501c28200f48800f415608824819044a1506015560240500c0c0382c9074003000f10050015092482c400603d80c0000e04907500c0070389883c0840c803000c420052404401c10255414440c00c010940c020f942c901094515003281c607038030f000000383e95200c0d8a04420010009003e5071400d400c000c01c21010f000381110545840c0024104900c0c0c03401d103124110443c0c1e5180d02c0208107962203091148468800504042180e10103412520382c2c00420480e060f0b0106044038140c60700e80b65410192803041005580c1d035000705010746527000340400300d4509440780344910000c0c881caa444050400030617400356140c80d0071008041c01c800004544402400784052510686810162 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 590275413 1250 590274163 590274233
    0x7031d030a0c03210f0509130c1706040b180a240e011a0304062310030c080d0203030705181005030a1a010f0f09030b0906010e0f0f04 59
    0x1070041c03070464999040400401c2004090007070304802e00065200382c00b1114440501402d50700a07549243c0400a00098641059071090410310b0003800c007100802c0840b5628802038080108003907101b001e141441c0000d481c81c03410340a400c1c805000a401c80e0041c800440e0001084813025050810150f20781e5030b000b00d590038201403141f40241b004c0d58020000e140489140d880c0006800c40c20034a040142e000d40711456480c01c4030380059101d50009020840c40324100c448542111182c4220050741e4203104081d0100c0250344180e0f4040c2611003a003681c1d8005285d581c0035650301e50009030704213100140d000c1d806207028101b121241703246040414000000548594649241d12010820200500007441514894000c00c1c03400800d4514022542c4400a040f15404a00031000c2041c071800801582d40b080481e0002503602c140903158a062400c0002c0e00c84009000b1049400504000204294855844240500142800a0440d031030740c0e140c0083e0340031146400e66850319164a2130180c12 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 590276663 1250 590275413 590275423
    0x10221090402070b011a1206010c08070501050a0e0f03040f170708030c100f0c02070306020d0609060f0305060606030c041e05030f0c0910030510021b03340807031d03 73
    0x648101c280c0c500640c1800840f14900c0ba42e1b601500d4011030601404110015540302d5135048002400e00903118000b5140602c154466040300600304e500b8142400b0030a01e154018903d01031035202603403602d080c1c410740b040d42da016601c0b8188914880040070803100074651100d026001c2001c0c10382d29240d85485903985190700c4282d0301d0180364044c084a0361a420648565a04018002d0041c0b00040003000004c0d954115400f01400541d40012680c841041d5940004000c01c1d200a06000c16903990304100210300982c801601e070b900950001580ba86810000c581c406d0400241c250b041504007116042204d40f94141c1c0c020440081c2030100702c984e8200140d105042c4190020007401628105000040320007801c01d1030075082003807040c80007400205c1c01c03d210105071580142c445040700c80c2442c1c2e40404090740b90580c000080c4400048081034500a40c40505948118820101c3c8080c1c0300503501180c400341c84007009120000029200d46250310410204002c0001003400450000e801d007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 590277913 1250 590276663 590276677
    0x9080d050a11070b0a05011401080619080d02060405010507080c07150b0405010e0a0e0c030c06030a0b0a0f0303141e07030201060504020d1d2b020703050601180509010605010221090402 81
    0x4411084200405c132903550151901422080c04020f000c0c444442c00680441e4001d0f1905228640800e1800c0c22144400d500ea4000c0200000720303001c544c64048081e4030b818003a1000c5e84c0650800c000142054060400c4502580304120041e150800c0c80d1102c030f003070201c08560201e01d5038441c03010192079901c42c09094060004041e0340c22450403c09040c1c0b046a80c0050340c1c0301143c020200521280d0b07008284500480d4080c2c60240e034940d600c417890f80050145898896200d0b040600c041010039020321203200b07680c4203440f04643c049681c1b150501e0350091030840c0c0c04144841400f0055080008047c0c604140b2a000106001343c940000900380e81165101042890b500d522140c001d211031485c000000c10300c1d802805080d161003807030200e0303003250406a0440090b00c060781074110744200000002103400c14140c03220365071213501102620412240840c03a6504040c0800c1102606115880c11504140c00802030b264040403601c441e1440e4030340c01f550715642806191610746480c0020081 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 590279163 1250 590277913 590277923
    0x150403050a02033a050709051c020402070b04030908011505060f120c090f2209021305040602030411032406010201020c01020c03040303080f040c0e0a0b030307030c1509080d050a1107 80
    0x122603100020114004d580902414415007000305000025401420308000d4071000e0710351141121144040e891500380d5028001c0d040b9100082840c2400b003000d5090340114440c0c2d035000030a6555011507800c3c0c41140102c2a80d4200e1034a04103c0b41c5070040c0180751900c01604054104201d008402004090071102c50008481c0010803800b07a00d41040c4198500c1c0c2e089440c4485d61640f0b081c4100c80408c6104000803030ba5480c5a103009550311a0400c48000d4912402800f20345414503001000e0341081d241143c0c3d00380240780700503ca280101d444608210000c2007020f10741c016200707d02c20242d0152803d030555508024030000e84500b030004103021100300703000307568031031552070300420b9a48001d001025019205081c03000080590110303108a0340d84180c00c24458990b14820030052080502c0ca660510000031850100350708041221001809040051a1410590200429502c50040c001c3c411007040200c0101c0e900b55038002900004d692800085665a00705600f042d58044501620 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 590280413 1250 590279163 590279227
    0xc110f0d03062112021504030504180513020906040e0a0c1502060c07110411040914091b04091b0611070504020403020a091d010f020901020f150403050a0203 69
    0x14000d5014000d00c4000d0062089002c514103501011642c000a96070380201032481c42405064060305c20402c0301c408061110300c4501600f018600a030007503000344600d103c401c52004442c4000300140c0700710340c40f030308240c0e5501010216942c20409106001011103612640d02d148061070701400700115001e444c82810a41001030802c020909030111440c00041150700030300c20415861440401d80c3c600035805005221500d5141d00020301506403000701e01c0c0201c130301280000701444241c2080790424100f072162400c80d1600c005164a130603001420700204030304c07946403060382d082640c014903081c1d0040084450340300780280c4940e00c00d8225030101c0300044030481d01224250003806450000c2c4012602189042d14503030106095011900c00c12005a6640c0c4880c100d42d0503084111000c4205000200513010032102c0400c001d410640c58140140b01e0310000c60340301400099814402c0d00841050320240d5600c3d0f8088405030300502400d4110301060005210342403148482e5002c148030401500 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 590281663 1250 590280413 590280433
    0xe0702010e0105060a030c0312210209101d1002010f0c02030901020d0512190915020408010b0603010305070b0c15040c03120c1709010509060f0a0806030604150c110f 73
    0x80d094801c084e1215110b01200070b42040010004844902125440082c3c8948129280c1065030903400c044240000301c20300c50506140c1e18040d43c010070200c4821243e64041c002020304c122950000748031114041400711018035006d203042e0003416901043d620004c58103065049689058444c2c1402c10341c00350f400482c0c908901d40e014040c10204507800d1401d00e050113241e015100766102c01901c84590720a00d943c0130014800e507074100345202c80d04a0b580f06058550321702403100a40c0903100c1c1d50829460400341605d00d03d00355080b6412250014001c2c40350904000036900154020017840181d84074414168445a20504095104500032120040000d1550500450240b040140d560801280e4415800041c280700354004803814410801901ca40d44100181d81c1c61050140c140e80c0a000441c5404071a5010320042071200b056075208503c1c0d40f90b46051640ea0300c01607400a10014001d000d80160b804258001f100800461400041c810860a07805080840081400609420a484103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 590282913 1250 590281663 590281691
    0x21010906090506310201200615040b01201e060906010506030c1803190501020301170c061804020409020d0209040c1805012d0f0f0309030c060f060e070201 68
    0x20a134008021345018004070009181c6010450144408522003c04098410107591050306c2d1101402c0c2c00e00011403200303400420003070380d5140459184c90941200c80c911900c6060034010081c0c00d420613103449a54015011011202c010380a11042a6200b4405603000810950308003004e158003031030103010681801c0320103e081c014140c2003036000341001c1041c048031032218011900240010702108410804280c00203040090340051342c1007540340095080c0c00d110040d40218102d501c2142088940e101c2c0f00400781c0c445240e062460392150b4140444925031024985c210042c0c00020030051410b522240d411040703812182c003c4540550118005c001d07401c1a00c1030711404509802e00100407040782900d001045258000c2c10f0400401e00b842072100c0c5071014041241042c10800083c07400d2001f00004c0c0003840c3c40b10280001799005405204860192044010068041d0341d902004000c0e612920701a080e445003400c645903803048009000441964038500414565001064034001c003004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 590284163 1250 590282913 590282923
    0xf1a0c0a03060905040b1f030501110c06011a1b010f0f020405040b0d02090c0702030a0606060f02060703021e03040f0b010312260a09020105041a030406060602031602210109060905 79
    0x318440384c0c40c00052101003140400010740c09100c2901240000c0207450b6001948040340c1d100401e1582040c3c141d500e00041000030b0002c2407031700380844142d681e0f02ea1020604803505d2180b518045010422508101c050601681344810500008a00c012180d51810200ca046202260056a011a0511083ca45401900452071040b03540b001d081000c0d1700012072042c00548544000321000902400719101488402003070390b0465001c219070b507540e11004d0f0044000b950064014060040000c0205000340f080d60401041141c0d401c1d19510600741080b0701d64400707802950070440446031140050301080700340b806144200010b10b241d081d0722001800e0038018064000512074a84000c000004108030710b6a0f201c84680800b2899889500050f6400c1c804c0390840b11404012070709640044403002c0056010301d2040b1020019aa0398950490301d0740248400551104521802c0402500c0d00b54410079040c0b04504802c5d922002042c070f501c7c21540d80803070895103103840308c85401c144001809 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 590285413 1250 590284163 590284169
    0xf0304120b060f01120f1103010311100503071e09030b18060a06050105070b07090807031a07030605030606090c04091806110304050304090e070e070e120d020a0f1a0c0a0306 76
    0x2000f1500c00382002c00030b4040408100c401052650b00c0f0150f051710b1072035030061213001c01c0c0c000740540c0c0c03940c60b820017260009140240a010300c0b1481000f01203d88a0412240b1403000b41d65410b41c14001c800318071000e504d0380f06102081142841d00440800c03c0c503480c0500400f42c07190000c0b61407511409590134080c008008041061074a0800c10083e600901207a51f07a0303511078400e0b10107a448400544410205030054081d51040304404801c02c40b03540c14020040701d0b91304400301e540e96580c07002c600741c4905025040e00341d0030140203e035131420089680c9402800d20f280395410140c0302e4484104440c2000003586003646044c1d100c00a2007818441e8918410301401a03d10b54506512130661740d120303e100b1a2050303075071540005104103080c0900c0020301603540543d04181417081e0000c1c58400103009081c030494449004402d400f9000a403c07040b44216000b4050307600c1c47e621202140c1215600980e0b500d148540d0144090000700f119034413171000c5002042d12041e007140300030103e6002d60 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 590286663 1250 590285413 590285419
    0x16030c02130509010b0f10080604020d0c02030a08010b040311100309050d0201090332070c05030d030603060e0a11120a021503040b0f010506040302041a0a090204080f0c060304080a020f0304120b06 86
    0x101c0000c05e1604c500107807c441c0b01c0300d800d10342602d03140c00000c134009114100d0203984607131a01c048200c1c11980440140480e4042c2e40d5100e0490b40c99101d41c0000d44640e200c0101002d400310501801c5003404406010000366900740083c14681c1521110b0424030340c40c10040c0140d645207002401c246d000000440e00f0001b010240d202681e48440e4502e05038604402c25480d60707004107541d0208a5140355003405440c0c05026180c1400c600d400c00b5001e0440d03400f04a4009040030141203c095000a1b0081c138250001a11540c008140c0107104c0700304e18414242a0601403041c840001d03071510030410340b118a10225456991801e42400341a00001406070007000b225100100100da0303d0700195425070f90100d400017101d9282441030100414089a141c1c2c1016000a00044c620220b03800340084440700c0c020727561a8048041500d0b1100d01c2041a240d0215040c80403030042040c5a0262000c40c0c0f40c0d004030784422010301d68491031908283d01c0408240d00b84a4200e0800c041c030000c05030850700076 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 590287769 1106 590286663 590286679
    0xf0507080714010e0102030c0c060a030902150c0c030f0a1b18060906050303070816110303030414010c08060102211902100507080c16030c02130509010b 67
    0x5007030b070709010505002d80582c141d4000b2081391507404124000d03041d01608002000415040300c0d403a0010541e482100d00d005864020010f05203540200c042a12908102c1d140c61800c000741d910140030390804500c40304d80740b200041403250158441040b910b9040d070710100076026840c41d8000042d2285121900510f80721542c0100e090320341081c4103001a5442d03509040c0c1c1e80c4100d0000a00800c001c20081c0718803d102c4868000b014400d2035500d52200c50703000085c0c03540d00140d400f030301c0a9806502e00b4105042c24401c2d80d070803610300d0421050320f03e017650010b07445500d004001c00b80c1498440c401072030315441204a5800006e02d400340c0000180c80745000b5690011001e00c0c103120351a0001140803e03004100b000e124240007203d0ba850300440c00d400e4001181d0302c4000705c0c05d015034041c1440048c0e0310a140d01320310301326a0000040c1845c00041701c43c03d54540800c018052060 = true := by decide +kernel

theorem cover : BRFrame.Cov 590107913 590287769 := by
  have h0 := BRFrame.cov_init 590107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 590107913 ≤ n) (h2 : n < 590287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
