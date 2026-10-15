-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4300
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:10:11.36581+00:00
-- url     : https://prove2.me/submissions/956607f0-f1eb-4b4b-a4e8-7caa931d16b5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 773201438 ≤ n < 773381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 773202688 1250 773201438 773201449
    0x317032403030903070e0a1817030c090303030a0f11040e0c03062b05120301240e032b05160f0632010603020a1d031002120f10050105030105 62
    0x100c503160305110402440907030740c806008580041081c01550001131400130500c4003901c601d03e000e01ca441c890000210b0014a800604000038100103c006442e640c0d0040e40800502c1110301445e41440040100403481c907081e0806e481a0740600c10034407040b500320150350b0813801107024003230490402600156a401c515809568440001019401d03111040303000302504202840c442406c0b14004031a60701844810400310500d081c1d241a0b451643d85440c610300c00340d503550681e21401881d090404000140310340c1001c1c0080c240141075502c4041410942c1c04500210340c0140e1041c0d000d0500d0901c107601680a68254401c58a101c80c040304030b507a180c4600c0201c100040364000d03515841107000c401c0c10f111002145060f4500e854420108280035994040705a03c080e0400d4010010b4494061740041080030148058107000100c0c0105c2c00006e0130207022290b80d200c454400f1858688211b40541c542d07000700c0c02c0f441c528045e0b80b00d008504501742000e0003540d002ca801000100200e0802 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 773203938 1250 773202688 773202751
    0x6041709010c15020d02070803010e06060304110607020f0a0612060906050f0904050a0b040b0a05060d051009050a022e26151008060f03011802010c020325031703 71
    0x200c001450840140517480403a0459001a51440b8010005129900c4441c03081174004008442c41401e41c60701d603072401c0b090301d940d4204030300612010403442c045441300480031010314002442d0010003a140c540042004012149143d40d0b1400c2003800110340001d84582015504060054080741c0364003024802400c40103802241d2910502d4003480100315640794007400740b0b11800e40bc0340030381055540c00d01640d101604441c440d88401c1414030009100085035100e082c0704000100710005642086414079480c0b0030302a4009150700c00316040b4040e140100c01103501580b03000c1c0f07080c1c024040c089440e10000800005180f084400101c140b15181b041d09900100c808240c044441032200882c408d40340a861400110b10a8014003c99181019418003d0203080c0d0080180510950448180984020002c0e040c441e13000803460640d01c09018940041106c03200413032084451180510141e09144002d880d03000b00c41c04401d07100f0040b002140d0042d018840c5014a4071600d134204d0602108 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 773205188 1250 773203938 773203973
    0x9090c05060f12010b0702010e041812021504060609052203140d1b1b0f0206030a0e071d010605030f1f0503070b040302040b191215090506041709010c 66
    0x510040f06448a481c9219020701402032003261110401c0c40003503e01d200007120f091165003451104d0494410070340c0002500390b040f0604052800e0380c0c000503810a0181200c0405495031182040140202074002c0700c202c504040f01002965200108015540701d00c0950300003160411140101091107440c140d1801c200106403240703040300390007155049030003403159615a9820860715010054000c013086c0c10b030303030500b03042d49080107029968504004480b210003881a20040003107841100315034005c00e0b072841d2a41c21120825100c400e5000c28066102040d06c0c10780c00000080341c424402c0b8281c80c0035500d61192501c02d51244080007602c0b10740032011800002104000040329501040601e004050403080156510301358014001952035040d1014044c0b0700d070565010500c0d09801d0f07100b049400040001d04403a1851801c242c041c0d24120244034428144807034042404000700d00345000d58803a4428660000401e00900401d005201d0003501082230805180d0100780d00c40c9000c00001c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 773206438 1250 773205188 773205217
    0xd0e030d080a141e0f0c0f030c16050a05060106180e04150f060614160312060801020a11010f1a06091f021e030717160f1b09090c0506 59
    0x4810b01c0e60f891100850341c240201000c18483c260010086040ca500001800e40402203480c0c4162060304610420758590b001480c000002200c55480105854112200c506500e9010300c150400b0380d5070f40b048030030549150080f40000103030b02e40200f08400780720707000425610465284c001500e02507000184199907517006801e000440520900c15640f0203100050300081240c2008401001c0e211419001c0303002c001c08000f8001c0f020341e00710300c0c084450b0f45890142d407030280c0c0800d4000941026800506550300124004400d01c0c0c0188000c1c50303144a0300000c0003d2a0508029401e4688280e036050310800c0e10000040c16042582c02000010000780156500c1d10212044030f4005000d00c40080058210b20030501d41c5824078440c8983c072107114801141051410344a00e906c3c044404c4000b01400c3d400102200340e41420351494492640081220525080074202001c03246840c0400c01c000401074070780440d1440240c0700e000c0c10740c5d40012018401d0340c00c240a000c3c00d54088944841d958 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 773207688 1250 773206438 773206451
    0x30c090b09130809030a0516060206060d11030f0a060c080f190c0521010e1305070e0a0b040213030b010f0e04020409020d02100c0c090c08071d030312090d0e030d080a 73
    0x151400c04c28280341c2d40c032500051804a2301385600e5480c9400c07603084401150002e9052040d0350b694492581001a000340e20305c00401c0d502c82c0000e24225445a1588140c01803103400c109028003031b070008502d0907041e242d098490745c80188034032a403d401c54841002e2900d0062580b10f14405920118189826050051409407046054200c4c030100c00154003034101180010712030309240c0442281c00100605001d003009150342d40b89526000140640100752074400c1c005039044031641c00131045980c000c3c05c01c560322201ca40d20301c640302803580000e9884200c1c82000190481148001a00721028501e50b90182d440f03650800c000340001501c1a80c0c0510500b8418000d40d0b9202242c00c088441c641f51505540803600d080c26001c161079200d44160b170f05c0c24002c0051250051000307540324206151841000301d00b0701c904440c4000301c44405415100210380501d0000c650811640a5602c4100712054800441001c503085602028a540c064002985800c03c6074001c42125410454802000c03444 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 773208938 1250 773207688 773207707
    0x30b03100e071805010503010b0316031b15050a1d01050a030207060e070b0d0f0c0806011b080c0717070501020322031203020d0507020106032f0415030c090b091308 72
    0x10507020f030340054541c2c600040107545003d10480131b8401040e000b400325110b00c50060301d00c031001d1388005400d181c0da407074500c001100082c002c207000e060001c3c0700741a0f0340d584060003003454001c05e007000003085070607000e0030109100f048140c521030300503501c2070304e80450244100c001c0c0d00b22610460340161552006490742c5004c2c014000038100c2c2d000e0190f00c440c00c0e0305101c1d080d03500310114964800d14040403080c240e640f0501440d4000d10030b00701659030704403c99030064040f80504015007192008980510003501c0414980c080365500d032008a00311854141c069100d003103501c03800340941d104102044604a5404055950100c1e1300c0515590760707a42d4841c841184100040f46001a9001441c51005011441505d8000080388001c0010b603046941d20708a038407004030301d07600d400255200300c499044020400c0c04003200141042c0441c03105a405149155564001110713400345003840800c0c0048c69200d80c80401100034114215901c501c1030700c40c600307a07400c0001c0d9211502040481c01 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 773210188 1250 773208938 773208959
    0x3020c07060809060c1303020909191202150108030d0b0a080a0501020901031a03060a050903071e0201080c1204081b1608010c030c14090a1a04060807030b03100e07 72
    0x20310345612a42c00515201c00c54904204009101406100341405502c0f200d80f413070200c0b031017602d5041d035080300c05442c1e484105242006440c400b203520500119903904000101c03a13902400d084580880b0041b00e44180103d468030f4003401900c0543c0d000340201d10b400610785d013001c0c2e444580a410020701070344444a032400e056100300d0641d816074000401d40c005581c580300381080c1c0c0300785038240b05200180b00006512032a028210032a12615200820016001401100c0401707900c55100e030005607071701e6090030f60382050b00800d038042180ca8001a4031b20400c4400c07110520300c000041012562241d4412115802a484e4036075000300c03900c800d81410f00c00300690404401c84403d060042881d107606682907521a00f550401c2509290b0070000042d00b00d91900d0124800a80c3c0c01d032200000750100701c80f5a2650b0100c1c0f5211480426160145000380c02007003580c48075903540500e583ca41718150b041c1d07400340d5600c1c2d400d580450014240e800c00d660008110802036415620115a01c214480 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 773211438 1250 773210188 773210203
    0xf0f18010609140105040302180a02130609081e0a0b0709090203190c0201060621090623090d0503070f0e03011517061302060f0c0a060b09060306011a090103020c 71
    0x440c182c1ca40038000404000c1a100d100202441e000d482c05040d9400311320154494032401e14035481d802c01040940e0415015075500c001c0410b020154956030300380c0140300d29880c1c401d680c1a4000c402c3d400d107242290b440c0045800d000712005016001e4107a03510b840080e001004a41005000d8030003281c031501034001580241000c004a4001100100c10901201c0410b00004256890300c1010007a054202d0305920303208007103072007228042410380602c0001d41071031331000348518030341406001d086840b02003200c4000ba841c859032040303503242d82000e50b5581c009550354000c100103000050b0814450745408411441d01d140101e2409015804642900d882c4911038068a0160b00f0911040300545924110040c480000300752500344100780c3c0d00c107051040404ae00480001820054030010340b011596541103080031a00700110505221004050004006124203c0030011980343d2030b00080450503075041032000c45038600020464003550f844440d1082c140341e028080148821070901104 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 773212688 1250 773211438 773211449
    0x90218060c101503050c040c0212091f02030a080c07170a110105160f02012703051303060906380d080318150103051209040f020c0a060605030102090f0f1801 69
    0x40b1103044d0301d4060f0a0110355444240150300d00340310013484950028806000301300074401c207541c4c0da103880045140e0038440002c0000b107801c45480d82245c69400001000c01c01942d940301440740d15144451640c921550341c1c080d1201e48200340712140810080c005003162021402e02905a04000381c40a00396402290002e07002c10084084c0c54040c1c0d007000032240c0074111072000b042400720300028841100202a20246104c0d0385c2001801014014811200140c411200c030028072640c0e41f8050b0017034000c15008030342c51800c20703140720304205a26100270700342c0380103401c04041a5000d20460b1002c0e035141d26041d621081c495202c001042d0104015030150084580d00f00a02e014901c815240440c0c00d80141404403812307004001140d0041400e007194034451862666a02c1c1400c0080d01402d02c3c0c4032001c550510008850550f02400500c01400c24455401407142c0c994890400d0f08074000c4d00d206580011070b201d081400da1900d4890981b0840b0700600701000300d9003011b00c0c040451000d8000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 773213938 1250 773212688 773212721
    0x8071203060504092402040e1305071809050712081206030304090c08100f06050409020a2d0314060d0809130c170c0f0a030510090f0b0a090218060c10 66
    0x30140b90034007519107000040c4005d442985060f14010107407044041c0146200d020240711b07580281080010f00c5840000c0840080d90a85003d000c10080001c0c4804c003022101840340f0b5000181740b45811080c60846a00820760340d04240701e80c51100c1c00c000c0e001340720a5040c0020040800c14a5081c85004510480c0d40d617000c90501d0400040c507428022500200038070b1101020401241360712000300ca094554003030000da100c1240060507103004007102d407048942d0002d800c3c81c003406004812032070340302e4000c2e54040c400300710310315000c203078201f17040c0c07110b6801c02000100d10b03001c201e0001c000d00440b02c010340b0254070646044c01030703011540d03103000b10000141c811095032407014000b14000d404c01130101a5038503101c22810b8007080d900c601c2c6103140030f040c0c0f10000201081f50342c0b1500402040301d481d040c000e0340744007441440106030001c0414400c00c04080c0204040c502c620a1303a605170840540105990560130800c50b40340c010000d00c4065101c0d0b400b5040c68111035016012049450381c0c103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 773215188 1250 773213938 773213963
    0x2100c06050f0903030610090f0e070215010503060a0e0c0a14030d050a020316020316030825110f060f04080601090e190605100b03040b0a0c0c0807120306050409 71
    0x5249041e104041d06000680c102c8034180b00d145900481101e402070802c80d542c0d0a4540361030025074404003e5402030450f440319507000682c40a81d030544520072038075642510030b603114944400400d00c07001e009564042d401741001915415080e0300c02c610342c650b104100c4044181032800a1641c54132030704071540100145006401c18141003003c100900d1290030300074106100d1800c025600e003c1d412490304050302405d484c1d41503480501c180c465401c0e00c1c107540e00d001ea4403030400360901e03840782da4001b0070415455031509205401f98100c03c8155032103511915000020f80030020030580034445070b0b5020902f00b00c0300d1041515500188028039a07607020b42955032400b000002220414070b00b00c403181d04182c841c3c07181c0c201d65030700c2c11881680c4420000f40d5602d4504400103003003a260000c402011002041c003080c0003490f8200c2d4801d43c4064403e00038064182022118410482402405608144034000c0002c00303400c0c48214000662074000380781c3c1c4d43d440006056606010b01038404071203051 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 773216438 1250 773215188 773215193
    0x121a03011808090f0a030b090f10060e0606211501020d03111c0608120304050f072303123c0a0c1515060f02070f0e09010902100c 57
    0x200701981090480080d15407001d5262008188240307143d4602c0f6000c01c1001403101c0e9124403e110285800c81c103003001ca85000400a0740e110140c0289646511905041c24240300250203080107440148c0c3d401c80c150b4075040c061021582015400c010913001500751120803550491700d080c45090310b1380c140c21200c00302e0030019062042561544c4101030400c071f120055008107600321400a1038445450b00d0011307910021a00401c140d81100e1ba590065111541481ca0580051409240190140d440c541058515940d88030b03010300c82c0c28a005441c3c00c4900300401c444d201c481c200440a4240c440f50003013144007009a0340040c1890f0ba1003401030321070358802c02106103404002d01c80406485901c240346a006d02043c012408d0070341c20450f07003003801d40c2044644201b203045030040c20004d00c0740394a20001101c6100040c091080015810100c0c10300c010700c00142c04007141c06110001d54181d0400f000c0714280c100050039200740390340314090030300142c48100848a07608503c2e80d5031840650300b41f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 773217688 1250 773216438 773216441
    0x1b050a050703120503061e041415090901060503060f0718030b07030b0d0c0b160606030b0105100c0c0909032001020a3b18010801020d0509031305060a121a0301 70
    0xd100401c01c00c0028000c1080940303425180c21f205010002d044894440240000b03030281a07061a400b005c6280402440300000c0254007144140360100c4400b820341d039442402c00e0895004e0300c07a0660541c8404007164032200e01022a5130400a545071104a002e6022081c0903a081d86030f1007121108a007508001c09550315101e6510074210482c0d154141c84141d0b00d035500c807608179019003074030b1610010b64102902d00c0a148a501c0701d90241c5d040c01070703035075138244100020001d1240c1030241454246e901c0b180c510590708c40004170750000d02104000d0502a40b40000c22108004505121841c600303084144031404410039001501c0d400035035100d4800741c0c024403440c0314460034000b06001400c0c50603400c21404100710782c0c0c20001140756040c1e1a000011b10030b844501700c03840c000204e480000c0bd104dc030640003001a800e030200c080c88130345c48420906680c0d01c221a5407400c04104500107000c0307482e240c03000b00959516898078118030152000854212000c964821030038108030000d5000f941002e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 773218938 1250 773217688 773217713
    0x40b09090f090a02300a031e0c081804051014062d070c0807151b03270e1b03040b01090e0307080a210204050307061b050a050703 57
    0x1c4034126055800c200c51143e5803140d219500038071a4520140e481c02d201c4904402107042d50f22100518000400710800c140c480c00350704404c0d400122001c034503080c010340c00b1811500e040000c1c0d41d0028050216124900d40b40c001141001c0c2c50818014414656941c9019490140b20b04c400041d640500d407081442035207030120160b50088a051103000034124102001c20380c500c6040c6155039840054110740b8040c2c1c425240000c00d40710185001081403640010f0345001e407040d6103001140d041e9803071804d4598001e0501072190b00c0e1600365040d00020300c10000b917100014440011001c2c48a501c514402a2a0640201c510004000304003c0c002003010b4091589040b81880c1900d581803540358800c411005000da51403180c0c655202c40d00c6103404100b1260142d410011481c0c6400280750b0003014be1140c55200d8481c0a070810883c1c0701816103108460455900030024401c0038504203042d12984415200800010440300206000c00c2040c4101040c442c401c03c0505811415031030000040f084 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 773220188 1250 773218938 773218951
    0x1a1806040914150f010305101a03090606060304080405010e0a0f0b0c121312050c060a1716050d0b060d090602070b070c1208090a05100b041d07060c0807050102040b0909 74
    0x20f0150100450b29100034450220b1400e01e80840c3d25590542c102c0c43c40300c52230340184503901d01c08111600505800e009540121118020383d4815183c2d01c040062900080c0c0740030f0005001008100200e601985940c04680705c00b80c2031244542e40e60302c07410030300225035100c0c450741d42001a21000510083c0b000e64045030303210644a00380030701404003120705840e074002c0100c13542d09114402d0a000c000c001d01048030100811241d40d515607100020031825852002c00c01100c900c0010500980c070341070000c100a11140d9486040a689051000140149159136900300c0001c001014902e5081d01481c0d900c1d6000b50303000360395520a45480924600000c00142c1044000070003000040c00400c0106e1140d40103140600c06074994196040c140401c125008081c1e108540c0103980b101c0d00c6400c401c606201c1120200062a044c0d0303108244110202410403a03500200d005004982c041c03802d84415a004882480c100a6250b8600d82242e200380c02141030000041085c80c5986440104240c4c4240c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 773221438 1250 773220188 773220211
    0x230c0d0b01080f36031206030a02030604060b1203160b011d0103030305250e0a1a03180715030203150f01021c11120405040e0303011a1806040914 64
    0x140140040448840c050501c82e81c04aa1000400300300c0c10101c8014074000ca06900b4540c0141d80d42c0c10103a17030ba484403544074070760010200020300c140350103e50703141a03075006800790240d591243c1c0c0e90002030100c030030031a03404440e02d0b090a011031b000700044d20110024101c1c0c4070b461442410716081c4048140c0c46091a8000752100407200113005036520f0450f5410304011565858000c00030290800344804000b03140d400c8a400c03d9969817040c002e0004074400c0d101d400e05c10b81c0390040281040b611040d0001181d4040000c181c07441c0300c03416403070b00c101c0880c0306450030543c44107103401c0751841e0241800002900802406100c2c401c40c01240140e40003107802c080030341710000002c1e454403100040c0601817001e000403100003501808403002c1e2120000196155002102002c200d6a0820300401e400303a4a03001d04840209800400c81c0c0c1070b210141241c0213440d40b000324000042d030143c0f100c0c4810f03100390544212641c990202500141609074804240200d051862005403d0000d000c0031461 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 773222688 1250 773221438 773221441
    0x7050409051b060d0203330303090f0a0b040303080708070201020a091203030f050106050a140301030c0e070504031a18060c0a0309050a020d05060f0a0b010909230c0d0b0108 76
    0x860000300d102451142c80030003442c809001000034002d010700c4003954510b034000800c00c6607400d060603894950b149540000c00b43c10541c072400d814010f2441c40b0030754140d4010840813000c0d1030a00f0040b00048002003140d04d4154490b0707a1204140c1060348110301140064050200c0c43e5004000a54003a003184001c40c102007514000074000701e030a201d00e1008082407084c02d0149407103030b0010034248000030010300140d6943ca10080c032562000c060400081c503d1000750750040d504c842124120b82e088411400c21b9400c1c60418280a0b82c007810314828040108000000180c004901c04500030450f00c040e01d00349003100750407205c21034030ba09401071900300d04101f03d41e844070003050702c04507111458001482c022070302e0403900c1c0c020740400180d4003880c0002c40c1c00802c080010307024131420f80301c038071003445440d0405e168003a5580050314501203900d0008c1030002e10352a17440700d000d0104080c001521501040548015207109036458169400b0000e80503e031b01d51070b80500c01c4a280c0030300e4034880c02d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 773223938 1250 773222688 773222693
    0x807020d210b01020a1221061d06060706060f0e06090405060135061e0906060616020d1b06050f030610020a0c0e041509080306012f0a0507050409 64
    0x141d0301d0104403009510707a1454404001e9200f0456034070740c2540000c1c2020340c81484c1a0142049640000c0b4109824048052032001d086034001d00e0100c1d6601c1e07031980400440440c0c6d05810082c01484150041c60501480c404030b0418003403100207140181059036a08d0402c0c030365007103040004000314015040541440001400011030904560428040c02c0302e21101c1c610002c072060307140f030540340e244000b0307034122a8601e0003260700741c0100382e42568001040c0509100d81040042281c540145030032220004540c0d017091001403071440d2405003604504101580003c480400814007500e400045081d107104071400344580001070203090500c14103000503d00160254480149268003d100802116454a0007080080e0400d07a01071440b1307072507917110300d8507118502c0c3c01c0301e0984a032440101610004820b030b2090100c40c1350010b0784c07540386079240d10064940c1c0041c3d000720509050f0348108294440100d05051a02e4000400034000701c48190801510b0130b40036400c07a5216034038182e0303138100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 773225188 1250 773223938 773223977
    0x503070f110f01060b0c0105010801181121031206030f0c01050d0f0501170d080f0708100302130903020609010515090c09030a0c0302121623030d0807020d 68
    0x1090030614000c1407410300c1580071410310100080d441c403950f08101001ca96141641c0260a2030101e65000300b01c144c1e41c407001607080e2450890000ea20306001142440418401c1c030360501c25010140591011800340c03104050103828000c13074100b0079000810501c000c6920f4500041e00401d003140280840a404c206458440c0c2c0034264040c18004000f030340d8817002c0701e550410b000c0801a00400c000b80c4da0740c0c001d035411000d050003001c4042d008108030300804900542c10a400f580c404031410f41ca655038044282d4030610050201200a10082070000c016601c45101000491030075101182082051501a24128000e03141d4407950f4186810840000c2454820090041c41142c1b000c915480d2640c04c0f03d00d9126a4140c95018010300e111007042c0101e030401e84045920a035112440c6040c040c641544910194442c4100c2c0d042c003035003c00030b040c1d2003c0d1840c03411110302081303480200c040300000c0c58100200d00b0340707020908040400040607018070001a400e8910300302003100c4e01a100ba041c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 773226438 1250 773225188 773225207
    0x90a0e030a050c0a05030403030e1504030c06032307050a09082a0a0e090313080d0806270406150506070b0705030a180c080601170a060e1204091a01050307 68
    0x700b0801103800243d070801005250030150708030302a29911900c90a0082109000549003401444800694030b00d442c883c0c01102d0480c1d800c031020021590421908a007c0c05103400b85401e801000007420020b4010380c05114011840c9468465607800300d0312000d408041d05a1100c10729030018944034041641d0910342d8071071248020400c00b05030702100005240f082e010342140c0040c440400030007078120310000017001305084585074051002c1e96044102c2e50340601059180c00101c0081c0071a895003040c514511b050100c0d0220b00c0c211408a4229005c0e402080703c0540d0f0140c3c0720816091102c10408100000d01400d03103100e4580345054490044c0310324003a06e55020440c1c00400030312a0100b59000c40340e240b50702030a442181e103050900b4412324589000d40c03446030084200026603030085140c108828128440038000c4440036480d020003e0455888030200750240c0d030504034488007c00e00900107071003444000141084007600304051803081030a540d052203420000e018486800c43c5c0c628 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 773227688 1250 773226438 773226457
    0xf061e010203043f030201110304021806030f010c180e0705040b0c030f040b070302070906080c0618040c09030b1005010e060c010603061817040608010303080901061503020405090a0e03 81
    0x1a0313004241500c0c0789001600c4d9000807110f010310094852444114040e00b0101c56009a00038452043d0303107010343c8103030311066500030361002988100314001040030381e5650703000b9001400e41b001c1510202c00ca43c01c0d554001007903030020b021503002d1010308442d01c41090140070540c1cbc000302c9614017600041c22510135409641c01d20140401c1a180c1c8031000c1048405118003840f01c1615a581d03800e122243c1d81140e007086000d4041e1040224061034244255000c0f180c0341001040d00d000402c0500010b903120160544528240080a400585903409042d14481c159941e0200c698603609104406071006030041ca40c0e441603290401c00c980c0d01210341400359900316003d581e0742c9003001901340103003e81c0d840105128240800e10841c6500440d0a80c0311f280954130740401800406400a030901c80c034041c5401003000d9030011310100784107075201c83e40a0f4846d00001043c603102c4008542d5131026103103001c002600000d0520490070201040d0b41c0106001a0038440c07842c072096034035101d00601914 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 773228938 1250 773227688 773227709
    0x3010627151407020406030b0f060405060102062701050c07120203120105270c0301170f33040c03170a1205100e180d02060c030402010c08040e0f061e01020304 70
    0x2c201c00d01c1c0c81c60301112281a4020810010180c0c0c03407400d030054240807146015203024400024640341818000e0a1061a050740981950b996000c0d0002e80703008070034400b180c0c02c1080d450441c841d641c01d129042c0291404c4810710748503001031914181412000c43e0304011074006100c0442843e050204441c10740b0b00445209112101e00300d030b0f40c4408100d584150040549140c24003059010002c01541622840c0621030a400740d2a1002035840b105011003024940c81824005912800141c020981c1040034035000c40d40c10580b8614500341ca01982d0a07100140b2407101001004643c0d000e010541ba4224160b07402d01034038400c042c0c505001d8071f0f02c40e118551280d00003407030080301200081c060708070100031100a00f0500141d55004003221011f0328a403042c0000e110b205800021102d10644605120501d150f656600450700400c8403442116202018030020034200c403e0180310b486070001003205c00c1d0501c3c001041004101d0b07d00410094486001061075051360701100b21070564041009 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 773230188 1250 773228938 773228957
    0xa0b03070312200303070f022404111c0303020903101107060c1b14100501030816030309060905061b0c100515180109140610080405120301062715 64
    0x8143c00344070280c0448409010000800074101d402002c62614a5a01c0c0c0c02ca5403210a062909410700c006d0048407403544000c440000c0c005840d03419004c40281d80507205288110030300319040c1040110a0084005c240c010480a10b507003020491030ba6407040c20705081c403804490060044061156201c003615898076568204402400342c4250800302c001d602e034243d10703942c0702d04000903660400e0701c1c078003414080c0603038848802c4c155014180c183c17504a0a19403418802c021048060540010110241526450803030046031a500c80d2802640c080c402502c002c1c6001c1000e8201100d142071683c050540c00c2c42900400c98000030f16000c0d41c54408000141c5840d50b099071400d03107000050541e80050590400091841510b0806040701c0a0701000d01c8103042455248010103011100540c008843c40b5031101114443d02c20755030064040c2c4281e50047c1d403047c1103400c20f94800d0700044040f918146004c0300c030307208481003080c00c08043c140b907d08082c02c00d8800c000c0410041006400c1141c00038 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 773231438 1250 773230188 773230217
    0x1b071a09010c02040c17070e040e06070207121e0b0103021804150b030a020a12051006051f1b0501150603050f150a0f08150a2d020405040e01050a0b03070312 69
    0x501a106c640c40d440c2c0c08009250851000341710130b4002d0075041c0103e040c2499050400000a0310740d025050980161000d01d0038101c1440d100c488401b815901440459101c82c030400300c085113000d041d40100f101d030410358194018082c1c0c03202402000203901810700104004200315199200e201c1c2c83c0380c4030101d0000113032400640b9004200038042c0d8800ca0700d807000921080c40d00d175480d02c03e910035000e54003070750b40301d542d40011625184203a035003003007010494583c0f0480010503105c8044040c20081061b5041c0814018620240c01040720b8607996441d840d11482c500a583d007000300010f14003804580b070030b04269010040d000c0d040d85460150608449041d5807410244405425213050904110396030b401481c0d6240c0c0e110802003940c540d00400308800410034044d41190103036240c0cbd410301d00b000c609403125460405281c107c0c80244d0900c004a260b9469004044c0418451400841d290908041520440344a8841d00e03110354481d8000300001031020420216100c01410111040354008 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 773232688 1250 773231438 773231447
    0x1050a06050d2a17060f0117190611030a06170721050102120a020a1d0108071d04090b0603060c030615070201020c040e010e070b030903160501021b071a09010c02040c 73
    0x58100321001303e100640c1c1045000300140492045060060f08503007640c5e00d2414501c51104069201400c0c0c000a0000c1000c5140c5010004154443c01c3c0c005100e6a0a1490b4000d5400a0f07031003062403078480e042000a0040341c1111080003100700007400030a880e0004809070003003038100a4004c140d90f5010790060110030341c103560060410740c0d03040d289803801004880083d0b102903001c8021510301c0ca003c13500c00003055414800c000045c0c442c41c5058655100070380701d0440002042c94264244000703800c1d2905d940c061111011311070024015142080010141040c600170701c01d00031140140b0030020b0720f5850034860364004445940c0287e480f038007400102c0c104500351a526801c181898007420001c0701c154440805400c164042c0d4480a4403020044030a1006440350f08940c0d1042c03102e07024543c50a030b2040e4840d81306100040c50030701704035001041046080c11011094100d04d40c1003000640100d94115843c422840c403528120442001803c5e07504002c1c8007030b006658800b4940c0f10540207 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 773233938 1250 773232688 773232773
    0x503070323070f080708130f090c0c060209150c03070507090e0309010c0629030c010f022508150603100204030309180f3201030534060201050a06050d 66
    0x915a0325607d003902d00e0701c4408280b059580441194400268100443c441d40206007042da44400841c0e01c1629908080d40204100d40d0f4403024840001d00f06004060041c9072100744500915246c0700e00d81003290820059502480c0c1003030070806500031321003010085401c403200c242040c00c141d007290b0919100928844100013401c04403031061348003134124003c0000007003800f20200c0315445240130044502340441403100000d03030b00ca06403101180c5035a4034006c80401e151210340c91100c0e5181b0250346003810340385294004245050a2050909050050748000300303010509601e00791130355400515910843c482c240640e4481000c08651804a400c200711490007c1420300c1913031071035000e54004050200320103040c0450071103504804401d900d0054101c1c3d4020707002d0101303141c1c000d0001d001001e0b1062500c110100040c0321180000b407a22442020380344641c0005003514041c4200e208131a180e80295103d4106400c035440091414541c41d84620000600122502601c3e481d21680510 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 773235188 1250 773233938 773233943
    0xb1c051c1205070507020a05060c010b0301050c0301030309082a010e040903080f10142106090609070e15010e01030605041404062a050c03070204090503070323070f0807 74
    0x111481000350a0750004010034801c0d0010400c001a480c0d5510a03203581c030451341c009410210b004030800c65454580081c1912030350b01000400c514601d4000a400c40300200d0745104584c07000310040c0145907004041c01d01901c01000109502c0c0d14101410010100c5c01c3c540a2100b41c1d00301c1c9030301c42a44908250000384002070401d121244951070058445241112600240707502c213800601ca0143d6410108115103808810400d4048400c06024001c61400d020340c1c0e110fa82c10038008503404003000b000c1d124405107030140402d8141201d420b81441c103154040403941080c01c06004101410408000400c202400d0225808401d03100590180c0f0241d40060341c09450014409c00701007a4004035449144181d0040042211036031102c1d0b00c0d070140c8260b85203456045107a11000c0b50191000300541c501020489040140641c0014142c5a82c03420840e1260000b003022010140c0050806409080721005203000c4040000006100d004401028040d140d03500b00d0802404400801c482072640c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 773236438 1250 773235188 773235223
    0x52404120e12250f06030e031e0301090516080a090302070503010e01021b01090807080a09080d0c0506130308191e06052404050111101a010e040b1c05 66
    0x40281155519008180f016a0f8224800580c4011903803c00c0d02503815240700c0c06640702041e040c210b048001300164944405c251104012030701c0d403641d880713469498030101d43e901540d0b20f40c18100140103544001d07111100c3c0148070301e0307282209038000e010b055110060540026011090307040032460b2031850b40c41103416500c5d0080c00c0c8042b11041d00100b00b440f05940e40030131301c2000c3e072141c18220b84c400003015015071800c0c00b0b01000954500014400107000f0300d000c00d03541d516402601d04000e150007120300800c40b801e00c010708101091003600e40c8040414011001c4038030b140c402400041004000030400b900032080d042050106074014061400e0036880d07004101c15003601c07100204800c0c015684607175211240485202c1800348010340c20000c21400a0807d8074040c0107545030b1100ea0794820040c040c0440d9040710b5082c512529101907640320054020345210000500b11081100d980d40c0520b0030034001071481e40b9100d03801013609100c0342c41c000c03004e440c6090440c00d0243d200305c0c040100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 773237688 1250 773236438 773236459
    0x71202150604091e0b1609030231060f05042724020711030f072301050f1201030204060f061707231e0a1b0318030f052404120e 56
    0x8206070745002e200713a0760346d1842e0f0341307964020005a6420000c0c0c400250b00c1ba940c03580807078a1040c12070000044000c0710f03812507586482411400199135141c0c00c84440307581c0b62803003005103140c640120700c040070304080c45405120764003e080540c001801c3c0040c0c44040b602d0300441c104d15200d84496102c41d0005000c549402040c50003d032084ea16204451280c81403444170f14568901040842c100c81004903001201800800c12694026000c46460b06100d0240b10b18403c000e25200100284051110841c0c4c0719810751041000301c85440c0c0108640e040c00c00c2e401d001183d0480740c00b40c2d20400d101c203505039075a1110000c507220079810030f0743d8900f0050220503480403100320010b4089101b600c040c080511070f1500000c402c4e80100f450310000507244201d60783d000e41c18190241e40f82c0c0d00038a00031284000e001030324451808698012141c02c044034510340184071301801034a1254607100d040f076014246540064240c01c078054006031106903841c0610004501581da030881031340c8091310070f00b6007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 773238938 1250 773237688 773237693
    0x10b0a1133010608131115070302010b130c050f130302030a081b031303020907030e1b2e050c030903010504060f0510050a1703041208071202150604091e 67
    0x100700c0564492900c4000160010500c2406188803511402c101d55101d501104503860300da60041140c0c2c281034001d08101400c1c6915800d0000070000140039400128600301c07148288001303192030000407056546001d1594486c954440110390044162040f80f41c3c842d02c034000400c0502510b540003d42c10b21600c11480308002e00d56020b4910700e00c51000894441c1c403292190b50700c0740302d80c14400d00135005250041c070052030000c02c442d812030a58640042d2216220b0707946c0f0b00d860f000c45a54041a80c02c1e041a81e05032404000d00004640700000c081442c85014505c1c03010100c0b00c1c02e20b0014008049850034541104006031100c5040080082c00305d42000d0400c50020301075800c528607a01d06240003c1d111140220401044030000340c02d60240c0c03440c04075078604035084500c81c02058041080300041d14840005280461401084c0319603a0301d050b1702d04031030742c021241e698200f075421026090106084c56031186602540c1920041a482150319103040810a44080042d20003007039a0314070107 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 773240188 1250 773238938 773239003
    0x3050604020a091109041109090403021c0201110a140c071203080609150402030907031709010906170403360e07020106051f0c0b070f030f05010b0a11 66
    0xc0d5009807001c0e482c9a882c0d5651034152051140c00c108103450402c84134803d828954096403201807541000b0341402409400a1746006041d0340c2540141d21194081d05a01c0f1680064108d100490000300401240308011800c03d0240e80101030030f02c8180140c002c0d010110108491100c180c0c0b90030344400e00c2e21003003000e0001002003400d50008103c0c8000802c0d1b414050041800f80c0c01000c80410429409001c0002035400100213095502498400000240044410003c29844055a241c507910228001049058207912417010800481c1c0301c959200f01802906810981600c0c0c19401c94100f0310510070b8242c18007a10005a030581130840030380d414428400b41c01c2d2036820044a1003526040340480c203941d840e00079958072210300c65117461290b0000d03400e144d130701c0704604081d01036424503150345810440856034103020034000700d041d15419625103e1b0f400704c00b618507802c1040313505105038040f1300d00452030190203101d015000d02148074010092040c0202c11500c0107099030500a0341c041 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 773241438 1250 773240188 773240191
    0x1e0305040905060607030509040903110d0302120c070c030308090703080307030f060603020903030a0e0d051203150901030c030f03020f1006031a06010c0206071109040b090d020607021e070f030506 86
    0x40002d140c400450440d2504604840444c2d805996007400d11540004120090023215001c0301804440d2003800080001803007802da034400075450050300c40c03003110a46c010700c1e1401458001d04034000c100400016044150315001d80f80c0528020030b041e03585800f400d2400e1100e401c050030301c04c00030082010185d49070700f21007001d410100c428000d140d954001501a40203a4500a0b4560014003c400c19103100741981c1c0c3d0541c0c40244510407241090322000c0c00c2c00b101b0000c0c410184030000c104800d03491803a440c003034030050560f60010305601d152125240080385000041644917000358000a040c0b007040303d202003903601401d89480d0100014540c00070a01440202d81e03509601c1d610303100c50f802c00303003a6612603a01a150200280d1a43e070800c41a42d2081d24120340c80401340042c100c2d281c40f1404110f01c958440c501c0091181014509241352806d0b0001800c11540700d041000701055012a111b40000c0d14442160310301340400201904007001c5401184502d002c00e070001092002c0040c255 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 773242688 1250 773241438 773241449
    0x41401060f020a050c010c060f05042609030714030109021f14090306010501030c02100c03151202010f03151d04060606050c0d0f0c020904060c0e061809041e030504 72
    0x4a0340009080c03400e0fa11003002000180541c0c020f1401004503500400400c0401d9100d0a000a482c1d554410480c2c112202602d0a0340d03411500f030440280f0301d248403a0800c13000e14207141241000300340400a43c3e02c500e180226056201c8414020b0900e4600350081214564010a80b0aa004140e103802254000462a2000103a520701c500200c003002074007143c5c803610024002d4800c51b03080000550181154140703a0781140b0818101c0300c05429503218006000009640205030403042628108940710381e0780155901012174222400141cbe00602034451a80c0396040101c0c441c203000000c90116201d5030b0007c4e41d0100c05070107034050400060104d0380f2032071041504024151b00d846040b01c0500840340aa096035001d40b403001202070090071a00e05d000e80764a00900c0086040c0d010071500041034401700d840c2c1ba2142481d65071990044041d03400c0c45001c2d18030901701500190103140441c2c1071a0340902401044022800748080188a880522542c0f000703000d64644034a002031a9034814406c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 773243938 1250 773242688 773242697
    0x20d0c12050c040f03080903160602012004230f04090510150518041e08070c05040c0512041a130303051510030b040e1c030b040501080303190b04140106 67
    0xb0030408029040c0c60540d104c0a1849031543d045070780d800e5041e8424983c461f4548594210f1401c0c0c0c141c000c031081c000d080d40740e001103044c00107540d903810302000f001c00b80ca030605802c2c0000d001c814001107800c100c4c2e0140c00e002d0700880e1108800303e40c4c3ca004010209800c6030802c2300c8c200600100080c0ba26424031011020000802c103008864030074803441c01250380c0405800c3c50040c940b401c038050503400a000c3c0002803400007403061840b43d403d001c070b941141c240c02c000c03402c1c00602211000c0100104010385080c45107500541008095200c1d49122030740b10482c040108040c000001d501000d0000f9a1801343c8141c240010409000881540218000b130f0503c8002420038114804548000c000070f00f0340f45420220b994107401808660302100c0d080f55070386c08000040b00040103a00c100204200383c0001d0300b0b0b40e0301300040554030601031407070095043c00010003104400101b22580315080f00c0d080c45208002c41c06a101078542e4044659204e41000c40740b0841d02216103245049aa1541701c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 773245188 1250 773243938 773243941
    0xa0207140d0309150905030114040302010c03112502030d030207140307020f06090301140426090a05010f090b04240206070801051504090212060a1d010501030b04020d0c1205 76
    0x1045910440001c0050019148800412442c070005040119006040c10301100d05511440802e08407120702010000c0c52901d6414041419020300c10f92285130340c1460309000c4070244800e030041901c5056815820300e08501e1200540c8980000c613007a141da070040c162000043d9a01c80100a9002114103603510781400c1c009421900000044504407a4068200c1102c2a90181007000c10740041c0c4a0395015504c0f0012840c0b40c2034501d0146115a100303404400540b866a8010f2900c0c5145003081650f005081207540d00c147e588905c264105c0d2400d117013030082c000c2c04040c102c4542c1c55550105402000c04907000c11132020f0039260980c2000b55143da11060b0035060012a580c100641e09940400c10440c01030145080100502050303062441c040c0d13103015034540c1504101d81c010b0078500d038a940c110040c8070b0079260048400004009000d07038240110048404083c5011042c0309541c14103944100f80c0700c49489903010780b50400000401040300c1405160050031700407145480000b09031800c030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 773246438 1250 773245188 773245229
    0x3060f15012007090b03160918050f010906150e0105040e030f0a0c0308100b0d05060307120501060305070506030601090b09150d0c0206070816231902191109130204020a0207 76
    0x20b12843c1c18410031503625240c7c0c1c9050750705e00040807882e900001d0102c0c946c40103c08034004020204800544a000049120240c02d0060481d0800b135145407203403030b4450081101d4500c0e029018159041250000b480f940c20511851440c4034201d494808103034080303500050150880d8090301040d0190715100d4091f5600c0a420040000d28000c03142209800d01031545408419802a0340c00740020341200c1da4507885080c080050380c0c0e4094119041c1c0e4646500740108482480300600034042a21582d0850400c400042e20741201c074020980c41c5c102c0800c0103000c1c2e540311034021950469000f0481d60b0703080c104c11800081c2171402d00e0040588203040102d54014841c00d5034911810500420783c09121140c5001c5a007400c4030000c201502c01004002581c1682c000c1c02021100344c0c200c1c07410445c1d0f1540401a0500c3c01d0ba514400400202c1c2000c10041115402103078a51101100c0642c01695010f07250b5068080620002e50002d10115800800d990000381030303001e40e070225080020000101 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 773247688 1250 773246438 773246443
    0xf0c210605090a09060b130e0f0304270b06160605070e010918061d0601120b0603010e07110706050c011d2e020c01050103060b03060f15012007090b03 66
    0x6101d40d07030b004101c00d8000340f6401400d51091010b244121008100c044051000a11030884c0318125840c0d00e903611460840b42c82c04204100e408541c51010f903040c5440c00c1401010404010038044503010070390980044000286d10040c0c800c01c0051200b600c40140c3c6100802130f03c03d4001c100e84c1c407442e01012480807400303225001403a00b4143d4980b15002d00b4440d4451740b50010260325180d0980351071000c50040340843c241d030001d2158014044403840d00ea40010070320031150701007a1449103080585201c9445020880e03040d14440c200651242d02c0b1b0400c111940d100046100e9000d00035403d01080c625800b8005100d802c41ea80002d0202500030340111400407030174000c0401d56407141c02441807000106c0c074401c02141c02034500a40300020b80c440481030380c6c8488139244059541c2c0c401441000014803030386080b02c405500411180c42c0c003080703a00c02c00c1d501500c482c0100e00385201c148001e138491203a8440500082024100e4a400c00c0c80c2c06031344181c240540118035007040403e09050a00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 773248938 1250 773247688 773247701
    0x5121c0507020606032a090405010c02010b0a0e04020d2a030203010b220c09081203010602060a020903100b040f0f050910020c0312071b030c02011d100806040f0c21 72
    0x1000f900204030040740340c034040b13046146c041c003c0100d025900c0810340e031038001d03552055020b03100100701240310ad14000d0849003904005032084403103c900b40050a10154585c0e48542d05071a04034584e181828002101442c00c02d241503010300154000c13001c00c1410746030000f16882600280405110301c420040c400034102041100000784a48030814003034103401c459a42107a90a03c0c800341601d0307407101410b040e240b0000c103140c200000010000c040c0d0401640c4c0c3d000c41c0d6075004500b82415080000d4a95060500d0000c2c1107840c0c4102150656903a8000411120801c0307007041100624113401025000468072005c25002e21100d006000070706000715089150300c140513600d403504500031840100070103842c203010007284048802d840041000982e90060007510740d00028030461000504045002c00c8055506003010b407051100c0d1070300c900150302c0141d00c0c10105942d60b96880401c00420240c04411a1182400c24690020b81c00a07002c0e9001800b40d4003a01c48103043d05810800c0d2180d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 773250188 1250 773248938 773248951
    0x140729090a030e12030a1106010b04030206090d0507091803030b061204140c03010515090624070f050304030c03021c170c01150b040503010e0a120c05121c05070206 72
    0x451080400000d1080c400000c3c4000d0041109503500c06083c0e540b0302d1074100c0614180442c192800d001e40340c0004000d42401001900c81c018a028190340c080782c0b140c01020702450141c000c0a50490030003100340641e202500c0c1d44401008007008114800700a401c02c807034140c000c83d10b040c182024509140c0110b40f10310038092040001c1303031200d944007844440001740c040002d00540c2115a00c6a500b80902406900d52640b2456940581d00401c40b4100015026a1150300031041c3d0b1440590494038802014191613081901c82145042840d008c0710188030090443c0400100481040000d40c100d905076030090b200323451016155149103064000501001c1c0100030707070040549500700020700400020b401900045003800d03204941165000054001c03030000400800c06102c5030800348500c00d841c3c000700d4018110559541c070f0780c1201b2070030404030a040100e66491403007800410000e02422034030440c04c05a031014400c84150f04038012451301e540c014101404204201e100142441c0146d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 773251438 1250 773250188 773250193
    0x30501051806213a11070f030b0901051f05220f0902030609011e0203040f020a0b0304031701081c090801060303051201060302190f14072909 62
    0x11811a00682900340142402d901c0040c240d50f640008844450044600e100c04009040e40000500807440d4041c601c0c95046400159400c070b04c03904075202e03d10315000100f50921075060580300260904041c17a5402081801114806c00010031601443c0d0354450012640200400e071514010440b03501d800504080e80e080c028401030006250001d02d2010290035406100d6128940c00c51100036a55100c48000c9859642c940110550505001840d80b001010000700085443c6010b07d0b080005681b440390015a40880003804220349804101c0007660020500701c0c07015511641c00606520445d411000a0005804544103085204d1500d05031007280000d01402d040b500c0222014800c002c00103020440311700000074911200780300303203005580a40d03a0765954115041002c10301c8881a8031450415104002103017407400000c5902d140c0c0041d80c50601c0b000d2055100488884a082150400c41400020042c08000d048056482c01c82c000761801c50a000f2010f1800d403070410115005021034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 773252688 1250 773251438 773251459
    0x5031f081e0c2215051203091216060e0d0c03240c090b07020a170c120a0b010b030c1201060302091002010626030717070302190309030212010e0607020d0f03050105 72
    0x200f85400500c1e80c0384c0c1840d2008481a0343d400003401005400b42d450000c2e400006608119003020007400284840c020000c1c40a4052503c04d070101100c10b100791010001001d2010060790340b84543c0c00a160b8012400340880740e280c4c2002c2d680c1030190039802088204100b41c070815400c4500401280c14050b440e440d08980c540310700f503961540206401c0303a20007107200c03000c2603409020780154004c00300800201040381c880c60a1260408055402035082e80c0300c1c2000400103000a0285819551000d10064494481c80c00705135441c0620b0302c50302c040021900000c54080e03455409040c000c1d1003103480070041001d40030180c0c03c84142b13009040010343c1002055010b122051001d103248101034040380c0c9090a43c1c8c8441814205403132290000c19000501201071603810004c0b00319010318502c3e44031450310f0b90ba40c094600d07000d07440000e020700a800300019244100b0340c401c0c840c604201d01920443d241c80c1d8030080d00c3c3c10480001c01e0208111510b1403840718482c1c400e60307050314005404040d14 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 773253938 1250 773252688 773252749
    0x140709061719150b1c0605030703120c05101a09160f020709020c0606010e031212060105280207060f0c060e120a0c060b04020a05031f081e0c 62
    0x181444210381c0305406881d122401c2c0360b5000740d881c0200404031200d13495100e44810740c03203440b030080400c800c032800c504191060180e82d60120b1a44116644840710702e19100c0c0d0801d040d508000040405851401104840802c1c800603420484110398a03142c0800d240880104201004806075008803000d20400c1c60401d055004001d5140300340e01c02d00458007a40c0e981c0000d5010390748002041441504210140030740341d40c219090601206084000d44110030960390900c1003401407074a503035020040e45000c50080d9004900f1112074040041000100c90810300c480c0d4a440800000400144a402c000040c4d151040c03280560802d241c0c0d803022440001611040c0103001040c3d111101c80c0101001039500e80ca0b4207000784a1411203881e1800401124240780702140d408440c0c01c0d0243d80104101a000d640c4901140d6200d0700c140c1e50101d0b43c1046001005c2c500b080b0703402407040c81c49a24600e0801a0403101c41da00602003100840d07070043c80000600c5844030b0369030024400da41d41c0c05454400c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 773255188 1250 773253938 773253961
    0x306060504140720030c070e0601020a020303030f0703090605130b0708242e021011070b040c0e070e04151202090a0b130c020118020906040e07091407090617 69
    0x200890040c864013429841503a24a040d40d02091051080d1b62041c0020080c0f07031600d510300f0768020f1090024040c80c40003500442d441c1c1c480180108110690b00c80000d141c14002d5001826158010750304100f10301d0581d40c40d030812012201c007075403500703900360000310f145100b512000c0c4110f07a00c8200c000303600ca8040c05010264a10700966034045040c1d0101c01c1d0311001013100464008851000c1c4d160709158490290500c43c010300747c3e0005505000c3c807451300c1a411401c44030800c0d481030f0188106e40c0d4500f0710382c0c0300501941000010750524818082450792001c100440b10703008541c20004040c0450b80b24282c1c035035070300ca200e00d41a035422101016281000f54a6804230392401c000c1515a145000036520904d0000e14200c03940d0b82e04c00074489942c0c24404e91039003101c0c045d1050150040b9800040140d8001002ea6204a803588884d40c070b1002c05204c01f10090221003c20b103d031442c09040c01d5942c8004403070440000396680800504030344112800244035005a0440542c0d49a2501c0c40300d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 773256438 1250 773255188 773255207
    0x6130903030207050a120f090b0a05180910050f03030403120f0c050106181a0d061a0406030803011d040308040803040f1e06050c131809020a0801050103060605041407 73
    0x1010305600f8040d84010035001c0c000c0d00c01c428451203181242c00c09450014020303140000c002410000e5142c02444054016011581c4050030360400720345400c00c0c1b104140051003403521140e0032482640911000406080700b90003600c0c4216a03c003410105001070507981d001e18400070782a100750b440d0700c9000500a500a81d44180310349004419104240c03115030a641ea00e84c0482054845600491003403589031103075608400c543c040040561000074001120b40790f121001921035a515030015149018181c2140340111700500f09002a5580e81000c8101c0e030802d2160301d09440d5440c1049403c0840c564846204a6140c0c40d5144c182c1c956880c4d00026800007001100c0c0341c00c07914024400320315040340e14080d818484040000d01c0d0380c28903080090383d078060312402600c403007400700d02094188aa11030090718000038640840e0348001c00200041d0100b100040d400814000c0003154402d81074104505903401120280400d640d41c0c1c040c4411035003001c0c409030107504040040b90b1803034031600340103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 773257688 1250 773256438 773256443
    0x30601120309050607050a0302061003031710230f010306030305040b090f042409050603070603050919080408060f010513090f051b15120103030f0908030a08041a061309 74
    0x10000681c40360f02140003948680410b5070301c4d5000304195020140d04005d03641c3c0c0010304080d072180c05841c4d0790b000b42460b0200c100c0c45c0c3c064448203001403845011101880020100035140c1542e00191a0080b1009543c0421890141040c4c414803c000c1d4080e0289400f204c0d410f543c0c0030b20381403038924198810381201c100b661b07103da050081c1088581d00c90140d4020f00b81048062400d0f400194490003e80702c403640280001800d042c100031440da000301c0c60364120b038020300340403810b030b60b60241e030343c0c00d0081418011102c2e0040c041d8650a0041040c044c2c000d40705902c01300c96203a22803807900071040700244201c039403154504a00c100203140701d41200303c01d030b8818520400e9121590740c459060141d400c005a2101001b240322444ca442d1200280002c403084021039840c00c030a6011024041c00140009424810b8a11700c0c1d0100520034220340d80200865419a41c030303241c11210003480202e01391419a00c038601c070740c03c8100d249448103100f0b009205c010400c1c600030a000c86102c0140c040000103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 773258938 1250 773257688 773257697
    0x71112100203010f090e0f0615010203160c0e0a06150e01121d100e030702190f09140a05060136030f030f02060f061e040903030c030b0f0306011203 65
    0x201200d4000365010b4802003c1c0700e1161801c141d603001c1140c9030030021076820383c0a0708050300081000301e82e85400120504408509000000050b4078603c04c0c0d0780803844003e4550791420503c041505040107842035048408280d855000b00380080c0d90760760061038004040300c1d20b0309035494024149d1102d07048060402c19900d8003500d850f001280e807884503680000111040012109a041c4224044068410300800607400440d0340c41e941d138010008001d015605d40b00da4881800951603500009140c250b144080c09611001440064070952130402e129401c01e40229601030454000e04c0e10420040c0e440c0000e0380c102c0005102200c1031214279000f0507606003010b64418800b0030284018501030074008110120070301d40103200d640d041030410115000348041c44000071801c05c950b50008011100104001041000341c00c1c030b076464401d040d52040c60b0868480406805401618050400d038904000d1040d48505012550303007401086641604041f005001c100786031400c141d4001d003c1d190 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 773260188 1250 773258938 773258953
    0x30c1207060e06101701090803010e060a0e04080a02010524190503030706060503070f0513090206190c210512130c1206050c0f03040f03021f06050114071112 69
    0x45410031005880800e144c2081440520a14480c4001c0c504a00c550300c0c0200042c203501c1d254100240018024440d030343c0c40040102c0e0303003030307841030b456101401150310910241d00b010300d05900f003544012071140240d420140090a21051640310806180b000c00082c45100b5400d410011580c4c0d002103054000e0328940e01c04152928100702411080784200720000d100c2e0308100400d8905101c43c0e1240500d484860014000e684440782c03000b01c2c0b0185003001141440940c1b00003000c50048d5642e481c20020708030402c072102584180c921000602a10202c6011b480070001c8030075100d001070403940803036010050a13442854020309070750701a040f82d000300049905581c9092111a480c1d0000030782110060030b00d000c1c4034082c401c00760884562000681b900307850010401d602e0200504c041c1c08000f05264000900d40203100e0303031080e04081a44100c140300303205140e5008155038083c80317000031f0054601c0c090350020702085418480d00210700314450700c00802045010b00d90070014142e540035840 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 773261438 1250 773260188 773260211
    0x5040e1b0d0c35030c16141e060a1205090c1c031107300c1202060904060915080105090307062027061602132a030e030c120706 56
    0x381c01c812041003c041c41e40d42130902c400c2494000006031040e42500000d40801141d00c0c00004418014070079200710035090185803654940d0a400c003c83d941252002a41507955544201030390605490581c081210340c0700c03015200d03907645200540c0c641008001c1803402c031b52064525004400d40c440e1030b26440003031031404000c0c00d281c050751100860803003e035440030110802c01c030807000384282c03604c880740748000d0b030b40301e0134007076882c2d0f1240703803421181c5d080480255100e040445101c54400b600030311085170f0f1907100d980282418083c05460514195010808940c10300a403806904658015801e0001c1d689518004101c000802b400ca040c410b00440c0a000d180b401070940342902c100c0140d10903a90049100290b500c44a15500c141410810000c42400d100160380c43c45806443c4183c1080902c03000100601090109107102203240002004909561311280c50080c2075940030302042c0d5400398001d40d80c1c02210a40e03100c0c0c0d0403a041d00c8074002007030805058020301405002c9000380c80c0d072 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 773262688 1250 773261438 773261519
    0x150706090f110306070504050607061d1f06050a090e011d0c1906050d050a0f0e0601080106050603012103170708160801060219050705040e1b0d0c 64
    0x184011500c8000d00088101440151080b610000d407066029028515000301d004000d8402c50003258425040482c4c001d041c885591f1043e035181611305c04c0003442c94104141c2c10b80d5410a10070b1a0448600404180d40c481d0080c000c0104442c8040c05003040c603410440354a004e4580400c10b044250760b1100c580000d07404010030003213400d410304050083c08106800344910a0030f0035141c5019896a94002c1088591203070441d030030544a45030018082d00c42d02d11041c003038140d89122028040c107052555000c15000f0902604031800c0d00001c00c01141d0710800d0000c20702092050284002d0f846204007040102d06118901c200d02c40d02d01550510038120940120308006c0d980703100069101c0040241c09a02e600c2c185107019a242441440c40d0b1504030000d40d1642021055592800114694002c2003401c101d41c0d009444010018445103541c20781c203503928800150078040908507003209030542d081240458800c1a000b2440c00542c504010320302ca04806d041000080301001d294a01d211022003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 773263938 1250 773262688 773262701
    0x309012a0c0f240605040203060603190e0303090d080112020a120f08030c070b07030902030d141b010507080c090d02012d02060601020f010605180403090305070905040c0905070e150706 81
    0x5070120f01824100d0406003000720360907a041039002d544100280041590b542c82542d50200c5001c44109141c80f1b46031170003010301002140c02065200100c107001d0301c2840440c2e8200d00c0d502076500e401c40c0d607a890845014120b459a00a5040200d0380340500c40e004d116200c04080034040c0c0c200b0322802a05541e83c0c541688219940803900601254107410030100e40029500061541b9090112825a40002e501c40d4181c6c0105000d1003a00240819004a40415211011100b502e12043d1507024010301e4081c080403200440099219400500c10b07a180105035440340802405130b80d00c92008d540103650f48003500080c005c481c00f6030342d038004142e05800700381d680c8810303958090099030901c140060300e0410310840c03900083e410f000c1e0900c020303116a020109200d6480c0e100c8241a26030341802e8502c54020740001d000e038029902c000c50201890380066001d20b2255010000c050740e070302c11000031510242c88000004060140050007072078200e801c82c8000310324100e82840c01d44142d039514106c0d241c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 773265188 1250 773263938 773263973
    0x1305191b0602010507090e0604060812090102010605090f07031d0d0e1e0303091e0627101d043e03040302060106120605090405030309012a0c0f 63
    0x51000e1041114040088014540d030300081c071a604203c030b4080e00e54401400b071040206c03024000200c541c0c1e81c0c0c0d0480e100800c4504140e415481d05043c44c00e2951b400202054090f40c00c0041c0083c450512041e030b24401e011907240a002030322071130030481c05054925900100f1030383d06248101e417070109103c001d94584440d00d440002a00c40c03800d0146031480202108242110514411080c0e1804412100400000c54a80c6841c01c4200c2304400142e164240094202501050866210154a4851000c0c8401c1c0b007903165448680e008001c002051003000c2c00c0080d4104072000b102c01c50340034594a0b05c0c0c1009002280000d03150703001d07280c28082000c0320721045202034489002854a4401d1400c1c07052690f01161440ca000e84001c5e645284c107201d4002000340500380602c11911950003880581401400302d03403d4203003410255504d03001a01c040c1465440d082c401c00d4001d40c0d8903444074854607500c070304081c1501ca8500650341610003200030741d0600e82c00c0b607014000494007014030b1658074 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 773266438 1250 773265188 773265203
    0x30c030e061c0609200c0a060509100f0504020105070b060a09050a060618080331090203090c03070602071202010c0b09030c070909020d06020d0912020c010f02070b03130519 76
    0x164400703440e0281e011041c502c1c81c0000815603011601000300b900145c100c03900740d0b9501480c403a0b503e0020340c206d020f040309280200380b05a4610102d0900792101565000340840c2c2c89002c0f840781251015075000340810410000faa001901c1d60403038070f038014002045104196620700c0f05070140c6a003102c148440640e124820311000b60000c440444600c05c000005c00610b0a000406039680701d030301941c041c1303850185498030f00f014051640e03003110100c4040c1341200703e40c0e82c03510300c01a401c00d1b200b582d0036026401d50b070354407402c00180000c01c40d42e0342d40c000c00120340782c4000900da41d002d0368401d030f040000c52054003020601068000d4040d074906401180d50740c07448524241840c1007608001c5441d8201840400581d841c5280010015080f18006a6955442d214600281401c100c020103c0d500d903225074200d6038020500081d20342d000e0300c40400d0825030810407030f2541c10a014041620009001140c079441c201512200b045208a04441402d68814209512080f0003101243c852 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 773267688 1250 773266438 773266477
    0x510030e010923030f0a140403120c110619030c02031201150e0603070e090c07050d0309060b040b03030f0304031116051807021c1404060503010f0b070f030c030e06 72
    0x41e82e03403d2409111038055400e0084c2461000381d1441964a14800c1180c248110010045007100f194015540404802a07030020b081c0080e06000000c04140c40c1040312030f020100310708011041340c00d00c03071405294039030307607010090300750002d0641c800c400d401c5203c24130803841900c2110303950314003a00c481c2c42c510f401444141d03030003003c80001c1168140500343c20310500c0710581d0054412044040101c4d40c0a4103035481d001c001c0c41d41d000e80000030300184105888410000d402d5030003004500e0044405020b080d00324003e20060b55580d00d1007d815a000700040ca031442042c001440d0894441d2810498100301601c2e141d1a004003004024510111400d0400030352074404001e541407017201c440c40a0900d0560006521459003150b031a445c505254540080217106000903661341800e4481c25032a1903e948000f01503810074054501d45070318003100031828044d0030ac103450401e54481e09018283d07005035000c44401110308011001c0c401c160701411002d60b00c0750094150321541c00040c2c00135 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 773268938 1250 773267688 773267723
    0x21005010e070c140c1e1507020a0608090c102001152c2502151f0b04080d032901180305070e071e1b030e03060c1b06100510030e0109 59
    0x101e00307c24200d02000404102c61001600c03204914070407590305003007115480d61000c0c60581000101e22441354041550a007100b899900202c585d1401d4203250303c180402d2074440412800c071400e58081115a841880c02001170400d82e16000d000304a15014184540280385030300d01e0440c07030541c0c0d050540c5202c00d241030b40c0c1204286081030002024801400c40d100414400500070002801e030120f01c0401d050301c0300e0529204e9034500d0080038140a1165100e135614821a12104a0150b02c170009041901d4400001c0790020700307414095202001c0500356040c40d0054500d102101d0001c2071034129500e0000100f04144005402440605002c014601e041e08006080001c03a4034140203510003400c01c1d03128558170075800ba016520458072003940707480e83c0c201a40d03141d030b6800402c0c0c0d1600c903031420481e0100c900b501401c03101042c1c0000b00408800749180544a4104980550040781c09600c2042a4030380f08071205104c0c40390381400074810070621012400c3d160507038010380b4004000c60000c001d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 773270188 1250 773268938 773268949
    0x40c0c05100218120a0f030f0f051c0e1513020f1c0b06041815050c040b07080f120f010e010f08120c010b0d03021005010e070c140c1e 59
    0x1c0003200110328181c1c00321004042203545500140c0641c0040618a01c1c03582c080000440864122105075692000703403174010000303018022418002a03a10b0b580403402030184003603030005907260610442503044003403034034000c0c0100c220b146920b00c240660344814200e81032445000d01c0031002e00030350f84d04242c01404015440448014040d0440c01c03045a8072259a50700356542a13448000c1d03042580b03401c40014041c2c1200003e1004100d86e42c00710408200b48480c04480329080454280b149995030000c821071400f55214600c8034032800c000102c0003030011340080c800d003d00c03d8107060030880c149800004108040f18644485044280140548999100ba6900415403009800d8450b4108907800c0d480780500341c80055000800329480030380c00c3c07081d008091710100183c0048400001818002d65481c11025941a114176043c00400c0700000f2002c050b210300710988640120f03510320313a1410b8200424845010740760007100c4c1900010b50310f68000b1182d828030f06280000c1d802c1c2c0d4508005 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 773271438 1250 773270188 773270203
    0x3042a060207091512020d0227190b0d0f0302031b030c01150554060306060d0803072a0203060f040c05060c121303060518101a040c0c05 60
    0x100e01e2001920f0400504102200f14032a01b0b43c140c41c070340e49060140c17000c2900c110101140c944810300c885060141803038040c3c0c2d09803048007140071a0001070020307050030f81241da096074170540260b10601c821010500c0c0c0e80b6401744a5100380704492500d540742d90309601c00c00020465107081c3e0000180d0a00020090080c0e1302e441c3c204604043d001c5203040c00240b1904440c030001c8080b154000410300000140040c00305400e11100b2055042601c0c2411504200549a042c0c0c04614900c0d17010030024100011401e11448010344104074a00b0350340c8458002d0b40001b400701c420807444503012100350700701801e0007160390101000d188640c0810320406041010040421000002c1c24081001090305003a50360b080320011761302c050f41c0b8000036000508188180f2100c4640c003100041143d5401e019404410031640289020411615a0310507800c09803041a0220000c0c1d201c240015135180155024000c01400d021034011600740301d1009c5002d4541540e0f84a000c21100c180c1901400320912020 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 773272688 1250 773271438 773271461
    0x5070e0f040c020c010c031704110a170601120618050607120b03030708210f010f090905121602120d020705030d0f03020d02091e0a050f010503042a06020709 69
    0x748500e403408800203540322241403c04e4100a69103802605050042c460482d100f6081d180080c0540341600703042c90400310b030386401401440c540a0006014030801c0c0100100d2180da800340c50180d180000898540e50004c41c19a8a103540d070440002d0b4506c0b040c09560014400d002824a0340341110019240142c0f1002500d40142402035918060f5008400c55810070b5016914640b01d03c40c59140c1c3c0c600d5003a440b41c40d400e90001d4001c2c44011001b852595040b01c5800a04040403600c5111000c10344807603207801080d80d480700c1d6183c00c0a00e04280540742c0e080e00843e0b1000b01100540002e24541010541d00e445908400b1450489607810700c141d0f00545000c2d4020441400c850400400e070411043e544c5042640c04250601c22205a03012680c80e040d00810200c00c0700c4010b0b810900840d05035200900c10402d26100140c02e003841c00001c40c401e07205071145425592903440700c075480b60480181c0f030342d040310400301c08800c100c20441340000b8111039030092a100d801c00d50010200d406a941d030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 773273938 1250 773272688 773272691
    0xc01020d020a08070501020c161a0a050324060d05040213140f04050313080d020c010810031e0f120905030c090a15080106060c0302071706070503091005070e0f04 71
    0x42091003500040c8220300642c3c0119001c0ea140c266060080c0240038502c140041402910b440107515040c0004180c283c1d0a0358506131821504905170000d58403842e42140042042400002c1035500c41001c2038903d03075801d50908141c1c5c1e0b0210005003865200c0d40d4245030707007a07030340b4140700039414921800b100260400b04200001001c6080404a4180007451030303880100940000d4100441032080d20342c50303551903030f0466107280c0720001b00e9100d20040ca200001440f030080d40c1401c0e5886030344c200e40240d00005071074104500f140c86050107441050300600455601d180010700048100c604c07072030300501540005581a5a00c0c400a060f41a1940094880d901104403480940d036240c01c2c041e0007010203000080c40a01e15052a0824521540f0001d042e5203030840000300c4940000340c0190852180c1d0170b035840705032244592036554540e280d000d15154040000120224014801150000700d140100c0d000100c00d01388100a0707800072580d08000401c2d5004442090900017405001500c04440 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 773275188 1250 773273938 773273953
    0x203070b0d15030b1602070f0e0108010c0201150501030c0504030219030b09070e0a051e090d090f080703030e0303041809060e06072a020a0f150219060906060503030a0906020c0102 79
    0x100d1024000001c0c200c0c07602c01941080c0390300703898020010355009092300301c00144c06c561303030b41c00f0f403040c4a400b4410b0b101c02d0350900c0c103115040361040c440c0d82c40d114412600c031800346081038011001400005071000600c0300c20032001c005a42d921003440201b602603240351900038110b160000401c140030305444815403062030248464080c0903001a40011074501c009043d94401c0c0300040700c44001c075200644c00c1160001e01c0110f00c8080703002d09270000f00c1e0b1142e03c40780b279a5000c1c030041c03030540b4850f031001030704120018000a4840d50032404510002001c032400c00780c03103d03d9903d07940f85c486416902c242d40d0b0340344074007082000c0c003422103226000343c041c1c91680b031f2065024115060782c3c0c1924030080d045102580c010000d01c0b410410701a000380c00c81c074005441c0d1003100c14031840e46c01030b548060514401903207540d10000d403501c813010440310041d02c80c0445641c0d0703c020302055581110450385038103001c505600c0c1000070303100c25441d07951040c4060740380c280301904004481c00340c1811508800e2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 773276438 1250 773275188 773275193
    0x6030c010f110f03161e4b051b010503190209090c09030601140f121f0f05090601030f1709061801090b040b0f0706090203010e0f0d03092001020a0203070b0d1503 71
    0x4100d62a0a8001d038084094401c003000f0003481c4251207e03501e01c08180305220020400300c0c001000746075200b00e0440d0b450b4007140c07070200f0100240c4041140007131003c0000500340031001503202207209540713801600b450b102400240b88020100c0b8042c0d054000402c1e04003da103420440c41d4010400f01d0740c02c4001c44000c030042030400c88162001c9000e00b06241e030741d4490840030801008000321102801132412610f4040d1006485000d02c1e4150705806c0c980456880240416901d04a0b0b50110080d10228890760710094121044501a403941d001170103150b0075900d91100600c2c407000700d0703100c1c90804801c40001618035491074120103103890060000384000e0482da0205c6084141c699821a100d5400e460000080c044c1107500a4065003400d040d024820400202507480c0080c200903201d005100080c22411203101640107070070003e141d2045904401282604c107a0410306105407901142d554001c64540900d03a07000039a4000002101503880030144200c110107005181e1240e04645581c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 773277688 1250 773276438 773276453
    0xa06060e01050702010f0909050a02180f011718030430030921140313170d0807020a0606030c15110709020f120405031206030c010f110f03161e 63
    0x83e44020f040c0501e141d030480c030140c0103401010081003825001d02c0703146003494800000c3d42040d00e803608640e210141520051801c1b04402144150694a00d11220713150011803560b598064090311502181c10441c0c20b405c1d40506c010030140402d402145030f07550050030015038440c261584160403044040d0540700007903210380d8950403616100e0171010007610b050240402c9848644000300006551110511410400300142050300b41d460004030000d0b40d0f039040001420801d0400c0710040d0003098988150a00610000b80c00c4030440c03040302c084481c00e694402c00ca50941e0400c1e0b8002c044054200101c640e528071345002144507140c40e00001d44030441d2256148090300410405540100e4501c0c882c510000684070041651800300d5501d08180c10503684a622217000000c90f11040d80c0000d01900f80011b070380c0610041a0754604c101184000d00b08e550300070840050b61640107003c4800006078080002c1c0003076a442c040d00c483c40e17941500e801580c100f52981800b00c04058611244041084c2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 773278938 1250 773277688 773277697
    0x61e0d0303110d0f060e060d030813030e060c01062606011502120706090501140103050a150f020a171b0d0e124003060b04020c12030a06060e0105 64
    0xd07080208000640a080030940e000300c90010b91804d15080300132800250a07007008003185e0340c4e950f1540b680d88504050206074032601e0405800308501c0d6010402444d40c2540c4100742034001d00d007803c0c111008000140240d40328602c03480040e03440e44000e0040344680391018100303e0385101d914056482c980c044a0701d444c41417185101d001c10140580c1e214900903c0f5100c0e41e05a19102e5076980c00c01481e20400600c2c80100c190340340d41c604801d209600f1014014981039039004401480300049660f505122094481a50301405072180040c1050b82481e0000c2c0590076002d4554070100c40d48001888801200280141000c880b4043c02403181d5a00804039020b180c800040820140030440009141028143d4900c0b400742d0002250070400c3e000020b8030440d82c00000c8448040c01501341d0b402c0c000103883e4070f500c034024852101007000401c0d650040561402c0600302500f04402c00502c6810940b04511403074801200004002044189210340d001420b000c0c1015494030100d800020300030f014 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 773280188 1250 773278938 773278943
    0x509210309011404080c06011e0b13090e010b0f0415061b02031204050306070e060a1b050102030109141006020736020a030605060c12130b03010b03061e0d 68
    0x20004007080c1d41030402e4014603c030900080c0301032a142014074103101180d00509040d00c1c94082c8100104845032921360781c11090814007aa510680d050403541c01c92a8402c0c0c46c00c8001e4039030b010000039141a035001e22070300051000b00003e46c031a00d1105010010000c449110720503031030406100942d001030130311001511002d02e000e4002201034405650702045180001e90305216404084040c5142d8000030010b4402c241c09403002c946070040d084e5040c94048510592002040c400f201c20035100e00d24096545005205580b001c40c520703190103089034000e07000324140c1030300c0b40c0c80056118407403558507410600d001518140c0d00c2c9013003002500c4614600540402c9213100c0c0200c514180f140e408200a070140a03500d080102d4100c40c5880250720041c40c010100f401d1483c0080ca9190030b03801e075609440d1590240c0790105071058420860b0380151040e05050304568808240e460758035016501919042c03e00c113a480c240282088030b15412864645001004a03070403640548442860207046a0f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 773281438 1250 773280188 773280253
    0x140a0618110417070b130303030e030c15190e070801110715090303141303020f032a0a08130e0f0115030b0105040909081905092202040f060806040509 66
    0x44200d02c3c0a8240b0480b54441c202e02c0300040740c06007800319a00d15000844e48281c4081020000e9101c406807213004140f1015401d8101a003849140064608490350150021013407c2440d020318000c00201ca0071a02000c0e065404841d043c040100c0034442c64000e90028200705003800116516404090081c00307810f0400d0340c80718181020140241c20043e88020020307000e880f00d19006020b00307540d031a441c0d41540148204855071007060800f200310741e00354505108000320703075100c21940c1d0f0141c1a09595804688030f10b0400d900800e040e20702034140d0758140559034000034540340007c00a03030406411501009444001000500204402496641281e040c0803540708860320043c0e03114001e03940447c2c0d0031418520668100300382c0344010084040c82c0401d0100241c2c5410040341e0340e0181c1c40305180c0003481c020b407168201c101403d20081460004802500d4951545070445018005074042d101140560041c000c41e850701d0300450398400c403a08014140440d00d4842c001c4005003010b030035088203 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 773282688 1250 773281438 773281469
    0x9060b0f0f040f030b16080903180d0f080d060803090622080106121a040b04020d05100c0507031704020906010e0307030c0b0a0207060e010215070201140a06181104 72
    0x18001000340c40083c80390b901e00c22100c9640341015400e41c10210740030300ca101c0201c080700000501940310140100107000c0190300300000710701180d0034908050b0100d0307446a800200e1400180d101207009010f0352207450b400c0d45648407111240141c17411600b00c800e254005220100d2140c44071019502250600189914103a0700c4103841c1d90201d41c943c10491b115402c0c110045415200b00441604451090100842d4036076070800c5110382c4081510f0007418074405001040241c5852115034001c2c0d030003001907481c00c501d51101c0c102141c05900424020410225095092641086401b52503c10b60204401d00745040d9000a0480d000141803034180004800c08508503241008510081c59000400d40030464440850355426080445610010301c907030b00000c0750492240101c0d850009043c0c0007421131440500c003502e216000200101c0c00c540d41c81d0014100011f10403111402444099000104517091009076400032060000c0b0b175280a0038810110715201c0304070229002c44180140340c0240 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 773283938 1250 773282688 773282707
    0x15040e0c090f120d09050f060901031d010e0601030b01080a030f0302030c070c0b090406171005070309210306090606020319020c21010b0103051e06010323040c09060b0f 74
    0x404410b8401d042d040400c58000144035007000442e00e115181c01e864034055140e0f1001080751100d0f0b046d51187d00100e092000640d154020340001c442103520480c4c41c903c122806d06480c2c21221040003060341a4442d00041052084040540307001d80000342c0945029807064402920482c3c400310814109940000001c1c10b0002447c107403090154407005400f0b00903940c5400c54455080940b2041c4250316050002074040220288040a600d446000d080b001c0c442c09910030003070000504034010715484007040400511030312002e0030b9104201031009074024840038000c00305c401d5074104c070320818542801030104a800005540030240014455074010a0041007203080468076a94980c1103400001c00c0075409071043c0c1003c01b000400402001490700305030044003900e0741a6400c0e031007040b01c810360407445a0000281603100f2018100400d03007000b034140ca100307a0301c4900c030b82c411304c0081c0c00705000422103c112064000c20b13001c0d800b4040c0300d042140507022407107a0401a090401c001901030103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 773285188 1250 773283938 773283949
    0xf02090319020114040305010b130902011b0303090c0e0a0b0a06091e091401060e030319051e041401030b04110a1d19030510061a07080d05040c0515040e0c09 69
    0x3c502c1042c4c1c059074031030390790746000e5000e00800801948030b00d5101c0309412501815114140041d40c05a540d52040d0b22031448045125800040940030561100b00c5080401c5008885400401014681400d68034042e0451004c0382d00c002c01d03081c803d90720340324104202540074005106840450207600c0c0440000003000d5a00140f0703600210001d4140088100c0c11038040f052a4103e98668988005503500ba01c10035850b07201c0d055084401e000050b442c004168403420283c8150404066415285c0750f4264243e07041382c01a5112010040a40f00040e44c5175a06014800000c6001d07101031105e1214203030a00b1560149028400c01c01c00c610842c03941e129031002d040c0141d82800340082441e05058455800b010016000648140c8a41c60030303500c074002e0a1003080200c3d100c0e502c1c000100c016102ca40b01856103d4841598150740502c1f030030110700620b10900d40924400c061500d0381e6440c020500c180718080c027100a00d4440c09000400c001a00740841d5580621841170040c3d0ba019000e00296 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 773286438 1250 773285188 773285207
    0x30905010c0c050f010504031e1116060e0303030411010f0216080a0c08160b09040608060f040c05010f0c0f03300506061e030603070e040c0303030f020903190201 71
    0x804a41c2400039280d852500031070354803041c90040094034010300355003800f242030380c0c4c00703981c020001a220b85c5003c1c401580e14108040900b8580383c01e07141c20080e4003000707282801e401500c81c14041881e8080090320b40066512000d42c0b07082d4080c60551526840700001800300111142c10700c1002c104c0a401d2070310a2102c006458084020628103648850513155990b04501045070024814440804d024a0000315150a66400c0005101e103600307004400207150070039212250010785888003c101c80780c05010b607611501c903407401a0160f1805040c54410707000360ba401141402280d51142c0b0074244d201e03440c158115040340c0d030401c04502d04e290440f084541203511404801c0d840f40016022400403c5403000c048403d05c0c02e0000ea16040204030b21486521401c80c0400d0051280e02c0400c0030700f0025503803120008041c0d54209070303104c1c0055a081022901254415200c090500030580c00d88103040c40300b4400541141002d42050103c0d90702c990004064000c0084030300a0802c40e8403d81e07204 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 773287688 1250 773286438 773286443
    0x504030c020d12080a0207230304091e0b010302070206031819060912090803040e152e08011202090a06091a010801080c03030304080a09050402120f061518010309 71
    0x4950701c4402c3c1482c04010208201d200002480d040110703214299130300943d201541c000c0c01c0207880d200602844406184000c07034550720b07400140000500d901880c46801c04080c804004071107625103251103130341180c1c0d0390201c0d00d06051040c0108000760321100300740c81d40310008882022483c009500e02c03034070f4241240301400007103001e20040d404001c9190007a03401144625600903883d1a418400d49201c0c680380a82b0392558000c0c03004000c2038482070380003078002c00e4100a01c00c40411540c003207020100b0308041010088a01241c014a0480401590311010350740e1401480a5040200d5a11600030aa00c003911400c8018017240c014282c59100000030010310404100142e1840d404003034070718800d10902c1c0801d160710000101c1a80c0800c4200705801c000b4095071035696181d407100c0b8503030003140036a03007001f015020104203030301c03244002d005240c08150801a141381030307a20380300a80d10040a13140520500030301910300d0f030074450070b5030012001c10800b180031014450049004100d400301c003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 773288938 1250 773287688 773287699
    0x2d0e09010f0915050f090d0c0309080706080601091e06030207080c010f0f0c02060411060717030c1b0d09061d040906020a2705040b0d050f0c0405070c150504030c02 72
    0x9400411014050b0079501c0560303a581403007135944450f040ca02c090000c468441d4250072014042d55490b10031342c021400a4030a0034410041512107580324540a03c603048800030032211428016650f81140c400801000c1030003a0307025000788008203030200600e03846039005168000c02c030002081b90b44e200703580565981000030852450481c08a2000c0c0c040c40319a030175128517245001b540b00d4030118541c3e10858020215001c0799901c1c5091000981c4101010789801c910141c10103076400ca4070004500420042c030b0901c0d00d9011403260451164445103508500f5441190440c14803900f10600608807405414442c50b0360020b0960300500c1d004440791294010702c5c10b246441007110550142c0329070001c90740c90100541c004000f04100c0c0040c0c101040b42d1610900041007070f842c10760450451080080d000d0400490566640341c50450f0a50025966411070b030205401400d19101c3d056006600340b4104124041c2d07500e40e2103903c9103804415210f00d840300001024036002d89001034049078082c10 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 773290188 1250 773288938 773288951
    0x20108071218060b0a030f0f1407030b22120309030504090612120203040e04060c0e04050c031e13140a0507080a0506070e1e03010e0d092d0e09010f 65
    0x2c4911104800c00c200302d07041e42c41c1074044409420710a00110560317901220107040c03105161203009a911130000100c03079501808542c0307132028200740580c3c00110311401e0300251500b4400c00c40404041e01601940804d25507543d01e4001c143c44100c040c2050b400e60400160b1550395040490b0301303201d0b0390002102507080c1400040c1c04c40e0007000100309103001d5600d449070360901c41e800700c5c1c0324451b9215640c05650340c00c01140100b001c0c0d030710584a40b2814100405410340d00380101d800d5031401ca4080965031004810442403c075000c0000307904480d0781c25000020714001c0d40c18521110b940102070098002c03481c840307500810800403803041e40c1d0040c04aa80541d541d000300c80d6540c1c5c03042802c4405000340700c08102c025010351580c80004400510172a02e41340c0c440c000e488040d001031842c507171540d00c0f81c000b800b160320107021100c5d0001b2990f03200490329040050704000f880b05803d03094000c1000fa000a0005244a6403c000380c9050b446203034015241c14001c82c2c00341c01415800c001c528038041 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 773291438 1250 773290188 773290211
    0x90204150501080c03072c180103020906030744010518030f0702040b040906111305090402091503161e05010c0302060c090d060e070518090a0201080712 67
    0xd40c0302214000d0366410440d40d10040d01640900040c0c80c00030200c0c620065180448208003ca59a09a8080a5098102c2036600003811594091540303c1211048034018000c0d401c0007030035590321010580060221030300e40032400b446005510241483d0511341c10b43c15182000c1008603402e20b000c40751840110800c08080c240c000c0c0303415100401c105401074208100341e4008001d0360340000c94407084901b400c0d90364080c000905501d80e4500d40c081e95500b40440058100d20071620540b175507070240c903150000b8034122400030425802c074510a104100412005a840720145a480188420807061100c5100d000c00e1074010741001c03900f0801036103400402c1340c030b8661051140c0005420080500b5650743ea00540c0c54041c1c0d540c003c1c0040e00a4070000e0b0349510700500800c1105030241c030b000d034407811030384641040ba608001c191070a9003000101301b006160440c0c1c0d01c45070382c0700007200c4807190401e06143d90f601c0d4040b18000781400100300015482178024100c0c45240c1c1c842040038002a41e285 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 773292688 1250 773291438 773291471
    0x133e12061801061d07030c0926061b030109021e0a120c0e01120c021204180507110715120f09021503280f110a0e09040f02090604090204 60
    0x2650000203601e8250001482c1c00790140e2101e0316200d8040344c03450783d1a4100304030080c02c11401d400741400780040740020340150b030020801582040d60780040502c680c0d4000c0c80d0901f0f0740a002c51a00440e003640302002a00350740210b90446543d414016600c03040840c001c1c400c01005100b40702c1d01d01c00803451124090300072102c001050098403040080904105c82914010040ca01d02c0380004d81007050304048200d02d5010511100240c01100c40600c00c0c80310aa101d94844c0d00100018074403c04800002d4855018090304000036003825000d8070400d9581d01c0d41d40103544950060b80a142c0380130300c6000d004014404a541c0c413948284443c0c1401c0c8502006080080c4049000b041138500346c01c0c5c00b80c1d140f400d8a024800c04219903041000c8150000d00301d401420389100d0031961005401040c80007441604403030494805150340340c0c1603044000e025501800c0c001406004004100701c00500b04540c2020100c0c2d04a030044580e80310741010800420080500030f410918000d010001d11100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 773293938 1250 773292688 773292721
    0xe1f1a0d150e0a180b060603040c05060d0903200307120c0b0a020306011b02010807180801380303030f1801090b1803040311120a05010203133e1206 65
    0x410f0040c0281c031075101c0291425a001d01002e07250302d805201268072454224001d40d0400e0051065082e40e5496a0000784141e02c04400100c0b1181d41d090003504041c0c0002c05028500d520307158004c403684051900545078402c1f940c0013406a00444206007d4500a40100c5159504400c090245250140014000390710586245010400d20760b440740341410301d408940400c1d60b040c2d5602c081d80d101d52400f0b807605154520f42200540003110301191814091081306030035283c0c2c209d200055a80401106916240d04243c0d940e41c41d41c0c3d110905181e00d0000071a074000726010440892641c400703401c0504583c0344503003001c05500744070700d142c02d005000f05218005d400c80740d2500305003100034030700c10382c0c91007140305c000d29580400400184a00c0c0ca628076003805020718056940041076543d41c4d40c02c90b0302c22145041c079051654042c8003809141400d44882d60301102000104568204903203000031185d005101002050401c1030300d690319200348074004080c4210444000d41840345203010b9244c2ea = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 773295188 1250 773293938 773293951
    0x2120d0f050c070c0e0703020705030d0b09061c110a08100b09061804060917030108010624052d07050604021813060f0b0a0e1f1a0d150e 60
    0x2008082a1100118403c95040c180e104010004070f501e4144020b00808004142005140d800c2c8894004500280010701e50701403610000034800c1d02100130049640c3c80070b000a07010710040b540c68032044081c002c14520032138020349005809050b17100014208c0906070441c4a06019800d10010210300c1500401070b4007504660b90109a6504002c1c80984200f140c004014403540302c0c046030210715294040d504035801160000104401e100e04400c16502c00c0e40001441d079503d0400300040800800542404030318071088501e0700e801e542d0001c000303006a000c4804144840e041a40e100e49248459050003d0000c003910f45580490800c0c5480702c1080b030f4164000d40c480405013041c10448080584191001180f640f40406c088d02e504008210180c1840c102c3c2d07588011103150342da600d04040000300f404480107001031401c681c003004000d6a14800c10264491080e0501124001d00350b052464411005101c0d10b502d03200d003122029000410300c07001d0390910440d011500100c0310390110301c02c48 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 773296438 1250 773295188 773295191
    0x61509150d061805091209060909040602160b010303080f040b0604051f080d02060a0204050a060c08090306011203030c0c1119030804121202060103050a06050c0d0507030b040b03191202120d0f 84
    0xc0c21b00a1030000c1c0708040081d54403800c1000b0307140c0f59107000203006801c5406400d0060a003117981110300030201280c00c0503500c0d030040000401c01c065210380003a0340031840d0070b0002c44608062351030307555528000d01850b20464403100007500007a0003c0b03826141e1400081200000c079a200c0211340c0350b0100e803828400600039040000c500400500072a021158043d201d42c544e41e16000c0d04561200381e41c0750444050500300301c0d408460341d00700906406000c82d200800d0f46242c0d01d00d0040c088840f089690401c0c041c603126910041041d02d124410308441c191060103031150160200140390381190001001c006001c0b80108001c4e11919140100511a0000c1c41144181c11026a07030f8007001d02c0002c10641c840300041000070f80e83d8200d2034002c07250f45149810060340188a01c191607044072540300203542d6450541c030600e0f19015107504079005601600c04020b80d00100f50806101c80c001803e6038031400e4400c11050301c20010780c48011f0880345100e85034890b100080000d014001c0c1a0925103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 773297688 1250 773296438 773296453
    0x1b03050d1a030304140a08010c170106081623070f0302120c060c090f0301020c0c0a0909021305100e0c040302031203240102030918061509150d06180509 67
    0x2005400d190801901d004004500300340c54031000310460ba540700701d49900f040700004001256a02401010b008007169255080f4120001c040502d0a140503404001005242001d0240f680c04203000815100d03907529102407a0b207880d002c03603801d1110008250716807180004c1c00c03400b030224403100c0f00c036020711139400d50b40c00c0a04280c10000f140a0700255103a40d400c00380114100401840c0140381e508406070044a0038511440028220781000865600a400035010310150f45030214444c00900f02101e41003015062940100f008a10218001040c455944010900301d041c4031704400010301c0c200521034000d14055060541c160050700c82280244100400421007030781d031409a0340300710940e041d00a003500b14510040307540c5006038175580c15800208403403d800d46810001084c12020346915480d1410080d05001075a6a44400e0401c081814090200c1c0d9a90701d01f10004400340080c107290300c4000c0e400d1480010a01e0307074402e4110611340c1f510f0341a1304565400851207202d0900a90346039 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 773298938 1250 773297688 773297711
    0x40c0905060f040503240f04020112110a030f06060c080d060306060b0c010b0a060e1c060c230403030c0305030a1404210309030e1201060902030705070506090a020f040902011b03050d 80
    0x907184106c034402d207900c0385d80c4005400400112900380c0c0c4140149003885c014501b00070750304222101c0c10f0401d028004001000d10185d44c041c0660603013026203c0301042800d03e0020010302c01081c04800609013980040c9122580310f01e508030b00c1c0555004841002400d5507240c1c00078155002400c0c25040754200000c0500c0c51400075060780c03c0f5101c9031100210701f0380e400c04000050400b4800c48882c5282032100201060301c0d48541810f406035511251120000c04881c143d40090900b901c02c08000100030510000c0e40c0304403403005171541070070510b80300e803980c0524070064195022100041d1581c1e40411060005c03003108094000300d1850800a050350001c01201501c1240b28050007240e00b61032400c02c40d081a032107015840800c403000142880c0c517415000240d90082e100740c00026004110030040c007000348400d60b0842070302c5000b02044405a80840e42d2100501c060174800e039602e000a009690042421001030109074040020b907454038a000307401d81e0000c206611b42a40790105c20303001c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 773300188 1250 773298938 773298973
    0xe190504020d06090305311220031c0c140109120807200c18090a031409030d0c050d0302070203150a0b190608060a0311040c0905060f040503 62
    0x100e40103001c090203810741d03484403006018400d03412003c02008008010b02d07090f040100b0501b1f220058040b00040800c105042002441c86d0000d00d81c00722901c52020006807210402d000d90841b05d00140b24146200300082d0401c0500c0000c1d240c1020007081c03844941e644807600c035801030300c505031440138204003982580c2250b5084900802007e040f28043e20581c0c007800400764000740342d1410300802c0307404c1d075041c0c1e60388801c6a0400e01685c0c031030f2840c802c00b490b14052030254810015201400fa150000800c0c3d5140030241c40a03084c0291151080c000398217076401c940c1c85003005800c8070700503065944001d041000c01c1005441034003844083c0b0703081c540700f030080b644403035001402040c81030794070f90400c3d45124003d015503000c143c7c1c0b1045284103840b5082ca5112810b640c80c0e0000400b407911030050250500142000d1046008040900000780001c0c40001c0b43c440c20340d00010700d41080f00041c0d9042c9030641040e80c4c851004503006a91900398030081003078610a6064610f0794404660019 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 773301438 1250 773300188 773300191
    0xa0f12060b0306040504140d020f0111031e040501090c14010315150503130f03051b071a031b0c030d0f0903090b0f0f160b060108060105030a0c0302130e1905 69
    0x1024110810128025180c01c2c1c21043c1c006c1c0c001c43d920b500c2904c0c404810381c03404403124152809600320b4041d62840100038440d00b80d0f01000f200d00c1c180342d4a044c05011540009030031140809804500128080c80425071020340455808140110443c1d00c0d03080034503c803142c10380d240c0d0000f810f061002041010507200d030300803100300320005e00444005c0403058409030401000c1c09010b00040f2903420100e0700259800c00c0a0380a81c648540c0c40300d8580c1d03000c914102e141e600174070780d500034001004043e00b0242d18520900001c05001c0e102e495030b4501c007540c00004990340442010100e000c84000c41c001c0010724088500342c908020810352000138000352440e680c00034001c180403010030014005148018111203040208244c90300c0e090a03078008440d003040700091705508070120004100504c80944640000c1d09091071880c629103003000800c0752000604244d081d9854100304056903010350107540c0d80041041403003400d140c6905040e850140102c03400610130380303400380d8100c102c0028070919 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 773302688 1250 773301438 773301449
    0x121706030d0f21020316090e101505070b07050417060114010509010c080d09060c03090b180a0203151b1c020717070c0305010609020a080411150a0f1206 67
    0x10485501ea64055600d00e090703801c41d0034020f0b1021041c0d007100e012440114400c2e83c018500d190000102e140061400c00035420460f0f0240040c02403001c4440b4407040841200c1e4034804410141c04824403c4406002d03070040100290514020721101c1500100a441512070301621200084030142071250303903002c284103074066044804a0484030354440d600400114206040020702c04900355101c0034198886244500c651ba0781d0b4255408011003401030410864241c507080c840c0c0d10a94482500c42c00005d0014003144002403e070700f415542c1030062021072030b001400e4654024001c0c000700c0240d5000c031002091180708040c0c0d00c050700020015200341803d04541d650103d0200c00000e0f0082d40112000c3d19060030342140c25001011031ba0081003814414860072815602c1e40ca0954295980303900300100080c018841a00340541c40004d26074800d41060500b07010000510100301440c6d00309022038810380c0300090300701e400340e007010105108403020380da003c500d1100c140340e003011100307a409031 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 773303938 1250 773302688 773302697
    0x11d253501020a2f0f25030b180f0106082b020a260d0218090c1e1b0304170c0112020a110f010605180615070807121706030d 55
    0x21080c07003600e0301d4604041e22410300360801c042201c014141d24009220f000a11198400c00391240680800480c10446201e400c044403141b5045030303a01c418401c00241840d1110b0240c410000740e0310030410012a15515040007002060340703410089d034888050703078186000b0034140b42c03842c0e02610307000c000d4071040040b640c040c00201003183c1d80c4c0740401031950070059034020920207416404a6150003000c19079511140141d407001c54150700c0180e00d601c1c0040502c80c00c600300420800302c2d1080c2c00c42e5003c000100d43c98002102c420741e0703072500740281107003c40041701140080c22807013000402003064846844a6010ba52031460003540c2d039080b03084880e400201010340e100c81404294010740a00d103e41c1c1440f4a024040c40d0415290010700301034100160346440080049040180c90000108a07003105004980381000c00310300c0480c80c41c007031003080321000505201030281c40800d44030707001e501c1340c0d2581c044403200c0c0c0002e20340d00c3d04030148810b003540300380402da59140014481540e0302e101e849 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 773305188 1250 773303938 773303957
    0xb0702070326030c1b070b030115080108071e0b0403080705070f0312030207031b08130803031501050a12060801020d0b01170105040c0e030a06020309011d253501020a 73
    0x1124244d982200d0304200d196407051400501c1c41c0001c0c03243d00017070918a08000d46961400c07240510308890b50760060103000300310b401841200300108016082d1a40400009000d460307103001888081255800040c411202083c04410003588400800c80140104115014152910181d00341d803041488000c0008602e4100c41c02818040c2d00900840e9011781081140c010b00cac900040303642c010031201115000000030b050480a01000c04030405002410011800c500c1c1120003500c984401081460504c600480e1200c1d020b8421400c0600c1082952028042c03c0c1d510324455010703411000240d0045420501220700a52058001000041226508002903481d2009000061031048040410484131034080b072b94588042144400042c480c10340140e42c0d02d000e5000c03608407240304c10b20040345002c911090780403503c0040c8031491080070044880d90725115410b100d2800d14254000c0b000b00150652018111800040c6030500386929640c2e00c50161201c1601d600300d10483d110200032844c5642d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 773306438 1250 773305188 773305201
    0xc12050c1009121103010c030b030105101d09120703020a02010215071b03031d0a14070501050d0c0210061403120f2718041a070503070309020301090b070207032603 72
    0x51a00880c0f500400c1c5203510080c1c21000700b425a0500c88400f80840c0d1201210601403d0074802c0e940c1c092200e014070341c1c07000d04255030b000c0141c6c640c101c13030003100c01c4400201e50440300a01000d43c183c02e1b1001580d54803102c0f40380294850501200590140c0074409441200c0c0c40805203151003030100780d40d821070702d44011071040d0056000510036400c0503920519901180000281107100028510041c8030020f00e518000c081c400b2528200300f02900100010805640c10106407041c1070348484011501503500710b81240341c0b52031400c0811420382041e0b030025441c0381003d0b100e04040c80980642e43e81c1205501c00b144107115010320070b2000b5608002004c0301580b03a00c800450401c402c005a0505030740740c4001000482d0640f0701c0c1820500003024802081070110a110000000076103129081c680701a003d002400300806020a140c4c491410030b0441d039007036100011203940108004090704012000030354425031400210756441c0c2e5800b203003107407030074078240001c08042070a0914a140c0c1c404 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 773307688 1250 773306438 773306459
    0x3080a2003190e010617101a060705010b0a0902180108010501091716150807030e03030708270105100906080d0309081207023f090d0c12050c1009 64
    0x41c2c8914800560302c240b07945900c0c2c82030007400024100c01c61580314500040c4100d6007402c82c4514032040c450303d48101003080b03c0420f096159100c40441c0c1d0151201141c0c2442405440b418844ca41d010001500100303600950794040c0c0b00e54102d490004400d02d00140041d65602c0c07080c00b0745808a01d07141010410702c110350003007030101c80c5001d06440b8003141c1000c6858140100d500302d80c000c4082444900360042d03204d110140d0000702441c0500c0180c0c4c0c1c8010082e102c2c031028080c14100144440000c1602502c2e11010751100a01c2c04c2024803c50f521200500900e02510182002100312a0004080c455030043e2410303a07034454050034800030b80c000f040c0e00a1204640442e81d60700b09001511608000d00d0b0310b00e02c11010b81d0040d1901200c1c1754000c81e01c5001ca85195042042411102d001e5034291414801107008800680c1da6034030307040d100050f5814418000200980d40b07252001c9440c8400108505150784a141150803040c410010001e180c0c17007071928100003684c00b003000c0202c807411 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 773308938 1250 773307688 773307721
    0x2b0302011e1806050c0f0409091e03080f0c070f0507081902061b010b06120402100302070b0f04060b0d03021c021212060a05120d081810050411090403080a2003 70
    0x45c03a40451500d80c4549040a96410903840801640e03503038110181031200201c03c0d4044241d01610304d0002840a40d00540000405801c940c1d20507003d50000d1090524882102c140039000107140e8020880d82c60710301e6850165000c0c0c0c0f6080c0c0181c0c0c986207034003085951802e003c682c1c004e1440c0d04020707140100070140ea0001500d04c291b507403580d1250080780c480200402501a10a003100c9040c079050040c003601c1e41c10078901c0c0c001c141c4108040e03030100d807084950780e8019040b060309400c140c8a50605501505886410a41c024490000304003019000a102d43c01610298110400c40e58000002d0f62500c040b40065201c04204010b80c17038402204801040c4e111500910100c3c80700c1d240d0000c078411009a100034101e5901090715200041d4100c481c05510440d07400c0c0942408800c40c0c4440d0b10f51510240e10340b00c0e15101c4004c1810401c686025500c0b4000240105a0500e82800c0042410000f50340050482d4504095500d00f913030348170300c2e9002283e8400c58103841c507100d280c94a80266503 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 773310188 1250 773308938 773308951
    0x4050c070b060406051002070e070516020f01351302010c021210090303020306190f150c17091806010906080403120e0d020c041404022b0302011e180605 67
    0x1510400800c460b46e03031250a065000d81e44c1d00410f0038a0800c075518040500c0580b2603414048140410b1081180c1100e0324003260368191020b4040954440041e1a00081c8c080e000d81c1d126825480f18021000d06040380c0c1080b00380310000621030f00e5000345004c0c3c014035400040d0000d40e100600401505015015005100100044901015255150320100c482d1458118002500003092140b40e01d0306006010342043e0103d401807045107404100100424180f06010320990214140b03074045008201c4400e03d06d4009500340e40213040c007586500c00307903c441070346889141c0300341309252140180411244598010f8585600d024108034081e600301000500440800080d10a41d12101103980904103c200c0c0c10f0009008000107500c0180c14050132401c085c0c000ca113030601250300600022803540e00160144d50070f95a8034400280a1a000544882030711150300782503c1108041c2e0540c4004d40c21281c400038070025550030ba040b82e0540e000300d00c18100065a11440c0008158540d1000d030700004d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 773311438 1250 773310188 773310191
    0x61b1704080102072f0112180206040b041a030f0a02300609130b130501091b06032901112a03071d0c0c0c040f0f060504050c070b0604 59
    0x7a910100d05080e40c1c03007035004030fa0071129804885010b010303604200f60381c5039000b800060000800300000308844650000c2954141d2125220042c0e007601036050110f1030f4001d010a0307540d60300c8038049a440d40c00380c0b048694501441041052914600d401d8900a50b0514908032541e00d829030807801075001103401c158a032090041c01d0148484ca10a030141c02ca000720a0700085190032010071010300360040661600c203a2054280300081c00945a46600c07003820400b5101d062014180b550060424250080040c1a0015511301c280720740c200d0042105c201d5503007880f00c0601040d860341322460031815006150b8841d2403503003a0f5030207901e48180c12052003080b0f03a589140410301800c00c003c112120039203203032007074008111814103000c418094085071020140301ca910b20540b0640f4078001f404140c1409020410321902441030115900384600248184105a01d0380e084900034030034255080005850058001100d003803a00806100d441000022820031015480d070314203880e0003c01e010f5119 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 773312688 1250 773311438 773311447
    0x2030909090105040201021b06040512030409020a02030c061e070e0d1e0516030201080f07050403051f180809061b0105010b031008120f0d140901020c07061b17 70
    0x152603500340140305070402000450a0309141c0006410a16401002d15503010a60711440481c0c81d0749040302e00b181d0042e5910038030003014009103411740c000c50b00560380d4207000040035100300b54000007501d8154003e006543c1e04d0703200d07140c1c140d03180d1815003884c503101015100014030150003581c40784002070010f850000c2e80a290f90714104403c503d14000503200904002540600100700560a041d801050703414120310b05540010b818104020540c02000031040d0000e50714030710540c1aa00215481000c0f6064540b88621a20514100c40000031480303203001c0440c03085020b2410f031114074070381007426649403600761300500c629a40602c0003011200b80500101078049003d01c103980c0249410020b207a22410260150849001c1c00d521507a01e5500219901840c00b034008220341300c10508984580d62900000c044d0f40180c10103000700c480f1007140000b086000701c010b400a003800452042030303415407915400d0540d101c440c1002411341d6403c480c0500c00008005001e8814807624158100d400c2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 773313938 1250 773312688 773312707
    0x90d0f0c1211010b090108070e060d0b090c2d0609010c08030a0606030506091009050601111f0c1b021c051b09010e01030b0402040b0f030706080f070507120e010203 72
    0x14950a521070300091905100045503240a10a40ca03003218110380890281d4945040f00f552400240980b0711400680b2005c903105039190340c2001b0f4265400300104c101c07464001421600e48020500941c0580c0d070302c02d8494100c101310400d0104c0091003407541115900000706000789600280059418481130034403100100340c829010718890f1282010118826040c40c200806444014041a01484510003402600080c0707044410540f00c4000c00000c4550718000100d40c100c2c100100340105000c0c403215072900c2804c1c654000f6414020510511070305841500c01c80e09204000d980b04d00c0d4480f001c044200600e01892020307901162541424104183c0340c0ba814107001c12200540c07890802e07001c03030880c10700b01408901c0c01815040114680303503141d6200c4a290f4078005100a20440d035684901d0010307902e9113080c03801d22001034100da0400b51200806410540706842008407000c5100006e543c00744100c00f102c034420351142c00042d14004100d0140c1d04008244a061b06602040c8040c084 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 773315188 1250 773313938 773313953
    0x6030903320f1315050313060b0a0e060411190c0f1b080d0201090f06050a09080418050f131b0806190510060e1003091b0e0c03090d0f0c 60
    0x120103a51440b039924103200b0008460f00445501030740b04070110301a083d2502e40c11100f40c941c00038454409164054103032901200030705210b018190701c08100400414a040140c0c1170344d100b400240c80802c80c0c61200344c4c21410030702030002c0710009400190003045d03c861141a80041c00703449480c0041c03000c3c1540c0d80e00701018000c10304408211300010003c10840e40104025441c492542c002013060304401d841c0c0740030080900b032015280381d84075000b240810400342d1080994030b41014080751a02c2e210b801752001c4009107a0700740c085070b0519021a030320008805005025002421200009403040d076100300705034a006111a0041000e10400160800103110051007000c008907841035809012811400300c840181020b607100010880600a894008100b00c1001c2c504882c003900c0380d500340348100e000d0220220010280d00c140b1100d5119007101860901c1650300c000100c500564a500304030361140021182c1025903402508407010b558050648000c04040ba46894900d40d540c907299540d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 773316438 1250 773315188 773315197
    0x50309030d020a050d0503070806040209061215130b0901090e0a0c03050307061a030c061c091a0106020d050703200d110705040b01050d020c1e010605010305010603090332 75
    0x1c050f810140b082000c0100501043c2c0d1040480e081071811411724490090400000410060080d94001103210003580c0f11815030307240700040003444109150484d40300700a481c003130014500408065101c810310707080ca805110904040905184150707840c042541c405020041d0b0401040d02416803040d000ca54000408406180104011075035034a0710303d005011206803e1420900d03413910014031425550100d40740f052810304880c0d150721804141c000c285440c1403890401c680502c0d0103900000c1214a1104651004100c000206540e90341c040990f00d400c80e104400c000113600b04036003000030f03000d5440c0c9a81c40e1020642c07010124002c084042c43d15a0740321010b000306021800f0500c40f19010040300018141c144c800f48000120400043e2243c02040c1e481400180c0110b00840307100020824007148413040e40181c5100b11440c000c0d18000c040b5401190300207801c0000220b445e0f4000d00404030f403d0391655604410040c0c041550024441024078403a07108451030744406802650000341 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 773317688 1250 773316438 773316463
    0x617010506030d030506030a112206140a0b2d1c050a1512051002070c0608070504061d1f03020a0201150806071b020301060603230103110d05030903 65
    0x200c0e030611500301450072103582d0200301014141400c000c100d80340803901d00b002c154441140000203071a180020040b104500d40d00d07080c2868110310022004054022004890411201c0b0740050300d0141404080303080e9014001c00340c00304000c0c07480c0601d980014110442d2000348080070b46603000d580d9000035480501e00107a1458520400550042c0c0780c815107401c01c000420030407040b1404510310700074810900c1490000c0c07140710145000d00c00c00340651288041d8102e0215039804041c58090100006130051400090068001514582c0188100d40c16204541c4038104d0310040000e02100c81801107080c2ea40144080a400c40d2001003a154881131490b40d032005a112109280002d085449005005e045140b1070308040040a07404601d5541100c224689400e02107441810a09401d4190300000e405628002d0005141c81d0b043e40004108581c0180720804400e9800c18041c884000b030102520343c005e100c2101806103040c81c00f00e0f11051140d0180c5c5c0c203105540c40064200243c24850 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 773318938 1250 773317688 773317691
    0x10b03060a0b18010806010b09031533010804200a09021803010501030b071b081314060702010e01030e120d1a090702030304111503070f1b05150406061701 68
    0xd035102c618106101001030320681458000c0d07589009a0381d5a103da061083c103200010004100040b40c4050000196155021040340c1160501035002d24804400340d44c6104603070f9040b5000001181e03043d00c02001018165191000f1f43c6568551401c6425100b0001036603450440b495400c9403100d541101c000d00c0c18100045e240d0210013002c420000f5021401882039142c017006000040d4141c140c940c200f40145042070090030444045410295004000380c107041000c0b420703c040c03000d07081041055030b00c810b925520501000090264502620070000d0210b2010140d40000354480e40c455602a07a0902c02c03550915004100310480b0b9122207122125503840e0070b01d44685031003001c0385000404055443c00c2d000d14207250000c0d00c900020b0001006044454035848460392908540d0043c0d0700040403190792420400806403d112800c103841c0085074081c44072004001d1480d00c50031885421a000c0d000740802100003019807003000740f040350043c0d5201da0110725020620003c1c489800203c00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 773320188 1250 773318938 773318951
    0xb0601080c190c350c0307081b011514090408040f030311060606120414010b060d02070311030a020709021605160f0e060f010804060e0d21020309120705010b03060a 72
    0x6200e406090444e10140c1e10010b1510b041302e0065202c1c0402c5041943c0c2000c66448a10a80303120b420b6205070700e005404150301145482c0d003001c04403044184410b1240080110084421039018885414411901c5030301744400110a40d003064070441c0c1d401071042c0c0c0141c2c54161290320300090608644c1041d40060b070b80310701d8400050010851075800820485000d0301b06141601e180c0351030040140b0040100040054140c10004250081043c114009080e0750b110640403400f80000d4010242c00d1700017800d20000c01040c802d0100450700901e4441e405003040030305000080e0b01035407084491154170401e0180e040007003442807148280f66008507681108140c94130092074080000760704102a0000c13082c003403059556440c2a10a030007002820410401d54460501ea0000c1c4402403840c80c060060a0060b409a80e108842d2000203c4d5881c09031003800300000703490101d001c115480030050740201003260b044030b807500c050040c03248218004034114880c80c000c079040000a0720224842e40d160711 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 773321438 1250 773320188 773320193
    0x4050c130915051002030d18021e03030d090309151e1115040809090a0c020d020105091e030c010f1409011e0b06090a0312030b010c0b0601080c190c 65
    0x2440d400080c42074401c180408000d070038440080303801e24481c0a100c0d840010706042d45038001d009448644020b900700f00413546811005140280c400c0e04100e00c10f801442605405501540c1c0c2c1818034a8050001c500706840800d0590080a503202c0070340c1840403040002812110b41030400ca552a2580d0303620030040003042c1103284200009048074203002c8000010101d444000501c46400700700403600d200c054407141800086ca100308041c058200d03502000b04007480200c2d4120211180603030b4211072400a2906049089078000e032141e50b401e410164048241c904080542c42d070350034800054a181205078a2000d0855248a000280494855044060345101c032807589031711078401d40080c024036a030030681e00c4200440507583e01c10560b441d113031551203441e0b110a0310362041c4060080c1c609940c403810001c00c5551410544d0000909114049229510801d2000c0c1c0d03403030340422714040ca925580c0041da1629002082c44072902d42c00c2c0500b1014450015804030f80d10001d44580b0120801d50 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 773322688 1250 773321438 773321467
    0x1814010b040b150d0915050a0e0706031103040f210206040611040305032703030d1b050c10050c0910080f10081b060409050429011208070606030204050c 67
    0x304510344240351954510b4820030f00c03007044a03000300060000040c00a100e10340030903c080c40e41c15400b0004e01d41000c00c011160298448d501c8003c494007125402c03903542c8011026549800c2400110410a0020030001510440c18980c00b41c405d900c0c1840c03181d1901d881a8484224211300001030344800c0a00c8140000340c0700707101c3c0d41e860000c826460a030171501e132290b492180040d024411100c1840303130f211180c480c00a103101e1003c0281030700d41d10f020300d02c1c0090140803224041101c03501f20948150318140100700721828a0808006010507a2020301070300c0007031400410400342081c04214107101703a6251440900c9445440d2245000c0b82000180404070380381c018080780803007411a070305001300c54002070b8009855200300c9610003901640400300c1c08030302503030344180b140900f444240001c102d4040c664600c49178112500c0f1072091406650301e4580107003807013103403841149a02c5000200e414400285401303406958042500e43d500d501040441d4030884d11103000000110708003900f042407 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 773323938 1250 773322688 773322701
    0x1305040908030a18033e013812010209040227010c030813050309040509010219031a01080a0b1f0f020319110f12040f051f031814010b04 60
    0x1c0240c240301422607a038010740072600f07070300c00126040d02860b00b5420300d907004080f1340c0d003184c1401106c40541d082c1b80c1145000e0b2107509001d0003262500c000e00b620003c1210b191505800440c611003c00003505810312110300c008560b500b40f41c1d5000c010000003070700c1c2c500042c41c0ca5050160009150008040c022301c00c48580782c1903a0400900040c2500400e40c026540380c0c01924000304120030a40e14a0400d2443c403c4000650300706041034100030040c0810340c0034040005070390b43e0000415040c55411421100d40044490b42c0d08400c245402c01948076900ac25400180004001440d04007140001e0311011401e4480042c950080d000c0c00c1155071200504590b00007d000071414072190800300701003522004004400c2004000710a0903078042000001006004441501c400800d148072400880d4460300482035080c0a8010000d11820408480c900ca0114444500d4414185690403000b501440481080b6100091b40c40d10100b40182c0000301007600c3e06000054020000c814002034900 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 773325188 1250 773323938 773323961
    0x40b0402031b090a08010e01020a180303090e181603050c1c1e020603010603090512190e010203042d090c050d1812080712051306021305040908030a 65
    0x14001d000c049542c019160403600b1854202e1600d48502d0070100707000e1184d541c4000400d40c28503090301185030f01980204a1a041951a1803020480104c8040081081d100080000e599440e08029110f02e015405130084625982481c40c0f881e8280d41d24501240c68050341100032100c5001c10030003004118a0740081c0c01074480d20000607010011075062880706174040d0081c200a20007a054014500075980e50036070007031581e80c8070b5841d910010021722550400f241d841c82882030400c6001043e005454101d4000040f0b0580a075202070121619054211003505510040c80045406295401c1043c00c06201ca00400f48035001d0600014141d52581d111701c803107178a8480180307000303513002046800c0781464800c045509042030390701c0c2c40d0000807030401409000c031032298803d40c954400412805800c036503603091482c104841501085401c15582c0248000c8040100400100940c024001d00015840f00002c80390356040800c0542f00c4c5400101c82182c0c000040040310421441002030984 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 773326438 1250 773325188 773325191
    0xa0906020f190503041d09010c05391e1204030f08031003051f1a01020714011808060402010f09061403250f0e04090f06020a090b0c030405040b04 64
    0x984560316203032101c01c08407100c1c0c0506442d10708041807000800486000b4001501e944124555900b44160508001c0da00949654246001d80300d80d203102d50182c406140800382038040d41200b104001c86244000054a20040d88140f4400441c11051040249010208075801010b0500010b507505080300e40c41d00d1540843c0074081071000c50f040c40780c00946164400031080e40d82c1c80700815819443c000ea40001c18a03c6401020b21684000c060262420314840b00148400d01e00e0004040004440143d5540103900200040000750002c1d4074100d045041170500e03c918010300140b24600c0d00c3c0c103410091643d80f141c0203001c11035a0001c0300d1020200a4948061340c40c1c101400103185070310a100c846080e00d0084080761122485244017404400035203901d210803142c0903c05009003010850034004154030f80202030140c1002c0c0612004c180d40158002d40d5000b03141c1c1e82d44029001a107164082051030381001c10507540c0300d001469140d400780c1c0210b4071540f600702013005545050806a0049 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 773327688 1250 773326438 773326453
    0x4021c20091311030f0708030405010e1f03050a0b03011a0a1d130627020f0a0303021c0e0a0b040e0c1c0e16060c05060112030507060e01061502030a090602 68
    0x241100942942d1540d000340c4581c041c4001c1c1002a251401000010659000722030001a58030000401402101e5080e213075100c026405500308580704003c003110800c40c4c10701c030201e041c41130700c41d0384610b9220407042c0d0700051050440c00440e00712032040d4250b41149024000c032003030740d10700090303240020440310343c070740c035a82c8252100c00e240d07980f01a10f1500d030388000100b004100718443d080440303490604401e0b288410b02c0310504020040b400507043e40036510030707441c070809424130b8035400d4250794068000303102d0610f400c4148905000400721050400c00c000c01082c009903903010410009102d4243d2142c0c5450078052525000764010f40310f04515042000003441980e10458224002c0c600c0307100004044019090700b13800d107290901005180c1c000b1000214840b504200743d2560f26000e07008440b545d0fa2507005032000800341600107404104140160800208550000c0300b40200a000200e0042d81e600031000050215201440c0960008581c684c005507000c000311000300198030040c481d8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 773328938 1250 773327688 773327701
    0x40b0c06150303190c020f04021909240c0f050304060207140d0f23030d020408010b040e120d0917070201120606080a02071b0f05011103070b0f04021c2009 68
    0xe400d60342070390702c02c0c01170510f040415952a02d030b00002480340a0000d46d5904001484040c0b0201020300e20030100d00526404151120350050580750082411a10090001944010b47d1410ba801400700d560004584040d00022018006800180410b0f001810410308040301440e030b810001210174010030800500401040c0d51009040c61260410080300c1c0004130b4001c9240328018164146005200004404841c90328a900503c03c0768283d00c008c0000c260b8910400040c4c8039072808404441e0b00880422490141030340041114080268001135100c00c90b0b03a40c8040780701074944200369450089603880565030041d01d003400c41801e60404001660a100b000b07005d51002030080d62145a0214090080003c030901c0f14100741d2140025003c00c1d90350300694040310f0060b0081c0c600051204400184080001098034500c0368404a1140141d60341c010305060000300400c10303030744030a0000102c1c2d034000b221095100703c18001c0345c2181103201282c414840020050f80320740d001e010040c041001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 773330188 1250 773328938 773328967
    0xc020a0506012313020c010c110d031a01080c07060501030302280308011707090e21193f05070f0206152404060909050129040b0c06150303 61
    0x180d9507404c4a6a85805400c0003002000740520030a518241d072a2000680003a5040141204042c0080084825102001000310280d822000b41c0405583e00c1c2000d2144641c01944690361200b012008541815201d4440b1000e079003007a070003900560800002300100e04803c1c84100050010000715440207152960300400b0800148208102c0e01180d411833010308000340505801400ca6038000d0107070103603200c106526400714141c1a202d980d03404000202a120100c1980c100903424910b8a01c0c030f0700b101c1e000361003041c0300c43c141d8a01c1c44082c0c07112004550004d1040310008004515840d041016844420f0855001404031420701c50340c2060411800c3d4001400707640595080c910401082c1641c003c03c00214000d0030384000002c000c8441413440880c04041d00840d20180c0d58208600d035107124180c00c0707075003c0c007070170784820003564010310305a400c481000b016603a141d42c03043c94542d4510208030a90802d011800c4607030400c9091014a40e007080c810241c03400e00720040e51800c0a2145001c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 773331438 1250 773330188 773330249
    0x607140702040f0b150405130501080d081b030910060e191a210c040b150a1404060207050a052709150705030708160f0e03010902040c020a050601 64
    0x2e210310f444050f040c0000d0b1468115000d01c40c409000425170074440642c000070b9800c50300620b40100c140c0540c0130340c0ca4a050040d141214090400b41200d0100350343e0403240901c0c024145040c2c806540c03a000c3e00100303184019486124108050400c40311300045c10810707030344903034481191030042c2c8050054880800c02c2401080040c840000382d51091822100303e0481140c010990001d59103404130348060319120b00100c12100c0c102500e5164040c0d2040004844000f086103801189800107110314590490041600210508121241c82111381e98aa07031a03115400100040c0c11101303040100c0e04184e00030701c010300f00451340e806050481902c50703015951005902c02038410b5107004502e0880c0240038003c2c500000f080b00f64002d00c1e04c0c08004e0030a500554074000080e8149001072000b0380000c2455840710540d41e01c0202d601c060b4501250918100c00e00d156042d5a06c8090f140107a4892084000b2a000d5401030004003045050241c10000705901c0690500f0108046028049500750b124 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 773332688 1250 773331438 773331443
    0x5060109021b06070c210e0f0f03010608030405150f0a030209010c080f13080307031d031e0f160b0f03070e0915100f0c06090503121806071407 63
    0x58569014900e01412403440c0c880050143c080e120a010300b465200e08114811030040c029109200885213130300e00e0301d031403107900c039400940344a4400c47e20340b51040d003807002d9080051607071000d8224003000a00311025a4842c42c840d034400541084182031030300a0070205423903014824140725980142c90524402e83c403000040680c0010034144503800783e080303a02c1603500203d10a454000340c82c0024007540c4412100400301004002c002a12070b400402c8400465243c1d60f90350003500410a14015a0480942141d150144401c0004001c2d1840d18545000340031368014184100326000d40ba00744440c900202c402d042100005010078400e402c1100c0c003092180c0c0c0e140b07a49a444200803612151401206684800750105120503114202140d888240048400b5110b014245d041580c000741c000b8003130030100e0840131620010884d1076100c5000240180140ca140c04510007a444038008100c0b01000a5a03440754a425114070400c50780360301c041c03242414a9450484204940300d80180c3c0f000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 773333938 1250 773332688 773332691
    0x603070812071a0f101703070b181002180315071214040302160504150302040e1203040b012408010b0306010201060b041715040b0f0a0209090a0518070305060109 71
    0x8072040054030003000c0d07080e4101540c0c1d00f80505040000c0350341500c06542900d10090a42000304090600c41c046101680d0610700661a1140950310714510b00b10081115080c90394100b4110f020341401e0207003100070ba540500059441641c0803e81e0040400344541a01a82c489110326100c0802012040c0e00301545013040507140084100010281030340c0c41d00c0749048065001400300b010b0b0001002a07180a5800c442410f203034850050000716520f8074025401070122400800142c100360348604108082031058450410582c0c0154203190301c00d49003121424540801000421603510007030f5000d035801d48141c0d00d00d04249000400b080c00600401902e10340020125031681e0003540150000c000058aa035140c654505281c104100d210038522000c1c001c01d141248003558400c84070348900e5100030a22500d40f91440b034101034180c014000c1000941c03c000340d8249a0f1100d28443c0b20340b603d41d0f004a020720b442848101c40140c5a110902181d00200051000a0012680c0e90659010240 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 773335188 1250 773333938 773333947
    0x60301030f111905100f12270f0c0605041401080723030a06060809120703180801020901110102070f030e010e040f0b09060d0c03060c090302130e060603070812 70
    0x2c0401c0c4810150640e168882010000910181456924241140c1d030443d56200700b0b40018a090f208004141040000903034148072103250000150f002014503044200f950b1004a80b407900000c41030b00c100801c2c0d500810254462040089100328040030340094a021809c140c600035015003500e07050540d40341800310780c0c0001011603200300308076036000704030001e00480c401c1c00c3d401b2000d1390350050320b102042604018002c102c2d980118007450055103504010b0200c0d80c2a641411290782050700218100310011000322024031017000c010000d0061000010703600c0e00000005058800f0ba07001c400b89590050200c5070108001c611500c281c50b4050a00c0c81100840d42e004980355000380b401c5a5010b881c0510041d5034503081c0c2e0015550042c240ca180b0000d0301c1c0c980c200728052440c00c4004198800c000e006100080c040c0c0c02c000170501c02820401030047d100c1e400204e03900304500002071003603a6200004150700c010440f16401c100c0580161040c1c0b070a2070a200d886491100480151160028 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 773336438 1250 773335188 773335193
    0x1030609060e01021902010b010311030f0c1209070906061b11060c01020c0304030c0803070803010612020405040c1706090c0406210e061e011805040606081b010801080c060301030f 79
    0x40010b14520402e000840d9100725060703110303544145000c440d01c0107601e00142c1d46403950107881030340055000d0710850350441d5074118075405007280003022210307640c400384401a48100307ca01500c0c0100801030241440c2c1d410480e0301303000c60380e09502c54400c100e0627200c3e051100b1071801039800720703c1c2c20403034402004601c0008511248201201e6607105e61000405011020700400688141e034810041e22116079130b2120701d03540e64002c40c2c1e0302911007401000100542800384034030450451324104c3c050f0410f0340e100005011036110340b8101d004120004046101c011104160740e502000440300300c400303401c040c0440c03070550080c1d020b60030600c040b83c66641114800300c5a084181c8803a42403c0c0704c000303080c2600680302c0b4000d96010704104e00c0e2010750b5010b44141507416041c3c448100c04140380f8202015070030050072010f082592105d81d10324020441072814090311003043c007070300012200d404000d0001003018030140d000c580660000021000c01c3d540705d0080b40d044940108040e16501070b5030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 773337688 1250 773336438 773336441
    0x6020a0e03060112021e030c010c0c03120302041404090c06140706020408030421030234030c050f0d02030a080a12050a0b0907050901142d070204061502060103060906 73
    0x240e4040d41d16204000000031040700f80416442050320983d80908444851060f04084071a10800749516030080200c0d65481d51290344801206401004007034800b6030717a5125418211800022000003d030001014001d004194070100c044100944040203109a1504c84a40c4603190f4014801040560020301000300c101d03805840d80d040e00204119552940c03829a180c0d03030342c401d01c6802c003120b500c500b440d4030440c110302c0c24000542c4c240d0040d00c000864240d0306c2c400c00c1d2a41c403120341e0402ca00d403079903600409860038450241d4032807503900b281d490419003081000740780040e59600c0391803d09600b400688020801d1642d160380100000c2e00c504612005803500e1341c00c1d40381d98580c84d150a0030041c0c80b643c10f40051000d0301080e80c1c0350b0103944600e1011111445651201c40c04501401c0708040c8444841000b40303d894480c9010159100090107000c4144a0220b020720a50b4030106038231065241900c940d0307000340110701065001a00c6410302035119401480040c28442c1e84421080501005 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 773338938 1250 773337688 773337707
    0x41060412020717030c060f01120807060207120804063b03090613031b0b07230a030801050936030d0e0105040b0603060c0412050321180601060c06020a 66
    0x110070007981c0901c107807003d5580750003044284180b0b20074480030a0081d0a1f6034007030f90580300040520080d1f03400a4580305000c2c0e2000c2c1c0d04a5903c0d80c200103c001261200d88694400f00c2655540006401d0a0030210166070704414282040c840c040ba01801450030f0980c2080316030030401b5005c6a04204a03411429401a58003d94100400080b40c13504650302000c2c020a480c41101c5070081680c500d2002c89400301c4500481030b880e4010803c403400300c4c6546590800440140c0ca55110010402081c50708003404850224080380d40040180310038603001c0e000700c1e8013503920b042000d8003001c03046001d001c0c415031810715070310005086001106400d0500445008500c92031003446000140310b40711b0300070281140e0030b40702c8800c800089549841c0204046025030061021a4141410039000441803029220119034902c0b080001180b04208004517515403061100d85a8485c40d29040e20251041c0409451803143c0040d40184080d0350840303960486a608003d005031940c01ca160180d50707003010f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 773340188 1250 773338938 773338949
    0x1806010e040b0a020a09050f04110c0703060b030a02011b05070312050c010b04061a0d02070f0b2d0c09031e0f070801050906060f030307410604120207 66
    0x540400403424403a04509507005a12448200c91240d0b280d07619141240290705100000800c0e04404002520b88202c0c01b000e80d800080000810f2402c21a401c5201e502c032580d54251500002c5c1d04205025a51180b0444008160060030302880c550303000034440c803290401282e0403491001100184001008920040c503800004c00e5245008000c0c044c06c55040503400000541c2020300c111141e08040c010705045526032007010b20341c00e40ba41c0b000c02040e00076a0744a40301c1a824070143d00403900c4505130417040340c02054003405900348404207000c1c034040d00c01039610303802149001148401c1403066841d48a00c00c241240d0729964503400207820240301d0724081405889501c0106402a0081500c00c5c0c6012107030122540182d40b10f035142e09030b070000c4442060981011000552500b81130941c0402184010280c03440c1050030754842c240c1c20a68030401e422072800c6215803031440f038107129880e500c82c9454405543c8484507a0003075501e0700c00400050062340c6030040d40301454000c0010201415 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 773341438 1250 773340188 773340193
    0x190e10020c03031b07050615010513030c0303140c03090603060409080a08061903240e070f210807030c080408190b1b04090207020f0a031407140d02010818 68
    0x1e008008840c0ea94000f0b942003030226201c0308411813406400c0007216106030740320b00605130790f554110481355002495204035051140803c1401003410725540820701851040900e48011421414003d07e18802c181c50f82c4034450042141e501c040c80c002064401a01c030444580307907240e90340b00c08180902800b10b0002d1281201041800b9240e4014060501c50030003030f104480c031070340722070401086008144000b403c140304442042c040c50095111002c002040d028022603070401d05a491454420981c0c40703026420002c803000d20156011101c0721080c0d80030349202da10084802d03250841c45110340f4100406201a110b0402c0c108070020003507800810302a42914019004d80381001000c010455040f5011040000080c5d4507c0951002a80b02c0d59030380301150a06050007041c200035407044100780c0e4040a280750300341041e654025000c01551150558503080380d000f0b06924580505500a1204502c20003403d458507122039041c0140940c092a044007141c5400c10140306c02280644041c0290 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 773342688 1250 773341438 773341447
    0x42102060904022b0b131116050313050301021e090406260f0303071e050c030d06180903270503060405030c0607020d08060904030318110117190e1002 66
    0x209000103000c0102d001012000c13006420f0600403c2c101c8072111034040e8449001048071600021645c88611885842e000741460b088210803c030742c03003c040d9041115035500000e1181403011710b843c13a0400400c001d500031750030000100d08645203500d10070300346000050082070346030300c0760f681c7e802990060421502034540e0300340b80491140c14044c1c810302a151485842c1c101c8902c040e001044030b11440b6166034411809d11482c0c10741c0398014400b8032050070031038107108107081c4010510040c400040700b0035000612510303251650029910341005014500d15240d04003002c04d810503403541202da0301c51f0850300003d114044000d90f4a82c075400ca0b50301449800100b000b0408000000e00500360030f1822140c0b107070703a0004220307503070318500f40c48078001f83c003010201301c0d079051849103150032034802d05010880b1181034a001d43c0d4620610010f407604030b80c06641d00610351f001b541c00a000003c0c540d1003490b80c64140c0405100010104807030083d03580d104c0c41105800d509212200005009040a5580303 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 773343938 1250 773342688 773342707
    0x90f05010203010602251517090c0a050405190b0a03150c090e01060f0c06060806130c06030b0306310605040605010501110d1206080708012004210206090402 69
    0x2d401c02d004030400341c03060050b9401a0350090043c2081c02c2c0705000c0015084d400d01d4803c0441c00110b0400406001d2031002440c0c00e6100758104600c14000c035002441d000c0d048404020000c09540c0c00309025600c2c1c04184824508070f90540020a4804200413414070081004154a80c0c1954130240c05c070715610314411a90b1500da08024180d82c52981c03440907440e00c805240b040c2daa000e200b050049042a0404c0c050302d4050903031a000e060081c28005540350f078895400d802d00d0002c4039442900c54200001c0401c0211015192020b00903d1404020340c4c000c0c2c2021175950140600b800b00c000b403c100c90925070000d0f142c5040265409a00d01098210291401402900040e0750440f03c440c10440041025482200300c2c42d400e1151400402d94040c003003809903400d0340081400a0b1441c0c0303030580801c0580e41008180010007401000140b0f50b0b1500d1031200e85004038a1048504000c00c0108000648280d01c503074110480b08040f02c071601d2918400034445101c5e020600703403c2400400e91484 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 773345188 1250 773343938 773343941
    0x51c140708090405011a04030b0a022a06070305070c0816051c1e05030a0506030c09011d091924090303020403021f052208060a0b03070f0b0a050c01090f0501 69
    0x21070b07160684052006988513552102103200c22198941507003814032080000c0f0784c1c2501102e4002c44c00c2c3d80014136162180107001175511034a00c10b90b04003070301e00140b0303001700008000c1c80780e1004480c5400c0107682072a60700204480d810b1400900b07031030008101c400e11403d0b184a19403035254401c003150009600e1411250400c4060081c20000c144c0d00340e4842c460348030a404107800000e5540e11186161b80c1c1c50340800007030001a01d510382500c03650b0790902054603021141c0340030b404d66048030508140d4500c076102810400406c03d0350a0340240c030b00506885c0d00b03203507100305450313001c0415411503402400f22070042a110103001c0f0542d08100084040c181c06a008109490080c0c41500350600c3d01c0b00008142d8a4240c01a00000c0d030401c401e02d010320b034401074590420b84000351464031541d50803006250101c03e90f00f071140036a565600c10420b03d000c0101d00700905207542d0050046150502c01e050501545407600f091040004604c1040c850a510000310544d1010040e40302c1c94013800d03c4e60 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 773346438 1250 773345188 773345197
    0x9090907080d02160608090f0109050601050a050a05030a0b181b04141915052205131205030703091b090b03070810090614090a0606050904051c140708 66
    0x11150148503012800342c1e202080486000b07440c0380818006510300801240c0340500107010054a0184034210311800e8400e000d034a8180303029800922465040030200501810f255000d0f038898454407108114613180885d003003100f00d030005080d12440d5900c4900781c5000030740d1814007065010320443c0d03a00780d02c41c103040a1145001680d007080340c0b1410040d0801100000d0780d000c40300d200141540a501401c03900521202d88c42d10780c540d000103a580000c141e204a03048010a0040c2855614503003a0340184035050b803015690000055480c030307546905c916a070072449480108500000004c025074040d0b0015840c20b98460744406564201c180d11018004903401500c000500348a0200300f82d141c002603d0041e603041c040074111306046100090014031091508603052900e5040701c1c0d81d00644240b01505c10030100001e049415814a80202201c00c69003003284034000b183c040c00b000c1100040d02c0b4408410070350110005802141060301c4110121600540d0b20700c0001c0e020040002900140c07 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 773347688 1250 773346438 773346449
    0xe07050714031e03040308060d02030708030a1e031503080c0a020a0312110643050403061b05032d0c091207290c15060907090b0f0c010209090907 64
    0x440750280c034140f078000d092006560245c0080d15070783c0410340d01c0c40c00f43c1c1e1000829100400b02c82106540b14122030564001c1400e40020498030b40b105001054008030420079071019181c02c110501407145a1081c00455000140c600c0c040450700c00c1c5038600400c400c28400b50024104241907a581c5000c0740401c0300b145042c1d000421401a51007041400100d690248954441a0125011039252849610303594021200060b610705284641c2d01050550741400d1119595402c0e0741303900314100700f029036024454001c1c1c1c4059000c41c10440c0c03948001940c0d0440e111604600b000c00041c60404007109040c06840c0d042001c18041c481c00c6110f0740002c000040d000d40b5000c565005444500e610740f0210f00c16550650903542d0b802c200002d00811140900041c00c1102c2d0408005581040c84c00101d84403050b0000b41400500400f40f03403010880340d00c2074451400c91001d074280611350101f03008090300950405004241c4254a03802901600d100ca00040e0855000c1e103480c480f00c981c1c030300c101d1040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 773348938 1250 773347688 773347717
    0x20c060706290f040b03190804030215030601050f07030c12030e010b0a0305030702040b0a1502031806181504120606050a06021204151b0507050906010c03090e0705071403 75
    0x11000301002c4184064031400014a1030107940c1103902840094003401c83c5140d410301450011241608424a2000300140181c015079200d509510500510701e0b61038502c11561542032042000d10b1307034448202c86644100c14500d0ba00e601075031034242c8410161400061040f9203d10301c9154480e030542c82800c80d1b4020310024021017800c1406d02c191103446e4000900309820030000c010250400c0d40108174685005072100f44d04607a20000340d58100342c5159010016000003c2600c407556842e113601012100441d007131440d2078030000842a507803208206250168a6140303c28403105884400e650040480f87c105501c540f05600c0c4c0b000c0208110700460f8840c101d2100046030451002802045440074004968906410310002d8040e0100092100b01006088944485841c00000a15410034800c50040c0b56150408041001e88c2e00001d220f11304028203c1c0c0c448010a03407080000d030849180c800301c4400e9450f001012a1184100c4901820004a0100c400c104010000040104a041211 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 773350188 1250 773348938 773348981
    0x50a122a120516061d06010e04150c050d090c090903121808030c0c1f090201171905090f03070c0e07050306092d01061107171903020c060706 62
    0x10161400e0043c001d00d4824850b2040b24400090b03200d40c0301d142c03c3d2100f84140d07080b0141c0161201d180040036041207071100c03603080500080154225001c6544980a1414005004d070b0010040c510300038003810022075a1640003800522480f40b11103409041c01620600c00c1020074103010780132407541c12103d001e07d40f401040701d100c4a51889103028455010710294603544a030030f801c0d07015811201540ea1140508401c0c5010001d0045600e800da041d1b914010580c0ca12070300001d8690f074403109111400700358040801c0038800c50015002c40030000301000040644440c0740c3c0e9031501140f20940c44040c440007400c2010b010310f04104000321405820340c10959540c29404503042e002c1620002d41000c0c02c030300031890b0030748a0100140d400301588064400300e41c45441003001100280d000102140502544c0d440d41d0300144100009060310f500f41031017102001e9001035841002ca21041d50b40051902080c0c101131080c080c2039450f44e40103182d141c444100381030a20003403400d8040b503549507201d100e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 773351438 1250 773350188 773350223
    0x1171905070e120d08010b07052d01050604060b09010c0317091f06060c0f0f150203061002010902060702041d060702010f0b0414220c0f0302011b050a122a 68
    0xc0e40e84d03030324400341c0c3c441541c2e07443c0440c0d01c4455001544222010f000e1100c1444071790703004120911207144030119101200030302001c290b085031005411070340513900b010301c140324151040084600421080c46c10544040705411b0850f0304503820021074101c41c80d071200b8071521010019440d0407171407030101c0700500086260340000c12a0164450a00850300b18045031020500c0c40501c2c08290b805011401c00d03490303a640c0ea45040c961626041e91078240d02005009e003c0c10495001800c00759140000c000080749a00011040d01070220000d10494840000c2020020000050f0001d0140141100c1040c100000043d005e4100c140140f09001e107000746d2011300c0c4c902809840a03550b8100441052030302c80390608000403c1070042c5a1041ca00019804c00169101d40600024540e800030190654190b20005004200013018040103005040965010550102e0328801c80f075070003c110301e00c4454002d01945c41c4006042c0e08240b490891401005090b800f0702c480039102d1203950001c41c3c0e116002d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 773352688 1250 773351438 773351443
    0x30112020f0d1e21030606080114130926040303080c030408070b0601050405130506031e030301060c03200c01020d02031c021c0e10060801060501171905070e12 70
    0x1c140140210805451805969260307124030007103c3d00500e0f90000b0a01301003100e00701641903124400000e517492000700040f80e441202c05002d0169110f01560000d807810005180c0103150203601c0100340d0780da04a004101e102c1a00031203a00200001c10030700b42803071000800b5a0804e00c8180c021418880c0000d1050824604803441154032035485401c00f1800d072208402ca0384002c00007070500004000100702a0794041c42c05036003540c03804e804266481d00c0e2060504080800c030316101500780340038112030700136004810340c4e05681c443d180206500e861420300b103450a00d4128200c400d00a9040c420360030080200b00c004a8210a808403051038a0200d412a503900c01d50502c1c0310b0354600c000520170f1b1038605400034800380d49840b212505c0c140204c0c14400841c3c05101a245460b84075005000f982d004a00800340181030100c020071002c0e29080c0040c1c00640e00c049601680c180d4440044c002c0d4081c803100c4480c511100c00108440e1406003006032409600c503103c640305118110746210301c0f0400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 773353938 1250 773352688 773352709
    0x6100e070305041505090106030804090f140103020604030213060902040e181501090c0c0204020a02070602161404380312042409031b050f0117010e0903040902030112020f 75
    0x1070207030703130702040050000c000f0f00c00504207800d00e540380e080020110b003d29001e48060b01121000152101510410304210750010901d4101d0281d00340c0108003580c1c640e000d41d012a50140c410284c00ba26540d030030001440942c201079038803803001c5004500040002d01c26031184d9030b06170803034204040c0310b0800380da1481007a00c3c01151504041c0180b09500003a0070140b0780781094100307100c02072060742c0007800380d8104200c0c41c001680004410851584d0411100c9480700b88425603d174440c0c00c03d010340c1e540c080c0d82e07a80356010301d46400b40034a440d024404d04103440300c04a00b4a00205a00c10982c4844240042250f031091007585600c08024031807208480844107030f4810301c86841c00302230907152803204203509141408201d00000020031080c0480d4652801161554001c180c240010400e601402110b210f04000520201074080141c000c40c080c19a5408040b410165542e8400745244d071085803c01c0068600100002a01710711095203040c003684200c404c00052050f560170300106886 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 773355188 1250 773353938 773353943
    0x4091a270610050c06150a1502070e070507140a0b0109151a07050607020708060f01060203180f060a05090a090507170a14010b030402031608071707030506100e07030504 74
    0x24500e001c00c40d14038040112001a454074100181019101c03100181000b00c1242d01c012100f282600790402413503c24900301c09080c200c03620a684008003080299607000304d019003148540000c002c10322090040701552203040c0e010100e030310103580c640c02564039456500401c9800f541e4072030000c11040644d019440f04d5039a0311810380115803902c2d00703642d08401d0140000c1491102080740002003802404594400da007503030001d040152500340050b180150040c420490b02c8070320b00041c001c0590220031510b020030705100e0f04000c40061400148444407010026a000304005000c0000c0e030340040290210401c1150400901c0d580c810208050b100200c0f030f101c00194800003007010804410b0072280e0825100301700010710040207400429180b00a81003491840d0010003040218130307007005041000d910110400c90414540250180c0c0c0b58140c0c050a21103103001000c1041e12401005000000c68000c011102c050078504194942880c031360062400640c003110000d41558064094a401180d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 773356438 1250 773355188 773355259
    0xc16030f05100c052b090f0c0b18100e030102030106032019140702060304140105060406210821071202040e040609050a06050a1d0a050312040804091a 66
    0x1140c881400d03144820002030036400800001a517002803a0344110043c0c20311a48510759a1034207070078a902c9000d1242d01a6044020410400741048130031642007110400c182c1d00002101c14403070040d54008000c91520b40c1540c404000040d4007070b81500490f103007110306040310300c3c107400748101647d26200d40c81c49100075403100001c0a41041c0324405c0c00c1c00205c60300402e281041c00c1c65000803200e0307005481c250b43c058112038a401d0039200c20311415410001c11a01044150700d40140e81c505683c104c5048420791100f05101c4091028510850748060350508940c80d0900c041252204c034201300340c51501c000785051080700304070329880c42101c090b01c4644407180e92a41e115624107000d05141c40c0112850701500040400156003402618010860420b01040901034244201c044410b641d40c4084650303c15801c0745c0105031b002c402c40b01d025046421101880e6164100700d91280308640c45030b0005413901c00b030107034200341034076040351f00c8a0115003050904500018418070b000700001d80c1341201 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 773357688 1250 773356438 773356447
    0x20a020a06050f1603020c01032307050c19050a030906081b07150e0a0311010b28031a07030f020c1902040b0a06090509090607050d020c16030f05100c05 67
    0x780c0194090860200040a4240b4103483c219000c000c40302001070490241e03100f24000074496030540102c1e896041940250041c680f0850400c1101140240403101440350002c0d8500301101c0a00c8850380042540c0000444c45a8910701190f4030b5816400940c005000d1000214070b0b203110b00003960080241c00d929942904c0160006240d90340711200458219041e8004031000f0200c600915982664a0b07024085095550a01a0401c45480b0006203940d2500d2820440e039030701d00d02c40b0140c8132070507521907003100310b10000000c00da41070360409005000b541482d608481c0002d503056214075003a07582404985d8110881c001a0f01510f015641c4079000010300100d24840704002d9541035000a00c042000220340c0d011415100440e0011000500102c000740640c2c05c100c44000c0c1c0001020004094074a48032500814a001303040545000a400207600c400016003044540f4240c40d40d040e20002d5143d0780d107801c9900d080d940c081201c81e4014040004000c241c40e1140d405d01c050a6240d01d449c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 773358938 1250 773357688 773357699
    0x3020312100f0602031206190311120304150f02240a060e01060e15070302070302011b060f051e010303020715020f010615021b0d060b04091209060e01020a020a 70
    0x84060007009403029a020150020351005440205801804150040c581d5112908444d003080d26006010034002c02018404c680a1034405100c2d5040380d401c1700c03205961402c0c0398001803c0c0c04081129080505c00401c0114044070b03c009020044441a00c03850780ca20100c0e0416031b150041e40100c0d001c000140005500340629040f003140d0b01210000c0300003440c6e501d40b540320f0310303218007a004080051034103880200c05040103000740c0742141942d0742d5507080c407200c0d54000b503071040b480c08024108010458413421b103800080c042c400c4141d01440a0003a018640300c440c0003000c0c201c03441c07543c10146803049801c0da0b0400c0b440754180c2c0d8265010b00031460800e20808006941c2c0c115000c118843c601c03244003042d20a12501c0c0c058000b00440403400c00107900000e25004c007a0500490080440d000320076590340e1910304440b5181e1000011620700701c2400042d00806600902625501090b1400c044d41c81d4041c00c4442501c40f10b4507070940c1c43c0070180049a680754000303002034018502101c01d000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 773360188 1250 773358938 773358967
    0x1e030a03050c0903070e061c0c090e031e0901030f02070335040f062910031b030e0f0c090c09030109050d02010207060605060a021005042a03020418030203 68
    0xd02a040070b008514010100001c00d1506a069010340714a85004041c09000d14000000e061020950000c1240e28207482d2a600100f405500c0f42080a80c1d41d2591104005014000e03100d40712090705100d41203510f280308080581d4400307039035140080d1521000c840e03956081c1c400d03141910341564810001d92130229003a640c00407502d00e0710000c58003031015000b40340704800d4500c3c401c83c45080d103041170320414606013042c0c880c40c41041c9001c440f000d480411030406505d0502c2640c2080380e80c0e00b406404914150003c006140c0c54040071000461100407c5400d9000343c03646282c0001110b0022044818080d15600c00d207909a134400003d00103d4291050403001c2c02060070000c00001d407500c102d68030781e86440414050800540d4000c100710007030100c01e109920040c902a241d480c030b03011804600070f48030141c03060041000d55550020405000800f2903480084000380c001400110300003000060070b4400d4401217100724188083c811748410345100314200316605800450400407810020344 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 773361438 1250 773360188 773360191
    0x306030d17160e03030a02030706231603021e0a11060108120f16050d0801350c03030307120f09020a0e0910020f0a11070503030d0b012c031e030a0305 66
    0x3010020f04a8032050542d4041c0001d285184c0b468000b9941d4440c5480d0000a03070754640d0302040100d0303803003000d85030300b12100410f1984481c0e40011030150001d0084240c00a02401c24031048a071200440f40d03146041e0f00c402041083c01c2610390580780142428900d5556a0074080c0c44607a070410952040d030054600041c214000143c0c0205044c511070741031503880c080d0081026516a031002007021583c5800114581c0980000c40c070401c41d21000c6216918001c034900100c1044c1c0e20031103540000c0e11014001c1e07000740319004080e02d60700d0400003001008034111072540c202035494160347d4191800184591248158040c0040e11814a8121218a0910000e24000d81c5000e200310609100300d1510041180f0b00501c084a6119031400c07400600420340008088180e44c4110024000c656001080e50156401c1020109070141c030309004a81120109a842e1060505410000f402d01c80611004074243d5055088030081c206640b403452407044656000c1006420811000d050035100740c100d039 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 773362688 1250 773361438 773361481
    0x7240e101109040f02070312060303080408090303160305030610031401031e05010203010f030b060108060f1c0804080703050607140403060504080f19030e0c01080f1015050306030d17 80
    0x26040c0300500b000b207801d4a00c8001032200307441d40000d00341d003019080171a003442c00312000d0041004900b955005058518060006042100c000c203100c901c90303404200321019200d14190103547c2080518003d01541c1041e1000c42c4613000c80e540d0820014420311031401ca90440c2e1341400c8040c4d03c6c60b20380d40b074140c44900410701c010328041d1822022820900080d8001c000c4001d0b40c84074181b079030034403d10b03480019002a0400004000b485015950f1a02e2829924000c482d10a86901c07107060482c015107480da40207215400c041000245800c020801070200c81c014001d890003030752038500460705484003120300040b02005002c1407001c41c2031070788903561291003481c07020724102c802010528140c0113280c0c0d04030140644031740c900109903d4015206030112900c010805403d032500060b1500c0030040c00c940b0041048400220030050014001c00180303415102c007440702e800b032040101960300403500c003802441030000340d0500c0ca00c146141001010038915410940d10341858004d0b01030b0030081c07003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 773363938 1250 773362688 773362721
    0xa0b04020d08071e0201090b040b1b0c100206060a08011b12200a110303010b09040f060e071709060105130b030a020301061e0f050d080c011107240e10 66
    0x3c1d40c0c00203001a0403151101c0400340340c412a854144001402030302150801550542c040c0810481a090303107041d900700020048a6040c0107415040c80c9180000f00303510a0351090814020003500da0300441c40900a58050740d00b0f42100d91108a803609079502841184480d040a00c0c5051519105d510400c01d9241c0f031640101c1c2d4080040301c48100004003450001c3c0e07002c00040c0310b200140c1c100d0a030410604651300035504641c5400000e401074010741846074000da444049421400c81540e00c010050110301c581041941007505000301202000c1c8003040080460a01150180340006011030480310000e000c1410030030030b004070340c016081402c0304030303018424142c0b0080141e03000e010384000303007004000341e0159040c0c1e16281d205c4891780d03501151a4800b0b00c00c05004e6074070ba2190351035085e508008800c0da42e120f10503403030b401400c1810308045000e401080c0c4d03008100f07251544010302c910455949800e541d40c9c002c03120848034454410440c0344e01c5150113a82d2080d00c1d40102c90707010380080d034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 773365188 1250 773363938 773363947
    0x6091d0606070609051e0f060108030d02070c03050706051b1c03090516060513060903050307030305040309090509030a0815030d030b0118080304171204061d0414010e090a0b04020d08 80
    0x5c2e403d107071000150346804034110100403a09400c2080249400d03101e2901c004004551610b0400d030b40341d02c114101d04062a8000401d0020322610680e072500460b4000103c0303003000e6440c900201103820201480c9071041c040c8602804a800009001c1c0c0303035603040d040220311a01d011340181d00a010402003120f50f40142035a0707801c0074bc3c0c80d840010041019445607540d440059400e0344110a154015038140702c0c0145040c0045140082641d000703e1341424001400d1302c80c0d05080e12600303521761000c1c034072034105010400c44040101c007030001a0140d031542a13944d12000295500c560200405075015400b41802c0343c3e01902c641c001200f1224103051808080e00c585031004107912198100d5500c03580001030812104440042154000344a07402500c9101d420100740502e038070030313841024104203001c481e0440081c1c44c03100210000d58000c004000740104201c401d0801c0d4000d110b1001038000340e000050044602250360081568801e400d4945a03555508010f10b90b81c4011040e43d01000501 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 773366438 1250 773365188 773365193
    0x4151e020703020c01020115083301080703021f17100b07050606090705040302010c15110d0c0e0109050a030605042d120302120606070302100c030606091d0606070609 73
    0x200078000a406940a081581d1403200003a09540080407099420003401d90100030300400440c0c2540500000d00e0080084404600d0a407602d1261822500b02e0f51031103000002e075072070001150f8003101c3c800c0d20207484e0407402003401d0307000001c08440341e000700300900f807403404040e0218003441d8004260348203a4071386610b4190305180e0f5001020100d90359413000382071018500d410640750350b1114031447d00503d403606550009001e104201e0000b0580406041e040c0185800380e004102103030f0032500c001e500d44403001e42485c050182c0180541c081003500c484202254400e45854056a001501001b0020314540c4c2c1c0c40001d25005006440c480710060190081c0c104840145403184504e41e00d4031104091400c04170521891442014181403040003584605040d40350300e194081d004030b034080e4803903440741000d9040010b00c4950340d10241c0b03041d800809054140c1c0c461829507203d0b580f820280ca454240c415069003480084050001d100b8000030b0070b03403070483d0081180c10300c0760320302089a041d140e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 773367688 1250 773366438 773366441
    0x105030105040b03011b0c020405091b010f0309020613140132130801090c0e091b0f04063002130903090b040807090b061e0c01021e0408011404151e 65
    0x1c801b180d0020303403030590380425403070b01d170045c1074104c40d0010280032510b0030000d058202c4110402641c0c140440c0700c507042500b40c0290f12042000e60003505103642d80300602c44007004c1c0301160081310101030000d0340380441940f141001c144441174030803d6031207181a41003280e034900c110041c203c1c60800208030041d102d040048045000b44183c20021406a04614040d048010715420402440902004010400030006000d900343c0c103940d102d981c4413000382800315000300310401e61282c00504001c00052407120040c0c900011100a80c481c4e50b002642e10030b0102586071401c000b0f54800320100c190300089900382d00c80c10040c0d00c07030b040c18641b2503034030302202400d13401640c042c80070381c1c0140f80104100c0748c15008980c2c400305c046541c103103010181c0c086d2102100d54050311001c03650740850208844082503044400006070b04c071154103072100c100c41541072940070b4020007140f9403c21040301d8400302108105405079600204104000424111920040c40c0314a140c1c0540d20740c0c800d175668100782d40d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 773368938 1250 773367688 773367731
    0x190909050c011e0c0206031306020a0c110114030a1512030201020403020a0e060907120213080601050f0306070210090f0633080c0f3105010605090105030105040b0301 73
    0x1032406002020203103000506020806005258108154255401c2d690380c032100c041d0455504865040d00c070748804c03a00305170880054070001c0c0254400601459401d42050407050b10700d00c54248589408460001120018511308101c3c0442c0002d101041d0001601d130404410408013080b60010a40c6d0b80300708410050a81e0030540151354001011320a40c14400f04140203401111000525400c24101148000100401a40403c02650840c071085429501100c150b607100c0c00c00700e00001d444006280d2150340c20b00c1060b2007a4003c0300c610103207080121b21144514096009000307451001200b200190541c41411a458148a0b5288002411600c60040000da001d42052604003c0d096070b0920342840864641078410122400c104411000078810141c4c01d068820104114003100481c0d0f19908401c031900e1501480c00092141a15850426204030b19030f01d0203021590345e5400035075443c4908400701d03001400800040c4244e0400350408550707100701400005415002480b034800705040e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 773370188 1250 773368938 773368943
    0x1f0e04140708090709060f0303052b06210b0f1302040903030e060601020c0f1e0a0806061306050a2105150603070905131106040f0e270a02190909 64
    0x802c400c1c0302c40c0300d804003c007a0180210400400a003820401c6480c5014024031000301000300002d1480300c0240f500101492a01143c4d04103c1004d880c090b8900140055000e0200d01c001049092840d0b005501c000c0031480360851802841601c81e020419800f140080c24038280c05481540d000040e1192310480384103a02a50700040c00d070300400c3c1c109040c1280500110304552040707643e81c181d0b40e00d80700001440c520440720442c20340071141e00d52480c10410000c1c030f94051080c030000600f80c2004100184121001c640c050032000292a400088a165019694000d07280c4101070000c041001c8079594a0300724210303042d01c81030180e42c2d00c030f140084d4a80e21a031200c3c42e46082c0031a0342001c2001501509074503006001500c1c0200106014607000300c0094550700c0f005000701e07400c0d01d80b00b007103501500c5074089100c249501d0b0807405020040035507581c80030b100762803144206610311406201d8092000b102a0a482c1c8480d0200b00c4031403a940007101400c0c0f404007002503407441c0ca01ca0b440000c2d2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 773371438 1250 773370188 773370197
    0xb010c081b0a1e170a09090f0b1c0210080f010501120905010213030b010801020408060c2212021c080304020f0303220f150c030309060204051302090406051f0e041407 73
    0x10010320f04505412103c4400d110324a01c05d0040318851904011381d407064a144040010700d1908103071420016003c9a0003060f00500d0640c403c0043c0c620342d01c26510a1030096441410916002004451414044645404201d4100c0c0107114030340c42140544403100b000000420700c00030039200c0508a07802400c4004250031100010800c20161401c1e990041c81d4140007141440e1038000b103180ca440000b0031009081400080c101006c1c010050440b015085140700119841d840f00c21307101e603155400c030099100c1c24103003242c48844c800c0c0d50161b902c001d034080303d03440c15078440340e00340304900c42100562581400b040c00140900300c4e0300f003031460a207044c8404058455103400516040c00c002500140c000c0e21003c0207002c1c400750080c2030364140550520380040c042455040800c000e01440c0c000315400003940a4541003040d1039000f41066000c1140c1c20044c09980f541045810741a401712201560a92810ba5100310702a20803501b00030800340c000300d006040c1c58024031740f0b40302c21240d550115 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 773372688 1250 773371438 773371493
    0xa06052d07120509130b12031306020106090b0f010c06141317120c1c060b04090c030603170d02160503130f0b030c03090f010615030b010c081b0a 64
    0x124030040540e5031510b072814002d1400d0740a40c04a051900c201c40c02d020750ba82c80b8140307a440c0ea140d00e0701c499002c1034104240ca0300c1e205020b9000d908010f03d84100700c015820030340302040e03180091040344c1000b20001d1540c2039148804005503030101d1620019981c00799503940002d608264034207034034400d4000c0c145c401e0445455150204000d410b0b80000460a1317014405413140130390712510250842c200b003c61545611018203221202c8056000b031051990a00f000010107540a0003c1c2090f10b1046100b444015110f02044049418901c0003600c400540490428243d00d40c00c0184420104001c0c05441c0c4000c03024800090000c200040b41c0c25800003c55100303070700c079981c030748405041440383c401d41562810052100d11301010707043c003090000010214005410410003c80380e805484028090740d5500c19000c10040350104494002c64240941241550311603100740c01a80e901c10b440c20308090070a41e04200701081c07c0380c0d680d0148180038001001c520b81c201d01011000850740e080808 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 773373938 1250 773372688 773372693
    0xf010f0c050705121e070f0317040b0105040e120f0a140307050406030b01090302030a12020607030c120e03040308270d020306061216081b010207050a06052d07 70
    0xc8440c84044082000024019400090700224005496001d8142c4180e10780000301c0c0c15540803043e41e11a581171440000b0303075204004c414081c98820601a07200c0ca000c0c1c6000724100a50007504840c000c2c4010b0260006001d41d14046d4080d800725100c000444186c42d00c0b5030700d544d1031a40542c000c01c0b51000086145a00c040d48040200e50407070841e000c003421802c140300042c00034016406080b050503140e28100050707900c190001c1c8000c1d0b0700181141d10b64210382c1002c102c056141030401d00107010700000035101c24068029610303402041c0d1303160000c1172006440c0d00010860084514800c1c0020030000000c140040082d1150b2600c4a400e00c450413000900500c0d0400c02000c21805000840c0c0e03070034056035010481991000041e5283c2e05140c1042d42d0741820034010702c1d50038110440c04480403e54210004a050056100760b0b030f8402980741050069988021911a01340c2c4400d4500c01489601d109902a01183c0c0360100034074003660071004244400400c9440414420030301140c8a400e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 773375188 1250 773373938 773373941
    0x9010c0c09020f27030601030323190806010201050907290a0519181e09060605090a0911191407110301180c170715030501170f07030b09010b030f010f 66
    0x4e2000501820302d485080351004280c50f490144070103030074441034550000c00c5a185444012004107100e080d55603911039803007807007290b8141c112004001132600c000100a075005203c1c00e4004c0f405070707004041c89807500080c42001c2c40c0d82c0301041ca41d450302d01c407242065158200603084080e825140d40d80c42c0c8020281c82d03400c00c1d0881a84904022056148100d041d0b1400120f00a940b03441d604072850b06000c1807402d074403400591044400a140040c00110b0580c414083c000f4884103e411030f02c450350f601120800d80e0641c00443c0d68a15080004039451038202d080000b041c1003d061055201c021107500400a07000b88900391303002030b01324000b40081d1030207104424910703100c00c03e18131180000d619005608000381c051060f080b80307100340e03034010050704201190044c03810032101785060b00010b2000303001c0d207070a10035400a8030740440c4502185402003407800c002007130800109550392564a03405000301c40030703100c450155610b4929400544050204415184810001080581c064003d180 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 773376438 1250 773375188 773375227
    0x1050c0a1118040b010b0705031242090612011104090606030c0206011503060503190b0907030503090d020406120f0302070b1804050a1103130b0708070509010c0c09020f 74
    0x40c10b8002104010000341461461815607070300503071050303e0354494074085103140315000340900107801e580c00f0480b04c401000c20203026000c005058410340003114241c828600c1503860100f00c030307940c808100001c80c10034410056001400801006600103100d82003400c54201c0901c0d0500c40000003401d2000c0d4029006201c0144107501e410806a250118004e403100c0301800761030202a4103180c22249a8802e4100700042d06009081c3c42d489010b201c500d000d00001000100d45040c50500040e42a04010034824212500600550300d410481d10401a401c424204100d902036511400400c03001982140e111515200b440f4421814403142030207458814150301c000c1100f5402c010318085d0740d820345941d070404081564081500c1c1c9810000c81d020308120303000c0380e5041e00d02104105d000c001d841c058a1025008442e010819110001c0840d1000e0f401c4400d540801c400308044011544100400d65025000e1011120740544034501c0c0002d80c2e016281e0301140c20030209002143c0c1100c1203c00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 773377688 1250 773376438 773376469
    0xf0a0909060c08060f0d06150807050a170d05090328110a0605070b100b0c03070c05030601060903020904111e121519060909120e120303010b0901050c0a11 68
    0x440380c0341441c0064a030f0004010107a000d00c00210698040141e1500b102c20702d1b04244810492302c5480e01c3c01c00e0741e141514402c0502ca1104030100060301120310350380c80b100e248090003500c0c00b1401c591043d1515408000769903014860105501c003241600441d030700d080062441c80b856084c80c54200801142842c42e40707103200307044c8a907080001c40d40000880c0c10281e030001a50710165220b0428025011140e032140c0031010340000e039000c48820100003050014421550185030644540c00e050b5a0b100174064000071032a02d01c8144054900840e510340d115103d080b00510f00b204080100310041c01d051102c01c0c6881440b0800300c02460050f00c43e12140304402c0007081807000000680c0c98a2070050222190742c10172403510441c800141d00040040d00f06510240318841481c030b0250000d441007400d9000080c040380e052011458030740c0c120310b512000c030f80c01141564241030149200b0790110310307828140901044241c1d00d441060040000e0309000342420500c3c6c29480f07041c00000100c0802130b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 773378938 1250 773377688 773377697
    0x5120301030b16081f05030a0503070c090b0312090409061401140121090f0b09060f01120f08030601030f060906080d111005060a120b09121204020f0f0a0909060c 71
    0x1004943e001421985c04420007020560b801820282c0c070b003460616400c007d406005030384500c0700340540000100000352040714016a90b40d41c48054400715548600340d1075040c2c000444d0095150480760182c02d00c204011b200040d1100a80d82e81d60840d4120750942119518400040107120044411040c60b001c003070811980010075180b09104420380e0410300001c403540c80500388288808140b103000030701d0340f00501d8146d44c1004071690f55074507411120680d44c18140c3c8004654401145400c0c0000c0da44400c1e0001d840703181d60356804103900700402e8103041550315000c0c071001014a0048d80d0041a21a40014071542046011400c000d2510311400a0041d41c0941d52554800040e241c03101e1030100d400012182c441500203403545100340d101030300301c590821144040c050558030843c0103000c07000072a5941b0507008010310460050071340e85200d0383d88440018000d030400d212400d04895005113104034002c1000001403d0046a809c03551900391303104030304c0040054030300c118840040726051 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 773380188 1250 773378938 773378971
    0x807020f01090c03150204030507080a0c14130e010209130e0118031209020402271e06040612060b041e0b03062b050303090a0201090504050114100c05120301030b 71
    0x15031210b41003e901c0b000340000204040702402d03100c958183c0d4051607002058a8901d682ea0380400d0b81c032042413000b40c880c0c0804000c00078210086e04139880c0c500c1e00151078070341c0071320f884184d0380020020502c885490703540802c103000483e95500590741c0407118901d03000410200c80e40c07030282182c5070701500304910780f02007090f100865004200c144050480f150041a080c6461010601a0040d031050703a02c21b6003040080300900100403d01961490b00b84c0744e181001d48218808940101c410380b42c180c00100c100024859244101480250b59420403004260b60341d03502404283d5a005074001c3c0744040f2410248000d41c1210120312000380495408982941800b1000031817108210040e40d0b2040c007100d448e1050400707151180402d154010b801d5a40341c1c5089a0516100c002000d422170015210103804103607840c6c1032142c603043e02c2c00c00b64614540280b14044c03145034a00d544407141441181c21901c0002901013000018420111403c641c0729407441c03609240c413032405808c41c40e80c1041440e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 773381294 1106 773380188 773380193
    0x70330080f07030b060a0c0507080601030302030c0d0903110607030c0614060103144008090108090d14030c07051e0c120703020126070807020f0109 65
    0x209140003607503095801c4046890000c485a8485c03001c3c00342c940a0b074031079040c003910580b00340d0481c0d8203140c03611811840c100c8240e104600681c40007400b0300d14000b080c0030014600d09142061100a400c0d584c94241c580c1c001d51416020341404100a8140341c85400d1003541c544d00a0760421020030410030440c0005811100303e0f001c2410900e40d8840d02922a174804d200e100403510303620404003041e4040042541b52001c0651304c0d5020500d21706003136511404607911600c542c8a555a4910000015140010060500006da001111029401c0b504240025000274480c01415500d40c0d4404244450340075140024055126050104c80d0200b507105903004022150001c460748410614104900c4c101c10340b07007415140d00301c1c00f4100010750203980d1094448191020395510301d001890b0000d41c04108503142c00004000406000031030342c051003420100c1c0c01141c0203000040c800d4 = true := by decide +kernel

theorem cover : BRFrame.Cov 773201438 773381294 := by
  have h0 := BRFrame.cov_init 773201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 773201438 ≤ n) (h2 : n < 773381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
