-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0557
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:26:00.658959+00:00
-- url     : https://prove2.me/submissions/5d1a2d27-3930-487a-8e92-96a49572587e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 100000000 ≤ n < 100179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 100001250 1250 100000000 100000007
    0x507020d260406020a0309060806060a030b030c1e030c01080f13060212010324020f070204050408091005030901180b010311040b03070b2706040b030403020a210215040c05010f 77
    0x100d0300040e007902040100d00640c002800300e50b4030740680c840c0703100e040e9100401c80304000f040b00d016820080134000041454006d030000000064010140c0e0f0481c1c240102040640b1481c0d660311400c0b803c024014817081c1001e000e05c40b1040000c0ca0103d9040ca070840609503020400b404d030a4003149441d80c1e540900c511a03041c2c40840d11115012562540c0d00e0070800029410101c00d0501d00c2d001500b54010703c130b140d100b22071460485055450a0540d02d4080200820000b84140c0d0920300c100840400f07955250101490140d031030f2945500d900b0608405400c551054050308400305d08030140d00f005c00c00000c9007504481d4001d40c0040074030341100c0030601400107a40840d8051045010118541164101a00c000c0403000324103008040c450f0908044528540481c81d004078081000f0710120491500071030b8050300074011522003601c65560300c040821710b82034845245a00030400c10009a050008984401070044620b02d2030403e07483e403038401143c3c1c2c49182d0502c40220107015000b0701 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 100002500 1250 100001250 100001303
    0x9010e100302031c03051014061803060a090515040201020c060705160b030702010c021b010c05031608030103020405070503150f0111010e060a050610020d14090910150507020d 77
    0xb0b028081e01c000c507400d40b80c48610010740d03114003000300c1d00317040c001040440c0300a50481103484801344c482c000381c981c500f8484154003180c0c45182c108600d42a0082d5920708202490003401d00320000a540d131801c0c00c005050450851802da40c518905081c0030150307031300141040301244100c0f2041d59a494510385140703040300703100949600d802d006c00c00250083ca00c0000e5803181e10150000d1000862140c01240c07507003180e800e000c001e2481295220603951140c1078450504d480b400450303152200e000185901c4d810161411940400000014811818a8050203410132441d09200742181003182107562092803030a126401640c0580880803541c1c8184036004072040000d000304084401520303c40d1f142c17002141e24103c214205004640581014010410010a1f56014015050702c202c4210f900341980350003800b40410901203a561790b511511114020802010300000c80343c41c00180000c80080441110144001802242d000d81c94440626050b9a8021540145800c50004444c80e100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 100003750 1250 100002500 100002503
    0x203060607020310090204061d01090e07051909110f120a06090906050402030706020c130c02011e0e0d0815060309010213120c150e09071e02010c03060801090209010e1003 75
    0x410035141810840481d840403800d00e000ba641231041d55101c02854403801041d02d0040c4450000000412081042c1ea102c0258050b071b140c1074980595803000028a100c40802d01035104000c800410840c210462084d09030344207444030002c0c24504402039181d400e0040c2e14140d0b0403c182d010010f442105c550340144080e0041400820030041c090900d40c004100449040340644034441021a18500004640d00d000b40010710002d0b01c00541917841004d04080503010043d59210b03c10500340110ba0b406001c81e92844072030004400d03160704401c07440c1000b401103980034002000240705140381d941403540458103040d1111542c07500c0315410640284102045d56600007070118000c00c1e0072003031181c030b15482400b801b030a0b880c503501c9240c0110004404008503000c600040825841401c0410100383d2041850401056004545908291840e401180000140d560701050501c458051190070301a020b1a0700030055000d031940810382580060155420640c02c4c0e0000800b05940d05110348080c6 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 100005000 1250 100003750 100003753
    0x70503041506030b0a1a0a08060c0c010603240b150d020921010501060206010602010c020606100507020d080a0909020c0a1b0b0403050102090f0f090601051b030f07060e031201030602030606070203 86
    0x740317842d400c02e0740104819440341d103481600d1442c018041c80c0110b060010b03550810003912142d10707459082100f44d80425a8040d48c0e5480c0e0000001052501c001c21a012300c00300302c213190313014081c00182c080b02e00a181c014400c49160500000ca8a154000e07203003203070044080165a80049000240f00b180000c003002400340b02e050b4034803413584041d0805412603209400311800c903600d0710400c0e4240c8440c40402001a48004005511480e05200042041da0703c0d040440c0350101980101d80040d0a8003c10390b5a4100040d20709146540441c1c41002400c608008605202d0600c040c25210314071200080c000c00305216040104c45281c0c00080010516054069a10f5a40e0314009020703400c0781c187d45204191440510140d81000d0100c20203480c001082d942541d80c2c0c8900545140e0011010b00060004121100110301006c0005050007030440d10b1183e00d0f1141740c034108003560300d0342c5004296074000307004038400080501b000c2410341744d01c10000360703c99640344085403140c0102c1402a605 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 100006250 1250 100005000 100005023
    0x513081b1002040801060609060c0206030403030f09030215090f0a11060c10061a0403081b030d020703090810060303021b01020102070204050c030403110c0102030d09020a150216090507050304150603 87
    0x601041e94000d000f210242802070107a145d8461040d112501584100e202003014450482c1c0189005002036600a00c01d05001410b400508107074801c60303959110450162740100d141d200540c9007100b940d6030080003800102260041c09401980b19064103000401c0f81414108018140d5201c1042e1207201e41541c2c106e400300782c26103e182c80a40040c0c41054842d208045503a00c60702040320440d03042d42e80200c0380c50301c4c200e00078540f221540501003030180c450109206040e43e403001c5000800c8620700a40e035204100781030500d05403d0640b100000c0b40c0180c07401e00c1c02c00010350041400c001100240401d1b40c803040c10940140d005e40301e00c40c4020340c080e1030f1404010840e80060086c600482c0650342d4103081e1500441415038403140300903203e000d42d1050054041c00c01c402c3d0419030907284041d10b038140e013682e04c0b6444801d1460904c3e058015070455098007005800d203400790b0000b01302c0404140481d0901a9019129101c0070304090044501000c01101c04012500f00070000c507442801c0195 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 100007500 1250 100006250 100006273
    0x141b0c1e0a080c070e13080f070203010b1f11010203040b0601110309040501030b1f0e0c09060d0525090501080105010e040e100b010e010c080306011b05030a1e030513081b 75
    0x4440e00d45004000e51030802c400400d07136129400c42c6c08500e45a000c00100c1c80d0001910b000100c42d0801401260b05640310300509259031500404001175601200326006903450780a005003e40c00c1291041d0460381c818010080030030b590250540c1c1003c02070130291040c001c080710040c1144210500190440e0034a00004100001828124400c030030801816070f1252803240301e8031324a10a80f19440d2012603500100300b210032840d006095138a4000e2009190440c2e0285400554400300c0d0b030303091001c0c4220390030a9040c0400181c031502c56038a1600501c0b40d800c1000203003034810f0600079503041065000084100340c5070f60340401441c1907003104035040810b00240307050143c080040c8a1f8001400d80c41c400d040c950082c440da26426502a0340641181e0300c00004542c1d40e4440c88455210300d004520001c0800c400303100802d90f6030a255181d20a248038800c1205e4100c07007201030b0008142c6040200003111101b900303078000c1607601c03c03c207030342d90710f5400607900804e0050002e8070501e001c0d4421449 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 100008750 1250 100007500 100007503
    0x18080309030406110f060411040902371a0904020d02160201021e03030a02090f1207030209180a11010210060608010305070902030603070303051c141b0c1e0a080c 71
    0x200c2d88266200d01d00e40718039034000c0762a440100360301680c0b036006c00045030002c0e2081800407500000a40001903101d203a80003d00c6401140000a107001d140079408001c2480c240c00e24103010b030460900d0040140350103c0494641c1204c0b03810345c10f212000c41e8a500036500ca804680d00036280300c034195282c0345045182c201d90500791200b01d01521400030501506a20381e074485842c944220099801c507551030f84108040e5002d080e40b9540921303400c104010650303600d4180c04003400f24000a00c00b0b20304510610458031000b4203003030034520042c08181040607000654005103644010215469a1490010f0303160041c1300c60360800080c10008007081055105c015581264060001c03201c450780d0b10b00540381244410f50708a0b030980c004200500c0480c2c000d00081c5803a0004412001041d020701c55240100c506461404030240d00400901924050038040d242145030988070040c64000e109142d250f84020103140080500e12a040140110394103209900c03da9801200303041d6502440070806 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 100010000 1250 100008750 100008757
    0x204030501021305120a0f110402030403180602030403020d020f0a0e07110c1008010b16060f020c010c080603031b0f06181c020d050711281202090103061808030903 72
    0x40040c0f031180c2800030700383c0b0340400300156549038800988070110040d01e030070741285015801540c1c0070000400401c3d5640301c920055105902a070380344075410100114070320b09e0384165441384085500501080c0056600c200321180c1d2507030b04561014030f007607043c4d022440c030001e81e5001008000f840410012041c0e0403441172030a564803070041e80c0b0290028804c20150003001c1c0400f20010b90044010b126881c8110000c1c40c00c24058202036141c083d050780c401041c0c3e1201c003107031481e05e600815100012036090188134020001410400414981003012940c2c03409007000e2441020307031054280b03100007803c3c0081600d040d079900540b980c0e443c0840780048003038040e505100d010301c19044503c05240960700c4040c09a21950b0140000c801c3c20b00080782c3c00e401c100f00690301c1c58a003e0082d0103607918000c0c40b20100303590841c8851441c0071003800b05e040c2035269102039900c410607102c0f940180c0d181c411b424196580f009001640300b94640c0203900700301901d0402403115500006100c07080d0f00001c0075 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 100011250 1250 100010000 100010017
    0x12061f05031b070b07030c0c0b01080d0801121203200d02071a0709050907110a0f03030c0f080105060f040e0a020702091503030901031d030a03020c06010501020609120f0904020403050102 82
    0x706194911603418000b03140c443c641e00074050301040004101124801c0d0440041020103140c00d0301d400302d1684031541980801c3c0d00009040d031003034131510701064004c04241d004150307200e964005500e40d5110b810119000c8540c4004055452601005114024541125500f8081c0d0301c40e8503442da40b05001b0080d0701c80c4c4030690b203854000f0342000300c0501489a4a20510b02d82d650112660300d04024400320801c064542c00078810701d0f014040350b400341000004071071401003841b00f46405060030013404032401d9075900c404021000c80c10b55029900300c001d00381103940c2901c025549440b00c200300130b90742c0100c0d040b010f86201d00c00203100025404d41c0140100340d000f00d54180b55074640700b0f030075510f480000c501203070550401c0c07016441070b60095010031580f8090f05903155900302d030400280d0450348100307031801c040b990124254511510070002e0501411081c0010078207820b14403062980c0301d801100c1c20054003000078205444503481410740d103024070042c00030f5448648914202d4040d41201c0b0340b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 100012500 1250 100011250 100011271
    0x4080f0c13060303120c03060e07120507020304060c030e0d051504110303040f140307080609031201080606090c0a030b0303070f03110a020a1a1c06050108010609030812061f0503 78
    0x1203240103081e0351182d10126541919481c00034103005078000040d0120404000070f0558410340080d840c8000f2a40c51711403012562420044191001204105e443c040c5c1004d0455106000a00030140c0180b007490b00e00760942021704010f01044005020240c3c00b0100408078051418060f000801c040041c0e806180b050741d182c1907520144080c15520b000c0ca200c0c80f641584004010460040c50700948000c244004e01950369050300e9800c0c45141c60f000303688882d0b0341c0c0c0c000280c00f0424080107a000d07001d000c2c40740203002913041c0f150020300300c0f4001034600d0200a0002512404541c0603a0240c03068810107000e0b07070384440c1f250a0001010895040640204e43e204907010324480c004500c40380c80e598014101c00f802800c2040d014110b2001c81e01e03440c40b5440401102c100c01d00b030b02d03501c00461075590002040c0e40b81420f0006010000c181d00540c184401e01c2800e00014201388155080d4000801c41c8203c10795825000030300c029020180100d61866200384581e149034084010351203007034081f1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 100013750 1250 100012500 100012519
    0x13110c15010603112505060907090f02040b0a0509031c08070305070807020604120c080f09030f0d081603110c060a060f08070b0f040b0c100c08040201080f06010504080f0c 75
    0x280e09603031075280883c120050170003c8a0890581006202214030704400100c61000d9541e281840d000096401d00c00561205500704100d16460098001c00000720b02c081d42824a03042e10034845001e0000c81d5802e0140202e80151207850404c92010030b04024204528040d00b009005000c040c030507a4884002404c0000207002e060242e60301c0390080c1e049500908407a0b84648501c01003881c0030250f40c007048441103801c0045001394001d41701d0b41d140400c10f01d90310f10b50030301054940090490f140486800c43cdc503070000c0c0e10b508130b6401d56100121500030030101d440304204800a101410811030801c0303002c51902d050075000a046407181c40f051004000f0781d600c0c1e240359202d013440c42c880c0c04129440064140801c02c000d4001d440d07a0f9003000300290806444034102200340d0014841b55070264421030300c00e440e008080c040d03c022680f5a0a010800d401c0c140c00081c20000024503130264886100c0200b0382d80d901c01e0044030000c100300800d480041c1c10288441c0c1d01d07080c281c07002a20410410 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 100015000 1250 100013750 100013759
    0x4050904020f0a12020f0d031b06110f04052b1106070f051e0c061b0715020307030206010e040b0a0b01120c0903053f04030602130501260613110c1501 66
    0x111f5002d038280d4040e2900d60a5079210000c81110b0800310004540340303070b2261406407403141d040c800b6055210804080b0f0751294206401e102409a1010035040591484500700c007840c0404d07420080c11710742001a85417a032014001041c00352140040003000b038500c10440d141401008136000e1042400741d0f0803103c11005514211340c0c2d0b424946080341d44000c00700b003480e2502048103044681c807022a0140c522140d6600e4180c1320340d080b0a0000005a080001d41008040c1d0510226024028021081c0f00c41c5c04c0a44450540100050800d20225030381c4800302001da010b4490803455007480d501c148020300b050f0000030036142c4944801c407210301c54420041c039a0f03030041c0d100d58031800c80321a45404503078045104075500c401480680e0110301041101202041082c00209902c11140f03c46048003807600e800101003110f0000d02d03024240340d440c680c240c008840c0d8842604044103c84117140c5401100318040203041e605030f405443c031f40c009460020403402003103514400b0078100c40e07003080c0d82c0d0b107 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 100016250 1250 100015000 100015009
    0x1412070503030a030c170103080a12060807090b030c13020c100203060904030c0201091805041502070c03080a0203160c14011404061d121506030c0604050904020f0a12020f 75
    0x503000d4298980c00502c4042c15541c400d9010380365055040c034014100d00790704d60340c2450050080e00280c50014001507500e044a030031126820382c01c4650241080881d1400c09950f0f102c1c0010300031040604d407a0b03014651199000c00c10341a000000400300e800301e8030a00c650b070000b9405102d5500741400382400b40c03005010b4520036244030328000380c142655503135103990485007007917042c400703d0500580d4500491280c0c0701d042c0d428100c01240c1c0000030103086c917050003038030007207000c06111006004001110020f404843c0100c112035225a18580300c80085901742c0c19801038119a5802d05810050702c030511142c1c410003022580b241c0451440120039600440e540d211b0051094000402000204011031168202c0649121f0b00040220400c0c920b00000c0c0d000c41c624a51075410b54084039a004643d070556008036002070044008080201c40f040204119000f24840c00c0d11801e4403030005805e64a80c07040c00840321400400102899441e107036030306982d01564500342d0241c1c01c5a014000c823400c2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 100017500 1250 100016250 100016263
    0x1021209030a150e2505120a170c0d090f14010c080c0a1a07031104050a0e1305010c0f0e0604050915010c02040c031a030a1101050c010204050a1412 65
    0x10260203080d00040d251203145120744207000d4880c40715a1071140900781030003480f034400c05d295015168400101c2a1030304140c03840315600414811440c0c0403881b9000640001e00b211080c0e1301c00c005015665580d40544018010003440308514042d880201d1002c86e41b250740141a20301d172000b2084881d0312405242e4104514081c8180880c2444600030041030301480546107560302c50044074a90300c1655110741d0980408403003101f44944480c01c1c095031541600402c00e2812160135804d060900d00303400034001224512604c510090450003262014050060000c900d941041c0284041c2104c0341c40140400c41c2003086400082040c40b14520510701042110110b0f40b00522500d1103446000c2002a14151607150a0500c12800c1e5040016151801061031507c0c840d00c00003440708035018000a80c84501c924948680c0044110200107840e034000c100307020100f07103445a161440070242600a12668001c154041d1b0241030019503842d0340701141010703000650381c200c3c80500020340655100d1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 100018750 1250 100017500 100017517
    0x109020307020c0d05010b030a080301030b09060735040803010f0e1003120215090705131b03050c0d060801060906061e140912010e010e160303080a1e050105010212 72
    0x1c10801c408000fa103002805104038600842c00011210410800249005046901100d0203680800100140b100050800f0392190003500038008914090400800021803000c400c01c1d80035459980913140341e421120340243c2d400f1400070400c0c0d4205030400c50f02d650000d2052101e0180080c60100d005091900140c2c0100c0c1c485544d04141c40c1541d80e0f01025002c004550030443c4504810350344200c002d268685e0090305841d01421086081c0340c00e11511543c184890600700e0f00b4010713002260b95005124048500b403a01d40007409499880c142201c41c81411070160f80a42009c070f0204d1803800c10360018040341c404010402c040c40e5280001e607000d082110074000c2d0000c000c810080224055a60728405081c110355892601c2038410006554000b880c8000203580e640703081282d0420001d2103103103203049a0030300503c000030303103142c1891513010f807400000c00304a10b400225070b030700350190840003030904002c1110400341d1480503244010f050901c152801482281d1306040074040e1002240c008a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 100020000 1250 100018750 100018753
    0x15080105040528170f090301051003050c0126060a0e0405010605011b03050a140c010f020d060b072003031c140703020f040b09060403020a0b040e09060c030f04020f1207080105010902030702 83
    0x1084c0c5940140d1075604184426540c86508200442681e0360030310920b403056460102060032241942403083c07030680380c40d810300d0500c0003a000c002c03420303030a80100c0c403d60401020340038640d55480c000b10300c3d00c0e207040c2c0c050349100c003485007030200b04407040d003020069070b00030390b68840003007280690401c48120524001e804140104400e164040c49258800d14500410400b107152103450030046003191410b42020a203140d0203d040c840342c447c14065a401402d83d885000d05010241d1544280e80304080180381c45080c1182c0e011190b81c4080c0265541d0110003031840c6001e00c1200c6000c00070f03000803501c0c0803030800e05800040103c2e000c2c0c4250b503803006807a9189070134142040d0a85e215640300d541000d41c850000e11000005a646100b90b101410f003084104e0340305d6240c80c00318840c820780a070030403115810034010003505020741e0082c1c070340c40701c0e05c04000345440c0c442c1d002182c1c0c80780244007007540026111800050104001800404581a05000308126aa00e07080ea0040340010b56908005 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 100021250 1250 100020000 100020023
    0x30405011403040c0b0a020a03030e011a12250302010e010c0c05040902030a060903020f12090609220905010506030d0203160f021203031f0603091515080105040528 72
    0x444038002e1903029204920b00c5903090744a141e802025048980c0d0340c03005901c001e8400e0101541400b030364500c289880b00a1110102d0a060302c1c0000d40e84041d9580608420141200e01000c10000e42c1c0c40304280e146080448018040d0380305042d4621301003a408200d06100f40003055229001c1100c0d1681c11010340e040c040c0c01c2000f0800584048401a40d2603c43c0c400a4000b190075072064040e850f1107600104000c41000b011181808841c2800003400031040c1b0802c01a84c44580844010f08001c84403074404810350156001c030b0848030006100c22611300a40f0504000c230540c00359010700340c200c0c101c44401e01055030481e90780c411b107904100c1c40b18041001c2c0300002c810070103241c0d02a2000309515484241c0009541c03964100f1150060030885104110081000090103600602903038502803040b80a5900e4100c0f0300381080d01d5001046913070f143d14110802d0b2a4240801510f042e00081c4200d082c981801c6540c0e07680c030781c0c12203441c03c000010003024448420007080f085da40302d01c00104 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 100022500 1250 100021250 100021277
    0x1211180103080a090506030f060a0b030906010323030d1a0406030503070b150d0506042f01080702210d0b0405060a09020d021303300e0402090a05030703030809010b010203040501 78
    0x141c0c0005070200c044c810502d9000c0ba076603850502541c45001001c0c40c44469140040800402c48025840016416800c10601050050205400707056a42060050340c1c5803001021003d003840200070643c0c81404081181280c0600d19080710a26880d507a0300315041c1580c1000f000100e404c9032000030901c1c0c0c020040c0200042018002c00da0051125000d000441e0400c2e0119040e1081d4160444160b00103000704001c116003598aa090b14030b8200e6041000c0e8503402d05081901d00c410201030503c076034040040d440c0c0c1e00c204220654004d041111001072988041045416004080d138601140e0034000310f210182064800c042c400c0100034071075001c01d890842020000d5210305d682020142d0200920391004401d110040e00941c422030b800c10400c42000300e07011807210a00d0019505c078421a90901c1031541c442e50031240c0ca40100c800503900c0e83c05800203038101480e503102c030390140a0360700000b081c5508182d9062181300540002e0104540403401281c8a205902445004c20703d003204811 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 100023750 1250 100022500 100022513
    0x9030304090f15030507081002251106040f1a0a050f03040303060305060118290609041d0304060212030103080711120124060c05060f0903131211180103 67
    0x85503603011001800f000005145400c02c00c990f041504c0340c0d4031101d010851717460304000080104514020841c200b000038040414481c2e2440c41ca01d80223800702010209000d802e142182c000440182525507560345e0f103400c0c48100c2c07510b00c14403001701e500c102d0320424028104200d80c1d403d8402e5881da460705a12001c84541a0806031064040507076403100800081c40c1044580c1c0600340104150310303110481c0b0603c2042d240700300c3c40080c20001400c0ba0340e08075004101c0e0088a4481180d8454480030600041002440101c65160740c0204208401c03450700c034040014425584540c0c280d07010314200074007030406840b0a110013080064104159000300b00f01c6500c44072040ea000b0100302501c40087d140e642501c5600d00340341850310724610449000e0000002060080085007030103007800c401c640301c1a864400040a17008610040000621410000e00031138080f5052003d07203440181c2c1720048044501e4400070111250846140803032402e14001c40504806040780c81400c841d61b083d980d030003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 100025000 1250 100023750 100023761
    0x1506091203050c0f1002030f1302031f11040f0f050a0b09101209050106170c13020d09050a11040c03110703030b010908011103060a09020a0503131b0312080c0903030409 74
    0x14402070154a04090b51220f0500184240b03217185074001d030b02c9060000c8084d10840010b451342c5d00b41d809826402d070041e00c0105484201c401c0d00d0400c3c00000580c58404801740c00040c555034580c010002e00440c00031014003403002550905200850401e85078400d008052115020320180000c0c1070252600d9071800f082c02601c0c40d18185441c0b43c0e0010550b000b04199208100d044400744d44643c0306100840f101050713032408030740960080221401d4640440d07001160043c0841e040340d0006204814000244c101000c2154050200c410b20100c40c00e0040071b031840030905500c582d04081401044511034000c8a03c1c140034000300702d2501101d542e0580060100700401810f0005031b441c00100b4031401c0c420100d14080c10040c0581c1c83c500042084031222031070304031034a10b5205016180d00281d0040c2601c0c1e00c5003a0340711a603000e00c801e0900e444818607100010711504c10210b804000c001c4005104105040161500319640c1c0383c1d115220030034056048400d42607401400100310307110703541c0c001c07 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 100026250 1250 100025000 100025017
    0x2070b16020304090c0e010305161b0f0f0507030605090d0914030a0501020417010b0904050a0b0a02090307060e010206151309060e010609020c0f0a0f02130e0a0501150609120305 78
    0x101c901c0d05a40300d079030505079204205d100f0045007034405142c1e401d58250090542c080369280454441e00807100001c2c043d4610f035199a207004000528031001c000c80074110fa582c25400c10404e800008943c0341455441c0c200c2d000840d027090a000106071440000540c0511090407500d80907185030410f0300e11803c1c11682c81c50290701d44a01c000ba00e001c03640a1006002030304003600d4a40c00001069000e40c00e503002c0301a42802402450100300100e100454144103060348020740c80255250400401e0280c041c0103812b40d45409008400600103420109113032002100b0380a90f500340c2d488810041a6400f4181810303049004036501056641c01e81d07000c040b8591203400002048026500b0103030845105402102c541c3d40d00143d00c4a03080300c1084034203060041c10000b030500000c02d648021071000d09440003070040310440700d1035000990581100c2450b44801c2d00f00c03140c0c06043c1c1002c0c1c1c0a401d510301c0c0f001d0450207014000c5203091049110341c040d2000300c034408042c1d08541c0e81c100c40a40c005900d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 100027500 1250 100026250 100026253
    0x1d090a080a020109060603051c110304050f1f080711060415020a030e060915100b090607060e1906050a06140f03011103160306090207050c0d08160606031502070b1602 73
    0x12400a0814401c6c3c001560103480240140b59079209481944807904403070505000035045050301003c4000b040b9010340320103403059400000314038080b03144c03c202401700903c8110240b413046001640310340301c141301d03034030643d030312070381992a04021030301d4000585024000c1306029281480303419a0f60014441032101d407500141d0b656a00c1003040c10a0300544400354a90007a030040b0300c2481007403000c00d4124400d1042c41500603c0d003c00004107115250190f8040e0380081005424003401e41e00c0041000600d105035025552110600d80c491400c512007141c945c2c4c1b620b008152144803030311982060f07e180041403151501c0c50000c2114201c200070200e40c0c10343d2902106030900c29180c019500540c0020101c400b2001c80000150a94615421426601348103000303845c040791002400d4180d4810039600902c4000003800c14012a100e90500390901d0501035100c00104602a0300102c202d80c05070002141c055091050042030384034a06000e07110607003030000b060b842400081c0040c07565800b0300 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 100028750 1250 100027500 100027511
    0xf0b040308061e0d0f02060d0608060612030301080601030f2102030a0f02011802040203060f04020406080a05060d020114030718060e03070806011a0f2b05060f3001060803041d090a080a0201 83
    0x619003c00d807227194000005c15085001480024201900d20506100300e0308041c1d81036604000805031340e140140700c090f00117290707202b240e414400e4201071801d44450078070a50103001005070001c3d6603a8004412140064129002411aa4410720901e48211400488452011800c0c0c00300300c00380d000034214039400b603180c502c045055900c0d480188004e04603030701c9007086490050303c000c0c200c90b40202a107000f079402c1d6000342c00507070384040200f03500341e51802c0803502e980740c2240850704034031941c801c101139164584020901940040542480040417011164002d40301c810712a2600002c1c4030303c5504100d84407022110018020280c05040c181c609510704000c0c0150700d8142103480c803401580785041c600001c000d49043e5000c0c103075100c01c00f03540274495080d6400209104424070402d00100c1442190140e098011000355020055003100090008a40b40d01505403254003900c10000c40c8041c0319280450107018030201c0b84100d0001010f0902591140c80304080303580000d012008656995 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 100030000 1250 100028750 100028767
    0xe06010c150507030b0913050303010b0c1c0207090c020304050307090b01050f030f1506070b0406020d09020d080301150c0c05010305070509120606040c0512010306090f0b040308061e0d0f0206 84
    0x1d00c1107503c160582d507004900c03901c0314828481c402030702500030020031101c2008000864000011030b41160b040d14210796841011809140c2000306030b1b4a01e030400f103071003c05445001d6001881009542d64400100244028044180c1e524801c2d88622901030f00001410040600641d0003070342e01c80010304250340740001c0048542e0441d40100c1d900009000b0500621280010050840441c1207041d100c8030320b46819a102d9a1802c140104010301c00e60300018540d4121a05401640c107050307010707040005e83c1c10685400d080c580c02c02d008988040c4190700000f2903061013040d41c8480160060154444141041d00440103060001e041c0030610000b0022001ca40c0c6403510252100300021010b000d090510340d0402c4152200303644850304100c0c0900014044194085000b070450b0b078481c0000420003024541003003982c0744908003512070401c0004000038075400c161034900c9400111645200d01a003001c40f820f00302d41c1b402d81c0b1307500a60a0b82884001070100700c4646959400202240e0a1100c130 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 100031250 1250 100030000 100030043
    0x122503020f2506091d06030705030102040e04110a06090b030406060b0f0d0e030307090e130501020c06010e0108120a03050921071104020301030803060d0f02030d03050f0901060e06010c 81
    0x804107000300c01c070700584100070403000b0045180c050003071880c081040e00d2604604d400480101c80020007100750400c0880d4455a0030807184000302005402917449030390340d240748402054110303030a503814005118a40d410349042a1024256807241c0c81b0154011705144480007560401001298050ba03540d00120300d0841d034101404503240460f401130f0b550300005100c1e005690030018014000d620600600c4055500080090141c60300a204d065541d03a0f002000300c0b550340f4021028045501c0011030300f00111004c070b10300381641c040c605030610a90ba1003250641d281c1c90000340d00b00c504418402c148850307229800c0709030005004c0b4120340720b070700200820180107400c0704248140140d0004020080140303810040b10b080310111030031401c641c51520303640103d2100400c01071240c40140c80500c10171080015186010340c0240440d07809000c4907102900610342511a465403104070000146603401c140200ca0a58400c001020386503200c8200540d2444204030080318510b1070035040c042c90144 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 100032500 1250 100031250 100031263
    0x3091206291207050901090e030409020406050304120906120903110d02030414040b0a06140d06030605040308010504020c0a03030b1816180303020a030f030906020c0c03122503020f 79
    0x8800448070300100d038104100070040201c0d03030020640c008500410859503035212030303411281c5504010403031409025140342580304075040002090320108011034044c1c0d000015621035441601981180340440344150b40800c40c0e4800c140014100c0c0720001d140c0341e41c0e904001601403180c00c203021001400c00c0b88a04002c401322440006a1011030b040201c0c0030440e9007000160802d035400c01c022002c0501003800c2c1d50381805100306001c07815060098000d030140c1120844d40000c80304100712a20781c07800c003028220039202a0300040e801700020400380307014801c03226401003030001810085000c1e54140c003d070803d0520540d01040142042d2080f803403003417803944500c0c6040748a0300410884034014005071840c1500c4214100ca41e071040c40041d800041524071182c15040000800e1441c0308110060054048020075a0b030000c03070314166021000500aa581008074140c1c1c40ca204200420842c5019001080070001590078040244030018030180041e64040d02c182c0b9140e80200d0140c0d4038240 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 100033750 1250 100032500 100032551
    0x9050609060a050601030b01020a140f0303040507060f05040b12070e150417070e0403180b070b06040b01050f07020603040203010b100f02070b0a050a03050934080a03091206 76
    0x10090020041e10842d01d10805511603400d003820450083c9545c0002d6550001c42c400401d10211030454650348181001400d907401d0040703080320b65038170b41031416a844030300324814ad2021900410410000c94051429a001c2d500b0511350f040c1480d100d40401005640040c10040610174000c0c20b800040e128601506043e503c10441980e995241c030840d113200409114150451382c0100c2428082240840c80030790b08950946043c101c003e01e42c41104e02c0440040c0d10459002c1d000003015020882c5e10f0305803030321440c0c017140c0401964100310700650b03e5100b00150340071140020040200140742c04d8001d9500940060000595101940003068014012171322541c04101030301d81001781c2d1641000220050500001002e04000b0310401c054418029500c06005043c2c607180090810b1500f080781205501908040031006c900981a4a200d80b00600083d8400d0030041c10120704014002030083ca0310b585a80d9120b411841c0c400081c80c0c104c4401e030300310360041d01d0364010001a0740030a061030124 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 100035000 1250 100033750 100033753
    0x221070f080d0e0601050609011b05070e070909050a051513090c030b10080c01230c0601030605060114120a05070c05061006030b030114060f0d2a0b0403050a020d0609050609 76
    0x20300c50044891300e06081640700c18800d010400000b03000e80d074410200c0d00d802c20944019801289240b421504083d6660400706408841104200748076a01181c094100c8452003010031885c1c032a9042641620822141e5107200d81c3e84801c2100107042503144034400704410100003c82410941d158400c080b0568000e4a40c10040d10a100b460000c00318840020154034004288203500100003a04102c003030004046010300d0702134025a50700001e01200d40180b404415108990b840345002c000505003520305038006440b901c03040b81c04401c2031044504001343c1040c0c40d4010380d145c0c08004041c00d030003041117040225040b40500050300401c80300b40038900c0c1c004404001428108001c0032a00080710151203681000120303034071803080958598002d40d00ba900403024285c42804100940b410842c01400c00d215a14000700b0f803801c600040829203241403541d400d4980d14000306569002e0380c00050907a4000504100040c030780081c0d509507040c071950740800c07000740300c0d04c51a051500403148040705 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 100036250 1250 100035000 100035011
    0x5030601120c05010c0c090902060906071202061302091f050a0306050a05251416060518010504120813060906020d05010906080309060306040608060c0c07060221070f080d 75
    0x4104400ca40d03a00540f00c2840c2002009500e80c80d100240f848622410700080c2d911140e0800f552140c0017200e8040070040c101c650789500902d45440000c940512800043c0200c40124010801c000c440744200340d00242566601d440386c0e4009841e1420004c0305400b03180791035100141507190388000c0b000441c0102400203151920400040c1512002040c076440d100180390390f010060b160103c4101102500e2410429100c80c640002941e8455400c0a82c04084100d01003002c012075508124031a000c0051500351403994882ca83e8242d440c203403801403001849450106844d446100110342c0300000c24024503c42410b03480c4d45048410600b829280c00e500000c01501c3c4004a0003428010703c1d0f038203010007495180c50003a90301c0b801100c00d010710400c400800702c0c1081c0d64a03008a4003030711808081e1111030038008500242e580c000c83c3c0513101802409400075580c1e00208000c110f4a04400c0c4ca007540a84041044a0a42c004041240d80880100d040f6010400c0640904080e140e40b0a00044 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 100037500 1250 100036250 100036253
    0x3051507020703021509130204171b0109060c032706030c0e10050a090b1602030615012a050d020d03060509060d020d050708010f0f0605040c09051005040503060112 72
    0x66204020455400e6622607001000141c030f610410881c000308414030982c41c0d0501c03800003400c0201481c1d070401c1c00307070002c5400300c1c4440f032007000940d102101c041100c050300950040749080300390b8002c8541c007040740f51200700229406640d040808500c2031901011a00c40606044241101b0880324041c150b0643e0080c0200e90f01445540d40340340703d41c1402c071084004440001d01401e544440801000400704d25510140d0086c5504400780098610a0341c07900b5140e08114180044404107038801c1c4a0a07011805d0350110040c0301e984003406940d481007012041a050301c9488c910400a06100c40f00c0041001148081c41303803c4903020700c0d41c048c3c40340c00100c140080c203852403600140c3c8254a0f003c02d000d4207035106050071881680c16a07076040c00c420141842030809940d540804184c2d424840c4402c117035280341e03200c0780303c201d1604020029541c84100703201c1214010591040801c14940043c821480c3c80060250510754902d032a51400792260701103400c0100aa00135180610030315076140 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 100038750 1250 100037500 100037533
    0x1605030a17070e09070e0607020d08070204050106090e242809230402030c030609100f050c0702040f02091005040503010e03030c1b0102070c180501050102070b090909070503070305 79
    0xa40059082c81c0090070003c41c580024900b600c00b038141402e2051040b01c002c800e071220025610400c0d0003c03c2002403400d01e06000009a001d544100e00c910301e02800495440c0c01020364005540300441942d40e103030b540940011b80d203c210f01c811980c009a042e22207505a481141e03140308501e00c050700c0070170811009156901e80c14580c0080d881203041c070300189007051500f50300000c1c55006d400c400c0d03816111400403d04001d1010803050705801940b0820003400c000141c3c2c4000680c3d011300410400307200b4905a000c9440c1500d50f07074414442080440c0240c60036401501d11703109003c0d070040c030301024100007502c40242d03610315402241e0003041c1041715150a2040c0708560381fa00014600d50300c0c0c030070200541c0b48541201410500040c0c04080c9100c01d00751305440e07804e41e00c515100c1c51142c1701c10200c0180308101c001c403030805081c40b00126140d4800b003001c0d0216003804c40082c3c20034840c00108400a0402030101c00140310322100046c1594081100d07500950050780501018031003071400c51f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 100040000 1250 100038750 100038797
    0x4060e060f0606071b0b03010b03101e06030218041a1315030f030201021c020301030203010e0a050606012a06091e0206030601080411040606020304060905030c151605030a 75
    0x19194031481204001140d1251001c49a004c0c1d030040051200b00b045040c1e040b000c403c03540058401c44000300c004580e40100c6002140070340190300c4641e980950301c881c1030440d9102200e044004040d0710104001c0309019401070001402074004081d100c0340380d00046001c44280c81162030104000c030010942904200145d042040d51220b01480081c04050352003151642c50311005009020000000013031520030350507a071800d040d124540d45050f0458000d04007039002808181d11070351030320100b89252100010300c1011039a001c1e000e0083d550b21440113450722410100c0840c41e802d044035a000c2c01c9031107400b528141a10640300024401614140b0650221000341007800100701d2001c4c5030b0240e91040c040d01d5204000b460701c401345a8952800850524646140982041c1400c0011600383d801002034019180c5079550b14620654031010107036100c444034540c54004c0580080c0700098009078001f0406100c00750062114411961b440303500d550f01c0403020200080c01c40b01c14190310020761115 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 100041250 1250 100040000 100040011
    0x1090e0c16080438070f08161a1512010b093c01180e0d090806150f04090606030206070303020910050903060a090302160e0108102c07090504060e06 65
    0x85415044100007100c2e40d001070081300100d080d10100300d40301001101c1c01c50561040c0c1c051601ca46450368400000e184203070409007114514030790311032000a0003c02821603c1103a064909080d482203c1b400c5c40801c11446e41000c195548406a0240a03100c09000601442261089000e06096082e0304059218021201c3c01e224514007040e0000c00401d0211906540741142980010403508500340000c0600103a41c001d540144003800701c2954203c04018201da4800003550402d07070711031000da05e100d801c8407002540950141d13068400b074102079100a1019200e09000100103869400040d0355800c00002180060b8001460700c1c2c013403d001c00c92001441d6581000c5044c5000c080019131250002081c40421a5540c960070003414820080203800c010601c0f5112003440c0c030388180074142a000d000d050070301c0c46407491000c2500c100c2e10444003105448602c07510258415104a400010f00445070005071003440d0340030903e2400c612030140502d2241e00c0004600114860306070a20000509 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 100042500 1250 100041250 100041299
    0x90509070315020d020421050c0306060a03080f0c0f030d060f0308030a0e010902090106030c02190c06080703200c0c0901051e0a080109030908160501090e0c160804 72
    0x8100009001a9582d80d0340a0040740d000d44c8401c4c000318054001c1c082c50344100c1841c0400c84104c003122844400610a41d0b0040040d10746080818082c1507680b40701f5251a90805244c040c00c00c08544040080c0000469810020340340c00d88800c0a1880c0080507101d15080350800224014108003912440c4010160a44600e81c4039141d40c455064070f00004080441c0e140d16404580301144003076003e100c216034018211030940d610340f04010000d08250151202501c1030312101684401110f03000780c01e09500c141204421402d042c01240c22100c041c100a05054036010300d04041001070418503080d5285108040c2c0b01d030080110789103018036a0b44280e01449001d0018821342d2903074141103c0003010304c034940780c130007103c6000328184000355030066071030703502e041b07080410140c0c4101c00904031260b0204a4203204868401c00d8604005031050f9404101c1e02e000420101011018031a40200b580300042e0400004050341d15003006002021074032824006000d100c1701c1d445420302d00480c44110b0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 100043750 1250 100042500 100042513
    0x7140310050c040504090201030b0d030503180102030103020a050402071a040f0b07051206010e0102150a05100509011211040603020d060617030c0a02040e1f0c0806010e01020303070c0510020a0207090509 89
    0x851907620303225502505010303a1b00c8031048803e690080c0c00c04094040050039104103120700e400c00602c03d410a94014140e600b01c2c40c002d0090280500a0380e05a9400800035190380b8980400c200081d4030101d4200c42c17a900150100d0b80038020007901510a81c003170360b024092a00b0a11b050031090000401e00ca06002043c03102c40d40d45000c24415541c030400a00b4107424401070900141e2810181a03480000152124100290ba941c141c03c5103005283c0b05041941e07080c0c4071020040111800d02440502d954540c40390404a1416080440344103809407000034541e03286d80114250070810503084c0e80081d01d82030100040e00c0600e10203004008078001031414142607402480c0c4407040316001038401c81d141c084c45005004144940b9030111a8442c2014146180c1c44000000d0428110350b0f0000c101c41c9070001d0419409120740a0424505034060341c40c541e80c1103029500204690000d40302445800c0c0c10641207540c40c4024040054150000c2c10035500e0100007a0a07903d00500d00c2e900b5410a1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 100045000 1250 100043750 100043761
    0x30f0a0e01081510110318040b060705030711180c070201110706020a080d06050303041701140105091602101e0e0c060a110c03010207030903050606040b061903020c0714031005 77
    0x202549207401100da0b04016401c1400031581c845c03014a100d6514000000c00310443d400c015004100114140c506001a1303034801c1c1048541d00071070704060803079001000607600103610700d1310034449284010440405000e554140c0c400c07a800c22145400c002800098003420356800c8000d440b2041c0d101c1006212041c00c00c00025112141d980c00289803610106400c116001d40ba00400007030580542100d84039981c41d0000413101403001340c8440355500c1e2a04a0030078022001d96217040e00c40140140000e9100c03203107545495001548510114001c0c804480c0b02091039010300c001c500d4425540e003c07c0d903504002c107003c48a9100310b40305190f2050b5000916911000f0a0350302620060400c040d420316090041c2d820032090300c1c4915499440042c150741010f0b00000c1c6e41007902d0161003101c800c0c2e602c600601044400003c102c1c2c6c0e200e0014402141c622607900301c8100000018a009424441a11042071425045411610a095408503d01014202008520106000e00d203060000d070400c03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 100046250 1250 100045000 100045021
    0x30e0f1002070507031704050a060905150a05070b040605060307081504022407050304091b090308030702010605060309010c08070c080304020f010903050a1a060a030510050414030f0a0e0108 83
    0x100e4035450a1035401144450070700c08140902c1d001150400c4d41480a00c101200c844025405800f860380704844502002c150b0328451a001c2d819100040d24940028000c980c0510301e0740c2100c4480000c100d0700308075080014040f00020750060784211030104a40c2030200c01c05080ca00070340c200381a1907001d42c446484042000c00c590b50069015a40000008042103486200c0c40264180081000380002c0c400204940040140110350101c49d0401c41943e4110318503c903004824004000103a1030f44d002c0c00440c542400554004980d40000a000c0c5c0e0782d64040340003508100da1781c034002c0c0d6440c41e0114240350842c11695010b0f40e581741c070380c0036440b080d0355440d050300014002a00070303220b40c81c1c0c8001c684d018002c1d64004d103400000f11020070400b8505000d040740c03400c0c2498103804002c004685c5500704801d229003501c1d0b005c00a4031103940303030100c1c0d80300070000140240d40d9000242460688100248020030f24100d4052415503202d2161070064004143d844255040002510400445281 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 100047500 1250 100046250 100046263
    0xb01110f060a0905121602010f030e0c12010b040f0902030c03070b19020717010c021501050d0803090a0618030206010b0414010c060b03030a03090201180803030f07051303030c0201030e0f 82
    0x101e002c0050401d60508065103008828071000007026800076600819a80d9010203201c00e910076640c00240c000c041504800380e508540c41c4a101c2d03400798050180500c0c1c00c545030080b0031500f400000700c144c0d00d0400203050f15048429011120340e00d40d00c4006508050109000c051000da00511075036240c5440484544601003692551400e05034410700101d10a1203240c006021174444c10b5a1805403c003542c1c02440c0300362142000d84104906200001c014106090482d1801000e01d0301d030410540300c4841c19480140300503094015074202d00c000603020b01c540c024192581400e842803800030301d0040c0c5070207010382040d090010244010003045030302210440d200242031910782010a614035141c4090506110041d606000c003180c841080b1f03906602c540c500c0e5000f665062603818420700e400103841414003a030a1503400070000100e2030b0070070024040c6c00140c5490898a8162525461035140000d60011800030f5820b00382d0030150769050040030b07003c0a0000140ca1004407174000c10703560f1031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 100048750 1250 100047500 100047511
    0x121112062d07022104120305090f03060f0a0c020109020a17061005100509010210051603060504050c0a14041a030109060b0a121a03010504060606020105090610060516150b01110f06 79
    0x190440c500070084c50042c0c0507100240610200100200d10f00d01c0c1c050540c2d0010001d060180038941b06802c4940b0f000580540502e81250525000340c88045c1910050540c000c5440c0643d900e56100d02c00503110307642910024a80d90000301e0900d100c980301c107420000e01804070b5000b030700b02031014000c035600c1d011014080c18103810460355890442d40141d0412110501c1e4084062414082000c1c910149804407281010390f1341c00c000464981041204541090310b880c0c001d1003040c4a580c0030350b03006500c0740d0b140c001490081405d003503507901e540783d102d01024000c200c1642e002c00100b100c41214010b12001d801500c40d1203042c030b0101d1100501754005070046140c215112441c0c1d100c29186d8144620443c0e01c090001d10507446c0605020005c1c051354490b001c019882c00c00011070703241c0e01140d2907004511611034440a245804405c41c0c80cac3d04404030380d10404035018400000100045884a42507000d0031303003c039403030f41d81000240c0740c00c5014141d08116081000ca104000101113400c46c0d214 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 100050000 1250 100048750 100048783
    0x30b0609040c050d0c03060b06131403070302121606050a17070311070f050613020a030605071407030221040b040612090f15060906121112062d0702 65
    0x1075980382401140e0048a520058001d021203003484180165a00020103481c0600414405202032406100107441100c00705101c46c2800003041c021050b984417940c45508004040380c1c6410703240d40000c1c556484aa0f422012580a00d120755213800310300006100074445414441d0515070308401c003516021010204021000f0510005107180d402540064524001036400c5034480030300e85403810030780c0c95406040e40c0c0d030321400e00020504e842c444100c0403800c2d400b9109060b1185155100c1e0080d240180021040c00141d041d0103404040003400303801228060b500800d0400c6e2030741405403840c0b1601c49441c00100007084288442c10603502260125041d510b03010203c0c00d0410a04402080c803880000e0180280303440c3c035018000441302a40058520307100c00c112096850480c42d0444519109441e24400c0d1400e400c804038070408031026600502904094041d01540700c104d0400340215158185400d4852507910010042d0f040418268280e01d1a9907450401510195a45e002040c051944 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 100051250 1250 100050000 100050019
    0xb01060302041a0c1608030a030608030a051909030f0c170105060319020303120106050901080112050705010f110a03121d07030b04030203071202010903030e0303100b030a090c090f0501050a030b06 86
    0x142041224546a0f482ca03c100d01c1055110071b1580d40b2135101c0b00001d000242000c030007180708180403007140c8140e201600c44510f400403581e51a0060756100318504180a070030180000030039181e0180d14290392080c54201500d50030b04040130400c401115221b00142c0c54682044070584000038041c29030011103041180000442c800079143d0700c21032034404484c1c981540002042900000070f401c4520098030742414982c2ca8a41c816002d00400e14090070035442180d0420242d40124104100c0081c0c500d85206451841c0e0000740c83e02400d039104400180302c51400382800c07041841904043c3c45440e0580c84040761900d00c043d40d4035258000a89010003500200742014020000c0754141a4040e09041c40300250b100c01a000300b000d000154007080c2403488015040d140030003202d01c22407118100c1c86026007032048100850300010441d0001d81d513210010b60200318842106002401e00c140d002c210340390180d003002c0685006901c9140a0341c01030f8070500004680700b07800360307200000b514450038 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 100052500 1250 100051250 100051267
    0x100614011d0d080706052710051302031b041a091611070f030b010902032a041a0304060b04020903120a050409060b0a0306150c170c030f070b01060302041a 68
    0x41c008442c18000c24500c00000d628080014607000903101c3c840b11041450010284103610941b2100261801e41d02d130040380411183d064142e0003150004185a01d0115001d8a540403031b03d0a652075014070100380d2400c25119607441c1a0003903400c14081c61900ca0700581552010896050010300640e09280c80182c0c0076400906c034500c1d06841d1a0302c80700310340180d83d540c407061207259001d010942e04008400004110203501c2d00860340111100e00110300f00302154a04c014010034510300030003100500f0000083c0c205400312245240c5003641c80a0750340da003411701e4240202c800042109026600521500000d640c2c0401c030040003030071001d6043e03a1079465950444039441190030039590103240440115a4403c5040900006589a14204005038a9008900c0c4003041080d0140001d0107440e11b07600003d10040c20341070881191a9180d0400403440d900d00d00f0364120052402c0544008102d9078140400b54900707500408080c2400c51509081a09010090405803032005185800240044 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 100053750 1250 100052500 100052509
    0xc0b040206130e091207030e190e07031d0c0d0201050d060e04120f02070503060105010513030b09010c0f03140103031d030f0313210f15050702100614011d 68
    0xc2c001100c1e0b59280814903224010b40740145016508200c0350700ca50301c0b9200e040003680044505403070301501c4242d40d43c0f1403038040101d10006142e180705004c1c2c0303043e40002d01401441115000d9911030300c01213010718101c107101ca990095a03c12441591203600c5055668a410012480683d02880e255996070704149544e0040c0c0030580c00882c06004280800c418404a41808040e5070407640e10f455003244414412a60780080380034841d0f050700428010050b40d80900000d0000100c07038800c904c900f0723a5a403140119a0011100d0442503510303050761050141c3d01442d0044a5150384c14100258a8011380000b03103020140002414025a044840e41e051036518400c40f52020017000c84400f8800d10070020740b650003001189c01500400790010030180040d40c09824824041001000e4160300c03130716000f141090030042922807013400402514800b0150103918810030241d0010203c40307454620072801c803407040d4002c0e9410500c0d0401c4000c0c0b42c0e0301c40700c1a01c41d04880c42c0c6148400d81183d0028 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 100055000 1250 100053750 100053757
    0x4060b0a03080a2f06010512010e070f03020a2c0c0f030709090b030307020906090c160c0608071b030e060405040f0504020f090601021f110309061005030d0c0b040206 73
    0xa40310390b501050007541181d0051000300d18400300004502840401800f04010891a040744252a080340e4010b0040742002d008880321020420004103060070008512070600303840d031b080030039001c46503002802503080604808000b4015040b11303040d00f1020440e0740141300030030741d084040b03c1e614030081010080c00d1000d42e5904456403055641c2c0703081c00c80002e0301074800781c85000d200fa818011032034000d14011095030b00d10303600600264200e5a90b401080010780c0014100010100c0500c5041507400c00b00203404801441404010101070601e0400303086803400515007002c00c00c15915020303001700c403e04440c00d034503411300300001950b03658000103041e801160041504645840c0754110540050f400042c05140203454080b0a600b602d014800c456008031101405070340080c10400401070801c020410304210241e0000c2c803102c82c04405c142c20f43c01a201c94515600800900c0254020702e0000401000308030b00501f500c0c003407180c0140240720181005000422548000303010354a400046 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 100056250 1250 100055000 100055003
    0xb060a03080301090209040e010c021b210a0b060d030e0d021809070311040506060313060e1f0f0b220608030706060e0907060e0402070201050705010c020d17010e04060b0a03 76
    0x4482c0c0325030316461400d0082d0008013800e8843c5041440100000c1018440c1e1a8003280690280a880c1049102078428070b62112032a60001c12541c40402c1c418142414800d038060480042c1c01d20080c0c0d4202140700c0c80f00030301a14407442582e49003000283d0007082c6607881001c25212041c02c070302c0500002e443c80100801c0c0c940181103140407c01e6018004c960101076034818800c0d5001d0404030410310040b40c1046070125040344040004c145000980c1d80c030440c00324414000460445600c544103414000441320612841c14405d120a04c0725a941c007624920480c00c0e0005c0291a02e4400004d48031005140a40036002014640542403e42c0c2e4100c14054140c00c022031b580c0345143c0c40c24a0083c01c00e44602d2450406100118a50303030000725450003200c07034a80e5054056140b807001c00009603c8000c0c2241440810032500e80058428006c0d602c1c0c0111075005800080e984400c06085164800d0301342c8003a032106801840821100d05d5100d800c030b504401e0014010035400045045600d0a400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 100057500 1250 100056250 100056263
    0x5241027030c05130203040b060609060c01020403030513121106090303090a030b0403020f0d0203030402040b0d1b0e131709010207080f161203020c0415051908010c0c02030a0b060a03 80
    0x3004001c0c0040302c1051800c8031020784008801e03c00c20742c520b50481c08142c4000700440c0780440407450500e441009480e102c94000c0a81d450158801900c60072640720340d0040700420030200b0190b5000c1d460341d009500801e0791a4500b42c565205940300b541e24141c003003440d4815100400c001016450030401e607600142e01034410b05100b41c49050608030503e08940840041c812080c56400c21a000703d42c1a843d46002d40007141540c80740c1c0e080102902480a01a400884200300000850a524541c03070031070384000544240507040001d28101800c008101c445100300c03e1100c07900090700c188210000f40ea2070100542c4a1101400407403c0012660040c011881422500c40c0c01c50008280d1410b002d00586030340c10b40c0da96036090044c1c034410454000c1c025800c0035201e24054145604a448641c48001038a55040c0e143c8000403071040701103044070f2100c0f07180d220600030548248601030000c80203050022a0800a50010380c0d01d0482c104018610003080021400b10340747c0e2003500004c3c40d03000300b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 100058750 1250 100057500 100057577
    0x150604080303540102070209040b28020d0b0307140913230601060318061d030c0f060108010b06220b0a030203150109030314180a0306052410 62
    0x140350f6601c0c60811243c00c600c1c440381d07260014644030520071154600d40c054240c88a070395990315000e1820034014101c0614854181c0341a072180e11607000c40814a0031260b0050f111030400c0c81110480381d00010644c0664400381040c0300080007400401c0c200c0004031007000c0c0541d00c815012240c4400c00c40e0042c00c05201c18000e0301c1402800400b100205e01c1d0100b02c41590f03a0f5101c01310f090782d02245070005c9030a01d140500010585070b0304040c00140f40e00c5400881c21040c33040b0340b45141d00c081c443c21b03416041030080c000a0301c0d041c40214010001e140003800080903800008840e0312411451078580d181000101c4000118601c058001301915880551268125040600a544101c4014000d5030442d030b91a003003507005100c054150b80d0150703101480880c4040103400280c1c480000e104d181c000d0443c0b810300954404d21128007440c442c000101e0141071071400000140c11102c1c010701809600c0100301483e407180c40701d030500740c903140ca400030000c2c034040d10412896401303440042c8200060b0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 100060000 1250 100058750 100058851
    0x1a0103050102030417160f03020f0d0e01032301060c030903060207030e04060801050708042904061b0504030809010c0807020904050a0b0a02090906191d150604080303 73
    0x40d400b440c131a40c081d90b01500507502d000700c461043d00c1078051940c400308a0701d01e2030011a512030003802901c2d00c01e0046846900f0305003c110320302001d01000100080c80701405580650341400398003529251002004544419603140703107198081405884100800d08481d80b040c10f101e1900d903402160082021940c503505820b0081801211102c02801541489000036003100144a010f224006d183d807900c00e16141c6035a500e01c0294800d02c0d806e039079500c003031609410001c000c0086010f640304820004000b00e142010f02400e9000c60300705801c0c01001d10081000c00e010b94100c401000d02442e14840300783d450724050909001e40c000294004a0f090300700810003100041d098003060280c014006c069447c4200c1c181a842403a0103182c00250400100d13960b810803c4904000101c01d0209490940d203c4405043c1104c1d40b1030b04040c5500c000341031004850012400000081c41078801030b00d003500740f0201d90396a11010b482c2c8a00760703880580c5042c22030b448074241d0082c40c64000c410f04040910 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 100061250 1250 100060000 100060003
    0x30417030408070f030317040203010b10030e010b220507140c03071104050709090905030705060f0115081e1f09060801050a061d09030c060403081f0605030109091a010305 75
    0x64010b186951046020210300440e00c05400800c50380c2c142e4585403400030060222055000281040ba055034940c0e00082440d6500c03610084c810750a80c0c3e00050203000051050300f52290348002c107000c0c04030818055800302069411100500140c2c2c0003042d903403621801114032044a2900c0030402001040308510b40601100600d2044d00600b040300c8032140c40d404220460390144e400b40e020400e40c2000304011000b541010750f03aa801081900d0030b0041d10785880c0c0c01e000c02281c0600300c0500c1200144800c14440742444d0000020f03142c06022441c005030070300e6207a044051400408011400091985940c00e86215001000c1002950740d650b40e484d12400034201ca0b000f400b00c65405c080024041c04018454070301101d07015821007103615910484501c03500310290420b1032a000c10000020070010401003603004a110f6603503107800303142c55560a64a06079003824011130500c511002c00060b603000c3c050700c6c1074684e901c0d000036a8038243d1a042d0b00321311041410718089180d500000090050 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 100062500 1250 100061250 100061257
    0x30b0d120809280303050a0c0806040f0209090703050108060f040209060d022809060602010b100305060109091802010f080709030b070c050604050601050907020a03020307060b060c0105040609030e0a050a05060304020303041703 99
    0x4c01d450a01c81c9440f107955080580707041d504110009018800029100c1c9416040390074940f010000040c0340084002c0425074465080f50003030042600d5000400441c4001c11009511100c0306426038000e04141c1d001404110020b800144075411034600403040d0f59564000366000740309030307420850458119481804d03418480c42482502450014009011401070140b4900007a008000c1e40400401510580c02031001034110ba0410000c494041014845482034460407020803022805414140c4001403440c51140d50740340400280e00240314169420000c403d0541f540401101b01a0b40c81841c00c8444844203c8054028410034040c0000c0c00404605a41a070f60162601c0e07515585420060384d4a0360604001001030340200310302c0c00030038500d80c840070000b10001c2c0000d150090401e009400d50b0010f85094580a668088603010540c101007a059042019030302407116918003400101d59490b50b00c545070180000200040456a00717108480c0039002d0741c48003207200106810480c1d502c2d007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 100063750 1250 100062500 100062503
    0x409020a021507020c03030d0f020f0d060e010f05010804200301021c0e12040b0325030e070918021c021c14010207110d060b060307050a030b0d12080928 67
    0xd10b0401050001e840400e00c00b040d0b18000c2c2c01940741c0030980210200421280310700d920b85560a1110400c10005c0c98001c040d8442499004581d060501500001d110410383c003c1c1c40e455480c3d20101704030303608040320541c0a034000702c0b41c040c054036052034401c00c81c04101009038154400100a06044c00c0407000403140c40c89580104804060f00040c16920045d126800074800300c148410000783c081030000310380c000011b640b072001d90541c8482000c00402c1024030000070035210322001240440400408000700180c4100f8009802e08d44200144407101d004041d010b1480c09e02c8031500002e810195482d26903000c2c0079001a00e81e005051601a640d440c3e080f40c01000001011182407014000d0710301e16034001c040c41d005c103150001004510240c10744100c550648440b01131800b0b07504caa02a40c0b044080e921856566040c0510040c00c40394800e055510a0b01c4861220021512003890f102e10180307103003400000b6840d2502d445241c0000300559021518103015040200c0034000e9001d901a03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 100065000 1250 100063750 100063783
    0xf0e09010605040317030c07020603090f0307030c0605060d0c0902071e05070807230906030a0609080a020c010c0c090207081e07020405090f250b030f0105030f031305150409020a02 79
    0x101c070045c0c12104a100aa03003e1000301c20520803003016140c040300841d008580042110172400290f0b240c9819034004100c29400308100450520a00055004481d4401411160117414096560343e00c2061303801405410100399003c039810040044d80216101c3c1100340c1f5580040c07103101803a019544684a00621505020301400014188e040c40c24203265051400c00c601042d202c85000d101c0700c0e590091900380d00d40b25158100010030750910036070700f1850044141698038021f0800103441c1c40182000d20341049145004080030801e144e401e50b0556207000f03805030344e07111541050a804e000c0d012041c8031080c2440305042c1c0c070200034002042c415100b9035040c00300340e0320b1600558441054000e4803e9a401c03290300521084800d554004542d02c010361920107550300c46d00010800d81044441c800c1941c0e03058010b0080380b50070412214583c417120015481c1c80005924550081381c03034400d031030250300c0492000790750701c801c2002d55002c0c03e6400340854a0700304201c4000d5845550b00c6940405 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 100066250 1250 100065000 100065023
    0x1409030d0605090c0f070201030605090f061c02010c1b18020a080a020408060f040203030c030d050114121c020304030b070e0f120d08040c0f080a12050310060f0e090106050403 77
    0xa6040944440c4e2040d01d0b400422400c01030341c42008091684040c10490415a891102140a54948a4480c020140e0070612461f1b86000414000303803040d001452440010a10341040060b03a100842200c0d155220119040c07407481c031034a42c001840c654008c22810503604c0d0142c00c042116a000c0c1148007800d6948400b04d89500306544101c2c403490207800305540000c07000460110f1203141a40d00244058110b0b0b18103441f10ba01107045801424007008810b8540c0010880c1c2e040d4003861800140007111510804c0c06030b0301e0344d0703aa0b92070300b070f01d2048441e050307070b4410681c40b4000d000351802903821110201d120310b0840c1c0001d00500c000b9404510500030038400c01103900302100890700c1c03a80081b0051050310040c000945000c0001030044810000400b408264486c1d80481d100007042e115004103214202850819209802e074140c82c03040060a0040081c0d0588510900c01250b0b02c41c180b6880182d0000c0b411100b8880c40c0d0515500850b10000006406a1020090040f40d008564210a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 100067500 1250 100066250 100066259
    0x6050a021602010e030703080c0a0311010b1804150f020306040c1e050f09030a060617010c02060103150905010e030a090504050c07060519060909021804120302030a1409030d06 77
    0xca00440194908080d0884000001035000d461503040c0031100500300c0304201c1e66a07030340180701c4e03100b060450702c2504046110003c16800502544c92248620300900c000303040e000c04139282e202440d10480300461210f010500340300712001060444002084140701c0c001d4001a0440a58019583c00340258540001d0100840c4103100180c6251841d00030440854481241110076401440641c1c0504000f040441040d90b4100000c0282900c908030100e41540f41c01c0003980e8130550070300c666103282d0601820044003640464070300d0541c0e50004107c50048041c1c12848001c3c004004010074542c83d01c03101c2c2668010010290400c480e159507101c00c140d4454090206545043d604000071403001d01c84400028a41d0f00201c0d44100e84c200c1c403060540c103e0300c11100740d070303807a5000281082e40c41c0540800d608015030350802008144030744540c103003059070340c07403185580c0c04c20100205540880420464591b0f80c010b03441140300043c040d0400c1c2002501e840e00ca50003003403a0030409103420000503 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 100068750 1250 100067500 100067521
    0x23c0108060a060f0302130e01090605010908070e07052a0606061206040209120601061d06040302010c11130908220e010603020711040f021b010b22140c070605 70
    0x14411500944010300d20343c0341c2041990907011800211061603000e0050041c00702d049007242d0018845100070141c19490a20481c3c204c45941d00113a0402051000600c40d1740b40010b01c0d1012141e42c00070000c40342c1e0f01c01c074040700c060260034498000d0a4901c07160b90b4200c0d03c01c081030700488138003405079607164540b40100003140c13040702041c0e03808c82c40c51400201140307072550240a80540180c00d0750384400e00c016032542004000d8011002041c0c9001a002000d000300091500c00c1d5410b582c0301d031605082d40c0001e0901c0689210081809040117503460650300c0744030401c0c5620b65120420311000f45545442e00550700944014010000c807079082001a1108d40f0408044880200c8030300181d9081c90800c078041c0d4416681a108402c4040303661500b40c4840c490211100c82020740144c40b40d42214000c00c25400e00080315046a04103030360b68000b5035500b070400c40c2e1005115041e1012075031441c48040604000c03c1c00e0f100d520500c000700710719142d0460003042c2691050404104a03a528036105 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 100070000 1250 100068750 100068767
    0xa0f0c020c010c0c0b0a02070602060901180f03090806010902090411030423010e151e0405030a120e030706091406090705040921050901020d02010204120f023c01 71
    0x1005a10103002616194010a8101403481c00b603078a1a05403925403040c02c0c45d5600509808006a1042a0801c417880d418003003160003c034918000d12080d0000c0c610000b26500191001c0c1c040014000b003041014040d005540044c680350f001d0381c00c3e80d039441a00d00d0094001c1c0318500d015505100c034014a0715150000c81c0d02c00d59008008103403554849100d84034540006115600130365840000c00d003001c604106074420410900c102c01c07042e103001741c13071036610307801d111420382d8a900c0c160140400114003005464011801d450f00b80c0c1a8200ac540c01c0d009041014081c0fa6140400107001c8148a059041540d0190192001c00030030580e21141964031101110001e00d1904131400c28442841e0540180e491640520142c4031601c07020005065406c580c1d03840040440c10024900e00c1558061051402040043c0021410103281481e0143e004200d02c000828030300c10000000704541d10003078082c0542887c848071011240340c0803c115100102d18003001808401140120015032140420 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 100071250 1250 100070000 100070021
    0x180d0203060703020f120f040201090b070c06030f060b03160818070303050d020c010c02160605090a0317070b0a24030206160606080a1b090209030a080706020702040e01050a0f 77
    0x303081d80e60301c0d180c0840003500951000c80b101c6070104640c00300c80e1074041d00e40c1c2c01071080700310040841c201131001400f0000c4039130060a5100083c0142c102042c0040b0403141180d01d90305000c5940542c0d1a42c00d001404a60480780e200b1001000f841b00001400303036014540742c85c0f5240c03000552070f1004001120040303000d028100341d010b44001c0c400a8400c3c00500240400b9800150420301610680c0c0d00307556603220203c0040e4003140c006803003c1c1691071b1800c001d06040c01c0c81c40c64400188040f40f140711840c00b029041e24000c401074494500003108440c83c29030004406020390401541400c0603003091140741080d032040300a1407015801d4030002008913039006181501c0c00781c43c1c00ca080d45442020605907034503684c5410010b5035100c240f01c0e0003009441889a443d05400d0171584164101141e08000910f81c0b061004a41c2034800081c034160054200b0703c4241c803640c0c640b80100103403155600080d001030074031083c000c03900c1054000b80d0040c030140c501805a00c03081c000c24012680c14284 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 100072500 1250 100071250 100071253
    0xe1002073503040f060b10020d020105072a1502040b07060b100c26030108010b090f0708062e05070203150f0a090c0306090b0403090b0301120305090d0f0602180d0203 73
    0x1140010b02c4001020140c4c42c031070600442c1024807000010210040302d68200b026802a100e46245141d080c41031940c41402818000441e60303901e520000e0b50b80d10341c2d04058001c1050341d5803005200a4851210350004904025980c907911f8045002068204810882c2e01038200242c23041c2620704200c9010300b4942035543d140844080d61560011100c181803002e48980540300407141381300a0000030742c003130101a0001f052401c14881031040400000f412142a02890b40601003100e0b03110035002d030060411155404203004402c501c20200c2d250390712980303078501481c40042da11900600030700540341c02201980ea41b0030400924680c11401151400704103240000041d030180e40c5a8020044a8059a035050080c1d8695481c41c0c102c442d1003c080d02c0c00d400e4081000b04256001c030000f005481050081400c4d075140c40045c0d8880703407040600405000c004030341c240710344d107a40c0e12850200390400f6513020b00b16000c1c10840025880303650000150000720b650031205e4288404004510f55000c0c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 100073750 1250 100072500 100072507
    0x804140109060807020624030d02161a09040c020f010903020703140d0f0f0909090605010905090307080306010c020f091f0603060f1806050603090d02071211040e10020735 75
    0x80703c1440740340c0a00482031f0b80c80b0041c0c1180d038191005c02030615a160fa9070014a403038100002003840c94185940039494068014450b07501582c100c2d02511048070003078901145140034500143e08020b02141c419000e90318120f4802c05160740040d401f000c480c010617403d01e04844416540e9180c0d40c00c1c4c00b6030b00205640079065228035100c1c21000b00042c4051810042140d00c807046501a20f20400095440c181c5400050000c220305101d010b411001030b030300440c5401c11554400e0440d0000803c01418000010722000947d2503c540100d042a0010884801c600e440c20800d92038600300100648040e0100341c0114226001e4807440d0240d600711742821003403d16181c0400118890030040710004c0d030302c500c0c002a080d11610061070180300940040c10010001c1c2f0030080c6490402e5109a5000c078000080c94082070070100030302107141054a011444e842024a060720b00748904190483d02d902c0051400103004080141d1100b0300e9000c2002c05558524084462810780785914007840c0c0c0c031040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 100075000 1250 100073750 100073761
    0x30711061204030c1b0b03090c060703021f020d0f0e0c0a05030304052101020708070b06030703030c0602070c18090605012c07110102121f0311010c020d08041401090608070206 77
    0x304195095a44610317a940c01d1802c45400c00e482c201170342e51261030414004001e100807200e040c405442410070a0315160f041c4840758900a5032080c09030032140c0010304d0b010020b0a0780e011601260403292070584c05200c0011500d441400600741c0309401441806403040b64549498942280b00440b134000f00150b05060a1008010150108442030a180310400480809124007030016001540c0076007201926402c180c04e041003c410010b100c2440398014600500c0080e27040400402c101d0f8000d0001a211b0840b85001c0c25403004940128000040040b6412031031045500140e411a200da202400141d07078030714445072607000000201c0c0d141141101c0380300764040b6000c1d0300345e44011286000329440c80b005031080d0032684981228400103603020100a0b02400318045441803c6985038200d4807246961200e04030203407130303540d054108454800361000b5517130b6042800c0c00094004d900c144c0d4840c3d880004240c40c020000c081804181d000800165580c002da82c954441c018980151400359504c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 100076250 1250 100075000 100075007
    0x10506130209010203040e01140108070806210a050601140f030606060a050c070b0403060615050901120b0a09050c030703111305100c0b0a1a04090c0902070303091403071106120403 79
    0xc0ba0002e045100031301002507419201e0169500030804680b00b600144003a500040000400808080c2404001c10500c945030b21048008400c005071403180c00d00380c185121103a401c146803084060168800d89001050b4030402140340564407004460b181014040b03641816150340e412660903a2049080c000e80c81c1083c005c600410802c1d44480540f80314035159410380c200c6801540080c0e51041d6142400d10100d115002c002c035004c0702508165003810040e10000f85011010840f1844550329402d1404a9850300c0d42c000303000e0140f45209001c1031600704a120f02c0e680080b2040343c002420048810303110701805044030001038100c1203503c2c00500380400d01901009040100003040b0f40d080300c203404038169102440c01410b001c4400324204410943c03460000c0c40c84040c061144c1e181c51a000c001680e480304000445001c800090785a0300c0c642801d40c003c0c0001d12014007003030010200d18041c0d072400302c02446c00318401c1c10790302628641d00013800014001e00328002c1c1a04206004203010138003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 100077500 1250 100076250 100076257
    0x30f0a0e07060507140114041505070e06070611090406090921140a020309091f060908031c06120b011d01030809010309020d0503130824160c0602070308010e06030105061302 76
    0x202c1748001700701c000b41340403030004501044038280c81d40c0c0c40003800b2441c4003c29000b5540c00000501c5c000d80026180e170001003541c4500b00006214594640c1c540f02101590029940e044400900800506075102e403036001070400301100725408410300c0b4900058600d2007490a14090705a07550004517001c271301007998140e011011050551006004c048000c3d03461100e168429403518000059103800700d0f0380000d189003513802c24810b1082c0b20900b406106030001c2910300c0c1c601380d00d480320a8511540603a80041915802401e401d61032101d0345010712031089000e604903030780c062a03041c03101c50580c5030090f8264280001051098104004840381d0f04c640c01110850b400282038201e540718039521585954400350040c004440340382c908110100061010300c0d403c2c80251600c03403080e2500c00ca0b10420040c0148212405401070a040565610482d2052038a5500540444d920791450a0180407460240b0400c04210044000605241018003509002e0040540340f40111168011072502035007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 100078750 1250 100077500 100077533
    0x13050109080703050414121b0d02030d02030a080f010506040308031e0907051e03070e131203050105090a140f13081209010b01080108070302090703060803030f0a0e07060507 76
    0x10340300c492440200d5984002482034900c40d8a615a0700c42ca02030190700c8081d48030340d4091069018005100f2440008a8801c080303101c3d9550700c40007a4814000140140046003000e5050b1107500504500d030b0340c0000080654002c1500c0300280b90b6604500341c0d08a02c424080c0c1c54021005200400014191102031508952011a41100300664400d802880c000c122000c11241e840b602c810401c90409107100001c0c544080c030b100c00f9012802c000700340d40d0a1148101c10000d520000003178078042d000c00230046503e0b806444501d881740980001800341c0707000c2c001c45100c0c2c0f8050012400c1c5d24020700ca10a6401541e03000d60850f80da400d11045844400100a03091004400c404500002c0c1c96000074681c040a411a050090420140789821030b00d1080911b4140030b984401408240d4000906200301c17a0f0456100e5616079525200300c02a151700d50000301c0d54800401070080d00c40d04494224401e50b1100d804010030040740c0001e40e40c5242034445e500206008000d480042940080111105c9 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 100080000 1250 100078750 100078753
    0x405071a0a08181009020405010f050f0d05030c0607050c060f0633070c1503050402091302010c02040f090201020d021606120b031207060b0d0c1820070512040b031305 73
    0x1007101080450030f1104d02580900f00c10f40c3d41001030b0851a040c81024050180001c4503403101c1c0c00c101c04103410f00c504880b40c1d481000c540040c0c800b0031100304121081c42d0444400d448a5040100000e04107030400050b0020794064400050801d83c0304015041c460400140140f40c1681d1090400d140d0312070b40e9459586c0d10711341c0e040c0006140701000c01440d1091040703011040b118540310180b00452058041c201c1058140814417015030b40d81442c00b50400303035000c403d11310040f036840140e521995a950003900581819480350082c0aa03a00c43d00c8880e0003031302510652075000381c049886803000035180c02d004d0000300c0706220003841025a8030007d0160a40050680f0003035000178904150840003051600f4005007071010001940200c2c401e40e681640c0240007001c1d966503102595005009559820b9203040c048d80d0102e403190012071030343c0841c0c003001030402603141d140511130784484401d40d114454281e43c041d00c850280115030031a245070395400d0441d10761940d0b49080c1c0304442d5042d07455 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 100081250 1250 100080000 100080031
    0x7080c19030608240903030402010e060a0c0204110703030f0b09130f060f020c10020901090b1c060303120b0109031a0903040314060106030605010c021e0303040b030a050405071a0a08 80
    0x800020013000100070106400c4401d00b050f04100010a030708000c04604042d003041c000e000060f40c0040c5100403002c0100c908039218280c90004a40041c120900a54810b050000c1d10784c1403c01c0720300600025009640901c602e01085100c2c270305a4031007464080e000120315002541f2030300d5040341001c0d1544500100f550309035540d1680410384008152002070756a00068080c1d000008100e0001d40202e40d410a5040c100b40400182100e1190b11443c2c41c1c443c00041d101081e440040310806c1d0301c150441080224548908004100106003080207105914250b0904150340c01006218100c13680400508a00c0712800009001030310081c3c52240540300501010000401e081030342d0440c40500070040c80b2640c5010b80c001d00780c8410381c0c40a810322030580c00300300c0541c90360365038034100c2d00a00400c100c0041001d00403c4c40c62013554000442c8000c04414000c3c0c0c4115900600e00485c0242d048070034403030310f0301601100100c1580040011150070809501c880e0b0259546940c4900d410300c1d900d01c03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 100082500 1250 100081250 100081259
    0x302090903121009050f01061707140a0305040302060a0905070504090f140604110103090803060d1704080105151503150d0f080c06010603051b0f0702030304030f0b07080c190306 78
    0x2071a42c00e4451080c044a1500280042e03020791161541c06503202c01034035125454240003030407442418006084940c040c1000401c1d49003e00700540c2140e2a4181e403a0395041300480085c010070302590100c0043c021354000c1207840301c450191203009500f0038003400140c0e141c0b0041000500c901c0f0422110300b03030f001c502030020440c03003040c1c0c40c002034240b40903140602e40351501c6400311850400003414545894118004128881e06a82d4004400d072511140080729080100d40301c07451025441e590304001402180000040d0049805558000d404640070314100040102000b003800448400c260140001801200c420b480689058006440706403000c00300c0d100c240074502a00c04c1915000c0c400030f00050f54004c1000b5035401444036140070021130425462264042d6114440c1c195642804034400030300038014401ca8000e40d500900301c0355550b03a246130001075044905404e44000c040d010000340c0703d90149103094442d4806410301c1c2d29001c500400072040c0c00b582c08000341010f640c1e07000800c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 100083750 1250 100082500 100082527
    0xa091a0418140f0702070501020a0807110d02060c010b0103051503060c03130b010306020406120b01080118021308011b14040e1510110f0a050304050123030106260f010302090903 78
    0xe000b0414109108400d00c1c1440c4c000c2d140180301d500040c11540a41c40e4600850202c00c15541c1a030707888801c050704450280005403c650401e035002e50b10280020b120007400c3d005500680b03c80c1d80a072010b114036503c1c0e002c0224411a13030340c40c0541541140001409180300c01008550202101c450003045503295141c0d03501040090f042200d4480c2d002500b0322005400010b10b12040140c1d01c0180310344e405010000301b4820042c840e0302d081c1c041e030b1407a0104075082601510344204006001160712983d80207024040c2004404000ca400c22404010320b1013841590401805844001403901e0709151100c10203403140020300b20011102c40900c032619903910b824210a1121450b42d80c0b815600695243c20b0070109150000941544000a44800980e0210998088580134203201c2d130104504289007a420020090402034000004008141c468001c030114145204407140a101008140e0300c4041180342550081c4100c50b040d00108018904200043e5001c0301700800d403810036a002400c035 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 100085000 1250 100083750 100083791
    0x35160203070507080a1703060d030e01020a020d0c0501090605030c0306090a0f09030e0405090c1503061c05060901060f06020616030b03011a030105060f010f080403020a0f080a091a0418 81
    0x181c0d02e42024641702d092060000c404a0140b020303000c454034506090000690500040c00020300b845045038480801d41e000f070000d9010140c016214140904151034030540c882e5090042d035010411054000c506984500d0a9034810305c0003060051454503810104046a140146451001074640002245048850140054071842a2154000c03003201b0801c104c00c1e03c0004201c6016980007566496945d0b0f180b0007103500c07500d0b100e01169942d440d18004a9420b440100b54210480c01c1d04418a0411800081407071040300484000c0010075140d140901100403944501c1c00140d0051000c075107901c000141913440303d441da0500003003601c070f060b0201c1d0964250002201400c80a0b00560030241030a0281a03400341c0d048030f0a4050540710f80018000c00040c0e46c80d8400c00152000040805000b009158901500200f00ca0300385038091510f44510f5203c0b5503154002100c01340700140411114074046644a400701d455401c09040c15850083d0950700020749180c1034541e40303018909401c1c2280c5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 100086250 1250 100085000 100085009
    0x3091707030e0306090c1806060d05010b0a020616201c05070201031503050703080705100f05041407034805090702030f0708030c0c0d35160203070507 66
    0x141100d6964a03400c042c1000320051040c00035422003800440183e50307d9611031110404601c1c401600d807288404035085004040400300190b140c1030010902c540040c0103081c0c0105d841d0f0843c0d01c03e81e952888000b1103100b80802c20003160500c80c01469a01002084400d24424a01114a4641c1241c00d25a03134900807090310011900000318141556894024800d034000e140f21100001e51440d80c8080c2d42c1c0c001403102030036985010032000e080100501031140031641092040c0314034500404200003c040641e0120b814a0b07a1080070850007101080800469030032948401001d0040b42110100e5800c94440b540380c190f0300ca42c54009200310504c00382d0f401460069081459050605001c070001000e4030300c1040d0341c8248040030200100c1000c0f121282d1b4003104554494030f9074902200e01d40117244070610f1074010103100001140c2d010016010b4081900d01a0301d40b1000c458203102c03612504004c0c00721603c05000002d07540c0301400000318441c1081d01c1200d28080350b50b19000e082103040e070071 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 100087500 1250 100086250 100086257
    0x30216060b180c030c091206011d010801090b15060c010e030304050d08191e0f0e060a1e0e0a05030304050706020c0f0d02240d02030115020309010507030309170703 72
    0x200300941000d94400007011034010344503145082c40343d515030990200421380e00c1c444100084482e599140c50b500060301091800494050b075844427549400c0c0000c001c244507801c58030800005414105005124078107400104042c40b41c2c9030322200c000c03044001b410082d0408000c02005400c0c0009205007039522552a010b9a1a4242480c000b82040b220540c12410001c900c82031004121500b48038010034800e000c1e00003041c061002d110442c1d8581c03680304481540c900b811495850030707103070408600c000c003071003e6400c203940302c0c2014400c0742c030303c4a001c0c255414491105800ca204950041414200201c216040f00c0b8150b03036010701e941e200300c034200c0321900411340c20803155404200c1910040c00031501d041d048140c1d400407441c00340a0100c00380c401c03413400494041210089458400794024000d02c695544c1c0040000c00296100381700e520100420440b645903680e1002c029924145016941c103443c00c64a51422009490500c5041c0c0350048a240414510351414001300019480303910f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 100088750 1250 100087500 100087511
    0x140a0b070b1b1308060703060f0b030702070b04060503040c1e0b03040507050402072406061b17030703140a0b09011a040503061306140417180d030203030f0a0e12030703021606 77
    0x500c403609205c00604040185414480180b110408800340001503030fa030b01d401d0686954a0810823071410030680d01c9942c19440003d0007164450707016004501c01d6016042c8088425a00d8050351043e26480384410b00401c44d820041c042c3c3d2680800445e0064040d9007210440d41e1200c000504980c81301404440c0401c160801050a4401c039400c210240307014441080018035200d800340041580300031000c401c22081d1100010071240542540540d01c01d144080d80b6485c1030340300a0010308080381003524003156440024040105c82c0590406040b020742104080e91802d000780c41d400c6602e20070141421014030011400340c03410010f903849a1483c4111001c00825424403004647e0360304408182101c041c01040003040b4440c5811003c1005920499034448619080c40c80d000d401c1207005500908420341c1c80140340d8000041c0d4002c2c24107100c0010a51610507511040b00c014280c507030f52903000f100b00d1400d01009200610307400001420050300e46507503103044d4180300352210307004c035281c2d6503e0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 100090000 1250 100088750 100088759
    0x604180c090e04051023090c0103060806130807050a0b0a0f05130f021e0307030b04120206101505090d12020c0616061104050a0906140a0b070b1b13 65
    0x60010000740714405514005060a48500e905c91034008202035000e0f48801c1070300303808446e6218141008003031018540c014280b040c8030680704c04450710b40754000b90034604046a20003003c01c00c0390052084240c8007107007405965807507129070002d9105454134080c4141c9580450301c6480b44510a05108800141000d002040d06084440140000d840342c0e584000c0d11002400c0c90002c04460354045074a030328410a2566916440020000c0c1290180603080340001003101d18031541e0300541c81100d103070882c0006007038100d0307450800303c401c40010140031400700900400b604021030041c0d82d0346825850584850081002a414410200c621011182216040d02d5051060020045040300c0d02d91510464072000429101d101c200605141d54541030511542007580446005000c090201010701da0b4a05140303009107285c1c03003048036880f81e41342041d505280002d40401607941d0394902030f04000181d150102212801403400800c524084070312035002c90b404c0c0150030040c81305280480c0484c00c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 100091250 1250 100090000 100090007
    0x3060c05070b0a0b060915030a0b030c0109090e0312180c09060d0b06041805030406140735190e040e0a03080c0906040906050f011106070302090604180c 67
    0x18105010000244007034000502c0b40c1c00d0b01900f04180c01400329114080030001000c034400d07100f01d03560000f00743c0c000c102801d034144040c51290484110400281c2d2150050584503866040c00e180040e81400c001e01480c01c0303d030700003103054204e07404603428000d03035082c0d544106c034064449908483e01c0c0480b00e5140003040001415480e01a56512454141880800c4804513410b8006004003178941c00500c3c1901d07a0b610146035003140301c04240110070346c3c0c00c00d145c60342d005000394400544444009920a50a8402c4038400e40e4890860000700c000c01105031598030200400081008000009540e80000726015092100803901c002c030300030495410181000440c0441c190003035080055251080d80081803101640c0e070141020360003680c1d14903d42080d4410440c03401c0c0c0c41240441d011070064820360101c004d490041c3c2d00400700010001c015030b08001043c89051459001d0030000f203040e803180d0058900c00c840503000904081d1605d401c0d040c900b45894441c8121540d44a08803807030350f0b1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 100092500 1250 100091250 100091261
    0x7060501060c151514190e1006020d0804020105090d0203060c0309010c0905030d0f02072304050c03040c03020f030c130b0a12170306011209050a0203011a011b050106030506100306 79
    0x8060508001e0500c000a440130514114400c201c0400c20f460511101c6880301c02a08a6080d00504818442c0d500c0d034009140f80302c01551400c240700504080800c81900010300d00f14100d41640b65803c4942e103550044605500201034950004603800540e0b00503101000660b0154154030525500c1e45082d426480c01c5841c510760000070002d0001d030400c25614003003a108145001444c100044140840d8103914085056010b00d494015012840c42d800840b4000c1500d00d540c21034044c01961918004403000c3d000503240502001c0e000d080400041c9018020444018070240c01c0e69423a5081c5400195406000b01d200d1082c00c1d2528001b0700c4a1508034841d40180194800c4201420101d88130a202d070301a480304450120780000102e107660b800f9a400040c19004000309001d2040c01d0b02d000340c0c40d000c6119040b402903081107010800d1862903c51044c0494041e540c82000d006502aa1001a01500d03401c1d10b076950b0319040072010802c1848100d01c00da800300b040d00300061442c50a801100c5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 100093750 1250 100092500 100092533
    0x60309010902030c15120903090d1a0a05061e03120a03090506060109060206010b090d060603050a0314090f041d0304080706180b040501112a04050a020405010503180307060501060c 79
    0x101030030300c100000f00c17404058404100c0c034166201c405954103d4403500c0c5200c0d00c08490f600160350712601c02000180b481c1c1140c20b1000358409038940d1110881407040d500203481c0281c1c0413922145011100e0064038240840080040440749a215442003006c402d60041e0705480c006619161420103001d020003031135030010820710f8145035052402c613009480710818042c00844540014840845a5800280c01050350304140c0420602c0e0b903d10301650713103855140040340410058800c034611100a401075079084c40c40901207041201c201c908102c0105112003007100d500110782c080524040c400c01c0604041e10a01000b031101508050b000340460b6004a20180c0407020040705100351000c0ea81503c0c1241d02c00c1c03c00c0c20fa203190050125080030f0513514500380f042500483c81c580303c0c21700305a800500b00291420810350315101800801e901c0b0b02e0040c1e502161040000c10520f94540c0c10440d124100b2409690030300000350b0382c2c0d00a032007082c0d0294000807090b01038501400f011000b8040d00c3d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 100095000 1250 100093750 100093759
    0x170903160501080f0414060709030506070906050d0f0207080f040323032512030204150507020303040e34030509160509060d05060a020712021f0f0b060309010902030c 73
    0x31440d00d00000e014450040440c140c400c2c2c042c2c08901042900800a40449100425242e0724948684020305545a604c410368881c800c000c04142882d00400c9030a0613900380d84e44091034101c005410340060040640703d4008164200b200700e0200300d110b000703410700300000401c1ca80c5d45c910758200741c10f59040008121080052003e40500c0c1c0050020481e880440e01000018280c0c03100001c1c10105031409601034009450810a0711015038564020000c0d140030a4008017200203c003000c651502a100c4020b402d5402080240807182501e86a6603100b42d000a000307031003540b903840042d03031006503030b05404108844284880142d600750240e194420201d100410b1842c5000291000340c0c503651040034094502400480c075507445014602e14816008002c492003800d0a0501c0c4000b51311500040c0c510f4000031015400c541e02c040303202c0303075803840d40e070409548100008581d00040c08218403040800c3d80d00d00c001d46040d110b4502a41c03080001000000d9428028010f00d820101c2c0c1e806140d209 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 100096250 1250 100095000 100095043
    0x8070f0504110a080627070807022e0b030f0d020d0e0d050307020d020310021201050f010c0b010b21090c01080f0105100806040b0901080a03031b081909170903 70
    0xf490b0710403940c5074019800c850b0345004070080c0a501002807540a031814100310030341c1c100170fa16038010a12a00800150f822542e011050180d2688001d10614a80c4071442a00c00c0300c1b00003e0b130f150424100d0190040c00d9a03451002c24282c1071030003144030300844c056041048105da445801c0b010510038050240c4000c0f404031055502c4544a02c00c0e0f00d4001d1055000e0b08080007991000c001550020080d4402103580302d1454001c00300c40ea400b40310b854803910f480c1d0140d4000b940705e03500c06500c442e40690400c51076400c01607607203181d401c020301d00003540c0b0040005000b40742e0701e18121030244048001415103000d03d2000100f40090081146101d400c80400400c40e0781c40d090b0f00405202d209150980c0300e07403103103030000300034007a000e11302680070702510000b06442102060b180d05003846034800b04903480319180e03a01d0072080719800c610041918180082c103d070301904250320111408000014101043c0d03035a0054448007440c003042c400c0d901080000300d9003410807082d111069991002c040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 100097500 1250 100096250 100096267
    0x1050604030605100f0f09110c0a0308071404060f0e0118060f03020906070809030d020606030a02010507051e0610090204030c050411070501060b0a090e0f0a0e030408070f050411 78
    0x2420311403840010022652000010350355000c82d5490405070210415030400380780c0c0d52110328024200b41c01503043c5079143c9958031960b1a1842c08172540049494060485000203440550310954014080c07401d010320b1140c900081c0d01c20900400c0980b4003900da24200b1144110014212700344100a5414030200000500320360b81c010402004031502d915144d5550326a04004501034007421002c1c0380c110074041500b0007013214440140030090340076411a094100c440d072040340d464009440d403603055080b5542601c055440703240249400c500130310850b086000040a02c095a01582c80300f002c10360402c0c02407040301c9c0c20042c0c94000610100c18258105030458550912804142c0b047c18465a55010040c00b580c2d4414251400d56801c02d0007080401e656100d0800c00b0391244000c031001640910000c02d20305694a000c50050344265403584103070b603074103031510020b050250340203060b44800d100c0000c3c0240100b1031140646500d00f20700407528a00010710061302c00310000d0400c0e000d4103026101d13 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 100098750 1250 100097500 100097509
    0xc08031c0b0d080c01020405010f050304080904050703180b060118061403130c090c0311030c07031101150b0c010c0306060f03090c090f02070c0e281404290105 70
    0x22400001003000203140d1550000038220b0b036084070009150740004685290781c40070643c080d00880c0d00a032143c00d1944041c490841c0d584c801140e00804050f4140150122030409600c0a6801800b038200002c100c940c1d8085c2e4100e0b10f200c0b4500700c0701201000b0030000d0650740460750440f01d45555110410045c10554085d081e01416076040740c030304401100050b0040f01c000c0700350405907048003056681e60389a01099018091031061007002c242803c613041411290704040300e21400008040341e04150050358111044940c00c0d506250a6403524000145008294a10002001010001a620300f5403c40361401e449040040e0f105140c80c0a404100d200d81040c440301a2803920318000403250100d01d4080c0d082c0040d42c00c001c03450b5151130b80818100d0030a900900c442070054083c00c40e8103581e50204035049000301c65882c040c21241c044030700340e00b41058401d010b51030107a6000c624003140b60178140900c007040310295070300d0301c1c0300900d5106107005441600c115440756101d501d50750304090201c8e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 100100000 1250 100098750 100098787
    0x904060602012304020a0509040c240e04020d0609060b070302010b040209030c060f0705060a020c0f0d0906030b030f0105040803100f0b0901050c01020d09030201020a0f020303010f0b0310120303090c0803 89
    0xf0016802c08030002421503a40240d0040a070000800d04025410607040201341c4c201e003802502d40e01060b4060001283c1c20f000050510f0050039920880108082000e200294101d40c0c29a07503071641359503000c80c19500c280512000340c2a0210907940b17030982030a000b4255442c122115000c5c9104200040442d200030a094120a106940d000d5841094a03206140c900c608940540702d03000f03040030711030004243d400509a80481ca8111883e0101c0d64050b0b0341c07602e42c80c04010001c240000000c2000038040d420907030400c80c00038103540400c403084840b2800d540e000c440031542500004100300303040007014403a00191140003c40c2502c0c9040c6400b9181c1c512440c1100c1e4180040460341003030a00094040303980000d00d4034802d001116883c94081d01030740090f400300c0041007146804140c21480002903074100c0301c1d207000401d0380034034286d000460365101a144004c9807014540c0443d00f8032888c0c0c02420420300c00d50b0300054198050070100c4401209070440389003500104601005e002c0300801e513 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 100101250 1250 100100000 100100051
    0x9060e1204050612090307050a1a07050309100e0328140a0203040b13080a0b0603060a0209010c1502040e0726130b06010e03070b0c070f030215070c051302090406060201 74
    0x4c014142c03100c4e0055403950181403001820361198140050800031401000c0100700c0101080c1852030711090010768440c0403c407040c80540d4000d022850000000760000c038800180001542c1c03600003600f40240186980d0401a20a140484c150000f466440740d4615541d050760041d403402c1440180c0020349a124a01c19080d05000110305034052690030802000100194001c80b61041c000b4034140560000403212640b19014060015808100368022100b40b0788050303440715448659641c40314094a2042e82d8800c50035428040490100c08011050340100c000d515142030321484220680b070707450040c42c07504d00d5520940381071003030b9a8140b45450161035400800c41c8081e0b610b210041f9820011170289603407620400c500098514021001021407400a40544c0e113401d072540034a0f220340c40580300c000d42143d1128040d1030315805640c05045550f100710a0005146e940320b0002e07001620341c9140c4810300340c1c0058030041501d041d210f08802003095000a21011101401c520550b0050014 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 100102500 1250 100101250 100101277
    0x608060c0a1b0303110c010c030507050a021908040312050d060b0403021804060b06030117060a09050d05030702011503120e04090b0118060b030a050405210415030f09060e12040506 79
    0x140308003014005d800080440c00e1100c0b405032900c001145080c00b82800660400202c0c1c98500481c3c600ca1294040350302c442c06907001011200d16a0200840c0b0407603011050780c89036020304c000f0002480c518076400d2125650b0350f42c15207500911640000715002c503403002e00a140104003c00060b202d095401000c44c100ca074001d11159a607040c090007900840c0c051540c0001700000110313492801b04040941c0341c02c0b203c01c84c2d41b95990109000106c0c1c2e0503040103800ca0707000e11142c00a80344140c00440e44220984000b0618011150000500304110381003201c4803004074142299160713001c254004c0522049400f449100125281c2203540b21042c015a1096011003886000c5440250001c5004007606591141d9034608010300800509040e10120780074001c03408805174190521256802040e480d400a519191030b1000c030356551003034014104141a01d8a01400001206107d82d40810b402008080b5004052451050604003942070780b1600c2c8000f80000e0020341c46250580c0e105126011 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 100103750 1250 100102500 100102547
    0x40207110409030210060b0c03070f1b0e0412081003060b1810030606060906020c0105090414091e010606050f07061e0212010b0f1204020f030a060608060c0a 69
    0x40000414110400094001c0d040140c1e039002c00d0750014030106007000346001040590344480034610248a0828039001c41c0d4814454031000c03400d0840041b6640344a11501403034400c030700d0850340e16086668010348899070000100b00c1405965244945c4440f400c0c03410b100946041c910003070210a0500016000903911403a1903601d450304000c030501d0900c0442d200c0000e240c50400004102e601d40001c03640a0f040c50400260306001c2c65001c815100d50790040c1c40c4602d1100011030345500060341d81d45d48540c40741514048001c000c110310b40200d807010082d02544500300c3c0c03008940103540320ba694180c0c1c074002042081130391000588070b08042e120b1400345d0310105030900d0700241c6030348014121690040c2c0c1c4503818061059008107000e0210210150060780c0c1c03a07500c07400381d000f409a01190030004000b14100c207084213011942c450300c0105401c20300307600d0a0110380b0b0101c02c624102e81d403035a6004144404101003000d01d03402850300441e20311302200d008001380603e1211020b66074844800 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 100105000 1250 100103750 100103753
    0x80d0e010201110f0912240a1803020307020103050718060804051606090e09010203040b0402101103191106060a060807030f0213261e0a080a08010302090a0501060e040207 75
    0x1c0d00100401c88143c40ca841c3c076440d1048403680d141c0d0008422501c920360034145494004800b044001280703c440103080e0b02040c802960720121a4028070f030b11718103942c40d1240704600003c0804145080c0c0254000c64503030001d40b00240032070360090710341c0303090080045031704442e40d00300c160000641e24907140c004515100c0b440c0c243d15000d107101d9100661280c240001c00c840764003580e180102e4040c0401c0840544841e00f05508030b100a55024188a42110020300941440400301070403c129144c100c0214012000003415600031040e02049441e00728503022007903030b202c5800b96a002c03039400906032034184100080ca2612151048405210203580000c0c0031038007aa0010180040300c12040d5582ca078921075034091541940203050101d00d500d401c034501e00f070100b940c1c240360700083e2000b07000001d66468288d02f070050354128500103114030300900002804040c094602c07010382d0b803140101941540b04110b05100000c0c001100249402d004001c5c41da03001c45100250340e01550016642d1a46 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 100106250 1250 100105000 100105003
    0x903040504090c031406060109060504050d02060912151509010e060d0c0b0c0313090219050d02041703090306010501050a02100b0a0509040c05090a021305060a0504050306070302030109050709080d0e0102 89
    0x41e0382c000f40c0312101d03007003405da0002d501080e4144205030980e1680e80345519400190b9560003507004140e005291402e0711801810903100a0102c4000284052004502402d6a601d4000f044186580b1410f100050102c141103800c0b10861030304003210060f90303a40c142600342c0206c000040040e84540e8403807000c6028400400e120030003415000403559541d0101c80c640d03680d242d025001c450203145450030005030403e258030903500e07005600220040e00c40c140200440d01a0024180924040c0e4200400034042c50140d05070400007020401540d112144c000401d07040550586c08141402020068040d0b100e80c042166800c04104500c009201007040303020520540070b903004250031100c07002c03d01050081524446084900407542581c2036641e5038003c0d010b901812000358500d000c802001e102c04d02d80b050203099940090710780300d800c0942e5180003a117010019138500020a50000044c4910001ea0244a0f4805031a05003402e100c3e1400c20050b9442145072100c40c00c010a050462034580e10 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 100107500 1250 100106250 100106273
    0x6111b0607021c0302060115050702010f051303050c0907170c0a05091302030402030c2d041b0f1812060e010f05010f05011101150e041401230f090304050409 69
    0xc0107801d0100d25041c816080f843e441c81100300f1303400b503c5050b000240740c1103d500d006000e5015662180e04004540d8010349403401c810580030180b22050054100c0c0c00c9542d0141002540502c0080c2245440700082c401c1d41140501030504000c20403070032401c1d6000c491100341e00581d450035440c3d42c03140075240840d014001e44c600d140d80720b03200540c01d0502100c290095409980200c0c103454056040408010400ca00481e001381c06c0d80c0004925840f031051600c050509107006040070502150268010b240039040c44201c00200d01c006422610705541b044c51b29030820441014a46020704040e42c0400301c0b0b904290040031035803030310405403080600b0341007201003041708402400719503140c100360400185607006090000300c401c0002d211500d014044d0844043d9209010030a0504101c4003100c200c800070000d6940940102030300410403001d10652403040141d4054103609058906e06203801000508814026444a0107008002802104480c2200c2084a000690028500e01034000c2c00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 100108750 1250 100107500 100107503
    0x204200405010516060c110c041b0f0c0803090304060207060c050a02040207050c121b040506130902060403050709060f0815010b03060f041505030613050d0507060e010e070305010606111b0607 84
    0xb410098441b00040d04140c0c000f0024016400b0b8501a681010600003121802c0d142524002a0042c0a0340c00c0b601402c44070346014503038030300310b00c1c04c101548621110b0350041d284401c0d40e0348001810440241e0611086000d0a030b2031502c41e0202096407101c50340c500002001900c0780d9400100700040001c208490102c264014100b0140a4061503000f512021248980b00c1101c0f2044007030b401d0f5241c20703c6074030311980c40101039568401b0507924000090100c0801240c00000400c0040081282080300c180109110304010440c2e60500c072900c0c4202e489684030005507804011080819440180140d05540d610340c086612680c40f100024002d0b5410140c240d0044d10300300752546038880402032101681d4041d0308441568440c00c2e00515441600b18000d0002c0d04040300340c04600740300c1c00c0201000e60042c10042940311001e82c4c16421108000a260f0040d4031030340c000c10800c2001e0082d28024461800c0c221101c9088000301074840800c1d010b044444107948030508041d80e204400c1d10030b01c5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 100110000 1250 100108750 100108763
    0x20405030f1507030b13020a030b0d0606050102070b03010305030a080a060b040303030e070608100306020306010c0c090c1404060203091c1e0b0603060601050703110c0411070204200405010516 84
    0xc074290100a49410314440c0008a2030100000203107079034045e02911200c01d001410050b54134004d40846c0d00250442a41c40e0205500c4000769041030392120f164210981c002c000008013070b4a4140068501100c039400720f8040001840100041140032040d950031090718100b024840c0e48140595006100503003041081c101c0206000c020315a01d68801c00ba007410350802c5402003a110b0f4820b03070b204681101c1d840b124040301e1000b0706c0003034115000b441d00000c06040c09021540325540325007000c04541c002c0e8043c1741d61034041c4803035240d116811a0000300800241803425080c000d000b901c0380714410346280508041c048040e01c2030081c640701d0081e036401100700c0035031948075210f515650040502c19520b0002c1e103400308050b46400b08041c0c2c007858058582d5031a003d0140c2e0180c1d908503105445400c1030248100d0059151204e001d550072220b0030036030701c1e641d648240c810442107840451201910310300b800403801c651100c5c20201c9047c0e038002d003005925040c042000700c402c00d0420390000e200c2d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 100111250 1250 100110000 100110013
    0x20318060c04140a1514070204050103120201050f0610030e160305031b01020a0c02010804021c0503311205100e0601150201021819080f0307110306011d0a02040503 72
    0x2070a024501500944801d240c2a1440203149070030020b801c261070089560510055001004190103106c010f50a090840ca03040d0a2504030f800040c11500c090b40244ca41400c09207911210780d82c203100d40c99200051601c8481076007401c10105100d0f220104484061543c0c940c2c00d444c0c5041c080058040e00100c490032a40b1040d201e01d01152283c01c900c1c5d08015190606c01e61103411001070003582c0f4040c007103540c1c02007550315540044030746c1980a001a41c101d000303520107661010702e6003a80c0c40038600850046942c1c1c2181400c1d10003000d00c42c140041d200100143e40300d081410304052904071450424072550f09010350038007a0521042c0041102030a00e42411130f1046040400e000b81200e10031a08080012403066081c0c1c00c3c0d10070000341c0b40842d8110401804a468040031100300d018a21001090031622550984d1401c2040d81158503543e102145450030055030764487c504641044d00074004552511943c01c00c0e645500b22035403502c07a0800000fa4080c4c0e0b251f4141c13001030800400f100d58 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 100112500 1250 100111250 100111261
    0xf0e030403020111060f160c021008070e04020414040504061103040c03110a180507140403030c1709010c0807060b090708060405012301050906040803030f090105011a07030302031806 80
    0x1500d500621040380840c19100503807121860218a840c402e4070400c18000803a40e5164000045204020744031040c44000c2c0c0034000075849040b031850b00c0410648400c503480c03c02c0200070b8504054060003a20440c010401403000f00d1000301d80d00452202942c0105158950f0300d040303000307003086480441c2521408010007044c8501d01d4115822a030040c041072480c49816011300480001d00d00a00389620b040c02c4c1441001d04143e44420350000da5858911088846685c600e1115849640b0540c00903203040100f86c240048240c0e2406000c054a41e0705c0c0c0b8084182001a20303206507644054a82c42c80414103005100482e0003019000314010518100c1b80b0300028040c01d0100706407040340c000d501e850004100001004501c108880044925445070313080d00d070046580e907110780e1009801000500c000100603100708091405810071090f00d0040c2d18021100d5821139105901c100160f0a442c003d480f0007003840d804481c001e5805180241c1c0c0d030f642d01050089203804002e20101d007449003404124 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 100113750 1250 100112500 100112503
    0xf02120c03040b07021c0c170c0120090d020907030f05070908010507030903080112020a03350306010e040513050a060b010201060503160504021308011b0f1d06030a0f0e 74
    0x103200ba446841c40342c0e03a03a111480c00f20303501e903041d4210718a0401302002e04410140525605101c4522400b400001e0012400c00070456800c00700b41400641c1d158000c408a00d0212f00644049034050307100700381841d5400f00001c59007551010007901450f4ac0701c0200c1c9941e0322a030840c9900c0d100c50b4500740b0184c244240018030b011040e1199182035443d06001c142c806109006031002e10360941e444611a03400c0c299000f40c90381003130208030391201181c50000001616410301070210702d91006c41018144080c6075032104020500310150022108208018040ea080382d010424001d0075640091250303038984036002c0744a441b03c0058214402d80d01d12401708001034100102590082c0d00901000d03a946c814941c4e2030341300061030342c40c0f4100d9850078069030402c2d80c050031800c4240030300c1603001591040c1c900d08481d01041003035a41d0300c81b141d199a10765007019a01140f0221450100b014460a10b6060070030710034403550a11030240080420030001c03c90300142d071801c0343c640c03041041340c0d2044d000a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 100115000 1250 100113750 100113757
    0xe2a0304060c05090a030803180f010507020c0d03090902090f03010f0c030e0111030117010914030a031b1b030e030706030f11090907230f03040302010b15070201030f02120c 76
    0xc55819040c102c40c01020b81c810400d40704500381c003500c1c0520940c11030b41c8041140c2c000a01900c00c100c4800201310b2010002c0081030201c561440c0005081c0c10b007804024140446000e001c0c0c010b5441c200e000000a0b48054058100c840c2201e00584451442001401d5000a103031030707581c15820300410301c2116807541d02511503901640c4003003008401079090075003610b404c0d03201040101014001042003000280d10101d101e02200e000261025190350750010f555200c00101e42280d10103c0c41c000c0c000c0d01031003602c040520300940c0c6a01a0018880140b82c0310303404801c1446000b10714280010940203070101803403540001c0c10b8441c3d694030f4100040c0105a8182c0c40f4010900b4541030324141d03e1400100e507580341020b400c2c0031690743d404e501560008002c01c22903003107032506008203168203081805080700c4c0706a03c80081c1c1c2c03403c4c2801d00900751540d0380c0c00da5115980f144450060700c0a01c00c2101c0800e6030a003404502d074600410b0140007070059900483c80a4220401c0103000100200103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 100116250 1250 100115000 100115003
    0x16031107060201060503100f090c18050915040f020a032a0e040f170c0102030a0506180f010501030f0605030106080f0f010605130f020912010b0a0602160e2a0304 71
    0x100e4500c20368500c02242a07804505c281034042e0400d400c1c0c802c003920b1641040d00c024542c21400b1500c12555075903040c2e8401113901c0107422080451280d000c02d2894040c003074110103810f00410358400c1103041c10480d10b10240c0001c002207000d0faa001d00315101c001004d00259040030f00000030140e454140c480022300d0b0002c007612500d60300001300c2c4124200c10090b00032600030b901c50980e04040c0d515400b0740b0306104500a03045d44240206c1ca0108000d000640c42011220404107160a2401c00e00c0300c002c0c010f50412010306900030400c540211008070090446109180c0481c6010607a500b41e40101940c0d08065019420020701007040c240006490180c44000801c4921200c0440d08071800c0302d44a0040c0d9500900c131444a401d0100301788c01c0300c900c2c401c4400c4014540002c00340018004d6089002c0800c540e515200d249030f05113130420200f00244018000f410400402c0c41e0000700c40d1000c0d00402c502500071070040785281d00b010008240e50b034400500310a84c80c0000e0320500007604100c80 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 100117500 1250 100116250 100116253
    0x60603091e1b120c1002030f070614060306090604020103020a0c06050f010312050301081c210605030708030405030303040f0f140313050d080706050a180b0118050903041a160311 78
    0x2010101418908612154240c0300d002410721324008404108082080080d4001144824440e42084110342c000500700701c0d104100c006582002880103041d1288020710039071007600210100801d01402080c03150f1b12982c24600144c1d80d0105040a543c000725044020b404289400c08002e0703600031007600c0c68140ea00a101c0c40d10f40300000801166584402d0181000715080303c1021000b010b50400703482000d0300d5904085046660482c901c50402d29654403090046454040030070050a0501c0800d001c0c0c030119004e0b516003410180401c0e5240701c041c0000b4102100e10080505102c5410211400c142d0f016a071642c00e20384090f019685c03500494402201c03882c10302d0380040d0b03038600f0407400d01115501c20f039181e00b006819103401000b030400411200e2401e4070340504013440c08511b014440542d10500c00da10302541420a11001005206400d40302d20745400c1c02c0c00f068003000419501140c2d820f4650400c440d085c45044044ca005042918030785491020091040603000380040c0f003007000060 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 100118750 1250 100117500 100117543
    0xa02010915050907060e03102904060b04061d0a080a120801150c060b03030c0f0c0604050a05060d060801021201050102010e0d0807030e07050d0803040203060c070506060603091e 78
    0xc80d501d08696066801d0401d41d4011003042140a0041ea0300780d00d060001400d480c41140f01114070000d60307440c0c0005550b81a000c0c07054282007000e0207204401c520040d601040294180581641d1500c1b0714000e54052100301407010700e4491050348020318180e030240c6000c40499442e22650b0341c03615190400c03a210380000c425110b01600ca040ca040c100e0307a05e0807480c1d0380c0400040c019152404060800d071802c645580c19012251010002010101c42c4500281400360300305a4060800c100d2090452080784100000c001950b1102d8404090358000c40f100781d9290101c41e01680189015803000361039500200d000c036810f84010f5517541c102e0300c00703800034170111000c1c81e051034036011303030070003c00104403104e0100b003641d8401d602c00751454129000726180d181e00c0d10005400c0d0841d405080301d11190000c104011400c060085a4110400382061820642203036242c41d01c5150003001180160760210006141800403c03a401c00250b10303104107041c01d009211016100c003004600078254a0265 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 100120000 1250 100118750 100118783
    0x50a1103070b01060c05030c010507050409110f0d15090614100f0f05130f08010501081c020a030f05040b030a051602150609091f1a01030c0c0314040b0a020109 70
    0x3004440d085039005841d454641c2c04e020040c0c8410440c000d05880302e210900841000b460309100b0280601070a0310b42c0342c4c507149440e8480c01512520100b0388050401400102d180f4283da90aa0b1000d942c407180115028109560068114203580e207e6020345003030060000d504004400710b0b4103412402c0d42d6441e9040100340e010307181c040605c9501000100d409031400040c40c03043c0e0160592100c2281c040b22101d94030340c00b084c07600d2825040394016035566801000040020841402c459410741c1200d520500307051800f070349440c07802d440601408001020052150710034411a005420000700d1103489042c450b990100801007215644e00e0751445d0305945c0e84090000403110240040c0b0300e1001c070f0594603281409002d4101170070044072071041c044440c006c880070710701c0e0452903140303400002070400c04181140121036902449505041c640b600c2c00090130342c40850490300b10781509002d02c4491000c21007407260701c41d17503100815003000480e080720400da064200001c03040c000c00d034868240314907 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 100121250 1250 100120000 100120003
    0x120a0b0f010503070c0611040906030624050102060c0a0315030303020702240f0c0a050d050d15030b040b090708011b1403100509041b090c0206090f0c220606050a11 72
    0x184c500d0700200e11540c00a42c006003264100548548600201c00d00305944c0e408880107907001134204990316507c03076211420500394034280c518403160310750390384c02c64610700b10000c1c0d26010060401d51248100080504409010380c101c0d080d0002c44545000c1c1c1c403603890030010000e400554049120792807030710420300655012203d512000c41c038a10001c0c0b800c0704400303401703400703600440b84510a80142580007002c200180014000080d0785d4449079034444000c1d4080701150801000c643c8000c46c1ca04003400456442d0344003950080e40225420784035105e90300c0e0030b032500c01994070030138066003002009602c0341a260018006610551a0b507041482d410703c00c8074050200715442043d02d13a094400b008540340c8241ca07150000d01850200d85c1c0010b08105003001d003040e68006500050300c03441e018516640c10019a50300841003005003140345508207034951100310b41c0a005100348512030715030b08501c118102407500312140a0040000a584600152198018001c1400404c2c03188203070502d100f80 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 100122500 1250 100121250 100121257
    0x1030509070513090212070609051206160f0201152d0b09010c15020408010203010e07020d0807230715050108070f1806080f06180a030207031205120a0b0f0105 70
    0x30010084041280c3d49a1824000d10040b0401c3e60f00c0020381c100c41d2100141404040c014140b079644003046141030005000030344c000c50049070f14941c02902084449041c0c406081d800d00e4591900c50000514a0801ca024244442220f001d242c0b0704000066001d00314150202240d1005180c05030f40c3d144400002400c201c0c038450710091040400410182d580f1a50790352403810b204d10b001c43c00410b200e00004c4100e0f0443d4100c0c007105d03075000006102000406c4a210342c8a900e901c008e04088505560041141320060141420305c0141d44660142c401c204074904011101d400c10700703458200381d05140310110310080400b803200d4a0800080b466030390101c5c400d019070b2900701003842d0b035920b41a610a0036111094207030702c2c115505c80011421040500114840c058490002c003454280b188401d20f07618190140481194004c0d032140e00080d40104114044a41000359041c800c0c5013141c05545034800c070702c05600300d00c190404001c00042b07580c4c001c001f00c0d042620a000e01c2c0d020100150382c17510 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 100123750 1250 100122500 100122509
    0x18040501050301140402060a050c0d02071a211b07050304031406010302010203030c03130204020c0a0b0601110d1103091f080c0403030e0418060c05090f04061203080c1312020103050907 81
    0x61200001009414114001c01c41c0c00038900e071403840c0c07140d2b5024a905103290321401e0030040e00074140c100301c212100e140c6201003c1a0040d12840c100a0703e2041c40c0d41e4106a002e006000c1c801d07000207041c4d42a604040f1140300c0b224140c65940c0001d4900251268401c1c0000c90b00140341a180c071200c18400240e4034141ca074182c005620b5a01c03040b9500d201d503000101006640c0324112080303001a11280007500044024030b00a00c80d142030740c903200f00340c0b180050180e41005030300070740c400a482d130019082c540c0417a6414516180395441784614150320400361a5034200e03100417070500c40c8482d00705461600d41019511680144c03a0100301011520682c030003d40015000810f200e9545002da000040000c0d038035458520b151003c0d0742d95001e950001c50f04802080b0b02089101d454107210500382e00032002103078100806820049174036030172601c10b94040c04002034031001800300a01c06007103a40c6915055995004141d0300e01100c1520450340307d08a0000c1e0400c00401d030030301c03030005001060b41d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 100125000 1250 100123750 100123781
    0x1605060907080309122503051c09050d02030a08070b040c120b0a0b030f06010e070f03090507140a03050114011508060108010510020102070804090506120a03022d0318040501050301 79
    0x1d003904100020780c1d007105403140490160841d21180340454604038a881454003034a403103c1b40c40c1d030130b182d41480282010701c650b5481305482c0403150b95004000806542044a179009004a0303030020a24140c0c1000d0002e00660b4009944024099522906441280b041c9040c8080503114140c8010508022000404065419001c503c140c54150800000031401030304581040f8201302038185007075004e0f88035100034020320f01444000c0c0d500200c04181c04c1c1d0305040a01c410b02c0a5510b00365110014440d0104100703900b0740800f01036480c0c1c2e40c8040110b40000007880841c8a4166402d8000000c1c4100420304004d1050303103903424041c500702c501c245416161300c1000c1c0e283c030060011898040d1190421550f08100c00c800280796407010308054041d15200240078907100052002c4414a40149a1a9800301d80240006680000e41140b174086001010b00c1032152080c02c0b0810400d1900f184000d07010100d06413900030040d0911110080045905000507681e40c2c0925080307451062011046 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 100126250 1250 100125000 100125007
    0x901060c080f0a0e09040609020a0807050d0b07021c0801080c09040203100b03160e06030d05040b1905040e090a0209010e01080c0603130f03090801050c03060d150f0216050609070803 80
    0x44040980140103040c815003019030340c048852002130003172207049504031825030b0f982c0c646809504000c0301a1019108400007044518108800112440440d602c02882e0340e0f1101c0c0001e03c0b03d44280420100803010020480f098541e11001401e03080342401202d00301e205400e0244507070b1800258040c055500607000d00380a60602090780050441d508a164040c03040300c255655441d000410400103010025100303c40303040104c101810102400b4054040001c00d0105110f02c201410844208007911003e0300407102c200c0390241c541740a035500001160440004001c0304071008109950054400c403031500e8507030388a80c40c840428200303000b085001d51215031096000d007060f4004603040759003880c801c0059240c0390b0301c841c00c40c10b2007402140000d09002c401c1145210034007421740c111541c241c0140c00d6180c00b00100b0700058060001403d4000c0c0c81141000d01d40b00d030741c00494502c500c0d400c10365540002e40303001c01400c88900000c455030f06c250000211045008200c0302d007514a190040c526 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 100127500 1250 100126250 100126267
    0x2010e01110a08060414010b070c0905040317070c020301060e15040e0606010516020a06050c06092a0d06060e010501110105040c060e0a170a030e010c110108090c031603020901060c08 80
    0x1031003c0300805003600301e0354030914082400400310070140242103000f21540d070340b40c5a192009140c05141d1190003014105000d00c00000d400070092030703404580d4046c031151981d6419007120035489911010350103510f0040d0201d817280b541d411a0344644214196441c036845210309000c2114400e04002d542c581022010400540c03241c1c00510007121034140c3c90324a074181d0b400084448016500c01c4c4041b1f640000c0c00c070000c503014882c0e03a074858000c1010780303140f84020521803c00d000c0d202144038003001c1d500e840f01d015900e0f1b1614005c0c46421490400616403551b00350b4001d04008c3c02145d0100d0030980300325201140500a0a00c181d0b4000401c0603800e180070020744422030030410540d0700005c1ca0038081400c21080312010022013400e4000d051200b01414054441c8407642c644904010040c0d1b40d0a0124010302180c88040c0c2d070a190020071b80d500c4841c3c6a040c24071240056501d801100020003420b08202c266600b039a000b03e0f0000170503660340d202500d4004011500500c000d8040c464182e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 100128750 1250 100127500 100127507
    0x5120d0c0b0907051c0b071803020103020913090f0215070503041a040b1305010e0d120f020106090911030f070e01060c02030a0206212a1818010602010e01110a 70
    0xb80c10078078a00480b4940d544580016450307400c080a46280c0703120003000c0d48103101c1060421074100605041c0b003410000784a140aa2200c0305000190605800042034441c039100c00341c0324044200c140d401080042c4040c54000b21621950754264410600d901c0030010801245084074aa1980305004600e840d10780701c0c6090b800130040d00385d01803101e814400082c071304e8100c50051485400501e0340700104c43c103110000d0020b0f002c4158250040c048100644005405002e400e0940b001c541440c001c8251640001c80c09025640c1241d0009401d20070140c040014000c14140240011800c1d035203050005d188480c0e4075549449210848a0000010030050f4002c0b0300781c940590018040d2080c011854022030950b51003480b10f003080e400000f5803881202000f9051603084002041c81034801c502e655002a51030822a0010034085400aa8400169904400d071444c1000c054400010310b02c20100c1000c01072403d10980008d075080000c0384601d0001842612200080007200500301494980100c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 100130000 1250 100128750 100128773
    0x40e071205031b060f0709120204051b0a09031106030f010e0408040305030307111005100501030b060c0106060c0302150106050706020c150109021b031215010507060203040501050105120d0c 83
    0x1030741c0c2400b0400c03981d181d000119040f020306444401c010106800d05059407110504018091020040460020b02070340302900850640c164044038042a59210724428584080e016125454110301c0002e1003107005800503c2101168040c014000d01c035001d08050101c0c52008072507103100e103003e110041c00801800d49103540c02c10300410403030341869100d544852840e4402d0780c18402150b0a8038620001c81c1d010845100c8000741d54500380b1031414030f04120040b00700540560340c140340d00c4414426868440c28140e0f1000ca400c80300a002c080c1d644e605c0a0b00740380b0080c1c8141d005020f50030843e0b031945403e02d5040c2c12100990340319841d20003151034050082d00542e034050f095010352040364224501c49020700d4040d01d999480143c0c2d0324007402030000b0788002e00c50015103a40080c001d5100c00c900082c102a40000d075940b0b00381c42800e08030012a85031260076001040148040b051206000b0305612043c10b81c9c5081d2000250404c04580c1c4cd0394429150070b89400240b055200880081c6000d81c24 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 100131250 1250 100130000 100130003
    0x3091009080c060906060a0b130605090f040504060c0e150403060203190e060105010f031406060c0a0803010303090e0601091401030b12070305030d0606030b0109120302070308030a09030905040e0712 87
    0x40c208000125614100072095800c40704030717409002801a64a018008480140014221149400c03500d10b181d0500041a200d900180100818112081d0301c0340720742c64410030300041040006d4079062800000424842000b030001510709500021203091144c040d44034104081d14481c2003034515a5140082e41c4002c04c3c040d08080d03070381e0070090800c00b580245a82820700c18042c00322581081300042c100b003134482c0d0503010142401c00c0710301c1b01802c203007000b600700c801516095512070b280d080d2035107400002c0c03100500c0980c0000c000000c3c5a40900c03100c06a50302582840d00603121540111008005400345d84d40030384c00892072083da58003075401103d11480160281d580c00702807030301d00c2d4106042d690080d225074000240e550b1040352103100d59000380850703040030442180400300003008184180144142c092088802d041410b008006010003103030300a072030540e40d240c004440b501030107405808070701041c8001400309840c90603004010398103400e0320040048a15040c1c000e140c14140c80030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 100132500 1250 100131250 100131263
    0x10c0602071a06040b0a03080c01060b0a0906020c01090e0a0203131e1a090706080c0d0504031d03071410090b0f030f070c02031203071206030615090203091009 70
    0x104000150a60019041c000d026002655201d64402c2826038602401440742c2d1082e45000e41030f1440b0358409028006494011a985448062a40681e40104001d03040140d500300080740386106141e01003110b005844c166800c0d25030390007912005645d00030ba44e000d0245841000c0000031052480c950107964002c0c50420420b10b660b14030b45548a00407100b031004480d1229941c040380c1072224a40300d43e51180c0242d82c1d2485e0380d24040e59100d88035001d5004070b1080003050780c045030b0340d010307050300740e43c11440c2c600000c118504241c41c01400f0340e28001c009010550072544505c07564a4003081600480e01c00343c4000d08206070710170420045801001590081c880c001101040d1030078004094000a114400802e560f0304003140c01060150004018200f0490700e85034000060307c01044c40241c020500c2d080a4132500c800c041a1360311950a8450086c0c2458001300100340318441d00b010000803071802d410400781391100c0090042e84012141820b455104201c105980305183d071005880d03034080e91707 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 100133750 1250 100132500 100132517
    0xc050a0c060b101805150405010c0201050c1f05010e06030718020408060a0f1401080a0803040c030b0a2901051213021305090c0603131101021002070303020d3801 71
    0x100001c00021144044000013100003c00c0006502c0010805010340001c490003240100340040ba10f600e445180100c1d81000814005802164014426038500c1844102515096a507030b074034802d20030403500702d07610390f050424000007040c00e945203200e8055040070b0b01030305010f03007800c03440c0c95014807161101185990030480020349500074403061b8001d080301c16000c80c4840074080207500b507a806802c0c40701442c08000041211400004010140d641e100441c3d40e220341d25410842031084450344040d1800c110001045003c05141e80f00c139480752090040c04140b05212040c0c0010611540400ba010030001c11048004003002c402803039020f5505c004168404165501003800451100c03d207129242c0c444040c06031241d810b0003081c0075040c050b2001411440e00c10400b0040251000000e0484d00c40d4001985032a442030200000309030600005559805091030700500943c006102a49080e24100351001d00c0700440e000410441140700b16101e0070844d42a0503110401d075680e40c18113015210303 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 100135000 1250 100133750 100133771
    0x20a09060801091a010501050d0509010603080c011401060e031e07050607050d03050a1a040506120d0203181206010605130f0e070806010c0b0a0905010209090a06030212010c050a0c06 80
    0x902803140a80703028400418603243c6443e1080644c40c0c1103958912807540d003801070002e83d9000e0290740c035101c8041008038843e100c001495004114a40004c1c0c030741080020841100503054205142400c0e000310b410800b0307a03075178508a402d52600024550f26421001940c0d1012402c17295481c083c0c1404426a0501c650f6240021a66400004111001d403c090150203201c1d41520441c1c0d40046141810b001c0e0030101c281c1c40b2200440c20388100d100355512400b05d0b503652100031207900140c10007001c44502d03101008001c3d507030f03402c030101090f00b07038120a0300c1ea81d8a0420a000d4080000000300402141c0d08100c3c040c0d81c5900100e18090140385080f10025003540b15110340e0006040c14103c03003000381000c140c01800300a00919050600c2000140c04000031101240240c0c003160186001540103840e2038180d0182c0b00c1d00f05202d911000c41418881d18402c0c0f035000e23070110b030310843d01000389004160407142660002021000815800e100f00c04425000f40d202200c0b25101d40800a40c00808 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 100136250 1250 100135000 100135019
    0xc040b01050d0c170903030609131401051005030f0a15050417070804090534091806060206180303040b0606040b03040506060103050106051215010306180504050c01030603050c010c020a 81
    0x7184640d40080d040313854a01103039004050a503040102100a1851480c0c808046013010001030720380c0200540c0b8500c0801400000c41d018040f20f4a035800a10050503c40380003801301139940610f52090041c0c008850804100065a2080341e40c01407505c0c14150102e44400020301000300291241c00c00c1c4400440507422020081c20031501c140007541d2110705003517100049403002400410b075a10300c50ba420f0404050783c00000c48a0a001e18a00304144110070211031082540d8081c840d82c824294104040c4c01d5950052400d4a81e41d42c00c80ba8160780358a0040072000e180036121b00c603508208081400304204260403688204064100ca1a0554514103c06c0e540e1088400344d51603002041808015030b418002c04cc01005946425410090742411070382c540c14020345403990781400c062a82881d0307400782d044030004048103d0300034019031700040c0ea00003130801113401312114081d0300301942d41e0350700900c15101501d40040040c00708070100070054821482549c800d0364440c0380040b00145503c1c2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 100137500 1250 100136250 100136261
    0x4020f0604090906060603050103050c120f0f0f010f0b09012c091b010806060d0e010b03030c03040306061e2105060a06030b060603070e010c0c1d04140106080c040b01050d 75
    0x104600043c400410b802c100c01203440030f421220806040000410100b0300001d8840720002045403004614204030794036925007003000315905c5260045e90850031510764041001c4406000c0325009210a221002c43c900131946413500803a8004019001131014000e91076a030a80c403c02240c0102c1c2c1103209055032a0004000ca840300486c2c0c1c8800054207000f440d56000ca140c3c800e00382401d038540d00344240010064051000d038107210f2603540c4040b070f51710082500404c0700c482014042e03e07a04d440480303180e5140c0c0c0c081c0c0400d4803024104400091900c40440b802400c003c1c402491120013410800b40e0410310b031144403488481e8140c001c4c9140414401d01615004000b15003000451034590f14090089420050000d031082d8400d00421901c00d40040642c604510240b03480740300480c5621700309010107500c0e0801005807030703446507400000c1c0d1148c42d11070140e8010000350720004840e10701d4900340c0307044d80a08402e03500210701504590500b60405940e01c0c4050402508000c0b41c170030201c00b00d03070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 100138750 1250 100137500 100137509
    0xc030d050a060302100206040b0a0b03120d0e060106090506070201140d060b030105240702091e01080d110318090a09050f01020306010e0d03080c0a17180f0102040e040b04020f0604 79
    0x2d40d00c280800451600c40303084120f48101c0e0000c1c1c052450301b42c550202d00500141b0f07429002d62104050b140da07540074000c02000700351190310306442e0752014003103000a00043c810344059101f940d00118135a40909402c0c400c440004044c01d1522000b640111500440c1350400092042c05004200840c5010b000350030150a41840482e140d43c07501080000c0d408820f4106911004084e207452105480b18040368111070301a41c5a01c0306464003444030301c0c40c1e00308151103009600042c00200d00c0a0307022817100b40c00e101c196200303803040242c8070b0915128461fa252a851110302518290720b0350601e03d136101e6100701981400610041c00e52201e0781003580c0c601c101021a50700104000f107640c1c1220241c000f0302010750324007829010700e0350080d2200301c0280c40c0050011011400e0114070781318140314440c542e0004e080704218288104621852084025843c865000e400180350158005100b0388003200c0503543c04a2007512107032a4003513441c0300640240d8200c01160010f18107030302d61100074002030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 100140000 1250 100138750 100138771
    0x14040803030a0906050601050a0c0f1a070905010215060904060b030c0d06090b010b030408070f0f0c0806040b0a1122170304090f0605060d02130f06020c090a11040303050c030d05 78
    0x91030286013080440307030028030480c144101800107404440c0c0c021162440c031603004c1048002c00c4c00c40d06186001d034140040149050b2040c030708100c4096031060101044030402e03001c07618038a980e1540d900014070704036000c54115201d080090041011074018489101000d0b051b111070700401070101c0c542c40f410782c0080c0c605548036405c10007084032085101e8014090151154154102556020050311480f14081e0504000c0103400707050000305034070b191000350b02440c41480140c1da6101d40780c03204800c8405880341d006840004542c2d44040c042c1880701c43c07a19912610b415266020080f40a0b050b00c601401c00c4c8100d44003180440d4800c0c99106400754900045444900e0008040142e800380c0c1d580c4480d00c1d00b4404200400d031600c100750348150441d4200541c07250070b0b60640720f18001960780122200e902c0742c00c0014460b9008284500c40904c1900e004409075980d0100f42d0584100c011030340e445140030003042001c00d200d5400707004401c4410b0142e030300c1c0803445500303081503030f10076699034070b00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 100141250 1250 100140000 100140011
    0x20603091f0b01020d0c0302030d020424140301090c020f0f0303190b0a090b130903091505070b01050f030a080406020319210b0a050a03120207170601030314040803030a 74
    0xa4400203501e4012007501040034440b403400000000e4890700340c44254000d1001030200c0c482050300a10581c0c489070480f0b403045407299170340d416400c400c140307040081e031104101014800030544603404480c1012044c0050f10303d16440d1180003001424944144001c500901c80c81c00300e090010310412011040310b000543c0c0700c0c14400703807032182842000031025403070707241c4216511b00e911054a48811610524000500c1d43c0b002c40200c1d540c100031a401540f554980070994040517044006881518040da030101803200781c030141520036103d18007015080641c0840108240c0c5410b0301544000c070405020398000191958803088190042c2c2c0050340540c0001c10305603980c1c030b801e0b400c84001c0c5006e40703011141200f4189841c000c1d94002841111070540318500301010384c50700d40542d4001c00018000400d055580c0c10183c208a502c0e020030300060080100c00200c1aa0b4501c0544180f0120809030460745d18590342510b00440b100c040c1503100c00c013408005110f08040c00070703520849582c44003051 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 100142500 1250 100141250 100141273
    0x90609060c02060c0c0706120e01020a0201090c061106010b180a0303020c090c120a050a0608070806011e0806070c03090f06080405010501080f03040308090a1224020304170a0c02060309 81
    0x2030000044c841a03000e00288200c0e940010300017035010845000d03040c00308046c140d20b68a50080d181c0ea0007176030f019600015070704122580c150322401145001d001c00440164440800319800d08180b042000c045c3e1180c00180aa1341c0b41800401d5051f009004101201040300d0201c1c10041c0d41c1e9005902603000590701d038000d4144071150f0b5512148100140b840c1080c042140600500d010342500c18199413100000c411001030351110002e071802c4c000700c0b544241da6036403090b941c1500b405600303248d80b01e80300540411408005038005840100001e405e07556515141181c00580455044d41000818140095500121000d91000d888241d40b507000d5450720b03041103420360300b040e4400c1b0425800301c6001c14801001201340c0d001c1c0c0354010071443c3c1d5a986040001d030b8007003558001d9a140242544940304208950f0018254030031031408000540076034903c0b500490004440c041e0400d4045160301500000c034034000c1c284544c6e00d003000400e04a1715000b203043ca4008541c02c603d01d40c003401c4102e9 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 100143750 1250 100142500 100142503
    0xb0d15031e0b0a020f18030c150a120911061e0a0c0b07020c031207051005010f0302120102130e0a0f092003060c0702090705121003030f0305062101090609060c02 71
    0x194070500640c820b40c50030020400540c0d4900c0f1b07003080c59500d10000c1c003095915541c284a4601c290b040100a20034120320002c1d074114540c4000300040c081440c1d020030750f05814440c051002e1298124100c000c043c1d01c404140003180d40140140210300d2007070031940c40d805060303001a14209600ea514881014803d160003076600c00040d1161081d94020641c2901c1c0d95400030b0304800400090304101d882e41c6562600c10301c2c2141e00c0680c40e032041d0030300001084282111031510700712402110340948a4001d0310003d4200c0c411503414002488a2440a02032480702e02102900f00801040c0091221800c3c0045811100214012907541450310085040100c910007001d01c0714100300e0107006581420348410442d4450098003d000d03018000001e400030b8022416a21507940c074101c0095185845c8185050b007035a280000c6001c102030581d0555000d2103489064400d41020700ba0b01801e090240c056a02800e0041c0e505610f9929040c0d100002941c074003454421030300c00e00c0042a15085c07041c01a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 100145000 1250 100143750 100143773
    0x5070507080f0406030b1e13020c0a110f0604060f08041a0906011a0c0703020f010323010f140f0d05030c0d08092b08060a05060301060507050c06040b0d15031e 70
    0x181d07c106c5010b0000b41143e40d5040203001342200132550b60700c210b1802d4020802074012404550180c1c050f00b1008070510808000e8102051400c0303648840c180034500030440d150040f80100400140c40e0b818606505010f0500031703802501a05000c160346101c2d10381944160b10440310305103a45c0007200100700085240e0b036240b009011094041d4286a0703104d4040e41e44800d00c0c44080d205020134001c209059000c1d07807142c03186800c1da810106d60382401241110158001384568032003940c84090024081990b03106414507400010078070000440c0b410704000140e00c01480554450000700090b01c0c1035581000045505809a00d40305c005261000325181044218001c3c824172904128001c038a010b01c200c0c400178604041d007045540c0d61030703d80119004000b10780040b0b40052000002080b01c50308a40035001c0580700e0700450700044400d0051000c41d000c0c82c410020312031030a2000305402e00d0300703802400d42c1101e0740c80c403401200d98948a4a40029001c3d940c040180319a141c8403090100b40c040308d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 100146250 1250 100145000 100145021
    0xa060f0b2d04050c1308060412050711010806120d0207030c0906030203031b0c04060b07050c01032c03120106030b10081e13020301051519030506040605070507080f040603 75
    0x14004000841c0c410140409030401e041d4440c0ba40d07003000441442601c025114000910048480080d0300d9400d015500c40c410399040c0e401c5d100d90024035a80f948200d04072118203510079003074810751030480010340e00030b94041c11060780301201951140c00000b0407c01103244403c0d55004003510361a600748890780c01f440d1703041104418148a020b00c0541c90000803a010351010207982c4c40101ea40c0503a440c14250f11000e001c0c2c0c40782c1044c0e800514010a040a043d0890091050700c185007101c1006404032110a0340f1175500c1d1f0310500464194045100203a000c4610000541e850b0000b4004410b060b1842600300b00042941d030f0801c0c100a0521760840030b040f5040d418044902e0401d0360140c01c141c070302600d40c0240041c8207070025400029458405110560103002845141050502288468036070407055000d003c0d8035800303000708100d00110b04112034000307014011903105c0c0d488540251000034420360500500f042518005142c69004002c0c00d900c2c104110f03211400c2600040075102000c11 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 100147500 1250 100146250 100146289
    0x50d0905300f09010c0b040b01030317040c0312020304030501060308041505040612020901050c06040605092406040905010b031915020304020f012304030f02040501050108040c0e0601020a060f0b 85
    0xa0708403641d51660200c540a01c9102c592a407164600001260341e11117091005048440040c144002c002c00d1844107410780348203450b036400380344081e014513005078412078018040b902c030131804002184021440c011148041c0c81540e151030784030f031600b13401c1d501c00c1c1d80704587d054400101045014610b0402000e60641494113901c0d01d40b501a005114104401c580c480059000402ea40310760b02400488062200c80c8054505910b018245040200801ca40d140c0c058000d180f41d02d030a0070304034404041003402e50f40e502e64458840c1020303c801031680400803030f030a40d030340d11a280d40c40d03038200021005200f003400c2c000a0340803030b89844500d8042c80200006418014014440180c0c1d030f03400030b180260000c2c17811080c90b40003015a403003103684c01140011000c130b0005010050000051070507405034002d175014000e69a9407001120507160498001e04880841d02043c0000ac40076214142c204605104544021140341c40d6401128a4074210b0040c140d664441c104081c286a01c6034a0f04040040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 100148750 1250 100147500 100147573
    0xf2d12050310030803060d150b0102070f1d0a0e01090f210c062c0c01270302060a020304050411030403030b0901032001050403050111031e0103020a030201050a050d0905 74
    0x302c002400c0c0d152800014103001d40030000500340c1d1a5201c0140c005600241c0b1211a012020003a0005100a40c60240140100703003002c210814180340d000100c86210128026421079440c100750145000f502581103283c6550b03512581a03024000c0042250148070441c80c110010720301040340ac1e1140010000d031810120b481c240d8039402654a1110b941c001c000840e52505400c2c10044400031a6042d0303c007004c0704064819142c40c0001c0800c6007440a0301c85e0b81549800c03800f48a004001c840c118060100700309400d000500301500070700710002090044a00b00394440b0300260a07603031040381c0300c4540d410200c10007041c1a070600a034044664103441002d61035045444800311a88030342000c4600d00040d940800c03040e407040044500450f0000c000f00b0004d201703441881b070140d1040d10450703035800c450155141c1815030000010f04890380244111601c9146500548158100d04405010f100042c800000d0194040c00f61282d01481000540105110100c880b07048035510300d55070740550340b001d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 100150000 1250 100148750 100148761
    0xf0a27080910170109091e0206121602010f1404350d0605060c060f1b07050312060114040306050a091b0503010c0c05070326040305010204080715020a0f2d120503 71
    0x1c4a4040c4007408007032041f6594503a0010400301e02c22102e442d004c43c01d0307480401c00c82440030343c40030502d40580d50007403080d10103040d030004c1551410070726041800d4891780400d00044080302d10100411400000304602c40c5046101015001442448042c81e0000240003003000c06500c1800b02406c81141d4050400b40d08800a0f542c694000305051003400a40003c030350f50900b00d5030305516a060100100c1c0d80d8404500d4955280e80001e04013141d03071000314001c0f03081980100700e01000060200075540c141459511a1406040c0c05040c003210140d0b2182c191001c03886244200040702d28010292001c5880c02d801d0608481030402d8407410050407481c901e000030030114040080300c1c3c005002c410f00400000c000241220007182c50314a02100003000810848190080c0c0121040c84e000d45001030340d1401502600440040141c005030018030000c0c002400050000755100d0240c441c1c0d1782d00c450341d600c5070070007403000e02e0f06100d60243c260400c07810171050541c80b5007185105d190060450800 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 100151250 1250 100150000 100150013
    0x30501181a0c0906040b1306020c100302030a060e041407060f0905060c010b03030a090303080601090f17070b0c01020711060408060103140f070e0f0a2708091017010909 74
    0x90107041c5518500402198504002d00152030300342c5070051640c0e58079070b5104030001e00c0342c1c003803c0741c01c4880694040000f05a8001f1a50140400000c0c010307a08400c008401100250b01c02050fa00495565450100b1104030003103045200780d2090341c0d83d0030800c14030800d10780b811050354040d1007000b50340d001d0f2201082d8415801e1085400a03105da585503003510583d40d0240885500f9035415110200c0d50850940d4440d4010040ba0700030744540030b550702d0701c42c01110401c49030701030b004401000101c2000b190507000c4100c0b44030540c810907641842c0d00d5a0345422180c2c400745510001d69004114030003440752030040000c602804640651401e482c041c0c0058807004144400340c982000d0b001e2402c4502024003860071500700040649010940300c9001090520058400218000d0401300107040c104c424407900140003003401110800d098401010480214bc000341140c4c41c0f002031002c440c5c5611182c003460000f261588035201c000f0014030070400140740503408111898204501603000c03803038 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 100152500 1250 100151250 100151273
    0x120b0601230a21050708061f0c1101111f06060203030103120503070c06060b0a0908060f04060c02120315011815031a0916031d0705090a110d020403050118 68
    0x1124200001c50740000070700302a01c50f84001c032102000d41084200301c100d0380d10078019032042c0800c07070b545103402e4054160340001c1800420314001080c110040c580100c0c00d1103150b0a141034051400103980300140a0310f031308001396400c14030f22040356088101102036581c01110007501951009504643c03458640340d440304111403802c4203120001000c20f50a500c100c54201c01c441d0060300600c055035880411440c0c0b80e011301c111400040e40c003480485c0c0c2a001260b01c90082c1c00101c0b11f1449038680c1d0321100c00810500380c0c003100350b08c02c0c4040c000d40800180b024500c281154a48100100c1254001510768a40410381c0028285c074110240102c4000a074580403540c00c0349400039200c2e0b5005d00780610055081c201d5907011042c501040301607680b40c240e9999850065a090103445840c4540c14082c10b1200800c200e1500004018401030a200c198558401c0350350002251042c200c40d20b10343e040c0c0c4032401000d4090b030001400c0c020b128007400b0704184191007240e502141502511035032101207 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 100153750 1250 100152500 100152517
    0x207080c011e021218100306032f03010c080610110d030b030c0406080109030f090b0403032610030506090d1403070908062a0309061f120b060123 64
    0x200c007850402d0b1041c0700300f000b02c0a52041e1440302d03903148419059a80d4606110107039921a0801d5002500d14910901a002c1141e501002000c0340041020100718070b00c100030a40110240c00f05204e04c8280c1d403d004820b6500c40356240e04100382800401c0c4501100301e406034405200d100c0010050070440001c901289400d2860001400c0c400c4000007400c00080e4401207030300501b040302c0850340c00d006500400203c1d1280c0c80f0800100d5845500307880c0c81c11184641d18487c0d01c10b100820100b0f0060181038400351100303900414140c6441d0b204003900c1820b035000d03060070341910001e000b00101040a15000500c0368000c14024107030380c100a05d204c00b940191203514038044040745009024519034400b400807a01135a6251909407140c0d51400c00306d1a510b0f4103200900d44003480401c015040f81d014054103405480c00395110307182e410807a01c1c0004070500821a0307270000245541580311307000c0320038802c103100c040d1401c0140004100040d01b800e0141f103100907a010803901041d0008540400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 100155000 1250 100153750 100153787
    0x3030206160201140705031e1627080d090e2202061308010c02100905060109090f0c03060b0906010f0207060f02030f03010b071712070503040807050d0309030207080c01 74
    0x1607a191808a0140482000340f03e02a0716000900a19541003405148542c20300c500c030f041c54081c01c5000b46001442550340c680702c120900160350b03c6034810256807050020442c0908608904041d6004040d0441da2080340d45400c4401c040c4501e65210901c80d00a0404406422003400e02e0404036201e60020f01450146418a0b1950790031510303180b00380c501480c00c4400381c96505036503401e07550181030070100035001400b811000d01412091071103000006900480180781c0d80e824081340030000c000040041d150181c8000800c80040c800e107000700080c52007080c0100e40031120105000e25010050400c0f81405215040424007643c00942801201c095203408441401344160aa085110b400312520342100700100201e40c90107800002c10140340700b021905214444a00d56000358003491a4000d140500e003008224100e10640c0a550803e000b040d209241c1402e50b503a03070389040760f482a86030101c0d496007000c80038150140032078401888160060400100710800080650b40c0940302540c01 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 100156250 1250 100155000 100155031
    0xd0c0e100b070b0708010b0c1507090b070807060f0605061801050c01090b060a08070305071203031103040f060e0309060702011b02040501120b0a020901050403060f0e03040915090603030206 83
    0x16680c00e14000024000074104a642d5940e43c2840e00070f0040c01c54002c808954010000981c0742030079001c41e081c07070901e42c018007140f018440c00024040d0780070f050401004224140490040110030003014039502c40c0d0300d01543c400903441c0c4581a01d0b180030700c041d055482e04200f0041c03500d903402183c03025848034928144c070912200040c0d0345402810140d40c407640c47c10801d40b0030481c04a1210b4008c442c101c0c3c03500e91059441d0301c500e5503001e090200802c141c0014408000c01e14811407501400303886400d0201d040b0429103255000c9400440f000d44080210005020903c609445070700c080d00c80c03040196184c04540300c0410042d1042d2400207040001c01111410a45403c1e8102088990700030414491941d45d02c0805020504000c4103550021640002c580203c000d842210003212043e10b50904051841c3c43e05001440c0e4400a0820607446668404c100c420501c028005010072000000b00100010402854031516030032000c4403516028052000c81e03000903500c0d90210b50140c00707044 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 100157500 1250 100156250 100156261
    0x30e0108040314030117060105040209060a1407050d030506010f020114060d02060c060a051803070b040807020301090b0a0c021e06010512071203020309091f0e071709100b0d0c0e 78
    0x680f00d8448219041000c0080f002080c1c00c5484000100400d0069046400a98a860400040f80700e00b002c2c5031f510032030030050070341c016024600c20403408044010b8142440d140e92142d40c100076401080200181e80c62081200c1e41d83c20400c1d0082d800098030003044440410b800c50840854007134002c6200e80111070540342107658a204071102c0031580420360b509800c001c1e500d500a450140c0f0640c580418805120344807030030000c151250a41c10101c51110f070784550704d03020160340c071610f0280c0c0c140d52901c0703010000c910701840c250f0182e41182400100140b4105c402800e0040400c541406d60226129240500c0400208581982e00455045107421214100185019120f0b4449080c04101004203000d2580101c05030050390025a444641c1e51358000c0c41c1964501c44400002c8820364058060000604000300a0b17070010740f80c1030400708c80c6031000700560041c20840d200c1c1e43c281d0004551102600a07030041c0b810110042d40c1c500f075a91601e0343c8041c001855402101441044c04c40041c2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 100158750 1250 100157500 100157507
    0x20c0102040308040f0f0e150103050415020a0903020f010207030503030105120a0b0a0b040b06030c16050106050a0e0405010e01020f160f06020a1106010f06050a030203040507150203040609050d030e01080403 91
    0x1c004640c0300070025034541c0c1c3c848551000d141103204010b8885a01040020305040329051035110f1040ba81e0f2140c4511105c07801134000b410050000c0c0c8041c1030348201846000814801003031300602e1520341607007491039481041510240c28075550b0441d00100001c000140307000040d2415203404840490389502d07010a200e20b0007403c1d0300007602c403601400a202802da800d074000a0f9500064600b800407801c44405d00c542844290769800201104218101c2c0108144444d52070301c500c6032002281080d51074000600e02c50441c2c002541c01040c050034407080081c2403240000d8880d4a030300a5041c08022088036200d401011460060f003040340306103101300407510031900e1407d03602c40070454680d0602032005280d1410703900c100400d44a101c001040c050210b2040d00129011a503400303280c0040d40d0800c40194102400c11102c3d1303c00e41320041681854602c0d0303124486102d0340110b8481d840c0c01382c020f0101c0300c0c0f50300550003021041a95404a544040c040200302020708141c035654441d4076084 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 100160000 1250 100158750 100158757
    0x40503070c030b010801060b0702090c0306011116180905060c07050709020a080402040e0a02060d0b0d06060b0703091a03010603050c09041b020d1409042f070b0f060a0306020c0102 79
    0x52101c1c09803503020040010360009141641c1459000b08142601c5146520052040036800795201424400060490081200450384a041031400088020300707400003d14050705a021400036a0410005018104600d0002800d07a42240070038071410469440d00d5850300000b820900c10413074002420402d0043c1041268002d14000408658407241201c0040200c54155003ca1007a800d11a80000b50b2500090000e40c55030000e0903246401c1050000b10000c100c580012504003088200380c81c0842c010b81710300c10082402c04019641c845003071900600c2c1c400c1c0c03600f101810881800d400130f4900580002c0e0b07815500c0c40d0400007610303100c1e03031301130440d50041c84c1c602035000d41041d8000925500208508403100f40d0398088031140c0321070035002c3c0d031040030008819014840c00d0012000c1490070760455034000740e8402d61a40d00e06020601d810903158040740d821101000081c61504010703010305056804150460903034100d040030400100d0030b83c9544005003400b50041072500003004d003036040f07 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 100161250 1250 100160000 100160003
    0x1b050717091801090605100804030f0302030703180b0106110312130c0816080d031e02180d260a020d030b0a1706150f03070b030709030f1425090504050307 68
    0x1502d40c2d0342c3c1d220a40d10140246010741401580d174112586260740c000c0810500459050310b07410142081d00000310300030340006050208040d1540c0668040c400d0392407682c6040b0340940401d41c0158186940a02188403030700c01c601c0d0740e61042028103c840d01c140720154210304883c0d101e00d4100302c142021545081c00b0741105017a1b02802040e042004240c0c1e929078200c400280070382d003075880f06070b00c181d003201d00e0010340260101498810007011384540d07004119112009528660f40c0c09008040703001445040000c4038862002000004008255003125588844044c216413a126289000035160640c040c041400e046e240c40c04600c0c265200714210020f0a070340088c0c0390b400480134450581d00e10040d51000c0c0400c401400c030350120b0806440b980800700c4050014805540350500e10050755000401c03101c104030440c2c03c00300000314a0114000c7c90b90041d8900304400c21b0f42103215003440101c501c0340719042c000345005181107042c019918105c03170070301c40000380599960800a0562045040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 100162500 1250 100161250 100161289
    0x30a03020d0204091802040b03030324040f0618060801090201050703080411100f0e040e0705061b070f03060b0a1a0c07170f0d14031501050c0109061b05071709 70
    0x540d83c140754185d4584814000c40f000d1000c150000c0615440b032209481400640d10400c00c2080c0580700420810009040175000103010800d40f1103100444025800411011000c140c03c0213003034006d801184042e01020f0000c01c00032600f940040d0a034030030560001c06212000b8002030034040700c210a148040d5024140c0f84000602c00001411180c010600310301249031180710881500305403013140c0d91080d075013004002c0701d4200420421245c20000164405141e808a80440c0041c28840d000007003440c0c0690310079460a514015054590000c00c25000ea807002c03604112528000001c4c1114074141002a5034500b402c54046082030455081400035001c8842c280d5900b040004400301200081d40c1513482444d24a08126143c40800071012028181030020404084031840f01046098050510903c2d008000c4081825900341d0541074907403a998200516448910740d22200e101d240398030f007180c9094003c3d512940d030342107417507a44c0103001400324512042c3c0d110994165100c41b0301c200c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 100163750 1250 100162500 100162511
    0x11070f0501020301230d0602220b030a05010902120406020f0d0203010e25020a0816050609010e0c030d0207090903030b09190b01030506091321020c0a05010908030a03020d020409 78
    0x34014041d40c000c0c491181000a40150105078030340c00c5600e400e00360b900070032032180e5031403135107a45020790410903400030950b0300c2d005000c01c1102844200d0009004000c200ca880345810b600c103000300c070b0050340145400c0340100b0500f070515915084440d805503110344016140e0428042214850040f1141c17400c5451000001042c80c401440307070701e8403e0351100212104254050507010038280008000001340c0d0004001d0701c00160080301421180c401d4040c00780061500340c41e80c030704d0040b00b50b4543c11565990020740340c420074107112820f40e0150075801404800f2004800954840451050708405070703a8071a0001010312030380000415100c0103000c05030504000102c4034000c00902c14205955162000e6444154000e0281c7c80c8100c50041000c0756aa0310440d100c0d003d1010008102d56801c0603191030107a509903001401d1503458154020240d8000840612441c2611034010301d0501540b0360381005090b500200300c40040c001c51401688450101a01801901940c0c0040c1c07a03240c20170 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 100165000 1250 100163750 100163753
    0xf0d08041508040c1401020304030609060f0f0c090509070c061a03030f0c0106050f0105030f0907032003010b03070308040b0a0e10030b0f0a0503060c21040c060206070f050d11070f 79
    0x20610b58000c0d0b0241e20600d004503510700d58800201300d55910140517810902c02000860700e41d0340540809030040401080b44502d00d4000d070202c420a40e0403241c02d80c2d03101111911244e006000d140030b07110544124440782884000a4410708209800521094807020764170203501079030320030b007442280140440f6220040250f1040702c41d0400780c2d0344003141d032038101c4c009000d00e092100c0420a240685485103162107501460710354a030003c003c6020352040000c00000625404a4078020201086c0c800e038100d0b21000406080d560140344c0a03101e50300c402018800308241004a804582c100314500795120305030042620402100303c2c1003940041048105010306400d500603a4181004031400c80802c2006420025401080d0040c02c2d01580040c00041040210100411081403040e00f6580c8074001d5034175010300b40c20101c9084441c00c582d40390801140d0b4040105640260443c05c026070304c8032141400a03e58000c0c0d441444602c0d480c0c144500b98050f2032411540307041e4000f040c031400e03500c15 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 100166250 1250 100165000 100165007
    0x120c1808031c0204120f03030e07090f0b0105030105090703020901091505030412020d020a0b0a06090e0319051611010c02030f1528020a090503030c01060303030f05060f0d080415 78
    0x114402c1c203100400208048038142039200f2141602e1001440c811400e5440e00d400c2502114884110241992a50032085000d0704120300d03c001c100c40740003c2440040c00d6101030a46085407545418443d0074001800155251100309500c0300240c03800603110f56031507004071044000c030b500c2804c0c041a030700580d1303030520382c02001580f1070f5004400191611440c02c130201d0741d035624075a004d070042c1c2005001e4030008984245450b080130452201050007502c90542d84202d440b400989807aa03070000415078074a4428403010402c401d8103042460408034031070402446150300d0f200041c5120040244045145e0058039403600054020782218031050032220026901d584514400005220300c41c0014100c0094090883d00030b0400000c0c034600301c200c12880d2000e50072011320340d814001220f10204060310701308060720301c800300c1400100c1d185e403840c14003031304442d42e015280402c1824132007001040d4130b5000143ca050242621480030281c218105450b4600864002400c140107a20444030740b50390 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 100167500 1250 100166250 100166257
    0xa1407050a03080c1e0c10091815060e0d1401060308070b04020f060f0a0e041803050d0f14070804030216060c05070504150b0708070506010f14030c01120c180803 71
    0xd1405c482c2004001d107050002d16030724009216840d48010f012042034245031501d506041554181640455140d41c29010006040c40010100f552390382001841c1441400d802001081c090814400400c1590042000d00f040307900090304150f0031039100b00d80800d096000400450b08100f85075280c0016160168840809480a0707120b608104031a41c0c407454550116000c030303500c01c590359242c64101d44058851000541000f988540e48003944c0c2c1047e1100178603020070341d2280ea40c06964258800300c980449500e1200c180105280114041d000d07020b10310395503000314203420318180c1641c440c03030704030b1500d00d095503104231440218500040c160341025002c414a4800e50583d060180c8030070500040b100c00580706912809007200421025070780100620806000c1c0380250b2034503600780c82e0245040001e034004100e2104140e001c0000c181d012015150501040700904405141c0310b000810319100f640b10b1011079659100800300e01405400040071000082e5181850b4980c1c81c10416180d40 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 100168750 1250 100167500 100167517
    0x13030203010b1203220e0a02040f0e07141c1d0706020f0c0f010c05010204030b07030e01020a0914060903070b03010510050309060c030c0d0e0706020c040209030a1407050a0308 77
    0x6082602d01e000610b880c441010703035000d82100031810002408441001081c900308180c0e420a05200c3c04100d2171004080244900c0d1212400b580d43d0f03182c01030503016203115901c10140301000900380004194803a10f0078000c4180c0b141219180c6c02407807495000416038a0203084000c1c40c0103000070040302504101c40d03a580075007042d50103c95503448244e80300c0c00b10b1400b41c40140c2140100d12414035010580d60241ca1040c50440c41b01501541c60320f00b2a0720680007079030803c044504000d402075143c0100d41c140024130380290f00b06440721307e0180002c0100c3c0101c080409003070603261181d8440074280c50440c2e10090807120800c0c0d0343e03414502280d000b03015150040400300b01e140303981402582220302410248005010130b07a144034209205d60000b804a40d14a4002c1040d0180705505000b8142d5000020014100c1d00f07241404c040e240500110485000e140148024601a90041800141c9a801140b04800c0345108803040d418045643c21060340060316400100900001402800110 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 100170000 1250 100168750 100168753
    0x607020106080708161205031207050304020306070e0d11011b0606090f020c06040f050307020901170f06070905040b041d0d18050d020d0501090b01061814060403120c0813030203 78
    0x181c540494075205e650000c0d400e032803e459100f0402c08070070000900b5500c2c501641c10347c2c0c28600da828002c1c02401007a1001d000040f0040b06000070b61034107021268015069040400c000b410b4080890003141030b03580050301c180c0d072220800300564003440385040022042004130f0000f80c0185400d5000304158003916545034601140c1c00c1010307601d41308881110281c4002010701d65201d5807008000c03083e95004070746502050140c440103868041400d80031b400c030f40010541c0300c0b601041c1140780071210f01c480c8089038408401c2c1704807560084030038025118159008a420300288000c140a444400100c000d031041c0c41500c4420710070080350303400090340a50b903480100d0042485c00030036081680541c55004a4150942006251807455034441904c90303070010030300c014682c642c081e03407040c2603010602081040381051252200c1860000203814407041400044205101080407800b542c04020040040d48158a0009000d5a22040d40d43d0f4059401e036a104008000c100d003203c0c6a1100701d009 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 100171250 1250 100170000 100170013
    0x801020a11030a0203070b1504020708030106020c1f030b01051603020607080108010b0906040c1b0606150c0b0105090402130c020106051002010e0d20030c030304030906090f090f020c060702010608 86
    0x5108000c8110b030300f54542a402541080d8054032429905940a028140c81082c56090b4402d00d417514006049194010409941c5940c94000301906200400c410a441038030507060321002e95a00c208103a14072603151500050b051410001079955108203000d00c0e84003c00b100e024800c260740066101c4c851043c035a1101c250341da0f940c2400b4240c50301112110f0303205040310000303842c03030409a11084040c649454004902e01c03081d00e10061034141c0000c20303141d02e030b1190341c180440d0000072240c0c48030305a02d240000c0c041089031101003500c00d040c09139a2103186c03000b000c5010f6654036010000c5940b02074404010407615120040d000740340a01c243c50050550041100751a40188525104c8000240180400c0c120000c0101c034100d000b09440103280621109900c0101d0301000580302c4000c1c00d600940d580d0030541805070054409510003010040740e407000b0b01c41c01000b507980e441140c24401010414480700310750b203c040d004070b032101d400782c3c442e0000b001643c55054000307004480c410400e40d0751 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 100172500 1250 100171250 100171277
    0x2070510020d030b04020423040b12030301170a1505090c0d051f0e0706030209120307031d03151e100609060c0c091404050d0804030e0103180c0801020a 67
    0x10652400c8a0003582000800329040c602035044901c03a10b500400061420b500c900c0034100e0281594218801207003407026a0000341000d102c1c000380340e807007101e00e0180a2801e1501541da444140a01980001e28024400341140c04001c42c60b205030340714101402c0560051410001040111080070080c0f25a40202c00941030959005c005190064058201c180640c0400c1c80d020b031098088800b10342d520100305805400034080c5402a089135603000d80d560101504000c01e00c0f0b03108002c0b0b9070319002000600300080d0400303200701040c402c1d510941306411081d00000e0410154401c1d2860400f0f00344100000d000c9245a003c0407403d40c0c0c5000301d91501c0309500d40a1f0071140d4001c11000c540141c1c0144441130007004446030051081c0c480d10b10040c0c9a665017015940d0300c4031000941000075060104010f400e12603042208480e14061100e850710b92401025a000c84608506066464851244040042c9580d43e00c40d038200043c00e1941d82e6444a181c000d6000314950000924240bda04c0d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 100173750 1250 100172500 100172509
    0x109080301180c0f0c0b130204050a061e06210e030403081c0504050d051308190210021603080c0f0106150f0903020a06030507051903020406030605091003120201060803030406060303020705 83
    0x5814402c41d51490b05d00c21069a941565a50141a0364070704146a406600140d03960b0091a02c0780600440101303125103041c0c2e00755180d81d8240d50301804218500f50a0003c243e00c07034059100000710000c0c11280144840030301c8014080360154a400d400002004002e2100b200c0081118103d6800c42564601082d1141e40072540107680041036604100c0748401030511403405000d51801c0e01505900090351548954505252075103c95094542d661040c0c0030342ca444d191816800e0300c42e00190285080314040ca04901c00315000040c03d403000854110107101c41040342400d021002d0b4020808107440365054500b1060004c030500010b030b4078032110350b0540e1044801c10101c0c0d44c05800c1c8940c090400e003081e000f501000300b05c00100704007441483c0560040d00d1104026180c0d94800503603490400750000c060b2592500301e28054a03600f0144030301c08288d001403a0803660031450134000800304038400c07409070205511a11782440040288011300c4020341c007020440e407280d02210302c0c0e03694940901 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 100175000 1250 100173750 100173767
    0xb0c070f0b0601090501261f031202060705030c0a1b0602070302012403020d02130e0a0f2001120b060c0a0c0f05040615030c0c0c030312050718050d050109080301180c 73
    0x40301040c01084007c55210400300702541150040e4000d50b0051000d04403d0a59107803980700740c1d105195030750844d50041c2c061161640144242c58060310b1451f02040703070619446803511507030410050840a0030342c0402d11854044095125500f550380d00c0090a00034041c04030044542d40004401c03030419040703d000540c8204980e40545200e2200b0007540801244180301c00e907285990740c4614400090a40a000700d04115200d5003104a551807d8241460110004e000240161020748203031000381e80c2080c4214482c000b00000421031000d8040814128040e040510b00c441c400d0383c0f502d908101c007070085203056031900041c17446029600c2d0100403e50313141d4400d18070241e480c1d1580d1100c1d10b01c00c0c0c000c00d03091202810b000180d0825980c07a281008034962050303000401c01c40100003101e1141c041c00f5000a40c61800124903803580324217500b02800f502c217403403241110688100810100390041828036401041c0326450b580e6404400412190031038040b41014602020039205a00407442e0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 100176250 1250 100175000 100175027
    0x5011e030b0a09050d20070608040b0403031b0c03110606060a051305060301030803041506050102030d09030311070303020c0f030a080f0a0b09040309050103110304020603040b0c070f0b0601090501 86
    0x1556965891a01c4841e0005409040d0801860321058820041442003240780d0503008181e0b04d4864041b410302d10410084446039142401c0d130030004082000c1c551041c842d036001074000900c5400d58445180c00d1700242401c00c000d02c0314049880d44110700320b4000b2001710743c5c18000d45884040300c4030b01e509107440300402c4402e00d601c034030705100d0305a05521410140944030008010050030320380742d4000408030f40090b03004840d604c000004000030803529205100c1c40d00d42c611014083c803810000043d44038041c4600848a4035a90101c00092501c02c0e0816402c03001c403011110380d100e8107410700501a50290080d60f0852150070b41c81030011030000300710780c0c02140c0c5961320710702a01d03005450028800d01402000441c1d80300c2040b6130060380c9a03903415001d03e100351100e5813407524007000507080d40c40e241140302d04000300f0b004100c09a12040c0403254855400100081e4660395007141c142c0038081c6640151a140302c2039a81e03010003090750401800394400341c89410340f6598030ba0044038461006c220 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 100177500 1250 100176250 100176299
    0x50c030126030301080a020a080a05070306020a18080c01110303010b0313030c1a01090c021218040e10021e09011d03120c01060e010504020703081503031207050903010501 75
    0x4100c0440d54140c070700c42540794030719a42229068980100d00d1a0005c2e08038500c903400021803d002c520701400040c1c0141070030b03005012a0a180d0700c400761121124440a4182a000902c41d6003070351150b40301005d50284050a1526162200f600a641d0743c0140c1d03165000c20207242030341d9101c240000a0b60304943c110708649146941e09405010080781c4440300328148035804820000013a00240c40303907215003000c010505258586030444050700c4404509030159000748540060040d07003074088030810032088956418001114000c01d0081c820b01c08000c1a5020f84c040b600312820442c0c00901160801c04500610f2821400c1100218803032440150b012440c44c20001c0145410300d04e591942400013000e03200c284034032400c140455801004802500d9668510503c960740700043c0640c003401742681c045040c0022641c01501c442405041e401c0103081940020116070b60420072074104484c1031500f030b1003500b480207019249802082c817140c429424800042030366403514082c0d40d013541100c0c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 100178750 1250 100177500 100177507
    0x1a0411090d030507020604030c0e070e010503091e030d0608030711040c0f1d060a02030406030f090201141b0d0e0f01080402130c0309050f0a1a010e06040b010507020d0302060709060201050c 83
    0x50b4262210b6120600480c0c120b0024071001004c5044100d1450080542e100c908100703140000008280300c250004403810300c54248107102c1e4000d00050713204044403444070700c0f200202c5040c40c010300e1801442401c56045042c02408140210040050440d55104524604004155004000640d2010030007407000402c0c0c42c3c14041d40314805d00003050a52018044c000c10b00000b0b102040c11a48060460805680f001500f0005c0e43d038144581035205282c2e050130003060242d41e0000703241d0103500042c60340c1403a010420300f17013102c1d0282d160a407942d06a401c40e1402c0103441805004120740c149540e208510401d5030440c15400756001900c1181d00034040d40442c107510a2840050001100350b00406944514080004504000480c45029904000c1c5001c621510300001c2154190f01c17190a070807018001041001c056190494000e031003101c0108844d6034a500491f0079001d2500c01941c40182659540306041d00441c080c1e0050103542d0b00c800300c2e60b807107078016404d80354147d50100b107044003003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 100179856 1106 100178750 100178753
    0x1080d09080a120207080115090506030c0102300c1c0f1b020d0b0a0617030c15040c0807151b2f041a0411090d 49
    0x246003280d6800c0c140880d50b42c44030340060303008000d00980d60039515414028004030004d0880580200701c28280c041d549440c2560380d11440c2002ca141c031012038210f040100340c01d4200c0c08181c0003040c0c0c5900000f51043e044030140303002800940d03072040c2e61442611020051081050010007040340d0321000d5402c00e9401800306904042c0403507450605821604400c1c100009515941501080ac0782030004c5041011211001070100e80d9040410102d070310b103079000d071003030b0f1b01384103075035100b1030000c2a80e10ba81e0301c81c22104a00c40d5212a80b80711184150307114030790f4040d10418945200540e1807003000e18101c85604001c1d141c0c400290840d015552289102c124400007040706c040704051070b02c4801e0014442c69150841400c14003081c1c01040301204260200c0d007010780108500d284035008191140b0b403203460144075904284600d0544180f40d4103aa108000003070000300b000701b15 = true := by decide +kernel

theorem cover : BRFrame.Cov 100000000 100179856 := by
  have h0 := BRFrame.cov_init 100000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 100000000 ≤ n) (h2 : n < 100179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
