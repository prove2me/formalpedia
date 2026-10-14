-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0186
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:19:41.998371+00:00
-- url     : https://prove2.me/submissions/3c71e0bd-fce1-4f55-bfcd-8a7f43a2171e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 33273386 ≤ n < 33453242 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 33274636 1250 33273386 33273391
    0x2060105090405030c0d030c0f03020301140d0c0b0c0318040e060c0c011514090a0b060403140c040903090e070c0309060809070503030415030501050d0507030201050a02010e011b26 79
    0x2401c07004000c5820000140f0568120a000d81c00b1036600301ca12141c000c01400c0c0c1e6000d0440840c01c040481d5020a119000700d03410b0303a41034403003d0b080742150414803038440d4047c801541c9502010703901203001c4448800078a00e00c401c0b00001c5485051760400c130b010a5040311907440c4180d05d000c00c01c450481c004030320705030f1060f540304603e0b0719484107144941c050511020008051807400d000400c80464042851100181c143c910388019a100040042220030071101140c0c07290080c07008000203094210070041c005d8516058a0401054101003410343d803074800c080b004180b440d0001d00c02600c65800d441e40c0054145440c450840c0c81e503d01134441d2503d0b0162400300030030003001404012041020100074500038040f27a0341c8555803960031151180d46804000004e0625000040b14580401d0000d4100e4020028107051840c3d40d00540303440e0b1018204405654076140300b0902103101b807040c1c15040000c07101c000f03007900503124010103c1071010343d86d26a90b0304c50084803495442031a196036 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 33275886 1250 33274636 33274639
    0x60402090403020703050a080a020d1106011401020703060903031407030203041505041e0821090709020a1403010b040f050102240601170421050f090402130914070e0d0302060105 78
    0xc1038a079424100c3c203101131608003401c0381c0324000d000c0d03041150130b20042c1a098550350a841c0c03407541e03814013140c56044983d075140e566803101c0d005000c0100e25074901d113201d41050048507103c0b039a80c1d0f901da060f19080c040560100f030740e44840402c049034041d440340c1c1c840c4241c6021451860141d075581503130950449600022951400018208580b1501500401c86034422510a2661a2520400726440708840c1700907140020040041002e0544400c1e000d0040c91300981002802c0201d00c4009400c2800503404104206004800c0305824000841c064a0b43d460f1595607581008294a040d40c09a40418110341c04280301c4400700e40c4100152a0f00b4031858918900c5031207100c0104c0703100034403207044082c203c0000180010007000c0300c221161015000c04c0a042400c03514001e40381030081848402c101002002803000b2464180e004003c540b010042d140c1401e61526511411035142c0583e080004500030103110303410781c22002207000d03194111030380e011088031070744c000351a550103110f0207 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 33277136 1250 33275886 33275899
    0x60304030912110607140c04060308041701020417070509100b07060902030f0f0a17040302031005060a0b0a110106090e03250b1303080109150e0403020f010e030d0b0d0203060402 78
    0x20410004111074415440348020b050617112920360418034801071840781905400d02c50300f40030142500301406510100c0303400c0b003c52401d0519226401d83d44d51900c8000c24840d550810002c81e4180041840000d0000e02000900d405410081401026100941100180b4258140030003a040c41c100c01c035031600798002300c04a10a00e1510200340760001406d044800e41c01404025070509030000b8500d610300d8011841149144146520300d8114461400003940640286175000c98445154111580255000d82501e010700d56030001000e007600280303e4100061076524140010060901402c0d01a0032031080c100040d2a01c2c020351030340c0348240e44011451104243d4610039175400b41c010340c2203481d04101c58000e0b610300b204691200114000c003c4021503107520010401120078441c01614581c41a25082820b003010200340741d4940040007202184603a510328072403110280a60a485003c0c50000e54807a0250503a08050310720312034031240684000b44043e40940d034002170880e007007501075595 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 33278386 1250 33277136 33277169
    0xf0203160c060902030d051c06050d39030506070206090304090b0d02090c04030b090d0c060e0a0210080106120e0a030c0314031003020909010504031706040f060b0a0e0603040309 78
    0x2c0c030060301240c403001e0b42c14007888810080f5070750040000c1460007181d50302c03c0743d0000300c600940300b2034056000301608100c0c0420300d140040d0310760f11010321203040340c80c0a9410011903040580080015220360040109504080081040402205401c14081c0c0080c14007880c106803180d95900503031095401140d110400b000c0107072100700c092031219070040d10403001d600d8040d800d411264081d21007203842d0014039001aa07402004908094114019070350070703098005039207505014080300e0a42c1030050180001c100016652544103000059140d2907075102c41d85803110103044480c440d00640141414036054041a85021803080b00d401e5050816069840d0b042c00d00725110b21002c610103100110000c244640400026040800c0300d108a0b039008250b81c07a640c2e0369003600c0e02a02c0080110f0040000c88450883c1200c6256210101030400200044a001640299004c50b441408aa400000e03040c400c158400c0751840503250a0300d0803413440c1841d0340c00422042d5103204e46407103074104181 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 33279636 1250 33278386 33278393
    0x10302030a110d090b06010906050403080a05040b07050601050a12030503041209050a14090c120f040201050d0f0e070602070e01090203040c030c080c0405090705030c0103020f0c0604150f0203160c 86
    0x100a14000200181d2500c030fa1256129030000e100000007550820b21080005640350b10480104003521540d650b9141040e20350790314021140c01c0404a03038180035080c0f102007482551640601440b502400042c005035142074103101c00d007540e82c0c0121a00d0149000c481010a8101c0100ca403c1580300c01140c0162182ca002251080416080154820f084400019428003018042400101c0c2202d8080f400d46402e2407410f200e20444140b8800d00c0781c0d10780002c400311898080c0b5603000f40181416440c000901c81e0260413155040030648040b41d80350351a43c9101c3c0c0402c144000740a181c00200242402d00ca52060700c4241407180500f5076400100141c100500c182240d401194800030341818a62038811507a1031386000e804040c0030b146054001074100100082440450700064090141190020b0044019500c044124505d204007080340560400e0308200d002e100c0c030f005807c900341d010018030380304080d51607104e49904c0441c01802401902c42960320100510b035650300b46804000164507 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 33280886 1250 33279636 33279641
    0x3030603030a080a1112010303080708130809030a020619030e0a0206090d1106040b1903060e1f030b0901050708130203070501050705011b050d0605030102130e09120c03090112140402010302030a 85
    0x178941519a1011492002104d000010039060700c6c400d44031180300307581d8110219050f08044030f181c400004138445010101d4100300081a0303610019044e0303800740000343c020964961004201c0c0802e41244403e1040c0e8650501c60b05204440c084c025025200131074002a0050144c030034454418903040700ca54080028503c5049582d0760080c0c4465200c036a6103003d810182c0100800425110b60a03100c0d1809511a120380710070345a102440f6200c036102ca00344003025811019400007032000c0303d0004000b26203640305061156402000204003864031240041060030040e0803180760552407800b0000503600031610340d05840f420310b44540c03590ac2d241449405032002044590000e400714020021036580311000301408ed801c0c00b024071000d40d07107030140740c00c074860b01c644c1507100a1801e100f0b1003e83e94008902e60407401d80c0c000c5440b080740300305042e095a408990603041947c40010b520126580100003400c051031007401c10407040c4107003a01180c11a038020300007810558000000f400142e03455 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 33282136 1250 33280886 33280901
    0x10b030f18010906060302100c020d031409060408010203070905010927110d0b01080618011205070b030109060501090905130b060303040f06120f1b0e15030408190203030603030a080a 80
    0x1200280f0a43c0080d09080c8001c1c0f00314082031740100c45921818418501482d50507a9566020748604803885003900d00310760b00e20300c640442d40070342000c110959159413590080c0015259490005a0307a091011014102030515441941440a2540e00700910a00d0524403e1508601102031048428598100b4020218400c0c111070819000c142080404240e9120405404007070321103182c1c503119a42000120700400248508030b40c401001405015083d80960356987c0c403c1040b04c0e01e540c8c45401503c4950408d80005161550344c6030108010b6038071941903c01041140380030005070402c0031142294048400010708010042c1e000305191b91410000c8800403d50200030410403034594000078113000c034100c42e2614075414051107105c0c03240b151042c5441440701c0c110a16555200810903074200810b00e04042c0e00c14001c9084800701e000c000c004503c900d10944001d42c2d03c0074030000110014243e440c0b40303401c40d401481000615100003044610b070184600303000109545180625000d40f001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 33283386 1250 33282136 33282181
    0x309140406120305030709030605040f02011106360601060203280807031a040501090f110909060108090a061802040c020703020f0609040e070801090309060c120c03030212010b090a060503010b030f 86
    0x208030400083c00a6003301c8400c280c401d0383c540740d4200e1896452603a68000751000711141080c00305059020030032000c01c01498407c1800030b0f1034516030429007030500700c09a0000c1c026030000a068008005400a0404410f07030040500c100749942460007001520020880c000345035460b41e103161000910100000024401803043c0125a16441c415002d00384030440038440718100000042c0500542c800e0300c48480c00548600050780e6168011612444081c0c0008018010801181d01084050062000e890680f80420071210814414082203600c113540d52011500829014001030780c0384418014281411540d1503100d0500f00d000070300401148094850912429000007110003040d000b011086000791502d07900c4956031101a5035100c3d107800014040401028642105401041d42c7c0c510305002c2d00d001402e0200000070041003440a802031501c68002042e60921450700300507440140660b80380c040e085500d0000041141e02003c2c018090100d2460300240038180e6844003080102d24 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 33284636 1250 33283386 33283391
    0x3050f031503100e120301030206092101060e0601110625030f0203040b01140a06090306050703020c190b0703020a0801050d080702181b03010302010e01270303091404061203050307090306 82
    0xd44007184001444054080340085c0920020881000008003e8a048a0b000f610251801b401d1008200c941000322802081d1502c0d00c80c040b00300c41c8801d104a1029240ba40340c0d41030039050050001d011240035030b50072036075a40007000700880d02c483c851000c020b40c41d40402400b04081800300079005051507060710f2000c071f17202100300b0051140540e42c45040755661414140c2e0b00f8082d030203019094126020f51b41c041043d404040000400d07650100e40e00c44110b02d40142020702c6103018070306090742e10000300c4140307002c09895403d008010024a800040c20b00b0114078200400e9800350880364144115071040b00724000c018140074401d800c540041d80e000701191102800d032541d02d45200001c0d0381c0081004021004840c0a00120044030305907038050f1140c2066800704e0b0011200f400240701701d07000221403040c40c01b034080d80d141e0b04080a540b190b202d207803445080c02520410355143d51040d510403800c0c081c3c20003e400082602840003034142c50b001d5500d0380c6418060702c0d5542103170b100525162 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 33285886 1250 33284636 33284653
    0x3020c150306040609020c030a0503040f0c080a0614060f060904020705010606020303070e0a21051f0e06090109080a12020c03041d090105010b180301060b030a0506030f03030403050f031503 83
    0x300480118032601c07080302d040000a440b4a603910480c06040020704d4a17074070412040340400e0040c0055030b84644100f28140e80801142e941c1d42c400c14065014a4280d0301c03240d0540d0421070b8500503000701e240c0310100c4ca000c0d07140810015409403150224940605000204801c060300c685d011500ca441d00b10b002408480d0351a90020350729403084685900149118030480400e207000c124000172a2011550482901d91b00d41480b000d00801e0340c0d04407402c0c03003031441603d40c504021541e25030121840c50005140070382001000d08191000b0b14401580e450718551100050603101a2041c8000e1442d12407000006444844001e101c0d443c048001da100128000825599040030303881035400004040616072070701542103090b11001c1c0034011240c80d0a2007960f0440c1440114125000c0b4020004100503640d040c5d0b0180c198419642c4e003032050741351010004281020003442c6d1050440100651651406440c000d045000b840007400e4000703000404102040013002034030b80c2d1140018192748284 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 33287136 1250 33285886 33285919
    0x506090f04060f030b09030703170703090f05030301050a090902090705090102070e040507091109091506040513021902030301060e01080402010908031603080a0c0219020a0e0c040801060504020304050c0d03020c 92
    0xb4031488200c403174142c40d0002505044021050b1004641e0540343c10240d40b8054100c3c03c2000801040f2804243e80c6940c9c0001040c03902e1007600945000f0b90181d656541803c05000602e4040c0c0c110940c04c1d8180718580005071608914a640484507203407280c1c40d0669000100d0500459520201c0201c00c010207000501c0700115808045418138030b41004114001c94503000d40340554a005079111031101c00041841490840c92611914018803541c80c05844100144013200c4c007021410803540d01062510345e1140301c40b0349603159595400114115072406100414040b0400c4a40e0304121842000c20110f900403032503100070f40714140650780c55074002444800c00301c1c010709040e00040c00c001c0225042c50200d2007005656003042c2e02404403080503c0090350078240380c1c0e00883e00110406000135805054050082c024400e08240923a210315040c0303100d0940d906030f009103100314410000d00000603800078038440d65003c00c2d5644012030006040681c00c01c00c6040304c1c2e0341c11560101110303800c2c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 33288386 1250 33287136 33287159
    0x2070f060506011d0306190f0f0608010f0501050a0611070b0a0806010201060f120605090f010603050706110606130c0e1009050117072319030203040501050a050c040506090f0406 78
    0x2035403080e44c0d07104208404030f901d1111000c1c2c402c002038154201c103000c582d0003a10301c0040d4010280d02100400c4651000b2014001c036018017000684031651142c0511260600313014500c041080404140400d50408001031200942d6120b07200500c200c218407241c43c0501442440001d10007a50800d440d00d4529401500c00300c012100715006501e846000324580181002c3c2000740e45034851403040100d1903a5640c8010140941400101d00c00e4007140d90113100700f4010180034621a002178848075207081d5001d00716580d803040140c81500301d007080259503203c0c1d2192031130b042e40d20500800d04551b49a004d5030240040c0355201d40140300000540c80207908841e0810860f28282c0ea4000c44c0c0048607903102100d81e0955503800000c680e0010039000d4140003800012900c50480d00390700d4500c448401c0c14a411115a107440407a40100411091100c00e2048503441151541c040c429403a0442804020b84107900460b4030421002c80d00c0300c1c41c1c1c1c4038521180c0c100100940100b00c0e45840e800403035030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 33289636 1250 33288386 33288391
    0x110a080901030b04140601050705030c010c0c02030d090e040303180b1014030307050d0f021501060201050f0906190c031e050a0e03070506040f0f0209040318050604050105070f0602070f0605 83
    0xc80e0818040c0c4080c3c0c00c0521900f00380085c40c4c000301d10130341c070740100456903948030304000c0e140c3d4441071090504210003031103040d1910309103864420a442c1d00e84145410101e503030488206000c14024104034000640b024143c0c000da1610703000174000d135400d90300300380160303651000740c080c5100f1010481c14242004044050b6808030b03038100d80b0040030340209680c80c401c00307100a09541140514001980c015885641251442d0050700c800103503041c240c0002800176400000140e4484061144152981d0b80c0717980c000c540c2c54040d20380ca182180040001079480c035898a0754176541d03882c20662038460790003050100c4850405400f103540b4401c213070020300400d032071108070780d4901000c24441c000000b00b2034042c260710001518441e40c498072401800c0d8082401519008005120349005944480b0414461440b94668005135107417101320404074044e42e000140900c8040200b4002a030300101035620903584880c0f00b2540000b945004000307401262802440030912070080000c00055030009032 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 33290886 1250 33289636 33289639
    0x190306050f04031803020d06020706020f071b06030b01080f0a0e0d02010b030601060305040c170a02060a0c0b06060f0409020903010b04020a050409140c0a121116020901080102070c0510110a0809 85
    0xa000d03014981135a5618205172000035400f1803010088400500290050060381d4041d4000600b402100540803209500c0224211600015905182c00200c02c100c003960141c88545800c0003000c81031800a0300303640002d0540c00c10448401c00240880c1040e40108003540e060301d00740d50300c84100100190282004181c0703a4401c1c02500e0000c14403d204e40300340b0b4402c0381c1140303400e0340303203031501041164a0564080040c0b440c001d03001c1c3d10380540c8440000300000c1c11103076510000d641031820048000e01001e46001d01c07803281002804110070740d510aa509603203410710300603902c80c5401d0009005040391444142c03c58004140041c000b40c021000d001201e40704441400f41071486910340020361412284c01d600f0000034003052104500c1010750300c1488005540c0041c48800c0300b6110206600300280c020300d4580603240e41021070a0001a190040420400035420301c5040e948540200303015005540c01034550158015249100e80f4500b258150448140c0d000136102e420718200c10340c00290000d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 33292136 1250 33290886 33290897
    0x504060b0309060c07050a0803070804020405060103050603100c090305070308130909021003020d0f050f0612060f04030e011e020102120c07020a031101051b0a051207030806190306050f0403 83
    0x191400c41401101d126120110141400d07030b0362000c00403110340040e4803e03070b1948508220340700000c0c9400b0007140550040d4403100390b640342c188100419608001c1189040604003070501049487c009280e18203103511502c00702e089142d4090440380315403198005081c0380f00d150400420311440c0002400503401125118179015110307400310040c1c4840d5170009400150781040305020f2842a809007141c4010203202080081c4200c652405035201078030880151780c6200d061003400c0c58006a42c04138004a40c003c3e246502e855030040e0700c0040018000303030503c40c200c10070ba400380c0e10030601c0c0003510f004031420028440980c0c500a000303412850660150101e00e40114094400c6d1105594038140d0080090160034250780e940081e00e00ca003900941402010312031842c800d9045034400b00401900c10050120248906250349008441c10b180d90402000300b1079080400ea00004940e48884180c4503416800341c0708412031400001c0781d0003c2c0200d4540002e10080f44980342e505805240a81d651 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 33293386 1250 33292136 33292139
    0x9090c0503070e04200d0507080c0307031e050c03030703020303040501061a1e0f0c01050609070305091228030c08010509070906180503121b0111040306090606090c020304050406 78
    0x505a440c0c80303d018080450903c8800180051004e0401310440d20703204101c4a8403031596030104019000445044915404c0341609000002041240d100320604c102e0082c04402d1031500c070104214a2007140d2041c44800001a200b8000204010203608070040d040381c3d5200281c6c1002902d0390003d480441d0503500701400000c04882031a0404140e500308043c1070300c1d20350310030070280c0341c00251080018007400c14081107070140c4024024200d022a840c0001c80c091034500100a601a030042100050618003002e0108000d0000384605029800d90b044c0303540d4810503001854000c541d020f1302c0b0a44980e03840002c0181da80354100d40c1c2c4415442d200c07000e960741c841c81001a2080208d40c81c00029815000401000f071144220003c0c0b5944052450f508540760008242404035400c9460451400020580415501c01d00300543e1555500c2c001c1105c0207400411145030312561102420b900d03241c0c020394042c4041d41e4402801805851001c00001d4080300000c1d4590b00517210b503e00c183d140110 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 33294636 1250 33293386 33293389
    0xa1706060402190e030a0c080a0624031b09020301030c030201080a0c050d0b06040b040603021c090305030403030b0609030729120402060307020a0b01090204051509030703080903120409090c05 84
    0x1e9070000b020902d01001c10714181c010403134841409144255152141c10341c210302240b80d040e51a006010304c080640707402d112505050342a036284440815000500305141541c0c20b400b003043c1c80903a130b4005000c02c41088400038850304044650404d0400c1032001000104000000ea0090104c030b04c00e88401c1002c1d507951225000300c401c081440400306a08000c1100d0020169201d071460001c0200800d06040d00c94040c0300c036640060f00705e88082a800200c4284141400034942ca004491390f0080c03011007180c1c1e500409502010300024181078565641100d0b076a40c3c0c1c4161104594050101d402c00c40c1d85c1d10401e46d070000040340c0301c1004040131301082c556001c100e04a0303080b41685400325034981c0712582440b20036840207002104500605100c00c00290842101074005e03d0041d00260b2168180030070841c1c1c4040103110101d111a040281509580b03020804d80b044a400c1540c2545621122012900380300c0b41da0384080050200080c04941d05000d1380c0880001d9010300040b11441c2d84840 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 33295886 1250 33294636 33294641
    0x5041e0f091505041d030706020405010206010b0307210b0d0b190e0615060909151908100b0105090a0b04140906030601030f02061e030403170c0a030f09020a17060604 73
    0x20003101c80410b4a94051015041c941c120307507400c1100d00541d16030000308414075410341d0002c42d0111746540e00081c04105940c1c1c10054207015020341c03a003c52850070148005000d6084000c01007403402d051302e142d0281071000f039111207a8103101030711401107803c0c580792402940c1c43c21503111340c0304051006280800f0700d05100c4c5400b01e900180040055440e54a00c0e20b02d01183c14210b6640840c0030064640203480340c142e064000c15009200c0650320840f50104007808100d5148000b0701c10fa9513100b000000c0c4002807090111010800026414410000483d0301c2c0c410a0047c0ea04120764890006080078160f0040048415030345078400071644d40e40800c08800c0090383c0040d8984d000398018030108201030301141000784000d1501e8680500307203e00b14030a20305942c0c91051403c0c04401c1005042c2c008102194034001c034003841003945031085150030075001b007407000400c0503074400007201c0b5400b4075031181d2507454000700706446a03645e40001301c00c001c94400d0607607064050307540408e1181c00c00b070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 33297136 1250 33295886 33295901
    0x2802070b070201050c010902060403050609010609151e091a130b09010e0a06090912180602190501060b0d060528060e0d1a1608042105041e0f09 63
    0x103803400345081c655030011a10782e08283d03003901c00c5550302c2964000598400000304011071043c00139111502d8001c464a0031a03000303902071040c95081600a080f191601d900b900c0c20740b60641002140f01c010b18000d12400c04060301710220a0789850b0400e0600c09803010b805040e000704982d03100f080001d54507180700b6110103010054020440e02c00502c0a052f0743d4613107507402800c40c40c0000302c1c04d60310011642a0303404101c003503a141412401989441c1d0380680d0038006000d101091110280c038203100290f950440c1803a082180440d07101441c2007020031341002c0e00400070640c0359030b00d81c00e070301c08a44000d0001c0d04c10309202d2005827091240c2151000c1205c070b414040d01c02000001d0380342050036070303180e84041c0b490b07980b1440c622410800200100051590380c02c2c48202007202d45001d42a0485055102c10b0f080d00384241d900400001807400302808071864210709c00f80b440c500c80c0c0c51043d00c15000729008030181d46840c00c1044480452741e841141210441c1484003165035070b6845203421202d11 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 33298386 1250 33297136 33297149
    0x21603050c1b0904140a050a08131d04031b02041b021606050d09170d0606030609020405030c040c02010207050615030615090414121201030c0e07170a090206280207 72
    0x70f03000200415032146000c403040c0340311401e856501c101942c1e541d0406a40d003000b21040c400100702c40c012042040000e4016207942c3c600c00601c661000650f02d410180200002e04002c64a4080d84a168103000c401c120294050410300048106120075150450383c5144100140f00d03041d00c0001c10492661108202c0343c42e43ca407649000c0e0400303100c0000d03140c184415100513890280b000100704440009103500d0441c514001005e0f400c0c90002001e40380f075039104c501014014001880103690200790080030b880d088800003807078620b16105a0190141c40c00251150052600300306070f031100342010048600342101510000d0b80c41d070581a2856988201d5036420041103c0054001019400b28000701040b000460b07a4001c8540040c4215501500e06071b28030a41030780040081040c80e04180004d48042c440820f00c51420f048010b060b07221918135640300b208900c01286e504007056205c001036507000340c4855510b005444003100c03642903540100c602402228062442a0b20104e038000c00e61f0b03003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 33299636 1250 33298386 33298399
    0x70302030403121503080a0806010e0103060503030409020306120303040311060609070f0c0c080d030605010e04110703050d0204030b01030303050f0a050601270b03010f08060c070215070303021603050c1b 89
    0x5081c803003034004100e08400d1598038131141030302201041c9200c02504a92003943e842401618000000414030a840c00900d4145400c0c0303c070500403640c001c026241661150b003001606d9596400008182040b03500c6c40383c41502002042c80245a8400314143c10b2180c95403c070741403a240d150601c00800740490b050340001c1c0b014042c12901c1803160100c0c0012500900e580704000d07489032400b40c2031501184e003980200f6034980c8200907030350f040740040942c10300271103003005549072090035585140300d00100142040343c0000c2e180390081680d4199405140c005529182c2503031a442c014009103010381e00e46035403041d02800107000c12002e0082c0e9118510603520b144441d1002d04101103c0150f8100700c1e04010a4a20041100d1000601460003084180031700c0c0301d06032424500a040840107020502070325000c000300300c050b0b16140c03d401400028000724550b1000307141022002401400030020103a2104401c1d0814035074080082c0002850f89d1040c1ca4480440c8142d8003002c1c030008901a420a5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 33300886 1250 33299636 33299657
    0xe1005040c0c05340b03010b030910020c0307030905030a0f0210050c0f101b020d050703030e030a0c0b010b0408060604050402041103010b0301060801060302030402031e07091401080105070302030403 87
    0x20540c0040640c40d180d0308142d403400c6007958a85003400c140b11280340910080d000c10300b091030384050b402c140c81c12038003240b18070450400305082c419120500400f02d04070030006c041060003204000055400284900c115150034405804a46030382c8034020aa00081038600d01058614010500d01021903120341207514110f62503090052070341c0000b440c0401d00c007040c00f0f005003150052040d90055180b02c0302600f0380800d80b444039411200005d0b440520340948c091000c452540010b407040e1560001d042190700c2d42c4140c0390850160010001c074540c2c4d8000812aa10a940c128414000e803a1142c004441280c0c2c9070f005448290013140f00e00c1c2c0095110348046401401d03d5409940c2181c00500042003c0e6280c00c01c62100303070b00070b80c449054a00300200400c4100e600400040c0501401e2070309520f07604103600061b945064070305119440713210306000300e101c0240c1040090010002c0e8003050008045080c000000e501007482003036299400c14000594040c40307882100e01c21135060300c0300c1c1c2080 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 33302136 1250 33300886 33300889
    0x415030506040219091e0f0e19060b0901030c050a0c02040504050307050a050f010c02060c03010302041509050a0902040510060804080c01020706020f0c0c03060f0114060702060c03130e1005 83
    0x400c0c024200c0758001d03500300148400c44441c512100c0c03603100552034600c1e90a18040c0094200042d1004185450028843c203001c01c8400c0341e42242290611200309146032203411601c00d25044c035103c001c401c90719001c40080e2100440002d012207075400d80b01040b000024490036900e6206118001001038644100140140385c240c2c410754000d40a18222410001035940d100c0c17404104a0090310390b0b034070100c490800071200340987c1c2c041003207910261246040004404501d400117000c002d209a1b10344040c014015202d03880b40000b02070030403085c4030900f04404601c001340b90b203103022390080d81000f001540d4409001403a20843e800c641e911491079503079861354100307500021100c0c44a55001c1119001080312800680788421025007002da55805000d401450001c2d00500c66000c0d40100c010044040d140403421030468011242c0b20070a00c0c50100006d007a0b1290400007940040007090808d0f001c0300000c003803d03c11a2002e6104191138558142130701200085400b50300c4000099400c0c17216 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 33303386 1250 33302136 33302141
    0x30a0b070c05070503010e1e010908040303030c12051006021e0c040c140301090b09090c01021b040905070f0303030509160603150909060902010305131e02030c03060906010e0c041503 80
    0x202c2c0240103481c5810340743e5000a017504c69204040d610f95101c004c002182ca000500305140c034496a400801038418640c0d901d9800380502d11000e400c0c1139403508420a0703140500f44001240f0500b040c01c000d1380c070b014905140302c480503020300001446000c1011117804d00604c000408030007d4001881401e83c0b00c010000648010b28602e42002034240300d0401d010f00200195002c1c10340c0400104110001c0c40502c040c001004003e41c00d19801048045a140d80109030241041c010a030380101d841020030214010f00000caa0082c590300c40d240b00003543d6540c501c64001581d101e950113001c07944480303460b61342e0f0f0041035402c4228845c48240401c007290013540180c00010120345890000790f6200c0c0941d046405410055400d19201d1514104642e07041c4651640300c001241c80f40c200c40700c0c586401001c000c010303070301c0c1300000b140503030395411743d50704101c4240b2101c0014111801850902112a1240b00a22a0840c0007000c4004601c030702c125402031700d00383c030b20107079802d94404207410b412400b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 33304636 1250 33303386 33303407
    0xf0601030207120914010507030e010c06020910050c0d02010507140703031811040f051b030a060902030903040306150b0f0a090306060803090108150907080406020904060e01060806030a0b07 83
    0x62503420401800069110b64008440c0203403911307482d208920340302a007110819100e44040c100842042007400094001402d120410300c2171821680f07403180b91038003a009128290b0701c5903218041c01e41c106852503025004141090036801918000e07100d4107820b0f0300741c070303c180c4815000c52482c03000300070504003480180c50414024a004a07001c0707811505462010054003060750101320341527801c4060305144c0141d0400c103c8a003020841450f062008200e01855104003964a40c000400304481c2d00c0203030400e0300901074a45c0e08540d00c0c00e03c0030b0038682c0c070350040c8004ca5680d81410780f100b9003000218030f11070031101c0c05844185418104214010a83e03c24416101807282542010002c15080e11a110140000034011965644083c0001d0010300300180311000c000c4004118101645410414a8001851b81000740e4035407a186042806401150001a003061600b84006582941a40c650b03040fa0030740e859a0032a0f071a45401d254807246440806000540140e011a2040c0d2040d0024003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 33305886 1250 33304636 33304639
    0x20a0e011d071803080d0e06070210020c12030a05011802040506370f1101090f0809061215040b09040302060105091e0a020d0501080a030e010302090d0803040501050103110a0303080f06 81
    0x4102844034000d2243c1445410680d41543d011602440345002d81c85114085040c0c00002e0000d841e0601d0000d559401d031017604441190049100c2001101c00c00281080d041c1c0464029102e10700b018a082c01800c09100c0e58103a07490501c58081c1000440c8201c0b020b0b580013400c410b19140301140032681e0b003501407241c03001c50000f50b003103240030704850200044100d405540f42400801e007030384018503040b41d04d807000440d64507180444001420b0191440c543e1684401e03240c0c1c94034440700004080c1e01500100446041d200d030204043d5080c0060b032070100a60403982008481520401d00c0000c07070080b03c1c01800340c0d1180780180520b2501d1046e036640700e143c1e0b603400d41007003000d0090043d2504040e0396807084103401040301c4001c03280031b01030035001d490002e00a043d180d03482c0d18001e00301e917140401c0fa17050641c0021841003586411030081001d541240000d50f80c0e0906103400c5000308424070007501d01420f6000051103d00e021403808040b2501030b9202030060b103e900722a1295400948400d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 33307136 1250 33305886 33305897
    0x201051b01090b0a0605030f03030a0f24090c050a080609040602160503030a110f0d02031515070b0718090203060d0f030804050f010207030813020307090216020a0e011d07 75
    0x2140d014000340251042c0912500040002c0e041c07400d1004155116a04018800c1d0461041c0f41070240d03000080e0707980485419408152400685800e00003040300001c4042035900f000b00b00d07078000d952040d500c82110910b6000304540042c2e11804c0ba200d000f01084034000030070786070205005141003515150020701846006261601d50040d42110307048200d022211900701004006040119108141c8404100407001c0c1c0341c0200b1110000c3e19200d50102080e516501101007812088000c00c40c4006050140c00c0903c560040c0b408441c0c02d410031841107401c0d002610008090f98400c43c2c6610180300c101c140022040d0800208001a4000030312a0342c01c0b541c180054804144074103202124940a03844100301800d0070305055040074142c540010441c2c1c010085400060b500503100c56001300100d14820303074416540b0009050004540c0103070306150001c640d81084041003000c408929108495031580380d5034591124603610400d1107040c8c05515100b540d007071100750b07920400f603100e031462400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 33308386 1250 33307136 33307177
    0x10b0c100203070c0c0806070e1224010311010f0f0c02060d09081308011512030e0a060509030c030c0a0311120715030b0301140106051606050c0a090e01060c020105 72
    0x240c004980003110b2010000e0300c850703125001e100c508034800019003010800380566141480c0041e00699841003024080e5418181190720b0800a014551503081c881140b22240000b62801c281c0e8180700b070200355885518040d03100c41641c0650404560408980c8034603240341041e4a003616044600081640c01a40c00c11484801511a01c01c00c282148104001c54981d44c0c0b520b031a0f03500c00d140341c10402031603240007a00e4180146100c4080c04489220b0b0b040c0403000803500d001c0b901c607001d03080720680150803400d02050301504400500000075054084506001550f400c0540e240070040d8015080038054400344089031246120340030400020303100000b00c10030300071194942103155101c0380084240701c02c510303681640750140c0c0300ca5040482c005e104444250720700c0b0320301c0e51043c480d001c01c1c00000101c460624020401c00460ba82d0002c1040010b0f107000001a08240c0c40103420304001900403801280c02014601c1240c180d94280d610801e4014072907005483c65071145a41c0c0400301c01600710f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 33309636 1250 33308386 33308413
    0x303020c03120421050f0910030605060d0b01021c1706011803080901030501092304050f1614030115140303090d03030c0806040516081003020409030507030f05040b03010b0c 76
    0xd5443c01a4402c80003a4290401d225480302408004482082004020446003001d00304a0302903a0081004a07440d0180040050044c3d00510f00c0764489500403001084c084005a0545e00c603c00c0e03000c081e000d403407c1888640e0201c14881001c9491804074449440004030040040c0c9a145d220b081030410344000080340801032080d41040d4412521400c0000c0d4030545940e140c0959401411002000e0280d000c1461103903a40840e504100391000030407170002420321804002c53345413402c01405623414005105640901c01107107000780140c52207044d916a4540c1414802e903101509401699031030941030520b48400d2400010880381e15120501c2159000e83c0c1c3c0301c04800740c1e5480b0b501d00049030f4410303200c041c054110040c00c2d103100324900390800021415500074030181a4031490491040d0f900c91198000c100c1c0030307400183d0890715081c000010503400800420800f4041d4946c2840c02c2d0030038100320340600c164010740d4040c4c20180010007414210380044c1c84007000700815601141c80d10300 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 33310886 1250 33309636 33309667
    0x12051506030405160803030105060f030603010b04060b0a0806030d080106110a1a2401080114040908030903040303080a0203090a032105070201150603051311030f030403050a0b070305130303020c03 86
    0x2070b02a0780541008a80c440300c00110200383c0010002000a5800c0d58904000144079006140103114404000400141c0c5644c0a50100070701807001002004140d88070285483c064104030106804540604085519454005245002c40115680302c0513260308100040301c101007000e0050500340304440c0702d00c0028202c800c1036a4000e008041c540b405c5c0c5030142424204021440e1182c2041c2c030802140d0425036440b81c8001d045d80e00300d00c1e5409521640c0d1000c10001c10314203801900c1c558002c07043c08042407001c4001c00880c1e02a44d5001ca194441c4031201040744030940b0200000d5001e80b1120300007a0150074418002800031004000e45418a00c00000741c44003144c0580041c0d40d46da004020925030181e0f00e0340078140d585001c10071482c1898003892070741004180030342025071010306101c241c1d4080000c410030a000d40c00b500e40f41c541e2460195503c0d5402c450840b03403550481c0018210034420722501e03110315420039803200c0540c52600c042e002903101c1c5d6540d40d000c3c0010030043c7d01d2140d514 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 33312136 1250 33310886 33310891
    0x102101401031b0e0c1e0705070e0702030c0304030c0609050a23040f0903030605031e060c071403040306020901120903051207090f080604020307080c0904060b0a0f030312060503030a1205150603 85
    0x11070314550340311540408101c2208522100c6200400181f1038540422800036000040e50802c04100910f500e641d4400d9285010315100c1c0c10646c403000801104218509201c64100c4049444444400e901c0f5010003001750800d004605a00d00ba0300311420107042d540ca501045144041d0000072401c54840380c000c00c1d114052401d0703000c20f840300700400c07181c2002c10149403c10000110354241c034000d429402d03220b40340540740c000c002c2c00c045412005c1c0306001e0f05030440c55403c1c0b4102c9a41d00d03034a10b083c0000c1d4005047c00b601141c040c0c041d04003031540034002ca80003030342d05a40796490300c442da050345048204041e010301c04004107100046420075006188602901c0c01c0300040c07140b46041d00c1014030700b20280d005805d40ba040740f82500c00b1900c80c2004213801940c040d2010600640a1000c29912143c6038443d101d12448514000185a00200540d519115060b000c0c003609032150181903692203200241800560798003590070007804241d00068000400740300c3d2140d00f4000e01c0000714590030a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 33313386 1250 33312136 33312151
    0xc050a150206010501020d0f0e060904020327010207080403020904030306150e190510080901140f0103031b0209071b020301020c01021b070b03010302040903050c0106030503090102101401031b0e 85
    0x101845840c00340c04000e0725004240910081880c600d0940d00100982c0146180b02c0600c0412200720301da070341e5100c0c191280d10401600864a03441c00c0d4450350070003240300d00c0d10380e070080c0044606135a0705410f00841d900f154012000d286818999030a100c102c03000100144c041682d140008200a01040120302c04000075a0380c59a040b00d00383c2c20072800c250400004007014150a0b02001261030b01010704600d02005e080050040e81c403040820701504000f9400b00c9100c054108028603019804212410b8078081d030f442000000d807181402c00400c01008002e5488508a8000b681d1244214131b400d1415902241119000404e940840d0983e00404106100f07a50046180030042400010504010088000800b6075514120000341d0601c01030001070300443d1580c0350341046c035020790215490a0106070003001110380d00e007006603d0b500200400c0c1d0040c0220003581064004034010b8000b0440c9100120345103034a182e481c404200149402d001002407221000a44800000351081c400c400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 33314636 1250 33313386 33313409
    0x509010c23120a03061715070c060509060f0906040b0f0c040306050a1a0a0b030a09020609100c1202030906030a09050f06100504270219050307080102130512030d05040c050a 76
    0x40f4600035090726100c0e0012041043e21014003c0704410006404402e1145030105119507103548008564403812403001400c264108004d114042c90b000980900c544900712061615403190080240c03100030588010f8032101031900450554049014126040880650041e00c0c296a959403a002d4070022103898000e1030703640c1001c072081c1040036445c0220510440d22070361424108402c0106070301001d40009072155598450038115140d04044800302d5070000e0035104095840c00005009800444c8120b42401049074240c91440c000000c0c0d03011004000c056500b0766171421510b00041403c7d4005880500c505546255504c0003480b805000e148200d11400d6428100700c148800c1e40c0d154003c60014416000700602d884944000e4ad18070340e0b504031385000851403030300012a4888201d42000d80d140c014a030340010f0260301540103000e0072030071607001c426103581e840030450180a02e030120701842e003041101e50009912a442140d201c0d21542c40200c00d5501c80b404a41c1c055240c2d00500300800c07 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 33315886 1250 33314636 33314647
    0x6030b0a0b010903020904060906150305010b030d090602150a0204030803010b1305010e09010b0c0c04020f071e03020601150909020307030c081f0506070f05030d02030609070509010c2312 82
    0x51035402800650740003030800c3d0b10050310f59804035019110081010301441d603031301404030030000240c1004510441000d02d001c241612800d11034024080781484034440e2140100d03c64180e0b0160030f2400c12a5041c1e0060000448032108540c1e1210005144003e8141e080002100052000012318041c1002d980255191400c1030515031034550030b5004181885118440c0c10940c0d81c400c22098152108000419220b924402030035107082803030704407a5170040c00401e94460501414000d003c19078000e800b240841c1a44141410151070035000140c0140c00c08401440b28074100381e2864841042403502075602c0c0c0d07980c14030204030b070005e4520b0000a6110301f8a0703541030303610565194000c04100e00c10080214840f1042c00c001025114445c042d4101050358000e200f4511003c01040b5005401d0302c0da06c0034140b02a05c0258402c956142c461076010001c074030010310440a86042e514103840710000d1803050785407180180310342c402c0344107000594844821070700d02c24068000828500c10b42145c983c0c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 33317136 1250 33315886 33315901
    0x30d0903021603060603020a170303011404090218061e0609040c1b0c170f070302040b0604050301230f0405060a02090f030a1203270602030402030c06071419080a030509030d06030b 79
    0xf48e0716500c0107518002c80151200380c414084110390440b200c4691650103c9041070214020b0254008080c1d13012585c1842c04680a000b00c240d1403042d241107a10f5840e20a49203031826002141c804040c1d0000b4081c040c901890074180d0080c0c0b0002c04a0424039144400d403d125114034204e070070122116481c0c904104500c01c0008914150030100401070001202c11003592a030740d0700326200191040d91590300416441d1100001c4078080c20000e40248008074046c180301c0c00d2294003072008181e289525000980c0c1041c100d10b0540201d52250103040552209030503003001e904101001ca901605150720384401361780800c0120758080c455010b542c803440000c04040c1c212040500356001c1c4c148803407007000300700102000b158807a82d8081ca0050301c07520b89001183c030300700c0b03800101c50b01b203200000c1d284280100880d41c1081d202e17460003103030002c441210804140600340c0000804060b01841243d0100380250003041d4400820300c222070030142d81c408482d0a0300c035107034004e540700e1050500b0b10007607 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 33318386 1250 33317136 33317149
    0x6280303050a0315291b010e15040506010b0309070e01030f0c05090105010512091504150c02070608010902070f080a09061709031e0c010c050307030b040509030d090302160306060302 80
    0x80e484c494100c9041d549004150802030b261315015034816034081c1d101c0381c5a07850840c2650040345800c646007501140f801c010724028410811001c00d5441810303048801c0030010304103948074603800005081c50b17918044130142281c102429140c054002c8203030200d40001140708040c025030050101900540c142d04004041003890340046003d41d80100040c0300c82d981010890703542203501142c0300300300d80d941c81404d41400e0420701e00903481a045007c1c4010301440c0c40504883c9080c0040c100010451905c003603998003a10302c118030120b080e42004104059555010303010484c01a07142d00382c9070310b06540e11403455104802c143c0210b8001c900910442c3d030300403400004101c4c0d002c130410036820301d00140c0760380e8065071458030410901004c2c00c402440c880c3c000d4030311108004000340004855000c0c081c1054100b02d9000c00049c1c5440880c80207483c15004441c020040c00015510f01444a54124041c15002d04c0c190150f1013041c2c48110b5440b00509030600940c011280025400e0441c0304002d030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 33319636 1250 33318386 33318401
    0x3060714030426040e10030b01060e010203070b0403080105100201020406020a08180904080c010e01060b0d0c021207050a0308060103090201090302010815060f210c090103093801090905030306280303050a03 90
    0x4200410041c400242214008c90544809050240c0c400302c0040040b4a9072140f220000c042c8200e07101030008160700810090306a4078101c44c005041c08012400302e08078007452081d03d0042e4000025400445c8445005044d070136010741c0d101002d9450704000c039644860a0f00d0840d04800c000540b446401030a210380350707032119458002e01445280400c100031a02410340315440c0303035903034200d0031007403c2c02000f4014100c407400002c0740d150500d908040b603c81883d90310070b0b0301050071480082c1c2150f02c0380c4582d040056050b102d00d640316003140c004403203061000f450031481c3d0101410b6854107507140300c041c0c80d20020b044000d0b0f9446440308004a010b40101c2000604010f25101f031140c40c104903000d030f42e094803082c6000507104000b420032040040d40d40301d03000d185400d00503007103040341c0d01007082c0079034a181041c2c12903050340d94201c580101d82d050f903000381c4160028070100d0210700d0a80c10380b24420944080b0344e090301854408000001003190301c118003003500083e12403059905802100b0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 33320886 1250 33319636 33319651
    0xc020a060c02070f03080c0a02100e030c010908030a0807020309030313080d05070308010b0306060403080f03042307180b031e010b0d0b280e07050102070503060714030426040e 77
    0x20a2603c1d1603c9200420113502009050001c0465648070f2410204810840190010503c00201d042d030f51000e0304501044101d540039000340d000c411041c1d409450071800310340503900214540403008100320396841d800b51956046020030003440007181c0d01000a81844014002d100524034a1710818625001040d01c403030091080501245010a42103101141154000304001c1e40e00d94130b06002860380d100c0d07900028900e010109140414400c0800a0343c13080340324020180c0c88031310320720700e10750148451075203452a50320945040c05180481400300040d0140b503500820b0b001e0404000909004200160030f040c40454034000240035002d020f0110281c80c01e50b40130313251204648443d80c00d80750080810f51700c4440d6480c000c034200e00d84081e60f008000509010800d10000f01007030b03030315001d161084034018865204003290310f24012504600951958a940c51090001c00c940711194200401c251030515580c1112141c101c004002040300c21040c0360b505a4540c01c222090848100140041 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 33322136 1250 33320886 33320893
    0x20040609080d0801180b1e0f030a150902010e060301030308070f08060105090922050723100305040c0305060c04090e0c031002090f120a030206060108040c050d080705010c020a060c02 80
    0x10ba510303401c0084181594003800410f1154028115441c010b4803030b20b00d00c01d4202609200c02220320004161584200c06c00700c0320800307207a40d11010541d85042c41040540700c40e01c840500d16100c0c1d419070000308443e1041c10020b0707060308400001034454000742e00c141c02040c459070030040c8065010b40c1070030480202d8100159242003100c00200240255140c0d18003d2603840040303141090403894420382c080c2401c2901c40b86018914006403140c0091064520480b01040a505844100601c1480c52030000d0030074000c1c1c8800b07610171005030802500540d0060a00440400440e4090001c0f5110350320045010750342e1303032030304259030101da8020104441c10b40101c80000742948d408900c4990341d40340c0d500b0250310785010400081c41800c20f184081e034810a106050104400c0115026001c240a81c0036580c540d07a42400542d8600c5049400030142c031900c84051045140c1240e1010645001c0c80002e07040c100b15a13551130071174440741543c1d0f01607030020484408101150050200c40c0070300f0300c040d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 33323386 1250 33322136 33322153
    0x702090f1306090305040b0d060509010503071a070c0e040308010302010e01140a031a04020c010e1b10120207060204090e070f140d14011103040c090204030b16032004060908 76
    0x104110803034641d00800080d00c82c00e010040c94802c0c000c0d02c001d4200d90020a541340c2410b103480340101000e205803070088149c0c100001d81c1c0c0c54041021000c60f81d41c11401113078001d0740e1201d91b44640c058241112400880100415400039140340244030b141700c0d03110388100d54103500015140800c1c4049084c101300d5411030000c1c42d40900819100302c1901410085140c605a1005100480301c00003038a0b00140301154980c40e640054006002c045414020340b0f1705886000c6e1101d400079001001103420031010341210404030f2150088800e40c1255660043c1040b48954501059074488d5002c1c10030135807214000051820280722940040010a00d220446890101d00c0451000800105442849052910800c5c440c0500c05040c190803400c00800c06c00e00c40365004070ba20380040e601940d0384120808003050b180040c1c401c031029650485e00750b4003640d8034844011003444d100b042c0d500c10191242d060481411104661440b480107401c90b030b40e1100d0410500400c05a1a980845020b5020204 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 33324636 1250 33323386 33323401
    0xc05060a0218010305070c02060c0a0309050d050a03050309010207081305030d0e030d18030203030a090608070c020603040f03030905120301051002010b15030714040602030405040e03090102100b12060406020702090f 94
    0x7070b145480b850030708002c41c0d65680c0d4071017654680c400c50710281d00304000040c1d00800030780226891032440e100791503401000703881d0020310a8441049100410b1030f448046400c000c603000e04081c6910946000001d0301c0d0640b01d6540c0491600514024108401001c006004c03501e000c2c01201c864007032070314144241043c0b00700001d41c0c5058001b9110305105009480e0303ca070f07009030382110b40515005005c4a540c1c1481c084001c1150559114480001d14181e000c29401361161000c0d4408540042045081d900c40792154817151407580412001c0c10740d68050280058010301000b40d80d049691103054880d03143c18180180351082d640d0140c00c6900d0409035541594400016418480f000d0034021345945d150001a25840000144590114070102d000111642c0c000000c0c800c1c1c0b131054800b8490144107810141d41e03401008007050258000c00e505c8012050280d01800e0a07071401807030b000c0c40001142c40325050200655064881c1c58000980205600740180c03080d81000c43c1130948003030b9151903103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 33325886 1250 33324636 33324667
    0x1150902120402091503120912030f07200d0302010f05010603021303060504022101060f06090308031b1b070306060f06140901360602070503031c060e070c05060a02 72
    0x10002485013450101291000384514010a040d0b0000340440b601516001d03c103407102c0c1c01c21a2014032943c0030300030f80d203500d000100a50f105009049070550030301100c0d0f43d43c003021084209810034186100b100054030355645403074005030740703000e078000040e400c07050f000540c00d50384140c005c03200b0305004201c0c002002c520304542c1c404498000384001460b4856100141d8801e46003403684074488100da189031a43d207010b41c09003080f5850305c145591050b668440589103c045072002401c6240f0a01c001031800340b252895110b1a1140d014803403402080304c80c0c0b005501200c62007084240e00007002801003100c01d1050001801c2c1ea004620f0400d40340140082050144800c51001e4050215102100e80d0044800820a1241d1149600c9421300c1e0754841c400024109210302030804d800e040003881c640003080d1001501d0010b4095440c202c50703004400c0d03e00264500100280303a6964000030521101c4c1c0c0094003031a00c640e24421954128100203180c03410251048202e41c1c4104040c44410034804d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 33327136 1250 33325886 33325891
    0x60901050a090b03010b0d05030c011803050703080709031202070806090703080304030518031005090c010c120509060d060602010506131401030303050c190f020f0601030804050103091b06020115090212 88
    0x110070103c0d001d04100046809070213451042900f00110494041c00c00c00040007800c54054030300001c0202d4440d8500500d683c01101202401090041001c5008a8403521840781c0c07080003810314690103996a134401404640314070038800140c021050070302500206124542d00420320000038180e050454071001e90307612001e00000d0501000291403400001d00451240004400405580c40d0034000c1c442803000d1302c004c498011050040200c0c980081d0300030401301081c6a0460301000c0001c1d418a001d8440303034014030301190301c640240702201d20b10103180519006850240d0020581e418000184182d901c000d0b00088101030030f01c0d07441d641481070b2900090440360546030210f401d440c1c0640000c0684520660100d0182c421016012426000340c510450780303500d542155000f004041601d81c8512080c000140200410801040030350712070b030001d00210703010b0340c026174501030340040c110103600d00d0b90302640260351501d41d001c0000c25502e02c21001045001070651038203600d0030345423001d031000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 33328386 1250 33327136 33327149
    0x607030b19210c0603020310050103021201060e041409070602071a030a05070314040f030914011706030304081606170621030906040b09040501080c010203071421070b060901050a 78
    0x4486403002c06042040400c02d280e0014010b034492074480e42e0007400b07540104c801030031052090308001135651003031003107a11000d442e5184020a03420000212030200300007188130b5125031a0480d00419132103803000c06020341b081100515800d880c0c9400a030070300340e0b6544014083d0308000c2d40146084030300750442c0e5204100c020000388650714001d05a00070441c07007105070010f1900d40100010840c00602034a0040e019403288076410383d445645100d0788400c1490f2030b002610020f500c251106a91100341d4100c80001c0907681000e40701c0601070f24040720400e0651030000c1103842003020039002140048240c400204000181c40c00d540450f020f8544000305075280c40040c42025281c25061096601c4075070000c008aa0700c941e140800009604402c8549104074900380000403290b5001540c601031242c180c01541c107140d6242c684040250740041154030031b0080d103000c856100821001300c0711074000304040b60340703c0260f81011034902c40000c0c040e80c001c600003001808990350b4000300d9401c5801 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 33329636 1250 33328386 33328409
    0x40306050903040e01030605060406090b030c01080a020403140709050a18020607050703080309010e100507020c06160609060509010b010206040305041502070b0406020a03020d080411060702040e0f0607030b19 91
    0x456110140c0307036100b00d1340b004100c401c1000001c020420590011406000111001d21000e41c8550100302264804032105074190f00c5a9040441d650041751490b0f40480710714001405e050390b03900c40e030700e000038814011041034003c12014401c44100744182ea4206442000030851141c0f65500c07580461003c3d100039118100c0400d6940810408000c5a0061980000d4040d124100102003030f000c5c142c04128200940104c91000c8144900780c85a40e100d214142d009001506090040c080a0360003101488080d0b5a401112008100d4a01848264510a03080018075203000b6a61508544107090000d045410140500000c681d1100680b01500d455490714400104005c400341c3c40d200b480d034030418089801041c009812a004194001c80798060740a840c1c8100c0541400c032090503044030000c0c40010070b41107030700d4581481406400450b101900005600d200740e80c0e544d28101c06072103407820326031001c81000b24441c0d05005840d032072101500c12641d0704500d280c1118892185009407040007a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 33330886 1250 33329636 33329641
    0x2010305041b030507080f0a051b060c0105042409020109060f020703051e01060f060504030303113907030201120209030106030c08030403030801060f020c150d111209060c04030605 79
    0x182c411109050403911011680060703407450403030b0f10f50906100e03034401e5000d80998003481e0040450038000003039200010b040040c0040e003030f045072032401e8000c05030400410302100703000d00030074410180501c1c01a03100d080130007060041e907200700d01c0f0580c40000c0d0a04000705c03640180d270042d4003a01034688a00388503040f10613251049280c10b1136030340090154407642c0324022200c00d40311101480101014020300c4415199050884c0302c4040d4801d08002076010802080440e110398890301b002c9148140c2c55150680082c0740b01c0c40d085140c00c140303c00c103642c00b120403c03200f04111340b004460f02c108043c2801c1d034619000a0118034042c0c60041c00fa42d000034814070f150b42c0070350040c0c0c060b5522a205881d03094032110071651301c2e0080c5c0030403000716410a0000c0356440c0199408200c0b50451350003000e0805e242c4051240028806d0801c842d2100240980000141e1900504d40700301000c1318000d4a604845403147c05288021708042c0e00380e0003400900440314002011241503e803c0100401c40e034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 33332136 1250 33330886 33330893
    0x2040b040b0415090b04050403080106270b030702010e0601211104090302060a0c0c12050c010b0405150102010b18180c060d0c0206090609071401050904060b04050102070b030c070201030504 83
    0x2031918000701984903152802009003881ca00032400e0945000e81c00c10030190031000144001c0303c10584014011600007401001801c0c0700d4062542002c001c03008090200495050000c03852100d5000340395012004800c010355182e09200710004860840010111545011a040214006030b080c98001c20f4100140a081c08440032042d045940040d004003e40e50140c2070094030384c0c2c2c1c19100c0c051001d060006e80e4080510540c5507040d820342186011a0051582900303a42a0340544002c1655549501c0c030f80341265582d2045511071140400c81c04211701102000a084a00030030103a031160030200b01d1103501008180e0600d5021540545010820395517400311071502c2003240c1c206074003d80c0000c2c9500520f20a070800c81070543c06408507036031929800901604d0ba442203c4129450b4481c020801ca00c00c4041000740d00004181800c61800322200081029034106070030010b0380c883c000400b0001c550381040050300400682d809941181000c00c5610700c2840b400501078101500e410104090 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 33333386 1250 33332136 33332141
    0x30f0a15020c0f0706080105120106060203030c0705010f09030207150302030c03060d03110303040309050909030306100f1b060e0c03070f05040b18130c08030702060d092a08070504110702040b04 85
    0xb00f91030392049070f5110707942d804010b00294003409a01d025417074000394590450070502884013524529000746085655550403001c254000500560312592141d9002ca49a40d040c4541202d0900943c00780006d642045800e001c0e0412081c00e140401d4410400c00040d40c0d00401681d400000440d042641c3c041541030803941d44134403032490f01c9180000400e000c1010b42010003d4211442500c045400307988000d0f14070b4403030104a80480d040100d0b1180465201e215a014082031080342c18040c4917034030320360040c240001c041d0204860311591071900000340c10303041050b42240003085000f8604e182c2040c5591480704182d00c90f46015603141c0310200c0095a6602a0310001121000c0d007500342d180c40c0c0d03400900b11801d20000d0b9007010802c80c01044e58207000c0200d40d140c82d0003400c01d524001082c0c58560060082100a41d20f018162100c45500074134424071400c0001d1006d464040d540c14140258100300050707105a2046252030340c2d00030610044001d43c1c3d100b64048800040d0700140c1e0012501 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 33334636 1250 33333386 33333403
    0x30a060501020f0a1716170304050c040204031a10081f0605091006260408070311030405010e09040203030712050a0305060a06120b131521080f030a0b090a0b030f0a15020c 75
    0x200d8004007071a92502541f00155118a02400448140d4a1854180000ca01c120300020b403090541c0d10416030019811505560400c900c0c000d44040903640d080d81c5402d00304041400722400003800016038480070355010300c9001c0c050445000b049410551580340002c016403090764103100d10400340d0640310b5a90a41d00707007803074449081003200c0c1c070f840d10301000c80e0307400400200d001ca0600e0150700784d2214000182c40c1074684c1030315800d00b800d1608003001800040288200c1e4140320800c0000001402601d0007080c0c82c0c0305844080e03c42040090240035a00c1c000c05181c020480f1020820010394089a140e103a40e0520200250240c0c0b914045002e880303515290400c120308000314415800e96a4642c0d50440310000d03902418015840d4010082621440000c2e181d6081480180c0098101c0d070b004640100004000080e105c2c0c460b07000c642c44040c2220020020f0390b656440a41600f000d006e1040e22202d00c03001f0b01210703c56681c03454141c28101c0c0c0ca00030613a13808511080b086804000711170 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 33335886 1250 33334636 33334643
    0x313050703061109010f0906021b030c03010213051002010509120a020c0306010b0409060501091203030b0a030f08090a0506031014240c0c030312040609030302040b030a060501020f0a1716 82
    0x21900d418010b052455104c00200c6000403282031008400c42c0c480c50591043c6c0f40e00354040e00032050520041c060b2401503070f910b142e046c003400c0701b4100581e800340b00601403c1c1e00e842c1c08541d054600b50400114582c98102c28040d64141030400610650119080882c1141d0259558440075105c1049107425101c40c90640c05100e40800031030715540380d170007920417502101014420300c0c1d250b100440e03685020b0301c0341180100319030040d03500090081c0c10040f8140405001d03410401d6507601d17442d8075035220341e1040c0c54507a000241d40c242c60403c07840c1311020745020f0f18850700c2c5040088250008082c00c2c400c4009050b0880c2c030f00c0160b680c5543c00e0459007004c40f403407095641d810900c0800d050340810102c0b0014450021408400d080102c00d030f9049403001c80c0c07021707103540da2500e8000181014510450070941d08010104403102c1480183d4068040500c002036081e04101c00646000e20300705001c0030303a41c41800c120740020342c1c01e1414820005ca69002a449510281c8071120f060f00256004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 33337136 1250 33335886 33335891
    0x10c05030307143006030a0f02090a0e03040b18010306121103030f340201020303180c060a030c1404050a030206070f050304060c030f030c0e270a0f0f020906031305070306 75
    0x4d50a648221842800307016410000b24400d450301c80070035949440324280100744441c2c00900401510308100584da20802c2c8540210300c0c00040c000c1d0700d00315881500203141e130b010086010302004480b400581240d000a00b0100510b50510300d1014a040241500400d4124888d6901c2050740f414010780d80300390b28808071140c03100c0030051004807001e0716801c0204030300f0249410741d1022181145078000650180c0195185407038154103440081840031300e03201c10f407044030800405c1c1d803100d200034441000d950760001004899803500078084136003800c81520b4007400b400b051050395240d80d0003804607036045a42d140e94980504c0c0112190848a0014000d80404180028900d80100c0340b030300c3d06031290b0348848000200b540160221006e001192000072103d0304c0c45845410708280b42c81610f607000290030b81c61384a0458851012104407005920349840c1e60b80b1142581e403030b000e100c44039044180c05504148564011400a00009114008124041c5424010b010040c08201c2c051508002c05 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 33338386 1250 33337136 33337177
    0x604090c031e0b03060c16081b070b04030b060108040203120706140c0c070b0a080406090221010614150a03090819020705010e010809060c091201060e0105030c010c0503030714 77
    0x1580010041e1503800e41c02170083d01d0014a8101780f1204440e2036141040e280118499591204c540396004040408188500d130340f00d841c10707044100803400041425100d0b0a40c0e960a61410b5001c5c410301520322410b000008040c04010703a07011030303a0480e10b0100030005869051134104840581503805c20522101d1408003441007500340361f4020591f0310801c0e4101c070308096590000542034400e00060340002181040400c00240b03240d00040d0900340000d10703802030044041c080d003866030644510b001c604d07907640c44100900d9446076007c1c45829002c44e10300180d44a2001c850145100c7d401000c0105641e400c0340104110084d001e46002c041c15064000d4048600c050195650040c2e010b800c0c00700309818024107456120b01406442102c898000c1d1401da116524035901c1500188003555002c0c0d802121804000c80074800c484c000e0090707541c80c490070b5242c1014982440c1080200d01d0421071101c20328404a400002125040101840c01003850b01181a202c00c0c01d024100001425030584000c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 33339636 1250 33338386 33338441
    0x50904090501060501020706081b0f0d02031005120d1709030f040801050103020a090204180b010e040c17010506030c030112030314070302090a08010219030b0f040509070603050108010b0604090c03 86
    0x4140c82e02a000c0719409901c036901a20032715403c441a050387d001500d41820a007501e20080c01079001e14000160403c5592501c80b1309a070801c49440d4500c42c82d40504004525141c00c1c00503001c20034001809403800c0184000b42510390782000560084208401b069a803074040044588900204103500d071201e0301c0e444110f0207001e0038031007039100d0290031201043c1e00340e10344212070440b80d01032408440d2a600344114805002d040f031020381031000304000c04405407554000c0d0314000074690344d140c801c2c11040d40310300a4010180c1245008000c14002c000660400c04222410b607810121350002c055202d20f012006001214901803a5209102c103000e4400d4050300a40062101101d1010301103407103035000c034201c1c0110082101d0b07950820340c40d614054001e0780045e25124002e40300001403044a004581555800d1b51904a1a808900100320300ea40c103101f42405414408020321810840c0c1c00025110700440c0280d00d101c0e581c0d03014603080346009600003103194a25000c0a60001507551 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 33340886 1250 33339636 33339641
    0x20324010314030a0903020f03010b0405090a0b0a02070506040201080907090f1b0e150a030f0606020304080d030b0d0b0a091406060102010f05040f0b06150c0a02010e0906090a020a050904090501 85
    0x2100312000c000b1851100a216000f0040ea00030600d141d944c4030740c0c0ca00d1502003003244004015055010355031249000400d07201c5000b200d00c01c002d660024440d0790300c0381c0741441c40303810004d202c4251a4814024400001c2c00480c0d451b4000390246000400c40d240d5024041c100b0480e80d2004040c0d511301203002404c0c2c00603410901e000200034110824440610350305540003e4141c100581c400440d011061080c4d400344044d040c4506c40e4580050813107221141c1d0400c891b16a08108050303800800c1c10480741808000180c00003483c0d10b024000300c0030043c0800c04c007540e601b42c02048400098005120501c0740d41c405c156030754000c0341c0d07804014140d0b1541d50311407105442045c01542020340011080045009807030140f0340c4041064aa0480c0f034889000342c0304040c20b02a81300101440800b8542c1528000c3c0850480c0c05025212204591002400c1c003901c079000076004070310300c0b0100115980c44288842d8828021040942c0d0f5242e00c0303200312001e100d00e81445072f1003032400107164244841503 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 33342136 1250 33340886 33340889
    0xa080607170702060702070b030c0705030408010608060c0c070302010311070209070c0b070f020c04020d110a030c08010f03020f010e0f03070608010e09070e070f020109060204030303051009020c0a020d02032401 92
    0x405140e1940741c01c02c040361101c4d01162450b02503401320100b0071102a00c10029548444c000250900b01100350361954150f51040e03118940b07587d1620000c1c80610414171110750002012452a440c00d1218031445840b05c40360310001e07062598420071002640103200481c1d0041d64003c00d000460300d402100540700e40d0005606440041c205800220300b41d00030000c1703107250709084d001000c0d0421002d00700400396002004040c2d80759103402e815801d840302c141c0540648180c40d02e020940c044202c030020716441c016880405c680007421300c10409a280c0d140b03c195070700e45c00c2ca06191000c007048049843d50360b04034085901841220340c0000c0c416486010365051741d202c251002134684130503000569865542c0901c01c444807411012070b052a000311200000c5201c540000706450600b501e90000701c0c0c00c00c0d030060303012a88500400019410190311a005030003410011414025001c2881c0d40c0e031900803400074000d0b481921500d0035541c0410585e070004607181c4440d505140c80c80302c0c05024081c00e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 33343386 1250 33342136 33342167
    0xb0f07030501140d11130e07060e06070c15170702030903010e0c03060622050f06040e010908040b07060b030303092a0931140c04050c030609060a080607 67
    0x3400004203180d0140f550b20480a500205921080000c80e00d85118075a8424259680041803400c4c1200302c4025004884076036807040060f09440b4509100982ba00d1080c00c041807040404200c0ca90004262050600070740e04086040541d00c0410700082e00c0d54041c0000b0030090740d07061ba0401481c1e0b6400001040103803810350080c0481d0f100c058241c2e9503447c581c0c070400c1e41a0054400100c0300c2c01c1c290708a0320ba0101c0796002c5140c1130f14420312441241c0003a1441c022001550381001021f003054000c03c010801200001c1140481580300d80c00d0301c0c05a07004207050543e00240c0350f01840400d4100ca225250001c095a0741d0b030400c40700f025601e03a038850b034031055261912228801c4011000c00075909100241100f0550f950300c40c4403228140c5104ca00020003202485c081c180d85010200d0400420300c40d0544009944191050382c0c0341c0502d11412921880c10082001501484142034a80003407040c0c4212401d500ea441c000340900e0820780081503a4400c0000f0040e0080d40000b403403503034052 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 33344636 1250 33343386 33343391
    0x12070801051504050903030609070507060609060303080903030702100b0303220302010905120601050118030b07171f150203040b03040b100501050c0a0221030f1b0706020a0f02010201090b0f0703 85
    0xb800000e000503920116000300042d00180300080441c18040000d540c07202c40b5260852500046070b40742c3e0101c45060b082841116903449040c0b00300340d040740d603064002541100541c06d518040c04001d50394050071080a20302a00c46d00c81c0b80392600c0400544d00c1ca0071441070105014400300001d00e00001d0306101c20380c0060b20440c800547c1c2c4c04c20348000000c104075400604940c0e03007880c00543d251441c0500c0055901d41d04003001010441400b0114042c05043ea2040b041c054004490020000c1c007903c24040c03400302d4500300403c03543d04031101045542d01c000070741c5081c90048007a4118046c0e0b81c00b01012703510002c1007200308880a84100d01c101c005824400820b07441b9001140d1034043c0780c11000c56075010302c020202529100401900350180400395142010901d24000c1c1140c00110350381d8140e08000c98130100111000d0980b4414044071001802503924101000755541c040d680064901a06420070009592003900000c1d001500101240f4007801d0048500b40c1e9a88100c2d05000000d1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 33345886 1250 33344636 33344671
    0x91309140109260f030112021302040b0703080f060d141606020d09081b04020706060513020702010314040807020105070627060c0c03090b09010509030f0102040509090303010f0303030b1207080105 86
    0x107003d03c003650026a012114103040d0b03030030b20307402c20309500e107055051b0703440a04059202488074076400148054070011a03100d403603603410714011b00603901c064040d02c3c0c0055840100182c0d070301e8a0410805080e04646104080c8038083d41071828100c12003003400c0414507000300840d40d07503000101d141240f0b0141d61401c852954642c519502c7c1e19103410319110b140d4090012840c1890981c02400709680600301c0040c807180e0701c100086456240904041601ea00862004150341e05441842c006840c5072a420000c1d01d00f82e95416034a21850000a040c071102107804001e100383c40d07204050109141e82040b90b41c3c1c2c0e84a100710200b0100b840120740700c0c0e08000900140510a6480c0b101007a819210301c030400b424140f0100403500100302c101d04000c010300420015a030b0030010300620107050000141d5031800c0200344201c030f01008007074592aa004000401c0723901000f5215204480c1c040c50002039041e810000950500c1101400d4031031031250b01700102e034050040d030242d80038580d4071100f1300015 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 33347136 1250 33345886 33345953
    0x150a17010905011805070f051b06011e050909060f04030c0c0b1e0c070612020f0301120b0903070b06040b010c0f05100606020a03050904020702060702180403020d05091309140109 78
    0x581c400c071450000561084180d0441714023032005004402003101000411108c007a02c11071600400741e0107004002d544c2d90311662914910904039020b4030055a04d21074910f40080e040b0341e10309014100407030340e00f900c40003d41807510804210a040da400310060b44210780d2423501542681042e0f1600c0c00081c000400001c331a801901201c440316012006049032a19280d07044d40c0300d414441182c00f079180c0070810040901a9607000718041c00400040b52005149410895070074100109002c00c954020450303c0049102007850b203511017411613012915254000040f254500800300080051a4900000c0e041203000314a81340f400d420380300c003000070941e5000c04030381d40d2000c00d1001e4040b0780704000d021031604050b00109070710b03400604840c1c0f4041c0151701061500d00030600c096840e51620043c0410113038140a0100380e0a128070300907043c41039500000b0010008040d0b00b007d120380c1c0790544010806072501141d03101501000800907169207052601c0c1e9440d0300380c0c40ca4810410004102c090 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 33348386 1250 33347136 33347141
    0x605011d040317040303150618060503090703060b03100e0303040302100615080c0f040605040612140c0306031c02161e0618030804030305040905060906150a170109050118 75
    0xd9402d681d0f12610303240ca1030208050300e48050015400c058403400521554403450803564000c01030344e6a004c151080304854080901016007040e010402c0401c14803c1da17260000c1c1e08003e50303802000000b0390200100000346081c5803c2c104905d070506100a40c9180035011014500c5035000e6002d440100d0428000e49040340c840e405003501c0004000400c8145c80d05c24818240e1000d190040c003071130840d00b0142600c4507001a03009000007400000c09100e215407001c1c035140c031206c048006100d440c650340520324045034014048001c102000c0006112680c08002544c3c00c103d06640340c401300221100001d440e441000c68000d0907941c0d410740040c0041d120406003c50004c011518514681031683c1210070805000e1021400780300c2d55808400710707141600800003503110f41c5508bc0d645251a040744151032000304000c0c841c1c2c05000070403007d9200e1400030000c2901481030540d84007208002506c111019104c07004107400743c94008950b261407a441036068071800001d070404c0c0070300e06460105 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 33349636 1250 33348386 33348391
    0x10f1d010e0d1202041d061e0a0b0702060d060f09060f0803160302150108060106110307030e090702010f020720060c0a02150d09060f0c09030b0402062101030605011d 73
    0x702030380007011884055200320007041c500700540c20050b28060f51030150001c00300c1e8100d216a0000401010711403980752041e5a82c40c0c0407091541c1007840c50b041c00001c2c0d01c515041c41396076425040050f508046545950441e43d051386c022200700509134540c00c441e50b0444a90158480c420700e014400300d465081519190101c0b205c98000718540000030007044c140413403098003101075100c1c1c040c608204940301c48106010303080200040041e0340c54500002c044a44285584103250001c001c42c50110381d000340c10800300711007501e42d28a151180c440403070051608406e021801480454800100b06a104003620041007601d8108a001d1400040205030b11405c6001d456560101500320b0040c1840410303844030035460081c2908011528a00d1000e4540da00c0341181c0c0690746128600189030b26101d00030341003805107000c040d42419507568000d0444040e0000e0702c1040042520181c0d183d00c0d400380c039004501e40c4024180e659403480d03d031001d82428001c2c88507550301041d5400d05904510445031 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 33350886 1250 33349636 33349661
    0x60103050d0c081e0903100b010801060309020d0210020c06070503070203070b0f040909020d0f0b06030f070b0a050d090503070c06080606070f060b030a0605100e01150207060f05070203010f1d01 85
    0xd1905548403135042d840c95518111500c108028443c3d44075a680501001000c2541c02c0c4020035002400000180800d6050304107500340740c507011180c405038840314025183c00d0741c1603414407060000303031406a241100340303000960302c09000138154080ac507010024280140c402e408440980303481d1803001c3c041d40100d001c4485035a0042c0420080c3c40d6258005281650020700080d600d00c1d02e50316415668895403900352107001d00b6009104642c04c0400c4601d00c01800180030740b01440c1044601c403000d2151040c4d041c200300005c2024400c0300290303842a24200c1c0d03c10101d81da01c5c0040c3c64040304e032070700510800b008248a139002a001c1e0070188111100c40d580322800507441c200d940d540100814800030100e0301445045a030f0000190b0700e01c1040d002c0c000c0b00403c04030451a1460601120405030413000c010281c43c46e03aa285a60001036000039a00c860034032022032100440203c0311401803460103503056003041000c00d6a517107194000003081c0d0000c0400c0000c1d00d605401c1600340c60a804a58 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 33352136 1250 33350886 33350903
    0x307030207231012020f040e060a0605030c09191508010902070804090e0c1801090e01020712080405031306030203060103050601050c06010b1308070905010518010819080c0609060103050d0c 83
    0x2c103542d182030503504403070380002d041c00188a820380640208907003083c0448120741c18001410310400918400d01e0b0b074041812940c0c0610582030000042c402d0001420080c175094001c40c6840c401da8031001c0031030140c8002d8120140c0c1d25500e01014080141840001c0301040303407940041500480740c02203551003504a01d00e54606860212100c000b40601c1c6096040d5000d01140141590b0b03e0880702d00211803441201d00a650408030074008440700d4502c403c00d1688108014000600c0ba41600c00d24600705003031102c815965418000d00394403c100c001100781160100c0400d0039a055400b9600880c401e03030b020031081e95184015242031044c1c03024070b44907038003c034010001d03413201400502148508480b400d07651941e481800d450507034a60025460f45850f000180841d0900995002c00090b00040d440d007c0d515050950340c54070144030700740c0e0141003190601070a00ca010401c0f20440002c00c0e0403505640f07402c12404c0d8540707100713000840d4907001e0002130b45500c0e0305c86e990706090503070000d541 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 33353386 1250 33352136 33352199
    0x2060114010c080408061305010b030c0d060b01020a0206030403020105040309050d21020f01150302040c031503120c02062b051b090d021512010b031312030b040501080307030207 78
    0x155010b000310641103450003401c00c0042140b150620030107000310300041440c141c2060b40e1078654259420405001d0280d1300070482c40c0f4955881c00d5100502c5900308400262032000d400040b8100006858041e400910000c2400700301179056010320712841c080d40c0d03490803150715101000b60301c0000c100080d0850208900c60600b1405c0052903140c00b8006004664005000019036401c0d91201000342200f0060a00d0410a50509014080500c581c0d8030781001841310130021703039072009560b00010301031024041850301110700892484081030f80040c00191031f584045100b0000f002e0f1082c414860740010301c6000003004030743c00385900444c1404405101704c0c080a07104800c503003141890f0b641c030002c2540c85401507241e49421040c100d0b8941e5201e9500c0e4407282c4004030700d01040c0c1c40b0310311103403080041001c81d890340813001b078020340d110014030301960341703070a08a0282c49200d0b09941d0180c034200000420b0390340000140503082c426000c2d42c20307240c1d64101c07008101c0352000390140844100f911 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 33354636 1250 33353386 33353389
    0x80310060804022107080601090905070f03020105120403051e0c011406010e0d050c0a080d0206070c020f040504060b13020a110606030d0c03110f030304020a0b1606020d090b0f0708060102060114 85
    0x2c4002000001801c48000340e030f44401d81b03890003c081c0c1c016920640d5440504040c44400c0c40700a02800410304407850f208d103580e000816502ca1040102d401d48003c401040805205004980710400800154032400c0c00c0c200b6035503036690003d02c220405610f081c1d0344103141201d09059070300c150f00c16110010300c1000202400801400c04034220b4450142c0c40c1840d2040c4c3d107a10180c0c003d04240b0000344156141c24502a00c1d114001c0c0411301032010344120761005989028400002ca002aa80800ca07520b0394a08840a40400e04e14160701c004810115560901c481c1d0103007621480303aa813003001385650740450a4131101c00740c80c440e805421020711560150302a8030780300140c510a161111358640348400650138141d02c080c00c0000c80d08008248003e501d016540c10b0f0140c04c51080b040d00e444000300106440d01401e80f8000d102c40d401003666600c5074207a03400724403055002840404d140c54462038410410301d0440d030500c007140c0b04601240555100003042d5043c0d4442408105540c1200070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 33355886 1250 33354636 33354679
    0x6090506010c060e1011040501030e0303040f110d0203010f0b010801050f0f100c0f0b090c090115032a02060604050f070f1103090a120507060302090a1a040305030708031006080402 79
    0x1039118004d4401d4224180c040380705841284401e00c0140d64080e150f6060000040541c1c5001400c081154014418080803c0e40c0034544812a6409000180d0b10f8940398049040d100f00b40f60003079490351074821b1188072508250414800001c0c2641c440c042a0380368020405041c0c60045200d800031124403410816080c40a80302040c06058140042c40b810659a0800e5264842404591242c2080244884018100300c250301c2c0500880302109990b045c2103e207000c60300c500a01208040c0ca620480c0d22031101340c0c10710701d181c0032280490929100e0b002000f0303503a02400c1e110580224540700000d44240d030084c0809000d0701150b940d0700840d20101c1003c8520034001c840c4600680800c00c0041380540d00c1000c1000109588503a00c08421600d003096400c000d02079000d44103050040003104284c4e91005015401d0302d1145481c590180f680200e4003119020b1a000101240b10026540050040400140d44522242c0e025207184d2502c07074500b00c4040400380c41c02034105002c00d807290403444820 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 33357136 1250 33355886 33355901
    0x13080c030d02070f060501050904030c23010606030204081204030503040e0c09030115030308063003040f081c0e0d0305030a09150b01110606132706060906090506010c06 74
    0x2808803428072507881c0680d0100d03403051200f203e007040c010000b5010001345005080c010202120940d03032030303c0c0c20349019000c914003080c010100d11380907821800c4c180554441c02e07181c7c0314000080005a0b110740000d4020f50140c000c1640a220701040c840d80d44414804a40581c0e46c407401843c00d16203016805400e01102628460044a05110391101074a00740308000300d080c0c05248541c029440c50078040c1c9810740107401140100c0301d00002c1d0304005241c0000884042488041c2c00040c031845032054218043c41c1c01659500c51007100000c0c0e035200006a814214080709220390840d0380ac618207480c10103403a1001c603040080780c8046404a401040a076074130020101c0e000c00c00300140c2d60350140c10b008844030724081307541d507100740000c81d40c0c002c0c1e00380f420500310780c0202100d00b0000002000c8c0000300501b41c0d0007a403100c1c059020609100c03000c800c0703c0e0042401c05001043c40c90824081c0035140242d039240352502c000050030303142c0ea0113410700403501a1680701e21540151141405003100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 33358386 1250 33357136 33357157
    0x603070503030702210f150601080114090402010e0301020702091806010b0a08010e04080c0f0709060f0e040230030901180509060d11030328030504050303070507030903080a020d0201141308 83
    0x203086d00f07008549814005210342e01070842032204285020000546400c0341038010203040c200c802c00440180e250994010340207502400e2582d40d004001b030000340644900c07017009410071801c5060045800103030549600080048080d6a85680c03109415042d034010f88110400041d26000100651128140410741280c0500280b41c035201d410103465241202103032007246164003e40040041025520424010b8034500e000804100e00e800301000c400000130b00040c1c4900c2131a42d140f1110700981c401203c190091500142c40007111860722a100d8000c01031880c08148905907516060794007502c2031040e54030080416240b6103038035082c0807619401400171503d1200342c3d280740c07115035800c0010f4640a8000000407143d1410201d0b41e01ca4092000180400d06007000107201c0041c1c4080b040d00da00003000d18200e6160a0755042c2103600b20410390001d4020304e40091480580755010440d15051322290b0000d121100f201d008450304802e0880d203486065203446150000903031201e00070102e000c01c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 33359636 1250 33358386 33358393
    0x1090e040203071a0306130b0a1406040807030819020a02010c080726070204060503030a0c020105070501020d11090102010c0f020705060703270303110105010e0a0209032103060307050303070221 85
    0x1c4440301c007400c1d01c03100d04d0810046040441000300a00d4072508000c1d00043e42c04092203042c6220010a81c5041e1030b00550030540214850740d07030942c545105560080410000701c0d6110b039a00e05128580d0ba00405860120141c1c80c0c260200c0d1a0000030280303021a07040e9107144070404140c13103004058204480403160b081c0d0a6400148000c480a90542c00c00c454074181c3d41c3c2d070042d910402044814552109010b500140401070051b6046100034660680a00304283d50fa0180c2c60542c1c0240b0a0303070004920107243c0440303051004006409800c20040a800810403505402820b5840c00c0e000e40b01d41c001a800008203012506009024182041c402e081484910140ca0030000c890740c12885121140b080000c420001e0582c40550750980c405160001c00241d410701201100c0f0740c0004260344d900b150009585000c80d00d0030090310414560a401202100709007056140c581d501c1074035510700c2807140e03c802241500d4080102c03440030f94000c00d600d00380c211440c00403012402e0085074030422702 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 33360886 1250 33359636 33359639
    0x8040303140103110f0a1401050c0304031a0a0e0a0b0a020912060c070506100e070c0206040302030d03050114010212121003050604031101051006050d051b0c0c180601090e04020307 79
    0x15019044602852080800000004105050007200c10001d124144106409801000703c0070347e80d02c00c20401d000c04c0c68030503a545c8510314850716510955000500201c542890054001850141c0c00e0181020340c20034070283d00072400035927441c80b0084010782941d00040115170703c00210790080c42c486030090700c090040300d01409203500309034044452446e8000002000c60800c00c082c41901d901c11403211541d519141481030301e0f03840e90001080001409080710468066503200d009540040d50300034111800c00003941b100a002e45001c0c4140c0034288092002840c456001180711541d10b40c440c1c640c141001a514140d02503600060012810466050804804210103104881c4201d010391501d20410501c06403450840300c00130700e204c00350716408205000c40c5905c44120f41101c10010804203090b228040709851154040344600c82100340042c90480820000c51000c00e180303821200380b0f82940304d41c550441000800c881c0140010241e000038000d1012140420350414005005c840d00315 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 33362136 1250 33360886 33360911
    0x70804020a0b0c0c120109030c11040f020f0a17060d0f020d0b01030317160903020607060b0a090b03060c070b010b0a02120a031407110616030b040c0302030714130608040303 76
    0xa62102c1c01c405001d81113940404441c0c246403580d00f195558190080020b101c031a01c00501d030340c7c0d0b40200241400400016054107648a801c00130790090480700456403002e104100c107003140d1042e002000801e806005c4000004da900070020300c80c12000d0702410342030101ea0f54501d4054443c120032030344009001207032004504e00103015806180319480c0c0782c2c00002110f401d44490000240714020303d14014641c00d40b1150310000c100c0c200e0390306981d119140c07050b41c40c110000d090720721031458108201712000180444980c100c0000c154050b010343d00740c1d40f515126090a8407407181c019200340c0d0808010042070270000020700342280340d0b20603202401d086840c510b0b9180e022017441000030303844000c1e61000d0b035101d9054903001360300c3d0308188000c001c084014070307140c640c0104840d50000700310703a031034913494000d412100000710000d004000b00c1421150141c020341090f51200b0000341c2c0c00501340c011070480422100d20501940b61a540e09280180403210400010021801c050304c40a904542 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 33363386 1250 33362136 33362159
    0x12070302190303051e0402010207060305190504030806040e010e0304050f01020304150306031101050304030e010302031506030408040f1a040b0d091a040201080714040e10051003050601030b060f03070804020a 91
    0xd0703442503401003614140600b20a030400d403c07003001d101500c500b00900c801030381c00140d9a003c0300c0c01c0381408a80707590b40420000c5500394010f0f1f8102c04a0604080008042d4000d030351510034507085808001c02e120300442a400c079220702008003a0340e4006c10003030105140049010b400c08405104a901e02916821040200307400d254000d004680c80c1c2d80140208840041035440d4040c0038608a81140b6098400905a180c000c59050506a000004c185880c8084104821440000d85401c4d582e00b0070345000380c0300e54010302c107030101da82d043c0501140070b00845280110019a0440c0541098104051194150f02540605030543d941d114200e00245000c0072255034101d101e40801c04610b0940005055120000e01c0c0b8020840d0f07911511210041d01c90035102034a007000d18500c4660f890058510b44d81005410456001f04013005601c13038158541c210030f01c6244203a806100c0001e80405001042c05007000c8001081700620000721413900c20340d0b01c5548a40001e040d186410b81e65494141d8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 33364636 1250 33363386 33363433
    0x3020f0a0b1c0b0405040201020c121903110708070803030a050a18050a0c0902090120010b0303161b0e04030e13020a0c0512030f0c07030201020903010c03140708010812070302 77
    0x5448011848205102902ca800440f0360152418031407031030151300007501c588103141d41c940715230308207140a00c05003020420040314101045103502d0001c69800c0103002541c00488046141c45880c01c041103401c00411810200d49510004508540710541d10002403c80140f80910310f43d9283d45522609600d1003503048924001d4000c0e0145405d5404d010b80c480000e07400c80c03d00755004114000481c0d80c0b04001100c10412840312801481a034103150b40502010402c40354948800300d04070171030b403107041b0010802c90711401040310704016100d603e2440c01114411400503a0002d000640440d010300894403940c0d000916950600c600203102800300e070018184100004c1840c40b2210802804100c3c032034005003a170801508501c0c000b81d080b00c035038900800b42c6880032404142c000801d4001d4040c1d51001000400a0101e281d80c1c01c0014001d0590032050541e4554400c0814120b90140f0b6016050301c1240024201800104031915807581c400300c030403811072107061203060503420b00040100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 33365886 1250 33364636 33364657
    0x11401030228030c06030507180603090501020d020307081609030510020a021509010213091503030c0203150f0f06090403020a03140912070503061e15010c02040906090b0c0a020703020f0a0b 83
    0x20a2031700b0b000d002821910010b19240500014181100003200c034075456004071100b500d4013064603025407400502a01035102810b000074008414420003d4000074542e228081c5207080541020f402402159086180e200181807504015901042084280c000300078a0f1071a0048842d000540c3c030030104240000c4074100300c580d60101300c44202c810207401c40e00007031017001c00501104c4522a200804503045202c01030500020840c00c00840d00c0910055003204220b601c004510714001300780d0b02c81010100c07007040300c005100c130015560b1300d03108101c6400b5507016402064486415641501d8060040381044601d000500c00080c05650b04150200000f00d80400740505505d44024185481e030301410343c2c840c02c1628080c0b1102841c28022032503102c4400c208040c1704e16107950040e15a0443c250740a5000f6092000b903005028103900011280d0b48100c00e0301d20940e40e8101030036824003808503082c005030080c0d142000945484814003018080040c110080f0980c4c4a1080400f40d00803032490 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 33367136 1250 33365886 33365903
    0xb010605070f0803190506030c03070909051203010f061b030507020d0201050913090204061203020a08030720030309121905030a0b21060c0403080a0503070201060302060a0201060509010801140103022803 89
    0x1c0c01c0407143e021b59504500290300911180d0f41d10400241c803079681c3e0103442c0d00180e54140354401d01c4800c2040035003110070800441c1d541e5846102c200342441c041e015800103c0c54020346c19000c07128080d030b450b8a03260107a45050030710300780c0e0342003000e000e2140c18182d04100090204480c80e0791210342814841da148000000e6062883c0b05000584055921070720803500316604200c0400d03004500007100c10760100c1900c3e602c3d900d100f0f05a410b0008010001c1001081125400da2400000b0003075002e07035408003c0740c5500c2400700c1401140e108041164001706c4203402080b0000340210065a080000b080e008100140101c01280441d000600c151107209842089580751300000c1c041c80b0381120281109a15050840e01da0b505284070b90134400080141c0040000da03118800e41c00310018543c02009caa03521100c01000074081d00385030280e984940d1801d000024250070510404003040e41070307061008a42c1c0f130b6400304015840c00c03007015004241901c1010801c00004445003014500c5060b45 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 33368386 1250 33367136 33367171
    0x9131419060e0303060d120c05060412030b121906090204050405030a090603050408090108060105070515060a050d050c220e0601170c0a030212010e120405040c050301030b010605070f0803 82
    0x18095901100801030190804c00600c030890701c600c02c18a9045820100c0c10b00125208070701190a5102500040c02d01c0c02100180310810101d030303203030240b8000030f503a0038050810410b00700b10041707006402da000ca0340d0060000a000790354906101c00414001c5a0014804185802080980342c00300c0e011a02c5410004460740c00c190001004000b8010910301049a0318041d92600700c82e110304403249042c003000750001a00c5038401c8040b515002d5021058402010401e050f04803031003c1603401d14440c40d44d40c2000310302402d00701035000446410400606900d90548144a800048034004054901000e1024a45c00c00603028002881444400a08983d81740c000308213101c0d01800d00020298104152454855540480d80c205698040f01c65003000d082e1a080e0394010050301c6c0c0d0410440c0901001d01148d02c011070f000c0c00440b50207540c1440455a4a5002c882c00e01c000d000060152400e03c0051002c01d10070303030207000c60301d04c034124107081e1070300d50b84814a079504225100060540d0aa03030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 33369636 1250 33368386 33368393
    0x15180b0a08030a090b0301350a0302010e010c1b08090d0c080c03010b0406080307060b06220315150e0c0d06030602180603090a02060f07021009060f050909131419 71
    0x46013802882d100c14030b5400c1d0350400f404c41615002c91700007c0e0060207a44105130408408032440c12141109000f02d07800c0004920b80640a0407a500700380c51194640f014030a0898007501c0114030300000326951a0344940c80ba5901c0c0007540110200c80c1e00a20209407602c00540d03101d40030b0000c0c1105400900300d01b01400c08050030b40380608401c50140d42060410007820b40c0001c1602e888550202d80452580500c801040355800741c1c42d6506480c0304541c1440d2040d040c0c00b551001504e0050f21114668610400c6401c1996244990300c0d8512039280380c1006460004508150003400c4001c0329850100402800b0003529584d41040e01e46580c0042c00b144030014581320404540d43c20b0b2201b90651401d20345003a103441391071034042e000340d80c0001d1500c905500031703046402450b4001c0031120102d1409100070502031541c0101c2c0c02040352640380303201c410f0117002500d40c0143c004100c181d06030f5642c0449001038008440458007a0040d8402c000e106000384407101e9145146010250390395024103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 33370886 1250 33369636 33369647
    0x705060309030c0c031207060203130b01170105160804030804050a0b10080105070e0a060c03030603020904030512070203091c0201030e010e0105220203060703051906080a0c05030115180b0a08030a 86
    0x1389140c800da11010542d509445010191440941c020b600161245e54140d140080c3c0d105c152001440781040c2400480c4e10a1051000325030a00c500008101c299174fc2490055001e192045030070102c1c01034400100041d100c1ea4000364041e20030703000d03550382015594071074a042d01e040e60008503424070782200f440b000c80309101e16030340412545402240703042028007081c501071660203640b0400110301030380340a05009801010040d0380c090043c0c0f225150a00303004101d80c00c08c1d030750031030400c0e1a180030a501900c000305440a62100500d0b0300c11250794a8003600881c100c42804905040e210740065100300d01c207100b4042160210800803030b041c600000b8480001d00c2080e13601d5001c000c807a1004000d40c1340011b249500113154200090180c070340f040d1a1810850309032015601c03609094020540800100d103017065240f01c1c442280c5d0310703620f50041509035407000816181c40702032040b003000190f0310200c5402035a5601c40d80020700d1400107003c512241504e4121030144d61000603180d00c100e5005 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 33372136 1250 33370886 33370903
    0xb0708010617060904080309010608030d0b0f15030105090406090501050906011e060206061005090604030809130c02060a0f0e151b0c0a03050708041d0a06350705060309030c 76
    0x80941c2c442c9141c00c00015182440185c406081580e001c0f00040000d2800d61058001c0c0c01d030358003181d84500b00101e11202500020740064001c0c0d1400f103900816080c8045c400306c20758035040d580da0841e0b007442c051004201c1c0c02042541d540c0d0300d501c04080420000c0c0b241c40d0080c0c0809003d00400d604101c84240c20324400100c00e540306080c005c003088080d9010605c0354001c40300302d51900460030302c0503044600e809240440f66002800181c00420070800000400c0c0d075550540704000000c0e82c0c20200b800b00e030100944080580c00210014807010004e81c00b0b00e40510b5004400200d51002e8945280f403c20b250349903502d041003410500a40000d407118065078820703403003182031030041c5078003441c0d445081d0618000c3c14014040745000030400020b0546025003d00c1012914010681401205451086c3c0d81d001d246481d1aa000ca00c14000182d4450440e509500010313017948402070350000c5e6022040b03416454061030348041800d0f0380300720045008480c400010b40e1145a41c1a0260901c2481c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 33373386 1250 33372136 33372167
    0x10b090606040e1504060e09060603010903050d0c090e07020a0302060a020c0a14030403060203070309061b02120d060306020706091b0509040305070510151d15060304020604030b07080106 82
    0x118420405103a44500444090b541454407202040c0c5902004a2442070b010744100d501500f000c00108280e261202120b00c984640c1040f13480c151205801c0c1400c072100403001900203075040010081400c100d400104010300907207444100c0b10365440240748030040503100000142c00444040d024990704200c0143c10203580441140342244c070052560703940804080080100f0304c044014000340070240705540096400845c01d642d246040c000c020000c108142c000c5540c10314013103921001a20400000700c500c103c1c5c2c4c0003080c01c8254038013180c01070b8007e540350035910358503a40301000150860001e0a1803900c20200801c441c0c44a2424000d0020803465079150004118010407d5941d01422240c001e5050b0404039500d000034240a800e08440800c045501d9003406c440360740c003410b00b501180442d8000b10300b59041003122449800d4202c81690b0704d01e62444440455030440c5021802942c0282c80280038910f4555259103818151100f29000c0020034030030001044160b401c0348a00d111602d4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 33374636 1250 33373386 33373399
    0x1802040e06011a041809080d02070b0f09011407120209030f0d090503030a1418090414120a020303060f060403050a06090204060501030501030203030a0f0e060708030411010903150216020a03060905010b 88
    0x2403848105000d8403400300c50905c1c44c1c86039200010300107040100c40c40000e00c03c000f9545c480071814584c400ca42c050700c802044860120005403441b50600c034035042d048110684081d140c41d0101c04407034480b05001100185a820081c0744840d941c204124410465680d01a0a03030002c0150b01038000403542d07000d58020f0704100612419030340d2140c55040c461081d52034032130f00c0b80800003124080301c032440d00c01c50300400004140001e00082c0c840307401884d8028030490b01e01d1501c0107450b510a000d0125030402581c07050000c00c0740382c505400e001801c500085c0a10303003460b270340340c40743d41ca440da1504d4140d40803a40c5108042c29424203018640140c80c0c28281445a0752650b80465600d204240c0701a0801100d02043c503031103441042001142ea10061003076843d450030b818410420391040c0c90484640481c4448041c580d4020f0301c810007205c1c0c0002c0d1000d1469171003448074020b0342c0a940c45042018a1100c0007005a84181511024500581001590820515015003180ea580b041c0910409 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 33375886 1250 33374636 33374639
    0xa0e220605040501050406121205130303110127021216060810081609020304020a03060501230406060203030f0c090301020a0e03010b04090b060f0609030109080a140c030304061802040e06011a04 85
    0x1104071208c0d440d025405600681c150030340c0b010441d024040ca00210791021802c04000060580c800c0701d00340c1c1d04046100070840300c1c0545030403001110603004131000440448900074094a00803c011003458800c50950b4080140c04410010701c00c101d40014003c107209509100001200c3c07e4000081d1241c0f20080041c000c251804100a100c03c0c400c00080d180c0010005d01107480c1c0c079844500035540b0250604c21943c4400040724448280d412400c0203421140d19000c0031b15241c080c040c203c1c0c1d01c1d600507500d140c441c03407803002922200034943c0d000701104000d0007019842c02d1006140f242d03119a40c1440f2800c25004150a4030303030000c4032503c83c41c2004144400719001c4000960040000c0382d54209124051001c6142c500800c00019499441c5c910307501d0502038801300400d80088190703643d031000c078203045009040e802510f0569005502c14000500050740d0743c1e10040c0c40ca002e007650103021210f581d00080940762481d400440d242c200c07900400c03e1030007400800c010001300440450074039 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 33377136 1250 33375886 33375899
    0x806041211060c0a02010f0905060114150f030c07051204180c021b010905090114040c0203030103080703030906110c0f0705060711060306060f070c030507140102030a0e220605040501050406 83
    0x95501401e0098024000200d2240c840d00075882424284240707e400e21440e03004e81000da03162a024480c1c0043c175055a0000e021500d07260313000b280c0302e007112003081e41006040242840e15070401041402c10110800c032810229900b081034006010030460603996582c01c2000f5121400d6122041d280800d0426113034040c115004603001d05900f14143c0503072000c038560001218141c840341d001a0304100080004600321a40002418034044255020704c1240c08203442281d40f44030074031010f400ca820074000c3d0fa0002c4c0c03280d00301952030350085602240094041c021401c0c13a07408a401c0c0d50701c50340018410001c500d001d015400040504665803820503206880b001640348000c1c15051144070b000001030000e9841c0c0d42600c120040c6030411907203600442c98485040c100c54013065030300340300c0c18000107110300a0141c40000650180c0c0a1424645000070542c1c00b5805540796035401201c0e08151f6030005628800d50181410041c80441c485182c070050204848040c4c2100e17000d18200b00003440320 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 33378386 1250 33377136 33377143
    0xe01030b100e01120609090507050d020604060e0d1a0717090a0305030901110a050703020105010e06060d090609080313020f060f1905040506130305061f050105180402040806041211 79
    0x342816800c154074003a0018004a5a00104c00c1c43c1001e19441c02c500400c24418130351010314581e214004886007980c41d1406c000c010b15801c030b002503001400304824041548510301c85041860050003068010040340e035449010200d51a0500d45001107404102a450340003d03400746008990450140718140320b01841d8692013011009000d100001010071940d2034254000840e0500c06c00d45141c071402c1481004140354803040341500190700301000800c01b08100100c0c180150310013080103281021403921a0080c2c003003100c00395180c664800081c000b24504400440c070820005c3c90500f040e014510401c0032540500c89010700401052203518074401c410070407942415a4031280384014400c456048580340702d160020390f002140855192543c00140e00000d00f500d101d070003503400a980c1c08400c0a090b0381080c0c0300701c00c40c00641004003c0c035402400102031203c1e40d1345402c0c07801c80110005c1401d80e4000c0d8000102070788400c0400c0701303004074000034150808103403034444a400c1c16400c40f03d9a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 33379636 1250 33378386 33378409
    0x50412081c090b0117030903010c08100e0f04060f0b101e0201020705032203050a050105040308090c0a03170405040218010e0108101e12050d020d02010209010518120604060c0e01030b 80
    0x14111740c5881c200c180f0290820660b02c01c3c080040080c032940c42040383c01000381380141c03036008441d80c0a8200ac1040e0031a0084a440713103d145c2c40824844d61341c0e8460102515050314591071542d070718205d60300300ea00c600e1500150800c89840b60003560034550801e800300d0845c140c8002c11a4030520000c00010004011501204c4561701ca61542c0c4c5005c402075851001c5550000b0010b00c50312408904004041d00a540b25500135121500750b5903419030324030384804615400c46c0e80a00c07407103010b000142c204041c0c00141e402c00a41e6600342521600403a0490780110240b520138100d01a10042569100c401452008000c2c40c1030b0901d030404d0201048810311502a000004001200510388490380101c400f004208400748200c0307280250400d90303103450307a62b00800e0050107144800413000d80140221520950103941701450100300c640703034882d003031070303414003240d000b4200c076031000490000f0082c2c03a00440c081c030360000b003896001e0700181584000090381814182010110f0103079075182c0d90700e0903 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 33380886 1250 33379636 33379649
    0xd05040f0308070c0e010905060a120201020c040c0e0604080a02090c091f230c01060503060106050a03021317030301060e0103110301030809040b040203070c0209010b040f05060a050412081c090b01 86
    0x6807140c4035407a0214130310026800c800c10240c2c061000088140e031a8110901441003643c012001c9a110394200048024070b000103400f40c0d1081001400c2420181d000082d0818546001d80d00100b804000403300d03801503201c54100d030b10002c49101540b8010017000d0700004440101c51428400b9004200400f103450031242119500104101c841c900843c1d1070380c591180c00464040d0304007a240049a84d4014175000c2d50150b1a010010032103050010b905410b0791401c0e120582042a2088120080c2d440200c0220514402450003c0c0c405500010503858040c400f01a40e1a98140304008041030081e07408141058181071a010b20444500102d90540750842c0400b0760b90202603001c030b4040c00344481c0c41904207200100700f06c403541d40304c0c001c41409882200c0460040c0d9030f0301400b02e8640a01d0085444680701c90004210034640480107000244c202c0c2082da00b03055031441315040d80452444161401c0b840002c100407521040440e5640100c0c2c50402001035514503110315a95070014080c00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 33382136 1250 33380886 33380903
    0xc0a08030325020312040c030b070c0201020c190305030d060303120501120201030902010c0b0a060510021c11070f0b0d050717011802070b090f010b120a02060a030f0219020d05040f03 80
    0x60200314801d1045a00b10210290b22420b103042070719208941c001f07075200c1a528400d212021511052048428414003901607008000d04480d042c10841c0441480d80c95406218405c2000000070b442403002e09100740600c500061060701d1814081c00e242601d45490001600d002c0043c8000c02c07032102101300d09502031800142064082c030060302c220608400c060043cad01102d0800c0300f18101a000042924420303030790128090f20114003641c1e219074201d662070b1443d111001241360240700e8541a071100f0034100403205810f95036074010815108a0f0001d62502c000003c001e00c2609d80f41c0105900541c00f0301d00140c40d04185101d02080e08412700841c0c1900383c0240b03103d1282e480e940c0555800f02e402c09209085c500300206586c1d603800100c05a00019400c1c130340c1000e41407034400e011075050000480a0128013007294b00f084065401386542e0424180e4900c0500f004420a10203000301e00181c80041e180600b20b11406450022000440001c226003040288818688125402c00701c03680302800c0f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 33383386 1250 33382136 33382201
    0x30a050607050f041e05010207090903140304030203040509070302030906010b0301030506150406090c0206060a0b120f0601140304050a020a0f0602070513020c03070b010303110715051602030601080c0a080303 91
    0x803c0340b00e119075402943c101d03282c2040309143d8907848200360100c075426000c941006a583d08040d0950304041c0024000c640b060b803c0c0d41c0300c27002000003140d0040c4a4815246016101c0000485446060f40c032800000c0d4007000704411820100001405444200400750a6603d19030760241c4e10180101301089600083e5217149281d1078a402040141c1203c400138040444d0001c0025959502294020304c15042003000103800c0714500119419100c064000c14070079980d80d0580411400060030a07810803071155034061408416001950055226501420026696004000690749550013514a08050040c200050303900020600103c5206440110b55005c02002c00802030240c440c04140134000081d004040015541c41d0605070382c403980b21400c00300204804940d88a40034020401201c41200207a40c0060044000d00010b10ba90754114880c004180c1c0403a0404000703a002140c41d134000301080020340b80c01c443d0000509540c01c011803c41c078103c5540c46076481d845d00056141c03002e0110 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 33384636 1250 33383386 33383407
    0xc0405150103024b0304120f0905040501090203010303080906060f0409080f030406050105120304050f0919110a02100e0c010e030f0610090c030506210a020a030b090c030a05060705 79
    0x84c1d0b81c403c0310142402440300402c442c80e192030038010b4240c031200079441401040801c900750182d80c02240c00421410501d540d43c0f01c02c2da0301013161010700c0180140e2070700000d4156a45d0240502034940010b01503201d52540c900900088000380c4040d615420580030840c0d00e803654003400311111300403100030843c5500c6007402a928071403072145210a4400104000c207101c9181c009604a0344180c0740300000c0c2c855000300c15140c1c0102d014450744410400348005080c9810030185402c00d41e541d0410018028071420b11044409480c82a98000f80200d084807031260140402c40303044e5001e040038040c2c0440840403c1e01c490241042a040c03286244003001c40b92020458444125011011034109080100311110800050b10840d1141d1b0308003200d81c40c2c018440c0c000d250080c00007401f400d0030204440382d499241a01e007058014548540f605140159460081150003540540201c034407905007181401e0501e50815880c500a0788950000c4000038400500745070700010910740b09886101c140c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 33385886 1250 33384636 33384667
    0x215030a060302060310060806030303090a0b0705090402070b04020a061407170903030a020105041e15050901020904020f030105120106050d0f0c120809010909050108120c010e03040f080c040515010302 88
    0x200b010b504010044100500011003004110580380ca648507003009a84070406c0640e244000c4503542c0d0320380c100c5440c1500041d000c0700700a4009603e810060b040c040c0d0300010a0032a040314205460040c50401840290704007041c0c00c0001c0c080518001507407107581c842154192041ea400180000940300d8142d030540341100985000c0f030b0009081d203a0703400b07500704000c0c0a042c00361410b4420108441c24200341c4181c4003030640c2e0003a4482689918204180d00c48802000000d011005c255002c0092072416600e074802807001c00c410140107602c0354180000c1c41004808054003410070781c0341500500950741d030040d810280b01d6000c2011104184903140041c098055580f100070403000d40034100c805c0040d034601030800d200c0c081e0380d6803103055034034600c0d01300756902845121080d40101400704805a42d403001410710910b0180041440707000305005a28590223071740010400c041d440014400c0f101e05101d0111060380482d0b05104900303002d000d01400400e4079816a040c940d0003d2500c80790000c42 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 33387136 1250 33385886 33385889
    0x4020d06180302010e0a0b04020f01020708060106090e010909080415050702030703030305040519121206081e0d0207030506010b09030c0409140106050306100b0f0c060103050c1003090215030a06 85
    0x1240a0010266a2440070094607462200b20055401d09070f1100c00c0b40e00c0000e08a04a5400210400d4031751644c1d02031108d54050510703054114041c1d840081103404040005500030f000a580d07600d003103451300c1615100e600341078200c01030280c1400603800c0070030207003400e850030713076888121500070080160000e031500e200d8004002d4040c05503203400000d140d0107501443c800da01950035070747d5100b10b0580741c81100d01c0d00ca10007003961031619840342e8150b100e09050a030005440308000b07007841d11115490700e8490142e901035040141640040410002841552216072441c00101f090310705660307a20b51245414050782c600d000010680000ca55800c1000440103200600200001c154a0410013100d951644003103480d98200b00300059903041c00203565108803203010b079411100e41080303480c0c201a80a0140600d0782981441440c04038071042c8030f414021882040100030324241c9006102441440c06002000d25240048901c0941c5503040307070111241001c15125039070303502d401c0080020040c5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 33388386 1250 33387136 33387143
    0x309030403150c030c05030615030a0e0106030b060102070503030a0906030b0a05060705011406060c0a0b090a0b011503060f06050924040905091002041211010e18040b15030a03050304020d 82
    0x442c0c60036000d0203115030040d00044410340c1d007808429001d0605075228482a80c4440d041f211840494010f0812031019580203580701a010030308840800301c0600355952904241c8516040d80240015981c0400401000b071100364040c40c2080e80170b00e40641b89406070f11410003407503120303542410590ba4003c080005020000d05c816110001070502074000c0c1005003070f04480712441001b080903407034032006550300f0461300801456035075015907829000c0400507280d26007900c19040b504000800c90701e00c0c10b000c6c00008111105540142c60700806580c026409000468152042030140d1030b0303c0007ca030030100007502c5120018100c0360681000002d0615441d082d000086004680b1100b41c0d0484d40c001c210340c0b0100c900c60040a40c1c03c5080f03105c1c510505491385171a050140000398001246044082c05050400300c2500d80d8001c241c55030b14045454005108040c200000c10098111098025410702d0015203902030000202e60b46030b08000d4060107010000c8009011951601d404c1000c180e072 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 33389636 1250 33388386 33388403
    0x30304260f0a030b031f09060204030b043e0f011101110a03060905060918070e010617090d021f1b021c050304020a0e0c07050607020d0f050301050a09020309030403 72
    0x40400300040345402c00154000028240f0311401a2840c00040703d00c0d1502c400c050081c0d040c010948014001c20001d01d0407a8000c0e020302001000c14071004510780310358080c44400d095840d03100300c101c1881d070741c8041c000300c1104003840d1110240d03514a1540286041a00c0d108040c084400058440308141d102e0300d40036608002c007004d082d401c031038060700c9c10300341c1528180480703a00d86056000341c85d402c441e500d420484c8203000075044000f5a426911407040b2001b070768842503c0300c640300301e4031000747c100b00082071056451640b8210310500340c560081000c03001c2c0c403912544500094580c42d0007080c0e40704508095581a00000b010b0380030600303201d458041000040080035010351594601001d10782c1c9076400d02c5141252600480c01c0b00e115583c003c0404c08000c2c14200620000200606450190340c01030205000103001003281c0d0340a882c4980040006251041008142c01f41100180007080b0041c001000903844102d952401e803000d0f1032000d6140d07526080c800d4518011944098601c00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 33390886 1250 33389636 33389647
    0x1e03020f011a1002120a0e150705010204030b1f050402030c040801090f05061e190204030b040f150603030503040212010e12041e03020117060a050d050115080105070203030426 77
    0x1081e0302c20722000e82038a50211a0340000b400b0798072a04c40369400e8040c180100701c0ca40b00c061080303524169008008100003840e00f000400201103412409046401d41e60005083c814007100b8080c165201c4134030011144090000d82c07000803036101c0e6100c0c1c41e01594004c40880c000c20f19200550340a860000000c1206048504000515a00e1280107541034064500440c5840301c0c100d6034040c145d04591139a403042c0e140c048010140b180802c18078419030358203100203c00255a400c000d0b004078042c1020910f8000c103400c2001180140c81e424880071032030b0520402c0081d41003c00c3e40d81c4250121404d540100781826a10b0140105008101060050308441101d01c08182d026005071104903c01565054020502a8001d0300a000207408036000400c0c03441c0c0c0c00c040e803074800da01800141c003101155603a80d0106403078102041084038540d450f4501d1b41c0560801c1c0344d45e0002408004000c1c095401d141e00065200e1002800140810305040c4942c1089110030414090b50b020251190750341d103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 33392136 1250 33390886 33390911
    0x30b130b040b0105042103021e0105090d0806031509010f02030c070c050306070509041a0307060f080c040f05090417070c060320030a0c0903020402160302060a02071e03020f01 77
    0x1840c4003908584207602e460310002d8254407480c00e44040c2c80c1c0c150809405a07460340e0040209a0304000300300c04610440d00c41003038030000b003011202d03000040380011659042082a41d418541c080c44003008101e041e10412030960780006c5c0045038602d07074281480f45525104420b45c054144190390a031814000801d00c107140011000134850140a0603500402540326010542c8540099440c00001882445694403e18043d03102c05080c0000c140c6801614042f8030200741444100c0e44410f011404080c4443d803d42c0c1c000350b0040d80403103a940d041e4505070030075540c0c81e034090036802224011010440050b0401440c00246808100402d40e42910351501d0310309200710003890302070100040d00f0000c0a6030416243d0b10071070020841c81c1112803c0d950381c000040700420042581c00d04018408400002503103a91000384041030501c134403604140c5090502903d00f40340641006955803040101380c020038404101241032420711002d59400050038142280340c0940d0803204002c0d54a880c4100140 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 33393386 1250 33392136 33392141
    0x40b0a0809060103050615010302120c04090606020705091b070611030a060e090c06090d1401090c08070303020a080f07150f0e010902130c020f030307030e07050f03031603030b13 78
    0x1910459603a002595079a039140903207880082c84000d1680e4441c0022965103000d400d0300d0003801806240050070825010503a404504045e0340c45100d11000007018000c000a80c0260b41c040c0505000906506261201160380080d000340f4065050030864241e00319549601c003200c2109410800034410882c000c54810300c1a4400d03150400c10034500000000c0c0b10398091251849071091001030b018030000501806441d81c031000d44194481a803075920000101181c4031b040100c2c00311800054078aa092820304030004590700664501c1e0b000c0d500400000c3e070300151580041d031f1301546040d25041d0101e08a07500f8010413200414003040c04001c02410f000c0b90380018236095800c00c082c0040348840404070b088034210344000c0e40016000b4560021000a6080840e02601e0340c412a0200307404420800c1c00e581081d00c2c068000394a818810a030050204600000381000312074401b0381d01086400203503644500925888062546d40c2000c05043c000da21400164501901c59140d07500d00b0b0400317000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 33394636 1250 33393386 33393397
    0xe030406030b0a090501030803060f1c05010207060507031104091a09040501020901080105100504030219080a050706090501090501050a030b030a0c060521060d0b091204060905120a080406120908040b 87
    0x1650320060002480804c030b0280d14100da030005c40c0140303103845590a0000b0800c040005c40c1d08030041805440800f11038a0000410b1070040000588810080c980b64003a25005443c0d02c042605100c0d4200400d10350034120b07400c03107803d1540080c208200215041e603141c1d00d0074186038000340003001c00040c0081034000b440042000da0b9400c0386684c840381049111054041c002c80090740c00c1c4400d200600780200e005014407080c1d10140406070fa1040c8040c9440b9201c803048490742c010344800c0100c1a00310140b5005040c007400c0c44002c0a00302800201a03010b2250f8190070181c4490b0400343c503840c140990b046c0c5036044004141c03055160b050140a80d4002e00104100080b1030300c82401c1609004601d43c010103006140da03054442d1030302c1d403511080c00501140345034014600d400600e00130030b41c0104000c00f45910780000491411080103001c103000406079003d0f030080c20910340054409000c48080d0344450400450541c40154004014016484020078800c0000303000306480054202518 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 33395886 1250 33394636 33394639
    0x8040306050a1104120c0305010c050c0f0102030105031504060e0d021c0305061005030622050f01080307021f021002030108060f01171c030e15041401091e02040e030406030b 76
    0x1d03850700c40300081107892041078080108418882440002240781c04072943c640510010213880b41c0300d44446086810b19000b603404160b00003078000c2240024400b01c0c0e40c82c10010000c40c1103626000210f62185580302044150428140000301009415032008503e110303502c0803181e12509501010350f071101c140540800c20742840740313107580c5144a03010782486100060983c50b601d503607101041d00c00741c00c0500004c8d8080c4118421143d84941c0c141481c0c602c3d2104100801c640c20614100d030002ca03070680014910343c100b0003d403809a282c81c2e041050722000072940000b5003103440b1040382010034980b09030b1002d031700010001074442000215207004580034041c44d0b1140c1daa407034034202080c521403c44001d0750802e5001b902c44050381454880d0f90440c078200802c00300b240440780d81c10440c0a20280d001c5010903800d20091007005070009102c401802c0003000364030381d5920b0325061446035980c000000c0221600705411500c0b030303400200c465070341842140c0d251074403118060041c24004c003946 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 33397136 1250 33395886 33395891
    0x7030e010501090e1905120309030d0f060b0304020d1112030301140a050a0b03090106170f01050f0c07060b060c062401020313050d05120a03020406030f0501081c021908040306 77
    0x200d20f44105110308002090948010f20700b100c00002000c148040848094846001e18030141d0080b188800c01103104110b100003940c0c0c0c800c12041d2680c11201c10442c91b1040600d003440c107116640400d0200da80243c1c04840d900c2d403138115481c107400414a016142d40d0406030026074111080c0001002d0340c1a074035032607443c0c42c54213112418004020860700c50385a0000b039062007005074154100003142c10103000340010840c9500d13004c02007810f1600204581d4160300848828440030000c2c81501c1c0c02c01c20325080c0c140c0e2420040109081e501800d00f020b407816581d140e59040540e18a4100d8040740d085005032040ca16201790125a880d800054450030101b031060712401640c800f004540c80e40c160300010403d5a418803007881914001600304680324402e952800040d032a0740c1d07001d00480780f82079130050380d640c3c20035000405aa2a0410326a01141064010701002c54040390903d4580804a1002e80300412080101d261008042c0900c00300205c84c05500180007900d4014402d4a000384001d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 33398386 1250 33397136 33397139
    0x5030f040305010f200a0306030507030b09160b181c0c080609030309100504150509030a02010e0a020d02012118110f030618010908040b0d060e04050d0507020a03080307030e010501 79
    0x64141d4009910170f0b0105110030900700c90b030004400240801511a00e000030385651255103083ca046000d400a840c0410744008002c100c7d0001c20000703143d040c4041c2c2c3c64850502c0c04001e04864011246802802ca0417640e0314145a100d404d101c82c1c440212044190104940d4140118491900c0c0150207103070041d9030009140401c0082243d00803003044009003007150b4580328000081c03502a008079109a1100d00705882c81003c2e0050741c0c0200203280107181e03551580e02010342110407401e500c5a4507009140c0c000c001d6602c2181c0d01e045181c0a0070141201101c0003510400c080140181c7c000891805c000e90010704820340303070303c0001403013441c1c441e4dc00365040342000707200140308034983d502d54030080000329801c19006080001103441d00010130010090750382e404003900035030030407024900041040d0005940d02c0c01010010300d040c40b40035040e400e1941f2096280c0c8185480f100601c14001038640c00c545840c1c48240045410021003a02c9080c10a030003009400204408029076003040d00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 33399636 1250 33398386 33398411
    0x13060203030f010e07030f020a09141917010b030d0509010206010e010510030b06090d0308090705060304200112050705092806080604020405030609030a08072a020d05030f04030501 79
    0x899004a9400e50854016072901a0000044c0c0c00200418105620340781b1054659110b40060000c05220351a580303615410a6018111240c03590f16070361043c44440079007030b81d107861340503000291b8030201c400003940d0030015001030141203943c1c10280c05105240e00080c0c1c0030340c084007415403450300f40c0c00e6039110390707a9182e5024514401c1c002c541e4021141c0f111010414020381c05039444c07400282103e42041915030014107145003144064011665640801214020034001b5070b003e01421184103045040c240c403008180c008408440c2c1c40c4403c100001c0d0850b030700418110007030301c910f050140894500403800404503000000594040c02d0396070950300e0f0080206000010f007141c80c2500c48102480c100c0f08407414580a40141d030005d500300000302d280d45007070011921500c0d00800450f0303a0050680001c004410080c400c0b000c104402207101c1c4650950101447c00120f0301d0030f071250008070341c0000754120300d8480006100d4440020510039101c9818090800c42c1e00a800800c0080f01188 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 33400886 1250 33399636 33399643
    0x90c04020414010c0501090c08070e0906040c031209090204090b01030e0106081207020f090405031e0304030e0d05030d0617010c02030906030f041e08030a0615140a0311030c130602 79
    0x2000d0507003140502c0b40156510a800707803218a4040c400203c2c2e4080c080d120441c80c050650410600794122007000c0c440043e0505910707410101381d00080c40c40c3d1409841c1e541c0440c5003400001e0100c05405003280310240300d00340d40300260902032000c554a84e95207600b0401003036840c0810340424240300d0170071110441841800202c1340c0d21400f40036000d0821410300019407216008070b038405011b44400e0740f251a12210180300e944180010b680d6002c8040080c2c0026000e01110400c0f840d0410030840005d41c41044100b1500e400c2d12501103103a61072415508501980100b0143c8510702a80000c80440030341c000c40d04801c00d200200403482182204a07202d00c11042c940b0b400010030070200300314403402091103030f2150080c4411003041003406203844040f145000305a4060744044240000c10115101d804000c3c8162050110f0440c031211016088840c4080c0c800b0440030040b421b411528003076040b1424095841034a103a0380d15003d998080c13150071815888082a00c2540701241160000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 33402136 1250 33400886 33400889
    0xc0d1406041a0901170102130306050405070506160305162009070c030806090c0c0d08040312020304020d200a030f1205090607060c02070e0106030e0607021902010c020a051503090c040204 82
    0x94600803c580c28440f03400d0000b9041010440d166500300b20000d000c0c019025040c01452058501007007a050500389240703041541e03048507100c1c01c07081200c0c620040100c0c444c0032079182e2600307143c2d4031450f02e08000c62621056803806081102d00032407110b0400c0c00b03800c0c0514141d2007200c40c1445600c84040071184494241001800319186101082040c900520820341c003104982c9034524040341072030a40c2c01c141c207055201000c21001000d0000301a0070880480010258500071170561409070000f03100200d15010140c00c0c41c0101c04007111406180c00600060070020b080c060103240d51345005110f4410245043d241186150003142580f071290045421b0440010700490401c80e26488660050001600300001d40c0b00c1c20f070b00011590682d0320f00e0b40c0200301940f00020041c41d9100a1410010300a101c0400c40d00301c0302a80203c0f201074a590b940a07030302031070250031890441c0701082c0c4a12131a00302a500032034514a000026201d030004510601e64401038594204c00c50f014007080c0d0150713 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 33403386 1250 33402136 33402139
    0xc040e0610030f0809041d060615040e040212030c03090102060c040e06060d020d050109020a0e03060702030f070c0e0f0403021c080103080f120a02091005130902030c0d1406041a 78
    0x100072042000c6640d002000310380030300442c0054a440342840c0003800700c0780b1044544510300e045050800170394500b80207075a8000000d40d000f03d200c03810841e1000c514403490182e00404a0a40c001c90301790340303a1081480c81d412540b021a6640c000c24010180d503600310b40a008e00510030300c00010b41c40c0d081c140aa03801c684e00c54400f48150349582e02040441d03008004c1180c280e6609100030b003100d412502425008000c0c0c10b80040e40c866400400610070f580c14207903603009038080001e00000c00d070300100712640e0007002940103840c0c180078900a000769070903030301240028000e00140701c5d061412100c0d0340d00591280d000c40711201c8001c4c19803010080388104000110391004010004500110002c00210401180b00d61070412040c00c0002e0000d0161403456007076602090204ea40d04240301c02d00c85421a505080342040c542411707400c410801f0317014804a441d008400302d861103880c2404e440080d80315010912500c51151105c0f12070003001c84c0c1d034038891410f1000d4001411555950070142440 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 33404636 1250 33403386 33403411
    0x200a1b15110c060f1204060603120807120506030c0301020c0105070314040302030304080304020103060312020624060304021003090807030302030402040b0a0311040c1b0302030c0609030405011209030e0d050c040e06 94
    0x2000c0401405801110300138101e07600800c0f071901444000c0c5e000c988030301c1c450702c00050303400d085003401e20540008500190a10112406000c1e88030703000884c1075003400164034007094640c0ca210208ac05d040406141603010b40c00481e4078505032506400c40307442918180c0d0b0402540c0420511800d10090035500035025804c2003000ca03010503042d0f030095510078018100030404680c2c2c6d07503402d882031060040c1500160800d000303100e542840d20070300c090400c250302c24520406d106803001608511025100900c10050007503c040d02a0082c3c00841c14141c01242603500c6d03200d00e00f03010740a503100b240c04078801c6150044940b554980684d04c03c0a032a04440180119900801800000c0160409401c2405520481d0b40c128400c03103410070021911031f80c040c68403882c1000300b8501d4010083e0000394560000c0c0301c28000c03a43d03c005844d000070710103500451280c2403030a00b650b00c9080c400c460798015041407440003d0000010307145500307450594080100b10726080d40c2c683c9508003039881006481 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 33405886 1250 33404636 33404653
    0x110d05090612150904050a0209070504060e01080a1103010605071e030807030518030406030f05060a120b0c1e0406020d0206040809041109090f040b010f06200a1b1511 73
    0x5450324441540089084400f0744158103590000d01e400400319411103c5e0360001c034804046062641d0116003080c200d0511034101401c1120242c1070000c2091414104803c2c90700003002090603421a400103080700c000140d5958407102d0003400c0c3c0d808080155400d0003148402c0f144d001440c440800310f0b98060b40d41c1030880d21501070860140c01d02a00304400000300c102224904002130005000815060f10001801d0110b4595401030301c50091031540f01e4a0781000c2007041443c11034003c0405e69004c0700786020381c0e42d0341d030410170386000d00303a03010712903e07001034480760820300500052041c2c4809808641a1100c001003ca950f0441200c005040310300c14080c1c10242e06064024010100c0c00980c12410040b640c40444d42c108070440e1040050480c60080c0424800e1211105004d482405201e920142c00c0c80c9000d0000031110b1036000750401d40d0303480c5030340603202803001d4003032964004c1600140d90944102030180b07100ca4042e0780884c4081040008a05001c4c1000d000e01070700b210050311444 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 33407136 1250 33405886 33405907
    0x90a0b0c03070203070c08010b01090f0b07020d1b0e070908011a130603050a060501090e0f060708060406050303070f03030506010e01090b0a181206050703020f03130302100903110d050906 82
    0x41e000504814258030051042000040500100e4005010b00000020304c0040c0d540006100c3d00d4598031116098224000510203800e4000403110085e4041c1c400c500c24036224a040c603641b00750078800003491501d040c0c020801e5407a0444080c0118810b9541e00301064030789880314200c501280345100c1010320390720740314000d00300711441c5100c1c40f181410003d1440d50b00c1d2900c0e070822151040859286a40704018040504a0710a48421011003c001d10201d00821081552a036001e441e140501441300000340050340d594001d007014010203005d9075204c50350780c03520356101100d02004601180c2810009030485d4031568014412040c140e40c0c0009903803130300042c40310a912807400441040420b0f1440303110025015181c0004003c0015031086040c00ca040000440d400a800c10f0200350040101e8100152040190794000d044411803907541d0000e854264507001c3d92248110b0418203240000090503003150442800c410080c0503200745602d2807000315000d200d45070f50903620010a110b0604130 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 33408386 1250 33407136 33407161
    0x3030905130209240c010609020304050d080603100b06041a03060a090507090306020705190c15050a080103080310240305010e0f160c0f121706030d1103070c03030e09090a0b 76
    0x11304201c100510719010480304001d0a41e4080d07002220080d80000038401044402c02807448600340c00c0c9070007503413414004c1c0043d03200c0c40e220340304803001c645442d1340708401d548241c1110010076800b9071042000360110084135075a0002c9a003c1d12800710190300060441c154010301d03100700120fa031050040d40c2581d0701c0da4025008004285c485218145d0b011010b13202d80ba00004141e03000305949803286141450314a2044a03a01e1800d08120062010394281608130b900700b81501d0f44060500d40783e82d94083c40d4560403046d81d101c442a9140d200d1500d07018100ca0521121a00b66036038180440d80c0c0340c00c62102e0f441d078280d46003c0f191143e50001030840d18090120b043c40c40543c0f0b0044808138103520744055000201009503000481c4d80c0300b50841980011001c0d070646650307084890a850300c100000c6d01d842c0b03080309100a02c13046103112026007900f8011201c03a107600c150880c1c1116102d060003441c018507035082c64094001301c804552601d80001754100c185038080e004242e155202d9158000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 33409636 1250 33408386 33408439
    0x30503061e030d0504030213060506040302061b0601030303020c010e0604020f0d2108070905040b100e0102030d0e010b030c01080c160305070203010507110d03090201050403020405060604050a03030905130209 91
    0x740c1c4141505580101d5a0600c0305480b040c1a0743c0d912501c5030f082d0b0040124250110101621041c5064000c00c800e480c0c05003642e00701d03601103e4030307070f04c0324181c0302400120075503002503030100e00840001004160301540685050a0301500802812001040240e83da880c1950007941c0007480d0360ba113204616140000d0000c1a101e820440d00301c6c1e544074145e07161440860385442c003088000d000c104d038840d404800322004101c111401d014804008000c41d84a00c0420035035000c00a10503030412160b4000c1048170140c6a51200400c82d12a100030958000c201c0c800b0321911a0048540c4842039600c182146409004a941c0349891300d4612440007100c41c40300241203052140902c146005a40e0030f00c1040d01c103440e40e0b1504030000c3d140c0c00016040900100d058070600d850000c00c0340160764400b080d01c00740c4ea41541d0000d8543c8403031000905038016039211990140c8120000f00c01c07d584020036108070b4005980d102001a800c80e40724041e0b0007103e0300280c001d8024528107a082d40311100062 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 33410886 1250 33409636 33409669
    0x3090303041e0806090d02150411040c03020405060c1e03030121020102070308120403090b0c031b0a06110a02060a090b06040911030106080106080709050c0a05030a291c03050306 78
    0x1050325a50283e207420000229500042c0b0381000d19441100d940500c5480801c0da03200110024038600b540c0c50042401031503030010300030f590380e84010640d03e001c0d904442c0507240007003c5a0b02e4210f00c200881e6101503c0000c41000300050824181804000050701c2c141c0715880c0c40b0203e441480000762607c8200b100d0700764118400c83c900000450304041c0101a05081e0018128040c5054100609801c440c4c0d44031400300c41d81006045d8020304080181d40700b498080c2505158070340e0382e141030b61030700c0c104480c0a0441490b045401185241d024001d102c8450300d0b409882031641c40768101d408882002300040d01880d9a60001581442c00b6030244942900c541d04c0c1c80d81660f41103001c07070b0840e099904012400e03076554400b0302404600300010001004a0301c0184400e2906c154215203e0094181c03540c00e015010010481740d0900c1d4000e0030095680840e003506201e0180941d0304070007929440c0501800c0043c9035070550f284584001802681c054842900e50b440c2c2800b80941c2c0a030301000704 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 33412136 1250 33410886 33410939
    0x5120705040501090b030c011409010f0908030a020601030506010f06020d0806180c04051503220312020d0f1803020604080d06030203011103060f0307030512030414030a09090605030309030304 84
    0x105141e51079100d481d01803c40500d002039628980030034180b40818a01c0c40c00d060018000100f0100d00051082781c60340d003c286825881003041c04000d8443c0c210a401401980c0000718211014985c0051300c681200d0240302101c4259070ba4100b81000d0020500070a001604012400c0c1d0340070340100d03113054000c0c002510522130108a03076004105110142c0b81180003810001303080005182042c0281d080d1120f64140e1461070130b1210b19001c41c5081010b0400e81b40c0b0010000388249801040c03007800120703a41d8003d5680388014034440c00142228100b8801340b0785803500c0d08038a09243c0382e1070002240d0540080001361038a49500c11150008041c403011561150750110041c3c40c00c0c0138852404e09542d840a4a07414110208400d149460003241e0181d84480300c1040410000214107108080c0c0c5a0007a6403074403642488959010214103803025880002010700c003980c3d1001e408403c0328085d140812a8584030340405490f40316096403030350b00d68000c2c44140005400b1901c503084804408010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 33413386 1250 33412136 33412139
    0x11505030a020a14070501060305100b09040605060303040b0a05030702010c0905030d08060303040b07030504031101080f0f06061614070b03151e0319030e030d08010918061506030e0c0a051207 84
    0x280b1300542c08144100c1341c1d85d44960041081002c10080017149031602c00c03080c0000224400480c0c01104000e00c05000151950007040041c2c03414030445020b1700b40b0040c0160340d41250782001c2d2190740151291b00c01503107401c0700c82c1042e910600b030050079904000c3c0541b101c0303806584206d61804000d0419136043c04100720000d00a1145801850654442d40b103060f2241d00c2c500f8480c21541c0350300600da06120340903040003a400344001307110b5409841d800d6086526101d800101d10540201c2c640d0303204104034062490140641001000b904c50614812a01141d8444403140401d00058502c03140c40e99502600360350901e084440e0708100d0602a861051022648000074a46911100030440005007c50f6441c00d1507804003404041c800283c009107641088844c0c01000c455051045c41d074620703515224906020400c820035003d4035082403041c0511802c1c035041c5084d4402c10700c20400844e00d4040969030300c0170701043d001014800200b2024003a45404144028040185041c885034080c0500 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 33414636 1250 33413386 33413417
    0x120601031104181107050c1512010e0402090702010b030d0c02031f05060109150905151308030a0e0f0f0d0f050f07150309050718020c01061805011505030a020a 70
    0x3500003010740c0403401010343c10320f0511400f102c0d580f44034030f0a6581c2c00c012200c04500002501d40d0741d40000c0c0c036211a03514003c400c0041e03034000c0d2481a90fa510901000045008101d950940500e008940304040d0fa150898142e00700c034100700055405400840c60401264047c0e05c410030304a0000e0709440041001400c140102d40000d80350206c2c045d910824050315503445a50000584084220f541421503401e60280c08ac10761840303610311450703404003c0c0c100d040300c4009540803080e5000c24948156110a030541d22a0040e1080c100040e40e190b20000c00b40c0703030088a4041105001d003008904444480610070034049000050721003001a020342400030f0010421a0366100b000000782103498100701d4204d1900c2902d882c02000c250400103030b41c0c041800071612100f12030710030b0003914483e018116a02c002c0e005403020803106510b030400000303200503911105104010186401c000581e21891244102da02d01011200041e00a00010b41203080560003400829644d041054203040141d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 33415886 1250 33414636 33414671
    0x1a10090b1818010c0c03050403060209040f0c080103060507050403020d080a051603090e06040515040504020406080307030804060617030304060902180c0c06090102090609010507060b06160c051512060103 89
    0x101c0d000c58510580c41403482d07411083c400c50b88a80c0780d41c98142409011034600401c280118017020300300590000e03640220381d840f580b1401040b0f800308010702100042590240016000344070a85d0168142030010300c2485c4214102c50550b907008004144444142d1201c60081d0041040c03032081c03103020008440d0388021000010700c20f51007540c0350384030f0700e04004400151240c0030700f04901450422050101c0b9001c41c03030f1003400c10300c0c055900040c0f55546000040c0030300b81550082d4103a01001800e0f80605038400f040c280302d41e0048200340102507550b10700f0440c000404461075816041070010800180c0150801d0b421580020141510400b090a894004070000d845641c440c0c071000032a14028441402001e5000d800c810007181004440d102080b610f114611490b030400800080d0b040c1009040d5105074242440644400e88680455019001810366424140c4a12000301c40000e2030b03103020100ca0603c20110180541403003d4080c07000c00f51074010700824141501e4110382e070103800146 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 33417136 1250 33415886 33415891
    0xd03030f0f020f0a021506060a0c02151314030312040f060b030d030902120610140103061805011a0301030c0e0c07060905160f0e0601050a0519020a1a10090b18 70
    0xf030b0b00150f4a011200c1c0c041e1a04503842c00341e0400610350b4041000690b10301090311601c4600d4101440038603458030000d1000c21510040701440391000c100050103030510400101902c1e00320078032011010050041540e00d00a00c0340d142105001e10380060000b40046040301390341807040c080880c00780a5800024207007480d160717032003000079075601c1170b9419032030446056008130b400100035210b02d00780264980320942d00c5004011744065145803498180c2d22a6100c0c10060603400c10043c6c8168240c1c104001078031081c8a020b110301d0003440d4640407001c916049038105d941c04220007440340e1400408503a4a10300030301c0c04418100500c40035021425900a0400c03603446a8040c0a500e6150340c801e2103544115042404031420700207061100036400d02c05260017403000d00f02261507135080001290640320f80e0f000301032850314140300c140d032441c2c002410351002c034810070010003d07000c0031200365503841c01111030005a41c00882d080000d044140e0200c105031300c015040c258583d5900310b46051a078020b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 33418386 1250 33417136 33417157
    0xe1c0c0b091504141003090203060a05131a090c060f0409050414010e070f1a0702040906021b07030620030411010e061303061401050105271002010c090f050d03030f0f02 74
    0x10081c4c0c5588030b103002990526454040e0608200000c44c40d00441d40d1003000400b80300c0c00076940c0300814010031203034851507802503109000c00b00090b02c107030905100340b02c16111020079200d081a2050710b0700d400001d480b0060000240a0705013490940d01c08054040580f040d0784205c554048130556040a00400407200348820007801044c1ca004100c0d500040c50340d004a0b41e0032134100c0c800051400d0131084490b1590104c5002c00d05a000d400c1140c0244102520b0344001c103c0305040924019000c602c00d000c07207000d01001c000c0c2503050b0003186490994040314a1b03440c041000001c0c006030403400040411031040c94000510841c0c070020985680c0700c1c2aa5001c449040203040081001c14054240c54100c8106041d580e54940340001c0d28901410b060342c00381c03548283d04080e0900030281c0c000038111000b080c500d04102c03040340181c000e0404883c2c5800040e54140c003c18445101100f50f0100c03040901a140c1f60303890b988044008007601140e10b540d150701d500020160718024005400303100324 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 33419636 1250 33418386 33418409
    0x4030f0803160306060207030611040f03031d03010218060c10020a03020d0b0301060305030403260a0e0f030a11060c0c030105010306060e0f0708010311040e010c0e1c0c0b091504 78
    0x24129a0141a030b205040d590781050f040c00300902c030300c1d5800b01c1d060048075404003020800c011002030950003401aa00003401f074589000d0b000040c10750180c0c02600010802440418400301442810b080c0c1c0300313000c002540c0d51020038402e40c403804c1c440e0080c10760900003800d035600882c8140654090340e00500c4602d0000b50085008120b042e410700c41c142c54030100320000c204a901d165035450303ca003d0361101a100c100d0004003000f940714003401e2580a4100841e541d561307484203002c0908400d44001a0502912440c3c00120a90400180340299190040300039451103aa03441002059400801c843c50b03580110100708005407130900440d4080e62240c0408501d1a050800c03c181211000f00711f00c41c51401c401c00d008006c1c0e0403040650540b500305550004c9450400d0108008d408a20a9411307190310f030015480c03103590300c06841c20700360104070340700281001880e0301805240e4001320050310014094408002035043e11005182c0d448014081410000b0810320350600c40d00250f11480f15160b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 33420886 1250 33419636 33419641
    0x30909090c0a0e01030506070c02030f060702070314030c0a0b06060c0f0d0201051608011509030f06050f0c1c1a030307080307030c0801080a060504020f19080601050906011e0504030f0803 82
    0x203441c0d02e00070b000d0b1020300d1400401c0d40c915150603a1300c201c040c04400074800f070516000150f4034140640c0d03c510600c841120800c0c282480006e50f0340300144019500d903200304c512582003c0010007113034441c080340030040c035104c0203d031240c0c28242c00c050441079010104109080c80c3c1070040c045402100a044041d1030480c100d041e019080d904018400f4945d006890009000c1d00c0e00190b025064580300d60443c1044205110151645000ca410141c81c002e00700310501c007000b0782a001544140641c0c0700e0200151101c207050481401101d0741e00c07200c14501010442101c0c10385d408407001380da5040800350f01700c04800102c2e0440c1d100400a41c0e00c04400010400199094021000f0600c154a41303500c8941c03400c140c4a45903100071100503d5a62180c02080541d690290303424020342c0300410402c81d4a030154064900b8906501c500c07100360181c600009024500001c0c00381c8601d406840e40000c2c10428035000181400403c07506040c40010710011010a421885621805100d06880c964a0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 33422136 1250 33420886 33420889
    0xa020c0a050309100504060807050d1103010803070219080309060f160f06060e06060301121103030f1305030307030c08030c1c02040608060a0b1804060302040c020109030f26060102030909090c 84
    0x48102d130440300500004220402659600c99516640985a440c02a4803071840d40c503250040d0a8500d1280b060280100010075202130110040c002c582c0b0888a102520345444a40c12070901248103540c1a034005204c8292681020802015107002c401122850510400500b9141d81d01e100e5082c0d41300640050f8003420860076120740009440207131500a481d1420400140c024441401f901c40d0400c00c0e44030003020003000c040c00074001030000701a25181c918016280d451034008a07000c092580f01e050340000c075800c001c41100c0c0b40c1e46c0c16030748a00c4141981d0b120b08000782d002505954420804000e24641102d4070902158103200100000d40e54900d004001424850301811180c03080c016014104003000600c000c50300750640a4514600c551750400014000704000e900103034100703092040c5030b4aa681d0641c044010349100351035000072031110305422100034403007040e80e451070304005540741012040801c40035030007041403044038038200440000c640d004a00b030310303004280d80c412295150503 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 33423386 1250 33422136 33422149
    0x30912030b090a1a040207030507120f260103060e030d0603060203060f030d0c03030b03070b030c0a030c050c120904061e08060106020109020d0209070e0901180506180601080a020c0a050309 83
    0x70045480502c4020f0036410071000c13800e210041c480c400e07a400070b144010140250180c03079136541c100c00540402c41030940d01900340380554024000050302402005114582c00076003001441c2e0400c019142d60b820b55592a00408400002c04114841405101d10310400303400388a0203140304000158481c00c1400030321100c0641c0c010101d00c01d801c080e4061500b103901419805680d50146004955110500b01003810314070a074000e541d00220010030007802c0740c6424014502550242e0b010048513a00c11011a10b42c09650b4130040780d60030080d600480c2440d800060940510000c0c40042c140303940b04040324000528601000c140f03010365008004050f0705102460040441d4002030180c2e0849170b000987c0304042000017403144503202d02141450780700d0034405000501c060b0074a0007558440440010700001045522500c0d41400d0006010707040c071003400210850b606a440a0540710f50006441c9400000d08240700154280010328a80314200800e483d03850150000e183d441c0022010b0004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 33424636 1250 33423386 33423391
    0x1e051f0204031b06050d110408030a020a0b06040501030515070e0604080d020708032a01020405030a0b09071a0301030303020a0c230606060306030706120f02030123010c0c0b0a030912030b09 83
    0x1010841d2543c2081010f820070308071000035480c450300060306d46c2104400c88950003940c0241d100c034800455504820303a00001e281c0c102d41c0c0902144200783d641c031820081928000d010003445034000d24802c9002e082c80701d001340e401c0451030901100541256000c940d0980080d809200c003980400081c01c951901880004060182c3c000610f103071200310200e13080141e00314070450b014074101a07200007800c1c40a5056802a00c0c0080c1a94030b010704500b40305035032460507200074015000e00740000403128055030034030040389800f0241504507841c58909030000c1d04490300d41c80170f20088281c1c1000241440c40d100c8045040741640010302c000d40d185d528907003880100300501402c1b04005000340da5400085000403a0414a030556003401c45949c0030000e0008406840e402c0c60020002042c013580105405801c0c40d024203d040440c4600c500444554032403850141a04034480030500115803d400104580d5115040110701c0341190380d1600d50070012000c8000001703a90300101c3d000d40c0b41443c0300302d4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 33425886 1250 33424636 33424673
    0x507080402190b090618030303010902040f06030b030a020f010e0a031b05030606030a08030709030c030602070201260a0e0a0221060907140d02040f1a010305090102071e051f020403 79
    0x2000b42002c1d10001c65104e042001407092a012074041d15145800c028107911100243c1505c0e12540d46082ea40d010b90813500501e003039030071040e401042040c441c0c0325425140b5001802040100219024041d1140d503086406040082a20540e50161038600d0080700852090400c01c02c1304003242c1d04000c4aaa5941015119402c00c209001d80d642c2d00044410b83c0030b8001d0034040d07a0f51500ca1095401044c0c0d640010b10340d4582d12000800d01046501a202d618001e8903940c40505000400c1d1511801440c004802d403c99480801e1034001c1590090f14640700d028110303020b410403500003550814081d083d01d60201c400c20405c091b43e0106102141d04140d81d41b00800ca007904200d0a040d0215080407054050b00c16807507450199130302e9401031459071400b10420018a241c0030700040c03401c07400080e6580424240307800324030080c5051003140c2809400441c0c60aaa1403205c02d0400300b41c1c000c007802e0307406104a440c078840c11410303580842000b038102140103070380390714514002441c1d000035000007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 33427136 1250 33425886 33425929
    0x406140f060319020102070b0c03190306080105060a030f060f0b0d05010f0b1008010306110d14070329040509030f040806010609060201090308011701090b130b13020d030f02010b03010507080402 85
    0xf50050341c00007040000e6031001048240c5410581d81428618000c40c50380141800804c0e0464486a42646c0404192090400280b060f40ea074281409030420f03007880024030b142c2e40c188040b0702040d21075000044040003604081580c407200340004000c28000034058903241d6498200d04441d01d640d11841d0301a18060399845d449285502010303011000521019100580f110b610804620000c421540481c4007540d0410480c00f50310042d0001c22004c88442c0b000c40c0c030300705101c919100032341c06200130783c11a0411015401910818040a0301d40580404541c1c032082c420b0b0250204100003800281018a004107455850120020f0030b1500950041c0c080d64500010400030aa1058907241035462143c40e0708100e94004400d58018202001c000e0011540d8006104e140700484d201e43d070280d8000c840c444442e1300c8141d000307601e81c08828002580242941e40140020340280444041d80704207000000720714403440b002c00e0039070340201e07102400102c8810802c01107260014005007c48001c0d03441 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 33428386 1250 33427136 33427183
    0x30a0f1505030c012003030c031f080d0309020103090609080a020709150306050403020c030f07050a06030605030709051308070c051c0f02090615120105011106130201080406140f0603 80
    0xb0a03200d0b0f50401c4124100007180744c00c248000c101c1e0a5030411481781d5400c9070313502e01d000d00340b00006030410350310700e1080d5000810f1442c000304104612025500044040d002e60705d00140280c004111103c8101c1c185500c5030f1100300440c045200e40002d072070281180d159266040a0020308001d20381d080382810620f000d4aa245840c4082810740a0300d601c804001030700d0300c4a041c01d92510885d0030f0071652500c129809422600804200c0c1411031788140c0d40b40000c503481d80d07025410f403105400303803641580c020901007104000b1600a590030100b41c0b84008050146a1035000746988007030030680b080000d001040145003450003500444949098840c06800520b96403081801d040c200040d104842c0d0102240c0182c4d200080f22200c101106a817a03940c3c40e035120410803800d000d100b254049080c000303441d00e00b40350110b00c035840b443c002000000f245803140c0c010f40b007140700035009403000c580e00c0712414414120418105e019025640c0c1d820070341d1410307000f0581740554100c0b1051410311200030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 33429636 1250 33428386 33428389
    0xc09100f031211010509160b072a03050a0302030a08010f050907120e07061107050301110f0307050d020a020307060b060a0207061202090d0309090c08060f1c08030a0f1505 75
    0x3850050340d520803084400365004034812520184041d89054541d4603000900030030356030000744c6812402c4080544601c65036101c0b071201e01c80c00780c41c8010f460440c140d194541c1100080c2d044a404141c00d0300045c01140e140c3d00c031149000784103401280507070710000c0c3c1685610740103010240182510705210f481765060101040d900040a041c07001480b419141020411240b9000085050347c180100c402140d07417064018240d40d905241e04106000c1c0c007101040c141010300032800204410091140b80c003c4803610308a0a44c4010003c1040210030301c01c0041c0912240020140b0307501030340c002c0d41c83e8002d43c1080f00803100c04250041c07040341c0c100301c0030010607008074880e01120450700b00740400c1091442400c01071700c1804086c542c0000035050140806800841c1c0c003043e140c1251042000d0b0861650965031188252101e580c8445c074006400080c1c50100240d030640001c02c4042e40380c84045555080d000e40064079141501521000601c3d8001c10034802c10350684030700340c98409442e10b081c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 33430886 1250 33429636 33429659
    0x1060b0711030106170102040f05030c09040f030e130b03010f0c080105040b011b08040e0c0c06060d15060b0c0c0108010b03040201051e030106020c09010603090201080c0c100504050c0910 82
    0x100040c245000c410072401c1d41c1c1e50030b500c200010001c00744040340b41c4203040000ca001b584507001d04803000c0f0001902244078240000c0c0440000006091310302d0f01d440f5912070261452000c1c800302c04002014260120030b03101d4503028a4519400c0001003142e500a004040c2500c215414000100d4a854200f480c1c003640003120b0760440700180c5000580c42c5420b03004a4101205120140c030b4455010014410007404400400c12554640090b103442c3e269401c00311064401c0d08007640345944010b0100343c0c103140010300f44401c3e9105008184c2410651510f02d010f40b03200d68055001078a012603145101c000c2030200c44502c60f000d00c2c050040d0740c10405840c8403808003500103410400c012440c1c02030141307000410f2007202000849203882e0741e92948022750b1603004105c01401038040710000a031043c02070043c41140c2c2e505031503000d441c0d5221181c0b45034076004007442441c51300c0381e0303100060502d16620405000740d0040010300300040c41d08080c0248008060722400c012200c0d284100491441c05 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 33432136 1250 33430886 33430897
    0x9081b150c09030a03030506030109020406120201090512030901030f091e030e101d04020403080c06040c050d05030306040f0222081b03070603110f03011202030606030c010c031b0f080c01050901060b 87
    0x103040007e426150300000c2801428548030007900701d49000000320f074050901000001d201d100340d9441104a0325070007032184004400440080a80c0148070b205001c0d030090b084010800c01540300000c5544c03103901d0301040303e1a501c0c2261216602841004145544564010ac200c40240d5050949410386200101b81400307502d0124100108601c04440954031601102c006503003204400b52110f56500b10f6030389031a82a5411070311800c8070400002c030742c00c1c492010a2800d810070080d5045945203c00c1c40701420b208040c61943c15070800c01c1446407100d02c80a0604079203040f201070645810038050350b2034000d00c3c4103801046404041140c003980c0c2c00080c0c42c4191b5040d4a0046003403d18806007007443c0c0110001e140741e07407001000102d803960309240421030702802101100c1d990b0311034500f451707111100c017908a03002521448a820220340100e180c03c41941c510810282c136204c0075195814100b03c1c4910482d080840040c050105400900410340c100641200804c01c8510f0218001860701c100c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 33433386 1250 33432136 33432143
    0x12090103050c1201080303070e190306020a0c05191a010503060c370318031b11040603030809060a0c2c030703110111060f0a09081b150c09030a 63
    0x8590000d4108100780b010745006074000702d21403200f035841d022100c2d20382c0c00c2269080002411031402031001c2c40d0440198410801d052440c1070b0203070440d1120310280d807141b401b280602c06111615000941d040103106055051403800841c11442c5150012010300b1407442a8181d0310b00314010b100d640c2d004600c00c0d40000e0584c0200356500c90710005481e00320044255648426400511110000043c011107101d900d0190303801c0082c9502a580c0b02c584004080c000b400081003031041054404040b13040307841150143e81062000b010000008050720f1481d08210006440407043c000c0d401c00410245400c260405024003003408003404c014207848011041c807145949441203002d111200041d038841c012000340a58820710f81b40e0030908400101e69090b11300091541c200008a4000415030501523140d0300c4944150fa21031120301e502901d00440181d912040030408100310310101c60680380c001d07404801800349503102c030340400400640201903504501c010031000d0700a5078081038145500e6807 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 33434636 1250 33433386 33433391
    0x1002090a050f0112050106031506020a050d03050702010b04050108010f0e0d0e01050306060c19021504050d06020a02011112040c0501080103030507030c050f070f031205070f060b0d080403080703030e12090103 91
    0x42e00d000403128041c540808405080c0f4140c0081420380c0d2640000ea40c0c2070380d0010f10401250b860600300c2c0e85580c0d03034201401070381001d103034100c0161003a0400c0d40c21480c80d02c00070400c4100b8800050840d402a0b110003506e030342d942d10f08840540320b801402d140d516000003030000e50703610b01400b52100c6600c01e45c80341000000400a0101d1742c88005461051300c40d4801c0301c071088844900f8944580c2c082006900ca003da1382c000c8115a0703111720407107064440150189851003050b60b80d03074001c1c7d00180340080942d5200e03582c0711000c0c00d402c0f0142082c1d00071010038034002e040a0070041756106440d00301c1810000604018800710381c000c022030760301a51518100080c030f9000c1c10102d017403203101000c14003180224000050314401807840101a40d028940003018140c84a10540d41e9116031071004090340c04000045010a0040d03010a2114001600d00e17800e44001d9584e20351994000d82040700d038010007107882c605165042c45804000c00300080101044680190b007000d85000d0b91401c1d030304168 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 33435886 1250 33434636 33434659
    0x303010605160b090f010b040516050c03070b0c130b04140607020406051201020c06130308071d0303070305040e0916090207030207090906090203151015051308060105031002090a05 79
    0xe00204502c01065046400f10201c1e0428441aa4580030101e42c00350f499030078902e40358503034681846018042c80e2103203404124107404910950381da03004039044a10500040c03040d0741c040b445003d103081c03140c4080401e10b03644a400a07031503896007140e030b00300f1404164207110604c44070003100401204206c040712160b441d03004610016024109540280b0b40181c0c1e03130a00210b010005401504188110740f00780c81c0386a031440c0309458107554240014000600100125004a0003112508400c150b80b010403105100392002007071450740075a408400084d0300140c00c0150550355a151a040400903010700038258015850712240c0203980600000f00b940000d003682098002c21600c001440c102e0300a03c80054241400c0000301442c19080e030007401022003da1080b07000000f8070b03200d0013821218854550905016103401d50040300e5407400d000c8100207440c010480058050010900b002c0104415810070081c1804c01c03034407014105220340148081c41d072543c2c5040c0c111007660415500e0031143e0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 33437136 1250 33435886 33435907
    0x70b180102071a0a27060203060612040308011d090a021005040302130605090c0316120b120105070212040302030a1214030c0c0607050307080a051810060503010608030c0303010605 79
    0x240300310840188006281000c0041e0b99070f09181892268100040030024208419003010300303a4442c40c0d07103c0079030740d18034184030002d10170f580a190480c0010b45647d0800e00c1d00d1a0020080b2400e48081c0d0100706944010440d0b02105680d4114074000703800300b0f20480c02c00705c0c8519038880a18100901c5546004810321101d8482c8059030001d64004240c01502d0920701140d1004003294007a8500a40c0c01c13000242983c88a80110b070301405104400311004240c41c1800c40b80d00301d2026000410b280c0720030700500d096135009011840c20001d007000003078a042c20040a441c100c1e81c0c0c110b20033faa00050108002613134020480c030b003610390030010ba1090340c28440700c11070340003000c41d401c508480d40120920031541c0303200014024002c0320700704a514580700c0c804203407000d0000f01c43e04400240014006800004140c00c0a500072100b1003210070844441ca80c4181880400c41c00b04c13a0060761010100114502401048024905036020f507140c4982d0300c19407600c070b100500882003070020000e40074801 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 33438386 1250 33437136 33437141
    0x111090108131b17070501030212010902070f210e0f060409090615060507030f020601050a03060b0f04050a090201020105010e0717130807150f1506110f0f01061802070b1801 76
    0x201c0d40a03d1072a02d81d850305819001c8035100700001d601c40c030601d00301203031a501034401c03901c0140f801d408012541c0c2c80d24108401950240c5011070300010a07840980c00030300003941c00802c000100400000c5500c0440300241071041240d00390307104d04003c0941c0d2400b601c0300030481d0251500b02d8404542100181481c4001c1e0880702440c0000c94414003000940a80c814050903146100350344000c2ca03501414002c0340d80c1c10003800b4407540401030040800000e0426030044400800280c9150240c44038030000404030b0f2811078441c0300341620307002480210341e420322079a40504020007944140d421b0a4000402d0074030f8860320740d0042580d00c0c0115244001c1085003000080c0d11043d400da84e980e651801c2410400050700c44152076060418a80c80e100c080d00a05202c1012a0a803441c0e461511004807066400c8040070b8106010300b03035409050314024050008580d0304c5400208445190003151552440c1c8401084401481030002c980002d03400d600b03094000306503e801921351030300ca000c034500 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 33439636 1250 33438386 33438413
    0x90213031a07020d0201050c16030315061d030105090c010305070908060c0d1a0312132103081303050301050103110c0a050601090b04090203070b0a0302070c0603020c011109010813 79
    0x294241d91098028000745180c6105480640c25240244003403542603090394404d0b100580b080c4403e0009000000f00e81d4462054980685408644100a144d440c0410b11040c1c0000d80011346c00c41034180008106000c0d140b9130301058008100c01c0c5000d5038441c0d00c4004408105040546440202c1c040c81c1c4140381e020040c0c154007043d6a01303814807461740f00b6181c0c4400c120690403801c150a202816190715890741222902402802590010380e140390400d511000004c0301c002d41000c0702040c603100c1c40c0c0800803c0c038407180c1c0d4041d00d01e01030b04028100c45001810f122288520121580c0020351040c01d503411600282000310380010260004501405202d80c0c3c503000380f041d0700d001e100340400000e409040742c0c1071100812410600d02c080c0810340c3d080c4030010790560300100301002030602100c020071a10942d49001424002e0aa0700d0440d0803903594480e8000a4011480b4205103100303105200303001c0704d190002858440311200103030400000804040908004280722406e00c200e4051144 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 33440886 1250 33439636 33439643
    0x513021002010507080a0c050a081909030c021c0c0e070c120201050402091605040303080a0207050f06040c060c020d08030a0e03040603060812030915040c05040f020306180403080109021303 83
    0xc00110903031100038001c040c1258207400007140c2c1c001007000d50045206d26843ea428a0f07031100e00c0c02c031410105483c4940041e10701d01d40902e16845940114540c0c1c03080c1c000462007552522510801401004180c03070103010b4a000b01c800c6002d80c2e10001d5880c4070a1401c0390b0001a00841a50700c000381603c6503031807408094401e2180f1f400f03e0248640c19804280300c3d52003114801120b4031008071060001307204003020004075404010501c013090040105d07551100d101c0201510702200341e9241804c0800c54580121707240d1240b1700344400c021036414504050040351800c035000740e0480c1c0006510711010240602003580000101e0800d601e50b4005106003080f02040741c0da150380d62039005000f440030344110046400f03401c3c50b880c00003d01300210fa015100040003007110048484070091030100150085030940c90209002400d0b84070b500805101006803000107071a441d02e8801e00910a0303020042c0b036a20f800c14000c01c07000907000203071241940c20b000801a10340e44031301200c4080716540d4201a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 33442136 1250 33440886 33440899
    0xc02030d1106070207051309020d020a1e0e0411120a0c030809010e0906061e0c1605040608160306020f0c030c0304061103030f040308071e0804030207080d050706051302 74
    0x4101560300465a9a0702a0540049a01d140d40c2d1400032602c0b50440d0240e140e021100c000c81c514070b54a03e03045103402c240000d001100e4405607a0014502c180c0760b030b108444079002c2c060032100b00704a510b00d1100030414030840c81c4540c5415556030203100b0340d41411610031545110005c9108004101800c2d00a80c85500c050207180c4a043c07000050300a035003e2400035070140c0c010b445500340f000280d030003088c014040a0804406500b054283e0312038030101c405080c0c00340465500c04d4001c0114010145090200c0e5000c1800c010501c01070391072981151030641c0c0141c00700c462062100031240100c98003c0d01c0140c44415942c01540c00d440346c80402082c80c0701c08584004010b0000c00204112041074480b9070400955070041c54890101b1248130390b008107420006004a401031b41250360003826441c10b11001c0c00404d800b90301848c1080310a100141700755040208058040011a0242c0080d0004101e409030000d4005c0844c4a04c0c0d0005040300d8440c408149900f40c0b100c0070240c400d5004008 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 33443386 1250 33442136 33442153
    0x50607030e090a0207020901050609010c02090f09070e0108030a030e0712110f0a050904140c13050411010206090d030207060e010204080303100b030f0a1d010515040f02040e06010c030c0203 83
    0x24040007008034614420b01c0e050000c11041e0242e0b208036034031141d014000347c00c1230303203007004114194100c0d07040241401848a01074005903512104944030b400030504c0383c00c10303003043c0117020301d401b030700d43c000e2110015034000500015100105036901c110741403801245844045014500f0801c966101c5804480e05030420800c01030090f040303030844071f001d59040c46c440105008104c015191071191503005404003005c0b8000c10600c240b84110030a045080326002030390306020540e4079500c540390395010759aa4013844100108520780102c10300007407000301068100600e080c0c0e150a0b81a0804052682c0050b0341c0d4204990780d040101c8592244c4000c548441d43c0d400c800344c0366881214004a090880340d8081323a032111420a07640100c82d0f08580100c150745140d0a1801840d480300050003110441030201c164100074010203100c0c40d8451041143c501c56030051000b900e03000d081003903c803070050005110b40044101c1c80c0e039000b0b0091074040124070041c101507643c4608824042e4040c01400300 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 33444636 1250 33443386 33443393
    0x41110030905100c0e0105180a0e0106020c0d020a06030b1f0807090b192a030914010206061005031008010507020703020f010e030a060f02040b070b06010306060f1b0c050607 76
    0x1c0c48456014105903210307240409961412500800318210118504130032001017948600050000950030760400510402c0b0071000600984459000c002000b0710440144038081c1d0600c0102504042a03808404004640c1d002503c1120b01f401400101691030740c1000482e41e03901c0101c1c040a000000002942000c1540105032541c1241d0b844007040fa0f4a03000201050160b04a485c0d01140c5149084601070411049807103180c1050740d40821407016040d40192100340305591541e42c840c1d07c842da120b62400d00480d800c003140c0200c40c2e040d50480410401e480e1a06074064208800c40e2402b550b1fa41d5503540c410051900b503410403200c0750b2a207000c001e0312580008456058a00894a01007584080710045601110b6054410303050340029034550000350300b50f002120440d00700280503007030941b9400072850503080000705503100910f0401b0700c0010750705407003014042d1070140b5048005420003040900741c1000f0320030f2180c000e00305450766002d00c000c1e0140c10018040c0280041d03540c121504 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 33445886 1250 33444636 33444641
    0x30b040606050109050a030c0905060607060e0d030506010905030721050a050705150a0e010807090803070f0b0105040504080f0702030102040f180c0816050903011b05070b010801060b030f04111003 86
    0x203154049245290085190310b8440d80b040b003102c0d445400c1f260581d00b4158103c9c042e00e005040660000c1003032100303100054403801180400302001c0300601c0744810f001002000d44202500d190b041c080740307080030b2095440c0420404255000c070040c416004d407030340500c0050490725400180142c0588001c0c0c4040000200716041194000c442101c040301c40f807801c20100e44140c0050b4008981c80325001a480c0d40503010555100c0ca4908098000d2a41c8500150840c3e000d40302c11030719100d09205903000c014201501c54054101654200301a20f0555100c00c0741d0b1151101810030040041a004110340c0e094044030007030300003018040000e598a0034080e4004103000c1000d101641003440e4a48050700c17404126101d42c3c04403070121515449a082a0344542c01090119015501c1e08210140f00b0b116200e030034102c0702550f6459540d0301b0b090400400d420010b030060115641040300030130140418100b80c0341c05c82014501503100b40c803a45014a4081c01c40c1c1404c541003541c1a02034400c2030b0f05075 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 33447136 1250 33445886 33445889
    0x90607020d0b0a230f0601020a060606030b13020c0a080d020d09030c11030a02091906170604020117090303040303230c030601030c092409081c1101090201090e060109030b040606 78
    0x28101440003142100380741340703122034545480882c0c40105000461240352512141d420007018010b68064010075141c0005880b5650055070100f92609940c0c130036030800040d042e01c40c0220f00e400f1030411000355000d0742c4444070842c0c0a4038550740401c8a50703160400d030b412901b000c1260041007241c04034500d006400590b01520644d031007412102d078030b14a0304021485030340840d8010500d4000341e8030740101094814203200740c808440d54410020a1203d4071400b41c18020900340e0080005107000c0c40014001e01d0040d00c800c2040c0042000d000320b9010010a6030b40295142c18046088204461407941d6010b4030003500001007108000c0c40b02c480d23070010040d40286020791f0305101c1440343c0070b000c0d10b4540c0ca6202d55a001c1442942c1300040b001080c10b1210038450b00d1070814001aa034903000c500d846442c00501150000712104035240c281c112800039030303ea2946001313204005007900040c1041382c440c8114403000c1c215400088c3c4aa11400c00c94000d5540000800e610f0b003080c0c01c0c00ea0042845 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 33448386 1250 33447136 33447151
    0xa17030601120213030204111201090203070e03010204090504050f030703170c0c010c0903060b1503010e1003140303160f0c1104060803040e06030606240c12040b030f0a0204050a0b090607020d0b 85
    0x142920f102040d1492230440d090512070600d265001e03480e1140c010025480105020100080c070500c298243c0e1f02800140001c0025280204a13401e02e400c0c05420624800000b074145d500070010080002c0d00007000b00038800d00c0140124540d034a550000c002d51044041c604400c0d40707002400283c041d00600e0450030b4a01645007000912600c4050002500d03111400c18403094003440104005072003034805030b611a0400702c402302066901e9440c1d00b07080340c0c0d10303d940d4045d41010003080300301461304999a500007031902e0050500702007080701601040148a000d030095035641c1c086070094955070408002441c4142c1101d5443d40c2e0b50585801c00074095074a00c1c4030340184c1001c28a00c1ca000f039100c0020b540600705003007107110394420b041010b50001200702041c1c05040c43c100c0e01c01103c40301410003018103a0203690baa00d40101c0c20107001400500400c0e181c1d01c1400140300c2501c0d000203040668903803281c120b40d140c2504d4001165801410b100a511118503200c0c6020045490300b1540604903 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 33449636 1250 33448386 33448391
    0xb030a020c0c030111040504090614090601030308060105090d0f0c0b0c010e070806060924100f080a0c05030712020f040303030603050706080103030e0f010e0306041b080a17030601120213030204 85
    0xb0000d082600b80c0380f508010500ca403506010074046442c085c2d1180101c00d215450000c4d0020103541d96060401c1d04980c0319407150000d00041040c11380002403035a01140920b0714a03c0c0901d16800118140b4143c0c1c0080d00751a94607400300c0c10017401d602803c010300000c0da2801d4032075a849800c9400707030440ca410000140103000c00000c1e142000a90140141e000828020aa941d1240b11052811411119103501c600c09030421126494525184490001540d9011441a18070307102038003900c005064240210700e0045846800ca82c0171060b81e0708500c1c1860003104144604a040c000b0307004400b41b00f1940c40f4001000010541c265101d10100c0384510251111240d031048191a00c840904c00600841d07200204110325160a07400c05445880504100440e01030030404689400f02c00c8504490103012200580e10324880904910700401120303000348501942a034a52042107044020010024030110100303440e82c2c001c0c840f982c00403480d440e00711745510001020030840805072100764080d61 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 33450886 1250 33449636 33449653
    0x61d0601080708070b030f070c08040b030708061507030f050a0c0605090d031401060e04020901090b160204060f14040e19030203070b010608131b050613050906060307081506040b030a020c 82
    0x92681741a00d00c6502020130130204c50340c070848140c41c0c443c1c50181c100c0702201c01704000301d4255540005140030b000c0594412005140000c00c1c4a05a1004944401c54075000d204181c0007982c410042c4181200c0d030301c1c0017a11006085402c0d00e5001c1210320003403207242003908104010400103158951518240e90a0142c10340d4801c901c08202001e01034880018404a5805254103080d001008800d0041c035210317440c255a00540f0140d900140600b40004060074507000079442d00303015920140c1309050741c2d030008629009032480d80c00409281c0a00031615110403540d12541807181c2181c3c4251200c4e01c60f810001440e0080d100e60241c40100c621141c0880037149440c842c25050b403103280c10f080000b01003100c580300c061004042c0c20f82c1c803070351914201c0c01207181d0311440054510306030134500340d9440e182040100401f0901c0144140e006407014010010f0044d8072000c05c640240700e03207038403c148050402c00304000744502e422072901e0b40c0c1c00109001c01402d05500600d0b803841c014060785c91a4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 33452136 1250 33450886 33450899
    0xb070501050606040501140c030d0212180c130506030f0d11010c090b0a03020331061103040804050d050304030221010b0d020a0b0a020a0519030f030501080307061d060108070807 78
    0x84c001e600a20740004c0c0000c000c0079542611200500c088030080d41200c0c2040c846100041c141c1c1d202c54024075415080c4000c0c40442c02601d0319000c2c0c7c042991000c1c1c8403403407281e80490b4003041e84542c066020f44d1030789c01040c0d9540342400b2030326030009c2083c01c9e100a040a640e001d4890b001c0d041c0054010341c03030b0000b0b01d10480e21a40c171f0300c0c041c0d4aa155196180058220046001c0c3d000a44a200b88101c00c207000340c0e06d500d52164901c0841410501c1c00240046810400121150300e0134150f4003050420401c0300080c03170042110b0a8500031680300d184040242407140c0345004c4c64100940000b0a0b0b282803003221052110381841c0074480000b441042589424000e5032072300400c0003500300c003403c2000c4c42101e01110103010030310203510444a15048030b8403580d15029030401d00500e01e8802c3c80301c0e24141603010300d030450242c046060034400d5524107044a980c07486182e1020b0041903540000103264a1544100304029184a00311890341d42c484006a868114520400b03825218200f00080c89 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 33453242 1106 33452136 33452149
    0x907080106020709050108030a0c03210506090601030e0a021201090b011706010609080a030503070504030213060510030b031b06090a031202060705070f0f03050d060b0705010506 78
    0x200e5140100c003074103240054201d10109802c0c40e005100c031030b174008100c41d00220546080d071403a1210741004c44400140c43c050405c204009180081d120f1840d404c407500480085a4400e0a512444015422105040300020140e000080c8035005441c0c01001c146826603104000b040c3c130350140d0754a1241d038101360040c1c010112141d034005100302003040405c0c00b401103070030800c003036908120700e05550300c11b8000300a041000000010314280d2090f425a0011070b40500855448101310707058602a124501409000b0b14040e01010580d80c0b10b80034248800700054040c043c10900311203038104c040840980c99800c81c4d000c100ba10340039102c10680c0d100131401040020101340403000000d00380075000c1c11140400005015031004070300e0140c0400031042d400400038440e071206280c2900c2c54002c905201c20b95a1800e80002081840031004010240c8914000c01883c0d43d608100182c = true := by decide +kernel

theorem cover : BRFrame.Cov 33273386 33453242 := by
  have h0 := BRFrame.cov_init 33273386
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33273386 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 33273386 ≤ n) (h2 : n < 33453242) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
