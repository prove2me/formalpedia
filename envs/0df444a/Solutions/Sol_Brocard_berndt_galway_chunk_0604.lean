-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0604
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:41:31.995978+00:00
-- url     : https://prove2.me/submissions/96bf35c4-c641-4b8e-823d-c8af103d8af8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 108453237 ≤ n < 108633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 108454487 1250 108453237 108453259
    0xf0106020d030204060507021e0d080408010e032106030f150a05010b181504050409060204030519080a0810170106150e01020601181508070603050a06030203060402010f020304081902 80
    0x1e442482100c2c141c900740d0300e41c282040c50350340a0100e5007805110713040c1d07140074000c500055a030321003000b00404d80c814401241e03600d06081d1340300c0c2920240179400c60310342d00c240140c00e810305580a6407190003c80c20414400b6960f0702c00028902a4482010261800f4420403903810082d0011203070f1003001e6183d400c1c4241e0360380d14455041485246403010050043c1144001c182c07130b00f0b0000740c1100d842c00041a041c652038000140894840361012144a58009030030410043c0501c02000498440901c0c401c803c1080e0b01c03999001c3c41070f0003041c010032820b80e0024803111008120040078000700300203c040700342202d900c64000c080501810100807000d130301b6120403502c0b60080c0d04043e48180d000e0403a9900c0e00485401c80701a90484100058440c488c034049242c031000c05500401c1c002004220300c61900e40c020b41100c4014207180202c0303050690600c09a1400130700b190300036074207290404100540407000c9085004079002002d8600902c4030200b091065940d40c55901d03070003110f15620310 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 108455737 1250 108454487 108454513
    0x5070e090f1501060c03080901110c0705091506070602090d08121b04050a18090501140f070e060403032006010906030507150212181807080610090b090d0b0f010602 72
    0xca070b00344607800020300c02c0e00d14440004e215513480e54002c4040c40c008114408400900d10345a01b1498143c2c0c16540105000c0041d8604070458a410880c0c092a003002050804003240e140d11900c5000b03040300b500000c0d190100e4495480c07281046411040440c0c562034074200041c07001078195080d10303030b12070703114640c0710105402c1086804a400080240901c0b43c6000c08001c1c03c0d244011804115039554072541d00866000c0c0030b8001d100490354214000e920340181d640106110240000041001080c2510754a8803010704560599801d8105a2203010528440301c012614545581e0714901940d00001400d4800380c0245007664801c409030b410568480058000d80c001c00b814cc0350040e840f28507900d90105881c0014040c0b07594070405440c1c1807403102e01041c03650419400fa8410040c0500401c0b0045034815902900040111041000101c10b00350080480f246401042e01c02140000c44070801e948078181c10b500c0c2640516040f92030310f0900600030b02030409208441c050b000d200340404c80 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 108456987 1250 108455737 108455773
    0x9030d030b10180f0909230712050309040e070807090e0703020918032d0c07030b22050102030f060a080a17040803161401060f1205070e090f 62
    0x940c80002c0d00340d04298803410b00c120381120943c11243e0511a15600108003824103e0400d40500701450000c11114400c1c5401c800079854088011000082800425035410300881d01001f1280d5802c11842e0b95220360030414154401c02098035400352411008112401002c90b5a50850740000c1c15103100c0c55491155006075900d4000016803a0843c9409000502d40300340c002e1b800c915a503416140707100c50b03e2441440c603407021000d2402d83d0160a140c1c03503205522508a071068984980d09414810a00311142d45c1e41382c070f80001807000c04130400058202c0b84024608010101c91100003a00110f10701b0030034002e500660b10194400a0703140091003c0c2481c400b0102183c440c2001010b601400307031590003080031912604203142e0401c01001400807003c00182c035981941e5070311141e0700e16071840e00d4000b02c0d006c0503054401e0f0341800007c02a019034200c041d412210484000e0000c5100c61500d1030030f1003a40d4115440505031202070120302c580015101c000d03810114101c498603034880010460f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 108458237 1250 108456987 108457001
    0xa12030f0b010503010506210403081b04030201050706110f0406090e0705090a030b040f020d060c0e1504060e2e09090207080304030f1707020a05060f0108060711030f030c09030d03 79
    0x2c08035104100401036400c29600814008510110b914240d0032410b01c0c00c40201c405450680000b0110000d06c10030078801c4218030302c041403048106240a285900180c024083d010016045582e0b4801803c0b19209800c2243c41c1226251890740d5910784440f40900300d48114080c555407000d00f20001009240142c089410140c0000c2c03406c52054510396881d07602ca034004100b00d03400e48100e4041c8006855000d401480d6078880c040c0451104801701006140002c944802c600c2850201c3c40640c55001440c11102928a1840e0038100424448041400c4000078003d40480b00120b0040604090001200648103280f41e6900d07585182e81d41d00000603030044c0c800161656004001090029001d402001c20002c0c142c00c20454004c602e6110541ca02011284840560014080003007085000e01800e68801c0c81042c00300c1d41541000d109680d1284000d100c0c3c0140402d540c45025010010019114040e04030b40e1095528540341411043c01c0d003001030024000d11641900201140c008e0040d61 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 108459487 1250 108458237 108458239
    0x1050303040b07030210060312020d02060f060d0f020312040608010b07120c020f0901260102070b01030f0c080303070201020d0f090b040b0a020706090602220602100507050c0a12030f0b 81
    0x181000d0401c00d04012070307408014200d095215600004041b041c950049100441c0035484445400a140308084c2c1070903220101c0000315009502000090314070105110742190742a0340e403000d911004c4c071308408103601c581d001a6061003802c4d51a4040280e81d0000d0096503001c0c0d0302c60050340d030784045400850003034000041c030f0b000081045040d0386120f4142412801d0004044501c04143d0101003040c54500303070018403200005080315203d142003810540b04800300b250085203860590b45030842014010300004090103400c50032117003881441c0401601618258007a25600d0030400d40c068006d52020103d10002c0e801c112a60703400340d90394401d990715039811010100241d039455603949003c1000900c11025280d00f8040c1d003001c1781103881040d040910072140142c0d0364203410907000034002803851410082c500c04105025142c3d002c6a4040c65000840010a103502c84ca0019603450041c401522180d21a80500740d0900818002140b01e000164034104202d40541600000391a1055051 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 108460737 1250 108459487 108459493
    0xb0c0a0f0f050f1303020d030903050717120a02010212010807060e010c12030b011101020c0601032a090e030403020411130602030f0417010902150322020d0b100f0f030501060905010503 81
    0x850600d2a007070f009002c004001d41503030142c607072264001041507014060540004858250500c20040100141c2014102903903407070525000b50781c40b965a540c0f85010b40b807801c103804204050898000d405a49441c501d50282e040c5941c0c4070034095031788031683d11403840010100442900c140d40107641140155810183d020310640100030103402802d504c1c40010b04000d08011210030009080c8003400707a84180002030900f031f5266041520f0b04100c41540f0428000c0900b43d04041e03515078030030340012640003a20100b403048100b5440c9044d40595030002c3c1d042414204441e960a80140c000e000c1d42c441c000642d1301d0b80c0d8a8405c22603483c0140c5010401201e020801070086500f100c09a124070340c0008008a405511039000c541040004020050600710101c01e00400c600080008400d0b40308501c42a41c1407000d90700003c0c01c0e00c46c21003018190442040104d40380700f480d030f10b2001c050103462040c1d001160381e035182000080050312054615510b0810082601c0380744c0d00505040311002002 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 108461987 1250 108460737 108460747
    0x504050a05060609060a1e0807080f071706040b04060e061306050f040302070513020c01020d0605010f0206060913060213030809010e0301050408040302010f05041a0405010306050904150c0c0b0c0a0f0f05 89
    0x15081081010f13100c2007c0310b211419000486220401c4041c0c0917040c100050084024007031081c5180000e00e40142260352204a07120241d0000056801e600c150824418070064880e401d0010081100c0e954491041c047e010800441d001764a0242202d1842618100916035a81c0b08580c00d02c503080d1070050050700003200c104000d14015444040c20280c0083c0180385c20025010a800ca80c845240080082c0e1140c03410001581c001d50850f1906036540050500c0b45000d034001400518014a4880740346c2c145581a018020f90b941034943d2868401110044e5a481c2c4c148500c00b41c0200290a000800d0007003182a103081c107004850160f54040075141c02c00e4110341c0151420b41000e06480f08004042c400010541c003240303035805c4501c40034800380ba40c681c1880c1c001416a01540c1006026024000034000060f280030104281c24088120000343c01400010484002d00b84203805451020f166043c0142105408000c110401e0181c030b902d1003011b00c5034001d485000c21100581c01040302400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 108463237 1250 108461987 108461999
    0x250806010e040b0306010302040f0e032a030a0503011203050c030309060f0c0903060c07290a0c0e09040201030915020a0908070602151501020a14010905060106030204081209040902040504050a05060609060a 90
    0x41041c0c40ae2140e040441c01500e95402989140c12040020802000d01c2001144428107292441012802007003d5031500c1800000500309202c188941e03083c40c954140030340c0501d4800c0059862212600301580c1e46da00344040705030f58420047c0c4841c00c0190450b00410040150360084030011080903000d8a040c0e035541c9501a4541c10200041c1c41035200c4080c600c00c4c0e0300204250080c1c44055804510321800c00d0604401142c98100301e01e400e101c042206240d00c0d2360741550444c0c2c440c1d42460040b44038a207074901006c80c880754a0a0b016414004a200003501da00244403070181d441100444070b5aa60b154000c9940307802c41032103023a44140e01400b003081c0030310500180d904d2000c10b00480300c0320b0704c090746c524843c0161140743e0f82c030036550f40e6580341c2045001e00102e401403c1c58a800e500303003400c2920894680c0003043c820725811000003152202500e45402440501c0e40007081003000e4a03107801c216490b9207416204540070302400c00090028035161016600800e805058820b800341000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 108464487 1250 108463237 108463241
    0x62a0f09040903020d020c040216080d0f180302010e0a020907260406020c21090d03020f030c0102130905010f0e040614180d0e030a0803250806010e040b030601030204 73
    0x10554190148100304103003058031940034501c0310912941c010b1403074424041c4020b00b0100000380e1140f00364010440c54034907510b49040303240001d800c400891b80d500d2007061160001c00c00007540700001c0f4180340d48103ca11003400c00c1c4c074a00c03e0003a0024014201851001515215401c0f03000354000310040202d91310b14440c1c101140201c0c0e81c640840b0a0481d00140ea0140c4441290704645040d0001901400d8600901103040311001c128402e03a0184042c0c66140d1007801040707100f03800384184002804c241031007009948640300484058076a07840c0c0614240c1d010350710100c20144444090075000852100c0c901c102e5048400c07201d03080a01d18201b80601c0f030050005882071b95819100c1c40249180428415020302410b03a0162190045004014607814148080703150002d0003862800c5406c6a20b000c1244a42c3e50392080c050382e560341d00d640782c000c0c00b02241d080d00c5125085d02881c10b0b00032600b1441c2c460103810309803140d02d07011102504100035100c0126541c0d4160300500010801803c041d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 108465737 1250 108464487 108464497
    0x2070203030c01062c06030601060e01020123040212031305010f090b0a0c0b060a03110d030908060f04052a090406110d0203010306200a0c03140706020c062a 69
    0x50036645408030901d10b90f801d4803a6504842c04e80401503185d120009242d007544041100e0315003210740c0c07510344403001035100d01051203007c050040041c030500d0203030303c00e40c000850718041c50003184600304072100d500d2560000315012400f600c00300440307505001000051318800d100700b203058040c00b0309040044420051205482081c0301d40c01d0004101000c0309005400e0110060b9107800644480b810030702108034003d4000c0c3d00802001c0b5041c00410400c0d000801c1e554000d54000d00b00000314541250b4100407a4041030b458042c007028003c031f40c0241031145001e58020001c98018030f002c59641300125059840015088800106d0380a0314109180603a5015004070400039110300021410310141d408080180e400650000050041014030b04c82c10030240f0313112165402a607000084180103215101d0090144140c3c0d049100800d8400c80381c101d08042c00480c140e031180618541a8081d41059112440314002c06001032000c151614a00800500c207120802c2000404c0740e030302d4199841 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 108466987 1250 108465737 108465739
    0xe0703090507120302071a0d0b0609010c020d1b03080a0201061e0e0a150602030d0e0105010e040209090709140f090f030d0b010201060807080a0c0911090f06070f0501051605120703020702 82
    0x910b1400a4803062030481f06075030788034010344240d40d0703c644c64001d03040710010b520040c811041806001001d0760f200c000080c4003035043d03030712812042082c100030903003074400f001220030311035208000310420005102074865800c0b02c2c1c000b8440c20781c031080b0b080d41402d9141565240420345600401c9400741c9100029040000d44c0300014000c4200c151802504210780c0000015034070000e241c0c21b8440081c8a03104c6540030610003040b0b10b50400c0d1a01300d18041c007510292042c20040c0c00b044030203109204d518001d1034000c0b0200590414007800045e00750b811142c00744880c0d102c400290050030003250403c032480d40b00c4041c43c9400707407186500c1c004142d252007160466680c0c602c04208100f080000380090000c050007030224201601c3c1010961405820102d207207810681c545000c0d41d54031050750b40c4800201c40991258081c440130652500486001814681030b41e8182c600b484010750050340903c03000c50108204610f01041541c60f80310f44114021b0700c12140780007507251803080d03001c0c003c8944 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 108468237 1250 108466987 108466993
    0xf1d15060d0f0e061e010f0603020a020304080109300c0305130302120601090c0f0c020105160b0f0624040504050c070215030603010c0c030813110303070c0e0703090507120302 77
    0x1034855210801c0343c0400344010501d512981c244101d030380700c02c0618002100d40000400392581012101c01d0566060301c901e205142c0c010031000243c500030320548010f00307462030080143c0303c420304003121001c4548801d1100400001905035034404d10140012881089850310703861a0115601102d11341e0024118000c01d40c80c6600220050ba2070317110100420521030028001035040c100e8400031502c403008058140103082c0010340c002034001280c082c00580900308142c0390380700c0414641a202d00714100400c0707091a5010002c2001e0000440c60140e042602c1240c101004945000085040b0b030f24008208001403000304841d1519801050380240c50f07002d41d07800c280c2e26074041915071441e41c10f00b10201501004005043c1424418aa440d0b40240b40c0b40d0038400c1581c030302804000d03015100e49211a00c2202c4030b420302140c1000d40d04443d030082c00706c2c0d64401d100d0514040680b0309000d1604880c40702c0000c12002846070050842c0146c02001411007103107008103801e5000c1c5030400440940c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 108469487 1250 108468237 108468251
    0xb030c1c0b040c031b020105060d060f060b030a1b140d0207021203190f020d0c060b0301271704150503070216030606051903170c01020708040f1d15060d 67
    0x911070f40a03800d9a100c880d203020580e4400b24100c0d0320000f031240c2404013168500f40070011380b0344d03408101c0c400c1690054000940361003412404400350005400001454900209001121610307903c00c07440304c8059940b00d0101c01070304504680311481c030404008c403071000b405586c000803580d500800626200410845069120071180390640c0c00c114184108000c0305e00078403404640003100420340c15100e101409044083d103001030081640c0700c0b0040c0c01d50340ea4521099464500b580700f000c81e44440001141c801e409140c140c054040268000c89810200724146800303480e19030300741d405840035000000504560f2050480d03440c0c1004120340110710814102003a030b250400c03403500156000c2d0501261050801e020721074032444400c218140700c86420300c104080b901d0302c0c1165424050002503039981c0c03004403000ca4068000c40030007602011002030000f0305c500540101604550380d0351140354450040703c60300004c084c82181d200c540c614140d070300041607152060007030161580100e0001415 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 108470737 1250 108469487 108469489
    0x1005010801090f15170609060402030303070f0e030a050616050304020a030803060114040905010609080d23040812090123030705090a0e09010c140406020a020d06060b0d06030c0b030c1c0b 82
    0x313240941c40704000c41100e04062000220610166a004031204d00400c51411300d640801d0b580d200003030207181000601c3c01c90204840c46103890301c0003514010111016040181010fa23282e100640d80740f0718a10502000e04603082c0104240d910071078005028401e0b540c81d540354100c096100500c100d0420180031441e8000382910b10150000d4400d6030030000d40d541c100300e0058142e0406030000d036043d5001c44808051b850340041c140c0c10000e50b4220100d00b0054001c0b203103166010b00e421034610b5016003034114901d04002c101038040014240d03100b100c446084002d111030004480400042c6880c10800a12503901503c001d2406040280c0a01d20090f40e4402d10809100c003603d0083c182d07512074031900c848035800b84c0c2a841e401c00b01192545400e11b0900040e55880032448002d00840c0b140f0144814403040c2c1c3e20000c0284401030320f0641e207056405121004102c0c0d0f0204071008250842e010401c0c0210b18140e80c071490050341c0f0189018101204401c5c0310810340580c0080d961160404a02 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 108471987 1250 108470737 108470771
    0x106091d1e01090605011d0603040f150c020c09070c08040303030209010203160b041704050f040b03010f022a03130618080d0302090f090702031e09040507080f1005010801090f 77
    0xa1603c40701c0014080e0800700018542041144150b15610201c2c05a545a80c2d4030800c03660851350122680c2517a191a2428106d03a5280c03ca60310101d074540b446414400c0d8011900e0403040750103c0c0e15100301d0351408420341e1000c041403000740203403800b4803041c00000c0c0243d0043c02d10005c14011203051414600f081c0508800d940011150b5440300d0701032100300040000002c49840c014407504e41000d003041d000c1340c030510100c052584a00c0d143c0c5c803a480320b13031002c0d84001038a00d03091005560381c420040e0514030a141002000c0038010300c0040001807000080151180400d00290340041d0b1464a2821110f803420802e1035105000d01c41c0002510500811456494660980300541c81d8180e403420050941009180f581c0500508020005001c0e8084101c400307401308041030b1410704855014a0a0074012140284c5e041440c203000d102808da008001203102d5210b107140800103540d0800c170b020100031288181400b20320030700010f10a1101c076030000211441c8159000805100b100f000f03c907 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 108473237 1250 108471987 108471989
    0x18120d12091e030f02010902031f1409070806010e040218060303090405190b1504060f0908070306050406051302010f0e0d05031605010b0306010807050f040605090a0c080106091d1e01 80
    0x5030405075488070b04105a00102c0d15411810b40340000c0101d040703e07401080d26040c0b415412400040c00b5080801011079951201400d0070701d8003001401490001040743d511512030080c01e050f48184000015502d1301030718500d12607139029000e0046c04049800b800c0c3c0780e200c043e2460707505002c00c0c002a5090b45032480f41c0391041020320a0400500780c0c040ca11001c031541140140d005160b00c80711039803440c41d40001c44040711450310341b5407820390309a00219404906500400828081c44a001040c0140c41d04242c1c00790380a46800c10041d100d20051900c00041d610000f07000c5906003c0d407120b06401501224410000640a00c0d5102102d0b500c03282075601400c40d5410b0f03400d00c6020442845000d2055540c0f1030800d03401480300d9410032034086da481260744505440b0b5641c10403090655100c07600000c0040c03a0203401c0c090740e41010140d80014100c0c100f60702c0002000c41000258071885205910202d03a09600d104101e06e080041714400d92000800032192840c1e440d80011240c1100c503c618 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 108474487 1250 108473237 108473273
    0x903020604020907050c071e05130b03060c04211b0608100501090e0a0c09031406070e03030a0e01080915040812010f0e070309050a02031218120d1209 66
    0x503915003841007000e035250240c5850108103080c00030001d802000520031080e05d19500c0b2204401c0f170070041a0303207030b4096034000c1500100e00c1c00070a0104000d41d00f185441400071016540c095a88070322044442c010f07449181024040501030012409142c410500c66500421031080310b10000742404003d001c140c1c0c081c2d070014450104001c40014001d541102401d02440e01d442c2807858034a10003c10386025001d0803150b81c2e261001c003115270260910400850b80181001c160b0b9841c80c3c400c03515600219403a6020401e00381e03002040745000b00496103456225180c0044e034003110b000441d02d10500503d10358151280d40300c011170022081401500c00c5118000c1c16580c0d50312911100442001a0710500c21540c5400003406841150350321282c1c030080625001540741c2141c10101e19114a80070041d425000747d008014944c40448010440481c12072034581b40d41221100b48000c5800314801000c664205140842c00745101c1c0c503864280c0c04001e400401d841c2c0351031b01e4400006c4103e02c106 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 108475737 1250 108474487 108474493
    0x60a031d0f1504020307031712010605040501120605060d0c12060312020d0302180609011e030c11070513020c07030803090a0b01090b010c060e030c06011508010e0c07080d060801090302 81
    0x1210860010004081c0d050407a0442e001c0b0360034550301081e9103207820b0000507e0042d810700107501903d00c1105544664601b0800120305503910391010f08540e00500441c0d0000d450790402d440d000540d4000d060846001400707052426501621181c0280002254141000031215291003000501d004090145000f01c0d152000400c8d5203802a280000d829072420a243c01800b4202c40001c0007001600400e10503a030145da1840004e0048a03000038031025008180328a0394543c40e0723154154482100603000b92a1610200040100940d135064544141944030b900960a03a8441b40e09070041c0401400d03030320440741c10540b2a41c2c2e845881d00100c5132601c0c603910585402d4148842582001d00500900701e04009025401000901000b02d01002829080c0c6521388516220002c000711307030f074440b020001d552141d41c4a0400001084040409200062601c3c0010a0803030b545a041405106807985046c507002c803654990380715803c9401c101e81251380c1d81c0c90000703003058203009403003c003480b903409 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 108476987 1250 108475737 108475753
    0x210203040506220e19020d14090a05060717061201020903120d0b090103050c190504062903010501080417040b070303140f0601020307020d06110f0301080f010515060a031d 75
    0x8204007a81c032001003469107405001c0d103402c1009617a040103141400250352400d240c16088050103105056265051048040000106021881860103442003060380d1050302d92100071500c0000e03481c07840e1113104419000c5605441c000301c01082002d090710001d0b040801000c0000d00340110b11101400100700050320154501c0d59116042d065601211040120350450b151150344502060001d400b995180400c0150f5030301c01d076844801458000d00500442e038031654110010325400a020720000020189030440d2a001c0c0d044d40d050b5034041e510481507507929100d18580400044142d10384000420011504125010080c403111780aa1400300c0c10740b954038420400390f88000d0802200b0054081800220380e4040204c41c10b5540488488603510040c1c1840801440803840034030301d560780061150052108000514101c5415005480030459040c4c00142070300c20840f001c00700c510340e00402e83d9040c9000005403003234070700c28540011080c1c1015100c061500519074000401e0384440170b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 108478237 1250 108476987 108477037
    0x10032318060108070b0a03021c050a020c0111070201140d02040806102408010b071104091101020609070602060f0411190f080304030c0b070515150901080a210203040506 74
    0x4075801014060020000180b0b0007004003d02d00402c500202095000224841c1c1c4500020b15405d600100490400c100e040081e4150020360014440000325420702c40c0c2d0001e0240710b10141c880391501070b1103440b40480c412006821640c012a00303180515401c0c04046041c00d0704118061140b1081d000e40c41001c2c1c01e020805031459440384030080b000c803000c1400039041761710044480c11600310b0080b0070f40786c004a1030010191a45030001741d41151611244405020f110903508101d907800ba02540c0b01038607a10309250300c8440303500a0340090b034081b00124522604002a00381c1c014090b01100d610110344100107044880000020851304e81c91403410b001d501c42e4038000c2ca004002da20001c5140901d1681d55012408040c45040c0f100ca502282e540305000c814801c0380c58001403004464001c0c6401100025407411003170106002e01c3c80b4070b0010548007000030b440c13804280c02c0924181c046a80e2400e02d018441130b001c1180c2103000a00000500e84c40d03002c0035240301d48400109080c000807900b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 108479487 1250 108478237 108478243
    0x150708070f031103072301020d090c0501090f0f120201030f090308040507140901090c0c0206040b03100b0a020c040e2d120a050706020f040b04030503090108090c10032318 75
    0x383c0c0c26000d4004004070000a140d0400c1294490031340254a10340c401c002c0113090082c02071045202199040422003400c000f140c6140c0015107170240c0383c003841252a5080444010024081d01e1501c8d072070705030103101030400d8460300720b0b404e48145008941e92900302100e0040e03a003503483c2100481c4010080c0400c205040c00140702800801048040d106100f030002070a00b081071081050740c69880c507000d4900f0b0312071714200d1503894010f8001c40d80d031603075110050a5035000302c2d1250f581c05840b00020072001080011912941e0303582c0c1c0240a0300d1820380400000b40b0001109042e40e1280300d100b0500413600c2080020361041706000e010039152859106406d0042802c90041199410001c14030056004400c0e01d02064120b000181c450708101c0810599200c1c54001040c2c0010100300001000400001800702c04420b0380e500b20b041d294100701d184c1d10310311074005651180020042820892080d40030b04140b4203160a00e00f00034041c081d00d03040b541001d032928401c98060b103204a000140070 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 108480737 1250 108479487 108479507
    0x414040c03020c1506031e031c0b010c02040f0f0513061a030d0c0507051504140306041707030504051c1b050102030406080a0e100510060c0503030105150708070f03 72
    0x203420254a011248201c3d540c0342d6183c810a0050130f07245401140068070100306860b08800010205c0b02050036003425035130345e90003072001c0c100a02001d40c9003000b141c046c0c3c022180d0100741070f1112400d8040c07990030132019200b42d81741e00308543e80d10440c10030380d24058015503004400220200a44c0700b0780d820304406480d0641d4116040c84454105c00c3c5090700c000480c1c880c0880c584c600b03604031030040d00d000d40c1070100a901442e84000515210000000482c0060046800c0108912f604100311381c2030540f65542241d01405505800700e1b6542025006001440310510a00d445881d003900c40b00080d1000b80d81c010840116580f41c5071007400c00c00400c0a030045504c0003480120705502e0580001d58903c1140034100400c407000300860702c1581141c10441907640a40207031521f11641c0f081d03120040008a40c4001c0c00725107000b001442c140074002c0103802940160280d45960300b0482441108060050a03140001003000032101090b40d0f0742c003805506224500c0d060001c02c0d18203009240d9248 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 108481987 1250 108480737 108480761
    0xa140313061b23031501020703060c090f080c0102121606020f0d050c040b071e0f0303150b1303080307020a0c031203060b090f090414010f0506130e15041502041404 72
    0x1c3c2d200098510440d01900c0c0e100064400038807055121000403820840342d80e00042400e410b00c0c00901a941e08000c01d903060b6201401c840505a546504031540d5882c800c096a000d80c00c02100540c161a56000804006600d00da05100f0240541d81f03140c12070f400b0b0350358031000c1da03004100041070a40500400b50000104100e40e820036003002a189142d00c5440030060501c044c900001c02d40540e08102d886100d83c11851104039240b807402c015000e00307030b0114208800c960000021401c60059000d4440e044040722a0226980c21036496130401d41c0044c00c00001c1d07110343c49294001404011602d406544245241d10403045004009070640c1c126801049070680f06000502c01ca45807d48110300b4a041180d04042940792070606400c04038160501039415400c00e035111044006a030000e81c0101d070251442e250307051518070501c08540f5020204406a0004115409913032403144503184c22078007414864158140304000304040341d200b5801131120740307140e80039401d180c9424810700c003556007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 108483237 1250 108481987 108482027
    0xa030510050607031403040501090c060c0308071b03050315061902011401030215070201030e010c020304030b01050324070e060d0b090f1017030d0911090c0a140313061b 74
    0x2400c0c0d6000d0f05d2112a241c1001618801000107018000c2c00d4210031483d90300408021003140e00c1e0140101900035405055002c0703140c0401040865109060070007841c1d5016000c0d05000e4490380d0221001d070b0020744000c0c1c501d000060440b501c5e40e81e60f030040c026008032810f3301c0015444035001a0035200a450246031a51141c001080561190002c0d244a040e441206c035544402900c0182c2c01403641e440300010a6282c6145510165000001041681d0140300042c00d1a030380e4170201549d816001c84922076410b1940141c44d844500b00d48800d410484505000030260a2100410050340118242800103526415080d0140c00d00f2011036404c07190f052003008142c94400a0052007050600c04e41c000314005e0440c07a40100024000d0351703182e5200840500420680382403140e0541501914144503c1c07031f150106000d44140d500302c41d18026151540032801c6031410358100315410042484901c1035040c542d01c00055113911503118400c0580d60800e00342c005a11001740700031440741032060040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 108484487 1250 108483237 108483247
    0x50a060903020a14130e030d05040c050f0f0f040b0102070b030901060303090816050f04020d02030c04030309060f080105040b1302070b0f010603060503030304061d030f0a020c012d020f030a0305100506 88
    0x1469200d19101c17031302e10307000f8041110904083c9051447c4242412000c41901d4507040c001040030310100d42085800846801203444c40303840c1044803d00c240c00c0c91541c0001101311a2010f0b00b802c0d003005c600020f0500555804690383e800100b0194421210444c0030b0f50358800038000c258000745040040c0000100500040c94270703c590a1000d18580505841280182505245a529901110012501070710299100c1c00c0c08001d00d4619001404110b0202c4c01c018000300c3c005225901e12422000035940b0800c85034605030501c00241101c4a46903001105164003808002890000b4903145108180c100010314010500301c1e0981010b8100004250400104122983d03000041daa0003540007040040c1c08801c22802a6501c01300070140384070f0303002c0843c3c00000743c01d0b050090680b583c4180c09450302000340400454600d4403041480900c0038000c218080391211043c021160280e05004850307003151701c502038a02e142c000405880000c0c0d02d62082040e01d84444031000c00604045e42c50364100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 108485737 1250 108484487 108484489
    0x307030b27030d050405010f1a0a0504020906030412020a06020a0f171006030203131b03060b09040b010b0711040f0c0909140610020c0907030b0414150f0a050a060903020a14 76
    0x19101d000a0700b8600c0c0d494201290031b00c4000c5d0701a1406880d81c581c00c2180d19080c003284414400100c100502c1003008003130000f2107040900864100300c1c4010a0940b41d0b50b11030317507204036020440c03c1c281c08501c225403c041c0000c00b47e100030080ca220540f1212007030000d41380001c19035280d5600e1000d0b212001d006110344130844100c0c48050780e02e0f0b41005a102c1d42c40d905241c400c51110507010344006000302c54081508011016142a030740242014003840c2030a805015240c48203580007040d11417140010000d940d040c002403ca01c034450035841004140010005055592140c2d00f190802e40d901ca0030060541c1090245c00140030411050201f80e400030306404070b403440100154021541c941c1480511741c4244030090b40442d00500c1841c0d50709200304020003c042c400541400380b4942041c030b1845000c29940288a02205034a40701011407680500a092648040f455004104d180010510756a03400700e10001d000560303580b180151440c0108820700e296640041c6060155002074061 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 108486987 1250 108485737 108485743
    0x2802030a081b0c100f140d150801050415020a17041101090501020c030a12050d1a0108070c020f010e06090603011d100f330206070f020712020409050c0307030b27 71
    0x1c02c82400c0070002c107000e1180a40700395508110008211b0710004e0001031600e042c1e440281118040803a0007803040d280da0019080351810388015051580d0039001c101a02417940091001e10807a203051003420403485000b0000c9201940e0031180308846a022614a5070700c400400f00800d001d08c010241541900c002c40e071103041101c0301a02c00d519a26446032101e004400301d40045200c404104004c05041942c140101003043e00c03103000030a61008220307218801d803140048141c004100d1041d0860b100015915100c0c0a466541c000340140410003c0b5500c0001460082c4001025a000c174100403003448940480142400003041c0210014091441641e10310010780300300754814006807190844d06540c0c0000e195040d020512840c0081c0000c59002c509a40201119180d01100781c544401c1680c40f010907000d0864221680948007001d03181c0303904810b01850081d0150b030500001c00d00440c1c1000d016410649058422806120008032640c1e5190300311003d21525441200300280602c0d1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 108488237 1250 108486987 108487009
    0x30b040612080a030b06030c07050d050405010203030a1d0d020c030d0302211e150a0506031915031a100906050d0b1008011a0111010e2802030a081b0c 66
    0x100804000c2070180f0300034083e520604002d01c00900c0e0544030f1400e02043c602d04d5001d0f0004070346500403000201081800b80701a00c0c15141c058002c0c5080d40e640d10b140a00802c2800c0c415596001c0d10400c144c503444003031090340307019002036000e002c0301d00f00031043c54035145080d503000c03007014810000ca0320307100413611004921010700b80707a81c42c0a0315070301e1102d4046d0b0f03000c40886900024080901222101c0326030b080c07480c140156040d81401d0340d9401004007901048600158503a2050150700250321950b00c544c010035400034649400503201d46506070042079540200340043d450030240414030344040d4000c0010b01c01d2210a1042c1800c0201040701d41001141c010111103214010810000d468003110001d800e0500c0204100c02e1040e20303030314000b0701c4080707034034041241480341890741c0406005039800009140b0003409040722180313140740391068400240401e01e035480404001030340c0074001c040341030780102009511507002c5107920384060b287c03a03000c030110341c41542e801c5054cc4804001007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 108489487 1250 108488237 108488243
    0xf0103080a0f05070605010b03180607020304170a3509060a082503060519030b04030c02180114041107030c0206031306060b0c1908070b07110109030f030b040612 71
    0xa0103201c4100070340f11409400030080c00107040400100c0c01c4204000a1881001e00000342900e006000358860b446041c20346031321005070000c21080c00700f4400c2483c4110b004400c0c00c101c42100c1c00544542440b105010300e40907001101d4050040801a100320300300c1d2104040c14524900304994001400360f108a804139400d001e061800180c11400c102d4104d0b012900100a10403140032807400140200703103900610b0f1181c80340600400c02291309a668400b540d40c0514421065200c42d1004d0b103030f050f081ca0040740e001e02404a601500005159003500134120000c00300ca261058804100940391070750544004258140848400f02e0f0313002c45e5400d071454041d21a59603030b855050036412074502d9943e01030005818298002408944580140716102c025030a88000784001564500c80c80f42a1801404c0b07180c042c020703100070510440e900c81e0000068209180f01c0c0e0409404182074610300307842540400e620168808034103030140103d00038a84111001c00c009030401545044002c0e10344009 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 108490737 1250 108489487 108489497
    0x30408031c06050301020712091a0403060506060f0a02061015080a09020102010b0406260f0d050c0c040c0c0605090c01090306020715060e040516030305030601080a1b03060306050f0103080a 83
    0x244186550101010b0f003006002555079812509100c1002100580361900060a446001a18207101c150300020f400da84000546061700d5078492201601c8040c1c8655400002000750800c0c0087c81001000c2c2c020f2681c011705050300c1e0010b0740f0f205440aa501c00c00140d1360004a503c01d0a03440301c42d9980c0200c05003000a500c0000e070004070f00618036104103607040703841c080380032a41507121f400c801001e01d1900401c0821810900b0095140d41180405039440d5001c040b6010a15018801600c1a244140304442c810784603940000d003a950303c0f480107400302e1012100301060040340c5c042c1640c0490700500810080600c0c4000900024a41c400582001e41c0400c05004001c00d04210343d20000410905100103a11405951505401134408491038880c030512400d41461480100d0304990701512a1800c43d514400191102007000b010b004806c0d544070002c180203040640f105080e60700e1a503000803c03c0c25881c2c44011544064280b050642c1c98100400014400c9001c44515085500d40 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 108491987 1250 108490737 108490777
    0x606090708130b01060201020d0f0e0606090a0e060f091504031b050a060e03031008061306020c0c0406081f140403051b10020703140313110d0203060405160803040803 73
    0x40c5850b800000c0a0003081d03c00e50000001e100b07135054001d4680340801d401d040080340c0031750007190202c0b20314510b40c02ca0b0360030040000e1582c2c9401101c555011b1002e44001c6001c150017a10f80b8201b41040781c0400c2c8058802c01400a1082c0401280c1d440405040c0020b01c5403e09031409400c02c40c40c1a41001c5003d04404040100031040c0031440215500c5070090011f14134100c4941d450350011a0401c0d00180d5684000590031400101030340129020080512040b40980728031020b507003c44541456441031010b100307025103451040400401403100909001030300036480d0805610401d00700718101d8103091000392078546e03050311242c0259140c2041136440c4482c42200c100d03d007507110605010300031055246103e21413a001000032601c170340c2e10b900103c1016062003a45010a0b1134900310089000002800512500c81482040390010118611204564000f0f0b15100b000c079011181500481c0e030341078030110024240c0f0701500c001806581054180b0f071005503240241c1200d14055140422 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 108493237 1250 108491987 108492001
    0x312192a020a080706090b060105040317030601050403051b01080a0902030303060f04181101030c1e0f0909020d090b0603070518101203170601080603070303080915010f090c020606090708 82
    0x400d290295600c01c0d911900c4044d1401d180000300070003c8141c1d000921070000414540c8128111019642c1c841c8141300d20010f0001c41e02c00d503400c012700c5181403000403c4003102060042194844400c08105401505002c100004001c58409098400c03164204000000140e44c08002d0b00d81c449416a802a500d181202c001409030020302045014a4100c441120900c0a5002030000c804030a032401e001403801140104e8102495101d0b4600c5410340c200d0303080c240b500c074070030034200c088c0359240c408603240d280c0d1852402c0f86d00c640403282c041ca0740c0b0080d0304108500d501e1542d07800034048020745103d51415010401d9a05025220b840c2e200c90301c400580d26188600b0004e001e0501c40021594074174081c58098148042c0310f25003101e11001000240d019881109058460721000c0c018040c010315543d0140d4542101802000322070091071074a018000c44001c03000d008000d008420341040e442c242040044610320758ad501d0454015008012141c0c80340d6400c2c503003104081c540b0510666a040c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 108494487 1250 108493237 108493243
    0x6040603020d030206011e0e0c030601030e010f06060e040b010219060e07120b0901090c1205011b0c1703010f0e1503011508011107020a0905090f0312192a02 69
    0x80c0000394801c82e0032180300c0603d607000802c14182c5046605910500c01880b10b844149401d9201e000d0403001d0003000a40e083c6465406141c0002c07040c1404501c24135501400b5080d0381c0c000d0305c80919169140d03410465264411500369030f00405944c10084104150300003911517820a40d9660307203074070040c02d88040180652048004090100544007144d40740d80342c0c40c4502652081c04d40c1d03941c113020007007168001c041c411011a503602031341004940d45072202c084200b5035010b02c159520356840154001e0201c2c0030240741ca045405644005402d04c042c500340d092001940342c40b160814051006002d203902210000040e100d910491180a648405606c1030100c2180f184a07055400c1012840d0f4a0115604120a540c034100080c8181441d00021011500a50002a600070080b0034108041c0030a94006500092020240c1c2c1070440c400c844e0364035540c003003d0f0341c0c41e00049020801002e40c5030f19004203d21070b5148010300c000c0140300901c005c190074445001c500100c6ca2101c0c03140d418020 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 108495737 1250 108494487 108494489
    0xc0d0b01140c010204050915030c0f01030e07120b0705030118020702040204180605040605010512060616050313030b0703090323130b0711040b10140d1e06050402130905060406 77
    0x1a41e0030a55651815041a01030740040c80340e1405100381c0e00c04203210055483c2c01e0980f4140240044c90140c1083d000c1020051009201034185903036180391003207410b01440f240c406800c0c81c1540c080c2480c8903180c41d0b106803000038140070803c1420f10051144981c8026040103e044541003d6110144c600000d0000d100c1c07540040d40b809010291a0b50440d000d030400401c983c01140c0411029a440005443c14419801c80030001210540000da540c94003402818070048021100c1580c50169070741c0e6403650f4400012022080c2c0340c035004000700708111101c075500c441185001e10128000e41d070042c0404ca403003944440480c0344222000040000340040c3c0c2d00d680358103056000e5050740e43e0840b90a543c000d14040e02c1400d00349800c0d03903040c02d107400f1340f0303000c000050482848800c4074001110080d0080b403c0001c080d10400404001c460b644c0a49049643d00700300d401180500114417000300e4009078001c500030790061014034a0206015100c40460795080e00101e071558400c030005000b4051 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 108496987 1250 108495737 108495767
    0x715120c030b030c0a0612051906030308090105160c02012001050a0b0f0303031b0f0d15080f070305070b1317060106170103080301030305090d051e0709050c0d0b01 72
    0x50056189a081d600d0341101d4040d58060b0156409201c1c02c105010005800b8000c5c807020a22822803403200384507da00141e0f011000545110200720020070620603034086034000d50020380d8080610203800028400c0c0d1390414120301d008083c10780e4005028008001072030020b41030090002540e0903501c400440c0e803a070001c07160700821040c41c1c180c1c0c6840c024400d04554901440849070342e80c52038180001124011601072135503090480e003c900c6080654010104800422010721219100107128018443c0b80003045000f0b550031400d02000758500310303145d80c00b2203d43d0300c00201003021410119800080da00212242070740c41800b0007038014044540c1d0321003005080184802e031105074011070464103030360f01c82e6119a441002a26000c0c4d1101080c0006001e60304100010030009000b44010300d44c03020301030520500c01d05151500340c103100c0000c007c02a904030714107140c10031250034010b802c0030300509a0200a40d081446100c28540104c44030710003d6513036a82c5603400c40e17003d0101809802d80e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 108498237 1250 108496987 108496991
    0x80a03150803031b040803030109090206190e090702011a01050c0c1504080705010f09060c02040603080309010b030d2a1704030c0e06060a020a03031d100504050609030903071512 78
    0x540c8030781c8180d40754402c4550b40c5450718258005010100c0300e2040310211464200203504607400c26642e580100941081240d00010401c61317180308202c4d4040080848503240c640e40c082941c03c03002e0140d1980010b2a41c011a4075004071040c40701c0040070f011044910a10b0007a032100e510340b00103440c004076558201d40c0412852a81d01c69942c5003001001610b2450007070f18002070340d130310054416840e4500d03001c010500c000350900c411440b405d00790911500003400892525543c0e00d5142e007660050380e2885013651140303c9100281001c0101e10303480102c903e01180d5020010f507980e01800c00407204001c1c1c10301180c0c00c013010311107951075013042c5501d11107195030346644d80d02d04400e4000c411300c240c003181c200400014105103000750548503500c14640140c2800641668201d0040050341007208500751f00e030f460065080c4041200360f1030080c00010000d6603041ca41801c03403030941c00402d820459030081010f40c58035280840d5900444107520306681840301c1411041d07840740c20740201940d68074 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 108499487 1250 108498237 108498239
    0x1020a0b0c1e030a0f0c050403080a02100f0b0108090d0917150c030403030b0a0b040306021605100b01020c060f0910050c0a0b01030b0f04050c06090109051c0209010e0105030703080a0315 82
    0x100500010350003120481420421540341901e118146caa41943c1400412000e2008001003032101c3e00406d80b10704184142e0302c045e0114840103007202d5440b07034441c2003103548030100781141d40c00829180e0821a003030300400c00c10f2080600100003034403501941c00c007265958000710301d0000802c60403076a802c0802583c9681e00d0310014091040d0400ca4042d00001c0c113101402034141010408841503400030102e19103000d040d500c40f003010f036111100c1f192100301c0ca005801d02242041c0001540030202c1440443d1000000c4d00080ca00422020f0092040f001080080c040105150072910800303801c2d50600d4100c130101a089d504ca015040020307105000f02002d0f1401c1144d103404281c140d0348200c4e8a010340d80c0307900d030001540102c1141d0090865014600c003040e00d280103006401c503080e0501d0400980c0b500c0e100483c519410b486010040308044a1148086191000c0c000780900881c140c0c0202661401000079900d000910002d422144001364001c41d041c4070b030b0060b98228140d088400426 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 108500737 1250 108499487 108499537
    0xd150207060917040608070c1b030516050418140a080c010c0f0203031303030b0d02030f070602060601231c02030907060f0203120c0a03060e0907030201090f0501020a0b0c 75
    0x5080220002c5400c0103c4400ca004403040780416501500c02983e01c41e0603542d00e0040039a034008240c102580c0220722840e200380301107181e041e2040554443c0d000b0780741c0003410550000200a054015511450500e20444490909282190f88042c1c01c02e11640c40b000180c0c0010741062140030000e0400180000c00450350001500034181d124090350302c0245080419030101d03100c2c00103a60031442c1901e40c0c0703020700210b8070a420080c0da07548000c0040c06c000720940d0009150030b40c0e514136a07450381c00540f800c12080d5014480c4075481a020b0801c0d104140d0080400c4145030b0410501c942034180104080c20a240c0940500341c03000e102e41011035480c01d1001c1c00341d81e0741e022882a840012240c000c104802403001c415107521103e4000440d4003a1103071100b40c1e0b503039000140301c10700b015503552000030a038000001ca81d0040009502501d00c460840c00010210b440301d8114a20004103080e04016999000980c94019508810a852540c40b86500d60383c445c8169520794800078003444102c440 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 108501987 1250 108500737 108500741
    0x8010c1b03051c090b1506070204090510020c01050f060603010303050a080a0b04020a0e030105060604150c060f05010f171609020307030902061809010e330916021b0f0d15020706 78
    0x100ca4010040095680e54000746d072480b0401c0d684941e50800350900205e0010b007021303001244290320074401c0d9070307625178818145400c9030000032099005a4481042c0b20600c52942d20450300700d0030035100107207158110740713015040c0d10840071400c040141c3e0030002005030040358480d820b4030350018425941c0b0802d061008155a0145600610952805010480600e00398040700c044616500e109064103001d41c00907200740c2403042041c0d600c0fa0f241d5240b01000d42241c400d640c040c00d40e000b054a0128104181101104444841842291302002a9100e4039041e02d41c410704407010f1001c09170303480e40d8141c400c40250203c0c0700000d4000da001701f05200c00e072040410f041e1752802e0a4802d0714003aa65030710b01501c3c42c1d0080d41c04001c070301c500d6124046212045608001421104203891300a02001b0012030541041150a5054201c0000c4507081d56541800080c9c190502901c0006400100700000359460220340d2000307104131200712a01040000e14451005810380154086490b66140d00305040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 108503237 1250 108501987 108502001
    0xc02150a0603172110150302041206020c0d0e031506060d0504030f0212070f030e0a12240207020a0b1c020c01050402010201060e01080607030504170304050a0201080108010c1b03051c 80
    0x4218030b040c40c1c0284001d001503459413042d10300700040e542e40d030705d405003800117100e00d030001101f00342d000c010110700480380d0319000d40290b21a5100683d65100381d4013450408482800f04002c000d060a0755000d10747c0d0016419280150440b280b09240d1110000220b481c81420200d00c3e0844c28001048281900030079140b02c2c6006940a960401000c0c0c102c2105621072038400a080003940504840428070955103400c4150300078240b08032154850300460712078001200100c03030008248074080b01d0303a1401c0600320554400382900f9820b1207040d0f40065416244e90083c54004a000700c0d048105c501c0c0c84c1c01c4804030881c0c2100440d41c411040d00c140b03001c1c0ca021074081c0e000d0342c24400005400ea2012400b24100e1702c4507030240006841300b89045000d450080e0055600d0010010b8050346408107200450007280300e50001c040d800064400903140420580c03000161341d14080c0c10007031290300036009031640c0b01d6130449114181301525040d64503004101100103804c441c207560303940100440d44450 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 108504487 1250 108503237 108503257
    0xa0b0103050c030a1a060f060d05040614040506040609060f0606091d010e070503040203010b100c03030f020a020309061b0604030504060210050106090b0c070320130c02150a060317 79
    0x408000d1100281513881e400c5010082500700400c00c00030846002e070403000d41202d4001d01c8039891810420018400307420928040461036a00d0080c00f0401405205030322100b01503080c01301c1a8034080c1c0b21aa1900e40c001c1020b080d0302d03102c1552008100300c9601c1048003419003281004660f807129401000d05440d40079159405401084169040c4109a082412104076032001083c1d40d480344022030302600041c000303e03099034940e40380420326901c001011400f840c2a903108046401a41001400c2d134090608240d0000d1041240900855021084400010041d210140e65132282404c418419904c40004042d43c0602e1040c80f040691000040c812a4810b0b400ca820300c4031240804030031901c0a10550307005c02c040c08010081c3d5140380307026104140a080945406540e603840e00a617900d070340d0100401120044120300c81624000d042c0002072039600c201040b010f02c01a402a5079881d240e0001006850008005480c80707600da0007070405964800e0415511a181c901008519000b100c211 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 108505737 1250 108504487 108504493
    0x2070506032205100504080a030507030b090622060b070b10050a12050f06180d03020405030604080304080415020a060e06252a02030c090417030c0702030a0b010305 72
    0x50585400026240100a064203068282042034070b200792454280030202c0e00c500441340703074050303440e003e1150f03a110718004c00700780303580e840c0948000b0212a801080007041c07600d400010403c42d1030301d0150a07403040e002e4845c2c1c2ea01c0b4982e1982445000d40c800c861003111800c220000c1201790014010700308080c4583c0c5d84040136160f107602181c010020703015440c0c0081c1510001c010742a500448446014050801c3e5a0070910300300d5202e040c407400b110011580c0700c1500c821150000308002514521065250860074541018001703910b03010042c2014000c1d80c2e0205c0481e0034003810f41d0441e0b00400d004003000200140503400652944529030055034071030b1500c0224629264003040c503a1080c0c2181e00c0d003200c0711620760004d5443d00390345c0ca003000c200143e0708110308001038041c1401400c0600c5032100342c08500140304040c5441103201d5010300880490050000041362010100c01002150041c543c590350340c900380420f14050581d01a5262041350761180c01c0c0285485103a060700e00070419 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 108506987 1250 108505737 108505739
    0x70204150302100c080307030507050708070b0906090f070909050c030706030501050f040c08040201080a02090301111902030c07120227100603201305090108031b0109020a09050702010605060315010207 88
    0x400c3c1d419003007212000d0445ca03000c04c001410540f20740d01141c3d00840d1410081d0402c00d4513164814941c00c02c200c04c0310b64019800030310103200000c010696101c7d801c00000c04601400015250710391400d84100310020740c83d16009020031009100644903001e01608840010795260001400307031800780b14582c0075161030380c81d8846a0030301e401548603891041c1c45021890b00d590303004681c101b01c001c1c40ba8003000da09200c0020745a0b820300411a0f008500b039100c40d1182c44200b50342c2440380040400c0d03020365004010a2660f140041212000c80d410040380c44042901030000c9000c55100b040b250b4100610051003c0e0960b820442c2140a004940b114541150721703008150100d446070000003514001e50455909031400d14002441e0219200d41804031090382c91000c203003030010070b07007000f10150400b11316001d000c6c58214100b600310304454020b0100c0c95503030f004901007030801d00808544640391400110858000d402c1003008141c050080c0b962403400c030700c10381110a04021658014018440 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 108508237 1250 108506987 108507019
    0xc0615030102090a060807140a0c0501050603031305090405070e011212020610141203070b062d0105030c1306050901180b040e040201110a03030609110a020a0314070204150302 77
    0x400e03900109000b404d41a005801e1a07415911840010b24150400c051030001d2141c191101014203180207494a5695005034035213800344c02d44000815040c040da000f40800d41d071080c4103c03030417821030308180d40107155a1110700f8498144840c40d00517610707900c0a40700006010703213100111031032103003c1c0d5032100a604810004980f101010b54940c0c0e8504140d82c01402490301e101c000c90740b00b0400400c41d21600c401c0c404c1c16802c6801128050340c01c08820010003030242000c580c544000c1107100003282406102030f030b001e0011a640340c01f4904000f40800003a000320316007411100000c2d84150b22010aa03a600f200410300da100d00742c030b680041d4040707034100f10002d0340b0405081034030100d5040608003800e0410700140e078200140164100043d0841301c0805080c18030880403914001e03900858200d0070700441009440040419283c082000c2120034401c0e9404140c1403192a454680b201201c482d0f5051903d480c0242c0b071000c1d40c807a103001c80d842e8a40c90034484503801c4902c2039600141641d4a44 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 108509487 1250 108508237 108508241
    0x150510030507020d0305180703050a0b0606030c03070513030f121416122105090d09180507091701020c0d021606050705030708040801020d0e0f07090b150c06150301 72
    0x103100c2c0c1001d03030f0203800d00b1004103010380c102c40d6001e829400b540c649102c203860001c2c42d20903250b006a8080d00203580f11824040314011442d84802c06907092032450800900c010306500c0018200000c000c00411001c166461940c0008025500210b0940c00304056040507110b510040c00003101141e43e0088c4032001513160000d45450481e252690072441415494020746500380760124810400e507a40181521120030f03082c142030081903080042c0601d0300e942c907a0310300303140c06440c101806040d00082110395203540244c080c61182c0070303011035103807114501039400b5115600032901d04103281c02021100038055010700052841541203034458101c0740d04c140e0325401c4035003059500a1116105000701c9016030010b00600e4030640c00c503450003e03161124000c0b500150020500c99400180411400c0b641d406010740010158003d8484625190840356483c00c0903c155483c0c16220b084881803503a03640102c81141128460182c3d48801c641a01754554100711604031421281c0d4a2500c4942814 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 108510737 1250 108509487 108509491
    0x306120c0f0d0602041703030103060612080304030509120304090b010915080714130308040e06040605010504120809210d170106051612030e0d0302070b0105040902131505100305 78
    0x240500c101c0c814900305000145010701001d8a405400304000120b8072201511030800b1310f0104003950b282d5041d80391400070346001d81d006100482d40c0b154001c01040d0352000301d0360841d5260400da5520104030002ca21558900d003034000041c0004100000c1c0490907800402007424240ea460380c40684510a80b05282c10710b41180c400034546600154090780900228808010147c0c1c80c1360424244c00c881c80a43c2c20a50801c45a5072004902001449180c0308880d402c0401190305201c0c1606010009006010394400c2c0c425400c04500010300381700d0300500b1913034030b00c00140452811209104104040c20390140d20700b8942d1051414958420340b10b10b88031411210003550f441e80903407034035004446a402c26628070340055221040e000001b1042c5030002e015420640300828020a10890307141411000c280c005c040c5070041101c1800240f0f54000241512022200040c16030018000b04000c40f40c02051584018039003031009070140d9281c01258102d55040b200b28140031a81e600803001e842007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 108511987 1250 108510737 108510739
    0x204050123090903030406020c2505040c020316020f12060c030f06010c0510020304020a080a0b18030702010e040207050c0a0f0f050d031e11030406051206151210030f06020306120c 79
    0x130902c08900050007a400a005c410b0b0480c041b1050703540285002115241c0081400c00480880d02040295040901504a80e02014005103040003420000c040d1812410880203205640b030194990855580f0a0b80301070006800089941d40d140140028640f42e0003580c1002e401e0000300002620f030340c401c0c440c080a09900c800a050111015038404020390400361049074068010782012905210030400406030a010346825162410001c9004001c08045181c0c100b890704100452170240c1d0300000813442120b4284c4006076074040d00d0a100341043c1d44107404580c088001c2c100001c110988440040c1981c0220700e84a48490307950b070400c0a0b5512100d0010040340205800900c00001f400205050b403405041641401040901746400d540c05600311002107070b8082106810900c1d1a0f41d0301303620003030940d40d010541e00d0800c0d4900c118050b160030051110200000030760700c0c0281c44d040b070b001564041d120245140711031030248013a400880705240a030b0040c0303072016400c0100280481400c08 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 108513237 1250 108511987 108511993
    0x604030c230c15070305070f0f0f0303020a0905010801270605030303090f0105090105070c0803072106090e06042406081204090f0630140a1e050601120f02040501230909 74
    0x2640c1c2c0c8e100341c5108920601500c495064400050120743c20101c108007a52281d41d0041ea54035401300058140c3d0820f40045c6c3c1040b986200500c01c1011802903c189407649125140c1c0070240281c0c0314000e031042c4e8002d00e8240c0004420700082480c00610910185a101c000303101981e10b00020a0880ea02220b00900154604407030000ac41e02071002940c00161614141d0f994034402c0041d07160040309200c0c0d1500e0a980c88500b0040b540480c480c0340b55581ca0100a01020b0400d40c80b00079140c00040b00e04280070700b10800c4849840001c0e8442c400508a400544108000c2151500882d03009440740f02902818800d0b03510420072613120b0007094480e05800100b00c801541c03500f90203564420501d8021010220348070011074070003060105d05400101c010b0070b403400e01746004483d0100d5004004184440f0b155640e00048011560038103403110024401e00c0181c99040a81d40c0d54032440c1c001c0e4102d4601800443c0b40c0c80b00074100c95104d03682580451100000d0300501c110150111000000c81e0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 108514487 1250 108513237 108513247
    0x41406190b060d06030c080f070312031817030f07030e0706030f061805071106040f06090809040e070509061002030301050d0602040506040f05100c050604030c230c15070305 76
    0x18025034071914081401408441c1440d0308991030303d08554498005441003804107804103e514801c11039480d918600c2c0001e00b08562540d03445102d10901103643d00e0a041e1222003554441415019401045812030a14224600491102181d960042c0e401b081c1201280b400610014080c2c0a20400800c285c00240200c038503200c0100c004140c00c106a13031000391603500000b0003d403128100300d417100c0806030000340d0f42412600070341801c66a00b142e2580707810940070000030a550a07622600d90b03400c101c001c100d040c000e1402d14003d00c22500060341c001d00d071103030b2240746400010303051040e60029600c0c2c8000e500e4000410000c4980390b070000c03005a00402c0188641d0600d001640e540c2031041c00003604050b111000101c00313410039048010441403202c020401031400c00031012030b002d958140000b0141007512166111440180040e003407101e4070b50087d0421804032001441c102a00101c4520781c9148400301b603c683c080c540d41441070305551005108030780d0200864002d680d06880b160714003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 108515737 1250 108514487 108514531
    0x7090e1618050301090c08070f0b030f040503070807031e020f0307111203040312020106060309021e01021f09020102060c030108060f04031707030207140106030210050d02040504060b03041406 84
    0x5198501c003905000c90301000080503102402200c01d0540b1459114215a042c00c2000b864000603500940001d41c4041c01000080d09800c212a0030443d8543c102c5500da86074144a840e41c4220039004020480019289040c1584005048000130002500e02d600a42000301280e4800e007014002c00c0b25041000280d00103000255901400c00010700060180c4c072808031198115001a441650700c8105021002c421960a2103810040c103181e060800030800540c0202c1c49000c1101190303549190741565012082c0e002300700030052201c03d060308101500e000800300c0050400c0c030354102d0161060501140006a1150075a41a01c0d0214000c1901d550303855045010707000302070020b80034080c05080301c007040310704040c0d00fa11850007620007591360099445c1081c0f040703500c02030410090b4540708041c40166901040749035a20179a29105171a4510b01312008028855544800d0f8001d00d402c4000448012410207103111724068034031144d17405480c1e44d6031515002c04071040e000341c800014041d510 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 108516987 1250 108515737 108515747
    0x1140d020f03100c110106081b0f0406080c0109080a11280e010510030207020d0b0a0e01020c1005090a0b0606070807050322060c081605010b09070807090e16 69
    0x40180014401e11406140e0408241000c5107203800100650300d41d9040ca501c5038101c2e185591060040700200181840c02c1d80e461340382c0c1040110303580c04005d107042009040da80c941c40703800c070182d000300100300c1160b4881800b9514890f03d118680461500003002905a001248941c3c0c581d401940c421a030005000c1004000e0f03058a0454601200301030038219800c00000740000504601540d0701e185504260810548030340620154040500412440d4010303100c650021501c03075400150142c0c240c40d1348202101034a0030043d275410381d620100300702289400010703405c680003c416000f00407589480710343c50784074110110050080b40d4000c1c08220a810325070300401c1d1031070060700136505112540d5070380c03400d582c480503042d211031407001d0300240d04811213003140700102441d050030031880b0015070340c1800714001c1000080d628003d0f4100402440030a40012030728250041013130380d45240c41c0c030028150900554800001680f80e040105120846001850103012041841d16043d00b0803c42150 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 108518237 1250 108516987 108517009
    0x105060307021f0207020301050c19110c1c0b060402040b030106080615030702010b0f0406080d03050604060305010507020a031106060f0f030a020301150e0f22050a0f060203090d080114 81
    0x210f00c03400e01c07010258482070140812120301c04201680c0da11060040500391500034068a058010070801484040d4244000c2090040035040c020101d6100d20b070210f00748240030701c80e15008000f02c207103c644100d00b0100f0141d000e204501e042120344800e8103001c02c074007440c01010b0f5680820001401014003e41c2d000350f10410080801d64407100039100440070343c10695007000941c1d1541f07120505c0d03280100310403110075025030782080600d1408012642d20640440000103040e0781e8000729290751500e401580286400c00002e001038201031600a5946804c1c5600380c00203418604441e51240010585501414008103c400700b0a405410004202c000b0900c2c00d0341480384d0101e44006031420b00404010404902d60300304c54620300700441040d02c40041100210100d40001c100d41c190b8502100000c0600c0b008052011801030b1510500d0461681d101a09002400c0700c618100140c075001180300c2c202100588040b0710015000b5980217000380211102e40c590750078442c1d45030070305503005d40c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 108519487 1250 108518237 108518251
    0x4030f050111161401090809120f0d050a0801151e03020712030605011413140102070b03010905010515132702030405010507030605011106010302010c1103010c0f0810060801050603 79
    0x1550b0030140900310300e0340d841240f003c1104400a8990fa06000340c0114015903c10031100070320005c8410f6541c00c0301c03485414038480c8501c0c041000c003040844d08100a11101d900c070404c880400a5484000d09140c00544460001820f80800443c4420a00440100754481c0d83c130382c0c08026070903001101d69240040c030f00f8410981c1c01d100c55000300d004401444106801914001351040c18240010300c5030410406001da02d440030815480000700a00854044803180741c680c01000110800403400c064180d40104c98004001c00003081ca0400c0d0347c0418101c41e011520640c2e100c20b43c0303c0b1502503024801011288281c001c10400502d8801c46404606002c3d0807401d91a2480369400346040741c00580d4280da00343e54407000c200000342c052140d14090082405c00302c13213070400400c4960341c411050000074100600101c0031130811440b000e0780342290800170002e121401c0d41c8003004201c120342c0441b810005042078003145408210035090f41c00d881890b9500d618682c2420103001840d80f01401c2c030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 108520737 1250 108519487 108519491
    0x140d0f020906070b0613291807110706030608031903150303020109060e06010302090a0213090509160b09010c020105070c030501090b2d190b10090e0a0207020604030f0501 75
    0x2440070380d4030000200400340c0704040400c40d030b0904c4c800313100640c00c070b400200700c003a40341c100c1c052000d40040d031003860300200c82176400200380c1030340012030400d03d0513248617015203e0220a0009141c0c2042c48401a0b001d00c104995805a440c4021002c2d11094402d42c2442e810410005000322043c90030032a0203140d03818045000d0540c1c0305207d90180d8030340e2003a0300503592440901c08010300c1e801001c41c541c200000410480d411500054003109024004107200d035400034849410101c0c06003550024050b01004000924285158688580c5419580010713001003d0010503015204410b640b04007806075210080c0c03043d960300658460707000e100291240703025544000300003a003d00401107228416000042241840750316076440f503103a8245030416264941819400408452915a000410840080c0305980c0c80082e84000c0c6800310500703400100001c80b52044580140c0b191040f43c4c0c00300d4205c1c0301c55480c1c502c1901203015001001798442000c000400104070f81c4140350050600070000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 108521987 1250 108520737 108520747
    0x6130f0b0a031802012a0b1f091512060b04061403060f070207170a0606060906020d0504060c170d05010828050303040b071701060207030b0f0f04120e0303030c090f01140d0f02 77
    0x11804914011508e820300742c801d0194030b1880f810140b00180c0188003150040c813003d980e10100d10b80101340c500600026188161421052240b00d400459210f2000391007000380f0790302c2c0c1400500000007502464064070880c004580004e002d594224410360450703010300306180c101220450003880b03441d080703182885061014000b0a1007803240e50004c1c038103500c2c1d8075100d034070303002019044c41810b5110006012040c40300704200e40d040008512015072209100c228a01e81c2c00d5000c0940c003407801b0081110307140c8800070a822a0007c0d4440620124001c0e0307802d03684245104600c49807130307000000d103e5001480070900144690f01c4040c5c00510504001101000700aa1a00303002e44c240e00c0040141e2080c00b0030030a100000308125000030001e000100c141c9450b1800d00b40e9501e0160000b081c00345441c12402489202d0011910742c100010107a903a40c3c108013170841030310703004591028815a404100303907003a9030155200103080e200c0f0b20041800c04818400800c02840c1e0401528044e6400b004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 108523237 1250 108521987 108521993
    0x20c0a06060e18030a0f1211030f01030212030c070306090c08060702101a03030315150a09030c090b030a030806040b060a0305040308010b03090c06130f0b0a031802012a 74
    0x103140041d0000030540c1c2c1c0b00c1d282c21041142061115106000c10b07800402c1402c4000f980071030b500e4100701c0c003070400e010400320758405500204041d0184118500020081c401c00d42004080c0d1812603008958082000c0751118a1540742d106800c1054555030010504000144042e0048003205008804000c0810303030b030b1746641c3e00b440c80403104140181c101040003000d01c0107502c07843c00503009410680b81801100c4000c0b9a8a10001c2e150400548000d50748105e1960740d603400d03480c40303e140c1c0d901135201c0d2074561018003002000e0004a440c410100c0010035405164480c2002d02036000300188034000c1241c8082d101d8010142910750003548510388500243c9543c0002c0c00c0020007560006054a49414010181358041c0c10010f0b01b0f000401c01e20450200c0007404010059040f9041907861b42d054000244072445503004105071001c501b4001000030300c25010b0f18079140c89440c10700910010418180c1c00403105e40009000c22801d0707000150517490029400d01100c0c603043d41c9507003040152 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 108524487 1250 108523237 108523241
    0x2130207020603040f0b0c03041101050c0106090213051305090d0c141207030201050f060109050415050405010b0703020f07060801090e010b0414090d11030d020a09030c1202010905190306020c0a06 86
    0x13601950481c52403101c1101700514803003a2030b40040c0780d6403401d08500305550740c1fa0b524a0009605410842c01064981112400f9807118004160744182156140140a400509000b9521445200d200410f80031030101c1e182d0b0140f148203030310306001350608685410007903542c00c610b09001d580e411010b4003c80e00313900b4100403035a944140c50000540f11011494003e0a40744001d002120b240001c10032701010b1b03600900d4074002c1c0ca00846011400541d821100702e45000140c3c031059100341044d000056110034403005041d840c0c0a54240c0e201303100b017501d25556500540c401c0c00c0c001001500100400c8069501c2440c4c07800000002203080c1040e0f100180c00e0710071202040c000000050248848c1410402900303410174000e040c0140403032030040c01240c032405a040010031480d0001007820220740708003000d40146900800110305d582c1c440c41c0d030180b8080d03202412404100240e5001c41c0d5450000e60403c8001c1141540c3e071005420f41d81c2e028003079003020134442d02c180704404c0040c00155440c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 108525737 1250 108524487 108524491
    0x10c1a090309120307050d0e030102121608010b0f04030f020d0210030b0406050d03080604020a0c020a090204030b060402040b0a030e030d0f02481005040605090c040608070302130207020603 83
    0x103802161611840e400b000700f4000c080c07070030142c154405c01c0385400094000c00e219850020500342603003a040c1641c0440d019102c1e4810504488592400700300b4174803422009410440300303d660b41041c6a884022401d40ca03c6080410103121106000410018507049030741004544064034480c01c42d0b10726400300d031204000301343c0e030700110b0346403011280142458445c0b60000e02e8111104c422003c1c06480c0070300801c1c006044940280d400041d40341c40507000d19080701c0b582e030340a4181d050303540d030f10b19000c1c0003500a030000b2208405403e01084061a01d8020340e01600c0d2104d00c203a181c04615039060340200074002d1000114002442101211740d903a1240c018000ca0020026941e071880c08c00d9003d019280e914504514100c0b1020002c00b887c0740b0440064001050905000d5420400600c03880d219a0342c81078505141000c00300700800c91607421860054244000700c2c0c071a003440904000540329903019648072548603482c01c20252a0890f40040b0001c4402d20041c5070246c207402180c00340e802 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 108526987 1250 108525737 108525751
    0x204030606151202090a120212190309080a030816020c090a0608060f040f0f06021c02190e01020d0324031406130b0106050307020c130b030706020102030114010c1a 72
    0x11410b26112590f0001c2465582e0031800004619250710240020460600c2d4047c0c10050301d4080c00c1c040454603443c002c02c404440f07104c105c43d4411001360f141180005150022000680c20303241c001402c680015a2104c1e032907145d12101e0466480e444400c015004106030281140704003003814100752038400003540103226102012602f5400d10003c680307003100c06465170309039810803001c02010411200320307500880d81c007441c01e000081f42810100040e000e80d01040905002c0e0702c0020315059120703802410981d052009a89001c4e4240d441562040c3d950f840d000c0c09a008031041c041c1c803910030f40c000045404400c40e05001d20441d901c103101911482d420849150404110007a45c05c4c10400c4010f5114a0070b100104440341c041d5900c3c04c0b6608107124401c2030000100c0070a400500078001c114000d4030142c80c580307000342d5021800c0042c0c050b01e01c403103009004d015000300f405032040c001c59069401c2d000d1401090030495004583d44c1440b000d0a0780c0400052650350483c200c4400004d0050720 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 108528237 1250 108526987 108527009
    0x80903070c14030d02120d020c030705010f0504060605010813030809120f0409110f16060609021603030b0409081909080303070509042904110c070e0a05160818010204030606 76
    0x192a0034149400c04c1e00a20109540c440080a0310b0706d1032050440b005111509000b44c1c40f682c071246681d2850056501c005c01c3c0d542042c003600135150450b032000d48200d010740780070b102003a6500e0054500850030384460301c16000000030a03021074011450f154004550b00d045a210903000e0380c800f0580e422281141008000019040101d03500d940102c400d00c040741c51105142158100060150703116088031503048100082c0031070300b4841240d0144008003420a030565448000300441e06d60790715a4441240480d14042c426003013400c281c4541000658460b07902441c0520401c1c2004080c17501982c000d04100c43d00c00045a184018805980540f42b6600d801c0d4484c42c1000c1044141c0e40303032150b0394003a810005e030400c000c00c224481d68100c0c040d00341c4001035600c0541c1114006442821201d02041c40b07000000281101c206000c1880b035507c20800b00059210400b1102c007004250049400103000040807400c000310043c44000403000d94000140b03400e907030b591540c0648616900a14401d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 108529487 1250 108528237 108528269
    0x609020c060708060307030609050114041104060806060f0d05030705030c030d0506090c071112010c02070905010f0312080c1215090610020601210803090105190204050102070501080903070c 83
    0x2a00c2048082d80050903820600e040e4506040800e58030016448081c126036140d0811000380202988000c01c00300241e075a01301e151902c1c3c02c04400461816050500503031414400160845012415a01603000241292400280307501003004a02520800395040c0c0410412180010300c10001800914907c034082c0d5241c2405820f08030450382c0c02050180500210010080020400d5044032202d90b401384c91aa540759200b0082465011041101c2c50550311300382e08001c00580001d611030440798807041c01d102d280c0e201e0131b01140074005880020175104448200d260400d01886200381c4c0251485c036a5401c20010040141c01a007050307404000200d440313086036205003002d52a80e60b1100099922409807400d10318025581e420510511400040f40c0c07511081402c140700048200743d4103c0039440e00c03070078040ca100d40244000d03162914140080d018450000d1228000e80d011950141c02a2103520b1a100c0191200007005007102e425000422440300080c200074002005402c0d0401c03002910 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 108530737 1250 108529487 108529507
    0x30910080118020403051e010b0a08010f060909350325032f070b04050303010501030e073b0a0903030c0203041211030a050d0c0314070f020f03030409060902 69
    0x310700b8000310645004002c203002191000802c85c84003240450b0ba4460b60400340c2011b4018108480c0c03455200341d21041c00106948150000450004090710400c031080e50348500d40c088984070741c4002e0800c04a0342076186808051030b00700c10180c104080745080a14400c0c41d01c1c03005c0d4002c030340041104005801031019001150700702e07107804030181810000090410551030125203d03c00006810140103e0070f84142d0403041907500f0564420404c030502d04091901540326007013402400d0000f464022222218140010301c08200c41004640100c07038040b070442403c504610071000114800d41d4040581c440f00700b0300402d40300b046d0500c070025408406190040c291054814001c0c1154021321040c444095465145460503a002c140c1c028480b0320340d004070342010452100504180210303a280740265801941c2050450300c41e517148000c10720128000700d4140a45c1901814000d2403179090300044c03c184000402d44c210040480303092603901c0e100542601c3c01508842406a0003150300300311 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 108531987 1250 108530737 108530759
    0xc040f06020f0c060f071b170c0f10090e060d080d0f0606080105060a05030a0e240906010b030105100309020406080c12070302010804200901060f0f030b1003020c0309100801 76
    0xc102c000301c41ca00e03e000c1400c105170855006100001d0301175203003220400705410b103654000c0000c1c0303003000c918103d400b640744c00941c0f03500ea0070601500802e2802040d86507850100d400c10010071454440c1a0702d00c1c10501c142c184000300a2215030425001410f41012420600c00b400b1084480040451214001c5c440d800548000703070f00c010103000d0380c0c10040c0880d84c0c4a9040d00c0c6200064909940c480d40d48034074440103050034614000c3c043c000c010841d03800c851486002d0041c41201d240082054540d000980c0d582e610908c00d5812301c1000703000502080c901040c008410403520b14011a2103107083e0005000c40300281d00000b101d6001c0d6002010034100060f84030a01450980904150340c07131600081c4c9a500024001044484a8060302c403490004140d58500c091000d04061095a183e96002c2c00c02c01c2e09914100204564008050041e4424040d440b003240d00500011201041300800f40c020350130400c40c0250783d000c10312915681d83c4480c62920300310b80c41c80e682c0d290654900b04021701 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 108533237 1250 108531987 108532003
    0x11070c15080c0a0f030605090f090708030708040311010203090a0902030121050a0204020a18030303020a120c0f110a0503120a0b0108010b04061d030a03020a03020c0a03030206010e0c040f06020f 85
    0x103000316402000441200c02090b142030150302d01345061543c440000031001800590050795115061b0310602080b42c000d045000c0c400c00c3c40a044845154880000e1592070094800061000034100414000100c000020391401081030040340e00b4440c000001036000441500b025041641c00300041146501002c03106c02c14155511000041c0002d54503031030303141c065101020f80102d80001e04200024820101e4400300040c02c440e00c2400d544a00d4010701950100c4540d10000d80000200e03520300000f07202d866113190503516405c0c00000c20900a54070360740e0f40311014040d03004003450140400c0081c00240000349814140100b14508a00b182007140c1511007610304100303c074801030089030002000c441c15503115080200400c2c00c40120a260014010343c007507058041c99403100300309500055940e001d070b4401c3d02980c0d80a804541848102140c6100280044c2d02080041203504da42980703240d0003400302d1000a1400761a0b91051181448a0344108010307881107140818404007441060 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 108534487 1250 108533237 108533279
    0x80f06040309060c0305041e08070605041508090d0f0302090a120b1303020712111206071e050711030c04051303270b0918180106080106121511070c 65
    0x440112185d280202203001d1402001c0384101820b5501320032050000d5004c0042c0104c00480b5416501c40c80c0042c180c0d00f00e0702c07820440145007500320208c60b01035061035110341c40074401044252a001c1c403c8030160b160702c01407414154204982d0b009510b0b50781cce4007c040c0101d14181c6c0c1e40984289428016220024003216981c00700906800010382d001c81c1083c00c40c2c03030a400c0c540aa001038104010082c05100c3e00c664408180c1c0705030307255094003040381c03031203040c00c0e40315502031042d8201c0c03441d283c9902180e28030010341d0810541d40094441d01c00c403191a0005000c80b1440c0c2c0d100302c00f080c121201030321000f4124000c010b022040552000c8150224500e11131a1540c00c1280c00d52103c111a45004201002c80301045401315612908031034800c6640b1030b181d203217450414150024042220341c1d440c0109509204003c51220814059141207407a00501148082804c1e1159409036903020304510340c568a548581c0141a0403601520049015000b0403820610f0708110312110740b2110495 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 108535737 1250 108534487 108534497
    0x50f030309280905040b22020105030c0a05041211090a0e060114120d030608011d0d051c02030106080709061701030311070b0304050307021507150213080f0604030906 73
    0x1100c03460b15000701d041903050b002000c2c404101802503082c4207003601a00400049442d1100b0001030040c11141c0e18011030410303064203002030b0041f0f410030708000509000390104404101181d0800f0f24480100051582c6141160501d0b88030385169000e5144c508050b564032800c0c40015001d481e00c1450107400410100e420002540b40203e0385496500510801c5201040398010b06600d890780e0080c60010428101601d2500681c80409001029140542c0d4201d6203408040d411040d4400201520002350324001c1901d00c2c41d0150446143e440500015902181100d880d00409041d001540c080d08050b00c410081d480d10700d90003042400d85030310002c104030b02520055080c401000e425410b494152070711a4007500b402e26260714050103644010a1007030000100301c02e1203808000740c042346208582c601602e42010009050500a85401071300040d1031003c0c644144000740d008000f910003460b240b07940555240f07641d41c204000d1203c00c00054002400300010143c3c400039000c0607002c0c40c104 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 108536987 1250 108535737 108535747
    0xd020409060b13140d050f0703050f01090803060402030402040204050904240216020f1c030509090108070f15030b040903030e0c03120a08061c03020a1e0816150608010204050f0303 79
    0xa0030003c4030750311908010318500780c0c0c01a80c588403041404003c03a001402c4800c2440500c000ba07648072601c0c40181c80c1030240b402a03201495040c0502c0b502c649d004101c1a003541c0340d54003044003c0d8405842281d0095007040002442d44812900d00e00c00c034041c400c00010440f10309012170742d0890203005016601d20400240c5900040c05000304076581c0c050300c004487e84410300115041e80908611500d401080c41000c10402d94800300900500800b41d402601d540d0340c0740002030303981300507002d100300f54049118103006201a41c016007500c820030746030200d130080e804008035088440321441a40000d40701c61000707508000410101c031105400341c00904c1c10804a01620002d8010b0301c0030001000543c101262050b07580200b40700d040342c50495101c400e414540f401954807042c0241c00c0301e4001940056102901d007141c1690714603500058400c1c5802c4503042c040b464680c1030481159510418850302c69070000500c52200a407880100050781e480c2048100003040521700b040070312035401044 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 108538237 1250 108536987 108537007
    0x6081e030715180503040906031e0512030c0d050c03040201110a030807030b2b0b01080a0803040f06140a1a03010204031509080d050702010507030b030c0a0312020c03030d020409060b 80
    0x41d005482c2600b0b90001007071040c440d914240c2c2103d001000e80503100101d0081000c2903694040001ca83c460b0007011104a400c0040001c1601e480101415a421100d00c5000040510000716800705210a42609c0c01c142600d12a0483c0c0707090b182540c9002c808410001156002000e564042c5045401004141a40d903030040140c1e0004007d4801c054884201081c10f0b00d5024050240203a00881610314020401c4400e6038601010300584074206042d0000448400c00314a40e052603410024032865a42c680d2554041410710b15002c0301c070980c1e2240842000c0d038040c40060f0003000042c00110302001c0c042d690b101003880c00300c1468420f920410041000034500d51140245140f90072010605480d141020440ea000c3c04206026040c2008100800c90340e06500052250490341c0b804c12a003a408420f041d0b9032861809001c0e0010b001c60024408a40621100c0480005601c12140007208100210313003150040d98118010680100d000d01c02070305140110030203403601c40201c07030030305a03520703 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 108539487 1250 108538237 108538253
    0x90a0609050a032d030209120f0303150d03020709051009150806070201020a0c020424031a0f01030201050a110c0a0b0d060b09011b0c0f0b031006110c0910030606081e0307 75
    0x303444021706500081c911403e1b100d00701e00940d00030301c050555468807015020641c0743e80c4219461015003040345500e03c620710304140c1991a294260340100422803e040d1030750006c0501500c00d06442824010002c0e0000d418000c90002002d11101c42c504289400d0341c0c2e514103000070740104196401881b10f25411580440d0082c00d90750100c0300402e020024040c0c5008507c4002d400615410212201005111806441055a1070100f14400040c0c1d10b00c103603100c90440a000c020300084003045a00c0780b0611500074009254000000c2d0362032452140b0004002c54515441000044004a00c1e8010400350344200c0e4010918410341600c0d01e102080001c284a10071002c401c0e00b202c00d518500240b043c0f602103480584441c0d030441d0b208a4951502880d260000c49451102405010b408190741c1d00c01e040046d4a400c0303c0c4001c1803024146003c0109407040103203001c1c40c91a04003000000b00380c050040000410f4458007400c00200c5400c0d00c0c11120201c0d20014440e03601c20004100091814 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 108540737 1250 108539487 108539567
    0x7120801120206090402130b04080f01021213060e1905010b09060d0212010b030102030106030b03010e0705010905060d0b10080717010513020a20030301140a140108090a0609050a03 79
    0x48807110344d15018040001d0080c0101c6907200186000003101241040aa0300100b003981c0307034441118082140708549600b030748550300100701c0d204035007030100302408500814003001c0c51240c0030103c7c1690f244601c5928150803006440c0171380205583c00802d01c503083c81040359042080da0991064179010020545002801d20001c0c06400b079059450b80d290829400442e480364000e00035980d0307503903400c401005441d0002105200f9460f08003050700218002501c00212401a164100e01602e4001089940e4015284101c40c00b5140c01141c3d5943c0c0e00c610701c1030340c02551521174040ea401d04000041054225120580c2c18501e008018080d643d01c00700112064901c41e107015903a4640d8040407111301e41040c0100008034001d0012008919020000d0f50585121401701003004403140e00f0090500713020312861203a40007000d02019294843c400c0a580015014200d0700716001e590384070000c988803441c0948413600000c00e050101580240d5440d100c12446424a444c40300c7c1c081000200b000c0c2d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 108541987 1250 108540737 108540739
    0x3170a05101406031513050c03100b1804021e0304141c02060c13080607090905060f0d0f03051c02040501031107321e07080708061306110f071208011202 67
    0x40c50048400305ea41b01082e210f044031814105004500b800d80026031903801c10394002d41c0b103e90a88010030754038040d000341e8504298048022400035180c10510000790300c081001c00c00c11000d030307904490740d100742402180034074880d40c00c2010801c0803404880c104401581e1404840801d0800b810107503a000a18036080740401c00036607500e00c0701000c5c015048509038041a079500a803010002c02680100c051000c403680800280709681d6180d0802990701222241c61364400440d0200001244106031a401001c0c0729040017850501400400519503807240c1c8003483c50b680000f020702043d40c0c03500641c2903111000c41100d0522040b90740709441c45012000000c100c60a0490102040e81208040724060413a102a60842c00d044062000c0b14182d80b40084d030f5510804c44001208040000c00c1002c60350100050541610749800c1406508024841620f400c1c2d1503000820206101d48010800c1445001040c1e588074180d240c8101c040840310a1002440a07030070042041c00407520080c00340a078 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 108543237 1250 108541987 108542011
    0x60a090203060406030609060b0f0103051902130915030311190b0402030705060c0d0305010503030901020715050d0c080712050c030601050a18032a030309050d03170a0510140603 78
    0x10b9010007240040c52aa44068800e50402c000d10040c80500c1c0d1201000d143c0554400740580000d00054007903d60070355a40c08080c211706281898450a030b4084c0401004410082c09596a80c00541080d10025105500182c041d11020420035030014240c1455504c00c10140000d8407120042000e181c10540313001c0c1680b90f4403c00103045580c20711182001e818000c1419843d400074424640d91542e1052078076002c03d2030f000c00414286000000d450284034160300401a207410601c036a44da072a415000b0000380082030048a44010450048403000c0f0200c0d0740790030151500c0040101880712011402650f42d00c2c0001384803440d04101c084940c400020300f00340399600307484813044a000300c03c5103401c00c44100d224000700c104030009044e1300440f6007481c1ca40040b07440d6100b01d506181d40c248002808038051010401071800d00b100581001d42c000d0400c080e4901040309050002d81040707d4401c031080c0c1e10020041060400e85118003c0d00c120340c0b40450b5200c0d0b850215440740b0001d044880a12 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 108544487 1250 108543237 108543241
    0x60f0c031314011d01060f0b070201030b0109030507031a07030e10050903040302060c0a05060c0a0203040905040201050f0a0f02010c0207060203070803060424060e010f0e0d02011101060b030406060e060a090203 92
    0x7182c0c00c40c0400c607030040341c8000c20103c1c10034a0302c21108900e0b401c40c2503055003440c00c000381c0140c0000ca20402c3c1d800c02c1000c1481c08803d41c2c015402001608503d50510100c6400040811424000304008600440746501c5414003d030118696042c020104410300d0325000e404008401c0001e0788c4d403040c11000e100014180c40b41e4054901d1401194030081d0701c900d0000e01411442804038040c60010712600440d18944c81d940080441406040300c02c1e001a401440304020030303012070300929001401814200c0ca4054074240c4040c980d44421240008121030207441c8102e181c0c2441040030403043c2d480600151414035100946a10594030040d0a00d18080041940d594942e0f210030240c61202499910060929000d84240e2006d44600008220301461030701d02035000d81c1d86408003c0300d595501010300c181a08004900c0342e5500242d04018040b510610308103824400c4102074070001581540300d185c1841d00e40306540c0660080c2d102e01a084080c0325158441840c200103846000030096226 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 108545737 1250 108544487 108544493
    0x50f0f0606040c0c0b15030a0303060e01060e011b15090f05070f0b0d0b06190c120c11040c0e06220b120c070302120d0501050415210501020712080702060f0c0313 71
    0x1b550300ba103541d141c047c5a103200c0030180c06078002c804442d2000f072011442d82c0d8514003603400c0e411103041ca901058898440c202d500800441e060f4030a486600030030b0745100c403c14100d040320301e9810200e40a00c101c0c9002c2c410300804009480c010b150703c0c260349401508101e5680e200d4014204002c13a415110b1805401c9640e40c4001e5940c045801105071105903280700004248800b07481003a1802c99580b6258038007144642078684000d50040031131500400c0070000c0c04010300c4a1300c10101040442c1c83d10000c80d40d035090041c000031303224002c504c00c08812000060b100d007040e94800031124204100c5103201c0004040a20760001080f01a82c0d10b0307140b981416400c10582a509041801e0002070b6500b40c0c41d0fa9a00190584109690400280e0312201886550402e0303402119001c0c00001006402c54001c02c4410072424403030720025003049400e559044541000c0044100400c00e90030030008116410814140e000e01a804010308505100055140f1031001800203034900c4d101c800c025081c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 108546987 1250 108545737 108545761
    0x20a09210201020d0309050a050a0b0106110d0c1103030d090c140619111005040302010c11010917090607080705060714041208030a02071b03120306050a09051003050f0f0606040c0c0b 80
    0x20700c0e032700002039400303001c154078201e10001800d00505001c211840c5400c0355620000569072180103190300c0d40340d0200d8003512110311003105105010f6152104009840c194862800360794002c038481d69010081504084441003407241c820700e13590240005200c408511003d03000b43d00c11041d001c4c2060103144e007100f4445420292206c4040303800d582880148020107505610031141944107607550f0038400b91070b0703680070b09843c01c00740013915034160032110a45a40005d8001c001a130b0f0b00610003898550307580d45030300c19030300b01c00d00580d03980d0007081c01c100d0b810390400c907030040c0304d0200e8098524180c1810001044202d1580d0003502000c0b012001654840e4117a04075502150414011a0900040101040b681c400c9000491700030002400e800d9400d8028050001a540c000f014445920b00b0071070004020300c0c00508003190011500c8000000c42c005100740c91242e40d40340301401e102202d20400310300d8030703d01820050085240800c01030007190700080b0800083d0340981907041545400c115040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 108548237 1250 108546987 108547003
    0x1020403050607020d02011b0206151f030e07060801050607140c06072003011509050907030f030f0e06090a0e0a0906060609090f0605060405060a0909020a09210201020d030905 77
    0x148200710a00c03060580020b40044555100e034001d00c60710503601c048c0303030421070b0305020040503030b1005000c240e084a101c07240b84803c1e40060b00c51625202881079440d0b04048444020340405d6490001581022003808030710007815040c100403190394034150205070b1500c5511005420450100034039040c8610034400d10580348801015584ca99146003001d007008a0301c031483c00c01020f10b12012030400c0c2018010103200a40030518040514a0141884043c003c0140b11070440d005941c00800003c0c01c008500032080e0096403049548901690302908841081c0c02c0d481c85103c003804aa0940d69900e600002a074020810640307054480a060781d018010191008043c2420701c48041203103076004500e001100c3d007070300040c0100741e84ca10000c01158068042c00b500f02d50b0400041c052030410000030110a0340ba0714000325999601c4881000300d0304021203140002d01245020050102c491050910320401c80f00c2400c800f50160340040d640702d29450341c01050581718003405003400030a0058036 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 108549487 1250 108548237 108548243
    0x80f030c12010f08060f220809040f050708010b0c06070c03030b0d03081608040506041b0b031005041a01020c12010b060c030901021905031615180209010801150b0c01020403 76
    0x1845542c43e0030032205200d101c2c1c0607000e66071042100040752103d034a25603e01451000c13042d4135440c080c00c1030484040b40f140d0720940d542c080c100100c46550700c55110303070058050b4220b0005030b5800d24410040204074182d0242d65045028000b168075482d000c07422580002d480d0502c071070101031074902a005000d0700000d40b9409001c3c115010203068001c41ca0174810300740e00c038040021640d030f40300c281c07186041510041c0050340301c400001d00007111148540b40c00c10004c0945032009136a0035210780240d0044030001c00000c8404404c11042c10540603021100034005085191101e030580000d603249a00c45e070551191103001c03007200184800394003152803944040d01c03141e0342d403281c0310344140d40768040b014050051045045a06241807941000c064841d40030300518984180c024001d01410681c1d1f0003607a42034202e580c600840070852080781006082a5040c0c0031030100d900422590711016408a0320702d0341806c1c00200b076145010103920030b40e0400080c042d11091211401802802690030003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 108550737 1250 108549487 108549517
    0x1030506030d090e280b0108010f0305060402040b0102011e0c17160305041403040f0302090109020304080412150e0d02101109060f120130020904030503180d05071e080f030c 76
    0x85d041c014880d8101580c40003080c1c803a800c0e143da848844001c1000148409002504030718046801071170640c1083c0c00c51801440081b0305601001b8061095445400700c9200869a070010f500070a03410441920b007070114504010a03134a4185010070f400b08441001000701070380d400010301041246117814403070301160380840313440e030f07445604a42504002d404182c1c45024114000240b5220900880b0b1269074010001420716151a584c0040d8804084007181c00440c0c0e0440300756100e140e44140111890460002c128141c100b80d0045c0c200071280c1c007400c4c4824100258404443c0d0440c0880c1e510010580b02c45603103040064540c5e025008208820020000105c00012031025800d84d10402d42512080300b100c4411941b03180750f210040303c0000b074120384100c1c00240424080e20195030f101e0700d001540046000200c50369801c4c0b140c042169008120085100024412034170b0340c2402c0c0b00310301031103640703284c0581e1240d244901a50207401160500000052a00100da0007603842c010743d80225 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 108551987 1250 108550737 108550801
    0x90c190c06020c030a030506030c030a150615031d0105150f041b0c1e1e060f05010602031809010b0415051c0f0c0206100306020309030f03100501030506030d090e 71
    0xc2d498495220315180c0c0e00281c1400082802c5289c041070b9a2441c4800400404000500765540302c0c100c5d6801240896481d500c1800080515080110300103201503a6400100014141440410f0081540c07502055038034040030401c07100d100c010f07024000041212560141c1000d0000640030303102e0000103410304065588131450890b0084a0305516030f00c03400320210b07500840310b8014140403020801070065556512054580d0000011402c4082c1c010640894909500d0602805481c1c081c0c1c01000140c0c800140b070300c1402c141c03003c03030449040d080f05d04140075403504444500b030307000798065603254031001d980791024280914106d07a0007004242c10b5a01101c81030002c20000c0c24104010481079090940c40c8004500c00702d025031182c1c4078501822491402c54807004000d410082c110302d41c0744810400020601840300246110b0200f01000741d0040b03003060001000e495010709118020717802484030001032504104c1c1c980c00c1d03c1e441c01056066a13203040c800c00002a5000000340300c2044410 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 108553237 1250 108551987 108552007
    0x120c010501050108070807091a07080a0806041109030705040b030c03060f0a0501060f051b0111070b060a0504020a05070f110a0801050411010207060207050112150806010e06090c190c0602 82
    0x300904032803098032807040c169110030095862940031204400040d1746540c05010703614404a9009891a0000d0b0039406d0803c16a00c0a40701d500c41e00f0309102150ba01340411941e0b25107802102ca000580f0724650341800034000c080707560b8522600805214548178002d9640648042180d1000500c0c014212001418143c064840f140710646800040c941881c00110b043d6006840c54002081c05503121460186040580d810b920101340d07952a80d0354031018001403d04600c0050036100b40500030407091070030a82e00304a69a20b05500043c0140c1c014481c1104c002c0d007003c181c45005810450198155080346040342d07580600000c0c1d140c1c400070001d0301080000303055005a229034030400418208403140e6006907034948041c40380100591060406000d00d5100d4402c000d1104804040421070325580d40c3c5034400990550800d071420b610000040000f01c541c00b82c0320381c2112007961055191300b446010700c00188580d107440c41415440642c1c00c0318651051a070300d08400c1d0400300464581500b95 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 108554487 1250 108553237 108553241
    0x60f0507080403080705090114090a08060702010c0914030606060715020f0307020c0301060509060d0507150c1b03080403060902010c051516091d061504030c03060c0e0a090509120c01 80
    0xa10150001801310001450b41c034041e004070381120720161641d107031840c003100800c881548030088042d080054010000350110b400c100240c0039000d41d4001007200705a04074014000a0300d0741c40030b455590402d401401648012441c0e580141c0300f55202651040d16041282e00c612001e43c50200342880007600c0012081217802a6014060340da00380c0d000a403a5030100350a80d03803a03010f0030ba400507040000c940c0500d081011a84070501c60030944400303a9440e14880001c5001d00411004504140c40c1c440412200004040b01e848003400310030a014119242d0b11000d0240b400b00500031580d800c9d0000035a03000341c03000f107003459100381145d569849a15003005004c2042c0c1d17002096079031030f00e030b9280801d00441711442a00c0c000c0c1087c08014000e000007890700d480c00b0b400309420001c40104040580d000c800200091809807034030340005031840c03601d142110042d103000410400301c0c0440400955a2200b4101140c2d26280301050f107071214841700c4e051014404510000d40700004851840034419 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 108555737 1250 108554487 108554491
    0x80a0507050a0905070f0302160f0b04020a0b0408301b01050a0c021b010311190e090103050a030e0102030904150905010803033112020c131505010c060f050708 70
    0x340c400c8100b07556035116040654605a401c2c0000c100208804002a0301c00e44c050908004a0800c0f80d00c420b1503610b84042201129000360390320804501000150b0400080000080001e04c25503462700c0e02d00445036442c1d50a07800101000b00340349403070000e511070720501902070760340c402920f03980e80c681e44005c1000300300d03c1c0f02e0075001c55080c1000540c1004851040c004990b005802800708031407214101ca91015003400c0b16410f0541d41c943c80c0f1001142d51000d44920003209191b0011a00c1e003c2010b060400d0b00d8a805210700d03a80c40061000510104080010302d0745400c054a0742d13000d0400503801c2d03000e0b0500c05070300180740844400202c0d002c001d04a0840e800b043c41007105907210b007a05a01e0707102c01c5403d0744000400789030140e0301e02000e191040c6042030201030910494841c0e5915450b4090200721070006030700403031407890306180160429100795160745d400c00848000742e0110f04401d04512903917040c04128496007090294035000800c146030150410041d500c1c0c041d1000e0008141 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 108556987 1250 108555737 108555739
    0x6020309030c03011e110d020c0d11010b180406060b0a02010609060b0310050607030207080109060e0d080115120902030106090e1b0303070602031503060103030207140a0b040501030510080a050705 86
    0xe0080d01c82c0709040c1032060003034240070f815003030503550010092980640300154040203000c4042100c25030702030079071014001000402024220b0b041030400000d01070004100c91150907498440403502c00d9480c409541c0e18084030602141169481d418003100816a96001411411000071100c9036264103521040540e034003903008100031502c40d20741c100d80e40030444100810310700030761043c081c0c2d1401a0142c00d82d240310784100c3e030540d529107880a00b5076001c103608441c0d19407190301c3c2c451034090910000c16443c403189004d0b07145600d001e000321201480141c03610709110750009600003070456604400c1ca500d801a009118807541d0701c08201c010a0fa0007801c8850340a4800c1c2c0c80c1203020803070062559954001c1c021030508076031342c480740002e52000e8020200307121541030b00c03100341e1010700c170441c000e5000350083c2011518080e10319014100502113035104413600e0001f8003100d803003e03040d542614428600002d10b0740c0c0b00c110000c440b041940080259200b902240400c010700003c203903060f128 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 108558237 1250 108556987 108556993
    0xc0b0106091a0306030c040902241c1a010f0e181012120806010509120609060a09080d0905070b040b0a23030604050c16050a0605070203030403090b0706150602030903 73
    0x1d070240520102e40001d55040c1d601d500400d012008507d071a400540c071090008052040a100c02140941902003070310300c401c58004042050440c12803278502000c8060489a4240981c40159004400d003034280c0d45203a040c00000c0c02454100c034820079141c0c51130280a08042d5401c0d0320302c13100f901401800c42d1600c8519811403c0415412400040501c03152341c0410a0410000d4040041c0c0b441c1d01c000f42018100310701480b40411a50326109450b507900c51340c4016211506142c01c1031802c0042c028110030f10141401042d00018010a0845041100075200010f00d01142e151081c2420303016030050002e4000410045050443d6500a101c400599120004c040c0340c848036800d051042091306040803401400020034508003500a5079100012540f12031402005580c2d002001c10f42d20819105907103c0143c140412000703106050708081507000070750a500d40f0b603600504031141402030090700d5002054501c00c104640e0001c00094159499019096490380b400a5880e000340406901c00c0c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 108559487 1250 108558237 108558269
    0x3030f1012050328230f0a0e040c0201061d0603010603020315010e0f0709090e010b130c030b0604050303040611030c1c0e040e03190203040f0b070b0903031303030b010c0b010609 78
    0x203100c9041184403449180c90360b074000d50094175074401d01c21405909501c1d01c002044940c2413242e48000605040b0240e44a4020b40c00e0480280300032039009405003415603140c00d005010601c2c3d28554601a03003043c00500c0700940d283c101080c09018280e000035014441e080211401a040c51000350581d2440300701d00340340da56281a90082c014040c4c6840c0c01045900780f042c03292003c82d4008158880c40d0f6000401c0300360011700460301031102000200d10581d84c803941044c1c0694035025036080c03120110380715401c0134109030000b0741f203114078400c1e582882610410041d2985041c402c1e03030303d0b0a5080c403d88580ba1421000c6402c5402d203005c10300005174001446911500d801e1042c8030349110604020b500b8005001c4170807082110100312031096100620000500445050145005d84058030000b44c071a81540780c0860306510241001f00303290428020480c0c1440400048001c4036058500800c43e012204016108140d880780e000c1e024004040010407100d400c030464204541003c07014075500 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 108560737 1250 108559487 108559537
    0x30209071b020603090c09010320010507050d050c100e06060f04090507060f0507020a080708060c0f030417220e09070f14120706020a020406050108010803030f10120503 74
    0x84030446504401c0c10030001d03100054144000615480000381048601c004043c40011361198401d030b004440495101c03d07095100748072054603d40082c0f00382403590603c8416551140c4921941c26003400b0088041500d241d40801004942d0b50409802010007014614100340707a01c50030115442c501840600c02c540240b428140702d00075403d9044405044214280002103c44105449050003048020b020840150fa20380616400410201004008052400c2070031428108010714000a245051289100800030802260350040d4003440c016504003e49104003054020f4890304028003100c400700c03080842070b825100c0240c5d80c0603084618141d840d184519039510041c00b54514900410781308014200000c04c004580d03880040400e40428601e120300d034980360b9280d2003400141c2c0030b242c040741941018424280039203400e2a00d10060360415021950303910010340020300e484e2042c0b000502c100c9144561038090860307042d4401941625040c415075a030130002a03101d1001c40c001c070050704 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 108561987 1250 108560737 108560747
    0x30108011406180f1017011b0206040b150103020d090b0402030709060506160206090301090c0608010f03110906041b121116022e0c0510050f0c0705030d1503020907 72
    0x311a110141410040e44d0b40d04400640450140070705100b1411440c0c0450158002600800450701d02000054100d0701003041c0c06204442d420f00c9000d640201041c00040f80c885103d06600c84002c41164188001c81d00048000f031107007440e03483c1124078110040c000c0054001940d4000c2e4000c80c100c48000c0d4590003040c0c00c9605510410fa4080c4003008115880c440b101a4000c416000074107682c1000a0000481e084d9007030b0150480701d02004a00508c949034011a40c5405410b180700300660785070550b590300b21001d5111001c03a1184032400d00283d140c0d5110380041d110019648008098150662405006044040d0b0703003074021800c00c3e58844001c9408000d035106101c20000d8030b07001600940a00c0001d20300e00111170807a0142c0c0400040e42142d040c0a60034a180c241d503040003904d01c90030301600b0040e5204803650380314140014008071284940030f503500301c003810860340da40d603049107040c0d86544900b0119000e04c6080c003e07030b0314411200201e0300c01101e000703039400d034203d6541940c01c5403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 108563237 1250 108561987 108562009
    0x72319080c04090c05040506040305030319051504090f0615050111010b03100209010903050a080d0b030a02150d0e060f09120f030703050408070803193204050111030108011406 77
    0x4259003400104400000c035003221354000074500705545040c1d2281c0c080f035a10742c415041510a548000709000c070aa03540f02580c01100c0000c501000790b0700f443c25210a401075850341d982e100e90f45440c5000180940b00e89010206a400303d0200321456002e4030752904804c0d180310b06404202d003259031075050074042c050004000402009802e02c02c0542041c14020340100c0079203410031000450100025004000c61a51140602d500c0b0342c4444545270b4410580780d210b6401070180e0058104180141c5960094001d070002c03a031540c0e506c840d0840744a0307000b40318104076544d55101d500213001c4c94200210312903010340b5076841a200c013820a410440c0c01e5120704200380d14610000c10004442070b1007513000c20340146c42500501d26140c1591510311503a081500d8101d004062100c006003482c11078410005c8503c4129100c0b0038040030f5404010b05007240d00e0310601444005400541001000c0d4460312441e905611019242e5031070b403007024020880c1a040750f08400100740403905602e09401a80 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 108564487 1250 108563237 108563251
    0x40305060408030c0405030d05030f250e04020910030501080d090806011701020f0403080a080115050d270308010906090203010b0a030c02070837080703050307231908 73
    0x10180d181d9a0325039482d5400106840706001050001082554040c020640c8200c69540e645407a030404000c0228004009004842034555007003810b60524825000542036424604140441680840c0420040d03c00d81d010700d42d003c04508080c449854140c4c2c0030a069802c0c91040f28110402458160b48074034031800364050a51000004100c3e072500030842c0c0d0354030030310f540c000f6050030803e404840d05a0015041101c0c2c1c1e01000c219440a41d6025404900400d50390103000c40310407001c03401800a1003207402d40300142d601c485c0c14400444002443d499081c1080c021281100e12909005192500038054a84514240200020300010b14025641a16a10249103240454845080e4020720344000c440042d80034001c400200e00c0b00c188807c084865200c46080d1030300156426010315150301645140014030850850400703d0329003420745180d96850304240e5502c2d120354100b80c400088900c60480e8101c14031010040d400b0f6041c0150510440d2001d900c2c07200b1503124415220301c41c040b1116 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 108565737 1250 108564487 108564493
    0x60603010509070207321014090402070503070c03030f030506010f08091501090b010306090e0304030209040c17150730020c030f07020f2407030306050613030b010803040305 76
    0x10300407480d10b91030841c0c01c668940101c40d1200d645810000403008484000d010445420410042207415410350440c1d494044845040704104031001818000f101c80f1120b41c00100400c0341040c5480d550704407001702c1e4100c400c480d00d41c0d01e80e1410a085205c14041100062140c1c10014015030103400b6060113000d050b110303415160b010704001c44419000400c007070114400d801106010302c00c0701c80403a02030300b140351010424401c24800541500d10395400102000c1c50003180800c14900882503030240c95048410402a80711030507c480c41403103a41084680045004000c03908100014110100c070624040001d06551403040543d421005000b000c0800e508503290801468000c802840c901d1400b030100608000c649040a80717950820070800304800c100092001c154542901c241204900403540445d81e020303101485c1e252600d080c00300c80b8400c080884c82008050013500602e0190402400c09600e5002003030601d0501d9074184003c1d0344601000707001140070340c00801203070f05481d000001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 108566987 1250 108565737 108565739
    0x9070506030717150307080f1207030c020a080309010e09160f03022712010b010c0602071a0a0f050a0b10110a05070b0403050106060e010905040c030f051e01050906060301 75
    0x40c000c090344020405070800c0803044a0464000a00b100b00303020f460302210303683c00982d01c4002e25103410382641082005a11820100c0d10b09180000c0703241407190141021038aa0340d141c5800e403641e00b42e17060000d6108264200c0403401e03042c00006445e044800f40d80d414400d40340807080c003400070025522032017002c40483c442809540540c445011a60b034910b00180707030005a004401d000004c0c40c601040ca80c45908141c0c01604e4a1a40d83c0000300305138000700318a0b80780400107071040d0900400100078940109604003805003429001500801014082c0110702e0580b02c420f000b0b10100c402e01ba42c1e54600030104260112510407140314107000342c82caa0b00005131f42c1d0103403191010302005003a41d20401c016840042c4051200e0401802c040606580341c60031841c0c01c80c00e403640d80d00b040d001c004001d98442500c1ea485180c050444070140c1e40020f0049804604070003500300c40c1c0c0703101c0c881030900080c048000c1201d4800d84250040050a000b1640ca50041122240042c0c8001e5805041400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 108568237 1250 108566987 108566989
    0x8150a050a0b0a0c060c020d080a051005010807050c0d03050a0c110601091a100503061e061c0e0109050d0e0411030a1d0a0c031a040c0e06030a0c03060501050315090705 74
    0x2004011214513800d000c25a00c0c07040d900d550980355100701d00c0d801a04484080700f151074201c9511500002030f43c0003404140303088102c081001002d8403e142c1017004101c00f064480d40140112600e103113056081c1c5803400403180c00034020f17180039a00d1002040c030707000e241d02c0003501c43c45030800400003c1c00540401d901c1c101d446c0010703101c8886000f01c0640407562031b05140e610f00350000100740d41d580310280c481c074200e41048054000030349255a0001ca12290344456503034081100c04070a004c0707141c0d584482c014041180101081e6004141c03545c07030100e8a030148000010348664031011076580c80b0140d940e44050105917110ba4001c000d071182d0500202c0d9803000c3c5600b18210480c0c0d22498403401800c00006a403601400c030304103940740d40c1b05000600c1400251011298020080744209916007041c0d41c50b95140e020605c91954005c90b18400320f0783e00d81e4280b040f200c481b0b0700301507030041d50341d241d0070040c004110a1040c40e00c01e104d801940c243c5c2032409407846102d0307444036001d4106e8a02c0c00d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 108569487 1250 108568237 108568259
    0x17040b060906030c0405040c1e0e0103020d03050909151e091618030605010306060512061305071d09060603060613020702031002070b0f010e13030e030f01020a08150a050a 75
    0x3409083c0d260060b942c42c5030075a01c032803180c0c5101c1c41c018281d01c01c0003840e01840d10f81640075960711032145141c046050006407510b0b41440d046036819990005681c02e5410111018020b004071964403880c903200740a000c070755425100745800e03022542110540c0461554000c001d03060385007681c00c400340d50001541140d42d02d00100781d10080e800e1420030820316125803030080348141c00c102c1c0d13401c0d03548006100380301e00341c410200640f0307081d038000c201d100f241083d4565a080c0101078083e1311624031011070410000780f142e0340040c101c4001c219a1800c5510601c800c20904442580141c424440000c10900d80015042d020303020103094000340017082c003441c9001c1d500c10a016a050700c5180c244030000d000b00d01c014540180600444403240c18516020700c2c081106034030106881100fa805d00a12094500009412640c503003482c2c08281e0031000071908101e840a034414a551000c118460b041d500420454400c204445d0803c00c84d107508030800c00c00048a015590708a8003001050200d10481 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 108570737 1250 108569487 108569491
    0x912050c0d110a0602040611010e030403020f0f0301060b0a050a020c18043c120807080604020a0e04020f0306030601080a03080a0f1d01020901030f09020616080706060e040317040b0609 81
    0x90000c3c0c92058000c2e45981007aa03006900110000d040d014046290290070f11070b01400d5910b032000b440c5401d155030005940450601c281502c00c803c01200340748503035400d500c800010401c00c2c8510352070707070500c50001d85103411100041016019038002620103240020001c4a40c100030240c00c24103884c1e44e124464000392000d00001e402c0e1214ac65000c2c1d06042c0c030031540c203180004a800b40c007004507280200718440b950310901e09200c40b4206008860ba0814840d9900850581740140c4440701c1c2c843c21105540071010041e0040c0c80081c944030003506080055106100a030111010345e40d856000654860280601500240d40540458560303250741e0007200301100041000301d40d0407174a80042c403819403184843d0100ea90700150b402000d5030140202c107084444400100040881900803a0b0715100b6190342004910400c0300160811410314150340c0f015070050010007035140c595002000c8050180d500350046807801590b02c61010524040d40d21565200c0c0f00c02c4802c0d1506030602640300c0e40 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 108571987 1250 108570737 108570767
    0x6010b0a05070f051e03120105040f090f080c120a020c09101805010602100603150b041811041b021509030c0a0614060a03020108010b0a030209090a0912050c0d 70
    0x2c02c000303000320700b140e8078590071640203002078001e60360000300c0b0415014996003031302d00582044c00704a10f60308000d80c00604503001528046070a00c1d04181c0c4200074064400300030031a4103083d6500040c0410783c00a0100600b024089138060081818581002e004038410800142c3c42190562094103000c450b00f5000540034201d0702142d620340c1d03001c2d00514114481c1c140b450741d0700d400401c01e1603410845600000741a210070001103095840d00c012500f885804030042d10744880006502c0e88039540210340340b113440c2d1008040300500e071400514000019940920035401c0c130f046c840c03c0c03122400481040048030b030001c0000f1041010001040000104101100d010600402a0402c0248010302c1e2241c420a4001440c0034000002810808003400302d42c00344030411030600040c0d8000140034103440c0500c2005031644880350044020b403083c48640c0790000340510500071500340d1900700b008954415540c2500201c002d0208070358034003d4020002940d88001d8414507110300415100111207a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 108573237 1250 108571987 108571997
    0x50112030e060f030f0a0c0809070519051512060105040b0909041104110a020f060702060c0f09060711032515120c0c0b09030c0c01260403092606010b0a 67
    0x41c440c80580341d02e4000f01e40d405e0603d03510380308215031103509100e1503020b0300b0281802c1c0341609010b44540d98501c0a0b0042c5070050b4181e030041982484d5106816000717080042c6030582280c2c2c90051004260040d04950002050540100b9165800b450030b6a050310303400c0031460704102001042081000d00a0425510550b040800880c20f0729503003d030075085100802c81a5032a150140c00034070341031388200c070301110740c00000030300020300d13400f080c41034101d03003402c2030913449d103c0301c61164160f40b14150300641d0100c00000c121003000078001541d64a44000c82c19035800702480c401103452050407088178030040828140900000a1402074025221310314038003004000342c05001501100c9020400c2800b09182079190001c000d00c007034260303501642c50000fa600340998203070314945c0c03802c600d018141400750390f004003426500019030244480240341781c42600e90400c5c0c02c0203040e100d12405002010181e130030f00f8100000c211984403445040c030500401c1280c1c41c0503000003c0340c00c500c0103041000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 108574487 1250 108573237 108573247
    0xd0b0306010f080706050f0304111519030609090c17071809060e03070b01090914010c120605030109020603010e040606080609030301061b0201020c090a060b0c03070c050301050112030e06 82
    0x144041018902801e0654918a040360810361450f15004055000c0c17001c01904200415802007288181ca4103d6803100142802c04107100c00282c101c111142094a040c00202d20344d840e40d808039449104a20044d20308120442e01c504112007542c4008402501c1d0a0343c0180c00c20115034280d070344800c01082c0304142c405040d103940b110341241081300c1c107032000d0a481d0307083d141c01c1c0300081c8210381e810b2800c0d2000b5403603d1250703030b55204141c4051084480540d69a420081841849010101d0440c0100000c1002ca103259002408403060818801e421525041d00420705050511424003461780052000d41540c1c6090b030000704d1080010404c4628640ba00da001070048000c0150f01d000700b03880d0015503140d44c1071038030050000b00a14911864052012051401340c0d07004640d1501c22401034411061030b0380e94000520290619a203c95039040e00091620748041020014081a070710580c0c80c0c0d041d0660310004c142c2070751000c1c050203a41451014003003001900500c40d00d0150007028190314280 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 108575737 1250 108574487 108574489
    0x10f0201060801020a0c050c03030a080406020304020312070f20061804020f0a020a030810030809060702030c10111015050d0c0b03070804020909070e01090c020304030f0804030b100e0c0d0b 83
    0x685c1101c004000442d5265810208002081c042c0390b201c0e240a5004508100003024003c0c60000041c02c0038140c1640040030130203645050213000003840c0404e02c2251b540f402c600e0450b0780801c03404015505602503107072022110049521140000000500481c20508003100100b000441d0b42c1c1415440f0b54200103040d07034071140708050001c00e0500d4002e04a40300e810300700a40030b1070004025020b8008150301c24400251170409682c2d81801c25100540c50300031510200e840c0c4500000301c01d5008070608103080c1603c1d130284107080840010010f03034160400381040350094603414005201d20701000d840c103010074140a0001e03040d01c0c0c045c031440c40300e00740c0d00e0b800326880b0760059070100d00003030344c08080005608005802c25080722030000104243c5252402c00301020f0418006c0e107510340d440c0d41c070b070500c401e2003001a03901940d002030300b0240c1c0902c24600146182d010344000c5442101c000000f54010381c0c0f180c3c1800880380c29010107086540c409020300030950014100b2642c00341c3d60031a41c1d0072 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 108576987 1250 108575737 108575741
    0x609061e1f23040306020c100609020307090e09060a0e03070803040305030709051f050901050c01050118320c0415020606040b0303070305070807080f07080a030c0e0f010f0201060801 80
    0x8208144071062108000201d402016081c400010030000e81e1410081d071815800c000c1207504417a0480c40041c1c4550040d0b500c030381402c0c5880c2002c50303030505000700481c4480d07003580110b0090020341c4503031400d40d54034448501c00300c41c01c488c81c400745d8101000007055071f000e6401c480450345100040d640703000b01c1c81e514580540c00c155400d40c0020b43c040100708903145c0181508014041c21140340382c520300400c0350f132003503100e441c00070201300b09000c01d1740e810b01c1c2d0145007070742c1c119540840240030568484d21f484644992810400504034100510f1a02c0300d501d0003004500e801000c0ca080e0302000903074040301c400c50400703000c0480c00c4108010004607545034488444001070300d98060034041c01d20360100400d40e881c01007440d01c660802c2200c1c8002a411108859100364088492505c44607181000c0c0d4040c01418246941c01c08001401d00800c507507003006042c0446140c90170018070b000d24908440515081150300d41214200003804995030244a1030b41d0042510700c004140da07600c070141c10342 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 108578237 1250 108576987 108577009
    0x11106040803070207360213030b040605010f08030406030902030a0c06080708071e0e030a0501020705060403080108011808090a0302030f030a0908012f07020301050106050d140609061e 81
    0x9901e2400700034010039550502128000340a280c010003905403904007503101104032182c0c10043d00d00168880c52800c0f00f039030156040000d0884003924001d0392030030007103015a402c650407a807807440c01c03001040c0c1900e40a092000c3e50200801141040e041c00400c5c1c0c018006110140d034980f06501c6000001800d1400d01d80c0500103684d11141107041401014114040151008081c4541c00d859061842c072032000c81000810325190450070352040c80017007401d03d034001d2000761a65000084100a11100003038240c0a80d10983c0ca614180e0fa0b101680c900300c0b2041061401ca554040704d85502144041c006850348440c010300d240003460780d035070010346880041d5102d20015000410614032070364001e0a4000102091030083c00040040e294228030f02510018003080328400f00c4510914024000a540301c0b154050000c0105584417400a00310742c2122040005560400325240756114800d104030340605005407000c2442e4860400308091a02008150081c0c44c0751201c0802180c1e5403280021 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 108579487 1250 108578237 108578243
    0x418140411011704050c1011031216050403030903121b030905011209020a0e1f09061701020c1e0a0b0103060506040516020718061503060e060414060f01110604 70
    0x1000c039000000340c05480051080803c1066400400001c0384000c15080c00940045414a2814003180030660340500c4120b20075006100c040303551a1110741c100005801f07880b00c0c1d03030354502c07048140008807443d20980c00020700140c3c400104000060401d201d20340064007900f0b02522658038006020452001c0313500c1900040c203400c900304840e50308011014510051b014050200c41040d40114240c9022889191f0740c40c1800d20005900110680000040c4500200780c1c0a0090742e1740d46147c0a0f204a00500c0001810b003c80c99484000510846610300c1524019010100550040d00c3c0e00d44e80c0d00070804050300030b000307101c00080d0880d0310040c061131040c940064a418030b00140012504000c0c0a046071202d180000c00e10990006100001c031440850340507580764020003070f403000d0140380d40504107540f2202a41c0b50714642640210041e02c41c54160481e1540d914400c10080d01d4100345200340032910840402d0590418490718000400181030442107c54851480791404208640c15 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 108580737 1250 108579487 108579503
    0x1020c060a0b01090e150301020f04080c1c050616020c04020c070e22060506041d0c0411090f010c060e072c06010f0e0a2d05031204181404 61
    0x304502c0c0300c0c449a0003400e192078030880381003403c44180c00c98041c00c40415901c004090711070a550940480391700c2c6007029200307510345030350303084e0344c0d030754182c0450349510403d5411036080c4e44d805890b0712485c1c000d803c00010120f58450500ca0050406984040421805400307494101c0c0e807114001880071a070380f03800030840301e86480300d011010f40340a0640080c2c0c2c031030a6000310a00648444e07800c19590090000980381d01e6030000100100902402000125000440007440000102d22444184020342c1c1c24410b044000c030300600940f144040050344850104101802035210300d0702a001603208110005904e101c3d558400d141642c2507210010800c034507030291201036410440d404800207800356080071800d0100010b855001200c2068007005120001c100881d44c4503001c02004140502d1140c04e10028004486400b1040710409454032540d103400147c682800079a600c80070307036102316050a190900750030481400078030380c41402c2c03a919040ca0444002e003091703885018512034640 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 108581987 1250 108580737 108580741
    0xd0c05040218011d090f070c0606060c0b0f100605070204110309210f09010e031509010b041d030405012d02031804020a090e0a06080a080c011d100203100801020c06 72
    0x41c10030084e9450a100036000b0f22500d0300544401020f1500f10f42800394205107643c40c4001111304102004000d8507103801c1c2040000d04640082403201300358061503140c6801c1d42c403600f020703900d1071042da4001200f11004070104207140c40342d005051454402070000c03d400e9541070304110f0542040c0d800c1541600080d0035003482000c542e03070156404091b040d24604100140e80c402c1e00600503211032a05110380100c0101450b070303050160509080342081484070b18100078051500800740c00080a01a40c608510125401100021a00c0c040802002149894109001100c0009040034141200c9007142051000200c40c07809000c9800c2d000c1d8001c0d600c411074038050681c4214030343c16080c01b036881000703043d00f060b51101418041e0b403050407800c00e01c2c1e1203140003440103168a0740004c3c01401100352840c10030090b4001007011041400003806103040b4030b4803003003043e025007010b08d501b43c4c410320640d000d00a542c5c024540c403485414010014a68840380c02c1d080e17a010305501c446035000581 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 108583237 1250 108581987 108581989
    0x1090b010e010e010608090c060304080405060a0f0305060d0c05041109090c0903011104180915020406080f010e13060923160621020310091b0f08060904020d0c05040218 74
    0x824010081c5e0b00d031290140c06c7c285502600d829441030224010800003002805000c2000d080313070018031015024581d10508824000d046103a0000940c002a0030100031410600d03000154202c29034004038903015a03403406007007200522451241c6010480e01b4029422955102040c8510400c1103041040e03030340303855030304240c210b0709074030107403d20100b003840306001881000c00c148403444030607000014400381600300071858441c0595810022400040e0100e002035021000c140039404441d21410300d641c0390f100c0810514070482e47c40b058040c1c2c005481d80440c0c4250090501540a200d5204103d42107421910701c04c0100c55099201d503001a10707d28810410141394001403616103040e030314001d0b024107000518081504000f07412343c0c000c00401c0c0248000d0007220300401003400300f009525290580c4680907543c04910201249072400d030b0303c0945000e902c00c0c5104040090040b0071070b0f6102e81c208600118483d1068030010141600414942c665100070b05001d80160710700c0001980d958 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 108584487 1250 108583237 108583259
    0x30f08040311010f14130f0b070c091815020d06030f12030605011209050f01020a020a05190201051603051210080f2a01111b0405010605090904080c01090b010e01 71
    0x12000e03e0401035600313404982e035644003c1c04903802070a410001d5803040e10f000d0785400c2080c03542288101085202000074200c10100061403081d1042826044855843c03511804540d04041140e032894604900709001800032408400207650080005040071035008001c0b08540d4aa041261b01e420242c0c015030510000300360103816140781d0b107402d10015003030200003041c0c0714040c10541700e2135841d00150b6081210500c0b005032561800d000840d01d0b1070812400075510801c00c0826146c078081d00c41d00c00522180c1d0740008042075010b84400f407602c40c100c04032021680205100f43c003000380921000440228000003135000b1003050a0321409a41032503c114248404600220490380c051059081e0700c3c12003174841c000783d04d014203d00d4041c045400040c3e41d04000e01c0d500c035605000d4050a00307074485001d0f103407404c0080d0070707902040750baa200d48054406100b40b91005a110128500140000d901803004140740e02c1590004610224035948100e001a820b800515540d40c0c000010312500c0601 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 108585737 1250 108584487 108584513
    0x6010c0b04061a04020315090603010b04181202070e0c0d020d0c1808070302030c0d0201140c010504060f0603020f0409030201180501061502010209060403140c10020610090b060d050a06030f080403 86
    0xc9408606d181050811415a0000c5005c0715000d0b5902c4000034071305a6003035201d11611100035105000c18080112a181c008500c0306080f50f40c280c2c2803588440280c40002c0707150585a02c003841300100e803220601d4a900d500b044403080216a020403079940b8201e0720f07001e006102020b58944241d0b112028500c0900080d032500440130305d0340b01c14001c00240c0e4002030f50243d60901614003441607085800100c4101502c6656a2a080070004100c074603464154480f6104030302524042066074046100c030003d80d5042d04c000395000000d440c0ba0407541c5059030100704128070a0000203440c8040c609941000c02c01c803c0c0c1a50582d56900040040c1500d460708001c486015100840ca00712492000500078001d9002c05411030340e40804015001c00d04001012103400024a0f0481d030307508151001f07545100882d001d07160041c850781c000440a8041c0101071301e01c1c0b0b00401c043d00340006858040001e00008100f400c1564507408000086500c80c500a001030340a281c4685c1d070f550442c103090240000c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 108586987 1250 108585737 108585739
    0xa0f05070b04080d020f031606180b071701050d030c20130905070e0c0403082b023007030b06130806060108010b0702060301050d02120f0609100608070b0306010c0b04061a 75
    0x8110301803100d8550500c400c007403940122700007000c1c031040c0744c00c0c40035070b0709000018210403070030042c481015000b401c40078043c0b40f0001a040aaa02c030307000d011b0070544460005000c207554405160019140348041c03960070381044114801a8940b2001070148115004900d50055880b892502440014008840070f0706007102444007030700340004180c0c03a80c421484060502640402c010040400080241c60190040c50b0b4080084040c07a0f03d800095106002c88a050b19604a4010b04d0450300b4121641500000441304007030b5a98003c2070300079020024000d58840001c0040d19800c083c00c88136080074203000c3e001000245030100001d8140e03041a0040c0d08007580130b1220302c0050303650b4004c89041d10b005031031040c1030034101e2000c110103e6607e030a00703846009082500c03080c1d101c0000d0452041030070604075242840500403510848034980640c20b0719422400c2c003030100140740002036402130070600d0044240100c681b240714010805131800c480e15515190b0304000e22068406845142d84 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 108588237 1250 108586987 108586993
    0x501050720030f07021021051e070e091b07080406090503070b1e12130201030c0f05040504090201140a0203030f0601031103040201030906060b07050309040c0302040302030a0f05070b04080d020f 85
    0x4011004110901840314000d106d4401086116401486504403d40f0f42c80c1a4000e61000c2d00801b150001030001103d00c801441844086c19112210550485026800c15214000000e50b16802d103e54100e008241083d654408608a075042c0144070060004502440d00036444a08250700208920032a500c894400c0d8401a41030190181c810112015101551484460304810f01d40c0603046015484c81c06050100e07560400c11107028000c400100c040c404d81c1e003000540c503608800d80e0480180183c4800084080c0011b003ca4101644240344443c014100101d81c422092503944e002d90045d4500d03001a0004018442c000745046442c81d003040e400d0a051240584038800c00b61745010003800a410152602d91140a100c00d903401038011341410500305503a60120b00701541e903a80f19408460145140160706402a440782c07090b00d0640c0d41c024003500c1c80c0c071910b8036424401c8001c80b10a980e41c1c00f80400c00248540702200a02c0100b008002404911080c01e1010b8280702030b1854041c4550 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 108589487 1250 108588237 108588247
    0x609020f0a0305030a03020705100e030d0c1412130b090d0306080d0f2f07030308010e040b010303120e0303070903150903050901030c02070306020a02010501171b060313050105072003 80
    0x1040071056502c41405c82c034006842d0026030a0280c40c200031800d08818852820703d01005400010004107210f0280c1e501c148038140640d131045903041365900c400856101c040c44810406c0250301600e942220120725199240440b60f114060240025207100c1c2603a4001c20403449010b8050156400620b80c0c0c00103400030048035240034091051007003e4008000a04074016881d600743c4540c0c0f210b8801c11014081c01e0000300c0308540d5116400c4c0002d8000c1489c04e80001414500c03161060300c43d59100f410b200c603603407039560241c0700d2260340c1158802c9181c85803403460101c072082010350310502d01c50352040321749890340c10000c06083c42641001c1700c071030a01c55400003080e040f00880750861820f19001408441030030b4104e00304a40ea804c0141500d000054040c082070381504030324140ea01c0014032440307425020400f50f036512070101002d941e59035480d00c00121480c081000e540d0120b0029002c000201181d5175031801c489084034100040349003507540402c0c0c1041d19072000c900c3d414a00040d4500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 108590737 1250 108589487 108589493
    0x705070f05030a060b010c14031308030c0d03270f0210020d020c091914100b0c120304020a0e0a0905120408150604021e09010215040b0a15080a0609020f0a03 69
    0x3900c0502c40130306819191820080d0a9100e0ba103503958031a04030303100403040280f1f600c04544a501c03403507078000750000088001c208440040110f80b10310302d4030001400a120040001c6c0c02501503002daa00c4443c200c45040380a1403440c00c030ba142510300c2008074240321000c5104001050b0841c056510455200020640b003e41d000030f1702410f106404c44000b84a0b9032076039400c500a43c01d03240d0032036125040c8084d484464840c04403c0317000e0b0300c4a002c7d9100c59034507a501c00c0000d0161610481199202800070b02188403030100840d0030a0010b000b03400d44a03266800c00c01c0c6100d0544403101c02980d10240482401010b102001da042d5154440e07524140c9072591041e81e416982004900015101e40890102d689039030482d4104001c48030b01c0e40804808a41200954103c05809070150140c0d003640b0381701ca03541c00c01c124407035980441e102c07186458560711080240451151460711020545004c40e0280e002c002110591b03220b07500100d154806071041c0203401c0300e0010b24501038000d0741014000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 108591987 1250 108590737 108590743
    0xb042306040602070801050a060608270a08030f07020c03031912020c1b01030618020d091e03020c09070f0e0a0b0c0c011101050f0c0a03020d14011d060108060d02010c05060c0705070f0503 82
    0x18030585028140c0e100753352403641c40c00c0c420505810034802c010034a410028801d0245200e80b018020040e010741d2407042c1030b40c4540288041a6140e002013102c0141806241c142c030302400b0321807800201480360f203408002281c0c030841c8450025800514102c0300e03481040b0410145076421701e07040c0b02161800003c9129040b40340b2510b40c401750041080e1110003295072120341c10b41d41000300c10090409911043c0d2080c442e40c01b00760014014032088100b41d003031401d00070b4040d84aa0341d1341d8010105003c01150180c050a0b007281e03001c0e11401000602882a8003e8001501500068601107a1081c0050403160b40c46a0000c210390502c420020020100499154040d018441003552010003000440003886003000390a01c440c500310b0070111030700c02421a54140c0711080f146100c010510146284464800c80b10240040c4202c00024103500b0028000c1900d684181800403201025540e0035050600440345a0007092011550a0034003c0030040f050040a0a03130708030845604140109031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 108593237 1250 108591987 108591991
    0x3052d0d09110618010807080403020c090c070b010602030c0f120d0213030605010e0403030e191203090c140f0109060903020f0d050607081009060b042306040602070801050a060608 79
    0x8203969181400c200740411806803448000c002000d0503500c007203036003007103407108201601c0f9400210310200203a40307071340070300c0c1182d01458150f001080c160b040c10f010402d800c40c0042c0341d041010020b200400000d02e6104002d806848075801860301d50064030407061030542c603401401c1c0c00d42d2014044086038005601281d100318161200540c0d0303200c103041847c02c1d04807180d10040c88640f402d070000402c0c81d05040924041c41c0b09581c148080402c2c0109182d0f1201c04a891074103943c082a500c00000349513210400d50007180d814085810105502e444452074500d42c0b00340c0765103e0040c4074000c14a801c3c401421400c4003400d04100c043d0a0440041115042c6d0200034014110f00045202640e0f54070b043c2034074181d00000b11600c518043ca0000c255400035100c1c0503a001d65041d002c0780580160080d04181c44a807110a800c10b0b00e09084074000802c0200c080b451600f42250800b4942c0703841000744050900c4d9002441840d1600c1c03a25803c403003005001002d8a03140c86414449241d0101c452a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 108594487 1250 108593237 108593257
    0x20c0a05060304140c03100b010f08040b130629100212160602040512010c081614070609020315041208010605071212050106030617030a1704060b0d03052d 68
    0x65188a0301039403945030403210300e0317469414481d00740d40000304c80e42500f003070071488401e0b40d854840c0742c5004006e68000d003094800130081c40222000640d01d001e011b0b40b00941e00d02601012400607203e4442101d0782460b2030380e00c0e00c00894951201039a0038401404810140148024001d40050441101881c02181600301a02d428000341800f80b03c003c0c0c05075005450001c01001c40e170000752000a00078103503441c4060119158400040111080c01c000e85000701075912610301000c00c4118004181e8090801103441da070399441c0d07450150720700300450782070b941200d5161205810310b403d20803a0020803200400411110000500006510400381d4642551207a28481d54584010b01036486c001906000d4a1051801d40005055585a0017035011500781c08940e0f8480d1b11361020703c503101c0c40307052082800304811840e02c9001c0c62221400d19072040c007402001500341d06132000038080b54139150040c2c000032401320b04145510711688444100207400183c2c8803032070740240580c010a0103140000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 108595737 1250 108594487 108594503
    0x50115020a0b091f020307030f0b060301050607020a03050f01050f15010912080c0f030310090203090c1504030602070b1008010b010e10050c01091505101a090a030209070807020c0a05060304 83
    0x41610300b003041241d5030407901d100b1355801c2040150902c0700000c1d001111404000b03410828242c258810510403260441e00190003a40345a08203024003000c3d501414040360806010f4400102007030060242e007000e0504540003081c0c604120303001da8507801300540030001e02010480e5000050384c00070004422909030340003400726613019041c1440d0f90300913268481e0960050594a2420110100055210b600701c45c03595980c894482d01c2c0031049000840c1d03252426440000d0110705454034014000ea00e40d41d01d010285071507200c1e030b10b03241031b80c00c94a07003100c240d01c40b00140300e43c981803285120040d010305002001050200380c0000d1601c1001c06080b4014030104441100240c0718404685208003007800a020400107850409070f4141c02580103075003585400082241060030000c520100c071061280c017002c80e04541d032101c12980c400c07014542e0004000e400040140c6843d88414807440c800d0311000203500d010200a81401c0306092440d02c030f5001c1c84001d003d81d070b66000c290780c2c116410090b0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 108596987 1250 108595737 108595741
    0xc03051821090904060b090108160e0402060415090303081e04110f0a0b07050114100308090310060e091209010c03080a091406041401061206150504180501050115020a0b 74
    0x4400614442c410311560040d100c80c0400040c8000d03500101c18101064500b0070702c981e43c1d4440070391070300c10300d400540790b00c0581e080410902100081d12904a40001c000300d00c1c040c1c4d180240e041800d500022034001c135103503000400030b26400204603039101005080802c40001c403001d0150714014010401403010355500090103050312812a801c0582c1c1c80609180141503d07802c840310326801a50341100c0a6080100100840c400c0342c804601a803040300c207603e002c905641e905442504061b000f141c0600c250100344a20054a00070000200002c008420103414021512400c00e48d1950319505d10020030408407000380d900c020000d010982510f460078284e2074502c00c0d03201401d03410402034580c582005e00d00c201c401c400718a0720f0003184110000c0c1c0c901c40822448a00b070b504e56114411042880d10300560100754240c002440c1d40804075201821182c0b42d40000f403c9503880308070071031207040c50b45644007000b200348207850262030446018500e440e074000c0000d560f410301c10401400c011000b40 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 108598237 1250 108596987 108597043
    0x40510170c010912060f05070306030b100303021504060207051209240a03020906070609081306020c0a030605091614010e01020307110d1a0a02120c0c1005190e010c030518 75
    0x31141030701b4100160140801c0c01d2441c0014003800c2503000a550207001c06000c2070b00100c18440482c1100d41c90707006002a59046003241d65128001401950485d4080001c400011418400e415600c00514144e03612052240300b4810001800b00594001c510005000c100c0c1c0b544000c1034400c10580c42c980540c3d43c001e402d01040044c00b45c00070040003203003040a08410004144013900c2c92407181c0c00c1945802c0c1e0b407918202c0e40e4042945403581c2000c40f1180a0012424a42003540d01611040c100e40c0e19992104c0c540c9004000c66019400c00c8060208061041d82e01c00e2040a4000007403008504051070340d00c91020302c5a180c51510301c070f134208241603c1000211100842c0c2101c5401110510b4603003d16080041e5004051110108003400d0010701c0485203041500c041140c00b200600c4444120304624005101c041d006940c648511401c45050b05114081d030310248111800204001380e01003006001d507580500504000694102241c0a0b03034400600e03501000c08840010448800c005 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 108599487 1250 108598237 108598241
    0x91512050601021e030706050f010b0403080d0e060405070e1f14010207030203030d02030a06171f110f0d060603060503210d06031b0801050c18060405040510170c01091206 75
    0x4084c80702d58464901110510840101c040d20180f40555028070045d5078142c1a502080001d004010404d44103200a201088060000d4a200d80c1500b400040c80780e0403400103490311000f107130708070344940c054030b02030103070080401d002d503080900001c040c50703140b0700f07542e441220501c02d01611139030706007503090903040d40c3c0308200d001e0041d5009001ea991300c100f9180039001940c41142d0785180f2a0404000080e811000c10012000800311009004410f14a520200800744030074070b0280201d44902c00a9807140c1d501c0024414070342101032907070761040d2000d5501c09646255202a0601d40b030704004000170303180460181000c103a4069120b0007036444070002c404901500c08642c4056151110100400c0703100c920340160b00020740f0030030340d0a580d10303440c05080c2d400488804800507403d00c0200c003455608103d0007511390009011500309510b0b03101080445404490083e49800e1107041003206081c1340a9003481000681d014000a069480000c3c0c5500090f11481000109803080c0c00d091058607 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 108600737 1250 108599487 108599503
    0x15020915210c0403050c0a05012c0604080a03020f0d050306090c131716142205070207030317011211030a020a171b0901031212020d0c09151205060102 66
    0x418000040d50411008600d402e8016000485143c8110943d02d03c6c00c2c640030394110100c4a050351005124400c40c45841001d49003c0384104104042e02c2501c41c0b80c0d51400e02802c007034040e01000709800001ba0a0007403904402040207801500700b02050032100f6071040c212540b24a055900c81140e460f5100d1000c030b58820952a604651200000030a83e60614a441d20100d030040c000c072000c0c500c910070760710100c041501c1185a201d80e00f4000003000c2c240303030f1440c0400498040080b6448050040305d2800c0c3c80040301e400c80140c001000510815820140e0380d50f05c07081000d40a002581400c064ac1c20300105541e014001e40c80002d4202c18a0303070b00304540c20f0b242da406850810680c3d5200220f030702515600714250030b507000d50891002032103600b9000d080340707400040140443da441c644070220310098641c425020401c04881c8240020321600040c03007440c1c0103d04c001801c8407801002001c3d40c0c0079421a031880c4100c026484d0400f5804294403102440103240014281c55820042c0e2a00c428 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 108601987 1250 108600737 108600787
    0xd020d0804030c270c020705130905120304170f03040f02041b020d020f120d02070501090206130501021c050d2a0306050a0902091305040606030b1315020915 69
    0x83c00c4804240a542d0f4500d92000c8800c15800c1d00c0580e0180740c6441c117030b560118036000140d00200007000b0600e0a11844107030021032200025000206454180c02c1c056030608040c1c5e2500c0c00400e0004000b20004080c0103010a000d003e801d00324858100700349031002800203418101000020400e6640302d07400a500044038055207080305a089001a440f21190800507000d4081e08940c461309003000b144401004201d400d01c14500032099a00c07000940110743e0503500742d03689010a500503107491000306201d10380840c20b03502441c50304000924140c13441030f800c1060381c425013183d22010b4001003940c140480500d4040703501e90780c01c6104040d061341100b80015900c150360801d4a8941c240d400002944c400b82e461002c071503100c0342490164031030f0b000d2040c3c000e1901e104a280010b0700c1d900807a0803610814012a4a540c1c0703403282d420908050702d140b40076003070341100ca4040040030b448882840b001503100358103100c004000101c0060341183c50020402d40090314814822250502c1e441c1e58070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 108603237 1250 108601987 108602003
    0x1090f15060c110a0503031605030f0a1206120b180f12041a04080a03180302030102040603050601260a09021503151201050c0301091a030109030e011d0d020d080403 72
    0x165070300006114005180090b01c124441d00c3d0003002508016144805488025000b1351504034184108240d2240b0a10b0a0381c4600003840041c4941c1d0380c040080082c1c600035500d01d007030f1703842c8180303900d0803100150700280c10408200c200c680001c3c01801c0300d60740000303200380e1144500c00280c2000d080c03c105842282e154000d1120807044a1941805042030303e8162040340b55000401340c1140003403250340102800307070384072054000c000b034460ba140d084803131141d00424141503600c2d40443d0a80e002904480007181e2140d0400c452564003590f0400d42c5c5d10b02c03d000c880000c2d4400c0c0b981c0c0d8010800340c5040420340d114000001551035605180414440307440c0559580d10700f91021291550300005800c4c0318203040d8440011410701402401d01441d05804510701c1c42c1d190207080b00040c03a8050300000d014603904a00c045556080c410103040034000d4454103c0d00d9100c0c0b0004000c0c540c005120202c940c0f120a01d1860340d01d5030f901900340b913503066650910b00700c040d0401c080703140116030005103c05 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 108604487 1250 108603237 108603239
    0x3070c0303081806040f0b0711070801020d0b0916030509030906030a2a09050108060d021909110711090606040302090702010c02010b0406050904030c17130f0506070b01090f15 77
    0x3603440a060b03442190701000341d034208400c03201c2031900e8030002d48000d080000503040742804078607003c0d012500480c5505041100c400561102410b2030442c0d8401011a5404552002508118061100400421a12940b00b0b142144c44030300002940183d00c820541d5400005149800800803145003600c0104941e0700c0b850502a00340160030040751074041e5003210122590410101154058019519110501991300300401182c40d400b0003400203503c44401d04048016842e014000b80c00c140c82610484007a50902c002c2805540041c004072001950401200307000c11001004248a10400c072412459a1513580004425008a4202946c085026020f02ca40e0580550241440545c2900288020501c4a04000440300c0e644246600700402d0400500028440e40d00b04110700d10507440c46d0781441e40c6c503656011075004810741c40912501000c05110f01121501c58200503e806c0710300b5483c01e001d9079100c0a2215041c82000c040e1901c800d91034444043c207810490040c0d100400074036011b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 108605737 1250 108604487 108604493
    0x20903010e030702030706080f3c070f020c0d060b040b030717060106142d030901060f0905041109040311030d09030810050616031701080c0907030c080703020c03070c03 74
    0x19a100d000120710030300c40c030940010702902541d1071074410508124240700a2b9101150111509810303011020803440f0200720761001a005c1c00c101c007820001c02c0d40182c03245000100600b0502c000f010b02420b40d8444600c00d060742c5d07650340e80c03000b645034402808180c0e0407540e40814003070507404500d1580340c0108100400c10070042c6800f000d840c821304048a030740780d03a6820140e4000700107030f840100000c400c111072583c1032995030001c114807500030780720503500c0c8914403004145d4000303454070034107070b5107561080041d84003400140b0060244141c3c03c20039030a140d903e60403e0340300741d15146e0064400d5000542854002c20100e1880340a80082c1c035a5900da0080032402001f84100407804100c251002c5064524100504003c6c3c82e0087c00711454462030903211820204210707812002c000d40c14041c4039020b10720083c1786008003c0c210007808a8114081000411003000b048203040514201042c10010360020010b9000042810300603503900e000c00b40035041d4441c0da00b01408170b620f0f01d80e0020030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 108606987 1250 108605737 108605743
    0xa0b040b0a06020d0206010f0602100b03100501150210150e060105040312020309090c07030804080d020c07030809030f06040308060108041a070e030f01090c21200a140102030a08040303020903010e 86
    0x340c04c11039820b407521070381c964102d8030000c0041e014260050b070000c032103100c10564590080e0110500241120f24031840c50fa0340c0d8059803802d030024031111040a4456150350340410180e42d900d030400f4010b000600e14002040526802882103100c50085000840c403d640950300301c4000c1d41e00078103200d5003104a1007000c0d50b40e602201c038050180381240002448a4507400c1940e03d110360541c0d03004016251900c0c0d002c1142c10072200b254407a90308212140e107107001003280800551003540701e987c1f01d880c0a0101403c01045100b02311294101e4020000000c1d44600c4031540f1140074209040c0548075400c1c03c070040800040825910a158000d00c02485d810041200485030100e08071010f40d043c8a01d018280d442c00c0c14010002c400c0c50f50140101143d014182804030b00c0300d41160011710094860030061011f9136080c0f4482c0c48030200c07205850078001010805400c0d030002801948030300382d0000b5628442c54040000b002045004107040510a4044609102005001f44850307001d480d07090352 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 108608237 1250 108606987 108607003
    0xf031005091506060a030e010209030106031505070905030d0809011401030308040c29071505010e010f05040203010b03060f01110d05090306160c02060a17040c0905090a0b0a0b040b0a0602 82
    0x1500c0c481d14242c85040ea1004140e584a420041d0110342007030080e910642c00b500c1d030402c0c1c3c1c440a54091007a00303801d40b800d20030540154003d80d401c5207507450740c103039030360464101401010401c00046410700c01502c0000e81e1154240c2035103045941940c900c0c103240e0042c42c0c10b00f0000802c26207000004141a031044900d80217078010700210000310350342d404d08601d018141d078002d144500e10050307061002c04001d024042c42c2e805140221454101400348104640c0f098001d10801000800180401629580490054001602c04500c1c55040480c1c01146000c01071555100311507420a422480e4070829012040c1040e0200f1620320080783d00d0041e01c1a000131400754040c2c807491002a4520704d121904244400098a442c030341071100b9000c1c0401c6500c100c4c4400d06203e14240710350702400c103901420b84200c0c0502c1000442c1e03801c0c003c00c9004ea4034080c0609034140e00c002040700208000039000e540005040310300240707190444000c50068030680080c1c90303000c1e0b0041d1000440344e4000c00d56507 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 108609487 1250 108608237 108608251
    0x3020a0b0a05040302060d0c1d09071103040f0f080f0a080712050705070e15010215010b0c0f0304060513060206040b070815091905012106050705041205010b0102010c02210304020f031005 82
    0x454850310000100409d00c0000c0903400042413000c241c0c038900800c80b454610300c02c81c05591620f601c2d00180c070a101050f074441d5001a271144d104001c848010700581400350807080240500e8266a00c1d060194001e010024002910784410a801c07640a01c049800c581c2d80142500c5031196a0200020903040844000c40741c01801c1e540065150305c080ba1400b0581078000c6030840c02d0b42025505412500414a02805440b4100e0094105c1c030301007001d00000d0440340d40d007958402c039650713062100402d50b0f8041c106650005041c000050032040c18294401c1092400c031078937540c2e02404c0d1103203100251110f60021800700511040d24801c5820711898070f582d142c01d10440c0d83e911100c178050070303401e1510703d24001484e2903800002d40030b4103c290010920300e030860402e501e40d01c4c03460441e4440c19003211213030340d510000c41c1c00396028000c50a0400840c00500394031104c161502c54101d1140142181443c4004000380c1150b451078881002c050020b0210341d051400550004001d050560b048 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 108610737 1250 108609487 108609497
    0x60503131b090f021c091a0405010911040207081918060201020711100819060f060e04050121061509050c0c19030f050307032714060103020a0b0a05040302060d0c 71
    0x10907036030301c001c1c02101c49841c0350345c01d45030204444001c0d1100918080c8021211121315500714121801c21051a602441c003400c0002008403075460b140d44400310049841d0b000d54014098900450051400d941e800044c05e42001d0320940b01d00411680b44a5403e400c05c0c40f4020044046507856055000e0000785100d00d550b00780460360f003401c1010a00000000b0f80000700408001031041080f90b41c0f155640004803400301d01c0c01c0c3c0310042040048540d400c4040010300004003000c00d450140101c50042c00001b09601000d00706103010041103052a0b00580000d031101c030384001419a03054803c0051405820820007414082c007524829401400301e40900d110315000c00703d481086100b4400055410b40f83e1304101c503d031b200281c8054100810b9131042c981c5c1c4e0000c440e06a10402c1084201400404510860100915020140c03042d02003a400160744900c0041c401600c808100c03400303481c0c08a02c0c468980c066028100d032140b25681000750044008a01c100c1e01007201d81000c40ca04055483e0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 108611987 1250 108610737 108610751
    0x70c02120705033f0906040905090c1905190b0d0603021003020301120f050c03010f1b0801080607050c1c180504230901020403050f03030f100303020601060503131b09 73
    0x31241e14910044c203900d4840b51411803424408112040d407400d42019841c140c20100440d001038202c0d00316601c0a11583d0f2a401088402c120a1042110402e401ca508003142024070410200d100310038001d860041c549090360403140700300c4c058068000e02e4060b10359035684160f244480d01900740c610040f8050030301c00980c03070b20850082c000d0342d051352000410402c0b540700c580c81d2032440400b400c000f41e07035034010001491240d840c203000c2c001c0f120321440004644001c440309030003180301051960000308880300c80140041000405d01c0c5030012a1441d1031600e8140f000c410f01c0c1070400074030307650740d0003040d04400c9045140c0003a810f02000701145c4030103d66541d110144001e40701421414100041c42c0c0c03140e0242c0c20071701c0c0c00c056080118440018202501d076a106c5150005c10300c0ca103180b17584040100b02000c0c40c00c1c0103140c0c2c004601d40c0c44809280c40c541c0c01075912001070182a040c050003000040c5906d031070308603030098942c11401c0c1a030b42c51480c034010f05503400035000b00c001c03080c10610 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 108613237 1250 108611987 108612013
    0x11406060a080f04060b06030f060f0d02030304150207050901030c06120b06030403140c0102040b030f06010207050105030403050705150106110d0513140a0b1215190509070c0212070503 81
    0x1003900c0c4071030090b85401c1c4841c1d0300c3e030b075050640c203100400440780306590707140841c1b0701d80307404c40507610608052191105600380041003100b401c104004540c41140d07030b40038050060300d0104c1682d0031070f124015800c50f5440040d4044c1d0922a460f0815a00850414000007d203c090b5071030108075002600e07804440600c03c07110744240e428210382617803c000b0400108000034451000c035007103d03111444113814684050103580c2603074400d511586001802005100d59403c005000940081c402d00042880500d40800680103000080c4081c06100c0041000d0062101c203011072403a1007481d001c000503560b103c502c003411400c900825845148228900e55080500404c2102d418006020112103c6d500c6d1041c42e1000c130313044190b010707048525040300280b00c825801c0500314120001c4140051442c211010001c03c0e07500800c4140700741e070350341d03040600011104440d03803d90301705541c5801981d035103900a5450a003501c90080d0400703c10045110b0400003c5070034400c1d00c9045003901e5100082075 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 108614487 1250 108613237 108613249
    0x37090e0901022703160803071e050c0d060209090703020a021006030305030612010e03040801140a1e0207081b010e0114040b0a050603070f03030503270a14010b060c011406 75
    0x40c42800a07407030407418000080c0046401d483c0e40480040446594140380c801a200c20400d5034440d0782e076540040f43c02000c0060711492000c07965031105c4224910305191701d6940d030350640030460602400b00ea043c040244000f94045482c5400054011415030510344c4004000750311445181006000f41c2011101c00c038401c1c02000d003141c1d01a5520ba0031a02c40d87c0400c40390901c0440703490110342d61130504886116050024100030805d0100001e14002da0341c5544406007801440e0001c117500e022208100a5203c0c0204950103c00860040c1c4031030a51030308001912841140b8803040101403071070041c1d00015005211007000c81d00082c0080000b0b0180c0e0b100c03640081c1e900510b00030044000030300b503400c2a130004ea40054000c08545190b5501c0c8a00c2d441d48078550016030010f1000801c100b030f810505000003404800f10f66400306110101807035240c4074041140004c0103010120010203010f8170035000b207640c41070b0041086954806808030301c2d0007000d04401000020400d84002465444d000c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 108615737 1250 108614487 108614497
    0xa121d0d05120a02011d160803030c190c050303131110050d020a1404030f05070b160b0c040f0801061d060108071b0c0603020c010b041137090e090102 66
    0x10400510102c07218080b4000d0580224280070210342d0b0b580080b0a0040c0b1114004000c80c4004d1701901c031000342036480902e5011b407038010207243c0e0320401c1407102024084040b1000102c0901c1e07010640c101c011170803910710f000d0401c00303446c1e48400710074030a80e580e502c0102c600c482c1c0300d00300943e4040705400a01c402000ca4402700b0000c51020f010b51101c1e1400384d0010100c008403403400c0020085296203000183d0130a40040c2e0f100748545803054208801007024001804015040a051400d2604001005000d44c1d80003007008030000c0100c0c1c2c0c80350b90041034401510710443c41e14841d03922010506d008203603d2158a081d04090b05050030035884211029001c2d400680d22a20b941d5100881a0cd06010400c0300e0b0107070907080400e41c4e002c40d41e00c0d01100090151a9009a92400140c070500e00b55450347d240300d8402da103804000303082d031100d0400b00d0309404079804c2180302c1a00c03140340000c0405070071700300d031a02c0c0080040455241e5521092090a5809824089200703460340b00c00360307080b4012 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 108616987 1250 108615737 108615743
    0xe0706020a0807060b090103050a03030609060e04021009091b090515160c1508040308090d0206070f09030203010f150605040f1404020d0c0f140f03070f020a121d0d 72
    0x20150740000894404030041c8502e0b4041c9001140016010300403401d040070991003911103030400c3c4400c004150381802841c00903c20b62006201290a050039002502d0024200a106241d000c60f010000d038050f44260004202c00401013000e5210313500b0100b17074064840c031060001500903070045400c0c0382c0100c1d1078000d001240340040c1803030361000aaa000b2484464140c03a418040c40c0001460b005103045030b001c160072607407141640c0c00c16283c003424010001d000f070314998214114540c0056400180160f200f0090310b840740500200c0740050312600c4c52074201079099400c0c09500030544145420000c400507200044040e11b03591610300300d5150146000d915942d1041100803c8004440c0041030381c01c040c0100010718004039158204200c0d04004a1407010a89040c0701c41003440d000501083c2c035082501205240c03814001d0702203a6444010204402c2c000b240d421800100d2007041048071003588140e1240c003440e40418050000c50850010031280b01006500034000d003010351420700790540c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 108618237 1250 108616987 108616993
    0x1020f061504021308030409060302040606020a030e1e03070305030414030304060203090d06020d0f1406010e1f09030f20010e010806010c06150314190b0f0c0f04090b01030e070602 79
    0x401e408002c042d6001a4403e2034400315484089421032090005000500c801031001809034914814442a95240c1e4042c5055400a4105502191304103a941040035021550407201c2d1004110552901100040300f54140c81000408402c01c03d00100070825186810180300700d00c1145020566240701c0c074007074840141c01c00e00003807800e810030410b940000d43c4a03150140c00c00d101035900b1404c854504072000c1030b16072030ba6030306545101e203407902a800074400c1c60442c000c0301525001c1541041c110034050a52207104d05402c014038030594041000d15448400580c9452030360a2071140001101c0034400022107504490000e5800781c0d01041c3d4041040c0c40380515940c60600660750604000000c0c0c030582c1e01d031140c92030520a49003500c4081c6101d010415521280c1d840081e02d451610541282a0009c45c0c1c5281c0104101c2031040394008030200038040e05d0354848002d940d59025160365048045000b15002c500d84019401c0b810304c048082e603042000c2250201e070a903840c90f6911a290150b0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 108619487 1250 108618237 108618271
    0x14010203040303110c09090321100b07050304121202060105060307140c010e030a180504020c060c030a15030f0b060103050c0a030b27100b0301080d030903171501020f06 74
    0x28011410100f0b210341aa05617000300c4d004101080032440200ca003400b02da0000140c04c0002d154000c503050b12a442000c81041034a0244c3d02c820070420f01d80910040000042a40000c010f070030000c5402500821042c0d21300310b1b0f02881c0c5102208003d110b0580540541c00c0049001c0c2880301c2034900c20030f000e644105d001000d80d07240707030756652101c000031216548a070047d0000c0413041000341104020307503851003280301c0d003541440b1301e80240c2d400407032286004118124090354001405a00444903039070186e966119003081e00000e003d10414a090b206540f01d000044c000d0405001c5d5909004800b02c4c24a03949031401142142c07000c4030f1420305070505202c0640c80c148a9403000c449050302030400d840c0150040003070305018031004d11890301c885461040009403d40d6601d0b480041c0651240c00e81194106002103032200f003200381d640e08142d55151101d05040c4a00c80740c807003031086c502c000407150410500342c508103200e4a00c0f05016104d003900030039031035000140191003204840300c80d00141d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 108620737 1250 108619487 108619493
    0x509060604020304030c0c0602030a090608090c190306050a0c0e060337020d02030a20040509100b0304030815030a03020c06031308030a05070f0809030a12020c030c01090606140102030403 82
    0xd41000c0d1017501002100c00c14400003800c5001504d0160816400031a11840c0c5514014a030000070b8101c0010084100e050101805002950000d00d1600311a5100140103001c000c40001d02c060b40040e042500701800c1c0701c058003059102105001007996141c04018181003804950b11041e52045049512002d046111012540c130a05801c48420320520414641c4100d03841031f40c010316072800b10701e60f000003400440c8005104240e446d112001c14416182080a91040240540d21034140200e001d4800034020694008800015000c007154441d220b007054240180040d00440384004680200e81c03e00200b403400240c20007070700c0e915900030f0901c49890001e000c0e45400180038031340b03007072000c90750f440000d5400c1005d140304090381e00c00000c842c5082140245812000c0a61101b8000c140080c41b500f0040802282d11a161b9400c04c0e04950848a01c8007001784520b0b0503403056030101091a185c0b003c019000005140d015000600000f901c0e0642d09181305c0b03030040c2c1540540e00402c010000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 108621987 1250 108620737 108620741
    0x180809030d0806090f0a0e100b040501080c0a0e070903060606030203060a0603150306021605010c11060f0f01050108271b06040501020606011b06090305040501080714160804050303040308070c090509060604 90
    0x20122001c4001f081400c4100c8034a45020306e040c00c1041155181c01c411040d500301441414010701c1a540100a408900008149050514018108400c4040001031082e0740542028401107921200400005031348042c020006c1d001951b600c0d01c2171a0020001402a12074021101240c142d000f0b80d0380b11a2450740d80c40c009600400e4078074440a241109080450740130700c1044502122030312078094412402c0e0000303040400080c4107540c000092030a00c004d6034108544c00d0b06441c1d003800c107117606485026040d040103c08103181070500004d440b080c1c2c1c1500001c030700008400c501c110851010340ca43c00801c2102d0141e80581070041c1c0c808000a03800c7d43c03046103040b502100c1054030b096541d0756a251002551899402580810b000050402c243c0d40e1240c0865400700907031410340c42c0307501c082101e0451071080c68007050142072034000d01000d2104140c1122700400303006044035500d640c3c070318044800340c11901050751492000c00b40081d21030802d00502d803184540c0c40140500e1b035200010480 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 108623237 1250 108621987 108621991
    0xc010309030c061401031e0c050f0609030d03020408012d11070f081801020f060103080306120709050a2a0315091a04050105010c0804030f06180809030d0806090f 71
    0x300121500042d000c11110320403040243d088114030b0480358114141103807043c5401c240f0b000940380d6040803202040c040c8503004255a01150250b980145003800600503010f40c4d40c0c41070b810701861302c0074403056801d9802042180d112070001d024a0f100f1050000c918801c0f60401281c200600d0b0704030132034401c16409101c02c000440c000c1c6041642e103486030000408143d00c21194000000340311041c0010202800c0401d001c00d20043c981031820802e511386031003040c84028031030200070011401c0d6a40c0c850301700304001d010a0444422942d900303503000140405403081f006203443c14031046102030240600e00ca580180c1380569411041d00c480840042031100180d002d00200d8020202e03041c1c6140c041c101004200c40c0780703e05508003500403c812110b040e0300c114103204101103850000703401c0070180c50449800000b2140030245500380b00c4044c080b68800f64100c1e20030070207223508012511000d0411140141c3c11074840b011016401e5503d940e05640070b65100d044035000070040310015182079 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 108624487 1250 108623237 108623243
    0x4030906020d02063103020106290702010f11030c011b03020304031706040b0a0303020604030e030c030c060904021b03030702010e060f1306151202030115050d020111010603080d02040918050c010309 87
    0x50300945e0342d44048000300b440081c045005035191101002050002c2111414504074107402072801c4022070b062044070303ca2210002d0501406100510f150b40c05064900d03801e841c4401901ea031180080031950003801c3d001036183d2034070414062000258400e100f5a172042e545034580307225200034a81e400142490040042c0e03402603c5502c01c83d49901d805001600442c0700c1d40003401c070f50401d40782c003515078150603110714000d81c011034642e02d1a0341c002a4640016000b60380701c0745d0340e0202c0d60101d0041e203d100d486c801c0c201070030562080003000c000025881a055035000708202450a5070340345c0c407400142c84428a10510300081140e40c5204080058000d05c1440f00007402c10040b403454080c4080c0c1e9001d240c80d140c00012003000d5040078022601d039503a00040048200e802e110008240560b060380217070400c10341c408150300c6c0341000d43c04500950b41010456890302401c814801c0654010302038441d0181c10307d198030b81c01403402a810380312164400003905000c82c111b1300440040c1841030040d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 108625737 1250 108624487 108624541
    0xa260d0f08280f0e0c0a0612020d0507081807060903020f19150e010c0804030b040807050109060203190507120f11040902090301060f030f061814010504030906020d0206 74
    0x3020b280840e914240d8203611181c007080031200a003031002121400c00c521480d6420035a4000801d50b1100404019584181440c84441909a500350000d00075844610303041890f01d01400621608000800e20403a0841c10b80c03440302c030010b140240c03100b00ca482182c0104005c0d1109100600e041c11521300d1303c0d04090081e00e03041b003000200035103400c6650302010f0460000d040c0c0441082e401428204100000e0130a500c25100a0707880394460301c51888080d028205500102c0c081010a400301c908180c0c1040081c040c614a40c20700100035031080d5541c2c141c0b10340f1044034201a5009004882c4600c0d61619030300c40300500341c030103c009400e003460002c9940b5510000303a0a10840803014001034080400c0c01601d9030445024182102d8154009219806000004000180c0914400900315500038808512a0110401d1460368044188002c5c91803c2215003100748810541c082480340d406607540c0c8030340c0c0d030f61040b080ea01c03140070300a02001a080000001c1e88440d9090342d00d0800b64000240c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 108626987 1250 108625737 108625771
    0x4020d1103010f06150f081617070f0e100516230705030f030412030507080904020f071101080c25050a050d030606020102090604030f0f020a260d0f08 66
    0x203003150b004007841d03200d607603581e0742c18030246110b441d03a42100000340c06c0030411200b082c000a0054a0002c1803c140b030b942c2e082c8034001d400d00c00c074500c42032900b000c000d045940c1485040a892024080c61410015401201c013000901e40311144520804d4103485980c03070820a640d1144000801c0142940c151109480103e521485071341188004030b0004060501c041c244010541804c0550009000310790092000344104501452090340003a494280a9920081460082102e00942c660f00c3e900078804900d081c440d901d40e400500c844c030f00c111004140543d05038010748280006440400c07030070758280030705d120391042503d002410b5100e1010f800c420794140d582e40c9240810080d01120240c0007089243c41041d0140940b40240101d800254100795115002c03c0c0f0600a600c0f024003101c440d0500c1e4400e00c80030440c2000c1c441d0b006803809100940710700702c3c1d40c0c1c4030641050480d11710440c510010120040847c2080da480c400341c0e00d460601e003242c8030485943e040540350001095501c0d003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 108628237 1250 108626987 108626989
    0x10b03061513031a1006050a170a0e1608030901110a060903050a090e010302150a0e0d110102120301050a030b04021305040b04170901080109021e2206140304020d11 72
    0x405003010411000380e42c4441c5046160181038000c0a0703c0c13500700002042d080c4074140000540b0380c0103030f80d9203191690b00c54000e6041102d04000001c03842d100c07000d9040c01d00c101003043da0000085000d45900b03ca200310441c0542241c20319592040e682c0d107420501c6148111b6200e48100c0b0103061811089460070203103a20b40c04202c483c0781104802041d40041d11429841e00030040d43c4c000c00e8038802d034258941c915000700300032180440380c02e140048001b0ba04995240103041545608501900028070445140307001101a01d115030100d0140c450f6062050041c5003075011641a0340000d02264180c1c0c0c41c60b0349446082c80043d004913030040042910240d108411f22500b84a940522005074a0707081c07030f0a19002c203844101030000180e00800140b22240d03044811581198190100165a0705000321004011900800c1c0b14180c010b00048500701005050b8010b00d503a44403070103a40441703694680a641d004140942c103108041c00f80300240c007610341413040080c0325008a0f05407101001c004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 108629487 1250 108628237 108628279
    0xf1715030304031a060a050303070c09020f0c062a04050a030f050102121e010e060f100908070b0309070501020304031a0c0409061d1605070b040f060c022112010b0306 73
    0x85000c040100401c0301700c0c03800c80c0045c401000f0a60165103019150345482142c0c0610f40109035549400054a1035004248011100d45110680071343d00541861840b2075515500d0904d69446c3c1106240c8211080056104487c12a48014200d5211501d113940ea041418424141031318203540c240400c030103400c041c410303540c071811403000d0014240e51000140342c2d4000d01a0844980f00a00740100180c40d1156540800c041004982003d0810002e00048035403c2c40754005450a0040078400180c90150a001d10b0281031603400b582c151a07111001240d03280150b20014059036038440782c3c0180c2900300c08a1a410003074012480c0d2500b6102c101d03880a0f25100c1c0e01000c0b1001541410302c8503002c0395038000c1d40260280e0303050b6103512100c43c001091406240009496020084080f0f010001400a41c02013290701000502c00319515007006501d60f09181488540f40303a25442d1000c0d00d954103021501088101400407100742d0070144101207940008001540049036100f0307000c000c1103a4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 108630737 1250 108629487 108629513
    0x150303190809010905061810020a1718010216111804120513170f01050c030a1d0f0102030717041a090a050f030c070b09030706030504030c210f171503030403 69
    0xc44c9091100b103110080240ca40341c4070048c40e4441901c1400a50005079001d01c08544504503842c006065480d0050350004116845200c0c0d25291300c006078070905604481c0c2d030208614011145940d0350311004040c40040001c8000d8084040310b5a0f0000300000c8840c0110b400c0700c900361900600341140241c1412443c0c68641000002c0c400500c030041c41c4200401c4070302d48400c1c41c18002e00c070314241190b41c401540800740000f10039a0703e95030710f41f240f13115a20980c0001040041115521100c00c0503580c000d46c4140e8502c40000d66095075001464501c8451354051540320345030800701c01c29048142c40016010340060f81a001d115110004502c2c10000318030f504540c04059556081e09aa18034074220340da9108441807102800441160f590208030351007114038509010405948601e0300b10790700409407900400110b44c01da00998250b952501c4100408507603101c0030030340d403c10170054a00d0340c030f0b0049911800c0324032400503c42240300703208420012005400c40307041a490350307265440d040c04 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 108631987 1250 108630737 108630751
    0x4020c190c030209090c03060a0b04150f030507050d0503090f01110d0201060801060f050102070b0706090803330f0f011806110706050903070b1c0207060515030319080901090506 78
    0x1010010310951621100440d04005c100d4003c0c00003685200c0426158100100745a240507540d0744660110745807a080f5000c40001030340e210324401d86071400c0b04d06000b00b50100355920320500f680410740341081844e041a15420100460810346031104200d03034030829145640c100844e01462501c504400c200055071103200750004201c090400e2184c07421240301d43d0180c103c001c5040020801660041051010388002c558100d0755001141840c0c00a4000c0c0d11000b02840c000000b042107501741d440340003101c0c4000d021442c2c1d441d100c040c00035070b003400c0e0741d400c1c1c039403060b40500030440354130740030f4450b08408030107042c41c2c1500102c6c01c0c4800345101d8541e02010105030310751541071042401f071092001801c0303a07007016418a488140420340c1c0b0400d50050100b014800184429290504040291005020801550784400a2034a04054401681c0480c1e0714401c0c00c0005141e45008810340da000350300e05611400b0700c808480111a8184050501e212655807000013102140c0c0621040d48a590 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 108633093 1106 108631987 108632003
    0x1d121b0312010b0703080a093f0504030512040807180b15070501051311010302070303020702040c0e10020d050909041b0305060a0f020405030a0204020c19 68
    0x31414850541c0704180c8000041d503e0111401403402c10b11940d244050350305d91380c4c0c00b40b045c0c50306650000c207002c00b6240040b4580c01c90310001d4014407041440a020b2030245206414128041c01851000540025060090182c200f020f030072242c030f03540111480c140c64100e00a80b00c207220302815002081540da0401a0034190b000560309540081c0b00240205200401d0a05988500000c81ea594284400070b640100300c0b40c48403041a03008144409210120030044000b540124012414540d0034805000540c0792840f800f07810303030540d4840581d60102d03c020032101e0000003035440b086600903240340c03440750b50020680304012002d84003400640c5552400003200e540201c022000c00c0e0343c40000005101001a0710350140303803405c008002c0501d12484080503031184dc040c00350180c1c00149400014105070307000b460305040382c009440e0300162001400d40c007048024002d540c000 = true := by decide +kernel

theorem cover : BRFrame.Cov 108453237 108633093 := by
  have h0 := BRFrame.cov_init 108453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 108453237 ≤ n) (h2 : n < 108633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
