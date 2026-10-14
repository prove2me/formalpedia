-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0093
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:48:04.439478+00:00
-- url     : https://prove2.me/submissions/a8a3fb54-a9cd-42ba-a834-9a0a49781e26

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 16546769 ≤ n < 16726625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 16548019 1250 16546769 16546781
    0x1c020d0f0c0207170102070f020d0f080406050315040608031204110a031104181205030406020f0c0102070c051e1915020f060112031706150f04030b150a030201121806 73
    0x80c00000155035066881545d0807031088000080500420340e4020f005494588403042c50140540c854104001d81940d842481d0790054103c1001308101109200721410168207101c400c0800b903030100700c0c540c20300e150980e8034003413601024482210000003c0c10002c076a9030f08442c0303500191148081a0b220f180030203130340441154141c051460102c4010f0b920441c0300d180509190048105041244150f00807940c43c1d100503c1601c81640800c2010307003030400b2078014004c06070344000060300c5038a01c0ca4030107011029507002c0c91084440b80780030300c05803214400c0d081281c10100da04188039000038015220134a11544181210340703070741c00c209198030b80103e00c070880c0d1001c243c1078940581e224404483c0003100d408000e00050380351107640d03001f202e50248044c0c01543c01800d240c3c849901072000d41e55988040f504800404001c902003081202040040d0b400441807460118500c0b260f01c0464a80760151001074108148880038910b080074640c00303c480c20280b45610a951030550500c1005403807 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 16549269 1250 16548019 16548029
    0x13080607050a03050a0b0d030c11180603060702010509030a05090a0801110705160b03070507020d0506091b01140d051f1401090503010903120507051308010b090603031c020d0f0c0207 80
    0x4104400158000106c0c858a460320100500c0c101d0481d1542d14101c070042050340003114142440c50a015541d84e413404460341985081c0c90740080c62034408103160411002404030b905682c140414803640610201c04d07502e00307602c1841c2003a00c658030390000514120243c0d00068155280c82e995070280b4903000001c2044c94028011a0700c0c4921000341c0c041c40301c3c510321640c81d02da4020700c085840070388a98000c01800f80024564124251992200e9007065416140076030240d000e85101a0605140400030060301424200031241d840d43c0d400c00e07c682d21a035600c2224003590b440000e412608856440e480004684c01990211a15081c030004400e490200302c5020901449000480b0303e030500134207540343d60694840992020b40c800240c06020080c100c602448810700c003800d005a2440c1e05003000340801800460003c1d2410107100120402a00c605c0c007a82080200c401c500c00204005060065081c90041c1c3d00c50200241c440102101c440303006100b802d12050b21910303940016054290b030307 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 16550519 1250 16549269 16549271
    0x30403080f04140904030503070507020409060507110706091202191211030705090c180103020c030c03031f0305030301170304030819080a200309010b0306040b071202070b0a0213080607050a03 84
    0x8503d03c82080348007682114010300090341007000a5803103100b0380185c02d6040c406031021079004c1d011354034582915401c1ba400400140d00c40b640d9110700004010b034000911182c20320a007014144000310340240300c4400085d01a00c0e402090380801c1050a50b218010141030050501c02112444c044924462703d1500d81d100b8403803280003288610740000d65601508219410070320340040003861540d03180c40006194113141d82881000d034412820700c000c1201120742009542d491400015070204152005988222041e00c1701003480001c100100f20303810f48100c001031101700050402c0d410725520842d08018503480000c141d030300c41c8685056407001420119168001d0640e1400950000c440c58007241d0310f1072411a44114000001000003150448021000420914041000b01e460f044007654115000c2c00280100050f895016444d011490b2062009600d03000040c0c0b21a5110705000d4002031110380d00080212480c42c80e9001d1400500c0703444165a40740c039000c0320161168000b101260042 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 16551769 1250 16550519 16550549
    0x504030c0b071b02100c0b010f08190b04021c021801060809011b0309050703020406170609011406090603100c021b010507020a0324051302010f020109030e060309030403080f04 77
    0xb541c0241100d01200038020125000310303016400b00258804405160424403290b05640e502003200d071421180a409030079480200c0b41c0c07902c03503002d19210039460031b004c10800040311040007450340b440d1542c10a0f012648030040040c4203004070006921050002c2d40249208000c04007044003c41c03582c120b8605480c0c000311540c0c0d201c041c0c1d0076101a101c0d0203411aa002c2d281031104e40c001d6200420081c003c100f00c0704541d4403680814200e80703040d0400c00c2078810342c04450002e11008c010503540811176100034030020845800c8030444000107415244100c50140010354162001c1016801c444800c00702800610318035400a9110410180d80c0e09085134030980564440d402501110002d9502a00c482c21440c6951a82d1020300343c04400a540c00714011400c0e480850240643d0380240c0c0c034560101d090710250b1001410080c4011a6401035904200350807002c2608042c000b41e941c2c00599065a803a901e0b07110725425441039400040181402042a03490005000040e0042e00e10b0020001a6 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 16553019 1250 16551769 16551781
    0x90f0b01030522060c030608100609050115090e040807020303030f1005060c031902070302120102340303050405120706050105030c12030f0d060b030408120109020306100c020609040504030c0b 84
    0x442d14841158050300d030002603100340018420f501085d02c0114601d800100c00351590b10f11030406000c407400c030b96403c0c0c645c0028443d9a59a200310b44c01007040c1c1e030702281c6503a10000060020b640c54400c1e0104c003200d0500282c240600c40d011210043d6000301a03a40ea841c210903844824441a9000e5101800c0054041064100784c4102c42260b400200250f00f41714540c1988407001e01255010310850147c5100000107890380f510040500160703a001613150001c42061400740d0b80d07000e512800004402901e40390792103003160352000740c0d80c00d894041182e5a03103040052405c0d100701d024808081c0300252400c24402c955000b1810317500200c0698621001101c10032036000c00001b44170303609800401c08041e2440201008003040d082e01440490040d541d12803103500c1d5041150306441c0803800003004c400d03100c4280486400350580c80011030550604001040d0021444040d40c000d12031042200c0c0c05650b118001d0360b545d540000d0040c800c6180c5450020300c41c0402c2d0304201c40c0100802c001c502 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 16554269 1250 16553019 16553041
    0xc03080c1e0309040e010902090c0c060c0304110105070204141806011703030117120d0c020f0109110402090604050301020a030b01110f1908070c0806010f05040b0607020f0a090f0b010305 82
    0x61001e00070010b50800d1003000400000302694610003150799a5584803100688803002040d225401012020b500d920a1121180c00d148008010942071241001000006100e80c000c5083c180d100386040d07a1181503038404900140310500101030804d944e001002440f4003000c0d240500c11100741c09581060341da6548400810003050948070b0203400600c014403080d00e00041440c812040d49040720784080180b00c894140354090803450000c035403102c040300d5290340c0401900c41c5d0160b100c0000c11070f6144507125000540740e502100e52055400191604450350344406490207818020021903451280340b4001c6c00420041480e02c0c080b440f1207000d0044001c021031010354483c3c0b0400982138039103481c500141070500c0d03200100c4079201d007840b01c030010030480120314020307095510007401154108505070152544d00da004a00c0740d401c10400030413607292441030b25412036051310100a4241c8000003e04050800e030421740b412840c1012000c44015560400300d81c28200382c17400c115039124020366039 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 16555519 1250 16554269 16554313
    0xb040e0102040315150b030702060402091302030d0e0f0a08010203040501140f04020907032403020f03030a2003160c0306110a0c0201080613060605070501051f060f03090c03080c 78
    0x10b80100b00fa8810780c44140c2c0141c01c24402d10117500f400b000030356102c018002d9181c02c1a540640160300030750801c411070404900305a040141048100040e903030300d0b8006952103003a00500410080c045500e01103e0329140180285008010448000262181103840c002e401c100c5003900e80d58217049140c140100c3d80e06149000c1c030307400034400d8000e503115004e0100041c40540034208055407031101c1042101400e0300818000925a1481e04151650040003205888030301002d120741c10070804000100d412000d0b105024450303414598540c0c04110b216070540c02072801d001104040d14418504000b01d0440303107425248104010131180518450761f4269004411441c004502100f81c020055800f60b59207030790082e4000c0040c65840940c801d95405d554040d4004c0e404613101080940800200f030080540c0b041003250b090349400ea0b00b00c44007a5840d81842400b043c0010940403000d03445c4640c10001d034190700050120300341c680c0ca240c2040194090810202e4038040c0c20250396104144010361 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 16556769 1250 16555519 16555523
    0x8010302010c11010e09040b060f0f060d09020307030b091f020403030905091b0c01020405010e0d020d08130306050c040501110c01020601061409030604060c08090606010f08040305090901090b040e01020403 90
    0x70300c80c00d0099564001e0030f1004902040d040c81400190301e01507a450784030403031156100c1d030350303056090401105209803c65048082c03441240002c0002881c3c0c0c0b94032003501da8800d60010081581140c50000c60b0500c00150005400300c91300b101081900c00e800a8641f1007002000399100c100c072110a000c13800c9004d5404010005411424104170030301d060134005030081d142c44140c4510010074811030100340c4c442d0900ca88140d4020074100010340e0080b621441a19090303540300c82c4501142c1c00a03840030340c00d020042141001150038900b03031a2005280c0c010355400710041109003040e0300c0007100d0760014071a1a00295452400900e80440801c0b00d200102060300246840e900f040019100c0c0701c44c200c441c0c11500010700500205650400c4201c1c02a0300410000500340c1c400c200c0140400c000a000c1440c80d404107040c08040d07680201074240d07010f040d180410306501c41e8641110075200c0c8019079036000782188008620184540d00000c42ca08044800300540c1c1015855a402d03030069100c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 16558019 1250 16556769 16556777
    0x10312110304090507110d020d0e090c0d24030317011d060402160503030a0b04060807080622050f0d09080c0105030a021308060408030103021809030a0c03180608160801030201 77
    0x20082c1c6941c0ba0440e40c5c0185290800d240c1204845044914003139181c01d1507801a404011422400c43d04071084200c6420140c942000b1460403039069144c51040c0703140d1604295903107180c602544542103e100241000301c10740c000203646c1782001000110300140c1078050f07100ba54000aa119070b181401840d078401094101d807181e0320001080025080311140541c141e100c042d110380002c900b880258030814583e6000980000301c4014001126080c2e003002080d50710000c002c1c441c1000c0000d2542d4090003800c10b00710514000281441e100b100c0550060951040c04d03076900088002149000503006907586881e00d00e03030344400e199542e5400071200c0c1d002c140c003000440d900d4010340d00208198400c0c02e100020311076981c0403440ca0070300200ca0a464030080400103008514004007828604038200040c81c07581d00380013282540328450303100040c0500c803c15401c2000c05015103842141180c0d0b104442202c45d07542e00b170143c00c0034412500342c4804104c0307071a0300c4d25007402405201c0c142c0f901a52 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 16559269 1250 16558019 16558027
    0x8010c0e040921050d02040b0409050c07050a0f0c0b0c06060306060319030503060303130623040b0f0306030111040b0c1c0207060804110d0303020a11060105130b180705030103121103 80
    0x2032020030121030030340c84100704d010080026001500c3c00104000c00d0900c4041c2c2c0e45600e0b01051404860018046540c210340030083e96000c42d0b0001040d42080340c0207600c407100d1044501d40b0304002c5215501100074100007040f11821080f0106085125901c00c1c2d0030348070b083d039905081689601c18500c505128180449000b00802c0c890b0002e075500a0028040b00d14000e00c68900b0342001c004c40e4001000140c807261000c030041002c100229882d01c1c6510064140f50602c0701ca0000c500940035000c080100100000b00035503825080b41c103100700c0e452890fa61301e036101d003d480402e13401040441864411042014011024250f000c0080c5403154080c0c040a41001d004540146000d0026104107030070217480d05060f99030018801c940c5109480050f51030303181000241442d16500b00001064020b8401084942c85145006c18000c0c4d0320032000400d20f620000140d1507203002c2d9008118541404104800a500100154162406450f00311250180708504a4001c4030400c1c00c40040c0d0000c0c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 16560519 1250 16559269 16559303
    0x915030e0307020913030906020102030403050a140909010e010501110604050c0409150608030403030809030901020d0e0103140a0501050910080a0209150607030309060c02030f04031202010b0a08010c0e0409 90
    0xe40418039004500381940c0c0340001c10740014183d0304d01a02c1a1500f4108464080c0406400030007480080542d40020f500710300d01514081c2c000c0c060715070391900340070b410703280d2650b540780070300807a90000c000500f96040307543c50b001c42c04131002e824026180402c1c0ea1707000302d08003000e0010350745110350380c480c0003001c8421b030940c103010150841000031941c0e0141d540e00a107540c0c201c5d0040c1c601038144240110740f01e51941c1802021030402034440704558008000078005640e0120348512880034909140d80d2045242c80101e000304980c0d0740b4a9240030315542400070010322a04114120380c3c04803080d0b407a50719900706140284040340708894556208030920401800e101c624680d021014a00300580042c040703000c184c090344105004c4001036501c1442404101d89032094001140139031008600304a29004040807503c00c9010140110450650280186100350003400103194040c011409055541d84598041c0401c00c20a0b0049246514010504e061900c0703106a081e4101c085000c14000380c0c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 16561769 1250 16560519 16560521
    0x70c020a050607170403060b010311070506070e01020f01021317060601080106030b06070210030e100b010906051b010204060504080f0a0b01050f0103090506130b010b0c07030b1003150501050102010c091503 90
    0x1200702144d2005950365038040f040d800784040d00065010741c030b01041c1800818001002c4850070b0b14003074441001071104001083c0001005a40000a0309000c00c1440303068006034034080368824400055800061110f4240c844a0000e90803246406100301c3ca920300040703c1516040100e0700280040e05076030040043c1807194208408d2082e001e440303036190503015000f0585291340c050f94130011a86600f0350010007803007008216034082441400b0051300c101400020514001481090100b01c00441d1100e00307401108101c0d80e402241c88021556582e503680041c100343c20610a0200d180952041703c4504480410a4a604d5500c0520040180c4c20201080b81c010b0364202128105076a4161010008404200560056804000e01c007401a03043c54607a00502d4141c00120700c80c18103100c4a52200c0300090034800f9203610459006050380c52041d09140c40549520262201c1c0c884c1c0c0074a03198450542c0b183d4180c40b001c0e802484400701d9100305843d0b240c4d07507124081e6400c00010440284500c2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 16563019 1250 16561769 16561777
    0x50c03030c0d0c08040e04290405070603020c010609060e1e011401030c110601030605100501020c100e010c120302030a0b04021903050601120906051501080708040209061c0c0e070c020a0506 83
    0x814044c60b030416442e0401940c03006000c40742216a00800a00c0010b08203882403080b200c031640070250710203450103507206a2286107501c2802c0a0680100c2c0351420080c0a400402c0585003a40f41003040a44c0e13082c4c501d40c03002c0f0680745071044001d80d68040c04810131010441d416692507091204c0e120142c04d00440080140401550402500c51100001d001c0240a114000d60107003202040c24100941c404030303d801d076075101b07d065512030300b446d80036a21001d680e403820444a04002e002c0d00301140043e50281c4440800401d107000503080414040d8140d07010703502659004400300500e07a00700041c40120b04c40e14544400c0c05a0b0f4a02c21a10b10b44a03130480c0394082410b14040c1081c078540181c800540307081c1e1000701c50311a281d104028424200e04a00f5210340400d19000c1c2060800d594094145900a000039010755038080010f0a6a12610b1119904401d128854101c0100030305007900c0f2428280034a000ac48440750104d410203100d0060500350307680003050b02040619141c20450b550380 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 16564269 1250 16563019 16563023
    0x40305070602160201020d0e01080105120a020907050c0c010c051c0e120717010b090a110405060a03021207140409050604060512060103030e04050c09012303010f03050c03030c0d0c 79
    0x68208806400202680082c00504240f4401e114495043d0710029040c900700000c082c0801400f0000310110340c0c0c0c04020300b4110307827054030a0074150340300c6070900e0304024640c6400f94100f200b03c01480810b6501000610880d580441501c140301d0f5600011100700c207192001900070740c04048036500d2009180300108048925040c17550700801048045182000d141c0140d05c20382e0458403041181d0300702c0501d5a00a0040b00c00200882c140e07580005881c00400f50651000039680d00200764400840011a000b07404000c003c0ca45030910244000c000e944142c0c0e4007445019400e01041280e40961101c1c4507420fa4100040c2c10a030600d10308a000f030030020101a4000d846100005851715802e5140317240d81c0a2102819180d819818050800324034242203600403881c140030040da01411800b40e40782c0d0304091814072100b50b6440c0181002480f058000006404000000100d04011200d000b00f200d2181c4d00f030705c05120031a4200354890141d2000c600c1c00b900800500c030141445009400c80d058 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 16565519 1250 16564269 16564277
    0x806070905040506010905030d090303030f02031b0705120d0501140d0206030c0a1701080109030219030212030703090c080102032a120402030709020f0d0e0d0f050310030506040b07031b08010308030403 88
    0xb1f03560f10700180c501080b083d902c80201e00c02c14818018141c2c940600c564040040c0b02c1035166060607400f07054002c000300024079000b040821140102700b07090000c02c1050310718517005031b101d1001da002100104400c3c440c0722050303400e0a1a060640c00d09045050300075030020300f0303541507a58026005036140d005602ca4000c110700322996040e06681e003a6064040c2c901c0000004401205140c043d141180115034080581080440100000e600044001c2ca09214002664a0351111030302940900458a0028150404110040384051056018501c58800c1841450105015182034162620b0f94681c0a5596070200a0b59560440e10100c294025102404585035150341e080e14401b2070304070f0503910121000014944906691a02403649011606c80c094a80d4601e8448054040f0300d03590b03203441c203014000c4002000b42091950f0000299000300981c4c0031031402d03240500c5048404c98060000c24275041c05a5450101101440e440c91810384400080d40d003941c41c0d40d19607810040c4210104 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 16566769 1250 16565519 16565537
    0x5062b03080604060902030a0b091b0d0c0e030d0c12050708090d0302030909100501030b0901050d0605190f020705011404020d03050f0d020a112509020d0603020d0c0906080607090504050601 83
    0x3849440290700c034400308d031000214005403404015100401900c408100b82c103d40005801145050454100400003c8005034001a181c4d0035901c440d00010031503410f006203c120340806030030103c10461140310b80c194500030b4070b507000c05031620b004006c4060801c0d0700034080403c01c1d00704030900f10704880c0280100c80c101002c20340010070a038021035801d6000c0c4241d4208101950701400790014500044070a9501036060130081100345100700c01c042c1c17807140c40d90f01041038a01418501070081100150034441003207030350010350203548580b034104c1d5207620706244411503506c0016100c2c00740754001c0542c90440101e032401ca40383c2d000100149410001003159510b0150b591000382190350240d21403441060080403264103243c100c40c100540d1007010006591a04141189681983c0006c100184c6070780d100c1c58480d0045c01a500002d40188001180409000b11460210212162140e05004007501d8611b0551100c03c20382d10000071038020841449580341075040140d2146041c5004804 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 16568019 1250 16566769 16566779
    0x20120060103031707020c010c120315090204031403030c0a050c01020f0301030b0411090606030a090c08010222060201060311010e0d0213020a17010311010f020f0607020105062b0308060406 83
    0x80034001e0380200c01007540c0f070000c0e0712a904141200c2d50300c40041e00242019501600018003102c42d91000148002c041081d4207100b540254401100201c2001c82e0100e02a1900035800083d07200380000d0b5011a40100b0707085642900100702c2e40b00d0108003150600b840c21581054034140c21801c0120140e540a000d1140400c40f0180954003d60080c8241d0f410340c11300307050412499000004843c01002c0304030030090b07070f62201400c0b04c2c2c0001c50303154001001c403801d0078441b000d20150307007108650754000980f0504000300748074190803040e488030a002c1210394a450690894440b44030040118080c0c8004156a6001c0d080051794500042c281e0500242c2603400150030804040506511560102c1c24201d902da00c0303c40c03d0320710500184546c0c0654116144c40d542d025038410802d0401601c00f0422200303034801c8c081055009514801c913003850a18040181c0a00401c80306240a5100703550205000c0d680155040014125003244c1000b04559440865042c103004003666000303a100c1c100011 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 16569269 1250 16568019 16568023
    0x705040b0a0f1403040c05060a020f010908030f0601020f061902070219030b0a02070f11011403090601060f030c12050c0c070305010506090a090b0f06030a020a0608060109060504080a020120 83
    0x305040ea40d01101c110b10690007400c0a4100381040282d101c042c002c000000da4134461110980388100c1d4441c1e162120820102d14000800200440715400c0a008108100840000d140074400c5036400c0c030a07558170240120703501c02d10002071106540c00007012440005051000003100d4070b1140c0050328201c990b4000c00e141c050300014070038016003046410018021700f400d61030340058000e03c06518010300c40c2c48006040040342c4020341180030181c1c00280c0c5a000350301720040c2d0005c0d440165120f20f80020310030340b01c19092003240c01143d9042c100c82c0300c0c14440d20a11842c07403810384592084102448001004107801403110f40140d00800129043c0903081020720f006500c600300115042ca40b20040c440c09640141134000c8550801c00d400c00020640e0184680c07010110011b14401d45d0b0b1840000c0c80c013180010041e41084c001c0c140402c90517131101089108900130703210207001c140d4884044071035110314410b802158001106c8038006610a08c0d003032140c0f192103501e42140d0060441118 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 16570519 1250 16569269 16569277
    0x20a0b0709030210080a0501080303060d08030a02160503071205030f07030903020c030618010f0b060a05030a060e0106050405100e03190501060f0b0306011403090607030e03120109020c010b031606080705040b 91
    0x4000c11703c3c20f810071440b50710900481d4050000c12024500390709052000c1011301c42100030040a2210100008014400301e0741034659490200ca0036000d509a00d040c11500ca40c450300d02559035100c2020141c032400e00403c02c8074084c0c9a5495148035554440000300d0080c00360031000c4045014a40b60081a0746e0204145402440401c3d840c1080c102c50f1b000c070a0840b0442c0c0c0260794072604140103040559107030300c1a00c0f40c06204e4106a9520f54410130041d0043c082c03600141d030f01080030b0002207002030340400034106541080c0c400d855030701c0380e0402c01c1e6044220724043c140c0c19403100c1c401005000380b43d01414102c610403400482c1140e120a0074100807041d07600320800c11000403003001110360713010000e62104007800c0b0080c0e00d075007000003074561201001008001455120002440082c03000c104441603541c980e603c24000f540c4807500c0901942c0308002e500c40543c00d25007201070910340072442251412609403900d82c0c00d46005802e0301d05c60701c024180824000c060100107000100c3c00024 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 16571769 1250 16570519 16570549
    0x170312040b0718050d12020a150507080f0906010b09010507061d070e041101081302060a08040b01080d0503180708060f040c0f050d03030b060d060909050d0201050601020a0b07090302 80
    0x2030381d1a00d482c80004140c60104007502000342400c2a040140341c039401e02c00700d00c081e0071209080500c50380d0141640381c401c241030700508080d944c0c950000c01901680c8054000c014030350b2100c5640c0c035100c0c6006101c0f1820740d00880c8a411010040090910070002484505011b0400c07034100015511418229548001d6499414000c46011070451205024503000313040440b100207a00e007426202c1c1c80c84c1c80c04201c002418040e80314080381000003e0a01080f005900504881c0e60b08001b43c0d0040c450182134400311600c62901001240000c07000c40d4000b400019607aa407801c6940c2c2c45004e03c82002d0302100041075004081002c2075105060108500c5940c001a0b905000d051518101c00c0c9005584c0c8080d00c502c4644005225560390b804034407040a42501d00429100392a0b000103003244560b50b14034400500d8184009280b07001134010740d10250040c42076413408041c0f240d0603400d03640100c130690300681040c480000007400139481907800000c2031900b031050036283d5000c180c403103469402c4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 16573019 1250 16571769 16571783
    0x50105010b360a121703070f0e0105042301030f020a050706020708070507080a15151221020d030605190605160501050411030c0a05010824030a08040509070c0c17031204 74
    0x3000c0c0246140f18175040202c1c0c0c92454918502104010004640701d032000e400c0154081d1241801d82c424000d0703c01401070010150300c1c00f0000c4001140b0303a085444002e000c2410481301b007800980078030946200c6501c5813109441d0044a84c2c882c2d0095100c1c1c00100d801d20310a0100c1c1d0042001040164007801401d80104290403860070a007110424403000ea00011b81000c0c1c40c035070300350103541003407040b00c1b081e506081c0008123902d010216524103082c1007410b2020b019403580c2a03940010341240746041501d04011103912182480400420b085060080c2c4000c02c1c0c0c2044518861001031241241e4041108003003041d658a00d400d454003580c0035114000030402611482c60244142c0950010484054810b6454640040c085480007400d40c43d50007000c03202c200c9501000018010744440040a17100490107a02c0c0600994003d4081d0324001c2c141e82000034411800b600281c1d08a039003001049103406d203002c40890080300506426101d40c00188074205194400400700d42c0100e01c2211 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 16574269 1250 16573019 16573049
    0xf0f03041502040f050405040203100905071a0f0307050f0c010e070306050108060702060103200a0f08060906190b040908070b06030c0109060c08090a0b0d050103050105010b360a 78
    0x30146080071401d0748200003a40b0411041142d1300c8a08410403c660302581c001c80c40d503445000181c00c200c90700049249036070900510208108010581c2c0c4141e4040145140c03a0256061441500c1c1c022059404403004c020008991001d01800c060680703911402c05051402181803a0349003036030300036200a81140d22041d400d100b04452401014058140c0000803c0c043c40c10003002942c42c03406203c0030b0010002039811409074501003041035070800003d008c90741c0b00740c0d07108260081100e0070710856200c0e0144001040720a4400303d1310310b002c1d111008a0944a0f0283c4220200404090902c1a8031070758822104000541c004064a02c15008030146403142c42d001c814103050002020b03805040268403041441200c2d00280e0300e402281e0003403911501d80c41140041a01105180c1122a01c071101181d000f00010041d006070341641c0c443e40007400380d642d03101c030a00d4550040b091070000d100060003096404070ac20610300c15800c1c140c000c3d452900351000010466503100c80d00210700da2001c1074 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 16575519 1250 16574269 16574273
    0x8090d1b17040b130501171501050c0f030d050a0b090c091f020307060605030106080a0f0c0509090a05010f200d0b040510170601030218100302090c0414010e030d050f0f0f0304 77
    0x244842e004040a00b000400e000b103151f02c41200d800d006040104050b2072012011069206d074082c3c8001350420000c036aa454542d41c9101c0d665044030750281440c0c0c2c2880001810284030340500d09013440c0c09480181c6548982030b000006811105509402c000d00d0b05925003505441740b2916007646598000d15541c80403420001c041c2c80a60300075034003aa061044c100b04440e80000e06c0d401d442d40100ca03000c05e4484a140144002690368803c0e80c1c800000c00c240501c080b004035040202c0d5125600801c103020b40d0f504107c2c140e8420b0451640e0780c030601e42c6202e001a003840000c0c88810303054a00042e400380a08005404c4032400c1c5c400c051040c6140406001c01c100a64075501d031010300d0f00c002e200a601d954000b07440c00c0728010a00725080c0341c481c0425042c429500c1c40002844e4003c04125062400601c0d407101f5410500c1411001d40d03512205440030b502580c7c103050143c1002e0007800401600e00705c00c1d28154080603400014203810844401c1b10701015014050b004400c560403541d07401c083c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 16576769 1250 16575519 16575547
    0x80415021b060f0103031e0c020a03060209090a060b04050f06071205030601020d03050c07020103020f0c010903170c0c0c01050315060c01020705070f060504360c08090d1b17040b 78
    0x100108a90f480310700c01031000c80e404c0f0704240d8401030074149620648516040c11900004008030080d08400281400300411089070080c15064a055032151204d6590035404001d8410510401d460600e042109010504100d0204009d8000181090b45000c8050750380910800c3c9100e004400607602100303220140d0b80c140000c030545051450305118a0030070765607030344842c0b25415000381410350002d401005601c00d2000d41b140e01f80c80800801c203003000750070003501e0301550b44100c2d001c3d5204100044c0e4074030204400d80e080340d0300450051409540010043d5071a80c400f800da4a6a450085144003881d50383c44014042042103400150700c98200d0f160041c0b501c0309542080305e04a0008805104150f0310400350f0703044620490000d902404080c103006401d8a601c43c4c0541c84984480ba40b242145045d0001c00c04c00900366100d10a41d515141ca41c0c0c0c507a40301542e8440043c5491040c04a64010050320200359401a400f050544c00e10342c0400156a1056010f95041040030038a1080810350b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 16578019 1250 16576769 16576771
    0x30c0606010e0105090a0b07030c050607081501080405030702121002180306060306010302030d080a0b0405040318060513090911060a1709030910030c02071802070605010909080406080415021b06 85
    0x203007446170034001002e001886035596402071401c0b1000208245051620070100c1c01c10303198012099503d60f0500543c0101101012100d8055044207102c410300f182d44611042e9100c4c0d900480654100307801542001403c40d243d40c50b5106903c80d0b0054192084003610040030245d64400044081d10000424142000402440607100c1d421220040025031800301b03140d805213810349040241175907809030100c010140304a2042d0414a850100020180c10003150b18424000c680100c208580d00c3d4001c442c03030320804140c0800440a0202001030750741940040e00c0315071180340171030080391711400480e0300b613040701d080840050906440c11000e2006161180c1c0c000350742d04065071900d42d650000c5461942030000c071008140d0713121703c410303804c0380b081c0410b1018080914001004003d580850000b0f50001c01080c1c504610740070000034035008c1c612a0b01e00f49a80611124142850107000b41d590110052044da000002c4107040f0072915214401440200c1164241210f0003910100d96850004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 16579269 1250 16578019 16578047
    0x90b011704050303040803090106090903080a0f050c190201110f19020105010b0702060a0314180d0903050a060c18080d030606020606030c04051005030105040507090e0304060f0804060e030c060601 86
    0xa02000c1c080440c0c80481100c1d03020340c12100859481d103070b000075140104125801152501c1c0741c81500c90400d80c1c0022a180038050034081800101c2c1041c140344200c443c1507032103a0300720a04210900a80b000c00b4148001030056000000c3c03078150450b40041e00da071060030282c08020000400e014417100d11041b4840c98085032000300003540c1041d40c801914031030b029000e40710380f00201b4842c20321446130304519501404211701c10501e0400c1c5c0400e00842c100564440f480d4096400340c400d01074444c079403100c11650414004c2003410204c0e1100700080146019810400c00401071001d82e03445035080b039000070b1400384010705030484804001030403100290003c1085400460074001303240d03000551800111422500096151a811095180000164012a015401d000c20001400030128180c0c1c221061203500b440901000755840b07860388154003508010030001e0094100c243c0c42254815130081c441d050000340402802030241c60364200c1d2100c041c05038001c504106282d6484540505454 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 16580519 1250 16579269 16579307
    0xc02030a020c09060f040c0206040b130b0105091e070203040e0105090402011d030309030a05010b030105090601030507060e010e0a030605041505130f2109030b07020a080405010f020f0106090b01 85
    0x304980000e480c1c580503141644142d6103c030210f802031365189488041030100420030448035040c3c200194a8090494050f02c031800d070341c2c00044407251100c402010585c0e00c41c4004045a00342800c002d419507001e0060340112010312b032508200301c04c0a00b614080e468503001592528035252040c154404141c1107507001d00030311801d010050341c1215a0345280c0540b252001e401d6070038280420b1071801800c031060b5052141240204c10312106500c640f40306801034000b440941d0703640740c00305d0365090280310082040c1c1c0010010030002d44141031649004005240c503007016803210000030702e0912103410035101582d981c01448100003850803400c41c1d01005040c24000c6140c02003820880f00746404000e844c850403141c41408004003c55403696200a0300452000c012000000520700c00003404121450891040895140e80c0005100d20446030310900003454141000c0045481e145804000c1c42503216040015103080e100b8003e29020b01030802d8000360100d0388000060500348100b6507200b0710 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 16581769 1250 16580519 16580527
    0x306050901020412150e07090209090906040b1305070803030a0e060a0b060a0f120905010b01080a0b0a03120509090106050a0f031103010b031806040302060a0f0507021c02010204030501060b09040c0203 88
    0x4801c10131603810b00d40b9008081081c00c102241c403110090143c090380d1031034030b01a2803000700b40610b0310b0b805040d094000b982c120105580f03c9030300d903039510801e56000d00080c844c00001624140c00c40d81c089802c900c10400d03200010f41c1c8140d01e91640e0410344003000c586407034049201d022081004185d80c40110403806004035110100440c200b4445c4012000402c00101d4400554901507200c0000418034480200401c80003070400d00e00070f00c884e6444a000954210208a4040c1e1601403a210120010002034200313186903034084850143c08071501c10701c034041c07181c0c40c0156180d84402d0300808260315015139403911440014084590f40114505042c0350003107000400ba07024050324150b440e00310d006ca40e039444405a109242003001d104501d14852007042100701035001c20000d00540c0405028006c0d0302401510005031002241c44500503400004800e001d8005644d4001c0d1a0307440f400010316060302c80d25281e0942d00e00350041c24204c2000548040b4070b0400e803047c01c0e40000300717101941c10 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 16583019 1250 16581769 16581779
    0xb040c0903020105030a020f070c0302030705010c0825020301150806060a08030301090f06031b0906171506040b10030e0d0801180203060f10021f0c021002070507030b0903030103060509010204 84
    0x580c480a0002904001c80030000510502840d030481d001c504d40e10056a4503191240303488155000c403804128003900482c540002e0a500508410540c581d00c01101420051703013000008001c2e0352850240760f50480c80401c0c10240e1030038414482c080390b280440c03812003030070003201034548030000c1c1119001e1501c007201041182804016203054072104100410030908015000c07000c0c0c48690406855a40c82d4694121050784600c02e40084850103a0300740b0000390b5440c2c05000140840c0040c86e5039030010050b01074403d600030701c4140d00460041002400914860105d005072011500c21400b00e943d64954220309001008a8402a0640e2625101e65810b00f001c4002490312013114a1b00390b5008004150543c2c1c80341043d103d460000f4002030100703480a04000c0d511042c0c400708460020035010305045100300c50051013606441c0390010b15540e0005594200298170070a000d84450107074080100000702180d1200b030052504d20020f50702c950440c00d00a00301d450180c004106a032041104101c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 16584269 1250 16583019 16583027
    0x605060f060703050c0109120801061409010c03080603072d1202010c0201210507030506010305060a1a070609020a0611060901051015110f010e1605060702040207170408010207060b040c 81
    0x902c1035041c6080d54aa04464210314003500c0000d0001b40340d11030004004840c1d43c3d01c11302c1241220307155552501c0347c070010300d1402018800e50300303881d0025a442e0f02c10408680507204140c0c00003c06801c80c0c80090350b841211000f05000240a0000c880001c40b5011801c022030007e009807954068040081d034266001800001090b03400030b0501c40a040b0b000c024800342c0141255a0200c08004e0200e880e00c62030050050100302c0c0c440d40803030f180c03002143c15418406003450640d0844481a110001c1e0301d1111680c9070410141154001d440c0c18011006846020380e0b14020000c6444890142d00740680f40c60030040000e10314005603140804000c2c1d40c1b82c0c040039400403035141c00c86410f01c440d00c1081c101c40c4890389001404961240d9070a030ba144100552015450340d984070242c5401c420700700803450f0360400c06d00c180d07503202e401403111704003602c0c0039402040700303a114100c080c21040e000c0f034203445035030069807000040f6503011800e0818070216015145120a040340d0070000700e28800e1010b0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 16585519 1250 16584269 16584277
    0x40f02030f060409050f030703080610110d0809070302030109080306090105090c0313030e060a02071404091505070309150606140405031903030204080106080a05070906051f0504120605040605060f06 87
    0x512841e100e4580c031045c0001807003503d8281d058903040d242c1d64440c6040203000c403901603030700300e004240111800302401d04c20030b13030500d07507150f4900a0008100a514100c40400024004400ca40101d81b00080140d40074030410030740b50302c9003070159224580803081001000050303015502444030b5000f004141003c08003240d030f210210f556070341c44d9000c4609045809010351030281c0d4000b0310003c1c2e90300c907190f00060720b141256100b24002001d4080141408151244000000c10520a00c0c81000c50450103412070b81d84001c203880c0004441e40b05403158101e01442c0c2102003081907940d003060200c03c1c0d0007040c43e49805041070301c280c40d052520003c2a40c1e050740300c10460401070403503800810588207404031401803076840c0080c4011601c0745a51a11605502030407280c9118003100080c00b911903000344421100001c00b8400a807885814151017007034190010410020b0401011490720400e075080390550780640000540381c602440c20780221840a08524850b035040001c954850740e40e40125 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 16586769 1250 16585519 16585531
    0x60f0504080d0e0c04020c0609010509030901020c010e0d05010203010605030106020705010c02060405010305060f0907270e0402090403020a1b1d060604060507020a090e0d0906090305030d1109030f0c040f02030f 92
    0x10207101c0e000b5080d0400d10400a100c5d0b00900016010702c8903c0300180103802422150000c0080b038961481e05642e0f131044441c0140903130400da04c40d0315079601452400380020b801a012460700e1049503a12403c85c3e000342c000e03601094010005001c2c0682c1001040041c01d402c0c202000014440e0300021300d10f010740d10400d4101502c0d440015225181c204407007500c154080e2a111690034203c101511380c03078110258044415400108001c2072145a0f1250b0845107440d403845403d484540921400e03000c014001e0302541700c0c1450510000d00720403074222084000401030800a400c000312041052803074041c132601c0200300c00c103000040ea207000444044a0103402c14655a5a0600c00b0410614284d070020015510740131800060441c0402e0a800541140e95064016a16844180ca403e02c0901002c0c0c003682c000d009a00309405103070722000c3c1c0a80f40e03008090070300318480c00180c60b0140c1e218449896401c00c002c2d4036070741d00701805003000d0700c5e02111042d0b04514000c107048100c408001d002d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 16588019 1250 16586769 16586771
    0x6010e0a0e010902030a06060501120b06040509130c030c030b070302030403020706050a02150108070501031103040c09020a050d1a04050108070501140904090c03030e13230601091e03060f0504080d 86
    0x2032a407401e07000d41c00b10200e581e0143c2511506005030034814020500c0d441a207000c1142d02e910303140303100581e20650180d584010011406c2c20b0611040c46801e1000426007880500c00c4804103020900070703050301004501c612022005941185481e0040030b0000d0002814980103005110000382c010414006491092502039141c14a0020403032500d01442c1940c103040c0c40400c00814541c001043d2001900c03008e80b02440340304007001e1940070500c8221400350240c455103000b845442041d40060803444140c1c98032138103040311403012034203c48403446103030710420002030800c559061034003c0c240104043c0028104481c50328002814040f5111180041c1d4400007507030341d20580e03482c0d01010300c0a80100d00c5c40c4c1d00b652a031a01511f5000703602d40c0a031045801504040c2940520b0080d500e402c40007078000344030704146400c8422840ca001c0c041d02d052102c10080031503510884a00402c0c4d80c1754011104004900d903062407000c036504281050406400c1c042084040b4039500c2c1100e100401001c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 16589269 1250 16588019 16588031
    0x40605040809060409020904110c030307030c05130608070806040b01020a0b060a030602030f010317031017150a09030e0f01080712060909030309060e07030c0b070201050f030c120906010e0a 83
    0x107440a03051041d803002a030f00c032401080104041c000d95016105152058508005403000f145100d913440c051000441c0b502e0f07200704000350403188242c0140e4104150750400a0600b401e8a0105856882d070760400301c005038400d02004401c5900845407900030343c06503020090f1898840000351507000e081405000e02860b100031070415140c11507104010b68002004640303908110402e2101c20381c0a1100303844045524140d500c041340340e8000c07203000b807909940840711351385082d0b1031604040141d14448418090a1400b40131510700300c04c190f224803d41400000c80c1880d43c034025181048031007a250103041400e40b074010344d98019507001d130048d41c40d080c0140c0700119401c4020180c41070f81c1060b10131500b4004044101034041d04031511880c0b05e00800d1101150741d003d00381d40c54110340b2000d403001131881d13400c0085428003001070503c1c0c3d0040c904079113040300d01b1820002950054600807070308100040c2c0541c2d0401d00c03070135550b00200300741c000d400300c0e500d001d0311040c80940c090540d903840e90380d0394 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 16590519 1250 16589269 16589273
    0x70501030b19080a050609030a0207180216080a110106050a05120715080709091812090801020301230604060525020d030807021605030703080304061104030609050111030c0304060504 80
    0x101c040d0103003101d90450300c1240e201c80c103c0b81c81c0c1c0d0000f00f08446038410b10000c00e05a0340040151003440411b5402041035a10341101428113041d808215043e01e80d00b00400c1850300740c0104118240790003400070558509048500609032041e4012001459240c480306100641e11588004210303442102c10180850074a190641001016800700c102d5040340d143c3c65011a8224030710038440c001940b5014a000d40d20940d030070580b0150300381c2240c010242c2e4070b810300181c2d0030900b04185100034030342801c0d41c5880700c40960032039000b038101d407016401941e400104500342110a030340040080d40d0719400d013881d04901034203a00815000e50007055841d440250080100840c48620705d8000f440d4145111050a01910301d0384151140401800384103407121440516003503040071601c000d0001d00c03011780703180c480340c6041d00050801c4441c640c91389140303854082d002004e88080c60003160300044004061070040d00715004060380c00e681e84070500803c0081085a0140c0341d000350454070210300c5645034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 16591769 1250 16590519 16590529
    0x5040e0402040504110d05010b040b010905010206040b0a2405121903030207020312030106030f0c0201061203030f020409020a020f01060501021605100e03030a05070501060b0301050a150302090d030c020f010809070501030b 97
    0x469615040521b529105003440b805400210190005030b40c100304060300c54004444444603806041c1c090380c00030000c9000610740c0d690999010080c220001030710326505448518500c403070520f41d840089005428802460044454041c03000703d000189407801c2645c505011000324603002409040d404207111301952818004c800d00c41d60074115103070341c03036854940141c0100000a041c00c0d640740341c0380c41212190b005106000c140c036603081604880d84a0340e41d08070094010718064010b01d0350203210000320340d021380c000f40107a805141c014207052124809918211081c551209045501255064108050b00d03503031501036400540300030b10b40d522944400c2d00c0c00040c41d07000700e0b058440000c806403000e0780300d009414500d20400083c80070964a000001a5010030700403960b10801101c001c0011040100401c5060191400c015003400e21500008110300c0d152082600407511100c1d0309405c5180c11600440b6019090070000028109545440e42e501c41c940501418150b6034900800580e540d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 16593019 1250 16591769 16591793
    0xa030e03030f07030506100504090b01030b030105070915081909050c1513050402091e01090e01080105070801080a030e010e04020d0e0a03020d0c050607080615180108010605040e0402040504 83
    0x41100d0752420a000880d07407107001180e02c440042d203004007181c2580f500207122003200400e80e5405041900342002c04005002070354096040c5a40c801c05100940c0b000c0c028a88102265180c000b07038030307162030010803003c1e2a17040302070308014001c01003000700c4e1354011214400b01d00341c01000590740310520309140352408007117116500400b6440e04410301d0340fa0500500c20124410002207402f642ca4040c0020b0740034040155038003d10070f0800700b503c0452061511408201450a100c0042da00c0f01002d46040081c0c21200d5980d458400304651240c024196078010200b000007400480c0300c1c1c9d00c5c01003800d0710010200b410407002313100405480d9a56010b0b41c4402e03c1d4200208080c03c44100e4041d80d802c2c1105084025012700946041c1550282043c00d0308150044040d107116503810808450b184002003180341d1145903621503080d04c44011740507058038881c0d01d10b440b0580c402203001510002e0144c0c80304041100802051103558a03210400e9005607050302c0c00304290703c41d0301e040b9480004c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 16594269 1250 16593019 16593041
    0x11b09031205071b031103010606020309040203040c030210020d0e010e0d03140f0406050904060602070b030a020a03060b0f0c1b0102070303120f092001030902090f0405151501090b0c0706050a03 85
    0xe4104602084c072008240090116440b0704041c0e003491000b48141820380360f0a1040d43c026030404d0103500d40310304041e0001d640c00b500c03822202c94010b8503035000032218840c6e00e0304072005902070300c5041e408581203240700180403403d0a101d03078031901d0036002850744a0788940090030000034400001ea0902c2c29415622100498050152155240d000051094000c03081903480b0310b0a150000504ca400840d40c03100b511003903d000342c610340d11909070704065445101803100b0503580d1040000c06001110140049010b00c00001c1d60b03035550b10700d07101d16103182c803d080c035028043d5504081e001c1c2e030009180c808a980c14101146800612281c1e000244070054480c0d4007241403031040c100b00011004607036404180c0c0c1d003c103c5140c0440004408641c498a002904103100c0300100f4a54022602a140d016120344110340350010341c490300c0515503005560300e400e6071010b68040c986e10360b000035081d40074003ca034400c10700340a48100b885540d803616110740b40a20000007502007000d4429049105401 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 16595519 1250 16594269 16594283
    0x1f03090506090a0c090b060702010c03090504020318060703060b0a0c02010c0c030606030c06080405030901110c1908070905060d060506060c01050f0703050601050c0601050108060609030105090f011b0903120507 92
    0x46000803040b0384402100c9421640c02c44450804617003000c1d6482140060100a0030550070304241d07038010741d504030741c0207415824040310180c0018180d40c2e40c002144281044c00071020b207101e00941043c03904401420003000d150a110007803040c41104000ea032178421851500024021441c001660007024825014012100044d00403090000700d400c410100e91203800009201c9075680070403940c029098034001c246400800011a113903100c3d0341031004050b4a4419291080341b03d90004e03100782501000c0300070f031084030ba2040200070824442c0c94018109460144094a8101b0000f00840b0642000500695940c0041000c94607160b00741d1f41290f0540c8000c20081c20130310448204031701300301c2c0c040c1d000a0401000641c154444d03800d585080a07403500a10303036642054010f685041c001408a038218000340015441c03a0b400b4001d45000d60301c400302801a0a20316140c007820740d5070441c00000e10101d42c00381e02c500700e60310640240450b90082d1117105441c0e05c03c541140d0500c00c0000150000e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 16596769 1250 16595519 16595521
    0xc0622030605070206010e01080d180506030a1401090b01140f04050306070e240a110f0109030503011401080118050a02070605090c010906020105151311040e0a0b0901051f03090506 79
    0x7590311103402540c542e0211242d507030344c411003008105001d002c1d88039643c1002c3e0304211200e0046503030350080900d5240c080607068903900894900c3d041219400350464580701b12004050007624140d000d0060030340107100a07841500041c0000d2502e155109416800040400100c00440248d501030400107094942e14140400c00501c01010026a0340c400c0c3d6200200044c9030396031404012a91800c01102424040d01030400c3c0c038807050710307203010906010b6008a004110400e102d0f01c41801c6c440e4a80d141c80e54140119144a0900410018140700e0340000601c0078135420400501c070186103440110300741e52059074100290180d590000c1c0a14148014440981d101045014029000b07a0392040825910f0740100d0a94a09989074841620340e08265607240c2000c2c52110030510b0032040214003d200707401c1030703081a40030340d1020120654a20038001c000d8080e000700314007a0421248840c16504120020f00c440805280840002021a840700e65103402030b0050751303042e5000b030251050703 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 16598019 1250 16596769 16596773
    0x130e03030403050d0b0a030b040605060a031b0603050903040602032203150203010e06100806040b030a15021207030908030703021b07090203090f0f07030210021e0102090f01050304050c062203 84
    0x16a04040303200c000302070900e51100146d062010070076044941207001094540c46d241c84050041030068030b020307082407041d40e011010030b10350035080b0f64002031980e021390020324080c40182100c81c09000c45001e600304100c10040940d00000b40c0701e4583d800030302c0004601c004c50100400d00103503072004119034982c90a1250403019507015504850311841503084a070380f01e50400000416076000304000c15000d8021032902c4c01d040d4001816508090101e03140c1c608240c4a89d041603c040c890409001e40000b076062480c40ba2200d000d410a0340ca050a104a6445503a141c0303890000138907100030191301241640c5038088040030000c60384d80903001d5542d003d48610842003c0e50040f40c20808c944511950300d0071a95000414010032011500a040300d10300396800c12000e400303600c11036400c505c5005200009190b55541c0e5049405811000582e1340c04078005001d06401d500a0703040c140031040c001c102c0801c1d00880d041d040c04004480305a601c2003802440082c0050306e00c1c1009803440c1d03500000c41 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 16599269 1250 16598019 16598027
    0xc0f160303090905040b18030702060309060a180506010b0315060a020a02030601060516060e01090206040801060303020d0507080316020106091517070f030609060b090c0a0f0f020a02130e03030403 86
    0x2080c0da009030364400d8850b48880209050b100217840003002007882e100010032610f840c00010822150302016686800b0141d000114503400980b040030050b08000140700060580748201c1303946d400082001c031703041c800c1c50710795a07268241440344108690740080080c81100700803005139000240100b495444410340f0320000d55407205007000300e0080c4503000011a28a0040d030680c0ca00d01043c60300d4507003400640e55018050042042e50848030b64841c0500801603403188040c1000c1e1041c9800058000d1035400c000385000b00054448090210030880400403494020490350f201c0030085030182175690921040307004081c6644020070107454031654050207102089001c0403142c00d1100152190048980e4588032020307842800840d80b41d41c44100005440341c2c20200009005181c0058604034000c0411541081103030503192040c8000b614486140c0c01129068128401d4034000d10322540e1b02c800607650f002d585a0280c4202c1e4512500a060541900312232080760b9007000340e940340c0c102450082c0c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 16600519 1250 16599269 16599313
    0x15090307030804031410020c0c040e01061a210c0301060f09030804140f04060f0519030203070f05040c03050405280501020c1c03020703020a021c020901080c010306080c0a05060c0f 79
    0x202d011b00a15408420380f6000b030003603070030310945540502916124541004010301e00c8412250a55494104c0005d00c80c07001a41d02c940c602400c840340707907100c1005143d10a83c80620030b00b4002c1171076001c28489207603181d4041c1d034150f81c84e9082a41c0c140c0c0c5403000550711400c255000910003000001c0100b40400e12200703560102d103098914549503500401008152481c0303024403200d810014008200c249010300c0d6415006443c3d00c221240103889130003082c10300c05103400010140785120010403d60610744160304000c1c07014542001503042c0b030f6441545460101d82e1442c80d001c8074258044101000b5000711295907170190003195903084400c1c0c90341d1640740d000c5850007100424070a04032100c0c002c0c000c89840b980d140e405001c04481c5542048038500013800c803001525403c1500b0b00041e120302000724007034907102005004000b0000b000505a4005030000c842c10717040207205d0040c588540784007500b0fa480840d1100e4861810040c0286004582c0f10350081500c40c082083c3c03c1d503a4080041 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 16601769 1250 16600519 16600553
    0x1031b020c0a0b12041e050703050114060f100f11030d09020901050312040902030c09030a050106090506030304030c09090227010501020106140d1506080109060501150305061509030703080403 84
    0x80c0c199550f0302c001000039070040010300303010650b113540000c0005400c26118009000c10f0361051018254640300c861410440750400c0b01e030b982d0744145404c000c180710000079900801c1100c035209150016000319028210014419090040c0c00d90841a81801140c5041040c1492030840340c40d081101c08104c09030104c580140c0c09262a14008212400e0110300c155283c0c618031091460309140101800081d0702c0208a00c0d00c000c014407244200c0e6070203004100840313014000100341c0c80c0c100f00c0b000c4200d800c09022207100360700400c4100000b60134801d00c1d100300c0d82104000200e00650340041210300650110814202004040070b0b41d81d0204040d40302e060320700a030300230070a0360340381c0012024410f4101052507102804040c00c1c0002880e200e030840342e5074409035011070b0b00c540e81c00005e401d480c4000ea080f40c000392a0401480500c031a0700c5040242c500a15051081e42001c0012403400c0005048101c12180c000492003110b4404110100055900c0807003107a41d90303030741d0410126101400c603030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 16603019 1250 16601769 16601779
    0xe120109110301140103030c050c090c03090c030106060c0b0c0405040e06150904020a0b07050106030605010f1a04050117090106031a04060c0206070207050103090c0503010c0e0102070b160b0601031b020c 89
    0x7001001d0a05104000358003000c8400521964256241694924034810040310a07104180b1503e019440344841d89002d144140c03075a0f1385900381903160604125505000c2d500a070f14010080129592145407080b1540c1c000f00c2c107015a0b1201080c01545200d80e4114540003810405ca0001c0c003600041c140c0d1240340032800141407031813484204082084d0565010354010b030a4401480341081110052508a110304000285140d40b540c1d4074003691001d0303200c0221074100701300412002c651906204000001d40031014a01828800068600c2c1e09074101102141115000203410301003d602280c05141c010000640382004110b0383d22042d18212000c44400b81020050f010300c60001801500070700e0b141d0040e1082c50300344001140144120403003540c00c445410740029840d1801c0c8030703038249242c2c41c0c1e80d00c151803042c00c0d0002e0710303028503580306200300c61040000000000842a04801182d4007810909090302c0b0386004070050301d81101450002c800e0301000307130481c0f80c001649640e00c80c803c0d54 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 16604269 1250 16603019 16603043
    0x70e01050d06080f0d0c02060d0203060616030801140409050d030203060a0306020403080406030e01150509060d240c050301060806060706090506190c021203061c12020f0106140f09070e120109 84
    0x5c002c0740c03620754082c0b009401140c1031010386c9007180550042e59010704e0180103942420200c480611980c2c1c0d0802040d80410034560042c00646280311036407500b041c050310309200c05a61540c5a56a41c484000d10034201980071020806550b250351444004580000f000d5450310f44a0070300b000254002e00c18000400d1401d244007003816010b00031a9000560461505d01d15032402040c0000c28200900103a0b00c5a280444440010101803260304907201d401d4501400c0ca180c440f82008403501e001c5040c05020040c00104070032035010306003981c0414180c0c0d00380d48402251400d0700c040c10b2425002482c0b07001c0c11080007852040c6e1114071156205104041c803503404610001c0e81c8031458202202d403100340800000700d2608094900e00c402c0754440031461800704e1941c81d21205a04014880c2d40180c00600c15021050000d000d50800344c01e82185030700c085c9101c40c0009000003000070200d405120000700080004d8002c10000c041c1210240c4405141c42800d02c005008003a00c0e101102d0b0f0044001c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 16605519 1250 16604269 16604293
    0x1051306060e010c080c01021b0607110a0f030507080408010911101413051503070305090d050304020907090e090304060305090d0903020913150501050306060315070e01050d06080f 79
    0x202a64007210110740701c50b05074a60701001180d8140c40b981d415188003100301b1400800420074030091030388641503c4403840e60114130306003d0400078040c04480030020445a90703c81503030046060400e080d80071811711f03418803c5140c140c44034014400c0190aa0a001c200043c0d8034106401900d0202d10a0400782415101350341000a502c8000b2902400141405503007950b00d00c040008048055600c14201031003503407800080c2000b403e03c803074000b00c49808400d01100c6501401115000300518025041450717414000504c2c03800f005101a200f20841e00100b0425401980c580020345110f07650340c0114541810b0041c2d0303d42c01842882c00180c50100001e0311900041444c010420903681d50039601c1d442e41d02000307076a07400604a525040c00c0c0b40104030002c0c9012100f030f00200c46003136001c10310b985000d0803d410004c0080000d4081d411009900313403824075807650740741e101802d818040e100740b03400b0004a031140650100b001c0038a2406034003040381071700001c0407420f0305040011628214048 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 16606769 1250 16605519 16605521
    0x91906030b090607030501150e0310020c011d01020301060507020d1109090d110c0907030902060f070303050414030921010902030f01020c010c0f1202030703110712030c1b020d0c05030703060203010513 88
    0xd101c0c04008d00070109040355003034400c00100450b50002012680e00c43c41a0380c4642c00c03a80158286c0d1040d83d551202010404a101e089110f4090260021415585012005042d41c461244000e11580a0103920000c02c0070403080d91080c04409002c800940c500400956519090000b035400400c850014220716103000184283c01100c014089080544465400342d01511916604130391000092202c030602c8030509000d42255070003542d020806080c6801c0858882c4036056400c886900f0030011021551a550000131031001079a5102c00d4140c036000c50f044c01401d107900d00035410f002f03e04000da81c0b070805402514031060310100801404445c1c03002039800700d240200380000310384140303201f91725100d5030b602955020100d0705010a402c0d2140d2009081c2e0390000800f00d80243c190089619465418410148465120f04042124003200d140300c42c4400c200d15002803003606208400d804000e000403001005280c081c4c00c90741c4c040e8032850444040d41090040d94007130151807450044101207 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 16608019 1250 16606769 16606771
    0x10905100e070506090406150504050109050405010312110f030a0806040605090108070b07080912010c080c09060405090405010b040c05030405010b1503040602090a180618090503030105091906030b0906070305 91
    0x2440c0700034442c40d0310785400c1c0a0b0f241c0003852150340c030903a183d00000d00851030040f003c150306c66598825a807242804005031500e03005070000c50099142c200140300040e20341500030510305050403e0125003901e2038096282c9030641285410034040844c032184c000741c02c040c903036004031800c9405026551b2142c00b8458240004d11945c038065100d0700e810000000004000c0c180c0c5409540c25600e071400d0580403d10b08400c150340801560b64900c034082d004e550001c01290800f1840303d80d645400354a200141c02c0f0300a0b4001e00d4440c1031b08202007010041c003584900c040b85000b51090002c03c40810020300150000c41d4196540d50800721118114030b014900c030342c07a4103600d101c03081c11502e6545074640250407071044a90401d41d01d440200d8601042a0544411401004007151a904005481e00a41c0e80d084c44a94602d0420440c40009040030064905540058402c20300540d01c2e0022690040103c0b400000414504a40401885480702f072292254080c0011102c854030f60758812012144 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 16609269 1250 16608019 16608041
    0xe0102090904030f051204110102010515151305031002030103020a080309010c060b0103090c08030d060b030112030305040206040b0d02040501030e032809030b09031801020312010303180306090501090510 89
    0x1010380010b400a8010520341100742e0051400034100383d8000381c00c15005000f994140e40c807071403003000f05400c4c1d0703424014243c1c052516400c1e00804a00c11011a246400c1c4600c020208000400c0282d511181c1c3c00c0b0300e000800c001400c960444003151200c400940c02800f0990249180b44030214000da00041124646141030b52031295400d01500c4100082c40411451410952242881c07408200307200d081c1d8000d0801100a0b6640e4a040281d0904075480303a07010360700034442440100b09104c0640001c000b80c40d01418007181542c4d40c2c1c07000541a210f40d03001454005408925000701d41d1181c0c0c0038006448080e01d040007004c2c1a040c6140e900d000c0d038840c02c0600e86030314a60622007458803520748050241403c218642c6900e83c2d41d0500030600031103e50001c0c0d4070124001c100f0544640207070002c0e40d0300f0b001441c40c0040b00d00350303803600f09014040501030180012001140c1e60b9454804030086070400340421411380d052810601070401d0b01016103203403103040d000100c2c1c010548184d001c0d41d6 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 16610519 1250 16609269 16609279
    0x3040609050105030a02040b0c0f010606020a17030403140301150e060f03190b040e01090506070804030504170a0f0305090906010e0303070f0f051e16060f0e040603051009060e010209 80
    0x580707020011641c6910050034109060303001d02000820a40650140c4000240d05020b02042814509590308441040d8410021980440f0546000c5480103034080b80221700d409845543e669030b818103680403518001c00e420418400000004c1410f000b10300140f800002e030340c0350910b44038814200001c0f4002d201c006050400200f0100d40c01d5250040b0031501100c2c00d440c0415070b02110030000303040301c0c440400940580d44520048003000010301030241d00440c6818030300c881d400d154400a1081c0540e010741c0d4001e200c034001440c45648100301c1e0340072165011002e000315500300d140003412504600f40b03160042078000045820740d805440c207112464400340046040103440d445510380c40300300d0502960f0204103c881e071008540c013805048002c1c3c0e035010001c0c543d04008003405191043c032400c204426a000c400a00c29540e1040c0c5003540401245403841c00010383d4800600103260950000b081d5115001c40607522070300a0304906e140718080c01d010400c05040d642114207038401c51301e06507404 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 16611769 1250 16610519 16610537
    0x607050315040f06180b0301060303140a0215010b0c060a06180f02040911071a040803040201030c02031303060e010606020106030f030804260711060a2f0102030f04050d02030406 78
    0x341c140400d204445210092000c03a01071a041041811207800d03400214403a0042e0005460655250041c00b409000c15002009064030b540c0f401007a04240c0310070380c04049000034220310502d108010152840310460003e140c15652808000d6407940141602d0081d4081c0d080094003200c00ca01c101c008039002c80c040031451851809a0704000c0800b031a8004045609110101710103e2500c501c120300c10549044076500d04041c18105240d03690408084110030b80c00b020400011590000e803500300741d081c01c000c24100007080060f811070040e41490f4445401c00c00000051003090b8000c100040010b400800445443d640b0407401d03a085804041d007145500c1c01008006482041e03e41e5025000e4901c03c110703800011540c1440c00703003e075803400342c480b8007140503c01d200512480c03c810400c211003c514128003004007801e50440c4400c0c2d05241564080c81d28070414004000c00008400d0744000c66903403404910508040740c003070324152424450b40b00c00d112414000400ca4050f41e17420746529001c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 16613019 1250 16611769 16611781
    0x2030a2a140d06110f030907050103050603030a05090f01030b03010207030305010303081003020105040308180a08060a0b0d02030c01080612240f011d04050106050406060305150402031009050c09090118050906070503 94
    0xa8050134040514161080101101040c0c51101641c00b5500c06000791030342900d843c00042c183d4001a000520070b800401c42c0c800340341e80000032a07800c54820b440c440d02c90800741c1d0044c1c00800070f0035021605540005841d80400d9490b911942c1680c0c8070703840d850320b207480c0da11000002d1299400028049041000140042100c0305c010b07011644950681a440b01010408034403d02c07141d5001a00390360154051100c00c400900400e0a105419514081e241c400e07a000030740d0310b60b200760b00c9a06100e010f1000c54a251280c00010503000098821600c11507076150580518031003141d45004800c00310000705921034a2018240d04a45030b001d03107181c501540e030b600b039480494041d00480fa02c0d96120800145030711940102c900900c0d83c0d8400080c185815010410700030b04800419106920400420000c0e050510004003034440c0c0c280c0c001901d070b50300c0c0300d26481880b48030981c0343c0c80b40021000103805183d0040c9001200340d018000d00840d290144150381c1c41500b6103a040104400740000380d2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 16614269 1250 16613019 16613021
    0x606010c110a050d0b0405070602060c0f0c010906020f040914090307120908060f060103050703060303050f0f0c1c1202070201080f2a210c040303050702030a2a140d06 73
    0x208008002c00088071a595400081d00c030b240c5015049502e04820385c00c200a00105014507802420140050a01c503c0c14180721820ba100d208143c500d02c10f404100d00182082c02d5100c00c000c0d6a116004555402d44900d46c6401501b15100d130524050421925110505403640601e008141090065080c420141c1d07407806100e03a400c0029082001001340000c1042c4e08000c2d440c01015010341e04182803c3c000001026104020002e100f8541400004c20000e9031101c110b07500c080d84510195252540c02980c42142d00c282c0c440c4294038400e44a0040302d04071100004000401140c8460200e00703280f0742036500341d0090100c040d001c03d51140004500c1784c00800d6240d400400d1400c0745016503004400d00e10708015503030031039421100c00300f20070a002c052945142c1e18820390b80c4ea40d00c0c1c1490003d04480c01032250340402410480e0200c0d0040c02c40d1002c10046003256400034420041c44403a0054400c9001c1c8160102480c42000c14002107030100c0034090040c00c0c002911107107414040e52070300b034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 16615519 1250 16614269 16614293
    0xa0b0301050d14060a0504020f06030f04030e030309041506090f0e040602090103140703050402010206090109050c060708040302130218060301030f12180303020c03060703050601021903090e0f180606010c 89
    0x42c84100750030059200f40320080c44040d1080052010000b280c2c246401448035444404035100d006540410038805011705803e10541c3c41a411f00d081028bc0346d40001090035405081c0c0d21540041c1800d086192220407010008142c0d20140d0b1a02500c958402e4040d4440c04280f107401040040b060210f00070800c3d0340c0082800c85e00c1814040388043d03a4000c15004140100c0c0c4500000c0c0d900c03403e00003150f034148100c0341c0000150f40244641d10384d030f460745030300c554540e00300c0c81c45400001680381c2002540020303140156002420841c03411080c07010080a0b521900c4c03000207403581d0701400c412600c0c1c440c1c2a24180c90308030f0100ca00c12003650741c030315070300210081085c418040c09240a0061703110780c0700c008000d07510036406821280c7c500c01c00e0526042c4003502c40020f0501301004c0050301d90380060305c02e21001c0e10601d0042140d9aa04040e14010f4050b00080b44c508624000c01c6807408005807132038050410b00591780300301908c5280301a211801a41d902d0300051040d241d03030b004143e24118071 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 16616769 1250 16615519 16615523
    0x1a040213090c0e0109090c06050f0406080402030703020d0b0108120703050a031a100c0b0f04030c020105030a06080304090e0d02070f06230a020f06010e0402011e110706050d0b0a0b0301050d 83
    0x940c1c082516210982d024a5090f800504002c0e152800e9401f0810a40007010007002d1a08215007003145154070702e0801d0203240120805c012140300060190342e0100b160070011a0003500301040403000e4140602020400d00038007515201e0b9036124036035103004c081190341d000d8266580c02e0600640c181c08801802c85035801980d0682c1040608245546141140340004e000352a5030b2110400b0b0324041e540440010f000c1202d01d07844404000202e9013080740f8461007642480c00540e2581c404040000804040d044100544804140030901414a5025115540c038690458031a018601c0c8100da503002940110150090001001c10155000d40305151400c030b1303e0107036004100080008012a900610708c80c0c3d00503440b069050f87d0543c420301c43d09002d0003107041014950302d01900086d0480580254440203c0342d03040303c9201c25481000c0e00010002c04200381d0301801d503034460060143d080000b074075120030b14006900d001850282d0442044602280100341940e10303007010000e68181c24681 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 16618019 1250 16616769 16616783
    0x3150601020c100201020904060902090307032603150a080a03090b0a020703050f03040e0105060705060402060d0204050d12080702030a020703080a1103030106030207050601050a060e040e120706091a04021309 91
    0x14450803030f50381c280010f001142c3c0d9070005844a40c182c0c2001309681319644000005881007285c51103e85020428405032034010400002d002030700300c0040c07525040b5038414100d0f04808414481d01e5141028010107900c01222068840c50700ca0080d03d450314841030000b0301044d10100100302d06496480640106102c80c0150707036040b5640e4440604144008402c0c002523000000c1c1482103d115900d0f1501501c000c3e681030b82030800303d5803078a50f258070182020707208000203e0039205428807070b0100c5000c0d0002901c1503280c8121483d001d02c840c84e10f01c03110070124409100003a0000e2000050310b41c044806d40c01011802e02e580c0b0750801652207074422034204503884082041021081000314001c11003680c1c01a9103103280c0c1800b500384441a0032580c802c03000c038103007000020b80c007405100840d24212400505104d40f082c1300707403a0561410564020000200b0030380d06000da540d104452031402048a0454100322100c2004148001c0301e0095004c01c20124800d01c0e13243c0c0c0d50120440a1007903007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 16619269 1250 16618019 16618033
    0x303191a0d02030705040f0f06060906050d2403060207030e0108091e03070c0803030118110409020c0708010e010c08060301050c04060507030302090901030c031a04080405040f0603021008060117060315060102 91
    0x1b040955001c1d050100101d81c589464006d101000e10540c0700400c024501860401e040c1340f00203040e4450351003d9200940c0712020700540c11045000402400307040c0c100c070386490340d580c64080040d4100d6401940030420341c000001255004c0e91080e885a20a00082c004100d200c000d4526076080341c4091002030712040c4044070010341c0c0d00f83c01c01c0103010190002c40e01d9625001200e020440d005000315074241c202911100036540c40c00a076030a4078002e000c0940c44103010701d9900d00c2e058455000d452250b08103400c001210728194850507007000a50f54045107652802c052500f030b50011f94030407864080c2040b080019070311510280ca40c80e4881d01d0050702d8056400000341410f402a0410b5480300c02080381041009940c84800703c200b15155050480c40c5490f803514a02c900943c480e550083d501c408501c4043d0000c0e9010301c1c00f866005150f01103d000080c0002c000581c1110420301150308624201048008024100c2c42504028010003142c024160b1080802c3d202900345819885102 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 16620519 1250 16619269 16619279
    0x61101020903010e06090709140f04020102030c061f05030712080702010923100206150111100603080c0d020304080a0213111215010504030302120a051201080303191a0d020307 77
    0x3016460313036424210014500b81c00c262080e282880d0041e1301c41080c030351420b8040b20529070000000303548500401c0104041c4da5840c001030781148180c41042905020b4402009600c1c0c04510054003403880e0f0501c01c085041d114008d056803400300e8029080105a040c10550004894400805c006031040c500111403958816005a01100243c2009a00c1a05407117001c0e4505242c00107510150321403005000c1403c110007005c14140f4000042d504100d41e200d2030302d9104d4070401501540d50003400c000c0051a5590a01c103109402c000341201c0580103821481c41c07000d1001080e1810b6030026405810101c400d6400c1000c0d101e010054070000c6500c5503100c0f1203000082c40a45114003c070455100c151510780a10082c4481c14103009050103401c1c042400480d030300050084110964200d400d55604400b070060b03400d0300420110210b0900040d0012400b44d8001c0003560041801c80040740700d10005041c0d801c10383d1340f903508400c00b6031920b1200b06079030700e400f51400d6801c44c005005c0da40020380361 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 16621769 1250 16620519 16620521
    0x2040f0e030a0206090114130f0203010e030408010e01060803090102120d0f021801090504060f06050705160308040807050409020108040f060e01020309010603170a140a03060b0a08010603230106110102090301 91
    0x612614800758019101708101d800081c020760104860b107030030103200d80c035120210742102c000540340036020f41c0c410314245045440c2503001c4154200c0260840b6191a0ba030203405002c0d0421a0000b01e8a5080c1100040c00b0040007064602442d81600540280003d480a4490742d0300801100342240352a0205203a6800c0588004c00702801c0403800d8205110000340003400781c20302a480b0f64021480c007002080400c40d60f611400c1a1019464a556616500c1c10a140b90130f05071b01c0c20780c0500403290320000070050b01000074000c4891103020759100e19600ea08000c112509010080d000c202c00d040003900081424608140003031090f40300040c00340b0020010390898104940e00c441e2603646000a1060042a041c03a50b40c200002d05c0c1c40c2e280c070900740700042400003801c0000758058404110001d140780a03400081c050041040c0c00c0d5152900380d0401042041c2c203205040200b444d0800c035811030b81c03c20122040415000c1900c1c0d00c03991804c8401c999500542011410380d550038014a04140c3d42 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 16623019 1250 16621769 16621777
    0x61003140a0504020f0a031112030702040c020c030d02010606050403080f0c150603120403350712030b0d0201140a02070915060f02060702060a05040c15091a0a0c02040f0e03 76
    0x2103030000090520f064814480c0002c021703004280314500c003c9007000001c0041009500e038000a03104c1c80088a13040e10002c0c070398003d40500075072203030820085100c03540e0b0000d1030f556031a40882c202d4041c4602c44100341c0c00c0790014054007000030f40802061011401800c0102030010301030807111301d0041214907480c288600120494441c2001c0000d204461030308100417001860420082440c0c146550f60388900e0030513880d044100c4588403250a0f450528071882030380908180245142d03a02d01750300d4030160300524070569101091a2a4000007141020202030801c030f54103071224019401c43c500401d065400801c800002c600c2008000306280903280211850814030b84040400d02d42041f40280c406d0709100214002c652128041180e840c1e0300140d2185c2100c0700250000700c07900c540c04c0500340c40545821810240d400c0d10030a100c0036a22050305802ca5050202d55800c015000400703603100d201e0b002100c2c000803405610103001d0300e40f42d40032201c408114100042c5c40c1100c0310a650440d04 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 16624269 1250 16623019 16623031
    0x106140d0f0c020c0f0616020a030203060406050601080703140612031905070b01081513020d0f0f060c050903070b03090c03070f06020105060105030103080d0f1113061b050606100314 80
    0x520740c501e0390940b036010030052074101d10881e4880c01c000d41a0002c00c10a020300104448140649800c1d841507450700000b420103160013400350f40903850142002c0340540016100a40058101d1700000c441502ca44a0741c50b003080d00c900c0350790850b182e01d0f040060b201d51603500030516000403c0b0395221140d01c040c0c2e03c0000680e0382c440710f454680600f4400300c01e03801648021070070f41140d01d03244001291904520351010401c10962001096800822000d81d49814020301c00042c40400701c05000b0311070220300b602c500c80d03101070008a078407940c121403d001c0c0401d40703030b01640040018003600311480d002d541e111103160120388804a40c240041d00c3c0c11078a502c001072442c58020244002982805840c1d07004000b070030300601c0d65240d84e41d243e507180b00d117524905a1540e22480030150400641042c403805d031040784d00f545c036044420340c6450485907034480e03800032550409a41d07581f40c041d40510070880b50000003600c41c81da50b01c8240305880c103031255100c00709940e4409a224021000001a024107 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 16625519 1250 16624269 16624271
    0x30f060611060f060a05060a020a02030d0503010e070309030228052401080c0307051e0a030b01180902060a0804080f1306030c03090203060c0d020405090a0f1506080106140d0f 77
    0x8161001e01d801c081c0c0203001c4030114490041049159140c0100a408481050f9141d42c3c2c1c0340c0362103d089081030410a002545405050036411034994448003640c10307254503440240f0030340c44a19041d4125032a42e4001405030700844000c404100b0244490401c000c041890244505090b6803003508001c01d2290050102d507001c905a03c0d007041ca0030500f03000d4060540242428a51400040d559035628800c0a00c00d01c01a40c030400d103151a00240034641101910b03c0030801e860703141014000c0c0e02401904213250208119900740d001600030800340c160041e207050318249030040c08440441c4001e00c15901054200314243c454505070005041002101d40100b840c14103000e002801d0781c40110380c08041500380051103000d0b950100d0306603000348000000564440c1c807a0341b900301034050b0780c0c0050f81c0281d1040030050606503682107094548441b0404001c0802c0c00311040d140c2c1d28050040a002030807080062207070500640c0c50100100170051000d01708000010711009580360150380e07010b11 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 16626769 1250 16625519 16625537
    0x3070b15010908100f020d09110112090201050702090601050c0f1005010506030403050307080603190c15090b040308031e070c15021c0b0a030501050403020303040b06040921030f0606 80
    0x10300d105900310454200910702407061070f00c1d041d501990b51204000c00c0780c03025034030a07126000120590444019503081c0741305000010040c2005206113600c0e655a50104180907407849521245204500e05160705840d00d5090002640030f0100d94100100f019050146c10052950079560800840d0803d511503402024112503070480c08080c0c0e001070340860300a80f010320501c130000780c010301620762180d468580045c5907038800000034a003003208150701c1300480803880340109104030800b044040d20000281d01c0c01751021010200c4101d0041d1280e600c034004144000d00010f40d0303507402103401c044080301d00c4004c03c0b89411840c10400b015030f0204007081c000c0101108000000520201c904c0010004500f480e00c00507500400d240d88441c10341c806903986071162001d554114050018540000017000f080c603003441d02030358039402520709440f80c070071880008505141c075018828641d5813000104801d240950009407021001a4040e03060549503110110000c01900c928130061001d03646603200 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 16628019 1250 16626769 16626781
    0x603010f0f0e01030807020d0203010603020910080c0303030106020a03080a0f1b11010e0d0309030c050f030a0908011e020f09090f180123040822030201030f290a050303070b 76
    0x80710035650302c1041400307100030041010891060640b8441501075549600212407032002900404031038100030f502c046040c0500031b00f5104988480d081e1400401160107040c84101059680d000911400d001641701502c03000002c1e00c00e20760b89402483d4a08040f5280900c8003032001601c000369622112484803140418603207078488200c1040404c9075008001c0c1101100310680c540c2050304915007816241c004030410144103a01102802d60810151052030041c641040c0c0c40e984100000c500052000b4400705030b94030b06201d445070203000a61506032a0b000a010381d401394000116441c6260b20910a030743d510b80b5040340703440c80f40e15801003074540303464085562210340e00710740c00080381c2d613243c1415008000000010185454654521908599624944899070b441002c41d10501003081d50308491180002c0303c0355a09492003603d040c040088400703505021103421036401c0d043d03c03c00d000d500c01c00d80c0880390b1070318034288094414801142c0303403000700e861030f48039820031103950281c0800c102e8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 16629269 1250 16628019 16628039
    0x102070809010e01030b150a02120c1014010b07151d0f120702090f040f020d060e06130b06040504030302041a031f030201120c020106051203070506010807270603020603010f 76
    0x41c00510908081083c0106d10303000c100303210040044100044800030310448218004c01245441c5d40049145554800b00402201e44031100c6592002c0c00c50b04040030701010f00d040c90204c0b4103841290348483d040141d603481e41f0600c9110b409504e200141e5411a40d40c02d07804000c0320940910062004140c04100403010a18044c010300c0c15038540c03041031042034016598010002d4101d0f402c24802c0441d901d40c1d0602c5540701d035103100700035404000c001e601e204110154001020030071707000090b900f4a44d103450740541000095080140240c41640000703000d440c0c40d91045421a00a00e0010b060a4480f40b01c2200d000001281407203811000c010400880812282c0013036020300d5100040c0c2071855580043d18003001e906800c40c10589070044074a64901c00d610001c0100b030024a80da03404e070130090b41da50305c0707600c800002c4d18640500b0f00081500040003a81508495010a46200c5c14101c08080c0c00f0080c0400d140082c825114480080540c1d100c1e4060b5020b092407407558800300d464441591 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 16630519 1250 16629269 16629287
    0xf0807020c010903020f0f0405040b040501050601021f090f0803010611070801020a0915140a0302070b061f140c120307020d0e0a0306020706020d0c030507030b0406120204021b010207080901 83
    0x80840d031000440d084a0b0341d01400346404c480d8180c60f0328006e44001c1c400910b5560440c813000c0d40207450032003040103020410080600480c00f50000b0011912084e0049846030003e1b0b00c0c1485441d41d00c1032200d17200100780c0c030241e2140c0c0170f081c110640c014680c1d13400c0c20b254401c0c0d00c110b000a2182c900003000081c1803100d00001c018072002103290886440000c0c04009092280c1c0362200402c40000c08024051280d03490705985550039142d90b41d402c0c4001900940000710151081800a8009425810407800144403500010200340003041114002c49103d50072040800b4441805d100410400d40100b1a1320b00860844c40f21b90b13100c0c506014002c1c5005001c039464020070051005910942e195500304100f52600071502607a14021410000060b201d2a1518984249031110340d118540e4190311080c051308150790280f00c0264124200f00940300c0c82d0050b40c50012150f034103400103103401e81c000d1100e0b242e0140550000648048403508a80044d202502c208500040402083da8003041c00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 16631769 1250 16630519 16630531
    0x105070f020d0c05060411150409090303050705030405101a06040e012c150406080f060609150303090409020406030b0c0a030f020301060c12090513060504050105040902010212030a0605090103030f08 87
    0xf5035031654151074103030b43c0da1409800030b0400346041c0703002d00c0181c0f6900340c03180c2c140c107120202a5490b0354981080300286500502034001070b01d0325000c501c105115804590041d0b8100005101d610814400b00005085003c04080c0511f00c4400245150300d0f08030140000307001c0090010b940f9850070b550740b60044400c0f510410041100b01203e2540900c8811641e0000c024420101000300810b0103d002800240c01c61038141c480c0d1041d1904000c0000b41e018801d11042d941203216840b00300285402c205288c14090349070300244070302046420160301068020f40004e002040786540d07a180c0e010401d4058400207800100062907000568040c0074031380080032811811440d42d894840e000307100740b880c0b40d0000d000c90000e0040880c014490715400018020080c140850fa010503010100241881c0c81003500540c2001d00002c1d03140740c1231003030000081d0103030040e018890b87e00100512a81c0020400b4102a9036080041165103c00c00703094040c45c8682c40b00d07440c400b0700f81d00280407003200400d4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 16633019 1250 16631769 16631777
    0x103080d11091203130504020f1801090906030506070f020d02070302011803080f07050d0518010c0303060b040807170c030303010e0a1b030506031006030c050d1104020c030406090b09060301051c050105070f020d 92
    0x8043c0d00e29040c0781110f003c4080400e4115180055038012508cc800542c071243c4002d0900c00302100344040854030b18011443e645482e051500720120585e1640c1e50241e0010242e00003030f10810243d406280d00118020003109280071071502c2e955191030a40000000c1c110180c008568001008010410381d80440f202d403d006003054414074100c10084d6408400504105c801c0c505001018000e410103c0501100e0f851281c07101c0c0c41c1c2e03403035030b43c1d4400b0791107400385083c1080700b03010b09040e01040480c440400139014500e140c0c04c00d0400480c551019004200c01a52070643c40564141d1507424510020540d074017051500b41a01094036000c16000c0c6912250710b002001c1001404902c481000c69806960446075461181803a050502e03d84001941050000030881c1c1c0c941404401401603075841c1d159602c1076622000e071421035018028071a42c120204100501003468032080c10345001041c0e050402105d0041e681d42800d583c010380f400004204204400600f07660180900d0100c442d041c50 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 16634269 1250 16633019 16633027
    0x1080706140a030207050c03010c0e010f0816051b03070803010911030702071401020f01110306090f1308160203030703030f060510020606090402030f1c0212030103080d1109120313050402 82
    0x1c0c0841e1910440107500b00349540040c0b9842000024001c0203003600f0024020030194160105c09000340d041c4928083c0003d082049000106000708141801075500d0740307140640d1414100240c0d169407062402c0031511064010b070b2080b0300741c00c01c001d100180c418040b4135240d51404010a0986d4008a582c00301c4c04070610820001c0d41e40020b001c0d0444640c14012600c844664006030f05003681c0b070000c0d241d036508040c20080550398100095014003011741c2c108520742d4410180909003a400e4a0300140c50710f8a00c940c5000c6480f0102070b0020000c1c2c404480c0019440e40e002a28550201e02c0c00ca021a4969220b01200355081c0300d0700c0f0007000d0540b510386860b00e003e200207403200303002025984641c08034000f00e415510200444c240c0709181c01c2c02c646d80f64280d801491583d6840003041300051003040035910f43c4400c8042a01d0403254403444290602c030f0943c4040e0300ad456103403450741440f1000d04c0081030903078690b81442a10714010300036603502c20b801d204481140450350821401280108 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 16635519 1250 16634269 16634297
    0x7051618020c1f0204050d0b01080607020106030f0807020a0e0906060a0f0b0a11010b10050705070501030c081911030a020403020301050f1005062110060201140c0307030c0201021c0501080706 84
    0x8a010040019442000f0000c0200c2d080ca0308000d00032900480c1c2c00c42e60b171800310300410505d202014181c0d4a0101192200e41d07441c00c04900361480c50000800d080c1042410a0020300c0a0001d4450184000e210f0784410780c8509148010540844500307030b540c0c0c42042485060b0400241e8507028003400d20060030b240d414692804103e11440f400349080000101c0b0146840c4c000390b01c800c0300288010b00285054021520003480b68100000c180ca860040ca040000c0643c020f100d090040005c948441740c0382e5803072040c04103ca0303c040010f92901c0b51a880c070a4207507130008008510603c1d581c0001130302c1e0783c01e5006040c2150001000313001040740220a0000e00c00c1c05904400403605c080b41c26039a100721180e40d140300e1064030080c016640f520340b418000d4080010034100d060b5000c1360700803c10740c80032580381c950fa03401c29502411040700400200303506038482e40264800320f070303980005842c000d05650b9082606074452480c40700c480d82d840050028440070302451005240624054200072988 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 16636769 1250 16635519 16635523
    0x40210020d050a0c020f060a0e1c0201020714040e0a0b0709140603010b0901021f0209100f0c0201030b01020c130606021501061704020409080304050f0705060f03040f02010507051618020c 82
    0xf5880141400b40000a071000c666030a1440c6403000406444152985d10f0108050181c10001440602c541620760040744041010308258900c030383c0507802003d46c1c5140c44060300e009110100400d400c10348409160420850810809820070312a10003418940b4281100800c248070703c2e08040c5503006400980030007540d40740141c0b4191a00201d01c207995010720001130746806c00c0780c0c00300c0c40030501c102c500c56480c2d8000e601811003036005079000c05030020240421105000000f0074030001c43c2280c0221070155104c1d5109903403911043c01101c040ca800803001811444807424102c1146840c0c01007441141da042c8504c012080018848407640c1d418483c0261002401d2402c0389041c4458500007425540c03507406c60780c80c5a0300320822035a00d0906060032610b5500404841285104900c0c00140500f001400c46c0c403064902c584442c1561103d584626100d0030360314061b0704002c024040311020450512203400c0400305d2000101c0039a00e05100307040444061011481014410301401c0000030f40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 16638019 1250 16636769 16636777
    0xc02010e011b0b0601090315050709060509010215040204020f1c0e070602030d0e03040b040b0a0e0a1d0c0f1606060e01050a0312110708010204030204110301080c010c0305090d0605040210020d05 85
    0x2100801400f0340d520100100c410382c0956101030500d40d032281c0400010607590703110034090715080e580c00c811640c641d042926940304d0030080f240141e00c030000580e0b51031980d080c81504203100901c00b500c2e00c8207850880101350401c1294141c4003401d03120070b03001c0405600c0755011041603007000c4c0c202245494006034481c0105070070104960303201c5101501440c0240b0454028208501d13580d1b40740d0f40c8031400300045400c02d01a000210b0107094210925240505940045030750310840c0340d8805081d01c0354140c0300c00000c0d142c031000d08414071008441d02240800340c136031017400d240c4c10346041c1600d040030425554264005200d076005000181b240392200240380e001d9a401c2200c0821001e070006040303881007a690b0b0441442d025280003c80c07040f9041d0003d100701d078000c450902c400d15405140842511007031090318880d9011031940309195010b0b50715001d02e14007900f8035030304000c0004041040300040440c101c80301c0b0703642d901300411407a1507988010800f00e140b009003078001d44448094400d00c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 16639269 1250 16638019 16638023
    0xa0c09081605100c0c060804140606060a050f040905040b0f071106070c050f060f010906060801080a030e130501080d1202070201080411031014070807050f0d020708070506070c02010e011b 82
    0x10f0f400405094160255840700fa03100c3d40300c00380b0185140d45d4140100300f000142d40c2140c0c041c0366a4080614020005152030007148010411494150000d40c1600c482d4080c1c0c01c262010001807000040443c103611895220714003030950080f8500d0580d80024540c10002c1c511800e02c40054045200b4840028580758402124203292030828070314201070b80b034401100903c0855110700c80802035044801e054150482d4100318043c40350580707440b0b054540c50000d020f8480b29600504002c8042442258a0500007002401081c100d4441c4204201514400d0300046100d50205056090481e40302e55545050008000c085050441c5980003c040f848042c10151065500b00d046d02c640303690500c004010a01034500811070010036020322085014100e0380c80e000700d000040001c8405020b00c0440300b000c00c203580c0d52303881d041058170b541c4000c3d08001000d68085600380465030001e4000c016045c003d440d01d8030b1b1071313a61340481d2000601d0114640d176843d041200032608006100d001c1201c200320f442d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 16640519 1250 16639269 16639279
    0x309090902120a140105070e0303090622030501020a08010501051602120102040909050a050c010804032102040306020c03070209010515040e0408090303040617010e0c0307120b03060a0c09081605 85
    0x141490000a911018502d0071801a000c0c1c030400400704500d43c41c181c600c00c101c600c0248400c0c0d880b80000d0311112651021030350503804c10014400340380b600100824100c0003402c1030540081400036092800e80e103642003100c0383ea5000454900480d0800310301ea00605091801900e814080c68154901c030381b110b0002401840c000d160141800804c1d01900d001e800c203100200200a00c60030115a03541c03c00034241d07100c0c051507910b9541c55101c2e080481c8074035099200d041c04800d41120313406e801000c42c045507805550038070010000072580d0004100c40d1540e03c0041d51100103e004004004c03d040c2d0009100d07000041d542544940d545e000d6404441001c05886007543c0d460078407004500c03412902582c140000600030440540041c80b18216181c0d10b400f800a907a211040d502503030b0025127840451400074000030300c0036031113a000b00d444016800b401142c5040c1f50303004a0301d48581592044541d036115242d05888a600038070082c02080030030700034003983c0c0c8000c1148200b20b040740a418011 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 16641769 1250 16640519 16640531
    0x61a0d0204020901020a120518101403070207030804090f0b030604051c020c06070606030c09020310090c020c10020304060e0a0f090908130e0402010809010b0108010e190f020d0e0604030909 83
    0x1340c0c000c3c01560031036600301e59810400c0b414407000510707a5126904d0000d0700c503001e10812845041100e41e514100138292120b00e20201c580211240a4200a0202c1c045100f425804400584a00058001000c01d02e0001c11035445035400e0900380d1b04d095036400c0c042c4d4410030811000c0761001540c1c2642d984003582041c24070070001c408908084100320b03616005000092048204200b82d4402801c0741d000e0101101c809442e80c039084141e10064400c1d410440e2101e40900602c14954803804043c0c0b4940101c0d0100762898002c42c0140d004550038401582000c078041000c0f03034000d0300700e900e00c9004580d50080b060512180943c11176031400341c950400d5803101881d0070003485000320340c001c40280c030f10007594a80d00c80c070941154004880890020f072080d00400d52004050051403d9240140c480803aa603090180c2400b0b4200c0040280c40d407084110b0b400402c1812030f22451854840030030000d80e0b980c900010283c15102c41c400100040e510040406c408240d1101803101568110740c008078075 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 16643019 1250 16641769 16641787
    0x6061e0c032015040f06150e0c03060a030b0a05010f050105090112050a0e160501021006080c0f01030b04090f1e0503030703110d0204060201050403030b0f030a0303050402030f0604050a061a0d020402 87
    0x38200e459031100b56a44616400d1006002c17028010080140c4601007c0c410900c00100300b03080f1032114441e041c07414180c20b0100e81e810807114040c6600c09405000d840c03e40b82e036130311011040d80041c1c4802c04615a224010f00c0980103921405026290a08216107080c0200c00000c215078003001070092019652408245410425088000140445800c070354141c0da8500e0805482409446668094480d41c04000c441c4191809207004450031440981440700c1e08006200404814405003410955a200c910110399224410300756100d0086502d0702252581e0700c3c020090300f040708601e500602c2000c260900041d4000103c0b036002a681c50080342e40554806c102416000f0794008803020f071300200300841c8841e815803000e8800c0f8000e66041c0022400d4a003401100e2840742c0b0104d8043e0015080c09010034003e801c10354100e07101404542c001f805c0092200d007051810749003264503411442411062140d01e004400000200a044040ba01d02800004080320f1490100a0180380c002c16800c0b8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 16644269 1250 16643019 16643023
    0x9061209010605030a030206070206060108010609030305070c050a08010b01080c0702030c01110304051e01020105100b18060f0301030c06110105010501020c0d03170108010e01060f0803030408090303070606061e0c0320 95
    0x3040f000d0101c0703000801a10b400380d210314044843c031006104105c005040382d071241e0b0815040382c000c7d48651050340e0a54908490303e5004143c1610018100c1c1000a0683c0740d508044d00184800340c00061342d100410300042880b20040c0c410074880200388110005644c0c041454069101d0900b85600880c180b0142c8505502491b40720355070001c5410b40005000d41000140000400264000c2055130349488a100f010003944c0035110aa150922140000d0700301e052040008000040c54181004c114003002215648260000c035986c1101000c1000b070141c100d559146a81d1030034000b4401581042c00007550368801101c0329100e45001f059200525010700701c070001b1050040c41440303d0b50b86640606010701041c1a64038415072034140002510388001003c4810f4030140c20186145464988800180e904503401d00307035040c0020091a03000886034070840e0700500c140c0e110310150003400303050089009400e14000c1d052007949c002210009a005000c0700141102c0c5428803603110345001c10034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 16645519 1250 16644269 16644281
    0x612010e04140d02030301150816030c03061206020405010e0a0b070605040215030a050105031c020615040b03060a0b1e030309040903030609150312050a0207061d0a0314060901020906120901 83
    0x9070340c1c3c0a400c20b40c858041c0d0120045040e181c0000c1001041441e56408544544017102d1700e425060f540300403c4580f40c4a40c022022221003464003090050320745080403141c0c451540102e41482d40000c0420041d40c00c843d08042c411000c41da4100414580aa10840781c4604180100b0303c95988000508550743c5030101c100041c10261401d032289002c801e0030f00144402e0040a01c244142c0891084c40754041e880f2101c1080b90b54041d00d0f49480c1c3c00402d4011151491881354400d840300204032450300e040200910070088907030041608500c1401b400120301000740380900742c1c1d41e00020070105440000031600901c1007640c000841c10682d00b0700b14000c0130030340c129200301c1c2d041003a07000402c403562114600350b900036074558009020108064403c2d00ca0924624050380140c038081140782e00a41c0000c07020b04400600c000700b0801c510004d0300c8128170303400803a020610429030718400c150400120303600142a81c000c500d41124080011018001c1442407148140c00d540020032080d402e4100d0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 16646769 1250 16645519 16645553
    0x3070311030d0e010f0609020307092102060a080f06060702090f0a0e060108030a030b060304030f0503070522170f191104020d2301030305030103021314090f07050612010e04 76
    0xc100f10a034140e0b605020b4188100d1120304682412000300351868580708803801381c006e90b1503800b205890680381140110361140389410300e9144001480140c0c03030f00c00041c054641181e4031610300e03140808400241000242606000745400d000180068441e000000c5d04003c0a00c5011010b6a41e2602a0054407004131089a03600074200005013002e00007004c1c081d902c07502d88090200043c05024070840307010803600600000c40d51100c52402c580241d0003560002d2003072604a142800f500c8003010410240645910440c614200420440410502c0c0522403403400014141c5c030b095502c2c210350b5480c010050f007039500c032818841c01c00300b10036503042440041d0003030819501c5142022804005040c0c081c0c44026241c4804007107162442c2c03412410381a45e5050711441c3c11139081d50280441541c6480096086c0f07a034406940421100001c182846200541e0040428801c0c904c001030400000358440f900400c02840a0310313000c000303030b104d843c191780c140707055142c00e82d0716400d2084c410340220000d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 16648019 1250 16646769 16646771
    0x5150d09060e030306030c0418060209060d09030207060f020607021c0c0f0f140601030b04030503040c03020d0c0f06031e0b030106031e0507050a050d02040902032d06100803070311030d 81
    0x503500b800030b01201070352240c00308800f5500c00c00040002e0005440002003d1038210004041c4800004d91a074060203642c000a07141c00c2c189000e6400c0c41e41110b40e0544150050783c4468410429654003900c03403811003d0a07c05042b50b810070707080103903540d000321480038010b80f813081e6040340301c521508c001c4040a0b000f0b030441c10082c5450400038500c509600341074482c0051006092501000010301a040300e138402c4240c4d0580e521911700711a0b43c3c0014208480d4440d1103003000025a031000c200b0030f116070040c2402c071400b926080030041c4d000d460fa400b060505061008034090340c0c69503002001d01d41042400800c4034001e00e000a030041c83c441e000140709148406604030145101501882c3c0f551080c4121002c10751100e080054404591088a0740010400014001030502e5001103000070b20180445405148010203141c4c0704003003662031481c48030001c0b409850502d040103000d420103000d1360001034280c1800f00154032481381c084094280041c000c40c4021201e01042180c52002c180b0b88 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 16649269 1250 16648019 16648031
    0xc01030905030c160e06030304050604030308040305090d0809090604051014040608030406020a120302030f04030c0609050d020a060501090e0d050703090e0a0e010b01020c0a120c080609010e061005150d0906 90
    0x1c80d803480d03504c2e03600440c4003640c200c00006880c1e080c00070494041e40d600400041c1400d1555030200d500401c0200210304008091000016541304c102c5010f2801d0700c65011691203035140000d01036604802000c4900c10303401c010900410003002c0c950b42c0c080d41e503400391800d4071842c6103000c80c0240101d42d112a01e24400090005081503010843c150414072408080c120104600401c8003a0300081d14403440d074403000004500002c3c012003e0004c25031045201182d004826180e26040544000c2102d015811200304007003008034912609001d4030303600c0c10400600a10240d5030f80c0c0d0384403400340384060000c0080c1100034140038002c0c10006054407084a04245000903c000140040b40354000c01507003882210204c560000c904100042c00c05090440b4041c41c0c40401c20300f000c1e5080b41502c14254101c0c1c0459549020300c92144a61002000031440c0c8a0782e882951a00c00c3c000d001d200341d012100d0b03082c0282ea40e0010802d6594180901090300e48030950004001044c9610b0300130f10040c40c081d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 16650519 1250 16649269 16649293
    0x52101150603061802030405120304050c03070305070f08030301030807080306010c0b070507060c031404020f010c05061014100e040504210c03030c050708090d0305070c03081215030c01030905030c 86
    0xe0007040913103105205643c10441c0480c00300741a03020680c4c0040c0507400c03a45901c441e2208107005142e205010307004842c4543c1015001c2400c00c080c540080d10160484001804442c90b01607510b0020100400110710303540c599125250240240c201c014840d000000220307001e60310a01c0030306000741d04450350414a04000305d001d40300d54004182160300d9400d08030309a407411300910800c100489007141e203075800d5549600300245900300305030840c1030044070000c000208104100007842080c0d600c190300121420300c4140030030702c00c25042035403040000c0326016050301d510040b1110034100564002c610b50b11a03150114854190248608100c1c00010f800c0c00c0060f40644144002400307924200b04a942920301201da038070454001030505801008220b03c6410314000815413140645041c2c0d042c00070075540c011041d0103a910981310000c000c107100081c2c0c0201300d0959040943d02218024001c440004a52202d40646d103860515649403043c1060110500031607050380201c00a58488074034107 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 16651769 1250 16650519 16650521
    0x2150406050703030c050a0c030e01030213140a080a0c03150605060f0703030e06090304030813080105090d03050a060e0f0603010603120201060801180b010b030a0e070f0e060a052101150603 83
    0x10b0b441900045d0510440306400ca016070308a50b44030019a6070819002d0141e141500c00d82302d50300801d81050313800c000d400a40160818101d02400a5510803400c2002e00000c0220101c00c0d90405915138008442c83c0c1c0014800d500c49d00100d9600855043c42c9880d00f400c0c881c002e1072140e000d56000400001c0f000141f21040707004242a6100780c404000078040e4040803551400216541030045d881004288042440c5401528840700c0c548441788085454019407030039281c055802d4466a81700445829800d6003600446a01c410040300c01c026076480d140403480701030400307480b21b10303140c2e5a640801d605840a400080203140c02110140004100110003402070941e03200b13403521946008040d1102d0003403002132420b0140c03c0503120b4116400c1c1450302069500c05000f4461081da1403800c402c000f04240820310081c16120b003140e105914001000340707001d4001380014403915401b40107102594641504003644142d002481c01d100310311a5500780100181203079240c3c01054a00006038503070f41 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 16653019 1250 16651769 16651777
    0x70506040e010302011832041113080102090604050f040207020d1103070803030c0a08090f0f0304060e03030c10020d1409010b04060503060709090b0609090708060901061103040e040215040605 84
    0x2c00c0c1d0b40c9076080e80d02c6e85500d604030f03845030140418010b0402c20200107900003447c50400030a8140d407030452a001940000c0445944551068070208003080c000b120b180320340843d00062074240d0007545824100b0300001d03440d10443c010f15210702c02c0c00301d030100691290f80c1a10720040c0d000d80b598140c50098140403040c0010841814880d1199003004a14074502000f52400b0311000842c19040120089040d03c0f80c6000030480c0c2080e02c1800740e44c0b503500b901080002d04040130640910b07a0f650900a0003011042d0b07149240380607901c10025010350000000c0d075503a50300c0c003103000107803100c0700000c009028120220840b61a0440312091103101c070b0040d0f00070000c200007140c0c10031056a594040c182c607071400701c036024003113015800c01300400011500030f141c590000074481b5107840c12070760014000620039a03c01000803040d03420010036040c09040540500b0f8181840640300c02d032001c41c15034a00c103a0007641c001d02c2000021900719200c1140c104418504421059151510b0703050040a42d04 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 16654269 1250 16653019 16653023
    0x2030703050103050c010f020c120a020a0b070507050f030c0108040c050d030203041e030201050403080309120304030c02090622150801020703050d060b090918160f0501080903040605030711070506040e0103 90
    0x2525a010305e1070b6002d0107078908151525000b40001040100070001040441d01c0d40300c0440c0204a10800103a80d1188410041d0035011344080c4c5510050508a10340789880e00281c0c000d00fa2424100034581e40041d001c80d03204000d181021595840c2d182c00792082d040b50b8410380e00880d6400c00c6404060b00403020340709980306d40094144410440040f80070301c1c45280b2010303011400030803061000c2045203001b1903000107108101c1e91103e100314045000b03a03204a9081d000604103405840c11440c00920654101c4011602c03041c000001410b1852850111076403501000d590740821800042c2c5440c02500a00303046000b1510b40000e41030190150344403100c81c040c220714100300441e8100703190b03040d60f001c6000504184d045e5a1201c040c00c3c10f00b1001c0d00301110900c10302c0029540024106242e1020300820094003a03501c2c902000503003040d8010b0849610340d0001e1006002082d4080140d940c0040c02c2e14200002c61101459181041042e400003500031a00040100340803007141c2036541203074 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 16655519 1250 16654269 16654273
    0xd0c03180605040302010c03050c0a0303021b0a050c0127090203010609080111070303050901152903150906120105010602010501170a02010207090f02040f0305060105100203070b0c0a120203070305010305 89
    0x550224010300300030305501442000c00c1d0280070900141d44a108101071143c441d0030014540041204941d10b0861805003c600003500014451000f107909101c941c28641c0104c01010352883d2555820340311441c450b0014100210158458840d080b04028040388060034448002080d40711041c07140694406d0003050085040b403a400107100070148161003038011100310041c01c00000da90100c1c0540b01c00340c8005101d6403150300b101186441c2d50b4080000301140c1d1a850381e6030030b004002007840c035080c60440d003c45005008122080705c820266056030841111328503825980c003800900450741802c1c007400c0a40ca0038001290b01d40c0c0540c0202c1c165200550342210b60242c07190215078030880200000d0043e08441c0c1c0030081e070402030b006090380c0611313031034054203254852104144d0780003140d100399003c0d48024010001800c10b400c80030505072240c40038500d4441280c40702c505100001d000d2441c0c411000803042c5140303109040c12911805440d00642d45e90030704080c010050b000c2070009844e18 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 16656769 1250 16655519 16655537
    0x31103010b010f0509010804030e0913060501060c23030403050610030605010f05010522080a030507020f0a0b030c0a021903021b01050408070e04080c0307030f03060e061309140d0c03 80
    0x150b001d18800b08507895590744d602d20340600007004441503013001c2d101f1024006901b445034001d580c0c14108920560191440410901c21814000184c0c1c60690068080c020716058010102c1e802c80b1604040f00c02903070311403201d208803c10b010b1031407040e580090001e024000500103039000c0c20780702c2003c40c2c3c0920700500c040d0f600c845c66580008006d10600c1c1c0865001c102c0c250002c12070001c0c040e503401044000521042c0d45110003800c1c01c0c0413100840004100091450443c41c100d103203407030207050680300d440b421403c00400da55540320190166003074040200d170401d8024030030001c1c40004031300d0580501049106142c042d65a0f01221441110200c000c0100c02503540700b01d00356421644800018080b50386091010003442602070415940901700700301c5e07605050000c100130401184650f071341c100804600c0c02d00138221070003500640c1d00742c40c8540901200c2e40ea960250304925107a80c00008981c009443c3c11001d8034824070b400003181c003511078070034a101d0300702014100c0315000ea00da600b06 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 16658019 1250 16656769 16656791
    0x702061e0c1b06030f0612030d0e150606091306091107020f040b010e040c09030807030810080a0c060503070c050703030509120102040302031207141006050103060504020c060703020d1503110301 85
    0x1900740401c030040c1c21007030910005c0e40c04644001c9098100001402080034001500c03009400e590008403803090040d20391180b040c10341410046016035220301500b2100c6400c2c100c000410600c91305a046100360009101c0707420b60b40b02a88a00010442490100161140c40d0103090803504600c0f81a4403c1081030740c03000d12410103005103140c2c0c0c1816526810b201c448141000014584003440004001c2001c40120000380c0d404000e0443c54040d4441d41c05514103034000c40702d0038406810849198000741c821800007006408118151582402c1c4203440f0765540302c0171600c0170001036000d4190700c1045000024141c02c10010b00581d4415502d4001d4100404c0000b402d0b0300c10b1b03100c001c1d00b56001402105144410170701501d0624840c4401d0862100d0300d2801c0c52414100804000c0a10740d50780c0304104541e050b105a6000f0001070300c0039414481140002e98848400070003410605d40c00082c8222211450381c0220700381c4540e14050b401140d26814100128200300c03150501941c070b01812508 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 16659269 1250 16658019 16658053
    0x10c120504020a0504020f07051219020d0203070809040b0d030903050601062604020402130905010e1006050901120e01060303080f09060c03150a03060504030809150702030405060702061e0c 83
    0x100c0745801400070603800c3c1c41c141c180402584906010030014806102c2d802c0000c10038490510181080d0300710750307200c400c41e561140b080d801001c2140155805181c0c0200602e40200a4070807550f044220183c540a500000c10f004e002c801108907408890034400004054106250308141c13400786084610680e280d24054581d041000700c81c2501d408440d4140d61181c00c0d074442070380c1c090300c094005400c1c00c0c03441450700504800354019180060701c0300700521003544201d000c10b60110003150154802450801c0150062183c2450356041000406500c41c03ca60150809000c00c51080c008021035a501d040040031a14240d500c0001460032001081c0034490014120380a84804640b513861920b40358898040b040402940580000f4070440000208189214141c40b9500940f03480c0058035024488a00300703504080d905d04142140410301000641c004292020b5034000e9502d40c0c1d40d4615030000640724003505901110503441d042c099100940709c0d80140c4805105035003107d04400784030200750 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 16660519 1250 16659269 16659271
    0x90412110303060109120503040b071a07020102070b07030c09051f03150311060a030908030a0507080601030e06011403070b03070c020a060908101e0603030302180103050919080f04030302010c1205 86
    0xc4c00500c8842c018440248040e241c143c1c82072190f42200e141c0b130380e02c0c80d40c14000c1d002070700b09640d1070fa40140d5842c01001c10174035203907120350148003c5162400c5a6201003843e8400303403c48042640d40c8542d070310f01c1406610000c0248c14010418074040f03001000994900e4200c1e07003094002400c2c9001c0c2c0300c00e050007011003802da036406050280301103a40400c1c4113841e00250000070415403511081030108400b20021402041910b13004aa64075002c58040c04828000c0e0500d030415180601280200f0404542c140c1901c5407031103800400803000300020300c0c0141c0c5030080b4054007400004d01988a40007001280c07024420740e544030700b280d501c0070142c44a036031500c01c907095030700500340321800b40b45240e00c91112036110040c040d28142e61240e80700115035a40d081103022a42c005120b40030103c03590b20509002c01c1c01d06c0c0c240010300d01400c40a440b40309401880c4092050301002c6020020301c141514035807e40340100a85660f6603041c020f000c2d05415101702d0206020141c600c02704a598000c1c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 16661769 1250 16660519 16660531
    0x160c0b0f1501090b07060e030d1a0f121002090d06020c0601050108100315020a050d050403080421020a0803070234090b030a030e0411040b070c08010b03120315090412110303 76
    0x6410000580c4a810241c000c2c2ca22102240c001040300014604a611800d105900902d100802402100d0300348000c40c25a2f088543c032a2914040c1600300e880001180f0f81c5400810a0250319415080c011401140807503200901650011a0a0110b448000ba0190403a603090761104850340380c11880340c4800c00980005001d4620700090300101500c5500142103d00b9186440c524042410440301e044803000d440803000170b07040714180000d03c01110310350004002d041e402d04404003486403000c5d5403103820b20302c0241080400b00015051900a101141441c0c40e0080b4655401001540c2900000c0e80c1ca15807283c01c1c00b80800c04240b19000740b00d400c4800c800a40107084140c0c0303e84060702c0c103d5200e100700350300984403400b510441c003484020f04000c0100c82c41085d00c80d59545000200841a03400001c001ea00d000d07007202a40c2d9000981001102180c04410764a85403044d0452074911403400e640c0d00318080d10144010004041000706440c8800c2d503031680c09da00c0d02040389449200660312 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 16663019 1250 16661769 16661789
    0x130902041b020a0b060a03020d140c10090302010c0f020a0308040305060705180108090111040f030302010e0309031e010b04090b040b060d0305040504021b0f0c031002040608160c0b0f150109 83
    0x7040040d070380c040744c2500104000d155841140d1350b6070000c1c000c04c490000c116030b41d050605400002e0030003007000c8203070003100310b038600c030441d04e4030000034000899807001078108403185000100b481808004c1488850300a02044480350b100e00744801c0c1a4800e01c421500340c424000050401c5d0b103d403094400c1c00443c11042aa003408030001182c502001030aa8070b9239559400c5603800f100048801000142142c41c1400e060528504000e801c4640c6010900724582081003c1589940c01081d45003c0d00c0080416007101000001d07403070b0040060044450f003051910000a046c014116102885203109010609656907450140000c0c00780840008010450510040c0f10601c2d041d0003504010340b400c03e980c0e8001010160091800c0f80c0030488070380035000b24111507043c1c1418000440303414a101019407600746442e900600303010006040d201c948540844d46100c0f640325042c8d00751201e03000030311840d0b1402c20360382900b600c0c103050302d0142021420805c000b14650203505414100c8440c820 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 16664269 1250 16663019 16663033
    0xb0c060a021c0b040e06010e060a05040218010f0507080c28050604020108060d06092102060c030a0902010c150501090501080106080604060c02150f070305060406080c0f0609130902041b02 82
    0x40d0b4003002d05901c4500710352040d00d030106050f110b103040080a0080098907030112003800e0001c28441e0f050810f4200c4c40c06940100602102c10b00b40041e000c0d4010801e19040b0045564203100703c0700c2e4021264000c010540018560117041400106d00968400300310800d010401c1d041c0741c00c0f00d514400d40b001829604100c001601541c002c2103019444000949010918031041da101021119507681c00c0701e00460440c0304008040c8889040c4082d1440303800200070a090502e02d404007800007c1240c94900d4072800501c0443e48a13142c2d000c40d0a40c0301ca00450780c0e5041240d410003401d400d00408450fa132400000140510050050340c04442c1200080c2c1140c1d1219183c2c0c03c041c0c8510314461080d0311900702d014490303a214000c1144180700030241503080c0e081c4150028140c80010b850b892089041c03903414050800c0100c0d5140020408640c1c014801d804103000c034031075000c1c00900c507038083e09030030a51096030314039040210f40030310848041140c09100550000002c412811140060380284 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 16665519 1250 16664269 16664317
    0x109090b0609070e040e06090d030b0117040206040902030a0e0d020d2f07030b180703120f030e01020a020106030b0604051b03041106030c0408010510060f0f12060b0c060a02 76
    0x165086070003c3d0b0610b09500b085900ba00400c0940302105000403003a40100d0800460902c00c3c0201d19400000d858140003a542d2600003c121001c507295201000c0c0d50a4007040455071060111801040080070a41d100d02d88001e00a00408207003007881107900815440b80520352011840d1241900c1903214509508440348100009211a4803201940c04d80700304c104041c0103013007040c00b000310b01c20b9081c524545003c2074900402540d010141c4802c0e8452041800044c0700b0300c5000c0d14501c0d0914080000200b010f501700e014040c907542081c029480021450207196044d00000e0036640aa02d0498044c2c07940c81c10321080320402c40b81254511074503d240c8001140302c80c01560400c0c040c9448403004030b43c603000581c0c6030340151480301038484005020803a5000038050190f002001b42030006240d8504040980b1002d050551081001000820a030b44d8500a0000303401c0d02031b842c0020001140ca0307240001950b071000014019170300c1601c3c00a2100c1080e8021100038100780a00c11842e03103480 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 16666769 1250 16665519 16665529
    0x210060308042c1513050601050403030e010c0b0403110f031206010302070c0806010b12060105031302060318060a020a020721021309020409060501030c1409060d05030c0f03040503060109090b06 85
    0xc40c1503906a50803c2507003640c0c1891018180307000c1c44448008541c840f841c0c10820134901e02c030040000076241080100580c682c0c103c000e4504a982509024900d58155001210381010040c4000e00c0e0044000501c81490b600400882074861440115402415261042a9603001d20040d040107803910000058095202c1c2e005841c500e485103900c81c1c660354403014102d04100c400d82000c100c1c01d4021a00c40100000c1000342c6400c182c4c00e081c490320390300384245101c20b002d00118020340034900000100340b9140a04001c03941100304403043e00d02038108080e105010b035200c6403850005100310307000031400c8019040c6e0840e43c0204100c036201414000d500b44a00d25202d4024641354642d140d0060300561290b0141340c150724071401c0c0000b620340c150f00c1d00701020b12150308100c917080d000c101c6141c92034032007510003074001c42c0459405121034081d20700390749584911640c0414038051400302502810303000010341f060701c4048003a10196a214803c8104880303410034054075600724080401d41d503043c9 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 16668019 1250 16666769 16666799
    0xf0905150c070806071e09050105070b1803040801020c07090b0603070c030e09010b1b010b01120e03040b07080403060e2d0c060a02031206040501050d0312020d050708040201021006030804 82
    0x202030291164240d56150031800d08000305c580d400807614181c506140500c10035991007500791181000d05070f0781e040030002170050242c1c40d0010a10a00000800c0c3c6c43e503203512540d03030b48818100407240d48036200c0c403959004c3d41164181d084c00f84604c001c0800c03041e02c039000700d6801c01e00140420b41140c0d1040b80403038082d00140c009905220200340d0040c0c0c1364841d0302d00c150103040e24081d03903075841990384102092080601c0d0a0758a1b6450004160360351baa0207860141a1206900d000c03400450721440f1900354450381e40410207816001403480204294140584212030082d8001c1001c101a0600d480e10780ca00903900ea0000c3e0080881d040d4182d840301c006c0c41c0035841d01c0f01180e024010403000314020394490f5641c1c6015030310100b86115400ca094104943c024001c0c0e40502145d45802c000c920b058902d8032006080c0220b04840003d03861990f41036450304a4032841c10700c800d0a0000380600800f000ba50180d00500800a60400002080c010442100c3c1d1180410b07182600e008204110030710 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 16669269 1250 16668019 16668037
    0x1404030c0c030f0c03030210150603090804080607090e0a020301080d1101150303031508030702060712270501080106020105060102070501081008011409060105010906050301060507020a240f090515 86
    0x340075400710108107008680c00341680325642c0043c4243c21400c0c060700d04140e140441c002282420400b0b1440213080c0c6881d07044401074100401c0202452820501500540e0402d4580e88603520401c94680c1d40640188115440c03440551081e481d40f0960350142e01c02401540c4040d40200101b21140b84581040941034416600000300e180300d0035406e202a4030207034410303070001c1d4071190f50898403403002c01544e00030100310000310315152140c2d010610074014044060000320b200400030348040c2c06112401030207807441440d200440c086025821107100745000b150700280391030001040d003a00510540e03004000580051010301d140c0b00c011940c0c0e1100500303480b41e107800c0e80c0d000103510710f003409444400d040d40d025100961802c00142450810141d00590401c41d040348100103094000342140e0550f4020b10f03041d40d07a503d103400404c9040510f03030710088090441e05032110484d92004603580c05412503640340c40c1c0d00c05500d141241c0215a0740145070f40329181c4c00d103001d00e0040440042ca135000c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 16670519 1250 16669269 16669283
    0x7180204080a051e0106030b040206070303020405030d050703020c09071b0201110307030905040b01050f030c13031502030901060b250614040b07080c040f090507020a02030d0f0e03011404030c 84
    0x640c85000303a906103a42400304680c0d55200b44d9042072020f40304a03c0585401801c4000c2044601d15102c0f082c034800f010b40083e010b45d0001800e1001c0c588660106c40240c01c01901701d905500c0c0d0b00f44001c1c00c81d03026090a07001405042c0c0101054070308000e00d80d0183c0a03503500c840f401ca0007004064014607140904031b05102c0f00004445c1103801c180060002c0e54061381b1440b003214900b5007480180c0d03054540441c1049810040c002d1500c81d105e0503a5044041c64820946410280008014162144e0000b500b0725010b0244803104010980086104020b44402406900d560340c054103582e0050800900d41500d14501e52051381080c03868401e1801e0040102140355090609241e214000564090702c2c040004410030039a1500f00000c2d54002c0c1425003014501850205038640303000755802000750554561002c02c010900c00c1020b24192500101a03030307415180d01602070201d0034902c80c00e501281c420303e24242e0700c0c03806100e8851400f1140180c0c4029640c2c0e41d600f12030356404034500311000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 16671769 1250 16670519 16670527
    0x1d07030f060305060106030f140403020624030304121101080705190c0b0109050105010207080a0c0509040305121005040e0c090601050a091d0105010305090f0a080903150c04030c080303040302071802 87
    0x30074070404c803860003404980c0303001500820a541e10341c2640c0200a18046d801e0114061000080d400115941c0c4440010700a0107008428200e4580403111101c00603458400801c001c524600b14008806a6074843c007601300f100001c0704019611a601140c61401281c01802183c0001012013400c0a0b9a65145010f041290303640d0741d00c4a0049080e000003000e036039220010f01003075030104602c038041c1c603403240180450103460351694107010482c0160360091030803c02140030980900203580400d480e9a0700e0503283c3c902030000780c0195000b0710545100d142807a20080e02400089440100035102514015071030341c90b02c005584542c0000b04e00401c00c00540710014540c0b000e1000800400722669041c0b140f54900340004003038460142030304071300d03804c100c0e10001e010314002100e03954540d22104141d11040701c43c001030300748a141420405200000401c10580e5001c00008000fa2445082005101900c60f448181c0d2804201c80050142e800ba04c010f1040784d005188558030465502405807038 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 16673019 1250 16671769 16671773
    0x9090e150a0902040e030f0f0702040b060a080601020606120703081303050d05040501030c03060e040b0901020d0213030b1305030409050c07140318190501050904060302030d0512011d07030f0603 85
    0x21800c4101c680405850762142075100b10702c2c0c980030701c480c1d009501000b1801e0a0324011045103900c20f00000079086030000844100f151101d80082c0d040000050030b070f50301c076201514007800004049034400d0050064200058051400b00c00c0c1d00c100a84207402020309a00316900d22200740d120b4411030b440000c07503503000000104200489403c0150b00d41e01c0b59116481d1000244c00d0301c03104888601854100703d418070602c84031320346050f44150000d44007112030300c0b0950348034020304c180c684148005000040c660f420100400074401103a2003010440402c1d99101d2080000c000100001403d40e0820041000910b0ba150041a0050030074030303030186440b4483d03131100000054042544031980010400000c0d00f50b0400f02c0030403003581520001d48614120b80c8207803125189018550521002064151558840d5031000014513805022103910b07900c204406016600540c000000d18494040086000c90710120140206442c50001d10016100d884041d80504881541d240c0710341c1d0f8070000000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 16674269 1250 16673019 16673053
    0xb1207060203070606050312090d030c150c090806151207081c0e01140418060b040602070528030206032d07110703020a0e1b04031a0609060109090e 65
    0x1041280c00856680f49a85484020380714154042c0380710f90000503101034500c2010003220b940900888680c039616a00d40703400d48070301d4802c4a01521650711380100494005241e401034400704502d80354004995610385c1250340d514811148001d0318a258101c8003460708110071600c0e400c0190401307450784c0c11f443c2c42d0100d103408000f40f05440ea0844d05076140180a4010118a01070f030001e1806401a10481040050900c5640305484050ba1603d008100340c2003140d000302c0140c0740d443c01055945a40b40c400965415481c016944100c0d02411059120303800d00201101c0c0d0403446074540030712860b40d020440701d43c200800c80d9102081602d410f801c1c840c00d0066800307a012403511a06140d0030410f20090009052000c00c07549544440f40c02d0001d0390300c1c030103480120b8280e580003001c65036921010724840190b61201c0e1807440000703d4088108202040c0c220281820048944500e50340c940401001080548007203020500200c42030294004980062200600040c100c40c01481d40b859446 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 16675519 1250 16674269 16674283
    0x3070302030f01060c05070e090a050a0605010609060507050c0d02010c15090308061203030c0d020f0f1806030f0f04080903070803070b0a02030115030b01090b030a09061506050901030b12 82
    0x40006940001040030b03484000c100749001d00014a800c001c00e210596800d0344ea0300303043c003446001914807030019103c07800c108000c450896100d02581d40c60003580c82d01d4409800c0a0103000c0c0842e002d040041081c034420004d03101c400d90801d0040c2242d04081040c000748600754082170341046040c14a04002c6010313103100c110111200d075800a007074121410002c000398806010188074800480b407108017410000141c80c0c001c182e080800742d881244032000c03002403140c2007040350340700c2012038075910303102c0700c0b402410840309103030a00030008400c01c0400c0210f200817141c1c40c4150403100c000c078048902100445d9806031003000c050349050300d40700000345418400d038841806644005104000c0103415001c590b00561162001d6085504001c0ca400211001c00c0e03c400402d9920001c01583d80e00c2503500344028140858415500d08052541c00060400802d050710030300e06100b411000c2c3c411020030781082ba6146d0352010301301084100111701034601000350903844860204902c0d12813005100390 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 16676769 1250 16675519 16675531
    0x4060b03060102010b03030307120b061201030c08061e070309030309080c0c0301110403050606060304030c0b070309120804020a0501030207020a09050c03040b100b040303031e06030303060f050901050a090e0f0303 93
    0x21616031410100080c2900c3d80c0354009030282d0028024014602c1e000710340d851480c1018400480c00103200c001082680c080c0340040fa02c40e243d070341c000009020f0410560402d42c0c0303080050782d0817550360411050445018100300c06407660184001841c01c1c0c425800380341800d03c24900450300701d0060300d031083c0d25009801c10740440e4020410700c1c501c504d824442c1008603141000c98a084c1407442e120300d134070744100400141c002d800000000d010035100b40f401c110256403002c4d48015504240000400603c146501104c0001c0e56044900700346001c0c8010522865000f4140c5048500381001140a5004020f007280c0198480b8404a07116440c0e0082d00d2149030015141610391800d0300341040360080281a1200402d1a60307410b00c081c0205108071402e50350541000700e900c8801604026441d03543c400036801c001d19120004c820181d060f0400402c44032802c0f19030b40415124070801014900030f01c1690f910001e030810412203c886074010040310b0313041c0802e803514826004212400c590040f501 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 16678019 1250 16676769 16676789
    0x1c05030406030b1806101412040b010b0309101d0a08030709050d080708031009090c0501030c05040f09090503040e01090605130e060406050603070b120a0b04051603020703030b0406 79
    0x309110003545482010030349030045801c100b2030071001008442c00100030302018060380c0e401502e1424a0f00403903d901c1c0d203400410603607030390310b224549003070042009941c00c8400035000000003038604020400d0380d00840190000e03004100002c2c096400510346242103070344180b1000d041c1500260103004000d15140503040303c0d9170300c2c0303000342006007610386641208d8070030107201070b451001c41e02400944081c140d101003401d42d00d4440060380309000e24140d1042c0b0042c3e08085801040194501c042c0048501c280c0b0701f4000e00d40c103d4003d0329240568055a5030a140c458010401b200712900172424090203042601d186c10345032208120003680036080101040d40350a0300300b01d02d0404400101d010700b90711004101181c0701e1500152a10800341000d00f54503121f90205043c1e0381c05008074001400006560b623580c207009031082c0c1000320120340b10a007040c90034910540c1c4c0d060501442d0300c82d00c1c40300200f03010301c15000c0f130580003134114007400e07010142d5441f152001d42d1918032030100034080d030040d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 16679269 1250 16678019 16678027
    0x4021c1a180a0305031504090c060509060d050a02180a05011403060a09060602061603050f040f061508010b03060906150918031b010b04110d09030c06090309030506070801030206070b061c0503 84
    0x20450302c3d0306c0d1180e25801107180140c43d4001ca0712000c504010750701146407495071072407140c0000e001c90255041e442c41c1035240109004e00b1800755030041440040c603541c10303150071002104000164445207e0b25020540348900c15014014600043d5803240004002c401e880340c50b0000002110f0541e00803d025900c01c805002260b48150445a588040352030140100d203040c03508000c8585002c1c100500b010782c541d042c0f0003006525040030b0b00d40c42800c0c42040144c2d0b07480780c0f4640a0308040700baa901038042d220202da241c3c000030400074840c00349417203829140440c030400e100f400d0344000d1211000000d48581600c22840034001800c074281d40d1000800101072000401d402c440b43c004469101e9403922006013019403006080d207008040c1c0850014080d03001c1c0c10242c1b041c40f0143ca0040001c4d141c82a81c00070944c1000c000c00c1a03034010740032111641e80d607040540d02c10100b80806540700070709002c1c6c040000e101c04091603002202400c000b0712070704500b040c4020a0007041c01200c60380c201107 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 16680519 1250 16679269 16679281
    0x20c06011205071502031b0f010f050a0b1801060e120d17010e0708010510050d02040b0304050c0a080303060402131e06030b030102070c12110607050604021c1a180a030503 75
    0x800015000f4940c0c1e18408580b9038502960360703c0742008905404541d0071901100050502861048081c418001c0c00104031900d460001800103c4035107a3303c0c0d1502c0e45610080c1170030311106200a40100500f0426400c0c14816195240c401100d5540070240002400f1100c0c001d0004400c80360b000d80b190f000003850a113400200f103005800c110f1452440504000110b6845038106044401c00d0380d80764840d041c0c22100b160248a42da2581c0c04039400080d000401c00c2032540110301c128042c000f070300d10043d503603020800b54114610824089920602c08201240303460b0b801043c400000020800300141d0f1a41c09030a510740001050b802003003c03a10412080c0d8143c0180081400218000c52400071503507916241100302d40109803200300030160300d0b01000b4186900007001d0200400440d11003400c0e14265a4407038089500b28001c603a19149590750369140401184280d601c80904202c850340c2c03000ba44505600100140005068075001d243e20f48824029600c4280c000d45d40c9581d00e24000d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 16681769 1250 16680519 16680523
    0x3080105010318050a0b040303060812091c030203040306020c0a02040c11010c0207060f0c0c080322080601030b040b06010c060c030e0c03030306090c0a020f030a08060102010f0506060301050f0103020c06011205 92
    0x440d01140005241e0300fa00c00000307802083e044d5220b0b0340150118019290341c1070840c0105910382080703105100c1c03644a22b810301c0e0300704042c00010004032205010b010120441c3c016482002100a0140c0e04c2400709100242054001d8100c405070034084a04c01e032503540000f03040e141c05000030f00101d44038242c0000500420b002e0b05907400850300061545600d0700e0001810100482400c5003007104100c049801c00146016100040645404803511000110000c2842d6682e03414501c000344001a000148194046222030480c0e40240044840fa99a03445004030090014505810484a1504880090414426160141001e540020f2105400c1404500d004e0380320000a1180c1d00a20030040150344840000380d2003489580450784404000401340c2c6042a000d48030384082c0800309214455941c8019100e2203094260300074045010008001011600c0986005d40c11140810060001d4101801a0b00d03c200044c980186800558040242092400e030031020005401c01d0b660020b010301 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 16683019 1250 16681769 16681781
    0x705060325080105010e0a030b06060a02010906050408030720060c0d0905120903070504180201050a0c08030703050703050a0b011403070e060309100c02030c030d090f021305090115050604090218030a030801050103 93
    0xc2520840f14042c1149c032010f0700101c00420300f910071000010400c003568800c2d0040e040c603550000050115003407610b844511600b04880c901d00240c2225152444250909407410242405a0140032182c8034041104030ba9401a0390b00000103444082ca032000510070000a07200d0200550300c03036110f40900007054108140f55010303a209500b4080c40035070450f100c0b4200710302c140e42400d080e69a95001d0609880980707140e4405448204007004016405400d60070061290070b01d69410480c5642e9500400b0845525020302030000d000b040387e4100083e20b100080d03411544900b05170b401501c04100190140c0c2c07040301c0103849504110154400401d480c014003440d0309503800a035081c0307801c0c1000141d0764000d01c0184c2c03038815111814801841008000e02c03a405401800b40d06d103642000008401801081c0d4082000e51328002c01d00a0b020403c55030380702512001040c0f149000d1400c42400082e400034406002103900268041035507507000c109101e01580701307448550041d85040c002400701c802d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 16684269 1250 16683019 16683047
    0x30c06051c0f0b1309020301050601031a04050a0209030118020a06050304020904061109060c01020a08090705010f08090c0402070f06050c030c03010e04053904060305070506032508010501 82
    0x4414051a107660510341564900c250305141c0005903080e102c0b03944006000d0005685401ca200301c40d8481000c503c41c0c012030600340c0260300a00254503100011411100e800308044440c0c814030084400c1407925030440340d00095546030150800c2c40d00c00000e404c444104607915404d0283e1000001141007101100c2c00030292420520704510b0a40c01051500c42c000304002c00740340d95040f28440c200f0303e6005407402404080c04c2a5201d80e9409950b500030b500100015020030100c90005202142c005903007030503928181d6551002a030003a400790340039140981113203920b00079000415655201c03440900030f0680034225250005602d0f041c850102e81703000d031030f00000780400c004200208007503c040303034110748c20590006540d68460074a1030030812910100c0032000d400c410070540e007040303840301401c42e1400c4004080405070424100070480704140710041858025900c100882d00c1c0904c051588800460390480703510801005011803507401c901400c0c0400e044800608c150359101c044d075110b401c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 16685519 1250 16684269 16684277
    0x60803130e01061e03020c0714040e060601140904110d021306030c09060c0201051b010f0f090f020103200705010218040213090203070302070204020c0a050d05034606030c06 76
    0x75042031001002e281c191160300c44c1c852030785480001d410748650304482c140010141959031190b150600c885038111089000303407080d07040c8080c290f038029004c9440317405820141c4540840f00f00002100740c03150401080070764041d544040300c2c08010b5030403008000d0302034007190041c2e442c515007070810800c0040741c1000040600d405c44e03510240d074020400c001503e0303603030805608003c0c1a20048480340f08660100c000c9030981c101d0b5045170041500700e002201d50154091000c241811807840440d07860007400b40c00c86000000340700140d4041e501045009180b40641c64440c80c2601a5921943c00a001210300341e41c002004c3e02d4149881c08070141c000741c115010751800803d981d02104104850045140032903002002c03490080c000d40c100d40321164081c0c0300f99125400a8181d0f901c0e100529000d5840780112005850035034421000c07039200e00c0c2c081c40c4000d113283c40700c0e902c954000800003846480c4c80507841c5581400e50600c42c40342d00300c114a103002ca00b860071450002105401a84041f00344 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 16686769 1250 16685519 16685521
    0x30a140106020703170412140c04021e03070504150905010813080304030e12010c05030a05010501080c0403060e0a2003070b040b04050f040b0d0305030708060d080d05040f06060803130e 81
    0x642e808600d1100b202e4103e901000440c5095010003018400c0f03902c00703807080343d5030500c06081140f102941d040d00450741042d01c099409c0d50041c801030703200b41000310032990541c2682d404030781c084401940d0054000e1803c5030816444159440b0f5808188005502084407158100025030380090300a40c000164036900c3c40c42c1c21181c1d1845910300000e0001418003d4400309130120740c84004405a41390001c1000b4044212048c0c800341055005842003044982030400200c1c1035400b41c2607890165440d422441d190901d9a11180020840da0f1100401401843e0485d004540014013500c0d0a61422081d1a0100440001c03d442c3c500540d00200282d4000d02003086207610039000d403400c480082d43d104440700183c00010300203214414206074003003240890781c024964080c1c055840b580c0c150b02e07260155200d1004001c00c81805840042c03c504040025a1031819190070250b0424460805c3d2041c00400740ea0b20170035035072190001d0515610125400d0115a680c5602c0e0000b84078804080e122 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 16688019 1250 16686769 16686779
    0x60b04020f0304031d0307150905030102090a0608041104020d0b01080601030e030d110f070305030106090602070e160e0907020d1206030b01050f06130e040204060503150601080c04030c0803030a1401 87
    0x15400003c0003e4107000c11101494204203103003280c00c6400c036004041d150402d0f02c40c03a81c86c00d6620821a13050014a0844000c100c6044c144203ca1050f90000c00c118829440d00c8012140460010411203d01c1d20240c500002522203002134401362505040c0820006021000108422801412a4101800c1045c2c14062500110844940024444010036002c801032807101031445014030040120500180b22001d05501c032001c0c5058680a5031424000c3c1ea80b18030072a6140d0550082c2c8007022940d00204040b50002107082d001d0400c10700b0301d094005030406c001401110700b1185e150158004104e030902c60f5038040c860300d0303201e10009401c1203040d0a649619482c8641406054041d03d40800030703102941d50300381520b60700c214424044201c25185c0798075001c0e100d01500c00303c3c05a41801c90229061a001c40c200c2c01511703070401101c80541d00c940044401010180500c440e4110400002c8003280c054070700300f00682186401035aaa0600c6240101220442803403003140032403041c01405 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 16689269 1250 16688019 16688047
    0x70503091305040f0206090103020405130207050d020d02061f08030c060108010501050d05060414010b06030109060302090c0f0a0f0905060d0617010902060d0b010516110909070f060c050307060c0c060b0402 90
    0x84d100350144e038101d80700c00c09800103900a12a40d04511350100c0c0c034000501c205801a0020480305215405640c130714a0a0f020903651030781c8000041c00980c010303000041e0140c4000030140c0754429601c503403103109a41c038250281035074480904d040180d00040010312a15800740141070061005907030b40301e0742e45200d8135025110341001d4001000e400340502018410300c000d402a1981c042c0003001c5659a503904d4208200a103210f1100304e0080c01c420b030008101d90428001e5443380d070003c500d12441c1204480b4201e641c03000241001080c03040710000443e958032080090100004480c0c00001c6a40c00c100441040341c5556a2010701681010b600c0340042e02c41c4400e40703604054040021a400e03100b400141d506000d2400c0d01211821245d22030814011564201440f0804c151100c48403a11440609034903601540034103002001903100400c0440d201d02c0016004134010720a4034144031171035032171006030380d05400e03600d00156a1418803c03c0c0070303091150390041882140c045117048a0202590 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 16690519 1250 16689269 16689293
    0x8010b0d0213030212060708090109020609040506030a060203010927020d170408010f1e0605030d0c030201060305030d020c0d03090b0103110607060603230106030b1303120207050309130504 83
    0x400c146401140e0325050b00301d180b46442c082c5900408801c50800110701c184c0c1d8545e4116500b20008403000b01203960000b0621882078550740140421b494090a601403001410014209a401d4401c1340514000715071580701450180010000105808003d081941500c0000030480c48614001c949481c0042c4d4030a0140b205035907200005246a0340700001075035072400b0b11b9014841d0795007442d1041c0c0240d803450f40300b40e000d07280040f03400e03400758107042d40030b021105035010744c0e0b4040d071020031076803102401250903642180c0301c0e10000c6049a2285d0314141113400080d4016846500400d00061094041c0a003a01030a0b461408204803440d589a4050216061101400302071330801581d10540711031080f00c14680e04410103010a07a43e0340307070020300401d460310310041c45152929240010901030181c801180d41001c0007030b2590300c5850b06c15040540caa0780403800d0101d4a14441a01c1d5020b0001c0e1058900480286840f1031150042c88010300c0041007100015180c4010030001071050084a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 16691769 1250 16690519 16690537
    0x307051315030609030e01030f0e070620100903080705030f06060d020705061302090c070203030f0d06050a08070501020d111902030322050a050306041709010309080c030304050d08010b 81
    0x10a030000c1c0501d00d100100300302e41020b0800390801011100b03068000044500003402a602042540c44501a00089075158214102c083d001a00204030061040d0348000755400c1d11445900030721004000e207464460001560010756888803807000905420501c501da0100d11410f10070700e545030011543c102d050300180081e12612001c80c0254a20006078141c482c0d281d840380845046040c40e04403554000380301c4e07008a1040182c6000140504241c106031040503602034025800c1942c00154940c65404c58000d408509541b00f9001582e60384a1481000030b00e8148050000e07103081c81c00090801c420300725100e06122040010061091000070104020b00c0440c01080b002ea015100090551003032034100e03c00c0070090010404400180c440690444404032016120b1550310b405140d01c40000322005000d080f0107201800c00040103400503e0403510501d40040c0d40d0030150b40b03a8449400c200f00c0500c1070360012040008205003004913400e500c1682c01e0000041d850102e070700351544111014 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 16693019 1250 16691769 16691771
    0x10f0b03061f050603010905060f0f01020c040207060f02071202010b01020a0b01120c0305010e160e0103050c0909070803030f040b06180c070503131706010e061c0201110a061a03070513 81
    0xb90801c421445140c40160200800590303172542d5544503c000b40c41300303442c000c0c8610701d507104c1403e1a01e804446030b600420103802808081c0000e9041000079040003d00790341705e60b00c1d101d500300b060f46240300400409104001e01d8801100b0303028001c0c2168503a03146a4155403006842c4e50202d00302d0614941103507852055030b0382010152402254090382980000e0280d030a200c003a548141e0003041082640200e03404424000b0754606288042d48400e11000c0c00c076030810b1080d50000d050103107a4981c0017804034210f602d0142d070f40325481d01d507910484103a01040314040a0108014000b40015004901140c4d03443c0c0d144500c1c41c0c00c0707400d61f4003c3d04603803801c6800140c1a0400000b031003954843e802200c8a034018a5664000701799803484003030b401000d8014500040b801c42d07944000b843c050701018180c568a020001d01e0034840010190082e81400348452060f84220000c02c078242c48035204200200e01207011841180d848448a00781c0f61107034000b020140440c0e00e400454038000b00140d50 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 16694269 1250 16693019 16693051
    0x20409050a0203010e0d0e0a03150b0613180b06090a062604050d08100f050103020904060b0a090f0906030b0c09010c0807050601180209010e09040201050d06030c08010f0b0306 77
    0x3404a2909541c500700a41550820080e4501c201c000300e01109800615215800071880040400a0b42c60741400010901c0c801100c0c404202c060651050300001000307001c0d0b503d44520910fa203214105284c1c01514026406103070600050481d00a071074060400b966400d0a000151001611800141c0503010400020300c2061040e100c203060f403082d0709030f840045851a818541842c81e2103403000340c005d901060041001c00c2041c03030003030303500c904640004207000710380c03418900110041d5000001b00f80d0320649850010035000c43c80f000a040de0340700c1e5101d80244c2d910307060101014501c6544141d00862421030100f011500d107240c0140c0c00300551028550300e900610040e1840c8020100181180708040780000c00c000e00000d54906940e0205056204100000b4004069109000302103002800c451020344c4c03a420b00301542c607002407050501034201042d94004404451207540165442d004d6a5001c0005101c20322940d0541c82030386e541840070903101c030042641c0d50805044c500048955070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 16695519 1250 16694269 16694273
    0x210201080402040c0e1002010203041704050a18060b0f090a0801020c1005060a030b070c0b01050d110103050405010f0507050405040605030a030c0b0a0f0c050405100804020310020901030f09060c0210090f020409 92
    0x110301031001e00c0024011806e41e010404024001e4008035800c40d0312440080d0b080280780180000d403011644010f0040701d07428146800000050340806142d080c054682a000c1b51111101c000350035803401c00d405a5071211014400c100301c00f04c807a80f20a600303910401c100e0700d2418022039802e14800c01d4138804507040e11110046445590f080c1c0c0050724402e1481c0034890000c0e846080309007000e0185558058503600e440c200034804903901002001211901600a0715500036000240c1c058001d60002503040300059805059500407101c050000e140003400348824940b610483d8050482680109280360301c5a501030000c900122010706000101000600322848039000054510358080d42480f84880121015000340c0060280d60711464007140d0440407640b0a01c2d034644129001001006d80c00000314804000390b012080c00d070304064890420680229032801002e043e80e00c0382200142c20a40f4042c001d00702804490800c03411420014a4000301c0c02040700025440d40440c4c00080d02c514038 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 16696769 1250 16695519 16695527
    0x901050408010504050705090a0b06030f070e030d080a0e010203060a090b060409090b0402040c0f0e010305090c030703050d020609061614041d10050105070f0f080403080d06210201080402040c 84
    0xd9101504543c01d01040108122000c62070b803045070800d4901c5050741c0c42d0402402c00340c4142e480c038281c000e44148006001100c844200c240c04c034103903080181801c00f0b6a00840d0030a001c2140020108207054103000f5030380c95910400f925110040c00860650401400082c1d04601c1d81c82510b1b0a1920703110a01c071103589001c100e40040c201c80e076040051642030710303001e02150801c0320f090f071140e49049400341c0e800d80900c041d41c0d1003207001c1e0368860390241c00d00019802080d0203441c8070301c140314180d2110450b80301040080083e60060f801420b0f0b01c60840c0c0300070f14100c0018403082003500b101040c4590b401490740301c03c20343d1100b42085a010528200011102c1c0580e82c400d2803468404410001c0b580711800085001d503250040c04000305407540e005442600c00c095004001e441003450000c085454503182000940c81400c0491500c1d43c0c1c1c0e00e0790301341c54004210001290755184410840301c0e07200d03181c007041c184107035180403041540303a00040c19000004002034011078039900001421481 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 16698019 1250 16696769 16696777
    0x20a0f0512030a06090b0901050d02010c170c010b04060906060207030f03051213150204230d02040e16142b06020a0f26160507020a0e0603190302060a02090105 70
    0x482030380700d0b1240b600110b003401801c06441113680035440c0c503034800e0305820300340c100c1810384034040c0820030b00302d8031680112440c00301c404056500200c6501d850003c1c0d0181e03030040c0074001c08000081050b00500d0304200c222103140e0301c031250700c0749000c42c02c0103d55004202507040342d8101d0200c020800083c20195128070902040b00c010140480422020030004101078130004c0c062044903a11039424040700b0101d00c224025414035090345003412800d100c4074203000011600142c90f00c498043e42d50f0115054542002c15101d4580000300e540420402005808000b00030340d45c16811006030040228442414104404180402c3c0f0540113212003070344040c0c10095588000119541e4404083c002c2c090010300071a0000210002480342c01c0e05401c01c2141e95448041250b0b01d001d40b120f001010305102c05080070800d01a09010110141c2d43c0ca00c0c0c0d040003130601002d10b11340c92404808050408020758950210701246201c03a02c00f00e035001070141e038401080d450042e5a0040800141e400307001d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 16699269 1250 16698019 16698043
    0x703020703021c03032301180207050303151003050c0702010302030402010216030303020a030b0613060507020d0b01080601050f09040c0e1b180103270b0c0c0d03091110020a0f05 78
    0x90740900103030b500f4840c1100d03200e10300d02a95003042003004402c00d00184d00c03402014007100107641c00060000301500b9200045180419030010702c6e2200c81d0762400e0541d0400c5500290503241d188425110b400d0002844410f00041c2c079040209240c87c8404c0305240c011440081e04250303010001a085900802c154898015203807001e1058540e20714009000c0d60010a01d0030000c0d007001100842810030f08282d5804286d100071300480181858011a803603040114260380c402c41d230004d8130002c90040207039039020307000001c00380c0040d60401090210403013554103079030301a0b015a4100170101e604400648141d500030000d150b460348403020342c2d04030090300354105190080e000a07400954500c840f41d41c030450100b078805016409811940300c00f02a201414010b039580c001c040a80090341003802258804c080342c03481824200c69071030a52501140b0350200c80480d5032100018180800003c040315882e100f2204c84130a1002c1c2e490003500c40001d910014110101200742c402003000c14003019841c91 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 16700519 1250 16699269 16699279
    0x7170d08040f0503180310090201080f1e01030501020d0516050315220506040b030a330207050f210f030406110307020706180605030f19020d09031101020915070302070302 75
    0x10300303035044038411201781607030142c442d100361031040e0981007660068105494050b15058036507a01c2d0100c42c0c0300b080000b07018081c4054280340c00090207503410104c50181d80074400050f142d5a0040318501242c0001d4080340810941d041c5005031154050110b9500091030043e2a135100610300204006d50103a01e03070b61200e5100c81030b0480f083c180780c3c0e10840c402d00c4112070500c1402c0002041c551503a4480300050903038000149042e00300481d1902540c056104032014800482c013600340d40c2c049030044103040350700381c001000009034131200300860b050a48a84d0780155812511418410b918400c9040301c03001003801100003414494540c5c0300c502d4800410360955030320301d88600002d480e82014040c41003c510f400c2841038800a81d509548180c40d081c0d101da510715200c1702402e40c43c3d404000c2030310185042d0342803018150045800a00340380b81c80e66502040e054020f180c00780c801c50018118542c01d03031040c00f0148280e91001c04100488a41d4402c03e9602c21041c142241021401c0c0c1000e5008 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 16701769 1250 16700519 16700527
    0x4020714100e1c0e010804170304080406030e07140f01180306020a02070b030403020604020409051606050c010c02030903070608040c0902032703072301060806090f07170d08040f0503 80
    0x2000e055000149040c00b07040c2607602d0300f1203080000d5408880e804440d40010320314071408645500425120b6007090003003040315070300c11080d11035191b0740e481203608981011020030200700450f010f0003440c41400b4603201412110b402c100e0f079681c034810b00680c818804c0100250310311260740100000c1d600340900c100c8582049449050002c0030b540407000d0400180f14103c00000d0200300355059074021540751f40500855250341d02008040d18100d04140c401b03000782c81c40d803842d100300d12103c07200a000b40e03282e14bd1a140c0760301681e400c540160740d050065404c104501807803a81e000c0f400d802a201c690030b1840c065125400c0203400c8020759040f1012451002007803111007459138510084809282816444000c9039501c0107890b070250100003441e0700750401445407407001002c15840706025400c00000c0c001e5464451902d0400c082e110100e441d0003c20107100d6444040c00680301802d0b0410286108450303240060303a4a42c0d0310740b14502008034400c04202004240351075007000c3c81e00401100d880f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 16703019 1250 16701769 16701793
    0x60402010302130509100501090501080727051804030201050c0f03010e09120a0207090501060903050309041d071215060803030a0e010209090103050d08090c010912020307030203060129040b040504020714 89
    0x1046c0346009080c007041102000040350b40c4110402c51050b0100e5450980049454441c0c80c080080040700ba6036108440070007040c0c0f62103600782414102d41c094101142c900709800c0c06421514040c04c808030000041166102c110ba5201c210382c11034240c09c0d00741480e42c1c8e0300c040f0907040c91940c0c00d060004250000d14184110341c0010f00000b9240d03100d800f003060366a282411341e014030442c80001c20582041c4200d1545141592210802d050a107012000904282c8400c908003075840d0482600681d6800411090211082c07000076042e100d40c8041002d181006c0440e580d030b0000801c8003a00075200d6540800e5600203406413120000081d000d1001ea5071246411911030003c1c100c194001100c81c0e0000c0c90706040081d40c0c1c0049441a103070342e440c107401c01542c0420030300d01d41c0060703800d803066200020050f1002c0280a000780030f41c040d000401c403800d4180d1040c5000643c524515601d040c4000e01040401000701c07401c8540c00c80340140e41e0303e85072030103c0f0302c1c210308010044240505070820032 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 16704269 1250 16703019 16703041
    0x6050f0d1805060103120f12020a0e0a0b0705060a0203040206070210050d0606090e0a060303050405010c020d020603090c090a02040608270601080304050406090504051509030705030307170a050603060402010302130509 95
    0x8181c0c1d1180b041910384001b151001c07241d410381c00745103034001902814484c5007880d03154014080c090300c91a11f41e6984a520b00800d41000070369108180d0000000703124424041c2c00e029040c2c10800d141d03000d505d1400c0580018401d402031b0100603100750180300e61075448500500803508a030110100a0100a99821010f40714000c24030460503111000d10020b45e02e1140c81c4103000c160395051b25954285030a1200448403002c400b1412a000040c0c19040d4025981e0b5501441c4541c0000c0000d11803d5403040178803002d0712028210600c0c44e8011310040c04000e030080010303644000481c031030801000c840b034a03045180c0c420000400f85402000300200b8010ba0102c02081903d00558062011544c0c07441c200c401c4900880d400740c06a045880e00c00302400021900b680c0082c240d50459081103566241c40342540d0050300d504e0007003045a82c0c09060404001102e40d0300c582983d800f00700ca80b5011012a8039400001c200904042d400515802c1c40144010405e02420010b80704a070b5070b00e00004400c03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 16705519 1250 16704269 16704271
    0xd090c0609050102160b030c0d020705010b010306051e0d060f0213053a030908030c03030613060e061210090804081209010219110d0f06060f06050f0d180506 69
    0x800150807500302003099400024508802200581c00c0360300300d45404103040c26504040d11220403c0b85c10050160003008a00241017590700410001901324200400176044804546c012809106507102c2480c01d00301d585108a0003c07030958085408402d6850610000c003000444000342a1004c0b0358031081c030000d860100f007521810780d926000002c803150182c2c00c2d10400b00104070a107588248000d040380c441e10708032040074800c1c00c11070801511809a036007550480b070b1030303000f040d4800f0042210300d00d172a80e440010301c003640d4010007030142000380c1804003000080c038a034090440704119440740d40302040111002403200e0010400c3c1011841c1500701948540324950503071140000000040d0200b10458124980580060041e090103449078807450414580540e00014030b100c0703848036619244480c21010384149000543c815171890b101c811502903802010795403a021200780300154000c01242c0d00358212100c0b4903100c00c00000000040c00d0400c4000b0b50303101200e052941041000103080d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 16706769 1250 16705519 16705529
    0x705091e03010605091302120c090405031c0c0f030209010e0405010f030302062d0421030504050f07030b01060516020a06020c0a080d0207030807061d07050406060302030c0306060901050d090c 84
    0x2030241507504c60800c01038030402c0d0398084e4151200740203c80145400d462603803c005524099030303806444100050055941203c0070f443c582c20024180741040151120114400a074840802507143c0f0068003c0441004400600030705500080380c42050b130280c86005400b10000b08284025070b102c51038030210000360b02c000c130094807030400404c0070a14030568803040d4940c443c06555400203e24030f490b069080162040c0c540300040c0c0c901c040e0054010340303040032160107a14003040d2410304e45030036843c1406000310b203007040d00190820b1000500c2488100c0c115019407501c140c442a15162401071a424144000d600c55170b07010b00014469000f0502c41801d900854296110543d15031006440380c409210000050700036010500002d028400a40741d0f0a02901c80020313096011200300d03a064821440c80c444560242ca400c01c0940b4041c015100500103614003503095003807c1a00c00d506000182800d48910004224640543d01c5401929102101d410003030001e008513060009444004e40a4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 16708019 1250 16706769 16706771
    0x7020a030615050103110706020901110a06090b090f0601060806120106030501150f030507030f081b150a02040e010b0705010b031203040c06080103020306040f020103060b04180c020d050a0302030705091e0301 91
    0x80050550301920074503058946c1000303060b18041c40caa5580c00254401e0786e0441c10b00000c084182d111100821001c810948111000114032926007880c8031285001800b91400d5401644128808500499081e0446401d810064a180c44040000792980070b901003158030b942c644071000003801015000800580e0318034038491078058440440300180a49408041d001d0303809114100300080c1c0b103c400c2e03141c2c503001d400d42e41d091220f1155198060b007a01301c50101c503540400502d445600340603003180e4210781d20510461406140001960360380d0780c140f042120100000c1030060034064290043c1c00001d000506980c40340f13106005c0e51409070070540c0d080d1196150a01d002c0307403141c001c81c6802e060703039001001410b83c1d80d982e80ea131030702e4644651000c07410503440d003100045084642010340080c08074139003001d800440903950902215514000c00303045502c1010040c02441c0c2000803034107062398504c1e0240c0d40c0d40d1441d070f00b640d01d40304d4441c102ea00912042c01307079060700c5195542195035074400c0f80 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 16709269 1250 16708019 16708061
    0x1206031e07230a12030c0215030702010c080601021203090f0f060405120307080a0b2407140a02090c0f040b0406090905070c1e030207051201020309060c04060504140607020a0306 78
    0x6031062500700701240c03482d04034281c3c0c2e01c14049900c99040c59041e1602c203180070441000d81e13601003402d40e00d9000b03400040003404001d1203841c540a02800d43c2044061411400c0b031316040000070b50350000c20030f803d5030303401c40000891a0039a041c86003400c4000c600085070f0002c86814120380d685e007402c0701c0070395260040c0044440c40c01468404c0b680908050340d5005041e88500600c00e00406080c0003075980000030807140c214a104d1051982c000c0101200f031349803680000c1c00d2503c070440800050244030b4100d04c041000582d201c1e0b0425070800482100c15413100201c0c90120b102c0d2080f0f401143d040400810001240f44e401556101515034009092040ba12105c0d030036503440842e018014640503075420f51401c0140300360311102d40d01d40203104417a0a00d69800c08518a05002c40300c58100303940010030090303407110810250750451000d40040d890685845070040c21400381c0d000b02614545c403c0701070f4800b90364031000d0713907600d03a0000c0801d00020341e00d107852002000400d0600d03044904000b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 16710519 1250 16709269 16709309
    0x608060a0b0f190c0c030308180708030a0305190501121208060102100b0d02090a090c0e010b030f070306030b0a060e0705070203030403020405090703080403120201050f07051206031e07 81
    0x110030360300404100d18205050501441d2640702400d00c510a0000300b003180044800454600745e0410300840c080d803140f21041c200903a0701c0410340c1e614441c0344481d5202450800101b80d0010490f80c6000c403a14001400e07032178243c4010447e02600c03209508290800d00045800b881c0e190007014145e218045014217205028015502e281d01101c03aa80075030881c030504040101f090300301940070340300182170380883c100b980d00056080c4020b4a00c108015500c55041c400c0103d82e0500502800301031311100d0f00340d03240c60141c0043d44401480012124540b03000301d0f8100c1d000b40c12103009180c0c0006940c41ba413418414401c002e11180c8070b583e020a2811002c180c026008074100c40b000741c1c015020314949420350b001d000192070094189000d91140e0b84002004c140c51a01900c0a58494110804c201071031070002829240040c144181c8090608181703c0903540100884480c002c850040038600d0382c1d6000041c0c1000c403002d03107003540c0980c2c0ca1588101d581e4086181e602fa43e0000e0140300c0404498 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 16711769 1250 16710519 16710539
    0xe030c01090e06010e03100c0201091101050c1b0d080a030b090a0b060a03021308070303020f1005060904020906040b040509010e0708070806040308090106030c17010c03050c030105100507020303040608060a 90
    0x148078102d000750a01000c680c1c55486103c00920175a000350031030360310310b4112841c08103c03102e02480d880107075914903420b001c00c1061441c2d070882d9182468994100040d00700c15a03201c000f10800d03800417005140750b408030b50302d84201582120390440d5105445440802000c1c01418051521030b20498022000030041c02a0b44a1000032b000064095030801102060940c001d5122210070060070781689400241c03020200b000e080514440d81c041e0848c420f07010721031071510007681440c2c01e800c3d052400300200c64881d01e070b0007a80250115100f6440341c0356800402e00078201ca000c210b03081810710303003005007003901500b09038070610081c41147c41180d9680259070310f411650151317680a030007074004074011034400c000c8160000c943e2000043c10950325929554119895800000c0e40005001d08840ca400280f144040000c61400d013400103203064081002144014000c0310710032000c40e51000d0150340708034141c0d00c0b181d501504880d9142e8455401800d8030504a1300c0034802c0180c10404100c00b40302d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 16713019 1250 16711769 16711787
    0x20a020a181b080a0209010c020307060f08090303090604060c030e16050a050301090f0b0601180305070e01060e030c06031314010204030b06030a1203110702041a0102010f1104030b100806070e030c01 87
    0x25502d4403aa030300c0c0c4003604c074003940c0034009142c1000b400385004405a501408000024081511202e00c408101031000d04000b01c01086241d8640052040021840004c40c0031644290300820015540111000980c0240001e0040b43c1e070034800c0300f40f08a0404003100d40a01504d200b25800a21b4550315020142a9103a0100041c8130210a0580400042c000015290410014140026406a81890903030340c19010b600a4400d40e01601041221001030701e4081d000d002240340044c5145034041c0441c3e81d400c00f002843e40105c00020025446903940480f010348107900c080c1a100b2042160786c0e0038080d40081c0004c0e9907150809021945500c0c00103002c0314007503400b5030103401080340d140f0305400070041522070b0004610104481001a40e6a100d003c4101054035030130035105040c50f00080c21110b200681c010f5140c60203480ca0380c02004d071015107045a5101030148220360300c44a0f01180b200c03503540011040d01c10101032006058100c5070610070141d00b42d003110140d9480030011504030031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 16714269 1250 16713019 16713071
    0x30605070806040e0d020705040504060204031505070e0a060f0c05070506070f02040e03030f0a0c030f0f020d060506030105010504170f010e0319050403020a090c1e0201060e090609061303020a020a18 87
    0x4840002044035003464ac200e141c1c4140140e50040c20301703a072030300d8040c03035070850b230520f144107668503420000880e41280300310455000a4036000b011505050001d0900e50400110f0010b0003141c50044003040310030000a4003400700a003405072030f0122454840074082c0e11000c1280b0507420140c00c0707000300c9000401e80b4031844030868035158540391402c4100007410f07506d501104050300e96103504803130320090042000401d0210b100580d20100714030a2821641650000c0c0d1140340e08100401080c3c0e400b60a44085e00d4100034080c030305800b04605185403004040e02040d1550134050030b030705208404005055011305a1000b2140c50400c24030459181c811404002c0d441807004200b0b100400442c1d0200442c2c00140c02c0403d8850b04003010781c880c0da80d01042d1034005070b4442105020b2a048a8041900010100700030002c504042c5010f171784640e4010114480507103110030300c006061081002e9090180c02a0103200d4544d140c0304e00c031803a024520344810a190501441c04d007400060105503140e00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 16715519 1250 16714269 16714273
    0xf0106080f0c0d11030601030b0402040509010902010206180c1206040302100605150309031b03040f060309150b060d050a021801050711100306050a0902030915041713030605070806040e0d02 83
    0x520050b04002c040b0505039004d44040d1548003040303500d51410000c00d8081c0d40501f5203502170f1700e002d104000640394003c180e4111030741000343c8080140d80008945410484400754840d04018040c8040e00e0500301000540d406241001c10b584c0b10940460024084c6010342e09403450314040c002c3d80c3d030a079a0513200315900020a800c5180d000c000d02005190070010724420381e032510040140100701c040107490303062001d0b000020700700f09000515403420002c0005090600919402d40c8559420100314421010000c2d247c82400f4600d559800407202c050300c510700d00b0883c5091800e80c5000941003000352f4507002c60503107800c18041d0300482c01d8030805070780004540c803045002c500f40860175109000f00418917440c1c0c5808202650b030780818101400402c4001600c03842c0820040c1c3c900809110225a41d52420080c403011030b805088030050342a4244181b03540e018030b0f5030302e002c991000c3e0f032011f4921841c0038140714580d40d00160090141b0700844040c00b2a4010980d2944c8400a443d981c1005d6 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 16716769 1250 16715519 16715533
    0x503070201030908090603040606090b0f0105040b031e04110103050106111b01120603060b040f1104060c020f0901080a020f0307151407020a06090e0a110a030203040c0f06020f0106080f 81
    0x10761080d001449018410140b01d402c1c130040c1000b180c40343c0c0081c0d4003140c101d03849040a01c2501481d2203120b45003a001c8504040c0f031101400081c110f0700c201d00031400c0030700c80000003e90300340c120702d1581048040c0c0c03540f10b1080d29250a01c080069014009180020b003002e00000c1d12754800c20b000102035480c1c4000d1300c8108070f0111007180c41c00c8144031135814400940303501102649280b00d1080110302411011404d01102c904000444041480c0c4100c601e02c0c00e4091000304500e103050710b082c0c2d201400e2161400043d4000030f04e00384c44050009a01041d02e9002040c1c0140101d00011141d10030342d401201145210101601c03034100f0b005601104403d0700009080c54400c06800d031a40350350480c0d0614001003030700424404140c03600468041142410100144100d41d01403580c0301806010801c01100f454803081d002e8482d0540c0c0804051300400481d05106490140c080100f00c15888a4000d0741c0d9035201a4a949440e40f00641551130030b0350000d03150102094118030348154038041d01d01 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 16718019 1250 16716769 16716773
    0x1103070e0d02040e030c010e0705060307090506070f0f14010f0e0c010f1b08030906070c02030a0210120f1b08090a02190f0618060302070b04030e0303070602030f0708010e04050307 79
    0x1070389903550001d9038800c2d100c41c02140f85800c18001051080c0306200046a40d050003000d403458000e0903807049024900400810070700030b601c0194102a0303401201c0540d0b80d00c0c807508019180f03140d160401703810701d58044003240811107030300078620303540d0242d000900180d0303250b444443c200e810f40280b080440d045003516200941c0700311000074085001f42011580540824881d5040d2403802c80100d83d1500c00000b407008a01d410402c0c00c2e409201c0e0325000c60752141a501003615450340307400082c0503a0010909141c3c00e400307626a1407648240100030000c0701202d602403000f0300020090802c410301300c0070007018424401d28121744100281d50083c180d0851130790034040d09200c004120003e460300c0b020301044001c503001100d002041e2070387d95044507103080c0c2803450303c0032080c1d8080380600d48104a030704001150710302e802d40c0c01a0142011443c030b510300404242140304a0400800d40c030710000404c150317001f45800d00780c003c030724958481c601681c0b42d44030211004000e4034050100d038420700ca1100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 16719269 1250 16718019 16718029
    0x4140709090c02010905120301080708120403030f09030210020a1b0e0609060d02210705060a0806100207090908031504050103051b130504111305010f090908070203070b0301091103070e 81
    0x403040100c3c3c0700024400c141604c5090404940041105280100100400c01141c007040201c025041103009002241e00303c107095540b0740301c0c81c48010284600c100100c0780043c050300b1310400a41d005024441a4500c910700291100b03580d100880d06108500c004050352445440680d099844002c95146103844220402c002500c0052400380e0226200811100503224a010140140c245c4441098a42442c8802c181030a0054104c18002c0c04140450189036611100c0c682d003049003590a10b004130340c503800132401c0c9a10340d000b03a0211030410b4109002c109200d07000758803d205101c411200090010204002d4490a200150441d84450000700c01d418054040540740b4900074140e124822803146028161502100c040c0d1b40389420a11203806030802c0409000542c0280c50100920342c105000300100004a01032404019542e0301540c040100d05003c84003150340050454041565602c0c001b1155070090043d66a560308000c600c0e084030380c860007030360b028031071544a9003080301003401840 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 16720519 1250 16719269 16719281
    0x302030903070201120f021207091406040e0601020705120d0908030a1403070c0507030b07110d14090303130b03060a080703020f06030606160501150501020604020d03030905120307020c0414070909 86
    0x30b17081e80c4142040c004d1005200500c41480345031800d04552500003400341400c0f1300c65200c2040c24014031001002955190700701c40070780d440e00e03802881030348551740100c4c501403ca4005c150090741c464030a8403038000024050b031061030340346c1e40c00116903101e5018580302d0180c4c81c4014042916040141d0301030840d040a164440d0552911840110543d125240351169070340c01078501c030003c0000d0204880e400044d83c01c0010781e80e00148000d801c1c641340203000714426010f811000c0b501140c140d80755070307040c4100d50f45880c05028001450f5160640c1c0c60141e4000d48106100d100643d80c00a00103502250714000c0702d07002040e0445006c0c0520511820740d1004000551000d003c0004098041c4024621401e480c001c0000181007441c0c55003e58211315503806c41c50556000304204030040c0d43d803201075090143c0c903240100d43c24446140043c5080301030030a5000b2210040700f08090f0607400920700c000d81408840a000c6200c92441c0c1703000421003a40c048001550048083c00070700d5050300b0a0b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 16721769 1250 16720519 16720547
    0x210303011712070b07080703020304020901060e2d030606030d020319050712020106060e0d0c0b0d0b0d030c0303050106080105030a030c05070504020d0609050105030c2d0907020a030801060302030903070201 90
    0x30b80c0c10402a2000070000d54009802100c0401460b010303c00318650168560ba071102c40c50908520354142500099005501441030204100c216441940c041e1103c10514884541841191807820810b803462140740d8031262916000341700d0040054038502d00054454038441050300039610b0f1109484080344122001030040c414001e0070400b2000181140a0b404250078030f580c0002040d5090ad5001440e000301e01c0703689031042e51500082c20104120072074090854001040d03031540c0d074400c0364140001c1c1081203401c917413207000482c048090540120364181218800da0b030070440c2e40c1e01c1e50800d071070041c02805242d415601400503400040e002c0c00345052064010303003c884419030381d180001d080e648106603181c1d80e9034488038200010490380c065a805484228084c00d800e50300100458090390156019a0480f6001c040c80c0b507040b05d030081c954480400c043c2400c03c1074a4844006544c44044182c00c0340003403400300c00001d00718070a2003504c1c083e00220340030394035040b200e800440b0304e041e00c0105 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 16723019 1250 16721769 16721773
    0x30a0b0109110f040e09010f0614061c02070b070f050301030b04020613090612060b0301020307050703050f0d0c0e0f01090807051306090501170601060207120f060e0604050303062103030117 83
    0x2d0020801d480d00080e000170114215030340500e00d0510942e6080d1000c200006031b442d0705208050108000345000345290784400c1e07070300c1510ac11011021048100d46aa8506038a5200003a00b00a10254104440c41408181c039044030402171984112054070007448054155603200010400516103580108074040e4414650085140c94110b480d0407101d55600421005584070700d810304024030750080d82d5500204038021421444c11000240040c451300c41c0003010858001840e8078145103050650b04c103d89065010000001c03140300c0604502c140c0c070740c01c52240c8400361038025690305c6885118103940c1d00d03c0c050b0003c01e203844180801c0221b4003c070030f5641525054045100d0a00c3c0c441c86009080c01030500c60b8140b0f4502102c1d0034403006030080021500410024130012080c8110032400381d5211540340615400d50400c1c50040030800080301550150005000c2400300c00030240d40184011141e040d44200c800c8110f1200002940d103400f02c035002800100444809002c03816440542e03102 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 16724269 1250 16723019 16723027
    0x5030a030c02100e0115060302070804060e0a08010f05040314160803090f0609250b03010b0f090603070c050106050402120609041407061206090c020a02040509120f030402040506030a0b010911 84
    0xe100040e9410354413100510f82d50386228802e0700c034030031948500602c0310b4181180f40c060961a103e00912641c0070b080c09000b805403600019480d00e111450041000c04000c0151084040031440540b0056031300b50700185000c0f00c0c41110400348007c6a820403001058411007504981d5500f40e030703400041c5103400c0c60003a01c0411988070070600c0068030429000002c0c0161002081d600c0650752451a1210840c1d11100024090315448600b200c6c15641c4407900203440300040c0f0148140751242071030303160300043c001c418800d20580040300d08412922400003070007601c0e200c1060004030b01800c0d502c0c501da00c01c03503808034076103040900180e81c0040c095058242010b0024100034038041d0700b03501000020700c5101403444038070120301c5010080e00a00340244107180e01010001d588541c034141c061320503962040480d440280c1004000341803811500d4080c0c8903500d0703812a80d07184e0021601a4007035814400003e50520380030070b0a0552541c020030820980c5d0810002c02c0c02005004603250315004104 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 16725519 1250 16724269 16724293
    0xf040201090f0e01080d0503090a1103011509050a060e090703110a030210080919020105032e0602030c210f0c01060801090b15100815040906020403050a0c0e0405030a030c02 76
    0xd108030142080c0503890b40f503540760070440341c034040e030603000101000810b106004500d0400b181e02d1050941000300c01c00900d190900090040000d0b14103c0c1040720303800000280c0c000b0503007110303124500e01c8004000c990350321001ca041b400c00490380b20078503410801060000540b02c102c0c00d40c2e114806012200c0c0c407507d80d0f011507500921140d05001040c15901000529076081210000820040c0540080c0603540e0740042c00710701024001d5110720011081400350b0075100702c0e001e06107032400b02e60502141d6135000003079101d6106c031030340e800940149040c075403c43c81801c5205003104c0409100c20300d03108000310001565009406003018554032807500040e03166090090010041c0030b0b111403007490821024401108404040083c0900445400660902c2d0848851948600040f46000c00748900c0e00004005042c03220340249031a00c04203001c401d1107000160a8442841541c8031110161900c1024003101008c40e001003c0750300400802007914800d0700541310b04030190040fa600c11441c3c03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 16726625 1106 16725519 16725539
    0x206070806010323010f090605060a0f0908010903170610080c0a0c0b1819050a080d230405010606050c0601050f010212070308010e100605030f04020109 67
    0x1000006070300743d000b6003246202403551143c81c0c0c0368912007120442d00c104207010f0300a02044569002c41d95030490301c0f40b01c060b500000c103c541030131400001100d08202500040d0300f000000f02001442610900410004034402c1c0c440309a040c13800c2c481881c0b07244006080a1040d03160402c6032038601d81006202c2d0304810050032080d5148004141603805002c00d9000412409005040200d9100c40241c488038460055081e070300082c40716001c2120000781c1e81d00140054200050900001e01d4080090250305005000442e00517184401da05800c40c08000c602c507800c081c40200400c0040c00c1c4160301c0030b8045810301904240c2c1c0302c0101d5588a0050040e42d01515000c200c01110303038000c0003494003020400702610790320301141c5030040086a0038840e03000c0700300c7c000c804035040d10041c08041060302c80c07681c1d0b054110340d02d0343e544042000020380706a0500c1540100450340040e6 = true := by decide +kernel

theorem cover : BRFrame.Cov 16546769 16726625 := by
  have h0 := BRFrame.cov_init 16546769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16546769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 16546769 ≤ n) (h2 : n < 16726625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
