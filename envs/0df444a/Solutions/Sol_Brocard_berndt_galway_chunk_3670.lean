-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3670
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:20:26.010855+00:00
-- url     : https://prove2.me/submissions/966b428b-8a7a-4192-b3ff-c347846d4300

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 659892086 ≤ n < 660071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 659893336 1250 659892086 659892091
    0x304030b09030d09060203191b0c02030a02030a0c0f09050103050615030a170417010504020a03022106090a020112020c07051e15030412050a0f051e2a0133030209 71
    0x703035000368907404c08e5003464004099180d0030103840c0341090f03040c0d000407040c4040c40d000c5c24000e2801c1c00d40d405840c00400e0500346420406500f50280c04600c506001d0301ea003901c4112201a0f0101480039901c1c171058007140c50a000080640d008480484e070f054811305440700090400400352940c1c501240c0d9040703d03c071006032400782803c4c4081010010102e40002c0956612100c0c00240130700d1801d980000d11501e000d01009100b09034500906541c0d20705100c0c1c0c100709984100481d015402e01c80301d11a07403091a000124000790382e21591a00c903c0a170b0098417032014203040203080e000d00301400c00800301502c4241380440011000080210703a51034a821804000c1c3d245e209039a420541042c11030360503045420014000200a10811940c3c4100c0c1582c0120340ba2401980310004115201803075000c0c4030b0881c0c4446030214400c08910981d00c05d1034502540244006460711f41c18952900340c0b0802a4019028040c009441030a6604407100c0c186605681c80c15000301c540306c0c0e00041100009 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 659894586 1250 659893336 659893343
    0x5040504090b090c01110a02040c03020f0a0c051e0a02010c03020f0d030203090c06040b030a020304211110060612090c050d030f0807090311060c07090e210405030304030b09030d09 79
    0x2010a008043e0820300070300140540c286000400403c5428509075581603c0d83c000f40640c0c0c2e101c643d40b038007034481e0707050340c2c076100109000c259501c480040050202c0a4000107441764083c48001d0a8401724810f1082515001440070380080305190b00152504902e05a00390254081e141403000b5000080c803260030301482c251030068503030801d0b8609e2454500401444c0703016000c200410f2040020070401d486e03000180d4100980d032a5601e1400b00801e1105510807541c40c902218041200c82e044606102e104030fa040868200108140c641b400b80e951a110703900129211214400c0c40c2c408580208a299005100c1003816581c3d0f00040703034150401d940283d000514010202d00f80c1e5612038500340d00310481c0c0c035282c1c00781802c40e2105500c0c40c00c400f0000d4820040003e00c4903a044040c01844024820f8040400c02507a030054515202d04e101c071290b080c401030380c861079218400d080c0c00fa18207580c800743c02907080c40d080d40c0d40d80c00001e001030140a075910081c000740d48420404d00807000150320 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 659895836 1250 659894586 659894603
    0x30204240c020a1509080d0219111f2303131b060203130b0306011b050a150b031618050907080d050a0906030c2304030c0f0f0509040c05100504050409 66
    0x14549070017001070350f850700802001c1c0c2000c0c60340e0400580c0001d00341008929103e901445440904c1c21104040a014400d80c100e119482615000031801084100c40d40e016210240d0f86c4841e89030440030100420f540310003600c2c090004c5402240c80080d0105814400c0843d480d4030020480a095525202e0b403080300164400a0804402010405030000a0401d6042c0710704505051002030000c0d01030800d403070540c0b02120700307580604c04104a14070100740c0219900c5880241c07403101c0302c090151548014003900c11409101f044400214014003102d0031014000c0c0c0140c2083d03810b40280c600a00000300920400002081e10941808100c007555250f03100c0d984c0d1500e2001c1c02900303001031a4030144c02c0c5450b0401521501360000c600401e0008e034240e10b0760900941041104150045410207040e000b410340020880b1200303175404c58151003420030354500b0107650308100b012400048a00504034101d0300010131076414150702040203c0c1f0710341016805c0c5034a0308089821940645c0058440c0ca1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 659897086 1250 659895836 659895869
    0x4031709030d260c0d0509011a0a060c02060c1609020702040b010305090a0303050711010c090e010803041a070f06050f042a2706060816030204240c020a 67
    0x1d000c10520140b01081c2c20500354804100c4400e0005000b20703c5403120640030b02d0b00041c18800a941100d01d000301d21070b000c0280d0f042051b0028000c101c0d80c005c107044940d500040c2c4225103820700c0344108440d555680d41900d88400c0d4207128035500908001091807103103841409003011020717100c002030302844c480141c44907007a004000941c0d101989080c140b6242605100c1440d50100d454090380d80c06d82808960760301e031070004981c06145071005401c103501e020806850103922420300f8040316000c00e0401030903602d88180075101d10031440f8100d4000d56410440c021300400c000940f030702c14003811503500c00425070703200e007025104111900f022080001c0100420000f40a160b45011285a071000c002c43c0030054011440180d103000d048481010f00c81c00310b01c00e16a112680b0b4069280000500103a1b5484002a1000b282a150243c211000d0354031000c142e4428800d450840f003d0715031440340068802c04000c0266142618401080400700c422030168540f214208000c10640101200c1c3c071 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 659898336 1250 659897086 659897089
    0xe04090b0f1e0709030308150306130302120301060c02010f020f0a03120c0e0306191d070609090221040318031113090b0a0c02210306120109150209040204031709 71
    0x550940c81d020800c070800003c1c00320443d4844881002c0c0c0707a15040c11242e036110b40042100c075884856000b58944a0841003000d02124031030b018040b0b5110380c0031262a0000074120740502c2c0824001d1000080308801e0303d07009076104d10b240405401c1c580c0142e8282c1e4148924007800c2850f82c000903800700e0452a003915018820b8803c0c0300e1450111724084200c00c220700b000130785801d8050030503860440328040d190341c0c81503a54401070050858296a50000c414141c1598450b050f501c40c8002040000301e0010f03c0c3c0c03003103000f02c500040349003050761f482c4608516076070710482c0040c10960401150400c10480080340c0d00f9004042c601825110820700040410844908020303906100f5842c02c0c82c0201c8000b982e03042c19990400d540420124000c00a01d07405c130302d0241030a10f6014448003451030184452940703c0114014401981e10380d050000c5030781014282d400410005182c249030100d4502e140384254007400241074014030240ca803540d2070721010030207004a01800c6641a0009003e25103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 659899586 1250 659898336 659898361
    0xc090c120705070309061d010815040207110405060108070509040207030e030f0a14011401050f0d0b0a06030b07080705030a050604181b050a080607050a1e0c0b0a0213060e04090b0f 79
    0x400d02880d140d440e100c410300010000440303180c01941480034030f50200b1050880f03103192b030100000180003103444424a041150030400d070f1184040c021440c01001c03d43c00d5201da1800d52040c046611542c0ca010313604801d10000794007103a0181e04102d2030020300310306941c080c0f052041c3c0901e1040204141d26107800c1200c103421840d04032007030320380c5001017a03160384010107901411140201c801c0003d0024200101d203450801e080018800a4804100412000a03070302060503030b0b02600380030001da07030f40c54001c2e039482d5030a880c2078000c500103000080e44100c0c6504002d80c03000c8051300c08107500b418948a900b00d400070500440708079000c2c40c0c00e41c09094030101c2e8070380107140494070841450319011007140c450038080c0500c402c20000080c0980c02c42d02946031703c0b007210112510000baa14465a00070245101010101e0300740e1280004240000f00c80c0c000c3d01d114444810258215614013481600d10080c800c3c20540c00c01e07241c18101022850041d482481005070300380041c82c42c5043d0b0030042c1e8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 659900836 1250 659899586 659899589
    0x90604061506091701060b1323090a050703061e08100603170c010902090a0e190b0a1505030a110907050a0c0305090112050a1d010207050c090c120705070309 69
    0x542030280da10410950760f100c4030100880e9040180c085107800c180d10b400380580340e50703046004400e1001556100c03080b8070322100c6007169403080c0d140b604a607180c1c1c01003040c4003a0b01d09040c0e0009521011610105995003c240c00c180d140c1000189155140f040501804001c10b100e4805d6a442c1010418004207020349200ca60b400700040050b94115510303a0303400b10401c0c3c0341561880004c106180000025800b043d91150024580c040d649810790440c030240000d20070042c06070144a0070b0313031541c0342a0800c6e40721b00740e401600107003d80e40f52108080106a6034480d21050b1810a50004550b141030000c4040c4600030360748010700d981e201040c07045414024084008203d0704001e902c0f40740b41d000f00882c2c4030b16031500e4465561691600121190a043c9142c03044c524070b8241400400c0c22a54403d08442210414880d0b425001000482c202d0103159006402c541084c18441841c0c6407081240383d1008500400c03500786200c540c100100300c1030440b0000081f4900144840c14560001d800c3c50 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 659902086 1250 659900836 659900861
    0x100210200d02030403050c0f011514010c02040203072114010e010303050d110c15010305010b0d020d0b04080f0a111515190801020708130506040b0f0705100509060406 73
    0xa9048061110034880d521500890850807076011002c5002c00d807080c002c5a102c200c81c242103840f60072904441c14001c062240100040c85490540001c9203607020450407480e110584605000c0085030f000d000c040c1d0300c010008000c010008120602d0802c2040a842107242e20000015000c8002c3c1010042d040c0103800c80f05c25040c00780300400009602030200c42404100d1f0001040422041046500c24016600c0c00c21890142c2c90201000c05001c070080c1e4103d85c0900000e00208284106001181903003001c041e400000054000001c5483c0c50a2190018030a50000746052091101c4428070f401a1169600040c80c050014260072001c000004040070b51004425441c100000369004000084140a0180040b210326034044108410700e0001020104001e6548076280c1c901030050394000c0000d17001d5108040c0c1c010850f13042007400c1c3c1d4155200c080d11503243c48240d002c004070540104104890620800100300944422801500d0064003d800240002e0815143c0b01d010f507180c059440 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 659903336 1250 659902086 659902121
    0x9120806060d020d0603020a03080304120801050f04051f0f060305060f010c0b10030c1401030e03070c0b1c020d020315121c02101416080c070212010b100210 69
    0x444107680e8041101c02c0ca840c0000b0059540501e0312200c0007034085503102a41c0070000c3d00c40041407080620041d48507610401c54001c00c120b4280c030641d8024000e00941d50059041e280c40003050070180d10440e0803400812142d541048441d1180d03000410303075000400311050038441005015050302429401075811074902d02c02c040c0d01000200315860000c8040c081004483c0824201ea8055180c1c80203580c101c59005a49074548844003805c0c0080c0e0010b1340003d01c2c0c040a00d40c3c440d00881034078240d580c402c222038125454000f411455400c0b10350360b182d1529042c184100c060f181480201411811b00c880582c80785040d40300803404012010105e4001c1151541441d880040401c1c111282030031868020301c3e50490300b404901e00313001c000c44520010328100b940481c01c000c00b00100d12030260030542c2c0700c3c0d250800008075000d44080d103011101c80b42c1403112a0041c0750800c130b103501c01c000c6a400015a803410b43d00007401c280f41201c050015803c200d400784030400c0300313000e0560b0051151410 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 659904586 1250 659903336 659903341
    0xd05070321050304060228050a110604020d240e0a120314010603050c0c0106080109290a0b13150e0a091e06020c0a1a180327040906091208 61
    0x1030010f100081c0001c10a9500091349104c00c0e00e212080f104080400020764507403080c0343d0019202d548111000400314061801104a01c00c0010703080348502c0e4045c01c81c3d1009140756807030b012480c4e0210050102401024407a600d40d00540c8110088564080014000d101450400480110b400d000b1081014140125810680240700032207044035002c1c80c00241c241d40d01e520949460080c50800d189550230300500044510054004c0c896050090f06400d04800d1002c802d0104055503c0d009059540b0680004d103010210380d000810b00310024020f08102c0041c0313009070f4100c0b80001c5440c1684070820005015280c403050946a00202140b4204070241c21303621a41864503440b0210002c60003800c0e0090108046501a14100c3c3e015408840120042d07180041000d550340307150544100081001031490084c000750b0390440c41019020318540000282000510788200d245400a1525809a0851925284944120740f4001c8400244000440c80c0218500715507401000c10090010117 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 659905836 1250 659904586 659904653
    0x1090c03231911190809060a09031704140d030b150f041a220f1e08120d06051207061d0a14040516091505090d050703 52
    0x22568001800703000346607964242c8000056140401006080c50030044001d00141010b00607107080e0302540905003002c0340c007100841d10341d601121280001d0303020b0f2001c111924020352001c00c05c81e0080c50031500311600c200e030040c5409001d42d4100c80c10055100e18440f07640e002d10400074016880e15081c001e0300c1409002420304440c1d0300c0c480b4409500019032003203030516081101c1c0140900404000400d0030001c82301d0198121515500c5600c41500d0a118003458030306130349043e95800e4880e411854246409224220001842020035020300c50002c00d032032000700f001c0c1d48511915102c86a581c8140303004031040d03a140717038415400b0342e48594910b9040740c1d02186080507261a80341c0700f1f00f13500301c0624890280ca8002107454024050b210301140f8024540840e80c9020750680d000d0000781c85150034410f5401041d1451800141400d44c2801500a40b001000d001507513858041d092070112000100c4650b40000100d1f0b01c1c1c1c1c003c4804100300301c2c9000141c0d4541650000c2160603036400c0c103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 659907086 1250 659905836 659905871
    0x3030705090307031a070f03050c030f040213050906070f03110f0a0234080316020609060d05011805090d0e01030f0905010f0510170307110109120303020301090c03 72
    0x4000000340240410710000c5a2010003659004541008904c04111042c0407191324241c01581c8050025942d20340082200d402400381078010b0b40680105440e42e44c684400701f00c4424090703c200c4e0701c545000102002107401d8001c5c50301900070040074001500f403c09001d040303c00d18800100c14581800042c8211a800d201594118107007908100e6841070042c0e000ca09218012443c092a0b04044198049401c849001041d904400500d55103485458901c00d95803405555030651415120074901401810054080d000b1600013030905414040c1e9103200c002521002d8125000f0802c00003c03500c84c405040c0241d1380c114204002078a020070319114002c104041003a03405050548414421301072120740c0e40154119900310008000c52103c012000c3e020b450180c1e400200780003081e0021480e10740d03009000000d00d6114005503d0102c0d644d84162010314140740c0141440703410607001a0b0801049882c088083c0700341d40050340ca40c10603020764112030489070000e08240c03070040420303030810160 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 659908336 1250 659907086 659907091
    0xc2402070f112739030609060409151a151e09010804080c1c0f020d030e030d0b0604090203010305160f03020108180f010e03090a0e06011e020c030a11011706030303 72
    0x20494050360081d001c13120140c100041d5107000b52148500e0082e40580c1c83c1030140d400b6080c1100c551109884180030401aa010b100e00038240203103001031041c03034006680c080d138070b080084140701d4002c510100000c0c9100070010301d0700998460004e8141e105051401c6a82d502046131a501c03414440da40c0300080c00f038a40100300400c041c000203140d071101041080042d0340c1200103800b261901d082004001d0060b803001010401511500481110480c000d010703040c032900380000111f0034040c1407c0484050a04203c610b908441d003003001003810080c0340000c501031030040c0b0060021080484a0f0362903000740e540149201c00b0600d00520060b80d01420194100e085503812410490511549038209020840d01e40007543c6400040488590f001c0041e04c91440101d886c000f00d5543c03604250b1811600300d4299000a04441c5410f01c10416114040030700c14031803040794240030024011070f00d00711001d10305945d0060540400350240d80d2082d1004200d00241030a50200c2c00d02038086a03890102 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 659909586 1250 659908336 659908351
    0x14030405060106080c0d0c09140102011a0409020f030a05011409161a0c070f060f11030406030c020a05030432010e06090f15070b070c2402070f1127 65
    0x11000c5828280c1c2001a5050b2110100080041d010383d224081c0c0b00c0c208d00c0c49510340c1c40c500042c44402c2c0d0340c0103100b071b81e03002802c0f00307014041c1050b203204000040000c14400c0f03034000c54614110009031020440e5a0406100b1000050b4840090b03021524000c070060100d022036010b152150b41219090320355030308071046940140b08900308540102000e0261811540f80ca1040c450009010304080c1c483c00e0441d54180c890b44640740c4071800450f0344180050821540da80104010444c81c0e02c203a003c100c1216080c03065030b034036400c9a43c2c0d00c2d0540d4050741c0200c500c182c4038070500c507007502041000c40d0b2024102c0b64100120f9172000010703100b04483c82c1c1c2d0611540011990b442c00351101d45185004440041440e018001c03903208191181c0c0000c04260345000e9003c0c00180c03054001c0220b50a038a4100d000d22202c40030f030400f419810b060300c1c04445061502403190f84001403103804030040e514820074082000381c105400344038000ca25a80c03040c043c411000c3c1c005010712855001203802c40e00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 659910836 1250 659909586 659909597
    0x50c090403031b030506041118100201060312111002090d1b0f121a040803011502150712111e0f07050f03070c0b0f0a050d111914030405060106 63
    0x80d01d06094000b000c002e508200e00206984214a18980c15842030744601e204940c204035140c9010750208907801140c0c0400c0c00e004100040342018035221948403040c452900c0003240054036955001000c031100c58480c0d01140160924080c003800034070440c4404180c2c40c00071030522032840002081d502d80a503008d44800303407803c80d041424101a00b080e001d44880e04e600b01040f41da8030115254014500c20a0b150a5041405643c1101aa0640030b00403500807524509603420800400100400710b0098001e601c11280c0c821758001541c24298424082034841c01c1c0ba140420003500166804040344180d107860822100d1941002c00c01d000306403480c084802031701c500080000d458130380300b0440064030b42d2040d21042d18443c0000001400c40910650740c540d500d981d2400401030320f018201c41a0306420050221448040c840c1014022507015440c01107002020840c1030406548102054283e03038405003240340405170401c60411100c1100d43c510b07859031416844003500c500060103010f0401c031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 659912086 1250 659910836 659910841
    0x4083a0e0111060c090111160e0c21010312020601080d03090c030506010b19030c051c1d060727090221090109020f030105190b060d02040906080118050c09 68
    0x34451580441c40c00c078088100c990b1801e294007204c245401003000c0398006003401c11204c914240c04142400d241f100080020f50090420485002c1c40d0b0300102509104003080c400344121034200f0b1415140c005542d401c002195040d41014114244c0b041005002c0d07601c11401042400800964200689030620700012645602d00d080315058040c1c0d271016240e40304100c00492103040b5080100f004c038440c0710304440c4128001c80c0a07826100d8000040c1c01003070050080070308104811800800340000c00000045503244e95560000c450740c04101072545901c2441006030031608040e041214042c000f401080700c10100c01d0f0000c0c400002d01492040300d8000c601c60f150480070201baa40c0b62000b070607540c1e190b4a0300580050091408010a070300c601c0c1660040100f40c2010700c00d05004e02c81d80c880c41c1006d8180c1c41c1491024000341e9116076040350042011134a103403402c2c4040e00107440b9a02001c2030070703468940f00705e00303613500c164208120007000140c0b440061000100d0341d072200025900c900e0940d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 659913336 1250 659912086 659912089
    0x140f0d0b0c0d0e0f1c021501032004020d0507020f0a0c150e100c0b010905013f050105090c060a050a180f0306140c1903020c1204083a0e 60
    0x240740341c0320f400c1502d10402c180c200001c82d010800390300c0d441400740a004140c0c2508002c076952281c040080201101e820014408500703001c41254040a42e980202403480f550741c04a022a03000c11008651182e481c070912400701e5050150ba01c501c004040100124407e58480742e5251f1554031070320051004440178040100d0083d000c0c00041d62006000014031002040040c00300700c9041011682c421482c400890940240c2c030a4034144c0c0c04c52500e002c800307416010140c48000c4c5107000e00b8070394000d04001031945c9980030580b000140c0b1450000c07801d070602007041443c018058803400c0c032074042440750075810b56000080c0c901c072006514084242c18a00d031030050314014a074001c11050a42c0e440c0c08400d000d0540c100042420400080200995803200008503501030381c422307030784403003c55a1480c0c4410b200b5009402c2e80103100054482c3c660401510709030303980c0715a0003111603401403264841410349490844203142d460300d500320781e0011410405060000603101000c00d000018425810030b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 659914586 1250 659913336 659913341
    0x7140d020901080703050d03053d0f0509090106150c03031407030218090613111605010e07060305090303011215050405031309020c0a030309030c0c140f0d0b0c0d 71
    0x840c0c000d00303241c5080d41c45140311501d039191800282c449220b46101521082e01c00d03c1401d10070320504085a40c4172001c405420914500a2204a1410914040510fa03014070f03030300c0440203003a0799492030308040c54802405203004000302030a426901d00541000506030401d4095000c00144c90700384804029450254000d180d2112407905070a00e200401030312035019802070008a04822800012840c4c101c10040f0060b0100e0300e4a40052810041d1900c10003c6c0c1c20100f03c42680c40d4000d414146c0c11070340590700c801d05d07010641e481d071746034030801c40364100501000010700420724041c400752800c469a01c2e600e100610482c015800024001000e10100e540d584500c20000c2d03c013030110341403d0601640e05d0304010301c1e1480030030064000084194051003110b08690030003016102c40d404984045c1e000308109803080c1c092240c100e0b0018002000703210040b016000d101481b000034001e0405015100e405642c07074900808400e010207003c59154282246c2c460100c4010690715084074820802 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 659915836 1250 659914586 659914609
    0x60e0304120f020108180705091902030a09140303250e060d06050108090a0c0b0c0c18190203090613060f0614031915020c21120609090714 61
    0x14203415108181e0104250a042c0b000e459000b644c03801000d86804400585c1c4140045001032a5804010708001c01d0400304c480c558400c01e4401c0c1c02d004500d501035a802642e1084641000c09030752200c1c003004010407103141c184150086030003503045190040e00b00741c2195840b0f2490b00340703002c0380317a071090082c0c8114189d040300b41010b4552901c03401c02404400182800c0d000307243c0401c07207090000c0c4542d00300241500145400c07901c61100c1d00c3c0342c00c8000090fa070112625541c14010400d440c1c0c3c064550040d00000040594440d081e103103020500441c03100760445107001841c1c01082480205540021403e070080c0807444d40c1c0100d4071440c609071008080d0400c025002c02e0600c00c0c0018a070500e2081218901000e80c2920354584072110030421024150750010841403446100c28000c284560240113a4545c840440d0603071414404540c2c0c0c41c00d81040400541c440003c1c000040d0b210401242d504040c045d100160300c4c0c1005a8119100d800071f0244160b40442a800d076011507031440d84102 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 659917086 1250 659915836 659915849
    0xe0301023603060c0f07050a020303120703050c070804090b21010c030b0337080f041e0b040b0d090b0907150e030d12020d0c03050703180807060e0304 66
    0x2a001121034080401c00e10511000500e049214a0400702810007080441c4500c000e40b070b207039140503900110f40645030031101055038144610034100c2c0060304c042001300b0103060307407200c604860302d4049401403c0d034200900c2c0250002003400000c0000d040081690140c810814000c85c0700108540070504e0000b610700204c1c115442c203d61610000310640c0500c6440006139418400c0c072014400703056443c0c1c0110203600700f40d18200018018000341c1354050030010580009460300e51100e8441500581080c101075494400000d8100801980b2105100701409500c280c0340105103070007280e5002c1d008600c20f082580c0400100c221031550143c0c01010142e5006034600a1820007110490740d80402c7e004a144010340c80c808107070003d00a8402c5010248002c0c000e107001c0e94000780841c0c7d203e5070200c400c481c0c80d03000d01605142c14203902070002c2e410603558000480e4604946c00600350b0384115190814030310245030403008600b014041302c3d5150341145010030820125000c2a145100310390140 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 659918336 1250 659917086 659917117
    0x9120f0714030c01082e09051e160818011107060e1e0c2e030e0d1d04020306120304060c060f050106050d0905031e030a050a0203010608070e030102 65
    0xc107484404845605030100e0a030120340001500340015101e148090b80c0700b40d0702840b1012061040665807120b298051007103208000c50f250b03202d00440903258107032a05949a0302002120344000314910903da88040c6244290029020750314014060309000f0303001c801054240008541c1c1304a09401c1100d00b8001901c6179903484000c2c4c1009001845001d052010500a076020200628202c1984920055200018000d0a1122001c0001040808050400d11080003000c0740c02c0b502c1028814184005a440105402c4800300e50319003031502800802c0140440404c500c0c0124039120786261403910305840040c3c0d03940301d410005800c6641a1110034451100140c0400c80315405003541443e07a00c2040140b0150341003402840c20346809001e81e1001450501401d0003441d000d03004000305500807000e50f85880040200d18076a00103180c00c6d0388d08140004180f0a05055500c1031a070320070b100100850440d410009e00904280010f0070310020084078501e0380a482c0e400307504a036154100320800d03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 659919586 1250 659918336 659918339
    0xe07050316090506030703080d0527030a0f08090a0605180a050f010b0a03020906010804060b0402160219030546021c0c0605160b070509120705010509120f07 69
    0x1e216a600c032034040e003034120741010b003c981c0504002500c4001e882c0d10403610ba0400e0b011402070001044003c00749030a0405951280c0c16283c41c0c52561f21900303403101c02031355441400c144003503d510101d0401c00100b01e002010401c1c1160046aa030341c400d076011070301051944400305100d6040c1601619000075028114040017004070001e8907030100c2c0d021900031300503082120101301100c05c5e00e200103900550f00d0000a8444d610071504035078454030030746002480441e02c101003800c9812600c01501120351b16107811042d850500c100011a078400c81c142803a990850740c525866194000703070410700814480e40f480100f43e10101d501c3c1140c8030090011410071805110481e01d03810194160b0161420396103120850782ca14a00100d0a82c1014882c8030359441e006089405601c07072208403122a141d50f450f100001c0824199a0240f91282c1e5103d845c0d0003c0c0c020841c400807a20200c6032154400c00003040b0503600081900c1e107c1c0c9084443d442a41c0300b142c07101d820410344c030200c0d0005006402c030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 659920836 1250 659919586 659919613
    0x140f160905060f03040201020613021f11120d0b04110f2a010501030b070f3009050102040302010e061215040225030f091206020a030b1c020f0d0b04060e070503 70
    0x245205c2c600076030031103c2c0c903107072a0884120030344100c4000c2e4001186185030258805100a000800d80d114600010140c4441020034241380804013494059031b00000c5807040c81c003d601071144800d100711000c101da80165140e04019200b07c0c9090800c161012a11030100d10310003d1043c00740c08800710584c2d0a2640d0300d22940242800d00046841441c11804140c40c070744262034601c030141042d11840002810100c01c40d80ba4086424030400c410720207204412070701c5441c010304103114450800561590700b5440050104450520010b0080070140b15100c02000e041405541101040c1c0c101d001c41e545260104029205d40000e10028030f06500207a0071090700c442c074441405000740e40c0e14a4400503408100d540c4ac606105501c440c074150302e01000451010f60040140c4009410001a2015800d011880402080300c00062031030783c02c10000f0950420305406002c10308216071100303d0b90020360b00c0b00c01444014101419043d922501504e44603001c00c2140081c0c5001811250084071899 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 659922086 1250 659920836 659920867
    0x180b18060307030c0f0603061a3c030105120c030304061d0d050a150b010c02010503100305120c1005010506040e0402120318120a0b04150213030f0204140f16090506 72
    0x2254400084c5010300014427461803008550502e0074a0203d2407610010b0080090300105c503011351600c0d983d251403a8040c0071150405a00310110780400d07680c49600d414100110200840b211603019000505035842a0342c010003107074180e41c030b0b900b0b0000b450100041e84200e0000443c01aa27040a0840b4a80c818424001500f06034144a160b081c0c2c030142c0f440e400301007a0345000d8400c030701048424156000660065001d90380c012502030b140d00ca803079929200d06161589800411f01e805c000044c1c4100c28001c03c0c000000c41baa504101409154500310102c2c201d40309503c2019118440079020030701f15940d2081d02c035102c20703d080440c3d841340e82110310501240080540b182c41070404a42000050701c1c041400e00703c054000c440c00501d507a03182c46a0f90000c4290f0035401101d81d082280340d8003240c1c880d00c0d071307405507000707900d62000c01d8018030500c07013110b01d14207030100e4100c5404100610702500010f065448007010103400043c002160090740e41c1181c40c0c12141d40020040b51140b15a02c1e80e2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 659923336 1250 659922086 659922089
    0x510090209070c170c0309060d0b1201060b090103020a050904060e010f12050604120c0c0e0f0903030f1b04050a030818010504030807110f1009180b18060307030c0f 72
    0x8030741142540d25200020303182600107500091044620603005400011110b000d03010060b80d44058034545024000041d000340d002c1050104031a5036092000700a00301610f05010071001d4034000c2100c10b040ac00b52481a0060001050405400040c1c1691051180341901c0310300102400a009081e252030700030161002c24003070805a6582041300040001907e180035181c20341041c007520031600d440e11049011000198514103004000c11040e00140d44008440018407410701004030074140305200c08983d0f280900a161244e0040c420b00c82c0d2200540e18140d0410020899404450b5459040c02c0b030034005d9038441c50384403001039400400d00c41c408004280002011440c13101124948005540c6c90240f8040500f100509122890005292040110581c0401040f600d40241610f002500d480d1241400300c0000b01019400c00000c80c450f50341944030b0300060005e0007260000804900b07118405c55080589002e480003083d2140c6041c44403002031350b0444200f261254450304440c1e0200c049 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 659924586 1250 659923336 659923339
    0x9050f090d0507150f060f03121e172d010512150a0b0d0b07020a0c08240a020c030309240408041403010e06090109060608070803030106080a0905100902 67
    0x41d0009076020034070072411100c03125030200b00d084000160b802c600d4001c006034070300d4910180d5600c0010a48800c0c0900070310046115040c07161840081400003000204108040700d00c014455290307004568110a45202c840c052040b850b525a84032040b0b150038a081d201d042d015000c0460300d107014a60540510b50581d241541c40c0340002c41400411595400b1040c03456808481180109100c008660000e15186200625000c1c2c01d41c400c0d1107501d00304205440390005a80700c14010001c11411604103070080803801d001c1e011107480920344007007081c40b6516441207640014009200e030140b6070305032440000c000c02101d48928080d011a59a80e11900d001240c16000004e100c140c0300c042200503102c0e6610081a81c00c207441c2c110802c21030001c1071001035055482d405180d52405040000a1040ca212400400c410310f4a00b07001040b140581c020000d10b4004000c24030000b0030010440341107490078070340070641e640c80b011900001d00300b0740300041690003103202c2e1466030061038001c0c0f49000d00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 659925836 1250 659924586 659924593
    0x9010804151d21032805070801180908180307030506070e1809070308070f052505011716140409060e090309030706050313060906050a1d0601050f0a09050f09 69
    0xb940014840f0b840104010f4420208080001800c0081780c80000c1003c811402074020106101c03a200d4000d031078084030780c2d5000499000c01009500212845031245a6404400308403201c1180c40d800b4203403241c5240041c4030940440f440d8019182080b00d10001c5420806541c040d0500310401420100c0b151080341c0b103101008660300e01d640903012618000c40303041d0002e144183c99640d81c1030309030704010b0081d9600340c041c203101004201c0a00c6010f480c1c4060421740d01040200441e1b108140c4001d03080303a810420310307458100f0407001117204190015500480b490040b51406400c494402001e14528001c94000c100020f40501a07000381c420780e85403c64000311079803280c40c0d09a03030f030044100855041d40800c01c1040b285010b0300095400480941c4451050003031a12010180d81d509982262030071707070b1401082020000da106821951100c20741d416a4411810505030340c0b10018000d035032142d0392043c0428641d41c2c4d40b54910009121321001400359140910041e154440708a4503a40a4003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 659927086 1250 659925836 659925853
    0x406030b010801150c020409050d0807110d050304020915060d05062b35090907020a02010c060506211014060d03050c0c0d0507060306051509010804151d 67
    0x180145a41816201010281300d0040c8040070b04403444800640180d8000b9030b10055200400c00c140b0006803090301c02d032180600c88c20410001850a2070200700c4000302d420000302071403c2e941c0031044a40080d0111500c02e81602d54003d000c810344480c2c1c543c154016000030328411040d840d81c20081c441c54085442210344078444504040f840504035000181010030b00b900ba00059403404d800048138050f0040354a1030520b035002c031078001e03140002d190b481400030034900c90500e441c1074038541c84602407015205c01c6910713a0010b40b41000e5402c0090440d6120701c005541c54581c040f24200381f1b102d480413200340550034000652034140300596070104030304280110100301d074000301c428050a005000c00904400585003101d081e003014007034050b94025280354a0455441c019100315450242010b8010645070540103001c8403280e5015900920060200401440f510000da60001c6e80a0801c03940690302d03031518641c0110000d09141c0c03110314103846841c0c442802e4000c0408070b10210100c51034103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 659928336 1250 659927086 659927089
    0x30415051003020f060a09030203120409060b04140d030203090301090b060f0907050306041802120616180b0708091203040612050f01031103151f0501030e070303030c110708030406030b 81
    0x1008503002c00303500100c103206002e519050100040c0341c000064500f0b40142ca4899000a041100b481182c669400001c2000c2c0800e10803449450b000300101071486140c2031038503c0c4502c0043c0101d641c80d00c180c2c1d451080d0400c0c140244100ea192503401402004020003d15156072140c0702036038401d00418010207010790b1030600c003508600803030310b40d16580d003942d8540303080001910003898400c02d03c1d0316080c40040183c6030102c1c400315500d101da01502c00d40c41c20f0039400d6070403074080254808128101c00701c110031010070a170340c1007a00c00e5940310a60b1403000f070410030007501c58107403a9a007101004043d02001c0c030000c005403060315030b641d8030030603510070352019501070b42c0c02900ca0809500c048030040002440d9040948114400a81a1007843d1014818401660f1084502603070004048000d0451306400280100240009090800410603070740500383da10845030100034141540d50100d210510300454850544120b20300494260980340c0714115140c1e0024840c4a011030704203400300e080c6 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 659929586 1250 659928336 659928361
    0xf05061e191205040c092705240f0f04060b190e0703060e2710060e16230c01020d020c0c090123010318031806050c03090f130203041505 60
    0x2e203400109105d9030030f05102c02c01000300029802e00c412141c40500d91520b0b1604c02c2c1441c0407141c0110041c0000603640d00c010141c1e44040300110143c4c010510401900380d03403200c0e0b210f80040751604050100d903181d2812a004120012500da0f00540780c0c502103200e0603c02200c00290b40030103035408560f880c3c1d91030607816542a4050380355400301c40360001d503106004003a42031101d80d080303600c1129038103504c0d0890304040d5084030141e40039803183c0c0c0600c0140d40003a03400344c10080050f410105030310305880051141420700c103000c001942003034a10181800309415a40742e485200001c554800e011841741001754411080340b4298081c051030000c4c00d1401009081c103d8441c1c412510189d02c02007401c51101250355011814165240408504144031000820356644a0b071502c2c1020415260300c40c018041c25070001007042010031420101040100c265050040166a40c5803007101c41c40c0026000e12058030704d40c40d51f6201104000034000940b071080703040101000c0c02c20040d21400b00b40b084 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 659930836 1250 659929586 659929591
    0x50906040203101a060705030f07080c010516081504090203032a010b0f1c1e0b06120309040e070b2107050909010e070e1f0212040f05061e191205 64
    0x2400e800b0b0b031a030340c4c52400c118004040381071040d42640e181002c0e1290300320094000c01000d0340c641c100800c0d14541c0342001d02c40c07903070044404e40781400c0301002104018240ca07801080000c140c100c4d03510a0308e241d1583d030403241c10198003d007600d4440810143c8010101c40480001401030304003044c10044407018442c1d101c6004014080504582c141d0060004500f00b603818560411500d8095401181080100d00c0c2c0c8810300048100709049141028030ba00280905144d10031120000000f18451001040700c2e502e100c26100403841c24402586c090420040e40d1080c1e060303610009109050310412201c2c98210381d042ca410400c942c84154045a5074015080d40b2034008289100621a1814448496500c0141c500c2d00c07201d03140d6602d020418a4020f100440c0404440185100f1003035018480a07011170081c60425041034944072000e80f0f01c040740c1c49028024600041c005111140104020301c0c41010446116602d90454144640a1513807407004400100c801c1c03080d80800070180034250 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 659932086 1250 659930836 659930861
    0x10917070605071401060b0a0e061204120c06020304111215010e1b070f11040e060a050a02130e040b0106081501181509031103030405031c0504030605090604020310 72
    0x421400d140007950b580d07003d40b10503a0700e030820a0b03d01407200f009005c1c070409003250b20100703922208221300103071920103d0350041d8450300051005120800007407410a52041c0c01060700d40d0000314540003526108420a00a80154000002c01c41070003156038640460b46c1064680306040507181818a0f221401d80c400780340c0f0340c2003c0303004203e905115890341e5081100658100f40c0540120a1100035502ca50811076a40c0080103078107060001001d00e03031010174800d4400303004160794030304d0564a40900400344101c05942d5004a04081003982c16034056415600c855072840b91614003060014200f250700720341c07045400c000810318600c913414150189034000d44250310f60b81c4c3e140055444012408030030900c003a1105000035804500034a410f0114425250071004a05504008a50030310840c0c031b00303002c0d5000b0401006035440000e44009a411005589071310030703040e403508039503600c02e0b0340c0007418040c1407c00b4041c0c51140400c0301c9002e284224100c401c24044001c040b001e03203007420b00d1103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 659933336 1250 659932086 659932093
    0x15120e120c06161205071e020d03050108030415270e01210804030308090c040c0e150a1e031b030c080a0b240d05011202130608100b0f03010603060b010917 68
    0x32500c3e0003641109030410350604098047d401c11100440ea1503100360103120059000300b003502c030001c1c1c051107400d0240a010300a140340c281002178038a003c109680c18001000741251a11020100803000107100c42012004080c0341c560358510301c0040c54003030094010038111308080080200c400020108060b901070075150409143d600d00341c6d03010b1402400f048a5024002d03014848d40c4d61441043d29048542c0c44141480800c4000c2c01a0503180820703640e0005801c00c810007801da0440e41406200c600c2c0c8844281c2004460030840280ca00009440301801520390791400168054002d0300c10840c0c946d42e180c0c450317606d481462080e81c0c20101081d4000a002880c20060b80f000340c0c4c3c404c600b182d10b000183c907010704124164118ac0c401d9211070400500841c54404600e06040f60389620603805400b80030b41810024a2515076012800c201070035540d44034040300f50b4943c041d494142c590005c008106003562030808002070141d0407000b90000e00200400301e46601e0283c841c0c0442044034004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 659934586 1250 659933336 659933357
    0x30d0e33011a1204200d05101104090609060504050f19050603010207050a0b0f06010c2111060703060f0f0f03020d0327050301060f15120e120c0616 65
    0x4080b81e5014407841c107260100401c910000f610300314850314021807064181c0c010f0034440c80d01d84d1420b43c1c0c0c100000d510a1385030150400204800140b02c441c8a81002e400140716403884413240328520482e030241c18031605002000407101da0941c0490200c1700c040e034051180303075924906a455403604031407c140200201c0c8003051050030b2035015035402130300031f0001450704005498a41ca0300c6940c441c21504014004204a4068000456150080001c0c04c00039a020b0b026910b400300d01c000304d1783c0c1c2c2d440d500a0681d41c1e0960b621416510182c0e00c1f0b890b05990341824804002000341145000d104180318034a680050152244148072080310211221000828155820040d2010003542c080d010880781c11807071004500c00c80542280442d580c1115207210385085d081c18203482e55540442104505000200081c480f0466a000700c030940389400380b40c1240c400003200081c8000c0400c81d0782031050400c003604403615040100010100403080b50301d0f0f0b680b02c88403200c400c0c1806222a0002c1c804c0c801 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 659935836 1250 659934586 659934599
    0x60313030804020a0f03140d0201050402012a0804060509040507020c010c02091e010e0a1803090608070306080d020d021902030a020d170f120f0405120a02030d0e3301 73
    0x725005480180340348880d03581c45000040310f425542080d5461840c40142c4002c1c2e038401c116000c005800b5000901591601c2c2d000a050007030100d82c808000f0060014044840441103010700449500400e5603888540340d4400600903000307840c2c1e07540100d04c0c260100f00c0050000440a021800594410340c00030200d900307204000310b002c2e2201030504021b0001013584010560914043e00c4406507101c845c0c6444480786023079506030002d0700724401c5007a0070f94000c01c0d4400d206405035070403820450142e80765414110000e11407644083c0d140d0243d071384400140d6901041d14a400c011941c00c40700d03103d03802d03140c030401e1110120000f94550710150901e40141410320303200c080c0c180141054007500b540d400c220202070340304038160389000c1c80000310a2003940780340c0c0920b0340080307181071454950314050395526550840513950042c1043c0200d40410254400c104a81d841d40300300909011b880b041c0100f05640703c08040c00454403d0940c6015200d6070040d4005244600708690f1007051a403a061 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 659937086 1250 659935836 659935847
    0x5060a27090807030c02010206010902030103151a0d051b060f0306040b13090507031a240a0909080702091608150d0803040b060a05030f1c030612050105041106031303 73
    0x80c0409140c031110301d24081040c4030b0280c55664000d483e007110f091020b2000909002e81600b0410300d540c1b040c030040c400302d09240ca01c19408c881da190300191501c1e81121000c24014410400e075031000410780345004000e404a101c09034100a0708441c040001c4000030020280035440d0320b5020303040306200080b26880d144d08000c0401e54080d000c10848981c00c141d02054400d002d00c1583c041d03101003c10030801c40080d40c8904c9914408030100c0e00f60a000c4204409514280c44441c0e000d036016a04400958400010500510a40c0303020003c3c0078503031610303580d250098001680b062640f0400169080caa00d0300c524040c54071070307540f0341d03041c0e44502840480b80c0c3c82c0300c03419400660b0718205400044114004601030707402120310080f580382c03000070480d107481c030754102a000350001c182100810707100094080c040580030303c80c00c0b01180d00b40400c400070b01c1198028200320f015a40c0304000d1040c10340c801e40c020360007580e040c181e82140e202444020700c0199040032a80440d50a0030740840d1181 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 659938336 1250 659937086 659937149
    0xc05180f0a440a06150b0d05010e0915040b04050102070b180f0106061706040e0a121704080a0809010f0213091b0e060c010f15060305060a 61
    0x81c8102221078907840700c0340d0140100c0300d01106004400d1145101020080001125692240203190b142c400c2d0078419900c504140c500186a1a05c40d007000340142e01002d000fa02a0100e4001507807209980c02070203000d000700b803064100b100d4000001c10203504001c03c0d440429241ea104585054940f43e8038103021480081064829550a20210000480c14056a4010600030710640300d0010910031031400c0c0b8010342c001c8000d0340c0c5032a10800c03201c0d4000f101500d10341041008000e2954400000c10007a110040c000f170620701842c401e400401112103101d03030a044450340e6450180c01c0c0010000c603950016600a0100d01e01481046d00682c0b00d89610b41d88002a8800030691341d4030b001ca25001c0c0c2c0c105610b4404800101d080c20b200003481845140c100050302c4203a2203181c01c1d0b40401504801c0c8004100740110350000e480f0a100809401a020300070044008014122030b28541c0f850285142c0078540010741441c001c42c00030b240413104403054544180d030282c0e500f42003800903441d01c50301 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 659939586 1250 659938336 659938339
    0xc090f0906040212010f1a0319050d0f02010b0d0b1008060403021c030902330301140411120a092906040e010603020909070806071e0c030c020d05010902040c05180f 72
    0x261003025046d868180034000320200c4907001d4007042d4400e1020507003810500180041010382103080364000c25400139284c84100070508106c1d512041040d03049000d000c241f04400c1e081080e02d20034004000070740d460346104100b03140b0200003254403807080d0364035507005650180c016405090f5429654100a4015403240002d0500180c094178950100d100112071488100620714000c2140280fa40d00303d01d000d0710b0303004050f40d80b4a551305203183c180d0402d0301742100030300031665600740c012103c4c42c800499060035101032142c00f4901d4000d4015000e48220142118003103194070000024094900b8004126a10201020602e9440a09100062500d4010344d54a503403a403030004090303100c6d07038442805580d03c0006443c00030300303000f000c070b1030810090010b41c208450081e500c04180c1d091003004030b20007203d2802045041c41814100d410512000c00a036201c003e00c49400c0400405502014449100303617028804500d19513010b8a49005021403035840c0000c1182040940c40c2c09840c0500d900c10 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 659940836 1250 659939586 659939591
    0x90105040519080c0f03070b071407090606090911030a050615040311030106080d08040318210201030c092720070308010b0a050a0806040e010e0c090f090604021201 72
    0x581c0d0001030814458030071200d02031442d585051115000600690490003c103442075a590008440825502c2c4900d1080e490848000708200040024840003880c88031488421a00d0058455a5020041000782700300808500070040c0010046202e0041e0300c05074010201460550b601c07032201401420004103401e82c84031003001134466802070030300548051400b0368291400c00782c4400a160844a007a0801d06442c0c0c065000c0080269000f03402076072095162070710070001d503007072090001c0450040d000b07000c1180782e80701d800001451001201c84554001da03410310408460a0041c1c4002d01c45000c1e44070004400041240110101c8400c9120304420000000c0d0f15054240e070036071144c015101010381c100b000030303c80041c10361001480c3c3c05411586c524610300601040d000d00148540228ad800348a0560001001a80c0302d80c80320b110009207000074000456240003090700d4108200d01184940c01500114035040a11a4600d2044003181c0060106448a07020000c124502c410600300725134 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 659942086 1250 659940836 659940839
    0x110d0f0f0f030929060613030201050a02010207061404120f022a0d0b0f0a051509060d17040602010c080c0d09082209060801090c03060b030705040912030b06160809010504 75
    0x42240038021080000c0c4c50b0507800340003003506130801c0868058003d40c46140b050140b540074500b02000401242e0342403d105641e401b5018040c4e0182c00354200c0580214504040d000b240310300c44548038411841501e0000388000c000742d003507540817942d00b901070040c0d008135032441e202c10103501da200702e0410001200007280d1070ba100003012a420000700322440c0d40b500c000d200d040b42104031200c1e00f022000c1c10501c164078003001c8010107401911405031113560907001091460b140c2c92911240e0ba9000704602c441501b044444911540c8280b0032800103620f800100d0301b005120390891b40c05601c540d44094509402c10380c012001e09840c0400381d81d4078000b0880c00d900311151868070150300301d00618103c2607a2400800c0c20403a441c90348004c506906040d61100001e10300c400c1d1405980d48280009103041030704021030b14052072a0899034002c1e142c20040d9041c0262075049406880860f5818080e040d1008203004541c00b42d811115964007940115500280c04040a0845014180740180c28a03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 659943336 1250 659942086 659942093
    0x703022b0f020c0109020f0a120201120209131a011106010902030a020c0d020d0201150501081306110a03020c060c04080304030b1308070f02180105130513050706110d0f0f0f0309 78
    0xd83c80040e0b0f04400e60b5603520f81e0811420030349a020380514044507011003052404140005040240c64024104070b12018041c03518800303981a01e59589003d0860954172052503220b900134000b1100490b241c2e510301c1200340306036105441144c040621103016000c3c61b440d0286c61006900702138483c502e070765000c9c4500014403804100e10b803035101c9264002d08051424050103405c554945080768568450090144820b0740c21500d840c1e0003000c96503107031541c90750711305040000b001180b40102c2c0346000054000c6c881641134010300741c110030010681d40710fa00c40c40b060408510640c82507500715081030004001003400c1d000c2d1140c3c48032030303030321031010034402a900c1e80d44c01d41c0b010004890005400101d081982031a0340e40100300200004105500d50524000601d100038041280004586520000340c107440c507899640c107215413282c1102c4406803a0311026000150440c0c00501078826008000303031061140c0710320880d0b007402d0740307c2c0e00c1448410340c03003120981565a140700a0648403035020002 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 659944586 1250 659943336 659943341
    0x11d030a03120e062509090c200606090c07030e0a0f030302060907030c090e0c1f080a110a030b0616060203090c01020a02090a020913060801140703022b0f 68
    0x2061180e600c00c403010740c0c0341240c80103d445120a40c42c160784040100003000034603190040d6a139218001144d80c04c484100220f62818158000c805040d007007105180b00107400c0603007082000b41c41e40301d540300d50840c0c0c01050b07641c1004440e619400030104000c6190700445c0302c0200b59581c06403400482c64540a00405e0b4150025403120144018450040003456814011941c00c1014500a040d090385961290a4154024020002202c0d80c2d685c030106602810881c00320200805000c80e031401800c6104107130035441150341c110204410100099401d5100d01c645182c1070752505115080c07015184088006018500310550000010819100584003070350750700c82402e00c1440003590320300c3e06900190900d5403e080301d605551002a03542c0c01641c480070040c0e40715409010040e101c4411200090111684403081501107141200c0403c008006401c14810300b4103030000641e064403518400c070200d1148126180070b0060220b8070401c0510000250311104805c01c0b03022401c0b01e00f81c00c0c001d04 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 659945836 1250 659944586 659944603
    0x90703060908030402120d020a1b23100f0503270102120106020f0f070e0603071a0d0501060504150c02030f2a061306030507210b12010c05040302011d03 67
    0x74041d601008100440c9440c1c0706c1c0f15009602ca03009400c060605000280d034540d444500200b8060907008040c444040560100000303020034030351545441c14040740710b440d0400101c20103008400c2020110340c2c1a00614681400343e0a41da80c1030325540d80e0170b4090a81c00340c001c4c025142d144003991a00c0c400d550900143c001404041075100703c951410030007038030b40b1580002c0107440303800000c19003014042c0802c104007107501d84580c2c2c0c2e01c190340310000603007041c400e40c020b201c0c60310460024110718410394000d404150640300c810007a0380d0700c4601c2130310b150149106050003008601000c40310244200c3c0c04400e81da10180407100e41294041c046401c01c82121140105419103440c0750440d00b030498840b440f14401600c80918120860343c103c10000b003940a4601855250008102c1c21032140c281008128070102020340046400314003c40580903150803184242000046071a0018062080e1000b0000303030303101c1034500352655006640480d6152420b002c00c040304d0302c10a0440d10140408003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 659947086 1250 659945836 659945843
    0x7091a100503090105060406050f010e0d0803070203031009050105130f060b0f07051203070806100207030f080306090a060501050a1803060501030f0312090c03020d023d21050907030609 81
    0x81c2c482c03500325107290848000800180c8190f0500404000366210092104162802880c003132001050440100d07400e0121004e00401c090000010000c2c4650b001c00510f0040b902c82d0b07803c0c0e8885030740c0d408240a641c0c0c00c0c010258400b0301c0c8400100500304a60040c0b0740e00b40b010320017142013540c1c1d0f1001182038004410300ba110240015442040000611454600c1e00c854060f26080d420407000091204000928460041042030502da4045000304010401140d1150442d15a00000c2ca008040740e00141c0309180688551070100c1c0c140805405103400350740c0180d48a90800300820710840705003d03041124484442520404030118042b40551406103000e8500340d15071003402e1030700274880d195030740344c2440480c42e060b901800a070001e05808200c9404036404021074030103000181c10b5512501011208510101c12056000c1000d405140c20841249519801e014041000d540c10704c0c401100019505407200a40800703001580250b0b0005082412940201d44903560300c011240301c40c03000d9 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 659948336 1250 659947086 659947097
    0x110f102309070503071e0e040f0803133e0a080a08071e11060322050706080901020403030e06070c0b16150e0c09061f05030402040507030b0307091a10 66
    0x3e01c01800d007040030380001d04c01001c1c0b402c0c0c014262040d50180c5152030041c0d000d48001e203000309040c4401c040d54208403507040400c843e0b882c02d152500c00c544002c2560308541c3c001c4460706e008030141c4641181c40d6140c401c0481303160055a1600101003c80c03640c11615403002c05120702043c0340c1c1d0100042101a403081d10035542d0340072a410f060421000032840f6201100000c01c05000050300c41d00c541d84000301c2500c0700c6480791103041d550f614076030860380031036150b080c066502c2041c4440007841c00101d130305a444042e415214040c08909034802d0303000180124447e010a10300300d0030b000005001c0030f40075a05804080c0d441d070401108035031020304a11102c45103100c056040c0011070002c44d000302c0381e4050411880b0504204079840c1e100164056102d0280d8000150450300e46818a852000e0285e20400b0701c6001e8410107000754106503416802185400000380d00342c0e02903c038941100a0041c002c0103c127240001d42005001c8014411181c510389000f03ca0250300e4410340c41503c817407140c848 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 659949586 1250 659948336 659948339
    0x15010305070e0403140c0703140a02091803070b0c0403020406032f09010b1c0203010b0705100c0c0b04080408060a02090102010e010911010315050901060f110f10230907 74
    0x85241c144541c10407450000203805020029401a00d04004a520307141c81c6501c41d01c011012a080c68410343c070281107045c01000700111014082910000d2901c00c071208025a207410344030b204900c8e104401c1c2010303540104202e001180244071095031201c09202514501510396000c10709441c8507a004a480032440303104e080301c1204803090b0000c0070880680c40244404044001501000e0610a580400d1000100509186441c021040045220750f00955417943d644c03592101030350050b50240d51501406c80040f645414074050f0303076500403032582c4508880300c0310380f2460507808024104841881c003c0000041c8040d051044a2040c45084001601c600080c8006801d60341c0c0d11061076143d034508181c041c0000d4080450002d05002803a00059180c0b6181d080c050f403801c25000785604c0700d0124000190303030f40d00c41d03164500c803601070343c50303000c110884505280e13101103084500403280c000405080c4d040c11140d00c0002540c680e00d00b6030f81c80020107411200b4541c070544000f034040d00318160 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 659950836 1250 659949586 659949593
    0x8010c0206160c02010f08060402070f0510060603020c0c09060d060f0b09011205070902030711070806150a0b041e05040507180b090a0510030b09190f0b0315060a08150103 75
    0xb102e0103480c680703042084240110f0f9000070720f03940100820200380440700000c90342c40e072541c0c2e040d00d14490b0303c05c00705da01c42e9500b070510700e9807400325100c030303d400341d090540108145200b8002d03514130300c5142c002001804000300400c42850002810150450b1810048130041a00c6000b0701d140c07501006000608948041c052004d1214140c00c0381c150524594555000140c00044d0141228000b50380140c40352100601240c00700c03210b00d504c0b0454419035002240e0202d0105010f8011030102d071100040700440401e00551649c0b501c200d00c44010140010440c140382c40d8015205490450316820300340b91140002011a80e09403020000a1a40304003e003083e204a9440805411009281c60820304000300103401d01c5d1280c001c1d140a02400341c15216030a0083e004242818401001c0d04400c0c64031000307540719140040b00c05100c3c20b091041a00880b8000d21070000c45040180240503980520075507400e076444c02a0045420400807140080c00c050140030640c80b0310104e0790b04100651440c103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 659952086 1250 659950836 659950861
    0x15033711241207020c0a03060b03010f0c050d09020613060c020102100e0d050912010c18050105040f12020d0b1f1406031902090607060209030105090109080405060f0408010c0206 78
    0x41c69000911641c018003000c420007242038072941c64501042c1c0c10b5560700e41d2012070900700c48154164100102e51804810032090390802444100160b0003040390038001e41d000e03001d54000d0810600491402c0000c0d88504079a038001540f21070024000c01c0c035010f807218604d1195803035a403001000035021101c070801c66a061003c45040008070306c09000880c0c0b00c00c1a69240c2144000c44010b00074005804041038a50a0b003548002e11100000c0000c029031901c041c0500080040003049503415240100c1d0641c0100d0a840a031105180446040c1d41400c5242484034048001aa40560702c4001000020707240800184200700480009001d6001807001c1413418269400c001215250f00c58042c0c00794995070300f0360b0382c09102c418103504210110442003000b03100f02456290000e400258210074020560000c20804400360002c020750307990100740c14204d56801100030525001080704100c6842c00c0310140192402e880d400038685540c0308025805c68031000c01300809a0042002c12185c0100c07207 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 659953336 1250 659952086 659952109
    0x30d0e011e0933110c0910150e030a03030b0102070b0c060c0304060b10260f1f170604230a080a14130e010b030c03130c03081c0515033711 61
    0x151b401c2a400d0810041c4a4603400d101e005903549440d85120514200388600c40c10300354107401809a83d042981c074140140130300214121b5901620400300c0005092007600100c4803020961005040c480d1180c11500b00940e102510549009440b03060b030380d0319a0b880c0c21103200482200d0304d80707040096100c498a81c4160030122070355031a428802c100043c2c0004488030300d502818459401c90003075102070700700c0201c5000b500501980480c1c16002c0748a02000103403a03010342e0185a0fa1000078407221422800002c4024043d00c043e00110074580011300e1840c09000c0c4140681441c10800d948051701011580058914a082c0c42000390304200307049000711120b001d4501c00c10458590310304020306562a10014244008200e030407891442400744007020880078550144489075071325100301e14500c00c909048080c0390308902e020081182161500c0d00e84580e840302a01420041c0080b8400960241600c0302607002c0c1c404c1507010110b01a201c01140c000f03148070b080e0240010001206001800251 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 659954586 1250 659953336 659953339
    0x150a031b0302160f02010c050a08071109060d0212030d15090b030f0a0b0c0d05090105100501020c2214091f0c050403081602030d0e011e0933110c 64
    0x108608032508030070030383e0024120f410007500c1c1403c009a200480e003040401c0c80181490094450281c20030103d50001c003030702d5005052042401c1180300070461440410359100d03521182c10f090000040c101a07548180007140d06090b6824400c07500030000548142c5040d4906512105e04148806106441506008441640101020810080303016643d260440015003250341d2880010020701c440021203007000e100d100c0601503800c007621486d010300b900791152000405891404125940300268845407600300500d00e03400341c2456003074801041c039003e8071003600545991440c2590102d105406010302100750081002040e0219407601b45030204240c4030206007440c40840c9101d03402003c1d40e0680b034200301c07a070399609003c084401c102041814029094000e5000c80c0d100c89400000341070f0036907404e03210107540b0700e500d0013500ea40d11040040c03070002c1000100d091003105041c2c003030126800541001e5402842c610309202110300441264940051541111609095402d02038001407200 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 659955836 1250 659954586 659954591
    0x40b0d141e0109110904060e16060e0411030c0c070f0f03051b06030a1d060a1d010203090a141608030d0614100e0f0a0807080118080a030b150a031b03 66
    0x41a82d20f0803059806180013a100c3d068140101d020703c113240c0c0c050041c00c6d510504440b107000541d41c500c4541d08441c41140c000c104c20941d03d250a00f41405419011803500c2406451a80d940368126044d8002c181c0c0009188030f880000701c0d1030319a09041c40050281441c6ca00101032039031070130f640781842040c00b02c100c108550b01004a01e031290000c0e0b80e0000c000d6000401c070010400003582446da440002d4540c284142c2c4140b0544000e40c0c0d20091042c0c04001e011484603543d8401a400e0744000c1e18030701c030711740d001c2c1440d00c0c00301c1c01d10180104065000c00a60300707003429561150100303c0707140e001040190000100d44441c12802c0c4651002403102c02c604104210031100001e4611000b0302280e4140502c000035030517955103100c15448500d00c0100400c107410741342c03816607680e04000d0280340ca0640c13030154010b414407601c040c0e48a0041d80b0401040c50140022000c40c007824141c181e04d81c00002000c1c2c00f010042c1100094103070f66100741c1d000a58180c900840d5004622404110014180f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 659957086 1250 659955836 659955851
    0x31905070308060f011106071206120804120f02060403080903011803020607030c0201020910090801140c0715020d050c0d11090312090307091e050106031505040b0d141e01 75
    0x80c1c1154909a00c80f20844108229500400041e03a80d002d00c10f03c14015801104100038480744c01201e083c00f00d0284250401c0034507120f5500d0030540b078624001500c0d441c03042c40100504040300c140341d41c46e00d00c5407500c01c2c0c103170703541d607012407100e4000d034000f1a402040803c807600d09007824410381c081000d804003082d40c0e000307003610082d45803000a484001050740303d4080c901424001d404940c0c924101030800d0034940180d000041c00c8002901030440507508084100e0b540006d140c0c00c0ca4001c414400038503213403600c0d540c0ea0085403080302249405036038080c0010a0181b41501c01c032031080c03800c2503030b4554500a41400c0e00455080030b01e000700003002031183c808c040d1400140a018450201007590762154000002071400c2c52941c000d8280d603041c28544034001c00c2ca146101102201c6440a01c0180d0701d9a8080c3c0544482c0110903006600c3c0d040c04200310700d495007048072054006050a40c041c402c0351541056404154499241680302c1c500802c120000e83c0070142101030010000c20030030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 659958336 1250 659957086 659957093
    0x221060405040f020405091e0a0201140f030c0714070b030f16020607030b1909020a0f02030a020d032d02030105130506090403030518030703080a050612060402060a05070501090503190507 82
    0x4200f44000640901d80d108001888007100300f0229940705a070070100c850030f100b510032065440c0000e0b80c0c101e0000f0310b0758109100040002050f201c2180c6000f006a041d0740d9041040100e40c0c01c440003d03a965109080b200c51440c000b88007000c05044034071503941d9a0702d0319491502c4c227480c001d03141410710a401384a032580d5079808140560071049928000c144a42c0300c4c0300040c1c01c032040304400d1200c0000c4200019550310154006e0106680340c0d15070b120f0b044c1100009980782d01443c1030400247e0082d804e03c01d80c0038842c5d404940011058002d0140c1089581d403110f903813122582040c3c40c4c00b54000014440c41c64000494010340c82c110b10706014500e401d4000c80c2070a40040c2009041c0350701e0f40003041d07042d04d807249842c0c03e4124000459031a00300c6820b00400d00c04080d81c56808192a0001240042c1002407070f046010002c90000c059a4450b0760078800c440e84010310810400c00140400307400a403080c014262082e015000031030710b03078000e0111030310a2014a1400000d00074104030804c0007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 659959586 1250 659958336 659958353
    0x60203030402010f12090203061303081b0301030201030c030e0a050a0b0c040f09090f080a0206010302010905180f1b040b0408100b100e010e06030a0911030303010617040203030904022106040504 85
    0x8038031615218000b0070850b070114000d4000d030031b0020341c580070307810130840c004c40d203a2109500c041c065039a5410329160a180341145003008006440c140308100b0050001d54082d80003985607520301d00c2e000a041035146585420403520b060211042e070800016802132020003e040d40d081500d041c602840c040c035000005c0e80c00c80c128454026080c1d04c9100c14028440d001d4140400c89800c03d80c000d0751f070304c80c50500948a03142404120f0108044140c0031445061010301030b15485032418984000c0c2d01c5030100d0b03580c81c280c000e054a21400f00c01c18841064031120300a00700500412000a440f1380c10500c0c2c0030305051441c5400d098141c90488142850742d24862071094600382414150311200003140102c0e1407032195950603400010000a2080500c0300c0d034808000d0b0b6014410f44040701c01100e080540b24402032040d0000920780d0480d0b10300145130100196001403008049a10b8089810081b40a9802440f4060302c06000a050800d82b276511502d2380b580004c045130104400e103400d560740e0b070701d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 659960836 1250 659959586 659959607
    0x31a1e0105060409110409050f01080105090d0e12011b030903020c060c03040e041502040b070311010c0f03110714030909010f031205091801030b0613090c051210060b1306020303040201 81
    0x81c0303a81c85071120101c2045ca00100d401920b43d2400c14015882d1403840400c8005080c41140c050350702c0c0c140010351020010800c950042d48641c3e800c050181540c04000880b9551514100d06569824250340c92070310036180d061008106403070200e498402414041e042104038203041e80542400c2150395003080000c0112030540700108081c207000d858030f09055001e840030382e108100a034400180030071400300302c40c06000d41900c26a19940400401c3c05c9860980d031449440e600412045004910403d0083e0841e41c00c841c10300301da032400c20781540c0307560058095144990481d0741000965070f889080524146015203000c401c05194980345a41c0c0a0109004554030410440003107440031041d034400c029071071125242107031110030f541c407818612a905000e03102144604e000400466504045014201c9030f581c001c1040c04031149000c06001804100c8030504140d405005d50700340200d0058490030740a04405a00c03036481d05c164900113007124000d6040a0b0940d0b01c14420000141e078088590034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 659962086 1250 659960836 659960849
    0x3011b02010c091202060a0219050102180f0108011811070b0709060908060f06012001290607170f190206010b07150c02030d020d02220f0915031a1e01050604 69
    0x7d90701d0320210ba00f241043c024140c030000400d00a0740340780500030b054001d01140040305d4800c25040d030003003040000c2070080054003404a071804004001c85126045040640e240b04940030075000c3c0018415601e541c49404100d032481448400d102400303600c00e514002505c40b40c2482c0c0b070b24034149452a5900c0b10002c0c44210100303210f000246083c0d02c5a8000390b801100c010400072810803241320940038009455000108a03001c0140f0040c201160442c808140000341015140c184c03030740c44103944880003076044029008100180d41044203042d00502c00541000c5200040d0848a08000d084c0740061b403100789000ca0901c0000041100e0f480c002190790008400003c01440c0d5503000d9003140180225200310620220302e0740c05442c40c60f00140880803403001042c0c014001e451039920315070513074007400e070a0a0341c220062000f80d9080c1e211000e05003200a00c512240e80c2e030781e100c03d403940120040312046030b1b0020a0218036006201ea01c041c500c05030342c0c900c0b183c2d8104008500c86008512484 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 659963336 1250 659962086 659962099
    0x10908030d0b03120c150a1a040f020915030403032003011203021002040f0603050604060e04120e1f0f0c12050714030a05090310060303021f0b03011b02010c091202 72
    0x80d0641d002c01c0f8404086035000d0904e52907041164200d40c07149070b100480256099102e00203418100a481075503003080c00c003041c441300740d601a810b01004041a01e07000c41c945034200141c4009a4a8402e00c01403500960225996850a4079005040e5a0b43d540700c000c070814280072880c00c50342c5420a9a041d680385001c0401c80d401031f4101249084c80c039102e819142d91001a0205100c05c201c615902a03c1460f11300340400e442c1c200c00e00089460500c0796400c040c08100100300007071403900300c00803941500c0ca001d80d00c40d0034180005196409a96440e0760f82074280025068880d084007290b4117200141c203040d51079201c184c4460a4041046445804000c0d0008800b0100203c10341e002001e06410421a61035804110002c1d041d80d000103c3c00788244507581c2c1d001c140e040b460082201342c80d81070b4040c0c400c482c00f4828080b01ca02d2822142d00d1a2a21070b411070716103450902c529803092002070800eaa00200601c006401c40700c0030a0204200908200d0a10040310a512803498075030381a00d54 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 659964586 1250 659963336 659963351
    0x718090e030406260c07050114070801090b0d0b070f1806090513092310060e101a040e180a0605100902070314030c0403020315060112020930030d1406010908030d 71
    0x13223401000071100c0c1ea183c030040d890034040350f40e84c010115416210240e0b001c21102e40c03044204641d00b0a60f110040950300c06500003804588903c1901c82c00e41c02904000c0c1c03400003241928503c0c110160483c030009480d0060410540c1380880c0b01007840e03070383d8850070061110309031100001024403845404041c10340c080c9400128104000308a0304030f5042000b0440652144107002e403800055603124a5503020190116044109045075100d40d018031091919207840c0201c0c040243d0070060540081e00e1034200201c201800a00c010514030f489100009440d29051500040001480c1c001100d00d501c18010440040d40140101e0303000e11440d0311803a101d540381401c5070302510440c0c10094042c0140d1190b100d100d00381001d054012217003600c4207a15078038401c04c180124091a5805070388010501450151000302d4245040c02c11050008805401c4442e60302c0d51456000708414868680e484841c0e002d90110545d1450300410240f0300394424910b0a09110f0750780c05503148007101c69948064 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 659965836 1250 659964586 659964593
    0x50a06021015051504052115070e100201020c070b090f040906090c030302060a110310051011010c1115010e0118150308030405060702010c05030718090e030406260c07 73
    0x400200401404070200d03080e03000ca0340c4d00c41d82084c4940d03400b440c5008003024140e1155840384000f42031b450b0050211301003404803440301000140c005018848800021400307600ca810741901021501c0d00056030703038040851140d2030040c0f2030b8000c104041d000c1c0203c0300c0c0350355407100c607080425003100c0c0810307a4107450414900030300b0b40311001409905c0150000041580115a952113188580c0b0200705038111520418660300c8100c91060803003040b00741c240001e140c54030502d900c5140700c0c5040302d018881c0541e11801c40b090021000d020881d440ea0501c000e5030304100c515400c0740a912a85440d500d0800100355a4106005a0071102c8151b0440c010300885544200103140c2040783e0070710203603540d04088080750b10540382605c45004a400066413a8014011030101c0340203559024a0b540e100c1400b00c852100c0d81d00c481c056030300007400000e0a00418003030009150f000c07101640c1d94501d851400381050310328200c41100d20400b00304e01a0030010050089601181601d00e80f0b0ba07854803440c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 659967086 1250 659965836 659965871
    0x20c2805060c0606010909020403020d1403130e101d0f06010c0b040c091127030a0c0807170d02030a03020f0c030a111e06060f240a0306050a060210 65
    0x8000503003020000ca01840400b00009586000761300c00e0301c98910307007615461408240d2040b40400b94000300c85a1168000445080f50110001c10380400d80c3d06088005c2d800080304c502c81e074000c0b8898070909050110480c4030046080042580d20384021011404e0100c042d050038004001d10618004d0b4000605240d01a050150201e0b034000c00705580e501e068030b001c0000c042c1e503015161401b898204030441c10314800c01121407003403101030142500794107212116410306040d4030103909800382005680c000b030b8100c60340101505050010704070a42c01c11000300e000c946540c1141243e40c0c041800d502c0e00980100845401460502c1d0169039403d03103212203a03045c8951001c01240b0310001841c0c440c4182d00042e520959200d25041e80d8038200031701c0c0c0c0180704244007119012030741c11040202d00d1301d180180c40904c03d814040c0880082107140c6085944000d010840c44488603800258007410075894451040903004c225000001c00c1d003801d000a603583d98007000010081d035510340c02c200103045070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 659968336 1250 659967086 659967089
    0xb0610090e06361008060a1505060f0c12070c060e041401080625050f0304110409030c05070501020a0b2818030912020603060d0f12170601020c28 64
    0x314019400010070004296a43d9902c0c0c500c01c8144119003c1040300003070080c4801210246001000b8a8484030400d000804d810905c090070455580341c00291615950043c0001e941c156030500d0300e0340170100700380703081c1941803a00c80351600301080710f007000404840703101098038418075005071420006c401240041800c4140391124040c1d070800000c940c007000600c6031241c0742d0343c010041d841d5104503c550401000303100c0b84010960034050301c0d004000d0320b005940d120b8000c2d02c045003110501408141120400c06081c0c000440c1c170700ba9030040c03140800a500040c0820320040416094640f41d4105100c00a4441210302003801100002100802e150851b000c95010082104140801c8089250000b83e403013100840c0d048034000507240c0c01c00e0020301c1004d4002e005203103141d6032101040720444d01c0000484039000c000072028080354004030504081900c60301e900c00c8141100e12403440041000307110504640c849102c4041549441c06401b508403004042080c459000b0300c001d15101030759 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 659969586 1250 659968336 659968369
    0x307020f030d0501081510050d0201031b08180a030c0f060b10020c12060f0103020402070206251a130b13050a1a090601080a150b060d06030b0610090e06 67
    0x440c6800076071402e40d100d24100d62038401141c0d80202040c80d00c2d000d690040340c0e0302d82d080010346400c01142c1007106098407910310501d00002c00c0c0940da000401c15540c4420708400182c2c050742000b46510040480c0441c060411f0000c203502c0b0400c0d50300501d54124510000e04407151144a00108640382d001070740301503030040502038461410b4000950b61040c05030228410200c120304940f0b01c1c00c0106210303011f40384030310000245a08640910029501c054001c07600305a04200c400f4800680e51040400c4002c801c5002e1761aa4280c1451080c4a01e10548240b4280401c820b0051010214195036411540020041d01a075280c1c041c6c028000d40028028200380180c00782401044040074105100c01407480081c1c025031181e070b4125550700e40c00d0081d4071003036211040d10804610311007195990a140240d003c078150b0080000306200703412100b4003032051629120305108200030701010991100342030343c01d1444409000c100078403c000700e10130109031000300c0340400c805072207052020302076241 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 659970836 1250 659969586 659969593
    0x1806010806094b061503060a090512030606130909031205070e12030409020f03040b09010504080706110405061602120c0d20060a1106072d0c0510150b0f030103080307020f 75
    0x8000d8076600c805d00d282e0302c45511030301840700050520a550300c100c21490703412900402d00100254081c0455074400340c0070a43c440c0051080c80c8911213903261503c0a8680c00c01c0100e1048124035000d00040541c130202d01c1c2560403c3c0070030440c1c903032101103600b050504940000c298402441d6242c19840345401503081c041c0001000701401d0560002507002e680b14140d0780c11181e54100c81d203400ca92003030f6001001800200003a1022403072a420003004100c080d06d42e240703820f42d90310000340742d540146003012620314042411400e61804808524810300101c0151113400070610010707014002e1000c00910010700180e880441207440b09000311400409450259203400d0150003410360444032220031481d22550002580241c86900c142510300b0340c0c8401040c140d020010480003d08a001c070080801c6003a00141d07010410800c00401d001d50644000181c4641c2c4001d000b4554240b0f401c01a6400000c110b085c0c50a0322078801c40703045940007040315032240c541e2001241400d41402c560780301840b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 659972086 1250 659970836 659970841
    0x50909060406031b1a0403020f13150617090115120c08030307030608060a020f090609031c050a0306060810031119030503030f070f02151806010806094b06 68
    0x20b0500302c003020b40e01c1130000c000f01445507401171046403261740002900025078030840816402c00800031213003641604030201c0d03140c1800315510001e960551125000174214030190804604403955a80c002070504001c0c00001d613142500c0c2601c03401c1d4820030f0803403030803c00301000340040901c0c4071020301031440549a82c5e08100b1002009010a030151800c94003690000ca45880c03001e1003112890044001980d003402c14540800407203404c0070251a4040c05403001040c540d07080c5820041e4044490340382e054880380e81b190010100c680781d420940901000d00140304030f07232001c0081801100d03401040301c5803001c050008951a0a500a0b68659041c54a0030110030003601002452048440c0281d802d01035640c0041110a1902c3c01002c201580001c2421400d014601007480d034071070440150045c280d4000e0030b000340341c85801d07400711943d5000038040c007648000c14000e134003840c1c2c48500c525150b10740400700100705050310000da10300092100314906144009a00016049106800356080d03403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 659973336 1250 659972086 659972123
    0x61b0c1b03010e030a02151503010207060f0b0109061202073806010c030c30030609060f060f12060b181008191805011805150705090906040603 63
    0x80110504032031095003030041090082c0c000005030f030640620396004001c010400c5c0c02c1c0041160002c3e041c2c1c140c2d06c807142c0c840011078409000403c500b41c40740b000010041c44d00c5040714120381c5802d80c03072030403c4a003c904000303042d400848603143c061009401656000240f034a40d07404c01d00070420b55404004041842040450030624400190060351441020341c0c0e41401150700042c42c0f00c0081c0803c030992545808607452101105a0181440045208069406500e0f07640000080841e00298403448244801205401000003e0010b108a888490b040590203030104002054010400c9403c40203982440007075001200100350401010341e691041c20b500e020350108009050740103010300252804036a109200842c03061445082d406c550010744048070780981b0503007031004014041960311101180d0b0a100c0c840180b0500c428145040840c2d140042c1441e60343d89550742d0302001102008182c80c1c020080f036404060840d0300e07418036500d510000700100340640000e41800507445510111 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 659974586 1250 659973336 659973373
    0x613271202010f02040b0a05220f050a0f030215181c0303140402060d020703050d02040905090601080c010f08040807120203090307050a0b070602070c0801090f1a09061b0c 75
    0x9040c590080c4001d16401d841c40069200c1e51080c0030b404171007042140750071481480500b800f281410600c0d41c040c110310007807880b1552550080082c96041c14410405881c240c84040010480c100d078940b42d031842c640004907100851304200303480c5d00c000242455400300c0c4810200030180d00500c0c10819100c60300c5001021100407000f1400300c3c0c5804441a4403d0f490545640304560050916141c40c0c900d5480710702a4011141c01c9062000500c051107280c0100d0010308080d00652100203100d14040e0503491038140103900c0b1891542001c2010410703030344d00c030303500441030038140c00c10303140c10344551505568910503150064507170b403a08040701a480364003000805a0034022801c80c2c414940b00e804200301d02040b44140d1040040802201c1c0001d110f503005848454000c1c0311802809075a404041d00f50786032083c0882c1c94000007140c110410643d4135241da002070716081812503500c1c200b005246d8403034000d4001e4902d641481e03c0490712521a40031a0028076400040d00c40504580810240 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 659975836 1250 659974586 659974613
    0x20c101e2705071502100509061501032004090917070f020f1201020703030902190f03060b120f030405090a02030103050606120c21060124050a0314070f0305090105061327 75
    0x1103807e003008103910600000300d050190b02510b0000041c0c01d1010015001081c503100103c04000070b0319407415500c03540c100684010002e0354400701300e103181c503d098145412150120001d0f140140300178000710340300302416040b469054401b8003a22130340c40300068004104404860302e5600000da0101010b80c141c0100300c2c128400d9501d0b0250104420020f00e06c400381e402350f02c1c0043c04900d0100003007100768000e207440e030070043c2103005140d0300c50510703500740048000805d170b866000040c108a2800c09103200c50740462030f10303000c604650442c1c0d1503d46421015100c00e110b01300c1d00b500500081c00a02031201c00b00001489180007101c0f100780428600841d1a0314a8580608000002c18040c203040c3c244072507280e15403811400070021010f48003600b24810300010980c3c1c848c0000000d40040ca0369034090344040c1c44600c40c0b103d800300b00600741c0d28010b002d00d2450b410f050901030710ba140e10f4045c80c0a102030107000705800071040c51501c0382440c51600c0c085403e00405580c030620549284822b13 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 659977086 1250 659975836 659975863
    0x90f0f050105010206071d0418030903050c031908090f0604151209020d140c0d0c170a0309050103021b030706020301080609030306090c0d020c101e2705071502 70
    0x142e076503000681e101c04048a070840440c01c442481d00c41d440f500d2421140e00d420083c0300003080b049140002c02160f0806000701c000ca061501d06205118082040e0801c01900701c0062490504034840090131071180e620083c1036035404512180c40b5030300d0242590044001405207a2580e036115003180c503140c681050718002c174100104900c5520f00c04d01480c0500d6030003070160204d20101e950b81407146a100c103101c00c3d15014070031107040c0175520680441260360142443c80d80490400c14240740903840103460740d0a0746d004825401c0001d410980701000c0302c0007420010b8503141c00c003a6118006a51f503030300070780c02c3c0000a210820000103038007941c10b072003d030011106103940d907402c1a0317a00c0c0300c1940c0d481c0d0310000900c0014110b1340d025000700b4803441d088102508200130b44030000e02c0c000000301c002451a456840c51400200210020801c0796689001403001d00c039090120f07003110903194410310034175a0360300f45001800340800400c80208961400c09082044001d0002e444800c2001c1c030f003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 659978336 1250 659977086 659977091
    0x2010f021e031c05040c03380115110d050c010e0f070f1a0d020d180b011a0a05040b090d0506090106030b0c040608390910050f030a020a0207090f0f 65
    0x10349111481e04c50a84216071043c0600001402c54651600c0c4c040421001c3c03c07000c2d004422001c0c042da000d01c0e00642d010406903803e007103504080301c26141d103101d80c1c1d000c010000b254960001070503001600e150008990300b04607070349580c1002e003507000d400300f0907005003180329a88180d0002c550015140b000c807400381255582c1c0301e459442c1501160907600c10080000414882d08101c055554010105c02c45d401c0e50001b0718240902010b003240f1842401540c04080d0703000100f020803000400b2903116500c1060091921980710310203880f500460049413001d05000c1082d01140c0c441894065200b03420004450082c6000c0b03003414003810b503600040302d454584102240e20004d82c0025141a29001d80f14658a03680d450303205121b0240d1203005102d4011941c5a0320b201c201040c18240e0300e030011f00c2845079034031400c07800d01499120f03100444041000410a0070040381d51001500e4105001d50405652010301034022481c003000703600240c5529141090a10042000d5400140c108445200c103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 659979586 1250 659978336 659978377
    0x703090c12080c0d0801150516060615080610021b032401060f0c0206030c0a09150c1a0105180901060e070908160803030c0d0603140f1c020a02010f021e03 68
    0x456115800b03100c1e280e1080742101f6111401c0d4043ca000e018000c020360808011038580e511864103542c21540700b0f100303450710b04520200386035004900744d40c4142c003512000d54040c0f02c1c00e0000d5896942d040a80a2003410420248a55500344410b40081e440702c0d9107070003d4040d07200b070b1107150742d0280315144c0440e0001c0380f40c040e0703d03000b01101502c45d034004040da82159100403400301550b102d4090401007000c150740c04110607160926030600f034881561a00c1c082d00c00f42c0341c1264081040b90b8041c2d078030440d01004006075601c194120724010f150200d4041c9984030009114003400d41d81c0c101034400034420003040044c0390b0090102c003c5900302402c481081c2e08001100d10131020901401001d9041000000d0b042d400c0c107801000130a412150006210b0760b05c0d11070164410000c1c641d1703481034100b003900c00e050b18010070102c081003640003010700301803550240180d91002c4181c3c000341030100240214203224000d2040780503032241c1d060420f4071400c0e0440c6035a240d41c4554000030110072030300c90 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 659980836 1250 659979586 659979613
    0x321032c07120209010608130f150b1c030f02030c06070e0907180b25060203010501030e070819020117180d0e01023d020c0705040b090703090c12080c 66
    0x71070300c0c901d4010700403130180c1c0d007040401c40341075400420036403400000c0481764000885070804200f54074000e240c0600c1d44041e0842c440240c501e020821071042c040001d400440324680441d180f4410f5050030035260401210700141d065001c1c04d461041c0c2c0e40510030400901541144400032030b40401c440020059072490300955003030f054007a11001900c49544240700e820342050040a116202d0445106402c18007400d4080d01005540e08581e000d8000c0010042942c140c00344105038003c88000d407442c0360500076001e41d119004402e0100d402e074500541d000396401041d81d0300c034007c5c1e56007800322240360100000341003162134042a250f84c0706840108030410700c640340e141d1070a40160301803d110b00a4110451020801c961403466003400b1103514003421034010ba201400804802c000b41c0c988134a50081030030504140e01c840e019605001100c502682c480d078810341e20090500300058041118140341d444280389411100c5803407416138101c1c007402580b6015015070710200b001c8442a450806 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 659982086 1250 659980836 659980859
    0x30c090412121112090f010e0f010b1203030f0703110d0b030c0102070f0636080705010f050306060c01090803010b07020406050f030613060b10030e01150321032c07 72
    0x20f40201c6a00c1050011508a40304860001e402028007001c075520601400300241c21500c660082601c03503803002291803001c40f800c2c00380e4140168206c510314000ba289184498607803000500410b00c9845020010348098081d900003802c0303c0d00c644005440d11a1250450000d20483c04011311900c03a21710600c5096100044100680c3c0c81c034030811640f43c0c80c0500c00d40704007611052507440b0000b1402d0304150001d4089009045500c240c141004443c500642c1c00d040c0704440c0c2240e03040149505c40c0c182c00f00c1e085422039800060943d00d550341c0d00520071a03180140b0101c400205501d0000000065440c00031014140c034a0007183c0c01c0110703940c1d54042000b6140490f801a4040d0007520000c1e0404416116803032000d4040c280220300504c07440002420700350805503010100b41c1e2904145071902c424403403015400d80c02c03060140780b2410b544071080040c1c4442032440b1440b226140c404030b000d10036004017442c0c0008042c00048003402d030104181c51405030700c0c46125441340050001d200030f40070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 659983336 1250 659982086 659982101
    0x1506050711040921031107050703120302030903190509030604030201051b03040510180b1f090b090612240f31022115070923030c09041212 61
    0x1340340545000c00665400c1d15600c01c01d248806240e9580d00c108005180d07100101030561240001c1e01e501c40c2540b4003440c044d2290308070302c000c261062040203540c3c480007003124038000710300b000f94644092070b1808580c18820001c0c10350709405140e0a00081540542006004420092030fa04103014044d03052505408100c2c0c02034010340c005884001c40700b040b0361241d083c2c00c85000c0003010f1a05240c540c0d486444060f00c201000c0e00702c40e1044d00c030a0300c3d0400928090400000c0030f1201d501d200000032241c040c05400b0511840d410004c01b80010000c111181c140200c0030314198100310009400480410101c540206069030500002e00b00f42e030903030542c5042e802041054207407a400109440d051136203030804030307000624160358240c0b940810341c8030510301510ba002000201880c0303415030100310000d0918000e11603d004240f0074500101901102c2c0804244030709000300d69400040d1410000075545034100544006120510001c0381c0c0304c400c80c507180c4e01c2d07100e41c404000d08102d0486446 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 659984586 1250 659983336 659983343
    0x4021b0c040902032a0d050c0414040f03080a1b120f0c0f080406021b1b01020f031c02280906021912030f020d0b0f030f0706110115060507110409 64
    0x118160800c10810b04036501003010741d890384c44801020344005c42c82c80d803a404410340e008c2d40305c0001c103146481c05004443d091038003003106065905250340e410894841014008040c0681d080018560244562002200b0385c400f510403402c0b03604034031000d0708030700141c04c10b00043c90038444d180c00303140c1d2103000b10b007124003655485882c26251803804454a40002e002281e603103808004031107481500b0701d80f244885080002134038950401072034041941b038003100b80361306540110300c0074020f50001000752510058032003007205d80428007142e044000e21806140c0d002000d40141804155041a0880c0500844544411240e103490b100141c0c0e071041e174007503044140038041d040440007881000b0f1074000e5403801d05011450941c0c01c007200d801c1e6085914145d258030756480656442d40f078981c8406845035026400b400001c42090b00c0c3d51b8030f4001600038482071109c600c01890080001b5808052000942c200780341c00075448002c0100a5070004000340da20940d25002140b051030079100302c20b1f40c0c075070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 659985836 1250 659984586 659984593
    0xb150a0b0c1c2a1a1b030a020307031401051c050a120e0102100e070b0901050c0105010e1504020424020a29010506090f091003150f0e032d0904021b0c04090203 70
    0x82c241c1d60200004e0050000c0c80341e040103000209a201140b01171800b403029050050780704d19140c40020212604445810f100c1160400101704945422104030100c08180d04900301c07030011418154540788003000c0c014900b90301d10040b00d00d4641d0004800013110001d900340c84444121200c40000c6e00c81404202029401041c0204540c00f0a030009007500c0c20103061042c240070740d02c0312140c2120002d82c821070710001c146040080010b00a201d40402d00d400312001c50601d81044100c005440c1480c41460740480b04003c0801d019000b0010002082d83c007120000f12072282c076120003900c4000e400f5140c1c86c3d02c402400031410345048025a1000c28010b40f85800a81000c003c0140e80540500f682c840580800d00101c00f0444110b149030300c440ba500c40204544540f80c02c020205c480c40b0503c584103030418061028070301d4012408031196400d520031f4084401040c1a100410b204210310f43e50311510000d12155988200c07011800340d42040d4042e94010320780d280c1840144c0302c8100e4001d52640 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 659987086 1250 659985836 659985863
    0x515120a021917061021052a0301050906220902010201270b190603031e0203040605070f020a09020c0c150406090b0f070507030506040b150a0b0c1c2a 66
    0x1d040c03051100d040c101e8a05007100002d00d488003100030809101c0b0540c000d88900401423000b61516845009601102102441d10302d0328851032103500040c050300c0d10071220100032075107a03034a20f210321402c507500034881051a844241003000528011b10101e015509142000000e0a0040d88011100da40e040c064038404100f9a2003075920b140080400d001040142e040000b070490342e05c2020091442610b4401120002d00c1c500d510070721b1800703180300440d8402c00041c0842a400000c0e42c1c103041d40215046060b5a50340f0008480d0440c0e0741040a01d607201044595000c48001408038600c08140d464940c5040d142100010603c2180101d40c040340c00c20b0010401043c0c2c94005000b144840700410381440d509564660406502c1d50082d9010b92201c418041842012800d0a0b0030482030801000054294030119a444540348145d070600700700410b4030000c0c034030213001a0013510708080c0001d104100340b90700940301403646c40490800d84840056007079106aa041c60010b510341103507680c203001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 659988336 1250 659987086 659987089
    0x30f09120415170c270a0312091d0402090709080616020109020d0602130b090d200a03060e0c06070804030f08040801020d140705130515120a02191706 66
    0x5010250340700c1004001002c03440c4061000245074001c1800c80102aa01d00001c1d1710f0540c1002a0101900d02964446100006586015814049175804002381411250441050780c0501140c0d1220002c1c4d02e41c0b104080c0419090596544201d2080f5541c0c8400d4440301801c99082c47d80d409005a10381c402004500d0201c0801003040c80c6180620001c2106120b55010460007040c442084a6040d000b050182c0e004926002d01b4000e49005401c050078110341100042a02c8601c88025247c1c0e4807500d401c282d4001845041002034070701a0030031081c55502d14001000301640c100f4010240500d0020f04010702e0150200e4a001da08662441d04050860b140c6440c60f210248044480240811000038401400c0c0050002600c50b50b0340040c41010360400314006410080240040200c10007540e032500038007030240001c2c0c0c0d009450360300c8a80b06c18110300f2145e1042035030a203032003a00310007002500185070b001006a984c1d020600c004100c01c00b00700f40c802040c4218030031140340181c0c00140c001d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 659989586 1250 659988336 659988359
    0x60504260706080603070305010212040b1303170a2c0f03040609030b15030a140607050c060a0f021c050a180b011505161406010b0a1b080c070b030f091204 68
    0x600003802d41b40e100d50307607603240c608a1340520341680d00c000300141000240f101807040b26a2200200318608492141d6940c000d14000661802c100a18240780224800c16080e034407071040c1040000310751618000c1004001a448402e40c00f5041502c9620804c03204058040207450480e101c3c3d07242c11501c2e604503642c0c1c040a2400030485200b56004c2a6402143e540170005100002c4c09030f03004500b00c8980d414000c1c100310004081c0000d0001c200000d601ca004005130b0254824000107000550b1041204804060300c0b5121190382d15440308503522010b44010351045002c3c68070403100b08480841c40389010101c116a440180c414141040104101e090f0090200110143c40c6001441d20307680c41c0d01c0e1020300740d2a680607208038000800000368030100700804c50262221120190806000d000300070301c1c202141c220040d031981044001406c100c0f40105039840d039101306081c0c81c51551501805c02c5c03e600110f610514102c01c007004114581c1010600d441d900110f0902e0310314003814501c01191 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 659990836 1250 659989586 659989591
    0x120c07050609030120030421142805041404051b03070c021909050711211902010c0f05070201050306091f17010e1911010504030b0106050426070608 65
    0x1055502e034a030303c6640c0343c5ea0940780040d2181c1c50810940307909007410050851904005103001b181e98113080d500450b60440408102c14a00300300e5640c1e0f842d419420680700001c40c42d5900400e4900940e074280c038a4002c4080c000f0740d14003444016000600d8810807040d02c90039248081032407070808403040990114402940c5c070198508120404285d1640402d40100000b1904001d901c5d034400180080d03c0c0a006543d045600e9141280d00c290408a0b9075803583e50220070a050a40210100e4200e40494425615190341d138801004080c0030692001e801303048440404030000740d45240312880240207000742d0700c1c155010f03565035046644440500943c2034018201e80703680d08440c492500b0070302f003458031000501250551400c040c80b030040040e00303499110041d00c43c03940050115005208096141e58540751300322001d04000900c00700140d4080c852a0406404d507c1460300104405800c1001401140d10b10448450907440701031400b0301158400a00f0701454002020401c0402c0c0704416058 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 659992086 1250 659990836 659990839
    0xf03090b0403050724020a090503011e0c1101110d141e061c03031e1a04050a0905031809070908100c0e030a06140109050912250311120c07050609 64
    0x80405000d040b00c00c220500f40e1000d044891b400007480c416440e4045500b0000305020740081c8420b00e80c00000184840503101c0c20322440d6034a00709054030038841d0101e07a00c03003c0008000c00500040040b800c4036076000f41e66000065013040c2201805501c80f1441a10400c1c0d107500303490080820780c011000e00d45010302039a40c003103411801e040b90204802e00550040c0c0c03107030b100007030050202e114500ca04e00145048151041c41c00c00c40021020b00742d0910a28441c0448000410703a1b140302c892001000c040402822074400801c04800c04da418403031412428004884c004880c0d41c070b0440844840403140a135140e140c00016002c041d103180758020fa900c00a41d828001080421440801d1400c050f048066a645840301d0b1000b000011401060780502100a801c0c009850144015070f500c00d4a0510803208050000e000400000b03a000481921500b010442038119401d080040c013140c003407280c001d410300401071080c000e6000d620840720321141d010040d25035246400100300241d00102501e9 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 659993336 1250 659992086 659992103
    0x30203091518070510090b090d0f0b0f0c090d02040504030c02091905130305040b0315060d0209030c030106050f2101020c030319050603060a020304080d0501150f03090b04030507 78
    0x1c401480300720707280307a1040701c4040751002d25104008400e45880c5241c1c3c0098052005078803d000a558060080410303070354540b603030655489601c0c001c1a2400035400000e4245aa85003514081010405a040c05090542140c080075190b81c4034038000e03489058501c0c0e6018099240540060074581c0005502a01a08200011035041d4000c52198581180c0044407880c5105c0c4920351451315110306c0e504204c403005002207842d41544d001d090b511650044012110700400004c40403000700000440340e4001400035034603150b0903002c074006508601255413081c0100031482009040500c2a0f004582009150f104184107990074440c0d0101d000c0003d1281001c00c0098041c845030900080c044127140300011548c6e450702400382c00c8a2115900202003150820050003a183c1e0001107103500003c0e0f5000042e500d403581e1070241500d2041c03500440009003424000075501a04d000012800e07130700c68852000840070aa01241110b103103c000030070a8211002003800301e480f40c4050884148a100c89 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 659994586 1250 659993336 659993353
    0x220b090307152c0a080c03160c030606050d12030f0f020c0c030c030304030b072f0706031d12030402060c06191d1b0f131410050603040303020309 64
    0xb0100109924000d07402d040b41c4503408440280704819a144000c05026244003010407503101503521640c0200c400707000301101244a1148410900c12564104000301121403e0603a520701413158049c94401560540c0c90030714001224101a00b0103803107968003031024104100c03054415070080440360740101025645122545d081d410a100a0148141020050600d8101d0300201441c20154800040c006d41082c401000000c0d180e1140981081c054140410b5584090128519054600316441078003100c0d5024150026400310340c020076100d60f0f5400b8000c4100b0b500c41640c60381c81c04183c120082d80180400c0340d5a95010010396007042c0700074411890600800b417003d00e048070a9a51296441082045525a5916128010303022101c2e41010324000900c841242e15500c032840c02981400394030004210541d03a41c6c0b4100c1d15510300a0a01460040c5000004000c0548481a40ca10107180c00420101101141050f040780d00c02000c4524556482d542140603401c00740100702030380f04031000e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 659995836 1250 659994586 659994593
    0x2011b08130803031803090d11060d2406030c02120f192601230117270609030a0c05010213060c020315060a2c090c0306220b090307 58
    0x452401015542c0c021500c030300f0030107040480c40c0071400d081d0056500800c0002c196864440019000c103401081c82c03c080021000401d680d44100464028030524280303044821443d407551046041103c5410070b407c1a440300303801c3d02211200941c0d540035034084200540d400c07144100600802ca03e100909082c2410b80c2e5420f440b00702c0c220101000b10300140e13000d5902070410b0390034101d101d4100d01c2c1a0525407400c8501c600012101428041c0503206030401c0c0e500b6402180250502580c10081385050301c0c144090201d00303011030040041d810b14120b090784d0300000c005460b600801440024500c0d200034188182d402d0422618101c4055409105000301c1e03000f002880c40090026858010712118684101b50504501d400d00704a200d00880174040c0c940c0341c00c51003030145c0c1d078080344203600500d000c03100e11401031442c0c8a81d0250005032040200403580841c104441000540c00c40b82c664646482804121030384a91812201800c544100d02003062803c010341c110300a2001d0360715101c850786 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 659997086 1250 659995836 659995867
    0xd0b010c0201531014061b3309100c0c0605010303020303060a050405150103020919031a09150718031e050d020102040e0609060f0307080a060b01050702011b08 70
    0xd1192424240300320f040d480740f611a0b0441d0700c0340c803403d42c941c00d0302e0405800100305002080c4d181c0c0140c6000c6050f03040d88503d01201103030307140420104e49140002c40844284204242e0300c5050040010041d0003100b10160701340c5000d5000c04c009010092080304c1346070020168458081c04002a59588a021603034902c60711740a50700960103540d0b00d1030404203008040304c01d64800c2d40a0351a040030060200100c3c05400e4000030246400350795011001d001918640c0c0880140000b103880b0b03d00081041140400d1171902070300f040c610403a07503032007411003612805a03400c03810031012484002100c40303128003402e003c074010703200001d1802622612069000d00c01150101400080c440c40f440a100c0100820360880000f40300135442e260400c0e81041010101410603030080e00000c001c9803039507a0320074500307268100140442e00800d5613506460340e51550141c0640301e142c0b4040c00851301c0e5110703000b15919260181c4603100b80c03a10080072900700c1c3e500311030309582040090107440704581605 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 659998336 1250 659997086 659997197
    0x1207051303050708191212020409060609030512040f1e0e011203140414240a0f030b1c02010507171b01140106080c0c150c0d0b010c0201 60
    0x144010000181803070750407460710440c1203c4009580c002c5c9481800101100c10000817041a858500f40c02c1c000c2d5940e0001a000f9500302c043c0007401c0003070100d94036a00044035012240541c0c100d542107da11511400184518007911109220b03509003449000f1080122003100c0000300c600d07210389179640b04000001c0c402a0411050241001c0b07004013031591105e811a041500d124130185040d2500c80c01640c05000d440e1b034907004030300c0c0f1500400e41c00d80e500003020f5010300008045a44c0c10801c0c00003040445400c0c24423012a140030441140740c181301254504a65080310144039100003030700113442c01c1c2c00030107088404000e07249115088a8801d005409082030b0028000b080d41681c8042500b545c441d11a00c0040514800041010300d900840782508496050302440d40d400c417200e405414502c2e100c0000c01d401e480070007401115404c10700184260014403104000815180c40111040c0701c01034000ba002840b4203903418004084180320b480c0da8a044c50b104908140c030141c4948980190 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 659999586 1250 659998336 659998343
    0x807030e040203010e070e0a08060601030f090519031808030703031a030a0c1517070f09031b090506030606090a05070306181b020708030706180b09010903020f030f1207051303 77
    0x1c407821b1220b001e4000031510030180085a1458019050000c080d56541d002045281010b0305d03000b19000814940d4841c1d034800f074020003503403a110031240e04484c44207142c080031000030341d13005a4002c60040d540b0050054031058009103260004684044025040007103024030305000010032020152340070410039400e540702c1d00038151150310b07011b410040c0000450354001070040d00c10440540842c41103d030b9500442a0500d03603020880c6c60411914080a0341001b005e00314040019071070481804200b4040f14045141441181d03608414540c46540940340640c01c901500c02140883c2d200d604041d81c8000c03540380000d099a960004240050511000020800d0781c03090407452000c440c480d66000b01d2030314001031001a203484201c0d9a648a85500500035607a01c69000140c0140707603083d2000690001c10f02d200c1e500340010494002d00ca0640c08902600c24101c194000c140080103481c2d0380c003011000a41080c0c10704843e00c0c2d403074100400c800200001000340f4001a0820041035025500 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 660000836 1250 659999586 659999609
    0x3180806180c01030209011b080f030c030406060b0a410c19020616060b0a2c0c0d02030a11030c040608150901140a03200a0f030803040807030e04020301 67
    0x4202001c542404154103400381018010888007880740d8001441c03106060300420318621859950405c1c2649000d00e0b588501c02140c000103102d0ba6498440c080c40c0158096001040060399504011140e88211250300000c1440c07054417080303240da4000c00a1145450001c1004250740080c0c0c24008003108005008544a02041c20516880e04108e14400029180d40035800c1000c00e030002140d900440121140361168558568204602030300b000c1a8000d010f82004113080c0c54024913100880113a50700007100c0110b1195610702c03080e4031845805000000c074410325141408180401a40c001014172014903250f140b402d101c180c0c3e2030020340c0300302c003aa20a5910780f42000c80003041c43d00041c0941e003090b42d6040b0141c20f9603a84a203414112242c00d512541519910760101e0404041c07584042c000018900309640c0c45850307060211030a07181200c855020684802d01088000c0c600d020140c845a0b052002400107218400208030302406401c220b0380c0c496500d030001c0c0c02d1b0fa100b60031103885440c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 660002086 1250 660000836 660000871
    0xe240f040b060a1709030909041407030209040b16020d09140103180308010317041401051b0d03061d130204050912072d02180c09150c1603050a03180806 67
    0xc64680c02174204964602840c541184c1c5000038140c9131001c3c0c0041c03c148003202000300b9850081000e0002194089c03d0f00c45035140c141040f560a01e13040719074041d490640307040710303022030300c00310b90242d0440b11601c80ca80510f007000c1051440582d890001818142c0e19503000041600a12041642c03503c40c1ea81d40316290704501d07203201c031680c01c01d100070b080d201c05110500c10203000a540100c440002e1070039944030f40405250a104030072001c415006401045013840d2107560581045069440ca03400304040141c00d00348141d4401e02c00c540380c40c003e4204014882c01840c25802854000d08501c00315131012403c42e0200c01d0680c001042102c10385602640c0901ca2104000d4100d80644003482ca692100450303000309210b1241c403000c0240f025600c070000b800d0710110000fa14840e000183c0380304041514003440002c070f07038080c0c20301400520030014004401c081e40c01d0910700b03489c0e01c000606010002d60358291603150300900a0b1445950a000200e001030303081112034811000680d01d02c5008 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 660003336 1250 660002086 660002117
    0x160606090b030d0224040602071e0c1403060115230c0d0504051309080c0102120f01050306010510030e0a15090308010506160b090f030c06010e240f040b060a 69
    0x210034652024107641045c03202d03a18010300e448100081600300540c43c0039581d1140741a0009201d2660000e10104800701c0e810448245a444460100c0c828541d01c542c41da101d03e1100c0d840c0c5000003800c6d5066000d10300501081d4400c0b520380700310585c2c0c1d0401c3c880c4d148075507185004d9090030802040509801080354400c07160200302071400108542401403629007403101017030000040d007070800d0440381c41c0e85003102041120300803a0481081000219241c21a0700c9400405010035a042ca00782030094001060500d8081106c604179000203082440303228010070203401138110b40411000c503020b504e003244081007107542c40f402e442615030ac0c00a040d4015107009440c83e207060b000305000308010b103e08013480079107182d035401c40754001d81024126516244500c2c50031208448000b52800041103050390b880d0b00140c21810381c1c401400a1400ba92121806008410780da0034000d15002081c4800e200d0341400042c8140c4000082c1001c2810710310b0308003103841a408107070458006448003d410404 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 660004586 1250 660003336 660003343
    0x30c0d0f15050c040b07020f0a1811030f04020112060b03190f0603080f0f220e090a0309090509160308090301063c03050d0503180f060408160606090b03 67
    0x3100c070400000c02890620156001c00340c003960040c81115031000881900355569001400a010b0b0010011200c498440786041c0040900700650f40d403607810a840154190520010380344a21807802024100e41c3e0f40e07400448000c1040b1100701403c0d61744201c0411030540d108001d52040c5141c1c200510011000c1c140201160f4900ba09000300710700d89201440021002070840748040120301c1c0458866114946681079480380c40d0381d906c0c600c03091440322a0a00300c0e0881ca801240c941030b100442036a1447d09650320790402003030050005054050038000c91002d540060380240e03442d01107031005407240340e25031042d03900d9400070b496900c1c012422402528003400f5907000b40041107200142401e0591500c0100f9040b41d46600e0780f50940079001c2903415000940034005c3d5008800c41c1d51290360303014050b001798000c1d1100b6424652801038000003020008140144e0a148402803480d6921501e90030000c2c0c000254020070030040003603c20219406002d908060601c007840090b02c0d1008804140c41d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 660005836 1250 660004586 660004613
    0x201050f07020f070905090c030102030109060305010e030319051302030f2d0304090c030207120c0203100920060c030a03060e160f0c02040207080406051e0906070f02030c0d0f 77
    0x115071000005201e00311000c44c04c0c0c0d04031910004080707110384410240606204501c4603098143d840030000185401c1240c11403800c80c5c2c0628001c000c40d18833140450784a1108450038031a5481400f10300001c00e0711540460f42c808045411109002d0041d40000c6c20070b9254840c207180d91344100070b11262520315034070425810f6031140803017101004601017142c07030340034902c00c2c20704940c0e8071380c4100c0303100e03009404030380c031155001400f1846203410880180905082400680c001e1180403103d11601c03c16106210300b00d034004101c240c540041c41114202c90402400c002e0300481c0a000e4007031003030b004002400440410307880c0031580b103042841101c001038006103090701c2d0b00421480c005040340c002c0700e01c1c500700741c06140082c84402640041000780c0314201004000b003600040000c0c1300ca41c05000b400c2244c0c01d602c0c102c028441c030ba48070728185020b00d50540d9808801040305100040704148108519480501903d50b00994480002c50201d00341100355040c104209030740e020041e40400010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 660007086 1250 660005836 660005851
    0x1f050f01080a03140f030f27190516151409180a060b0c010609140f07081506030412020c030f0c1e03070803040e0a051612090506091b0109030b0a05061206070201050f 73
    0xb84141203c40260382d0384520540041980e0325031009e00c007070080074070201302d030783c0d4048018002c500d030b941000b101814074603007807000015524074080c002c1d003c10204450014000804505c1c98040d4080d11951500000d010004080d950304000242640300d00041d00da0002100000100c5a03e444511403d55040116240580c6881c508001e0320508200040c1e40140c07652800c41801d0751a040745030120610081119444140030003044208010310146541480c46030f070944110000d04000c2c150754200d002248a04c0e504103080840450404061580e200d00800013540308040010f13010a061420720b410034601034000260502034540d50b680d4407a0800707545c80041201e46411154510504008a4680100601e0650940f0000c2680c1c1280c0107203908102511003904111380e5080e6102402009810f42d01030401c03080400303600441407107048175000741030b00440b5510852079a006004c000c000726441301d2070f80c0a04401410400c80c45104402640000580e410180c880d06100c1034001c01c6030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 660008336 1250 660007086 660007141
    0xc0c13060f05040b06040b13120516060507030210020901051608040501020c010504031e060f0c080714130509070903050304031a01050d03020d0806040b031f050f01080a03140f030f 79
    0x242c00c03030319000c2c12a8101ca0301240c0c1f0580307031418080034180e001d4042d4440851512507061070f41c14001d01042da00c0002c00c41607480c03140c02c1d83c1da070019241405a15000780140c0c0200712202c0b1140ba6540061044000502d4507624110000040c183c500203141400d603400c07030021405006035601000340140180d42424883d04161556903031040810308120b6036071127868018903900400c0516000304124803c40001401984950322000304443c0741100c10000181c080340c10174071743c3c0c41240304036225085e098010f480f0890030038081c4400c0800180001080008212001000c16030600203071020314400d80d0f0520000f0b00c215289180300e513060700104d2003080c4103040b40000a4000804003401c01c003d0504038840e0390b61500080040c2401030003d80c050041d60715241410708988040389039010012420007075034481e07540e042c100c40024094100390354003440c0040b01082c002c1c44040c4400440a101c1890443d401c0316403d1181c2042d902c0d50f1000c0310b484144600c162440e0ba05404071860200d41 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 660009586 1250 660008336 660008351
    0x6081501140603160f0c0b0411030c010e240d0c050a080106030213180e1f0509031608030a02071b031e0507091505120c120a0201020604080c0c13060f0504 68
    0x84000112428201350705011070044040146030003140444162508a0749106030303464681044084024101c0c2d00341d220b8001e045c4100c200d507000c3c21001c1c131001c8010b01100c24003c0882210700d00760700c010140b050b1b10b420500a0f40425010b03402900d580d040b0964501d80c5500c941c1c20060501103042c2c2040b010b2500601c0003c0c8035010098900044880182d10b2407040018000d034400288110042c00e43c40d0b0091464096003c90300c03200f104522000150100301c907030f80e140282d5072240036050080000300d03100050540800c40403005503420910402d00107142504943d10100840030107000c20740991a07040c0104103100b031660001c0030061104a01c40c0555243d9521541c0f22000c030b000e101d05a55449503105c40400c05040180e014000181902c0c031900c00f492140f41c0ea407103000360f91314401c0c4200c01a60100c0540410800c0580383d06800400305a102c2c0c1d0350720b08440c1c0121820494621907043c00c0b01055a501101c01e043c10403400c070020350035080800016002a494100502440c02c2500 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 660010836 1250 660009586 660009601
    0x821070504050d060c0519050406170c090603072a1505100e1003021522030804060807050c0109030905010f031109150c03280f0c02040f06081501140603 67
    0x8401c83c2141e010b031000600c01c44804061710f650066000010140914880826005822030014020f4031069100e080e41c00110031070f00d00125030106c0c1c00f40d00e19001884054910f00341381001d9134000c5181d0610f80910307803010703941c0d4080c1c5d60007500d1700c400c0038501d803030840c00e06c107250345285503007004000b00340003030700c0c1115107110003028500c944800d0301e07115000150103041289059028681c000d00e064140c0c1d400003c1c0c1d407040d80007480031020142c1c000420800b080e82c8840c100f4122544001c0300342c00d2a00d00b81c000c0d1481e907402010341003400b0003000390900c80b110038401e10310044d100342c484d260580e017001c00050940c60350190000a0500c0d00f80f09900d00303440703402581c2144004071011000280d1445075507200307000d504070412162101003450442d0b802c4601100001201c1007113200c2540b000d42104544803200201c8400110300c2c402c0403580541801e030800c1c03800014590000c80c181d9503c242e01072900254258950600c080603006000303d0100036551000501c00700c0c4c0c0310382541030003034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 660012086 1250 660010836 660010849
    0x170c030d0623010806011101020705060117010c08070e010507060c0309030e04230408070b180c0f0d020105070f021003141f05010f180906030227010b0a0309082107050405 75
    0x200c150504c5102000605503078480c40041c0521400e5070025521080e141c5086580daa00030f016a05100c51030b440d920605180c1403058880d00c6140707568604050f22059800d54465030b5071200603040120400c1840045000350003400c0c600300e10703603078000340000c51403d000f0b0840d0000540540f103a400d150011184010101100070f90a88404065925460f5403030b21520622614a0040c5900390740030400c00c81820710040500380d09090030503116104540310401210b0070041074802d500c503800031f0009000d5403181c00902031203813080904da141c100366a0001040f440d8110301c417000080d2900b070300c0010301c0201070a00b60460b55000c1c1307681000d046064040e80f01ea446000d194100b00714000000030712407107100d55015900c1d00f40158000700d6195a1184003031700300c0b40002e03802017168201d88042c18001d00c11101c203940c0c101031110940d0b403c0040c080401e0b4060f48241c000c040d11071581401007090f00005140e4000e141907805482c4031420088070805400a246105100d02404108550780301c7e036 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 660013336 1250 660012086 660012149
    0xf0105061801030e010c0f0206010b0f041401020a2a080a0f0b040312090f031409031c090503060a0e0138151c180804030f170c030d06 59
    0x48003a03407000c11200100c0040c06030300314000403503007042e04460700c07203400c03502e01c13220700b50075070b00741d890603a2200450b806c1846810390403180c50004010400101c1c0c602010101100414415504034004585a41c20b030f0300d010141196000402405008400e00362101c0c040003403000e8000f4002c00b03003031901c071071114190702800074020813000d40008040601c0340580074151805003100300f00070300850400f0781e0b01903030150084003c40d0b03600082001122020040d20540d2000078018140c41502000707482e6103442e503221075000c0c0600b850021650b0780c0d040c4002031103046c0200000071841909074065007950a000c8038840e070000f442d900610509084050000d80600383c9007110718041104010600a14010441158141c8040382d4110802503221160700c1d5120a00e1701441908810326440c2e074040c0075040e0080c01c1c9201004108001404540221522806424550030407910702e181590158045920400c0701d800006920700c50b00000d02c03d0b040900804010120369200740300c60040d885c40721 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 660014586 1250 660013336 660013357
    0x70f0f021207060902060f04120b07080f1302060408070e090706030b0d08160b0f06010201050a15030213060f06050a09060e150c0a02030d02071403192301020f03010e0f010506 77
    0x184d0030100c0c10b40d1541c4089031100d602018800b50b03202c3d0745401403400351410324822144039181c0004140c031244a0080c4d5801400340030150052a110010401c4c051840e241b4204d03000782043c0800038000d0700070301c82c3c0c10050040702000318032032400c0b0700aa070402a603504150185840e0080b16440c9855100414004641c80210640d0b502001603910406d44034030a00102107054000402408102c00c1c0c0c001c6000390700c20b030001e2140f43c4500070403e040c2e548841103050000c140d403c2c1000549426440826003002a500000e03245480e0015102120b841d40c0148000c1000060b422140c10b0740403003603038020145441c00740000380d40c4100198841d592882005c0075404046500342d0380f0308060061080c110750050444251b0703a44188003130b403107030304c42d00c202d20311500005050310103130401184103074005445040d81f40e2007480ba03640c0c20282d10359400d4169200b20800301c20345c00c0440e00b4070080c559070000e00b03e0a9120f40c540503103062421b000500b90048400721400411007501c654064840c1481c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 660015836 1250 660014586 660014591
    0x90c1d2d04060b030a030507021f0e01030903052106011101020a0903080d1803030f140c0d0c110703030c170922150312260a0b0a030803070f0f02120706 67
    0x64030b05050024220060500740d16010f4500c00c4000c00d50800300801c2d520b4401c2e40d060700608200c2ca40c00203400d1600c400c0c3d07004181e0325110805e40758840d03484000720702c2c443d09009091259000034061801c0300743c1d510450340f0001e03800b84501c541e0826954904100810025032512030b42250050040c00d940c8402041c41002207905d80c101c0130290441402c1d910169007900c58a8007a0400401418503401c8100c4118909030b00020102c2c1401035247c071a0041041203890048003070b28100007803031f1108503041003004c0e0764000e454a44044c00900c00442c042c0d0750341d40182031141041000c900220716800a590300400c1440394070b489415241c10000740b40201006c841021401d0790340a00070905040300c494000171008010440303540c910f50340e0390313005903030318245520020b020714101c1c4a40e06228802070348200005030044a2500000c652170300103413510f100d2690700c0e41c6124454000780d03500f0300421030039101c0e107c039503a106d0314002c91240e05100a00400240b070802650a00c5505406041a40c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 660017086 1250 660015836 660015841
    0x8010e0c1017071b0b042012120a0306170106051005040303091202030c032506080f04030f092105010b0414010b0a03021b010207061410030305180a0602070801360204090c1d2d 77
    0x140073303502040041c100e0382c1e41c020a024032190641c0c024800ca01809200d0414856965480d41c4140103403000c0e2a45070b26500429410200000350100389078000b05e07858440d84c0f170300c14001d450078441081c2c00f540b0070745003409202d00e0360703250580c5101a030400c0302049100400c00c0611620310000300e401c5600360411114407100301008813071b10740c071a80054014010030400116a142903071001c03030495000303c000700581c8050342c0c1040203071080d4018224810007940b00510049144000825161559090040c07900c02076200170150404041c6001071965404200c0744140a0035018280f08204c4440031000030b4034003030b0340040d035245080c0005410071401141e0804100318003007110b58620401098840b64943d10a002503841041c0c1c0149150f95082510780c0000720787c088940707100031069401c02d00140d454000b5001c0b0302c1d400707800705aa0164482400d080840e07008046140641032502903c00c203c451400000d074001d4026100c00d54144e041404040f1402c041e000306183e1420008140b81c058 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 660018336 1250 660017086 660017107
    0x30103111206010b09031605032107050a060b0f0909120711132a0219110a0902131a0706090c08010e0c1017071b0b04201212 55
    0x1075440441050042c0305400002c01d900001c0c00282003801c1049040742d130800c4040f00429580d904a04c104c0341c01da88841c00d00d4081c14410a42d002100c40842c4602d07061028070303185d50740f078014883ca095a900703548144407805070410100340c90100303030305031401100390a09417001c50340c4100c401c28860ba240c4010800d48100640d002428411010007420041c0443c001e028140003041602c101d501040b8607001c040000e00d8151106522100c1c0640291441c4503101241207222104e08108607a11940e04031030405540c0d0380c19a590240040340760040c1c031750200ca40510324420568001d036040300c00d41c070004800146c107041204d002d50b034414404221b04a10b480c0602240d681e41d00081032950170300f24241c1c599035000804003945241260b049008800030141600c0311111f034a0030240d00b034042c03000661451300904d85041d580c818850181c003030440c541c94001c82d4140545040303d4103080d407205d403444500c10654081e94400c080740d40340c1001e0146007400b40c0e250080812203200d0b01000c01e800850 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 660019586 1250 660018336 660018349
    0xb0d060b0402070b011d0709031104051806040c0812040e0610030917130506040e04030f180e061017040311100516081015030e0c100f0909090803010311 67
    0x42d20750140044c5400e50312285290b010081e00884021885440400155007920600d4400e00301ca800903409603000300444144009048002e12070318444a00e00007003001044100151840385001e05400c40c24181405403903410b000b00c03410030500e40304041c0004e21005001d6040c161f04440b0440f482c954503105044240c1c050300d81180060240b0304010444d00c102660207004000d00494000c400c001385488a0400010b4025401003900c41c000c40e01c0041d00003406090b17040908140c9c0e080c403200c98947c48883d10403a50702c54001c2f0740c151002d4002e000c118100103150344c864010f241440d1000e071042c0380c100c1c0c4161100903c00740420100c05480040248103101c6400000000e980a11139031520880d00e182030346039020300c000013900500004023078080807445902a101d0008041900c80c000c0d40d022005003001d6a0000118000ca00500c0d1055a891030a00e540b8411500c6014041029200c060011141940410f621900f811000c4000031070340c208880c15607500100254054151070003040a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 660020836 1250 660019586 660019597
    0xe061008012639180705160206040b0a030e030c03190302040e0f0106020f0a02030601050409030504080d080106080a06030f02010c0809040e21090319020316090f0605040b0d060b0402 80
    0x9011070480901c0d20140e002c3d0f4504a030620340c0701083d141504a05020001e40f0030b5072480c90441040010940c000d1240005210f1164a416544041112500000c02c0c07a4055400304620840000f40b031895160540241110182e240c00614208024816829100d01ca20361440c140d1082203038078061081d000b0ba0603100a0400d05207288000d107098131034500078000a0088101520a01101e80442c6070001140c03218142d020700a4051a440d050620001d0828060b044042c00818080442c0c4104e0401800031503001d150ba840c0800d501d0501b003d01003ca02401da00c5041c1e042210a202003071a05c82c00c82000c560a10742482100300303609041049000c1c00068690017410000c0d00070f80c42d880007458801d11100510100604521104414160f1080240300c54051300400422600041e6070703c840d0039080c0c009000d031303644030700200341420f41401160440700d12a42d846a207850180c007980f2690000c1c01d01a0303000c1000219240000310045500c9100520643c0c40d083d5040080c0c5136601500c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 660022086 1250 660020836 660020863
    0xb012c010305102429070c05040b01030e010f060f0e1e150301090c0f090e06060f0312030702011e020f182b060b040b0d0807020d0c0e0610080126 64
    0xe14007500c0f00c0c681d41d0450750010303003d0b14544401000d005c040c6544001c589125078000316411190389014244000f0702031103203c00d03043c155520016117a8500a02681d058041407000c0003c201d03080c0710042130300c103256802095600482d10700700411f00781d0b400b038810010400f180c000b003466901d00c0b001c40807071a403034040203804d9402c07c4a08810003980300c030700c80b05903040020040103160300c0714040c05c2187c45d03415507815554400c0011800351304003550f41140c3d494001d0256800b1a256510382c500c6a8030075101000140e6540e0110b5603441075440541010b5030701104194030b000c02c08a0301c03411034050358659400d2203d00c0003480007242d40d000540b00700c00c0f500052490201d0030040400680001c481c00c250703138103410811103030f40915252103401248080140028400e901c20307156801d040c1c202990482e0420f40603142d0b070002c552410300e03c0004014418500c50349123044810f0203029544030309158140300080005120504442241040400c9440086000c1c4111403001c940341c00c49616400c07 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 660023336 1250 660022086 660022151
    0x30f0403051305060406020f0639070c031b090207030905040c17071107052b030507150504020102100c0e0d0302070f0b0309120304050c0d0f0b012c01030510 69
    0x90354035000702310314032001c0d490070660b00c071941c401400034000801d00303010100c1c1000c0006261040070344a40414a2150700002440c02c0c640700d07940300c10b440c804d5030700180c404100c0c5044640c40b036643c40c0300c04000747c1030f0303800c040d4104240d0b5039000d0071080d801d01442e44101e40740c100080f14280300b5090b04051f100180c1790b224250a1815000d0b0200181c0400d11049010b855000314a134100381c440c04203600754018503103030b10b80940003125005a035044000c404204003007081c1030119041000e10340c401d080780080000c480c206440060301d003160240000c1c1100d030502d149406083d411540e8860107a005940b103003030701082480c049041c02201e400141041104a5010600d409104082c501c0740800800b00c0b08540980c0d41512440c0c002100c000340340b0390005541c41080d050035001b4410452040345102003900c19550b58a02c902402d80002002004819403443c03640c01c11980038400c1d50340301f0342400055046444654076950306803410310325162105c8904c1035001802c10b045020301d10441e560b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 660024586 1250 660023336 660023339
    0x509130b1c140f030306090106050c10020a05030a0b220c18030b04020a0b07120f1103030a0903230301052b03020d02060709050f012007030309030507080102030f04030513050604 78
    0x22106400028039142d445403181c80d5090010000c02c9a00503c001401c1c000e0303680c60103230102c81907400340704103a002c1e0242c0040e10060304a5800030b0401e004194070340c6a228640a10000c003101c828001d058415a05401201440c81e00c1c0410815489861440410009003154054814180308800040080c0800e0800802d010a110a441c002c510807038400c0a203d5940003448628000d0407006030160049207105074141d4021216079502c01c0b500e003444c3c0d52001c0c4074035075141140c108036a941d00350781c0c03507221180c2015801100034840c0d07112800c15256900100c1f214507410301050142d580616100c400707844d02d100c0e4645291200e0203a60404648051107032400039280c000f10741d4584054403a2901040c10940105022016510064001808406c04030011540442c1c0950300984281c402c211b100741643c8140300702c1c4095402a20340d082824594a0b016107084079682c4404a07591041c0240f014203c1003911040d0002c0c0c151030865210342c00045031803032540d00c55100b00d5110200050 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 660025836 1250 660024586 660024593
    0x6090d050a050d0206040308180705061803210702040f14090d020d0c0308130212070b040f151b110303040e180f0c01050703030e07030602190509130b1c 67
    0x80010910740310b00191a8650720004013030781d070f0755001c1e07a00501050003200001e0f00740d481480100600302c600b200b2541840d80d11030210b022641300441c07030510440c143c0351560072420204540900f06c514282140315451002000e020ba40c021660000e1040f600c48480340c40160710303500b05ca4184001d5020181060a0204441e40d480c00140a41c402502a00d0403d0503030600481c440e0700b9642d0191688003141d9541001c1c0c500341070a020040344c0c0030a446040081354102080f07018060050014131aa80b60700b005c550458030792150b801400743c1000c03031018602031940800c4000e283d10b111a03031100b5194171840d01c20030985500c5042030301031001190010304c1031410400980a200200542086022200810758031003a03410301d62140b95000410015981d48110000c1c000302d40207280000f50100175082d01420102182d10643c1c02d16008140510b040c004a649010b16800d9428008c0c64190703135002003403001c04681c1c080414655100d4004449469211004510f5003455041944100c003e16 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 660027086 1250 660025836 660025843
    0x30f03041508060a030807030201021c05061203030417030402120111040609080a02100f0201060e011404050106080906060f01030207020301021b01290907090815040302010b0d110103050606090d05 86
    0x410210701e0704a22001c25140c0b402040d103940101c0d4041c082600a508549800303017150f11184040b41159420005001000c2100012188205060902241c281049002c0120999147c00e000055800400a010000b010b2548028110310303002500c50301c0ea82c66000281e0711641040c049c10541d400c03c2c0c0140400440c140061080d01c0321a103804032456214440d0a47c2d5401c0024002d41007140f0880e000c103094000c141ca540712a07014400481c40c0b0f03454040300c1e08600700a90200b0f00000d061401c0300700514083c06910301405e03091529407028a040c808071a503da4001c2c28681c0154801031010045900c80e40440700026000f030025940e41c10f100c042d0712004000c1d40c40032082940303000800709020010082a143d6410202e50b440c0c06e6405540410040c010090400740a2060844001841110034410110300903d45030302d074001881e1505000c2d00307544941720201d00c601300d88940c00d400905004180d4003200d0303003880d00049540d185400b080c0c0501c1407000740b03070303004510b0a000c13001c004000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 660028336 1250 660027086 660027089
    0x17190317090d090603020a02031c020d0204080c0312070201021c030609060806040c14032e18030e0405070504090e1002040b1809010b250b0a0615090308040611010b030f0304 76
    0x80d554a10301c113030394400c200c04078040c2d10f0502006800401440c009446500b03e070b0421144240c80041c42e18440341110000c03079102e80c0c41003420f500302d03e107403200914090041c0f0994950324004907280010f5640001e490300034600e8040804034840c1058441e052003039000310060103c11100300004c1d80c8403148940c0e602d1007103e0448031010070510108841180006140781c03d14064014400b040c001001000c0c0000c880040e0850040c01407208105140300380101842107244500d803408500150800501d106254140035000350b040c44240500194810101d8040b9040c8000c0080c10008142000b42001841c41c0000c01007400450701140911310000203120020888450740280010541030101d007a07000d00c0790212b0400d0a00c1814200c90484004482030100038030541010b4a09507116280b080d800d81e603010b509640c0d0f1f541031116011003034064000201c141030001c3e07c1891540c9001240c8036900400040201e055881301c81c5c80400d402c1044400401419116240a031894980d0380790003a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 660029586 1250 660028336 660028363
    0xc0c030c1506120706020c040b010c0204090606230a090b031903080a06291b030f092e1b08040e04050601050904082d0d0501050108011719031709 64
    0x160b000f4030094440008440d0b0481d41d1640150003004814000c100c0140900c0d02c030f05041c030400900310f50040e81d49106024034a07104040001d045820300402011440c901c0e62250360b04e10201403508032039604c8dd0301c074500f1120320b44008075103904510046400c100882da03c001d5402e9084c80000304058200840c14407031011a10200000741c2c0c2d0b00440e580a50001070041031011290340c21300d000703820650083c54940d0403020032814440c02d400d20a4a190700055903407444800104e85002140350142480170703180c220702d007201e06140303044030f01500128000c00480c0504c2011040e03030b0b0007a2070350303c9411840358101c400f054980360307a540b02e1142c448040b00c084034540610030010a072858800c1c49240103d803c0101d5505107442060816543c81942c08080051840152000e4030340a1100c000e188400b003010700400c080d4980030025142c0c6006030005420f80710b05845000e03240d0000036420390191080c1540d0507000859083c15124075803407100e5807183d56200c00401c4442140041d540704074248 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 660030836 1250 660029586 660029599
    0x4140907140c0a0b10030f021003021e070c090b1c020307050a090e07050102060702030a0f0302190309150519050c0408030a023a121b110c090f0c0c030c1506 69
    0x205c80e191480764180b10300008248020380789003800075081c1442e140c0d45180302800c0040c500b204031329070000039526802d03aa24140d0400180e1200b04017010604030f00408000c0000c2c49001281400500d0580200b101c0e10041c44100c41c0100c2556001c209030030040c9409001c06c06416102c1c0d002c1c2028048043e03000280c1e1140240008240d440002d003684130303c03050340c0614140003000004455800030a1410b004058090110300400c071024880a0041282c0b80c0700090079a1046c6404100020552013170070004e880c0c40100082080322410301d0345085004900001c45503225807403500e141c010b6400c6183c05100203e040110707a0f4000505981c00d6488003001618004030b0240941d602c1c180e262413800c041221400d8040c6c8070b02444060a0f403d04022006c0b8081642040b02d4943c070072020503400000f045c14026500d00c81d800d01c040e0140100585540c1003624080d85038107281d110280402044040c0019104a0000c1c14801d0b68210402281690040c00701401d084130303032074400c2d54028800c10 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 660032086 1250 660030836 660030841
    0x60a02150c0c030405130902150712172d0f04050f0d0f3c1206030206070224030a09030e0402030601081b0706060902120c04140907140c0a0b 62
    0x10300d200640c0c1106050b18000e5143c18200001d0004042c08900c01210312078030b80080c24016507070382c010071011410584582d034844006090100c1a840c01c440e420040c06287d800240200328031002642d0711600600003400070441781c0750700c1800d110020780070070203101d1014140700d4030400141c15203000300c0c0a502280c0ca03c455054440f901d5000ea2100c66001c02d0300d4a50b59401c242c05900e80081c0840131800003000900240c0300c0050141305007849002022520744191120354000d8030304202c5160140080100c07a00310b901168030783c480c042000e440f58000d10041511114911099074903862104030141c0c5034101810100081c00031000d00720042505d00001c04021b003020710a0fa44110016501c1440e503480f40d50454802e0740b9000203105280360104101c41c0420003d0180000078840e00c14010782d104002030000071102c3d8007030500601d84908100803c0038020f5503001d000440c0341182c5500c0151a0080309540c426240d101c4c0e4030b0f203144c0c040b5042c4010351005c103c000410b0301890b203460065 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 660033336 1250 660032086 660032101
    0x501030b100e090a0204170c10032309070f060509040c0512060f030c0d1506081f050910060303050315190303050904140f041101031e05040f02060a0215 67
    0x1607018031950700c002441103103012500c0c07400c000d200741c01580f131910041c0340540b14200411840c5510b12000c800f9402902c90120504003503108442000280c0380411411a01c00c1c0d51040c0d001c0640c1c103840445080001090310f0724410302c00e040040a0040c503080040c0d13940c1d031015040d071b001840d1491186103000d0312000d155002d03008030341030105120b4910000e07507104005c120220000e80e049503010b01c1054800081519041014464035016002580c003c05110700d0341026110641c000d9880c070b40003490850405222103000361a18031901c5008946903403100d07403007807820300610081c4c04c00c0343c10304030008203243c3c11000540c024269180c9646d44a202007041c00300010b100301d09100c07030481a4070100040f0f0701c168091303d1660700051011a8844103800d4104448005403884603845820009020030030403010704c2c80c0d0b26003a007801c0502c00349a040481c3c940d282c0024503100d02441d26000000c040044401d100f102661340100400d48440d28030744e00941d0351000e004241d80069005021075a83c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 660034586 1250 660033336 660033349
    0x20106081506221109120a05060c0705190f12030b060406110307140616020f0a0f05100504030f0e030a082209050109090201031b080402102006010501030b 68
    0x9420340101c1815191200000e002d80c1c1044180318100045140501d41a014858051441c0c000b00100016031180301900c05c210300c08a40d03d100e02c0580d0301410031000094404159298017039241c003456501d4016070f04000d41000e450004005183da4001105c900f00007280d42c000d01c00c0c60058a0303452050030060000d0341181c2901d00d099a21103410310040180d24468003400110b07451043c140c904049a960350041c1002400e070011040b600f0100c100902e0301400c4c407880c0c0c51062503200a02e0705040710805e541d1143e075008005090503650010304010f001e01001401c0301e000b0943c80400c0700389000d040050015000540c00300c000786007808036000a207400500a0f2007950001c82c800e2030044901010100f50f00b4262500c05400382e010400602c0100520030340303000340740c0e076040450702c0015440010115080316510640450600100f4026180c5c0326682d5684554190f404500e24058605e0071317100324200e00403000c4c205280104809004401140c0c40d41220f8081c0c0302403000d100500c0070801c0d0b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 660035836 1250 660034586 660034603
    0x13150e070b03100503010e0d020f210a09030b04140f030a0503010b0306040902061b10090b0f04080d0905070f0605042718110906030303010b0708090f040606020d02010608 75
    0x880d038032004003406000004001507401c41400b000031121655550042429107103146680d080a0f040074403a024080d40500041c0c00545450307003e024031110291120010a403200d5080541c50004628801c120380100040c81c0a075410610207980340c606843e00c0d440400041e0380003000c502622038103405410b000400c3d1a8040c002d03450300d5085a081c0304c0c0070080c0703800003007a80340d0294031503014401684404004068000c04c1c81c6082d0b1117280e02e41140c51501e000d60038810429032038012a500070400009409030804141c040d400c081380c9441c201203c1c0742c06101100c2c0c110502d4640e00c0c41c10000300240b0802265540034420343c03002d50741d80c03060380d00d03024601c1030042100000103003030414420301c0003184190791250b1000460740c01045c180084801c008808072400d4420803c0c1604031315015210a90007081200118915030410300c401003c0c6c01501c80040c24010b020901034130640e10355030440d0b0b08ca20003a20401255944040081d030700da03500720100001d5482c2203008a070001011079040c5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 660037086 1250 660035836 660035861
    0x70507080c0d02091f0602070819020109090b031213030203010b03030307091203110604120806031b01050708090d08252d1208071209020f120a0b1315 66
    0x124200c40c2c0c1e800340080ca580041200e040f01c1d4440445c1700c0d0341000a00c800d03018040b258000c050090030710a9942c508201c4907860603101c159422410b0040c3c2c3d000301041e0a840f15040080b90400100011918142000840741715055000c01c0c20a4041c01803180403046a008030000c0c40b40c0d0a000c400c2c96140d00c81918400e002545501d414080224a40d5000d0100c030300ca450b00d0900c00621121542c00c00009880484c2d00582840f00c0e0400715034807a100310380080c3c1c05ca002c1c01182903402008a02541174020050500a02003001c800b0321103020161010000090300460500490b4500720f05107501c0300d0710305c0e09111041540311800b84500c9600160960f07108224160f03900048100d01031341411b2500c80320382c10035200508000504080b07007010440c035880e156a404c5050124002c1c2c085c1034084103907541245402c51000c00b6994011030b008059505881030100161504061800e00445201c003500301801c400611804802d015000200b00b4080d0404844038030300c40b0b241c0002e503001480c0aa = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 660038336 1250 660037086 660037099
    0xd1a01030605011815051902103218010e06010602061003050705010e0418050a23030d180803040c030c0504020306010e040f0f0c180e0c04030305070611040308070507080c 75
    0x602a10002185c102400401414902c0c200741c50100d0803108000310030300507001038002c8055112600302a01401c1041100c00d45800d94010301c00c1e807403200d2041d80003001300c54500c0b8000443c1e81c1250480c8031350000d01c0c001c0024800c0165440310780c1d54800d803c3c4502c0005124150000e000e409010200405903544000a440d409140c50300440f00040d00600480d4440d40d01e504c07480304840803c054440041c850f8019003030050007410600121517482d1448142614541e910790062040441115801119030300001140e0400020100305074000c4c4d000184690800000d0109009841c0002d60440e0710455030044030035210f038140400c4e4041694110b000c40c4c80c48100b80d075207107416045440181d0403541d000070360ba00e00007070702d505585a100c407001c0884d084503c94941b0000004405016007800e00e50540300d414481d0200c001807240340b0002d0200500450f070300c0c0410003e0703003146900c0400740b00900d842c1d85c0c0301d04100c0034541c01500119007038410328200140e942c03c046080c40e0754800080c0b10 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 660039586 1250 660038336 660038339
    0x41b061403070e0405010806090d11190c0e01061e0c0803010303120b0604090212060307030314031312030f0c020705032a1c02130b0303070807080d1a010306050118 72
    0x3400403900007800c2d010501803400e010b48000d03242e81c4a80c40c02004050014080c40c00c0074140d860038402880313009020800d42c00780c02d02c0c0c00c2c04005000450900b09081c914064400c90034410419181500070f00d0325140000c00004009503c0040381c080d04010744030300040601204804d80c1c10000000c2c00406180b0240300400c082130040c0c800580c00300d11088003040302e040d90f000044040d40b00703401080c49503a01141078904848000090307a407240c03080e4018000c0f5415a20090203c2c580c0005529814800000050710418400c82451965030b104182c003040c2003080c01d010700a004200100c4071244d184c04010604980300003403120880d4000303000340c020b0801102150511000148603010114440030151980d6110072000c609140c01e0f000203035003031030704500c108422582c0f04403004601d10b081074508281542c003c003c030f610080c0c0c040031055030740c01d1506e01a0014080c1035680642d652600035440d0400064101001d44908241d80130000c45460f82c005449400403041d5851540105080 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 660040836 1250 660039586 660039617
    0xf05070515061c0c090605011110110f0703021506041401140103060803210112050304050603040309170a0605100807120203030403150b030607090522150e041b06 71
    0x141650450009011910846050710203581d81030007549088400703004e0180c080007008454420f04025040c00d18005500d1a01c42d544a6902d080040201c401141d83c0c103414a402019a0122201040802c260649a00044c14040d480d40e00000100e1503d02441d0001a12864280305040d81810246400d42e00c0340d0070107034821018100840800c0c181580c500340455040d60410103001c1070848140d212404540c0d2035131000c03100c1410390241050038503100b072080001d0004030a9409852043c0d1b0300135141c0c2e0300c500301101c026040d5480006c0c00c0c402e240040420b00c40210300356904a0107400180890740b15415250340360f100c1c0d81329281f015041030b0341c2440680c0b0681a0904600d0009084034146030b01ca4a8404040041810390010b441d56181100c546080a100e00d5600003228201241d2161a10005c00c146614004c0c5060440c44600400e21401c038060384101520300c0300f070040380e12003900d4200103800400181c50603245030450b0010b059812100c241200c0580791180d94070b19100b070301002d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 660042086 1250 660040836 660040873
    0x22030c0506190e120109150c0e030607050d06031e12050406090323010c020604060f05010b0d020304021210150e011d0703060b16060c030903050f09010504030609120f050705 76
    0x5807403a0710030100304501c4213140c2c0074014030059900a60210140e003514042c80d174110303181d4040d100180400c28400a540765400b187c2282c0c0900d003400e00650f141038102c507143c01804150001030403001c01440e501c280c05001e590744404948100e80881d02e5046050060314903010f24450301e800030340801c8060000402a140345950007a842051000200c46120b03102d0946094a400c1d200680c0000204002c0c40b1403805245100200082c04011550501d00040c2d5036208140441c0541500080840c01319107030100480ca40d804880c1c2a0390a0409914000c0c01625550080c42480c8600030380c08108554079440c3e56040b03a600d5441308074400319422504005d00c00052040d41410343d590030020300c0c000200300520f850045540c12440c1c500c1d0625040e812105c0f0f0f01e8080040505c0c0214000000350801e080301d40e40c40d6020645501c42201c0710040b582c0703100b2504014030403800d10148404020820010845003021900c40e02030744a0b000004407070380e000d030540140c1194040001c240c425501d92 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 660043336 1250 660042086 660042107
    0xb07091a09130e010903020d030507050301051210050a06050a051801120804080703030905040f2c01060f120203070501080c0304080703030b060c0f120711060f22030c050619 76
    0x5003209001800e007100b0001102c00090002d840750f516805282d0415a040c0002041d89240d400c0400c00340c10700100043c40390105010782e43c00703015104001c10701080100082184071003004406d004626280406001804281c410103000340c92003d0041454640418000340085113040d030410396a01c1c05070702c1089858160310544800c403040001041540042c080320300554040c3e1070340d0700e40f07500c0c200601040b2000f01075081c61052800710a002501c050a1020304400480d44242d01c202c0320046e102c83c0100340399400807194008174a800665018112440700c41c60307002300c1c25200016954001560814403c41d14034440d55402c00c000360005c1c02e410f0107004058001d1038002440d040705c2001c01c0d070035804580d158424ac0c2c002601d40710120b00401c81929014112046241071030400d958180f035400500c05590700c500c4000c150300d09403000350401c0d1140380800a084984100340c0b5200b140e52400180825035191000320008a05822701c80e00b02c2d00e880b0740034104200001b840000c12964a0441d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 660044586 1250 660043336 660043339
    0x20a020d08180604090902010e0f0d140f030a180e041203091b03060e071e1a0c0109080c06010b07150b01090e16231c06051008040b07091a09 62
    0x1000d04482c20740d25400041c2000c0d044c0c4082c00205140759000143c030710302c28880041c1c45851003800d8070340592209420201c507941d00040c203441001443c0390013400d0500c010300c1465148004140b07441081c0c0d0000702c07940c500d030ba804004160b0544500240c2d40324001281d003d0003107a0b500102c92502403180c6d02981102c0e02455900700341c2c079040d0a03070020661055000340c1d842c81d02c5000865801e0b1080c000b140091170704107400f01c00108031050041c50341504c0e1042c000f048080c03603800d01d00f0a0702c0104540212190070002c02c00380115250850050f04a9001c9400a100b1440040f0b0a5440d54046401f02900030900840b054000c00280025100354492141081300380e01c4001703602ca41d00c01c00c19005403420140c500e21172003d05402048400d81929a500884d42020703034014003840b00c0e049a4211308c01c0340c207025070b81c050690b04401030314007030b0f100d0ba4002c45411020104154032000321405144610001a41c580b41d22000726284912802125204807406d40d00c4089506500d0080c00c03031000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 660045836 1250 660044586 660044617
    0x303072f0102030f0a050f061507020604092c0d020a020f0301140709140915042f071e0c17010915020a110d0215060a0b1803060106020a020d08 63
    0x4403816150982c2c005480c450031100e03400007803000081c010f021b0682d000000c248403850502c1d00100041412048135180f506503a00040d00b10155141e580485000d001005024001e40c0305200c80c40000b00302d2a0300c0140e90501440029400c500081214050f619282e402010381441c10340030002e030130022000555240d076840d03251000a5040d074031039901c144860303100c000726946032106690400c0380d8151003e1040d03687d8400c006952004080755520741070250707030004044c2e25681c085007058042d10a500d10981101e105d107046803005500402d1060710582c04178042c4422001c0440c42c00e03400f0100100302c0c102e04541405540070b160414490704000d0000400e0780c180b1522490306c0f42c219000340030406a00010307181c82c4950049554044d1480a900900044821800007500c0f44a1002c10305440f11141001c42d905540c0c4500c424040c0116000c0d065554100005800c103400307412035190300030f000d0000000342c102e00101d00c00705e1440c0c0103030003103800010300d03594050780d5441903010030031403403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 660047086 1250 660045836 660045917
    0x3470402130f0c270806041407030f321c03060906140906090c160201020304170105100b040f35030d050c0f04143f030307 54
    0x218a4060a4110107251300c81c81204032907408a95043d0916071080294541015400c208070306000852640c0242c00024604401c00280d42648c03c10300b00e40e0014110103c0d21400c0800d2000e0340160088034543c081c40c0303041100045119041d00030b41031503202501d4100401e01260100269039403c00c810540c0340c00140741d03807905000002c445541e00401946c0074a04611452800c3c0004015001403040781c40340c0052800840510240c454050b0000f07004600700003c030110b9008205440142c68400c850240920460758a40d000f440200d548044000a41c0d00000300c940c0d01508035015035003420b400b104076a04042030b100001940b00320100d04002c8010b01c00107078040303002501d450f8000a5024540d242c0040d4010810307540060510842024100044c4000110f80e41c1214102e40d100041a43c4541c1e0701400101d12071584c405c04c0d078001c0100d4010b9002c44402011204441e0321b05070078007284400101c00c40b075980c08111240c402182518025060820001c05100c3c24084034810450707007070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 660048336 1250 660047086 660047111
    0x1203030b03071e0b03060306010302010c06020c0a060f0c0806060a030b0f13090318180506130504050606010201060b0306090112140304091b020109050606090c040347040213 76
    0x1185580c0300e003e05181c80e01d0724558000e607100640d002483d20100060844c1030820009032140010301c8001c3c140b103041208841042005c0c1c0548500c00103180c140d9042c0c24050030000c0140451418a5070b01e607161035014407400307001d07000b030030f0041c0c0010b8800740c1001002001a001040c00f1001c0705e0740300d080c58030001d5555551240c02c10018021460125800da07551030060030a0002d41050b400000004a0511803030305440c5105440f01070220740480e0503140c1001065450160300700941e0818201000c10003031010010307002d40039600a078020004690790300181d00150109403489036018100000402104d926190085201401807003000e002c02103c5d2034003451940591302444d402030726800c642a2241001c690b2140b51106030000780041040c2e5a00d442d2500d100030216442082d00e00c000c1880480450140d401455102c114040302c0c2d042c4041ea005200d40c0f07042c2c0103040c3e02c0d081800d00d150340030051b480c0c2804e039003410801c4415260ba82c200304c0c5880311207080d1440a603450440c41000c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 660049586 1250 660048336 660048343
    0x60e0f1b04090509240712200c0705010801090c0509191d01050108010b09030a15021903020c06060d020d0b06030c09040b090705240708040906030302072408011203030b03 75
    0x919920006042c00009001d119480c101c0752011005c0d5809007108110a042e00080b1700d4040c8000c10900081203860005850703206032a520003e0f1070044041420072030398400041c02c406884007601c46010707581e6038842400564001a01060008505002031091410f04026000c03841200c8950410602c3d100e600683d602c2d0030b4003020300d01074003c0b4401000a560084015405040e921440c1e904d000c1d01e034408250b9800815070000c20140a0340d80310703122492a40e0684002d40740c0010032500300b29603118002c02335003100a140946000c0c00380803d003d840d0100d1240185640a0300404501d9030720b0b11000ca10580080c00240c16000d0b0711213070801556005070881c4103d01c144011006428030080b20303071034042982c001500030804e030148a80c040c40d40352800c280000306000320682c0c07100b640c60140321a001d80d500ca040500d0030040040704041e00848c550b4140c5007210003800c081d11181808001502040c0030100c0410303010b03001403005070301c2502d040c84828082d0030003140b00030300c21010a14 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 660050836 1250 660049586 660049591
    0x50a050c2502031221060d03050d110f070615060e0910120b093913020703090e070c0819170403030e0111030405061512030319060e0f1b040905 63
    0x2030490000489800701c178620401610780c008070683c1546180b410401191240e00e111402070140b2030082072900114106e6000318841c10343c04000503031208100741c14640d442d0040501202c1d802c0c01d00c0b404c1180300c0d82014039075040360400da9032903500151040920081c150081d280c401c1c2c85201c11000700d102d081c40e9040e920600d1145c0b1040c1500d11f00680e2460400d2001c1c180c00c6203068507819400c00c5d099040d410103070040300c400d08aa29030002d05001031140d01300c54002d100b8650000c2000700625030030548880840c0c444407005c0c822555554400c446c80580b000700241560020b000c0340ea00341401d0000c151081c5254104401d01e180805038064450100301e800310000780c0c58001d40b40b02150f0a0203047c2442c503440d40c0590540c14142c2c0ca00c3c0e01c03100018144642c0c8008004256100e82d03c4801000c12045503200384c0e50f07607081901003041d070030140c0a0301602d22402c1240000b90040568a042d02c1440002000f00300d031f4580c500320f106541c00403010180c41d09400d1201161580c0184074550 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 660052086 1250 660050836 660050863
    0x106051b0601030f0b09032830050c0c1f06050d061b090b04090504060b09010f0509070c0b0f0901110a090e01050406030308010317160f020103050a050c250203 70
    0x2c0c0d659a0b6203049440584010b06d0340501c0e0300140400301c0d0604201c1c01100c2110b00b0504801105100c1030000c58001d42c1d8056001c002c4002100d201c82002811901600101000c0300140410380e100701c2c1c000d206200c0c05000040503440074141460a03007003a45000c42c40c2000e00400f09a2540c4c800001c1c200c000d02480542d00d2031b0340c03200281400001c0038841841e24000d81001d000702e614005003503602e40640c1c440d0f04015030b10740000604000301584441c03000000141040361550b151403140b60002c1080c000d140c050303810140444c0341d03076004e0258401c08a9228800c6142991788030000b51340c816001d0701600a940d03e41246544215800000c1e0888100c681d50ba81017040c80c0c503408020b0000103034070081c0500e00c0c3c8038051012a6002203a00d06581d040103891181940a0b00b564500d40f103200c4d1010b680c3c040744014001046031540340035504038000d0341c080c8501d860340341c4148200c6400303888205107a641006200d40c550a8075080c071818441c151600e0110072250380100c0e00b0000044c1084 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 660053336 1250 660052086 660052103
    0x1205030a030606140909040606030b010e0a06050402030f06100212190201060b160f08120a02300720010c0305180304030816020609030d110705010806090106051b060103 74
    0x140140307039051050100800840c9000c0e0406002849040040c0c414055102c1c000e5440b50001014003c054100c01c008544c000c02c2f8021641e51502d452101c5e100650743c152440c1d04002c80040c080c44c190081ea806502c1014034010b041e250303441049111840c000100040d030003411681c0c007200c0c006001a080d05030990031540f0480100720701c020301710703091908100e00081007800308140c0c01501907811b1300d1103076003c0002201103245080000d001c3c05400e0403c0d1181664104100040040e83c01402102e142c0d5011607000c95184401c01120003440b6803012044d001010024220501c5000e00110001c0001d000840e0341c0509004682504d4410001c00042a10750003031020b40864560300041d405c42c1e0710b01a60070623046a407190203601c114000c90b01c403076002070115002c1d13540714001ca0f40240070040483d4030036080071001610300c80c44103070300c200917000e0300c000003446502a2120300d128000051004110782e00380481541c09030003044c100d2040000070b150300f8117107000c2000814061405020325 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 660054586 1250 660053336 660053347
    0x4090b0f030d030b240a03020c160b0403030f030e06071b2306090a150507170a05040b090c0f100c050607020f3a0519050301150503160503040606120503 67
    0x1c0c4180002c1c0084070001030303036400207170803c107840400035118201d5403840c0140e13440b10710380c600343e180c044034402d00602c1c0c00d4500000100c4401c2c0c14010011644603480d0031605589401c0190f089a4908401c644140c0120002440b11071203040a20040c0c40104103806400f4102e03100c1000e9401e600030038448031419411108000381007000515880001c5031300a00d5070104560301c1154840d6196400d03410940c44030042440c10f8050010704d10306030040c0c2c00007010303444c100e4040c102400043c0c1c1d00703840100d05070000c501001710100b4034100449001c0d01c030320074056511050103031818072918038204000c8111020b0300000c100340130141c040c0f813427a4000c1c008860400340c0e0302d04068042072030700001c01b003102241c10b44d00b0451811799042c80a200d480c01900d407800c0c101303840920074101103505c18100c1007060003190350407001075410380c3c201300121041d06000c6a419901da1206903641004641b01380c6904e0f00d80e0b440b80d0011a1701038410b8901141e00c0b0340e5600c002c421018400c0f000c65a80d08080350 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 660055836 1250 660054586 660054589
    0x7090e0102090a380415020d09062604060605030a140607020c3001110a0207050909030403020d06021908040b15090109021b12090901080303040804090b0f030d030b 72
    0x42d4003621a11340801c01401380700201407000f03050380c03240355a60044a242e0141011059082d100203207100f40144c6211130f5070f000300a403600c41008030000403800060b0f0100e0340601c00c480c0360303401410000d103080400d0301d0540304c0c0202c0c030b44c003e100310780d0141c80e194040382c2901e092140040c0c80384a000b04440d134221800116041c503000a00c400e04541c041c21012001c0d42d590b081c046524000051046100d0740d401f05000700c01405440210019800c0c44158510406c8400003040c80302c0040d400c0c1e81003180c0714410012054030540e21030030740303a006000910151602c01c400c152a14030030800146410201a0104c88500082e0415004078404170200002d211151810b80d40c05030840c45030014540c2254000b5407100c0c41801608140e03580030498400b25405008119801007200d03040700c42ca00c6000000e2211607201801c02c1c1e00800e110000055400c00020551f4081c07030f441190241481d04100040b0001c000c0c0003800ea510000b007000014039034400748003026620407140e6000c03070381850140 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 660057086 1250 660055836 660055849
    0x201b011b08090607051e03130507031101020c120c06091c060b180403091707090e0a0201180e040609021513090606022e1b0203031006051804090507090e010209 70
    0xd02103401e0001c10082e070140d01030426180d94405a1546c1902d4507034441c050001ea5280c80e50f04003d00b68801d841003c400d1080215541c0c0da0804243c1c21030f403641d0a05010721803941030f01c840640c061380c001400607040380f4284002e03200d003500250103007030762101d84800e074448103552100a80d185503446558180c1401d10800082075030340241030301140c5041c1540c00403c1403015108640040c03007202131401500b0010710000b802422110710078002d8003040305080e522815550001c03800f259045501202044452400200b00c2d480380149c4201c650351a1250ae002d0315407a0800ca9100380c0181d443c0000d8280c1170043e2071207901a008070014035040400c91030440e00c0c0741e00706a00303544c40b11103c1c541220f010140d44101d401260030b060005000d070b002901c040d000015030411140611200c0c2400568000302851182d040e44148400f0b103075031203c1c00d42d40d6224206d000d030107080030801846601d08064122088461081c4101d41040340d40d02d0820b0226031210710341c219965000500c00ea41c614003007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 660058336 1250 660057086 660057091
    0x305100b07030806090402130c120e160314031c0917030105030d03020904020d0912020c0f0d1209090606030209010e0315010e070c020310020d201b011b080906 70
    0x100c00d240000741d4501038504030008200d5481103030728000150031500c40b504890301c94161b03588280f01c1c00f180500c0140010030900380c041d034a249020b5640c411590006059180d03a13125040880d246421a159142c900042e0f20307140e08184810800d5140010245c81c0e41c00303000d0180a0005203044c12450400000443c102c59000801c10900060110f0f507004641c40b15401c01034200103030750b104047d010602a028400b1440e01d01494610210240300440744020381420250307094a550107003160401c203804100d4070700381e50084000703041d05000a540726070034032404109003080d4424a07521002c2c40b0903a0066009400080c1d0046000c042c2560030045510065404401a02044611100119501c1070502c515042c003035144004c100c1550003010070406d0030360050183c0301d44c48482041c68000c0e52152074842c5201c0e00e071130380143d0408080045e201a88100c0d0914926058a1000c00c0d4001c0c11400740451640d503942c0c5543c4a40307117801b04003003002420340d2642030b55450640d54081c00d14100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 660059586 1250 660058336 660058349
    0x601020601030b16030917071406041e05010b030d090f062d1407030c0209060906030c06031e04060c0306050d0507030204050c09130f050115081303021903030510 71
    0x39000600004030380f82001d542c0203031132181031030388402500307012000f0340150b41010b440482c1c0442c0700440102d280000700b01c83e5001c0c0c0003071007144c00c03450b50b02a500c2c2c4003103078090300f64880c0703044071000404002c40800d4407034010800400c0784418840081d0038003203251019004240c0040c020841c045d50024054003d00150804c09a520301e90110b101e04280d00c42c2e06c426140c3c655611701b6285174000c022041c1800100c26010340c454240b850094910741120005074450f00e410b9002030391516140380320f81d102c0c04000c0d002c0d1007081c003800244010398001401c904102c100c44a610100300d501c4c850740700d00c102d009071800300f4500e0307070650041e04503009500724600850f45000a40c01050002491a0440758147c800103000d60f43c0c00303441150742c0240c0c9d46035944800c4401010f001200260800107018004500412269a076030800c0e604a591440c030750400f01e072103000021520f8400c002101c03442c600070f005690664007040c0002c407110545150480c04a80d4030014090b02910841390700c00603001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 660060836 1250 660059586 660059593
    0x150212160e030a1101030603150501051318240e03090f04050103020306010b1c0c230a0905190305150406050906190b01030b03010204080705010806060403120c052d06060102 76
    0x201c07030000c65110515814080c14501c002c0d02c5080b0a41d01c203600103801140c02c503a8072425035080e1420b00b0003a16081c0b040d18442c4003000343c284034000c40e92160040d1000d09900e001801d200568800d00c0b84035013900c1c0da04e511040c01168a55491207030140d42009600400030b15950001d200c100152888410b0060780100d10784401400180c90004d40b4505407501d048050340c503120280303094601c0700c91110140413024101405c02c3d4456412058003c0d400344e10a504005201d07074401d01807042e006014a51000804112081041c0c2c2001041103c212a0004551000c40d4413520303418a4841c0340d01c810150125804100001d000162085070740005000c00030b400c42d0300340715845903068205500310342041650780c83d007004e141e80283c0c05030600d40d4001d002591903a03903604509480311441e20402d804140c0c20000580d0310314000084401741ca0b8054a40c13182d14814040440d442da060f00c40c00c8940f4410200c0c06041e0f4920801010000b601e40003038022200780314410103041c2007000d4030740d505651 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 660062086 1250 660060836 660060857
    0xb120303011202061c151814012303070e09060c03070c0b180a0b16020606030703030804022b03030606030902030705100504090908032a070f15021216 66
    0x540c4502d00e9010740e83c04403101510b82410702500c0940803010380101442074601942800d1402e03141540204454840841810b5480003040001c1a6814070607140404a007000041c4074241c2d42c070040c0c02ca04100d5001680344900c00c03001003840c5c00455000b01684030958020003010781c0f410450140d014075601401ca0030741c1000040a082025160001004200c40c10000b803d508090102401c060400070200c0707081c0c0c103450409031285030b801d0b15019003070000944100301031400050250700510f0058010082e903480c40d1003c0344c031030001910490303101da100d424195440c2c0d21000c0c400c41d209002400c510610707860f45400340c111107040c0e0042d030505003050710040241e6070210b001e1045940944403583c10000850048980d44074070340003400030618044c200400e01c40301e03c02a622545800011f80e10382200c510380d0440d1444200200c4c45181d0003040444009000c3d808180044c2c0e1240625454840c0440d00610990b000419414100791106d0200040440c051680e0480080282001070001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 660063336 1250 660062086 660062099
    0x20a0b070825060216030806010c151a030f0706090e0f060409050c1002010209030706020312190b180f010504110f03040203030d24050108010f05091b0408010b12030301 74
    0x500940140446203071881d91580852607500c1d003404242540f0041c115a141000c0c00660202c800d4107106070005642440020b03603a50003807090180721030300015608642e40d0403c1c4800080e2040d1410707842220300b02c4095140d25201007165441d03241001c800b40142034102040104600c40c1a03203d000e0412856052240307101c0d1400346160040c1d402e48010031400910b0911074a841d081d40412a0441d00b04e51528900d01e42c10b5011b1f100e101005c40c00e81d03801a0340c07140d00301d94a0062400802564080b04082a143c0b51295001102c000403240c0c049000c4142c0d400081441008400c0c9082c00d481120801a0102070059042d000d04411a002c2107100c00e060300c1c880c030301d0103814059a44560000081000c0d56400c05c2a18560340c0950f41c18094140c51a8540080c0040e00c80c034018080b500384400724143d800b03000308906035480e44581c0ea02d040e20700010810003600240c50500404c400c0c5079042c800c0140c4c80c0082014000c1d80002007000b071001014001004620340914410341c0041c001406070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 660064586 1250 660063336 660063353
    0x60f1d01090b0702030a0b0114130509030f1b0303040309080607020d09050f0a0b031609080619090206130305010b010e04021c1d0d0e0117070c030807141204020a0b07 73
    0x159181c00802d540c880c80b040c03000ca803803d4481080648000c1940380001038451403c801c0c0c08009c0c00035030340005901c840040100c241c48003901c00000b95002880140f4a1a0f22030b8064450b58817030858030b01038102121815070640c1c0c02030b10b0540000d12401c000744a014002c00c01c05030413581c2031000b0140c801070204000c1c201c518500410740314604280f00c0e41101d540b4140400050080c110a030360ba46e0400054031424546c0b20320790000492025040081c8211003c40c0151191300d20040351040b10002c1e00c10540100008241264860003c0c080140e03581e41004400014511a000005420010070000b42c200c14403485070903c43c600410004404194502c24009801740300722022486a40040d00f0050042c903142000784e05104411510781110350143c0c05c1a007803071080c0c90b40400b00c0e842038070384190343c4400c407140c6022940c0c20b51284000392140300c07555441101480c01003000d140440d45134840f9803020241000068408040c041545483d40f6098002c04505040524005c115560b01c0b00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 660065836 1250 660064586 660064589
    0x30302160b010e150d0c0b030703150b0c0105101d06040f0c030911190b09030c220f02250813030c0e0705120112050106030f030f080604020c0c19030507060f1d0109 72
    0x580d0b0101201003580705019802c0040d40bc2c0106000c004450f80310803d40d001500014000e115a40c28031000c1012132000d20300c1901134a5403e14240c5012043c1e038142055920040c0c440b581096440d226641088078a100b1030100300f1513030f9000300d4411040d050150720f07a1582c998441c4601b00322592076080303119041c0c1d510100c40d103034500240c8496002000031b0a100c0c0070f1064a4001c0703043e0550425204d07030001401c21b4880c3c0c1002c06c018131507000480e20b0482c0104000309280f0040b14881841c1c0707408a50070b5202062148031583c0c40c00305182c0d03810f10080d100f94400c44030ba4004a00c2408030074030f00315616a0103450b41c13802600b4081e008030303904c011602c103102d00e1610350656110003040c407100390400ad01031500600905141c048a18005006064100c2078600041400010800350300d8203000311400400440002d0110164450810840445040b115482c041001c100000015402d100040c000e0400d034994845100d4500b4015000c0d030302c408180c25000c91600c3d40410581c1c3c00001c00c00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 660067086 1250 660065836 660065849
    0x2030702040905010b12060106030513030c2012100b03120342010f11030d02091908030405210703080309010e07090e0106060e0d030302160b010e150d0c 67
    0x150140b400d0820a0041404480c0d80f500300c2010060203079041e0000850354100e450f42c0d078003001076541d440801d0840c090002802000904100c0403c03007c115407561020310610315002400305401150001125201010b509035015007140d0f0a0000c5640c10f80b25415200e641034025001d01e05140007040e03114813004001c68500300c030b18500d00d00356440e0410348100c80c071080d078611482d145601081141042d4250007a0380021405d20b0800782c100e11840c07900728821101c200942c2041c4c50f504207a0301a4110804ea40d07041004403154400e2440341c0b81c09031009103c02000f03150350310700740001e00c48411810400e180030382e0300c030103184404400001600412243c02603800342e26a20382a0740c0e940908088170341402d20744503440340815000740380d611501c419111a002080010742d00d120070388071005800c15280e0310031074040182000c00d0203500100f480250340b081318880c0074038550b81d001581c80d0a0f040075092041e8002080812040341d5060003000d01e00b2661301c1302d00c40c026a81c101d1226858042d10 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 660068336 1250 660067086 660067091
    0x1104051f2315040905070903142103130804090b030118080301052101020c0705010f0906050306210a06050406060f23060c0d05070c1401050d241202090a0204060203070204 75
    0x100c1980e200c0c2c02514060051050144814181004001c00a04007800103803419110510481c4940c04002907602092070051040002e00c800e114082c94135400007440e208668a00c24401c1c80000e0202c40144054640b1400c002082c22510081c513085990501e80001c43c1c0703150b443d008011509150959045400858241c01c034030b006111781200464120741070700704645c004900d666400c2004507020055907002e82c0c401000c03110203c3c00b245c14120078451600410000c00106d12141050b26a9806c800003030200303403500c4e03000020441e103810b19001c410303207800e44c3e6141070204000d40c0307000f04c030000c0000040d404503440c10b105070ba06959104c400e9084c8180c0f4103080080b80c03a00d5450a403109500d010041d258988180c680c00303013443c6d0001c9404c0b1032079881050081160410000c1101d602e24040e558141407825a408400c0108584e103013614909001002000a6000020300c1c40040e00002005201003c02403052121848014001c2c0c03a8003401070100f417060641c0001a03034138568044030003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 660069586 1250 660068336 660068359
    0x70b060102010b06030c0a031b0c0318080d110d21020318060106090303080901090b18030c0106060504051306060228170c1608030301030605041104051f23 68
    0x140d00500c3d551020036041031003c400c0020b00b03219100a0032050209440500008103105054041070010301e0841011482c2e425030100400e101300100c40c11019041071403280b041c1c4446205162440030904280054007034048401400020f0065140781c1006003443d00405101d070801003a100206117600c00802e078040009903644246c01c1e4844c1c2d811040310159070403944c507000003e0a2140030301060f0302186001c0701007440010144103003880d440d040b1000600d16201e11249041508d0300e8415110b0a100500101140800c2882518020925521865520b40c50724090000c07450001c2800e43c81c0c0c40c80c0c40c901b000030313136008540880c00c103806407410704114800ba1040141c0c05d5a00744c020741410700c0300708400801e4400300010401014281308482d19141c208500f01034004c0107000e840c0503034105000403c0040c000b6001290842d100310104103a001401001c9412a9402c50b207046604400c000c03814403980c4100300d41009002e4000383e4518001c02ca455611b100c0b00c095011030b028516a020 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 660070836 1250 660069586 660069589
    0xa091701090c0305030910090302090604050408071505060a050d050c12120409061a03041e02061204050606100509031f09150603060f0203070f0e01020c0a031406010515070b06 77
    0x4401c45039030b0300c030707110200d0951242400c980c0ca400c04100580034a101007417000e17030103003e440444101c0e43d000385510400c0c1c2e030302000e00002c1d0001402c1110b251405200c8900007401e548020041e6407004080050745150541c02c001c03003084154032a60203500c100c0ca200001c00e00c042046a0604415101101008104405c0d6498152425802002c51030f010801080844594102e107044407400d00c04092129400d07550040103100030344001344140c0390195018080e44984130700102c0f540c0011300e4035050080b199145140404111012a2143c000d001046081d180400014951180c9072800600300010100847d949510001080300383d10b14030a281e2070043c0310b5802a0000e16400b007505c0040302c0119510354086c0925000846078141464001c1182e0341c081d05c2624070562442d510380b001d200060030240c885c8a030203e10281180620100c8a01640341c0620250007580f0652514914080152100d4200441070b0401c511405048100d402400043e10070380300456001401051203455410 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 660071942 1106 660070836 660070841
    0x2031e040602250b040e191b05030924100b180909100e0c0a08070b0a0518090103031205070206060a1a0706020315150a091701 56
    0x80054a030401c0da60003110700b10a4050303040740904e031161010501a40503411282101d43ea440a000d0f000000c1880c1c500c45c214444c1041241c900d403010440c0411056014160411a020001c541d5080c02402612400e09014005501d0080014180c21400d0821500c1c00640c3c030180c0ca000406104140c00c131224031541c02c04c41c2070b119103031008101d0940005001d412642c4a4a41580c6402c0a203214120035412f00c840109241441c0340c0801165081c02c2e044201280c116110400c4440950000c0d41c000c2c50399828216210300c1c00001c09000c10781c50f5104564030910341c10001040c180c00c2040014a402d03006010b0009565032501a42c1d120400c0da0825089540040b040016008552140c07103040c03a40f072a6149020090f440390400c3c0c0e00140d0300b00b0205411030f0952071492510f01483c403140301c0448850746c14114024800b601e038044034820000d01c50380c3d10340030000d4454290b = true := by decide +kernel

theorem cover : BRFrame.Cov 659892086 660071942 := by
  have h0 := BRFrame.cov_init 659892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 659892086 ≤ n) (h2 : n < 660071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
