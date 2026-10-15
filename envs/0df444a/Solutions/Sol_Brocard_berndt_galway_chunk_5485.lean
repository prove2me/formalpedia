-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5485
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:00:47.119615+00:00
-- url     : https://prove2.me/submissions/e0ed0608-370a-450f-858f-cf7e34e80fef

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 986330935 ≤ n < 986510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 986332185 1250 986330935 986330951
    0x16110105121009050601020f0a080304140a050a0501110a020a11061606020702040b030c010504030f0309050d0b0901381807111009030c12020708011a040b09151219060f 74
    0x1a80c0f48c401403d50040e6a03040b1082040201703018000840d00030348117001e481d1811580862545c188030407001d0442d4590021000c3c8000d1010034000d08807010510092030b80380c0805070b04065900c21440c4001051703100b20015601195a562041c0d90300e40d00c440851000090a500d0014000d41c02000201c2c032691402444004c5070030f0003d0004807107441030f16800d140034103540311500d08101c0c1d05011810403c4911011583e515401d46081c00c070b5205031217003e00c5050810085003507403500d0340750b08050107198200c0744111201c0d91545901402e140c480d0f03018001c501010031682510134a041c0d0051402405214125601406068020749a10180c5011810341416242a10ba49880150001b5109188500422102c0001d500d032220240120781005039500031260944140511004056425680c40c490b00d0600c2e018800d00000212441d000620307040c41d00d801076a2409412a01a001c0182e081c0f000d00301c20448644070350200015000461790502c1d25001034400308500111040c204501 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 986333435 1250 986332185 986332187
    0x1521140106032313260d02042310030c020106081203010503060711030a030f0b0406091e05160f14030108030a030e2a01020102070b10031716110105121009050601 71
    0x90a0265120400d680313200b03606922444610840c0348844400c2c84240303140e209000804100800b4076400c0c0160140c0c441e40f03007140c08034407110340800c10656244034501490302caa4a008580c03542c090141400101c4000c582012401020b140d0050b81443c4940301d002d02c0c264000300c01441c100c0d8411070445600d941c0b5030f102100c404100c0111041141e1080c001007900f0360082d0000140a450800300040900b85400040c0544a1913071002d444c560f076032190300c074058424604451031540800742c14017060404224004040101042032010000c007c0b03292400a84504045510514103802403616942c6030a4a9910b945c020381c50500840c0c5000c50300c076401e460104501145402e43d0f6102c1224885c80f43c00310018905503807d01c2e0440d582000b0139400100301901d014014110780c20740d003041500354608020360b901400f004c8a040304081c041304000c47d0856096030080c03503114104042c0c1401c0030b001a01c0d2030181c64040341440003200e00700012041d01d140c0c881d04a40405e08244525110000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 986334685 1250 986333435 986333501
    0xc071722030f0b1f0501050a05160b010509150d02041a09010b0904061d06010e0a3203161404140108010e100605010c02010e06040f060216152114010603 67
    0x104c003040b0040101410800340d801107000d401da000040c1040c0d4505112801c83c00c2c041a04200c04440104103030005000f9401d001000035802440b42003103122406a0800182c0d00d43d641120080c855600d071903400f02c03103d265050400e44801d01420444413941c480380003c046030880c0101070302461402100152280684203c21861070b04902070720b440e40c49a200444800c5403400943d40c00000c0d20000240960b40392040044100c024400408050360050401155602400825119500540411050014815001089400005218100e00c0080340410040d01400d80c6c0a14128100d4000060060041d0400b6200d900d110095a4400c564982101d00b1100a409420700081240c901100103501401c2220903058004001c241040e641d070b9104010462581c00c10001030700211101c21409808001768400389c80d0300300d645050a04090401454030416028021030020896080e80940705583c0c0701c2102e03100c2070400b00c0ca840d078603001e000d0003500020840e041c0003000014003011141e114a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 986335935 1250 986334685 986334721
    0xf0f0405160f0c0c0e060a0b04060203070309170304060f022532060a0504080601030c050a1a0706020304061d03130b0301050a06030e100c0305040b0c071722030f0b 72
    0xa4044d00745424500303940800000109916004000540081071000410001e40300602e81d03607000f5942c3d0070b450f00d80181808043d0384605051300c0c180d0f030040026040802600c042c0e841910303000065920f40e04080b450701044202100c42c5d1030004000b0203d103541c40b440c1109a90400b0b01203690f40585058145000300100c2c004c000326a01003041414520348403005201030019031400500b0640c84510f0f6038100b4000303038001c0744c00390041407081015091420014000744540110650030308205800760075644103020000f4000c581c0000002c2c2003000c2d0380c3c44003440c9038120340b0500c1ca00f034005408683d268002c428082c1c41c40d0314030100142c90301ea44002c590580d00d000e403c0300e201c24507001e03007078014114103d40030500b07000350300c2284141c4e2950321035203110300103a0b54040380078206030070b000b8404440603250003074090007000110042030182d040f1081c0c110b04180226681d21003000f84448105c14029141541c5074081c00020900030745581c43c0c03c0c0135000321420f981035240c0d00e4003070b0000ea0704c0c4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 986337185 1250 986335935 986335943
    0x10204050a0e04051e0f0f0d09061407120324050f030f1f1407050a030b0d0503032412010506040c0309030903121206080a1104051003020f0f0405160f0c 67
    0x131709030340740d403541c0360307250240740141049402c0480c81100c401d017010900d4440b01800d50000c805005c80301d92140c0070000404032401d0441d005a0018a680d40b24410120b0180c03040b0710090560903403512980c4440c240c3c500c000f18002c40c107504220f501c1100e02031481010310400d00c1030420460361802003204000c0c01d80c24401019482c180c8120151048025040c400c4041da40304880045076000a641d0742c8240034a5450326541c1002c048040c007100d5540b16994080d0418500079000200b002040b61740040002c3c8510f40c0f4034404120740300035000305d1404c0c2500030559101151818005400c420700503e011a400d10951440500032011299000d4000d00022145002003001c5800c5c0c81e618a41d0b91124680280003401798401482070b160190700640040e4043c80135a000c0c0304209142d0103e0714400c55003032100d820310004003000b145180c000644180c900501d55591651540740310004268083d1061000c0d24000341b801e86218601024030003c05c08035447d4918580c46940380c01001580 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 986338435 1250 986337185 986337193
    0x804080f0d1e0f052815120506070f080c180310090b06030c06040b22270b0a060509010c05070303080402090108010504030c06020c0f060a06080c1f111905010204050a0e0405 76
    0x1146221000100030289400a15540d0790940b00d0003282146c0c20406806061840741d24951030780740030b5140484c010710b410b08020040600180c4154013110340f03a0040004102507407183c21955661200c0f00090000950611a41c9402c2080208075003041d00428050082c8800d0382d1f44070306c10315807140c030402c0c1003540c480002c200a1020b01c0300c0c2005440e054801d1111541c000742d100d1040400e1100c503801007503128020140081080511001222050410400600c09900e01c1c0c07010034040101030043c10184135010400e0301c1c0c0e80c0d21800e03101c0307003684c0c002c03040b514029528180549503600586003030307018100b10000401c420005014540c021545595070303510941d130381d407284c60003500610f0030408140140e01d007015a10b00200003090162452040c00a0010f20b40007007180341c244030301516805540d01e11168a140c0d481c030030040d03665401500780311021a04a4118504242d041c40760310b414403a0002104090110550142080e1801614403e0210f0f440d69091030f102c0c0000c540051aa500c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 986339685 1250 986338435 986338471
    0x7051507030f170a270b0103080c012703171315060b0a0e09010815010e070516110f0406051c150e0f0705100804080f0d1e0f05 56
    0xb105a0035604211080d1620700b8100c850b80c03011030040d03807054810682d03c03516030b011504544007038400c41010b00c2c402500a00054099034074100300641c1440003030000100803030b5070384101d1801e4004600030040c45950100510340000d045218404402c401d43c0010a0005010140403142000398010540500c1009810103d0f65a500f10341514000718030318162118070001e640018040034011480356501d0750091825090b060284201050f0b00ca80e60341d904c2007441451494000d9040c3c4d05540d068410402103070b0380c034070342030340c0da0b20034000b084409044103000c400a1000340010041c070f0341c000300d07000366111500300c08010694807203000d950381c4400b40201003442c0c110f0001e9181d0303003584592503050b200381d060031518044801d03d218410a5810000301c01900d02e5003802810080c00046406640800d40403c00138000100103000610303029000800745540c40820042c1d9444194032001440008105411201500300215009070410304205618100455034040c16100740c003500301c2c00580d10 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 986340935 1250 986339685 986339687
    0x1021c140c070b24060c030a110d0530130b010f27060306050705180607050309100306030209041a0a09031d0a031415180a0221070f080705150703 64
    0x4041c403ca070412042e442688902c4c00e44400c009049007407188030145403214098031016002d0010803501d00ca45c2c1d0091070003043d0184e04801a204030001081c105940a83c41030f85229005100540081d14610b55004100242c0071400c9040c0340503220300607580e5543d81c1c405a070416070b015401020210401040040040c070b0509111b00036022070340a001c11007c0d0b480d111030342240c01c144c9280300041c1d0300059650000381034804482110005840700d0385082c1d130035140ca0307840c0d018560701b441c072510103140d410401c94825044000516002001c1d204a42054a805211000040300d5003081c99000780000d410155103209010105030940c5410030001150720011071031041e00f03540f55500541d44034021000c1128191075410040c1e010006280881c403103c0341c001503040081803400c003c031046114130040517021903d50702240d0b040c0c40001c15040407002400110109440580f1144548107000840107441034601e0200d989035419903581549580a10102a1600003420b02680080107a45c00203 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 986342185 1250 986340935 986340961
    0xd0815060903031201180b030703150b060c010f09120201050f040803270109020910030f08030a0b0618041a1807020f030a0c03081509040f0501021c140c070b 69
    0x140020103076460042c1d4802d04c510000820307081003220a902da136003001086480d101c1e2101b141c17000c41c0140b0203d403440d40c031040d103481c43c040f1509156440702d1810a03141c4aa03802d84050100d01c0000b840461103050f68080100b078021400d55040401c8410320b0340590061064500070519400c10300c0c690780d00c58641150950002c1c1a5040003283c405a004000450005101068a0180004c030349842c00340100154000080c180c0c0b400480d6400d02000060b5101001c0c0c40b075a5804851151644e581040100c02042c0c00d034081c5030001000203002503841c080780c00d0440d0204040701e00700704850740d5520015a281c0607039440c60f000b9840061401000324001005640700300144111049411491005070658002e804139070003042124011408140d001401c041d0311407a10102e0180c92101079002410703418002d000a00000c8204907036209110080d0120780e40700d40d00848280005607150755000041c00003000b012a09008940414010354100040f01c00654010b0b1404089417030b07162411043d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 986343435 1250 986342185 986342197
    0x11202012d051308010c020303150619030b090a02161104180c030b070305100b031f2303030306030606210604030e040c020c0a1202060d09060e0d081506 67
    0x52000d442081041440e0855041c410021041d982c2c03980382c079a0440207046094490300310710003e0741401d000f0683c0c0d650020a581e0300041c4464800c40302c10041003c2542d41c411100700808401c00c0758088481a60585c0110390174601c1a03c80146603075951500c28100d0054090b9044403110500707680f800314009250602500c08001c10006002e4410025070b040010b005c0812110041618001c006001c890a01c06520640d54101072240b403401410600a024542c01003040c0b400d00480480d80304108046c40c02c1e04814010f4007a00c47d06c0e158500e006058500400c2102010103241008866060100940c1c1c001c0c10090002c3ca040c1c0c803581c00f00b0072085186100050b00c481d010201d600e5032079080109a02441c02912a04204180c20f0f0030311013907039080c0351a04255801500084069165804440b08890b610300b0f4a644443d0f881c800a540e034840c2a0365928011306050148003444002c0e800403004080580c121889800c840f6029242d0490866050560b0319500e40320300128104900144070f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 986344685 1250 986343435 986343467
    0x606070204110307020f070905040507030b270f280b090a12031a062d040911190c05072c040b0106090f0e0c1303021302030f0f01120201 60
    0xc2c403040700110302141a002180e9542c0141e1050b032001180100a01440e800ba1001c1d61091001d881c20f07072034143d0740c0e281510000b8a080b01040018028201003101040540000c85402045403001c4d020f0950b5100e035a070388001d06000f4403030744100c1ca1700f18440031881030b80003869001d1080c0854860200d090401080d4424a010702c07152031b800109207803451400d80446840000c0c1140440e0105c0200a9400b61020b004942c10060050038841d20b81100100c00b448024551a18944085d41d800900840e40414030b01420201340c1400e02e9400805041094000c1004540041c080308049aa01402400c0648903800080080c44a410420340400c01d40c00f401004007024403417884140d0030300e03008642c00c1e04c0c1c076002c000040c0040b0394001271501c001c0603210100f114035800d184a81080030030103001c140703801400142800c080d005041101c0020342d002000d213444045200c0345180039600c00c0307403021902441079000851041c0521900ca05841f18128801d00c200507a6005640d09040425060 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 986345935 1250 986344685 986344691
    0x1d011d1c030b0a170c09041e03020c120a1401090201140313020d11010210050c04050d11032a0102391002030c12040510080a060305010f02070318050105030606070204 73
    0x1a0300c2d44800320a64010002c00c0f0403080c9003144440c22600b42100030b13103603911446c071550a00001ca482c4d10300317070704040745500c1008014403000d24041c1c2c9005000b00c03400741c0014040c400d811030004082100c0c0e0a880c01005040400380c11225400d0072124202c400074042006100030039880300e800006140d0016081080c00c0c0c4003111500014403aa0000504540e9100b601190824559043c80698a000f143c1423040c082424140d207900c00380d008030300a05010320b6040f1140310911481c250450741c040006003d803a40c2211034110110300d51003480c019a07a81d508107659074040d5100081500039a030206860b121b15035800040041042a60380880c40c0800c03448507001e40030782c0c07001c108200100107074004590700d55212014a081140d401d4450408001c01d000400c0700741c43e907404280b078034013081c5091070090f51034690003c010440c61300050007561a15240d02640015076000b4207805000ea1a0210708240308003140c0d44460990151500256081c40420f13104d0901e003015040440c4010004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 986347185 1250 986345935 986345951
    0x90a0b0934330314011404090803070f0206070509060a03113a06140409210207030c092f0f070605040c1e06140903011d011d1c03 57
    0x20703021800060300d40361200d00c11808001208071444030a400c0c0445050901c60901130309041d400081c03051140440c240c1841c44942200e65440e881080c001354003047c07558880c2031500d001081603003d0200c84025100c1c0348081b44689008500b82c0d01d80c10f0340201214a0409940011809480804900d40304503600303229440c00f504841d00c401c800303c0540d840480c6401000202c20130525a003000000081c4e203012800d101030030000040902c04841514041209080da1401c80185800c0600303511900f100c1e244d1003401c0a90106410007240d01400c5c1d07014942e92941244400c486e18000040441001c00c2c000311281d80d02020204012202c040c551410850149506056503005082c111411a501c1041100708001e00031600058a200d02c04801c000000b1a105071400364030740103a005020301869060040b41c4000e04a5410b00300c05802400342c25203140c002d2012448440c1890099404d0001e081c0000c2604c1c2041c000300d0401d200100060146800b400c1c1d0780e403000c400780400301501ca030342c4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 986348435 1250 986347185 986347199
    0x9030412150e030304320322030b0109050f0a0216170c010c020f06090708032704020703050306010e0306091207170f0414040b130510030b090a0b0934 66
    0x107544100e0281c8007015444c07551104101c680001a884c00d4020880240c0380d0506c00c0c5c000082c3c4066507001c180102c401e0f643c40118a5090080b940000c140240c0f030b400200c0c0214180e080030740a965081082c4055480d82c031058010382c011001d1381d5000303000710300012010401c4404400203411409441d145840017468119081d2160850010056440042c40b890f40d01d078100300c0d240d0b000c03213418090020542400881e0f6224455050300b05000c000e00002c505c6060849104001c10b07200041c02190f440324503180182079608110b8420340170070700b580c0c403444440c01d000c0340c4640700d22001c1020b0b096001c517040040e100380e08009426a0b40c1384540e0b0b080c0050141c05030042401d10310201c02d1940b21482c1410b62440b541608481a008905282d4002440d8a80c0d0f41030b018511681070b0041160746e1001c1500328076000e998005030403100120207000e402000071400d90100c42c080d03900d100e119655a110180e458000d6803c52125202d02c142c00c41000103c0b2048940c258030401c0c10b071b01e0043d03507a05 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 986349685 1250 986348435 986348437
    0x3051006050901050d05070b130801360b01120816030c02090c1809040f0f0803060109091512050304090c12290618040207060209040509030412150e03 66
    0x108011049903940c5041c051031410311051030040000300d40e4090981100d81d82c0c251214100c0c422000034110203c1c0408040c10039841d40400341c900c440013001004091345002030f08809205041443c00d404851000b000310450030010000c0d90404400382c0243d10340100318000100030213054410030b405000802000310544550a146401b9942e0f180449001d40104003603040082c1002c0e004640800c520900400103801c0b0b4940043d085500f01d0040d51075040c906410034800100910080104128004207d1050040c6029240c07e9964610481e1503081d0103040300c02c1d48541100e4040800ca040052082d10b03482684000d21503001c1c0d83c04e05a50310802802c3d18070106441010440614510702c6007461031281c0010225074110442c0c8541c8110380c1c075900d0740803000d50680501070000d119020315003404d1f401a01f42d01d000d08115a500f5060034460300941000350694400d5007040003040d03a021740002a02d0a0ba00c514800d00340700200783d80c800360900d14000c100d0405540b07440c0c009140d0b00080c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 986350935 1250 986349685 986349703
    0x1801200a180b090306060102190b040c0506121f0e011203050f1204060c03020316080606190c0512040806150d0b010305010b130606090b0f1315030e030702010c0f0c0305 74
    0x540342c0030f41d02c04040c01d01c00d00505e0581154019002d100c1140011140c2d8000c05400c43d010300c3c03003500ca500380f800d079506482d00700715000000010782044050011075010b208000d00500031800296100840354086039511441c2000303a8480300500103180c441400140c4184641402c500d0000ca03840000701e9500050014115400d00108000520a49000e18034030000c2900c3c04500e5480c162064001440c00101290204504800014003644502e82101d14002d4140d42203442d50b454940002c11014000070308850b47e0052280351010080244259002e81d610b003406071030745603a51011f0007040d00405491a030700244056619010406412105010354000c2c0d0010610b0300d42c2109001c01d03445080c15080c034451422a00b0480d09030f1104100301507400c000c10b22941c03100440401d5545c0d003e44c0740d62070f02e18028068005600540c01143c2b24850156807800d00181c00c000c2c2d07080343c0b00e005840021740401c0409000000180d050900d103000c0911036098400000e84903122a85451010 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 986352185 1250 986350935 986350949
    0x6030f0902040c0c0308060f060d2d091e0305040e090a0c090b18010608070302070201020703051501050312030c07120215070503150306150405071110051801200a18 72
    0xe02604045c181d0011003241c0c03000e404d80b41005a00c1152000c42d15512a047c170190a49684030b00d05150520300c10340100c88100c203000584200245400a50010a0a00c00494040100c232010316100d080300840380300d000b03070141c41f500d007000d2a10500e0442d900c0d0040c020785030381c011580c4800000d40c18a03154000b82400d0a000180301c1161800c0c810148684104400d0301c01d01040100202d0750700000e8550300051524026031550041c0c0b0042c0c1c608072076908000c1c40d074080c1490030840c0311488030100741282da045080350110501c440301841280310540d0b00459950007003281d0310204001c0c901d8080d0250039031044454800500312803034074454059801c05c0004100006001f000390020080d180b80c464110080c1006e420074081d10220400c500081601403038031100064001c9006050720701c0307280210002e40728000324182c08103000380b500b00e030051b80070000b001807103415010500c1280d80320160380030103841d0101404500042070f000b0151390327070820511660103070540656800500c020004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 986353435 1250 986352185 986352197
    0x307110109061b02010e040e0109060b041103150105031008030c0601060f1803140a0c0e0f130b060103050c040906120203010605150f09030732091006030f0902040c 72
    0x1154000400d001c01d241d000104000600c0d000218003407038007a0300a05035609080201c0d00f00254008100602040c01c031454a41d4138240d480400c0c02415081140c40e0601110108043c070701e40600510a40015100d07840d007091070503071021075540940c0095401840f00104066101c0e540c000c1140395a10801644006811800040015580104070050704c9403003410b1a450161500c1c08642c00c0e4151440050913501004140c000c00c0142031004401113908546103003403041c3c603440c0c4c110002c0b1040d944901c103e08001c0000c0c40040d103a0141d40c00055000071012000c0e26060011000b402c409008415180006c00000030402e02500c9404000c1610314403100340039480e070042608441d45540624091001c00d0003241e03640749880b0031074669484030b40006840304200400b09161000942061400a80304207142c0f82084030780c41e500c8090a071143d10b0031a4025240184416414203407400c4c0001032010000f40059402074201c0d08448103224400240c100c00c0b600020262822400341c1c001080c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 986354685 1250 986353435 986353463
    0x10c12060602031e0c070f1706070f0804020127180b281a0c010e0c031f180605071101110708030720010b03100b0306070806060c0307 59
    0x141220111585001a41040108514001019441c0d11900c050700303030002c180010802e00c402c888015901c0e90310801048809082d121035105030f950031309000d00c810038070294144a031540800549684688030941d079a107805c094006017907642c0180036000324180a40199580da0200c200c0903503203203840d40c5001c203c0b00c05140103000036640d0100307000650f105080c200b60700e115403140200c0003201c18022641041020304454401d184080a42003204039620034200c0d810350910320009400c0d100382050007004003482c10099075503280324024500740c068102481030a4000c150b6030a4480301c1d181c001000c2040146104070f108980318800003120060b0344c43c000d10001e07682c40704a41000c01d000400030800714900e086580c03620b0003400030060605000000141354903120301034484440003422140700b804804030140034043c0011104d201c1c00381c0300304c000310742d034100c424000d00707200c0b00d4007501030041d5445601e011900c110006000c603421400400c2002141c03001000100061802085a159666 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 986355935 1250 986354685 986354687
    0x3011521122a033531021804020303040e0f19020c0d030f110304050f1621140d020708010b06040308040302101b0809040c05190815060d14180307080a050d0e010c 71
    0x4040a00d010000341d407090410b401a1112805031007d81b0102030300b0a03581d580d07807000901c0c5208907004411004500c0d8180300c001d0b881105181c0c000c800c120f40c0b60341180100d141100803401821055407e076442a00c05c104020700944c05100c2c2014140d501140550440c9200c282a1b403007601d01311030726445034001e161102410700c40d8920818040004406c80c914082c43d072603030450442c0300d40044c0306240c0d482a04005030800b99400890110080d10303201c44410001035281c407664403d01c0b0065081c01004946450200c0440742500d900501407800d0174110f80a00c1418410144100c06002c07507240014610f88803008a68501031159220542e070b030103507106000644044080360b42c01c3c450140201e8400c0541081403a000703400034a4140100c0d6102c5411320048408520740c903030020400560310f40c0301c2130a60042406085e82e504103c016488000b1882100707403503148100300d01d8005000e1800000d0a60009008104080c41c001d0b00300503210780c41c1c0d400c035000081008110307959007400c602c0321 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 986357185 1250 986355935 986355991
    0xe090d2d170a18031815170c0c10091a13050706020109030507020103020c150a0e1204060f0c050a0b0a0f0b03011521122a0335 56
    0x842a01d4809103c0b07050041024503011910010007001d000020100c0b445091110b003558005045e510124288004400b001600c02002c090101c401d1101c0b0400003940d00760740004581441700840c004248192004090704000c0000074800c440160340a500400c650841356481400758018000303140b80c42609141c501d01e0040742c2da00c000d0640e4101180c100c040b1f900a020384280325020f0030f0140c1d13100b021011290a200d40c03070110390150b006031742c01c3c04441714442d8040d52210032614111210300e5040380450703035a40500d01c10080000c0c030840030004070f10b101d81a840c0300e151140c1e044415100c416650719034010002ca40f07180b0100d94031841c013401c0c811a8083c1c00c2c052841580204001e80c03c5001504800f6a18050300360455a000c0300840b200d50900c4000c6034240c2c01070318007030341d085501400174048044040c0d444201051115031f855241c00441402d074442d60705445400c0f83e0189450060a49603d81221444000c0e03e140303090490403580f000ca510800810180b00b0018120001410f50 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 986358435 1250 986357185 986357191
    0x30108030c190809061602030105010902090406090905030904020a09080105010b070c060e210f0a0b15060a09030303110c30090913050316030201060602070e090d2d17 73
    0x1581d20b00c02204082408007003195038140e0b0030b0b030303016603038080300007144540d01918000250150b19101c000940f2001d654040d11007040300b150f0501c50242e642e5080000c0e00d2407500302034102d800070080d078281450194001d01d1010090f040490080346c3e182030441c21503509910084e8041c000140d00010000c0a50043d001f41c9401e0800f2003901c2c1e00030001c00d041e00c40c400d000031507500e04408010720114003000303000f21a0420008079021070741c0361b2a044440f00c3c03040d18680e10300d40c0308000c980c0003460f01c9030640c0c18080c1140e1350380b94142d1a545085000d02428001e9012480c02080740f40444d000602407040c546810a0790b0019821603021781628500142210700074182e800d010020740c07943e50350481900406040c40710590040103007441811449625980658940002211400c00d0303011b4101d01c0c1159019020f684030107a455a400c1b000050458884030280c1000154282107801140444805019110350b021203003411203e903c035550119a140700844d65504d280141483c4041900768 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 986359685 1250 986358435 986358463
    0x31d0f0a0803030907171b01021906020d050703050618130b07110c190504020c03040f0806090d0c020907030c020f010501180b04091a040f05070605090103050a1b0509040f02030108030c 81
    0x201b0803030b01d4411501e8401c80300c03120f00c1746030400490014680c402c000801c0c02c55110300d502c00c49604d0a1410301f009510020803178501c0c80c201000542200d001e1b1150a200f840090107100240750039491000c0065001800d404900d001c0032101e00202d4106006e4500c80c0035107480304000601500503180c0b4209a03501201d20800f0601c0e17810b514007010307000303100864100f80ca002d622601251150b40c11402160402d41c04224031f0740780000c10035000035449000e0246242540c411043e080022102d90721a8400070f90401505030110342440e119906c4907a141e0b4151050b160703e0750705410000c0c25180203a10114600045201513695255684a91105800111410450402e1782d0b0344183c90280b011121580790084140000c06010040d44901d07441544a000d40b5440c688030007028001d07400c05590140064a040d0000d069500203202d00d0702d014247d2440d000d81050003140486059221840e0740f034005888003066040655140040c0d0b01802107400078580f02c80c0c400d00c101380703013580102c5101 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 986360935 1250 986359685 986359709
    0x1200303070804030305060d151a03010c0c121b08210a0e070b030906040318210b071805091e15010e030d0e0609150a021b0d031d0f0a0803030907 64
    0x800103689449e44126a800c90710045000000e039001c0d271895100c01000c85c0d8144d420a261503203101d5002882a81d500c0c403035042c154900304094004c4a031208840740807d6101c50f01c000280c04100b4080c068454503040919488142481000080c071050050720410007240c0c84541e00c641002d024842d0f40c0c05000da68018905500e00883c8241da140790161000c0d09124000d03010f054056180900c3c44050301c1c14600042a0202c3d03c100c1701440c181c1c40c4401e0b1450209400440c7c2214841d501d8145046010030307803581c0d070b00d007801c0c200000240c001d0f01c0d1610304c12101c400d5445000b8140c6009114140003100000440140b0b0005000d0510f2001c07810722030f81081e00c0504901c4d80103a0303001c01032401a80c80c03944540034003000c1420400505804400000c000c18441080e503800128a840c008d841d14525494003600c0c8180186821201c1c03005000c500c1407014048038030500810046d405000503c040380e0420001f000c02c040b40e8054112010b039410000411010900c1001220001c01c880d00c40c03c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 986362185 1250 986360935 986360959
    0x6130209010e100e1c061b020322180506120d051603020307210e03010606050f03061813170301050109050f010210020301060906110613020120030307080403030506 72
    0x82040b03504000440c46440c890002041e82032081e040300d1070080c8017502c401d503c2e0030300600900d1040c940b07007801c0340e000742003501d1040e2070600150601c080320401d80055061500c40009500e0743c1d2409402c60401a4590340002216240590038068805084a00003100d00f48001413000406407154541e226501c61014000c40c560f000c0200c5030f81044081c56464400075070301d0200d003148614000a00384a121041c99142e2a1440640c44107000d615119404121142e1f400c1c90309840c0c66120350381c0031680c02e1159880c01d0103440021940a00000c040900041c2d00901c6580c00d8001036031b10b400c00003101b0b0100410400c256007010b00904102d01c1040c1590f14200008001032a0350003814011100440300d100581d00802001c039809061701401e5460b503844560041a029051091030b0018001c0e0301d00c012548804a151f9020311a40b4604074250086a001034540000b94003d1400c4001d60071400e0b0300c4640284051801000b003662252420304240c1001070642c0c0d000351020344144180480 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 986363435 1250 986362185 986362187
    0x32415050a090b01080103020907052719030c1e26190b0601050702061207030b0a050a0e150a09020c0c1e0102100b04021e040306060617040303020d020c0a0b0613020901 74
    0x1445e4110317a81150300f0f64541c0d80e2520125441d0081605074503440080c0c10b01d240100301c0d42d000750001c0306016100952820361031765101d1a40c1c0c08500c0007511841700480e09105803d00482800f00d00d0031600760100c882581e442401070000d488064114016800d030140520700a41030000403086140401c20384000c808944903131a1004000c5d100383e0601c28001226800c5469000588054820603102c4660b81c0c0741602001d40a08405510503115101c400400b03c0e80303242104902c01a80e2000944a829580308440c0082c0c49240a80c12580094401c2e03000907030012a0005000301d00c3c1c0803002e401c400350707244188071450454400f0b042240741c085031b000c02140d83c000307180105003041a45c080740034010f4602240003886550151850108804010000c100f0081e0061085a12910080108a030303a0f00c4220b072251489510000414804e00101d008030f0b11980140a601c3c60014005103462880211589001c042c2d00003100c1e515481000c2250754900305040e4030071070003881c2c1c05628000b18100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 986364685 1250 986363435 986363447
    0xa0e090c0d0c0f020318010917011d0f060609060619020f0106090204060c060c110a1a060303030906040f1514040507050102061605031b12100f050a032415050a090b01 73
    0x82e103125a0740c0b08006d10744a84e8890b0883d08000c1021840840b40700501c039611501034506400540480d410a022070f0301d0702030001561480300201c1c1c0c406008603448420800c045540098105580300c0c00c04d02824950406503c2030304041034180d001420380705c80c2d0a1a090955100754003c1c002d4030f105100400501d81c002403264010381e407280000545410005050340e0301c80303c00c0c3d98001b042c41050f01181c1000744c44295001c1000b0b421000300c4c0c0c1940c030303002055908d2204076a080503681144004c200051072641884454600c1011901d08845904e032600302282d48039018160079070b40120038401880300038024500508000e20107000c692411281c25400b0301c510030842c01c2082800000221084480304000d000c08900038030441e5200d10b02c40c0020040c010170366034640345070b41035180001c403c1520480c6c2d00c1140c0024040d1031150f46180c54400304c020800c0d00d881660f140940f0411080d9009102d07800710100f0f41e84070050401e050800340107200d6443d40200d00001e152102544041ea0015 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 986365935 1250 986364685 986364697
    0x30c01052802090a09241a040e18100c080604060f1e0504180c1203020601050409060f0e031b032d04030803011410030b1003020a0e090c0d0c0f0203 65
    0x81c00540e680c0107040120384808581d41c011100c0d0303031509100c1400402c0600179210340340008000c1c050703041c0d03d42c031b01201d0700d54080c0094070701401d04000410102e00b80705542075200c070082007c0f113150004a40344906007906441000c030310594800204102980105410740c01c40c1c0181d604100c60340c18803c046007c160940100e81a1000340c4880c510a0142081da8102070074001d0710a204402030041c2c0d80c86018075070202210101000200410f0007407865064440468260740106041c3e4603040171701c0000d103424007099503426207481650498100a003e0b40141c8c84847c0c00450b43c1d440b400c442c510b62185054070503509900f0030040040246802c0c130044401301c8548000b100984100c800d0204248900d030310003003100801000000f5410000140607150314000d4400044441c00300d50210111208440700b15400314025103480001c81c82a4050800700003642404011085d9040c0000d000082c12501509001342c00030380c90045126500460381065807508126082600122000c0c3d22400341c5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 986367185 1250 986365935 986366011
    0x20f03041403130504110919050109120b0403051803032106061314031609020304170306013906020c0f0c06030408030a110d090b1627080f030c0105 65
    0x5542e503240d0248100c070440ea51601f00400c100c1c1c50300c03400e00c1d0b410740c0c81200d4881d890210700300c4000003070003480029a404509a00000280c40d170b070388a640550301608008804d42c8480050000340d17221351010030007000a0440c1010a0f0740c0750307140040350541c110b0000d002d01d010b10b0b810b200c0e46035004410300441707003542e5040313401981c040e0311440030bc0d00d860503a0410180c110b0540d072000400c0c01442d4011402a4043c140074001c01c0350318004000c0a21060f030b60765002442040f0a4600e49441c0760b2040e100050042e5240780750f5050749105150210440d01c265022a03001405003a221030030856218000b00e01070145c04a001c88000040560100500150054000000090700d12503642c0c0105a041d0103640310648a05095114800400b844041100d07500310400c04200540c0c82901983c5064119640d0419100110a8124080c0380c2140c01410410b0b1503020201d0020f10910100142059000c02103817502000d41806081d00d5001e444450340c245546044200145000d6880050240da = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 986368435 1250 986367185 986367191
    0x1e11191e1202071a04110103020310050f010c06020a030b090a0b0a0e100e040c080607020609100c14121015050904091103150907061107030b040c09020f03041403130504 74
    0x24660041d0042e11420600802d1a82800161040f0b0101050703814051070003540700340c265225920065080380710a407100340380e80c40820800c00103403804590415180406141c8601c032800320755611410780c1c011100440100b520b610401c50035061486102e54000c1d0340d0300050240031010808a0010101d0380101c0d8041c41c4c030132001801c0300000d03040313407001000101c550100038a018100046418494000c50042d4020f240100c0c000d13510015456004503a4800607101e003800d035200f0300c401401e0a175200011f01108030a42401c3d1010f0001131b1540040780010300109240a200e00c0c1100c3c0c02c55000b88900c00c040d01d1000c1030310f9501405550500030161070025442c00941004403800890f03030b5033103030f25214050545c201801d0111105010f4801042140c1a15807541025105a01d00a10f0039846030b01095003040845ca800300c09503003142c014110065815260303848541a81c4c1b0294006030007020010501080107960383c1041000c0e034500c000707076003004038000840c04101454450343c1e20440d1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 986369685 1250 986368435 986368457
    0xa090c0806040303270b011403010608010f020406180602151803030a0b012606090408040e010305070f0605031509270601050a120201121e11191e 64
    0x820100401800244044600610341407a005025105444443d0f1001c0f03900e44d460003108000c88034105125502240c020b11584c01e202c05410320140c404c82450b450341d282c4000085c0041d080c4220b20b20701e9800f9002503034031418182e000d481d203000c1d1104130041d0f403916402005500e9000c00c4042d000007401c030300010f0684400900034170074140820560a58000001481141d0140c2d5008040381d50007070700d13401c0c0c4a0701050700d9010031401c0105450b189090410014447e46441c60046901510a1400a0030107031103581c03800c0c4098003600119201e41c4244001d00c840200380e2141c1c00208101e11345070303182d0328120742e60f082d0742090701c0c01650103440800e02140500d102050100d00d41c1d00c3c0800460b50000e20301c40b10070344d40c417020303c03c1c07034020114004045013811200c442100c036a038060f1941800340007090a82401080c7ea114100c1ca00026801c15138a2012140100d010340503010300000c0e21105011607642018003041550420720994610440310540e0701d000780e0148500724245104091 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 986370935 1250 986369685 986369693
    0x1e0602120a0216060503060a050f01120b120a0c18021603050c07051003090c08120a0c0c0503160e070c120c0c0513020415020d17090f0708061801140a09 67
    0x10070016405860340314072480880c00c1d42e8000050744c1f191004891a41c1da00703568109200031603000840c4a4001010039001e52203806c201d8000d1141c00c000a807060b60308510020001d030410031820400c44458804050401648296959210051f42c4004046150101d2014a00d5890040b4030b0001c00344000443c0121244005009200c01401d000d0441c4142076503151000700107203e070440441c0c44451075500800c01c0c0c0c00000d4810306400350040300b18545180f80b1030540311402031210880d030340b021902020500361014000310800041e840051010207082c0072160f0740b5a900286540100002009680701040c80051038405600041c00c000b141c1d42040e0170718144856054111542240c1c0c0c100817455001511360040013100c01060b1000c20a0000760b0040703868030341952040740040c450320f645442d451803403891141c02c100703c40101d4a0601c000c020440c04d00080340d0040d2810340043c400c21800942011032140684001030080041c524801c00040346248042c100c800f560f6030310b1414000300 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 986372185 1250 986370935 986370943
    0x105030a020f03010905012d050c0a0e1306080105040c06020c0f150c0303090304050109050102190602090f0405160e01050901091a04080f06010302010207090504022d18011e0602120a02 81
    0xc46d400c40020301245401e65100c2070320741c140d029012040c0c42c20013001d00d0030085c00d115941c061504401014502009020103d41c0c901108000d02d41c403e0b400948102004114070512006110340000410741d8901410101403941280c1d000307400750741041d01d01c00c03910b40c8d4410210211031000c607802a529803840ea99481c29025802e440c0020340320010510541c9a000005042100ca00366a0b182d221601c4000481c0c0340d144c1e091800e649420710034003550000341d098010300758402c0c01510b4854854516800107040e10402e0712140c07084600d012a100c4590790044604c8020790302800c145240c140424002004807800c2d2043c80c80d00d03500ca000c5006804440d8040328005c0a1420841d40c0a120743c00400d42c4500007888201e0241c400c1801c0007d040c01117000740340c07041d6001400260f10303040e44a000c03003c21100701024062400d0b480c003109101d540303079941084126490746060b0990340c1045150b48280c5811041c00d0411194194200400c0b680024003020f82c402c181030268a50180e80420b80c0f038 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 986373435 1250 986372185 986372201
    0x2030619180c0f14061b030909250504080a140c1027230d0b1e151c08040b040308190c0809100513060804021203030105030a020f0301 59
    0x52146900c01e8101401258105030054840c19084043d0740381d99032412410ba9842c0302043c0d60042d1050041d100708002d03000032103151241d0201541d1070306051000280c28000200d80c6544030203040a4807080800d000c0f0707004264900f050130501d10340340c100322520365110b01016008001d540a41080400e06800f03004007400498060210154034280c0070014009552060b003164162170040d0800c10030040c0551b400d0102ca020190224140d4441c2840c521017408116116410100103c0350718000380c035091045100356644010300c1301d02035401c0a00c043d010350181c40c1a1042030214644021592000e00c46950042d1402c03441c078200003145000b81180c0100d80c8005080500481c2c00018020f8600050603c03099010800f403541458140946007110207a0f806000701600307001707880d071504240244031807042040c00e046040150410384c1110211041d000135001030740a1082c0402c6040c1000304014002c440702c003031750940d81014003081d6501c1480d10041d20030b10041d138510585850a40c0300f601 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 986374685 1250 986373435 986373461
    0x702030109060221060112021b1b01030c0e15070f08030405030d11120703020a030902041d010524060306060c1c1103041d060402091e01091202030619 66
    0x841c0004a052040c002d4110402201484075114070b000042c1e044e4031542417080f135050710745040c0c030030107591080000d4001c08540c41c5107180e80c50420306080410810312151080c59002c26400890140004003230780d1030000310406010340f00c3d801d00c400e541e800000c10003d500350580c0644404250a103803a1110366400054035a1000005100a00c180440144005c0d11403217020300210300c2000880d5004d01c00c0824030f0001e01c0d0100042010030740300340c00038119080c1c2c5180c0801c1d6407aa5400080407510310704418070042600c00741549507500d0a00802e071740050305001c02034225500904055411286280141c41a1000130003d001503607501d05659003218050b01321510081404001e40105103990020f801281c40d507502492005000001c64050310580000403034800c00201e86c040c886000580501c2c0e00580902151034951100300004159000c2d041d07440090701c104100140610080b41c003e40c8032290b92104041c0035031400101c803908401c0c00410040302190b044401c400401c3e000c08091 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 986375935 1250 986374685 986374691
    0x108100b010929120a060b0c0a0b0414190c0602060705070303090303061a0d0506040b180603070308070302073219150905030c042a0203130f06030c031509020c0307020301 75
    0x40c130090502c0380c0740708a50000c006c0201941b11009513800340519282c1401d02e0b88131205480c0061007800d4425085071080404030042403040c59010b080240341c0c0d08115201e15101c15a0003405582004a40181030704d001a040900340b13030900900a2142c140080d05040e1030302d850204048c4240d00c580300604400300251061200d05d001e0014641c000c00c0c00720703e05410413003c11b009280c33a1289100c0110001d007040704941030301d5092402003d00410195140c012084d000010440c1c01000b480301e58031039400352400600301103179200354420003800a00703603080003240141c424045c1c035080c00111004580c1190f200100003030a1845c201700707800040303500e407046420020b10b03500851a0410345000310240c1c2d000d840b502e0305210450307003c0c8100030550031301402241c800143c015034021140101c2c1c03042d01d250048501c00c4031056840c5600400c06020106410420140d00d8450307000c0c0721005180c00e0013942c2c00441c2ca02c110060f0780c0100000d803580007644040c00316007002111a0f0baa8040c00034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 986377185 1250 986375935 986375947
    0x11412010306020a0816120c02030403120f170105060d0e103e190c060218100309030f2f010515060309031e1b060108100b010929 57
    0x41d011350092103e2501164009000c0341050000c88282054050155903420520142c5001e840c09804219610301c19400b08000100108403030440556507110a92103825000c808400000d001d2503211b194074040d4a815401881182d0b189000c0307440920b101c81011903030380814540b4a007080d1a00381445012840c190350008110010030550210340b4400541c1952134441c00004038099074001c024800b280010041841d840308008908200710b505494240c1207900341d6601c5508030380c01300300c03000c80440001d611202107150610481c683c0302a0380c50248208a20703998064402c04003180010140f1030301e02d584285120130030000300c4400d00c003a01e18038440801a08943e009000a441408012045d0b20000b0820705240741100c0c040c0c01c8182c000d40c58180d2040001d1150401494641030020003002954180344440e2941303008604500090b20880d450442c100d480d01000d1191008000e0401c011591981e800040460442d194104c502c10612448907101104624003c00400300710400306030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 986378435 1250 986377185 986377193
    0x7080a02071e03170c1305040f0902060d06050301050a020913090203100f0b090106090e221502180418021302070507060804120c0b0a0e0a021c03022a0114120103 71
    0x1440c0c02c64403002c00800441e22005d0342ca11171482080001c60b0042031611040100d030819502c0840c2d11248804002640012540043d01541c8101120300340192038000c1442245820b01c102500b160b1000c00440c40d0100140101c0d0380140c03c1816421069680d101440945d10140002d40e000343e11808204400494101203400400300600344901592002c0004241a40501548000e40c0ca03a206010708035541c001c101800d288482108150350f5500040441c001414080001b84418900001503180c250f200c1d2521001030700c0289140c86581845140204c0c07460180c44000703d16016155003e0000030062040007034460124000c005100300e1400280d00307603028144a000700d11034904422040008601204c18801d184000ba00300184080400d0300320304c40358861142060b441080d83d514100b15000207142180541226504417030030142d4108043e4184040340140e4050180101c51210300c0c1c2c041c1019010302000c0605008440b01281120118241658a00c50740c0c040344e41c044c2c0d038491030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 986379685 1250 986378435 986378447
    0xb060d06090206130329190603060903080402040b1f260108071a040e0c070f02151b070e1803040e1302010305071707180f0906030c0e07080a02071e03 66
    0xc03040e601e055503000c502c0d10905051170704100d401c0e00000100c5584c0c84601140a82014005002c2c00d5280c8daa0030010000e441c600540d96070318020b448401540c5468010310050750044801144a45c440c5088a11402d45058944400300d80703030303e0700054210713203084209480c880410b21040034041c08000026005000121041900d40918036000307110291521042a8011030007450503081040c0002020003a82801034014280145645d07440c5680316004156180d4400c0007452481f80c1c00143c068200001c540518120444400200340c0ca0740b0308024905c0b00c4030042e210103c0c0c0440103002c50301000b400c00555010303014010056400d4140b40c1d1802021070440d0030101d02290a1038009060300780100701c04100c903207104045690301c1c1d071241411a0f80c101c045019075842d4425034004603d110400b070344000a01400c0800003422401c41c24a0714405509510000051001c0801c0201c0c4035805078403150443c25148000d40c407640145820302c01460750801500416889140810926078061 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 986380935 1250 986379685 986379689
    0x3120a05160c0503070f020f091f06110a0209060402040e0106030b0f0a060828020f030a1503081b0a14340e09010612080a020d09030b060d0609020613 66
    0x1241110221007041c0a640c940c244034000f402d00c0d04140700d2280868562425511410320003410160200661800130719500c90a4a044550151944a400004580c491a580907000c14100b20b81a4408004880d9440c0b90b418002030140c0038000210306a611160151000741000d895141899a11032100070010305a495030103114a840c40070f102000e04160010000b1b0f51429920003030242d403a00301070f11070a10b84c0000403100c440c642d208902140c4007803014085203d05d094401c0c2d60303802c0c0320003404103450b03100c0c10b04060842c0f146003c00020307000c40b04030f40c68078000980001c1441925070025090810400c8064007c643c0091031124080021902046000306440c11b28404401402c0c8010750441100c200b21052507141000c0c45281e003110001c990100c2070000220718140c50320b810f040d00c0701c5c0c40070f0b00700e8001d10081043c1c03816540600c02c0d641444260300c0c01c01d07042440e684440415040c0a00f10600a101c00044503040c006c1d01d4001011054000c3e2030541e485035190101c000e40d034294 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 986382185 1250 986380935 986380951
    0x41e030c1d0109021606091121060a111c061a030f0a060302010504092f0705060106080702070501361e1202121c080a0c050313120203120a05 62
    0x3107400864401442d10030b4880c290102c412034010b652255a6510040400b202c050b54400321690351120b00c0d40e18410b44020650308125142401100c0313000140c6800806844000300b00d0600501c08030303440e00c000036038004042419090340d40380c0080d1807100040413542c0001581000500c61510030b44d00035001035000c0c2003082d103281419a14400428110740c42030200a0000e0307002c0008111009041c1c0104c108c000d0000403e0310882c80100e42c1e02c080d4001044891102c41d40031402109110052202a00502460604031000d01d42440020b4449490340a824180b020f485c2140020a00f0200701f10f11121600100f20792048400c503200d03501c60301fa44280c2841c202d2603840390308000464504601120038440594402c00c031982c3c2006a184400e141e540d41ca84112130960182c8280b4410080d40001c0e151031b5101030b41407480707a2030700b40d034202c0e01c515007030080c20010300c0901e10510440c094030b26080710344650101311a0000300c2c110310a001142558410920900002c080d150f4062800b500701 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 986383435 1250 986382185 986382239
    0x60c08101409060f1201021206011b0308010b0706020415111002070f060e120706021c090b07031e0c210c1d1c06050601020d05030c041e030c 62
    0x14076204021001e51a41e9030580000c900350100f407860034821100c121949004141400390f041e0303a8005401c98100c00d100503108038814003840903550300114010039504400202c01051006a10081d200c20010b10458180300030000d484c1051140550507140a010040341210403412182030007042d0b480840900c87c03131400b80c0d0347c140c1c3d000d01e840d108440c440b03503010204800040007a101c2c6030080012240094803805090220401d0003900c100a00e030640c8180401601c810401ca42c00c211440500c800841c6640361038210004140b80d1402e01d640130040e441c001ca40b85004021904042044003408074080d42001c0c42000b44035003018101c9008080b624540c0c02030901d221002c030940300340c1c440030408150419580b00171105a60302c80c1e83c1b120009003503240860341e8030b020003184441c030800c00d59000e40c0d07600c2070080660b4180000076842416291590443c2007140500a145c400c1d4462040f25094101540805e8209840355100030f6411080051046950b201400b4100e000d510701d58402000d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 986384685 1250 986383435 986383439
    0x3050601320f070c270204060c0809030c04110903011b05091005070503070606180501030213020c070806010608040c1a090126091e01110a08060d060c0810 68
    0x504166001e1650950140e52555240962800c5180d50100c0c52803042c00104000083c0402d8071284154000e050310800e401d01012031090300070200001d84c0c40070110f68010402003000c16400340c030511020341c1014246a48003d12400603260000a0904ca03030080e09003c402c620350012100a4032400d0800d80091200c903c0040800050841d0703480d00381c01040042c88506628140012a0480c0c20b140e03003001490310110792074080c61074000344001c0711003d84940d003d00403c5103081074014400c0700c03208180103650440d4001401011406203101c000d503070206003000c000170200081e100524004080c0c03030035035031201d400611004048030280e0f8054101600040c4089161200c5001c0039006030425081041e01c00044400c0c0405441400702504ca84000e41e0100030b51031006409440c4c103000030000c6c0c428864112400c0c02ca108003003009640340a44002061055804907100d02125150000155039000000358544a031584041c144030300d07085500c06030a8010140c0c5c0e01484460142d0411a5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 986385935 1250 986384685 986384717
    0x1b0606030d02072907060e0a1502031e0604020f07052413020d11091006020d0e0d150212090102030601090b07030c03140903030f13050d080301060f0e06040603050601 73
    0x190520803004ca0610707000304a440000400d00440d0480ea03061030041c50140c254440d00195049120125034a401c2080020308100d0041c101009030312048000754294a8419101c00808130300420030700912031901c00042c0ba90f40e9507030450b02140042d00322140c0725400b038203040c0c3e92560240c80b501c03001026541d60403540001c030f12105100308025140310701d0019065081c040c080c2d80c3e40804a0b42e00e46003c500b0140b641c2c4213001c8a11030700000c0c5206540700c0c0340c58002803a001024920506009164134a12403a840b400c002c00c08403500030868041d0301c0d103142c401000078403480005100f8050240248600010103400440c02030509985401009481c2e0f2801d60072482105001000704080d1280b1600082c050b846040040030312004250074980410042400c41e803040e11262102c2800240c0083c0d080e403100c952801404096031250700e1004540d48045503440107014074024080f0316024981c0340da200d11101001c010020304415111a0b446201a016002c151246808102c0c0003902039014 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 986387185 1250 986385935 986385943
    0x301180e0703110a0f0e0a050a020309070302060714010603080403110301020301211b081e071523120402040509010504050304141503010b0316091503050c1b0606030d02 74
    0x8022400c0c0508111861940c4a480c0e0008419505401800c408800524121002240c50040040144031405841d00d960040100c0b900242003903480ca2041c804c1c0062810b00103002c0c0d0507a40e040d03d0039903a0300741c10308046082041c5181c01150944c2040030210400100c900600112845500c0165000540c03000305803c0c4c1c002400f035074a03d00b2001035000340c2000d01d00840066a4020030049801c42504442e81001501d81e40103848241e02c40b400c0004401d084c000c6c4e0503800440740d40641945410600c01c1041740e00c41818460410008900317140d8062042c407049141c80500d5643c0d075a503080d456503000180c800444069102d5460300c4001140301e10103000321031095601c48050742c50f260078551055140c401c07240d4000c0d0040b8403c42d4505101c1d07245001180a441a410741c40c0e1289464410802e281d14080789000420940362010001c02808100b03100d028249800c0104d15540c8843d8842400c3c06003081c1c0c2c918100110251001440010858a004103000e4042e42c00b0040d1203881640d803 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 986388435 1250 986387185 986387201
    0x50706090624120803132301050907093317070501030c020303040309180216061a060705030406050d020c01090c0501091e03061d0a2d030503061003020d060b030118 72
    0x1300c1000c00c0001c000407406900c6010381e521855180480780750b0f2114910f0b03d0760b60304030011103e0b9510000d000046604000f100f000781110306082c05081e45424010000e080001e0000c0078007040c80c039005140000451002002d011034903c010009034049d102955907040c07a224950200b407901141c456850700c04000c4a11541c2c0549696410a00e4016401441031114024460442c1d00b0300000704010045000c0b44000c9004400224500d41c10036030000401c0300c40e0300030910482c4100a5000081c80110a44080360f1a80c10066107510f102043c0c00064451810343d2000c651070320341503101b00320b080051042907c0080e42c030413001c640c407a1039809901d10b001e14600e410701c81803070f020000544070340c000e0f908035450380c0c0800c0854030101c4c208e5072a00505540c101c40d10321801d880c605400802070b04170301440c2c021030071040c050050354401500c2c5100140605020703041511090302002d00035011a000307000d01031820481c1d00c0d80c80b1130110454000380034685190548081c030442c00b82682c05501d103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 986389685 1250 986388435 986388443
    0xa0305150f0d03050d020d200304020904032f1e0105071d0612040f120c0b0f1825090e030a051308010513050d170705070609062412 58
    0x1084144441c10480d07007031034180e412400c003c0c040024280c5c142580c005403060307001c041004541c04040d41900010350441c00b00c02400701c4028000c0001580d10300c008143c0064041c10a403070032103061040710344035a00220070410240c43d0907040c04043c0301c00244600a00000354070b15014018040c1c1c000b0300344d540c240c0d51100026040c030740d012600050404262569800200010314003003200f25208034508040310195244072a142203c8184192151b2051007000246041440c261039070f524075043e2400a441c00b01282c440c0c40003d044480da6010707548009032441c04480c2480070820340101504028140b40c1d00550a5600000303403000c041c015407107414103e0300038508000302c14004881c50381181003401c0b000084184001400102031081d01c0c01400d0200150b40e40c070351203080440c0f5003440382150904020301400c10000b100c90004040e50030569600e03005a6400c0c450a045026001150029141c14030304035010310710003220121901c1d0a00030000241c0b0032079889100300004004d482c03020b4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 986390935 1250 986389685 986389699
    0x1110080601080a0e0c280f0f0e07170412112b120608060105010e010e0f01140c01020c070305060f07020d08070306030f0b010501080603122205150a030515 68
    0x243d4400240d0440e40b2550030a80465101848101c0007901039000d02040d4111000251900c00700d09040c01800d03405440c00301e442120182c50a00313003044448292040600c10703100301e00400d0403140300d543c0c0700c08010910101c5000f41d00f424140803008210381183d00c40401c0c00c24140b035030708280c041501e0145081915541d949000240e4940070030140000d5140f0030420507000050300701c8100c1c4074040c05400710300000c02c400e40c11f00d40058041d0580968590600001443c14542c5540e80104140e02500038038054504100512419525024685e03020485500109240c02400000181001260302440882d0310b02d4881010780e251156043e0303900801600600761240c4642e0040e074820360403072010310300022030995030f031a05100034801c56011940040181d004014070760b444080c0319040b16048025140c2101c2039545075800380702d0590349107034a420b15210030108070214420f800c0103140252845000f202441400c0d21554060b0f83c01201003440c00001c501c550403e1540c400c05424041c20007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 986392185 1250 986390935 986390941
    0x211119150203090c0303030703062306070213061d041101080c03010e040c230f040219180e09030a020118020a0512010905010e0c030f0120130305010603111008060108 73
    0x2800107540000d000c8440c9104203103030000344d524100021807081156580004540f410140c01841c0140703000102c0c600f1803c441000c414a80d1080d044aa00ca981203412401e82d00b0107002801c05031895074002da0312040ca1042c00c0e44014901880e562140f031088000ba80546400c100544070f9500985520380c10000500c014031010745140c0c84140c115001d125080c0c4010f40e20742201a184602402150380c1540000c4030300f40c1400c01010a8406681c11941507090589200c1503200d001c00041c4c00500b00102020004008412142081d0141a0064000f0194030300003802a507258000800180150b1030001c611f983c945400000081065008207071036245458801009100001206454a0365684031444000250240b18010250549a001d0511b00c00140100340c1405504150100385904001c3e00284092406101e0540074851600642e142c3c844402103244c010429000248150310300740011051010050504803000412030b01d550341c0b0203110000305c41101c2e043c0d6003c1e000c02c00c285e001c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 986393435 1250 986392185 986392223
    0x50a1e1a030c07060b10030f0506090708070e01030b0325060905180a180606150908030417030712020610080a021e0d0209011205070f06050412211119 66
    0x2030840e240140e201042100e17007040021158140c02c0c2550011036650a023203010b020417401001c2d401401200d94079042d18144030f014082080c010425404c003d140011802c007a8080c1d4030412040101a080708c9030305068200000144000712145001d180d50341030005080c9104120341002d440002d0045041e00e9418081c040c1030300c0000d0403800d041c548890640c1c04202940003008180c60003454080764513840e140c982c00400d440203800d03008014850313409010100001003101e0031038070501c1c01000242a01c0c10f406045000d0100020000000062401045640010094014800c500880140c03d0781c031200c1d95500c281c08c150007504458005100c007280c88440c449022003032400b400355030b03c1e40c0d0140d00041180f8030907003080384034021460380401880403c2115001030103024049106003410128050101e0090380f0812810954441508080003110030701581c80300d9503100140311054211001a00b04101048051501d05c5a4400850308510740141c800c0c0c1580c1100504045241c1000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 986394685 1250 986393435 986393437
    0x20318120d0207020d0f050601050913021c050c06070c051f170402012f060903030f1501032a032417010b030703030206150907050a0f09050a1e1a030c 66
    0x24181e074407103030f51751450011420354000758041e03d2003880581210b6050404110090344040e0940100d8800800b940e4016150700680c003a11043d103810a540da8500c038a482450300c09100380c1e1540252012030b0250410112398440c0007a2842140c50344141500c09100d6421840c0341709007034000030001114442040c80c40000d1641280c01072502910705003108072a030301421010304c0c2110640313030044414a43c0300d90500ae1140c001c20781c10081d600d18109042c4032a140c24000d0607041014120740f108441581c081d40c800003842c149050ba06042a42c108021100c0c81c882c2c480081c08241014080c0e0003820701d0302010301c400103401d410f49551b00d040c1440580c0303000c817900f0311102665a40340d1001c01c0c1e80d41005010001c2d0701c2a4010038903460903004030000c038021021402d010b44010b0080c0112240c003c02500e00c0b1a0700c2c1c1c03130010503084406000b16900e0000c1c1e40015001010180f0120b00f4642580304080b10003c10010204290f64a8900300c40346e05d04030100342c0d0410400d1000c01c0b4504a128 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 986395935 1250 986394685 986394697
    0xf0806031f020c21071e0b0c030903070213090213051b0705010608100b1f0e010f0c2003010c05090a0302060f390d020a020907020f060109020318120d02 67
    0x1085440b0540186550180c0700201504c031100c07002c022481307404020900c000500c1d4400c0c0c182d885c04040c1c0250b518400412009025111700001c04030020f12090401c00585442e560001d14080c2c5d1005500d451600a000059059000d00044085451b0201b200d004003070042105d000703080070340c04031140454415000707920700b02c4a40d502c503400011902c9c820001003c407545041d00c0003d400b0040001c221850320501046400182d4034884880f8443c0c0052079002d20719400c0c2040401e4140c5103404440d401d0381500001c080849400b1001c00100680d01d10542240040d03008010006855005980f5801078440075030b8848031820061006041640241010408454040d41000200c2d118520345441d0402e0700103451600030000c00900d092030440b4000702907845c028002c6000000c00c001d465540141c0040c1c018210300000c1107907107100700a001d150a60b000140c540c0c2d949c4640106c1c1c003075401516130101603520070803162076407140414211288140444400c0c641286001403a020790004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 986397185 1250 986395935 986395957
    0x90b040b060d050a05100c09060e041d1903031a24040806070c0302070f3602040602031b01060f0611011514040501091e0b060405060a0f0806031f02 65
    0x220b858400016030070041c140001388504d01038441c05100d480d15070300b101c051031000010418050800c0149540008002035142402d44000c100c0580d1440750764407202160147c102f00d4483c0c1560321484100c0007050468451182c0d0f003d0006400c02c070910255409031040f8680d0100450011452411032109488901d481c01e11456081035980d02110381440c5003111141d002c128001030030800c01d5030510400000c0c20182e83e070600c0c4a42481a021701c64515002444c1d80e07a070f100d502035400030440011074407105025450965946407036002c003d41365000f081c880861418105202e0110345418018101910000c140d044070302c61034a04200c501605000c9104165540d40e11261241c0c80a140f11801500c940c40400d0305241300b4200388400c1710416403144061902d401400b8040800203a041d60014280000215004d404072002842c03501c2161301c4554440d40000c0c1c484886500500003280d482800d4451405640e2000300b031546400b0b9203082c2c0c0d0380c004048404010b07001e06a5014200d1a410 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 986398435 1250 986397185 986397199
    0x5010e010b30012307080601020a08030f040303091b050a14010503040803130203010515120c150702030106050406120c0614030406020a0e0a03050304080706020307441309090b040b06 80
    0x2c0800d0758040800d80818401031407811104111741c50f0b8000c80c820b508204280b009001c401c0c0d440c1c48540c0d95000161620805003c5400407509240c4260010810030380c03ca4a0a070071070041842814668001d0b118081c0940c100f100005003d02d5101062030784a407040c0c54480c03940d0303500da03180681e80e4402420b1000c11400d548184026840034811b40d072099001d5444460b0320b504140c10401c60402c803203003004d0198015081c0c0c0741076803a4411103440588410350303c51f4940000d0b100003805841c0d103400898001c3c0c0781030000114001e42c1c064030031a560007080200e503508d403122400c5400e01869a80d52200742030030000305001490f59030060044c034100b0700e840c40b028141d01000594007429039105a0706503001260500070500140500401040a400154a031917125541c41410148944401d256a4452240036181407141000300d0b04466044420110a6881010301201c54000104a64110f050880003056144151041c3d0035000e4200004051903540c2d681c2d400c0b0800030007080390b500b180c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 986399685 1250 986398435 986398451
    0x6110a05070519090c032019302a020c0f0d08031603050a0c0c0803041407150905060406080f04030915050702030c0303070308010b220305010e010b3001 67
    0x107041c170615a8250041d50041017000542c1411860a84524000901c04a04010546101c208415007800c0b08005080007107541007c48442244c605c0c00108071402d103810b01d41500d40510f09079101420746142c2da64a214400a0940c0180d0100c01c00289600036a00070412640d0928200380d0340c10565200030a41c61807040988c1c3d580049800a0b54584410004400c0c42030350f40c1e805000c0c1310b0784030302c4074101000001c5038a20001c25075001c00b04040c1c040360000001c0b50034040c01d10f402134010180401240d580e140c1d11542c0b00e8014403403100000000b0503040b00400c0510301078003200e00300c444039650b003842519101d01020054002420440901060000c0007810801003046407080a1090311481d884002e980181814444d400c805e86119800801c03500c00042d030010f140c05e0540d5000010952101c0b0071148040d0315000c0090411020304d6040340000820505400141144a4140083c072031150800705000c002c58251000c3c21900e545407104a110160442480c40d1020442001150210b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 986400935 1250 986399685 986399699
    0x1090b2a070308070905150d180204060e01060305010f050d110d0210050429070b070212030a0204181b03020c12130503120a05120403020c031606110a05070519 70
    0x1c1d10121044000ca000c200c00c02101e2508032088100a1105a901070b100c40004454540c19205501c00311503d2580c941040d95250128101c0c000c210f940034004001c003a0311503420400c09c00091041000003030406001003101d00d104517080f002c0b140003500c000010a0296651001500c4400409030086040b5403048007603900c0c103080784600e0010391142c80e600c0741024804d0700c00115400040308041241c4510700c41074603020084480c03a907001101d00985450b420000c80c2405540341c55a42111808000d001126105a000f030080b18000c60754a030300305120103141c3c2d042ea10311610106a001d070080d080700010740a0380040c005680340360300395801d0840340f00c124140c60708401c41c003c080000488040c02182410844880c402c1301511100d402d0a0301d45400030040d1187c001000352005e0707244003003010580200074800c13448000505a03000803541c000206138000700c91046c10b00280706031007030604e20a00413446001282d00140a000e00c0e5007004140702d80c075030310907800e0002c1e01140300c0002054 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 986402185 1250 986400935 986400937
    0x90506040b0c1e04150302041a090a03060212070905180601030c1106090a171e07030c060c022a01080411150403050a050105010f0803091003020f2a01090b2a 69
    0xb20503460742503151428034080790704600f4120179020070b140c030400007031061103840400c10400400c222101a80d90307400001241d140e005990009107190300128101c0800d1500300401c038071400042d035811101e60b80d900100104001006407410362003c502d0045106544241c1101c0850b59460502c252201140c481c0c061034078104a400c1c0350b0940006e80700a04029281d02d0030b40c1034540c007c4281c5e080c13140c0c0909004064103c901c01c4025410f0008902080500a401c1000300c00e410550402c01051613840203506c4080c1d510056511540d4a640342584107503a0f000d205410304182d45001c2c00e5a20356071852a000448030782c0c542e06c218150b868802095560008101561140c4050031b184103032880c1040c2541e006030401300d1135100b1400c090000400000a81364050803ca0b5424100310421009a000303101c0c0e01c140c0649048000703480f05008003008404804102c01402d5181c0e01c0060314404c500300c80c001040100341004082c0421300c10700c05244005903800504051803240c1c038800c12241c0203 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 986403435 1250 986402185 986402227
    0x70c0f11102d0206151507030e0a080d050708181906020d081302130f021602030c0603070c1b05031e010f110915090d05010203041401090506040b0c 65
    0x400c403a00c01a2001002140400204800d04442d030250110030406500c803080213110301d1807950300351810511a0303201551010315800800c0c255075034400034200208a042c1c440120303405503c090303000282a050014a901a001b0310b940c406d820030900e40d643d450154003140000d0042c020311003902415135180401c140a11a810303110f02c240030314104000c0e00303088504500c401403014900411004070301003028105e049504613440030004804988010003440d01704614034070303648040366038800c01502c009076465150084080b52001404038040009d13a100440307a04c000a103080c0070020000700c00c101340c4c05240c2e8412010520090726203022a02d031992000c107a40340200685642d5425140c01c0c4180d040c0300d030740070398140700ba01135042a0328181e100d04c103a10390050441c1328800214800e50410f0700c403166002003614102d0704150400c607004c2e4000b95010703107510080004a9001290510456071042d6100c00038010700d030780b40d0f15400000140148441c005010411601d0030f4a001c01002a40e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 986404685 1250 986403435 986403437
    0x70b1b010e0c011b0b0705030a1d0d031503080f09010203041a0405042a2001060806040b0c0340030201050906060d0c0b0d2004050f0405070c0f1110 65
    0x496420b2072000109490641c0d0b020800c00c80d140c42e5050041030030305141c03a51141071828069a03944070b000c0035000400050941c501080200c1e2a802001c0030041480041001302c0d9805200030b1100130944608015203200c02051007030104038a1180c08940c4014054800f0140143c81c1002c0d5142d601201403003000100000b00580010b0a00891900d4850200c004201c00410b44101034240e00c2c0134004609201c40741e0a00085e10a91810014809100f840c2080040d0007481459a103200d065a62030003502c088420b201150006900c110080081d82e1103402076038040f01002c80e03500c1e03a001e02d070400f959000c940c20308080420740b421141c40c01c503a659075100e40c0c0001240c0c50803101c03117801c0182c00307005244039450401c840390120b48232402c01c500361031801144035907030000d8450600041c10314801c0803c91600b2207860341c0d103400441c8040d01c200d403c00da400c0800301410f1000c000c1102c004031a030401280c04880340780042101c10100f050007500c03c0462500f84c03960703a00015001c0e14205c010300 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 986405935 1250 986404685 986404693
    0x609050d050903060a0b040618050f0601020307030c060507170103081c0e0d0809070512100506040209090115030f0509031b0c030a03050a03090c0902030601030b010e03070b1b010e 79
    0x1001420003200d2241012071420740e00309034184001980b540000380c00c42692603120007032540c06640d01c2d48000700070011050072090b103a8050101001601040b50014007610040c40018070a500110443d1440d070b501d640c403009078074200d030303284001070802528000030010014810900b509a14100c28061170251000d151070b56402c8203c01d00140f151046680c040d4205205a4000c210009000c49000300c68182070405a40d240e410900c0c000c0203501259003c102c64080e5030107940c01007aa13140788180c4080a00c0213540310400d200591080d03451050f00320f45032400400507072030311480b00d02c811125840c2c00b054240f510060202a601c003601c130110a5080050b4030404501d1403060307889452920009004100d4440d00000c0d02d8400e003080c06020310070b0000d107510074184258010181c040d40000c00508054844010030000d400031111a130100f86032905040300303036004020450701210020000d10401d814508a1440c503001200301e05d69107401d8080083d013074402801074001d0315003240014 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 986407185 1250 986405935 986405951
    0x2607030908010e1f0e0f160f060806010206041401090204091101030b15070f031103030103060b01110307110111010b040204092007030504050103020304141b090108070f1205030403050a06 82
    0x49400c640100e01c00c211951301c8103420018801c1d4100201d825480c0d0ba0400090664010920300e0811035044021072490082030800845005c090350048150b80007540e40000440d2204411390348010190380c0a0b0250780080009400205203903007410b170503415080081100c0c002c59000c10151908507030125101c1c480b0022110341541d051090201014007114500b5809001c4000c03030140d4030032030340c010f40001c0ae0308460a0030b2601802d5091903101c1c88404480e56503a49041860082c152403d0701c0b40000d40e0480e0b40310458100000303071180790707400004c000700c6003807040015100000c0d03140d40007495540350301c0c448145e50382d98400382c0010111200085040d03002d1812082c0c0b064045080c3c454290401d01252001c03a6101054409aa600b0300700184c0d80d0710b487c245841e2484c82d2100b034118500c1071028021494000c002d0f01d2208500643d1014004d980316211252220400d0180c40c030f0360001440204135510340b6403981d00e94140034005480c07a04d034503900c8407403c000d20407200380c428507112842 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 986408435 1250 986407185 986407199
    0x51903090f1505070207030807021003061707030213050702030a0819020a1d06040b030c16080403081b0613020105220b1801030b0a05010c11040e0c1e0a0326070309 72
    0xf41e10340c099003a202030442c1c00d00b55514404a4001d0007000380c010b440c01080c00c1039a80c066802640900618044c440700d500034080810382d1182d041c00201d002da41034144202c0e00c16494003c140c000c83c160340195041841c0500115184040140703801c40c402c4411150403801e000910003000306100b15600c15000705100e030f1440c076020260b289250701030181000100040b40c0700e80d059079089190040c0c25036541d4130010071164940d1140310040d124040000e000420004c080f0000c4c800443c80391480300035020745122007034440c4011142040036822a49c0c80d40300644c030500c0100400b0349540244115940f074000c40c8001d00e41c00740c10102c6507400000340c01084903114000802661400d20b41800b100d0040707008a5030110703c43c8190381c1480340f1700036008104091503803074484244000c2d20401060700e0201106541710440a651401011200025501d41d84502c000382082c0e00e0140400610b546156102c0c03c1c1c0b583c034544c0441603480d250342070755480310704840203011042c00f035034a409146080c0300ca = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 986409685 1250 986408435 986408441
    0x20106080303100e090c10110610050f040f1d010c0801080106230d05011a0109050f0906101e050d0c050c100b0612191b051903090f15 59
    0x8401554014401c005840d4071083c24002962000b10500b0710035210703642c002c0c1c81d10a12a40569000c815900034880c0654060207562078410324104880b40d5489000d48100048a01d00030903800a4000c807000000e42490b40040f01c004090b0440096101203040c0c00b101440382036480b001ea01e9450341c00040b441c81d84030705031502505510008000b90b0b80351501200f00c24030f00c0d9000c0e00060210903401c0a080c1d4582103017904144d00070380240b080b0703a4160410040000c00703116150104940d2880031405050000b02d6229010010300002c502e07840d42c00401c200c0f05242c0200c0400c0240ea05044d0091046d0400d441c40390041e2a00d901c1d84414582031454147c550400e02c0170100002440781c00300d480c030005901d4030500b2a9140008202078140d010404a00c9148000301462010405201802068481c400003007000340c08208100d810300100440b00c4246001d800300001c900740580b02c03a110811b81d400c490142d50b410001009981a507a102c6003010b02c010955500381c01e400400100306d07140c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 986410935 1250 986409685 986409689
    0x3060f0108090d0e0f06031602100c080a0207080c160602060f040f03211e0b04090302070306050a1e0c1826100603120212090906060d2a020106 63
    0x10810385102e10742040034a94650b151070140040208118000e0302603200c0b040f0311700c2e07141e002811007139480c50304a0316003178003100c4a40f54a00500c20340003428151012445400915556651407003103580700c3d481910040e40144000b0360782c4450402c44100c101c482008901c1070f08600000c80c1c0065031a281019041c41030050401d4414101c40341084001198200014000b65160401034400e000700c1202c1c000320302c54000658011890102c1c070400200e83d20415540e290402003051202054900074401558590b01c5d0050248c0c3c001a802d00014030302e0b13040036610800814000450141044040c40000b80b84191100f22a9032880054500c1d54403071941d07141d8950584801a07100d250901d000d002600440710041004480e039406043e0360018420400030300304451041c08007070380360f040050002c031000194401512664114941411080c03050311803030f603002049004907580c1c0384140409507001c0300900303032025034802c0d92900c02411840982c1240720900e03107036031403040055006402c46141e030b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 986412185 1250 986410935 986410937
    0x506010810090c0611010b060406020a0510020705031c0b0303040b0403060e0607120c020c04050405060117011a01111f150f081e0f0d0203180d110f06040314010203060f01 75
    0x603144802140402070583c00302c074032a02d40f016160502c0700d0003a00624041ba40160301c4100041c001540c40d074009070600205002e2410381c3ca00d03103c150f01c60000c0b032041c21001401a00148a810a04104202500c0e90102c0074030300442d1140f143d01c002415948603411000f410784003c1401d0051018a01c141071001c0e50b4800189064107002001900b2555410700640390b0b030f9212001b10701c0e014030034400c82c0e00694000d40140001e00b081d00e005c070344031403090080300b8498010564074542001c3c14083d00343e140340500589030300f00c140c403070044500c041c545100044510402c07412000c00f10307442c00414507030708a10000213008008020544540111680992080070710b20304140001000440c0008203000c01120911618003101c05036803c1c0b05000c00c1010040c050001110300d5950003200038a040c501149406861000100402401c0c805405c8060719060120411500b2424109101b180d158030003400941816641d0741e80c04280c200b007100f0800565008814800c05050401101e07c4202c42 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 986413435 1250 986412185 986412191
    0x20d1706150f041d150a09050c0f04150807020d0834030902120a02030c0402070501110a0503040506070c0803040b1f08010209180609240d0501021315021f02090a030506010810 77
    0x180d440018400b4802d40207030717020548d0701c00200d11040b1000c0201c480444245190075122543c6e4030101c80c00f452003c00c442c01083c103050001c0c0f4118030205240e41c0002c1703e9210480d2a440b02c40c200c0400800303035021401b19020441401904001000074a40071050981e400300340300001d071061100f51011803c041040d030344405d8110b401030f0f501150300040e540b03003540c0050702c41205050190142202400f00c034400207002500d00c00443d0f1000c021481a070140d01115181c1d01c802034200c4104803d4400a42100c00a10104d0300107802a08150f400c0b6045030804000b505004548000c44c1c80194880c9500369400a160b10301410300d00d04000303c14030005003044c62840c0603000b0070100300c00100846e000b50503003003000d90307461400491059280b0b400341a00b6030010306031400e24000c0d480800650701c06a420100002d40140068000c90319600603400340006800182c5844802039802c4091404150288100b00390703030311840c1141e00203500034001400954905032084d400e01410480c40008281 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 986414685 1250 986413435 986413471
    0x8120a09050c061c1812050307091212032408100609021e16050303041103060f090d030f18060914030705120a12060312020d1706150f041d 61
    0x81c80d130301d840307441d40da190000c2800c0900c111854213404146800070221003c00d6038004060f40e000e0040c62150030b440d00d869402e6a11906020340100300c2c1d0710000c110030301000c0040700080c4642c20809449441c02021410420481c40e00d01c1c5115841c4c10500041d440341c0c1d0030540b0041c01d80100300050082c072904510300000207141480c1c1552a41010030148000101d4011844040311440c200d1074106c01a03d84904140c50044850f005403007d00388684075100c045070000c94141c040303502030508200200b141c4603040000360041c00314000340c14082aa0303445008013039880c4600001000713101d04d40000c0c500c445403130b0028104401c4420040d4607401800790750b0028a00003100702a0300341410016441c1c11034010204c0f804050760203c070b4509424031000204000300d00c5c6c2c18510303030100b80d000c0c4c2d011025952021aa4000c1d155501d124400d0644042101814104c0041300b410701e101e00c00310b10b85014800c1d4006150301690016a180301c0d10074120545044040416421140404c1c40c01c00d006 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 986415935 1250 986414685 986414707
    0x180806090c0f0a05010f1e020d0906080610110708010911190b040504022b0c03110a0e0405040f0816050d0507020303120c0c0a08031005190303030908120a09050c06 72
    0x5945000e04c60510200110580490340a001819a443c00588482c001144940c0009483c1c1c40c0540800c0045410402c0219802d40218181445404003410101d00186000701c11249020701341080c400d180103050b00494410800e000e04a1054001c00009214a209406025030150204030b500030092030a070b802d0101174083d40484044500403540946c4541d0f619080c0f144d41421014600300324500510f011400c58060b4000340b038455010f880402050b0010500c9112034130500c400900094070b074150910403441c040e0701507908140190030381c44000304107507540701d07469101700315821841c2c1820081b0781c100401001060120842840c1260034040c880c5c1c040303a60380c00b40201c0b4400190b41d00d00002d141c0110030042c3c4442c400d4800c1243d8800300c160a002210343d009440c1e0305400440c1e000f004c2006d05209400c03141c1c0f14102e03a90100c0e960b02d5078030308400070140000102c2d9640030802010409298259200340500d0707002030001000341d00740ca092490b0a404209085c0034010601000c50301c1c0c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 986417185 1250 986415935 986415949
    0xc07020307030b06062b0510060e04092a030606050a211a0c0414090603150901180c2c1b04030803090148180806090c0f 53
    0x4a6104500c44902d440d01300c0000c0c40c80c000c1c4220340141801054407003445c40d507100e420075031800c0f40c042c3c00c003c00c0d05ea600400a02c0080ba019070008a07424103050145c5091551007849018014500e21001408080c4400c1c60031307000b4001264260315615090041c806a8441e5800801c0102c0381c03002c40030300d0102494030343d520000241c0c0b02032a03c100b852050004070540d60440540180c404e600324500500c40401c40d401c580120307901c0220061200d015400c0c42c1c0d103a0741c09010014018039401c00744004041e01c140000f0b064034459500c0b500002e61031140c0d0100d2261561084105100c02814207681c00c40c1d650802c80380050003d80380004418a07034003000143c1d0458400050b21801403034101d4000c6440c0b09681c001040f9550010801c41800010b510070a00a000084081d0055115541c050400d4001c422501c00c0c0721020044581c0d4611040b0450402c200031b42880c0d10701a40c28922000070b50b043d80e0201260381c008e4010042000428070601600c62400c030340c0c20b4102101200802c0c68 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 986418435 1250 986417185 986417189
    0x1202070f02120c040507110106050d0b280905010f0e01150306050601021f06030b01080d090e0a09020d110f0418020607020f03100c02100203041e15020f070b0c07020307 74
    0x110074003240d2031800c4030144484100c0f008043e0040c401800c02c40b0008103501c101d400c08519070351a0000210300f92401101050318030790041884140350721841e50303801e1004010b184180c0c0c41059030780f05c0ca403190f40902601c07254a000c0c20000810703011919600e070980b0354007080891183d140010200c06850701803610415281c00010024182c0c0da4100141c0c504410890210402c0340584064131042c0d609030010300541b4814540003540ba6038070202a42c1e05da1007008040c010454059003030120b411903108103a0301002c1c0f04e50215804c2416000b0898a5407282ea0907140d1070140340c0b06d081b842c208400c0f2449000e10a4500300001e0807203440f0f058552200d80002841a00001411015540d589800c0040160020113540c40750014030381c032100400c41100340c80054000c40b000030f8a0300c60035100352032049030412042d40c0690030039609025000000e480407a048442d00e801501140c08500c0508a240c01001c0030300d50307550542c144200404030080521090300340c100908401a1004a01101 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 986419685 1250 986418435 986418439
    0x30c06090e043c121e0e1c0308160816080603072408010e060603040b07090f08010e0708030a1e030e160e13030f0e031509010504031202070f02 63
    0x49000300700710300c680c500c2002c1845101000b10401140498400800c04580a10500880303000d071106013000e4a2900c0341c140c0b4981c2c04501c031602e5010403030280604d5a46014010000a80090031020303506c6403159403102540000d01070800c101000b015200c1400d8440c030581403440d118a018112103002c110701d0001d41e010001e003c2e0205030170351003c110040207400c80041540e5017556002814100c810654000300000f005031000045096099581600507100a8070992444d5155103400c043c40700c1c0070b0600c0c410080356141c0001c0c0e00421611400161003840000300e030441200d41d80901d8403182e03400c501810341041042618042d040b40c0c04401c02c441107400b814030325030001c03026001481500d00b88603450182202070302101035403101000c1503030542691801d2a850f4440c10f26104944000014082242c40305100903490046003d4001e20074001d044600400a24440101d24001a110012035079100c0050008050700041103050b80c81040c00c0c118241045903c60006000c801403000e8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 986420935 1250 986419685 986419703
    0x7030e0705042403210503040f0f02060702090726190e0a080414090109020315010509030a1a04121e0e060919051e03060105150c0703030801030c06090e04 68
    0x24a062100c003e2080000070030400b5040e00981e20b00b80b44008007a008100c41850b500a100b02130007601813015640141d070041e101c20429400d83d940d556420107060030580c0d110400b406140016500e1070001c030710884442c1d4909103e1400e02d00ca07044c0040c5a20041300050314064100301c03000304a40860040c0071000302002c81c01200e6111054189a69074001400d0741c0d60014021401240c4001221450300c42528042c0701030f130341c0d06035680c228042a50480902e20701582e10141ca984540701400d13902100030107540501e0120f503600d03540d00480080807048004c5000401091100700291700030701010303030f040000300784102c00d82c00542420003082c1c0c842400a5480c0c509000d80703d4406403685240c01811810b11000c409007603041d203034450b103d001d00c6403000c00c80c820b600e8a1801421000d5100c0500280b03002d07401d100c1001103043c00c60440c6041c20000744100640036104110050081d8000d0300d41c40d00300e5055040255250b11140c015106102032440100860040d40c000c2582c0310360004c9001d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 986422185 1250 986420935 986420951
    0x20604110406051810270e0304050402160b060117070305041e08130f050a050d080d1107030f03020a0f05030628050109050f03061803130b0306010807030e070504 71
    0x20002c140c503400c2a0380046459440788001802c0b0b1040074050301c1e034403c480b82566079a084901c44000d4190400915100b41411041002e42c80d4000b800504420000d4030705098942001c1012a00034030110421074507940030003c00d1000c0080d0040d0070540c00e07c0c01d04100c500211680010301405003201081598030000142440000d120300720213030150110b0640310120b582002000ea400040b20280000c0f2200720024440d02c0c060300000850301d02420544e01b040c900b8082019146a0100550b040b100800941d500c1008911504081e04024490191502107600b0000c100b1109140a4800d26104104910b110350b0000c5816150701d086141880e501d554150214020003284401c6041015805211061900b01c0c031000d4020b68030f003a80d4080c1c0340b036542c50402140502904640341c041d0030020205104200203489000c0120b09503080301d2030300c2c204489070651192942e10440460f031002c414480190b911500c0c0c01d0304400c462a090101080c29500c0c207480d40355030320a00e441650340ba001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 986423435 1250 986422185 986422189
    0x2070309050415051011011d0d0f080a0209010c0c06081b0c10020702191712030f0f04140601060f12021215010e091305070b0307050405100e030607110105150102060411 74
    0xe9a00308800c06d400030702980c440d40c0c8004500c0d1340084803858441c028500040040c6201d0004800ca181d0641e90f05031880e150304104030002e42c000c419590400c0304000314000442e00c0c0410010052109039500381e164600500c512402c1011400c8038039442d08100401e003000d0800042100c00c02d5450704005a840c0c1140c400030b5100d180001d41411441840c8070006151000300b580780001072010020b6460130070851100e003000c2e01c07045510310940842030020030752103507a036408276901603c624200c0950031030341e9205619101d401d80c014800114001281012242c1c81607034003074620304514096080640160494510410042ca050311451420300c000140340e204501921741d081016045e0821400e108800700b943e240241c00a0721a80b00344900011600354100442c0d00c501c0345662414100307410102004003807403040001c0c2c410081218810041a5018440b841c0103070344030b840e04591086501c40081c02d54030010700711201201c608404416598021034181e0f07215500101c09a103003011840 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 986424685 1250 986423435 986423447
    0x5072d112e064e060c14040e0709050a1202220608100b09040218060307031220030a0203070201050318060f0a05100303050d0e15070201020703090504150510 69
    0x310241d121822150b524020043c981100c0c441c038070041081003d54040f000d03900c0e40303c0300a03040b805208440a403454020541942c007003a26a0b407a0301d400443c0d89040078040c00c1c3d07904550002122450306009106545800242c020000d000030359002910900d44a0640342c1662900c0b4081c1c09280d915444104a0040d80a0b144d10402c24120402c0f680341c4501d400c42d915990203200503000c914019000119140c0544150701c21360340103201e144404144442e83c10311440250440d41c25104004010000482020010480341a00d80da50624031501440415589520040c03ea003680c00400c4030348040795012003140c49071602801e11965a0300c650303a2880019444420101c00360041005010f0700c42c0030054850f02a80c1b000009101a85070700001e48500c80c103034030004000c11420044440d0744a61a0840202c034070070f81c002e5980c10500040400c5a1050803200200140d40c0001c0b004101031300725280c03501404058608220b09050a01079038286c030800c1c02228460307160700804080983c4076213 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 986425935 1250 986424685 986424689
    0xe0a03020d0f0e01050f36030c0a03110d060e060f06090a050708070c0c09060e071106060307030b2e05010908030c0607031d010207061401090b1305072d112e06 70
    0x2001050f00647e0000c468411642012051081c0180d0400c0500d0b454007072410800e580e08002ca9010303004280b410032914180124081300c0f104e40359071040008007010722040e4071945441410302c40710700c0c0030b0b002c1103103142c0010240e1000500c0c00045c0300e00c080e44a4109617008115003421140441c107418003031044181603005040d043d0030440040703840b850004155010b50401c1e00d40498140d644600d003a00c07188215005900740d4070030303481040461144004582c0180310548044049501a01203c60201607111140100151060208019603019100344010044480698200114140560f45941018114404254540c6503111009101108001c1d06201e17802c000c41da17403030507441e211000d05040c203070134192045000000a0480c9042c010300b140d0f420700901220081c0d24081400006020142c0200e00b0031170110000204103001030041d40d10403080170403100800c1141080140310030400c0345892000c1e008428052008a10020400314082d1101c1030b4000000c12400d0341001802d50f5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 986427185 1250 986425935 986425987
    0x1503060204150806010203040e0a050604020d0c02011d010902010c0809040e070621090b0a1a0607030206101a0724050c190212090607060e0a03020d0f0e01050f 70
    0x10001841103501c00c00b0300e402e411035100c1514503982c0d08016a1240201c0c4078912006a590b000207920b1501c9502c500d81c00500200010f0414440340e0040c03040301c80c070419540260b07646040c8010346450006484501c0241d50340284965141980002c00c10201c0d8070004005080124240550359141d800410058250b031040350300c400e584240c01003d107015107881e41400201d900d08a900700303c981c01074540b255000b49403002d035500d0321000c05000340200c100410705d600c2e01042c106d8980e9143c00003003c2e9907010381c2c000d010b10b040240c000741d0a01d1065100e50340451000c3c0149421368221401c5e0381185410001e0030b44100840c2540b04400100308800382100341c544400c003d00e5905010251a101c4e0308003985403128400e69000303994502c0030200414280c0010b115030f41c50f0b4940700c00106071240c0f2030034010a2015014402074130305201058201c0240c0c1000c007035111030560082d070030780c2072030785901d804060b059080c40007904074441d54071700c1c030303048440011024000711212421044000340 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 986428435 1250 986427185 986427187
    0x309010b120a0c080109081204021f2f0706051804060608090607020d080115020316062009010c230709020c0c06130b130320040f0c08010915030602 65
    0xc1900080c1c0c4400202c1021240c0314809840425991414803178031007a15809040c0700e2420300c0d84560b444044100030030403a40a80c2d85408107610388100c3c0420400c1110329201c11f00d488410720508100c2802c0030420301c0d010504400c58034641c52000800404680c00743c201669501402020800382540b1031000e0f94100d0704104000a0b02940480c045214442e5002075030016107500c1422a2180320000c0117038002100c06005010b80c9008403820307061144030f40102c07440d00000d0740402c400401c10ad80161407407941d030080380c0484110000300d0210305400c040520300d0100d00000107001900b031904003034109505002510010f0447d00c070399480030102c440c01c450392642e031f0360043d4001e58013460203000d07039010341a0071207550305081003510003e02d0034503400305a040c00e0070701c07000f4076400c0104404000c60f8502c0d40003012072800b1a101100d0b200b0443d4080c10110324106100507518291041182145000c90b03900802d503100c0001c80c195400030601049850b042e00c50443c15801c250406171075184 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 986429685 1250 986428435 986428459
    0x10906331526160309020907050d0f1d0c060307020d03020706020403020306090a02011803050303061e060c011a22320a05060108061e0402270a050f13020309010b 71
    0x501c0912075110f904804100d0808403071400d01141075a0400f00002d401c0203d800205103024020809031852000c84000090101b82074071900060300e03580f403c0000d01010402407248103150034010340c2140007042c0c030303030700c1c914140204000d541d81c07220a146010103030b01060b03038810410345404a60080d6002001c961a03810b212f03900d9501c40e022890100d0100780d00000c0751b0130032050f03d0032480840c0d8111010b5811a40ca41c024000c6001380c4c2460700b140c10050610703041099960402030002080b10000008400c19103518181031092500e8080388501c00e09003440341d0080c1c42e42c0031428861042c24000c40e4080800444a02d4804001401101c090900e83d082e1034000c00e615032184942c0c101c000c24802511001e0040d40c407100c0a6464a4100c14261003541d00700c41000e01d209050310000e000140760441c2045403451044c5e607203103228500443c4564540781d5182941b020005098111545240724407010300041804051411520741d2a80100c001140d801d42984072007041d48010300b020215407 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 986430935 1250 986429685 986429747
    0xc090e0a0f06020918010f03030e0621010314070e01031103070b1611040c0e1009151d090705160c0b03010308030f0702030f1215030109063315 63
    0x500005003445c0a440b10350308807000e04c0c61031443e50f41254032001d95040c0050441e103048980c0301003200c0c0e0f183c00640c20403002005101c0e04801102911081c4030342d900c1941140f6103041d181d246460301321199805101e00788007c00180c044941100ea001d00032429600c6e5940200e800c0200c130398480c844403030004c01c0103200210740c0640d61221314032071107005400864013402c1200701c82e506e404c46000995000200440d608000b18200c0302101e19081040382d203941c1d2544200985980300c041c000240800400d509248040340754808080e4003102c48c1003c51a110744014801d004003481c01407036001411822060120b0003412030040d22040351440d940e581c4a0905110030340c8103680501503200640c00140e541c40c40881602c18102101750102c1ca0540303c040d90403545000500458120859956550f1480e94248a103000e061311940002c82d080d48450b503100d0040c42c00b15804545901c2c542d5022181e42e106031125425104d035503080ca203196082c0c040c11540c1050000d0b14074050708465090031621 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 986432185 1250 986430935 986430937
    0x114011518090204092f0f0c0613020f03010c080406051b040b1e27010504080d110c0a0503120d0e031b160b0a0e03240103120c0c090e0a0f0602 63
    0x24654442d4140100601c2d11080c0c080034204903204d25004981c00c105071034064502c4010502c1c6400c0111490402c0c45808d9001c0c10441c0c142e80e0b151440650506080031404c01103603004c40c0708811402000030010500300a84201001000100940da840e1b0004440300180203103440400c2c40c03003d00da42c860b030321114504980c2d48004e11000c1044554080b80300300d0311850003260341e1042589102400d10400360100c0100411100c00541844018400400d0b0707030008008200c4004056650a4600f407203816989080540101c0c0da04e029460326141405161000203010b0342800c41c0905003542d54211864103001402c801c03451035824000054a141410b070f02d20180e41c401d04003001901c09100203c00e02c140085c440e4400c1d0344071220b060090490301e074002c44210350590750182c21313540c4044407030f00458410301030655800469581003006200707000e12000c5400800c030080c2800c03403407018582c0b2a81040c2d1114464400c11946840c240503034a1000d125035420f0310350248800410310190303d403041c0a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 986433435 1250 986432185 986432189
    0x60b03070f021606111204180b060d02030c071101050405060a081302030a0b04060509061302040203070e0a08030d05091204032009010e0f07212706050103140114011518090204 77
    0x4074406c120070040b0f41d86040080341c0403503200c0e0341300c00200303071111821a024088084869501c05d205000380702c1c03968607a00056104d9000005400e0382c4404501d0411a10b40c841900141009008d1001340b0240c0c81d8402160740c50101d80c1031551450f07031480008d6a4202c0c1c0e2071002501409020103030420030100070b05040c0aa4402c0390f00307000d05d41d0f9802c0440d07076407901180d2244607450035860083c05814540e0045810007680d00c3c12040300c443d030201159000000340d1007030203d0743c0005158144c4898034403401d0341000c0c00f04003405207501040c0780205030740035600000d131852141c0805c0511040d40300c6140b05c021403001e00240728940c0d41da82c03451180303001210304812000102001404591140b1f0011070f03a1120802802054a030744109080107104144028804143c52041c040e4204644800341b1030030361103102c01040301c0d8158030300600001d840c45022a240d038188201280c1c8003a11400c014150752040303200e03502d5810012002c80d2176a500c400b20001400341407102060441880d001001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 986434685 1250 986433435 986433467
    0x3230c03120901020d0804050d0c050c091612060e041b120606050f01020c0a210503072d081c0908030f04050c1e040203060409050601061809060b03070f021606 70
    0x1610b580707000780580f01038601302c4004182744c1005441b80401c5001d841d01c50560303802102101e401c085c81c0f20105604081c00c0d100d11241510700070b81860901e41c451491a0300c000c00c0c10043c0000ca00d012031003064040054401401d0304460180e0654140915000a0040900c6001602f0036090360521500030031450062a004025542c0d00340b0582d400056540c6140c0c501820301c11030685440c0000c0c07425494500300405400c1100000000302d20100091b00b00c0a00403c040c1c52401487c4003005444101240825640082c061211001c11100415a2407500c50b005400304060850302443c1d0080c100c00c1ca00604c21540401032165041d01c22a182e8440e911600c11580c4c0040030104000b0b480d0600546142547c19058010200b424181c000d907400010107400411002c05594800c3d0429400f6000034000902880801e001c212844d891140102813804d030801c2078604121012040c0d11000300240207102c040440191001d100304495018404d4644541e581a42ca8038002028a451200025 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 986435935 1250 986434685 986434693
    0x10e030d0902150c06060f12070f080c150403030f020a020a080f10020322020a09090803160e0a03060914030f0a030b0a0e0f04210f12050103230c0312090102 69
    0x404000610012a5101201c01c070041045d0b070b035680d041005420702e0b4001950410102d20b0301c06480002008484040c0c0740c000e20f0319a41606240245152a50100c10141f0600014086039500c403076800c02c48069a404d440c00c103140f5501d2481c1a4541008080003d40103103070481e0004600b640883d00c0c1a0b107051540564280100c81d200507030a9010a0720403190a04c80525004003840040d080380515620150000c2d601135510039090381243c00070201035441010000400c40c140009070010034110070355007807060103090701340007261a0003998040107181e0341c1c1d214400e0040c0720350820710360045040e16040b65580c45500e208120076801200095000c01d0400b403c010b00303403904029500a0324001940d44081d03585018020b018034070098800d4564191240d03c00100d001143e001c07444080a5450705071545e011400020302c402c44d00c48403401c000d803426005000054030300e90a14041111401d10b82c034404241d000040c00e0100f68a003959161052080e007491071514100075141c0002c1c01d800391 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 986437185 1250 986435935 986435959
    0x90218150d05010e06011d10050906100e1003091a0c030406020a0507240c1110050403140a17010e0423030f070c051c05060613060302121e032a010e030d0902 69
    0x2d023594954021154464102000607200b0f0800c000345e8041d01f6600d20f01842d0048070000800d00c0e142030075002400094542c2441402d00c003c40008003020509c8150310955847c1274803070400c2e20b00000e0001062160000348039194a4814070580e2895500312036003181003c030034182008003c0708803a00e50315040c00c1201a1001d00e01840b203842c94181c00b5400b82c00a41304482c4100020403005000310240306448400e0700064901c540502600c1a080d12450036201151588205160050b03000304d0300e541c0d102042000082c018020444a4080c210140482800c0c2d4100e09086004101a0340442440856000c0078002140807840c11502c007514000b01c00c00700600d8421a4020901d8041d00302da00690100713000d420a8184040b0701005a50f0010341540c03680e0000f81c1c0d03002e440e10b901400e94000c515194244101d0030213001c90410b917038002c41c5400d100d80c0f400340d40c8061001007005c02714070011800058035020b4001084004c0e5100030750355507588900c008001032120002c141d000d50002150 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 986438435 1250 986437185 986437201
    0x80d0614030c060f0d1e0509060a020304050c01201506120c030601030803060d02060f0903010c09062709111308060c04091508060a090218150d05010e06011d 69
    0x203020490100508070500d800d4804c042c030607085e0f202c0b91210f0f212594035080c15100306c00600d40110100400340c00400c207400c06c0c0f811240350690143c04059214410010b00000403c00603011041640c2070811150000002e07040d1850f545204074581607a000341c80f20905101c2d26901550722176a4103c4608072111051200595145141290540c141d07024500500100e13150300c000d15400f07071000f006040000510350214100350801c1d0f0200d41d850070b01140350f00240c5020301138500d46400600d0180b1242c0d280c441c00405201514640c5020300340c0c1e80340718203507900c0041030200240000d01c80520140c0401e851840b926403144071034000d15603a03100c2c0850002d201181c0207000d43d141020b100c2c103060078450020000c00340c400c042039010114000c0001d1242d0284686480342072000c100144078a181d0050090000840c0200030340411080104950075020074103070031404100751282c25000e991464007a00400c2003054400d558454203000141c0c001b0802410043e02c4000701c02e48200d030700d40920b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 986439685 1250 986438435 986438443
    0xf060e010806010e2a0c010c0e0f0d1401020a0906260c1b06040c090b03010207050709090203071a03072d3501150203160b040f080d061403 61
    0xe0140750b40041c0300412089800c4402c80d9009525038014641c075084030500d60380242c1699161300078119010032002c029003428803036100d0300003990400f060015400e0b030000354103d02002029114410743c140c0c041c188415003045034040c00d03003071008640d1a84400400350000c0040c2c0b04107400502c00b4551180003801e4482c080154a00d90100c002c103e880e85120f09510707400a00c040c08030641ca440700c00e05105000c10010780268087d8007561241c9003800c00820aa841051030035009a00404c150000a0b400140c0c1c82e048520703240c000202c0306603c0c070000e81028902c1e0300c85d02c1c095804920701e03484444103400940c010b114036207034038081c0d407040a41207483c8080b0035118a03000c5415030075425100d0080709075144840c00307c11000000149240e405495140b0110340c1c500c0b84115800610500000c95003403030b400401c500055042c1030035924483d0492202c2c83d0010074a064180200d000c00802c0ca20b54614240c0c01401e00340c0381c0c580c0c00c0c06000200000d1051006c1c184e450501c286031810041 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 986440935 1250 986439685 986439689
    0x6061401140901140906180418020a0308030414100f05060103090203061b04090f1e050c0418110301030f12030b01020a0209100503010204032003032811100f060e01 72
    0x41e0059041c41070701401501c40780303407803020b01003882800c04c4403d103d03903260310040c0442c00607002c4d84452003c0120500c021038409a540c41d00b0301c50081030340c1300907030b48503e2107104aa6108403416aa44e035545840c0352000900314181060341300d122020804025150880011094032803410440c80d0f450400440c192101e504000e501038001c04042452000040803aa0035202c0e19034545250580d03d41904c01110302c000d680017030341c5546010001c0c254203491031408007000c40c83c8040c051410711400c810710f90310542c41182000d40b0200f80c0300b4051085500121421851140019141d60792410896212039180313408440030045801e02106041c0644030700b492216069005000c550003076800c0c0525508040c0c5100d030000300300540010307581d90074001440030707600c0303070035038401e1401c458074004140101d9074043c41c46030300203010590440044400e403035070b51507019100d0a81120500d00035a601a041200103610f070284181e013640f9400b0f80e4102441c0490300503020010381c1e0f80e42c0f80310b400402e801c1c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 986442185 1250 986440935 986440967
    0x3140c030d08072c010c170c010b0a08010204031101050a0c0c0b121308030106110f01180515060f040207062405030706030207120e0a0b07060614101719060306061401 73
    0x80c4d05900460f510424401c12054882c440b84904500d4031030140001d034008100483c9141e440d46038880540c144002000010000040203605007030660303443c062031903052440c042c1008008110039100074403d00b460121076403c42c00362204191251030b0700d06258416010440d4014441d800304070004004c2100030505034025140c1030039039080030000c9480010005440c2181d00ca500240d071507014080c4240d1080c0b1954540f0707103546148900c0c00c18240000700c0f110500e8100380380c003001a070f512440310164080740201e80045c0e561000d8500a002455031203621901c0b652140e80171003610500441c07160a0307038000c80c00c45034120360302c5030100c081e4840c041c0000e240c000c0a1071a124114000c02119031005001403807d00255143c1e03100b8400c541200070296200d6480d00c804000c141c4a145204803800d20603180c920484d45146c01c060140031100c1201020034010f100006c40000710b005640d017568445070010701805a80303041c00320190003180034581c031000c16091140590340c05958071019400c40 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 986443435 1250 986442185 986442257
    0xd030b030c01080420030f0d0806010c031707090e090601050f0d020a0e04020f0d1a010e0106020607112e0f0b010c06020319020a030509070e06060403140c030d0807 72
    0x4ca0b90360b900228803001150301c806460308114410b036902401800b10041c002c600400c1c0306030008800600704840544460f051101c0e00031000d0200b5407040c111040c80701461502072080d01e4006003115140380303503032040001c81106001c2c080600f00c08940c2034100e4030126440ca491071010010400308800c040d50081d0b01c007a00b4a82080851a071000607a401800208111001a8148003040c001002000704480001c21044103800d0f009161450501412214000d0000341d030404001946c0c603a40540440700703004014180c40050781e8100413061409001543c0243d10500e40203040700c0003101c40f00b04c00141c9041852042060b0054452482d18a80580d10103901c07640685800c0300a45c0041c0400203904200c201150414809000803c039041891354002620310301025950308003540b5801c800c000e03070a04010300c8150740d98142520207a903008a10492640e11890023039150006941d4050b0301070244904480b20f030f98004a20910407000d030b4950401c6030303602c84900990319580c212500e0f86050 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 986444685 1250 986443435 986443441
    0x31b040513020a08160f03110d1b0605040f1d07051b0607050c0f06010317090f19150e0604060309060902090f0a0b0105030412030e19050d030b030c0108 67
    0x150980016410030107000000300089203540105280356003d8100c240950700084815403610010401c10008000e094051161181540c0d00c10600038040c000880c410707000c4800801c2130004c1d688010703204a80ea080d070b2802e000c1d611800a0910f4016200d99008511079960024400703030421703201840800d9541c4c500006551b62081500c0030b420440600807240000d0000d20744070001000075500a0b640740d150707103840ea03004000c042d01d01800c000c5003910b150403202c01040040d0300c4c6640f000c0141c0e0100e0701141c0320700c0400041400c030401c0c603208662280046071072039104040400d608041c0ca01ca08514544180c012030183c501c84040b4104a8000c0b60400080080720321990007200c1d070074410700b030104030130a141d00000e40c03c40d401c3d1035403402d0b80019424030501c01d5152180c001c00c4117003030a0950071031405481c5c1c0c0070368814522248013816140d01c100c040c0a6010700c1022a28800c291150110303000b01d05201c0c2d50784041e202d42c00d011038134200c0c206503546000904120070380d405940344940c030340e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 986445935 1250 986444685 986444689
    0x705070e0405030c01020c0615030f0c0618030a110a1e0b030403030e0a050d121802091003050f15071110320402040b040b06030117190f11031b 63
    0x105000384142c0b074502003440980481d00d030a0004001c400260001440c1c40d013800036810180c1501140042e100e5846200100003030305022408084512007220401e40745c46010480d9120707001e8a00c502c07613142c01451109000c110043c5804c03a5034071402c0d01e1004603103860304a2044020801d1106480e101c0780c0c0b0b40c0c2005110840e500443e442442450701080020380c1d180301d5450060302002c107c0e401d0300540700f1142550303848800b1068000b140803007402003d00203603e10880b0100248003a0165103444000340303002c503942c0c15950040da40603044413682d05520050036111110344040c894004170400114640c06e126410350f050005018019129098111140307400400825501d115160804150360040480a400c4460010300340f000c3e6900c0341ca880d104002c200d603040c0024910176450051209004d0b00c4007025a4103466000e0144c0c000c402010540b20315180c40061008450305080389044c0c1000442c0d04600d60380d910030916111000e45480c01c05888815104001d4110103523440308203035038 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 986447185 1250 986445935 986445959
    0xa150507080a021c06150840051501080c040203060907081e130302010501050301060b0a140f030408090102100516031d070603050601110316241407030f02070507 71
    0x71200d440c0e82104e03040f01c40a204d070a4a4003a4040e456115240800d8001c454004050903844049013020701c4600100300e00030242d2043c0c1d8112481d003a901e120b51512002000030090740f03c0c0b90014125a030303501c042c85640c07100340c1007402000100c0c0190103060382181020f0080c0d03801800020214a800c1c0e03108a000c4a1100b002400c1440d021080614070150f96000c841349401440303140c80c0b00c00803c0c010308000e425140d040c1c1c0880e00a0307140c61000c01110310100143c40070001e051404113070740c41c8105481d00d0b050080081e8031101a81c0001070004010304a0024618041d00783c0a03501c4441d030484001080301c1044038142d00c218890400d121540e4826031082d44103140d10441401e80d1600a04100c3c9801344507048907001c241c1d20750030f0001a40c0c0005040d072001e01c8410041d407501c4080b81481c0c2a04001400c01403010084801c0c200361000b80408500c905074080c0d20410023130000f02c0e0115001c0a0607540c00700400d24040b10164202070900841d440c41da0044000d144861810703001180c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 986448435 1250 986447185 986447197
    0x90506060103020c0a170a09121112100e010f0c03020315060c011e0507170702030711120d021b010903110d0305070c030302160e091005071101020c0a150507080a02 72
    0x4c180204005940080c00210030980792209101c0084e8644a102001030109850f942000702030307450340854803001419a42d501251201c09881100e41240164011807808801080080ca0a4200955503800c1041507201c85204440f116041c0000f0840000c15000c0b44800d59500981c034841d46192003a03424044004c04e044210700c030001861003611a40c0b40c14483c3d1000034400a951118207001070980d11420b20003403038000d900c20501c0340c203040502940c1c034030907680c000304981540040ba0119030b4801030f030410a400b862007500c1400200e410025110400041c0300350720604c110055007484e520400e2004141e9500c81c0115512010f10b030300b04003011003281d030101d080041c10012400050b0031441881c000750320a800414003644001951800c1c106160001c50584003100108200c40400265141201640e40800035040e19401c8084990700b440c0301c95000c2035800020506041c02e00003401452942c01039000109c070500e24052201940e070b0580d00040050456008600b40141c0c60b401055 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 986449685 1250 986448435 986448457
    0x71d1f020705031b030601210f29070f1b390617060d0b06010c02040e070e10150521010b21040233040f05120109050606010302 56
    0x1e280d503a22000070345000d070300110400780c1c13509682c41c00f4282c1c101001410302500c1515003d400180141c20340c1c01e0511448140a81001c040f03940a1060200d441d00c01c4049207014803130303000b0802e210060083d004031300b0b03103080000420b40906800708074468112915420721105103111500403607124000c01004ac40004030785801900c40d060749138540510703014088051002045491760ad4510068003611707800c1e40210140320744100b0403400360789905900b54502d5001e1103018080e225640104e0300c1c94880100250007a00e001c4103071040100c005040000c0310010380c56001d4a81e030b0010500d06010707561003200b0102e4400ea0280c401c80d805103018045000c40d0b210300502e10300041b050340e05082001e91000d0034085001690203840200c00e10b0800082e60741da0400640e0b130800d94045811004860541c6000f005580c9605001d00180303e0340001071590b020996456548801074190045070510516100c1e9210500040d0801d80601903215880c1e0001d002c0c00c2c55a2b43d04005401941c40410900 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 986450935 1250 986449685 986449693
    0x5030606060d0e24160806150c1f0608070807140d0c09090b060d0b06041a030105090c100809070504020304080f03040f020a090e060411030a1406071d1f02 68
    0x5840400070013401202c160030119503200d04507024514620840060800141400c0a603468850140c110301c4068200707070252865080307290b44074044001c502403224404d00c01c1c05100c0c4da5904602403c245440d22200c580c10404ca9650750303041c41640c904603441010b0321504004020016840307100280810050003400303031080e4400d40c1da110b2400902d01e130800340300c1c20f1759042118103000204011903030112040c3e0b0390011132400c94a13042d84000b80203101c94801d58440700c80d481030400d0a0041e0b4814100a0000c2c840f90900240f80c0751208003640d245401002d284945070b1505201e41d4105004051410180010a091009110280d0300003402a40d02600c1000381700f0349040c0060086100d50300461814018110b0351041105405056002e104554202200408241e00204206803c19444003400382d00c0c04814020a0030800504000b074503004040b42d0720804201c0100320280304182c240c2d500020703c4981e01c2c0e04c1c82c0c0282c8000c07400c0d8012480340283c007018841c052030500804400d0040f6 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 986452185 1250 986450935 986450951
    0xf0504170a021e19031806030b01020a0b0c1c0e0d020c0d0b040f12180f0612020313050105010308210f0f0603120d020c1606020a0807080f0307050910030605030606060d 74
    0xf0410340c9414013000c03800580150b00d40424011242d14480143c80c0c01d1409106141000340000e65034605010058828030b12900892801807a5904503131940d20000b22010403106050105002005c45501409160050800221440d880460160340300507000b41aa0705036501c64031010b4003e800208211001000f4481000100f003070100c8a03504641541c0d00c401250b264a580721149030f10b40da100465442072850140429900620b050003846c04188005072a5a00d43d08010390340181500c0180c065460f040c000b01c240155800100f003070381504843d1455644182c800f8010104049902025512020010855642e003d0701e019402c00c030014110740c06007000703191500d82c940c0b01c0c00e003658050f40e00003418030388090240140c00c2c0f03028903c0f19181c14186807050103521400034404c020940440040c0304820402440151092160f900400302d88a1500c0c00700941154441c02100707100d180a0743d820300c0382c0b40c406d005902c2030300c1c2d0190103805507031034000c2032200d940c109500685d071280d1910740e4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 986453435 1250 986452185 986452213
    0x10e0a060815062742010f11210c0627030c190519050109030801090b0a0b0306030106030611070303050708150d0c090f0504170a021e 59
    0x140d40c545a9000310301000d80c00d2840800c00c001d110413907001800d039080e5180a002215040325103a201d85501e0645520045a40049100075141d10f00404803045d4111910104041c003650114124000e0300e9010310481c103070b9819190b4100024030204c07985d10808000e501900d010200520f28048840c4660810400301201030500104540e540070b000d6644100400229105c000c0803d8216114003851500d00340c3d0080079281c00d503185250340c0090070b8616290411008001200c0342110307c1104e03108006180c0f5059018200a480642c0050101400461100064030502c807a0800c003c2040300090729000072141c454200901050303065507902000008031b28540100f096410781c20846544d10803d030300e4045c04032600503040c0360400c04500704002e80008903103c140303030f20309003210800c0e44040e1601d441c251544141e086050321608248203104100080d40040d4011441140c0e05800021106400600c0340074448141c00103900070a01d034405040420f84407012503c002003920910518006 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 986454685 1250 986453435 986453443
    0x2041815050a0f27050705060c0706032003040624030f02150a09140406030c08010f0c05090109030f02030a0b0c0a080114100815090a1a090105010503010e0a0608 71
    0x244a00096118000c0015142103880f501c1c0d0350b0011850100300c0d40c000c110141074010490039041d0008000c8005540034840e040203250010440108038a90350f403103c00303481e0780f9482c4a2040d5001300307060409240350f64011400021a00c02501c48060966480707485184c060302e20004007a000c043e44843c19804a20145a41c101441c091003003d1072102c010f20502c4042212501c44000310fa40c02c1c40701086031540f0400e0302d000c58a0131508d00114450190010300184490360004182110f04000054408019000344a00d1b00d00318004000114000800b5907140c4910304c074490014440340c0e4107100152035003442e82c9415001804072030400b43c196071030b001408019600c018445902040942e0055840b6000b203004d4800040109015500d00002c104200da0b1442c0c3c10051150755030001d0212291850104200b80b4010680b0b24542410f54246006090800881c0d16241062102e8607840c280b62003400e0483c0d5040e96500d03c1c40c0e20701a43c1c10300368000605500070b040d480c0d003000240d24030100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 986455935 1250 986454685 986454713
    0x105150d1a040f1e1407260f0403230d0e010213060302031f06170402120109030503010807090204050f1002030f030c040f0602010b0114030627151c020418 68
    0x210740040d60700c0211004803d44000315a40e01c04603424200090029480b01e40d0007a004160707400c00822407051552040100540c7c014001340d000040700030000c1039940b865132240140d0080d152880348905400d0750400e0007140c0718262402001c00c020740c1591540300d910920004040c500010b04085613b018040040708a6000000107900802440b2141c001c02c00c52801602004941d0317a030350340c54864082c00d88460a00d4200160b000d0b14000f4055440d5481034034144070122008000c40d00300d23480d02030319541080c0100c00b802c2c0b142c0c66011900c00214401c03a019114028104003105401d00c04024000d48411000811808140070364001002c90001441c040c0c0207801150f03407910304080c103031280d04100d070f8080c900b10381c180344000000366003041c105840b00d1800c2c104a41c0c1ca50340e50740032882010051000000c24120f542c401c141800c0b2545905010380a24000070000c0c100220070800034440034070042903141009600000145001e07444026480d0300411400000742d07880d226414141d04e42c0c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 986457185 1250 986455935 986455961
    0xa0e1008030f130518070c1133070308061203040e010603091106030103150506030c060a020604050f0604051c0212040b12090304120b100317040305060105150d1a04 72
    0x416210b00f40d400d0b0750111005800140c485103114038600038900c42d00c603000f5100c9400d0101c0b804002061140c0703241000808240075101c0c0001d80288400b1004610040d07010208a020504444140d81c2241045800250301a1b85010258807001e041020440400218418038441080002001d44a458a1b64028001031301c0000d41170520b030410719405500c0303000203885110204014000075103454944e514680c0c803490001141d96585000c00d240110b0a01000d500103000302c1c1180c0e055900081852280384150305440d200c0c8030b600419541d0304000c0c1e8000301290011000380322403900c1540650541030361481251080580204031981681c019044072071210000280500701c02440f444842d04503100c10029480c2500e40030b442c400b0b01140b2640201420384200220f0300405003010910013a5800c0070040302c9510903a02035101c0c40d406880121024000d038000042c103407609a250004507505c25411074589409a038080c0c00078a444503d010341d00c083c42c080b2102c5a140c0b4402d0f14002080 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 986458435 1250 986457185 986457187
    0x29180406060224010e010b0a0e0a081b04090507050d2d0302010c021b150702030712120f0212091f02010c0e0f060a0e010210020f0403120302090a0e1008030f 69
    0x418003460700030000e00210101c00c0e880c43d004100e43c41034440020304640b0040400c684414010f0b1085600940d41803100394820014140401c0545004ca804103011050085120740480b2050a001c15140a142d001d04160400202041f190a1200d00008864841c40701200c1c04002c1c04c500e04000d012080c0985880008042130b41b0402d43c0910500304254800d00040030814105030355102d00c0d4180c114a02e028909131628030150040100075100102e40c01415a07501c181c440001c030a81000f44201a0f990b6201d0000300244240207140019420340c1650240400449d41901c0100e143e0007401410f0300607140c3d080e00c0521140e031101517007000c840c541c008074041d210b280c00242980000c9030011722420240c00750858954480301220b20500142c00c5c0f4a040c802c2040050f801e16030018801e50006000003001c21038078030a00700400990b48600d109003240720481508804138011408400c0d00a08010024000683c000b011240e02007071100b188007031240c80b58981401d58001e000342e0941410 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 986459685 1250 986458435 986458453
    0x9010510050d150e07020307051c1808030d0b062517031503010606110304170708030c070302030d080c07150b03030705060604050f13080a0c08180a291804060602 71
    0x280c0b124410b8110702284001c5040248c03944400c0e440f6044802c47e03401c4000010b00310101745000d15410542210781d000900801961030300c0f550b40f207074000c003281242103161031a10240e5103000c0c42901c454801604108001100c104085124411181800d44a45010154001864214400031886010070704c5520200035807880034103007900c000f5049401485104a80510005000000d07a4102c03020344c010000e0700e60b240d819990034180c0b40c0d0000c0c105400300140b41642c0c481d0008070721080780d10030b030101c660701c003107528049a0051040e41d040b68220410424a0041040240e4064002c001e55500242e0501d112001078950350001d0402c0710345400c03410412030780d49414030603e0f40c4400e070400403800920341040702c03945013401c0c02802002000301080e130b0354400344076402102e0700300d034401c000554031402003149213001c2c60300308402c80c0301e0703011500c1c04200c01c207003c0e40303031202c0c424100f6408030601d0041203454141d401ca000d603600400550340030030f801555140510760060441e078015000e064 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 986460935 1250 986459685 986459699
    0x60f0516081206150d02181513210311160603150e04020d030f0c2f030a051e01020f121602030306010e0906010210090606210209010510050d15 63
    0x2c01c000c00d0b0703d114560211401c4c25580c400e404555814040c108010307654000b5650441e89550303089040f94000c4103404045c401221494020014407090307a01100880c0d5683d0b800390520007620301c544554403481040b5a00003401100340950008118064555980001204500030403c40d8000f00000e51030342d0003258030300d90124000c00a03013804000940310f45401d801192800682d404002c0400c2040044001c3d13a9209848500e0695800420005010403200d440740505e54889200c06803c41c1c1400c201c175242c900080c072940c0107175016010b08010780340d0a407142c0d11500945141c002d255001c1003001401508100107254004543c003282c500c50900e0f040e070550613240e0700c01500c00d6520400a000300b036a003201c142c4154460850b0b000849940b80e00040f4104600c1c0311030b103c0744509005c050820000303550440c40644051407070a1144081455114214450924010350458580340050007182405182040c044215040013490841c034514010b044a0518031104800070141405200310 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 986462185 1250 986460935 986460967
    0xd0c02030a09141005031308031e01170a020427051b0604210804120f03020c010c0b160e03030c0a0b06040203221103030c0f190804060f051608 63
    0x1804014184080030f180140c0443d00e024981d800207030030700501100003140014900c0701c500b0070303035800100107450f82414505846903c0c00210213002e964282030000c100b42440035900c10b08551294000c2c10400559024000203203e22407a210101e61150045c80035098103103550f101c8644940004e003848900041c0201c0c010b01c0e0801d41d01d12440c81004100a66010000301801c0d443c0004100301207224240340080903881140e20403540002d681401805000a00d55916030700c034044d800799204403542400441d41d103492150300412200105010440c0f904184400c4500c2d100203060841c07012039944002441e50304a10300303e403510381c021200c0c40108403002d09003d80003101924294190300b05100244043e00e0f485540320702100e000350408081c084000b1034001254400f60903240e030394224a0609866103905000300c1100e10039003124900c2d402107883c41107280b98100007070a090905258085031440b4100c3c0c180d80800400384a01c06d5031110503032181c401140704030007159852443d0441c003040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 986463435 1250 986462185 986462189
    0x1234030c03020c120d0e0c060a0e01021c05030604050a0507020a03030e1e1c08070e06030402030c0406080106050a1409161205150102060a29061b06040b0f01030f020f01050d0c02030a09 81
    0x14a4100b2040692244c84008c2030307410102050a000700c611103c000101d1800d100480032204140c5c2e0302c1c01400e0625007080085020324415641032165507507014603082602c0003521200010b07800385240d103020034413030f50042100644600640300d51820214000d040c809444844500303941191150b10005101c20590341084010382c100001c00c1c0c83c100c00c000d403d5201c080b0485001c0c01000000804565061156210b0254000c004000150701c0304038540c024030950046c11b026170b06041d0045441041c18084040d441d40c001c0000d8216a1440c03040341c540d030400c000034411310003110080003040c61a80030b001c0c407421030710004003200782040700020700d45030000d00000882c920306418040340c800728450381404081039a09203040090717040c01140a0344100021250000c0c0e01c00c000c1c4d20011000703d1010300442c043c0003d8139044d110030450005041080c840209a010030b5030300f40d801030600050321440f203c01410030500b4140096404015640e02d9040702005130400101c03000519041062400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 986464685 1250 986463435 986463461
    0x30c0a11071202040c0509030105280506132007030e0108072c061c09020301061e05011b0515061f0e06030402040e031234030c03020c120d 61
    0x40c0c06203080b15a499150500310064000c070388038144000400d0003001100d900c940090000c010a10b840198081c0144c0101004034402034000700a0351107604034014a40a00e0004084100e85040c9010f040014129132414030100c100c80c8100900f818007410150104600a44601c106101d624000404c0040000c1101041c400c8246503000361900c18000020b2034207441035903180800010f400169140140100c60220072040700d881040510160440d1101a2080c0c0082c0030307050700e4400d4982c091403861516080c4a8090400f0060341d885030340401c0e6170343e000c901041c0c00b0600d1525a81e081c0100400305c0f454503000c0b4014000142841d00f070702030034403000c522080c58411010710001c003440f0045840341e205100c007001040035581e031a8803072418101641b080365600c02d1000304016a102c1d00300c40c1030f00c698082030035942241c12140c1c001135200900c4100c0c5a45110400000d81c020540c1400142c1019401c1c4074515801c0001c004e4080f02041c5044500d46030741160745a0819107100c00888a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 986465935 1250 986464685 986464693
    0x50a0504031d01030e0a050102040e0108240a0b090103050d1e12050c0408031909050102120f13260f011a09130c0e0106120e0601060c050c06030c0a11 66
    0xc0042503101c0b200d039820050b500ca00d18015050310780124041e140c0d40450341c16502620810008200055000304100c6515248490150381ea8030b5605071195203140740c01c41020701c00040940b08442103442c556010411301c8002603611140c0380401c1c80032038240c000302c4143c0e101d21010b42e151a00321004155407040c5813800c02c04070f000c1c00310042614100c0c2a98903041c0d0345450104000105039025500a840030030122500d4080f400600342c2240c2419141401203a15200040313103551020a440c4061081c82da440e51034030380341815000e11588960324020b9840c2c6841d07008610940d003a0640c1c018011010600880100c90700c01c15410a90105050417485c3e15003040c0803c0440d1000c1144a542001ca0341144590307102c0c103c0210390321b625076000b0188a000c402c0451401c074105501e6050701c0c0d0903550304c4c44150b02030b0b40100840d1115610b10300d0640c040d07401004030a108412054840b0312503010f582d41141c0000c00329159400980b034034042c50f01e0200b0f101311000d500401c22004420200010 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 986467185 1250 986465935 986465941
    0x3030216060e150d1104030c1401090b0315040e01061418010b03071b0c440a06020d0203010311030a030804030509041b0206060a270902040e0303010f03020301050a05 73
    0x140c21030030b1031840e580c0a540d1110740d20741d0303c01004040d104ea041c2032080500403850000c000080540c4107000454040d446080d01041c0c04d0481084032000d444180c413090a00740c200f441400003a0002414004d000502072080d0416031128000c506040f00e00e54000b081507810103c0c402241210116001d02a49050b00f22800602c80340c460300d41141c02c21209181e894844507412950206034400007019088558013074400c004206401800300c4421300d009500b401490448603138504c00c1d441040800d170b41342d0107115000d4002282e040601c610000200c07081d084013961001c003a0381200f01c4691116a01000400600c0803010500d22402d0b42140030345041101940e001c0d00015002d00090308104002c90041400d488541c00885894104041c410410f071494200139130301d62040b42c0103805103a084100054102d807072032104920105942d8202503025041e441c40000300008801a039005440d5a00010001030610055000e410300340149007215007180141403c0d18000740000080901d00010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 986468435 1250 986467185 986467187
    0x120a1a010c3f0201061203050304031416050f06011e09020a0903021e030f07080a080702030124080c0105070309050d110604141212040302090907120c0303021606 71
    0x8200c40d480e8080e2590307920034401c18912860082e49880c00800c00c001d42c031109021091006004400d4a2541c001d104090700c4040c614403207a00060014040750301480800c00281c01001c601c01c8e10b45c0314011250a2100404379428010040c210907100c0f600403049420003c0c1007840031502404611240c0c480781445a02e415842e04620700c580c014260340130800070310451140208030000d40d002481d8034104a80e5000703e0716100e4a46c05070070300c0791050b008088072134400882c400301150724800190880c4443c6880b001800d5009c1030040307030715559402c4200b0602002c0d1511034a80c03004208811811802e02113032900c2c3c00300c040c075828184003050002c00d0009610107140000e40f242500c030501d494466203400203280c140c0c0442c0940c484d501140100c2c01a08103011845102c201b2994030344071086440415031205264425050180c7d0b04020600140c2000304505401080f0721084995156540350100803044007c2800c541e00d003540203040051540c104040075090000ca070850044910701a0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 986469685 1250 986468435 986468447
    0x2090a0f05060a0f030f09060f05060a181109060c010c0206090f06013501150f03110d0f0501090f030915021011040e18010c14220b120a1a01 62
    0x310590820a604c0d41c10903669210380c10090302409200b600b440742115518050010304072155008049510b0070002405074946600858111094007885d402001e480701070000c080c007c02e850600c601181040304210a4407040c004080c1003000100009000c1c12080d0000d060020181c200c40030750303120142e502089070020800e2411141c030f0012407001c0c003021551550203548e10a44d00f90020141c58291005001c0640005800000001d090030506445030107003c101c01c0310b404007502e060800c178030110300b0781084a070030722000b4003c9907203d406400c01e035241c6003520101c010850340e904c140e861071003c040d0802840781c00380410361603010030080c00d100c00a541e403c011800c42509621800d40400011001044502908001e030802c1002e1070700d8092902000341c448140c025541c80c0c24581d1408600c100e00d0b84d03096084680c0010b01e082d804880300c1c501d1418070900308140098000300042c401c0e040d40010310580f080244c0f929842c2c540003416404542c1c44401c1c05102041d10000d4107a1071781d01c81 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 986470935 1250 986469685 986469697
    0x1203050c0a271d070201110c120706090b0109021e091014040b0a0201021c0c05042c0108060702060906100302150d020f0403060501351f02090a0f0506 66
    0x1006201044600c41c0942d003008180e101811000c0540f4120404000aa00300791154046400a12050340040c09540c1584220450b02040da0007134a198456000180001c149043c003484001c030f20881c03a40c0303845466140aa022480681c1d000505090000302c14140071060122045807508007401040445d9602d613440290381e040001100c2070201001281040d10040e0981024064a40001110280c001d502921080a185203545070300c3c440c5405038000d02c1101d504681d1124200b0385001d07a121004642c0064500d00e2400380008580300c1007a041c0168000d01c0c1d802d004001da420070740300280c180300c00500080403642244080140945005240d181100e50541d018100045007108588007405071240340d052072800010b01002110118018bc03060700e00801d810030580e40d88911480f5402080111803015804600072862118003920f480310440008006072420b10703a2041c1c07018003051303101d142400825800b09220706241890b06054001d440c0c202030b5600854200000201140280f03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 986472185 1250 986470935 986470967
    0x2d0406081e0c070809031e010b13091113020405030115030308090105040503090f1305041a31050f070f150503010e22050d021f0b0a0e070504030f1203050c0a 69
    0x5100c0c10181c80800081c801c12102c7d1400e00540070b050b074200350183c0b4510022910448518084d0040001310744100d080d82684050741c1d0b80f5403600201400007051500024503c420ba00f40800940c41d1400e020340e034020343d420320240d00006d05601e80a00810700242140c803880c0e24010803c80066030000c01c58200030401c94144103c1002a000200c0c8584401118a040340c00c0000b4001000b16203044100c40c0c0e40d0000f03807140300b603859000c40f40d80e90194111005407469013101c4040001003400885440c1d5008a0075a5082c1e0381d0541c003c0c3ca8504542e01c240758040304004100020581125202612001e92400030310355403500304010803014000d0710040d220075500320302020b140f025030750301822a503210003036400304040201c3c0691214840c04034145107014a030501d0003088100e203c1d81031442e5005040c10959420070b4081c08007000c00901000900108000c0880410600c00398840312621030b9607481b0313a00d2041c4100600759000500480300300d0030f082c4442046542c120b1203114800b880 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 986473435 1250 986472185 986472187
    0xc0606151201080c131506080c0c070b0a080f1612020c190c0b160212191b0609030218070e1c1a040b010909111206090d0f052d0406081e0c0708 63
    0x411140c043c991050045030070252007044000a840340906010300637040c03041d01c0c3e2013440c1d41e440e041203100000441d10f541e0440348005e1b4a8500b640586401c0c80600549000103051664034025146480e40082c10b6000840c2a0900c400c200080c0050704809004001141810b0500e4810384800401c20110020b1003607500c00d45021044c0400c0012400051240c09640805030305400d20b02d900714402c0b081c80000007500e010100708103000d0285003049075405402080c8003942e5240c0d2942c001030191075801080b11645c2036600a40d605c1c07010b20800f840c10001d4205102c0c103881d10f48040c034000d08c001c140c10310300f030400c01003c01c629803810342c1113034001c020100d850451031420000400c900d0b4240e5500581d020085900d40b00005030562182440340102e8103500e5850303100780c8188030010b65100014408105440380d005404c2450140c0000d44c0000c964085003100000d81c65410903003000000a8107807003000342101d031801c07455641240004122a2030309148600000e28800e0309005005410 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 986474685 1250 986473435 986473441
    0x1306050903120f04030c091b1d091603140f04080a020102090306130b130210031a0607030201020a02070902030103050d0509061309050901110c0606151201080c13150608 74
    0x3024080640c0b450031007810a03076100c2010010202c581c00c540000e807001c0c6642c07a40411004400c2c403400b5403007042d522582d800404450000c50303500055852104080545100f80001e40d10f8040c96180030f51130b40480581c165001844c0101101c0000c41d43c520740d000c56209000850905c0314105801c2500030016980c1e903400428268064498902c289030544108400c0000e12072180c1c0310f51208602c181580600c0e600c810300f61102d00000c100000c2d50005c007c02c0902800d9000b980503070304601c90036051503070b81101d1000107299504400010340250b500010104803096051107010041c007109001181554115141c040d81c2d41b180d5441c03807040c040001500c51040c2c1c1c41d0800d40d0313158242ca202160b01551511106005804265007540c015801d148000d46551001c90940d504040d45500904060381d0b10b0003000585940c464204d96000001c0100f08500f940c0c401300b65018001140003040c0b0241124140800310307185e0009111081d1601c9a81100710340501c45a10403245180f030f241500352 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 986475935 1250 986474685 986474689
    0x15030411061b0d0804020f040e060c0d0b09040f03080601020a03050702211009140111030f0601030b060304030302070201091a120604020c010608070311060c06130807080d05060f0613060509 83
    0x100c51000c880c046205080403106004c0d48180200e00c141d100b0faa00310400d00d115030601040d9030342c1d0342c2c01c0e005607007003100001e900d005002c01801034a08145000300390b560111010034114074040d10241c03211007800030b80d0340030726402c071220940003403082c0f0045c03020240a840003030030741c080c02600a01c82d86a039504940c1940c0c0b843d424905003820041999a0309101d005907000030160100b04503a11030014000d03650848042c403598100c3e000304801140741d035881662400280000034215818980d03240058235803511448041c52080b0302c2902d005903111440c0c000035001d05000e50002c4004120a044c4c3c41c12500c0700d0054031006844117590142685501c2d000130080c4c007420500c0c45a135817802c0701c0024a9200010703000e086074001c041d003421031264401407142c3d80c4265004140168004404181c1078120302c3c1018044901030b4000d40d003801d445a07a01ea55552140d0f40480005032101e00b440000e141c9080d640c1c06030341c011136941d440d02050012101040300c0a20403a000c2c404040b0341d82082d6 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 986477185 1250 986475935 986475967
    0x20109120501051f150c0c09180b07030c050403170d0203010e01031e080a0c050f0610030b0606090a1e09140a18030e191205031207030e120a05070506151503041106 72
    0x348c807402d1003c1c00010101d60000241c544105c006485401454021030b01450007807168401090700c5569a518150860306c0380400100d040c281c902200e1406c004008101d0441d00c00766010340141e008060107941340d8144804000a20f2401d9200c0190705002000000d800f07200311802601182045c81d40d03400d040c2801c0d4146032504003498241c4c0150010800540010070703286080c5c1c0e2103110800c00c40d807155010700600d4026148444d800c000691020700c14010580e114880c0101500c00307480500c2d44a0010030207032503903010740100780040b19040c46203454450007880840801580d0801c00704c0c9003500c0c018030400300c1c800352a005908014600d1081c1d0310190003840134241030703d04240703803142c14940b196803a07110400030410303c0603074008103107014840d000d40300c03c40c040100140032040d081d4080b02d0150b40b01d601e444003030200070004000020b8007441901d21604000d00703400d000c2c41c00b450900c82c03c41d680340880c042044007081044002509940c0c0ca4003105000d850356506d448240c0414941c03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 986478435 1250 986477185 986477189
    0xf150512090c091501030f0e06012709030c0209010e06010c110f0415051f0903060b010c050f16052b030507050a05010c020c0d120804020109120501051f150c0c 70
    0x8142d070100444c0c1c04003440030394519002a038040081e11070030b824070812101c45005180e80c0e50485070041101642d070101c0c007200202c2951546071241914030a040031960b607610200c5c046500c50f1200c0f4154039114101500501081c00c000f10030303141441c002090b520005000400c882c03480c3c0003d6810b0340342c40104010224005d0400c014110b10181c00024403000c0b4440c05101d00480006000d0b040c1d0303028410465501d01d915401c01060640e6111400340c962404200d0401480c18691070110780c0030040c0c0d40069841c031005c0c0c0400c05d4210340b04041e080454200b0760040e554210702000f1580d42c0c101040312058002c5641d002002c651030304a41d944101d41022303019224500100040c00411740c4079007900d440e2034003200c291010090070301c804e08845080203010511040642009036010300040360340188145003040d0503035204c0e40da0042c07424074883d040d6510703951002000304c1d4144805194510012240c1014100d501d09002120082801c240e68020096101d17115400c00400e1209400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 986479685 1250 986478435 986478439
    0x1103060105071b050402040902071e02060a030c2a0c1401020307020f0a05040203090d1205060d140f011e050606280e040c0806040b0d02030c0f01020a1205040f150512090c 75
    0x1654648e2a401c0e840139422004007038501703a03039a04488000005005110161540c090003103400d08484800a0300141003002081007070004204140303c03d008403c5c1c0041044003071040e02864911142041d0054244d5030304992042405407600f000145c1e000410b03a1007a550444410840c02088004228501495880b05800c0b50003c03081c00f02021010500680300241940c0350503211301da50007214282c51050f42d03c150001035110107100030030b01204158554801c518200c0c0d028251131400c140c2120740e40641c00c500d50a00034801042c41200d806516000b1100b1618907007415940c51300340796441c04440d48074420044a10821500342d008074100e140102d00104200302c03143c054180584400001c460140c405c0d4034100d00b103011490101e004401c00b907006001482d1540110052040503a40444228150b224408443d0f00058596041000500055070b0f21510b0354a030402c40c008030040e07a0001003002d05104500da101c103034403070142c4041c140c0d07001c240c400b90703103864400d2401d2241c0e8862550f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 986480935 1250 986479685 986479687
    0x20a0f0305013b130210140d02070f15050105010e0a1d09120a0504060e01031e05090a0f060e06010e07081b090402030405070e090109170309150103030e01031103060105071b050402 79
    0x130084c889a00042c0320b1402600c01480c2880003010031100d0803007008080521080038800015428482d5015040491295031302110b508101e413515130084045806800c0010f4407540144015644001c00d10180e403015500300300901d0404056410054600d01500c5003094036400013103090a08011007410000440e5030981e0b203122050004005500500424001c5501c503984410039500c6441024410035400c044c03560b400d82a40c0d8804060040604045100e20070b0072034010100e032401c0300391843c441c4078400c00600984500074841c18000145d1024180c02081802c02100359005034030954807181c070100f004182400100c2070300041c021090141d41243c408000c00041140c0020718205076400c50420f070345642d407440340c1c0c5402d035400d019000345001c250038a4000e00340162005141c0111031001503650780400c0c0300d6554440f24003607000b580000c11104441600b5605403007548680072036075015914504d0000f00103800d900c1169401407080c07035891a9414284031200342c100107024010415 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 986482185 1250 986480935 986480941
    0xa0b160e060a091d070c0b040c180504060606020c01080f09191410020c1911100239010c051c09050f0901050d02090c1606020a0f0305013b 61
    0xf40004401c0c020907a4143c04c0c0d103000700141c1d0b0714a589520130540c0d035580668001c51942c0f02c1381c2420300074208a42401501c617000c600a5455a1041d194000b2501c000034203113882c0c00e000083c0e0781c01c0d50000c020b540006000078210f0b6440100c03540d0111a001c440c03225a00c2e00f1200f90b00e411080d01030702c040800c441c10007404000848070060b00051440c012140710340e85400645080b0b1003581010196a4001c8080c6003d0491100807000004d0103400c2c4031090740d2904001c245217800c042207910041e00b0a01c940340d0250503614a4140f070b03036500b50900d004030348542440c01e040c0d43c04035001810701c2a0091680c0401c0401c05c1880e107007062800c1010344555210602030b1501c609401080e0bc00c0c0f4840000742440e04044903650b0485000400e0600f070700745940c00340420924042e150301c4250908100800e02848050f060b0300115201b42e100503030b83e5950749030040910403140740310010141484010042070f150080c00750341100d002c08502070350100b400700200351646002004544140c1c00410 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 986483435 1250 986482185 986482187
    0x705030615031b010206150a0513061d040c05152802120c03030c0703020f0708150a0e06010308090613170105090d0206130f08030a050105120a0b160e060a 68
    0x206000000702a001c42c0c410700419403004140d1498204210b0041c3e1184001489030307140807940030741303690700602458407480d1141d010640580048411702104c0c0d8035240304020449003110012142c034455000e010542c14256140c0d08c2e8030f40c00d8440c491007009aa81c42e0760000610300b003214003260200d0f40940071040c07a007500441080150160902500a0b54150103014070703070100300c62440f0900c1c0d001d50b20f0356941c0d5403144240e4011400540440c852592001c852103801c0180781d0113000503200801030031503a41c99084051100401d00044241442040340103280c0010700c003815280d10100f440d413115404000710b942030081981080e8009091200013481052054100214918003402030265543e00481a0350340c1d0b0b03400410000503440b1800140030343c0c0191400c200e1640c4554020b28155a00e0b4540c00b4250300152910f22715280d42c0c1004110720301e4000d50080c10050b60304050031038405103071240b00b102c2400808810104404c609034110440c8503101d80000041c00401b41070b107a000e0b02c80c0c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 986484685 1250 986483435 986483461
    0x120a020417010f0b03120706150305070806150f06031b16031706010302070c0b1c050f090c010e03070501030b1c200a030b0a020d060f1701061a031807050306 69
    0xe0b81e44441c946120700c0310a05001c2a1b0402030b01d038900c559841c0c0386040d514000200505006019400340f205e00200020701c00340a10f0004040410040540d41081c203403105600003421289440381c5c01001c1106c0d00f0ba02c800c420b0340c1d4005402d2807000c003000041841c1042030f03c503084648070860f0300200150304240d000150764540e901c0c05840310020b0b42d25280190100c2c0f00c1c00c080034001c4840e07a002000111008402050156034200040d1240c05561102c042170f03410644030042c4007400c074070812500b00d8041020a005103004d02e8412201581c4102082d100c01d0b682c09010704240e11f0b0f241d0710545464130742d004058040314140c0c112a13460703541400348580c2c455180701c44661000402c03145542c80c00c4550700064070340102a001e102c2d05d401400000030f40c8211b481100c0d143d180c82c400103080c11440d28400013050580e03103801c0c118010000c26821549a50083e20f441001d007a0312003040000007080e42d034000c9003c00d4040744610b0b0300048900d0200c2c103503c0240d2610803c0104020422110 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 986485935 1250 986484685 986484701
    0x40603080a26010f030209071106040c0302011e09060c0f020a0e0709090908040b0306040f0606080610050316030b1f17070e01121a0303070503040e0906010b120a02041701 75
    0x489440800c9002c540c40e950001003032190903200f080d1a1818405880c0559034075401c0705450400701c1c44446a0104542080030444085e560058044010400d65800011050308999903480e0190a4424540094544210303402400c041007103030001b1108110a0721805040541c0003000c00192942c1d07160042d050320340880d0104001511000001502e03d9140511202103501642c102e0600d41014100062504010007155200d5200c2654905c58410f03807290034040c0ca26030361000290701d070040c00e0108000002d5000020018100100b00c0380340c5541d01c005030b1410310f51034040344441c01040043c42c84820080048900300c0c1940680c800c2c140c101500c01e00321200c4204016240d511300505071070390640c0034221408202401d055240c00031a0760f10684d500c4490101c00542c5000310301c0031078a5600800c000711115480043d0034003020f0500c181050340408040d006014a42c1012001481c42c01400c1a480c402021000490f91311081c0d03030160380c060244c0a2034100c40b0718255008034003030a413030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 986487185 1250 986485935 986485967
    0x901210203060903030901181e060f1e1b0905130204030c2903060f0108100b1c0b04091e23030a1202130b0c0102250c080a031706040603080a 62
    0x205000d614a03042018010030169002275940e1060012010201e0740d03a8400300d0101d6400d55140c0003840c035101c0d80e02c03c00d1751200719250f2541910606415078401c8409400d0307540d411401c010040c215095016442030182c070000c0e074250100a107411354200113801903402c01406284803c4001c214a01580410380f03900d00410080440b100d00207103540001c3c44103891264001c1c1c07003900d0b403541550081c84a0303500612041520140c0c666154440346054000c01c0c0444580806070000004001c01c2e13000e200c00300f450803075041103081d00341d90707400b131010f01e010000780c80c00c0e030000c40c0402c14440459000c0c0300032294007140c0c0009028907136286489034450f402d4540030405250b50358813400d0203842a60070242d1104583c001e002e0524080d01c00641140c0c404805a40d000c105400150000c1d00e0704840070030b07c249041c0e000080602c0e1005a240c01a0008503541e444000c4100100341e10000d4105820041d900800460300c40c0404175003d02003c0d000944001c030b0001c2d003084142d80c040d0210381ca00020f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 986488435 1250 986487185 986487191
    0x1401050c090d170f031e0609071202070f06060605071401020406020303043504090c1e120b0d030338011b141b030a0c050f010c14030918060901210203060903030901 72
    0x7d07400c03c0124600c0182c4294002500340d00310401c7d2500705500400c01c06020700500c0d5a4180c0654072403042e540982c010400041c0701141040801540060741c041c11007220f402507041c2818640c00941c0ca0000402c00f510312040b440c006200960750040c00c1002d5100d851b0384040c00c0e60607003084041030388207200b1900e4062801c502003a074203108402c08200134000c401d44d100b0f015014181101c0d4903940b40280c400301a501d41d50b46505940744c1c6c0c2d125400f00c1c880d8030089114091520018903640620300110f0034480500b07810300c031481e0042e10003600c851003403c10b030f0025400c020740200307500000c100003403a5504074a4841104600010b00b0311300f40700107070800c4a68009050a05480f102000030040c00280360400c140480d02e4003403002180d20070107241184102c062a21500500c411508050f407003600006020022800c0000000740390041300715107a01c03582044000300b501988144140c24024103044443c0002040300085040c40c00c1c1c00801f00c1c1d0a90a044907050340b81d600c10344a10781e096107 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 986489685 1250 986488435 986488441
    0x906090f142a04091e0902090613140f040302011808040603090f060518060709050108010b0d0219170c07020607020d1113020d0501051c0323071401050c090d170f031e 73
    0x103410f02070320182c19400743c400365240c1c0700d0805218001e24ad41d207a6130000c035110b80b400510036807200b040510940d02c17200700034071904003030401900f15194600070000320744816440f40003148a160845080740d403185000240c1c05240d0509441e40c4580c002c0007400305042906104454000c191004d901035410802e517007242e1100801031b80ca004840c41050f0200d07020400405c504002c03030010303003040400c02c1c601501d0020691003182d82080e96428003004a205443d1406144031b41102d519481104036064a04e0322100b500011000c0c010b108000344112102d60f094400c02900007078201030401c001d403800310440e00c1207094102070b4215103410b07451640f400000090364070b000c404841d000a4510070807078101d0010345084900c018034803489114203200310310102c1c0d02a420f00040001500680c0d1000540035400c91050030b64802500600b14501c0900030704465945845070b6036880c2d680722403811683c521040c41c1e00448c3c02010300c0140650300c08820044400c0004006501a041a0303d01c803206503 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 986490935 1250 986489685 986489741
    0x1011150402130c0804061407020a06050901060f0807090507020610180b032d0102090114030714041502010e010c090902220b041712090d1b0906090f142a0409 69
    0x2d08111208c20060f4044452100412520313403085030030960030710000c00c1080d191040e14070603245644c40b030300c51076001000400103125140b1405810401c03030f02c050070f56418006040c000c10502030240d62000c082c0501091048011fa078010000900058291082c640c1080ea814405a0101444250550b5070302000c0b443d0243c10301c01c035805094161206080504100324650494000800150900140580c2000001c00e048050402480441d0355480b000340a40030007820740e00a4040c8010320b170b0501484040b03c940005100040d241d2400005844524201101e400e01c010f50b142452804448900070540b443e05070020400e881009507156040d92404060b540e460300400002001e0601c1402518000e00d01880c648140c540910003c4a10b8145040c0c1502d403100c0300c0d070080d010366a0b074810030030003801d03035000d052607c44d2040800c000074400051140007002008202c241c0003807101c0c42c2c0b150042201c034003c00302072084805e40c0f82c460f61154218802000d2984459004465503540300c4904 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 986492185 1250 986490935 986490971
    0xc0301050a06090e0f06060705010e0a020f04090201230f130312020303040c05060306061c0501210b0414211c0b06070201030509120a0903021011150402130c080406 72
    0x8500840c40e0358483d0b07968400f003000ca460082c0ca071b0755005504001000104109019042c40e02250070050108001944100f201c1209000d12450289061100210243c1e801c030501ea80042072003800007220001c081302290300380c841d40c08441030000011920001c8400c69100c0101628842d88030f0080201034100180c0e81d0b400201d500902010b03840d142402a824610007540e003080e030203802e85017018155070b03400300d0416003085004d91146d035031001080b0300d20368884803c0b0819003032005240d20840302d4942c41a192030051000c0d102e0018103981580d13048040182d511448840c42c4000381d800d0b45010201c006601c000140f04075801c0c591500c2000781c0d658802da0700d110700c00400461405079254015005880020031400301c0b405541601940075a420009140b1046281d1f11490307400e085204200c0da80d00d0700c98815040102041c001c007250030300000d0312010005c40d128401c1840d030311072001641c101400800380ba50181072295003000d841c0c0080b400d0f4000c41c802c0b8400c0c41074540c45410721280e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 986493435 1250 986492185 986492189
    0xc12190206131106120f100b0f16050c030a050706020c040515041a09010b040f08010b0d030c05030f0a0e0f040908090d0c081203090f010612020907170c0301050a0609 73
    0x1800301c002c03a41d80c00045411070000b610140242806042459031030013100740c00b004840102e01c44c02c0720700c1001140d02102c90340201514034455a05e04004146c13000c40324500504426510403035040340102c01340a02009050318030b00c00141283d013190000d142c4180c841d00703588540805442030710400070300c0785007a0040e40d00c188031201c000c80361402c480041001034034810103048548525a120f00746981c481d0120b842c0600081d001c420741d43c900e00900620380c4070950b840f102c00f50749811209003007a036584035485106a01440c1001701a10981810780c00c42c45500150388400c0ea00160003c10180c10002c03448200c2022625035005049080c10310040d170321581402040320341d0400046401d80b400103400d0340024010341404010ba034030341c41142d1410701088480d25401c2c50100c104010200e0401620605012500c024400207207003441c2c0125120342000b009100d0031090000030300461240e02c1c441d46048000a441c00e06040c266140c0310150701c203000e030354000c060829000c50094066100030b41 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 986494685 1250 986493435 986493451
    0xc130606080c0304030315091e0605060706020306060f03040b01090e0d0c15061802071112030304060b01030e0105040b160504080304050d051509070e0105040908030f0c0c12190206 79
    0x80307982d070780002c01d60080d07000400803414540c0e1038100d2402c240305002c1200c040c103454040090039081e00d2a8469580a018401d454041d040020622603500d40c5010750b484254010300c096101c1e114140018128040c030222000c0380c01010003004280940300c1c950320b0490300286001c000444c8002899502c903c08100c100c004034982d104072070006040303100b000d00c030700100000010f40d40d61125804d44909440f500da110034181c012510b203041c05403142518002c088200e03540b41d400c6081da41d14a4427404020400b42100340d4401a07851240d0080d04600056100c06001b001645040e203440c20846a0907074140240035481c08818442c1b6014070125401c0d02c3c0f21a00075810246800100310406002c000c8c11200d502904e20902112403050040a004a2004000d440c0c207904100041c882d000c2d0590280d40305a04021294010541a0f412242c10803540c0104144a68030716100640c0380c41407264465647c8903840d03010719864603200261080056106917003c021007200d20803a940c20045d65168 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 986495935 1250 986494685 986494697
    0x1140303120a150f080606060405030d120b090c0304031103090f0d020f0a0608071413030f0c05150706051003020a1e150509010f11100b0604090e0c130606 68
    0x403076007400009195512140c00b180116107080a8401552048065405100e214035010700610200700140300244c0d00c03032001d8440500b090320b00350011307079182c08030b190324800e1005a032000c001c00c90044e0003a84441d003000d07003090104d0402c110750103025401101c082d40043d00303090700402588808400c941071604002c095181d0040315400b00321403541002c0381240d100d0840d41090403e91144802d000c010b1009032503c081510306000043e201d8403014845000750042081605056a00f45203010280c0b42c00c41c0b4642022021303803031300c91440c201a0300f050303500c1006086800c4110400400030710403135214802c20704c402e8a0750780307800302c2c00344c0c86001c0203500c00300c24a0140200f0b41c0301c6401c40981100c0000500300c1540d0307100005a0800384040600000e00006011225540c20203a5103d1550040c605000c4000151030704580355101c50320021a025180c080485c029a10f000580b400340c00401d4040043c0d4200e8082583c1d50b6a02400c594018251203012400c040c010748070300d82c2110880d460700 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 986497185 1250 986495935 986495947
    0x140102150c0319060503010f1b020601050a0312020f120d06050a030506040f05031b06010303090501170708071103031f0815070509011b0506040b0912071b030b040b0f01140303 77
    0x200f1242000101c07440034280c0d00c003030000f0251303024042d01c22885407034035000801640001b85030f018548040c011009550000340100070a880d5046820b04403500500381d105545031000e4102e0030700410140301c000c68403881258a010241010080248101500c01000459982c900340583c801c600d201c06000ca8212a0020700070030b2501c09e00881c034521401c00d0781d03d403802204889050303143c0b058000b2103030f500c804018010503802840100103410242002c56003690011402c02141d58000d10359802c12096001140142e80608548801c6401c0d1200b034035100e141a0440002c6804501c4254148a003074060000b09400040f030000240d00c3c1c00c45650000f9035030030314140c034641d0018a00f181007040110310001780e003440d001010f07400782c46139016107010306003070801c03031b441d800c01500031915a0030541c180f0745044e010703070222403c4541c040381031401400ca81c0716070742007005598400b40c0f008030320000f04020050b510820f20701c50700740c184805501d40d0300e650b030403003c21f03003a89030054040d8010800 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 986498435 1250 986497185 986497201
    0x6030213020c0a1505090c0d02101103090d03120501140105031f030209090105190203240409080412032c19090c050702010e032d0f0106140102150c03 66
    0x911100304001c00300c2d00c0d03514040d500d56030045a4098a84c43c1c459980c4e0078005212814801c0c0e1540a0342240c082080107242d40004408280d0441c0d41414001d2071030b02440c1e420300170b2040d90310030040108228911813484c01d004d070666000074170014080e45400008101d81000c001c500508040c1a500d181c01c541c0d41d5824240e042d03400c40c04641e01820151400001a0360340044544145100b07000401c640c02c0101c00c02c4c0703420f10044d03210090740c0c6c010300822440c020256006540d0010280148200e8000c54021070000c0c000341e580034001820005002c100c4010314200e644140b8482e503580c0115001103080055003e0f2400601c82c11080842d6004542d450702d580e5081410311081c1c2401e6aa81c0c0e00e58a050466035442c0c40b100100e00d0101c1c0d908195030b00f00c0c80c5080b0000c416405801d0aa0f48441e05200151781c0c50440c15040920559018190808000d512000c07040003000b08440c1c1c1d01e40410381516099041554014031501910104441e0310031900c9024044043c00d0394290340364064 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 986499685 1250 986498435 986498437
    0x403080a0302040b040b0d0b010908120d0f061e0b0c060703020307120507030b01120b15070f05010903050403060e1f0218030a1a1305150a06032a0501030603021302 72
    0xc400350401d07400b80302c0450034240c80401000100b840b954010307900e405c0080c0a0742952603920101c3d05000c0d00a070200210080414100046c110341307503a055031400b0802e2090003c080b009081c3d0b00c800e203002c01c00700d0314000380da0101d000d00d4002480d0b624038a42e621080c401170701c1001a4611560422804a5212400f030b4010b141c000b0314a040c03c0c03e0f00c2468041c1e200444108880d041d0000b80c441e071035007809581044240001c055601da00780458503692000c6200e00020300000c440d0003c00103881c60a101221f009015100d41c048024807116040303041c000d0072900103006c180ca5892510f0340f603610304000061010040c40b05c20a1440680614001203c000d41285620060401007408907565580c3c0520041d42d0b0148645501c50309550001407815001400505c10200c80c1100b040c0440440c10004000000740d0300c45020200d0f07541e402c04158003400e401e40c402800951b402e215008107207001c5101c401c1d1907044c801c1c0200030f80c1e0b0b144011801e807800e510019400000c1c180300d40b078190032150 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 986500935 1250 986499685 986499697
    0xa08060c121e090d1202090d17070209090a0318030210211518090b190f0c0309020301050f15010c050102041e1502070617130503030a0e010b090408040308 68
    0x1000051078a0741c042d0000c0000e4812586210070f5008a0000c0c0e00d000d800a8030810300ca0040300e0118107086060011840407200e00d00b001d00b22861441c0058001904d0400b1102c20560140c80c8000c0340c1400503029a0b1000003181c21400304d40b41620712001c40c41810100300490790020140ea5042040f40c0095409031030786107810700d03402d45240c2e60b400c41c42001d0148030125030400381c080d4080d03850070992101929092240c14001410407605001050030242d045821451164030602c80c8885086020000c14522911070062418108003600c0150180e1065802074020b0700248102d5075443e40383c0754084c0341114801540d40d049601000c81d9445030fa00700c1030321803003400014a0309031109114100c0102c4409944020802450181710005c01d010076520480c0150006124007030414601601395500c0040c895000502c40000505141c03900000700e0200303801c0000d4179981d04142030034070081d1200741c191400c1c542c2010000542403c02c5901076215a4121800c42d05140c11a0764282c8180e0243e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 986502185 1250 986500935 986500951
    0xd051b03150f100c0c0b190f09030c09051f0503120708040504090b040510020a050414010e090708060307081b010807170106020105070f23130b0309010204050a08060c12 74
    0x9909070800c1d1149900700038a03200e661658800c4103550710f01701003100300c543c00c4160300c040180302c0111121003101380c04000d8a0541005074040522036400c45801c0300740e500213003554541110014007030382c1d04c1d48090700411400741c8000c0061540b00342d11654040d6445054ac2580c01681001000d20131203000d040c0d0180704107803540c40c040e80c03000058240c5041c8281618404041014401003240070840703410034000411003541401d80880c4090120300451142a091141481201c0c1240c1c0c41244075100703101c001082c50b800d9051034400180b015000319080c0b4002e110b00764000c9400680010840000d0400102800d0b2a0501c41c00440760b080002e8001410301000c5014080c148100c0341c5594084c111980c00012186046000100710301c800d8500740c0127000c04031120380515030600e202192030000042c5031a0740e40c1422100303e0400512907000f0f8200c0c200100921010908c1900104200c46d421a401c1160507103440007251135400564500b91522000c0104d2031004111001c1c540e402044 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 986503435 1250 986502185 986502199
    0x41a0c160b060f06070b0601111c050304022701050f060f1c06080d0c02030618100c020c030709020c01050f1e0402010509040207030e010f1112030903040314030d051b0315 75
    0xc2c3e200401d031a90041d0400b110110955002c1100d10b50b40182c18850282c0388000500910381206c01c0315106070311802015041100020000d03066454458046010800a2900c800d0071a04082e60b24680c00007030040a12400e0f16140780f04a80c5890416100294402465685040503440d80c900710891848480c00106031600d000050803603007803000312020812511210f40c0c6804c2c5204150400c1e07002400f4000341000c158484450304000118041001c1142d5000104825280403c3e8a81180c101d03103c0c4d494400c0800101c0c8001068002d0800c5001410007841992500c803000b44c01444201d90340501c522807c10b103261120014440940c00c140103040a0303280150030400b0809917800b5020503004109840300230a00c1c1c2d64401800c0d01d500c001c45c5446e41041400d41c000640312131b858102d1024881d00480426140c5400b882104c006580c0b24200170075002141c00c81d95225044054605207040c901000101e03035800f48012455201140c401e081d2a695810004800c40c480762450a50001c817 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 986504685 1250 986503435 986503459
    0x106020729030403360b1612050a030617030a0f090e042d030203180301150e04120806060d0c170a060918020609101403041a0c160b06 59
    0x100304008500450081c1d644910380e091841240003038191440117074203107103c1040e1091001140074005d0050716200d041039a070740e0000e1076610384850748004018143c0852001c1c03040f00c0e160003a009010304c103015103003070050641c1d800115403030035030441440e50207400270800d121100c0e1285c7d46416000d492402c0c140c8505803640608005148201e80071940546144000b00b0a080803103d040403c408409c85804900ba4541d0000d449006070070441c8505081d81171242c40c0d0340d4084d00441c0a21000740d2034080d030682d075990710581503001501d0948a0000c0c2100405c0d80700e100340c0c1d02501c14403014109070b2500b81e551510708000c14441121104010006080350501d10701d8000f2140144400341300400d2450078801140100c42d0502414020b003890b40d002100180c0b41d40098529121084542c2d09200600b1242038820340010000520000400001c12080000f1003c080728119659000d00059945103840d0700d071148070b50318142903280643c141160010300c484400c03560140c0c1c040d100280c466 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 986505935 1250 986504685 986504759
    0x23060112050901230702070504020d061d07110a0b0f101502010905060a0b18060103060329070507081e160503120c21041b0618060801060207 62
    0xd40c241c40c0708a00e6510b892100309003130004001c400c424100c1e038002c580c4a00741000041d50750307203040c42258000c0d03070041400070012403141c0c400c50003810190381000b001040e800c4101240d440c03ca51072808111044003900c861000018880455540012410031680f00c400c1440a2140010169240f81441e01c0d0302045045030140c11814511854001007030300515441c0c0282801c02c0100301003a0a458081c20090b940c0e0f5045e0005485036000380d00ca0296106c1100490160411760005013022524007550391151145590504249048a00c2d4205640b00c611085a6034401d5807405014803006200c4402c40c40c0c1180c40e800c581c0c40352110920300e065191150711504580c00041505c0c107402c017007607022084081081e0340764024081c8503681c0c40d02038405074041c2051500c510171420f004240c80014204410801001540d041c502c04c0d07100110781e1504000c0248030000c041e0f007815a02c2890004155008a2845050368240c0d00500007042c10400b880940170310004c0c024402081030317240021b000c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 986507185 1250 986505935 986505941
    0x1d0a020309070323060f07050d0e011503140706032c011b03021e040302010f080717040804080c01020610090b15030403050a2a030e04020c0106060906020c010323060112 74
    0x200d41c001c0688100602d0045158140710380200a5111801b00c001006801d60340f02045034a1114a5440000d14410b000711060040c401b000c506003112815103004414001a04100140740e5020740803242c0e41611500c0850555041ca00d081d004100d0303280071407988529000e5400398460621000285410220040540c41c10902290070701095001600d2100b040c042110b5044c840344407600503181c2469680001d0140281c1582003042198030008503990300d11603502001c1003c08284030440606050a0a61a0341c0c0705101d00c45a0b8030410071f10240c1c55001090242c401c1d00c551405902440c500410030b400b0b04400011640d100c40c00074210361580c15020091401640682e64158031400c52500240c0140b403045100940c450403042c14121801c41401c4c2c4e8050540d25160244a00d540c600104010780282e01c42c40302c881d400d00d200810342c1640301c00304d80b0442e96650f0866482a40d058010b404580543c0c2c260078486008081300d9004100c0514000d4108034189442955024907081000071 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 986508435 1250 986507185 986507213
    0x1b01090606091b0201050f0406380f033405040509060a05060a150e15070506070311040b090d0809060301061e080f0f060112020d050109061d0a0203090703 68
    0x10b80b5911a501d5404004100c0d8a40b0b645200780000c00131400c00d060720748549000180b00501d07041c0ca0703c004074040f92291070800c1611080c820308a00c034010aa40202020080d00a00c0c3c1c041c07518062000b030740d4580043d0344070000300c0c424001c1041000b0341510741d841d140140e00d51804003084000004a54580c1d101c0e5a00c26121030000c2c00c0c0e607003043c2c05504282c8401911542c07256000c03038800d2150040740c048007102d00c1d41c0f07814540419422500850b00d51020428101465a80404c8100512101040940c0314850030360301000703810708103c14a20540118004c1c81e018100601c102d0b015410311081203042d407405100c105d13040002c0313540090b400d640240c1014000444008180c04407444002100a01c0356190504808528100034055500d9400520b40c1c030038039013004003092899008202d070f800040404203055603689001c1c074241c000740c00203200e0318031300c0c80c5000b00020f000414003601d00100050a543e407941c43d1038114140307001c2e41015004805c4c50140703c0c40040050b03880c0b241384079 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 986509685 1250 986508435 986508449
    0x6070803010302040c030204060203030f070e0a0b0d0c0206010b04090203130804030c080c1c03030b22060509100807030b04140d090312080114061605060c090a080f031b01090606 78
    0x5034a41c1184144400d139200702e60301c0c000313144c0103000034441d10b0b401109980d0b1124103003901c010315030381c0c10b601100c5034109051800e8101307c200101103985d182c10030052170110380c452410b00990f500182c04a0351034800344120783d0342e03030002d003c1840850070b1a002150070140300c285404400c02c0743c0c0c60b50701041c2e00c00c1c1c2c01281c50300d600c49820407035400c1c2440341941d604811220150300358851a082401170300307c1c0380b00904056480c00c07a00199901d50340b062014500312114041d10f43e080149420044ca841c1c0101c038030542055000070300c2c001604490f803007668480000751400500d50b81c0e9280d00c0000141c800c480c61029040120304154040105504005055513400fa8035844e50510003030b80c01c4414961010800c0840060203414940e03010112111010f564442d074501340600d903400c03d800c5401c001000b83c094101444540d00300303040900403070042150104455980d8251031503480c1c048000410035a00140300c0098a020b491070000e03a0080c2040000c02d01c6a020380d02c1c042101c0442e00304e11 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 986510791 1106 986509685 986509687
    0x209040203031b070f050a150503070207031208061e090c0f0706020706051005030d23220e0903160f1109010f03020103050f060d060902010e060708 65
    0x15200301c80c3c0c010340380d0000304240b00460b00c4601c644115200010203007804909850140074000480e403803000b54000700380c100f12096400303400060088056010700000040451440120f900c4400416500d21030140f90000400003c0c2c001c402c640e8602c101294841030f40c586401403c0703600a4a45481c40b0788031007510140305ea151094000041049002055100401100350000c0e4010310400c240c2a14581e210030500d0b5030f41080762081000240d0094603144030b14407038201e00c88000245c40b206443d00003540240c2071504100c030103041700d0f00b5402208000d400103031985c498110100780061813800000c0e8400b44001000c88101405131140f03411031204200c8900949690309401500d82e02466945424948901d40c0600c03042e80420b04080c0002c00c0310000d015514840d0500400100c00130700c058071054010490500101c0c1031101e0000522281c0e60354502804010b4451303007810b = true := by decide +kernel

theorem cover : BRFrame.Cov 986330935 986510791 := by
  have h0 := BRFrame.cov_init 986330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 986330935 ≤ n) (h2 : n < 986510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
