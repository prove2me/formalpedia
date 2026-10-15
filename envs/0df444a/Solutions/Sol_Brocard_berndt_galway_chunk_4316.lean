-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4316
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:13:42.485358+00:00
-- url     : https://prove2.me/submissions/36760119-e3f0-4a94-bc86-f4c961bd4736

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 776079136 ≤ n < 776258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 776080386 1250 776079136 776079163
    0x8190605280b030c041b08090f070e1603050103030906050d0212090a11030c03191515140a030308040b070c02040c020c01030e07150f1806030509100b060901050d0902060a030b0102 79
    0x6d10301c1c6154450750410a00c521040c0358244414640c0701c00c14450b0612018200800c000e1107940303030000d1503888040300c0134000d00c206c0203001c48420f110f000032002d95500340005804150401d0040001501c03600081072101807c0e0703801820000e440b211150b0a07a402e41d24088140c0c00520a10305110344540310030740540044004108000407a804aa124940d0010403100110700e812101d0602000400401328402401c10400c80540c200c02c000c82d2a003164000c141d01003058110080350790429001e04c0040d0f83e05074031804240d41c2c0e181c0e902610480001d00c40f50410000703007a0400141c0f00e40c003d580c0c42d12039030340140502503d0480010f003220001001d40103558040581085107440c1806031818030440341ca06000c00022060040e039681780356440394044007031240c10004400307605a1103203002e031009070151645017250481400c180c4102400c9164031800810440c18158003c1004000e2030614a00116212005800040072900f0010707404011903107810b9140b626690502140100150 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 776081636 1250 776080386 776080391
    0x111305060906100e0901060f0801140d0206070305390a0f0f050724030c0203071110020a0605130201020d0513140604170c0a08190605280b030c04 64
    0xc04000048440d40c0251000d03006075801401c0c28105841140d1050900ca030190400b40b503942c2d034241c01041e8400701d0540200141281d800400c0100d0000c0040880550042040c0040081602000040e60124208605014040040d040b6080c3c0b0b0355850100747d14140081000c10b500032007035044c42030820450b0501d642004001c02c0005040301030107880140c0182c21010702c41e800f894102e1900320380c8c1c4c0000040040c00707034080d10706640840c01c02200110654080c08248a10325050380e80c2c1c0146d441c000e00500d004001c4880504180b02d0714103c0f40030503c12210740400300c0e210042151020341f080040c9144480c030071000d55804001c940035001c2070f131030028541035040580754107202c200d0280024079203100d40d10b5440c554440058a0140c91441400c064480b50000c200341d4403d4400344c1c0b203000e0000c01c0e1001030120808541900d403c1780558070b03240f8101d103d83d1140c004090080c00d00d5201071884200d00074500c10340d5061840454840b1001411a00d81403c01d840c1c865801e140c0c6100b0350 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 776082886 1250 776081636 776081641
    0xc0306031b03200d0b0a0504020f040c020a0308071422050a0605031f09020c160b0f1b010207050f1015050a0302100233090105010b03010b07030c06020403111305 71
    0x2400034812111010300d0b044950002c81c840d41c0084c2500718071820140502d107102041c44401c0c1056808280180d00c00c0701e010a000c0c000d00144016200c002c5036150150f0071590302d5001180c0940c84480e8402c40c1c524208009047e000b0030509a900500003400a46008030300c00c995040b002d800c414080c180c11100820481c1c90008018400c2c44001c0c1001c02c0b1010304401481800030000c181e001519000d030040d521169003142103666400d030300b10362048814601000203000d1494030704443c0749881c0b1080036031a10203095210301c41042c40c0002da640030340d403c101c0b1030045001030115098025009001d00001440380d5600e900b5200014070f12040043e40160030400c0355140c41e205400c40303905480854000204400503030074061758030184800c04400c000031100c0401c2c3c0c208031011500e018024021141c031a8860700382250b03070034000c0b5554543d0030001071040369036590251036258442c2c81c001000509641d1a1003c1c1e800c2030b401201e994449a980802a1506007241e03145003004400402152 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 776084136 1250 776082886 776082893
    0x301110a200a03140708161203110f0903070506030f01080d0f1b0206160b0106022b0e1302070602030f0105030c0a05010e01140403050c0405180d14040305010c0306031b03 75
    0x400020b01e00800740b100e5030000540c007060b002c3c140d07404207800c1035055465001c0340082466840321884101c0b0a481c0680c9030f58400d60180c0b0a4030418001e252149050068100e00445154400904103a0512946800150558031640114071071000c54020002030b52420705010319100541c000301091101544088802e154030020f48200184030030f001449a005e280041070390343c8100b001c10b0030b040f1808071441f42840401d85c9001e0484038964203ca0545240412000030040818103807854810441003012032a4410402c1c50710045005140805102143c80b41e5002caa21502e822640650080100086105041a0b0030700600c07082d0047c0c01c00408482c000f40381e050b0a805164180312580c014404103920a5004210307040100040540c1c8a84034182030340d803007440c03640b800e100354180000940070301401200c1c229480c42e0140108400070040e603082d10300030b020700e2041d084400c0078000080880d03c2402441c281015940b030024600f4110b04101c00c160840ca840c08e041d0140401082000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 776085386 1250 776084136 776084143
    0x1020d0f06060815090403050405090702010e0d03060f09020c01180c050406120803160e0d0b040204060501030b0d08090d0c1e0f08031204080f03090304211a060f0301110a20 76
    0x21000211030311784090351186000e4415006542010f50801c3e5408208a11745405501100d1851802801c4411a05250000718156503850080e41d036042091082001103155540150854800310800415030900180ea1070806000321002039400e401d0302542002241040d00c07550b0041c1c0000030b01449006092303282c00c80580700c081c10302240c4080d40362051507001e1090b00d4071014624001c01e103100800d81400c001c41c2d4030100b624240d114901c1d250f0000b40c5903010344a10140d030840a41110000c682c592641d0110b9004100313880c0d00000c186407400005000c006803d0090001c200107001d0740e00c0c101075540d41203045500b00e1050340d0b00c4c1c01c0d0b00303008012002080c0c0d142c0400100c01070101e0381d200d10b0400744900038100721044802c2c0c0071044c402c4e4003102001800503106030300114014407045001010780003104040282002500d090500640500c01c0311a1307500000140800c002c0c0c500200200e82120400e043c4c1c0c81d003250002c01d5074030f90a940300990714802074040b039200743c0e28074003080302d581c9 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 776086636 1250 776085386 776085421
    0x1f06050604300b0702030d180c0e0a180812090d020325050a030509131e02070303140f06040f02070b0f1f060f110604240b0301020d0f060608 62
    0x4110110350703460409507003810303540c000850740f004040100b820704007400b81d6650481b0403002221030a084124080d00b109141c40d5060a0f042814219440e01c0d02444c14060400a442400c070795413509094950000041f8461083c144148102642c50b0040c08960038100006091340da42a0000d80500c004140c1c000150b0305801c1003410889007921039524034402440c40c000c1d00411328040d11252000f03140e003250192540c00020f0b06e0700c0e003000700707000c10300c8040300d0589400d0500105290a805480351043d8060139065202c2c5c1000170300c0c032148600384891002c08586122800d04450204292810a4001c10240700e0349002c056040844036035074004401c1c2c0080540510170860400280204026103030404121818054002c026840d039100a001d40f002a440d00f01099418140d10140c10000940511a83d0031040f00c9030034442d0601c0c8659244a80300011441c40d0721224900e170345540a20003054220000380340019007903c0440003005460305503200342c060203803d804204d10900007194a00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 776087886 1250 776086636 776086679
    0x40f02120615061308010f0606022b050d2408010b010c1a070e06070606030b0c0c0c12031312020f0f01020d0f032c2a04110c1f06050604 60
    0x182c0356464054444450146940105c4056084c1549000b146240754081c1c0255030301d5500b1b0380c000340c45103100c284c001301d600311480c0e0755005540760381459144602c0180485248291010852280c4c01010110618404c0c254280250710070713078200301a201c240f00300140380c1c1081c00c00784498405504c40c0304204003100c003404a090700000000b86820b1003400d54070103041000308560b8648546050200c001c006500003100c4000c03100010610100c010070644460000120061844510100620401000040007880c0c6803100748010284a901c82c0300c1071001e030a101c92070b880c0d5440030340100103082c4e10114216008002d0703011501c1c13869a02144074800a4680d082c949414140250304400038583c007142c01c02200382017003950070080282800421030400d424203c62019800318107810f00e404900d41200ea8441c5070303110003e81c90900350000e104070449188980d040c040031003641c9040540600d0303020544414800f82105018191041c5030280006840060905007003042052400c5110600c10 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 776089136 1250 776087886 776087899
    0x3090d09120308040c030b0108030a02060c0f190c020405091b2e0c05030f090108070806100e030708070b190903020a09091401060b0a0f03090807022106040f02120615 73
    0x3e0280700e9804e220740700841d80407405850b03030740c0c2d2740302c00544a40218520300d00500550001c10072009480c8151140f01c403010003428070b8011845281d640d944054003410084c0400045000301581da9489524440d0040402403c61301c50007002e0001c0d0614a0b01d00f4038450420103007034214110741c10348401c11203040c0308400100e4010107501aa0515194500240188230009040007604c203034070b000d008c0e582c0d420789602c6d005482d200c07401c0d108500115821038020001c0d800c2c0c20700c0984030f1143c2c5c1c0c2c9841c8014003a0380089031910015810101d02c2d40040f18803081c0040c079040c802080401d5106d0794402484c100f5007150130340d0700190024406224a4200541ba42e64042c180000c050441528100c103c0080102960340c200001d640c0c0c011202100202da5450001640c0a00038007501054640c0148080c0c60400c3d95401c01000f5041c0c2c00d10200c982e81c100b50400003c2004100d80760040f4010920820005180d1041140018901400c0f14550b000078040c07080c40c00f43c5e40c1d030080400f4001c40b400d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 776090386 1250 776089136 776089141
    0x709051c0f03111002040303050405040c1b06331a030108070501050d02040e0a0501090b0406080312090a0f0c03050616020307060b030f0a0b01031502090904030509210303090d09120308 81
    0x10f81d1030200040a9503451a100250010805401c00001c2003101e105840501226007402c0080e111940c0c4044500407044030246100b000500c10742c4070010080f0204807040045080820351a00800401031004c0143c0c3c0600003400390080c0e540034444a00701c0703992614595070404803010303101c141e14401c0b07a06001012900016454840c0c0559029207440520903010303240168000010700710070f00c1003e80003880c2c0703003038001070741040d010341d90030380703210000030740c948030380c5402004414800401703c0f01d03a402074a500400140260b440f01c4042806000042841800c500304141040780107019283e41c540b01c541e0308100c164000c01603841068000304002180050100401e050050a88402c0c0380707409124290010000d103100c009060340e000d00d05100f541c001240c3c04900300d01c01c402c05107a01000e92000036000034494002400144030140103060080014115503520f100382028079010703900040100040ca81081000143c121954505200050f20b446030b21540052540c50140811619100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 776091636 1250 776090386 776090417
    0x1504050910090c0e0720031908060f0a06120506030c1e041e09110303120105060f040b071a0609060609130e1006051008060a1502150709051c0f03 64
    0x30b00e400104500c04030020140780c101c0000f8055a0b46c03d00c0d0380450441c18038142c200c280c000080d6518024800380f20400d0100e00007098a642d80010304135980b0543d841280d8100b6160200c0c10340040215440307690315642c0c0c454400c8240c80c4018192402684404521405951048212003600c10b0201c10050402540070124010f448810540d07081403070b4248401300c8580f9641e00803c03180d4014040014664050020181c8038452400b45049001d424130050006280080c000c02089410244082c43d042d43c44190b9802c503003048809039019000d40c0d02e00c00d02d048060423100c1c0d00c49011a500035843c0307402c9001072640e00500004a004d0b0f030394408914080c00c46580042400d079500f8044804402c2510442d0b005028030b40140350064441200c041c00b194010b0f1390f0f40d401110002e0a0a0800e401e1805842020f00019150b078218401c42c6c103900e0480080d1a0001c3c040c0d6010781c0c0f0f240800c0d041405000303061000580f5220750b440300040080c04280512040859507078113140600a8144a91 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 776092886 1250 776091636 776091653
    0xa0e0105070c0608100f03211b060b090a052e09111e0408190623010515041a0706060302061215010503040f1b0b040e150405091009 58
    0x42008098410b5a1008189580c10112841c480c240f8684014451a102c840c503080b44083e03403000814448421058048400a0100c1000ba21055151401d1130390b140100304000c808000405035103d41e40c0e003074002e4050030040c500c5a4401c0c070010051005083c1041d1030344400302001d00202030302ca01c04000b2722010f1001051180107005404050054025544440d43c840c4c1c0403950102c03204da412050801ea400801040d10100c41065001d8861074481c000161180c07021500c0403100c8580d9103441050451032400b0181000c075480080101c40e604000c01e01a61103001c03500411194428041041007140000d4140c0c0c4002072030003120b48170a032502e4048081e1491b80c10081d40f2480c041044140300c02c20f500072a10502c2100064585240c10b240191164802034a0250050341800d00390404550340000c10721080d02c1c2c6402c104080c66031850300c54641d030401e812000c04007035400b052011030103001d6140001c03000c00311800c02c92414104041540e580c0d240003416a02034483c041141402640f5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 776094136 1250 776092886 776092897
    0x37020c130209040c120f0903080c0a020111040b0903070b04150c1115030405010510050901050402070c050402040602010608060912032206150e070c03091a090a1d01060309080a0e0105 80
    0x340050111103403107940a00308040d4040100445c0f8030b4901c1c82503101240d40100d440c903035055224a060360f110302805021710380c0f00c0001d06055640360f40a0100302e01502c401480101b544007400d039200c07500b040030582081100c0c4c1c80b41002e1038050105004400e00b1501220701c4d12000d00b001405481c00d440c008010310f9000030360661201c4400c41181c550117004000354441d0b8407520080103556600010410142d140c0e004090300460900c005100c50704290b03008042c0b85000740c0200400030b40e243c00080c00d0f031f4041d400440041c0d461b91401c108600007003000c0703600200108003808588025022001c1c032804001c04868540c122005040f04201d03c241960b042c554102c40280001d074446140102d1001070392040d42501d102d01c02c00204002c0c0700d4181d201460b6410794405030050b24017030212004641241e54031005403c10052548181d5405003d6802442c16005d4505599084414010207040582c001c0e0107041c1480d2860000800000071592041014180381c90703035260740c500407101030040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 776095386 1250 776094136 776094139
    0xb150d0215120c0a0f14090306040c091d060402040c09031e2d0803060312040f0f0519050405130204021b070603092001050c0337020c130209 62
    0x1401c21001c2420a0009200d04541011010415152805052241d200b1400740e08002030701000701d00c40c071620900a9038200b00b0204070740360408400d000083d0a000c01a20121001340c00e0300820843c1c810030b40984002d080d01b000d0500b10404e1748020403a210b41006000034480e1744c1e47d0400c001c049000f580104090742e0406e100043c14820f892040411888008041e20b150194222014840782000712207107400481182d0003d42e0705143e9140b00c204d400161541c0d034103000b46040e50f038844401002820040c01c0c5400700001c124a041d100e140030005076000a400340c0001142680f400260742061803c40d002590001200d40e5082042c00d004600d8040013035100f03000141e0501064824452140b044d105882540c0c40250b50700e1050301101c0340d0880017448000c071045401e9000c0c240304201804041d040c100340b450b04001540060841c1d1050000e411800c184402030401806540c80048500c164007400744040200e03041c019555609011440340300700d0f240090300c5c44180c8280c0666459060 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 776096636 1250 776095386 776095399
    0x301291503180c0a0602193305070807080403080417070f062409110912030307030b01090b04090509010906020406020c0418020d1e08030f0f0a05040b150d02 69
    0xc1004002c8440c0010740c1c0c1240162064a10482c020b2610326040011a60590010038074031540407038100d10315186240c00d40b140c050042c81640200c40d840700a0090f90340c2c180148607a4041801c2460840748090078074003c0003000e004010595801448194000d501410613000e03d9580c0e107420401d0701c0e016140301c10100400301c0c8d030000708915513100046461048500b031207815048901700b0030030400d03584490105202c0315010040e0151642c050000c403800c641c4541e2074031490001045803e0744103c034030b1265600000801c200c02d50304d80300b8815002c4091800300751041c0741c000701c40018022030040c4a0703003da0b1000810075920003540050364490b402032040d5100e6980f0300c0081d40b1108842110340c06941803244c00b40c91500c581000700321099000b440881181070f03540b9020401c640110110381d44200070b1140c000451030b40c0000e14410316003494002410b1a02c0030b98000152005455840c24030709000038003000954900d080e5034081d141d01e1201c000d02c1c0b0307658002100004001006904038a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 776097886 1250 776096636 776096641
    0x6121b05041812170115050705030f1c0501030201050a03020a0e10020105070905030f0a110a0315091406040309052214090c014b020f0c0301291503 65
    0x40380c2c6805454075004050401c00d0003030b801400e495400c00c056540300b400c0300746001446048500260881c04070050329020f03060182c659540d91459108442e40300000c607000c2580c1d41c0100d040c1095034030f034802d100d030184480d500d13660000e0600e010b07517a140f034145500824102c40c114420710f9103046030703000280390084811500d00041d008110a036603030000148502000300300e0b814000703485401d004c05040101003c0d0020340f18208060070804081d6400514190008041400d120105a4030340c043ca00001c0d07014224a00607689108051038888140c20400401c40403c0e0066884011600261000c0b09800004103240040303002d1940b211941a01e005044046041089807240c81100b0410848581500c43c0700107417121000d1400a5032400700384c01509001e2805a000160400084418080141c11411940106e500c01d81c41c800c0c01170303000d400030600d00070081003104802501034000b04143c00c04400040310b00d0700013040da803800c02120880d032006a294112148440303103162a01030740b01d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 776099136 1250 776097886 776097911
    0x2041119120b031b0405060d0312020a0315090c1704020d02040b040e010212010306230114030c040c050a030605060405181803031003030e1e0d020a080102220906121b0504 75
    0x210080d40c02d001740c2c40d10002881c00c2c2003915040400070341640300c4030040c0091000d880065404100c40307004050b04c90341070500c42140d42d03130101c02500032418007140000d140743d001400d407101f003d60f00070354407401030520001d43c6480800d4018650141c0d000300710300c00c03450081000703068a201d40c0645584009281d066084c0c001107403505880c441c0d44240982003285010b0103206500903140b0300e41615a000400a00c1003030340500102200203030036546031003203120000341128100d901a00100d1000554001e6a5915105400161008480c0181031509100119100a0305044101a09040e10001c544100301e05ca107074440c0302a0708070469540389881c08240e13203215503e100840c0132408944100030030349032601e51220309200c40000581002800c504204503011780240a07030304141c030a0b001090051080c0018450100c4845031420328810b0349407046000c42e0b17203a0004411501e0004140500c0c40181c3d1880c0c50f194100c2c00c00d044c404c4440340140340116040d4011584249801c80f0704010 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 776100386 1250 776099136 776099173
    0x906021b0108071b150b031b091303030e10060914150411070f080405150c0c0d11030f062a1603090905090a12050c0705060a05131202041119120b03 65
    0x104209509030781e01c052402320008980080010043c0d403005802000482d8003103a941c02e000c4040c0289408200868558003003410551440204c40c0c03610344a040502034a0300d28001c0840e000d03001454000340b441c001207441c484000c0a8006449140c49110100040d2000c0081d1241d054012231090001107462a202101d503000d4800d4a01452002c02403040702442c0c4002ea41c0c0034041d0501500d07007400844204185031443c8241100c41c200c4440c80e12020b80c07010884602034900c0407005084500b0881701d8440c60700e41c280309003004254156000605d212000069070108202c158001c10144564038007640c5801c06500b0002510340b0f00010440d0741c8a00050740c1038018000d40c500c1c80c103e2050031045a0601c25008030b0600356100c000b04010606203000102610001403030810f0030000d08842214114000e980259005d04c491040c2c0002e40ca01441280d2201e10010700091402440207080d00b054112001101d06203c250001158881282d801c6030b59048401401e4480c90b5800d0750b4607514 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 776101636 1250 776100386 776100401
    0x109020c0712170d0204090c08060418021806210a1b0b03060108060103180c14040603030f05030907150302070b09010b0a210c060906021b0108071b15 66
    0x2a00e10034008000303129002d1186241d001600901014900c00c01c1580d6110140d1000c20b007440c00d203070b0801000540b858540700b41154400301d543c8034200780c2070043c10041910314954045aa2100702c20a650069944c103082c10861210766024641a0340c1e40f0001400045ca01000c0b00e0901c2600e0b000c803501301e9000301d50030205922a1407928280e0340c6504442e541c5510500554202e1241080070411a40c000c0301540c3c3d002030140b40124003044003511220104024440488400003580c0d000e00200c0300c80c8000b52140141910200050361554400034110300b0b10070380d40c0d400c3c84030020202c0c9000303e0501c0018042c10740101e001e1500030074040001e009510255094404045410100300b031884c1c10300882414410051140e41c00311700344100e038a00100c804087d4102a011025500c0004107150078000080c202c5031a0281018a4441e02904000880344620710000c075078841200f09a0700408490b400c5181450319003018620000842c1b58410b23103410240c01e000c9c06031350b20b80141c3c0168001c140d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 776102886 1250 776101636 776101657
    0xf0708010e0303010b07020d06110d1a060a0903030f11030a050d1503051b1c2102190809121b0307090203010807090908120f0f1303020d111203010902 66
    0x481001c0010301d5100e000a02540414800410414016280c2540311544460240900180906035821042030551000303818140c05034840c3d80d00100944e21a08501054030281c0d01c0d0703440c1040c0c458000b4407400d450302000302408a00603003441d0311071041150040b5040c580d4107c0e0742c0c51909080c050080e030020704554175000d0805003000280d803902e454250441e544000141426409410f01c0c426085c011003c0341e802070880503a10780100c0413109110b903410f020b500c0329800346403400004880c1203201d40750a0b0a640c801c24401e55260492100b400000b42c01600745034aa201c0d002c0021240900b20342161b005210380350000000a10300d28003103d0000c0200c0850380320955468a8405901092065101a8020082c1000010020340101d02c15030f1149418514242c40002e0f400071004042c0d0b44220086007100802041b00c4100030126000710000d1a02100d060403603900030350b518048801402040700b0b241c000440c04508100009c000340c3c130000c946840c0d40c1c4030344603c8001d420030344194 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 776104136 1250 776102886 776102891
    0xf0a08011a0a020d3b1c150207030c232a0d0206040b0c03030f0109140402010c021314250507111306090f0f2c0f0f070801 54
    0x29400c4041410440740a4041c0c3e80151040002c0c015082e1a07040d15110b8101c0c034510703032698104100e04041100005408015030195003280c104061090074210520242450f8181036941c1000c50182030220030300c1d207460301000d03944d509140344c2150342598220f4000d0051040d0b007218a5024500f6404001120703102c005c41e0881c0049401d01d0002c912180d5200e0302e000c2d011030b8081c0c1d803410500403480c0014000751244d17160665512000a095218400d603011680000c4144003594005224607401401e00311020300c4002500c1c2105401075502510003410700010921601c115101c240320b404a5030f82c100c80800008000c41554003610800721030042c0450904402d003c00704c20a143c8140c0c1229050b916541001c2980d5201425004d44271455984807403040700c0300d4400000c90203204068010540c01060151030900301c0c40030f42d003010f0070301c5d0b0b6181c0c1000700311451403190042c448420309944401002c11074842080724240407034084410214046c448040688640019001e002c82c3c0c0450000c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 776105386 1250 776104136 776104169
    0xa270f0e18011802510901120203100f0b0d0b18063c0102010b0a0303140f09060403030e190303020607051803010c1d0301061d04080f0a0801 62
    0x100c500f00d60a1a800748a50806608058007506181e0644074408610007060f1301c8041000c030308207890742c80c0488619160010b200d03c4c0b19108100c0d588180c2e20301c1c1c801005506142c80c100000e494200a00303c015005a0f000c00002d20ba001e05c3c00109005140d09401c80806a03250200b0707030000d92203890040c0304e20b0304010802080e820088000f6030345048110070003c0b15203c80b020440602078540160080004501c1c0198040308445003000c400d4060941022949078040006400d54901c107003114403400d000b07002000400d41120004c2c0a00303401c0e08107203980f600b00506203440c9004c0d80ca40e40c1d41101011401200f01501710840e1900880200da0307007480400030140381170300300040f40801030040e0441008a03081500807409040213020304071929908400200c0401c1c00c641e891440b110000d40e44803560306001e02c20042d098002181034009101c42410400c0d010b510601a0450b14201e400550014081c001c0788019984034081001c515580c0f605030200007401c946003801542500c4240004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 776106636 1250 776105386 776105431
    0x506030d17070807021002120609010617060103020d14040f0201030b030303010b0d0b01050c010e060106090b3103050303190c0809100b0a0f0303020106090f020a270f0e 74
    0x41c0265100640c0c2218003541da450b0012601440054995402e42c8150380c905103a8081d01d00280c200c2c5011003c4441151a0000c10490061010b071f000340180460b801179003c045030440000c0e64000c0d42170070056501c0c0b010702140d10040801d0100184035221000a0208018100a04100782d40c001d980601c0640d942104240c1c03039200a04c00c081030904204134a45031060103401c0b40e40000c5050400700c0c00c1051a00d111825500d107000b100f01141c00150050002c19040082e8101030090081000c0c24004050001d032202c101141c0000059200c02d2034030010030030340400b981c021f10750000030b413616404d00d81d68a044085800c2e42c0724905030b00784480c0f803c03000d2044200c103114004020040c42e00741c524074141d42c02400c162400781c3d04080d1030700020507088614966203000310312070782c00010303003501c1e0140020842c0c400f10000b040d4140104000a012136000882d45e008990050210340c44603401003068031061003590045002040180f4005031081c4030003140d92044581c0d00102006007801c01 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 776107886 1250 776106636 776106647
    0x105070e030a0f0c0f0b0702120d0f0e0a1d100504180201080405390405040f0201210c0915030522030306080319020f07050904060b010507150506030d 66
    0x104030a0301648010392a0000c82c1c0b240c01c501c2d2515001d41c1008604035183d00480c40e51030140e4016819130fa0002686d0011070034003070301354000c60503845c003d888c000780907880c01403c20f100110a002009640000c1514544e9400180001400d5509451101c01504101d0224101c030490b504d072100d40900d840045e180c142400746c845601802c60b02c00091046690041d2070f40840904241c8552194618100c1200d2844403c615408230422400e000800c560300070900460742c60107860f01540c100001d01c000110140901c0440c00c0c6d090030440740c00010500300c504441d04074000010384500f080b1514111540040300801502e642041700c610721082c1101c283c060352800d9131000075018981c0b43e0054400c001e0180c081d42d140c030a29012407c3c40c0e0300d4440500d150011210010401e80d404001d80c0004e03010001d104d440480c1c000503000c803a08c1d2800050400340c00401c080c103490b845406a0100c3e80c46070003224005a0311052071740305403c40154070300051074100c540034001e1081d440c0e00c40c0181c1c080c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 776109136 1250 776107886 776107907
    0x3030c230303010902070f0c0e0604060512060105061c0603030c150c0c11010e06030f0907061b23100c030e1902041a1507020f01030207082226010507 66
    0xd030045145920346139074080250f105020540d2440990302c4170100007142e08440e00010866000c0b00480c90400e5401c100480c0e02e60380c00144223101800c44419906000728101d411600d00300c60321520340d9880400710050050460340c24200620313286020003010381003000184018011034405544100c40d11440f021520b05440f0b400200d42c01d119041c001036001181d03c000c0c0740061605c05042c2c41c0010104140380c00540d00c0c40301c4c85002d0000c0091b00c0404008400003001c4500d40a20034001c2c08050528084030040301400f40013020b810341000310300c2e031000c2007852292902102c54501c01c2c3c150171310040006130304100000e0700300001c0b8200c031a000134000d80201490079503024603981170342c2003100074448103503801c0300328903514840c1d40c1c0c03607545000705000303428401c1566035180110300c1000003050521138040c0c18140f0602a1802007403000060b02c2d102940d4500103c0c904c05c580700d1544400c00103a005040c1e85286100b207140a0401ca42608840c0c80914020300840c0c64040c000d540c1120072 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 776110386 1250 776109136 776109203
    0x509100b0d0210030e031b010e01060b0f0c012a03060602011a061b06280504030912051509011416050720030a0b06010e040506030304090b0f0a03030c 66
    0x1050341c42000351070480c1c0000b91503451030400107080740c041e56070b0314115003091100002100d107140c00410145400c0c002c400315015800c0007089a076040500c000b4642c01013040700184400003244542901c00250300502c94520154820804a0788500b00010f0740215007980380002030801c1000510304c0e0050045103852447e031074000907109603030030a100c0301d500006c0c00555900700400d06070b01130700d10038806180203808984030034601803003105807031004402e8140b140c14501e20780820040840da0200001040c3d0300800c20a140d843c0c0681822490300c0090010315140386a840144140e1640540c0400360503041d082c8848016507415040e010381142c48a46d84d000701c1c50030803000e400601a9446401200a0542c460711080459008030386810b05125040310b0850041060013419a048030908202e010119070902c424034142c80841e23200c0c02144142c2900646410010566540300f602c0750740410f902900f2820707900d42c0c904004081c80304803078064448140661549004010006401114480 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 776111636 1250 776110386 776110399
    0x504050d050901200303072c060f1c0e07061407030302030619230f010f050306180903180603130318050303030415150e0f060a050904060509100b 64
    0x154007511154080b0000504000b0103010842c01500b0600200400d5402c2c04000d40d04ca14200d18094400103641071102a01c181d038401002000700b00100301e6040c01000d13980182c0f90814076141103403030b004030342800100a804a003466103d1030b050348241400410300c3c1c1154000e9070744040643e956207600002c50114001007203074001003402a0025500080050641d0b03020058181562126190541150854914141c0058400740011010100b2100304039214114806088000303090050410400428080301100040403030b5a00b001d1748076013081c01e01e200c0c548d9181c41c00c4450303140d501401c20440304000821110b86203041000c1603911580014040c1c41e071500803503e09580c2e200400100559100c2144404661901c050002e14011803040c408911400007420300d003800da801286c0c0000c02c03d00040410800e0782400140142c105107040a40400c680b03900d07002c07684103450364004a030800015030501c81002160780c4010b202d0030411094454203903c2603212010b888010100341da2260 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 776112886 1250 776111636 776111653
    0x1030905060a090503090d051609050c1215213306030712030f021509031209010e0f0313140901170a0c06020c03150f18030405041401090f050405 64
    0x240ba0348072201090080b400c407030601c4811400180d0750a0307031031401c40704d5030071003006104d0034079038500c107413010389692181881145002078108100340290101602e201103580040356419610001440d06407034003501c4440c1440028810200cca084c21030b85990328402e007442d141c580c0d20068a6408a0380d0703107000c000061403d0364404000d003540a014254140a8030318006802c1c2607068265458511a448444000250110283c1030060800512845c0254501009400640442140c5601c00049051955034a071101d009005081a500d002110310031100c0c00400c488001003d080a50501010000100c1d19100c01e680d0f05050000f440f03410400030360046c00243d1446c1410340710700c0c01300320032266181040d841d4078030700c03404592019016820159240741c11b42818840000175100e803006030b5246090002480c0c0940b40000c04800c842c81003010307801400c07d01032044800605000f4400d000b071550542201c0c2000900780701e1611494900742205000140754010f291045030000c01805588 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 776114136 1250 776112886 776112901
    0x81609020a210b040204140f0904151503020a06081b07051002070f02090c030118110306040c021006091d012901030b0a090f0e0a050a020f0409140604020f0103090506 73
    0x21542c0044944190302d80c50464016151440508010004118409501805c0005000f81003050b01c6085000703401d10f00410020510485180c0400c1000b41c1000038180b180c1d0320309080710441a0130080d4850f0f1031140c00038003598000800d6018240440003006034050502100d9030314420084010620b030030414101501514550190050a00441c00082e440506600040d42920200c4606071b44460120050000b099440b1030000060349900080000d0ba481c040f58414500009185c2031090380c4507140ca82c5620301c00e200c2030204404181040c080e05480d030201c50003900c0c804408661200f894055070010361014084c01c90f450702d520351090304241100b132407101100110303140e1038107154441c440c056581e25680407540c000d00d20340000140c3c040c000903080080da60100281e074a10350000085c0c802023140030039a0307080ca650441e0803800d00c08410010030051300e80c000c009080d030280180e01c40344d4401c0202e16103104510846040a650f2030354030041d411141c8082001c0c0c40b545c000070008401 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 776115386 1250 776114136 776114177
    0x2a010501050a1a0a092d09020a05251202060402010215011206050a0209060c01020414060c0d0e01021006030605060a05100e1306050d05100f09030e090a09060501081609020a 76
    0x301103191070a600b545d41c40703400c0100701180b250b40c038108400442e4100203000c41c100f60110043c001015055181948240e8002d105006031401d643c2c49800c1e1400350300506803c40c3c564420310b5800740a0f140c04414414029440340300855090340980a1806031541c68200038400a050b140040041c5808000c6030300d4143c01084004d00c1c1a82e62a400c0050300296612140038201c91700b1844000740e90385080c4cd80c0c41a2450b03501c4044e0703015003003d200307001460340301048144840380c083c900f09809540f8400101e140c6001e04074000d0120345001d030040300b070020b160080c51007154103480080c0115074410038070100d459200e01100000b80040000152481c00440c030601443d0744103c080780c000d84840018020750480f070002c03103880c0d006807030f076801c400d0aa001c3c00202c0c42c84503c1c100540300c0192130207408090450001d030711070204400052215039082c3d00a00100f030b0042002c012941e11040016590035000720182401c400380103000644042e1802200e010300700c0380d6280c2880f00201d02c40d402c00c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 776116636 1250 776115386 776115397
    0x3070b040f110909030a170411120c04051005010e1f1409090114012c1309050607080106030b06040812091201020d090201030e2d032a010501050a1a 65
    0x1d0360200600b0000300e9580f40044903018400201c09180e031110810b101602d610128030394103045400800800000c41c2d4000c40081c880c8409681c600d460707200d1150b150303040c00c0c00550b032107a200d8035003002d0000c1c403254440b5040aa0702e0030388070120726034240703010050b0a180c404c10003034011380c0b07040c084805548030705120201d81400c03040c0c2c40c0c1001031820000724001001d80107042d49440600c0344900e25a401113016110322280c0c0a03030314240c0c3c942c482900c10602d08002881c0241912300c00314001401c194020108184c128096480c0d03802e046400500d240ca084c4580c42c0081d04200b5051054036011003180d0498290500400041c0c1020664000325040002a40c0e4001c00902c4d00c001c1401086c001007001d48a9200005003070001c1c1c0c0b0026003190319200d4030701c049901c0300c22000b403280040c0480300c0303540c007072038080c41e428902c5403a003070303286106040e602c0040c1c420f03c400c80c1c0c4440d00140007a03803035241950003d0046a0703e803001c0c000000b002c2d2040e204c4103080e20150b400c002c0c820000a02 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 776117886 1250 776116636 776116643
    0x1140a0b0c03070605041a0f0f0103110d060e210f03310c03020a06080906060108180706170a0b100302030c130803070c090b21010608070e09060903070b040f 69
    0x2810030761644ca68004aa1040302c0a84031f85c00240800d80c035014243c90020b40c40503040440301c43da418821482485e4000c14000141901e8042aa0854568560a105440a50025080c404640c9080a0a4a941d00c00c4c1c00500301e40c00040300244003100340401d540c005280300382d98500f5540c03103092080910203540f0303030114400007025004805114800b4051071884c080d1224030380f094610b20611401c031050b54402001c00c40c42c0810b10114030ba0100300b03140c120400b484d1091103520f40c134113550104000d410705442c6030303c14036400041d4035800c00311940c00315007014502c00c2d543c0e65910740c0b00b0950303181415040e4420709008407038240d81d0080e40551b07040003202400c5410b0081001130301d0325200c0a41c002c034041d07904c0404c04004024605e500071018000c242400d012522078000411060052206000001c0345200d540d040d1b01602544460010800d031004c5625840d913032850304000c40810f481080d05402643c00203903000c2d00c00001c030b03800345511841d02c0b4a10f607500e44070340e10f1140c1c0c0c0c0310089 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 776119136 1250 776117886 776117893
    0xf150510081b040821090d030804031404091d03120c0714100617071a0d110a0e1903050309040203061311032a0f03042307050901140a0b0c 61
    0x700480307404038003500240c14854020080c0780d04000090102100c01a0000c0d41845c04002c070315021307195890200d03040c551600745040c0645a910302595248000d070030601c43c8010200f8006001903403504107049000c4a04a40c4001d00c00c1d80e4030950302da11504240764080d24140c2c0c0032803c03407840c04c00100340a80c040da505500301c0501c0031465080c603260486481c0d90a44503c2c0c18080c4154501046090802d44001801054500454406004004001038869440100d84047c66400700d400194850402d030010039900d031400303440a003986003502c08450041c00b4141c00c19185400c42d02a960503a41c0100003107040c60030700410400a5403004056030380044013802c1055140c0480d00807210000203206542d0b446c0d26090440301c41400e0f120441c2c88080c20400150020013030302c10111280100b041c6203a656035507880c207003401051442d004004400b1040b0400c480381c1d02c0007045040070744208607403084040e660341c01107000c041c004008076944442501c4081100c4c85100d4014900c10007a0002d0707 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 776120386 1250 776119136 776119171
    0x20c0a02030651060d15180b130b030f0313060e01020a05100c0c1b0e06041413030306030507080c0901060329010210060f210807080a170a0f15051008 66
    0x3205a03591205908000340f5003c40600041c0031111a4081e005848002048001c2035080001c02c26000128115801581d40c0c02e08180b6070bc0500c102c0c620405200211307540e81e411b0380082d8658000520a40c4c0c00264110341d04c6500d584007280030000c0700e410000605448401041c0304000b4580180e06006005104c582d03d030001d40c103405025006002001a03c0c1e202d454803003010f0045c280100704503c00d0345050346074500003840060b4650803921029003440903424034079055004145d10f404c050040c1c81054000200440e0001d500c0b06942c00a40751050f080e640c5400c16802e81e19203400b82d60342c0c1c0307182d055129040d403ca070001d900c174804144111192840f9100e0100101d5201d034100b868600441402071000301c00700316140100f40030207405e030f02d07940004e5251000c0d1405040001401c0440005090b09054411060516001e08030b60500c00c640c20202010b038000c041c050014510a8100303010306814030842035200044900160003040490f241e03100841d41c410b00204043c02d414600001e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 776121636 1250 776120386 776120407
    0x1b140d050403020309130606020a030e0a0f03151443020c0103060f05012c0918100b03100c120c052106060904020c0a0203065106 57
    0x55a0700580c00780d009550380c0c440b0001031046480c01001d2000c24541003e0f0300300b161a81c0011101d0006070907160030500403181c640040c4071000b0b1f42e4040620b21420220100912603500a2521107091700d1204011036003031142041c038140780441d0301e0002006078010f440b03000b002c20a902068420b6200c00801d0720703480c00d80c0c14101e89408000d00401644142200c11440d40c042c0f182501030460b81d031484040e41c0c541400202030303100b0084120403010100302a80000000c032040c59110000041803203e052030036010011094000c0c0e160402c2b148075a141405220401d803240403203480b40540507242c00008140a10050714041d19654100300b02c0d0440301030b03080250700c54000007100d03540d01c0690381d10508007168138141401c6101c1d0150660042031100c00d940c0c00c2d0440710780b0030782036030096151a4854a100d04043e0494030203034050107503508000c000a070502c0e1341e00740484046400c3d55005100c80e07010482c480880300d181080ea400511180c0000c80115805a01020041000385001c40300780 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 776122886 1250 776121636 776121641
    0xa02090a06030501060f090305120903030f0a0f120213030201050306010e0d0b07080121240518010f0207050619230907060509100f1814030607031b140d 67
    0x1480140003d0790b40006100329030748280790144a0743c503454031350890303800c5488507501d07002c4981200e01d1000e40092006861b840c00d009807a070061003501044e864641d8518054181c03680e04110b400018101e203580d0174496024401e40d9142400026800e0041d41107a00644555001034040c0307050019100f0807003c1d5582d00c0781107080c41c0e032107608220102c7c01e1005c8003410442041c1c1155200c044400c0c492185102e0a071460716201c3e4001d031864001c086454685d1034680a0030042c2c00d1128140000c2045120310b0401112030320000c1c4008100200d0945941c000f00c0c058100001e00c0b40d0420300104200349040302c40058440c20500b4006404200c40c500300140310402a8104024103140080280c056028010304c0020f0166042c6103190811031000140c900da40c1740144401d001c0c0c40703110a5203191041c0c180240c0c01c00141c6810b03060a8035036509540085174508141e1007449144005482d44e0711a0140d0004091501c0308440048444842078449100d40d0740349441000003404400706d60007050 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 776124136 1250 776122886 776122889
    0x1030507182402060f0403050f04030803130c0b0309031c020405030136020607150b0a17071505070f06090b04060501081c051c062615060a06080a02090a 67
    0x55400c000602c503404103450310050080d82d000944d00034804010110500280950b80194940b4125944106139417a0300c01c103014640004c0c20042c4003204000320861449101a0b80d180643c00121b04180d4403001d680d070902c01214110601d400601603403d00031080e041c0d188110342c0041c0f01608290310340011a08440144802c0c21400c130100a011044c0b0380800e807140e21811095403003255011460300891050304c9105c03070040c101414496407903000d900e694001214400001c0603144820360754040d00307230070443c03a600540f0180150381c1d001442e000010001844c1c0400340e02c4140c20700b08141c03143d1801d003140c80f0040d03c105456580070800030f04403008507031145110360000a01541018101c81c41d0051981c001d10180e15003c0300700c650035030010142c7d081c10303840118a266110405544070054161395010b0844404258641122144485910164220500c040b81c1c0d46003010301c0d94518012003070f202c90740c00c4801903205010300b910032007030760341e00440d0218050700e00200c0d0808200c0340c0e00303103 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 776125386 1250 776124136 776124149
    0xa090b070303050126030901050a050702030a0506090d0822080c06040620071a0907031502030403022503080904140423121b120a110115030506060103050718 69
    0x1c41e4011700c429855082840050884403202c141c603800640103150b030301c0c41500c03103903414081d01003240400c3c240700d0340c100c0c0c80803a400b40c1992842c11181c90000d59445081d030b01003d05000c0d103042c1d00c1c0c28900c03410005e48140c004000c2801d0050b00c841d4089407101c0b40c01410f45103124200228078001000304500c0707005621805001030909040e02c000e188011100c0180c0410300c1080000c03401064002a07110414a800350760050107407101c01e451132911500c1c2d440140214003550101a05660940c09948984d00075000d8400c0602035106045080000700c5200c1c01409000d641071010980740d0000d0584120050f000043d28452484000303480c1038112000c41c2d203100b032000402030b82440c000c40d4290070700a441c000c00300d003541b14003000d00a01503181d8200e0750ba501d004400c029502e0801044400840c80502144c1d1080c01d180002c003514507a95081085608002541c044090101c000c0c000b00c0390400c010305442d440711030044016140c05401102004a6401c0014050040348086c0008041 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 776126636 1250 776125386 776125391
    0x30507061d0906030c01030f181505150102070605071a04050a060e0316151b1716120209030c100c06050a05060315131a07020c04060b0901050a090b070303 68
    0x700000310456401d407003a20140a00c0c5581c2c103010703554030300003040c0303030b00c448242004140350712201c1c20b25008040c2401c00981d140c0004294006002d03803041c0790196401001c0e014411695285c000b131500304030118400740103a1081d0410000715118101038032640c3d101d6084200003a9100d484440d0f9907006840079207503a00414001c00800410f481502035080305c20307014500b02011000032140308807290384060310041118180b03110b4400d441d4803000c0c00c01000c4058030f800c4400618028088207141d032000089447c0c07036010884185010702029824405a45ca0202445102110320007941006c10103030f4061040d810762162a50740e11850001c07000701640c484d02030720780b0b0303051202c103a800141c10804130a113060107200254401140d111883c442d9928031070388a4030740d480c0c04804260800000341c1000e181142c2c0c600160008032000b40a62440d82c02c68252130010360411084a240c0d1192042c0c074503040101802d60f50040001c0c10740c4c03504c41e00303000d144035a5030215003056030f000c0602200002e9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 776127886 1250 776126636 776126657
    0xc0507030b150928020f1c02040f0602010501151d0a1710090f020f0102030d021c06050102011802091305061503010e0d020a0312180c171614040603050706 68
    0x709076240da940721190000d0b407000031280d01c03080d1020030070428299134101c3c2c0003e682024405000200c46111aa182c0b80320141c10141c4403410003504203002d82c120072080ca203400a03403180b050044038183e0301c0d02e014114103181c0240c410344010050032610400b84800784254021681d500703070120000e04158408003012408080058286031010682e9103102e40782a8074035001ca0b001c01d0307440c15419415200501c110003644010b03840c60054008440311913000203005013007000c0041c45800700082d42e100a1101c0742e00c0d20300681c01d90350144d00126211041d007d4038405850149041e94004203071483c004034400087d01c815041038030448040181d66450350300301589040902c50204070b105000054416800c400e03600030b4495030351510141c1004000006500411032070351120440f0203215040c501112090301e00301449020030b00c10410364072080e02c1d03c56886070000c40d60048480340e00c00c804c101c2504100340e030300b1b104030004411500582d40300800f200180c0e08012000183c401901d8800071076 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 776129136 1250 776127886 776127889
    0x111305040213090b0414011d030a182909030a060218180a050712020a180e090a0b1b03090a11011d041a0402040f06090b04080c010c0507030b15 63
    0x1041951400d864551a20b40c0c240045410044e042e03405c6640000f421160060b000070380c1c1e0140101e001d40101c180245001c0c2401d5050000041441d011280c45d042c640c02040c10b800b0a441d100d0f480751360b100603005605101d08400c0c20340010002445105034605080d0b00601080c0b0b0500c1070728040b51400e600086044103100c203400d0b450b14900c01100c242c0a8004024851170041102400080c2d000d0b484001040c000360049503003c2c851541900119241d61404000402e802c0f69640540240206002c0c00b00300132102c03201c0288205050301c02805101c040e96141e65407420000d000b6445401d80007995084100c1d4100158000d44030390000345842d00759800c003040054400d03c0d8080c1071182101829000940c1d5144101c616003003200e0000d8542d500203900d0141c50301040b4072940c0140300141c00300d294200155104152251a41d0704030b84180c0f1010414200c0c8140c0c001d40c07109604c502c2044c44151307c0380b4100c8110510440a44001d80c1d0b9070b40e9412820081980c040030303078600e11304034591207 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 776130386 1250 776129136 776129149
    0x3020a082b0e0c09092b0e090402030c0f210c121501120312060905010f0b12010b0f0c100606030f09200109170a020414090c0603041113050402 63
    0x901d0070700801c107420320760b11250707070302e00090720b00d503003c0e144540005101d11420300c4a0b0510002d4000c680c0c108181c40d49010b070081c041d0642c110040780383e426204100e818020b400c24443c56001e40140342c0360360800e08111300c1b004000f1031182e012a202c1e603590f8010b94044000c40b802000f800c028402d80004000b048285072803a0401c0320980c0c00700c84c8810011030700300e0b0030904590100c403090364a40ba0341d0804480e40303052900b05000741400c1800008a0040c0c3c1c2c0d000c28100d030b00061403002301c2500c0c3d080003074040c842c0711445c1040ea40980010301819051100a1480751040544103252008c3d40b9042401e01c5410000c0c5081c141e602c04042210a8060250340740c5403401003c10425103245558820106091001c0c5198115a40f228a44070380d0148039820050300c1c0034414000c03035407450b41e1881e07510707200380e042280502d080c0300c0e6034040900d00ca18203078007c4100c5006403005104103c00e10806401c0140180d0390f007400100e0382001522448507090f0501c08c90b010100d898600390060021 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 776131636 1250 776130386 776130457
    0x180c04050a0b033f0306060f0f03090f19170a020c031501050906040501152f011b0206010605030a0507210213140609060c1e071502060601081303020a08 67
    0x8503440001303410f0304685103401220f40c800f2080710040d40703a02c0d03d0364810b02e890165188118013000b00100780f0042d204002020884400000c0c201c44c00d0105003403d5002302c1202c02d00050020074814001c4444a04003005098403c07124411142040208000a440c00811540e082c0b03141e4404801880207003000305813030340c3c0003500303503801c0c8410f5241c481c04280c1201d0010b07217102040b49504010702210400c0f040c40190050650251001e041c003484120b0082c9480c14082c18030f0035401640011440c00030031064101c81c0e050701c49074219902c4e80810009064002d102c1401c101c0301c000c0000100d200329130845041e80074140d0050b120144c40d44030340013105060304140c10202c810b214407000e607500d480845012042c1038850725100c8483c807110f14075000901c660b003a007007140740403600a80240000d81d40c0031100b400200c030a0443c98846c0c1030342c0707416043d503041d40060419000116107800401211502610910444803a0313210b9807074044054014007501030b040c4000322050343c0c004511104049 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 776132886 1250 776131636 776131723
    0x270c150f0504050f0f0a090b1f090302090c04080307080c0615030613020402091c050607050a020d140705010e010f14060d230a030e0108180c04050a0b03 67
    0x10303100500009006030140744502485950020f40407601a00c0d01c21504030341d070701e000c1c04400c0100c1d100e0712180c014001d880c0300640201c419035440c80c3c0300e55480746651409009510341918240c21a020300003030901c0284003904c040b004100008901100304000c080c000d01079080c4940310003920281c00d0406502800580880c030610907210170582d0003042c2c440d0854040c2032020b0851071180302040c064020505020b6121100b00c441c0300d080144208455a0035100b032095480b5603680080685190041030714080060740310300c070084000340c000e084407042c15081c50991400e042c140d545a80c29541c4c5035088070300c40d0f5103991560a4442e9a070007507004000b11003d0800a81c5050b401140c00f8183c1c03070602a000d00a90070304a03030790384000380141107000d03800c909075016021103050243c4549030003206140026000000035520341842082c124030915000042c0c81443e41e40d030104406064090903603580c45594503802c450a640c10031260a19002000d0040c03e180c19000c15004e43c440388101070b4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 776134136 1250 776132886 776132897
    0xe03031c05060301090503220b070b0c030403030e190b0c071a04030512070c0308010b0403110427050f010509031603050f2b0507090612270c15 63
    0x216500c4088251190440d8800000054569100e400007809040354203400703040381c04000703960750040c4100001d100d0251052062221942c0c3d0701c0b4030741d00c0305100f9070b0301c0503026001040220f00203007034403001035421a01a02d40030400001e511074850414412103204050b54140352268030401c0442d0004030740c00400c1401c80350a080140d1161100801c9100700c8070f14100c602d400007400c240c02282035500526072116511190300d00000c001d04000351102044d001b043d65400001080b81c003e40440713041d40e40c44078078650940782c10b071f050101034803140f00080c4885000c1e4001c10607580081e500341e003100703000354000c02006030f08104807800c5840c00342c121000c5e40c000700181140d035080c1e00e4000800d1503051034980e584200560a4501e203000343c090b5943c0f502402d00c24000e4411416034098005900c1c0c2c1410041900d40a8042da98200c661140c0300104560890400d03010303480c4c4c0d000d0010429030440001e07140a038071260f1460000701c000c0c120f0f07100380703021018010040252080c0346420101d0a05 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 776135386 1250 776134136 776134147
    0x9090d0903020d210504170a03140319051e0c030708040314040806360607030b0604030501020a180807050d122007140d02060706090302030c0d050702010e0303 70
    0x504000e06800082e00030741e03102200408201c41c55001c103c2406054000054900e12444020f050b54172611072081d8580c00580503111010000c906c0c0a05158507448805914a900f640284550001083c030900e031040f80a08601c071400601407140308140c1401c043c600091403202c07000c001c40001e42481101d030801d00030000015080040c654225406080200c0e0300c517400140d00615100703541010006000310010701c0040c551004181d4558801d1101c3d5584298010759282d090304041c00a42440354020004504114081d40c4030810a0b100906030618003138880e01e4081c02daa110901d11800100c0700079059907114154140c14002e0030854014054407480c100029196071240807010301105509682109101d005d801c3c82008110809a4840e04e0700000d40e00c0b5842e10803e22800e688810198030790116840e0004900c010b2a034004d0500c2c0c00c140341c0d5100c00004044942c1d084042d80710410100b680c00c1420040c183e0f103070090b651a1507544115100050000101203c454081d6005108 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 776136636 1250 776135386 776135413
    0xc030216152906091306030f0b070809100510050a0807050906030a050c0f01171005130606090b070503130902070c0b190804051c111e1905071d060909 66
    0x104070082c0c0e00202c6460b5100c081000018007024030b84c030441800da07468924004208070061a588040720300602d00740019582d040000d6603135070411110104241c0043d008480b044460360300494200301c603803060f6120103444001180080200350013800d420742c02407408000d60314211006950110041e40544440136450f0f640e030f9907810740840b0481c0b040e00350a502c100d40f6440746d4121920100c15041003106420402a05903111016019460060480b030610381d082000c00d0040d50b044070099170317502d03164074500307524407049030003041048a450004000100910000030b0000d0080c100d03100c4011790311941032074416044030655200c5071015106000b280f1a06c40011a584030302c034010300b45a4000d035110318003e41007490780400c3c0085042d4403882607080c41e46c0140d04080c0c0c40642000c94034000462084c0800c104241456264258810420760902100b510801e58516204d081142c0c00306456111460751040d4503000545410a000200300151400d5018a40c024504001410703803e502d004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 776137886 1250 776136636 776136701
    0xa05071e050c061f060c060902040501090f0b03060601020a110a0b0a080109060905161808010501170114060d150204050301020301090209011706210c090c090a0b120a0c03021615 78
    0x890002844031baa0300003401d001390b03034004a20722035005204104a40e1600b424030001c2c21000011643c42c0c2c030302400d000b61803c0004200703004d584160014080f42705503076194811000301542c11500100c03040c100240ca0000d4001402c0341201580340c00e0099030500c2407007821a076540e1b105041c081d05000920185228032070310800c9400f91071600c2e40d04003040c5260900000003d900410322507103001c0c000039040120344e00511150000c88000d0041e14a545515410403d0035110a0760115400d040840001e218143d5102a004828400741c140b60b541c09c0080e00b240c109038044621180c001448541c5507911061041da01250260400880e040440110703d644190142c40b06c10540c10403041003550808020550080030002c10980031460032102c42c06684c0c10020403217001d020581c4000c2803e40012040c0c0f00c20117014182841c05985030044203000d40701954046003030641c03c200b03040306c4040c0d1902c0e0038403150003610080c420741d950403049012100f013101a500000d0210b51680c000380c4242 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 776139136 1250 776137886 776137889
    0xd0b030f0105010e0907240c02030a050d030b030a0209010b03040f0c0e1e150613030206040314010c080c0901120e240105010f1407031701150201050c070b0a05071e050c061f 76
    0x11f100e90540074105005175100003455101940c103110381c0b40034004120001071400b4400386030756001e020300d404600615a07180754811001350f002c06010014010800003c0266500034003c4603114045241a2100f0021400320340248501580c008104481c0003000c0e07101c510101e185151008140c034212000320001da02082d41c01c2e1190b0790002d104001016540f01c000051170f0001c00269450342c0d00c1c40c01d034400c1440d0510100c503950074241840d100900402038640701d032516400c1c3c0b500d0180840011a544103100344400078580d0b4445550701114070030801c045044201308104c0b00d031105810014018450141d000504100c403c6021401c1141d2041410940c0c0e000c4040c0c4030b072109501d1405548422024061504110700c00c0c0000651650f08030308000407803440d40003085540c0b03c8500800c1140300e40c1d00060700c00c005000c041f0308224540e40c01254481c68514083c4070894400c1e01d5240341240800c94a0006203001c260100c4824044c0542c82c0c224070b00c03044a414082000301403180000c0c05 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 776140386 1250 776139136 776139179
    0x50a030813111201020d110702120d020303010905060d1e02130c09030b1005060a0507060b010302070c030b1b0a05180a0302091909080d050f24060d0b030f0105010e0907 74
    0x9a007a400c00300340e405d4040e1183d80b1030005051141140305194101c03940c00920341a0300c161208210f51044481c041041d0007160059070255295030301784101000500000703007103180c200e140080b400c070201b08106042841600d5180203000ba80b2502e0041008580d006d040541c00c091030110007070441900100c0c000c084982c40204003181342d50b010803034035000d1b005a00c1590002c100081241038168010000e02519114210410426840c000110200d0082d810300801c4c400c1c00c1003050020034403a410041d40b000155112100060b2074003914007a54000a04440100f44085242410720b070466000b45c01c00da100303075520301c0c04600d950001555400e005d0b000d012004103400703016491502d84c1d004086640c1e0824490750762524900354181c02410100c4850b0041c1030000c000c540700810003050201d03001c0440d0b101c13400e00c2e1400c0d0100402c5900c0300d02408550f80c0d075182c24403c0750303c09002050003842a03e000050942c034000d071861007a4401008410240c01415080c00002c000d0030510114401c0f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 776141636 1250 776140386 776140399
    0x501120b1609120302070e070c0201021b09011424040f080f0604060c0908150f0a020903100c030204120c030201090501050f041a0c0f0115060c1a150d050a03081311 72
    0x100b80c00c00381c0c1040c4651f08122806020380d0704004d80305400c18540c0a500340300ba4225000034016082070b6000701c04100821340e0101c400c1d13004000c40e902040d130090b100300c0010642d03da1882d20004680051800d0303000503480301004070701001801c1c10800c0440050000c40090840c00f6a0314a9654442c200188018031b110754034903492103840e01c80e0040401030510101290008125488014004502190000350010710880054640055402554030441d0040d00030a0400300da00300d03010180c14030105800030076034240000503040300c0c12255621502c0c01181a00c2d4800d085d030000401440b0503800c134a06100307041240101c406a90411a0100e411106100444096691400142c2d2140c112023103128455011645201c001c19404480300fa0801005040040d40d02c1c401919440452240500022809101681e500002c8040564499075142c102c82c85c00001d0000640e2417030385c00c0001d41c1c4540c0801d13081820140c00010140e009011400c00c10884d48843d03480324041003804411600448 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 776142886 1250 776141636 776141669
    0x6010e1503060906092406011d041113090c08010902090f040207030203031e010b0a140d06120b06090c03060f0415080d090504020406021e0a060501120b1609 69
    0x180c110691249000c00405a030501c1c1051446203641c0d04060ba450251800380c04203140c031400010741070a2045c40c2820061401c0c0e07640c400150343e00c04131040801101e80d03040030352004035603035885034032020b0308003070301c42c5840701824004020350b0038068000b42d070301c10314003413100e040b00c2e030881000b604442c0c4098015a54800c0e4901052a10f44440104c540040c0003040240401d0303000700141d4815040301d11403a0f1180e500070a04405800b00b8400c0803455007007040400969840790b40c003440e50140d1011190316200100c1e40c103004070303030003588550314007000c0940d5074040181d41034045400c01c400f118180c1c0b007403c5ca60a484e406100c054441032081407002898415030300c0c2d039000b0000c5800041e41b01510a6035031803805072a60800e02e008000144103140119541c42c1910030340f001e035040c55004000400c81c05102a0f484000340c0702c485203a00c191340008000900500405000e81101030414100c1e540074a0280130b401005803180420303010b85074000c3e4906510584071401c40f107040002c1504030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 776144136 1250 776142886 776142901
    0x1809051e100e0103200303070b1e01140d0507180501081912110a02090a0501170613020d050a062301051002061504020c03070b0f06100e10030f0f0e1e06010e 69
    0x54101700380c40c640500000c80c041c0c00b8000852142072040340154144c4001c1c60440c00e0800201009008408030030180403100f0318507017403d61440700710920030403ca42030651107000c011000700003512402d00081d220001880b141005024001c454106107288148160840d500c0038104200c2640010030030810800041010303004000c008880b0b50003810118a60500b00c031000040c14090103074407101e00c00102c00c88144000000d100703101c2c07460369100001c00c48440c2d08200f070321503150400755018031803902031901090252052018010500b045450344c0c0316180140c540c9110140d00443c801d485005030078001c90b03000f042065000c0341c0641040551a00a40080c0090141e420200e1213440081109801c011050343d1281c050340c002002e50055076502410418000c841803441c50000c0d0300b50f0302c240032509050307043c5a001c60702800c0c0401c0d1850324189810840710f07542c1440500f00d40b209005040d03680180003046070300e012660783e0041c841680700340700d0b40c1e0302d018400c1940801204c800101030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 776145386 1250 776144136 776144183
    0x2010f090504050702150903090a1404020c030a0807021920060f0d2004051c060b09090a0210050f04050d021201060605030f0c0313031809051e100e0103 67
    0x2424008000704a0f50422050003551038004083c4010138074030502c04102c0c1c1203800025a800000c0c01007001002d40d09201c901c000c01310f0400e10140e000b503002c0c040810300c40e00070f04c050305454803d60784007a43d80c504014000d00c1c003541e070441e821211240802410114480001808024004400c4e030a81e400b034110204119108070310b40141c54060100b5000d80418075a000440010003c210702240407034034400c1d18001f44140e03c07074150b2100206400502c480c100000507a40d960040c200095201200000306012420440399818142c0189c180203086240c401400d8422a1081c9803603401c04d46400910121445075000c0c00744035000411100b800c5580710000c0b800700c411703001c0081c070245075a114081c110b030708103550b0b1140c107008032000643c07400400b038190391083c124981780b89040074058500341c4412910320304a0000a03c102c1002c40d10f0052802903500450b42d02d04442c40340515026284a01d260180462503942c03c0c120080041c010920b00007411f50703401100205e8899000e031341c2d9200 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 776146636 1250 776145386 776145389
    0x60a11120a0309060b06031e070c060213150e1c05070306020f0318030702093d0911070c06050c160f06031b08181f0203062b02010f09 59
    0x610030000a80006450b42c140c11004081e0b200700c409000c811909410001140422207801c40c24075041c950b5040c5800712164500e402a440d03003452036842070b83c2d4580c0010799100808581d0740d0001288100070300c1c0e49500c0c80d140b45102d03e14186d41c0704080c000000e1418261580740040e207207005020340c414072000340101001198030140c00c540c0d803a6000141292604115420420340e004114100403074500407080740c8040d0f0b802480050540c0e10300c02407203250380c0500f04107103103428841c9500d0301010b030540c411504d40e801c07056191211450101800280d80100a00068010307043c4880030010340403c940c1e80960301c99003400da88501e1403c880c28582801240c0a00c04a8030074180000c01c0e140c200072450550305199005d01c407181962042c074003d46c40201d00500080e04440024105c1540b22183d4104190b00b041650341741d141241015001420010002071940c7c1e00006121152602c0740c4001a0301d0004541c010200300000180c00303541e250840068103000500c140c07114858441d445040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 776147886 1250 776146636 776146663
    0x903080c120705010603020406081c0f030f140405070f050d060506040b100f0216061d01021e1005090604030f0509030a230f031602040209060706180b0f0105060a11 72
    0x10340b00c5042d4105140a04090320090740101e20b06075010950fa8070118840c8840300cbc00500c10152608094822a54002e810140208142c2c0d50342c40040800f00314003e188503007003030030880760190038a030802c42d05110241c0d0240b09002c040030403c02171911205103070030545801001c009600d0391010041009869002102940140a407005040581d00407824030400351700c0340d0880c0d0803204502c1000d10440c00d00c0c01010301096084a04840d50400d131051a0b139030b04010b2041d2030f00400034045184050b041c04a400c540c03604403510692955103a8460194828410801000c2e0760801d9107014140c4141c07840640c0410000003490403050302d042041724100c6030311600508114a01003c0e040915000c181003042c1806190540d2140344000030036111810030b0115482c10303000e450741c00c110084d80030070b001d503401140503c240c401086003449519001d04002c482c440038010fa51402c004000402045070303076006008401446542c0341ea0065844001007804c220704000703480305000d0701c7d24001c8040341 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 776149136 1250 776147886 776147923
    0x140d06030f051f0203042a18060603051b090904111c05010b09160e010c1403070302071d0c0702041e0b0f0409050c210d0c210903080c 59
    0x2039003000000103240c2102048401c941019143d80c542000c00d03803000b40d8001d096840b9110760000d80c40100001020694200500001510b9030707100861f1110b00392000c14078901703036129010000a03070940070f03096214403500500303800070351814003400c1d982c01400956030007541100d00250401180708803400000f01e00901c140d41e54a00f5503800c80306c00b1500f243c2180d00c1d5081c5102413596060a4020700e00811110702c2c0c503082c1d031150000850310101a0800304d41008460103500c80800c0444000d44508a0b4110186a5420050802900c0e01420303500200c69200103000500f102c0d068020000e0b08600056402c595036a03503400003402516056104140a00013080103943c0d01c5502e501c6070080c080d0581d503003031122042400300411103000490240180e003140c10020305500d0800014000300c1544040d07260103c170404541440c000ba1300010001203281001c0410502c007100c00f068000900140f04154417000518004280c0f03070740e0f40710090580c040450403c1812606020204e100607140c01d0701c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 776150386 1250 776149136 776149163
    0x120307051c030902030607050a03020d0504050705030c06030c030a020702010903051005180706021e0a0c06050a081005010c121b08032202031c0306050d0b1006050901140d0603 77
    0x2151507954042008410140c00c20410602600a0040d0b00e003168009010700701c0d50740d41803030a440c554403030170300383c0d0405500b0440c0d50108c80152181d280039034098001400d81c5400c18052501e803d1007100c1c06031241e1414420020782a00d8101203e5100b00403040158603120644016959452143c10081c0340d40031708600400c0819003913000520401b032482e002001464444059034445400d03000d85e800581100703100c4038a1003020040c2d807001d0908001105c41c0d03c622500c400d060035042c1e4101d0000184005584035495a20a80103034100340c200b0b514241c0341d03260000203000016004001054902040610854a80180000c44e02c40090f0611041450b05625220b8155030003110b002901040c1c19a02c8074129406910034545c4590290040000c038021659108484484001e104201a03d07602c000c542c0303442c0c05d240f002c1c425104060900840c03d000c509022502c203a034110008010313060001d80c0141ea070140e8842d24025517550f02541d81c1d00e90840050160550350009401880200740 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 776151636 1250 776150386 776150393
    0x2030a060f2f070b061504060507060507180e07020f0d0e040e0607050f0d020702030d170708090c01030908040e070203040602120405011202090d1703060a080c0a060e120307 76
    0x101540403002e000b6500100072000c00315060301c60982010301d00c052428005040061030121810b83c101800a2441c40b01140b070a948401039407180e04070301e0002d440481c005003000f540740034480d040491030405118001d5007200404a054852040b00c0032480c0d910003152a841c024400b0340310907060070054402c07030020b00c807025015003001d903a03081c0510301e0320342680d5509402244840c0504410756525181002c10f04910a42c2e070449c2d581058025030070884400103a8007040074508070070701a2105151259402d160f9402080003e05020034030440000b00710059201207155030a106090078002130141c06418004040d0140f90032060a805880050010568000014104440159080725008012404560a41c1c050380c4501808120f41e80031302901c4500300e401425502d4400b030045140042e05850b410700d26a01005082c00d2810000144652414140c1c28080500f442400034005100e220000c900ca0401ca0b104150170402c150f4009801076640e2403040c0001050301003140e03120455400c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 776152886 1250 776151636 776151641
    0x4061d07080c030a08090607080d050a050a0e1903050a0306082d03040f26061503010f0e0604060b0315092a01050a1d0a0909060e01090b0a0902030a060f 67
    0x6508407900c40c00261640c1c81c0340003d003c40c2ca1a0340304072501d007800148014000d841c2c002c080d0403180b2950900c0b00c511400041d1144620400b8600c0740801c060904168032001c03a010020110126000003141350b00091480101201565051500940d19102010201d00420198001103158058140350780700002c0395260528100020341e503a82d2508000320101582c0b48524030170401e00030300d103100401030701100c0050341400c420b0411800151880b1180b90b141005021a20011061010300901400307050910450002d01c544040800490241a035032035aa5000113000402103502c0346a40d0050303441c10300907804003408403000e00b411818001000d035190440003010114074820020f055070b4500314107000346030b03200d410784641d40780543e424421614007040c0418484440650390384840640c861846550003000d00c0715001032001c25900d868420390f20b404a0712521170b070609145c500410b80c0c0d0f00c1d4003604101c80e400001044502071020a00f080140003000e05082c2c40c04503110383c20303000b94 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 776154136 1250 776152886 776152889
    0x3020c0c131b0818070602060127020a030c020d08010501020703021314011d0609010e01060f110706260402090c0d142d070203030118090203010e01060302130e0c060304061d07 77
    0x1501001d0413114582006aa46803207100d40c8005a1218004028010f0107044180e040b0b80c01800100341c0113880550301099a206000300710019550707114003621654103120b106440001490076042075450b240000f5034038141800041d1080c40211701c200040081948600c1c8003c0c4100e130321103100e60f940c3d150b5000c80181e0140b01d01c006600a00054414688080d003a41620070302036070400346909100040390480000c84460041c86400480000c800000300300c0c100080450356290244207010384000a041c4940e074098905d81c0103580c0a1100680e26888126801680b00b41029218050000b00401402083c2c0c5031221003032601d010300ca4103807010044a0700c807410340c01051242c0b0105d2030b01c80d540c0705011641d0200507002800180b00710801c1a40d809030100b10144081844191500080d0071200c004e0340f4807840380e540f14010400c41c207145160b8a510a064078041014010b0b6011a5440c0d22204814034440c92000002500300042a84141c03040c5407103170151100840140001541e64219 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 776155386 1250 776154136 776154151
    0xb060103062306121e0901020a1b110406031103070603060f0506090117010608010302090702030304030804061d1606020c0613031e060f0903300507110a080405040c03020c0c131b08 79
    0x500c2c0000d020001b05008880300f070340c00740e5a0122900d13804110141c0b100c1c0340c0d81c402c6a001c07501003951507882d50380d40103003000f650082c40c04100119040d41007526028859018800f4541010781c20002d1090140700c260450f54142c03a4240e50340703641001214641c006000341c80038505240000700c0c0081d489405541664800c0c2e500d00801d13101c003c03069032386e4001110006d0004a01c0400180002c80903000420200700c142c582c0c10425040543c00d50900071018001c0c12a50031011040001d20740c100f0a41a400c01c00303035101d61412808071600c1c088105a400003408105032144480c1101010069000046400910070401103e044040502400d21142c2c183c0015500440d2150001d4a0084005000d602c80c0c019000c500448440c0c50050f003c010002800d02c00c0c800c9091006040600c001d84100b40714210030742d582d83c1400c0030441240c4907000e84004052050221561926000600601c0780c401142c65030710380a202c3c00d0030000742c5205c000d001d411102c09541000601d0b0080b442c5c030700034900d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 776156636 1250 776155386 776155441
    0x40f0e1b18071107090b060a120605040e0f1014131104021602130c0c140109120f0f14040303081015030b0a0b0c0a03050708070605130b06010306230612 67
    0x2034410102d002c6e03030800940b50781e01035810880e21000e0f50098005641c10714040d200407034000d40c0c500010302140c401441e01002600320181910041606100481c18818401000c01810801002d035541085008202860420784060b0300c1042c0156140a0000042d004006549c5c50702810b1204409083c039210490151111082603014480c860184054440c030503a5442d811107655201d60a101906403c40100b55582e0092900446c61004c1a408911842c2e11200c49900000000504040c0003510880c1045035441183d10302e0f109180445003107a03018945410103032a08a02010a4a1581c1c403145508e42203090401c0e94540503041760030502c0341103441602d807680d242a44e049500c101182c412107034104451100003e4003403400f070070007207024000d001d003000c1456443d2000c4840c281d4401500e442c47c22103910801c003214403200e03401102031a0500006d4a80681d6044000b0f220365034921407030007180040d00d44d440724401d44240030507004100080d810109405055030220002e00c2c00d450a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 776157886 1250 776156636 776156639
    0x150801050711062d0708040c060e0105030403051b0a051b0306040507051203040f09050f130308010306180206030f06012a0b1b0304050c040f0e1b18071107 68
    0x107010b40c541d51004100e5102500d140e40c0e80d40800e60100700c4424410303404241c1e0006200f180c0c4064542c41d0311880084d110a0040c3c00c10381880014065203074810300812000603a640800d0341c2c024143ca402035414240300340ca400c0b840c8a5050480c141900c41e000f10b00c240d00410043c8a0300241c00034842c4040117001886110100c1070649814044070060610b600c40c000400582c1845400d03503990403180801c1d20301302511071500700d02d091200d60100050329120410b0200c0d82c0035030101d4a40111100c60701d04c0070442d01e40e901070035108052001a0078a0b0340d601d1061444509481d0499480354001c05032a0369103400d14000d00341501c242c400d05d001a10300300b804048500a500142901080055108001e00359644d6581030310b00024a0507070320a483c03200350a040c2d03a00304081c500680c0b0681c007501000e405070b42400101c0d20203400b504002400e00c0781417519803401260020003041c0c0d0041e20031f0840e2504000c104e013044203000b140038500704601040744803544601301144041e490000d580409 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 776159136 1250 776157886 776157901
    0x9060307120e0f0a17040e0103050c04112104080418060f0b091305070e041a03010b06180913020603070f1209080313060609021c06091503080a090915080105 69
    0xc414541d0490300e10351000341e540c1c000c00d00b60b541c4a405d8a0190f041107181070380325540108450b03000c0c1d2048500b40d008103040341c003078505070103052480e06002086a0801100c1c030071040f0300100780042020502100c20210f01444902401ca40241c035048214503045c1240c0314064001b00720a00c14004694a100800b1a86810364002c49200c2c00340240308048481600005200801d0043c0c100414000021800b130116125801404007220201101c906004900700526081d06c58200100744622810080c081c0305002420208004400a13200d4120543d540078030031102c04103810000e1750040340030003000388096104449a020303e00950360940100f004c420503905482d01d50000400e850018800a226168002d13010b9010303500032100030440969035031400049a10404000301030f114482d034140560880ca0003450700070240c43c8030401c02c6851540ca01c0001b01c1c1d017400002c002c030b40c00144124a1520903810358014045000e8104808402c1c074a910700c4207c054481c2c180c5075421710380041d084 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 776160386 1250 776159136 776159143
    0x618120604032f070b04031407030309150314090703120201020f091e151801110a060b1207060309111206180a140304080c030610060c0809060307120e 66
    0x16039042c1c0300c501a59090940145100d6900019000d541d020303143c854128000c10040308006106000110343d4031420340c01c0030120310031040c10342e82d41d66018902c10400280c0c04261903044a0001c44403d4422840001c2240948585044011070b00205c81c140f14407a8004240b01003160321480d694006040403c800740c0c05d07030040d0200d4411300c14091004003050309002504040c1084110403480540e104100020152507148000c1d0701c40303d20104104008110780400c00403944024240501042029106641c3c2d0303a0300b05d80700418464540f82e000806469090848608248180943d015281c46490041c0100203d000603070742c0788055045001c0e541403000e0900e20000c0100d000d440c1958034006101d180d40801c020804c10f502c19450100042590802c4482c00b10b00e03142c0185030380740e10b401c1c81d17245410281c5022900c45c0e0410b40070b101050f1010341d0031104480580c249251034022742e042101a80c0185800d02d030b0080f00c00002c00082551008031100c500744905c100b08034104c8114040c1d6030307 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 776161636 1250 776160386 776160391
    0x11010b04023007171e0403020a02010e03070e0114042a03051b0901030b011206030b06180720010213080a0620121015080f090c010c0f1106181206 64
    0x804c0449450500003002030618950180e00e514410f1010b0b8140c01e10003900b102d040301c05400507008010230404543c1c0c01141882e4204c400c40003001418203013014103440b41c03c10310a034084201840b00b40700180d00c1d80d8009407110411211885143d044401e40710b5100408036100c0b1000924100c000b03440052445800041d024004ac5880c1c2009040c1c00150014800c1c900350606200013107140c000b501c980d5000750070155204480034000c4d410300b5800e0050b5650751600103002d14140700d0403c2007441d4030500000350b5038030032140f100d1500700c20302c0b6541c020701c02c522a1002c0d180c00c184011031400c40000340c14840310701c50002002240c00c02040900300f0900740c1e8004000c0081008041000051400101d420141503100200c07016650000781040c043d41c1c1820300c0c04100d0410400a10f00c54000703000390b1105c2104040c201c00340308800000e158001000005000280941608091001c83c05a03000c070254043d0426076141d0107400c40704812701008982c54468412152080201c480100c0c1050 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 776162886 1250 776161636 776161651
    0x60e0105030c12060307050a0b0c01061d041b031b05030d1106070309020103060801090c031203060f12050f010509160f0e010b0c0f030d0b090f0f04020111010b040230 73
    0x3d08100e140703021010122805424075030f0500c41c02d5400b0460b40d8400d01408010400515081ea44070fa0366141c542c255405079102560410140c40b800500007081c0e803c0507400355209480c4d406110742e80341d01c01c4009034a50000381040d9540041610b8220120040c00c0035144102d013241c49203444144222070001c020a810304160f00110081808a07001740c005280785c40c81414041445500c07451401d00319400301401343c0348502c038007408005100480341c89003d03004082c0f90501c03a250501ca078007021282284a041201e5100202080503c002400024551030313a100083c4200e040002049a440c4110864005140101c42d8000781e00741044130110202c840b272403200e0f41d1030382c079240c07502c1d00076041444034140c6409418510396601c2014401807108440003240095101c442109000030154000c00800e03a0302e42441c06e200540455451030b580c4160b09180c0400e2101d000d2820a015004504449400500200b034841420030408142800844080c407403241010002851290301441901e5a1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 776164136 1250 776162886 776162911
    0x509150a14010c0213091707050a1203090b070206010f0914010b030907170d030b0d03120b031006030c03020909060f011202060421060c020606011d030c09040b01060e010503 76
    0x1c100d108000c2615061400e8141081c0e2000c071120707004105030011109006040c907a0b5411184c04001c001c0c4441d802003440d241005080142541d10340d65030701e01c2c015001d80401136600044601c540700b9000401d00d00c0d4010841c8206d8240194069540c400a0144180e82c4280c004081080030080c400c0c2a0f0300a0011440700d035591824418503816400505440050b0144c60300104125420404500c3c10a0f1a070005058a040d0542c00034101c450603030015100349082441480440d0f0b02c04100055841e0003807001032400354140019151140b40c6c1c00f80c0c8001401e258001081c004410300c5d50089a000792500394880e503c20604545a1604075017204420010078014007800f0b4002d01c0d000e220510141c5400d291940350106254045058401d203920843c408126808100490280100050207030006040b507040ca0b20005c0d000d000f04140080105100032a14000c1c2d0780c0c02c0242d815081800303068130b0060708081c101280c0d622424003450001c1500d010803213140c0c0d446601128480d5071118401d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 776165386 1250 776164136 776164139
    0x6110601120f0311030d090b1024030b0307120c09060503030a0c121205090a17040518090102040b04090506121507141306030905060108060105090c07030513090e07120b0a0905190503040509150a 85
    0xe6005103004cc1d0404c3e01341c80340c0c54010520980301c000c2031580c01d0240082c000618a05034400042e5a1107804c854084e03041403107030500c510340011584e02060781c00280c0010081c91070740210350345d0b070808001c1ca55084c2424203002200c0800308000a00e50f01540202d0924042d01c00144058800c2d8481c2c1d98020b1090541c10f102c42c080070f000c154015031480c002500d41562035040040320b0300541c10004a0a075908140003c5160101c2124400000e01d0b001d07245984508d08006c810030401081402030005c02c071001145021000c044a40407041e030002c05100355140c2c04010018082140111b603c2d00c80c07540089201d0074001081412204020000d03000da60b2010800b143c0e90b049610304500b030040c18803402000c106017805d860040c0c40d40b543e0000d00f0111007560607280004990000d4040d0308521102008603050000003980104500000705407003d2610b030403403900c1d400720440044d060107522994104400403006004440c4212202c200584902c10013400407400c01e00c515501480f400300 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 776166636 1250 776165386 776165459
    0xc1106070806010c051605180910051e09010903080c0f0703030b0d0f1103010606030c0801030228030303020c060f06030c010305100503030406110601120f0311030d090b10 75
    0x910740e60001061619428403901640d54500e810400d1003103030480046030405116038182082c400f1561002c0111440700b6042011800303841d060b9a0343c503810102d031039400103580490242c8415800c00b00e4261850614a000502c940c000c00303948200320001802c1070b000ca220b504010082d1804070009502603883c020315a50103030000c0a0b42000c5580003404414800b000c1010002d20740e4000d0b02400d110400700540703a0815007110401d80010341031610341100780451940c4261014150707a4103440fa00c0103146503808112600080c03040110106580300008010107505030003400011440c80d044400e50b4540c0c004114689800316076030354160b40101c00709407031584650085a08003400d04a9002ca983d00c0300f0110382550300c01e0304544d011803246070501001c4a0200301c1c41c0c2c0108401e040b0f82500072900d90700d000301800c10507030140c1009641d00824013000fa0510445448855400301007211036244d09c3e01684010040b51354200301880b1500002c1d42142c0382000d1891095004207002c4803451416 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 776167886 1250 776166636 776166647
    0xf0f0501140a140a020c030607180e0a0609020c0a0c060c031205060a0b030108030c0712080f030c0c1902030105070e0121020705030711150f1b16060807030c110607 72
    0x151035000b000300f0000c03074068648902008281101540d8041e000980c400c1050600e46080508100f04200c1030044240b540380707014210b0401d441082030001841d41320007120f0fa0180489805c4421340354800104c0503201000022082241441040303444042951441c0680c2c07003260039100900420340c4800d0308840003280364051540410020600c034455a00c40c03104e512240c109800084e0668000a0710b500c20003010820203009008508040340c070300c4029964142140241240c0007407100011001c607088590392020380d07282c1d5801c4422280c05120080182c1c04050070840e0603806946000081900c940c8984d00c12180d604043c0c486201d0414544030104600c5221074006200503424441600025014070081048074080c1c0612500c0d2801c45042103014940c0e403400c0b060004040181c02681c18548081c1c80300549401c0f074950940101d405400c0c00c1045500210310a0424440e011800541002d0128000c3e55150340c1040040c0c0407d00659000d40841c800c0003059105c08002010a4400e4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 776169136 1250 776167886 776167897
    0x2031902151e07052d031b03061c0f05160501080c18010e0109031a06040b0109060c29340e040209180a09120c03050307110c0d05070f0f050114 63
    0x301e1800840c00c16140000f10301d4240c45c600202030500000b440f03c103501e03034402c00c030203c0c21020710145181800c00018071103400402400c60507040c0c6103006800c2c801c58960181195801074103407040d0441709001a004481d480c0251400b091003103012800030342a030410380c2e540c01d90f1894850074010444005684c50038001c88030030b0410142d10004000580c880450328146d290b0440d41c925981406810042624031010300f541c1003144a00d030403c42e955000c0410300041c1e400584030642804004000840d08070101d9060030222030300f206100c00480e01100b0303400400070000c1c1100750003110b14500384644030721000c0305002540c90000b0000ca85001d6000700303401c03280100100a8220410b80c54031180008480380c00d40c0b035544407035640512a8200d50131361a04494a40440044a1a603000d82140000340001c800c0110b18031220009007010000c00d451100018100000c4202505e010b9555185900480c0d0402082260000f0040c030302d0a0704c0c1c001d0340e00585850b090404074862402264211 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 776170386 1250 776169136 776169157
    0xf03120b0918010e032209050f071103040b07080a2a080c0f0a05030a08010501030506011209111306061106160807020a02040903030203090c0a051f02031902151e0705 73
    0x80d102c501e2000441000180046c807015080500300c222141c41e58414685140d0007250b0050500c0c00300049580085a407590041c102d0810301c045190750b000e41469400f8640000800403000640c85085c803a1403000703000c8032031282c3c0e18000345551403525030004148049000d00c0060307107000c134100010075800107000801008811103c68900c50714100340303840007404058445420002c0d00450350b5902c004a9405000c080c2024089410000d0008000b0030006018501260390b4a0200d010460307288513010040b1b0b402480c0340d00c00228258903000a0409114000c04140c4110303a54409030720101d591840b8200c021b051004802441c60180c80455008101d8011800745018000050340d0702e10500c518503000e90b0380140c892800c2d240c0c042c030b0500f010300d1051040e14602020405981e8100385d0b08124801164410a40b00e20b81c00241d24500170092030212071505a07000b030011650003e500714a070300c800d1060310507a49820b64241c103500301c1030890f2022984c4080005103080c1c06100204840c00e41d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 776171636 1250 776170386 776170391
    0x90b130302010e12040513060510050a05070b0c09131a1c050303130b07030509071a070206070f05190b0714091906030b0303090117060a0b0301030f03120b091801 71
    0x50703a2250368184213040180c24107010300450180000e003020311010114180400082085504202c005903541d44801e40300010000c00244050256210b1000da40c19164000e40c48051800d248006400c25044888050300038486401c0707001c0000c0b224080d612180b86a05030a401d02d08900c001d0003c000c032114003030962004001140b071f002800c200300031842030301c4020049403241c1c043e1400d034401040180174102050b040c48184103034018049500c03002c452400304010b440d01102c2c11307040058014860080e42c0040e02040ba581032180440c0d142c20711038071540949211301509010180c4000302c09030094000520b250001e00580e02900307181083c610302100d42820700f501600016150405803c14100146100804110198060180450280046000e0b509040c000070001300703007641b081c407824600035055010584130307211981c00901401d00003448559075030710f074140108402020f031801ca00160340b6004841c0058010f1140b40c0903600001c0c50f150f00c0b6200d000700310902240c5012001407030755 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 776172886 1250 776171636 776171651
    0x160309111e090f1023120c1c0203010e12071103010209060a020c01080705041a03060d0f050304060806010c080405040e100e21190807110304030305031504090b13030201 74
    0x203503440142c5200b5a0925681c402e6464000c10740a203503801c070340c00488401c1c680002003088184001003600f000307030103890501c1081c11443e1140d1400188480041e0062a442d140e100d015606504129400d4000d9000344505682485170b20307500c2c045519060340f002428031003203000440d00100c1c1e883c0e0060007400503080031102d800140c001d1f800866448056803140c1580fa0195821001071a40f2030b03010f0400b40d0526191092a85030800416500d5840b1280000020910354468a0b10b084444c0c11101e121400d5072586403180d034980c800d00440021409240010300698494041c40ba1096402010242081d280c203052001400000364060302601a080100803202500e101d0b10790400b207054002c000d05403001d00e851340c0000894213011941e001c200b100c8142407000c0e6900001d03c09680c83d001000b42c0e50701c071044a849449102e12800750000040c00802e26611078083c50090511180150110284030100310445143c00801004040740e4400645000c1900d40c0d5100c400d0302a00020550780c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 776174136 1250 776172886 776172889
    0x140307050102040b030415062601061d0f090102030610030926032e150903050f010b042a2a060c0206060306100513020403051005160309111e 62
    0x90308190000c4c0c03040403002c01004140814004540080625001d04000c5c40c0e042c801d0143c3c182400030000c900721508810088401c0e0b60940c0404021f0501c030049080d06024420080380c2e0440560b15003e40000e42808184041d9040c8216030085200800d00074a050300380c80203401a0110030010b40d0f0025611040081c941140004880c02d1010901017542d40d2130091408440059003080303070700d18803102500e180655076000c5c18410951341d1005211400003100e1804603800c1000b5003009000d405004164045a001504010b00b0410100e90a00020445911a0740300103501c222424107441d200d1000966603004000d4200d056500c05481100c4a0410342ca40100c0c0d500c03998219882a510a01c1206955061040d40d403c10786c2200074061900309030700300320031149190082a220303002c085020443e0306040d9045900460b400019100401003c5416400a000480d07080c070350510a202541c8810340309104400469500c0480c07403c01d0b84e40b080070701c00203102055108880c1c2e1003402c140311a9 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 776175386 1250 776174136 776174141
    0xe0a20030a09150c050403020f0418030809390109050406060e03210703050c1903020a030e0a061b020607020301020301030803010f05090c1603090504050711011b020a1403070501 78
    0x15001040010035102c101d4a040c200c00700340c0d11415125149401c0a0003002c41e40031044500710ba804803400610007880800090041004410f0045403a0490040030101038015000070f11035150501501c000114400d2210742071045500c120740400400700840d04010741c8502643e4101c1e40c10301d000240709032580042000c0f100d15400803004600301055490092504000d403820b180d21400400d8002642d401e00100c1e28000c1280040034081c1c0450901801c1c5410810444e006461688120040c4480d0801a48840035840181c0c0041c5a102201c3d49a04081e144441118050b0361120207511000e00f01502c50750340d085089074804020060b2002584d02400598061800b0312510750f56035242c58610703c20107030799034042030250900100308404c501010b003d80d20200c00003a461118030f08185002c84c2e140d040d503044030b03910a20380401c0c814046e0748401c03c18900e1000720000c000101c0300c2e9500041c5080d04000800040c0d000420410008160b094184001d1135a04212400c1c900980d42c4c02e801d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 776176636 1250 776175386 776175391
    0x1a0a08072a050105010902090a030311030d06030f030f0e0109090b0622080f01110316050c0a081902300403050f0105061c02182d0414070e0a2003 64
    0x295910031280c402070100a1144500404203841e007146440103108c08158400c085100c045c003803045001c80004020000d0086500b000c4001204205803134482c81c0c501006d8010010640001d0310a101900d105405000149c0961a050b151050a41e18185a4030054030441c4400e503003058040c840003005185803503184224211044142c41c4140c1018039551800c11001da40c21407581c1801c41703001c842200d43c2c0880381c001600d5403c3c1000440305020580c0e46120b200c000f00035502c04c007042c0ac0c0500c000c520150090940ba602e90509045411108a945060003051800b0014161320b1b141c2c08007003050303890b40c20410b61809080c24542d4031b440301d909290900700c0b506440e0351120b08201e46450241c0c41c82c2d1000302c01000040c003014032500406e00d03d15803050b01170400401d403008940ca0200c5e4407500e02c1040b1060582d140030000806640f00fa81100342e0301214240c801e8960390400c0c140c0031664505884480000d0400d030390320014400c01600700f40b05001209880c010030701d031101001000461 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 776177886 1250 776176636 776176697
    0x201091a0706020f221d1003020612010e0109020c0709020702121015050604030302030d0c020f10061a160b040f0f03020a02090c03090d0507050c061c061a0a0807 71
    0x548540150741c072040740c00889400102c150403041003d0000c41321a481c8211006e0405444003911307a40c1e5020001a00d11a80002c1c1d8802000300b080e48a001a014071681600ca90a41030fa840742d030b81d602d04200340d004420320b12041307170410b0a0a10088805070302804006000034008500709011401030390802c0e0079225164030140d101d25203489850300708003000c001880d050320454541842c54600a40b2405401140300000f61074006003442d941c0300300800e400000c9900243c8681031120f000b40d5005211510030700c08000b0381c800d05040050f4803c01502d200c803000f401d2180e82400076507140d000c2c01340001c1c01202c4c3c07844030a17a50700c003040c696210007500c070340f01e600101414003090040011404005124a41402003002001070003407010400e207500c6451800d1164a41c070f078615043d4140780c05228002d400020110b10b1201801c0080000c00540d40e08120400c801070321000c6030004c0c1c96001d8404d9061300d40400010301e10910913015140d201d15503140140b01621358006100035400f9118841c03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 776179136 1250 776177886 776177917
    0xf050c0309011227050c0607110913052a030d080402061608071406060a0f060c1410020a0915021e010902090c09041406030c04020318010e0a1401090201091a070602 72
    0x500401c2410425040301b640300700c9140c1e08160880c1e94100100c56038204260140c04500c02156064032000741c0030b0f1081754042c054845c9a6807000760300015040c2e1030f900b0030104002002010182c10041480b100c40c4041c0d03900c461942e40d42d6028400c580d8400d045e001130020b408030086020545180282c082c3c02d106a0f02ca4185007079401666180520141180e48544d290305410455410040c2c0800103c0303d55061100f00a00c00e41081806117990351111038041c02410008203d502450380104040d862980b0b58007002521403032000043d070748a11550025a1161550035401d4812460210502070b007800040382c860000d030701080080e00140d404442c00140400d650300307a490180540c00c018111002d00c000c807480c281001a58601060352401e00640e0300001013691900101d00750b20000c107141001740181c014015856580b4100c2900980b402d100c9048800600b2506006035419260143d461000c0d0b1420a81da10355040c1c43e0031060700c83d0800400c00140004d40500251180d80030000b0030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 776180386 1250 776179136 776179211
    0x80703090f09021c0b0f03072c040816080d0207050d110c030a15020c0a08030613060b090f0f030709060503070821091801080303070f050c03090112 65
    0x550040c10458010200d22030061185030314002c80307a914121341009041010802011040105944000e902d203226018005c401c4c0201c2c0c18490344407400802072041d15a400541f081c5540310a40b9081982c0050000360b0400000850600605c042c0d803c09011300119840c000298040c20f04a034060a400c0b552070b0001401000001d821581d10440d4480003070103010340040c0c48000a84580d075100008000f81103c644c4007002082c181c1c151200c1000c1c00003254030044003802d000c030094000312012071040041d039280318140b01503402007004641104401c0d07800c00c61000100142d4542d05e9a00e0380d04048843d5680425907410040d5800401480c5c00009000d82850141030070601d07140c00640b03244d4071205d280f0380f40d0803580c21180c03284881d961590342c80c0c07142c030300000303a920200c82c0100003145500070000c115110044000c40c040d480d140c90b020111081954141ea0500400100c0c0304540c1040c007843c40154000d500d815044011a03400203060052420420b001c1c0e01d407852480c101c01c510080 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 776181636 1250 776180386 776180399
    0x20109121101180b040e100503060c031504180213110301090f0f0902030607122003270d0c050304170d0206090a110f010527030705010509090a02030603030708070309 73
    0x3903c00c80c0f46903030840005241001c030f00b10624400ca109424100c00c000d00028541e0502d1204440501002001c0d50f80906108030b001240744c1040d1188a00107440701240c2c1071a140c035218805908041c4165030800c031506400f00691206483d048000c81d54907040305200c4043c280006502034a084080040c1001203000c44070112505854241c103c20702c0c5c05202c8015a80003e503803a817101d41e901e0712010902070a1a90809051714886440344110707a004c42c000c019556801031485081101001900300112049180740381c414034400f002c268020500c6003180d11300c6462540d039024003c008403460a80d80d0200d128200112740c0003040150404819030050f96810b00125800c4051003000b40081c0e0002e07101c2405280c061015140b09014403591004264012000e0b1516034849030f11201d00c500d0144030b003004041c00b0413142c910a0140c1c410108441d0b000340c0590f90030003805401c5000c00d580780d084030002940302800c50f950600c0188800d03c00200d5440050414074400c1d034500380040c1c902030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 776182886 1250 776181636 776181647
    0xc03010615020d170c0309033606090f06030c160507053c01090308030a09060b060c10090204180309060914010225051509090f0702070909020109121101 67
    0x200c650b0108410a94242e008061161245400000903414180c1c0c1e81c0340d43e00d0b500d14500c130314803550001035120040f41c2140242012442030707011416000c4e0448210780010003a10f8800c00002f10340c4a40142e82904d07544c00c200c806035500000480e4081d00c1c041c1b0030111106c0340401460100d460754001c0105101508000000c20340d00013001d4101d0402c945c1b5803441803500d20407280310b0110010200203001d1765a10880c5c8860003503820440d4075560b0304000c443d0a018000d08401034500300d041c500a0710a50402c3da003210540c1004c0ca000e0b144903c154003905000d401c21714416a441900c89943d001c010030030200100c4540e01c2911800c203130710b1400d40c02805146965000300c03841e0644900000040c0d13001310300034603c4840e420720000811030b0ba1070002d8080d4403a0b041a0303003045403aa03866100941c01401040092801c9503880065641d02d203080302482011503d800060308214000c00400509400840c100f500c1414860741d45174541c00c0100c0c40401e440303030607034205200320400c2c000c0c0d58111 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 776184136 1250 776182886 776182903
    0x2090406121713030f081c0504020406170a0624230f100309150f022502010e060c0312190513081905040302041401050a060912060e0c0301061502 64
    0x150552410400078690f0701c409050b0b24803010300803030b02da00311540c1040481c1e811203001c106945084a071482140d140d4800500741284c0881c0118506840407650032410741ca04120b000d0404001d04586405940d07204c0500090424400c602c44800360741c490b80d480c4021100050b02121a02c500c141d1307a00c600315017102c24107410090007640805a0407006803a100a01181d44440b800c01203100d980e14601800800160400400c2e05c2c2d1806842c004450181d40040043da00661a03008500901121660540d801402d009005c904405840c450710b00700300018109170400e80003a241411034051801034002400c0340d403c5641000d506d8041d480b07258500c201da401907000c0c00c0e21303a070040701a034411040e0710401e4070785801458618910422140f01d50119800b55501400078007030f850711364401d8143e0f088280200c0d40b03d18155000818003c0c0300d02c0c042c2046868404040b10900034035100d240043c0018082404030340604c21285e02951030034011203009109441ca01000841e040c0360085c10200038 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 776185386 1250 776184136 776184173
    0x11403011202220c0819020c03041509030804030f020a230103051f091a030f1f23040507080102130504231e0a0605220209040612 57
    0x1440103001c5034000c03284908031941c0c15500039038071a800101c040d0302540c1d4034241150b950708100300c055a0550200e40300303010780051307082c1b500d64004007240320059010320b03095039000358414001049000a01c0e503920450056504000c00d04c15240c0e00e0b40300340c0d580960402c0d02c402c004111100b0071030900c0c40c5140010807503000d02401c0052204c043d80341712020b8551450400d41c07643c1c00b0070283e4891903c94090f070071040c90208900d5680e0702c0c94802400c850780300d56411040d0341e00702c80100c0c02c01040340c501c40d40940780a08942c075001003c01001030b07030b00e40d580362810781d4550840b20f045141c42e000c13017035803401c0643c42845440e10349007031032401c00241c0003140541d0041c410341034044c403055510810344500b2035000ca1080500085d000c6c000400c403030105402c81c503850a0101082e2954450201107986212122603541c94070110020f0b2407140c0f0400741c00c00703d15201c412100700900850765548400703043c00b504d49807042001805856103034000403554504080d2102c10450500d4039001c52451 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 776186636 1250 776185386 776185427
    0x4081e13060f0c0b06040504082512090609090e0c060d0902040507050906070204111908010806090712060c020a05030a180f12140309040f0e0d02010e1c0207080106060e01 75
    0x801e0341d2030040004d4040c00540c040c40e2940007080802051409a4500200030f16880d0307040c0c0c8a0700007130241c00001201c19240851079136904c034181841744200c0d20994806403030b248021440c0401c2000101101141139006024240011000e0755134080204960120440c01140720040c0740100300440c1c9009c2c01a50500c0b00c204002100d9407203500030744d1415601100d000034940c0400b040c07100c552050858191060742e64002d00a5400e0b04010218140c400003012518207584500e0950341c0c5503c2c0780140443c2482481c40350001071940d4200e14109400c1e4030580e603242c3e000b079452907d1034021840000103e050700d03180c41400605900f40c4001000001030312640f0925014541d15650076400c0e01a018240840c000070072801c0400c1120703107c000150080060b0300c0e01e41000c00042401908619041c048c010031810228814010716000521031809020320f02c51400c15081070f9015403459030158012414005400d41c0c00303111f0b08008000507154052403004040005104402c0083c0c80d00709490b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 776187886 1250 776186636 776186657
    0x50d0923070f05011202090607030306081014040f03171611060c09060f04030f12030c02060907062604050102250c05040b01050d05070207050f0a030b04081e13060f 72
    0x903041c0e0035481100d80c03e0824022000d954805140a40321f0307907040076000600000e1200426916a0004045038072410075146c15116906a19060f2406906460b00c01180f000200d40490080000c090030288a420160162140c00e118000c0b411022100305a80a0003841070301c0700d0726000301c14400c05d035a07010050000780c540680b4035541401411517160040c0c0c4c021443d030080034004e0f000c4030080c42d0420300d050504100c42ca041e9420303c4402e00203100083c00c11020820740380c00043c03014000c4020230b003e05402420b000d0200d508018030500d0145a104842060703070044240240c0d103005501400015a54900f80220304103031142a1406400000c0d1148010011844401c4ca2100303882c0102c5e000b048250356040101c50501607000c44a9440d4030302000e02000d9a0001580c4089450a860f81c501d40703d498020088002607521010f0468604000081c001a03194001080c9000c120205007090b12a881490781c081d81042c2080802e03851005403d0181c40d401031562100f0308107611300090080c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 776189136 1250 776187886 776187899
    0x30b1e030a0813050a03050f150f0a09032c0f0f03070b030a09060606020c010e060421050f0114040c0e0712020702030703080d0207060623090403050d092307 69
    0x103846045002d00b071200c000c50448074050740d4a52000041000401d01c0e081151281886610f4070810111030f2441c1c425030b013000b00e0583c1c070803034464454425030380034491942d150710b401d82c050304401104400f001501c051452102c503010842201700200c024a003010941d50030180310304d0200c01148503101e030f4208800c407001580c00141d10401d594800614035100c0d00d481da074803c00b50422420040505041140c0820502c0d4000783c54182064260b8a61810100300c10600c91984950300880c030510f001c0030411910040101c0711440c10070304c1901101e015059031000c40e402c4400c9600c000215128590a000511595a80c0c0318007030010403442c0180707402c0c140b00103084813802c03001c0452a1a00801d1507402c0d95420301171440210f0b00321070714036600e44003200e121009520001007210954035001c1c020618444103901480107140800402000d1440c0008001da40c0c04e0052048041000c2000007400034140c1d402156070080c81610101c4039400c858894410260310700000c14469800307650104a80d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 776190386 1250 776189136 776189143
    0xf030303010e160c0f0f03030f0c12090206071703060909060601170903070611190504050a1e0305030a030203070f02060f010312020304081b030115080601230d03030b1e03 75
    0x40440c0c52074040b41076510f0b00740c50546504d04060440d00d00c00100c0d90a2152504980500d148245e604204003840b41840001319040407419400160740d010b40303071414003626446500d01c01d000421140c04d01d8616564500140b1a8120710a10100040240503450a2208a09802488490140c00e0301c2c504000000c0c81038a015801008030a01c40007c940c0c1c0714401e00131901c0840d0804004d0009000101108030035131b00c0350784800301350345d02c800300c05403003604c0340c410754080c1d6500a104038038540c17800292041c154824124283c6000040c000040020381c20001804c0c518125200942c032032401480c09442440c01031140ca0664000030108040340c4028998181969441b001c05902208550f000324554050354000311034500c5820b03544000d00d02c0c9110b2050000404074001c0c012150004200c2061013010b20810005900610040c85402442c011031101d4201c25580c0c074440308210f034005100915240c80641c0030955811400c103240c00e21449140500321100c030400074502c0c148010994 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 776191636 1250 776190386 776190391
    0x4020409080c032106030708060f060102120a020106150306082d070f08060903073302071104151505030933011d0a0216050304060306050f030303010e 66
    0x426551400c040003004140c0080d220092240011292134141c100b01e03605000315411045030340704003044006426813500080040039617a041004d05100e440d0014581d900349000392196042d070103a059040380d2a0840e0029001c180f5461b0f0000c28a1464075001c0b003600703800b400c415020542000418014048001040403810505103e8003511400329500e075502c0540d00003162146004414000903445815030300c10080c0e8440d8000c0d034569440340c6102c80c2d0340313218149004121400389a0481150b41c0c02041400180100c0759045031208901010318080717a1150308100e407080f12f02d1184030283d06092269007441740980078445c040c0d03070030329150b04064001041050204240000003456a040502c503031050402e102508171066403503002d0301e40200000151494404410100010300c00710f800c1c0250440000d41500114035860700c600c02c1010350711540c0c1102d1400c44000303204000450400050004000950700003c42504100c104411105d800303408038482c1d8024070051081e292903c000310b8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 776192886 1250 776191636 776191639
    0x9100e16090308390712020315070c060504060c02010507020a03050301050f06090a0e010302120109031403130506010f060f020705030318120a120e041802041104050310020c06010f0e0402 82
    0x140ca032904910072000304041400000329410400544d400800c040c980b507602c0d00c496070425101400d40b80e80c48105000b2906c04040e50560042c02c01c50b004000041086402880905d0083c21916440c0c5881050711810b50b011107466648910b02c2158507420300c20180c000c4d1251003d00b500d01035648000304980010300555200744030701034158100d03035145401c540010f08043c002110841d5108540203038044240b005a0182c04401c0e6a510b1011042c0301e403444040c0c0c5600e81003c02c1c00350b400d8441c11500024051200300e540c1d10340b200003254007004414020020060b20308105800d0540c001c200c810300c00a00c4055501400092006a40c0032003590001200d060303190019940c1e480c0019481406208074030703114029100f00c5000c0c490010031500e0810b00f580c403019501241c603070074001141c4440c90741ca980c0d819003070100300041c5455000b545151004d02505070a140c0c8443c0003909080c410521481c070076500080f45a49103c05000e0140101046440c12055615180307003480c050f00000c000a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 776194136 1250 776192886 776192903
    0x307050c0a0506162406121e0804120311030c0d200606091005090c0406080c030103200604090e0f0106150906050a05040e070518030105130f0606030209100e160903 72
    0xc1c040f0122081c01c5e4145c030341c2090f05011680c3c0c0c1d03405020846101c0c00040c4c8000c921518407662502103024034072445940008400d2400d4980704030441d81d0581c08000b20200002c000d14440c612100b00b01030f001001c01d003000f4040e1141c8119020340107011a180d03890f0383d03411408620050100200e00c040d8040e1080c4c0d4034024940e9001d2112116a580350050359000000b5021310100e90540c50180064410315294003200d43c81c4c004d01d1910034002480000e003850703401c0c03078107200483d04410258140e00b005840ca50405485513800c0090321885050800340e6408400d948802c00c0003401341c2001001d100014a600d003007034003030040841c076180c0150001c0c030100103540c500c4988a40101c600404107891900b03200c2c100b4020003802a80116840518022103d0520003d85018420079004031000c90200100c0019543e603c0002d40480400381c55171552201c0010141c1c849d9041c65100e001c40800200a10f400c0a00079514044c001e09000000fa912111000e003c9400c070720510296500706148 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 776195386 1250 776194136 776194163
    0x2414030a02190b040b04060e0d0b130f060e010b13020301050315130b070f120b10121404030201050412020d0504121b0b1b0111040e040c080307050c0a050616 69
    0x882d020030b8a50001001c860001000602e20809002420a8441c19950448031500000c100300c610240030b50050000c1002202151400300c82400e011060f520458010900c0d03ca01d4541100301c035580c0d048640c00365141c00c0400e416203002c4c100e1852044a50108506650410010030364424150b0705040681c1440350104034246d00d410600100346910800b907440c2c92410316401000484910000000728195543e06940b0310050301800725844805080c7c0120b103107090204403000d014100302c80180d555a800304032050790000220300d02c110700035000483c45082915240160007a400701c040d00f10f400c80198949a070f907000b0200e504548800c050000c04019904281c0c0b44039a898031200f0181c41c160034001043c284a2010749269006010301507000b08114020500782c1e901e0105000001008002c1444140f8035640225000350140c815040c00a0700c42c0c0c0c140b8913640c01450151081c0e4440300c060b08036882e0190070640a00303c140e503041d0501003000046002c0140e51030f40200700e0002c01c0318 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 776196636 1250 776195386 776195419
    0x151401020f0a051b1806090604060812040512060106141803010513170f03160e1801290901111914010c051c020c010603062414030a02 59
    0x3000c0d044540c00c03000d840440406103802913071450088500560307400c001c800b800161402102102d000301d2400b81d0000daa40e40c040400850340310040600d6801640c07000c0104c0c807114100b0800004050380c03100f495860b030925081000c4a60f85012240c440d42c0b10000512003c2c1d400050b43d034050b0804012980c40398100e003802204800000c00c0d10b0b40542c03a0008200d0540d070291000040a800b5104009501e104010140020700c2005020b81c85900d0410100750100c000310592803a5402c2451300325403100341c03070300000c1e5042c440500290503200c1d080010b00505180d81c0b040c012881d0503800384802c0c2005104111442d0003140728030703070510254007100c031081541031040c010039690f0755a00c450700586070319005400340305c00d11900180c1c3d0300e8243c174001d005001c0c00071505c041200081c10422400c0da0102d54010b90301250100c00030f9500e4140c00000100d1502400d540d14074144848688099114101c0c1c0454030319a0211b542100710703502d255a291404180c81250540565490510750700d51174 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 776197886 1250 776196636 776196643
    0x409081204081611010f0e011d180c0a020c060403020109030b090708120a090524070302070504050412030c180b0711090f041205070308010918060e031c15140102 71
    0x18151140007503e950310302c200b001d580340c40708202078242c8403c14032408021040364021500044140402d4a0308100c6400d000d510380d04200083c0002d09840f0f0309000905861750004044c0c503590700001000c124410002d07014488248142c030150f41d110304203440c5400007030480f0b03811701c4042c1c038529008021a82c29801400080d01a10200007245c0480348960140d0406c0e5000d03054050019003004800704140c40c0c0302d12035500c0b5008040118043d09481c401e09a036680c02003c048003948120074000030586c41d00c1c09418801c6025080700418803d000b03d020b0305940186071302104200e070056441883d180c034030441c40107440c680303007249454050701d25040c9001c6500000044e8494020801c0000d10080c0709112803050b032094060000305410381c001500c1c68051041c0c0240860036110040c8207448455000d45c01000e00e84054000620807611b40700304407a90121504d84036000010005403621003902403100f0140007003420040c01e0003645044199803d103008244040000100e0150799030b1080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 776199136 1250 776197886 776197897
    0x3050f0903010f090b0a06140f1c050607090306140f071209151a0904240627110405010c120917010515010e0108041412040320040908120408 62
    0x14401041084d015040444584004803804201c19003005400706040f811010380040001010300b81c101c81c44003100801c4071310b11144242d8040380402071645004103004004540c0520040c0d1140c00c502030543c03d01b18151a0048400c2525a11001c18860990a135100c83e59120405250012010b451481410003400c50ba0384054541078aa107a2007140c0441c5a120f2480418000c0f82c803502400720f04203022042c802128080c01100c007843c840d4080c20040c2240148060300c060000448a4494190901504040b40e07100c580b0758450182c02210b054503c160f64407d4425012075040030f250000091820002d40d070020102948045a98411401000210050015140c1000503455401c074180c0c02810f003124111440c880f5100010030950048096840d0800181e4031846990365036181c00d903441204d141c5904003882600884608000303202c01070000355114002d080d4640451403507074824003407071184051089180015031400902030104030303011054044804d4019903201d0410324100d0051 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 776200386 1250 776199136 776199161
    0x1d04060b040f05120c030d051303020d030e0f1e0409061103042109050f0607030903050d020a0303140c040e15030709021c06081002160804031a010b0703050f090301 72
    0x4200030520b00200007070728040e108244c40c940020090b2288041c0e80b001c03503041c0603030150410280c02c080c092061004141600b0100201c0e180a070f81e07940440c851b641025000d900050701101203546600e44948911410706007112043d0100741d140c511003e08502c2000b58500c0b6a40e5441a40c0422009800c50080c0c0070000e400c06880386098108040000014400e8411041c5021020307c00c280c040c9105500b03a4030040e1810084403601e409003c1c1950181d401a020700c4a41030000000070b40411041e20b0104059000d84180c40582c540034095420b000c40817112074003100d0400049000c0f00e0151821110020a01c3c100382e21030304900000218a600c6a94142c01100808a080d40e0240c00030a0743c0041100c5e8660340c0f0b0105003455045074224000c1d0071041d001850300340241e240300c2d006480113511a140c000d1000300c41740d03260040c1c0c2d0f1040e0b1040b14405c2003620700704840001138100500500082c00c025151403503580c2d005005100b5044c04020100000c40c04e42091b032825440007172804003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 776201636 1250 776200386 776200409
    0x604090606050a0f030c0609080d0e0f190f0503070302102012030f13020d0b072a02010908030c0604020108220c1e030b010527040f0201080a0c1d0406 66
    0x32243c0d903044c0b01c0c50075400700780e070000007a00e40000d415105e14802011100b080001e040740703500303841c0201d8094000d01402d0750b2001d0495150b240f182d55004026841840ca002003c61b1603242c48201c8000790700542c8054465040f070b2000704050386074071500360b107079005504d8910740d518074400c5c1d00c04409141290b80b0225100d8a5001600c0604c09030045000b48803460403030340316990701d844003500d070a451340c402504007004410320800030312281c07a19a0403d0950070480c540300003242507000d440785130002020150444204100c29540c00c00003c50240c850a005185420302ea000215a02c14010380b00074100404100010350241062014401034100018171071000b100604021046070110f000d1481011200390800800303a4400440504036540030840d03841a80c40c00b01045207540001649214000401d01080c4605071410070b1144124400c0b251104240540d000041200c00000c024441072441d000403501d64030f03000528009000584400c04104620740c0c404500038001641c481018001c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 776202886 1250 776201636 776201639
    0xc0f040c02100e030708031503010b10050703140c010e0307110607030903120e1201090c080d090303030b150703020f0c0901030f12020a060204080d0e040c1403040302030405030a030305060f04140604090606050a 92
    0x1120062400c2c208102728000d10400f460f01d41080091107071056640c0106e0410450000064090b0640307514414503004400d09102c040c4014071300b035070a480b151282070b400c0003400400300180400803c2c204103040e904142890241e80d0080c182800a02000e454040e481004482c40b03845950202082c002c05410a5405009041d8007030290848100c220340404042002082141e800203090200010540e21600180d03c0d64070240c2c0104094030300d080e0000550b201c200c10340e112030001002d00320701c640c1c0103004558150410505103405040c010380718420700d0004001140301325400032915600030b2816404610a14020783c0f03854001c10006200071300204000a00035004907000c03c0c0340d0310f1500c0e941c102403c034400f08030403600c5192542001c070359900f03101c0fa200c40161024550051107030040764500780d26075000a1414500303041c100d000980301c100704880c9080c003840030203c0000945041c055001c0c4c0d01180010302c24020106401955908a084240400b540051005001c080e00f0040c046 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 776204136 1250 776202886 776202901
    0x110a060903031409121849050c12150a020d111611010909060b0a03180f0b060d020405090a060c1106060603040303060801020c0c0f040c02100e03070803 67
    0x141030510701101280c16840001d08260310110300703040402d05016901d0314000181c80303c4509804042c1220780c00c25010a4180c21110520403105500030b69141003045461041034241c22030000400c8211f5a00a2004440c002805c00505004440707000c44e0483e12615805600d28500720b41d1201203c40b1242420034080210025402446480c0300c0260074840248500400c904034440c0340d100304218821003c110000c036900030715412202034140340c04500d05981d820141c06640180e00824140c0200240440b41c0380d03054482e0f1b05211814100e82c21040c902038464000601c1070350405407003600a000010000c5da80c4807041c1c1c080a6004004106a0070300c0380070640c1d9111585801c80d9282d18016980b50b541c0d01a41c8107a50f4004510002d1440d030360b64001b409825000078004500341501d83d400860b140381c080c0041c20001040c0b00040c000c0a80340c4d4104000d80b07a80101036401a49825403005445a01042c00c81c0c141c3c030070203000304110141c01c0c10b41f8078502c10a407001c1c2c038070301c80401802900c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 776205386 1250 776204136 776204141
    0xd12021b1b04050c18040b0f1008090615011d04020f0a05030103021e0913080d050a0c23040e0c040801140f01090513020409140d0203041d1303110a06090303 69
    0x79031041d601001181d940314404100b6100f9009242041160501401d459181c01d803c6407101440c040c00d450400d14400002c035800b41829202c0001161800c410031118030b008014940e849802c02100e0b0390075001c008000792a00615a0354401d0f0b1080c107002c01425522542c04444c0c5200842c1a4036669480300c103001002500203000c1284207820510300078600b00340c400031a0b140c400c4000c00c80300d05500d503800318006d68210481c0440c0c50702024031022007a030000344280340c402c1c100c10002040c200b066a80c010402c1a071135900302c1039501c00c00c0c9000014070b60354042d642680d000710980000e94071000541c180381c1c05550b10282d40780d030801980c4221007400307070125030040482d0b5030139007000e03622000c80e081034450882c0c2c000642c00d000707140300300176162640040010078040c210003c0407078801044607081c42c2201803114050b034800201040315048030709404400f281c5da100380e01c00c1e60414000008801d00c007100040c00300300c0c00c02181c00c030180342400b0f108000b551220040054508270b15000d4003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 776206636 1250 776205386 776205433
    0x607170a050c0f03070203070e2a1903110a0f1716140405010e0f0105120c031509151020011505030105060a0e0901060801020721020d12021b 62
    0x2c803801400642181c1c50400400e4a808aa004000e800d4042c1401410011144000c048429403900404250f48800000e500314819042d00003049540e00c440240c9503d0122004009104041c6400c034952215040c900c141c5044552a10706004403407407140b0107c4a840d040b2428400484a5006210740300d80c40d000c1e010a88001e0361241046c81d0401300c450509406548990340c042040d81210140c80c2c61300b01000000781405040090500c034092035520f42d1190116060983c0800000601c508680301c840c148210000484907035101d4500b4a4041d2004100c882c47c0f103008920700d04000308154066900c058400a02c68181c000d56201514450b000c0d01d50810700c901007005602c03000c078030b50030103000f52441000044d29520845250080100058000800c800c146542e0740102087c41c150038001404554020001c0c80181c040c04c0d40441c403000000f40b5080259072015901c004901d4008003940c00000c40385000584480b2100c2c4051205c155400442006015004960a009004c1d164114 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 776207886 1250 776206636 776206657
    0x20a061109040e06100315022209060b0702031c050f0a02071508090309131b02060f060a030c1e120302060a050c0f18030705061b010e060c090607170a05 67
    0x11541c0c5040902580302d10056440807401d034210042440814140440c41e07040c1541f0110062805d181010101e0301180c841041c841400440f01c030030040e0314030900690b405422580640c9207414896400213640b200308518034041103034043d00d81e5802c54081e0b0156070010110030040b641c1c5165240c4025122186030040100b114100c2c0d00321385145100f40d2081e403040c4d4141d4000d614008002007006540301491004240041e200d00408142e04850010322589920700e030010610f03030800c0409032444031001052107000b0030b07000c2020408141402e0800c42140c560544c0c20031440b10b8012705111040c500e0304170140d440b02203600541010303800a01540b0501c3c2c540e108004645030001020500d03c00c801c0d0f40c0788042000d0000400112880d01c000104200040c21504550b43d1940405c500e45c2240c02d55455801c10303072185012100013070185559407070310840540400d240100700b96516000300d46840f4001c030b40c04100a001c005100620015014041d801c8984804900200034074030781c480340802 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 776209136 1250 776207886 776207891
    0x60e090714031908040315112d04081005090a080a0c060e011107021c03210f0c030507090b032a120a0c1106040c0b0c1c030c0809060f0105040507020a06110904 70
    0x1007c110f8030511410443d201d0703017104030385004a4000b41c171340070401c0d20712a420410b90128002800d40c05c444002c000801114014019000c1078203120300c2219030040c81d0507840c2e00800c00b900c0c0041c503604125480700c074190a0070340c0329603901d003004030051000d500c54280c2d40d0718200c40c2601c854240c4000c2c00c01c1a100315100d582003100707030100c90300010140e40018041490f614401d1890b807003440c249230080303405070000aa0b0252000d003070410f42e40410343c0034001c80d69841c1407003611075204940720089e00d0720804480c45c604200b01500c9042c003100d0700d1203403081e1f41c01d14882c20080d0400c01711a000700b907150344c502035800c0407e000c80042070709009440100300c050760009083c1d080824400e10480d04000e0720b00440785808980b196990000344039510070f0155920380c08018100304c0a50450b40200d90300000c00a01030540500308160103044031075030340c0c0b0440030440c03191076444200741952000d48000c0b1f0b90352140c8106901d81180014010300d024149803204140f4002032019000c40d50013110207 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 776210386 1250 776209136 776209163
    0x40801021e120115030e0610030507050a0f0501080a0e160f150813020303040f150f0e0f01031d031204060b010905030a06090201091502060901060e0907140319080403 73
    0x38502ca030075125510301d05a0401042540d400350b00b4200012154200814404004c090b41801c00300c0c00c48003804076021a038001e00030b11004014510150906645c0c80d6800340c1012005076440e00306100d401e040200a400048100c0c80e25008498101c000404a41c82003a20080d850282d10860141001d00301100c10001204562a19401010081c0e62901101130301c1e0350601201c0c95111880c142c3e00341c4020040065010102c844605c0284001200c0451191403040020070100400c0003000412000e0041c917843e607030700c1c950142c03104d08090800254120702e8031610320851210b1500c0c1d1401e80008245090040085048035220b42d114501c1041041554001580e0903401c1d8040e0a13090781c020385505c000942c1540c007429000380141040b0741650b5507498006904500560305d007005800840600c01e842e0024020b42c00545000d142c21442854100072070380eaa0700f028400e100e000c10901e03207a004a0349081c010b81e03c5107018001640000901400c090302140c0c0988403c031b44c0100ea2409 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 776211636 1250 776210386 776210437
    0x904021c05010218030109032a2004051b0d0b0f180901050a0504030f21061427180114180c040504080904020a0318061b08010e06060309030c0a1506060e10050c1204080102 75
    0x202c051300c4000b00261740707003850080c0553b600186042c0201d2500032130009810003941d5201d41080c82d84c481c2c0c00c48003030320700d243c0f540c84182907500103400a0b5000d03043c4014000000d0300322640b003210045c14030b0828250b40700301c42c03a52515121f15011140e034624010000c5050072800034842402c49081e50303180301d6600c487d019299031680c483d052540241c094004a2203024038084080c8580900c8000032a07000b00704072140f5124503040d181c0103102003603401d0703942c5014000d0210000400c8212030801251405c0d840b404001d1056031103242c0715950003c3c00e0b80c00e650003603211109160250103183d042d00d0092604d00000c0c001c5c450043c03901441d0746103202e0024460610603040c0c0e0280d010254003600d4403414003d154101404404060200b80b082c0307641c2001c100000b041c05801408015580080e10080e80211991504050100194a0b0400306541c84200059104165030b25040c0e81d9909e64000460510401040c54903000b00e000600041000054000d041035078040c1454031445401c01c41c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 776212886 1250 776211636 776211661
    0x18150a06020a050d080c04090219110d1d010c1e0204050c03160c080d0c03050402090c070203031b0f030a0306030b0106110a020904021c05010218030109032a200405 72
    0x2c034002c20690214288070103092084002c2504404105401c6041584440d003100c143d0708141102640090711034042d132071440d4013921b9404000320352405400c00c41903079030004102d041040e0032907491444d0901101c215074413900b51204240e81003c1c28007041c645042000d01642010503003640710b5403c04010514140402c0f0131240242c0c0c14580285950030f40307410030349442280140c1980c010400380126007050030503001c0c5184508241d81c0c0020945041d02c100141000041e100c0c04400728140003400040e1400000c03a14118001d002135882c000b90395266500d4101c0c600701c856468000800c0c850030241e055004542664407a07040e07030005a8035007004580d5040c00441c194102e600850028000d4200154115003103400980b52440190080f201040710b4620054115841c2e94001036030303100801c10211000f05d10300c048000380226205030720300070404046900220039540d400740c812051414205421103480703902480c910250050f640001150407148d0000318012401c040001d00302c8600704 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 776214136 1250 776212886 776212903
    0x90c0e0a0b030d2607020604060609062904030609141506180405101503020f030102030130020913020103050f070519140c1c11030301030201030b18150a0602 69
    0x60002c2401883c04042103034002c10a09004403804449a801000c00c0710800b0403910424541d0014079080c02e0502c0d00b0710131107445501c00c107400c62070000c0c144610805646640302c003852100c0c00e600040405480c10000b441a640000c0c1034902d003141c0d48003000811841e0080601c1154259040844003101d001140203003100e9403a404400d014141080b202c81d1100103800ca40520202c0742c80b00c1c0f44510343d0741141e04100c06a0125504038408000714600b100322050480c5051340250300359454a01e03d184440d030150300680d01450b10b4501c0303000840c07103254020401b0790010103921076420000c55440003600c41b1041030740000d00b0580080c12640824000d42d0080459946941c6450419003801c1e0060003c440701c5001c0100c18594501e148003102d003e0840f21130420301402540101c1c122490307400456100b80030500491500c03080700d43c0004401e4034112502800c0106100031712800142d60615000003400c100c807500c0c814009405181e0381c0c0d010003034000359072080c10aa1288001d9170780b10f01c407 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 776215386 1250 776214136 776214139
    0x31e060f160c03120b0a03030818030c060402060a050705190209090105070c02062109010c0e0a290403140a0302071205071421030c070b090306040321090c0e0a0b 71
    0x55416501c0041d00c22811301881d20418207000030704000f1000000e584005d02d600c242c00180c11a0107201014000358050301081e44100015490b1203140c1001a0319088002c1002c0d10850000ca201d108440c060b00450341c1a5a01c00151800103845980345464114900c40c168042c111000014140401c140f240900800540c1c80e40840400582c0c00c01400ea40101c4032130b02e0710440c09000e80002000001030070f0240f6502000444e8a0a0105008103181d60b8120201d200302c044104c100032080102900d03039262400000c1d80c0d030500c60140e4441b00a40315a07800102210310f042c1030341c0458680428a000e641d8402d03401c2d0340079240e0f04c2107070001d2841850005000f540040004200007a0404230798010f11102401d0071100c03100c1c58614071540705038014065400d8000299200d1004000c0c4a050050005841c440f41003c40d003001103980d401c0020401814421615510f0f0984008090302c80e01c1c048040310103210004261601002c0c40c120340c424002d0a1344184042650a0818098201038820 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 776216636 1250 776215386 776215397
    0x409080904090507090c0c0b090712030834080a0203071205060d0209090a0b01060215010e06041e02090906042a11030a0305010311030a12030b031e060f16 68
    0x5500c01000014188410115414403038090300184001c898001c1d42c80341601c41d10703030f050038014504002e83c8a440003440381e011900121800c1c042c04520b41481e55210b5058608514151b46008901044003100303401c0c800c08148604204012402e140080c0041c07120300e41d00d901c910789441821200b07901099410f540401c02d41c020340d0400546641c0314640c821030050802c2075907407058020800d8804190b03000302c0c1540209000009201c03400c0d48883c01440030b44001e01c407402490380780800914040c001c00ca4008034030008504582e4850304560041000c5885100400d80325030381034402548201a6140128800310005400e40b4081c40b840c60164400c10b000109640702c03c81441c1d80d00e504030010b0050001e000700e802803da004001400010b8415280020154110308040c0388400320501200d1180d804544a000040c448411a5000c00b11034100401c08205000020781058440400d00800e9081c0080c1010000303800a4214040c0b00030840d8103c098441d201250414010400802c01041 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 776217886 1250 776216636 776216647
    0xb0105030c0903120a09080f3c07180b040e0703060b06040e0c0a0905102c0603090d0915050702090402040204090e06010e1503070b09010c0c08030301030c05040908 72
    0x1901c0e0080400c488010196400494402030045803138126a41a100080040000f4408a1020003514205c0742005000f041544c0c45c00d5803000c541c81c80d108a10b06084a00c0c91064201e03404000d2443c045905a02910116a215003031003200c0181c0d006d1207000310b0b0400300d848485007000d100f20358407894408040c10001e030640d180c42c4081d0118101075504014108400110150a1070003d401500c001c10f000d41e4921034018010102d40d41908214811641c014880c01800c1c1c01068010f200300c049907010b01d1583d43d80248200c14040c1c0030030b664000c4d00010400a1a40011410781d401c04400c3e00c45400550715079910390806412034081c0e80125804004003400340ca02544007523403180c40100050704d05500d80c44c01c042034801a2010015592046c0d005204c01c0f0091007040380d108001d000c00c2004112050002643d61031144140c003088400040c240480340d203e100c2503452950040d6050088907901e02100e5602c0d4001d101c140c0b451091a58081180c0c98107000b060b081c25003000c211400e04 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 776219136 1250 776217886 776217901
    0x1d010c0c0302101e0c050c0618120c031501080105090f03030f06030718050f0711031c020904020301030309060f36081c0905090103051203040c030f0c15030b010503 72
    0x100f00d030380c0c06042806884d11000400d03024608112402802585c2c0d045980c030024504185040c0c0c10a61040c4201c03818131100c03152811f6600c0c0300c0341019044075205001d62403005483e040a490b01096238060140c84c4150300c0440000c50214104d0347c06000070003070740d40d803c00303000d40f00c2c141e40c030444c10340b0f800803c085840080c0940b1043e82144009082d200c1c5169a071500c943d4604030620450b0450303442c0d004014441425007031456125043e800c0c15078946018561080d101c1c829021102070044511152515404403641a01d4070908007a10440d60703540c42c2d00b0050030201305403140c41c00007101c5000314080c0c0c5100b40e901c000000c04802903052200c075894090110b00700d4804051283c581d0084002a40540400403e003c03015107003283c80591298100040c0680000e0700f18501a166000041000400001c5c0480900700102002c030303200d86480c80c6c94241c00000303034170280641d00c2c00c01c0a0300c14400c40d0100f05c81102e20208e0201146503180d801581903034a00085035011480500028406 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 776220386 1250 776219136 776219149
    0x2190e0408071106040e24030c120304030f062906030106030c02031603030c11030f031b040e01090c031d0a030503070903060203010b04080c01111009170a1d010c0c0302 74
    0x2503e226400c0c403082511500c010031501e40040d80015a00d0402c50140310360720312120141d0041000c0246142c6428400c400441c5d0348090140c4124042e80003601c1c84c0650030010300079a0b0203190b224807030714110b030407500f0700101501001021000e001c0b407041014041341c04000301c040044001070546415a80b030100c0650080041e0900c00040d4042040b126a02d030071501d038060072071442500c1c001000c0d5441c0074000c00c0d008000c4e21460465004000780380e10f82c15440700703483e03008004100742c80100e202d2500c6c50006000f258040b0040100c80c02c000305009820b50091182050655402c100d820490f00d14150319004082110b00c17540c00610400021a10901c01541d00044138140040310381e54a56441c0101d074001d078031002100002260a00541106001d0030b42e080c98240f829214204132000b40f02d40b00c98100d4186980d070b940d5480fa000805c030b584120400440001a801c6442d42040b01000d04003000f80e45500d960000d00345c0c44c007030496014040120b10103420000101050b4115400c0c001c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 776221636 1250 776220386 776220397
    0x2901030f020402031305031c0b2706010e0303040b0301051302070f02010c030e120a02030601060c031e0309060501151103030c09010c11150d0c050406050d0b0f0301061202190e0408 79
    0xc0000141d0781c05c2c00850002c00043c620f0050055100b105040048060011142d1b465003413445a0f00002401881c003840c00c00344080200446a08200c50700c071100141d84052901074226054040440c00144182c1d200003d103040ba00d01751107480c03510760415044001c0380b094600c000c102600c02c0b00c010f000f651196002048642c1300342000031080c4949030000d224590441041c60466014489640c110704091018030b00420b800d09103c2030842c515500a01402c804045105220107881c865040c0c00e880b0f50441091290810000c000031f5031242821200c0c6500c100c0c3d43c0020540181c00754400030030000880b840741628001c4c3c01d00300080c400c01107410801c42d2800343c581d2403180c2e0a40900c0d6540900c482d1000003501c1c1c440b80d80b00441d0380c3c098140c0351103c0c000c805006040c0700401400c0c0d0000e0841d884140354420004000d0f981d1000078407504410500b1b250107601e061008120402d01c0099462164002c641d51035041e110750000f026009a14010141c0c0003041501140004420802a10 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 776222886 1250 776221636 776221651
    0x330b19030f0b0a0f060e030a030f0c1e0b0a0b0a03120f0c020301060e01060f1b0f050f1f0f09080702010503100902180915030604021212072901030f02040203 69
    0x40c1540c0c42400203203440c0d0060b08003c4020f041c600d8104031701c0e038101044c18841c520960242c0f1740840c980d180a0320440c4a10b5042d024490308000070002c11180451408041c0002140200042c4036814075556943c412100012043d180078101030343c0e840c10080d03800440354030061030300841008413400c480810008900000b40b01d060b050200041c0d80038060031020301100c886105541d850484001c0001005056100600c80002c02502c018416109034220058000129101014692900c24940b1515010400340e134025900300c20059803d10030321388460703001081c01744000074000f88907404a8000100040000b84200240c0b001940680d0103036605c00720709034407080c1c00d5030350f03508450607a41315640b5000000701d083c40f0b4602c54039240c1c03030250300283c905000c05480400e0390f022980d90349001e44041d202d04403624018665440c1000f520000d4400030041985444c9145800c0501001a5030742038406180c03402415101b56038480864102c03030b0081c4c80701c03502604680911000354005001d64 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 776224136 1250 776222886 776222891
    0x403030e01090c1415030c07060b0d080a030615021b04050a020715090b1e130819090305010537060b070f050c06180112330b19030f 58
    0x403d55444a010040510071480405290014200504000c03d00e00c43c1d0038038482801444006482801510703a11544503e00183c90180d450018003c0b07100c04030000d084076000a201c4d00c0107681600042d044a00600000c0701e20000e6020513611280a00c7c540e000040350486550726a00e0a604150303040b199900700145004540e8544282300300708100322101854441d1030140c10000d1242e000769004404040b000d02042803da0807178804500900362007480321898040c0403e0100c1c0310221044c040c1c150b9141b108034803d4180c060408403881c402507842d54a007000044202c00b02207044048505110b5461610481086080300d03003c0c403007451040302d20355410300803409a820744020407846020f2012408400d1241c50103601d0440f240003101e02910007400100142d07544510b070100744034000d0030084550340040b200d210083c4040200b0003a04428941d0000055103800c8000046c000d0800c03100450035150840d04035103105070301c2039450700d0345400c0070851410310a1b4403c1e00381440301c0c00003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 776225386 1250 776224136 776224151
    0xa060b1503091f1401290a030f050a0b010207030807170d06170a0809130908030a1b0e01050f0f0c0f0f011a0f040e030403121e020f060403030e01 64
    0x1540e0964008030740c00c07480e82e032001069500c41280e44900800740c0d00034507828040504420b04045012030180b1075040c0450100b0b01104a00d511041031554415a0003100c0c0d841e4905040010094000500010100340c50007002c0703000000b950150500002c0103800400c5c1492840e41e51240e00d6005030025590b021210440400d6024208024000c58010f8540490028105811060141544c0241d6901c5034081c40c0d1400000780c414090368603210040307178030f011070702d03074001d2254094042e502c001002c51030700104101d40221598040030659180c000480d030030700e00400040e120440480e0f0748901146040c01002c11229080006101040000c003141d81000c50085045113402d203c800c0c500310755040508400c805030803d10851402c0c6500344c119299551528000c140601041404c0c50f00860319103042c1c450049003002110001e650010300d40d05000c2d2050002803a62607100c0300440304440110300e9850b01031000039015150710072040a04015101d03541d080c1d000700100c1c1d50301401552103110 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 776226636 1250 776225386 776225419
    0x6060a17010303031406030a0c0b0c010608010203010906090b060307090b160203060405210f04030f0c03050d0c0506010608010806130201180602031b031303150b0406090e0609030a020a060b 83
    0x40c041d0080d403080c1c84c0413a4059100103101101800100228029800107040030301080a40c04048100e4039142d1040b560b90003407000150140548c0d41021955600020000070400e00d5035214070212091803200f0400000c12004100ca244410b07586800003400d414010300011201c80300030944240103400040720400300d45c5c08a81801c0080f50b044c2d1f0142c01c10003034041c0d00700c0c10050402540c0441b8030301c2c6241610f280381482a50040b030101800300454141c1680400070100c0e00c2d90065034000044406444001d10000e040d0200c2d01c2044441d0300070fa2000080c001d0003403141d181038416400141c0f007d5900c001040100c094035030b00030b078100032601c442480881446801d00d00600500c0d4003542d9140d0107144070024020f669421168590301c100070311060310340b030740c00514280ca0707200800b6040c007116189401c01500c910300000354002e00d07040340007a21700301c103502c15200d200c0035106450755540d81d580324546074040e820001000d0b801050b40400000d01540c00006548070003045d201c1054a07004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 776227886 1250 776226636 776226677
    0x20a0207300b0a0b03010e0d08041703090304140604030209150a0302090c370c081e04030308090a08031306020c06070e0306010e07020304090b0d15060501200606060a 73
    0xc03082d02d81c0d001c5039050000c91116402407240607201500207002ea0240c0f034206503a52180c40d454a01002150400b00d000c000d0070302c0f100c5140c2400c26801503282e04241d040190ae950291003a071085075203010010301c55041c507105650890b60014032400d1241d407440c00807030050000c0032001d50f101c49500e501100580d03440241038001c1c1410940c0341d89034501c403000038142c442d40e00c8100c04038003440843c0710315400040e0074400984600d03140c8488803410500e070021190250340f43c40c3d0b03031400405195a001c51841030240c011a4025030b82e000054841560298030344001c031101038404201003000038113442c1c2c1c0f284991000c61165400528080e4110710250501e1401e442050009040c0e0b0707003200c0c0510342004030901410030051424041e04003900065603a20484c490070035455210200120030741d6515240100d8150055001c1c1c44415281000c10020100c50041d01e01041b403001600395911034804001030b4aa2020000340230544540c03041084d29004408184100407900f1005221202c404 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 776229136 1250 776227886 776227979
    0x114010c060b040905011a041109060a0c060c050712210c02030405031902091006050d05061807021606180b0d063303050601020c0d02061323010201020a0207 69
    0x29000000e202e0349030009002c4207c40680c09a100b1802d00c281c050442c81402c08807442d2110440301e136661181d102806660070300c0c3c03c3d2800380440d450704110b900050782020042603c944541d50303800d61004040003c0d54410480c40c0b074810401e003400031385010480e20707502503c610501030040fa4180b0369181c000070b24090701840da034151281c400395a5003c44c1052045180c01990f04001031381d450f801e10f00018010b000f084080c15001da1a0400304210b92120350f0310703c11890203000400e020703107808040a561001d50300d00d0380014810111000500511038565000c040c1284410454000d190401503906a00f01646001c40c0745c0c0e540c0e40008a6101d1450036040000d003218a2225070880120002203515403580b841017414108001c01c5a07986e404603008001d0207088401103516000e1340003184640c003542802103100c0350720b15800305414610700f1a028550070001d07458405044490012403d034024101904003592100c2c40c00e111240240c810b400041084091103900100c1102210042a124 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 776230386 1250 776229136 776229143
    0x21903231504080c0d120c1b0b0604140c030709270e0115080f060915011203030f0c030204140d0f080a031503060e060601110706050703020c030a030908060a050114010c060b0409 78
    0x140c86c0d40398000309805000303951521414890180600300701480701803070075444018680140750b0f0000e0255541da41c00300d55402807100f0354030400d20b0101c00c101c03c10b9000355083c81c08100c00d0640041c1c110100070040e072200d11810441074410041d100454041c000501007801e1035500c4030102440003024018085c0241a080020300316100b010b00854101400070340080f805400400491045070035800040b07044500400c0e00608552141c00c044004080540c090424641401c00c40e900c0c03140e02d50041c0c0140e40306040041801810b10081003a13010300c040c5c0040080d400c980310b00000c982000d01415054400e400c02040365207256141413144111600b0498089607190ba6076a01204200110b039880b0744c1c00c1c240a100079044035040c0c2e43e105241e10848041010000e0310000300351083c001c00c840d900740a41103403480b031914a000780520030a4010340c4d030340341700d0f00c000921131010704d009881c100e0f11003281c42c03618294008011038400c440c50030113403a00d40d10340b00d411040d0b403628400c0c684482d01 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 776231636 1250 776230386 776230397
    0x3240a0b0a0e0319030f020f061305030712270305060402040905070b0c070317070f110303040302040f02040e071803022103070c32130603021903231504080c0d 70
    0x130249409052200e40203014000c40d40a5502da07500e20000081441e0882d10900c0304442401c11480c0c010702c0d601c1001d01c001d155080700074110a403941c003e4503c0385d40c0c0410f456041244034402c0290100300c0864130000d440340c0c1c003c1c004a03000d0f048c07903030103e148580284140c410103511000c0c00340305940403ca210b040e030783c803821b000c0040c0b06221a00c000e5503000c010410340707081040e0300c40700c00c07007080c40380050100161501d841c001542c007081213a0096034098001c0c480d550413545418029080741c0b0801c0c0c52061304400003641d584c8070f0500d4401c1020f814140d40015400c54007440307680103209088490b5011507d03071034001402c0801c0903080c250311a0042001190500c10050003c80580b126503024407034890040d41001d8400002c4482d50300266100b1200d5900441180081c1c100c50344040c3d0811641140307101000c00038207103d01a24011503101c4071014401e81e10b00311282203441107002a400550900680e0b1080034103d40d04103004200c05030800158211040c01e1030f0030540c0100203d013 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 776232886 1250 776231636 776231683
    0x151e0f080c0301140402222009090c09090c0a0306091103061905060403150f0e0f070605070b01170c030f010c02060c0708040e190504030503240a0b0a0e03 68
    0x1074240034809000008018000130b0b420706a01048402c140d1020000c3e1542600c001c108014210703034401007000c030101c0320781120142d01d03140d600d180c0d81c401240c1e6401000c81c100041c94031102c032011070350800b802074034900040e51824000341340d5402501c000740800d41c84801c005101c19060185106502004506aa6a0034000c040140ca00c00400d09040a40102e410401ca00d0750742d04242d901716034120120955095649181400810380704000214051422801c8502c846e000102407054100c07400466a0a13a118403080e03925004d400c2c0000c0c0300d080300000600a01e03200c511030520404001044600160b42c030000a824450f86c640030700c406039511450b65104550400c1080d8003c41d403400e407145032081940701d80d200c600c2a030103009206d50b54500803558401903c441e034541106c6c82e02d02000103092a2800900741c0d03200381d6500741110904540c039010b402e403400000303017071407002040e4142562800b5035600b1140c0200d01c40e00c050000e01c114004054500b80300001c14040c1c0150341c4070032030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 776234136 1250 776232886 776232889
    0x11070819030c081501090308070c0602100b0a122f15130509040203030c060f1602030a0c0b130b010b0c0111030411061c1506090603151e0f080c 63
    0xc0e1121458481018101241950041d402c6010150816184600c0307420003102038006a170881c072680d0000b0000c1c0c80c0040d00a0078014803203458000d513036181d42075902c0c01d00003015000035034070740b4842c07540e104a06402c100424007080c4460f00e44544144816215045103121004840d2000d2007134a1410f010302c1070b02002071500340c00760548130a0700030f0f200b030814070260303840100c0740910300802d4003c002d10000f06040d07550400c10b0f50884c8500c10300f12a15841c0002d890441c0c2c0e0b10a40310754110382400c0766005110390000c42070f903030780324040e44d1144628500b50700d800c0c0180c1c00150610070f50101c50760307900002c40e1500481c2c501030800c82c00e006030f6800034032000e40d003160f401c0003d00b02d881d00148107000002d2042644030000354002c40b1469201c1420b00006d802c4a980308510355201780ca080ca101c800c494032444c0d020f04407a1130f0f40711450400d9940034107405446624a040100c3e580000040c0720b0460070302042e04d20301c04002e1003a181242c070b51204c4150340d20300b900700c200035502c06c42c07002000303 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 776235386 1250 776234136 776234167
    0x150c030e0a1d060d02150c0d080103031707090b07031d0904050307060531030e0111030a0c0c030b0c1e0f09090702011410060207090b03070b0d110708 66
    0x100d500684078186420301d0210101c00544a00c81014242c1040b02e0218903c0c0daaa50980b4469940080942d04598402c00c01c0c8030080d4070100007400c007030145041c1305100d68068445c0d50304076500b51300c50894014110401c503080c0c060090143c4140508450302140020280002e085c040740309807503403810038481440701c0c2507003048260316a06c0703030303100d1010400003801c0031080c3c4000e1540550701041985603a81b07144015111102444102418078401403943c804c0c0142c03955450303010380c681c0c06a5406410044890030742c11403119081e940200f15040070305110b070500308140c07402030154650b150b460381e64403042c25500341c80d40c450900e000700e264040302c1c1c49081180c005c54100441e0b2480c00c0310024620b010307805900f1120344a80040070004038541e0003034000e88200100e00301c0f040c0c52840c1503801e0000541444c01307250010310800002003064103151041c2100ca04004001f084402c1c80c0441102e49644281302d4140f0290f01d6004122000202c04040d20a9900c1214000e031108402c10140c0c50 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 776236636 1250 776235386 776235407
    0x30c0b04211707030e0409230114011a0f030109020a0f1d221514010801030c12080705011107110603060a06050c01110c2817030a06150c03 61
    0x10240003210250740002c10040c2e50069040091034440c0c3c4030f401500b02600e00b0300951841c036802c14140b4654000700450305642420f188042c0c2041c010082c080f040007401c03103c0482e0042440c0701c801005000d1450305402c1a4070180840700554517008500c1c02e030087c681c0080c0d00c400d07545600400e07440000340d0881904201d00c840d514008040490250003420644001c01c4d4250140c491b00b14075204034513409048d00c4c4007200b400000c0c011003003880b2218200c100d19110750301c258481e0044a00c955803155041c24100c039000a02e1108030b500b8080b001c11380600c034a004442c485010840d10300000d80a0180c41403017040501069110083c070300f4461404907003c03510501c07945040080203016134030086a24159071261800030f4a6a00300106d003801000c104620204010021038602d0003607900148401c1003244000c07056203440c007000400f0062040e6034000400099042d6060100300005001031588a040340c0004900207a4441c00c0c100c80c1c0303148000850001d68009aa074042c107400016100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 776237886 1250 776236636 776236679
    0xf1b160c060c05030f1c0e0f010f0605030a120c0203071223060f06010918061a070305041a040e180607020303070c06090614011d010b160219030c0b04 66
    0x1180382e01d0983e0342da9102d115042c102040040c01058240540c040184220500c80e0100c6003004009501c070801640d405e000d5001c0b860540c00e2110400d00303101103024480444e01d0103001403032070b00781a50b00d501c0000c0040b0004400c102410fa0588003503601003004100a05444201343c04040441c00c015000d08080c82c22091090002e5940800402c00052a568030055280141000d1780302d0500403030381101c17140d01880c1d03a2001c591002501021560003901114615030506404174000d00300c9540307500a55801a0224a0038001080341240e00c0e80f0747d03c044130302100810326164a800303c40030a07260130b03500c191203d5429514010030314002c00809420108a0004509600d042c40004020124040d401440e182c3c440114004000303007030f0000c0c0e8040c00409000a07580d81c58a8407130001c19890799080000c42800000000c0036240d2508a40341c0803513409003101d2161003a000d00c000003c20921001ea0800c1c012070000114205015400107013451b1000795944030b01c1c1c1280200c05648d07580405 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 776239136 1250 776237886 776237897
    0x110a0c05062202011110060f0603050a02030709030b18100e0106090c020304050618030a1101031823030d021224060a0302070206070203120d0b040605030703060e100c02070617040b0f1b160c06 84
    0xc40250b4100c030345432040b01c5d0700c0901300749103554403c00b80756001c030304540d4140a48140c100350580102c50303420542c260784881d0001c014082c0c0d640d20308405d0f6900c4452441c0580c000301300600050034981c004140c50200084181c4083e40c1b818042481c00400f107105035444000310800041310740c0e0601403004407a01c001010781c1246803948480c000f103811602e9942200d101b0200900f0001c10a02c180e8581420b1104d0464540b120500c1c030107004d100c100c1c1c14101d05960f00f0007400c15582200d2041c2001c3c00d000c0e0645080000042c0c040c0e00039400020282d0b0305c01d0040c0440001668100178440da15400605415101c0c1520100c1500f40d84400740d07000d2045007032070418003894038001403180c100e03604854040b40130060661a54101200d00d00e08500c01401c14000100d00c2d500010b100044a45c81c1c0e0340c00000403440c0c8075030030300b004003a50010721034103004001c1107030f19020880582e00301c280e01030380c04004000c084a02070550f1180503030344006141440668113003e00300c2c1a4000400e85c90801303 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 776240386 1250 776239136 776239141
    0x190305060f0a0209131a040920010f0e2b1a0901060e04021c2a0f0503030a1112041e09140f0a110a0c05062202011110060f0603050a0203 60
    0x1400e072250000b50924015038480032007006c0702079a032080500000190081010624a060400c2d8000300300520321441a80001050495446030118142c45d1609076107401c44001c12034200444034178500b00b081001d801140040803403085085214890070302c5400d6a508600e801d0906c0180140020700d0041d00780d14202c0704001d8008080b4071264001d41c126807403510314a55000741300030142000ca005d440132801c8082c904281106003101451881c2840cc40030301c8542c1c9088030201c1d0f46403070055070780540060050f204198094000c0c1004036241d001034410300e00364000b450115402c40c0e48180d1748001e103520029031151108401a01400d1031071802d0000c00710160350640d14110140c00c80820f08200c00000e1032580380e03644403480740c014285000342d03505031b40b00c8010044528a902a00d09000b0040416151050000300244d15035074800b81d00c40015441d001511001d4411107212242d000e030140168080c10035101d000c0180480c885540c00f010f0134101c1c020111f0710700400c40c0d0004c0348100103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 776241636 1250 776240386 776240389
    0xa03140c1305090c0408060c0c16031a060112020c0714060a140d021303030e031c211404030513080303190b060d0e1e0a0b07030b190305060f0a0209 65
    0x812810b859043d644100b55468000070084644100c2e0300c10002030003000140502c3d048150010440651150b00702c48400039661103807162441c0c0e510009100410071021580c0c003082048021b44c0c0001c050600c189121004403041c01642d0280100401c640c2203c282884000c0f0031455508408000784d81103402c08050b0f0b0800b81888101180c04443c1a1001c182049603441035011500c0b4803081b000c02c860840d60300d2034050100c59000f20300600c0390050319400442030020302c2540c94a14660340e1010315401c02d00c01e800a12007580b611a014031900c444000c81c0d112a0400351070701031803080d502e0076950140210034100049041e044591590030401c107200a81c1c1c0180c3c0c0294080c0c4900070005064250800000d40a1090103562541d0505001030205000004600d81421400034441144c1c03248000c0d82d51900c034204070b4001840700241401089403207109501c100c4840d07001603e8060b45800001100d08001c43ca41d2003180c05905c04000c014510341c031045540e802400e440c00070f40c203021140e030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 776242886 1250 776241636 776241667
    0x50310021305061e07050706110c030703080903010f0915050f1b0a110d120b06040528170d030b0a0311010e010513180501080609061506040306020a03140c 68
    0x10400c3c1c420324022464041040019000000311300c440400346680346054a4480d032503440e10b104410100d41a550040c031048000300e12414140f500a01411004e402e540d82c42c3c140f50000c2c81c05542541d40c0e05108403c00310203200c3e140d05035002c3c24220710100388029280059031700080105040c1000907040c0300d070403024101c00c40702e400ca186c180c1c151034011104041f20501c2114140003940d10444c00c11240d43c81e01b14203070041c41110420103101c85100f24091003040d214510503281c00c070804c0070000302100d80d50203900003d10101c00c4c1186050755143d600d00c4405400c0304030342c5071079002141000354580d0188606066070398156075151020f85140c4800e030314131003004042410300441121511813a84510200c82c03894480c0c616100d015a01c2c0c20301103c10322120407085203d82d184c00c00110f00b9000006445204000d0032009041c55516820a039410380e802c081d2490f0020010f00c00400001c0d4503001410002c80103690003d800c001d0329104800c407400c058026086418100114404191041c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 776244136 1250 776242886 776242889
    0xf010e011d06070c060c060f1806050c072108010503011404030827010c020f0304050604051c0210030504020f0d0b1b0706060609030b011e03020d02040906090c0503100213 75
    0x1540d07050445002034000c207007944900e210041803214100c0c0c000c20065000320b0400c42c1640207038020040d01191120304001c440c615030f0025030b102c05c8065990001990340e001240d00070a00d885550500e81290740e007a4200449016000c04204011240b031801a4401c0c038a03401840d00b02d00901840400c40320a02c82c502c0060006010130441d2000190300c011210a1115a0010f80f841d034a054920605002d0081841000c00001400f40004d68001c0c06000800c2d28150ba00c0100060301d01860541041146860503070443c1d00107140e10110005a038a40740b41142c000010388010460386440e00c1001000356400307040500c261884c49000001c10001007a0f19401510142c10129964101c1c1000815000314400185014241040880c80c0c90f8010ba0403c100e074400c01101005980303503090f01202482c04a5803002160809000b00054a000d0b50354108880c0040c0c40021400f1107904c405090340c039882c0d400c2d00d403090000c13010842410100140141c0d00310606045080c1400076440c2491032105 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 776245386 1250 776244136 776244167
    0xd0303020906090a061206170d030e070905040b0a05070305040f1112031306090e1911070f06061701090203031e090d06050610141603030b19050f010e01 67
    0x85480007554a070003088070400d02009141d0400342e580c131900104803c1094001c080403d040400c0007800700c444014510320390300b0b103101030016140115001c8000745041802c00ca01da101e948000910012a0b110361402540600c1480950b440c2410120080d14000380014042500d8502000f001c12034190a8515070340d40700b41ca04082240c2040080c51413800b50303c410b4020300000408001031400030790720200b08c070300b00d448515115503200c9114424034000c03945a9541c1e5840641401c01080c1e5038046808070b6071501c07940d42820929112000c0d0385455030003c5a19507500c0505020311900c04208429200c00d80700288000f08030399021a44034020102e200c001040c8800c11035111000c02001d1300c01117000640345805031800c0b400d11002425041d02ca0070700842c10f000c900441d851081c212a43c4103032050a14074602030100400c0c04400c00303010020b4040503990a1078091990311003036400b44401c07026504401807414081040545501003c41c6814001d2012003d40180d0704082c121039502038 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 776246636 1250 776245386 776245391
    0xc0a14040e07091812141209120301080f100614091008010c08070305011203051c0f02130f0e151509030106061d01020724050d02030f0615090d0303 65
    0x7900000303519004182d04010340c42410301c0300345000705490540c500c4901d07015001070510002d44801c151030944035078624020380d002c20421201044500e607402c60b00039a219089882c0c6600d000da00c103150390400c4c1c0044149811100f420590f004040164510708031200008104e05403034485403014142e181e4910501610401d000940111708180c3c005000f404100c000b484100c60002d0000c00d40300d03003212010042440c00d0000303c1d48075039460f030380841e42c1da00d134031780030720f01082d2100000c20821050410040309403038880d444e815903124005404401840482080712a04210b0901d14030315a603041440c144069a08000a03e000d0807903400c1700180030341e070b01848240301c00da441d00c040c4107403600180c02d5030034500c00041056000c070059000410801346c000b03440380103400480e1511103500c00c0d40d0408078089030100140051b04940388500c2120b0038914503108c500107942c0142d80080f201c1180c681c00e00c1e820000203040c4a0480542807000d08401c1d403512a8410015041c0c040c52000a400c00d035 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 776247886 1250 776246636 776246651
    0x2061014010e06030a090c230402031519090b0411071101021e0721050d030506010c06050406021206030d020607050904090b042001020703200604170105010303020c0a1404 75
    0x90003080d0105060001803c070681d41d1421207600300140a1650381120f10540710000010040304480d01c00755460f01210707044000916510030800a504050541180300c1c11125050300c0540d5882d00d40448030340301d09020710f619072030802484102c500c4c0301c0e00d6900450800d01d505109400c400304407052a64454582242c4142510040345009500c0c0380000d412100303a5814800d1740000207140c1c2c00c83c1d02c90068005005a0325640c810400d60000005080c1c0e441100c000c0b8480c0e010350403041d40540180341c0b1058501341601c030f0b5800d5030703019075050322a6513000865503607000400620b694801d0060f802803648001a201c004d6903404d0042600d0100b041c0424207041c0d668030f03504100f104c42e42010301443c0d1803c0a00342860b1240a0b40d581c0b140160442003582007550000c2072243c200c0b50080c00302e5600302d40200b07098039100003100361907a001d8070070000814040c0e000a0f08040d01c2a060000142039815454003030302c0c0400c3c0303c05d454443e520299003080304145520380006c101005980104601 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 776249136 1250 776247886 776247889
    0x515070501020408061e07320d1805060c0406090e0c070215220810020711280605121311093d060c050f060705070303050702061014 58
    0x24011908038000c42c2c007801050008034686d09a1403260024000c2c0305034201c2d19000410350310700107229070344410040e07400c03400301b8110640c3c812154000000c0381e03000d10702518165031104845401c0388107042050000e0081c010311408100e2180d0002c0c42e41406484c0a0801002421040d05442402c98050840c00022407603100c03802500d00c0c1a5001e0125134110041c0018400c4c0703608403c0740386503414800c0347ca03d0091170700041c84d14100c4130380e9000350180302d0104e0000760107948424010b90381741a0403600550035488201c0424802003201c405035424108850040140c0012942b200081100501c45e44d04801c03000e030b11094100c00b810003405507680491a10031a070326000d44210790b0142121040201229000d00458078054480344032594029001503019210000c00419114246400300305000440c0181d201e0174031640a14100d40c5021841560f0743c0c40c0580403071b0488005200400c0d400101a018001d503500320342c1600140c07403285058403000120080d00d108003121a903148a841029 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 776250386 1250 776249136 776249141
    0x3030715090b040b072d0c06060b07060b030d11030909130f05030c0d02010e0613170d02120601050703080c0d0204032019030c1a09060307110c04060515070501 70
    0x1c5561004110380c440c90681000039240408484290201d000c501001c908144681d0708907040c220000c040300300e40700f86c40004484030602210115011603460b100440c9500c01c0c44090528244219008079100c0840820300d8180b4000150341e41c1803080c018441901d0b0400802541d0200c00c00f5201049154bca001c140741032041c0310f5902400c2050401500824000040000c240c044403d0b001c541142c040751500328200c610050581c0000e4000780c000c00d0041ea10ba2001d07203195030003442404148021080040070360f60085042c00003540d400100140740c1010344c0c86066001800b400c1240c1006110b4030041c0107000028a00b8460300c00c0060041580f80780c41d03058502854000c140c6088604000d00c1401403085143c1603988503004036800b881c100c241811070001900e621030b00c090000c80c544000030700400042c40310300a40d100140001142500e84001541c41036045c0c2d03427070750440c041c0d504015007401c1440f1203440c02141022030920450300c60811229278142d00801c9151340340e0080c10403900 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 776251636 1250 776250386 776250401
    0x609030309230606060c0703230d03020d06050f100327050f0f0d050f07030302040902070302160801021905030c04080627060613090c03120c14070503030715 69
    0x3000c084a8030800c102140110041418800c070303046850f02e84900342041098020482d03100710035881444103000103a500c1032620369500c1181003c2ea01801ca0405036400c2159048414001036400328840f415100c03c0e00420340204030584a100000030f504020072103085002072030105040e00c4400010403101c01245481d000303654405070700c00c0c10000340780c03068880e074000c40703854032034130502c8400c43c82c01d1000310700503002034070903102c0718904201001440700581180c4819810306500748400a907082d11400100720386032081e4058242c035444000c18000a41658104443d02e030700c18040e216034003116000280001d02d580c10000e03103a980303902d00b50040c2c0c0f00e2904800c0d481c2c001c080500c01c104141e10500500c3c40c01c140b025020385601448515901c034000c0341c4c42c40c1e201181000100c03410366158042000e550242d000c8401090322503d0358030003020314070f041d14001240055600c0501c50b803940c0303a49100840360040c000e00ca141000080d80c0b400740001c00f4040403030680000200c4c01d510352026a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 776252886 1250 776251636 776251643
    0x307021e030613050d440c070201091a03070f050f04030c050111010c1b060b03010c031e0506010f1101020712091404020702060708091329180720070f03020f03030f03040609030309 79
    0x1c46c0c9140806c1c260441d41c00601040303000c201010008a4242041581309200c2d0340900c111034110f039100842100c048500e07950036000e0242c10407075031000c099000010009580140204548585010b000401c0311541d28440070321039142005a070010390b40b101d6282d14a421454941e40006501d0401c00c000302540c142c026410340c0383c4070784180c0c8941c154002c480110075026000c3c038080107501001c001e0311021100c0c180003035140740c3ea803040140030340c048481e422100c500041c10021503503a4180c03c200b0001c11040850f0341681d00700040c40410b481c1480b0070406440c15030510080e0b074089005402410001851800c0c0460240140e40711481451005007107540d085c400d000c464400c04001903490740c1d010b01c0d450f403007071004182c1f410301c80e0b18100108010384940340307203607036191301210104001d020107a11000c40101145072150208040400740c040c0408040720703589036104000c440c14401c40c030030b400f036042071040f001c84070103000591380d0158220704041740300c01c0b10307150881c000d12030140d009 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 776254136 1250 776252886 776253017
    0x504090501063201230a08010503061f1203180e010e010909030c0209040c091508070905071d010c1703060a0f080307021e030613050d 59
    0x2105004054101c40111200e000c03950703c42580c8010b40545a0360f001811264580802e140000c05501c52a0120035800b060a0815114902c400041203154044000000010145001801586001d001031500280c080c2e0703100030701140d000c000b43c0c0300b08550f12400d6180c0c440003911105040c000c225580c0380d04800840740e54107648405003410a030340d0a00a0403888000d501c00440d1415042c464402e401d9056110b4940c48034040d8204911a40d000304105c2c1d0810f2030f4400020105024043d0340b1045541480c5246100d00b4862403510b014402d50182c999242004140800c40c0d421021402000e05c1c41031f51a030b01582c4900042e601d80c6604080103010308021448501c811040d0340c09140103c404444c402d0301c0ca0703503a00c860b00c694041c1e0300840c103031900700b0080c2c90b0061a10320800c940b29000c0c0d00c440e044814066001130b00300601103960030003090710540217808016040c082840c50111a041c00c040c441c07800e540c940395a06041410311751052944540401080e1541000300303012501d400c04 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 776255386 1250 776254136 776254151
    0x4050708150702010516051206040f05010611060928170307050414091605160206040828080301030204020304051609020d06051c08090a18060302100816030e070504 72
    0x81d161103501203039098015440c05004c44c0d840c0c07144502d821440c141659030a810800301060003000e1400180199074407543ea005040070842d0a406042d000380b4107900c401e000c480b10612201d0030310f00014008102600301c400f840c07100c0704948400d40a50400e0b03090005c0a60603e191075000415003101ca00204a404130400000540c014001d005aa982d50718040003200030b0014015400c0f4180e403200102c064041e03040b03030214800d0002d00000042c4c0701f012500d0648540200c2c1c0182c0c41070700300c60a1a000b074a11640400b05000c200c0e0080f42c80300c3c503044c0034a0116155030000d0b002c1800028440d640000110f000e002c0c0401c50280310068840b4181c0c1c0b5159540c50800003503010707152012606040402c0022541f40104011051a140607240c40e40340350955540e1100e540a4a141c43c0c1c400708504000c601842607a20702550300440c0f550008155044d8010803002e503c252503030030104080c070010080302c0802c01003500c00100c40b900780414540004a021410103010b0b030080c540140c9000c50 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 776256636 1250 776255386 776255413
    0x4080318031303140307030206010611010603021c06060806160807271806050f190f090f0506090402060909061c150510030f0f05070308040b18010203030907060804050708 75
    0x18418101c034840c0644d50564011084034907200d005401024000d03803c55001006424050b003005018030b520423000081e0030b41c9a600040c00e41400c210244081c420000c01c02041043c0c6114103000380007440b00a2080f441c2c10342000040b000304240100c1040300e5030340071600c00c4d8060544000c200328a1032071070070942d880c0080148bc2000910490b010191208180c0c580400c1c1441400c041c0c840c090500030002c03208038240440c2040000000f01080c261010005240f088011054090042100049245684091203006039000a85010b126a00c41d1080c000140d50344012540c1006046c2c404006540d600e4002030045442c00041d40302c0d41d16070750044810011101c0c22468905840c4504005548940c04054900c142a0200900d14255903415001180364404c500d0020340c130030340445080039244e90700c01c0116005980415000b035008145c40070200c0320700e0401d0500340720030300c0114118a030205a0a917201c0d024131540c010b1051b00e07804202402401e121510143c24410200c03066010941c8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 776257886 1250 776256636 776256667
    0x11130b070b06121509070f08160b0909010513110a0c0c0e090607110c0301090c09050f040201080115050d023c040b0a031503060b03100e060408031803 66
    0x1100c2400c505400a401403800071880101150540000c0202c044805011500180003420305c0070148504400000e186844904a401a145a034003421034200c408c0c10602d02829241c100c02c5a0040030301c1000142d0b200e1180150450344101c401c628403190078102c0900811a02c18003021404000452282c1981c001901c800324178841e54111000955400202c65020410b880000c25a0081d50120301d20b288a04600003080c40d0403819603600b14074190002b030231543c0c1c00300102e424131603110040040595900c241c2c3c1d880b40020704000e80500d05540001c01c10b9505000d201c08500340144403080f10362190040d0740807494100e0045660b00f030301070b45032420180d8802401ea110041821885111032070081f6502190441c041e02034103090070040c1c0242e00e0340000d102d540425176140e4a4003494003039002498004c60007075000007100314540c0306160515400d03201c16254141001d204c030030032920000340c0d15070180e00405140d46980b100713100901000e0b250b40b007410440c8008500001ca1040c103d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 776258992 1106 776257886 776257897
    0xb0403030c2007141903260a090b0c03040305030301030c1e0303021c1707030614031b090403140712020106210f052103011518030611130b 61
    0x11241c15950442070381c429200e50b40c0000320a22039203440c0d47c3d101c07640d0080700440342c900003100e00050b20f01f082c540b203103140000700040c600225071800e0096501441c2c0c07100a0301d80e00c1d43d60b401d10780003100490003a401005100b802c003140c0d14918888110489a245d00940355200980c046142c0140d40070341460240318a0a8150b0110280a103480388980101d48001a0090138036016a801801c12100140260300000140015001c000860990030008032a040600d03035982c5801c46d84c0400070301c14440314104c003184a034100242c41361000034051407a130080040342d90307845c0d07031842801e03811601b11207181040d80c3c0d80010030a21315144030002d018808643e0146032480f40302c0001d91950804034201c180200051080328002078082c0c50403000362900c0c4280c4411540d511030307540500d00c4000c199907a680280d0802d40d0304101918104200302c1d040382c0c2230720768540324441603a005 = true := by decide +kernel

theorem cover : BRFrame.Cov 776079136 776258992 := by
  have h0 := BRFrame.cov_init 776079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 776079136 ≤ n) (h2 : n < 776258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
