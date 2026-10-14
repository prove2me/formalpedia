-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0759
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:37:35.980045+00:00
-- url     : https://prove2.me/submissions/cc9c6c29-747f-4f34-aa23-4280f2db9998

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 136330935 ≤ n < 136510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 136332185 1250 136330935 136330937
    0x30102030f040b040c0305010c020304180c05030c1c0c05090f030601030203031606020904020c0d1107050d02040e01091202010c020f0f070611071502010207060609140610020a06020408061006 84
    0x1002045072a0300686032580d04207074020000f50a5564034101000c116649400041c015400c214501c281c99034004042c1081e20720303810b90290403842d4500701904075240301e000140411070900c0010341e9406050054028000d00043e0f0b4911201c4510504044801201d00540405c40c0498202e4490034100240041c11000341c000b040c855045400207941c0380503c120005014503041400c9007084041e03015030b07285a20140066448244210001d41c4402c144448000007601d00c0110403004a000904a022590003174984c1100044036000d11000c1c0c00c0504a210700e9640302c8008400287c0c04000184514085a00001e1950401c0300e00034202980002d142001c1e030302040106e40d282c40c001c5110412030340241405c180d440300f00501d07a070402e8519030140660031054800041201d4064004040051252204219058517958403d0450315036540321081111481e000a10b641419060b0040309903647c0121040500c2c5940c92105903400303908100740380c0e0460001d1002e00600c180b283c0015084c5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 136333435 1250 136332185 136332187
    0xc02070e010801020703020c040b010e0d0b0402240a03090c0b0310051504081002070501060f060305100e04110907090f090b0a0806070518060d0e34050108041b030f060b030102 77
    0x5c0d44000790384075281c1c0035103882195101d00203401d50780a4038000b905010058250b00705021242040d540e4104e007142c2c1030b0f020707100001c0c540d0704000004502048040b003040c14113007001000c0344201c5c01004806004c54075440301c5107010901c86000070145114034022800440307201d007002c09003c5100c03035403030a4881c5844148400c1c4014800030601c01640541d0301401038942c0c0840c1030503405000558040d035062515003c020032080e5050304014400d040c0c5201003a82e207581c40407a80e040000031500508038101174125000b00d0700d0100381c45504040c0915100c01000c1d200d18000742c1802999000341842541c4d0f0014403c1400e001d442c0900a00003e0042c0070685030035080580180f0400050280700b5030313405003001c09a9564825a0044408064100030391540c900c2159a210b460b1043c1136142502c044144814201e0144e80f8200414414100b944c0036207030a005583c0c10310050301c00c554940300d8500c150b118820f4510072900950003190003030400140f40c20a41c080310700302d426850003a40 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 136334685 1250 136333435 136333447
    0xf02041401031128030c02070f06080a060b04080a110901030f0206030a0e0d0f020c0307081f09020414060118030b060105160b2503090506150102100c02070e01080102 73
    0x51800303800100d1000382808284164004000210f51140da445900c002441e240304510b1030480f41036040405002d42c808028403040b501041e40c1c0c4900300d21072a900d81c04500d00c280400b41c490003c0da5007000070b01c900421582d0b00c1d1212208150095003099001c0c0e444501000306100ea0504204a960816a10541154116141c5001d071700855940031303002e00c50020100c0c103459015406180501082000d507085a030301d010005100001070310107c070040c03080040c80301c90340c6400f00b0721408403002d81004001110b40d01118010072240380c070701113003165500c921410160702c3d9030007000482d5601005d01c42c020700c3c09000252150000039072141d100900100c0034800185c031408529001203003400d02a86403103140180030398440d130060000388102030080c2404004205090003441100016031081c01c4202040421402c480c1c40b0381d0b010b0580c1e0301450100f500483c460b80d41c60640321062040e41c640c1f00c141902981503d00d80304251005a01c02d1000f0410142c40e940c4003800740400400a600d020 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 136335935 1250 136334685 136334699
    0x7021204050f01030b0d0c0609090e0c0922080d0c140301061403040c171f02120a0917030c0307030f0e03030402010e0a1a03011403070f060f03200705010f0204 70
    0x24030b1440340c14140360383c3d02041c0040f81e0381c407400c0202c40c80e0320484103c1401e440d0035008150b180c45204900c8503e044c0070300c10007100f4000c03c8240c004200030f0000006640d603000048002c00800d010714a00781304403c084030109444200403d00310610520110b200900048014003550101da24910800424001440b900b68450121404d02240c150b00503140d48032410300600703c2c0000d511002c0031000c54010f48003021004903050384417443c1c450404041e8400c00d242241a440740c060b41d0180719034828000b4110b00580c0c0d0010071070601802c201088403142d6499080a5441a203290f0040500401040980c0b50f050080841721010720b0004d2040002d4200519a80d020180009060055100850b031180d12500420001030480d41e014400a8040c082100c01d994001c0c001d0700c4071403000644100701c50030005415812101c0c02540440010700d0203804a81040c1c0c5001c45004040d00c612800c000b080c81a58010301d28184010059070380c808502d01142140e602c0e0a095040b03d006200420404c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 136337185 1250 136335935 136335949
    0x904050703060e120a120b0a05010504031b05030a081207050f0703030f150f0602070b030105030601030f050a0206030a050610020d14090406090c0f08010902040b040302040c03140c030702120405 85
    0x1294400400f0a00040320341406050403840e55161641403c04100312030500c2d800b0b031510050700c0c1c1d00241045030940d18400d102d00b030b00b014010540070400800003040040c1000720f204038001c00e020750304044507840e01e00013400c2845c12501603422080101c0e0355030030340455804281d0031407141d0800340d19185501d4420f240300d0140c0704029050540e600c07074a0b00d200e2016008940d608000107a91144141c071540712115460742d41c050070005210342c00b8081401460715049906842004000b02440d070701e1940d800041c1d07229440111854002d00890300d005807604000345000d092a818041032604d0842d0034052208031000081e000c550010714400f522030b40201c03d0720910100480d099a856400c50301107000f07440b40f90700211400780340914203100142c0c0b1140c000e45043c650790f1a011166a542c400c502603000318098100c007950200820001403819902c04440c041d42801c02050350401010300f9450650200c0e560404840008100800a581030145003105080d001780d044c00e05003004041052 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 136338435 1250 136337185 136337189
    0x1110030b0d0f0f12120c0903021e01090b03010312110105100608090c0303030901020c010b100509040f09050d02070303030e0721031e120f0507020c190b070b0f0609040507 75
    0x40005502d082c2d40c1400070100040c9005034000e0f410302c01c203000070380c1c004003402c42d180c0500c02407078600380801c140d41d4130a0110508481d0024a0345280b12000b042c0e0f2010b400c0294541414409906000a84101c101c00554029401060381d01c010165011018240c4c0601405002031649400c04100c16060085a403a00385c56582c83c1140065860200e11403900d83c08098480e403600c008400c0000d00d5a054000300060141e00c0c000b03001c1c07031409106109000c1000707461040810310600484030281410752090700304040002c00884d0500454276220b06140c5021008401a000b442050041c0354050143c445a4400741d00103240c0245020b8003200441400b60114156002a11032881410310499800070b0811041001c103d00e5443c441d405420501e8440002910074241404044001528414940b043c455034014141c810408010070200c1003504c01c201e80009101000454a00c0226016203901d6100342d500d220641890080448221001440795110301c03041400c22000400100303070001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 136339685 1250 136338435 136338443
    0x5010906050d0b04020301020c010e07091103130b1f08060901111801210c0c030801050d031218060e010911100c020111071e0302100914011103161110030b0d 69
    0x181d144c610019005e841910380760303c0f1035820700074a44a140c0c80460702608a0307d9144003000710030200d8842101c113000403540440d10b03a10240030348000c03440d1604815807012000305035410116034040341055040458108000f940c1c4084104002290244100c02c01c00d400702a0b00e506107103071025010004138006441d2410410441040540c0030700500304000c2c0740d81218002c0c000e1851000005040303549a50307041e40080e41c0840000b40b181130031a428001a42c25903110400e07424020714584c0641304011104150329041c5900f1008603405115000c2e107000c05c0390011451504500304900c866000700d10351440b889950303071058803950700110901200ca40c21309010004129100d180f60500700180e00507124030041070400300300c00c004d1421400569108860300041000b0009003107804089a005050510b02143c15248596000b001e142c0b4107011080110b0340b922558407106460010045000c45244000c201d0b5107119192040141c1501299407804000f114118000210f94000d0110040c0c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 136340935 1250 136339685 136339703
    0xc030c040b040609090b06011e020604060b0d140102031b0906070b0601051204050102030414011a060d021b160608070503040b10080d020a0506011406030402060c010b090c07020405010906050d 84
    0x810107807541d411110041180c8601003040c0c0d0317100e0800d0407402004680c02400a070425541031011600c0301c00c04031544034190b00528842e40c4580d191002806401c03c0641d02c260b054030b414ac00076001c05000084103581c040003603200d0070212a04281440c8460a50000d0074080c00551040d84945080e08e01d002c0e04440454520784540c401601c046c8141900d5480c803c440d002004103018054000b1030040d8854200d2066051650483c0c0e8200e6031034107041410040405405c100e646031110107881001001c80c1c5c010b140c20f101440b40e0100360b0020f6020b4001d5000004009011141c1000000041074207040044440c030f05135500034014400248000c1450301c0c030a001c00c0047d5031800d0040f015028003400c449003040c1080000c0d42c0d98030f80c1c03101100c041c868000081032070048a0b03900048000701420890858449600304040f81d00445410612596921700b855070716515500310310b00580d103050130303982d50714414014001a900140c1103101258180311040103592244541044000d401540b11 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 136342185 1250 136340935 136340951
    0x14030a050601050403080a08060f0f030a0201030518100b0306011505190203040f0305031e160807050c0a06120c091a090f0603070e0406290a0207120f050c030c030c04 73
    0x141e40c180240d40000d8090391b408500030601e0ba8028140b140252000c60340c0d2103186000d40104000c0f011985a86a01a00305140c0b600055000760003850300318011208601d1301303c43d20701199250640c161355545003d921000b844a5070b04040c0710050161190071410000c0b00284003000c0c1c010301c00c900c40622a00e55400d0703c0c080d12071081c02550081c005c1d4221200e840c41c0d0702d041c01030756a0403911840c542d080d50504c04440740001130f8111140000c0d4500d54102c010000d0701c400400d904600c0c0e054031036018403547d08400c1e40d50505450007a00042c1c840c2c50078040c8100128089485507030410040c080089801d00907110005441e1a1140c401e81400381c1d5a0703001e002041451520f00d40f0203400080c0801400160350b005544d000c20407c0a6a0401c0070f15070320501540f01410885a00040d40c246690007405450340700010418106140122005951f403444200102c816400b8146c1d152820a80c50b541000020701c020002c01c4411030051a00c991560002134172518420b44031071203180e4440e22 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 136343435 1250 136342185 136342187
    0x1203020304030206070b0a0b03011505060d0b120105160c02010813050a120806191a030402030a0816060e0a110405091501260307030e040207060f05070c0b0714030a050601 75
    0x2100e000e190b01030401d6480d1100740c542000501800d07242c0b1032612341000881310303403400c0c1480351200c0098152002d01da01e070714003c1403080369402850840641034584146020700d031108a01a040200c056000140c1e40c1b418250802d0440c95900710700c0c0c20001030480c0040542e074800041d0f504407506854694903182240382092518206200040420f0f21000d000c134080c075045568240b1450f016920300100846444000c0120000c9006029000c4900d000800751914004043c55100b44042d0407280e0901d0756407240c049a8014601f01440702845030303520300810400e80070300c0740d83c0258030000380950381036076940801c8120403480890045a0394000100b1400b0200150490482460700c160709a5844200c4100c4000e25819038601e00018610401401d010000840b601075416565122040c0000c00c200006540040d4040e0b0700f00743c03101c148540c0079409110751400b4941e152038605d0000480e2801e4094218024104801d001413122401e80340303880b1804a076800700d4180310010380c9a4403100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 136344685 1250 136343435 136343437
    0x611060601031a040513021201060b12090102070507090501030204110a0203180109050a12050f03091c030c150b09010501110307080702030a0803040f051c050a030b010e060d0f050c031012030203 85
    0x10f0140c0d119060805000b50164030079500810305000340d8194104081c1c1024450a07140c040c800c0c44000d54041203546249034080b4021900101c9080001d45810f2a035143e141c41c0a0164000700c04070ba40d02d00041003149020b100b9050103010180d000c5050a10f40318000e9282e0060f503018459198216003200d21130313071140400001030880200b0480e081030300d400390405410140941210180300d00007010b0b180703601c000162081c0003070080054840c039000e0740c8903001e207000e580c000314140418010b00c03000040c4031440c4907804071040701001455070300b0b040400404490603400071341403104269081c0f08400300031003110240341c0c102e904140e8403030031803003c640b404024000103403242c00084140000c00400348000c441c0a40180200c44000103141441d448031820b440c40800480c80402015503841d0003500000200c040504046403074580c0d03100440c1c142e0303003d603690360382d0340e56508581c0221405a2140c2a005840c840c0418210f15140b02d1800c41400d06005281484a6030b150074010584204 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 136345935 1250 136344685 136344731
    0xc03120708130504050a090b0a020408060117070e070c1109010303080a18050f030c0d030506030c09070314010b0c070b12040f15020d140115020a110111071202010207061106060103 79
    0x1404c01c100c82c0c5090240a030082a0112003100c0211240022a4022002d4020354041d00d851201800c040d910300b2061428a240842000580e400b40c0180010000044030f00d40f80714006684584409035403c3c5403689403c9260318045225074201c500500100e41d001c04601e40c05503c41340c000a2224190304850910a02964010007a1050141e210594000071000e80a03e100c00001c032446039004070415001e82d113040302d400d038150740b040038858a18902f01040c2d82e00203030365040000340c000350011320881e5030074243c00c52801e44000180500307001a04122a000034140200310b0783c2403d54541183b8066000500007419600001c003003402070180b81041e150303401d00c11034401c43d0b031603a0003486500581440d207541f5000e0820440005201a403202006400503510750240c6500d2205a45d44000d804036561001c0c10800b215600070100b8800b000444081d01c158061200d0f10304941c4002450a90b050b00700f14100400583c034500014000a0750175002202402c02091150001014071030007a031704 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 136347185 1250 136345935 136345939
    0xd022101080d0e090f0a0209220f141b090a031b0305100c051b010216030305240d060507110f0105010905160c15020f0d0c020111031509090309030f0f0c031207081305 73
    0x11300790503c0007131018ad10a03c404e001c0800e080c8040501c2100b86880300004842544100003030003401c1c4203080564004110805c00180640100c07511f980304c190350006002424212016a020140203014003005003c102810841060024081d1000c2c01480ca010390204d081100f4200502003007072071002e405035610b0b2401086420300440d11814001c1c080c05054486445564000241c258800203c140b035070340c904005480f020030980b030365841d04010200202900d082203028a4804004101400301d9080c00070f0320400480c05504100110040750805042e0ba030184001100c003400044d04601c01442040c1c103d00008078010804061801074815401c0d0619500d10004080200458643c004c4400c014035900030409440706111800c41d5100a8914006400f112116008113142010040c2e5010b0a46030075a42400c4246010a01e07086a060f8101d00740e810400010440d500c0c10803890404100031001800d924041c0142c0410354030800d0743c05000c5c0340000a59002c6040b01001010040c200 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 136348435 1250 136347185 136347229
    0x90f070207210516061206050603180f010e0a0203010e0705010e1e061603080603011103010b07080f13060f0e060706050c160302030301051e060d022101080d0e090f0a0209 75
    0x1404d6014207034030142e014210108507509040421003d00d8800e003015600c000c3c0c070092450711b4006d0703050710803004984405910710410110201f071001c2805945140c0c00c0b01c200400103040648109403c0d200c0c0c401d4a99004da004910810943c1e9204101503040310003641e01012102c1040a086544a10503101d207410600008a002000b01e030341540442d014043c1d0340300c4200da2280810942170316900d400c0f49032000410b00060010861040082021512513003090340f410b08039075055022038004900c207124000740c9000401102d500031016a040007200d00d400801c4088010010700540600f00001d41032903551400608500094002c840c02984131401c403002c9009a490001d559038000d0250314041c2c10b100c030840069402c840b2525030344000080186040488960094000b500b0520060701c4150340b6415041c050500501c005006c1d145e90b5000e44200780c080540549004103002d83c1034016080e403402c00c0954010100542d400c11020040075a5a45141000458101c20b2100700030480035 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 136349685 1250 136348435 136348453
    0x4030f030908011406040c08060904110307120b0a0c091508100e0f010312020a0206071e021201020315100206070e1201020d0e12071208100e04030509090f0702072105 73
    0x11380000ca032041004035401e02014144d1582181e1820003036070760030740114001000c07600142c4e5008003800140800707030460304610703076448600e4030645a01506075103a00d801001e0102290345401000146c0390309080c03c0758800c0c07070714441502c540031205031102000f01c00341c040b036400b23f030414034600100104940710b08a820003521302e00d1400b0081c401151610000b0085006480c004600c8004060f001070120b4101022030702c031840b09404541c1d0030f58102e031884110400507510a030440201c11884000140c403403410404c8072021710b02c10800c151161000d03441e608003c0da40002e809078410a60300d040403040c030904000c62000622405ca402d40c550011500496800540d401014001040404c440ca400142d805410b201e214115001d001d0241000740448a10301940407190080c141e1404c680c1203a9988080300718514050710304400141e800030328070708549490b101c07064114021b01c6100e080c03130078200c00107076039842148503004103680b001038a000c0c1090055050398007103030080c0a07226258 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 136350935 1250 136349685 136349711
    0x4020301141f06030c02031b010b0306010f090501140d060b0a03050105161b0f03080c04080115082b0c0201020319020f0f03030106080712090f201504030f03090801 72
    0x8100790201070001c29840c000040c0f02c6109000300410341c0d105802440c0383c00d00295503004408480d080150183d0340315281119541c070100000f80c02009408204101103082c010844103940045e403200004800807020000e8555842100340c0d00720b507100e040060090710b1080860880c0c5026840580315510f444208148011040c05140340d02540d56122440000b82c2d10380040401002a805031192140c41304507000a400ba4403015042248a00c503282000d648600d03607402d440c1101c084141803000701008003c0c18004119040c03002600c81e918040709c3d60a101f02c280c0a5040c400007200300300c85101c0300c4040d64003c0c0308803100c544c2116242c007002e444040e4041d60314078200488002e1807084088130102220048241c0741601c181c1c1c0c0c0c80045940355444102c400a50740c09108100c0c656503814840000c60f40021101228891250b5217243c4101c00c901c04494416040114000c0104c180d02401001c280003c03103054951008010900d012141012074910146800c107080035807809104003410 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 136352185 1250 136350935 136350961
    0x2030d0305061002060c0f07020a030f0c030c080a03022509020301080c10020a080316051605010f0605031219180b04080115080d0c051014040c05270402030114 70
    0x1100251034400f0041420a0100d0744c8240c121000503070007030b090145220f01c1900100902880780000c01450010ba102d0b2035807510404540d5045039004000d09040081107440e650000c001d0842d071000d014000007940b030113916a5102041c1c201c0b80a020300c1052500d84ca0345a4840c0906001e01d4215201d41c0c64034180d9546400c86240e140c850000c070307582030710000d10005203401481e5201c1d124274115166440c80e003542800140803c4188881030201c04103190340d01406003000350065001050310400680701d6805c03100c5540056001c0c2d0401d45090000b0b070400c60444120b18408030314461502a4030704111807100448200c404004c40c0aa0005200c001e01c8015200759031000008204011401c440e030341c0f00702c180740304410058001d0040160000c3c081c5100d4000385021300c003540c1c940e182090b06403003180d104210010303082c2c801200384400e101d507000841e005414142d402800c40340700f074042d03d210380682d03a808070305207048032002130119102034110300340f4003441d40040071407410b141078400c43c1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 136353435 1250 136352185 136352191
    0x1020f0c0709060816090b0d060504031706030304121b0b1b01180c0303050a1103030907030c150e060f0c0304031a0f0403080606090f030a050c010206100f12060902030d0305 76
    0x9079060440210300c8a0340400c202010511317070000392000b9440c01c50b8038000750002c025000d9010b010761903410701242190040c0c2c1c1c400c91095540100b03200c540c1001d01065880900120301a91040c0070900412020b03210808041e034010382403800419903003452240d41d0362150481100041c02042c4841c0d00d100314001000c07148507400090098600b80ca040d1012865014009014038880050420101e8020fa0050049181515010028480c04509145145e000351000c4e0b80d07a600c441410424030a000c600d44001e8041c4507a0a00d03c920041402450082010728252045c1e800080240c503010965046072020324020041c0c1e5103444c0d50f410200a1007000a030b8400b00e20030f0010019820030b445019143c410355154a48000395140c001c188034040d000b8042140d0000c1e941425a45e00d0744e0100181c0c540c240c0305000500480810600090a09201a02024000215910510000b1003090300300081c3c401009007240c0d00c108900b0321002034007403420040e4040c020741d6144101680c0c15005070348 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 136354685 1250 136353435 136353449
    0x20307121a0f06060403140124050414060303030103062d0c08090a02100e060c03030103060207060b01020d0e090402011e02060105040b1002060a180b090a02040f050f0f0901020f0c07 80
    0x41d142d46014202020030000c03070300c2551141d01000180002445003070303d008100615400002c16110102c803c05507000402c10892145199203004c101d6890b080c02598500c2c4841460555503007400e001090383c034003040c040280142d8580540c1100e20f08060b0b02e0402158041100c0d0201c02c1c9140035800041080b001d503036000412100000d80c080a000a40307503c3c0781d5024140041a2000040450720714000000301d41d48958204001d4406030400c00c061406140180030069403241e003450240c0403a01c5502009055400c601a810300c01034020300c84400401d010b40340540d10f03544502c012900c0141107100c41c4080c00b20307180300580d450b034005584c905803641036808201100c0d4400c00c110980c640143c41c100160321a2002850801090300701642500480d10740b841070601c44d43d50581c502e08108c84410701c541c40740111500b03529003400340240d0f494103032f142000b541c100f1010b04641071000a100d07035041050800890b0b401002503044440070218000b0f055221071102c031030306489000d6841000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 136355935 1250 136354685 136354733
    0x160213051b0c0d18051e040510080304030b060d08030103050604021203040b0d0207080c0304030b0a05010e060f010807020a050601180614010507170409050c0301080105090d021902030712 82
    0xe40c0508a07104481480e481107000303201010320668100c0348a4940200d22000810120380090140c84a560400403941c0c420300160308501410280412114020484a583c5403010030400402708007100322400d070f941010404149503030b50408681129202c42004000700ea0020000052010104442d40a82c0c42210b85001d41040e021500e42e50303001d0303800780c1031055070200254500c1c5445030b0b0083c0641c911075036900d4180340b0800c2c07001d070440d0060b60050724030071500750411103410200c1c07103500d0240c020182008100d00b45440858850420001011305000d04200421007071802041801c103001d601c14102c0b22130b980c548100262082c034820410b010305090510100e01100c440d01704049500d41a0f40701c500f0032886841c0d101c405c0c100c0c1c1c4030380c2e80c41c3c100400c40403e800c1d00c113000e0035200320900b00819a4035403610f048282103d00c0141061403d03000010303012211175000c16a2445080401480c210803002c1d0b00009040c4082a849080490050b0301c10900300030344000c040080b406002c800c5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 136357185 1250 136355935 136355971
    0x2010b0d0605041e21020a050102040b2d0315120a14010b0f0d0209061912140f0c0f180114010e0a06020706080406020405030a060e060c090105030c16021305 69
    0x100340d1900c4c80c401c0003042591303241c0100e08440400260039a15246500c1200c0782920741c4c1c1c99190880e80250854005040002210f10020ba0f4500380307000c041c9044103105910221200640c0807500001e80724400c44c8052400c3d0110039640e142c9040411a035141c2036070080446460914502104009094203550a00054980d286440c501d041031448001d013000301c28890030b03401c011119100420319079011500d841d40310380d0301084c225504080c000004201c0c40000c0c1504000c00340058149407400d460303014641121202c00c004c25906038422065882904080c040400118640d10001c80007165807151800000e0f0f4441041c0c2101c50f40c5800e80b540e0f5421041182440345009c3c0358000c00700540c1c000703c2c04202e6240b00701c0d1400e40c0103000d86801418651507400190900583c4902694201d403501800d1010420600544d500b0411000d441443e000203080040c3c01c03804000c004600030741020031410841030321541c40315a1103900074070602c0203042603400c0e000184001d66420b0034918251500e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 136358435 1250 136357185 136357223
    0x61508010b010507080921100504030e060711040e011113090e03030912090a120308040c090b130f060f0e09060105030309010c020f1f0201020c06060906150a02010b0d060504 76
    0x8442d21a90000175161400c8603000c01d05c0484000400c4501845080790403e2151180a00240710f0140c0305e40800305e15400d15080040405070401100741c4a0346003003009100180d01500400080038081e01c008c21029a00d41506004081e201e400040c10100010107a0104100c01c0a031000e442c0864400c00000390000742166a0b40070440e140000c55026500603018035064902070007400100900c0780440341d03215050b10b8100b5034000c0b811800f14000500b80800c00608032142400f40840310030400100300b402c400120301c000030007005180143d4600c0016201c030515007202000c0e005110b030519a80d542c4508148103c02c1c2201d20b4030342070081100110381403902000711140721070142c0d039081402c2c48030703000c202031690a025042d83c03007803204c20708038a04003414034022076104543d0001a10356401320051810160000c0206124480c0b49040011035581c0c05444002c0301000b040141d140c80c886030303060b401800f2094000c0d5022001078410702c100314050b00028882da110300151010313801c0d0034075 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 136359685 1250 136358435 136358437
    0x109020a050307081b040914070e031921020a14010209090103020906060d05180d1e080423070609060516120c02040515040606080124030207061508010b0105 69
    0x601a8000307402000803038503e500ca00c0700203030080310000d454282c01410a14280c1d4a610507842101c0c2c1c10741b01c7c5501502001d00540055201c00d07075040201010045400184d00c4000c0d00b40e0b200f0f2400c03003041082c014880080c0030300c84800802d911201c0c242240143c065962a198003003210440050701480c41405010300a0b102c40b800050301c10190f1ba420752b4204000400b0080c81d10390040c0040c8220071010314240255805000c0300f900c1d61000c0b41070710143ca410525011030340000e000e6080c0c2c59804120326100d05951060f2103280c5401079899918000041391402c0d40d8040c071741c008080248082000100d101e10489500340c44210220355101c6066a8500400d074000c04032800800e1200003190281d1807400b400c807000c1c904002041d5030303603000400b01e0b00c09603134459040e941200c4a071520300b4a0b1155030082c04160034800d002c3d43c50004110040000010f038816005c0d5451440c00e2010b003c0e4050341c0c1d80e04d07401041401505202d100905014001d8800c90080b903080021080855000700 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 136360935 1250 136359685 136359697
    0xa0e040e1509150109020a110307120e03120702040b0105070507030305091f0804060b010203130e04050f010908181f0206040c14060a030b0d08030f010e01050306100303030e0a060f0b0306010902 85
    0x400d096000341c0c40c217040240250000360300c1c401400070307001024001c1c2c0c5d0180b0042c000c0078400d41041d1403a4134561001448825017441903802503102505c0001c3c000c071628140c950407607040f00d000c602c00d402c42004070342d03070300a11200410320b1081c481c0200425400c60003800c10804141c49610684200019600c948086000e5890204103104007003001b142d4250000c5405003010b00481e0b1030581952070420040c0342d16800741c0040c0b0144020300040140a0000510301103440c4020700218030192141c04051180b001e11035149904460800381e141c9960340e02e69600e0480501c480307032502007100081d4482c0380031902164061090680401c41102c803111192001c04050401810490600010341c010b045820005034400380d07602101c00018103000045104003024840c5080d0fa5152501401c1c400718181c014078840d4001400b04200c80042400010482c0d81600d030100f2000c0b0314280e440d0a21440a4010f416941029050302c2074144030f40040c0c00801081d4111144c03a07a0300c28031001240071301 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 136362185 1250 136360935 136360963
    0xa150b040525090f17070b030c0705100501051c050a0b070c11010306030507060c080d060b04170601120b04140a0605070e030f0604170408031207030506010509030a03050a0e040e1509 80
    0x8444140248110703e06003105d41e0300910300300ea14554840d4040109a00308503440e001e100c1d800a03800003008024031489404c515034180c01e118175410100020b46000103000c961140000114600013444070410403001c0b850340140d41000c0702e003081d21004051080d010002e6802c010f54820445880d403280c4105000c403500040600300701800c0c100215081c0516550070f8803001d8080c40342201c0590385101c4e20f402825039502c0c141e611840c01070f100e840c4403e035412900d81c68010100421002103c2000c4803520f5500c076000e40300503030b61440e200c00401445000c01641d4490340c0c8184040100c65030015000e04400e4407640003050301102003507510207814803880c0e182e801c15004100001d211541104c0c081010321a00382c2429298121a86550068107540410003140303000d01402750742620442e500b1080c01e190072480c06420a0100e5900d1f000c80b08000c080100020300440601e00c5011404c00d000e000510a200c18151000300c0c07961140e410980500f00c965140c042610305c5000146030b1151220 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 136363435 1250 136362185 136362209
    0x5150f07080a0e030405180405012409020901050d0c080105040f0603030c0803060301180303020d06090e15040c051c0c080d1205130c1d16020a150b04052509 69
    0x1e0b48000c070024111000074064a440184000320b482d5803a0008610782e040441c182d41c40c5442c040c14a20b00355103004d4044040c81c550810801d400d82d007525600020b5500803a40966030f5454000122090321418141032282490f060b045a40d065002c406181220012102400030001090104d001c44e4494400280824140455680040c4404d00515888bc400400014507804080340c001d9200c07d20003000c50000303500240f0392901200a103e101c01400fa00c003400c002c4d50001c500c0003a5201d01d00c080c491199101c00c40044d0400c40010f0399100a080050109580c106003d170141151031007808088030104050000071650141c0001c2505c0200d0881e502d0100c01071040140900070140540000740c0704500302c4114000c1140111307020700401d40745103007000100e000b007060740300300704050841002000c00e0b89800000c10750008031000e41540102ca200c415080b58082c61004148500c14a038015081004001507c00310301009400d60390711f80583d070b0181c0141c1030211000c801c180242926108 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 136364685 1250 136363435 136363441
    0x1020a020a02041d01020309030c07060903020906041a0301110a0e03010207031b08070611120906011a0901181d0c03010b0d0b1915180e01090c1b05150f0708 69
    0x640ba800004d181034100b081c041c080c80e9540c2c080c6081e41c1c0129002c4100781e00004045640c0318042103040018101d610305640c245080d41d00042031500f02070a618800c3e500e0b41c0314001c1e1801850002440880010020084506010740601c2c0c107400c40341c00700c2c001c503a80712182c040600b410300891304039550694950980250004c841c451a00d2541c405840f1506c003480084002511441980c07500b2840031001500d5510051030280c00b01d1000300380c60410742140c4010403040c01e2003c0c140a20182c001c81090301e90380d03100d0040716442004000384e82c540d11184000150344070303a00760740c050020135a0151601c2c5d54607000000103070b100031322400311020070400c0703d1035084843d42d00000c5248001800c100c8403804082111402189a40000c500780d124150399001941d004105512011403148001c040301c3d2070000d001d0a0141c0503c10300302c0d80b6444072080320b6081c0c0700c1c070107518804c88203082203c0101c004e4241a42c0d56440d803621110140c8101c3c012420000c07041c14014851809a628408696 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 136365935 1250 136364685 136364689
    0x521160201110a0f0b01090612020906060901110319030c0507150f020403080c06010626060d08040515040603111612050c0f2103100b0c12040b0309010b010201020a020a02 75
    0x1900c241c01008860083e10450b10020314000301c5034003018003a801d108090350602017a10101d68103075014198407500000e910f001a2101c540440c3d000800701e4855071074080c041e0040c6e40340389110400e0740c00740c04001107034170608a0303001a2140106640e5410444205c0145050303c042c41212009060101e041c4030b041502440c94110708180103081c000076040c56680d43d10b2100d42d811a4031020715030342050006100f0039500c09684441400210205848141e2141041303c49800141c4101d0081c0b1506480384180620302c03040740e0045c00d004c5d0a4811941b07215280b5546604603005060010742080d000049101600c0305496040c007a545401e2108200f541d0780059450342c0f000c500c014008140031000d600141844015290f01000002c0c14032414076014655500350461821181c10802307100b4400c4c03220000000d0016101c080c48000c1c0d40f080304484c0c5900c2d01c48807000c12054000000740103e0542d0009016601442d5900020310a410260005900740d0182802c8c0c81d0040e0b2042e60428058 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 136367185 1250 136365935 136365947
    0xc0609010902181905070c0506060919020c190308040606050a06050316020a05070b120c030108030702062215020606040c12090807020907050a09080a03050a030207110306040521160201 81
    0x800d044e41e004424508411011074141d43c2c0c11513011700441d03010740c0b940003840001e20169a005404850b91036561130f00c0c080e400341284608040700a4241e0124827182440717003c003ea448120010b070300e000110304441c03a0080c074010045030308540362801d101c80000c090034001a00b82c10b483c816100c3c5801d5589014510036404142c8804108501c81c08020202107001845a00040d00c17580034a940d56403885425692443d60141451b190440200010000100c010044e182c00ba075044a4042d030703c65100e0520a605e00c091500c1c0c0c1ca8031544004001404c1c2aa06150384030301c606074080d41c1c0c0315540c034400c000c201c3c0d1161007140086602142c1c0003a4400c5245c0c00700703840c2445240ca00c4c2c10056260086488001c0440300740000c2034001402d020004d4000120100800851004010a0203aa03800403d18024540d586d0181500800ca0320104580c00209100341c12000e402c03540d01e450705051082e61140c1711188001006c903440d500701d4004050300b04454050110400e01c0641d41032650044600c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 136368435 1250 136367185 136367191
    0x30f0402030114011e05010e0303040e09101a01030605060a17280e0705030a08040302010c06020405040c0e1002161505070b010f06170601020d12060f08030c060901090218 75
    0x301d950303240d40384039500040c0d0202502800383c03c568461400d9030b281c5408840304064010318140000d00e000340b042640c0c004122002d84015400365000c030303111200102c2c5481503040801e01c82e2400d141e80442144011510607080310026a42070201682e00c000344029031040107103400003e00d00d0719a500c102801c60304125002010407070003412211041449452600744d20000c4c1001030b450f1149860850010821840901021809041c203c20340c0d980c2e02c00c0c83d100b10301c002411b02655504002c18001181e0545004000c068014041090340c4d030001070108001800c2d01c0c2c8a0250310042d60079036440021040e00c41d0a400008a5956007032602401402000111030b400f04402003040800185c104820303503000304081d100f502c540c9401c00101501007a40ea8106880c004404000c0100030303030740090021014512800d041d06201c100b02640c0b0041c2c03000c5e422182200002034800100074030000020805041e1902c01d841154031094901070036503080e900007075070115001c3c10315190201d40990650f0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 136369685 1250 136368435 136368439
    0x110a030c031b0b2a0c070305010b0108070203070b090a0804030506060406060503010f091122031a0f1501110f0705090901020c06041202010f050115120b010503070c0206070203030d1509090206030f0402 88
    0x300241e15403070860f00c4d5070f001c050004101e03004020304000f0440d00f4014a1000701007424818420310300440e00039034a0203220005000882d48501181007220144888500a070f00425820345d6140c6a00301590b03500020b0b034485001d10b10304407000881d5403152064038141c0c0c0480b4503044032541750220042c0540f01c02131920b645244100122074801c06180001d4502d03809003d05840182c3c518102020100b501c1c00c81003d10600360001c01c018111045101c43c1c0c42404030624005281034040126005410307404004514400c12a04002500c0005403807811604c0850306040c0c1a030b210180e040c240e00401204000320f0703105002081c0040c2e4101c020901c0e025140c40002855802514210241e44081c0e008000e60709655241a00c1703140e11000000d0120300301c2c0d006005240e900d500003000c52000a03d860100681420b1140440da00d400c219015241c004040780c2d20b03844da81243e2801046501540c51401c00407802c00a41407000340604103245c0d4004021a04540e80c0f594038041c10800204101e03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 136370935 1250 136369685 136369741
    0x20904020d0207051507020a0506040209180703030e0a0501030603020a051c0b100518060a0b0a0504030606090507180308090f0f12010c030b0109050a0302060a110a030c031b0b 77
    0x10501907400d1000e41903950060004095543e10ba002030b038840c142c094111811074008a0080c0c2c041540012000c1e04140d05485d8030446544805101c014003415170141c0006005291000050641c04120103103050011502250f40965440040d4220380043c4402900030701b038003008000c1c1340b400302003214108880f00002400307401d40e0740d03560809940440303442d400302d001104140054202100725200540c42c100000130b030ba00b44400062500e420360722034107012a50004002d420782c0d21580c140e400031f40d4010014044c0c203440d10381d9100a04402c840c050005002004a42102e0002c030030804101c0b50010005490641c94000348032600385443e10003500700c80912903481c0c00d9202c811105d08003080d803400001c0c1484000c0c1004096031500c501d594104583d2034014003651761282d542c80c04403903046075001c1d901c41840380b0070780714070585c03034040d000c14003030b40000e4000d241c0c000310070364100d5200381e58003c0d0313000c000c2610001100d10038034003402d46621400018440c03024032400b65a8462410948 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 136372185 1250 136370935 136370947
    0xe180102040f0e0f0f040816050c06070b090c041b050903160303030903030608030a092303010c1709010c08010506071103032205062811060a0203160306080d0302090402 74
    0x20004188a54080700f0a03550010420041010b2952610380042e20400c090b4401e00f4141c84500944c0a041071216041c0384842400c82000307800c004c0c4000d80c00c4007603d00703926200c65041c08440d0400c101c2d0b0b150758901400e028000c1c5860035208207265002c80c0c84040c1411840148200c0d9141c00200e21a6014400d003a440501820160303107420055200c0d90740854000c10340d150003400c0d28100e0380702c11081d40c4107100303c1920540180c0303c40c041d1500c3d4124900307016961505108070084184c0895055442c000a0607201e1782d004190001001c400326001c00c15454040440d0b080703aa0441c686000101c19400506c0300e4a4004c0080180c0303130241c11001c007034505400000381150302410b20405010b0b0301381036259902c50200281c0c03005001c212500382c00c205a1800e584034030701c84060032100e1010380740e03540c41d070160044080b031182e070b10440111011468181840c600940c800e803100307a440b2181b64408144c1d41d00c00c1c0030380c070181c400e21740190030300031070720041034020750841050705030720035028450 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 136373435 1250 136372185 136372199
    0x10e0601091a040810020306030c01020d02100f0b0d0b07140c06070503040201121b030e010519020708041715011403070302041505030a060902090903041a07060618150f0e18010204 79
    0x94089045c182200140d403030422804040c5428041440107040d5040582218080b503000704407030050340d0404102003050010251104014400ca100301548103135581c49120a01c00c20403d580d2080320b50740c4601500c0b40d00000307400140e020b50b94182d41c030f42c2d00c03010008074410720400140d40c1103841814505e920481c407000240a40391000400d0003129008000700d070800d5418000c03808c0d507000d064001c1140d401c0c081036900710690410f480306050360f0006020810400400111401020703a60800906401382d202d4464498503009003072aa800c110800104840804040f02d89603210003e00178050f141c07440d03090001030700f03194240281c00c8070201c50010b5207031028404000704078414400018020a54410000444c2c00500003910a0b80705200034051890700441344c03002c0e440209100c80d111202841c01001810703a03500030700e040401c05006a0800c0c042500712540c0e43c0c0d1106524800b0075250520000049103910174545102111004a2004540c10002500244052002520345520b1b509 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 136374685 1250 136373435 136373443
    0x30906071109360312060d0209040b0a0b060f0306010806030f010e0a12080705042304020d0b0a0b0903150405010b120f16030804030209101703090306010e0601091a0408 74
    0x1e00d1400798403540d0102c03003c080415629041030805483c03640b2185440b40001c6980c0c0c0511582404603080308404540669a83c3c2d00c46d0750440e07802000d00321140f4241c0741007000c042c4283c544030090b50070070a1070101807601c070b01a41c40303440c280035030103046030f4914004442540000d0030703080d0180100d044404c0c180d0800e004c0c4006c0031400c04000d00c2180140d04e01600c513504c0780400c6d401000802c400380b00c1c610b64040112012a648800d282c0c101249100600900000c0311401a50080c800540380e2070210b540d810140c01014110340341d00c58295a42d444110303900c60416001e6240d0002140201e01d80b05004005402c40d02030800007a0412850b03021030440518030303010904642c000e512040c500c60041118030021990312034031075440c6185958460146c0144d0100a20079092030307001852908800c00450010040043c1d24a101c2c0b0f210341c1d4454036580400c004a00030700a000c00400c0d0031141c40c4159000d090b041e5a0843c1d168034201c0c1c1605600242040100c4900c3c04100004401c80100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 136375935 1250 136374685 136374691
    0xf0d030c0f061b020c0406050a03080c01060f090c0e010206040201021e0114131202070305120f0913060801060b1804050601050c010203100e0108060610030509031c0c02010b0108010305030906071109 87
    0x15403c0ca4031140b0780304040d1810074048411031050b801e190040c0090f0f00c2e02012202100c0e032010320305448400c00e41c02c0070b000d0b01d20358106c803980d10060240040e4040440c5c008d800c0c20b1030b0396211031080c90300726001280c890f5822100030307025a0060020ba02210781d810214003031505500e00004d0303402800c42076080304035400e41d404c621442c0059215000e00c00c04480110600701980000c00b030240c550f03515262100c0c0003040b41403090074084ac04030aa007100c2c1049403441c00b8010200f0085071100403000700104010300520620303600e002004200321018108440710050909409001601c00b0300403c4040d20009210504000b410700c41440c0903907090006d0343c001c507000640c92448034101105180e8040d0b05030701c11007080c1e00c09418000240c5070a027001d092002d407403402045035640c00111901d94410654040e4200c1018940c50313100b4000c55000e80340c070a140354000d00c10040d11000440300300314280006049a0002c001200700342c0b82910041c80400e01c1401c50300c51800070080054240300d011 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 136377185 1250 136375935 136375961
    0x10030213050a060509010f03060b0d02040507020601080f0f1c05041d01030b0a0b010519110a0f0c0801020405010f0f0309021c0308090d050a031d010903120b0f0d030c0f06 75
    0x10402c0c4404645203000c2c59002d42002d03a81440d041d8508448907903890b04511016026954841100c0041d8944440301d01c0e00f150080e00c140014141084001c0d81c80340d09109080c26405281500f5103500c80c08103407254141c0b030420040c01411498000b042d0070003601210780302401020000050100036504080c10b80402403580d6000541c510b007094900308070010a0403007024039013a0f0030300e4241c1e0888140d03070607108110302e42e00b001d4120355000d60740c600b5908039091030751241603502d2003000680d00d40f50803e14410310500f03044a581d0000d141c05d0340034500940c2d022520f603900703491400b0b11410401541e82c81c42e11380440c205040c0c0e004644201c03c0000c84d002c0c1c9900c3c83d05d0050505401ca180d6681205200d0000e018540303540c20010680c0c0250010b030001c0644038420203240c0c02c401e10004a14042d0759000300400c2e00c180c41c001d890701440c280d8529506041c0780d0007000614000010155140d0042c040d4812004a5901121000306144089800800e11809640030600c0c51056002e05405 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 136378435 1250 136377185 136377191
    0x4021623070f090f0c05180f3f0703080309070b03070e0f0f13021303080f040503150402010807050a020a0f030e0307050910050d020d0501090302060115030203070e0910030213 77
    0x414440c3d4064404004110740b070380d414048000c80f115444000c64039444c2c0554540500003200c030001a41141c48075407941c1e03200110940702c5005540c000c0340303a010628081e83c03201502c2d081440c100d694078051000074481c0d0300985010030208940348001c60780100c0c0d0a05a6020750740390302561140b50000d441e0000021604024807009081403240d04802200032182c0c4400c0c48106400038450405215005d0300d201d40101d443c45154100481003009180d221100580340e0071340e40c455564940251040038801d00c00c3c003400002e000d09805030302d40596010f80d51400c040e52030130015165a4046068502144908910440412403031412140c40c41c2c400c0d52400c5240105100301460180c56421061060b800101030008100c501a2030504944003034407007101300881c9000094600030501e0010b0403650070f00268108159020458a040e12400d0740d803680041d0300000304400300d0000300d4440010031440003000030a440c0c03d00c1001d44c000c401c0d0780e03156481d40e200d5000c40e0342d40c001d003480803c807162 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 136379685 1250 136378435 136378439
    0xc07120c03080c0903060402010f03090f08070209010b040e0403051303080705060108060901020c0a0204090c050a0906030201080121060905031e12010611060103081c06060c020f04021623070f 84
    0xd44858019040b03090f0000c118104640341d00042c0d213880f17020340001d06110400c20301c4400a4041d82110380d100c2c1d000004080c0d14025810410b031540e02992003244503001d01170001c904040342e4001e442c2a20a400d20702c0300595599502a94142e1001c0d1b02d403000000c5c54000003002170b0706a801007410900c100702a0074154904901c480c54404060031003280c99005109501c03014070000b410448080d0121404510316000d0b092903014145a9004181c02480402c40800c80300915000b0704101c1c0e1007079994151ba6030740c0d1561000e40344803040d000c80e1278000380c540d1300000c00c6c07068000e071196502400036285022078148106d40386001010360302400060104011074160b0004070b50b2401040c8605000701203a52241c2410380702c1d04140001400d0700381c00f04603039841c1145007030000070441d41b01d0300070040c0580b030f42c4025213414200f0b07604900c43c0000d411002d07180d080600030340e521404e00d481c1c0e5203c0000140e80e201034201c01c21400b4000b40806051106556604201340c0000f014003240390380c24030f8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 136380935 1250 136379685 136379687
    0xb0a090218041209090b06090d11040903210b0603190f0e0c011d0102060c0c07080a0809030d03060e0a0207030c05010f05061c11060705030909010b0a0e0411030f0c07120c03 76
    0x6415544400c5c1e55500d03200100e5140d4680e4001c81c0c80904040707440312000303441c0389815880080c40602d1a60014603000048041642000140b41500c80361a64803260000e1130398200140d81d403170000907400100c2440030600200b00004143d221255075400440d03454110f10300c1c2400c482b8000d140050f1036010901000c45960055140401e61010100c0c2c010b90906110001c2e59920024225001c46040050002c10701f8206005040140140c0c5041e10125203075820000d0540e0403a000451190160304a01c101d843e0181c41b81d0812110507030084c03259a503400080380001d4100d200107909000e121a90480012021b21030b401c501c1d0a2850002a1400c0000610103400300d2291700b9059a8245250000450503140110140c040110b8006a581c0610b01c3e2017070075030144411940d000a4210008609905d50b40068402c2c42110fa4416070130308100000c101c00e8803183c4075170b21000f0030200007168040e408860b1a81d40414a00421403a041d103a583e044010010036140d0700024000c11864002c01d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 136382185 1250 136380935 136380947
    0xa020d0e03040509060906031204030506042d0b151206040b06060c0316021f09080c010f05040b130308040b120a0603021c02040e0304090b04180b0a0902180412 70
    0x40c4000d80001c500b800c1c103140200d040075002030034192090b5030060001c2e420f139904101048602d20b400780026110743d603e2812a030788401c10b072000c0700d800411007010340940c0d00c1400803969800402030402c0000c49280c48003904500c01a200002a4049203030041a43d15044203020390700c1c440f2001051035261a040042c010307038000d0103240c414030081008180c6130348000150341e0310140780d000d14903680030644000f8608014006000d83d1000480070340c4202950402c0948044030300460554001d45c03444401103032007000042220011480502c42440b02c2c2c040c00000e80b8818a000803800050341d102c0e12802d045402035401211240c2c0000360f10000740ea006e841082d08030502c5442440b0407401e40d0b000803c899044c04094007001a489440700940d40e45c1e401224000c281e4900b03a81e91903440750340d0344014013558a1054010b60070040550340e20700300d2040c0d442a05c0d41203900210291156907400000e4100703510142d9000d0811a40082e50003818420039015a100352054403844039034041c06061 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 136383435 1250 136382185 136382201
    0x6060b030103030c170714030705070b03011208090301091b0f270209010e090907050108010b0c071203050c01150e06040908040501050d0e011401051203030907170c090a020d 76
    0x1200000c0c40100b0009400048444089601c1141000c0c0401000328010840c0180040a068442e041c556041e10101c0400100300700c50003101034a0503c0d8848010703600c40d2101b8492199842c110288007008281c102000e0040c1c5c0900400214561106403215038007640d80440701030030304000304000c000101c10540240300812402406502c60458110040c904d0042c507a941c014003a000500c404040c0c0c4201c2e030344451264000c200451070308203010703642e54405140c000e590202e10240008a200c09008003a20000c1590b0401007401c0380c00e0400030302450703440400c22800d0000600c044191440280036941801c81e404403004502440c20480c2101c1d0782025002c1c13801280342140e801c000c100c00004890a9440030300703003169550a01c004030001041c104100e203242c2e500e40060054401000d0030064101c4a003240c4c40c507600b0000340b81160b101d1009891300703459035101c1c21003040b003160030b8000094044000c0c010b0318400031900001c40c10828040302c90400d0301c0d50028200582d0744140c4a0411 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 136384685 1250 136383435 136383449
    0x1030503121308040501030507030f050a021309270c0305030304110103050c130e180105040602190207150f050705160503100905030306040b04020f0d020702090a18120201020c0d0207030606 83
    0xc01c0720b005490708030052246028103410103440710b00060744d990290f040b501c00e4007941d210400c02ea1401c0080300c0001d410526804c07038100c0174040d0002c1c00151600802000141da01000105001c50080008007240550b0040744d003038160210000200d0400c0c0099481180290642048141c410000408841c4014100a00c07444180900e00c1d842103945a40c0c400c0d150518040d502c20b4950a89210408080010200b81907003420b040008001e941d402078099020141c17404000c008103484103980303801140c0118102030b162030061076800340c415a42030309213519605006203403c446031039160a21007214950400300c4410134040141d81810020800b90b0b00c16108200581c6041d43d540c29100e00c0081c110a1196859020b030140a549035811240400205c1d100d5039a1200c1ca42806006900604c074141c1c4a41c0741c070000100400c2007801b0300c034426107104c05001040c1c210b070740e21240c40b41600d5800008541d801d1100c544211000c10034585c130140c81da0000c04640d40713585403140c180c0310143c100f01 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 136385935 1250 136384685 136384711
    0x30a05060114041d0702100c05090f040605060a050a1806020d0f0906020705040b0f03010c02060114040605010c1425091d28060609090b0f280605090103050312 70
    0x4080e01940e420080b0800d00740c00044229117450400300c0c80d080070300481180345c516140c040e504054116004144020040e250b03442282c0d020410041110303514420540c129001f08182011a0700c80c00040000c075443e41840000900c220b115000c038240d242d001a03000d030303000c3c10000e45a99001640424200a00e1030305c0041181041d10013911210b032032040d5030040313448414800499035242550081c008001e402041103840901e80295100790a1184071991046d03141508901d041500420043c1c0303206031030b5101c0c802d0302584c0351040c05c440c4001e0880036000741e605105c2c03c4e84c800d500045101044944000c040350401c07a00404440d1902c00c8003030300c07500b1000311070040200880c00706180d01081d00c000c0b42c1c00303d00c17140c0e0358254502080000e28030f500c0d0440c0400d00702103580c4510101801041480100c1c0d480c02c08580d04010b040d40d403046030f80240103035040b408100c009010740304c800b0210013042d0305a88001145c0b21000a810807a0590400b041e800e09000481001c96441102c00e6452 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 136387185 1250 136385935 136385939
    0x60e010b03070501030b01020a0512030115260402060904050411030f01272303040906090e07030605060301020f030a050601030b090408071203111303060b0303250215030a0506011404 80
    0x299119500e1142c2814552a880c6c6021903a0082c03224903001e940080607151809006602e4210b0b0354001d004142c0c015528013010700c1824400d40301d02c900740380703442d80503266035402c20080d040e03001c4010001c90744101c0070006614191074a0241c5402644511076a41c080b818440c101414060886807400b480e80c0340040701040d0106c3c43c1c81c60516030070005900003882081d400d04080c1d40303000f0401402d6241c0d0b000368135648803c00200900440b58080800c11050f80c840c240d09084c1c43e60305401c014140e0210314140007107000c513031100d81c000200800052909a5200080725983c1088801c8082142d462042240a50f050b000d00150f0a40890710410316141680d1215a5030150751300c041d003400b0361005841c5107a8001c0d840301c0c401040043c002d644823400104025100041800200e96240c144407109016080001c1a52140840b0402c5444255590007804407001003485040ea1b11890400b071003034a010020000354081c2e4014000030400780f030004000b5244006c014502158281c2c20041 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 136388435 1250 136387185 136387189
    0x1707080d0c0203102007050f0d03060612050c09040e160806010e0c0306031009050d0f080c040302060d0f0504081b0625020c0a08030a0305060301090809100203160807060e010b 77
    0x264040101c1140001a01c040000c41d8080801748480034100402000500c0105002000400103007120750001121880030719513404400b5914a849681c0100e00340c2d01500d00e551055411140d4001e00c03420b070355424201c84200160503624810030b0b4108035040300300d1203140b203103054070080058862040208030355450050b80c2c01c84000b0040a07030f1503010380170000c1142d40d0360901070414503688208c000e00c04c0c1a00c1e420103030345070501c000158006c04d4000d402c2e100440e004d542d181d441407501c0310200d03081c1850b5130240a000d5102004400e01e940d950000ba4541409510800340528002c4078015140d004a010a0080102c980d03400e002d40c1e80b000040100f071400c1090100c00c018243d12410842c3d8882010903071a01440322109039100b0480440820103c400101030941003280daa82484a034540d4003d043c22a2460b40380a4503070201042000d1050030300c0d0084030180d00852040f680381c083d224001517951005810100c503001c0300000d000003841043c2c01408809900f8a00800c03c000540d40 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 136389685 1250 136388435 136388443
    0x70b0705150a0f020f030121021e04110c24040b01030311030904090303022a0a080309030415031a040b0109090f021204050d0206010605130e0606041707080d0c0203 72
    0x10404501c9035032000010701c48000340c0c00c007000c1500d8040041d92101c085101e444000d8009020f01408607000c80703101c62034403160845032070000d40c000e0a91040300880c034a4580152004918843d0415250541340c540710034040001c10048489001510070f1902880382c44180e50201029030307410f4074124041c000030400145e803041c11650306060a0a80c25085013240d4294082c2c07112050380245080b00703c100381901600100b0500c004490740c20000742c40da4443d1b0f105180341c0c110703c094903404041104c001406280c01140c01c036105000300c07030070103a88405190502c00b152036120300280d1200b902054001107501003000074001110140042c8004a0008051990743d10510440076110700008601c0b0704254100c600b900d140e9180d0080314501414003d41c1da00f00a8030b80001480341c0400010b1680c03042080d988801d441c600341c504000d14152644610003009084640c1c800410400000e24542919051a02c80d4203c4007500c8070902c2d0141311810400d08289010502001c43d110301c00580e8042 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 136390935 1250 136389685 136389703
    0x6020607021009020f2d0d0503090609010519180e0c0703120b060a0801170a051005091912030506030606061611090907080c03010c0504052718070b0705 67
    0x21400119031016000040c444003841c41600c0d001000c0c00c4c02103011100403d40c0343c0c6558502d0003e80b00c2050710724107111a41e0302c4150048d102d6001440b00c000d41e403a0400080151060526080382000350001841d400e0024407680f0038041150340038104030074101c0d0640c4000400d01810321070703c10700e0110b54005082c0703e0038800408000316040a20524a2a0381c004207600c1c80c05064961542042500940340c0b907806e00914002128030b141d05038400c2c00010b95400540d50110103842d05280040003600540000342102040c0d000da8020503910705041c8000030b075024000d4928402c1070341a140b01408580000d0005806500030078204000d60f102d580071519074a500910000f07500c0d5180c00c24005084156503c145c0c44410203052103007079100000c55505a070000020307565841901f204041c200c80350440c0300340206600303100421140c5440810b14807000213409510f04007040e003001440000030300325400b2002c5442810351801032001003100c440582074220b8101d28000a41d107400390313201510 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 136392185 1250 136390935 136390963
    0x711070509010e0915010b07020109090b1005070602070b040f110406271b1707050a0c0b090f010c0f0306060c0209010b03180a03050406120504020a15031d160602060702 74
    0x100d0081516580104090100303100e0b101d501040346d50f10f50a40c3d000c07540c000c100503400103400850100d485280d82c45813910314070005094070017080e5081c000303031000c1d085848262512582030124401148000c403c40c1e00c6030b4030440016089184d5803070310091400b510b00020740101c0c503114044c40034500f19502c404805a41509090b81510036142510161503207031758071070144d0704c10f41e002e1003a107400c40b80002c00c42c101c0803c0c7d0701e1666520744007180d4a0141100c0080042c2e000070555001c1aa9806841d811591100913078240d080d8055060742501c84407600100090020356030409110790500c10b0401600061921101d006c1158000035010f80c0103016a4142507400800f0a004c80c40d00c403002428414000103803404030320300c4d0a000d882c0e6081803041e98085003802d80e0034242d91080d0301c54213108590040c15400c0540c100340703151034508803100413103003415a00c1428400308032408803004445650b25000b02000c120440e0004c2061100d42e024809640c00741d4140603100b500030451108070001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 136393435 1250 136392185 136392209
    0x10e240901091a0301110912030a1d01120c0e0a05010905010c061802031006181107030e0604050406080c040c020127080403023c01020304030b040812010e071107050901 74
    0x10150031014205095075869140d07107060f081011b00c03000c0d20301034003203407104035450b0075801081081c480e141d10801c40d10800007150000d40e0003030030f0720360080d0038480c3d007041c94006d03070302209029840708448001400102003400160301755450b00c0c00ca107000000e020b007884d0005000f4078040018018080c0c4840c0140f0f078644556a81c0d0008a0910131450480e4008088400c002d05030301007407004218a0003605100700c00780b4140c0103010114002c2c0500806880103492405010781c5044a402c810507072940e034444010040040e880d911401b92202400c40c4102030204c2c07440c00b00400c8115000c1ca0000f500f9a41420b60740d0301460762030412030544400b15091052a40b0991030a080c144c403e07034000030740c000350240343c10502141c0007813040896110f4407880c140fa01c84e07055040e2007400000c449030307005038020081440022804801a50040e1203540f000d41405588144003001c50360076082180429620340802000d1030344003e1140113a10b160000c1d01030b580c20000410306080c3c0c140103111861003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 136394685 1250 136393435 136393451
    0xa060203041d0c0c06130606230103050709080601180b090f06060c030c1002040905090703020306160c050d0305040c0b09060306040504020d060507020c24031303020a0b010e24090109 80
    0x3d030b02e80c1101d21100c04003050390500d1800c0c450b1005032081010781500ca881c94418041500d00104035011103041442c0c4035040c09501c0c40004402418008040f03600300004500c0014565500700030342c42c080c00701c0001e00c00e5000700746402503003140c0e40c01402510400340581400001204506840d4101d081550341607522990041c1580c61071081f00c03000384807807096260145644c8440d034043e07c1620782020080c08103450b090034060380d8130094080650b15402ca907002c03580c0310540403007200c5000c1c206e0920311401101a21800c0c02c00990640c202c000c20346400400c020080d9440d2030310b01400301c040c4050708002018000c20700c00e010080203103000f1540c9001203400d640d01c0640341140f0310343c407130020702c20341c90034010003911140340407070b240c0c094100c00d140c1c800852404024150020b02c411205811a0760300075101c40d1203904a50180c0c2540152945100415420711020307010b4008541040c000c0e0800900103510a1603070003028002c0c0c4880a14034100ba0741d20311000c1e0440300c40c69000f1504070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 136395935 1250 136394685 136394701
    0x906160804031203090c0503010c08060103050a0e07300f2004020333030a170f030406060e0a020403020d02010807030e0f010527150705071406060a060203041d 70
    0x2100c0c541010744104030107081c2000035135158000081c4c0521135450120b40b9a0354006241c01d0340c00d21810400410380e030100081c06035220703500150b8001c45811001c80c0240c8446451401c010743c60f002601002181c00240d082e00950000e4250420188001000050104e417034800d1b00c1540180c000300360070b40042c000154404031100105045100810455a80c100135003d41082d003911060b0401891402c044201143e408640744001000701402800081809580f258001104421a041040030501c40601e03900f082c02d0281d88118454800002c0309410301c028a5086a0000c04052203240100f00600061b103654441c800c50301da0a0030030840700d0b12141070a8000c0c0040d001d42c0700541c410341a90604140301500100d00840007091110316003203000400802009141c8141c80b52a401010306580b0300d141032a6081e032010711854000c1c182582641c0740c1a014104d000b1010700c9a1244042c42014902822140024281070004510301172a0600200440c108140ca40c01d00d1405000051801 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 136397185 1250 136395935 136395937
    0x209091612111903090506010e071b0f050a0305040303030b0d030915030605030d030207021c0c15051c050118060f26160608090708060c09030307050f030901110309061608 75
    0x2c0c0f4101074155940380c240c01030080003045d044c40300b40e0b9240f244600000340320b2444140d940c00b402496407030b840d040c03840a4801a045601c420300300d035011803403c4104007240b424440e810341c1d00e01ca03a844a41e2a4030f13609000b07060703900700100c1d80c0c401c0c3c0c44100c114001903048000c2ca005c5900c8681d480304401022807040d00240030301c2e485107405004a107600390f0342651507402002458800c4a40c0c00884021018003120001141c0e0001d00c400404503042c04001c01201d05d0801c00d04151401318a0110300c48031902e13400d50811643c0720103d44071001408480d48180400840341c0a1180803c0322520341543c003803c0c0600b1b0300c200085102380580c8002848403d001070f080c540703000d00c02c42c3c1ca01d12031020100d40310840e44c8100c80000d4020400f081d81c40d40003051700320441d0050402400a030700c603c1e00074283c80e40310581d20b50340361000300811000908280040c590700f04d4150b001d55210100c0742c002404414090ba180b00c21038008100c4d18a19903140710a48040c9540440310780c40c00400ca140c4a00c071 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 136398435 1250 136397185 136397197
    0x10515040c030b10020706020d020105010b09010c05030d1b08240103050c120f06010f050a0801050f010c0b0f0406111216031413030e0603040503091905060d020909161211 75
    0x400303c00c0f140c4c2c460903500003c003001110020382c01c40e40f03e501a824101c0c02c8a20070701503c0341443c810891810158403038004161840e00803801d80c3d241103014441e007422542982c032094111462078014900c0c8507002007505501030307500040d84d280c1c0100030541100207a0b019040342d040c1903907940440c80c94240b41302903844507584100caa07500c504200340052840310049482600042400c00002100b911900c02d80d410111203888803030080c0d0074001000f40c074881400040341080440421500414860084903000e106621480b0510b411b09041000030381d15018040b00d0190f0081200c034000080321812503a10030030700840f40b00c10070391002c03040f80a0107460030b0344105040c504081c8a1007002c4405000b0b40380f40300e40c0303c14050307020040900c4aa0300007102c0182041d041030000000d00d09245080751980300580c964900c420b42c41d100000c50f5608468112042c1c41d03400705843e100c0b8100131112030780184504461041440c00c5080049c10954091801c000c040d4035200d006901c2d481003015211 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 136399685 1250 136398435 136398439
    0x1e0c010c020c03060702070b180f100c110618040f0e06100e0603120307030b011206080304140406030206190e041109180f011707051818010515040c030b 67
    0x100450440400a58859499010b02d103e030013000003244450f40005900821903000d031030260b00f070044c0407d0312010300e6910f0801c2c1b0340000315201c25041030f0b50b4a6400d8240038030507072113840752050141006060052030240709400703020108100040c4000c002011220980304850101e210040100d408000c1c0554400c0030304203203d0300003030290400404040b10706858480c88000d0300391381c0d520201035480302a400ca00d40004820004203109503c00c1c2c120083c0001c0605101c030403000404211011130740ca561201c0c1250b04049001d01645c0c00c1034a5100d241c0e07400302d0b401d1054509640000726035108a0480e0720801d482e001403500c405000d031116180c00c0500400400c0494a868680c810325404030300600d1068180311500b01e2440c2040400e9401406500020f00007a27080040310652100d01d40c1400c0d9240c030072840d0008284e1b40d03010f0b603034102c0c00301d550010038542007400844035140d5100804500790307414102007140d0b00550810345a15104211008100100034840607002400a196515 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 136400935 1250 136399685 136399691
    0xb1c0201140708070b0c030c0304060b0f0a0315060816060503061c120f081605090102070f0b0a030c1106060906211501050315011502071e030c05010f051e0c01 70
    0x2e02103c034015240361402064611501e5407828920801440304441039560194244045070100303000c1e610030080c80c00090042ca1041d00010000750550035181e001b00c548040d6070300d42c1c43c1422aa40140c1c0c000b8281d80300244103030420070302085a0390130a8010380041103030210010345599603101d40c1c406c0ac070390001d030050b286a2003030030801200300440703070f86074040340c510340241c0c40c2c40b442950181d10170460b6003400c002401c0d00341c1c0211070550081d40c40f0f81c114480c0c10000700e1000c5000070304c40b0081c031203410200c1d81c40000d02e0000d015984906404003c0c00004e4521001647c408900d0981c0b203a4200d0318903050380e481e203000880503401050400a0ba03440860030175003e01c40050025807240c030020b02810981ea81c1e40c200b40d500c10f0710002d00e0340301801d8400100501b200345507a002020040d4010340701079540321304040c2c950034004074400d01e0041d914074040060140d900c0701e000283c2001e10302506c0200c18400d000d4518800c0e60300c0440511143e4000d105d028004606480024031040024 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 136402185 1250 136400935 136400947
    0x2502060c0309010b120a2603061509040f06140402040e07030207150216020f06041206050c12040506010303030509010c141308070902041e0303020631060c0f030b1c020114 75
    0xc1c075601e51812404940052036212800301d2402500842180d160982c02040d1443d0b0309d1005000d0b40b9070062103030090010703003409050300315500c84c000c00c01c18407148000010702e5468904000e804400045200e806540304010074408840c4081005510280d02d08015948480c3c40c9040300e120704a070009608d1451000c01c3c0307400012110021092902e0088486c0d8003c81d94000c00c0101d04e110380d00c03c0e0103002c140b02642e5000101550482584140040801814038007502403155260318101c4084440c0e07000f11005000f0507400d0300c0350a401940b1030008014902100d071340680496445c1c400034051040109041900100c0c1113014809445480709a501c150364852525003c0d4006000d00040350100e030741d40b640300d4022a6080700499805500410054480d01038115440440f550352170302c84494100d080324140311220f0711008491268400040d802510440180000300b0442c007003041508111a030f003066070f104459035848148820801d48207544c6840142e81d03401203e149400c00d20004104 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 136403435 1250 136402185 136402219
    0x1b02041a0405091f090f050601080a050d030501050a06080a0f0c0302030a0f0b030d0e030a0c080d2a1202211306090f0b0f0403020402030a052502060c0309010b 70
    0x900448080180c50610283e103030800702e0303620b03007198055110000d203420f0600c4880110315000203c06038050010705150a104d500c1e8241080c0c401d030880c0a041d800103d040f41085020004015a0701803450200601d5060400003404900244198420000d6502c04245007401a41c041c2d000000101410400103002c00d0003c1c000c0c1d041200d02c1c0c12001d24142039a200d40800c1d0007003003c4040d0003070141400c441d0203001502c01e40207003402c480d09482080034400024221242c1d000c05403068500412203003c0c03c4800904005081840c0c2810b81c04690f81508118084d202c1c10309255400325400703468040702582245406004171341c070902054045240035180507030f4001030044110b10904260081c0d11980d003a035140d811031161803480e6583c1c000800000d84400058040501042d0b903040c5002c0d03607a000103042c1d80044d0303201d010351951801406035a000f82c540450b007031040c0e20b500340c1c01005540d1b00a0b44806009003075001c0c04c8000400510074980a51017100d42d080c0040007140e0070030002034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 136404685 1250 136403435 136403471
    0x3040308040210110c0603250e150c0303070f02012702151207110120090922020103091e08130501051c0207061401090b03120702060306011b0204 64
    0x141a800b0b843d4040d55000c42c148030380015240911601c0c0242000c40074001030003032a41c001440748400c5880404034408020103009600185d003141e0345e4141d82a000c140411a2205080002c2c103c031020400c01c90822100c0481a2580240c00c2d00346050203000001003a03002d00808100051100700c000c0365400740b070403544845400c2030f000740d59480e0340890700c40000c8620311030b10120010703150600c0300041c41c1d58460461400366500d0040042003400d5183d1401a003071000103003c09402c0b6000c80c01516034101125800e07402080d034006941c0400c1740603c0f01070424050003000c0d04042c0c64085030400d112101402a50b80405080619048401d034100403d140d0040112044100c10860001401e0341c8500c05481c0c004411402c4202d11542200295000354094a0100c81040d102c4102c10740340242c422000e402009082c1e00421b203261040101402c01c10740201d5983c4001c030600041c0050384440d001d69522020070b00b040141c90405035003600d0002000c1400a40c840d04004644030000e450f05 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 136405935 1250 136404685 136404691
    0x91202030d1b020c1207090507080405010f0c05090d0611030103030c020a0e0c0412050c0a0618050603040b0c07020a1802070308010b0a020a0305090f03030c030c120301080601032603040308 83
    0x410030810182075155004a80b60500c00e08801070f413100d003404001e45841103080707101e60b1600040720100d555500b440e0003070790000c851840200700c6010400081c05403c0c0114500400c8400d805c00c9a20b0310395a024009001d98008640150150030102d810422981d020048015442d882c0760b490751b940c2e1070002c20000388100300702d000707400d0b01800213121908441c003036001e0388082001d1401d107420190b17001c402158140c0241c44038841d15507454543e440350302d5120040c14141e500c6903800355021441c90401e40d9280e011b039000d00302c10400c0201061941e00096048001040340e2942e031606400003600c0700d403450304071015103180036049002c441039a41c01000024031948904415a0340c6c0e03011000c5901503224004090703049642e05c0c02c0068412801081d6940c001040c40b140d0f0b940d024046071568100382c0b0340b0440ea900001c0c0107900c05e43d042020715483d60004100764590340c100300f983c94076150180b1000740040c1d0a49000c50104840407544004090313103a00b034585900e081d040c0201800c0040d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 136407185 1250 136405935 136405957
    0xd1116060b0a0e1302010507140a03020706170406090206070c1202030d1706091f0803030a050606070f030807030603060f0b010e0102010c1b050c0312041e050901030b04030309120203 80
    0x15800521509002c1000000c0700c07545000c842c003654030855408550004c24008070304002c400c0002d032001604c141d03c01c0f1142010400100300c0507000b0300e8003a02c2c040301a001a024059102c070540c0c01049042c4c8620b81c03255012402140381a21803020860500540c48001d1410007080ca000c01d035161041909190103008030201c408100c40d901c025900070410180c07042d1800490000110744d81030503e0525006208280c8415424600958410390546181c005880b10780001080c402d8852460003200e4003d1002c441251500c0c059940e0000320501c0380070002c007070103004000100c1290282d8401c100964008600307100c3c08240e05014401030081880c0781d030101d0b401c140c041009503c14441c03055030520f04d80355860040c03141c5004900e01c0c074070b46400b11007501ca0780c000303546d081c0c5090015480e50a0300c90b60564555090501061401080b02821101205030500030010b0390713164800c4c60f04403504000c0e01451500c6030300f411005802840f0f40500700c80d46038910a81925030000051081c0301c50 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 136408435 1250 136407185 136407191
    0x40605030a0f06030210031503020312090126070c03020c090c09040c020606011b020d0203030c0601050a0b120a0513051c09050901180b01110106030b040b0603060415020d111606 78
    0x180b0040307002220000c0c080a504000b0302e80d51445c0040c040d43c4001441c21208080d10141e41d640d0740060b1818220b83c400c0c1d01181000f0a2844095030000c1701c8417004180c10a21000d1040e03040e04000ca003d000408c01010000070704086000c0c50b00900c0204103400c0c01030b000448500d88a411010664011541180100d00e043c0200b0391407031021440c14010700f0143d40701010002d21220300348450744811420307031b0f100700c1040000c2c2c01680c003000240390070a004e038003a00d0590b1502041009071a095403081e496040d04004403981c0c03010000d812a40702c0041c0c00c0004168403981401501c41140c410014580e201e14200c104400440740e09145c0c007042256203629196480e8420301112050a00c20032089000100c05209031500e1a080b41c0803094041c5840144004c401421a0944407164002e40303040c84c051050100788401904100c0d030114041e001803d050406945150a50030341e00c100001055001c51005040c40e0307940c100920f03a2040351030440d2030707403920042015804042c030710407103e242ca = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 136409685 1250 136408435 136408451
    0x703050402280302091501020a0320061005030d0c0308040b18030a080a050108010e0c060a03110304061a0d03170c0903010905060f06040b010503150a1a07121d01050717040605030a 79
    0x1425484040c11b210182d01610510f15030740d13000d450110000500900c43c085074441464056020010913114034032000210701c0c42e0381b800050605010742e07045200c080040418040010982040b0f03000d8000354410400f8000380e03907030f07e101c0e540d215084103078001d94000000d071400180d5002d0111801400500010440c40c0d0369201564200da5250f00311030b4aa820031a000d012515008014000c1c3c43c0320360074082111130140e98251640d90044034210307a85590350101c1d100b1a0012001c1c004140820744540d54441c0716074502400d4440f10080704401c100040c0c000a0300c0030016403d851507850003130002d2000d0f56580c5810707601c641c4201c8610070072105082c0003603941c1c581401103101e04071068480c585142c42d0000081c0280c84030341c07206034200c00f0441000494178000302484e14042050141140c0b500081d01c0c0c00c200c2140600c144000300200b84007840110103941c40c20400d102d6007402d01568400300c0c1e18003c2c0b4011b000203081d022801d80840c0001e0410341010065210f250100e0080010035 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 136410935 1250 136409685 136409701
    0x212090d0e01020a0b0a0b040c050a110a0803040f0c03060f0b03010b06031021021003060602060703090b010501050c0115060206010f080d02030901030209012c1e09070305040228030209 81
    0x65a5072031150050344552039080104890100c1103401c0039250a003c1a240b100d075000c1000d48480c0c00d00103001075000180c035a661680074203c1d40421640b0009410401340c41e85400850340800342000d40300c0040000d94800700a0400d41a0000b16400842845196820048a4000c010300000d1a0083d42052803036500351600c1400c69110729811400e0200d0241082080700401c0d0480c0041c031040400c4c4400000540d885004818514009a4010035103d0402d00000d060600c09440d00040c5402d0621820006030941d21460641d5003c1ca4241c1e11050384055071800342c042911171980c505504000030506540c0881c1c81410703583c00300c3c06c0c61591662030711402d50302c1010301c00040058109209070800c43d03201c0e07001407a508078145040030544418002600c0e00301c503400d0101810807507400024455040088060840f445622860b44090302000c0c081400101d004103480d0425540f0f0700041d003103646080040c2142440c2c901c01e64241c620301c00782c84805090a00050b0b1084800c80c0014000d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 136412185 1250 136410935 136410947
    0x51906080c0306070f0c0c290a091403031c05060108130807021c050303160f03020906041208070b09010614040b030a02091b0f030a0b06070c0303050705100212090d 72
    0x4200903008140b150755440f003c0305d005801c13107260410082100c60090114104410b1301010f0180001d448100001010400100c001202035007010580203000c104030294111500e8000c480115444940340241c60000034110301c50440804012800c86000141003802980010b11940302030300c80c410f090710798921421100181d1440204030303000800c000c400508005520072801405507018007002000f541d00c03641550030840d009000181c04c0c070810302100d079004092401c513034064101140b4060792040400d0741c51040340180d08020000c1f030b03030001c10860007904445101d60021031a0300541414403185000e04001c4c0309800f0405800320754140c15142900c1107c407080c10080c020440c1910b15801e100d01c05070002c1086240150190009100c262407000414280300c00c080315540c0d1780ba124054000f01c8400904450103803101b444160001626201c402054a4044c2007a5441d034651707203000361511002019a481e40b41c0041a4034a94030700020a55026100420942d4075804003940d0403150 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 136413435 1250 136412185 136412203
    0x40f1d090109021e040f091103060601051908060310060f18060b0304140a060e0c0a1d24040207080301090f050705040b0a110a08130608070e0f011205190608 69
    0x1201542c1110b1013600e400228441c03124000243c0041041201520800112805500107444d5078048a0f004901490300780310069001c402420500d00b40701007100c56400711a03a841c198030a0140c0000440c625a80c104015905180d5620b020b00141c0d44845554820110310b10500c1000345402c2107034424100e2600485040c0c0d614000c842d030640d66070f17403034103a44c8140707100d00c4009a005008880b0040303411400398042450b00840200018001d200030b0080480066002d4071401071500090030365039107072103909904031840801500d45281270701e0704548a4045e14070300710b60045c40003810000b000304200207903040f20990181084410104103a0400780c40c0122130300f41c0003801c01c201c1840744091740005400d514207117180c8515402241e02e103c5207005484002940d01100100d403921a07242262591009086c1c0351529207018103100d0800742c82c44222a084510510184108208036485004c2600000e17221100038041402c1c074542614003900407141c0800e0041c10401c3c0480c0c8010001902d0038 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 136414685 1250 136413435 136413439
    0x10605070206030c090d140c030a020a050906011103070309090513020904081309060b030109050c0a02120702010c061e0b0105040f0512121209010c110a060e03040f1d09010902 77
    0x3140540590800540d03500090010728010804c0c4420441602d803071400300302d0b146c4621190758415040300300561900c60714102c030300c1c400e0b40184450700c016111241d943d422690191400030554070340400584980a100c144517000b8403010074214180755001000f20301702c400078902004151110300000b0b1940860f0040650000341d60750101d000215084000e00d02e00080d00a0703035511a4448440f81c1c184d038002d0340071304010a4084010320000125101701c94111813401051454a404034101039160328035000340d08440840030400c042964060000d50000c0b5912440404c4008608203100c140da461a003107550846191610200080d4040c0c8110b4066030740e00020322441c585002c00704040740d03111980c500c00754001d801c249111840c042c0040c2c904203994001d0523085203030420074a421101106155800c100c400040d52402c180007090010840b5004103010808000300040d40d880c6206aa002603014014154005128810300c580c40e80b8006d46454490b28944844403098241c4014407400b075 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 136415935 1250 136414685 136414687
    0x30708060607030f080a06050a080102070210050403020d060e0307080307032c07090504050f030c060a05150d03050d0603140a0201080a0501080712060603020310050a0b031b060a0311030109020406110105010605 92
    0x8004c0d240120f9019a02c07010b0000301040c220348510204002d02c40c281e0007860203a40100c3d040d800c510b0a403901c4106003255240c410304282c83c1d03800080c1000d0740e100018000e2651410002140d0005004403a03000b5089494a96a0300b40200d00400801ca03450700580c2e0042d03607a9038030540c100300f060045502c1c02c88000814156013803400038030052102a2040761907203c0c1c1c1003a0305050300c0034005403d41117600e1006d4103581c94100c0f56a4242c5100601c01030003140d0041200d2040d90711150010344c01c6405143c02c2c2c0c0c480b40c144c428100104110742014003c4001d04040c0040070000242d012031140c0700780d0b1861044e0b00e90000c0d10040d101c081c090107100c3d03000351105100c401c103282406003280d4003481000c81c442e507503600403c0c20a15601c0644515a40707640403c92003800e01c0c05080c3e01040260000c023069180c0100d0302d039980c1010602c2502c100c90015a00c0340c114072a80140100b010f00401c000e03540d594900b03001009522920800300401d4034074503d0900000107104c3d484c101d4805856076 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 136417185 1250 136415935 136415957
    0x3240b0f031c09030b010906050307080a02010210020304290108010f0501030b0711031c0b040e0609071e050406080c03061b03060d031101021317070b041205012003070806060703 78
    0x4244840b03901c8600420400c02c6002000c5150508002e00a210b1a03c1c006090350404080c9800c02c1c907144c00981c0c07640e010549a0b00180d038001000708030781000b140016181e46640c90460a0100c161610b5190800013440a200390711581030300d0380c12a403050f002048180720003107182050703890910000d801d9401a00010fa003480c02404110b1594001d2420b49103000700c88900320702c0e054024181500c000f503a94000d04414146486240c1c03041114138001c1025203400000310365145080e00030449030307980450004e01c41030f0310051414081c00c0000e1040c400542c031003815aa4070010601024440e201e0305020403031000b50864105194460b01582624503035504090008100c581c110860400200940d260f4000c81d00b80301505035210902c00340035845141c55006c480c0c40a0020821945402403c410003501d643d441c1103400316084101d0362689540c560800a004000c018414245210044410096070800600861180745940c4079940300c4c0e00c545040c02480d0064031030050100390080340e0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 136418435 1250 136417185 136417213
    0x6050d030207081b150a020123010303140403050318040b04090602120c070c0311131d011104060c030e0f0d030507060501060504030305180a270b090402151303240b0f03 74
    0x74006c0070380c01d00000c141104500c101c2c604001502041d81143d142c0c07180140205a407194843c03841e0544001d605050504545900742c0b644a041c5148940015230402c80789103881c0d5070400142e4000c010301c20060703010b0b2400c151010350703c0080e00b40041d41c5040005002014001c0503210034075040803000d08003034116903c1d010401c21011800c3e80c445140a001900824140940c0407112564920102e211746214007081c00d44918503040d505004040c0002d1007041e40c0841c90322200c03509440c0c070801801da04400316071002054500340e50080e04c41034200041c0340c1c0001c0107009551041c10b04100d10707aa0b0349001c40390781c082c60000030006901001001800e001120750850382400041c0405151543e40c2680a99002414450307040c03000340486041c131010461040c0c24485d00191021281b48c5007650001c1c9100d01c8100990500f804041a07010403040140d222070051980300b0510000320310f0a07664803000c481d100070700340b03940c4d402c0c91a003010354101840240d81e1064083c0003000c0707240d84005 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 136419685 1250 136418435 136418437
    0xf01060f06080a09080a110c01030b09071b05011103010302100203031603110c06070807120b06040302090702070b0d0b0406270507030f050a0608070b0c070308090406050d030207081b15 81
    0x802c0c04010344902844c00441c140000030301d2a15407a495001039407480c040014181405611810f06143c649410f00459490720303071055600c00341d02c1c034101e10300b0302100f20328100203495104040d08a40c89c2014080c10411803000440c182e900807104020200001c0904983d00c0c1310031241c00708520020314102d0200d9029400c46603c0c420395060180c1070034204000580340480032100c2c400002c41c2c42d020321039211b0b00002201c2000d00150414804420ba40022030100c0c421444009d0041034071300e00140303860b442800b29101900b8a040742c20b41e98840c80044134047c0110042c41c81c0328520380030001034800200421508401c001c0d8212401915000350000300400b0700801d40e405058581c20041d2040c030711031060fa4429119107000062180c1080c1246240070056046404c4000e0100903151840f100000c1113011a0741c0550000d03a074200d0400400d020309038550260390072040b138141140806030082012801c0d07903121300440f0040c903c10b62984080b90601000daa40010000c410f504401e00c0d800 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 136420935 1250 136419685 136419691
    0x9100b0304021c0c05090c0705060103081b064204090204060902040b0c010518061f050a0308120705041a0705150103050a0507050f010504090c14030a020c0f01060f0608 74
    0x201146800781484032814503403450190222002c0013104414009441c04520464100780010381040c00c04280750385941c0d4645042c0405000d511700800e5200c0b15078500485045c1c0c5054a0b410394409040106458034035820f855803500040502504000380000c041c0010780c4030000840d44c0e101c241c031403a018007000f004c1c10281a030f082a1900b0b030208003920709000420040100148640d5558804008142122000381443c43e0b50f00d240c1c40f1907102000002030080e00030640c10030000030100d440001c281951401d501c40c0d904007071180000002e1061b458007034040300900001d68041c80e1346800341180c0c24840d44c001d000003405c55500c8a02c100039140d0203022114404c40440d135000380c8181c00040080801d0740101c0d40365111140000400400b405241c0081805865540c2105290b00c00a482402503016002d09560794000440700386110304080c00d100303c0381d14034040d66401c003c040032019620880c8196410b1240d200d0310520180705200d88400c40b98a000240001400e014007190300040c05 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 136422185 1250 136420935 136420939
    0x1b150a090803160c05030f0d1b050703030309020f1203041205100f0204061701030b060d0510050c0301170619020c0a05010e03040e0a0509150601050705101a09100b030402 75
    0x503000032500076001c00c0100b8502d000280c0c146401e00403450640c5110855800042c000d40103150000f080c2c0300c0c00126444002800e0904610302255100c840c510038031110b40180039442144c500005043c1c15500449200e40282c56060390b02c2860b4080c04402d402c105640b00d0380d580100410440d00d041c0540541c40d16206800341c503d24042007a04206031041c200600c5602d65000a0420107150810100038100b1501c001d10f412540c50f54035044e1b14460001c10107030040101c240144e08119060110401d00301018100304250306181e040305441c1c1e0030034007500655401100da40810080b002030441d1154140f5030f40004a90440e01100b0082d4100301c000040314800c1403980300c0060f000b800350341100150320000b16242e0707103460380c3c0306201b56000d040c80c0b071414540313000d0105000340882c7d00c40390003c0c4c03091007a01c20348600700125054410080050902d000700414400c00e01102d8001222101c034211880355044188810495030182c203803035040380c41c0e601d0360341080164148005181c0c06800 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 136423435 1250 136422185 136422197
    0x3010b0315130605010b0405040e0d020709090305040305030714010c0302090d06090201112505010c0201020a0f022704050c010f05120903070f06050a06060e0d020402030a020c0a141b150a 82
    0xb40e991034405548003a001880c07050808201031116050a1080818442d0356a000704810b000d024030203501d81032640150719000ba200d0151a007494041d1040b01e00541c1c0c032500300d81d0303501d141303003840c1c2c07410030000c0c0c5a40025400c2900c541032441c400d0003980d0920000030045510303120543c0e1010024442d030b9604038180116208126540c000501c0b00301e606446007030b484a035000030f8030044200d00919810680c1404000000100580d0f03000616520165100000d20317498480e50001030580d002c1e50203500400414110081c000128441d0700d107000e81e1080c0112110030000c0e90055031100018941c02d000100140700800c2508040116140c0090203401039a1800000381c441d0b85060071425030aa035115210010300c406800715118007001841549020041e0885110003e00911a42040a4410340d00400032880030105641110014a40b400840382e1200043c0f03000c41d1146050183c0d030076075001c0e480500075020903000b40d212880c40f0042003c02981140180310f50f4642096000740d04100c8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 136424685 1250 136423435 136423471
    0x20a0f08030307030b030607080601030f110a0207050102011503020603040b07050f0f04031209060801091a0a29030c04053001060521031204051f0b01090503010b0315 73
    0x4140909100905088405140d03079180114010301511415240f0602980c071081c2084501e0303600042186c0c00c40f4003480c0218220320a00b4002c006030013502d0300f007c80010300041c00104941c00148020032a02c0070380091002040b000c001038800d00041c44080d40256080001a00048a000d0034682c8004181000c130f040491700810600d041c0c20040c1c601020100001d01481802800c580b03400344000380e03103404141c01e82410b10041440c641072280c03060b40c070f40301c1406d01604c08000710244400b01f400380108007529521001c1817803070a00e68500d000d010b0101c2c51402c101003600c000300c0e03224040762500c55150601d000148070110070f0308100145034014058014000e003001c6004001e51908140000c11100c0c1000104070012030f80202171461103070000d1803094040000b0003550706400484d91805120703910307410030394206030166500751400504402d0350003c07a200c2d5403000038900707070a0307840345110382c2c8039030a2600b03d4802094107645903000900c0100507601c0400c40c2a4000d04040000710221 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 136425935 1250 136424685 136424699
    0x90f18200304060207170a0c03030218030f01090308160e010804030c0b041b15170403020c0a0914062e0315030c0306110313080a230304030207080105090712020a 71
    0x81c00654048400d9070b000100c000c140289403146460f86d03010428101e00d0700003040d4000d0700c0620001c600905054010803041c1075400890700c4c2283c120700280582d884500d800c50998000d1000d11000c8002c0b6049102280701080d40c5600b4900600340e948030843d60130440310065662203401001102080701402c4000e002070342803080b05008a208414461102c0b2208660f080070390755035044408101884001c07001700940c010380031a50b10007079100140840e10395080c221305103007215841d190420038000700060402c00c0365103d420002c0b403070015040c01d84c031f84c00200720405170960085070540364107850301c8003003402c0f18894843c94011800e000030300300154980501c8502c01030340103039142043c18008005000b11800f902035030305601c03c000d83c61850074100341158094800e50152819602040c5c05c4d8038a40240d56a43e01e000604260860980c04030b500c0e01d2090344215002c0b00140519180000c4425050098074011074402c4c0140c5412030801e908810104488801aa4070540b260760000d420 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 136427185 1250 136425935 136425937
    0x140f07170412020a091104053007090b090103170c070302040606050405010917030f0a0203070c030627050d03110403060f0c080c04060c03080603010905120a090f1820 73
    0xc0520070b10048802d400e9004000c420f81e0b0365409884100d040c440310204a1401c0000c450035203004075442e10702100a215440c04e51030701c0035088032055924004544101c0030004403a0b0803074818210510129882a0601001c2c40080c40b0042100400c9140890310b1440308024190720210300b0102c0e092150740307400040585d9032a5010340702190780000e00b40020f503071040c0703000054150102508c444c240b0040810342d5038070035524007103601e00002c01c10003011b520a0045504040d008600300300502c0d242e041400050100c0c00c107d01c03480c0300c004840c0c081041d00c504081d080daa0000043c00004110072002c1e03028004d001c000c01d844400402c400300005402d4401c108a1201e00480003820142a0201804980c4080e01d1400d5201c400c4c0300401525a200c10303a050701072350620b000b1810f9202c60021a015100b5000020b0040c028540c0301e4103502c0d1004060103000c46195a0102e0780350b0b954105548120143c040d00403010016000d190300d5200c00c0e04000c42ca443c0c00c540341c2c202c1e40c154840d51155 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 136428435 1250 136427185 136427189
    0x9061b030c0906020106080a06111c0b040f1a04050606120c0a0206060102150703111204140c0f010219170f04030221060a1a0607030201050f07140f071704 68
    0x100e5922045a40c02550152010015042a000030480a814240c00c1c950b9180003801c0105100e41342d024940c000480403043d5042030107007501d85881d600b40d20320780001520030110000d000c1c4d40703012070000104100c0d0007002c411310f42c91034a28101205034028840580b400612140d00321a04002d83d60000d1014101c0c64480c411903241039441d081070180080c1460340c0a44100c0c115441220312000e060b441e254219044481d5050000781259400f80001641c05400c14031001102004204404c2c0b01d649007044007208483c505541c083d800e0203041040c4a0448020319005a00006d0070b4200c002070821650b0700f640c052500012050f0012510420b241d00440f04c40c4507090010a0420031800d040070039011810f41050004640e901e55242c05586500c0205060300d65503d4207540f40031156612001e00d48420081c014543e11091800c0c042e001c1e0806a4490b83d8001c03410f0005089a445540310101c0e0402c9458054a00155607003184501d802ca580c090340d410300d00210b4945038007010002400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 136429685 1250 136428435 136428437
    0x106051603230d0b010e06040b03100906030503070203010b1903110d020307031a01080105070f1b060f020901170103030221040510080603011b0905060f0d050703150b0711010309061b 80
    0x2030f640491241c0f941c1a07a403551400740c1407005010500750565685000c0c0d805035580c500580b80ca90307550f00e00c600c030f00540355130103030518511b8607a012060050100040c07124038006d0b030080c40342000e103130306202810301107040300e0b00280f55800c1d00b4000180c680128841d06240107015590614441e000282484c2c03c40d40111844c001e40c8a90138244402503030410700400c90306d4000c02c12031501c210098010703403041c40c9400070811482042c0b40d511222200250001c1e8004500700004c242c91604a0020f502640000f40420302e1004003504e1600102056410303a58194041d00d04280801d40c01440340490450207075001c00b05010204403900c582d85180848640c503511240d041c20721030700381404c5842c11403103aa80501d9212281d00d6041d004a090403c44405031203050b80d50b1100ca80066180c0280244e80d11000d040005004406030b00da04400301202d0030a01c02c0c09115a1107591150500c03c1d150010100c8005104a1601c1c0d07029900c8a001c43c1d00851001c5851880c042c68840301c9034403103082d14 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 136430935 1250 136429685 136429687
    0xa06030f0f110a020601140d3f2003070b040c03050102070609170703090b0a0201020706020c060105030c060c0a0303050c04090f0c0e01020d140711120f010b09010605160323 76
    0x248954104080b600412141d8a0070241d51601d201023040e82d01d4030480600761241296002000c90440b0050000b01421a505104560380e48000b0f03101c0910030b600c2400000d01401c409600c460850145003c207900c03014000c500d4005a03964110201c0f13001003054524601c030800010105100b0700041c07001500c03a080000b000d4004d0328210622300d1081d10a010380300c0c01845000d000940140311081500d88800440d0303216034800c0c000300e019120301c00000781045c1c00400c2211b090000014240c1c140e80044043d40d500250700000d001c20b40c0144081c220060b4000515840441d01070b50002c1d0b044025040380a14260f03d920185003a80c0b42e40d1501003085030b840d21440e4049030f009003440d080f00424030141641408004d00280f84601e81080000b0344500001c00400300b117805030100f03010000c083c1ca90305401ca00b2240f0342c0d0f00c0d00740f2031064900c95420311000a0042c50044196416600e082e10b0343c1d4100b2041030480141400380b80822424003a8020301c01c0c105082600b82c0b2903080403401469 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 136432185 1250 136430935 136430947
    0xf070506090624090405030d0c031b030504081206011206061d0604060f0806030c04050108030418060e07030b010c1704031e030e090901090b0a020c16050a06030f0f11 73
    0x5140307080b800510a600300d4154144018440544510700c80b140740c0e08880e40305490322182030003819032203207500740640c00d0b2410103050320194040e000601c508511082079403102c007400130140e05607907084074003c240b10000c00036013081210124800707802100c1890a8500020b101c20b40d02e0880310f05800c0540031076800600c0e14000402641440740c15070301a40d01509092400d24090101c0c12074802800900a000c40001c10a407001c00011550590081041c040d03135940b4038106031298424080c012202d00c0014590b81c01600b079000340c4089401d00d0981d481c407666020f00480c020400340c8111810090401007440200703406184400100410340e0b071729551145189001d04000003021041d92074281c80b421a0b60200f174000040242e000b0703054440102d03d1341c815110f40d005200002c4024103001d8008103001a00045a0280c003090190004941c8031a0310704500fa0041503c170f1140680c442d0200e030050061a110342c00c00c00c00030000b2140802e007201140b051130141c0e90100003040c00c0c41000b141b8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 136433435 1250 136432185 136432201
    0x1502300a0801080609160510030e0109031e02070e0403050d020705070b04090b0103060509041103030403080a21050906010b0f0f030c0a09120f170910020a030815010816050f070506 79
    0x46400011200c000e212600c40d88005601006c442c3c49294803405c001d0401043c803c1c000c2e08401c90f0f200350b01c0e000304040d107200d00d006004429010365020a00810200100c1c0d80c0c1e00000740041550300c046001502a55150707001c642c4c691003c000281e14640034462000011001c01c09a00584142c0030311541313550030728900b613007100c1c01c07011814101400e02d04204019181c03680025082a000308541c81c10b00c2c1c0c0c0e040428903520941d440202040d41c0000c80740300995000701008841e0954150070406104404122010b640043e107112100b60804c80040042c14504001004185410742c40d8a00745040100414540d4008846000c0d5841c0c0000f12000001c0e480060000030749000c0e030702054a943c1c5038030303001c2d400e07400b5030030050000c2030744604841c52841c40c806407201450000c090311403010b21400000e481c0d642c0081c0c1100850004d1000c00d008018120031340d0160b05042e550855140d541310307a00303c2d042e00540c6000091010070020302c2c490103c0000100841405100101144d00302005 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 136434685 1250 136433435 136433443
    0x8010e040b041118062d060a0c050601061701090c02031219091a07140d090c0b0301061215150302070c03050316051020070302011d0c0a1502300a080108 67
    0x1d001300c2d1043e91b0590b500160038450840030311102903030026129441000291100010143c02800c54030817240000341c1c0f1a4088244000080007481c40c5400e07036600c1d220101928080701b22000545c0050082d14130652400ccd11465000040e6944401c1e080b000e00d85040c1290410602502c81486400039a2041c180c54400581c10040302d14048960404450b2410303218000d0040c0c94110a85a0101c80107210319410b18001030425003054076034a5135101c50140080807480c1c08001c1e5182003032000b40c0c1902e110712181c01202c2000d0010600100400b2040300254401401207403a10350035040440880c000301301824801c80401400f1030241c043d410020300e44203002c0300700c0c28054280081000c48003000c5201611004c030300400d9584800c03192405074090000c01d000b80341d0741071003003400034054130000a092100c0b50080da00d4140e0075860304075008800048020650140e84180078101d500700d8400c0240c54215a8110b40c01001d8180c0c0f005070703400b5480110102c0004a0080050100341e20a01c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 136435935 1250 136434685 136434709
    0x1401030e06040b190e010c1d0d12050d1d010b0306010801060b0403030807050c160614040506120c0f03040506060103060501020c03071e030606080f060708010e040b04111806 76
    0x30042a0501d0555151002e01c030005028001c4080c2c0d00030904540800380e0030410700410400700030710241c40152030050104501d00810842c4240352143c180e90303401c281c605605141d820904181c4200d035214030a503030a07800351044008a550301c0c0f0fa400a141000002009021082c00010800c100c082d410103183c404107800841060740740c90020061000d0b81c604075001c40c1d42c136003082c00716603483c2e0005a03918061180c0505803806014103852184000001c40000d458403511400c0105400052010050003a40905c0c0e4122204001e003104905120a15541c40000882107900c1e203d03a00291102a800950b0202c0300340c1c2c46001846005c2d038040c003c61010300307c28401007030b001528800080e9038400c1032042c0000014401c043c0750701c0d507152005a80103190058820311420b941d03403031040c0d580e03201c0409100700b41c0501000b043d0058841c010503030403030b010102520344d1900d07591030b41e182e1501d01178002c442d4190100b2480c420717a100e002003c50680e11616420156240000c1840703a140303548 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 136437185 1250 136435935 136435961
    0x61401090f14010e040212070c03030f0b01020a0f080405031002030a050105041103061207052e0f1707030212010e0402100305070207030f020a09060f1404090c05090619140103 77
    0x528000c1c4204102c2e080300d00c040c01003d18104424180d0500828000d1180c04110011107100d80200003805400c444c80c92a82c0740f2990701000340b590050582421508c0b284280350058000c1da030a04007140d0b000781070910343d60281074503619155640c400a07140030881d400c0c07407140a4010042100000c2c69105d0381c1d0040400340ca0a0010324007a01c0c80350030900c001096184910b0300b00c1a18a81c10704208506c0c805041c02500380450340c1e6500001d0201386641c0b042c40e020700a0414010400148542d100310054103050b101c0400e01001e00081c026208401040081096400e00c8114038084100c140d060080c10f66900780141810640140507106860004d40e20034942840c0134455215800070f00d407001c880c0c0021412400007440c0c0f0000f8441c001c07a034054214641400d20104100040f0640502181d40445d000300b460b04c042018401510701c2a1400b40c03004110076420032a5040c0741038883d611140091908281401c592a8030350317003880c1908100703404082c14401c400196014490014817001d2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 136438435 1250 136437185 136437209
    0x1021210050a1203030f06080d0e0916020a0201051e0301031203150e0c160204090b07020f06090604060b12010e07080d0c120309140d0e0112020307080c0309030c0106140109 76
    0xb0a03400150043c21040028100355499034820f103501c51a50110014150b0350702515540e050100f802440101640da50510500c40034001c00e54508100d80400c0007186990041c241c4108241c00650301ea4025806200b54280e4511a1040040e0204d00541c0038600c01c40e1482c030707810414034000381220346070301d07410001202c10b20080c0710071164100b00c19480201e500c0030a07929070544421904480070100d000350070600f820814420000382d02d2100384902100d03803c03162203508103205195141000d0ba00450150444c202090200b80039802c107540b058006407181e8582d110701c00b030207400c5408604941945822017101440f082900b484440100c540074034000c4411509520380e80a15140c00400e0700605945481a90400100e6007103003420348140b00658440240b007017030203880c04808210f03890016901d40658401ca590b9842507c0c00f0b030506075620405a07aa981d030840540c0d1020b0801a440d00c0107210150381801d0034040c01025010500f101c8851040e0701d40054584040703038100ea00c00d450303 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 136439685 1250 136438435 136438439
    0x7020307031703040c080c01090b0f0c0a0c050f060423040905030703080a0506040908160309170312010e040f0b06131109040b0a05060a0309080d02030903070b061906050d020c01021210050a 83
    0x2909c01c903441700355040c9207869a40d62425014400180c42410501c040f01d019511802c014416040c4041048610a50b9801c1e110640c4034108140c40c890f074000c403003a02c0c81800c039003240c503171259040d00c1200324003400001d80d025954413960324540010070201c0000d02c40608001e03991009000e000e8002409076814042800c82d50359603003c9000b00220100203035443d10701c4a0515105142100061100c14980c00c000b03503484140b503840b54029501d2401e044400c100020b500f00003601c880e44510382008084030341d407a441d5100a0140b0004d48140d0340190402c2e142c01802e03000d8403070b0001a644030402c04d603650041c1018401502c200c06441482044400b00c1001141c03202400c4503400d001500d4001031460f0689000911801100c402c0d4400f644003104024120f84000010400310b4024108103040343d941c241008000c140e440341880740240150701c10440540604058614204100005410008400551422131b000840100c1c1405102c0040c0414480d03071806903030242c0b00584007030782028 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 136440935 1250 136439685 136439687
    0x15100207050105161a0c07031701050913171917040b0f0703090f06020706051008101e02030a0c0906090e0106050a2619020909060607020307031703040c080c01 70
    0x8044d480754100b4586101c000d800401861140c0c6060440d03540910000e01c0c1807400e6864115000b0f283c0c120081604900802800403440441c0e0b41242c90007032440025076541c85107801400c802c01d02c11039000c55150f14100711103044002404890000503240040f6030f00302c1000801110721804101e90082684062101040f00818007039805051300710f11046644421000310b0003444d100340c02404a091500c241c400b0800d0940082452038011765052000b80c550140842078803205128040171035101c5406ca0100100da6000100404084500c01c4219211001c20a00340e90089500d903411542c1d5110300002650003440c1d800207040b4603e001d8041e241051602c901c5a00103008144c207000000c14000c0c081031242d41c5881d94103160707940f440700c0d2035811f042c0f440c03c4c0c140584104020b0241c03050b007154074114502c01d407010fd5100401b502c525448a005000560b800080d059030180190388010000c200c48620760211040b03540b00c000d60300e00c2c141c10001250500b680145403160080da803410826 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 136442185 1250 136440935 136440937
    0xe03100c1d1e040b15040b120601210519060803030103120807020c09040f02040c03060f120203070e060a08061504050c09010c110a08010c02060108010c0e1804080d020315100207050105 81
    0x980c0382503800103100120750000414091405e4446441c00303a000402186d180150005007800c1408070741000d00304d4403100c00540c0c03609412001d0b01390703c00c443c6108040705111500525048803030f00c054903001016018601040e0781d0755801c403142a610000c0100100320340f5800385805900c4a181000190400810007510b81080c034030440d105203000d80205080c841c04140008075158010010800c0300c40d07405014002e04181c1c4101b03441040e400780009141c00400300d00c100e100f94001c0c040e010f160b061030310071454483d024101d16000340c1d41038000f00b100c18041264a0140707909010400c00300603840e0400064640007070036040411402d001800c2c0c5a602f0038002c0c4901030b80003100c0036604501c400450044140795005450300c0d8204902031503056008505181604d00c284020b204020840c60207813140c0c800c44030800c0d000310341105001c030020791030140c21350843d1050080c0b515182200311940c00b40c0e04191000300714030f01c1e5420524614504481c0d11341c080c804900151030000d00c1c10340080d1403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 136443435 1250 136442185 136442239
    0xf0215031e070210090b07030e06010b0706020c0708030715050105010c0c0501050306041116030801080703030f050d110f0405041b080105060a050d0504080306091803040302010e03100c1d 82
    0x480070410000c2100b4600030301c0f659665005100c410444540982071064094030300303546c03020200345400c0c00c10105501c00300d03081c0e0680740200c0c1614038000a95035484020b50010314002e149008034880451072400034002481002e0007001c0380c00b800c3e610301141008459060f4045418040d5101040000600c651100008c07254242071482d101d40d254008100a00401424800031110008880600008410700114414025075818482c1d83c0c880381550750b903650303d00016010130314032072030704021074407941c01000c1700f598202010420300611a02441c0a41000c0311904100070046001c3c00035003410b02c901810f110a5030899011450720b44409003000714103008250087d8000201820541d005408403080640000e008000b203190504201d1a15001a18054818040708020504118100c05280712036035041d40558640307071640d07005581515002c0c1d4256014080d690a00c00c8450861141c10a51a035039100c034103c0d00301c60503e4000c007a0040c3c0e174080c4030703140940c4900c130902010003c0c0c0308 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 136444685 1250 136443435 136443481
    0x12050907060c290108010608060405060f071205090601051e010816030e0708060718030c05190e07031d03161502090306010902070b0601110604031404050307030f021503 74
    0x4122026040c00b5907800f128003900800d1000110250b20710440d1250390074101d6500800800c2940d4440040944038903068134041c0061b4030040c04074466800000380c1030b030005183e040481807403c41c03a0b107401c10f4510444890070542c00000c0100410700b0440b0500303500b0114002c00303560080705000040c01d25880603101c454500410201020010702a42c08940c01d21105022207034072940c0c4040060361454111505000903207080d20401c2d9120025203024241c0741e102c808541e22600301340502087d00811000c0b070500603540000020300660560040b1b00a0314a5940400e50501042035008180f46e1034102c0b401079401000241c62400a000043c9000ca03400741151107151009420707500070340101213109a1601840c0300008501000343e000b0541c4520031242000b01d55130380740040d52620707481ca284500a4011500080c0028854a411120035540d200b166040c945c984000ca850b0004542044800d902055400c40561400c41c01004940000c00e4801e840e42c0f0384645010031502c17890b8000c1c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 136445935 1250 136444685 136444697
    0x602060a0b04110d02090f01110703141c080601230a0302030c0705060708010905010f030f080a021c0e04051f030807050c03010f1d010504021e010c0b01030c03031205090706 76
    0x1e01550303070340c1c00207214400031080440d22069401e030080000c0d40b0064440d4030580c08141a507020394015144541c07284100005881c64a02c0c1d03440d03510000051550850031402604d004c42912619002d21202a051907680c80186280103800900a443c60070500ca000504003104680704040e0300084480c1d01a8a10b800f5840381c85004e40a000303402490401060f82c000c1000708114aa07100014034102d0f0480713801401547d071303190002050b503443d038040035003114a94035690000c502c004009011100e1284120762004c0c40600b22031401070001e420b06000518858400b0b14185081d00400350008401001904000c9000d40400104c2c0d80380c4c44010001100410841c00f884028881c4c0d008642010b4020b00c401c1900c01f40740001840802a007041d410344007041640e2902c014851588215070103001440348440600281001062001c00c00d810400d80107101c4c030010344400c00043c001c601c02c1c1c00301000c440c1185000b80145030074a24400c0102d10b0202007010b00c07100082d1180484055060072 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 136447185 1250 136445935 136445951
    0xe010e03190309030f1101200604030f0509100e01110705030a0201230406020703030314040302150603010207140a050712080f13230f0102070605040506090a1503020403060b09010602060a 82
    0x39a8440f041d54400780490268100b004144800702000e004a0718090340ca058107012241d0403c00303141904d00280340554449000900024000c0460103a142c115050090502a07030701e001422400f0344040c1800000c9103100c0c00b81980d40c101440840701c0740c522000c1d001e03160400003c070b940c0c2c465103000607040002100c034030301f414001c441480c261402d011942c9036486448040217540c4013800c1c401100003e291440d0701d403050403000c000ca40903a9259010b0300310030340d0000c40045034590150500751306543c20042880020b880710009210402c1540c0544500800c9040940c100707581d65000980c19120840101c001032507690480d41c1d03002003142e00036100c0c03201000a0100481c15080802618820181012400c0543c1d280c2000034508454116002001900498a409003442102d000c5403081c04180907500c3c00d04064a100c01001d440c00310441e694401c0e194203449040e00e4580400da00050501c140b09070b500501d0518001076a00380c1305035241020003540d900700200100360765507640c81c40b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 136448435 1250 136447185 136447187
    0x40f0915020f0c0312060a0e012103020c0a030f0215070302101104050405041109010807050a0623120108190b0f06030f030f0c01050a06050607200402030a0c0e010e031903 75
    0xa50b82480d01078404c994941c0005000181c1c1d0035010795005128410844002a80300762030505203041c1d440d00041c00c425143c0c0b500318a04500f22424089040d401441c2d15021241c03140c26021000314010751407504c14020500501c6000d486d4a0100055403c003004494042900060440700e0031602450014080040307114140c1d8601481e0049a4409d05040500052201c103000002403140200c078110486c0e40c1e10340e000d50342c0d00303900d206041d0010075a15003080641e0040c0042000241000c0c41910301c07400400f44103209510903c0d400200c1c441c039100510803000104488850b0007049603241010007480d4407403548449000304003c7d00300b84840e000608a071428000403d070010b040b03007169151000d2070501001a002229150440c0d840c22000503800601d600590041310b1024184528007107164071002d070850300d02d49c10b410449402c03421841da60340315072000354890b500e0703018000341034400319200615031100102014100000318204000c1c654010034400440f807090360a1000700452890 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 136449685 1250 136448435 136448437
    0xb04151b0b040807030e100e132a0207170a06051906080318011d0603070504080a0f020405070513090506030a02040e01060602071e032301020c010902040f0915020f 72
    0xc0240500e58020502042019000c0540380844c0309484011a0342040307070900032100010642038000035421726034070708203003407020030204180740061020030440c6899050004041c809101d040140c1401070074079031443d80c1400440d010304062803031440000d15181c0b8095480038142d00261542d941c48010030b55040003c0d48000c18525040424441281d88a50b80c6032a82c0205150041032100100382d00c01642c03045650f00064003041c041c000340c6c60b01e6042400607981004215100740b1004000118203407008024417201c0038800c181c0020306503094810300c01039582c05021181404018400582c0e02031980026009440070310f0f500044994640300001d00c2c00d880c210003c0e41061a00c180c1203650081900301c10181c030665021100c090750713580c141909030300d40380d503405803000b144520900c002800410851071811980030034059005107004000d003241d02041c91140c0a039910184d000450805025038501840100401c10980a0f641c0f03c90041e030a0740d05501c0081d950016608007a269404 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 136450935 1250 136449685 136449737
    0x40b03060a1707030b0603011e0902010219050d0201060b03160c05030f1b060609010513020c011409010c0807050301180b180103050708060112020d120210020a0203090a0b0415 77
    0x64008902101a02c54540d20758040c0e020a6805041100005040381014001d00e40031141200e80c0c601207030f281403807250080a101d070049045014864041500310345c1034000c20b504601600140082c07103070b148406403c5901c55804070815a400b40b007000b008850045c821050480c040c00c028444d0780c01351034034600314409c841407031040c14030202d04001d1010007490084051440c000c1240c1040c0c80e41e0040080641091145a501c07900b5480580e4100c043c5402501d8000e480c4400070a610445098100070200202e920300242ea55a50002c03e8455016083d550802c4c00350424500d1941072000c01c120120050000c002c1032502c40b01d20110319110100c1c07010103641070148000c520350b1245401ca0300d54086e03104403a4240300f46000440c41d4000700307180f502e02550041c0522040f541d44e94031500010b00895000c41903008000c00c9541c07103245ea000030442e20200d6400743d69207801100821980e12400e0700a0592100700f0f10060201d000c0d000000e1408940314201a00503070200f01d00340003010810 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 136452185 1250 136450935 136450949
    0x9030804090911032e02070b010605070201030b040c09090e1c0924050d1a0904110a060206041211120f031501030510051e030a20030304030503040b03060a 68
    0xd8009007000055000041c010300ca5115000c0b20b006110402d942d902981958258002002e134880c20740d000c4000d25089030078422800542448803e49818842d10700903403140000c180002064000c5607458410303150000022a8100f044144540000f08181528090303d10b5265903078801c0c01d0f17042410030685000b8090341d5020113500034032010003400340b5103620840c4042c855806d0400710b03041c0c5d89004400402e40d95940e560500c405502d841000d44210b0b529040a01d511607941446a141c80b080e9030700c21030042c0c6882958440500c01d0141c0e400c0242d0001c0d0864002c10240300002e00c03000c0d0500c3c80b81042c1e1034124081c9172465641401c0214105042000000000f07800c1c040f900508051403044150141404a03984644019404d80c0c0c1d0844001140c00e41504003800035240c0306081141c02042440242c2c080b80d00800403038680102e098042c0c030322049214600008c505210b4248003400700c00d901643c10545540d40b034503904e02990149441d40d40d0301100082c0d540c3c5a42c074241c001440a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 136453435 1250 136452185 136452187
    0x5070309140a030311040b0304060207030e03150f06030714060702030c0603070306080c042a02030d020423030c0901060c03051303031d04020c03040b03060a05090c0c010c08011d07090308 82
    0x101c49079190b0348080c2c00c60119042c00091071402d03080c102980c045a104030724691440d550390f580d80d0000d50140b1000c40c141300c2c0c21038000c405600c04004941c00201c043c004c4031118144452850010b20006100c0c0b4801d922441040c0990054194026210441501e500b038907040180300090400032003650058008402200304865107525400200461300064240c4074603028a42c180415104c240044d8440201d0f03444c4100c1c0b2081c0495803542510010381305903410079400001074400d0360300c5540300400341e0032030640c0c2c10880345103c1904024060210000d207540c12141c00421910300341403244409105400000105141c007a908071500003141107110480661285000b03442900c0030b096101803c80007407980300e44c41c1014422103140c44da900004604103482e114041c06d850f800100403d8210a800d480003903652100b0340000d0184070b4510006480e403003081d00f03403400c64241e075145000308201c2d88010030400c40403800d0000c0303080e400c0c0c81c51f10890381c85400c00c0c0c03840e5540c1d0784001c10b2448 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 136454685 1250 136453435 136453463
    0x1204020a03020d0f060b19050d0312020a03090209010e01050d081602060a0908010506030a0b16120c081b04050a0b07030e0307090b0a0509011d130b07020105060a0509040b060405070309 81
    0x4d280082040c289124885c01c10440e00d040b014402d24102090248902005003030f0b081c80b4a01c0c0c0070460401c8540300e4a0220050240c0c002407a041e42c0000070100d004c261178a200200318076005074414054844405032246561410001a040e900545009080001c00142d0320846081c566164800c1c2034000c0d203140e80e034800c0c1090052984c401441020321035441d2002103051490301182c0c0e045580e82010381101c054131402c4030030380c80c00c4e651204141400314081c203490b030086060241d95030b18601d81c0c4564040b46031508140700310625846540a40d004104018020366031010145000d460f05810070a4232100146030030b80701d4212070001c290b458490010005940e10003908010803c1500703072110000d0690b03c10a100c9082c0b400c0c018104124013400402107101686180c041d404a5010050104e05c1c1044c0c468244281d000d0343d6810050f5120720801c500340c2802881c520007884142c5080b42c882c074003521a17640044000e00341501c125210004035a0b000d20030340101100325006185400d43c08 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 136455935 1250 136454685 136454693
    0xe15090d06110306130504031707030905190b06010906051c020904021803071502071715010609050a0f0b120c09060f03010312050c070b0a03090b09060a0e060c1204020a03020d 77
    0x60000c9400c50b00c1100003217503c2c54422224010711780660391585680700b001303809010f40c002c41344000703111804042d5684070030004548204803022084071150002040c041e180d042003284090001e00b4541071240200080266551000484000d4402d18035421070b002076180b1210068400e407200c285d0b00600104482c3d085ca1041ca418441c0c0e000300b1000c89600c00d03920b02aa5070390700300c4040c211001d81c004140c100a007034071010460310245081320070781e940340510322500340042307000b03030440740000e40101814442402c120f80b00e10f0161154003007405140d81b030160095000e00c01c64000c1031540004001042420b420902520346801c0c0082889445240002c2c0c0554190001d20040d1240005100d80808083c0590b04554500f44044090104541403954828050303012040320303002c041d030b41d028481c00300c5d1400003c20301821415020b0300e039500f1701c2c01c1000c050301c4035076001c0f0020b50001e906120100d000b0400f180c1c0c22200b00c2c00c4420441d595400014845c980e942e0001c0e404c2145041c0100401c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 136457185 1250 136455935 136455937
    0x1503080913050106140903030c19050105011e0605090f031911090f070c05030d09030801030209060103110301140a030b04060603140705011409030a0c030c08010c0e15090d0611 77
    0x480c09840040c1103020121410741503490a02c21070011031960f15102030b0b991080320042101c840040c00f200d140100585007986050810107120050248404511040000038044d0707900501c002030b00c600c0703204000380041f04113811030b21880c01804130019840300142c40748002141d100070f0040503a640100d0307808a18211042c90401125010102d40d240300382c514050440c540180800c0d07c0000c03c60f0780d5130300c058600c0390010030152003520003030064048040e00390040c201010300c00c5e518018594994814400c1d50358024002a06150030028811031548030402502e0440f61020382003407102d80c886002c5130b407003002030300007030000400c1300e0030081444007981050040724450040c01030b00b00e01c1ca0304102e403528a41d010701400074013011002d1488001d050301030600000024181d40049102d0782d12520700c500c0561049490006030b00301000400020304c00c074101800207050240c0b0807007001e400100c80b040849002d200300080825034503034a88660050500c034503030101041004c08550341041c80c513 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 136458435 1250 136457185 136457197
    0x2505060c03090d0302160201030e190c061106040f021c050319020f0d0804030806010e06030405010507020f0c01020a0803040f08030a0603020a240c051c17090d08040b0a150308 77
    0x400d200e43c9004a02540c440d01c01ca8070f034440130b031401c84a00c0c0e16076030046015184c0d0248102462140540e846d41448a441c8010140c0340304203083c942e8030781780c48400b424008100142000a401c140e04101c04525202c40d10740440e07604840030115507070034030000c054202c1600030180070740c07002082c3c1440184020114050344040c940885400c80c0f5000c41d5184c0d61400601e64000281c01003010800003030045403801e4000300c0504011941444c40c00100b10190811103050b2101d070744900034407110701c3d01805905844908030006d40402140d07a0000303991005540401031030f0a40001c001002d000b074000d00080015413284803142c1c0e0b8100400c4c40340c094681400300b68810000418001240c1c61229001d03000e00c40c0d043d0407010b070100c0368503060f241c0541d004010340da00d00442400d40300c0800c0d5001e4228441c01c07242c541b0800c1040414564092200080030511070b9802103c00d91251a0003089141d403040d44201c0c411507940d0b410607610040c0508940c1d080c102c1c2d5083c04d02008008229020b402 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 136459685 1250 136458435 136458451
    0x150c0512060a0302030318030304120510060603150302120109060204030b150102070614181f090b0301050a0e100f0608040b1006080a0b040b0a0e040c0909082505060c03 74
    0x415407110001c02403800903900c0002e40c590320810403850040b400400c0c0000f025001401d9904259454003403030725001c030520084a071604040b600111205240c070a82018141c03d1404001004a07046d00c0001403210f03000192007003020704c00601e00c0f03240035045011000e0740b00600355240e40e40c91904a5210344251240044e0174007141000005510005201c0100c54680c2e9801000040e0066040090ba0040195000c0d02c40004001c101303680319000e000c0341c80ca2400c8030b03580400854420081850314690403400c4120410001001181e4070b40e441041a02c40940e445035103a02c0f04088103da10105501140300c0002c10b100c000798054200d4480c91095000b41800c2d806a91020350920554105001c0c4101080003840850f4050340158049a20090301400010711500d20400103109603440e075005180404c0c2c0141003004011464000500a049040d0103020702c1c045562510503d018590884100a036079648025028800c01510701401c1e800006036101401c00c44046643d40e80121034141c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 136460935 1250 136459685 136459717
    0x4020102070608041a06010507050a0305090f031506060a050d0e011b031506050327010c030c080403020601050402030a091a0708100e0a1d0607020307020102070504090803040b04150c05 81
    0xa01900840d4024840c1d80d1217500e609010300d054204400e60711000d0401d030b040100c1484a14000f0b10b04001c00482240280c90322a00c03220280b01300510b410300c1c0c00c2690301a4105400300b0041f01143e06002e900300c20304413007a9840b900c0800040308d0600550500300005402d060344d0703c2c140030307041d41b10007003075100d0f081920f0000100d01b80580c26142e81030710324074210a10340810441c452040024603001002c42201c0450f01f0481030004501d80031410b0007074840c0c2d5440f0140095503405101c0c0944442440c1450781071841c1030b480c040d44440051290a01464002000601c0c8508940c4000b0340301d41c1c03205187c50946034041c80d4a0325403008690040104d03428801146d14040b09400c810104c40d41c13a40d28901039907a60451101404103c1000c5000c4080101c009810078003d108a504c20343e01940103680312001c0b80002498100365600c59030080e407900352880003044510040700da106170007241d04000c50b181e40c50400c0340780307041c4100380e200e55160490904495074058014504240e40306015 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 136462185 1250 136460935 136460939
    0x9140604050105060a2f070e010f08100b0d020907020d11010218010e030c03010e03070515060604170708070f030c0b0903150a060315050f07030b1c020a090f050402010207 75
    0x4002281c00c00c0c0541d03a0f0060042c800e8102c500e120705003c2c5c0003a650341c00b2070140622641384281031600d101034004090340040c0e10521003640044800340c0103111921041c1d01241c9840740080c1c45502c0c0740803e0354410b03111000c20401e600d420140080c4603901a1454002c0d14195600940b111205404040001d00c210300c1c1800425050003525025011406100e5172002c551005640d040c100602d2660140100164110991303130a10445a41e040444041c2d0f076243c001c3e181ca14186400d298207480344141300c3c014440180c942c5801e4906861100185401c481041e262a41c940f0400354040207585c45400b2010400e8440120000c0c02c41c6d11955007003a40548840303a0703100d1b50280d0300b201509540304917005a04020000b55086d0010800400000c1058480d00c2d0007001001c105401d40c00242c0b10360500c81015455100c2c9a8415050f01c0c4c2003101d00c4142c0001101c000d04c0600d010841402d003044c60b002d55880c009108000d101e03510042088020b05c407146409004c0850303040e0b0240c0644800 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 136463435 1250 136462185 136462189
    0x3060512010c21140403031407050712052a01060602010f02030610051605070905180a030c0222020c0f0c090c03010e040c0302030105042f061c020f04091406 69
    0x258030810712040d121501c004201c00303000c0304101a1043e815103000d4440c510071564880083e491070107030b8020390f0b010501071300c1d109030100000c1c1c2c0a04420304100d01080302d44045003800115000403840c9284c000c0d981c1380c0c0c40200040f01c5017030b01d00b0f141003803070940070310002a18154040c5045a80e150000d00c885801f003660341c4220b0008490094100c845405d206000324803804c003c1c002c58003050303640e02d5928030b583c542503d42b007115004840042daa0704244083d0b803003489003c040020049008189000c44c40d075005080854464000340030301898201032403110079a038842421083d0074141191210071000c42d180c2e0369a141f00411007240100100b403503a50a10114061140000d545042d00d581d03c1c002d08040e001c0700040c020fa804e0b01c410031001c001a43c003802410f00031070140c0b055110070151201d04075031412007016460700c01c1e2100b100110b03268440c1c0c1d0030396a18036404158040588007002103440a80b0580d06502d02c4c0d4100000c0c003040041140e8040400445240000d4100e66a10f0302 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 136464685 1250 136463435 136463441
    0x601051002070b090102010204080601080607090b090f04110c1506090109050c041401051606021206031b010309020d020901030f1703010f0302040b0a03080f040509150a0317070506070306051201 85
    0x40510016009000107115000d2020028408138406100042c6015a980d800d80c1c2803074030a030031218494101105102941c0d9110a01c64090058601d0180c2b500350281e000892068125030701b28065504d40d0b03001a0605101003d4901654541c02070350f12030092078031515660003007221050712a01265001050340011441140c1c0f10781d180040c468509400c001c403001950100d40fa42d54100b0900b00300050041d650740030101404c42c8aa2005a1174500e88422004064001004540281c0c020742005800b0405a404e4042c0c80d00c0a0034000b070002c06500201f403501100c014080d400c0707548840000308009841c0060003071140240a0314a52001100c01401e5622003132194807101e16801710183f000d45042c2d800810741e0280100100d02c119601d40d94110680c02001c034404c00348401003400c0003181002902d40e0303031003400380002902040002c0700143c020f61842c0005403110303208100d032402007140002151040354008084900351300d020600140607101a0043c140150710400c0c4d8030a508130140 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 136465935 1250 136464685 136464709
    0x120c010e0601080604030c05070305100c0314060604050f04060503150709120b1611061f09060308070807050703080d0605270f0c25020102010b09041a15030105130203060105 76
    0x809000e40791210348084440042802e4241c03294002c0049c000002041044800506130800700080b84100c1310590140858081810b440b45c0020a00104a45559208112410b4400c22602a0407498514010900130f09803a041160548a02ca01c1c24490201d02c00d54944034119a54801d00341c1500c03107209e50086010110002d020b0b4140501145007085d094000071039500d40c0c0d2030b00400b030100c403644a07071030000c055600403070403140030b1752070f0b20040c540826000c0503041c3c240051049501c0c1d0303590401e007481240c41c09852440b010500004003c01884020011078110342e010f911420101c2d0700c280104030600c14580f06002a040341e8540da001c41000c0e2880c0c0340500f0488659903110300d03401450100003010500b801c40100000e0300610000c081522a1003071410f44551940c0c3c01d4030000e0700f11074040380c0e40b911400e805003c01001411104149254504102c69964035484039030303104040f03150321103a00c2c0c0d055080404000321108689401b1340040d000310101c5d00d99036030f200c081c41402c070002 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 136467185 1250 136465935 136465949
    0x8041a07050d03050a140423070e06060a0201020c03040e090c09010303020c010807021609060f090510060c020102010b0909030c0c1002210c1c030b04140105100e03120c010e0601 78
    0x1e11660b07600e000e98802c6600403403801c2c01140c58150302000040d020b02c00c58003120a1080c55211000400c1c0044800d02d1100c4c10350000d001c0e45080144001e40c08000030001442180000b6500300001c1c0b00f03405a60560803604101e9403180d450300a600c800c110111040001481042c0305507800d498843c107454102c80e055000f40801d00d410a00441e09000c0007042c10003548603940043c448a1008822000200103a81c00011605d080c41d441d105048200d500500b4050b08180600107c44a049010011104141816030610a07a840180d014011400d1607a40c0094004204079408201200910208001ca810b50302000558030421100700c50200300900107912184201b142400c243d0554485001c5515045062480c0300e480c03503103402041c123940307600101148101d6011a402d40505030112004580521901c480503502100b09001440340380e100c0c001e5003804801e03050003403244594544000e01030792030841d192a02d002403a0b1140006150661a003101c0c034403070103c0840d0180c1a541c0c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 136468435 1250 136467185 136467193
    0xf16030605060a0f090b040614030309010f0e04020403080a030c020a030e130b04090317010e040321020d0e060118090b0103022704030c0b06060a020706030f0b0d08041a0705 76
    0x6589584006000080a00e500800c0700c100200d0b034110b1400000c001091100f42c0440d4078820b2006002c00d44806a2011003000d5440740c5d012501d076004410740c0c0312480d00307107410201d50441d440b00301e4080142103103064010f031000030007000344001c041c0103290b0070255860034007607100d50401c00c1360703100f12547e030140c000b5407003417040328291404207170148801011f10300204442103040d0000c4c0c2201c80d1498102c01040340b40d40380d00d400d000200400ba00401c20726107075400c540742c144c030041e1840106046c0d0f01c0742d45045141ca003400c80255810740d48100490300040203481001c0c41e2442d90b0302000c0c02101e107480c1401c1c81c030390344c1c10000b409112030195022814013840c2c0d103583e090100c19209280136000380fa00405c400c1c4401c8410442c0a423085000356100186800030b400c0918407460042c2c0401c0c01a0000c0100424594002034a901110310303610380002c050382200d5545005100a0030f0f055404000c2c3e60b0070000f802180d10240c801d07520411b9110401064a03446101c3d50b20541d0402029500 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 136469685 1250 136468435 136468439
    0x4120318081618060302090c090a050907020606091003050a0b04060e010902060f07030201060314030d050c03061f020c0d06020c07080c0d060209060d0507020a05120405010207030f140316050f16 85
    0x1072040f210100580441c00114540b905e941c0002c0505804440300f148400380814008640d140180c400f800614055451040741e00b001e0000035154003008201c10b0094190f80e000c10703003081c4104ca100d0001c54000059076409a03052401d20040e0a041d11300341c0f03005041c800418103403c818490400d0f465801414640b50108400d0301c01500c0d00081c8044d41995070702c0c94008081451210b44c0e03042d40c600000030750380e0748029078215422900e0240c07140d042c0c0c80040c820450141c070741c880815585100c12492003411040a44101d2030306c4409105241c004000c1180e01d02041541d40242040d04d551078152a08940c803502c00c0d41d503940121001e2a4003241e41070800020030341da54010681d1240152540c1c0c640907610f81c011080d26001da5210005034401c03001c6c5030900c4000d1005203038051007108118901850705000070741d22060740c00060118600c0e614484100001144c00002a00c520ba0070f4946072001c2100300d1a20081c3d903c41590140100d01504841c0781011541b8208080d41c00f622a020138 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 136470935 1250 136469685 136469699
    0x150503030d11040f060c03030c0207060507080903100c020a14160e0709030618110d02300706110f0102040e13020d0204140a1826041203180816 63
    0x100c011514a401108100800710b0103480c0303104c81c40c014050b1501c038a103c04100d49401000c4410250144045401254080c40303842e03440f204480c0046d030010611a01c03aa0100000303070516004403440958185441120300750d40790003090005040c1d00500b8603807024221408015110340403c889620354000c01c903401d020701441e0401d4550804610714120040585031f54070401190041d890011001c0e214500c440200500b02c000c080b401102a40c00ca02c0d030a0066012072461800090030080e80f02c580504a02c5001e02d40d10075060011459040f41c5040d5034841c805400f03510790409030344403805030714600c8150802c14003c4804a41c0c6292491101d565514404034080003000d60413a0710800b014000d03405a910b41c01041f51850100c071980b00d5a0600c040c0c00c00480d602080c811517000100f86001c404500400701003100402540c81c510f02940040305185000c0c425500710185603240340760720b9014140c0c4418840d60403216a00c00c40c0d40242c0354040c2c980d40790324401c40c4103135856418606220700 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 136472185 1250 136470935 136470941
    0x120c17040623010e18010b03100b0402070b0a0f05012c07140c060106020c0a050109030602030a021306090503060a2c120a02010902100c0b010308031e01030303020d150503030d 77
    0xa0030065081c0c0b980900d02c0c40252250350420380c0f0549042100714248820084030b6a013180c000e41c000b50081191540d5003000c02d0300c684404094802d030726511004010a611684c044820741d682c0021211110311700030620000501061300300a000a2614001281401c40d05004c80220301003010001909112103005000b2204020b01d41010443c071950a0b49010f59100b01824a84e4944000350459605080e40281340481380680b640c07040d0200c80003081981d030480d1030700d82a240c2026001d65650307100707440c1e00040d04c50306164540c43c19030800f0010f46264080d40000031759000320240d68860311340c2045901a10700010360081062081c0688841c2d41100110381c00d00d65240741c058070a51003d605030400e16400490003034000d07035155501d0b0021480d0604580140c0d0055061010344103846032524040003005000040030088008046a25074803400c040740c1407201031080d040d01c0344d81c491900402a4008000080030b03203041242245001c0b500410080644101400550500305203055074809 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 136473435 1250 136472185 136472201
    0x206040e0709031a090c01052b0603080403080415051207030504061410051207030816080d0204090f0e0109050c0f04021605070807141f030b10120c170406 68
    0x5201e100e40b000000600455008284c070700c0039200c6031401d403410460f05400c1c03400354041141001010098225090550185c0301c00d4040380e011030384401d48442101d01c008003102d0300043c000c044082000410400118020016104040c1e400204400c80c01ea0503180c0f0b0189034589a0040031000004d4803143c403e51000794094010700c0c1c00300d00d10125100700d80c6e4001c000c2d01e5041169080c60028400c50405115071158001c5080040410514549a802c094021196103104541d5401c00d107805201004003038545541ea0480704569440d1b0340d2000500518000d91602070721030030001714800990040c807802806940250160140700181020041441116583e06070311a0342800307043c161000c41d8112001251040e0010100203042011484c0b4201c0c003980040d10640e03000d4803000d07181e1141042d2025503458010803c11741c01c2410429406003175803017402c5804ca807411403004181d60344a07880108070f800c00d00c0c080210a444c0c0c041180d00121400720b00c85411202808100019890340c03120013 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 136474685 1250 136473435 136473437
    0x30903020a0b0a020408010b0117011a0f0a08010e010b090312250b04031b03020a1101090801020c1b15030c0708040803040305010b040c0e090612010605060f0c070902070206040e07 79
    0x18084041d566a010300c0c02040c0d5074202c4080d408902403101d82803d100b40f207007100c1b007402c00c000300003c2c000a000d0340e070405010f1302c0d0344035064074112400208040c0550300960b060503140c07030301d1790300c80c100080044009110b2a480e05102900000303094442000b21015007802034007401c54007904920461481e403040740344100070280b0b42801080200d1114038950300742e1040304030422134101810018542d14402031042c5544610b40c0700351000a40002c1c05c0402c183e8043e1030804a900c6580050302c810507070794042c0c4240d5000140c8401c0b042c4d0040340022459181d454500c000198034010300101052501c0d85c0440c0420810105401d49080350103070115070b128000c11490f00d510f400780c250942e00a07500443d8140c2d1103221443c2a49410b000b000f510784601d00e45214988041c100003800b282e00a80010700903500000070100800013900400060840039100941c1d40c040307076024079002d078090300e481c404500034080003085101e83d0340215620703150000d0405040500340700c6084a072400c00b401e204 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 136475935 1250 136474685 136474693
    0x50405031b1c240b130b0103090804030f02090718060503100306020f0409050f0402011e030f060b3712090f031d0a032307170604051009030f03090302 66
    0x4002402d01200403680d80308040e05400f860254400d000d440c80b0499007080030341d091804112003a2144040c42185042e050300208400900c20300580c020007003403001824507440098040300744282c140100810714400c3c2c6003001a5900c0b5030080355501c0d03d001746d11140c2d092411040084500ca00041c5401030110340b8600306050b6070f1760300ca008a80c48140e14180340e071400309080100c2a0300b449003641c0700c4d2525148041a2500d540020074030900e080400100181d10111000414882e9000001303401d90240c08202068031507640d00210381010341c048001010411600d1b610010810001c8229031200c038030074900c01284c400944280e626141c010340d01a42d113610f40c4000c90850303001400035078004d490300c0041c081412907800c1c001c0030039024140a840c40c100c080000450707402c01d0f820390181c0380e041c0907410b00f140c440301c0e401d00c0d00c3c0b588224030b02c8200c00d00340221a503001c0b038038a0080e4800c40407a104085280f0180c015030704070034406004103020f280c442400038065009100c105100780306a03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 136477185 1250 136475935 136475959
    0x609060f1609050301020408150901090b040602070303180602090f0604030b0708131704050a0b0304020f06090a120b0a0615020613150c030606091a0301090905030906030c07050607050405031b 84
    0x1003406ca8019501028086e07004442031040702035581c1135260000720007030091114060b140c075914101c07000a2b00040c102c550026a43d000c3c10303c254480444803111800c0796441c3c842905000c03010790800d45041d0320911600f00442991b181040403501101e60010a82003582e48403181035583e01e41c001c0c030310212200032218580009038000410761804040741c0b0015195801c000500c05002c02c85c2e00614600c12041042c000981e84425405507948070441d8419a106040c1c000310340d120032981d029050f41d4a41d411414104030010030b05a108040c040030070044156500a028521228100e8682c090b030001310200d00d8075840c050701031171030501521524001400d8604064202e500b5907442000180d44c81e0418451603501c041408014807a0071024112618081031381c081ca0300c418403070076040555440c44482003020600035290740c5000104119260314020843d02c50b158414a400c803545d0040d00700180c010b50181c41518180d4038007400a004200e4151000100c81640c0c1e541c5175800088a482 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 136478435 1250 136477185 136477189
    0x206030a0b0307080f07090e030d050c0d0609050a270821090f0129040b0d120903050c03060705090906040b03161d06100c0305070b0c09030609060f160905 68
    0x81d00c4004d10401000303010701c04105503200d04049013a0080c0f0140743c203100c2e902c0c3e0f080704000203445900e0700244000581e51914a9560810300c94070501d001031a051890000340c0c0305040d40158440d5408513028030240015142c1416803039019001c24141d0004a569180424a1031002c0c1a490f10000403c191140d84444000c030411000c03a4040c2199001c0305003412400000e002e07540c590054014140646814184c1c1c00d068003200340005801542d4500701c10031140e694200d20f80701180c0115903190f03042c0602c00f0041c8198014041a80d1510585100c0c010900340002c80d184280b00990f030b440d06200741101000044000034110030b80c442c0d21000c00ca04299400c0c494a00d0380c1141e1240041c0c028036000c0740c480c2c1142040481c0112032140e00401845450301c40c02c0d044e4001940c50001c26103110740c82c054642d8011181c000e071014040804004480c4001c0c0010195402d00701c04072103075a0380d110f4455640391021980b8072078002020000c102c03803008045808240301041d0400c403000b90b40303c80c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 136479685 1250 136478435 136478443
    0x80a02090306040606061d1005070501110a0309022704110f0a06031b0c02030303010504020c070e0403030618090c090507030e100c09150c03080c0702040f0f270206030a0b03 76
    0x107080da0350a54518040012a40008802e1b0b20b400d0a0003400c0b41f170302c0c2c5440005e8804041c1c00c40c00814000e0024013107080000c203522030602410311300304198851441713000050081250600490207030b00c0c0340c01c05c524030366049411412003214070740341c5c44907954031592030711a050220300c4210f802000c05040e514113540d072402c1c5000609401e0340c2c00920115074441c503400d8020350203103090512021140180158502204403815940300b075801581d02e4800b140494600005e5034890395021000d801800f080642c55080702d400c8858002c0d23003e084104200780b41c4105d4010040041c880d2616100822900d07580380c200311341c001f000d8180000e803a009404034504101c1d032190200801540c3d41c0041d00003541010140c0042e266100104002c40320044004d44444008100581070256040008011b10100710032541c0d045c5e0301420030301c400844140050003800c524546261010b041030a07544050a1101d0358500e0070303018000448140703500b07030280026580040d044d41005500c50320710059a0714108 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 136480935 1250 136479685 136479691
    0x1618080d08100f0b030114011b05150c0f07060b120d080405010e060705031918030503072a060509120309070e0c0a1e0e04050c0c1b0603010303080a02090306 69
    0x6160301c0030900d0140000074035018181c20002c0e405840490038000c0c842d20b8026241075402401e00d01d80001d81d00401038a50004e600c039140c8020504004c28001c101010529200e00b001101a01c001d58452200c8504030f070242c0c41034980a03900900990000c035010360880e001e16200584214100c010924405040a000ba040c840100d07109805101c00c01c88240301d4010700900303810107010305060410b0700a1451101a1020030301a58002c00c414080c140765110b9078940d400f103018044400c05514018015030421616680410741801e130b1011000c190303141805240d84900c000f400c5070300059481c0001418042c00240781d52150490010301016440001c5004490000c02001d049280c0500207a0100c00203100c20b80710307001072228544107500450000723801241800d5031a00c1c2c88101c00c00300c03240035104440315030007410901484101180d481c0101100031482040e40c2d240324031524181103038460b401085070804030400040001c01c0c0f15500d426001440d030b010140c43e200381040080d260030340503 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 136482185 1250 136480935 136480937
    0x60112150518040206040605070c0f030308090f07030503040501032c011b020c090103020607020f0415090c110d1803120e1813020f0102160801050603151618080d 71
    0x308244400d16000302140c2031480d075208103000c0b500e401d0f4086801c0d03014901c02d000c00e0040114051701001903411000003d050b607c80326007215641c0381401022001c0a4851076800d02403060701d00d404440105c1e081060360f81140003545481d182a004400a100280402c0c2a2500001c0d004051080010b040c181d44048000003084144041200800c04002180300d141550311000c82150103803074039000b45046a8040320341545480c7e0a001040d012110307018450350080c42e242121041c0c0448294110070b50304a0401000084003d00c2c0696030711a100c6ca68564550100f050305520343d125000b00160540c81c105490305940c0e880d82e80d031401c03458102c0c0140108240c02c207100164140b41911030001d0200c2e00c0800d186040165085085840860001e4040c4103015074514103a4002c000e242c041407801641344004a650b000b2450003841e040d5615446800381d484181d4400c0c3d940d81145000b00140705506520703240c11001941d8000c02c80102e02078910312044005a4543d050084075248296 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 136483435 1250 136482185 136482221
    0x60c0d060f080f0609030c060105100e04050a090b0604020c03030402060a020106030803040303020d050c090607060509010b060409050f0702010e0d031a0603010608160504060914130501080708011104050f0108060112 94
    0xf80d078002e5418000001e10340ca405034400c1c880d06c0c882d0350f40020a141101c206640340b04000c41c0380e8504407030121903040440d803c5814a41405a10801948000b00143c0600007100340e949a030010841a8483d4011a0b00c460703005001040241c50305030300500c0030324024000000c0aa942ea51402d60b160012602600401d81c04515601d10f0304d00c81c000c0980c0302040003001480c002d240030000759540100403025003803641e11400110040425442030320102b60041460740c0700c683d41c2030f84402a01044071214201c1d503050020441403801406600c2da40d203080c1d03010340204145608220010040d203484440c0c0d1600750059868240c50340030040d80600720070b90760070b4050b140c5400b040740b54240c641c06039803c01c0000c210030004070f980a0101c2c801d41c0e2082c84041d0200c0c01880004e24805034466560030828070700800001c286800080e03a0b821206907900a100070494406000d415001e28443d80381c1200003400e41e00040c1d8400d4801d50350003c1f050610500d0128072245d504201e912a0f9424107202c5a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 136484685 1250 136483435 136483453
    0x16080a05010506040b0904031107080708030903010e010908070f0f020d03030506031908030115090302041103270303070c030302070f1209050306010b0904090213020705060f0a020705060c0d060f08 86
    0x300b80516a0f02000030f4900b441040b03000c501152203490000e00190400050f1914034812100600020005111510450303d28135252005907480b68030841074580b1961801e00b6007044084180141c5803100e0f0488400c3d42440d840361901d90b10700c5034001080b19415901c1c107034140183d44440c003c004040c00703541c000032a4a0a5000d0624001e04c40082010300681020721000284500c0105e0741543c058200140e078901504a00f030300d4501d042c0d0802503200341458014480925080084d6101e81c00c681007604030042d4042a40090840081c0c1a04041e0410800607841e540201d5040c54110300c2460018034203182e603111140e0014081c4000c595200700d11031030b495041d074850f60300c0c1c01074142100603003040e51400b25440382500c00c0c0a1221f02554032011100255940d445030b01c0001c10f000f0702e0640d42c400061810580324001103c0700340b414400d01010907201ca515100743c0c1c8050341d02400804550319a140d0300791341500950303154400c0316154a00442c43c0d40072441e04000600c402c2c0003d00c4014 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 136485935 1250 136484685 136484693
    0x31202030c131d040809031204120507050a060509040507260f1b0306040c0c050607090501020d050a1205040c05100518010314010e0a02040b180f0102010c050d020c16080a 75
    0x61015070010000a40040f102e80c080d030040c0b00d01a420a601c03444103540d0b600c03540c001c80c1c00c3c80182c46c426200e6200c0490002505800c40c0c0e02c10720407a101c0c50948921580390000c00c030101510f4011080001c00500c21600c05041c2a8800303038006071507041141d048103001070417010743c61021546252619101c001d0001c040060404a0740200d02c12030203000111525110100360f0100a160a100e0390319406c202a074103000b4070f01c000e0300f190881c1c1030f50744d146050b80e0040d002c6200d0b440360b03d00601c41d2070fa1440c2c0b454415815038552240c580c2d12400d600160558600242101402c10f0b0781240e4a40000515951203429442c3c1c0c1e5200303922200d445440e00c01940340750319502062241410b0800c070204c1d228040224445055038a00002c444054035040001402030041c2c3d08000200c0400088240c1c02c0a0031140e070984140c02200c1780c1190aa51800490981d1900030740721020a2080c4100c510250a035005010112442800c1340c80408600268101c042c0c401c0d0b03c43c1c5002d0704030042240c240 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 136487185 1250 136485935 136485967
    0xa0f020105010522020405031903020d09050d03030b01120c020f0c0f060702010807050d020324040c021c0216030c03020901090203040f060e03121519050a12031202030c 74
    0x44001400200000e40c5010003140c0400ca0704134500d2210a01c05651021140d0150b05840240c8000780845032102c40a5206100f00c2d600200142c0140c840d4100c01602c0620500b072100035900f015000c4040b000752641c0036009000c1c440c8034581440340b02070804452502038814241e100310580d00030091024038a0301c1a040c0803600c2003c1e07009210300104102c46842d040110b992169083c64500031990301d18900300c5140c02075130000b2014030700010620041c481c0180d80114005040340c410f400709a088400c03c0100e801443c509800350300245440052100c2d40b40040309414000d00586140880c60a03081c0c10910260300111120702d11444d041c4198103043d403689008d04032451086103141400e44a08016080c40301000305819280d05c0f9081440c1c1d4141700391664051134480507030450a00910b40c86030b1031004c084103801010f0182e1b4551030003081107000700499002030401c49034141403006c5000301c400000c000b5002d100c009807400c4c18801403403008510465805900d41c1c0c942d05014072135014 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 136488435 1250 136487185 136487207
    0x31903030617010e0d081306020c0102070b0c031501030510030206040305070f06090e0f060406030f030314070516020d0f1202010e0c0603040201020309010305190c0507060c0c05061b120901020a 85
    0x810380c94012442c1d1312480024008004407500d041c8400c40d9514030b00c41800070722100e400100b0701400402c0040121005401030040d0601c140b24400590343c407001790412031300088688200101503c0c0b004c0d1040d5000e54411a08400e110400c0c1083c0c54590f0085001540f0a80c01125294800300040040307080710100d0401500e00c17171600ca80310619250000c4090b03d8087e00755030102900d500810300c1c0d59240c0c0d104500031680411189640340035410050001e04601000d000d20400307040009070014861822100c440b400303200c140142d101c280e0280084c0c0981c07031100f1584824081c2e000f0b00414206d00c0c285400c00c03101e90001c10741011040c081401c05940f403125500980d82130090200503038021094400841081c43c000400d562045c00e01c07000c0301c043c542052506860080c0f003000300c50380100142601400744105009003620128101c2d01002187c00140c4190011008648213410035129050490140d81030f61381400e1800360080748801d81510212081c0c0c4d400180400140c1e0410000c1003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 136489685 1250 136488435 136488479
    0xb04050c1002032205040c051201170d05070503130806100e040308060603090a0c1404060b070c0312020a0204051806070801050120150109020702150f0708090319030306 74
    0x34001d9803006010359039001d0040700c211407160901e812130002d100e9803418401040028810702415100a41c0a40309a00c0000f54490042d082400881c40041d4155803104070410b15004000044402004440d40c1c0c000700341c00c40c4c0500017004141c14030503081103688003800c1803102800d854180404016103400301c55100d45408040003040001003a0401c1155a11a00940c1c04030354903034800700c05604101203240c000300f4100c00e98502080c02010044900e040d04815202003042d280c84481481c0706000c0c01c20002e2092078400707000e02c0040c00d542c01ca14181c0445004881c2e0b803410030750000f000d6400858003024800783d58012040c9940302000450740120550908039003650400c000203000304c5112070003a21941102800503d0554104021084010081da40350655619410958003941c0a1082640f18040b004204015260303072800711040c0c43c1282c404145407010580d103000a41c2c11000c02194140200840c01c034194610103401c0300d4031807107580c00040d07280c186205469181c40c4107070342c1c00c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 136490935 1250 136489685 136489699
    0x1170706140909040809043806090d0c0f0602030304030e060c0a11120f06010519080d08060402040e0702010b0111010b030a0f05121b070b0708070609021c0b04050c 72
    0x140010718040841c1c408032026180c001031036031a42080900ba01c12005501d82183c038007503045844c1040102030110b44003002082c03031011010024002c01c036446464486621480030400071000d460807a030110a541c0c4101c0040542c00e6980d141031040713114590059000d03070000000c0004040e446401d46046a204540d0700d0300b48547d4078081547e41c112844020400700200082c958141c0c0e40d020313068101c000300004c840c1c003000034491850b21a0820b1080900446603001203860f03450050340c4031030580d0600c4004080081440c03004840940307001c2c208a1700103038208000301d424a03200d0350041c0718045640002c1801c49a9030001004050b0505044160742d151803104095582e0119006800540044a0601480c034505081e414002003c0d5500000540040d40ca948a400d260b00c143c1d403141e00c10152880c1d00d56404c0507141034494810700601d946010041c460001c3c007190f110f80c0c0550b00242c51448044031203900c09940c0404100241d8503000743c1020001001010881d102030440305403196 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 136492185 1250 136490935 136490957
    0x1020607051c0c030e07030515180d0315090603030314010e13081c0608070e0a0203010b07031110061d10210303091a0a0e0115090c0507020901170706 66
    0xb0040307003041c0b4590580064541055455030b620030381049408501d00c1c02a1060141d603484c0540d0b403440641c1400c0e41198004000425041c95554030010400340300d8054591020451401c40080c6800c0b80141c017500017611002c5400c004900c00d180156102e500c0c00168510b10310840c0e00c44100581c4607032080b402d031004102503154040d445101c03803030348404003d403540810022101d5061101203c4001a858a0f1000559150005294007102e1a880c8134200d5501e884645d441030b8842402440c0790b0800410140000030b103c0e0224140c0c4c444440d041d120643c0243c80184142c3e02654030010b00030b00c0d14440b80283e181d036003c40310740001500103070040c0c1d94603018941c0d1443c944c01c002285c081d103421001d14140b50090b005041ca16a100400410721a1001c00c0d804c13130840d0a07111384000307a107840401c41000304140316200032000001e002c42581481c200c03e101c003030310f41d12101d0800c2140a008070001038a4048010340a007502c401c0b00c1160806003030b140c501e000015444803003004020070030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 136493435 1250 136492185 136492207
    0x8070c12090501031a030c040906060306020a050702090a1802060304030513080303010603060e0906060105250b15030a0b010e070e03030c030414180411062203030f020312010e220807020102060705 86
    0x3039002068001d940100e6180c1003810030400032f100542c0302500c40c5000044c0b69407a194004007c180452003100c50001d242c450000040c01c480c004080302108089015174540507250980195511501c00e1070081c1c54040780f41310303200006010b51300c007100c55800400180101d58043c000c00300500710001d000341441c606809103035a11140038002d24148100001c3c40e0071038507249002c00c000b540c0d1945a1024600d44d83c07a2070a44841c04503243e03150300d4036540341842e1501c0c02144a0300e11603040280e019950742448412450b04002905203402d010003e44251740540f001d002130000600c00c0000345446500d45000c02e000c40100184a42c800c0b42241000e1102c60b40e072a01c901e401607003001d03411202200d658080b910500c2078621540c2c2c100a00003004400300e4204400d0b6041c0c80c0302c2da45200810301c512100780e0356030050500d12407031404110b0050101c1074168410903403045003070f009c6c281500c001300340303410414509950580b2608000a020000c0d56010066070390040c0f00d600d07001d40b82460102c3c0e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 136494685 1250 136493435 136493443
    0x150c03020c060313120503060f101e02010b0406080303040b0a020a0f110307060204090504060e07050d03031a090702280f060b0f0622080102130608070c12090501031a03 74
    0x20282e100e21004008540402803d6a2003802503501c242402000504940b002e00290011035101e031217460350080d0070106003486082c2804451154846212108441c001038540080785d0140d0303c115940c1d00d00a480a079a1405080014000000950380d170b402d15080083e0321860003000101454010045103926a0303014a00d100c9402e49460480c1d8034840c41c030b1000c1e04501c6003540c090709950001c2000300d0585001e9000d02d0140303100340c0040142e01c0085004e241c40c0d0341c0c54403500b80e100f031940d0501c0340170034082e80008000003170340c02ca00c1d0b21201c40140011074107103040d80c851300140d100452400c590903ca01f030900d4007038149040b85030640000d5132003100d001189400140b415803110f91880701138840d5403038032120f914020545501d580c0c03944d0041d42c809240d4407a81c000301c880f034140020002c0041c4200c42859200035a04a9601d003080340c1981e020307201030302d40f804001000300307070324045400242c284805050b190b860b415203603d80750004054410300301c01d141c0c1001d01500012030f0390794005 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 136495935 1250 136494685 136494703
    0xb10090e0c12011403010e0703030504051507080c060601020618030f0d020c010608010209040c0c0f02041808070501020909090c03060412090503070e0603070e131e050115150c0302 79
    0x18150851a0759064008a080e029081c0e42540c68040c610000c02c40c100040010300c6000402e030000c01c40d80125200c1103a036040d0512000e0f001c103800b000240154203101d800250400e80c981e0359981b90100a607a0000254010f02d100c1d00550082c1050005941e4188a0a17800041d10200c905000400c0d003040c585070310403140c062003446800034450010b100c00707806443e00c11407000d0080220a950360318a601030360107202664403403441d10040070030f001d000305540f540b1035401280b9402030034601e40c20701004105944e01d500502c11400c00200004619200404015110707000140c1c45610b401c003401940100078044070305035048481c0003980c507180003a5140e4050b4000521194508000b8000c0d60003141c243c010390342501071200b010500c50000c0c1d4141e0700601065044a18080d560740404540a02c10380c2c120300c42688d0004600701082c0c0203022840020302d01300e000c0c10503550756520346007181c0c440345408030b483d01812003c01c0060000d20b00c01040c40b0807400c200d5890552560025101d5103a1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 136497185 1250 136495935 136495949
    0x30b1008100b011115011703120402130e070b0702030c0108010501120507090f090518070f030f0201030b0406080a05100b01050d09173103081602010e030111040302040b1009 76
    0x2041ca81d082d5030700c0707000601d5012031100c0c1030f00d6440c060820301034112038090081c1008103165040c903d0003404000110760030000311107550000c0c0d4459508000750503440d013142d8910706840c5c0d007050250040a02c0714000802a4084082c1c0e030340c100e407050605104000c42994140b08501004100303690b0001c640300104042040001a6640c1d603203410b0320704c07107840d41201d20900c9a000307000c0399081081d84170034000c82c410a009503003404d000c0c000c2540d441c0c2c2030182003882a44034004000090204010f0841144141404912060f0110115040784d0165100c0080d9500009078101881024032110354855074000b0280005880000042c1c4a4450b5201c05030707201e03544219140501c041161440c0042c1403210f20542c2d1149400010000145003035151082101402c1907103000c48100b4015804483d403142086081c0f185030788040e07000b49800c401c2030f810320452070503607069070f6000c1c420322005550310b0354490784483c118014441102c03040301c42d040c005c040c00003c0200043d04080710700d00715019 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 136498435 1250 136497185 136497191
    0x100203010803030702150c092218020f1009170f06040f0213060b0f07020301061802120c030108071502010f1104060e040b060d18210807080f07050c0f16030b100810 72
    0x40e09c4191842c07009180700d0341010749040001d1000588050000c0507080c02140c40217800008602081a03036400e0780c540c40e001c11304ea90010490a152600c492001c5031a01081e241801a01229107042070344c00c03941110380e0380380a2481c1086250000345181242c110300000c12280341005900000c07440f0300040785000d003d0110b500c50031503400f500080050a4081c1c0442c011180340a103d2020f904241000420010164000750340c1c0340904050343d0403102c00c00014007045103044800703170010105240b00411075407a034007001150240b0b8022680d28415501000740da45140c0000207065510b81c0c00710900c01e5003000b40442d06035480da42a00e1403060082000070b40000c01c485110240c1080d660020030740411502443d90801d424642c00030400c0480d01d42d48407a40d03031f00d0801c641482c021141c40a12040c540c010600c0644030b00090800b080a18084503400c50a40d8096854607c0d01801a015240180c50500411080271144d6801c520b4405150380d495042284041c0c0715070100311200200d41c1c1d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 136499685 1250 136498435 136498459
    0x1d07050a09060e06041d1806220c0e1006030c0309050703022b0507031109060d03030e0f0a0b010f1406030c030c0403150c081501020d11100203010803030702150c09 72
    0x741c3c503030444000b0400040c40d00c01b008200d2900450240c4200e9107030801c1e4081501c0d40e0403510011030041c1c4140c400800240303904c41102080c40124019510a55801d4019038005c01d00c00c01001c40140929091a81c420010b450214020f090342d004001e01e8040500b4000311038001180089c1c84019030340d0444005010502c4064042c0410116011b07000030400751800301000d2100205d1680c060707034018900d1a200700c1d54070090040500042d01c8042c0c102c0c120852400201c2c1c0700382d1189024030359200a8484841d031101120703251034140d0106540192030f0341c0042016060b0304a48000800074270412041721440c0302c0000e582408020452009000700100040c80c841d50300d0209e4000c0d581c01040c3d200180c02a001c240d0043c01300849800129560402280004010041048440005900600640d081c4c001c0c100d800d4251408041a5803051a000003800300440c00510701070140c40c1c00454992074250802403812802aa12854940f110424020294035000032035680043c00d40c0c070408031036 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 136500935 1250 136499685 136499689
    0x10e0a060509030c010501240f0c2603090115080c010917070504060906080607030506060409091707030c030f080106090501030506011701080618160608040206070c1d07050a09060e 79
    0x80b0031080c4c0701d11594a880000f050a58480000e005030354444640020710a091600940740c1d40b1401d0314240114481407008400120000d86003900140c4c8182e0003903028664a800304031681041e41d880b82d2594481c60400342d1414110360140042488400806550803180e002806501050194854120072441c1d8040d140d803080014600400740a0420025641c6d00c00000c0000c0c050b500440b582070180401180c80d0520900685000d49001483c9900e443d103000701c114000d281c030010480b05100d070090810031880f12a4050700d110b40c041d455076a07040e00035203002804c01d00c65600c1e54040c03105007001405850740c80211351003554020300300068107403541e038010784114040001e5511021802c000101c0da40d040031400c980501c60786501c2e40740340200c2c0b8080903102d110740800060366020440041200034440c040c0640c002d070000c0c003010700c0d0110549844099122580211100301e40000a441030024064007091b4000c2003441c2c885d042070440c0c14003d0111416124800030080e21120a800507 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 136502185 1250 136500935 136500937
    0xc030504230f0a05010f141e100513060906051f08040f08070302070501030c03022b06080303040b071205131506260c01020114130c0b0c03030603060702010e0a06050903 74
    0x80742c11504903050300c07245241041c040c00d00c000700c1c0340690742840903c01c1b51503083c0c0500b40c001c183e02c40d0030602000d0303841c00d40090b52500030440c1c183c0750b40740280002c03075031100180d8803142c87e070815000c02c096040186050645040703902407402900e0488029640c3c3c205081d4031040b180c00380c07528091946443c1095440f81d8000e141c00350080c100020040c0070150002882030403100280c905001100c0745803025412401008003000b400040c00418201345600e20113051101800000e00060035503c9500031072940e041110100c81e030440017000c0c8508260480280503d0422800c03080c0250702d0b000192428444803480020003001621a0352070100215401420161155012403102040403130360300d080d0040316a602134618010030390130807415441030140d041710b038031001171104658595007117803d8100811082952600408140820780400001c0102588c0c22940029074990400c0c200701070038000042c03c29415685482c4100d0350f490070208075401c41d1030300a00002426039812125a0071 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 136503435 1250 136502185 136502203
    0xa0203060a0302061605060105101d0303250b0619030204020c0a1e0c09060b0f0307090801050708061c110d0c030f14070b030f04080c010b220c03050423 67
    0x7101c0b10101c0c2560041c0074045c01003400034081c90484000740d989205110301040d140400d000010713070040101440c0c8284040041a042e0003030201c80c0781c0f01c94050241150700740d500e2804ca0807002d8000b0031040c400204840d903046070b0212082d2400e14101d6a15060002031840000c0c0190380100b1440c1808809114040c001600040f0200078018610703130310200006c900704222204260580d0105840d18544a168140e40c0451700e41498100c400707101c5070b4990801841d40042109503240442d15140c01e000d20341c041c3d00c2e0b58031841c007242000c0c410000726206209040000c041c01c0400b0101040e8258807803c5c2c0020140e034100c00005042c107080708240c03516000030780007070b000c18888005c1290070038858031045a61011760350001d0715030b0581c0281d444107503440201141e002c0040740201d411640180812080d03032000044112201020654000d202c0c01011000c3c4103e07a00354141c0c040e01e00411030f001c0202d21701080989000e6954061000314041008070b00100400c00700e41141c0c080000100c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 136504685 1250 136503435 136503439
    0x120702030912030c1e071e080304090c1d01080103081305030f0a02030f030307080c09131b0311040501120207022209030e0f090f0a0f09030201021b070506030a0203060a0302 76
    0x40480c0492012550325070000441d44100d20400d00510400a010040ea8100409050103404c48900d019800d00c0c86508003001c036807d5028503600012044000c00040c0001d10b50882c01041c035030a05800030713040081001d2888005502200c0b01d029581e032118146066035403103480591901c0070150441c80010310317500156003620401655800c2c032940018003442403803084048828006c040400c8a0322030100703072a840302286150010640c440c0203040904281c0c0d1000e03002030000700e508004c24040c0d078410105550396a44054108030115810b0203040031100604255902d840c1ca4000001c043c0a6101c2c0400103050307010418004550b203d45e20041031400c50880445030810070306054004160080c81100800c000800001c1503040c80b1810703040140c0010107800c041d0b91900b501300c44040008210900460340c4090043c03840c102c61003000c01160180c3d0006848180002454540d0321628030b8184480d48504403c20450741c441044945c090078200002d41c40e52100000310300c4000c51604025 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 136505935 1250 136504685 136504699
    0x210408070e0108160806010e0403020a0206040303030b03070602010e070b07060615050d0b0d020a0e04050114100303030f02120c0f070213140f06090a0b1207121a0c1207020309 77
    0x1e0095070740e00e00c06050714005029144011106039600102a00501c03815045422080040048442c94102e19901c41e0090064450001481d400900c1c598816001140880e40e102c07640c00041c01c08002e0b62010789017030300080100d1400d022985a0f2140548980240c040c00040c4500800105401c003100401945c0a0541184800d8502034074582040e4170f042c4205242c2100d000e460314080f20070300d41031a0040d000701c8015003001d9402d44945002402500e03107640315030161000440e01347c40144a254288a0080c11078110719009040e143e24821200b029401400424442c02c008000e540d084000a006030766246000c00340b4400034000c03840080d600459038441c0d001c1c90109a00410714003840108508031541c0c2d8450b040c40b00311404e9807500c0c0c100680074002a1000035503030020a082500528408064680e0440607143c90b940790080c40c01c031100c44899800300070000300301c43c1c01d050804440d82030310720f051141084203020311041c00c0c91540821003c40c2c0014001d20450740c0210000d064a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 136507185 1250 136505935 136505939
    0xf0f030a03050a080c09060a050a050c0d23030108060609060307030501050907051201051e0c0d090f02040e0a0809090712020d06152d021507020601051c02010221040807 74
    0x140c0981c100801280100d1311280004001e228204102c820003040240018100307601078200b11155084540403906000d800c00400da0500320400242401c040144ea4064030a280420030410f0703032200090811505002f48010302561102052a613803000066036608515a80c0000003440c01e1455030000c0d1081d481e100a205400c075010407000140c4500385e0307003403c0380720609500b64202c4100b101c41d941c130b9615a491203040c03416884209e0b80c0124400d035000d801c20920064407400c64654503000c03140b4185880d2004210300342070054007003544001014140d5503c41d511030240600c500501c00380710391040c130000790580d40034100c01105901740303280864591100d4180e090061040740144421a010309040041c0644200c011442401009050000388011601c0420b0350203402e801e014203500030201400000c84044159520480b99640241041e5140009100704081042038008196020080040241c1d80018000c54a55800c81d41e07240303039006e800c10016260059405c201c01d107000750280 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 136508435 1250 136507185 136507187
    0x402091003050f0601080c030601121b2001020304050303070e040f1d0106090605210102070f1a091209010513030803010620030301030201020d0c0c05130207030f0216050f0f030a03 79
    0x30030310441501c1400f007215141e1800540700102c0c104c0d081c0c4844a81000000c40e907520501040d1259220110003080c4104c0c200f40c02c4981d0003611a00200181c44c2040c040c600820400d145204444e04030000c6186040c551910340d10307880f000349960284240003c6580362a16a03902008458030900800c01980b1160811400000c90f510880c04856082c850040b5180703840d031186a04840008024141d441c0c1203502c00d40c0c58004a004140c4155030a02450300403074001880070492a114501c292a00d01d25865182e0400d6009003c02a0542c803480c601d200940100c8201d4418100901b000394541c10f41c00c812900d8100180c000404400740071000140039500074051150110302c043c900e218601600d06040e680c0c0c0001d10010b40142c2c031401504054600840800c15480c0c0034001100764580c44401054850383c02c990b074207500a40c0021140e0625601545000a003c4544040c10140b044074000c1c4031850181e00441e842102c0500341003030980e03100c0c203182540e0200502901c81103804c42c10 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 136509685 1250 136508435 136508441
    0xd1d060301090203061f0e100c0b070201020c07060302070f080912150702010609050402150a050d1e06050105120a0e030903060f060f0105030403050a0302160812271207020402091003 80
    0x8480340100a110411950305051820800301046659201500390387c2040401c03005c15045182e01c018006040100310200c2c95042071544908003603000035986c0d14010219603e04400365000504151051020340e001880c0908803020030354000b010662035510b1a80040c2d21440c44801e89142032107441c800303405100030b05141c6441101c40350001c000b000d03a1014604240e840032100250700061180740000324007641805408410b003a450b091703091120b00c070118811034500c8484400808078204407810070718254060a8050038084ca4510304115803462f10480c2c0b9400030304060380da40e0700c2c1c884524101d07100308140c400b00c0100030308555840c2030005180d802c01c2c005a603164050f141010308a003065016000702d90240d43d01d41d80705480c048071010b0860003900152800d41c02c6a03c2401c9240c042600300d005050b103041c2100412202d41800840004036032140900c0203010b42009412804910010944503d80d02020342c0781c5603501240c0c400200244a07422142e64000c003111b001a10040d4158 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 136510791 1106 136509685 136509691
    0x120102130b09040627090816080304021003021e030402240d050f06030d03020f041d0403030e011e0e07090e2506020d1d060301090203 59
    0x3188024140c03110741e0181d8200100801e440c4014034140c482c250052100754072103050350b04007400700080141219162010f0301e584d4165032040c01070340012500803030445149500d1080481c0f5140c0c4054100762801c0e809a040e0001040c1030314040d100302c5500c442e058050441060043c140302807550710003403040f60070840780ca0b0034101002400c2c61100d88058030607040d58440f80e0f0b0114003021900000c01321000812030400780002e03520082001d1021803043c0c40d016a40d91307a52112000b0030720950b0701601020400c0c800707030815003010f401c0e0385008030b20a682c2030041c009411522403c0e503c9044954038803003d0500080321030b0f00745901840007040d040b4252101d440d643c03881a412104070b40103c40c61a0007035084404c20301c4030140e0040f4007252142c00d0b80c110301d007006030096454404149002c1800034a0000d40e0030b40b150000b0301d42c0c2c003e000606142d529038440500c00301a420607 = true := by decide +kernel

theorem cover : BRFrame.Cov 136330935 136510791 := by
  have h0 := BRFrame.cov_init 136330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 136330935 ≤ n) (h2 : n < 136510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
