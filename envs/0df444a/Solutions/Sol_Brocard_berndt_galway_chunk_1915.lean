-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1915
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:08:39.443626+00:00
-- url     : https://prove2.me/submissions/7f6330b2-5bfd-4e11-8ab2-7897ee626d2e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 344244604 ≤ n < 344424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 344245854 1250 344244604 344244647
    0xe011a0609153411060d0b090a06080105070801031709060d020706061d0118020904091203230408040509180613111f0e030a021c0308011a180a080a03 66
    0x200904003c0c000d01180710303001041004030790203220612107658080c01d481044d40e03894000e00b104907210303a060980112400040040d07043e28000c401030031100e000e421f000400c9180d40c01000031507910350050000e543d080c0340c015541c104610004049100741d02920030100e002041000c1441013503807118044074101040000c200c030f007800540320505000d0294020b680d048140c81c0344d10001c4c0d0b82c054081028050030004099000361201004446c00c43c1d03101e0002038071a0b45082114044180d4400090b1000315511000d042c59a02c4811a008602600d4020713030f2076400082e501044c01100a882c0c200c540305851850910000a01c0c284403240001c0e2a0000e490b030040700c1c04c0c14510300c002541860741e5103500d5080309011007120003440043c007081c2c1c588501d02c800c00240c5c1e9445001100d822030700b21800000c654a00e805008d003113050303001003007d003103800c0d40d0401c0c801c400301210004404400c040040200350300010340c1448107900401c071b40d4821031588500305500312800e030384141c10b0000c410 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 344247104 1250 344245854 344245927
    0x1505190306051f050907120b01030603020d21030902010507020409081c1a0603070206181f021206030a0b0403121404060905060c130b030c0c061003060e011a060915 72
    0x4a0840c152a1100003e098918801942c4015400f0188541051502040444ccd40e42c000030344000d030812056842c2a1940c400843c05c07440c01148203c40303c5142001c0c464a83c02b80c0001c2d0490281c908085e010f6a00c40a42108108418040301e03c0e004030032008200c50b4164000080052290701001c00c42092803031040e02891030b00109036841248240c1c018880b07a0795002003c25600d904446c80c000c42d200d0104195400749580c003070342c49000078000d40140c95400e844500b141605004c1d0080b4003d80190b100440403030610164140d000e0782500300fa40e840b03805041450024003405540c03a201c40b0701117003800200402904581c950600400072a25103032640c03640d1400d1441840203144403244911000c1150300c00c07040c091548031860120550401402c02c2d50300d4140407044402010100c000b0509008000721403040c9101854031000030407038040050790900d2400a240c5d120303449030f43e002c20400d00310707603903c4000510080c000c0f40490712000106544a416000444044c64038041007020 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 344248354 1250 344247104 344247109
    0x61205010609030b0a02090d08030c1314010c0b0c040b040e0105130e030412030e040c03150605030702032710030b120609070b03040c121209091505190306051f05 71
    0x50b901a030b0341001104000345c9803c03070342200a41c000da130015040001c80c0c0b01840416105409144103120301a80039546c0d5024071912541c0d11541d40200320405003141c40c00348540d9110f410700c02c0b82c66121000380c55036111640004c0980c047c952090340040000074002c01c0d2030041000b203a04841040e00c08003299a404141d00054035a1283d8550741035000307102c1084001080344209201a0181c00c04490b401c070085c020030151500500030f2008a9240d43d010b44001485503140c20041015107070050450502a40080d124851500481c4010076003142c044055181d407441d1480100f0010b0040c81481c41500003c0c3c06400d8450407103214407003405885104600202d2031381d106503000c40107446105d0500b001c0c03c0c4550000b81042d0307440d200e0f10b4000b140f007545440c010420940580c805156018040400415098442c0c1140170102c2c204408546c1400590386a00c0c1a51006c84039043c407400000a8903581c454568400b80415007400140010b24140e0000c40c0107070032a07001c03001000e5807070f00113 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 344249604 1250 344248354 344248367
    0xc07090e0307050c01030b01141602091602100504020f03030c0d09140102150411030303191112040b040201030e0d0e03010f05070c080c030409110901020609010b010e060705160612050106 82
    0x1001d4207507000000c0c01c00096100741e1045408a805041c00003941940c40e564100321307001a824010480316032b0101c00c007545012080c41d68080680c030305500420000110080d1120b40f0085240c000c2621407001c90b08547c1c03007840030301d0095006000c403501c401711200f1007941c40141c0400400445d0500f51f012901d100103020f0100440810380061042528601c00e090b28420014401d86040380b00201d520b0065500380010340c022048000c0100c1c030b4611140c045004c450748030703129070034640041007041880f4a10102c103035405600014840620b94450005030090000c051a4071068003441c11305800c501d80100e0520385c202e4069000704600403280c400d1b04102c1d40305642ea90081803526181e0310024403110004c100d0301c0c46100a880c1003681e01e450000581f880d50012961280010030304155550381003100d15032052000000b4411802c5010000e013205404612642c0100000245581402002c10140f200f0711922007d1010b103944d2003400404030b004004144c0041402d04000080c8988540d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 344250854 1250 344249604 344249617
    0x61a152208150a020705070b0a020c0901030209180c0603091b03031812010603051203071205010f05010c030302190c0308010e06090606070317070908010605030105160c0302120c07090e03 82
    0x204548650451201100400140f80790503090b020414800003407000e008000040c00040d403059102c48010034060304201e04115218090400303c2c00420150f51107940c4650405140c000050191105000c003c0c14003990f0700e038103030300100f0000600c030240100007050040e06c1601000303001c81a14a00405460f842041c55170100d400304004000d00d646001d034245038030306641c0000024801d96a60f280750034a07914501641e641e00703000c010001c0f250782040304503075400b08070101002a0340c10b181c2141480980c0f0b00910f410003129103420002c050013581120046801c001010301d401102010040082001441c01c40003e42640000140d12000c0d00d00d0b41c0c01054010603d040907030303c0e803040c029140c014450603420003821010405a4110f040303100c50007023501e07075580781d601400c1200300760035144141d228078000d81c900000c00028400324178002d0104040c514000b000c5040700c0c181240b50ad40421541101c818002940b40c09411001650030119213007850309006181444e542142c40e4016107 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 344252104 1250 344250854 344250869
    0xb070323010603050c1603030b0114090d0312150b041401110c0904030507080a0e04060f1202040213030213020904060617070f020f10020c07050301020301060c061a1522 74
    0x144010300a15000b5042140d10020805255007049030442c100101c1b011030030f0065000c00d9481d08003503540c1d6030010900c000758056116040c608040c0d2030200d40310f0251140b0150070440002540d500304c14494006881c44101c00c012415601d80b226035160465210b485000b0600001800a200c1940507440520440401001410020141009009101c240200300302d04001c4c0401943c40043c81c5c0074040c0900780703c3d580c5d907001c8038800d171414041255078a401c403554003003240c0c0c0204000008186400d141d90b42c1030342c0150321107001350250240341e90300f0703000250310510201596001c0c001d181d000d89141182102c0a100169881038155081503081010f014007001c150001000303a405511500300407101c03403048031000803144407210b06006000b801d1003503d540000e50850301210801403c0007402d01100214915450210082d1520452500040074252103454240d000001e101508008407070103042907030301481460014178680d00502c100d80300b20040382041c81d10007929082000559601e07 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 344253354 1250 344252104 344252171
    0x5040c110123010306050604140f0906010b0c0705011101090c0b0d06090b0f06030601020c1002151608060d14010c08011e0e0a0207050c0a08070f0603020a090923040b0703 75
    0xc40d1036800161a000344501c3d0069141c3c0740c0305d86030076104220f41c1cac40f03038001000c500410704000c00c0041c00c0000c103900c071089003401404204080c54011602c94125003007400c0c844140750300918a680174001548010300907600510700080c1d207840c604020100141150020001641c0302c020702c10031268811300903500320000100398445070808600854000c84140112a02003072000e0000e620030580d0f1800c840181c0010343c00181d882c0c00c01c0c120580002a10401480308010140300a010f0b4400502c0c01c1d100e10300140001d03050140b8a0380424104201c0002400041c00216020309214000c4c4140c1d0005c03500d038400c103444500030f61070700740643e20f0300d200c104140d03195040124060f4206950a0b28607010341004448681c0d12500700c42c004190b60400343c0700d01c51800700201e03220802e40c5c0c00360040c540108880c1c24102d900c030007885c06451030707031304001110580c0010440741a07208101c0f5016056039203061000348038000745076502c02c54455409009100d6000004141040244e001c003030001d40d03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 344254604 1250 344253354 344253359
    0xf0405040c050c0a0528050c090c0c07080601060f0503090a060b060c03041805100305190c0e13060f022a2a0a060801030f0b090705040c11012301 64
    0x405801c2002415110b10b0154103202050201c1801c001980008881c40d40c000b00c41c070b161401c0704241d104040b004c013195440300d400f0240ca8a544410301d41d59520f1041507528001808103d9160650b4100171409040321004d5454881040e170700e07102802440701080082c880400450300c03520031a0f218048450180c02d4039400c9030f848070090722041852a81c082c0d0305000800d5000808c2001e0401454680e9a45940e4001c031034900040303c00180c00c0460002d00d100b41840840c3d000140720520041401ea00b000c58180c900b01a103698882d41c10810745c07080f41e0300a2003010030345021030350f03680ba00403c020490402c1d0910318074128843e84846161001e8400e4400c1286401e000310741d84d01c03107004003d0b200d070800245884046003048a0100c04141d00340c401c120b4003410407055003c05824241054007081d410344d00e40351b00e1440c500f10000c20840480300011580c1005105c0c20f0700402014005020303004003010080e14068058020140b15840d0003070f94822103c4210002c200c98442c01c1d2030500c543d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 344255854 1250 344254604 344254609
    0x718140102070e0c0d151d0105090c19120b0a060c030f050901120b061e04150f050909070207030b130b0604060b040b0d11120610030b010807200604030203091003020f0405 75
    0x614005041646c64540c100051760248090740d03403100350b40e6104100d8066050408021f007502000d4981160150184006440c2c080c40080d92180440740b8145040021003090405c006842e29500c3c0b0368202450718000940b840e0002c054400c81d40c441d8503107021a0807500400c0f5003d004002d0f1150008100e40c04104007500ea5900100e25000045d000e01c0c60301c00c0400b000350082149900d01c6944040000b4100600725116000503141d02e07261500d00b2130f450010100600034010078a003a03208980510100300c038607000304101001140d201c00130b084076150031500100d110209510544d4144c5140c000070309903203064424401540c10905c100380c20706042c2107200c042c0341c114011000c90207030740e424406601b541344130142416042032507203040146002414800c081e130303038510030501303150800300c0d0785145a030020310b003130340c00121841d020845040c808150307443c103811086c444840e03015150600091560100003448145000d88409401040407a0101d0803441400414951148240818041403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 344257104 1250 344255854 344255861
    0x18020f060d02040e1513020301080303220b040318090b060d091a161b0f060c02120c0102030a0c090e0c090112181b0f030b0718140102070e0c0d 63
    0xc0d0340c000d4014101600d41c13000300314486041e900c0c3c1e0000c018028049640f03241034120f1100c800850030055055525242d5610ba480c04060031406502c1c001040302c404e1302c000040c1c00d03011903030407200412060509050140058024a1580070f074aa240300c804103015105006d81914600302030702c99840c00402003c0304d0010103a01a00703c0300400c640300c0c10070360420607200f680d0090400c0d10210380304c05200382c1c01030405103030308070301e003c035494002c1c00341e00400d41a4503461805e940011000c103005e41500b074100d007054551411070041031000b003800c541c2001c2c154041d41c0f00d0004148100402c0a0541003640c1000280c03140340c0108600c1d4000030103594840000d02007454041c103048203000380c13194869060b11a4041c5540d5200520044241400b00403030016200e02000b00480b04420f0504191400c15aa2400003510b108c0c4250081000d280c41105003003444200c7c041491306807a01c1c4c003110301145d072900c2090303170052040850100301c3d15440c9241030300a20300020b400e803a201c1b1000064018 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 344258354 1250 344257104 344257117
    0xd0807030e0d081207031404060c11030f090301061d0a0c0e0a080313050109081e0a0602040816081218030703020301020309010c0201180308010509130f030c0618020f06 74
    0x4100c46504103190355110b500d107081c80300e48a807010b15210a0602c401e2104060010521000c142c03c1100c0301c00c2042108103915080340d0007800104445002c00c000707480208000d01c50303801d140310000303102118685000142c1903549080b0020311819603108a0351b038100419590b074000c0b48140340c0200e0b1008446a2200f04190454204244010f00c840001841d007445980496401e40000896603c8402c84812002c040c01e801d0030200501c0b800d2201d2030340d035041d1000c0c0c03001090400c401055180351080240c1e05c0c036558004d0f0155901ca89880e28183c440e24824a40242424140408a44088089494000b030368203d020b0310b092001c910641c0080c00e9200002d140c1601030f051011015882c01c0c001107100e0705000e00040b51501d141c440080c21103283e24070101d200c2d102d00c0c241400203039211409504541d412074400c085a00d40d10070700c8182c004c1c61b0100622541061140c40109900016151482802180204045103100c18a440100c0010f08003d41c0071604c0c01d100e44140ca07000010b8040d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 344259604 1250 344258354 344258357
    0x2012f011802151e040b0a0305070801030c0501030905070e04060207140c091b2106030c031207080c1c090e130b06041802030f15130b010510120f060e0907050d080703 73
    0x804007001d101810b469172103900600c45110000420001e440c0e010f0003803603003180d000e2411520704d46c0346031100010381c2e102b802071504050f00c030040e60007401810008000541031803d0800d4245c01c0c646800d0009501c800402c5421800040518007145000f00721024617090241c40803075259124216003810504030050b144081000340310300d26070007441d415a00884e035100f103171000c8141001010145405e2650b9040e604c01c0c0d0107e094100344981640903500040c0c0d002006c1501c43c08072500d00b900b0a22041142c2c4203101e40e036043e0703405c01580314403880c044030540510360b2810745030bda0a039009101c04c1c440c0a0503c0b29050003281c150b0800c0d40c84240400c03c1c030094000c9902a59001a00741072002e409840c0327036400380041c1007000c0c900c0518160030001c0303060364480c4000035982d41e90a80c0b10502c1101c1c850101c401403002203034090b0340e10a0384401151740400c451403819941200802c280d008180611800340c0004455802c0020301a0507120300803c48801c180c59a9030300501507120620850 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 344260854 1250 344259604 344259637
    0x4060509130f0c08010801050a060506120601032007031706031e07050607060506040e0f060f040f0803010905090c0406060504290408030304060b181302012f01180215 73
    0x105410b043c416541103c0113569001441e52401c5510303400d450001d401030064520b000310411850341d1b03043c01c0341c0c0f40444490080d0030640c0c1d140b0050b001030a208042400d0604440782d0416a1441c0c00d00410b4000e21944840101d01c8010140c4007802e02d00b102c440750154028054100100d000603190b040d11503031300007203d16494840780030480603003080c0012242103889a0910007285814010f003074040704c5160041506074940030000d0b5a030300001c1e040c0d4510002d44400f2609000a2401212039640c11106d110b5807569030341d40d09002032030115a044454054510941c82914250181c501201c0155859608207401c0815005200d2031407002c40703002c8481d0811213000359403510050001010413001541e141c0c540f60402005843c1c045132010300c00c900315919800125038200e522034018800c40c0c030800d40d581c803500c010f1b144806046c03901c50f12885521090251502d421203d50900c1c01200001c0c001e09200c2c00d42c0c004103541001c0029071141d96420080c0702c13440c0316006040254010f86644 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 344262104 1250 344260854 344260871
    0x501060f0609090f050622060509070f030c020609031c0b130b0310091203020f0d0603112103160f080316030e0a0302100c0302042d0b0406050913 64
    0x6140e241141e0301800126480580411007100b4910444070143e40c5041d041c40030b8904407000610b204820000440d603080c80184220f180d0030154084000707040c1c00361048809040c41207020f000d202c0b103203202000090812101250040c4085204d500660b400e50045041ca46519107000c85080c1aa0813902666590340c0900380e40d46d5410307041036805a10780f40000300e48505806050414401d01c0403202401d00307241c0781c0c01c0010010078001ea04500c00c4d103401a10f8207540e5442540034400d02d000c1d5035105041010100921460900514101804440030264841e1603140894440c80031490588650010702001d40c4020240030300400481c0308030040c04401c03002c0d958856580d0801d5071405440d415008520500315094071480101c94482c8004041c0241e00c3d175070007540e0324001020660415107030400510300034025015a80a40700d10f2000c07990300c5da000b5840300c0603c9040c170f2220003a1f40e1240000030306003030030900708c405842e00d550b034952030450107109001214041942202c4031a40c0d80004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 344263354 1250 344262104 344262119
    0xa05030301030609030e0a0b0a0c022e08090a0803041b080703050c090c0c1f110a03021206010c0317190c080402120f030a081b0301380a050304050106 66
    0x45001c0c2d4840d07200000c41440303034100101501580c0c0c00b428080e4914032070500c07480a00d44c0c04c4c1da000000526007904820f0032880815180d031507038902c00d0b0000220034642c020131420300500c25541c118642d02c6440c40d80e1450f03106030b554450390b0341c058a40c000070804180810045d0075010003003083c0c0d1745036180165440c0000d510b0a1000d51054034039408c8400a40b100e850000c2d059508045c440c2c0709203040800f4011520749950910308400c01c3e4604541d240b161403030a83c0c0088003c90302c000c0e03007591101c006c520050083c2d03010452200150340790b030380041c52546c024100a089590581d845250020131905441c6550078045c04003d100541da6125980100d0103000c0d526040f0041d503900d010b41d003440e2041c030200f440018140c500a40010194980c01c2c140001503030100c501d245041c642d140c42d01c0001c100d6031014002ca43c06050000800441d240d0301c9449004032100489100c6501c1500030107030382031518294019040c46003020829012040d12078409160058014000000d410365100c41 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 344264604 1250 344263354 344263357
    0xf0806130e0f19030206090d120b04061a040501090e090a0b150a12030e010906080a0902010905030601030506071b0c06030c02010209030114010503101a0103110d110304021e03060a050601020a0503 86
    0x10f2429a04500d8100300406038140180b941010420001381030350b00b0847c0c40503210154508904428580e15140c04a01d5580c0e070f00120014582c0030b034444040301c404800c054880e885401818003040a041d07000404000f5a0071851054117414040c00c11509a81c2e42c140383c42c600038000a6401007a46a200c2c0d40341d0b108005900141184020609452003d00c1c01400c6103160b000d00070705111121800300405504007043c0c0e41e01042c0100005220f11951005840c02c524a400c400d4241c464480007100300400010300d9401281a616048040c50010944200d00f83c1240e81c010204100c00000701300c800e00a030048162911980009410000c00002290031140006c200030780544c20803004100b541400c2c070180f001040d0b46a01405a80484012000017003040300c034803410140c1c1c0e034101c95a110034034070555a8510b06040288a44150310310b15a0140e001658264030504040b904012070024203c01c5a0300310324040c014004682e901d51040d801042c000b448241507000301c4100c4c800284046c070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 344265854 1250 344264604 344264623
    0x40b0607150207020f120c1c0506041103160f05010e120d02010c030b030705031b01031407020102030a0c090302031e010b10180602070605030a0504031704050309010f0806130e0f 78
    0x1100180c4540013070041021000c00d152100d80944541111004002000f080401a400c0c00391450f005c0000d1182c03088a01c8200140050000d01443d030501041240c110500d003503a000403800c031680140c02d9100c1162405441c400c0c002e070030010110811182d4007541202d510001c004003584418101c20442700c3c144125500800010b0355500009440c06415106103a04014103800030b1003110304010101e40e55481c121621140320075a10651900340e0720940000350780b84405011003117241088000a8040e40042d50a10107041c280019a401e561184080710102e80e0010001c20000c2070071000c052000202150340c2ca4995201c588580454460341d10000c010001c03540c444106100d02190800c0c00c0840e5005601150840101000610b6016060780e40200c9582000142c82d241d515080d1030f4a541e40c410103041000d41d0040006101c4040b0240c4410326081e00d8100c4400b01d074040c1101d40c1c4200315a40c41d07103c4a958216640302c8100c2d80102c22161030740088036840342c07140101c06d02d05040c40 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 344267104 1250 344265854 344265893
    0x6020307080c27040b06070515060d0809010c0c03140a0209010503060106020c01110c0a0b0901081f090e0a0f060203100b0c0c1c14060123060702040b0607 68
    0x2040c8150a940700004076440540c1208403418000d5618001c0410b48809010008200c102001080035690700d6002d4014a8401001140e03244e41ca45010754451005014010780b070004803000888900f07100400701311041e800540b5a280c80900c3d401959403542043e01959a170200a502000040d00581101c4843c1d080383c0007840d015155104105050b034050300420f010390030250040090540000c0d108810310f00c03d08019070605034042c13503a4509480c01d0341240d40300e10000d000240115071a002881c41c0502070365403201c1d95541414550329204d9039004030344030f01c6a42c80304201c40f0043e0b9010381102c801c0607003960040ea0036034a6294003594101c4043d40c0c000d40c00001d10080045603a030102c01800390702942c500f4100090000c0703807240001062940105134040508900c1800548140c5110390f0100307092030800110f41000e5600c0714240214040c900369199950442d100044a80c1c2d21084010012317850001c069081c4405804103641c104c0d0010f1007030002000007820310341a506002040c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 344268354 1250 344267104 344267107
    0x20a020d0627020901030305160b01060801030b0a1b18080609010e1501080703170f0c0c0a060e0d0f031403090a0605150d1211100e0105011502210d090602 68
    0x956002081c03510ba0440074104003219200c0950040c0c4603210660704481d018188143c894080346e5200300c5903100341100070100c4060178008900c00b0b42100303406050b00e005812940d0155110b03841141251802071040c07211407103004101010900c500603404258041400a002c2c0d590780320079681c45c0080a9421039200c0c0d44410226503440c0c0200a03040c540b035107190ba031030603e5142510700d948582d00ca0202601190aa48502c40100106000c071850074840d00320300d50380e41c0c0800351000c0d00c0b09051040107100f283c4084000481c07610540d07850366050402486180c1030006980c42d10702c002c40313280c012018000380300074840386100e905c00594480c2c3d118901a0a16550324035104084440041142c8401506400f030a02da54980f031010a003000c0c4c0c040701047c0d141c00452020341c0d405c8a245845106482150140002801c25401800703020054500034050f907621105c080c034030070000e840e685006a0004804001e109071480046181c04030030201d4510381004040c46505071410602d0a5403c680c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 344269604 1250 344268354 344268371
    0x1902130e01170706050d0b310b09060114070c080f21041202100e0a0603090c09050c070b151302041401080919060212040b0601020d03020c03070210020a020d06 70
    0x600342c518450840a54018203d668240310003d80203000c0c5c0d1000044a0b540d844820900d511000802d00400300941114135203201204200100034484071218440b0700e013404103454050403d42c0d00f0a000e0401611204000c8030307170424020503604503083c00c0d24034914440000640190600000c6882031301003010f03001e4000503000b092040c10040225001c410000c00c0100200d0080914860105a045421071181514140c046403000420b209041c0e100d1000140010b540750141d00044159200c0d404521038280d07a03c40c0002224403c442c4500708410411507880001d036840806a4000c030b801207070215115503000855040801d4a1207a9095035001505001d101c2107000c1841444509192400862800848844e110b2800c2e0652072802009480041c040143c2c41e01501c805422004d00c0352860b10305401d01c80e12641046c5c0f921809070181c0039050f035140344203008a610240182c0000c2d450485c0c0741d424031010303c12204644045000f62070041e40169114862050894011000880c4011 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 344270854 1250 344269604 344269619
    0x6020f0c060705190c06020c0f160803030f060d02130c020a020a0905060f01110f12180a0e060603101d06030f07060804061a150403050111040305061902130e01 70
    0x214058074250500c48244002d0902040700e141068000c4c0f0240340c9804001118a84840a400b50014030002406040307034101c0070403000a00d1030f880101e120141044035079131f03402c011b45074803066541540940145000843e141410700300000054406011010b0071591002200c04851200e002c120068004070b003140c0551821082c0764010f08440b00e4104210f0501c80d00040c40e01c036404030f1791414408940324003410404148000480c1203090826103001d800b484201c5034080c3c0c80701751121200210100d10490b0707130401d28031400a1b100316001c80c0305151110810440d040d007008022040f400002d440200344619200c01140880002600c500404c1c14201d00701418000080b441c0d150561003a80200301040e800008280c209410050000d41c401d0059945040a000d00162075040813500300d4035513444036400014000c90380134000030441380141c401001140c0c8180d02c0050074551007040410341440004108500850b0442d40042c0342180555001d500750403594406072074a2802d000402944 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 344272104 1250 344270854 344270863
    0x8030304122d0e0f1e0405010806060108011a13170106140f090a14040b100803030c070227010f090501080d021504080403050604061a010309030e040f020706020f0c 72
    0xa400501e84402020100c451000c0d040082c568802c0c1000b00c1e074a03040a807a1241c40081182031005480001d981400ea90603003000481412103d00541c42c01e40000703601c540c0811a5409008140d4801c8400d900c1c040e0409104405070a42c0e5003611020086001a014128101d00003481c40c00190140100b41110003800c584030356003ea41c01040d5642c1040d8582e48414904c6d0b110001200c1c0c110594596028140040ca8641911401d07900340d82c06003c2070100e0030070040c2c41004091111940309448601403603c03400103848480c0515414850301c001883e0680d10f242898510000304400d108504c0740358106200c083e0303c10040c1c200682020b11280e2041d0140502411107140101900622004001e60b510302042e52a103100040c0804038040100381c0c001c480003582c0080840d002c5080c40d0400400501c1005401c190400c28125032050650103406241c05040e00343c0c407980480f500b80300034480a030940040b0030b00031650030040140010402c0c4090940c0e003c00f104440d0300d40e4a018001e91a0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 344273354 1250 344272104 344272127
    0xb031f09050a1d0606121203011d07020f0d050a020c0d20040b0a0302040504021503040b06100e1008070315080303071404081009020d021e0316061b03090803030412 72
    0x1290f02c560f41d0342d4203122001a84a802000a4900e0550050369003006428582e46c0440400c03941c10000c0005003141c03641060340c414202e0050b00e4050b079220704001f039964100660003400c00c4d4201d01c0703040c1c2549000f070024060241007401501d0404540742c00040c1552011f050888458440c2d044000d12a00711040c1003011311825102084019000b00c0091178050f003500c4000d10498951001900315118614401e00101c000c04429849040601c1d15008001c001c4403514040d14902d8031003001140310b55040c1e9046d440c0500011860909040c003124448802070086040c152200d41000d074142405c4113000040c442507028544a00b00300c0c60081c5001c4200c4136414a0403401d200078040c010002c1400310080100040018681c0d00300d20102d050303041c07030080181d0b004c407a20400584130071100c090078a21071400c800341d45900a10619850001009000300301c00140c01800b0b040c410081009100c403510b0190400d60f0700c1c10340e0b0b4600d840c03469200715001c40d00c1400024411903410341200b140034a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 344274604 1250 344273354 344273381
    0x414041b0b0a2a0c0306050103060b01030c0f0807180b04080c060702030d031a04020d02070312230402132903010c0f05031005120a1a060a0b031f09050a 67
    0x1601028500040500841c0d0040a080c2a180901c60880110216003d0781440e4040181c101c01a0307a8280b12005040920041d21180c0c1400120401c6600c280715a08140400b0384a40410000960085514420061814003805030400c0a038190001c40d110305001001503000e42c40c0d03101d00f03190486003402600c0c100940510410b02c40700006946c081181020075060b443c00241c4800f02d501e07070044420400300115081840019081e203e01d80307035001000d52034002d03120f218a02d04100c0048089841c003180f0445501801014084800c90a402e010303002400200345040c010300107030b20801181d081c072a03a00b4011101041c140d1030b580b1214201540c02c00c00710000c21411018503c0503000b002408401e0b0108100000002c0c91418040d030100058440980082d0401030010305d5507954041540d4165000446070152010404050860070700c41c10002c0c14925055140004400403a04080c180038080d08000600000b4540301d52841001409110b5000c545070415446800032070314400800b42 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 344275854 1250 344274604 344274607
    0x60c130f06020303060d080409110c0d0f050f07020103020d050903040e0106050715020d2004090b04090c05010c0f05060403031a0405160509010504030209040615150207140414041b0b 80
    0x1c1041d80200c140ca6115405170b40032500e52026141101040c8603a40140c0e141c40c0c6003030f80040001030a5030150016446040131101002e408403010b895045580d02500c002035030401c200380d6507042c500044c02c12180306042c090b040c950007046a0059a504640765000c42e8000710341000380d02c0010400d03600502e01802d01c1071800400d40ca83c460381e41d241840c000b07034841d0001030950300e040c032075844040e00c4480680301e06120594860700764225030062007852022410200212002d00d820b20409240c030b0780c07060314000d20502d04401036556080340b00040d00c0309008150080b0100d403042c00341070301c910310a5070f00180c800746118581205070060651a030040c0d26200c100b240108031881d100c4511211420216104c1c0f00300c1004070390501c10750704003d401c15203d505000070060103070014200b56503090143c6d400390761940c0c11000718007802e869150041e446044100294200c00c81c220300640c1e000380000c42d807000b400303e0750a6000f0741941c0450b050354900304940e500b0050071341c00d0300140880c071503001d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 344277104 1250 344275854 344275859
    0xb040f11010507111e0d0c06022503021c0f0804080d0c050604020409080d0e031306030c0210020a03020d0c02030a030f0c020a4115010e130c08060c130f 67
    0x10089400d180d0115001e8900382801074804103515280b84400c41004101b20300003100c91518400c00300e0f051080c2030242c0700c1c2c1d026030f00c1500118036804c407900d9800600120000d181d41c081048441848498090014845503c0b0010070410000481401d00452180e5078403803a03c3c0380d061502220000c8001000003881402000800124a20341c000d13404980220302d040d00390422200300d2041900864010307140141c12850741f180400940305100c2c00304940c860340360303407058282d0075101a22720000058121600040602034140d020700001d180d40e00c1c0c01402c016941042c0402c480e07404e4002e00c00b60b0310125100302c1540d40f501919101080d164000e00200d5080103006c1e61706d2130a00c90003009001401000b00c5440d069145c20102c0b0040204550405544040404051007807560504989e000c0c40035410411740f03491074418100d900d144248059640c0c0c002009032540ca1404080f1001040342d600040c41e05002c00055003d211110485a074942c2c0c00340c3c10040c4410240d012100b02c41a01408 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 344278354 1250 344277104 344277113
    0x90209011b03090b0307030c0201061d0103120e0307090501050913020f040e10090b1f0f1502100603030201050a0e071202060901180e010501030509032706070b040f11010507 76
    0x21500400d0120003400c1d040302481c90305a810703c00d642c000c0b603140c0c000842080801985900000708014107a0020001c298444030b81030f4174454004062012800c005c80100f0000d4034a003540c203a8074410746407100c040e4100ca000070f030900d480343d4003012855850324014441071800c0c0c00c02c183c21a840d41000b04c0c071000130381d0114a070490302d4100b12b4030030f5581d4080701d00400da05010002050b030450300c08101c2c240686c9002c28815800750388a50303130303820f9254669a0740209100403105452680c02d5002000340f5041211001c0f4601d01079840841c054500e07810723240a402e014200185200340c00104142c900301c04900125081000c0d40714182d840359204208462004108500707064058036144d659103886001130f6001c038602c107209114580c580307100050807004010218140c030800d03078040c0070070b031601007000f41e4a0045400f841125101507081c20350140c015942907202d0302014003014241a0940c8a42c2074004085601741d2380510111000e400b0018409084050f4039000d0031300c5428240384d902c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 344279604 1250 344278354 344278367
    0x7050304050a0803060f06161734061b020c061c0504030306180c08333c01030603150506030102091e01030b010306080a03080c13030302150109020901 66
    0xb0003400d900400400f0803103c1e280d4001103940170401401003991034454044080c0c204402e100103840034076400891282507800201244c0714900150080040800c0342803c001d461a8030880540c208204114444005900340c014851540e00201901c008040c41244c0030342040121700030380e07201e208104072079150324401c040700d13817149440448000cd4550b506c1ca4141d0080005030004200c0c00095107800500e49500e4221140c901c02665590400da00c810000000700701c81d101c41a20000540d1003202d100c1584004025141c50700200901c030f0b11508142600700075003180020483c19801c25803100100341000c51800724450080c40d0402c11185180c9030181600e51003a5400d168984600c00f0800f01c4e642501034501003180100412018051801c0d80c0c0344913810403649901081c00c00d8007040301e940c003d10402c0b0880301008050016548560ba0172641c900c0002c00c0d0b5904014140001c1540d60900c14101016621a40050040d00321882c068008402c050340607543e02c0740104028901d9990014 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 344280854 1250 344279604 344279623
    0x609030a03051021110901050604270213050910080c060a051909050f0901050916020a0614040b0a0507050d1109300a050d051b0303010312080705030405 67
    0x94001070b503843d400307490412043ca079404500d010305810f407590340c00ca104460f00034041e44504000c440103c000001e00c08400400d2280c02c2d071121007404100150b140c030003181050130010890213200002d01c4801c07101283c111060601c2618000c01c800c3c08030381882c50340346400c00402c00100042510b0700403101d949503406000240a518041200e05c9074a0040c2c09803910724108900b001031075030314403000402d4000c96100d140d00c01c070703080101c9009905107c2100c5050b908082c0c03003040c2558440c2860400c1150000f00001140304c0d15112030080b6050744074021180c1c0c00c28102d40304a08003030800025019019045e4090b040c68181400230300d5070800201c865041d9201004203405c1101c40c8803641c14014420515045100b4040c1c45580c90400045114a02283c0291259900c00f40801d0355a503103c480c1c0060042d80300030003240f0302c80d0055000d40240c10701c010710318880141d1301c800181160002c0c0d1089900c582c080080d40007894025001c0d0341c0c06070075450050704610b040d84138180c0d14064107 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 344282104 1250 344280854 344280857
    0x170a0503090409031806031422061107080c01050603060c13030f080d1805010c02010207051509011b02010902030616080403030c140715110307050403120903151d0609030a 75
    0x884a090030117001e0942e004c000f41c1054401410b4585d035110180250582da6841110b010a6000040ca403066a81c0d141288249440c080d440c065401c0da900d10081200307240303180d48914180900000541001c008000c00c0085500100e01c07070604200303040c540440a00040c0021400b40843e0b140e04060b01c441070201e0b5000745c03154144180d5810030104074840c010ba040b8805040c5842c0300340c42c20101d001e00c004a8401c1000300710030700700f0800c101c2c200d00814074010310360340102c000c0500c04200301654a8205603101b00019510401d41c08400310340c000c4040700307400342c2d440f10258004d40c0b4003804103030b07072090340503402850051a02000410794a00200000c040c16540e4221000b814460032219070040d107102c0300c09a43e0445401d1841c12039550b040016205402c102417071500c0341c1303410256400f43c0d01170b440c3c660a190075a5608590840300c0c40e481303003c20200820020100e103180710a54218072101d01d00155520148121113501083e180242c9015031010f02800b04a0f00300100700c0d481402c07036 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 344283354 1250 344282104 344282111
    0x408010f06210f1a0406051602030a0e04050c040e1f0906060f05030403020f1e16060206070c080904050a14090106030b060d050a0c0807060801080c0a060f03140c04170a05030904 78
    0x20780341c440303002c82c4c44401c983c214228110400c0100202d59004500524000b08524021064080100da491140102d08400120035883d01030705030800c2d070001034209503d404200d0400d6100c0f00c01e45000d6200711451001c0b0464032600b652040c2040e0080805480c16500500009080540150503505010ba00400b0001e0000016041c5442803040c0c0a0b4403031161705680900d8007844a240e01c80c011156004264001c6030101070010600880c2d4808450040d0050701159884c0582950344d030703083d6602520040b20400010940e965244201d6114a11410b40007421503021000c04200200003400310070180e240180c2400401c020b01a0b5690211084480d6054134800303240a07402c01948207001845054202c502203007040001c5030f013009a44d01a40c0b07080190703a0b81e0703d11030356443c1c0c0510780b950814400d207000d103c807611410381d81500c1105410007262446802c1c00c01a034244044480100d040404941070105000580d000c61580d0f074000d000780a1062107489154403441448030031441543e8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 344284604 1250 344283354 344283383
    0x40302060d020c0d1e080103050601050d050a050f06011809051002130506030a0504030f021c14040b03090c09060a060801090b040b030a0b011a160b1503030408010f0621 74
    0x541d0b0301210600501c240030f642450807508409825510800b5451888503034070313508086001c0c401e08001c0e041b81c0d00840108140c0c0d1030705080c00103410b6808025900b5001744441a80491000c2059212240c20400240f06a600d1b203600a205010250300703040705141000c004d00c02041c0d000811500d1101205001aa140b14180c1114195a15544690342080020041143d5422a036000340e210781d004c0d80311901e048110b42c0781243c41c0d41848200321034401007203030140c00243c07058411a9101b803180d8500d52406444602034020781c0c100b210002c8603507121500711034160400018640c0c1008c0203444110b0700c6403c240380541603000c1406904189a580d098114181c0d94903004901001c00290a03030300480013a013402148600f013405003680380c0b0021541c0b4040240280700301d44981a0b0b48000b02c14649940c1c0c1d0300802e2150241c9420040c14842c00e03a0500c0b5601800200300801002c1e00014203041c0800c0607806552881d07026501411401500414540c143c46110114039404042140802c1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 344285854 1250 344284604 344284627
    0xf030705040905061005060f0a050c07030606121202070b180a0e040b010801111603080a0b03191b03020315040302101a03150601090623070302070e010b04030804030206 74
    0x8020380c0801e034418104040312081c4200440c42c03d02810b0700c1c00c000100940c4407400d000c203070700c11107469031a1080e0801a4104062040002d800c44020000607142900e0b5a41c80b91010384029402002c09108400b50505c100040d2030304000c0248540d0006d80000703440c2c400b010301c860007482d0b016451a511034100d04080d03603845040b080078019452400900b8103041c01d00b03140d03180d000d0203201d10035864507400072910b140080c19500525110100422081c4143e5003c81d80e9000c0a04103825540e03c4e00000b54065800f8481542803116444590716494990304000314201c0c1064600c904c0c5075103031a014005a00d021035814518164500c2d4407085440f20b10741240352058600100071a1458401c40200b4030059210340b03c140801207080b143d06050f80054107101440a90321a80881c3e01c3c0703002045581d0281c0d940300000012504011000200c1c4502081b06070b101403070490068100500c24003084000301c1c8400c0c0540344000ca0581000e082d99124081d0b80f0a17400040e02c1580040350042c1c000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 344287104 1250 344285854 344285863
    0x91403010e0609010b0a0b03060a050f0d0f0308060112060506040b13080d0e040608030306180c1209150705030103240603080c0604151103060418080a0f0e0a060203090f03 75
    0x907106800c55906240198115000f8022405468401c65003d0400504c59450703005980c01900c004140000d0740d840c000402c07900c0c4a44142c6d176500162800f01500108030030240d030f01c81a50090700c0d400786c0c0340783c0000010f20720980d40c000303101e20a24061007406036440c0da0303003902c1c103580c0314018072a40d41d03512412230301d40c51495520030505032107007800c61a0b03031503402469074041c0242130758180016616188201d44a00003180d00a130407012001d550008542c5180015401c45102551181303000259080041070241c22150460f555000290000040040055035a4840e01501d401400c650541d550f00300821b54065400590310702e603000400300004c66501c440300a607030186001da41c44a11400041d2940c40407035059410310909419141d00320120b0040c500c28907401402c03180b655031080100300003003191400d0481d0b06082e014031400001e00900007401c1200441e103540a441e1100310380107000c810b415103a140a1030040c00e0410525030000182c803560030301103402001210801c00030034a071 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 344288354 1250 344287104 344287121
    0xa3b03040e22050703080406031104120f02060904090b190501061205070e09011503110c1f020f04030c0906080a0f0b071809061e0608010b0a05041d0609060d0309140301 74
    0x35801030130000010008410300130011507000c0d0310103009244401c0e25034681030040c0c0c0f04000d076417000d0b42d208400040800c12008c0b8150301c0202003606203180e05001ca012914000401c0b0b44005040043c0180c03e200000c1010b040038003450140a190305080c0003c0500d45002500c0903e1500c1e0400300d01540d0045071425401000504038017101d69444080114a1034002c0541002c07034901181e090000c010681262040c03c1c5160041440ba4072003130541500428805600034400c0d42804a001c03060074000080c001076001c0c000e00ca00d100d0400c51050110f909990151a40398480b0b51840001760712034603900b0329950490280c030765940e80d1100990344850700a0b58035485801c7d44c54003180403900380e4407400035204084031a16640070140c0b080d0a00300c416005141c04034200030010042010540300402222074203141c000d0a02da918a4044609000044d00d600e0345210101000601d00308980c038558440c01c112520740c80c14445840140095009010f14000c0041850710269942c41c2500a52107 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 344289604 1250 344288354 344288363
    0x40c21060803030c0711040b03031e0d050907080f0a02090103060f0b13020408240115111f0f14040201050a031404060c0807090812030a3b03040e22 65
    0x341da14000d541400d00b50b1104030102e404131b900c03c00010150800b40301d02080d91801074010f529080f140d407640c0d401114404003a142802c010040d03440810058081c66006440c4540189240f505200b5184c1c2841e07100c0c2c01e0311000b54450700340307000560764100941d81140d400c19000102c0345800101c100140481d0089260000d03003208600c0c000c08056402002102d01c2501907444100038808032024400040303090521040c000c03401071001541c13100000351241018201a001160706009040c240205080780e078140e6034102c0d680d10b00808141c000c51510100084c801c1201000400c031540700444060000b80c100140400c520307403003c2c0203600108034410010f611812501e001d15220002e482441141000140150081440d550080784820706440d0004064a10032404c0c0c4c0004000e5000144555039140d01da05041501800944201c1a4080c00195100040c03c1100d20002010b4252041035144d620821081000010340351030107803c01400141c9400800744c0040003d081a81c40c42c001c1c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 344290854 1250 344289604 344289607
    0x29071d091f050409020603060906040b1201020a0201060b0721020c121c030209010210110403020901030b06031b0a06031d03031617010e061003140a0218040c21060803 73
    0x4a041080d9070a21820404046a50703041078442c000d00c000e980c1c41c02e000a403c58014404180c461521302c94072580524003038000030303035200004002000240783d1000300407665800100020790660a0041d400607109181045192a409544600c100700d0402024450300040048106030b080c824130404483c4140204600d4642000300c00d140d894101c0321048002c04450b00c00d1102c0c00d01e001e80243ca016910580107020201c803000c0100e8041d0a00100c0030841d040700300400f00c010b98038000c016010f140984510780b50740c5401e000789440c20803080140085040d580c90703010707016502d041c0c000050ba000392902292046c0c0516100202070340100796103505001c01700c2000211a01c402d4010510700a90342c405500d1440345110070807a05c03080c003034000c002c1c1ca9000014880d043c00703400700c0c4a100e030a00e00001ca412420271007424004040d00d002e9041500041e0b00070190010b60030444031941c00716400c01c05c00f44420000b4000d41c0c291010b25040003004c4000140c00c10056022600928001040c0c0f03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 344292104 1250 344290854 344290861
    0xc090204090b0301061e0b0a050c060a06080c090402090114031603060504020a170a06090f0f2105040b04060806240a030e0313170102070501061229071d09 68
    0x140290007542c0b481c034003e43c41c0c100009200c015410303e03046440101c0c010b0320411418108048202e038421280c08050010401070060545010400c0b13030b01c913010174440017070a42e0400c00030303600749024075008502c6221140c00340000b41e500d00c980181101d01944141c107400c588003002c81e080c00703c99400840c80d01d0703000314000f05010305500018411031088429081003500c83c08100e02e01300e4014051500b0b540038202e50800151a5804244a0303401140c80500c6030304180d8070040ca804608000700d9031112051031105000c10428081c601100c42828054100f07030408940440c203000710710542003001428000300d216a03d4807010a02d1400050394003000c1d82001c1c6d407082956620980780032000a06c1c0c5400200b00060120665650001c14514207061924000d140d1070310481800100900c1e550801000300014824800c0100401441c69647d4603c03095013090841008255060310072070314142c0e002524a19403c1141d5884071144c01e081c4810b5407403115080040c000007690940124003072003403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 344293354 1250 344292104 344292119
    0x160506040506010e0612030711130e0d030c020a02060322020d030810050109050f0d030332070f080403050c0a0816060c0201110702040e030d020f0d0b030105040c060c0c090204 77
    0x925043e218582207103019901c07504180404200c8070844090781d0b82040c07288000007105030425645800008ac040c081c011920003246045602d1401c0140c900da0000c001d038420b003a0940100b40d0b4943c81070000d0811444e4603004140584401004c65000643d0321220541c0d12200155440501d41c000e041c10303040c01c2c081d00d0003800c0410180c4042d460740310340c0b0721700045075842020310400351800604640301800541080c0100385514032011400c2c117031181c045034040c1380854240100440c8450940d010342e540781d09181030b4584050081e004108030400c02009a6410040741c58000360b00d4a0100c2c3e48417910700b00c2604080c000c40004040080020b0740c000400e903240c0b4040e0280c0e002c0d540401030b040c143e81e801da080742c041c8200100c01d100240000d2002d803909a000740d03008801036007070340d11302005219610304076400002e180b96034440100350301c010b03078103584100640742c1e2003900204110b00746901c811614010a200790300400c07035803010138130402241c1e6106400a04a81400b5900d0b9500e4822 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 344294604 1250 344293354 344293363
    0x51207030e09060105120a1b18050f0d0201110309032d161202010c0b01060c1e0206090609130501060e100201060f1703130b130803030601141605060405 67
    0x1000d40c0020207014000030549440b05a0740c0c09010140c480350718140083d5400070b42c81800801454440741d90382d540340f520380101548140c14084a5859100ea1903020401d041595440d4204c98024421110f522800e502c4807183d507010389409080001c0a032498944441c0f86102d03000c46030b80c06009078840882c0030500d4034581c141d0a0644480d1000160041018940e91300030491900703440302d0710880400c20406021070094446006241c000b20611658a0f465514003081e03200c140000c003411050f40c207001d0b84d89200d080340241d5107945840307444c4580010304580183e0308054410304d40010503040070342e00c41c0c103103140303501c80140144229030399198054071904c1100c1078580100c2e00c0b218500411031040c03044a00b502e11b5000f01802c55030820100ca003a0341c480d10703000c69452200f0003030b14a044840000c3c440042003009142039440c90702a102c980b4004c00c0751712a0b0301550040c014031429a03004a4881ca2005038500d1040e1110384505603c3c2d2000b80c11040981a4002d0405000500c0030104 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 344295854 1250 344294604 344294617
    0x50702030a1505100e060a270203010e06030601061b0204051e0703090203062235041e0b1209030409060315180803010e090c0406090207050d030b0a031b030512 70
    0x103510070b84c1c01c0e07540d00c40d891034481c0c01c4505d69803140c808102408041011005414910b011a41080c0190006030781c0380201d134001e03080b0481c8952110100301e8540380801c0700741d01401c0b075450a1407904080d0501540000c00707081c03000384100d840328006000d80c0c603c0c04008284c5444c0c0c00282480d420301000160042804c08070136406401000700044082c0c2c0041030900d01200700b0414940b261119032030340e110301d6043c600e04480000820368074161002003449081c3c20b0540504070207907191308d002c0d0b02c0ca29400c03450852103070460301c0080c200b0040c0500b200b41e401ca000d10300d2209003e80c2c0c4990520f8294441d9401c0076410307529040340441400b1441c440f500c021101c80c18208056211151414514007039018020708040c2c040005000c041010b40c0c81c41c1d0060800c8007112040170302100043c1c03e5584a8200610842c0d010603c40140282000345000c0080c8904040010b60714283c00b08a4001950001500305400c041c0c03082401444130f0207110095801c682900c54140000c402c10400c0d90146 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 344297104 1250 344295854 344295871
    0x706140319091202011401150302030a0921090e0c030703020705070302040c021b04090b1308041d0403020615060d0902030c040c031506031e0504061b080703200a050702030a1505 78
    0x11906c0d01c501040d0110280c141e80d00b075680e031542030303854580c1100654401800144055184c0641c2000601e041c01ca11049210b0901005d00c0751070300010040c5175942c943e10030002241c1c3c4000344070031961440103e942140980c034002d03039078205030f00b0810b1801201e0b5100a40117441c09200144c00e43d408641580d554050201d01241124030400304425160745050260207038865001081003003076800b0b0a007503100e104594190501c1da907190701c500403010003401000c1602650b805c0104140d0b052010b0383d8480f0036a1002d09c40440c0c8140460303841d0051201040200380d40c0d100b15030942d075040140d02600c0c0300091003804220608038000340070701500322495504040000c0003141c624002d000b034118190a510781c3c1f4100c08400414000a404041c2003036960698980c108201518a4040d410307010500f41c5513483c482c20000c10040894051020728440c02080f5480e86055502850443d04681401c0c0f9081d0344401c0e0900000c0c0c10032210a00041607401d441b00d40c04010f0201e038001d1889403800 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 344298354 1250 344297104 344297111
    0xc240b040c020708060a022d030402010f0201090c050f0a0b030c0705070501090605031308070602070308090f1203010b0d060e0414070b04061e0306080f0601031202070614031909120201 81
    0x100050340e43c1c3c000350041d8080c6401079400642c1e508001e6010b449805c8442c8400c1c0d80e8210941c40d080080d045241010040700000400c010965070003003184118500c0130710007045644003c0c1c0f80c0301c0806a00b03010b1a40f00c0c01401582640a980e0840f6080240c07440d0b071071442e035a0415142084160384002421601e46c020110000750320360003080d0f901c044400381d803207a524503511001442c01d501b210f800c08a40102007481a4400b10314a40301401c1003070f20a440d801043d04280414034982180031a94003820b40c051400c0051460041096a0444102c600c80c00c0c0c61381c4002c2e00b40c102402081d048002d805050354104403d02c40609161700c80070800909691007961a031007000402d01c52030180a01003100060f0f80354886141c0d00c00841c01501610b00003c005865001041c01c2800500920344290301c10001881400010700450701c4002c900d0008016252525001500d41148a880021003940210006a106403040150100c0ca80a0242041419180d19000d01d84031010f8099500541c81c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 344299604 1250 344298354 344298371
    0x9030615040b12071701020c12031306061404050c04060c0b09030d0e070e0106090e0c0d092018040b0727030b07080702010c092d030c05120111040302010c240b04 71
    0x8061089801c8e803620080030b460103140b499600e4a003684086e02c2200385850754a42d02d07001c6001841a440540341c411610700c0c1100c0081c04000c182c84001c3d0021450a50401041001c2e681040e1041c1c0480c0c0d03c4800c800f055078440c600c0c41e007580545400300d0107460910130310304080100811203000740c0360a04a1015140d0700d49404840d030107064019407014141c24804140500c0480019000100e4140300c0802d0112031550f81208610903910480010405018081414540886002e40d80400403070b105505203030075190005c882902821040500507140700071000c0050140c14403040440c40004915400e070b41e480c00c01c500380401c552220024000c0c1e0b01080c0d0180c41030281c86d04800c029500c240680341422504d04001c0203440d4a41841c134541700a543c0c490700c80c04108801140241f00020800d803401052108042007c407074100d080e458070030f8101484200d90191000c4d81d80a00e80807000501e94034051029014040d480042549a0340810030030040a4001085501060310305114181 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 344300854 1250 344299604 344299649
    0x60a1b0203034506100b1911071a1206030c030c04021c2309161503090203030313050c0a030f120e1201140c09030615040b1207 56
    0x10b5400b0100c1c494090385403030042007007031103a5a15441e100c0156001c51003021070400c80f555000e41c080300f607400842c1040300400700901010010045e192031507181503140352007501c001032401d4918003801000000c408103104d080100354054580c1020040844062049080d0035800c035450000d0249051000981c4500300807840048408000d4001d14204e04001304100c0a50000958514415013070214510340f04103c0c040c1140c42d441180b21100004411000890090b0008203032601e56880340187d03100050303045101d601110090321502100007a4500114003524000e0b501960621001c0f041c1b2114100c3d81081040e46403044c000c031201ca005040c18062000c289100161070400307a0092080403544072100f19007000071600d4800010481c7d5430001d20006401050990a41e5403a022000c0000606500a40108509440c207061038842400642e54400c001c00180710304060020194264035142c10000100c00010006a0071030580020913650b13001c0362150381c0225500310050100030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 344302104 1250 344300854 344300857
    0x5070302090a06140103092a081b0d03030c090e04030e0f01030608120304020f060a02030705060c1912060906270b010503010302090414010f020307021c1e050903060a1b0203 76
    0x80e41e00701481e40e244c2c1c1003440150700601480c1c4d0242c8041c1d206560104844011508022075119254250340000e03081524051400000c101c0e20036080079100c0034032005542c1d00b0342c9625010750529012170041320070a400c17036864550b40d1240b200702c0607120034401050f0704250314400c03401d000c0d030784117066120030001141540c585224070360507904030a881c20256003403027000310351060014002e00c84068090002c1106640054801300c0141c01c0403413140304101d01071004680100070383c1031440c14002907241c404410041b07000406d041c040701014403401c03045107070000002010104410098541d84441c0f40701c0310640340000201403070340b1400302042c207480d034440e11001104c1a5a213500b103070300310381c02c0c0081c2e450301510aa481541c0c11f081312a1034402402428000d5a0b1802d01503124182680c0c00ba10300442c01d040062181c40e440002c143d021350000103100d844220844910259100000c1520b9610800c40266094011a0300b00250599103410284004414900b01e03855164860340c105d88a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 344303354 1250 344302104 344302109
    0x1719030e0f0c010f031107021f08010911030f2203210501030f0605060a080604060614010203120a1109060c030a0e06160321020705010506010e0a0e0109020c150405070302090a06 78
    0xb1a8244c00d04400d498445c0d0720143ca80441c0c00c3c0b00514004450f0002600b5141414103002091400b0500280c4554004103103401000c0081051040142c012034083c0c950000401d42c40e1030b94040c00014503105000300c01c0f040c02c1450000100a00c1c616824001c0070b0064442c0001c8403031041240c0d041c0d100986104e801d040340e4000401648001080d41c50760090900a030200c1d0b0b001d85203ea020403c01c07001c0c0003050089110b40130024229107000c0c4050103400340340f210f87d41950024840340c0b4180c0c0e040c65802c0d1307018501090001d4210150000b101507802421b5003117400c00d02c04904441c005d02c0000007013042ca0855110740c0e02020442c0c0811026204609441d200c5c1e60f0b030102c0c071000203401a00c64459020808042d0340c003e040300c00c83c080484e0401c900942d2103079110400e02000303580010382d01d29000d0064402c140814104003018140f58418802c0c940da09a001035481602c41d402c1c4412940d10600c2c0889002c3d0b406c09040581d0f690350325002c180d00c68418000031640152041c842d0204 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 344304604 1250 344303354 344303357
    0x603140d03063804031b08010605100806040e3306061908040302010209090a0c08070219030c0c0302041e0605060403030c0f0c081c030b0f0d1719030e0f0c01 69
    0x10940700203c0041d105802d0810200210081808007000242030252448600500707030000b0724500e4641041c26096034020303480316004003001041c00350866440b01c1c0442e8410800e0b00c01207861400c50020030b207082d44521017061a10b803032100c00c1c020410b00c190b080e48030004200703004005485003001c00c40c0f60311809103034040c0505800c40068945015644495010b4040c2c000141800c2018011130741200c0100c0f0b0410b0341c16642c61100101d9a00f1680054000d0b0280c4000c090340d0500c0d02904114210149010b81403080c20210a4104008800f0760005150301a1080c0400300390150040030300070316508401a40c0b0306110012179141090350607182141c2e0036548001024080d92941c01aa540e90303a400e07540d11a138036002207403401e07080019143c1c1400745c1e82e90302079440340c0d04002401c82d11411100f0748540c11110041d4515601d29194686007a0049144e81e4002d028094032a868810340007a4010b0107880110b0300001d640507448281c9449030078090751413040c1401201500d500500024a0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 344305854 1250 344304604 344304659
    0x501080a02100203220e0f04080906130306150e15030304060f030f0c0e0f010309050606040c0c05010e07030c151403060301060b03010906060314090703080d0603140d0306 75
    0x54500002005004641d5005603171070f02140130050303c10807061820150001c00044d000700000e60910781c8444c0c4c000c0c0c260301d03a90380710b04240c0c2d2124850311804070b2461107402c01041c01000307890706100034070043d60310980412084880d44480004207c1c07611507055039810f140009030113000305881405a4071310003400f840c607040c1400e00036030740034401010701c030700f01540c4240803490301c0c086100306e0107050703c903842c2c0031200c040050030050140d402c112001e0415003040b28200018100007103580c1c000c4811140450003c4541e501121601c1288002816940c2072280c042e03100007020814100350f900948003102603d4585000c042c69141c0403c48034000f80b40a102d544030150340b81c011b180c00c89402000030501680d2582040080e170001e03000607005a54513203040000640512400c920b84014840366100c610341180b880d5240c000ae4440070740141c0b800114620284801c1c1e00c464081c40c0d0201c8104100c04038003001a40c0c2e0101510100c0100c0d181c000081410b484810504400103150003209 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 344307104 1250 344305854 344305873
    0x406061211010c0309170a05010608010606050f0904090206070b090705010302030f06040e072c0907030f0f020414010306020318030309070501120212070c03090e04080f162004050a050108 82
    0x4650f40106401c054082204e50342010442c8001d0302e69600e03200171444024000c0d4006401c105003101c00fa6808421130b40c1c90910308000d1550800c01360794030680500c440c1912042c0090224000d403c800e000294040c40010f111000c00182003402400707440800e00b100e051a807900d005404902c400e50702800ca020004001403020b01c1c0079001000300d03240300001e40b09041c0e42c5864110120a000300640c0d811102080d240c00751109582e02240c2c403408960007003c800d45140c59000d05240c4442025203514002c0911704107544941c0c000340703400c08200ca0442429a03690034890b00030f4100b520003004028000500e00081c0700c0000035203014401181c05407000d0f40ca00001036510125440145940a80900c8003601c495413000505200d101580c50f4142003a5583c07070000c140e2103594104180c8540b000c805e21010580c100299584c902d06c90340c00c1030303860780007441c3c0041641301888001d10901c11007555401c1ca07200008070012021050310140140e0b19420782000a8038000d0045e103000e076010f0398a1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 344308354 1250 344307104 344307107
    0x30528080c0d1b170c0909010b0f16080705010c14030c1b0604030906090b030103080901120e060103050102090f0d110f130e03070c080105060f130221040606121101 72
    0x1c05108080350300018002c01d401059803d80c5104891003400b00b28003082c00780a90105025045d880220102d17041d103000d040301700040301a1b1042c010505541004580036602c09501c90440300c0f1410035101072480c1c2c031000e1800380c1040e0301c0084112659420103c120290b80d0050b50900c3e14003a0b5841150f007507980345a04440650403550340048005500c2801c40e2a40300180501400b5031301942d590041c81c3d08150004c0c000b00065480100b07201c2d03042004002051a2405490914800b464803011860115402030050003401c51a043c16020303840001003040340541c004c191020f030660300300e40048210001c1218608004001801503100899948002d1400110942c00154000e000070a8168021a1030003150040f240000c4c281d4000242d100600c200e0060b8280203294139002404075207002804106280d014a5042c0d024101d04c140240c07030103801d501580c40880c1c1141d103040410a021f80e1201d00301034151019a207a900d420004034040454241122810303030072061095404001000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 344309604 1250 344308354 344308357
    0x100e071707050d1515020a05070302010807090305061915030b22080a0324060f11010e01020a0c0c05090f010e060409020405040609020f010305060a06050c01140103030528080c 77
    0x11810030008001e4206041c0144c0b0408007224811400700154a051000b18241c0e2901c28915500f136511801a11001a0000411100341d0b0b9080c607202c80e0396140c050701502c41c9915504000c0050143c01c0400c00a041f41030841007641c6150002070020000c40100d040700c80d070071404040c1044189000117107000d0f034440da03600c0712500065400c481c04145902c40d006d20760007114407400005e40f40d05004110010039030042d1400100c541040b40d180e85450006070031003c10003150420f0112004580b80480c1c030030750100d0380342c0405800030346d81d42d074510340000c210012403501142c41c03415042c00401e05051a000c42e5214100f4011003454a0b4241140301c0c20f09500202150f80c4251666040b5005844d00c0c09158042c0c3e00c500400310300e5402500c1007003418104e82d00320604142c80c2404101050b40c1e040c03c903800311680c500f402e075501d10084050034090524034a980e1090381000d0000010190b008005210003d0110307080400c041c2d00181d103120f55403031050004001000580800e422144910 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 344310854 1250 344309604 344309611
    0x90604120528031e3905030c06010902030114041802030105010620031908150d030e040b0d02010207060c051903051b0316080913050a02190206041a06150f03100e0717 73
    0x4082084e0410050801c5c900d200403501141d0340d405c00b040407100004200442e80c090329114409505541c1407503503a0b204100420032a5104507141d104100010b0203c1ca01810603a40140c000c2c4660368644202600d030b070849150303003004e02001c01c82c00c0940d90300220a880400103040d000c01511004ad04007240d004c1c0700078111030303101030b05403d84010303a1b5950b00003810410300c691a0f581c00440c0c080104001c842c400c03c56a4095801c0317200c1240103070703404604d0700203803180d909100702d2040c0c1d6130806500d02681c40841131070f509041d60208090507040400fa1070600092510140301c030795540c40d03c580380d016907000d0042c010803581110700014070b1171014010f400006041071045d50b1113155801c0603070768150317840301078541c3c0098a070000083c800e4030361410305032500003000c0c0c80c1011380d110411107100d1070751894004030140108046580e10742074401002d8034014560740307a18001602d100340d07500540d03104080c3ca40040000032201402c5001511400071901d500b88201c1504000c0302d04140000c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 344312104 1250 344310854 344310917
    0x60905190902030a0f020112020a0e010f030209090c0a1209080903190b1303050c100606030b040207020303030c0304080c070b03070315030b130c08010905070515090604120528031e 79
    0x81c030000c40446000d1025080400856507004bd131200306400242c04400c00030209820035004000003103160f158107091540011401c0851503540c080700204544002c000071414040c0d0342025122410302500401a041180045090b0b964501d1002e41600040b401000c4c01012004a0000148507140c20384088030107902a0500500d07003c00300951904151b42110000b001a507142d40502c1160780c544180310003040144c504624105458000a69a0000801c0720405400010000301084a020140d5040c03019410031965034603181c6240d808140c10456004001034039050135001c0c94500140b1910803030b50050300c41c01e501d850303060301041080001202511502c03103854001a03ca10248600f040d0745010744d01615803181054104a01145442e0310200c031404c00740013103038a6070f9686040b50200c0303e01c044140600c5800346070540c04c001c00c488544400140101c4070140541c840c0300c2a1480902c6990391204d03400d83ca0003c03041101c0c1c03400c3c204001448003034139100c200b07220a42d00c41015804 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 344313354 1250 344312104 344312117
    0xa121b0b071404030515090706091205070504020403031706100c02040203061f0903051501060206010501110a020d03050d051b091207080d26040f0b0a0f060905190902030a0f0201 78
    0x5450b00d16a42c840d0f4000c072601ea000c2944045c0d42648403103803e801500020103807005914002e001403c015142c040c4084090307541000104010081042c070b0018074010300207640300c84d40ea040c017400100c2d4190148000402c0e100c0080e49500d07195468022200c865218900d11032743ca41c090100a41000741001d41004041000c1354810003495520703065505260f450302030060648c5000d034140703c01c041c6c64942d44041c0e44014042c6540100c0e405066817401e103001c0c2413145000c1030341c034940549810060340201e0443c01c42001c0c180d02c4001401c1c140e00d144828450b646070301c03900119501009044803006501488030111615100d00280303036401612085440c110340301c0e402c89080550026801d00420048400c0181c0c0310102c1c1c81a01d03000070021070810407450280c89401d9880c03d400c00003050440382400040a55441d0341c095400e816522600300204c54844c00004002c0906a074800e440801040310000c00c0b40360f50061010a076400f03400351003415020b584a24460f50200c008a044c082c2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 344314604 1250 344313354 344313377
    0x3030218090907170114040308191e0c0512040305130b030115030b0102061b030c040803031305070503010917070c0315020304020916020a110a0b0c0a121b0b07 70
    0x11407010031401009010003900445141a01c3c41240c4000c0700c8100101c3d906100100c071503d001500e6540d4031a40509007130045030b131100300c00040c2901024080a0407032421020415100c45085c90701c803241002c100802c021080c6403000d40b6540201000344107000d0301c910000e00024400c40c060420090240580011152504040d15464109130403054400520f050f640b441c895150145000c50785080c000361449041c024210046291601e8002000100010110309a200d0003021075004150600a40e526030401e02840f00185880000c291103900c1403040c0410946010310a0100050744115001078000d15040c0c400c01540201c90143e9030700e0314201d000408140b1050184031a0314054130300698a1420748104481100b001d031040401035404280707000c40300d03000070381884540d400142041c40180003000041440c811500080c181c0c1d18041140400414005079442840c2c0c0305000c085c5041c43c000c00120740000d100d42001e10000b02c13980440d000301d4040c281c003d130071201c1c5180c00d821084 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 344315854 1250 344314604 344314609
    0x411031612020a020c040b090903030a09020112110307031109030a1509020301020301180e06010509060f1504081605030a080406110709060e0901050703050f060f010e0405090105010f060e01080403030218 89
    0xc000b43c16003800341c1c100d01199402454079114203040c1d440c049604000d1401c08104860703480c00028070811107166983c00200039a030103040005e4a0062010b000e101e006e007640c40304903040e003085e0380850201c2d052440b108160b00321403060711001c0030003400501c44c0d41e0306504c98001c1128010740401c421070383ca484004c056182170000b5800381880c003131564041d2299081c04c00c01c032428000502102e4001c0801480b96030355070483c154125104543e0041c0c1d06e400b217000a411010a03884440300302100280005441038041220b0044c82000541c0d0904e840d40e403824151181c040800050031140100401d00070b29010300c04200084c01603d04483d8019251507803c1c08407210340d04010b54604010081241d021424003840c1ea21039900d1400380001d003021035840d88071070300c05404a840307a0300c80c0d81c1095050744141c60180c000706006006000506088005a00914080c09605100480c5200200e2a0390213085800501c0c04103a4038601e00e5911510114025040080d41c102c3c1035000c00146450755 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 344317104 1250 344315854 344315857
    0xc15120109090c0b0405030d05032d06030c03120a180b0d0906180b1b0c011103040b060d0b01031b0302040c030608062802090d0c060914041103161202 66
    0x2400007681c0015414031a00308542000e40d07030782c04040906030421092141c0c0d10045034108114149007003140d03c0c0d403030b860442c004025000c0300c04000b020401c0703049a403200051910601414050303083d5900c0143c20014180c8524000d42e00d5a003c8000300110b95015103d910348401421140c00c6000c4019200c8840540c00c4d88101900a440f0317864491850511509100301135440300c2e0701104102c101d400741e40305800400010502c4258604040d281d9245003580c600b02d94013140144020041514524450ba106810580301901c1088500002031041d04100324101165a00b004806806a29560b10f201e8a1002c0280741004d201c03000c40e0010050f110f03030081a9000405860104490f4202018a031502c01c00a0140c80d0703454540084104482c4000030500c80c10820b14005a92803001d900411050110b90300b0041611200c0a0002045640130048509907400b1440c01081e00c07071030034100000d403080041c200c040d2100400104000b540900d481c190000580d0501e4080c00c086a64044c080307 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 344318354 1250 344317104 344317109
    0x13050309090c04061d09060d03140f0409050c04050607121707020d0e0418080702190f06030b0301021201120311030a02010609180c061d210d0201050402030c151201 72
    0x40d0a0040380034065142c20601c1ca210125040d00b10700d203845c5030480007448420001c3e04850048011110320f03003e05108040784143c036802c1c440e003d582c078101c40c500e07070322198014421410154601004180d1100c1400c0c2101d04507080148894181041e5880388040c1f210a408150280280ca400b00d030002c28400c10f40511501c2c582e0054801d0010010000d8481a0a40700440c1304520703040d640c0b407211600d07045c0450701d150801c1034030751640b500d84041802e560401161807100d06510311300113004900310040380255210365600703200010248040c1800d0f03005450010a44040300f00042c40311a07800500e40240a00900c0c0001120800b04880c0741554404c0942d0b5005075100c0c0000c1c09059010702404d42400c1c004110010301d2019900e40c64034480d140e00034030040051504280040725108507008007854070060a0f1001800100c840000100655000c0c0200b4090003a210790041d006201c2c0ca84100d8000c5e024040b4070840404102640b071502860014034041445241c20b031a480c503241501 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 344319604 1250 344318354 344318371
    0x20c04060e1f0e070c0b15150a0e0307090204030213050f0402060c0309090408090102070605130b03060a2c010902130b1614011a0a03080904020d0f0e0703060509151305030909 77
    0x803170464103280881e00b00040c42c070041420032860085c100c3e220440041d101201481d1103649500380184102d6a4041c0b80ba0141e60601ca82000446d4be02c003c0d03030003081224801c035081c0c04400d040d25611800c1d03c0d001c80c0c0124582d0301440c0002c01504100d8002c0482a1009050b42d242019600014486c8a002d8405a602c0400170520140550f01001450060011420102d01b1310410b029a540d000c40c50380285400c8000c040085001034a4622a91014040600100303070b4101c145031082c2d240548540f050300c0901460000003c0c400d86910031a0f55040424000d44c50703a900744a0344501e01d92010003419a0f01404280f18404101c03450703904000c80600c480003181c030941c080c040e1401c2c003000c103585a114803c072640400004013800211200c00d1030650300540c903080e1a400042c000c00c43c03088000c0c40c85003400102e0511800103c0c8800642e84110000c00240c3c42d070710900d5a0b110040c0c1c1440c5592100140400c01d41d81401d222680e289200da4112490600a4070210745882c405031090407 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 344320854 1250 344319604 344319617
    0x140c03060d140102070303050a2007020f011707170c0306010f0309051204080c090604050705030f061c050609101e050c04080d080103140604030804030c02190602070501020c04060e1f0e07 82
    0x4207200760094004020340322042e001103485200c0c024ac0103100308800248039443c150038003000d80e4000c10f01c00c04006c0c03007414540018a816000035060080410b45072146041c118005031100783c130324054901400b01a52401e0b194545018190b00405010f41c0640315449110003101e01e02a00c840108050240903002e0195120444144801c0100160030303103106500b8801000380ca694042c064075484804608901080c0e120340010500f58440c00c00c580890400710145e131802d0040000d0030174040c0300804110f8404900e0005810125030981201001c4134403404000d0000148a400550304060502441e0749030554941c1018030b420800e040000224403448010400e00030402d03120400c8642c4800a4002032515580007004018002c0c0020103205512681e14195115942010b50182c000118440525182c0c940070b13558402a00c902030041c03081c50314054443c03c0c03a003d103038211860072145070925100e01d0718003641c650310001c180080340020800014401d03201a982030160f01c85407102c2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 344322104 1250 344320854 344320861
    0x71a10050103050109020325031e02040303110c090712150905190603080403150b090405010b0a062f03121905090d0207030303050c040f03050f01140c03060d14010207030305 76
    0x14055900c140d000c2141907105000f0402907a518a40c8c1c00d190a81030707070503034401030510350058008118002c440207512440982d410982d0500360b0041068900a498030404c1c4c0c0301113540c00b0b0f56103030304000182d0052052004600d6150041d404c1c036158003088100422034291014121901340c120340d00140d010741d1120140020b08002803040200005004800d00c200e0342107494401c4944aa4480280550340300310880d0042592680b0801c0e80903001000800301d4206418800e001e80b01002c4854820107824100254242c00b560000360240031241601c26003000c3c4000c500403040360300130a403100b8001048010088400160403500c00c15203400b00030510342081c000c2c4c2c0d0403940d00400e1104168041c0020340191600040c081c2c3c204c90381850b001c0307021385c6c429885c4421030160350f00101c4243c803074040c080104070002c1450400381013864020481d0b040c80101c103000040c07060b44c09c4080c0070020404100c85007080d803a6011150f005203503000382c003100200711600326272100b54191300081e50341301403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 344323354 1250 344322104 344322107
    0xd05032d01061b12050901090909050609060a092105070b0106050d060617040b070909020408030301051305060d0b04020d0c14040c090807050f0d02030706020a06150e0c071a100501 79
    0x1c582d84804000c209000710403e40c2e42d2036038403a414140e103406010b8081401c030300b181c2c0319007a40d101920070090f092001d502a0f00e40940d513201c0998800105014607400900b1121061055040480e004503810040560010616000c00e500c8060503082213020020000401e1803034110a00a01c0c041d81c601c0d943d01d000f401080110781c00b6401c0071040201800e001e58100315003001468000750802070a00c150f4483e0142078841c0d20260f841400030074008100021040008000b442c100d03901581c6501e194500380103098103d403000c8850642c016075a000c6080411011075006a00610203421003a0012440e1601e074000d05aa5008448004003800c0401d00c40c01c10b4021550b01031b210341007000790581070071443c8ae01c070761507401850700680b80d82c00340750710f01c9e943e0302070844180d6006400e030f4440d240c03a4079000b034a0f841042e0b001d0707440504184800c00f11107a0f034000042100c66039001d0b600d181d1943c40b20ba14944d449800155941c0c11440341360110040ca010441340126400d242d40c4c84031502d003900 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 344324604 1250 344323354 344323367
    0xd0b0103060506100903030509030a05071401090504021303150f15081c02062d0112020108010b1e070201050c12040815100308070302070e0a0b1507050d05032d0106 72
    0xc40f5010725948641c15241e075410180300780641c1d07410b090660f100c0745c00e08042850903072440000f600c1881581d00004203c40c9010f00c060140c030003a030b1035007130305511071f030a002c00c2e441010f1400190700c0703040400b0800701d00403080c400413a032462400401c84400989107281a206441480f0b0101100b41c1d004200d6580704000b800c0b8603c00404803210305040d03641001c0c1d12000c0041411008000c04480242048803d2560019904200352002003d5842c0c7d200128915089501240403075150310020840300031000c15242166841402c14400250f0040729540c00d40219500728140007080c0003072100c100c4207000214080700d10a41458031103240107401d5103480350700500350005501c01c07002c0c002d00c0c09021081c0c000340d94010b90318540c1e03044180340807407500c982940280c1c1d51860135002d00c140c00740c85411807500c50504548a1b80f0109609105c6032951040304002800c0307510114103030a030765000340b02a5504c00104a010075100c251080b000c01d42100040d40c141c9292211401400141d40124 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 344325854 1250 344324604 344324611
    0x60306080105043503010b0a021204030816031709060a18020109031101020f030307081b03060102060f061f02100c081003030c06110705010f0608061e10050d0b01030605 74
    0x2009100909003500e07104118203083c030040c2a403200380441c220031309001a9549070301151030b0600d15a03039070303407503140b00019000181010018011300301c40d113800300b00240a643c1aa50803111280c500030314082d00a85000700181c00314240a40000c1c0b02100e02041100d10744151003450150403285041c004079021900d200448820060401c41070002507640000c0c4501500c0e030003512007612000010050786007075004050b0502a00c40041007080050780300200a0240341d4076030700c0c40740240010800c0314650100f207a0a44c0140e114100084c070100000c840c00740c1040c0054180d004003000c0703881e615201000880b074040588e114500400e02c14000d0320419a03403580301d2a24034442d04003a030501d40031451512000e4104040c0043d200d0030b00a49a201e180760400032241a540c401a40c40c040b8064441d0710341802c5014070300342c000038021001099961082d10488030410800146004242881d50060147c00442c0d40320030740841e0702e03158004440e00a0b40501e5400d40b256140d0314144047e80c0005 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 344327104 1250 344325854 344325869
    0xf0609030e1210090501020d09511410050a0801050108070308070503040e040311150702100c050d230c040503030327071503060801110f0f070c0906060306 68
    0x2100400708900c0045400307810704202c1d01000c2035084e0f490030418007a0051008200e01c261810085000700a600302c150840190120302d1409200c4000e480c11015101c3c1d01c0c003040c41852503004403c0c4052400c4900c034608906454001511812000c0041c910b0a04031116024000400824002440c002500c031000f0001e00c0c000713101c250704000090361201c1d280d1000030880b02001c590300c0e0400005105882c0a081e101c11040c1b0b4600c0c080c18001d0010301042080c8000b401810b1848218151000406115003134a40060106841d5080c4440c001c0101184440400c2000d21235004804110b000c3d099171121081c400441e000c0b16418a080d410300040d001c081d6081e01004100455240402926804184080c0003540e0385010038005030b000c1010983c410090041120200700f01d0070b0780e514a4400e00c11a9000c00450f600d41141070700f06c17641540c8180f04114180700255410b8407140040c4100c60202480a08122050b40c542092007002e401400e801c54448de030030b100096140c4201d40050016 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 344328354 1250 344327104 344327119
    0x3070b04050a090c05041d0708070c02010905061b0115080c060c101e05040f060b0a050a0504020a03020c1c080f0c030f0c040803070c150507030215130f0609030e 71
    0x70600010100c40c0a4802c10a41c01e45640c007906080e400381d015034000b0050042c10030120006244000e50303108003114214081000440400c842031b20a801c981c000c29810b0719054070081c1008104021a0000300609524610402e2120b0012100b07001c1d5100d9104e0300401746600c541030400c0541800c044035400e6000e500240003035010103000203100740281900520010b070b903001205009c40744c00304405070610506c0c10582400300f0000442403100880b4040c00041000d00e480300204481411740b40b06655229038541d009012610323269004060075a6a07003401440c080c03a4400c2c260404c0240810303074a00c100342105c0c00c4403141d003108050742e203c100c0c0c185100845c0b41c406a40b11213400090941c1c085c40c4110b20015591110180455020b03000803011a0340307903001490031a40c00b05403401100390b911542d162802e0300902410036202219854ac02424a858141241003c24080180703a1400088100c41c0100411104485442c11034051800860305010a040141400e0580c80c10103025420 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 344329604 1250 344328354 344328359
    0xf0102030c040e0703020f0c2a0105120c07051906050c0423180c070c0f03021c06060f09050403020c01020d021b0d080f031006030b030309011b0f0c0503070b04 70
    0x40d0204540c1a5001004602890346a00c6130480c028000c641d010342d9500000140304901c07800c0019410403100c4080d4444051102c1d03104503648038244c0580c51408070b1406c1c007080b401d038105400c1c884e61007900e41703412500f411460703103542d464480320b400b4240b24103000f0345006c018418980100b40e4490b0400f4211458189864a04041100f028009510800021924014a660781c0c2d000504030310450241d00c00d00e042ca00c480400603805210101e41d8010203601c00a480e41c41140b460f0103c17600185201c048500b00c00010b900140ba1303440c21120a9690b19010500d011440142e101a002100c000907042c5064034000e460801010311540c1558000c04030100240d60000e0090122032450052916130f00004020070420420762000920400b8007041880120003140081c52081c840c1000c03140884c2c2e95414168125441f41c05940d070584c1041028146650050754200e04034010f40e000070304007c083da103404040080a0034210703030032094a1800c11552a040121401a01c800e036001d518107813 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 344330854 1250 344329604 344329621
    0x304120807080105010e0105071719020109050a020d05120a180501110c012111121003080304230d09090b01050f0403060b1908030306010206130f0f050118050f0f010203 74
    0x9605201c0c450400c80000d414440c071b41d1048e01a2610070394032400d400e0300084514584015034102080d01403c148850302c1d07881d0301c984140204200390340c20030007600d055585074080c8000703208a010107980b80d03c588194002014040c500a1080301d1042d903582c1d0405c08060562005940b0550105042200490340c1000c004c034089400c018100c3d090a2651040b00c0e5594000344050034050158400c078a855000601c0c848201c0040445401520440030f20f552000380342501da41d036a0001420072032090000a0000c3c0030f2050380d10b401d0802c1d125414186503200c1c05503213800440904000003d01e204400c0040819500410580031800d0901d28100644020b91000502031440080c0903552950308480c43c98544440c200103600441d0040c2c200c0d1501c032102c80b0303545d0f401502d4146c014821880050140548800b4244e03510340c2c41440c070358200500d920782c00420740086e0000e0b1815542ca400e0341b510300c0d140401f6144032038800c0700603084000000e1426420040c0c1c0c3c003464100c2d070740100100710a04 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 344332104 1250 344330854 344330867
    0xd060e01031a04020a0807030c0302040e0f0d0c050c0a091416050726040f180213090b0a0509090106050405010b070515130503070b0108012901050a0c170304120807 72
    0x80a12482c10030580d6501d0001800c0c010b01540902041e0203a9000841401021150303101a640203403400e101c800440c4400a030758001c1c0c6130780b042c1d035500300340000d030303c828850070f9400461703801841118941140c0400080710030700190f01a440459135616002c40801d400c4040d240d108403a10300e841c0da8403c681c02e000d461440390003001080c102c41000c1c81d0410310850740306054017007001600e090b107958507020700750540001d50169102c2110345103003d503040b840358021207000001c1401075410013844c2005607070140800c1d01c00e0381e5001400000201751601c03011441c6100e4040d02d400480d15034075042c280811908107030400305880800304080c00c041600080d00c0701c2c0880b0b14000384649036403081c0480030000c0c0c152800800a010000b114805d121485107802e050300c44010013040321804180000740c14190001200c0100c20010440510a40c000c802400c2444580e081c0700000701032b5546c0f4006040c03040700c0d030803480e44808020321082c07000405d03900302500c0d40c0d818644490305005a018210 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 344333354 1250 344332104 344332133
    0x82b03050601050a180b03010e0403110a11040903031b0914030615060703140c0c1f170712020f030411090405070909080d0c0206040b1b18010309080c030d060e0103 72
    0x20b020032000082c080c0c01160300703d58001c01070382d4a03550302c1e540c650030489c03136866060f6400d0380041d0b080558040b240501003400716080d5032121024042c0c5211b80305100c0906101642541415074880ca0301c46010700740b190b0f007044541c0303590b00c44034a030b801e0a07026900c13006602c10711800303640014200550401c00461100d40c290044461f552681d0b558513040b2400403102c510814807600105050035102000030f505200c000023100e628071b5202411040c1e03400804001440000204072001140b08400c0301c8102a8020001d480c00ca201e00d14103020361016039021a0300c010002c0000400c004c1804512952212010002c58107840c580c01c3ca900c03281e1740d5000c00d00400030065601d80c00d103410080268102c03000040181800d11821441410181d10b5039011102507400620b41c1001450380f10410944a400c00700c01505242031090b000744000c42c0d115400701180c10716544907034040100b00d91402800c03613000d80000950362800241281010744642d90701010282e02548014000a24000c403072011 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 344334604 1250 344333354 344333357
    0x30906090b0f07020f0706090b091c0c080d050c0604031d030d080a0b090405030f210a020309010f020c0d1110020318163b01080109060b1f050c07082b03050601050a 72
    0x84034207501340002d2f403082c021078401140300006503a400030080402d0650080b201d50106840a00e4103100091303400d03200b81c80a00b60b69402a10016000902a001003080750021210554400c401600881d1070b05048101c50004504100b04105d5040d02601880c1400f040544589000381840d941b40f0755a40200c5c070b03a078200c500c004551050716850011140e0011007039140c0d04945410440e8240380258030071340c0c2c1c00d0110f500313010003802101e0403402240c1c454031344c2400908400c442060116014000e150001841c0d000d0440d4800948441d4005580a80ba0f13042484181001a074a21450207607205042d4002102c1580c080000000050303060018424501100301030301c08076541407240200110302d07400805200000460800c4055016544c03440c855071041014018180400007001401042c2011511144002c6054a481003000e0300d622880c00c03085505003601c0380041b50401450244031820040c417440d420002500c1015000000d00c030341d080030480c0e820410300003001440b0742a40c020 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 344335854 1250 344334604 344334607
    0x21c06050105070311031c02040501030e06060f040c0509030303100510140d0b0d0210020c010f0503060303070206090102240f2d0702070504060e040b1015030906090b0f07020f0706090b 81
    0x45e6032060080ba070f80440c00034040d010559561620600030b40041c02003e00007450210000c19450f000203206004005c01040d003010f241d1901c08220141c03c80304100d01c10800f0070310100840d40c8041024500031031030300f44100a40c03030503c1c1c14421f03880740c50807507001042011301c403810721000a0000c451010708460700101e0a9412400469040d08510344c0094000e5a180394003000e0580c0820180000d1400b41e82d00309501911610803030301d501040e500558150402c1142000505e8658000c0c03a4020307042c0161060765200103202100f24400607a545c0b04c90480c9401c01c03114107a100811540107100308a051010003070520700064590804c0d004010f12501100440d110500030030000f0014000280305100194461152402e4040140c0c1c0072140c41c0101c402140c800303648040c8100644003000c0c8007103400300d1082011000340080303200c00e452040d685c50540c4041881e4a05503441001d10000506590901d820002d24114032201c84000d15008410705016483d0700c42c2800b0202ea00000900e17 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 344337104 1250 344335854 344335877
    0xf080c0a030b06030a050106020601060c02010905060711060408010f0f020c1c091518050a03150906090609080a1103091e03010213080610091505060d060f09021c060501050703 77
    0xea00420142c482c00741d01120210030802281039907007155060303441d9a03003600c82d945d982d00c000b95400e4250030402808034401d95001d200354109000601046400751341401c61211440380400d90b19030242c1c001005a23511110342c84100d601a0013000d85807104a01e085140213203500040e40c65400c00c0460281c0340c950b0303440300b1444034452164407000d4020300301c111859507001d0801400072841100b00102d089000c030800204c0d032600030080b1003141e400c0340036980e032110f908240c0c0001380f40034682121925a10140003010540034458010528819005540c0d5803000b184045c044101240c0401c50641c010082545a902d406202c030310303411501c4440106c84c0c20b20400081c0640108400010f0030081c2240000b803108000079064003c0840360700d8100400d4890713001d6810f844610f200c9924201e410380d4100728500f4004001c00b9201040c50300001c1c0b540d00c07001108080d040d603030f0140c80c0c5213802181402601e40d040d86079000860301400c040140618000002c1d203203008140d0080d0500c96018041d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 344338354 1250 344337104 344337107
    0xd180b0f09010b040510031a041703070306081f051305030a0c050a0b071e03110909130b0901201206060c0f060408030412020105070207050f0f130603050d0f080c0a 72
    0x300c034030400c0013071082c41940b4200c43c2440484d01644030682d810000741610f01044440e0400c01c0340039a401400710494410030642452031544081c046004140c0d54041c00140c21405015118410900c00e11121000218614601c2a5030010300181c041c6031018002d080003032400001c5511108140c10559810f1806041007070070859034201c040e090107100d500300007007141c0c007152401c2d0105602044805141a0754021012582d1340b8058030641c180c00c12001c07240c1d18100c11080e5108502c003c041002e510b16650f038621a01e025540c400281c1e440707013100300d00720703556084000720901d0098810781080031480300003c004e44090a51030207403100040320502c0003802e100407001503030b040044401900385442c003040154002c9500342e5600c2d07480d55902c041544103014490052000784e004004641c00c0030200140001c000ca40c4940c0044050006507007925440810b00035aa40c0c0400004e0581c9503041007414003e00e000d10307000f04800c03000000e07119a0045c8409410411200803c1d49903c1001c50 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 344339604 1250 344338354 344338361
    0x20f03120301120b0106020d020a0f02060918060306070c050c090703090c03050a060c05091e03031306080a0c0516080d0204030204021803070f0501050409151502030d180b0f0901 78
    0xd50300080500000003084101c80d000030840000d101d144a2503060307990f1b46003241c440001030610030050b0031080002c0c011070500c4860041c202d0004006c14644148240010107200141030b0300012507403058200310b81841e081c0000e5a0250540c141190044420f644081d1220104010680300c0d520101c08144482e2003503228209150b03000e95a000305c25142d0034495030703411410504507103860400c10203000440c80382d030a403040300d80081d001442418107401c045001800d42c03503c0c6500751000748224030340d8504a0030b0150040070300c0d84600c504c41c2010034886003a611103000a40620000304011507079594055905020990060203140e2a000c860301d00d00013a100e070781c0c00650b000e070000c50007410200c80030b180b42400500440403964002e94038009001a00380a02c01e4501194080c802045514610740042d14070807050400d008030b1940312250403031440030203071030080142d1000c640044081c13201d1003402c402480d010420181021695625581980300505c4a105c1080701000328591107025003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 344340854 1250 344339604 344339623
    0x12020702040c020604050c04060b09010c110303030709050306160806010513121109130b1906031403040503070605030105092e0b0903010c0e0d0602090a0e0103080d06090507020a020f03 81
    0x240188469a1100b030002d40c1c0f07600c2a54182c4450090f00c0406800e880c0a00c00d25085804141030282005a9030b4010759601c0003281e026180c5d0804a00c40c0e5003d90360510081d0720442d1907484480e10b041c01d0400703041c80c100d4010030f0340ba18007400010381105a074105929945c410001d01c0d199580f0107815409001942882d40032182000c400d10a15081001610302600014016a203c159543d01c0e85c9002040c00c0d88100c01415900481c400b10707002400d100c08a0060060012000c01d010b540c1707039100d0308004440881181150800302d020b00440c90240000c2c030082a0601d00340f4159410440061842d1001414866003071668000911003d082d0300c800d4201c019110403030025096680c0c240207480c1e48684902d81c8203501c4c1c500c4101c082c0d40994528015800050103080080f0490b0355104001d51102022540c085540000020841903011540c1e018500c074480490b101c0012000303c206440e096000b880815040c00204148903070b001031203400c05501180c00700c03418085400403e0a104a40e03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 344342104 1250 344340854 344340859
    0x20604050d080f030c0315030a0b0403050906120907090b0307031208070903080a0e010f0221031f091e05090d081906091d0102160b0901060b0d140f0105030d12020702 73
    0x1301c1080400b070b1004003d10300c248050720032886000e4161040646444020310001c10150110b0b0200380400d104101820b80400007034034403031502c3c2407503255100c1284c086640424642c0301000512210002e070160541e150020340040074041d0a640e5108407500050418400300020707000003401ca00c1c4121104001160040407803030307540408860041480100310700706030210702840d91108646100181c140603890150224440c101009a0308500c2640050031203a440329051500e0941a04660712280c0102000100010702c802c0100114000d8240303d21300341012403510b42080002d00001c80d045044024928004a260340c501604a191450700c3c03222080c4a840c1c1407005c40c850704036511030394441000c25a400e0ba05944101e0b05400d0b88100c9040d214140c040c4000e4100098140e05229002440f0500100e100c6480c1c0c07030001065000218060509034850050052054282c80180c0d040020100340d0706003503040c80d0100703a41e4000d44c3c69900400c4400d842001400c0c0300c9030f060300e0003079500 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 344343354 1250 344342104 344342107
    0x1c410c1504060f0e010510061409041d2a0a0f050108090109062d0203010f05011101020409020a03090b09070e0c070203280512070c03140a06090b07110a020604050d080f 74
    0xe04c4598002d0000315981602810300720700100d545800340220300c480c1c2030300d401e07070910b400c4840040c4405003040540800c4580c1ca0315007401c0f400f500500001e446050311080d100b0300d802283c0710032001220320601840c040d20320030209000300c2d00c2410503c4141c800030300300b10701c083d25a4201c03280100b494506c0500f4040c0b0741b080c0c1007201c20580301d030003540043d01354020050303440030f00106080384001e1040e0b40d202c0c00c81110800030740d4010700c1c1403814005140001402d1603031f0390f50642c0030f99202065000000b0341d81c81e010010000240307078480c1c2000c81d46000b407040605000345107000b100e02504640e01c0f0300000c00c400c03045540030031501042003d2100d83c030580344c20640040022805004c2d0427650390142d01a86e5580c0030011007035554064000d401c9030712061543e00c421807a0881305500341194000c1046130301c0890b8080c0611260380c0d12644100250745004800103100e44405100b50030340742c000c40c0c841c1d000340e544c01e42605c0136548100c802036511809442c00c10005c0c0310b00c16001640c04030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 344344604 1250 344343354 344343371
    0x10c050a0602301b04150905100c020102060a0203100302150c010e0d0c03120608030a0f080c072105070209040b060102011505031c410c1504060f 64
    0xd40381c01510b00003090002c0642d2050103001d00c200d0f0140001d541515101d076250000c1c0c2c0e00e54080728111502e240f030320a1246401c0e21601821070303200c07400b605207011661956080100d81085e07040a190810076160100d042801640002c4d29210701528080c0300540100101c0c0d81410725020080c001d40e0b000b02200c1590620401c6500160040d4205680d10b5113030080c1d041c4154404a403040000c500e80d44c406071401000c0e41d0650b0100c0c071040d0000c15031665640e0120306c140040004041c41080c0fa1030303414100c20080001080d00340001c2038400b2111081c440d41000845c002c01032900c800101400f111180c0c003000c400c48070350281030030181d407180100303080c00700f40510130403064060802a4024401442ca24401c2d00c0b260400c1e102d029007584c4102102a0100186a0540d41c2004a031800311800d00403085101000e030120300c09001401110079090b42c00c1c1c6400070740010030300c2400c0070305803d103490341860340e8507040740c0c074150950525820001000c0040a0b8480c80300c420b03500e10100040b42 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 344345854 1250 344344604 344344613
    0x60a080411100219060204150c060c110a030e0f0301020a0c05010f0603030e01030507030b060c010e250506130f031208060108040519051009050609100c0c0809010c050a 74
    0x2505840a030740506040800154904141c40c011281c103509400600c0c0f038480020000120f4007010724140c400a90900c030109143c001c2c404680a04075007640c42501320341c1c40e804d20b14201c4100c0034141041c89400c40c00c200844d400400d020b0f042c243c08d410b140030041070600100b803201c12602e41880c0d040d44000f0303425417241d81001039002c0c120700600007007260555090861003221060f02014011451401c0e50b02100c0d0300c2504200d87c070013820b00d00030809400e990302240c404c6d00051480384035039450305900605c0c5141004500c03104541e80d40c01200c2152404541076149049010725405050000340020700050794a1140f0001d158009026804543d00e05144581e191300420800000d403511000c0703500d941c4500f601074040c0d030f04000a00000600840420400d1745440002c441902405480710449545846030224160103500980494505040a503013008140d038040040603161101140c81a80d02020214070290302c840455541d4a410005035003800c00b482c40180b05100702107103002080b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 344347104 1250 344345854 344345867
    0xd1e050d24060f0c0302060609090a0501061526010b070503040b0a020d080a0b090f060a03020d20150426011b09091107120302070b01030f02030c0d05030a081005060a 73
    0x101c610342d03a240501441c3d908212220842c0c0100500140c1c0b028001c01c40354a89161029003003c400d008403201021955034450a584450348000c5040c001c00b02140807858110724205043c600500c6130b050a210914000c116203641130180104252001c251036042210400488001d040001c81583e2180034400c402036803182e40e11480d10008051368040386100c43c2500a4030398044004000103010b40c1c0c2c0311201e20540c1c00080c1520b600190240d000005612110b0880380321034080c04e05181c0c0c40c91011140c0070406189424a1300841358103802e0020400200180e03001d4500142601d03040c4d64440030b6110340c402c0d455107070202c59442e0200154501c0c441d841c129020b6402c03178450305406581e41041c0d0084030142c9402e01c0c0c080b03404001500000c4c0c4200c9043c9141c150310f0800605001c51a103414102072801d0304200c404980b0404050305503d0304105180250300100c4814a1080c1255921901c9001e0f2680c42c0701404050b202080e0481030001402c0050040981056141c440184004066 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 344348354 1250 344347104 344347109
    0x10b0a0207060f051c0f021231030c06060e07030f050a0e07060c0213050405030a1101020306011d010e040c02100b0d0b0105060711060a0c050d1e050d24 67
    0x341c4620712002414074010610854a402c268503110708101000d00382d01c2500114180b4010400d98402610070f1507003661018100018465201e494545440349010128250703540c0c911340710203202c02a0720300c0b00741d40d049107541c440d5051400703511405180c50b11001070f25658015044405013030003040091036059202c4c144801c1c145c1410b0001707448480101c8110358104c000e8480d641c05c804020301085005284c0101c0c414070103003984030103814551030030088540644040301c1d590000034220748169440741482503090550402180b8600b00200040d08020a400400296416280303911006a001380004c2e084440050000d0010040e0114004c0d244c04290058000b0103192030390709642030802080740007115a010f0301c0b01002d44d081000f08003c41d0400c1c0c604490640c0c1e088c60310300d46902c0c0d00010380b680c1c00c0d07151954090400135184c40303801c1880454001d0104148a140070041c0020354910810707040090a1241c0e49114500c00c10000c0c00c3c02110b0640e08904d170255050f00107900d07451034400c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 344349604 1250 344348354 344348357
    0x733050402010f0807022512060605030601060201020f04030b15120618070810050c07120207030605010b030f01090203061306140a0b0a051812010e0c0f040c020a060f14010b0a 77
    0x464880b214103462400f4103880380b0005a02644580b903890803000e049140f0006103072400f1b0503c0340d03074114044440307142c402300f140c0c444e4582c0d000700075500303040000d1030241581380001c1d030038103801c0c071102c4116006610000e860302d100c1401080c0101c40c42692541140b5000c0c2410386200541d00405a031494180e50b4110405e6440100000d0040046000000d454400002e08142c00d492003001c07002d440c1c09050b507804810104401d01c0000c5440c070071030b00c4e10007042d00078045103807842c10140c2c200e5005038014a4404810030410060107c603104050644030003100c016240d4071a0008100018403660704558801e00c0c5c0400490b501a100303074880d481c040c007281c462915503140d0390000740c0e40c01100e4422012a205000035003c5013243e48500c60802030150421007607810b0590558259130b09840050510340100040842905000b001042c1d60841510b0501520f5075a540013591100310000240201c1d40e51030491101078001c1c0c0040d050344c0c04c00844040996110072070700383c80da07001445010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 344350854 1250 344349604 344349617
    0x30a120230101505031807080625030207050a03030e0c060f0403060606020a1e03142214010221040b030403110f0615010c15111c050c073305040201 65
    0x3281c80300703881020704031251079443e13506688402e00820f840302c00d0304420007041e0040b05408038402004000c4144035260306420340c51011544526001c20030355822514040500420411010400001d0b8100c80f01ea4180360004038501c0309545982130414801400707038441c07000150612040f5240c8090030650303001c0d070403c000240d40c54000f03981e0740350803560051182440104880134034403583c1ca42a0039501909007050b13001c0282c0e1b941c1d0f002c0d9120f003140c280f04a0700b9418a0a043c1c1a550548003d005030301c04141820072031000103990340c054140c90394129000380c13000e440c0c80c242c0341e8151402040c81414041c0c4034181880c001d401d001c465200003010f440340c2310031541c03e80c3d4006001401481c0c50340f8417001540320324004481003c00b81c801910840083c0a011007000000c1c402e140c528a0340358402500c84011100c454400301c1010b0384440d1560625080c0300d4010f2820f011281c582d035011080f14040d221000c40740c107035842d0543c400307100e9a030000c00d461844c101d642c000b1440b540c400d85c2d402 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 344352104 1250 344350854 344350859
    0x9151e03140a02090d1e06140906060109030305040b0a02031c060e1b03060607080909040501061d0408160321060603180b011e03020a08030912030a12023010 69
    0x8800302d004050150391300c000c80d09440785c0424001c030380c4904207003804d25082e040d510551721500309542401600c0548070120004000381c90100740605500401e0900c3d00c06103051468030010458000c0703000303070801001d0005200804d01c0c020022a4449000783c0008010445c120005c5001042e180c0f04990b2804214000500808400507402a80300c22840505085455003014400103820a000803079040b8420060285940e580c2c00885200701c0c0f0032000460360382e08050310084d11013245070004826803180c005100c00100604252540702e140c00182815594403410121900715520102e1020f2281c0b000c85900102242e030403420a4074201d48082c40381183c8060a4101484102005032441c0d8031100140001058140500610a001580c015203d47c0700e40004000c1e400c15400481a9400017032004071504040b0044100080010701030f509000304020050403400060040354180b640c00070784c0380000802903810031900000104405002144000c079416002c1c81654805021030840800 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 344353354 1250 344352104 344352121
    0x5120a05071e0303120b130c020d02010b0306040209060307050d120305010501050f09040b22020408010b0907020a03050319050a05091203010f051302071a040311060709151e0314 78
    0x28000c0d90b03030030724681151091540e02c0450750001803007880302c82580c032011040807699401485091081e0200b20008400e04641006072030480d21080010a690400840c9801c69901248082e40310340c050b0740140a0340e407000000b81c00d04103190841948000561200380900000840300d1140c0b401c0c1d900c00f0001a43c0340c4006554502941e1070107040d00c2020405620b55007030a420060701c1d0000a0030000e1141446c83c000304104151107a03c0c600b655001c1420409580300740070b1149100c00a4407440113600b8885002500ca8646490103014442c000000c10103a40710300f000f0124940040008110751b0400300401000f510060f0345c140e546100d0900c104c0607103072502d01107034105d48880020300d072514940014403c2c00d007205544400f24581c2800403401003160038140380030303803401c0c9101da8000e840e0600e000341013010700d20840c2078550300c0396003001015a0003c0b40c0710151841c4018800ba1442c5a4200701c0301303d0300701d030b801400c090303242041004041e402d1380000c010003ca100b0740120b6542e681c5003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 344354604 1250 344353354 344353379
    0x6010206010b25021c170304020603070f0e09040c03030806121e0106030c031208090312040212011d0303100608090a110102030d02071a0c1905090a05120a0507 70
    0x1078004080d010066558116403a0b80d04166500c0c80300e415400500903030f00094440c14a0081504178803500004071410400340703c2d640040c42808044e0b044c1141010b802181c1107000040c18081031020700c2d82060034a0740551300c944401c140c01881480315151514149002e10664030045003c500d001021411600c1c20882d03201610202e40000c0650340092a4050b211031081d80d942e103c95540c60744017102003000c945e07802c0007171130148011602c403005036030009107140801000399025800a2000484005081c1e85c01130300960101d03440051100800c009900410444200381e01c0e0401052200381405804000b0b0342c45152844118016280d48880569007c41c048070103c1068204642d8480020b818150440401006204403810100650561400c0742c2c008402501e8281001c404030605034100f00181c2d038021007205c22a03007807095440391010210075040b4028103110000c02c168069480e6060148010300c4028000e9440c540950401e80e296680008107540307600550901186122b401803 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 344355854 1250 344354604 344354609
    0x24090c091407030b1914150406142a010b040f02070c0b161a01082802010305090c030a0809030c150d0504050c0405010603020a0207090b0f09060d0f0f03080601020601 73
    0x7039010300755407804400c60051098054040d8001024404a03100c1e5015040702c030003400c903840104142a48040411840e40f51101e0f4401a10f2004c00081c0103079036011180402036032401001c40d481b040d80340000d0358000308640c2410b0a03941c02141902c40010150080d0f8058801500c080104a02c0c000200c004c3c0d2003103030809040c018000d6400c020340c003a54401009018040c0b0040b8083c40304c01e943c0c015844034002034000d5039845804c011f001d908004c0c008c0294100c0c0500d00040100c4900c0c1d018043c020003000c3c00307418996641c0000304c0c000000e0101498820004041c0c41a2003000d283c0031045402620740d660291284850007421414200180725055002d40700d40c07420950810141c4014220052044800d80507061080465443c1c50050501130601d5850240e141d040c0000300900d081c1607035001003e1181003a640c3c010f40e480b00d61019288481c2601c20044599403080892544902c524000f002d0240d45008401801000b4520116140c429903c0810f16100d0320f00481c3c0d14142070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 344357104 1250 344355854 344355881
    0x20c1c020f091b07050a050f07030b101508101509060e0303130b0a0306091401030303051530030412050f0a1104090f0203120310080a0f0b0424090c09 66
    0x20f90741c5107901158000c1c0c4802e0303108100321045482165941c40c1025075848001c2e8046e4032003081031003041203450301254002c41601c182c0101e40e00e408140503810924a0018003405060004101c05184842d90700028141c1c20a58003907050755004000c103400164401d40001030074043d915001860003000300c0301c8502980c02c8134941c250400040881641c880b0800c0b01c20f03d1303500c000000d504d0520b8002e0103a00b044200b004039080d851818058140c41006060315032409140c20003440c0c81d603e2810b5070102100c05030700d42c5045510041c180020716055aa13806d0303076210100b00012900d040b40083d8842601c5401510740308040924400c3d07590124800c001c0c544121040b10b801035041c29800801d1a5001c1d400c1d5040e450349030b0700440d0034000d0b03000c0112006400042000301d40e00000800301c0081c25140e0003015103030a0354031030a100300d1038480d0040180460b507000c2014080c2c06407082424a544c42c104000d070440812a19000b0500100d00700c030548840710000038003524030310602d0580d1002 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 344358354 1250 344357104 344357131
    0x21513081606030b092d090102090108090625050408070902030105010f020a080301090f06150e090117060606030a0b1203090f0d03051801030f02220e0603030d0c020c1c020f09 77
    0x344103102050380d20f0700c0d41301e01103808801e0066246d82112001c450094040d40001652805842d00041c118580200000d406078080303410f11911016141d03461040c00140d665904030400c50000489040c032456000d21000d01c50020049520225580114129102603d501240119510050341c031005070303810181c00100144010401010a904421143c02004100045003a1540d1104128501d40384019000440800445140342803070801c0ea405030440e0184071000c0207a00ea0703840d41d00c03140200194000d809c007201103050410310b5003040414400041104114000b001042a50ba8124450880c440c22410540b0303007242c01d10b620301c205800e0701070341d82e00c1c030f0080d1180e00d02a50103a070307107a83c0d4101903a910f02444004031502c090000b03507401c4110900401c0c0002252280c110700e50f00003000c140101c100b032144983d00007045a444402400002c200c0c1d0080010582c1400804034000d90024182e0540720b410012455070320301c1881c0300301d4054054898100a100801d0070031640082040d84 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 344359604 1250 344358354 344358361
    0x409080a050d0b06041409093714060910020a0509120a060618060506040503030a1206030b040b040b09060709051504090603300903021513081606030b09 67
    0xc60002442d462205903400304201c1d003800d01081007588141c1c0a840d44c0d1007007155100d100c1c68001501604500100000c040490001d5441075140c0014001544482460b4800492000d0030384504c1c59160741041e81d907a00410409607203502e6150803940007429002c0c47d418582d100c165882a96414903d5541c0c690404d2014410311001100d1060b0f03100442c440c03088420001541c1d2f0003a10701821076118201d480d00100c0c8445422b03608240c020030f110f510184014422900c000007920f9142495160031040200c480300b003c401846d4541000d08240d210700b00b0001880426a81c481c051807043c3c2c001ca42d1aa01c080440e52034400c29107422002404005040209280082c04808190440002d01d0310f0b0650701e80402d0119144c90740201d98041c4410381120a00da0200400041d0b8400201c1c0155102e1004000509100e00b50000900c640c048540c10003d140d03000f42a40c1c0a20a410700c0361030510380381c10a45549960719240311030380300440013001c64103d21a0141078490000507016814545 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 344360854 1250 344359604 344359607
    0x50705030117030c19150c09060906080105090c070f12210e060a0f27020109050d080304080706020c100e0d020316140c030d12060f0815180a051b0409080a 68
    0x200343c010991b42d00c0d140a21001c2c04038aa4031070258051241d45414082da4a4600040c24000c410f500030300500030003900411894a40b00000c5074400c98100307455941d00d00503d07004005610203c0040d00c0c2c03045100ba00b651043e0022050001141846812401009503007144010350781a203026070803d41202c00440d00d090165004111210a910404500d0340c00c440caaa0030175081c0c40040c099400d030303002c5d10700040d960485e10000c081c180540d4284850301072501c038040144005007009000034800030713903c41400303210740c10b072440100c000d001d40b40c9030220540daa1015014051894040f801500c0c1031440c040e00000803214805e140d0345840301c41c0b4219849503946c013000320851030118003501c07038060156501030200091010131501e60080c0481c48141003001c4400c0c0b500850042141c5e00d60030f004015000882d4840503c80c541e9400d0740395203680359003038548641c40b01005c1c00c1c402c02220710100140030404050120000c08880010340ca940c0400041e69a106c0b0040c0141108001c0001550b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 344362104 1250 344360854 344360893
    0xf030311041710050a0621020102011407030905070801052202150c0313090603170304030207030803150418030c1415010f05040b0307150c0c050301050705030117030c 73
    0x18008114194101a514002110032003155180307842c0da9001406000300c64002d40c0b2403540c200205040400c0090b0401c010141c4500e5000c541c0b81c0341e696103801c05401c682c0300f50009220b00d903050000c2c202d02c2c1080d0b40c0c080c1c00351140c40821552270081c0c140c0030807070403814405d00303105064030400b960402c4e8060303004120a02c5c401a00340d0b0016412104004510054401007108080c1c9400550f80c074000071071200e03115001c031303008900741d181061010004100b40c18062010160411a29a40d80c2c940745020f81c40e148565000804c0090040100300c03580e50040e400a02600f0152001d10424403054030b05c0755101c001c03660007030108010407440030103d0f0082841a1030004004101c80c1d81c11040c1100300c04140e0241c0c40704c40c02200e009400e000505140c010340420131010b40007001014142420850a02d031191003034000c2003a0700c1007032002e00901440780b10003800d028000304114100b081d8020040d40c000d00442c0b851099040c0410003025001044506c0720a601d0b0280c8800a0940d02d4402c07503 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 344363354 1250 344362104 344362121
    0x10020706020705010c020f07090b0a061121041503060308040b0304080c1005070e06070c0605030901180602181c03050d0e0105071e18090903170708100b070f0303 71
    0xe107942442100b0020b8400d120380c00030100140c004144a40c0706401051508100c1c0d00040b11a40c200400481c0315203e150441d000da400b83e00389280c0b090307102c0941500d803545407100103071f0b101c14034010f0952010701c440060058403a41c2c8484080e4100100701034095071038502c402001c02204000070403030301c03448001442d00903101d150078a00d0554050f0703a107807500a42411012050741d480003030040d841d401c05000150b000c1c040da8074506000712904e0386414001c49104140900100100180d0303040c0e000c1d884413210112543d0080c3d100d045500b000b80c002d41244070391140c0048500c40b01d20007481c4c0103000401903141e4411101c2c943c3c0c1d0a036000c59454012042c05540c1c20b440d083c080d9602a001c0c015a886600715035100d00c0740b00da5816401c40e160940d0456082071015403200e0421160345840300a00f03030340b000301011444507024a8111081903c884081e01e5410142c010310a103d80e00011483c055915880416107103611100900824810100014058910b0505001c002400703034200d40c20 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 344364604 1250 344363354 344363363
    0xf0b030307020d05010e101505010e061c110c0f0105090106031e0303090206041706060423040203030f030f0a050606090108040b100509190e030c0705060705070b0a09170a05100207 79
    0x140c1808901b89186443c01c40d03d1200c95441e180e1043d41c00c40008145404001c0100746081600f420f00080820540d1043c00440031224902c04241c160703030561a080300c9030386100e604540c0d030754091010701d0315152410041c007160b040d42030001003000003030140140070680350401101c80d2100701e0358001c0340100c0700c0360504800b41138643c19901c025030344010145c002005004002c030740404138040e032039061082c01800140312b5482e12801c1842c43c4001900440314082c40682d03015984c40e2800080d04d11b020f01c1d45d01100d104000000c010f03514101a10203805018461414042512403400308103040c0203c85c0c0c500d000404075400a40483d80d04601d654210341006003d01001741c46502141002004550050078581521322040002c88144103812200b060400070303506161021f6081c80c0c89103554803c041c403071300020949400f445000d001883c01094104551a1b5900441c10080c100700b800348555140e085507107480c000b03140c030082000c2c12041d60000c090007000f4444940c1d10300a401951060301d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 344365854 1250 344364604 344364611
    0xa050c070b0406110c0907080c07030504030609050f070e0c070b151203131e0302090c0d0203090625090e0714030c180607120509010c02030a0c05040f0b030307020d0501 74
    0x748541140000d0020380300c01e40d02d50035404220fa112904c2d16803000181c0d03004e40200b80400101a034080a02a04072a01034a25a0707605180c0c181240c5030301881d0005003940345007441400030404002038000c00441c48500f070340c81c0b29960701c45800d60040112080c55104600b00300410005040341100c80e44244000ba10359442c400480200e4290300085c0364400c01527000007420711412003401c0c0d8030802010003180c0e161030004010300c0b9240446003440024040c00c401008901c036504100c3c162100303a03203165011034407494920b62035551554207807a89444c450261000ca140016041146100030805890740c0c682a460910006500b9000416403001c101c4454075500c3c4000c8541c00444c00303410f8980503903032105159074030f000d440c0d6840c00c6801c1c0b00307020401c03c003000201000c00c451740003e0641042d81e112030521006985021406500a5050185206080805c40305100003003d85c2c2c003c3d90704010182c8079038401401c0740d6487d4206541036105101d1a40186000c26200c0c00d541d00c16800070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 344367104 1250 344365854 344365859
    0x51206012708010509070501021b030a17070209010506160b06010905030a05010203010509070207030312050c09040504052103062b0b071d010306030201090e1e0702012f0a050c07 78
    0x74024604035045030001c42415081080b81190074010300e900a420305020705441c6251a0001c0e5440200d524005080c2c1c600d5a04003100d0380e03080c41589440da4100175908555200038000380c5450380300d444102d2003000d5200020900d030510100392902c0c20004001e281040405440d140d400394001040305041080c08070340412607803024812070030740c248a28009601c0394100010041000401440c1e40304660054070100086135001d00f0880349010f1882c0009115214001f2007241442080b403c80e800c14100002d0100f081400111180078483d03801840420381c0580f81e441e9060312065561a078080c0c0da0030120201a0306504070301059a8203003250584480c469a2a0280404202c540c030740820301050f01d00001c2e070141c0c510341a208200b40f03810851103046a00107420701d051809101504680035001a4600b10120119100000a01035068851800c036100034064000d1741c042115150034040042081032900040e5500001d514400e64104582d01c0002c03107c5170000d1003446124418042c00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 344368354 1250 344367104 344367137
    0x105070f05010603080f04030c05090402150a112b0914040f0e010f0501030314031b0705190507061101180305072102241303051818060a0b03010605120601 68
    0x6d1450f00200c130820f5481d07500d503040c042d2408103643e11040c050101d02d0100401a641d50108104c5031040c02001c903290b058800c811034102000f00928541e510540044424801c4203680100d040a5504280080e0203e0100b080b01c1091103441107500358480320800e01168a0f0903040350b13080c1c4000c01c000040206011420a0943c0c0302e030b0703003074000741380d55880140301341035000981c44e08420a00d10020716506100843c4000d01d841c2041ea1418550003285030010040117010310301b400d002054804560640030f082403610fa0309144a0017012031521005446003941c1030240076820120b41c03c0c2c20002e00c0c21901d080d207841d8040082100c00301c0c007103510005041d10364115080c0001e6654014254250f0b041d5905045a15030301c0c5600503040c00701c0c1080f15001341e20301360403021036040c54100d4554250f1030b44512081c0c030381c003501c1c0d42c001840005000c00010011030710380305070021194102d920382d462003501c10620080c0950000610100550405050865221031700705030185401581142405038 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 344369604 1250 344368354 344368357
    0x301110d0608060603060f150a0e07090801051014060a090806010e220506041103010e010c08040c12030215060609060301030b090d2f010b1c0606060e0105070f0501060308 75
    0x104003201540d110000c0c4180201002007070b90092054008041ea07081000d00e0301d00d403c0c0020b00e00f00d84c2c2a880c0780c5000003074440c03080f800020300c2c05c00403d00150900740c1d00600540c005010b40303901c940c40e0400282c820841089035404a40c0741000261079102080207102c1c00d9803180c0c1e28001408940400081d0645041005900070420505244441d0401412003a552682074a01c48402064840c2d240003080d008110300c0d400c1a44450f03041c1c1010441800300c0d003d00540380040d0541d5184c519400c255680100365103100c0e503c904030b2f8802d42170300c5164840141d241c0040c0500143e01c03000c0e02e4009a581c0c0305903103400207001060b0f9424140e2002c00903d10750302c26041260320b20300840500c000108204005c042c4036204c0d040510703400c44a9405c0103941c0300341d190a10b6514010b052190380c0a030080d4800614510082c0201c82c080c00c110132205094035240c8800c0310414078000000503101d00c612a4030b4161501691940e103030100c01c0c0c85048500b10003072800d407515503031503100000080d505d40 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 344370854 1250 344369604 344369617
    0x14011b0f0f2703120905042318100603050f060f0f130203100209120109030509010f120603081209070806010302210a06061401020601030b070503101502010204170c130b030111 77
    0xf074a51001c80718800c000d150b061700f0b62000c0e02581c20403060566803110403218829010083c0301d001480e9480007030f0f4801c0b00040440c0d162150007011000007000c000e13904084282e1340078404031740c5014200e0009543c1c0d8072084458504043c400350108007481d285102123a008155241484d003c00b0203900000d0404103c5102e10090541c0000c0f0403405060403d03010182e805080c000300202c1d200c0e0344003d0524441e2a1602b03040143e5002841200e42c000d03031108948088006040203000e44904c0c200c00baaa204c64110074114504100192880c1400500c031010b884c5007501804041e444c44c0d0912041c0c00c40082000003401c1d492003611284802006018a441c1c01158085035091600000d4045998900320050440d0880001880468548940190000d00c9407604950300d0340c0d0982c03819040c0d078158002550500c40982d410345c41c9a815000380007510005400c44a120031004145950360294100c0c140e0032280980c0e200d110f80e40154801c2001d400c1c040c001203800b62000120700f480d5800701 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 344372104 1250 344370854 344370863
    0x3041a0301050f04021c1503050105010e1b040609060f0915020a060b030304050a03020d08120906070e010c05060403030f020d0204060302120a020423030a14011b0f0f2703 75
    0x48010011443c054034040500502641d00311301d4581c0074203040e20a090701809200e5070340e40303401d1301c21095a401c4028000550f0803000800c0035585444c00466071210a4400356505c0354a0890b60191030055011071b000c4410544031003002e945840d805072440b00204486a060145400001138000c6608803c02c0c8050003990190104400d640361110840c0d00c4901c08500030390042c00b0502803030b1104c001c18019240c0446480a400d940d61400d90706501c107545401c2c10300100300003030241001001074424013031240ba0b1500401e6810392401151007131803070b00001d0041d03440140803d000c81d0180d40840c0010b04180b501500d442c01d500b0b401c40c03d0307a03c2980007800199001034a41d242c8150540e460b504610100c10943c039141c60040c03140d250282c041910100f0a034403000c0110f0b00d507001c21080066076402810b4098100000403180d0017827000054004101000300150b006a51003419600c00418082c0c4440941c02103c9c601107070401c1d0085c0c0c0441c01d000500003010380421458a03c4402144503 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 344373354 1250 344372104 344372107
    0x5040807182c0d02070609060302030619080a030e030109030c02040e162c0606030117070302150d0c0f0f0509011b0501090515042117040c0503010608150f04030203041a 74
    0x10022614680312641c5034400c210340000d801444040c0d401a240403c80d84035240162f10791311090006003101c80001200f003085610300d04000341e10a00803e906820368002e442d2602c420744598289801c1c1c400741301005000840300300003440103160680c00303032002170510b03022243e4481544404040303c02c00c507080b0b14140d10b82108910800c501c01e240502c0503018049080b200b900f00391010034450700040c0038101a41038140302460004d54200107500c005c1d6001801c1d02c541e01c00314400c00c02e1f154410451481481e0a00c5812015580604c8104030400003956a02103501118402200c842d00406103950410008445580490261000b6403000b80d0065000280d24042460540d01d48850110a0450180d0480c100004914070b09a00f440c80d40d61010b01d5924504114003c03a00322103803800310480101c0407402e0100340090460500213480701030b00200704264071a02d103030750385407040c0f400307019101c4a201c009203401e80d41c1c03c9996017040c4a4012207090940ba00c0682c04120b1000e2105072400a0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 344374604 1250 344373354 344373431
    0x5071803061a18070e03030c06070302090a0501021f050c09180601090608070e09180d02010c1d0a030f0303021b060421021522050304150504080718 65
    0x16510710080c88404211443c0402e884070b5481150b0080300180f00000740242100c2550070313500c0a00444040c04c0808094070329518086401600a40003e84ca480c020040d1001c04550b550001404542c02c0c04000001140d42c40446840805054010003121940f031040c000801980c0301c034151200c440441c003040000c180307061000100450543c1d84800304100c0880305009500d9008600000001d80a90302009a60364070207145103004440310565030a0312480408180d201c2d410340c84540380075501e03690540b40e43d07243c015800c680344035413150360303400a20b20b0401c20001d5440c040400e0110f200c2e040c0507050400710403404102d02c10249a1042942045c0200300800c420642104642e2180c40d881c000018188a0002c2d07581500c0844101e2000c1d100005ca8981401c0c11032510040d80389002c48001449a480c100d5240c0e00144074484819580d500c1250f5054001c00030b440c01c0c0c83c640030085c941d4910700340d40e44640d09800401d0140d11503880c083ca007008050f64900c9151940c0703410302908001e4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 344375854 1250 344374604 344374631
    0x90c04080102070f1b050603010902070804030c030b040506090303070e01120b090f0124081302040e030f0d050109090809091b0f04031401110d0e031611030607020c0904060507180306 80
    0x75112640c0d50032000b40d100900c101c2e47c40340c013502d0564040440068591041f4a0400c203144900d8101800c0c400c6813020000400540d469024429031240f01685c402d0b442d102c030740c03647e83c3c0025900d9130041417a1415140865214030750300250308003810008245101ca181c0414844032007030710303582d0f0100d80550050180340c000c2c080b030903402031309040049191142510010011076016110b09842710050200d48255500d07900400702204d00201500e546a2040380000c1256115807010088030381418000100e43c250351080c019643e8000760010b1800c0c41402c20000c02403401000f01036002c1c041400f0180800c0b8007405440c00c0c801c1640e12956417411030904120100035030269142d50380c10321a0b104a0255800d0586665501050380031030300802c914102c50544c02091400d42c5070100d18260a003d102d5201c0e04520000008d4050710303015214081e003282c031101c0d001c0ca01c030780090740c0602040000381c1c1903110036803100452800e0041d4680400c550960051a9841078808a84600c00014000c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 344377104 1250 344375854 344375873
    0xe19090506100c02060409090203030904050c031027020309031c0204031421030a0b030f010911010c120f0318050601090c0309021c02010c051c080f01080c090c04080102070f 76
    0x740c14074200701184a43da80e0000e0080d02c40c600034403128603150f54003c0300310745080080d00d03000ca030000d109204614207010440f03c2a0402c4512a030a00f4144900140b1641002d110852001040401c3c40c207028280b50741c280650b0001c0c000040c0c52204000c107003505211200c0e100f5a1500348540543d84a00c3c0d81400c0c43c101000180c900e4554200303011451210340e0300c2c45801d5181211140703c0703440b0743d1078408050062109000d400d0301030180107490000e4060651045014070b114100c01e0794444050401120307102d4203210010142400c00e2030343d40300c0d0390003101c0b080700b491001d15011850054995803a0307080d10b550b91017159194030a5005006040b50341c020140c0c249043e1800300440d00039500001e1040c0401d04c0300d004040103401c140001e5900c038845101c0156002170444103828281d245100402400e6240c40000031110760110720a803c4100115048030120700003401c1150020040080074040540200d080384410030000943c460280003620805008400d08070000d1140c1c00d142090 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 344378354 1250 344377104 344377129
    0x601090504020d0b070e15030c19050c0a0c0f1a070807110d03030903020c041b080c040b040b030a06062607022104050f0a0e0c0f07020a030b090c03070311010e19090506 74
    0x1071f0800b4002c00000142c00340a8449038104020002e809140e10031094419110340715282c04a401043c1140b400c0c8400d0600840444a40c400f154440998840361400507a007035044100720410100850004a40c01002606d078482c029200300c5103415805001655010101e6802c401090b180c010041c103040d018001e000e540c103411b0b202444000a0503084400c107800e580c42c00c006010b021720114034000391480640d009000701c00420784d5119215400c1103010f800888042d10303810b00b0300c0008955035110361641d00c20078200d10510f01020307400281c5804085c2004143c44114411701d03a014545205620410b0011911558a1a6910f040c503040c043c0340c490b03400e0458003030040b218040064501042c02c0c1e0b41d1000c48075040d591580d110120820f224401c01f03001a50185401c1c13804814004000c40550041103144121003d0018120030b150319040a0711000d4404000b5a80d03084c1c041d401480b2030344a854000f0709501281094141031a41b00742213030010000c00741e5074402c104450030003800301c990 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 344379604 1250 344378354 344378389
    0x10905041103150c0d0b030109033b090c120f09071a03040305160501020f1305011e0e120f0109140304030803060118090c02010b090105120601090504020d0b070e 71
    0x141c040c83c1400e03418088009440c040d0201030001e0040b00800c0954803804045600600902813940309060040c612080558244084e9210380002d500490000d03800031202c25500c100311a180c04410200440c4640c001c0005498100410400000c0000ca044161068404035101b160342e04102c02040d1070310b11142c01c00c2082c03c0d090403090b680c101d851015690b11580c9803074103e696282010055842c1050350788000d01640c00400c120409001c8000030b001000300b4400501c0a0396600c0d8011200c890040601404c102d96a805000d6242d11900c55540300b846c005d40404c1400125a0643c0d103051074003080c24032241d5450400e00c0c00c204078002c0140100c1e0340070001314141400c5440f0b000c814400504002c0c140480c6040080001112020043c000c0000000401c0711400d00f60019001c1c19000c803100e44a0141c071000420b40b4540003241d0307886901c0f420010440c42e820700303030940c004000140050380d00c00071091200000a04064401c2c0c0b02d81600d40d0350226611140043c4207248008400004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 344380854 1250 344379604 344379613
    0x8070609060e1009030203060106021c0912110a050607060b03060a02070804090c0c0f0819020706020705060d110703051909050d1209080d200d0c0308100905010905041103 75
    0x4a120790010b04094082c904540c50358682042c00c0c000d0b14000c0213a48025014001c3c0400026007940101f84200c60810300000b80040c442c48080031a0742c1c00c02400781440c148403840302038000c100b0720520005050800360103c1c8a590702d680c00034125400c180b0701164a070351108044442410180b000a0701704203200419400e000f2690356055107405203020b44060582e0704c1d42c80001052080c00304060036500200301801c00000c03405c0c400115404104000c010198446000d07800c98400200501141c4060b4080c20307646007000c007081a10b0b03001201d400c1d41e03151160554032450050000a24035148a620382c644e8610b0b03880e008041c8006248405400c0c0701d0100b00400c12600c40c4030703d0340c10701c59004140900c40b4402040035501610160450b0b00e441c07103960b202c03a0300300340c1250214451030741d4a0a0b582c00f001c460502c00780c4d1503109071000400142038481e0351000a0040d10f2441d0040d55984000c8195922030804504458090b481049110780302d40500003031004d80498044603d20917000342 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 344382104 1250 344380854 344380859
    0xa030e071a071e1101030506090105030d1404080f010b0306010614030c0901031515090e0412051b010203040b01142d0303210702010e0624010c081308070609 69
    0x3070811282018849040d400c0000d2090200710612050280c218200d034105078200f42c4604048019000e01480b4601003450030011410781d24100c2280c0341210b000400607d4143d003c0407080352841d20840c0c00160b030050512020450390001d1108512aa8981c400062120401000c03d403034451f041e4010424080342544a6030145c9402040700d9000e0001c90b03859030359a2895004034020018004520041d092103880850001c1c4100350104c06620682e03030346441d0700c1e110684055140000c0d40c0040070349484500e00030313247d802800545104410100d40d07461506048040ca420f90b48100da044801c9180c3c0e50040c03000c200c030482000900720f4181d41da003106200b10145000e0300b81d4050005500361f62420096205581c080003113880e12200841c1d400100c0c0b0000c661141440001d1315030601550820b280405a42e100003401d52041503a590800360008661501380c0007000301341400740c1045070052004020400120044c50005110b22402200c0c0d46400b11503030610580f80c220804010f101e1108 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 344383354 1250 344382104 344382119
    0x70b0c0106060c030207060f171e07110601121106070b2202011704080d0612150216030e0420180303030106020d030e010b03010608030703030f091509260a030e07 71
    0x751b0003681c22608100303441601102068034160642d1030101041d401c3d900c208403071002c1e40d4036803840c0490200d000400303e071101c25060756400d000c3d40025070154000001081845002c22214614601a603e000300100c0c0d000003040540d0702108003641e48a03604414000c0d400390000855424860403881c40070384404c5640001c045c0a85000c0030110101e051010600307003c01e500843c4c4003001060b50030404030b960341881d2400e4800405c0152141e0814041c40d42c8292018001c07103c03260f804c1c812000d1250403942e401d42c0d120848031510b5401640d5189402000340d2800740520312540c0340b4021948645002500d41c91030030882d00107034000e42081c4010440c481c0c00289143c601241070801003840c1407440702640c01401c2a41c0301d96032540c00c01c800010000c801000800c440b500035035040c003545583d100c1c1c00341550040c0c0e900802d50035000104641c03140c4c0035401581c51601c50094840300342d40400484081b12800b40b81c140b240000062004103154141c0306410009800c000601451031901d401c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 344384604 1250 344383354 344383363
    0x1008100812040b1803011b0e0604120336031401060608060f04020f04031109090102121801140414100e0a0303020f0409020a0507110603090607050c0708070b0c0106060c0302 76
    0x800d05840c4000c80c5130070303091a01011681060001500810507507046102d20b1a044d007400c01c00b1804207900e40502007036404c100303003268260303540007015101041007070761704654244001600003244d1148405c00d80c501c16030814080024180e50490403035090071410010034140f1203030b00000075a85819410400c00d500a0000c581c02501125141f6500c11014003140181c440d4144652009500140120030403034003800c1071140c09000d481d00b401d680c0d00d00040d42e0807881600550000c1c0c8603214001074041076a010266400346c4564004100d418400d46660800c50041d00c084a1000c1030391a0014103901c20000b28583d0642e0a00a20010411a01d020307240c40d003e00c03001d010145c00142d1805052036200466000300040d550456540c54612001441604101000c584070610600f0a011a02c0c204066034000c48450001c1c010700c0d100c01000769810790102100040900502130009224041800040004d20400c180f0f5036507502c1300c15442c2e0840707002c0d81100041c04034003104500030030360010703 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 344385854 1250 344384604 344384609
    0x702060c161e0b090d031b080309100b01110a0204050a020714150903281107060810050603043c03030905010506040c050708030705040e01151404140d060209100810081204 75
    0x1c001087c104c102001c001d00b90b10752180500070840020900000350700001e0460707144043d94404003c0c00e030b084801183d540f8290400000180c0c0000b0030540907107002d60080d0b403c04c400043c010714145969880711600c401e1b0719035503881a04103a0000440340e062102d00c9030304c110300201131441c1ca00c110003400b0014502294050b009911f0041541c1c1148c069107800004241030b5084031541a9213040080403148200ca15180c8841d000c400000e89007030a0095038080c692084106482c200c40f040342d203070750749210b40c2c0c0f01541e19048421000080c0e4004607030703081c0c54000e40d030105404009042003401c1d204068001070145141c005114611030307002042d80c9c1d6056110900c20f0342c984034100211a50b0003150400800081c0d4040000b45005d03071000707680c2181c0700c01d403107101d0210000680342c8018042c0d48144081c03d000320140050b02e00c0c01500c4421040c2c860100103080003290b40108680803c40000103001c0742d024401d00801515160f41c8000a00c1c01a009143c51345880c07220788420301452 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 344387104 1250 344385854 344385857
    0x5010c110a0303020d0e030c0607110d05190207031e0c050303070b1603090c060804050d020c060307050c011415150301080a02210a0803010620030702060c161e0b090d03 74
    0x17082601701749105812100c50290031008403515448042c20040d2645c00580307900010540070312807000d0f601c60200d0b05d0200340f01c941d101d081c20001d00032001010031041c0c5d0030800c1140103081001c0b0004d1406a400b000b5106c84c8494040d80288501d42510029102d82000303210794402d000040005040030101d40d4040126229107207a44218a4141c0140100100c02040b000d60502d0218030701d5800381016118600071011103120b0011000180c0c0c991103018007450b0007030350400000e03c0c0c0c18040c500401c1c244803214000034842051880a55003440103681420700b400c1c04142465003460311035042d0210034098620701d491540b4010440341e40b600c1c00d450080c001c1c0c4d42c250308051071142445850b00b1100c0010705461000c00c00386448440755100b40195000f09400307201c004a42040580001c0d580f200c184002c41c58180c01d07400b0400c1d0341c0c0042900214511540480f203444d840f031600c61100030004101004400541d0030503810300040c0541109a5100c0103110f090400e5856540c000c0509815 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 344388354 1250 344387104 344387107
    0x30a0f0206120103030c110904020d020f0d05011407110f071e1d07030c02160b18060406021513021e0a170703020a050d03050d0b04200705010c110a030302 68
    0x5032000c1030460040340d480100c01503500d0000014541c0044c00c5026141c81100d103180c1c0d0f50b00501c20004888800c0e0750107904180f401c28046c006041c00c242404081d000101903030018030b41036907402d082d20ba0720403400c05042c0004017807205190700300d4400201c40407148068002070360078055441e41c50b001c5200d160540034500301801c003860382070341c080c00141480c00400203203030343c450740030b45581c00c0291189000203250400401c0e800d4400705e40f141004c2503c90000e140e091420103500070507084414204803514030001e032030042c1c4c1d6a2000410080034240c000d0305c1900206007500e100b80e43c0050a040100c0309003941000140d4480804412451601d140e0840b1750601e240414801c02c25504000b046149145802401060001c0d110b41103a01c00c0302c0c1d00040e41d40b01e209221805442c1c40009010410620806505001e590000074801c00c000d4000076241403070240d000100e00309410307054480300c400203048092210a0140310a88219428250134a00c0030922080c0d40705e280071005010503a0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 344389604 1250 344388354 344388383
    0x60c16020114030a05071101020c0703030c11030a03120501140f040c0e10090512010e030f1e07142a13090602030103320a02040b0f040516020c0f030a 66
    0x90501038030559080102d80383c492510041281c0142010340369000811000707080100310324014001c45011000140140240514540d8180c1e92101010f03001c0f110b44407101504001a1401c01c203900760340d0701a580303c01050640340c0c9600c04440046e04803044100d101c5e011540399032921141d10a6600c010b80e00015113403803900048400e5000b14090540c041c40f00111400060342c82070900040d42c80899000b070050308181007480c00c0700c110003400d003034a40062203c15009003140000d032148050442421900300c0d00100f0041c45940070300300072100340c2c89000040030784000c10042603881c1032510302140d030314032a03a41038015401c0003003000e90700c50180015680ca0211450700903201c0e855202c44255125610780c80d207000d400e00d115100d01c0c0060713000e00e01490b001d0580b038054801c00c2e07a018050441091540c080c4400340070a0703800640c018440d11078032402074895204143c400e281824160301002d011101c024144410030f03440c644550040040101c2e035a0f808102e482c410b6910041d4138002c40c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 344390854 1250 344389604 344389607
    0x7031b0f0c050706050306032401090207021f020313080f1e0c0d111c08040504091e0b07030e160b0307180f05010201050c0304150c200a1202060c160201 67
    0x24001c1004046000b05080002d185802c180550b0040c01e04500340c501004000b0012803001e11031080800c070041c0c19400400011603680c0c0241525800508440b01942d8458019000c80814003440b8005a000180000c40010600c1d00c0c90042c0c081007002e8540da501000345141c5c1c1d81c040108039510b8002e5521480c1d0703888000c0005881c843c1010b42000d03000d100606040c40c41602d862486401020304c00d807180707040003401c2c01c02c40855901421141c141030402c403d00c4000c14040c901150401da40c0380905403c05a40000140d941e132040031621101e103002e400080c280c43c01a24410110381c04148448080d907007001d01c41e402e41c2e10942c0c00f541c0303c0c1d80b84042282d100020b1804018011003002c0d01144051600b50510243c1c1d1084e00240a02e0f100c11004509600c0102e80c081c03c00b0b00e0070341c1780b9502030301c1c1e503000761460911030300d0235807031501091159070820003410100e07040b03035030240603040c0030415580a0102d120240e400540f050340360075003048080f4491104da9512a1502c0300803003045a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 344392104 1250 344390854 344390867
    0x204050a0e0109030207230102070303050a031103040813080d0c03110703080c030417030304030e0d11150d0b040c08070c17040f0501021006082116050a020907031b0f 73
    0x6268000203203e40041410040d4480d041c0c2e00620345501d18000c804c0a10001030401441c0460f01a4010500c6070f1640e20200da1603089030090000300744d180c604038090250100061800707140501100e0ba5125518500d08411781c100341e10104a0380c00158100340c0c2181c000c0541d062860705410203440311020070013040e05120943c0c200502550011900c80700b05040000648161000145c6402c8001241c001c048e0b524001114000c00188650001a41a00308680b020f000d4500c201514400d9000c100700241400d40d00f01c4410440c000c010448210024850007004001c88007a6410001d20080c4280113046c828010141c1040c032219141c0c21081221310581e5401c00105100b1640c0c8589d2184480c0e184050f1920440e0300500c1800c042d03007400c0c1c0e4140710341c404480e280c0005100c00c440caa00c1061841100328503001d1100824081000e5005c0c070f40d031a420407588158094802c0354100d02c1000310f0944060103820425261150020302c1e54034903c4402c10140c80c0b420f181045020914089901 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 344393354 1250 344392104 344392121
    0xb0901230a1715070201060f030204021c1e0b010302040e0a0917070f030e0108060a0311060d020705010b012709020313050f0d090b071a04140a08070b0a0501080a0204050a 75
    0x100c0000b001e01d05110311011408000d04082c00070102d00030380300c0400c00c909841280c0102c0411a10a07041000145131990080c190701200c6c02852245071032034202e42003142d4602e008403090040d240048284403409205907041217100f42011030900342440c0c2e090a4040d0003d0141c056542d035524898103201e018114284c0c0040e0281403c0d50303494951408203040e60030544110007166503d40e10520660041c6903072440f030107010700740c0ca441c00c2c40c686a66036032030541a420754106004100e100a09080c03030000f0301855024000100e502441c00000602860b101c80030035101112043c0c0130380311020343c0b0703c078801181e03006440580c0365140c0042010300c1030049403006080703115072010700c50300003008a0010030b011055203492000c16907034440e4020502c02d055000f4103a5858107000001e160a10301c2032a0894000c0701981c0e00251880c010710725140c070261041e5151013020582d0401c00100e0f03540b0584c00b401e0f1a00c180a2949020720095851081c00c1000340305030b449a00103161940e041e4404030b413 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 344394604 1250 344393354 344393369
    0x412060e0102130f0509070804020310201314010c020d0b061903060b040c020c03250e010315060506070b040204091a0a0605040b040e0616020111030c04090b0901230a 73
    0x3c10356480c0701c0f0141d01e1420340300d0b0754000d002030000a22018000c040151260390080e0233403440101110b01c3d0401400c901c506204404494035084a8411208001d010541e1200075041c400e203040441c000c10920341035000504000e1150404001070301c0700703441034241903481340403c03100e500ca680009098810248a02e51b441108290010500065401c001d4a064069904021244191000b02d8660360614030f0250964088003914001810031070007024000076002001d541c01c2e4480c00c00200406080c1c3c0141c40031502c0c130004890180c601d1248100811040b55564601303940b80e074071001141401030000e44110364600c13810090040a5103d00b01d0010b024000c00450301d043c2400314010300890052134066442c100580d0350703178201445682100c10003a00205015516407914010504002c80280115500c80c61090060030000b1301a502449801e03d00300e4440e13040030030395001c446940300e1141c8502200c800400c0082c0040460003114005a40048051100880480c81d882180d40c0140d5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 344395854 1250 344394604 344394637
    0xf030304060605040c0c170703020f01050f09160320010e0406030c08100b06030103021507050d0e15030f0c0c15010308040e06120c130b180703050a020412060e0102 72
    0x300300003550740842c09a0308101d808118400250200b21000c208400000344007420640040204079000c00151140c01e12a10469200c00c046241aa00390350003134951442211903a401e00c00c54902c2030010020b450003141c1610000c910b1911203d80a486440c00710f00d00d02410201c1019992090b034011407448005001400300b15030300d00e00800f44000030701c140a098011003092070302d44031b440d0166030b84000004140508503401e54082110128101d0070f10b03c486141004403e0004005001e0700c00601c04030389070005102c820105010000d450300c0d06000005c0820030400916070380c0040707480c1d044030311030203001e031610441c03442c05180140c02c00b1510300d00c103600d400000400000e000100b06032034071090780741420f0b00e034107007445942c1d181d001c3c1020b8a134000740d6405916007411446084080c4000344045000421803000c900460b07000191000c2003c1024204aa060b405024058001e500590b0031071800780361618110f4180325140d40104117a8a910462041c403200f50140c40c008521a01c0c0305 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 344397104 1250 344395854 344395861
    0x61b140a0c0210080718060212090616050109211b05030c1e010c0e0a0e060a0911090f0f030d110a0816030201060501090605123c0609040c0b0a020f0303 67
    0x20b004c07000211012400110603a1040314008404d008140851f00301e0b8009001e00c4080104286642e04811f104d0b40c0c00090a1019503da0030400040b41c2d01c0b07502840002601000078102503090001e80010420b4010b20456680d020303d500ca0790441101d06407101645000311741e40380c800e003103118003510301200d8401c04a0b15210804201039440c036498a50000704171080e04010103444201c42550444d0340301249200070815007200c9002903501c071000a242c0e600aa49441189088070980020706049c0940031030320130700c2818000c41d5415900d00c101c8a5500c1c0703521520000e40e941c4a0450708030704028a540303100b51003100c10088018001d40c803982043e10385412032459510508186015001582031100c001400e5025205010036607407155101868031603001e094061900340640303030401c04203000d02c0c00940c141c51000c50314a00c0407041d000e08134031200007500d00d0303404202030312140c4261705c0c0f403052000041800c46030000311124145c0c15078803462185000e034201085a8205044c500000041 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 344398354 1250 344397104 344397107
    0x509060c10110a1e0503010e090102130b070209060f060a030f09080a020f0601121e0218010902090a08061509040f0c06020607030606020d0815040b0a030609061b140a0c0210 76
    0x3d407400d5029655241c2070504011004e82007074118140100203d5010001030004090404849a000d1100340003d458682c00e40654019005c0561040c00070a001080f0f401c1140f50415070143c100000300d9075410500480c400181007842502c1e00c5c4014541c0d0303220100030049007604003800c8582c01c0911035842d900800c0c0c019445003081220000385020310740022443c401410106003440740c00440b42401040c525140502c3e820842200340d030f01c5000461480114111800013602804c108800541c803031500c10309014040346103801038910303a04660104400e0084826941caa035043c00c44540030207850b9400d04c200120211003024003040d500801c085007641e000950329010711455039041201654801c8100c1e00c0c0d04240c40c1040004424070045448107815240808190b0340050000030764240c0c1100003000c9080d294411505075480342002d0092003041d2040e9a061050340c96191802000e0b003100a05114204000061455021548034005c6102d6400c0049130366028110721001d0180f00720 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 344399604 1250 344398354 344398357
    0x3070e060c060912070b0112030e0303030403090905010b0c0c0f0109080a0308010602120403050a02010e040f0608070305070b070812040c150e1201060b07030804050c030616020f010209010509060c1011 88
    0x403400c5044c4220300300901d406500c0070450311455048240b80d40c41c2d03400c00010080c6d01d03540300ca080c0d04004000b2000305599805100a40c0114440c1d03e8098000380fa00d4021002e0b154160306c0405034010605c919500500046411560014102c0e02268000b0b83ca100503114280300ba0400a914403c8a08020030141c200c080f0710b0517100d0540031030b0b40312014043c1441c1c0c60f02c101e00001f03060750003d00a10340154090b6403420300a2030020404180303180d00c1c2010318100c541c507511100d401c0c1e00569041060090504c070b000c001c0c21400090500d81074494480c0300903441000c0124015207a40d00000d2700f0300069415442c0032f001441c81c0200d11072605a40108000e81c1481c8d000d01c40d21030744251005600c1c05104400407a0346001c450341c2094160348041da40c0700b030300070710640b51741c082c4650100d5169000d01249116010b42c400d131401d0b2468842d0000d02c0c240140303002c19a04d0f031040101d1540e42c0c0c0c12109640303c3c580c0071a0340556410304070741e043d403c040503191307210300c0542401944581042140c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 344400854 1250 344399604 344399611
    0x60303020a050c1e010834230a0f0c05121809071b060603170705060a1e0902060c121e1903091a040317151503070e060c06 54
    0x883e12509000c0c810071400b143c4a004100c0e403078140c1c0e408030701c540d40a0001c10b41e1000c0c0540d800300000d603021740507144903110b0021801c01a00c548402440d002d4100034284075030341c0000a06c1070003030802102040948103a062903028442401000c41c1524411501200e8851344041540c401d650704900c0440c00360805802030840c040503101d01c1c140c42c18841082846251140e031010361201e40c060010060b456540b000741da0310340e214007010000c1003407100150b01e140ba4400c1d48959403180c600f415070802201902410446041c0060880c3d4070f415100e07441d01c03403101c00b0400030301643c0340c0c40083d40300c1c8100341341c01040c0c0c007802030003850740581a405400c400042c81c071002041e00c0e020411100070f100765417900c03103012102004003100e14404c0c1c0c04004440c1c8140005a0701c8a4891401c14611508482c100c3c0056603002007020200b45804605802c08100360940c408001d0087c0090f10510311002a0042e8680201c00140e0080c454280c149a0480c0076000343c0da1142130003072164590f103048 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 344402104 1250 344400854 344400863
    0x8040206070609061e0902220207022706180f0a0608251a07060203040f150504050d0309030c020915131d0304050a031101170702010c0e011107140a0306060303020a 72
    0x1c0d0080150041724007883d0016030f8000d00c80c1c603112070700c03940701c1c4400c6401160a1807003903420b01070000180c5402c08026691042295407001c20444260f001040d0480280101d0041c0300607410b0942030601945125002030502940581c030303a8030178040348000e00d8103510401c2644607005138400c801091a6596800c00c2e44180c0c02c540240d20b030b61110b076040380312001021b1124030800c442804180c080c0d0240d80c1007485a460300760150031603160309015220f02541092096691420300c01003040400480d071440e0914201406070040544000e40002c2c0c00c400060701400c032040008140881c1011100920781c801004840081a0a19400001c00366100b41c107400312800d06552060300070001c20fa0b400c4401c000c1c0011503089c00c3da55110b43c01e000c0c981109040c0b0165241c051005030f085102544140165800002c10219a100040032901086289814020902980010288086808010354610200c124081111800464000c00303113940b0190125280550200400d68017003468501035008 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 344403354 1250 344402104 344402141
    0xf0c110c060f0a030b040b030a0308070813020f011b20041104051c05030903011a030d1e1d030303040302011d19030c05030919050a060512070804020607060906 70
    0x24001480924414260380d103038080e409202c500d036828131a420060700c50078090f10102d0352010420119140941044080b00425030040411044a910010203a80b286450b0300c041d13450542a0003050240c0c0c050250f0b5030403c042c800c20700514034000c200d4040c2096105035910310600c0200c1e9041542200c0804079031060b818040d0b030002041100080d0780c20386600809810700840a6010507030160300c0320710116540d010511071009107035000e1294600784c0310030392884501e1880c16403c244c00d1030041032115041c04902079503070743d05a0b00420b0241c6240076606041d0b454010b404000f192150b1200070346640361000104010406a0640005044940c40042042011180086680c641e0a00000e0040a200043c4040042445241040503031401003007940c0c07030401c00d10041100c55a25903407000c91240042d104001d10305140204000038001881c180b8200766462098162100380689014100800c220204056594843c00c07a550140d04c08802c0268500f60b10f0110054154444541c3c1411316 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 344404604 1250 344403354 344403373
    0xc031808010b33031803031005010906080403020c13090c03110906090108030904050a0b120c0a050303070b010b0a0e2101060b040608040b07110d02010b0a050a080703060c030f0c11 79
    0x4856040105520f010b0f143c0000b035094020909025070401465003a00796090144060100804c0c00254091542260380402d101c0c10700e00050808407882d4014001c02554004003c0482e902060340300040c94110359030740c54841000e03e917001801d110a409083c0307540400e000402c0000e8100c012251000948000980d959030000300072004400b44902c1050742c0007004000740f18981075200c00e52202d042c15002600b8028503010400f650301d44558058107500c4580b25107503501e014110b40d0000c0c04101c005500d803241c1a591001540b00600c11240d0100300860b550312518001c0c10400440b03800070b002c4411400000b00100108084202d000500d5481c0040c08194516150200c40a135403607a00c41010540b110395441c0c0c01e1b200020301041c2000300b418840b90781d52606121000083c0c00e56070002c00c40101280c2007041e600d10b507512541c4549025181001190b9012a041040700c0e00404001101a0041400c1c1d000c0c000b00301ca84c46806141419010610382c1002c80d010003210802c0484001c00c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 344405854 1250 344404604 344404639
    0x100b0402161103030415260712020904060e04080301030b06040c080c0a030603080c160504052802090405040f0b061206060d0503040302090a021905090d030c031808010b 74
    0x204a4000d90000e01c01000d030031001c103881c4001c6208102c4060116460b056a4680131214100f6885030352000607500c4000307c0d80b441c080700f40c201604503104052900c6040900003d00407030100d140080140c1d03000310b0348821540d02d036800a401002000000341483c9001c1c54200156030090104075107465021003c94810f051031b100340f000030302d400c0d00c0741e5015464800c00200141c000301e02c0ea20401d501c681000c000501c2c40c1014110140c4840010b02c03c21300c299031003c400f0241900a0ba02462500c810041c1c0c02d0f1100142103650300520b881e13018900301245181c0c000c5c2c866000143d402c40d05120170b00c42000507460300d80040c607001d4684005103803144010810101800320b6100401da00c500003096007890704110b1220307941c0c031070402c40740f600e544c0340d002c02d89916080b11100803403903000c243c4d4980c8240c034a10381d50070f801607407801c0c501c2c01d085040000c02200b41d0200c043d080080e003d02079410580100f50020903001a202d0702240c81c4d07516401103010300081d5904602a0600012800c1b40c41c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 344407104 1250 344405854 344405857
    0x10f140604030303050405030c120c0d020f100c171504050105010e13020a0e0d12090506070503121b0c010e070617220206040e0f0105060a051603020c060c100b0402 72
    0x24000a00c020300e0075195440450140c28060b200391564002000080744c0ea0800b001102188000c405003103840b1904503480c0d5040c0445142086c0a43d0401c01e0342c9a8290f0020405003a41e0416200024540d800b00204030780581010307421446184002041c0300034803003882001e0742c0c0d03c0d00403a800e11060782c0301c0004480e002204a11907801074000324040d5200e54841d0003400c0c09a415191101c40c5000c0c4100040e4500b081c0340003500d50107a1451a402050b6011008201410056420307500d850000d55079580e80744520f9150260303500000303010544400c05240c800c04901402805181c84d4021140018020102c1e071a55090603c2689400505a03008131034902c0c810100e0300d24014035598080404420b80c540c440b04904000001c201c03d40140c0c1c40708081c101a02a5071091031407880c100d140b0700100501a08560711a0005005c4042e5042c0d02c031044a070210030716541211402801d1074160f2130000d9118001c1c0d0300c4403000c0b80403542c0d12310019490b803252404000030701143c0d5219061108a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 344408354 1250 344407104 344407139
    0xd120606030218010e130c0c0501060b070f082b0525021015120f0302010c050f0307030b031f14010909020102060c07030509090c0301090c021b19150206010f 69
    0x801c0c0101c04803c0390301901c6441c4140d000507103001e120703900046581003200c10440c040c00100c1c0d500324441d41444024800c0c040600300c075524140c80c0c1030550f01e868003100e1500500900800d0001032100c83e201c48548000b40207880080b0240c40c007448902e414014007421204a00100740410656a807221203c0b41400502c0700354000c0e201d00c0c0ca4800580002c0c220230f001842600098841c0055801070310103418951034002c0c1c000001900c0685402420340e00800f000300104202808044100c481210403690040d1080c00c0000c1c05490b03ca01090a00e064500c0c3d01c5200c1003692101106603402c0d81001801003c0e9140e562036583e2603510303035012640c59007000381c01a401030300007400018104004146250007070509070308001503200018403e60301182c0903141040080010003000d10940030701d800652060000d08800d0550b002c01002c1003504420700391155800c0400f251543c0031640c1100042c00d44c4034643c04541a44ca400699203510a20891044c0c1103200d90001c0c80c0003526100c03290 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 344409604 1250 344408354 344408377
    0xe010f0504120c0314070c08070602071d07020a05101a060c030d051b0a030903200d050307030f0906050106090f0602030f09060906070308190204060e120a050d1206060302 75
    0x604465204085580301d40c40c0f441101405003124407a410181c44d175000e0715040b0b1059052044c0326081c143d80b503040ca14107910603001e6500c4004244040601d00c500c030303d034000b800ca601184555580d4001c92038003040c540041c215001e141e424006070b0081da0030001680040d00c0030084c0c42c0030b104041c4001c92140282e50b2609410a010000e0f42320400c1d0809a0000035401513464842c4003920426099448000300380042070783c45694104064014003000ca0380410304610154541c0860b250030f803540414042941000800000509103a010794880d00f060161000200b10000e418039115008007403e0064002291400100113070004641c5400400c1d110a58061400d0808003000d0701000d40001c0c2150764064001d01c030749091030b15490301600645019540c2c3c90242d043c008071050365070014500f03145101d0300410040c042c15030800880074030090b041c2d81d100b2400b441405c1c000d08010105400034018005d800360358002980c4030f8080094102c20b83d00410089903208000c2c3c0803841501071006 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 344410854 1250 344409604 344409623
    0x16050f1f05040302150a020a03140c0d050603030f04080c130c0c031815020c12160e0406090206070b011719030503070201060f08161712070501020d0f0e010f0504 71
    0x200c80200580050390007500c00d00464405103a140408010001c0c00c03034007000440d90210710001580e0b0306000d800411103500c28806200c0c141007182402510850102c18142d5842d41e000c035206032000c2040310f140d8180b01c1a11601c49495094154980c00085d02e135621580c040c003448042d0030868802c2041c560001c1c0c50f4595101025642990280c035101c581c0f51071030004d00702c0001e103008150504217600c3c569034003901540500b103041220070414903c040704a0b500c06180c0c00002076410703a4850984660288100c1c00303a81c0d9142a001815076940020340040c0042034074402c01c05100e9066040c0d41a41400f0450407001010039a0740c0c0751050b00020300092031100050200c0d01401c02035400800750300c00070886580303c201c01982c26a140d40a80c81c1c0b94030403007981da090941e460700b8038060714800c01e030316048030001116540d07a604800d4480c440d01000094500c1001400d41c11510042c00d85a010300041040b000b58500030144c0540070b09a5509291401c0e81003425445030ba403042e5409601c14 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 344412104 1250 344410854 344410903
    0x5090c03072106030f212c0d020303040303180e0609040803060105070507060906120218040c1209050304090b040516140705120d0c080702030301270216050f 69
    0x18000b4100300d04010303803a990f0340e4400300115050085001a1038010366401052145c0314101c4185040d918440e5020806007943d54190075640d501002c004240d84c91007045e2040007800041c0816105400003035042c40000750010806402001f01d40701c0401140c1c0300d2580b250794100058007540116513403a400744d81c4030b00040009039014059a000070781894110300b440407a079202c524003200b94201801050049070208040755110b02a104000b01191081d400d1440c007002c6604003140c10041b00344100e44072844210480d10a820030211020410401c0c805110b15003810740c2c5907400f50041c0d000e0705041c0720945139a41402c1c002c0758028498024122038510710341508403182011540c40b0140b05900f0040040030031810455000c1c06402c0341c0c07402e41d03244030b0100288200d40c2240c82130b001b840404400c00c1000f503008001e0380e0442e51882e80c0e548041c2001c003101d8090340700f031140004441d44007242e14071401c444c0580034407401d0322401c211400450401c0b030355981c8103401180400030000f000c000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 344413354 1250 344412104 344412137
    0x110c1c0c2102100c080304060f0609020f070b070203070f030f0206061f0c030e10050316020705101101230a0b0301020f09040216050f0f1606050409021e04080705090c0307 75
    0x80003c22a900d16082d54031000a82c2c030701c222980140c3e411f541058807000d00c44449800c501c505001070550100861400e51099100350650080344005080881c40b10b0002c3c1849000b8022201100d500074520150384042d1f203800303015031200c146014010b109820014144c0c4c104881c28525145810400ca618440d003050b00b2038901544080880400024420544203501c5118500030b201840341c9526032a85010f200324000c5032101485c00e0115800b001c02040151114190181e5909952501c0c000300a081e050301c078050070801c12131040c401056801c442c1e81c41c4ca0104249c2c050429007109014242054007010f00340d0143d09107401a0f01410050b00081d0f00c0d00e07a008100d002d641814416040c3d62540354141420000c1c042c1c45100d4004807000a03c40400b484400b0411224815040006040c280c0c01405405a4001c9950050340003800b810301c281040003034184194075070003580d078075030b100c1e00c50703503203c046c1c510815016158850208110384844020340b40701303803819942c1c0489090070615 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 344414604 1250 344413354 344413369
    0x2060d092006091f091701060e0a0203100314010b06070f03020c012a030c05060a060509090105010e04030c08161412090d11010c1b03150b10110c1c0c2102 68
    0x40310805c3c4403555200050685410f40c80850744030022000240107842c02004690102000b05000e0000d0300c10401c00002c441c002c4a85001e03203030030500001030b40d248001600e0040039030590031030340301e4000320f00038007000032003100d9030740eaa0722035402d880c88000c848005503100183c507014005111440303034507200584000c880201615021b450302c43c1d0946080e0b200c42c6e0420205841c403044603600c035030741481a810b1518170203400c0070001008200750740c503040380c3c07a018000240c40182003103240340001d81405400d0040e1900303034040c0e01980180c12954070307001003c4041120032035442d00808400784caa07207023950165441310034050280700514259a0340c0108800b4142e6000b8180314207503081e040032481c000d40c40069035800c01d100c0c008160960402e107036108222542101d140e41441d91040703050311003007001c2c40c509095041540b40c0c1440e80306a50f052005140d40305070001031407114801c00c1d04d150300e124170070903000d01d006025481d21400070f54903140c072200d00d600300809548007800050403c1032 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 344415854 1250 344414604 344414659
    0x1150804051011071505150109030804030803060f06030711060c1611031f020309011d0c0f040b030d020102070c08012a05040b0f0a02060106052502060d09200609 71
    0x700844c0f0300380c041e980740c1404a600c00001c5005030364400410851101a4500d44c00c5450242070001c58649156101411441203002c010200240400417400c15102e00d0154040325000a1149442e0b180016004100d2000004003241d50b22a4102040407512540d044405100b2000301d04081071080743c4619004e4070007242e003903806119080c3c070341b292101c1400300b50002038070082d805070762411b00281a0742522440042291105414034182d03891a0001402d2400500159600500c207034440700010010b08245105030b81501640e03141d6003807107606500814415101e515003103a034603243c4080c0e6088603030b0b46010704111100380c0154140942c4054580e10150708600d4150b20b001d485030380c0050b09411140c000300d1320840104240200daa014080c15015200c1c2e4a084d03410f00206403002070b100500003000e494082c1201d1340c0724042d034036207500710342d140d540c0000144020754051071f0006904074401c645e80b04039030104403815483e00e1300900301c485998005000901d0491106910002d403980300 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 344417104 1250 344415854 344415881
    0x10b0901030e0c03072c0f07030f0b04150303080f0402090612190b07030e0d091e031a160906020d030b04181511041a160f05010203011508040510 64
    0x81c0742464041d9010081d9102403c2c1e4406e281c070344c1b07419500950301c80b840103c6070b100c85182c10b90200b10a2103a40000d042d4840c00c0c0346030100b10054440c04400080c50070045d19500a41407000710840000f5210700c01048034440e650b25106a075403400300341800035080c1c80003940300810030046032591518400c0028100c0d03602007940c4605c1c100718200703141d040c03100c03600700c50030150b000400c40e0054051040210000841e005411b8915101c84024050000360040340341d110f5900144c0c207514200d4541e010050b5074440f1120003c0c0180600340c1414090444403461421182c2d80c501d98079034400c2c400101251030382d40041501581304002940a080350b90110358005564020448440c00000c0c840325446019808006840c8051b201050949402001d21614410104800c001543e04615195020060700d50902d8440d8154404140d44420703080003d000080c52030005414041c040d40214126401400281420648200180d440300000ca8000e400d03908000d20690005919810440c0f11a024 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 344418354 1250 344417104 344417113
    0xc1009021e0613030507060e03010b010f0f0c050609010225051911030d1206050a050a09020309010212070504081b011d041d06060a05012c0406091a0414010b0901030e 73
    0x4035140358001044c0d030042d00c0c0307603118500803c511070300700c21030b031080040540086c82203000034030018008a8511151000308114554010422031160181c1580164000162040b0342016103619001c6d4001d00840e00d440513542c01c040300014000103128000e1a4440c02a000010528100c1e100b4000c80080544114458240011403642d082c00480c0f0b04501c0d5441b8049000740ca9000388003266a690456401440c2c101e8003449513688440c895000c9541c1070300e01503034941e500988039029000309407100d0101d0125006003c1016003100181050328800001c84851081c440c118080410420150a0104110300c05507204c1c0400b90100300d490340405007011454603400304408101034040d204404454114400788000c9190410180740100000d01e4151400c410340b50000c0c1d00040002000f44440c8000a1815529201d5400240041c210300d0002c010320800907905500303082941e00341c68440c03072801d950340e000303048800600ea058540300703640e10341000010380040d0024415043c082d00240b04 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 344419604 1250 344418354 344418367
    0x103121e11030706140403090f060203040b0f0d1103012d150c020a09060e0c03040302120a02012a02010b030f03041503063605151c05120c1009021e06 66
    0x70700c2c010b0030000b170103400c4194480d11b03040c01c00410a084641043c41d003600048000c05c91294000181e07416203841a20f1141d55296104a2518600c6101ea40f00803650400d52000c4030f89444801441c12030b141404076091080c1125602d20016902c142503900400701003c0600c841d100c3c411000400e1100c03410195070380480368001603008000c83e4024030700c4035180d11061001c00070103503169421124080307c483c1503082030b40d0044d4807404401030400800c000480c41c0c0c0c40f018800d4101c054540300008210050810040301284404418100c03003001d903088c49032110041c00c0c00601c0320020308104020351b04043c10613500700c0704440e070b20800d1800c064860001242104081590001015000d101802e0580c085204515031094a0b11941405d0307141800b0481800800300c02c6032003200e011242c01d00503403c90310700b111071440b00440c09000ea1154410b5001c04524000c0100240e000c4e1804941c40e00040306d007202c0540320349400c0290008a21203c28806070b40480240021640092a4505051 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 344420854 1250 344419604 344419613
    0x603030706050a1a010503100501140f0a0806010e0306090d11010f02031501030b1c0602030c0705010c0e0a120503041a04030f03050d11090d030c050319080103121e110307 75
    0x6600350f42200c0580e540310468144240000c802100c04642030130010309600d0725074620b0100e400d4a20400e0f041c0b05001200380248d00801d400c64070480501121940c90310b000100081c0b41c001c0841e4214040b0f03400d41080301140c03a0000c0c2080c03162030441c004160030085910704031914096180c0b0129030b5034844010024000c420700186108101e0305180f995030784000b200040544001c11030050244030701106207840700d8031342e4101c140825003040016a480d140e00314500814842d0090150081d488e140703244071140e40c04800700c83d80410413502010900e489100b11404800a9000100207034410401008426982e002c00e4148105044001d0b08203666a210382403070344010b041c00c50014000207000c0396220243d100741d8801d02640c002817070030041624081024202408409070a00403000e05510810000308100e0ba50305001c40d80e00c2c00284d007000e41c003a01d420400e02048070103411028441c040c4500c201311004140c02031002106101030b84880603100c0303841500d101441404200300d20404036 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 344422104 1250 344420854 344420861
    0x31b030209191d15010e090a060e07051815040612060b04090209090703030206070905060a1803060e030a08090a0c030b1306060b0903011506020706180806090d0807020a020102070e0603030706 84
    0x90308000074000034100f0302c0f030751424913505070040480d00c8400400d01110000c0000d0520342194000300004414142001e81850460a13034449640f0442915241d00d40c1c0fa0301d0000d0310300940b078501c9600c1c2031030744d100100b2098482500444405001d500700398800701d1103030f40103c441494094000038100500c0e030003184c82008100e4007002c8a60044000f04101941000442e6001d0800c0c503090006909010000e2502e2150150000420400702e584a40c00071420291200070362340440304101c4602d520b211152a600000464008190800c0c0007400010000c1280c0300e1031680902c1b414941380c11aa0f920b000900080e1801e44113102d901101381c0040d2241c880c88007e48420038021b900c42928008040c00e48048512107044c01c1814842040419000951482a260f0031b0410010401110400b51042141036106162500c80c3c0014070861040202d0b90301c50b61030b1595101c00590b680c1140607641ca8031200002401a03000c406d04014407100c081c0707280e80140c0000c00b81c85c9080340b030b6282d10082c0d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 344423354 1250 344422104 344422151
    0x2090f0406030b251e17040507060f08130b1806090109120507020a06081f240503011505070303090f0b16140d02160803010b04031b03020919 62
    0x2e0003103900c207102442c1c020303070b14a2404841510300d071940000b413090014545420744071000c14800f820581498268007841801a0084100d12050310700d14207801c042d580c0c5c038824424400802c0d818184200d0b070740d100e1170855104405c140d010030007000146e030741e500700f10354020000152034103008078041a03d40c0034005940038224072b1001080c44012403c0803488901440c6060b0300b4400f08009100050b11340c8014202141d03a1410300e000650380f0f100c030194102c055440d400152152841020420203012071485035118450031004000c07818040064035288020300400181008280c100c4058030b00c540001c1000714403030318000c200868250b880c1e9580e02c00750181294400c40100c100b12405000300f908541c107a10500c3c0c40079103940148030002075441407900b40010340e600015520340e2103070310340140da10850f4060703000c1c0c0e48c96940f4100409a40c01c2030000715545560004448194410210400e0960f500141491119240d0b45a01c0d8690211424404581d0b5212040300b9049810803c01419 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 344424460 1106 344423354 344423363
    0x1030c02071a041d040c0b0901031404050a0b0610170612070806090709060509070c0c0302150705010b0402030907030b1e010906030303290402090f040603 68
    0x2400315075007204120544802d03950302041508402003048440041510381004100a110030180c5401e440103404080b00c40ca0038454490700c04000e10150505040004192614107140191404100c405551315006103001009214003c81d000740d20480c00c9800ca901414041c002810703040341904502405074492000030b005480b203045041052000c00c040b20f4103140e40c2e960050b0b8885045074000f20314002c000000400603c18005d020654800030141169035990b2101140c0c881e0852400740e540f003500820020168640e212000010a0020801039890f54541002429907212040c1e0364041c910410420641c2c0202049407400e80f640b0550010094840d03182a07004082c2110b1204d008144420000070600c40703e6003c8000c69200392020f02290400c0c031701c0070101021030301030303141070758190442101070380343c01d9004090101d0020442404a01c1030008a421143d00303410459 = true := by decide +kernel

theorem cover : BRFrame.Cov 344244604 344424460 := by
  have h0 := BRFrame.cov_init 344244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 344244604 ≤ n) (h2 : n < 344424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
