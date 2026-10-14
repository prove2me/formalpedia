-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3684
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:22:51.966045+00:00
-- url     : https://prove2.me/submissions/f1d42b49-92aa-4ec5-895e-dd625ed4be0d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 662410071 ≤ n < 662589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 662411321 1250 662410071 662410081
    0x2030105190b060309340e011d040314070602090307171005040b18010f0f021903020f1213060c051b190311100204150f2d121406012303 60
    0xc000c0040500c1d080c25600041001c029a4051030038015007100c040c0c2448500188002c82c6106489d042e201241501401d9602e440da170000d013101c440d4039450701000c9000c5030317070001c211180d015603464070800340447d0f05482c2d440710340e400c226121889034102030203140b41f000e40d440d90303a000740d03403080342c0181c040702c110f456800c0c0680b80c0341c000e0304510403036540e980c08076000c00703002e80a41840c401d41d40c40e0268481449440a440f41625604030f4814907204200c41480040303402c040c0c486585810180c82074030340d52550101a80ba60f402e00013450a8074000c401c0c401c3c079400502408500080c68050446820703e0701603195200950782d40ca03081c1029003007042c000284203100440c0c4190744003003540c0982c2d903d0880340c8160380081d005540c00076600001906140e41c49100c071444440e01d454201e036232410100011007107640304039004540b4003114843c0050705000d14400c1c06c1d910301c040810403000000d1405250391070f40644405000500d8003031800c5179101000340c0312040d204000364440c03035500c070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 662412571 1250 662411321 662411353
    0x3060408120c04120c181802131104090e01050c030402010e0f030c0d0c18020f0703080703110705100b03030c0d0c020a0b030103140c01020d080a0b0a0302030105190b060309 76
    0x100408401d403102d4104400310381e0342c4014040342490362086000b07264050501e4819144a0f281003c402c1403d45498401407240d540000e030100310035011b456034507140140041807800352600e00000410184002070000d102061644400b8007400d481008000c42c0d02c804040d0f030441c1c0720980d4060300040408024400f94502803840400c42c070401001c8841003041c64000c1035060180384e9050b9101010080104808040f40018008243c0b041004501c0d02e1060160240503001d04c1a014003003010100001e5a194060313801800640710081c20191035102a1406981da40700700008a030700203080a010358040c0c06c000059030b480401e5240500004003034030000b2680400e10b01d0080e80d10000070f92002514184010080d40618081c440100c04030061403d081d1500302c19070310050440d4050400317400721035402441c3c143c100f0100c60021a81d8140440004c0890029400c083c0d415481c040501441c00c12942200c0307000d241c8400180b110010718000c000b01400304940d404500e0700959009480955 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 662413821 1250 662412571 662412607
    0x605030a050a06080d0302120a05060d170c1b031501050a050613090c050405030d0504080a03080a091a16090302031c0c05060405162c0a0617060601080603060408 71
    0x1030a41c0b40003e0103541e4405042ca40744d0784032041c50210f580000d00d450402040c8224952061042c07400b8446070801c840411a41a03804001400d01c800102c2e1a0003082040b50860f060501100d08440f81082c8501140907109400e02d1340520130311030440076500036203442040c0b6040710001440ca03004189004248070741c40c2d00065890501c0c95410b28081640c114500c00c428801d101c0742d840076107490505041c14a002d0640d0341901c240a810300c000c110302c4100180d00580d0701c0e4145402c10140d02c6000103d8040c00004034010300e8400d112642890b07080345802038900ca011200d85c0b043c0b00c42c0c882401500c0030451404040e4050300010002e0410034803401c031920700401c040c078054400b015151642d5003804410354040711280c0189800c148041c0240010303c1c080d005d840c595205130040068540c4050300d8510780e20062110301e100060501d1030950140b03001f0708101001c603041c08282c1c10303880e45031001110f2060214800346c011038942d040000e08180b1490313106500303c0c5808507045001d10341003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 662415071 1250 662413821 662413831
    0x100510080720070315050109110c0c0f04230702072c0717010e0a14160e0a080109110901080d0f0806061b010504030f020105060a0e060a0b040807030302010f060605030a05 75
    0x11043c0c6100100103110040780c55071910040000044550500b0001c80664150b094010040d100c1800b62038003155020428030074100046620740c165000c0315000c94040c042c0440030741c14900041070303801c2488001c804200c6c0300795000e80c269170780e0988880b60301c010030300c146c5079280c44801001c038200007156001009641000c0141005000c101e001c4030001c5201c4400d07009000300860300420710072100c101d03014a14401c7d0b12230560100d1846c5c40748c1c0803268040007000510030001d4600c035644940d103400742140090b000c4000244119001800c01d00d0981600c40c8002c0d0003001e021300000b501500c041a080c0a1840d1030740e40b4106000c45000848050401801850784400704004002e0380c0030400b02c0b041106549100040340d945481d00f8058200181010aa420340e410a02041295030350400c01c901900ca4011b0b4010050b10b03a4800b19444c03405503049421944c400203004a0070400c0020b45004881c40b036030080c0f01e03041c2002402c40076210144510320100e001403010a80580301da13000250305c4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 662416321 1250 662415071 662415073
    0x20d120c0e01050d200d0b04060b0904021803030c0a02120a0f03050a0306091506022109120c030d02011e021801080403030f050703020d0f0209030604030e06040e100510080720 77
    0x5d03c402e03080c005910164016a2401031000181e5140803482c5018003036040004840401c103481c03428070306d0011441481c2e180c034821032740054500708092541036042aa0000541241c2d258402170303420340d5032203c40c490140c0c030030b9010b0000c2d040d402000040c0140610350000303100180d80e24550b400e4480d60000c040d0002416250100425815058811a0a444883c4022550342c40c50600064206620300003107050700f00604601d031320000e80e164112080646c081d01c000b64040708501d4144c1c00c01c44d03980843c50741406403c81c01c04106905400c507452490408582e20404100f041d0443c08178413031850000c41e19142070329246250b60103828520b6120f4041e04010030011000340c544000c40e0000c89103000420350101d4001c03d100074030f10039100c1840d103240341107181400400000f84da80d0001000102004031190782c81105445030350a44008114010302d07035106080c4144600c07181f00c0103000f040c0c0107030900155140c1180c418042c0d580120020703100c090444110000e2141e989015100134176036 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 662417571 1250 662416321 662416331
    0xa020f120a080c01090b0a09030c03050d020f040801090b1e040209040f05031c0f06050d1217070305010510172a040803091c03021203150d03020d120c0e01050d 70
    0x1281109000b054543c000b035000140542c2c15291054a81601400c1c0381a420b01d8400d0070f0000a0300301c11401449034150410540b00e4504140c0a806441007800381d01c1c4005011070002a42c500542196408078070038031402e2203554941c41070002019201d460380c010016000085005801c040030741c990014013803980864134050325101c040c41c542c080c460441e0f86030b4081d80e03003c941810364840d04880030340704103080c82481d14040c001050074a19442c050600c1030000741c01d203130950081d0b43c0d81884c0d02c0700044941040c5031505000c1c0c0200000d01c6220301440304010840800784c8140343c44503116408010383c80c21901c40015075030aa0b4050041c440b00411141d0240487d03010103006440200407800086030f60381c0300e0200740300301c14840780143c4004c19201c102003070000c1d401107103034120609200300207600c03036481126100009801c030301803607040101c015074202496030106254805240d03030f4580c0c1c0c4079051152101c004580b003110b9a40001011074026815541c400d6000b410030710a12800441c1c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 662418821 1250 662417571 662417573
    0x10b1e0d02041214012d0b0303040515070b0a110403032f0109021507120807050d0f0f15030c12020a09060e01030224300109020309010e0a020f120a 65
    0x20400080b49010f4540384c050101d1411040b80034010000030040e109541e15900c40034100892034229929105012075850740000465a1410419a402407500400c1405215100c020041140d03200000a0b1030143c2d0740000280000401c0c00b6843c8091075a500d402c0c9840e181d42c500711403500c642064000c18600502840702010b00800c1d80e540440350800001640758818410031840b0903031a02c1046030f0600910004011484000254500f5892401c2040040da20b01c0c40817030b03940c450f800e445000300b40741c50503540c0c0e810125440201c400341c80110800201386180280c0c480c82d00b01d840010f103082c220700000e201040c0d44518041c1d00e81e10240114090340d45400c0d0780410350300150000100080b007040100158504405010149406401c1503040c911495050f040c4520031012100c1440b8034098403203607a0308200e11040040c008000d000c0380e40b9611410f009004e54420340f806502c2d03608180d4090303c0b40e1004036070382841070703401010940e0100105060080450707206107491170b0ba019151040d4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 662420071 1250 662418821 662418839
    0x30a08160c0305061806040c15090b0f19020f0c040c1808011b050310060e0a1710060f05010e090901060b03040503030a0606081915080a080909010b1e0d0204 69
    0x20001c1d41c810300c0a01254508064410b40c640d60305c800b01c03680d65002000380300104403884152420751304181d1140d05a9045c60074259240c69059200044803480000c00341c100d280c000c406000000d507846e8615800940041302284ea1f0f032988003170b00500d600044107003540b030b00e090703405446509030b141460394100b4072503180850f1000055000d5900b9944400726501e50030703001000d640c810203c0b41405400c6003445000007200c00164092142403204600c0c541400b40c0e00d5403070344002814015111013030648201c0c00d080c7c0300c6203048070062103141029800b140c25400ba0503150252001030b502c07201c8009a00342044149807004d010030110755624940401d025580200a41c400c50141c0d00039662400d008031660116801580b0841c1040388140c10301a0f100101c0c012650084181ca00224200d10280b08001c0000b007d039101940504c600e40c881d400b045840f201810540008660480450b0380e00d0503d1702c00d03403041b841c041c01e014070f045180610024450b40035101c940c100041c01800c1540341d0247c2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 662421321 1250 662420071 662420093
    0x9070503010e03180a0308040306110d05070f0906141e07080a08040b100b18120115090f05060d02010c0303180c090e0703030813020f15070b0114030a0816 68
    0x540c0390400101198901e2600d820310080413000d6500081580c50f58440c400e040c052400000d241c5a1101c400a041c0810101a500e90796181c0c081007003075007001032014045000c1d8021810205105040016005000700001d8150001c1c80c01150315000c445007000c0c080b10000100c07018601400d000399400f0840710801b030018000c140d1611041c60401e4207001002c0c49005004907212480d100c01130110013000f10903a1070020a10408001803c03054000a14040840075030842a40c600005180009042c0c80c000c4c040350400c000400c03400079a0310200081e40c004a9681343c001502c80c0e00080154810030a5900c01070180c80d001a81100c0090b4204400140050680c7c04007240c490501000350325100d40600900d4840007410050f18613540500b11030740c01440d008104a07030b0841001951622200100a40c000801d5000a8541d0402100341a040b4240646035000c070440082008152006031410003034006005000c1502182e403003a98a81c81800b1003c2c0102040301011300040c003010b00707 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 662422571 1250 662421321 662421341
    0x40b07050c0306010f080a060b010302120a050a0b010302090a060c080f0a0306051305040c17150a1d210d0209030a20030a0213020705010b030a05061005010f0203120907050301 77
    0x540740300541076040500e44030068000b110342d2400050200400c44000901d050840e42c130205c041403500040700142c000380030b1341d20341c64000b034121401c200022000d64001c034410802c1203020015039421030300440803806507a030003a4008150b040144421070068500d8983c46103e0080d40b4640983c0754040c90309a007010140101182c0c8884080c082450001443e1101100428081245251a4031103c40010983c0b040415001d01301400c2500c10b031702440b082c4284181030b002031300c190805043d6031000b006403110030001204854171081001c540030030001c0c91031900da40e40d007807011101111485154000c0c000e10410681c200140c40c0c0d161001e100140c101c0d80112000040f8a80700520b51090341090f000d01440b84d04443c10341d5005903100010464020b1407104d0041c0c032480e507032401c1c0707004011840300785600d072088803131100070060001403e6214500c5100d108c0049030340da80040d61301a865030180d1026030803c0c880c041c080980d0309801540300802d1005c83d000c456607070700803d00311600c00c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 662423821 1250 662422571 662422573
    0x91504090c0306140f19051009150302120610090e070905090a05061602100207050f01060f170106060507020f2e090b0301060c20060d0209031506030d030c05040b0705 73
    0x6207401e100100c840411780d20051a1070180a14a40012102c0782100800310303140d18035983e0341c0446d00488069200310050412850200031070070b1060020a80e0b803020740320407403280000c20142445c111010a20b1806203208141c1080128105080c130b001400200306114072500c21103400207907180d9130340039250003030441e58042c1ca00d03030307072541081810164000d14001740500754105012215500003038040c07038060207039030040c0c64034418501a17042a040240c00305d090340c00c0010100704200250264022682c1d42910010300380300320300440c1e00b61140c80c840d460200d4000d01c1400d0250500d04001c00191200030071a08181c0e1246030f00c1070802d14440d034402450790100103c607090710b070004105d201400700d01417220704540c9007100041c00c001d54540024030040c0310508140580000200c03064048034010442078460108690b141c00940190925034800d100700050110072041c0c00d65540e010742d80280140204241801d016406811445407a0341005400c10000400c00c0b5450041e00c00148184 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 662425071 1250 662423821 662423831
    0x1217090d080421030e062a0102040602100b060a080a0f1109030c030109150c0909020403082520180c0403020f0105041503050a02071b05011b02091504090c0306 70
    0x6992640b200c00c00003003240f42101e8480200110307821110030310740b05000f20f401507520910801c220540b1522190785044407140a90300031540d004c1034014105036030555088a50550040d05413000b9140401c0080d6007083d401c1000000b264850080c551f44600d0315180440c01440282d400000c407404200c1101c0c0100d0045003441c0c030384c60148000116001e08900902c800301d420341314a854140c4100100c1059545c4030745210032640980c680000410000303c2c00c5444607500e0070b0881c115448041446402442142000285000c001040741020b42080507140410441655420180e00e01074445034880450100d04c400004c0d038041441c402c2070f0780c0050b9501d543c91441484084090044064180038092001384002c04025440a6005005140100f80c0d51a01c0b51030700028403d072070001c0e056226101ca2425481c0c1494405400c481082ea030346044004a07004580c078142103214000d6011180d0004030781020401054040c070107800600010350540f06d40c1d9810341042e40c5d5481199015151 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 662426321 1250 662425071 662425079
    0x703060302090903070503030112020415060906030507050a1b021216030210050a08150f0d06050414070609061211030f010f05010503131e0b10140a1217090d0804 71
    0x102c01454000741c00c40c00641c1400200c1d1b550a80f6404140036000740304220800c48001c0d540e560f00000d100c4103050340e04014082d1580d0000f802e0311058010103011038107200100715034602c110211220503c1036580c4030b8080300704400d0f029507506115030a81e4043e62381c25501c01103560500491120185d0b448010200c1c03851841070200c0c5d5600e49810105002c002d10501027802d8100001d240d100d9408010070280c209010001101440941c0007650000d180c40d80c4842000342c203030700c9240241d000f040052014000c24588564552040c01030310000f682c441810030006014074074851040e00043c6000c622004218041c1e107890f0002ca8034040c1b070340b10000040221036403808009000d08000e20b459482c0d0315019020414005141000a04403d000c689c035101603018680b8510407952700c084055001d007442140c0240c00350b454000c42c60741503140780d40da180d60b280020048080701c1c6180c040c03804c50503a41d102e426031041101042101e0b00c03010000e00c0c827682e81d800c07164408948110343e180d8643c3e040c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 662427571 1250 662426321 662426329
    0x307030501022d0f0403030809070e07122f0a050c01020a0f1b020603130f1208070f230a05070611030f0a0e071a070203010e01050114090705030712140703060302 71
    0x1480c03c0c84030100070070414000e1124000049905507501f509110200341c40d0000d030341d854607200382d1120b43c1c001e030101c0900c000c503607102403207401041c4000e00900400a8010394990f0442d03038101c40880aa08050300c006c0300003252030141080c800141042c0c4d05010111110a007a0703400040d88500043e5420401c403015a04282405040350304210b925840000560100d02148000740000c030403418808003800402181600300030b281b9500c040b92001841922202900840702501d40501151403a00850052841f0b5582181e000800d04006002d00760502204000c0d03900200760b800400804000103808141c0c58002d0507500030008410300d03500e24005183d4010070300c0142c02503001c9401c0010010085500003541419034003d050708210380301101c2c05218461054460007500b41d42442803142031401c040d40810f0485960074081c40b5150302c45070401c184160100d0707890010175024030200d0000c0780300d0201c1d900e0ac2c490b801d0001500001010714180301c00002c0f1200340c0081d0b01c582d014002c6042c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 662428821 1250 662427571 662427637
    0x1206040201032f30010909060902130b0901060c0503090d030c170403230c09060a0f03140c0102030c030a08060d150b01230d0207060f0624090e07050702030703050102 73
    0x503240002070301083c62818130300c4100600c11070010680315010390042c0034055202040050b4010021a0300041d8403016074040c0c08c10702d40c024442c003501030002402e01e000300c0d21118115444409907140c55441420004029612901541001038060308900084c400c540980340e4034501841d4543c489145180075050143c00d40303002d121080c0e030201c00c01e040324800510110b00c00c6084030303e00d009549003004240c1c0722000e0350000b201110317170324400018840f501108000c040c001d20240e0f00d01103286c40040e40d99105075240003001d0b80c410000e180c9158400c0c02800c3d0403210040940e0310101c0113881d416841140300320070b0450140c0e18101d07a510303980c00500c4041001e0340d04050301d016440c003e1805005000b10030007134000d140c00041000401c000c6a00010000c1c1107100200040780c0c03982421a285800c01500c0262940e41c80b034811200c5001c0d101503c12038880c010200403e03610460115296085040c00f00d80610403e0030210002e5000e001500001004c4202e881041700400034810801c8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 662430071 1250 662428821 662428867
    0x605090703030504030209091203100807050604050603010509040305071217070206190b0a0302060406030c02070b070b01260105012405030903090103051e010e010303030b1206040201032f 82
    0x80d0010008000282e082410b58084a4040b50300003c01d64582030104c0c10421004040001d00e040041000006001040e1181c107031402e0b2422990440d407141c051005a20490140c980d0000c41480100668a0700c500e980c0c2d40300703200340742050400390f446d40c50380d00401038900b804000c20380070411010310055080c10700f580712030144010081ca050800d148504955026440701640d510341041303120f1031726080c18040046601030705007a5956669100140200190307803920f0014080c0c581c000031400d00705000d544181e50814206081030f403030b00d1103103000d0210301070071241041c00c034100181c80350900f8032846008164121a8a08c2c00c00044850780a01441d0181082880340910600840031000000d460352000f0a090008086d00c1d8450324030300c03210181803000e0121042e14008a455805c600e0719504991180d10188240107000041203900113100d1586070301584002c0014001d0340c4203812000180340c03460850102d043d035086556880c100450f558107440c0500154001403040c515120302c88803 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 662431321 1250 662430071 662430073
    0xa17070305070c060b0301091b170f0c063609010506070b04060902220e0d0c33020f120c04081b1908010504020a0e102706060c060509 59
    0x540b42c8824094011154443e000e004c00ba5a02c40c040c1e415182588003d0100d60011100c00c200071103410341005190050141d4040250510503040c201c060014071020203020040c05400d1464160003409450b4104000b051351004040210784040c040c540043c40b40c0c1c03c0740e180390403c1214210180000480c041e444030b4001c007410071203080404e00316580b4035003095000601090700e034494000640b0980d1407011500115200c10001f22049403140d21021010040d070043d9500f00203a0401550104a0740034060032081c1e4800ea000c0380e00c12580701c089160150034540c21509034818841c0001ca030045048200781500001d94011102d1a01080903446001440c200d482c0074240348c0041e03243c0141080341c408003a080549040c0c19540d11401c101299034404014900c50790310010b0700d010300001c2c0d805900403280e109001c02c0030302c80c400d842842564292541030100d842d060002c400e040a4401140190690320b03014544015240590002030a4954500b00300720b1303117030900300c1c100e40c0040d16107540313 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 662432571 1250 662431321 662431331
    0x5070c0608130807020f060a021e03030c0307080901060807090213123f09140d12050f04090c200a05070302040c030207060c11070e0621120a170703 65
    0x105040b00362041c030126884800c10b5120301181c4082060001c03280115544101e0209002c00080d500007502034a4883e02c83c1c10300521280d48840c0c1c0d803070388030544070038880f103a00300b0000311b1440c018031004c1d410005050002840341d9444100c44e00700613160708034001142e00020100c000340000c0059401410842003001d00c0900956030340c1d0100c101c03100341c03481c2c0710040c45010380e50340076030081c004044920600443c41c050310b00303080100076000900982500c0704000444e846141880300c003011344158040d407102504c2c6541300017602d054200b807041020401042102040c111028054014096016200e16580b820503510780f1041c1910120450010ba100c2c3c2034480c00300780c0014100303089079015503000a04041c0e01208401910903000003a1400742406d54142e1041d52105111400501c68401c3e120415213890400446060030303203116502c030648600201e00c00740d2a072450641c100701001100d00c1d00c22140c02520b110307000502c100700400e102d01d03015400c02c0c3c40000310952058403071804101c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 662433821 1250 662432571 662432581
    0x60a021b0f21250f061b1101141b040b0d1512050a03030b120307030c020f0f0d0b06010519020705010e040c0f030f02041a0306030d03090503070602070c1505070c0608 73
    0x101180307086902412000303003941c6010078003409060306800d4076000913061109201c800c04003c1941a11b0400500040c003800c1c08800ba454188106150b200c4100c0140e80a41c4801100400722241c156100d208404200030000f9515180e80003420103110707200c8045000c11010203481d1802140d03a011217407251075824401c001440214000d21542c0d0726040004102404202045030180d449161200512000520f481415004448554120b1080307885030043c00c42201841041800500350942100d41d11000d0b00000307400c01e441d251b11441c185440d50034043c071203000100c03080c044d150f50000361304248130500076035a2050220484403800d90781401214561940141044076801b005400c242d55544202c5400342d480e011100107100b6241504008003100c0005d035041d07402541c0c0c4621900c40d94800e040350034020701540240e170390400040c40c10a252074881d18065402500b04580a008140010034110138024400051140382d55589445400903e40701d89210f006803c040184943c95013049 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 662435071 1250 662433821 662433847
    0x6270306011202090c0d02090d0b0a060906050a0b0c1006030b07020f060103120804020f130c030b0f030319180e0a0c0305060a053a020a0611060a021b0f21 68
    0x145c2050701020003d544a5221b16500000c0c02014040f50b409074140e210b0074140b20240f218517002e020b21180c10800907507200300b00401c44146206031078100c41156010024414080040c007010700c0b5920075141214101e24091049503a5600101c1d6541066014010090b504209126200503540c008041950450712003001840380f00490744104070000b8001021502c0d21482242d543c440036008a10304030ba00c0b9040d102908265942200183c58480c0e42007031880c201505042c90003019029501c0e28841c0481a00000d040c0c40a003820700c9041549900c0e0201810040380080c103c50000c1d10442c1400030030f080986050180301d0b020582420280b0403555107200c2c1003c1264002c40e81462920000c07190080c208614030304a00c2c9010f1205025440c0b1241000c541c4d26442c402c5407158401521a03a00b07030360507850b42c00c404d50550711990020300550500c0d40144001d5040441803159401d804407924a4a03981c8d80000e10386810001035280307445400d58034148014299420a0b052a0481000ba = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 662436321 1250 662435071 662435089
    0x50901030b07090b2d090d0309080f1b210f10111809070c05010f02030901060e04030503040305070c05130b030d0905221b050405010806220b06270306011202 69
    0x41e0780d00340c400c00c000000010041c0407201b00e003002400c44c02c5041c2a6050203403511048e403003040c1c964010031400c440d045c1c201050501c0030b1a4028094048401210b040c0b0000005080031000000d550921590004000300004034598600c44014420602203c0086083d10070b070050507000381d01c0502400e42e09103441c034100710369007006841071217440e5111001111110384089c805001c42d4a04211031442c0700c0250019071003640b01c44c0c0241b0006545000300c01440360100c801400040085c0f0116002a1044001b01040da000d4440003000d0b640340c2001449403010450786440b42d0382d84a040d94030300d042c180b05d081200703400c0d41400d9000920f803e0204000c020400a65811086141d4501c00048401e40c8121380004e00100f1500c1c0700710b80d81002a207a5440f5000310b40c00304210b0707400141c1a04d04101042c00e00c400b00000900c0364071001d042e00001d000324082d8284d2040080c0684012902641c4115001640700040c000c45da00c03098062600340441a0060701041c580341400c200961510700d04 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 662437571 1250 662436321 662436367
    0xf0d020103051909050a0b10230411030901150e0610080a0e0105070c061103161805091302130501051f0903050303160f021c0302090a050901030b07090b 67
    0x1240554680d0030b1001c2c0001503c1c52207181501e0004000d05014000409100e010b10400c001402525810300d0240186940d22030381840d105401001e401d007060401e13081014400c06000460852103400e00320303c16070421280400260741d0b4095480e1640c1c00b0385c410f28010f100313404070071005041010201d500801d40651140c10701508401080341d41c1c43c0b5600015103287c0c01c074000c12030b500705134800030b00d18a145001a5006410421054004110041220f004100c450034a54030a84200000c1c1c075100b0240b545603241005907400099191141c0616902c0b5508408005242d030001d803040100d8481c0f000c0201c0487c0b4605001440079441e60800340000c59080030005400b10224001203400780e4494000500c10700000c42880301c04801c10180403420090750f207440c5000c03080b0f5003040f03980344051007070011005040907071044028041c2c0d00624004101920340c444030b5840f00c0104035114000e9004440e03012076003041003500c643c40741c4000c0103040c03158801c51030400107003410703240c218030410 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 662438821 1250 662437571 662437577
    0x105100303020c06090105160305040303262d070306090f0e0c0d050319031b03090201080609100801021c050906280209120a03030b1206220507030813050f0d0201 71
    0x65411175981c025000d403440a071409265030880131107460028403a400901c8102e002c01d0313825040078039612490400300402c1e10b0b400d5003817030780395500c5502c0d25803031241481030305510a09050070b0b494070803140c2c40188141c0c84e07070720b020543d10f03c1d00c840703001243c8001c141c0701c200c5031a14081c082401404a200c0100540440e42c42c42c4007165420101e007035203c0e44010bc400044031452545001d03405400c03e010700d000600080d60030000d45042030b0191051500001c0c002031901c0700042451901d0384200b034210400d81072010034591280c440d6030132a84401380001100349a140c610058071100e0248590045000025241c00d0134040c01e000a140003181030380745010342c2121483e000403030399810307101265801420700c5158008402003545903011583c040c3d0000707003000c40d540d03c01d0410f4100b03075800c2c0300407900402c10f5950342050b02003100c490300d03c0e001201c045254520007042c0e0812070034015500a030741c915a05d080d038000381c0d9480011a4015030040e2003a110360409550744013415100c940e0203003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 662440071 1250 662438821 662438827
    0x90e0709050703060509010f06230d050403020102042c09070e16020307020a06030b0a0503070b250819080a06030c03020d1b1203080a0e06041707060c08090105100303020c06 76
    0x500107402500c000c5d004a6000324204000140303c0c140e50103900308035025612600e06810005114110488d80c0c20b1350861040c02c00c21003551a5002c6511107a0300600070f100040c2010346403031917421440c40d2180c403220701c901003040070f86146051304212a0007800c0328008000403880c100600030005401030441c0058141000d030444403a0003401128103c41c4e008000088640c1c4404000d0300a001a4940034000d1b603444070040790724100040d4103425903110003140c50801a81180c3c11070202010706940240c010351200080000d5042409861891266007106c1c0d400c900b122001040d920004103203070740c141e05108041000c2035540041c6030176290151800130300c0c0a06c03030401c512080d17103028005001c8a2241400079010360b074941d0080c04141b00303a0750110076485a8031464140c07074001a0f5000e05130020710101d0000362280355a60f28482920621509200b0700d03485a03400c81c5d01e034804a00114100604200314a01d0030304c2500d90020600488040c40750854034003d680b0001104580d00a03c400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 662441321 1250 662440071 662440081
    0x301020c15040503040e13050c0a0302061804020912010c2a17090916030b01030501050f0f0d06050a3e0a0903020607050706020c0901150c1110020115090e070905 71
    0x1e1048170050f01100c0412040d40c240410b20464001c1c003060151518094502c18007028580780303000300c0860707030000d022a043c203880380c04c85171072981d00d02c0d02c561b8050341c01c0207504000d031111075002c0c0300007581c0c41c000950710300c8803500944041c4c1011606c240030100f500744002ca914000380100501c41c3c0004100c09048202100d07038041344036080b2410340c00010001040303102100c409610b8049040c1c5d0780d090007120345040c0150b05450080c00b5055029100c8480c0402c4c605241450f6140c0c2c090040c1b880600b420191520790444006035000fa54460700c0e14840344201c0e0b682c5264011148020390000458101c601d52000b00400d00b091101480d040080c108401c5485014024059500145015515562031074000d03030b501490710500300507001d0003800042d0f925250030201c0c126210746480500240403040111000403004a0441c1e1004100c58103d4141d01c0d448251124401190000a8181c600c0e03c520054561a40d011146081c24048041078800e00420302c1d00441e034030940081001c2d162 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 662442571 1250 662441321 662441323
    0x6090c0914010f090b03060130060912141225020106030c0b0c0d030905190b06040e0d020d2006160e01090303081302011101020c030a0e0301020c150405 67
    0x415441194000e0030201c6600d96841c85203210707070480714034615045000f9501c0941070300752170160041c664903400400040040d039150104181d8681c0a4090f02d030030b850700203180208108449401615020751302e00c06c9004105080c02c41544540e40d07420700c1200074061525041c054401c5200707441800d1880f101042030000c251010f017424400810003540242c08042d0700034000c0a2a10040d81c1e040c00380c090000300b404d454000c88100070070381d4000e0721100d02c0e5410b00350003601148104440e01c0c410707240c015135290844070035261851b1207105000644d0901100700f000782c3d821316000b070b170030341d0400c42e502c0c54556000075200001550368180440c0c100c0c0c07035100c510008103d002400045026444c10000003100803100d01e40040c80c0c1d41c840c00b1018080c24011600b42905000040c0414640004265604001d40c50310848500c145002105000611a85070a98120180308034295202046098040d9088404400501c4040e002141803011450f0900d035600d0038641081c0103404007002040c18018 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 662443821 1250 662442571 662442593
    0xc0f040603060c231611031c020a0303060e060102031b030c120712090605300f010e010e04022b0f08030618060f0d080f0a09060908010213050f01020f0a0606091b09030609 75
    0x2079100168121600c00f10806525991303801011000330b494402c01040c100c0c010945c003805041d06070b00540c140029503506501ca0700c3c030240741414a1105100e0b0100c40c010802203099162101203c40b030320303172200d40b4110741c0f4a03401614080c20b1210108040c01015480000d55042054000d0700000198580007001c0024100301c5602c05070315003440401c01c0741503901a0940c12103000c446102c107681e0307850319180c82c940001c3d1f030f00075440412071891b40b108180800000c2440c2c5142e03006032206d0b064690700e01040c0d03a410a8102d54002d00071041251038602120030080141c02c0c50b48401041ca00303c6c00049192184c0000c880c405c40d001949101031099050035101004040301d5501d55840684001030301064452084000103070451202161540040c025922030022007002d4003940ca08080401100d0644d0030f20046c11403080c0000344508071400c0111141e40d6000c0d840024401d8106940102600c0e14a6401d5030301c25505c4900b0120349503c548000201c0390080c07000a800d070740c18941011004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 662445071 1250 662443821 662443843
    0xa150203072a05010501090203010312090602120d0b0612010306060504090f0f0624211e1b0b12070201140f0604090609031d0102010506030c0f040603060c23161103 72
    0x2d840d017000032071220b0641d802907041c0c0b03020744070030102d28416210031140c403d158011100141c1104818203000500d0201074441259401f2011502500040105a07590000707070044c2e0a000c0380a0040040c00710b544a400054001a1020302503044551516050070710045401080c2c01c01c41c0c0c3c800c2c414041d00364000f0044030b000c0301040100b400d50342a481e00320413160044030071002524a0130400c512150f035106c007465600c0b04001940369501d02211b10100c0d5031001c15281c60310950585507a40441010b100050b00000300303819101c001d034062180da250b100070070540079a0b1500c034212660f504100081c0f070344280411074420300c0703546100128001d001900d4006041c0382c10902d40000300350304411040660000791160050170341d1034600490980d801a82e5594150b00680418040c60070403a100f119440d00252022038510350340d944140861b540d41c01c41400250b610108409804c40b8007400400340d43d0541941802c102e02560128034582105400800b41c0450032030310903580e1400d0121103418 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 662446321 1250 662445071 662445073
    0x11a1512010b07052a06070606051201020403030801140105040b0c070f03080903060604091203020a0e031005060901091b05070f02190f0b030c04030b0612060103050a150203072a05 79
    0x2542d4071a444903090304468421134913405402a55041c4403112601d07014030350f040030a4080b0100c658000e0261320742c089102950016240d89010450362900509001501001000181d03100d2075070178020301054040c2c1101c14403142200c800099603a2000c2540d0655503040c6815655503003003190039281c800607501c004c802c3c000041002040c4150309014200b044803c4d000e455040ea5404d04000c01c4550280700240080604102e045c1801c4c440d50142990684908001c01c203203507807034002880c264800a031a0300550302c0347c04010281c01c0c032407241e50044c10000e109221030464420750941400c1841d4446081000c041101010b00c01440b00d004a6103402030b150640c0c0c5040c0b811205d48006145c000c9425000a1800005502c01e0101c2120f12400000203600d00700341c21640c540036030840c080c1510750711625101c0d48110608042c08224021071054000b4a10510f0a20341310380d841420850320240b5a10600c10404040d80100b48079500c105c102441c106801c2d0704403600c1c41e030920501070151a03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 662447571 1250 662446321 662446357
    0x303030207060c020f07030303020c010902210c060a0507020103201206090c041208072103060603050601260612010f05091504020d030e0a0506220503011a15 69
    0x505425030300529915018007401d1055604810041e0f0381c2e0484680410700c1640000c100704080f9104c1d0b0b018107542c12100002243c1c820705500060b450810f9440810a40c80240510100f050310400402c02049002e40703001e828982d0654000e09203002d84180a41030649814141803607002a583c07601c041010a00d1180d00c4d402d0303200d40d81c2c2808000301d030030b18028aa20004110790621810595080352140d086442c40203034142d1320f01c5641d4011740e01c102c540d03006400d64920360b410072280398002c0a0303e5590001c3d02ca8506100101075980c042c08150500044091040030641d846c1c800900c2c45c01440140c01194543c0004901c01c0000201c80042c20352030008844581401500080c0c000d54540046850711942c0c1c08520b0030000c02500d000350700c45260410200000d00688125001c6507008025140480e544d00c042101984241a00f081e84d21060600d8884c01001115103005000b00368020840541900c400c00c1404000d28540c51007a2510307603c4201070561042111440b2006290780f000e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 662448821 1250 662447571 662447573
    0x303060302060705030307140f071719020313050108010e0604090f140c0a09060605030711190602030402091005130b1f0908061e0105130905010c0917070e0f1f03 71
    0xc0c40f46c0090765120f0024540100e45502581e012095845078084a41000d1030b044450307959600b496000011036074404024071005841c0109100702d0341002c81c00750061544c0304201c1d14015607032003541d0040c5040c0102e0f8401031124000001c1074640c01282600c0001d186da4041c2440490b80000d00c070010428040701c03e0040401c107010510840b50402a144d0465280d00c034601d541c03c2c1e8000d40581c900080043c00024101c41c0309044050000c0340900076036030b069426034180d5413204001030f000d80f18607130004140021820082103040d4004440745441031507605000008103c4400060035220aa456805009440c3d84100300800002c0b111640341011041c05200900030440b41c0c8070b005040d019403800665143d42044d0b045041440740d00c0c1c19440c6038205402c0006d42c22a49822a0b6441d0b070307403021900024801d01c0b40e03401504650302c4078129207140c12080d40c0c2c1e050f0080f50300091900701e401d04221817040e90603c0c1ea0071040303001c2608450381e43d40e00104403000216200001760300401f00004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 662450071 1250 662448821 662448823
    0x60e0d1401020910020a0b060121090803220b010b090406120b0708060307030b011809120309020a090c020a080c03070f030e04050f0114010309050c030a03030209100c02060f03040303060302060705 86
    0x80f00c043d034151030f1a800311004003026a126480503102900001a0000194507984507644603201d12500c1c1c010310500e803440003e0401214448002101d610000005020310101200c060580b90a0b100c2c0c4031109042055031205007a0300107208078461314034046107110040d070b0303aa0000c00c003070242c04810b0301c002e4900f800c2104044006644160228020f200421064280031400c0310070f0342d0b00411306604130f1b442d011400740b9808500e10300c4e03c25076503650400f030002212030b1769100a105040d50045800c510034010030003007150540c01510820f10b81000040ba5540220340c000c466900003005507203d10b44010850300350b2284c00802010100101400010590800c0101c03941513000e403010030440e661a02801045a006e0142044031881030b0520031482d8442c0c2c01a0550ba44500b05881810021b840464078100030381d0400c8001c80c0e00815007101c5810400e6540c0c0301e41485140007200402d0f07039000709500d40f0900d034400c0300201000000405050080d00074600466024092503540c0700c05041c11 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 662451321 1250 662450071 662450077
    0x110a060506090703060e010b0703020109060207051b19091107050726060f06040b010314010605040306053d0b16210f0e010e0303040e010806010e0709060e0d140102 72
    0x4288500660b1022840552182c403602050720780c002d030206020f03424001d1208094000300c50407011592103070703040c800146071400504100740c812801880c41610506095141d1201d00c10098007881c1d041100441d010882c44086080b03070440000000d208a0101c9490014441c0800180003445040c500061401003041d040d05190601410310b6601c1401803a0203480341019a511070170002e0300004248185080c2c0d100000000c014140000c410005101c4200105000d0340040003151002c2006c0081c40068007510b075001008410b0411113000550302000e120301e2986050a00880d1492040000e24044100b0405822010041a1030300a05288014045904c54044445040308400080401c540340305020000005488440382c5500001040310b4030340c0d4642619042041040380c00390300b5102480148054400300408801d07540c100903509227071403c107074000d4004804010070400520342c00000171042c0c51861a191208040d688002101102c1507a0082e000f1480200e1050b9101d0b015401 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 662452571 1250 662451321 662451331
    0x120702060a0902030c01081306050106031b0201020309060c1308070e100e06132c06181903080406060b030a060311010903031b0212120a2a1101110a0605 67
    0x22500386994507040003090703030089040203401d54400049111a0340c003c58004d80c0c0b1920695500e00345a080351903c50982c1e0081e4801c4010940c2d4265502d03601c07400000140304413240340025440c60030a1143d1554a14000704499008100800c01c84880d210804100004041c8141114005521658032445003d0141c81030098151122070000c1c18546141e140c0f40324080050120b102c02107112a01005080002c26910f6000c0101c1034420b10140300c0c40c007850034065040010001864114075001c54038152442d0011030398800264a0141408031003860001941880c20310300d01e0301d45240142c0541101c0d00080606a0017104204800e09139500c031400f201e02540c0c4000050528000566541c00b030b5010103000544650000c070041c510b01c44030300c1d00703051000d00901c2c00213203aa80c1203800c1c010100f0103001c4880300018008000c5500000800c0c941075051600030a914146450f4000d0019842c40107000e0038840b50340000c580c0c01030303204005051080d0152850349446182c480002c108c2112 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 662453821 1250 662452571 662452573
    0x230c030304080f2a041109030106090f061e060e0604051005030415021303030516080406090e0a0605010f0305060102120408010618110a111207110f01032a0c0503120702 74
    0x16640780030344100d90407030b802001010000c800004c00713100740409042c00610300d00f00f0742801c02c40560a0349091141d00010200e142c1d000882407070004c02c00060718503644c4041d5450b5500c640501038402c1ca2001c41c01100e4080c24242860b44207400440d9150180d503024a81c0070780480360310300099421000442c800c3e807081d9600808400c0300517030041240070700c0300010301030b0155010601c0020701400003804820300c0154041510202c641d40e8982985c095001a0005031600700c0030021017003121126600412000424041c5c1802e107400206020a00e84009003015160f00124415034020701145105a1240c2220342d6603588940b05030740a46540c1c420035925000c4115a0707882107140384142d07100000e446102900d850080b110403030340b40b80541c00c062214061008181140d0079400003c05134144548200c4941d40303e00d0080004164038514070340d042c5030902d0324107901c130b400e003510231411007446c0c01001141130010b0004859034a41c5400c002d000e8840000c102040c440940e10840c071455142c2c3c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 662455071 1250 662453821 662453833
    0x18030915230a1707270305120c0f0106030b060f0f090a0e1501050901090903050c07060f0e0303070f060c0e040212010e0105030307080f0901050d0c03060f0f03230c030304080f 77
    0x418908002c540480710075001032156002c25464419032220290210400e213400e243e11764503030b201c0604140403100d072428001030000d0540c2014000780008881054090020030140e403030364031606060000100b165104035030450545040e683c42c4042d41d5642c900141c0642440c1c074107000424000c014155140c030003072044103103100e412048000c0317250690300c018090f20010391070106e14a01505403d038048041c00418480030300c00170000c0008500800d069503c5044400c840c1001a010256442a4501030f420410900010031a0f518900c5407240c0c4c080c05c001105540300c0c00c00c4036181e29900d1880c0c2e0142c00040c0510b051405c8c00241e85c16503100c0007481c04036076641c10405940c2c1c451541d004005074020702031128144c0142001d005254018141136203000a884071540c11112202c1c25440841d5954000b40304407c52684020080c154050414680d241141c41d141924070a402210b4000d42d0b05590003280d480307081c0300a03c19540c005d0222a141c0f5181c0380e40300c1d12400c0842c242c001621580c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 662456321 1250 662455071 662455097
    0x5070813091b021f060503060f0a051005220e01090f060c050a0c060c1803031e08010f0e0a020d05010b041502030315040e07030b09070918030915230a 66
    0x1000440d900b01410b40042905024520345400b04400303003aa030250f441d40c0c645c4009000d8a092001d144551140f210741150b40c50640904000c032503001e0403003d40140d2418041c009607c0c0c1c422140b001455422038100d014800d80700300d1010784031000120b00e0b55401d01d9a84002c00508601c1c030510284610014046d844400004940a0094100603800a1144d040d10808a60198003065040590b482d01d140d220101c650000d01505443d402107000507060000c044001700c0950600500c84142c0c43c1109036945820403284000d4543c0c0074440340c010007103000c2108023116a040302c1003a04605d10911103503960710f0403011513030000d201d10100c0c10880d80242205920100860788105030002d48207454400c80410f12000703100f513040c0001203201d581404008a05000201c3c0d02c507066560003400501e040c0030b28041a10001c0030320304200e21590300d80f0030009400c400243c00b40c419204200315045e5200300101c40d0802c6e680b09070f030b22580610348007215144507480180015031140d03c1d060602000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 662457571 1250 662456321 662456351
    0x606090e10242c0621040b1503070612240308040302120102130905060607060504081b0a0237060306061b02030d141201092c0607030c0507081309 64
    0x142c10282c015440b0800181e010fa242030f101515450141800c0301180c0c0d05e1103c00301c41ea10030300307960540300316000e001040116402d4824100301c00c081030b400f0b020054582040581409400340b01010001c2d03e031a020201002011501c80f60003400140001a01d542ca04144900b540640026401150510181c0021a005000700c40742030700c00613110f01d180703440d10741c141004242c0076140c40d5202c4410044140410100d000781c9028500030552150b6902696448084803014202c0a80d0f007074100c0e03d411800b5030b807820002c000d000c0100c1c0038000915400b6064038186180c0c150254005c50900c00d012070303840c1c1e00d41d01002c2500d0590300c803070030004641131200c4c41c00e03e0980c400a50641c080441449098824000c20f80d03c4800980501d05000f03800c0036480c442d00003600000d002642c0c44440c030300c81c2400c00c0300c00504c0c40e46c4600300340080140c1706071040d21100c0050100c002d05803641c06980b0010311490031241c004e0341050f18030340c03908600b100c150f12941543c460813801e03900f051501650952 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 662458821 1250 662457571 662457617
    0x15050a06050c0d0302070c260c030c3f0d0216050f1002031c020d0b04050c04030b0c0909070e041a010f080402060403060908070311010606090e1024 65
    0x292001c01415000d01d07805044000e98441b410880f0b0781c1e183e6020009035036080b800000c0403059a82d113180010768079903e41604c0c1c180304144141c803d41c050041045540c9441d40c0c0c800c0e40c0c0032154581980524802040018002d580d040519440d1400c00000c40b02d4102240b02c000c2d8680b0f41c0d09403040403403240300c082440b030703081e008050344891810040b0815113842a05160b20a41034016030b410001c1000c81c1c121380c040d0a15a86003041c1d00007030901240c3c1128441c9408118007101c2c20400d60034543c0008200b03002d540002407414060602080e40035401d44162403036504020004082c9240c038110003841c10502c0503a4502642c10286005800034030b5004002015006a481d9081c0382030076003049a00b008080c100385e0b0410ba0802000c00864558015a00042c0c01a003ea0341d54102c43d2038001c0210060650ba86243c2c1d160640611480368454000011203070103c044e42c0a41e1035501411100f5040e80e401419071248440300e0760700c3e201c2d003c540500c80020302c0c2c4030741d40340305207100d80b00700340d44 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 662460071 1250 662458821 662458837
    0x6011e0b0a020f0106080c03151b0a0e090c0a020d08060325151115090a060506011e081905091c050d090312060503210306010c0615050a0605 62
    0x2940240840a010000341030080414811280d944100001d0b0300e084410b0b41c1c00101d8140c0001003080c900742400c0104003940c42404000740094a0032540e0014911070602c01a0201000061440001031261080203403900303008200c44034600309001202c0c00b13031b48240d04900143c0211000b9944031030007492254403954002d401340604841b0bc94462010012200e5285040344a5100210b02c1460180744150800019101c18040006038001107140c07020b0360102031007100315241040111800816014036699201d000031820b501ca07000180c0f18100e807004817130f10384901d404070401003a500c00b0001d8003031508410035900307032001e1000410641d001190f81035126484490205040381810012900714903840c40c11508001140754071000392010340800703400046501942c0880b414140c403076032004003002c4005041c04080c62a660780c02c02c01078941c1d59600031011002510341d0b4000d49000300c0803503100310200000100b0405130814041640201401070030980c0010650601480c2260106 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 662461321 1250 662460071 662460119
    0x5090f1017014112010e0304080f15040312051e0a1409010216171306050a080106110c010e120d09090b04050601080c16140f160b07140304031703090601 67
    0x43e4524030030300038030300c41820407071402d590780300302050b016801400500043c000b0780c0d000d480c60a8407160748c03034a0242c4401c11889180700502c1404006508207007101c0003550002804191741d903c0302812408110300d403240460010f200010840300119a40c0800074958a55900301001d45690b04440d080307010302a405c8160074a2100c0c1e4501044c101c5081c80c0170a082800c810703140408100078002064080d901c00004140041681c81c855a0004411805005607241201e046240503e40564581c81e691210b410710070413009510a0340c940702048480586070038111703440351a0b840c00040c000e060310b204200e00c1c01d10b000b0340720207980b4082c000da90040c44169204080f6440d506940d03143c0d944000c0c2100400c0b0111b950f10400106014900c860701c504103c043d10f404030140b0209803c01c88410f6200c1100c1040344014048416280251a50340790005a602c0c036600131106040d01d9840f407034001518224441c00c1d4000204180c0004522544408007603481d540da0311500244440300c01480c019030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 662462571 1250 662461321 662461439
    0x106030c050f03060607050a050703110f0d12021204080a031b12140c0a03270b030711070e0115200714030a0b011503060605090f101701 60
    0x480030250b00519000100140340c02d19100499980c54606104442c04840541004070200148200301040c840241c4059480c007c0303240406000490b81c0183d502d000341031074000c01c03584191501c00c210308207000920024541d030b219201c0601035030b1007482100440004001d4600080e8844600010030071003503110a0352052000710b4036060b00c0030000c0c460035840290042c4030340d54a084081041c120558003c2d110b03500054104071384c404001e4200b4030308806100201d00200300b000025411240e201442c2d01d4082a84521404401e007401c41e00d5110310341d0502d94500114840d400002c1221514015484512401b000401c1480800d10102e14000d030a420079842080326091841c0f1020303040e40010300760750080200f82d039400f080e50402c0e04080500c03268a91440d0400b5010300c0380c4c0c8050591401d200c1d080500c641e000892100d40f00042900494007d80c00d001d10302d003c1c50290701e1455400c42110310540e1202d034542c402a55500c5907030301c4240300e5910841007694103020403102c0c200b45108484 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 662463821 1250 662462571 662462587
    0xc09040b15010c0c090c05131e121104270b0a0b19030b040c120b16181205120301060806040b01030c02031225020102031008071809050c0d11090106030c05 68
    0x100818142e107006c02445004c1141c2413810703050401c0c0101400c1e1804a448403c040c0300d2105680308139507004900304e810941c01d6000800c61807110400c940800b2100481d8040040039107220400400c4041c0c5491180f0250b52010800b00d102790701c2c880c1c00b1106007000284524000c02c00c0e4041088004812071030708a200307001042440700c0c2164098000c0b401e5041c0e440e52031003021521548414269070141c410300c01d1140444078084541e00354001450040548400400003450800b0a0321510801c0e540001405007000740a22003208108030400340e4980725a136175070b0094209802180d60a20951620000040c20760213445104140130040d402141080c0e402014004800f401404802c820b031011841e2820381c0381100591354046503c0d90015840c0d0524100304072420032280c000b0045500310700000d00c41c0007241e9114020f12601d011000c1407850031810716904004540a00e240c004400c1c0f00d140003448020f001401d440b1070260b5211916a9940004504848200d20420002181080f07020 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 662465071 1250 662463821 662463839
    0x80c06070305030411040b060d050a0605040608070b0d110a02160803070c050607060f020c0d09141503070c020d0305030105010f031104060507020a0e250c080706020c0c09040b15010c0c 81
    0x1c0245d00041c1000840d0180480001d00f40e411407100030004035168020000c1302b010501885c801080140c0c1c2c140040c5090520f065150035082c00368040034100401e0000664a0980029800300b110f6101c81741c2e038804600c8001d440e072084000702002c2804600c0002048400041114501074201442002c50b900340000c00080742c1c46014159071142d01c500810348051101e100034800c5034120b4000342400000900003a01101c0544d00071a088184001d84004c943c4500d60903540344650820303460342d241d0350007070103944000c1540c10107500301c03441207040002c040d044001507050711003d8841021000300b4643c01c806881828003000342400061004114460045010b882154070040840310056107902500034050380440c2c0c00c0ca03030140b0a00c0041c3c0340610003a140032800015190159281c1000d44682c0c816209000c1c2c0140220760000da502d80c6814103100e010b4018200a1060481e4205802c0600031032030b00340c6031104100c003401103c180c00d43c05003031401c4c0d078560b00140424209207450410 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 662466321 1250 662465071 662465093
    0x60c020f1b01031109210106060309080a0e06040e09030a030f09110f010c0503030c040603062c060a03050604060b033706020913060608010b1213060b100306080c060703050304 77
    0x4c031503400740c244485074582c1d5a000d5101e02031070b032002c0700907944e0540810843c25550264002010b06251400103400b00e0000c0045402103c05030504004d62040c41c07011032443d109503401145240d009500744030410001200030007008000e40e60a00c1006e00c0200c4e400101d4241060080c2481e0204650315904c1c2032488501402c1441410241403085035522800c2c110780c022034041440200c00075081c001140c00d44640800f6000c403031700b0480724010008642200903002c1800414101941000841c260344050101014540c42400c2c1c0d00541054607008014240d00030800d0f00c83c1c06503100c50662011031a00d8031520780c00d0030f17103591001c2e074819000c120500003802c1c0a54030642c08102d140380644a40142868441c0c400c40000b40180c40d185008005501c1a04072078041d1000304030490030400080304042d000000c10000f20600c04031441c1140040150905454020301c0c0002c03100c03007642e05540040b003200c06400c1640e9804a00e102000740c113200700d40d001400704000340081008244002c480c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 662467571 1250 662466321 662466341
    0x110d0311090406080f0f0f1f0612080304260f030c0d050405071802042301031b0e1804030807050a020f070b18010207051c110409060c020f1b0103 64
    0x20318500701441c07011405944058000820640c0107500340381c1c1a40007080180000c01d520b2000d80054a0b20107584d030389403508400038240e815501c00d0000b1000659a2007a0f006000e00c21128004076000e1402c036200350800c4506a5402499070002d41401c1880a001c0d05152503405c40940b50400c142030700d100304d82000d03240a035000024040403100300840e2150500403070040d4000c05030a0325003c0038044c0841d0800b400d50702e00e40123000c204110080800e080640f5140c12404024404d0500d00480051031640d80d10804810720880c6403d04980200c0e00c0101000c1c00e48030250420340b03d5400c81182e10040d20020000b032000c4000480861046010304010312036481a40d03d4044050394061070002e10360090703008400700040348035080510b48004000c2500030b001406140e0b20b40320014003001450300945420021350002c0c00200542c18180d4210040020010442d032542c2e42040802044900a404058443c9008001e0705400004060700c5200c01071241440c034a00500c0110094010038103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 662468821 1250 662467571 662467601
    0x10050a14070c080715180b0a020f010f02090f040e1908120c0307080601081e090f071e120f1b05130504030e01090308031b090a0b120601110d03 63
    0x4240010b0000007038800100b800000810f1601e017850710380b82c01a0307106488501480400d0300c0040d04180c02c01d15400845100050716078488074250001c1c2c0c2001c449020000d2254a0005d04c0354545400fa0f020300500d00c4151010010001d8840c03d00048519000403a82580c1c040303007401e020752140f40080030b0114461a5454185100c056111030350b0748040d15190280c15000c4108540c00d54000190350b4040383c03d20b00080e541c01d03c8960b05030801300081d2201c812080300000541c02190070000309074000c00400456410654071414144030401c4a144000020107241001410022121008007050740104000440b15800d9a440540d1346001080f200b600e01492400605559000c074200440d5003102c0e40402c05290914009080d800c4600001c2e0601c4514507050020582c8202600d512900034a41c20b12441d194041085940c0264403000b5444400704002103880324050000d462103e80c904007043e02030701c40400643e40d80041040c00402a0301c0700300340e07443c1c140c80b0f90005c825504c0488 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 662470071 1250 662468821 662468827
    0x901021201151403040506011a070b06010807020c0a030b1009020f0d020c16030b0a0e07180b030c060a090e09010605010c06050a0609020f13050d02090412140a120b10050a14 76
    0x40065030f150b400c12942929142c110308010001c421030740085888164900e20007500d0110740b0b94600340001409040707241008241b100050606008001013817285100420b15900f040e683d00d0017a2007881c0440d000c03400c50a21501c00102c0c0d49090007500d2807a0244001c181c2003507240075610009410696025040d4445ca44440d03d0f03a0b0319600d000000b0b1070160041c91035a1502e400303c202901c03242c03001000c007540081e01c100400d2804180da45c040c0c81c50050041400641d0700e0000c2c1c9008150317110194070030800681c1406c42c60304000500704950344c080d2124010b640b0806043e00302c40e80391040e5800f1481c00c0007140001845680101e5010002620010f103440d1540307140400ca8000c2c405000031a10009021040104d5800c0003100402e01111900c40e10903242d804a40c10791300150004000c04000c000c0101024040c8007079400c001001c0540540356558010000c0c01c0d03e01223504149510b10705201c8420a04101442a103224540d0301ea523803400756040c008651b18200a9100100c0080034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 662471321 1250 662470071 662470097
    0xd0f02070e240a08030409110d020c16140102030301030b0903130f14030115050607020a1a0723060f0705090a09050105030111281101090f0b090102120115 68
    0x3108450040100000e010080b1502d424100c0c1d116010702e005510516509400300100c150000440381511030040c0c01042d00c030070b40034442009000d151241e44200e8000318154110000c00101565549902c0341c90880700e59850908105003601002101d0043c1c00800052001c01c00d2940e045401004c00d9040700d1510703041056240fa020780030741002ca605001220104008a00103078418401c5c90308800800004035810023003004004148105030040c4001b09a480543d40d0b8285a5002466050401c0c8003820244003a5822a44544000c5484014044446101904030101e00303d12600c807000910898942c851135011102001304600d08010041000c03041c40d44a030155240144460b45000ca0303d541420105402c1d01c00d612a03140303414000780300c8500766112016445018044000c1c40304900074041d20200e4400d038900c079500c405582010380101c10804240488841c6901828001c3c202e40c48440c0c07914280e100d0118400c0d40248204010f11040c2041d82d0581102d02c0a030500c50009086 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 662472571 1250 662471321 662471339
    0x10030c090221090708011d0a12050f0a0306080d26100503190b061c060e0312040f02010e0306061e21060906060f090406090f0602180f03030406020d0f0207 68
    0x104443c1491150040681044000002d0048622051420041d810f0160f01001c02d1503a400c21101c024183d62030004103d030764203020b013003102c0307840080e075a84641c3c0d5854141e0203005400300d0710403c4268070a442010760035500c2101021b0340c150304074a01d01c6034081007214030644a100540700d0301064002d00d0700001d00c1d076810401088003084c0e62100c0301200200e400d00c1904040000c0450b401230100c9201801c200b00713100c0c070000c14503501c418001703104c0d08040302c0c44e85035014030300c184094000c1c1c0c88180020b0142841c54080140e00c00d0fa070300c4410b501094241030325084151401c81c0c00401c0701360781003020001c034010b03d00c074064043d10301e083c03443e842e02c1c200540c1c2c080050030809a030419010b101c5590b40c24401e0303540c4200141d40c07060942c6152404510000c800078406090960303181075040400000101d00d01d01260030480075501d4403d80941480b0001040c6400e910503840d9002c01106800c0100950302100c515801400c40d48549210554184169001483c11270240030300124110b16 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 662473821 1250 662472571 662472637
    0x4052103030a091e030203091509030111090f03011512050a0b07110d0c080708180a080c19052110020a0314060409121409120102070b10030c0902 64
    0x1e59042c01184102c4a0304000c000544003240d0007210050410500700404c2c0c001084074105103080e0342c002a01442d05540b48514081c0d00324040c0d055003480c83d0222100710ba0f5010f444106003c44480301d2400082e01098200c0324041d50150079064813030b13020001030768510003001080d030042050300e070038918980da0141045030444501022511082e8890030015007000085079800e001d0500e503050000e16110103009000d10f071001046410002020703680c000d082805580720320700140224044513201c072100c98554044009090144040460100440c0d00c086207000c01c4940107008151291040000c2020b4842c160008500c6440307420a208102c00144c401081c4d00203980c0d500043c07990721206039840c00000941101d104e1820f1480d0140411809900151401344900b04000400d00000820400303002d9003882c2c2ea4031035800d5210040100e410740003031480070303c2541d000d201070703235462542d650896042c000501200312158042c80000c166500520703111405000e100000c0090010414560f5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 662475071 1250 662473821 662473831
    0xa0e010e0a0b1608070507021903050a0501050106030506010c0309050402030903070c032d0201021e1e061f0303090603020f13140405070e0102121b030f0c0d030b060405210303 77
    0x41d88000401072200200f00000c2400b05042c9008055401e000078024068000e40d6000384c482c1c001012060591204522258001c5030708c04195120040c041c00c0540c02030000340b00c3e0a01103810280017905641c812848080b0301036150311961651820807041c80001c0d00010031680d1030788001c0001001240169007440002c51080480900003c0520303261101181041c0301c500343d040095036943c00507038011518094000e603410401da1710024100f0000d03e41800421040026014200b0658002d90041000e078420300c02400c0f20101440709021820003800e4510020b000508040d405014543c400e40050007001d07240c00d6030b5410400e0700c00b5800b02000d11075000c1d20741894500c0340c4c12220304090207081c0c2c2c800040d01340203030552000e40020707484203554851040c220800050080400e1321003140c00c402e80c1400e1007180d843d85141d05600c83c05a10000f0b494506120361345c904c401141c46401004600b40e4060021403c041c40c2409009501c54403030080484803021812100d02031500308041d6101e0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 662476321 1250 662475071 662475083
    0x50a060501211107050a03090503070f270e030c16080d1107180606030f0b030304140d0510140f01140904030203190207050f19060806010c1406190c080a0e010e0a 71
    0x8a18002d0540b40723007540010f000390030440f000c01086010032802011154141510902101903402034415601e0040c01c9505083c60540190030844000020305048600f180460718803c122a07000d00c401400e030b1140ca01541c3c403464031501654880c00b03244080381030280072505a15204e500c8281c007081c104d06080703a0582e85440400505a2600402c00505070b0170104001160352500031a460340705a00440442c500b04884542d0291509040310311442d80180035101e5400341c50f07541c0d00c050710a400b04134441c001c118003c0340441002e6078045041720708296401d141d0700141c405012200c1c0000348180c01f940002c1c03000406d82c0554415031141c041090703024100c002c0c1030200b04005080004580760080d880e0444e0161240c13400068a81541c8050400040c20740d1250012185d11402a0f4000d124a4181d0074021100c4030015400d401040200301d00c0c650005c4a0b02c00408503103480041c400017801390303800b0a405d14400c2e03220710800804400041580d4901b65085407501403151011120 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 662477571 1250 662476321 662476333
    0x21b100f050f041a130602040806090f0d0c0605060d060c030605012006061e030a0b040b0612060402010f0203040b0c0618030906030103200a0602030c01050a06050121110705 76
    0x340002481041c0d40458004140c110030b003025101c10a210105104000d510030494011903000d0080d945012480759008405641e03c6441d1401c85840e920b040d109a092403095940c0034125403000f11f501510b84565030f981c400c02e00240d44860000e4038001d0720140e0841900c00c0038202107117060040388900300d2140c8010030690310300000180742c81000040e0140302910120031820381c00011410b40d0308120202c440c000c6843c010790b604000028071070f20055041c0300e11600d17901040f48403007110344942c1c000c001100703095840301c05101403d0380724917014004e034000c0340000300190300455070b920014100d441124203054640d109001e440d8044012060399611000400500c90710510410000c0c0e42d6480280d410107003681301268603808103000041440940c4c0b00042c0030070080006019505000401c0c580d0000d50703c901c00380d04d0342c2c041002c02005500b001c00194180d00d20b400740504456040c1e441c0c02c030a074044a042c0d405107010f00007580805844003001c200054685000d44451070090018081c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 662478821 1250 662477571 662477591
    0x50916050f0f03090f03130e1504291801090216062d02040b1b0c041404060e010905030405010f1e090e090c01020a0312020c060c040801060504061404021b10 69
    0x132402c0c17003032280d0b64001d620400c03108460340e0301c000c207010498400c407a604403251a003544507080d400f1800c01a0307820900d0319400c4200701d141a1040d403100080c1c46120000362100c031084c402d80d0f9405d55010b036003400350035004000660203540140640d90390500010034040d500da880e0400e40c0c1518200e130030000c0e00b05241158210303001a0201e0a03420f01c110442c505480c0c00c0f5441c619000c1d1080c10900402d440b00310000850f010700c482c1a0604c00184100010808501c407411003442c181c0c6c0944965103031070f07075031081d01c08148542c0214680010080d81070610b0100116407540941c00e01c0000c0001c2c18841d180d0455144050464100054890160450401c000c0d803940703040082c00040554040d00580140fa42c01080c504845505442d0410306480714203807140192045000e9003805200350020080c10b001000080e1054034041c0b0300900946079114108019500ca80c000c15818030b02c40301522000f860107030300038484482d210b201c910060782d54603440c2d400d03d0218400440c5454880000c10 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 662480071 1250 662478821 662478823
    0x760090609060f260a0e0307020f040c020a0506161d1f120f0e061e0712110313120e06030609040507051503040308220605040302010f0204080c040605010207050916050f0f0309 77
    0x202001c0386c0300110300b1b1000030303000280076100014482d40030b290b4070155080f50720310900805110325000001c56866082852040b2441d2070300807000c9001038184c9218210003410001d800040090081c000c81c0c43d070710001c00000034036584d01254000d03c03c00c02100d103801c0340c09000d000f95100011000064001c0d40312651814060000c120f0060000002251181d40c149100701d1a0044030a14141614407010b003410001002401655160740501000700f003003000c04803003010125031050a2072008900030b80c9058079900d50030100c0c5540084144001402d0381820024254440d000d8030171210b005550b0400302d1000441c011104a01c403078000b040105040d002541c040d009040811460140c00302c08240b01280c00c2c0510000703116549400215041c54400d4011610400310300504541e259030b039105c100e03554608480c0300c90059060800c0090a50300100c0e81008560003d0400b610076030f46c0800c0489440c003a87e0001d41408810f00c045203035028501c0280600c42081c0e1505a07590034040405 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 662481321 1250 662480071 662480081
    0x5060108061308040b03130804091d030a020d1d12030a140403020a0b03040c08160611011109060705030c0114180760090609060f260a 59
    0x26410340c5202d500910000d440e84040340c04440000c5440da4880d12074000348041c91881c45005056a000072601080d2421146d001c200d1080000c0b0403100c900c140100c01a840380200c8103d40d000d82c00503c400d0382c0c4a4010302c02002c04c000c0d891000e01c0c0d01c640c40c1b00003e00d030250443c50701c109540003041c100c18098008000070b58035409544500d090500d107034006003400080d8003031910043c9020020800308180998504090003c07002a40c2d460b4150500c0500c54901c20301c076440c0000c1c0c00c1c442d1039000e003030188102024101c00022807864100854140f09544e4001031044480344020000490039110a00c90410b01d543c1e90129240c941c00e00c400491010911100c138900903810950003040010200e01e0071005801e001412041181030b0440501200e041e440c100e4909200c0781682d040000207206641c1000b4160b0625000c522403c10004490702c003104d000c3e110100344407180c01e000250140c2c054070000c0442d07142501005000c19404244400500c2e9422041406001404500521030040d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 662482571 1250 662481321 662481331
    0x60f020d18210c030803090115050a050f121207060b10090303270e04020405160507150617010b030f1203011a0408060937170904090506010806 63
    0x480c458003a00d04070791481c901860300c60180104001032440c140340311849000500c440c0c21900501c0b00c3d66981c01c01c03480743d41c4204c5040149518020041c0c003444241030900081d50000b44c41e100e88113050070280503140d8842c2901c5a444001894103005411007080714004540d488803005403a460103162500036102051141803040094205010041794810810fa007100e405203071044010103c01c1075081d500e0100271400c200c4280702400400c00c51005a140d9028078403d032401c101564071031340c2d865281c01c02030104c0b4000946c10000100812030a00c9202130311100d84000203075084e50340982c003c4043c000000094a651207030070445061401f84130003003140544402402118402c038981c07442a1005016032110949030f0258007034691070f000d00f520044d1100104542e9541002c0c042980c0c2e80380108106209141c40d02e0070b070b058800f240c402045402520380f0344249000c1c0d55135101728800e0014070f4400344401c0140001e04203656240141c1500e20302420280002d035061184090800f50300901e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 662483821 1250 662482571 662482577
    0x19060c14070b07030b040209060d140f06010804030809010209092a130506071502070332030403030f0e1c020f0a02030c1c0602070602180904150c140301060f020d 71
    0x220100100e526005601d030f00c8445840d0010f040c4d814500050024014a40c50303942043c1c0201d0040d0404103541e100c00c0d1a20030240d6903174010350321027120501020707045944d1400100706c20301117000039001d07984407034000084000250500c4440d0012452400c0300303c504c603000781c07901d0742d16100c0e00101503410304038642845003003481c0002541c4841c201c40084d100e80e50007008001035003803d121905080e4040f0300e82c03c074405e658982c801e0070300811881411801c031380035400240030b04045c03140d00010346030841215500d4038103541d03640d20140c00401111034904812526446c000400340c80c203100e46c010000700c14540e0001140c0301300d8002d01e45007214010096a910201504000d0b2f80c0000302071000755400c0715010404038400440401c205030680000304000c1c004640c130000c0103600d401030b10505c1b14a40840600318004020028589810f03640a00341c510100000040b445080d0403071262031a00c1c0c00c10341454044803a0011440e80300362310420004140c0e58032214a16814440007004081c030307107 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 662485071 1250 662483821 662483827
    0xf020a030c26180a06020c0102090a0e060901090f0b0901030308071b21090b180f031515010509090903071217012913050405010f1406090319060c14 65
    0x18040c2184204058004072050f2580d0468807803e420400c041300405501c0002503484030307400c47c0050702030341240100c0c51188910440100d07064400c039400798070030304004011010b03591a1114440090a040c95110b01e0941c88540c108116141d504907d0b0007140310341d132030528502e00908001c1095040d02d19688111071031001000104000d500f9072003500c00c8448500c01c09050074842540e421146a210352403030540440e51a6190b0001d00400c86601400c0d07c0e0329092170302000c205604e40202550580b00d10b618040861184129512ba225000d07106040041ca424040710000d09507007030440c1d840301141d200140040400c03640700942c0c1f0761406141418280c400d000740311a140414140124010441c0a50540b407100d03019144606096034040c0025990701040403070382205000d140100c50103141030200000d9032100100401c01150340141d05070b0704032502401005401d901604c1507591611810b810300e000c41000803441400a4424400010b40400d2160081c04650150407854030f040414 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 662486321 1250 662485071 662485127
    0x507080a0f1109060c0f160923070e01031e150e010b0f0313020a030f03020705030d270509010b0304050c0102010b010f110a0c0b1e04060f120f020a030c 67
    0x100159410203000b01c814070380745e0240015191500e403007040b400c3c40340c0c440c080240e0942c4020704114421703101c3d00402030020400b003074401904d0100c000c0d042402c00d00201d0000f002c0612540103003803543c00503d800b00c0e802100c0f100000b0140c00020b200405ca5030b80e400440703aa00700f5020f071203004081c013505050703156251620b0005140215000d00c032002c2c4000000a06040007401c2100c2d506034014194010a9220f0811003040c4550780340403005032181060100f00c03480e001a1550b01c070031007036032900c500382520360500b01da0074001d00c00743d00f07a81d64800020070280c1c1d45424030340c0a4420906001d4903441c203820464034201e855040c85044da450300d0340d00303e074036648103240110541a508140e006800f011895a00c0d2085a42c4003034200b4641000c04140852401c0c006c00000091904c22210f49003446512265481203100b05800700d1850030092542500a500203030350030701400301c00101000d6440ca20b0060344c2c0040e1a85002079500c424404649402154140c03280602c804c0d100345240072 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 662487571 1250 662486321 662486351
    0x20f030f27010e0d05010608030f1801020c060417010605060d14010e0415090519080301060e03060606030a0510090f0b042307030b031f050105011103031e0c040302040507080a0f 78
    0x7584094020400d0004c107006002e0300750040d200400c0584d04481c0d946100300002440e0b504607003003a078032003100c00640102c40c4d880040e502c07100c0312000301000d04d401c0c9050403540e0240000c1c85030309119525100000340716030b19038001e41000030188801050b160181185d00d00c3c91603050304001d19070040300042c48003003094101d031400d081088401c0010300c2000b9003460b9107001c0f4208508010081031119a0b820043c86c4d10145040310140d89418865258110030951102c0701140c4080c0c02c06030500000700c480126410640e00400b045000f0032019031180070300b105980ca600302902c04180c54507407056250a103407044031991000300942a03865800010540072201c000f40c403c4003019110702d1100c081d40d4062102140e800d110700c44448081d070900944034090f0034240300d0703170b0702190044101464000003c0112445580c00364250180307903210842980c954800608100040383c0144004001038072148035507400396140351078203106d5103850b90301d14007544d00d0111500882420b0101c04d6024001f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 662488821 1250 662487571 662487587
    0x30304230307170c0613020f121506010c050607030e0705040615080a0b0a08070503011103070c0311070f170d03060515031806010e070f03020301060905010807020f030f2701 76
    0x1030700001008064101402c600d055001360b0106031800d01600302804641800280c8001e0310701d2083d60800700728404a0704101038190000d000000d150860401c021032159031000b1a944040141821304a0341880e84800d440c0590807910000441d079115075030891588100140c07002000c0c02c0380c050050034100a40c648400860000c000e0600c02c41387c0202e203080815401c010081d0308083c0c82801d625980750740040d600c08023071041900035417074010002d000700d004c0e00459201d546030762603500560881f950110350310860b48a04410380e028041c400b1451b0054064a4001000b6a00036000d12841a840182c14204c0341d0f10381c0d4082c903161400030011a100c0991102244041c21407180d241d550b201c6138103800700c0400520041501841001003818603000d9045809030180e0b0344e4451070410201002e4040744003c0c0540350100e181400c2c200b115600c41c040d031942c00071051040e564682c0343c0c84a0f5a295800002609030951404913200401240c1803489280e0001811000507090003c0300c00a00910 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 662490071 1250 662488821 662488823
    0x180201050304030905040c090f0e07090302090403030f0203040f021c0201080c09040f060b21010b0904050403021905010c1803110f0d0b01031a0a02030402010215060d0212030304230307 81
    0x104020002400f0705009644d0900100400b400030b00280304503c070004c003a81207078022071600402c1d11a011900a10040714203100342c445403518940e03d42140c08002d0300c81e0008000f20304040d00c0e00040051015640051402030f8406ca2400d40400103502c10400e081c02c031840403008828031050800003503a4803403d855002903080d804650f4480384e0b240802d02a1290000c40f085440c1070107000118400764800170410f5410510088004142043e03001c070310382c0b00c01c0c480d101070b580013806040307450301c1c01c0d03800070f034105201e0300441d05124440002d0b546910103d40094510340d5654099044e0103801084005120f101074520514050450f9030315515100c0b401c0c140c50042d007441d03501003072030345503100084005900007144640660b5079160000c180c50350307418000d00442d07590303000c154544064001d0300c0c080c84c0c0c141c01400e1070b0100445002403219005102c0c40d80a80005243c10250712442e4007203d0134440e840283d6901d11b01030401824021050410100c0018120000d6426a001000751003205d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 662491321 1250 662490071 662490077
    0x9021809070201200301030c05011d151b060403030b100207030f020a0f080d0f05121b0405100804050d0c0b0f06010210060b0c15010b0d0f0e0a0312050a180201 70
    0xd5126000101d00410024105824080503207007507445100c0c110020314101e0740300c0e10112420686030001103511400c030200081c06607498a00d02401850010080880044c907007041c60704010300d20303018491170701d881500b001894100d6000c0c80285545800b615090035405e0701c10320640c11032803600035541c0d140381c44054a00984042c1e181e00719514469070500820701d00560910082d1520740320f135102c103032124104c004a0342c00003400c2c81c094010400d86260b01d54017080c0300d40695500d02d1010b80103c01d0301e030652000300d04200108807541c0c4d10500a40d050340030f54401d01245443d00d40245003c400b4050501404011031990000400800c011075228541d0800385800d51244001030740381001290880d1801810118082241020b4070054425048800c1c102c0c0d0031203c05d01e1000702d03120800e009003400da0104100044402050f50002032071007030070a0000805007505406103080c64070101c0100d00003590034009070081d1000b03014480e0022118181040708484440803e00303086c1c100c00009040c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 662492571 1250 662491321 662491339
    0x803040206040302040e06010f12171c180b0f16050c0307060504032615040e19050c130608070e06042a140306060304110a090609020301030c090218 65
    0x441d01c0d4901503070b00440c2d02070002e225030340344141c20716140c03142409001840c1040310b1000a41a001e401d40c055051b8004910b040d03400200c1d10005003a0b40240d0380341d010994100c0c0340c450101c40c2da20601050f41c0d0b6081850840e182e25180150441801400c0341c88918013020901c008018816903030030f8004036600b466075854052081090450003180b5001e0b000e030346488108428960414880c0003451041410044c1e040b01100751055021400d44280407907401d0300302d6259603410b20340c2c004070304150508200c550400826400a030900c0d032002c400c0758030f41c004200a060a0078051036501e80c141d510705080c8009810180d0f00741da130703035034030310584170302e980c0c2200460000c0d00d966000002860340c0c840c07a559500061040c2c0039025100b0041070700001e10132070b01c12008031507003425070340501301c0181201d2950711030343c948494402080f00c001740e02041100b800240b00360300d80b194400030300e900d110140c0c41398514207206140e08403d0380a0034041b4010800220301d0420b10107561000074089400ca48 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 662493821 1250 662492571 662492573
    0xe012a0215010e04021f09090c0e090103061b091206020f09030615010f0203090d14011512021507120c06150303020109060b0d0308010314161401140301050d080304 72
    0x80340801c403441d6420007010718000400d21044000540784918000d13140541c1c00c030381401183d00304406480003003001076041501401944000d401101c1b180c03547c0c0ca004c507130440d900400900b07c03100c04c0c0d204842c0c440d510350700c44910050400511086a446080c07a03d259031524681c4040c002d03014000a10301a8001002400580c2100030f807a07c440020303003119454030344803200480382000b54179518045101516541d034903620000848801ca1001790902c00700c6407260303442c41078945144491040765501c07403d003525490780511602000b031801d1506004500d04ca401401038000026180340300c0c0f07060401015011521046034840360341c0c06858000201201401e02000070140c86040c400300310400400002410f0b8150001c0e403041d4028401041030380d4682d0104500744810300da000f1302190f6108010808101e410f1040681070101c00160781600308000b4200000c66a59003004841041c400d1140d5090350b40030400000703900d4013141d000c5c0b030355040c00005a108044035400801c96040000014 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 662495071 1250 662493821 662493823
    0x60614060315010c210201060509100b03040f080a0801060f05181210050c090a08030a0206010b0a090e0f0f090706120c021f0b031513020f120a050706030e012a02 71
    0x1542507a040304174842102030500042054074441500380d00158200b24012803140b8096100c24007402643d070759501440c4ca41400700c203550704020801d503443c15240d40f40ca004948070000500c044850b40c0d50303c4040351b040040140112445400311810044180000715200200d48181d106181c42150002030f2000e504800030300e0425030100b8100306508210911196450389006848111030486a03810000e44825110b60b89008004811005a0248004101c1034112800070310108480345803a03401a902c0d150107020903e0295015850040036500300002000700360b800540100441014050301441c0280003808540040d0001c0d1107590b0310096906014020800c6030032950016403003052144020100800600c000d010b01030190003880c0070b0166044a00211074400d204140040b0890348a0740c0900c19019a00828180c000c848003494a00f140401c0000e100603601c2140205541c90030618020240d0703201d13801e580c4a980c1000d010322200f07401e01c1c05146000241c92085100002505400c03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 662496321 1250 662495071 662495087
    0x8030703111309020c010b15180612010303210c2703141e0703120503041401020c010e0c0a030803010b131e05010f050f03060904030e1002010906061406031501 70
    0x228500c14000400003904104130380190802d10482c600800c841880d035018011051039559003e09581c00400c40343c0102d620548501159800103000d942c18440c0035400c20340c03070080c207030000e07008208606d10110808100c44d400b20040a117014003030041c0b2070040c4001e88100090540c250a8071035404101c0303800c0e0000440c840041d504030780c14802d4845200f005a40b110010551140c07030783c00d4860100c55586000840f00102e0f544400c0f181c0b41e80070840c500700c034039800c00740c400c80705043c07060a9000c00032402d0010b4000028410000503160726034a50042c500604801c1c103d018194900c0d040007c0741e000c03c00e0344e0466001c02002942c9000440101114000681002c001030011402c0c124543c00030040480035280c00780c86041040110650a40b020b000b00b04094070344840800003c0da190402035240c03600280710381410308440c62500d0000329818101510040140e54600070582484003900030007008041c0a81e0400e0009400701c00f151481c440201420303801151a28001426403142c408 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 662497571 1250 662496321 662496337
    0xa1d190b030a110a1d01090f0b0907020d200a02060f07050d050705010c0801050f2404060e0f060403050d23040303030911041b0c05011d060108060708040803070311 72
    0x20394052400520b0040f445094141c84203024600d42000461a4180d00c20812241007052412580d603038a00101d080152801210100c1c2e4203446494100d4144c88860301103000301c0d415009480c80c00148039008290b2851000303c1c040d03008c0c11018039041c0c14030210303010b5080c603016074003190346c1e5100070700030b182612810600810a2241038040e0110300e0340300e400f801400b03100e000240301c0c0070207508086030807080038001d9036400041c02440394100d1600103901940303032004c45d035440010b0300c5104100354240c1040d80b005002c5468412694002c1c5003009101c2e4018104039005402d01c0d06540720a0398031021029404180b02d00214909540855004071440310240c800380346540d16282c4c40d0040140c45a808112140548406880707071511b824016611f103044007803181c5c0b80310041720000300c1e08050488001d427000d56880d200460509030415a07010a07000d0a8002c060315458020001d20308040100080c0070040d09105010021341080304480d0000c0840c5804600310311070f000f42081c01e01c00d41c51 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 662498821 1250 662497571 662497573
    0x3309051c0f0506070809010c02060606160b0f16031e050c040305010903020a060615020a03050a09080a050d14030f0a0c030204051807090609050a0e090a1a0103020a1d190b03 76
    0x51440204040000e44a200c4c4003141e448144c2522a83c51041c00d80d40c0200e6114096009140020510700f4208050005108246c2041d201e0b02603d4855001840064030113404801468080100d02d8081c40d1003c0c00712461440c080120640c0f40700384041442c42d98a640d04641d80710000308800c8444202074401541d000f034001c02c0301000030b14000e90b40d1040c1c4981162404d003800e4001a1046411141807004452600070b01510080341d902103416034032680b00030701880489035000c50f41000800081e010a842231000b48100c11004101400886c016011003c0c40e070340400c10003910380340e104010764002c1c8094201055103015040240d010340680d81100d030300310003554590500389c010405054000c05075915460b05154548004603408841400b07801c1e007100e022902080000d00d150301050303214601070240c0b0845119540e5180d0f00c8800c2c400c0c051b001030031400050080d4900002d13040d005005a00d001c09103054110520080d854009010080c64012031310725402003209070b0415003102c20024 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 662500071 1250 662498821 662498843
    0x616050301171c020105010905010e01081e0712030e030115050a06120906090615080706050a0e04150825060f0503060a0e0a021c0e03120903070501063309051c 70
    0x40f4000707008100034840c0e4005d0904000001a1407038002003140d040e03414100140c240c8017654550b400010200148090013449401000030307544403090a80154644696107441140401d04101400c1d5294900182459000c1840070811543d4443c41d02c0122007075800c00111844111040700c004240e4040c014011506000b0314604008407540206030a44101c80120441500d9209541c1e132041d05025440205404200642d03681d03009400a1507100c900820204040c0a585000c020700410343e80511a65800318081e415450702c45110a4440d2000c2c04c107030707440c05103440340c0100b10320140044d01c418860000b010580b940c460300700c5440900901090400181400325001c80254420024010118004440d4280750b2040e4040d2041492195000710304001195401500d4024041d1000c051403004205620000e42e0a005000040c07503d0844507441c0c0110907003140701c8a00400c144001c5400e182102d24143d5040001102030719016584400c80c03000040c0f80c2c000c0302d0740f1803001a08003d038038 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 662501321 1250 662500071 662500123
    0xc060204031a061e0f130209042d0533030a050706090509060f060f04150e0a080c22020408100506012a020105070305190908061605030117 61
    0x448103007401680c0070ba5103c800707040f004e00e42e0303010301c41c3c018205503011180c40300117142c074900b00450700c164401c0094014a840b00d00c000280c01c0315940c8041ca2091950141540540c84900455910381501204180329910b4810702200c407030440f03042880140d1001c05c0c450b10b03005003814161000700801800300c40500056080840e07560446105502c0007691207440441d16041c001111405210050070040d80707031448000700509074100444c132540d421000e220014400c11066910b40049801c2d4550102421025041c0010745983d90000d600550207802c40072182e4030f41c0580441202540320715129801d54030b02540003e071140760301448484c418090300c0c02c2e0004460b40124010340c426210304600b002c4200294800d10464140079903030055440c04c12015500985c02000e04034800d150003071070492841d08120b03e20a1480505c030008046903011f10203100c040040c0e41d040800d40d94002c1c142561000f00810b24407050148698908180ea03420140f02c004102c8511250300e9440c84044d08155 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 662502571 1250 662501321 662501363
    0x515100e0f100e1e010f0608011401020a0503030a020c0105060405072133140a09050709030605090c090903090d1b080106032402040509060f0d0209090d020c09160c06020403 76
    0xc001d0340d803010504c44200005045103100303143d4045038000d481d204c00d103070301e04044038100c030569001460540c02602035100c0040c006000945c0b1030f10740c44500580340c0844901180c01c41d100188068010f40c5030405002e00c13107410042122140e41c0840e801c24030024242c0c0c4c810041d280342c49401507510007041254007080e04007000304582c0c4d0072034040d107039001e6610070740d64a03c0c611030741c41c0701d41120b0040380601086201d03030011680000641403010f100340d80c980d1910112401140d0031903c07504100204180f40c80c008400b1908441e0650040d400c0402c1107000420740f02c82040b005080301c0d41ea00d49022080500103005001f445800300800201c0e6403420020b214049040032070750945502c4415060b105c0036482614151100a400c541155031246c06021040c0c20318948642c0c07112000c0b1002c070060f514008080e114480d0076000d40300400b07090002900d0102100d441910039400a0b0401c00c2002064000e03001d00e44c0b80d4900b0318885103490230550020b2085030406003291071000551000e03854 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 662503821 1250 662502571 662502601
    0x110a020109020111060c03011a090a03060603051c20070806040c261525020c040b04020c0a0201030209150a0207031101180b0a050c01090515100e0f100e 67
    0x2c000c0e240d00550820a2501c161900c404880e88038000c0700c01d01c018030a0340300d48952400c20760b6043d0f89903440c0403c001e0005600c0b860340d5100716040394580b601401081800c5c0407111445105615040e260101c8020113007810040741c2a044000741040700107545030004000c44001440c42c0015940c0d50304050801d56502c01207801003256401c081101d44806450386c3d603042e084200c012000d0004403404142c424001c003809414407083c01e00d490001d0802455411545030903503250f40087c262a10000c062005841612070210b11491040c400c1d4001e48001084100c5520745c2442d0050780c0350200d0002400f02054484180440000032a420302c1050b00040c3d4441074901030304195038850b5203c0700468100744425000701020307101ca0410048400c4413805402c07049c90605045040141c0403480b1030845e214800b003074441e907000e1050b0144201c0359801c1950003614180300030821900b80005031304c103640041c05c3e250030055100000b407030300b014a000000c0641025018a491400e2102c03003184048 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 662505071 1250 662503821 662503823
    0xe0d0c17010b0306041e0f080a08040b07020714120a0f050a020102010501050f061b1c02060f01061103031f05060415030507030e0a021311130911090a030b0604110a020109 75
    0x141c604440302c4001e10300041c100b48655448207421460000b1002a01c05414903074008440c0500d0214258001608003000b80c11030440300d956200841c60642012403040c1405440701d02590031020050086005924480c1c04011040d50355600c0f00c16802086464807219840240c21004003809820401001241c10060325000b40d0003480113913200c10400c000c2c0100c0c4445580e010400f082030800c80c00c1c0480c219600048494243e800400751003040c03658811524035118010f070064810444542c0038000c0503409406285015007444005488030341c1d072480041c0540c003071003002c403c5c042b49050486811034050b04000d0002600c507650790312000a880d25140014006c64104000201124407078802e84a0704101000100302c103000c103800b4407100150345880808803e441c0d00740c2c88140302c4128001d0003008003180c200580700e45001c45040845103840701c01604000d04004c0424035541d03114016081d40e411a1562415440d5100003c0003443c00344280c1e00724040208082d251140c043d40004461 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 662506321 1250 662505071 662505073
    0xd050c06010b0307050403060f0615020312090c01020601060522030f0203100504240b1e012010230c09010306050303090d0602220e2508070e0d0c17 65
    0x240d0b01e4640a8903a030200300c2d403030000594203000800c08250300b40c0020404401510001031709039115230035082c450b0f0030030031008056800003c1c5035105408000b500d44e40002290040c00c41d0f01100070001b915070380f041c071442d4200000071845d0803042001d5107401c0c1031848000101c80003150380c0e15054808004010090340300b030140c0b0301042c043d041c0b1400f5062040d40e000c120340f200220a620344100103850301516201d0030b135540020481588580c0e203501c64903000c6064610b01c940310175000601c3e5600c403543d505807212000c81c0440340c03440002050002c0d403854090105400c190501c02c9071014466906410b07000c0c500e80c003400f025100c9180103240d1800c00380c1c1c06221940d2260180366a920810600d43e4014001003015804526a036028059400b0f900c1074107400284850358801841c07440d0341100341564800c100380300c43c2c004100068030400c61505108016100d1502e009841003100505e04418005412440c07005aa10383d503120f0016a07010000e05409910342403c242d900403010401005 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 662507571 1250 662506321 662506333
    0x30501060e06032809080301080a0507080d0c0f031b03030e060c0c07030813030c0311040b04180b040c0b0f090a05010201090b070e130504081309060825080d050c 71
    0x1c07424400100c0e8400e0046200e00c001c00c4501a03210b40e8200c42081c00c150115503115030f92800103c8250080d402443c480000f0001041281032450600039954800c0b091603100a4113014420380219180ca0055004980030700b84c80307003031304003035940e02e42814400d1400008890b1800c101034060340810800b90600341228465504d00f04210303014415051340c04500d500c14074007000000c54040003400701419080140e9011a540d6640d121410201c3d007040302c143c0d1540e00f00d403542d410030707204082044104a40500c010582c1e50b00d1071072800c1c441c40002d800403602c0c80000381405400040d00300204ac8036910b8503560380d4244541d4841b5004503040e244200c0e05140f000a0640c414003506034401d400074024141c81d25610b80540b80800d820110030382000d41601704410b40011846828401c5005200d030300ea90b5020031016040c0005150001100300f85040d0090200e0a000101c81c0300284d8410401160182019a210704903280769000150b00c1c8604a1038124182d44031002e80320b900190b10407160 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 662508821 1250 662507571 662507597
    0x9060f010503070f21140d08100302060304140c0306070f1101110f030403030f0501030f0209100608070f030912111b01050d0f0b030a060506030c0f130504020114070303050106 77
    0x40c507104240f04013507091030400c1d800d0101c0019585118001411000c0340e0b011a105680c403c00d0080e0100d40314509608801e080c0d44000d500420b1650340010381814511100d03081da800141540400342014000c03031080b114100e41000100003114841c400281112224a03000b900200042c0f4203e0b01000050b01180c00b85003070210500aa1168140c0c19040608060054191152070b80000f44203070101034a03441c0352001d109051113075902860195040520b10a842e006106a80001500711140c031040c41108000d20350b03000c1c1000b50042a030341f4001d60001c80c5000700320003a2840140140110165404200019410103c551020a8803405445140b2002c0d008c100c405c001172840300303000c00c03010031081c1e48419099019800501c1d81c9500080c51109900120f4580480010708036440395035a802d01c82d940c0340030000c8106c14036080342c07144192041c0a01281c860a008000441d1607921040481e085a01510803000305030141140c06442d80d81908001300500402c0c42480e0201c0c06000707043c6 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 662510071 1250 662508821 662508823
    0x180506070e010c020a03110d06050f10060c0b040809010302040b030c0d0e030c190c180e010f09080d2d020322030e0d1403040f09060806010e0a050601120509060f010503 74
    0x8074440c1d00101118980f86c55a280c83c40140311801c1340590003080c400346e10380098a54420140101180e044003030051805100700e100c0c0540c250030010a00c2010340030390f000210201d91a56115a0120a031505c030102030f001078001e4002c1d500203071156100402000741e001141f101034504500c50741400e0165511030500c881c5c0724811100100d9003600a0303d501c0c040002900600d074000c1f44206940a416a41d9000c2956001c03805003070904419100e00b184465a0002d01030615030404114040001000a640c3c0c0c0f41284a0039008504450700d400f03801c5d01901c6410210b0b241c1c402c903004550030212040203041c00070b41c070842c1c0e001400311050544070100d80d03070700d6991b0704000d91645808802c0201c070001c100c50b50b1042d000403614800c1c0d41075410508a03091000d4002020314100a8080031f09010500d0700391803191b003004505901050040150101052031203420919006002034181c6480340120346003203004011140e807909003000d200820740002420380c0b15110b200740741c0580d80d07241d900301 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 662511321 1250 662510071 662510087
    0xe0a05040203160804020102101404050c120c040b1503131b0302090f0907090c050c1516050703050d05041410090206032d011706090307150f180506070e01 68
    0x80c0040f00d00c1d040001442e40514a403640040c0140110f0344415141d030f07542001e0b907034000c0429002c62030703507803e20041260400c0300030317100e050440b00307551115100b8114541d00c40305080c41c035201c0ca417100001c2001ea1030341650f000c810840411019606c0c0307022090f258400c600000121120540c0c075001d80c446c0c201c0b802412060b03c2d0b001784041d006895018001c012240b010307149101c0f50017080c500152a40d003d105071850000f0548035151101d18034482039040c0708030b05200700158030341c900400c2803000c0044006a0251600d05000f5156a0749083c01c07a500d0080c142d4665400b482d1030240001d02c4150940e080142d007000d0100c4a52100c4055800180d07489400020b400c68800e1010842002c3c03002e003a2034283d5801074900c20210089254840069402e83c03006080c07025045d03001e40b1407102400a1a803080000f8021440c08816030b59201d01c2e0306a031101d030000d41d540e40518014810442c2c0011180c83d641000303a04440b0700c5401d05c1519880290342140116603403840920b902c2d4010995 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 662512571 1250 662511321 662511331
    0x305030a080c04051509063f04051207080d11130501020313141309080d240e180105070f0806101b0c0b0c06010306060501050708030420100e0a05040203 67
    0x300310f0340e62051605e9081c0c240c00c04402d1660010040c000c080f6000c2c4a448010700c4400d000000318841c0140402c503510005404400e1920711030500c0400001c500001120510001540f045650760602c83c1054001d82c0909184070b1a12410840414980c003100d0001d000200070406942541503519801687c0c3e0740304a40e107140080d40c00240400114213508940080307400b0107000c801e0b512300c0c043c02407000c950203003004407451603000c20b0a80b03805c00d852280c1348406010f2001503a107a002c0300b1809070000114400c507000c820124000034800507040801e043c03011546802031000e4204210040d06840465002400003500b2200140300c51131324071424041454662a03285207000c01c006000c004811740309080c2c1e00a420542c0000300700d80c0300b03002400c1010600d4050001541503241100507603001e0341c02141080340031b11846022401500c00c917034010780c0c82515944a1681510041c030f0b1041680b0266034480e00050002c4034461f0030a0528400340000c403184504907465804000481c041650 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 662513821 1250 662512571 662512579
    0xd0b0a09140f10080312010f0801060305060f1302120a0506071805060d0b06030711190b07200304060f02010f09050715050904090f02041d0d030908090a0305030a080c0405 75
    0xc0451010781c42c5150250300000803a0000b10101c1d02e45414038556845110a00354055030400100440e580000583c1c0240141d40000d00001e8655158150340c1c8c1009444441c00c0c0b488600440c200d291b038455015030399980900210810051065020303240c0c00703059010781d00307402102e0008000a101c1c2c54054085c02d002409414000d0401051060395001080002401d607a129041903541c0d07620030155205404540e98602d81c80359581585d81840c001400d0510a046803800c80e40c00110045c215a40c0f003915880e085082181d22810078200400c1001d024909020009000c80c030507500140c10300070702c0000c0d0002c1c002c9080180c005400c4230719281014200e034201c800c041c030070501034081c4507809016524156060a04c00c10005044550f2a002110394820b455410800c600301070090484a0303813095180b4400c40f0112180c03907114014007114001701907581c0c02010070000342c90300781c0d0400c29000d410700ca0f0550301c0340313081350f0740ba031040c0c25540103c1c2c450000030300030580100845003585d40182c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 662515071 1250 662513821 662513861
    0x14040201090b130b18031c02070909020613150f0c050a0f03050c071203030605241c090c0302091008210c0d0e0906040209151602060d0b0a09 62
    0x9030308003000d6000f44810140381d030140d05000690300002e102600c003c03450410034429a428003000c06240c400c0301750301d0071030100c01200b41c0c0754107076000310310502101d034600d03c0400c4241452000440b144504c030300210742401c1b610008640c000709440480448202601c03084151441c0401c240c0311280d810600074042d5004424000004518a91131710407584281410390038440c50701020742c03c020f40e64000c000c680303000250740024035916006100051000380c070448140c09079100b01492a103458140c11002e20390005001c2007192032074071090030380c4040100030491800c107454a0003040310244000d070310802c0013030302189001003030107070080c101c4540d00c0080801c0a0b1032507884100780c000c804100030001041c000c1c1c000404082c452000e01d1015a075514905a8821042011564000c1c086501030b920500c03204030b180c0c44040324040c040e14641c0d880c0340c4482c8001c840710700011001c00002d401010210781d03c41100d506400545200302c00701c5044120503100c6458004440060f199108555400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 662516321 1250 662515071 662515079
    0x1406040216020a0303020d092310090f0b04051008060d0330090b1f030204050c2101210b0412230d06090b06040605251101031404020109 60
    0x954000e00d4540406541c46010314029000200300e0b90b01940142c0140e0400c0e071a0300c1055174812100c80207000005030007040c1691004440d40780500700f40b8a85c0c0141c03001200220f145019109081c01040d600e1282c40d076958552002e0100303604288103441c098181350f0000c0c10441e000380d4140b446103a0160200c400d07004552402c64040001c2440c40c2d045011603002c016240070140c1010310484040080400d64140742d1804241d9210010030100844161100004540300240100d604880d0101c50204a40c0c0390804400c0003845080700b10200010114007511004540b41182812100608001c000d83e01038140d503c0c54158482d040148030490040000b80040c1c8180c031300c0041c251840c40d240da18202000c250030740921078100c00310b14400d404680c0081c62503d038054030000c0d14180f001444007a00440104c1d4603405035002e950203124002c1503605a0f1324a121442c0b20107140d05c0300004e00d40c1030b5402c1c5400c07200000c08070a4000303030500441100003042011514081d079411780d900710005243c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 662517571 1250 662516321 662516329
    0xc0706020403020406090212060a050a051002070f06020723010905040f091506080c01050c0d0807271511060402060d110d1a0d0512090111060a0b0f041406 68
    0x444088414a909210120158642d4850007000e000c00e40001a80c0712030318520fa130714002e4000c0205100c0c1226010a1145480700e0301003104464090b140340c1e4440b80203030f80a0b0b0400d00a6080244004000900024815400118481120100340c0300002103203074500c89900c4507030070030b420074040780300c0c480100f03c1410a03511450402c0c280600005540740c403913442131410440007104000980d12004140a000803e20a8541407042401d01e07a203805031100c10651584090211503007131100c4500000c00d81070060f03200000c40340940003503004207401003c920004031914019143c0b0510f2030189020385a016122401e0381c0280d040050091396282e5003004483d520801c40b00003075546401000c1800d144400143c180d0480c0c810340485d40182404111560300000400300e44200210720404011420219039209145941e4482c3d03031b5500070000c0142d82451040750319030850311070b13072042104581069110038002c1c1c81c00ca41c1d0000511100042005561a03103042c2804c111090001c1013040c64 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 662518821 1250 662517571 662517577
    0x150c0702040b060d06080f030c0a11011412010306150b07060e030d020403050102030f090607121a1002030a030f110a03050a090c03051e1908130e0a09140c06030c 71
    0x88000c0002c90000701c0100400c3c02074014003148000c01d521071030103103d050030034000c00f81c1e0484480021418102d440e82c000d0341e40c08074014041c00c1c62040410f2845545d01c10003030ba2208011a048159a603130000390018140c4a0034441600c64a00d800020426074042c2c28020084170000c0074002d080c6410f03034640b000188003481c28046548400c100c0d4101d660003500141005502803000103031685000740c18441c400500509550301038000c0d001300f100e850380000032500b904003a01170007c1c4120200050390b00f1250381403040c40e401144925040105e6500000410f58882e4581d010710140c50208200d82c25195032000281d40020180a012000e40c442e03403106510281c050030104205645894a0704842100d400c217680541042403011900003045003030526108241004020455001000c0110300c102e202c030041401c5000500b00080300500c00d21080a841d000450360400d0030041c941c04010107014104540c031001070402013654440210b90103090311030250010f403940d690010001c2c480d074 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 662520071 1250 662518821 662518823
    0x1008010e100e180705061e0c25031b0810020a0210020c0106031205070209040212010b092401051903050709150302070201140306131e090f020a0602150c07 68
    0x314003044000b8080400460042c0584640b580d064811598841c40710f003800000e0304414080c0e201041a55803c2444c03045c09035151103180b11441d120440c0b11011030605a4040e00c2c0b800c400b140078169840b440c19680d56408403482a001c02c14000702030100140405258828404d441d0041100a402c5c7c07440c0c0e030010000b5182d11b00c181e850988401e480314040b81c003d0310107091241e40d954424020040541d181805400450901504051081e0300180102400500003400b40c01d003112440c1d91450250454180c4c14801000500b052070011480e640c60320102c55903480c4100e114044007140c0d40a10222000c1107100760909031410012002a4040c000c050007840800c0f035058000524003500046180011410f0394000d40d4529040c0001400600442d42078240f6200800074000c1c1c0c0d68030703a240c408080301d0a40010468940d0300c804180c45006007a0f011003610f04016130324040000011092b0f020510860700340c85d12645412007242e031110145400b01340f544c06034001c5424030340900060302c101 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 662521321 1250 662520071 662520091
    0x30e040e1603080315030a0f030c02060405061b0601060c0804030b060d080409061503110306041d07090b03100204050306041401020706060801020c010608011112100f06020607030501051008010e 85
    0x1ca051541001036414140c2e00c1611502d0003c401d201e1002c00f114a240c0d8414822001407007040307029110541c810310400300040601020000e140c085484000507100201b80040c1426201c25a00e41856074100b41c1403003d03211070050034004605240103030444030029400c4000c140c2000e08503501d10000d201d0152400fa03011940c40c003208002002800100301801151401140d15483d041401108017483c403c40d00c00e15060100701c891003128001070703d911042c101d80c08140d4403103141d28035101e419031180c1200d42c0d004500c40840c403150b036031f08810340318102601264000e01007028100100d0186005040d41500510003244c041200f0f0a01d040682181d1400145007403565920141110481c1c0e10540d0141d401051452081300300388a101c004204003402809800c0c002140c4180d540b2a40306d6801d29041014045817810b01e652489801030400000130300400c6845a2003e50766110450301d8000280c1094000303e114204840c9046060400c0e450303a501c0e030390911150566007807005000c00c0d45 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 662522571 1250 662521321 662521333
    0x10030b0c0c010c0f03050106020601050d110a08031303021503040f0f06020f031e070810060f050408030304050a0b0c090a0605030612070e060a0f0e1609030c030b22030e040e 76
    0x48280f05003410310520751652840c5402c0d8840290035103a0580c000d100755004200100701d152a648031011f00c2c075903c45203030000030800e080003034000300c6160000c0d1554400030401003d000e40d02c04082060f2802201d00801d0025202c0781504140f01c11240181042e50713804445000880245030b007680c2c24402c29026050002120701c850890304212075040b1442c42c801d1711111400e1005056940203001c0c0d14103014189840c0e1b0040380d0061440c8190010003501462800442d4400c3c800c0d203015180e500247d0740d6a013414103050303959505500d0181d561403407075004a4a42c0000f03c04840011501500c0341158501d400300594080c0c100074031003604082081f04400c1c804106001500103040f00200300086030070000d0a02041c1c6003980c0058000c240004418040441810341c85d41d44880070f85442c4020b40000d640882c0c40401e554001810124040c602108101091405900c9424006c5101d81c1040d115040d1080d4a030001901401185070f20a242085080c41e810601d46070900c1c41c2103448d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 662523821 1250 662522571 662522587
    0x1150902130e0c04172b080703092a0b03160f0903030816030f020307080411241605030c030a030b0405070f0c02041d03030f10052d0607120f0810030b0c 67
    0x50540110000410445006c1c40a551119044640c068000c4040c1c50100306241007580c0701c1507a402c1e522945d0350b003003c0c0806031800003110380f91410064800b00c400d15450b4142441038400384a0030016480204403404203115040f441500f011045036050366440744c407512030802840ca070904101040c810192100050543c0c4105030004600802c410b0b40c501402d4601410400d010310340203c80c06100301c40c3d03000ea044c0440000360303450511114010303240303a03a038204048070407100302c00b114000d100d0b00001c61a01c907064008800b5005010254070240002c440160400044640888401300403444800d043c000d0707980f040c003410b426248040d0000401e00d108480a04803c02d1902e4441020781c0004104a81900c000c4443c940100b221000201c100313080c200002c984d851505400404020380c0c0d2503011910101c05030768445c4e0039000d828242d40d03120a08000310084c5000c01d400e03020800307a00c0d10414032031140082c01d104881c810f1002407042d0560740c8120520f003014181c1d1603160710034840c2c19 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 662525071 1250 662523821 662523853
    0x9170c150d0f0c020f01061a04060809191a07090e0c130e10090b120a021002070906060903020108071106060105090d0b0a140c03090a0b070201150902130e0c0417 71
    0x51030105a940051004100b00f02e521760035140340360894443c04d5103a0460000390900581510155602400d24041d01d41d034400c00c0318980b510300d4407c0344000f844988074000344a02460034151011820f04091020b540317107001590444498841d48048000074000110014441c0003d00440f05059a0a0300d4555590604881c0c2a41c20f980e6864084002d8408000d80f0780c2d83d00c5001e541340016035a0000103c1c007a440d658603400074500c043c2c001c09001031880c19a44c82030140002500049004110359030721024001c0840015000480c046008030010031005400707080120300f4012120b00519956a40400440309030700100352603608100100e801200141d409150948100044900054112191540090b41076000b400340040d8103810000e02070040c0300071520b60b082503002402d204203074039240130072401050081ba000900c1800c09902046445064004186110210740c218084035250a600c1d051800151208003140c85c4c1000100441c6041808014495001900f1b6a0761180207005031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 662526321 1250 662525071 662525081
    0x513020d031d0301090c06050f1e1209010b0307031e200103110307020303131e210306061b05011409160b0304020f040e1c09170c150d0f 60
    0x44012a000820201c2c80c041e01e52030011605904a009104030819070315101c8030902030707018036420090005100c03142c80d1078410846400681004007144204603010410311160031413070620014122070f401040c50024140103100e901c090040c0038249980c07441e0b40b0003403081504548402500740e0740a0070808240304ca031011010b2084040c0c030001510500c0c00041c110780343c0002081d1060814070a0044a070fa0010980c0c3d84580d01a5140d1445405418003003000f610032151102c5280390b0f004601d041224002c05c181c41c000c3e51403260701c0e58182020090301171340e61902501001031640002c0c4603071080f0b4a10513403101c82c00b59000040b140d010704c038094018041110000241d5201005190f91011070301d80c0e0800902440403031909604103a80011049242ca6104920954540c0d40308542c1601c01c2c00b07484106000d000c0b914440c0e10802070b001d4000833051040000030950004408003002c1702250b880070140000300364030b0000045041704a01508098070495000f555100001c960303110500c55 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 662527571 1250 662526321 662526323
    0x20301141e030f25031a0601140406050a1e170604090b041b091407050a030f180b13020306271014071112090324070807030b0a06030513020d 62
    0x25102d4058640d00001403450ba4000038a015030400c04d08101140300c180f800e030242c0f24106002080b90301d031200121841c402007102402d2049000800060082d000300c0207054000d10381d00c03243c2d8840806200c429448802e492410042201004450310b500c0140c8070142e405000103000180003c0c203a103401900380b40840d02100c80044882c1e41840541524400d1001864004010b00030442e07903140c895188040606200240300021900e41d454500a420407110740d50706c500c0030003609015000112080c0307505503091782e543c245c0d240880e8001034100500c42e4825000f5000f044181c90346c1d5583e00d010640125140824082640c0c4020b00460521401c0f01d000c3c0c8440d0042044025401d68414811000c3c1220040c4906440030300f11821022802c001c1c034101c81207019440780d00c4840468201060507140d00da000b201c03c02c0150742e01495014417801001e10b43d030365942942d03400038141c0403180b010711110381c000c1c0d1040d01005014401d8118940c40311074940414002201680814801040280 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 662528821 1250 662527571 662527573
    0x10c02030403200a0302063714070f0b06030a0b0106020318031b040509100509010204080c0a0e0105061b010509010b09100303170601030b0a080c09060103020301141e030f 75
    0x14040051041a1000c40184549a030446412075403201c000340401d0281e00c40240175400200d426071800000c8c1c5241100c0c00781801c140080ca0709001d05110060801c2c241d03001c0130512118088500499143c242e40075150310180000a80c9990384803040c039580000c2003958144520002c4c000000c5401022900801c2c1c960011610340d10200110f8100018910f41503020b0b61040e4a40c0400403043c141004455200781e900041588401d051542000c45200c903080c003083c00c000c1030000e090b10540c000e1080702d039400d083d01c0c00600075104214141c03900c0e1280d8528000461300600c55480d10b480142050030309019501040c2d00446089400d449080310810050b96684028400c982007000000764418080200c403a0054110b80d40a4010301002d00704482214480c400191543d0003580100c580c020020280c02006070b031030342d0383c5d0f6035240071328801c40c0503003984008208036501078002c1c1c1c8d05030b4401403490720f00000c030307802400207000c5030802c1a0018101c501005069071402e2000d01c0043d50114 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 662530071 1250 662528821 662528827
    0x21f05030703061409070e0a051206042904150207170d1109100503090a020d050604120c020607030f121803021504050a1b0801060f060e1002210c010c0203 68
    0x80c08030781c6664070041c88030443e000140001c0d900c0c03e8650703500c041b00c0d00380480f11a5207000460400d180c940c06c141c3c0c104941c0038000c041c46100082c003c0c89a4410400be0f010b4100020513000c90b105200c403490103030703400305c00070900190142c1c00b0300c03024103001d000060800b6010f0302d6104a00f400c800c0e210300a468000b400c9500f81c4071a000d2003200034422018a46850382e07400200349086540c3c007001c81003150120100e000300300d0500645400360740090039610b2051080c101662241c8003a0340854151004503941c810071802001e164410a8006040d02e04188c081e84080d0380914941e456071040143c000c920700c03d10480c900c80c009072010003040c00382600d03215143c007170300d042c0c44403102c003a00240800030407002400004582011580c030264502072039099030221509620382e038000c21030550808001142c0b01e03104ca48003070215683c9641d44901a9101320500400001c03079586140103070000400110000c00314104003240000c4c4c01503082c94201108800c508403905d410501c0f005030000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 662531321 1250 662530071 662530081
    0x6080f152701151409010b0d15090207030f0f0903080a0c1506140a06021504020f060706020a120b0d05070b130b130501020d051903051302040e060711010e0712021f0503 74
    0x40c0c020140016045d212642154142400204180074000030080e0700b1b603d60510a60f005071402d120001054558002d6460707605504e0b024100c011151410000943c2c900810240c0500c02d00200d070480e6041271525103130074000300040b2881c0c054414203851400010f603003c0031048085c800d8800500842d111990310189400030030511110700d60040c4115480207007080320104018070020b4000e50b04440c41240320701d90760702060140c0038600d0041c103401e2021402561480d000901c01c81110401d03a41000940741c00010803091510a041c0501154042103082c003200c0301b200d00510300c42c00d0b01007a492045a44094501c07165001101e6111310754042d6100300040e50301085a8100444503050050422a0800e11200d41110f194400810951110003041e0807207110365681c10803903000b5000f40b001c16a562580ca0f03440c035050307800c079001401c0c0a010f40f13100001840340030003160015001e0850035240c14850450b19943c000140d034801c2c44102d00d031401c1c41c50802d00385480d807242d868150300ca02d00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 662532571 1250 662531321 662531339
    0x412050703120512010b090409020a0f080105060a06211509061707080a03080601120f0218030105060d0209061801080601140105090919060312020106080f15270115 72
    0x140902c001841000d20224818030001d02d500c0381900c10381c4403001d49074001040018090051840702a42103001c080c000b00f0030220958445043e10350502c000e122a0316002d0a206c4258402c1c450240014000d9a5401d10701181c60b10125210f0b0400c000400e00e16401c00c004511680c50364806480315644150403c03039082403d4007420842e281c40082c046242c6081c0c3d095450700e02d00c4038014100000c42c800155543c2c00380d240343d00c0c100b00c610404c200e01c0380000f80d250029400b90200c56418002040d070b07081c09260502465100380070240030300c0c41050445d828005100000341401d030348035180d5803005440100d0781507094020000600223205652401c0b50050303050005215807810803004102c0d030070550322521012030b08040e0f00e5070f080f081d6a94000a520040c070a907000101550505207420b44d41d207174150066001c0e00c03211400c1d5040440c408422903961410b134142c02c180629035800190308012240204101c0d00300d00110000c140c1100041d40d82181e10440b5441d10516081c00144503c0301 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 662533821 1250 662532571 662532593
    0x20406090216020910050d080f040b0d06140415150c06050406050709080303130b1f0329011211060f041d0901021201151b110414160507080412050703 66
    0x11750350303204881d80303400c103c04a20ba900002c00041c0c80d92400165280285910904803402030000382841c68032440340900040151419200303e03804c1c40c4d08068019030078a4940308100940380c04850035001103240822400c5e41c0b025050a000c10b00004442c03083c00302da440d0054511462148000059510f001c1501819666007034100300e200b540180708001111039401c04034500387d5003040a4008036912007865072900760300324900b40b00c51a03c1c0b000c0001000080700c00240100305640201d02070031500c4105441c80042442985ca620154440701000300b6907403c201014848050309251401980444a40d0142c0c0980d10130300c030950740009418034501c01a2009030300000440c3c029854003200510b0b4201c11101801103840040810803040100c0b40108030303d0b13414001842e410070013442d80303080101700340038a211030364011030800e06011800104034804910410705a00443d0034400d0740102150f0703c0d00160402c0b03d114404000c04034402a190300348950482c454001070a1035070861400fa01618 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 662535071 1250 662533821 662533831
    0xc14070b09070f061b0f2405061212181f03110702010206070e030709140604050c0f070605040f081204021801060e060c100203130c151202070204060902160209 70
    0xf0003c500140f180039803054003114800c05a107140380c000102d07428103589031010341000070001c081c0d420b0710004082280e071301150b007400240004c00081d41e42c4030071b1024400754141405000e80000352540b00c000c50306000b4000c0340c522140500c06195810000c00e107400c2030301128644002c035144881e001260f25016a0f0b2412854816141c100040395001030750710440980007106010054007551344c0e0761801c0000300c0041075500c5080c8400320f19590200f070407403015128a0f0103a4285400100389150000490700080164200305142100c1511042e0041002800c04c58403070040519000c0400d80760f001800c410901c451040d08103092501c100003140355140403807441882802c00400c40301c3c0d000b40c440c0c0717016442034403503580d0384a02441c01e90400202d1480f151109201009000f04689440d1041980c584030f91111501d85481c0d402c001c09006040003464001030480c0400c220b142c0031a00a008440c3c40074101084068550003180140e802601d018008001440700700e03419460f059100607004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 662536321 1250 662535071 662535089
    0x40305010506030d0e0d112812170c0102090d0b1504050412120902030d02071a03150d03050d050906070329120316050a12031802040c14070b0907 64
    0x3032001a0702030302252003845c84a1240708801c40d0f20042c0081c202c210510620002c150038120240e41c00030112080c2d0002c2c4060580c140c126012851361010703000280404e400981c40c4409520810305003150b41e00180315040c03a550240300d008a0b0381c80d03600c8074000f074500c610240c1c038851820102d0302000540224040e881103040c041400701040394440d101ca07014001d880c0c0304a80f01a0500180050803518000a402d44604003583c1c01c07440e40402d450003541c008d02001014995220000d400c940030070354070440880440f8004a010b4600001d03200074040c801e040040c2001041d04c124000c4850483da580000e8004600708000d80e1b0307140c4942100001c061010310300d402031000c010650145001d00080c0129088000c4202d080d604205485440502c6075803800403100300d140960f00c8051420302101d050450420214110b0701a000360a500301d1075018101504101e41c08000180c2103090b05101444550511160305007404d0b40205240d50103130396501c2160500841007450640d16a004030300c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 662537571 1250 662536321 662536333
    0x311040b0f1302130306020a030506010518040c121d06010807180b1c0c0e060901050d02010c0212012f0a02030d0e01060e040501090218061c052104030501050603 71
    0x1441d6190811030100d0003094910b40c2d0304102d25038000d4024810700c0c08000311514a180000100702043c2c000b004d00c910569802e004a407250401541c2c2d5006070300b40340005403000321314400d171400c1907840703c2c034003002501c2c1820344402a07040c0d220450703080e40c0c000340368842e03411442011840108110750060074524000c00d845441d014512150440042807001015100d5111400580d10944018150030700c0b03c00c121214042460144040c0106108a00c00700444100090040c541f40e0041c60403250050540c0e0038014450b80119a0103070520400caa000303d0030006002220424480c0c082d20b40c10128014840c0100c80c0354240b0303242a075860701c5001d10b204000c440b09103940841500d03042c200242c008241c101d1166001d074007500b0b26401a80d524040901000140303d0305400c100110360080d900007401140d10005050110000c803269500f00c441085145c01003600c1c0521034080c00d000c0c0058031440d6140f5060a0310030f506402140e5101c020208050041c04000e114042c5c0043d422001002 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 662538821 1250 662537571 662537591
    0x30606020d140c0709110c07091404082101120512040602030a140f18040e0105010608071815020606010906051222020a061e0c0503160c0f03080301031104 68
    0x5a00c1900340640701100208103c03400403c100651400b4005d00c0c4000d000400e0000d60000e0710b9040003020141d18070500d000007400100900c921001041c000d0040c0c102c83d40c071034440720741c1940a50058040d030032034018101000c0d02484901d6001c0c0207440f4100d00203c0301e030308220b4609145042c0303000101078100b208100301900081120300305405030030011100380750100450024091803a000d6034071f0340d0009482004003094a0b000d80c40303c008440800c22542c5401031542210b4090103000e001c07c00581c0414400c40c0682900c0b800c40d4959140011990b4a642c0406286c00c0a03000d14070159100101340b10456030000e004101030080340c0342c60f070300300030000c0d031040035551015240c00a2030501000114852001c1031151044a0b00038012003821981d924008107540030a0445c5584103150340c0c0c1c00c1e00414030031682c120110390080300860a040c0c481c18503002000c000380c811039001a401c100000c140b07003417803880001980596140c681325859402d040c0140520072003064484c2e40346c00000a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 662540071 1250 662538821 662538827
    0xa0c0201140f16210609050106020a050a1502040f08100e0d0804023006100b0a053c0309010606091d07020c030f1b0d020a0b090d080a0e01030606020d 66
    0x83ea100300344800480348140c1060003074032100e2502100600d0811034000c03d00c514004c5410a10071100000341c20009aa6104802c9846008041c801001504200e01a0003c95508045c400c001c030306034440140303850303550740c0403000c802003581c04040d140c0c0008080b140d516095100d500076116003600540740980415000601007a80144001d110f0140001038180c3c170340ca00404a08003c40c0d4050303800410f09640d48299850301e0403185500300400f00803002c151500c500041e02c08000441d11194203022840419042c100c1c0c283d071020007401111505031144c0c0d08144014041d0045001440359a400e110452034203581c1380750000c8092142d004010414118010b200d2403c0b4403800101c1220740d1201a0203e050035200006664188a030103d6904400004500c203d03030703032200d04144a10a9040c2007405015940a0700c06940b10656010402034400340400034003031450000c1c0000240744055031042000d400c4100c145000030100301c883c400d19601071007028058501c1d0300051a580c0d100100003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 662541321 1250 662540071 662540101
    0x50910020304120804050c090106020c10112a0a0312080a0902010c022808150a0b06070f03050f1605010b0f06090d030908030a020a150501120303180b0a0c020114 71
    0x3d000300300c11180000c0501405200c3c0e4840309100400d1404c403075035a000000c0da1143d00035a5280b00c0c0b083c10084031180d601800c1d80ca400c4404000240c402c0003d150702c04c4032114a125640b220700d550811030011590380312038580010354032503443e245505240c0f82004054480041c40710b081c4910307010b00c04016030b8001c0f04152103294109c50b5614042d2144152071b050781080e501d40803903040f012a01084c00c0402085002e020000141c070841607a0703440c1d021b4000e640c0681c4000342c110030100b00b80c00108900003100c42007203009041c05481d0104d508100005544407044176030303d44001c1f0380b44000b0001c0a000c0c4004c0c3c039004882051140100341c0000380c0600c03a102a140c8101039070b90700201094001c0030700600800d03014043e40d4407030321003280c040e443c5c18810004440410742c0044c188040c21092103000e0607181c0130800c40c0d0b03441b500781d5402c3c1d00078416405c80d1801483e18031484400a40606140740c882c10400501103600d040f010406404d4410751121003100d100d0800420040071403901a03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 662542571 1250 662541321 662541353
    0x15122604150302160206280801090f02090d030e12060705040f050306061e041e02031509040b010e0a020c0303040510150605220b03041b14061c0f0c03050910020304 72
    0x1071640d41c600303841003502c1d01c903400447c031103080540036840c100c4d0342d8001400b07504075205402d06020301301d0203c03a140b040748200d04055501c03400c10f0049001280c41881001c080c4d400140c028245400354003040740c034261040758034038005000014240000c00c4503440f40002098242c00400d41303420400000b402c1d21101c464510b100704040340000c15507075070f0346d009036122100e0750908120290300000f141c001fa604c01c607040c44690b074003032840461608140882d98812504040d42c400c3c0759081c07100c440140c06c3e0251001520319001c0c042590300e548180011402984244003c00800340d07460b0380780080e582c079006161002050480d0070014150080104d80c05801081d6044024900d205a259420421303900201034915010007000100320311710451071810480d915407941001d03542c40c10040c0104070541c41070340205040c00300000c600707030559a84000180c140000300c3e840500300c4024007160b29404030800082e4440c800c1c494450300c140040c240b181c208000943c61454a6140c81c501c0c4048488 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 662543821 1250 662542571 662542579
    0x40f0c240807030204051305011a0f0d020c0106091b080f06010905010c060f020a05071419121403190f0203010b0405150412140d03151226041503021602 67
    0x7001030b90300791180d81181c0241000410642800c1c80105240e0010207090090384500c0e81600803220794041c1c400c0c155640500c140000718a09824101018065002526020740b15904d03144013142605060140c000c501228400d00040130a600d0307001025201c0141414100341c501c641440600e036030280f0410242d4500b8200800750035501d00e0700d03000404120440741c0700d4030320100f040010150b0000041c0030040c001c440c5074a9403103d03109280e131600100c02c09941c0502c510320400d00000e05a20322002d15911a0500e008503001c0400200310350ba0040b83c00201017444400c0c2050300c40309520a00030600c001d010118119810320803982c403140700e80c2c010988108000400340700d600a40300c040340d002d003074022101400004149804081e640003040d034034506004220391380c2c00d41407003841202c3c180315800c1071900c0e202e032802c846480c84110b180310a0340e8407900280c1c00b0300c2a18001d40000d10500c00e1000d0380b40c3d90752514007101505207141c480101050b004200b5011940c1d603586000300260b8040b9 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 662545071 1250 662543821 662543837
    0x612070b0906120901240501020d0c1b0e061c080a03020304260703030501050402031b16020619080601090602060a0c1e0815120a0b0901090209040f0c24 67
    0x300014914041c00e00d26600b800303000f50400ca5081010b420034501c0408401001282d100b25007012801014030340a030b14016400f030440036032102c0c4601c200714038075409907810b100344040700010351100d807036141c00000030f6118201c2400300034101124690700580a901410808080a90360010b4510a05103107004140d00031012a061080f40f02c8454030303603100400c0920700880d240e580074016400070181940802e152000024070703420035008480c810300182110022040700340322040c07030a4102d10100f070b9820300901c0400005031900310041040307401c1e5a4901c194540700c0000240001e400402c1036041028018041145a40000d1015008003c040303022a500207a007030110f8480904c14046000d080403114605080d0350007100781401201d440b410f00302140d0451080c40250860500c1c01d502c1a405a1244000300700b52044403a0050251400810a44000d40002c0c8040c602a981036138240c1e8900c130384904200104031000010070a10300c0260b414020000c1c5540014120203040041c0f0a4607 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 662546321 1250 662545071 662545087
    0x304180b0111150106080f1326040308031006030b130b1c0f03020708071401030e07050402040b0d06050d0c0e0403171812040e060d11041b02060612070b 67
    0x603108510703a011078902210442e2203e1556001c01e400c0a20414006c5031201010844181840704007910800d034040e2059400e00041da41c0c00e86100d0310001c0e0305c18030258542c1719100750701000020703c021802a09055160b0421407003084d9511010f910150030301d46010031007010345d1640010000c091070450703070000380038003a40045942d2298280c0802020b614540c005020060080d007000082d900039401c5071001d580701ca0340c03c0c0e07540c1070038050120000d0f802c60f800c0d00b0301d612a4110010130708141d4152130400d55240d02180aa17081038112188604002c10f001001e81428820f9000a10b012190302c820b42140b40c56019080d01d144c0111031440320004000f83c14540071b08844440045c00703500c6100180740150240e0031049880480080500031132181090494000c410b44003034404400f03400d2050785a0004004006501d400110741c0054200d0b01850140d07118800c07007004400c10342c0000800030044100031300b00302c002040d007031041c2c1d0188064028135800080724025030711781300f20303680c1d540c130503 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 662547571 1250 662546321 662546327
    0x2060d09050d0f0f08010e18010b1207060f0e0a0e0a0e0d0f090e06031b1903050a020103230408030603030c01151d310203100b120304180b01 62
    0x121800c094075602c581500c4050b103940c4110101c01000450b5100141c0c03140010301110104000e120b00c0320110b0050703010404004100054454038540b010000031007240a001080311107507401d14099450f00500c1003040200e03000314082c003911040b45041e03c038800c0c0040000380f2644042c01810207555402d80050181c9816a0001c86e940414a08844a40c00f0020009141d246c950110f400003e0700640001060918550780c5030003180010b001d44200c4034449480703404840003031155070b88104c0803141c9021810b040c03811400910300401c080c2c60810040d0002505403905c000003c5900100b0174840c1c0312507403401840380d80080c0c0c89811503642e030700c0e00750000e0306c2c5020f0315a001c07569500e01580c14510000c0c004002d011030b851407442c4032850f40c041034140f10451040724480161580c0908040e4482000880203a40d99590071260300136025a401280c54a00c2c1d809000e800710b03640d880740c5501c2c1c1c81c00b1130140c0000c18401006501e0b1030b041203104102000712217001c0e08599201c038600d150b2a80 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 662548821 1250 662547571 662547581
    0x507140306313f05090924060309010c0f111908040f080c0a050906090a0c090f03050610170a0201230a020703060f0203151002100f0b01140903070302060d 68
    0xa151080505680306403c40c01150300324500303040d5803810403d4002203505010344d054880e81c92000703040d500c0641d1505010b01000c2510002448001c06032050140c803550344802840c094854003000042c3cbe40c2246c18040d10400062044100b8000e902000f481003000002e0411144184c0310031080f1440110300e8011580e000395002013200a11080740811a40030000d030f4180036000484840c0745031541c0f4030900841480588401d904041d030480042d003216096088004080e0043c50b108441300c0c0e4a4000e00c0c2c001800d908119540e03003120090017209041440000042c20381000b5070207140c6205400aa83ea429102c0003d0502c40d03080b03442d149540764012000084440c0c0d44041d91f5441a0600003074480303056001c110790041c81c041030510244104d1081d2441045000203018081c10220100880b001c20804602c0840c416101044180602801a490000180380c00030030003240d20800500540c070440c0c5402030241d4140424003107581d00056400c00c0307940594000d0340e142030044180026103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 662550071 1250 662548821 662548853
    0x601030c03060b2704180b040c180603050f062701020405041107020306010603021309022208010e0d0c080301120804091401030209011d0402010e0d050714030631 71
    0xc0442c2030f40800700c500084840410500c0c400c00c00008184c1c0410048071140300482c00c408142003018800110059401900640911003240b0340c40d94404102c40480c0714808142c1401d030701c85204004101e020400d540b6400180d030003400061070406a840c03403402e800901c49407011205580d60050410a50494014200140090100d04000c1541001a600404040303010380b1071400005100d40c070a200355031058803284810807002d45048079031406034103c10300303245103d000320703055540307401e640c8450b1002050407100116005a104c0c403080c0c00c180143c3c1c41b41d824031180d44d6002000403164822a419591300540c0940c0c60052070400015a000316003040d502d0602d008002c8001000c54200141242d00c01c8440e20200c0ea211282802c0103030350b146501c48240400004140198041c071000d00d00700801803d182c243c06955190b09103040d84560060750b480b002c45c8c8945007507040c140f258541c003411080c1c90b600b80c00841034181a000c80d000c010702101c44202c0079000c04101ca620102c909007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 662551321 1250 662550071 662550089
    0x4021309080c07060e0105040b12190f0c090b2503051207111903020307171c0506040e070317070812070809070e090d080c120906070905030a0b0601030c0306 69
    0x6242c0c004060baa205507038000c4101080b01c4603000c0310558421004c0701d0a8035900303c20b56041410254000b0b050311310141407e02110300991114506000e68402c00034080c25071203000c24817205d044005040e00382541c000b5406104100514a56000d588258202c2100500180009110a8201114036015680454000312040000d00c030705558401310340b04070103400e6800d6800c0007800c014100c4a0801d07841004015030410b11408020440223010484020303680c480e801d10f05103491070241030040e4401c041c0c0c9050b981e180244810f900f42440748842900a101c02440c2240c1141c481034250400800000060b120000d00401003160080230b981c903c452901403050141484103024200503001c035031900c03092060744400111000d40000d16409100300364003400b80d191000d030307044801c0f40b0028180c031241d0302c003007042d0035418844801c081d02c43e1041a01030310045c05c00c503c004080034500c0d80090321030f50159043e0000302c3c02900100750011002d00f40020150015072058000e0000ca80c030180300 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 662552571 1250 662551321 662551327
    0x7080a1407080a02090c2208010c0207090905120a0e0a03030323040c120602070804030b040209010e07020312071101061410110304120c0906120b0105060a080402130908 74
    0x4100c8000910980c4034450816200815115034009079112001c0c1c00c069801048440860b4101d04800700034003030038412086500354003c0c0030059150708001c0350b0004005039582c0801c01003042c1c3c1440014054012170100f031213100e08a032162955000c20769101c1d203a4040c00292a00014020101c1011804005c0c0501c614665281001b50051000390710003100c1c0c00c0c101c0c1e80ec00d0100d0303c1814043c0b083d58007100c2e0960050825000d500d260050840840f0b5050b800c01020f0045103682003e40001c600c5005c0744030040c40c151043c0040700c501a40a5002c005142090102c000d4010040e07a09008290011001c0d03690f605508031800600e0160703002095103004000300d9031100e05071790340035170800c03e0728200000c04200e42c08842a901080f03e00350782d90001d2109010f0344040180030703020726001d07045101549880f1940c3e402128401e1f0f005038071600209640800f00110f00546500401084500e1400e0410703600015001d648020b0000380f103040b200a0b98400c0b00b40581c000c044081e001000162 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 662553821 1250 662552571 662552573
    0x60504050303060405010e040b0403030b0303070609151107110d11040e0c100507020f0904021503010e0106090504021921020403050307050c03060105010203070303050c0f1c0b04180b0907080a 84
    0x344a900030759a084c01203040500104104412482050240343e02a02d1071003241e40b9030302c1c2180140710b0780f103429a26000800c80c0300c000c01c0c0140a140e01050140007c0901035000b4040d817400c40f41142144001d0354002e00c60039001ca02e5101010000480c245c403585103c0105113000040e0313a0254a00ca98030a240c5040410039040006405035101001d84201c1004425903206440501031420000d501c08403102945420341440c8420a42007440079240c4640a200321040a080f80c100740c101411591852004111096004180c0d00041c041074908619001c01c40144400035420005a6014401c0c03e41c03443c10b0010022008a040b02ea000c0011520745850b440c16a1b1260b1003240c043d1280d1103210043e00b100c3c43d0124805040f124160002c614241c4540d400b034019010003040c050201205002050440918000420789600010403503003e50b41086101c000b11201030900c2c1e0f02130b1380b5045080007411010b0240e40401a08006440d40c16078031803c00074504982038114142c540600c0b40c101d8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 662555071 1250 662553821 662553823
    0xe060708180627090606090d0203030f030708040510060f0e060a0801020406050a11060601020a15090b070c030f18060c050a1a010e090307150b0301150803190c0c090b010c06050405 79
    0x205407001007081512440f009481040072402c03045e03500e01c0c0d11440800806e1903a01d400582c2c018114805030036281001c80c40240d0b5140e03038104070b84100101d420007081008120040c05882d886006040c1e04000c01810010305402d4841c0a0203403a00c1c90b0354240c00b103501d42e45e80c64950700007048800d0096590f00d40784c14009046410040007440070403100c100b0703d850104082061442414107a0050200d4841c64848100d1400507030401c107000c5544407640e40c0841d10b060390140c40381140380c0392440207088510380107043c00260076408080001c1d0a40900c4882c100818803012501d5910b014005031415040c180d00346800085e00802841034a58410500360151802a040700d0400700d2040e8141d1742e8041d96512446a40c6009003543d080f00608d00d036011080e0b0001c5140b44002e40002191581c6c1d401100e019290386c0c01601d119800072400300005d40e05110803a030007203418035040d5000311003031b40c61900c001202c1c01141d642c941c4800d03e6400503480b49840ca540d5507000003042c0030b82e0609007056 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 662556321 1250 662555071 662555107
    0xf020910080d030b0f062503090501110102130b09010201110417071e091518091104060605041a09091303020d0507030509130b031b0f010e0607081806 66
    0x500e218050885042c00c0180280b0400290744030241c10840d44100f02d0302046030035881030f00304003100ca007030080500401c070303c0380740545490340f0070f4548841180c1400c001401e032004c404641041607004210f01c0c080451840084001c07503038010502911080c0801c0142c0c05001c03014201801c200c0c0100c4c1c0000c0709956006072405201202c0250340381d840c0c68030180344902043c074500e4120441c1d150401c0101c1c3c2003d0b03100202c0a01c002c07000c0d00c1c1c1a80c840035218405070054214851450301c808208051142c40403e209a8034000c46040021030700d00715001d80207001c0ea00c240e4a040c0380000007140d003032031040101ca07440f1000400048452821807503c05840070450000d5006105c1e80001c81040d42c000c60403610659003541f1290b00b0000318400308805814411100310302d080d00c0d80001a030741e8804120281e100340241c0c4000c803070002c04800744031030100c4440e070840c1000244405c801c2f554485004a451050700404110f80e14a107188000c0e0f10307000c3e000ca0040d0000c20005841440c0300c0e0b2510700d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 662557571 1250 662556321 662556329
    0xb0c091c0b06010f0807050a17070201020306010305090606102a050307050708071406071104050106051b01020a210908040b03071b03120222080c10021204030303090f020910 76
    0x1410780c0e501c1c0d51004486150114840d030000c250307104003044e1814016806042180c2d450b10f42a150308042001e054071801d07056075482d0140c0e4005c400d0028960700340c01484e9021607650000e100915240000804411140c00040305100003500032406404580b400c4d1500443d450081045c800c40714a82240e46e5031002d00280c6240c0180303c008a111140441d1420031100200e1284881c40180401c10455501c07941c811581e1220340603c0b810503850f00c1c01068002d00030b588a550b00d907010052445601e0210390200a102c2c0d20401031896050303006101c03003409800b0641404540305401510200400300c200c80078081d188089000a55104404c006500c64a40d5a990b10304d07141114405c01d83c0751043e0a4004c020400a90301803840c5c103c0d079030107050b51414007020201d566804451154035074a0a41040c0f006401010040410741408284901c142e00240300400030700c046070301408074070f000d10f000040c10075131541c4c2c6450900040f0710042c4450758000b0820318040c284140e00350b61340d1078a842 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 662558821 1250 662557571 662557583
    0x911060f0409060e040b1320130c020610121235060a1202100302030c09092409240f060d0507090b0c0a122102070209010b070f0b0c091c 60
    0x40047c0740104240303200d581460b4070055000d400d0780d904a07200d00c070303001c210909908003580c48843d1a9007425805241f4800c15150007600440c10007072685440c42606400503c80c0664002100d000954402c5105100c0f41c0e040c0b409004c0b004410100b0b8904680f11110b035220b881c0009640744c100311416006a0040008aa0940900743e440090344030040d20000041d600850200045140d20b02940040d944500c840315401d01c0d0127801800501c44800c1503800a1b900c060501032000d40b6284d141d813100013030300e04075240314181c60013040d544a80031801116610112859100403801d4840c104240002e01c0005d24079600c800c0c20380003441c0141001c41d080000200e5148002480c4940381040741c04e48803a8001600ea03040c4e00340c42d00102001d00c0b0301402c3c20003441203c91011400c0384510001140760071080565951928010404000c4040e00200c2202e0820450500007410706040c034000c1a82c0001c0c10350450303481040f4000f9502a0341c10068001800000ac0030b8044c290b0b604410026101e070b4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 662560071 1250 662558821 662558843
    0x30305060a05100e011d1203120c0f040605130f06080603010c0e0d030c0507030c120b0c0301121121010c0306080d0f08100902210a0911060f0409060e04 67
    0x40700f0024070002e00e100300c0022034688200e10f01554400c101901c00012000d15103182071800c8008107101c2c9906419080c110b070400b04040d01c0352401996900d070024503519006081031500102620241b01d944a014103020b00001d0414414151107004c00040540c4211003400b030340c1d04d030805803400c2000c8410501c65441c1001c20030302540520001d20345604043c200a07030301080e40c0d80035140b100803000191004e00c210500000042d030b240c5024005070030b188468041d007074014a8440c426107005001140500401d1005018410902d20350400c49900241f40840804040b0080b941c407141d0300c0d17441c42c0e100c030402c2000301b04c00e44150440525460b555a00700802940c03400d10f1034541d01e00400c183c0005443ca1503828100340700340016900130f055180400905540d80c21f0030b004992110301004980701c40800264584011050070550002007c101440020015039a50b0b68800190440a114001c0483d504450811000690300905454030301000032540315a181413420404450880d1303010112 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 662561321 1250 662560071 662560079
    0x70c0b0c1b120a2001022802060103020d0204091506060e01091a120c1b1e030307120e19060603060c0c2d15050f01060306080c0f1c030305060a 63
    0x1d1005881403045209a050804076502281c44903112801560504070013401001101c40178030042403a4408050b40f07009001c030940f5488001a40001e4031429034101c0401003001d030b1901c03910b2038040c50b81150000b074440c86a19004090900803c08030112038601003021484036040003c036428494240c0311300195a40d51007501219030300c3e07507150800b40281071108010301c0300a40e840e03035000000200c071242488481c001741c16580d1501c43e1110750a60243c640e926040c0491005107201c4034511001d1413a5191244010385600d841d2906201001e0307650440a076181c10a0000124401e4440351004280045050a80c05000d5900080d40e00501d01034064900038060b9000702d0b0583d03480b000201c44510404c03005099201c00c075902c05c0d0080c1e1621602000148407180b110000199a1000907550401c0d50f03101522802c160440018146025411300451200140312080c50800f02c8bc603103000000c0c00702040c8010b0661709080c240c0e0207440c0f1080e0406400d504958880c0c3c0055400c8c0403001da503 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 662562571 1250 662561321 662561323
    0x1c031812120b0f04020d060b0f0d1b1d0a0506040905190203090a03110c0918010608010b0a05090408090301050405150702010b18130816111f08070c0b0c1b 68
    0x4040b4501c0d03409100f80490006905054002d00980031100d8070018038240d032603841800310b034007154500001100c006890b4410032070324401c00341c21070010621809083d882c01c5010345190300241c60800c8000804500604c03540d1854140350207888090b210584842c0e40324030a8000c2c0c801501d4130301d000380020040100c404040c0c42500d10800c1c0c0324006110084880e02c003070303451340e03058100c10409004090040c00142c40e59051103020760811403244c3c11006c1201469821641290040203050b4103140350b8410726919070740a0300c1034031421a44124540c48601e4015828403c084959415508003003c0100380080481c03401c065650340c03072030044a6501d4a1089080310b00b8100855805403802000003031b13490b4403207011503010714202080e412041381c0352211403441d0000c540c0034036440d0511a0010801c040a40c03c0150010140c400c1d40300100015148110070300a0f03080101040b6035500018561031044070000340c8190081000000c90502c021402c200d0381c0608800c86000195800e910342c1c450b0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 662563821 1250 662562571 662562581
    0xc07050f0a06050c0f06070903050d020706050d1d0105070206090d05030613020a03020c010609241d06010c060e0a020109170c040c0908013204051c03181212 69
    0x41c0444025030030700d10281c4207500408490482c611411040b03808451040280501a0a0980b035031500786156103010380c5483c0402c0354500454000600411059412900781c441c1c0708201c4e040490b03151480703091100700300d1a4400d009041c3d802c1406012002e900404d80c0c03409188084299000e0a0105505544900c426614035800010a0040001855159000d04401c86035840d025242803907078103c0900f0b440742d0b500910307a40d03980c03000040c0d540b000800d1071080806464128031015846d15141214015030139055214a031051000200182c0c81041d1032105203070300c003030304002807101c0445440d507a034030604049012079082c20011420b0351001d001035a4600340e0900902c8540207200520005e001074451400c14040300034408641140300b8010401d2031607585814100031400760040d01141d00d00382514a0200311a00144008101d0214400d408419811070030b0040c40c0455034101c00800c00d071090042e010020f420240100610910510b60603030407662076801c00c0010720700c1401252 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 662565071 1250 662563821 662563849
    0x91c0f05190807080d09210305060f0a050405090c0a140f1806041d0a0803060310060f120c21020f01020f0a0b1f06081602010204030b0f0402030a060e01020c0705 71
    0x10000784003d07000a21008024072802e42140b501041062642d543d880035010b14100a2581240d140f031560304d5107601d841850352140c0220303202010802d4000200d0310b1840140160b900407030f10380000038800c010802001c45181806404507e0722980c030850303610310136101907071b035407107054564034000300c0d454070703d126085040404a00c8038003a1907040401c0001c1060403600502c4003031810402105800910101b2580d50050000382da40340b41603420941000381085190005520b441c10a10007984c13151000810390b10ba2526221035885603040c01880c2c1300b000d03032040300b006c050440303d19007404440105c02d5945100303035035003400b100340e0320016a2110000c1c8071024542c0c1c0400110f501294208106941241c0341781e1380b012420b0290f03050002c1840c8150402400719040e0000d000d01d00758031a4400b1300c1d40175540f00031401d00d42103540b1441114400f40c080105041d04101140c00e65800340440c10209501000800c518040386d202507001c0d40101d4141c41d05400760b02c0d000151402c003028414810 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 662566321 1250 662565071 662565083
    0x3210c08040b1605030a0905030f0a050618010605031002040905060405090606060921070602120c060a0b1314061306050306160203070507060215070201020a080705091c0f0519 77
    0x454103002c6020200c0d0490381051400302108940341022403c240010040550180d0762515250b050500b03241ca040701100072201c0c158030041d00d54010900102d40503410030441268200034208090b81507000d08000d070003041e07250003080059600001c00350300500c1120040c100a000541d20340c1c00304000c03118111401c950942201001913035a1800200070520034800410000d100d200d050109801e242c1075007504050765000c0c01051000d40e804001038200e1800508080380752465134892180c5990010300702d040301a44805038807089590707461481c1308501604008002ca40f040a4810030100c10985081c1d008a4030312100941d070000c58003c02080e154040d0007041107403200d1000300c4c03203402021403090843c04140030140014109101c17810080c045039006145c00315444141d00a121303400b804850a40e881086a200c0113078020424580c0020141802600c5410b02030209100c484602c85080074072001d0b848513130810a0b120200f02038540103100b118901100d1107000072201000a0001d426 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 662567571 1250 662566321 662566327
    0x130e131205090109091503061509060b0c1005061203034219080a03121508062a0c0717010203010f230a080f060a0612170f0403210c08 59
    0xc1c160315821503850122070198400e81a80d494580408503911500002707402081e01c841006402042c1c012540038028113010310f403038006850364407940c840c416040f450380c0c1500e440005160341c0e10f09015000c2c9210600a903662407400084401072624251417050450910003060012b0000b40c040c140c80d48004a840480328056040410090b6510026140c8104240303100c0441c04e101c050150300450340c4291100c0b5040b02c2031143c4d29068a400304103800745c081c039801013081142400aa183e0308880707440885c1c1c008031004041c80481c80c4164028004006000940c031441350400a200c81c2165540c0f5842c9640e800700041150a03888207120b210303000d01d0b95840500c11040700302c00003000480c80c9511084804c162501140e04004943c0c410b42854000001541e103092060200a5008050100401000d820410780d9605903680320405024450131b841002d05200b80841261120711100061030b032115502c0c5007140712070381202c49581d00003c40a01b08000c1c81c2c01440d0900010745e110480c00e00f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 662568821 1250 662567571 662567579
    0xa0b09010f0f0611160303090f09050606030f132f030109051c0e0301063003021f20070203070819030f1b030801050307050108010305030d02130e131205090109 70
    0x1074040b00007403001e050b6004805c50140c0c1c60501c42050070055110307864001c1c1c90361904001c3c0502c4405039008d207040720708001c10040560707514403c50380e002210520655094070750214003425030007543d0004245140907003908000d504c0455400b48a8a440c142230400214600d0500d400d0710301c4100b009202d0303030140f0322410b03200740441c40081c45a801c525003803050090b030b40002401e4039500d03482468499000c2e004521070b82c0082d1151800180300840303602c42c2c5100343c2e5009603113031140500d032800d9a0010046511600035500031641d4803021650340a2075042e00004002154080c403801c0b0310a100b0a2000565140040741013882c3c980302d802c0c0d058594050340c606564400e948482d000422000507841c2d080c0007100385440413100d010b5907c4c0555903041101381407a12149402c0541072200380300c010400102c00100300d8100510740600541c40b080303440301194a0035a29005064400b00010812105807185428482e03900e018481040c5030072100002a9241d104881c03406001a0b60610280 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 662570071 1250 662568821 662568827
    0xf18040908090f030a082b02030103030906030b01180510110111210421051c06060e0102120906070f0b07030c030f0b010f0c150c020313050306010e0a050a140a0b09010f0f06 76
    0x107003014507d814401e821400680b15070100d070300036003044003c561a0042842501c0d418880c440c081c1100303003040d00c0890b01d1036084143c8501c0d180f103403d21860301000f22039045480f40540304025454800280a0b54241c280040c1c4070f604417640703e0003000382214944c8032100c03900d010030340620707045038403080c47c41c1c20030321f42034403c10004000609200d0100080004140f40f111006990464051b0020b0070078105240104505807a5032101d045600c105060140c003128201110100601120000e6a6210301d1411000000b04104080d000317462003410485000d4041c2c0101d010189503035000c114120000701c103001282c0c101990140060030170184058480c1c0900017088869009640c01c45824100680640c00d071520505004010b13000440c0184015a600c41050058142113000d4030309581400342c03070900000c0090906030050384481c0492103604443d84114040541100c1e9100207282445540000d17150b2000c03414042c0440710000145943c60300c4c44c503802d4503031013001b045070741e0328044c012 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 662571321 1250 662570071 662570107
    0xc0403170a02030912010b010e060a1202090d0b04050303040b0c0403030c03180e27060f130606050307320913030e100801080d080c0f18040908090f030a08 68
    0x15880100482c0407250b60711714212800c2d030f0f015070022540050b44400188440c0c0c2d51b40300d441c0500814072500720003d81150a124080c44180c0740103884200800008100041420700503040c00c0002013440103111012006502c0799011744100441502c030560010310710f214910001d800107080070100f0000a00c02e101e818101100351400c001126220b00d0349183c0f803882030304c83c246651080e1040c04c6260802001091110020501420240c9007070360340d0301d400314402018102d280d006048404c081041c9903000d10050040a811501011345507018021842032545803403034102c4c0000b50500b2804598001e901c100d4a000d000b01140c0d0b180c0c21041000f1500b5000c044090003091203400e100354880b6030760361078401c040780d840702c080d54903000b17460341487c000c079800504114a1004000c3c01284010480d41c044542c4807005a83e5003101c8100302d41c00c1e0b4029000380d840303410502058240460540503050783d01c804c495042d40000f102042564904d01c0c5030000b080603900b40302c0052030444440b0740c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 662572571 1250 662571321 662571337
    0xf170d080c09131b080f01120203150108100e010c0e0118050409060c0924125a02090301020f0705150609010b1803190303050109050c040317 62
    0x620340c10301c032400c4001003c1507070751002d020040780d07110242102100e00c0c0c44000e1500c03060b03040008050911005100300101c05001e0402c842e50300d170440c0021914100203083e90321552115001443d619984450713105d06d00307890080d041d40d081c400c1603164440103100d000004881c42c0c0f00c2e20f058220240043d5014040800c40d0503459940090009103600c2354000c0000d8030748102c1d00041c96010460016003415400d40001189000c2c0c0285101420005a24500b4810203800c1406074004a110300001501d80020803002100d16551030020306034003c0f0160a45d0340c3c080d880d01d6004100c1909062401450041100c00c0386040d071444058004994020100d0010290000d4a042461620002c803940318500c1140c142e0310081100024620031600550003c10031245c10380b0b00c4d458035032101924010302481000d40c190000c0c004089690402c01405203808142c2074000b071020504015004103000d1242390041070411000412461084007150300b40c0e036000f19a4800c05480d094503000541202d98 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 662573821 1250 662572571 662572591
    0x310051f0f080612070303050706150303050d050a06031a04030f03021312050c03010c17010603020304020f09060a03050f011508010b010f0c05030702150406020c010822031b06060f170d08 82
    0x5030070314104000b40a5840030314000e0700d0b01070f5910138510b4031004442c0071512f000600c0121510030300029901204441c0c9500506001043d1601d8000580b401014550310040c00c080c1a035003204060703000001039501c0f950003910381400c010425034050342644241981020601c4c0d1010003848500c0742050910581030161040f5000320903160701090841c0c40500860002c03641003035050040c611602c102074003415031441d00b5421424032b54086200101c11a220f14032407904c8100045460b221480b0200055070010300301c8003071860011180b0300a03c1a00c4004065050038003002c5204038050043c0c1d0007402040e9109e2410080d072290481d01d02c98210021200c2e80000c1005201598030f0810103120101e015400b0750b0340702d240101c00781c0313000d6044000e9410b11104404100c3c0140310011040e807001c020a0302c41c3c0c04111030b441d0803101c807000686c5182d072410b0903405440a122181e44510f0954034030b00c0c11042200e480300b85082262903110100ca82940c010703001c68105520521140c3e03003000c2d442c9 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 662575071 1250 662573821 662573839
    0xc02031c14070f06020d0603021c0b010b1c1b1106040203211603021e0a0b0114120615090709080d050f0409020c1011090a030210020309060310051f0f0806 68
    0x9904c410581e1301602c00200865181c42d81071041d86040c400c10343ca41e4020341d0f40d140d989400e0382d640b40103501c0e051041c100000300105891881203c130310102002210401820400030400c084440b82c10141688204000789500ea000d0400c10000201a801103400500070551070308105d424100c4511000c07401440240240040200388160441c04209544a034000e00103088005030b6001030900c2200804045d548104440d502140e00e6101f0a07042d0358075021000c00c0c1e620210045071500744401c49649180c07143e1303001c1005195507100b0780c4130614012207181c0704c01e803242d002c01c54401b403042c001c03100c030b43c4c1062903c1c041481c0243d00410560103d87c84182c189581c03601e95004070703001446021445c0e0400040d10402c203040e40b00d507524142400e00800d00708800d65020911990705404000c2c0199102815001418000c00c155881c001c0002c00d9980e882c5041010405209001d125182c01400030003900141c02e80e08030784407500c050301545c54440b54030b5004812184c900c0040c0180ba0005281 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 662576321 1250 662575071 662575073
    0xd050703020c1b0310050f040609030e2d03150f130c03030c0b0604021e09040b0910030519030c02100e03070f0e06030d090e150d030c02031c14070f 65
    0x288181c0740d0043d60003d44081111180084c1802c2c4121054000301003840d1208211550341610511900542c1100000a582c0b48900e026030b461a181c000703090340419200100920302d00c1003041216280380c03800c0d00d100c90940b80d43c20315544444032943e490040c00ea910000d90f0a10280d00c40c1ca5002c1200600c02d80800095190030a120340d4030707001130300001d81d602c04040521818502c0b0a401070800e440461070109650011000d20619685000d0114400149806142c0d1940c0001e1001c450042000311281010040b0007441c4915100803285401058105070f40c0283c980e1088840d143c260300c8505c004e50941e0b01b00b01d00c42004080c12418060540c001402d03a8904000c800d001e82400d00440c1d04150504600c4a00c040c07004003420b1007640f03c9980341c582150f0001b5080c1c120350000c4a0001c80d6116003846c817030311020010a440c2c00010043d619018141c1c032849000748075000350190390421442c860400000c40b001400d0300d000c10b40340e8201d101042c0d00c100081003030a0082d141d9070000811 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 662577571 1250 662576321 662576323
    0x2060f0f042d0e06060a2a03021603170307030e060f060a050d02060a030e0a05010e0d082d0702010213350607030207031e08010603051503030d050703020c 68
    0x301e40c1000e4070b110100702800007840c203403410a40360642e0011125210740d1509486080e03c0400400c0e050040e100810900407032802480c558140000b9480c2c46032084459107900304c01c6456080f41a00180f18030051101c054592010350420390341c00091220b80017101070b40c0704106d54405401003080607a035981003609040180180760045000c0d03405880c550910f1000c1000e0303414980c000f10300c100c0b0700910782c1c0016a1208200c40300c25200d4180803076890300c039030055420078440c09409456542440740481d1604d00200c0c0304880009030340c0f00e0000b42d031549a100400024400c141210002c40c4891540c81030034000d01c1c0c29031040300340c40054a021100c0c04010a961816400300d80d61048001210082460316140c0140080307504204440304041e050b40d4580d540f1000c2d102e84107059001900c401418810098406044034404a2000380c1008910040c01403400b4451080004d00e842d010901c0400c1e02d40304030003400c00090041d400d0940c3c0d210014010706020780920b06142d4200080014410 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 662578821 1250 662577571 662577577
    0x70807030809060a0605010e04050901150608010f090c1704050304050414060f01020d1b02151b0609010e100209040609061205060f06011d0103060f0b09040f02031302060f0f 76
    0x44030741d0300c0140034248031198520303040d0054600e0301280d06000007030042c7e9900181c1c40180200c11a004113103038549412071401170010a0004510380700301000455101d40007802241240c074078840400201c2d98170382010088400500d0141d0000704481840100740d04400100d80c1c01500440a4a00e003d54410006040302d948030440300e808010b46003007200910f001520505a44800e0024241d01706103404010070003c80b5034600218044490354540540d103410114258030507020407503956070800c411008418401c840c014407014410300b0300055040006015410141045030001c00111f40303c209100044e40104030070b143c000c3e64440002403800308500454008119420300d0707208800365400c040d42480c1004000482d5181000c050000e566400034843d00b24100b00700e10320003d0a40c1100403401b5240380d60001c403091480f0100402c4006249005180e40101141c08110b1f841a0300001c40581c0070031a07440c4080520f400351030016090a46c004c041d4050150301d42450302c1e94492804c04e89030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 662580071 1250 662578821 662578823
    0x1051b0a121d070803040f1502030705010c0c120c0503040902090402090d1a0c0408100c020f0a0b01171b040e03130605030105040b0f030c040c030e01050414060f01121205070807 78
    0x80030b9000d0301c181c0c503602406007402902040010b10300d0103042524003c0803200f2071168813000c0b04400080c00165109000b03440c540e0740c0c000000c4c0502c10505600410f103202c0d946054403203074622101d50000340c0c02100c01a079030641c0718018500340ba190801020007900701540322604950200020f00f425681d44264001d800d00c9030300c1540782d15001900c4070000c540010501030b40444108001c2c81f55502c0006c3ca400002e05607040421181c0305008220b081101c0c80202540620402c2008401c1041c550a03190582c7c42c1c0b000940802c014042100d41da031034001c1800d10040c212103181350401c1c01d140c0c01003041b9422500480c0d00d041c010b40c080c040340f400350345c2c4450001400400140143d20345801031440401040b01e448001c211140700203a22455a803507442e12a5555400240f0118040e0300107034140858007008100c1840c10b801c100301c42074050740007083c0d02d008407400100b0001111040c28103035582401c10100120680d034583d036668584048000602400380580c000103200a070003800d200b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 662581321 1250 662580071 662580101
    0x9140c090a182304030c020405060114030405060f091212040c0f06020127020105190e1801090f1b0f03090b13030e010201020414060d0b12030a0905010201051b0a12 72
    0x1030f00c40010a003041580e41c1039a800652a22041c40007007a07000c6c4031244e040780c0441d4002041e440d180010f031102c40c4041ca206050002c04010001845004543c05128100941206106030744080c822a181c6404d9030384002442c0040c00030028001c04c801e5846d9109104540c2d50b904552900340303401c540f0b043d6074462030050707444650b602481d82c81c182180034142500142005c0d6040c031b5500203002c9005408500c0d80e651252001d244c1c030079103c4d07140c841009101902c464200f10303158507800b40340c0d5824001c80e42d582e42450203017006000b4520880c1c1d01c0700450000c610f80354020150494422600150103000c1540300c502c00d40c04130306640c80c418002c990b0100341c0c001c1800e081c9005440c0038603040000b0306591040c0410400303038080441c035001b005402c03140d45549500364000304004000741a00d0b640c012202c552100c0030841c00000600c1c401801c0d032203a000b40d40ea100012400da03042181c1e200e0b03000c1110f0091107840c05089024110701480ca0034450003c103001c100c0a4103e454401003c41170b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 662582571 1250 662581321 662581331
    0xd0207140c0612010b0a0309080d020406030624051c0c0906080f0912070212070303020604230c010305060409060e070f140907051606091b09140c090a18 67
    0x8a41000c10190301c1500d4251030140c18100031243d0541e4440c0148255210088000741c0c0c0c4580074403e0b840300c11620341c804011600d8075440007022000b500180105400b0900d08240400e0880b03642000d030b60403407a180c140010140e40110304030754503000038444020035101c00154078442c180c0e50061440307005090759020080307460824020003014002d030a0741c01d000300f4038090100c07071000401d40884200207400603d54a00403072021441c00a043d0500b078046014142c1c004c410154046003c81c0140c2c0642000350240841311107442c1d0852400681001a03441003a540d080c9502070b0300306550040300104000b402940c1707915140c2c03d543c030091000c15a41c000780300521124030303043d1003003024200000d031416401841102040e01e0744000307070400041c82000304244240403a01500401c0c0c060f4402c006002001171440c04090304000c40c4011403442d040d040d404610b844580c42014003003110b50000c1c404075241d82684117116448140c034150004e558050108100387c4030401008441e6030307500000341c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 662583821 1250 662582571 662582603
    0x11030a171201060c031d011412070201050702030a0503060f01091707030b101a0f1903060302031509060f06030c1c0210031503080a09090603080705011103100306020706020d0207 78
    0x20400d20140c10440500c500350441340e01003a80440c0d180f0048560400b4617001041000050f5564400550814a0700ca00040c1850808a000d03802d54010051900284a10780320043c05907141c3c0103040e580c20000d01d06000040c118907010035208041c180c107051041c0b00c1d503154020040c00da160b00c503040107503a01c0304204004214018680b25448a10340c80040052410550080010312014540c01400580032401c03c80c8408034100b111111502000c800c00e840103042e00181c003401c1c0501c42a8401d01604c0c42821050014031a40362141866902415031542d40240780003a50034003403e8190503200d101c0d0b401d000d54a03205422462283c81d52030412581002d8070401002030ba02c0580700041504215241001c541c0c410100c00907280c1c401460b68032100c65200c1107507070402c542d101a89050818100005008800300244840ca009100074070003030078841c078500982d110a0300c440703245610805040001c90721070341c05010201c2c070400c03000d0700c0e00494584d91804d9030040e0704180c64001040c59004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 662585071 1250 662583821 662583847
    0x527030304022806120b0d03170105101b030c020919050c090303040e0a09120e030f060c1e21090708010b0f04022a03180603090a11030a17 61
    0x2583d40c91843d18200c07815401410018410301491142e9400d01207841840b04000c25550481c040c1580c004e0042840c0740990304004240d02105a800d50103004500004546810300024280342200580c80340c1190724070013028140b091011f81c800b41e040000c10400000180c0c0ca101c00607018114000340070074000005071511046450280c041d1604580c00c10034020b00d524080169411259118040016a6510095200a020030080040445400d10501c44600e50400000d0303106c088160110b8081c0341d00e400d40581e40c2c0388180ca0365812403a06110202107210407019140c02e50121640540c10320342c25032085000403c0034807040604070604820803020000c00c221100081083c803000340030010f242d20206180d17800008509012380e40015041881603545c520074801207107402985507083c11001a40e0340c8a03005250742c0c80340501441070210441c074054007030301d0088030b6001c09444050100c2e520441203485101c4090341600a002a04011540b01806401543c107070300080e07907607000d1040640d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 662586321 1250 662585071 662585089
    0xb010c201009150e031c14030703050106031803020703021011120307110d0504090b0f0612070908010e0c120c150d0f06061b1e110a060905090406052703030402 70
    0x11008100105071050301a1781c00107812104200501c110302c4002c100090110342c154460a8041400f480000500040399410751045040b00d20302e07a0100192103000c0c0095400780d040c48400360041e48207240c184098a409102407034801d80781c3c1040c3d005154103c00e01400c102c014000c6a080c0100842000384058201003d4075010892402074585850020300180c0140268082c624040b551003a444007aa200c200c058500c80c800100080c0d1907a40e600c5040001e50707411940e900c005059903070001003860b0f05000d14460f4519580191102400c003c080c0f00356080d411001807039920424504500540b110410801d1302104064569600d0142d06100010340b00100c0c0a403580c0b5142c0542040030176800b4164443c0f00b103090740f0323486000c0114200201c0c0b804584041111003800d03070740ca81081140303100c0a0f1954607000d40307004407115513034401600c8414007842a5504204d031140060300203a015803015a1207112008607100e50008001030344100303101451200c0b1103600000c00d000940c5000012 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 662587571 1250 662586321 662586359
    0x3030c110108040503030c090102030d050a200309030f07020a0302040c0504031716031809151e032301110316120c0207140102030f19120b010c201009 66
    0xb01015040a03034900c0d0b968130009021601c0c040001c2411112a84240112007840b141c0300f0041c041400c6c40719150000b00018051a1841c810144e1040070658080f01030b640305401840113542013070001d10f000240e95001e4802240c2c400c5002901200603031b40c512034013130070810580e1290f881e10b0035490107166900d0380d40b01c0361610f0b0100f800300700c8052000d500f14482c62545440d140408101c1d0111403480d612113031f000b1513209401c00004d4044070104a60f0602252182d00d0b514100b414903541c580030101c0c2600010f0700c100303c5c00c002d0681044840192040c401c1e19a400001c08c80c260044801d03103a041074414810301001b015580403c582e101042c082ca072034004034108040b5021250203940e8044511a00a1200740400d10100c20380c0240140c61195035140b400680e02c2c03901011100c0780101404140d804151100d0711415002c40520544080c03041c10307110005485441d403285c00c00c00f00e5102614020032018044402035443d2804001d03900c80450311810011810305c94080388003801c0000b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 662588821 1250 662587571 662587577
    0x3080901021b0d0201110319021605011b03031d0307060506040501091814010e030c0d0807230325020c04060605070c140a0b040b09210d11100603030c1101 68
    0xb0071196540f819a000c0b1683c0c2400d02d00398201c0080406803e50040103400c1c0d071440f500030002c54a150300400c10103108503404c01407426060b2600e0040d512452040c00c04502e24000080600c0064017a6000400e00384561282c8440c0040c81001c0903c0c40e40000c50403511551914184030250400d03000b880d01504240d0070a00061400c0d80204c64049101400a840480b07a00c0c115a40100c003035021648081c9058140c6e6134074012949802c6c1e440034070340e940100140d47c41d0000b9a80500c15440001c1c20388a000300160202e02604106030590809800813200c800720411854642d44043c4940c403a5906907006000211000020402141d01d0f44c0c0c4400140a0f08211031800500602e6083d801d89401c5c080100810754074a020901c004c84d280c011040d58000014003103410305481c4080c0881840440c1c12907880e10407e007140840382d031144480c0380c03298803400000e50110300401611111703108210844560040502d0034606aa40aa2081d000704445a00761414400d410f00098040c500a00b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 662589928 1107 662588821 662588863
    0x15051504030c0e060102031c060b070f051b130e0a02030304080f100b130b0f0a1706011a0304120e1e01080901060f1418010308090102 59
    0x602003642c40804081c03000511038100404548100070680c050f50402405940500449040c1d5150b03072803c3d46c4410000c00c1d00d4800d44068225540a0200c0725881d89150400c9810900c86c02d90307400d68512001d030701c04125180e00301c4584008405020004d0024540f40d811810710025500003517250100180008504d0000110001400c0c103903001e13034040030207165150301100c146031100c6421009103040315803961301c154010340011001814500f03040c2006e0b40042c184508a82000d44061a1a55038845482042103424050001d01c50200c08050141c4c0920b080b034040244001c142d2864500c81c0d940440c130400f41c06019030f80141a00031640c039403c2c01d000c0300c841e900030741600003506000051110b182c14041c41c0300300e959107104010501c0c24564403c29005021000c0c5400008000442201c01c20641585000303500816a040d19030016000084c20190000d522602d241159 = true := by decide +kernel

theorem cover : BRFrame.Cov 662410071 662589928 := by
  have h0 := BRFrame.cov_init 662410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 662410071 ≤ n) (h2 : n < 662589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
