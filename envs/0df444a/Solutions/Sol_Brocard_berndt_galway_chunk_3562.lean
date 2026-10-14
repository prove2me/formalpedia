-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3562
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:01:05.944381+00:00
-- url     : https://prove2.me/submissions/8622dbb9-8b8d-4ab3-82b7-4fb7ad18f64b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 640467625 ≤ n < 640647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 640468875 1250 640467625 640467629
    0x60b2206080a0902030a122c22090c03080c060f0906240a08010c08010f030f150f0603050c13110d091416050406092a110f071401020601 60
    0xd000401041445440740c0200d100b0710300040480352282c0c2c0503100d058440744590050004541c141c50001c000c220301417003c400c10000d016421400d0234025001c90204050b4045d201201070f00c01544802503145540030307100d00c503004103035501ca1540360328060109034482620b80f5800d203d45000144000c203000c640f14450500040685216102c800003603d03003044c03003e1400424244c014101030b4548035011844018000381c40045080880c102c800b82ca00001038004407500c114501c000d0000c1000100a044020303485941d000e00004a8500b600042618040003514242490000000e00a00042d8030112200c01c8526000102c0420000400c039605070424142c2d0b20341c14800c000d010941c90340040344483c00ba1010701c0b0301c80d60000c1414208444a24000d00504044e8000c1c8001d06047c424030b03024141c2d00c0010070800d9116000c035042c01c1d00807450409803a142007a0540386d284100c1050026003241c10858803804c01802000c1c1d21102d05000c0d445880f10036048180196100180e0241 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 640470125 1250 640468875 640468877
    0x411030628061215051e0412050c1009020108090307031b020d05030d0c08060d03080a0b2d2407030e04090209040303051008071409090a06060b2206 65
    0x2200d409001c261090058280300e210300312580e4000c000382d03241d01154226080391049940ca2030028100448a0803107030701610718000b40003424041400b4420201c00313541c01a03084810b94070a1501450111003e110700da186814500540d65800d1849820f60007000c0014405d8966001c55660505c01781da0f6401346c07100180014110342400e842d001d44859082800c2400502200701c444820f4035a24990343c030214404003035564800d1810f004542c80000250000c80413074111540d9140e50324020320603100941b180c52055580c0c41c45100e00e035200c840c0c048140ba2244514401c81c070f000b40700d00e01da801c1c2e049040c500485194400040e5011001000d007000d40002800a042c0052034404603101b8481e58012034000f5544c070982400b6a0b9400b103000e11491203950007142d540f502c0084a0401c441c00c4d0b000d000c060703000d15000d1100d0352040c00c0f0080d540c0c6096400c020156a0b01040302d00d0b040d0001005020715103840340101d203190840d4010000c06028a07804a291118283e46032040510381c4070b084 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 640471375 1250 640470125 640470151
    0x9080c0607081b0d022b060b161b031e030e0a0807060c030207030b16020d020a0203100c1e020102090a0f0e0f13050607030b130e072c01060804110306 66
    0x400c045502d5001d480c2c0900807183c010300b8940da440305d43c9000b005d00c12000341c401e21100f8201001b40114000d0030040c00c01038451504051060301c04240040f48044000d100b03280411089001c090303c0c020403001544c1296040352000101d01503008245000300c41a00010307506c0302402207500f0b21642900407515014000d10041d440c1c4001101e00c52090401182180203010700007000c41c0034010801e0260b003841041c1c8420240c001780180c58501048104000e54104034503c5015035800314180d05260358001d004102411280e50844813003401c940c2d809020b101581c5407082c0694154040d2a1039001920031855007501c0f0717640001403002c54865284061070a034001140b10fa4013803001030f04102c02c0001ca01c01041c4c6542c4150a002c0102c548000082e555003c04c055850117003060204400d4000080202c014454666526407005000740001c0c01e0801c0d100c0020007001041e4400d13241c1c80c600b040442035071585030003442c808040e0750030f441e00c0d402c580d1404c1081c07401140c018010b181d800540 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 640472625 1250 640471375 640471411
    0x11040302040c090807060207180c0c021e190801050609091f020d020c0c0a09090b04320a121d04050a0209060d050a0e010c050f13050409080c060708 65
    0x1502e0404004020094a20800181d00c1c0c410400c00380a095540c0150040703034100006050300d04420b42c54604140c3c20301d004c241c0c0385900f042080d80d1164059401808076200381c04106068543c4000c01504100e64201c00f807420600008030b4419241c020b002444551282400c00801d04016a08114075030405140d40d4400100b0010310f10440703411110160816200b40101e03001c90f0401c920107061b641110350450309a103020a107207005004021010005400c8949524180620003000180070030882001080135400d0204d05640207141c02040401ca4000240303401d03103a001e00318007201d0740d01d800c851082945004412103c0301760361850004070114801c004210142c0400341410840903805c100a4007561103000003030243c480e2450000c5013604100d1440300460780c03a01e00610701a403500c49400d2100360b01004495024144c01a415250308100a404c80c1c841c18a900103039100340360040000401540c4000340c0503490314002501c0a070340d18500151400c1d481141c0d030b0f402480a111031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 640473875 1250 640472625 640472629
    0x30509120309060c03280f0f0501120b060a09180507050603040f02210607020c1203090a030803072c03060703140105012105010b0403150204081b0d020a0e071211040302 74
    0x14546c00302d2800010100c500160200c1ca000c210214090610241c47c1e4000ba284003815020b1603016003183c030302c10080c4c0e601d41401d60082d840d030024010030180e071034004102d1969030440100090300350064100485020421300c540c42c80907658046456000b4a9000103081c40c00c101601d00c070700e4102d1851000f01c2c004c0e40c01c00401094480e200b0300c01810b211303110840c000040204a1190381c0c0c1c4d400034820844a07804100320f400341c01100442a60003000f420125842e10000d85080329401340303855840c1d446145080d6034a10300d044c500e485000c0d0707811089400c1c885000711101262016019146581c503460001c81c10707943c07100b0100100e50f0f1010010842940300d242400680441c04103000081c0b4541800c1c1d00070b9520030f03800301d030803502c2c01308080c0140801e104001185140503a0114901854407030f1aa031a40e4008032140c0d0100c0b0403139014809511414910380b11503034006c180d8100d843e110141c6000c8070009891040000e1488940900b54508034411014680803501400c1d085c04d00e5542 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 640475125 1250 640473875 640473877
    0x30519050a1407020705190b1e0f0d0f06050d0f080c0a0b10080d020d09050409030903060e100b060702130b01410f07170415030509120309060c 63
    0x1040121003a600d481410800d502410a075014400d15400345c00050303d003008000060003032800000d0b003040c3c1650100305040c040000c0303410043c85010700c4600030043d003c8941260054513480701003080005213460059035268042a00c003a0070750001c125280c1c0f1402446402d0340d0000c001840490303200100030101d45894041c0024000d5101143c0517000c60f42d40c2c900c041d81e000d4800c000c0c00c403a980c0081c40075000c207008040000304d10780300510f05500c1c0702d40d008010340031030f10402d80250340c0c82000006040c49020f00300090341c0c11150a0245071000c00b1055950508005405600c62906561240385d04c0e228046074240f070307001024000000d0042c202040148002800e450502031082005000340300070315041500000d000d44480c0e03000d44400629001042098003960070800c1c2084400b80e01c02665040da41e80035001100440a1030610390391104510454010303001100212642c05a02985908410300c00c1d080b80040d121284c02ca40008001c5000964a490740d0f42c00280000b0680e40c0248 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 640476375 1250 640475125 640475131
    0xd06090b07361206330e130b0f190c171e0903030108010b01050310060516080c010225020904031d09070309020108160915140c01060305070603051905 66
    0x100b0b40b442560754403450358001c5807540780104c80b8207071503503070705100c041421030030900071700070a45060445000c64984202685003402000c1c6140e051001081c1c86250604030560030300e40c84903040c0198200740d940146000c1040b982180712844225070300010340210300030040d5840c0da9441d1030080358025001070044410040410101100442d80c0e0b4070000940000c0b070303000741a000f014581c0c9504000b204d03801e503024810800e043c45020000e0080c1501c0360400801100c08030718146403511500750309900c0b201c15078540900b0200d8040f8005030342d800190300801e051000d01c0c0380b5541c480c1030340d004c50f04225510140030354003101000003d004039000e00003200c00400c801c00d1030741c60480440000380c104030041d50740500095607204403000310b50300942c17802c0d04502200041c0c0304c0c1031100d030b80050420a43c1d00480181d40107140a00440c82e00550b0034003507502e900702035641c4800d1f00c044864002c003e035100548103407241036000540e0034000e2040e14094441040e14040007009400d030080503040107 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 640477625 1250 640476375 640476467
    0x150306060a0e2a36030705060903010213150f1d04021b03040308040f0b1303170c0a14012004151b0318050315061e0d06090b07 56
    0x80745403500c100f0400c014280106915440602c0c21029520b00c024884406403424009900c4590140c69903000070304901200d00845240341c3c0c0e11307a000003003030180c0241100030355103024003800881c2070508520780850652150b41e5080c440469088201d07540c0e00400d6088801c40c00301901c100842c00c150b00244040006101203401103040742800c0e0303103140c2c016801a1401d081c0410306000d00180081d000d401089004042030508286902c10401c00c84d052000824030300c2041a00d4507003070303842416540c6881490085c0c5400078500c0c14a030134051a46402d000055280940c400d071144410b0910207142d40350802c015013004c1c1425100d442101d201400d11341800305800e400d0f54124581d18402c034000c0d100755a100702069104140341c00d51070003030700300d14402d4100115196410464a484a5000d60101d500d8014071686500140070300c1c0e43c070f40e000b81d0403002601c6102c0070b2000e180c1020600303611a409103003695840c0b01c01110350400c00d0091520141240e141ca81501d5104141c07103c0800c02 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 640478875 1250 640477625 640477681
    0x60b010c02060a0504090606050406020c190f0303020705040e0102030f0408070201091a09100504060507032102040608040c08010902061902120c2401031106031e150306060a0e 77
    0x4a50006081c039008595243c000890020b010300591845000d4003000340400c0c1082410207003003200180d08d8003811041c4902500d00345920007000c0c009494070758001c001070030076200d00b103407a42802901d503c11401010b0180b410000703c00e503841014405c4a1040080780c2035141c103078499542e45881948103a00680c108050908007207085090600300c40c02c911030514a213aa54200c400600c40d20945490810301031000c00c0c00704108481d04101191801070307142c6440700c902c440c0d04103c00d21300416884113090b264404940814000d030003580c03090080d070003421011240360f610801d07242600d54005000f03402c81014007442d5030800086100d000c00010500660301160540e1124400c4c94006000c8081c41d640a158103018140c0c42058030800070200c06001503056055880329842d541c078400340280100000070006580258404500d50b24895040a6136200d0800c4a039038540202e080380301034828040c8c50049010b62070403101000440e040c0513070654850b40c0d80320070400e040714025004800482 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 640480125 1250 640478875 640478897
    0x108070e0916110601030503040501030e01020f180a0b0702101b0b090304150305130305071b0e1608040f02010e0f030304080f19030519031404060b01020c011803060b01 74
    0x1507086040c03803254000c240c0c81002c500d03000c00d0042800c00000324808180d000700c00180301040e0044100c8090b0f84080c20040f5144072403000d00740c024811010b8141180c8400b00302c80b84015481e05542407558011188800007644500e4401c519203d000c000035030104d0030b1181d101500707000b500860600d8003012440c40d03000380552904035909004882e1010300b600002420300504503403603040968000e1ba450100503602d00b07607c0c4005100002035000d014450702042c40c0c4c0070826150132081804112200c01c9100c2c6545400c40d42c102c080545049051a0f1082c240606451103900c40500c1180c000544409098041c2c0043d0380c065401e0910030b4010200d07131003e501d030352410401003009011810040c03d80b290711140140c00c0401c03042c1d00b034030030324003125841c00800d9012064030815111031040c0720f5040c010010076401810406900050740c042c01d810402400140d030300c0001d194501b07800756680010814011102e91103542075a100d0b48441e0502400032802c0381c1d118280c3e581060400d0320300c1c08 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 640481375 1250 640480125 640480129
    0x609030604030e03060c1201030b060a03350909040323070813050a0503030d020a0306050d080904050121081812030a0207080703080d0506032b081807050108070e 71
    0x1045a090b000724483d901e12452600b0b003040410307440a0090706081c02d00c0c2095282d141035010602c8040c0800c055403000c200140d40d600a41c44c021580820300e0b0701d110f10f00e449800000910904804c0c40c00840b1191000d168440d80c0807140410740081c040365850340d50365010348a030b0b20649040440b44030b20041c0200441181d50051408a000b14807060b120711720784079003600c076030f0700e1307820490141c400c3c030340104000c0d20000300341c0d003080c5980709016890704107034401280104100e60006500024000c0c20000780600d00006021401003503078180b040f41c0c0c8a404049564134580820528042800045030118040401620b031480e04c1b9010103280669207000034421044010400080b5080020170700c002503010008040148540300103402001e00d07580b17803181f5a00892142d000381c00e445000140c501c1c0d4042c44081e200c0581100340381f420501d52040c1c40741205c000e0400c0b40c04030b900080418942c4018110f0062183d41d5100144000c2e410100110b8424401411241c18800300e55140012a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 640482625 1250 640481375 640481383
    0xa12110a020402030a0b1e0f1e04050c03040213110a120608061008070602190b0601022b09060c0f170409060b0d0b01112d15060f062502060903 63
    0x5c0d2158000110703800111600b00441407403020212041803180220803191070301c4441c00c0692242c811100803450070b02c0343e01150314001c030515401e5171140c60141000f8040c2030741000340d40a14001d030341098052111420100031204000700a110501d401e1180046142c82021290301d40d094508000c00d2843d81c0b41030b1645410300c188e030104070700d01004e40d0a1040040400c10f8000811192000b40000010211441a00101818050800321a07140002c105074000c006160800c80742000311300311203101c070559a085210a05420340055254440012100e106003071040d24a50843d0903c130b0929803a6995010f02c80d8501214101c0382003d200c0001d1003103061140c8002020324200180d9074079034410000c42101c8400c0754007410f001f441c50802e8495034001844a580000c8401c2030440340b00c2c00078800c19951188403110010340f10b080d030f41030400d0b0744488503680540c00903110308246031000000c00640c2e000d5215140922041c0c18038007000300708401040111a40003034180351900c940328010a0130 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 640483875 1250 640482625 640482631
    0xf0610081b0c150a11120a05060a0518150d080912011407090e0601030614101413030b01050a05031011070c0e091516030b040f05040b070807020a12110a02040203 71
    0xc0744441420041000a80d0081101342410001d01902d4a140913051800c01b00002d081c00003010341d02c100013400c81d141d2501c0c4030060300c001412819482802d003910103c41c8000c03588500319030b20104c44003d2605150105824465201030440c1c03c010800b03091001c5c44048001e4034820390740f01e128a803110308031028100d00405490780d0b91803005080c0040b4482003c0094415070406280541c10000041c02c600410010042100c429410b00c071440c1007210901d09801c09007041c0e010014460450030b1141110343c045a12852010b001681d80340c1c1000401821072140d19010b401c9061030303007150030055201c0700e07d00c0d0075103903141c0c1042816114401c4054a0340c200c221003201e841e0900c284803001300901480050884030f00440b5142c480700d550506651040a602803513200e10414900e0760ba03d4001650395046140b0030030080c6440d040c010407504c001c1c0c1d50700020032240c1012802e001c2c804107a4859240c1c000034003403140007024104072181c080360014501e03513029410045006039598001540 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 640485125 1250 640483875 640483903
    0x2310270c030c061b061508060c0409050a02040b1909030b0a0e0606030c100c022d010807020346020708070501181208070803040b0f0610081b0c 63
    0xd8403419071034281c1021100740c0048003406484a06903403490707100100401c05560100c00403640d400300d0411144140c03501d0b0441070440c02101c08000c1c041081001070300451b4140c120500c455140c40a29030201d01c0380c0e0042c0c0d00c800000700081121111400700b00816440c41c0c1c506000c1b11940e9468504046505880034550552660843c10b01504100045904010704034041e080c9800f1480c0003414265200217810180008252680305643c0c4008103400442c6000c0389800c41d01c00b1031840e0041c0c0c10403100701103000c40d40741c0e008203181d03510000c161134401e82007003902d00d20b01304880e2003d07980500c00f4190b00d00291103401380d101c5004100b400184c0c402181d4008003107050030008000e00f0300c0328079000281082040418914103a12031003000341140d000302402203160540f4100001f05204200004c4d0034404000248801c0045203104030f0310620f118800148203455200401900d15010000c1e100040c3c2a2404107201804907403030000031805034000c061410003400c1010381080c40c00340c031110b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 640486375 1250 640485125 640485143
    0x2040e04030e1c050319110a03210908071a0408070f021201020d1506020a1a0a180308070905010318140f250504020316030209130216231027 62
    0x3aa442100403402400c01b0420308000d0800c1800d8040340d81c3d0b42321000009810803c00030300001c14064401407910f200440010284865002c50811607145d40c0318103011a41904503440d140b09142c1b010010500680e40031810503d0304429031a040d60050549609a81c00700e205c051a0360044800d200404d10010407940c0402d602d41200942c1003041e40e981c5c8240f0540d08210400d40000d00080716404141d00f404400000940f101e503d208001c00342000400842c010302c0071180103040d08a16218895403031550740c24440f686a0380114155181813100b081038501c800310b102c0c0000e15070804004880640d03411106030106083c0380d58500b034000c038074007411003c000d40a00303154000345c0b030050094601903030190b10710f0920180c1e5200c500008946030742099404075800c452a5540300b8503a1500c01307a0034056403683d070824460502d212880504440003507112010702840c0110341e402038411010000541246402c0030b1540000d450050421030107080302484484030a12101900580c3d02c0c041c00c801 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 640487625 1250 640486375 640486387
    0x3140a0b09060a05010516110a0605030103050601050301361704090e0c06120c121509090d02060a0213080a03050301061821080c0d031e02040e04030e1c0503 69
    0x40008020042e1816000780d41c42502030000da60860121803c44403050140b14080130281044000f2002030702603d070f8007200c1000006400b42e44070020314140c1c2d0040040e1401640d8810416007250354103c020f180c100f20391080b0307900e00c0308802040001010704881494039900076071360f014904e281c0640800038125000c2800e001c0882c00c1e205480c1d03041e540c07400800080c200e00300000c116004242024103030300340d20000201c80002e88415a00c04c1a00600341c0080ba05122001c4001040000481030040c024400058080d01e400501d11120180e590041c0880b5241ca81e0350300041c1d8011440000e140b50050000614048100500162a4080d47c1d40a85039414003000074024515002a050f0352100c1003000c5c825910002c4460f8000a8103040c616060440e81c034145005005d424a4a20725018941d0314555040d0107400100f44484030a03181594002161805d10072030049000c1c09055a66030300c00140080c3c001e032812210b8034002080704651102515202030003041c4000200d407560400310302d03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 640488875 1250 640487625 640487629
    0x30601090c0f0212030a1508060702012003270304050d060204031b0e0c03130807050c0109091a0405070203090d0c050117060607020d03090f030503030906011d010605090103140a0b 79
    0x2c088482a5201410301c2030004081c0c00713981e000c00742001d1032982d591503956400c20300c280e1050000707014003002d0b80c1d010301c0c020b1300c068028540354004000011742900d081602d90001802c80b84109016442005100d121000d92000440d02c4100000c41d03110400000c981a6601801d0658140c85800003580d500d0840c0b4181c443c10001451119940245072401e004a09401d45260340c001d00d1440d0141c2c880e030301c051044016140c5540003400c03140d00010b40005010b00130032841101c00c0c080e01c81c40581e545d02c1010f02d04642c1450200450f8a03a03040c0c0c02c60f014039090b0080e03a0001c0d000d104903402c00c1d018100007044445120001c0b6620711201004014035600501034180742100c198004c1c0b02e80c44c01c4004104544248003000b44a05030710080041014001c41108014005c800301040f846c0380c40b89480c0d0380c0e07540240d0340c0401078440d1400000da444403080000700000040301882103182d10b4035506541541040004078141a105d0a9034250407411015070b501c5840c815801049a1441a00f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 640490125 1250 640488875 640488887
    0xd0308041e0b0a0f0612140c0a08010b010311030601021b0a15110c032116060507030e160501021207060f110403150e0d0e0f090103060c1206031104020c010b030601090c 74
    0x3082c124040d0a02004000001120040c01b4402e40c111805910300901c40e14450f013010000d05031a944480120000b04601205504c0030b204500280c0f0f0800c0b0303000180021005501084074400e00592101c0085500111001e0940b00003920140480d85410f460b5460701c4400342c4100c105400080814200c0b1440100401c813a684002c4250007604907219400d0300f404080341c1014450b00383c1c0600103a840754078005007610350340d015000002040141000d03200100944104410403c03e84a280b00003180014100c240508440c41600148800c41e00b15440000b1600008801e40701c603a5152480203101005000d085450700343c02c407600f42e4071802d620305280c100c410440c0d504609454264001008000080c01c00b40e00c40003030410075036402c01d0400050741c0301401c4102640005511f8000400c000e1b10b504100d007041c000d900c40c8010445d081044c24100c8200b48005403c50400d4151990582070a0b40249040b1043e0400856041c6801000c285408000e178082d00700d0540c0c50b020300c44c05681c050307 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 640491375 1250 640490125 640490141
    0x30e013c090f021f020a03051b0d120f1b1416032d0207050906031e0303070e060a050f0d020d0e06250507060e071a07050d0e0d0308041e0b0a 62
    0x250068003130802c1603009507038071151a00201881000252022069020494071100410314002c40d4074115000f80002c1908848400c24144142400300d420001c0d00340d0b0160410f108103041c0312101d9004040003c540c0750241c16551a0500c0e0f0400040d514060b030315441d00d442074020f8031411810782c0d0090080ea9102500c03d00c044020844920410b40c56030b0104100007250400c40310340119840e100c00083c14940d0168400384007504545851000007400300141d8824040c1e9142c4102d010180c5041c00098402d0140c8040021820007095800080781000f07010031100e5200e0050402c0c20720002c84040720303a07295031b488a5901003410442c11080c42480d880e540150141a0a618850180b0150850154140040c00c007074075556103000c0c03d8020881c0000070710102644851121841d440d00c1c0c00f50380100380c260341c14000c405000c2d61090061030944403051015213000f80c007a10a8404851050002d042181d20782051440e41030754404021000c0c088600034000f01303205041184011007217407505 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 640492625 1250 640491375 640491409
    0x1030818060316111c020105010e0603030a050304060f110a020f1b03210706022a070b1209011514031b03030a0818030a0906030e013c090f02 62
    0xb002004000c5010741c00d90141c0240b142059844015490740d5181080020300f06031100310030400c42094041d03415045181224401d1039020744540300c0009164491040c1a450002700740c0c10001304000480980c000481c610790b0300b10000e407143e4007100c250440d41c0702e001707900010b81c0301c40b040c4070316804240420440c1d41040c00b1641015110400072a40341c029201905d038a0000409007200030030380c220b0071615401d038811011541e89421295010f028030a4550610280c050400885021a0009510b40c04e40300401681810f142c1640300303c0401107002083d014141d52100d0b004004c2111085402024280906078401c04900d641d06042c90848085e0954042c0b40e00c6581245040c1c50100403030b210981c5510707003091a5507540300d00042c4500b018040036010b00c0001000d4009640c020a0740c0c0984116950610052a40841203800c0e140421801c0500da689407580d10111101140c85108a000c1100007201044080111200300c40c0f03c1e400c15a20000337400144811490722140341c02075a204 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 640493875 1250 640492625 640492627
    0xb03150901030209010b1b0307030305101a1614060109052e03080912070b030a050109050603070b0a0e04020412020307170d0302130806100f0902090112050a0204030b0103081806 78
    0x50b64000828802c4180f10704080b481c0b00040c40920007407000aa49401300c0200c08881ea15085460300400412080300e080709110004d20010072a040100c2e00400494040d0610900b0401c411201c0103455042160440f49500007a0401180d841c040c40700d54001c00407118001450320b444071078866a1300040c0b10042e1088409540e485805070f80c180300c102940e4000d6041600c3d10388a4001c174081e005050044401441a550005a401c1200000b1403140b044100d05000303036643e410401c0146c517016a00c059054000040500c5950b070b40202a040c00d003c940307416402e552100012908030b0b8085e420450311001070041e11002d40c20100403600040191880011f8a52040410292603140c0e0441c10700c100f640005041e8081c4c00c8411440700604441829100c45080c0092412284000c6201c0e21111a5540b0300010fa6179601d842510008030040e1100219605540384c0140103200090042c207a082d401c1c0800301c0401c07480c4500c00d010310310540313043d035492040c1005001000025241c107441a00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 640495125 1250 640493875 640493879
    0x1080709090f080306150c1c0c0302300a0801140303040e070c0807061d150c0a11070e0c041802040501090b0706110a020724080f0703060801060b03150901 68
    0x684460001d242c1900540500e0b143d444110001d000c1c00e4081d0441200c0410125081c448108041541c01c081c0d0204102600310260004055030610800c413400f4000d6004050009030407810b00c620000101080f5400c80c0040e40507600311507003a0040a85100009c5650300103005100008401c941c032420110000c6042c14a40889190906070003050b88080121503042601040340a5080e06d41c101d0b4010024000e01c1110000c100d5101300e503488030f00d528030814802000305468410a6405800c180703201910304101201e0a80b002c00012741d21014610545400141c19091200c81502900d40c0c1c10340c06039124070b0440c6020141e610341c0605048103104000410080e1b03000003800c000c40c2c00d441d03081500c44200b800c0000042020002d180321010000a1503664180d0104180381a90281d0f0048900c00c5800e10203146403410514501e80405c0020010503ca41c1241c3e2403180d00415600e00415081c0d281d0300c80500b134503041c5d8007211009c00c01000780f103e030038640c4582005c0b540301a0345000d1a58 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 640496375 1250 640495125 640495133
    0x204061107080a170d0902150a03050a050903160f120c0c08030307020319020a050a03031e02090607020609031f0911040509100b010c08130305010b1f0813020301090b0108070909 78
    0x11140024611200c000261342d0308105c030181c02c070a0420745c00610801c030b2220f460f40d00c00d440703a10141c0100300003442c0c000080d00300c14407440f94a0042102d0401541469150790f9110321550795590181c070852118240d910000700b2846010400b03c0803a616003003403400300c1c6080c032140340881d00b0005007900180b04010320b55500100f6030794410309414040c2d159140441d4241d0510042901c0540035015000345001415099001044813040d0100390100c81d140e841c50850882c0036a42e440c1c0c0c3c1c0f1440c10418003016180542c0a007880c010020140c40307503e1492800542890301400029001a803907000040500c014000504030b401815034080c0921f02d0f000e0011902d40301446406a5000d0740c4900c9000c050344101014046d95034000e242a80d5442c5106810011407003500c02103900b5800c0415452250911032040c082889141c01002c160000c880d5082e110360100800305d45440081c1c0c984840036a40c00d0041c900101d0181130481840d5041012450420030180c11041040e4204200c00c8002 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 640497625 1250 640496375 640496393
    0xf010908120f0c0f061510142206260405250909060e0613080315240304020f03030408070e060609030a39090507030905010204061107080a 61
    0x3801d9003100e8940d1101c01c1203001d4401c1c040c4898009140c8200c4001c4030841500184044c0a507002040e90141c00100c40c040090035080001c01400065a01645401c0041d040001c3e115501c640000f68011407880340380055040c0c1a80d00c840002100000c04480c1002000010000490030740203022903031400d602c4266440180e00e03800e803090900301c0c0240c1c030343c0600c514941e405040d4205090107180c2040c24200050300405842d450395003c0e08020802402c80e18144900d95a80407146a045645003802485c0303640c401e190007504840428007035200710051240b481e40f511099800b0985034241030050100d2048040e211070f0080e842000144146800000c01400301c81e071010f510b1100796106800318800303000c0d1f5101c4075010f105807941c038010026040100480134582d4411015101c01c3c480201c03c071681c0c40d840801014528940500c0000d11b50341000790b02403140d06001c1501d10050b030b40d040c01c90f409988804000b620f000d414204926041c006c01000b40300d02d8001f000c0c07131183c0c0c0d29100d0070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 640498875 1250 640497625 640497643
    0x2d08010e15011b03090e070504170712030f090503150109140912090f1009030515040c0501030b27062d0910030609030e09060414063106050f010908 65
    0xc40e030f600c50024007054401e6003890090101070100c100030b810a841d001d001d41c0c100380645d105208081c10000501c040000c0d50301c0c1180c503000a01e803007004154400345e98284407004040104146480c011415071000c00c40300c1c001403150f81c5a1000c540c507058829003201d90455407200e104011078280804c0c20300005100010490002e8502c0d41c1c2c0781c40200094001e10f024890a4000c80110210341d071250700b0804000c212070040c1d05444207a01c0d01003040c08450b204880c020020280a5000d0119500c03940c02644d8082c005818550304880d410409110000c900003004150050f030701c2008014105040460a07624110f075401c8100824060100d5220444403220f030701441e50800020805815529084015078102c601000030140c2424001c155040612500f40142c0e003034004150a81020f20a90201c510202c8503000c494941904200e1610002c1c0003046080343da08903290900c48003200104482070003142c0015406241030240820313859a400f80343d0511290100400441d000070503600e031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 640500125 1250 640498875 640498907
    0xc0f010311130308090406060903050d080414030304060609061e1a04150c05070f03080304060c02070902130503010c050c0604080309010f0e010b0f03030408030a2d08010e1501 77
    0x6590790001c4006415030081e02c0d40c1080100ca803810010500080340b0042004000583d428442c4079240c1209899005d180d101c0100103074003141603040110f100b81c0810f900644507050841d18030381a607494504c1e540065809942c1550b0f0b6800030460200c03103105000040c2451a0611642c0b0200442c02981424605ca20059019800c60099000084004a1b0003801e0f402c00c2d1485202d60000c0020000a6500c03000c4034903100b001008038070b035003558004404807507016401728076558860391150044d0075015030b00303400e6204d0030070007144d00c1d64180040c0541c0510518a03400c81c529210406080d1381809190805000c0108080e58001d00c001c14078a9005402201860343c907244c1100107401400d07184912103030145041c0c407480c00311f18190004101e0001c1182d0041e99491000209a100c0c45144100b2805a004011007511035001d0002c480508003640504502c50328244c0040306202c0718421030310300265840c40180170040d441f8010540041400b207442c21040303000c07000a0000380140807140 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 640501375 1250 640500125 640500131
    0x150f0e10020702061317010c021207081612020a03170c1b071a0c010b0f0a060309020d06060b09030706050702010503010e0402040b030109060b03150f01121a090d030606020c0f0103 79
    0x80542d140c803801c445e1158025a40450110b69500d810310841301c0d803008a071815400c04528411040c40040c500c0d4503405660044c038039258580e61990f04a500c00d40c08003000488032985c840c04690307483c0026000305101d402400c3c0103005482d00603c41c403e140e01c4c0c21641c40074002840f9014481100755040100c03810303498001c48035601011303490030042e1b9100086039510380d103403540407003602805050206803c1009200c10303c0b00a0030004601d041c035482d0b03500855140d03c03c0010521907000720340918005410288107100f682c5034501a2a01a0440038414a000401c91034605003005130100819003803a0090410006600007403481c4070622072145040c01c1c1c2000716042d56216445000400d030010000c000303c4240d031420f80050b11030301d8a0701d84240a8140c0c4141942e00300600c00d40f01d54204121103245078200002c6906480b9841c03c2541d6181c0c01c004885a15104584030f103024851200042814412840d4020241c0702c1035000007045400030f08201040341c45040c103060460000742804 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 640502625 1250 640501375 640501387
    0xc06110120220e0a06150807080c250b040c050d0c0e0606040b2809031a04051204060206010f0b0a08151c080315030d0f030522150f0e1002 61
    0x159074203d4010403aa100074034140300039600c480c3d100368125628509005d42503681c0c100240c5100358100c64503004210650000b614003a005001020141c2c51080b001540c00c000000c060810080350390104c07150054902071009004410402e0001008200c0344500c611082e47da44880c40b44452150004d4a89698040b071419a95002075401501030002982e44440c803419145c21000e070400714195080d07400c4216136851a11900402c800d42c0d0304001c1451407405840140034001500800940700c0f402010940382c1e9240c2040300034802001d156000b00043e50400c14280c48181c8660b00bc16803803101089031000f226004003841d81d00c458079242035400004110b0114110180d00d5000c0d440200107d2880c000b0415080050741c05546450810450312800c1402e241e030b14440c02c010800403408030080348040794829040b065010228603c0000008035000d0910714500340c01c001110a8211100781d91030140c000c0c0300300c071a40300280900340070011120007290349440c0048102c820031a00002c80c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 640503875 1250 640502625 640502677
    0xc030103052505090a0519050c0f03040503070204061220011e170a021b0f060c1305041503060b010c210c050d020606030f15060d020301090c06110120 66
    0x2160010100580001c80d13900e072014900000340300c00c543e0080d9141c00080e16030305501c5148903061040d04400c0081d8074140100c0300481c4d440c1c0005208441510040000078010b0311031b401031500a01441da1302c4980c0d1005031401807456a101031076a10a0000205c1e80441680c2c004803400074440c00c1000e9a008203c46082100ca10340d0074000c0c030340707600c101c03c2c1804a4100960b0080940c14164a4074100300590410704a0302d80c400107072031009542c82600498030000a880c001d1481d40d110407070072800f0b240d443d408030302520642d441c11000c009520328200184241801080c2e0380003801d00e00842224503596401c12400c541030100550707051400e08202200d4002d90f0490f080707541200860300d0309852490300a613201802c0710310350b010780130300d0000300561349000504601055858030050240d680300d40c1032141411684c0c2c0c0a0343d166403100350740d00c04901c810452802a002c1552445004d070603040e2581e0944100c60145640324038181205801e0010b0201550086402e06403d29080215154 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 640505125 1250 640503875 640503943
    0x10909150902011704150e0601050a030816060e0304030209130b07080c0d05090c120714060d0902040f0501031106090a0509060d0209010f0602010501060905090402010f350c03010305 80
    0x300c80c01380b01d000d401c03d20040c001414007088018405400622002548170f4620b82c44207020300c2104d806c001440c42c24000200c428001e8620b480b5148120000000c0c0b9846480030303545c0710221b505403a00002030510030f5090110409510808191101205a04658403041c207482d0050a0501b0060240d0200e00c0400d0700d4000c858034800f42c04018001800c1a14600d07494070f40ba440d007103100340300000b0f02184058001c101c0004496440395108549001141400ba1560214041c200d0091780c8000300300060352a88680c0c640f07008900c100203002d6065144c054098103103000c03650311a01c41804500305c0b0345e440a0a0001745d610a44d0020101e0300d810b004514441c499020080d1b100f0b00c9480003181140c0c1c404041401c890043d4001c2c015079903186030070740d28050305000b51504600c0e000c00040c0507500400002c2c09405c07242c40c04151a100c5241010f2050070843c0d20000c0d88100c0d0b5443d00305030264107031138030741040d5035190f024510f5145035203480e82d80210308003000107606400000010000e81c14 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 640506375 1250 640505125 640505147
    0x93409051501121107060b030706030e03030112030203041212030b1e04090c030c03121b170c07080313090b0a060219290a0f0b060301090f1b020705010801090915090201 74
    0x2404d098441d407071481c0442c040d00e20020158007a102d81c520004296100e4001d80411280341c20207980380d81d00307240101800601014068003036100c1000001088400341100c0b00c0c4090003400510a011800c040040c1030b95850001580f04040341c1c0c45807100d4100319445120010300031900041c500b40c007494008000241c0b50320150400f0550700002081c0b005904124603098000e90b00c41c85a005e00184401d4500c0220300040c01004140c00d105808100c0072004010f5031402101700c4001d5a52541c1a526507402050000701c0018800005c0140c0040c60044e08180c8d1012512300c0440c3d800d00d08000c0d43c52880000d682c400340321100d000c10a0000d03001c10b415508800d8450300428084548200c07808010654201034403501d48420560210300c103206003c0c00c0c0a0041510740b6591a1619042c0540564600043c00e955600071294000c6021001e4505000c1c4903009800d6842c50040050a800380580c0100802c601b014580b00004100c407141c040401c81d07a49000904e001c260004855003a004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 640507625 1250 640506375 640506401
    0x280302030304060c020117010b0f09190f06090902032509030b13110d030c2301050411040c020609030306211905060606120f09340905150112 62
    0x1000f0800303136880105602c038036000381c07a82c01c0d042d504444003240c4400e0074403410300c0840092080b820480d12040050519401c020b1180306003010041e031401072207a9a60102034010910441000070f160002c2c0e840f8001c1200e81d42c11421031400c1c0084006005441120300c079200d064000c006903060098400401454102c00b4a8646142000c10351559100b04401510072400c01ca813103000034504044011203040d4580d81e240400c01c290340ea0401004101440340d1050701459105480d000800d104042c451030013003661041e03103003a1106020848042c0601901150400f404000020000200300c9400c602d041e130362401803d000c907a44e0700c1407803403440701a03d142c0515119600f0040c5400280c05000c1d0040081d83c0c03c0d600c800040019500c10300c0c490300241400700002407070668105400e16400020704080e160300003048800402c415203241100c11991801d1504501d450508160503c044c0010746020410fa082406000d0b5800002040305410031580480d4802200b00d02c2d0800d80c110050 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 640508875 1250 640507625 640507627
    0xf0d150803120f28060918030e10090513021206091014031203010608040201090819060b0a0b07080703021005040209010e041403030127330509040c051e2803020303 72
    0x41400c140020380080d01c107240e0041d01f404100300d4902c6506500d4446aa0706440c1c00b1342c008504818408501d52420008041c444090000107541c4c0b68801c030111002105840161b0700c00500700d0040c6005009000c0da801014460704120304508070350240005d407980340700d02e41603484070000024036086980c0c122141c2200044000600550000e23b110f01a41c400d03228945c03101d1b00c500500c2d9907401508208041e1006140000d03010aa95502c02c1c1410100070b042002d20329181c040c15551503008800466107600001141703414185d05004179100360907a03080510240c141900020b40407181030141056000003040424100005468030004680461381566180c0d070f5a000004100c0101c400d01e0003801c0700b155404c000501c4a8440c00c50880021100000000b2000e03920418840015a40005151602c0e5010610f590b038002d000344a6445249100c6200e42000f040c4010824403882012001d180780c170403181540c1e9001c1d03460900c40b0801080b90340020080f541c0c0459a840c5510203501800 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 640510125 1250 640508875 640508941
    0x1701090203014a0f0901090c15020a29090106050d060b0102010b0a0608240307120305040e190f0902010e040e150a05040b01080f120a050f0d150803120f 67
    0x9020030041d04c24505800d110b0300555410346114240c0e55038103001803036403541da0424040d02c071001500c10131a845910490f0300020442c1e983c0034a0f6040311242c0d0803540a82c005d45036008501400080d80449079100a00c01113283c0340100e280500b1b4640000c00b401d484401c9080f2591007503003c07900544000301080301041d0b076444090320101041e1110061440750220002a01d00100e5140e810303d01c0c0940100400351400307000200940695508800f0050704120018449a16610300d034050044480c1d054000080b0102c0e040c01c840754086a401114100b00c1c01202513038209282510059054402040c03040f100380810341401c80e00d803040000c0b4090f500621810742c5031076206d46e1180784a090410040d0b40c0303e001450703a401100d15000d0711a4483c82080403404050400390034454514108241030505440c0b0000b030541000009240459132180b000007841d00241424008029610140d444d0203814030000c47d0003080285400c0f0f0005e06c00c0e000c0b0b00d40725040140c001e00c6810080d00104540 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 640511375 1250 640510125 640510259
    0x81f1d0a0f02011e170a020c1b0406080d0513091a0f152b06080d0f0215041505060108150f030a02030f030304060b060a050a120902030d170109020301 66
    0x4c10401d81c1240510405c00003e500c00009100b1503624042901c010070034030704140460022351611008140d0001d44440e400194002d040100072103100320b41d00c07010303250706a12869004821780740e807152800a00305240388600d10092042910982e0051750152000d011640100d182007100140c0c410112000240d004400c2c4100702190302e03141221003e0080e141100070910b42074404a0003045100e4200901d0480010b000d6050468400d07030f5401520b58010381c449002c4018501114161040070a40c100c481d0b036002d070391090603031045003420007402a0800c09001e244090050404078000c840c42d5001e00c5d4195820025020390650003001c890b01800705880c61603ca0300709440c11200c003414210501d4280c0ba0080944000810704c2d5596030402d00421800c030b4010070591f880d0200c0315900c00c10780c00540c40c24041702040c44c4850325415801d4188100c020400c6105130b2110ba481c61041c00140041d4500388030400101f81c0c030f481d1344119544582c4102104800e250051985030000180200041c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 640512625 1250 640511375 640511387
    0x801020a030608010c0806060304150908071a0903030c090303040f060c12210f15090204150207050d060221010e0f06041b0f0504081f1d0a0f02011e 65
    0x10000c95941482401e41e540416400c0e584101814070201754104002201d90900c0c602950740640a082450585071140c02c6c00f408403035540c4005c0c1d603861000901c8200f030020004034480c400100d014807051615100d020075860380409400c680c15020005204449541c0c200b059030040c000c6070040191840e80e69101070800c0362048c80403903c2c080c501c24401c5403240521f280c05010260200800320701492100804001d0130040c104034412075540c884c4544c952a00c08924005c1c0c6800b0100503502c60821302c0701c554050b0300a01100c11980801c4061019481e681c0720640f94030340c480e0340585c0f075010001d030301018014031481d102c4c14041c5c4d000000032528402c03170b012b501598404400385c406840388001d002c01e48032100201c5031000c14160702034221b0f903c00c080300c2c4490101072030a0307030030103440b102411b08005080da40d003a040302400441c200244c4291092030800750900f11500080300c244d80040d074450309601c41c05003040302201e03616015039016520144841080c00041c0b80c42c2c2c50145030103055 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 640513875 1250 640512625 640512637
    0x3260f03090106150e0f060d090f03081513020c1c050403031256030c0108091002090103110a03200f040311040f06030f050c061809040219080102 64
    0x10741d41c00c0036000121180c0d240c191000c01c408550b10f1030804002c0d07505100c0761401a10f802600070781c0404c030340d070071500c0e01d44644070440c2c0c401c02c0100004852420020010030002d409034200d20400c00030581c040d52520000041c2c64030141c005038507081081e204900381303240030006d503441419801c034181103070f5030040041041e244a6225030202c01200c0c2543c0045501020078a0b5001d04030901000002c01259004522200c00325510344c1c01c0301c41203441c000b0f9190001070300d40c840500c14541c150140f500b40b020043c10030b42841c7c078202c2441c184084071707500c0c03e0104608030407075400900003003164482d800080402c40c00380d80e104d6544c1c6103410000c0041846224103080102e9400f555107030011640c00725072668600c2c5d001681064210307140c41d050355100320142c50b401a6191104210700723805005a1008500900481810a4042c10410304003141030b80454400c15080002a034030100c00300204242150589081c00c00d0b64031480442c21665500c030813040c0c0c840c2042c00005020a05400502c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 640515125 1250 640513875 640513891
    0x4030c0b1c06060906050d0b03030a030b150c0d050d0605030303010303050711150d0b180906041415070c140a0c0f050a08030d0b0d0c080604060c021603260f03 70
    0x81c000300d10348407046400764020b44001a10ba6401088a5403050002e0b1071529644a03000070f20407054000685150301846c03005000caa01e41d40d0790f0000340b900c22008181042d21029032031030701903005a96500ca507414141d2106101c004a03030803011124a52200d4045c09002d002c6a81d00d5071203003005021030f004508200c0b914501d2a250000c2c2c0d086c199041c281114a04102504002c221b5007000e01400d442e805964100740034403840b07142c06503000d021a0140020f40c0c0a080f0130305050a2002003400449101e070366903403081c500389400f199028180c9911407c245000e0700b2130300c90b92030040d4401d92881420240c9114920080007400004200141110402582485805e980d2014440c034040c0c02d00c03541080f0340007030040d900180c000e03401c00c00c0111002800c14004010550b60825034000642010450358840c000700010130082d48900500c140300e81c0020001c0c91050704c81d070750790071b8114003004100c03004000c0131700300030b070100c014103003d04c0034890801c0d49503101c558440604c1e405c101c5540e2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 640516375 1250 640515125 640515157
    0x90c0501020a0201080403050f1c0603020913111003020c240601261003020a120308330310020a0e0a17060f060a030b0a05060a081209130204030c0b 65
    0x6595070000605040065042e15001c0740340c0c1e104d4070241c459401100d07404550719010400c01c420b541c0c1c610089100005102e90020f003490560051000e107502c0202501210020b800401c00414100c52a103442c211049035003008840301480d00b10041d0180280f00d4400388a40c440304034a2206034000403103039940c4024a513510b40d498000440c1c0c0980c5145003214105075218544076003105a08a89902661000e1040036080c1d4070b5001c00c0080409a100d0b83d0390f01602004401010b50101681d030708003075040c401c1c1e4241ca00f02d40c091081c14105a00b031008003060403490074260b8400744140d030007400002c2c1007103440d035614000251880b10883c84c1c0900c50404101c01203400b01100e1b10b06507046c00000014183c503554401003145505010f400740ea841051a4400000240d09031034183c803518003108085070a003080d0081c00b5001c88590407815864000b410421101180749055600482c02222035007424030502c03409200034882c5400103025200c80d040d01040184009005024070700000f0455 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 640517625 1250 640516375 640516379
    0xd05090304060c140a0507060215090610180b091906050603090601150e0324090106050306070c170403060501060f0c0b0f0403050c060f0901060603090c0b0705070e0109090c 76
    0x12612031080303002e05004124040f00400100300c0a80b09a00c001c1907200885156070001d46035180303020065841400103a00060070580c40ca1040e04005401c0f2030410002c140c64203014001000c00002400be034840940c00c411400c1e5a000f1070707001208200d00180c407614031400c1407046515810840c1c0c107075615a0b801d000002585040c040300701c82c46144108003900d03c0386d080a10f102121100d002ca80c0040000c070900052485d0740c2400304442c1c00d10500c542c96102203480c4425440d1400c004c040d004240d01d05642027040d03480104550ba8404030501c0e058505501e1441c1c8102013035009040405285008030f40442088203942c41603040c1c03000c070744178000401160310f8200c590384625000148205000c80119000001d0080c640e50803522a08046003011124120300b480c1c80380481d00c42184a60410a211015100788078860290200d03180c20f000c000100c0c0c6400803082c089100d0070003c10380c0081e01c41c041c0315003071005001030402d041880400d941e513261403002410a00405847d262141180 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 640518875 1250 640517625 640517641
    0x20a060e1c110c240a0212030901050a0606081b1e040b090a0f0f060c02010e041406150703020c0904030306030c0803040f3302010b15120a0527010f110d05 68
    0x2146414044007039002d0007510094051501a40150b00c020003588a0800818601087d80b0055072245801100008440c64403400210682d002c03640b00c5000d00807400180030707566514100348441c42005641c0c1da9641c0c245481542840745805003e43c2c40c0140103c0c000c5103040210380101195542100c0f924403140e00c2e010421024046407280680341c1400d018200040c2c3e000303410b0380c01010300504001d104c0b0351001000c90140c584003001214200c00c05e804112062a0171f040e200605203001e0981401c215051f5000b079552400502c078240302d18a200002001c041c801d80040c0003840d44090391307180c0c3c0da9690710803a40d42d8205000f00e03003103110b0a2001040040c0d10382e0982004248420071174040c028240d40b09031501070f0900d04d80c006c40d52581a450b8179911b6411090b03150320b031910400e55540e14441620096444050642e0003078070300384000d001c1c0241402c001b0502410342071285104260850394601d0050110700007070b005580c20a12001e4090010401400004100710401c0c0075654130100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 640520125 1250 640518875 640518889
    0xf05030102160f0302100e0a0b150307030221161802090d080a031b02030d0b03010903023310080c01080c1602030a0602040e0421020a060e1c110c 64
    0x30030004604000381410b030101c3c42d0b124480ca851806801507802014484114406680001502c40c6280e030000811104001000c210340b6032011051030322110b11112180025258841448041d100341030102c0300c8400076410598a140b00340c0c03000300700e42c0900310400c0344000b5502d042c41190039011820f011460942140d000b05c41721400c0040c01c920071601d869135140d03116002070b01c0c46003c140d44c0e585a40c0d04803852010740d012000043e0001c644502810030240700782d4140280460085c0d040441e030707400080e00050b001d40130a2260103660088001489a0407115840300c031013062504000c000d011000d940f02c0740303680585085a0903074140720070782001520364110685664100707a00401c00324486412141c00b0300c2c3e06a2004040d96030012050f1100c00a90f0455005140070486032024030040024100014007002e405500100102d00410006915000205009801d07240c540c0340d4a07280d99003d124a0600d2104080c002210500003c1b0090000b02c911a080b0040d101d0803a00398002e04d0448 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 640521375 1250 640520125 640520137
    0x2c0a0b040305121b01092103021201030f020114030a050708070f0e0108070509090903220806060d060207020d030210051005060403080706020705030d090c05041a0405060a15090f05030102 82
    0xc002404203c0745500c1c803c0350780e030000981a14480b1124003444040b50207004000d00c49014010a0140c01003040c001c0386080180d80c07040040c50320422050464451b40301c01c9a0440345c00841822031204240010f80e4a140f1248604040c41341c00010031059031842d6218600070b00041e40c9004080c2d451200c10f4504442e0340002d03002050703038000c1303805e51988602a26540410184ac3c010304060700800800c4490405440da1170840d0070100302403289141081c00700c0c04042c00c0d8140c0c1d8411070702d8a00207039103414024154900440030b0240d20350510045404079204c04d81e000e03024891b81262400d0081d1540a16103c54080c0b50804021520346040c00301c3c0c0380240d4000805080c030781480c1daa903c110540c841d0104a882a4080c070108021030800c0c03028101014070307080c0210b2a808549003000c10342e40c036500003912a5117031802400700f0001505030f900085000b600d0010b2176032201e000040914480c0d42c010701c074246200d83c1c2c101d5103d03808201c4204031650346448648003038803a81058241d000e04 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 640522625 1250 640521375 640521383
    0xa0306150e090c040f030b01151e0c110d0b1605040f0e100905070906031b0504050927010b01021b150a050409050c09030c1504090c2c0a0b0403 63
    0x1200ca41e541e4581544a42d030040d034006045407415030345c0e03034041070f8001079540161160b20144004000c150500445070352a04500d281654040603111503102045400705082010130200401500400528280118200744000c0c6042000d83c17881c40c10703e450b000212851260300c1c81c0707511761180060113903080e03905983c0b86040c0072110a0034450052120071000f02041c020300005840004c0958040c89003a0040090341c0d42c8500c401d00b000400740640e145051000325843d400c01420849070750107400d031010f80c0c1e412982c200c0517031100303101001b000c0c01440e40c1101503800d02e61004080041503205081a13802a000c1c4d5080100150f10101d02660740c1c1031254108503840c03990340381d12120304010710749955103042690034961506c0f0014111003007202e503004460400035002d100f600d4200444017511000325129604c18915021040540c000c510603040c3d2641c4840b0400c2c03515002e605002c00620030701203c10460038951000011464203118203d000748403038003000ca07424140314115002c0c0c031b0b00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 640523875 1250 640522625 640522637
    0xb01140d120309061104060e010f02240603010b0301060b0d0b0315040f0f0b09070e010b03160f110102220f1508060d050f01140a0207050705090408070b04080a030615 73
    0x1d280294082d20521030112211039590401d003066001c500082c00281c0003c0d542c06040e815150005080c40c031210802d401590302203aa18107035078070301090024540704400900c91440c1c030740390701080c0500f07c40060258594240400403810303074901d801030165001100000c2c06010400010305407a241000507459500c100000001c0215550301a01035041c1c1c440c0d0180f9078030ba03459031a41f0942c0f0300d00303455413101c03504924802c028010f00d181d0124054502841041c0c0785003080401c0d1400b070140203100d90305200c46540300741601801241a1503e00002200956403082c140c8400d440c252400031104081c200c080700049102d4a030554103100341d4a50604601e295562a2410f0720301000c01420b80b64060b014012500c0064024400d945080000f00008115036000151594441c00c0003030841d03504a1041c46030801158000aa0a049403001d40d80180c00751281e050505451044c10000343c00000c0c02c0b1700380002c000c21200142022180d942e401c0080680300c84c0c000e081d0f6600d1041c80b10000315 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 640525125 1250 640523875 640523903
    0x101107030e04180f0308091612030e0109090e03041707060906031113060336020405091c0c031b0f02040e0114150312090307030b1b070b01140d 63
    0x902c0c0c2c0c0084121548140e04003410501907a450404602c0004200c3c005100350041c080d4842080001c40c1080b140602070100c001d0402100210252506030080c0812642c0c0c5d210460b10390007120184e000d8a034282082c03240707840c1e10701e040d0b541e83d001d48a620403000504806144550021031a1f40956455580c1c0c1040940760400440c060702d0080300701c04402d1410095401701e8103035066408005c20494034041484d520000c40c0b44011503800300a8004022600460340c1c0c05c1d40820200070026904490005958681d44c0119103030840550002000c0c40d9604c607500300c0240c0140c43c400e071651080e40c0b000245850820481c48492000c0c100815140108007490010329080e00451030340c1c01e001000003180001ea5403200582401522138500d54010070400300050300b0144030003100e0807508030160345050700180219544000c940700c09041d6151120218030b4414052050b8000c0ea443e0003d9540c0340c0c0200d042035031f14400701f03110b41c0720a10b03079080401040e0f041c414190f101064112102e502408 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 640526375 1250 640525125 640525129
    0x306080c15040b07050709140402091509060103020f0c0109050c2b06020c030d090804150804054207030612120f09180b030106050607050303060409020114030405101107030e 76
    0x9080a1000c070f849000c2c00c6c1c004203455600b8412100282d2401c443c0c204582464014000c01040280c000d13103000656880512941d203601070440d4006100b0f290045c0d454025135100840782c01003030003041c1d0315400c0c8070400c0c0512500081012210034100d428216100b00300d6154441e01c01500400088000008047c401141c0c0700d502611042d9000c90640e0b18020b03821151000700e03001e040301200c4000d008541440010740f58180584d142c452418150014102602e4003551980c10300c1c8201440641d16001c002640d00b14000201d6a10002d905514030308000f6604080b0030300c003103d1207070010b4a002000180c51102440d10011035400560107004540ca1134012a614141890307203000b4400440e0000841705181440d041e0322809100c00094026940804c050030754529505c020300c44e0b5001c9c411070001c07480204c11a60400070481d00015255418401650000c561000030601a41c02104000600c200440e040c503003104268000c00c8840c1d1001d000000d10f000790500503000488141c0d81807424 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 640527625 1250 640526375 640526377
    0x9100e0c09150d060906050d23030708030c07060b091e22110f030303012723040201030509070f030311070f122603041e02040c0306080c15040b 63
    0x240c0400790103400300d000b605814100b582d010a10f100010303641c3d60810000c01c150391080c000501000c9401d440c40d4000c9481d1540c1814403008a0703030003041c0350040e52410000c00c104070390003217a210040c1501e0f0318254951a0458020342410b0721100e0500140061514161000c0e600c07680280c51100750100708000082c200c03c200806440d6540742d8180404131030780c5820010f64082c0e100d00c151820152001c800c0c001c0182142070b0f500e000b0791050005104500e07000c2c6250407a254a400d580790302c0091208400c003d0403c0c510703983c00c0340c041c3e00200b114001c40550780920445c000c0e00d05002c0360701c402c6115542c400d41e5103d1003801000c1c0c0c020a00c0001d204e18a032001950203642200c00380f41d05c41d01c815681c0810f035444000440c2140c80003101700f01d0708044851a0076651200000f44440d242c0c4425290320004000a0402500d040743d01d0554070f0b210101c001640d00035004010282e580c1c94040d000b061980140310700b51080081d01341642c42c12030070013402d00380a039170b04500b4a0303d000d14103022 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 640528875 1250 640527625 640527637
    0x9021302031512030a02010e030903030307120f0501060e101d06070204091401061503050103020f04090828020f06040210140c030a1706010201021303170403050604060b09100e0c 78
    0x20b0080b0071a4110341e41c034640312802c0001840b01031a51052407080280c2150400c40071801103030000d000608996034080280c81d488030340d6050024141c1290981a0010308201d00e60b602c01c00d16207000826100c7c1c1c09a8081410301d4203913001c4170304000c0040c007501d180c100780301210407580c080c03541c403039183c1410710140007058405440410724241d42d5440c0e0340b5111907100c6a0640c0e81d9510020020b8400d00b21038071424a0807030900f042036505540105284903484c1d0595070145445515680030440e0a0b0200d5810700d0407494000400d002040400341701c001e00b038404100601c5079518000c400d50b0003058803401903600034407050181d0781c0c07403100361142000405207440b403c00911454541070401d20060000b030041707665903048514020044000c400c2c01415440c1160b00c18014191200c107000418026680c00c050003e01c6241710900a140d18810f5800082c8140904400c1c4000c02c06540c00c2010003803421150704050742d0752500d03503918425a81c41100d01d030b8060340d808505000704a00080031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 640530125 1250 640528875 640528891
    0xc3f15030512031608010608010b070809060d0e010b01020d0c23100204080610180e0f12071707020a0b0702040216050c030601090e121b01060303170a0902130203 71
    0x2502996078641c5401d2180c44040291101400400c01c0001500c80109000d042d03024240305c072555042c60401803803c201400f480c0088040080c10200f0700143e4010350300d501000818555441d0061b41c402c20243c20b42c09595190780d803c0c1801800d2560003c601c03412503038165560210a9200744d1a8040c04001c1941d002070000082c0d800d12450350750500c4143d115100c520401b5a07994600000c41e850800000d11394000341329040818004010a0b492803141800a0310740400c8420040403000c1c1814854110840a445803112020074001070300b02405800d4040d61085101030390700441b0307003500c1c0f1070484000d5008926503801d000c41281c843c05404107600140005080101c10320240e4036500280308292400e038010310440303586107820803105008d4a20f0203802c0c00310306c4191300090340d94081601c0c01b0b2002c00740840c1c80c08030b08000c0750b503108441510070020304c4410b65a05001d007040d2090001440c0c1d039004a00014015061401050401ca034041e011030076005035401103100a41011781114 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 640531375 1250 640530125 640530161
    0x309080706020406271d070e03061807081227060301031110020a0804260a03170c1809061c0b180c0d080c07090c3f 51
    0x40e022400307602c041e00281030152150103050000b5624110000c121500440b1082d105100503c00d00c61000e81040201d11050320044403034417440c3c02928440406c41c21581c043c49010100400201c4079002c80340708011504c01c2d14640c0d0b07242c100a43e00c0d181d500410040181d0f04003c1000c40c1725550140003102d8503074900b00800da41703140b000a42140e01c280d20544906905c040c984080d8a80741401409075600c43c001480031485650314500303d40207601c5080440ea801e2280528081a03000e0341d6030320700c41501b0030f442e22101180780260014103500c8075002c0300d42d005d20000307009082d07a4003101c0b9265114840c800900455404000e4920401080301c0d40046c241800202005031443c05640007030b114038444002490014080d031400e09200348400c070980c2c807003213582e4040e465410031804055003040e000c81e03450701d0038a00030b854103d2541c0500c3c00c4515282d40c41c0c0349103a000340d0030703203178581d40607207944102032803580c0c0d0700071410741007800e62000f8180d440302149400140d005800819280c0106 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 640532625 1250 640531375 640531387
    0x806010e180a03020c0405010602010203150433030c05060309071806050d20012f030f0403050c0a0509090309040c020f0d031a0301020c07140103061502160f0510030908 74
    0x403820102c104000700c0c00b5a100c0142402d41d071030f00e40141c1d8003410141c4001c50541c1342c20481d01c6000404008064040e583d0380d120080400d205480e2000e601080e5000300c03102c0580101d0402d0340c80050f22060364000015400841c030741c6000c50441340500180c0006080442c2841d010302d0b850240d0a1491005907600c440c00541521740444455107903019008007208a0700b4030910f040c2d00a128585581000b0715659408540030f07100c0c3c4e0200d100f51298581d03183e09070b0340400c4a4918860312052595400c2c002c036002081210019000034403103030540b81c404206030307580f0902800c241c0079144480c00360030911a005007414035900c40c00b011021441103840c6140980103d90500c01468a800002604c4691000c05003294030680d202409050340210301c0c005c0800071898551410303014141e960480c00202030300300c2c0c1c465009003000d840d44518103049036025000c060744d21044204440358840d14110002428190b15140340d007142c00c0505003541c80005820101d004001c1c9000450350b01c9414000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 640533875 1250 640532625 640532671
    0x8090120011506050c0a060207020604030b0f01151b0b040f1401060501020c0f0603190f05070302030708060f0312090406080706020307051c05040501050f1612030606090806010e 78
    0x40085040381a8000688000d00c0041c04500c1e4901e41c0141e01845000c000f503440702900068980c009903080400107071503800900c0040d21034403e42c1c0c00903081c2e0070100c06211003130090250003412984005c0303420702045075407601903a10000764242484900c0d83c2121140104040100c0507038861b2140c00118140d0420795100b0000705044209111169501d40007849156010403000e21009400c8070b009100e0300300301d400185a444018208500c2c8000300d03408d41c0c100401a0804820400320702e83c10700c400e00e441c0d40c2c0103000303400c03c6a030100001e05030070109011f400c1c2403100c0007031500c0c0940941001d10710074426904550108045581095541100007070602e000d11581c1d01510300c40d03015660701c0049041051800b100c41c5200040729200501c6e460007103805c00112821100203082558445040041d0304106005a00f2103c1c007818030700a103501080315170301002011040e10345040200381d8888000315984001e5006d4400c89500400050110030b08891040c0d81c400c00040030323040420034100f2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 640535125 1250 640533875 640533917
    0x21041502010b181f030f060b01050c0a11011d0306010e071407050f0d180e060105090603100303030e0f030706020c0124060f080f1602030c07030b041b030807080901 72
    0x1121203c00b503881c003445442c25109a103501c61550342c0c81581582415038480307850700e10003103c1c02441c2c1a6105900301d80c0da40520207a5201080410030b0b115522130350b0900186651080b1103d030b001841c11017440b07040300f02c05400b160070700e01c002d0004c0200d80e0a000701c03042d075020064003650600c0000240d50080f15041c2008040151017100540884000f6404203807801011603960018070801007541410400401000310840f110b9803420300140d1251001070785d40340326401c41540c000030004100102c055039603d0f140203d910955003044a107086a007100d4035003075002c840d20402e41081240c840401e420b5005410158010000003600429480c456070440000408458034264481010004030f40c210300c23501090f070000c0c10003040b54601a800200960001030019501d004c0200d100000f5502c20402c0d04d01000383e60084802c580d499040164498070308413400c48501321218400311482d410000c035002201d030310140450400810340d0b00c282c8036401c9000428108141d8001000035804445 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 640536375 1250 640535125 640535149
    0x3021c0504020a0b0d02040806010e220c030b010b1801050412020d21020604060f021207081806070c0c300501091a040204140105060306100519020f21041502010b 71
    0x40b005030390394030f0300e00700c1270408405a22150440e2206d400308240f020b0601c000500d0700d8020b490546103485945865500a1011780016101000e0203002240044104008200c2e4515600b02c0b07095500b182d000454591080340100200060038910100040c1002c000400b541407003161007410040440ca110010f12000c00c0c2e481005a22440c00d100500600e4440c94580e80064a0706514051441e4110158200007814203401c01c06090001440c0c81c0040f902c0c4a8040c5034102628903900f025100144401128001030b2500c0c01c451100007121150141c441c10459103da141c4207400484460018030702d2680207081d02c03695210842c2c00005645c10311049001d09500c1c5e03070f0084c5410503005000880706600d142c82d174001a500018040796440000790395000380210b80356540c111a0000446e01e900a010100a4064080002d013103036640102e00c2482d04000401118058440d200b0b203181c0d520313018000b810604004110a2020044d140d81e0002c020011b0300010803442081804600011800 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 640537625 1250 640536375 640536397
    0x30b0f0415030b0c030c07082506050619032003030d0509060103031103130b0f04030f0f12090b071506120b0105090109141f050a0801020309060703021c0504020a0b 72
    0x1c1100303000304500c00d2a69034212502940300c0e8114504408052aa489407010180c02c605000c204a881242800000d4280e42555422140d038425149007803006400c0c151081445008203510104203903041140030b40880760410140403600161a04801070301f50500d00594060000300030011024449014160003901000020012036141d810020014991007100f04215001001245e40402080342584103807490110000d5841b401040d240c80507118030713880207100c016259002c0c000c4c0a411004244254082c3c040f1200d00c8040c11411101440680112889954140506000b2610001c480b10006080c0500040c103140c07100055030048007900d10807540013540d00014801070501070031990051a03c5c0302c0178024151415940500204000d00c51300320030405084c0c0c0641c01917282100001018081c200000c003070b403104020fa003c0c1d4411640901c040c4a800d010605a44c400d00c00ca40000030720081c0f1020b205d9000040c0c8024100152007640d01c40e408000c045007100b11a00109004044 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 640538875 1250 640537625 640537661
    0xd0c0215040e0702100c0c081c020417030309191208040507091b0f0e03100207111f08070e0a05090417040b0702040b040501061403071202070b010905090715030b0f04 73
    0x80c1c0e041d0b0340c00b1b0380c0854420904102c180390044001410030f001b1380b0080704800c0c020384d1094050800c01d10090040340e00c810704100f081060703c6c02c0f0070310110095000e603810606581444041100c00d01c881c800c0b141c0020601901c404040c6c000c02c0c4104581e5801034440c2c402e940d00990b44200032019166060091030400b0010401c0c503150a8001042040000a909000e40d40044240011351620341803002d552985800068000c2005007040b0b01c0c0984120003401d155003805d21001403407804084442d1320011440c0c0c600406c601718017800d1030400613140144450109802c0005001c84103401410886000803524a264501480300c005000503100502d50182c0f80d0905004010640d0300c0500342c180298076140040c400c80e07511200b040f40f4014416070041c0d0366251440201c41c00b280c0c0c800d1404d00c0320310114000080049080485d4103c8035902d80074000c0f0303210a2441601d80e001d5200340c0307a03101e000610408071039029401004034520010240034568071004081010f460040c1c0854800d260703 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 640540125 1250 640538875 640538893
    0x8130503181003060b090d02040e0105070203120a02040506250210050a02120f09041e06090209040608010c1e030b2119081602040b0d0c030c05030d0c0215040e0702 72
    0x10001c1e580c6280c4030b00380c50284001840c0c08010f45c000d22400c03003454003e5180d003000307174295120341c2c010301c0c5100c03403000c007c110f03510748050000e440b90000340a15100c2050307000400d1500246000369001d543d001000140342c05a00305980000f0383d5402c1a80e0005214460a000948d0301c165001c404a080f07501d034207a803184060301c000d09101d0368402c0c01c07100880a000100b2032460113000d440100c1001d41c2c000841254035208848204c0100300c00800540c1403800201c4c05540540282082e10000c0d24140200c2d0b032142045030071b070703081c1c247c003600000e080704800c001104582c41c0071070740c601d0b039420005148071000c00450b1235140d5200c02154004000030300c030a0207000801034511207600d400d0540105101594581c00148035204c06a400710000b4040a015561a5844244420fa0040800e900c400581c949a0300b60310040c8001e851030340b107418000540d414003240c0c400d480800341c0e03611141e90383e0a900700310b003c10002c500d420280c8014030001c980c4406050082d40507080329002450000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 640541375 1250 640540125 640540129
    0x405040f03030e0d09030f03030e06090c0112090308060f1314180708060a02031509180c010203130b0315040c020a05071a0d05251107050a0503030306010813050318 72
    0x286844001422a0b200780000c501c49548103405d001941c4d844400c0e01805911410b04402400740c0b030141c1902405100140061040c0010b101d01c0076040c04c0c0c0380c4007001012451000100e070307000a070190200b0800b00006a0b01d1600d9250320305541c03001003489054080f2140604100c841c0c41d440390108802c80e8080c072002440750040500d40c580050f00420041d400c3c4000503440381c0300070f1b01c000c1e85103401001142003180d07032100c0c0d034580f504041c2442d41103280050700c240c000b03500e205070b115840c0600340c441c2c61154800b10840d8041510320303014610051800d802140036502c024a205a00c0c1404580030f0729a0b0746600440042e00078035130003014054081e0601d43d007000604da202c90782002d4024041c103002100c03041a26084468444000740c15a10210107038603000401003036200d92040c1610030003002e5000030703d1400364400319044446594070b1348140b21205115000320743d4154824000103000b03600c40c4209641c800914500342c6003c20042d1f0790945035030084440b08a9a002440e0089054 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 640542625 1250 640541375 640541381
    0x5040303051b01110c0307060b0604060207181410170601150c030e03010f0b101b0305030601230d0e0f030d090f0f12080630031c020a0f0c051005150405040f0303 71
    0x100f09c2101d001d0b14117031074030001a503140710601c10368140180f0900880301c0784801e50700c48a0740741c0a070050020f107442c1c004150148090386000c2c007252030444c8400c3e44080c20740000c0240c140ca410048400b000c20551400f0b0721020b103030040031001c01c43c502d40140b1140c1c5080c00b81d14044586000041441802c14040200750000e04000404010f130711884a464020302d400303542902901030034156580c4d10b030200100c880611039100841d0307512115018404030303c50100105150340d41c01c041000111900c102e42901c03102c5800905071154030601200e208201075500078040903100b4204c10800301075669030f01d45080f40b209402d0341c1d04800e01c2c1c2c4440510f504240144c1d03115004075101c504ca0000d0707210702784421404a022070030b2214075003002202600d08104a170f01c0b420075114141d555001c0c516420010707520544101d00000d601c03a110b072410314010300c0c0c0101101d0703105015100e10064240340c1d00c0200001000c1e1305403100e079050200815150351058038002c40c020b03170780302c3c032000340504026040d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 640543875 1250 640542625 640542641
    0x21020d02040b07110d030c0b1506070506040501051008060c0c030405030f0d0314040b040b04060b040e060907060f051206010302090a18151d09010f02121605040303051b01110c030706 80
    0x5e40700340144507001a60001c2c0c9200f00a81c4408005651740703841081c44c9800140c5106c140d0040c42c00110881030001c00120988594030400080c0907070b40c0d40348010b690342403561103504884c0d4440c0000c5911804540d01500000304c0701c07000c6a0501c0e03078420000703150024070007c28410f034010025400c04280d241c007071302c2c0c4004041915015181480d60341c820701201c001740007800079501d0300302003001c002094010360701c1c010f4024024803040f007900030032585419050390500642d115200700091118000c44d01806070102a850720f9040500c10312040601d10320003005541016030803c42a1a2584c4004148015040101045803080e1854a00d8002c4400c1f5001c01537142604100403c1108a08424208400ea007d0810495034558100b80d5014002c049510040c150003c80c40c41e01c0e440a049040d8814170b00503e02015201d041d01b0300740c0c0c01c3d120354000640040c3c01004800c02c1080341c0b040c500303040c1d00103000002e50f10400300e48210841d0040c0243c0d0459400000e9804103011082c0a0302e03070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 640545125 1250 640543875 640543879
    0x9040b0a0515060403152909090f0d260f040b1f150306030c0305031e030415090f0606140f040e0a030e0d1e02090c070321020d02040b0711 61
    0x490425014000343c49805a440001c0c036200d41090364841c5122070350000340441c3c2c3c174400d9540c0d00d034140044c2c2001c110038052965029405020025000400004070f4031100184134001d068400d020107022100359540480c8a29000f0100d031000301000721030400c8030320910030300425086034101440d01c0c0000c0080605000c401482c00c00c000020710f1407104444084418480000000c00d400c41ca0030f80103081640d1024105100d184130002c00d0044c003100131304000303546000c80c1181741d103035100388032450009403005030490044206102019100d40c0c4a048114010a03540307208440947e0307006c0540f045504a59840d0403403200604203800c0007000545925401c40e001c0c8810403001d000b50347d030754550034005010410300d02c130040e0080d11420b903c4030030140c2282e030201c0c84151880d0501f6800c0f032200c00490140d4000400511400704070400d03580796070343c56500c481090349400158910034601e5925500380942c20404501104501d00c0200010082c501000b51540c0f198180b50f410701d010004118 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 640546375 1250 640545125 640545151
    0x4080f390607050a0306050402070807020a061803020f01090902160303050c04030818061608090102060105010306270e0102042301030203011518321005040b071109040b0a05 76
    0x840032110101e81140e004a40c3e16255071625031303015044018120b550300264115100007105420712040708001d0550b00d0080d0744284080d5658a003c4030b600441d00303540300c00190406820300040c5014030308c00c40355034030501d092003000c0d8030307081c1d0507080382d015819003140d02100d241600d08150b058050300c3c0d0311160803103c040c205461031710344118504ca0200300c0300c500d03034400551100307541d500d106855031401411150f07020340b8294907000085d94403a240c01405845008000240d40d8424000d40003600c0441302c201c0c0383c142c50b000c1e00c11034030805e448000e06155201c1195551103c001d10141c0020841c0354040c0044600d12844906071a03045610741e810540100018004e03602c1180e050204100d43d49000c10724a085910040511030302900034482011026100280741d00b1100c003040d024070010141a1026414441088800154800f1050200da01408100030144504024120359802040c100b140f03620810f00041d0030340300c100c0781182e000c20240700303010441c8000c5c81940c1c0d02401f68000c071 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 640547625 1250 640546375 640546477
    0x10050309070512030904050a0608030c030406170402011407020a09020f130b12010303110309090a0219020a050d050a09030b04060504051204081f380a050f0904080f 72
    0x2504c91085188081c0216290300104e00c140ba400e0f03002d20010300400307003500e446500e2207000e6030302c0f03510a224000004042da000c41616052421006000f907505031034041e201560601800f015801210081c0da001e002803200060005040c002054124500003804d0303540d010800c100c4e0011001d0340c0040000c92030501142c0c000b1030801c92040e041da41c260512064520902e80024030b14030660008641261740ca03001e005000d09c140d0064000d5082078060104030252902080740d50301e62000e03024005502040f00101498003400042490300c0c640d1800200458032601d038a201080c7c20f450880761140e50f402048288034060180c8124a02c038034500b189040c3c6001c0c04da640d910010461272044104420b141d11803103070264030408a80800072400c0b0300d581c1000e0703041000903c0c80c0194007040d060942c0000781034540b0740201015030380e0081c54258190030b0002848607404008204540200b0208600c0f058801d0501c0078000c10840524030002e14440070814031100c00c00c000b85040c65190b00012 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 640548875 1250 640547625 640547659
    0x7060201022706071a0a0501080c0102150a2a18230f10020a17130b0f0c0304090204140604030308040f08161109070806101805100503090705 62
    0x20025032803012004802400a4000004210b485512001880301051170141d0400340140d0140c50302c10b101c009810005680ea8000d06130300c80078401035450041c0c01c03c1003090401100094182d401c801c0c4a200013506600480268080100e910f103010000f00500b090302080c580d025640301201ca91916441c8085071412001259101d010329034100700351300301022507160f41c80309048100401c100038014422358070362010194603421280811345107040702403002108814180d04507140200302c610100030043c900f100161158015519801d1109010484011116070800150024242c030020050b9500d103011240002c100500c8141402000c0070b000c20408240c220a015600c1a0460b003412842070291070008404e1043c0c404001c03500e2103601000b000c0c00032501d02d01400101c10764105d00e80b03460300da0042c8c4003404122511903201e402910200b4040c0e1280d0080c01e80c0b0700081540301c025644034400205000c0310111710400203140407040010841007004404020241501c12a000303105d13202e0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 640550125 1250 640548875 640548907
    0x1104030201050415050f03010b0d2904111b15134404030b0604061511030c15070e040917180d08070203060702060f0106030f0b0307090b030706020102 66
    0x1c1000c202804c80d45074001c501d400756084035813580346d401c1c885a50b980c50740707480000d40d00003040805080b171030908058402c440320381d00401030700407000346682208400005c0001810100002e0380b1140d01c203218404180304140704004081100401030014a190007920b00400c00004040301043e801644118004c41c05005049a0400350071a2080b000340f10850022512040c65204e002c002c0348881007911030a5418000d00140c07841f80c9440d6641c2d496200800081e95902e01400c3e801d1044103060000c11409204900c000381082d900307a0341400043c2803054240ba5840002410341d20001c000c00a920750701840d0186002022101001182155202c40b51003000703214011080ca100000d030201103045540101c001c041004003005002c11251415107400d4201d01c004034064820b8a000c18040344c00483c0312440380444410484c002d0f80b82c110110090443c0419800d4501d541da40c8200482e202442928003138420602c0c04204503403030009051405850394403802c21a4410b1210750000d41c107402c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 640551375 1250 640550125 640550129
    0x210613020112050901150603020a0e01140a200a050a0c0501081005010503060d0c03050a0b0c3405010504030216060203180d060b03030711100e090a050a060512060a11040302010504 79
    0xb00014465940e420360724010072603120800f10701741a42e20000380d05641030f00105441c0e00c5590380c800307042d82203070f0041d250f01081c2440c21110f401c1c14481100d94520901c0040400c00d0b0074040d1b2904c821a521540b400c103441003a042c1c0c0c1e0358014640c10000d102420380c3e404c006007000c2c41e044c8140d16210341008004205130044a0400c030000021903456035889510f82c110039080914121107580d00d1406940d0b8104210007181d02810032400a08a05011426208018011005002c1d00b0014280364101c0440790661500c1c3c6ca40c00c0841c130008290f0134032540c1d00c154801e800402c48040d111062a40c5074207180c0c04001103503c100000c840c001541406683c604600f55201035840d40149400d00280550f81141034140c803010940c10700703000e4403400841507002c007940c10b41c03a1049450030846501c2041040a608010058041030b100c0c0244d80c816903004588080018207580c6400004101000295140e00c565010700e0611100300024819010410191903540703151500c0c40d0300180080c0214 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 640552625 1250 640551375 640551407
    0x2030d141b0c03150f010503010207030819020f0f120c04050a0513110a090603060803031006080405161518030c0314030f0406170604051b16022106130201 68
    0x80701e480503846500300440e07000514020161403044c2c940110301252001e0844841900316000400011541410300c01c82d8180358050351105017583d41d1503400700342080380251512110782d003003016031150781441028182600505090703070355404a2a44000501e58043c000d5840c03240200b004003c55658007124004681c0155801440e40c6c01c00f0003044000c0003107406e03001c0415400501c00c800070b03070f01c41290130076a85c580c3c4003000070350348481d40309540307020403904c1c0300c00b41c51a1031080c40511f004040c0264021b10030011102d036034861100c1021400b4180d0b1003035110001c000f035413260300c0f81c02903802080320858840445141d45180c680c075242d80128440030348804030050009103059800d208a485044100f49115039075070380d5442c0200442192404a400c000c4034a002c14507514141c06414010560101c482948840c0c14000348801c0c0e1103a0401d1443d46800c82c1c04100580742c4681e03940c0404981007143c030170010150003590270100c00400f9401c41c400000c0c61540143e0708159811a80911 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 640553875 1250 640552625 640552657
    0x2806140c0409110c07090606020d09210f020312090f09040f17040e010312122c070915030c050303030c0703030504061113080f0109050a02060702032802030d14 70
    0xf805818207214403950100c90400c0c00f03911400b103842105a01701c1412150142e00703d80903950301007c111341c680c030540a8102c1042e9140c0e407410f8603100808080c401a8000c5010f44109022070f80040e00d0b203600b4041708091340c000411300c14001d1504c1d00003266071403410364040380c5515042d0b0322043d20841d4604014000c01e10501241682040d8400303844c054a041b0528171386d01e50f1241842500f038201c00c05044006018540901c407400b0f082c0c094080c110003c1c0420035080035441e21300b41c0075074840d8402c0482900c1141c80006118085000d130203180703181c131240b50500c64210304242c90141c4454204038001d40c0300300b0511034400c051404070b55441e60589030024060700c4903c0e14101400c0e4080e07000e0040c0102041014400d000c0c400a01c049031150070071280c000110380b86203400c2e241001c601402c1500120102801740c140301009000c920710041c00d4800c086000c0401c1598055203100c2041040803011030003085080c200030b40d40881c4070718100b4421074032205113010020b2082c8104d02d158006 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 640555125 1250 640553875 640553891
    0x607031b080f15030607030f0b01030c021b040f0228030e0706030506150d02120612030901050304060e0d0903060606080c0301090902041b020d1403040201140c2806140c0409 76
    0x1088180c3c5040d868000301510b00d5420600001070180c07041030381c01040c0a203424007207619980684a040d0f6220b8090f00074044d0041004c000140040b030054400390071a403070700300c5e014007103840784020030054a4034000802103181144560a0803408000c4160038140b800660300307008032000900c001194103a2501040958544010600c000d0f4491074030038090300c2c0840c500d000b1944a401800b6900c03c0c0220320101d030341e540c1d070401401d0101e02007011201d030410820301d1a15481800115403040c040da40224004922070700c168070f02800c415031480003506040050003009031038041d4000030029403500e051141403c0703802117520302c0184900ca1700980d440c00460704645484d0021080c41c1480c084492a0040d0700c1c2c400380d121000d145801c00064100c0d2802000700030b000c01528000c0340c040c2d6642e20160080030701c0702c6450b0700560303102825200d1401c084640b82084488030310300312255001c00307040300724900c1c02c9025110b07560150f10300000e00b4001c000d0004500c205407021154540310101d0321394 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 640556375 1250 640555125 640555141
    0x30b16020a060c0e0f150301120809030d111c09090b030a170301090e0f10020309070b070c060e030c2202130f050324041209170607031b080f 62
    0x81d090150040406080c252141d01d4590000704081e0b130f0940c2610741400c060200800c00180b01c400c1d405aa40440c4140b0051092080c000e14109481d80318804040ca00740c40c04000a01e03042d40012001c000a00b031241d00f0030142014080c410303c10725082a9000040e078154006044102d450090a81c001d9603601006483d41e010000320600c00e0304103e410b06041e01c1820050000d9109002c0c01440c04e0070100c40d007401c20310000c1d951498204c401c014007a20180070b180d860117584080d181ca001d0b4410140301140044900d00144240c5106108048a8515140025202d89484c1c8600d070720079041102144101c0c5c0f80c513407000d06540c0c6184544c03140f4004503542c3c5c0303000b4080d609402940104183d008525990740380100700c1a80c0c8110300b01d4060b400360001540071040d501c01c8200241d0003c4000c100094828400719000c00c4084c10b03d07645540e150302107420280c1018020322121b0344609c09005c4282e40611900c020032411507040440030344061806440da21001d03101c0210060000b000030062 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 640557625 1250 640556375 640556383
    0x1d0c090a0908030a0b0f0a1802030402060403020312030a1505011b05030f070302070e0c03040201050708071a0a150e0709060e0301020c07080607020601360e2e06030b1602 75
    0x907680c00a061a1a82812a500300007801e902c04024058055808406200c0c50500001012160700140c0030130703113141074008800a0341001e0012a00450140408401a80c3c10f008414581404400560b224640a1a50b505948800c2c80d90310740c91203130744814469a40c1c03244d8640c0c40d0b40ea01004207900140c0c45d190843c514404d561000ca0006030101d005020582d0201d000d404079500910b80c0c69180e07c0e04440005c0794481942c000707000c09c0b0208071440c001032030a8054004107002d4843c038009580b1244040322072480032100009156036030000c00364101c4a403103ea0000c0c241490703001c8034a01e407118003d42400b1542c0500c41c244001660700d800207540c2501218404000b59081d21900d41d0745010745690340768140c0303110000d4002d060003c68100c10301001a0b2040c000c0d0010300d40614000b0345070740e4070011440452a4035a4481d03c50f4400e2010170801c254604003425034080003030200d2210741203603c940920303082145007000d40800105012801c401d07000b036400c604200101c0300d11002a854 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 640558875 1250 640557625 640557641
    0xc030f0225031407080303011a0904090309090c1d0103020702031e03191b15180c05180f0604050612011a1507020d06110408120306041d0c090a 63
    0x40c40307a072803061a52503010390a41c20201c07032058050040001c06400201d071524144d0042c01144e62007403004200011032498110310f8000314150341c0345850864000305003070b00e6811106030301140090b0f108000040c031070303c0b460b4100140352030456081c1c420300d460111031410010070b4038105a0003003145019990203101c0f4041022503d16441d04001d400fa0007152070390031403082d01980e039501699148499001e41e88541410490044071a8400401c4c0e60780312495407143c0c011403615540340308003261a00088500224039005070300055032180760104220540040c80110b900110841c02409601d0b00c1460416811040c121004600d03a5164000324054030640b0000700420340c20302807404401c040c40d48024100c040700752240601c0003403880080c140c80c821440000c0d005a411800d000c00708009030700c607800d042c031071040440c80d00f0b6880540f10301d403494101002c84141c1e800000c2c8011840c151007441c1d660014820703c6008590303100740c22500c503100c10324100d001c0d034880c000250082850342d20680b8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 640560125 1250 640558875 640558903
    0x31305120c04091a01061b02040507030b120106140301060605070803180a11031b03060708190f0b130e0a0b07030b04090308040537140f060a0501050406060c030f02 72
    0x1006190400da210400c104040c84c091440007400400c606104081d0010400014000b0641d8610113500b07210090000602c102e04042e90303850001b8150360b40c101c500c12030000d0318002080b1141050845a845614082c05d00d105e607140c80410001c0d03940003816200c10b207811044140c5c803a0341c0c0c0e0f0310080c40c02020700c9074104c1c14090780001d00108501030321402c20301a010b0f42190744d102140b065900035041070500c9c0992640c00503001814a9215440ea10f50003e02700c0c0c3c0c941e840c02d8081c5000c20503a5080341d510800c030b903114001058103003410801e809500301d450744180f14090800ea85981c0b0b940d01040060680081000050352241c06504103d82288014000308003203e400e04005224500c19501110140070341c082810f51101045201e2003861041111403210138082e41c41079126254a201c201d07805c802002c104030360307241c0034066686510f40f00d1014240c2880c1034903c5d036040310790507004203100314500401404059409410080e2603a85800c2c0714042150004080c2d20f04880030391114 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 640561375 1250 640560125 640560131
    0x703020901091a0c0a1a0901020711130b0a17011116020607081c060302210303070f09050603150a12030f05030c07051b1005071e170c0313050102031305120c04 70
    0x2d00300826603668200d40e20861030b496419444100d034207424ad110700320010b07100055911284070f0915002030404e81110300504e0001d071000d02000810900c0d4910750241d1040302c20000039482401c820b000f50481e070000050b4141c0303813900743c483c103003404000c1101c040c2c05401d0201d21103007080b4200c0100caa8540c02c14055040c003000440c0c6900142203c1d010407401401300500e4061488401005a42c0054012020f581142d4034042d040700d01c0030703070401c08400f041840c650008003034a680c001140103c49131402c0325052001d220600c02d22202c0345d0b001d10404254124060040b030b6009041c256021598980256030303440d4181160102e02a207e030151882c000e10702410b4481c004070245c554844c0061380c171000d00c1c00400d0f800761f65a0080d14070103019208000c40c420a01c1c2450104070004502c1030480104810650b150ba08075a000040a020641d02c000f42c011002000c80c10020010712003440118501207050341d50040c03003107482c404e0300e020ba00e0512101489e51828840c0d0900120060010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 640562625 1250 640561375 640561393
    0xd2c03071a0c01090c031a13060506041805030d060e010602030a05130314060106080c090f0f040908070b0103110423092a0f0a080703030e0307031205070b0703020901091a0c 76
    0x306190701c451000700c645500c0c012040508141f0b58134424428820356000400610082e1901005001c0050081d43d10039030303c4640e43c4451140203041640c2c03d0143c0c008680741c3c4007000170082250310b10741001ca0310343c580c00c0040098943c00011545031500601c0e0454803502101500c040741030540e0401000b290300032480c400744e081c00107211070403507100303a68803141510307545058465481049103071904244c1800120700c0c0c41c00e041041c100210070103840020f040802e52074400207900705a10481344450110010000c1c850650104080403508881c2000103d0940c15500f44080307869003408419107180001480b4610140000701d403403003c003004e00310310542c0f018a083c102c1c2c01c6d006145214514508504010b410305640ca14207a035545002007100360705688042e90b15030a09000c56031306220f0040d0220025a4400e25000700c2401d81c1c0301e9a4445400780341c80540300b140100380310304051042c414148140e07800f4001c001201c11142c0083c0090300e04503501015882039900b4400a03120762081 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 640563875 1250 640562625 640562633
    0x4150b150f0a080105010810210b0c030901050c2502150309030406080a140c0f070c090606030e06100b070c0b030c03010f0b070c060302030c09030d2c03071a0c0109 72
    0x920300b02c401690b545405a072618015901103a042d1010741420364186c0c0300340120402000849100107444450080c1204244e40e2401c44400403100ca8400403804400e100c0008030034060241c004048070f400c2e80c20b08881005007280078003120003900c1c0c040503070202d00080d5200c1c5034681092a4584a00da0380e01d1400304007955481d4021302c1407600044100c0001080c0b41558440d0703242406440c0398242080d03c8200c4e8094403a0420300303d66608480410000c000122008050f41c000c010450001c5001464100c0c0030b1304440a0740c40385540c64100c202005140c04415078600d040e180d9074042152101d1581c100282e01c50341e03540203e41103c5d00002480f0f4486110009181290140344201d4000f03601c6982e258440d0060041c001c1c9001d6400006000300b80c042d4000d103901000c4081e01c41d051410440000b0328100b104455180482c02c04804009a84a0100841f080c410745110903d034900355040030030303a40c1c01103110324503503810315071800046040d182085601002e0038034002d000c08202420 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 640565125 1250 640563875 640563877
    0x9070305061512281506090e1b0a0309082706070302070e06010e100c02040e01020a08060d0c0f08030c070905060310111e04030c05060304150b150f 65
    0x11480d114010b490301e400d600100030421980f0f4500e03c14038a40e43c5450340340c441240b40d00b400072080141c1c0b51030800c2c880109020b108076004c459130368481c1c0c9011440c2c1000680460b0b01070b0000a643c86200c0100240c10b808403603d40c02c079031010480c480c0e64502104040700284120035005040510014a209480f110200c0101c1403452020030120403400c3e40c0100300311481403000c000c02603000f00f1000c00c802c441c2150016403014041c1450384e0715201d000d0020700b0f14502070030100041041401000b06504051181e40b48080f6044021860601110005810407100400d6103110b90500b400e00010000c10441070002441e800c19044c54581e02c90300f11030349039000100c444a040c070415500142240c0c0d00c1c01000d01440010300074048564944110202510f4101d205622044081101d06100c0d9111208040c1c0c5200f41c0708040d844505506d40048240d80660201d407081005000748400329442b0b01c1040303103030b0b0044200010b00d20725a50115801100c1d0880b0400c01400100da09203040100d10 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 640566375 1250 640565125 640565131
    0x30313090207060e0c0d0605040201020c060f0d0f0606050f03040609050118050f01140402062206030c02151006050c07030209040b250807110f030313030207080c0d020d1109070305 79
    0x3860034054081d4880e01c950392000350741016a8458100d5490030007060303448d0300090b005401841526058030403080072a078150b0120082c1c2c200f00380001a440180c078901d2186c0200c9040c00402402081d28014009020307001e562004600035400102103820080f9075401090090f911a0003030042c03c0001d21113038450054050240c4490003648001d203007100c010301c2140d8443d0345d515240222502c40f0380078020541c00c03003401c150038240d15408004510710354201e084002c1c1a00d54003c40e00010b03407807009060540c902c00c005140c2c2d03004000e00404000c0c0b5004e4806031401803030801d40710b08a11501901c0c11805a201940001181c81400144184040704038440c20002810303240440c0e09402c0140d200d00007402c0b0b40d000544040216140c544240181c102a0f000754003150980041c0308021410f5500c04d45542d01c101d03411040300410143c050003150000e010410252119910b800301140d809031119000a100d0910000814208409c4681805c440300c0d0280c90002641340080018000302130a03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 640567625 1250 640566375 640566383
    0x180f030803061903120516020307080706020708010905100b06160302032a0c100e12250f030602090109030803070804050c100e0607020a05100c0c06080112030e030313090207 76
    0x142525034244000401030008817507000e0241581342c900030b81d0845076504590f60002d4518105d407840e0016990801c07458000d024000050300580d4904040a840c0c803015502c80c0e01103904106043c008078801007903101d000001d14401141040b501d00000300c0071300c644001d516101c030040d130325034007410346c00009414070020201c2d00380348030f25150748403107030702030b1500704a000c194030084d1154079500308509024400425401c210310440010b8002909a036058404050a42e010703060000f41a0040f0702800540c4180000041a031400c00c5600c419800340d602002c0c103110780004502006910801601e001503412503021900c0c1d0425140c0100100b0041c0c0302612144541085c074640c0e8034081b81003c080040c640c03107486250812a040c0070701a008481300380e81c0901c0c450b800203151380321144054070100090383d0745003242c9241c0c5888031505e040340d04610100308560005200130030b403403d486850340340c15003020311400f0f840000007444e5100f59540c02c592491039110010385c4031b4403034010741107107441 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 640568875 1250 640567625 640567639
    0x90108011d06100509040608011406040b0a06050a230903120310050d0c050d0506100f0303080a0f060b0c0a030219020913080903060c18090405030a180f03080306 71
    0xc0d44501000e401c0d140c40090241900c040040b44151822400300d8820303102e1400c1c090b05100b4084000b50480d00e4652200005944605220040b00120020309901c9034007150204034280604c004174900107028050607080c0304c400034101410b0b5004820113801d80096402e05c580401d550540c041e12a0482c4641d10701910400e1500c030400005002a07074400e003061038034400200e14010070807415408881c001c0c0c4110030007040c04125500c0d40210081464007510042c1b18134200203003141e003580c5859200c0c214008040c1424000a503000d038006811540c10940450509400700c0900c0c01801c2070f5220b001900d000150010341c0b072801003030405036a80250240c807110019130009000c13280c001440203601c11301c0f800019480401100520308682d029801881c01c0c9000800443d1900605840f902c0d042a00030840090380d92044140354000d860544403007003282041d40d10290360f805081148400e10080005840c0858400314806005251500c40100701d9540c1e0304100781c1d6980203a503001e0081c01c07 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 640570125 1250 640568875 640568879
    0x30405101b1a0f0c0f070813080706140a0905040b030c181f0f030206070507030c06050904051e180a0506040c0905090f030f0f041d060102010b0409030519140c0309010801 75
    0x360b00c2c4465202d04030b41e40045240ca5145c4c0c0d08280181c0c050710045602d04000e0100c02940d060700000c40015001036001055940d00b4418050b112499008880c1e1403080304004030a02103502070302c0942203820903030340442d012403400006400d00c004100804e0f08a8501200910f24583d4484c1d1a402004401a8807803501c414400d03240b001505800b48001c41c8040c1e103010001800e00b5002403840b180a0002c0c1c8861546aa4901400030b20b030341c3c0000002507011960343c1142c940343c810340e60404213103415041c05410411441c15500801065210b804a540030000e2101406100b5031076110f90bc0310986480d031415141151045480c0d014100040c0d01d03090015460100006110382605e100100940c10f00c2d0004844400903030041a84501c0c0300414440042e802101c42c4100e210414440304100c0b0a01d8154002400c403040094441e01c954186051440440d400c401120022403c0c11142e000400c1c01d090192522480013580c05524800040ca55000b0748000c000b42c0441103003640c50b98105e0b6 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 640571375 1250 640570125 640570141
    0xf040e040f1b0927021903081204031b1101140405130e0105010503011119051c0f05060303041d040230010b100906051303050d020c03011d030405101b1a 67
    0x80004c542e290244003c0300340101c050300d0020705160030b218a4070300070f070703211900c035a140280e0390000d102c00c103602c1c00d540c814003007011740140c4102d07a56036100380c080000e900281c464a884040c01c8107030038184001299a51f10081d0311308200d4014140181007020a5420312442e03900900d001087c8012a5103810004900c038503042c098950b1580314110441d0500b651100d001c00c1091840c0001028000d04011602e2444103c070307036907101050011400240220811030090a03550020003551198108005c107001021540c1407980c400710815000c00d4465855101140e18901603079a80800d000030701095265803150400d0481980200c04024000b4445090038412100410118032012899004050081e10310030000741454038021600108115600c2d00c83c2d504080640340000010b80042d0341544690409000b200440e03039405a12103500b0a5120140b44c0341c1c0510b0044134880c44e401d41c4032040035031080f640d041d4a000500f107000640702503890031590303221241c100340a159014034002001d075 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 640572625 1250 640571375 640571411
    0x40e0304050112020408010c1709160902090f0d06061505070f020d020409020907050c07060801360219271a0f030103050f0705060f040e040f1b09 64
    0x1500000650400d03080400644001c000c0c1041c4a1240741d0074400060850424000c10a01d12400d8840d015403400503418441c10b4100101980d20305c1d4040c081042d26842c00d150000100c0f6105000180c0ba849164005100d0032128031450354081c0113100403409110141c1d0140d0110b482d180d0f00b1007405030780070300e06a401d4016110081d00010844081d0405810000341550b54140300a01c0010100620307400100001c8096400b0b100240c1c000c500c0404c010801c0160798040c2c00c83d42401801980342c640b2141c0f1381c0551110f105001c103222090f0300d10100d00101c00101024401d4015500c9014008020704548546240e040000d0045603e004030159000519403441c006d100b4036845050800f03e456507a8110071941d0240040200b1540c0a50b00c40040a50b010790700c604080d141c0500340114291070440f50750012486607008216041c0f003564004100d400300c4421019a001d280e4035130a010701100d287d00c4d00a80782400191003942c5404401e10f01006555842500b0021035101103044052 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 640573875 1250 640572625 640572641
    0xd030b01141e28020d02190212010209060d09060c05040509040f0312020a0c0209090705061803071206050a0606080903250f210f1224080c040b04 64
    0x20340010040700204140707030a03003142180b400308042442c1060221945400c0c194800b40c030b410b1a5180c451075015a0b5041c000640c3c84185880104804264056058145950000c2c02031003440040c801d80c648007400e40540e4014103000b07100b540c440f03400c105030001070101188100e400d0341c6844407a4102030300070b0042e54180c401c0901a002a1754442e41c4100c0c00001e481c030150113110486078820300c00c42c410300042c42d12042c150f5076880800c01e1441485407444014282c440343d60810f03001031025860361000d81d280060856035245506491034007090410030070350003040d95031303071010103490911005411190244145800800c4003c0d50340d9800c50ba146000d0790f80c8446600f040200e00300300020101c44440740391594030b6403004001a0398070708600101c507503000c036049400e07415213070301440000400070400240c90601c903120a405039401040d40b819101d0042c013581c0d44040800d1405103a045010105120260300e5a610f9102c0c4900e9a40e6a040c20685106608199000300241400e005001c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 640575125 1250 640573875 640573907
    0x20a0e04051c0516060b0901180b091b0d23010e1302010906030f02040528060807020c010804050c0910091518180f1208072610030c080d030b01 63
    0x400c0c6121303210074500c0038007071850030f83e07409450b11006500c80d070f121352440b8001c2c141300d0346518043c0302d07100c0e0090039039000c0c41b80180b2a240480420212000044100f44c00a07111640f0320b55441d4000300d108000c10449030190000203c030094000310242030081c4038140d86403281d040c0b0155950142d212001d14914034004c1c001820a01c0030040c207800394101e110342d11822100541065214004902004040c0e59120031800f1043c00c00800086c0c0c06440740050441e0381b800d400745180003031002e13560385a01d541c020304000d01500050144042445028440f040040001d000c90070310742c1241d80e81c2500b44c0650411186404803c1302c2c000f001c00c00e03910841c0d8883c00c0c4803001c580144070850081c0b602d00300e81e5070790120340d03503019000a62406421100902c9401c0103401c0300d0400740020869100145010207004030305080d81040c00411500203090460400403008960310209108410f801d6540300508038408518089005040803909005410341603804020544d030080045991403030f0228211 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 640576375 1250 640575125 640575127
    0x190f1a04030f03110f03040c030c121113090501050a060e0601111e0102072f060906070f03050906040f05120601030b01140d24150b1213020a0e04051c05 67
    0x10340418041d400c07140c1000c1048104d40e041580d07100c0451070540c422601180c216480010078001c210324041184003515010418003012010b503030742c07100000c03240000d19200e40c0c0900714010001d2101d801661409a03c00c0080c450f50070007846200c042c044e24000e490000315100c0001d13440394402c0c0501d15103a87c604c8000c4c000340b2180703513a5101c0d0030110035210100b035408100340d00105d10300c2042ca0a1a04217084d440001005c1051005000300700520760764812541002641065a162001d035810710ba0402c620103501c0d805450309807031034810705010940000001c03600103041c40100c03a0080c11904240d4100c03881e0741c02c00d60389079100e803424000280340080100c014041c02c90000e2000710b44441c05804542c59154646600136403403203a1420810300485481c4062441007503000e1b135030300d0b5003c04600302c003a00c1c244124080d050240306280c0710b5204146c000940320300190640181b01540250881c21140e032543c0203480c20301c0d000c80c2c1c2540c1902c28008200d010840540074004c10f488507580300e03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 640577625 1250 640576375 640576397
    0xd0813150f0c050c1c0c0602030703050712090302091003020a0909030c031115010902042c0703021602122401150f0309060f0b01020705011806050705190f1a0403 71
    0x1a02c000e101900141c8007842506003120f05900c4224016075124104409401c01c3d4501d40b80a0082c00340c141c110390115001030012400207a000020b640c0c80561211480e0100240e0320012603000ea020351010750b11465101c00d002004031280101c00039240250360040d2001d441d210b6010554440d5000100010385600d008008240304101c8140e04858506c15500d1803c0d13000014101c0c400b003a0004c031411940014200a8554a800c442c46420545041404c00454101d036a02c420792004144405040d00014032034a82c0164820040c0010350040c010b11001050000d003e580c0c06035440c0700c45c801031107202c0f9441040b810050040c1201c5446600d0408400c650070100d0f6985007046900043c161039500e0400090b0301800380444880083c103001480780da01e00300091604460380d015605002c11603403540702590500019205031241401c019596148620f000d615082010040c210703000341c4091100104080c1d03401d6030f034109000b40304c005a10407600b459000710010546000b07001c41c0400c14070b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 640578875 1250 640577625 640577627
    0x302060d18061a101e080703090212070806010f0e0403050a0e03100c12020a090902072a09110c06060103050c16030203071a06060717090d0813150f 65
    0x22240740060140d039003076451a01d03580c610060b54450307850400e0602a140c003d26241c204203500f0f03150240d00307145c03217103042c070000c4d03411403000440c1141941004a11400124454040d030003080740280d020b0140b08445404105c002d4844586015041c0d40c1d02800700002041800d17000d0600945d00c0000204e072440c5c480756010f85941e80881c1c00c000030b00150003042d01c4160f80074420186100510000400d40300e001d400002c00f001e03450801100341d1441408034003070f500e900c88240c4094a058040c0141e43d0465420b24410040800030203007000b0700d0700b500c00341341c1c60008940b66007200c1ca581d0082c0071444980341003a09502a80c05941903d40c001c50009100c1e62194101d944c000000e00d5655242c01490400f50407a03130110700c01540541e0000036850200300460300540007207100c824101410f4102280092050300c150100605982480481c16048203d1001101d01e60301c0020200882c007070071440c210305c084d00b20704d041030112280b0080000e8003074890b1181d0801c10300725560b43c40ac0c070809008 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 640580125 1250 640578875 640578881
    0x40c17030a0507020315090d03050a1112060f04022214090a02220b04051216030201080c040e0a05090115050102031608090a0308090306010816050105030405010f0501090f14010302060d 81
    0x24007a0b92620600c0d15850207081c5c90040d56025904d8400900082c0d8008c4a02400340c440c00b4000640151602005904000c013140940e8034450200c044001c0319200e100003d40c905a007510b00541c010b2000481008003030401c1c030003070040000c6c41c1c40102155541c2c441d1800c0407030500c00068010501200060225209070300034401100e591900380690001d0300540c95003200560812480c0c4d0031300040a11580c50080c0c0342c400c814400e00d00505d2500c240703110081910b481c500c802414002d44130080742d010584038082c1e40151140c1b851b8030213140b50081080015000a03500c460403546010b11855045e002036208205495040c3c00a614080b2018024100e6451000055400801c140068406a501c6890b06c40c000c600810b0746640314045001010304003803040e445010507a02c94140c3d401d203a0103c080882c103c0b402420541e0300c0396654200503016081d40505030801c603141400200c1d209045610855041032600010408021804008800300c0c00a010180d40400140601c0f019244150 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 640581375 1250 640580125 640580137
    0x40b0103061805100609150f060509150a081e04110f040605090a020406090e010f050f01170f010305070b090f06160b040b190501060509210a030305040c17030a05 71
    0x100001882d00302e192100c5040801610781649010380310802000001124040c031034190b20441500c6d80381034a04100e40400480e644a00818020046140c40301341d07883d0118060300700a0400d001d1780e90f110080c0010300d0f20304101d540341400c0600b28410701c2d000c030505501a1150768880400005400210200308400540300030749648a5120240420301c1d4031a525020700810305040007585a0342020006841481242c00147c0481e105800405c6095001c082040403500d01b69054100030f071144004840038010007050141100340541030010b01540c600400381282d0241701603a003886e03224001c3d0319551103440082a404000040b050505261000003400e000c401c100e0700d060151401c1c2e880074640d1200311f9042e65521110020003001e1a03084521500b0f81d500440e013007005605020020b441400b030300000501a042e07a842d030343c0c0148180300800c48543c002408450808000341380c01000780108540881d480001c0c0380300002d4000442e4103681404142001031070920044d800e0445d0385d0780101d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 640582625 1250 640581375 640581401
    0xe0714092d03010204030317090c01091a040302042a0201050603070e09010603050f0a03021204120305030901060b03010b09040f0c0c020d060f021c0e0c1309030e03030a05071703040b010306 83
    0x40d6040405075800748000c000075413003a01ca123103121485011070b5a207208000c0c034180090700094103071600382e030307110614500743c4200c12443d04c910000070305a80e03000e001d180c1009400c5450901c500c1b0124640e0303850003e4240704049040d03207412008408a090b642e00b5200141c040d40003c07c248401001c1c07050107580003110300d000107021552502e0f2035141c0800c1980300a1703140c00c950340e12010305a051182c2800c9031000c1c00810b1616142c0481084203480484000d001c005011020071603020f0203411660050070503c081e80d4403541c40b888002140d501014607184244d140c250440440780c50341c0105151500541c0316801041016000e00c840c403102c400003190395680e11480800342c00c0003440a0030006603042c8101d542e1592031202c42d42280e28420b0b11030f0807684101d50040056540805810b10f43d5007521003c2000f8070140b5058a034403000c50701c1c490303040c0004a581d204441e4032102500005014607a20052160710780040e811620040d100034019001500050002c2190f64000b400f130b48a00c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 640583875 1250 640582625 640582699
    0xe0f0409121103071203200a05030a2d051503120406030203042a0f06020f06070f031e0509070509041703040f0503120f011703090f0a0f0e071409 64
    0x10685c0e815026201c0e1100450100c1d071703100410801031101810409103a404501075915000801c040500341e408000c064000c041c2d01c948904503d01000c0c070708040d0070110502c5402e5541071012144010b8801115103040706200180a2101c0385800140030085d504200c6440d494981001b400b1000b030340c4001c00503500012585410312400c41d2a0303c0604e002d1544004011704c413070400c001c140c0c014040380d0041c0c0c115807184a505c0024440441c1940e08201641408816a50035050a502601562003280b44c0a8407105400e9a03403882d03608094850340c5140141c41100d030711001008100b00d0700b9103010f04a00c8020603401c90402c1404000c6030003d0003028410bc10300450384d1131525561043e01c0f6a5141d21008007400080c00c0c403019881e014105440d039040502611231a00c0c0e540313014081925102d48040c440c0d490407521041107000180a410080364200c645400c100603403d402600c9240010740109200e0380c0c1c0f003880b002901c40460307004160071038990a9040d8030301d05541e5841101c0483c09 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 640585125 1250 640583875 640583887
    0x1b07020a180b03061312050c06190f0213030203100c020a0308040614090f010e010c05090103050c0c240c13050d05010f0f0b09060d030801030b13020307060e0f0409121103 75
    0x740401050b48a10040c80022000c504a41b4001c0c1c10b8684441c80002442818440c800c1d038000040791481e44494008903031500c415101c3c3c0008042c0601c6200030700c4c014400260440f508500003c54020799000390126101c07074403284807400488010005d81d0005030449030030840004d2081c01016046805400082486200c48005000a000070743d00010181d01c4044803100540c02801041c84001c03c0e1380080203c612186009022403080000c80341c101503903480010109072820003075540e0130f90840101d86060306103495228414610481c010360301801c200000300c2190b007040407518182d20060740c1e0607505142c902444841041481c00f181c09540783d024176540c450682c0f01c3c041054030380b40004100c1211500a10404a50107443d0500468010b400c4401103030704030030520304480d4008051500390307a07421a0380c0c00101c034205000354035000f540000944c0980c000c0304403840c00750495001c2904140b000401044950584c402489500503130102c900c0c043c040c9001c0d01d00c00e9800c500b0740e45010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 640586375 1250 640585125 640585129
    0x21040308040b03060420090105070c030b0403080601080a0e0a0609020103090615050f0d02060306060a140c1006060f020c120c0604090f1b020615010504031a1b07020a180b 75
    0x5009600001010b0300040104004ca00d00740c0035a400c0e41c400d10221b04a80b2401d144544282d04c21401c40b28140440098503008200010032100c000310f070410002c046508252400800200055941a0004105102191000c0d2940c81080000e000385001815400007540d03403040904089002030f41810f90b507040e8003000c01c60f10f000301101c00b0168960300603110b0800e810030032103000341564280910300f00a090b0f801a02c1e000d040329044031088408035280c5041c001c2c11501c040c440c40100c3c0c0f03010700c0411150080e800009160700d5409003400c051141c00d031520300858909910006e6030707005a2081001841c0340c01d0006840344030708100800c0c2c802150381340010560035071040d40000901552000e00e00c0388007200788120070841107040c5590119140507180250740302d001401c1a64140708198101075540c0c0518111402550b00680d95030414540b54002d00d030492080310602d456102008441d0500c68036001100e082d542d00800c2c21050f68101201c100c019000444c07060f03034155850402220316 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 640587625 1250 640586375 640586377
    0x260a0e0d02010507180b040905040503040503120a020106120b060103050403051312050606010c03080415020405040e010f1b0c060e010908040e1509060901060c051005090a210221040308 81
    0x6003080303400115032030401c1480280684000610182000341e4050301780618001241142c04942841e0408540c0d5242ca0405a086100da03a100e107505d80b054400846880c0c159901600920308590001c12901d030740c6801e02031303020714034007002400500361000180c56580640c0c4081d802c240281381403414200b50507140204000d150708000e0043c9030191084041040400200d60b2094080c6007a4030144003d560140020740007400041c90b0209810150f48000040d60690b40103140052040c0000c003102c40800d8000c140c0394210f000e205082040b100103501e2642c01108030001d4569940e0468411034440500804107005590b4541d5216801800810091006072025009d41c1e602c0d4003007424555051445641112034003401030341c1c82000c2200d55521120354074119529401c00c0e81031000c0c0c9242180c1051411001142031501d01014440c20120000307a9080841c814803a0f465000e0a04010088400e000c10b48131b03005034040006203a4000181e001c10611a504441c014240b03600d1703035036043c03913 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 640588875 1250 640587625 640587643
    0xb0109181b210b011e15020c1504090c0c021c1e061506021f0c022a10030513061d07150e0f030703030f0e0909070e07260a0e 55
    0x20b140101121041c0050303107541030300500710000550720604100d80040c0400b5424810780040b102d0480b0800902402070165410020005100142c14040a484800141c01500442107111700d40140d0f0b81140d800740b038210030b600b0f0b001003442d540d0304199525a1075403500c2c22000c0340d160840e400880340342d2080301e4010402910901d000305011000c1c0343c451480e0341c032581c848070466100050441c0014011030140076004001c2c1c0d8086240d03548191b05078a0044452041a00c003164410820a03000c295041254905011548050705c8555900e0880a4030030903601d00300c409502d0840c0c040000c50581c03080b0108000e140c2c400146000035400c02e41003d10070391060200d45102d0700000c2d1015404042007142d0b240c2202c45000506040f008a82d031800036020050501c200c6c00c415280d0396004008041031034100405082035442e021008a8a852161041480c10f2041a002c00d02302e900030340c4040da42d590312005298000e09445500383d401c0001500304c010380303a0340381c070f01e908000800d00080003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 640590125 1250 640588875 640588919
    0x50405030309060610080a0504080f031005030106091413020103110705010209040b0a241809061802121b07060203010312120618090c080610030b0109181b 68
    0x610707864110109414440d0044c2902d208140d410401070b0910381140540b0b80024031040000764542c0ea901d461465842524003443c0f0490000c0104100b00010101c4a400c1e50810b400a00c5059075a825400981c3c00c00126624a41c500e4000510a0340100d88268100307401454046059100e00c409071040e5071080800b51116500090342c0c1400b401e0070301490f0345d411800e5400c208682e02d4000c0c8541c1e1100000e1061221501c51341390a22003038840c241c1940d241e0803d10822101d00d41d10052075004203594410783c00301b0780314081031130051415442543e242c0c1490406034030140da11404881c405d82e06501103e80c075000140113443c00700e1450300c0518081e611a02c1c03181004102c40e0b50191401c2044185404d00606010080c802601c400200d003004410740440401c5180f15494420030490b6550096075440c403e0008001040900619a000302da00850700c1590598075140524140c50594955090304d006c3c010001c0000b03003040700001c80b0815141c0100e45c03115111001031308142440c40f1068 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 640591375 1250 640590125 640590127
    0xc031e0c0f060708040305181207030303060e070e06071b0b04050306060909030a0f0504030b100e10061b06021204030f02010c1d06090109090c081e0906010e100905040503 75
    0x440c400003006031018101040380140b006190800d0020121080140024100500864032405140340c551841071600c00007000c21000c084c24200c0d1590f50489403009500190905d4000901d9018040c0e805020300c8541e65800c00701242c12080c0003042e807206004507404602e14060307030700e546103901240c0054044000e1840d070359844d041c00c1504c0c0c40c40244c2064800c240d0f01d0305202145a000045420130790150074031100000c20550180d90500850780050071102030102000001000300b545041610740240c4165082e850310350340100854614080c0d00c0101d90404100c0d024203030030801100d032481c82a4405450708070014240200c0c500c041d2002c5007c41c0c991102049020380a004100462040785000c89040e40e1214442080034120109140038480020700c1e403900b64414090074014200000061004c0080718400420a0f0400c41d582d1000a14a201c00f8480002c0f00b003069000eaa68180203149907400c2644003645880042c003403061a0803030140000b0704d01c0c80350007554425401030004d1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 640592625 1250 640591375 640591387
    0x15040f03030506041514121219020d2c030f060601300509010b120a03090f180b21070509090c010210090501060509041101020f030c030f0c031e 63
    0x40e0a035603010300704503c0f5900301a100018000201030540c1206d00103800201c9608607030000c1000c0050014004180340905400103e055280c0c1009040d00c5040d484000c2016440140c1203032506802500e04000500c22507031825408400c01d864505400b001020503010054880024548210303033030000750581002d02040703860340c4c000192100304038400103180400348000103180740307400141306c0c43c0301c080e6504c00210396120300950240426210103005040d0420f84248825550b9018a4046002640741c0070003040080101d0f0b0140100c558030620054040500c41b040c3c0040d18468a8550b0030802034407203129400900d081819044840070054103640d410002403000441000340300e2203503a0701c100d11000c4613036800518112408040c03180080c200c031aa01d0803601505142d881507900410b00d1040c441800030700b0b58a0718012000740c003181d41036003402c0c41c0302d0740364043d14a500c00a90002c3c016a0941c2110000503c01e0f0000d900549180c01420850000c050354501d0682481620200341 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 640593875 1250 640592625 640592627
    0xf031b041203020c03060c070b1b07080d06060534050105100609080a03050a05030709080703060b0f090403140a030f0e010c020d030207021c14060403020c010318170304030215040f03 80
    0xd904d40748501600900600d142c001030707020240c1f088a10081130610b40c400083c2e0b00300c4a288000001342d21160099079118010700740134806422240d8109009441d001c030004142c1d000310102c881012810b40c091000303c0c0c170a0520320310f02c42c000250001c500020390100c80064030038070505105520380c01e13488840b6801e01800410916241d0020541071f40300f9100c41c00400e40090036500c1c40b1071145401c903a40d654a840445008000358482100c0703109801d0701004000c01500030000038181901c2050b16003900300200000c8000503503024010a42c00b40da40440c034106074004100c000c0c0c150402003500d10740c9246403012140c1d14140c981160350b4901c003484200b40d05000c10318203c121840c0960901c05140c00084c0991919008544004903000400c42080845030b2070710288000902903d081d4a05401e019403200140380703189000034034180d5524803501c0c15000c03400f651034100e4175a08035025480e07000100741c0d0004d04280d0561040300800e805081c00520b6644c85140b10343ca127070812801503d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 640595125 1250 640593875 640593883
    0x3021908030a0b0d0f0b0c0d0c0509041802210109080304061410030b150d080a090915080604060902030312040309060f090b0315040f0f06030209100305030f031b04120302 75
    0x40c801d403040c10806002004204030b05d0319140000d800004502031511000403044240c81000800000e090034100006d80d85a004405400e10f09000c3d10280442c1c8010049a00b0b10b08000e58001d600180c008500b0461130607616241141c4070300302c000000e6001058444c600141c004071422182c6640310744c0c1c0700401514422820303420055284200220301e0459032070b11a00800101111082103880080074840d581e642c0c0c210f03070b01c150008090741d510a005500181a00101d00564440501b82120b0110140350307050003004995080c0e0290000c2d031603a6482074054170084105a81c188010311141901003811282507002c0c80c0300b5180c3c0c00401785440320107089041000e80100901c418004200607854011701201e034401d0711804289a40349620b00054010b10081c1070b840001032406014a01c1c030f280945c08901600d00850350301c0850303542d0340d401000c90300d528080280340e90410b00058400c069200003960b0000c01000d400c6021841401310072446070000c0e4440b20303e105072421901d0505030140 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 640596375 1250 640595125 640595141
    0x5032116111806010f0e0109091a091f030f0206130b041509121e140c04110906070b09152716120515011410031a06030403021908030a 59
    0x41c02c089814a40100040c040c002940500414000074440c00009680324211070809440c85150400115000d80ca050070074a001c101c030140100c0700030303010900e103585040070811400c41c44980302c4130307050542e914401103a074422400c981240b4240a03041515280d62181009401010042526145801043d00d6541880c1c8090301c00e000030b0410600460056003890040030387c1049106010494442002010b46404d0401400200c84400d0000030000089003643c4c5c0020308030380510036610f150241d504079110b01607a00d43e00130360400c040800101241100340d40100c503d0180e60315286000010035400d03d0480c1c1c1d014040b181743c88810b9050100ba981c002c10b54600000410208004050f02a201030650003000911030751180640c081040802c000181c42c105075101022030b503500d40700c4010b20624403540b1440b8156079005099070622034828000680c001007019110044a00c0521140303a0015106504500400700d00d80c85d01400d001c0c1c40c00409105240d255500e2a02242540c1152510 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 640597625 1250 640596375 640596409
    0xe06031002040f0302010809030c0a03030b1311160c03050303010303080109050114090a020d0e010e032d03010308160203011d01061202011d011b0c09150503211611 72
    0x521052201a0301440f803c0240d070b60a0a241c40e482d210342480078514040d0440c001c9c550b00c1142070708020540e05400c0310204640135034031103280c110900c44c26015100700d800705030f46460b811300081c010700c03030611450b00126004a415200076501c0e500c0b240d007194001d800a0700459107034001003085000c14440c07240100020300d200141000c400000821006018003001c245135004182001407041c164010300400701000002c02c461501510541c0d240d40010900416400480302d8848441c0f0030113003d0010304104008140c13441e030a55996080c590450038641c1e201004240000300141c900344a4600f001400e5201201907254421180b070035101c09800180d0021601740d21a80140d0b0070038682500d9824480c420107143da01030004a584a100201241c40003800662100501030030014030004d4410014050040c0301140c00030350300b81c1c04a8071540e034059008000820301043c039001c8541801c11042e225078944810f840d07607400314000c059419a6599900300c03003000c5602d0070403902c441c24149 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 640598875 1250 640597625 640597627
    0x8040b040c080a0c2306070320100e0c01020c0102121c0501060507051e0c09130204021233010f03060803211e060d052802010f02060108061506040f0e06031002 70
    0x17a004120240507910004083c0035400e5264608014002038009440c6030220480d01c22216001d0300401070030401491840c20b0040d48941400c030751001c80c8071480260180c005101e2200b44561051f00795204411410403019403400d201c200d04010b000b1940209400d5842d0780e20380724607080c054140340240309000e400022040030503500d201c012078046c02580c0c084454849590320070008170b0600a1100c4002e500c0381c4002512055240810311842c045c68000a10418107404140001060002d0211410000c1d03140003074a042076201c0d0002c210710b4440c0d0700d40890010303a903810051039900130310b0784403415500a40303507840003015842c80e0552154141c0d55040811803540d40707040c00c0407405440c003809410440c1181c002d0000400004c180d015800c40e1600702c00c100b196950b404c80c580d0040c12400a030b00042400079651000981038180d80301c44c40684900c0d242c4110b0982c0e00342c5c0c440707a0349420034800c0c0000189600c5a41d0000000c281c10100c0240d02e140c042c0825003090301600c422042144 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 640600125 1250 640598875 640598939
    0xe090103110409050f0a0f2001020606040504020f0d0b061311040605070c18020d050708040b160c0b0a0203010602071a0a0c0809040207060c080702010c08040b040c080a0c 75
    0x1248080c65200c100041e1800550103c05041c507a08100031240340030a503100315000b6208126141c80740410107402200c003043c1c0c01c000d00790106001800c680304940180d0000c4041845031030154801900075100400030000b840320704020424007944140140c52904000041000758240900c1400c61401c83e55070400841c2400f00c0c0601050240b400380108010020400c4420130030301186031800f84c502283c600480d0102d33800030b03c0280d802940c102c0c48843c20000031400c4140650801c60203158008000402c990300c203051284030303d11032070080e002c100007011040040381034021443d000d030390591409a540d40c107003000039140c0b07406035012004040c480c1c01e801e61350326494400c3d035a1480a92070440010038050078120340f41d005111a95a0041c8001121000c1120590028503402031580390036003a0743e10054141e0032200403c150307501141c0f80d400064009200e030580e03140d2082c41004641007081d10348000300d242c44058607044030040144101402401d54401c640d000341501002543c40b040 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 640601375 1250 640600125 640600133
    0x6101e0306051e030a0b10030c150e0418320307020a060c02030709091a07030e060c09150c0a06140106140915030a06090f0207030801090b0f061b03030708070e090103 73
    0x4900310000d00b46c0902c00c8085095464150f514100070b64008410041490700c54019126000701c1c5452040860b00011201310941410b0140740929522052902201d8241d91500071000c0c5801c0c00900d880c648118030351042d4403149810b41c2e0304455602c01561200b441340305102603001039401c0f00c81440440884200142c1c0e0002d54801602d00508011801c03004a00d054003104192032103a43c9461070000801115070b9056010804a005400440380305403075409500109214114521790400110140c140340c40718248000d1070364240005c21100000015101d9108446a4082009850382a100100031807907101014803520000d8030040e0b4908140000090443c0c0c2900c0c140440c54034010002075001c2e680c5034801401007040c00810f0200e1161104101c0c001e5003d6681140841c500700004039024510f446003070323010070f000b0b031514039028485800c002070b542280600d02c407401c040c074801e01490403003480554040c0000d034844135104d0401d4407015100074a0100003074056030103074004001103 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 640602625 1250 640601375 640601383
    0x50105030a03050a02010b030a141b0108070e0a0b040b0310090618050720060703110403050a020922120306051905040506030307051608061303020606101e0306051e03 73
    0x41c0381d15042c01031341e0b5032a69009034003400506009640c1401003420010030f20000203803654404580360700b900c091101500e80518a05420104540019100d500294500703015818801881400500041482c1e60302c100c002c0050740b00340c00c00030b007141010040c0407002d8508d90416020f060b11103418040103042101c981400401c80034580c98558a40000c00d241c2e9001d485a00010b022103040200580c50f144991135032040c0030740313500001038581145c01e94801b50000035235080e130b0b0b802070240c6505002e039020801034690240140d41d80b001044849003404000866440074a40324880090303c101c03600401a0894031380e80d000d030b800390003980380d1085d17507400020b140c50a42d00c00310740c001074586942000c00d00c0d41c02040001031152054610312045044c1c117804680845240c00c089450782c1d07440c0341c0e02c0141640300c0040100503038090008a54039150401442040c90700518000f005100030304c40720291072010034121000709a45810901007820b00f00801c03072a0452240c0f00d21034482c02c2202080c0e803 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 640603875 1250 640602625 640602643
    0x9051203010e0f0c0c060f0411010f05040504020d06051c110402120406090c090f0902090105030d05190c060c0804050c1203041412060727270b060315120105010503 72
    0x80e80c6614400030f214401c0302011749000a55000c106c94032481c0c860f2410f10024000c0c0e50641f291490311494000d250320134814400001c03155a2180d0810b4603000c2800b000c3d401a0b003042a03402d40f118800f1904c0c2d126200ca00070a41902c45416040b0300712030820000c00303603c40c1034840c01140108590b800601003100481d42081d404a00081c1709184c174204031803003203500c0d08405510740c14000c0c0d61100c408542c11500100e4001c54803402e40e80d0340c440406541d03d22900d84000461814400321540107008000c065500b52030707003840015041243d5410b404c551041c182d0314040b0b0b08060621042c40420030080d510003078252100c012440a02450304d580e400b581c46800b403c42d00000c441003080e220003603942229050041114100e041058000c5c0900c901c0100100102d005404070800748594030041c50229414102507010b10b441c594004031800c4403500103040b02a459071940c09640c0c0358840110b01c24000144c081250404001c00c2100040d0a41140202e80c1e040000500c0142d9000c182c40407 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 640605125 1250 640603875 640603891
    0x3050f07080c0901090e071d06070218040c0f03030807120b1f1812020102100c08060f0f0d030210150312031d060903040e07021b010509031e0109051203010e 69
    0x42c550381c107140101c40b0760005e50410001d810915082c071500d2070300503081c088071038564211840e910701044248900c41c003031010040d50001e403983c0c010030103189069481d40c10600501c010300c68240c8a802410641c0740076803040b400103c0810401916561104284c1c2c4001030b5140d0600055207650700140c68000400280200d401156a844404a004070507040e041c1c040a0303400200150350344101031146484003016030140c0102090304041030701900c034800d0884d82980326040340c0d85a90040c0000040b4456419410450034582912a42d0314407904018541c403a41c0104907580d0002403038015519407507203480204048100c01d000040c0d031420580d081108a1030b00141010300e0f05d0400c42c9032010f64800c00751901641084c0500c00c04040010025034490b40c441d0301e169298044103c4c1d03100792010a05007140744140c101003035036101c2c0c0020102440c0040403a02107114600d00039003044202c0c6e403500d242d03179910f40780c0c001040000d2055200d6400a80210381c1150b14003003201c0c9400c1c1008200c11 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 640606375 1250 640605125 640605127
    0x5030d05180c04020f040e0103061a030325020103230403020c010c020102030304080a020703170310140f040b0609060c0606030c0d050712060906050106030507030b101d030c03150703050f07080c 85
    0x844905900c2c0146e0b0700410400d0840342c402e59681c00c101000b0f0010b40d500c2e8480301c1040d50036440c1424000111900c040096181d650b403c40c07000302000c640600604124105030f00e543d8404803803040c00c84484c001d040710001e203c085080601e006881c00d0880c03000281801251605000940e80100540b948150004001d554035100c8200c124100031090300000e152407680940c0d0520021004003451160741c02c040c090500a449100ca85450404030f20100c0c1d01040b111280c0401c4e0515401c06101040301505450900003c040010f1094211690314030941d4007003020040f10f0300c1c041003450320450003550100c28014a036216a603d40c21603010700f2524000f2920031104020280d84110b40341a0042e00c1007006584804004002d02019a401000a401d00360008500d14190010b4041c0002e0f07602c6001c0395003081600d50020003881e9000540c0b60003070625030303a0a83c50911142c00d07024200c808075605442c090402908481b0007a09124016407048104025160440405a04002994a25 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 640607625 1250 640606375 640606387
    0x7021905010b1012050a38060d270201200c0d030f02010506011706010c080705030f030f07050301050a1a0d06060f020d0e060301140307090905030d05180c0402 70
    0x3803805850000049500002da041d000800e00f603100102180c0407040550500c01a260040da90381034400e68141c05e06152500104030302c10116100908180f8808004101040d181400c00900d0fa6000011145125900c424400c0b00f030348040021140c2d180d5584400ca0148079142e00002c2124582c44250a0400300c0000008420a02001100f51500004003809035003c01482e00818840300d4600c1d58015600700000305d1003644c025802246005aa08880459551803c0044480050400c810784a500d0304000b81c102142c41840184400c58040d00019a07a0074550480101148001c0910003008401d1006000b41c0d03449001d900129455451542117654811392010141e200c0c540e14071020924242000030516081542400d80c0704098095940200001200350b4a00c3c00c04042c0d203030301c00001c0005000c11200185800e014000c0038044030410f60301c40341b18400b20362110b070056450b54000325074800501d000d40603940d4030440d4040061007500f410303543c50f0b40c1c030b440002c0c0c6c4c2403107245c0200314 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 640608875 1250 640607625 640607633
    0x2040f12080d1107060906020d050106230a05040f0f030209070507080f07080909072703171608070b01180c080a0905010f090809040f05090303011701020708181305070219 75
    0x13500c2c2510f401000c2000750500c40e01d4440d000394020b4501c05800340c02c120000807000d001d01c0d00f00400c9803110f100b69000404c90308044a4940c083e801500601c0740600c00841c03030380140c400407405071240c25100102d0f103007180100403d551004180400b0880100540e6000448004c29969000d80610b040f81c2c5403492442c20070382e00e0241030303006a0003008039400c008003d030f030040c01d80c44181c419001d821a40244a40350041c10400c502019000c034070306410141440401c0002085078403d015440c11000072160b85100c403d5200c2c0c20103950301e10003540117000d02d0070048070003030a074140b0400c100b149002e030a1000e007000000500c0001000c0c0d580142d14184403081d000140c841c0707500502006096502d2a11356056000300707d900740154500091804902c001c0d00c6081d0003180301500940c1541c1c81d08026540404a45003d9a13045d5020311650b8000b42001018000090800c07c01c2d2a024000c8000d01400c0054903000159007806c050500620540200d0001c0c02181c1c000501101c0e0540c0d410 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 640610125 1250 640608875 640608877
    0xc19030b0603100f0902040f02130e04021801080f010c020123060103060f060314090f06060907030906020f030901141611070509041b12050d0507230102040f12080d11 73
    0x30103260b9041c184011513824841076800422014406c0301c0800100c504405604100e000d000c16080501c10303441014010020301c80e0345c2690103403009040b112031613100100c2c5821403000381e1081125610400724400c1d20764081c011103680000601c0200880301c00e084620300d41d10b07a056604070081c003140010800d0399100c0d400080c003a2034811518000c0e103607038060060045c881401007405d4140e001c0041020484013140512590400200508071500c581082099030400982840103242e900c61403a00010b800c1e0008e00201e51030040c50795102d1920800d02401e45a0125900158071520800c000c0c0e041003400c0807500c01c3d400d0749844035000428142c1c01c1d160440c25001254045a000100802c01c171000b1a04401c500070004030f40d0203036603140c030004414211900300501030342203041440156407241010b001034a0007803c1c04030002030855110311004c84001485401650002024010100301042544c024000a40c00310b110107203a890b1480305015500d110364411361541e4058070040340d504 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 640611375 1250 640610125 640610143
    0x12020d030f031d060105101b0305031e041b0611210d150f1703090103021c090c06030c0203041404111c150b0405030c010e030f030c010e0c19030b0603 66
    0xf9040b10003410810100c0e6074410b0241b0680b032090440e003040301300c00380c41040e0140a4107030042e0000d2003085240c1d0207455a40000b02071000d400e03a40c4030301051002c1e0315550a801280500324480000300c0c41a1180030046c0207030482018041e02c400b0201a64000165110011891200b0f10300c4021a544081c41e9500c918444440d0b010300b0304440f141009200940c0104440c01807000f13206050f038542c143c445103200346202c010306401c14415030f207203075010390000c189440118841d2044000030341024421501c00c0030060b18550510403042c0f10480c3c041c4940d500e030754040c2c0015801c10b840c0824002ca8413002d044800e00440c2c079820300c0b401003801e10080e03411405403d010f0201128101c44208020f010305051807031503c1259200240000200d4101c2e0f003900e1004d0043c009c0c1e1007914006681000e9400031140d090b114948801600050600192101d022810000f107900425500c4051608828154a600c00c40070790b090000c05000c4008480100c80e8400d030182d1b0555182d10010341000045 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 640612625 1250 640611375 640611401
    0xa0804020405191104050f0a27021c05060102010e03030115051b010c0c11011b0b060f1309020f10020c090c1213120f0503010b07050321010f12020d030f03 68
    0x44c450886800c0c042000d030040c4d07007003918440c8042401c00b04004040c000d500c10b414104400d002035003080d840d03600e4801000c0b000e9020142c90011011100d8074010130a0003207616090380e0b43e00303101c5950b0382800b1712000304a58000560555060030458848010f40078604d205105d00000c118425070400da40d40030300140050020030070704e0620600075040d4942107400b22000501800c80720001d6006a400c07403082d480040c10140c0e1440166035000d26900d0290403607038026801403000c90300380d448200c4e04040240c800c0010072105000d105010700400303400d200b24400e154214034005480e130700023410502248208e807490300d03c0d2100c510b040264860825010610300b4120104000c81c0702a130204100b492041a0b001141e10741240c0c201c03021000b0401d503000007002040100848207101d805800c02600910540345041100842c0b807491390030814080d4130510101c4c004000c0c000900180340001d103412a28071101305a664000388200481c0040103081c0800c1840b018101c07446a8000b03010a146 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 640613875 1250 640612625 640612631
    0x12060f0b0918011d0c07050312070c020d050c01030e010204050f1504030b04121205061e03151801110a0f030c1707030f05060303090a030b1b030109020703140a080402040519 76
    0x104c3d130640601d48a0399201405020000010680f003041002c1280c0507150064055802d0040080300e0900c1d001c80034203a002000036241258002d0380d5411500d45925110f18010720000e6000c0780007405031907001100c601c49034414401000617403106246d01c050b14204a0f6064850b020b00030051486000369000504012900001c220400c104400c0601070240c0301c0e103401c004140f10010b040f040c0c640403180305401551f54a803c621419125030242201d02c030003010780b20300703004044140720000800c43e24132040080c500c600700c9a00c1c5003881444115144542c0c110f207002810003004c1c00c00d0501801740410942c1c8c81c04099100303445030300e006512840c4038403082c1c0141030208004001d401e42c0100d01414070301d03200c045011490b0020840d540300780090704030300c0e14915548038100c400400418044000d10400940000410b9101c02140a40505900140c884920341401403102803c801100e0b007030503040181d000c81d1034001c0c018507405981101c0c0031a09a0301c14a69080c1d1064042607449003d007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 640615125 1250 640613875 640613879
    0x90905060a0f3c1802090910020a02010605040c030231052706030106181508010204030813050d0218090a06023001060503040803090a05030d06050112060f0b091801 72
    0x514514161040490344000075100b55200394510440d1420358012132580086244030006050842c545a848200b940c150f80280034000c1450042e80d0000216070010f07559008240200c2c41c080c85810a60400c6250840c141500c0c008108000c4140c0861000c1040f45081010424a09030140c0d1010f0680075000c4403105022240180e40e50f80980c6a9255006c954030004600f404e05107e40300854801c1c0d408541039131a0100d80a00410b81007100e441c2d441000040490001401d00040c402148140c1b44550b0341d0001c5140d420401440350480c91242580c0c501001c05680c80808a80c100302c4001c03044805500c40300040b0f8034000e40c80000514280c00840c482e04901409c1400c0f06280040c0074018000700d668500c1c0c04d158420074014040070401c140040707800300e41c02c840a11b43c0010603000b1210160010b440e02c1e45190000180075101c1529400b0038460303075030b009400301b102084030b0b0700c148a8642041c4807000c1703850441c0284a020940800c202000d6680d0f02d01700a0b1020b210500b40005503 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 640616375 1250 640615125 640615181
    0xc0312101d0601170601140c01180812011a03070e130c090906050102030c030336010903030c0c0309030605091212060301230610090b180307090905060a0f 68
    0x61400c90703a0314080b81d104000c00f60484c0820304820b02c1000140d40da2500284030800120b10b41d080602050020340d47e80202c9081503091401c6460100d024881d000d403241004164440c0c0d030a0160010480910381c17015280d03900d1030480070f03030f0780011042c2840c030a80d00f488004106500c1c407406a24481ca8100001c803014150018051000d5070b80c1d85200307004d02c80d100c4005913a02c0c030559141450503881000080c0307410428100d81f4100f0315150a041211008030381842d040c1036032181061010b0b941d110601d0042540512420108480a05080308005100d84024042c0540d62101070425615480015003c800501485040c512400304c1c1035120004da542c414510030048030403500035840d1060302a0021000100003009140c1100602c0c050b82d1028144000b4440341c41611049c000b80520104010940b40e0140007030740c0010300c0b0b15030101e4800c1c040500d01080b80d40602e416514005c0c0d2030f404107001040041d8807041010000c9500c0e40300010720b800501d00a02d1119080a6150790740c4000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 640617625 1250 640616375 640616429
    0xc051b0d0614100503010207050703060905010b1003050703060608010608070c2a0518040c0311150304140601051c170c0307030801080d08060603060d0303090b1305060a020c031210 79
    0xf000002d1501c0400da48a6051500b01d01c01c0030070107051584048020400121190440351800c0c1c481ca00214507950b1503404101e014841207131200210341c6400800035280e0345803242d100202401c0c500b0b00d03415454418003404809006d00910100500403e0450621800e001c0180843c00c69013801501c2e054a40c1c21032110240c140551407054020b85281d100c5540510720323103030082d60840f02d1602031501c0d550b140b08400001074001034025083c0300400c08a05da540000c0c52150b07009807003003034480c00c00d8903e082c14400160407940c41014140b04030720f001908006540f035910f91010107451805280001000c05004903400100c4900c000036801d020140d01c0101c3ca812651a0011070350f1244414005844140702226a9a08a0700c00d000103403981ca8180c240c00d41107406030a001504442c69141c00e000100d085803005541c0e41c42c011442c040100400120398400e00000381141003a1000003401c0e101c0c8500780c11164620440030200d801650184040d0000301901d228410411280e9000c010f40 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 640618875 1250 640617625 640617631
    0x120f020f0d21050c041509090203010e04061409060a0906140903041a03370e010b030c010305100302090402120303072a020f0402030a090f0b010302030d0c051b0d0614 73
    0x10316100b40600d9102d0305014010305002c2c0803452682c0341440d09201101401d1100541001c0030414000c20002da0720002e0320045d0301819055803684c1c03140c601406c0c140c094030002e040b400c00440c401d500308074089002051964106050703481c040b541c0c07589030815002904885004902082c0c0300e205005200100000074400c45440c01d40418402c121000e40302c0c220302007129881107443c0002a200402c0c0e101f98031203070105c006001082c00000d000c003280e400701c54900b41414a180e545442c41c2105107001c00c40864480001d18082c40b9900d0101001c9034100c0d41c9100c024091285103010a0456139210355110740c1c44c1070002160b48074641100020a000d40c4480315224240b03d83c140e10f5010a19100d88040c07854019110b0101001a80d00340f00c000d5000404202c6070726501e10f01d080000b142d040d0341044084c040c03441154654114010503041445c0c03404890180b003502d030301c500002803010400f1000300c0f03100b009406c0524540c0010944040e00b0304c1000740380da481c00c0798800035442e203e044140 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 640620125 1250 640618875 640618907
    0x2040812070309150905210129032d0307020907351b040f0308070204060501031401060318060c1e0207060e040f060e01080601061b120f020f0d 63
    0xc61581c0e0f1441346032244040340540340003440c2004e00380890704050003084d442440c0b00710101404003041d0211070840b4050a4030b50304101180401551006c1202600e000e080030443c0601364480756204000003000c01185103448040d001209126100418402d850005801810000103841d009100400502c2d000e042c4441c901902c91100580c4624403040c003004000300c000000e900e480710424900b02c204121080702010780104004510600c41c0a15070000b14443c1a40c56100c0c10188100030030707544d881d08414101850321030700341030362507081a400c0c0c1112801d0900180d0050320340e18503000c42543d05006020f85042c42412042a40d00880e1001c01000070209443c08049000c0c00f2130300c590b918460440003802c03144401140c0d240550140b0b80ba5042030200123010790b521000380c26120400d0f880b000d92130304403000400c0700540148070309841c190360100e0503d400001e07070b950004180c1c02d242005d04011103806111145402041451018000321049402c1c82d072014000400720301e10200c88203 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 640621375 1250 640620125 640620137
    0xa081201030b0c070b0a2d3e0f090402040f060e03060f01051908060c04170f0a08030601051c1e061d060105040f06020c0a0503031303060b0301020408120703 69
    0x1400054a01c0159159076070b1250380400c081e1180d503101030284c21a0034107c482480d141c4031007510806203c640c0c160500d1200d0340070410250140300c0b0004030f8121800311115941c40120305400746a9000f0035440340c441014095104d00b45008408524000c164105811602c0010080742c04664246c580b0700720b5032240d8401c07194a403440249511503200707589881040c54a4801848039290081460031801150400503204940d96082e0340c1c42d000c400c0e42c000c03510341ca00250510000101c16414107a0081e20b40081540742030080856079910020b5034003038656030000c40842d00582c03048003291300120b200c2c03403520b1081a007407000d0b000506010f419030082008011648001c544240540c00464070800b2a60701c170503140140b800c100300d100a0000f81009000c00011814035108a4000003819240e401000070354035410a111110070107401c103900c02d500c2030106007900203403080b190051300d034072410201d83d1200841c0461b019000d690080341003401805c0c1a03040e0041040c02425009020b580c0ba1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 640622625 1250 640621375 640621381
    0x90c0907030b01090302040c11060f0f060a18110c0a0606150e060d05041a1006080106090e180106080102180a0902031902180a03030210110405130e0a081201030b 71
    0x1a81112081c400e00d90101c1e183c000d0400243c87d1170380c803080021500d800c03c0700100c0c84095605042800485400b00a806030100340302415000819082d071180003900c20140240c14000100c02d00c90406030520340007500c4841208200c0d1150041e2901c503a2100304030303840b880c441c2ca07004016000c14015018800c840f654840201c52241071030803851030000c0e18941c50444064056400380c080200b080d03d030070080c1c90040c04401404086580304042c404050a842414643d000f4200380060b8003040030005288428000481004d05503501328404017007525451103016013250251800c1e902000036544041001000081074030480c00510900702c411a19107034440d4003c600f00d0005640040d40344070f50440c3c10700300001a5005040442e442c19018032103190907000551108481e030801c40058201c18420700c2c16405078015000c1280c070006105080600300404100c41e0703a5030082c11a03540d07448100142800d001448144e412075080f03a441c6644070050840c008000d00284012906a4240000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 640623875 1250 640622625 640622627
    0x3011d1b040510060e060f03010b07030e22150e0109020901020c1e010c03051e0702011b120c020103110409090311010e0303040b06060c060a0e0f0a020f091e090c0907 73
    0x2d018480c0604a0112032164184841100e6102c0c1c1d4000c001d800c0001008200b0480c80188003950003841002c6815039224101c0c03400800340c140e9401c4041c050079000c2c005805900c2c40c01030f0350700d030300038a0300d1700083c8403104021007040500240d200400080c1480000714118016400610711102d00fa000c44808504410a0081c03c1c44040c016900402440950700c21661017a6021212907020745400750800309214404101d040c40c59030800407503000040c0c1c1c00c0855810041141440e000175101003200c028949039181e40f00343c10402c2800300420313600c030203046a000f903011101c40750000c0142500c4603100c411410041483c6901070b03010a031011040040c145c01409144450210f041c051402c640343c0d60b0b01e0340c002d40c001038070003035100c101072100c0450240c04025043c400d60a00d000400d05015400c28141030801c1d100303010306290071415503100580c0381e103000011040da041d04c680100b0380d50a402010402c0d000e10310500c400c010881402161030700000c50340c15146040703c120126840c0e40034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 640625125 1250 640623875 640623881
    0x50d060f0e0c1c1a0103060b09031506010c05060901060611120d021309050901050106030b0406050102070e042f1801140d0c0f030f0b071b1103011d1b04 67
    0x86081007403101040042c0300c4a038110b01408440000b6140102d003524891800d9003901c0b00340404100414070007000c200e040d07a16004480040c001d950305107281c1184400401c0d01d55808911105910342c103680803411a920401c038040d522900305003035510314205181014040c02d07080c46903030000b9030741d0f40c480c094a12001c9407420010b081a005a850710700304010f004041d42252010011600801c180001d0b10210790241c2c610503600000001140c2d030400361b0244c1110362540805014910b0320030148800e0760001800b0060701c0c0c43c040754401d650b840d85800d818500c00e0b49404410300303208207128140c140e0341141070b06c0c0d1400100c96503514200d601c0d40d8000301e40024401c60120380451222021281081805072040034051150702c41140d40711112050b510b0230b15030040381c2042c03408003e002130081004c50b5a40004562400903a204000442e00804982505010300f801c4915690340c0040e640c258020f28a0082100c020040c0007089440c81c0e03100c00c0e10704901c111942107919030204611f0244 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 640626375 1250 640625125 640625129
    0x190312110301090c0e03071e030f0311010e030c12091c21031a0d1a090a1505090307080c03070c06030e10060f060c11090a0902100203040e0f04030c060c050d060f 71
    0xa0700410883c3e140c23240009403604074a01400f0991900c80e00800401e1001014110042c001e45070100e00c0110901400c1c2100c0c440d002e2220650800e200d0845443c0b0003148410708100510703030403a15203c20344001001c0d215a0100c4443c4240c1c00105541000690504c0c1501a0f00c03285d00c90103024403404003501035944108016a0b4080074420010492401081c0883c2003809030702080c001c100054100e04510006a40d403c405600050f91001003027032100c0c01d07004c03412000c402404541051600c039a0b41e8000d040c3c008120300c40c0880d121000ca0810000d90315601e8001c28410783d8940c1e1810003500a2800c54071101e8517015203004e219030000300c0e003d144102e03603c818540e03e0440c5800780840b00d614501e20115201d02d1f90a1010b0710580d00c1c807895a005182c00c00000030340001e244100400a1800390000c0190342003030004005144000011756400422446c0210156440d850100d448070880340004003041c1c940270210600680c404090320581f0a0f4160410080351103080100b400b150038 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 640627625 1250 640626375 640626379
    0x30d030b090f0f0a110903070303020705100c0b0f181006050109140f060c011503080901080f01060c030f0e03010507030e010b0a3c06030905010518190312110301090c0e 74
    0x400210713040f595142d00c000074040d03c0c284254140005e1100080c2449400d9109400682c4203000520051030b041300e130b4603030220b03003030529141d0b6201d01c0c1d8031000c884000504441c85c00d400300c1d0000360000811007114900a030031307000b070311251010b4164000c010181d900a10b80000d09800c5d010406905505030403c465000920010008101e2010020320340d001c0c14000149540340e05d003802ca25108510144c014511802d5050b8542c21041c00042c0106401000d00350342c0e11281004104a03074000c040600c005815180c003a10881c4000c100ba41e071209194240c50705507181c0420030001981c168004c810341c83c4850700902051030790104000d69846180076031544900120f00710080304902c0c001180c4a4040c0542c0030004c00d03c001000450354400303a1105000c80d40700c0c4100070400200b0712540384d000040e24002c02ca441c030542d18050b03490702c800c0e000c900b400201c540c02d9418540a0f0211102c01c403800307801800b1a9806030701c2c00c009900280326245d1070b0381c20b0010641c4114040c0702e0700e43c007031100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 640628875 1250 640627625 640627651
    0xe010810110f0919081e0f010506010f0c1b260106060f030b030a02040e06040309060c081605100204120c0f03031b06020f1b0618101a030d030b090f 65
    0x201c00d081040101021a107040800d0300841c001400f15002e00c8481c003000b46c0000800c292540310b51201d030406481000d600d00e540d140c60200300846ea0890400b0303410800501e466681086240341c02201d00301e00c904d2a0354102c042c1030000460605110b641c00d400d4042032041a00900034045240c20b0b14003601685c80410502d07a01824400d203e03a114100040300103085a040c001c194000c9821603001d40103807800358000a041000b41500403410000a0280303142814080085495403c00c502910503101007500c10031080c40e0500504010729010b1206c281300c2150f42d140d80e139100c0d15080d9003661049550a0f07054400141541d0010f2280d000c0b0f07909920740003071000901c81d0004081d24080340440d10203a003802000440d1211a01504900801305550440511900d22181c81c0040043c4170701d0210001021080310402c0101c3c000440c00036854010600442c0114013200342e02d40451220382600c11003c1c0000e03000e9050f00071a0348160152440e9840381c0300e00c90850081c00c0d0403925440d1602ca = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 640630125 1250 640628875 640628887
    0x9091202060c0421150b01200303070c020d06050106050405040e03090607080f070606060e091303170a0b06070c03060c050310031e1a0f0a0c0c1b0e010810110f 70
    0x200c02001000f03030048500c4c040d04030f041070f61314080390800141e144825203948959508865820a000800f9039180c20130354401d0b00c0d004030000d50399100c01418102040b69030840d000131511810010680590b00c00b00a1003d503846800040c515001485810f2059082010307403007010501004581410340081c00241c54540b15480d802156400908908401e070410060800414140d20569010309040d0381c481c00700d01d60340410084000c001900020403281c550740c1020029400020b14507912803001e03580880c1d507940c081406c0c000d10600c030b4100e0304003400190a604008003a410071050381c1c411740b001c221050703100108860901048a81d50700d5060401c0d4148081504100d0040360500d2207a0803440b0070f00259a0016040301e0619070403101754190b42840025502840c0041c0e01a014000401c194440b110005040e04d03a45400070b42400a02c0b4030603140740024050f05130152840300c0040800c3e5039544d40701c581d81c840e904401072406203840040c102005d1404110360480303034051982c1e030401d5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 640631375 1250 640630125 640630139
    0xb040905340807180c020d0810051c060e0105130b0406020f0a0c02030607231b15040605151e0f1507030206060a120807030e03030409091202060c04 65
    0x303441e07241c59480d410102072040c0d200c80e030401840405001c1a10161075414908807005010301c240003081014a4200404071042c5580001c0c800c400d001c062402c0091034960005c0365001d041650000d0780c0105010012508502c1c04450001541707119420800142d4542075030344c2d003207460a0b05c3c400b014103650060040030030315241e4904c0c0c2040c02140c0040c60b20442c1440a02a0b900c0520043c0103d03005002803015454148604c640c40710550800e050380c0541310900303081089481e009501400b0f03000ca242018019030300300403650481a0001c5902c482c0c1c40e68168108200e0843d01100c0107400e0000103080805009010340ea4050080e0040740045004442185000c2c040a59240c002e00040ca06040e241e0310480c07500c00e2200c5c18050740380c0c0c1d003c15003402800c10100a120f180038040d501c104103e0203600d07126008020f60840c0c0c1603038490b039052074110b65020000e1305079035062001281c04214040943e00c51640b03988640b4508140b8100c81030284e8658500b11070100f1701d042d05100400400b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 640632625 1250 640631375 640631413
    0xb0c0601030f03020106080a11040c0e0303190c05011119020102120a0f090203070e01061103031b07020607060905010b120115061407061b030c110d140c060f04060b040905 75
    0xba41c464000429030588039404c440c5060320305601503c0340840c000440025080c90310401851502d82d1600d100d481c1216008250342e442040134240360400001541c0c085c40344651110320b0860340c0318001307100305e9605000300385a0740c00035085200900c2d801c0420342e42c014014402c480c100400791041201c0340d61400b40200041260310210150244c03100c04039030060303905000d15000b42c0000140242254100b0000404611030000d0f200c2044d4800c10510100c90f2036088681a00204a5101c2d0341e2032084d03101159060250131301c02400182048116000c00c0819040902028410f42d08184040031100b800381c00d0314840d0034418641100c501c0c09020316889021001c0300e031720962220a19010007036840c00f044440d420703c029040c02d4141c040008540d818001c00b000d480b01da01d0290030700142c0c40c62083c0c4440000c0c0101051003142019000c80700c4080e81510095480340d41030750303030b03501e8040c41d4000140001c0300e0031640301e840e2840a0800d450144105078507183c00100820540507681e03155042 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 640633875 1250 640632625 640632653
    0x70b01030618140a2a03121b0606080c0603071b06020f12040203060114310c020d080604110a030209180702070e071706010302031e010b0909010b0c060103 68
    0x54440d09031024001ca010304140345203d0000c08020107030071055090501d600d05a02d011031303072136001d14201c2d104d020b5038030407102041d04d421885502c9550040031080e00d00d0342c500c07218201e011203200c2c040b0713052003d01c0c0d012001303c507000800d45040400038020042544800c455005c082551600c160345004c1c60f41c4505648103202d1000140f800c1d000c61112451500151086200d40280300100811410140b140c00c0c01480800c00340c1102201c0e55000400d58000d46000845000300c4420015400010744072105005c83c0b0100d04102c444000c480082d2074a2428108201081e1108045481c9007001c1c03145121070114a40c0c3c1c0c40c01c10000312412070195201c5400719a000040c3d0121000c0300350030240050266000d074004200d00391030102490509100100b040040c8000d1441d0044801d07003500b00c0036071016003480d0050f9690b48901d1102946400c88480b1140380d44c152002241080e00c0710700030005010112941e800744d0382c0c2c8204401c01446890302c400c030a40c02400c0100001101c01d094100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 640635125 1250 640633875 640633901
    0x7080c0d0b010e040513020a0f0b0f0a0e15070b0714180402040b130e09010b0603040f0206070f1202190f030c0c080f01020405042403140a050f0d0e06070b010306 71
    0xd948071000c3c0001d040d15410740b0030b850b0707020507440420110f14042c41e2500061840809410520b13141c5003410f400c90003485850355840e61700180d00300d0305511580454a080d800101810040b10744400801840c0d0040f0808595130395032070020410640c0108541d008180b20403800034a840011240b081600e0642008a50003913000c1c000810046c0c1c258026003c02c0e15405910041c0c1341c0b602d00c078100a180090203903000d0f030b45003018411082d100c07081180c1d4016000000710215082d01d201044452040d540c01070300f02e550038000102000302a87d42d454204074254225085110000c00364465803a1400004100f1000c1d8591000020f01400981e15200d0196851848459549030800d040407602c040403480760b54002010f005030300d001e00c54510290180b111543c8407140c0501183c2100b21940400fa0607091008200c0c601801c081254580495201007520861309031001400d9448071095680350200d01c010304500420308004068a1109400003a40c19050b441c40e1504030040c110a50f08603 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 640636375 1250 640635125 640635137
    0x60601050d0e0601080c010f09030c231e100e06031b040b041e0e090606040e030c0a030c020a0e16050a032007031731050706020304030b07080c0d0b01 66
    0x2852200c1e081c00404d008000340c0c1c0140c80c03803c08580005204491103090301c01030000c10341083c07010174280e44030314040c1e07840383d540c40f40072404029810800114a049141c2d01c10b82140c51010005041211034400100c19603040d200c10748440800e540c0c05048407501c40d0812018000108103605c11001d894250f440b42d404185460340720b12a02d42164499000300b000300070714969803110f1000c4003035014010503800d6046c240c076041c241c21041d111036005d401c05102d2900c071100040c0c1d0384c00600450389514800001c6862060461401514043d40703c44264412940c901e00040d24109039111144240c842d48120020065000419641130304100d54401c105942c804603a01d014860408030790b05000038880c40e649559481c46c0081843c1d01c0b1090a000f0050100e081c0000a06c0084c0c58902d109009000415802e6070024101d0002d0515040a0000c0c03040403000101550044002c0042c1d0f8000e5031201195a40c00409483e885c20075520384030411010845842c090070a0340c00070303041c1d620500d408 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 640637625 1250 640636375 640636391
    0x18030304141e0604061d0f010f0507060f0f06170a080a08091011030f180712080f0a090608150306012c0124021b0d0213020309150a0e060601050d 64
    0x2c42d030075801035040f400204c6e02ca1018900b826100509408000c0710849801c120b41c0072840000b0007030150500f0180c24440040350501c200b2285801441c424103280200304040400701a4010103803025105481c1d0111900000189030007020420194894020340150b250000c070b00c5003224540350044c1140365500488040680d8a065402540c89110020300e1454403428402010148140c01820240400c90030b8040031402090124280c41151810040b4052407243c3d400c068a0510480000403842040058400d080035081540e12b000c4d98000d685103442644d450350058103140e480190103516900c220010821849081c0306203215480a08442c1c0107003203e00e840d0000c0c0300d000e80002100c4500f03c1d144800960304132210110091041c4014214683d442e422140e41406410915000d030024403044003e648448421030844000c07114210348e40e14100e00101d4881050913001c0102601c00320218401c50058000c1c0c0c00054401000f80540382c4900d001518580d02a04d41d00b2905a158205 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 640638875 1250 640637625 640637629
    0x60901120c05031506030402010207031209180f0c050f07060b010509060c010e0c06041d06060405090702010c090549080c120c0a030c1b060518030304141e 68
    0x19041c625845854080d01d90070050452680d1441e00081c560091105004110141c0c0c2c0c000766203411240c0120003a0910b071004d82040303580b200140c0089103030417007600413440c646003503501c103040542c40110104072502e076496040340c1138441c24070502039041d030a1000c14041200c69101c0414014141003c5160008590100c0c103139030411691030345907941d11007840d0000501480503408005040b211540750908003007203a0307102d5500d00b1503d000580c400b8000b440350b440707440865003c0c1a004000d15000e1070b0460009018049841c0ca62002500c003280c0023409060120101a26000003050b40c0c14440c90f0040207205107009c4484582e1110040080d1240e4041c00942c000e15540140302e41965003151a082910306010035089a485070742c01c021202e4244400b1960103601c45e8185844100c50440d070400030003030858810715071916681d000c800206590064020a649c61003c2041d011b401003500415840340075a10415801005280144081d450b10210042c2501140070998030a2a40303500 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 640640125 1250 640638875 640638881
    0x30b010903020d080711040c0207030b0402031509100c0903110d17180913030813060e060c030702010b04061422051e10051507050c0d08040518100506090112 69
    0x2056031340e1130000170f00b0414403410b16014103803400c058800348905244584020b684052611024001c0c11104c404542107507014001031004030710007500d503200d5040200c0301507242c1940100d14440d880c0341c44201c0c00300c1405103407a40112500101ca44460802000511910540e45801151480382e1000b5550b0b0005030840600000840252a100b40c1c600e03000500a2384100078003051142100f02d402040005da00c1440d8645c01400e0510905220580380360500c080c00c1d0400040515004420402c03160105143c0170f180f0540d5503900a2010880140500c0b084030128041e0101e110b08100c0d00c070300d060402c14a008100702c00d411111035840552000f04e0100c500c10f44400b0b009010b0420003c0c1e160317240000340790700f0980707060001c041e0300d02d0714000a009040c4165803d409100124500c0705201e42800a12803080c406400100b0030340651810041c1c2d0b0744540500e901c83c40700f9081c0300440302881d00c0561301c5070f4084d4500d400014144410009180c00a9500e203041016a00c0384580b0300361140 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 640641375 1250 640640125 640640149
    0x20d020d060b130f1a09121c0e0405071e02030d0603050c0406080f0a030c02060d1a0108071718030405190e011703030a0f0e0712120201061203030b01090302 69
    0x1e40b40d1510389103103c00901840c0c0199001e510034424031003042c4950410090301815a281c00000d480e039860810000c500c5181e507500c044841c5020f584011075072803412844650b8560501e42d21040b00c21500300400c0121941601d03044001600541441c15200c010714208080d07041900443e81060800200c030000d0300c3c0382e030304102c44503040b54089000d00d0809004a0000d1b10301040a007040c850f200c030704a50f80b01280e150103802c00003030041000554540204446210642035410f1007100d040d441459403040c0c6801d04240041c040a0000300e4a03440380080090040c1c0c58010051180c661340381c2822140007000710208a03000c10030000909a503103400382400c100c0c4042010704118500750440c08120b1050b030200b8109160078540d02e160071004022241d0106840d1000a011f00d42030080c140142002080090144a040d002080000c030780042040720a2154142c18103510055000300c0c02d0321201e01c980c86441c4000042c26000034003907080072040d00010324020066954940014800c44120 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 640642625 1250 640641375 640641389
    0x30a05070510141903060b1215010908070e1905180f07210c0305010216050c1008070f020f0304030c081b01092105011410060807090306020d020d06 65
    0x100308803504240025000364030316418051200c0381010310380d10f060b102d01840c1c20086000b840420f05002d001b540090081c111a8058984400e18140d0f104454981560407000c82c0511528018056208082d4141520f03084005000c4e6185090b14441e404d4001a15017803034402d00c081c050101d1034841c403c030341c810003c00003d03c56010034001c2c52424000d040040c03100b2900210303814840300ca01d680300c02000020f8440c02e0312070007900d800e102e00c90705820341004080d9400015441a0402100c2c603400e84075000b40240c6601066140410080c0300d02c5520410115000b5000a50241e0140140080098070b50060f1050703a0136800c09079041d5031103500704640c480341ca5030052004c180304100720441c208540c495112040031500c0003a2000e0303003a2040012549592081c0d601c155410802401a198850024071821070803034004c55030140101c6407600d42c0442e04000183d070300d02c1528124001c4000f9219111002c0c01c40d100c10000e58000c5c55090b004503000c00480300980c04034070864000f840d030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 640643875 1250 640642625 640642633
    0x80d0b010f0201140609070c02180a060b0c12160f030206070801080309090411120106120203060702150609061f0f0201110a050412050a020a2408072309030a05 70
    0xa5000241007901440c109a08580c5000b90300c0c44020074514069400050441d04588140e0315810125920402010020f401800c044080203940c482c0105482c0542c15100040c81183e4440324408100d0103402d5542400741d21068800c802d10310420020011000d900f034100e284520252a2141c03c4180c0107012030040e07015804200d0349580c06600a4094042c40025601c0c0c6441d090001e070703e1490160000d4210b0540d0011580d6035030f9040611100104124001c0c02100d94524020410b10a9080d059000b40600e500244149201007022043c02d12401040b00c8291030f004240f1510010041c800e5811444904a414040041c60360005034039486940d80d00714405005030080c2942d103c2c4e1b00007100c060f0140300324038481d074010090328255036a284504148280904056103441c0e08003e0280d0070240060022540e07842c860011202d00a03500c0d40c05107c80e824060403682d101e42181c440c80025a000800003c1c403032450310552036040c04891150501740103400290a04501c1e40f4102c45c951302c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 640645125 1250 640643875 640643891
    0xe07050405090c031315060f06020a060e06040b010e0c07170d06090b10050c0102090d300509060703020703020301420b030c040b070305031f03051f0207080d 69
    0x80d281c0318060740243d05010746404c50a101417018503000403008024039480007030b94641802c84496111000429807203002c00c0c44940e540300d02075142c2414800507591030307040030101e440b008000600d0a025a9100c02d40c00c040d40e10700380c01c0d42c2d52038002038699801c201040100d5404070740b020b1855000c0c11a101100740e9204030340348140d000c880107076200d070001c18188015190295110040d1100b8940181004c40d0744003181019140284a9108645d0f0f120503210802010b00000d4251820702c01c3d81921000d41c42c000c07181c4100420062007411400040007000b8280e41d40c2031520240415600c01d0044a010343c0e00c950029083d40c0064a0340440b1b201e00c0483e4140c20303000b4040610443c500c50144140070001c09d0001401280039000b4a80c00c1d07100000030903918030907601120014021040791a440d0201450000e14503031055071126100207502a940d40c10340340c05071105040300d5100000b02900b003100d03540c44038088507603075012031059401d10503d0080384c40e03a0f00501c03456280500001c0c20903 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 640646375 1250 640645125 640645129
    0x1505040e060315060607111905011211030604020c1f0f140f1609120c0e0906090c1201090c080705011106090604031d0607060e060105240a090e07050405 67
    0xe001840980b003a4400540a03c440c1030050140d6003144080d5503856a800c81800c0c04d04840c03811300311264010005065414980c03040d080c10100b9a0001d90320300540c81c1d101d500890070340d03500304401e1421084c06c0002c10400d180a030b00800d00000d143d4150750100520b44002181482ea60440304501d58803010a0010894203106034240104c0c0f0481e11401414805490070301060010000080c0325080c6e10040c503920301428100c002001d0600701e0141c0d1480f14500b1103403000300f0b4892200702a0711000821000000451160300c18031010000300303043c41c030080c1000804100500030440c29540d8015090215080e24841800750079203400403c005454580018212010403e520311590864000d008a91402044164000d501403920010b40c0303246180424000c0b403055621980a02d0008248003000410f821050481d4102e500b911000d81c2d0324014452000300003101c4912003c08201c044418000210107031400c0b03e010300e805c1c0500c035103400e030000034504141c0d0010081440810100818 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 640647482 1107 640646375 640646399
    0x40303171305030c0a0b130b041b08030a021f0b06070b0402040209090a05090f030c0a03111006120507050105070c090f0b0603100501021e060c0a0207150504 69
    0x19500d13120b5000303507501c03030b50f410460301c0b44c401200060500b8886403c20764810380107290007000365195514089100b1142c6208800c05130a01c41c04103c1a9040014000303200c22500280070303400031042c1581110402c85080c04096040100e0080d058842c081604d414543c4a89040581d8403680b0000b030280c02240559600580700c00c040021000c540e80000d8020142442135030071030b140c1c150b5020745038400e08003282e0090340841d500d800081d205010307995064003070304151415428440002e10940d11103038080b5500a4407074109100f48502880048000c102c2400c082d46048840c3d0b40d8800107140324840c54140315920f94660a2074031054001402185000b050340341e5038038040303c0005c0800d81038001e850041c440c022042d00398044009081c041a0a9400200309a6460a4101d1a168001c4038440110300880314001003026010888088170103540d19001d45846c1030155018136 = true := by decide +kernel

theorem cover : BRFrame.Cov 640467625 640647482 := by
  have h0 := BRFrame.cov_init 640467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 640467625 ≤ n) (h2 : n < 640647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
