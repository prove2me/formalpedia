-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1721
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:25:58.099983+00:00
-- url     : https://prove2.me/submissions/e1668c11-cb3b-4f62-afb2-0246e928df41

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 309352517 ≤ n < 309532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 309353767 1250 309352517 309352567
    0x103021927140901050a0501140303040b1c1b080702010501060c0605040203070b0f042d0e1308070606080c090c0f0c0c0a080d0f0c03050d02090d0c060504140330 71
    0x1400e49801ba241008844068204201303441d8242c1501c3d0300c40d60004140c40130343d00c1c03114810f0b687d02916024181d821200703e04078501242458660100c0385001c80c0900d203103042c1c03a100c80000d903454660407802c0354424040d03280417903501015007000c03c205038811940301d84050202d6030340301d8031040c5620703c5800a80301ea8180c0200050148104140203050300c0341c500c4c1403103017012a90566002814000e04c1c600820714582100d00006003810304140d00c44140b01d0f000002c9603a56611800d110025100c1e600807001644076900220f0b00d142000352044d032291955814050402c0d8000d40540c201e5800924035202c603100f82c1240300610307640c0020309002403008100a0005801007400540b58540700c0b108601441a540810800f080e00801102c610444010005075510400070019138441c03c210380c0981103141141d4003040041d002070040007175801c6025542090603e4008055a5171303085a8440740707000c84032251a141481d00040031011640c80e0f6111800c04000544440c002c01000183c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 309355017 1250 309353767 309353771
    0x504060b031504020619140d0f060501180b0d0b120f12270a080a03020105072a02090402040b0909030a030b01030207022419080103021927140901 64
    0xe400646400c0050741c82044012104120b2850941c002880c17501034003000b071001c90b00d03690310410214072500900c06000010f0b80190349840002c0c41c1840101031000c0246000f0b8074010000c91290300a0700c007460b44151011000c1c4007141840b54950164000c60b8464040d26103a400b2a4220365a00100380b0013044400010a6600040d0084d02d1401c00c000201e1114030780200520008001c0182a0042903c01206100060b40941d004554201c13000e9000b04490b01070402c1003001c240d0f043d00128050f0100b030342e640b00b204034011100c00c01911803225003190401ea0152100043c00e08403185984540010000206e2030900d2000c10079500c1c003200c0c056003603003000030000c10264151088000814003031a04606003059580481c85107160a60380d03c400c0031000c200e1600b4200b00d0000c075090800210b0000005403003801d40a8108031007808120b11620440b04c0307840c00c000380305144008480c000c00700c4001080601100e02c000002100001724550707100d0391a003540440c00365546016110f07034000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 309356267 1250 309355017 309355031
    0xc010819090c1802090f01031e022802100501060905010207091a030a05030d050a050f0403121104062312011203020a02090423070b030a15050a0803040f08010209010c1104020d050406 80
    0x421800c08041b0301c0141c141490003440081d0610452303406103400140c0400181d85001d0b2404100c1900d15800144107203160b0f6072042c01349260301250314a502000d2000500840c1d0300d4520903500039001d4081c40b2b0069000200400ca1240b840c1c000e1112940300b075091100701d07000c01c40820700b07091103658181c030b4603840018000c0c4241000c0c807410340e00c0550210100820300700380c0703110040c040016001a041103140b54101f2102c1445a00217407401c00c03010031880d56030b03503202806003001156540a5130450030b1404008882e580103004c46c1d48501c1d284101c0e0041c0da003410340900c00c00c56410001c0e401c511070075030401b006031205002107020f24004c580018051120502e6110820700c55400550960002c0b0000c004120000c0143c2c1d402c0600c0080200f10223403101304005000c401c0364800382d4040800040094011b00c040001c10544521001c0c00102544482d01642030f486030070501d600050821a509020a80c180159040c0c450024009843c0440c003480f180e007500d03015076060307903a86d5480c88 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 309357517 1250 309356267 309356269
    0x7030908070b12090c090f060a090e0307020d03201b0102010920060f1201050111060f061306080303090f0714030303010b0d0b0d1101020c010819090c180209 69
    0x1014004211a80041c51901e00346080d0000a008825541d40d010b00410003244981c10140000c0c030340c01101a241080900d00500842d1018006407001d0f070040c14180c00201e03600c8080c1c0100c4030550310050081d4601421542448000b0102143c141e00b0040e00c00550344000e4900001446000b19100040c43c0b40084001e810030044003130036000d41075a250080000c001980014442d00340c028081d81d842c1c404480c8004514644142e880c441900c800c0080c4940341d070190300a06906840b0280d072182c000c0c00000506566440701074818110300c000042c0050154070f4580041642c00560000110b4034560380c00f103061541c0c01c11340d0100d0f40c5400c654113943c0301c4442002944001c3c5911450404070300c00c84000f003612848180280c0614600000c0c501d0404803194005690311000035107103842122890074050403100e0000705450050046405015081d03120350b400c2401658482c020301100451035003000c0c000c0c070700c000c0d04403100301050b40c00042c80c034401c4400881c22003082e100542e4486a0b80 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 309358767 1250 309357517 309357527
    0x2070203010614130f1e1e0603020901120f020a06170c0301181107020312040911091c0501200a11010606080123150910030618021308120703 62
    0x50411681040300300908109a690711070141130a072800c03180054055400d0492502034581c142c0c00c815900c01c2d408500300d00f1000c582c083c505404c01c0d180c1500001d903400941d001681d40511001e0b40c0320b1301c008014002c03940c0703241c0170428151003820307440400c1d400b03540810700c802020b41c0b281c4003280c00121035901070500100d40d143e10100104086107598141002e500b846500c4010760300000d070390f642440c810204248122500660010121200790102406014240d800703402068842030a16004070002ca0500e016a0444070f8000e05400b0021849483d82094a85034501582c40c2d64032000031a0410310b004918032030221125103181d41d1805001303030161034044400c142c944c1c642e2403c1c0080080960080b80c7d18191b6100d45220316107800c040150009002c00c0c10002940640202c1c00e05102c500c245c4002c01c1c0210068a010308001c50f025015400c41c1c03480d04c074000c6180000e0030a040554400c0d8001c082014a403880b6154403074586180a01e070002c10101d082c1e00b1040011580c040c59007103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 309360017 1250 309358767 309358769
    0x1f0216030c03020f0f0625020d080910050406020a0f060b150d0b0916050c0a0813030c050f130e071d04020a2408070e031027020d0b060f090406020702030106 69
    0x6840307100e01790001d400400c01364450000540e111020b041d40c2011401c0312048032041481c0c0003080b80410b01d02074213064109921441103503118102c2c88003c0401340b07004a0a481c2110f85036006000e8107511031300d41da4465040703100100c684950b0340100417040d66a0584052510013011500da440348221080c2e2002c0f100d0080410388603411140030400020f0012640102201c003d16010740c13214038510b1910315040c1d0004004100307035004a0f480d075404008508180480e03005d521100103260b41c82c418001040030100d540c5422817410218010000016088400814241c00885030b036580d0720481c480c1e503842c003848030190481200d01480103519103a21802d01400f0001400407086004024503141c01500402e6101070220320000a0005801503403041149000a015101e40000c220480c1e0006d0821030500c82c0104401000340c0180c2421426441c00070758081c140c8550000c2940718025006001440103a000039000912002038071000152802a07209079005621409284105402e40d00a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 309361267 1250 309360017 309360019
    0xf0307052703010b0a0e01120314030103030c050c061908060126010512030f18132c0303090d140d020a09090f0216021c080c0703110f1f0216030c03020f 67
    0x11740d02d05000459181c228141124105215002610007510f41598204840904075040d40008000002455040107848200c6031043c4240c034401c0b1149010004240115403443e0502000043c00c442d200e8080c160aa41150050510a8510980c1c050f11040024400c0e42041c4020710b04004000a0a01c00307202207021020002543c14415403c404142d035010711020382080003401c035540e22041c0c5448084000f00c511040c01404075034020fa0000c41070340c401d655600c40010044400c81034030b51f00881560f00580d14003010b003040015408003242c00d03915125426400c41e40400c00c544024000c2e00c003e01030340000707448940102e49802c0d00d14041320b0145002258550040214407003106410345001e40c0d02c0d90480d040201d0040200c1d082c0c51610407468018580440050484c500040000350441203902c41c0c1051004407180c541803141701071a00280d250450741e422043d142501c0b00804a0107410502c3c41200d820803069040703100030441e035a109803010401c0250038020760804048070b0148000c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 309362517 1250 309361267 309361279
    0x70806090c0301050903160803040809040606030614191412010c0905100c0803060904050f10151205060c0a020f030a050a080901051015030e0f16060207030302030f0307052703010b 79
    0x2d0305a450701f41c2175010002010140000005010004440c042e1407651001504c10407280fa00d40300060001c0000c2d008500c640020944016000c2c500039035640442c00c000c890186032185805908425042411503047c1c1c4000f030164900c4070035209106600200e44a980c1d4818194504400e010030041500c1c062000c0214070f2801c034003c21202c10480b80c010a00380d1310001c043d92103080180c149200c2c3d482001d62402a00d40e84200c8038a135800490002a9515680010301d076a0009154a80c04194008002d9046000002e846440c001d002d040d0240385801a0f44201c0070307100c2c1c0b075402e5030b0bc0a514600862004140718419a07403100240b54003078a210b00800071030500d080d0000b00a0301d80e108680f91044151100c40c8064400d03000a008440c8100031030340320b1280514510b46a04d1086009003241c140c02e10002000d0b4400196081101d41580141d8600305110084594070390000717102030148034040140030440c4680c400c0500180c1d0b2a03090140c0c910120508060a45203203031072140c8242 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 309363767 1250 309362517 309362527
    0x1a06010801210204060b0a1809021c0203060a05030706050705070f0503100903050d020406120b0d02100c111302070b01080705150304050705060f130b0f030601030e070806090c0301050903 82
    0x1c041580e1260018500300500d486012440c0f0000c2c2c0680240c0c0c00910302c042000c80c41d15801c40d040205001010f000040c2000e106d0740f0381e09070074224015030315090f0b85418480562004100d00d907000350b800410190144401c29182c1c0e002c41d1900c401c4d980920001180050031200b0b025040c02810050320341307501c0e441c203194541000207540c1e484640c6482041540d8102210816004a0031191034035050042503440d40e0344c0702c5000d40449900710904400e40c2c1005c0c002c003128508241862000b59004184004140e000d41003292100034008003260041c00005416030306648800c07000c41088030819000d0781c1d032081407502d00d801a10603444010142e000d0b56040c0712640d2200f00e0b9203006610a071101d510f0b80d40d10300b0200d140580300e900a68004000140559030034500900400c90b500d00b90055040c0203607901e60160a900c05d17503103103403007814044c8085a481d40c400e82140710442000c40c1160103450712003c5650a019041c0d49990042d8003032140c0d051181400e01800360f02504000185080c2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 309365017 1250 309363767 309363779
    0x15090304030c0e0604090b13050f070501090e1021030f1110020c010605150702120606010e060a021e010e0c0904020307030611070609050601030c140a030605090a0f1a06010801 77
    0x8a19078040c004000c034065000402e6600c5d60f500c99100d00303400060300341450621408034080f08640303401c00d4030180120349805a141074001245e2080b158182c0d03400143c1d519001c0344211442010b448050811402c60300025a41c0c0010081c0300f09031503003201c0d6000998145005002e04400242c20024041542c3c880c0400a80128840009450314203025a981000600700d0380188030b00d4005550284c0107a01030303450007000e40058400c0360700c00c1d951050300000c071040e003d580d003000300c595a002078500e070141c000c0380c10500043c00260340e250044840c607603d620b040745805036005100c1421a0340d0380700010030420301048030f21481c0c0741c140e0709150203080680210380c49070031034003010301182d41300c1c0c101e4000d0380302c1c040441d0806030300154108019022840c1480d190030007071000346c80401d001e01e4040b519590210525065039401808001803500c0c41e42d4070000b80000411b03200700c42c0544420035020481d844a140e2245200e6450315107600381840d494020610041c20440c108105000180304c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 309366267 1250 309365017 309365033
    0x40501111c1d0405011508280f0207020603041511070809100207080610030b010906120f03140f04150c02090f10030c09151a0a08060a0b0c1509030403 66
    0x150109192101140e40181c05452182c0e00102205401625000001642100001c80e0042054040d50341c8411500c80041442c0010038801103001e501070068030b15201620203621400c8005407580c800350404100d5000146150400c132000d8660b6000340c1c0480e00003da4034410b8500c01c1614074511801c09109441740725682c0140ca9481c0d0203040c18074001203d09000300880c0008241c40070458060345006800320708441820710085408100600c0046104940d0303003d01c1c42a2442940400340000c0036845090300b40d60346000640c20f000100340d1079448030410304003c040b149a20f0120590359494944900c00c9610b0044d80182042100100800160750388103600c1e42040a181c640301141d21554005015240030380d200500401d5403200000316102540c00c558824086410f002072070507654403d2044a0b82403400e10001c2d20320411031840c21034010815a038201c80058512900c0540302c3d000c0d40c4075039000f1f0381000c1840e840300c0f2506071445140740b8007a074080000000780d41050310790b65070208e07 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 309367517 1250 309366267 309366313
    0x40303030e0703020307032003010501120f061b02070e1302010504032003060412030e1f1d031201050a0b070506060d021c2603040809060a051e04050111 67
    0x10030581c0707899190140c060300300086070207190000c01740c81085980340b40034001e81480070840700010080d44008031161a06106041c1280d0842c0790008038040150307a01c0010201c900030450700380d5980c16400000201461042e80015969002400b545061450508011500900e0f0300d00b060502a03043c00181d900c28161011a0b500202a200190380903180f0682c0940b010726aa4251042c48104000e001441b0107016815000352810841350300c003015520b4849004d00d4042e9240d90307000301500e1901e80282d021b140f800c45c03080c1c1c1e000e07046200b20380240c0c1150b120310304100141aa00c40148918641a02e0400040400012592401903640c0e5107607256070707000307010900c1882c03002d8102c4295140c40140d0032092410046030385010740070b482c1c00102e040410107002001c001c0c2188680e000c03440c0d4070840e401640c1001266050040c12420825580d102c450054100001032108600c03180c4114140000d800d84400355945490414000621054504005140030742c0a016280071840384042004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 309368767 1250 309367517 309367523
    0x1401030f20071a13060c0807021c0e0d14010b10091503090204020c070e0114010203120903120c04150c0b060d03030e150a05060105071a1e190c0908030403 68
    0x66282c041c9420410415018100e19500304043c22081107410344094008105040c401d180800c108581c0c1101160300c21400c44400c405a8041122403405031422074243c5441c600e64500302201400700c8021906080440070101e03040302c2032200800100c0428011040740071019505803003400d248220017820203c03107200341504d000c006c0c1090b1f02440d20981000505540151055607034102c0710031680e60306c081920500034100801c0e400171883c401156068078080b070050b40110304244d6400d124408016005c0c080010611081005004a00740580701c00d204d2045c12503019205c915040d1299001031101c9020020400f000349208001009014459000103050320314849540e50791600b07500408540888c07a01c0c2c2d100320170000c1da0484a4040041c450290080d05119a84410006566a00039a200204040d08903484044a4840c0c078904a500c5030440c00040103441d05071070140800101980c06c4024103400d8035603401941d0301d40c01142041c80051a0046545240c0032140b912801140001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 309370017 1250 309368767 309368831
    0x806070c03120f06060c030329091302090f0103050c030a0c140310060b071e021f0210050a0506090601182102040203071701090b0f041e05011401030f 66
    0x982a9040300d42c05490248030040f030070400c080d2a11000ba040c50300b44501100020b04028000c2c4100d0101a0724030004048100f5095060b1038800c01c101119100810b41107112901403140d0001d6900c50b40417a0080718a414803444a5055050840c01c1c9002c11541502aa101c1802c401c00145690803082c200c4280d0304011000700303949030000b42480c40e130740c409030a094182000880c1d0062540c008004503441061500018044101c208a64540741800030794071449600d02d2602070403841007003a6841000b44142c4266030100e484c90030485001352007000546544004008007401d01000382c640000090034002c4d01c10540c02c07020380325100203008a50030000c0e031a6072400300e60341940104a80303d6009000759100d04c1c04420040641003600c1044031091000c000015501c011841508505540540940c44240d800c80600010306500702d1140348903554140350b00c04150311031003041d0203800d003034054008800752a030004098801d4800b02c20b840c01c1c0b6148101000c0c01c2d05030080f1030035030b40025070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 309371267 1250 309370017 309370037
    0x8030a0f031b030515010201050603100b0105040306050108010b091f060e030307050f010b01080c210c070f0b04031d0a051504080d02010e0d1b230a050c03070806070c03 74
    0x10071800b400d4000d44a00324006038000d4102615015042a803003140c04841078000070841000483c00d99005a501c541c041e000003190103c4c0028941100800c140d06050107480c00c0d43e0303503131600b04a400c02d84c0245001d035500d0035038103080d1410710a00ca070001022071000a07800c182880a918070003a62107014240704400640401d161824801e42300c0307003504a42651803080310301c2d0407140a40b140c00001400207541c6d800140d01590050180c030071401c41c0426600c000e80c0500d02410032010040c0411800b884244108800108c4002014803142d10880348001107007000d26003d00000c0d08090003070240310808200701c03101e48070442103070100d8800311064031104010484c84502303442207800000c4140a04400c4603000e0350150040d211440b01c040488011040c40c076070444013003c043d998074042e448201021b50201d400b05041c00d61010b2030354000c4048860f48042949011740c05e210496a80d08980f607148503624081c42044014031440014001e5850a414000d1110f07030f20403802028082c013040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 309372517 1250 309371267 309371297
    0x608160207051305011505030108030f0c01090f03020d03050f061819020a18080102040303090506070c0f0f09050f040314030426120702070807090b0d0b070302031f08030a 75
    0x400000104000340c454440b0b0407450083c2c2000c0d14003401103070031302d400081c10110414800d41c00c80e4101d980040145080102224074450f0940c086003000f601366480c0c02c21000481c802c540c400c0000341c440d400404800c1e000110240a54034028a0004800c61103030070003c882d180c0464000500c14481030003907090780c1303084440064017400948407000500c04a440d04000f42c01c2200110307600d000c28603082040d40d070340c031909090340310f0790000034001585100100b06c2424040c02510f103a0348034102c104102074aa0010920091b0030303500c0311006c194541400c00454115210b196082214620380350300394a810b0710060b01614590035003040700140000001c0c24020b0400142e801000c011070004914044c2d8106d41100e6040b1008030410301408a0220311218000594001200c002401900e1601c2c03030b20b00404024485c059010303400c4024281074200160007141d4240c424a0b00c0d80b801600ea0134010458a400480f00c0c0c1000044070561409200508001042e910100c84614003800510461341c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 309373767 1250 309372517 309372523
    0x70e030c010c1704090c140f0909090c030111130603230c19080105040f0507020d0513260f07030809060313050a0f050d090e0109050702070e0103061a090106081602 72
    0x72650301c40d203100120b40403404012035040f80001c81300607070f0341c40307d10748171802c01c41c002d4400c116185040b800c00308580ca6031b03400c044c203403668480184002c2c1c135480d040343c0001ca403d50b01c202191601031032002900300d413000240c40e001c8000c1c00003464200700714201e0051403034000445280d10704440119800051449400074100c0d1081400c244240c03010781116640036018090a01844d031043c1c3c00d001c00070100140c240300b001c0c800d000c01ea004040c0006403c100341c403158441c440440c15608403500219140710040c071034400740d407900c02c2c9401804a104400c181403104042d0303a0080d64101c082d0400219500000b95031600710200d0b0342030350b41e40741d804040c006004d007000001c00500407074210406000c041040480168003030010f5408090700c0e00402c03240b10b0000d00901506060802c01404607443d660311180d07210b60140120b407605910380c90502c44020099108891881d00d840402d440204c8500c490780d00041c09441558a55040000c041d00843c40148401e4070241e05111401080340700b0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 309375017 1250 309373767 309373793
    0xf0418020f041203021b0303030609060429091e0c030601090f031b0515041809050a0b0103050d0e0f13090b0c13050904050c0904060e24070e030c010c 66
    0x1c21801c507525503441c0c8038a80924103c40782a030150150b10030050101211048004c8842e00080c051031460390b40c0c01c200f0820590180c0744503001507540d90351070305501d1a60441a00c0201131140c0880cc040380350700700503000b10f0013014020709041c00b4003030711158148a00b40a800c64001d200440e165910f440040711404030b290310070104054800000402d00100c1c0c03041c402d89003001d141c4010300359124024080d900c500b0452190f802d003030070001000240c030351540740c45501024000100e444007007526510721307000c3c280c031041d42c1401c421001042000800c00080551840314144913000015000004a40810118980740035040141240c51a11015407152070325036800b0300070041764201500b005d005904001103c030940403603441c01003541d14141d08030500c81d6030310000400c1001c41380c005008580f08003900403502c81e51203005500c2c040383d091068284690b06a401c0e00079403e500060f0010701500079285000f070241c520a0b0410301d407404a00c160820340c1c01e00307040c0426102c1e494110b01074585 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 309376267 1250 309375017 309375037
    0x26070512120a050c1902010f0c03141206091e0609060d06060e1006080108060c16050307030503040c0501030b13020f040b03010b090a0b1c27110a0b0f041802 69
    0x100250542c803494204015002040042e000c5030202d01441d00f0b0401d04810601d00a80460042c1c90680015072041015680d15882440c0c007405112000e034550250390440405506844140001c016450501d41c021036888462004588031400344126101211500540510301800914000400644859030111a01b544c084410042d00303a07502d0720354403140c1d000e0714401c0c1603100c03241000507201d02c04c103045070503154030401902141e00c0e4038100c0b00a603070000640e140e14484001403000031402c284050020305e4082c0e2165541c170300d07052410580e05802c540189060500c2d00b960100aa21801c101091400820000594500000051403214050b0b9030083d10504d10020000c2122205500074200d4130720281c50700340b15185c441c0f00c020100d0080782400d940100c046400700000481c0c3c0c0c0c102c089140420004642e18621507014031102c0201e01d101540c00420100b42640182002850b000080c10250036050800b007039910b00042e640b096103d000030302c1c40d01f0400308404400c154102c80120308 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 309377517 1250 309376267 309376303
    0x709140f060f0c010b030d090602060a09030c0b090303010513020f16030219031101050f130303020f04030f0605040b100b0d09051504030206091b150a0c0804090626070512 75
    0x110fa00c0424040c141d44407520340680211b00d510040745010740d0035901603e41300e40150090760388500310b9000904035448240c00b027000740440c2072f02081380f04d20900d01031308040c00555925818a010701413001400404445014030400c503070b90007501c01d80300751000310b2030000d04640800c00e0742c00c040b85001c1000c541455224001c00040003010b42107103030010701e031142c1002407001da622241001d800007821903402c0c019150310901400002d100341d00405480681140d56401c068417500c80d4910003005c45401c442440d42c8030180410f003c103000000b5407041d41e500201824a090200c00c00b010301035450066046500d4488000822000f0705c0505c0c2e603400c804c50546a02d00c3c01e03080003507030784034261000c4403d801442141c0703100303e0b011503c07900728890140641c52190401407448481d81c0c840448081041001400e0390001510f03400100b00500602070003080d21800d04101e8040c0c401c880540380074241941907072080060000c17901004841c401c64190f081780301030404840c100605400c00a100350 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 309378767 1250 309377517 309377527
    0x150a03020915091f060f031e09051006030c170a060507020102070b0901060302060901050705031c151e030b0403110303040f03030e0604030c1202330709140f060f 71
    0xc518500c5010040b10403500c07103440d5141d04022680503501507003000e1803e0850351050101c0d6002d07942101070700d030039450000742c0d90a80091480141070800c007220300203621f4113138034030a201d0104140b100340c02c00140d080090520b95588e02071910118820900c2c0400300b00010441c100b424007400c0c90058104800340060300d04114024001d50051700c0032182c02c00c4640c0815100d4005110b2602502d9014160518044624005440d03a4100d01030072602880704000300e0118069404001040340950700001c5100d8050170320700c651002c0e8070341002260301f021040c001c0f1380a240c40710003411280c12803444000c3e9280c505085422a010740704c41c11080c8000414070003040640c0c0c2c0440344050207035908000000c0b40c0041e15450790001d482c040d001401030f40c07030301001c07848000200c0a0b031103503401203803110f4152100f07161030002b0342501d00800003107002d50011619021403403640c4c412500d2811a003200e0801042c406070f0100200c4084c054032900051441b903440301c000b01e0301664883c44249840e1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 309380017 1250 309378767 309378781
    0x8070e0102030705071e172d0f0c1e03190f0507170d030b100827060910020702060d091502030a020d060b0c190f02040203090706090f0302010503150a030209 69
    0x1000d144100f07a04803880d00001e103129600c2d000c046055540b00580400130b052601c00010704002c10548ea052140050440140308080061245001100000c5c1c0784080d0310900b0448030f20380f00d925114a0b44006403020039a5a40400e034034208004500d1030741c3c00b2501c581041c0012800010380200701e44502034000c210341560240700c94900140034110b407040200138000300c0559221403c41500201c00c0324800c14a41e0043e05019400b014102104004450036a82c0407008840403103650f5194200c2c1050025204c4140400910003503802000c0d0b162504aa01141652140c50201c410403a6110b040c0c2080101d020702c0c2e203601000c051003e646074100702500358000d520070020700d5900c070301d03284001450380284010781e0f6445280c00060411040000e8007000345400d0000200c03070000b5a08198030060303036203101550040708090f00900c08107060500140c4905455004991140c020f200c0800060380c0c0314040b00c0c1e0000c14000c0c050124010000420041c0320290002980071494000b00485 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 309381267 1250 309380017 309380039
    0x2e0603061d0705040c050405010509030c041a040614010c12120203180f0a030e1909020c06010f06050301080a03031a0d080a02120313060e10050403020a02091608070e010203070507 79
    0x800341c0682074032040740d40c2c0c10403c0215242084044040780043c80200101e40c0900c02401440da8090150394441d80408001000c5407118450a40f110801d008880f440342814441c030000740c00740d00c50b0480e000075440c0019186404c1040300520403103040c01100005c0b40f107503248001554100e0401d544a05080507003103011852015020018400e50408071250000001c800c6001505038580c410040c1c0c40200b4008541180c61039400d45580b0344400007031401c840d10081940c0040c3d0806400b20b54141000c0350011441a404001003041c02e0006001c010004140254a65814280000c0f0762881d02e4188201030310702501d059000072090840001e01c01418003c0904100ca40e09484204904900322102c601096400c0102403039140c0400c0000340055215140b8281d1213811600020320716080030080d104116001c9005811640d103040444c182a00c40039000340047c40c00240840d00c650f001005040700030240d00400000c100e96480903402803046602c000e0f008801d03100101e03110441416 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 309382517 1250 309381267 309381311
    0x1030308040b0703052e050d0605010f0501020f06130614070f0905100e0d051f09060c11030702011808030a0302180402040b03040b04030509130b010305092e060306 72
    0x140311a00d41000402e064480d1044500c1614824406041d4000c18202c800c030307080d40701401c1950851401c0020400c0d42e101480d40782609e10031003010503158104201e00740c10040940c00b060541d40400352581007900081680d907404942d010701c0d03881024545c00d100c0e01400407818400252044007003842002c1c4ea0101d841c00c2842040d40b0f98011540d070390024001c0c1c440c2d054009d00c00007200e540c070a60091030001100102103000324101c86c1181903001250000280c2080b403c2c0722b1958035121002000114020800ca01100381401083c040c405281e4603281d120341c801c000d04000c59042641c5c0b503081340a0030791015103620803c59486602c1400050300079030110181900782203044c14003450615181c02150b0954400c48581f50031030b00c42c0e9540c11071a58000d00f0403810b1020502030b41c240741c1c0b00c040400c0001c62580d0720108015900e0000941107450103044901540c10082c000c0b001e42d4a40b4403000840000003e04c3da030058848c8003480000c0015070070080180741803403a402c0c2d6551001030300b06 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 309383767 1250 309382517 309382523
    0x3030d0609020c0105180a1403040806070c0c150c0b060a0b0a050909150a031b05030a080307231c18053301050622080601060905040902030709150e0103030804 70
    0x401600c0f00d182001201e641841c03038009a510400d0b55100003241d00290710321231000b01d021607041c140c403401c030a410704204a07803e9000803602410842404201f10382c0f0001885903500c040e0714218403e40040002d960b10790090107420072100803600a403a500c030030400a046121155880d0b200d0550010080e510070b4009620825070b02c004a032145806000c41e000d000c0000b0710507100949155a003000d040d0540c1d001f400020003c940029864806100c4809490b1044011941e03918000d18003a040b107000e80000045d4035100c16181505070001011181c09c0c50020a1a020440305c1491000181800c06031035810340e001e8000c00d0040080004a020b1258103d00c00c0300034240c480000c003591440400d56624880e00104010000c1b814040010903800d81d81c19902c005d2891030702103078000260281e111041d43c1c1c2c05070700100441540301d0f1a40010b46000c90b01400710282c240c0000f9940c0d5118024000c1959440c050707820001699003c2400508060b10b92404560b500c0c2005004000308603010b07 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 309385017 1250 309383767 309383771
    0x1908010606020102160308060a150306090e0105090c06030c130e0a060509090606210604030807091406030103110103090f030f030507091211060d0614030c0f0105160203030d0609020c01 81
    0x407036000d006000ba100e80c0d0014944078040150f050318210760b4600e0150185402c11207018010035010b401400d802281021914007145c400d141030000c41c112504051030250a074501024000056030110b900c84101e003080f0b034019141d4440d800c5441c2e2900c181c0c00e28801c0c0c00054000020711103140d0511511600c0483c0003045659503035810b0103820001100d031138103150440000a001803402c9d0741d040d50056940543c21803811002024645000d030103440c2039020480c01e0040251165119421001408058495402d09551840849d00d03900040c0002451281e5008034200180d21030381c00654503542140c402c0401a180e824050031502030850b900300042d003090300040180b40544800c40c200c0b09034a00c21a50b0384001c1c0c03620b040070161500030343e40c811420040028000350502a0001a180c0e42000711803482e0301c082014508031900c0281802080b0100c0610000e80c1c2120640320f0600840b489c4004074136240c40041c4c190303c501c40322420124a007035404a011007844c0d0151100190010003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 309386267 1250 309385017 309385019
    0x1a060d06050a0902130b0c0307020603070e040e0706050a200115092a03091109090114090708030901120f020d09150920030109020a0b0c30160219080106 67
    0x8041c01d0307105d86096504200c0c0740b800c2c1003050203807060003401c0040c0d889041d00e00f000c07203507800148107034000ea44400001d40844140c180f140f81c24410080004041001403042b185000809041d5004154902d424403101d03880c04c2d0351107100342e031a8030138810b503c0008200508200c110341c20712181d140514415075181c0081c1c5804001c5513a403003841c0e0307000a40314035049004010224080d201401d070407a10007284803e008100d8030381030b8060f40070310742d40000880c4104001d90588017001c0b00501342d141e15400b02c001040007030004411542c1a000030300e009405040706942240241c07124000458440d48005100d0100e1600c0c0e511128010b446907002c4206081c01e5034003c015109004c3c1c0280c40440e4803c0d000340030f09002c0307032014111940a800820303401c1e2103400003440c04103154003585841000054140d59a00240184404070518090900b40744428008a0a885d035038503052480c0f140002030380240d084040d00308200b04030303802003060442c0b46400c0b9050820204610500b8055070070018 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 309387517 1250 309386267 309386279
    0xc03060a0c0f0905030304142205090c040b0a0306200c07170a0506070e13021206030607050c0d08040201030914010b1002070302032a0a030605040201180b0d1a060d06050a 75
    0x21560080320b000030001c0d4101808e006c1602e5002e8003542d00b940d072202400c8043d510701c84506051814400b040000050580382400d406401c0401c1d80840a02c00d510303180f46c4907000d980c3e1301802015243c101000069900c0402c00101003403172f000c140d03540d00c140085201010244005400030588800003c1c00308201c41c2c0c403440039034034508000001c5c0a50490000604407500c00c5981e1100700d070008002404015400c03000b42e0032a03021445001d40841d10b10108079142c01c081001e0b0303412a07132a241c070342d20b032034038115985450b520080078440401222030042400d42e8800d410800102e074220307507101141021901018000c20020061900441c80c0001140c980c1d40081481c4045a40140140610400b030707041c1e081064114444505070001804141c500f2030300c3d041d0100d000707540b24000008003805c0500001d011000c51f5941c40c0341d40c40d800da006010b040381c86c2c1c06132041400224808648500072021814180701d009800b02c0d003120020490000001da6600460120340c019900c0c9564503480c0d0b0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 309388767 1250 309387517 309387527
    0xa0f050c06040623090d0501050a061d0a0b041413021201060f06081008010903022107030f0804050f010509102304080c0a022d0301091e050c03060a0c0f 67
    0x4801e100c0800c60102c0c07a6900c84181d40401c0744400c0c0c442109910b442ca2420000e040300741068000d84580c1c1d9274204105c41c1c42c07042d114620180c10a40102e681185100211056030140203001d80c0c10a03440c1c004101c025211307904100543c1a0321000b00b0403a1400180340c030f12800071020280c0c4034134200043c1403581a4180301d818251040000c900e0022405d00c9000d988048c00a094400e02c01d00400001400460a1107070720541803195009d448a440380000408441e6030060349481030800410041340041c0c1c110204c0090a82e060420101d15030341e034104035080c0307402600030311055402c26080003500300e00030502d04400c03814280d041290440f114032079148140000320b0802918411400b00740800d40a80103000084100d40460f071480c0e40031f0b4041610300420202500016041010b03540c88801e00c3c450403201c05000f54020412a01d41d03450b2283c20a1004500d4481150702071660327010300000380000140040d010701280c04a0411828500017840d0008030240080e0b2925022040c051180d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 309390017 1250 309388767 309388769
    0x40b520309050d02060d060303030507091502060f0a0e0604050c100203040e1503030403060204081e0f0a060213050406080a050114010e1605041e1503090c0311120a0f050c0604 77
    0x155440381c0340d50741490280120f2103004842aa80542e040c4440341002e0703420700600c00a141f0070399010a4905190300040c140b01c800385c200241441681a4189905500044840d8000b2840035072a29076120010008001c15805641d2002c900035130342080144440010404141d071400e46040d0350b9100e08000403038407030180380140750700c0300441404101003e086880c3c0c2d02c412007008050345d15091b520355400d401c03039210388e00550094100140001c0c494200f00400d510700308040b40038040201100c00e42544402c0040402010640d0110368208040610b40c2aa0080e001c003801c1045040d0316409040d42d28004200b04071041d609041070304100e0030800720030604940252000a109032a003201d104403a04108a80d03400300407040c03100140b055110324410484450202c0d584a4880c14061901c565206a02c400b205260408661380001081991600110390308111a003164000302e1002907044200081e1b8140c1a1141c05004024040122110700e681da105908581e120003400040c00664040c07 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 309391267 1250 309390017 309390023
    0x324030304230a080d0f020c0d0b0a0b0f03060f010330080411100e040614030d050c150408091e0307061404030506010308030a050f0402060a0807020c0a0602160b070206040b52 77
    0x741020032f216444503000340420f100001c182050180d000c42c0800c0c64014116406641110104010028048543c0402f900468640f0071311504400040c0e00007070642640c281c2008104600b800a4140440d441c3c3c2031203120070003800e003c070070400c02e0401402d00a42c20410352040b80f81c80303400104410302c030040c20317014900a00130700308220102c8800c1e100c40d0010b01904100d80100c1a01c030041e11000c002c0144102e21841c0c1040c0c0300c40c008402d0200f524032101021032003805000d0040036030381d0001001400c4134030fa46440d696030703000d0f6060310a0f14051944010315502c510f0001004201040e00a5445020400010421a030710005d030340c4160382c41910041d4212008101100c0c486108507502c40d0300400c82d00450714030000f001d01049600c040c9038840c00040e0806c00e03a02d04108081c080c060000c20b13826641900700b001580005a0034802d51240d0b0484000005458000e020007000c0002c4050710005e680408041e003079001d00d4071f5a00322203901148000801d01003c1c0e0348440c0306000625030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 309392517 1250 309391267 309391283
    0x1915030c03053d03020d030c1104050f0141130b060405090406090b150418020604170715260708040602030612030324030304230a080d0f020c0d 63
    0xb011140c2d0603c10070400c3c0501c011196201c5010000d80c0310b08900a215a103c0d6035240c04040c00340c1000519281c0922240b44514200710901030b04511194a06054981494906000c1c4c41c1000e0307410355011408101081e50006100032980340001620054680c07903060f00c403212070780032600111040705c2e4000d07046940304000703010034409400d02d801c9560348240b05020015500390540c031480300e503c60881d5900718040611a07111100d0920380101e0a45a44620f450120702c100c63b40095028080ca01070004941548107080b846018100700000090564101a100100000304020120fa0706030302001d0100c8140f08070b150080c0010100399100704002d68580c02245c40303c1e65078002a6102038a1180d010314000c0724400c4540052004501941400340343c4c0c5d04002c1802e00300351100f854080000d201c1c0d0005d0104205115030002c028200c08845403001000301041400500400c5103904490300c4c0344988c40d40044008d0b0450103040042c0142d8084130304800c0300d003081120307442e444640100019 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 309393767 1250 309392517 309392581
    0x10020f030a050a0c020306150406050402090a0504050a02130b040302011706010e01030908130b09190605070323041215020a050427020c1c0203090f1915030c0305 71
    0x5105034003030020364035a441c052070407040c05c2c2c002902d005001d5070709185070180e40d5410307240e520b843d120752001440b040c3c805508100d081d0000a11241203031089034066074a403c0050101354003941210140750900070b00c008290f813910b40c06038a0740c0040c00200d01061000c03d0851151402010452061034140d40e0716520390881e400450250118480880c1d060006012400a041c0703402018005071206c0c2c0d05880c0c80b1107020081000c200c0c050003410184242a030400d008040d4410300300e80700349426040c070240c03050f081041e030102010301c4024681081c002160204000340b0002050141a0083c0100e803085004950031404a20905c00c40dc804600c1c200020002483c01b001d00040c1e80c100003000d007166204204c00002a43c2c0031003620b41454001a4000c6082c4210380038412801183d13200a41c1849540008a50140750601807d8424070b50103240068610607903413110040d0400c1c21203011032080b18003000e0098500301d521840480c0c10040000c410107070074403c0d82084596174050b9090780e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 309395017 1250 309393767 309393787
    0x3070804031515180e0717150f07051c05010b0309060714090d060f05010303030b03100204060c02040e1e030a02240403050f040902041d06091608060d0c08070510020f03 74
    0x203c0809101d41390700c0c0d00e03580c803264404400e020304001007510f000c01c42803410060143c3c03800c100760902d82c500c0b140a0442404490b0305800c0c8680d034408210b0070110703038812480c0d2448503119941500d01107031a0524002040c07014900010318090b83c040305c11139109440b4941c6c26074400d200702c58104d6a004080c0519071a916001d4201e001c114010840000d00701c2d00b5496003401e4410980040d4042034031007641c8802030404102c80300304070280d01002c40c10181080c0300105510f100400c040e00c03030b1341c4034564141d5849080c4014641c401c00600c2000348401c6c025a55600c82d04820f14600150013a0030300b0502c200003d200700905800000c405903000da0b075507a81a40c40d80c11600c010140b07040d0600000c40c85004610040c006030005176100011030527805010038922000503c0140503802e5481031100a00f2507410402500e0494186400d1a039104c1020507031200c11050301400c1180c440c00c000425403000720b00c0d40b040d0758040c0c80a40701e40d8106241640c0c7e03200c0000320b5840b20b03481000a00c1d04 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 309396267 1250 309395017 309395039
    0x90309080d0c15140c03010602071703030c0702060c01021305150418050901110d0510051002150705130f0302030c01050f0706050405070b1b0105012403021b03070804031515 76
    0x401501d41800143d21104500c10552004c41242c50b4100c500d80000103002d590b0301040140b0041040c001d95102502110311059224000030f00041045500802c0850441d43e8980958090190b08070085480e5244003200c021040740c61f21669000c1c069000c0c6400090044a08480644100c83d8041c06000c2c1c4504c030040042500600282846d507031940c9074000855013030000c04032151241004181030800780d003107074140611a030115104000640c034081e4619000f050800b82d0310001203e140d803a54074040190341d180301e101129108544104000318101c51060030350030540f8000d0f41201c00c00101c04005491910408200c031815120a1002600060160b00010b81c0580f080050310740f0f0030365032130302e05107241c102d41d80c103280041d1000e403900d484500074440d60703004012400e0414070680c1c030003682e41c0c3c006050030044003c154001803288000c030f40c9004a403070702d0582c10742129540c003401c4c24032000d80d40190004440142140d005d0100c0c442503030003401c1408204040c01200c1c0d030300d4008601c90f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 309397517 1250 309396267 309396293
    0x9030a05090402040503070b0c0d090e040803040501060e240306040c0510090504090605061c081b03040b041202011202030c0307080403031d0607090509010b09010323070201090309080d0c 82
    0xb074015000c000109958405100100c0100049003034242ca91080400160804035007483c10707010405819020040050300441440c3c00540054005540b40c95a051086c050401c0b50000d5210b034240714240403090a00b800d00001c031481407007609002401751010182c440105440281c41009506014481c514091542042c549140e05140850f00d81e40c0000c202a585031040540c0c2c0f41d6a1841000f009040508400ca02040c1a08508401c00125501c0e01c0c420300403a400040003659800e07803000c401c0c00030000c031400360410380941504e881c3c0c0c03003080d401c4200c64580c080740000c25003410450001c1d440c0c000e42c1d001d2121500c1e004c0c25955880012520076500030010b070101a203d03828010701c00700390609d03950044041e401408072454500c0c1c014003c5a02d40c0c2c804e030b009820100c010000e640d1403c064400c40c1c082441c0204840c2182e100f4014030300c0408900155042401e010f0203a01a015030004035403d100e900e42c2140c41e0341ea111030689549181200d10040380d0541442400520200000d003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 309398767 1250 309397517 309397519
    0x40f14061005280c051002120c090108310602030411011b0605062b020306070c050705120c090a02040501081005010507030f0519050304110a08070b0f0403080a03020d0b0909030a0509 80
    0x9000c138580701e040c5040d0100c104000300f69400a104160b0102c1c0d2003071072381d00a000d11682c61924403d0303800201848401815101d090741141c242400d0070181d65a88443c0c0c20b803510580c2d81410080c20084000c0d4402e03a8115070000054408085a50094840c403c50143c0c404a170b40107031034144c07030b40ca003d007000410542d0f02c40400b2102c034604200c204104007010f01c00818800009000d407040c1486c007c4050708000901c01000e440000095001560500340c51701610b40f2b42d400103010403201d2815510503403080d4050100010000d5902c5294068070884800340c4e540240b6403a0265401d040740d140c1d00840303000031420815003010074015160300000d48c8640c42c096262482003151100c8a04140c0514400104000180000d01c01803c0d1070000d0408100c1d000b036121850700d103400c2d98480b43c2d171143c1d07509001c0c0451840004036001c0c0580e0001c40d00310812541e11085604c004000703500501c40f00481500d0039610290728240b0b20300182c4600f01440065140c14400300041e40c2680118410b6 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 309400017 1250 309398767 309398777
    0x9131b0b0a02030c060c0f071103010b040c050c07050603160305060f03011104030335041b0906030b0a0903050405150c031602090a110711040f1406100528 68
    0x5911510180203014001c22079025580300d00d200d442e0142042800740c03451071040707818809141c0d0450382a0860b04202c1c1d01040c00900d4050750008a0b01400b22400320320742c414603015400381c0d010b420000038200601d07040141c520319510340741003040a0005540b1030040400e111f0601c11307924029440700743c001000a02c03a00141d08241c0000342910b05038900c3c507031600000f2400704100b5410214094000c1c440d8026000126000b2941e02c402d5410100066650390000022400f40203486504541c100b02d49000c01000030b8503600300001428403440100d0302c40c031401000034461312861003031081c0141e0540d50945032a20b41020442040e0210015005c040c2d4100121600020104010040100e640701450a941082c1c010040e150300001e00043e2480d040c01c0100c0058541102203032a81540044000c680d021000003040050481946100d080c91400c2c0310440781040052150707110354030446006824129081045860b400b4050b1039020310b1103042d03000302512030000f0718400a0301080c604 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 309401267 1250 309400017 309400019
    0xf03040f141b0105030405030a2f03031b091809120304060e2806180f03022118060a02120406050304020310140601030f1805150609131b 60
    0x3031041c058141101002003540061100c00304a0a8003000000c20755090800030f0031464940c0301d1035220b01c12580391900b040040000084441c00074000c81c1401424111140c1c40f80281c2542d40340c0da5031040d602088407849a0990130407010305d00301141d12000000d01042c03407288214030f851405180c094aa22528000c480611410204400140d8401e0b4050170010524985d5003028a0405049100c440b1020340c801d6280060500b61f40e40351000d280d03010f0340020b01080a4901443c0500180c14002c000016900900c0d0615600007040e001313028030f00821b07c1d904400700b00600481c1c826041c24200302040305020400314908075010700459000d500585401c03d11040c50f4428543c070a4000101041000c020701080d42401c00c003001c007030100c0c880100304000055000c0c41440c0c10081901e0b04150f1241090660412645c0169010b000e59070f4908221134020301d0180d0302d41005030360142c99208010005182c03803030b1008189004100034404603503400e0264903040c0c130010034002c10251229003454 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 309402517 1250 309401267 309401273
    0x1b020a171b010e01080411030a020406030501050402010806060301140d020303090402040321020102120a0b0d170403030e09010e07050c0109021903140f030d024e07050f03040f 77
    0x14440810040c40041c24041c515030041d00d03044280d007980c60703040081d800241152660000d03180e6421039004003000700409039050010345046100e10009401c142083d10000801a054014a0189100740c84200c404d65859042c00181d000c24801d07121140748000080c0e0f01802d10400110b601e600250541c1d240c4aa0780000c1401d03170340716a00468600802c000061409408071180c543d10f1440c82c0300a41c94a0307000380703071440c007000050003400c0310715518031001c04941c2e0707103502c080c441355401100d206010002480e01500c58010b444140c0c0442e0000180c2d10300c1d40703024031815058501c0d50b0088088d5480d08001218543c202540d801c1466507075440841c056900d001540188005911600d90340380e04601d4456480d02c01d100d025500ca03070088a560b401c02a02100f80c41d21440d40c0300c0c00580f50040820b800240d004070380104034861000a00c54180c224510701895000d80c4080064446080000000b0008075402c644060006805200740d88806076501d000b1a0003d02410400768503103030a031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 309403767 1250 309402517 309402539
    0x1106090d0c0b03070908030a02100b01050d05070f020c010302071a0612060a020301090b1903081309020c0c040605100c0305070c03021f0f020c091306060b0f070c05040c1b020a 77
    0x24002e210b05032000300c20001c40540c03100c0203030040c208a4000e103017860303203200b000b95450081802c221151622901504880c1c1d00c5402940d0174049881010301c110f050030080500500c5080c29008014040d091520f40954042d0003219541030b48040c9551900300c0d80320a40001a2000e0600d560000c0d40003825000c030381c41006924040c41504c40c00503520751412014200321405c00a0940c010010100306c80c80f40494103c1c50021a50002c4405540b054170500b08101d140503034000409461011407102d0003010005409041d1440503602000010786420400c40700303002500444000402704084100043d00c02e501925800d480307025140d40c155101d500080320b0702043c1d000211140c0e42d0780040c1c90025842408201c0c800075600281c001d4254001c0860705c0000014100d650340340410440700c041162540c004d03002804041c2ca420345860b03919041800d10307407001000380c6942001e5000030542e49424800c404403070200361540b00070840130028004140c0d080b408141c0c0d2188084030001490030020b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 309405017 1250 309403767 309403769
    0xd0c0e070507080d060e060f030309040c020f0a06061517011202030a08030703150f0605071b03050105010e07020106091a10030902190f1d06090405160303090801050f041106090d0c 79
    0x42034003c05c40e80d0414000070f0364184000c100724030401403c04034405a8a02200300d41e02c5800903580031480c84200c0c10103070f103090f03000c0b0003501c00f42c45044845014800542d0101c01612500e19401c10742031291340b000c851701c20201c42040b06291b004001004181928420111203e1019003a2407a03000541c640320020741044801401082e03e4100040a090b0440c10070b01c00362900d60620005581084c01c000d040b0700401e50b00415103c41690301c007540d058002c1c02c00005541c880000e1106603120242564001001c4d02d44101644c00c2803c041a4900b00d40540e884070340086895855011040040000c84036a0322000c81c2415503414124001d130711070103406240ba407030820320301c1042446c20240102c04c0704160b1050843c100106514900d5105182425800c804201c03a21034054540b42800c1c0c2c107060b090401811040d004cc0c800204040e001550304086660002c000c001940e25112100402c038002c84000b8407182034403c0e0711405250580103043e2215018054680c001820703901d5400030501 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 309406267 1250 309405017 309405037
    0xc121103070b0319110901030f06080601080d0f0e0102060f0c070b0703150e0c0318070f060c020a08060f0105012111190c0b042402071b050d0c0e07050708 68
    0x400810044c10000d09429910720b1460941c00300099100030b902051280034400b0171504054907290380741480e40940d0810f2003d440308009032000da5a50b8440d02d5524405165000046254401c5580e15075010704447c200b5000b042e006801c2d01d94034180e52100c2c4080090004030315400911003600800c0c1c503403c605104000e103880000d4407004404000580d40e2007684140c040012301800c1082031100d8130203994111940804071400c200c581c0d10040c2c281206608128017008000f40d000881c2a402405014014000d4440d800001e4803181280e03100c0d4001c81e03c0d80c1802810000410203540b092512000d002d0611212404441d14000128250f0b015202d2164000d000410010440c80c3c584459031a64102400d0a040200581e5100002010014009405d242e1302e0b203155002e800400488000e122060842103584806a03c1c0501c4811400a480c0888240e51100460345060050074540b03201e8110000305102032819260580b080401040700007040424402c960000da04400030b001c0ca049 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 309407517 1250 309406267 309406289
    0x203040c0806060409080d050c090306040606030b0c0c030a110c03010c080405060f0601020715050403060507030e0d020615130b121011092d090910180c12110307 71
    0x450001010b1820304040e0107640b06500d84040080002d100c00200c61690049400100d4556102c41c0c90012034001c0c8407600d5094010501000300700a2141d0080c41584d100b101941c10a448011514506015040707001b00ca40e44108150f050250046441c0740c10000540200c450250781036000c00d0a5660403500440400c1660307040c0010418240016075004030059400da12030300d0303c0320000b542e071805032003484a090600018050050b00ca00c2c00c4030091070300f00c40d05220900742004d004005019000c9000d807240030b00000307250550701c0802c200d401481c032040350103039120b5407000300060498030030500000e0603030320710701ea154648503c3d583c0340d00c6800c841c000d03251352a0310700803010a844220029031180031040000c100d9950f514180c07050f213502c0100301002c80060090480d0011041802220380c130810758004c000407400b00190300d01d0840a540800c0c4020210401103060f040900d4200418011482000307014160001c0c00c000c0c5241d000740b01010320100704801090804540d508010321101d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 309408767 1250 309407517 309407519
    0x3020105160c12060506030a11060d0204090c110d020a050c04020903150a0905160503070b0a0e030a0c050307060318021215040302030702010807080702150c04030203031206041425120203040c 84
    0x6107500c110707681b0580c107070050044410a03a8074088990a03803560188035100100e0030289042403a81a02d000d0b100b000c200300109011900c0c045c1643c03080200d14005846110b80000e030041c4042240c0700c01d5644030004150402c810340030407000c3c3d0003041c0c80a406204200c2c5498401481d840220302600d452080020300d0142410560305125840c0d0040c50a174290b00e40c10000e54500164043c1141ca0390b00900c1d407104c1c05a081100d055860344400c99049c441e8014180c1423010441c10300080742c500b1000c480d640c170b90300c90082e416681045403400024079400c2003040541810080121005502c8003070f1203040c520401d0b00800e803101130b0740940041e84081031040841d6002582c90389c128480e070405510518100c40025501d04a00d00d05c101410680404103408441c4201640c0c0510390040c166511501800c080010780c00040310f4882c880c0d0304155900100c204080506401039820484d221414400b080c02c0010329520322896508111306848081c040b0740d00d500c055802148642c4440d8006 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 309410017 1250 309408767 309408773
    0xc032709011703030a0f0b04051e0a27210503060306010b040e070f111911090103030512090c04020408160503010c0e010804020a1707090507090f03020105160c12 71
    0x120348141c000c1d1245004074004101c90100000550382d00c40701244010400c203403240d01500c080c201508034590054102410310400c5140d0384a80400c1d040e4210f10324105650b029180800d94040340c0c604511000b8480b0740b610005076100109644600501d8503460154032607031450480b0402040c607400040d004130038081075140c00d009490061045080080c20b06041c880d1143c0c030141d0141144090142c10b074030b0b010000340a0a41146a0201c8109450b14000c0f00c034035112301c0410507607084640600c21003410b400d034900007041605880c0c05039602803c00092041400c2101400b400b1b2440078415900c0d4140070f940c1e01d00082000c0c1c0600c4016011070b1035490120404441203400c003500c2641050211100c0d107030b022041e031003406824601442c1640f580e0000c90744a03016900484044000f13800490840180041c0020480d5160902000203640e00e6908460410f0305004510181c01c603080304002540c803e0001d0080c1d803890f034142030a4415650b03102c400501e03481d8051900050315400c01070034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 309411267 1250 309410017 309410029
    0xa03230f0f0f06010302010801061805100e0a05030d02121b010510050909121801030f050901020705070b040815072f010c0503060907030207050f0f1b0103020a12020c0327 75
    0x24038240c0b8401841c040d41180d0020384921814000d2101300188100d901c00c16404d441c050500800010308001c1d00d001c12341c04000e0a143d01c42203120b0080100d510300107076908000544465102c41130740a0041e43c007202c8901c0300d0540c05058008441400c605d01400841028854140962884c00e8505600d03460001840030841000303046121903003210701000c8c030b00b010f220202c0310351214224203140d00b02507050050300101461809990141d1800d0204280f00d80154008c1241030b010350202c8940c1a592070310150f20307118034029100749070010301240c5903061038015615001581030803d0130720307041d0071a910f00c1c0d41048080e203115011107800030050780b10300038482d403600e26885250503499890200085802003001070030942c00c05900090903821300200b407110b06200e8045a0640300f525440c1c0028650f6910b44101d214140360075110203500039806031080b901b10710792644500d5050b03c3c032586601c0c0250401026186540001c001408a48548160080c2e404081d03034003000c0248021800c1c060 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 309412517 1250 309411267 309411283
    0x70806120f060a0c0e030c0415120606090617030a200d02010c1b0f0807020d0c0b030f06040e1009110a2d0e0c07030c0206161703060a03230f0f 63
    0xb0078040c3e00011441031b5280440c0e40c042d448025200402c014910410711180716a450740070b00c0341145c66400000401045400c404100c851081050001755101d0810581a08860080aa655208005412601e4000c0c01080240036480b004c8481c2c984004454508042680680c817005035915950b00705101d030130110805412510099801110540e913441032400c0c190100c0181041d900856030100310364441d04d4041186602031000c1035002d64541030a42d0641007590b14051007404a0000b500e1414188211101800514000e000c0c140124481c200201620700c0143c404509548030381d106501d4120314500204810b601c14109846000d22182641d51084550440401914020080f14444d0740780c040d04400031415040d034681d050303d010b550002d888071000350820400300f000e140c46001c44c0100d00d0894004c01d0751900010700c075140d040750784c4012141140d102c6070300b42042c0003040640c203201c41082d90448440301511040d0449070314220402c0c41c1031103d40d00164045112490500c0050 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 309413767 1250 309412517 309412541
    0xf0c0a0201120b030709090503090d030c0311010504020d060209010309051209240a080a02040909030915080405190302030c060109091a0c040b1606060e1b040806070806120f060a 78
    0xa034901d540020340c40d40780301c0c400c1684450707d40c80000c05101c024000c40d10004401007100810388070903d07003d031101d440000c0603404520a4001e1100c1c1c00c80c103004442c81903070300030040400d00c200b0340e8541000f50440c83e541410144d07a4041e81c030001d8010080e0311380034020110880d40f140182c0701003012000c0311030701d018008031821711089080da000d2402d0b202361800a09041c181da66601c0c1342007009028aa122105a41c1060308010505412811300c509a44030b02e0b61006140851003800d42c1c01d41c02c2603500411903070012084031840188d0f440300718030091080c41528941b105180b0203926121086c2c0040c070700c0f50b556a400c1000c104600c44504103400825103480700f41d1625020041c241c1c0664807803100581c0d40001d41401d0b50307008411355a1121b07488842040a15218202c86102800c112007910f030f9402c2d2107004106104104050b941141c815030002c00300c41e641d1070005c6406e0790b0050109a004a030010112110240078030400b001d08a501004110a180075404001030310300100c656 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 309415017 1250 309413767 309413771
    0x102070215032a07030f08151203040b0c0309010e220c050c0a0b0f0907121e17180901050915060c030a030603060608071511030f0c0a020112 62
    0x4080103803600208105000d2800d100385442e0b95502e01100c0f19039251011085032400c03007812801c0b1100c0c14034054103640b406541c846800501500c3c080c0c0d4180c03415203651040398480e0344100307a1860700421030350102207a90b0940b4209603481d001c00c0380c2038100c8118203072650404140d02c0b11035603211034004111001150006494084084050b01500c030304011068669100c54814441ca40110119550001d00800b02c2d4030303d0310182040c10903030000350351035089800704002040c0d40030350000d14070301a55410301500d101d000d0a60354007180c1c0c10342e02000d508005005002c14001c03031003d0007042d10f0101c1500503266921500d88995060901e940111032240402600501c09603d902c04401e42c840401c100080c0c0c03d14040c0c000800d00c1c0542104600e06200001e07140007202e5040e01b1980c101da100704014001070f40c95050780cad62503024034020310b5082580100070050300d600c9100001c080e100402c041d41d28011031201000d80c9540414800c0c103041c0d205000c44001c550340510700b0801d5404035042 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 309416267 1250 309415017 309415027
    0x30f0a020420190207030b0406050421050406032f040311042306011806030e0c091b03070903021504031a011a18030f060727050625030816020102 64
    0x280c00c103800f0301d912828510003500702a10005000704003040185070080358101076440c1c07529105c80030788400c5800f2610f82994100d00c02e2907800d414000c1058140d0303501d8181c10700d81480f00071002003605046513100900c00581e80b203010320012012903c10640000d540d81e0342c0781181043c1d084d20360241d60a500851900901c14414910403001030340c2c000002e178041015860b100d0048810108040383e00c0460f2610340b0b00015003e8140d8001103400d0014015149a80400800c1100c1007078200c5103500101e0700d0089140c0c441c8400d000440d8043c0700d41c18000e035055203075004610a00c02c998078100c62000001000d00a200c0442020500051010350300342c101d604060720f9201003d082004014014004514a1145045080102410103010b011034181c64140c82030556607110581700d01e00802c00b80b50042800981c5d20034200840c58105100b018840e1400c4244259648100c801d4160644600a07420070a81103810707452580740680d440c020a030030007000c402250420b400100e41560310401c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 309417517 1250 309416267 309416321
    0xd0507110d02220e0106050301050c220b040f090506270a06051c1202030c070b0a11150108010b01110c1c05030c01050703051014040c0509030f0a0204 66
    0x40c8503251440d054402001a450500c041055290380e84180d80c0002400902a4a81e0a541c1c0c80315101d040008000d000090390703441803500b00d40040d03800074042d2408018910005042680344030803415800ca41c1c3c03e110390740302e01c0c20300c1580080e08294001e20b1000d504010901650040d5030b04440c040b10000018041080030054900040c405165a020300e40000b07960380c07500303a0048006101c00307405445c9168a4500300c0c0c1207150314400484011110700708000d0414030000a80b603107a1103040c001e01c0d1107800e244c0c14004640010490a0410442200254014106110900d0420301291440345154144860726082d81c0c5140c01440c100000d10840015034980029580d060740030945204100b0184010303055060f180415000c1c1440c880020580002d09055001c148140495a0300f0011511038141e6400d08542d9841144e5400182e20071071401490258400d072a01a80c90916a141202e40c2001ca820031116216450050b0080d040328015401c003802940c0055420b5100700c004140038603 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 309418767 1250 309417517 309417533
    0x3060118060215060f030102160b0a0e03040b0702061b061902180105030a02040504060b03150301051306020d060f1e09050c03040f030302070b01091e06211a04080301080d0507 77
    0x31000c0314014040e1008036100d81c461040d605c0c4c51040c007900a40d91170f03203000800210b8002d00b0000b03e6004c0f688800180c01c0300101c0c0725030b590120310345000c1c5240c00e140a44a4246400403181030380c0c0020300b04080500460203890070f0190b802210003a003c82c4c070702141202c0d07002805903181c0007814010414901c03034648003c100074006009080c002c0e100d4807840c8804000740190341117690064030705540850400c15800186219291000300660500890801d05080e40d406441c1d1022201c0700e4a0708030002080340e0050540d0044601d4001515691840d21481581d0654040c56620325104040c0c4450000040c0030b60103400868414420b50520002000c064440144041e00351b070700482c450010544250111240f058012280c031565585a80300c607001040d40035580c1070100c00c45140300000f4902d5008220842e2400b24070f0b641484a49265090382e1030141d03104031014182c0050140349246d80304140c1d40194001c00b8401d8480d8101005585003d96001c81d0000f4810244181400a0890 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 309420017 1250 309418767 309418783
    0x40f0605061009060c05070305010c020601050907031808030415110c0d180509091507091410120b060d0501030f050c12100c050c010911100c0308010504150806040503030601180602 79
    0x1d0701c1e02c3e04190105c0d04085040c1103550300010059400d054003541c405034001001c1341603910413100e1030b9464880703410035030403108040c0c0c550000d00a60321140010806075005903502a015400029040b031a1400500880e100c10711520032000c0040341e010074440040014002d031801909040450034062402440054041e1150521600b040c00008003042070a10480d5040901038000c0d805030b040c180c00150031000180101002c0c4040090400c0d003902d0702d01c003003086805650f2103071146085420005401303000c003069010b400a000300700340c8001c85094841c0274003d5018030600d14041d1298900a801d0041c050707851407048011407008113500e0400b0031908000a022000010207042441c0155a18014407100300314551070f004c074140a00c0000c641c100069842142c0301d1110039a0344505960b45490507001400141655005114a042c07030703840289411400136069a44903030702d00046240035421101100c25410120500c030165801080042003035841d03507040e540d0182040d000a564040d2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 309421267 1250 309420017 309420029
    0x10f0605040e0a0f0303111b0607170f04110604030305211006032412171e0903030d0204180c090308070b06010e030709090c081b090717040f0605061009 67
    0x1310300312910415009901c14200c85200f0703c0b0b0b981d1240465075040480d98090140c82ca51401000c00207181e091141c40414590f403a420302003000c64640c004484076880008108a0b440c614650049205640d0f00300980700030741c4070750340c5d465a40021100b220405180b440c00b0302062510441408081da200301c041d8410307103a40e4070380060742544aa0401d61000d80c00c81522000740d1a800f000704000382c00402c01400035010f03910030000300d070825900070454480d0b0010b4030032006a10503185544500100142200746c0018100ca0426501c491448100d030300c1980917194a81007c0c4044902d03d0203400b1f80c0040c0440d90601e210b240d499600c9101040c0f081340802042135174010005245c40e03001d04bd18108806005c1c0490b113031151100d007050010050f02409640b50b0044d8103000841039400107000750950b6000042e0340041560300c0c103002420034040e101c0000e20040b0309106c07003d01c1d6201c450500c66805503180c2c8a210800d41028012203001074000c038000e1041d525075000042d00700e20b403e822102 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 309422517 1250 309421267 309421283
    0xf060605190512070f0206070810060c050a0b01060804021507020d020d080d0f0b030c121507020f01050907050a080102070f14071220030304080604151d010f0605040e0a 74
    0x1c0300d50201c4a61090b4101c01154500e60b9040c01a01c5512014a0500541607022603006880d0305106a4403e40c08481107141c500e009a0141300042c0b080d02c03021111031144d0222801100590f5070081e050300d09800260004800008010641c0b4050740100b01620040c112940f525245d600880c69a80603000060f002d01c3c085140a0100480744040702c42d40c4880c04010002100800440c01c09003442d04a203034440e20404200c3c400b2450009410002048160010200c1c1c1110904c49254058010a000113501a00e5070001c0d0a034000e02440b48201089009000105d0030041000036128094000000c1170b031040c000311000600c001c0c00003104a0b00441b484a0400f039502810b868100c094003d644504c00800c0d02c0010452a2500c00c50808410403000108014074030500d40e89010314030510f203482e4400004280410070102d01008108030100c808140d17000341045900c2c0140c9000740034000b07690344d404200502c818900c191b80150108a4003406091407100c01d039541c5c0c5a4440014011007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 309423767 1250 309422517 309422557
    0x50409020609030114071d0f1005190801050405160f030e1c050d0509031603050702030c06030708040b07140f13170a0506010812040e191d010f060605 66
    0x150762641030303406042d402002806030039000101054001802d642d1034022444030300f00100d6071008041680c014103800b82000b42c081c2c55205c200302000029030f0150003481002c0211030441c1d409003000183c810712980390100c2c42e5140606020460751300030121303800c11100d40c9541510950007454600c0364243c81c900400e601d00260f50340c5041064101c0d10b405186007032004046010f400001030444042c2d94001001a651008110340d11380c07141201c000fa100b044810f4030400030b40240701038654540003504460015135450045100c590080e00c8040c0410b00e200100400c102c0e414402a44c003030850320b0008030040500800070f1141c0900221b00b0b40303c00c0080340303900b119003401c61144020b1215510f0700400031101030240e9120702c10f41c02c0a03221401220000b003003131080007030514000e528860305103117014902840400e9029018010720720b404550000c0b202c942171140589106030b000c0341c0360018a48030103c030032821601c442e605c0c9003126042401c2008115004800d50300701d0f9407070b000320003201 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 309425017 1250 309423767 309423769
    0x30201051e0406110114070c17040b18040c090b0405060a050f070609140304050d060b0d0b04031d030f060a0213080d030203070905010302070507031202031303050d080c0304030905040902 82
    0x1110306540c00d5440d040000c5000105241d1104d981e00c4c4460402008004240b0b000107150b40c122030490390781d008240956001c070b0024035192004400681038559503401d058407501000580c0d440305481200c950f0f4000400a0641341ca44a200707090b40d50f038140007170307180e1514182e003d050141c0d20038540708860204102842c107018404551128512030000755407105c041c81c10b940245800c43c0103440c4030540c01e074002000c400010455050750b0000f00543c000b112581e640d800904000002c258000c00c0a02c4418002906501c078580a68403c1d00d6081c104a4400741c0e01b6540c004004001d403080c2d102e0580c821040c64042200d5422007500e40e000341c0c0e600e8034941018141003d0b0fa203c4500303880342c00c0c50f0701440b542c580c1c003840c054007c03562071021041c0d0783c800450603402000000750868000080410000b410030000b1503803001c5c84d0041d02d00b445040d600c0c000c60500c00381d10590365030b0403801c130601c01c043d8842c43c0d03550301404d03a0b11806d05504203a00c0040c40d8000a0140034040d41c0d640c1c8100044d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 309426267 1250 309425017 309425047
    0x403091401030f090c08060c1602040f020c0102130504110703211107060213060e061c060f080106180e150408040f15030516020d080402040b04140f090a0b0103020105 73
    0x260761141c40b0306108014945ca40301c55000581d21a05406c3d0141f680494502d01c1424103c0c1d9400c4003e00754045100e810360204401402d03c10030301c0780d401f60f08218030341f0381010a00180c605c20905c01058400a403030003040c0302c02d8070010700019820f40300810510300042d800803402417400940303030741519510321139101f518003c04c00080381d1218071101050100130804290002c1c07510861502d040840141d4484040c3c42c81d0341c5504280e03900c40e00a028246006110705103000300859a51000f040c05a940d141102070a01190400300d00b0340d4660000740451a00e0b01b5008002000e11481041a160000004d0b612903003401c8122403e06a0003001c82d060140180035207014104c81a5074078212650344c0c0e240c4540c1201d0b1208880402d0038800040c840181a035006458000c00b134020300000201c90f0022280b006e001041240c4c0704c2d40c0c4e14000c1080fa100c6101c1c40200c2c89254440807442e0804001060200e0320041040c0c109034010b000c11000252504a4a41141c0d420b00301341d915001c902810320740d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 309427517 1250 309426267 309426281
    0x230301020c0a0b1008160b070512030703020403020f0a0308030417090616050105060d050d0302090105042103120b22021b01151a0a050306010c0501091a0906040309140103 75
    0xa241c42010070b41e0040c04480c0c2049805030a0740c1d4079400c803490303443c15041d0f2078160040404540030301c000300400078110104000e1010300e02c140251840f01c4005000c84546402c10380d00080040e9020030107000f1800d00560003103035001c0807640d82c443c0d20320759503030407219101c010401810000f01504010840841da8251000c0c4580104401e803180040c004034100c1e85600d103820f07686582001d011440c03d091004502524a0b003280141542da2401c46094001c0d42c40a18851304010702040002100c5000c9504c8840d023030311651000c3c143c2005410001e0901004511580c0603e00d0004027011583c1c64a403800707008090840c0c1d45415645d111320b1a030082c014102a45001001044003144506042d40550481c00641130b5544035140c03920b000050f910700300003001e02222010444007090781d00035400380d68024014540710309080d0860390f4040c01e41f850b60b04c0c02c44a03401c80707400760686800051182580000000028000d0b4941510020242c41c194400e203000c404c80f02d044c2d03125a9201e41c210300c07 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 309428767 1250 309427517 309427537
    0x3112a04020f0c031602100804050604120c05030f0406030b011107230913030329090411100306060e060a051909080d020601080c0118031704031a060102010b010923030102 75
    0xd0701d0b0380d40d54017a40f003200000e01c3c1c101d1145003a09a0304400078080d1240c81d001d16000002420f048d0369039500d80041e0150a8070b20300601c4840c510250000350200003e00c81440004c0c003280d140c51603d50080c05441042d003e09040c4801c8801d400702050300010340c20103c0300420101d064a4500a19003080081d140381d00342e422441c00c40800805a18011240424512a550410181c2e0302401ea1160240310101ca24180146c00d103649902807805026182e0024052041545c6898500001030440000b40c0c1060000ca91508010020f003504003940040d06a0107603007541c40c0401c480030040c650321545031100402841109015583c61246180001a00a00302110030054841c44040d5951000744220100c9210b5801c2d104165481140c0c9501075480801c1c41545050459492029240101c281080c0140b01400004003050440103600214040c415130100107051000009082d41d1164180318107110a980003000001d0a0b0302016412028940014a400000e00000303406441001010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 309430017 1250 309428767 309428773
    0x1706060307053a110102070602060c04050904020418210813080c0c06040612061202090103120c05030a03050708060904210903061b091212080903070b0403112a04020f0c 74
    0x15002c028103100c103130280c52000d80890305a1070780c07403404036650003048900d4800280184010801d904054020b6900a41700810101d120380006804070300c8601c807120295221003090713000091014410f1881030319103100d4035142d01d443c60700b2415030f48038012808000740903520015050a0481c030500c441c0182c0318004082503544c5036241001414081c0ca400c48c007800c14940700c6c00150300c042010a10015070f601518a00c0c5503840e40e100d075481100450742c100709110001d00c2610000703e00307000909031012541c40c0001c2e1803d1001000b81000d500800050142c04004280f00105104041e90201c510f00c15458102e4038000d00811104000c15500080c84c036410038030814030545408002c0480011155a81020566100c040c030111000d01d04d005800c03281079a1501c00d58034030498141c0c0c4c2c0649000c0885c3d140c4641c2d5560a41c407440200c0e81074000400704004020a910240304041012410101545c0711048590101104400e00c4c840e00f417107a1342c001a6491400d0f410b00540f142e4000050603 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 309431267 1250 309430017 309430129
    0x509011106040b0a060503010209030a080703020316060f241406090d2d12080403030e1005010602191703130506070201020c150103080a031a0a170606030705 69
    0xc40001c0f00c00541d000380c8501c0c100768001c140c5007014030030303110b11580040050401000ca42c4540c08643d008420a41c02c50008022a034161107142800148582c8100740000b040c20100902804a49007003200714400038001041c031440b100c04100e11019262401142c4000512500002c1c4407031240c1842c0d10381259080002d4002e1218000605900308401540d03003200102002642100da01d01020003098031125080440c54175106412040d80144242400150310b40c1c1143d1043c0381000342d1203079940c502d494030300600c00240c3c140b203050940713000f50480154440707655a4081825040c0c42c1c0c00c00d14410080001000b540451001c5481207130480d0a80740107060208000b07000c5d40c44a0304c034500071701c030724101c01000e8107442607894100c0350400021400d2480c403c074102e001d00080c0c0d01302140071a501d07180750340c140d8a810070000200b070b0700c0c5141210a46c0200c0f00c2424040028503c40c0309422600d410041c944640d0f80034000400f00107811000b2920b121103040c070b101003d0704011007100400403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 309432517 1250 309431267 309431273
    0x201051909051c1a0130060608060406060b090d080c0c04021201030b0f0103080d0509010f1b0909060509041e050a03090e0a0b280b0a0c0209070206090d050901110604 73
    0x28103183c1c0750b4000d035101c94028482400344600e003032080c4a0502c1003a402c0348a00309009840d00890950401c0ba00700000d00c400c0340d02c59100350b98485e042050590419400d1104018551154100030400d10011034140814900005c06122800801400f6840b00040c0351200031000d01c8101c00002d8000c1c4115240c0525845003201c0000034082241c480790314402080e060100580c050341220390100c5420724180e00508140007404002e4034441c00d07076483c1c003611054850280242070710905440c00c581002146d081c8010f000b60f105900030b6820342e1500030300f07000340d8640002555000c1e40060b16010032200034038100240703044043c80a40036000e03c400030020180e0150500b030440d1600d21b409040c40d1202030801040354500c0f500c1c0c42d84110314030f03410280b8510003032800710036900580403100f071166114080304065001c0009680007c111070060802c600e8203031031050700008a4801050507180141c3c0040e03844440540e440e041c005c01207441c803001d070302c1150018030704025442910b0b45410586 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 309433767 1250 309432517 309432559
    0xe03070602070803041203020702030601510306080a021504090507030218040b0907140409050c0301051009060e0108040c12030c0b01051e09150306040c091107020105190905 76
    0xa28100d500400c421030041d0000d07c640240e5051540040c06410f4991800ca000407a503000d0300c4180c107051804482030040310850000004100603181c0d8850020368104401151811003003807800c0c241032500b44103101012000881d004d100f581920303a88a15014149020064010340d0b0051000324140010440b030198150003820861200003a00c03000c5d40c2d01901003009030f80c02c4200c0d403030700800701c6070010318a03500c60050b10044070b8407406854601911220007034144e8a00301c3e500c88211100000401c25400c02030803080c402402490400c6000e130500000415076000b1907a200e04110181c8045020302002c401030f070000b800e454041901e02801460080c1c8a21000b107015030300a028000001442d0506042404000101480c1c607080440c41c0010004800d0000d40001440d840c0321100215036141000079602071401103c0f9103411a1a04840106484280e40700e40b84100d001d201900c0181d0300031041d902e0300c88880001b813411040c47c4008031901c070015400960302401424a400640d00e102c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 309435017 1250 309433767 309433771
    0x6080d1211090d031e080906070309060b041805060903250302010b04090609110a05030d032403050a06110f0403031d032d010603052508120a02060a0905100e03070602070803 76
    0xd2010016005c0c0300392416200301500321032500c0241c0000740001d1050f40f090b0301001036540715400014442103001c4c0850300b101d602164514148181c150008188442086002d83c030200550045160100f01c20010f81741c0c44a02c4481c0003030301741d01e02d00041094001e4003c0d00f81a0070191040043c12054242840580a0000d041c2c4024007a400490070307a09002c224841980e4010b002807115030034400c400c900070040803404078804501d4a2180300024114046580114003c0000b0002458141080b10484240d1a07159050800c100460040c00c101c2100303440c101ca17018242032031020103140f500d503002d140d001d0b0001e41c140101c18011920401c0060040046c1440024012000320001225801c0701c0301404082d02c03980c001020500310200c0001502d60840052a108000c90743e104003003458111443c0c1d02c078825000105501a00079410030032590700005c0c9040900000c00207444481d02d5004000e8030034080354684000e420404010000c036004154004401c43d40d9500505191040f6041 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 309436267 1250 309435017 309435047
    0xc061809041515140a050a060c061b02031903020703170a020d1e1a060313080d0e010f390203090d08040305070501210b01110d1206080d1211090d03 65
    0x13502c08040b0300304030400d1400d40f40d0103015001901e007000800e40b1803030f4002c00c04031102d984994103050544001c0700100c9141e9a1034000716219042040b588503210f2014481c00101407048c044800800d030b1000e580d90035001d00c5600328810f07840c0c1c001d13100043c0c40f406070840038150801107981c5d1400420f050351501041100001c006130005040c800d10300c135a150603401d034008000d002090040c5000c0c010220068851000e4503e40702680103441c2c140d94008505d2180da9540f01003040314030805000388a1b190840c081d00342140303d0350030015004241003407885a618046001707003446450080007111000903005010302130104091800f115180c3c42800212510b0007030300c0380010154090070b49410705055410500a2548010350520024188042d030541006046004c044c41d00708107000e04000c0707680d6a541c084c1108040c1880905444140e4420095a031200e900036200950150100e0006d0038500c1011403400c000d240e007082c7e240900140d0540c8240d107220080101608405102c3c0c1202c2c1d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 309437517 1250 309436267 309436289
    0x1120812131203061d0901060e0703020301260604060c09120809100215010b07030207030605040b100b042319181515050d060b0d0903020c061809041515 67
    0x1d5680c0103c2c15100755101d18241c00d00d0310803c4516088031606120340c4803036000000100107a0300d0416011030746082c1c80440c04654000010301604007081d8401018200c020314180f444542c5002195a401c0b00a1020700819502e03402e450340d0f14800d041d0b520003005035030425210071140b41030000459200142d42882031000303500031034400740007141d0110405c61900240045078600200300740f15030301c0010200c0450050b8035000c80003c03201c0c41002c1c0030750300446901074146004003d011203140350350800d44001500744010403c0500c00e00c4542d410100c000b506032184c0d214000440c0400303205007084002e00040326070110306882d5000300400c4001980506111407071506050080c07540050062204c91100707000702a19143c0520000c0a80040041d00010103d44d10071040590350050408041e0480e2100600018998104031000790341004a0315507140002c880c0000000303103440400c45026148543c00070b0180403411404580714452074074288045850458021480b880d140520300d0000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 309438767 1250 309437517 309437543
    0x8010209091e2205060a090213090203030f07061e0203161e0f020c03060403110c06030114090c0c0d05040e0906100311030a051204090b010c0b0112081213 68
    0x1400441c4491145210301ca641e2103c014042c0c00c010046030786460070361103029060003c0e03420000b0500c101800c0300c00164900c0c6601c1000804103a082816500508001c51b4402694012007140d000200c11030076150b95402a290050291003140483d10404258092000740414070f40c000310b1103001484200c080e038050f115401d0703070a105410100300842050000030790b506030103601d0598545141d0f0040754005400a800a403a04100311821400140b48020103664100100440c5000e00402c0b590107003103604080c50042d955480c412918172840c00d50000c00c425408a05c2103890000b50b0009a611410380b405001c0c282ea44640710310688281400f001640d4030b0408510980100018500400e01528544501b002901c00c42c072090b0340b6010b40d0500748000b13501000500e101000342c000b01c5072100c0c5828020411036000f9040340f13042c000007541d0100010307601034007035054580c44c2d1485160032840b814061482d0064428096400003124240710340074884241140a0724031580b10362500d1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 309440017 1250 309438767 309438781
    0x715060e010f030f060f0504050705011409030303060d06060312080105030c010c02030c090709181413020a0902160204020f13090c0906031d1c030606050f090f1503010801020909 78
    0x480c00c00d00ca540c92404000304140001581040c0a80e00140140000314480048051120444805907800c407140d41c040401008117582060b48a1201320345010010300b0720220780c020940302d00c402402e05100d01d1050504801300001940701c48059904141d1240c110040c80c0d80160040c0020301841d8401c1c410b800d401040c56100752500802d07140e003c0c026141141c2840300384005000c000c2c1840041c400003200c08a41c517210600a02400f20042a011620030916040c291151074054801c001011014038080301607204c2801c408101d507074403003006a8038000805101c0000c1c0002800a6000717000241030b58010901002404031135403c0c0d0035a40c842c40d0303140310200031101411200004034000d4001040001e00a6001c0c412240c4508000c0803038074210300c0700a003041c10070810b481c1d100782440865041940d0502c01c010103420603050441c0b90508501c03812089008520440d8400d61400d0491043c5032030b1032604080100500b40c446071207584540718a8041e40000140300d018500c054001216 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 309441267 1250 309440017 309440039
    0x1905070c351b0405042d1e0305070b1005060f04080105161d010c050a05010c08130302060109110c070b0315090f0105010302090d0f030f1e09060516050102071506 71
    0x34100002c1400740c0411690148806001d00030003d0b5009090926002200b100100070b00e500017601e5011800c0d00c54162400c048406071104040d00704c0c030922004403001079000001c5584964000905c2d039260303a10410412050700d144d400c80e682181000c01c10a5109801308003400954083e20024015580c514001e42c4510501c190041d00140078100c003205040c500d15403120f0285018500040740e210b450b02c0e80e030724001002004a0b0180c3d0b4a000003020030394450300c83c50b013003400180341c40010070003070b10001c0d41d448041c0140300d04182d41d420001045101d1b001140d0b1481a8a2305442c1d420b59112009819130304200c5902d06000c0e01d08418045034640405520f2080001c1c1188034070a90901e40110000c0d00700403012a000814801d41c8000b058011441c0240c071031103582c0344660b129003101c005000f05110b280205244420060b1041d0068002c036400003030b02d141d483d250f0344540f09a61081c05498006002600f95440080ca000500480e0041100849845501071005995419120366 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 309442517 1250 309441267 309441283
    0x6050108031c0b030c0411070203070b03070f18080a03021c05090d08090303040302060318070e04080a030902031006030809040c020d0c030309060b0a08010e060a021905070c35 77
    0x2c0421020b02185055070204212002c050700b20742d1480940408101207e40e054491207401c080460680d04601e401c01c0314101921044011500314100104007600c0001107000030000d200035101c04150102030b4980380001448140110341102405040180d1508660a2010448101c151010103024000c0d800c642c540c0c18090000345125585858041c03054101540d81941800f04110001c050307907070740010394010a0002160002111012001440c101d016441010500c0d1140200400b0503041004e5641c1300d0500d08004c5000350f0140700007070401c4040c44080030110318001c03000c428440c042d00940304100c0305171020043c203900450140d1f5910396200c1180005500a401c030400244250802c02c0e8540c442d031000f0039910380c01800a61080459040603070703269511040b1805420040014640028032103a04518103140003218480c0600301003840360a000b0005420740c10000081c8108005000303001c1c003601c000380a1040002440c1030319448905901d05005180096280800d5140d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 309443767 1250 309442517 309442537
    0x50a05060f121606020f060703060e01050409021201021801090e2505070c0b1213050c0f01020309030303040b250203040521060c0d0612080301052b050a0605010803 72
    0x1a40e410310038000c100180e190800d02d00d020307001d1840e0114a0241035070941c40a01016005000601345990000f481d180d4020408420103050007803c110306a91589420f054440695001c00e15038003c2c00482e00c4403200f0f4640400715840001e960b02082c20303c5070142040c120036a50b01d0b01a59540b0310b100941c90043d00c4c1c2c402c25140d200d0040180960783d0445c09000800c5091050030072030640c6400800c000541d100e4591004009606810001030a0300241c0c41103078010590400740003911400ea0b80c2c4103501a4500940300141131140f80c0e03000f0001e4a8500500404a031307540d00d42803502c200540ba05540c0e1b19082ca644c0140900084d6007564000a00ba2036030b401141060324003010016410141c034000c10301d074901c5207131481c981d810500245c0e21600207034802c030b42c0d200509002c001c01c83d00c00f603022104401c894032440c8002004501105e0440c0c100701d0b012043d40441c00c5024010b4000d5402d40e2030084580d00803d0304000c0e000c203c822845d4000c40c81002140c2c4c0c0c54803e15181d00c241610302d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 309445017 1250 309443767 309443779
    0x3020c01110424020f0a080d0b030d020c010e0d02041b0e0603040803040b040804151e0e011707090b031015030c0c030f0306090e0c030c0d0b010311042d050a0506 71
    0xc61038100c0440c0f20b100d40d1016104498400c5003103103003941080f0a0304000d4851000010f40440e0303004560049420a990580c010414003400d00340003034490006240d50b50420000040c4001c042d07903803100500c1c1460b0010070030840d511014202080c00610820704038040780126064020a241440c1a41c3c45180c022002500c0d6030750341d0343d5110a00344014411030310050140400300380342c80315182c095241e880d107031148000310780002911585064503422000030004010078a0070700341d03407040103c0c0130f07810210502c031603d4a54520075100c0c0c42c0c0301e8100c0d518651001c000c100e01085107039007640407240d195110340c0031946241c80c12815112014405008948a03003000c1000a100f0407001240c10000c0c503000580030340b00c1c0d4440056030134482105081e079102a044401b07901d014406489210f40449a03103400900ca0350310040324100511000c0e01020144400b202c050711290084460780c900c81800b0f20804c0746011184611000041d55010514580b000040b52881769115207409070a0043c12 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 309446267 1250 309445017 309445049
    0x305040e040602161103070e01050a1710020c070311060301050a29040807050a15080f100b16060e0105090709021b010507020a03020d0807200c09010603020c011104 72
    0x66202080006042282c1c401d608004120700d28001071071460820344074141003102203200c0010189002500d4005410031041c2200400007a81c618440404440c41020303040b0075402c200ea0f80c81d003405103401c80d600709603000244c5980b00000116458081d00d2142a400c0b41e08440101406001c0c0000d010705504502d025509000b620a0001d0003009130442c44a400320742032942c10600e0b19a0019449980c50390b20a00040c0254908007100c0320243c62443c51004901c41c020000528492000e00100c00401d401000f20391000c4880c021032028118074426181e4484c2c804083e0242001602016140a4a403c8201e401000e040c040c480c0900c501c1030092100380e00b00b4034100c0c003d5008008481c2410316902e802c01400c1c00a0003028803030700454020701074a091605000e41002015001c9004104d082020006055005980080c00490b40d00003030034070740d0411028615203080d08641d2580040c17203000006030150306030002e10070300e4038100090044802003015605240954040e90081500308a8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 309447517 1250 309446267 309446279
    0xe01090e0c011223060111030705250b030403120e01090b0115170a0203010302010f02210f0f0310150c02060906071a090105040308060a050f010c0809041d06010909030504 75
    0x82c54003e0b14001c1c80000914400603402140b03090312050940840b030300d060003002460340c0c200e400d1510415840c80a18500074259541588900075442aa1581208100d0882034442c03000c000030007038a9418801a503074102401c0282c209030451050f407800031f007400c04480c0403c4c4180101e0190365400b000402081c0d0900f40c14600d402e455a51480811140e081c10700321074400300c019680103103e800e000503503a50550000404030310801035444290340c45480426038004601d1849440601c000300d040c0e45a158403511103106208006101d100c1000100c20300c041488003600c04000c4038001074010342c0f000344050085e501c3e034444101c083e6111400780114003a03800c0140041120b10322950006210342e4500780310719424038051303c1e2030003a45c0d90b9000700810550000c03c00354000c941101d410b034a561038080081e1000520b04c0c88503041140300001c0404100e280002d81d2403c0c0c400400900845002090b11001d42e140305410500c64800e1600005410200f0311035824900d805940e0035150504082c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 309448767 1250 309447517 309447527
    0x9100e01021617010f02041206050423010e07050a0f05010c0f06141b0405060a030209031e0c01030f2c121614060105060d0e010605060f03010e01090e0c01 68
    0x640060550080b0945020682c1036902c004024200c2c50240b0101400007210349801c48540d2078010703010340e104110070700881c440c802c18040ba566020700040782e5541c0f2403411000d40007d491074072001078160b41030f02d5089081900a041000c10100484000c542d0f14810002d240d262071190006100c4241c90038009540704100c0c154070765002e16411070050b402036071101c0407645c45062030714134078400e041440240e003003509040c420100c0ea40101030615090100040a1f44218444c41d4140356001400191644044c06000000130710782019000d40045000429240c8107806d04040c0003a26084d00c03000c008105104998284050966459001310042007200c3d181e40d111860400034070558810416801c038600c000c00568948200c1464031000714a888151002c5a03026066a07070003c4005000548690041da5103052600401150012030500c0319801898960070180d00007000003001d8015240d04c80007141210b05070303c0e54010681e6203203819812202d0b0703a181441e10b070304401c82c2d200040d8411 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 309450017 1250 309448767 309448787
    0x31a010c051203010605040e07020c1815030a030906030b0102030c0706180f09060609080309030a03030f06050a08010b0108070f0804080307120203041208070306140d080c0d08040b07050910 83
    0x1403000ca420020311101d02c603080350401d07408400058000034003808980070721001183c100c5014001865001491000111005040c118042001000400145881a0040d40c2031100318010f07044d81c20003078540c00c005014482900800f004241010003100c0154400000c544807030980350060040f080c28035404480425030309180070302200648001107880e00740e0300c0c500c10080c0480140090702d10b14001d0058494865a48002210780041c010180e840c0c40100308016101d40c0b510b80040d9100c2c1100550f402020950030864105120010100392040158060706000e8800d0722440826503900208542e50b00301c1c06200c03000a8113400100c0c000841a00245400c80300c141410051702e01c80c8203410040b80c02c200d0341945c5010b40d801c1c00301e04094004442e40d81050740741ca07041c0b0a513400d00303a003445400c0c2103544140c0200c00550400302406010b205a8a20b41321200503540721881d0103400030100141940e0a41c0c004a40c85c000c2002c01e8005c200301e0b004420050003000c50030400d81c41c10707100c101003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 309451267 1250 309450017 309450023
    0x515010e03120f13090e0c04020a08130204020f0403032303100b0730090b0a020a15060e040b01080c032b0c021c050105060604050d0f051006030b070f031a010c 70
    0x205001c8960301e12030905001d0081c0c55141d5002804202280b240e900d0f1210814103030703002301c1c41081540b102d540d0080b44e1a91003284000820024001840400c000784620010124058008580030003050fa0040c407200c004241d0344a4490b01e214205d454010ba444181c4540400c000d8460040040b00b200ba009401074901800d92039100c3e14034402c980080e0001044e107004c07200075140c0700c0e40580b03400982c0300019104007030030b0b2810315005480c00396035003406071005880c4105003541d0008603106034000101401c0e01e0a07051125003821703e0013602044083c001e200c15400340201e0583c240c00c0000e4040c118000d90841c40030b076281e1200302095083c8480e5551410014650940340158841c100c50303021038a03e0585040b00c410080c2016030071031304081c04292141d8420082007026503203802a00001640101a0894964251611514040d00da44442414038101040001802a080b0b2084c1c440c0390161504603009031034040c1181120000002c05485003200e9400040551007041e244840c544 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 309452517 1250 309451267 309451297
    0x70e07091203030e1905123108070e0c0301141f050a0f1b021002101503120201050f010308030a090609140127060213030609060515010e0312 62
    0x1807591290020440c0c0380e0300980129481c0d4011000c504000c0042e400407050182d03800480c00ba041d950740c1d03151140400121401c00c3d000c95114199000e40712482200030008045000010148880c0c2c505010750f84a049081d02542c0400668201801d00e40c3e441500500b4059103140e003050040b05034400160852508201040903030242e854444209454100040d11000d03100c0c0e500c4040105400c804194140800681a4034815400f400f41c29002040380e0485114a0481c0040300403850034000308810344449050001d1031403020740d2224454140e03402040040c0d1f012210080030790903610240c50b0450554450340040020030511009140c03c4a005c4102003680302281d107810040d18940d6038196501d5881d11080c0510700400d11031840e2425288000101c5c41c4500500d01c80b000c40783d9075018150360b40029070404030022800020028581c4a50100306209182c24040300030a03007140e01c10381c0c45140d105100003a44c01110480010312004000340b020100f0341840000c0382e00028001c4450f00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 309453767 1250 309452517 309452519
    0x1e0609040b1b160501050a0605030a020a090c11060c0c010c05030108060a0e07080d0503100918030c0c05100c030212030907060c0206131d0a020a0c11181603051503070e0709 76
    0x26840d00b510003e034052400403500e42486803c000464a442c0d2110b03210b81e105e1814000161510300d040c40454404c0c19000400c00e0102400352600c0e0310080c00048a40035150400041e108880e001e480e1080d40c4500030400d2518071070003a926071200b0702861025034084070000d03050641c03540040c0070700445541510301d00c036640c0c03c203145002c1030301405002042c1c0120030070104202440400c03005000c010002d2100d2880844810600003428102404012610101c0c01c1403111980804004100103880c510b003030b03801070a00600e14100004110018015407114107a48010807095034010391020000e0700c0a00c0c03800700280e60550f0083c1c1c00b240c00070018012010704401c0e400100c4001c00f8006c5041000d9241c1c2480b02c1c82d50b55005188203c4c60b4070601c4000d800c1a881210902c2803035100c06aa03204e41c0b15840003454000349281c0e03180f035250148080000d0203903c0700c1ca01b241c4c4007164800740038a8a92001465210304600c1e400c54056000d184c5c100414204114010b82100640c11f1418001d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 309455017 1250 309453767 309453787
    0x8010512070b0a0c031b0f0305030c04050915031c050a0302180a0308190f05091e04050a0b0a050901030812130602070b10140a0b211e0609040b1b 64
    0x903002203901e400804d500030f0303808081c181c11001c11241c00c101c41e184000c914506907100d00380140a02d00240401c000400055070b9120840b0846000d40002406005d1900d042e0000b0890007041180040c004e00444035041501021015400401015a10781030700b050f000310710880c001d400171010048118407201c3d14111507181c05003440082c6001d6440b0590343c000624410340d840008144010030040d10f103130ba50041540c40401d494403a0f208407940c0d62502894101858422a4844043e034880e16110078009090401d9000c2c91003900c0603201c12002c503564000300070300b103103092002422401c410042140030801280c0901c0d8003940301d903117454481d80c56071610401c0341c1001e0002c44401055005004a59200790740507001880103802d03940c01e017240c18002c90724000080c81004c6800c90041110800031b590b4a0030900814906003552105140c42c0c41002c0e844401c0850105a161040d000309021341005522644183e820090080c1346441d012861502101d00c5501700310004414030100340c40c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 309456267 1250 309455017 309455039
    0xf01090e09010f24240e010311030a050f1302030a080c01090b0712051627120b0604060e090607180e010e07080709121e02040203070c170405010801051207 68
    0x4d04d07507882500b9a01d80501030740006003400c0640010040381011041900031105050400c5681829807928081441c80030f00180c0c05091440710100340d596021042040e4000740c0e90141f0700c05c1e91070002ca098039440d100c44041c0050249640a0f416420901c2d400010400f0300b4010b040030480700c00001002046c1d41c6030031003024010f03500c0c800003440c0d1035450440500240181a006502d100210f010b0f05e44003c409003041c0440c0c06182e50341000d1406038000c1c0920b16684500600300809001200001403501140310202225407034405c0d460440c000c9503060f04030712340c2482000700c0002040035131540d000c1a40c110301103900304d0400c8040020003041c080d940700401b034000c10140200941c01d04107400003800b0100010b0600c8200500008208680320240100326030745500401c102000840c201071401e100c072544e80b40a50018000014002c005500200000090340154a074903e500000c0800d00c10710300c01d601c591800905298018055850408034040d000300c040401c54900701e6031481c0e8240d03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 309457517 1250 309456267 309456281
    0x506100815010503040503091f0215060904020d05070e1611010b0904020d240504060506030604050318150a081b04180203060402070c0303030615020312010e040203030708070c03110f01090e09010f 86
    0x3244000d21000c0041b4681c0402500258070010f07442f8403118503200c40443c001180050011f0f03c10100d4103a284184042407207030701b0162001d090038120501d080311400342031078904040303000040d12001200004002c188580010f0000081041c52281c039a40c007000310604d80d20200382c691040d214010322407201d0810074050000341c2d40102051525083c20103004581c00289070501a130481c004100000d01c01104850000e03180d01102841041102c020505003040046030405034100060782c01d0780b032a0411843d91140300200b0381100c05580b000c000003903a01451080d034241c100300401e0b401c102034898001c1d60703209a010b00010705088590725064044000e940c02a07020903951074003071062015003020300100d049c1c60700046281650b0786c054403100080501c15401700031034140102c0e0441d42e09200b01d450712078010301440e49410300d41c10040c90f034903424402180c12012510f10f0031202c2c20000c80c0c3d404088016181c2e45a11454410704110030b20000300307007540c25540c42c148040c00305000d10680d9 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 309458767 1250 309457517 309457549
    0x15010e06040e010e011802190305070309080d0207140a0c090b220b0a051017070507020d0606060909271103030403050a1109010305071415030a050610081501050304050309 75
    0x4107130395140c072982622482c205c03011a00020700400002011001e90440f40900b0245413800007095502d01c5012001031540010080000034002a01d22503400c2640192031000e000d0000e510380d06006903000c81d510f403514070700201814040601000360106603442401d04410141002e01c0b4008051580090a41c0440715030400598541c803a0000e42440360440b070140100342c2e0207a00301010003002030000e413940d0400d642088803142c002501d06206909940c0d11550262a5849480d1075107886c402509060203104e0000340305110005001c070090241121402040a80c1c10010219407010700f1b503106054030035681d403103411015003080d840070401032004501400c050501080c06142c80c3d003803c1c411600d8030388250001d0380180017090000c95031008464443c107002e0300701c2c0711103000b18203a2702c010700c07416410081c04400c02001603056040030348140b0701150951303007140f81c8210545502c03100f0f42c0c002052611070303015500c140d40070300025a08940500300300d07418200e01d90005264403000030021 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 309460017 1250 309458767 309458789
    0x61914040f03030b060a050d020c0102160f06051308180a08031902070b0301050a0b0703020115030f0506090a120f0905060f07020114031b0901110a0305190815010e06040e01 76
    0x90380030b040d032601c5100d5120700c04481e12880e0030001400202a4003e500044000607030014680010b64425070407200c0240c50300c1044041c8960791706210510790824001a100d65082c0400a000801d02d9145900040d81c01031440c0c1c10802c4100e206c1c2d07842900c0143d481d403c02e07407100011079a40300030800342c4050302004180c00311a22401c64000c5c1000401e512070810040240014002640c0d04600b20b0300b52a200141c00341c840d0007608040340509185a408403012001d244040f0030700261003c41401e8500907012036466442e00003c15030f6030b07054018041c140c1105446c040c6403880c07285010450342d00c51407501403034a9842d0000a1899403080c07980803075843c0000744007421541c000c100843d90b00840b00c0e2181c02c51910f04803001622043c4c03c407000b010000080c509034168003030500c900705902c2c808125410b1402c589406070950381701d02c4110b400d1030020040300802600c1026181c0c82000d1010040403400c1c0340305e00540c4c1c00e04024012560100c014080400d941c1e031310021007030003004000c0308 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 309461267 1250 309460017 309460043
    0x1d07081b120f1c08061005162916021b060c0102040b091507121407080c1b040204030302152701050114010c0f1403042102120f06191404 60
    0xc1c03031615140c440c43e05050024400400c86190740e282599058168142407260780c0303001c4299a01386c0101c00c1800100103da20700a2900000c001001c08504048651038400260315142600004c208400d0030324001680490b1305400f01d98030340502c4401101d40942410306120b41d422005082e60403035007100b961044c000c0f80d10700b01803a18548070f00c4168004510b80340b526a154132041000d40c4ca840081c003e0201514298603580c0401c001c80700c41303075049140c4689501c550942207072514051405111202d0400080a09914291003100c0459900d81c0003402244a900803207024141c0c018040804189207401250b00422103211920701d0b00c2c0c0c280000030740b542c14000d502190909441145040024407400704001413249901c24000c00e420000e208081e29540c461a450352040e41c0201c903160b08109140c03610f000b40100a008840e1085800144007000e0f008441c1c1e40300b240d41425521544201c0128010072040100328907030800e214000308810184014103044032505480c1111694032441c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 309462517 1250 309461267 309461293
    0x50309030a0f11010e030304060302090f0a12020a05150d110c030301030b04120215010905090a0c0b041d07350708010e07020d050316211d07081b120f 66
    0x643c10107404001d00309282600c6108011960f0703402103005d0305061680c0011802019a112030020400304001052030b665980c03030790300da41c0d050081c4441c201d00800c81050040791501d44289445800c0c1135014140c4c4c107041242220001030960510760300c0305600204000ca086a00501c0110302840c0202074064850815160481c40c01071842c000c8421500b005440142ca400300580e8941101c04950001c9800d441d18841641000303a1a08028030a2101c408001422744c40900500100c0300c0d500b13800d881c0700d51030401104080d60100d80d4040020780007401c000e00042507048441d000d52000c000030780e6a4040204400c40c0700d034180e400d0300105803940c0c010000481c20100d80c03540300810f8400390104046010001d0704034000500f01a4032401100d010f42e84180c4511070300e00429070080400700c540220910703e03a00800b190010207029007034011a25010741c0d0009081d03000c580c440d81c0180482e1444080e00d54414441c21016030384020800b100c5000d03004204060182c0310881000f405089c501c8003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 309463767 1250 309462517 309462533
    0x60510051e360a030605070e130605010e06090a0e070c050a0812061c0308070225050a05100806150d05190e0a030e3003070501051e04020409050309030a0f 68
    0x41c41100c001800e80c040001585410120030300712541720001042e15107e1a000380d80101d02425043e0704205030000d26020444242c201c0001c0b244280c0710039808417400e40a000042c4250224a60000c40c6100200121014095910b41c42704051416034980070031032791603e0400303002d01e800307407000c24000c501d010655440c8a0b105811840c110789100300000307010380c160002c41c15060003a0511043d0700000306507034001c0c0f2210f4480d40c03087c0c13840600c4030300d4003500700c0800e02540205402205440301c0070070700303080c0301c0d07881401c1c042a0344500c0c03402d60f80e607800c0091018240140e407024180a0080700203404003401240d000d42d00001e080301071a0340300a43c81c030448000c10340d0200ca0f640091281d9001c00d4000000600d20b1000f40c40c03c4507074120b404864a100101c08220600f40010340c80340101103500840901007140c4100000d00040d1144512468509a005a80001d82060002203001407a003640300c10181407080c3c007603a042001580001c1e04105da44602610366142d0111300c401040b50b44 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 309465017 1250 309463767 309463837
    0x80706022a15150a060908070603200d0603020a060210050f010b0d050a0603020d0b010e070512010b0d0f021303051204080c10020a02131e060510051e 66
    0x1800d0011140c00c04401d00070390b202c40d24120400c11602c03100c0072506030544481488018500036202d02c0e420359a65200030001c01c00d41c407418466001e40c08010500520900820140c0c0c1c0c540c07804c100d5060900b8059211650041008210041c0d403120300200585072401c0800c0204075039000790207411341c9a6180400d88200420442080164000510851003030707004bc0c44a0025400001074290717a10481c2c8401003040750400382d84110034074507003001c015085941c981612038507888042d640d12080d04c16101400780344010703000d0400c0000103110701080f0801506000340111008078031080d030550488c0c104da000b0558024006c0c1100c4040c02480000c0001110000644004610f407078980046691540e0301c01d543c0070310030411800310301e0ac028402c200201101e0307001403440c4401841d026181c4003c060368820000c6207c05405000b00345005840703003208442e4040c010b04440a02218200d44540c0307c0c404151003801500001156000070002620345000340380f0990300a64003020b140c070007900768 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 309466267 1250 309465017 309465067
    0x30b0916030c26070803031801060609050d1b080c0f0d0203060402220e010c08010608090a02060307050c06090304030611030408090d02060f2a0d050712030908070602 73
    0x500002000018145403001c030480d03007014891009070445030b14054203114100c4100038148554113003c1803058020009501510040ea0103d05507070009100c94281c40340c52180c80301185460070100b01c41d050040c004040c00748294507202c480c01200100c1da04a200d990480c1c10f15078424680700c1c0060030480490b1049000c01c0b15030b11810030503076002a540b040c00400084c011684000c3c649466a040500001d212030041c0c020301030703502c8990210703000344181500c0c1c40004506030000100140280486401000d500c0040c04a00c041034092203403e510181040d410008100820039040c001031266600804001004c0d40c0c3d07503880d50030b08000382c610b8115100542c036010400d200000c3c001c0402c40c3d0107031105543e50034203455140001459030041440c581070b40f003400640e185103603420100d001411184480c1082c012400940040d0b641d0800700d007003002151041110401245c0c111450645004483c540403800a000da0b481d440e00e03410140c4102c0c1c0307042d00443d140c090f03054505440290005 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 309467517 1250 309466267 309466303
    0x6020a1e03020c06010909050a0803040317100b03040b06270414030c07032a09050f07050c0309370305060c07020d0f021504170c10080708090a0c030b09 67
    0xf5803c07000b107449140c1881a903401d0b60380d51861008002062051485164000d040d40d0303100d143c503050141040040301030a908940c51030b4002403a1000b80c402c1003007031344c1000c2040ea0850f45c4c0e660702c201d0b45000203404030354441d94440944180e140e03141004119002103038038400040c2440c0c0303010540d03407034105003818044d00288090005454001050011a174100481d400000c080703440201c0214408082c40300c881c0210310f80412040c0d40c43d08000d00652f080c600b41412a5202e00040300d59000e41242040b42e5042009500d1541ca08200000740a410403800da042c0400003504580d003100601c024003548401c5010104140b03c02804000c4c0d100c4031741c14406203000120b03030015424a22500340203082021468000c0d043d900c52080c42d890350a00d018500343d50399220040f2000340d00312030000220764880c03025460210705282c800005100007030b490707040340d54031400415100034100400c2c14a09100d05111140410040002400150300445c10030404e030078240b110900345403c813000400384103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 309468767 1250 309467517 309467527
    0xc1509030c1908030315010e030703020102101a2115040305040b03040816080910090b3406060303090617071404030c0b0309070e280906020a1e0302 65
    0x918046242120a0011200d02d0104101007a4940c2040899009845948004020000807002031900b5180090b001d88403c1749003800d5208041d034500c11400002d00603006500c0c4a43e01c0301158004950340d43c0c80c80d04900f450706106000c038030300b05481c0c642e5500d107192204501022135400d1010300b1801e0207503070802403a4a0a030300c0c00740c0107115610901000980000000b428020340c8d00950b1150310350f80002d11522141c0b8102141c0b2600b014590070b12903072403900500304040c0501d03441c2e0200c03503d120185040c02d21032854400d941907011560002e0030784a94082e81c1c47d225620f00340c20380718030414001410b2821403e005041c0308480d00040203208540f220542503142109185038040b0f01498803c0410008840076445130040758130040c1000b410080c003290000505000c1e620400c00401100e03480780d510641c0c2070500c181500c02c408001d030381e074107403003510b602460784410341d082051004a03c0302d20399500c0400302d0f4030507900c1900040c1d82c95100c000d043c00340040b040d2040894a0298142 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 309470017 1250 309468767 309468769
    0x105060a0c03080c190c030207080114011a0903070b04091104030201020c120106050a060305090c03030702060406080a06031a10060212120405151f06091a070309090c020c1509 77
    0x9088a0030150074042c3c2140010981d002140480c0c14064036514401c04866a000025089565a940c12805401001c401081c00d00d070521034803100301107841210035a6483c1c052040824040400c0036604190700708000c2c2002d4904020080003411201c1030f40c0d030b5a900e4040a20300301c50703001c44038262004040204002613170740003599421030303c81159030701640007070480e142c0c0c0188410b0f40100d40140c0e01c44e20016906805a1007107100780d00c41c405540250400c00d04240c3c403407103240402540800c05100501c012480790030040d074815802e070000140349450381c485e058402e420340603c4805031451810068261802415078000b40a42d0000342080102c1c400d07450030364056080c80501441010001a00b4054200540032400c0100345801d40a418600058042e015100400c0350100c0065080001c016118003020320480d00c1403d4000d03a0800207480e814050f5102220540421071513600204110340c00740700d44070701001c068004001044c2590140300d1800c0b05400000c0310321074140107200d05 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 309471267 1250 309470017 309470027
    0x909010303031a030d03150807080a15020412060605040b010206071d0d0b09010b01021905030708090301020d15080d0c050d05090303120a05101e050103020f12040b010302090105060a 80
    0x540c0d40c54103002c6a0580712949100c070340103a42c00b48903854401c52440304d00c0e540d05036020400d4807801c0303401400d080b80c483c110300f42c0e628441c1c841c5030321580c000704800012030200c0300003040f82101c0410141c98955140351703014448803141000e44000340d684008000501e01449141c41c119020b00142006107413512010703105000c080b900c030410450404001049544503070a544e89a40d1104070115141003d5103454001c0181603140c0d40548a6030340380c95840320a48500b405c0301907200004602d803010310b98821002d50009100150999003e10007002e0200e003034002d2605031200480c4e1401c0f22883c06111074034003000d0001d03200500c0000091640070410210b1048001c51142c06d0184d51860844003103860b510410000d60520b203000f80a1200c1c0c0c4107603411185c0203020148040d100340b900d031400d03014114280d1100d2034140303405c044108015401b0340c0113000d220443c2c1602c42d040070603880c0042542e42c0115401c0341d00b01c0100d1300500c214500180301601406060729503900b44020181c01404d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 309472517 1250 309471267 309471269
    0x8190b0a060e03010908040b040905010b070b070e120d020d180b04050f011b05031e030705030708040c0909030503240112090f020a0803031801020a02070506090d0804060c030311090901 81
    0x708200c00c015580e44140c400b50403ca580380c1d401607a460742c0f01c0c1d55440f070b00c0711500a07000310440c00d03040000002e1143c07142c5042d10003503a0801c0700020f41d80c40b040000c0d01ea00501c0301f22142c03c01d2906521541c00c0e8010b00c10800640301507005400c5504030300740020009500024000d8020039483c0080c410382c121074080e00c05032541640c241442050b8440142e9002d604500d480c2408006000300404110020000d4404c10610140010781c0f420329104101c400d00040342c0000010f9002d10018540750700c10921160000d0041c401d134039203540c40b041c201b0f00342c3d4245541500455030020921807500c5101c0c41907560701c1c03080c06915030405c00c1c62000800040d02c1112541c05251900040380c02d020948198003d010360061050705401c2d5280f04094480c0c00c00c40303080d8580d800100d14a410340006008441704408568003400c00d00341820108129900007034041030704034044681c03603800a552100280042d100d180c4400d9042c4000d841d00030155640c5120703964036480c0a010716140da45903e05014 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 309473767 1250 309472517 309472529
    0xc0a05031b0d060b040e030a080f0106080a1a10090e0f13140f160303020c0a080d120f050411031903080606220324050c07020114070c0608190b0a 64
    0x51075500c82c01d0180280c00800c404c213a219140140c5146084000001011400391a4036840350b26a21613100aa40c5482403141c2004545500005412007289900441c0c9a91400d070341c182e8420540004036400784da46445400109003014001d11031103a9a403009940841c1c0c01002c802c8500d84171030502c1070650125401403d00c45901456441d6480c18440e0070000c01d00081160501c0843c17415940d0b54045601c02600980a100403005450414110900641e110300000340348074951044215101c003101c0141846550f0b4600b0741c1d11181089000d418029800340782c0384110507281c40d0806040c805d5010002c0405650350705600e00081e009040d191f0300160440f4010380f11298070705c210b4403480b41100f08000700750001c44080100310011800421854030501002100c103446000d1800705c4400751240b8106040c248083e0006622a1030071340e0340112040c0c0c45500304000b9583d409012040c503000000450550010003071003081240414203074284a030341c00d01c544c1c1036a82c00f09441e01914042c0c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 309475017 1250 309473767 309473779
    0xf020301080a0210110607230901021507090302040203161710050103090f02190f080c030312040c120308070e1f140c03040603050108070b04080d050705010f0e0c0a05031b 75
    0x1104119029040c4940c0c810f07030200540b080d40c5403994005200400b10902d005002c0721408c5d000039000c0c860800e0f19135000040e0003d04001242c80003240c4c1d410402803c450030072079104404001030312140080c5001d01c480c09881e4014461111340038000d060f282040d0381d110302c010810042044200c0140d0003c0f203001303080001d01c1141d182400d855580c0c8490380a500000c1104420b0f007800e001404d820201e40500c120351058645803014103894240031110103030305600501c1f891040381c003108075458201d4804c202904002c1e03500d40e0b507040c00a26414041e808200c11104015040390070801e9800000e400301c40c2c8201e280079288502806005d04140b0380100000a80b0494405d5000c0c1c0c2101c050010140440e600c5580c1e031000200504400d00860f0346a02902d03400140700c0e0140f01c00c0c1d9094981d5900a8126019240001c44080c4c100e0802600d456495000d44155040203105180d07814400c040507095142e601d07402e01c0707419545a03001d24060390000648602d100034940040d00746030011103138 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 309476267 1250 309475017 309475039
    0x80d0c0b090102040506070b0405280b2a040e07030501050a060c0317010824040c1e0b07080307030e0d020c01030e0a02040c050a020f01050606030a110c0106090f0f020301080a02 78
    0xc030b00a0249401054000c0d20001c2d480c800d1000403940d13203100e1032040085800382200f1054211030209590680c0d2078000c18560840c000a040d4071001e03038010b1540340a83c41c0c8420304103130400034510010301303140d540b500003500b840b003094400d00140e4840098201485103515103404503804c54040d2086104000c2802085002c1510408000c7c132400a40100e007100b550711486100e89907042c100b1261b020000c5441008d41140100340180e101c3e0360860740b1802c8052810391480d2003566107001c000c00c0404490004600f00890340050312043e8060907503241c407071030804c0c03000e02103801d4000000d0681c0e200320107074180958000b90400d0304003020700c4d01150307141a09160f40c0c40c0c40e0750142e00030740c06420600c4854141740e0040c05003851180540c200d8482c808681d88003402c0300c501b03403022034102c01c0030130010740750311440d401402c030b4916488817046c030345150005d4003800c5910980021040c1134032802d1008002c1914000c55500380d81c00b140443c6103500d8160080c0c1e4408170040700a00811103121 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 309477517 1250 309476267 309476281
    0x6020a08121e0c0d0e060603070509060d0b07021608011e0213050d05010f1b090302010c080c1f1a01021e010b061206010f1b03080a02040b1b07080d0c0b 67
    0x110b00ca001c5204494000e0365814480c2080c009500010004584645000d214040004002407464001c80c0003401030070f1147c1c1840c0500c2524400145001e03049281d04006100051890444600c54072059001d003040302c0074103100c81080c00540c0d110381500c1c0e040c200c64942c03100d0410a10750103440814001691075000c000c0d4100c125802d903025030380c40a24699a50240041904030031a48d1002000c04c100c40d00d040d0f0520f03401e5032000700307403100040d00040041c801075018102103101d40c2d01074071410b82011001c4440c01e2801302c40c0c04a0280d0701100c00d003040420311150140c0580116040742c8500406842c0000070340d1250030090080c60283c105202d04203100e029030000301c40d00006400c6607134841034500302c800241c0c002d071802e40c0040c80c0c240c2e0b40041079214609004c0100e080300200350b240c1d4000e8600300c59600d005426201c08643c00c00002a402e40e8402c01031440303d00352070111603d000644045410806144c0c807222241d002003202340440750340078501a10090307100600e201c0030f88503c0c07 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 309478767 1250 309477517 309477541
    0x303070810090213180203040b0a0902033a020321060a09050c070b0c07020616060b030106060c0510061215180c03061805030306040c110303010608010f06020a0812 72
    0x350246041c64400030310307070441300c2c404101d0105445002030000000140440444c04a10080702c025002000c41408225401010f800c000304007030008040b1107015201041c81036200e555460440c1580d0502500c1856600b1442541001c035003490024504000802c0002d00b04003580380906102e18401c2d400042c52070b541e0f20481406400c1a010801c25450100c80300c2106500561060700c503040000001741c03891039007008507629641d001d070903541011061224a02e4904074820100c5a003510342680e00b07240d441c01d00c40d01000380400c0d0b541030f101e031003541030542c180384084025100690a00704184004160040390070b280a6020b900c0d050441c051140300e80050a01e0000e0880c03030400200d101051000180d905801e0382d0051200300b111907469000c0750b400610440d00104290018000a15607281c40c0d072010301001d03114204205030300c000050550851f8030981120002c10704400045c00201080d078030703c002400503400108007030321060311141c1c001d02888034103521b1901041c000408402800d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 309480017 1250 309478767 309478769
    0xc210709050c03010e0a1b0c0303020d0510090b010503130b0c0c03040806010f090e070618030f06020304061506140a11010903030c1d011202070302070506071101140702030303070810 80
    0x201420090782c20300c09211880c0e5842880354030004000301000c40c403581c400c0d203c0e0300460520100e80c0620120602da040e40c0c080007207141542856420b0000e186100c04a010702445000038007800a013003810f04140e00100c803000261981001000d0041052089a100590000540140a00d6070a541304070001c01240304070700400b001c0d8040802c00140f0040c000440606030350a030700300d17408110380790310040c000c54244014200240d844107204012481c050103180001c40010052003164a80369140e01500c0004a07104441c00c95001040006022a40c45820b43c240c66149551016901c0d00800801c0c000540101d8030b0020400103d0400b014095044500c040d6600b00090200c4401d900700035004065074000700c0081603945184180c00d0701800c80601c04000140c44c1d00f10b504914003544002500544812001e5200c0d8900107c1d1513940c070342c050004a881013408500e14050320000400c050443c205103490a001440400d006039000310950f6031018030740c500001e903559a15000b40c60740c111 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 309481267 1250 309480017 309480029
    0xc06010303023c0f030406080403081b120402060f04030305070b06120a120c060c02030d1a10200703141507051603090e01060f0e0f01020a1e0b0f0106020f0c2107 71
    0x400200004ca258020b448e030392145000380c8401500341e0300d0700341c1c0522000c08054071406500c41001092412030080c01c03240c0d0461700180000381003405204001c112903110f904250f0218802003070380340c00c0202004000d82c0c802010358020307001c940c504200320f41e1519900070041c07a400c0d00c00161050b10388a0000d2140e06d9402103418003d417802090080d4403540080c0d401c1749410300b0508081c1d070300c25142d0007440c0000c101030710300603210144400445052146005000e411114460040400d10042085001550240c00708030001d20f10038180628140701c1d9500d6102e010501e00c1080045034000c000d550202e1096074034501515524581141c1120050704945030520054001281030ba07441000c003410075282d61180d0340019a81000c0000e09229003100c980168030101070080080c40c1d000181144040e1240703140b010003001d541c0c1e8a412035040382d02c6d54428080c60010041158104240c0403d0744010300604415205040818000048101e15140c2c0c40050448101810000c001550060070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 309482517 1250 309481267 309481273
    0xf01120207061103250806060903030c0105091c08061e0d0204050c250507030204090503040e15040b04180204050c0706090602090a150207030b100b0c06010303023c0f 73
    0x111190814801e130f001642c161204040301003035040d4069804542600a0320940c6610282e9618501080b80da540910720140d0035000c01e01164681c12024011240550b0450020380000203441e1600c00c0308170014103400040200060030b00c810b5850300642d180c459680c0184540b14603280070040ba50000e02801c000750401c0c605010045000440d5018040264188003c840303458409015140800071240003e845600030b0101000146460303807060503000d00c120241d80c24156100b000c2120003404070f9078072400480b1402d030084589424481c41c4194a01207504000c9602c084003ea01c00de40b42d040001d000b1aa5040400d01000e96001921202070780080d060154401038544240690403090700f02d802101c110802103001c3c05a003490703002c1151294000c0c2140391450302c0310611450054035011485130454000300d0403012640082000d08140c10041483c0e5145203402864034400c844039902c502141101c4204041d444a40011141c800e05000c6071041880100307503041408464206021384 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 309483767 1250 309482517 309482531
    0x2180405060103020405060a140906040e1506031018032102070c09201917010b03190203090706120612050f013204030903050706091809020f0112020706 67
    0x40006003075410b813442039905100302d032141d0003440040c80a900a02e0142d81c40d0400c000480c1c00c18030744079503000d07034000c10114a002000c1c0e020b6040060300e0354100c0c40c00c0014010004a410304110240b54010400c004000c080010311121041058041009080150006c9a0122004c21985d00b246000b40c0c060210354414451803c2d030080d03c018414504040d00b0000b0a03c0c4200d965072480340b019040d42d8181e45406400071907051640360301d4000d0701c00e0100b06d410310350f4040701c1985100d0217810060a025560308207407603102d860b100000210a2058010420458078500200f007041c1110800e0030500b0059021004d007801070b198540107000c010f00000104420300400040034140748d0703600300c001c00210030405e11140038200d03814182d00700320903c540e001c020612030000350790740607001e450500c00c216169964141030196550104001400c401424051100001010342c034101ca8a10100004092580481c10030100250f44a0602c0240d0500348100e01803901203a0500340e014100708105 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 309485017 1250 309483767 309483773
    0x3110c010f0b030a03051c14010b0c0c030a150c0201240608072615040507020601080111030103150b0a090c0507230601030b07020f060906040b130b0f04021804 70
    0x2041c00c080c9051005003840d0081407a420041544456503400d961a80c5c0b43c9440e440ca030115210845501451895880340c034561520807405086001c0c108105481ea544c2c406036005a1609594500041c481c2c2c00c039580c92000600c400c8007a001c49035051030081407843d01c05005a004080c2601408500c00300c4072143c1c0380d80c1c41c0c1c48003150252141c0341c8940180341c4489074201c6260000304c0c0c10504014a03503150381c004080ca48286940309001341c040118180c0f03c48045420f846003070b00c03082d002d030384514014450003000707009544a40071100c10960542d807450f05c1d80c540741060088041000f55540d045001c1e951202d401c6038000c2d1a4a40301801908072000c0c004226a00c01401900c8031811030244a0140310016044034041c01c0c800000c0000fa400d58070744095104010300200c00b0f6105225034903504000501800388221783c80c1014048600d02818040b618103002012218a04080040403001401018005030406000403c1581903500d03480420403010b1318000040445405000700410 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 309486267 1250 309485017 309485021
    0x5041101030c02070b0906071103030a0c020907030c050306041a030303041b0f060f120f0e0714010c0302030706200f0c210406030b15041203181d060103110c01 70
    0x5040007a40c1c1000441030b020422078880720716008000d250360007040654541d203000c1000d46481070042111021040e95480007a14503484500b5110200d60044201b000b5440c1183e000d5601105a0a050100c0421110300400500c0001d00b00c2d84a40c0c0c0d10404250030140c0030200e01201c0030040d088035601c0c107040c20070f101c618840c045141102c4019000c00b1401e6007540c4d0504007280d00c1500c2d960780100854405484070304141180910380e640d01c2e403d00708401c00e94051411012403146c003400d00142404201052148032400b10f5040c00309200310000003d50000880d0311043d00100001900400140d6440d003100011010304100398000c15125084240e40e0000c00c00a40040f048440c40c0e40c240c91080aa14a24220803078032102c18003082007420701030340000c2400c1000800016507680d05c450959450f403c10740114400e0007070703100503500705500002d8980e001401d1032441c1041c10710313100c401543c940f6108500400ca04007100410680c1e402600003d400344580c48031300b92581c00f01544c00d40 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 309487517 1250 309486267 309486293
    0x40302040617060603010911091b0a0c061a060f0a170c03011d0c03011a09030a030201060302130e100c0507020a0603050910050907050d0c0b04030b1005030f2109040504 74
    0x2d2900550b00844c0407813030144115000c2a501c48181024010b50381c0c20400000c5008000c0c81400d00c0000c0b074074040c0ba4805005081c0c110042d00d4641e010715050408000716144ad500c03420b441d00b910354104009540b888207958a981c0c01c070340c40300d950b604200000c551a00a08482512a50004d02031240350020035029605a4400c001c4250b1171010805510068000079a41c021001da006c000500c10340783c010050f40c91050f0b00200f81d500d040c440c440400c0c982084418150010f0350b40e05030920840c40e000030700e075840000d840340030b0188007500100302c1d88540d03510100c041955955100106098000c3c01a00c41c1a50010100d20031655614400f030003804003100d01d41c60324041c0304241203441d044d500c0b601d8040d401c900000c040c4141490b080c04035180000006030351100d83d0400020302c1080c0c0100501c003075031041400d0030140c113010041c05007808040e00814841e820100c00446180c000003440603030400010b9854a0000600420407101c4c400e42c16103540150609040206028070412051 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 309488767 1250 309487517 309487559
    0x81e030f03011d0f0618090a02130c0e090403121509090605040606120503070210051b031e090d02010c06110c0106081002030402010801181d06060f03070f0314030403020406 76
    0x80d01c26540c1180145561000321400c0d0380c031041c03c104181044c81b600c10819480304220040360103c8240b60005800c0320300c46900070341e0580c3c80704000c03114554440000200c807041035030101700c0c40c00c2c03a40c1e0140a5501d05440b11740007990720701d90a5140c01000007400028040d032481001900414103280001d808201c9041c0d4106045c04030005500452510031011540c00801660900e0b0582d42000100801510250104441800111103680c074151031220b040700d0440045030344541000e00056034501868581419103c1485070034a6501c80010502c00f20b40c0c2460540a51003040c540940201030216540003001d10114405000d110154418001c1c2d8514104883d90180c0724041c0030240e210844009002034510001000b642410b10003403a154540400041404840401042003100100c4010f910329440407040c0705841c141403c420a441e1819005400401d00b01401030800740310f107200041844880a200711441c64060040c0c80103154010424032140c1c1e51244c4800c00000c0c081048 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 309490017 1250 309488767 309488819
    0xd08060f06040e061f120b01090609090e100e03041e0317030405010b130b090a06081e030706060b030f0112030c0308070e0d1401060f081e030f0301 65
    0x1098151610302a440c101610003001589071608202010754001c102034040c5400c141c2c5991885220100864004800c00301035994400c407021402052041d1380202001d14180038400f1024002a98405410401d1710030244001ca10f009078070704100d240030000c1109135030300e52030201c1038940140080000c0041720700c203c0310369010072213188004203a41190b01c4010208003d4800c102444206c0c0c401441c0d1141c0104000580c02261001098007030700144504040682e403818020801c3ca0412616500040305500c1004030500340b20808d0340c2d030390010609844072001d0301da01c07010b00c01040040790020755100c401030046642d1411440d515800a565000005541000204040601100c00c01c80c0b107070190384540741460140c405550412000d0302d28000c01090320000a0a0303200e5801d2020b0261117040d145c050100400d10311821a00503400c86000b030200a001000b55540010300701c801c401050074008650705c50740500074030310f125069500c0306a603004400001c0c1c115000300d4481602c3c030300c4429 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 309491267 1250 309490017 309490021
    0x50a08130605040815091e030304030809030304152f03070e0312030402010513170708160302031507020312010b130b07020622080a1b060207030c060507030207090606020d08 76
    0x10948041c003c5005100c66944182c6000c28a102d5031940d954001e98101c00f61100300c05640c07034045840000200004071580f001091000b003580c07044040e036005900e1000745066044c41d40c0c3d2910141d001c19070122140b611281c0c02e030301a003410002543d02042c2c0051050f912443d1840100c0517070411100003000c1480b10360300c0c1d0114180440d801a925001881e554a15510340d801582c1d81d400625a068010391070300c0703000c16440070400c0503558660b1250000d0a1726840c040ba25880d00801500c2240f004807104402c00068800262021280c2000b981040784e654510030101e103580a03c0e00710706d50501c0c05e04000070b00d40c11381c2801000701c0666030100c41c00c81500c545101559100d00381b402034006130f0422075000707049202c07c0c800f04411141e50b99284203658480003e8a8824100f0007034640b641c8440301030f125602543c40301001450310340090301d82a0314545602c075087c0190711801d824408000785082c00c151091200070301411000f20308100e02c2d51101c000039580d0000209010119840b580 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 309492517 1250 309491267 309491279
    0x60e122805030408070b090106030204110c0111040503030f160506040b100803121303030b041109041a01020c0d03030f0603030c061401080c1201020f0714070906030314090d050a0813 80
    0x10440b80710f00c0d00b0400aa1038203035950b0311100c0d00b850040840c595035580e103401200690700c1e800b8260b20003030280070031034032458187c00c050300311901e1451484850004100c100500d0714080207607107072f00f503001303280d50340751143c80c00c0b10074880710a5040140b1034000c3c6010002000f40c44601c80b801907e00c1c608072191580c807401d1055891154501035281142c1510000d42c44900e40012165601c0c864a00400c00345000f50102d82a500038158101100c400855005034a04051003031041c0128a952585140c131000c0d0300103502c4500c6405442d0180540391081c0050500070380156466441c030a108002880e0b032410000d18aa80b070380703c02c480c0c003424400f070001c0ca00c021500701c1d07060b1048800605580700b1018108201c005140c4003114855400f4044404201700d0311000e0b10245010721803090000480c0c0d03640394100162034104904442c030301030301880800d0703111092052804083e4132060381d0b8001d23800015004a00d5900082040c4580625a0208460700c2d02400003080300d504541c0310300d5101c072 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 309493767 1250 309492517 309492527
    0xc090602030c0616110601030501050601030c0201060b07120c05060403050318010902032806020c0d0906081b03060d02060712030b010201060b0720190f060905010c060e1228 76
    0xb140300c0d0302d9002002161504030f030b5041d0250071107000d0030003600a10001c1d41084c240300003680251340e80c2e5518002c010055030140100e1902e100d90384000c01100d8101030302e1801c14040c5044c0500750f0b003403004070460b174a0f0098059012090300102111101d207480d03c1d00a0441d80200c9024940c141c59403000c041a038014012000c105a00601510941540400080910079403601641c00c180d82d041d095404180c152008041244062002d001c030705800791001740031030350140c0c4044100289070041000d01c0d0704900e14001e4240c40d20f4074041c0d60361600f80000349000341c2a01702035408007001501400b0000c0c0d003805040100200d4609010031100d0600682c200c524911403415400e40400103038000410849442d5a00808903e080c1032500000010174004c21112012001245c21000c09102e012020301c0c0d104014040c601d0824042e03418000001c2069031001c400404942d20303038a407441c0c0c2a00921015201e60b0342c001d05239445070b00d1410b00c45c400c4040007548082d61044910180c441500c52 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 309495017 1250 309493767 309493777
    0x6070c030203070e160e010509130605030d050304050601060302090109090c0e01110102130506091314010603050a020415050903010603121d0906090705070c03020604092703090b0f090607060c09060203 88
    0x5c8250f14420300107010700b85c881241000f1014100b103010404049540c0d24a22062803a814012000510f18208000e00d460040903800c2542484000e204010010b100003d0450554425143c050386940c180c00c010385401c0340c00d40054121a00303146405480a5100541c0e0042100990340d0743d4400e440302d44107600304d02c200c041005d60310210717000600050501900410840501410103200d24a100201ca421a414402c2003e090550003004200040c1d0500459400008103d4110b18040c40c00c44003410100d400c05814003480000715980105950a600c58401581c010aa00c0c84804440c0d034010409115000312810b009480091201c5600709050f05034441c8501500041c0300d6125004140c600b0703001100c00300d0b034007030081c2c1d404001600c6040c0580010251984007081000140070060301f03035503d042840017406001c3c203042e008039600040c030030200c81841c540c080d50f48180f85511101445a03003282c41c1c200400261070310420020b075005089821040d40e034450241e4440c0c00490b100d00c20 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 309496267 1250 309495017 309495031
    0x160c020306071805030f03040338250509030709022a0a0c0806060a06031a1210060f0807050a0612051504140405060601050408210906070c030203070e 66
    0x1071001640c058040d0000c00b41000c4003640a044195903000060310b00040201800392541010404008208800601c1150340002e43d4118155401038494011a403601d03910b03542e9424800b2000c100100d40f4038440780ea501c181400030600c0c00481000241c515445200500d0107442444400100d0740c1c0148260b41081d126041e03040d8115046400c07040c4c52244000003600280603c0707015800144100160304020300c0441c020305190f290140411003200c80e03582c0881d040c542130801100c01081902a40c610560044402c5c1030802c4914060500d007560b48a612110306107030000201d041585090340740100d40c00312045502d5161250103100550405110360004034000517510010010690071441e4019402104501584004400541070b120b491740d002e0303522540c4500380404d000c0c041c45810340c041002e0030301e5407a06141c840c040b942ca03e80b500389905044241c0103a06403c03540f0741c00321041b004000b002031b40c413428030341040b00e003052171b500c0100d1013440390140000d019000c0b04d8206100d002 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 309497517 1250 309496267 309496273
    0x50408030d020a03110c060a0f090503220906060203030406050a06182301060e1201200711030a140d140a030c030b0a150e030102031012110414160c0203 67
    0xd00700507024003035003218043c2c409041d04c582c4959100301c108405440d8507556440280b8103401c2c615403010454548450343c8005504140c1a500840c50000031075406900c2078080000e082c0340100e49501a17192134120071052802d0a03030000365168004042c502507030040d2820000e43c3ca5a41c1e400d02210010f00c01c21030402c0204020882c010340d180d01054055000d60303040d0340031421041e410310010100341c02c10000f207000c00b484400d0ba0700303045a12124200302c0c04000c12000d0305000c4050300080c0c0c04102482501c4001401c8420047c039a84500700ea00c03000fa085481c45505403802100c990400c41c400805840794070380081c2882c0c4104802c014190300d01201910340b034800201140904883c4000005060b00d66000280546403034544000a10b4420b04c03004c1c1a88020a00a00e0740140030f94945c03007680140f081c8071100c410040d00d4011100c0c030800b004090301c12803070070b010364107100850a64414a032082000d4003401c2c45040c40d12803a014108000043c6401300c00380c1d07018540442c080e41541c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 309498767 1250 309497517 309497527
    0x81509060d2a06110a02010504090e0109050a06020901021011030601030c0509090106020d0e03030906031515030a0603021005120f0a06081204140a1d1825050105040803 74
    0x400d00551079040309001d03003007400d000320b040104560034014a1000755021070580d0700811509521000c04907040c84888080c040d5405540c0001341103000d03d008109507642e5480808400b184254006402150b001d800c1da01050858105078009410280313149025014100d00800301d25418401e084d1450203a10b9024210744501004400404c45040c00100f4010104468019607840300100e500904181d4010504522401001422103d03805540b9001c1c0e481441009540c0c0da13000140ca40c400100b00003000d4040307a01740042d606020703c1d000c000c1d000c0400820701014100d10f81259003524000c1d149201b8420700c47d401110a441680448407107001c014001c1294010043d14858121038546030208105445141c010300b0500041c1745581949400181003043d05e0f0301400d29800401e048541024892038407411004143c1503041801103210b4410004001e403642e0f0b4120080502c1500860f00c0391001c041800c03261200004400001202c440c000080c1584908203c5082c1c40081d0007943c00c1c4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 309500017 1250 309498767 309498769
    0x1f050319120306080f0d200a0204110432060909060409170d020408010501050913060c0504030f11030f030a020703060915050403081503010218130b03010c030b0108150906 75
    0x1240540c400204158a40c4030019500104000c0c031245c0c0c0b05100040c0480345a01e0001038444150100c038030491244410483c0200a004940c40081d140c0648000c0b1700200c3c01c820500f402c2c03240f0b07001400e90f10740d5603020b07286404030b0340010881007585040700c0c041f464524041180ca80951040180e00c8810b1400013002d900700b035000595818451550488400d0a58955000a41062440c481a10b030701003010405200240140c034014941aa208102803c00f12185000c0c4010b984000c0c03c140d80303610008451030303c82c00454008540000951742c0c0d080307891502400310f020f81ca4141d44207102c1c4541580d00004040119005009190000c00c0591319654500014144119042e54514445d4810000c001c0050061900c07452290380c840009241c00c00c07440011304000d03950280681c3c4181300b501254104000000ca403450103c0d07052959041c062204006000d00c07414054055090035480c03440c04d50103411120110501b40c80324102032b902c1c48030120f215960000042d6021750120041145 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 309501267 1250 309500017 309500033
    0x10807032f01030216080409090519211716022514030111030711070e040215091f0201050603010c08093c0d0f02060906060111070e1f050319 62
    0x70117802e030a11035581025141d0820582059002c40d18140d120380a00781004000c0c011850b42d0b0303d510040a1062103252154114403101038094022503924080603081340b8010041c11504170841003500c07645203441030b0b0113000781c185400400094032540341201c00d608864041080791940301400481020b150219403049601c4001005400d55610040005101010001548952a16100c541d02c017909600b8007454010349504c00c1e010720080700c050000590b07405030304d07407600a014607200b601c4032440000181008541b4200c5c103034110429000201c03198040d040b40d440380008030000c04c03604156801c16986a001140e60710895000000f0003c0d4210f0f205410031811180080d410140b4281210740c00c4802203103064a94071030340031348206412990300241001d520003013440a0300c458188070844503035991003d4802418021681030320260b842c0100300d00300060485803070006182c203045a061416011074110380104005494000c1030034100007810f903000b03400d0451010041c2403640c4034041 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 309502517 1250 309501267 309501277
    0x3030305012304110c150f07051912180303050901050105060708220506040f0e060103020703021005090c03070b04150311040e06130f021216090e0a0204030b010807032f010302 77
    0x940ca8606014407204584208050701400c54401c0000100c2d050660008030302200081c10300d4208503003013104041009411100d000000218142f00b080d00666580072070240101c4900700801c100c0c030b00c1c0050141581030b0485405010341c90000c11450740c81300140038040c4548c801c0508150420080c0554905000451298991904081800954440d0000707099544503031f10110821400440902458050070020358100d682403c0031403404009d0b96000e91680818031582c280a0790f2070000071000c0c0002e001c1da282202004041e0307035a280d2075034144111500f103800707540701c4607112200d5041351500911401c9801030400719458205460800590500720008103a0f1b40c10940030300962110600030b000c0d100f0203954001c00503895108800d08503080f0400100982c04c1c06400550135424184c0258103601980c02c0c0c0d8171040101d90321003000340060f01c0785a0000708102c03242c100010340110041220b809407032144050392152002403200b4030403100b2145002507508400e4428507581d60181e40140 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 309503767 1250 309502517 309502541
    0x604051e0c0d1e050106020a0b0103060e01090203010e2107020d0b07020705060a030b030c010c020a17251701020301063e0601090f05090c0607081e0403030305012304 73
    0x280352504600c0e021050f036490f00104035010b608807044a40c00507075030280c5400341010b4030041040e269a5103800c1130b03040e81880050a25650388412460385402904102981d6030090001e001194041c60b186a84854031000024501294200c82d54094040c42c100c0300c0c00c0760010460007115156489450030030002038000c9042d0f120b2500000741a85840b80508003c1001c1d480001d2611801000e2505000d58040711504210f0000004030069541d00e01302c3c070a0f01c0c550600c5400305c115a000e401d141035506001c000200c1d042005107421a4826407041003600c01c4803802c20303c0703130300400c2e0201d007030303000070b02404020941250244a140018507030180c2d20042c201c05a11a249150b01d24100d40e07025640e926441e0b820400050094101600605401d6601410200203034038107450559282c0c00086515481240001103400034041e01d1b0703055650640e101c40c480d200d108104481c1c1005544188000c0b4040f80c20100001180f0143e104000f070440e0009803038950301302d5440e04000062054a82c42 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 309505017 1250 309503767 309503791
    0xe010908070327060323040f08091809031306050c0a0201210e070801050c040501022a120307030f08090a12030e030c0307020a05030c10050c0c060f070b0604051e 71
    0xc81d65420440020900800940d2000601b8020084c068080d02018449004003501d02c54140720004085607003c216040d001440c09899840310400206c9045000c41c030b103900c54921100b0301004040c04401001d500c1120301c2e00520150f074600d02540c241c02401d031070805070380098003d0ed016502a040c00b200710035151410070327070300d240c0000090b003101c02d094400e034600c0d8800c1405100c1f103102445066007119080003124201480c04000075580d007412000d610444884500051418483c01c00c4280c00100041ca507002610303507004007d540e0b800201050300007881989001060b6801458014003526460b00904006005912400003000220180004043da54580103402c2d81051000e001441041e03c09160b0310895070040045c40f4025810541c8a43c01409804c440c65941541128081440e41000c4e615110007211060031b001d405a04141c02450000d201d8441090b19401400500d106405250b0152154030030f101c00c80c0e00c12501c0c003026500c4181c587d10008244032105038040415540 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 309506267 1250 309505017 309505067
    0x1202060f0c0102161a0702070b04031401060b0705030307020d0504050d020d210215160e1e0d0308061c0503160c0f030302070303020d111207080d1406040e0109080703 73
    0x1070b40004d050704002602c0158030f0320341600c00c5007062440c503600004540f008181083c18143d02200c644101d100081c40401e0310294809298829000b00e0000d02001100715250542402c00503142da000319202c9005019031522040c2e914001d0742954291140500400d510090b070754240448461800d0041e1003512030104980d401a01c040340c604507144086d8090011040400002511070a0241c414240d0b0075030088111821648040c1c9010854422540b044207980384035500004c005d806207950f900680c07510b11880901da00100000e015410030303100105040d141c2c07218058810303000310f402085908104a4448000c1910121489960064407a03105090743e410b502c2c0c1c56038010740c0c01200543c0104200b00145501442814458045405c110074904080400d00e41c940c4290001c2000e00c440108264040c07000580a49060168034081048040c10845020085080c00c03120188111305002082e00c1030039041c000c07401d480394858490350404c0416a0b007640d14008151805c1149940f03048 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 309507517 1250 309506267 309506287
    0x21f1505060d09171308010227060705070e1b0901140901171009050907030308070f1e080405010c0309020303121b04090c030c112a0a03060e071202060f0c0102 70
    0x112901c120552a03803003a45d1900700340481c0c08041d8159029242591040c802c10703c3c200488614003034402920300c00d40d400c0c4100c070400101c1500030a040649544500040840c0342e00d9401c40701d80c014001c0d0088071600d0482800300a8140c030440640c0340c0041c00b411a90388106d1048809800000814107029514607112003281002d8501154940b020b0110040c04015002080c86020307044207070304014007816400c40d200506003000103491002001019521210114807824192a034444e6a50380783c01810300b1500c0080c0083c40c02d0b0703800da8555203005045d0000501034441c101e0065809070145041000070750040e1040d050050414131070300c0800d00075080360440c1000410180c0101c40340040c07494035106005040700d4005004205001c401c0c807500303c505100007002510f44480c0446510014240f0350000000d41c501d0b03400036040b0bc0691404000c00ca01600b124000c1c181d044100c80743c10799542400d24104866031800707900118100142c1304ca200f144002400c28ad05508005454084a20 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 309508767 1250 309507517 309507533
    0x160e0a090903020601050a050a030f03050a02031308060612160519030821010b03040209040b040507090507200d1b030207030506190c08060105090609190303021f1505060d09 76
    0x30000c800503001311005000d2454201c0201000e8007086e22410308072401c41c0c1d01c00c003c0d10440b0341c014052000102e42c40d52118800c00c2280c14103c060600303400860f698900c00d980d079003001e660040c0f26002c811005400901d00041038200a20008020f50066107400288a0005090381d040b0160400c000c00120106254a00400c6072800e16250001842c030300036403910340804107802800301064200140f2015030345094129400c19041114466251100d00d0240d140c5899035025203251400e001c2044009074000c00c03480c80a14901c03010a03c0340d03607407001d500d80300d440c08a0620041880800b10200705036052410017a01c40c030900456200c56100d850311481d00c00101c524001078451241d40980e900018000c94804071594200548182424000a0194066441e01d14014200840c000d08030f07964110401100480300405440c00d00e440e070900a444446142c050502460440c400e668903518608c282d0b1825007603514170003a96030074501048071640c0503e0068000b0380d01c1d14895004503040c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 309510017 1250 309508767 309508781
    0x105070807050d1407050601030b060d0203060a0c0e090105030d0e030f01110307140702010c020402031302091828120e12010902090714031609180905011103160e0a09 73
    0x160001d0003043c0925000800742c5031034410442220000f80043d100003000098024150380d4840154a2540e44060224901088010b8080d616105030f07003e00c0001c0e09582d101d2111040e455594480702a00181805285942071103195019881040d44e4504188110940c00c81080001d041c0d51684502a0600b4250380c070100d00100101d0000003401800d94000b4002c00d15072450120070750402001e034001030240d032080d0201034000c64000001801c084d285003800004181d00a006408a040400c2c034400c050700800140f41140c86039031a02010300c04007a0001c0b1312102420000ba00141880d520321036619208103049040c0981782909401940e9018007410301c403a05400001030112550042001c8110302420706003e0103d11a044500d001c269400c803a40150100306903034400c00041c1040760140d41561108900444824800802180070303003040d030500e07001c1e00c028440401d4134030000307142c1d10040d255007a20f0084480c20f00b00c82c0d802003084055500d002403003008080d41c0c81e60a001030326a4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 309511267 1250 309510017 309510023
    0xf0f0c1107032d0b16090602150711070b030117120d0902210321130609020d020301150801050a020f091201090206130e011428180b2713020105070807 66
    0x1310908100145240501c070b0609a580f46c600301c40454a07158001e5140c046001c4103a0a403008140012452030140003a0025404000215a501603407122042c020341c10038061351643c0d110703110b091845c03504002410300c40c41c25410078039403400300403040d508024014803600f00e800401030000c1905120600065040000303900000c0c0d90f4a01411103c3c0129603907c066121104070b640301030180d0540394005145040f5800000003a0090f07090001039041014420000c2d41507003400b2004080c0c800e080c03e66411210660b0003403081d900d900d070040c01640119401030b45211801d0104c2d051510f041440e10549405600001503013060b02c1e00490102c0d0300105050300e107200280300401200109080150050032403000c61600c419030480001e0440c0c944141c038255051070400c070340806010b08030300c040091214020f544002024020404060540000d6062080001c03c258450481101400c05503109080303500d0b4140e0f0743c6050801c116600b8402c1c3c182d0400c43c05002080000740740500900002b80 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 309512517 1250 309511267 309511283
    0x100302190302090604060305060601120609020a0504080706050c060c0306061207050a020c18010e043e0105030f06060a0207030b04080d180507180e010f0f0c1107032d 73
    0x1055006010040030f000e8450341c0514171b0140100302040c0301052a5400031170034607154180c07100c000380c3c0c02c0c05030803039030403185079107200203030781d0511a03045001401103540d550140c0b1b02055440c2800d03201c0340102c100004154000c14000ba1a480e80d404c011940050024020b40c00c0c400180c45100c5480801c9450801003140010034211841d01040345044481c41162007020440c4e6100c4e8200c1c450b00184034075401880058007007820040048004d1004400740241d00000d4100480b641c0f02031040076603801100384040f1001402d6504c128212403182845d115002d000d034031580240a01940410800c0d002c50143c110040001604103c0080c0100d00509016813070303d044012890031140000f2150300f2003035440c0a0480040c501103880b200b01c0d050701000c91000b2911243e920064032800c84245400d5283c4040f00480a07180e030f1140e412280c1c0c1c402d04101d0278070401c2041c2c544c180c2c800c7c00040380c1e5012134410000124032144d48500140d111648010b1030491000380c90b4590445042201c03020 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 309513767 1250 309512517 309512519
    0xc0901030c182a23070f03020a020d050c0901141f09080a0809030c04060302150d060e010e0a05010e1b09060706050f04060b1503010e25180503010606090b0310030219 73
    0x40e40605200038121489500c08003140f42e400c00e042c0d00b44101700c0d006002d8444240c6020516009000d144c4855401600842212050713113000da85443d14031850500c20200ac00000c22a6800c90845400404019000321150084407503404c07000c0d050005400c003048000303000032401c0310041c040b406225200e1a449a201c00c9108101400c14500c121f070540174500d0a0410000360b51340c0d40407030803910034421049580b2004c14410a014100303e8001c54428104240001800b0180d51140d9114600c2e4010400480e40c803800309003101c0380e040d190300148010014001c112140f08000070450b01800800c21450642e460740c80300c2c10783d0303821182d03102500d0b0303544d0410092040900480048810841d00500c1c5038915a401e60380c80d00041c00703100c600b80d121000154140054043c44000003542e0b4110b46c01072003817000300400d8003400c04a00300f00c0e0600e0807000202400c05024040507106651191700c101401e00101c04582e80004200e41000107820130008050b89410307680180240d1482c0f0069880703 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 309515017 1250 309513767 309513851
    0x40515031305031815070309120c0b030705030405151005060a05160c080f062205150406020a030b06040803040b0f0d0c030504060b011b03080711010e0c01020c0901030c18 75
    0x101784014030f4044803d08100000010b940321620100f81c4d504c81c408109502500d023042e0080e01c22541080c11118000018081100c0d000406544500c3c8584112401220104840b50200805072801c228000816a06006a1070264040d02d081c2d01c107840c00c0303401c20f840c01c0f8100103040303200f941c10b80d282c5641c000c0511540c2000c1c003c80c1d0522035640014520303824000d2401c154103403402c000301c0d00003d0f035240c54410031009000c13891a40c03402e840c501940341840d0404e000294002c040c02404a0f250407101c46240c00c0407429201101d8038074002d141020f280800b00c81c0941c0c07020106d4000708d20204481484501d903403045e00c0c10b2001c80d07500003c0f90b18003881e00c20201d8002141282c18426a01c80a80744002741c0030031510099814602406140c803450b005451207094090400300c0c40d400e080240081060024000c0b2220700268225007107840d0300303000c4c050904020b00015200e5044400c0500941584034072044005403074060000b101c803100d0803100484005080000c5401e540f990703080142c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 309516267 1250 309515017 309515029
    0x20d0912140319090f200f0411070b130f050d02060c0408100f022505070603090807060903050906040602030306040c1b020f060c03041511030405150313050318 70
    0x7450350201d40709451030810078040c0c803003140e54048460080d074680c8480410002d0481900d040c0d180e008081c031507041d1040250800c000c2c040b42d55075008100d03e442100c91494140248403240c40c00013031032071a01714661520485502d0051860103e05a81d1940c2400511700c011813516490154024095070030320700c0402070070b00c0c0700a0440b4402c01c80500003444509008210707040403596081000603040301d13281e01003005e4024081596410524480c0d80070f041d6882000c194042c0c0d214070250b4003041e45a50b070a50450b0403941c80038018010601003040000d0660b480030390740c2d5000b03040c0035040480d0900090340e154066000000180c20200074028103040a01031607003459040d0500001c103800305104141d014100c1d03d0081e106e04000c12924a4545841c000c41ea80211014141c1e41ea454560822002c0621034080110006000c0000c81480314004410ba400f03452000304141988150401000301c960406480185040383e086d014034005001000102140d4000440d0190103d00481c00c0040d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 309517517 1250 309516267 309516287
    0x60f0c0319031a06031005030d050a0e0306250309080d0902030d0e0112181b05010818030901080606091003060f0602070810050c070507090b040e0d0c080a0201020d0912 74
    0x20306081815600c0c080b1128900100401400c1c4c422036100e6071088500c2c08010941d6000c5038060040e003102205584e8802c000700340911068803681e0488036030105250b03992001b21525a400c82c0f0309200202c0304078035a40d050180842915001c00c0c0302c801c03a26101c0c071503441000003c5c0150b69075001c150440c2024845c4180828032401d14450007009400043c200d05003802903c00e1080d5108862182c4c4513041320340040070307a0010007840680c181101540c1d54007603140200d5012070020700002e06c001040088100302049041d01850038003402000540318120301030041c580c0903d060061b8000d646949580c602d01d04800e5502140340388c5030400da1800716005800110864110b0182803080820009244c45d200c003060340c00140540d1440c103106640d010b080c200078003074081c0c8080000c0742001d80d000000b2030101203504000300501d0024040d50b03556100c0e201e40c08640e0344980d03807000c6941140500101192800090b02e01030383d0711407500880b191000c04581064000d90030a0700298441d07801d030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 309518767 1250 309517517 309517567
    0x1e02031e07051219111c0e03040803070b10120b0a060902070209180c0a03050c1302090d060c030213081b040c0212070c09050c0a03140106090311060f0c03 68
    0x52610a442088282c0c0c5030004100c160b13003d00800d100646014035510881e02914103403081c5855064840b592002d002d141014950940d0a15002890300380c8044221421102c5540066161200039074868401c010018820300c441c955032900065000902c400c0c0c0500d440c4a4881c264084c94180d2003102101e40c80e402c2004054070501c0b41c9030068544005194000d00a031100c2440c204900c4142071400c1c82c4011a035400102d081c2d000401c001000614140400040b00c80c03440e0001d070210050128003900c0d445661008500982c000860060703409000d09524034900503141640250450341c41d04507943c8500d8183d448090309680c40c00c0d806130383c4080352004072000c0c40100180b06000f9500c0c5072100b8100303001407001948038100844401520020484034000344102c1c074040c0d400700c0c842e4004400441c0828280004030700b005c07111014a030305a44c002d0b114410352506549030b0000806140d039070f80d50000d4042100030741410707d000c050200e01d132502e40210b603030302e0f0120442e80038120040e090f0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 309520017 1250 309518767 309518777
    0x20f0d15060e0909010905030c07140904030f030c020a120c050111040b030103150f061401080a09150e0a0606030c18060302010503010e04030c0b0c0d1a030d031e02031e07 75
    0x60000a82c4001e02d040310080c2180e02241c0c0b03407107070034140380180986100180700d40b100285101030503001007003a904130380703e14075442c40d886030350024002a80e004840007000103819861840100340a503000040e8883c0910468410320341c00da032142000e042c0c014440010510403040d03001045002d00070313096002c8a010303003282054607014203181e95000c1800300820a01643d50b040c50003d28585c4003858038290307500140b00c0181d071a51824680e43c000f540c22400100110001203542c071182c06403450155105412070800e0b44a640141e00424681180b914a805000c1d404000304045010b40710182d030240d01100c81d041e1500c602064100304062040c2ca080d41486001c00140c0e030494140d0f41140d8054032184041e541d036203030460b580d05054600030614040003050245401d5003001611032045404010020300d1400c02042c400120038410a6030706074490098001c015109811034000d4420340507451101d129843c0360481640c01c126100c5000021401c00912452a09882141c00c201c00e4201 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 309521267 1250 309520017 309520019
    0x6010f080c010504050a06080705072004060e06030a02090705041a0424080408030402011b030206040b06031b060d0603120e040c110a061505210706021606030519020f0d15 75
    0x41b0b004580031b849800c051040140001b610035000740c04440c800ca41c800741c3c45030405880c1d4600d4040404000c01c00b400703149400004140c1100c0d00a0311401380030000c0003002c3c0e05602d0b500300514404005d1528080043c24000020080ca0008145035030503002014a500c50b421300200740e0700248a40c0400130f104040d6009101d2241d00010100d03002070700401203698a5540780016500081c81800c4c0f502c6a43e10520894141680401d003d4020380c8100606102c5840300c40030160b482810300c480703291040401e41443d1451401400800400d50000c1d00800c1c2d156403078444003040500302d0101d1010400006284005151600c1038000c2c10000b401d00a039a1042d00100d0b40e40e071841e2090003400d00d50b030792401100300681044084000d1400400750003601c482c106074188a901d221007001100e20070380d00c022601d03e0011070781c02c00d401808240040d426141c26011005032034003400c10100344409101400510203a80014400035036402401c640c2e80c0d100c550031004991070900e000c00c60311003082e0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 309522517 1250 309521267 309521269
    0x9021c110a0c030e040204030f120201060b041430062d010e1b03011e0803070201020607080a060302040507091502070506090d0503130e0f0a09051c020c0306010f080c01050405 77
    0x40700515014505884c001445502041c000e00c00c0350005012444602c007448200135020f681c1c07500d102315a5000b40041c03036032503d180744207000324021003403002d0b001c1e003d141079410901d040300c030400c04c0c00c205803000c4040c0b001352600b096584a98510325411020411110480484404038075004200079203410a2096140c2c40f0400f20602400d100501039602003054112200d2001040071400802c1c1f43e603039651760140f15859042020300c81c3c2c44904103078000030000e10110645040c190107070090100340e40d0b8440d0489400354000c05044185076204c0021000d61110312802c1c1c41500c1c03c0c0c40340c00050f410444c05091203081407114108540c0408028046616514140c0e600c10005035080401c1d4041440c00d641540242c036052a0b84814400c00080d00c200e100003041d000d4076100081c45042d4440641c402c00352003280384003802c02ea00c201040c1d0340e650a40b00080380410703050f10503204822f510700b0001c1c2c00c011080e4001509101080e0f01403055810902c040b2030304000c01d0904501d031902e480 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 309523767 1250 309522517 309522527
    0x5040234020a141206010602070504060918060902060d0e030301061407030207060503090a061802100906050f0304020a0b0a03090b1303020705060d02120702010e070e070509150409021c110a 83
    0x10280c040d840e03c03031403002800f82e284c440031800030104000980b40c00c1e40c2c4803c0c3c02550f0329460b101d69842281450400265644140708420300c000c98001d840180c0d044c10b840e110061b00349002c080340c00040401146070551164403560390a504150040e40c7d90754035102008140c0e500703100c200d0b420404200000d00000c0d80010710901103410f40c0c00e180ea16541c8000c80c143c141210b0020107082d0908007001038a080d0b61701102d5202d40b51007107552103944040014200c4004c400c9000d0003000c14400c01c2050079441c004405940d10901c001c01c0e003004c10f0380302c480300700b000d4010f4080c0f0400b080d1189505010403080403003099000c409803000c4900541e5980300203640c0d0b401841030600500c0d0009a010f180c3d840354040304c008050a90403080346082c1704000030700802c0c1c00051500507002d40d050102d01145550480c60095a0030303030304c0c5410900745800700040e40e10551051a49172034100000a80c641c1d250020744440e80c810080746032080700c0240c0900c10f4800560780d83d26024070400100e01019045 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 309525017 1250 309523767 309523769
    0xa172106010e0427020310150e0a0504050303011403070308070f020405061504030813080601270b061b0a052a0d0807032006250305070f0e0a05040234020a 68
    0x1d02240007903203824004a410414038400568940e4101142801d002305166180802c85201190070426552500b0900f4221601910020129001080100b01c10807100c8041c40702d45070b000b002c5d94090359a03580e48107041d074040b09040b60305070a08410a429480c4c2480b0f0317280d00c02000c1d10318003070000c800080b10080d0310079400010080c585c0859060001903c03062040082c0401c00c0440d8019611040340d0b59402c00c61038503503170003507400d690751040d900fa45004054106001519203030810f900d82c40c1880340c3c4c108051002c4580d00c1100401e00c08250b0802851400f0040201c540d059104a407500401400e0005003580c002c6480002020004070301404a40340c040c0c1509c0e02034110001390300d0220000c0405d00481210b8881ca200340881e44d00e030b8000424101da0030302080c15a441c1c0585055050341c00c21102034020a5a1039805c1050034024608451104002048000000e480e040020700b01d802010f20503850401c580380e00d03010b040c0092043d00035848030500704401000300394001600070040d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 309526267 1250 309525017 309525071
    0x80d140306060d09021c02130b0904110102030d15050a0b0301150507020d0b09011508010b0306012303010504050703030e0d0b130c032108180a172106010e04 69
    0x7001803201e403c00300943c0711405145d402488400d11841c0c10358031300000c0c01d80d80010b9100d40307503100d46101448120b22481420b0f00340585008402d0351103881f0042e030b074140ca00300c0e207040d130008201d0942000900d00c5140343c0030062403c01c0d050b0608080a000010517950452220ba00c0c00300300500c42d038100c40c100b00c078412b25107103807030b907510001032000c0340000709917010040c0f9500c080418008402010740020076076401c218800386485136915021400c1c0d03142d1a0459030580c21200050001c90001c0c00c0e80c0084070480354102c10a4040d01c0086802c449085a0595a54012074024401c1550000302c105807054102d0302213400340690b4035440440f41025255008481d000103204c01000180092030340103540001126019840800c00300d06040810800000042d00c9100014070100c240b03d54030700600c039560003e1650302d085603036241603000480ea080c0401801032020029070f0300c0b0411600114040c8604241c2d490400134009480119001e542c14450350810316807210001614110062440e0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 309527517 1250 309526267 309526279
    0x1e051305090403051902010b0f060403030c020f190e060a080105060a0603020721031406060408030a0309020307050a0303050406020c04020a1b0c0f090b01270302012610080d140306 79
    0x2c07035107420346181c0f14403004942c07024154854448180e0b01980f003008003007400ea45005400513106d003006103921441c00300030b02080b10b01203203a0240c1000a40d900e441e400140114159414040c1c80c00080240b59101050700914041009a98184013400c4d00c0140703e072000901581c204000003408107041d82c010700c01059408120b0405100f24402214620000c07000b021080211000000b0302601542403d850800c42c00d101080240c00c045040302d003280c0d0480d0103141041040b000031030107840c210906a0781752081207008500780e40e42d28140e0008600c2500d40642e0b403890208081e04200e51330014a204510501450361059040b4101200490b6a0109040600510320f007204203085140c100030702c0c80105003c080b070503002541c400c00b003078502600c500c400440000407168802585442038810300703e14050030801540150526961106104e10700328818120011200000b24222404040044900c0b0108076400080c0122080c0154502d02480c441c2c810800030b120350308c0080e0209005107 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 309528767 1250 309527517 309527521
    0x9041b1407030309170d0c08060f0111010b18040b0907030b011715040503040f1a0d090f1209060905180f09011d0a0b07051206040902150a1e05130509 66
    0x984203901046040d940300c00e110020000b90045c041c0c868200545100e5103d1800076100c8406025a2803c0c0c8030b00d400925841c030201da034400451304c1c0044816070107625921241c214900c0d0343c07401945140b01e81d150030b400c507152400d07003059444040c0181115411f904100c6052010480c00560241924810307504240c522491505075454030b09616103480d02d40b0180001d002c2003000100003801100c4a440e80242c00607114500e0340340b06030040542040c008001c1152041802e901c3d0011a011400ba00090700c02c142d07a0380381c2d44e0361030a02003043c40006034070480501c4010f8000883c0c0003c0c0c60213480c0c07a00002841d21510010300c41c05811144880b001d03000084c40140c0c25040f0104151080315120311001c0c3d40d20b00141e507111546030864410720f031000000d038100d00c50780581340e034106956507540c0c0646410342031000801c5450801d0b40c102e007205600c0d030a0906244010030b094072180c1d41d0080d258201c1c031448a21201415090402c110741045081d03062001000c090b000d035401221541c40d65 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 309530017 1250 309528767 309528773
    0xf0b0d0203130b13051b01020c04180506040311010515011209050f0307031713080a0c060b0a03050f010c11030403062c030a0e0d0b0f150604080309041b1407 69
    0xc01c445540100b0301c0c0f00301c00c1081000c00b020364001d42224490800c031040c2d840c0a1641010010031103500310b00507800b1100e00c1c802460180c0000400d40b0381c141301c440d04035900e5101c05042c030300100c0c0d040e40410b04802c4c0200c80100c09105031940940c91100d1001100702c0c4000003896203034040c1d0000d13080d94540e444401401018801d803103a202c2c645080303070783c0ca00c424980070301042c6d010880902014860030026403100501500d400e9680c1e80505100d01c0e1402031401950b1729544000155008c9607192a011a65256005541d010310b0155000b4903200510013046420754010143e224100401c104019114800c00000e51b4103582e4002404900c0083c1c00c094480844403000c10060004003e09410580c1d21010000700001f400f1070381e55501480840b014401c44192510000b0202d9082c0700c0052207180140c410190007000852261562041520001c3d9240e00180c10180340785d08005081c4000f0701d071902c9000b010039200007001d0b00007160300201401880401e02c0600300c3c0b420000d8130200f0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 309531267 1250 309530017 309530041
    0x9010608030d09020307090501050307030b0408040905010f05120c091303051e1b030906040e0a02070c06030203270303060f010c05010612020f01170601030b030115030605040b010f0b0d0203 83
    0x2512030101100d49401d00340221801a0071000026402809180c401080c6c003030300c6006580c181c0d90054000c0500c00d245689100005c0300c018800c1d40c0304c2d10140001f044025a6024140c0203101243d81c061240b801c000c100484200d04c1940110140c0c00300e80c5d00e24990f110429016440389040320500514551414160f420f8840d05510b01410818005568045090100600412004004040c1c000210780e00072503a02d10440503d140c1c0544184402c0112200c1c2c02d40e03803a400824040094180311481d980c034a28240f66400c08008207402000300306010315140f40705480c4c01c1000482041054115046030b8403848080d2050313004841d91744c403940040e402800040c00313a5601030000c0010903914010b11712424404c01d8120320035507481060070072941c49104040c80e82625010701c0da07041d4540c20010340c0113100f000802034055488403807103801c0300b4008a07500021070040e01d01144618092801e086d04503c142c0000d031001090002c00d10001c0b00190a46443e4410300f000113950b03850305610807030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 309532374 1107 309531267 309531269
    0x61305061006020a0213060b031014030a030e040902150301080a0c1505030a09140a0501060905010f08070902030606040f030503090f24030408070507080d092408090106 74
    0x761404030103615006c1d014410020b40c459490f070860403580c00488101240880a141c10807501542e51200031170b804044001c0e0101c5811039038050220700c03010360142d0282c4d9580c1c0b0743c2c00864907400150100c4000d500c42c56034403927949100c90303035541c1141d000480306019028800111708036002c1c0c5c0a0142100c0c1e84a45040d03544034540320004000340c0c882615840540c41444200c00014030014040c0c50180300040354050401c00580241c400c180c0c000b0320983c12840742006454004280001074944e84000540c0d42c2e1508000940c081c01142c00c0240d250645800000410030000010300100d00103031000c9006d100d600e010802c0c0ca040301c40041d8032025584140c0394010a401c0c0040d5401440b580c1e010342801c105d900c5a61a204075034000e800640d200750001002c0a4000650b0f500900e0066603503d58a4400894015501c0c0781803100028040100085854034100f904018 = true := by decide +kernel

theorem cover : BRFrame.Cov 309352517 309532374 := by
  have h0 := BRFrame.cov_init 309352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 309352517 ≤ n) (h2 : n < 309532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
