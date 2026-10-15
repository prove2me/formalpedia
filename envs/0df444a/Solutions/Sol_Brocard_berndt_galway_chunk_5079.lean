-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5079
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:40:20.489722+00:00
-- url     : https://prove2.me/submissions/8d44719a-3555-4bf3-8dd9-a9fb8d78d78b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 913309352 ≤ n < 913489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 913310602 1250 913309352 913309387
    0xa08070215030c030f100f080a1208070903141c0305090f06091f060e010f0e090705010f1b060617060a0506010f1404050a06030203010e060f0306062103 67
    0x300d000792880c510520240c400402070780c3c032442c0340303400305072650f0f582c10711004440000034450600d00e4131380c040124001004542c14405000c0c400c000781450000c60803d01103900300c10442e0030820403ea02000101540b080b2040122903000c0b0340c402c40c0b0305003503000c02e0404043d90703044808940c4620b80c054081e589500310600a41e9554140d647c0c08041d281c0098440030210345004055011650a00802440480454006480120014400340c45a2102c0e14818003070b4404841090f03240b00510004004c1610241c10490a40c01007084900d0007001800101c401d9020400f4030002080880d1031500000c1c0000b0340a601040030041c540e00c03420441c1c40e4150101c090800c41c820f45000a81070141740c030a0078050342d016101c040d003444140008440116031761109204103401880001500c1d143c10718100c000c0d040d143c40250700ca42c18507400e8000c08030010649841001503141d4110552004a00150896420b441025031050341c45804900d00d240c030081a902403000041c01b400c40051000e1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 913311852 1250 913310602 913310617
    0xb160516090b010207060219080702090a0b0108010906080c010f05120c0d0b010305100326190e06070c061211070b0a0c110c060711060d0603050c03030c060c0702010c050a08 76
    0x1c0c20030520114100490307844580c0d008000151740140700d00c04c02c1d022810240c20b09948a010051328055055022800c2103206690031a0001d4540790b00c0e00c000c0d0b802003841405850100c104102c01c91400340c6c01c90f61480e0303c10800703040c40386110110115501c0307402143c5c4404c10070342c608512030034111401e00f000d52000e600d4203102d92030030466814035231090003124002d0420000001a050a540742d444000502c102c07030454450a42c90051100c0c0c004c000549078140261030f02c075206c04a40d0740301901c102001c002451141100300501000910340b5a5000292006840c00031707041030700b411480c4001c00380c00c00d03000c040000105203207041200d4042041e10446c000502440342c10b481220981e0781402e80901440303a40c01106045241c2d081240c0034152441c0568a01e100291000d004030310180c0c0b000081400c000c0c4c490304c0a00503c4400c116800080380300f60025407901613a01501c980b0307100040d00100300b4840004090040d60710902482e8555500a070070395000001e1882c0c000032950020702d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 913313102 1250 913311852 913311869
    0xb0a0b22061401090911090a17010c09050607151508031e030103050304120f0609050d1403061c05030d0c090608010515030402060d0e0313091508070b160516 69
    0x41001c19220000020000303002c07410f859148010307040441c0800600402c04044504003001c1c404254155600b050400060400030303850900c01c45000702c51030030344412681d0b00043c4444000c1c204800c0d1181e40486003a01e4000f5a080b2032180c40d28001030280c551000811000340245401090720100400200000c410b40b20054901c0c0000c410503501d180003d10028110f60000d110030803d83c81d07003040310b0a48501c82c00200ca00020300c0d94411045500700c100a0724030390300c281c60400c4072a403c40e011030807051000451a055240101c000350707480140c1c42c14940c0c070b444841c0031202042000c00580b07542c809498800e1105014042000380411060711541c4002100c0c2c00c000079480c2000341d92214a41004000a4955540d039000d0180a5001181440c02d41740e403056019800b040501c0034142e100d00c284201c981035032a103407024003500d01441114003c130304003500401080000288500840b20141c815076103401c000010400340c00e000140190850007a080000c030b00241340b42000c001e6a2440 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 913314352 1250 913313102 913313111
    0x6010b130e04032f2e0501030b150a1802070519031d01020a050f01020408010b09060f0f21211c180f0b01050a0e04050a0b0a0b22 57
    0x300d00940380741800750780290104124195010030310980d10042100c21039040340c4c0e898140000052070385000d103414207200302d070b44420709007030703990400505c4600c0c101c3d000107828031031541581c44070219820b000c0c040341c00902d00b144036040c1d00d888240303030700004141d96031034809040407081b03002002e58899035040341c20380a243d03005000c5e0000d0016401b0901d81683c0d0f15100383c0c2400203065814200c84600741d040d031042c02e91003c0000c204004900d403e801c1040050385903403611040c2402d4902080200f0310803009901002000d03224034544050b59402181c0f548408050300000c01c5102540c030483d40b00040911841013140d0f41d00050b15406103002d52a13203403200000700e680c940307240590805d185080b03e4550500c4140b032900d41000c103100300c0310258081c03c0d00c4696140c0c1c0601c003204204940031024040104114604038444e540101000d041c0f11601d840c00d036607007913207440170724000610540103800400c44030342d100e0340009002c1c200a490701c43e00b2008400700014414a04081c5615581030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 913315602 1250 913314352 913314359
    0x210501120b0115021c0903080c070e01080712061109091005130203040203030a030e1c1106162102090616150e15090f030a081504021c0b1206010b13 65
    0x182d040c0f81c641c81e48075a019122111040c481c030014603201182201c10006441e90120200d0607a000600781000d54074014210305283c60040311401405a0200d58140c00032a020000d102d403000400719150351000c000102a46c1c1d010f402000c0340101d00702c03160054104020000e000404205603000d89000700d030207070320202201e4461801c1c3d1100b1136000b505a0010320a950000b4001d400c07a04044c8041d03420388500d860546030000c4c03101183c401420025501401011400c05c0034000d03140c0201c07240d0311241070f4091145000d040c004035080c2c0201c0341c03a00c0603114030101c0d10380d50640d140b03110002d040681d5101000e055006144021f0001c2d541d0300c1801400c0780c0d05200340d110b00c010100041c000307450150614400f2407001080206002020f0060604040b0300180034001080e9407071140c3c554103040d041049142c040c0c486c8212401e805148100160399203045000060112489000300104180c00e0000100d070500000760405011440b41000118240300e0340e20141103501e4070f00000101803541c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 913316852 1250 913315602 913315619
    0x5060108060106090306050a09172107080c1602040219120b100c0f06020705160f0b03061e1201050a0e06040210050c0f070f03230607210501120b01 65
    0xd00f8400e0901140d10b0790802c100089040d007001b5032001241000252903a01d5440d1460000280b0020840351003001800500900081c51918000c8044244003601e510344010058015003028107038080380c031f4021400c4000e441400c540c10100b20b5020344155110801610401080000603042401007100301b42c00034104800c40c0700309508004014250f0400785000041907807454014607040d10025030864000010404900040842034800c6008100000003865010b0301c3c0301c02e9401c00c0e100d154103c00108003003244001680c1d0808422986400e8100c158100840080009040c098022404408506e91201c0c19806640b1501c819681400700018400e041c640baa603085800a600c40340b205184407000317216101401000c803850049070600a942d40680b86402d603151301540e8103c008180a10070010800c00c440003103079581c1c070403041101e00e040c0c80b2510303128002c0c4a2020490404184007030303840c05200f1001c4609a440040240c3d5848820600700b511403687c003510300741e104800000780f904 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 913318102 1250 913316852 913316863
    0x2a0402090d0201050d060b030f070e010f020601060815040903080601090803070b0c07030e15030603010f09031707051e07050f03040b030a0203040609081b010b01020c0a06081801090f05060108 84
    0x88010700c818290307240d69005403402d412050340d06000720383d15103003c1295032488000314010040410915a2464101401030190800c180c64604101a1a080d100c800381c00140c82819038070681442d44443e590748101c21510b40100c0160b80c0d0150504007900207240e04855064041c031800e90f21505420f031150b054940d01e00c80c07140c00134482d10790310700045c1841c0d000101030401070380b01b07240ca68803c1852100003002c1120540035480d80820000a0040628007480f807c1e8030001050f400f4802c0e11410740303024080400404094428484440010345034900c00d4044070461904010301000421007070704441d1140e00508406c0320305208000507000e54400000c01ea60444028406042c1345907201913104000c0c1d00081d008079100c03030b203540c0e414001495000c003804082590582c0005d010951211403401c1d100d4074140c085c1035410212017185207445000c0403000b51612414694500d8991030084600c41d190703000c8450165190250840400c0380c03001c02071000900603070840703030a40d0701e401e003054685 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 913319352 1250 913318102 913318117
    0x6090317011a0703050f070501060f180b0d020607060b0303210f0c04150207150309060f1104050609241c0506030a03112508010f021c0e0a052a0402 65
    0x3850038440500005c0c800c100a2501a00500c0100e08009035580d410b400c2d141c40303801680d40491113a000340900c000c0404145d001e9408400280004910040490f500c00039800003c2c0c042d840010381d55003031000980007003141c2e50000c0c003104c3c4c0c1c503001d1044425002c03c0080140c04100c4025001c255200780007001c01c1d00591180440d00c1c40c2c10700d0032003a040030305518101031055010b4440001040301c000025801d20900e19140821007018a1804404540c10b0310701664405140008038004240000151000e6800540b80c2e15940c159070340000360440d0028458000c1403c0120146506c140c0700c0000e03020800508041010070303041c550610003650002c42d42039030958041b00c0c80c3c0b00803031310503150b150780078041906071003041a00d0307080c411041303200004008141e18091001c0080308401d100c2c050400c501002e045003030000c8a4000746c03144170700c0d1080f1440b83d074a4990440116006012403008990700034112405509890030800344440490004401181900038001044c00c02d40200d071041c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 913320602 1250 913319352 913319399
    0x70c083301051c0609060614041a011409060408070e1008060f280516030b0d110a051c050c09040b060d11040903020c0301240e0a02070609031701 64
    0x303682c01c200a100803d002600c0f55407503d0024400880440d02c103105405440d4000c00303010071594144440c1c81030b640106965540a145448003004080e0380c0d441c13044050000900c1c002011001d010300848140c01a5051958400000540007603402070004030902155515a0062115500c140d1484245000313031050070b440d03400560004a02507410341c292588004911120440c00f043c044441410b4035000c10b0781180c0581d90020f201400c422000542c0c0951102d181c10700a0785021004109016100034000f490b011045205201031303903648010001030724028002803201c803204402000003000c942e209035035601400b0000c542a0404907059849580c1002280602d41c603510144801003401250503140242d000c1058103040d540d900800f5019400b270360040c86002c8c0000b0405003111901c0c0ca000006c0104030900c0124040d8030300311481283d00003411100d255803841c501e50301910403007400405c21440c0151544c200754104c0780e0305441d5400390302c082c0c4081c1c0e202c0c22102c40300d40c0d01e2000f00f540c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 913321852 1250 913320602 913320703
    0x40914130b01060f17131401020a02030d021309020c1011190e04090203011a19120f060b04021c051b0322050a0305070b0a020a1d030102070c08 63
    0x603401100115824041440c1c0002d40c1107864000c9810114283c4140044003041e07046e5000340714100c1c80f80201d4a00d00f000851a0070782d5214041e54034801d040405040710340210703004040301c08001c000710003000326900070b560b202c64410201d515280000d61543c003a81c5040c0042424154400c150f500f900c4031400280c0e00e0300300c0f0075030945a00d0503411b0880d50140e101c48003807006840030b01614510100c204100c01d41d01000e50704010100780851a110228454040304006117241d503001c5412054000705071048c1c401c200c0c01e03c0006803101420f0181c00078000180c00c950301d60032500c0424a154000c100b041240c075090740c005c0c01450203050340b1040280600103d0102074a4400030341d11407031416044640d442095464a0801404180907000304501103a200c0511115900081e404030341080e0443c90f00c50a0400500072640590309610b0350041e1003a84205600c1c254121a1100d4100781c0500134156500001d5541e90305114100f030341483d00a01c21a15000e02e895954000c400d549507004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 913323102 1250 913321852 913321859
    0x1306030b0703021b011104080c012d0504090203010e07090806160302160b0f0f1807060c06060b0c0a0606050102070b030c03100527160c030e060f040914130b01 70
    0x18065001080c20180c2908240d1002d80044d20901c1007031055243c29040390340391494111800e041414074040c040c10b201c100800d40130b2440428076007a4102140e2485851091086500bc03905805144c01000e6054400800440c5a521085078a8031070a034944d41d6a0035540c540c0c1010b52105d0042d1098006105051140113840e03000343c000e4050b2144040c005007202c0f1a6466212901c1c0e400e5800485000c0d210050046881e541c11820794000b050150024884808125480c1d880040e841400100504003006404006c0140c01c1407004004011189031a6a10702c41d40b2521841050402c6481c80d24100000a0130750002c40d604d01184e18981160742141d48040350420030b644014007948040124913404500d60791342004480341c0f4200d8a201d49845c0b45028402080410041d00c4400c68100b60041084119802814090b00c141e01d481c00d00490b504e60341c0860701c1805545480c5089150100d80070030783d0300715035014202d54420071081c0e41840e21601c290140c0000005805007010b0003080050 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 913324352 1250 913323102 913323107
    0x7020a0807052e0e04180807110a030305190314070e030d0e0312070f02060307181406090105070303060317250c170c0418021f0207050f060c03181306030b07 69
    0x43e03e0315007003d0004a04c080341c1d00742d09801b680c030104048500700000b00c0d841d0180300706e15141071260702d0103998107100503055071000b1704075001d4050400d40394102e01c541980b03030a20940103413aa2446804040560342040b4402070002001012428040d20840c40744c110501d11480400c600104068041c1044881210202802c2d80c0480c0043d41c00b004014040c10058803071a0080d0300c5410340740d41e41075522181d0a0b41010003a0720b580041600216600301400c659102021903d43c1b42e4242005903444595107025400791900380c0c000703040c0b0211040030f0140f45810b48010000c0c10032000c640e0000e280000780201c04080305107005099003454950601203211544002003904180000300d42182c1c0e48140040c00390b414003a0980c0c88042040030110031400c180301d07148905070b400d446402c0651400e02c070003581e42d006840350301e00c00c40d00040040b889445880489807800d051400752660b580449074007010b02e000341005107009800c01188980783d802e00d031081c2c1d8140e0358441c203440706d41d4450f01e004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 913325602 1250 913324352 913324367
    0x30c0a090b0409140907050a150207080d021c050f030601080a0b09150118440c040b0607170901050702030f151b1e0d090c050a0512060f0c07020a0807052e 68
    0x49c1020751051620110306110300f002031070015600303580142000e001c0d04411000100c0394100e45010311005220300003112038003905480e4401004e03e0316100a54540354a4409020785540d1140c2041238081400076450a100302c51200c0720080e200c075640d0311804044005980800c1c4901c03401da00050301040a14141c491122445920342803030032075440780110001c0f00d1402016400d031003076444100c011240d814036010b155003850044540500b054010703190981b1700310800031810600000026000c24581c040c0050300c043c16009012124608481e00705581d1360728094111080b618805030000d0f003000084110340c0c4004488400342420140c2000301c01c6503903107444a6440d18a8000c0c408002c024103244101200d00e405081110f01746032420f0140050110725801a502841050b80c400880a01c006040c035000700e040448403039196110039002126010381c8100035808400a0340002e00461b000480c0025903c0868480210070914520703411030000d44803e00c490303548121290b03000180141007 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 913326852 1250 913325602 913325639
    0xc03060a0f02090a1517090607200a0803010503120301030f0602160b1905010609050a272c1603030c03270608011703030c0a090b0409140907050a 64
    0x4000d03040c890b00c1d40c001082040c13203402c1642d01011803001c031441e680e4030102c48100c0c08112140740540381484612130783caa5100900c000c080c010748042c50664a0f07554074070b40d1002884001031714080001d91500d26400da0083c81800d21034452010b4200e28407003c04116412030b603201d40000c1c1c00d00990b82d00ca9001c0c0d0030046200e04c80309040d4044101051481d016244110310032401d40c1d108028840c1850120f8406810030740401240e08414003c0b506d0f5150100d094460012080c400a03501500041201403620b00b42240c0c2ca06211071003440c0c040e10003442401d480d400f01540c100c0c01900002030b5a07400d0781ca550700d405402c860b0040021030b0082e032081c0103082c080d213032461340c0418800c00402c040070444651910796010701e004100356980240e9203405080480039403181c000d40215002e80e60300018007100340110b00013810410f01030007400c1c1000100034007540c05444681d15820180200304c00803a03000e200604200003003009030041140000d8820042841103441c0c103002c11911408103500 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 913328102 1250 913326852 913326881
    0x140a030c111501121a1501030c09150c0503040902160b15010c141005040b010501180812030c0417030d0501060c02180a0e0703210f05040e0a0b10120605030c03060a 72
    0x80c5d14105010804010740300e8215070800c18090001d120005085420303142c403210030809080340500c032007041c0e00c58455440030145840c40910109060580c00c41c4529802850524400221000c614948090400b1100d010300031004d581d54500704200329420f880f94503e40000c4071010120300040c01024140d8059500e2800c03030307019110401454044800c15601613402c003a42100402080d81d0000401000c0590f1107a80141d0915183c04190b1b20600c3c101d4074401001c0110000f002103449605035002000c00c10700f0401c2c1c850f890b101060f00c03680030b5030184127162305040020440c1d034007136074000020980c040c2036108040d2a81c3e03400a88400e004e4203521802e81ca600c129254110200004030145014581d108030b6020007400075048910140c14035024000b0104c07440303040c00c0c1c11006440807074010901644065550f1042d1078000c00c9405001c036032040340320341040d03000341d031000102d540b01601c0a010445162100c1c105940c4090203107099034036521181c0000c02c0b910858000d103c1928406 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 913329352 1250 913328102 913328123
    0x20f0712030504091a030d03110f0912060a06140409110904060f0f0209040614061602010e04090305090f19030f06020f03090f0c1903030c0201140a030c11150112 71
    0x14140303041a20054004009800380e64510640145414821178103440c030a400c0c104010802e0106800391400ad102e82d43e0080e01000c0b079840010b0b15098031203991010280c1c02d03501e42d40707050b1038104000c0589008913400640c40303c1802025003498800c5000064000c3c40200803014400100034100d44008d208441c0142c4411084500c0561801404c0805980c4c100250b19142c07240180421101164031030307403141d130f020340c24800c441d11124101c1e83d401c010840101c81704111800180c40100c0c54002e00c0350404e180c065807106059102c0007038140c0f0441280c041d9015403c080410180f11040f58407000840d13030036001000007030395100c00444554030864000d41441c0710043d80580f141c00c1150000900e801000240081040a0001e441c400c54210740c6d21080003820250840d0116881c0002010312005c0a040b60643e80120301c0a545d2340b101c110055503550302070030001c010b00011200303000818842500d85022201c08148907a056010b12954006a13180059040072260500ba064603c201e60 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 913330602 1250 913329352 913329359
    0x6090c1b063206060306090c160f0c0602010e0a0b01090f060b190807081302010e0d020a0f14030312072303130c0b030933180d020f0712030504 63
    0xe1a21036541d203840100b0304802120110910015510040c26039100310b10810402800b9034501403c1904604817080e006d0b16130070490690140340020600c040d02e02c05000c011031080201107440c480a80307080d58001d10035000d040414a40c0c540b503070280113081441d04030040c0074071515903000e082e60103010017011076503540e02c02100c4420342c00fa0183c4410051400c95054a15800c450940d4115402e494150010701e0030707030240c100351080000024100000e83c10810303031903501c40d804040002d400a0018110079507825048a1018403171040040f51105001c0320081480d0100c00da03443c1c040340c0f0b8142515542c0d00801294800303549444c8034203040c44c0f075070150103400f40700c0c002c0d40c41210480035091510400781407104584240c1d6110510000d020804c20004080104c0d041c4440b10781040c4002902004410b10f0f91901c15240007007030385640c40000c101c020504c00d45044040860703041558107a0004040890300c2d00c0301c01d5815681503000200030040c00e0010041c02c86454001d1030030900b0181c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 913331852 1250 913330602 913330631
    0x4060806060f121f0515090103031e0e04181716021207030b070509090112080a140c012d091a1e011806060f0f120b121006090c1b06 58
    0x119001320140036580d0710200706071329884802d000c011800840e220348044d0300d503580082c14020440ca0b00e00c032042c80302c03802d0802d603030207060410004e0030010418013600c0050300701030a0000f0090740a40e2201030b660311081c400792a00782180c81d0340005200328002400a40c0030302c541180c0100c00c990310741c4521080040803038405040c1074001e40b429661304d50b0303441c080d4080148069041e080400055501c00214000558050031910f50f0211803c003c50310124880c0151031a002d210012409542010303810003010101c0641c5a601c510f9107555100b200200304c07070020454502110050202c2c08092001160607800d85405a22250340b248900c14112441000b01c0040001e81c02030f504c0100b4181503010034a60360194102a0090303140101c03242c0341000004045240b00b22520051003240c05002070311450701e41224032103810181c43c1c0081d80010030541036607402c1d00c81501401c146040c00126003c503450160001c0c102c1103513164494400d0030316240040c07040380c0e50700704e507403598500e40908a0310 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 913333102 1250 913331852 913331893
    0x30b0c0d050414061e0f073609020f030708040f020d0b04030806010201090305090d1b1d0c04080307020f06090a06080105010f08010f260a060b04060806060f12 70
    0x24801c070082201415920059484e04d00042c1009820301c4001030140c0402d0301036165554800c10659444031582c40d994402d559440742c0728100c145440e00c80341408403d0302c841190414841c005032840402942d1100704000b280280d9030003030380142e410800300380151b2242c4a029080340c010101d00811840750b44c0010005c03150300c01c08440035910801040103141d0013192060340807200380028030046030590b80041c130521070b180040307106806801002081c400104043c031800d038a4480030070001c58030b0f2001c00c00f01e40c40100340301c0c09044009002611100100040d5070803541d5001c02142084d130907500304924203203d02525a000401408146420b959042000f070082409e40c9800c181c0d541044001002030420b02d61440901c022200100003d500300d6805d0011201e42e420442c20501d10081056800d10b41d00312407110500c075603204c0741e00740070543d44440328403001183d00300302c400d580d441d01d95120300341210480c0e80329120100d0030301c1c503090060961043e0f910b100107071410607591005458400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 913334352 1250 913333102 913333111
    0x9090309120506100e1302120f030711031c1b060207050a0b190e21040f0e0a150501020604020d02031207240908040902280c1506060504030b0c0d05 65
    0x83e0300c00300c28442400c40000100010b45205144085545041e4110a000d050080c5009010316010140603083e828103205100305213031b9083c1629030304c0d0340c68109400d00f100b01240d0140309001c5d6000401c403c0c0b00007054000e25500d00d44800c0d48211f61005640400001c1c104180e961031b8080000ea400220148480d0080781c3c8101860001410316100d040f5040301c00c0b0160007001494580402c0040400240c0700d401e03e880c80d5041e1000405a1804132114000c940c0141c0b1580320174a004a40010501907152042c00c2c141000c01a04580da0150003031b281c0e6510510380560081404a000740c01c006508101d241e0000d8121041d04039240c00f195031580c0115030a40307004e0300c07410000001c3d55221071300000c00e42c0c1c00c081c2071003c81c1d03d648410403244610f11802000550004400f010507040c1c4031081050845080180d00c18042003801604483c1c0301c000440e644072100e04604100d04c01403003070100742c82e1071f075680350300b06400c59480d440404009021070320484001c3c440c003040194603002c3c442c4603 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 913335602 1250 913334352 913334363
    0x240702101d0c190b0c030918010305100207030e06090117071706030c0102190c120b01080105100e07030c02030d060906031202010506030c0103020306040b0315010f09090503040909030912 82
    0xe20030002416401e000382056068071410040c3c032030b4400180311400c000d003600c80301079880e540c0b9202c117004249540300d4501d10780e82280d10b03100318100c040c82c20440c140c101c82c0a441a41c204034114000141244120203004012035000c1005501074182030300500a51001030500c0c411803080c003c00249210011181440080c0910b0112440b40704c440b0b003100d400040540051500b68001e5001070340310501c9611a443c01060500c5c03800503c011611888010aa6504444000070b032a040546110009014421540d030805011035505001e43d09010200c48001440c0402603c2e406401c401410004002e01c0071032000307200d45540f03a041803282d040104818800040d00038a5868801c9114002078440400d5914050401401d6200401c01c004e03050024a001680d030382d1160006401005034600c0c0c1501403098100d07400000ea684c0b001d8034103885110340d01e41c1e011a520f1080b00199100c440c03004205800130b0104000c40105a0441c84189103c1d092144103a903c8828240c07047c501e005056a0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 913336852 1250 913335602 913335641
    0xb07020627121b0f06160f0b0a0605090711070302060c0f060a2a0210092301150909020303040308030703021909030b15061b01020409110c0d0224070210 67
    0x1820040c000c0383e101801015039503900403402c8000011391a015107802501c803582c030058602d04201c008846000130320391013180e440070342c201402200010101c03405524080d01458000c11086401601c003c4041c110788001491254110b83c01d00c6520f8110368040112403013190040c0c85c070510705108640c0309103910100019291071070b0744100803008003182c2c2c940d1002010940c0d0752852384e01240d05515807841c070b600801c80601c07a1a001c020b580110f003a4541036000714107074145100042d00450802c2504072441e042603912402d81c9011641c008200030f40c1a48100001c10008003407001550b480b10041c00d0050905011a124040b4541d240b1400d01c0000c190350340078410013455503000c1c1d030406500114841c0002e0b4020200e01e10340b244034181c082160449180c004502c800750100c4004d0046d40c0d40c14046520040d002481c1da400104109809000d229841c213156880000c00301200705103504050851484040b031090440c0c0c001d8500b00460007120503c9031105003d02408070800c0c1c03a03d03107604 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 913338102 1250 913336852 913336873
    0xf0705013b031c210e100903090302090a150b03070203072009010e090609150402040914031606060927030c08031305011506020c01030b04090b090c0a0b0702062712 72
    0x4d04109202000130750492805172800500b00d00042c880c4110100d213840062202c204d4142654003a009170b00095002070a10204100402e16401c500e0310014940444544581c5905120191340800c440e00d100682c003e100850100d400d41c0a0349107611082400561030f441c600000c120144003d030000324a0404400c00d004008408004491384241e52801810082c4403081c010f100000300580041c0c451034680442d4070a00411222050302c2c010711b001202d40d40e42c100c45100304645064102035800526042001408840500030703520445504810840c03613501040d00c015991f02015810340030800020403800c00251003000840c003419040518510500c0b15190603400e541e503c8900700e45803510311800b00809900010040d0512000b420045100004000420010055208050038806485080c030130002804200030241d90b80941c0c100c42c0076030b1104011852740c4221440290007002c00c2011b905c150150200b890b40000d041c48410b21740081d04400114102c0f1301130755200c90350300082c0707114 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 913339352 1250 913338102 913338137
    0xd02070b0103140304050d03080a020d0e0c0f0301091101110f0d0201020d0c020a050723090c072f0603040f020405100905070903020607110301020c0f0705013b031c 72
    0x907140f00450021803615082501107200c24030700c050000c0c1070201c00b20120b42c5030301003601625046804040108240030070078440550394a00300c00d2007405a900f98450384040e04060013030800d041e801080c07441d14400385d00011201d1081e0060920814080e10030300303601881c0b040c0135501150130542d00258070795694030203010444a044c0b41c204e01f994000520340c00003480200e0800121a5a54484500d0600040d42d0310410108242210ba0040c4c101c0100486460341801619800740150800300f4904078a805484002d0001d00e40041e0544170402074120314a0204000d59010f80b00d1100f0700f94041442c2e000c20107454090b1490107040c1c55441c01808684468400d05a001e030083c540420303041c0c41e50700840d1851084400140c0030401d0b07040801c081c0d85094040760301c03111000007107031001c086c0128410340300c40140c001d442c0020800800082d04280c0d260700c11100a0364030404030f60802c5030341e14480c40802c0b03054601c2c2d0540904012000c42e461280d0002100200c0c41d00c0e0751036203c0720305142 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 913340602 1250 913339352 913339373
    0x13051c0c0e01120f0206040f06090306050a020a020303180325260a08250c03121104060f0207030c0f06030f09030206220f2d0321020d02070b0103 64
    0xc41540e51807070010007140590301400c0507507540050200144040a00219941e40b0a503007091f10080042c900000d502d0f0351014251040364001c01e000c00c015241c00c45503209a200e8140580010790060002c10090702000c0c0c1c0b0055070155541c11a45815200c0d0600400c0070311743c540b01442e032185414148184402100c0681220059500940010f070140700414014004d0701c00e89070070012800001140c800e20101c0d00004040c0c1051110b03042d4400501c010420098008220002100c80c90842012441c60144525800b102c040701c504203400d00314100e48072440b849280c02140302d0b03072200001007511080315002500070300d0016403589017402405402e0f03c49404140703850a2400750600e000c264042000f40d000702480c0324621044903015900c01d003040100c100030b0040c6035135100c00c00c1001000e400c441c040100003070910210406420308844452482403015001c182d0302445448042c87c003a030060002150500b0050800101f52004c7c1d040707800c503500032922000b000005000b400000d800 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 913341852 1250 913340602 913340609
    0x30e060c030103050d020c10031509020301030807020a14030d1202120702010c111501120c090c051b2b03110c0f0c15090409030302190e0909120f13051c0c 68
    0x5081f40d103600b1000c0340c04400c1074141a02010b9480290030703440d031080034224005120f809030664807942c49003030150b480e43c090001244100d02500300000d0b0010b48000c15145c00314000e014007410300302001e00382c5851401c140303440300e43d540c00c00424004106521140e40103542c541d00000700905120300c054900d40b600316a81e030300740c0e10544030912840065103425055608801043d01c0d541d0041c40c00881340410794110524142c20f01407035440469100b0060031001e64005031501e025054045803603211600a00c140403a088042101201030303c0c81e030014050850503281c00200d040d203a04154560b604501039a54071074010b41d039580308181c8200900120036104035a0100303005885c0c251030420b0701c1440304042c0515154400c2c4400d00d07001e54152004100352702e801c4601c0040303c400090840d510045410b202d1080e510104041c0c4d10001040340400460403405464010494205070301600007143e21444841c8815010820340c072142074080300c0c0107010b0301040c2e80c0b1b4807078501035415820030740 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 913343102 1250 913341852 913341857
    0x602011a030c0607110d03030207110d02010f030b0f0303040303081b0f0a0c03120e030306030d1e1416030206180d0c08070c050a06020c031b03060115030e060c030103050d 75
    0x1906000d280c0e0045041c48425004075162a9100c1325880c260220401d5224000e901404500c2074000f4143c041d0024212144143c91140300c00240300c04010100403000b001a0000d43c22443d04c00410303000383d000b1140c84200a05001c1072500e00300000b4650750040d04120002a10401800f40a24030810f0390070700441640d01550401281001d03042c000c0c0900800f81c0e0410000c0c1103601c0a244c0240701800f5942d503480700c1840a8904d03141c8007070b40c030303070050390b80c0d41c043e12030f0100c40c2541ca84030300c05511003031540d414140d2032603a000c2011118912011740454290208001c03a503511081c1c050080131584c401d4001c3c1c482881d10340c3d400341c0300343c00c1100d80d0308054000d1001c145003d5800108242e1450b44158241e440f450306d414002d00d881605c0d003106d44c00180c1c852000c03400540001e102d00c09000201d08903900302c15081c18030000003149000894040e840a0014099140c4c49205c0b10340690191500091000d0166800c9107000030903544003d02c07410010061050003410f0103220030401650 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 913344352 1250 913343102 913343141
    0x3140402010c0f11040204090209010806030d05030c0c07150c03080c0316030509010905010f020d06051806010318120f092909010212030a0f052a0d0207021801060201 73
    0x580002e0415000c0c214002d007840740000c201010002402d11881020601603c00c540321621014154020343c07140c041d00d17000c90700f035000040345442c0000c3c5410810307130165603039411a04d41c040d1a000607000310034511402e003d012004a01500c240030a14601c24031959003541c00c400e141005840b500c0003418983c400c03441002001540d5000e001400aa0901444c000a0a690318003119004181d102e5006006508001000040300041e8000d0b040c02c400700c0b03000308586070f61001003055420b03007840d58508046140d8002211903020368000a010300741c0b1001c0d80c0b980100f80e602d100803980b0382e28408001c10101030850149076403102c46913002d40f0800400d0046280c42108140e210400329042c4100b000c40050240d80c940d2080c064401080c0c80b81c9480340d01d03824810b00301405001c0e251032140040b454000090780300d41044801b2241d0800705914102c0310910040620b20742d500801c3c0c3c90f2041c540070030103400140c0f00c014000b8116110310418851950524000a09550110518000c00c1040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 913345602 1250 913344352 913344361
    0xe0f0f01050d08073206010303110a0215090f0604030b090d080606030f0402012c0907020309011707031803081609051507020a09390503180106090c0509010314 70
    0xc80483c4d405640029045900c045c909201d4103098030004d00000700030b0030109181c24102000103900d416a88681c582c822002c1011245541c1c6902000010398000c1e6040031540c0260b003102c009102e5040040d22500c0502d408902041d09680b1135802261a58840002c20040007003c0c009401400052724013051a810403a0014466000291101c0000b031042004641107a008002c80300c0c034018481000d40f100da00a12207002d0780300300c0c2d4012500a41c0e147c1d0010310510320100417200103200507155610203084072140c1804202c801480302d402d265646110702080c00c44500ea500ea400d20030380e902070680c905041703074501c0c2c0c0c60300300021020302040103001c0c00241c0e503a400c00301c0d80110066110f600da409500001c0c803280b483c0e503c01800e0926200b201461284800c1c1c0b1401400d2511281511918800c0d50000e030804000582e07100080d018008071320000140d2103c210304400640001c52940c6e00c4070300180440720f1040d18100820300c0020000c0315940c142c0142c40c40c07a0903803150b01d41103140 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 913346852 1250 913345602 913345613
    0x5030d020d0225031221240b04031b0819032d0c210c050f07061409010210060f0504110c1b1206012705070207031b0e0f0f01050d 57
    0x2070000800a021501501504a108940d41d105111054913800014403031200300d00010240e00b0725880b800c9400420072403c9147c00c040003000c940008440b145014507544402c0c03907481d0391000130001000080b0000440540410910540e442d03820511a0603464038030303014054101c0c00c10700d0300d520291030f02cac1510a84055000b604482c2e40a09101c3c078400080d203410240d6031100d031030800c4030154140e81801e0059214110300c40051058003142d40c000705100703440b03603208094482ca07030019072117600451500034070101520040b8010300440f07588000c4002c0050640d155500a225a186611810400c034a418001c40703440f501e024002074505901400300342c0d150380344d8072801c212481010304901c07202e4440944400c00703105007030b0a40d805540c6a0001512095020080140866409048030094600b910a6a014800c540c00400801c0d241d0758070048c40748452480c26150302c801c0200010070460726200b907407141001000e9040e40c2d1070b195a8607140000306801c074034007806565000000240703 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 913348102 1250 913346852 913346923
    0x809070905070309140a02010207080f10090c240e01030e0307081303080309030a08070f080718091104050a0e010b071b0f0909030f0f0203040e0901020405030d020d02 73
    0x21100500401c440d60b4240050b03001d0840d42d44000c0c801e8419114511504502040404440d03100340d00351600310307541d6840385540754050716107003941d80c000c19225075804074150311440003180320b003108070143d544d500c0083c015014500050040d01c40182000070007140c0c00b6041022078003090070f042042c03000c08140c8940c0c1c0e014504c8000c01050001450b81d610b105130705030034401947e0294280c1da0700c2c41c0a400e0300f5102c0e0440d040340004618642c011650302c03400b590204461040e039035600030840d96590340445000f40c8490b4104580c1050581c0410400103601415000130764408a40c0e07516440c2c88280328071400b26038819a207015400740103220b80e0703900307000315090a03402c5028840400014019441c0701c040380c0e408500300c10100d1a0010326613070583c010341c8219001c1d407506860b4502c201070139217810f00d80b40010401a0400c201c00d008200800c070340c1d0768214000100050500e92210017091800c3e1040350410b0142c0e10034800c51050b160304110311800f03d00010400d0f8582c8070841412580304 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 913349352 1250 913348102 913348109
    0x90b090d170c07020d030c050624090612010f06050109050d030206180708070608191505010c0c03060e030301051014090616050d030b040b03010227150301030819080907 74
    0x700c110402007110007520b882580c80894004000c14442502460007402281d200341080f15580a0701000500513214542c0d980c1c0d121006040821804003484108030b01030b80010030070303940011904200c0e1240e010903c102001940d5801001a6150078000007620740038860344000d01c940120003209000030b5010440a40003c000010703c0c0311650944112810503d0907005159036103e0040c000811a50041b24a40566050380042da000384610600d04252804045185002694400200440c2d44603d0921910b02e0040f0f2021018907200c0d560300040d10003002c100c5000b0b500c0800103105628003260700c8108030303001d4202030740e030000d8501d071510580c061411041c2c812100403441034424408214a005680d0780002500c04800d010400600200a02c8109901840c540304d5448503c0c1030501c2101c15880c6020246007a0083c00c01d102c00c88038821514843c0c002008448092420f0952806076010b0340c07107141410f46940365813030002e043d20740310b03504001008131105c2030043e220000705015050703 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 913350602 1250 913349352 913349387
    0x11030913090512070b1501050705060103030503100306060e070e0303070f02060a142a03090108180a0b040303050910050f16050f0d0e0601050d210e13090b090d 70
    0x100301c4506020f8100441410b09151202000440e90104030101801d248541840590085174458000045490380100c200007040c6510640c01400441d004030069503018a1102180c4001d9460b503450000740c0b10306070310035200c121143c000c0c0246190802040d94a000703003a002035003000080d0b15542c1d444000400b002e03000303100005541d00e442e4420184080340d0000300140d1740d554131103015074541070350008035070341541c0d4500c4198030310444000c822030f40600c4050352000c2d407944412141102c0c44500180c605c000707100d4140c0040000c1c641040441c8500d0007920f00040e5454048041803c054400da03504140328a401d0822140c01c1030a80403e40045540048000120403503000307035801d1150914040c40f207500031442910207070b0650000e8070142c20050694040341d90f94800d221b2035030b0214200030400c4400480304007420b40c052a2841ea07500c4607107000c4100c80c044d00003143d000d0591a10818426841d0810401803003401089039802c100b42030010a08981d201800400d0f0640b070801907080c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 913351852 1250 913350602 913350611
    0x604050708100e192a14090405100e01060503190603030807120e010e2d030901053915040b060d060603120201060f0b0415030905030d05100611030913 66
    0x38400c0c1212011604440704c5003042040c0701c051402c00c2c84010303052441d05171000242c0300e04440c3c68814258042c80c54071403140c040c03c0111120812016010003440100084880500010140c105074007603802840c2c40c0c0c4943e0f41c1c03404c084008101d1054000540b80e141400c0510420000e90f03c8102146c2c4040301d8a05000d150290415100c0a0040c9580d030300d00c1907080c01c40c0005e11010100d415a0000c441859441d02a0300c00c041e4101c42402600281c02c881d002808404965400703280101480c22010059640c078a0941d81c0391251442d41c801c902021039494141108903401c204042102e00c1e104402241103890300365500005564000e120360301403441140c03078808000f1580c00880c059a881000c4029450728404000e0007409281300d4282000442c104c00117014540c0011203003511408440042c0d1a14108819006010002d000f240d482c4010400140000180c3c131075240244040044183c0b040d1030303c203000304031041d40c0504852035081013101141a5480d40900c0442146a210114 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 913353102 1250 913351852 913351861
    0x50403061d0f010219020c151c050a050a0b0d111504080708030306190303080103033e0105010504020f1c020f03100510052b11040603050604050708100e 67
    0x150307080300804080d926482501c1c10200c01d50010b4001e0100c0d0030080c3c0b41c00780403460300001265a41184041d668215080c0c8140a46010000f401012035a9800d40c403d145041070161030004c84004a400d4003500707135540d0520065039442d001c0d000b0407680444c0c1209a070003050315107000100214001920413049119480c46d00c04038140ad443c010710420054441d419a00c070800c0391a9072080f03401900c00d03205800d42040248545003141c4c00d907505591811900c0e030840d40e06945101c0a108000300321002502100c03000ca03003402c03071030042c0041c040c81410021852281c0900b55081a0000c5100c3c0d0b0041c0610704034a0580025a062201840c00700fa0301c0c07900801c5010020b1141f010b42d84140c460010812010009015110040364030a482d403208418681a0440707040c01911001c3c00001460703002114040d0090701c40740c030841c0386000001744440444804035a503600603070100b0b022949031420070003140340c148101c0c1c0d07011000b07092820b42803800c0d00800d880340884e40a5140b0240c105000706 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 913354352 1250 913353102 913353131
    0x30b09280921201f020f04030f030309020a0303020c0301050f090d030902040b060703110d091a031b1b01060b0301030c050d1106040b0d0b10050412080c031218010c05040306 76
    0xe101e50310b034050002101d250a00304080d02c58440721201e080400b1301c6003d25103144101d20850f0110080440c01ea8205811540d50041551604c141941010b03103500742c42001d0380c0d07003000c220b0065200303070000c0030301d00c50402c1030600f91369005010311450742e0710100304001d0400100301c010a5988915000611a20b14400100113107003985445800000c0482c4050030517402180c900904075080c07040315003103c11440100c079007150034041c000c80d2004038003164034510401006140c104801c0402c2c030710201c0540d00700461642000c03ca11103a40c64007000603c4425003071203200b0142c40728414a40c034660564582e00c3da07400300c510600d800703000c2100364a0140035103030705c200d17a2105004180f10354642d076400d1b0b031001540000c00c0080a8900d052945060362420040d41c050905254603030508086c41d04c080700d50440358082c0c1c1a50300071340400403a1117229081c0014280350042c082d00c0d4209050035441000d0480d02c0c1d010f298001c0e0b01d07006107607103010782140507503049907480000401d03103001c5c0c000300 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 913355602 1250 913354352 913354367
    0x10e0103090804060c051513080d020d2c46050d12051306020901020703081306170403120f0b12330610030b09280921 52
    0x2410b0880046070120344c0c244d00c616501296809501102c500d02581108020a001c0903241d401d201c00c410351600300011085005088805038040c00142403c060200741c3e010703520207060304600c07201d0149101301c003030300c0e9083e40b841840302ca41e0003400c08260101c000090070a815219030000070f400841003100c82c0c14038140a00313400342219106546551403914a6039144181458008140304090040142c0c0551084030710402c01c2c1183e405010307403191078190095101c0c045c158118064144040080740124009100f120720165010310001e1502200800b000b2031a05a50a00000d02040c000400d90003605015918107031304002803007840407503140b00207104011a55401c03010700c2d008243d1114000c282e03a00c0700480d0600d50200900ca441f0f1800d5605564103828082207501004a4841c1c00c0c03002d901d9021860301d040000b40d00c4003081c0014000c060031189155084950f4480d100a00882c0040a12056510340144030074040307903484401820415019141032003004020300c0601d44074084 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 913356852 1250 913355602 913355621
    0x7030c0b071518051b0307150f0f020c0409080c06070503040b2212030c02010b040213090b0334141c050a14160b040b070209041a0a050a1a010e010e0103 67
    0x860b905a180214031071080c100151005211f809010b81c0020710803402940c6c080121a640d403010480001920150380a03042101c80728214031904404070115101c030f00c03614074094002c030a100c0d158480d600460313141c9140203200a08000e01442440001405184101c1d0061407400020682d45d80c8002196880d41001c00007070012001d8204100308c154040e4003507815001c480c2c0c02804100414000e200c140d100c0c0d000304c0078400714080010410001c6542c480100d00c14010305035204080b59160310301060702d007000060500e201580c0f1a81c0300c070310010070440080980d1501c0858070690f034030018485042450303c151218961304128ac04100040c4007038a5910340c8107469441904809690941c0d0f0320802240c80b41ea03800c071410210b035100c1c042090b2001c4801e9140c44503e861900e07820310085241c058800c031081410041ca13800141c04400400e48201004000014103241101410054a5a0701900010015405501426668403841240c40d2900a003001c00c0d07010300303480040780100042c80c1c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 913358102 1250 913356852 913356863
    0x20a200d06050a05063003040b031e0703050709140105090d03031d0309061902030f0f0d050106051603050a0e03010513021921111207030c0b071518 65
    0x381460104009640094000d0b04900010019a5652003c0c003c1e01e0020200004c98084040d480c2d20850505d0900c84100c1c01d0b5003025207040c01d030341d1031854409401c1907624014150310920b4603483e044802c940c45074060b680345000e00c0030741003164000c0d041d00c540e80600c003501c110f1400070701c030039900400c2140d050b0308016040f810b00010038240100142141c0c28900484001d008458101c0d003000002d99522800041519150081c0910f0102d01441194075006c190700040c00500d82201e1140c0141808292862410751359449000c030160480d07a05030000c8051000610001c4000140300d020301e20820b9050a05076900d0035400300654201840468066056090404020701020001888007489100392691520358041241c4848038000c1c0340100c00b4858030301c01703000006850a1046000b494090700c000f10110042801082d051104c219041c84941c1c0825010030800c001210088018040d1101c081e06010f42591247e101c0300b00c1d0400900000e07194000c141d0f200e444110b002e5000d0341d205 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 913359352 1250 913358102 913358119
    0x403170408030a080108010f021e090301060b030112060f05090c1e040207050f0c1203032409040803060f100f031d01050405071a0a08072f07170a03020a20 68
    0x1440000c02c04c3c0004d004140b401e50030300200e4080150700d4005d90700d41135174901450441102c40080c202c090f4215210031076156417203540c00616120042c0c011130203800b65800d041902c554500340308050724002c4445114081c5400c08002c0d000f1030100d00b407a460070084603c0d0403613a01d0b4000b02400854903640c400e0f802840003900320308200d000aa001d411652540c203940c0f15084010400c1102c60f01ca00000720b09800400c001200e070350b0300160700ca8415403030300c40e030043d1021000040790f029001141d04a0780c3d000000705104552810303c56044411070700301c2c2c1c801040c3c032540000401c071450108508003803648030f1702080030001d82c0c20604c401e09140140208035514090408607660141846a00e94040700000001d102c18094002c031051064141c0343c2c6038168459017801c5407820202e54550300c001201e01c04c1a00c7c20740c036412a540c558074085c401000150b0624203038041800c0b5075503004069a00072031200000940100d4401c03840c0c0d03003142c00c42030b103000b1202001102481401102c0d030b010001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 913360602 1250 913359352 913359367
    0x7081b040807210201090b3402033f0903100203011806030c060c0809090906430207030503040929090f060a030615050420040317040803 60
    0xa00104403100030030b003d1151600001c800d00c07040a0558040c5c001006650305124071030700e4030300820100444002d660800100988a491079072141c03010034a420001a0716401545420402c005403144041d11203911880c0451204075600f41000c0405403443d850001810b03031400309810b0795200e8802034269207a0340310785400030009500c00d0058600c60401d004843c1c2e884403980c4110015a03500401d2111070900740170054900c40001103044403100d80810001b0307400d45440c00c40b00d0007120703050004e10240c10b102c1c212050250540032000321014004000c0d00007003044078440300381183c03812000144856034101c202d04101d400d0304090164400021b000070703001c0c2c40ba88101c2121050100e05030b154809940b1201c82c0e04841041c0380da1041140000c5402c2201110b83c442d0060401440d206d0322503560341d00c00068540300d41d545a200e00184104204c20f043c41d01401100c0b60b0800c1c40700004030803000490140d4025030001415034150301005c1c08400624030121000380c0115400c032a140c495 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 913361852 1250 913360602 913360619
    0x3140f0103030f0c080a03180807120801080f0a11031608030a03060504230c04081f0e0102030906190908030c0c0f01020a050a03050604060e180d08040b07081b04 71
    0x100707100c100e0014510425203825070b0304c99080c07000910390040d18245883c2c0315020403009001164964482c81c441000c051000441070781c000e00f0454880c4580703805000e161100502031417030592200009802402031840c00d05000b00d40070100d41c0c2e01c09145007030303c4d0440f00400d02c2c004a0a10881132100403144c04660150000054000c010b4542e8040c8445034403502880142c07506c03403030b814042503c02d0105040700400c03280000d074001c29450055003400c0c2e407020a24980810300d50105050b8511040e1007002190074001c000d4010036100c025442c6007800d800c1965291001000101c14103020300b01e071001158250040b40e0201e8001c40500d440c3c1c107054140c1580c0c0e0384a04c1d0b0160951241064800c941c04041c02a034008a10ba5180c2c20b040c0950203200740d002d000001d0019a000d80d8444003c141c421042085a004804c001e007004200c08010b04181e14040305c490b600003d1203444010000002c0341c0c84103990b802001441c143e8003a88640410300c1d940c55407540200c421480129000c85e0050 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 913363102 1250 913361852 913361881
    0x3060b120a0902033004051008070e040219031a09060d1103070e06100801181e090308011809080f0a0216060e010201060b0405030a1202031c05061017070e010314 71
    0x215403805c58101000e90a003180b4280f1030707031140d44d401918070650144400c0c0140d0040e90b003c0309500700030814500309800141240d0080181140702040e0303c0b40303050990352502c124064070155141c0d000140d44d5100019241102c0240054410418042c2100412803e48100901c0004c0941115601612049450140c07103040715450b0280c503000d00050480b5100b030b01041d049031810691011411404c41c01e29014041a01c0f8007041501120b111400b0829544150318100d4001c2d40c890000303504240010709845d02c1866200700382402c0c2203088000c64210011140d01c0d242e4000c0c6250b550041003c2641010840b001211984080c20340001b1915040140031241c07402c00d0b8000c00003070703407120030f568003602540c01225016170040640100141605c100246102480d00440c1d0a286030100143c074502448071000c41283e86510501c03015062450f6201c0c101099810aa4004241c00e40300340c2c44480f00404ea601007251183d00010a64001c0e88210b81200c0d4281d25038406203031200040c007480 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 913364352 1250 913363102 913363153
    0x3091005090a1101021501140319060b04230a020a090b0a0f0e0402040e01030f05070f090218040b091b0f0a1107090e1c0207260d03060b120a090203 65
    0x1030b4800f1114240390710114100d0515140060494541d900300451020083c454032104d60705031080c035914001c0c80c1d20305200f8119040c4207079000308680d1000700601041d1010707a03400940c2c0c2c205101000c0310324108100c00c00c1d03200030360340c00c010703182d841d148004c803503008440c1c0c4184100000041c0c1005050360001d4003600d01580f5407650306020701071100344000c0388200d100d808000300304240180b001610442203d4040c9000d403049814543c1c0f1284403505c042c1c215406000120740c00500008a04c6000d400b041080c00c0c201c40402140903250081140200c00a242050f010030710349040003c0752050080c2e0b0001052890f40c240c84002d4141d002e003000300007031240f10844c403075230740c000032900401e001c4c07404060343d544054003459200346800c40600b0f43c821101000e50082c00c40110300d0200319908054495000442d003000384810580d05e508107800d84d0901b40805040130001e204041c44a0304407180f01c00c0140d149041540d9108214006014111009505018000d02d84091050550a00e200f6 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 913365602 1250 913364352 913364363
    0x3031204020f100c06024e2202121e070b03070f0c061d0d230f0f09030a080403061508120a0302120703050f15010e040b2e0906030203150603091005090a 67
    0xa401d07419054003c030700401c43d803143d200403a00240c0c1031800d6070000f1460700c440c4092b2044017440c80c0f83c05c10300e052584030451641040c03580d6601c0d03900c940c2c041003e600206400300c0ca092850a003000028846d03011410a0307000e201c0119081020014560321480003003812148544100301790003003a5884250b1504010001220080e54000c80c80c0c85804403641c0040d4014107516101340709100c0300d843d8116840d031a101140510002c1041c0d201800818030092080b03890b10703551400c5280c8001190086200000c41d98030760703101403080141c000f440a54041840d40410b48410091b02c08501900c0f403003030030b440004c240c8006e00c204550903070007003401441e007082c1400795079030340000d00c040c0c802d07880c0070300c50000f007605c03401c44940d0900c0d50240d82c59400c09451591000044981100004000c200400200c3d05030201c00b802164041042e00250130a03103401c0d4a1800c00c105282c41e81540c41c050315100d10800008200d5214041020107c2158125014482403500b01c03141525030248450a440 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 913366852 1250 913365602 913365727
    0xc08180c030c0f130603060618020307080f0a09061109040c080f040308041e050c0102010c02010c08010911041203020d030605010c1e03030b03031204020f100c0602 72
    0x1a006004185504900c80c0507005000d4944000d040108095030855442e800a03050000110404030741e00441c1d0146006031404104245001000c0c01c90003001c030f11114180e4418024400001d6121829903001031000c08400341c2525406944401002c2c40352000b00041d280c440424105480784025203003400003102c0400c00030042030340c1501c440700110346030b103400355070034002400080c00785102c41d41103070040ca11800d4054000b43e00d070184880c42d04040d50903501620a450745982d0900074105a80c281c0d02c02030241d1543d0190180a11406000f816240c985455403c501d15000d501990014152504951040340145c10081d40320050403809000203030a02e40081100d501601041d403d0365440b00b81c04560000039005001c040c0e0901c4021820035840d003640e00c1140d90100007070680c2202c0080c0003100380c1070034410081031111540d14503000743c00520081c2d4940d80c0040f4810f40064100c0b01c0969109507400d42d4011030260b801000c0c54410380c4841e018241c5000139501050003281280300030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 913368102 1250 913366852 913366891
    0xe041505010602100c1e020a0c050307120201080c0d0606052205060703030b01020c0411090f0d080a27030303090b090109120516080301080f06150a06140d0c08 70
    0x405640c0240a690050b0380030506000d08440103520804000ca41c030b180040034002201e0800e001c8048902400300180d1140c030207142445503852400000b0641140280791f00c13490580804c19403100c280d0080c0c1070060010008a407001407004030369003440789c0d0310100507030b907100d000180940d041440307805407585009040007100d80203000301506441c8000c00d0113080c00c0c1160340807000b038011015814118003c0c01303094581c030f03110f6000703a00701c1e550380c81446504e4180100c180040c00c013174001c405200b2a00c060007007000c20384a60848564417003e1400090500b007407240021044c3e808144546a840c0e074800000c02d0540c160701840d9650320820644500f42c80340c071201426202d50b00000740460b080e200202144034001c00003003404040314000c000b06001d06890700c08aa4001b40d21a02103a00940358000701d809003806107541c00740044188a088610318804100304540a001321070601c5000d500d1040010400400e480d084503195009101461304030305c000704006800e0f603031010410342504400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 913369352 1250 913368102 913368143
    0x120a09240f08091b042003071b0206030103110a0e09100501090c121505030a150605010203031003020607030903021309021203040825030c030318050d080706050405160e04 75
    0x5000701c442c5070040030800c1c15144140300200d003100032070b54031a581d08009010204c10610306c0e86103010002c030442e1640303008403014001000b0300c0f10321030090160b0289080181d881d8410303039056a8000001c910300c0f903150f2002c5404044203400491030303c2d918604001c0c00c20400a002d00b0308410966081c09a039a079070301d140060311092101c04001c100200d44440d14050307181d022511200319403204c03045003590361001c0390404140d068161080c100003d405140f4920f51f0044d003000300340a100442c6180b81c030109041084810f404000d2180c0303000a01e01090601c1003454502643d002000c400001407802d20000c01881b030300f40d041f4064410100440140f407000700541d81280c2c126006055140314a00c81d09019030301d5102c6990070480030b103401101298260044070050751080e16440f8092440300c10400700c03c401540071703d2140a101d04164009840001618480c0364403d1000c40c07a80ca991800e07500b442100700740322884441c8048006020746c02c1940351401540111800306e6107040944a0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 913370602 1250 913369352 913369367
    0x100f09211806081503011d0c0306150d080d0906062706060c08160c1715011202010806132d09080301030b0711120d0e070503120a09240f 60
    0x2c2c0070106991000141c00101c20310b0000a09a600500010b184005071008034034051408034030600a40c0b042c90400b031141020060300b608101c060200f03c0c4100284000904582c041860091091902047d80702480c0840d401c0030183d1980050180070b0b060b190303410082e2400b014100e0071400004900c80d580101114400c00c41a00d4556440d5443c0000c80d8880d220a1ba00c4003240009803400c66200c0c40206141c2c1c003402025215021485a0b0032484650720392901d8030000c3d00000c0040042c00410a0b00c2e5011084074030390b5420f0078113900547e05c2c031001074801d0124203102c402c2c0714102554003046005000011600d15802600001e0408500d103640046030442c0c0e07001402c0e42003c100500219200da801107030310092500d041d8900c40d42c119401c9062001081140c1510b0b000896600e100000d140911815040b07064001d266a03458040040c0c0c1d910307504c01462140c42400079000d02c0b054403803544070015100c0300440005c888403200501c2c50701080892554005408016200e5441d4802c0f400c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 913371852 1250 913370602 913370609
    0xc0a03060338060f010e06040503100c090f050117071b03020f010c080f061c080a0c1a06240d090c061b050d0f11060a061a040305100f092118 62
    0xd403442213244100640d04001e80140541d0722610502c400100c90780d007000507400c550341d004000b081c4281c1343c15004d0808030a5420104d0301c400d48200a001c1c50340e1200801c0b0b801000c1c8a01c2041d1502c41810603a0342c03522550180100003007500d1510b0a040c0c00003207011803599001e00811174101070b8042100c1104080d100b803100c4000031404105a403401892002e0104a00c0009500765000c40d0b80f072540350390000f2600d2020606211614042c00803c07031540080d40703031940303c8102c0307407405000140d5a0100c1b100c00e42074006410301400003180c4040301b590881041c0e08010882c25070581000900b828043c80380d5000984003480080161400d00c1a290510f40e00600030540360313070818016a090303814900300104205078a4200b0a0003030701044214040c11311280700040d25030804001418a8100062201e030484081008000156000880007982c0b0300100000548945100100740a040306000242c655500c04940380301400ba980d00820a280380b07500d50f404818400165004031300b51510 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 913373102 1250 913371852 913371859
    0x82d120405150c1501091109010813050c030a0b0411010203090a0b070503120c1309020f2a0322050d0f02010305190c0c1104020903060c0a0306033806 66
    0x10030150424030300b1000d050400002d0641070480c00e0007901d01d40000c2d807810010300d1102e0360040042e0a10340c0b0845c28000c0e0701c0300ca43c0c1c2c47e0080700b9001905c0090040c11041c1d41c1a2400140d505108052019003a208070060a60f80244c0c02801c0580ca0541c0c185c4060318400c1d044001c040c0340751b0001003140c805070005030000c91001d00d440e6241c22141c0040c031054569010804c00100780c03075004141e1600c20401d201c081601c5400d113100c0310701c00b002a41c102070440781c8100400e1612851030f90030b40304045500a2507410b03a113000103001c03100f00c00c11081d50b081c42c0300101d0503000040c03c81e030310340c03580f08000380b030041c04650340310204183c1d1141d03040090040700f6001d00a00165100750005a480032089006c03800c0600f00d4001241200c8241958000040c034a0400b002001241d10108203640b104880c254209640d43c0c00003a00c50801901d0250401c6d00041c0300e06815000f41c001000030740c0c001007450130382c0001d03403c000809001984c181d012140c1d040012004d90708140360550140710301a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 913374352 1250 913373102 913373107
    0x3030b120a02090a140403090e06150904020d0e01020a080702061509070e0613030305090f0d050601061b05060108060f010e040309151b08130b2b0204082d12 69
    0x10340a0000f40c2c07101420507008240c5456407504000340342d298a40c06103200c0d075501c0241d180b0f000c5a40480010191425200c0d003071441804c444a100a4192410080700302da00517070700c80c150f502101c0245001c1d504203c2030750001c6141480e1031f400840b218412412502030341c1e0385991300b104020103a003140d0303609a0711020040224034603e11a07070304048220b1000d86030707900d0201c0a91030381822070300d01c0c0d204400051b0001540d66140c10503c079587c4010f0360a81d200c800565140e6211038503038034140110000c1003640c0c445800701d88203001075041c42e41c1c0c018003910070550711110066128041103440358a58030700107000140c40d0f1a1030798002c0c800d503096600e28001d203003407076400f210058903030040b0743c20010804071880007640c00404001003184600c03011079852680c4a1210b810302c1003940500d01114080c401a0040204201108200c1010149030f03ca5884d803039500c28004d001c0c40c0c1010001e4400d403a0703c01d0404111440c410400010645101076003400321100e156074417000560801c461405 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 913375602 1250 913374352 913374373
    0x60f0406050601170a0603050c0114092704080306030c0108041101030c020708030414040e07031a0a110705010c081005180907170d09090c090501110a060e0a03030b12 73
    0x10741d21140e000241454003000340036554145806545041e0b8002020341d545460400803c4001c0000094090081c05e00180e105406103030740203180580d052050140c00c1c0312003e01c922160307c41074900c2400c40203076110110308160a00c008640c0044071094001d22544040710000e600a5511610481d401a0346600d6601c121004601910070034282000754031452402241d441020b00161000d00020b01c400c1c1c04d10390b550401c20040d20324401d0088156000104244049808290742d4005641c14020341029074507204a000020704d440d030400c0e101f9003800f140c15404c010040d004240707040d207166103810003a00c466042c580005211700c255603000002076001031003540d05c004801ea101c0e003e1001d8030440d07640c03034180d283e402ca440540a000e5400c52480c030401d4681244601026251406040152880f440000340180c203060060320f06103c01e541000300d0000c01046110748565000e041400280c014490440e0340d2440c03040101d01090500c5040050b9041c444103c4880029000003440101c81c03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 913376852 1250 913375602 913375613
    0xa151a06040513060509161b02210c180105031506130b0f03012a0f0f0c020607020301060807210206160c170a23060c090f040f0207020306010503060f04 67
    0x1a22a051403c0368803507034009800e030307900500c8030f03c1801d43d40e024010300200400c00a01c010701111760703604980301000007007007da10b80c010258035600d107509148802450302c0c401c051a00400780d81c0b0507807100c2e408003000220703c0c2c28030145040b075400342e0480e00e40c504001010303510315400710b48558026007044001c120040741c603048424048000f40104000f0054000031909484624200700300116910f03ea40300d00c0f2000d0078000e0a45041c51500710590019100b008107035030010540075040180180d442c00556650390201d542c940e038000c008008107991410f0694690050b4419507004503910205001145000c001c151400c41d8002d0085103480c603180031000403a1180002643d421400d0900410141400c0344100603100348400100540c01891820030080c1551000e00c0c0d12680816600d000c40010018207140c008588203001501c68a218002c82d6a043d900c030250b9900600303014100725003071010703801410740d00c0c001c1d01034403a20ba0300c900038565604410348580da03104501e02c0000300400e1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 913378102 1250 913376852 913376869
    0xa21090510240b04080f1603170f030406060806152404030c06020102090f040c0e280e01030204110319051906090c170702030f13080a151a060405 64
    0x2020103040e000341042e07006546680c1007903800462000b40d0000303040c48600b0080004400748540c00008080c2c0303080141c031030141e68609200060070901c000c84207104010003082038500007070340300b031601d612407402e0305103400500040d101d50355240c002c00010403d0240c45104010445802030905d041e5040050001e5100000003118684d00440074030000c000210305040b00700050200780d001688811800e070402c980c03080d415a88a115900e424016000507401c00200c1c0d075080d9007200c001c000f081900490703520402d40d401e0300c0070300f24003ca003001c101c441d40c1d020001c1c180c80c000da508000b40c507440e1003090414401a41d0b03018800c6154000d00790014116040320382d102c4041c0595882140c41062000143e5606400c4ac4030065140c0300c03021003180e0b002c0030a0f083c800b002410b88503641842d0301300ac2e40f6481411410b103180c0000107000c2100c44160703000c40000340f14040131a002d08015090005841c0803150725005c11900f000c0842b00d00302040300c0d00300d080c1e030401800c084c5454a402c0c00c101114 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 913379352 1250 913378102 913378121
    0x50601140f04140303070222060501031e0506041103071110052a090303301b0c01021306080117030c0d050d0b15031b03010308070209090a05030a21090510 68
    0x5102c104481c00060320350038050003d4140c40ba11440c001188ca80110341034a086401203030416203050203004080c2d07802d03d101d456604010900003295220701001c5400303803c0074200020480400070600407210b5010000003410001c48082d1500f40c070100d60418191a0182c0e40030040100c0c000d820000401c41100d00ca9050b003209100500d011040e901290864211010410024018402d0710180c226100000034a10700e2015420f1038902d8034005140800040107898000307000c020490f0200d181c825812100d0390041603181e840017a58401d4010404d070001d00410a984200d46d200d03900003000081607848000044c0c0c046c15240a400c6c00807140ca030061010030141c141c582c11025110340f40d0480c1c0400e41407292035107030f65a14181c1856603d0040c5001d040d03000510801c0100049000881501c00280d030495035140d481d21041203580c5401d0a220014025010008004190301e800c0310719176034088100b0104064080307440c0700540440e001908050320640205080e43d1440300181d0121804 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 913380602 1250 913379352 913379359
    0x313210320100b0f060703020601090f020f03010305010209120f06061c0b070f09080c09061507150212010906030b07270f0806090106060c0f02150a03050601140f0414 73
    0xd100c01440c0c99803401d1010100201025620304410030581420188102d4584d019031700c00d8034006450703400945d01da10502c1200308003941c0d001c4030f500c020040c1c1c0480701001110419191a56100e0038180c1c004d5010803c25441494903ca454400c544042510001d101451020f4001342c0e699509000c4484051007040d0000c407540d100b4000040d0710f01c01c52501510142d55a440001110f04014050313013620b81094040e0b500014101009648504409600c18010340360301301c3d034649105280c4040e0045020040490720340300080411551183e015084403100000000c9060f640e408501084403e1800040c0c60b0020f48000240c1250040301c28801141c0d92211038061044078103d040c8900006400c02400300e000048200001d801c20003285403c00d209038020030002c2d250542c09090802c41d048002c10800250780040155a12130441a018242c0c02c4006951008c8108006000b44030460340b20f400700c2c20401c0c41c0620904202c00381e1304244071500c965031500b420851400080000040a5a070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 913381852 1250 913380602 913380647
    0xb0f090604030f0309060336050118110405010b0304110a150e03063409080703080c0f06011809020a1a0c100e0c040504150e03132103 59
    0x5500ca40008000441c002c1007000c145052600c0e0080c640d1149500000805092070802e0840c0498203540c120001642c8080b5040550b09400c1841900a000c0003c5c1065180000e183c0507503600d52040071000380300e4407007000c050755000104800c84d5009c0c01070840c1d05a003440001c0c001040102c0b60407014800034640301c1c0681ea0341c41e862071020102052030001844244003000d06040400c041d80d0000c1c40c000b00c00080d24031100c3c0708416502c0509403802052014068050113900034400c00c8064020481640c44180e160b0078200c0c0150b03c86a00e140c0c00388141380340340002141c00300e007060507144500300d4400030000301b00d00f5001924910030700307a0303004d441c100c0300140350034641141e030303503000c111211180d25a0680514542800d14482d017101d021810300d07107000b40350307400401c072040b00520880d000a0302d0f40b19411310b01c52900c0681e442642e0795260180c10804c42d40300002500d4812840640c65010540300c0401c2c41d4450740b40c22480320a04803116100c40024040d401000d518105480880c2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 913383102 1250 913381852 913381867
    0x905090a0b030d0f110f120306130e011b11100506040b0d0b040606061d10121508060c1804020304022413050a050915190b120a0b0a0b0f 60
    0x90600005041403000f05142c0030072001d031103400c55805c0a071100b114000d030048243c03e209254844c1c8091141c1c0140242c0080000c07002d55988030814410a5220340c1001520000d001550080864480321850704004201c540d8010344224091b190359860070000c4c0c82aa4107412031400580000f8040c2e55001c0d40b03070b440283e001d4941130228000306024100f02c400798201400d04004603031054203d0010851020b40c0004400d0b490401d4502c840ca06a68000d0010060030341119015008800d100303034103060050304000c0525000074082658104416a0040e89485254000303070f1045800d4070b1400d10322680203403190314007071780035561040c0013078241085400c0340e20740407a400e10031003001440c51102107044030140ca00000d11502401c003d8a43d00380c3c0d241448005039090500800386a00000c10b196400742d80e40b121031520f040401250614025981c0b18100580c3c260014401c00c1040110038001952248490182c05660b01c400740418a24505004544507141e11240b52403403d82010440030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 913384352 1250 913383102 913383109
    0x3070b210a0e012d06030305120406090b1f0602010b0d0f0f050d080103061107111309080f0a0210050c09010c0501060513050604050702010e1e0a06050c0310150905090a0b 75
    0x58080040d21200000030150061819484130440e00d41d1130043d18040040c00007039000000c0341c48007240500050030300d50b1140b9041c0302914025800401600d41c10007441018003000007040b2981115004200d0f0300d5865241c100e0884217001d90f0f5039800a80e5840440204180664a1407101d00400b041207820f010740d29410b1400c04507104001c0055140e80c010810301c11548590b086200d9240203040ca07100154840c803003400e0030030380d0f0184601c1603030380445551400f540c80440c11641c0100c515480b580c04400300c01541c2c010b40103420240c0101d00b20304401c0080d910a0b2482502e500ca261810241d03003c00450300341c50055000c0710103659605c00412940e9800e04000580080000c0c0421503280017014041560710203000702e003e41e0304000c00202d4100340440e072010301c0005005202c50300c02c400840d091804000c0c040142001d494102808201c1e82400700851064a000f0342c0302100303942e220241e00701c02d01030804880024985000c24042490302400a03600070a500c03602290440c00840003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 913385602 1250 913384352 913384361
    0x30305400c080a1403090607080f1b0303090d0201050c0a0c080d0f0902041b12050a060504140103052103010608060103230f1b0706050c070c1403070b210a0e01 70
    0x40c80d020303400300c030300318041111214034081c0694054018604041c0b08074003061f80da00564034020100c0c030300403441c080004d01c1541030310394111880d030410144c0e42140255a480364030503110545070b80103805296000380c2c0140200d90190101d220054a8107102c41170031103000c0152942100c00c5d5008000c0009514107a02034540000e1201400207013040c014030400040b01c03000c0c0d0360100c1020860b03001310740c005d4126810401440c032401d0042140e075508204c1c04020800398001a500500d00310111041c0d0203541500b506803441601240d2140c4c605003080c070310544091720107040b4114100014007981d440785440d5900807406041c045040d14100c148503d91000300e140e00f00c034582240d010040e440031a00a03d0f5000038001a404001d0408502c81302e141c2d2142c0f900c05800952200081106066504101d514254006050008458662142c848205220703082e0522030312441d14003280c0c14000d402150012480042c890610b00100d0790500981e003002065101e11b40e590300000302c040b800c28040e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 913386852 1250 913385602 913385609
    0x1020115060206270604030c021f03051006090b070f02010e06030703020d0b0418110307170601090c03022511040f020408120a0f050d061206020304030305400c 70
    0x5482d0918042414071a50440e0003054040910018002200d8010120304a1b81298152802003034442140c00482d00945444071900008808011581403850341a0700040c041ca410b03409030502c030303955440700311501e41c0e25001c0d000100a007044000300241407203005c3e0501c02d1040c140301d1401c202e801c000504c5074204030b0302200070a800003a44800c1c49603500c84c540c01c803081206c0810000e5410b0000f5100c003400700000403c20701030002c0c0c21846540c2005107600034560103188075850541c0111081c1c07a8082889511070190400000ca00c1582c064020340e560640040b55076007118031103410203480c607401101c0130b44020a030703c009401141c0311070003130070540e42c0c3d940f4026940b44c0c5000704d0145040c11107440d0b5450a40203126010101d50b020025130360201a924145441e0300c40c20003c0c00081126900c501d032550b005030510343c03c101c1c440d00658401c074001e03241000607503200031200e0390130883c1221350340e4100a112203641142c8001e882c0400d00140310800c98440b0200781d6541500e00c5241c0c0c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 913388102 1250 913386852 913386857
    0x1c0f02030c0d050708010e0106030f14010303020106050907030207110906010c02031b0307212618010f031b110a050115030b010b04060e010807030f090b041e020d020409020102011506 80
    0x95500000b16540260303604520386285c0710040b0741c50408010410340c418010341003095199a07083c00301401c9900200701c00481d441d20400d40d56502c0c075029000b8001d502c01d1501822050000405690080c401e440945800415101015030400700300074004000a0050f810300c1032000ca080c01503101040900140e10704c6481e1690102c02d11030405140c0701d55980145040c4014100c13010303298800d04015503032184e2050402202c0303100d41c005c010340d0980712405907100d09008511040c042901d008034444c2c800081c0c983c05500c90045404509441c1d20540002100c0c00300380c120000f86104000c252601c40e0320070161221001d00e5a28207083d038907028590500c030001032509005120f00034500e0350042c845880d03d03d140500e415400340c002030800040d1410320444500003850103001e078000e40b2105000c00b104100c10b0241d480c1450641c1c1d401d503000e90b01e00540b5080740255842441c170240c4560380042503801620429403c001c0505117030802281155213601c5605042c0018950003c0544141d8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 913389352 1250 913388102 913388107
    0x3171603120501051e09060d02091306060b0702100e0301180602120903120f0408070b07230a0909151d04051b090606130b040b1809010b1c0f02030c 65
    0x20441c100aa45042c1c1001d40301c0d800091185800c09205e00e080100e08001381c1c0d9105076036581c00009140e14a05040181d080f24a10040160703684100d01c8501c0c0952003500108036480d01c81041040c18010a00000e4100c1060400c01115500600400d501a4001030000c51044c05051070f045401c4099801200c01c0d54001c80c42404040c1d1010500d94400c01010040d0f08144101c403060301032400280c1a1000452418046000e122032502120401c0f03403c451221154249000000c013007100c145090344403460201c04004400c08044201d03066480c450740c0d4641c05908140c0743c0401818620100c11044041e10400030701e070806c84000080254520344000900c1c64182007213030074a0f20074003041c118805c816854200e9540c980314040c0d004a0243c034015200c01005408094100c01d0f03801c5000801e0011400142c50b0300c00000809017854038561011800742c0e07030014481c1e400f001b805a404c000005001d07804085004108010300103100390800708580315083c0700030080303900640747c18680c0c0800 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 913390602 1250 913389352 913389377
    0xe030c01060524030112050708030a1e1814010903120c02090714160f0204061401020d080912030903070f0606030b0606030f16020c03190605091603171603 68
    0x9001c1d1804603d04030b49415220308010b04039520f240700500410f04041d10250b004000e101d02000740001905540044075650080a200a41021080300c4654010401c111180f42041c2c41014989a550711400c3c0303d69816062100e090811760b1000440c6041101c040d2000001c074041c00074484450b004da403a102015512401440181c43e0300510400501c5600002141516010001c45064040d102c07050142000d21345010710a010b61100060b42c0142081c42c0032070144000508034020344e80903003c50b04401c070b501c0010f4506200844000c1055005202c0c00521480e0700c03002958007041042c180c900e8100107540309951040d290106607145a9100c500f807080001d5110645d40200040b215075045d0b02d4002c185280d00f94000340111510074a0b11f40c0041301c54001c01c51488413403001000c1d26442d6001004040411740314580075604203007400f001c210008404260484203101c0c640440a00e41d0660702c802032402041c1510380c0c0040b9041201c801d1a60408200e00341c1d103440790783d482441092 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 913391852 1250 913390602 913390609
    0x807140307050c130905070b070b01081b01261504061406071e080c150a09200406080d02010906110309070e060d14011a15040522020318060f04080714010e030c010605 73
    0x1600000d12030303030141ca0b40c0c04100c040004078404040342440c10281c0b410f001cfc0d2100232a8009098001304809955060200354210344108444840b8251400c1004035510756940c0c482c44000342280d908442c0402c1141c01042c0e10200089a0013a01f00c0500302c1a541a0b50f80311965010703c04245031908858101002010300c00b0700a0380140c00c183c4d00348580070458a61215000303641581240400840c030034080d041d1940c0d04048028000d180907201d49245990020f806024a00e4044418614080501c00c0304614a4188c074003880300b44000742034180c10814040d4940a016040d40d40c0080180e441400040c0c002040c3c850001c41e00c40041200d5410080e15220007841c003071001e10800b0030080d0740f18000c1640701580c1c02c441f011501c010341d90b40302e14144001c90040c0f41ca07603850300703000000300718201000078000307005100c45c44102c5001340d489085038100c1c0c106c10b030b0b0003c2182c0d01c10080100800c0700e00d4407000d001d602103000000c58600221103185146d0100150300d04076515141d04214030f15 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 913393102 1250 913391852 913391873
    0x909021b1203090d0c0c06230c0703062f030a15031415011a07061e021c020c070302122e0e0102030609061c0b040807140307050c130905070b07 63
    0x11310300d0401080c80c80c56550b40b52044403c5004000c1003001004001069001960034841038200034104a6a200c00d090075503501ca0a441c00141c0d855800e02e0342600100100d540601e09404036040d01007505d41404031028501e40c0003925205405480e40031003001580442041d800031403003041001c0074100284003403820440b2049086075425070040c0100060508210b031201000c02d541409561084586030485c001c004511800b52aa243d2200704500000340c1e40c028202214071800410103110504540d9090703100e2070b9511580340c0c124403401c100504001c1c00001d04d807000241655846810002c100c00c40c03c2c180c00c081d03c1000d0340d0000d00404012640b00c0c550200b02e00100039455454400e020440c0054050700301409241041d0891072100801c009910f0030070361142d000c0e501800d040c00c0901c40c0b40c212000545e42201103020400313101400000700c071210b07503014000d4004001340360204042010054110740c0840d407a044100001401804114041c24211701d100b030721844d05080c02c00640 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 913394352 1250 913393102 913393123
    0xa1406070e1c02040c0210020c2803050706020901121b031a031906060e070c030f08060306040609020a0f030f050705042a021203131709010909021b120309 68
    0x81040810b0b0b03451280380c070000c6000c01038040d50042072409190100701d00d441d10600105c40b0091001c81d05d01541600401c241d99400e2000d09203d01c40080080502c8550a0070500140805d408100040000e040c5801902901c3c170141890210351100034616800da039000001c010140750311103038524165405108101108021010070303110070385d5410120350341d84032081c1ea41283c4588003242804209454014002601c4003a402d6074441c1002800540a403c0040703045022660101401d41035a02c50034100340314140007401404a9220350b00d80c40000d15500f101603820102824020681e560240403410055104100000340000b00d418454244811508000d2117941820000b5031140208000003200c1040c021120b141000b9500090b89080030107038180100321404010481c000078110301410721540078464081c242080318070285280c2c0b00e00714510340490124601804020610380c0502041c2558240b030032001c1a10020841c1742c10884140400000000002c00401140070700101c40003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 913395602 1250 913394352 913394359
    0x40618020a082406090d080c0d0e0103140708060123040302090c070201140c0a0c060f021c020601120204060b041e0b0c030324091008010e030301051804050a1406070e 73
    0x503d8949030315849100283c0e01c1107441944040b42d007400356a2002c098600c078035840703510b02c0e50700c0b082c03848555200e400c0301c110400802d180c100350a082d54003901030202c00312800c0020348082d560700b80c4140e82c031000280140d41008850b0ba050400d189144a8120b584000d04540035110303480d5204221085400510003010b51006000c80703030050360002100e041d02c4034403004190701e911000d06580c0c500b80680300094911100440f001070521b4109580c4030421703030503900355009a5408400b61090304c890310511401a8020340041014540c0603900c040755500c024008511150f076801c2041c010f820681152000d03081d1110501140c981c100705020040a540e00b03014107120a10b078003203440c1e0000903d03425041a160038003201e0000301c54400700c0114401410003103241410490903144103e0360040035441d45c6400041e194068000050fa4100d4070000c09921408582c10034451190001402c100d82c1c0f4400d100c44c04000035a07010b500710800c80301c80c000b01190328150400901010b203c9040500 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 913396852 1250 913395602 913395631
    0x31713170708010905120304030519030b1804020f0f060f0d05060f01021903081302040f0914070e011a1303150b01050301120b040302210405090c1303030e040618020a08 74
    0x407070104060302c11b01c012841d800d80380d550724103080d2024412021441c00d480c000c3c11440b686590035901602c1d0810701640c0b007490649984841c50441042940c0282d800402603e801626141103040c588494102801c22402c042619030600940e0300810355895005448408011075800c25483c1c2540616092005040911210034112012021207c0150400105000152800a8040742d4248407907000c0c000304180200c0380622002003640d41c8049900c0d0b5182088100d01f0040002d03000c060301d0061b130003a056031346020700c06080d00c02d00303511007130071402c1c00c1c07082d0f14012411a2a6400031401074001c0341039000303256050700c11a400b40c0b8029050103401d0005011001d005240300705440d80c8a001c0042c1038540d4101a441c000d00e0f0783c01c04c1456a41141d040703400040001c044c000b141d00030b0f1442903950300c40031480310b1075008190b002d041240c5181001c00100c1d209080f03d00070514041c00c0011fa094903201103001c52450f622610210540000b02c00080c2507101030010b500807410b41d00b440c0c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 913398102 1250 913396852 913396871
    0xf0c01020a0c090213050a06050d050f060f010815090c0d150b0403030e12030301060314060a080a022106040609050d030908040b070c09050a060510050c060103171317070801 76
    0x2c10701d9400b40160b84042d54082400c2d24011840100f400c080d100003412110190b684400c01000c41d8800141582058140004a1700b45480403407418000d800c02414101034070540e0004450106009201c100411558041000c46440300440030b801412031000f41d540d105c0301d11701e92809542508aa0340e41c01814140c041200000b920151010f072a03252401c0d04e0b941142000040040240360642801800000000140c0c103806900c0614550304070264104c0e80c4e910101002031280007807103056082d80000403102c0040c0342c0303034841c0011038441005580311105102089417a200b0b084800303c40055a450709101440030030000007685940314501840801e52030340d0307804000d001c0d5210303d0341010f1020032007504000c07211b4494006006080c200300541c0c82d0441c1c2d4000075201c948203031802403615912440c90b4611960465103000e90500046c80b45918583e940000b11740d200d01d01081450003070007902e40c4041d030f091000300207082312000c0000810411889900300340081d8800c000aa14050300c00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 913399352 1250 913398102 913398113
    0x9030d050316080a1d1e071206050606070501142401090302060a140c01060e0f010b030402090a020c0a030e03071706010b0a112e140f1f080f0c01020a 66
    0x1a402ca982516025425450302110078002d042e40d41c600c0818101d14154149880c040001c0e141d8000407120020b48080c04864a100e450710840d01600740d48540040c0d1500100340b140d004540c1050b005072429103404801e40301d450031540782c030006600c088014402d02100c03802c0c264185100c0d0070007141d040301c61102500043c00300071081c03000074000d400101d8070009a601503a04900c01e145440d9603140c1d00c00708020118001d0400780548a0421404d002003519500c141c1042ca060340e051041031031039500c482c0c081150003040100440d408a0f000c10200075218400e0002c0170746c00d0f20030345641e00306c217804408050400d0003903040003550210401f2058551000058464112101180720302d40d0307400e071040c045411400343e00b0500018440ea25a6134290385450903e0000d102d29038090101d02100118540c098540400c0c80a1441d05580042401c022401d4180d0340c0140508446443e0146800d800380c1844002e80c4c0024003a4002c1405006201424010816600800d2010b800d45c00da05503500f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 913400602 1250 913399352 913399381
    0xb010519020d181d04210e10050c030a11120a0c05010b01050c0a06200a02060a05220803130c0b0403021203030f012102031c0f020a0308060402090a0905040809030d0503 74
    0x600315505050030104041c4103174a040558404188114034146d410101400351401c0a0200058010b0000c000d6030511a0b11841c01d499880d2449006503152034066001220351500440c0c0074400e83c01000c5600710103130070f81d40060000c000e00d03440301501010581055401c440340709a200341803200c00c0009080211011441403416a40b000d0002810403130108903c041c030700d281024290010001805d40300090700010018481c4407001e40a1000303a60300c0380c4994040b1014a19004820112608100010816405190b00150041409420a00c01d8481645e0240d0765401081c3c4204000350070b00540c180140d80c044a0a00400107515504000500844543c0c052240050f01510011112070b58a45035588401b81c030f400404a441d02c181c0100c00598003038031104440d0104510b2100b29141c82d0000c41c4c20141c441d0151600b003000e03500e00d002e110196010101b1940e005541e0100442d41414038400c0500071402641c1e0a520342e03100c4001d041c030740421003010f0340a0000c00d10030069038601c80f031807 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 913401852 1250 913400602 913400639
    0xc02011a060f0c07030b090f0c0102030d0e0c0307030305090103060e0408191b05011b0806030a11040902030f010203011d0906241c1119090b010519020d18 68
    0x20150307036a014140000c1d00358024034610505034044d0881c00810f2244030000940610381210990f441e1042c4403001130f03603035103c42050361f000d0713001880801e0412109500c04601d80c0c8002c41558810840e01001030b0a22049820407404618046140344265915108101c05043d80d4072090703c1da410300c1e8036456114096800c240205a0b032255851040318410303003588164000c0c50040c032420200070b10b000d0340070302407555074088403070020515092a207120710401c600404001e0081c0c60640354079142d03450440009181c09403c15200c01c640e400684041020200b0303090b1041c00183c583d41003000c03103401c00d000c00b1500c00819031440d0500501c03000100340c0a400c4810140b558440c0300f0003001403003400c284510300c02d9203c0c81300d40b0742002070090f980106420310320030140000102c1c40601040711803c030711107080907414003800b4240b04140d0660b10480c8040f505042032810940105014104820700c030380c444005030800c506c180d43d06c0d43c01c00c2c2400d0f000c10810340740581080c10403205100e503c28100 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 913403102 1250 913401852 913401859
    0xc0f0414010e1314071d010c05160b0c0105010f06020d0f02071802090f2b0c090203090709050606040b0f030403180f18050105010917070803040e0a0c02011a 69
    0x100d840000d80c051140740c00c07030007009044629181044402d44006000041c609202c9689035000524102d10500b240c9060040c40b4580301810b491000046030f10115480085585104042144400f840e003250a40000c041024003169200740b120308072401d40e40107074042c82c17001c40e090380284450341d0085444a2a1131991811400710000700e0070881c64491307a50700c401080e005101e080c5007003091079001000001000d40700071403082100d000303200000807183e03170044100e00c3c5500307510280015071002c034500074065212500e045840e0009001260b02c156140c1c441644550350421081282d4020141c0c800d070b04550203810140351848891080c0305002035840040300c000001010540a4610600803080d101d50130201a0b45801501c01c2100382801003c444441c514580d111b8031106010b1301f81a01c03010307520a4a0f4500d8106013010300e000628901041d406141800300c0d41e08401c00107480104050241c1405904003445004121044906040704590501c40300101c400854403101d0030034401035 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 913404352 1250 913403102 913403129
    0x501080a0b0a0b070201020f0d0525140d090e0601140a030213030c060909090213050403110f01060617070e132a030605030a1e0f1a040b0c0f04 63
    0x54000030000c0000c80c030140d03441100b01101040140c01c140140801510070303000c0b80e8040c01034041081da24902c0500c081d00107402040710b508001c50504462008400300090700780814080d0342c81e6810b610b104407041e14140d00c00c52002c00030303d43c4140d03d00c00a180301c2e14005c3c15030034642c0009160340c00d0083d080d004180c2c00642211400e100345d040300c40c0d0420130324640036440c2c2c6914040e00100824402e480000b40300110224140d0b0031845690684c950003072103083c81c034018154001c0607001c028000d40070321000c0412603c402c401800a0b08400842d9000068005c6c180320001d0245c145401c1c440311038a1618042014181e000514415407080403130350f0028510f440f5900720081d1600c2c040010b0104141021811041c004002411031100903442c01d01000ea250800d15595400461001e00300003501d103101c1d4800d10700c4117910705242c5d010322011140342400d520b408400c0c000c4100070740d41042c9040200700500c0080351030745030448040901d44e0b191001015100600b405070b030084c0110003070303403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 913405602 1250 913404352 913404361
    0x1b0d0504031713030f0b07080a0606021f0b0a030503040602010f020f0313082205040e0102072004141608061e060f0408070608090c06070c0e0604110c0a151401050108 73
    0x510700908001c42c5d2241000c031100c1c0c001c3c90305a6074440d0981e500781c0401c0840b404030340f03c03600c540507100c15140d46074010320807c654034170303810104c000000201c1c1e80070741c0d00e407600412074032562245400386000c0d000444e80c5a1a0003002402c40c0c0d80c0451909240784140702c1000c285615004071303034012814581c610a061190308003000c8a11610100c440700480358064a881ca1030035100c41e80855004031010001c0d03400d48450036080c1c3c4541040202186080110050325040310499803011840181002403501000708a501c42c01d5001d45648031035140c1c0c11b00501c02c1560141e2100d81c845801d5074070501d83e0500400d400d20414140d0742d1a440749070042128600c2e40124000e039401850032038101c071091a920750026010303070011f542d03050103401014440086030400e10100e400d0a54000340c019032540c641690001c8114001c2e08103a0701640392540c44141e883c0c450003030001d4a00210141038807101c1c0e8549070000400800003103140b2420301d0010807007a0301ca040750307604581080c00c0c17480c41a0364 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 913406852 1250 913405602 913405627
    0x3030b040c17090304080d0f110a0b090115050a090209030a020904061e1509020a1701350c041e0903091a090306070e060408031b0d05040317 62
    0x5084405540040c81c00003501c50103a80a03070366110304141c400d440285900c0b0800240c0d1244074a01851841c2d50204030076102c42c44c81001ca01d410003509182104089107802640c60810b04014400d90f14010f800c420301140741428480e58100814580392801d0f814a44400300c0c2c4d00d06014419040d0300d941c0414001155102400000b02456000304044418503091500c28004c28410040001c040001e04a220541c403c3d40320b103824045900107550603007450010303594081d600c003200c1130041041c1c03400010614421402c004e4080c2c0300b00207040c0203010017080300000700c5240741401102d605000325003005039000411002c0c6602403e5802103403807800c46540e14454010a44554200c9190204500506610400150507207610440c2410507004041e0101c2070740c021540301da40d150f0048004585503a006005c0c2103040103000d400281025070b1185910305603000300300091002e60b84c0d100e5004069800740103140e01200b043c1015030500d0304681b120302e15661540c1130805601c400181d85a5403c9 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 913408102 1250 913406852 913406861
    0x901120b03030706050f040309050603130b04232a060f0901090b0301060e010305480a030219030c0912150c120605030615210303090a0510051506070303 67
    0x1078004d4800e11490030300401600e003c2d002102c0907000521005404074841ca05201113900409010f90407000d9919030f07450304116408043c0003191030000301e9041c030120300d0440342c0c031038907940c4110058080400e24801348008604041c0d0b02c000c0310302c0b4408180060343c0d2a40107503004000903c1c1d070a91151144d40060700c8601550308060720255020000040450348a200410303403203400e07a024030190302c030182c03407a0f401080c40d641c180c02c0c031018600801011184040190912000d921480c081170040c004003200c07a4081c507075840000b030300002c030140d190a4581110501c0801843c00308106041c41000803c1c0034200e01822001d940b51001802c01d21003021000549030300310120070032540d030f2000005031050881c01c01c110212070501400044915001c90118401c0d03081d400c2c1058481c20000800c03502c11814000308000f0400c800040c02c0c1d41c0000c0028502c06c241c0c02005002e95107141c01d00d10320348440d03604e882c20510b081c04108200d5100d1a0350749880440d040d01c0e00342c3c580015180503800340 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 913409352 1250 913408102 913408117
    0x50603091f0204053a080301060e2b02012705060f0c070e060f1807110708190302072301050a03090b0c031902071119030804090c090602030901120b0303 67
    0x2d02908029002e80214000e014080c85202d04004c22000a1707120b0180071900170701400c0079905000422020f0b000f4131103d00f0181000748404025441d818141c1000c1041404a500e002920002c80045580104200c2d580081e0b5241800e902d20542c0c80360712042145014660040202223100e403a084070f80020780e0203090190b0f00fa41c98994851061440000c01140c0452196400700c044024030305055095006010020503a00160f90b6003030710944190b4000708034a07000c1e10403010001041141400b0303a801110203400c4406507034201c1e0400034034202d180e80107100300030707840c070024500320307154000d01c0504031401e00704291140000c0c802079005100741d0002921110f2004104480019034000440c858440c0f000c001c840350031540b10b2042280901c00d0028100800c180c802c40760381c540304010b1917403420305d101801140754690f84c49603c02e412691168210305d44544000917810f40101294002c0c0210348020b40c11702d000da50000780071030308241d18100c4040e40c0304031747c003040d88040c01116900c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 913410602 1250 913409352 913409359
    0x14090907052107090507031b0c330c080c120f06010c05010e0601091508030304020915060a02100b10080a0510080d0e0f010318080a05070f030e0406050603091f020405 73
    0x3e40d4440041c2e014110440d64000024640580c10603241c1404100c900003500b16a104058108269114250b58070101d184000b481140c62001c0e001ca484014071101e0481000d01c040b6403102c2110010308581c03409010705122080500400142c1c41c8841c107070f10750100580c0e803000400c3d102c4100507115440d003280301910f19400c00300040b0642c1c60010380c0302e04807081d8860400c60361222012110001e0090300441d40c2d41d40080000c603015140480489412440c1c6034480d0440c010700f50000351700ca612030700808002d1381082c143c90f608858544285400d0300404c0c0c0301c4c401c0c0c841c0300c408001c00f440801010190000d54030000311301a44400c0b644403000d8612a0f0880d02c2690341200050300503941c0105070b1348119100d100c1d1410551080c000c0422118601003080c00b01802e03540e0f080b1681d04a04190b0f4200141802038002150b00882d1040c08103000b51140040301001c0402d000990b0b0040c0c2206005a60400030301c91003001c00211149041c98860301820f40c00d000c10010700c081d2081c0d9100551 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 913411852 1250 913410602 913410613
    0xb040b31020f0a08040c050105040b09011d0405100f12020603040803090c0a0807170706020601060f031506030624021b040b360910050c1e04140909070521 68
    0x80395004403c00c5d000b10700840301da03000d06541d90011280342c42103010758148003a003488802400c0d402002e00d10f09410200ca00e0403404120240450200c5104460601041d20111400c0101c0d182d0041c4060240000000c0e850b000d00740758022840501c800b501c002c0556100100280c03500105110f04280b00c40c006240441d22907231110311070341e40c0c83c0c54050480c200301da5080f0034203241000030344a01100c50070f40240c40143c3c070b8800141c4011520201d07940906803a01103206000e595000c6031006407820752030000d0f00c1c03401c05503010f1002241e040300c004c980d03425181c1144044c9d000201110500903000030111303140400000309000d86540d2501d9134125013440c900c0c82c4120301007101d40761200344250b04904001003030088586406c4044d00d13061040d410105c1d0b9142d26220320f4000c15404020003504a00d03151060400b407550340c01c0380d42031a040030000302c0c0c144442c0a41071130b403040b48a0b0851301d400660518095458582c00e440c4940741c40f46ca00c110203443c01d40c04034040c040801c03c0490640340d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 913413102 1250 913411852 913411867
    0xd1a07020f100b090105061608030903040f080f070506090a03050a08030406050601092403020405090421030603020a0b0c0f0f070f0b0304030206040b0a0e07090b040b31020f 76
    0x1e684041040d0850000d00030540c501e844503403184190402080010000d0f4800d900c0c220a2004981c032620050320380b2000919000d001c200ca820003107000d0031003030000315651442c00c0043d0484c3c01464000200c2c40e00312000014071218006084400d41c1c01c1183d465035580c000500256406072603501c01885406488000000c2c08070010107035105078055001405aa0380d0300c4011a1522458040c1441d03c001e81c200e214245006036040d001c111001d404d00611b0151070b4000210828000c860848501e1041d0000e00004200d04203010440b110509052140341e042d9030010703060b000e50f405045903400c404a95401640d008000105d400d1030700b00160380801210244807a1600e03a00c0c040c22a0700c003074040002501c1c141c00c100f00c3c0c1c81a43c065000c1c050300d4440c2d948507603568001030800c50a0359200d190342e802b140c0c0c0078000d0310010042c540700010380310400341c00c2c40305440f01481c0a41c070071a501b50600001c0c88070400d5110885441c1c40f00c45850042407078415000f40100a1180c00540e00401da03107 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 913414352 1250 913413102 913413107
    0x721090b0a0f030b120a1b0e060a0e0712050f040507090c0912020406090c0504170a1a040201090305070906140307080312041a0a020306040f0c0e01200a0b01060815010e0d1a07 77
    0x5034024008907c5640102e51584092a1602420b95000380c0000e4041001c00c0a01000d440039500204180341c40070740d1011043c440019110240c07040c00c0000c41280602040010030411180207050050b41031080400028000c0c2c155000d51081041444105a6080c00c5503a584e0040000e00088481002003254040c0000c01c990018051520703002000088186125400180b50200c035500c800b80c40c0c51a059040801c00400d00030704200c4c10b100c1d8140002c40042d030240001c4018001000c80041d001e4605007807044400c20200c0282d0294102c6c2209000481000c0200c40380680440c1b61090552568030380403606049411901080781940414000d0042480e001036009900c12581445600c42c0020120201e801c5038844501007170540410704030950284049800741c0d41e030741d84034034248400c02c2c1140d404c000c16810226646658000103002c116081300084d40c200c80c1c244c0b081109250204000f03024520107050880c45400c040c400c250802c80f078024240204080c10005120703500b49081c02 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 913415602 1250 913414352 913414373
    0xe03010207050627010603150e01020d14090d0c0b0115120c1706220c09030b0414010c09080a080d0221091b0a1401050721090b0a0f030b120a 62
    0xc0b9045050f10445500d05006e01019240c1000341499400d440d40f0b11007000b800d1f10245140603540900c00204050003510891051380d070440068001450100341260400013010040000d0011119003400400e00e0003800b54155007102d203c0b242c000d080080d0a0751038084a035480349078141007013a40c034a0181d020350001c1d800c0d4403a1101d204c260b2512020082900c100b507050110000c0c541c0f500b55204041034001c186500d00e2400c101c2d079500d80301c2c0c49082d8074440858040da0081112444244541003d109600d0f0001491900450080c1002a290f44844003190042c00268000c1105ea6100140d681104c0e16101d500c204600514007030008224250b0040b0344604150064071110400e2490301d08446140140c000d003201c0700b80d030a0603080c1801c005200000760412005124440000d0368180d81300b000082420f0000b1084200840c0003000207805401141109c070043c01a080c1058101c0740c6100301400c942004910071100c040400c4441d842d9065030b08545c4501c010740070601c1300b15405d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 913416852 1250 913415602 913415641
    0x30f0c0f1902032406040b060c07140907050304021003020a0e0a031202071a1b0c0d0503180d0804030f030c0c0b0406030e01090218040f0b01150305100e070e030102070506 75
    0x10381d402c00d00c0c0302c40702c1c4c9044810b00e1981009000d8a0f000180b20307140582c006224048020401070504268502d45460b0808a4001c0d04010242d02000307149860030152403944802c1c1490000d01e1443c007540450b1245480152800526402050302c0e401c0354000c8819842101d4050f1440800c90340d2400c1490f0301200b20810a40503018207507010500455060343c50780003801e20000c16140104101d0101d000c0c9100118401e003038001c80c10080d01c59601c0280c0d1024140c000c100440d120868051a2040e5040720142c60748106a052501400600030300c060f5022240c01c49601c400440040c14242d42000100e84001c1c11404034400210312484510050b00a07034116950030030040010400c5c0908841101c940694400e00740c3c01442508408c00c0100d0398014402c00c0501024001c03980e4601860300c00703070400c0c000100000016600e26074940b0136281d010b0011980300c102c461500c0c0309800c09000241820040110507602c1164644094040714402903001088525074500302002c1c03400154982c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 913418102 1250 913416852 913416859
    0x7030b0c07110d08041e0b0a0f09060203160b0405010f15091103040b010b28080708060913020f2b030f050a02100506040906090c1a0c030f0c0f1902 65
    0x700e40340d00b41803a109540703103e03078003108091506080c0343d800741c0b15040000c40c10031640400800420202c03c0c03400548003000150b00d030380c0c59503855008090050302031030708600215401070011100080c02c8903103204005400220f0b049440d125420310a001d03081c0880640915404c08500318001111043c031030003211602d07071040042c1240543d554160307120070303500902138444610040c82543c500030000d11000c41c3d0000c00070328410386184004107404e8080385220101c1e48010070440c00d1500080c4550340076004031041c1440c1d02e40100074400000c035441c8040e000f400e00d03c542c1d0000d0349039400c000965005003001c8801445864644c03c82e540104d140480000d500daa0002c001140a841583c0340b6078020340241140d601180e080f00000d280041482e68466100c0c078451000c144113110742d99565010300c60103040f00d81070011f5200e128883c1200348012240800140d12205030120a132040d0802501c01c3d255203000c0c14400501e80071a071034000f41903004082c86002002e940c0101d10b400c0724820b4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 913419352 1250 913418102 913418123
    0xf01030212030a021518150415110a120f0f05180a0201090317160503030723040608130b1003030210020435160303090509041a0907030b0c07 62
    0x5400c40d02e078040c5070062005680300300c0c11010000c09040350164400400c040c500c040c0c01103201c801e854052071000e1000c85d010309074140000c0c010307680031203410100351501c140280811320005a07114402d000040303040080c0a240c81528184941140d1251004500141f0a44180c908070038020f03c02910056503841c0007403400b541044c0089030400107240c0503110302c0e41d41491034484400007141203001d085102e108002000c50945440c0220800c58080d000854a0385040d03200176140f40c03000083c3c5015610722103aa000c0400d15101150b0030703542c481c034150070b0a4803244410103190b10010001044807811204022944090034100c104880c041d5003110305115035000071404a00c550300501804500c080070004640c604c42c0c1001c1070020b0400d10345800170003030207402400c4c4142203040f0601d0071400d66013001419480440e800240000701d841c2c206506196071800c1c0401d0a0340b11003040020114002242c0b01000c2c0102401150851205441894240906016544503030700448152818 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 913420602 1250 913419352 913419379
    0x6181205071a070324121b09090b04020906010206190b060d09050c21060403030504030216060305061206090322120506070305011403060402040209041d060106090e0708061311030f010302 82
    0x105c500d06021941c1c10702c200000c801054076407841e810041e0100c9202c0360f0320000e00140d03582407880b4081c800c5005840c5841b0504062041084100000c3d02e00c0b41154410b00178840005840c401d100c0000038141400601e1032118000b080c040c0c001c541c20060701a00e0000c6410070700402141051654504541a51540b140f09609205c15090004030460541c440e00004c2c2c0042c1c00b0b82d1200740c0140c001e0040324a00d0101a21595000032581c0003140003d848070180051818400400700c2e00c080e000010b0556443c2102031981d982c0129040c0d181c41291822042840105160059016110f00c400020504d0500d0901950b1400d043d111a0700080c54003000103529440c4040440000e500107000d4100c1c1e848035001c000294101009150b44259100e480712110044180e0709a030880032100645803540c506600940094815403100c808150030004010f0040e40c44151181d000c2c500704c50140090103c59111030041403101f20110801d10004180214595407980c028102c0c1e10031550034004108 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 913421852 1250 913420602 913420661
    0x120c07030c0f1a07050a03050307090b03100303020709020c100b1206330d0210180e06150702090118090614091204082d0105040f06181205071a0703 65
    0x11303140d0161240d0858500180002d200b8001950005114a490456151a101c509400d42d10981c1e9406944411070820020107406210910003004031503001c60922201c001c4403071310b400e01c180100010a076070b00b003a280550754050004d058000541708403043c600e403884002d040d240319124246881108a0700d00d22034411b0a01c030380d901140001c5c00070324560105500b80001340d100403c0e01c0e03050040031010030329416031720410000106408800a1450308000c400d100c00501c0d0041360f440402c8081080d180942c41c0c040c011411110020614015280600c024200070501010000c14160a0005c4103031400b50034034141d8041c01d10790742a24484511818058058821072081ca009500204e081d8081c03080c0c07004452540d40d00d03034007040d0842d60403494102d0031194222022109031402440040501803030f841948481c3c41e666040c01610009911482c00c8003504050030420000002080c1c070800110402070940c1d54522030f100c8045042480000d80a0b00d20981c0305020b00c520b8251240341c50381c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 913423102 1250 913421852 913421857
    0x30304020a06030c030e19110411030705070303020d061d1f0b0f0f030a1d010e060103020904140604120314130f03110313050901050909120c07030c0f1a 67
    0x550051070380d03a2140c6442000da0250203100813000625650340442640394005100d03500d011a002c1000070070b60b50311840c10901e031060042080c3d01a61a00003010300c10b05240c01100e8200f44141042c945410243c50110081d02c500070428290030705100700041d0001d10100f0950403600740d001710001c95607d500c007080401c1030510790800c82c000000e1040100e0b0024200407c0d001c030361046040e180140100c4090102d07841a52000421640c40001801c4c08415048190310154004000e0100d40c07001c1c0da180da40c3c0c05040c0400703031007400c1c280045020000034044403120000160155201c601d424240701d040d504100508001007410403000e0220741c04007800c01c40c072482604001d2611038040f0b0700d46000d035a0410030103d00b03000404000141140c070401c06040034821a0b080844201c1c18001071001200d81a4440f6014400d44410311040e001c0c0030540d8a0700d041c2d0904802d8a902c0e01843c418a0401c7c00c0d030000d0b0070b800201101080801040c940242920301d084160044009100c51202142c0b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 913424352 1250 913423102 913423111
    0xe0603010e0c01080c0d060807080f030a050702150d2c241b04090213060503130308190c020f1b060a11010f0c0224011a09150a050301090605030303 65
    0xd42110054520743d60107840c034a0340019000c0b9000381030850599503c0121501c5030040d8405901126040101100030020104c807141c1c0000a581800d4840038040c2850140d00c3e40280b050040b2140a01b81d40c03076150940b411034500c0e003000d10140801c250a044440c00013520102c10b00140421048410790000710074074001d03030b07000742c0c4206140740c040007032581a8040d00080d560308000d00b001d00b484200a02500241810040c0103130340e40c8205201e281c401d10140d0040c0c060110070f004100440e03031a038a425020a4143c14480d4440d074a10b403000103525074842070000780600d00080c02c0310007940002c3e1221041d00c00c50880d480c0c03601d425401080c02c0c040104040d401601081402171942c8981d04080c03d1032003c80000c0f80c0120581001001e4803645810100141d1142502041400584440c045841c44152050005504002c0069481d4459143c10a146040080c01034030a4840e81e8140c0700c100d04281406840380009003005010382c2c42807051008103030801c4004207042c5408800c0724090b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 913425602 1250 913424352 913424381
    0x30c080108031e070f0b0f1b03180c030105130605010e090d1202090901121b0614070201020a06021b160608070c03211b020a0c03030e030a06150e060301 67
    0x14854590090601c081810045507200c10701402040001001040e44a032011b10420308680b00d850202404450480700600035081c00041d00a5100001c2c2c0c0d44007145c3e007081c0741e42400c0b80290310000c4054600812004c40b00c2d0190328200c100512502e20020100d1407a120703080502003a6a6540c402801c0700050b038a000c882c0c4c02841c07a011806000d05003081ca100c462a401608003401c200004210304001d038042465082808010b800700076488112b0300c200301e202682d00d01d0072820400010000c52044024000100e00012004107680c006c01030070404ea688203005654a07190400c07081183d120184800349203210360362042494201200060041e1091680d50310345541c0c0f810f1045802101603a01503043c046000909901803501092080b021401c1ca080815062044148034080c0881d5402d02c004540107103030307004009058104402c0c11281c04d4644028801c20100000381450340c04080180304910304441d4521890b0040c1964044441201c0d441195039207100905080c0d13a2081c40c0c0402 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 913426852 1250 913425602 913425607
    0x1116030b090d05071a1e071d01020a1127011e06091a03100b2701110303010306090804320d081b030405130203090d0e2209150c030c08010803 62
    0xf0021001702072a0b02c501c104ca40e82e401e185500c00180302d4844280c48282c0000d00900381114030b414420403040c0400300030320040541c034145803541c0c00021040f6130103920071900258039400201c1c180c00c7e46200900c0751250480c15581d1803070316250740c403000046015042524240007500134040d801c0c0d1030464900300340c044030301304c1c2000080c54a41c5c00204055055928040c0108038040750501509410400c00d101c02c0f80040004010309090002254940c10081c0d00c1d2201464150044141c034111303a0b0084020403440034602c0d2803c0d4500464001d9041d0401c00c07440b060711100e0280002014004600200e41c00403034000c144000400003400103000e544081000c00d0004002c0d81c1c501d0011140102520b0810b521100000c00c41c80003184040440c5801005200741c0b810b091000030b1181429080840b02c5003141000314803480144008c0c3c00d501d0f44454810b0004101942100d41c0c0c9076481458100c1382c40352011800000d250440769480000e2070035180082080c01901658141ea10301c000450 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 913428102 1250 913426852 913426883
    0x140708060112021f050d0b03030c0c090a061d071805060304020609030f0d030902090a0b0102060f07020c0607140d11030f07080403020604090b030d080c07031116030b090d0507 77
    0x1502c06064400c0f60054a140006104d1096840700d140d07280780d0998640d0b81d00e90203004910305580722080306900c241c10421120808000000d051100800241e0b02c5034469511814020300602c4140c3c40005049a102800c6d51070529015480c0e10410141c0c0700c0344004881c010f00181190b01a02075280c2241c410000f140251403c01d026022000c03000b17040340d0340708a03482e94403400e1060b003000300c2d80800c2d01d81030102e0841c98034070101c41d0b01110000c4204112000c03400000e5031410701034135001d003412850022070412072003481b513074160b0400901000c1d602c2c030251500010301101038042200307600482600d502c0a0388254030032100b84500c0c030015030800203400704004541d40a00800c0b60100006c200010068440002030030050040000000f4107488032014141030004d10110941003140c010100100701d00707140c05440c001c5400d4503006101d04070b0204410300c4c08200305240144120580b0b00002008440280b040c8108940002e0354051010b080d41074a1a002c0c800700100071806251004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 913429352 1250 913428102 913428119
    0x603031409030d120f06060207080f150109090f052d060f06010810181d0a0812180f01091b030b0c03060d0f030315270f0e030a020a1407080601 63
    0x1000007428140000070906401170950b4100c409551080340981c0042000b0094008203000122500308040094a5091003031402400018814007420109944d0b40300420180101d90411444865001c4211200d9403420800e8085003c800c0092320200c219480000039000d402142c10b41c092811000004801e8035400e0055a04074002048441c400c600c01c0c4000074412100759407100d1340070300c445001800800400a8001c1018000880500c80c1e107c03501c1d03140090343d100c0c1214105446d0102044a645a03440c8454480b81110b41180781442a10043c1842c00320652190070310038425918800d800d0200c3c4084240c0580318070024202201c030500241d2400c030260015607001c80024000c800840607a5516030030050717190b4055000a90350000880e031017040c5810300010b460f110500999641006850140e400d0800e41c2e10403420391a0740e01d203402c0720110f030051104e080c40802a2926030558445c000c0d503c07861404151003400d007072144c4036031404000c103802003a10010405030103107a0810101c0d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 913430602 1250 913429352 913429367
    0x408061915051818011109040615020a0f1a04080d0f050702030d051f1e0608010b0904020901140d020a031422080409022a1204090c210603031409030d 66
    0x1086268018010180d011030020320506240400307985121f503c500ea160148011030f17525402c00000388419265814405400103400001154803040040340d40d121403034841000411344c0d9001c0d00315245078040c8030822480001510390004a0841000032410084d428410f4035004c3d01c40d10f0168108022000705103ca0f50465544801c2c030a101c0110446558401c40b03071b5030f005501011050084110400b420484040300e00010000c0f45001c00c1c0b903504124001849100d440009845503130300060346410b503400703003030340104c5072000840740b03502d0700c0424800c1030180d0700400310040000d141200c5100c2003810740003101e00640d03091301450074080703054a00a6480b0744405041d10140700601c80007548403d180010103e0303403482380c05403101a010341c440c0d00d001e0b420542c019400e43c00501d04503d4015404c0c0954044540b03203680840c4100300904290b07280c0100c4d40075400c00703001003540c4400c0c1d80c245400c1101102c1c0300740d907540d000740034080e800841030103100d0840398160043c01914514600c601e50 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 913431852 1250 913430602 913430611
    0x12280c08130809030d030b10080c0a050c0c03010c030f0c090b0315060f0a050706050106170712060801110403020f09100303050a1209240207080306130204080619150518 74
    0x201d030f140c11407800000b80b5044d21400b0150019482e02c8056070f583c1000c201900c020340c01403c0c1603180d42007041c480d0400340501c1c2004401c018001c52424074400041043c1558400c01600800120f40d00b0321005000d40ba88007800d05041d41082c1000d031501c2d10801e10f0104603460440d0301c0d429600c98180c426403442910b00c003141c0c4003405200c003e030240605802415802c409840780c81d0349000c40e2a00c80c0c10303510141d0141c0280000c01502d5900c407464000c26690096641c0744c960310a80410364031000401040d004180950310f400003075842000b20034014002e881c002c40c1c10154040c200810401002012220050341d010a8441000040c1c0100e000e403100340c61900b494007012002e000c902d000c440b00040b0175180d45d42112001c14140b40e43c141c1607050070011140562400d1312544a00c40300c0d02c0041c03d0180a210110311500343c405941d8141d0780500307501820380e1712a0400c156140402c0001d04015a0414a00031071052000011400034080300e801030103000408040402c8032850700301c0240b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 913433102 1250 913431852 913431863
    0x40609080405100c0204060f0e1816080703140309150c192f0a1e0f0e010608070207050a030b060a050603010906030b0f10030f0812280c0813 62
    0x40400c42d07540d0782002900111071696005064180e0f801000306031075440c0d10030704101c1000001400300f2202550000c1c0e004e00034140c0e0704001c04c15803803014601620750640705e50103440c085000c2400d45000c5043c000f260701a100291218210040382c50b168400c2c609140d901881c8108400b025400713103030180003107851010542d0880d000c402d03403414002c4a409421111110408010001c0312081c0800c40c262881d20b803403030884c2066000200f80400c00502800101c0c041c0800030000641e003804524015080600480300300d10350b83c02c0444010709081c002c48002c5001c200000d6002440001d01400300c071001417200442c5461501c6142c916800508816041141c80101044a885005c0210f00a06004400181c07803480c0d81420825103c0142110f800109010113000c810120305e06d500003500e8001c50446801c41841c40c000016101e6503220b010501c507003c0801051074144a100d41501581c0c48008001c151aa400b0104440078100d1200c08036900b2008035030340e03a603549214413081c0d1040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 913434352 1250 913433102 913433107
    0x6040308070306091b08150105040b0903011803050a1b05070b0d0e0d020c03100603020f2707081012050d0503060a121203150b0403120905100827030304060908 70
    0x5040d0042078405c0e002c060f21139182d03c00c503002e24040d07101c0001781c0d03c00d8520800700400210480024080e02c1544030b0348c11203010214600da0560b0b400e62182c0005d0b0411a001c981c6400c8901d80600ac0350031000c2a4004588105907980c110890800c010081c5030f232003805444c01500b000d076582c50756040101544090742d43c3d0780301d003e032001e41000146000300700ea8009147d6064031200f00b61400d13034207041e50140f090400b0010001a1503008080c101c1d62411100a40c240c41d400c80d03024544170081d900d4800d501c0031902440038142e000514a80108880d280001c115a140c1225140700b040c5110018099402007020007400351140c2d01558110100404880e80c240e554118410940807041c020b5407104409040e40061076094401e45507291352407500d8102c1145040041c011078019480094088072060000c185d4861040e0300d040050320000f0401c0c07c0641ca00e520081255104540252540d99440e60004841d40601000104126840029890340c0d4a41c1d4a540281102c40000c0b16107007800d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 913435602 1250 913434352 913434359
    0xc1704080a0e030f011401090902011202030718030609020f090c070f030e0d03080916121115120f07031a01120908041205070f030b0a05041b08010f1d06040308070306 73
    0x1403242500c2113050303100224041a820500c0301c00c0c150103901c04c0d500b46180c0900440141d820542401c4020842d00c00103880f5642c040040c0c404560618490301034403200c40003c810059a0340c0141410780c000c3d6601c2c1000d920030401e02c110b840c1c0a85041c05402e20600c551000198031000700800d09200c1c1c50801c0802e108540890034810300e1000440114000c003040010030350007001090001700640d224607080c54540060310b90b03070480180c0060314402d800c090f418455201d4090050300c00844000c0c980d55a024403840c1200210141c03002d008005c404070100e24200c1c403a024441061100300500903808078047d005440768004012500c1d509502d51101802184410010700000c048056072032500f07001c075180907418204160020000e200032003505001140ba01c1403155407042d8094000500394685060a40076214041800ca502d034421420200d000c3c40190030034584550001014040c51103180e1800090280012100d40b040c0d01480c00200403921500000740c1040482c100015010b44 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 913436852 1250 913435602 913435609
    0x1101030e160608060f01051209190b15090f190905030408011b050a02190618060b0109140d06091a010e010e010b0307090501031d03070c090c1704080a0e 67
    0x703882950400e45000c500c08000c03181c2c000d40c529501c100c00b260b090041070400000a8000d004140880c0ea41d00c0244000640b0b089082041c5c0c04083e010000c0e82c5403e00d514500642844401c0300e94134180f0322405000c1c40b4604103901da0500a00c01c80801e2401c0d60354507100c1e400551400d290315401c498440d10200c001c075406100500c0a0b150480000c1010083c803103001a00202001d804410004100864510141c1c040f980329051080d80ca452004003049003401000307071000ea1407071821401c03113884c00c01c03c10400d54081c500d00e00003a00d91828965941100520100c0d44000d41c5c0d4215000d50000d0300020250780c0700b4034015100d1212582c81244210f01103c00b01801d0b0070007284d000d1814010f2122013078120205005018149400789185012036005007030807640e10403c0e040c15102c410346142c91842a8100740317040010320460361501c0741c0e414245a03200d45c620074131107a40d140c107840302e041d10301c18a00883da103240040c42490644440d5140c03c02c2c1c1d03101a20607803c001040c107840382c5554 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 913438102 1250 913436852 913436863
    0x603030f070804030218130b04030504081606080c0702090606070f050703080c010b0d1e020604091401050406050904030813050304090203150406090e0d050f09041503120f0c1101030e 80
    0x42c01414419112800d52050022110f4110802540f1140810801c29606080f100b4a000e5590080000324984c4480c41e05895030301568028a10741e00408007100c982c1040222454102d4580303039107004590321034004000b03640c0301d040700194100c0c201000149071414440000c140c024416074680c5c2069205444160400c021904100c950400c002505400000700b40110380075000100d850400003a0f280e40c40001451001d22170840503035213501600c0956851006490091034180002d11051131071503081c2810800900815128500d001d202047d142003851b81a44200e9168441000c1038a030038411904010740d03003500300d84a02c01088049900d40c018009907001e450240c13540d680103840d660401c02079800c07581208200f00d1a0012000e5404000607a01c0c00d40b05541c00c1240d900d1060a205039914401c2c9000c0d2030704141041101a544603d032402c14086a019041b224481442c000301114804861100c203000900c08100c41c0012640e4040c0703014105038141400559036070072001c2da50070007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 913439352 1250 913438102 913438117
    0x151d040908071109010e0f15040203280207031709120d050118050708010b0c0c030610150203030c07060b060d0f15080c151e341a0603030f 61
    0x3030000b290b10010080e050074804000d507030455407600300b0740c1409004440132400400700f030b0055543c180410000141d110703a182c580030002d0015583c0746048080c0e00d80c40c4041c1c85020004015000440e40900c181d8820390708490744c155501414075030070158041c81034030080c02000d500d0150360b0030110040b002c44010030190b210590041040c2d85001000d00d01a0b01140440390342c11b0030401002007040d40080300c1410b40c0d0003982040d4485804580c907a190001703005e032243d0548140c10620034185181000002200d0768800f10003076044442908a0b01c81c002602c034204100c809002400c00200f090f044a091007001408403424804440301d2502075410700d00c2c0d4070020941d01c000e844403504003c08036001910515004000e408602d5011a034803d4600381d00c0301031083c000c240a080207020410000c10400f4009c801034450303080c00c21940b549840c64102900d01700030441d200700302c00506249500348036041150001010761a84044042c044024422079042c04108250403c9030303884400b60940 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 913440602 1250 913439352 913439363
    0x140a060b100c1104020d0b09090303180703031d040f020d0e0c010c050a15090f0303020d0b1c030807090513060e070221090102030f030a02070201030c09151d0409 71
    0x1100203201446116000e00c03022904005540e040030000c511031000b111401602614010707521708145040000411002c0b0340d0303c1d84003120000340009800c00201560203562a942e54003d501a4880c503159981218070000740800d040c240180c80300c0c60804136402030703000090001701b40c0d01844100c140881e03100b9003c0e01c0803180c2c0c4292491882c1401c100814400c0028200344080d08025201c2c0340d540c0c44020401040d0040c1400b1169007030301c440e00025140b9a0200c59445280c00b40d24002e806504006c0309824917500d0440c4d540301c240341c100b0103402590f00c07203840d680c26680c03951800c40c4c40300ca0040480c805d02c00c9078580082d032034440c00c08941075009442130020b01c4a090194440b05114007400360b04c2158090740004c40b80b1034074080c030314591010401000c6e0340c80903039000507030079801129050708030b0a00200403c00140e203207400505207d03201b6a010041c4103242d000503200601c99000741020b0140d5203070783c8090b16000d40904400a14501040c1441c2030190000400355890039504842 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 913441852 1250 913440602 913440611
    0x3080c030d020408060712150e0907080d08011806050d030509011701060e0406230d03030612060504020907030e030d0c230406090801050c0910180f1505180d140a06 72
    0x2103540c8000a0100310707c0040c0280940c2c200f4030b10f5200ca0381428000d01040ba4550700c0420345181c0c003004200024241c01083e01c0144416003030141034401d00b441600c0100c0754071440c416440b4203a11511003038400081242c900040623480440312a0041003486051125110300a03101e0b58000c1c142c98000c00c5983c0e200c00c144c50310041030000b0b4902d60750040a0344048000d4a180e03814082060103004001600c080000e1030440c2400c401801c5335900c20310b0003100c0241c0f1901440302541016125500a551091544d11004021001c59070701c6182e01c80141c00c00c0c0184030403a002c94008000b911a1031800c1600b00071030482010394003510105090501c20001401c011071600801240010503007076000300480d14008680405921951007010710810300d001107520080c3c0914038401041100b40064561a5160aa515240d1510b0300032440114200401600403074416011101603000c241404c00a80d84100240154046200801c640c071707500492181150520400c40009010b014082c0420b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 913443102 1250 913441852 913441861
    0x11070e01080c061e0307021e0709110a020618030702030111030f0f040809010c1419020a23040504140a06140f060607111504030c08060705040f03080c030d02040806 72
    0x6140c00b401c1502039020304002e101c4200001c1c0d1102c0b500035407808060f613142d07030f0707a64102d400c03810258080304020a001d425400080401d40000f11901613842c030034008c000c040c105404400313040c064144000c0050f8880c00c0040c00800301040524030312a00d01d01100d0030316009500090070744102504590601d09c000c010000c44086102940342c000513541d20724660f41c10a512107030200c1c80766419071030600c1204512903081069401a0395095002d03441580c8900400204020030412229000c4c0c0c81003107508404102d03610f4240d8000548504400e803846e1420712503041c0300c06004010410707a843d00004d107120070741c1c80051042440711807245000041005018061003c4800098211005810300a04104103030f191401100e1500c0d412840000e4154840000038907030058001640700700c05804036001017085244041d19064032883e20544142d96100c007001c545501542c070441c1060201005c0c100007083c1c00030000c00080c500e50050f64070342401c600c1454166842540f01c1c1ca0141d0200c0c0800 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 913444352 1250 913443102 913443119
    0x1103070c08090d03020327060a0e0609040e030702011d01020717030c07060c06051b0a0c05011b030e07050312091005070b19050a140a0e1615091517060111070e01 71
    0x9400181d201c7e54400110501c0c0d00105106015111400c4103000d48640c01c2842d55440360150b41203000010004e00031b00340409040c64881c0c124241c200d0100b040070301c01d0300700b20703044102c50201070314182c0c0209542840d000c0744003100040c0c8154007050b03000400c60010021001c0c008400505248e071681c0c8134a035103d2501c0000c50b00d000300a09d644030350403162407a01d0b64910b000c039200303500c0c3c03803402c0b00740811107013801c1d8010140c0001880b10004500c0f18940c5641c0c2541100c102c1da0070711320036101c070760703558105140c1c403484d49099451a8540c20404101d061030101d1440850000d185403c0e07003011455aa000ca0115054030b040038031441140c2c00c0c01d000c810070302945a002145007018001d9400241340c5401d0356201801d6148404d407104109148000100600b002c616152803505035007940d0380801405540b000010280007906909000c42c0c600341404420810010507554a2402c4600424030303074032030b280581040c0c100084100390740c4007401c080002802a000e0402d01140e5035141080c1c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 913445602 1250 913444352 913444387
    0x804090c0c1704360c020c010e031219180b07021e2b0b1005090708090627100515041e02090d05100905101103070c08090d030203 57
    0x50a0805608002c14480300c0340003902000d113000c80740d031200e10b2045500c1800d007014444405005001e45001070110740603500140c41401c010007a2038058841003100141600c1c0c10340c1807415031007024100100756101001202d1781d00950214600f200415081c54402000754450b90b00aa030706e52801300c1c50300d0540c81c00c2d140c104100710010518000e624004008608042c044041c00004000c11541140901c541c644641d400180d0040c007100701840c24803075000391100d05001c1c1501420741c4000213513002c0d018404003401201104020301450f80c0300706c45a005070602044461180c13003000700f20310b03200c0d800704511620360910041c0403800e071800e0345000300c0d40c00e00c2d287e00300d00c40c07410043d50350110741540007007180c003200421001d69621840000304030b00350701103440100a0f02c074401303112003500c03a585c1c005040f140c0f090f070a807404c10b0608405842681c0300362200d1603000f00f080001c50060303401000c040e400c0c00c0c840d110a07410728074002c0000c1d034102825541a070240e0030000b480700800794001c54 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 913446852 1250 913445602 913445633
    0x6070e09070e01020a02130e07060903060501050303040b161106030123030c0a03060917070803100509040210030504030c080f1b2b12091208060a05010e06070804090c0c 74
    0x50a81c2c80c03920510000f5910440c244000e805288003a00c2105550b14a411222005d01400c0031142d0341503666400030228802840181c3c0c06030324010011075a845e01208450840340075402680c10030020954207102c84c42081412500f03680040c074a170310315858020282d40289035441c0b011303d00050f02c83c014103c01034240105480b0360030040350b40c4815640c15983c0010303640c02000c0054010264503020101200e0001c070702c0f940080c0481d903003003002000001584148120180c060010b0b40c1e40c007c0c4142c00724150340080d07010241c601d031482c00310b104c0c0d032007164814004c0c41c205003100c0c100c0c0c4a02940b641712100d040d80042c0002801e401d8a28a030b20418203025050004104490a003496188446201c2c122061042c03a8080d40d00c8100340b0500c00c00312130264100c000c00200005140801e0303c0b0700485c11020200364004005992813512030b04034030844e541038540c0c2580c0141e0800304000360b4001071b802c49408405000200344402c0d03134440d100c0c1c0f044154880460110060a001e00c03100c804e140c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 913448102 1250 913446852 913446857
    0x2030726060f1602030904110a12090201170c090d120905013906060e0103031b0209060111120711090f1b0703111605130c0c1202010e06070e0907 64
    0x601503450b0310703081c40643c00a07010b03042c05803070084194100d00358868418269840380c1800d0500e5049000d180040c407400007642c0341d9543c400d241c81c142c181030303924020020f404a881c0305548034450341c0101c1082da221600c152010b2900c070041d000101e07140a41070301510382811100c0030810494104034103202900e024200031480d201c260400c00e03a0184514100c02c0343d00c100700c2107616036020b0407005417040c551081e03003407100640f100020352500ca8244030641c005801c2050445210011242d45500b0a4001c2c1c403618a60b90341a0066940d06100380e110417140c0301e40704405c1450744181c4080d1110910540c107000d400504030040095480d000b82c40e070105040350390306201d4078078040020344410046c8140c40036141c01d00c5042c1951051001c098031901c0d03000b43c1014485076182c020044d400d6400485038a005033300c66001000c2203c2c1d20600900c003180e44070000034042141c1c00340c25240414107100100c1c00103200c9180b0341c00c1c280300f079034240081340e03080c1d01758451481c0c0840384580c49842031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 913449352 1250 913448102 913448113
    0x903030b19050924060a1206060c02030c0103050c0f040e010e011e09110405060403060f052d04060e0a050d1704021f09030c1403151b1602030726 64
    0x40c00700600544100460618425103590744c5502c04035585200300001d000d551107034160031014000d03644a0900340d01a500e45000810b00e54050f00208901c103401030000d201c0252504010f500400016140b0344108200303000103280c04071804000c10240c0124449401503500d0079242c842072200603048010710f440390411155481c1c110b0306401c0c1c211b40c505240030480c100f42e01014a0b0701c1c403503034108507044100064040240007160700503e001c041001c504201c40e07907903a04501c808039024802441c059454030341920924421200d283d4209005440c000789010981444910b040a024000c4035550483c00300f0600182c1c1000041c03400c0c00304c8155100941c036250f400200517a0460315082d06002134403d4800c1003c3c400c41d122009550b114402c2010140c035180c8454211240480d11842841001c102e290400040c030016030244020b13030001d440f5181e032145050b0903504003203031207600c864070884d201d805640d00b04401d02c024a01c14002010401c3e000000021041d1024090240d50f07009 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 913450602 1250 913449352 913449359
    0x71d030628090209040605070f020f0d031515030b090a0519051807080c0a0b0c060a09080c120433052d0a020f0f0a0615090903030b19 59
    0x2000398110100e20354086902500000300c1d200006180c0c1220194200b0003400c100701c200700c01c951196001e06000e490300d06007501e004101302e07070341d620344c1040781740c00d802c00c100d10450f460294100b81c1441542000c07040e440780d200c0305040c4108001211010019480d080c4c0d180c40c03428220803194100c89142e4050045240030000944041c0107a8952894165100005840307545099408944800528207130707811690b40f441429542d041c3c000c045403050f20b000d04d00059504002c01219031840751400074000b2a65001d4504000300f04a030800d80f240b010400000e03021000c01e026203200000c101c0d04040e00c403130910300c48402c0b0308107800c1000201c0f90740513446000500038180400c035640280c5089603598100d8401c065040c102c855441100d401803040c928213112020000c0c100d184203507401c8440280301c4681d1144d442d030a048403800b407a00107c80c0e500100c0d0700f5400015a00c24090507640c11155200c1c494011561a0181900040c0d51807a03601101d01d00344241404801d1604880c001d220305 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 913451852 1250 913450602 913450621
    0x80705041a0307090518010303030e01090510230c0406200c0f010e0a03050102071b0e010311150c10110906250503161b0308030606031806071d0306 65
    0x1c1801846003204004800542e40a02c00c260a502800300076240c3d0610300500e0322034035600d00c028041100030034242a1040301d403801c1480703800a85508440100740403a660441d07500101302440b403030003240d11b9070030003a05c41c199044603440c055071161021541d107610b001c50040024141c0786008a082c0c58003129141c491400144d00e03070384500100c5451782c50404100058990b032106140c510380080c1440350010030b09c1019400f42241600500f034800140314488500341e03001c0c0e958022510791120000040c40850450500c6180e540805400d520246111045441d6150070181503040c1c603610a48598492404600840310b105003811010303400e1146950000382940140e509802040220841e50400150303035a034240202c0d600a802d0700e66400d400250380f40c900c0c10042050391201c00311180c894120412000c140103d94222003c035003180c480c4003c00030541c7c00030740385418509660300c00c4580998188401802051180c9a50701084d42c20040a2005038228100f035102c0d40004042080449 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 913453102 1250 913451852 913451879
    0x303060b070b04110111010c0507051002090d0b09150a09051009050309010e010c06090302012306010512040305070b0f012c0a0902060c0d09090612030e010e012001090308070504 78
    0x6030b00028000042d005000103c0d006d4201e040c502c940c075820680b00c81c241c01d030010003c105180c000c0b000e507104080c1d04901031003070b4481e0014260b00308080900c04000b00303500c0070750250001644010303034543e080149050380104500740d509080e4250390b2050141003000420820051810358881032210007400d480c3c1503102c2c000e00c0c81c164140500151032103100ea118104214140364008410000c04805040090081044508c1c2803801c00c9900d03a00d040071902504041e02c81c40c0140c0d991458080440140c1e0384c1d00f03001400442c1400340c284101d01c005500c17040414820b0183c11800c0718150b00d130141400700039040c541c00d2489081c0340c2c004400b9010340d003413a4961200700c40d14040740c20101c61021850520840b15640140c0c020b81d40c50f40d40603a03002c4094011070306c011f041440182c0e210f030f00400e0552a400c0340100071840314200111154010240c126680030141040d0501c288102c83d2689010350407100030200703035500c2c0902820180c001001e01d800000c5490200d0400b800c112011f44c518 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 913454352 1250 913453102 913453111
    0x31b1606030e0c0405040c0806010b0415052a0a03020d05070203070e060a15030b0a0b1c2708120f130f0813080102340809030c100c0303060b070b 64
    0x551030b088100000340d010400d41c0e03a00e04000d00204100e01e031504145003070401c5801014028054240001f540d40d0002040d5401d844c0114074890b010300d034865064940e50f0000011010b02e007a54000044400c0220708503221415800707001e2703c2d000019150007420300001100d4142030142c10b11159026880002d00c0c602511520304100d0710316103d03c000190f22810a80c40400c49a81c1401040d000550540020001d03540c01d40d201d451140d00c8280841040c010462025441034100542001652098000001808480c003074a01c03440d0f100d80b98126902c2413090181c1c3da4000c0012002d4000d0400440039030b10280c4210b000b1040c1c105034040a000b2003000c00060030401810b0503400c1030025220440f0300810305003030030488056035816004c0c0030303400941c0851146021008858a102e00320040d04140100c0400d11900d0202280e07101030458210f011040c1d018483d9501c000000d80762810f054258954a8540140c5c541d402d2070000c041c0d0780d00e60410081c014043c0111000292100150b43c1c01 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 913455602 1250 913454352 913454357
    0x312080a0f1a0609133204110405150604060504050f040606050a050a02030c150f25030f060906030c0e090703080304330509010606020601051003090302030d0e031b1606 74
    0x31803c000000410800d55150640b925034548240c8500c9160306d1645e801d00c02c4840703840043d5018000000450088003141c015014402c00754410640e450560304c400d501180700c540703442c0305125050100d00c2542054000d40e0110b000000c0500042c80c200801200303000b030480d01806001c0c14450003c04074007074100610180030002c16a480c0307044c024400d807501d035000401110081100140290f45080301610007640302103581001c01e03403140040102412080c02019400800700d01480704030001c003480a0620440342d45e4031404039120095002e420015800703500303251a5241085c0c900080d256010b0320106840c0e110307030802c01c00601407200b60f80d8040c0d040f10510000082c6141001e5580701d08802004010148092841d101030082d44110f001d50100d0008012480d21900184da03500020300605510680d0701c03040b604501c0c4680c004000c42032281c81a81e041280104640d0103030f88803510220f4030f07030304003041d08140340e4444100005d10507101c0000701165126841c00c0700700c15410707000c2c0004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 913456852 1250 913455602 913455607
    0x510091a040b0a030503071a09031801050a1101182d0b1308120708061021141302011e0c2015030109060f030503030118060312080a0f1a06 61
    0x440f5920350603020002d58101040da542c4224600e0841b0441d000c100310a458494480c1c049040004000250742d0f40303000d01403403800070408103401035803650800000c6004000103043d03c100d984a007806041c1010701da109a03e0300420360707462300c034000b000e40340c02d10a1071050101840e280d4034481c801b4040380c43e81003800e100705038682e0314040385140d01000d800381c4454070005a2084428141c0340d40d0b44a0001651555402d032220400c0081c50300041d000500003503c181a001e0440c2480c51942030032500719100000c0c150b40300c64805505100403110180345c4011880c010080d0b5030824408150541d0503003d20064a0310f280010341075a07001d9002518507410840601151024080950b2034540014201b8101c03218403100b04050354800d002c0c1814107400d14a000901e050840c8000040d070743d01c800a5400d41e800c3c9441c0c103907464042200c0403c260b403299000004038035900c42a110440c1c00355260840b82c07034000c40190680b9200103851991610f8410741c65250411514082e9013190704441190303 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 913458102 1250 913456852 913456871
    0xf240702060718030f051b091003080903070f03120305010815400218070f0c0f020d0311010b030708120702061c09020a0e06010e0d0f05060403030510091a04 69
    0x421103503c0b5007000300500c829160200500800090a4070180c00894605010381190400e1156117402a100d40464030704145080c000605c845010f49080c150140444080680e1805420280741640d40140c42e1041e800a0802050350b250007000e014046140061000814106491300407101c010180400308006081c698012109407401c8901e01003803810841181c0c11144901a070b01c09075030303012481022582039020444118242c2c0070300c1881c03035072151314404804110554030142001c00407642201400340560040e511400d0140d0342500a664a09441c003016005608545d0b4480545100780d000350002c03c0401000186030314405440305c11652245083e01c0491070398000d803004d40c2d034a03a102d20364031049030030150b100b140114022a0498059030ba280c1603454140c90607a1228005042c03c02140348508004244103030075407180c4c0002c45401100d490309420020192412800640c407039080c4a141c0c81401091405004c15007000c01c5400040002c400c0c1d0204240d08860045407580d4114 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 913459352 1250 913458102 913458137
    0x28030506070c0f0b2d01050301060608010f051c0b04030203190219061e0f1a090114060a050c031209060105100503360105100605040e0a1d0f2407020607 67
    0x1240e0b6941100f01d146503005c0001d51009042002d000b030394000c0d80f9040c80019450703c41e07040d8504030f4105400c86101c5900380000c2c02543c00c0340203801450350b41610b0381040081e48102c0790303d1185001c1c3d805035860741003500c1694003ea480185402c21580074010840304105564940180b1a030300c1800050f4504071620300e85000c4000940102040e441e0012801e540b800c0e40c0c2000702c54009200030040303e44200d4040000341c203028094880f200e40c0c03000d400c068900b410401001340100d141441400e09511200d040c0c6036510401800e0170b03140144c03017480949041042810b0141400301c80f240088405800020b246020050904454101f65203005011100d4a4070703035065a0b80d0329401d035a4103405030200700d01030401a111440c007008a0100024030714441c005039400e40e46800200030b170544540c828030028082d16220814807641d0110700c4005808100100d4090320542000f4011804003030080c0c01c640440c030f04050b50102c01c82001c1141d45680410b070650312601e07504140110b11000d2181 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 913460602 1250 913459352 913459381
    0x31707030b030106031b0e0c07030e0a030f23030307020d180f0303110f01050c090f040b1309061119110a080406170711030a0e28030506070c0f0b 64
    0x581e50103500e0301c4d1010042c481891142c14100d2130380642c000480d56215411162064102d9200e03400c02c4090102c040024428136010401c110000e110010490b225202e171840030745801421144a070380d0692100b10140400400c121640c0c03114003075401c500e80040d02035140e0a800726800200810a07420340400300c022041070b40640080401165804c0d03e80c075000d030007210092151019445100000d1142c9041400ba2520aa0041d0003440c1484100000e120500582800300f0b54001e4580100c4843c0c0d88614070410020080840046074003c02d505200e800c4445100304800205da041001401401101c02c2c07000d03140002c3d1400b40c01c0103a036070701814281403486200030309920000070001049607000e4601401c065100d04884445d456484007174540229004c50380c0c419030010700c500701015000d11100b504015001d0001d10003148980141145400900c59240350450b2104092050060410601e43e007d81c1e603041a1188041c0740d1135015103c82c03d03000040844202c42c00007002001131545 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 913461852 1250 913460602 913460621
    0x50f0a06053108030c150601020c040903030b510c070806100e0612060106030b1c0f05010605010c0b0c0a1e030c02060702120904020a0311070b06090105060703170703 73
    0xb90840503498010090f180e44c405800441c052051080b0207140ca9600e581031409202c0c140c000f084501500000d03c4041d24003d4416414590381e12082e010075219215507010183c504017480494001c054054001110a41100760304c0032034440300c0d29801132000701d001c03540701e4444280c103483e42109035040b45400090707000f14220340032340b0003440120000304603450191681c44a180d03040f940c54030103108038507690402c0c440142d8000401080560b0203540300454800c0e01900e451074000c4891a81d120446214000304c4250360098002c1041c0003007031007100050502481c1000c000c05503512041d02400d0060441300d804880000d41c940303154000d50004079011040480d5590071a94200d010b00103044140d52840940a0301c40018005440842c684501b07181c03020344103082c180d104c4d0600000307400060881046c90782e18032468406120000162000610848080716140380c540d09120418106a12240c00398209108400000303410050b801c0500c2e200203080a81030b0307030b0401e08401616800c0c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 913463102 1250 913461852 913461937
    0x4020d080403021005030103050d0806010c15180312050c030c040b0c0a02040929091b0f0402030f10091509090f1709150703020a080c120310050f0a0605 67
    0x24514134042e4000c00a181201d010b0000d407006042e01e01025030b200d01086130790343c0c0000c071001e070014009800401e4910f20400e05100c0046c00940c0d003054000601e80d50300b03041c0c012440d15105044030300d009005095021140c5604141142041c04a08469000e28002e042c030840c004103041d40062000c0041400090b00104148410803042c185114060880d40810000e450500c0a240076100e00003001c5008804c042e0044c5401c1081004000b08215203503402548136020305500d48103999580050746c0100c1c050100c2500c2420710891640385201941c1c00f0146a03410320340c005030340191085031402101c808400218141d00285003ca1010401d864000e092402100a1024410006001d020500c01c1581c140c040d110001450281502541c00010011ba103d1807004001a440802910b500d5100608880490030340280d01246034200711000c620507030309940d0400692070103004151b5400c4090710711145081c10000d0080c800d102e4074000a843c4142c1042d1804035100c1d01400302c00c61a1b140 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 913464352 1250 913463102 913463119
    0x910120b04031b0822032004020f070c0509100b030f06030a140709060504060b073e010f11281416052d01091d091c020604020d08040302 60
    0x500d05020340e50090740107405145030703005c2080b40d030040d268106010b503900201000715003c901685140c00e03c20000751070750000d8080c010300d901024010050130781d8034418414000e9460511702409980e94005201d101107491207801004480c0b40704040360b0b000007280e03c1c204010794920011902c0c1c0340200c100100611301240041d4915640410394030150f5000100c1403100c25902d070108000c0e5112801030600d81501089644000b402040c018162000403413401e004080d82039000000c40b880d118005450180b00d40302401d6170b5a40081c801c1d82421090508001640040c100c072503540d81000c1192000d80c18408038150000303041800c0c1c0074074582c400c142002400e46039007080d4071094403600700648114101c9010540340740200c0a011100600da01640501c1d088810b03100f2100c03030030f010203410701c45480b10128581d006c580c00d00307071441d4240065440c4d900f84150800c0c5800390751280d00080405a210414100342e0108038160055012035901040302010b04224440b4401c030342c0300070341c007a001c0c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 913465602 1250 913464352 913464407
    0x124002180424020a140a0e1906090e07020d0c03021c02010204141f080a060f0626100b0d1d06040309050d0c06030207050c100e0910120b0403 62
    0x4070010304a121640d070b1004840d202d6520008801d9015120094001c0303242c0c030490544592000700079000c0031511385040e1000e81c84140c0031030703000000c00c08410903180100c1c0d01070003090780142e0302200900044c0c8880f0b14070714120000a49420000001c01d00700320b020819002454400c12142018100c203c050180b90001c00b4000b034000d61241c400c0501500b6044251183ca01c0d007010310b241212030a56600c00c600c4c02c171500440d441c0c1c000a082000399503403010b0104d5030000c1103040c000504040d0300c8201e0b95003032060110b6400e042e0b03100b10420b41400101040120145000400d04841c80f4401d05038a6000400d103c602600c2c50070701c140c40c01d1081445c0c0141c0c04000143c01401180240c9031002c1140d00c40051044100401030090712004d00c2c0c03402008032911a5008040c0c02d0302a009544001d8050701c00101140009207c540005007880041d40300b518004a00b182c12101704201c2c01c2c0c440b4508112180e01b103800040c003510f60080e0f2400103003810b000e0f08800020702c21124881d880510b5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 913466852 1250 913465602 913465613
    0x219030b1006180302010c030810080d110c0901050f04090f0b0a0b13060602071401020f0d030209010306120b010909030c0c08031902010209091609030501021240021804 74
    0xc8510500c000500c1e030308580b01000a0f0b19041105494040c0c0d134171051f4001740c1d10180c0b82c070803000e030001c10f100da15540700107000a001c1c40030294442c01e0b507036000000411807081918068805203a01d04c200f91071001001981e07250b008a42ca0120140d4000c11810f400e801c100581c409082000303000d414055040142d10241c0368449014008111020080a030701c540960303088854030302407000980d000c0f5209000d0207040c0d0501c0e04403400b051048034107508100012a090080c03038841500401d402181000c103d40e00340c050740300503006c4810140c1115400303866060748150107208050f0410340c0c50300e04009052054412000741c4d900b0045412100e950303905040c0c1c1d42d5010500076043d140305141680d100900c1070080755401310000300039001c2c1d51940c2010036640b40f03c0200391028048001e0b000400207000b0b00141080500020000700c0500d4800103514801003410707c2c00858002c0d01458150541c40a4002c0d054080c0700c0c00907205244040c0702080044150310140ca0303c07852014104020404c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 913468102 1250 913466852 913466881
    0x1103010216080a0206130503270414150d0c150c02100206010503060c180108071101061205010615050f07051908031503071419150203041a070f0219030b 67
    0x72103a60880f030305542c0e0400c036400b5292841100a11a400402105d04040c040200c00d981d075040349c841d2240d203241054001400c48158401d4046c182000404004441d0541d81c1c12241a000c2510900301d6a41c203562608141a980c0c000c40d0801c998120451101c1d520a800020b041e644c00b505d070415003004810042e584180c01d108140c400e01c9010000340c0300d80d140700c050341d5000020400010b840080740d40103454220008100d10104800c0c1c0c049040d07244002d010f40d070028540e8506104081869003811802e5a01980000000346807082141c0c00b10f0340d110b41215044e4030491205500c0c0d4a151500b6030030626101c40c140c445002c00420702003480320500095000301650b00c840031400700000c09250704d5003414400d852000aa083d0505040d0800b044040700d00390b20b1176000c468407511603907040c40100c00d2503040001680081410b000c0345110b0300880c81032076195140309003400a1952601a0300103c0380d0024051142d01110003e81c05252001c18061684005c1544251030301c2021140c4c1340 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 913469352 1250 913468102 913468117
    0xc01020a080108060c180d14010221010b0f0f0a0c061524020705040b010c0605130209072109060905010614031b15090a08031314040e0a110301021608 66
    0x41c05030202003072a102499080700ca195143c882c4c2c1340c41c80c03101e24042044200d00e8800075120023080c2050000300f56020f00c000c0114580e405424040070303444a60070500010141c110642c034030010081c2d2011440b429041c0c0b2180221403091650720300480b0f008556400107101c00501030b50504100390319040b42c1103000b20607500805a0401d011100311004100c3c2440000c0301400340e000740c0c1c01404281401e81015400c850181001380b480c1c000c5580b424100c070012180c0640b40c11401a0210071440d00241c1c0580040152400840c140482c40c440340c642241c44c0e8001c00e24039654020036041040540103400846c0e0803400810049540c0c1800c403141805a50348940b01e40145000940c246410190710303600141c020700156440d14404000340f1590b0b1040589540c8518030190000e00d1110030402000c0c10200700031241036243c50545443d02c42220140c905200d00d0601e0352000e400d007800100290410742018050420200110120340244680c0c1a1103c4810582ca500818001c0da00e0041015 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 913470602 1250 913469352 913469369
    0x70b01030f0f060c0f1d0109031101111b1f090b0901030f051311100e090a02190210051308030f07230c16050a0b030a020f16050705060a021e030c01020a0801 69
    0x5050808400d40007488861240ca404a00c8c106024000b241e040400301044c40e034181400303e403a411002e08685001c00541890081460f1001c411030035003041000c080d200809468090408065400082c2c148001409690b506841c081007014040c1e100c1c0d00801010040c0b80403c11403410a82a484104000b030300003660a2071460029565508154050000c1541151348180c8a80c101104020004002415004a842c0c0a004010b2254038582e51740e04038941070340091240c0d1300000f1f20081a580014106410f030005a4240740100b0380800c1200d0b030102004594000d00c2d9107051b415984510030001231205034076008507000c0043c86010040c4038048200084503030303d01c881002507a445a86000c0c41c0d4010b41140b204008014941018642061440d1009401c2c24031610340682c40340c0100311b84501c20398020844406200040c4a03040150100359280c07450101481806595100012612415280e1902581c081e001091003564408a44400250b69800c0c550f000104a91000e001d500b04 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 913471852 1250 913470602 913470617
    0x2150406051006020f150901060b0307091a211f0b091207080c12010f0207200406060e101e0801081006060e010503060f0405090f0111070b01030f0f060c0f 68
    0x55242c00002c01c017051030444130040041e060004608502000c2c0940390504643d00c440d00401c4c075030b041c600a144207003544e5a0324002c0c02c1c9400d0040d03a81078891140d1030000f032820042004901c4002010f50300c98248984c85010a442c0c55541001e1026001c1e413009820f0800400451b41c201a40010b0a040201b110500c0c28005030b48040e60b1544554410034420b070f4010900c15009041038551000701d07031030032400011984d450040788001c1c0d27070219038102c0b24604400341c811000409020032300140e02c0306460030040705040c082c02030409890f03040380a2255080420031002c06210f010440300a054403a5000b840440203400580001c00c20f000e100c510703009180c030750710540d0f169110340c1049038160383c1d03941c20a01340c00c001502c041c2c3c13004d00b59a4004150305065a0541c17640d014242c01400301030010b1183c0c031062007556007142e0000003d00c1c3c480900304080070204040210050550780c014107614405081c5140c54141011010030051480381807240540440d50441d2092800c200c00ea2603030781 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 913473102 1250 913471852 913471859
    0x61e05040803071205220c03060606080402040f0207050d030b0402040b0d0203060a051f1d09090d0201050109061206150509070c02030d090803030a0e1204090207120509060d050601021504060510 85
    0xd0a48208440c0c0f818004142d05590b411082980700101b01c56016107000e00e140c5407284c0320034040e5030301504880d001c03841c07050520046090030b01c101508501015004c605000b510f0366559102c100080065003059110391039101640c7d0b80398105e400420329500c00640e124007407440e543c06508110342940c4900303d441c0c0b000855003040141005004280c1a4209400d505501d0a881148003001031620881c1d040d803034080aa2139841c142070184110710000c000b00d41c20035074001e00307580f01604061003ca080150400c440b804105c116040190300400108036656107602c0040c0000c0c699100a601c40003801c18020a15080311480341414004e500352510231b0030100d8140c83c0d9400c1d0f8071841903107500401c00a602415107030311890f841310064003620104a811400b84801e60807a41158400580c00100d120410080031010f1049500c9414031300d00b0720910304000350081c0a902d00b024446500d03940020360581c0b090103802d03d02c196401c250480360815082c400003c01e81110107804001d40d00c840030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 913474352 1250 913473102 913473137
    0x340906050f03010b0901030b1510020a051204141519080f070f120914030c0312010e1612153008250204020d140112080403061e0504080307 61
    0x4c0782040203418240740b40d10f19601e43c0903816004141400c3c56400a0b0b030a00c169940c080c210031130103942c0e230040008000f18140141445000300300824905070401c0b04011100c90307490a10700e00350b0120345030000c80340d000d00c904506200380f04881c11140b08400c0c40342c80c0d5030f0304043d0a6004043c6d206030924030b41e580c0741302511518171814200011400f4020b036031521a4a54000700d0f026445441c003280700e281084d458514540114941610980000c075410340b100083d020741c68010440141c029056080c48150344a006204c444640e0820070540100c150410b0b468108140595240f65050b240d40e50b5041540c407045c100c0303c150039840e4041e01840c0070400000e0640402c45402c22082c41c50000080b80111181c110b10b1340314519032021a01020150751a413014103210014450040b611116001050b44000070581051501040034004500403400c0001590180c903840800010031190f0b001d508444a4a0340b0145640d040c1030100700010040f0b800c001e94050546511064a10700c00c12204 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 913475602 1250 913474352 913474361
    0x1b10020705100e0601090b190620190f03170703020a09090213050918031b010507180b09040f0c030e12160f0201051303030201051611340906050f0301 66
    0x42d803030f190b00441c018410340760703e40d1040452810091030804226040b40c1c5d035500d04402940000c02107452401d41d026070481c2603102020054001d005040d0000307416200c07048e41c0c5504800903181c400c2c000404000c15000303002d5202040410039413064503280104009021350300482845000907000e62001500d001e0320f0099400c1d401d50031040703694060800081c8900c00c900140b0a102030000380d10603150120060004001c81c00c07202e08031030045200c5103031850a690020b000c500401101107400403e44002440c2c42003694200354245641c0c0001c2c0c00010040d01c038450b03480d50103e160100402c074042e0140d002c40004000c40003600c0d1461041401030849001c2c0c8410203804c8240c0e00c0e5004d0000343d0210b260703140640305042042c201004180884075241c03160308100d01503950303141401a122110001420104e600740392110b03850303481d0f050007600c032841c8088840b070303d11440002d2411015004800c1499008a802e1143c0465940f1100c1d0302500052140d1805801403082c00b92746410103004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 913476852 1250 913475602 913475621
    0x3070c0e0702190c1e08010608120a050a090e090607090501090b0d0902030102300606031005011b1b060305090c090103030c030302070b070c140a11061b1002070510 72
    0x501040c0c100c180c8580030350f14444000f1030344810304950200d12010820300c11503005032607000c00c090071414035588508446441c0c010980c3c691009a0060800440c0c1041790000c00d4945046038035800c0d40c100540d001e00c42da1700600e00da86142800c114900000046252056115940d50f40750280c1e140010745125903180907200000b041081612845007a0350444038010f48050001071804c005200400b0910005041004a0f08040c40d10801030340c0e00100c140b0b40009044943c03d1071802c100882c04850b01451242c2c83c1440044243c06030304400d03000101d141c5a802950700c004180440c0590b101000442c090030001c6403030800440e40c452000210b010300707010b014080e400c0710703400c5850941d00381030f60000443c2015020410400003076000d0000a00401d42c981301d1f031744031606074070f4003201071140e55604401a074030814032000442c020004405910390196482c50b6180b1a0204865001001c00300b41071241c0f1400c140c03c00045aa54000d2900502810030355a40c802c070484001c2c15a000d030320 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 913478102 1250 913476852 913476857
    0xb0a0305100e0717030903060c03010b040e060d02130f1104030f080f041a03151f2006091501050909060106030b0f030a1511090603010e2703070c0e07 66
    0x10300ca003003100401d03400314512905003000c6510072903030744d900e940e100f040c103400859281c0c202007078210f29410100711554108403560b0000d4150b604201070a0344c40e0049108843e070304e4403130a000c11116100e80d0020a4056001707801d0280c040e00e6540004090700d0f100c141c1c01c00c0c55140c6042000040e084500780e50039641e02561040f0080203589960219810580704000007200810001507041d000d20070585d40703c3e100c002c01545038030b0941c0e201b80b450342034058220b0007140e4600c00c03101810292560189070445a0400c03040c03810464070781d55850013400c2c0003004284101c0051000c1d1000004600004581c03102140000340c5c1c8480900c900038800b80c803400c000390711040c0144801c9000703400803a44c2044c050312540d0314002c0c20b800a8503205d07020400b5038111240260001050300300d40107100303420500390001c074a40b4003644041401d51005200e0701200c030b0301a40204070388002802141070428200c004411114610310902c80e100c0c5d000c004111104c0300e105900242c680c18040c1c0d990f11a50f0b168 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 913479352 1250 913478102 913478113
    0xf03020303070210031d1f0e031902011508060103020301200d0b0112061409071d0d0c12050601090c08150603090f06010902090310110403240c11010b0a0305 69
    0xb64244038490419500404c14991151062070000703111140c1d0506011011005241c64044201c4d030000d011801400c030000c05003810100c601c120300001c1187d411034460004a000c0000816040b030040a00741c43d0002900b00c40354001078142070009010741031700e000b14001c000900030902c1301d611840c1c1240c44030a440b50244607864a446103030344144c050040c103040004081341811515401c4844d1500038040700072704c0a500004a0810780e04082e40b0407801d0414200303009401c0c3c90904010201410944200c00d00480281008000c041d0742000b8890003401892a1606207007840c1c03580024040d00c0c0394075140c610141d040381d01c00d6281070300a2468030502c8400365000c2060012030390005040c254140f00d000590080010104000750082c1048000141c590452204040c101901c1080e904840ca05040035030021360500340c00c49044950181e40280d02c1c0f040c9480c142c0380b00310010440c850301d03071920302600e14943e0844184070b60f40c11805e000b000400c0d110400c00810030081e0001801d9507000c0d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 913480602 1250 913479352 913479367
    0x5030613031704050c0d06050f100605031f08071418060609040216020d03021605010503221403030f04020a050910060302130503060910060f0e06040c0504030b0a150f03020303 77
    0x6040446403c18029000d480c0001041c0020940b4131140e01000c5078455994801c204d514052080d0250700702c2c12070405c0002030703840e14034024100e020103440d000c040d00390035030802d0a445c2030400240080c401c00c0c050322055641c540002c0898011100000c0c010041c402159003a0049d03c45021320411000b4025424502c98a0a2000a4014541901403154506540c40140e501e81d00090880b510a50060420321051101c6d070001c0506940828144241402031045060526039013001507240211030341500c120605001008c101412020306550100200f40090544180f0200e0f10550095400e082501d41e10360500101800884100101101101045c808075200e0780040000c5c4154030030394410035880c0d4000074105601600d92480c4c40d803103c0480a50202c2a000354070042c1041200d90003150f1900780251810480100464421a918259000584d001d14140c501550f008884412036103000c1000000a2405424400c0d03184804640050030902d08520203064985c050040e50500c00f6 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 913481852 1250 913480602 913480637
    0x30f0602031b071239020102031303060605010206070504060c17040504020a030f051e0127020d0e07090e0a030c08040308032e060917070515040503061303 68
    0x3001c2c11100b001a0603041065051074960090540c441c0651a0001000d1140801609121036910740429001c2040b1000c0c071500240c5190042c2c40b01d80202c120520619440101c0c21352040b800c030803601640d1000041b091028070350106003901c03400e800309c0e8181d480380d00e005e40340d034012031158000003282074900000080b0840c400d0300c000100541c005042c0f0381c07540005020b0f40c10a41d02d0741d0003e5903030400d9144184217030041c42c1d0442d21804082c1381c135185a040f80c0c11110014007480709110300c201086005d0141007440303e10ba00c18070703030400c41d15991280342441c003415141103011020f104094010808034164465900840b5014008007110240350b5415136000310805c0e020344001400380400000b02d041d00c4010f5126503a850390303005100c0310002519a07014556280c084242a00c0c0006100c130030340285d414016038200142b242d8a03440080780461070300301d41d5001103420440e1100910743d0450400054400d4400440680340ca40e501d04007140c40098075203202500003582e001c0c2902e940380703 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 913483102 1250 913481852 913481857
    0x3060c042303030f090f0402030c07080309101514030d051c02120f0403090b03040c210f0309080708012c120f25020f090a1404050a0b010e01030f0602 66
    0x71440481d200040d0480c400a07045030040310b941200407400045031002d170314010140c0c0c551070780704039021800c41c10300b600c0700c1d4201e000fa0364000340185000008260a21001c124121400c0070403501404070300070644280301484158441c4400b12300b14a90301c0c3d081c1c0e00d000b19441040075043c2e5215420070300c81d100418110502c80d00c0760040700380d080001e841c000c3c07100408180309080303540c4440380307074201460000d011140e164401c80d00d60405006020000d00f40c0c5649030b044400b802c10046560860f0501212060f080f50340c02090103c007006003100f010f401582c01000c84120106444107555100249400d961212070070041a002505450704080c8601201c07050f483d55105c102c9141040c640241d42c1c8d02da1066030000c04050011940b21020300b80100842c01009a410701000350b07504950100e000c116003050454401c07140080000d0421000354402051613400c00c9007c203540c206814990f46600c1840d0090364940f01200c001305640f8080b05e01d5604813507218400b02d41c00030950319550f0007074 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 913484352 1250 913483102 913483139
    0xc03120c1110020909090a03080606210a09110d02030705101707050405130e060609043201050f040f0f08120108251a0705030702092403060c04 63
    0x1c0c0c01200301060108000c03424080125050050761008071104204641900600e6251036070b109481d40000244d00074602d54001c0e10680d5940c0c1c031401e03041640c02a50710b00f5142460340500010070011480c2c0190801d07035940e406030420840516007242403220b1a182840007035090740c0030000401c681d042410b2902c42c502114034080340c4c054101040d00c1e00a000903910000043e0b0082020b0110745000034080f0000031901d201004038130b00c491140c5803605002441d00c0d220300c060300300060904c424602c40481100544a50b4032f9081911218950005154030607240c4540c641000503000154041c0414000da4200300900407900460344e82614100001c80704441d601018008885148100b41c1142c4c081c10008029000038800e080703051250005201d40705607220a840405c01202c401c080640c403924203150000340d96600c041c01d00364654458540c00035005220074041050781c41e2145082400003070402c4042d008004442c00300355031200103903100c081840f401c10041140d440c52403442d0035603 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 913485602 1250 913484352 913484357
    0x301150804140d08011e2402070b04060903141504081c09380a0f02090a0f150302040617090a05070b03091e100b010203160f120c03120c 60
    0xb040c000015040c90580c2a1550115000c1d80051203281d03014a00064019404103a1003689441c10055070049070300c041400103060007074465942043d109202250240c484c03480300e90742e83c0345e0380c1c0001007401c40d082c801aa4040301c000c000c11070072003000c10f0840f1180001c008292250700c031070319803c0f4264025115600c0a00c400c030b40c4092141c9031402000304c014040e4041250286001440d0002c0b10412036440d0610102400703007004524905280da50458040400041c040107503070035400c001c5c45403a5110790303c111a1440026500c0441f514181920200c100c01d142d0081c1d04e9109134241d001764090800410b01d680298081b5201c2c920a4030742c051650412131344044942d8550f00c0c1005441d4000380c2455000104101404904111b5688800d8100702d5001790f00e01c440c41e040c0c1d01e5907140d0100f5041c00d078494062014907842041a00c0088a0420307204011800919015110117800705e0200d516004803121a000e4500036000840300c41c0e09510f41071807103009204848001d0801654a00c10b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 913486852 1250 913485602 913485623
    0x9100e1f11120f010608090c012106080f030307030e06040510110f031312180e040321060f1a0d0914150402040509030c070b280509090601050301150804 67
    0x71500c24507002c601540b054421070686504000005080d840700070800041d540c8190f50001d0395036848043d110043c400c00d09184c00d4012a040c1680240c072107548410150710405080c10008100800190f00511560f1010090901046d410b107480b0345d011940541240c01c6030643d01050b000503080042003602401c0c002d0718114010a045e00d03030340c0042d114404c901c040f0780e590104009070b00c150084800000d0400500c00c8480c6001e2090b0204c86020302240e9100b00300104040500071025209200c1e14400008040d110441c4500010107180c8194400c2e1940e691000804a02c3e181442d60150502000c507031620350020b203c0000f0340301012084610003444020720081c444144034440c10320460300d20440030b600f42801000b042e0341001d004aa41500200721001c0d0001001a0120413102160710554486900703014040e80449150030032544050b05019440b2419840401450107030303411913400e01c050f1038030401180caa020900414195000410902400743c1c003450700070780c1c0f061103203400b140c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 913488102 1250 913486852 913486867
    0x1809080a1101021605010906050109060b0d0b1201060303270506190207030804231824060f03040312060305100906021303050601030203120c06061005090909100e1f11 73
    0x14000310840c13078295841c1e591042c24404220090060741d00610f1102800e00005081c40b400312010b20030745460f500069951a0040d481d80c031390304854100795071703404003c00103d66070742409054846c0d0401b402c07100c402940b040c88841a108046507085d25406810782e070810701e00602c3c030600428400c10110035403095000000c0028501d00041001d03107415440071800c1d40246810040e402e88080103181700741c040089040600c00a0307500c55038000500c080c512160f15580b54010029005401c4042d04801e0000e46542c02c000480010744c00740f0303c85c0c2c0d20742c2011010044a40c044480a000c01885500407550000707a048107a085441e125005803401885c10310494551144250154030444403900100010402d41c60b0a001c040e0b1070182c0c504c1030515121425482e42e4884d040100010b11580329040c5600742c4601c10010f07102160700181502c2520b040119103541d4505407102c0142c920b5040030035180c0c55500120350050b0030f006181e40e40b516848201440c2000d4040d80c5503003441c800d030501c04070 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 913489208 1106 913488102 913488127
    0x6080a02090703020f1306020307141501030b07110109050d0906090f2309090105220206030a0b040915091205070809090a11040306061809080a110102 66
    0x107030744800b03160b81710003503000d00300308141c4064510f240072604a070000020140c99000311441c0710241d24038a8034981d01d031141a94440d10803030700790041000543c02c000ca01d8000ca69801c01e038440f08400c0031032900310703010013805464a51110422002d00c94000d0445009000d5520703107100d4041c2041103c42584140303100e8065610b42d140d814103107501c03820000120305003006001e0700260070201801e0f8060038003641d61250003a46110340a19001c030442c035120003186d01902c924210358507009154000c29200241e59041a200c0c4889000078010951080c81035903040c0d00051805820304051402d40d1240300030700240a01004050041408142030f40c00b0081c00700c40102080e500d003030342c80c006450901160131715060046404410480340e90009020703283c90002680140c4840c0c0507800a80b412400c014258440070880001c206110329802c0da000b842100c0090f00e440c40712902c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 913309352 913489208 := by
  have h0 := BRFrame.cov_init 913309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 913309352 ≤ n) (h2 : n < 913489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
