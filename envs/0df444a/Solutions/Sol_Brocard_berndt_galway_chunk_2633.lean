-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2633
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:16:45.659614+00:00
-- url     : https://prove2.me/submissions/8e72177b-16ed-49e0-b65c-6b15000840d2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 473381294 ≤ n < 473561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 473382544 1250 473381294 473381309
    0x21608031b010b04060905060a050409050604080901141602090109060b0a050c030d0e1f05040f14010b041b030e0106260118060203090610061b020a0f0e040c0608010f 73
    0x1900c0354081c400a41c4034101c5a0402842000f0555a07480114007410080fa8600e00c1410345000c0002c05080500900801c5a030110152445503269500c3c2216030700918509030404c0382618400c40d025000000420b0b420a5180000303241c1ca110703104000040d00140c1280a00c241084020003205520302c007603a103006100e0a0803521001100602840c1d0700986584541140c1450001c01c828203002c14074604807503c21440c0311401c9900000c0c0350a903001902c00400b010006000b0f0008248039581a00c8031515210020a60b0311584c0001015120362174900b520701e440017044610f106c2c0e09031081450001e00f0b10700a0002c0b519041c10218038248801e42468216a000421080a01c083d4061641c034030903102d030411805014203104009400c01ca03208209446840040703900a002540b0035000c56040c0e946100707090101d08040b01c803440e007140049802001c800000724070340b520208004c000c0d0020050f94459403800d42482a22040c95a00c00030603c25141d0050100486048000c000d40700c01 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 473383794 1250 473382544 473382577
    0x30902030f0313050108010b0705030d020f16060c030c020616050f0d050c04170a0203120f0f04170c1f080c0c0a03120c020304060e121903020303060102160803 70
    0x5a002003410514003000c4544a030000151401c03001c0c102003c50b10581d1000e83e43c94605a89031412031880d0321420034007a046600901c0700e21900c602503001042100b803841c2180f810980003080c2d07403100a010041c22101240c403140c041409640c180306402d00591a80700810113030900c55010400d41f00170710428001c222000540004082d002e504641c0101942441048140b5100c0105a21030b001409140d9980d0800002d0311000e4400046582c65150000c014011445d007170307480154168017140c1c4143c850302d070078402501d83c542400081c0c0300408031010804030038050140514241102004c00760b118542c003001e001101c50000d40b42811050160402c04019103c075035a2850501506502c18070a110f4602140c08140d4001440c94201d654142c0c140407403180e01005903103a02550080b10b001440303542ea898403601d0904a0507110401003801d86210403141a441b0306508442082503016030300000c1808040d59040080056100b80703500340d01000d50400e04020380724414805110090204c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 473385044 1250 473383794 473383811
    0x118020906090618010f0602100c050d05070909021815031e06040213120303050106050f07110604210b0f0f0a0b030f0f070305120c071505120c0d0509010c080703 71
    0x180e2904103074134806411444039156a403003002d00034560340d034000c0790300501071086284511440e5001c3c822182d0b07850f898880c14008810058001404001d004e0020095688000108444140f005003019040509141c2e000020740d011310100858003e03c4c90003c680c10070400100c1540360802900000068012455689031103001a01030f00641c83c4d4080120051740f40001c041d18030040d0032403c00c0c800c0e1410700c2030341c1ea66030068501d03000d00b800c02800c4500800807a800143d4070100c1154024009100780c0c201a140d00011045500b08a000154084581c80010500c001220100d40c03002c4c104100e0440c5140c041171000c08801d028156940341910390391003c90a0f0340c180402101091620101c60301841000600c681c1d0314058131080e11940901020a000c9022620454418085c80c038018000149000720000074503401d0704501007000300c02d000e1581c90360400c10000b801110142c034010788910039103a43c04100c940150204509030f161860307421040d600202c64503030000035424005190b28 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 473386294 1250 473385044 473385049
    0x21515040f06030201030b010c0506010618031218090b030d03020c0f1506011715060703110a0602040f1202010c0602030a06050303030903030117060c25050a0605040501180209060906 80
    0x244420056030141c01d0900400880100740c0c84101103038002d980c18041486c05030015a40b0400300311000d00a90010001484503034090034055042800c0e66500904c41952525001140038a09440c080000c00401c0d80001040e100b81050303001d002038030780400943c0724844c0000c0c3d48160315040c1d05d0a0517000304038034080c0340e024004403501c00d894100392001d0110214100f8904c10f01214024086207220412040d000e4808007480e100354440310680c10b403040031004000b01900650030407410021907843c0c111392080140840d41d109807040c0c0c0d0250f1940d043c041001440300c0541c100d18600c07148003400c030b800743c5c0e81b140300a5010358208500607030300d0b140c140540000d407803e504103030342600c00001840324551700007000f181242c09030700343c00d911045000000b580320742c8152128402028148034040d80844021507100c1c0904580391845030ba296613684650801d8148001038555541d2030b010003084c4031003030084c0c2481000090001c0c51032006680001c0c055040584407030300588107a4002190354 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 473387544 1250 473386294 473386321
    0xb0a030b070e01080c1c02092d1305070f14130b04080606010305070f2a05100b030f0d030f09141e0606131a100f0305160215 55
    0x454100c00060528948400050700c0110700c1c03040540042d031400005600d28200c01c06540345d0303005200c05403094060580c40800650000400d483d4400c4422100310070384024902c0c5060ba54404204407070201980d401008001d0b00a0b407940003406003088100040241e0001c01001002c0c41d60802c81c0c030007402c0ca01e4681950080c0c504000038028031390703400f0560703460000180c0301300c82980c8116a020b03540c4c00c00440580350f0980c0c0203004192140c1060a01a001d40d8022002d604d41c1880c08042182420003ca00c0d40e9101405803501e0700405505003280115010b04031800f0400d50081ca423406c401c0710031320b0b83c1c0c0c070072545030008141d92040b010240480c1030f00218000741d0004042c5241c0151074040c1d0b034440c100c001004004000545034107011410204095200304001800c9042c01025140d02c40042c0a01840c4178107000f00ad4200c0d007800740d655003041039000d11b29944210401104d148054110340014001080f01441d00307204040c6294002030081ca00c440002e041c01003501c9415118000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 473388794 1250 473387544 473387549
    0x50a150201111b0c030c0901050d15020d051e01050603010b2101140117041e050f0604050c010f0809070b130f093327090f0201111501090b0a 62
    0x41d80b800107440b40740102011019256040c1d01c0c4155458007844404166507007002400b55500041001c00400c29172410318100d101403405031200f5407030340c2c400203980000c0b6800b03940f40114083d40c4a061105a1160886000103101551041c151a504000009100f40014400c4004d08040000ca030000b044400c1040c0800d040000d03050412541c540da0400380904c41102c4290000b41c0111000324442c42e40069140620740003c030007211440100c50003204407000307003819104ea10925006e101245800c1006900c2a40a603019082030301d4048001401001801da9040400214000384000598003282c503800f1680d20b82d011a41d1205005130551502a0307a51005204158000c0b0005404401d60007004050084001903034100d000c0044808010000080c24400960b00b0a000d11803141c142421624034007848038064000950f007080c403010b50340d429100319071480c4d039201034004550308940d942c004044040c010b00301312414a00740f10481f15051245948003500c844003520540c580c84801c201 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 473390044 1250 473388794 473388821
    0x6151c0b0a0204120f05010e071a0906040510080f1308090f19031209060c030c0b060a170309030d03140403180b0f121012060504021503040309060f020304050a150201 73
    0xf550844e90030402958030303104405650700d50070845800f412840202d2840b00741c64111400d00c9513080600d0318000075410090304190043d5040001050643d5018081007031a9400e6891207035600d0503042d401d1050801078078440340721181a072240005549101920904102030340c5c0001582c0007c40020040e20300c0c95658089a4003554002c800c0c044041e10300031184e94961180200309a4484049600002404d40540041c217031a680c6000940d5004002e5000b110041407002e10688890080d6840d0401e10140015940006104140707428148070041120b16a4282002440722060842281d04d500610040801c020072184210702d2030400307407030000742c00b074000810349501a55241c240140c1c00404900f503c50349601c00900381da15080d4a02058030300c5000901000a12a600c804c09072070302510480e0b201148440400b024184100910711480c001d80d1030300645840c2504c0038154184580040c1c00b15001040107025549400d0701003000c80744502945000b00900b03100c00c9004011800901a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 473391294 1250 473390044 473390069
    0x15060c030804260c0c030606060306010c0c150c030e190314010e03122202060a0f1b0b190501080304050108060f2805093108040806151c0b0a0204 64
    0x7910b00e5a207602a0003030480c01d004560115005c9403c00d41e076220300710b500c540e11800c104002900346d4403c2c2c2d01d550720148078425031302d84240c488843c1e0415250301005a00000e014440540505500c45110000030310141c030f850319488892500d100800b0b02d80c3c003018140d80408040490031900c25030003110901000003e603503c5041a0803d40604032042c0d4240502140c4000007801240c20180f00c41345d000e13402400719140c00a03088007030390308034500c440250a2020103280d040c1e00c08040f00500c06010310600741000145001c0001500800700e442049204038a80001400f280310000b00300d03000d490090a000841d5030700c0100090003a5000d81d200c58000905000c09080204805507811740c0300348044072500e40544420520103040000c031100301d0120041030031000e03040328070104040c011212580c0d00c01c1140c25621003916503031250380142d409601040800000680c004e80c1c200c0c0e422011030780c100b068002c80c484412000c0c044600609076902803000310ba0b0b0001107904680007040b01c16002c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 473392544 1250 473391294 473391353
    0x8040806040b0a0501090c08070f1107090903081f0b0706020918090d0203070510092604050907090303020a0201030b0f300304050307061b0b010e0a15060c030804 71
    0x7040d400240d0f00c03050501d08000001c580c40d880f03406000c0b0b4121a541e1082816514030404032003103905507030007005010b621941c082c400c82e42400000041c1c1a40040480c0340c000700d20b4010182d40c40140604041003001311190301e014503003c0c801c0201d0740320054280d00c2d0800c5090a40091080ea00c3c07003070b444514843d40b0540203015440951042035018280c178100ca8840b01c080e03032203204080000300f6581203e501e0410300301d01a88034900c2580609503e00ba040c50001c4400d110202141001c0c070080740202d020442d40c80c2000429078031024518015819038590743d4042c1d502c01d08070200905041c0c541401005c140c0780c0c0c040d98005500300a265030020303204080301c0b4000b090031406540c40b603c01d0080207200c11a0010896044031409001404036918001c0c0c100d5250a140c042c801080306c2281081c03012034403400c0031a010308125800c5140303609014000d40300700c58106410820b8005100304c200b14080e0044940075605805003000481607030b4600e050101900c032200e4400703841980c44a207 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 473393794 1250 473392544 473392553
    0x2d031603030f0f0c09050904080903030a050c070602120d050603100c050a030b0906060909090c0d03090e0a060807150302040e0702030403020108100b0301050f0d05070b1306050301120204090804080604 88
    0x414882c080e1114100a00b14485489400703a407511444000814a540300c200601d04003141c00300e038401c1c05150120b051440800000c0c2c2580d010945141c0081c4021442c00030000b03041c000c070340090200d03000800301003d40c80310230b00440c004ca00c0e189130602d541d04001540f90320288181032158180c030740100103140320000d025010380c015011050001f0b02d082e80d103e0203410503031541c60040c000100321604141900041244942004000e01400e0140e407a070310b020b589a4440504015100b81c94190086080c49048003d58500900100300319003401e1041003040302c00700b001c02c161034280321029560810160103802900c2150b001d64585441c00040120640d4040040c20950b8801d0381c030103a260302c6042080d1540c036603078098540c00c0001080104081d1610fa48981c1c07484201800c1442d15000b40e48480341004a82d5101119094000840e810415071105054001d082c40d82402070a6504203540c1c00c416040c4410000e0089130b44040c08424002c0c0f11054a00901003407003281c03100d00d007920340b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 473395044 1250 473393794 473393801
    0x30b1f03020d032f0d0311040f050d02180408190201021201061107030b0a0c08011d1303030603021002010b0f01170f1b04060f090b16020906040b0604080318032d03160303 75
    0x10120021f03240c6071340a84401e24400c112001c4400780c1c64042d03083c80c106010001030984a20040382d20410480c40d01803080c030440180f80c491402020b096403030b0a10108003559140580243d1011a44100003409840c0b40b180402815540507140a4102001c1c5100c224545151a04060700321a42c4d20700301300c0d001030241c00c54403100b05c050b668406166610150382d140c021184c242d00000d070081000156031850220251781c4c0080c005d140101701682d403a004510200702d83d000c002d006035120360705007039a0704000301c0c84c0e41290382c2868100102d50b5404020003589001a207041031150440000c1111400841c88400c00c0c43d40320600c1595455403101d02408242c004141c0300e010401120002031800074103402d84140d5401400c49103070000c010b508100c15800000c01003944641d55180401040e240d140290014124890003944e40c0c036200c40380c1d95000b500302c10401e482540003490b02041c0240c103800414030107554510310003000404415690560090540e404c0c2c5154500c407003081415030640 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 473396294 1250 473395044 473395063
    0x10501050a0f0303020a03052a0102030901140c070b1302030f0a03080108061b03070c0b090304140307060e060c011b050720060a0c02120106030b1f03020d032f 70
    0x240c11480407551401280c158042e1071001801503001000500c0120380114002c2600c04a0062003aa4005000d0f4600d54010314050039607226a50204c00c120118200340300d902d114003510200a100d524040c42089142c1c4601d1030010b100c80400b0f800308410b00b1048410f42d10140d402000d403540c03111300070303a00d0ba83c484410105a00048145000003081d050103d1a01e0187c90741e8031000a48040500c0e01c210b056101034041400c0003200c01403e0040b80550074010b01404a503c09075036100d281c100c600e261480740c3c2c0300e114860f4010044c10030216400840b12003d6a10580705191100b256060560040c0300340300340850290303540c403118510207900c44000c103006480358092100301d11509015480ca000b01c0300009410480412600c00c0c014041c0c2150021304d407005104a6001226054040c00d5072407550003194925852000c0c0101c0d0f20b6204007091806e03045400c0004004d10310340005102844091300034042c441c4804040f090001005040782c103e02100c498030b4071241084081c5030741c541840 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 473397544 1250 473396294 473396299
    0x406090603061b0c0f0204110d0504060203010501020723091036020703090b03180f1e0a050a0b04150219031a030703080a020106080a08090f0f012c060c01050105 71
    0x1000c5000b00f082c05080b02c1a20300d41c01503480b90380c03112580d0a000c0104071584003541001d50600c00c104920506009041c0314500c22040541c030395141c172001918000d0540c0004410200340c05410074030040d0005821003801c41180c0080f03244d16a13820400810a2940040d40d01c0c071000290850040c0003100b90580c1c524050911800e8907418402c054101e0180103002400944003550803c00b925070350002e5070700070f80505c4070550020400d414281c50103d0074026040241c003d0284c810158460303015001841050001800f14890a5500c0039219902d04000805990024000c41c0030b100025641080c05c4105281c00c55030360302d0307040d849040c0395084400700340002d01f010003000da40700d140b03961380080c010050000d0141e40d0550b82c548403103800680a0904540d61004000342c01c03002004440d00d102e002e1103030725944690000a00545050000505000e0140c807040d100c8140d80c000e04402c0c81850281200402221000c070380c591880680c407105900400200308034201800642c462812103104 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 473398794 1250 473397544 473397581
    0x80403120e0f012d03050910050405150415022101141003020c010b0a120510060e07120b03030a0905040b0d050c100306030c0e01080d11030d0209040609060306 70
    0x400100c07821803100301001d80025103912180c02650140400c00070305074012071003000001003600002c100a5102c842c810000e6120028080c072002c0c1444645010b14030305030180400d26141d01c035190f603203000f94421b5001d035010385c00140520000301e90f05000d40c0d1a12005643c0c4140401c91400804c00000e000d4042001d40c2000040070810b901910382c0c0f06502030007184032400c015909800035044040074801a5499540e041056690705100300003920038006400321554980c00d106103011100c0007916034551070801e0a010542c0b403a500154842c0044c505248921101c41d10b0202410703094140c4c03600761201140c0c41d03c80c0c079042001c45065520035a810480b482c085e8080191051154074060103e81049401180da070410f14542d1180105600f004a10340340d69541304124803c55500c59100000844014003042c001400400f04803034451a11402d8104900d50058883c8130380003040248030384c0010304807901d440d160000002880c0071103081010f26900c1c10101d0190403a41040200b0790741 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 473400044 1250 473398794 473398823
    0x41403100905071a0d020406080f100f030b06010c0c0b1902120921060403020604152a17010b0405010e01050a120513120f0914030307110f060403080403 67
    0x301446210389058001d030090801c00d103005000ca02d9400e140c0c0c400d500d40c0304208044e018aa00a0006200902c0c041c2d942d05082d00d029820a02000409000c242c0c031a00322090410003400b50280d84000c0d00d42041910b05a52108001039032400c00c00d48000b0046140100005800c1c00d2a1015001c000b48200780c03040c4516082c103049864103032103d400f41c084081441080480d0915a003036030085c11040284c0408005e419802528282003143d04030010390040c401c12080000307035140d810380c940c0d90113014007c1a6041c10b450118500c180784441c03107404030400c590307407480c42452144280d10055149880c035584902d45045160b00a008c0c03103020031450084900e43c0d511a00448200100307585e94016190f10540300c9102030040a0302c01c20900807281400343c00301d01c80c160410420040d0340ca41d44507550044801504601072940b0001d0650001d0840d24902d4801204450100e5801030900c00c441010a0019180c8000300360540d4002c207001c14003000f00016107000300181ca0090000d150100c5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 473401294 1250 473400044 473400073
    0xc081801060b0f09030c130c0e1c030c05031603121109060d02090102030702061b060901020a0f0c020a0e010e0a050f370515040e0c0d230102041403 65
    0x28814464101c0b0709078108808039081c51000040d014010740141595241c01d101ea0000300d00c40180b60186580c85c2c0d54003041c01d046038001c0400c40c81c220040d40c48185202001c0008901581014005001c0c011030900c9901045000c2c811900200d0703d02c000d0380070034091418014030b908441c0c20481030712032412000b15a41d4034041c0940e004c14500074100bd00c1c01c038198480d070000c0d400511450381940b20901241c801a680c910203080c5201c2e04505030701180301d05000759450080090302d10b90059104000c01a40c42d070f03003c100c542c02c1c0c40150800303404910261002c108454250360280340100e403054000725403242c003000414002e0038002c50600c00fa0b207421a50f41202c95040d9030704041c0c0402c116403045004000a41256207400400c04183c500c0a2030f1a4482a034400700c0d136038180300422011200481c5018800c0a04480708100200340c491100d1001c00d00945460401802100d40600007891a181e0314200200b2a001c18000b951a15500c0c01070112011719280e00c20b01c240504810131100c40d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 473402544 1250 473401294 473401301
    0x181707050c09010e04030c14060c03071806021209030a0204060e040c08070b04051002100c0306150e0604141c150b010219060b010302090d0b01030314030c0301091d010c081801 77
    0x139486944120000e0b2181e5034143c8030300301922800c444190f180c0d8000711403110f00740b0410b846003200a0501e544c1b0b1031311200c000c104d1400060307004101c080f404401c0c44071a41c00900f420050300b101c80b0480d070756090b080c0000c3c0323090185100207501905045001c41d5051032000c149000d03070311500464905a407103525503600c2c0c01841c010340741c00720301c140170810081c0381040512803268201d0051b907620140d01c618420945091141c00310209840710005c0102140740012100000014945507c0c6a02e0000005100f8811403041c034580201d4002d064a0315030790a0021850070082e114800c0007549140b90800801c0e001c100021841450b001c082511940081a200000ca0138102c5850091030070750754050007080041441d604150b07080c00055480d480b0300d503401249500912588a4540c91454014200c0c0d40c030700c3e032503071070440c051051040c185440800d8a054510050000c0b80c2d150300a4680c00f03e289180034181031030340c24180394440098221050601500500c00d0300895240d40440982c241c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 473403794 1250 473402544 473402549
    0x406031104060c06020d06030b0f040224030c090102150109140a020a080a0f0608030a031e0b060403030809100203041401050106020c010504090b060c010608060a060503071503181707050c0901 84
    0x8583e80c00352080005040e0307801051a0f118203840081c100b52a030301c4402458804540409a200d022000e1006510f0240b241c20070102583d920800c04c3c0c00c0e000e107807025502014003d4644a00f000c100610140e009000000040c150a22184281e696401c07031140a80107030300340c2c50500d5115201150340307000345000b181c142c094a5111500e80e902e40c51a800c0c001e010044032001e02aa4800001c58200b000f40000c000b03404069601250b003100003540c070f043d40150050f030105460315001c510030407510b415080d0380071250142801c084a0b924400924113294400d0351411443d80b0000c200400c2048011580035500c0d00c1c0b60003084103030388034038080c1d07561b240c1880e0b214007003101844200000c0440c7d4100b05040500a404641000001140642920455004011035400c480108030714000548900310003088202d00920900d40340002c15003580a030049143d00301500c0b1240c10040325560065121850343c42450b404141d2070381e5400d84001d0700403d908540343e0141d541c140d5180d26200034020f05 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 473405044 1250 473403794 473403797
    0x30b09070801030b04050127020906040903091a1309060608060306040b15040207050105072c09150f0a08010b1305090c040e1c0207060e0603040c0506090f090c040603110406 76
    0x5030342962101210200005c108460340e40d25443d00702000840054580d42981c0f000000482c134050f1841040842d15008104500a0346404018000719074410200e1003191503510501d040512810302c003622902c207200000e0890958202e00040d41a02640008202da510741d644109a48032641015110340301960080c042019180100340d18082140c0100f0038024002d0006143c028985c0d106400d42e1000c90f0220046032180500552203d0075820080c24411491190508a0b200c000001e41422000d40541002180c0c080303194090b072a500503d00386420001d041c404140d5407100124080d01d42c2e142e0a81c007404030641208400d80140c003800b40941d015401518203c80048103110040400c2d00700103969214400460944450400f900b1300c0140069014125090038588054002594034807054005e001c100100000b103506511400183c1d813003142c000d642c48406200081141240c807450340d510407448024445d40707803204401442110410348060103004600301d0040d41c940a80d200d200c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 473406294 1250 473405044 473405057
    0x151e030c140a030924050c040e070f2001060915032d020604120b130b0a0e1e010f060503030f040306020304170705032809030b04140319030b0907 64
    0x8107030803907200604450801403800140b0140f141d21411040826544a03000400740303898021000d1484e405003d07400300e205411b0034030f0545403420443d42d045e070040000041002d108107203140248101c40000c196003140640b600b501e091055140d00030000b510981400c035107801461a0058105905a01280d40210181021040c0c512010420003150440c0c0200094449450700060317070761034050001f4068803070306085500b1052601321100d590252079501c095001014410000c4d0381c8103040d80c0d00540d010b401282c1d0700148182e440c81c00c180182d003403566012a81440080341e40c15030080c00000700081c42406545da40d02c05240e200e1150350842200307504104414404100c07070390010754000b0301c5022400050740030b00c40c1c3c2c8141078010b808203c0d2fa64200141010142418000c2800d2500300341c44442011080d40ca00600f400841348001010301000c2d400140901246084a04215645000742d9696990021054141164072608030300030a03d0540f900303084d800c0c04a1400d10503160754581c032 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 473407544 1250 473406294 473406317
    0x30405060304081207050a080a02040b0d0b011e02030a021b060301170a080a0903051b03030a0f0c05030a0e0901090e0303010501050304061d1b1903020910151e030c 72
    0x22107680001c1081d1a030403020808641320ba40d80c00b1219102c3c0740c0f55a5071790b840f0a50314800802190000d0034060348640107110611003807225004481c0600081c6038006075900042d4010303914040b03840a280841200c0c0d0340071128958010005255160345070b804d42d0100751f561241d10801c807c08002081c1c01c640b043c0014003080450b1002e4500f82802042150f8000d5015502e4003015480003403040001003960b4030130020418204044126103804184e807040b030b1601000882d43d0f0340121205030040118000003020b030507000d91420208c50340c00c1020f503a0340b10071903440600440c5040c42071a000342c4480000080702d08d040e1140002520041000d140355911340001101c207600041c0003541c4965640c0e03100850307400c105100618213942c180290010705076005540d141922031f0100230f8029006100070002c9080c41c03283c4241565811101810147c4132007100071980380301a040140c442d00001048114690440c012070080c0380030381924000303801a104102d040d10b036182440c03404200d2070342c5423 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 473408794 1250 473407544 473407549
    0x93507110118080d090b2809210201080c07030f0f2016050307080a080a0e100206010306050618060108061201020d0e010e0a051504050c0a080f0c12030405 68
    0x20400d126005240c0a00009010b044481600b5520361194000e80c1c03141112070506a001350f04075005241c00031781d00f8104034030f5403403841888440c9500717288219503100b88660241d010341c8025000d0101410701c00c49140c0301e41041c03500c4a500403011380c0420000c0e0000307a465408601240c3c3d0407603043d40c3d10641920300030420750b51240c0746200302d024010440a014402c0404150b5510311110710030050121a610201d00030040380550004c0d80207811016040c0705440000509500381a80940c0e4582c3d5142c81c000200c980302005070f03801d0f40c4592402426400203070700042441c1600d014403402c10882c0c841d9001c1003a13120000c00c1a10101e03045c4000a0410343c060b03602d844e4840300140006150406090310b15003203034440881050362a98581c1d02001300c1d1320910810143e00c55910050003032840c586c03510399a413044001800c110300710440019041110511958288402c003400c4103401e291155407040c0c4800344200b40e00903520072440c105009140200c04100c01d10788910203540b0305800c1c04203 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 473410044 1250 473408794 473408813
    0x115120c1217070609020d030302030a060602030a0512100b0a0801031a13032f01090b010e10150905060a0c11040501060e040b0d0b04050a051011030606071401093507 73
    0x2042d81c0d9107039a00705c40c0c80545c64000c0c000213401c1c4269001031352841c200751071a0840d2216001003003154018030108a41a030848200c440d00442c40510901d180c0d10880c81480a0040e03402404001d075002c01d0003c801904081003078183c0f8401c0320a0407090280040c100020b8a08450100704240090041c401080c0600c0d0013124850180d903010318031440c190b003102602c8040c0780f0300d50420b0b950b613800230050081c0040c0981c058515035401d6330710750a0944070540b48010900850b10f030307003403000c3c900031070f4038004c42c000802042c0c050142c0340c681c018504050701c00392002d4816646801c072803500000d985042e00c2498182c0c8e8035601c6920b0a10024418400245030003140a42c0054181b9040c001041102e048184a00c0c8500b00400b030f825903d1410f01d040c46106c0b4034160341ca608107a1814940101a01601d070b0110f8140c481c2600c0b0352441c1030074108038190000d104895480d05036004140b04070f001c81d07060307031442020f0300111502d0301948035040d081010250710702d510002d0044d203001036110740c1d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 473411294 1250 473410044 473410057
    0xd0f0e040b0d140d1706090106110304030c0902040e0c090a14131103010512061b07030c080c01060306200306240d0b1f021c020115120c1217 62
    0xd0020050051603600c1060000502488440c168000c02d584c42126070310060103081511400c403101c80c0340c2056008100000c04c180504400d0154990310044800802c00640d1300560300102a08400c41d9203243d03001c0254000e01a9072020402e107000240d103015100100c1b0000003000e014090b903246008078400401100810480d40000c80440c1910080741034095201c031002d01000c4959254901800c02c07a980c01200c02c3c40300150002030400c110034090700d081191001101c03c18030380e640010720b003c42d040c4402140061000da00824004101081544064242c0703104030307000c001484c0c810204003401d240c0b8202d031101c50041040090301a0411103c0007001c4001803803079249030110b101460b42e00d90000b090320345c9410f50b61960b002d401d140c4641c03600d01c0c1c501c244201d84918022030340b0094450041500303640303503130860b1041c1d01c5005200f540110328400b1a02c1121800316186c0e807840095580510b829107001c6842c0c000444d49250343c4074400702c0313950300805070195440e02c80444411500a00c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 473412544 1250 473411294 473411299
    0xf030608030a0302040503010c1803060902150a0c0c05120c0607020307120b04060b0402030402010e0d0312180201110622031b0b0609090c0603061306050a03060c020d0f0e040b 77
    0x111000144280104064480200c06890160305c480c100400c1c5030840b80c00912200402601d03040f0f6180c102c0c42d2004440640c0d17009540030a5903000e60010030b0308007071102246c00c0052070000e0340c024016409181c08000d18843c980c810301c40c99452080290010b007500380085030ba0480e0100c0400da291050043c402688003400761034000d5541c8c0d003450b8150206000039100754115108000401c45c0d00e00c2401c0258104850850542c10301d500000e000418030b01c401801103041552102c10300d8001d00700030004010412090040700504d6102c003903910712200b8104c2c00310380c16401001504a001c66218440d0341a9a510886001d00081c5510190307114401501070041d288440500d040d206031070b052400e40100c182203680e041810501100e05802040d180d46038110700d503540034658503082140c0d08014100e4090f6020541c440a03d00203002c150301059000e42a000000200940c035000305111030000d400b030300d452080f0030500b5a1024103010340c0e03400040c001190340d4a545005e52090240c544007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 473413794 1250 473412544 473412551
    0x51207090603120206070309030c02060901050d090309080c0f03190f050706090521060703021b0109050606010f090e160302040e100f050303090a032d060c02070509010806070f03 78
    0x100c000d03020440e08580c00070b4031621010b94107500081e404011190b000800c1d4034040100003481c1c0c41c01001e046914100900c10400096130f42600d82c4920140c48041035202c8040250701450714021f003403002644100b00c2d0764000d40c1c7c000686450320668032155000041e000d0402181c940200400d10074410004441a881c16401032000c510204010809001103440700783d1114180f404004161450b01c480088282c070010000305200710100392140c100751141009030b1112080380c110703215411600220ac603950300e0415035006004c0c0000d4000d010700c0c6c0070f80710030141c500312260445480d4240e014400b50301035200c0101c1c035003004000707106408244c20b20780142002e4891118611014007518030202c4400c526500f481600801c00e114001894114000c500e000002e90106550603128800585026800d0344907864140d101403500c01c0c5180c1a80c04200c00c0d4a052030000002d040100500006104103513000c40d140c1000c140071811703942c11000806955407912802c803081c00d211594203080644 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 473415044 1250 473413794 473413799
    0xd0501062c1318060b1903050c092203020303010302190f061206032405090c0a18020d064a0402030109080307211817090d1415060a051207 61
    0x3c81080502624401c983c040380c00554082081720f42c80051440c41820031000e0300400000310001034560910009a91a82c00c903585d8000f10039030060344840041ca03000c0d00b040000308040d404001141607a100303c45da040d02d64140c8011901d028254015103501e030004000030300105000b2840380118820b02030303002c280503490b6a150140302c0740b210391390087c102c6054050411f8681901451f0b41c80000b0718001d14804210300001040c0c203456120742d44404102c407400500b69030440e0100c9101d0f2012000500c000b556541034081101021001d00050000d80b801c0019003604d04414162a0140c01c2056105001c540030041c801c0c41c0d01501c226495961180c40d0000100d21070003031441007810307454500c40c2042382408280b802c428040341405992800340040d1881000309441c6002c60b0300400f4083c0c1d440b04c59013400c09140301d400c2c400c0fa80010860307014010000031007001c68103181d918003070352603104c06400e01d010f0b020410b0390100d5100000880c02e01c102e0a1002802840e00c041c00100c40406a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 473416294 1250 473415044 473415071
    0x303080c090418030210290102030c010507020723010f0813050a0b07170408120c0c01050112020f0d1a06010201270203060105011809020901050f0d0501062c13 70
    0x1020f9003c3c45011408120320681816014480f074003102c0d4250380c0c24014549a00408034225403c00800b060300841d035984149240d10070010340360012404402040941041c000186d9144080d2190b141d80c62075000c5601c08002d0314011301228038106840e582420704154200380c5503500010660754058541200140114100b004200300c0306000d5884100c00307003040e940091007040c0d01e04410166400203018000003c44d458212003d20b5000f00d2140c80315100c000d85a006480b41c0c940d0f400c250f6003088001308015203c0c10919500c140700300ca80400c41c3d01514207200c8960844040506203c051075440607605e0404600b49034002014400020b5541400d040084000031201d1184803403034940702124114101005694003514090070702d054542070550300c03150309501d01e0017071480c0250003040c1d0300705690103203003521440601086103a89802501c00f0550040209210f040b000905628146621200071a880300c00a800c1030760030b0200d5071455080c0100c0240b0340000d290300e01c2e0780d541d1341c0300800d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 473417544 1250 473416294 473416301
    0x16061d01210c110c03030906070501060e04080c01140f15010318030c1b08190515010b03040303110306011211070f08030106030b030105061c0f080a030c081008070303080c0904 77
    0x40301011000804107150180103003019038550300c5000983c440d03501c503041940c00109441f9a0681254407681d140c2c018907105001d0041070b4441201c000b058418001002044005420901d0391139008201d01c03020035004448881c2d06030340656090a0394400f0910034000445590071510041c18041106100e52407d007445544488041e0002001d000c07a940800c03500d80c0e007440c220785884601042c52420601c020340c032040c0319020001d504004000b950204503060014010b1000e80d180c8041080d0b0b540c90012403142c0c402c0340c044001034030305540c2c15886420340701502c0c0540410380d9003200c40303100c52007024014014461001090b950500855001500b00301d00f2801c0701d840b5510454980d45445809410b0b114500b0318180b190f4100010170045850701c01540300800c1e19044001d40c460150704100c00796410300b21003e890f0b5500000c0d4141030700c1d0140c000d00501600f40ea0350780890340d2403400440c94801140901c081d65040548100f000c40d1044441c03d030060403e810351403511410800049c100e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 473418794 1250 473417544 473417597
    0x40b090a0c08010209011211040e0a0b06040909060b010c050c04020a050d06080a0506070906051c0207060905010c0e06130b0a140d090b07030506030c060f1605010501050316061d01 79
    0xb5a400154070100c030750b40084c10f0900e011140c10144419a6060079580031805240186028811140d0004800300000d4221600055010f00041d98a40e25050408085c00e4040d40595030b941c00c001c0030b05115403180c0b084071750894014020b801c030100e4a4040201942c0700c0d21004c010400140030750f400b152510702c1450010f020000003001916141e01e400e50601c24000d00e10420b002c44400c0400c21940c1040481e5282c15924143c0360103a592692084000c0c002c50704050300321761504c81d2600402c14150310a03420101c2c07a845007070b00c282c01c0318100b02c80d91248840f0100402e0740700c0030030081e014041c400751900820310305140d520049a040e10380c84c1ca0300071780c0d50580c685849003006020701c18001020b41d00861079240a010310701d45000825607410000b1500c07070181100290013009007041205443d0002c0324820541290005820410b010303100a00540f4803c0c0200d4102626194110170040101d40031911105840340300c110b800c62001440710712071410301102c021004040b0a01c400b03003900 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 473420044 1250 473418794 473418809
    0x103020c031e190f0c0f020604030501151a04081903090b030c0423180907170c030d1b031110020a0f020c040204050607060506041803110d17040b090a0c 67
    0x125801040c9400d103400036030940242c140b0013100108000716030312411038101240c1003012444108020710102d0400d2245610241095107820614120318001080742d804641590307844065592607902d51108a100d00c0c41000c0e000d0703210842034200e00c1c00c0c04040d4000940030b820031190440d62001324517826401150400c0100c0c03030002d014040c40c3c402a0040f15880c221041c0605aa66102c010608541e031b0a0190141e1468100001c0c8540c00d0800a04000e03109007442e2842040c50050117598941c1e04036445c0c0d02c2400751048a1900354841c144812040b20004200c501d440e40c1c80d20145c4401c1c022580c8540c0c00e014460101d144000d42c0d0009115406040d541c0c248800945580281403025034110b051050f07004000400480d41e51105a52405030030450009054548070001801041c161800410101c40207500e4000c0c11740100b0501002d43c4e802064480244403601c0c1142c500b02c0081c0c803081d25200300c902241c04950106556544820b2400407903108003280c1d101d500c00c21800c0c1d4085e0300c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 473421294 1250 473420044 473420047
    0x2060709031104060b032d06220605040c02011e09081b0f01020f030403020f0f070915080111030601020d0905090117030904050f090d051e03040c0b04081e030a0e0103020c031e 77
    0x4110740d0310352072006005887c0203580c55801d01c68001000003007032180070b048100c01540708454810ba40d84c044801040c0041003040380d61207400c2e020b03020301800b41400d0304040b003943c4c079204028054003c0d02c0390305e5842880c035840e122101130340810307020030403400c0c035240c0c40b90035420100000f0900c01003021f44140c8464a0b2070b45840d281c000e01d040002aa01e521f150404850800013040006443d4143c9810243c08550000c201c0302e25500d100031540105103075800e141c8160008000c1030b000f140035100030ba09a40c86801c1401c011b4034141254401c0c00d8211403043c00402240c20385002c0352810300040000d4a251401140c0020141c90065179010429554501800000b0400700017020701000c07582400c5090440401d20301d6483c2d190401240500b24001002400b00000c0350b0740803014268015045840d640c0710f01c80a503541019007010039038907003034580e02081800000300f541d4810096a80751500c0f404e444004402071b4000070010004c81c0300034482d071101440451760450099510b4001d96 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 473422544 1250 473421294 473421331
    0x13b0717030f0a1d0102032a1204120b0609070f030218040f0c0e011718030c0609010e01050606041203180b07031d0a030209150d0b0a020703090602060709031104060b03 74
    0x40c00c19101c0b130100c05041d5401000840d1200001303981c0d03812030000c0d00c0100e8416000f094030160604d14141c80c494000d1000180c0450781c80314080c850142d040c000c0e11030039102d50790401880380b00b000a0701c03d000469150420160400d200350024007514078910070000a509102e0085801d40d01840c125030b05250303c40b0066842180e000941800c00c54091074101b416480d840d903001c40d01e403400741000241d0b103207500c20000c0c0007000304211003501c0c4000044803406e00d8620b081e18001c00c560100c440d074070b50030000400c0781c510741042640c0c16074015001860308400c035940d0a407021200e000c01070004041c4043c00040042820014164890180c0c03100024003c4060080006540c4407894034800c908608080c80982c90b980d0362954441c1c0c82000030134603017000100040d0000307940e56004005040076410031140100350f8010300240c0f4402d4841d403412548811050361554400c50302c2000150120300d0800200700d42488041200c0304c082d000003942e1741c6071028115194812a002c4c1604400f2001e00d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 473423794 1250 473422544 473422577
    0x412060e01020405060f07171611030a2103060302040f0c02010b18010302060c0c03070603090b090d0f031104150e01110109020109061101020c013b0717030f0a 70
    0xd0110005960000b1490b040c2000001012800340c21481924400082594420045902640941491440a256220341c0603844540c3e1070823040c1000c580544140d0055012401c0005003801c0b08c540c45421100c10b250003031100310b078054401a0f480308041d2181000409601c5c1d40c480d142d2405a07408010409a40e90300010b400d440951a5542c021405442d9a07002c0403004101d50f41502d0341124025036078010072540e145020f0043c5999030b414058100c1c000b0f045501a030009159520410b10510b0554034202c2d640d4403440d101c1d0340000415159110181aa48642d021032041c04681e0800d0703040c640c40d603101465688000c25500d0100f414520301103031070740e0415000c1404031040b0b002400448182c0c3e0008140082d80e01c0bc160030700107036034500300346a44290103841e00e094080307008008070840310b0251a40c204000703801c000d0420740521044130240b1041c03003407400031400ba00203009151070141b0a0300c015481815024060005104001c14441c1d131000404541e00a0f03074844141c0e0b54070300e46 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 473425044 1250 473423794 473423801
    0x1b050d0e0a0305121606140103060506091e070212040f06091211010521041505071b1b08060708060118030308070c080d060608090706020109020112110d02041206 71
    0x480d0340c4241524801040011400280425103050044405031102e510042c1d081144024960040005003007903885500e0300108006c2e00d040324080c813824042900c0c1d103400d0100f00b100c01d40d80090f200404284030780046003104111604000c03284100e0359401950010841650040d411203810401814010001d0700c1c6e01c404054054401e0100c0300030808820ba071000203501d151039031981449008034000802c6500c6001043d06e1050b50181c200503407410703182500c00d0f060802e95100209282c040890140d500c40c1810400a88000300c40203680411038072034030b00c440e4114a800e61074152420380411003a1050180034050444c0761118101c40c10100009004e858003e00411030400602d8820800309501909498002180d420050f14112240c10400e10342c1c071555640e0680103040444c0020010742c006c480511503000441916989515140200d0a0313070510380c0083d00140c030382110000007070101e6010701100385244003a549084942100041680c010360b02420700e0741400000003050124500 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 473426294 1250 473425044 473425067
    0x50f031201051f0f0e060d021902160f030308040f020a08070806090105071d010c050706020c090a050426090904080a180501120209030109080f0301180e031206011b050d 74
    0x1404508003100c8880c000c0680c44d804520314108290458148000d840745c1040360408158404150b43ea00280c000210b50b01c0100d200841c014490400e491301c141000440d004c0540359401c1503003419524645088a900b00c028009544076805110340200607a00c081c05000104401005885078a262404840c10600f0041c02c0102d203904100c02c10140d140d0007500d0f692042007048030031010019190040b242851940d100418602c2003080105006400003034424a484044640034100e90310700f5125000d5980568006003d114140300782c0400401c1103407008901c2001ea21081e0410046c200002c55090003524240c07154440040d5140d46154008801e0040e070031640107010300207160000090103890040e002d503461960106201c02a50b0b001c2d0003090110350130604040c1c541a140039420200c2d4400e01c20352524600703241c4031442d80707501d078020b141c0b5403442600034504080d84000d07102454880140300c40d0400150019074040c00f00d2189803410358074001c20050035200750541002c0d00000c48003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 473427544 1250 473426294 473426329
    0x921020306090c0906010305041406010305100e212b05011406070b0402190b0d020c070503070e0103020f0f040e0a03080601181503060803041d011d060d050f03120105 73
    0xc3d102890584c0f9070119564102c1c0c8280790000c1d1542c1c844c01d04110302d60403d002c101c098003800340000706201c000031f9a200c0000c007041e0704200700389000b890640d44150b00810103c00000c2000c9060f10a182007028019941e408140c4e10041d501078880b0741400300380308444100c001d036240c00500003040ba6000a0280030320613140e1928150142d01c90750b560b0f500081000b44240755411302240d07040d4071190800002c091141d00c03170b500c03282c0c1c0c0f54801004e50000350303500c2d02511070f10000107028900014008102c0d000422001c0340750b403c54080c4036513503880c1e40305290410101581034140e40ca840c801d1595059260740038280482d00707480c0007041500081d0010b410007180064000c120701001c1164030403528407651245038911000e0094028041960000d1090300010400041407143d200600131401d201c0100b290107a1788503d00040860281c85211000080c0c03030300042e0080c1030840c0c5050b04c040c000c80c02c4032503500303001d10b416145070700981e01101365544045c0100028248006624880c5001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 473428794 1250 473427544 473427553
    0x150206070f0e030c0f03031c1b031407030203040f080a0e0f06040f0b070c1203021e160506130e071106090c0105031909081201180902010504090c092102030609 70
    0x42c10020b80d40b641c0840c4600d10410251000c3c90290380c0800454100c0c2074103281c41f110840800480c0402051040900e8483c0c00705008070410a40c031a110342945002d00f2081d1000c5519200f40850094000410886030100413070181008551180054040c24800383d0310000081e945806110071311507000d0704603001d00d03000d00050011406440819003907a01c14400c480d01c0d0720030380c141100c044620742e0010560154668200e8141a8041102c00c068401d4603e040f103040203c0e00725036501c00c80390344030000c2036500c2e40d0140814607214005008051030b45000041b825114010508a11b2003507404001242da0083c2203c8061000e00c042688008840c01078185841e113180003070b145100c010481e6040d1005401c1c020347c406c48aa200d581529007100d281c7e0f4660f6010514407140560a00504402c1c241100510903030312141d020741103100d64180d464505191400c00000c000d00656002602440041800440c09803501404e0801c0c2d45000c2d001c1c034852402c1401410b040000c003401550700340e0007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 473430044 1250 473428794 473428817
    0x9040b090f0a0c05060a050706021305190f03030e060d0606020d030c0504080d0302091201060605070b011e05090c040503100603030f093006050702060106030506010f1205060a150206070f 82
    0x100343c0780840c211501030711250350f1100301240448075031044980040110303101160b01c04400c044c2807200c0040d9401600c0580b00b6200307503001141e50341528400c1000c00303481031105100091181031408240e40000d0003150600004546800981e14260003620060703110900802da001e41c14020b0040d841207504100e846c2900b40201e941d00c4680c2e0b612500c06050700004c4940c042d80700e0218002441380010000c11556840709402480f55110a0b001d40d0040b00480012440386c0301302840c2c50300c0f0703024403ca8110313680c64003091042c8032400809c00e03860080c09000010345910240150b80e40900d65000c005041d500390f14002c0e100380503040309801080403030700703050294040b89010031a80300100b45150200d441e14840c203090040240a0061a0600301410b00c00c0c60340c2c00051090603503010780c4041c0225922140111600000d440380c040014108140f404440b0186511240d0058000b5000c80703200350710340c8e108004005444944800582c050005c01c0505540980c1408480030342d03203000c004681 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 473431294 1250 473430044 473430053
    0xf020d0f170a27050a141503060d0f08092707020606030a0609051609140901020c0a0b0a09120f080603070f0501030b010e040501140301060806091c050909040b090f0a 73
    0x15a40e140c400303d0444074034968656241022165401030000620300c0001680f5126000c949003400d950090080e1580c8040099801605084d82d2240c00003030b1003140c000c4070303903128400c401200620603200c00f0400c100301407090301c5840701c0e000c440c01100d00c007501d0580420f280901e800c80c0109200c045421442c140031003980c0100c1d13250511508560045031401d4030f4200700d824800090100104880c0b0f646000500d04c96540098081c01d544280e00c0d55640d4130840c2d01404c2c0e11034100c4c03c0100b50084000c0c900015000c509003030700494291800102070f08030f036031203544c80c10702034000c1004a080400e802032400c0d0f0003c1f285078400001d40c0541a4145424000e964455040c05094107040e2142c000c41c10782d074441e0071040d007540d00080082c0910350b50381d20300d0f41d003445403002d400c0e00079420498042041800010007a024488060041142d0580c030211501c0304002c91691400f0054100300080003a55140a89400341c3d01565041c0520b0900d903440300c0c601404882000003503000900c190000c00d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 473432544 1250 473431294 473431307
    0x70b041703131703190c03020c01020d0504270e0f1b0f150d060609050a0b0702090a110d0c0305060405010e040506011e17010b0103060b0708030a090f020d0f170a 71
    0x120f1020000d03480b041e201d07408040c2507001d010000302c840342190b881d01075040e80c08100070000302e000307800f504c0c40703124414012a2a03951915040c000b00303004100402c1068266608120a03017002502030300f118810469100980d5100355051446620110780300c40c1a034010704c0f01d21856403041e04030600c0310f104140032548101684001c00c2c414800003804915129000080310080c006001080080944400000d0b2840c41140100c0e8000c20811f0320114000005500300d984e100e800130000c036000e03038411803028041c080200064802c030000344040b4800500c940104003000340691000f20316880c0c201c003070100f01c40c0c050380001c9030400480280004950007090582c1920805026900304034a10010114135820725808030704080c40c0d4035135200d41641c065001d01303150002640d0521000c0d5460188038030301c0c06414000b0300f20600800105a01c58a00e90001010324420000c003000a8020f4000a00c0306032208001d48810b111402c2c0a400c120b0f1000d8407502105e4000d42e62030504181c0ca4005090 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 473433794 1250 473432544 473432549
    0x4060b041d100515030a030f020607181203032003041a04020f1905060706020c0706020c1807030914210a0c03030b03070f03081b0a08030f06010e03070b04170313 71
    0x2c0c250b40300d01003080b150884503450303810365018003100d52594640c58001e0aa140b00b0220400600441e0003003800184154004e403c109482c3c044501c029041641081c50016000341c110b0505556444c01d2000c034242d110989480c3d518120b101da160314080c2085c0b460504000d80d400450407030030082000598880d4421303401e02d46c0c20365990303055140c5860030f41280b0510703801583d403000001ca00082040496002810640404000d81c1c462540c1c5200c2a45c3d00c03204403840340ea1000d02c0c409039a4444c0c0000c100c20307078007105918001c10000c400da1140071001c0c5054004d40c8842d00a108001c2d40960007100c0081da40c000c100fa043c0c90620740c150010883c00b00c0e880e00400701a200d640788603c40c0c1e41040200060301ca0703107501628407590380c0f80c28031607640180c014a220300401075801000c001e0110707003060301a4021035114559658a444107a02a900900c064103000b0b8045540049441c2081114007503c044d401d81ca540341d0410342030a125461041000b100c07030b0302c1042100b016007aa40f07424403c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 473435044 1250 473433794 473433823
    0x131127040c0801020f0a0207141f0e06040303052104020f061602061809070801050904120c06110309011503020d1115030a060f081506010807050405060304060b041d 72
    0x1865291464001001d420580c8560403540c00859894410262100101145016074003120b03185541d0342c801c00640c0d0303200da01180d0300c044000401c10715045003140351403401c521031900002d07030f02d60035000643e1a04282c000354000b5102042440303811201d101c1d841c05e00382d58402c070105140b40603400a000300c415001440d00900d404204810702c0f2050f903601074112a8010140344c2c503101d4121000c40d603000c1c20071445100e0300c0d45402262049018240f602c0c140c4501802c1507060ba82d943e1500d141281700304921204204441800d00d0100303540c0c0c0303d0498110020342c40a5940d007040b44200f42074480031801c09200f0040400200016070314051400c00c0703554032400d40714143c0c01090004030b61045030814040700700c1e000010003800c06944d6201d9410703540600241140c040d2106685a0b83d18071610707034402e982c20503a001c904958083c100c9154400c40314500320349019200d0000c950540c1082e24100d40d02c5440744211540344c5080e014101044540040d034003003a100c031101196968001c20b41501c1c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 473436294 1250 473435044 473435119
    0xc0c0b0c131403070e0f060315150d17161101020f0a1205070c0b0406120c05070b040c050324070e01080703180c03050c011205100612060e1311 63
    0x81e01503e0034010b4600600b83c104c2c4662a500d4199a407004056007151032900c2402407006803c8280012018a4000c0da00e15070030f000841c2145082c001b6020860700162007840b51000d40300c2a0034a02c800620803096909184004040b651400012500e40c0300d61540c159040551002094040022510702c0d0540021031302c071036051701280c191102d00c141746029002c0c10a5100108180f680100200121103142d0380d102c82d42000248010200c0d802c0320500c50019204200d6100455101d105140d01b240c000c88400050a80e40d00001c0d03c1c1c03e003001f51801d2403a220001c42c00440080b01c140c99403240907400c0048886484800003882007a00a000505041d640c800e031040e074501c891015030a1035031240c1443c91194680c100981d540700c0c85204580082e400c1c407403101c400015401050f004c0c2c40c404807481441c07401c1200036a05040002042d02e100c59031401c00290b0129084240d500030f504071b001c6101d80340880d04003e0621444511140c0c01402d206455500c140c0500031000c181e1543c0d1000c16 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 473437544 1250 473436294 473436329
    0xf18030f0f1002180306040c080d080c0d05091c0207030302120a02060117070306020a030e1009020a15050c06010f0302190f120302010f24050f090a1e0c0c0b0c13 71
    0x4c20000980390001c81c3c0500c6030404100401c5448008a4160741c0c4000480e501c00b800d070202165a902d049070060030740c0c036003840110524a4030350006504059660152031881c80742c0f00031030101000381801080181c1c4040420402d1607010700c580501c40110b40c0c071707441c42c08800103000b96440d081841217041550303c040c00801000801d02903000078681c88071083d542c400c0c1845000303019005500c030ba4100c5000d408401500d200c098841c40c00c040c1d5010303050100c0185040c4041d0b44400c040c0780205d040c81003c000c1c08078200d806106440c082c24040d100802818118014007400c881001c02e0030b030748071418010a00410080130150011200c0d02440c1e405c8207401460200e015101034826a50740b07600300a0142d90304001701c003240048074080c251808060b55508100500050112045034001c250000450092541074102c404800d041030300f40300f426008110b01c40101d031900e02c0a10005120140c540040104444902e6009000c05134842c0c00c0c81c8084c8415102e050301071087c020002506c0150 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 473438794 1250 473437544 473437567
    0x41109100e01110601031a0606030403090b0d1d030c0717070509070536010e090606090105040f030b16050403030e130608010606110c0402030412030f020f18030f0f1002 74
    0x1103c68024043c001e0f10001e5940e0300d04000712036150444007001d0514840090a541005000d07244aa41c0541e581c01043c0c0c6001c0400070580e0080a034441e0300c64641c0c20300c446e0b60f04c0070b4002c8000c003100c003c01980e55203604402c580c200f244e0b60b0014007001d284004100f90b80c10300000c07280c060b11404c89901c43c050b100c562058540e8030a2030340b40080d040402e2095401291000420030303480c0c80c404a41c00050144034011100c0400c0c0203a010351080c0c190340891490308064001d8000c01e081070600c10324142d1a4480c110b020310762a40101c0d8902040c0d002c0100d0012100ca40c1810140e19050050a181c290340d0060080ba84511030a4022003400009014071003003600154010582480200703c2ea680303401004001e050114030a01d014418244880703000e040503c2204d1007a50441c0144038816840c003002c80c0544400005030240580034010b0b90504202200280600142e119410b07217940300b60028141400502802c00116820503002d100c1c19203400318101c1000c9180880050340c47c45076482 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 473440044 1250 473438794 473438807
    0xc090301020d0c0e03070819062c0708151603020c1f0902011107080c0108180105010b1c0606080109020a1b031107090b0a05010c11041a041109100e01 66
    0xc5000b0300505256204500d5500048040c0d48404141c042c1d8503903a40324030640740e9a0000405490702c8240207035404001c0b4003141c0c00b020300c00b1903418032484003500c01c1c101c103034800c01c007208100e609822401c0d081144000070000304642c0d504401310030780325103010b80b0714240031706026030304006150b000212100c0c000070a02c0000781501c00d0034402d0440351a000b103000300a000c4540f04901144d2411002e00500b45c0000c8e00f00115507002c4028107000c400c150046030307404805000e8880d681503200360048085002c3c01072501800b40685460f0320381150400304c0d03145503d10f22889101514042d01072022035030100e817060541e45580e0700540d82d009012000c50303081d61040c610b400000c0c0006c1c40d80040540c4112540009042d04d41140c0c6481d446002c1502181c50300c203a95940130340e0100040009501480d81d54101034040d4008182401c0c02c0300204003a5441d1114800b0b02024036442911540361274401c2d444000750000e400d5007000d11104c04944286402050641407220981520760340b60322405 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 473441294 1250 473440044 473440057
    0x140d020609120106050a0801023c180a05120709020912060f011511072105031828170f150f0609090a0311030f04120209060411030c09030102 62
    0x410481c0b80c8030b21000c8160080800d406158030500101c100040c8005050003070710415441000c0c2c0d200000901400008007150004070000402d020714488408202140080c0a901e400d0028072400907154000b0010700d003056401c07142c42072079001c1c0f04e60080d020005a07d025940c14160040c0d40301114030002d5138902c1d0844c1c401420b842a1420020090200c40c8054102e40e40e0050130441c002418000780c070250f6091100e54210f90083c46c04005070456034102c03414015415074244464610780d02c52a096070f004c1040030001251071110220300f410100d108800e400181c0c40f41c184e4203030980703032030742e6a840c01071041c08020b0030383d5040c2c03008500050005584e4001c4440c1140d00c8044108425801d034042110010340101a100c0041d10504103a03844500c581d154102419100120b50790030b507030280ea1121000260301c024000b206a4480c00c0f801400504040d940781018501d46104122488400402e1030f40902e0908000030443c845d094203880c0c000c07600109139900c4006005c0824024080c00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 473442544 1250 473441294 473441299
    0x2210c0d02010e37030e0a150e0103060602030d02071502040305060a0b06180d0c0f06020304090e0f0c010f02010e1b040c020105090303060f030a0b101509140d020609 73
    0xa26140158055100740b81d1588103400340c404080303001c11380c1c403d800f0320182004010360711070801c01540300708030a022010350b01c80d04082c20786811480100f02010156080b25a50f001d12150203503282c0e400c01101c050124007403030300340320481c28604002c0d201e005401c080315205030045078440130032644c0c2102c00c84500204000710b49403940c0381012955890103031801c0e40d84a01d40400c00c1520b042c144100da610031064003082003500c200c0310034021a060025800d840d2104040c4011600074a552811401030103554011902c039401c0c44602c2003120f00300c0c1e0018645030b00112004c41d1843c004500d0070b44081c02401c0c40c0c101018005000d0307006d809c0d02d140e00c003054050b9240e8811149030700003025083e02c40c1960701300840702242c40e05a00300e0f5816100000382c2c0e401400003c2840c90000e86215030040301500f66911007610342d4407050f03503004c103544210228103911020b00405242c040d44508440081c6080b951030f61804a071171000c403000003003980c046d110542c90b50041d0b480b1001103d5060501 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 473443794 1250 473442544 473442553
    0x30501182f030a030201050f2202060906090d0507080f0109170f042103030c020303040b06060f0702040204080d0e15030403180806070306030b0603281e0303050a11070302210c 77
    0x910707000b40207047c00c0f034000c40b04641580200c0d03a0a02d844050900e10314000340900c460301c400c2e03000c02c65540c01c140740c401e612200070088510b407500e5400305408252711880042403040e003030040140c01e00200c40303038440c2c0340d030702d0b00c4051030115001600201c41c0048010a071503884180e2014041e11b84500d401140d8a98003240031000d00b0340404c003808080724000d0340c04000c801500c0c0422a100e20050741c1c007803c808007100c003141c180d291100081c4902541c40c458107160180701d9010800b6a00f1a40c410314a50700300ca0940141c241e0484c2005080c401c1c202c814284070303100013041880a001c0a00042c041010200aa000c104121a5120068a0f07030004403906482d20090040160120380001c07590307103142d80041805403c0c0004d0400742d200311284c0032907803c5c0340101c0758424200e1041054900f800e500740ea10740408004020303503c00300e009036000300d1103140c008046000d0702e00039042c0c00d013480740800c2024042036002c100c40000140951110341207220040c6003610718000c44000b803119014 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 473445044 1250 473443794 473443813
    0x1410118240602060c0307201009030801051203030108060f0601122d0b0d060e0102070f03120e0c0117040c030b010b0c0105060405010b090d030504090203040c030501182f03 76
    0x800800e141e080324496400c84090703540701e9a03480c3c03060000f61900e10101d001003605814020700c64411003a0220944201d440400141c0c603130b003007658851034003a0046080c800c01803001d82801103001015244170802140386524142c943c0f55a079200611203014060500007140c400d0b03102c0e481407000340300c131180107200c41801803001001c0c900749864807407986ca0586043c403080e03c5150150b1125002d00424410382d566440d140c0310064105c0e601c4140e0155170800035040000d02c86c003454541d00e4000e9a800800001008420701258800146400190301c03540560819a91041c031016030320002b40d43c0c03015551598038040114900d1508010444601c3c1c00021803082c3da1100501a880003800003400b89480351010b00c8121407080c0503102420004002d01800c604040c1411915503200b03181c047e1600d99210a090201c0e0401d03101100d03004e40300b01c401c006000003402040b441c2c1003003642a654002c0b43d65030754840713060b4004c1c01400c501240000388881c00e0790f4850003007103650090142c511300030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 473446294 1250 473445044 473445101
    0x6010f0c0c09140612062206060e010501020d02070b0a2109061a0904080904110f070f0611210709121a0108071a03060607020301410118 60
    0x201005201040003d000000c0c240c0c030b0f09041e81806011090050552912400b090040322030010f0048208802c900003001c000a26510542d07001341401d44d5524080e50402c0002410180d040d580401107501402c2d0510021546008482e0b40c119079040024103404401d01c8010b4284400c2c0500e03885c60b01c1d00303a00c10140541c54000807110314900d129000d0480140003040f102c45420356000e825100140f142c060b032070a066020301c01410300c43c0310a60904038a0b0307203100e10a90052108560030500f4402038010480d440c090605041120388081c1e0402c80110080c61202c90490004480b104005022a82003401098075501a00d801c9403405010091401e000106150039038074003400700c42c1c7c50000a0002c50200301e01c0145c4a605003500f9024542034035104640e0005800b59521010030044c503001a5800d01c1110381302d03020790024680744010355548200515850134600404c22034007100e0030069014602d5141943d402211001c0d403006003008100c000c01d01c034518414486210b402178032410 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 473447544 1250 473446294 473446301
    0xb040b031e0f102709020f0a080a0323090f0111030d060e06030d0c0627140d0203251703040b10060302070c030b07020a0c0902120a060302060306010f0c0c09 69
    0x1403000070310021040b42e07a846107410320041443c10030213202c9000070521000d007081d045101c056000078403036000140d030400002c13207410280d4440c117100d9214050100030540c00002e1014181540301580c1d402c11400c04401c6058400c0003140f5225031884503c0021580c0030340c01d280c44041206080380d1312119010b902c0700091400717001d6801c48401c20000580d8a207000100301d0b0201c4d0700c9540d16405520309a513014058000da12403604100000c20241c01070154690444000b94000c00ca501c18000001e00340904001d0302605410840d00100175030006030313240c0100d800e010002603004100c80502410604030b200040e1088104081c0300000340420b014501d03090500401c03c0d52001e800b043ea0b500011b8040b8030401000902d01d0141240820100e110099041da10041c1c0e801030303900d102440d5030350b103410390695007181380d81c20303030100751003a003100c5001c081c81e400085080d00300011400d6400150190000400711410444c0321080e00c0c001c1d500c516102d840d140d50103800e13044820340b1400b150024 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 473448794 1250 473447544 473447551
    0x2160b0916080d090b0403030c0818040f0c11011b0c0804050306041b121502091c08041403060105130228030605010f031b0f03020f04031109100b040b031e0f 69
    0x54007200d008170b40c0045000c00c0790300710b0354951504180c400e901da462400a41201400354042050070041507800e4549000d010122450104005910b1030908006800c02852050fa16200d81c941800c100d80070440c51480a03145540d030a01c99244040f500d005100742c0b04942005030140500d2083c00108a600310032015081c0480e1b415000042d103c03154001c2c500c0210501030b084a030700883c107850290841d4001d1181e40300c042c100005030520012040f906141d01c16040741c407294000b074108080d0041c900409401c031400c4000d00341c1545040d0000e8900c611007603e08000d1940020340c2d1020740d41c0560180d400020b4184000c59004101c800030340108042e00c500c501080c0703075011980701e252003842076009a201d2604c841c20071149101d0308a40302e5240c001c000040c03560070090002c818000c24058001181f040c203001d08500c04010034008555405400b000851003840403e2145031134050990b0186ea5540c001e0540b00e5590007920450b9880001420807206564014807624143e800c00d507511 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 473450044 1250 473448794 473448797
    0x6070c0308070227071211070b0a0b0a03030e09060f030d09081209030a1b09140907050909060103110a090507030b0a080f030a08040f0203010e0a030806010302160b0916080d 76
    0x4010081101600700000b1102e04c2041352180000002c00c04ca00400c030300d000d0407114010010f1850080105000d03143e024020903100644c00c0010000190b02c0e50041641c4c044080d568141407a24565001e0880c9a10100c024070460b500b000280309a00d51261072140350381c00400b21810100b2180c00a0304000036030207250054080c080c031040002c001c40003221003008028004001c88202d580790a50b01c0d4018004088414401d07940005030481c1e21b004504c48504030000d41d075100c1c2003030303041149021415400780780140d0404e420454a140041003107811070303030080c00c0000710200c0385001805800881c0c00c00e610b00351a004c1400701003a0f0643c0041038044081e50200445134680c00401d607602e58003000e40110342e02c1008048a4103100320461500310740708074002013400b5502e0b80000c0c2520314041700b405481d4420303903011050580c0260300311703000351080c00d045203020864507070014040001080600001e140030089042c11604104000e084030098100380038290300c800450b40c440251614403070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 473451294 1250 473450044 473450059
    0x9120816020604080703080721060f050d0f0f0641010b0a11100204140a0b04080604060903020f070f1401020f07060e0303130b0703080a0b091506070c03080702 70
    0x150301078000105240a030b5081048181000d03910b0f90110740c084002003680b4200210120200303001c500c005949484c004911602051079810f04011105079003542e440680304082c0007403044081807500c00e460500781e4001c1a00b05542450b4140700014051030b02610034661725030000d10311120441c1d141036103106a29200380041c100400600d1302d452100f07008140c0b0003c010030400007994007c0c01c0c01c1602c03c1100c0161041c513050082d80904a030401d0b4030007050751040c0049032000e8a040e4100c5006808031000003401c3ca4200501c00b0fa950100030700c01054291790310f101c0380a0500810140b020307880b80000303e80e034081d2a49010305070f404c103a200301100000c2c8403111030700759800803518110b001c0000c402880a646001c41c00c68506078000104c5030117000c03c20248042008000d000f8024051b9030914035a1012145002081d01c0c030010700b441da00c070b803034091200501c0d03440300c0030650001c40100400780c404040d030000072040d225983c002000c09040c9070000082040078005040007034001c84016 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 473452544 1250 473451294 473451331
    0x2030c21040b13120b1e1b090d0b0a050a060f03030f0e06040509130b06040b03061b040b1318021c050402010e1e030114010602070e07020312090a02040c0e030718091208 74
    0x6e00507a000fa20390f40822210005400d0030080b6a801804100c0d10003840c07040054010381700c8280c0c030001561219112501e401c01c00815007124091440103140c1d040310091007524680300101801005070702c600400100c910540000d6a030305081e140900402881001c00c2c3c203083d2402210a00d1018003182d66084400c001540340c41c01303104441c000c40002d4094007259841c3c4241c954400c03083d2540d0020507205020104201d800d02010303000c01503c04802c00401e60411529035002030720402c654041070700400c4034181d8240b42c0c0d003804000640302c15003c58903440b00c4c80141c5503104005142c0343c110419118440140c0e04880000c100001c0c15002081030344072801c075403001c0751424001d1202583c817050381001540c0c42c0c0c811707440e482646441942d0800300c03150342851101c0380a4030051001c1e444100c04900750f24041c8503551900000c4c0c1080c2c032411403400301203516100944034800c443d87c51170040342000c0c0c0d0076400c403c00d1160300c5040700d1181259000d0140130743d907041d581440c80701c1c1c180343c11 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 473453794 1250 473452544 473452591
    0x50702070b1b010608060708071106060d03120b040f2c0606010c060207061a012714011103030f07081302030c091801050702030c21040b13120b 63
    0x1006031804828680d20700141840c402d0751550282002000d659614440020890000e000040c01030089070741d510214180344000604151410380703811041e4000c4428003500303aa4130b141c5c0744015581810300503c200c036445021402085d14500f85c50b086402e1000b4051156210f030300000381518010180341201a986000f441e5170074034040740c03900b51b902407000304000f0360280c030b40481d80c0e51041c007016180c85501c0c0e4a200070b81e000540c3d108022500c0d42440205580c0261520500c4200101c400c9450070055032040488200c51180707400305aa041c3d031a680d664030840700c032321200070b40c282100e80d60b060041281611240071a103003030000f08144082000308108c8520f420001780c009004000c0941860100300010070041e010f420b18030004800140000c00c280283c5105154a4000d0760b100c5081d40c8101b8280142144450f20380030f19032a4880394044088103580a40310040360464484101c90024409849242c02c0000f14010502d041c10030808501a00e034480c0141d00c40d4038034138420382d120 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 473455044 1250 473453794 473453803
    0x2011508010908250606090b09180c01031a040e030316110d08070c1a040204050a060f1e0b040902070606090e15040203191112070f0b070c180b0301050702 68
    0x1d0051040d441000380000341d0200d071310f01c0e040c0d040301104031203140d801903a1000210381041c0c1c010091280c51306c0c0e034800a850400300e0654002c000382501603082d10079001c000d80b164210481c042c141b5a8442013800180750f0940c42d802d80300e401a004110806030440450783d2508210340d0410800c210006024110b8400d03644c90703400c0b680d684010312644c090075a0a41c1e0303012004003200100700c03071028100c011400c0c2000c61035261500b44a400307800d04083c014003080c0d410040c40c84524070f040a10030800031180000b048122609003040740600301c4041e0560511281c240e0200000b0390000c100801c0d407090590007000c1f03035031140c80e041040d5592922a1829620980402d01070b83c0c00c482c005240608040b01300607402440201641c03216901c0440c40d044180c80c1c507005484050a011507454182082001c03103102c0e601d50700003002ea26180c03040c0c940300303000c05014030303541400f01003a03050420aa00c0d00420180889090074038022854001f43e0009001d0921310f584203608000205001900108 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 473456294 1250 473455044 473455061
    0x512070203070e0c090d03050307020601050f060f1c060f0e06090408030610091a070615030809100201020d18060f060b090d080409180209070201050f0403120b0a060201150801 77
    0x5002d0318001e40b8048865044000080c0410300c022070400200015986d21005a40da03103120b03460b1030341c8034103005100034a081d0058000901071300300301907c40941d9480c0e10030340d541c10071502c5105e581c4501580c907508491030300c400e070015402d081501c0403070070400c00321880e000d840904080d4440f6540703460800030b8100e400d64000e070101c80b007000450104e003000051440041d1507800d00f9011560f662a001c904059998401304c043c4401091502c02c211582c0103c51151540300c0f0700c0c629a0741152035804880c4030700014240b04928005140d40c10714000e405036078440482c400d013049240140141655158850030084802e1440c041026120000e18440c00b4140c07920340300078a051542450038401c420215540c1668010000e00000039120750501031808682d010700c2510350f6980442c0305110302403602500714030559041404101228100c2c41c40703ea40300790140f502c40142e200d4440b00c0401020034107140340c0c010700c80c1c05001c234980b40c05402640c43e048100036204101c0d680c1750002030880d802c00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 473457544 1250 473456294 473456299
    0x1080f0c090108060d021003050106020118080a030b0a0801020d05070e010f0801150207080303091b0904050c040f090b1e0a0e2a0a0303030c090b070308281805120702 73
    0xd110800075540f0540e00035a0102d4094100c10110007107030006101d0b40701c8001990006a21000140f2105a0a000780250315142ea45022481d9041d40e4410781d00e4010300e02a481055500c5070f606c940ca43d40c16400000074200503008542d5540211036a1029000445000c80865000c01344e1445c254881c500c4030400010507640c003040350b420100f02c0651804001082021403181c1100410303400c405100541c05100c0b807100070400381200c41d24402900f0b01c0c178030955119458150400000c924081440c64042d0780448001030000340c500c0020000300309000d4080c203003090319400c11001482180d41e0794100300c0807a40d074080130380d64030800006541e0401003a41c0d9681240000d85240461100b00f0070124003130001400840038000c02250b03160007680d0068000a803201300c070302252a003012004000e00540c900c081d213841c003561401307440c80c4006001c101844544035030f10710113403041d000d0007210214401001c2c8200c0844440b000012161050141c540f4005e205504c01a2070024040780e0005078003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 473458794 1250 473457544 473457547
    0x70501091512151d06090f070f03140a0c08060915060702040f050903121005100e01030906020d060e0112030804120201060f0e0f09210a0504090603050106030201080f0c 74
    0xa94004680400304003011600454581c04881a8050a9030140003e00031400c0800c44450200304d5502040da4003030040c4d40107001c40300170300034030080b03030301c40c0a80c02603ca00b0240c0b200c0c400c03c0411401001103d0801c0c4240c0c01c03131000d12401c149a600721180750304140d40ccc1c20446440b0070007008000c103400d4408080f2070301c19a009140a0614802404450340020030003d5915131441503201510800c5032007031070f20703007001070f1102404800302031840e0050044080803040394204004199008103c4000805001d1400c241c024160301ca90440205c159001105545a01c2200c9003500603000c0b03406501c410140540000c541ca115208440e904103030959104201e5440e107840311810326000c51302650855486800c080b50068201070010001c0030f080c01c3e02006450800403c01003000041c2510301c413034200c00802201c00540c480c880b61103c7e0582c80007030356107250030400da49a101e564001341403241401800000c0c860706620200c1264005c0c9c0782c500030381c2d0390900582c10703001080380e514211000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 473460044 1250 473458794 473458829
    0xa05060a051f110a030c02100c11210d080118110f0903120414040b0f130f020c0f030a02150c0301031203020903150612031c020306030304031403070507050109 70
    0x684002c00d4000350078401141024004024144500c0c49000e5000c6400c2180760401c505050740c120310380303c6481c9000c0a610700b00ea0750300310b990403884040500c107212641e40d00070221071022003250b550010100300d0721a0000114060485802481030306c403842d903042c00300142e40300c0e20f000d0343c6141d00a0000c0c9034a040d40c000e18088181c0c01030602e182d0144180c40401703102285080c000c002a15280380b031841c0340b100c607400b080203803030310782c01001c0c050268003020000d2074461100c3e14010084d04000480c000c0010300b400070003400342c0f5100074603500c160f80700082034010100041c054411994255030f0140d04207031034942c0080058400b6515004200010404a42d00b150200c0f04503102d864017501d0b10326590006440c001808040b400c2002d0701000340001407501d403010711820035000c0095410880c07100c0c059052a81c210014011940e000800100c555405108840155902080c450355403000b910b40c0036a81d401280b01251280b043c0800840e0700d600034280b180440b510465554032246 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 473461294 1250 473460044 473460079
    0x50705060a050405100c062702040b2413060905090703020901031407050c071505090409050a122102090a140102011e230705043303050a05060a05 64
    0x1c0c800e214500400100380f001149540e07508202016810340e56a4011100b00b0b64100307901160f80f210800c05c4480420400000402c558112a00701d4640441c1c00060081d86240442c508401403c8000c280340e030400400d01c941d541c5540a0180402c221907a840c0c02925640d0507912600749000e07182d88a480390001a2071b083c030980040042e0003040c50f010072054072500d000100c0080c10344a03000419404500c0200c242d00801802d0010010300d0400c4400e40c9000c0f4000d00103101c1c0d070703c18034001c54440030701c0414840c08200304c00c100f0380d100d40c8083c9041c0c4841c000501c00d0401d60440780d001c840340390500065111b18000d844100700010100703030f130780c1e440d18003c1d441c0e140b0241661b82c155529041e514500710018a81d0300c511004001002c12201c40704400b5403c052039110301c9540e20f030154414000b0b0540e11006681c103441c0c100c400210f8190550203448050301040803203003e03103a05510943e00c0c555140d0000c6002e4880c01c0828406600d40c0010000d0f8007009020312600f0034050491200d409 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 473462544 1250 473461294 473461297
    0xe030403020a05060d0e06010f03060c090b040b0702041e09031b120c1a0c1b0316080a0909150510080402012f0a05060411060f0403030507032a0b060d05070506 70
    0x150382ca03180010701b18000c500c42402c0080980c46034a0050315440100240134181c050b10134505902e1501c9031141e410104510418066800b0f17181851902180003411911240e0014022000800c0b1007003103c0854052040640110901140028548144509248100342d42c1218103540001c41c504102d03c0020121240f280c00c4805444003010040c040120b501420b8107035014002d8501801e40d60484003c940c0911080c80034400f03401d91080140400e441c8040c1030520f2450391040040355600f4002004440d8112150403099140d4a03103070110410403948004170040300c07810368182c00c101c1680d800a0300c8041040354060b01064a1f0403c511107441c2081c01041100141540c400750203104031041403a202c1010402c4880340e1041051000b40140d012081d42185401c17030f0141d00c1c09128103c0c591581c021844002c0500c0408a8145d0416008020103020000900c83e000e400741409000c160b030710344a551040e6a0224540d0115080d030500122600e00c03036070450000c2c0280740c030380000d00469 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 473463794 1250 473462544 473462557
    0xe03042405071203060e04050c01030507050f0316050705160906060f0f030f18050f060c0304030f050a050403081204140d02191401110c07061d01030b0111030c010f0e030403020a0506 80
    0x1015507800c07006c20b10301c2501c410a030142d070060005048009210002508841c1c000d40354006012091184540d00345200080b43d030b2101c0040315413030b0010f945250039100b0b0b000e134490003400d80c05482c00c9940b0350704542410600302c6410144c00e200c8a903842c44160344c0540440b83c08400144113803000c0c0c0d8003900a4000300e030108209540001c90180c4039400d6511301911100441382500540150504070104005484d006014407031028a94101540c010307002082c140fa009050010100e0241c003100d0085050390b0003540c00000559941c041c00440c040c2d0712104640865803040d070b0701d14800d5500c000140040b620704d00307500200450307060354200c0c4082d515103d500726032501041c00000200700081c0134004801e012502041e4035940700c401c09500b0241d030758100700304011000c1e409483d80c5000c68141d01002c1000e080000d0034070080001207d00c008000866034440c480058080702c90441507000160740d10b22020100a200c1c2c8240425480f4440d602c03010303600c690300785400e00641c540a4010000e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 473465044 1250 473463794 473463797
    0x40b0c070f121e2102070f060c0314120c0d0c0c242306010f0509090a180507062601050a03240507181203080a0c0207090e030424050712 60
    0x40480309680d42203007454005213510601e6110071544940f00e81c042140720042d00045e078041450a042000c003d240d550540d6020b42005400ca00c80820480c0c40c4d802c8802c5d04c400c2a4011080386000c80c804001030303004200c60804240340504c03a0542e03e102e401c0007003c0b0382e40241e015150100380c014402140e809100390307d4a183e0794840410000b18901c4c80e409102c0100381c2450042d00e0f040001411000a03c0b40140501c20100100003ca43d039000030580e200000306e60000702c10500c1c4120b6042015041e000600074440c500b40414081c2c7c02401c24211035a110f440380000b0342104540c5500e684080c4101a004101c03280140700045c010710034480903d0302520800f041c5200c403500c000c180c460507241d010100320031100b400d0005881032083d90281c07020191040392204281c0d0003c0400d031005009000d02581c030808401494030a003e8140241807008051159840001101340c1701e074024811404100c0c90260324003140a14058801201d8a45032100c608100ac2a1507652000b2405031000c0d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 473466294 1250 473465044 473465093
    0x9070f170601030201120b19090506150a23031e070201150b030405010902061615020304050c01030b030705100306170a0302030f0919080a061406030c0d08070503040b0c070f12 77
    0x11035030b0b1102c6880402c49102050238110980ca8545880c084540c0034001134041da901c0d41001026a49040803100d59041d10710700a0408040d207440201d1440300114103400403a0300109000500140020309810907220140d00741e6a03032030b240002d900326a0240c80b4002c14120341c1030100005840c4a010f1540f00c0d004400214032076455900050321a80b29119064403248048440024480500350a864080941504502c1c2d4240ba4961999442003e2452810152612060130f5039031018801c0100402000d4404200400d4005c805009403002d8040e807044001d4955040c0034900b0001b40414009415801035403502030510403110283c3d10800d541e54014903150b229034801100f0340d10036001030000c20041c0c03002540618002d03003510000b03500d48a01c10640e40500000359030100340c0c0b8490490842e031842d0310b13140916080d204e40c002d03181c01521602002c100000c0c04480c000c024194207640d00e080d1454941c40707101034030f00041d541c000c40201162003800080041c0b240b17940c1c0c1d50007590111742d01c03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 473467544 1250 473466294 473466311
    0x9150b0f130f0203041a010605040e0105060c070302100c0201080f01030317070302091e1c02031923070303021002040803090d080706090813080714040c050c0609070f17060103020112 80
    0x584c3c0c401e44003102c0c4059009102c490304c90070818039a000d485503160080c5440d1802e0030220282d0418000d05205040000c0c1910b4a25020031010008641c00b8110030b070132140c10180a010381e03007000ca00741c1c041059900082c5c600d04080d16800d040c0d0746c1c11346603c045211191100f02c5240030003422081415802c00090b001c607940c0600c01000fa4804450b180b5007840c0e07140502251040d20a941c421405100124100581d004200c28440040d0941c583c1c86001c02070030411280d0908045400b51001d1030001c811750264040343e1581943d009400f00c400c00a051100d5104a110b5481101a59002409018058641800f180036000d01400f103031030400d8030544a0700110792414804580c00080010010034054042c2c82d10001802181c0203001c1c0c4600d40703400e1504100b504403d2502c1036944806080c1400d006000365000c4020000c00c942c00d614003110300079503e04850050201e00e40b03600300002415200c9040c0202c403171100381c015146903407a580c010344910403c45038105041d40c5031800ca = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 473468794 1250 473467544 473467571
    0x907060e1804021801080703032c040b030705041b0813030807030b36060a0501091e03080301060503090105060409030c12021c020102130911070312090c0909150b0f13 73
    0x1245c082c09500703000e0031700c6510f5481c010b0800e01d1000c5c0c4500907034042c202007005d825155000003150310010703170300031076450a45c030700003410b000f0300360005548140f03040308002891450b040c10050310f5a190321a14415215000c0703080e0000743c03c90380140000c00010000e41094400d40000c040d8407009004401c42035818a1002c0b00e102803402180b511042030224441c5030031880d4605500700301d05a402c208601d0901000a011510318000c460380640c08036050042030806641100007183c0103031aa0b500d9503140e04000f000d80e8025100d80c0c16540c20000031450070b260610910301420b5040e141c41e107003684a5914840c8444192803400c095015103200209400410000c001041006030300040e607a403403c1d116028070791b203241c00c07000d51146404e00000c540c00400080f2618240c060800138183c42401c4041c2c4064a00c80344003c0000810200c0040c2c40c442d04e070001c80246224a2591404000d91000e03d021140c40d0b0340f5107170b403083c200e042c01c509030f0800c1500d03842111801d00740450300b100c59511 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 473470044 1250 473468794 473468839
    0xf0417040504110a0807090b0414060f07080c460606080109170a140c010618060303030e0d0f0c050307023003041a0a020f150907060e180402 62
    0x9070643c0d40e6100140300c1900c0c1c0d034010310455204260f401c0c800c50490034800c0304000c9001c3c1d80910310554043c10703107801580d560f00c0b01b5120b000c004400090340d106054a8402002e811084030500c880c8105400c20194010721070700310b254075036048031709400002420300700560440e06140454804819a030030390b020440a010300d030050401040085800000f41c40d103003040880001b500030780745106002c2c072980305510441500030b01000c01d903005c1e02c1d038000804160041c9401d40c81001900c0d0a070704080d42c0240d00e5002001100d0094504001c18503d03c2c070a662034003201ca0810740003c0c00e00209045d42030051112100b158040c030126807c100056020540c000615007000000c00c3c0707101e584c402140c0380a2200d190320038012018505041c90300003805c8100244050080c40d0641c01f01e102031440d4820090341c0c69102c600c1013100c4d14621003e08003c4401c2040c0c956411134000e42801044e4240206030782c6c000510090154103650100703924070296010058012680550003400c480351351a03210780d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 473471294 1250 473470044 473470061
    0xe0d0f080903071220060f0a020705101b08031905130b060109062a0605070e01120204050105030f0c04050a1502061302030a0b04170c031207080f0417040504 69
    0x2030600c0d540314180c0c030800d4907024060780507403540220031451900044210340c2c042c4207142000c142803501c46035100040d01c01c0c0241128461060000f14a00f0072882c0e00140e00f0f4100c0c2c10907914401c0003115290200d440f007040f41407216500c41d00e540f942d00014440700003590b0000c65030244900c44c00d16400e4100075035109070b8424015002c00e400440c280814503101d950806401d007820200b0038541800504440c0404400b0101400000c00d800c02000103115500c8001d139005204101d0740c6001100600740b000c0e5140310500190f480043c50110802a03c01c0f60143d51050b152a81141d503a02d02035180ca0000400d80d00454205210014840e10703202401c801400b00074841c5140075140e520000d151100c000c10700405207101d00c0e0000c004d40c5000c10000642c54005803190115070f01c508006813085248501e089407207400045110031140c000c00544082002036010190300d0311540e00880d1020000c0c0c0d00f0303080c2e410101300072900048440310748180f0580e41c0c05951741401e65410000302240c0000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 473472544 1250 473471294 473471303
    0xc03041403010507051303030302090301020d090f1a0c0f03040807080c070303030e010507051602030708070b04030209160509190906060801050418050c120a1509030809010e0309010e0d0f 82
    0x92815800c245802e014050f40900c00b80343c02801c00d01c1e03181c80070f00042000c1c0700240915500080e03005a81e1401e4040b10b0f0540017928040c45810340b1450300d000c07001d003050001d0301c40030030f030440c075005c0e452490792901c8c040c0703282a40316828614156108006a8005401240c41e060304000c44000a0f1090016046900308d10020b042101e01d50704002d401d54071140f200e007140d41d1602d410007010782d0304034080c0d40895842c80c0401400c130480b840820324000d90b0340c2103003070184528080025000341140080051b64400e480b40b05044d1035032800800d08003105240c04e00031450601c44241d01e0706020355501c04150f5054003465000d6550340c03041040303900982103080020780900062045d030400d40102181900c001c1c00c407103142c00c066143c00707484084030300100348510014125504420340402400d840540c02c0a404c00030300e1503100d003840c010101040f048000c07e48040004500140602c10780348080052030245250040120045500160003424aa4051181520800810a030f0301001c28a180309 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 473473794 1250 473472544 473472569
    0x92416110105152b030e130501090501060e06030f060108042a03290414071710061d0a0f1d0a02011e09030b090703050312060f010e031f020c0304 64
    0x107011342c0d41a542c07695501513102503808140a190b03c50241d0005405103070001007240c021000035a124001c000704008141040d0001c03540040980c0018125982c0340c440c1590b0301540c0044c004507020880d01640030001101c0002d940d54018000154828418400000714a6182d02900340ba228442468403402d00b40003420b004210000040403200404191003920803196409802103918006200078045608804196004201000000c0241c40048449480b145008081703558652540c9040c0300388a0402c00c000034a03050050660450701f0349100c2000e02da90720000c4940c040c04c488020003034023984e14880000700360b00070366000003041c040d10041e19211160740001482d00004030101700c03160610b0222043c82603000f029090449610814054059071507030180703810111a0390010703110b80400151480500350080d102403151408840205900a10500440d004203e203801540c1640c403013403c41400380484110050020030f0081d01500d04000140b0b101d0075034200b9405600007211 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 473475044 1250 473473794 473473831
    0x109090201081003110d060b1e04050a0b01090e0402030a12080610020615011b050a1a01081515040608070b13080c0f01050717070b092416110105 64
    0x9201c1c44143d040642c44450880e80390541c0c9a252021142000c40d0744141d228a10000401840d5004a021034100422000d03a50695440e0030480101c08410644100c0c034050000e5440e010601c11914900e90681d0f501c01d100d410000c500100701009042070b0303414072400c1004400508c004070b145d020032900e9585e069a82c2081c809100382c0da04410403d100755002201000640401d040440a94140034071b800860710a43c03070068241404c1002d0050024000c62005c0000d10807108241005c1004c15041090107a07038400e1060384807003d00a941504000040120340110240107400b094550010000912140c0d94115149403510651001002d0300001c80c0301c0da01141d81d00c203a05d00410000c0e020705064110500003c41c15626124201e06210000c500d0b030050046081051481d8103102c1031090f0395010904112014a03000c0700c3c0e458051041800304000c10380c04107070300703810041032055a901a44035441c042d6102d10031a60b0701404c1000035030640700c024609000d040d00520f0300080003646c581 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 473476294 1250 473475044 473475047
    0x8100f0914090a021f09080312092406061c05040303150905060901060804150905010f0c180311012706020d02030c030406030213151110151511060109090201 69
    0x60001c05410b40d82d0412040100035840340c2030310b22a000d016844484070350400803001d0f142c0060b06d41000f6038074400400d42e01c00f410396483c5464042e020b0b04049070740e40c82080008060600300040c1c819003a24200000c142181008806041c0035840c508030010349045808664046900860301900001e1321079500c19041021154101c015068000082c4040d00e013800c040345119406110f00403c1044100c00a400e10416484141c82020301c003406101c041c6040c1400f03070180c21400c1d030038204185030091403e00180075044c07503404800102e00758072410f03166071110303c400c2c18550402410710104070100e01d4510b850541e44400c48201400d01072003107040c40300007440d00b03030b485003007105640c03040024844200001007501c0845041d0310300540d6480c6203012045000d62641c2c80100c002c1528040e815106420190410503407001d8030842d901051040310792816900c1d0f845c8181503080c004070080c0995034072211840e80b1041c4030300f0315035548000700882514100003607004064150340d5405400031907 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 473477544 1250 473476294 473476331
    0x3060e091e010207020306060d03051e040306060609210302160608040c060305090312060a03080706140708060604090e0703170a020114061815061b060a090507030308100f09 76
    0x81c0104402103003803201d503502282e603408000d4400f602c0745d001310440604051007a4115100b50900708e25407c455039800c0d044103100d80003400200e80d001d0916001041180c0302c1c1c80303080111040455040d8007075410590b038050034142020300303070110b0080c896202c1908034240100340060406a8404602d40b510b810120103e020540000e070406007094140882e0b02e4001043d9150135200e500810140c0c0c071031a00042c40c840c2c90341d00040108402041c1c4c5d03401e011207035112009001e881c0708802c0c0f2503a103940044644823000c40e04264010070501080c011800e00ea44895101c00701d0400711a8400e03226103030120644a195000004000d0010781c5145080c2d0a000d00c0058501250700220b8504195001540d11052915402031a0b0154070009504610100c0b0400d0408000f602c050f0b51080d40c200131652409200420b50401c0c410700010580001003481192407898102d00500411429951b041b901000050000807100415060104244681420a6004200001c00002c070b02d518400c1400c0310 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 473478794 1250 473477544 473477593
    0x30f0102070809120f07061d01030501061e140c010603150504020f100c06050f060301150e220c080307061103100311040e0303010801150506070804090c03060e09 71
    0x59006201c0d5200168810303040d01d07000314048902c083c000c0041c08401d442d000388110380c6006403250380e0300024100d422502c001d1800c0c442c1c11080a08440071001501901e0f020702c14040011907007501c210b03141016107542c0c42a0700280c80d1050070711440c4d0003041210b4024820640c4a40d42d520130400030071a003400041421082d103035003401145802d40014803410000c00035140038414082c0c00d600301c84c0c441d88840544591080c1e04001601700300004010034501101c0f41402507117490542180060001212401c94914031411041980c0e0205080d88040303c504418100c241842061000100d170500030101403c0d800c001591100c00c0e604000f0127481c24251907010104080060200c3c0100d800c001e50203480d089080314540c003c071100800c006281c0c0301c4040e00d1500010001040d2080190022082c00300d500010141c2e0548030000c010440c031600c00003e106800807c420400c002440c0c201644460560030002500d50341c03080f04030800c06084840310398542140860801c0c20b800d0001c10340c0d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 473480044 1250 473478794 473478823
    0x3050603032206111c0c0201030b030a030e120a08090d03170405060403090f030210230f0304060b03150f0606040f0305030a02060106140915071e1101170f04210c0203 73
    0x104540b1107086401e154400d20301d0380e1701300210a601242964000c0c1c110310441100a012904584903a0034028102012002814403421100b07240c00d007544000140d0030a05604501d0b054076000d800d2040084c01600d00004070700b03210078020b400950030100f0070154400d600070009403e03940392500d8000d200420030b07080100da05600784030a00268403124140c060000036814010100e071508d00507007485000021150501d01e100140074001745403400051400345105032000d204014100003090b845001205010300203100c4140068041d100d10022581c01c04c078041c042c00d1800761508140c0004100940080d01c83d6400020500a090740c1000700b24014481407400c06809040070880d00103a101d442c03407242c81151034503081807404504c80102c56400703900208494085074450510303044290510400d072405010b284000d4140d500840d21040160021181c0f203172140e03104c000c80012500c0c040c03c16a503140c0364400000341c030072520b21040025400e0b925052016035541c4101840c002d9611341408 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 473481294 1250 473480044 473480053
    0x6010e090c0117010b030a0b040c020a0302010b0402040e131401110406180b0a030c0504090e06010f060c0807060f0b03010c0216050402122e0306020d0b120703030305060303220611 79
    0x5101c0300f0481040d06440c40d8500d0300e944d81d1104481703030002c1c11400034215480340c03602d400e020250f500003903000403642c801c0e0000e00c4030703492500420040340900d105035040e83d03980b0f000207408004009012603001d8800c0c00220b405e2442c1040301ea08488184040c448140b01c0002c040c0622608800503280d03071250303d61101c02650804003042202e02400b00c0300001c1c1901c4901581000707000da02a5009045202020021548200c04140c0d5134403080c0310b51000c0013a50351011421034802d42c124900e064000744010b1078501d80356030b07103001851244081580681e40740001a96940e00303020341c0c42c024566074000c122001c00c00500030310349002a0320103449184108000040c0d003c0c3d4010090780300c07849204240b00c1c00c64001c00c800d50030310001441c40d840e010210010042007403aa000d8403203003000e80780410520121005100750510075401c054404d5000100c01c0001074480e400c4a17501c80e1001d8156170414403160b00000c40282580c0c0e01404580c00e00000b030050301d90182c00044000000c01c01007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 473482544 1250 473481294 473481317
    0xc060c07021201020712110a0b09011d030427021b0601030308150915060f12010807210b22081207030605010c110103140a1a09070e04021b06010e090c01 67
    0x11b02207a034100002c0401d0000c50f00b540d00402a06001258030660400b050203d05e02c4d05900444c001d052000c052104010800c0c03d800c80c2480020a0324291122640300c811109a28843c80b200c51085c0d01c030241c03800c4d03001c0118610b4200c03c40045162005144c004040035411490003600c2410002d110b802c0d40240d030443c401807035840c5407050350400100342010f1f010420031130102d86188a0140d0445480300c00044880955030301481c070030704840e4000160b0b558240c80da003200510300c0c1d03201128107003518905400b02c082042c090005405c9160750194046040180d5a41c1c0d0400b440030505032803032400440e1502040d01040c059030752051180ca000c1017110f0030840068180c42c4809000307040e2400c0d081465540f640a5403100c01c0b0740e9115802081503140108144000d4035490801641c0c00700b10305800d00b52800c08842103400b0324210b49520221032850410301000390801c121410035401c0c07421400b228458148016800f0701801244128036161034a005403425a49110305410801c0d101903e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 473483794 1250 473482544 473482553
    0x1a0d050601020c010516020d0b100305011a0603070f03090204111c060f0b07050102211510120e0c09040b10080303010605040306110c1c141603030905030c060c070212010207 76
    0x485206da065003001401c5107145001050050449800081c40801d5a07410701ca80c6c640c0b484540400c8a01c140024080a4100d812043d1407281d000942900070b1800d1003c00d203201d0043c5086a000500342c0b42c0010095010380008041d107a1030a000e070050319001461003d0843c45401c009030641512001f480454545071041c00700030710381d01c140080c84101180b5002000429011514644a00311189203801110711440400c01000e49141c040d2070200741c01c4c2012410a880101c18030b51503901c60001d88000c41050202800840051200c140a0144100381c46d68449103203a0045008403441350403803801ca00001d58140e031039008245241d006000411200380d01204580a407540b01c18042100c014023108242c00e8001d00c0b010300c203180241e00314401c40e10010701004400300e0f002d03aa402180044011034035450b12602c548000c1039020b002c68400420700039080025850310940850307141c82a03a17400c0320b043c8001078030f10720103101d000140d00040d032405a080007614003200e0001c600d03001403070f9503 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 473485044 1250 473483794 473483797
    0x1a0307050405071704200d03120c1101020c030c0d0212090409020a083c0a020d140d0306090b1c140715021e1501030f05071a0d050601020c0105 63
    0x9400e1007251a980016010340c071032098035008000d0070700903180c01e080c28a4006102d50b140117800070640d241c0d140842c4c45240011040c03101c550144c0340d2000c030b00240b4050b080500003580c0042c040c0400c02c03182030340d00c0d00244010080407112001864440c0c00100700e241c01d0031684940b2604551000c4541d40c00f15100900b1a560400102c8000594201c0e61011071244000f43c0d2001c01640101c2c03202a080007500d81e072407907202e80c40203805001084080c0031840c20240354503641565070f2002c41d40d48014180f070841c3e12011b80c000c6480900046d0303210750007864030381110114000a07480301030804c5008241c0c000c150028070115141065490f88250181c07106c4210000500800344106000300c01c03400c01d02c0a04094662034055900040742071101958540450000540c0c0003d020300c070300c0400c840800c2c2d001e403d10640200048913441c43c2c68400030b011000d28255150b016156000842c2003510502c07682c1111710a03420f60702d81101541c400110341700100401d05541048180e480755a078400c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 473486294 1250 473485044 473485049
    0x5010806010519061b120c06151d04051204060c0b0c0f0a121b020c0a0f1409070504360506010f03090c030204050c0c0f0a110603060102010915050702011a0307 70
    0x14008000c5c142d80c5002030110380c200c107006003214404103035030240b40354400c040502103401803005009401c001c80c0d00c0441c119042c46513280401c00e05400c5000d0f4041400c04170340042c0660100c99416090000300d000c560b00c1640f1445c040744140e84901d00700801605000e6000d00c071011614203082088482d00824480d1800050400203c0400440d50701495400346210030421241480c9414074140060350f100c80b2044000d110710b421040c00200103040342104403c2d54408901000d4170718030702c03050000008015056000344201444081841c60b1a1800d040311000002801800d034203125916100702109070400c1111070b810300d010406942d0700312400d200908411316000980d442c0d41c0c109118211420703080250f00c90305100034002104074050240411450b00f105552904090a000f80e5485030741080c014400c8002d03201540070781c41c0903400f440c0d00400600000c9098181a03440721040c04292040c2c1c0350700d5039140d007441421a824403488002520058900e0700384020580041c2c0e0b1b070701461 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 473487544 1250 473486294 473486297
    0x203010f060e1c051905010e012a030921120b0306040209070e042c1501140103150e04120809070e06090c0f0708040302010e06030103020d0f0311030d0501080601051906 74
    0x83c98480c1004002c018020000074a0700d60200000f00925109010705081200c2000540c05d04180381411441640118040c200f204d0f02d41d000500c40f10307001c1d0003500d04450207849284606202042c154206030500348208655620203404c880c4030f94480c03044820f011030040c041e9101004010068645a4201c0d40003166420404107608100c00007501816001e41c2c861010030b0310300c1c0219840500030341200c1040500170b017a02c564502c500c0592408442c01d205044006c010140000e102e94000e62107001d03810518050900d085032218403c030a800c2041c0c03002c03101651000e54901c511540018116004260300d405014094540115481d168001a10303551007401c0710004603116003490021101d18181d202c0d0344a448100c141030864043e00f02e44000d901003081c2003d40c41d520314040080743e058079402400304001d0341c296220034681d40c0e0b040000b1018003900b0004280920b4003000030b040140c0e0300b40808103466042400d0b0707505010042e80805d00410900b84000d00b00aa0810404c1c280d40c041d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 473488794 1250 473487544 473487589
    0xf060f010e12070602060f0903070b01090f091736040509010905060f0109060603111b070b16170f0304030c0c0b12010303030b101d0103090b0a0203010f060e 69
    0x4000001e290358056036690b5290b40309161001503190740110b141840f511240481890a503a1449425281d1080c80f030700138080c0c25590300610960034950b20041140b01000c500058018090303403500d81d010151080d11203403000204030401050001c0303907000c100311104000039006005041c115000c07282c40700c100c0c41c410b070344600c0011070302c040940c0410880c6822004981c883d082064150708241c80c00c1c0a65880103040500208800e07000e402807040080340d0304130311032610604281e85403800e8502442e001c3c3c40c5c0200c00d4001582e4030140c01400c4241e400d0340741031141c694a85404c0d001c2c8254002002c000b08010300c8294000320442c0d003925445901070602c1001305005142c034004405d91a00005032401d00400d480b60300b00718150406042c0c034800d44041040014010400040b512001b4002000440501c007884030b5a00303600d10304035050010b0501140040c810399a040a400d0125410004c090713000c8010803586a80007036450090002d41404020307842480d001c100c142a4009060f0f45d0140e1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 473490044 1250 473488794 473488817
    0x41a0114161505060102060a02032401020f010509100b03011b140f0c0105040308060409020d03030c14071a0105100c0210110f0a050c06040e1501020109020d0303020406080f060f01 79
    0x56090031110722030b600c0307030014450074010802040100400e90700ea03801482410f00240140f4080c1c03080703900624014000440d404d040240143c5469000f11095045001d0001031010070b000034080c02d40103610300c10242000d62207400e480f90880d091100024442d0381456030284c82c4c91000c1d441c0020760182881c03d0741284202700404142803103085050805000001642c85040c07034194440350040f440799a40e5480da844074420001510100e020207507104040c10204000280a80d010f001d0220311814500b00340e05039082070030b01c2900006420341d41d00902e0f9014504442c072501c0013a01404d01190741021071001103a0081201050102c000d018004c0003100101081c0214a03140c0895402002c031031a40303603044003a68588a148408840720321030409a06000d2400c0400d83d015159144c022254541e00c40032002024090808003a055543e141a0580541c40d4400340702c40c694040d85000da551403900c2401007084800514100202046e00b042c80b00c1c0c1d590719a0b01c05e2846000b4a4810441103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 473491294 1250 473490044 473490067
    0x20a170c090d05030909010b0f0a08060a05102001061a07050a120e0a080f0c011b0f0804031403070f0803150a09090201170907170c100905041a0114 65
    0x8540300031194014420080b1070100403000000303050701c43c0f05450b002c140e80da940610070598017446041490203141071103428091440351705a181d1010f4010590300c0c00c5a61800071440401c0d01e171b003201d00018000c1c6541c1c00f04400c2c0d224961140c0701040020407082c1d260118200c281c40a080584105e880c00040c04010300904004080340d15801401c544540d4003190350242c4000010b0200f203002e11102500051f1660000c2100c8402c5030b140b20240001c0032801d001180d880d02104403003506006528001804a00a140c0c100d0b4040e01c0740c040965100e045040003080054844c100c1071480c1d00400604000401c40941740c2c04690b84030f00500c2d16034880d1040100c8004075584410b0304925035220020301c401c00b43d0050380e103c034000e032181030103400c0c0d502029080b848101d90407070099100711802c003c0e006d843c0d81c0c000c446201301001e952001c400038000600007101c2c221000c0c005003074190248900d24052140480c1c1c41c42902c8103d4800d0100d80010786050103880d98400c03034680110301000b501 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 473492544 1250 473491294 473491297
    0xb0c121609030f03111608010c170105010507020d0501050a0504021e030a0b0c09090403020d0909141609170a03030b0108060325030c090c030c090e0604020901051c1b03020a170c 78
    0x1075410310b098800030703246500c6000321b5911901c5800f01300c0d030030400c07040c45540c041c0d5260800f200c03411000d0142a8244801515680e20214040340c106000a01c41d02c080750f03080c800c403402940407140203c0c103030a05004001124503002008140c1c8541e030f21149800717640006070b0b07141c12a8040740941035a0b4486003240c072035015208510b5040043c2e44200b00c02c00d580414070170270300041030301d40003e22519048148115000106019041c0d04401c0214000a05041c6030030043e80c1780d403500451082d16496519800b48005041c48086e5009441210805070980202554841e081c41d0041080c07921000203035445203104e40c050b080d041602d20900c3c220200041d85406150030035200d0092030ba40b4103001008000740009840060300d0403420801c003500c102200c90440d04c0d401200500b94459400b000000c0d40804c0e0440e051010030080740100303240208541040e901d5500000034210b8100b4400109052445882e104041c070401465004a401103280c10146601104420065441300680c071490b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 473493794 1250 473492544 473492567
    0x61b11040c0c05011b0c061a062706030f04030c0219061211030c0711060702130b0307050105190e0d17030921030601030906090b0c121609030f03 64
    0x460300303101d60404519003202e11040910b00c18402040058038401043ca0480030700e06024000896115031480811819000088101261559807a100400000199080e4004000c00c9580c04070031100700301c0c03460b2003c0e4080c2c4000c42910350a203580740055281000e46070007040101481200b200c48015500e440c0700c0d42608040090503101240e440d0380c0c0290190261058040e021030030103800181505000059034000c2583d0300c603c40c184141d1b669580c1c7d03160382801225070052014040031000d40e80320201e10700140e00c40c0a0024070500f00c2c0f014141812a039801c03d9052000410054040503103450b4090200f1840740f800207003480d10303580019814245007801901002c2a010f64000c11400c0390000c5000e4540c1e502141d0f507401c241c81e11100c40c050020300c810602074003400000c0c09540681c1200e1015071140070b0000724a9034a584010755503505681d8000904000301e24040313134400265245400c2590314585490600440c24000d2000350356010050990590300c868801301406450b0701c0e000b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 473495044 1250 473493794 473493799
    0x3080c0703050d1710050f01080c0c01110405030c0108060901170a14010228200c03070e01090c0c0c0303050a050d02120f0f1603050601092319061b11 66
    0x318900141c1c0c01032a500f03402d90440c1132000c5a401040b040303202e11480d28102d42000c1c0c003441d90403221174015078070064000c04004107501c1c100700179804e800003841034400c01d0b00d000e003003144c480f400c0009041c84d2191300d0412505020b044002d10045a940c058014110760019802c003c2c0c00000c035080908001165400410882507045513601443c4190094908401d11084c6894000c0700c280464080e501c100c448000070a2002d01014042d030410072403513110341e2400c0101c5d4809542c0c03c002c01e03c3c22110f43c0c410401c80c16064018852100c640c003403d42200c40c6031406e0030f050b14103034a4005141e0090703c03000741400f8002a80c034240030b010b041500c020f1400c40c242103480341c2c1040280d004200e07080740d004c0086102c4c3c500044001900c5203115008521094924481514000307041d001030501401180c180088a0f00c0040c0e49101034401c6000503810ba148044015292400d006211855041e5208100440032003407082a92144040a4412400c03051140d901e82500f010140d51007015440c81c1c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 473496294 1250 473495044 473495053
    0x60c0f030f1207090b0d150b0714010e280c05090a0507080604020c0c10090906060504091505031f090209040f03020c010908150c1b061b03010b030103080c070305 71
    0x1000007101006414110894029408941e40384030040701c0d42c0200e40102e542e2240144421a5031180781c5d0b10400c41e1040b40070350b81300360a44410655403190401d4004403a1101c991989030346440e000c2c007400c002c0b4400100206601c40204c110b4003a82c0d5606200307d040d41803e5040c410901140f914208000c000161600b01e41c0d040c21500c1c9030207000121440c46c00314030103c02003036490400d031081300d46459035040a04160000d074020010f0141e011500c60041040c6113002040112191081100801568441d1070b030740c030300c1e001c10794041d25082e40c41c4650482040030208603d4401141c140180c0303412100a40d29100704210990050011036000b03500174842d1010801000300d41807610b5103843c0a6000c0315082c0b40d0050044482c03084a00810059401021048505900b00c111050700000004141420450b0811001e040020080501a075591040701800a032407400c072400240190741c0c203822403843d8100134901e042d52106210041c89810001100052083c0500200340516442000d58 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 473497544 1250 473496294 473496307
    0xd1a060c0f06160909090609120c031701060816141201050414010f0b0702011b03020105042604120813031101030f0207020307140a0f15081501020c060c0f03 69
    0x381e81d900207600728200324410300c004107000f0085034007040e81ca041c9640c0c44020701801c201821014104c0c000040342e0507070301c0d4071000c00006c0d062944140c003825280d40d900d00016550500500d07001420403180e0b0020944001444100c3e4001c684c02c2d4000b1340801c000341451003441c01110858410403040800344400701c5c10000046c00c01c0000d078100c0e102141c00f030152581c2d00207861503450081c4110040c141c180081001070034400700241c0740d1140141800c480d41030410340b03000d084a0040401b1070050f5520020042004190175100e13010100103100c034007416172040100203403803145014503180134241e00c0144c07040121420807240400c2454220044240d5a0725092001d80080d6040034080390601e50020101c0c0190b10035250080e03001401404510320b000c914410060142e4009600911a410080307007040401c5e288000800e00c81003540800400c1c02e0000741400c0b00070745900400092059150041c3c0e80c009480b042e1a03004460f00f6680300f11400b0030382d103821400d91048055002c0496403 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 473498794 1250 473497544 473497567
    0x3603062e0b1206190b0706050c162406081005010b031006080c0f0703090f05030a050606040518190201030c030506010c0b0c040f080f010b12030406081515070c0e010b0d1a06 76
    0x1522071b00e4410303001403000f42c9400d007480032140034100b020790589002200403c0445c0042082c031560700c5010200100c0b031580300a1704400e070344d181c0e0021000c40e071100d819070f0390329800c0f4842d0350300420410f11100c2c11410585580d5402c203d451203107104100c41140406d0030b580340d22013168264034409283c1607485909203009015034960788076000101580d00000a01414041081d5480550040c05004980d50310802c20008010150008907114080c3d540e9002d129010003000304100c104e0443e0100501062000600ba2503600c0c1800003054203000601c525030b42c1014051029691041d0b03003506503510001030074464015035000d610010707001800000c030181c020441e2085c1e01c030f170302d4000e010b2007040f8000d0029038480c400490240e688200802c05c40c06114000f0180c02c00111040400c650030840d001400c44406c00c01c1041081d00b000546404004000e0340c5000140398891204c4c449616001c00e916041c0a88005000b096071152101568500343e00262028044020f01058591340c4950380d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 473500044 1250 473498794 473498797
    0xd0b03071206052406040303050c0c03010207050f01061202130c030902090a0e12040608010b160501020d0506040e011505041109031209030d053603062e0b1206190b 72
    0x2c02c603405810840e513018100c001c100c40c0046441000d00301da03152900c0d507035048486500c8990004118042d0341109245980c00b0b000414980b4003400c01440501320000010342140c2181e404118110704905072500161a04038409000108039400026209190703003065000d01002500258000b080700f041054401d0541d005c0b04000783d100007201c204104852600c94588514040c050110f41d00800401580c084040103105a00c0310030080d00610754103544044c26a08021558480103840f1010000b20303050600c18880808080c40003072002d003045810022040ad07a50280f1400b8689980362241c00702661403c0320800c3e0406402c503056811044415052a080780182c00e10a0003501c1109441ca44070f001030b81c05095040d0122888203c04603035010580c040500c2c5204050814006040070795000d1011602c55080074104002d25504000b58800340c00c0840081001c45880300e0381803003100c1c0700305d05032000a440000509042e40311000046c2e1420222404800e00095600e00810144449030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 473501294 1250 473500044 473500051
    0x1020717040602010e0307053a030b10051206060307030b060c06040203011104030b0f070309060c0c1101030213230a1410030603050c2b0606051f050d0b0307120605 72
    0xd008201d90944515420780b2480b03014805002a4450802e841556101c106001c508078031022900651034278a000c070305120100c030040304020a070344d0b1030140450708103c0850080300c999407400b00c0c0782c00002043c0307010b0352101411403402018007000007283c060007036020500100c8010922601c5205c011746603942e8031800c440490181d42440c49143c10314a0f080181d809803a800702c800c48243c1c0d200135180c0040f04005008800b09902d943c41d020102e0b20910900070b1429072540e541ca900e0986040c00040039601c034402c01d040600c100040c501c1c000ba10081042691400030540864013550070214000ea6105074215a101460140001e14080c11001c0c80d091182d040c0d808544984603418107400b114224840a00b0641101020644514143c0d091411059100e48400300031000074000c10b420a40c220781c1181e04c9503444c08103001d28030340b80c8002c02c51000703c4080d0b84603410741400001c0c40c074080c40c0c050303900007915160b0101c0b80380d03814040b1002400d81034440c10500501418a000681410b8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 473502544 1250 473501294 473501297
    0x1f0302090d08130504061a0a0c020d0b04020109240521070504030618020f121018020a080f073602180901051f030e030301060f17071202090102010207170406 69
    0x1000009150410380143c0d8116403c04403d1084592202c141442c2588204208d00801000044640040c1d84006e40d0729215030080200c82464501840094092019504514240f00e409040c541d0003c0b800140315020b07a2840c0361203a200c1d14000240344084020864050714106004200110254844058821240645428007004991069a50151041400c065000b0080020400040c2081002001c01c2c540d40022145c1084400c3c81c21021078000d21155007a032010421030030194030300000302e40080d0112401902007080104511580c23440300d0320402500c03c0a40c3c52345504d080842d00300c070406500e001c2c0611140f601c50481517000303505c13035540c504400b41c3c2c107000004c550815040b03850607507102070f005c1d031640803024140b09800c4410401e2a0308250b1203c3c1c0004007641d00303201460091006072580c80d08180d4034000600016142080310320303030701c0c140d004200c0916400a01e0498580780c580c3e00503a664a0a40100d02a01c203544001c0c11041900402540782c942e444001c1c01110b446 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 473503794 1250 473502544 473502577
    0x6060904420e1b060a030c050d0609020c100b090f09120c0c100507020120030c0109060f0c020a030c2d0f03080c0414060d06050306191a1f0302090d08 66
    0x450751510456034006142d4102905010142004e401b035408281800300b00e084c00c90400d0001d1100c00180c403510b03041040184d4020403904039a03501040b000058070443d140512079880d05401040d00c800c0028a0070b600b02e14404042404690103100c0b6215074400c2c80e0710315554807007a815031603441d103080d012640130701601072034051001e10079420748995590503510012424046004000c040858410010f42d90204100c2a59410000d114500416110720808100010700e540f81c0402c440740200d200e400d40d080346c450380c0700081d4000c0000d042c45d98030030f881c00b01c00d06401c110b42040000c0005891031900d4100b100500744602c0780e290b032910702d12a035501b074170030307a11035001c03910500403442294038400c950b880900d007600d0700c207003d804040d800810025a0329640e1000900d0194199180405030510750310400e8600f206004800501c1495550004004004000f10b8a040c81004660003d83d0380c0b81e035000b41840c800c1c0c049408042005000b100050200e00f4500110fa1100c08500c110705207 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 473505044 1250 473503794 473503813
    0x1c0b010e06120609060a080d030f0b0d0510050a061203020606121603020409082a0c06120402040510031209060215010b0703080c040e01030602070506060904420e 71
    0x3041c504440c1c07150384600000105032900e81c2030201c0c800e00034000c03e80c03240030074901181151042144840c610f05950300440c030080e00e66410004c841110f40081e015960681620012800000e102c0043c984240c0c1d0002e1240e0b034140030203008204580041c2103a5401d084168240b5a0000b421401510210340c00700040c0c0c2c242c0c00d8603903584140c8481042420081d82c01b04007501c1e25074488081e85019804003803808601d1035800181080d0347c030503a14004108440d03590060410401400c0c090025100246440310107030300e4a03000140100000d115a454000240941300200803400c011588020700c8091103021403006044408180210340c0188101217141c0382151214051504807000c5446140c6000c1c59610120b4523041c0003049009914420032002449800d01251a4001d5008040058a82500745082ca0404070050100c47c420001442071001041e42c3c56016842ca00c5c000c0b841a1308070346104000c003200c4010781000d6040311401030b00ca81c40355007180c002d6090300221006079800b03c0ca = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 473506294 1250 473505044 473505049
    0x30f101a072a0b0c070f060507030906031404020402092106151804020d2414090604031205090705031605010201050f010f030305180409050f0c0604120b0a021c0b010e 73
    0x41d4961095003019465110800030300000c500246070b0513a00c08203483c0c1264842030881109a5154401c80002d4000200c01e424568801d00030302c0075000d00d240c207000e00b00301007034840d00110703010740064807840e0700162001866036500058a050301012058a001c0344204a00715106ca8003141c81d910b000310480403a0900e442c0000484c689490108464260f603266902800040801c4403001c680e030b0300c509140d003142c0d0460070144030214280b541000c105e0724078040d080c00054001415400d00d40e403150092000003508190f049501181040d000102c950b40c0020161500307006c1c0d445140c050103141035010481c1310f047c0410003607030020b0b0001e2265843c1d900204203030003400d02c0741c444003500c180710500000348035a005003100b035003500355861103006c4d00c00000d048450a0740c048440340d01402c142e4294000510403603102c0b00c4101c0e52a42014070f0f001c5642030342458044010800b14503200052101c801a60644100002c02ca800d40ca0300c400004240b0002d0240601c4e09003c150001d13201001c91 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 473507544 1250 473506294 473506343
    0xf21040e041a0c090306180102070b1006120b01201f05160c03080a02070302150c190f020a020108040503040b0f0a0237050a0204050a0b04050c0906030f101a07 70
    0x1141c0035000742110ba07036111070414058042c7e022444155001c010401c04a04142c0c21540101499441107034107500d414406891032400c4a0200c10107410546090758a80e0019400c045981181181600c3e91119802450400a8284900e00c02c1001242d800308031504a5000358854064081111880340d02c54200350303001444c0d101c000380004d40c142c0c0000c0e500a4240c002d00f000b43c0c0300703004403120580c8500308481018000c4078800c3e0780400c08111b64000541480d40d280d00780e0054100043e140031118002511210f0be0900a410b0146980203e01000003c008803402403d015583c2c0d074580700c0c0a5031110403544000c29290043c401c10305402d4281090038030700c40a251084200c041c2c0c5004030b5200c80c0390150ba600040d5000d0081040c1c800150301d0702d00030a48035070246000059500c0000c41004200c40340604101001e0380c0902070a010f03034507042c2c11650450701c468081000f03903595020f0044020b105410840e40c6000301076501da8245040f0000d0a001ea00c22401208003040c0e00030070f403011 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 473508794 1250 473507544 473507557
    0xa02130204080a0f1e0308041e0213020a051c02120903090a050906040e0105070908070b03041208131502070b0f15010302090f041803110f21040e041a0c 67
    0x54014050b03801c0050300141c0040d00313241c410b046a24244035020442c441e0040111410750204c1c0411007000200094021002041c111480354810064101c3c2c0101d2054901440c00c0c0c3c003c654000340400240d4010000d6600010341281d01c2e802151a0004400103034000051440c2ca8040e4480465654503007c4140c844100000d002c40e8006880c2400b00540400d0103080a1f80080d550074441402040a0040c03602c04c401949800100314038001c0e03018074081082d80245500d4009005010002d04c01d0741125100d0741e46894401c040342c907041120001606814030040c9070069141501c0024100c5801402c0b074103001c5c445c10122941ca500c40c0c07250020044402a0000b05400060901076000e680500344820006d40855404411440801c04451801e585101003081030341c81402051b0340041041c48110340c0304086c140d45018044210b958100001014030a91001d0529245d0314070f0400540e8002c00400720030700010709040c00c01120319030100100405101e014000a402c0d1280542145d01 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 473510044 1250 473508794 473508809
    0x7050d020619020a0311030f010512071a0307030608030307020609060601032c03090a031a070c03020703140a020901060513080c06070615170601140405060a0302010e0a15020a02130204 81
    0xb141030040d0008020b503c9045001d00f4182d983c0e003500800760b05c12015501c0b400e030710151402e06505000070408020b640c0c0002c400701c2e1340402c40c00e00445805070080c0401003034198070542c0b2904d81900540151a0386e4102a040d88004400c002e489030340050400d010b0114201a285948c64080044058031384184550488101c0c070b0541d5041c40c00c0b581e282c01d84e584244001d503410b0607508c5000610890f103a0380140c510080301d01c6007002e5101091003041e000f51590030300800444c202d650183d00c4816a01c405000714800c4140403c0c1c03250240090041140e0080c0a00440d40e1a90800341103500100c0400401c0c40310140003041c0540d0010348180c2d08403000b030580b41815080d80c0c1c0e180c041c0c40c101842807081c04030080c0c00140c1481c070510300e5034241500e50242c9182d604085e90700680350941195640710320b0038001405015101c1520000590740c082c40d00a41c1102000041420f100c11540441c00021030003d130f0042d00c950201e40c0052051007200e40d91040d003ca00ca100007603028600030403a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 473511294 1250 473510044 473510071
    0xb040b0d0f030e0315060d1b0824060d080f0f12041e0209190204090e3003070f02344707030f120e1203072307050d0206 53
    0x741e681c0b0701034185c1080c02e031007400c40320490008141d0700d03411070a5651112607994441180503a00450ad101451609848849200140d203403020004486800e8017101404000b030000c0d06200491040382103176075581080c60f00c160b4070258007081561500b0304a4064030000841c01041425115070081c54181c9030700100030283ca6141c4c008080071b030035103074000a01c0c865420800010300c03103100e00070540c0b555149406400e1030600e110005e107034550807049075039081450701c5421155aa81c0010b9a8018034039142c0fa00c0400d032000ba05904c1c11061038214242844410858610711750b04030f01c0c4080e22101e008581c280c0395a501242d00a0024848078407030f201068000b00540030b80c1000d903c00c2041802006048803480c45c009001c003c0c0d101c0c14094002400c08000e41920940141001044101c044410004030103000320a5807a080c07061b44413009a040003000c230328032510801c0141c40c1049074040c6038403070740b02180148505900030340017180e41d070242c1d0411007000c50000c01d840f03219500103403801 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 473512544 1250 473511294 473511301
    0x812180a140c030f1501060908070b07022b02100507020d0f170a08010807150e010c020402040807120605062d01050f12060a0f0609090b040b0d0f030e0315 68
    0x5881c002101416041d0310b1140c028a00050343c0c0400c9140540c4075050007a2002170307200001e68098810580150060210750002004006000242e440c22221a000b559485091620005010036451004002072070465401d2600c0096140200f0260303e01c221000010248480000d4410f40a445006944841d050340030801182e4481c0e84845214841c5048500d010914001c1d00c440741c00a4400c1c400203007042c4018004440c040045101070211940189142003100e400240b03038505200f00b85040040390742208045445d04c2d011f0754042d01c1840143d03000261114201c0108224424054803480e0910010800c7c50801c00440c8804a419a4922000a1410010034807414080f55a181001410001c82203a140070101801c17050b074072031201c40800c0c11300e80100602891181c010500828070725004008894220000c50201c48101c000461180a250001801441c8200d11319421060f181110320800940340541c811541c4217860313455480d0325101c20f050317039807049000c2c00d0107014a01010 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 473513794 1250 473512544 473512553
    0x50c0a0f0206070c140f0d05120106140403060209012f010f050c040e1305061303020c031506010c1a090106030c0e0f0121060e03040609090516030e1005040812180a 72
    0x540522111017003152800c2c102e0441c014a04442280c0000c0058401f042202040303140c0c0c0701c03441c01401c00d450421562240d00c0c0000c0c41c00d100c0c61000801700b44c0c5c0011b50121070b9004138a2058a01d05000c508a0f20480a144640c242c4013030030381c0100c10394030b000c40c070300c0c0c802c0454414580103000d00083c0c070f400c20382071000c020403030780b0060104443c120400454000040040056070b2140d0081c6044441000c01c030f1801914080e0080e030b015210350803090105002d0f801d0100a15030041091038035403e24076844c1011990550340c0390300d421100594100b0004540c005402010480c1d11400d440b40030640d03156a44420003030140d5006043c0b00c01c4800412a04d0240e051618600c80602075486081900f9a00c0c0700c11140c5103d045a40d03500041020004130b41c204514000601556038107100034a4980c034090003075510034000d1010705980d45009030b4071680820501d00c3c9840455400c105c40e0030181005802034002030300407034001e003c0e00300142208490300942d24034086c0c0b8200030202c14410b42e0303e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 473515044 1250 473513794 473513813
    0xe01060504180206072d11060304110f0a0306060f081608070302010c0611030f011a131a07050d020106290307030b03010209040f02030f01050922080904050c0a0f0206070c 75
    0x80c243c45c03900c0311a41c00f4400b11899400c0c0f450194a40819030f4a0050b07e25015484488044400c1d120b04000c0c001c12003c2a00021514003e003400c0742d03000c041400c0240001c003808040d800c007805452508101217400140d000c0c42c03000362180a02215841159003201031440c1d44503000d07507c2d0b10f801110003000154000c0d0744000510340f00b0319001c2202d100000750340c42103400842d08506c802069200410a2484002c0200c039400c240d0101d881c507000b0000945612014680f040c2d100261303522101d501d502000c8020742e481d0b40c2d802419035001c06080f40b07000b806800f041c01030365181c044c0100c074181d030040001040802014009103850a41d518150180d000344058860702ea003554013041490010390342c0303120f030b404d043c00303e982c005032a0304020b42d03403d241180580109024074410400e10032000d840504000f54044c403200780c51106405890400c005020b80c0c10000d812505080030700c401032a124010b490040c0c5507030341c3c8119484055100300d0352494142c40800200d5000c0f1444030114000d1803 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 473516294 1250 473515044 473515057
    0x1538101e0302040312030902183102100f020f060708071107080601080d080612030412141207120f050a0c140a0807020a06230304030201090b07030e01060504180206 72
    0x74014105680c0342c584112150060b041140020b40d01d002c000118903000301407082001440343e98102c2848c02c10700d801f00503003010810303c001050703460700c40034101c4040c030914a501d9030180140441465210000e000701e4192000c44000d805411070a4000400000b45a441102c1554841c0c80c50b466685042d076103506104c101c407540e8011400082014003003003102034000c0404400900303140443c500000e0203003401a1099206036855016418075010003c10764068441c0c00b107140d100c00c99140780010101e44c0004c2c8059003401881500d00500004c20060300c2c80500500e110041c1503240361041f03580d680240560004130b502800140340f03041c4641c8810b00396510810104144103281d4130b4092415150301001c50382c040002070000110304028203018001d11032401c100c0c51140c402c0b0701c10212444c503a40070034614240032001030f003418400d410085405800c41c1840c40c844c208000d00901070210806115069801d1500004403420148a41da401d500c001c0c80310420507200c0d500704885a8000b5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 473517544 1250 473516294 473516297
    0xf0f2c03090f01021005010314011802031b0a0e01030b04030e01050c0703110411030f0403090e100b0711041a0f010c03020303190204080f0a0309060c0803041538101e 73
    0x5d40c11503410b07503c1a203010390b02a200710040a4800d80c40305082d03c40c0b080c51130700c0c15135141002c0401a140080d14820140c421a5200004803802c004034404020719400301026031070307090001042c848584d49181c0030700d0282d50303200740690352080190360f644140c0301d503540350b0b9120364020808101c05003910341c40a58014400300c4d040c8201d4010000c150015603000454000031401e000c105500402c2c40e500031301d032900b03c80c03103240380039010030aa10707a2520031116807841c00034540d02000f045403404981040c3c010410001c0b45601d0740313801c050010714501180071b0001008203440b158002c4002d104090b40c1540298034695458986001e03581200c0c400c10020340d001e01001c01e6000003030161518000c1108014100b50341c5500300100004140d61040f4180a01d244d00d82c3e01207404641200d901c60340086401d54030205180210008184901000d164881c40348141c500d50800c541c1c503a0400b1480a6640d00c1400d802800c1140880058211a01207907181c070801410400c280700460003003806 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 473518794 1250 473517544 473517553
    0xe01030b1317130819080d1a0a0915230127030b09150105090105120a0624050f0f0108100b070c150309120c060f0f2c03090f0102 57
    0x404502c0116007002c0c20300c6001d01c1d420034081c4106101003040400c001c900704440e060700301c03071902c6000d070a115070301c0030707441c0d03180c85c2c85202000b03002ca442a00316101c0003a0003a1801640e82d40910000c2c00351b00d0b49540c1d80448000000340401e400003c03502c1c1d03145104000004440c0000040d501c0350095540c0540686100b2002000104940388500c008d6024140c5d41c02e5a1070b10305005801d0200b00c000c0c40d040c1d001c1040051005848040420b4103480c03054908800e0346602c208554a04800d401c0c000740040d0526051400e601119840c0b10f81500004841c001420745400c20000901d10700c2203203640000f401e01c4194001c0d0300c01d001d000d401c9a908001c8038036182d1200d0340c0c50200e5100960035280c03041001c04c1000010440600c0c0c4a4016a620313041051201c0c1da503079002e00d40107080904042101849030300080c001035501185140d96600f0040119032140b000700e501405400346860168210a211040e500341c000d4201a07070420404061071074202e01404108003e242c0c504c00c0f90441c0700c0c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 473520044 1250 473518794 473518823
    0x180102160b09010e09090619050106081303021c090501030b0d02100503100b0304030302070308090607080f15030f0a03090b0f12131a040c1e03060506040e070308130e01030b13 77
    0x1950850503006d2041100505558500141100009910001820f40c1c0519103001001800ea000c007030a6040703141070b41c00070b80c0314540e800d00b02c0c40d00401602c50601c11007040700503020a40c0210b5000c0c2260801c0c0c81c02e01803820790000304013400d8500d01c80a508031708944003c00d4014820002940c1c01801c02e07100c80d01e1292580200c0364550411134040340800e5001412806241d04000b030301d68001c5035800144074900c0d01001c010030141f80941620310070302400c0086005446150319007030304034001500310303001110091340040e50703640002429404903400c4000840d6480920080b40d41c188511034100d85000c14525200f02240c2c802402841d0f5201c40304c3d01b16001901b1f004d4030400e024001001c10541d0704190034201881c0c29607501a91008072049010417403200011801340c02c0f6500401d00040e250399220115000c0d04078600f844206014025020080080a901070b01c9400c10a40b001c6145039120351208420200a01028180062a00c005500105540d40318041c42d449403411200a03039 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 473521294 1250 473520044 473520049
    0x190302031204030804111c030e011b0809190b0a05090102070e0408030a0605221808030708070905030a080f0c0a0611090114072102070509010b180102160b09010e 71
    0x203100b035804030002660300040c401484449003a05400c49001c8607a02c11154246071400a40e518448004080c4415a0104622a8021140405a80c01d441c50000090340e03185451500ca0b880004014402c1112514007840b8944a10100081e0713030115492902d080d1002c00123a5264112048980c110310940a003c01e401125112050080703202d0302c0440d45070b00300303103404a0a84d0240d070450f034080c0d5a42e000c1400540603050301c4d1408800100c80c0018400905280e05210740c10f05e000c0503050a070b001003480401d5911540e4240700c2e4245a80d0100141d440d2010151610742502010380303c040103000e19404112054010010420310408490302d00c552035403400c007031303845121005d0001240130500355103a582160750300541070b010117221483c00380d80d075540c04000100341001c84402074031041641c0d602402008224050540102850850f6949000c1c0803202e9211151070a0748039070103d40b040295000003020b0700401200326a99540b2402d00b414000d81b608043d200c00e0401a00d800120207d4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 473522544 1250 473521294 473521327
    0x6010f120213060309111e012304030302032116050a23090319410c01030e0312010b03091905010203040b10120602030613050a05010e071119030203 65
    0x14009600e000c03915005c5030404401007a55402038900036183e010020700f810301844c405210340365003420002001c2c40006d942401c0c40c00101c14a4202c500c0001d00402815000800360101b2507294103071a5111200d240144540303407055680c86048150f019412820f41c0c0900094801b089451400c0350312038080c07411000c0552540548896203650010340d1040a04080c41008610202810019200d41c001e90310f005015260904401c41d441d1b8403982c08030030038041042005140380001208201c81c1600c00c101b0f80f40d9402c0341324140401c1c9404000340700c545000c07095407c8100b5213071140c2c0c2240c1c80c107002002e4580c0014016600c88c003d80045448401220046117505800780d0b00050312854140703000035051078050b0062503610f40c5198108100c40102c00c8a40020380e103c1ca016880e0b0316410003140d03d40e0030704030316240490304150411202c100b00380d0095048a81d4469504281e88503e0005d1383c07800e80750070501505400100d41d0711106032445045504191182c41201d01d400b00c40304d15070918 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 473523794 1250 473522544 473522549
    0x1050319030e12011b08090f0a060f090b010609081605032a031218040920130f02090102070b0906040e0c0403050a03180605090d02040f0605060d0606030e0606010f120213 75
    0x60705e518200508106500c25211648500e180e4000e0440b1200e02e248030365160f00340c550003080d054544242c0c10308950180c0040c9072150b40304258004950315888007078505411030040c2c1c1e010b446020b0f001c00208140189400c01c5800c007a0160401d0080c2c282e1618034200a130400f0010682e02c410f010860783c03030400403a20080104541543c89061808240c000351551100303040c8940d0400d4400c00200700d612441c600b003d01400c269400c10010703000411240244160398426480c5011054607030004990000d18085000342c0c2510802511145c4407840c0340201250315400810034442400303d42c54280d201b1350000d0f99084030b5802c0c1a44c03039403881d00c0c0034070204d021030015140240903402040191180c0b00036201c0c034140182040000e8000c02c14503da01a00039204548801001d244034006920031001f5100190491307070b071120060030540141c1010710504001034034044031403d0712040820b09500840d4141c1d10650441007002007250480c1e146262040701d0f03036003008444200811070b20100c00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 473525044 1250 473523794 473523821
    0x60c0320060123040516260a0f050f010b041502030d0507020d080c03060303030c0d09060c020d02120304053004060c021804050706030c110f1501050319030e1201 71
    0x480c0f800d00035094401c0c01030f28501d0041d8141424411802005178100c0b20303100301440c2c00801e00c1300c1009401c0b01c0c2c011000783c40d12a01151020302441040c2c2c0d8001c6542d145029500340040d843d03554a06040000900c2003540800050200340030100040b585600302d000944101c0b401e1a4079500ea145c00c80700c080e90014090790002179601e0710143c2081c041944a041411010700358078040b401b00e5240d100045c180c4102100018000715080d019500c2441d01ca42c0101c81007100c0105c490b0040c3d545c0300d14680352800b43c0300d0240d8483e10109500c0441e4803c0740c5c404040c040c103139014203480075402c901348500c0c0242d241e0452448140c04a801c090320040002c3d9960b0b041d604075500500254007484001070003050300020801010502c009601d070119661868005003031007070b07060100d940c110401c11109180c0641c03107040d540c035038000a52428021402e05a0611a42c0c3c0b141010b0342e40c51140320403400042c1c064002d20110b4000d6403040032a04001c1c0040c0c4410300000503840c2100c000d04a0b000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 473526294 1250 473525044 473525069
    0x310030204180503070305070c0b12040b060a060c140102360603150f0a050a0e16020a030c06021c14150a0501230d02030f0403020d09060c03200601 65
    0x41546001d000702c2d441c010b5095824249508a901d8181d141d1050400103002e12000290110802c03c205505c9002044405c14850304c810303e45c80c05100e0000b0646082e9856070105000c122280f5095047c4400c03208582c031508041c40091b59101d0300080c0c10b0316144407075513080c0135000044400c0702c01072440d606111070b010304416400c400304480303001c0304004500401e02881001b4203510481003011904500300c401308421020030000840b41c840e42d0b000b454200f02603690005913010510010750003000e9600f040e100c04501450100d07510280503c0141c00540380f9004280441c2d0300c0c1c0d00a041c40070700b50f502941507090351581501031340d40c010b501d11102e00d80c80301000040c411890240600350812a4000892071400e0b00081007a6501d080c00c1c0b03012400750001581801c000d50071640302c08002413003076441e0714003c904034402d8141203405402500814143e07101c0700c0d11503001101511000c3c0c841031210b41c45900d0071a507085006041c5100424814200c0d0011441089070030f000701005200310 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 473527544 1250 473526294 473526299
    0x190908040b0406091e05011d21010c090b0a02031902030403053f0a111e010e0609010905100b0d05070906050a0b0909040f081204050d091512020a05040b0310 69
    0x80e201c45d00c8000c8850310090058030140700c280c0c1e1001c5240404000f0038460346201e40602d00281a080044048207901c2100c0700803001c48a41c19041030010b2415600d0790302c8495607d6200003420300c0f940385034100581041084060601d2401c1d28039210342d02c02c0c4100d0341055101d554441c0b1b00506070890780c440d02c003080040300c0301201903c03117100081c0e02c0705013a14841c040c010828515000700041da100303002e40c01c505110a003000308005015800400c885d03030741544241c0103460007401c1540c42d21002d80502c500041d00d00e0340500515012903845001090b04130314469640b030040903002c44040d84440140200004600304000c107402810160200068151a003810402840c3c0a64004000c00009200280450352000e84a4ae407040e00300a407500300f400640340c828024420100c2e82102e83d580c403414070040c00310000709541400c445881c0d072000c894940041039110160345449400040584000c440c0350038240d0013410200c0c0c454104a81001d403203e200c040c00d504121003d40c111907150204 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 473528794 1250 473527544 473527559
    0x30e0a06020c1906150b070507060311160b09070e10120831050418081806030414120c0a141f05040c050a0302090a0b06040b03070203071a190908040b040609 69
    0x40078006c1c401484607900d44007550350743e60b0b03c80c0401c0c8900d006041d07640001060040034401201d00e002107403200c0c0064202949403907241d0f03a03016215944240300b08100403a40e000c807900b0043c003400e030603c0c41410913498040c202e013004443d10350442e0915010720500141c0c3c20086591070300f004040c052420207495801815000d803081d80e108902c036a007170040640702010100c444c02c8134980c01212840d41c9845c0404c440015140366191250819030000030030050288011103081801c00e00c1c41502c42d030185600080c2054000c1e2403103c00d050300004012030010701e08100a0080003031001c240c807240e03004400104241c0400e0940906401c0d21903041000300003041411030f014107000c5800c01d084505503000310340d21840080585284656904250f5001da40b50825207006010344c0c0b00441c0d0328900300d07500075140e41018004440c0c840c021400d030440305002c41c00c2d451003a0880c0511044900b4404841c101501c460320701511850000c01006c614002244000c1020300b0391a110104d4031881c0a00703 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 473530044 1250 473528794 473528831
    0xb07021f0509210d0f0b060a05070c0605131421010b4002160609060b091501050f2109070b040e0103032a1103010b01030e0a06020c1906 60
    0xf024180202c144203d0202d140d40c1c07098030302c004a42d0304001090024400060010190403400c140e200b41c01081c040007082c0d0117001003020038858100181c4540d036844080e1010b004485034402c890080d010240301012071200454a0602c0c01060440154a44541882c1e90a800b101c000c09a03511180c1800e45410006921000d200d40c5500420000e03009409400c2810011000c0b408a00c500007890b0300c0c400034a80507036100b10024801d40d4150800351502c0070003403196070b8007210500c2c244003000c1154640030041501c19420105110020560b120045a840c2c0c8000106841d0403022302070035190182d00f490f090445101d4001c14141410711803829490720038150700240d8840c00c00c0205002160391019918110b80d41418100f8803041c0b1a0340400300da031660484944d000403000c00d00c40601103240304020406605030000c1107000801c00c0114151250440742c46d040d94080301880d40004da542d8020f041c50700341613094541c042ea81d5400307100c198040420945060b0f44170180e6401542d20341c80c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 473531294 1250 473530044 473530063
    0xd050c0307020c06130509040c0305011406100e0f0114040305030301030c0302211213090c03060303090b070209040b06120d030b0901050d3c03110601061404030b07021f0509 76
    0x1101c0a0170906400220383c0d51425038003031a40940c1404000c50104241c8890340c001455000c0c00070301c0b8000c49442244150341e400c030384076885400d080001e00b07203444c000c280b40e440b000005000441480664401502c6c0c103c100c0c4011414094100000001307c1d20500186010b10320684004031030701d15500400240b26610f035100000311201103402c3d0b02c49a00014800804007041e04100c1e00e51402c022109030104440d8891580107040a440c448910b602d0340c000c1050382d04c2500e030080b1143c6c413254640d001e4041e03414000d400c10805004203011940355081140e20041c02800ca20316400c0c1e454507a4100450b4818510101c3d0700da4003a40c1142c500b00114a015001c00c1d41e09840010041c2c5a0050030f011746000c02c80c0d41e00220400e0300507038902440d8202c03c0200501d10386400c2c0c03450b01e8010010000c06042c04201d00034140041040c03841a0b4032200400d1840342ca003800c05043d03454100785003030040c0031a000c2d8400e40d01a64244030708a28000c6036441c0c802000902887c000e01c2c418200503138074 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 473532544 1250 473531294 473531299
    0x241409060a180527150108030a0f050d0f02040b070b0603010902090a02030601020a17040306050a05090618031c0f0f05061518130203040309080619050c0d050c0307020c 74
    0x2050602184619905202440490300800f0079140c4402d8640788080e00868209540d102031220503158200b0b002a90880e00d10b008100c0384101d03a41c034940326440b80115400700300050980d50ac0b0a40d20b91146018251154441200007910102084036104a134807a0340600040c902c04075800050083d04401c0c3d640c0100309800a000c07001d4182c0c005000c0c12001849081400d5021020400e00d1740300700700708954140e01c000c030102146002c4280e040c498000d44411590b40d4102000104106624062a8003c0034007400810715a2241c0320803a01d602c0d004464180148002c0c02078002c048400b10020328900400c590000d0503070b00c0d4072555010b544010b43c401c40c5142c00c141c140003050305c0f0f100418220701680381032951281300c141b80005162014841e01544040040098540510503600645c05240f207a202c0030a2560341d140100e4039914222059a8401d8500e180b0400e1302c0515002158842040074601d490031070411150400c491040d2081c0546200110411014540401c00b003160a03104 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 473533794 1250 473532544 473532559
    0x501060906081803041a0705060a0516020a02031203190c030c0e0f0112021c020d0e151015050d0e0a05010f060509010b070c05031209012604030324140906 68
    0x700c1c607903901d100394425040901451b44003032880c0560103090704c490f0369001c015200c0a081c0407030f1090240c001681d040301c1480b015603501d01c9c2c03a4000551141c0b2190302501600c84900001c7d425056900028080440b00c1d92112090568840a06c034032281145141c50000da1311503000b400034600d140038036180f805800c44031181359051382c01c100302d8070600c42e9007040543d0380c403483d035030318090b60805903c0c44212a0011405040c0d01003550442030f00c0041130000c6039034446090310300680e4000f041d14100c0c441c1c841e18009201e042c0b0a03080400000500d810a9464600c003540300340201c5010204140154200403118000c0000c01c0c0560040e0784080d00d414080d0340d0030b1600081903200107100e00b6040500014603c0200700e01c0c88400801060028159000082c041e101054203500c4010700034002410002032181070020303404448900c107101d100100706950780f580c050340140501c20404900100390341803c0c4604142c440ea81018154103d9402c440c80914030900c94140005001c86201c4c064 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 473535044 1250 473533794 473533831
    0x150103051f06061b0206040b0c06011403010605090a020c0721050706140a23070b0a0605030102072d02030f0106031e0206070b0712050a2f03070c0302030d050106090608 74
    0x28407984d00e602200464404150710349407071001a806214907404515002c40c0400c41010800000c00c100f4101c8058403c9248100c940004140c200c0307509005160f4000c800c1c00103e000303d2055805000c6047e45682150300c1c40e612548a5025030030312680004d80100c010880d601040000c0c04400c00030442403c1c0503a5015400b842442e440c001e9000800400c04504114440d440740446013041c084904100656245200e007071548281038121a80049603041c41c40021300ca0030148219000740e600102108141404106a50402d9820b0048080080c281e80961000350342d050110700351900003a00000340c6945145410000c0942496074090191410030480c40517856480c211103655612000d0b070781150303130f440001342d4408000e10b2203070005078503020070000001c1055221020840120210204007080b41203002c200070100a41c1c06030412003440465803a902035034101e810688680160fa0402000641641c11070340240d02c0040042d4604a003080640d4201c941d040e0408480b0b00d039901c0743c89 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 473536294 1250 473535044 473535047
    0x82d030711070f0501050f1908040519050a0602161208060a0812030105040c12050709050f030a0c0504020a1209050606150a020d0e0a03020d12021b180702150103051f0606 75
    0x100c46104e0541404800242da0941030100c0007203846101180134030085605441c54001d140100c1290304451070310a02178400d468156400c1c000000130b520200510300c85040d6072745c0340042c1d00205903d8a88014144200700007032501e603042a4610481e50302d14a4514011003003200c024410f910010b0203401c00c050401a1102c07030411241958410389020131a070081840c101c1d21100400c900010f10b85c40c0000b0f120007282d01c080003608179201210b49a81e446140400c040e200d50481c0e20003030940c0b24078102085581081c1d001382503104400e0400a001c0e0300b030141c03801d00b41e07a0749e0fa0003161b15030890810052103207018403807401d41071800b0704801e0400d0b40003003003c0d5956400400003414030594030380095196881c0b41c03503003018641c09001c0000e0403805141107030b05000750103105030160248100d504074003140c01c01d0803105845c0040c088510846c1f64031075000282d6002d080300b0118080d0141041d240048008480d0080d03100d08020100340511940031081510480328000d900c1d03041c25401c00c6810b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 473537544 1250 473536294 473536319
    0x3030a290f1c14071a0a0c060b03030c0a0308040b16080a0f060b1c0c0503060a05040207020a0506130914040201080601030507270611010c0c082d03071107 68
    0x49506968a00c05103548003880126504801001806a510f802ca500a0300f000441c15204660a4405a90308080c0e1400c00440354000c030761384140010040071240d400704805030460700035440050b06482ca0020102c503400d08080c81900c099020800e010140300c00c01c80b03580500b07035005071058201e20102110b28801001000013900910410340c803141104464502980140e005108044489039544a400120b0380310308204041c0c3c298040c1780c5404681c0c3e42c2c2c002e05c00c0328811b40c1c00500040c9100d040904201c02908010303001d9800c4a0213840106440d01d50364000c0111480ea060b826920034070b8034050b601500c80e411100b5000b0b50580e428880140d802c6115240c0200c403d09010a00703070369611040741e02d47c040c10504866404580c86e40740d81c010022540b036050720345030307580d0101c092035107010b190984644804000008040c400e58001040c40c0e0005031000d12125512046103014403086072101258250300100200300010a10a180740c2111603405a4500c1c81c1c09800743e60f160402243c3c18 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 473538794 1250 473537544 473537569
    0x2606070c050106180e160b04090f0f062405070209190b0d030e010e030f0d0311040b0c030904060603050f06060f09040f1506110718060803030a29 64
    0x240480d95003000108078082d0024030103044182d00c05052400754500d640c2c05001c1910000d180c1e4021041c3c02c40f100d64a20f4803040030b075155420500d180c40d00c0c08020800610250690140069440c00442401d05c460300a800007041d4022100c140749000340380c1032550100070b0781c0007002c0c01810009100113071105110329a20400c2d9181035404070700103900020142c5000902d141d0700480b0b02600500309501302644100101c420380e180f03071843c05214103144d81c511268a6a000341d602c00302c0074040c03280c80780d0450498840124421800d1507900c020548458108a007800c00c075802c0403d0181c1039041134405c5d0401880c4600d418402401c05030315800d03846002810305401004002428225004800100c40440b03002800c10044c00c00d14442c4040203040c0780c010590003060885000400c0c1d403150761a11441c8201d02c024140300707460400c5010424116a8140301d0450700d80070000f440100c20300140d40704040b000c0c0003140c0012081e441c070003480f49015801416604201c040f01561701c80240c9034a1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 473540044 1250 473538794 473538797
    0x3040327030f080403290105030d141b0a030302180609060928030b10090b01020d030522080c0d11030909060a030b01081506010e010c0206031b04090204260607 70
    0x40340c4002e400c0442c258480e607000906030300c071900c440141c4401b41000c0c80080005010b401901641c803601015107900c41c0008600004051074802c442d071600d080700406142991a94410410303072400c001c10305004040006401003503000c1811000c13400da0f00780c0e292a51800322001d500e8814800c0001d5444d002c0d860106016240408411214031560000e080031500c9500840040c15940d180040b08074004440304410510001b0300050100700f18028000036940c160040c1c500c002c807104044000700700040079100060302c0c06030801000742e401113922511901030147c55a40d4903c4182c21807074080fa044030070040003044005149021004070a94044150031543c00070300d0707180c0c1000a5000c44007034001800c150b104000000e559100001d41c40380300c61104881c1c2807244d9428005540d10340c0c1d50031449001c20408400c4000501c2d020009640c003d60b0754440391520700c0c0c60b07030200f03809400542120703010382d034001024032440b602c42000c3e00175188062001e200b107000841d0142d407500c1028040c1e10 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 473541294 1250 473540044 473540063
    0x27051312020c120d030e12040b0705010209040906021902061b1b030a0201060317090a0e0919140c061c0e03040923010b03040302060705090103150b0304032703 70
    0x18000c910078001c1864038400281025203078007482070320750f881d9440182820003191510320001c1e5202c0c404070341450704104882006041a20301030b10300c005580000300849a40d5802c02030b50392143e0300c501c80c3c41a6039010316401a01c0310740c5e142c85803018400c44501c0c07206540c020420418400404035000705a1409826102e41b210340d1040340c0b4007400004603001e41d4038000410324514840d8154403000480380103030140d00c0080d48140e02906d0920400e2a401e4111740c1c0302909104861031003500c5a002818441103d51048880300c0ca41003c180f880821680c0310444140340403030700e50070020460200e60440702145000200f1051804405644818510316a11400802003a01c02030040d01c00034542900c1c140141c0740050400c005c81504036010f07101164500c0300105500016074250307445940d140e001000b041c2c8404030b0580312a00700b20310850405884640100c0c2800820001400408211003036680b641407916010700700c0c54502034010585480b21050941c5050705c0d90b07616003100e4101c142c94 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 473542544 1250 473541294 473541323
    0x150806130b0f0901080114100f0501050315060d0f05070212090f060c1609180b190f060f080d030504050607050a03061a130e0601020304060516020a270513 68
    0x103071400b00d540d0714459000e050040000382d5000103400c900c0c60302241440106040d5074002c102c441c0a01240107070302c6c400c092200180015400380c4025900403181c1e208a046640400002404552000c080c80050a4442040d000101c440340201c9030001c2c0076002811510f0000c6400c0150741c02200754441c4991a40c1c0076038004c0e0340f1990101ea20310148107050302c1c0e444d845100111b988a41034450240c80900d02101c6c3c082070f1107010407107101142e000a0108443d10303142c1000e013600200c10015958590b98100d01c48000b50548101001807510402014589150804042c01d240040800300103060030401044002000031914030f42c41105400c19580313490180b03c04400a02c0d440c0c010040c81054032612880d85440c1d0390162844d4540c4105480005413158030448c150001946e1440c05640140028450305000754041c0140b00e8003c7d42c000300d8200a6000a1015412036101c4142c500c60450300043c84880d201c6001c100816480c3c0500641c03d26441c5605800031030030015001c1311400d02d50 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 473543794 1250 473542544 473542549
    0x2030a0311090d26030c0a090510080f06012a170304050606010f0e041401080d031a0111460f020111030d05040516060e0a06030213030501060f150806130b 68
    0x6404800300e13103100141e22881e0585184400740e100301009008a1450600040c5500e0a00024500c0011a0346c0303082d641e0b1600601015000c001401503818800240c801480810a4502140c1c003a0100d1003a09141c03030403428004100e160f40044112511410801c000110b2000075800780c1002c428603000c0b1580d001260b0840d8801e00344100d041d4441e08103950346d507514030385092003070607945004107865001c0031803581a8120303101e118594aa050074094020324070340c010030742c20b000942c2c00005d43c0d010007030301546008441c0c200400ca90640520030301203580031007070b8902c0d050340a166203050000f9560315140d4a0304040d034188002c2c100084140c0624508100f481510744c00c00341d1090910881c24580303002500d42e152407081e58004a80403c000074018450a4401d0024001408414940e4201031080740139501000f13071308051243e9070304008000b80003441150b00030710591001c131110b2420180092117603004030b80315608002408040c00913903a80c91641c084148080c2000088a2a00b44003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 473545044 1250 473543794 473543843
    0x6040f030f0207170601140102060f07181805090606060f1e0c06090f0c030115180915060906050409020f0d0c0801020414040c03090804120309090c02030a0311090d 72
    0x2003a04482c0000b043d04613803281c0025001d0580710030383d11031941e000c1044012603580000712810b400210700f8002040d440e901541c40c8103800460402c41d0710456840d03406450380c0c1512a891020415990810490160428400d1a40102d4100c4441d45006064191460240140c2806c40c0301c24420b0700440201d50b08440c2202d00007400c0780d00791a5549420140f42d61248440070324132000d0b000e80b808240b41450188a60b02c040e2040c042d80421590804d00707040c0d0310107800340c5140d0440ba1350301141c2e4040f52015440d402141e1041001048081c00c04080006036181c591205015508000350b4070016690601003401102040d00c07156540c1c2900c3c10460180142a0b10032000e0794400a4085020249070745a8050380409450a00c00c000d8030f51000c40880b080b0f0100a411a9420302091100c1c00c5005012143c09000380b625061342500e84000304d0460701811a43c50250b44000341504030a5054059407020400d0000c0705400c0201c002e0124030218000340c2c00600b44c01442d901c1019076600c444 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 473546294 1250 473545044 473545049
    0x1b1612170d06051206040605010603060f060305060607020301050f1e0408030f0601020c090c0d0e07030807020904030908011406030d0e01020309150c01020a09180207030c0206030a09020d0b100806040f030f0207 92
    0x1c145131221056150065160b80c0180e4042d40e00d2410310001051040c02030140304203d441c01410619520300d8858110020f001c040c0c08168000020030000000daa000d00846c0d00a100c0300300d0226450604003001c040720000c0e0307a0020b2485103d00200000b068150064980c031200000b00c030725050b5900c2004034142615140155402000342c0c0c18090000004070141092251010041200b600e842c2c144960f41c04c0c030b07403000a003c031000304a150300600300b8440150304948641041e80803d07841b0070280d030a403901d40030341b1032508a19004011413840c08018100c4090064100064010100c4000030f440b48160f440f114095034005c291003018803070340c0c02101d10030f2141300000c545400c3c805100801a8a880c03084400c044800410342214000c58400c440c61140e05440712690008142d0902c98075401c0145430000d0b485c1d4691140340581c85a24203904000d1080c4520041d520b01a0815030085040d0b401101899020000300030000e2214420352000c180c05045c06a105d80490608078074110058 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 473547544 1250 473546294 473546299
    0xc0d0b060118080102041a1c020906070510051b07171605120901030b0108130b060d0b0f07020f0705010e061e04150e010c23031b1612170d0605 63
    0x864000f40c20708041d4054010f5a14100c010340c50082d1400c00088240a040a21001d10020030345035460000e25a0080180800141c103c60411344113440d000c1c108001e23070421110300361301c840800c6194580440e0901c42190324181545c244001600c0c0e1100551081c4142c112080c00003450001e40f00b906007402d942168000100c400480e9030740f00040d515000454110b0109040007403040d1598000c0a269102d00302c02c0400790001c00711758481c082d84040c050b014540012104c0c4030741021034490107400b445002e4400c200c018908080710001c0c070f41801c428480286800108044c400d581e4420051400c00b901210850344841c904091450800d80548445a505800040020300c0381e91800740780259000540700d9407080c0b450308005480300e4140381402810207101c8401078580380011140301480000c140200c0f402d050b915000042202214115101036505c064111500f00f0580700c064006404400c0305482c51881d903950f40e0090528604102c0540d035008584040410300e154000c034020b0400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 473548794 1250 473547544 473547587
    0x306010e03190c0302190b0a211103180c0a090e0705030d080901050a1404060903020c03010609090b0105030106120f050f1903120e0c06090f09010b030601020d020c0d0b0601 76
    0x461403c5003a03100244800c03402104848801c600d108800c0c82258100daaa14000e00e1400b460108101d401c00c1b075000803103078525004004d4010002c50381c401c00c1102e8a1088185549049c40040007640c1060700001c10300a5004400007a5240c0f21424684106c901d00d10f4085004a038201c085030504c1c4003a0011505481082450b00d201503100034080d001c3d000b0b5200030806600c0d200d88803810b0f034260a00d081044201200441c2c00240581d2045007030354044d01c180c5001d111034034002400c0d603201da031280781e00c55162200d01d0103110030000810f004040450003000301d2072511201e0302c02c4040c406005464802d164100701c09100c1d05002802c41800400195001242d105d40490104040312070140c000606140d05003131644034a00c1448c44d01184a001407a020182408102c80e9a011603295600f03d6812a0140e4040e2510a01c02e800703001a400469141d2070030000081c42e003107800380040704662240000d8041c9031540f80102940a130032000f100e0342541e81078016900c500d60054200c1a8941 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 473550044 1250 473548794 473548843
    0xd020f0307081e0f0c0a0c0b09060109061d13050a060c1214040f0b0702010b030703050f0606010f0503011a0f0d060305070f030b0a0518070f090b04060b0306010e03 72
    0xc0c001c2d0b05a114a0b084020300051035910b21081c0640241107070444c0c0713900d4510022401c0343c1902030141c00100b20500c0e28800b404c0950b0f60300650094241c410302d403030b50b1000c40148010f40807800f40401800000380c0e500c0c0c2403130070f140142e030a550004c0c0ca01140c5071041180d440900c1024072400113030300c1d00888140507038400c406008040002c05510303100414605180c2c84030400e65220098012504510000c40910060711074014a90020b09401d09540d81c0381d040b41899101486151300030b50080f006000e240030152440b0f420804004d0035181040b90300c1c030207245829002015a81544c00600031300c0e480014980c0d002400d84205801221a0f0f04045103490a003600c6412802c242c0744104280c2d081a070380e07100403089054940c0070041c600100310f030005007241200e40c0160703880400348400342070300d810180c006800c00c607581d000144401050f00060109900301c1c018075840c4a000d0303034100002890500200d6030f40c080505500e040021050350700b85036543c2004098008207120340741c0e11603d00b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 473551294 1250 473550044 473550047
    0x6070218041a0a09150c02010b0d080306040c09060906030f020d09240501300c03030c0501050105100c030f021023090118030c05120a0806091005030309060d020f0307 73
    0x40031019180c480c0c505900041c0503003e2502481061540c88083d400c1c0010030062400043c1c04241c1200045640e50100c0c0142c039641e900c820b0b40e29074042c2c2c46084d601d0416030103110541e0103850300d2200303101c948002000910707031001c000750854100b45000291842c01405000c081d20440180c01961820701002100340301c01c41030103404044020040000040402008006881d4244110044040100003078040c102e0900c1e541ca039041d0f460188800380400c59650700d00404083c0e0003c1d80001c20590a101c101b00091042c0c40c00340600b141c0140c940d101c9400d0080c40000c045400404002400051b11040383c0200f220031410b080d204000e022019a01018995a170380000c0402d404648520110350f800d40184666403240315290400c10ac4031869072020b07220072006038821201071240c0c80c1249a0203204002501100106076200380180c100401009000d076405081d080121803d107100300400c0e81e0002c02c07908904015070b10b8039215808034209100900070150351b281a45030001c10860640e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 473552544 1250 473551294 473551313
    0x3090e0c0406180810090c080a0809190302030606010f120516031406090a0b0105070b0411040501050603060919020f0f0406230a0804022706010206180c0607021804 72
    0x90319260344800500340c00d50000c10070380c01540309000164010f00117010f07041410390096501540140441c42e074650707807815050301d4690385940c01c1d1180040840e407804180b030844105840c20188410b05020b0703904540001c5c0c0c58902c090701403414032044203600c0000c42e019241407204196114400c02c40e5241500d6045c624806402c1c14100191901c0503811031a5208101c41e80101c8001d400c08149503502c0740c009000307005688a4505020060101b07000240440e0410b034800d520610302014407001d180c05020031f0781d40681013240300300c500380204801ca448008000e030f07220301c09040244c3c80040d00148903000f80b00e4042c03801140c29001444203010310b20013000b801140c00d50b81c1d400c001d001c1e4201c050510415101003c0200d524204400216244034001440c1c006000500155030390600341d02c807180c1080a2018072034814200401c00c4000d60301403100581c09114008030034030710790985040300d880d4800000004d100b4071000c903041040d0b40700d800303ca001ca029501d07240c904d94101818000d480 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 473553794 1250 473552544 473552549
    0xa1502070305070b120115030603080a03020702030c0d0302030a0e0406080d0801140d02010203190e04090b070906020d091e15020f0c03030406140d0b04050a060503120306100c03090e0c04 82
    0x183d10412500250822210003100d90040d10741410f041280d007000038000d0507076881815001010b403603e2012000c1585c2030000c00200d503198a0040e9640c1c03817441418104002d002240d4804c6400c0c40310040802e40200464124811500d40080b40a600302c0008005003030a4004000b1072007100c0c5160441034010b0a480d05035500c0004c2d02d1a400d0340d0204012559109039002401600240041004c240d0718440c04c1c14204080d08240c03600300c030b8403000716048802c1d89a043d90b0120442e801c2c001c241e40c00c010110b004d41744510142161404511010b400841c0a01c1180c090500c001412381d04c0f061300c1115040035140080c100c00c0c0291800b24001e584074000e0494201e10b000f6102200490715000003210300b20b840340e440303988642e210005040001c0d0800b49940c420030f511001c22148590712841624804c5298050016526082c003050518018285c01c04040c0c0c42810030070300029640304000e0034036023003035482c0c151002035051904407100c103000d40c44035085c010b01000f80a80420f001c0054010f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 473555044 1250 473553794 473553803
    0x100f0513020d0b04060e011104060e03060705161104020c010605100504050d1223040f09090c0510021c20211812010207290f04020a15020703 62
    0x964440c100c200e000c08000010095000300c0c54000180000c1c4201c05103503025004090003d410f4600f61200390a54403a450712689202000030700384140390302b280d0407141d184016801003040b8905000082c0152007415110600d604003103620408003e03072090501c1800802800079912040c900031143c0c0a000c0d94000d0a21801c0c1c000752280200b4401c805582c2181c0c4020f0182040c150262240403036007541c6149030041010103074610524159440c201c81c0780d00d4001c1c0c20740359501d02d80400750000c40815004201040c0c101060300d0b010030303031002140c02035a40450b00a8484035001c1f100343e15140b2840055000740c550281250703c46900200e10342c0e0160290026900c80010103881f107602d442400d01031030548000c011101d00000b40402c0600080ca401400317604201001d10b00041c1e540c20203000c0e10219070b4000403c0410021203003c0303504241c1c550008a442401c0c105011944e00000602045560440704001410355803010b44140040001080420f0340c40c1d24150000e484031258081602d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 473556294 1250 473555044 473555051
    0x6020708251a070e0303071a070e010c060c0203071407051503090d0e030708251e091107080a05071202190807060e25060201060509010b1b100f 63
    0x3068a00711050030844158040703036000d940200e400315201c10b4074010f08200c00304064800800e100c0e45080000301002e40c00303651440820790072454009010703d00281803000308210415210791603600481e0801a0781e92101d000310b010f21302007004030700c1e42c01103c901510410f115148a00e00040210b042000d4500a4030f808414140a030765444036031005886031403050303000855040c65140302c2c0720250035450303000b01501c80b440e544400c10303440e26800440a6009001d198030384402941291900700040021507503042005200c00005110505107209540c40c06407a2408264800181011201c80c1684200025115003a0b08801007403038101400032148000c4205800c000d2500001c0c880c1e0582c040e01c8052081c08070355558100b060341016104807002e40d02d600c41c00710301550500031000d002e51001070800d9118107680c00c01c1c14540c1c481d4490360646e45044420301442d21007800c041c0c10346548a00b00c81d030300eaa2261050340070085940d9240024003554150707904440c0140c2102c551b8000100090 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 473557544 1250 473556294 473556337
    0x30c120807120515120c1f0f05250c0e0f010b04090b0301020705010509010902031c0906080601021908090a0e0f060d030c0c0305100c050a210906020708 67
    0xa0355019815030710440419410b515480340849650031242c0d100c1424800556024a43c0c4003180c081d401c8880180815040a4501505400c4c4aa810750492031022400100a85001c501500c140b41c42900d80c820040001b0f42e41c2c074003980c244c03c1d20100c1003568141120345e2200d81440e000000c3c1601600f100c81d902301d804941c0b00c5401a082c54181c40501d40000d28003440d042000340284505440c064040d5000d02014020076004e10603a0310407104030001142c040306e1441094141401c00d08440301c64591920ba142d04103a01844180c2a80c080c1d003841c04181d140c0300300503494101c04504440f00340c0003412030702c020420880094170042400391100007800d40c4503012011001f0040301c03400440c4c00f0040028247d481d101844150290090803e020300c02c64035120a0f001d45c507140c0042d619a80003031080c4803641d103244952f10b9000e02c0381c90f241d81007001c0580700501b031a01d5442100c802038074403100f030217040d90164040c00c95141e00090441d0390310858500001039401260120494600781c442c413 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 473558794 1250 473557544 473557547
    0xf030303022721160807030b1b0706110f071a0a0207150207030311030708010e06010503132a0f03060b03010b01050f0c100c0c060c111e0f0a030c12 65
    0x800c8400c0020040c42900c000703001141114400512002c11a10500075140c004030211328095020384250300c094150141141440300c4031880181c48844800075940050000d00e0803907040c0e0b412150312503008185220521031000590003440e03401c00804100041e10030030807031080380e004804809a0300c046903c0da52030800800f28001c0a07006030a5164100c82d01300d00d03d4142c0e00501a9034840c0c00c0018405288010865081d002115120b01050f2000018040c000d48101400d6100201b444c0140c9075181ca0049211616207040d0001d101c0c0c1c4807043c00c00d8003041d40305881000f03c440380503983c00c0142e42d01d110900100c15803100f07032001c0b40f812002d00042d08040c011988880f0043c0c40750b61074001d044144c00f1079948600c0c0c8a070050700600c0b0300c0c602103040c28011082d6000260759060380305030840c10200c044030740c03080c138090034041d00040e40c80c107980012407080014100340e00e118020f18442e4074036608151401d01090000d0007040c40030340c00c041d00b100602c0040c9005070078450040f02907440 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 473560044 1250 473558794 473558857
    0x60106080702101509150602160f09090611031302010e09040305030c1303060f0c11010608060a0902010309170c0d0f1211070209151002010b060304020d020a0f03030302 74
    0x1c0c01c41c0107801180490300e1610300360f00548441e0072802185460307070703030f41319001c1c022141c1801940c07a1031210070908100c3d030342c0d040001240c04451118060300c0d9a2800142c840c0e1003286216170150692181c00141c103005086e80801302028481c0c14040d80da02e44656214810f00c0201800c9000c039007000710521003810040c440512070345c0d25440705850354a0706c8089a0380340d0003010501c0c4071f08084150100c001810b500514000039005000442d02c2c40b808034016040202c81c07080c20200d41c0c504a001c02100300d0000b07807103400400011000070807003003d000481c00b40808442c05480c101c1047e80c42c143ca100000000c0c2950381060341070b5924591201c10454176120b4014009002801c070358030340c2e100c81016510280701ca0004c044005d04d4000c040d404150041c00884007001248851940072900303051041103603e01040a00c020400703a0304000005056000180000e4007a4459031101310441d10b4a81e5004081c00c5c800d40304041c0f041e80e81c903009004c0c1d840310708241c65903403c0c3d02204220341e20680 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 473561151 1107 473560044 473560051
    0x62b0221100212060d0b040303150323011b090b0d14090606100f05040308030a090c0311040c08010305060f040809060a1101061d0112050c06160506010608 68
    0xa016030081d40300083ca480d00070001d0441085c00034680014040c0e102c1d605082c000350702411040400c6081c4105d0b00028504450a4486402c401110442c01a241c00c0c44000b40441c10044030440a002d07006003007440811090081804101d003070802501c1b602d60503030000030324039a620114003110035007038a02e500c168000100740451814414202200305400b0306058017200c207034240c014032a01c6a4880681260340c04404139608426503004102c2954102c05035803006038581c20310001c142c4901908a110380d26103500e201c05c41780a04202412207401001410866882a2800c02990402407045542000402c1090410742d50f06010b01201d0005544243c003111035424241d00310703101c1d078000000c0310145803200341c00b9000516003141950910044626150503d1a04e280b6044000321616801740c008075104904150303a20a01c010240903c040f20301c641da9521065075196000d4 = true := by decide +kernel

theorem cover : BRFrame.Cov 473381294 473561151 := by
  have h0 := BRFrame.cov_init 473381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 473381294 ≤ n) (h2 : n < 473561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
