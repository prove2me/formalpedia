-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2451
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:45:06.341579+00:00
-- url     : https://prove2.me/submissions/399183d4-1478-4ee6-ae16-8a4829912f30

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 440647482 ≤ n < 440827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 440648732 1250 440647482 440647499
    0xf120a0f050a05060c0f04060509041e0b1c0f022704030210050a020c1507030b1c142b050d05090604020411071a0c0c03160615030b0619 60
    0x209018180c0d0140d000c507800408000c001c1080540100005646a0030b2907440349a04d0050707c00d44c051141000000b00c5c20b035006841e02c0d04221083c0104441c1c07103ea0340100441c1200030301c0d80c40c02c0c00b0b07c0741d40c0640641c50100190800450019004131030091003407555003c3c003100b0210203a8010002e00060f01000ca81d003640058507003c0c511070781c0508025801034052405840c401303041c6408082c410000c400e00c00b080001d507155451440c80b003020b0b065442c86401d030000c0c030f03000102a41140301012110301c00840ca05010b00210310600c80d290b80300c0c0410b441d80e0766030540d0801c40140000c0e15600640c611342c01200c03646240c02d49242c21841d00a504801c00d050700e0701a21440140c1c4c0c4440148000c520b06405004001340702e80342d00342d00341105612000d450a18900101000090b008007003070302d1505800413542d03c40d141c007040b00d5896010f0401183e20700d800d007405480c0325151010241700c4900104101040306d40022901c40701d601c588007040344040001c4603500700300d403c00c640050340300b6 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 440649982 1250 440648732 440648753
    0x103020703120c09150e15030609360f01060b0702130902040213060e10020d050a030b060904050f1e010518190614030105010902040f15020312131202010b0f120a 71
    0x40d155511b50095024102c1807140d030358580140c0c61803402c000e000308401c0d07031600c500d4198401040030603d00021707030b440c8030f1035001500465012500d145030207030000c0f4170300005074452440141c2c0c80200142d555030180c4803030324010b100009601c10841d44030140480b80980040316032500007080103140c1651844406c100d90102d070f01550220b0103401180c113451400035031902c500400c600280009083c401802046072054102c59402e240e950709180c2d80503116481034aa5040e4041c1013004103042c084240a4074450851700c0c5403403000c2e8039030040c1b0b01110320301006048520141c5155040c8003010848400035400501080815003c5059030051039602c0c00355400503d04004811621440c0900341425a54144c20560001d4010001000000c1440c00300d203040b1000d014014003c0340e070700342c0100c4c20b610825207030050401d054801e221400000540035108140b103400c03640d18042d00607c00fa070a942011841d56842054498101124141244e500170901552015500440126601d001e40031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 440651232 1250 440649982 440650019
    0x6050402070c0e0a0c080a0c050c06012409080304030b04020111011b12020304110108040f05120405040e0d02151005180a18150f1b0e0901050103020703120c09 70
    0xa02c1c2c56441000a0101440d4443e08070940040900400e1411000900124400750514442640d260380c8205074612810582d06003101000c1680c0c4a565500d081c600000100794240d100004861085090180100160400c55800402440c180740c99921600616500240240d05200305410f0317040c403440082c0300c0c0354440c103904492148204e0b82c80780010850002002403a01c0306104105110114030b10310108154a1800d191045056540d841d100d9490001c1500041c00c91241100f10b9010003100800b800503100155001c105491581c3c202545d1401000205d001680204000095030781d040c0f00142c0e842198105c5041509a03208003040b5845020681034040381d44e1710b420301150040b02c1c002c00b00c01007804050010703d80c801c2c1c0c850000300c03000501155a0f0703c0d52224031018910703460300200d000c02200e511850b0441c0703001070094955911040f51510951807440007140c158041e100b52403e2075050b40d1850507000d20302403004002c2c10200045028800491400110900c1844441220 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 440652482 1250 440651232 440651243
    0x1f0e01020d050726181c0c05060a02121603020903030a090504050c0a051206030a0b0106080f0702010236030712050106050f15030a0b03030406020f2b120605040207 72
    0x141c2c0790510005003141c68414004c1200c00300d010811511901c8070790b035260170828042948103c141d0300d5408030714000040c18520b860070710300041c000301150070a90001c0081d00800a652580c0d43c0e03140c81c20201d1081c40100c00c12086100041217114241880022000c43c2504005261807000c80c0024511f40204e90300f500007529000e810f02031828540603458125000e22040c90601d1143c03003010b0030600030300c605040210141c000055140e9003c02031002069000004507005584907040204006411a2441410310066022551180c414401c54204241071025040340032035010441000a11551120031180400400503c09a4040c40f100c0014851144120b405a0b800e14005080d0b800700c2d0b201c28811001c81c1d05480e582d450314690b289049580882495403680d42207682d200904080a086070588000300740862815000500e03c05494514401c46003540d512000030007140002d0030031040811862000d100d4280d0143d040f03a084a1900040428815118408101242c100031001e844 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 440653732 1250 440652482 440652491
    0xc0f02041a0a050f06090d0606120b0402040b010906080c0702012c1302040f0303120213031101020c0a0b04030209070512040303020414040506010903151d0d0201050c0c1f0e01020d 79
    0xc040c82c000044200402044e00d42c4085102c4000008000c0c0c0070b10343d01c0501803c000401d030701c10044550b000710b002d401602a03240c81d081940c244641c0c0300c0812101240102e14190b0688083d40c00f502c0c000f0101c503041d9072092043d580d11244a40c0d260840f0100b21b05028440076010340e4255144010262031404465a0f441002c021007007201f9070b0031048254030450310400040c043d01401c25112070a07a1b4241c100801c0003044070501c4d400a1044690385149403118034004401c10040e0350710b03170480c401c09908036481400340c1c40030007a00e451240709101d00c0c94002c11080006080241000d40c2c0000c0c107080843c2405009507070050001000c0302d0441c00030350300150510108141c458400c05911064504011501c1e0010020744070780c92a000280407100000e6442d20940c103a50008040e0500c1500005103005800e4081075451386807150100155003482c1c001890426a90140ea40c0c1c0d081c40802010901c0031481c681080c50140d1001b41900e42c0c0b0b83d5610f000510090000749a840740b4001c0024 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 440654982 1250 440653732 440653781
    0x18020d0203040f1e05100b060403141005010915121a0f010e0c0313032a0b010e0a050c07030f1e050a090602010c020714061b0a0605011d070c0f0204 65
    0x1e003c2c4080c03004807024034004c1a40d040440c0000907107090015800c4000100f0040d402c0025419001d2544001c00c0c940c0e4440c007001c1515800310342c1c0315810181440900942e600c0c0d440c00d0064611501d000602c944007950100200c012010110403410700683d12002651008905083c4040b03003202c15100803d1010010840c058a03035803800c0e4003002c40450582181089c6080c1840d010182401038204054000280c000407004440c40b204000080201c1d1941c3c0514901491b003003009114070361b104060900020303509420341c0074852090070021b00749413400f00a0340d0250b03000508000080c0c00c21550307080006021404c5140f82c07803544040c0d2900c40d103403400c40380e00603e1458183c001e1011641040744400f00181c0004016040d10340f260b9203c04207042071008500f29001d0040441041000062540802240452102c2c0000d0150f1700c10700036607880f0b04401760300810b4115000e80655244001070803240c0300d8030300f41c21030038841d144568410300103800240075100c611803031340887d039001103030307034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 440656232 1250 440654982 440654993
    0x90609030809060c13060f02070e011e09060b0702010809010905030301061e0c0506180f060c04080d09050625051e010b091e060a080115090b04050f0118020d0203040f 73
    0x150b88400c041c4c681e507190a40700c0b020500225140d221307980a101450040045441c000e0203454003074050214031440c65a52441e40150403044080140916081c150010a010310640188000e6562a440462500c1200d600450f100500200501d105558800710b03840010707014070095000703104580c0ea08100d41c0c01c28190080010100c0305d10760a20404110f08400030390042181640070354040a04d0102c103110000341d81c1421072001081c003140c080c40c810001c1e04109a00070b0b1042d00c009004a03400ca501711501611404007500400d079100e20107011041c8030046400b45001c10b56144c2d00e44000d101200c0c1c3e40d076440c060311543e200b60040c08030443c0d0660180300f480368152600e003c4480d54074030304050201c0c0501d102401410350126521a0028201c0c0e2500303070103032004021240c020011140e44900801c1c10150134041c241c18241031800b5410145014006c0f18001d012010381e02c1c8890b4600140303140f00d0b07100c0c100301c254016000e01661440200740e101562040d402070341d90111001862070034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 440657482 1250 440656232 440656243
    0xc080a02040b040c08010e071b0f14060c0706021804152c18010e0d030f0b040204062c1203040f05031203040f0f02040f0c110c030a030c0204090609030809 68
    0x302e80c0101d2034000b1480440e0f50080b5150b044070b44840d241e00c00354440e05400c4400010807020703001210040042d15080040000d40c402c42d0350300403004036150091385450940c407281d064070412100c01003400741c0b10200e880e0b90300404d2019840707940780b280240f2a8012a09a418514401c1010700441d01c0400c0311148100419140408000e600c0c03c07180d810000781011400090481300980c8448404824600d10951040d40649001b004a4070b41c0e0040301c0b401800b400c01c1681240710581040111850760906009642c1518080c1e2102083c03103121200c591301c0ca600030700c10814103030f1042d00e2407040c035243c0700d0a50f418104c03080095541e803410101c101040d0700300d8bc0c0c4041d0181d0302030035000180603000c006407034000c0d61124601a0441241c101300c03203e205c0004000e0f50040c0b402080342504a040c1c0d104900c60000750320343c2c00c42d0614101a141d03c81441031441a090b4202480340400244201e0456400c1c510081001501404c0303a1510341c1229440002140400e4582c814000c440408011 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 440658732 1250 440657482 440657501
    0x70905060316030905120712020f0a030c0609111c02011d0a0b070302070506030f0901050708160f140d05040b0109050915060303070501052502012304020d0c080a0204 73
    0x161585103042051102000e403624034221800c2607a2600c4e0030003000360620800011040d600d013095100c03803007800c04001c05080e20101d50701611400205111114010419110301a01512190003200e080d89507080946405107084460104010403160603582e61884500c0c50795441e0003880b85400280b0014080402e0021090400d801c2c00032040107036600c00c1090000e4078140380f81140c548000d460180d2074001c0f1500080da03c030501104020036101d4080304c41c1d101d8101c0c00024800c0d0b443c0d4503820362700d040c010f95002a41c01c0403100840e6406019a03000b40d845074461600000e501000310186c02c89821018440e021a0b4440f0240800d100701207030414007600c3c600c0c80800c001e081c00c80b0403581c0c42c00310f48000b1491120002c00a6100d540620503154410340160090000c3e107040c0d0156031040c131400c0301403155410081c1502420600c1403003806844042808401606100070307881e00240440104126807040620320000c000a04407074204000b0030300034001b4400d2180610410058031f45074175 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 440659982 1250 440658732 440658739
    0xc0703030e03010c03050108100b03030712080f060607030212031003050a080316021b010e01050f1201230a05120c1e01120b0306072f031209060405060f0a091505070905 74
    0x5008a23040071443c15590414420f0025011185c20086403c41c0074606011301484d99403854240d105412070045032080425800ca011250380b20000c00c04540a0904081c0c010b81c40f50000c48100c0c8000b000850b00301606000e14103e043c1d0720303525140b0b0150305030310440c0c003035401000b44601c500550f880c1c068010028000b505074000001100d035117180011400f18104410030072558083c1e402030044030380207003090454541d202c241c002011540038080c030881118ac29001c04e000802c0403455001e4404480040c0218600d134600420405944085a04103c02703010b10540040507079136051303003001c40b000400340e01080002e944001502064030f41800340c03615820072003212100e035404a6056402004d40c18111700e4503c40c40c41d51480031704030808a012404070104075800c000000005007510a0001c50707502c000e42e8441d900c880d200c2c5000d580003440d580c0901d0100c1c4100301c8484449900ca02e02542c00142905a5226005000c200ba07084401055a5005004500c0d5000c45044040d0805a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 440661232 1250 440659982 440659991
    0x503180f010f0305042102010b0307060302090a1403011b0c0b0702070b1207141c050c09030606130b1008010303120c050307030c0509060d32010303080402060c0703030e03010c03 78
    0x4200190401d1410b912010825a9540018040282e4601090068403c0007200c0d80300c2103490101074001c021800c55039120344520b041c0000c030f080c424000c881d01c09001038036000c4464034100481d09100d50b90703080103600d0b5407600080d00340f514030342d011602c080ba07207652207810305045400d000070201c102038055021500201c0081c403400820034100d401c24510130010106644c2ca400c8111340e040d00d001092620010002606030318240c6904590040203a8124200003545a0100002032480355101b140d030982c001d80006003040c41c244910300d5040c4000d510118510852000007603841c0b8058841c0c102107101e0000500c2030560080000c20f541c0c00c020002c12041340c0010001d01280401010b40041540710004140345521030300c103580c206003000c1c10039900c5465143c0b41c2000791442c0c1907001d841d01d8801c1a441c20010102100c1c1800108040d501c900700d03400d42d141121400f0008006070b0300108100440d600b0710a040001c480114041c0d41c41480800c40c480c100360950395551090400c140c01e2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 440662482 1250 440661232 440661259
    0x60703021e040b07290a020301082b11031209060a0e0a02010c110d0f0c090507020312060d0804030b180f0705030712020103140a0e0c0402040b0d1d010603050318 71
    0x40201d84d05a42c200c0d04039042e40d044401c0c1420800141808000c442e1254402e01000c200725802540c1030b5030341d203804e48007510400e40e40d10b807030f01100c80d0010310307220705449089070714500139004075910a00c803400f9030b4980001f22100c0003d0141c2070b00d0705505903100a0820084091074800c0e52454100c1c200030382003810054000801c100b50101e00680760950060114070251788008a078440d032503000c444040ea518290400d803d60449503c030700040142007200050000e8030100c03c82d03901c484240780c0d5211075228801480a0000084011a4a10740c104030200c0410343c190440d0f8414444105004d00003480d8151031801c001c41e6100a2460b0303806080e091096540c0130405030142c8a1307001d100d284800e0b45000490180210700c1c00c0343c0f451046d4000303001607107080ba0000d62242401100b21042c0c108000c003071100b2442640300e080040003044c0005601500750346c2000c5a45400d00c803000b075414070403c201900311901517104071869480051100d10703d41b030700400c82051510480e1640c40d01a20b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 440663732 1250 440662482 440662499
    0xb07020f030a09140913111c080705010506010e22021614070f0b0d270b0702070e0408040e04060f06080a11040603030203030103140f0d08060103240b0d0b03060703021e04 75
    0x107a0700c20003001071105420202090321740b44028812302c0b5060002c540c0404403410944229401034100340d4a0354242000100554000e100e5a4403880018140c0407080002019095045042106079851550200319005004030311035000310209020307a4052144540607a4034601d881c4455019021411403420104298082007050345c1d103460b004c0c4808603002600c1000c102c1700d40d521001d450302e14080d4903030400c240003589401911808090302210b0029480c0c03028202c02030750454004040100402090102c0000000d440f50441d114440108003288840200015a0400c0c2c00810955000d04806001e00070100c070702c000c00c14010740307003004424110744000f910792005000c00f90001503d030401018208081002c035807030000050907070f2141405041d0040080d07000380c803690b00190078031051082d6a10050310f061294004002c0820340b1030300c2c0039018552600131445010190b030303442d009060140ca0901442c3c0c420102a980140d0b109508168030419680300c00841107056004d0000b4480441c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 440664982 1250 440663732 440663761
    0x3030316111c1101020d0906062d210c03050c0a14060304030302130807120209070806010c1203140903030703061211091506073c0b07020f030a091409 66
    0x1c0c00c61800d002410519100c1d540644141084501498a0600b0703007c14000030758030282c04d0f580d8003480038401801800f40c0307040c0951480b046091403403544604000035032401c50800e510400340c0c500000c540302203898009904070701c1d510586082d044a108400c40317160600060028290340e1840c0c60701e81c0c01031400324800d40402000181030660014401102c0c00c52030328288010400002241c07007890320b421603611620341c2e80b80c081b03000320402808100100d000f070014a2180c0b0042c0d40340304480419454407054813080701410001c1c103555001084401d6140c440c000d00c01c13540d460055960f400c0181d0010f0803520260300c401a406100c0c542c3c040000d08960020110010880b0041c1945d20b9410341e51901c001c81d4000d6692140b8002020003c002c800400819076002080b040c2d055901c0c0b800c400c10740402c031914071590f80c0e01c0c0000520000749020541c29004220307403040340c070440c803c281d40910b10b0b8008a1104c0100308049410402c48041101403000c0301d500ba01c51b4005400c08451400b01d65 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 440666232 1250 440664982 440665033
    0x2030703050a05010b07170a1b080c10020f121506070605040c120c09020307050f120f060406060509011b020319120e130b04110301120c0f050603041b03020303031611 73
    0x600c00010890760080c8660422401102e0b8409c10144140d914500359080740e004024000d0a0300680401086d8150144240ca0b5080c024039052441e2501056010003d070500a02c4800f422007522030800050b1908800b40c000300e40f0170b07c000501c900b400e0411807142c00c2070764000619005114011030009041b00002c004881c5001d80150710b03038569100a881c1401928181c5500440100303100c50801c40303403480b2070301032400359402401644030a02400103517092401141c0203d103040200040b01d5100e0750415100d001039000108038000036a0002e801c0001803c0c2240102031031b04010010b201c102c110160b0360042c5030074410308028044000c01c061045810031003d9041e5903056203071060311035800456086031550f2426580c2e6031074180c019a80300b4001c0041d500310039441e01c0420505402c11420040c0e90b8010469402c640d40c540d0342042503100d000b4501302c0040c00000c00001070b201000614007450b1003000111288031511b50003001c6d50100c0d40e00500300d5108000414440100b2402004003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 440667482 1250 440666232 440666273
    0x70b0c091008090c041e0b040e0606010f110604080403030f090806040b0a020d0501080718090f0b19021810021605101404090905010507050a05040e06120102030703050a05010b07 78
    0x1666030f450191400c014090b103416401074200f0b0580122000100b901c10415506a841009090450003d00041ba204100b0218281d8003490104589601441044407514160b1916070008181140c140e4140002a10103e508940c0405c0610815030010101110041ca616040426078948160140c4d41c941c0640040c00403a20007001c1111440c0741d4048a828a031411018412560341e10219940c0701c0942c810140484201d20280c202c0501703e004003040c1680180c800f60910764180c4600f0344281001d0000d003c48480b0540c000700d48801c90014051500402c11880c56092100d014400080c0441709103004540003450740071403d0003803a03109801d40302c0c103032102d40c0070307000c2e984041d41c9070b80800200e10300c40040401c00048001e0a42c00240c801841540240202c2d2560941036486000f14520301020a070140402c0c030442c0d22940d00340e64042c6004010a07404201d0860f020b00b240e00a1b1072400009403500100f00050099004450040040c009002e2401c0c09644a5450b210500c440c400e00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 440668732 1250 440667482 440667497
    0x15080f13020d38010803040b04050f0609221b081602011d070512010228031104090905010c050f09090604060e01080f010506190909150f02070b0c0910 66
    0x307002100d01040e203000d20300349803003201e0b45880c11280103450f800008000c040d0403071400462040301c04010b42e02126040c8801c1810103043c1402c00030b000d20b01a6049401480031301642c041542c07500310703a83c5884c405072662220304180c1c1e6078a20684032049a1900c0041020b0542e11a1580c03202c603080d4010398525001c4107049418000b00e016248021812486080030b0401554a01f0003140500072228101c86841e84115203112403802c0c0d000d20b6290229141c0b1482640d1003020807180026020010b6240004002000c0021114180c02a4010411043c0d480c2c1c080410044240b05e589330403030031400d0007404c185a51030140c00c103109241c0c42c07600445c032502c0070650036210750f0090b202a080c181c070b06039829a110f405035951101340710301e1300c01d044d800c08c5c001ca010340c18800d05480074820b2034070070204d042c0d0918080e60040c01581c10103c589c030128001d4074000300824440e80541800d11720025988da20281802e80310401c001d805614129003c020780050707659541b0140c5164030040c01d1224 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 440669982 1250 440668732 440668759
    0x90308030a0b12070e0a050403020a080a020a08030a02030402190503190204090f060b01022530050d02070f0e18030d0906020a080702030703080117010f0615080f1302 73
    0x7000e480d03415003003604050364280401c0020004100b40050351681c1c1061744851b030310440303c04141c034015940a0096040501c0d4840410303814001403801042e01e0045814881641c0d40740c0609900894102600d180c1c0401400110318014200d180202c134903818145c181424070b000680c80303005651161004c04181e03030301c2404548554000e9903181d44c210200303041981c4942421005084d0001d915801130040c40001d1082c0d5070f200c0001000000b884031001980e40c2803204190030074101000c0301d10000e4420960f10f00d40c0d005c00d004540d14503c210040c0000ca000010040d01c4d184039504100b5480c0c8421909009e0019800070305a804a00d42d81200020f07070528245c24254456001c1485140d81080310303c0060100540040800f001c003035840700310766568000704076100d01071000028000780141d00100851844c4c140242110480c1303c2c000205003202179110b0084512513407004801c800c803040c041c80e0b582e40081c55194440000490b80450740382001d10b40201001840f0001d1041c859144010b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 440671232 1250 440669982 440670001
    0x1306020a0c05031b040b151206090c030408030109090c081902011103120c1810031b0c0f030315051309111f030203090712050c2119113d09030803 64
    0x310580f43c10307c02c411703a02d0f250080005865602147c03102d00801440f004100d01c0702111088070f104941124481b811a400c003d8404c001d020300440c25640071040020114039040240b0000000326603540d40d501c0c1400e8144001b401444000d04080c900d90814404c0b95003e211250300e040d03122080702c2616a56440800881104a0011000d00d800925402000d0080794156010310315404603100c143c41140403252080b545644042401043c2445144001c00024081d4000d070843e031815103523058880da140c1011038070f40c0100051a0450726100c10181c401d20403005041c050084064501c061070a14090845903407484500c0c2c001c040583c0040003594115081c030092014040030390300781c0c000315103d05215544003c4408641d1003940094003c10714160030300b840c05007401c039a00c0a0401e240d00e003110a90f000706582c805860b04625080a880e5a40d20025041c040c82100c183d610f01010740b0203009008110a04110b44402c001200d5691149402641403030071a0751100d5501da4984d61800310 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 440672482 1250 440671232 440671249
    0x50d02040905070e1009330302100201020a09090612080a021606031406031f0209010507080706090b090c090103120c020a030c080d14070206030601051306020a0c05031b040b 76
    0x751071402080c1d004940e407407211241a0182d11418a000b010941b148698022101402803030201040c02d1020090310743c2e1258003c00c0e00d03c035100004095540d5903008078003218008808040141d500203003841f54107822001101c090401e0207401c010027030528000302d150200c5210003510718070300402c15410071482003021880b074030200302010701907a99a100107800b41080c0c0000340039149201000801a060000304880c0c602c1407501c150703544c05c6501420800940c0a014594100081007080101080c0301600404110384107106c009111074243c100060303006800381c81c5080e07540124a00d0110395580e500001d0540f60014101201c1300c2c43d544043d81c03100b203030000c001d42088030b0038000414001d0b508250b00403540860705549000380301400458080001c41d40d42d403001102480030f0360140c10541c01559010310181402490075400151441d01c4070050b07400032006922244003c402c0160510b502001000c4c254010101c80f00303031800c1c45c80840c0d02c912000c2e02941d0f58a0315407140d86d803008007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 440673732 1250 440672482 440672501
    0x5090a03140c0a0b1215060c01060b09090c0703050304120e030d0f020712034506140c06062202070503030f0106020a05120f0f030108010f0b0613050d0204 68
    0x40e10034110104200752512950910907482c490b0f1070344840060100501411907844032840700c013506843d5100c4c002103485c003031a100d40c45e4100009110111151000348600006840680345040d04c0344041c1041240d40d0310b000340701180e020f605100d2880069081002c0c1c03500942e0102e012070038404800c00403207050f040d0a107040e5151040b0340d0020192a00000f807110826166421703240c46036118025000c24854503400240040d0055000440b00036491000d084141c180c21b001000001c602104841802c0c1c416414155140041408020b03c60f0480c000950065400500c28103056203926000c3d19000020801c1d40112070510110380e4005d0000d041d082e010700000001c6403104000d0a185680750022101e511030030520100115409000040140b00264024000c080c0703040d2004480c412904400e20000c030305075040c00f06074080d2101c0c002445c060049403000041e4030a40303100210980d0070200c038242c01402c0070450140341494001520081d550141c0f00d515010606101050043c0301c50039 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 440674982 1250 440673732 440673743
    0x10f020703051b1603080c010b0d0507080105150901090b0111010f2705030406140d111c0e03030105010e0303250506010b270402071a011805010b070305090a03 70
    0x30345808040d003240241241d004044a5011422112410390380ea521111101401000c81c445081000813a184002d100400713040c00045480134003a008240c500e0301c0c003d4226103d8000520600ca02d10091042641c030150083d04d0342c1d03808201c0f002282091106004440000752110a4600da99019a00f01d03580e200504008108081d00c0e10b07481c90042c00300b03c40c1c541201c82c80400c20000003030011842010550058040c524162800c0720a48410503504d40040169900344541c800462440c801c40714544140b403a45683c402d180d040410b81110000004401189010305451042500200303583c1964401c0c2011400031011100091941c0150405611302080301607180e105480c000504c00400c070300c0b0b00101e8816980760700695503903014002e010044442e511907040f43c01e000c12009542030b01d001410051918140340c0b91100e41c0720800c0c05041c1c081da4210010424031590762070710080c140f00c89000700825410030000d108144100e640c06010010302181309070899580c3e003a60030084d035100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 440676232 1250 440674982 440674987
    0x60607020d02130516090e06061b030c0714030604050c040e01060519170a0b040303050612010504031709030a0804060b0f030a0605010302031203060f0909120a051306030c050703050705010f02 84
    0x442c003c0d8003400302101c180940d00c0007101002c4025001c0d98080d01900c0503e00500901da58000c11321441e40c00c00e40c80c041074000c605000032176070340041c4028030072820408081d2541504240c200c5180070018103480c1d000707510070400c110202e03e021030311540e1400111008280f0043e216143c40c05814a608085c0e400105078203c4203a0020036044038040328240300d0b0050075820018081a103405600c08080c03c01c0240304001000070f0721039403041d0b9100c4002400d00a640d030325881d64a0842c0c1b01158100c0201c1c03014100d5020001000d1829035020110390000c52520b03070700640c02046444060402003d082d140c1c2d0b101c800315a1000ca212031551409401c940041000c1e0400e40f000d48002e00c0160700074001c44507034040c52100e40048034810031010f44a0a049142e100621450b000d0040501003203010b8088403080b0b40703801c000142210516650303850384503815005038950130030441d8411828985482421208140c00a05440300a074060410b26207030f008c00d08025001d070041e504202c1045100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 440677482 1250 440676232 440676259
    0x50703061511061b1801140708090f0f0a0306020f07060e10050106030614010c231605060309120d110f041d0910020c010609180201021c0503060607020d02 68
    0x440b0b400c004001034084620580f120400401090b1446080c01d00c8840d00700b0034180500d48882041c0c1c8841c1c810300d05122a0f04458100d030809401040b8101d43d0b80c10009a00d800b10f10300042e503000312102c1203c108070641884000503d01d400e4900c4001d0150b41c0202e64104201c02e00000d542081d40c201c1410301c070b0b400c4695508c0341c903004656541001c091500d0004142c540c402d1003400140d070780b41c0c40c0ca11805081032006482810601d202110070070848002c90013800034290302800c820800c00e0040141c4c0101013120300f11151300c3e8000303500501c004d1003082861900040c04200c4243c0c9840c04990b42da080c81d010310082e00e00b00d017070041032510008034641164116002803080340d02c000d115448201c00c0d1082980c1d24101561b46080d41e40c0140d00410051a5030740c01400b00a030054000142a50307550814020768035600e24954442a640a1036415941c05006414000181f100800d81429440078040c002e4000604907a00454021401d4001c644400710703c51030310b0b50002e0200258608 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 440678732 1250 440677482 440677487
    0x702150a0f0e120c0706030213031502090d0b1b09180910090804141906030b0a050310060501020f030304050a0f0305040321020111040806061e130905010506010e130507030615 77
    0x582c20713005452043d060300043e0390b0b1007442070b503250341220400103400b2455a254250518a00009016903d5080210000554541c000d92020900c03a106070111440c200f102d58500305d0801c1d503208030180301089545465036614000740450100341c40c115120b80c460311050f518280320821000302c018500300c9100248030020f40940110b520700c01c990001ca501a05c02d10200c400200801c7c02d071140d1a0b28107003d214020741181c40312440181a0661243d40c84000074035000404100c142a107507140810321055a0502c105004c1a00040065103103040c55540c030341c5e4034000350b2406411544441c00d41e104252040302118011504410100d078010f80c504000ba410b1006200030002543c070380088075560441002c15141216148009850195205400c3c00100c10500c01c0aa04076003888281c01030541e80d2280148001140140c0010540490f2030598212a809402d081c148005500c1d280c03c59500c501880030b444411440c0440c454450607001c0c1d0182840781c004000200c614291151f1407175 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 440679982 1250 440678732 440678737
    0x4030209060a030210030b120a0c1e0e0a020703020102130e07020c100f03110d020c0304090608191209030b090d0210050105031c090f0311090702150a0f0e12 69
    0xa00031103035811180c64100401c2008030803803100941042c9100c0682035100e000e903005a0b41c400c0d010b8200d0040343d030044c806500700303a4009030403607084285100c14400c0c180f02c0e0209040c200071703d5002046007410071810040002c0d00070001e00d4010340019585d010903200703405981078212003264404490b41c45020303920800d001195214018031900c0b081c012140f801c445529040000c035103c6c0b0f01038403041d01c0220040c01152a80030581f0404115681d1030009074402080c4c81c1341e581c809180c0341c40c1080f228038144d4549902c00c040a9000720b804d01c41100c46d40f810300c0402d0758001503061400d01c06650585492400d58405082040030500704585540081b40c0c2c1a080a115401c0e034100c1e020310100401154000e000701340d015801110b401c4030300202007004103000d50840c20b181c04c140c0e43c1d4049001c500d03411604122041140032304803003100c3c146100c06540012503070020707111905209403000b48190307000b084914a00e440c0c085502c40051158000b40c0d1098541054550f012415080b0910b240e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 440681232 1250 440679982 440679989
    0x13020c0606030115050f06071205090918150a0f050c04051503090a0f030908120910030920150301140a06140706270f02011202041a03092104 62
    0x1409603a00060091406208524040701e40b10107040d11542428240440c226242104507040803040012001003000c580822122920941d581a641c22548040c4203010f08083d100e009241100d10032141070100c045400804104500c2141c2260f54446200d5006800c8002d06009100d1503c014810703081400d0000313000b90341c026150340400e82c03112a119006407108a4081100390020100c000004800700c1125041d140203150090a45848000d698101941007000e0260000e00091442d060f0815658001c0c4680d55820108440c0481d40c445503010840094152038564040040e82d0850b038582030a00340755804817241e2034403580c5030890300e20790400c000190b43c4a500d500c0400552184030b590301d410f15480720114181003007110307074420000c0d201021011200c0045074020200a0b201c52002c41030840c09040e202c248800c0500002d030038240309040b825200c81c0104402c4c0140a2060f103880d5130302d000c40c52026560340d15049054100791080da0305811505511a11160b140d03442d40207003058 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 440682482 1250 440681232 440681257
    0x3080a08010906060c1709011707030606080f0c180105040801020f030406052a0304020f1002060f0a0216020f0312040308071202030a0f08060a18140906061507111302 73
    0x41602ca100c16030345c010400e030000b00507040062241402d503032032101404144c4010304015080c0e4100f1038071048246400ca52140001f5916903040000b20382c001141600252480039007482030400012011140c419218418159031508600c480b00d40d100e03c0c111001400c3c5a0001c54490b2194207600700181c0c015241a9042c07070804002c038a00e20a0062038260642038052994014004141d02c400035030001001a81d21182e5541e00f1049612100c20001d41410541c1c05840107140c40c9429540090024020106281c0305105403045240d0713031020403012179011100d10083d503200f0320000345050300c6450340a03d1a90041400020000d10001610215100300e0510180180c0404120b0750390181804900c0020900322109089034000d00382a42c10541c00b901d004c200c591610000c000d62036028880c2e1300c1032941e4400d880c102c0d04001c1c4580c1d0704070700b801001d00180d05003100000c601c0150100e03200d1080c5000182001004820030b08110341c048050000400102041c544c0c000940040305c8202c11f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 440683732 1250 440682482 440682491
    0x10c0201110a050a0c03050f0304210c020102060c07022106041406090a0609020d020907080901060f050609120312070f090918140c0d050d0e090702060a05060a03080a080109 76
    0xa9201e01e601900e0841c1070541c0e07810b041c400b1400f4202c400030709090041d800c0c410b0803c0189021441940114450f500640c05e46990f500030050507584108070786031280411051f588404d0050380e0100300950440e041030740513a1201007900000d4030441e210148214080c1d0030b040c044001d100301240503846140902c4e0442d001c100725400ba2616002d04603001b0401c0d42101c1c4100000440c0d540c4084009030000e0100c1081c0e580660110341c0d500b90545160b00404d81107070800103d04000d0103100003902600840c00c82540c50500850180d004400010f4030030ba5071140341f60f1810b0f50400903509440106540748089040030207000e0028441500060001142d07a0360208100c8030a0049066900700c00c82150103041d03030703a211441c8079800003803c05101e020f0355400e905a591410004201d41d4064409000c000429040c040c005240e920f40140c003d0210b4820040c090342c020030b42c20b51099441c04082803640ea440300003410451140c20040c0340c1440490611281d5902142d124184c4244000420 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 440684982 1250 440683732 440683751
    0x90c040510150c0c061407020d05071e12020913050703080c0601231002011e05060405010e0402030a0807020307030206034011030a08031e1b0414010e060a02010c0201 73
    0x81e150442488003400c0a80014410480e152242059602c0c8200c00c6c0c4050381003031030943c00900c05405200c0240c0b06a4460307072081c000030301c250751510044881d00c041d1400071403800d00410f0501c024207001074031818260000409011201c0300c5448600d500c80305850841d40c8a10300701103290880306072903400c0e2140c500040b582805105941441c0d506d291914482c0720003003010862402d6a08028004554843d12800150b20380130746201100c1407031040c040f4a0746031140500045800c142d0258050b000400b061002584020811b1107203280c00034141c0fa0344100500120303183c900964070080d048040040ac011001e038403010700200784215041d140d210b1036034029540042e60901c030403000c1c502116144000029250b1054520707030400280546501c110b81381c40b1119950011110001051421802c061803034a04007003503607100e00642c54030910301c11400c801c0910380c010350080c044103141c50b00c44c3d60240da0090340d04401c0300320000c0455070f44810041000b806044d403a40070301c01544c2407080d882c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 440686232 1250 440684982 440684987
    0xd020306010611240c0c011e0605120a020a05060717030a020904140403021c03060b0c0f0607020a1104050a0e0a030e0406050a03121b050316030813050d08090c04051015 74
    0x54920090401c2c0403000e40c4420790011300d1948207150607051990b0380e101111001260001c100741110601c03000007005888c0c2b01c10300150800308008002d19170000c01480d00140e80e450041c000741d44e01a654552202c4082c5442480280c0300343c00c180d000700f00402048140c001c550000d0030b0343c3e48169401e0000219003029042101e409980042c0940c02032014034002d101080d000e041280c0c810326010884541c0d685180341140d0022621100c55000010f0400d006030080000903004074003803004202c51076241e11403071000074080351a0380c861500d400210701100c9143d00130403c004070710701c00d656400c10706182c042c080c07414a00d241d03030003a803d101c400281840d0041403641125040002d1090100c4ca0210864640040101ca14a0f860184101030040303142040031300f0b000b03001d0b14a045096003076404c0c00340c114503004000b01c1c40c41016000510009801003288800c00c2d1032070038502c0c001d0312202c0c2c0560405d84c01c091115041407800c01000340c48180400c0b02c4048805d80c600b2850b07101c020b00303400c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 440687482 1250 440686232 440686273
    0x504061d060402031203060a1a041502030f04061803083402030a080702040917130e04021e030304053006041e080405090c0a030b04290d020306010611 66
    0x1c1e44c16004250003109541e0640025a40000010850049552505511020781681c102e40d810600000b19003030189a032030002c01d10504040c2c0c0019030400120100c0254244290f0080c0c008000c0600d031143d02880581d24141d0166500080e03d41e1114039103511104c4017503c41c040315100c10045004541a0245000002c0885030050040c4c0b0261442c1d403540541540818000c98216a641c0d21344404500d03e81c40318103203101918484c640d51503101c0d000f6035524025070010380d1048140d100b4400140e40e400c808000c0008c425805540c54541e6400180c1180500d0703000d03540140b03411420002c5203c0040103c408481070085810303441c0030120441e27640e6034045500a100032000000001079420780305000d628140b0a150051800c0c1d1560007243c10140e050700d408805c1c3c0c40216401c80225010701440da03d005080e5010050325034600703500c112202d00e00723000c0040360003510040b02c40c1c0e8641500c00c540c001d4000d0100c50065075204c500515100c8040c85015040c00703580304a00658005c1c900 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 440688732 1250 440687482 440687491
    0xd0b0105160215090306010803030f102111040606050705070906060804020909030409090803150d03020607200304030305090a0603050402030a150209100e1201020f04060509010c060504061d06 84
    0x3280070410010b5400c1c00b007080104141c1c901141030511030304846980801016001c0e19800001e0768030b9040078200b1035117200c409005011400003880c8103100300c0b001c80c0d800d16503100411036201d2902d0036905040106140790104650010308146c4041401034003c070080c045244200c080302c4a06a40307420100c101c503170798020f980015074a080440e0140c5040d00010742c2080010044d01d00d00380d039440000084a001c2401200c1c0c0100c007204010000c403412107000144401507404660700003459500a46890b401005001804000b544198803400d00d039003440d1040004c0c00440c0c1d03850f0340302d082c064055040403d5091180740d4088000c030740548030f401018010755010f0000d008124603036503018402041c0100080d042a82448040b00ba9581c0204200c0003012580300e11071340f05855001e0100d0f0300006c15207801107078010401010303801c0d459012201220914500191038041400040710001c4800201524441c2800240800d011b810781c0850200c1d0201d4103004e00d10000c1400c0d20b03850391400c0700c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 440689982 1250 440688732 440688757
    0xd0e07080708150604020f0c070303030b040f0509151518040b090d050a0c112205060609010516051207050c0a05010f0f0e040e0a0305040302040f090f030e040f0e01020d0b0105 77
    0x101207401381c1416006030074600401d20940f8107000d0320f005100d01e0511541d00580c00291140102c04103030416114000c1101c0c2d03410821b01080c0341c0f01134126904c4c4003d04030340c00110121400a405c1001c01d02005500400041c0032500040785c2d440444540380080e5425508500c2e000003090710703031500055180a102c2c0f15107a1b181403401c8201e05031065003a10805403034100c03118484400035647c20720035007107800e03414001804405c80c501b6500300b203e0f4000c203024040d000030081c1201c2e0781c0e0001d09032850303280d5945000903511110300c2e00c28100f4030303115030250720b5010218240c030411402158903460724000f560844140c070b40e61070044403040391600345800490b860246102040d40300d030140124940d0050400303c0c0030f10204082c185418488003040c0c0010f04003090502c1145071902910b41c84030340c1c2810038000c1780c98684404c2d40400c0749410007414020303048854280c0f40c80d80d03017220030310100740101004038140e50500c8a000c0c0d0701a001114070380b0300c0c21400c1034070b540c0644190b80b84000c814 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 440691232 1250 440689982 440690023
    0xe010605090412140a110105070509060d18060c020303070f020304031a0a060b04060e0118051f020a051504020f0a0b1615050c0a080903030708060409080d0e07080708 73
    0x20b480754a0382446a502082c2000102000000900304540040c41034600c2551703110046d01010902908582015015004100081080c0915580c0f21029603c040200010004404a01841c20002c207401c006009100781c0c14040000303640e64011000e0b601c50703d0365441c3c5089035040c03410100c0c0c80c2d1245010040540b012000800c455840360540140c0c00121000700140300e684404c1c0c00700c0c2c190841d40c00344000607564101e02e03a407968854070038040d0117007074442c0b403044a051074002650072400200e4810240c5038841608500d603c00c1140280711034009094860010f202c08441c034031740c0300469050340141224103085440b42403800c4d0100032115044002c2e402d140c1c98032900384800c414141d09458400c42105000c458803d580700c0d07240101c0342680d0007651503d21040240011400400500c460b810900c2000203090b0400b81c11944001c00300e90001c0e10080502e0011070070f001d407041e2004240e2405140c1e0404d000001050020f481149d0112103030305680d40d41031a0b03910030440040e00000e060 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 440692482 1250 440691232 440691241
    0x906030b09070b03130302210408010e010e0d030c0c0b040804060e1804110d080f03060f0307080703060213031b080f0109201f031a121914030417010e01060509 70
    0x806282c105c0d414880d10640d003091081c0c00c5d10a041d0700c22428100813901001408214a440901c42c271400c905080e0001d118040600700310a4540c0d084943c417205040e210500010024031510401c42c4e0035600c00011020760419007400341564006004110108840d41e244c4c5289240920710080101c0c1c1c50300e4812410303aa69990112800741c55440a0f800c402c0c100c0713119001800d244003400522448d5500c4a03102e01d401c81c01c20490403d0084a00d010b6045074600784409040400d190080d40e4111001503590000300c0405401e06400c0d9001520f03400004100d0034001380040c41080440d0174410444a5403481d110096089580ba84030041032a00c001e0401c0784a560549a12800d010b070050040c0c00c0305803440c044800d08202000e800d400a42c0d1000e000000c0a01410300070040003090321945000080a40000d90314014811292908988144000100f111004074040715891540030780341c44a40e00c10b580603a214101d41c0e50f02545d400c3c52420300d10143c051280408a07000180050010b896 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 440693732 1250 440692482 440692501
    0x1c050906090f0a05060c06040506010f0f060e03030d060b0a1215170f070e07020d0c0308010e04210302070611030c070b181605040c08011505180a0906030b09070b03 72
    0x148002c910b03007202260000044541d01c0101524804849a024046905d0b003032400c07509100c0160014081c0406625060040540c9078045100340c980e1400d21825611041d00040d10398010245a0389000c0e040c4131000c12034900441c0a00720f04601c60b15014403448102c00448141c800007504000010542401040103403425140220a009400c00faa0212580804114104603107034100d034607080030800c00e002509604215500e1008050f141c01c41081040788d400505100d0184a01c2c91103620440102c2c0a004803104044420341c6809243c003030144502d8409006500f229000391842403505d507aa003402344015080307900c60f18012a54a14105090b6074002d00c900028201c410710600562180c2d01450040010140c0c54680c41600d044640c0703040c08100c1511281d10f00502000b001800401c0038a40d100810403c12815003802500c1d210702001481e948280d03001e02682c014401c440008101225510000c1a2070241074034030b030a5501c91607000d503a6080d40c4106420350710100b001659401 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 440694982 1250 440693732 440693749
    0x10506010f0e280b0c06010909052d0d11010c030b091b040b0a092402120a020a05060112020a1203020d05130b0d1416091509050901081c05090609 64
    0x4101481c800b29208496010941200340d5048062141c1c0300062005c4409000c03ca001d00400d54000203006120301c03940c41a0b2580f03004003400040c0c4883d031220305031107000113a810f94806009012030380d5003601c40800412075000740d0503040441d442e04640061140c42406100c14450b00a8560348594450b00394080d86207071441c52956070f1560500001c101005907000070408250f1590b5001201420a040c840c04038901c4000642400b0001d04140d0320303280c02240e1411105440780549807a06400441130341820b10050006005001d00310000c6410410b11100281150082d1104501551074403804215495901009005603210614a03188607202c2c0d0000c202450a5003801c1c50307009c0d030f100040305031604155000352840b80c031907141141032140c1052240d13100414001c41191005400c4001d00703131f0803040c06000380c40301c1c1035225103601c0d0f80161003180041802401c80c41480d03a503000c2042c0c44161035036001c030080c91080380e140d0540d03100c1c034141c41c12a88000d11107850040203004001594 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 440696232 1250 440694982 440695009
    0x906022b03150801050609100e15040e010603140c120709020309160801051f05011209020f090906070f020c01050307230d0603020a05030f0d181503060305010506010f0e 74
    0x1584032100b446000031a02c0c0b42c1d400401c0408004078403824644100250b281d80100183c0785c0071080c0ca42000701da10807914290700101a03c09582010441c00c01150290420100110881d82011000020403064804100500e001c04003680c1d950400e034010000b04608401c001c8031903520015050044801c254011604210b15404890303482404c524840c0c100b00c03803640242d4060b55a217003000340300d0021031b014072088041d9040b03c03012181040d00280c00d007400035003c4000340c2e5a070740c0030780e00b1074a8004c6602c411400c001c1c180c41c040e00d08451440e564903c21030341c1500245c81d00c511080070a00000340b014010358140c4a1500316903654604035000194142242c0c1800101c002010f140245071004000074400f90b54040384260031801400f0041d101079000c540a5880052101e042c00c401044955400c082d500d80320030700c8900b46001c00400f44040e0080021812625450101650164004404c50f4440d100034085075031103d00540e000c4640303000348404500c015014209038030b41801105840c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 440697482 1250 440696232 440696237
    0x1801200727050f0712110414130e0a02011b050a02011b0c080f0f030c03120606120f071d0a050111120d06140a0f090b060d1406010906022b 61
    0x2607400e1001d01400e0b60802d842e1a01000a03000030b21001075071042c51000054800740f014402c0580e030440701c140c03170312952040760604400c58040a4080d40c0340d0130035a0b000300d080340042c00b860502e4585144c0318020043c089011410b20115241c10180415860328100d81000181c804907007030307800566142c005400c0710003800d10111060000502e81c0c089100107048400002c080d000030601c4264a0100d0364071001506a0080c401c03043d5143c00081154074040703498044500700d0325948003090f10b50050440c0800d403002d0401c00c00c011141100b20f030a100781070319030701c156240a02c190250010403484480c15000240003200340600e500175014148100302c450102c50190030040850b1800703400000c0c2c070006090302c4940820141c001d840c030a0094400488000c8401464902c200f50079422603c02c7e1903040d0b848003525a140c3e555442a110380400100c82882100008501c43c0d401c0726048030034602040760940b0101d003281c400078501c3c41d07c80032000701d83c030000c0304207020700c424500c0300412404 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 440698732 1250 440697482 440697539
    0xe0c070204231f05280303260402032505040606050c0f0c030a06090c350c030d03150305031b06150d0201030c030f0218012007 56
    0x1611140702ea007004460105201041c9000c0076034081c9411005000e52503010b210340c840070000182c55504000303c2e64102d030032042402e00760040c0c0c406156440c0010054035407091000041c950070080415244204026003030400003611444000c01d1070956002e909a032000d0038902100c2e8680d040010603658400895081d0b585c0c44000500780c43c0c0c10341192000a1010070b1003510f81d203003088020700d0540380e90041c00b684c0e070b03801011a55514560501802c8140c680008005010040d01c546004d03081c05160400103c580e007c1e441351507490340140081c0d02c410001203602c105130104048405000c0100a805025103a0b80228050080c03111400d418545600300080002c50030001020710183c11001c1b0034400031040d500c07606000e00100040300610880148410b56a200c440c0e203004142e0908001511003030705c91088005041604c1c81406152000480b845d500074800c2c20f0200c650402da032b41c4c1901c0401c80c03e0301d030080c0a50a464041d2079220307110902942600c03d90942c4041d10301801c035131 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 440699982 1250 440698732 440698747
    0x311090a0f020c01020c0c030c1005030c210105031b0112020c0304050a090c081008070501050c030903070f090b03160e060d080a0309022b06020904060807030b010510090806010e0c 79
    0x2070072070b07105596101560790700107941b000700ea07000e21200400503811400340c4540803680f4003160070a0032140e0408108071002000512146a000543e425401d40440c1c841400b02620645d5040541c28043c561203031080d40c0400c0180b0701503a01840200406944041e000030810701428041e401c5154038a24a010601001c565911600d8a40b4003c0c1480100031039901c5403e01c004e056440c02811031a45d002d0030050510804000040040440341c00b8601141c1d40e024410031941180510707080e45516004282c1c000482c40c00c034000c40da090780e403103400c100241664038040640e100c0c00c444907402c0f204000103040000a07400c1e00d129600103000383c04540c0200a60383c4495a41e4000407840001c26030380c20031401581001c400ca601040886885c105412040c1003400020000031a80100240d40002c0c00107070a48136070f0090002401d805c411601c1c4640c507482c5c012000102400340300c1c0104084806000000d01c580040011a00603002505480c1d091101d09024850000e21040c0448410003024 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 440701232 1250 440699982 440700011
    0x9130204020705031206060c0a02011d09091621021c0f1b050d0f12020f0f0a060c020616030b15190f02010506030312040c050402041508010501090311090a 68
    0x100112882500903564817503401070005050100505050700070300052094103654000002c418685a03024200413000400c0385414406000b500780b40c3c142c100001c041441050440000d107003642c1c201c0f0303400d242d100c0d586030f0384401c207120074102030b068004004d89440350143c1840c403982c002c3c691100c510780c488400039464614100305003400448401400101e00d014503c01d4402e02c40180c042240c1006011149840b500310302032403102c001e40101100300c1c01480c19030081001442070345071001501d040201d400d5107587c480400c0181540c00c2400d0a02c41131180d0300c0402c030a48500781180700305402d40c1c02c1080440042c03030007096a41c0c000c1c000c0030040c4284400640039004111103018011296280b0b458010105061500000196818102440700035607011041d124101c0c0e00e508000440e984a05000070944e81960145401510000f40412071400c000c0d02c8008841e100d8941c00b44507641c07080115051400d622001e090654500740d01e003618a0106109500701c407070342c4404110481515601c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 440702482 1250 440701232 440701237
    0x306092122060908070e131e0b0c0c10050934090204080d020a03050f0702040605060c010504021009080604060209060c1b010f030905070e04051501031109060603070e0913020402 78
    0x24102158441e5000c0148031003c10140b00a0312004000118508000c000d1401f1090700b004010000070380b848110015950000c00c0b804c4c07098101e20b0f22140350a200070607004590200349040410301400100400381d107194099140180c00d00e50042c881c3c00c0890304105018010fa05480301100c0014400c50110b4110864020143c1407010700140d40f01e01c7c0960b5070349407100b01e154a5080d5000041c01c98013082c4c00006540460307004003011943d8000a01c00680200031a411a41d880f06007c1640c428038501503020520907442600c0c400c0c110207040780c090b41c5440607403041d1002503000e10300084c00100b00703401401c00020050301e102d00304901418000d080805840c0e54042020710b520109842d9a80100e0110481086081c200070003c0580c0394039440706121700540b401d00c1c04280110301040001c04c40f201e488800385400b451156101c4c40d00d00c5840c03592036040c520614036000407070075618000b822203006180680313a180a0384150418860b0b0014014181c0007403918001c40b183c051f8446000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 440703732 1250 440702482 440702489
    0xb0906070609030806130b030a02040e07091d0708030423010309140f070b090604051009031b05032a040e160314100c1205040204060f06030b0306092122 67
    0x49144c07080c584241400410240c002c641041ca900b0f1074240f440584005c100060216010f6a0101c1c40950402000d4505070041c1c1c403580085251034042c42803c04000e46100400e4911015614041d40c1c441c1c4040d500c3c00303076008000004805440300704a0214817130400c10507030018100451168400d032602403000c4012075140610b07070802120006011000d010708400392403014201802c012036140410100e001e18000c942c010b40566002040041c00382c02850015070b80f00340031030b42c007600501031a00000042e10411740a4410802d042c0c5a495090120211000052016408015540d4104005005800040710717090050b804c903030b40c404904a1811002d14090403402a614564100352454203407a44030181c4114039001d16248400c1c0c1c01b080714507000e060110085030540303550000a0080072158040c84081c500b00e8000282150140c220600d20f4000314280d94640c1c0c0c03040805603c42d2002c030619034840081e80d860305d000c0900c90f0003411100345048a04909014031800740880f0401d183c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 440704982 1250 440703732 440703737
    0x90f030507021207080c090a0b03010e07030b100e0a02370207080c090115030b040f090312090b070c08090607030c020909070b0a05070206070c1814100b090607060903 73
    0x52981c1903052601d0051049018100100200d620307050307100740c0f909218558944108241d030081480030401e03402001180c48002c0007001043c02290142d5034460181c40111101060240080c48014004000004075003111080c00311543d103820240000b54000700c0c00d2194002c454142135030801d18919501c14915064044003401d2403100d034064a02841903001008541c0490308c03c804503120040c1590440d04500000001292201800c0e400b07800d1070310100d50801e14080007858106046e8100801301c40c002c2c4c980c0300c001030043c0c1032103040e0348003202e02804410742c0b10040303a078551040c2c0201c030020340980f0244c0d0401d410b81c800200345a01055050300083c04203413003041035180401d00075400c03038041d00052099619040c80b0441c10302543c02441d043c00030104d16503044d03490700300032145440e81c004101c409aa465111110383d080c07100480004041c07170700861300c1d0300d6001821268080c5412071034000c5158a400448050760340a0344000d030b0414424032548001450394083d911a061081c0c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 440706232 1250 440704982 440704987
    0x40311031908010f0b0c031801020f030a030510080a020a0308160b010909050d050c0705090c0d15150c02030318040617030c0c0906011e270f0e0c0f0d090f0305 70
    0x9404100021322079080031130f046078100585070640310000101c400840c1c901500e05022a03002005030b00b0202012a00c0c42c240c0000545043c0300e55150380302c80e2090005809001c1c8213620fa44486a91b0714407002e00941001d81140140301280c2c0c144098000000c3c041c1120180040650381d403c1e00740700a0f8014952980c503002d4460800009001c00790740760540d0b2615a00b0404070703c52880d0b8800441c400e06024004080210b000118164102c600003140001c0c02e01c03000b032080d081300011241c2e034450704055800d010484100e8500c103050740c0402c25001001503080a9a0b4240440c0a82e0a0441964010369450780094140c0700b01200c2c0c5200603d04015684a0781204032050810070300d6500c00f4400c440c1d6004001d2680c1c2c1040485000d00842800120085a8a6001d8816200c00c5803400d140e00807103848030354400701c83d6134004181c0c2c007010000d0031015a01c00c1c5070f401c1d000d4140c0c0c40b4420a80f09015a610700e000d41c3d009001e01010541000c107007188541c46440c43c191628800740c0006500 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 440707482 1250 440706232 440706239
    0x1b0804031d0604081b010e061e070f0b1e06060430050f0105100f03030c020d0606140102070e01030804050d0303060b1201330e12010c090509070206070804031103190801 74
    0x3210594001030900382000c2c1a61601c1f60001001441450000040c0c110481d0050b4603840030801641c403110740c0080c1c26031100590303041105001d5412101004406c0c96a04a442c0440b00080b0b00303400342c1405481d4a00702400d14150012903640340e11942d141d02c698281c40c80d40f0300031003078040700703881c1c040d80c003619040420518035825500020048000400e1543c0100042034510f100344086130740501d0070b41004121380c0300040520031412000b9044908041010881c42c2c891105405403901c245c084400c1c5a503140411f11001c1400d1002402900041c0020460781c108840d00740402031181c500082e4454860180514581088607040841210080140410030039403032110710714414100c46010240c101030002e03c91380700242c10303102005015a030314049519000d50301203542c24008001c2c407405510704001443c4c042144941382c4100000004122914000704043d4014101341c0c0d00c5503992341c0c95031002c2c1c8519402544c2150540700800c9802c000e06500042032688030f196a4486403107524 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 440708732 1250 440707482 440707513
    0x204140106051323010305040302150c0c0d1704060903090b0309010f0c030b09061003060f090207030e010503040f0f140105090106050406140a0e100803070302101b0804031d060408 79
    0x1c154104c604001304006482070a02890707414000c00700001d282c04580c543e02c91600700e040620003000201e20386800018015404809405400303030859400450306e00c01c5074040210359101d4a404240c078412080030206010031280d802071081d0701c7c06410a1030910765202c00b81c0d9820b9008580c0c4040c265034560503082c4044090140700c1c00649103150034000e0303400c001c0000b1001c20001d80994401d81c02d090900c0c1500e030007034111000600f00c404c014001660343c3c80c081750280d4408002107000a90810300219250f00a609803405241c0041803812006a10703038840e207407120840b10550b8101060010014035403030074052036100341d4101c8000701e80c0b41c0c9002c00703110a480443d041422102e034182d0b4211840d4841c1103a040071a0f4214030001d01da0344a81e5101082c206c2c00e900800c0050000007940d44c189a00015a454191200c10b8100102800c4489010200d40b0062510b00010460008a00032170303c188105100c80880100b190540c0d40303e20002600f9610a6100054a8019041202c0001c0c0c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 440709982 1250 440708732 440708767
    0xf010606081506210a051e0f10180204030210030204030803040b0702100501080a02031020070c030b01060203071502040b0912010e0d09050a1a0406180503010f0207050105060409020f0d020414010605 87
    0x80301e040b01c40e91040802211001f20b1200103140840000c1c0002c0082e0b8501d49250101006100e000482d003402101c07007c1d210069481800103030700444120040c12503e134481d01c2100c0460b6000f21403203046486556521007065000741c954011442a41700010000e142e40c8926402061094020100e8040501c1454105040c10002c02c1c080e5184c403c907488020291150555010300d00d06003d95180c4c030a14001d81d440c801500040c000c0b00c0380000100301c4a030000000c082082c043c03861000000c1141c00a41c00307030320139030082c08003c8205000c11740440c102252040102c41e40f5100100e00e011a03903810364034003820441d1010000d06c440c88204450704000102c50040d11280140c2c1c012880c584060810070722891103100c2c10400088481c4140460050080c0060a0300030001d0180350380e001c10020103500102829a0654600320201d8020310b80340c455002116409054000410020300402a20016a850690304140ca91030103509415003182d00034060a4503494154480c0301c0c103003001c072403203 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 440711232 1250 440709982 440709991
    0x204241701170a0506090718090c0b09040e1f0e061b0a11010c09090605010509011d0402090d0f0b010e0408040308030c190309050f010606081506210a05 67
    0x20106040c1580c98100d4003059041d240c0a680261500c0c20166986181c0265858041c100b4001c10701404010100415004200c402298515060108072502c0000700c40c203651000784265100300b02000992140b00180c0322142d0002d000081c11442404401e080880f44e0b0741e4840612040381420759449414800e141884100c28000c00765407805050307400f08010318030081000c0c08404611b804002d441807103087d04501d1040003d004e0301c1c5c12480098401e07183c0b8010302c03107040d04020340030403254401c00c196000307440c0595440e8800440065800c69400c2e183c4040d60f08641c00300032500413505c036036172419081131086089542d600c7d46820b0031034201106810213101092000c00b48000f007000b0740141c80551360404055540c9403205020841c00784204000c015400044103901001039030141d0062800a0082007550420301c101270354070b4200c5100b8022a000720342c0c0403001c900c00d17070041030107100d004801501440c6000c0d05240c540c420f80140d001e41c450500804002c00040381c0703150207180e401 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 440712482 1250 440711232 440711237
    0x702371202061006030b130506041b110d1e0f2003090f0904080a0f02030706050405030909010b0f070305130918140a020108040311010603021009080f0318010c15020424 74
    0x10000310900103903010040c44142c0007c1621070000c070307882c0e40d40c40d406507031001c4564445441c030042c403000c068103200c038218249886010b440319040b021806500f42155400046071010144d6045a002341c5048200e141084100190440c50448442842248292502d665402140c40f2082c0310200130030109000d5a40740254401c109020025140b0400e6039181031050410303008480455100b00d00d5070041c1180030304000e081900380001e1000100040038008420340365009540e80f54100030005115030801001c004004101c0e2002292043d00600140e110120061940342e540d194006c068404032500302c0e8100c107442c0207440c100240304814020603441100607041900705500040c1c50304070010805004d000c9400f1903024002800c1d400800035540c0201918941c2000d0305000f403114096000744d00d4248540c5550000e055800010342d13100040309040d195100d40c95000445406401c10011254803c0ea03030200c045a821500260003d400d002c20700300381c0c101c0a210b900f801c0061880c01c8100703 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 440713732 1250 440712482 440712491
    0x19030512040f1208091c0f0c0e070903031d0d0b0f07110c060304020114120108010506030c010c170c0313120605060906090103020405090a17030f070237120206100603 73
    0x40e02c040036944481c5c800c68584210380740400a22650004881d030080000004400a100b0020304145460940c2d000b121400420717540d006098810400c5400080c01081c020050f840c000344440780c0f02d0038142d01c090140300700c03e42c4d641d45002c01120241d0782d50f4107402e401da04104010340c2c84655880904000d00040603921149400f0030468400500040d04010700c01820151003500003044411103944910300f04290340e50b0300146030003000b090350068403a01410550014540c4144514281d11b9001480c429111031440d410f01015484402042c1e01d50100740020762910109080710382c001d02014000400600c0c151814008651000b000303580301e0f42c030100601c04580c50316001c4074192607059170001225124020103c0c60880c2013100185042c0c2d000c2e203003003040c020420140d8001d82c010760b52011030b130702c41800903621142c80c3c911410120000c102c02010002c800e0442049802241550b007510343c906c0e0712021a9802125030403030143c2d004500f030003481c1031410003c00040c00701c0d02d002c00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 440714982 1250 440713732 440713769
    0xf050d0513050105070311030a0c020a09060815090c030d0f03060914060d02060c03040f05040501050406120b0601090f0803031509090a0305070812041b2319030512040f 74
    0x1541007050281078100040407a2401c20140102c0a10540020304001c8039103a0381c0040c402881008a01c2049000d504003c01c0001c096080f4081c4c0810764440101400e143d040d0661109110300c40240f0180440c0b2400514420350740b0240075a8000383c685035102c0417040340c10f14014003600c0c120b5000c1c00c092031030710781040c0000180c810956000351048170303540825001400051545d0245d203800f02c180b80000900092030b0307940104d440c4c00f103d109070340500c6180c3c0d0300e80030001142c002d440b552039140440100640054039076011030742c0c8000141032135560f0540b81c41c1400d2600e80c030b0340c1085019601c000103115102d180154000c0030100300301c541420703601d002440070b038a800381c0c004010103015011a280007001040d20170b0b1105040468000e58031761415081109120040520400b060542da50740403540d10318060051100c030b41c4164803400000700745018486042441101070a120208010200004909013322545100e4400000303854070b00b0200308002e6100d656200b07854880803040d410 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 440716232 1250 440714982 440715007
    0x20403120f0815010807181503021c060303050405190306052706070f031a190e0c030606070f060b040e0304090e060402030a03050f0715021305180a0c120203040f050d05 74
    0x5030f078000502d190a00000d007030543c400340b02041c50340108154000300e11484610549c10341c05455288541100fa051100c3c801749050301b103070028040500016004c0100b03228600f000c4859004202480c0c941480d010341d40e413035a0049400c2500d40811840206251505811055444100c1140d1340b402400980c06c1180700078040340040c0550f4801d0544910030640d4103124000400780323003203010f0802c4188941c1a2042074640010313000d04a50449490003003040151074005807407103110082c1c44d691600c0f42d0390315840400301031564101ca03600d031224042852502c80d4020b1141030f01804000355129421304011030281ca015a18000456205000f0000035035030018803007041c15018104641d070381c850313840b400500d40302e1000c0207890141943c4603144100c4586d401494014912800122104e40341d90800404d00584008540600300d6640070643c055000d50201c070382c4076424148080350544001d80e82060b40c00403507081d02c0300c9012660f21402e11106001a280a5038a803820a29108021112 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 440717482 1250 440716232 440716247
    0x30506010603111318060f030b0a05010b031605130302042c030c060f040f0210170115020a120216030609021c0506010e150925050f040e0a020403120f081501 69
    0x2444400c0e845e001080081282c3d0344e010714050f045841080210949906082c01d14103400c0ea02c0c11a0309181100000d20740040d001500c4c081d074901c2c1d41125400d000010201d0b1241c00803103401184207114100080140d0725842031821140765400f40e500346030b40e840c0c204010580013802c02910fa800404c04510340c10b40114150b9449183d0310340d522000c0e00c543c14030402000704d400740250400080c06000500c83c0e001000440180243c0541c920f287ea00c03442e038440d0944c85c030452080541e21001452002600c0110f84050300c99461045450240d004c562201d20f51440740e2064034180d5459a0b4003055081c00c48104525561550000c45031211540d03c042e83c1c1c080501c98034400407038507008143da00012a0340c10800103001000c203c0070f420011400d06062440d403c050f00f003000e0310458002c100740218190b81e44014144030181c2420325040c00008425401442c44103520f17400c0102000082c04c840c1c00c0c3c0d81c00703612540e0b030720103030614040040d0044202800100c0c0150719030144108680e0301548 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 440718732 1250 440717482 440717489
    0x8010c05070b0a06030203030a05030a15120303020a030b130b01020105060f01050301031704030f06060e280f06051c0b0106030203150d14010f0e0d09140d080f040305060106031113 79
    0x112507901e03551015624000d01132a00001c1d8540000036100d0520780d400005140202107881307081026081034050201501c05ea4801c020320460000c072030b940400d0090740034210f17072421401c000c50a00e07580b600064424054501c06902942c1c2c8100c4c0204650f824801d440d802074055400040c509010340c0041c0c044e01051000a20040b400344209106222034800d490080d980030120f5030b034014403403a21342c01a21050040070510000d01c1c00060031590800c00e51091000c44152504c400c00b403c4038518054888603d02c0d40c000c03526203c0010f595219022030f03424805c01803040160129582c601044854410b03440401058018000e228207075104103008070144504071110746c00c059040c1743c102c1095040144401855107091400044802982c00c00035140410805071640c4801c24507080e941ca000034080c2481e8140d00c2e6104031204d0600882e880c10f00342c01000030740c0c1801c03622180220070b54001d8004031860340204004018030794040c0074a28801204000c5181800c002e8805010b20040610 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 440719982 1250 440718732 440718743
    0x601030210090f0b030a0e0604030e011d06120708060102030304032a0f050607140a02060a0e0a020a170706050a080a090204181a0708010521241008010c0507 69
    0x2140c1c62a9015030740700401040c03007051140885a807408050819041262103441c2c0606242014140e58408103480b0300c616450b0b00e809100390303040401114500356491544400b00d1400c1c00c4031405540304400380005000c1440c1d402c20520b4600c05c010321511015020f18195403041c030906c07002070f41110010b20b04030010b8089a58810595540d050400c4000c0e50141140c203170014820b00b48400815600c0c0300303031340e03d4491010982d40f14421041901c584000000103802441c049524080c243d0007054101041d401202c40c030b06003e070006402409558010090a40302d031004001042050041d07800a0465042c41401d040c0b2400000d011240b009098460a55450600c201155159486000795842807810924144038901d4091b98900f082d0900c4500e5a01c1d050001d1882c900c0755614038140d610107041d80c100340503110b8003d0814104034030384074140c0c0140c02002ca001c0940a1590003907a2418051102c1130800d00c098103180102074000851507414124644580c0790010206c50040ba8003d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 440721232 1250 440719982 440719999
    0x1206041203020c030906040303031d0d0909021303060c0c050d08010b0a0e0111010f1a06070206040b030901180c1701290619030617010501030201020d0c03050d061710050906010302 79
    0x3d11141d400c0d48a031022441d40254081400f0003803690591040300c20f881030000d015500d000003070751a80e4800d208200500058161041800240380340c1c3c001d00f001115030a010054942c51303645402c02d45560039200c100046895217034a091200400c84d820740342c8107600f018142c0d9410035880c249a8441c004021081c840f9030a9040b00303503481202401d08510a800003000840c1586080300050400c450300c40c072292590444c42d000c5450414100c907585a4002d2215251605e0400d40000582000300004115560340400c40900345010502c1030295104107040003400c0d00302105c0e04034091004109044a0b89013002086003090f06009041c02e00d443c20040b01c03110140840021070320321038140340700340d00114140166125601504504240e40b214503000380440400030701c4c07a08030b520910010380181e000020080000703024800607a040c3c3d0092400e503141c000e40300042025202d15903c440e104016030101c1c01030310326091100e4802d07400f00c140c0c02d001c1814a6201c5640d01d8006001c060301c1001c40 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 440722482 1250 440721232 440721247
    0x11121302012a020907030c03060503030415030506060f07050105071403060306011a0409020c010f0608030f0307180b03270309090f060301061806060906090521010b030a050c120604120302 82
    0x1190710802c8168001c0074070440c2c0c5050300c401809419208000ca001c282481c4004c500343c900402510306990071900354180201d80303890201c0c0a02800f40c0f0842c1c00034010130030f080d5040d9241d401450005d004000120303160600700301c0100b00d528899a00d41340064240b050040c0c0d5580494041c1c110b4584d460030961303c104901c10001c00e441a507110f040d03483e00c000740c030f1504a4019045651452180442081060b03a2006880c1d141e218001402072081c0e4204002280c01e80951030480c2709404140c600403903036482704025072541e413041d07404007024603c04d10310340003140c9211203a003491a40c0d24042c50408803840301081403040d000e80030201c6032481c4000140251000d5104400400949000a07080081e500314100280028054540002e070740c3c08000c40d032940603000c03020032102c015001c916614480c0d441e00c00e40001ca03c962007940c2d52220244041980c0c02c0003981c050130300600107051000b41002c1001000319180040c00d00d181c03c124104004190104106003000c1c0040c01e01503610102d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 440723732 1250 440722482 440722547
    0x15010506071103030d0216060b0d050304030b070207181b090b040302060903010902031518030406090b070c0806090115140102070e040503071704051206010b030604090201121112130201 81
    0xb600e1702d0640080c130120342c03200350f81030b1a0103240601d800b520302000201800014014100c0208030050400e0380200030805c001001e40001d6a849021881910b504a85440a0240080300d04004e501401e0701e88840024030015035800560401c42400c02116823441c20210740c1444c0101d200c00f0380303d94030110712141c070341c0c90079041181c40560040a0305c03c00d46c0b5081100700c82000c1a1026220654181c4594602110000889003521880c1d141d5140f2140340400e030280c642d00810044958400b581000900c48400b0820140250281c00011560560201c80b140108400d0f80c80961350700c0300c2003000852030346c0100f0080705854964040020307d50340c40c10321030314501c1001c00c010039181294101b010000304200140054400440d03034500c039000441c0f21140d4a14003801110340462040012450340d281c541e10680c5480c0c03040c11b148100081243d0354104690b048294881003d4000501001d24900700c20240da0004601c5142c280c1204a500001c080900c0102400f4a00c3c007400302007818000d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 440724982 1250 440723732 440723737
    0x51306050603040c06140c1005092406040b3a0f030507030f0315050108060310140105030c0109060e0105030a091509031b0305030610091806081501050607110303 71
    0x3000340c61a60380e03003454500580300c0041d0788245d40009041c85400d140044410088481c191500c000501315800380d03090840041101410200d003602c6544600c09112800070790a040d540820020226a4644601030209441d15820100d01c80c01c1c1e1809800481141f69008504951044078108102e002d200404d86d00825003a17000741848000c3d03080c85080651080003040038910940d51882512002c84064064a280f210711608041c0b80590901003944a1402d0aa1028005040750002c1c501c000100d401c0700c0f180381a00c850508214010b10413402c01b00002c0117081d60072700e0f0929000c5d01e849002000400c201f880ca504102d400804030310700345442d400c4110704c0e542041c115404103000d0b2440b980102046041140031448c070070f030303160224665603404689654150312140d1556594000b00000c0f40421103051084c8004001c010905201c0c844000000060301180002c00a084c03654a900d80920040648500c0844100602880c0c80390f4007940c001541c010104501c00c8040c0000a0450 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 440726232 1250 440724982 440724989
    0x180a03020d0c06030f0b0607020f1f020a0b0106050c06011a040e0a020d0e030306130209031504240b0a090e0705030d200615120a0c0b0304050c19051306 67
    0x1081c1000c000340010980e610703085036034035102041800051107184c000e4416204095610542c18044a405030414100741008108014106240d5000181008d00c2c1220070004035001644201c2d01c0d00100400410b94134050030960402d41d003003800c48148160f40e1340c014000e0300304040c550010f6503400316000081c1e80c09020710041422840c90101c070900d0003034121240030b0104a0400348980174400703000c42140d0080c40702a260b0352285a10071490806580600d00c41c94052080360b40d5180015803d8ac0900d000d00c0c0704400051081c81200740c40700c1e000d80007201002d203003440c0511000c1c0329a90070b4082c0e000c42c0c40200010030708403500c00a10341001c03003c1d40840e4140c00f5400c005030b060395011424442081207503030041e655420550b034860755403c080700c14104c60030b024100c00303029203080f125109045c007070002281c0c69040740341e8504400801690020080382004024041000818400c00c00700c02e00c1561946842c0006d4011000c10380c01511406000d081c0284406081e407540e9044103014 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 440727482 1250 440726232 440726239
    0x30f0a14040e010303050c1e0705150c010515131803080403030f0f2304050303010608040203120f09101110020d02130b040512030a17180a11040b01090b180a0302 71
    0x50340c0e590170060000d5201c0104001e06005807000c0400c0d1075154100e07120103000b00070051081c51304210500c1b40140312001c031b01c10004001d000d0941440406d019091040949418112004101006219604164080d44484181048100d024140048d01050ba4942c2c05150403240d1361074500b019001040440001c11015081042c1200114025000b14000550f26a071220302204a030f0b80d0b2441d450790070384004000303400c100010855240302e080d04641140c00202520342c8016010f101c07900035030004d4a0641020008038a40c6544c1c505100411b0402c112803d020360080c0001c0442c648030b80b603a03a550340120350301142072848040d842d81580c866013900c0c8140703440c00c2e889102c142c0c4203400034030a00e441040743d80c5041172400000300541c0d03202c0c9000d80f41c400c4010704004d804410a00002c0c1001c100141c072034101c0c807600b2420400003030396074040d0207540c4103903840300d09100541d054000d9903414004c07107083c20030807100301d441102c5c12a52403846ca103c03482c80e03090001e8031220345644040d50 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 440728732 1250 440727482 440727509
    0x40209030a1109010801060b0d11160b070813020904030c03050d0c051209010b010c0807060b0607080316020d1d0a1e090507030b0105180f0604080a1103030f0a1404 72
    0x100080001a050b41d4042141c0011003aa03031203068500342c4100340500b4603031304428481910140c3c440d800c045050341240c003600382480385120b8010816842e000d81596000b1a141c1440b44140d007000c030440c4c210440940c4655803d9060300812800070000d0001000c00020030712030170926200d1400c1c4e42c20755525880600602c5043e030030050543c2c03c0315103140348a109c400c01003904000305100750304071071106848041400031130b6154000c0d02d4010000a40d452900c0d6181c2020b41e0341c40034002d116103813041c0290303a103a00b040610703000b17440c0c24800d080301954800f02c1e4103400c06420408010022902124480740e02802038003103000e02c0c041e41d00101e0101010010900031002050781e1f9000e0310301041c004c2141e0740c1ca406045007036941401845000c01c00401c4020f41c2440b00c2e40c03d8080c2200094000d101134081100480c4003544964011500e94210074001c900700f0080103074460602030b08800850606031141c10560441c8a40d242503000c0c40b100c2082c600c0b01c55442c200ba03a00400081c1030050 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 440729982 1250 440728732 440728753
    0x501051b0d021f141306020705030d1b030501031502090d0501231e0a0905030c1b040b1e1908010203070e010801080d09140f0613060207060804080d0b04020903 70
    0xe6440f0a01400e620b4082143d80202c032603410148035250121340800c41c07080503510f0740d45806103903070001e44003511503540801c42d038404a031042000f03000311680128001489014011061450200012403104140c1080010800f0800047c5041c80701d812065006940e11103190000d5044001c8100040c119401c001d14401f5a0b400c2c000310300c1a1105800160701156a910740110030440980898820100300201040c4c0c001903e902c04900c3d10310860071030745441280c0030140d280412a074171078014000500081d04450802c1e0250861000c025201740c440842e1940020941c1c51650340c0070ba000300404080c003868449080038050040034010001c41d601d0402070300042c200001c3c0d03550540854880800020b62660002c0c03c1d0304000856500c251485003046512541d112840c0c15880d44401000b0004d50342d56108002041044c0e000b800650740a8a04603002e42015125403110003403041e00d42c200700106000d4021103140e07400c0700320000369000301c00000030024003030a0700403501407050700e81c1c68 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 440731232 1250 440729982 440729987
    0x3120108070504110a0f0f0c050f16090b01080a0c05070b010303050c0c0a0b0d05040c1701050f0903071e0213021209070902091810080307080307180f0501051b0d 71
    0x4900b601d00079182401812106280ca02080c841c40c810307800040c0710840301100251103220740c4004c12401e4504440071603691b03101d05280c0f4481c80070041e070681000180c0e99500945040700c00061180e0a003d00c60608284000ba10b140002000030a010303445802c2902140e2041e000c94103003a51108042e106940c603820002e129401400c2c0e00030261181e00c01107201880c00702100400c440101035141d2410004045031406080c02500c00c4400e07411820010a0310321039500e00c02070a03210400001040e140181000130b400c18040c100041d00d40041181c140400c41801c90618000d90321103507429960b0711880072462000104c0d00345540184041001841d080200401d80e01070440f8104945107207403600c1240c0224460050181e5201d05d403000800b00c03d003c1c0b0414154405007070090030303100c3c07070366070300c0385400c503030201c00101c44081e0f00208100740306402902c400308895000710500c14207410840541044015401107506021012400d61405c0050000381d8a00c00341030402c0d611500100e1802 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 440732482 1250 440731232 440731243
    0x50114030a0905031b12070c1403010f1d0106170c0613050901030f030305070824120613051207020604090509010e0f061605070503041a16050714060703081803120108 73
    0x31034100d000c0c100741b00c0e0095554006036110150400e004e400c0f403e2400ca6840300ca200c46906440e050f5484241c000f58082140c443c00003a0881408504002c10b229161542103401a0b040814005050312907088040c2c1d0001e1003603103615050380c1c035698840c9458602b011001c090b078000f0758410031080c008030400074070300000c1c01c0c142d110f03440074040b5841d501020381e01103078100c1d0000744840321054841e05030031100454146002016103155035030900c44841c00c0c18004200c1d10200040c8102c0b08000420404000c240c4070100300c2440603003810ba580e400106248500d1207411401078650001c203111034020b6000700350020800045495020007002d0b9036466410480d4181c000072031485044039198001d000f00c403442540b08024524007404c000503e4400300d10b03041c1141c081c1d00284010302040103102c40040c0803e02807402400c691b8a0552b21400440304080480c0c012401401400b000030b8104c01c032203400034191480020b400d40c80c5046149907020b08003407400c24080300c40c000a0a001c0100c0c2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 440733732 1250 440732482 440732527
    0x60a0e07120f0506101b0512120106050c030f0a030e0a050105040c06021f09031403100e060f0904030e060c0a08130603060503100b0d0602030103080a0e0a050114030a090503 76
    0x3040c08101c2c040d4010702c08a580490f0703041d820030000700400c4ca0342407082154031854900341c101d01e41c41c421030740c950b60300c0d100070b500240d4114540040c20000021410910a004040901d40a4680f040c03640741192a4000c10700c40508c410004280d00c0e00d1940242c00c08660102d003001154000300190400a0282c08140d800380c4100a60074400718645101003110707020040b40707600140e0b41a00c1d000014004003585642a802c01462400034840721526000a600600302ca000c0c0d0352246003042c100f528140b10290000d8891840b9540709901a200d8000c0181d0190305401c00140c51140030000c128075119040950b54540145c1c5c1c5003000701300d4100042c0c8002c007003a01910359096102c590540490b105801a41d034946e20110000125044c10f82011180f03102c0580100c40f0355140d59543c8007030380c000781c0085840c01350214620300c0c0140d0060708600c0e042022280040b0123464880082d10b0f58041859440c46080004002071100c00b560b00494092a0300c00c6c21a070381c5524148041e01005440320 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 440734982 1250 440733732 440733767
    0x14060709030b1e0c0d1b091205070f0b120703060303090b0924040e0f01030f300809060604050f1602030f0304030e03070b0c071202040b130f0617060609060a0e07 71
    0x100c40b1208440418103010031405d039107c03486044e0a16021050b90150820211143d205201011843c880c40441c030700002c0c49002c089a880d61001c0000c1d1a4140009041408240c60b20320100082603008411034115012009000d0761501070802046202685000044910030140031410361400b4a400038412070340c0d50480f19890351104e01c03072845006403e1002601100d5100b0000e0041060181c40350b515050315089082841c4101e5466102d4070305003140080412052001c01c00384400520601313900040031103003000103151078600d000c0d207160302034080443e0a0580300300c03c0040c0d0081013298902c42078644000d0700d030314040c41c0040102c5415081103029001e114000241c4040300c0d000e40f994410b005010304405802c012002c00c200450000c26640a0b8662401d00c50b00c1d00c070181c4142c961aa825800318100c01c03070212080c04e4554641c0302c44e05500c00e0b001c880c4100d8030041030142d081a4212400c99054031840005402400c584d00007a1200f8001c206020703240b07402c103404250041d18007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 440736232 1250 440734982 440734991
    0x1107230d0212070809031f231303050a020309060d020304060e06040309090525020607020105060a08150714040824070819061e0314060709030b1e0c0d 66
    0x1404200e8036a02505000e506001c4140100301c00034044c84040d0282030303000f40485901c4404000d034003d0301040101c09901007955907a48040c070382402c049109a00040700e14900341400c02020005c0c500400c000f000e000c02a000c0f89003184584284126551500b000b042e15807909079000e030240095005a6044604904c0d2040365059400302041461059406488030a4410b10305400400a8000140301c02c0108850303100403030480c142860040e403c8055540140700e9031a2400e0047d00b15000a8001031003080103550800075000700007440034415004581c400819203507114140c44141d5210034202c0d5140c80800d001ca07044400244000b8603c40081c285031408003052490110800145e51042c0011810800100072040c1900c845603150702012000420540d60301c42c000c411029070780d034204810b040c00020418444201200ca405400c86009440c50303050641d03015040344c10a1000824a1125030005001e0389080104400c04828040000902e40f400082003901c03035021070031014403107142 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 440737482 1250 440736232 440736253
    0xc030106080c130c09050d03020a0309270e0109080a0f09050103050402060921030309010c09080102190f0c05030d0c0314060a090e250509090606060706110723 70
    0xd03a60444032000b42403044034852205031003028004c1c0d0009001072051004001840c0c0c0c07541102884218000d80c00f504416000e444c00512140b9a5404422840100a40c103218a5900400120680c0804000003410b0b01c1d0f60481502401b0440009098000302052441000c1c0c0c000207540300e94421503440d080d60740d0703c030001901100c07809d440294003d101480000641d051004140700f205030140405042d96581c54100c9145d07a004540e401b601d40d4403101c9c601406500b103000e14003c0c1982c2c80080d8100b607099a581e4403501c19014006081104468005200600882031078078856000b5007505d036a240b0307015000001d0f11141c16080c0019260055403003421000200c7d00340161030092141d5002841c1141d00b401928680c208207400e80100403c1c0600049850600480c402c151400d18031813134581410042c4528004008500d15088802040901e9481c41d003110003180e486000010107a035410300a91072030041100003030040701d007c40908444d0500c0486200c4049111040b40c010460 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 440738732 1250 440737482 440737499
    0x5030714160803090f0102031b0304060e0105161b031a011502010b0a03030e0a0f030501050103030e030712080d02040e0a0608010b120303061c05070321080609040f0c0b0c0c030106 79
    0x1070078810340c1c02941013804010114645610760304603d5205204403402c14082405407010007001040c0c1841980c40020100708054100040b82c00045013401d109041c4030904180c0c0e40b421440c828014540e005204080c0040d0000300b00001c091a0015025241003100d0b0482400914081c0242c540c103002da00c0101c1e0b0241d20502400c2c11441c0013800c0307540d40301d141d40c0d01070311904207132100300391301400008000c00c615102407030000046008030004207855146040103003480c088001c03081c2c02b83d0480002403141e010000d41d01000a0740c01705000f1380d18080c1075907407002401503030062071001511509016045000f034014030199a5000c1c0200f02d444c18200420102d0b50382c1c1c01c4540c0907600700b440080e40d546401d20240f00d1a0200f0300034072011540c169286414488650800c44082c611406444600c054035140130204100b242840092824601c0000d1034404006000410340400c000043c7e00308100c1c6402c20004040c919070040c1c41c0c01003c80c116465211403080c071402036280035000204d044 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 440739982 1250 440738732 440738773
    0xb030105010e040f030f0207090f090b0c163201050411060307120207060b0405160305160905040e0106050405090a1718010c110d0305040503190b0a0b0d05030714 71
    0x1075001c10b003140c4c4180b85035401d0362a4004a841d080550089290001e000c0711140202c942001d00e14400103075040451500c80c509601c05041c9022002c010b03c001841603403c40604c103a01c40e048049100e81764400c83e9040ca54070700b0340302c4040341e5807895012080e058105401160089109009604082c1806000c2c072403540021101c0c140003070b0402c90a100409a1a0300600d4042e000c1c5002086480380900458240c1d582034480e8805d030034000445540c00d40c3e0500c41c0030340243d040d20303440b101201130b02402071203040c0b44d000300e0784556903603010f1480030b10096008000070100500300b40144c0c9400540a42c44440c80d1006a070b498481074000d114159880e421900d50041e03503044c080d003c4006800464400384d841c20b088521600d403080c1c2c20750f207a844c2918103200511950303481d552a81060203160400a000f082e01440c61041d102a00005001c0910705a20580c0c007000050907825880000303548181240307010b06a03000000d01a03090245102659200450481c2100c00c80d03c5051140c400b502c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 440741232 1250 440739982 440739991
    0x6020702150c2104060e0d0c0305031e090306191b03020a0f020303160f1403010b0d0f020703020d03200c0d1803050703022e020709060501031103130201051204060b030105010e 77
    0x2804c0005100ba5400780d01440c07a010b0014212108000305540c88100d043c4680e003007030310a40e1001c9191800d4030178410202c40095001c03112242030000542c04070703540344405050001810340300d5480c112540d030168400140c0820101440c42441d0f2001000350080d80301042d40c1d030005400301d807104405800001140d0095808525100001c0d4164404450b0507a10342400010400613441d420801a80100035601924900d44120340e1442c00c003466404803030410f08095200e900612140b00400d401256075400da40403810007040301c00c06003080105251483e12040100300000c9903024510780300103140754042615840c0c04002e8214100c40a51700d03809440001c005900090051006041141c0003c05100103040b80c2640c200c5a040007513400907080340b0030300069204140c00c00c1801c55600a00b4001c0500303007070030082c8a5203034446064a10000304920042e0301800c12490071644a0b004542d12000b00c2d61400c0304508052405030b02400900041c248070350b00344000800c1440e40f210100d4000c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 440742482 1250 440741232 440741293
    0x2703121c110f0a030608121c020703051c0c1b0308070c0c05040c020c1809030d15090603030507061116030315031205040f08060c070201030903090812130f1505030406020702150c 78
    0x1803240323400c0c004003950000720100c0401c5010f00056071485090302c0304480407041d4070000302e85c00960709002000d83c0b001c58002400301000440d07030700101381c2001c20380340c126129240103605202c05041c45a0101d0281d44038603000b500e0811210701e07941d404a03098000d9141154924295030f01c0400d5000c2c42c510a44a44199820801c491084401c069102c2c8081060504143ca101c1780e0302e050027403c582d000e51058012640c0000d40300100001c0e4480d8031007070142c0e002d0007800c00d00411944014000d9a20008082c5030361180e8800303841d02606c61450080d0b610102040040c20814001404c50f00203200d2004610044500400c40040110b040391240c1c481118450402195800450162604080540911074611004101c054052200e40ca00e1b4032000072844e9030304560811782080e141e2503480203140070709448041c040700303104c091620704422903840c240c0d4490f116403c26900901c13a1040095025113501558681c0b608a90003608101c151700044d15219017491081d8185150301c0440483d4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 440743732 1250 440742482 440742517
    0x90b0109180e010203040606080d020f190f0803091c0504122307060305090c0f03070303050a090e0411010807031a10052703121c110f0a03060812 64
    0x110541d11024812a2404980031881c08111a6450708a034020b54068030740684030308041c00400420041c0e080d0100e241c0c401000100b00d0390340ea180e100d0f0944008005048030702890304040c4411074100d1748069811021082d41c0e81403120016560f02070000105c500c0500a5403101c010034050815a01114921410540480c0d2141c2d00d14504010703002d1201c0318541482102c100d000c0c0c040018802521144d00c00080798181907200c985008151001d0510a00e8500c1c40300019840c003290352003c895060410b81c0e16078154100030780f544031143d0403540700200a102000284002c803c03501900d0344080c1c075408004c0d21020303011030549500c001c54582d0264210301b49a1103061918400b10a40301c2d44c0342c89070400241500b0703a40045003045240403480381004540c1228a400c1c007118000890b08004949000c1403030b03000e81035561480740d1403d0075555407007410002c140d044c0c0455804c3c10003035039004c0d0750b0014528042c0c02008280110b44191041c410383d01311042c0004110380444124030400c29 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 440744982 1250 440743732 440743739
    0xe070e0d060e01020705010b0109080d0e0d0f14060a110301140d060e0304091a010201050105130203070c0212061504060605070204150506030c070b0603010c0e1c050f03040f090b0109 80
    0xc10054203031411a4055034038070050314400028800f4010291162001042940c06900014800c54035504600d145400c08124000d41c5900540c2210070023400395051411905e0905260080f09900b8034050069031011600c12054a00030070090301c11039108038204038038248000c00d1551400700340100c040244107a020510b80b8500807100c003560740d200348070100d810091290349500b5500a540000d80c0319498400200207003054a01d1250741503001c2c4001c01c505e40c0761200003101440f0450543c19100c1d400001724403420304c0f9a10540d030701038001c0c010700a0f40d1403100200d5034420b000c070703051800540020b100740d010b031400f40244001c58a00e81e80e200e080140d00d0b0204401040c6140510601016010380060030343c44400103107106204004215880d00514103051183c484024640c61299140003000c10386590406d4581c00000b10aa5100c291000c0140c10600424140180502944180c0b6150f00c2040e2000000700261094094140c0ba059a40c4600c4406d03204c94250542c0441e0b074100b41030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 440746232 1250 440744982 440744989
    0x1a0304030c0b040f0804080703060e010b0901030f110a170613082a100c0206070c03140903010b040509061815010611070f0308030609010e0f0f070c1b030b010e070e 72
    0xc2d81c03c02e00814040300d0042496444e026190322950103c441504040001c000748011841800f525401880090203000302c60310010b03106000500005052075031007000f03182404880c0b280c0d084800f4025020170103464455481d01100d41d5100d840264a105110010758452000340070101190303804010a410001c540c050044c2c905000b81d0383d03500d95101ca4814180010741004480900f1074262000101c140a00030004e041030001859401403103000e84422000036400810030411381d2011040035156003e200000e8003400f52140a40d030703c641004180803d081e00810356038001c0f0b04100460185050105285842e0010500b100b0300c0c103201c890040224900640000c00511003920541d000c490315188040c003039041c0d981050350001c0300031007002010704201d0791140c050000351022003034520b00040d0b451007442c0c0080c18185200ca21b140072842641c09000e081d001c41c4c2c1c1c449408981b810281c1c03205d1305080b60390310040e9034036800a13000040c1c60354070341a20345c095281551119910361405050 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 440747482 1250 440746232 440746253
    0x1e0c0b0d0902090f0406051602030a120e250911030c0c0c0d14010c050f07030c031407050a020306010e09031206010c120e09010902090a0608060402040806101a0304030c 74
    0x5911603150070001c00141d4a00d440148a1202820b60100c603041c141441c20440744002e0021b4028150b4908584003d50000300b40c4020409030704c0d151650962080c10070380545801000881c4501c903103d10300204444101f4441d44400b40e01000019841d0307a164071205440e01d501140c15074440420200303d0845d019802030502404040c102d804140381c9101140c40305e1440c9500360b1700907a00607058802040c00b8010607101103110b15101d802c0c103080c0342000006200d594002014004040c03900001c00d8060712403070303400d0701c2d0310381409072503c150b4208180c44442440d030480c40390003040c2c00450b50850841c01c140c05405403100450514010b08107a800602001d00986e061054441e1000002000d019100c1002c0c2d04658954181404004c00d0001c4840c1c10303003064281c940184043c00b582d4980071a0201101c030949468103440c5c035200b003c5002840346810841150045004111003900d48410746800c071103e0040503030404a080021319030b41d0005440090020300f0703103051200450201d111 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 440748732 1250 440747482 440747497
    0xf060a0e031e0a0b01090b011e0e0a0902040504061d0f1b0f0702040507020c061e040302060a030204030510020c0c06030a0f0e0714010224090f0a06091e0c0b 69
    0x2102e50030200340c1e00202501c100860b55040c1944021400c40030882c070034441e2801460742050501c5000c0e4100e0003e45011040c148540060011403038074010b1a10400f4070301c4651901404882d81c00340c83d13602030b41c065071050007560f004505020000505102c11001c045040151050003000e580740d1110452480e50301501c900404507e08410800c2d0341e1b4100c0080561840b20880c40d41c0d2803011384140025208014400025900b00340e02100642d03d4101c201d4030210800c0c01021401c0c200503d40c0c000c14001ca0300301a40090000c82d1480f88030350182c0c02803003643d000f10102c44084079090b00a206912601c0480f5145030023014074403c46061020142d50000c000c00d6022410301c0084145400301c551403034030384403147d20080080210450000c04100c0304442031010b0602034600c544006d41c45801c0c3c0c18441055811900020109030f002e020294400c640e820540300109614101840500790401003038940d0704000b2030325000f907441c0f0000e80002d158803041c211141c51524586481e150071455 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 440749982 1250 440748732 440748739
    0x1050c0f060f1b070510020901031103040c0303080916140409061a01030f090302031902150106050a02060703180201080c2104050c013009060204150e0f060a0e 70
    0x1800208140303001e200c698401c11500a0440301c03440c0c814200210f000c41549002c18905003004103001085000c40c0038480384a01000143c2e5400f0000e004a0060128807181107404038040b003408100540daa4205044134041d644a00840d114082c245481c0d2101e4102d03841c001010410412141c00840c00c00030350b1040080002568408507180d20b81075039011140c44c8170304004004400410b41c0c05124000e01304082c3d0204002d4803429980c00782d83c0b031052002a20001440d032540d200200d01c20031420009115500800660756516113010b031858024901c0e201c0540113410018480c07601c1b911030480c07040c480543d58541c402d066001036802140c040c00c461325906080020b0318281c4c2d030003110060303041001030720a04107250034245607050004aa001c28104882ea00c0120542840c4c5952510300d4a00d9444c2d800c205501041044003c282004004043d0350000c03c00007410700b10401e441540d804241c5030020f164840c0c2c0104044980800c00700d81d40007605006160207944224105007010030040e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 440751232 1250 440749982 440749993
    0xf021006150f090b180d0501110a02070510050301150c1407050f0f06040e13150b090928060204050d0615090b06120402030a0c03030809070803040f0501050c 69
    0x28000001038414580004804680c1094032084080d40148154048010340c98001812828030b0854800c0d44a60321136501108844906a00030350358900c0c1a1001c40d0f446002004501c01200000440d50003031031044025014002001a85003484006c41c844040c5a0b6112882c45e0309003403070b80c042900404600020080c13014548000030350060090200b05036040c0040c22036616000400089007100f078881030040100c100c00590341e80724a800d40c2c0641e10010043c070320554940300307400d0008400e2440542101d450700c1c000c0713403101e2403984034440e50f60080da0740f82c442c1d540318196140d83e00e00580c021002586444e120b8000d2a01181c0c07840d101d0f07485071801529090760b800000740080c400740c1003030f15619903036003918005010310b42d80f101c0140707038544080c00803842d6030000801354080d8000086032032007100002001c40d80d0030301801c9103055003e401e9401e1756403281001040c2d000c04075201406485480404a031150b0000266801c4130010300060708e07043e003040011034058100c09120070702842038 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 440752482 1250 440751232 440751253
    0x11b0806100944030301080706020118020904030c0b010e060405220b0c0904051801150e04021c080a0e15090a0311060c0d020604030e0109050f21012c070503030a0f02 73
    0x740030f040d40d00100030304021038072541000c070348509106a1b0760105065a15000c04174003002a031544092809404175520041656681001d0740c200c0d8078400010300d101d43c001c0c00402d0006241c0c1e2202e0282006813401c10040e941d100b00b02c1c6051150304144a40100000c0c80d520006003901c940d40c0d40041a0001c0f01c2c1031003085404038042d47da0688000c941c0500300c10017450030040c01d1040c455841100c482e400d01544c680282c0064045006c0c10103030003100d03ca00d1480301c45010b40302000107268400e140c280d46030081c100003000c0c1100820214803949130004205800d44028003030720061040240380c0800140f03155502d0710025016490320707401c07807401e01130400002810700502c110318032650054022850286002405100403509030f40c1400440e5000780240e031104071008007000c1d01910900441c00100b10214080c1c034080c000006c940d800c201e011085410800a0100c10448080001e00c90048003d003450719410107020381c580551090041200ba00c0c4269284900031040d401580c140021 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 440753732 1250 440752482 440752589
    0x1205041e08070501110f0d0e03040f1d1f050108041b060c030809010501060905010c02030708010f020703110303150d11040501030f02120106061d03011b08061009 71
    0x6030500941d5031210200d10b4800f8003e0a01824203100c540c0d041061802d240107140c070b1400e020307031441300d50704031f64071a041e04d045c010400480d0040d04400047c411034a68450880c2c1c8201035000f1080155507208000c03c00c0c7c03149401c00151004560701042e4001c9040c0f000444100c0d00042c0107403002c941080d1030800351542c549621000d0035607a603035420408071608000c0c0c0201c4d8003070807903081a85414010499241e1142da4402554400d1a04c500502d00758000a854840745400c000e4540d46420300d50303445d20600d40e00800940e4465202c610a000c3c0a03055a031700ca01044500401d1a8040b15400c43c00b45030204e800b502c0b0603c0b48808030245015100400c0403500b0981088442e070181080c0c042c20341c074100820715001c0310315100074003100b07041c60001400c08660210382003140f8903582e8880942e81d4290000c0500001110304643c44943c15280103101900944126010b0f039400304940040e01d10444081003500c81e2200704001e460171303415210f80e41c0500c2039051000d02050170441c02c1d1124 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 440754982 1250 440753732 440753783
    0x9060c0c0913021807020a030309030c05070f0f051801051c08040b03010e0a051003030e180c13050603010b03150d05030a110601150206010306020c070509040f0302120703120504 78
    0x851085100c080c07000984144220f0003007440c0019182e030b51320f204010125500081000016030f1502d03006c41c00001900e019642a0071103403009015011320040403844a140400250403184180700c040c007102d40c0c0380180115901c04a0444801620030001440f040c10100d03000400c5140c0c0040c0c078240c860b150340f10070102d9089604490600d120000042240e035940041042e006480d24004200e00d040400c0250b0800f4903e01c80141841790f110015002030703440040320707071803502d48850129440c501100008e44690280e1450b07020712540c2d05012070f4900705107007524161101010603d2460701c8a403034903040b105642101a50000135000c0e02c0000550600107013031101403a8455280c0b03096100466420004160841b4640b109035002d0703c80c509600082090450f600034500590701e94902c4502400e141032a045241c0000d0842c003400100704c41004440545400380c1d0030f0b1001180542141d1a06215000019000642503021949040c540e9030129030001c0c450752541e20070840d00344041c80c401 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 440756232 1250 440754982 440754991
    0x17090604060e0103150e060121060305060105090a1b0e060d0f0b0a0e07020a0303020903010605090702060108011116240513060b0603041721010b03090c01031109060c0c09 75
    0xe120440c80c02243d40c040c003410104299030b03d901c1d5115410134a5408184200926180c10049841c1c590076110600884101c03100300d00410034400c940d12800c000c2d54407042882001d0207074180c0b0000906420a91182c0d2804074240c040c0c4028010000c282154001c020203141c03980b0503001c0100201c074441a00c103200340c85803581008215840700710200881001903901041c03102508408202c0825030100342c0380009076240c00e00503182c4241c0740209004214542080e40c10051071018010f00d40e40004002e8103c816450007404080300c481c000746064080d0340b1954034556000c850a200151030342a805040300015403160f0007040e00052001e0554505580041642c100c14104a05000050203070f0803112005039485865402d2680e591801c400c4880001100520f0200300c010340e80000700071280152100ca441c080903943c48034044292544150b5a4070f0691050b124020881c0d4020f00030140d40c4000e8107507050400040c14148151a4040d5184428a000320004441d10b40d94056840b80034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 440757482 1250 440756232 440756237
    0x1503070e150a0e0a05090f070603020f040504050103081903020703090e09031e0c0c06040f05270403021f0c0e100216030515060d0c0b070305091f0311090a031709060406 74
    0x1600b8000300000c11217134040c0ca1180660050143c1001e0389200085010031981589001680c404508100c100030740580d805c0a98003508020002081c04903640140504440590004070b004000d1801a000c80c810250000d0100d55198030800440007102c1d4015031140b500802d80e403a0201e00144149040300c5240d808051040114030305060080401c8a090b01d000146c607514906800c100010020404a102e040d101d18181d000b00480c80c000031101501c519901c01c00400241050301c0c02a40f181c100c1106191500003004626110300d1050160100e4002c02d92034109209900ba410300107403c800748071369000d520411710000a0701e034060030a800114018800390480c1922000800802e003805840d19108092066101c00070815080c20081220015100c60f699540d4502c1c040c3e4582c02940601684011b039a00d075000318134009221454903200e2960100005a000c1c40b42c1c120324000c4502c0c258001465560900c0080e01484525140c500402600c90400120500042d0745602c5500000c00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 440758732 1250 440757482 440757509
    0x180e030309060106020d020304030c0504020c011113091b210b1e0a1401050316170109020d0501050916231b06060f0d02010503060f130b03061503070e150a 68
    0x1345560600880700c08009900c05149403070b10315100e0380000c01160142c2441264002245410300030b0075400302c0c1e043e298a940d402d80b54600e01000f400490380a100d0b042c409130429078600c10301c0410000344809001c1c503480301040e0305001010607c1c40c403021840d07100c01c0c0d641c0d681074144558560f85603014041e44070386442d040300c100105018181b20f00e5440000b80e803d00c0b00520400c3d0303070004162a03108106140000280505140880b540074200c0c1098a8044201001045d0030503580c004160b844000c1e841171200b80da0f19024041500400c80c0e84c1c6404070540102e22104074860050380c01c1540d01110104494282c660020040b275204800015501c0000c080e24007080070309200f0769600c000b00300c0b820202601e405003c100c2c010003400c00203040000001c001a510f584261038160307901b501800401398111203103d0b4200414036078115910900c9017400040101060b40369102007660041d020b0084117240c469881c0e140c0348041e2940401403205c201140301511004007410041c250b012285c4d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 440759982 1250 440758732 440758739
    0xd060f0605190807050636190f050f0a030602030112050d03050402010903020108040311010603030324030807060203041401050a021306080f07050901110a0803072601180e0303090601 80
    0x2603220510710742c100b521840020801c100400032490f1011904251442a90760071043c0b0100e800090015101a40c016443c01742c5007a000800104464080140e8440c45100d4064440300382e0800948941c01c141004014144040d0401c024160b0654502605850050b84c03260382d840242d07042600079810650090328030100303004040240038401e40f078a060401c12418103800007001c602280c00040c3c1445030140c0800e04142c452600b07044503110b408002c101e0940c40e40f0303004001d0051a5030403084014481c0c0c1540f5890700f40080401202d9100e06014507000745a80c5090194100400c160b89620036072b580328884201c2030103001c1c0b2440040000680e2031040c0c400c401d984503015044101004070203030400803080103078419540c006102c0d050542d180c60f51500122100c5010600500950044403402010130908002442c01901035031104040d014462080c1404402c40006907070f0078103182d500402c00300c50783e4040c00e190301100c800086104e81c4450000ca195500030f64010400354000300042 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 440761232 1250 440759982 440759989
    0xc0f0809091012060209011707090302030f010c05030604180b04060e0d030c050d2f0409060e06030a082a0303061513030b090c03071d01060201290d060f0605 69
    0x1c0e80c03040c55014405401d0703042c84000d01203501d80d4280205095400075031410301e68010814402800c03c3d081c0010ba041c0342c10386000345500d540d480202c0c001d01c2000000c00040b4410b008821000b591070307a9041c21691b0303500400c806440c0b490100f00074051456907450204518010b060300c10341c000d142c00b10384040c0d4896003500e400f41c44401202090703e00b0704600d45103a0701908444a2003402400406c41c50080c804200280c2c5d10740070312305416486e030b81d200ea048204200281c811101074440400c0340710b55540a0016071001203512603415003243d0b402c2000a2020b1000c1c0c903480f4565446201c050494210380b5616400c5085588a02e038000b00800045241201a00c5503205007180c0042c04c0015000442140d04442c0c00000c1800854400040c0e5900c4100030440c035078030f001021194030595038009080388070130000600c0e2007903030400c001145042c014000c001155411201d240104095194000e8204507030300b66299010048801c036030003048090084101d85200910000b90701884c0c2402c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 440762482 1250 440761232 440761249
    0x20607060e120316020d080a05150a060309030207120201021e0709020301060e0f220207170712090b13030611070606062a0209060909030d090b15030a050606040b010c0f0809 76
    0x11340115402020105103c81d4410301a036001181a60301080513241c652a251003120355411464000150700d500081c4242c2c1908014041d50007034007550f00d003c0d200c542107503050865000103030143e40318884144140ca424400174240c26106401d80305215100e8105206aa20030791000380010301c0c020700c0b4600d5142411100d4600c2000f2912003c00d4812440205054512500401002c41c2d001c09d0240030f03c6022440c907414001c2032124a595113640f03292200614020502c140000341003c00045000300c2e5500c1104c149035651f00e002001603180d0340d210f4015007210072180c1d6500741c1c24030070320300081c48d41e000b0b00c00500095214065010a220000d070100d10401002d4441c9115410b8884090f0b12031010064018009a0340c04040b59580d0b056240365129000303c030001c4a00c1c1c440c410040c001c030002c0784c0d030060300d603440c2c21004100040e0416541b07408800e0040c05980152001ca201c13442c2c90361000a0300030060401c6160140340341c40f0103026030403a00050fa048400020098550b2505120 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 440763732 1250 440762482 440762521
    0x6080a02040501170a02040e0304030c03141903020c09061f030501030308090c0d021201060e09060709051206070806121204080d050412120512070e011106070c020607060e1203 77
    0x400d071203003080b05901590f9030041900b019010303a0340d40004a448c010140201c130302445d004594083c0d0182d81f441c01d40141402e0300004825030003095452007128005112040c00b0a401d036004155480309041040000817024010b181e00c558440480003c000e00070040c1441e1840c0782c3c90020f0507601d1410054580a0b0083c80c000c401d8100702d003150203554611401401c0f1980646000b882c41c2c001900990040c5580d411441000f5100010806503907000103a0920400c26541d80003c0d0950307401c10b0108582c01e017110f5104541200002a039902d10a00c0c2e2140d11070001400c0800229842614a040003e0340441445541000800b800042b03002c2154034610b03d15440d01d0b0b40f07024138101041e4880d40c201880207041c0422580d524203407030304c40c00c1656050141194003000905003034001600c1046140c8540740403c0c0041c400c400b034540041280c61140c40307544c85180004403103030300700001d0f03a00443d4115005a83c0d0100ea2241600c10400e1076103402201c1e5070300b40d41e428080c0901d4011154400c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 440764982 1250 440763732 440763749
    0x40b04020901270e030405060f04180506060d0903020a1e060e06071e0e0319020907030608030a2106080106061814061c0f020315060313081303050106080a02040501 72
    0x160200c49420b440301003c2110704520b840010350740860111681188510340c4000d51109001c20b010a25031a200001c00c02c036a00340d0803404120814181c40c1d8143c2d81c0403192701d54448014845196810002e4212080a80c4607205480c090055503940604016110b80c0d03940070f403048003409400b0440d00d0300c03c000410b11444001c1080d4503140034001c0140c404480800080030031050001c00303007030007031203101a001d03001002d030f60b40d1f444982c0c565a07101403e21010380c07103020a000440c4c20789019201d18010750769060090361070280f0620302500c26403080c10a030840200600700143c00480e0610842024050a1001185003803800e074000b8030610b00e0001040c0e00000340311041060021002c2190142001a200701c0d40320910845210740401228030480c4800c0e007816500c01e03d564842c0c0c0258070500f590107401040b0b1240c0e0092007528001150031426401111000300e0101e205d14002d8040b82d844201ca100407561203645041c02d44040350700012184c0d0007140340d2021443e0901505014151a4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 440766232 1250 440764982 440765009
    0x307080304050319020d0c06020d081302011202090f040608010203090c030312060d030903050615100507020d0803181902090610020d1103041a070512040303171905040b04020901 78
    0x4400a074949401c203107904040410f040040c81103449610502c3c0c00d40e50080382c210105030b48d511002e901c03410046250000a824040003500e444885808a9081d0390180d460b491f10311030440e40e000095001040b0b144c0e222000c4409000380d07545a01610f0040c049400000d88c487c01c1c240e02c281d00c2d0200400525200750800e0120009884015010b41e0388100f0450b19141c44490310304050b01d6448080e003015202c0c4c0550703000c00c604401c95418045010201b994001420202c3d202e0854050056280096001c250082c41ca004601104050b5400444c1e11620401380c01d40c8c400c2c5189002c440307104401401031481d8580c029881c014211641c80941a21a002400002c150081d211201e5100c1442405000420a13010400c20810b98029102240c0c1c0c1c035080076441025801c10f0341200c24200c0f0715100d40340c81c025030303990104251411a03500da161981c8054005112082180f401003c20754111021002c419015403180101070099000310022511400c1030f005200c0d180c007050300201d0201c00c80 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 440767482 1250 440766232 440766239
    0x6060307030822030602070b0717071202180307032015040302120a02060a230403030503010e0c0d060f03031107060912020604050a060e1008160e010e040c08060307080304 75
    0x40c030110f400060350303c0070108000d000e03518114070074502c41d003004e0411071010603d9010020003004040c042c141907140c0d00503d041040101c00c80038012681d42c4001006501d1000b05d080032500074011143e003042c00030382640c041c01e010928082c1e00e07030702c182d4450144040c1c0361401001208180d00014003038401c0807080041d445121124452031000030b004d02d0350781d8603c01782440d0a209942c2c61540c02040c41e9554424110020a103044401400c9114041c599a014030480c0c1c1404031001c03203034940c440c1d0f401d5078a03000604c0100340c0c00600d9401486020450341a00c60050312a0700c0c00b515000c00c182c40098103508000703201100c5203105541076400200148070a5412104d0b0780120ba8012044406200a61001c107030203016951107240c1210540c00041a0303140c01070310b00c211030007060781d0381451700c03084203c202d80f0038200341d5100c0843c0b105d510908080500c141d02c15141c206060600b581c1c1d0001003400b003011220003581810028440f28240249481c003808503000404c6200010f5003003e05 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 440768732 1250 440767482 440767493
    0x30c0f0e18060102031b16060302070c0303030e030c120406030606030b090c0306010c081204021f0e060a03062402070f0614090a211109090c0907120c0903050606030703 74
    0x2a076000404200e040440010b04581c400c10848040705d0301c1041035545a51002c40060b51105203091514000c0c12660010401ea4400d1003a902007980240980320f0807461038030113400034158514941400e000400000103101c0d0100b019000803c08a01c2c03e50f62240307040e100404072221504054101410001544e005a4641c207242e80c22880d117008455481c0c0b04c180c01030b52440041c180042c02c3c0d680200b510400401c5103d1380c41e2242d40256118000ba10003003942600244600c001d160101c0d40101d0028142e00300781c0040c0068090a08000a0b083d0315590184411061031901e00444159200610002603061141800612242c014095110300b409000380c00340f400f00c1160f8a5108000c40c002d030140d91401003200091207a2880011101c2c009100c42c0c00070756200fa420394042000903480c4841e400c04030a424032401492024028085006040200110002e070984041200c1c040c1c41d40c850880510540c01c078249586c43d03c1c000c081c51031501906140006221512942040700200041007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 440769982 1250 440768732 440768749
    0x20f0d02090a0f0e10020d050703020c06040f1703090109150204080c0409020a0e0c07031b020612040c0317120f06010f050d02160b0f060907021b03070510030c0f0e 72
    0x380e000e02c0841c40c02540360501e00144103601c1003800f944140740710b000c840c2c1d03d81c2d4001c20074160340c894240210342d2451001c0c0c09034840c134250408650700040005000c01c0c0708100403a419440746900400100e00c4c58000303469074200380c1d0040c40c035954803003001c4100502031171144110143c0d20300560800f0724100310f0507158101d000055006907240e910642c11503580303007a0a00a02568015910b0340c0c180307080c40403c3c40e00801412004200000b440c1d2100c4d404580c51010400e5004000510f460b02c00a200940c00c0400780084592030900b69000c00002d044004402802802c01e000d9911100d40c1000f0f000712003005894010410350035418080701c0d9034020540c0420140310700701180d4492078144000b00070b2143d081c5251920032081c1c1f880c2d041007840d08001e0300814800250343c03003948a00c070801049031400e8038800e0241e03204628100d0b140d41851510488100000c2c2600c504a5841e8003050940645610140000e40e840c204078129607002059503021a08602d840715802c4030080100b00c100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 440771232 1250 440769982 440769991
    0x9010e0f0705040911030d020106061101140a02070201120903110124050f21030703110c0904060b030c12060a0624051e0d06030b1f0e0c040308070f020f0d0209 70
    0xb5512604c015040c00109080c501c02810301804503008004040c500078000c040d0713801680001a50700d14a15500001405111081c44484003401e1258464071501c80080d80580c0049040c042d480c55010f5411130741344a0941d0150280e114200e1f07607180422203030300710340d804402c503203144464a01c41d0903102d00800d800c10540780290307605141800d001c0005100f44051802c1d01d201d030b91040000440c0c402d40030000d45403161090b190400641c43c105000c540312000700c04e0094014210000180105002e900080007082011f815200000464000300d00c20701c01007214040a5403041d4140407040146110741c40003400201d2043c5584603561740c1e044ac02c854aa0044c2040142c0071a6258801c400c040da030000417102c078500959110320300da4807540984202d21050301c00b00030110028203031581a0202d6400f224404940202c01400c0220014410a004d0a4081c00c03072420300011000860107401840054010b444120650b4924070410041b00c001159050080302c4000f485030058552980f0b040c2c00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 440772482 1250 440771232 440771239
    0xe0303041502190f0219150b120f03040e010e060603070305190e0c0a080d0221040509011217190516020a150e04020f0703121509020309010e0f0705 65
    0x180140745091030103030241d0b0000707040b42912002581c1d402a04140c0344c1000780c51076001d03110155a800f80741c441070080350030042c0945030102d442c50b413440816481050100c1f401888900b104101d81489880d003009815030b4195680001001d011401c0c0c0c14540c14010108050812003d19108003c02c20600000c0d00350014141c8920100b0003510b4400480031001131821010000c01072a41c10441c1c0d1100b8221a0341c2c05481c5040c0080b4601e1404203c0d42c40d0740000c0d40040081051f104448841c85a21800b5042d00355000c0c0804145a9a0041000d0003444101c844001121031030a282c11580701c140ea0f56000080108152000c0351060025103443c4916420030030340f28648401142454003d090000354851400d550100d04401181d990641040c0d00d07640303030080c0561000a1004034441c403802e26600380c1c401d1218200080c03281c42c45561083c00c5d81c1c0c000c5650b01e1442a4040c5001443c1c1012185a401108000f0044024801c4008021440008041080c0e81540c9582c40700640c0c041c4900 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 440773732 1250 440772482 440772503
    0x712050c1c02060703080406140402010206150105040902030906090d170c0304150906020c0705043308070609031109100e09030909130c1203050a12110d09060f0e030304 74
    0x994415070360030281054003d01400d90350442c61800a1072910121002c030780c00c2c1c0c41c01d43c84002c8804600c144511469040c1c000386030544540d9005100e808030b2525450400004004c049004045c0b4000b642c000c01800006118508051030641c0c200076a1004640411101c02c142010030140301c2c42180c0c1001556045541d03a4030f0b5810f040e080003a0080b00c0c98449418a0041010894540c1c0146403095001c8140d90105445104200070340b0700000d501701c1041904210380c1610019080c80c40c500c82100c0b40c211440f9503450680f1820034809500000110b41042020000c4c812106006450600c04940c42a103e1803e41d400c0d24225105001d151410b9000300c00042c0028401c004503259802c00501018203844d01500000c2141241903048600044d55207002409d241901c10555480d603250325100d00349190328000711000e04000041c060800d44900310700e5040d04241c0001c1941045d14a40403070700c81c00b2070415000b903a894040044425190881800c0b1118010056a0b046944000503c1c1c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 440774982 1250 440773732 440773759
    0x1a032a01030e0102030708012d030210050c060108061015051b03040503010f0203060a050904120e01021c0305040302010c020607050f220807060305060402190e0112020307050c0712050c 81
    0x20020007000a40d03030400c3d840007040c048040d8110319028120f406800c0c0345100d0203081b003841018154082400e510304048044207100528101c82001c40c0f14441d0f04d0581c2c100240c43e174506181150a03030081200380c0008082c842101917801c210b070050000104c03103d01c0302802c074600502078400e43c10855036048035080b190304444000e200301c1e0b000b460010024005038042c000100025801500c04078840c180820b000146402c004203111712554019401d410019501881030303400682c50726405045000f1078100c1c120040e1110b500800c0201c15950000d003a203490316020382102c003030044080556000301d08100d07081780d22204035240c0c0c20003600c26941b140b00c0405c100b00c60000d03800f101102d16440765004104580005068000c0711483da4080c05251180703001e000c100c0c0725031115184200c1d1031024071003009001d0700701c1c001010320614019099001118100e0120380040c0c9201c1d0000b500020482204041040404041c4c075001180005c503018a555141d03640880d008a140142e494501c82d2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 440776232 1250 440774982 440774987
    0xc1503040c09020f0901030b03060411121c050c0c030109050712031e03090b100f090513020910091d030d0b0604030507060305040605010b1602041d101a032a01 70
    0x1103008103109030065444c0c0707041c1c5592990384d820000030280002d1814039910001c1c074001034080d0065810001d59440c0450105c2032059406030030050800c81d1017001d0340841180c1001c2c00e07010f10b410860b40c480361241101ca143c1414040c40d032840602c681e04180e8600c01144c008140b020440344001d401c0405000301d4581500d01d0529042c02084e50406203890b0300200380c1641101a9091244040f413145580386840588455007501a81d41003d00446d002c0c041c225247d4452070300543c502c600c1400400c0c05074009000484200d0310003540070b2410b54100203c00780c80c09140c1c60303100b9004010358040000d1031101e0343ea000740e5139000a081d4403155108016100c0034215005980c000d0f007901c00460702d0f0700b4082c002c1c0c60280c43c1225080e1411000141c1089e200b41510321500c0041441c2c40826108c1c0c080101034445c4040402c1401900300081002c2d00f000c112010511181b03010104010302001500c0104002d807581541c003940002c000c0c0c61030010007030f104140040301c0c06910310f0081030a8004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 440777482 1250 440776232 440776253
    0x10908010501241106011802091e130b010503040615081507090f0305030a0809010605061b010605030f21070c060210060801060533030f16020c150304 66
    0x188954a05030001c11101c0c0c42100d0083d002c44241006040c000d40c10304102c0c0c81c02100001014950000001481050a510380320900141d040b2000b504061140300020911a000004188480d0300c030f207035022035810401c1a200b40d0b0424240104401d0b0041d000190151200030001000650342d586007204410141c05000003918041c4200d5402501e22001e5440801c010780e190004240c0500b00000d0074140128001c041d241d115000d1418504404400d642040e0081c0000c100ca54031079102281903182c0d2009401c1c5042c81440c1101c100084100040c21a0583c0d04114000d8001000f00468407800180209002205903a85003a00102c0c00c0c000e0b085024014000300041510840000c105030700284203800c180c04100204a195503c0c1d810500729000b0788900c0d41c01070340d00b000c003c02c0c56000104030b0341c044190186805070703500303414010020303540f04454200e4010410810b02030641c50079034810746980d491303000070816060100c0c00591441482da501c0401c0c0c0e80300200240411040552 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 440778732 1250 440777482 440777489
    0x20903070f060512100b070b10080f03041a030105012109020904030503150f0a2d09020309070b13050618131b18050616080705012a09140109 62
    0x180307108644030500105140e008007008240c115010011607040301401d060b0304111a42c200c0c140e031400e0800d58841c0e0240000600d405440113032400c0004141105029003001c480c5a03101441da01c0b0300306403020141e98031610030803105180a00042c8410b981001d650b0310411781103182c4092128041003080060045a003000313420101640c00c0c80109604400514000e0300000340c00c881100c2d4200520840900c002c41059210142000030400140c814000f1900a2042c04a0700754580401c41e07420401e60a80d401001069800410400d0000e1f041c80740b40f02038008103100320f140c120740d081e40c64890380e5140516882454005603107106205c0342102c0c0100c4103009844140d40c08403a241c04801004088000300c40b02c003100300240c090500c2350210b078000d4800c40c0d1100301e01508010501446070400190040d81604810340c40021680550242c044140701c0c40010804c00322840d120a00c000390210840a14104480c4008220380c02002031420703070314680d00c01680030010340d0049484282550 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 440779982 1250 440778732 440778749
    0x180213030602180f01050a080609180312041a010b090f0604210512120f0c0c0334020d0f08090a030609050f03161e08031503010f0b1302090307 63
    0x500d1260100d000428240f1000203c0c1c0190481c0e51840064525110340b105c003400050722303803001880c10b03c1c1220344242c21550004600b0041c14450104c14590341c00200c00e0300e8001e8804d41004200902c188502c1102100c540c9401c0280d40b400b40c1408030340c01400d030b104c0c2c860b1840c0240c1e03c0054440c00c090718004d01c49049049500e0080d4000407103070032803003401076416010b101ea00c0301c500b000e01c0d4111010900340c8043da000366921002c1c0540500700c00380500e07590440c204101600b9150400c060440144800c40d08121303180d40b113600c807802540d04010303038440c82ea14a11801c0569520f000c020700e55604041c25803841c0c0541d00d46020f00748114010385900c840503010110178400564000c50041b0300c228121220040f00040b42956809007050000004150304031180c0010440600f9407285c0282c44041102045c081d40c0f07450040d081100c1d585840307401c01500e40641c0c5400d018030030362a21289400c04c4108075000204024000c882d4009141170380010f90032100751001c0014100500d440d8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 440781232 1250 440779982 440779987
    0x605030415050109020702030d020d0c0b0603100c0f0224040602030a0b1c0b01050f21030d060303081e07020c100e0a06050a080901050c0702100314012607180213030602 74
    0x3464154029041b41308181d000341b0400c8503170125640005414940c41c2d019442d0f2a0303200103150703210030303406000030902c81c0c01d070040029004030201d846c050520b014a40b612503c0010f00380c0c0c80001d20b00185081c2007032102a4180e040030301180f410003000d8000e9000900540c1e241d0f141d0701d00c8000b80180241c115003050407542d6a80e1007000010320041d003030b803081c0c0ea49000c0341d0341c0360308100d024501c40f0401c075840254041c1c0658000c1e0b481c81e9000410403440103907030170721030b070200d103072040350003c0e4420f60110b40241c08100880140b2004550030000c8801001c5150070b09410082d9240740744c0e84154000d4194a6103071400c1805081e20b140c00280050080120b1a12400000c00d9508100d07680c20100b62014082080c030401801250b11030021101d440f41045469000c102c0000c503040300c60014166610256204407800e410554060000140b40c41c40d0b40300e40300119003600303071034094482441e00111401c0c003e5106001c54202c080d0007445015880701c0c03440301a078180380c0e42a400188240d200 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 440782482 1250 440781232 440781239
    0x6030c101d011110021c0615092c07200c01110312070e010509031504140c09130309081005040203151e090709060e09010b0a0f06050304150501 63
    0xc00c0031516041c1c2008440058010720a005503000e1042203010000d07030b0042510900c14200782d6010301200055405c0e10a407100d10303040038604691403508146504100c0c0c060038003845030800c2c4c094004040c4135401d16801e403c0008110031602c8800107000e0001982408115a58030440003120328004c0000c02c0d601040680381026516240d040206000c01e0b1080344540c1e000d4404801e0b41d1905034041848110f9584207902243d282d031142d4000c9041c05010f00401d986610700300119050b5920180729501542002e0401d210071341d4203504070004580c005440c229181e1980c1d8000c139044070900c80c2d01c0c078190105282c2035415109503044007806114200d1144003e10107900018050b03030080d001c0c0c4d01c0d900383c02d03200610300b02d01c04c840c24910901840c0c2191078042c900c800c203035485800b001c141ca88994807100c04a0a80d13031164008081d509411090114201c000e20a001c11000304071404440b481c071300402015140460301c03c0105104000c030005040c00070110755010400c481400c20489980c5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 440783732 1250 440782482 440782487
    0x7020f0f0319061d0715030f091103060a0522230a140d08010b0a030e07060216080f0c120a0501050f071d0a050607030201110315030616051206030c10 66
    0xc0700b04107030352007800c010440001498001c031039080015084082e040311810b01c4142080e212a8103500c01c20541d40d0010b071a2440d20603c00da0442034800c02880802881d241c6c10103241500c081c00166603103107004d0900000386016201e800072400303940c2c540a0070301e4071030410045181945141c400c9007000440c0110004034085580b00e440c510540d0034005005048015640d10300d000342403407022030607034030052180849000103480415080d24012444202c0f0000440c00c001c20b95001d00c025902201081105803648c40224010b00700e020010502c4041607588599142e800140c103500800041e004d100618009118080c840ca40142c000d02050402d15054000038104680724400100940002e000240d150340300b0f034031403107402065403101da410f040400c00d45902088044040d5075803103094003620388007440a103100300182a003402810399141c003410f06064004041030310320302404507014101600070301038980b40081020030086590311040070915001080c80c509500808048869250f00e0307 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 440784982 1250 440783732 440783773
    0x1109010b0910020303060307090e0c04090501063b1803040b0306090703050601020c2701081015120f0c080f0c1f0206061003060f0914061507020f0f03 66
    0x5009507000d44201440e0b6800300d80343e000a8906950640100000b0803400a17aa0085410f0004040c02d880344100c1081c009001c640c0c6102040b9080e03511003004000110345a00da96619500c801c80c400861003170201c000c072040010788004181244a82c2c00f1800b0514400300039581c40410100f201d0ba180d4442010710f03020303001200c405210b82070440004602510900680c0c1c045d14041c3c00815500d0b0850041144c064000b04c07074078a5a060180f40c902550180d103114500a10401001e070110740c42d4021102c080d42d00c0e050811801156000d01000709a10b0ba110524640d1380044503280d00030110f01c1e0111410307400354402601c5115030185a501e00c0d20104030090020421a04400208400b01040c640300380320241c4440581c02c0500050160f08040300e00e41420f00c0b040c9000034126071621000351707658100d81c11005001e07558000540c00313605030506007a00050102d4002008101940700c407207003440356210083c06040300e0b000c0040d65842d81ca0422806200090070388410140443e000c014a1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 440786232 1250 440784982 440784997
    0x4080a060902101e110c030d0c020f06130605070201030f09081b0105070504050427080705010624030c0201090506180705100512090f070e0f060a06050a0c1109010b 72
    0x110358500c0780f41d011500400050443c2100842c4a070300010031140150340766a8216191165405000e0050310156810f108101c11001180c0760245640701d940188941683c900b07603c0c81c0902c03c100a90454200591303241c404480d840d00e090f82d07440f406480100d0141c4001305054244a040480207401c00684030054600020000c0d0307000501c04400a0309801c2e00d9041d2980004250b0030030052090b0305154000d5000b000041051900c4035050795074408155820750703401c2d2010b000c04940340301000720a004200051941e544402011090b20286203c010140701d810400c0c9942d400308884054001c0d080ad49009801505039080c40c03618a5030a42103815100030858a4062201c0101d80c82c81c11214407490300b8002c1c2d40e00703410908030315200042c5000c0907000e0422441080d10002842c1c2e403c02400010380012054059641044200c2c1c1c200da60700502110720400c219071003400a2580706007500c13281134542c544071580203401e081201e10032000800c100e0f0003490080005c11846d0801000f083d44 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 440787482 1250 440786232 440786239
    0x703150e010b3f0304090504030f0504060e0d1505010608010512011404030509150c010209010e3f0105102121090503030a03050a0506060c0703120504080a060902 71
    0x42c03080082009407040c0c0b0444007401d2071205204101240d403295001044901c8900b145802c003102d8000c586286811591203020620b803070740200f0003019802180380790307a0050703400c0c07135070900781861406000000001c0d030f01c9019207030040042e420f101401070b0fa03040011010340100203550b152031009050300700074015180a03802c0c006174040e10207014841c0304040b81d8803004501241c0c45035a0112001c3e0300214005034410180b0002416610081c03004040f042c051200060f528104c417070001d082c1c11445201c80303100b5440d45a240d50b025030141c10b00d01105002404070b8051555444614035600444041d00303182e0361806d0208050910320100b04425980c0c0c92010300e0105545220104121046110081c42c03040454010010038942200c0f00c440e4212605028107107989032008285180c210162a1b00000e0301d60050003400c1d411482140e4000c030003956020320741111661100e030b032800c1c548402007410300341d600548482e0341316000b070b24081c01c100410b40ea0000e220b42004c00150805100a074030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 440788732 1250 440787482 440787491
    0xb03040f080d091a10210503070b09060103030311121906150c15021306050901020106090f0207021e030312090c0d0c0815010f050111150c0d140c0405120703150e01 72
    0x200010405d5180498100134000002008180385030f000c01c1d06002c0d000c071003501c020b000b81000224072503e414031506840d030003001d01e580f4505004065640410340c00884c07420801800400440011610343d001000d120840000c0034a0f0800d42d00800d03c030f0f408920501003c40201c84c0036544071480500d554017808021a000319210b8100e4102d100d495800d0340d44010b0701d08101b000301d0090029041c0200d05000015481d42d8400304c000a8038555003000b01100e90004210301146020703110124410401d0581032140c079a600082030b581e20452034802e010785000c0b000100c12110030032042c0e0040d44054011000303034001d880d0480b00c0555500408855020b20b08546001c004500c2e146412980b01480340d0422341e04d0300c40191540c030403040085203540124500599505a600d1216000e0200380d2103950380c8585014110085aa00d1050a56444d108000b84440051004241c40988000b03e90050580c0014504036140000c582d1000305420f90b0042043e400c1038283e0311060004241000a00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 440789982 1250 440788732 440788741
    0x30f0c01050a0204080c010f03020f0d09120228060603020a0e090715020606090a150b1312020604090e1905011b0804030801090509010f020712020c06040b03040f080d091a 75
    0x500f03078081d82c0a8071039590310498002419612445680c162010107041c01860840201180d40c06980b28012044d011303900c0c3c0d80c3c3c4108006403100321030fa10300190302c054044400001c104800410140d8a000051650362024006120300c40c2d1020340256401810b60200355941c80e01d511403c01c0440d444049406a00c00018a030311003071112290400541d40500030310365980e010080720303281c003030aa09211584c810380d00305540810510a0041c2c1050b020058407a8003482414491841580003115403410700528000161911404e550585148580c00b19007400e0850645160609e0390645003070601e5070240540a10106610402c0f100b030000c0101d080700c0052400c2500c2c0900159001000111010300401001020f0307403025130803c1909001240f401034200f00c00c8281d800190082c1c4420540701003034450580c0412a541044400341e42081c1810310704a40080355000042029044e8440361b400b400070091a00c4c00c88541440e943e404100d000100c1c10880e214080d000564021600000040f4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 440791232 1250 440789982 440790001
    0x622051617040807030c030e040905060402240d0b0f21010c03090302150403020f0706080a0c0e01120203070e0d060b0a082a03100c1e050406050706090311030f0c0105 73
    0x348155040f5001500d40f415603502201d01398101c50041d005c0100f1f9128180031603a80703006900449018100411060501d4010440b001072450722150342c00401070311102c021b224042c01e03690341d13007008500002c1c025000c034003103440300c254039141d280d020401c65025400c08502d10399050490344000000c01c00c110910109070115120540c000e000340e0300100c103a0f0820b8450310220340e445442881541e85926140c2c250a01c2c1203a80d800c41000f00c0d0342e1104111079410309201c1c00101110601d40340c0f109600e0800042c0c440103440c900e12100c25000000690140c0c002c0407101180000641403020350740b07080c2000700090096408440c0710308030010000840440001c0d010316a44102d03c080056186140450201c0740940704240342c01d030203013000b03a4200310000e00c18664020030030b0b02c40300410400120181e041003121558402807210030700050024a5100b01580c21140c2e00c03201c0082c00303c005090654004020940c0c90072a84000500619415410b4000d481c203220180000d022986400750325 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 440792482 1250 440791232 440791277
    0x30909021614010902030d0e13150303051b0d120c0e01080606090f040f0c020d020703030207061103311703070803061201092904050606220516 63
    0x244658500464001c001058025011003a100c011a000103106a519030200707081048a45ca42c0020441810050079035060900309101010344002c001c2242c0640400e002c0c040c3d103070900000c1c0411001040d241380c0b4412440c2c402441031001411034100c0e0014207802040301c0c2c030902108205600b40302c408081e40d8010300c001410513005854402131b0755151307000c2c400546c00c0020100d6201c48103900c25580b9481c1e81c820b14107400b480e1079002c5941011000c020b464034610701d0300704c011940884810008a5404103180058a40b113161001c4e2040c2c0418a10b07245000c1c10b180c41220351122800041c182d840c203480100d042da98441301c00400c641d135261811410112807510307071140d0070130450b200004074200019540900000c1142c802044020f007100c0c01c49080e01412514416034494401d03c1001c420443c1442c01c0148000c4170b010314190740da19840710b06c0a0b201d14014010340c1088205600e0013200c580c00042e184808002c0d40c0380035000f101c00d412050034408042140c03140c2d4154904c40f103000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 440793732 1250 440792482 440792497
    0x31106101a0c2815050109060806010b0a180b1314030c03070b03041a04050607033e0c1b090c040b04030b1f0b0a031b0f0e030a060c02060403090902 65
    0x103400480804002c0021000b04403040c0401a0b007064101c20005400a550380321444e201c4100241543c10803520104036070494000344103070344c8003400412a03104c1d000c1c121403503100140342427503100c04000c0045c24040615007183c0325680003c61070100c0b600111420300115625101c1402c00c09800005141d01c60404942c11030b055081204103002445c845c00007160818406c07410304e1420b42032000030340490b080c183c40071074542c0c006000b8001d0103585405041b20300d1540c00c0080390183e144042c5292502c0000303100c46c90f01403a94170442c40703242204054468602d20b90040c2c1e40b858101c03010054038040640709481c8102519000304011003048020b0702c00303854404e0010745c0b0349403d54480049190000300100b031289031101c40c15a966034980300709002085090011a11a000301d01e000c0c8c26503c07002c601d003d131070118803030b07203d0900e0744031504d080501c0e010f007003000d4000c07203110200c0c1c240701c810074000d0491030800031900002035000038410f100c2d900a0392410061078841c0001c1e8140d100745034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 440794982 1250 440793732 440793757
    0x1503150f0b04032306090f0d0f05040e04060906180209010f08150c04050a030c06030c030911040911041406330f09030a06051503010203040b040807031106101a 70
    0x803e00000c0c07200b480380032041c2c49014078a01940f1502d030b926450000103c81d006155089205070000b108001c2010301070010107802c00503002d0060980050150086101c0c5603280c1c81844041014040e07035501803155190441c4081c821043d1300c101019460030f44100c01ca000340c1d2481c00025159001410b1070702550030101c041e00b494021040d10b05000b2002500d1100303600802c010006269541d507003640000c0d031140c000403c907240740c20b601800311f4071404001c4080c142810107030000640417220b00800d0140888000440d45010700300b0140298400034000d802c14035260280c6078400f4001480c5100745000c840426035804807106031032455072094080a00124404029a0201303003001c0501041900c800c1c94508003510a4000380c03030034031903900c1610000d41c1c91050082482c1004840d041e006402d4000394a5810701d82d607890f081c00c2c8004c001411b84200800c0307840426105a01ca0032403106503204841c00c6040001f82480c00c01924032440c55090b040d85650140744511a05686a000166 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 440796232 1250 440794982 440794987
    0x105251110090e040206030702280606050306062409060705010b100c05210918150f060d0b0402070f060e061005031f021e1b06040506130c1503150f0b 66
    0x5c0d402d0114540015020005501614030440380c00c3c5159107102c501d4a100200b1041e641c0034138203000d801c0340c1443d000b440c026000741c020421a61140c071301c0b0240429144541004c0615003c84400490142c0c01c01598802c070001018030074032030705410400d540c6070100c41039480d418500c7d01c1030f201d910030808010980d4100c00e80040401c40c001195900202030f1041040c6041c00d006e0000c0e40e00072444040b100d140342c410080c010b00c880360b0500024074003420744503070200054140004100d4000c032900c0c10206511900c040203d5212a0180c031401644002c040c05413071075038903048000d0114a290024079108080000c2c1000210030360410072a034001c0d014011000141c80f4001c20142030700b2444031200d40810401107094084a2440f255a0550168544480b0100c0d0480c1000c119180e201c80541d0024082c840410710114042c0e0700940c0c0c2c102503910000403442d01a58841c05e40c1e00c200c400b900d10b80c3d003151166030075070070100303103600c0f08681c21040644440c0d070000c500103103005e0456264003e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 440797482 1250 440796232 440796241
    0x501080d0c060b1305090a030f0e060d050a0e0a0503190c0b010506030403140d06050306010f0b030106200a03030c120e070603180f080a17010803090105251110090e 72
    0x707620500c140100607040c4075020005041302402d65509843ca64a90b0b40000c08100a141e4031054032900501744c0d282030050703e035840000030200c0c0110601841c1d425603070ba01162925203030b40d05c8181d9180c0400190b85030300c18103080c529202d401103001007400c443c201c020088403910034108060155401001c19480d64201414040c19030030003030040342480345200d43d0300b05401a41c005481c00300c510800c007003085801c1905160501406900014240341008810300001c0c0d042d000750307815150640381c0143c510100025030328206d40d00d07500500e1703a03009800d580070030305074541c2041030302c25141d880b1114080850038104d4101d99400c2845138041d000301c0300034020544030344c100c02580c060000030131600418507180c061010034000710484031540001002d801c001d800607480513010242d85a8003180b90314000d9015120b10845642604100d000a06c010744215441481c030f0003088020001c40110f2010302e004140440c0c2032580e14400c42c401c25540b004184203450071130036134000a2102c0c400b601c8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 440798732 1250 440797482 440797493
    0x503030d0c0203070606030507050f0105090303030103021507080a08070f170f06180c090f0913080a0924020c04020903030d2a0c0b010504050403020c1e061303060501080d0c 76
    0x540300c1c99021400100040404138059000711005507004402409403989040e003041440c0b48090b8070305042c010140a0440b06aa001c4240e904594040c1c40968182000282a403203134401c102c0001e042d40c50103d204a849039002c21214800c9000d40ca80c841c650355440c01c10396500c902d19610f0807400d8483d4000500301c00d0140385042c0c100300040c140801c9103065500c400440c080880e12020a600081242d80c1c1300d01c2d001d60116030b606800c0c0c41c0c501c4182805800105c0c0340b4190140030740000c07400558510701600c201400300040c54010508000711449803810700036403d140c2040401031181402c0002c681c0340500c01c480140340000c000350f18000d80131600d00003400c04000c01d507066400c00d20001442000065035820f68040a5640c1b00ca54001032915100e400e5041c0c002c0c0b40a1480c0c0010400001d80000710500e6200c4e04030f510201c1d5503030802803d01c1c45480001d9454000c02d02044800701c4224842c00a403d5038031415090210380c0c1c135000c07003c2d600c04880400c10300090000030024003044 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 440799982 1250 440798732 440798741
    0x1050d21020319170106170c0c0a061404140105160e0409021c150504120509190605070302211e04120b0103120306060e121e250503030d 60
    0x34000d0054a050188400d40442c040c11000790b014040792200c0400f4221850403403a4501511207810540b02c140000d014228001500030400c116007403001800e605900400c0001c0c0038119840242408a0a0501c0103c032504d041550308680c1d080c3d07140f041115081c418010f19100f000602440485c1c0a80c48804030b4910070203181e01d0350001d0307403210000d000da16a1104070300c1c0d020030901c00440051640c039015502c01c5003518261119071610f418400043d050100000100da15403401070b444602e01c5c40051100c00b83c413500a1120f00030620002a1550050040c0c07210b0340c026003e54030742007004c0660106488203800c0d1444041010090142d154001d5804141c0038483e014010b401c140e101c5409841014540c1402c0ea04403240400400c02c10413a980400c02d011007a24040c0110741c54180083c22001c901100c1600c01e401030b0031000f40d50403041058010f80c010400c10300160300324040010b40c442e19810065204260380024003ca0142080c0300d41c400c5542c00390045103000c0b0156507000040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 440801232 1250 440799982 440800043
    0xb07030903051b030306010908010c081302040e070609180204120311030d020309010204050a2103121e0209042319062d050f060d09030212030a1401050d 67
    0x509100c00f82c241c102509420a03490614001140d6070f00b488000940f039940b10b54059039003603040000d040d20166101c1042c030b4200548d00e80300515140c00e07100290103030084500030b070301c030744500500000c85035440109101151802c2000b00300858079500220103074031660040c0549080c0c1e9841190020344143d5103524074003d0002544e040044c408080703000d0341d1054603040313050381d00490184494038000c05d82100805101080300907500c0c1c175644020304c00c5030000c4040d061100207901d50048001c5500072000d00341042c5c3c01508040d42554a81000f50000740c2240d02a900d0480c20100021a244480800700c01401c8042c500390741f644c43c000f0b201c0d5107540700c030100d030703501c940c000907000c03222102c10720404100745d5802c52a42401e00c039039080c144840d881103100d51244c0700d0307081c159111182201d40400c3d00c0340004c21b03038521f00d050907032a03d6807140192400340d03000005c004910304268405501003805a286060703030303641c400802048034107581024149100c01000980744900305049079540 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 440802482 1250 440801232 440801237
    0x804020108071b021c08040816051e09090705061204060518060f0402210f01050901050c09010c02180c12130312050709151112040305120c0309040603110301180b07030903 75
    0x2a005968501b00c941065010200543c02140707d0107440f034051013000c015090a88155000702001420000e1710160354600f0390085c1490303c04105045018001c001c041e110241c4119034070081c2d010100f0802c10202c40035101c851419010a0f0161030707030441140e0118524004000c2d680f01d0901d000c40c12140500708982c00b1010b0542034140390b151074000d40b00080c019002d440642d1048005901f900c5c4010302c0300350399074545002c00019a001205480c02202c0c20b207008043d554544c1301285c00992542c001c0504003480c0e004202082d84076500904550724808181c05c0c04da00d0321020618460030480700200403450310b84000480940991000b9404850f80c030302041e0542d40d9140f41c5112081c11405080002d00d044030709074481400300903000000c11084045032800c0c2c03543d100c0300c2e10f0b180540d801c02490040000c0d0040788100800c16142030030307002031080103100c1d640c2c50140300e850034224a81c0d0095003400d178969030900300c1c10700e58080143c1000825401e6911060100c0090491480c21000d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 440803732 1250 440802482 440802529
    0x19050c01061d070201060f140a0f080f0d050a0f0509060904090803090f06010311310f0b01030c0905100c0501140f101802091f0804020108071b02 64
    0x11460024014800181201e0320507070340a420018000b07004541c000e142d0029603040400030800c10480c41014011500201140940b5014000c002400540d540d40b001c4030100c50180c0200d155540450100e6024442034210b9040d680080020744036406140c580744007040c0c0c1071007404400c0380160024925124020802480c0c21043d000190440f0210901601c04400210030045690400c000700314440f50041c00904066145a80301400203030380e64800e0303001d80c0400c546102128040c583c4503012010760003000503010f01c84842e84008102640000c1c425504014401407154001d2044104403121580d546581508040522a104d4000358012040050352480b61005c07134820701c62450b441e01c950144040a0030003100081d07007103070045c240d008401c2c030000080164800b255910098594003500242c3c907800f00000040c80e980480643c0c44003071192403207022456034007400491180d4403d0326810001d44601c4422030700021b54600c03a2009488841098016250000d40035200c100070490521 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 440804982 1250 440803732 440803747
    0x150109052704080c19031214060d0c0807080c10051603030902150a050712050901120e0a020d03050c010c0816050904090618050105010501080606030a0c0c12120e0a05031905 76
    0x41c6040518a5458203c14245c050041010380c001401e2408140c00315040c0300590060069500c1ca52018010a01c46c44082c040ea004000380003004000401c400c8054800d01a40da0f9591511080100ba446220301083c00c00c43ca111806901951007c1e008081601c11445140c2d40aa008200c0c44405a9100d01400b40c10340341ca81d840b0004145040f41542e582e0b4540b9202c0c64a0b00d40703000d0001803202030007400d221080560361712002070810601c540001040342c0040d200d81070304105104c00003a4001c803210940710107140d0844001d154494621000300041c0034800c50884000e00306441403071006900360f4155100a00c50409822094401000021461156030303441048401c51000c005a00c02e0440d91042440804c0c4030b4540108400e08045075680351950005141d480010410001182d50751032050245101e000031048036070b03001c4121800b0301100c8a010b00000004900032031524100160064050030115a00003402e500800071410b02d9a44410507454074084280041001810f0101e60b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 440806232 1250 440804982 440805007
    0x20607021b010804050a060218330f1c0b130905070b0706060b070515070318082503080916051020070e0402010917070b030c09030615010905270408 65
    0x5c29012800420180603800c03082c041c00401001103104c0c280ac3c0c4041c5011001d00344000411750410a040001c040e034031058180354070054050a400c6010440e84d484100c05440b1003640000800e10341125024600c44a16114178242d40d105071008100d50070141f0108442000103029001d0b441c865200480c00343d4448030010f80301d8010a5003915154012101403185407528404242c00444a02d01888030300e056421b502000004141e0003440e4074000501c000030040701d219020000c030020f20441902c504181001810302c00d081c1c4071a0b441d0301440c01d00c8022600032520405c115000602560a83c81414000391154034981c3e40807407d070341c080f007a241d15188060044002925500301c1110351403e1030f000041c20340b04590803407487c144000c0f01002a1500c0012844100c0e03d18005090f0750b541d580c120100c940c011030380019003501c110814081c041014525102c9005420b030b032038410032944da01c100080400c46900700709040a00550611131005100e03811a817050084000c1c078505040000d90313 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 440807482 1250 440806232 440806237
    0x7020d05060105181b0703050c10091209060e040c0908060f04051b0319050c180103020301140f04030807021c110606040c05040506031f060f020607021b010804050a0602 74
    0x1140ca030341000c00180560f1400c900d08400a000202811441d8980b5038182e811041061a400d0610030f4081080010544a8002c8480340e80c0c210066441010b4854800b1028290341d401c100c1c2c290800810020050348140203040856400d55100c0b481005018184002801a000300780d007084240c840c0030130718920810503c0d002c1c40b14040700c01003600e0315050090403c200004003800d00c4045409002503690001450465910800102030f80440745103001c515051050350b00303e401c011446101c205030001c060082d4100c900a60080c4012442105200305000c3c0444c6d8003c01118044080703804240725000e41a8400302a004841010f004100e040c1c08104040c85100006182c03e4607440142c002400b0f941c1c0c001070243c1d824002c403901100044c10501a9000b40c900945022002420740d80d01d41c6459043c140070480340a281c40d4440340c3c0100b080d80080b10410140c030958010a10952001800300c6c62607003686142815043c101e0011240751034080c00540d1217200b241e008001050b0240300 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 440808732 1250 440807482 440807509
    0x60a03020a0b0a090503120a0f12061214060c030f070201060e0f01060e0a0305060711010209040c0306081b030606040e0c100e1c05030405100c080c0106090e060610140702 75
    0x40c0b1500c919403030714003d0600c2002d401581c040d400440094609130071080a8803d00f0846061080302c400010004981c400d0421451030714040c2414000618000318802040f00c107402010907910007038000d60403940d03441c4151081e185a400806c0000e6420089034092a04210310b44008200c41c0d03038507007503501703c00d00075104c00f0800042d50004208181d000030b550f00e02d1600c2500e204080c1071031602c903143c940e02c00804560510441c640c1300a0388040c20340c111589418010000c000303c1d04a17500040041a1078011010240702c0c120340507401d5031003440182e011990041c01003809550f402e06000c064080164076804c075210300d0f08414900d644046044a01c2141c580d00d05400f95528020894801145030b031090030010303100400700c04030b07402004032825200305680315070170500049800c5034004400390002c1c0685402103075003494040d040d0000400c60300c2601d410304c240c0c0701c5036901c03030380344d0f41c003a43c0243d4001842d080601e81e4a00503240244041810f04681d0304040603074000c0b425150403801c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 440809982 1250 440808732 440808749
    0xb0105071b230d06020d18051024030201030f2a020624040504050a020d060209030106090c020616110f010e0607050901080103030513031502070c05120a0b060a03020a 73
    0x14103208890510b808040002c0b00000003041c0800c12601050614601e50b03000780205400041c042001c1d541a04018001c3c0040c01c07000214146908000361185541c0b85460085402e000029002c0c07450501c4011a8288601e680ea1000345150300640062a210b44241a400d0300c41d0078100d0b5521a540030707c03039070b2103406441c07070580741e80da960090801d01d008140101f82c03480300c01102c840c50341e000310b07a940840060700d0004040e2202c1c14281d20701002c0490095000c161075003914108440c540180c4100c8030709900910903162a00e2400d01924900e034000d200580c41180040c0d541040d001c0d40015020160504c490121000381c0400d0422006190600c2c05a44a5070005d08000007040001da000480d4074000d0b00b072969450000b0017564040c40007601300031020901e003101040098464009691102e0380d40001b90000c103800340a900444030585081e000340f00002042d04200e29034001e109004809444154080d40e0f51004060b0050002034203c81c8041c000300040c1c1302d51600002503d8080c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 440811232 1250 440809982 440810033
    0x1404080312010509010f0308030604090b07180503030a05180111030d0b0f0d02030a030f02190c21051e0f03041d011233090c060908060f01090b010507 66
    0x50031100c0e82000c040c2c3c091070040d944003004204081c840440107081d242d02408031662500e80310005009082c10303441c0030301a405840c6c28030280c190820b40d00c2c0a00030320710000084540c2c0d214101900c030f0150800c00c44c0400c40030480701c26541d00c600404140c15070305042030041080c0300000305145030011845061000e40c0d810301e102c45407030003100003901160704484541500050f40c0c0820b44a1364801002410b00c006145040f144900a2210700d00d180a082c44152102c051420070201408040c030034241101c050007403031180c81c0c60040811902e540c011004140e080c2c58104195000b03030789000010294069455840350500c024001440101004148000010f44c0000490802101a1701402200c186000e10000060400f032980003070130075001e600d08151350404080382829030099072148481341740801349410420700420385c005899050b902c40f8034458036000c1c00365682c14140c44c0c128072a044200100402002c03600030b0b000101c018501141090010740d00c12628500902051003048801d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 440812482 1250 440811232 440811247
    0x304140a240608011a060703051b030a090e09071e030209240a0e060d080403061e0e03040e1302060403121119080a030b0f0303070f1103010b060a0f14040803 69
    0x19010b00d501030b040300002003081c01c408220043d015468038110a0158201049110500d0300440030340d07040c000203a00c614078258400c9d001e1902ca9003d0070140000c1038035107034007013440104c1c4070745103104064080c01814150708010181c000d04e40d054062901800d0b8180c0f001c40182c440b001081c3c011001c03450004805049602c4000038101e007046514050154a0340030088031498603075054003d0303010f940907240c001c42c60402c487c00b4821500050009414002001400e45903a02d409d0300d12180600108030540c2c80c5800d0302d8907881584104078082e20304801007803840c00c1c2644850076552008001910709503413680c0703152080c4007981c0c0f14000300320300182e031303034100f5009100b0000c098852010b80c2100001070399803401503000b03080c00d07030302016610302510381c06403201d240720342c0c48400003400c03680c030307109140340440e9503084540003282c8041d0031384105185810705000320261003000609060811506410032110310000c808004200807400c5015009488604024400b030034043e0007031348e03580b03d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 440813732 1250 440812482 440812553
    0xf0905010612080703030c051e0306030d03051608061c050d090f0b030a1806063308070c05030706060e16080c03010b07060b03030307110706020a03050304140a 70
    0x30780c0c0c0c0c03058680b03003044082100003400c00011204582e40c5428000341c080201034080714280a5408200300201085c84040d55030200ea5010b54403c800440881c4c41c410a04c0d10704800383c51081d2075515a2011a081c0c51064900131481c1940c010000360220341d2940760781030480b20700040300c003060f181600300d1800006070301e030f000105401030a40f01c248004203501c2c1c50303098240c5100c0100b604050b00c6e514820751440506031b500e08100c039600f00d407052220a840e1043c0322810701004a20924411118540c01401410500034482c0d0400c07580b6601350b6a900e44509843c10400040308131454007041009070000340c03142c0704a4002d8040401c1c6201036203003c000c16800380b020306000400307000d183c00821010380700070000c90741035800003002c16803074000a1030040060170540320010b0703150001004101115500c1142c414240c0d1403541150140c0d41d80b001d0507601d480c880300001c4e000660400000d400318941909032109841d910b0704490072a1400d0322200060803020302c41c81940089214454034248 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 440814982 1250 440813732 440813741
    0x90c060806030307020103180215040504060501110a08160b040f0210080405250305101a0d0309050130090203060603070f0905151e030106090504081611040f090501 72
    0x141000449801d00c680080d60b24000c00a0003410192100d01251f01e205400003a201d9030ba9000e00060309060030301c0000d4890750401e0040038061491300b0000070b000d62162100004039a5600050210300c0c40d6a01c4d291416401480e608010b134000c003034803000180042c070000d0303c101c2c09050342d001d10a00d50310400c44e001a81c038541401308101c800078000400c001003000c0410705610454064200f06841003138a001500398009400d03270080540076400c030303480398019100c980e074440da1070380ca400540c0081080804001001170001413003400140810750140040d42841c10000c4103500301030920100600d00781001c0401c8903040c1d030700c900303d510440c10b00704511604007070114003a29645007080d01c881c80d10b105030b00c034101e2042d45800100780ea841e20000b0b0101c100c1c0001e0b100c001c18150164414051a103038125940c041d40c0781442c00251050b0a124045c00390303501c4a94a46803001d03c0f0b03642c10b80c621407a0400e49a04000510071a050b544500c9a003050300d650902c08541c0b101941005406c44 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 440816232 1250 440814982 440814989
    0x708150c04030503030f1506270102070305030f0d090606080a111e013905060a0c0f030b1810051509010c1b0e0106050403060c18051210020d090c 64
    0xc0c24288010700000b030010007585c4e801032451102040350707503400360101a80b0081c024070070341007400041c0407040d65806000300c04142c010326010071113401100004a0391090107100141140d0414024031040d020601e00070040030352080700110b0b50342d6540d143c80c4200da00c0ea5000c01c1e1207602c000340c0e03002000000b44820810300b004440e0002084a01145d08034070861386807000c3e0400143c85090304c01051031245442801e0100c0051040b0300f42107241c454419020350509030b07002d214410004a0402c1d20303016402a0b041e40d80e542901c070303c428032010340c041d110725043c2d2580041e40200c050503654030001c0c65441400040c0c021800c0505c0e020510001341000303440d94040003420010b0940c145d0f0807030f03001d41d0203580c00440a001d01c2009200680d507007000350013101e80c00c1484400010020342c000003800030750340030701d50400034141404015148280016084c03005101000300420061510743e5940014119050a8804020078482c10008903880000424001a503542102e02408032102240001d03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 440817482 1250 440816232 440816251
    0x315040f06050a05040b04060f0801050601200726010c02010b01030e01151703120c090a090b01020a080f360a030c05041a0d031e0504060503041e05070815 68
    0x40c0c00d010110f60301444070300030f4030b000f251950849031aa40303603507000100900c0c001d03a50010494654600d903020301001d496041c00520104051208248524071420164000034000c1c10407510300300312184a03031000303041408041c4900c0000500300c0c40030f0264000040b01c1d40c0c000a00c940000002600301c0703031075120840b25a891300f0303400042046020202000d454814039031449a03000c1c100c41e2440d52059084822540020307505000740105100040c254101c03044034040e43c0507032900d0010049a0580c0c20003030040e80203c10f450013082c9521f0040030040d242e601900c0c035040504280d28005402c0c410019500c2003846160307408061008442182e80d0700c1280c5061600d4a50384814030a440c40340580c9100d0b41e524540a1910051980c2c02000c1d500e0103046003007030102500f0040c080003c010114020150300c0054600c405108408841c160360168550600319141c54550070210500c024015400c1450120f46002040c410003000004000500007031250405a00400d01d203c20040c180f010f4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 440818732 1250 440817482 440817491
    0xd0c021603050c0f031c050304060b04090803060d05010216080d05011509031101020c09010320270612070b040303020106051903080a0207090e03070b0c0a02210c030315040f 76
    0xb40c1c0100310b07240900000c481c1500811404000a81400942e01d90342c01c0300c0c209002001c5005030000091032159000300f204014403015002070009944001e0300040801d00c2c1040083d40500c2c2800480115a00031000141091241d228005004c1102e150036501c0c080c02241400b0528aa0f000e440d0240c8004c03036481e02d07012038006011f03010405602008083d410001000c14142e44200f00b4140c070317408001c1c8002e0555a403810088907031566841e244c3e901c1a10581ca164407410415101006020482d080c2c100009905100c02d9040001500c0d580c0c4c040750000000c10110000c20034180501480d103006540c0703919620b0064212440c50f40958001c04140906040e40403c0740c2c221800c8035045400c3d0323561041926012404c2c01c1c5d054002c998164030303104012560f424000081c110715071244540c2700301625001c40d504d0640c05880c0c01500181d01464054a02a0340310100c03101d14010142014180390503140184c0c00d6030400c0f501c400601021040f41c8006207083d024044c03008003030400402 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 440819982 1250 440818732 440818739
    0x306031e02030a0b2e050102100e0d0e0f0301240f050a031514042301020708090607050708010216061404120509061e0307090e090304050d03140d0c0216 67
    0xa880d200301030409000d400716031000548170982640c4140d00c80800900700070319580d068100c1a4a55050700075240188107a1000400154041c85465480e5404400a0941d100e030003004640c035244580e43c098009001e0b9688007102c0c1c50901548451906010100c0d45020501810049080951f40030050340381100b9020403094880c90192170540307420645040d130156450700d0410207009100c00585070307c54a0810030040c442030b54041413800c101d45040c02c0c0310202c0500128240c2c0552100500b840d0340c100700007506450900d00500074503110b82d069481c01551048039a08a03080076800c60111305049440c02e08121070780c03040750002100b1001a40c1581403d4842400c0e10035010656400e0200c001070700c00031650b803201a111b80e04c490070469101c149803140c440030150015203582011411040c804600e03400312203122031140724031100030b50a152a140030451005100c0b43c044d4240810b80450b181c114444071700906d48101007100100f2030240003e4001d20f00b00f2040a000d900703200070302050 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 440821232 1250 440819982 440819989
    0x1030510061d0409050f06060306092a0a0f061706010903050307020d053d0203070c17090405010e070905010302192006071707170106030207030314070306031e02 71
    0xa1042480c284190000c10007100810014410140044c01906c00c1d40c080c40300f000c0300010710070710506c019011f8807015156450181d0703a4802c004030000c040040203403500640c00540b4000e00803800028a1410415550784107040c40c0e070041d0b00040c0014520751007200008048007216504140b0030310f4000452451034507019103d02035648020f2080a03100e00100a0110030045c1999603001081c000e03004804140500354200d002c000c1c2100107100350502c1c0100782040340300707a078410b15407038880d10380c0e09800381c4d41c42281d4212030360a0811b0440034800c011450310745120b024003070000c0682c2a2502d0810301e0340608001c480758480c0d810540100100c90f1480442e482091032a0700d0350818900341c03210383c2400c06d440d080721162415144511404c02003596407110304060524820122404142c5980c64103c50209584509010301d02620004004041c465401454420300a00c9c00003542100c2d45581e003043d40082c0c0f0140000303902c8010510034080c4091024181c01010002030440c80d5075980031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 440822482 1250 440821232 440821247
    0x605040620120c010f0501080114040312020412030e030f2b0e04020a020d0801080319200a0303050628090504080c0304030b0709060315051e090c090103051006 70
    0x540707200141e00911080281010001c03032100203030300c040254948260100b69802440ca00190480444c02d0000002c1d850170f040c07081450020300100411640d41c1c81c0d49040d90501c4461407150012a401c20000032186e00e5159401c102d0744c130035600c1e501601c4010041601d442c90403440003105410900300d45150560b809580c4a84014060b11013003200c4070241c064902c0040340002c2504140005041e454030317030703000c695212407003842e454407091070362980580e9940703008a00d5140030760407203500d056204d02c0c003c80140441254820080401041480040d401e00000d0301088010075191014080300e46480348100182c00320040d90300102c1514994002504030310746c45291001e80c2c1d61408202803140d13075801c4404125111049a58956607450841c4240800311b46020024220200200d074851081c000c80c120000344e45900c1007440d0810082058407003151000440075511446400070646071040304610032942c0e000f81d82d40f90f0036848000350a036a001041004440010f0070244103054010a1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 440823732 1250 440822482 440822507
    0x1403221508070c140c2101050117030f16020d031709010905030708030604060302060316030501050f01020c0f0a09060320031c03021e07080306040b060a170406020d020f031006050406 80
    0x40a502e154540c0241801d00909035005500200b010103054200403030365180c494040c105100230001d681c2d03541c0c1c2c1402e001000b07220002c01500208030b0241003694207406031a000d4400c3c2460080414113500044024914200440114070300146031203031042650540c42d0b008100c000207200382d50b999642c0580700c1c46010002048141e0110226983d13403a1540560061680502095600e090420550402c2c04120100c0c20009081000201d803030304098500c41000340e8180c0050005491001c1000f0100000482c4190880c0c0040c00001d2040014041d440c001c6005031407510850201ba04000852003082c609a8000e030b200022040ca05030b0181109424601c50707113401030301d0341d1150300c100c02600c0cae80d01d51030922060080307014070034070a12000841c020281264108501c2c20114140021030080c12201d501090140f00410000880400701c564428071801d00140b4102c03000f5a010b040783c01001c0404c0f0042e00200401240096132041d20015040c14200903044c2807030080c00910085074000c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 440824982 1250 440823732 440823743
    0x60f0f0b0d0305030901200403110102030a080105040f0f05150307080d080f09120a030c080f0103120f1704030e120604082506060e240d1403221508070c 67
    0x111910000c0d03103c40341211f60007110035004046054002c11603005800246c9505103220b4211a031580000b044a05c403040c162a2408582c3ca00003c10000300802488580c1d560b4035403c0c1d030645250301d4400c0310f02c09c0c0ac50710107000f0040d1001c41030501e010700c3c82c0c01404d83e0f5804075400c42c40c00c0350044003079a44003121940c0481e2683c0c5140d401400d15802c00c85810b521030000c140090025051b41041300c1200c410790395810242d4640c884116008028800901385c407018607030426406110781c800c2225a512414a01c40b000720070034100759503881c04c076001da0001d00c1100c118450f074900310f00045d0392800c1e0400201201e04207511000305500c1003100c42d030700c810310742007500c4400c22a000304078185a800580805c1001d660b400043e0b403504080316014080c40d1070054608011880000e13181ea9440041c0c218a1110310382d83d100100d0300784002c1055024481070101c115851000c025440780c120f100c65110880c1490031084007440103070301e03480c401400698000c1006065001740c48105658101 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 440826232 1250 440824982 440824987
    0x90b030c060a0912080711040203061302130b1204050616020d0c11030105040309050f1212090103020f0a030e010f0605180402010302040b13051f090b030a060f03060f0f0b0d0305 78
    0x50b00c15a00c2c000194014102c081c0040da40c9410300444c4009844074500404c4c10f100f0300d614007010001244022180e8a901000e4051080004d01c0103901412505c4d2080e00c00c0301c0e101e62070f0b003000100f03900b010b242c130001503010b04100801c01030140101a00031848800c021411002c29802a407101d4254064070108542d42040f03000340301e1400d9518840310b201074001c000305d041c01e08000b040c400301802041d000302409001a482820003503031158a24140c00f0240c07000304a030707070392100642d4800031302c0c20304040e024450700c401c03200c52a00401c0803c4e42610002101e10200c144642544d032a095142011071410b0001c20658545034a0310031202c100c14101600d0b644d551006134000e00075500000030100010540070b80050068608006840003180d40442010754411074210380c50140300d2000000725005020000807101401541d00301030140c401103001c40c2c4800c011031b4042076960041d14090b850b8983c041d1203076042c5c070800c0d10b104107480042c803c042c1c1c3c0310003240c46100340c40002800c02c40300 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 440827338 1106 440826232 440826247
    0x112021c050a0504020f1f030b030c03150a05010614030a051f080c190b0f1b0a030c06050610050313031101110301030213021c020f070203160f090b030c06 68
    0x80111a0322081f0808100e014041c0d454015401d441854100d45d4503a030148140c80c40ca50810510540b01d2911001503c296403060348030005005a01c43d2104005e51a0307011030f80d000302441e4000c0385030348440e8280c0706c0d41c44d1203003031581c0d2442111201081c00e10010900d0f01100c502107450141c036207074040307507203d412085110b0074031403607000c2060098076000354010380640200182e14100c0804180c260f00d06080b8040403c80014070b1211041041094520809810030815a16a013410840310000f0f841751101910302c10f049070240f80504100351080b0f440c203410082000084c00420540c0070700e80780a03042070000300c0c8079040c94149140900d40d54829102c03619489844000032252408040c00258094500c2c0c0c2903014040005202588040041c088404002c07003003020114a803e05c030440903003554010002d101c1c01e00c03c0001880d0307000140400030510440380341d43d89801 = true := by decide +kernel

theorem cover : BRFrame.Cov 440647482 440827338 := by
  have h0 := BRFrame.cov_init 440647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 440647482 ≤ n) (h2 : n < 440827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
