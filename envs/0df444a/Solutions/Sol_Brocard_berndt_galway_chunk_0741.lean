-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0741
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:31:37.126879+00:00
-- url     : https://prove2.me/submissions/e5b2acd8-b3f0-4c3d-af76-b8f8726b9d1a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 133093525 ≤ n < 133273381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 133094775 1250 133093525 133093529
    0x6060907050c0c12070302091608090d12020d02281b1106090103020c030313020109051507061a1203030405060708010e01091e0608030a02010e03030c040306020304050705040c180605070c 82
    0xc0c0c440140d00f5651144ca410f0158540010b0b4100000d0030402400c0f4172802191601000a5610110240d4405201a0711034501b241064002142070b811110204400e8019040503551104c00500e0304102c24069081003002252920810302e80c04030544030035400408030000ea00d11008003d00c0c6800565a401400b41c1040049202c1c0f54040741050790340e4401c1d411b440740300c0381d01012281c0d24180308440441e0406001c8049000401c1c40d10b0104d40c0b8100b05135110888445480894109107960f51400040c10344011090301001445098041550302c40890035820b44004015580d6420203040035802d103100200303044184044000104026400005054116602c1d03000004448401031021100c034184450b08003251403c110300414020001b00c000e008081040d00200720f500402041d02c0c0c5c03a8001201d5415202005010801c0800e80d00d40003550f1242c03150065420701519807001508952002c161480080d035102c4885d150600124080b102406241c10072606040065455141e010703554 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 133096025 1250 133094775 133094779
    0x70504020d09020607051606140306040c11120909010e01031e0c0f151101050606091002010905100b030d11030702060a02012a0e011b08130b0c06060907050c0c 70
    0x40c1c1c0c024500d015500c00740181e030740201101e58504480c10f106903039040f40d03032030407410003076195001508074021051100300b00115642c281c1190349000402009081224074881480701e0314509034114001800900c1100c000b4140e03c0351101d241c0024030100d440160000301c9006840300051000c20144c3c0c608100d03802417000708140110003403806011801c8141c2c062050f40041003070129680c1c1e42050140c03150446659103901c4402c4059030340f4260780c0151102c0d5000b503010410301c1540e080c02c642d00c41c14082c041c000805c0d035000556a072843c00b00c0141d03403500200e07a680700031311403403038240180c0445a4661829540c50280d001d00c84d51203101d0710200900c184800034005032101d00039006904050003021605480400103010243c520910585807400a20340f01100103080d802291200311640303c00c107240c01003458542e03540d01e042d8080c04520000f0729070700b00e00007130040302d41b001001d90140e075401400090a2130000d1180800003c2c00a10a001c020301c0100e5a42e140000c01000e90201 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 133097275 1250 133096025 133096027
    0x70e0a0515130b04060203183003040807080109052109010e0f040f05041b06050904020304050f030301170d14120601031b0804172106041107031d0604050307050402 72
    0x1140c1e140300c4481085501c0126192800300c1e00085c5103801001038a010221040396000c040411170402c110b590340101c0c1d0110611144a2241442d5001e40894800910083c222440d03d900d8080c400d03d043c0817503000c403001c0e03911038640400b00881800340c10150070240113607108400c40040170341868001e00600b1030400450b0301080503243d86401d42412041c4000c2d2041003503410208402d000b828046500792007054215070446094090f00c441481110800d03500c1c981006800300422002c1d40c8007034001c0e201845075089000c4031040a000460080107c1070104141c50300ba101030700c1c2416001c44507082400b5070440b203041c0801198045441c0138003000304c0a869030740c4000069005100140e178120302c588a1382c0a51107a16040a079288c01035002e03d45085908803030070020000740c8246410103002d01c1c9900203089181d1013030303100b4941040e070082c000300e0078941d0000f0807082d40c3c01c451015000034500c1d82c2c9240c0c0c0046641e408031030b820802e43d041d51401d41410086036036030403244941c41c00b5680c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 133098525 1250 133097275 133097287
    0x11d030f040b071a0702060a050609060d0807060b09100f0905100303030b040e011a090606030105030a030c030309170301090b0a030c0b0702030c06040807060206010602030703020c091e010905070e0a0515 89
    0x801e512111891301180c000c100c09034100108000e550700800c0758203a08280c9014013044507031a151140e607110340d00042c180300c040b00d2503648108090300040d404442e0a07494010f10a0603a6034a100d582c070918891100b0510a450509040c0311a00141d0004c0039031031030001446003210b00011703010190b1383c05003000f141c0220b4000c0030500a11006036240001c3d40fa00c001159040c01d03a40540300400d5084070380c0c9030941c0300c0004000c42c43c0b200788206a81030b40701c510b44400003030280d2514103e540c000e05000503e00081d460705014203d624002408141c5e00000505c0001030364450400c0058095441148a50031a03a55600130040ca00552569900c003055090455504000300c61400102500359a1a0340e030700c5d110306648980071b000d0072015009940010807510303c000282d4003003581582c0202403880420045c8014040d01410f00002152510f0a070309041340141030542c02080c226600182034581640020801202010310b03074460340703644104004560385c402c0d010580c0c08880030603559500c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 133099775 1250 133098525 133098533
    0x30201020c10180b0a0e0603090d0305040f1707030306290c120d02070308010608040308040210090510081501090e010312030221060f010503010b19020f030c011d030f040b07 76
    0x50140d40c0b410003500800750000c136000442a02910340000c00b51501c00403039402c0e400701704090108030b810208542c42441c440f00c90303600c6038000a070003038028400c00c1c02180b0307203895040101e84800310310304602c1e20001d201000c041d0b15200b05402003400e0300e803025100703801d143c8055484519504110a40c503003c00c108132104e40038408110014400f40c1c0441e43c890803811198081d40000c1000c2d0b011a02d14400040c40502401c646071049602d50755900e03031503541364200146414440901c40811502100104603a00e4041d03a00142c1304140c2c650107154601442e00013682d80070319450904000c58200204240c1c003110108a05580e03001d000c41e8540d040030300046009000d40c0f03560210b8501030a0891920503040c01643d030140710103480d01d140800000e0015103981c4000c1c8a035409151003004409401120544c260b9004200d41c41139850000e1560a82031031034000f04910940350351741d064819000031000d001b61448614090145003440340840d41c070145400780344140c948001000458400704 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 133101025 1250 133099775 133099787
    0xc0a02011103091008010e0a0209010207210b07050705010f0c02100f0e070f08060a110a030507090f0b180409020906011b05010207120f0215010b160204060306021c06030201020c10 79
    0x34810143c041300e09104000801040c0680c00e2082031001c2200c407002c00c00750b0f0464021501d11400c182c00814403035182c00c41480310464845107048a908022544c0f40c00120848200c6028a089907106a20341015040903402c40d000060f1a91042c1c1c030b0030540018094000c5691000c050b0420b02c001200e098800e1400045d158840c10104580160200414402c40b49400f41003030320980c2c42254825501c10050008071210250b14080c111020b21220b202644642c011075807240c564545204055940c003044180b4456640000c0d0b140b9101040e5100580403042c410055102c040b1010f104001c1d994000c40c800400107801d950410458010700c6a042488030480c04400394002e00131980d480d0396003011144490303580c3d0204c0010701c50610060106100284200c01e0003e918180c001c2c2d40d180c00b9a21016a014030305c800e1103034122554520241c1d8813031081300300a50003140c000d03a071911100710049a040904040304d2803989040310903c0580d80c0090b48007103220090300c4000041c102980c0607660b03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 133102275 1250 133101025 133101037
    0x102061009020f09030109060c12061a07050c0d0c090c080c070204090305040e0f04020901050607030207090b03070b07050102030105030c09040506160c0204050a0c080c070b130c03080403050619020c0a02011103 92
    0x66007403003420713000c1040c02c1d48400104a6103076a4103031042b210460360000e62f030441c41218103444221004d8400075000700010000c2e680303da001c40c0c040d0b06101e0085084242d14590a8034041c240800c1000030803000d0164850a08142c9050031461a00e40441c0d5107234060036801a021b16920440782040500403c210307400703005a040c018055150120711030750702c81e50446040740510000340000a2030b06042381a6802154141c001c1c000244c01d00c0c2e100b10040010300381d0365616120b2008002400c11880005280b998003070000540c2d00c0d0f0515061500d0054030011250003070910f80d0821010580114241ba040014000070b21003000e00864100d400305450308020390300c80e00d0803050007048441e551009201150540b5004540d9a980319100c2c010702030040b014048140d48000a00180040440380d180c66114844110302107840f0b4882c510305420a8104507410b922090074448200300315030841e419401e4412080d845d10a21030802900c071018008008e051000c1c8081c083c819101c1442955a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 133103525 1250 133102275 133102279
    0xc020604150b091f050f03060f04170a050c1603121101020403170903100e0c150c0303010e010e0105060a0c060b0a08010f1e050106021c03200d0b0102061009020f09 72
    0x25a80c03d194200742405201184982045a1806030002d0f1750705102c07003030402c2d45000034054541ca42d00d03042c900011402c0100100c0324048800f44011441200758090b1541c030b01079655660300c40311030b02245841c1048030035244106180030307101000060380070240c040108000340b6007000034500c10301c203450190240b07410080c05100461020010380742644058007820308124101d4402d840481d019a084030030320686010b8942110300f850740b8a04220170184811800704c10014641101000351600355042a00029804800000104101c074000c0d40b07403031f01604003194440e140402004d00074201341c40305200203054645a038411002c59850001840081003150020302c0000d070f00031142d000504080301c51010151841a0120f0903020a2041d18142c2c1d80540050100400034104d092002483c44568001c041c0c489140040ba6808401003000342c191961040e9180c4108881c40020340c0d0900004904641c4130030f0412420581c4854844200d0303280340d400507078079504011001c1481c414040c07159 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 133104775 1250 133103525 133103539
    0x1203020d02041202090a1e1a04151a12310302010b030115030b0f092406120604051b03010204170c0f0a080615120f0d0906030c020604150b 61
    0x1540d0b603040001e6044451007210b40105c20b40d90502000c00700c481e280520b020a081100c60544001d090390300541036818030344204014042114000f50135200c0c90038070b030445540c000c3c2c82080100600d004080326084420002424180181d042061003800202400e5010181e034645c2150300300303000800300c0d502407048000c665691090a010380030340240301c4064025803030800004d00c20301423581c07800c0550340e2007202440161110301c100051041c0203400d5060364010034084c01c0030603110f0003040340310384140881411245003c408204004e1640d00080d18070342c200600704000500042600501c07048050a0300900d440c411002c01d0090059400402c0c50002d48160300f0751515002030718103100002181c00b02d1083d995442840504500c0d071154440c2503220f0004551104040c09840c42d0150016218071602c9007100b07102da1800c04030b9551400c0e66085140050401a0310018103800380c8981d0505000118820900035599180204058100c0c035507080c2c1c040c10501a034106900011000f17000d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 133106025 1250 133104775 133104779
    0xa05180f19030510090203150402040204170a03031109060d090302160602060117190303050a0906090803071701060f0e060c0d05030a0b100906120b04020c100e12071203020d0204 78
    0x200c00c0304610360100707458504c0340000c40d4001e0320b000d0180c0d40c0103990160180420050080b1841040345020344100ea00c2a0280720104d013800c0c21011500c014480c00c001070400c0c0c90740d070501030201d507810b4602d005086803c000512058607107400b00c0d41082d141407800500340c1e2107414124100443c0001e24a80006015030000b03000d940040c150703068480242d05002c010404400080d40d40c3c6020f402c603e0344002c44014507001c01c5c001c2e409540d00a111180100341d44103d60381741c20840d007030b03121300b200e801c540442032000060740903071302c92840070001a140c4c1e90341d4109400a404224510020030801c403441c1d00004450b1500130503180c0b002200703400c40340e69034201d9070041d016400840300c8507516440d1407644c00991401005071026401035403181030015003441c0d81203a030030304949403040d440c548171045800c05480f6031008003611003101010b010f0a14205100d5029181c1040300309105602c1348020420808000c0f00711111150b02520703158404c60710310401d030080d0294002c0001c58134404500 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 133107275 1250 133106025 133106059
    0x9010b030f0c09040b0702010b0604030308040b0a060803030c0702010e0a170d0c0c1502030c1c030e07050922050105090a120215040212010b03070b130b0a05180f 71
    0x1208044880032001e6a510700300c0101c44a41c1e5240c20b150341e41d4001800c10100c0c012821103a9100d0704007059200210340c9803600b40200380a64001c1d4011000241e070842003100340141305030305a801c1040e0003070a104003450000072581d20700016100e170006810004e5450216030040041c2e0001d0700c40504280421756861403110f1703060820034500480f9004042100183d00d204803055130603268001c401d40d1056080c074000000041401c0d00120540c40100801000341070701f0455182140304603a0320041030113040340020152200c0011040d0b040d8002402072003165910708010390300c5802c189415801411680030300d0307100440c030070024015510388010301c0712042001c526014120300420414601d900d0182040fa40c1d401000701c5501800c52840c00700e001440c1c5450480140e0718042c0000c251690154006070405041d580060b0781d40c140055192000500e80350070000801c59101c00c3d41c103010200e240500340c1c0c402c1094044600c01c030040550055031b20f1740b20406139902c000d04011040071750001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 133108525 1250 133107275 133107281
    0xa02040e0a172d03010e04140109140c0406030309050d03200304081504200312220f05060d050910020309010911030706020d0c0819050706060506180d050a05060901 72
    0x102d40905103901c5145012000b944500052000a403003c0c0e02c1d5a10745a41581030b890301510407079420349981488140b981e000d02880c8011800390541c4481e08004003030031490035075004002c034050303820114204007180d044400f84c011200162064012200c0c20702c0c1c1224107401c0c0303182c0f048616001e04002c8000c50000809002529076507412a80c1051941c00420202a81210010103103040b2544400000640c0e440c18400306e40042d040711054030500c2c116992603006145200001103545204490406480200d14024028a640400d04c0d6043c80c0102e2000e118806003200c1c0c4548440101d4003d100c20450035035981e40d212807c41d22030804481c5140601040c1e01c0503900c034594048442d0580c5400704400003110030540040410441c890019545440401003d0f40d220790706109100305203610341d142c041e104c1c541d9034505075030b54540c3c6051801c032032460300454040d4209002e44449a101c0c54055903030700d08100e800340143c1e41580741983c1f91020b1031500425500030380040c0480c15038150 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 133109775 1250 133108525 133108537
    0x350604030801090b0a031509201314011208070506011223030a0c0c0e090d080a020901050405010302071e0602180102010e0c010f0908030a0c0c06050c0a02040e0a17 72
    0x41d4070000a83d036075001c250705131040056800c0d44000d1082d401c10006100c4070140c125048029008502801c40351101c0b0b80320303c07120b01003100c1c0860f1800d42002d285041022401d1000c042001082880006106421180710501810524598481c01031052161001c29203e070103501c0422102d0968440c5514001244485011a030364500910301540310400c4c02080681a0401c030011400d0001c50141150b4901603500d00313a604180b42040810b81c1401003221a10894040d80280840064440003c042e604001e0200708040d00c14802d02c0d01aa912600315804c8038003d280158a072a000d052030b007080503510a021a01c1d12000309010104a81074000c3c0c21000f8010700d00d541c650070820300583c2a02c4044c01503902035001508207514a41c0510340130420034500d440d041c4030541d2600e441c145154801c0f0106004648a1640703d000c02501e02d03a5a00900360900c7c1aa003402d1f0601e1410b5034a4a06200092003a52640c1c142607804d0420014601020b4202e0b40c01e41c19214542e4075601d140e4412 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 133111025 1250 133109775 133109777
    0x204050a0501050c0a11040207050109140d0804050c0613080607080403030b030706050405040515060a0809070f030302060f09010b030a030905040b0f0108150301060504050a0b010f0e060435060403 86
    0xa610001402e6000381d003921002130262000d4103401c10240e0700c11000307081810f01e10754880e509102c0c6101140c0c0902c10481564441c1980403041d09007201d40354940300105207401c08219038041004005100810642c0d940b100c141c0b40d458030b400c0d110300c110f10b149240f80c01c1180144510380400010640c400f107801e006900a413030801c02451390400389034070743c81280100400302d00200010000c41c02c0641c4150742c4440d5541d9441d0040c1421000541580c2c08072072200c0004003002c0c1400441d0409010800040c808100000c02031851a03078040d40399000141a900c4000314200002c0c0c69960a4100c429903940080594000c0342061030050100d0801e401050b000e249000f50801c45824010104032000d00c0586514031195182290100c0312501800a2a05035403202800103560300c640c000c95001c0e070203001020440302024400100403511407240f10301006105403181646860310350846095506440c0e010801410400c101800017103040c250401d003450300c003404d00c0103403004102240501c1c03003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 133112275 1250 133111025 133111039
    0x40503330f1506030114010818010908030f090c0901030f02030c03120a02100e0303040f03020a0611090906030c090604200a0305010303020f03040302030c130f0f051503120d150905010603020405 85
    0xc510b040c00182d000900a40404000c8076018060a600a84c1c0b1307181c0c008103a9220046100d035240300c0d03038203440b801d280807522000c001c8207100d001155010410b5000740c0841c004c0c03952040c6203000800e11101880060040d2035103822010954800b841480600d800c0a03040301c08070808400d1019060f84991003070401405604805620340c807080c0145103556040d20000c0d4150b484d40c0e121000c20358031442c000c4095115040c840000601103024000e500c4461040c0d180e01c8051b40c0c0c1c00e01c10055402000d040c0700f9003001200001c3c0e9943c00494540210040e64001440c0c0b40c04d42d81c41c90441161102c1c500c421802094400032250305811450580744a03170f003038844508514000e15628080c82c04000d5140d04400910640360808403040440320480220200c0c816189120810072154521403010016880d2020411032245504d600e103504081a0010440d00500c0313030810145010390911030100c29251401c40405d94101d070442005458a05000c0000d541e444030080c0081d44984913441c02000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 133113525 1250 133112275 133112311
    0x10e0312030601030c1806111014100603050915060f06180a051804020d0c15030c0206070e060d0c030912020f010507050306010c060b0301240305010b0402040503330f 73
    0xc844e000c0429920040c01000c6d00090610a040d1804280d03585202401c2c45100d49114540d411400360700b58071220861480b6640c2400040c03040968203c1d0000400d260034002480356442e000030340031100c40b806010910075505e69034001015480c6885941c1d5001c94040303100c0b940e105484030104101681280c180700525940c205120410301228004003107031901c41d002501608256122504280c81040c0141010b030303e0300800e5a442c803100c000000013070798400c80100000e4040200c3da42208080c1001101040101e00065041c440d496940b080315441d10700b0b00038800e0081d001000703615400a4010f000d240c0c00103009690302a036040001c1c89600b00004108030a02400403a80070b640c0c1a074660180300b590b82c0f900301c003402c201209150559a03d0b40c01a002d010f507014a4a01d0440b1022881802d030300d142005425211035141103485507104010410aa036400a0305088000d0101d051102011040403c1880c40d0744817a241900348103840d04005024120b40d8803a88a1140e901d5007400d04d40c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 133114775 1250 133113525 133113527
    0xf030f072c060a0b030916030b040b0a0605060d021309050f0a110a0f050c15011e080105060604030f0f020603040b0402011205040510110f0703110706020307080f09010e0312030601030c 81
    0x807802d40314603810102d01481400845070302d600a550181000080f0b40348854171920f041c80d00041c030703442915403c50354400e006c200600c070440e05402c43d1140c48144500c5041c01c2c002a003e1041800415110354001109410854180000070041480280403c42841c0408558a20b03400444150420a103003210f0040600880000d4030031040007070f81e4203016466410010f4403990b000f5102050540700d600780360080001c0707041d0703039038041d118110740c4064142090107040302010b503d400c0114641d041800b0000c454032440300b690103ca4203d145928283c215050105400d007040d88060341050f00001084184041e42810b84c0c0203078402c1e03903030000405040c50311340c08440c0180c43c001c1c0307650451031400002034815040400d0301c01021204502e0003440b60400700880d448890110b01007641d0016120f414030007480764800400300c5d40041c0d45440070954416a643c440d002510b140304102060414440c0d101c4e40460a0180000e01159640c080c4030094503000d4004a506500080c101403004042ca = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 133116025 1250 133114775 133114859
    0x6091d1501150c021c03021b090103050d080421020109031202090a0e0c09060c0d02010e03070b0c0313020310050f0a06050f04090f08070b060a0909110f030f07 70
    0x2c0b0000c000d00c4400c0001d602c0c044849404000099030f100078900d540048465041c484010f00c14842d80003404152108103005030b551000b1400300d440350401e01c00410100c0d070041031801d401156803070090140c3da19850200758242154084440450903100c03416082c0307405510411806020707444e0080180c4c154190385060344190605a40c100811203810130146002141d030f943c00900001411342031441c0311000c1446500704140c0c28010340d1084044184198080c441c0c04803481011014501e003002136211030092080c0a8280b01400b6400030003c3c00f41e03100c01c400300940b40c0c0d0041c03d035011845404a50806404203417210400d0680c0c24000c50f441001500c031b01001c0b50405811695414a51400c200091172501425030708814803407198400560303110014000c543c0f21300020f2090b420300d031f024010182026000110031920b0844403001080703160164150341007003140c0110801000c1b0010034107020070380d071595040b4820014041140403004000c0003031024041c10040103110303e03034418050 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 133117275 1250 133116025 133116029
    0x20c040c02031e03040506011a1603021f0b181320090702010207030801150903110d0f080a021b06090405060f03060901020406021b0108190207020a06030c1d01080105010e0406091d1501 81
    0x1c1c00030800c040a444850307003001925580c04cd0040e41e0040010380d007581c8100e44400303254541740fa0b41c0c4182007001e15050080400c0c100ba002c03150b140d2072528284d56040320310300100150240c510408401034200d803c0c5015802404040c01401842c208800040d01079000410308801141000c4000b0401c084450808483d00c6000e42c3d801c0398a52550712030400d8440820000354000c901c0004210115018600d001751003846000500da55150840009081c800c180351050702500b5a641e0600080e6a80c42c1641c04a40d001c4800080b292540b50024201a00c241c038001d070103009510400c0101c01066006c0d00494110782c00342d814110302c009140144480810155010030381c07240224240c140852182d03c00740d1904c820041c41c200254000480c1003000794001d0b000030340c488000c008599403100d6044150111700c0c204120004840c00041e100f03000c1406858104801411030b180c01e03940390b8100d5001486020010403003220b01c1d01c21680e80141d0860540700303c1c82000348845000709148842c0e81 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 133118525 1250 133117275 133117319
    0x7030e0309010f02120a020f07080705062506050906010504200a050306150705070620070b030a1d0c03070f030b010902031015030c031506020c040c02031e0304050601 73
    0x101d0450030324015100f540f11a202041188070384008844013400250041005104030b4000304051650240154684141c3d03800810254120103820000c1d61500c03800e4071660200d034142c0498000462100c2501100d05a201411140c1031006000d04a680402c240c0e05a40d42505c090201509094442c0e0041086603e1002034040410003403594504c40c50246411440c0100505000f1050021441054014032400c0c0d84076044802c2c1000740c00d400c02001d28180600304400145c01b000f034004c80761140118860590700b010000f000032925659035200d40d41c0e150390300204152001c03407840b5259548c0e5902008c64081c0c0310354840452003a070715109000072240e10a600c0d001c182c0c01c005866002e504080d005800404000b840800d50381180f04803140070234020b40c0e000034615403400d4010160351460705044a8405150b000340070305907020908a0810b00240c030007103041e5080312802c07495485179070014041400c9003c80c00789048003880c011070040c0c1c060001c60700b90343d8a8100e0101c002c0b0050754010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 133119775 1250 133118525 133118527
    0xc061003060513110f010201140406020d05150105071407050a030809031b0307030f020607020a080d0306150c0209040c05060c100b04020307080f09070f060504090e0a03050912100c0e010807030e03 86
    0x904c507162440d0190780c01181840003142448800340d9100600000ba0f6007161902e40211780184203100c0352045a61150b9404041c25148a582002a01900c9050340203025151000e6005980ca801000600d00400000c0c2030002d03220350f2400c1c01085500b001460784d210b8058900c66900340482c6005c040da070744000801414943d45180d41b821800c03c601c24089030007000a105003405a038580c400500244070400150400c075503070800080490f0580c1c4c2000c0003184044946003038865200300311861040d416a841c007866182c504100442d0f0f03026030701003070f030003d4006240440c000e8003140c91944024003807001e2040d400050200300903400104c4015002030001d600188600614003103c1d50011038403804e540030140c031481c9200307459455400401c0807442c001410004281e0b18400c9150741c081070005418000d5166800500511500ca2402d204a04031010303142c52840505c4984450190031008205060403601c000d8a10b01c880111980410107050000d40c2c2030b80030b4040c54121448c0d110140d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 133121025 1250 133119775 133119803
    0x20901051002070e04140c0d03081f0b04080c1509060f210907210507140111060a0b091e01150504030f1a0106090b0d0b060c061003060513 61
    0x803003a1505048015000c6104244001407000b072004a001d000d41d015010142c000e1b60140e50342d629180383d05480e00e005814019100c00800d5015440c1034124600422510164000300070b8100c030004290002c4102d418000380001c0c59500018404c0d0080409403071014070041d980060f00300e0760285c5004135030400c400700f1400a403805204c2c0241a2032040340c4050b604819001045650164110380b415010b501c00c0c0342c01c0c005840c1100b442450a080403c0a070021085956001c1d01c034984c512604645d4050024400c206070300610348281d10341e0100e000c6600514040e072004006e000c408410340c0c001c40f0807002081d030107100100f20040350303c3c441c05a09401d034030b00000c1203c0300d09912002070030084103000c0803001558440d08020240c3c0245d10400d514022007190007201d11060384144180000b8a000700011800c2c40b0580d0074081c407040d400070324407440a020911512a90020040c1030203140b00300300d45800d443d50310406403401104100030a5a802c40e8002e60050700a1016117403180c200d000c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 133122275 1250 133121025 133121029
    0x130305040311150c0705040608030c0309040b151201140f01080622060b0706050c0327031306030c11030405010c0b15040c080a050604112205060412061802090105 71
    0x500b88000018216500c1c1c114050807282d071541040a807080f5907005444100058a000c0c050403000c3d1080c000918601840c451402d5a00d00c101c1c1091400b454660000581555a03010181e494030b12103d03140e03689074007049011305016000d000303400e00f1901d2000e19400d0340c14500000c10414034182c58030700d0f06407160020071124144801c01d4151242d9003400310096500c40e40915002801b135092401e80702c101616040c0180c5000a0142210400a00c10894411000b68010410b80400b140d8103026101081d4002c4c290f201d030a40341e003000c140d80e001c0000c241d94903510040e110f44807544c80e100c0c034005032030405450f03210b03910401d0300040280d80780c0b8001c5064500040c0d0405251584d903041c5042100101d42520301503080c04004c143e01c801044004080c6008080c3d01640072a4100300040c0361400d44951400345c000d041590880030b0354450510544c4c400d81c02c0c058900104859110307507507081241641041201c044510604200c041d00541d1081c501500f41c080c1d00400759840c1d0703824001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 133123525 1250 133122275 133122293
    0x91401180533040f021603081503010213080c030106061d0310060801020702180f0f040206070507080303010f14240d0204030b0f0f0405060c03060f0312121303050403 73
    0x10100380c01c980740740b01e16100640c4101c0b4880c8550400c442440030885100300001c4560050700145041e004011400a03030391101240480b60b075060034080115200c0c5042c030408800d5030f03110160075605c0002d024000c050204555401c907005402120f919482000515013a0b4500c0e10599001c50b01d007030007880608120524521410b14050104c07281226007000c01c40a84d550740c1d00440b4a43d500103145410b5080050801518030080413441c10b580c01c2c1f142c0303268004040200701000c40b6510001007401c40d50f85100700c4103410707040000c84404c540c0711107040d6101c2c3d00a2141900703410b182d030320004000002e40a191a400c4009004512103100780030300f0071044145a4000310600010005110034a185201800207580143c0e1950700ca072400703032403420b01c101d00a403a22b08601c0440c4200000500009a210351284030341180a4494503908003142021032901c0c281580350041c1843e803800d40c01d4100180c082c01c0d001201421464445801c1d03551030b16500080035000070310800050001c141201 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 133124775 1250 133123525 133123531
    0x6110c100e030304030c080706050c0303061c0602030f010612091115120109090c090b092a0d051608010503060a0e1c0c02010e04051512010b04050702070914011805 72
    0x10400600e080407020010f41507510a810481c0c0308951039509020020b81000380b8000341020341031052030040c42d03c0c0c41300e03070b00d02004016520a8503034402a00c40307403412080130501c480d80a80195200d0400241d40e45c820a13090003041d00040d16401c25124101090041e6048182c12900400708001807034107002d400310000c02d4200020700c1c208503041c2c000c40c22441490080c100072000044400291924250042d0030346d006c0308890f0304204032074049941d0f107a803003a000001000d241b2658111080e4080d108808810090943d07100130619031b0b80380f0303015040140701d03002400b10a155042c020718152480030003030060a426500c42000075038005a02c0d03100c2503040c1d04c107501302c961070240a02c04940c1c03400a100c0a400150303200b400401103513008443c1c420340c0c03c8111014046840d0007102d05003055402140d00707110388003080015594482c29400780904e10b40240083c000d61901c0d03500a036031505c551150b40c010380e14102c507456401710400c9455041e0b80b40c0c455806a81c5001c200c081004d00005 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 133126025 1250 133124775 133124777
    0xf050f09010e0d02090f010e07030203011406091302040b1305061201050613090c050901080a14070509010e06043206120411030f0d090e0103020d02010f1701030609060606110c10 78
    0x200c1c01110241e0360380d00b041480303141c058440001b60342c1030500c000f0140c5405031650050500510061104c41c0f13280b5050798a15105a80850700e030803481c4005403452610f0030130000c4c03140c80054040742210198008080f4001580700301c0494903955130620000303224400210001084800050109103850001010032400011841c03600030b44420284084480b4810302d44046107001500824658201c0d100c0b43d40800300314020094142454400000a20300270020307420404005002103260380030b80c0303501c000140c01812003616251951072140e512403001c0020000401d41c2002c1401018141050350884040a000345040c42c2c0c180c5508a4030041c00b0b4411078212141400701d0301030741c6041000103280340107000108241c2101e0360003d0b10741c0500e0340103210b8600c0850010700240c4c950136000c9010340d50a180080d0401074109007100d019104031a54808407444000000a02c00755402c00015103005110411980303030b50350010f4079103598a500c0034200d41c101e01d280d4080e620f0712810481e400125 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 133127275 1250 133126025 133126039
    0x2121204020402070314030108032a06071116090608070506070507030f0c08030a030504060b01030b060405120102090613050103050f06180621060108060f010e0c09010306030c06050702010f050f09010e 88
    0xe02c441186e039034009070040002da030305c08600f4200803000500d403003c0d8400d0850451255040c1c00c0c428a40301c03840205400305010b404041c40d480c0600c100011454070350f44280d96145252510f0706200a8640d510500c0c2e003a208000f0049031504d01a4200c071400c60b131050041407801e02d503036105541440e8460058a03007032001ca00001e80c080d02070004000302d103030540e00000c080c070302072800c68110b80079003041c14101454002e400c40b15480310313004c90341901d90840d5420782009150742000e01a214461040d80c03c50000711706010b0554145404031b0a82c0d100f624240500e550b00801c0b103d1548086031925400b100c4c400b582c7c4107071007405040171703008540078010002801c201e0071074803900800321007540956071144e0010061020f09101070f07a0010ba681d000031155515110680494440242540307000c0c036030001d00021140c3c060b074414801191f00000601c0b00c1641c459000d4903507004901c0681c0441c1042c046001103a12035401c031090078150504840c1801c48600c011224040001c07100c58200c45 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 133128525 1250 133127275 133127297
    0x228020409060507030608070f232101111309230723030721090b01121b03150c0c0c0801020712050a0206010603050c2701021212040204020703 63
    0x40e28001c14022070702070100480d00e0300b005100201298083d6110b000c590304180385c20f00c68010211514001ca603020525154001c020040d0094220110051294400c1070942420921100013052b1080010145c0003080002d03141001042980f00b0400a5285c10421032428000f2603525030100f4400d21004441d0440303541000d18000090070152100000700e045071307075510076251062030740d000b203040d12030946419414042da0191483c40501c1003280c3c0b0800718120601507090300e9001084064200e8461310055940d591080d004c14000c05003a1100403440c1d140d00c0d921100700e0051030444c0d50140d451001060b500e82108001d0021071181010403418074828004104081c08000c0600252400181d481440c0e140c000300b65420800c81400f0b00105020721602e8940205a1a0440300d86003004107440d510542208540d1040b413200c14a004507506800395403603024007502c1940780c6c0c01e030201c030300101e03a180d1701810902920404080804040340003800508003038000d451880d10034103103c11024 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 133129775 1250 133128525 133128529
    0x5240a031e140601080d0912080306060d060308090f0108040f06020c030f030c040608090703080712110a0f0209090c033c0c090109050402030d0c080c030a0206100e07022802 76
    0x80300b400108407640d80030304010302007400180403480f100d00c19421b2031120306143c11000d2009007210040a05541030100000d18291554401ca59101d05034110801201d905d034502107038150041d00c2018003404041c6051175081d405002c17854020394011540300201940781e920385010f076012040d10b01480c002404454420000180614019840e002010343c540f42850b1004049a40007410030049038400e510400c01704002204039141e098000380c0b120003085514505543d4040e031000c0b100080c2c855600b949040c018400255000c883c0700715141c041644624072055603407108194282d134140c110014410407410302d02082140c401814407010780900301c02d2040340700710681050300e02e44c980004440060320314151014030b000d0420314904010340d00301a00442d80d103080204441c0c05003c4030341d0369001441442810344184d07001d00c10460766503c034000d0000391100025520040148620760b0701203100d081e0b080c1c540b842460380342c0c014103001e8416070040c415041004208541980c46c200f401d0096 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 133131025 1250 133129775 133129793
    0x605030f09031905030402040e03030f15010306031e150209130b15070f1103010911040f0605090a0e0708030702030312071101020d0c020c1801050103021e07030305240a031e 76
    0x103243c02e444d4903841c0c2c5402d00600055a1032015490844e810070001c210030a0250080c20707411114800303180301080800c100580c0200b01c01e8102521440180c1d40b10070110f401c1c0080d10500b11311510615041c210940d5000003039004402941d80d10a40a41044c2c80790303c07131540000d0400c1002400444110001c40140d41594000002601d103624855035000600c001d02300c1c0c2007010803040d0000c000402442c0c0300c10985d50342c5039041034440c585410180300300d07565030341214000d8030303008001c130b00c1d18180449428020003449418810b140030b030100000e0035040101c02d13144180d0700500514500500d40f585180813440041019051010080c0014000705c824030141c401d00180c010f00160160404002a1500b411221010b102d40010810024030784800c03c0d480e811600c00382030140e1942d0b035581000c0340c1e122f440d1481c2d411005000ca02001030603403603040301e80104010482007103074075079028058003910b4081181d15001030a0711020800030b254203111424003407021200143d401c0096444c0c444c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 133132275 1250 133131025 133131067
    0xc01060510030212010806010b040b0304140f01020a020f010203100b071e03020102071109060123090303070821040b070c0303180f110103020c1908040302060a09030303050a060605030f0903 83
    0xf0b5011a0200300d851070f541d003840c094625500100003e41c905513151140c1d120f01c1c010304100c200040042010030440c0300c1d0301c0c2d06280d2031a050b6115010750301c8019001390070421003280184120f803c4000e42410620880c0d024110403030440744090301700310503540e0355072050a0484003d1807ea100f800058a41d030b081c0748540d4804d50015985542906120702c00007413041c1d58601c2050114140000d40e81c101c01c0c0d0700020a0007072071842c0076440118924555010354400715403d400000f07400d80400045c640141100401030502400c0c2c2031810140c0760302082c2c00c84008100c100f4860125082c1806010000300040c03180c0384c003040e0018013036522980b2050040c03044450301d442d44040400c00c52000b1003104010340c20312701103040407081c486207981c0701c01ca12103902050051071011014461154100c5002c3c50300901100c0d56103040981c0140b0303c0c42d080c0b205a0010340341030701164006070703540141c2c1d08035034056403500d0840c0c170382042a012004000c0c0008100c3e2100f0004440500310449042203 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 133133525 1250 133132275 133132277
    0x1112091507080c1204060804020f03011509020d060801020703020a030302160f0803060405060405061309230d0e03030f0708210a0617060103020102070303140706050a02030a1b080703020c01060510 86
    0x9201c4000c071030f03a2454000711600c11038903c04240020b000150380305280641c0141c0442e03a140d100626040482e0042c41d0071944111041d0385180040703981040354004003920810322008011050f5200c0c2209d00300d010700100100160044002c150203c0c0c8250041c08070001102d220704c1000750035954114011604820417104c00d80b001c820410503240030b20800d030740001c06a90901107450b0480000e2400a600820302c03c1041c0c2d114005420310070000700c8001c0d41c541030008440c2c900f40d070400c02642c58071900031280000d84050b00e041000d041c0441501c07070240415100c40d05100c010b580b880000c3d005100c1110070824003a01005c81407010b51103060051084041c0040c0b001c0c100107007480341c40340c0c0084e03d00c515803200b001000140da0010b10041182d8040c40c1c011250304c41404182c0b858451001e001c0c0c00f26003803100f80036040c14154000c500504030300b5401c2040804c868690f5080c1c2c80c1081c075413804145494001003110f0300a400400d80d8058907000007840d140c460f400039583d480305121303240c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 133134775 1250 133133525 133133527
    0xb0916050a1223010518010e070609150c02030604050c10090f060e03010912030614060c0307170705030406020d0f031a0111100504082a070302130e0a0b09010507111209150708 77
    0x1080300b0003071044d8941c0b03030a110044c080d0309080c04002f4000040034030a1010801c00c3c54001f10079a4850015118440d90003400e40b42e507800c050900a80d02d0360385010309da1145c1b0815480d0140b07140228581c400700c0e000c9002482c4460714081c03044c1c1d06110b10741401074145d5290b00390341c4001202000d00c0d41c41c0f9012502d0001c1e01c9400c00c400c01c04c11010284415000c0e901c20400820744003000030680700300030340c060400c1e001d0071070502d0001081d020b039290080043c800824045030320343d0041120b90864902c0e035911614000026412810b8641008050f184100c0e2590309041951190301c174091094901c804032150300038944000c0307080301e02c1200e058901d2080072550100030303880798a0881c000910ba01c0f5000f03105c41020800c1e030b220889844001c0c46401054551000344d85e058202900c50500e0702d00759141900b171410540d001540032201100c044d46030130002010940545a803411074034200e001080803a10b80d0284007000d500c4480c54607031180b8510020032000c107158009208580c440c520391 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 133136025 1250 133134775 133134811
    0x303091101110c0405060d0c0308190c02090f0402120718060f03031209060902090702060702151509130c06050403050d0c1a130b0916050a12230105 65
    0x1500464800404090400c035241880b4110600300090b003e1203800e040b1400502e54403400c0019800d0071800038000c0c902044a500041800640350240880c04502b1007070000c94a0002e000703c0f1803051090009500001d030170040f0b100254041040c40d032143c07003e45281e000445420b0807a19048031a8400c1e0b4000d95040c01c0d81e0254201801128010244c1c1c90907a00c00030701f1543c01408404601c41c03200e80e5955a425070b101401441d4000baa900c9401508080c000d0400003c02074a503032048450b0360251017000c0c02010364210b03580049220300700c051a102c10b0240d2280811440340d50240c0352900c0100d03c0c1c1e81401c04110700c02e41c8080103100c03584480b0b0f504c034a1450540d0820406410a509010784034040002040c011001d0340c03c8500d80001f814415552440b0080790008030007070140100c1080702c05c02821a03400280d0401c0c07030408100b205552603442d000c02001e0030b404d00951030420f0300c071034802001904035035850320790217902031000d0203051101c40403070700711101102c1d0303031200709403d100c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 133137275 1250 133136025 133136033
    0x109090f0b190317070f080c0a0215030406051005092419060f02030a020c010804020112060605040513020726040e090d140a090614040906120c0e04030c0b0a1107030309 74
    0x860041007120000c608008480d00c85046c0106102ca010700949000a0000c0520340c0500c4845c84440d030050030104250405e005001690300222012100245040c010034607814510815a04550005266090b640e648031310034200501008031030108100000581c24185d90b444002c1c0400c449200008620700e864202d0003028003d2140d4000107542040046e14209503002c115003481384400c1c24a0070f9551034030b20040f40d90001e210040c210151400c203021030499070100080003120021141501c0049006c0d90842c204d1203203450040103044d41916641c00c52100340341e403110f18288500f4440c14180c0c0c4204a01054000f15140d9403141c0010030801142900055501c6c0507100c4250000d0422038000d501408205a5025030700502218200500005031544c08890183c10000c03014000c641e55a10070440704a00c0c1201107844440b090400f0540d04001d04189124a8140e69801d000c1031007501c40fa541024050800e100580d264555842c20348030a000a202c107c1c42990f0001b503060082c20 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 133138525 1250 133137275 133137293
    0x5070618030e0117070c030903020619030b011701051509060a0305040203010c03291302161104140703020d02041706190506010917070801060b130509060109090f0b1903 74
    0x11000d0600c00140c03000348824a2502d00340781c0c00005e40c03d041c400e881c018202511803121030341c0000c0d405440028114405490720007800308140468a06001e041c400344019121550038400101900b50b5142c010082854002003402d01c48804000706c901e049296400300d41d1651001d421070010030317103075021710046003401d00c254001e60906280820012940d02c1c580c1900c1c0340c03000003101045260103441081c599a09074060400c8050800c210b5988041705103c0c103001452030016100440821a00091410140550111050b0f110240d1810380d8031038130290002d401000d40c542546500703000104060300d42441c01040c83c401303a0f000f0f20003403505001d0600100c0362a1242030030b4904100502495903000307081c1500b0344606543c01080c0d003610f044030b60f14203003881d03200c48030700d60802400040059444000740070a0581c070345400162503c401c01d0050690055442c0d5001880803c800c00040d40e543d805100080300f001030214440d0400ac00041d034040b002440503080c1c440c24a030410030007004070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 133139775 1250 133138525 133138547
    0x40e01060309020603010603232e030305090111010e070609090e0a020303090f031c08090607020c030a06090206120103060b0406050a080d08101d0f060609030a030f0507061803 77
    0x3180500280c9243c0d40464036900040c0f060405260f110014200202207480e5821294020b030b4868840901d00140000701602100c0030510005500c0c1c018201c40c01d1114202c041569095100c40740380c44885001154481c074100c104000556032240000741516052104500510885d03031612411410615042c040b02c1c8103012120040d80505103580040e00c001c002d548174440c040700c08022801d2001d01090400d103046005460403212050741c20303201030700003001d1400313401d80c8811601e440c0e0b1484400d903900c01410b03210315819448201d0050014001c1c0c1c20186640303101409042c2411070007c4052003680e420307002215816225194a1180d080902c6103c00071704046a607200e0715450b020a42d0f03124207046240c4030400250000082140400001c24801000340c1c005004801c500a18820340309030060310913542c00c18580e008142e66250000075124408001000380110000035034094030700e5080d5a4120f41481030600c00d01c0701003200b500c615607202a8a02c058002d82c4030f21300d0010441c0c0049 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 133141025 1250 133139775 133139777
    0x1208030703060504090510020a050f070507031e0302070311040207060e060106021c0c020616020607060506130608060628080a060b0103050c16021c0602090a08030c1f090503040605040e0106 83
    0x17030084008558001a220681002c1040c01a074420a1a50442e0279201345805106040e000051f030700c08120001803241e04881c02144180290040001180a40f0b041c80300094010b030300c101001c4c00442c003135062855450301b008100500c0c094041d6610001d45401500c1128907070041d00c01040b40c560180047e020250458409040d51014120041e110300501e01c1c002c1c0c01031101107074001078000042c00002c02d072600241281d80320751441c43c141c0302030002181e041380106c0e8105071200202c500d5000d5142542d15442c0903203e1581c50360f0031303c2820100d18450fd100302c6c1c4004041d030101c02c80360b2220805490401e000e0441d2a40b1401d2500a40780701c081c41d18101441c2c03c041100b45040c0005070356001c1d00d003032807544102c00799000142d900c070082001c18800403014002c100400501e17600400300e65200b990300c005003a507504500d580380d0080a4640c2810340000d090300342090002d0b1603100d04102d200c2d03c001010700781c5407181442c44d085500800b000c201c00040501001d055050918010209 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 133142275 1250 133141025 133141031
    0x30b1f02150717041506081f0b0108040f030314090f0111030609011509080d0908010c0c3f050418060807060e010c0f060b1e1e0102071208030703060504 67
    0x100010041c8000050b0b07007000003c3c554403002c01c00300720040c0e4500503032a03841201070040c5030319400f1240d00c0319054032401407504078100740813074602c000c0d0050400c2d51505850302407640c0e07100c5d00c81c102d0808450808404055441085025010303402c4d1b011400390403068001c01030b4411040000b421103941c0801100440d200348208600340e6500c000300e078191007c0000c6102d145c0c1a42909a400040340d4100d00c41c503000b0f0b81010702c100c80c2c1c812241c000311140c050090040f26100c1030241c6010018560103010400309104241c0c000100b00c1d00c584102814255080e040c045c1342160807040d1103910705480010302d000600304102d00e886030082d1040305441c40b082015074070340607809580b072801b48242014809a0744072a0460303070081c6500c4640788e42001803244411040e01d040001004012542842100001002250880c895078910054880a4004521040300280e2105020b220000060452160305004521044d801000c1d103003c920400c5080d4403400d0080c400360540d88180c1269004034a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 133143525 1250 133142275 133142281
    0x415050702090403110304030b090307120c0b07110709020d020c150906040303050c09040f06050301050705210603010905030c0f0c0925050c07080f010c050702030601090507030b1f0215 81
    0x5950740603290000d44c58100010300d0100ba41c2e0460545c01b41d41c0c000341c1116030500400084c608080006c182c0c45110310b070303900341d40e60030807406803241100c84801402c004c2c4000d0000300158041d86120170109020011991860b5440e00a071003a640300603021000350780c01081c820355403001007241815050003103840680c28a083c00040e036a03036400500c05010541c80d1400b0490092001c0225007800d007018005010440b00301310302d48041c10543c801c2d60b00139880c0c0000035542c030780716a06035010b1010114501c0c4803000100c1c580710a600002d090654155a03520310440040c10030802400b1140c100005030621841001c4e0305814a07150709002c07070280004504028541c4503a48075607a003103441c0710f4540d890508540040342d4600400340880500e21851340040380064001520320540d802c3c040091011002c507260440d114029070320002d40560003c1c005000c0313440690011a8040c0b030515000a056200c18005900510356100d48031403403c0141c0303120031680d03040c4200c1030084107000201425003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 133144775 1250 133143525 133143529
    0x9050a0902060d1509091a070e010504090e0708061017070e0c070f0c08250b091c08040902030f090d0813050a0b250201060e04020d0f060905030415050702 68
    0x3118298120882c59503c4001000e0350b1241130f0660003914084008101d00140c45c50000c2e1061032541a0208584d9450300003400c240c880c80010351104410380d5030341c0c107140c41d2208a074080c1c2401100400140110000869240d50030404240319908581462108070729048500c034074040e01c40d42d45120364100c800c1c14060f01741c1c80d820054028017045425540c60100342030a141c43e81d0117072070040044840580c0000c40c19400105a021b680d03104c0c9441d4108540044c64401c8074120344584c002181007800440700c5441d01072003006100211480c1d840142c01256204c110682c495080482d80c20345c04800d12045008200307115500443c0d46000303050103444000b020b0100300000740007049140d08074108004001c01840314a846a502c1f00030014242030049008499190032031803103034800c0c0308103846c02c2030750300c1405100100c0d94207582114645d282e540910500c003145d04005d0302d0f82c00f0b5850603040080c1051040080b480d000390061510f40d0b0800d8200e5442401e103191000800c00103214020142e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 133146025 1250 133144775 133144777
    0x6080303060913020d050f070e01050306060105030702030d0603120e030a020904120e2106060d0c03170c030a030c08060d0c090905120a090602060a022505120a030609050a090206 78
    0x202000301d403111241d90b02e5001c0262402e140c0e0800a404c90001017003902001000600607031314404844c203450720562256041c5080220902c2030a50641c4920003040c095400b8500542c0c000600344140c81c80c02060702c6443e03041d11907641c81120110314520401081c076074499107259465034110003402041000b030b000907002140107040035081440c07040015503840c1c0542c000e80e426103409080e40c4c05000c504007040740300c522070081c2c0a46078000c000006000e40f601c50745c40401c49a001c8101c07164241107480e424500c400c000c44105e0700100070894140220030400113804000c0c240d960110343c0240d0101c2c000c0c40b80001410041c0240c0000402900040d4400ca0f440c0550310807400004008213641001403500342415888564400001041006564000c003820151402030302225019110000d07450b080b407140034012801c024514207402505521340c9103d2101e04d0080d01107411840d0101000c001c240d210000850200350b4079102040041114000e190380001c8120040040b055190081241 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 133147275 1250 133146025 133146031
    0x140c07031409040c0507020909210a03060f0312020c03191b050a031b051504150905120f1603030906050a03060815070806030a021c03050d050c030103020a06020106080303 75
    0x1800101e1030181652079410041e900e503480d0081050205410000c00940301e5030006030107a024416003000180310180006c1d2043c901c0b00c3e00001d1051000140c254000c45400441c1c00108142e225000080d042d042118a4005980036030002900349514000c06894040143c01d418080e40040d250b10207032444070300c00b8410703003034010000c20054a0031410b00c030094955508120f0380401c1da05408400d0040401040b00d82400c103440c03241300c441c0c60b00c080240c0c100200029002260003040140305c43d800602c0c19a01a4581342088028580c0303500010350f5501c2c050300740300303441d0b403248156051880080006045103405845901ea003941940c071b0050804181d40140820310100003201511248664880001070034440f003034985d0300c0e00c81b698501e4401400e4030030710b0014003400701240d8a8600818000e40c640d900400d41030021407506002c410703039076240909805000d414050451a0350f0117004151094039440e84032680c9604503c100103420030075401050840e032512100780300b044c03000030482c1d030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 133148525 1250 133147275 133147277
    0x105010e0c18030313052713030c05100b011704020a09021c020a0c02091f17010e0610170304030c0e04020409140606120a050705040c020a02100e010201140c0703 71
    0x80e07901c0c04002e020704410100030b00641c0500c40055203260b5200043c00c0202601d80403581c156003401503000c84046407800b00c41c100800102c450100e0582c100986205108500c40d05118007000010b8584074203000140781d650301ea0644a502c40c0a407980d00c40340780b40c20284140030b8030701c660030582c000c2480c106d078500500e10b0550b070004094920207218007842c24230610400d019503a81c4202c80005110800f0700e001240901b010310046041c000c04c0d411800d003685000340c440b2102c14a80000b061104c503104000411955a8a240d40742178030082c80390900c00c01004920600e840c2c81d1205105409456180000c6103030000e02c41070000421000c102e604075081e5400c0e042260301c031400064010160008002c00006069000d079801d6440819480e20908084a8071840c40788000001e83e21101100c130020b2482d00092420300047c03819030702c21068052148125213407146c490740410000a8100100b9000c500f520000c202e8560b4240660310444100c02040005170511040c4141a4000c00e40010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 133149775 1250 133148525 133148527
    0x60408030406060f060903032c0d06020d0207050708061303020d080903090402070b0601111207080f0408011d010b030a020109060e0321070311030702090c030c07151d0105010e0c 78
    0x1c00380041da8008001500c1210143c106180d992000a00305030101e2101305c0205800c10144540c0820520012003255901222071900e610a10304000814040840c101c0303100340c0c280455401c142d11840038120051180380100425410403d48a00c0e00c00c0041c0742c600300001541d03203603002070750104002001c9030450411a07965192001c829055001d849003068009101103010428800d403458428003031802030301d03421b103403484c825191900d500000e0107000708500304106020010303010a005040d9138180441da0303400c0a894610040c25507080015001c0845941001080380035400e00c10f641113031030110b000700f031441d002d54006410702c01548100d800b48182c6500d240e506840c1480342101c13982c110852040343d55240c02e54052b4503040010190002044600804003520000044132800741d0010030211065546181c04044c0b50700080c00702603148002c4c00f40400050700445038410746895250701251654811081d8420b040c034560f000401603040100420201c8000c9203543d401c01d20102c12a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 133151025 1250 133149775 133149781
    0x11b0809280804030f060926180406030606030f0203101817070f0309260c060903100203010b180603160302092404081c050301050f0a0306020a030911060c06040803 72
    0x142c036090086030310181c03134440e0440d680b41c1041041d43c030400ea06849610500c240c070524461441c190410a1021500e0f01400c000b001d40d1075000700422031140390024000320340c081d2280e0351441a0340310381d0300803100c40074100000800c500d01400810640c500741380b42080004524183c060401c01c4c048030207000c42c1110300c11400041300302c400310b82c0d41d141c00c2100f961511000f0325000307110100038800d00b00f00e96640114105007a280359152120b1910810040801c40c0a1100704a40c5a0050f603a1560600c59485207a4030359400c0d002071802400508401a240e450b030036110b40000024030800303441403008004010403420b0320300321081e05114520f00161940701708004181c0001c0e5503480d1a5210a20141e9900800e1055004000351074901e0300751240300d2801000040e460104440b031102189040c00140541d0070a00641d02d84480c000b006d680c15a80d407030b2201c2c1e0883c0e00224040d00020f440c0c0b5400000c1c801442a031621418040e00e00c2c5203043c00360040d541d103885003e480180980000404 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 133152275 1250 133151025 133151033
    0x60f12051506131b080108150109230106080108060c0712030b040b040603060f0b01052b020d0c030207110a05360f0a0e0c090609070908011b080928 65
    0x90443c0480412408110003904546403000050501107042e000507280301c00480c602101050040c145981106081d515034281003404016200e2106d001130a00110007141e081451048800707402007902d03403034074003055040000c100e05048008201c2c480003103080101c02d00046840802d222011068940029403103211000030300a000c1c90001507600c01d05212000c02070103a25481440000b480180400c4824286001543c0901604004040100f101d0741c5000e420303907200d20b640043c0b01c8544401858031100b1700d00401111602420340002a50100d01d400400c0700f418411009004c0449142c1401883c0c20000b501844600700070046800440b0344010300b40dd02d48562030010403c8185144440c80c2074005145642402c4a54034035583c00d10524a01d04040455621100c1c0000703445007101e1703070b40d81d03062000201001d001d10307007080038803031f000907861030281f00d516803c840c8130382c03070b94882001003400500149000c0c04504c1150000c2402e6040001064440000050b42103a100c00b1401b82d424 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 133153525 1250 133152275 133152289
    0x708030a0b030f0f1605030606060a0e090103060614030f0601151103040303020a020a090c140a0e0301090c0501030606051312080c0d050d06060206040b1503071701060f12051506 78
    0x40c810b6098821901c0c0d14440120200e080783e0f4081c0310808454000c40c100781c00c403064014a1140c40e4064100e5000300e08103043c50401000011100c0c100100c14a040101181803110f09900c2511065a1f0f000b081c0109042c45c1420090180e0460003070000c12194011552502410722860207080107214104040314015281000300070804025240c0b0345580f401c0194503004410745c00c03440340304441d40103e03200d85903219681d20340d20b055460360108182004448030981c031510141c13050003006c4900250741d03642402490752051007032030702c503014602c0c0c00000360a40715190420707020301009014403440190300c1c1c40f0940c2242d191274952103000030b06042880f00c5220342c40c20700ca11400b96420004691740c000000744a075600c0c044042000590b03d0b54100d84940081c2c4000703101171030801c0410210045804051142140181130360704091382c0340c1d04200303808a00c1403541000d9466000401911104180300c10003400c94180601c10140c650303858a071034041c00514800e001050001080a07a03c07102d07 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 133154775 1250 133153525 133153541
    0x80d262205100f0c110c01030b011704150507020106060e0906040207150219110303040b0901060b07110a0503060705030c1e0a0315050103020f07060228080a05090d050708030a 77
    0x900ba508911160000321000d0140d000c4404030160400900304682481040c20281481619000e06400c40201c001100603000c0819040d0402284030760700c17140000d0207580c05004030320600f24a03040810070354440081d40d100800c14800e41e49849410030026030041c0c04c03507260b210212000342c81da03130b54a000503009000310781002c3e0403003c1c80032511b44158426402480f0449030858200610803400400700e88054400c1710040c8150401c4c000301e800a4402001c0c20342040e1030200118246403101501c1190b40c00040782a01c0101d0084100581400c010928070058081a03011b418a460b16101c050710310310000d050201d140f5400101d4040510701c0c3c1c540f1031649144403480b00d07070f91141c8140042c05010750310b507000103c546100c8005615801b81c8211040304402c100360754284001612141c0080d0007505030100c941102007000e040f5501307801c494503004107c6807621451414041003440856070001d1030411aa804000d82440441d004800e454005510180740d0f0790702e544821a03400508144 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 133156025 1250 133154775 133154783
    0xf05010e0f0601030308010506130608131b06030f05010e07080703092405090606030c1002030412031808060105130509151014010c1e080f04080d2622 66
    0x100c588031031404010a0590481c5d0107550380110690704c0380d041042510444061a031414070760300d42084210300590314542d0152050f10a000c1031b0126407a64800c140c54920010080e004410052020581520031440c0b14803503103a04000d9981058030702024400007030804000d000d40c0360300040c20984250015486284d01c03690f044100610b01215103001c602460036030040c20f05140c000380c100b41e4001096445840e004008201c1000f814060201e00d00100342e0b040c085002c1084082001ea4841d0070741002070b40309981da09025000030a464030031006a81103108141c000b2001041155a0101e82588209405000240540f518403800f494001054035080c06040c0c2d22040044050410a40398222246e100e000c145140f40c403401124001850800208421405c41e100c01034928810b00100960384100e107040d280c0381c0d00c580c0903d00c540086d80455916440800c2c08200c0d140c0c80800e0881003025680d801001460702070b22601b0707130a0700500510b0003400d040c40c81e80280000c003464980c0c641e00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 133157275 1250 133156025 133156033
    0xc050715021b011b0305090c09040b130602030c070201020c090405030f09041d0a110f090f040303060519030201090609120212030f0706020405090601020a02060324040e0f01050f0c04030f05010e 85
    0x1801c4c140d074070b03000d58040180700485d1400e40050700c0c0d007101203450030074034000a2101b40c090f070b9179507900914a1b030090003132480201f0205040000940500c02123004402c00e42485440b50b50340e100082ca015400c01d0114082e603c00ca003840300190300042a03030400c580c803090032a101d80303503800810001c00c50000a0a40034070a4005020409404a0045401405041c0320002c881c404c509000e811822030302c0060300460003000280e02c0601c088801d60300309101e8500401d4080e0784100181e501070415420358482c100e0480208119a0010003400c010501400c04031140d13481e0100d211340c02d805030070019001c0d43c06880090300d040f0701401154940140c0b48012500c0710070700d09024000750414002d441c060f400c4a07001c5106507000045020b0080c2e07008000d146596034000c0e90114041182c1103200d41144011804417541c1c5e41d5000d4a070320081c0748002004030103030f9090041d080d60000383c5048000c031242c0080c80b00001403c81141d059940200f013800421a0500d00b1500601031101010001e020b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 133158525 1250 133157275 133157291
    0x70c0e0c0904231623040302041e0509120f070c05100c11040506090705160807060e010b041b140403060e060403021c09030b0402060c070303120c050715021b01 70
    0x203581c185000440d0f11800604140d0756402c00200c201a03240700300c0d0b404621142080308202c01a07403d605444002c4c1c05025040039565808141691488680d0841c100c0c202803500c601701002d4450542c1c4001c006000344070011078101644024491032040011480c1c0004070803092085082481c1c00402e000b8155504100d50000014142d000100c0d046031341c5888450030710590b140500516010300c40003443c002a80d12000360035907159210150320601c0100ba40c03016004130b1000b50203003010f00c0c007601c00070540700741c44003245e401c5a14140c0101c0c840c903c1e090a500c08040d0201420750828010f080881010302206581020360095610007030510b400e00e082101400300210303a180c02170b0310079002c5a07800d940d0340005c418070100002c0300e0303000500b003040100081034201d8090740d006400a001c0302c0c074007201d49101c030741090f100d6001075011030610010180c0b2034109204151000c0e0841c0351050a182440e0b031140c5103040b10500914415401003a03000c401d40c02d00051f810601c620f1002000500 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 133159775 1250 133158525 133158551
    0x14010507080c07180c020a0206120417070f0303180b010b0c010b0a12060e031c020d0e06130203190305030a020d0615031505010503090a02120c040f06030c0605070c0e0c0904 76
    0x3031441c4e443c1c51403040c1009140e000c41d80c00010000d40780c1d540200901d060000701a1000c05c0c029002b80265200314944488a040d0600329000f0600c01e809141e40140c44a9603080c098261800c8c500003000d005030380300c1c28601280208120b24192240801060b94a1004070300752405044c0c440c0003a41d01c06d040150000d0750314558894080c04511030003050100c8114040c0301d588034041d210300d0194030f08180e5010403c80710142d00425400c0080c6500084078102c00c00110714101c0d04a07150850300000b8105002075140811006a80d090180a46209002c0035a001000e0340006400c03810310540114404020001540141c006032850700c1c500f142d01c1d03030f0f0707084000d002c0c02c01c0001b41c10b0004a0a940440c580d44580e00f1a03100d41312000007031107610754550034403040141501070700300b147c0600350007221165140e0041d81400d059400000c01d8403810341c2400c606541d0258009018041c0400c061400034880c626140e0441d044405004095039448a2401051083c0c01c0754a500c40c2c90b02486000c20 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 133161025 1250 133159775 133159799
    0x3022109030d0801031a100314030d091a01080d050f07020411070b0403270e0402010e04020d090302010f150608150301060e0a050601020c06030a090f02060c06180714010507080c07 79
    0x81c0d004043d24a8607084601d0811b031810340075294200341e015080000d1002c981c061380c0072074500785520126442c21403800790341c800b107c0407100304a5560703a070000c007076030070621460f2154090070860012705291081c0722800340403031080941200442c203010850340c0655a984d4400210909400c4c51903580f00c409207030905002e10111011001315600e0035030140e0300e0310030303038a00560218900d032910201403c2034480f407280c40000708200e0420010345aa402c0640343c034000b0f442e50b82c2180d0b4002c81c0300002842c001e07003920004101c20070b0803890040944844c15282c03024500301c500f80e040000b4152100300c1305034030b40e002050100b0380540c207202d03000581c20b801f4000c60384107880005040085860311401243c9845441d4961035000d1828804115103005030380c41402c142d4804d00d4045000b1045901051072034010320850600f58202100b000f01c11025026010b44c1d0603110806424028200440c10348020729001c0c01c241007000200e030803800c02184e541243c0704180f8000440b408180e481e9201004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 133162275 1250 133161025 133161029
    0xf010603031106010e09060103021315060e0406050303090a05060901021c0c1101050c0a0816140307060b01180b090f061207111b040506190303030209091303022109030d0801 76
    0x3144030f04400000c0c5030f860041c07094010aa0800503052a0f482d40d003c02a0505102c0441281c05940c0c01901084026234498034005103c240c40d104280d003441d80070002110300310b070700c024020781041141c10910790b81c0c2c15008094910454083d922109800300403440c142d6002c0c1d891034445034101e001c034052504180c0d92181140b103540001d4400c0340040045803a400740303e0304000c45501082811700050001070141412220325048a0582c0c2c1168071445140c491f8800443c00c00e0f003000400c201801101d00415407588000e007071030140c0b103640004034076911200384112581c0c0341003c0303001662951101c0c0049503c00c0f00600c40c1d41c403400b0300e840746d048030b42041e43c0160104524441e0f40740109404101ca08004440d0118180140107803014840030703000081010354000d0100a4010034524211b0080c0c025500941d00141c98445080c18040d0716100540842c551000102a0200080d400a008015088241003140c14100512400003e6000300c0d46401d60500070b2714001007006501c41403c41c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 133163525 1250 133162275 133162307
    0x1103030103110f0402090102030706091b0902030f010605040b070b06041d0c090601030515010309050316030f02010b15030c130b0a17180a082b0b03010b010e010f0e030f01060303 78
    0x10f4003c0a441004100d1154145480c00750704140881e1000c2981da07400600707424041c600d005404c400d40c45a4140c05450344c2c001980da5503002c0184009901940c00b80da0250a05041203890142842407040103400380c0c0c040100801da51600280b455211034200d404c1c10049042620384140803000d035181c0740c5d880103c4081c020002030000032560761003400360b071340244104000b0902e4060420011000380620800a0300e81d8031041001441e044010b6a075403440784e01035592040490740e0200028250fa40c003050291080700c2c003215040241180c041181e0b00b182c000000541d6480c0f00700001c141c0324100c1d5101c1c262900307020821818607908443d201e0214a0340c540160095512825511092404c0500c070700041c1c3c1c44000341c03030006003001c0001e0200324440284070310031603008070120692420a844e00040f950b11031154607150b00f024002c12400c1d10090800e40007411101c2d00007400b9031041e8422404000d06902c05140c2510180150109105140001c2c80010344a003000740c512450000c0e860 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 133164775 1250 133163525 133163539
    0x1021207030902011b0b0c0d0603021003060509010e0603120901020c13020a03200f0c1606020a0201111b06130909050c010e1005030c071505150405090106080307060c110303010311 79
    0x31720110702640c415030450b64070042c4132256450300021003401c1e4001c50000100710365a04008000f42c1d880c07140c0b56400c5581d0f69000700b1094203050a205603c04180c2c0403008031001c0c40f05111141d540821106d0800f0403460032a42c48a000800407854001740b80d030b40b0364221064082d43e0141c22000d40060030000c403213031030600c808a80c0622021044004c60381c55407566805010074044a00b01e240102042c403152011208640103006541001305400d900010259001e031407520110358104c0c80c00f8010500c1c035406003421842540c9804c0e00c0340b11301c5040c0d9200d8100094600000e0b401c026401000c1d200d60401049204110321b00650764400411440c0e010520600315900745140c19010034641e501c4039900e09083d5168006610941e8022050803a0002c0c1c9190042e499014a417080c03611620380a1f0300303000680407401c2408100d500280540b001c9905018080c015284000100c0d4081d0b54407450000c0c010518803001c0300c00c121505c140345024080040000244545078142c070089070400ca41d41 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 133166025 1250 133164775 133164797
    0x31b08070816031101031d01050a050c0a0e0103050c0c1f0f060f0e060409021005030a050705130308210f0a11040302010c030305060a0323010f1503080c0102120703090201 75
    0x1e542d031030020300304207415001d03042c0040c00003c600000020020006040101e00b0000f4140502c10b649001002850142c2d911000c1149800445c0100c90300400741910a92400819443c0100500c980b054041c1c1415100c5000c124850a001c0c225044103400b001612640b02c01d86c0307903e0840c180c680300245049070403c00f0800854501d803080004882d14001c031080401d18104c4006840c0714010012580940c0d11002c0c400544c1f1200030841d03000c55259201c40d071300d00c2c00782d2042c400ca40e80038154004000c800e10031180710a07003034036500003541d81200c0403a454800c1984c81403800f9107c0c151210300c4010510900918056a030b40700c41c040c45075050140b00304281d244c02e1072094002e91101900044154042d04042802907000b6a00701001400040301d50b900d9448460b844040310101e0100003400d4100780300070813000e00c102d020003250303840e003444055507414110030f8541e4103002c043c1811400049100e40c03450b00750304440d00030400078100483c0e45810b000180040122500c180d020a0824117a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 133167275 1250 133166025 133166039
    0x309010212030906040b07020106050312040e1005060f0f070812070909110a0809031b03030612060108030a030e0703050f070504050c0307021c030e1f140708060402090109031b0807 79
    0x7a43d00c1901d503000144881e58603074a5144c0145009805007007955600c0c81c01244070303101031140c103450703101a120301540e0743c1c58544155281080200320540c010399005047c0400c1e918182280c044032121488103464031044004c0040511500000810450f400209800800c40a20880b4450318003034581201d079980e508401400e0b20042580300080c1c807820400d500509018841d220b8101280b44122403d00305c201c0c011480d01222880b64640c0f55001000300100c40c0303000482ea100c08044840a8156540340c0500156030340142c1484d41c1c2450b403529424080c040c410406000215009022150b0030803080500c6522400341c3d0140354000c3d420400001d6044030510b04480c0184a1940140303807013594032204c402e905120300d8003202015201ca106c40c4005808200f180d19a04000c5000540c0d100744c0600c0d80221030002c0c1360184114091010081d049030444a466440801a10f02507641c107107071401201c0a000b140c000801e641420130740d00030300d585a080c0000540300034004403600b03113803200301c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 133168525 1250 133167275 133167277
    0x8070602120d0c0c060207051e160b071b0b0c06060a031e020a09022809030201090611010603120302070302070503011802210601150311040b09061803030c0309010212 73
    0x10010140503800c1051544240b841d5110400225141c07401800840266988105aa009102c01c1d600c90f88512000340711056007080c020340e8045403000801e00585806da8082c1511103610070403040c0304000c6505001e10000d920602c248800070100b80c2581600c03140040441e030002d05424420703108040008a882c100000602d050b642c04c078000380f0700d9190b04036201b84075022505080b41c101801d07513400035040c5d610340044d008040e0481c14401d20503500128010010008034044d0040041d200420030250b40c0040c251003d40d00d003032a14450505101c000f50340509003550005124440f800030180707015615a01034070949100e07070300341c602c0c40d079aa004150076506410403038003101c0b94503020000145041c603045030700416107100b142c00304010410041d0601109a00003413a0740c8882e1003803c1c2c0580e0511072011081381070800c5c10300b85801d01049268a0050030300b0280a040002201000125000310b40c0c104040c000f42126034401b44194681d882c1d13003144000c0b501620441c0b0b64114001541c4c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 133169775 1250 133168525 133168543
    0x103030e0d020a05040e0a080a091a0a051e040816050f090f0a0b010e0a0b03010302031002040b0a030e100f020c0c120303060f01110a21030506010e04110d051008070602 74
    0xa2068031082d0030030382000005c6c9960351155041e803040c02030b00f0700010642c01c058507400388103884000529140103001002400c51100c2c20515480820418008030380200903903502e4885600b201c40d1402c8040006e042900c01d030340100c500d80c441c00b0301040c00444005050b605880090f9120b07070699400800f4040c801e0001e40e00744803400007440c002601c0d51819407022101c0304051508103d001000c0000c558022200d40081648070303000030052003582400c001d010740c00000c400c1c0c114605883c01d100107e1b6405290580820540c413002c1600004804110007085100000d1040200000c02c1200324029405802d941880d4081c01125041c0e078644071541a81c0c42d1400703c06989503503110020000e800c0800d201890500c1150f01c000b00400900704010103540d8071940030b90907004220549106024404510503040508010400509992110700311120740310641c0c012403d107041d4504859a030188102030035425107043c0400034080e40768030121044640400c260786945032100c80880c0c4030540d83c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 133171025 1250 133169775 133169779
    0x30c080703020d06030204090506090d0c030e0904020d060f0b0415030f020609030a080a030e150402030d030504060b04020705011401050a0521010207061b020705060903070303030b1c0b0103030e0d02 87
    0xa04250094000f4900d8a04500d4000707621130310303603000904981c01c105d42901c0e5940940c0800035800d0080091f800001c08900f0314850828807560000c03e04480c000d0038501655010010070304646404441c0c80d00954051301c00d018144441c0c1e4100014101c50b00014070460400c49580f042c0405150000c0941c0d4001140201c4a569502400510360000300e0039905441000042c20100e2032032805030011490350756010815503a103200482c40c00701200780080c00c0210100611006942c001118200280c040c10702281907500c0e81000002440480306080d009400050141c04000040d4459406150303450b08205860f41ca4405000e1401d845015564104291501800d1711000175141820215182d400151810005030340e0502a202c6410303032000c040810824041a031030301408400054441520000d081c10042000241d45402034440035090564544140541d0788a44001e641e4040080341f20414420781841c08100d4080c0900c015000101324400003005898080aa00000741e00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 133172275 1250 133171025 133171037
    0x606031e100203061305040f0c1a03430210060b030103080d0908070c03021008090303130201020a020d0c17070305031c0b120c01091409040f15020c0c040c030c 70
    0x1808007034000942c0090b00450788070005d02c0708003880b00c1d268024144564451801d0080d0900c5034a044a0046520780022070076010902503002000d5003403066a5100107004490004002095204440001130454986241600c0921750101003807100c0302044643c6d1030390848421f250107001d147e0031160140074100007900204010000704640c0b4000c2c0c4100014048006880d249550b51b003a039036405490105e8180003404010070643c80c2410026a0090710707414400e03010305d086042c0680303910005110717002c002130001107001964801c02c1400780075a406400c2d0400900c6078285aa40c01c2014440d42c07458a0441004011101010602c0070440341d00000642c00c000c1d030000c0300c840d11001c1c13486944021390381d55140410b5544501d10116041d0400000e084400135034000100f038207400d034024110041000c1e498940946400705016401604040301110014003480d04841d010b4841b441e10300204e00104d103d100070240490034144240301140c082000340005001501074503080a0307071402040b1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 133173525 1250 133172275 133172293
    0x7150305130b04140d020d031107020a0504152102190b19140d0c090f0302010905060c0f030c0105060a120807060510051002070f06031407111501080606031e 69
    0x40a010031900107224216000118014241440c581000c940d03800740140d007c240c813507811682500c2080c840481451a20303141c00c02640210b00482598461103025a03980d1040a090300814451400600403d081400025941c5c41040580704205241039120380c40e50565a2074403050303004a03904403042d8407281c0d401d04c801c0081808180c10341c103481d0340c28419a002c00c06101d241c0340000300301603018400000340341e03220000c000b80308101a401100800b12034110501c0940c0e001005242180d00841d0456500c00c5402c0e0507a0800d00400c96a000740e2001160100f0f030041d041d0015485640e0075500031401a41e10481c000c800541400042c0241b0b8040005001040c8142c00055021001c1e150000c0c0465a800200e07010f889038590520068100180070700034460030b006440d0040040f860f050005a503a10601d40260fa406040381d420b01400d0118607921340380a02402d29039506513030141405696408141da21002d049a6542c800c2c090707038102d28403905410000000415071000103086c0f2117 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 133174775 1250 133173525 133173533
    0x612030c0a0f0f1202030714010501050a210614040b060d0b0a0903020f1002180901032d08190e090f01060f11060c120a11030406050717090715030513 66
    0xc0e0482d01507a843d07032940f480c5404a80d40013082000c4141c154021070351418141403590910760300d40361030421030741050010092961080410010380b803c55040c02205281e0030540b00410544201c000d0925003420302a0f034800c85101c940d240315034002c4882c0d41260392450100440c0300080c150042c52040300302d011450100040d40580c1d02284640100c440400aa00da000c0c504070014a50880842c0c0004007441e40010785034040220140a0b00d0380340385941140d4035039109c6100031200c8104240940c00d0309510714080420188072036001004141d48504180c90213486140c3c1241c0940482d0b18030014943c50b081a07000f56200d55084004440d082e4200081203620041c0b101c00202002403241e902c0c1002c070740a0040a01581c0500b80296451302840c0780c2c120041b0008100368507a515100c0c40605000000044941c0f281c0e0101e40080c0d1035543c92001c0c0c0f9003005007580c8298500010702013120000b1b000418000351030010100c942c6035100341104400341d0b00d0132200082c00030a191040c03000030b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 133176025 1250 133174775 133174793
    0x20313060e060d050906090c0a050a03030c080d0204060504030b0903120a110d050a05010509010e01080a1203061508091614040504030e03030c1606030e0d08040201180b030612030c0a 80
    0x120701c0c018903151418841c00ea40c00c00b0b49a0944491034240c10850512060400420402030310640079146003034440c0c40d08000801741801d502c40076003800807244418041040803c215400710780444006c5440301d40325400100150054081210703464424000320700d07103220000660714041315402c42c80b4407a81c0c0b08945400904801419000f8064052041c021400c0603809154410030302d018001030190f140408011070814181c0c005845000d800c00107000380d140c0412807021003900006002220a1114400c0340101800c2d44418001d254038044030301c5071640008400d0141d2090ba0485030920792984015900b280070f8490010029842c007c00d1680c0c3c2029003000341d019010707040c8162030308580d10110703040d07510003802e0301119003103c2411a109071061074494007601440c0f82c20091986510b0105a540d2802c0100405001d01200060b0131a0300c01e0114841a00440e054015139560b81d0320641d110303400544001744183c0381007000380c2c0c00ea44004280da91751241c090081642c802591103144031 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 133177275 1250 133176025 133176047
    0x906051f050f1b07050109050108040f170307020f01060b0306030c120709060e010303020105010e0c0901080615040b0a030e0309031504030e04020f0711031507121e05100602031306 79
    0x501c9024000c1240b074222050240c039042c008400d01c100c43c456220500340c01c00c0302a4000360b05000d0080001d00007660b00182c000d500607408400d01c40000c1050800c032034030184129070000f10700300000c10040e00e80c2d03020030312100d00007000c8000e00009450300288000c0e400200c0f90715030154403408144010703103000b8100c070403224100c6064681598441080c101030b02c059401988044144000400130550709105003401060359101891260805410082c8148614800c282c1042418408520f0642d01e040c01c240d13041001e241d038150b46958a0f80c9512061b0000b802e40c101003494044c00b0030f10000080112000741000801400b020051260000001180640190104001d0320700c4962640c0326403006004c088a80c25485d6194ec0b4240750055203004001c1c0c07054003c0e004541c00851040303643c0800c0746c1103451810301c014074001031b035403001c0104038001250002090755500211882066481039028400c00605012001d48410013642c0e00e203d107000c0030004290b080d8040001500c100c00d0008 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 133178525 1250 133177275 133177277
    0x20a080a0518060309010c08070203070f11060c0a0605012105060f07090306110301032d030815090a1a06030c030a0902010504080f15011e0306050a09050a03020312010906051f 77
    0xa0b9624118001c03402c1904116400706441c0c0d55842c420040ca50032110300381d44500184011071400445946a040007041650300030310914840c01d90f500d00751781d0b5a0580307a0504200c1704403101c4950608080c40907240c00c0c866860741004200190200001da81c000c07801a507000401030065444030b4101100d07811004040302d0400c04003040200015610707010ba07010076040e400a0540301d50641c2807821806002c000781312035041c2c420300c0c0c88508141c000080ca8030250182081c000b9595050505811150b00310380d51a0b21030b00f0441040000141c560044000308022403040700314041c60410b01c8010310003611020700e03441081c4001181d1550316044420340910602d020781c10913070341302105032500054110811058100005182e0421000310482e030040812070481d06560300b004820300d00f48003650101a180d00d454000140400c104c5400070700405500104461602d4a6401d0080d281c0e000520032203801002900001007007142c40c040d98043d140c0080c140011800c005070048416184038174254 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 133179775 1250 133178525 133178557
    0x20f040605030d11060703060612050601120e28030801030f0f0206071406060a0b0703080a060e33011707021e03040f09090809060d0e101407020a080a05 67
    0x1c10350b524288100c14160101d030325000c2c1400b01d0748030250b0034140d004281000301842c0403030030000b1a038040500c413101ca100d040f0020300e071340719000102c440300401c0c0c208440c01400d202e000c240071840026454180d590212290b400144031b0014241c81d40c01086018001800140061010690300b01d50b16500c2c0d8440c1c4440c0c0e0f00207200754007040b41900081c40603034400c0036520346c00000f04824400c00c1e0b0b00007002c9446080142c28030300d070551940500c2e600602044203c00c00075905e810560300100c041d00034510f0106151074a0080a200c070315101185003181c8600003548059a1220798040003050340585503a800c0c501b15211400000300000c29000451042182400302c81c02072056080d2020405400303036235200d04010b040c0e0290b40b6168005501c091030541c4000104191304165040c03490b040b18003e0742c0c0c520441c5514040c02001703200301d0b114000d08000e516108200d038408030306c100031100c100b601c907a5030320002c3e61101c040840251201c0310801c9490a1b90f0321400c002d01d50184628110 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 133181025 1250 133179775 133179779
    0x105090f07051204080a03050f04021e060c071e06050306180601030920010f23090a080102040b030712020c0c1306081209090123040209060903030706090c090216020f0406 75
    0x248072100081e81c0035504417a0004d03444c0c046980c14000c0e1540900c200003104003904056010401070020b40c000e1801030140e10040a42558455040703520b2543c40b03004480300607841d02041c9111003d855801c10020021104c0080ca56000302d0581e8890710b070080c441500c4071007110f000500890020041810569207010101c001140045101140124060580c080d000c01c00005030201401107240024082152180018003592904200007038032110140780e122a0014040b80042c18543c10520312035001040100304040210050340c421981641c03181c81d00d020300c8481e18121310801800f0181034000c1c01c00d031002c50401c907903040c60360b49180800043c0d0907030b108002409c016600b1402c03101070303070700140d05607443c60400b24135030241803640c0781d4042604040c1c00c3c4054102500c240d9a000c3e41c2c010400e20904c0d62041c00307a803641d0314040e09a03952841646049d40080c0001001201c00344410741c000300346260305100381c500f8200b5144072240d20444039002c014040c0e44240c40e86e94001d4807041c0c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 133182275 1250 133181025 133181047
    0x305190504120515010605070818030c09010306050619050102060f04110409030509030c040506031e010912050c07080f1002090a030f05060a0c08060f21030a0903060e01050105090f0705 81
    0x2101000c907000d10040d080c404007200c0980000501a40b00c281001003e01c200d00208e00038001316902b5000142007413103000718450109060002c409012540704900130700001c18051140c0195110b500c4c00c4640344100da07031884440700c3c00e4280d8001c05005030300031000110000348000d5048d801600408440e1021109c0a0021701500c44031941180015000b08041d1070a0508010303c4a1403041241d09205a150800100340d481603241100d20814410102c0010008000c0d481200d107a500101040a403000343c010141680c1e03c5950f00d585a80f040000005244001048020010078041c0140030800e0308044110040e420151519500010b00c51000000a252030720048a503031240700504282c0c54051070600488002c20b03144010f01c0800d100b0400e1540c4d4120b101c1c15112011240050761451072914030340ca170b810360340000109100004006102582001e1803208680c0b081c1341c1846a10b4900130f081c0d0a0360340a104e00d0ba00100400007194018450b00c4056502c081c107458042d04150440c90 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 133183525 1250 133182275 133182299
    0x30c030e010c0c0b090a0504020f190507050d030b10140d0b01020304080f0a1505090604020105070f020907081801060f03081e0304061a01020c030c12010618050f060109030305190504 80
    0x1c0b119051800001d241041400d08408006c01045e0032a8210704001c580901c0304543d00c91000f802c0c1c5a074203008021011203010308192040c6c2c94004044a070640c200303001c0a8020405030141f103100e4030807200c50000886c49411000c040c000c14241139070800010040b01d8018002c040c0d203d6040d40818840450712050422045030407820020041407141a1810040440d028603078004c2680e0703040204020b1300c8000000c406802990a1030600d0340c5048900344442c2c9017140910007540020440248401607510104040c003810003489800c903080c3c0d04010305400c9410707603c160245803081c59800c00100e5081c1c000360241c04280307100c1164010a1080c18a0240c1c130441d0100e44655071a0100340b044000c00e80d116607020000e00052091a542d500060380d41c5107625001c510407035000c149150204001c1d00000d00070040300101440700700b00d1240f44009030008490301800c03505060000f071910361045883c1012603405031509842c02420394180c40d12020a2000f50f01484010030000810701c0506e8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 133184775 1250 133183525 133183529
    0x40c150207051f03050916030f02010314040501060e1003020306061507050303090102280210153302010b0a0303030c02010209060f09010207090510050607023d0c030c030e010c0c 78
    0x14803ca60a03480302c8101508480001c0e0416180d40d0108a242c00c18040c502c0038030381070303e801207650a104030341440101e01809507007440107102e1110905010410105410480a48120384821034440e41c40c0688041c1516041c800a90f069101002103012401e1011401c40d10b003075681070940c90500a0b8032800d255600130740f0103101581d0f0000d0040824045401102c10212540460485100001070001c1d50746054000518a45603603c00781d20906d144042d01d04e00a02c808445804010000c2d031418585e4062500c525400c1c8540741540310348144107200d040440c1c10014090340e0b003a42103480c02c50051019001c55411356500b00054100fa940d90340141c00c5502284514540d03504000300024100600741c1c0c030440c4854208424050603c201445160584d0400e0701d1803529201c40d4000503c8142c482d00041101c6103a02c40c840031a09840c1c0c0300002110703c280a003c051000114044070b4400103000068002140341c900ca13030000348940b0140c400c501051410805008080e10b4498640400e6 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 133186025 1250 133184775 133184809
    0x7030b0408070c29040b0d021813020d05010b090907050307090807030b4204020f0a08100b1207050307020c22060b03041707051009050d030f05040c15020705 69
    0x56400883c240c40c0350502d0403e204d80e607000c1c1900309480d01c1c069500b1030144810401d115a0040350f02c610a521255100345951001488038010901320380a8000a500c5050402641401d101c008696180100101c80381080040c0400f01c4507510044100c074607400107025203040240c580e000003402541044400d010398010305001c1f0890400c000d0314003240701c1072044906881141c100364440010001d240c10040510251058018540203000030001c0c41008070321822100041ba00320865a4440d000c184a10075020444c00410344503c242002401171020140c200108000040c145034822400341d600007502e4012900e62b204290001072141e40d400040d00c030218020000300c040341c1468010310b00203000415803107203542170645900d54009010450144510030000f019010070a04009551404940071410844081030340340090300c9080342c0e050007000900b8000c00bc1c5801c501882118000c50303004036910303c91440c04204400c0034880814610a47c0103820f000125502d0f200100b51101d81c103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 133187275 1250 133186025 133186049
    0x80c0f07091820220c1b15020f1c09030206010f030c0e0711070603061a03070e1302040b070308010e090c01090324020703110c1207030b0408070c 64
    0x6040a0700110742c0042410400000c030030714000d0105075002e500400d4031040c42504010f031076000300411140301d42c0b020000243c01403020500440c1c0010b911045040d1020707615000c0e84044007100040f0600c002901030301c15901c410b0034407204007540e07008080001c003c90342581044041408d414011001190012000782c0314144001019810b00c0968007429403552480707401800c0d07842d042c0343c0002c280142810001c2080200300c51074041c100701403120346028203c1c2d100039140c0d00e004002d00440d209a14094000001d049001d460040903640f150026a4503d200742d080355042040c0078400c031001c0382013690300f00004110301000c8030080c40610700030b450392100755141042071041200020140c03802504500b88000741a80d20070080d208590300100361200e220300c0600b40b01200701c94152060000c41c80051a2003c240e0444941e402c81d000c12000e40301001008006e000b10366006229030103245d000301205100280b0480e8020790000c4c003620082d403c00101d50b0342e02c0201c00980c2c208407070f4156 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 133188525 1250 133187275 133187279
    0x1104120201090905010f051306050a170d050901121503050d050903060606030c070308090f0303010906030b0f07091703120a0b0a0603020901080f1302030a0c050123040e04080c0f07 79
    0x42c02c40820401003110030380810980d031411405038040314050050520034500311860f820111100d07040b64000d0007000306650212030b6100c200c0240b446a00c4010440ca000e841030101c03005010728142d909004040e118a2242002400800300420b608103044215501c403c0b00440400c1302000b88144400745034803541c4d50365841e1010507192120042025114403810801c10019005800c140e401d11036050800c0c4400b600d0350481c007030030070751030000101e582d21010000061001680d01700c001100c2c003a03d0313000910b458551134112022022906d51020600009080000b20b15401d004144001c800b4140d03400c2080c040308403500ca0384141c0c5c214000f1030712602d510b0120702d0016814030040040c2c0c00e00b1454403d5040018000c00401411681c21198120010300b2801d131001c00c4840e12680142a50158451490080450005030280c01d002620658407003450340004030f00c01d44000308200e00c03d41414a00001d4401000d0000d000b1516a28140b050046804007003040e11600c654000141074014 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 133189775 1250 133188525 133188527
    0x10c050901200a0807020d0b190b04051e0910020d0b03060106020a17070303060b072015030408250302070810020405061608131412060c120a1104120201 67
    0x68446100c150855040703215500b1640001680350500b07580070801640300c220a000091004503181005006480e458080100301c1801800c00c04481d89100f404000d1448a80c0034002255000c5480c000d2500d501d0051100c1c0d1036682c0c0c1d2803980019940e040301c4a40158070848801c0c4d03085907110400c0301da16034100402c0da28042c04001d0241c021032000380f00f50700b030a0303c80e003900c40c90382140c100c1074110000304203051511030b402c02405000103001d042d40c1d070320182c501283d6500648809140d64407031180d0347c81440c50648551b80c01100380148450440d103a54894511660140050703088004040818006d030300601c80c0180b203014026000703801030718581a04c8a0900101e443d55900261040109010a40d80c1070281e130781e490b040e12030028401e0303650f142188a621500300b41e0300c440b2806810000b06500b4000c41920780d07010590b100100090011000c50ba1414140c0741c0c080a004140038941e940480f604400364492910711001c107585440c4864904a030703015811070716001918001840540d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 133191025 1250 133189775 133189787
    0x8160305010f0e030a0e01052104120813110d020a170f0303010b04090509160f030213090b1303090e07030f0c0c03020303060409020d02090114010f05040602060c0318010c050901 78
    0x9040e40000f441441010b06541d03840c2e205400d020800e020000c0c2c42100140d12560903101d11000c1070000701b003034400c0c03e1140254005e08840440342d00c411605001d9189204002c440e0241c8204070500d04098a503030f8498030000b2000200a4002c1d1020300b001025070740d45c03c6020010155903401c85413031512098118107040c440c01064046174400c10041144010780307030880f0200ea201c101c00180075200c1e80092401c043c0407403650505000c400101140c0880c041d030307400d130803240308403601c2c101c0700040d084201c242d4414800282c1409419000911800008005003200030300c0f918107044800d031240c0b02c4500d03050050f80c1c1d001c0020360f14071031a03040d8407180c49040100107241c280345107001350707a6500940d00d100040c00a4082c985903d404001c43d10b8801d843c000d9140c1c01403c0040c2e07985c550404140e44149034448a0006940e0110a130499000d803040700c0c203170350b01340d07018010f2035881c5c0d00c88001950000d00300740d040c920022480b41407640c081c855440c000031590741351503544590000050007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 133192275 1250 133191025 133191041
    0x421030606021218220b03061b0903031903050f010b16061808210606070507140f0301180b0109060f17030702060403060609060b0903060a050a02040816030501 70
    0x14145040340900c640c603000140ba903c0580360441c03440e5079080d00c9282e05446440c107415075802c11450640480100340805428040010840f401c00600b44840704140c1c1e85c0704140c8010b11100300a858083c1152030680003802e01100140032a841c1c9800750031f91a41d0440e4400c1c0b4100085d0b40c440501c070008080602c46401040e600d103c150030411010010184540c186500030b040a5503017a5000000800c070101010f0f560304051080d40312a07040e550b0400c43e1019072028043c0250a90001e030300341c80c01c041a1030a42d604400107100035030800c10071692070800c0c4251070741d100008002904983d5402d000e20000c1024911103d104a546072034182d04081042e00b1500101b400d11100744041d000740341782401181e0003940c1d17540014101c03901d441d00f18800d403c170181d04103100003000b00905c88540c05c1402100d552030010085c04e03075124804006801800e04156140d0450000710744091440d400c0b4607040510410010700d002d039581d510781e00d001304240200402c10740740b4004105001003841313100740e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 133193525 1250 133192275 133192277
    0x30803091209010e040e1f060e010609120807050c0604030807061d1b06040302031c091202060910031e090201110613080a030609050c030105040c0e030c0103020f0708030421 76
    0x81000780b00c4001a10f50034040c3c2e0f80b03900a540e60583c040400783c08000105d144c024401110080720009500340d0050074080c0202d0302e0000f010000002c2c0035124840000c12140c03140740c0903141020a95a580140c0e00403a0156071703501c02c410003082c59603114001080107500c68958a43d4074141031400d42d0a0341e68410b420204201e6224125002000101c0e4000000d00310700c035010648a56040000e01c1806036400c0a50188141d240540071100105541185c070a102c1e261703590540d548070315090b0994001070000b908010144400c000030b061080c1c5140e418035003401c0100d19109401240b485070a070100e9224007681c1c59284840a5580144009014440610142a0601e015505076003504600c0740700511222000400c0c1a034140b20343e1040300a0140741c9402d0042c0c2c2000c503500328060b007080c000d00c3d11aa103085101e028a5000c0e800c1480e005001401900145c001e490064000703400403c80c50328070071810002000010404001584a60320039503034000c1c0106004501024082444c9402c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 133194775 1250 133193525 133193527
    0x5010605061602010807031401051201060b0307110f120f0a02010b0d0b070e0a1505031801180b0606031b0f040f0b07060b27061c03020a0204240b0c160308030912 71
    0x3041c0202301c418040e05440c000e480c04030306400c88105007030040030181e01110b2020404018410401d03070200e151126020b54204a9140b050040c0d24161206041c0700b8010080408000308045100c0c10805000c1004617400000b40309604840820038078103a001c41164408580010071401c180c00034040d820070b0205880c0403110b2070505240688000b0f500d400c420921002000240343c0100e003101c45403821071160024440c5540440080c0400210b805044540e0061100060210700f0180c050701d1041d0b51814529a07004c51640028000d98800f0604d1a003d0204103c0400c1c00711000e00030303078010000c1200301c0d42d4540c5035041038411100c1035240244949400c500e080302d000c00301410640711261012110807180c4a60000411071200c100103c060031441c0c2c1d41c0c00c0c040c15008511001064001e075010700c0880c420015448200c0501c1c5001100380c6c1d88c07505c042c80307890341e035402038a05003648a04a8000c012125010072030041c1640c0100c0b890700300002002900396060221801200e1703084821 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 133196025 1250 133194775 133194791
    0x30d020a1502090f0411130305070e0117030d05041403130e150a0612201908060a0e100b030c070501060603020403080409050a0f0f0e011a01020a0f0501060506160201080703 76
    0x6504c914001081d01d110310b8840c1400404450340c50304031a030f07001030707d09070210855491805546803640c5101c1c45103141171042c000210740480f803032000d89140c070303180140d45403403003200900d4002d08020700705a8a0601c061000001100308000401c1850b0244081b0b1044500d0000b24403041e140c020510101c900c001c1d000482c803130300d40e113561506660b05400c10103294208074090200501900716001c2d92610426514091f03e010500206034603542004191411540d07408141c86000c2c060380c5450b046126100104261542c0303035146d542100d404110602026641c0340b403203c0355001611000c60b0180300244102c20800244600c01c010034040c03d0950a003072a40d2202045801213200ba800b0141d22400040d4024556034003035031651259141c00c12000301001c1c5428024400c681c0500d640b03618000c4ca0313100d0728040c0583c2d01480c1005070b00500c0c140540d6508c03680359446100044880f5034035010040ad0700e90321314000e0302e01e40700000c1003c10300100350f000040986902806003801d1510380180 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 133197275 1250 133196025 133196029
    0xc070203060c030903130b040e150603071b050a1b080a080412021f0e1c3906020309041407020c10090302030102030a0219050c1506040902030d020a150209 68
    0x5119409182c0900c201c3d2250b82d04407145045205805800d21010311441012812444e5080a041555054400d000701c03a582d02e100100d149a54801003039102c0e10500c0003d0006102d80d881201c107a851107091000c03c94141e070358502e0480803480c21a0040f03220840c14828004170b484090090124100610514120381c4424649115500500d20310260300108481552201e40781d01d8a10007641c100c03130051901d9400010812010400c400e80308080c09089075040d010480d550102994011442e85034821031040384440e007404030007030042952942c1244010100300078400c007009028a80255554412900c02c100072209164900700b400f5486005200d0300c990300003520300b1441c606a0301d020701070300501c00940701092141d20007076140d800002009001e1100b03402a21b0320050350700e18104003091084040d207a80c09032078004652030740119400003004819804460700400040e00000724400c07940c01007820003072245c13024009607122104c00000c01a180c0044c0320341c0c14075100d04600317100b20000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 133198525 1250 133197275 133197283
    0x19181d0c0f190306200703110d0f021207060b0603180606060a0f0e041b0203190504211505340c0b0c0d090f0c05010203071104020309070504230c070203 67
    0x240030580d403208110503200c000d84000c07400740c00508242e511003021f4540200f5030140100c12400500924603101103d40c020b83d071268110000340c01610520503d40540d10490300b100728103440b60394681014001c03e8480f140158003e03403001c1221038800342c0c1d074010f0305d10b040320143c08903001d007004110600d8020b80c800764403408144185403501141340300c8000900035080001010320347d2410701d1284010241c001009107013903400200034807083c0101c4c003c15034041c000e51051201c2900d1a885000302166140301c0c10180602c200f0800c3c058010b00010314080351400c0310040d816003400ca0030b403003d142c05141c1c00d440082c0c2090301c0c000490044032005112152801e130040114a4a5001c50590741402d020740d04514000d507010444680c40e410222401d031055607080e1030150001c0c0000c134840d40301000303c545031030308820f04070742504542042c8402948001e04191450080c1c04000c1403d54650081140580e024500180d01203800d452240a242d405490201c03101010441400184c901003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 133199775 1250 133198525 133198529
    0x207060503150f0d0618030e030307030e0d0302010905010c170907180e0102160507050108070504050d080d0905120301080c0f090f09070e1303030b19181d0c0f19 71
    0xd500c480380112680040b07024980701306402009142800c5500e01300c11316030600280254025950a04114041700c02d00d5124443c0d140f001e00050107100040816003005458500c40030b100341700002e50314103281c07030346421070b42450a401c0000741900e03e00c8807081c07854401c0c0c0b41c000c0084006412601c1c680010345488580500c810400a600c1d00c2c2d00406040b020741c1130324291491080050801c521a00d04251102064007405011800306801300303c3c020310400590f17041c0e40c400b6009002e0070201d9142e000b480c0c0c101d410360320241d03510f07003a4040c0005e0080c0082d0a0b50400341e104640c50794140300745035007030440807500940a510360348120943c0ea56400c1c06d041c0c101005990034469500e0b00c428a50904040e0b0300100c1c2540716080c01c1c0429019880344000c080c5000780e808100d6602e0b03000421442c0d000d8449d03004507692a603601071100042100342e030b5000d0b401441b80060900104131441071640c5480c0242415074011070240c1d4458102800d8840300c180003200c29034108410350b0905512207a02d4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 133201025 1250 133199775 133199779
    0x15031a030d080f0705160c080609031e07150c08180a0302150a02070f140d09030203060406050901060807030501020d060b0703050d020304020112050c22050a18110f0307020706050315 80
    0x88013007884140140119804105140240d011090301e85c201209525014440d46620340b064000051142d080030007134480300c407440c0c0d200c005001031000c0003182640008909880d03030264140c51080480a92103400620400d6031580045403070200512071510302c0d01c079140070b04d81c1c00c10b0881c44002540400d0485030340c1d0582e5054401601c03500442d20090081890041c1101c418500f43c9003030020907018603a0b0010b000c011500c50001b9144103c0380e51407a8131000f5095070045010900040c81c45d08a1588410710400009885540300c2c035007443d000e400c0d07200380c0d01e030703513000459600c00403032400b4503030142c800c1c0009145407160581c0c00170b02c58800c500414501640c00b001003001c581c40b40c071107032030650a03404007030009040c403030308034905941300c042d12090506404800c50a82c00d0200d1142c412100000c01d20240d45180140c00d040501c588100310102c29900e1140400d140800c1e80a40212020031910640340e107401030001c0c0c0341c004103400440502606000b0001803030b2010610340022441 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 133202275 1250 133201025 133201051
    0x1030618021e070c0e010f0f03030e01030e1c1103090904032a0308061804031b050f1c0215060d11060702130f06050609090a0504050715031a030d08 65
    0x14a1954501c2d0034448800203400150006540c2e0500141e1079001042e6010152101181c0c0d91340c50548010040a21402000260660007003022a01030900318904c0e18041c100414482078180805060003124a1150910312100300c000300a04e601c42c014125000131000258a0040d89000084448400510042c1003103d050741c7d051129070b4070480c52072181c88280083e01d181040c1c0c40e02038002402203602d41d01550a01070040508208440801d00582d00b40d2a4500008600041d0061403480c1ca90296181d100f50380a003034001d28100b05018404032202442c9890700d078000390003800c0138400046c0c0e501400b08502440200c2c1d4611000f0f12060b40d100600d020705042c3d410200e280c5000b0000701a41c440c4002d0402c2121404a8218284000d100041044410748803000c01095010f00000142c00945240015600c00b82c00c4c2c1c881354000c7d000d40f0442e10329640d114516003003c10703014041400603031901380508100360f000540e0014400114054180d241000340c0c01442c01000030021a0300c020 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 133203525 1250 133202275 133202287
    0x20f031612020a05100209120607080f0c1201030b0403030e06090c0d0303060b0a020a05100603150c0207030813030b010f0806071211131e0b07063602030c0103061802 73
    0x4002c03c11031008503071110980c0d4510601c525104000c0d0848560980142c0d80308400c581001c0300864010310510741c0f601d07507115549501042402c81c0000400c0300c0d11910b0f081103070b04014415400118000d44c4581c0d161000c3c0d02c1c041c58020159030010030f80b03001341c1d448401403001c00c44021444801c100d20030784940c071041a40341012406000d50744d012500b403110008a0a8003d64040780c100c01c400d000d4011111856108440302d4221511071101810300c0160110b82d5600072400e40000e0590f10f014411100b5445d02e07621416115407010382d034401c407510141030030001c1042c0044910300521310012090f180914140e1225158540101032108011140642da808c001e103ea0203680350107103025455840f1462568a1340202c1a9401014402c007103481454580100c90900c90b41552520008c050074090146d80301405403440010040705658940c103e6114030a9000d41304424804e070054030982c6030303030b01d0060509101c4010115030426041500a100100c03404042c42c42d09088402c005039140c1c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 133204775 1250 133203525 133203527
    0x60f081f0e07090e030d05070503240d12120507050708090d02030a0b01170f03040b0a050d0204180209090a0b1e0a050604080f060a09031b14010507030c020f031612 72
    0xc04a0300f2009280746070010b030f03403038400b4000090a00081100010132068491000546250004407481c00d0000198501c1010300703154a1a85000e21002400b40e40c81c025095076034880c0c0c0c07210151341c81c1c0002c4031307015002c0b25808240612a000000c5081403071078500e46444242c418412030b0183e90041465800c0c0204640301001601d1101c4e8024081c2101940c492480e92000c00b00e490300c50a05102e89603000c898210040121001c45400b40c901c0303481c0014980e410fa5494012054030300842d41c0c2403000040c1240e20261100003540c0d4200c0040c4d460311414100281b8910180850b848a840c0004041c61500e48115081c0c0b06240f070070300d030b010742802c400c00104981e18940200d0b40040000c50300081840d00018202e000d80d010f5404e40d40c565407041401000ca80d071009011300042c01102e142c69480c920001c007190394600036102e1910302032034a0306c09400e58030290341c44800a03039150403240c80c40340c3c180036004070310340800003079440c2043e540700c00d071801c040c9800054110380e02c44420125403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 133206025 1250 133204775 133204783
    0x70e04050402034206130e0708030c070603052d0903070f0c08010e120301030b1005180f0c1602040506040e060a0501060206070c03020d08061c06060f081f0e 69
    0x80c0081000d60000c12100390442e41c8801d0140f18540c0070f15004c40740042c00340501800031449a07070040c000304403540c0c03100504006426507204041e024000d4200c0440e10401c180014119074410600030300160707140000040890301e004060301454070300c0604003088081c4032510584001441c11080301341c2c1d11110340090452181090081048600308154410450070707520900865500000820490907600f400c07a0301c50b0760b05240c4c980c11140030801400014071401145400c9046412030710394054071140844c40366040c2007040c40449448000308468407440c00b18540e80320b5040901a8100400301b100c0a001c955130f80402817203651140c001a80a0b2110350010042c041c0060858210341064008003005003002e0065900601030003000622540c01800e041c50195410303802401a00341c9403900320783d40c68002d040359501034071002017000c0b05010038208191660042e0000528286000d50b01f441c400d1250b4060314050308030b0b403240403070340ca442903c0d0300c0c0c5100e942c01c0110395610030402c0d250074 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 133207275 1250 133206025 133206043
    0x1612050f0d050108070b0405030d1206150203070c0504060b0d051f0e010312020a08090904051203150a050d08070308070504030206040e070f02070807050d02010c05010c0302030717070e0405040203 86
    0x26504085209050700d00150006412504090243c40d01c540c3c0f2070500c8042440b69000d001d40550104c800842a50b00c1060b850184401c02030000500c1c6460308244501c00c0c004100c40d5005031300100c0d41000380880001820010701088400b00b0415103031907541c0441d800f4080040c1001680c4d507000075426071060034200904818804610080307511440f005101e0780e000c0c041644d00f42c1090081249040c000112056050382010105052081d01d03010070800600040017220b1030f02540c0528007803400610043c2d401100e034260840960b450300303024061080c045030f103d0740c070540640304040d001c100e01504441400350076242140d01566442000e0701c0234419544001c1d005040014005540b054410109000b0750b6103540d0005401f068020880c0d45042ca80a0b0004039004460304000d03519011281011070ba1060401d65900344a540b90a400c648036a0307201d1002c01d80001c204400d807a0f0040c8000d0724040c0c815184051414205402000c2010044800d809070f65640007242c00c1d55410050012 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 133208525 1250 133207275 133207297
    0x506010f0e061e0a02010903090905060108160e040f0617031e03090f0703050c2d010e040b0405010305010903020c0a0b03190e0109060c08060d0206090d031b0b040c0605161205 77
    0x940c0e500c022000038007d0040c00c006500184441c10003085007000c038050a80202c5050751210310680b19085001ca041c800d20b00c01100b442042880020562540d000b84010700e01007020018201e4900001d148002c46040176440407600208440d00c00c9001c403440d80603021140a15841c0c0700e50b1005aa0743c54000030078801c1286205d1400008200840040d98056560781901c0c51000c2e141801c40c0c45504a405154803103401510341c0c00d02c54654030400200e4010080103102289414000c03002c0b50071a80283c005503050307510b8135485400c0c50740401c4403800401040e6450b00206107004d14003000303130201500003400004843d001d01c101d600e46810000d01074889c180200311000302480c1070002005290450404180820009110707460101841d50f102c0741c0140c003103850003e8034401c120440e90100001c4052100800c034800021142d621000034040c4550a8580941481c0c01d004561a1403036000c1c20402c4820000c1900f4400848c410014903903110a11305c940303135410b140694050040c030b0740f014 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 133209775 1250 133208525 133208527
    0x605030a0e0f1501080c010801050d02042c0601090e03090d060c02030405060409020a03050603010c090902160c030c030b1510051e0d0c202a04020403150506010f0e061e 74
    0x54900d00f2240c2e05a07040b1040d0b402143c1c0313138001001c015034103a9024401c155014214403c400090f0400350050b404405161107030300c43c041d5103000e4040004e41c40d065461342d10b42c40540113200070303800342c4a030000301e180000045040046030000500c10070503101004142a85508110121500810503a0040d00000f0501900c858a0308040320080d0032131418000000e03b040042031690806124010300a000344e45c1d51403155081c40e0041010f9400700c0b007004841e10742690761002181040744003901441c03240d01d10141091440c1000c80b2000b60291409003202e03490001c0540350f980342041da04212005043c001c2e1600725002c080d040220b58524250400303a0001035000f81141964040c1c900b8880303640b10401042005000c50341907864156440156038000003482d40e8000748001d030701ca5000340c043c14500c3c4e00324071407012506176002603004985104c091945080b2802c001e003d603d174015401e1074112052003c1050060030800c00c0d40b20b1901410000500c0441c1c000118100027118050007942 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 133211025 1250 133209775 133209793
    0x1e0606090c0c110d0b07030c020a080703080708010e010e04140f010c08100b040f0504021c06030506070e030109020108060111070504050f100e011518031b0f0902040605030a0e0f 78
    0x2401240745102c1c101d03440c5481c80c010f603d1910342410386020305504102219826500c1c00c20641c0180202483c11003075105140040001800110060030020710035910344540e420020b401401111040e0008405c00345180c005101d4042d1074484980d10541045181c207a04440704030035820180d00d518110403d5003003014401c502900312500d6070180c02149040d00e10280e076000c850b445c9000da40100c45000b00c0682c400c01261500ba005840c516aa05120300c0f290107005512030304480c82a03204a5a40d0070800400254541140c01c2e03a1206d1004d0f00240444401580000c040c864021300391030602100d03804a08624104000c1d0a000c1c0001400802942c01c000e0b01d20400341100f19654001b0900c1c8042c0421100c1d000c4007040e0403960006803034800c040c80083d058079030070b4003e80f43e000e0350031340c0e04800404902801c2144d516000c00c90715010801c2c0c00e0070459400d0010582050a00500400c01002469800400c03203a11801141c1e00090b99484a40c1d11410004003500c0c215061248203a4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 133212275 1250 133211025 133211027
    0x270402070b150d0506060d05031308010c02010f0b010512070306050402120f0a020a020a14030712051803010605010f08060d020d03050a09120309050118170714040501031e0606090c 79
    0x10721070140d02c5020100c02c290546000300440c05420000c0200142c00440200d003032414541503010301c0d184074034180d909004000c940d0f4101c40d4003130303480541a45c0d12002000810fa8081c85002c815a00500f024000f00020900207450351203841408040d035821b000000322428444da1044000c0e0100600555035684500c0e07035840609415076240d048031407103c01088666a0504c21912a142150042c0071545044d8542070b4000202480b01070b8280030421480e030000311b848200d52142026612026240d1a0b501c441e01c120020121440c6d000f42c1c0752250600c05a0b0b08840d145161200d1441c0289841c2d40d140003240003403140303030000ac1d00880c8040d02e8208058105028150b400c000c6e40d12048859134035410404100040301c4042c01064901905000c654880c8001c1c0741a400c2d80c19000b0021f035941c41c444000c1e5512076982490300d410441c0c040c09944013114030420010001c541c14441941540c1f10203150101c20b10312140c004d080f0400ca9410000b1980102e4018014154108100761812034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 133213525 1250 133212275 133212293
    0xa0c061a0406050925030e07061e0201060f140607021302041706042f0307260f060c0901020708100b040606020a11060a0c0b04060903090f0b27040207 66
    0x8101072040b03051071400701d81400d108071030a01c117050100484003e038003840121411012a901c40c4000c05448200104010008010100c01811555600309441d40500c0f1550550049a40080110f90400508110384444c00d03a41c4d2081da204101d01c50010742030400003030483e1040c400d0094001c215000c0700348241c440340d80600101d541075540780d1030640800c0c8096403545400c84004010246000560002c07030361640d042c0361095101754404140c6068000042d00c4c0081c07a600480300c28010340000940003641e00b0106030003140c0c101c001c2094405801c002c6450350802400302060100c003103010500c03a0710801078103000384000401e0711103414405c2e140c0c1e8040c00d1545d01c400e00550900000080262001902c0c0c8151504079035801c08055035a0104402507101d080c40034200710045040390040b0f01c54031103980c040d80c03080e140068102e10b00c6c039000c0d010b00415841110011280d803820041d982c440c80844284800c00c0440d4070b00c609460369007040c40c402c2001e00700e400c1480415a0010802110 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 133214775 1250 133213525 133213571
    0x50d05090102130609061b11030105240604050d120215090c03010c050306010c030c02030f010e100b090402150d14040f020406050907052508070302161203050f0a0c06 73
    0x3800201026110130084c0c030307210300724841e40000440824002041035040924010424450401e103201103046000003401d40b0402d4864080181420011600d465400e90b0b20741440c0c101550210706091500e4001410307042c1c0940083c3c00303203912160480b600351091183e807a03001d140c41d00701465400c1540300c0603528120b00c8a500d00943c81d1a08811905006005907403080205a5404d85d4481440da401c580c44030b00608100e03050701c186102848080c3c803e000785040b20b00e1080c005c01740c00103030005030401c5e95820b2000354011036249041c04090780300d40c00c2c1880f2844d40c1a0340305588843e1101984028400982c01c61a8801210b050100b00001000c0344240680216010301c903d030786130003c10444050681340800410010001c0c4107540b603640304000b075816615450312001081e10703140c0c0e1180d580040c200b10010f80020444040241d60300c020007000c0c040b945107242418242d030f41d0103010762143e003001081010000ca4000700141c0300c0e5056800482d4080f600788035440d402460480410615 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 133216025 1250 133214775 133214797
    0x3040510050423030f091e063105090705070503121321050406120209040f0203040b0106020307030509010302071b0602010501080d08060a21060203090604140c10030c050d05090102 79
    0x10541001c0200000040e911a6052100c40030711b400c08031010401480a0740800ba40c0c1740203186040406903640001034450f0804c00756100051411142034100480c1c80090900041e08a0a005101a03241d0851880e406015414201c1c1c1d41c80301ca040491450084003404416518214200300c8110314160f11a40c00d14800d00311a43d2281c0c040100c11740400c4030100000000f0420f0204200300b9200b41c02804805e450a103005207845030300400b140c00d40b45d0050f603407000150000180401c0240c281c0540c0d006190920246041400b141c4c1d0017403591060149180c101600400c2510601104c03000841c041140b2480c2480c1e071a03076492000c1d0103400309200b100d140d802031440e403d41d1503005040729440345000802000c590781c1802c40a04403400260410a0750011341c040030800030f400c3d44003c60042940700018074080c50240740030075200d4aa404092899082820503401a80301c0b03c01d60100d50f905420042080100ea81e011101406103142414035142001c050160b040300640c004c00366402e40b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 133217275 1250 133216025 133216073
    0xc0e0c040b13060e030303070e010e0d201807020a030c02060c060703090c08010603050c0d110907090f06140711131d0d050f0406080907050a090b010e011e05030405100504 75
    0x1d004c04064583c041140c082c00403614000c406040780d8465030394101c2410004041c6c201d80c050a468860003625a030801d960304540880c1107144070b1a11200c16035500b00300c0145c01c01d1504c0c1c100d1009480f40c8001c1e00c020240b20105540d2800c5685007810780701e0b0300d41d0310002c13218249010103009003d80035050058030b00f40d5400402240c00c13035040c05117070103890700100182001501e110601042841001040d5070000d4854400d02e62581c801c00e00b50b0040c8003594401060b1814512a28034521041e40401c0c240141200340d000b4604000060301e85403504045a441c0120815000c100001d06460a4821380e524204214580403d05000380710300840050484c1c1c14241c00321400e640350711410788071040c1c0c007074140010002c40e071090010941c0144440c045e226070641e40d00200c1c40881c5190015100a80c941c50700310103030f582c800754441e8858001d113454414003804050807103031940710024080c20801c0003c000f4040c880104405142600307804002c000720f00e401d0030402d421202011030354240d0340b0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 133218525 1250 133217275 133217297
    0x60a17100b07021504031b061d09011401091a0c1c0e090405010b060301090c03150506041403120c0c0319030504260703030206010f05010504030c0e0c040b1306 70
    0x200340032010654002040940c03901c6403039003c0051880c0101200101243c0c03c00011001909080090f110742c1d00c01ca40300c3c0025414034030090840490803c000c0c0d20b030818000c03003081c0340d0343c0c40d18a141100d520104c406490142840101c9291400303820076000f0884924000380c030100e00c2c000602c2125044070940743e0780222111010a0790b2041004000045e10403030665040717141901503690018820b07000010481840000309a19400c00da100c00020365035805c4c90035401d60903011b50b2003540d41c507202a11040b810240041d0090155000c0c40000c98841c0d000e400c15a1000c20801160340c1c0c0040c005520380401001a60340c4544a000c5240a406910303052848104100e601c3c40b0030552603100c150416040040c40a10400c5411055403000781d8200c05100f401414003030400030314040d902500196040910112100081d41e20150400c4420441000440c81110144050740c80c028440301c01d46e00e880100c0407050007150040240304d880012507240f0a4103c1c0310a40c1268419203608280380 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 133219775 1250 133218525 133218541
    0xf0c060304080a0809100f0b010f0c05100c02010f020304050106090e071415160f14150a050a02040f060c0b070903050a020d2f19060212030a060302060a17 68
    0x10005560041c9070b154140440942d01d4080c8418070350001c2c12030304558800301d9540201095422018210718241d03628060b1480d1543c0c880d500c95040e01d01414000060342403a0784c0c19036207036865580845401d684501d80d0090620039000480503d2aa82007076407207080c503040c1540203181e14422a282c0500e048101c0303806020210300007084522144003044e14035000802e11402107201000300d2803d4000700121014080942210741c12240501a089240444c3c0d260082c045540020b51a810303500a003070304400c00b5101e010142d401a240d070310110345600d901410b00040d00584e00039036a2102030a0700407684590001d40c84005602aa0f1085400c0d15000e105803030b05400c9000c05049604510082c80150a200d103d080e501c0b0b02c01c035640107840c011208502819485180c40c401c0f02d40c0c14a080400600d080c0d646400d540e40501c0c00c00015503d0486c019550387c0c01c00040350907140010000629020301540908003c54004e401c46036944e8401c50020038900724045d0035000c400c1d2500114000d1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 133221025 1250 133219775 133219777
    0x801080d080105010f0507031b03080a050f090a0609060b030718060b0306010c0305072a170f030403021011010f05011e03050601060c0f0203120a08090606090f090a0507080f0c06 78
    0xf1030042e154018400704a030400c4800341e00104058060041d1a8961102014400d0003c60047d0007a910845e141c10647c030440c00390358001d04141c0c8081c100b4018441c1442000c83c84408250b40300c480001c40d490280381c080090b003203408420341c0c540070302000003c461800206011601c5008042041965224921018280015160640080c00000e900400a40542c00404c0850700400411a040c00c400032001190003c807808184100c1318600104901314484107403010310002c84003e007030038254003040b9507680e010360700c0b001e03100384840c400020086014a52061008400310005d00c00003002001c0340003e094284034440b100e030f1003070b45103560921b0200401010b5990140240c00c03c0d0b46040011130b000c0c9614002680c403038100d2000741d001a541040ee2070031840454a1064880800520160010380000c107140810f400817810007285a64801c082c50380500e08140c511020745980b043c26180240307807200104207104d0f000340880c6502c000150480800d46490407100b22010003c140001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 133222275 1250 133221025 133221029
    0x602030304030c060f0f020408010b030a0209060f0a03060504033606180503030c010b091b070321051008060a0e0309060c010e0d0503060931020a150801080d0801 71
    0x6820510114000a1182040115550244901188484000c4080c0044695445c1882c01c0d5950015041101c100203001c0d0000c3c41c401200034003180c8102d50041120000f0060200c0c2c030a0450b0170301c603001607407404812801746030401000c000c01e00c0c0503c2c000d040400b8514030f42407084c641040d4110b001a01c100d80e076046442c14540c21525624002083c0c0340c0d40202c44091103c60710010001c40d02c1d80307040026081c507840501c00030031940806001c0c01382e4000041c000580554074003e03881900c0c2d080da4116864583d25190646990900195064118100b07040c508807841c20f11060003142c904a90501080d50b00e4035090701c015458110040c0f0458602e40c1d4a007010ba0000e1241c0421b0746403100c054410700c00302900108000101078280c40c2040b4ac512114404994084140403641c104400116030040200c8903414440c00e2745503c209200080b03403401d111004101041d1011900da105c015401030221010158101103003602c064070862090250360914442c4044d00d484a82c490600c241c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 133223525 1250 133222275 133222277
    0x3021309020309030703121805011d01050c1b0106030c1205010c0e0d14070f1508070207061704030c0b090307030210051006080c0c070e0108010f0504080d02090d06230a050106 77
    0x131404410340c3d01502c00d50100f500c0c01c81e146668145459148c03410002c00036203148114000101c8103040410124141204c152036101e0341e14110801070f810180c4070488100403a03403480805829810307604940904410340009003030841300e09000800c000341041500010380b2030002403020ba1401e810449484583d0010035a02c052040304090100304504940014a20000300f0341e00c401d5100c540b11803015019900403000c5600011a603036042e5030103d040c0350000740da0703c00740c0210b914208005151a03102501d0000c4c6031500c0c004038003018062252611960751081c0b45001e64980f408110740c803504986001c1d0054020040602c40b4048984281489683d00030750003000c581c1808822242c0c2c25000781792020714201007011031042001003200340024041030842044640c10301c00d520342500c1014162210f6a070900c0c0a01001030220001c0d24083c0e00c504500503280d045200005a05100081026025032711784201ea0310402040340403c0704500030001c1d031101c40c1e2905128142211000d00c9a40 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 133224775 1250 133223525 133223527
    0x1508090a0c05041a0d0c1a0903060109020a0e0307060806032413020111010905070609051909020c010609140708370204031b0f1a0f0c010204080703030302130902030903 74
    0x4482032600b40d0015040904d06006a5002034004012959812402005603240f00568008200040203040c208804141c01e00d001414440c003000465a50700060060354141c0e900405c0300710030244039240002d0050030007004c42c0c803825a1210301401103101526028000d018450010701e121605072603c0000e081810071711440d80da1141040c44103d000a0803c1741040b08950544003240d80034040d040d001070051000e0030b0441d00e040000341030000710342d002038054025840e080c00010b03c050130304e904450f00002c0c00340c0ea589140c11407900400c0140c01003400c00349000d500c60b403440798101c00144100c0e09921444556141c5207420030142c12600511a00803003035070f441011010014140351454001c048000d030a040d00c2c1e50b01d55100c0c01d01148180d401a008140401100c00e110031510300614a003208100450444404030446209400d0072a00c0320400040c0483d4804095040300d004001203410baa880719142c0c68018042e50010b14405000c100d01d0701c003c03468041c00d10845e40a202400c0080d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 133226025 1250 133224775 133224779
    0x206010b0a021b031504080405040c0e01020c120c0d1113110d0216081224030705090c0403060213140a0e0f0405150c09030f1203240301061508090a0c 66
    0x41d440c0d42c03030b40003222501070044c85c0245006101c1d00c40c42d24051442036800d00d031500c0c01c00d030901c0100ea80c1071031810100010f0400b40c6040342d0300811103544070b040179a000f9010211030300c0207910f4030305035902d12500f0680d049414001e110b1401c2020410501c202c0345102d212040c40c08103400c0d240e41101c03415003402d0070000542c4403500b650003401c44013014860001003420f591110351050b041114810034500300d5604000e0041c90710100312041da000002d00c185d02541440101e591141341d40070702d0f07009140300404501c1341d40e44181654029030340400290340e0f403a050b040603001b0300300300d00c107451034052128611001840c0051800c03066903140c1649140d00e80c1d403801203a41050001e070060300c450103810340c02031104000100c240d104604800c078617691900e44105240c070300000040b50f000290451070078624000c0d104405c40340c201c0710242240c280500c0b007100c60b10b00b01c00074031f81099240d0f2914400140d6142c3da5250406510181d45580d00569201244644c84507020352000700780254400f03007 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 133227275 1250 133226025 133226053
    0x1a04081203070e03070303090e0601140a03090212030a020f06070201270812100515040311060f0c1b09011410030f0e070f03050f030403030f1209051005070206010b0a02 74
    0x107036502950074680801402510004617080c11500d402c181e001a01558090101c0155000c00741c0d084402032801d17913600f4060121309035040c060445004200f6031100c20329000c1d0f6440e1480c1c01c1c040000301d0181c0759142004600239585160880241826005890001d517884e80103115004040303209030200048001b030594030240a0b9000b007403c03511000b0520018403180302d09140070388100b0000307004040341401c01d42003040c54903007070b004440a41c02c108014400038040f10300a14a0f90780a4031500e40741d4200450344145070140040e01c002e98480d01408162090b0351038189a180c1c0301c00d941074105070f42c035090368041e0500e5800b10544c000030a03010b2162468444c0c2d00a1340142602100000c40344011100c80f4100030b115880300020441c210010300600109000c5400714a032214000c1d443d05265680c00341c0706420300c000080500c102015098241103291b0082c41c0c0c4030f075000f03003520881d0b500251602c1c001c00090701c80000522404002044000800040398510780e1681c0050140c1c4001c0c3c50 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 133228525 1250 133227275 133227277
    0x2106060305090f03041401140a0e130207031409040605060d020703030b040218101e050712030506090a090519060c0801082107080903010608030715050c07021003110a0302041a040812 80
    0x80103904100080001d4034048d1095006016001019500c80c4d051003024020800c404e1042110340c1e42d0703544100900c80c002034204140c54000e54030030a6940d1151004000200200141e43c8a0303a00420006141d100c0131159600400095101f514100301c141c8180c000d002c200d0117854040b50080480d8440c0700400d240c4204264048442c40ca000803510400c6000801000308801050011540c049018000c0224400d0551100070043c5807c0295151080014084200280801801960b1040c180c000d100c400d1080d280c5500d4084a414080421460000d004000b404d09070000900d00c0340022132450b01c041843d248007101c4400994152180c1b41a06030a540110002c82d20560300304070341c1e58991000c0c02524010882030001d580c4440c014100b4280714407464400000542c039100030082150f40b07500c1600d6000d5015940218880140c0d10103030300800120150800214000c1015000030b58507400a00075207000c10101c10040082025006180c0164040c1d9072058008190b403d404099581c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 133229775 1250 133228525 133228559
    0x20409060b030f070f1a1e0c01060b070218040804090e07090c051306021603060e010e010f0b120f15040309270501170706030c2106060305090f0304 65
    0x10348005208298580001d2600604051110041e00201410080c0710317000c811080042001682c00c4195440340c00b804100352180c007907400002030040726000d02c4055640305850b943c000e10740003080850340325150350340c0350341100034101d00c1140a10050141c280700c4034000c50050ba0301100080c1800d04000d08540a00011961107101d031060000010303131000c085c054100c1701d00b02d80c0c441c035540d5110600302c1c1c00303d408550040015944012160000416402108811030390410b81c00503001950818003400342090b048445259824444065119040c3c1e50000d0840d072001c40c1c010b001440b071031440d170752508200e044949007070f0010390400d0320030030708103500640c403921915102e0300b8551a0b0442031218145629003ca180749803194000110300305202c4c55014003046942c50606a405151159640b542d50180c80201522440d00d018101c2c000c05040351700c001212007101e044586070002c2c0d001400b442c401d010001e4107210101d0025840031038030700402c640700406140303801d0801d00d040c65454811 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 133231025 1250 133229775 133229783
    0x4090b041e02090f0609061c0305070201141308010b010212040b07021c03080f0a09051c02070b0d29010c060209031906050f0603070510030e120c060915060904020409 73
    0x200ca039a40060303a40302e003070f01c2c841e40716181541079509006041c400c4030340c4003d01c5240039010b10369122030420341420305140030f40d138545130031641c3c1d92062004031003a0700c2c1011800c6407808003144102c0150180080001a41c00250003000443e441200481e40d03203845021074482c0003400c07c01805410480001418030794000360007405805013449584821025a02050700001c208200f403114000d044c03c105904641c0061040c030111509841c1c66071601e210501e50181307020546150007440e40240304080003024200499511106a007903110040e24080c080092000b246501c00d8500202c0310101c2c91035000180e591000b0312040c0d60f1508020f40c0006011949489213040c1c02340041545425100040d116075008101403e0151504a801a016260a1003904048030500042d21445011803403a00c0d545001300724210000801400e0905074242051080e00028032410318000000705035010314151002c8441c0900940707005a00a401603403000d0740201c070440800c3c05807901d034000000036409 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 133232275 1250 133231025 133231073
    0x10210908070804081e010c050f0a09030203010509251202060d02160320010501030201020d05130e01061e08040f0b071704050106050a0b070506010603180803070503010f0504090b04 79
    0x5a4442c03110a03003081c1d100340351303d40c40011a95030358890788100151480c80c2400910543c114460f0281c0340d406145d0075105203500104240c2c0039548034641440080d600074008100f10305041d4000b5443d515000a240151082d1003400011040800021001c46040d124007030312050b415400c12106031b01c4401101341c000d800380301c80810b001d0140e280e508520b10a8a8200300d500c00c5051a1b4901e101044a105040e45080300400140c0d070042100c054075022881d1082d034078801e90003200402691900620242079094001086241c0c011402d1000a0403415031707100c407114202c804503000300c03044034010300c0c80d2500721003a4001000441c10030380040003404c0c01160103155018550050703c08039005c0c0c600743e4640100b0800c60070400500000340084200080c5403280b03580b207503952510180300321402c043d652615035123115281489007075402d5020081950340d00380880c2c02042074100380200c110141102c04005818a0a40b00300f40e0380d158402107000c402d0b40c66440301c44048295603254500010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 133233525 1250 133232275 133232287
    0x105120a0503120402130c09050f0a0f0e10050307060c06152c0705040608150a0512010515120d0e03162705060312031e011410210908 59
    0x9000d02c00780c4001d00412a010f0014a45401000300c440c0e41804c54001140c90f00d51300189030ba9011503503800303841084c2c91000114a40c0720208400e0041079124104840150801240034494010114050711501c038060501c0c0f03031240100f5442c0c0d8100d03c02c00011518140700366001440d56000140f10b9503560703018440c00b5555030441c0c0342081c402c0001c880c800d80f86880041c10f99104103400d6170001c05a01e041f40c10300d41494800384c0005c001501c1540d00d1215a40b20408039940c140c3d5260250001400a543c83c0d81901d16640c080d00d801da45003140889520340d5401e0380e0415070f02d44002558064000c1c41c0d40b81c0002c105031307404108a4042c42c2c040c0a001c115841586030300c8807071001400b542c0e20580684006510003c1c2e50340320782101ea41c5c02810041480342d83d41e00010303020b00c9000703030303480701596500c40040fa01440c3d0810110362003507600c440b0000460480464440e003034400103485060345060103c0c0e003203418816451641c01202d05d165007180c50000079504c5031000360710500117689451 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 133234775 1250 133233525 133233533
    0x60803030711071a030711030a020714030a1b0e01050105070f02012303070207060e0a060c03080a021c05070e10091211060304060203061e0a05060d200414060c060105120a 75
    0x1900304404080384c01c000802d0240c196880301c100148210703540050350505e005c5001c005e40700c2102c0d1181500e4421500f00000455070280094034034558403042c110010325140806c3d83c011225485091803c00f15a4000903c650107a0111403417542e20550105210490342d00545030396003807420403400d440342c000705600700001d650021070041c003c03900144a9507141020040c00d100102928a024000a890070400c003900007200c001c40d1a818144070851356610300f0024000c1c0504c440c000d043c000c200340364107036249556018071b00070303520380d524191002c0c0307407200307004c5000180c00442000400c4031204000302c1201902c1014054810100340c900000c1c42c00020303d40d42c0081e81d09846c001c2d03002082c41030340d21302801c5240c8000300395805a40100c10410019294850a1049a001e0100046e101c20500059880004920724000414000b20002410600c1503000b03400782c40030441e010642c1c20b14030710302141901c12901500c4001c000980c20309003440700110405102a51610074918201c9c001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 133236025 1250 133234775 133234799
    0x3140c030702030f1c0309080301030308092104170c0a0e090f010905010e0708070303050d330f090b0a0b070501151d0109050f0a09081b0a110406080303071107 70
    0x10000ca0703002017004144e1446010070310903141c510b40f0281031902d0031080008003104d069a044a406060588107903507281a03041c1402c2246403018991441d640c00748062440c114041c000b0380c0c9030440c90300d854140403040c440e603501d0ba041e41e1a034418103882c800c0041c0c2e1030484d145c0e40d2091241080c0d80040300e11003103031402c0d01d13900201200d040c1d440305031442564100300b000d0001800c4410040c0600c0e803954402800c40d126041c00c46550070748447e64460001c03142422406003c0d0030f07440800505001c000d41c0c62600070a402081001c400c49600002c16403540d000341441c4110042c0740b5808145491405d8603e58003591048550b035484410884183c190100f0420040c941d02505a0000852314032110300048140c02540340c8070b1500b01440f40d01c0e007031081c11684c4107202080005081c0c580e8148030281d401404414201000d08009400c26200f0100c1c600700d80a00c03400c1000ea46030b48500401042d203031a07000b8500c031039000740000b900e82c5204010058000751010107480c1c243d500c0310482480 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 133237275 1250 133236025 133236043
    0x106020115143114062d01031806050405010f021908041e0803090f031204060c0e0a0f06031a010c0f0602120c0909090f1b0303040e01090c1b03140c03070203 69
    0x19070f104400c1002d9103d00300c041d98000400c407001e040b622481c501b52a00c070b501181c03d9101c000941700070300500d80d0103903000b40743c440250184284880e10515089019000450f000c440c25401e0040004650195009903810441c0340044418440d6891508071001a0010b0060700c0035401c0802129901e1141030b8603101407800f489034250340b46400b515075490521800c00c003500680c4200001e444000010300c11982181c0d0002002c00c2e41c00611070200c4600e408280341903030010920100180502c154607041c412560f60742c03405d2141c03000d90401c052564138060381c01070105420501d640c00040c1c21300b12100140b4404c940050a02c6801c10300300e954903400700d410701450140002d22020300c0c0f0349404011361150500b002041c64000c004101a00c2c0d21004101c56505260b50030000e03881d940034000c0d90b01400841070072000701e43c0d4894081c0301510403001c215000c1052503070524181d540380b05028006580540762005802c1d2055446c1003141e018a4941c00180414030a0500594040c460050 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 133238525 1250 133237275 133237369
    0x50c0904050a0b1003032a061b0e061c0b0109091b0e0939132904060c06090213050604050604091a070302070b0708010602011514 57
    0x2d1040c501c0c41d00202e15100580700c032460100011042001a0740000f1803c2c4040200c20200201c8400802c40603a15240e404003c7c80103003000d582c04110b5941d000130305032244481d5950b803548954a420720030f00d4070944560b8018610310304500301e002200ba42000c7c11011043c54111042540e076220742040b01c480f5000c40840340100c4070145000c580c020030500d0124011156a106414804429031040790032500c1080c0c1900781c02c8050691b012007644481040e0450003186a175480030400c4031061802600402e04620031b01c403030707580039030f40010308150341981851440b6207014148003064070504940003040703420326100c0035880016296083d00c014816095440824581001400c20055560040070180214685549130700482c0191201480704906150003550a8030344610440203842550805041e0040c26014003220503030007451541281c0d901e50080040b10300c1043c85510702c2d0ba40e4402c2400c02c2d003000017411541c1c42c200d108421340a05020063b52035000801007401c1c1c0940101e68a5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 133239775 1250 133238525 133238533
    0xb0f0f01091a130603060b07020d1502130905010b030f0403080411040e1006170327030604050604050d03150b0d06030606170f0606091815010311010e0109080606010507050c090405 79
    0x4950010142d4a0758050031003414140a04c0742003d250b0b04072400751541c0030b4400d8014404ac0000d000d18413120840050b10ac007015507540300c4045c03548512068034454540e40e03520b4540001014203004003624000c060404542c08940c4850702c08441e8014064000d4446040c030507841c101591307541c4140c0300d580e02558044c1141c010840010701c11030303440b070344115082e150b0002e804030001804011260942c282c07101424000c190114000d40380c034100c015594044c4a4001804144a00003031b1252145109004035901c042052000710b00346c81140b451410120890b0382c003400400c62020140803080f1101d00c0001d106562a21a68250703000c075880f0300da005044855880070b1050500100703a83c0a560b600502a03403c100c0c3c0890106400105846c442140d45101c501030107505000401f2078000703031400e02c0d405503101e0801d0f41c41e070f800010944d030208a100c4090484c80d4090200d050807910440d01900c0e042d5903903030041d9a1030340286001c442c18003410b4404110707031741c83c0b200b11390240c0d014038010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 133241025 1250 133239775 133239787
    0x10b0402070c140d02030726030c070f230112020d0903030b0310020f0910050408070303080709080a0c0e100504060305030403121d0112140f16030b0f0f01091a 70
    0x5000202420103c603000da41d040f903500b005a140014180308075110740c01c040003200c12881c8000d05840b100612802140000150140352440000f2041d0542d40242c1c1f52009055542c814001d03110100007001c4500c45603600c085a03a1b600130001c4080d142021540503203401e0100c0c0040c001c481c20748104601003550b4044420882c14100210f440c0700080c3c8030218a800c4101140d00220b005032818540b00b5060640d98203030341d40c0705209650050190900711005103480303182c09084290221071a5000800b40440020204800112a8040c40d0031280c0c0d21000c5061541101c81801c2c010072104462800c0b400001c3c4607100c41c800e10b00107600403070245480e641580b9000ca4114450782100041090100448030b01115444e19400b40c2d0713a007406c08003c42d00c10200110007a1a10290b801300d81201c5a08001340003c10b88041c0748030b00c0904600c0014804240003c2d012034014404060304000003101025581c1803017091480035800504240486990780d81d001030740311421401c0c0f42d10b040030108072 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 133242275 1250 133241025 133241039
    0x61b08070c0203102003161b02060a030c090b0a03050a0b063103060203070201050a060b040b0a050702060409110c0f060f040f0c051314060409030c0212010b0402070c 73
    0x41504688646801c003684091030700080e41d11100c0d50b240465469070346251200000b15044081412012103000700d03242c1c0381281103000d00000c030101c01e0002c21241200d8500d8426001001034485030b0051070706042c110f11000840052489045a4060042910000c02c54690000180124200507500401c0740e10701304415000741c035000d180da5070050324140191542c03010320440192010a601c0f042e0000c02d0030348a00c01900685661014000b80e1001082c8210b00e42c0c103421040c410701c0705050900449680d074441c50020721407840b40e0b81c06407034107004800e032045c8240000c244007400200141d0500d91603105040490301c0ca49406480c2da00e000036070150008050058030a41250305020b4039031850003503003c40c0c0e440002000104100125102d80040181400382840940fa01900d0212103d1031400000000c00c5540d920840c040c0c00d08002829a00d0305001c1c0c41d4030207505681f550302c2d0101d030b94240001c020380003142c1e25081d5292074207000652583d2001d021501c2c011180360380c1592070008 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 133243525 1250 133242275 133242287
    0xa0807061b0b040b090a06050a051501090602030405010309080405100c02130b18040212060106020c2409100903120305160201020c060f100f090504110109060f140403061b 75
    0x40118084a1858001c40120300c4508440c0d0f40550400d188540c40e0f50341004c801c0c140b100c0070200503c043d00d004107002403101c00c1e5004510803015503000d010000c11400055485021a210304001640100410b0001c0c0d40300e5004184000e00c0f95100500f007075280c00000700c80c0103502c00d2a0f00029017081030720095290502882c00c2161400c0c00400000100001048101c1c0d4074031100104030800b40c0101d011511000d44001c0242c50100c262001940c4614000791515082e0490500c035100c01c04d02012000c6400d01c42178081307540c14101c0c900e440810701c01d22202d85049032460301803010021001002ca820030f078a0750800e2060780c3d4009954507010302d219140c660f2150180085a205018000350400b0008089800010038003580590756542d400390201c08450350003035141e2150b030030750010b070a450a82200b07020340e10411241e08a0100c40c401141c900c0618444c500000d9803080d40740008074080c0d60000c40b00708401742c80034903007901c9888200c1551500c24280c4070700c2d94003070050003446a1101c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 133244775 1250 133243525 133243547
    0x10915150c0c2907030203030c0f0c060a0b090a0c020c2106100f0f030317040501021b10061401090b0f161b05032d0703051905060603070509010b03090c0a080706 71
    0x25540c0380c140f41c0c44c0e8800035a40d01004007a03591102d80026003d03c114801c00c16a881c442e1407408a445134035000182c0c0d400b80c40301d050054040e2403d403020070440c120b54090b41c20380070142c2c0d00900203100c111301040f05000c840318101d1001c2c00d034896010101b181c2800524411080540d0104004c0c0c50300c0108140d100c1554414005006144020b0001075031000c50282c410a89403233045075a110344c10558024460540c20922080842d803000e0480d4001240451081c45100d400b000501c2e503d05144d1510381c141c4007040e00207006c1302400c0c000750b4028000380008014807803a040c20321580010001041048440681c0c03110a51181ca000780010809100c2c00f40500fa401740c4200f0741c40e1076240030324a4040240c0c4d01150801800c0c001c0f04c1004004100040d900f04040340c0003032800e421507450003c07920500b680c49004060008130036060010b03002c0c04840c406400403003d07a02c0c0030040d825540001c1c0081c14140070f00300b40480c0c282d94024050340544503040c05001c1d0300c0e15002c40940811000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 133246025 1250 133244775 133244849
    0x402090307240f0f0c030e0405070f090f061e0c050111030610090b0a0e03010e0d1e02060103110405040f12091409090a241a0108010915150c0c 63
    0x1d09043c040300d6403080100c44e200c041424228448941072074280d072035118a006464007d442c1008008600e0381c040400d900d1550551264400507844800901c0c400302a800b030500894050080c0d181c0340e10340c90041141301551072a040b24440c4850b511035094401141a00034114400720501ca214500700180896009440c2820600640f9103220700078140900e07003401c0184881c01404c000140c400390411400302c0d0356003090f100f81c0c10390742802405d152460341c440640c0a040030503e2405600000c1c00078141d0340c000c440c5080040c030400c2000042e06005008950f52080604c6a0300090141a410140d0841680710340000b00d01b03040c419942140c005412501c6400c180e400d002d454140898100e0449030809060f5155100003943c1c00d586540e840000c00c04207107400fa41d103000849891000e10029026a6111940c1e60b94408510580e00e801081e81131001d13060704c040016010940100b4403140e02c2d4203004a100c001601c60645c103494a0f440160561030f402910098059203083c12055840c107 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 133247275 1250 133246025 133246037
    0x6060e0102010513140114090303040302011508070e0a270b1018050c040506070309093207030e0a05010509060903031608060d0602040314120418020702040209030724 73
    0x4d0f000302515034040c0c80c0291503181d58848240c403840080d00001000c0c14000c801c0031041c14440c0d40d1681d65841101e061b8010f52070700c4490034454484001510417149080000c100c0242094600114180080c0c44070b813003180d443c02c502c07011034001c00510b49107800c003ca06d50034031215418060440f00d0000c098203c4001c0c490b4051080d100c20700414008003516200005182d070b504c11810b1054400c5030010780d8000c401055240415904c5004074081c1c2d613a0110600c50b12400060141c900c000507066459058505254542840006507815a101e0103514002c134102410048040c2800c0c502081960165103440400c044a503080010701c1c0c010024000a502c2e62500c14070034080340889070401402c20109402040c090f580b560821130b8401c5c0c006100f103548542c4c07490654410b52000ca440981400340c1d03060402800380d440250b404448000e074280d03030000821510324000b940000422a4002c2d800d228080540d1010480ca901518401829000152403407014000c226041d00d001c00c10802 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 133248525 1250 133247275 133247281
    0x18030f0e03120a0507080909162a0f020102010b19030506090c01020c06031f0e1503060615070204150905040201020615010e040915090c05010e2b020612010906060e01020105 76
    0x102412101d0041c298a085074075a6034030f282121b480c4c828403c545621140080070311076801e482503d0300302c100e041030702c0d140c00074aa00c90071103003802702521103402c202d0580c024000c0455074440d0980e1f03665205200000f02d81c600c03cad0000d9041100c51065035034041c804201481001010080c003a001607548004140500d001d10000390b40e84100c4250314003620021011400d42007040c80d80314610700d000b00c1110584c546402008600940484008001054084007440c2600300843d52501031074024081c00f401800742d1464068907400307032204981203590340e06038200c1000c00f819031802400000b0000310b802c0c02c00d4000240f43c8a40030340092107501e828604003903030f80c4c0c100c0258120705c0400d8801217100c4840b420700c46d4028002034414442c035401c0451581c200417000d41c80c50184c1d0b200740c0700c03d07103100001c909000c110307101c1d5084c0702d42a90701a101003201000d4513292000c1c4620040134985005a44168100b04240c01c1c2c2c00110040d1320b0f02c8092200d00d400c4003151036a12407c0c40200a145 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 133249775 1250 133248525 133248553
    0xe1506210604023606010e09090d030c050c010e0a0201020f03160f03050705030d0b10092601060513090b0a18120e06071b17070b090418030f0e03 64
    0x7000c05000240719240071100f508580c0041d6015a98000c204e600da103c1c5909138465224200c4000c03100726000580841c0d0b158030910b0000c032924043e525a000910309506208070580091043c0700d028014880180b0240d403800f107090143e218009407584c00303064220090320029240c08940d442e195000d4106000040700303895014a030031080c681010340b0038403020007818242c4192044c1e80000d05036020001d211620b030001c0e03412602070308009942008011020250803179400d9118000c01d0030311803001170005401000960802c2c4d4104040000041d042e568000081100440da10804035090719481d03202d06001042c4402c540c40140c002c01401003648004482c040642c02e41002400d200c1e104100090092062490030b6201501504240c0d49210a0610342c04150154244280301440c0900100340d0403001c07000001e030012240d000704001414903029444903081428550380185c2da840c6c1c4040300300000094896610300035150150f914001d00e00003402c04580c86070340381c0a81e1061070010741d03c0c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 133251025 1250 133249775 133249783
    0x608011103130f0b0a09020f030d050a050d060e010608040b01090c09060807030f05010f030203190c0314030c1605091003080301090207060609092102070e01050907030e150621 77
    0xc802c41e00215080001036191070386900c925040060155562182004001c0e243c84e405002d40900803a220f12148011500b09555405030543c01c07030005505014440000f03000304003600f940b081e00b010201c0d03140d0312071b04080c0b2030100036400000002d28000603c0207000e103054001d405000034020a1200041d528006400d11401e031242d801001054000586014480d42c884800d40014210038081da5948241381c001d15060340c001031307209006500200510240e00c22a0707a81041d480038041c14a207240d6120760250070641300510030395000801c80280314010520503040c80020303d0000745445820201441107a0900a103034040c01c1526150a1020803a1441a241114000c0c1c801581c1c1c0e00b40c42ca0490f0152900d54414610f8500381840d08041060040540c0c280903075190342100a00709444040b0b070b85030b40620480124003510300042c0139508003003000551003aa1410040f07084089180f225141000c4030161041007031320041070064502d40361a8108100358905a0407000365044012241ca03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 133252275 1250 133251025 133251031
    0x90b06120406020909040606080d0528170403030c0813020108010902030702070506070602030615070f02010305180f0c0102251503090515011406070305030a0509010e0708100608011103 81
    0x1040380305000060800106404851160002400d0f034140c0c0e0600340740081c0a403980d400b500c1c141c2e003d8000c044450358850000c0d1542411030a880383c600e440b0340400f000b00112000019030030041c00041840d15032500d07048e0765001d54480e540c0024031410060002f06036901c0641100440d0f0f100e07900308805030f0303880004141518200600141c4d039442e500002e900c1c100d038075400942c001c4804501102409480c0d4081c500c218410f0790079103604007480000c00568890594000c1011968952040265201e584031550010341ea42020003002d0301c00e840c5c1480d0050444501401d680150b40690703107540c0c140014070072100c102110b04218828424807103c0d050b01400313082c401407030810314803291038820340014034440d0300070b016240048448008001c29070402d00030540c988441740601265400e000c411500b60340d4050780e9480c10740e11510911000780c400504444442c2d902c3d4401050b207407605111007001032884100a01600b15014400000d403509507220000c981d160130400303500c0d10411011030394 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 133253525 1250 133252275 133252297
    0x40f090b250c08181c051c0503010f030b04080702060f0904060506030907090e0a08070308011707150302031801020d09150504030804021944071202041b020a030801090b06 75
    0xc4c0c40070b04002184802a00e0540c1038092003507840000180200492102c0c00d00003080342440406030070303003c141c4031031100b84200500c411a829040022802510724540c1040c401c203821458048140c001807800e4200c541207444040c40000c08104514180c400e004c000e0405540ca5411442c2045140340c466250348614891030303486400800c4044000d0124000484d44031840b05d481d0002030900418002003400b40c0350007000e401c80d02202407400000c50004031124003500c0341503400508012800780d0000350a06600000c00103030311104990078000340591000840000907240721a003844d401d08110714a901d450300703140500380000300c0d40c40001d9030303800b0740c0603588110480e00ca03070121144282c460744455912440d80e010104c4509070904050751070600065030401050001c080400c10f02408070848a82c2e034010401080a4803080044c08581400200001010300310500340c100d4170740500b000c400040e0450340b005c0e02016000001c042c050803440c0c80c2004454002c4011800390320884907002 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 133254775 1250 133253525 133253557
    0x1060612020d09060c08100803120c09060912032a0703060203091501091b1d2b08130e01030b0105090402041b020601030204110a0e040f090b250c08 65
    0x49030b01d45194201e25036065002c0810480c8403004400103151030816600900c1c049010000000c810a0001c1529a0f41c211382412001715248c07404030822541c01010441e41020003880613402c43d6484602405072584810041e590380c802c180307405000464155001407001000e9500d02d9603c410000b03064040d640d1000c0010f0b500d031920541186007103c41c05205c2d02c086001d400126440e0b4143d040b402600c3d0b0480000012684014015195108510500102c0e032464002079005883e00c80d081c0d00380009002000c448140c40703505011100c441c0d081e029030b490780e00001d143d1042e9400c400060010f1403035000410a42d41135542c3d60f464903206100d0342e8480d6003204081029541c50354041443c1e0f032100b0300307a0b501c00310840c47c029440e0b07a0240700503031280380b03801880c4071004104400c0b9028410075550b02001d50803c030003008000c044411201240344c3d44c80c1c4c0b01c3e40019a52194503800307014004003800e1500c400b03010642102d0b4680310203000308903071200020005844031081e94030a051084540e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 133256025 1250 133254775 133254787
    0x30504170c0d0f0501050a0207120e0a050a06050408071d04150b210f0c1804260304060b0d020109030209090c090106031a09062d0a0b0a020f0106061202 67
    0x554600740a120072250700c48034000c80b80003000541d60141c20824840d030000e00c82566040650701c01ca005410020380760504141440e00001e20404442d0b0200c03400801c444c411580b01c01c00315003113007200d8002c03001250b000242441103150811000b00204448030706203105010700001c080070144054002001da051001120058422035003080401d503401803da01e07a15082c09601c840a82610500000980140c038181c014600780170802044007080640500c0040800c4c0d9a080110200144299950480b0440041310100012003d007080b190812820b901d90602e07081100480d80411081d500c0f03110035905810050341c000240307400b01c1e901140c1071941551092100c505213030703041c0459903020054500102d813581d003590180040908a2081c072041031724010603c0f0715040d0a40780154404404624a454100050b01c101c50010807040348090f01c49021700850300440f45500040b248410103d00100115410000d1500c021886002848800c0c60044050320140600d0301d540c003500d4002500c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 133257275 1250 133256025 133256069
    0x6010f03170c0109210f08041707050a06061214030a02060c0304030c06050108060703140405030f1c05090601062a0305090109030f0809120708060a0903090519150309030504 76
    0x807900e4142d40000e5003580c0e040d011040d40c80c5e1215070000000100380b000c4048440315210342261441560b000d81845043c0c0c0e1281800b0065030840b120460716441891500340010380360703010300d174010140904081d24515240c5445110608000c4600352030354410710000e08983d81c00640c16070404905524641c1e26211070404641100341205e01514030760500c00000341110000036200c1c89404960340c1000461900c80100c500240181c41c0a0096172007030080004174404280101461a018424000d884d0b8400c05000103a8104484c0c480d40e60f00001c00410041c4c0e046206244805c01d412510030003045108440031540c841800e01908115000c00e4403180360f4010301d60080070316003002052150030740c1c03894031400c04d40c05142100c0c0610300742c0742501803559000980710309503014000905199540c02c80d40100800300080b0590801140e038000041984401d00c2020134011044000480142001055108240c0c001c48030000c0600d84400c080202c3e501c681a03606495522000f00d00301011194 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 133258525 1250 133257275 133257281
    0x130603051e0d081e04110901090b0109050613170703021c0506040b060310060e180f0d0302090a030206040311041a0d1b08060c0c0727050a0e0f0f06010f03170c01 71
    0x13803606002c1c24042c240810300c0384c0a9910b2481c00021200701015a80340c0301042c0030348400011346804108900d00c14070480c5028805403082000713240e007800900e44c2e40e0704074290718807146001400d5604000011b20540c2401c05504030a09503e036080808603007955038039a0340f00001000070304000c40000104031551303400d010f021102d48680600703210483e09c1d444070300380c506c0050700d0884511420030300f0b900341c0000c04901c0710030322840394001c2d28038820101d0043d0080d40c00400c1302648110442d4020005941d4000540083d602603052139151800040500c070854980500940103030b0040c078032488235562a9010101003d034004c80342c5407200f80400d04862415126004009036004603000c01800d10f0190014043c22040310003110091542c54078502801000c0081d100c040c1200d04d9480101c08603507800907074028130a8040050916034111143e0b050190b0800740c80455002002d043d40350b1401080175502402c82d41d000d4181251869481c4c41003c80d8000c200c6981030780102e503a21103503000f94 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 133259775 1250 133258525 133258561
    0x9020409050601060306080705030a11011206090f02040303170411040906020c071d070809030301090c0512042009060d140f0304091d0109110105090609130603051e0d08 74
    0x1c1c086450550f140c4c207000c3c0141c03516000f040b81030f1041ca00b00240c149000119403626a400c846100c02c66500600115145490301e1315490300f00c1c1e1a4100083c5030343d25442071003000f40d00f4020060311079086150042582c600c2840c0b001450b41d01c803040c0300c0881c03825880c0840701c00040303c00198102040c030705480030b809031160f124240d01a0250020701e08030301d138201240402e0094001201c940e0703482d20640d141e000035904030181d0fa00c28030062040c035a05d60300032101d90307d55052680c00c20002528400000404880c102d0b0001040011764140320081002c1544480045403d90460320342100461400703080600f01408401c0f4078021220001424402c9010b0820302c402500d41c2d4076151901d0320040d102007001030f0308018400d000542c00d0001031240400e481d90160360a408c480d580801100c45801030309506034000301c204a003400e0f0741c0c1c9a0030500800d4a401d034000c950300d455410007074100110302104209841c4032008415443c130011410b00000700e15401c00c47c0c0251281c0011002207200c038 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 133261025 1250 133259775 133259783
    0x305030105013510050a090506090c0a080c03040f0803090c0a090e061314030c010e06060d020f04050a0204080a0c09060608070813050a1403120c04062102090a1203081b0a0309020409 80
    0x12400f0a41c0c42c088d400c140d1044c5010b44959449458070140100e003423050117240c2c00081e11031000300c1c03018502e0314000c4d03402c10b00580282c44a440c0c0c54a8200d003c0d8425a03029480340d02c240b002603400c0c140001c420000b0840600c01704444003070b0548413a220400200321404801c0c100e44944104143c490400503a1100d1008807a19000039210703960080480c900090181d1003003100260317161070314819040185902401c8160410100b0341848007403d009407820a07200d80910020410000400c41074032007074029052a50a1071800c8500345c00c81d0700c00d400c64800c201c40d19042152154100310050341000f050000180801d40710f00300541040aa0300d0014289140401c0744084200d000024250390821203160304407035100d5034084086803003240305802c0400d0042c0c59151995281e41c840307a0001d100520058917009001c4005648203040d60007000000448681007400c0c141d0044900d9400100c83d0492180603410100c0d10109004450b208003c06458802c00403c64481d46c020a081980c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 133262275 1250 133261025 133261039
    0x70801020a0f030b09160503060d12020703031404150c0c030812011403061b1809040b01031703010302030c0906030a0b15100e0d1205040b07030503010501351005 71
    0xe000ea000303012074002000b42c070000b824000401380c1d5141c2043c0d824080ca11003d40714400701440c4034251402e400040249502c03e0a21014034007151512240c000c400e07403d980030b401000c6c218038001d0a07404a01034088607082e018401404500e11949850035450080c0c20107072400c0e03145141041d01c0241540004148460107e19042c3c080c08800754241610400304a040c0d415103000281a507070b2078101e620071280f00714040d8204188025900408006070450000310940f280d05021420200050b80c0c200d42c00600c0c4d40c010002d11107001d5005400811031070320a4519455900080d1b0b456103419a414850045100030032a00c2d80c0400c0078105840c0d2214290079249451601481d2058200c20f000780200c1c24055041405441040782415018001b001001441101d4481d01c00e14110455504280081004042130075a000c2000d0110740e44a541c1d0f00380c1ea58145000107040c0102407840011030781040300e0b240c50700a100b03071000b0303a1180d0101d403000c019aa01d211001c40c5811941c4101d0f00310030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 133263525 1250 133262275 133262287
    0x507090608100e0109050a02040e030d061e15090603050c0c060403020703060501050d02061204020612130c0501090803031b04150305060a0e04050a0807030c0c0617010801020414040e07080102 84
    0x114082d003010300c00381420451401c00125140c242c1d100720500070081d0700510444401031915030300580009040300220307810710301c04207041c0d011100c1e20382201500d503020210a0598055289035070300035213039070f44080c1013124200c040a0400004d50017940c00780f6031030f4400501c80406d1801030b07030450802681112081c3c10903040181d2528100d000940e101400c240000c242e5042409000c408143c1c0070380b03494900300e4005100c07020654050b000302e17884003080200060069041040b20301503085000d023165072401900d8450501681540514180000c4d200104050340c00801525030021110614070340c0030340004821645442070381c000d0341700c600c04154609082a456400244079590903212408841d0310b82c008822000700880d00200310354010b21048002991940c06805014820305110020040c81d0381c50712020340c2c03e038000c50000b43c045043c004800204166035030043c10031100851800d8200704180140d0010084118040c68441aa018550404010210041156034002c41d2200 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 133264775 1250 133263525 133263539
    0xd09080306010801080c0f1909050f1504050c0a030b0a0f1716030222140115020606010e0603010510120603050c01021b090106030c180f05120303090604020d05070906 73
    0x1400c25a41c1d10b002400d940008500760400045800103200002c04280d84a410311040141107141025002c04000041c840015015458003a86004001480500c859490030703040f0070000d4900c10210900c224101024480d0041c100c5080340d90b08001880d0102d001c14048001c03c0d00104e855002c2c0c1c0340004030200008000c040d102c60010301282040c29918109440541108886103502010350302c1500c3c00c041c40b80d250603020100c58005042a000f05159500780644480c3d81d80c00d07400b03001c44140c4009100003150b07043c040d003944103209080080120380f144000c074259000500645018042c8548a0b404403402002101c182781551380c03040c4449500c030f01d0b01c3c54580041c10090f60141c03164903150004031510602c44280c13242d0141c44101a0b80c60000210050000c0e01190001c2c401441401c01c221062500c4c041d01400102c1907040070507182209000c80c4800196986201381c005000b401801c0c1800300e2441c0e0082c1e0100e0341c481c83e10806c1e081ca1401c00c0199481050700c9450180001075039 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 133266025 1250 133264775 133264777
    0x31302040b04090b160e030a02060901050c10050a0204050a05031f020a0e2101050112030807030c09080a0b010501080c040b0414030c0a0e090d0302030f0601181a0403060e0706080c0a050d0908 84
    0x30007170b595070f0880e80308001c10a01d65a00c0780403000030750200007032040410551055001e89811200181100d0043c0002c9103c403040b21010b684002503c2c1c0c0000381407001e030410800c200010f0030150010001080b400d1618019040011580200d240d00019002e011a10491000d5141100201503003032156a240280000d9400f07102c000c0c0d6554200000010f809041195214106401d5220102c0c580e641030b00c2180185950303001c100904c5000e007000f1034048401c00030905824071840425803c4d50400b0000740c4440e600038a11002004108070621a007000442610106c40340180180031140302c0381c00003420200d8600304250000000800011320300d045445040c080c00d4510705030340468220f400100c007a84811030b618040c501c90040400e550754801d01a00a030302220041c0c8040698443c5c140c42c0c020002c450b00620300600204003070050041d50b12a004200548100a04205280c0000500044401031009650a8011031142505406042141c18258040c00c0403c40c21946103024289 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 133267275 1250 133266025 133266061
    0x6050304020a14090703090f0f0609031d0d02040e030d020f0301030b0106020105160c02030703060c0906080a020403050d05030703060e040606170c1e042915031302040b04090b 77
    0x201c2c500c2c1980006007004581c20304100301d0000b9145140550b25000140c0142c01101001c0b2007030501010400003103680c0d040d00d00c1006200e620042082402814010000010001018002c003002074244dc2159182a015088641d0694010405140c404280da0a601900542d00b009a0001405140e028602c5c2d0085041e00d106200302c40003640c84410480c201c030000c030f0303c540c4003040074900514118007039003038454400d00c028221880591665120350585030307000880c1020503c504014003840740c024031040c0d404100144210305007883c58460079507418103d20040b00f4841e000011a80c118443d8200c00003611a1188404441c10185030040040020b80700e459100d101d01c0700c0b2840c21f2074000c80d6401c03107400000c00030121000d501e5010407070b150714141c3d1641e02c00c2e0358001c5600044003400c00061841c00101140440d600d0100c01c0c40310f90126042c12000401d0108204510f01c100c003509032803195010307103000a205614401060040072281005001e082c03004007040000b181c50014114 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 133268525 1250 133267275 133267279
    0x40b04050901080c06030105040b060c010e0c18040209150a030812060a1202090705030a02070b0901050612031908070c0f06090c080304060203040308031f0303270b0901120b0402040605030402 84
    0x1d40e03a07a1010340c3d2030300c004d00100c580c000130400c0101b1041c64284c00010803004001c00142c074100c00751400781e086031010400c1d120b054124036890301c2140b500e085032507117090011411200c245000d500181810344002c05201e0b208040c0a246034542d1a86840400910390080d0041d0343c490750391380408112a011a03001d481140007001c0480c130355001103013840318660701620604071074680d40002d071440e1700010500c0c0c0d0740c66803e100c2800400c4400d07000e580500806c03030000686041440074840b0000d140000b4150640c0104401c075458070380542000710a1001d4900005d841d2500c4004a65000341ca40f00605910540300d580001d009940c1d02000d5810312403140e0380a080e5841411a441c1c1c0141c1c0718060141c1c1042c0420004182d5800c01990b0100d16285d503240080b035a6412507400d07010315007040d000150342000d181400900402859956007900c68130301c420501c0c00e00400002d100344020241001941c1c0717140100b11300c1d29005032421110091007552100e0300e500c801005904102d40c103038 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 133269775 1250 133268525 133268539
    0xa090503030c07091a01021e0c040f091e0804060e1f050306040501050a0513050c07060608030c0105060301061a070201210e010609060f230411070302060a0c020d03150506040b0405 79
    0x400e8402e5100b01d007101290181c000c0d1405880e15223081c0034a00f000040c802450081c211010200d585520495802c14002000050000c0490500c0d041c462000e1030a510f420055010400c0412220015030341140e0161502100b0724006101140b00400b10354210002200812802c001c202c0c0c100d00914481e0741c00b5039003003010baaa68010010030f045e09116594004c05508032580c020410f6400865000010207221843c290760340e036400d41200e0065015046a801c0402ca06010800270702030590440801c8000740a041e0800c000c159040c480a0000c01ca82d000000e40c0e0340443e4003030054140703030156280d130700c1644030044406500940000211049a5480c160000c503000103d8401c500a40702c030b4019400045081080d070103406054070303c3d032012140000d0040c0030070f95901d000b12909190248050364488891346400b1745042c101805c1580b98a00785010310902550000365212603214503d030126615100b10700185c0405a190031140c3c208000140206044603118014011a80252908 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 133271025 1250 133269775 133269791
    0x3030c020f070b0a11010219021c03050108030904050601170108010501050a09062105030f0d1e050601120b060c06090d111504030c0303020c0102160606081207080a090503030c0709 79
    0x465103500075070260f00b0442405004032992036100e0130038942c00848900005103000540c5030b140c0c21000c0c050700a0030060b4841c1d081d84040801107104005103001c07505040c00554100b40d03075140c49020b4000c001d80115528000541560300c03641090119441c5a9040645075844910b424081d0030240191030146820311000240211644105001c45104030a88a147c101240c016110307008500d405072400e00c414014401c50034840030003006510000c0d0400140da90f190f1031031490000d020245104041d1030b000802103a070344c11003103a060701d102600001414000c42c0001580d0303402040d10310745882c4100c0c810410041c41c002a800710741c10b0241c0350400149010405a652501001d83c4078100c44c20800c081000680140c10b0310442038071906025061007404d5207c0c50881c0c0011484480c180c54108107001807008620448020301384680140080503901c1c100c001c014411030700024805003000400d280c00d50701c58170030100607000080560b80ea400b030b9149040d0392003000303010700c4040e5032628400d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 133272275 1250 133271025 133271053
    0x2040c020c03030409050411120f0106050609061206061b03070b221103031e03191a090604060b0a02030d0f060f0e0405010b0301020d020d050a062709020d03030c02 72
    0x5001d100c500007001507142909089904001e060f01074070891780581868000d024669030049030010f800100401011520f00c001c58440c03c0d585650b100d540038100070800380381c0381c1d2554002c4031540142210b0f0a0050388426003c240e0070f106142c0303090301e4440d81100845074035002200408820f802030741011442d445001c50312074900754214200b03592040c140010f0300018105905007070f5011004041d241810084602c9094040050038400e0030300d20004100b041005612a540b5100d10700054108075000e0310440e03449105941040c101e100d4580100003810a965580004002e40030180d050b46d100c0c80700d148007a540360403008281032000d0070001d05841100c014030800c02140d00103d564540d44d4500603107017910090290098071107540303500d210211501c090009006400441c9801070f90703925410000403c403400a40195085814642c04103c445140b0100449012007040d07203803a08805d0580300380c018004444000d40160900030600107164040e44000b11007407098081d135101c18500a0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 133273381 1106 133272275 133272283
    0xd112503020108070206040525081b011b0201020a0206070302030c07060504050a2111061909031103010c1d030111040b0315011d0d0305040e090a02040c02 68
    0x190400c11540c1c004040b0f0f03840912031010780f100d42880d80d01d1030740b0f07030018050154450a041c00f055140034010000c200041c0320071801c40c3d04040525200108081c40d5843c202d000c1808825000001c444181e2404a1076905901900100c00107500700105904007950940461000b4880066681c80402544000d40403a86959881d2881e00c0200b00304401550017003081d041c40c68143c1e501501001c150720700190b51044180102d0176050700440c6042c010703001b428045901d680125482d258006000c0410340303000302102468145107009040c241c810b6031804500154401080d5422448641c07000031039484010004222004002040402a000350700710240a0070700106000441407180c0c4506038a04007800c3c0fa419800c1d141d114040200002651780340200ba02c000020109440f4034222b601070590107100320300030f0a0100541d0380d2001085000ca02817807501004d400240c0c0006 = true := by decide +kernel

theorem cover : BRFrame.Cov 133093525 133273381 := by
  have h0 := BRFrame.cov_init 133093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 133093525 ≤ n) (h2 : n < 133273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
