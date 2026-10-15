-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3884
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:57:19.112304+00:00
-- url     : https://prove2.me/submissions/c79c3d11-1938-4188-88a3-096ab6a2e0bd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 698381294 ≤ n < 698561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 698382544 1250 698381294 698381311
    0x181f0810080304090f0c0206090c0d0201120212010302150f0a08091c080105040e120d0b19030c030209250e0607080d0603060c020a030f080a091a06120c010905040e1203 74
    0x1102000c0282e00c0606c0341a0390f5400e80d001074100c40c54940003442e01c0d00303180011540034a00c2003070810304580c0b2591042c000c09041080454588942c91084080311000b408228000c1060b00b04c1021001c003c02c081d1014403420703c021a00d0000040d004403481800031303101e200303588a1003a100600202c5000720308041c018543d1000d0841d0f1415040005a513103101030085030380c02070507000c58000410401c481e0080300101d004640c0902500100b101c840248501e1070200d0013070700300401000000880201140d0080b00c42200a445419003000700900d482500203400c2400c0c04c0440704240219003040c7e080c0e50040c0301c1c43c04c144484d00e40c2c20040d030080c0388041280e41d50310014803c200041c4543c489003c0103200418805d0345595020342903104c03070100c1070140211200010300c5c2e60025080561025070121070716046c014005602603001d00240e45840c030490704c0c40c0b20b8080003a40044c51a94192050b502c1e05551440c180600000385000110025503005416548081c40c14034401180200c0b10b0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 698383794 1250 698382544 698382551
    0x70303140412031104290702030f0a030e0a120201080601020c100314130503030f0a09060c02100b030f07031514070c210801030312060812181f081008030409 69
    0x4050040403145a02e84c1c1c608a1202400140b00e0a41900420076030005800c803680c9040c50070a114116600440c100203505225400707103800403080c0480e028120a110b034840c42210b10b00003042150604c0d982c064429802824002d81016611400303005400c0b80f81070054071a00c2a400d40441c401103400260400820b80b94641c9143c0305100821032640901406510007400f005903546588a20026000090b42e03c1d4002c080342c20b40f0002c2d031086050aa10510404c500e560fa01d40c003a407100302c610014a4043e10344481001c460501141c080c080001c401d014010360750941c0d81c1c4034490610760f80f00c5940b041d07960b034070401c4140c607001c2418003031021a00c40d10359410491514400c00e507403180300100c0b4500716030792120706d5036000560302d8152a8142004298640e604a003540200995801521207200781d803801d00203980404000e0100f1080151280002e5502e44240900f00310400b52141412102c00f10f000b80c4988250b0319250000f41e00f43c004600c1c50354841c6000c3c50343e0495044007441d10340c0d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 698385044 1250 698383794 698383823
    0x12c01090b1809010e040804031403190e0405060f0102060105060f0f070c080d090305070b03280b1302040503030706150902030a02031503010b1f05040807030809100207030b04080703031404 83
    0x1d00c801414010541141d490040341b500355643e0007540114032004000100d0360102015415080c402d40d20006100c002c4401c254040b0380c0b0041c4800d140008841c000c0b8540804031700181070603059210a01010380040ca200c0e4030306070502282da4003040c1c1c6241500303c1408400c02c80b840d14001816070a00410001c0c0115080041040c10411091103120900400d00c10410015070040381d0041101c0101079556204e81e00e0b140c11544c0c0c402c24401c0001e15017101c00d041d02c060083c3da801000054000d80d40840411380c0014400104d220300d01809502da03006100c10b800180658100010300f0102013071510006585204007005da80040d40c15201c01a004020403400c0ca0b007544e8414a141c00440c000d0114030707550380200d040b11001444080104003000100405c00f40204200d5000b40304040840c2c0d0150341d83c3c14480101c0d04075010041c814801041e01001c45840005d980d400d03070703421034815105170711603554009a6500c015030480c14542c03503401003144440000301d0648114002c01d0840003281 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 698386294 1250 698385044 698385049
    0x215090a05010804110906222429220306050a02090f040f02130303050c0d08070f0f0e040f09060e031903020c01110c03040801050105012c01090b18 65
    0x82500100d0402080404004c0070403d4000c0141c011780094411405603282c0c44042403850203610b1032083e903018581d09100d070f2400b1641c00014200303603500c210583c47e00c0310309018401030721502c504450314209000841c0c42004a901044034550410300c0c462500308658510020307104d0f1016150b1840300c2040c1c0030010301c101401960360201c02040114070784442d03400000c003a407403a1500c1d180203542c0c0b0300f03945200f40b196a0403144503061807030f111400b0913520710b0004d1240c0d00c1420090200e0092140000c078490182c0581401101140c03038150b5140c4245600b141c202d91140e941004000507a65120f1594603644204c4008050008002c40c482009040c0001903c0310b504401185a10401198201902c1e22094420b000d500c5d290169640d081400090701409000da503120401b20001404201d2400000c002e10403640c4800080c44241c3e680d80040d01c03410292440328003214108200d031094072000b0100d0b030f1221501410942e804075140c2c03404189982024149164094400740905400d2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 698387544 1250 698386294 698386309
    0x40e280f1208070309081813020313141903050708070b07050c011b020c010c06020c01112a060106121806020414151b0f0f01060312020a260403021509 66
    0x1075007401c062004802e01c4ea030714a0244900c45100306a60000140c071412a61441e41c0388048c00320441003951a0705100300c0b180c161049a4800303c3e04081c000caa2044150004584080c144013030030a1807103804031030f4034142c8103544050350484034501d0030004000011a0103416502030425640c3d03854490b0702c641c03112821209649104c0200844004c0710120003030f40010720815841082c40c0c0401c2007134142c64880040e00609130320b00459420104880c0c02e0b0a11700c00035003100401c3d041c442502d00010f801c0c5543c10084659240383e1030304640014400a0302400145500304000c0b20001042280380044061a008601c41112810b4000404114086144841100d1403000b20740c800b60104550341061414480c0140d04504004144071071840001c0034400c2c188804040e0701580c45000c00c008001e0300070040c902086481401140d5012801c1344001a00d02c0b001da8003103c0300e80c1c0624101009038800c1d050390080c0c00002403c10012005032105e40d00704c4200814a0310450721480f01c0e10410030070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 698388794 1250 698387544 698387551
    0xc08060111060115050f1603171015200709051e13080906040b0910030b0f0906190e18010b0105070b060a0f0b030411040e280f1208 58
    0x4000c01820a44038500c000700c1c2c602c1c1120302c80f81014504840d90582075601d4014044442d0301d542000ca4105e120746984542d00d09264440d5135984400d001061002c5107221040c0c6541e0b240e400c100800b80901401400e014080f9956030070200442078868005040c3c41d2401a41e4035015001208100f0000720f141c000d060b04912141500c03c601d0140002d21440282d0080c54030380b0f5002807800c15024082e4075021560400005466030346c0c3c076a210011107465600c03c858281c018490b1041e05407003d807013485014202c1d8402400b4040b8240c1010400c000600c0150110380e11102c003e041034a00c8192080c41d90050078410040740291504011601e809070344103042003010b0341002c40c0bc1030103a034014100c43e41c01d54840120039260b05c51070b0100b80b4145080d006030801e039015080105041c0c42c0d00000e98415880348845940d40800707001030005440850658070040e03030004150000384005540f01e01e400185d4050410f040240310713280d90103004684a0117803820740040c0401002d0729070bc80e5a0550 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 698390044 1250 698388794 698388797
    0x20d03111c0c080318031603120606051209010e010f290a05010f0e040609060924180f090303060302010f0801030c151803030f02010c0903020d06020306150408010c080601 75
    0x16a81e011401a00c10b0b410204010280c0c000080080d1090402c403100140307038a131901c00c60351505030030445034201404010007075004c01c01080300c06803507a43c103005540585030380d03980d401d041010000219004550180070f81e80155224402499039810900c1480c040a5003c60040b0300c02407807004010b4100f10003c603178074441e09100700d03036401c0b5104c8600305400ca642c28617150b030b158a6a07107c01c40c1e0720034004408950250500c200065072051640000301a9454140e080000c0e85060f0704400c0c4401001034100c201c0036404104100700c0680c0ca03c003800d4240201d2010804240300d120710001c41d14400c40450210340c1d10780090043d540e0251403048010f0050500c10201c0d4103540f640c5e411429980300f246e84500f10810302015886c441c600300d41c16100209540450b0980324038000c3d2420035580c4040005601c0c140103103003003038441e1070101d0460340c0103031031500c400e00300e5110000a075100400e042d400c59050154402402481801000100b941400015209548440040c170310240a0170007030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 698391294 1250 698390044 698390083
    0x501061106060a1a0712020a0605090d0c060b0f03191202070b0306041812030e0d03060f030f0809181e04110123071506090c0219020607020d0311 64
    0x2c16218185a80309030b828800b404003a80b02c0f604601641031061940c01045038203c041c5181c4a035400007201000188203039428001541c030f0800e099502c0c000c2c1c540348000070f03400114200100c0d50341d51284c201c92001030a400c8200360000040f0b45003d44883c0200d8003130a23404c40714020302c2040500701a508040f480a058018030700415075040c2e00001c0e090601c0381c2d0f40d55101d90140024807a00e413071607690200710b65a01100403a00030b8001c00205e80c081405018a0341031100481c0b04e0320441058400340701c030a0107501c5c1562190601112402c07000c4a1b039800402c111303805035480001d00400011040505a0b680c500b0102550020f031041d4810f00520704d40d02c2c28400000d910540e069212082031901820090544100c01c00c0d0145241403c01c02c460300107140018041d0140140010b1784140340c003880b40030365600b1090201c4000c400c2c2d40700140c202d00c0c40006044203000f1407004040c0001d00c00c1d400d10b104d136000160349602203502100030030030700d00d403041102a080c00b582d03048a40542e070b100c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 698392544 1250 698391294 698391301
    0xe0312070201050f1606091103100b060715060e1003030e010f0e0405130b09010e120c121c140f070e030715121802091b0906070f02030a060501061106 66
    0x1906500030f0540c4d21504002c0424026241400800141c0c80140c202d0303000d10502e040740c00c0800c2506000501c4a00901a295a840002c1464007071200d061201800c010f20f880c02c191234090001038152a084640740d101c48001400010302e40c829802505208200c1640c42e1840c5409002d803051001818140407164482c03400720340d042880c0c48281c0c06c0c155808900c0342d50716207590701c85407028103005040c02d2070001800040f007015801450800800d60072503801b03d02026900d03415000308106085150f0007144020416038540c3c020b4010101001001850070040c50b0860301940e94402c4075013802d0101c0800c002c0000042e844491300002c050410050311011080843d0f07d0340c06a008100e1261900c1d10144503883c41075140c50b080300b04500c0300f0071565a08401410485900780001da10a0302800c001c1610540d41e18040762035034000c2c0303800e6447c0014180c01c1c4142c6820000d01560800880c892034809a2000d02c01840a140318403000900c0358104840500307004442a0f1402e0254003a8040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 698393794 1250 698392544 698392547
    0x41a071707030216021908011d190c080303010303030f1d070b130e10051810030201230705060615070b0a05100308041502100e0a1205190e0312070201 66
    0x10990061072a1070056a01e0b41c101c150107255410119000390000304020035610b040405000c19016a680322000380000040c41c680d130007003501110301c04401d07a003222014400105a00c407810780e006225641000c0311541c0c940031300d421074000b6403054000ca910b03240311403005c880310b22444000c040b107156082d2010b0721422200d642d80920740104505810002488030030000b04228000c0101309900f40a1100d250079002c6003028036440c41114000c40d0a00100002c02c01d20441c0d40f44111700035204001182d00c0c580046440000c83d50003103444054100e084c41c480042a0001c01c2e190780104010185403d00000340b0000380c600c240550420b81c4103000c058001004101c0c0160041050300d004605500c1d80b0a44440504030795200070450300700082c00041121803003042c1880000a44c081e1907182d418001a0801da030320040314003c503500000512030024032a00300000b0b5044c02840c0260803e00983c4402400d240f003031b003ca4011548001207407400340b80c10401d001030600b50514240c1041904e900 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 698395044 1250 698393794 698393837
    0x1060f05030f04170d0b1003201e03040f030906080603030d0b04150f03060b010311030406020a0e0405090114060409030203090d05011b031d160b0a03060509041a07 72
    0x11400401c1c0d0321201090621803070070080070400c4d908052640e40c601031203603024010103440b040ea5000301201240e02c20505c2c040e1140f440b2800441481210081c941e02030300313100d03034840880001ca44400f9407038240443d00038400f8511551040d19150f140340100c0c2406003c13440e00b86d0040c81004140e004120f065100841640e10700130865001041f090346100009014041c0c160080017414040500004c281d00a41050380032240912030030080881c40c10300440c10b4440e2808038114a48003003001c90300064441d40140345c1800d991034030042c40c9180c400010103640303007079070704104680d103803051100160000d62409420210444040002000c44d41c1c0281d12406040c2403140b0031107081988800384071080d0051040003034505905400c0500d005000b40080225910001d1008140312130528900760000c0d01820740301c4074843c5000118036202c0903c40d540d020071084420581c2f181e03c0042c640e00c5400c12140203030322030340c0e8441403641072502544441400030000d02c00c0005144854a20755078102 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 698396294 1250 698395044 698395051
    0x1535090106061d011106040503191409090406020702041a0307080a050c09070216030c14121209060706060305010e0105060915060d09050607030b0a0b04050105160606080a050a0b01060f0503 83
    0x89588000741c0c44200103940309040c100d602e11a46c01383d5000c103c00c00101100030001201e00c182d5003042145214000c44030103c01e040d92240342007082044005d00c0c43d04000199002e0b209600c094a000c055501140945030784209181c1c8004507140c94000c0d514050080402505950005001012032a2203060ba144071484015010f80e00200110b440c2a201780f00c82e00ca60442240f020308440c0d501e01e415481000b5910550f4900480c0c1c004880c15454065203401c1030300700e6140144000b0301c0c00b0380200050382c0045411903100c00c082180344c0c005810350050741300460260000040c0750154001d85e40c259500100759512418031041004a010031004000308000b000351002c0382c94086481e4464001c2264032006042c0d849680100101140d040d001440c60020a482d00744060382d90f0600e014490113a40030319808141d044c010321024885005608008601601011600aa40d030300801d0401030104400d84503038220160325800c1c8101c400c0c03040c0c0180024584841e0003a00250014100d01025 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 698397544 1250 698396294 698396327
    0x30905011b08280207090b0a1212020f0f060a050a1503060c0507300305010f052b080d0605180a0b0d0203070f0e01080706050301153509010606 63
    0x70402400403032240e0074464080403401400745140b40e290f40069500d4045109480d42c0ca42131a0003411b4a0900d08081d00c100d81c80704940c01c003610324658440c607034110a201403c04611444150803150081000303c29150311802c80582154144180c664003541d400402d0103400e04c1c03d00754020404481d40d484941102c1d00213400262182c03c5100869480c03040c00c10150051030041145501452015604081810a150300d00300d1204980e60a03415144240700c4c60a28103d0b40100708180c2c108a0001102d00c1800049000c10306506020346038100c451910654018a0125200e144c60700b0604c903c00103440200c60041c100707520032101c2802100700070301c4c5100050300c03203401f1a41034440031404540d069008003030b241d41a440c4c0d00d11040f10156440350002401908000003111403000c502e1000391206035a0303051560382080301c0b0b100e00001480380d52081140c07000b1031f05801e803411400990160390b03c1e5058070240082c41744134240f141d0b002d002d180e03599240403030400031242c0010400020801d030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 698398794 1250 698397544 698397547
    0x51225030c08031e16030506010e1e0f1503071b02030319030902090114010e01091203050c030d020f040906060302090d02040b18270f06010603050c04180603030905011b08 75
    0x4020400700781c204441800c9006611100610010959545254102c3e0354039035410800341d900d20004540e40c415031444140c2111140c41c9410800d01442f0880450f404081c1c00882d4110b810380c0880c0414112014065041c43d0200c01c1c40b001a500112074200904034101c100d524100940000341c8074400c0c41a1100e0b102c40f9004100340890082d00b00040d00780d0002c28610301980e5810300d044c0c121864a0145002442500f8142da10b0360140401c0002e6403008a0350003007504484d0f50582e0b42d98010044d41010b44000d100c400c2984880c1e0004007400305404081b56200c910701481c1d00d0030344289030000428140184070071100d5071100341d543c02c8001e40450340413840b0b030400300125580c10200780900078115894400c004540080b0300310004101d40501c0710031540b9000104060725000c0c04500d210350b642211004010a610076001541c001c21100c02040c40d0941e1207036554203c03507000740c0c0301401c1d81d16008100285508000e20304001c000c28201101c00411041c0c18400d400504917008012040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 698400044 1250 698398794 698398801
    0x2104032d0f110a03020105010302012304140f0d06140a0e15060a090903020114090a020109060302090301060f080a0218130303090501020c01020403140118020f010e010c051225030c0803 81
    0x129540c40b5560b100e07441c0a94100325a01e0800a0203403800740000d07030105040702020034450100d0810440701c1030003125854145404d011694881d0390b000c10010f64003031190740e001c010550701c103004040380e0f0f441503000203414a11007200c1c126031000180004040340c50104801162200030986052155088192050940d1040002884088150801d00c541c9140103900000c058056000240180407610408096654038901641e211f040003c02400a5104001081514001e030090501418000d0002c5021511800203400300d036507650020b45150720020020055081c5104484054403c0841c14591072420411404a001409400030304040e40e4254a609010080d415035908403003010080d55202c2d0f032410705516000400c2c2d010300c120b5103082c0c0000b5000c00001e480c0d040c200d81c0902444001c2595000540303a001c82c0c42ea05e05c1c1401a158851000114240540c1c003001d81d400100799107030000722094500700d500424112a0a014000d040c03400300340c2181440c91f800d175010300401d40e02d03034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 698401294 1250 698400044 698400047
    0x1418030703050f030d060b19050304170a050403120207061b032c0307080604030c0b0a140a020c1015030f032003040311060304200102032104032d0f 65
    0x40c0550000c1c0c0580554818510b08603008001001e0207580a00103004264403202c030b13a400d500c94041502c1c201e250700741a00c0601802a0055030f03000307000e0940c40c440500301c0d0306603d86a038416400b00001940000d810710400000500f8890204064030041809608012014046d048003e1000742001c40501c1c14004051041c00760400b14a040703280801800704010310f507881c200b48a644d4503c00e000d40e010210308008000b0f85036200c2c0350581d441c01207022054441420004000d86126030240d12141500922400000728900400501c0401039079400c05c03180540c2481c410a04d8031504038201020b00c0c0c004001c09404801b566000b6280314481110b07442d050f240b232001c0c0440c0c4041400300762810a0015004806442220701840c0030070301c4840340c401040050320084600034800f0044c12911f92081da007014158104034010f004a074500308640580d40e00c0040101469011082c0b1081007004060740700807a20001d00d50840d07885101412198204a2135510150200400c1200000403825a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 698402544 1250 698401294 698401303
    0x6080a14091f151401091703030f07090e19060b0a02031e040302180613020307050a1101020919090b0105030103020d111504090504120519050f0702090f040c06141803 73
    0x2400071110f4804400c1d903403480d85503500603a90754580414217030300b00080d410490f403015492417042c03000918a181d0300c9401000c15004080c11400401c5150900071030680c26100806001d810640c0886030b600b9050680c0030140c8115802106047c0303810f0008510140d0000240d402c01c0146200542c003240c44044400c0440c012640041c2d801071803442c2c0310703d581c404048880e00a800035500300c021400d80082800a078401500d000340042e00802c05c2d050910f204401d404041d040b10400946420703461400500ca00008031540c900e4464150400c0003140d4862183c0e601510007801c000d0b0442d80355030005094520f0b1814081c101c1c3e20102d807071380d14680d5a0b0b2580b20302500f960307500c5c9484a840fa50070100802003260301701e9203d0b02c8488040c0406000b032060b038a04e2a20580e580d0382500e071103603003120240c01100900396008420300412005a0f03071407081c24488d510a84513511075160a0400412696690384500240640003030102007441c03030b0408a90044040c00e81410203810321030007080c41c1c0b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 698403794 1250 698402544 698402561
    0x90501030209152a030403022b24060f060903030c050307050d030504020f040504050c011d0a09090302101401031103030717040f0501090b0d0c0504080706080a14091f 73
    0x1a22000510407880300079000c0c0c040e80c58802d1030391501031901c903803005940e40c2c4a11f0102952000300c124400000030886800e00229101c80003031009175030b0040e07541e00c400608c0484540140c032118800341c0b085100500c00c1c0030081c000445800103261030000040c080e2240e80c003001d0200226501d010091000420880b000c2c03581c46000c4a0b074032450000010300030801036404910807034422494141916060007400e0003160000094a1300620101c01940e03004011416040300d48000390342c5880d569a50014100100140034000c02c030a102c9281c0203041c144411080d92019140c0030407018102c05410616056a901c41041030702d0b10000c0002900d103015003c001401c1c49a01c00701060f080404001610840380500c1d68041d01640b154019917039408680070314180040c0900c2600101c8a50340c000d03100001e000c2c18058078190300e9424540c10802280c00103008941900d040c032158010034400c0061444405a10564608008407515240c0c107031100040710104800301804120045603200109 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 698405044 1250 698403794 698403829
    0x100510140a0c0309030b09150a0b2209020409080d0c110c0105160b0a060e090c0603130212060a05011406031513111617070f0f080d02040330090501030209 68
    0x20700e4030f00320070f01c5566101940d0141d011045080027040882480d80150b00900c2030050118a5501c8038030007040d0209000b490002d5550703140e19000d0091b03182d61140302e201d140660340745680c3c0d96030501d07070100b9102001032002c200111005c102d1071078040415200903841c02442c180b9274845046500418042103020060070420003103050000d100c00340d90200040b1284444c032500c4640d140008542c65180541030550000740400020313488c01c10002d80790740e00314801003540b0b0020140d0003140b844c010703040703c050404540d41e100521001c1010508482007a00403980541785181604039039121150b00001540a10f8040100d041c3d030a407240c015108540c0d05a80c403603180c4d84041c0c1a6040c0c0300f00d000d41940e0102080b03500c03550703980b803000880d1203082d080150164412803698805000b1030140d5000c0ea000741c8144040808210503000500c011401340040341c10314030300c0442400340000c0526030f1440c6200e80791100c18400e900300780c03048110390007420016290010b0394042516554503104582 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 698406294 1250 698405044 698405063
    0xc02060d06060224090d050f0408030a0512010e011d100e0721050403140313080712020f0f1f0603050703080301031b05090c160506100510140a0c030903 67
    0x80c11650025001c4511107a130444081c1d095a4643c2043e0b401c0010f40d00108690884112148441d0180d4024410460b44001c1107180c241d03907414160550700b001500c07100241c0009102d80300500a11f441c2405000c0104003410194540382c4000d400403401e010405848220200007642843c043c11050001c0c18034000b103890a00d0600c000402d1040250540000ca079034140b0002d590441501c9168802c80d85501c0d008134841110501c0001a00003c10100802000211400000f80e6150260181a208150001c01c130f916828019042a00d0700706510950b07440b60003075407241c40740010340134240c0091101084080c001e40e500940038112b0382d00b020b0440e00c50044000308000c8540d000314100ea0086800d140d100085001d44000803060303100d5564480480004070310715111700f10003881d41846050751207100e103199540316070030504110f81d00590310f06018010403442c10305030706aa298440c3c0c0d182c8108254003002d0745101c5400b03a00200d074204002d46000b54100b50080500c8005550050f0200 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 698407544 1250 698406294 698406299
    0x120403180b0903070b120402040e1c0302070b0a02180402030603010b0a080a21020304140d1a0406050a0c09030f2301051611030d150906060e2b030c02060d06 69
    0x1e0318194010280c0358042e2040382c10005003160740d407080e41c0c08541a2110124151640d408000262072a030040085e1350292400d40e1207e2600d0f50740d4949034002940f00940c5a903001e04190800410061840d0798803801000001c0742402c50344c40d0660415000c4800588030340741d11010070f0040c071003000d1458102c0140040801d0700e06001500000701803003000d650044248001d80001e520300c44501080160740103100601000c0410310000b4100800505404045545501e43c911048000006032804855030003c1c8810f012040c0213050380701c08104014070600b0b040703d800810000051001138480c02074072070305200b0841c400b030100f40361040f010105240071111000e114001c04058410b001e001c0d950340c3d40c0091890207100038440042d061805181002c8460281c6c401426607000c0c0b0701c60b02c01400c440410211201c0c800c02c806852a036503141244842c040502816072103140c01200b000041c08020103000180086081034107500d4641000000068401719401d40582040c1d00611802c0c111b02 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 698408794 1250 698407544 698407559
    0x41b080f0303060901120309090906020f19030e0111070b090a120207090b031207060c210204052416030c02032b0c050712080904050f010f090b0612040318 68
    0x10b03600800c41194026901d913614200030208a07420b10000700451400c98040008501c550702c0080410701812000d0b24146180c01d960207650300040401460080018115104030b0703152207689100100174008105500c10640c000d441030181420090a20903150001a440d2806010001d07003581e12041500440b00340090180d10740c09070303028000d002441c0c0301e1480d40516000500919030b1019090031464410b0a4807804050410300910009000f0300c460b00f0030780840d002d00c00014043c44140300513115401e007020405130214000072907040c08401564404800c44420450b00c0203a00c0074010611403010386415178035000d40c44c1004e036141c0502c800d82035515080580c0502558125402204185200d070009d442c807030f07141d52010701203a2142c02d09112064101601310b00c40d5000c0c444040c103280364400060152001104e150b444030f10003000400001c11112824030180c203282000340300d15800000840d00d80d02580000c0f00585403410085824580911080c9041c40380103030b0b181150640f508103 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 698410044 1250 698408794 698408797
    0xe1b130f180b09010c0c060b040914061b0304020a05010c020d06050a051b0c0d0f3b0a06050f030601030f18050c041517032203020a05120303041b080f03 67
    0x2000d0b240394030000006104007006218a10b00b030812910380105030020750303c07640020024030036040d030810307074820a200201c1c0c4288103000303070390b580c150041c10b036890010401c8500480020034a49090b5090080c00010f0b03540704a604203451080c60b06c40c1440c00700e800000c545040c0070102608803464101404200d100701d400c6188954404640302000701078441c1201580e120b18819000690400e940b5944503034032950305060200b600c0e241c5802806001a0307089814080103040c0400c600c0a6082214242180c1d03034030200c80303401140d43c00745e80c0d0714299014009204007290b0010b541d038008002030050f03002c2c0d44032002c0180c612030104a055114914401000d4215400752114410000741d0b41003881d160007213416104031000308480e102c0c03800641c1c07005550400115041c90005000750424415025079012081100b68030148400d403a5006000e5003400b140c0103c0c0c0111514940c3e02030340c45001080742e030440c1d8001c0141503102c820480048a030420354120380f149009400018000050010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 698411294 1250 698410044 698410091
    0x309060a180e01030201211e02070614130b090a060615030b22050a0b030f0d180e01050f01110106060504171902060f04032102010e1b130f 61
    0xa4000401c5072603500c0c2c502460401d100090009003480924040700b4141642d800c648404e044001c104407043c1d078603085442109108690a86a0100d241014060207004001c452203001c4440e071064240b00040c54001c8a0b80480030304005485404240b81c3c0608002e50101c42c0d4103e00e0030820340392115516807001d410383c00441c0020b820986415a0f51404402c9023100c0d81c0c500c04000080c8180880100181c40d0003424550030558131401c1240359141481941a01207480c00500000ca002920203010010038840311a66071000304410b0008462052500341035910440d0369000c036441c8100101c803101054040000c4d00c1d420001c0014a054100b005003061350b483c0700c84e0607804e09120071215a2040e43c6901c00c0244800c902c110703802f40c241300e001040c00b008a2a0340c0b5103007c3d00d03030326549421500c440c0c8c040003050403524841c800e254207119008144090b071010b02a8030400d034013022402111031191070f1042c01a5842400b80c00070b1944a5012074003030034418030039082c010001055842426 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 698412544 1250 698411294 698411327
    0x80301090b030705061e040b0d0204030308090606030303040f051c050a0e010311040306050c0705060c12090604050c090a06030c08070f1a03071b1a180a020f0904050309060a 76
    0x810001d00d10329002c00d00d81c054a002500050600001c141d01e00d8005440c0001c03c0200c080c10400031889403003910040a1107283c00601503900c034a50f241c0100002030041955403690400d000b4884681e42c04002c0707a400540162180040b00d00600b4802c0c102698444100180106050007800c0140c210f0050100071020703880701140c040000c0e0056040c1d9100080c1c0c10780c071580402060000403990f80c001d54001c082800060300f0801e190780c500d03152000a640c0e1075400c400100c0c004542d80d0002d140140c0c844007682c051321607420255a859503400954001911850307145000401180e01c80c0d2111000f9904072210f0f02d181980c82107415100c111a010762901420140c9000c075411480440c1340804001c290346c198510381c1e0b03080d0120b03402d0300c075043c0305c103141407500c80300001140f09055004007000c1d4142d280356031400c200d0103040e52a03070b600e002080c890b0400b007151005607541058000b142c5505a901c03801c0e1340e035646405030071889821109c641c04035011803400c0703170503502945556000901 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 698413794 1250 698412544 698412551
    0x180406050601031104030b0414120a050403050c0a0308070b07030e011a0a17030307031808070803102312070f0e16030614060912030a0509030106051806210a08030109 73
    0x1c81d00d04031482107000c0509561f06080118002410000c80013090310340c00c01c140e941d02511a580d42c080756000b50030b1400024004030b001d00a000303060000c0712070407200301e448240c41c41ca103035070b1000c0d68014903d0180c820ba1320030300000c02e02c030700035005080031018040c020000425070041c80804a40c40f1082180208141030303010410281e0342404c0e8015109000065065552301e41c001ca01904203005203004801807003000c174002402c0240a0084a813203805025241e00e050050b901c4205102da12085159121840724501c4401d483c5501c0e8180000f0b440481c40c400071542d4403031401445074003008800041e034100144a0002007041070082c0300e081c0301400034122041c0100d0a4402d0f6002c1e000700140682c0341540c032882d08130010400c01d0301c0541004103215a000e1960b0441d040b803c40714000c1800094038000030700d003c2c03007550040c03c0121500700c000303002948802c0c1c400b5030061032180160402400031004042d41880150300c0d50301c141c1182d082c3c004900d45400d9030b41003807107104e10b20741c02c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 698415044 1250 698413794 698413811
    0x1908060301110910020c0901062001060b04060c0813060c0215041d0403020a0b091605180a05090735010c0c080a09050a030609120203032418040605060103 68
    0x201802102d40c1d5082e9848400e080c42d4400c01041180500340e0071040551042100442990710b40e00303e007a008010503220040090441c2d4254000c60465004c08256a4501142403180c200043e00b81c400b52240d03440c0ca01c0380c0444a241c000c1280c0f01d01c06014942d070000c000000707000707a40004100d40841c0b09886052007014100340800c058087d41c0900c1040301a000140ba042131605000030f81e0140c040c0c411200c10040586400e03002c11825100090190001583c150f8004105580e020003030805803060700c8644106074142894082c003401485e415a210804951a14001c118140c060030248072450040b00808220800c52405585d1000150302103e50b8580e00d01e4040c46089007000b030703e446198403094141c3e144559903105400120038080021400700b0710383c0700d600da04070245205103000511540b4508000030081800205482154007c00070400910101e49081e0701d0000d90700071110381d641880340080c0d41e07002c210000d000600059800c00060141c140c1045000c1c40e02070302c0420000a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 698416294 1250 698415044 698415049
    0x90a210203121306140f0703080601091205030d020706020f0c01020403020109090b0f12010e0f06010e090c21100c0302030a05010803190c32070b03011d0a0b06190806 73
    0x1c030795400340e014100320020401d1300d02420211400c14605202d0601d094511829120300b900002c02c1a00081c00f11410402c1c1c40d40c01c60b080741c0c06402011407111551071aa61407507500d03c81d454440250a030081220804c125861701a280d448620501a680700c91821411034005c1d0854442a0300040c2000f4000034034400f00c2c401e045c007040000d4100100e1710040300501c8490b0301240803000c05036680f40c000340d120b40740c01d100042c070405d0b002000d030a4070351500f0000f072940790001d03010449039004900c42144a030303282d00a0842d094541d03103840c0c140036085064142000308100711040395a00700811000450303030582c01580b00300c3c3d44980400007039803500009070b668010013080d040b1040040045541c4580030740c8004241c1442400c0500b009019800800c0d420000032548503124071110000012510f01803182d0000307000380d0f54441e8255890802a11224614034034070700340706240a408500100043c0d00a02d41d2044094906a03031040003015200e01d00c00104500400541c040740440e0551 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 698417544 1250 698416294 698416297
    0x20411032203141602040c020c1f0c021207090510061b0b0c0c0316052803050304060504060b0325080a320a230307021302090a21020312 60
    0x607070143e85114004072408a6690b00f580048071004a4002c485141801030b40c850081c40384495482c3d001e00162000c4000b402203070540c1c82c0d40036070000702d11454102403d9114030040388486e011103034034040e4034410201504081450b040000614140000c0241d4079445410301c1c0119030f6960341d541403104444601108800c1140c10003000d9014040114035511107140c00340000100300f0064134900918201d0401084281c080101e4994019000d02c90302d4001c0a032a07983d0780ca40080208180003c00d03039004100b8440140014070355070341c50001c18140b00d200c0c2c0c4050701c031030f0003c6c04940901d0940d15611440b1043d11a030b07800c210101203270100d8100340200b1400041a40001a0044102c101c0f00841c02e4140280400d80d048011081c600703c41c0500300315641009000740100e015403990300540b0301101803000c0035908254000c203d0140140c07a44000700025071021100141c031402c4a00c002050f492040d40038041601c0c0300d080c00e00c0040ca02800b00e1901500c01c404551030540c0c0d00345412a103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 698418794 1250 698417544 698417611
    0x60201020a02070611071d061203130e0c07050138010203090d0602121306060b0304050a2a0815130210030c0c0f0f121d010e0d02041103 60
    0x40e00000f100f00f1071180241c20724030302c81982d502034440c402c1e07e920700c00d02d003c054011900304105096040c0b1070706090420951456084290141d0f141505c45182440080e5152060b503182003c4100001c1c24040c0304000d07a41c00b56401402404001e41c4510224041c1c03280c65401c9090a40c3c2c0400d4202d8003c0008a00303100394030603005542440c00c124104041ca01c0301101c01d0310015020400340c00c14440c01c42e04140300d00c002103244400c00041e41400d130708035441d03500034200c881010801e0001140c130000d60700840d203901008805800c80c0004002c1c2800350003000108041800410129a020300492032014030300907540210301e2940c5040c1103411940728840041d4110988240040d40240329420000000106042c46140750005940319840600402800d440c00424000c007001040049120281451110710304070407182e034003c05501d00c3c484100c0f03025040c8036620307898240f0303512008244402160000c108011082c01241450702603442281c454858000c011044804120100b50b403506 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 698420044 1250 698418794 698418797
    0x60518160e01021504060908030f0103053c0c0915010e04090b070c0507120807060e0a03090b090f04020a030903020d05040f17031603030b190506030604050711010f060e01060201020a 80
    0x205642044c00c0c3c280c40c00000390080d244c10ba160001100403a045400842c054009064040601d40c175606009040502c0501341520483e40c0300c030381b082015050a001d413465240ca13508081c28202c54850b052422000030321441d0020855010445115412002550054800c0e20303041040609803003084110380d030500008142418070307004075a03e00e00c6040f0040b039951003a800c58a149483c0c030618034220110301c004488080300080c4441c20010f403400384c509034040d40340003440601700995016000c2c181c64090020b40c54000700b81c1a10039550700b1840f4403403110140c800c40da030303106005008004e485103d90940151082c0399040105c207100c0c008544c11543c01c00134240a0a050070035444807407450207601c1403907210900c8608013011040510101e854806c0d00c0002d0013604060a00c618081483d2840c000428140700420032038603901c0440f03174010402c03100040c850703039500401e17200d80d40e6054a4000a61900340b40d28043e00c134079480070040e0b62108501509a03aa191003c03400d031300c02c0008000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 698421294 1250 698420044 698420053
    0x50a0e040203010b0712020f0a08190315030611041a040906061d0f011e0906180503150c1204061a1c03030c020c04023105010207030f0204060518160e0102 68
    0x103000c61007400c600010010580b05035441a101c080c23581d0b152000000003610300040c0050441c1307240c4108681d0700c0c0d103126a81400d2001d00024200c140f0000b000c2d20010302015100c030000301e0b01c0305d581c004683c05000700300381301c4440e003280325040940303600075002d0100030602d001408900c15014426140c00b60111012041c800c143c010284454040320006603410310010301d031404500c101021200d5480d00072039980500481c80c2540003040c080b0000d20310541d581c1d1418042c0305580700495a80f58180a05a03000d00549681c19600705034800d505000000038804014030081004da80c00c00504003190050348450400c0f00c1d0100560405045482610103503400389840000b40a034100c14143e14890054501d07012014022500766440006020680200c02d2110192450346842c03640300c00040c041c0001c040d600b0400083d40c0c3d464035020282c40030700d440f18110115070321398000f50040c1c44003030041440c6094000e08640810b105a0783d21142d4021680b00c04000d52190120b903690078070580c02070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 698422544 1250 698421294 698421307
    0x230a082a0403030c05010917271c1b15111212100504022101081207031124010503010b18070c050c0a081509030f0a0806120d050a0e040203010b 63
    0x280c84044c08914111103d540307a81c04500401c0312000c0442c0c180c000c001c11300b580da09a801d591200741d152460006013400785002c100846442d6040c0920ba43c00480420320320704150346c20aa900050301d110342c841d900000c03290109503031a001c4d041085d0f90b8034503113500400160102c4442c0e100c41030103404151254091020390020078181c04000d402564100700c0400154071140030400b60380c44102c941000980c8071000c5038a0b015a20080f41c01441c404020f004044074940403105075100d00c00010703003001403903250140d00c0c50092040604d0880564051100003940ca0030403448401c091040c2d900c25481c00d02c1d40c155600b00b1035620a00200c0c01ca03040b00c80c2ea42c030810305640d810034a42082d41d80c0d11803d0f0440189440c0d400005000d4241300004003081c003101c451000d0a0310004006100d02e80060042c0307440060303001d09407401c07265136080c010b03025a111008201e20381c1c0000d99110151085104203c007958121000b840322030115aaa003d01001e143c041c802643300038451406450402c2046 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 698423794 1250 698422544 698422547
    0x80c12040f15090605060f060702030c0409020a0f0e042109171011130b070503030f150402031918050a30020d0806090103020d0201230a082a040303 65
    0x180340e007240c4625501c0c01c040030b404440d20110303500b20302c00310340351641d80e001c1c0aa14581800ca04c5051401100e88038542041c95010075210943d03003000c20b0103140c440c078195045680d419442009480326001d4541d045588110009080030305540036100840c950100e0007035905032280013003414007140c941c407000c140b910075000103c0315542c0700e0f2078140c040c500032844140054040e082c52030003410000c90b107810034031096409450702c0780d1141501c13000811240d000284080266980442c5910170b880d45655507150704066443c601d07400580c000c2c4004100310503410b00c050001c00b40544848200148100c00c450102856941c44010b0700c2640030101900029404d181c1e040503c00a00720f9801ca079055005541000d250b10788102005a001070420707000341580300707040543c030a80403a200a02540341d82c010560300c0e010b416000c0e041010001000340b4894410003e810302c6102200301c250703100000940141804800d5801000c5a0030142c812070104035004040c47c002d41c466890030b0f14080c9103540 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 698425044 1250 698423794 698423813
    0x13051c0909140612030c121e03010608010b2505060a0c020f071a0403080a122703032c010614030a050c19120804030b0a0c0503061315030c0501080c1204 67
    0x701480d05105c03c21015110708403e01000030b03204244640503032654500d0703081d40c5a107140004c85494184060004025040d800510581101c3c8644010755840c22028034800816110014007003188a010202400300701000070218400c2c0043c0c80e08000741d950300e000c1241c5900364454802e200d40c0c00440c0920400ca030180c000390301100040202403800383c3d00d40d102c5100340c011400c2d1300007042d402c4140e040300c518940038100c0750708403002e50201c021005150301100e01c0c070508070140030142c0c0c030001a921480c55028003113070b03003540c0107985a00440b9a8001340c0a00a40c0c001c000601001d0600100d00e41800513041000c0e985c07000180c00306000e200d00740003a510a0211421051018100004034052115030b0310107414002d5070344c25510b5046041103100c1030720107008211902d240130b90720400d440d80301007502d80000c03044504442c1c640362804000f0141c080c0c0c0043c4040312070807200000822000e00b032600d080302d030280c9803480703160f440e01803241c1c0f9806825003080d2945124000900002c0c07c0c00d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 698426294 1250 698425044 698425069
    0x15071509020102030a0e01020715080708090a20010e0405010b0d061e1a0708030106020d0e011706010f0c0203070e070809030a0c02190e0a0608070519050913051c09091406 75
    0x4100d402c0035070382b07180a00581940045030800b0400b500b051200710b681c031508580d840389a074001418050141c1c0d40319100301000b101030301d00101ca825041c18441c0c0c0708145010803030a00400601031540c4440c400341d502d80c851620403101e240746c61400542004400311001010403610910303141e0604c0c020b81d40b40030f1500b2030745400c1680e000700302c08000544901c0240d4043d00340ea5000f420320444001e07010b091022080e410340e040c8100803051480c02e049015007036601c060f0078a0b2041482c500801c0580b00850000d10083d81030240c00001b107551925a82824071400442c5c2d100b8500791601008a80c59200700100c2c2030000e09840c50060250070803282c4500020f0044d006054050341c4c0341c40800c502d0b07100380c90304c2c1e0003152100d82c100111307181000b154004d0b1000f12607040301100c040c9400000c0791100d1003140d008200b41400200800c210341042500680c00038151510444415821140303d0001a20400400e40c1a00c0100c1c81d181c06100d81c081d482c441c00f030000b12607110312080150240400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 698427544 1250 698426294 698426297
    0x1024050d0905031b0f0d0e0d140c060c0a12080103050a0605060f040603030f090902030c0a0c17040303080a060807030f0f05012013090b0d12030b15071509020102030a0e01 75
    0x208400d081130303503084058520703070070603513000d0080003403040621402d000d00c182d00441084030825180e1030b140d550414002c0038542c40b1255080d0301003007030615810300d1b40311441c035a031145000c0740160300c840021415013007443c880c858420402984031401d44880c4402c4c04007800c140d10015100c4005001a4800c0d070300864010041c0c0952a4004002401d0340d0994104500060703055041000c2203800a85030400342060080560561424000c5610f0900501048004205c2c840c061002844074161003050b4035041c4225048d61982c0340e04000d49070300d0b0192030701c04009262500028142c40041180d0b01a254811040d0b00c2e4001039855062080d041c0c0c11055406540c0c800c3c1d4000b41c1c02d500100800c507914000348150b02c0d44a000340703410090b44158410f80540e400d00040516540c1d6410000901e198418080030319100c141101310000c3c80841070700c07034002000703562004c5d900c1900009004028400c410b06c02140502c94610000d036204424028007680c4140003884103280507055141a80506 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 698428794 1250 698427544 698427547
    0xc150901020d060927022b02040603210f05040b1c0903030b0f09060f010c05120a2307020d03050d11030a1409151306020d051024050d090503 62
    0x140040b0103d03811613200501c0c05a4502142c05001108054810100103005510382d5180494000c0b901c2c0d40760303126410b5956040d0055500454940c018210001e41e00035108102c3d6507100c7c038040b01d500ca622240425100c0e807811b00c4580306480341480040220042c0d580508140c54101080c2060708203500300700b1158820030003485112114071818202c02d00076a03001c60361b4500c64040c0041c000d84c0385440c5001d030000c441085400c0c1c075405460200c0e200c0c203280075800c0b40801d0a10300c2c1030030a41900c50341d90420020f000c0402e05d901c868a206104610100b024a141043c98444658032903c0c100035084000ca52091001c607010364003421100c00c030504003107110b036200c1100c1d203240ea20480b601da01d07160756800d41c0002901c0790307110507a0141d0011300410710305881c013183c0060b01100400700e4421140c03c04460040210a4050b118a6145004140b215084c10b05844030040075030700404c4030031440b99407002c030b00754406410030403003d006403107451a00d441007280d200a040300e0307982540c86100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 698430044 1250 698428794 698428807
    0x40605090a1e0e180c0f06120f070212030f06090403051b070306061703071106070b0403080403030e06070c03051605120d0b060403021302030601030617030406140c15090102 76
    0x2d4101004503800a1400286081424480030703145101003d092001d00d44082c4030462060040001c20504103030b41100d1700e242100060b00001c2c0d840c8140b0448242c56001030061042c1d4004075595507001c0d10560702030b107900340081d44a0821314041220b0441c41105020082034003411f000c0422900940a4640585021a138401d800c5000c05a8400300807680c0c040c2104000340001f0344a0300000e01003000c80c01c4c20325801201100d0741e0b4015a0009000c0e415510b0380303007600741e03510021220784661102c10240e41d441c0030308002d840e1946c21039050340400d048c6042140e1081f00807c034140b0074220340c1c980c080b407214179440c01c80e9590003d034880710320300c0f46100443d804107204100544c9204c170550225a51804140d2002003651440901240181028441407006984130b01241e05041c26070803005880b50b82c0c280049004d08400d034005602003801c510240204e5201000a00c01e45a0980350380d2080c05e503464025a051081d010504826000314290010255126400d03c0d00010540005404d000307 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 698431294 1250 698430044 698430059
    0x20405011d06040608060402090a180303020c0d02060709060e0301090602040905061504052d100206060a0e22170c100e0109020f0603090703140105100503030f040605090a 75
    0x200280c11180103910308205034120501e1001a580d4070900596050081a02c1c04c1a840d80c4c039100500000c3c825801003002805c00c60169101040d81000005d03007803020905420060000d43c00a000c00704c150042c46401040d980c00040c0305800381107603641c1c9440c050b2402e030013110300007170343c8443d0b80e81b5540310000080810003c3c0060005030000110009031b6040903030070400702050300040d121a54903780001c000c41d03070360554000c5c4002220416104280542c0852000310f07180042140c0d80b000380b00241c000200d60014143d0721522054400300c0549031981a11030040504179008c081151119000d00400030312404101038140c0b16001c40e12541240901c03412440d041202d41d800d003584102d44100310301403c0e0055081c4180708600030002d480141d00411102c0403000102405040000081039203140700f0050780d001541c0180204101f0080283e1140c041c0200b5a20019040352046010a461601000721102039040416640ca02840e000050380d040c1c2040c00d9481d88205040b2001a442 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 698432544 1250 698431294 698431301
    0x806060f19020d0f080f040807050105040f0201121122050a06020a030201110c0a06090804090f06081b01020d12110313050708030406020705010e13111206011404210204 74
    0x40c00d16121140800341d00c00000345400c0000010f8410002d0720b03210100e003181c001c1483c68000002c03040c040e0840c3d440f03003080300c8036100b9054010201e40ca0082008184000760002810662007640d4120800c1d020034070740c2040d254038840c1020b180e40100004030003454058003c40300c40114190041d141c594500004030607003541d9100c4800340c0c0100c10020101903086c4034403d40300906a80c1e80b418003111003690740e42c503102080d008001036544c0c0c8145c014000c021054400070309600134180150340001d5440b40150030a441640c10901ca5240040309030070705510300d0316030984185d009140602c56100101c500500748075403629299990181c80c001051000021442600c120f408210640607900e41240b5060a680c0580c00f03681040c40b00340802640807134548200c90091811861507000d00d00010540c24100036284440d515121410344000710038006440c1c3c812941e05500c05641d106070040d11904001d0701d21000f010410082800486181800d50420b0b01040107108030607000b940c08a4100d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 698433794 1250 698432544 698432557
    0x31b0405060f03161a1213050a080307030e070b040e04031409060703051b070b04090c0318030e0123030a020d0e06090601210c031106070f030e0109060315060806060f 73
    0x115040c1c42d414417501c44c1109140b1000e503141d90141d4070b825007845444001a00141032005040310150040f001c1c00802c00480101a42082a10b0b07a02d05080c14040c0041c24601c03840209802192030019211300e09a013924200d5a034070004d0101c036034455404849210442c41c903542001e00a2080040d55102c2d000501807441c842d403221070b03682c20040d141c4090104075003030402c09980318110900440c9621400c1c2d40484187d2480403843c002d0009084c2c3c0a812920100c62150040c0700101b024140c0c81800c2000001c4280c9404c0107030301c41c821080c5100c82c10101c22034040701c820030110320010403075402080301d61415103000803e140c80125140c00d041c81924082d0700703503201c0401400001c0c10403d0410120704112a01c44001800303a48990701040f0f18400500b88400b8200610b60644800c41291001a030000640c1e500d000710f407a000d0b1a00101c4045940041e407604001704407a8060301c2809030302d40744005c08425191912104450b01900200040d412210034004c520300720324002c015003078 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 698435044 1250 698433794 698433823
    0x9010327030509010e0d050d03051320180705031303030603050a11030105090f0c090601030e030a0302070b0f0c160804050d11030d3612050c0f031b0405060f03 70
    0xfa40d043c0000010506000c45010f244a0200780103a0320002c1c1d8005065601100c1300d00313010501e503440c0120000c00784d840e0840038022818031454001c0030416481c0c072203ca48012501b111200c0b0b44020f080f5051b4508550320000b00d501000803030003628a8a1000c03206601c0f0b8079020400944980c0e8585c101022408100e03100d107102240009140303400e006080c0c1c0130050038010010050f1620140c2d81e85c07480401207d01403240c2101103213440e4400d40004a0b440c0400b01203c0d03561007002c03070080003944015000e41302013401c2c03c00b0402d0a003203d0f18490040c0002e500171400c0180000c5022202501280b0444a481e0300300710004040d160803035940400e80c0a04c0e00c0f0400404c0d0001031504148050881500b00a1148604030300d200e1041201c0e0001801450030880b60300610036452080040e9412001d141842008039908000c5e0002d00d010051070f007551640050f44000007855514102204008210711005c00d40135543e003040e50140d58045001090f00c000040c00801107400c00268450180 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 698436294 1250 698435044 698435047
    0x20601030b1b1c0b030303070e01031e141006020a0c15031e0204030309090b0d08070c05060f040501020c0a06050301061d040c02010203072c090a021209010e0d030e03090103270305 79
    0x910000316131103584890002a0051071540c517003000c008090500304015581803503a11210300715091510301402d10801e5000300d0801100380b121050000c000c900301c80f00350700d20f500b40902140291004c42d41f000901d40c007510300c80c2c101d82002c4445051540303400e5080c0415580b5500403006916003004010039003092040161387d6401d5083c0100314907113035000f548205040c0845503542d911a1415044d01580101041d5280c4007249030003a04003010b644882d512031404114a00f000b005e00000b002143e40907021241007464000030302000f10030340d01c0351074003080c0240010030101e40508103000c0f215980104881c1c003516a5800142103510480c0500f005079400700c10056507a8001d5403800c41d501200c4441c58101000000b083c8046010541c2e45001e0150000410020580341c2c0545400301200300c00d018251801c0f00341140205140b605401040c4903c110142089000c1c3c40385501440d0140041d510f4654400b005402400084801080c0d01c012020440c0c0344070311005025403142d100e959070310f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 698437544 1250 698436294 698436337
    0x4060f0f03020c0618071a0d1d01151502010e10020a091d04061401180f0207240c0e0303070f02060f0a0201060603050a0b0d0b060f030a03030902120c01020601030b1b 73
    0x601d408010381010807011350244441f00489004015608030300c040c3c0b04085034820080896002008007141c0c205881c1d820140c0840c0107000c1e4410107001d0390700c0c8500c40d41550109600c100d098840b01d21b4a01c685402114414440603142c2c2c00030580c1d0402ca041002c0010303595031011191841d5100881c880c40d280009110822100c1d006d01d00d01c0f8036942d1107218295061a0340e0f000146201c00c042c0852640d82c110040000740d00e0f8064610341074028031148103a00041c000e05683e0704142c509000814a000c40c0d2a400070b0040844a11108001e0011410014140d5884100c1d42421106a070310000911152180380c1484c0000d01505070181c0c00071680c1031a0050190076103a024000d401c0c0b45040c44410b040d41d85400703000c903003129001a51071409842c4c4201144065400e810050707014011160000c042c181c154100da1100c2d0301c00e40b80403c80c0020040c00c261110074080340540103801c900c00400c0480c14400140703400c020100c00c040050051001c2c000d025911040c001d116515108030f01 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 698438794 1250 698437544 698437591
    0x80102120109060501090e0a110a05090111011e020304231606080402090c030709170c03120f0405130e0102040608090f011a06160b2a04060f0f03020c06 67
    0x3090040c8a88070302404140c0c202030010304504058000c000800d2100e1000030151102e42d0888014016403420340b550703510b507001004140da842100514049048040d421240c40414030481c0140e0421200780800389100400282c0030754400740058031102020603140060720308061301c0a02103c0307100c00402e0070b40715060248840315445da1258061000c1c03030080201584445441e035500145d1121040c1e540d41d03845c0c0c000e84609269421005d881c0e010304044001241000507581401001281200c40c1500f45407042c012500c9214190703501544240810062400c040a10f1000c1c100c41700c4d40030920919441c280d508a804c16800480000e02e00000e10022480a000107030500030303060028440d00714400e034a543c4000030440524000d980020f544030040c405420410030090f840200c0c1355071403d1240f40904129041c1501c001094000041d014a0f03203011021038003282c1507a101e100c29000702c51410307681c120700c2c9001e45080c95000c001c1d040c40c20100740041d03445120b00d406110107618101e8407 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 698440044 1250 698438794 698438827
    0x1c2708030a2d0206060628050c1501080d030b010521060906010c0201080f090a050604080d15030c060c02040204090906050f070203042108040812040501030b09040305071416080102 79
    0x11004020404071001440c80e40c0400d401754082025600c403070399408111803147c00301c05904990300003814030b03890681c4500d510100418900c0038a404032500e50000075610a0100801e2240700d03455401001c641003d18001e4018030350020781410850f0803d1010603803085e000001c00d94000802e901c69003007203514504100c0e9160000d40a07c0d000c03403c10340d00ea0000e8801d0901510003140c0914600001d5505101000948a4030790701c0001d81c0c8140c103252605031242c1d0081c00484007800d0602002d14880000081d201e8112074001c030424800c41e2903d10103a0351407100c107509a0700150200004540989180141c4035150721401001a4510307040c000c4d201c286201030008000c6400c100010004a10b0f80400c40d445401101810850799100d440d2840452196611214040c09000e01c900e4044032448041c0040f240203072002e1200d83c20b5002040360300710701214024081001070003010b011500001c5c0042d0f04c05c48990440e00e5030302140700d4180c40c0020583c088141a03400251726040000c2044 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 698441294 1250 698440044 698440097
    0x240609031a0613050406110c0a0506060603040201050d0e01060329070e1311090a15020f01230601020f0303150109050a03020901060c03020c0d080c1c2708030a 70
    0x9103100041c1440b000048841141c00c0c2d02911203900c99020a0600c14182d000e13400040b42114080c1c4e6500445001903200c00c0c040c0c0050b90745000c1c03180040c0460600900b124803035641659030130300d0007240c0781424000381032025000f03d1666031351001000055480020002050901407008810fa44503100d074188444020620420400812a50901621003c40300421000b00e42d802141d90400000c00c410749000c0c101000380c0c4491199000543c005d0198a4260108501e6090311282c40f40c81c003c02c0e0a80b85160b5080060750345100d03208511b00d805450454202405105440710304500060091650704140c07030800c100020181203c407a076030026001d100906041da00250020724607000036807220b605128007070610821200001c1098400e100b60260f16030000c000144210207410041c0b0242c119100d8001148100341447c41075a4560300300ea206e06085681d00c00d81401c280043e40c2c2000c415030000b840402c182d000c045038444050002d4042004079542c6d01740e800074408000d000245026 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 698442544 1250 698441294 698441333
    0x14150a0c020708070b30040507080d020d0e0d0b01030305340f031e020309042415110106150201180804030308060a03051504060c02120d24060903 64
    0x5441c10040f2407800304240c0100c41d2000840d90301d0391445103a55660f4203070408249000d00c000300c00850401c0c140c10079180203034040d400b100c1c1a943c4a8400d11b503111100320510016920036a0240141803090400300c41400b0040d103055210103096880300c500c40000e0308103c0100d0f10115420123411009408207042c481e0260200d8203900c0111000343d0300d448055400f62040c00c2040c0c011080c10300440f03101e1f00e000d20300751030b8140c0034804000003910781d044040d0152042e82428440d8855481c0281203112082d01c00d00150506854859000e6405138033604a40a2001c0d9142e034a000c100d0078480d0b50028428040b01785901443d401c402400c6604201c035500e8000c00580400c804280c04ca01550150b903031504110340140c0303801d400101411240d5000801c01c1c0303c0d08000210040354581003600440c0308910a0148440c03a8030140d846590b0100e903580050301c18004842d03004c070240c021103154215100070914000350303101c400c020149030741c114a0104440f0b02c020810410304000b204220b2014 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 698443794 1250 698442544 698442553
    0x10b0405150904110d08131a1c050402121902090703021c020c010f020c0c0a05060a0c0b15040c09060810050a051212040f09050115020d0c14150a0c02 66
    0x11800010b00c4500301030406003109280024548850700c401010900054000358115214960144590701c50030543c0036016144405800715040783e030840054458401c00040640000c0d81000700c110000c110040c030583c1d00103944004900c0b071030000e20111028112046400881c0c035079600501030b030300d000a405407007010f20400604820303601021311650340140d00403015030f40c0c18401d5100c0e4003400c00d001d44195410f20000c0c03420701c42030380012442080745045d10310a6503665100c0c00c10150303028007207000004c80e2400001400003131100c104158005018208425000c29040c00304040320110820384c0c001c1803140b0810f10025400540762548605d80e806044003617030074800418003421143c80b0301c80c0104a40100c1c082d00e808244503104a00b251000c410352119a920403c141580403440350803406c51504001048210704415007108801160b0024501d944955000f00c4090421071025a13509454500c3c0031080c001c10b00400420202c941800c80b66400e200085008456812032003200b913520 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 698445044 1250 698443794 698443831
    0x1060506030c0301030f1a1015230d110c060603100207030212070302010920150c120f1e0d06080c030607140f030a0608012f0a0c02040c02010b0405 65
    0x2030b0700304aa0560303501c140e03158200440e520b0540c94076019010a030040700010002c21200c0707203189583d1800c41d40100c5900900c541c50340e074203466100d2110303646080b0100c0c8600200342204401c0c01044402108038002450403e011700c04c98040d0030100c0405100d81010091180d145420440000f244054800031841c11125a401a42d18102c0c08081c880c01e240c00714040701418000c0d03122007030980d0040100b01030110b00004408804000d10740c15885040e003c130107000c0c0e488040055541d1641154024109d1114031900c01d40703103800180c80410416003c000c610320414400e902c01c2d52021844c412291154400c1e520041a15901c0c1c00007890340e402074041c2030442e45c0010b070164020009050580700b990b0440707a2001e15120b40100c84031410000030502c000342c8926030003103049504510007001060303901c000c4003c484540c0041c0c100c0c20952124451021211540105000b020608180b181da4106602007001c1c0c1c0d10f81d12680015035515070107201e05003401e0041d075602c02e21527502c0420081 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 698446294 1250 698445044 698445061
    0x105090615071221091b060215060f060d0501090b04020c0a020f04291206060d06020a02011e0905070609080a0b060f121f020307140a12050a09050106050603 69
    0x10524040d012444800c3c41c60202400b409031810181e2104003840010000c10300c0400291010a000f01e40c503001c0b80480280c44a440c5091005541090723004c0d1208210122403280d488001400b56030f8031444036400c0c10010303503400e402000d540c00601c0010510f5803402c49444102c91101039100d004e07c0c01001888109000425440d24840e03044420f02c94440b119400f0800804003500761030f010310401c20301c9403441c00d400100c4c068000400c56580042d04c124042042c1c8801040d84c89607001504000300310005850343d0040d00b0400164800050580e080030341d000c0607000540c20030340040e9602d041d408180103041c441e00000e8442c03400d2600c490303858600e074141d8915882202130003e01038007000c00c40700c1c0d9880000401011004201060006140c0200c2c0e0b101c8031401d80c00011400040169003c044580c003d8034841c1d0110788078103100c1080300e40d51440a03070100a009082010724600d98a04000e144601030050400c2140015241c0d49890003d0071a205904814442d1409204018892 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 698447544 1250 698446294 698446297
    0x50615030705090a02030a0b09010b0c0c0319080307031e0b030c030a0b0703110705030d1b0f09090903020115031511090d061d061306110306090c03090c0a0b030105090615 75
    0x4018032130041c0d0300e5441090000c028120222820f40c03040904000040c500c803c88007801c85044034200780c449010110003099a00d215801c50a40440c820303a03400000f14440c81c0203180c0c0b0290f00d08002c2410502c0c0c03400700c01340e4443c0466210b8182c0d0303160100000e17070904005400e80c1d403030103070f00824003070b0300390b071911102140010030800406440d00400f85132440a20261620241d1040841e0388404082c010a40030700b110109280250400c0c807283c10043d80f05180c0d5103252040c0d516030078812410410000b0141911030300a9003550b40780d9000300c140d5950003c441000354020710b0805000e20401d0a014243c502c10103142014540c14410f4071f80c280e941e2181200301642c840340004181404c0424001b14440c46070b0100030380d0003104100070b000d054100c0600002c52042e4402c0000f400800715942076800240d69181d00314081000144a400302c0780005d5030409516412148403600700c20002d180e0b0b410940140300448004001000366041c41c3c501d160b0441c0c805c4484086061000d800620b56 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 698448794 1250 698447544 698447551
    0x103240903200c030a0809010806060a21090b04030f020708161e0b030408070b010b0315010c02012a11060702030a060f090204060806070f031b0e03030f030405061503070509 76
    0x40c041c104006009010b42002401c6072040050705684902e12a4108940c0325084200070502081c2c05c0c200044040c80c00104640c624001c5072543c500001d29220200c40c4180c10b19030b01c0c440150b44071881400f10342d0f040342061140c0d2080e90754078001344030218004e042010310360040520340d00c003d004101032444000500c3c181c4101c003c034034850002c000781000007940c4951101c1c4100740004107001c00e02096400600c150741c000c0e0b15410316640e13122110080e034801201c00c510307007049061031042c0300d602c078208070b032056801450b090000845011061100e03c1c134420000410821a18030041005800108a8444e120072103d107030500f071a50300440c0e1181c030001002803500d50386034540b07002c60701c20358009a803c2d90050410081561582c12150344c4004c01d41c0c9850108541c2d03181000e09511a000d80465079141459106c103040400100360340140311440700d03603418081804101011403855001d503200c0c4c0d00610051070241407140f00e030212a03840028690003030300080300a10040d128841800d80 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 698450044 1250 698448794 698448827
    0x90c030c07240f0510170a06020408101b0e09060d02030f10050f01081252020f190b070605270303180c04090c050429060906120103240903 61
    0x1041d140315040302e407e1440c0c100d8010702d014408203000c25150700000796450180b04066040000410400d84c1841d80700280142c1e0001450030008019035003046690070350019006004e059030441070341d0009080c4040c2a41542c515800489030480d80340e241e004464000d5085094072000c0d50401c0c8070b242e10740390070341510303011600001100d18403c4c2c41c00d8104500040742e80428400d10841d840312590480300041e1a52400262002809404000d580e01150540e4001c2c8080c00c0414ae0005000000c880c0058501d8107191000c4005002da0fa103100a08003581715000001d250f1500d80c4000c021395900e207002c0c00b5580c10b039480d0a000c2d1000003080b40d400c62442003020508003c462091482d001d00c100403e900181440214800c000c2103c00203030988200320740270f200c3c003055142a5a4030703d03060110380c5629000d403811080181419001043c5418003d00700d00d1a110411a034910030240c280d00881d10710700d0002c154800301d0510381245c021009030f02c105001125280d01c00504d8500c030749481d5035 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 698451294 1250 698450044 698450069
    0x303050403110a08090a0b031927082d030403030902040b03030c1b0102010c12110405060412150504111021050f15090c030c07240f0510 60
    0x302458000c20700010010300701c00031151959483d2404196582006119901403059400040f88120b145001e0300d00c641e080c02d000b80c02c50891000d04030064a968801c501440305060801001e4511440913240406d0042103000d40d5004c007e402c0002c20600c0088030082480040d284c040c1e03c540b54011a030b00250546400308060925000017170051403002007169040c40b0002e44519409404200c034076a031a0101c8071aa0782e58080d00040e0b003a07461501c0312900180e50380f070081c000c0945551000c80b00ba00e641038101e0415440700003080b02c1d80c1c03054200e400c2c007100c030340345003030401542d4646503004541010b010b0100b8141951001c0000e50b81e131142c07504c0390501c2d4240444840c407031002c0c40c644144424014000721000c0510364018402603a40c2000c907085a000956400c040c07204403031008134064080301055a80c0550140103403c082d001c40c4041c074041044030085058051043c2d80c090f401e010300170701d4801c0004010112441c40300041a581d041c882000190b40d01d00c0001c004071005404480b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 698452544 1250 698451294 698451301
    0x302090c0d060906060e010f0905211513050609070b04050f0117100302030f0d090b0f0c150601080a0504051903020a0203070807170a080417010e0f01022d07030305 72
    0x81d00900450341081582902e00711000448907804079607040039031b400781c80719134840c02c180314110f607a441a8011290003021012404101d40400c8420600c0030190106854140707032055242803140d02c00384c65182060f403141014405000c4240940d90301302d049203004200407480c002000d0b845010b00e20509100c0c00301143c0c01d80c80c5901810504030004941c078071540f20341ca809215030329025200d008c1030740079108141140307400640004040110b0105500e8040c00e8a20f0824854002e40c4a40c403041c1e00014180f0501c80d8480c410008901075042c0c0341d03201c1d2030a2414800040c2560320041040b0013450a002c00c0c0008200e012480c501021f82c0500700d65096800d6040680c0b90585030100250588505000052018004140f100585014000b500140d564505100f651440d00c1480540304500c00c110400c80d0b01000140100c0107401700d0000710390720841e4150682040c411100c4550142d40000d1400e10341059034441e814004103041c148800ca24161203810610b004d2164014180f581d1000071 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 698453794 1250 698452544 698452567
    0x70e010f030f18140c0f0d0210111006030311061306050c1c0501030501140c09040510030b10050102160b030103080a03060314030408060a18020d0c09020a02061b040302090c 76
    0x40c10300c3c0d81944461a40102d4a25181111007241d0084070028002c0300c40c407000c24a00b03220740401c1c13003100421280000e10240c0800051010895680c414403000d1069615003240c2804101c1c6c04490010700055503510318103000e441c001c4aa50501102c1d0003040411065800e604444080d00e42c01541c001420f580f03220114000b40b0a00182d01100d04003406d00034440c40300d5800517816244500f000f403019141c2d084041c0c1c040c0344280d03089941104140300001c110705050b4491980458848030440046a07661104000c14038156150300d032100c00c400d800e0042e541c040014508007030303608205136001071174a01d03506428041030000a000c5000001c8080c1c005110781c10805c055904070700b908560b40d881b1110701d5501d030700c2403041d04014021200041c0000c030091041c0c04102c084e07428450b1110034540e00700820018071150480f40e580100c4404143d050f203510107401614443c2c1c0050546003401d007090f88500c40107910141540c4c03000c100610050f15600e060941100d003c8500c03a0f10341842d00c05 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 698455044 1250 698453794 698453801
    0xb01051614030f130f03020a09050403050f0c030703080601050c070306020f040b1314010534150b010e0904053012060103050604050420180f060306070e010f030f 71
    0x1c1c400e0715110128031500a2420b1a0081200134800007904840ca6070b10a11015100caa41c4806940300001140400000045070041e42d030007880707868012f2030003020701010501d58002100c0c0d101203a02c04140d060415030403400c80d9410040900f000c604028143c0d0045990301e0f0030340002800a500030948400500b40801038801034810300640d01d40307581c5c0c42c0c3d0444041050307900c107141e007950700e070481801c01d940110225440c00107284050816181c10145464081c0d4140890003120796282840c000881e51981a010040403002c01c042501c2165100050103044080b41152203007018109020004200165140541402802c0b10343c10560b803c4c00d01d1641d200d00c0c2403500085000180880c0602d81c120300240c402c120176201040700d501c0790410301c0b045808c1213400621410303a030300c2801900302e40b61482d05007091004000c2c40801c07540381007481810300c0540d02c1403c1e03c074880d03003400b013a8901030044981c8500d4926200711820110030002f005001d052000302305050356000525100c0c5920341 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 698456294 1250 698455044 698455073
    0x30c1a090327090924070507121b12030c2d12091113090c03060203180307060b1c03020606210d080412020c0f0405060a0503101406040b010516 63
    0x80c00f0082c07a00c1c0001100c0d49a142100e0b260b000d842080c404d0b203d124140c4034555002c0ea80580e42c0c02d0402d00c1ea540c030b81412512001015041c045481e01100c0f62004039030200078014464904040e81080714000076080c0c2d80e800540784d05104000d01d40101c1614a00c49607003d0ba2003004076110724246024040c1c1e0320b078540c002c42040079810408080c0620440103140000000c09403428040c015112070110112000060001c102c20301c0000d0410201c0c4183d00a0342d040006146070510501c20308111503d140c2c04004112140703a10b540502010b45441c0641e03c60016440e040b810385900241e800a49424005003418400c6000300204459030a00f5009080500c0c0840120380409440c1000902141e03001c803000c8880e000c14220304150f0700e1000c10200c01c0181c0141076a25001140304c100700c09440028070003034104000080010f00e590701007042450301580d15000161845c0d64842d43c480c18000201801c2c040c5040200d8078416076805401c9401080c8072206a1048052a1070200080c64001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 698457544 1250 698456294 698456299
    0x9020402040e250f0c060c03152903010b0a0f0c02040911030705150a08180109031d0301020708251b08013c0f0603030c1a090327 57
    0x3401080b10f21035000107030281108412051088105000c01c04035000801034641c140080d039188400c90000700a900100704048030ba0501203841d05038442c3d048005281c03a40202d03416402903c904ca182c0400710fa0044081c0008840c0c2d602d99030411090760030500c612401403003000101c0748015030480c45404bd0403003680c0d005005100041650031b04c10154008a44824840c0c0a09a0009600d01d4605986215003501124450420305c0ca1001500c0e0840010320031402c40e8188100b10038801c0c42885001c900d2031080c0c5a85e8400b4010008262000c1f5035081014000c0c0e02c10005100400d04120070789096005c034902d00c03e0300401030032800048040181008040c8168080c100c00c0c0c0c000c40750054000c2d210301800030407082c011401a014a210b03104401d01da00c1c0b03d03a035203159104c24001c403507149010300c04401052090a80900b0b100302e40d500c1d4001d4000850f901042401c00c00da00c0c030407441950040c04000500e08003504841d499100f1070200182c5401340c030481ca42c044074018051998031400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 698458794 1250 698457544 698457569
    0x10b0307200c13020316080603070501030905120a020322080312060409060c080114010e09060d080f0c010207020a05030105070f110a02030f100c020a0503040303051c020307030c02120403150902040204 88
    0xd4241e50f001941095407064074170110b4114a2130054802c041140c402c1500030001d10040e4607140041d0002d00c80031a09590a026060b0480044a07040c0001c2010004540c0115591000700c40c86019400380220008400c0285600801c610742c0000141e0b480101c940d075281c0c030140c0f260400600100750496000300a10b061000307496041d5000030b10340341229200340b0741e0050742c07407502c00440c1c801d81d01a406039840304410002c5442c60030141a2500068400c40005151200420f03803440c0d10340052100d27072541e030340000c2c0e00421828a403e0030310040000303400074003d03818108000713091100d2007050202008284074480481e0581001303107800c4d140d00542a14081a02c0004460712001c1502c4001c2c0001c0c103005030303040074070f100169a008007504600035604003800e40c0e0701100c01c1d41c00418045100b001c9c0c02e501c0a2003450078030080d8000c0d18580c0f80001c81e804000300283c28075245c1c506920300c110040c4020000b00d106511243c04002e00800c0c00110041c440c80020001c2c01590420001c40740c1c2d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 698460044 1250 698458794 698458819
    0x1106041509051014120601030b030f0106081005040305091e19170c03060f1f17060109020307091a070b040c1805220f05061905010b0307200c 62
    0x1001441c0c0300944034191400d180b0900ea03403405944040c480103040c03403116030400c006039142120700da6840d041201490007040f060030490001c0d01d040c1e240c1304440c2c0c0031b9544d840d0401001e1400c100c181c2e283d000c0031005000c2460180c4000d0070034041c984c3c8840c02400c60441d10720985000d10148841795100070300c02c2902901c03080020703844038031501030041c00d650640d003040d44250000a425241c00c0c0300400518056440428081c0640070103414180300c6003031003107200b00700c1d0758200404000d81601c02007443d00101282040d850203034103900c507400961040083c40318542d400740d405415510710480311088410b0b68000072906218200c3d010344070740b072101e0920040001210700304046a004500700011490b20b004010708641c1d01341c403010029485041581000b010a01007241c2d03082c06019280c00200050311890700b000d00c00c84010700007001403400b9140d9014684070b05070150210889031802c610f817556001e4252500b030400b02c08280da00c0301051030700c4d00b400c1110043c0094041d081140190 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 698461294 1250 698460044 698460047
    0x90f060909110c0a0825030309050c09091e0a050607090519050609040504060f06080c010314041101050705030409060b04030311010c0c11030a0b090303010303030b0d0c0311060415 79
    0x90a0380038200045003020182c4030400080002d07107030203a111202800414440b907861200951161800c941e0701080d04030a40e40600000514011090003038501080b040400e00e0101d0070070100903601445951280107010b103030078002868100308420080e0000c074502d0702d628043d00c0c10740c4140c0001c5c580c0c400c0c402000300c010340c808080c0084034019a42c003c01002c1c0007013200f49480a501030303030740c000005010b540840e24142d003206401c180560000034580b80c100c100c0c80d0a039812504581d40030751010030055180c0d42d00d031003580852040c0b030329a200c00c1e05040e598a90904c001b05001c40c1040317400b0800c001402800c3c41250001d00e00c10310204415aa43d5a41c020146c01521080d1302240199903100c40300751040c041c12130303160825628991090380740c0ea00c589081c80305881e00d0380c02d88910089140020300303140c00c4038003072716118000b90b072258918034004090356000b00703c42d8040c00c0800d6911000400204030324060365803001d600c6452420ad003012594034011944011100641007641c110b689 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 698462544 1250 698461294 698461307
    0x60503090c06130815012403020403020402180123030604020703050921070b0c2d0312010503070807030510022b0c020c06090109090905010222090509060613090201090f06 75
    0x81c4c03419415142c0e036800424584080c50000d114403101c07107002c83c000c02960044a0b2000a003410581001420704e500c07500803804076040700301c2d00c490036010a00003051960b08a8610602502445614070002c051608040454040a00080c1c007598003c102102018004d1051f01c06050019000030740c603401c4503071014884400700f0341165580c000c8205c0030400c110b4900403159803508001c000c102d6041c818800d0540c01036081e407029031703480030440c00301e2108600740000c04103c002c1e00da081e040b5506207000c00d410a15150b12146036036000c2c001c1040060408a06000140c842038001078a4900345070060409841481c3d10a50395611a4108003d0b500c035544198080103443e401c0f900a0000d4500303025046c07241102281c0031905044003005000040d42001c02d8242c400c030300250501e507890b00f140c290710400024620603c2d00c1c20209004203040c0f846071304d501c00d44000003440350741059000f05510032900f4408020440c0c94120032030641e40600d101c4002009590f088900f26640c03242c00a281 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 698463794 1250 698462544 698462549
    0xc0207051c020d120f0e0d1401140108070302010e030705030c220c050c0105060a06081b09042a030902090103290a02090109060512160c120c03030f050f01060503090c0613 75
    0x124039039000c6640024410719044280c0031001d800e0070300c410008d403641128011640007120466407190b46800d14208a40d41e842d000f0a41d100c010704580d81503100140c60000d441890a01a0340807038000c00150f68009a8181c2003041600c0242c401c5445030340001440101d080c400403e9800d02c40046116a40480107001012410300200441e44441c010060015128444e880000e00380700b008c9000004103540d10b038421900c2404851070000070a004c0740c1a03801d80b04420038080c850300340405079240000c107810074060407450104a0400e0582c0040d92582c018040a00100303c040b1414816110081102c119042c1c003211b0404545480d0913004040d52050040c140001c2505a0005005010342d0030707216200d1401841c505290342c1c4200251045001121210070848211142408a40c3c4106450300c0b80fa0385544856090000303050260564200074440000180b40408106810310507010359815903245260581e41e98441444081c9002c1a20741803070f503c410005240120510107403102c004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 698465044 1250 698463794 698463797
    0x150b03041101031b020a061d061009240b0f040909060f1508101a090a060806010b0f0703111213090609090803131b06020606130c0207051c020d12 64
    0x6500c20603013200000740344101d1a40c0c00b40c2d101b0302141d030004009810102205615080c041c402c141c200c50454501030702074600e06029a00b554081c41841e481c0e0107181c8c1a100c070300b00d03c0034201031111100440c10301d151140201c40840410201d40b01042c500450307000b0030a0045c140948079041c20004000e04c0344007501c920031441e1240954003080031542e080c007110014070203000d40e4040f0174080c001810000b26076520002441c0c050040956034845031600030242d202000600d035003003419040c03910781c040e0045446e03200148007581c800d5010804407000a9410b103040d105033ba6000c1c05080c50000202c48000b203060020503070060741d2084900032401c4404120307040c000240c0d1003200c0804c5801400e4094041c0703100f08002503d01004400520b589840344101d5140e0f00d102400340115900c107038015030010f80024048c04680e00e40f000003070486a0701c283c030801208144200281d0fa40000c1d00c503090250340f424001c1950a00d41d81c40f2466141d80103480400c1d03903d0185016000303070400841210 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 698466294 1250 698465044 698465051
    0x6031f020d0e2514060708040504050c220e04080a12020f0726041e03120915020c060a030e1002070b0906010e0f0411031009051e011b03150b0304110103 67
    0x90481d2450704103c000c88a80c91181c0d41514010790138400503900c00b020664030306038201700008454070383d8401c1030301c00c0311640e80d0561611080762000408042c092000c0001640b121030520400c000c0d007541c50707080780c1d01084440d41ca8450007410350702c81e911301d02c8501809101140b00b903e441018001851090b22564640c0002030300c03c4440b84813a01403032800309414906010502c0121a143c000903280103031041c20312012030b581c1d80d50309807001c1008101d1300040c0b6107400c00c0044a110104803106035202e03002410f065900600819007078000c00f5242810551543c1c54140440d80903c5002e0800380800010340d5541c12030305041181040580d0407440510641000123410660800030501030410f81c19101786584031500d03940351450000958903454081c0300c00d5100f0014044c403c40c01d034107125030090040c06525691042031004801c0007915503034100810000c0001e04041c1c450040c0d441030900140911401c11400030481d902d410000c1304440c0001800140141d0301d074411160b0700c09903000e1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 698467544 1250 698466294 698466343
    0x120b06040507260109150e01090b030709090602280e0f120601080307050d021b010507020414150a0501030b0307031403070804030503090a060509010f0c031e110c030606031f020d0e 79
    0x608206c405d0384a0101c10308500030052026411317a400012400900504594086441c0c01d456400c40f60400812664294001207000001c44160500e960401107180710683d082c40700030010f0900f490b001035061041800b0804000251740c0d0114141c00c001640040310681c2da121300c502d0341d07294080341003078890744034103072030703510060f1001901101e0701100444004040e40e04000540b030f40c2d0060882280c1c00ba89075850100b41540d0030340c0861140f003924506426030f03004e034014032602c4402d42d0000c50416081a0800c20709841c00100d040031203a2001e0704007007182e10f403c5180d041d0f01842c000240003031b100103000014407038000042c19010350b040741c01d80d41c1c19035202c20a460500c240281c0714040382800c0e00a80c01c45000b00142c0c80d5060003410705142c44e0b80340310708102415148224800c080703692407a8505a80d1802c10405241100035001070409040884c0041e50b0f550042401101c2000320b400300c4890201c554040d41e0300824400760521080014a40e41e41e100c0a12450101051940c1d0810 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 698468794 1250 698467544 698467571
    0x302100b030115150219050d08070206060d0f2904060507020c150309162d030209060d080c010504062a0503060d0f0203030d0c0801120b06040507260109 67
    0x4109250f00303045950610240b40c0f025a812900496600f0030079405030f103030b4860b0204a542c419201c0548504080d042407101400082e001c0e0101810000856100d41e04000307168039000040b640141d001184c0d020300d10554a00a4030321400c02105081d406941c5140800003141c980d491401540f142c10709010580d1450303812a43c1d000c408c3c04141c6c0c40f4580d19130544083c16140011500801d1242c15a11141809060f0115450160b44485902c5049840710b101011200134040303e13070068031010002e440e1464000070700110020f03200c80e200c1d11010030f0020801170b014048a40c4900004000e11241c501070038407100a280e600340c1034a01104100349034030070440c0c5807080c00407174040707485480c1192206024806120303d980e10450b1300b1812031030881d001d650304201030005c0c1d944111b00030070b20072501c5a000b402d00406038444160580401500000110a44211030748600191800101e0b17030b458000440d080d0a520101c080d00060003606809414416100c441c1650300c002c0080c000d06081c0400b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 698470044 1250 698468794 698468801
    0x6090519050714032518080304140103020c070e011d22110d061506141303030c0201123b1c020106030812040614011401030e0f0304030302100b0301 65
    0x142e40340012000e034020741c40304000c84051038005400c040f1480c085c0880d002480010081c0d13085060105030783c1e0010050010300c50580501500b0b021004d541020300d81102c404940341c2c42c0d100706051540218510b4000c4a0400410b401495418404426540d481c0810510124040704401c03241500380c00084145c081800301002428510740120025640b80e29455400c40000d090294000d10114404003c02c6c60b034094480c92250245c1640e48007407030304101901c3c6d2900841420284c40b400d11440385400010142c00701161342601300032082c102580f0040396500300100d01c440b502ea1030700000501b2014481041822452038400005080b0320203030031101d00b402c0e65054034000703502c42082c07030200f2000d03c0c1d80d1000c0310406000200d000c545030750354010107402c2901c0c240000c5101030100028002c2c1402400d1181c40e403600303090340c154146400ea85d01c000800d5402c505054590007200348403c070030043d4031709480110050781d440e0b075103d10f002915010030425000c103c07402e010000c0118035040c032 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 698471294 1250 698470044 698470051
    0x20f01090b12060f04150e0907030807030e061b0109050111090a062003040303021b150405060705160902040f05090603030316121d060702011b0e0d060609051905 71
    0x103141c02d00c2e41d400440c10a07035600501e1190840c4000e03100c041c00d0380300c50048401103041105d010903242e05000c11083c020710001e229020f03550200d0710810100303c410045803a401d030185054000e41c0750800c04288540b06003c002e44250420318000182e201c0706502070880648190024426449100c00c0390b003090042411080c0d011605610400c44680650221401a8031080840c07401c809031020440c02d5030060303030040d40541c01401c15203000519426210740f041e00704980307d403075200d54000c0b42c003d0fa0103070b40a50703400b44000280e2001884009c100302c45500580f140c6000c0902e0b01c41c0717044400380d0011320489035040060800850586417040b4030340d01c12440680114295a07030080c62011b2150010344400c103024104c181c940303070a24103000341c01d510030301071740300c0b1814192501c640380c90158010000b0046900d03100c6500c0a00245e524007002500d5280340101c600d8803000006081c0103810440181040d20340000020324a070180c211500c29000303072240b9a8481784400300482a2007088 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 698472544 1250 698471294 698471309
    0x2a081f0c08090d050d0f020d0c020708060f010608091501030c29181201020d0c0e03010c02071802040b22171504060b061209010501050d033603030c020f0109 69
    0x82c5001e05000748958090117044040040c045404200071210384102e9110002c07450340c0944400288160503010005000240a07840c018038080ca0200c0700380d81d0310320f01030240c142004100004110030312420800e1640f4000840c9640d035440d44d42e440c0c40224085c441c46200008415114003402c40c0140d11158440824106a07980c68110000f40045503074040210183e400040c840c04c424803041c003440902001282c0e0302d4001052185190040d003079603070706040241300340c2c1002c03410010598081500340490350b400c4622000c02c502541110080c0c012500b05004004000c00d8542800ca8a0b1003201141d014004400548586030a060b8401c03a08021640b0b002e64071041c2c000c2050042c0054565205e40144000aa0071040d03400160007641b00013014110308040c0b2050111004080c0304440c014001100c281691118a039009001c0b20b04d2210000b002019030003000d900c0045d10a01d01c0b090984103205401c925840e0f14020700101001201a40940800007990a5650003061040280c5040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 698473794 1250 698472544 698472553
    0x90d14070809011b050a020103050f06060702040506061c27120503090304030b01030b06120613020402160218040b0115052a011d0c06072a081f0c0809 66
    0x503500d41c001d86a1201802c0360400140d00001200010102c1428110611a801604070f043c0079000040680d00060800081444050140019591060104e400050707042c0c501051550321040055494080c401650540d808004440c9075151a80d5000340d002400c666040450109650b4006484285c0124002c00a20000c000170008901403800b035684120108100c9284c1922940d464200b14400c1c0c0c070840d02d0844000c12300900d850114030031000098200014070b00e074076141d121402c48044081d4080c1c000d0b80e0005500a11360440c0c0030f100340060700078240e54100d2a0850401001c04c2c0111410340303c1007010340011420200b400f00030310311401d407540c800781000448456007841c03042100e61740d045800084090344001e9000c1c00390224168042d41148980da140f0000c4505000a00d21613902c02c007003c02410001603c442e90f4000c840c400028501c09806a008940c25036101e55000303a0f050381314101c55060064482c04460720a0742c3d8030f0b2000c0c003003100c4441003561500011748601884c1d400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 698475044 1250 698473794 698473807
    0xb07030801030b13210206070c030813031704051f0b03280c0e0a0c0504150e030708030c013204060e07180b041410140f090708090d14 59
    0x6a0240c4a80194406240c4c802034202980d513004003220000030308807a00d0800c0003244500d0340510189a104c002402e201c0410381c0d10355001400300b00000c1000070320340000342a60040c580b1581d0103c1949444c0101000c05061900385240e03580800036008107a84a50540d410030548240150185040058000c0c5060362511408080080300440c00c032103429a2841680c010481c6514204e0050100017281861400c180c0300d008151501d10141e60103011040004201c030307003404040598007518500c1e2260100c0440c00010741002c00710f034041e500714880418004250326040d48004202c0040c1d241a0400d984451510704007503490450925015802e00e0000b00411110b40000c5002800101510741580d00d03500d00c2c44a2010501c48114466075490310140700d82080e21418090345138406003200545008007a45680070054055004a8562424400d1060700e03104000903080c0402402a4882c0c6800301001b0103985084030054401c0c424242400540d501034480c0c512107041c10004103103000c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 698476294 1250 698475044 698475053
    0x905060c0f040911070203030307030606080901150b070206120403120f0e03031915060c02120c090c0703030207061e4a0d11010e1903030513060e03040305070b0703080103 75
    0x250071340010204d80b001c100c02c0c1c0050b503051000f54440d000715200080c00600305a402030040000821288050307141071607904000c10440300840888640200c0c0c030307a4440503031011802500030600a0055210998140001c0641103a61103101030103503503082010103140b0303400d00d00759020103008540d41e420810104202d100111000382c8a24034040011868090814603000e40f4007a80d07024800180c5010b601034110310b8603910415089030070000514101000c4800071303003004000f52000d5121040050b1044c00c050090f010b17202d41940154080000e04290030050340301c1c10703410881e0204d9502d0422481c2482050251031401041c102e400780319070002c03004040681c0e5003c02d800d280e0300304e20000c2c42d000640e41041300c03900452007540d407034a45040c030252040c02d583c10191410810b82010348140840790050f091f103000c00d80c051502155644456600101e0111640000f40c00d01d400c04c02c802c14940000001001124803c0e8216400036a85611580300303401601d10040004000360700400c00b14 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 698477544 1250 698476294 698476301
    0x3030305040317070f080f16050a020a06060b0702010f0305070203092e0203190306030506060103020f0c010908090a091418100906050f0105030309031f09150905060c0f0409 76
    0x620070708021002907048030030040380c40c3c400c4588800007070140241c458400d0780b000f140c5402101c80c4121405a0401a2940c185e41e43e00c0d80c801c4007041703008106000210300c02c000e1494031a030041400c002c03050300c07407401e100154480007042c3c2c0414000041015218468030840e0b2107041c0b15809141003d05c25820001c4800048052200b2000d40d000c0e19501c00b080c83c003440a025080d84c000b150340e0018025100030110301c0841000c107140c03a05a00f0030100e00027051a81d8001002d190043e036810030183d80c07400a016510b5800050f43c44c100d40c84003002952030003800e83c081c08503582040165071340701c0c280c25107051804882d880e9006201160400a000392540d1083c00c40d0826200812124130400c3d0031150360741c07015528103440f60240090407800c01c100c0ca0241c1030a4010710b283c0f09140c0f010036a18641000200c1aa6a40c840f0142c10486560700c400040c56005041e4080900415118400741001240030b4545004945c0803441700d200d52004c68540d145017084060a140c50244824001d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 698478794 1250 698477544 698477551
    0x6030509100e0c0108280c111b0909011a06070201050405180109051005031f1b05070605250e13090807050d0807020a02240703021f021303030305 64
    0xe407050301c21410003007285006081c03400d15404010b00346403402000042c00b1104c00b400e4010762200e1032941041d032080b441219900c034150f080c0c0104141403640c2c4200c0300011810088840d07405019141400c100e041000e5250100d000c64141d50f1503200c0012450803106010106480b0180141c004d0700903090080150070103900504200e420300d5a54070204107101600c90b00c0f0401071580300014413031244144200740d003250200110060850520f40860f5a40d00900591056071280741100c000c076000607040340d54100c9124841d06640d4068a401411030380001404a40f05410080000e4649218078000d4034081c5501c440c40801c454954426244098070f07a01c01c070381205000b50302400c01802c5028004102c1d2117100090b94640c1d42c0d04009082c282c01e40005d40802c01c2030380c140040c2c1940002e40844840c2c0486030034000658a5004024160385a00c12050003040840c20000389a00031a11f80810700003001d04001d60030190350307044224407031000aa401071403801000c0c80440d100794070243c0d1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 698480044 1250 698478794 698478811
    0x2710140c01060e010303031113031e120c0212010b0a05060f090301020301151101061a0f040510110706170f0c070f060203070e0415060c170409270b01060305 69
    0x14000045940c142942d945400a07003207180d03104010803c02d940351040302c0311104850f911a00b0300343e00e07600e421428581844050024500c4d29480102079041e0500c9001e9683d03ca9002400701888840c0600800854102070f44942000a140c0d50727403072030602820320301d02801060f450550f400c0c80104007c6410000a40c01c03684014001c203903240d1800d10045001c0c007102d1303203128194120610004c2c00c69011030309042d0203904007401044884402282440c0e0380e150a0706990b21a00101c1240b02680501c2c0d010942c00100d4009a01c02d031500154000350b02c602940649582136100c1800b074482031051505040ca03140d10600144003407802e9004141c010780003103080c0b454400c09032504510000780303600980701c40c0d41c000b007813101c2c442d00030a17000c4441200742ca00f0b014522096200308061002403103150240009900184100310740030316070b0400c00c080380041d69101c54503007600c900101448424824410454115480c481046020441c070185e0310144600c0c1c0c4cc0e003070440440c00340902904004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 698481294 1250 698480044 698480047
    0x6010303082d01152007030c060e0906040e010915060e0f01060815210f07050a0506040302040f20090a120b1303050c070303110105010603090b0705030408070b0c271014 74
    0x1080010721104030f00b005c000c18001009030604606000b00520120f170b00c1401032112034082c00f85251101c01c41107521020885d000201440d024001c1030152144010090001c103a0880d00301c41c4800c1ca60000b025200711101d0511140d891000c0340c070038104203000f0340d004224000c1c0065500030400c44001c106100292040f4000ca100c2d904000801203080100c15003900506000c03070782c0c035004000b50002050304480c3c0c4c285a610702000329417544034038007001c0d00032502c0300650548102c0941205100b0001c0d110b03940440745c038040741c2e60055040940214030442a020b800111045003c0450740d07000c0d0480e008022640343c0501804000d04905000c46c1400310601c030101c0d25060a020103401180207468291803140010429400c490058006000341031509100d0030101c0c592400243e8800d1072402c0c000d56070346403800d002919008003440100a1401d40b020440e0341305100000d000702009a04403c2a0080942500321015078003010180d0040328048002c95490f01c11452101c00303812941405 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 698482544 1250 698481294 698481317
    0x50607081e0a03360b1806011d060405040b130f120309020315010303020d0807051c0225260702090103050a02031c021c050c06010303082d0115 63
    0x4016400400c0d0b00404203942c0c0a09240081091440e0000300801600209800c1d04503a0300d58130300000c9010103818555000009164250400020700116401c00200e8801c0c1da5204071804010303803075400344480303082d400000ca20b071400c2034003c244c000c0b82d00c10b08140142d9104a07440c501a4085c02d01500c00c0f0303040c0000440810000940400002080e076000310702c584460050500d4600d48900588064800300010004290702055a010305560b6240151154030380a0080362140220308048046001d0481c1740071840c1c1c0c00d5401450010210707210140c0701c50300040e0a0750840301c07280f805854403480310f185070070101e00c01032142c5038009601d29060600b04141c01192080701c090b0000c80761584100488029031408100b02d480d0300302c88281c8500c1c0495040f000942b030348800d0381500d00340507a50845080150080054540000542e01112429a540c0c20000e208203403d407602e070700041d110381e04020040140003c10021490320310b07090301031f40d28124005070b200710070b249e96030b0401c0b2014821 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 698483794 1250 698482544 698482597
    0xc08010c14180a300b0703090c030506090a0c0603090c0e06010302252a0e0601051917090c06071106161115070f020f01020f010606080a1505060708 65
    0xf400250901450200e5150f65180807203c400c09801800d0448130103036298180090100b0450680c0103405281c00300e080c03452440c1005460303402d508003c019000d40f50400815a600040d1819401c1c007954400c54007651f90442a01150700c0903a01600b00343d9924002d002c030310004401c55401038810f150043c588442c2c031a01607004441a00e4840079005c4e0208070a0a1150490300141440c25107822005251803101810380070100501c60300c81c0b050790a1001a2041c0e0007402601c4811042c1e5400c2d13004000c103604000d03c00008903a01c0b0195003d03210104100316000200105514400341800e80b030101c0d03c4e1a410307100720f2044156548030004000303441d00505d00c0018031043e10303c04c50400e841c00c03404a0403c1002c030740b202c0041c041c0e1201070100703101281144140701e40301074043d10781d284500c034032000407400c0c500da9010444145d0b00700700001518641c8204000e12541c042c5c41d007000b114601d6011200c209059100790380d80f10302d083c0040c9021584140007001c0b41a9142c0301d0307141400c7c84000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 698485044 1250 698483794 698483809
    0x1d030a0605090f1603020a060801180f0908070b04020915010c06020c03300c190c050f031b07050405010f150c0c0e150a0602060a0e010f05010f030c08010c1418 70
    0x8840130700440b034000401c06c5043c2100c0303a01c09813050303007401d104d5981012240f803070b81080320301c5109010352691000783d404030b019803028030015049103000c0c0e90b4400604044450760029a401c07030050110303c00103031110348040040d0b20b5900e0140d59241c20319407591500320294015400002032404104000000d5020050084030b0100102d1081007400b10720b1031407203990030001022410314060401081010080426404650103a141020200c0000ad070600078508445c400c640d00103440009070b4402d880e0030006122002852032021501d80684800074403040c1c517020310402112400c0050140085040e11241e024004600d20b00390741c03000c4003501e43da8120507069100303040d500c01c000140000201c80f9032010700e10310340a83d014083c1514080c402565840020050350685541d01440e9030029400e4010003503007407140c0d0040c0801c0d41c480c560120405401d120840354000c03901c400040441d010302803042e80100170b41300c40070318102c6a11900c9440d4021441d04135070060040f0070003640c1c1d1320100c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 698486294 1250 698485044 698485063
    0x905101b050a09151e030516080403051e0c0d2f120307030f0e010b0d12090504020d0b010e0a0f0b070f141b0307120609020a0b04030b071d030a0605090f 67
    0x42c0e50300172140c440c90000030405010414041010f0800301041891091009103045500396440c00e80065516403d08882901401e4591503214009a950103284840000609122240034050b2540c015100da010b43e00c0d038411320405020016030100b460300540200030746403030054460741a2074068112001020169008942c42000301c0c2d07494542500f625031920541610812090081081c2200d21000a4500e059610002c0038400c81058803040b0790f10400000c402400051320640d20b440c000c1400801500c58020514002503000c45120200c0c41d010455808803401040121b10850a01c03829800390341c01000240c1e420340c02c0d404010001841880b483d402201f000c4003a046144404c0c0f0b007507500c03195483d841486540158001e103c80307812101c50803400d03580150700085071041d5201003080c15903968000c80c0620400704000042c00066901988030740015500d4415650031110f140b0404c030030b107440560305944210043c0380001c42a500c07043d0054002c0007103d0102942d401030926155506 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 698487544 1250 698486294 698486297
    0xb090f0a0b061b060105010906021b01091805041e0b0c09010e13051005010801060215060f040c0203340b0a0e010606020c0108010801020301062a080d0905101b050a0915 74
    0x9240c048403c0401c2c012540504400d20b0410045450094025a00c10605058080410110151043c140c0c01a000c90000b04081411640c444240500150040c1002c407004d407104841c0c0410382d420400c0110b6000e02182d0310040310398540d140c032039410586400c00e1420354188450360700704500c140d840171a4200c108852000118a07440c1c82aa4140311800310360001b4140095031005200c100c0e004640390442c8080500c80c200f181ea20f01c000901242401128503401505c0c02494820441e0302000030702c0c1d0303a0b1350800380002450342d24804c0c800d031069440d420300501e01841184000540901001ca0300406c2a0701d0100304403070001d0589007110711952150300940d00c40d1120742450758004010600403c1200021801c40d071420394054039007902d88149040050fa001802d1443c0074041034480b07010782c0c11501d004c1d00c601a5411305001884021419202845081070b40d00e50040785008401941c00100c2d10078480c28001102030300c02e90000c440074010304c03400d0131010542d00315504c458414003096 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 698488794 1250 698487544 698487577
    0x71e0b04030b0103061a014515021501030201030f0b0411030a1104290705100c09090203070c02010509031e0c0a080f1504110301090c060908010b090f0a0b06 69
    0x19407503c00102d444180060340031003c00d21400c1440d030f0f00a41e4218000c5050002e40c5401c2080304800400c6100320362301c0d41121480210340b24403a030246107808040d160f11120042c1e80c00203180301030740e68108000360360004180c2000144015417003600b00d491a0340c074841005c2819a905000541038504401e4003014085010042101c680d05900482004c040c908c07250a182c54289031000104100303c4083c143d4000e014020402c42d991500d0484038299006020b5450381220420384001811500000c04005541c070348000c01c5580303441c82100d0160740d00f03449613030030b1040590066485410244041c0c1c1d040c000c00c40c0c840b10b0b115083c500c00751011240b0024010510000c4108000011141c21114860b88001029201007800180300ba00080c1d00c400b80350000d07a901d1a0040c1401c11000d0896015400c0c81100003c020b101e071a00400d540e82034540381d002c2a12000e0103802c81e0341d07040d01640d003d1607020118031192152441c180d00b090316224081a8540580d010a1681e4442c030051100c4014 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 698490044 1250 698488794 698488799
    0x13060f18050c091e0c0702012610240f120c230403170306131b0206150607060b121906060b0a27081f0b0607020102071e0b04030b01 58
    0x50140d0a07550103c013084011100d1801444031078003000005054180342140000c40f10291387c05049070010520703165205440c2161006000800c01109403080d00d0f0360781d9496401704030040280c5141c01401c250555100f80442c03411000c8400c038042012a4040c004115590020300310a0300482c40084440e490310b004642a01a4038200c403c0c4000c02c580c041c4000f4441440014218548400e10050721030701c4076100c1e15980006441e0f407800318002c5041c94031704070400c0da98a040650702e44c4a083c1c2502034030001c0d503d0080e0101c10885046415500c072800f00f03c5000040c1c0b49a114101d0703003d029200c5600000840300d014a0800c010381031080c0d0707072131080208003006418010740028090314410b03507050052020300a8003908130f4401100c1d01e881d01d0300b41c41e8107000b4251261001055558101c40d080409054032081c0e40c80344010022540d424551140c0d10360810300c1c203d8001944c1030380205400d5140c642c000f00f603806e217101101100c070710f2b126000030382d184401d000d0300295000d8640c4007415413 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 698491294 1250 698490044 698490049
    0x1903021203090f06071713080115150f02060601050f070c0b071e0f110d150510060e0307030209180d0e0406120c05060307030209040510090b0913060f18050c 69
    0x2000761075660301c14813040051320001002c4504140400c1305520100e903c9020305040700440d44029008110f456290002002010184200c00c0301211a580341c040c235820301814003201c084501c0708140015912090120741d01d5407241c400bc01c10768206846680c100941a41c0750011034500717a002144007007011644c0e50a104c1442545540c42d054117002d601461141d9650500520a8500242071044400c41c030003010349030151131381e5030140d0010300c034007009106400303d400401003074030b03040600000c5d03180103d03009024075200701d0315500050003414200e00d1035081101c645001030201801c090401c65400d0307604020000d1135a1200d103600d0f544410400c410600080325078a504c59441d0b2007001145002188035403070a901580e60507121550740c8e540c2d80700154080c0c4180988203070406c0c544020055030b4103a08800a040d1404103900784a512130500070000c1030101610340c020b00c1e8003000d1015000404650103000c01d003003810400f0459400380c0d2810306071080d04407000d54641d04983c603112020b1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 698492544 1250 698491294 698491309
    0x4121716051b0c2d04090c0306141009020708030a02210708010612110910050c2401050906130f062414041406090a0504020304082511190302120309 65
    0xc401068100140f81008003054044828984801c3c0586c1c0d540e554401400100c40d00b00000d143c012000740011101500d4040700941d0487d108440c200c00941d01289003070740ca000311509280c000000034150b44a50715000000c0d4001d8200a200000c149440005002102c4055120f010640c44909040d0714088001c1c11600a543c0b0102082e0710b0910f0100d801e08010040e41c0070810140c80c1031130020071484080d6490310410051403a18403ca142c426178090800007003612144607280194481c2c1d03614824010345400a0b640c15511880031100060580410b40c001c50601d010070380702007501552081000c030601c0c2d2000c0911148002440580c144507000145100300c084541c1c02c10380391514000d9082c100001781c8a48601c503c0e03000521544580e01d416030000600030081c0210741e0b0342031a180455031980481440150000039802c078156000007035440140c51500480b00c0680148480100304009841d0b4840000ca40380d02800800580ca4000b00440300c0082c603001503503500303100010850309 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 698493794 1250 698492544 698492569
    0x403060f020915090103061e08010e06090a15200a0e01020703020105090d03050d05070c02011d090103020d0609060e0105010602150105151b0a03050304121716051b0c 73
    0x481c0100034540031521050f00c1c2400c400b069690090319a00520012009826607511100001d0301c106282c05695070300035040800c0701c1c00400200810f80348003140545030310b0200e89504071030700320860f950040303405c21315150540c1070300ca000000c03144084011310b1142e900300d00d4070b20290440458001d0100b80c20080b403030701c0200240000e041c114035590008000341710304204540141c03480712580082501460665100303a030100400d00c41d6203003602004105005002c0b06070b00007801c4240c0c5154041c5056034182e0a510040c00829481c1c0c01c42d024402d8215407820110380c4c03550380368112404078a4900c101442c00d0b9180c00049181d5140034002841c2003e0429641c1998041d080100116602e06c04180c24009890304d0498443e0f0280d280c604c0b004002c4035001182d801030602d09001c15910034020b521440c802d8000b120321141c0d13150308a940000b1441c00740703903448a01c404201007401e81d800010103141e15160052401580400320a10030104c00c201c074007503a0200d081414146008914543e1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 698495044 1250 698493794 698493821
    0x1020403080a201b04090c2d080309010c030e0301140402040e03160f060902031009030906030203040f060f150801140a230402032109010e01090f0b0d060503070803040306 75
    0xf03141c01c8449001d4883c41940381c0501403400d91009503c003510b4070b802c80e030f8040c0d0308100f00081440d5103080b030a21990320110040d035400d40a401402000035407580c000240c071031880041d4100340450b00151200016128150305016054691344e1240d9400d0041c54903003405814254101c3c14103205110554540705405282608180f003501342801c0080c061606150b00000305254602171410110010170f90040042c1d00350142009044400c0075030381201c0ca590f88660350b20032070380b40d035004100c0490105542c01464030300000ca8030408101581c100c6042d01c0e01c1158001090206138101081309070250388018266511011000007503501c1480403640400b06600a000d00c0440e8140c0c4012281c44c132940c0024244414049010b5442c100300205800c001c3c00c095100440c034034640580c0c140c1004410500180450304090340c1d551007500c40108580408060348401400c051418103241c1086488502c50740e0394000006459504103c1400207120600145903150f0950070050190b80c240003036500d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 698496294 1250 698495044 698495087
    0x409062c0702150c090405040305030702150c40060912081905070f030e090702150a020a020f0106030602130b07050303010510021603121b0c141201020403080a 70
    0x110380d80e008070358590058226400360b02280e0b2070b42103071318840c041c0301c1d00c2e80d030401d281004000800d030300304000350702402c0283c0032651400040c00030b086502c041103074000640c904c14000341da4654807445100c56081c44202100301404c80807540240303c17004407600425140c2001c901040100d4000e0003030000f81c100580516940e2401d81c4540780e00b88601c00d150b00310840400002c00c02103100c1c80c16540e000f540710b1a40c0380f64198a040060407500700d121840d120b081200701081020303000207044001d64125440c00601a80d80d86c16400080d0001d00b070b20403e500502d0713103001000304280f142c000030310320a11006844104062403034420b1314042d040b1008041e000c00510b4040341002066904681044900c00310340c3d030b0b0800c0101e04105890803c03070102d43c6902c2000c010800a0280e52030341c0d500c130f03070398149568800000c52080d40c10340c0741c009000c140040906100310b0340e40340f001c24588600989005179545c40c0880050032070340203504c2514801c40200346280c1c5540e1000320252400501440c84 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 698497544 1250 698496294 698496301
    0xf220c020114041403190518180403050c010608030c0a0606060518060307031e0912051606090512070c080c06040e060f310f02190e01050409062c 64
    0x100744240900f01424191465241c1d10f8880740800440344080303011280c8002003102c40c20060025041031051089080c0401c03500b41e0981421181c2c403459490303403041500c2513142ca48090b80c56038401000603181e55203a40c404103501c2400c000802d1001e0f00da10003000700d2040ca0500301d0490b04640c0007081040b404208888003480c507404c08000e6031500311401070703503601c07408000c1e002403d0308100d41c441c00000d820805180b00c0389501c11000030340206000034500f550003004841511402a1914078145240700140110f2030716882200440c2c80b0f40121503d401c0c180090320b60f03680200a0468030202e59840603c521282441140f01c14802079a540382418180740012103103410003801c2a02600319000c400c04282e603030340d00c00340d014401c0320701071300e41001380c3c1030703040c5050381101c5440d44014104200140000d1051084545040c4003185404000051690445501021100c0301d410051300748808603c0e0680c42c89604014100e09404291080c0ba11084100c0c0c066014492002e080020042 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 698498794 1250 698497544 698497571
    0x30c0f0a080304240903020d080603120d050a06030512071406040210050a140a0507020306010f051f02101a12070602030901110106031406040b090d0c110f220c0201 72
    0x540350800e501011440004ca84e08095518195040880c2c9154504080ba010281078011928031521075180e42e601110350340300014555600020340031840ba960003000b03c501e0044069014a0b00102a24030210341603a5a03107a6924041c8030a40403400c00e070300010403004100640d003003130030f100c00610060b002610b80340d0001a00039008411110a00000052001045100388007645c2003241d0958030751b4071003c174035500401a401c8580304901074406c900000c01d614010049072411140010528140f21100d0004400d100c4140101c2e01d0540c4548211015088220301580326400c103a00f80d40748144106008021000c0c90f001c0d8807207569045140244092640841100c003007407020b0800f0031401d140d9620803801401030b030784050b114a128544806001c0300210b0468010b0780642d0442d40d10340c4800d01c10781d031180340410406002c01c7c26030007030000007941a400d88490140060400301106008400b20b0074848003401840801c60280a19914810070343c0300c0c141d400b40d4148001c101c904008100c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 698500044 1250 698498794 698498797
    0x30809041a0d0c090608120708131d06131424090c03010611030f1812060f040308100e15030a120e030705040b030a060e01110c030c0f0a08 61
    0x102900440d00d03440c0d041d06200c22890095580d650182912000d0201410442c0e203914040c0251222603082182c001000103000032142a1340c1f0440c4051890051281e99108080e800080403200c1c00d4400100080c501c803240d198803403d445092505001440c14030100902202d0607030302c0d17440b0103180000c0d441402c042031000396031000140c62408640f80780507020840c02d58001010640c004c2c021010060b04107080c07400b450480307001d610b03140013440041179200c1c0c81e1f019100302c0d0f000c1042d00307221400c0740300001c540f07164845002410311584040e08041c440d00701481240d21104400c8040305202c101030340075040320790140c401d9122640c410b00344845106c4a60024294542e0b00368025040b1005684c144110000e491b40440402449403c1200192907244105207142c481e01a44200003064100b9004465443e04010090700741004182c3d5007000610b410351150203990340e1800e01003030169940d0000d00410b9134a40c015600e60150134285460141c40740c58030101a0840900300000840030300 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 698501294 1250 698500044 698500057
    0x304030e100306090216170c030304081e0703030c021209030d050904110a1106010902070c05060a020703080f250317250909150e0a0902010c05070609080708070308 72
    0x101c0000002458100440c00f414680c1c01004002e0310004008100301412254030211612034040307410108402036100a00e03000304030b81e01c50150020000140040d100c10300400c0070020103810310508400103410795049030410401240803d50300c440b2001119010420008a8902c1861040c03074003240c503000c00c0d1920988c801c560305100740030808040e19a00e541000819250000034284c40c2c0071a2031005042c10700003421905540110400030034100c850780202ca440c2c0703411009041c0c40900d408140304003640b00381509021070040d2100400041c0308400200702460b840c01c107540c1c0729034103802c5410010402a005403800c90081c481140040d8000c1c00d40105100d070b0b01b003400416a1032046610201a40d059408a1000c45081313092040d5000072180d03007910b0115004200c80f194901822810f0a6940140140c104c90a00040c2e02141d40780c001d009000c2c0306260074448400907540715864100b56400507400b15803c2042486460b0b410000300c3c0081680700b005001143c0b03540c03030f0000c1c14828007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 698502544 1250 698501294 698501299
    0x50a0501050c0c13140c0906032403060702030309240a09080d02040905040611030f1f0e01080601080f12070303050c0403050f060403031b020304050409061e02040e010b0304030e 78
    0x32900d01c0c0d000d941408818085200a0301c0c030301324a2203440f0345400601402400c01d01880c5c41d00007103905001e038041560319603140034282074a03540703400c509181401680d02181c1c0d014507000e0203070341c01a18240426801000c070760700115100e041007004181040b1059161425401c2d2084020012040c071090958000200e00c4002480e8401170400e01c500f480b61042d440c20782400010700003034500181d88224400c9000342010450758800320a10704540c0301c00d640740d1640c000d60201107035070328180c00e146440e0322010030749a502882d0750700a11f507a040b809901419a6811031001040054001d00000180d910a174001e440c0078200741070204500e000f001d8006d1b0826039250005060b02e504001102c0146070001c00f120f600070f2220b0310150307840c10308a034102d0019080102c54103040340482800c0107010500c1d0013071350505080000f40401443c4000040c1c8440d6195441c900f802c515292400c0d0a00600040140e07440341400c000940466040e4403005210004108120110340e0011003604101c004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 698503794 1250 698502544 698502547
    0x10b121209060702030a0308010302240d05060f0a031a0901090c0b0702030a0c080303070e0a14040203100f081e1c0509040e0610030218010501082e12110901050a050105 74
    0xc03101040443c001c0000080d0980b10704408401450342200502d070483c1d100702c40d40c1403c280c5d807038400c420740c140c04c0c800c4420964085c40b0001c20301c802074015075800f01e0007800340c00b1144a04000203000300380a40c803da82d401e0048001600c071000c0441525402a030700f60082c403040c051540c03480414005841003140c902c5010070004115601400051010b68001802c0d01c0c0803601c0d9010240c0340c3d4020340b04a40401e0403c0d0b1100c1d003900740409158100d41c00c0e180e0701031071605005c042c800a9480180a00c03584281144041809403d120a0300058030302000241040f0b140640c0100303107801d100080c04011740c4000c5141c01d0240003c0d5400307c000d0001e1920310703200c502400200f406007440225004e0315005e22010056007402080c6564200c0e4000c0301c0c11900076140c40d5941180388000c0c007903d80014041d10004848140030b2108a000c40d2140e20306015102c002001195001c03010340107040070009100701207040c040090703c1540d8004003100d2100d0325515280018000076411312030a4103200d070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 698505044 1250 698503794 698503807
    0x1090801050f1305121912060609180204090c05030910090203190615080c15190309020a080607120605010e090f0712050a02070302070e01060903170405061308010b1212 74
    0x201400b20070321950642005544401c00b80030f0541b400604c080344600000c101e841c83c140c24800c54050341c42150000e840d00c1203450f06003040d13088101d08551784c1ca10165001c02000940d0a82403060780c0d12110140d94482c1ca80c00c02d000035908120303880d81031054040c104034180000d680c01080b90310364484901091000390300d013482c1110241c01c1074013040324401c01d803040025410001146c1c5107090541180d0f1010100c8214002c01902d0051225403103080d20f41600310a40b0780d0195020138580d9000516210700e0326640d01c00d091800780c04031a041c1c0042c00c40840805c40c61030f10701404000d05024200210315000c01400314140e140010803005d5090084c00c00b01e95400c0c052044050007080d400000d11162801591070400f07544450400c4005100700080003450100110106058800301c1d0340700e040c0c86107952184003800715020b030100042c4004100000307031a0b40703910003045503c0c2c0b03140d200990580740031061421521004c44445c01002444122030689102062140e040351028500c0e030b40706c00c07 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 698506294 1250 698505044 698505053
    0x708070e130b15041e1407090806060904020a050901060f090e01031a04290f070302031311010516030e13050c0d2003012301020304060e100e0a090b01090801050f13 72
    0x3200820780d0311001403614010340054280c6c108a414400c84510001c00e5194080d0407118813110788254005c940195000c81c0341d03850070b542c0ba07642107800281081405512800012960b080a0b40107002048211304108030315500044240010552100d07407041d9985507494080385162005280000200110000381c20451f4050803e0f006c0704880f004844844255803000582e900c00781ca00406040001d1300085840b8820f0003140c4c80fa034484420542c0041e0582d5a070300c022808030504e00e06110313040c01035441800001c0c0e0300f030ba03525009036500e5a034100d880060010780081508191086410407040100540402003251403081c441d60000030300144a088105a0b10360104c0491360400d400800000d88208180d11400200904180750400307940540040e6078030f10481c401c81c00400c80c106034a803411f04d0710000128921400d424002c20b82c41d0707044005890380e1070729000281155540c02c2e0f20021541d020250b030029001c81301c000c0005040c0721134282d40f120340c000c00200107055091030040801 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 698507544 1250 698506294 698506301
    0x3030c020f0111030c0f01240e04150c030902130b09152e1818020f090d060e0c033012070302040501031a1516050708070e130b1504 58
    0x203c50001c2a680c03921484121207450300b000d0790314500250b00b07010380106880361078000446c00c400340840131010035161545000d49604000c2054070b9285402c98820b140030154098a180055142e0380082c4180042c81008503615841280280ca180740800c610810b464840d029504640c0304c0062410404811002440c0002d02c0c10346000900c04008281202c01d41240e0a8441e0100c6525402d40c81d210510010340126614447c3e00755000f100a03460b17001c0c0c0903907401402154180c0e4085482c101001c1d02190600f50950011030794290383e140120074000080c4949100c40108034041d0040c0540d00d07008900c0d00010072a00c0601111025081c0d140079508022104001201d2505088615194a010380250401c1c07041c1404242001005030240d14080f00c4076040310001040300070301091507138005071250800c5022209507107902d8080b40200340c041000f1030003803800c1c1c0002d0500b01d0811650481c2d04c0800392801c0c0ba04462400c6460000326801c00141d07009001d43d0395006550034031030014014 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 698508794 1250 698507544 698507567
    0x10e010207110414091b01120c02061609080a020f06040503060a090210050906070f110a180e0705100f03060b180901150c03031508060c04080106080703030c020f01 72
    0x65031000592008001e44040355072000801190108140048046800301c403200444184e03200707410216811282c64106000c030065510103241090640c07800100000865403240c80d84009a4807400800200500c280250010140185840e05086181c4100c980c0d4690003d40000e1113820700700e00b14071084c0c8030fa2090703034020440182103c095040c4000800c005250b14071059000d844190000c0103014003507412211040c50107031085140828544a0500c08018500708641d040c140f2a1070940307650320b404072840a00b00005000c00916690b07400c0b801103611501403034415420841c4c003080156103020300d4540001041c200840501c801c6d1000701d000340700c0d54000381111a00032406101021445a510342c172898282c481000030398031242c07006110182408142c00080c402800f06d800240b2035045125403007410a10410115201d020003401e02d1001c540b011685200401c040041d000d00b4003d810040810310b010b8050b2504541740240404010200603010b00c440340c0e40b103040b42c1d200f02500101c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 698510044 1250 698508794 698508821
    0x9030d0213150c0f0803090106050a09020c19030c02060a02070f180e0a110d11091e07081e18100e010605040b0307060c14032209020304032001 63
    0x1521504010340d81e59410160068400040744080d180300c81c503024070b042c3c0d24020b030805511030f240340482d543c80409a0000701508465500c4010000795900d409035950b000d8404403001507292291108164500301d80f07058000701c1c08403d00e0505001c00d40000c004c0c90401c0d0140c4415607070307841d06902607241c8001c690000790061121040000d00c080c9029090f13003201c1414000f4400f00d050241d10303d0f03a458588c1c1c405081c10440340075030380d604d00c0d01c502007460062103a0031240720b0b4002c08001442070702c8202c8130490711000c04d0500007000c1000380c1c880c131b47c480610b04000c010b60802c211804262030340c84110842251141e80850300c104826041130000740b1810b4110b454a10040c050301d00035120217943c5140075803c1500100c0e9600c0c090092090380c800250090140910340001154507040783e8205664030012640d1000070302d081030000b0300010210440890881c0b40460f0540300e40c10055014685040c4180184000030758043d1000c840002c40b0991104203070306030301140e07005040c0248080d030f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 698511294 1250 698510044 698510047
    0x309070f1d0108030316051b0105130b0105030706020c04020d14070c060513020612060f0a09050403090501031107020909070f0f081204031a1003060507080405010507020118080309030d02 82
    0x70120141c0162035410309a0846000041e41da402405a0b07a00094568642001c1504440c9102e944100090200355614440b64581d0440e01800360303086030030a884942010a4210502051185005003c3e0040c4402d40091040c10310341a0001d45802440380c40d03510031a000503a010b5500000d8002c95681d841e1414046840e06142c04042d10035040c00c4d4007251700350b00702000154161030140aa400c400d070080c010070f00d0001c0c0100c07010750780440106900c0c1d0180200f03d28005980b62002c1100c00b6000c1403400140ca42082c0c240a0801d950690109041504003030089194022180554070442d5065848440300d0300d58080e400d003403e115801002140458090004021064a4101c000c681c080e10550381514044c40407521603200c1ca00002e0039003440e103400c010400825441d0540c1c0070400d40100d1a440d5143e42da088c3c15940140d4014001030b9002d803d22003880070a101d05034001c41c040c00200f1801460380c80f0340d0701c1c85c480d081c00949003a60210020b00b900d03201b481140c3c0328030405070045 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 698512544 1250 698511294 698511299
    0xc0b2a0702030c0a18020319230f06010c06020c0f070b0d050903160809010c17070303060f0b0714070914091b2d030303040c080f12040b03041e0b061e06030c0309070f 73
    0x6070801d0740c80100306e0107027900020206d45440c80300c0010b1809064180d4500b00d15242c6911031b20b0180d0300c66150f00703050b40708400240101100c2030181c040900401d000c1d40d82c0c1d4104201c035610030381d4406000060950401c000446455428014040c040c552000700c141c1c5402840005841e0244914009020605031105405c007034414240103004440c03282d10108500394a41c00d42c00c0f0720341e40c00d015580c443c460030450a4003003200300c4590407042192804903420161201250700943d079000042d0903a2048000c24440c10385001c0c441c20340c0c200f125082050810041c1e41c0040c0f05000c482281c80b0312041940300403400302c441004500398282014040780d583e81007915200119020034405c000d224050320070007111144000c103081025815100c1c00c40c2c20281420034002c429071004c3c004981800510320240000c021382810100350f24020f4640b1000b0380390443c00d00c4003050742c500100c0b5500c03001c480112929901c00b0243ca030001250201c0a44a5031a0028203141c07a10b66040290002800b8200 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 698513794 1250 698512544 698512571
    0x10f0632030a06140d02012708010504150507121a0a080304031106070b0708060109120b070f090501053a020304050c04020a0c0b2a0702030c0a18020319 67
    0x40d800b450148100304880c6640364080a0543e0385004426130048503448440702540c07090b400c01003400d45172148150a813514048009280545900682c417a944a00812050200b00303100603101000e000c1e010f00c034a10b0840d200803c60441c101e09042c0e0301d0340d40c204288c040314020881844e01d0501410411803180c0301c51448d60f407600725200c102d90030081c4200103841404d050701a500c49036072201d125280f41c0c4400c0c50654107000300409036410403002c0c0c2e8000400c0e0401101c160382040c01076006000300d04011070002e0201c9034010154003841502e4408105607644003088031020381d40001c0d201500c4440d9a000c14842c54000e0300703a42d186141c04490006020194010344c0158800c6c2c0450b0610f803c540140030a0f03000324410000400d021080b40408100712800c29580700104007041120490483e010284449180102f100740900c040303005c800b18242002006401003080715a4020b0a20b48180c224038040e01c42c0c509050750381c001c000302e0108002181c0115064400000600c0307100000f610 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 698515044 1250 698513794 698513797
    0xf060513090209091504060f0212070e1e100e060f07052a0a05040c0c0803010602070515071e060915050604050a0903080727080601031a010f0632 64
    0x1c20780c0714a8010000c90700c0f110001601c80e540444240522419603280d0700c0d441d00404144201081c0b00d9002c0000030040444107407541d201c0c00c0303207840720210b044c001414401429682e00000f55030048180f0045120342e502d00c80000811400c3c580031004511110210b00c80d030152200070241c460001c0f0b41e403010000b0200d041104100e004940000c0c1209588103005a20380c10b030b151303035007002003034200b4031032030909401010980101d42049008550b0903030f075240403680309030300540058011540501451420200c0d04401103401c42900c3d04260441e1a4070905030f01c0001121000500b8840443c10131140c0e810a10041d0b8002c1440a540c0c081c1d0b800c1032010b00f0048a285100b50700e40000554103405034402c072450380740c140d40c55042581c0e0300b6a064a045c03041c184004680c000c056240c0034845407248440d8082c0c21603801030802035240d890711001c2001070355070340b50780c5156a800500404060380b070b0704012200e60303182031a11510009080041198035044410410550054060514040c10b0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 698516294 1250 698515044 698515061
    0x211203090d05040506040603020a021e0c130515010e1801030803180a0f0312022803051003050a02012015100503010b0a0504020f09090403030c0206280f060513 70
    0x3040c0e6400703881c6408115524030035401125806070742030100b406414403a902820210303944d40100d407400c1c01001c00c0c44e44c95901e9088100456442803502003143d00f003060b503101010100000500140c14404000d002c44030040f9042c0f410481c0c010204c1e28140d685c0c0e81c01ca5028a00507590724040e585070306040c11103510440c0c09407002580420752960f50b80e40002c840c80020740004404039001781c0b550f01110200801160340d625940c0a00202002490419000442e0004110140546400c1c40005803c4e00d10040c0380000b181c0100c0390400104101045031030502e0760900c2c0c01d05440d4402d0a8542d038003491440b8054052260700b844802c07400c01d400c00280204003041c00d102009030386204060aa0b40c42c0f03100d294000d03e08200410050030140c01078080548e03844869030400e80c4980115440720000c0700c0036030000c0d44403080c0f6654550140a619000254400c40508400c3d580c41c16a40001c20b80c2c001c0c030180c035614103000031005820340c840c40140a0040580003401082080c0401519500 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 698517544 1250 698516294 698516311
    0xc0b130209060d051b06041508041101050415050a0215010806070923010503040c030b040503030f100b040303050901200705130605031c020715210506030c211203 71
    0x110110b03045140c4006103604450b4490003c1c1002d402620a40c190300c640210043c0d0083d00501022078400544c08201c540c2000035034501d4524034040c00c00b0300300110303e462101c1c14000300300801e1226060614a00030f00c0661030a08a940b41060003040b481c080184021826030099180045000ca0700850454060074169071a21442d645440b0f180b02e02c03040d10303415000f104005410402065008a01940c1d00a000f0b0070180e1520b80c1d00d450b82e149852007100c0032034250b08000100170552600815094102d580d038900182a00e0612080d01110710490001a0600102141140003688100141040a0400040c1070740d0b5189040030b80f50340c0e001c2c40c007425105045146002c1c10700324aa105181c04c556008004002c50071070390a00c1e40c41c600519820100b180502000440e0803484001030301e44030f12055407900030310052400c140c105501581c4050003a64200414810076542c00119004403400484118031000d103180801c4074002690401c0b01034030701454040f89201c02c0ca4002440c03259404 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 698518794 1250 698517544 698517559
    0xb040b04090e0d08150105070c0602071811041a130308030105010311030402030c01081e09030403062703030e010207020a080105060102061614030a0b1c02101b120c0b1302 75
    0x10b44115078540701075400c3c80c0f0004900c4000034880940600342c0c0b88110300c0605000d4a454000c2d201c621844010b508142d026034441c1408120000f03581001c14440e07401e61204003c249404480007d0900c030380d10a0700007681618a00c01c800c1500c00040715800500c400301105010760728601668540c10901c500703800700c1d00e824442400c010340d0b5812a403013107a005014020810120b001522080f81c040c0040343c03c2d4042003603000e04280e092112030f0003034142500841e15540380d484d00340e0a940c171030060001001c440e64900100310405880c403e40b4607525040200300d0030880c01d209070080c000c80202030f60001030341030000388850341907010500960080c2c1c281c48896441c05807805241d61041544000121f02e042060091a002c01c05150040e401f6000411901c0c554070004220b000e014100c0e540c510300c0204100700b18500079254a0344502c0508001c040d04480742c40708059800002000b83c032850031104080c0e60b891040109002099010304080d0182c188003c119482c404d2602e07003203001c0c00c7c5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 698520044 1250 698518794 698518811
    0x1121d061b0409110f1204120302120a09060e15011d0403050a080402010302042d08071a13080105070c0b071d1e060a03140c070804030308040c0b040b0409 68
    0x1e401c150030085111a40c1d014981490301d0043d03001429000d0003224180c00070311041601480e684001d01b86803200491103202410302e81000903140103041510003d1620400140100503520401503501003d034040000700180e0a042034005004811070301e220900400034a14000501251810306a444034034400c100010403900e071441246082d20b024020407424807050007100c0c814030165510074418900503083c15516000005d0404103010640d980032200720b00c16002e210201001c000510040e80201200c6260441d40c032007441803101c41140c690340000e0841c0110b649580340c04002d10b0110001c004034500810300420313001d511942200c01400410104010038802d2040e400100300c40c1c80fa0400d0140902d042201c10003000450058030922070303421140c1552140d0103841d0030701c5c00c0d4401160003100611164014140144440040b180602290012440c0d40050310140c0380e1606000c842038882d420b100e83d014060750710002c140040001d010440a410360058004c98503014800d002900 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 698521294 1250 698520044 698520061
    0x10804030c0615092007021507050d050901020c0f01080106051608030c04050112060e390a0e03010905070509071404061701050108070e0402030c0904090602130605070305040e0601121d06 82
    0xa10110505440140800e00142c88e241407501c4d400b846804065280c0395041c1d0b41c0c1030416a540d800c03040820808213022655507010f00c0401e82207042198007801d00408280043c11840c81030144404111010554001d00184d0a07151840346030821080c41c0c50345088004020554081d0240e103001900e10000c0c462052403500401c000e0b145460b184075035036990180350400c980c131002100c0d011240314418060103c001a04000129100c0300c00655039440061005004d00520b82143e50003680b6100994000c640041502000d64504581c2801c444e100c8400c1203a80c102026000b00c04a031001400041054002c0d81c1e500d02c21800d880740108503a655001034409480403100701c00420b0310442c40350350516056005503480301c401400c17181810302c2c01c008201210400d0004844d003d50000340c0e6a13501d102e120000c402005141b030403600c4d1000c1070341e000700356014510840ca51b101611000ca440760780550781c107005c0c580003001c1c204000c02400c480712046c1c0038035002c01c044a002c0d1701c010a0b103d1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 698522544 1250 698521294 698521331
    0x812010302150403114015050a03061d07080601030302010c110a15021905090f030109030f050a03060b0f0310061827090b011403010207030806010804030c061509 71
    0x1290400340781081c05c0102000d02c882d042d984c00c08041518246140da070800755001c29005400e00c0c1300089282d0215098001e002220520040d418034100e10101c100300f03540c1c0e403042ea10705a075406800803d411003c4414842541505c0d03108000c980207089000c00e098000192060407a4001d50003400040c1c44d0203402c5d100d11485095142240d046075200d817001c140880107901640240d0600146031405005074000040500c81c1c0450000b000000c0600c06407030100e420500c08241203000b00014605650301a0410940c01c14a0090207004204228414040d6011900400450032419901e410510400f403081e4807c60711500c8180501340e01207480344c420244180300442103046148002d082c0003902c500520001d0103254042a0550b40b140116554016010494405c40342000c4035410100780c5900480308000b9076000e0307803042c0301d100c0120b036209000035004030081c03c009015848606080f11a4001418040c10160030070f10540d81051916006400700c805015042049208000c03160600 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 698523794 1250 698522544 698522549
    0x80c1005070912020118060f1101020a020307021309060231050a1211040c0f090b03071407060b0904110f0f03071e03120203070303140906040b06010c08120103021504 73
    0x24140141c02d0180140c0c004161a149005040c0698011584011b41d9503d00ca1350304004002242000080d01094110080c4c02c8102c030404002d505062001100035030702e008400c00a4072807801400000913251889d80520b0700c85800210642d5105c1c8401200308241c7c00840840c80301c8a00c007802c4452065a031100b01e8191400100590300c0d517454484036418a0610030025500108a08040511681c45100d8045941d1054032030040c01c407017020018040021070b900400300040100100030b14980c1c005040440300868020310303611007101e4140311004000455400790841c0140e0144010b00ca050088020840411540e012980e03404106014ac03802c3c0c0403003240c1c2c15070701c002000d00074070307400c00146d170b5001c1610f01010014641d0794641605001505a900d0b000d600005440028140c0c580900031030f01c20350503424030541c186920708981d11080107002038480c010300404906968440c980440301c440e00144030b203440e0362103010580c0480c00c0a100c201d00c55469002440d1008400760705035800c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 698525044 1250 698523794 698523797
    0x110c12130519050f27010602121926040c030204050a0204080a11280618030f060519060306060806180a0b04020109030c0605130515041a0c010504080c100507 69
    0x10360900e00300c14009406001022217a00401c1c400700340041815440e0032500c80d40403400942959458284080d0902440d505207104807142085180c0043c202c11203401c02002c020b20f0071003058103400801189001491356101d940c0000a001d01042c018052150703810359008170740400240e190740c07a90740120300c101c0c0700d00e013019004081c0d0880070171500006000d203a040902002280e40d003100c0e20680e0b03990a100c09082034140a6824005141c1c8480a50120f4400440010803141180c68030031243c000320100070903268642c00082c909000c00c18441036180796111080c050b00d85c880c541200982041e0050081d40c2c0303d140005002c140b0300c42103000d00358055101505004049466040c0c80c0c0c0401481070741402041c0c40000000341307610303c4820007040070780d407110349034070040c4600c900d05440c0e9840139101e641c0b201900b045001528003298215140c00280300080340070b51114040a0040301c003074030495480c240812050041520081c200c000c85103080d5440741100342c10900c101c0d042582c6040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 698526294 1250 698525044 698525089
    0x806030712020307030228050a03021f020106090e010b04050c0f1909081b10020c011d150a030501381b0105010305011a06040e0a110c121305 62
    0x200d681d6020344428114005801c1d82e69154503500442c20404480261840054000c107445805802c03803000440600421500300e0891407843d00000d420146006000025119415000b83c8650003540480020700311a0024408100030b00d41c41d600070b22580b095540150300f004006494000b0740012940d04064941e0540d0810010303403a0001c08001c110a05002d00000c03040c0400d20003400c000302603000c1c10810040802449002c2402900020819002d096500403400b441150b07030800b5100c4820100e00060700e04860941001541b0000c2c00101940c800c1d000007489132442d80d0540007181603444e00c0800080089212600300c003004445000010700500040c200380700710400c20b00400704503040328420006408044112821240700703900c00c42e0240e6580752200307401240f041705003201070b2045410700c0c02d01c0d00c0c02c01c244c140458000c2100f5001d41e580c0c50f422080180b081c0545070390b00b4081d4203d40c1c203e003112003035a8207a40100c4240b1040480c00000003035501d4a45820400c11343e0501684c03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 698527544 1250 698526294 698526299
    0x40519150c020307030506010e061333030b010b070c0807060c1e1a04030212131e0e100806100308181c08070b1006081603022b06050108060307 63
    0x40712100380e00e03081242d041c0a4080000045030041090700d010b001001250102030405504000300b030030503c07044006c07035800c2c40c46010440050500b5107030751107003040c007004410141c2c900303a032014115600002c102c001c24030004180c2a00c841c01510b0324621030300844601d00d031141c094555a0015100b9074001495140140001422096518012210516041d0110307021035a4010300051203001c0385079540343c210200310505da410004c0a0800241032a40d42c904079070091103a0340ba0702d0074044c400040c40210f1118001c00c4180c5841402041c07003115924030b5040c07400c01882c212714280329000961203084082801d210304084500d04590717000340500d20f8090602c5060640480340c1c010aa4482900866001c6440c4098000c6081c80d200d00202643c03280c444c90030078000370340a02002c5040109803030500000e9007041450303030000e040c854a14400e68213114210064032a1340560b400205500710b0640300503007030344801d1014990100c0300f44156520b84c4011100d902d02103032140d501d42c0c84039408 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 698528794 1250 698527544 698527547
    0x1120506070f02100501031401060927080706140f06090f150d05160302011407020604230d0f020108091204060f03020c0a030c020a090c050906030a1b020304051915 72
    0x50b03914100c094010342c0e103040c0005030404e0403100240c0c02030b40c0c0f1410f1000443c84078082071140c4e00c09400711600400c105480ca0050007121040320341c00490704c4201569400902c04498103540030203038804414018150764070916854000291540c50310b281001005c5030061410700c1a8a108500c155094011a50782c842c0d8603600c100643c440c507170803628103060340020074000e0107440040c08120745500d40b0b151071440014615403030300c80d00c04c5500702c044c000c48005a50784000ca0b4100c64807c04031070071940104000121104001603825808421141000c080054198801644900076201c01c44c51307694030804680c8403070780e659011280702020401407140b0740c052200c0d414005d51500d0014103140d08807085624001c4052800d0b004601e6802c003071011890100c01c000c01820f2505000d00040c401c44401810742e000706548a4410f410100000c1d42c0040ca5500614503040350120a810544503024040e40f03d620901585001c0c800100e954000c9182d098016401c40340741410360100040745190 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 698530044 1250 698528794 698528807
    0xe040206070623011a040f06111203270a05070302090c04050d05010e01050c120c0a11190519030e1c0b010b19090605121902070308040b0112050607 65
    0x1c0445001d50b0f40c0d9110341081c14843d00e4400d072550700f00301e0041c45505011440c140320000c00d01602c14280d007000240149047c8041031000c43e0514102a00e8000145407400e0500791541e0781003030600c4000c010041190090034040700c000c44001640c04d491040c0e4a11207031140481d00000c3d0080c2e22a00003040142400300485a0284d1000150b6051640716800190741c0d0760001c3d070541ba030b42e444102c5400d6440302841550303001002081240d00c1c000c00040386031560980100703082c0c841400030079860125809500741801e490465403e550b2101c040400f402040d00b07040106889078414448080c00310324543d450000080d0700368440002e40f101000800180302000280c0c52000c041c81918880011036a00700d4902034100e480d030345a101c905883c0940c1602160304104403c220345401d040141d03a42010403181102c0b840000d0b540a5525039240c10020520105039141e010302c006a40818554821940c90080c0e00c25094091203983c0c0e4815070b10720242005000e8540e070401808514440e01a05 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 698531294 1250 698530044 698530057
    0xf17040501063b0f04060b0f0a06030e100203060303090603060f120d020c1005090d02010c1707020f04020a080c0706140c030f1b030c0901050909010b1306090e040206 73
    0x40366aa4880300280c1e08882400c03400c0542c10680a01102401c54890450703060300c8464803c03030010301d0300c0148a0046003001c0e00c080d00d2555a45650241615400d00346418010007424004919035220750040044c0a2148855054080e0311000d420100850080b00e0055400400441c1010320355801c2117503560001e406151700052100100140e41c95090090348584040c00c042c1110505802002e400c06407100e81040c80341901d40d0401c0307003054000e02503170546501903441c01c00340459840144c035909403000001c1d10a500c00100e40121504500007800c1c40c81c030903510003d14a05a0082c0426405440c000740f002c2841400020f4801e07041401034402d8600400000c602c260110440ca50070b0003096401e00c1c012000082045142d241c84100a90048014a214200c40000801321406800054260380c041080022960510b0784a87c0940700d100c20000c0490003156554030183c4815401100d650514075040c8000140d00d1380118490412503608400d14101583c50b0344c01c000207031303100c0c0307 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 698532544 1250 698531294 698531303
    0x302031c030f0f05060108071106041205070204141801110403080a180806042a141810090c0f12022a01050f090d0e09072703120f1704 59
    0x764904145202140507882264900709000501307400c0240c0010b0a103000202081c090200340040e042100e207000500715440780d0030225402d8100030448045403544035011000e90b11604000041c440c050004c0b0525000d102024174034407152680c1d4003a13500741c40e110071030241c2c0410103000420100e00f003003005045030082c5107410040d51032480d504202c900247e070400d001c43e0b0f014070100000c218100a401c540901e11400c2c0da12203a09018084083c4022805a50045042c18041405948030f40030240c2d440d040294150000e071505002109054a03e4410703c080701d8104102d0b0380a050041c00169505203480d6655900e03148040c07c0540650301c45c41c12030910310032440f100e03460001c150034902074269940d4004a07c0341014906071341e08200141030045103410054071110b030a9003001050464480030b80701c030000340e50fa00d0826209c005503403485507194001808040c42c81741499001c032040d42e201d2800e11901c09008482101d052007002c1030040852510b43c0a1741c0700ca610414401d0707020740f20b03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 698533794 1250 698532544 698532551
    0xf030901091a01140d020609010e03030c0f0609063d09050c1305060c0d0e0a0806040c0305070905012105010608031c05060411030708090109050d050c0114010302031c03 74
    0x30740d0b881221208098040151041490700140540382c00300003c1160440c003259405940301464001403120311030680301ea4184078201880d40400c0d1014025210345021900035151441490380225446103000c4414442c1c5000702d10019000380741240c0d4000704200702660f00d1001072660700032141c01c441480c442c0940f02c0390300480014900c500d03020301442443c8a00da665110600e0404500c45603807070f50030007803080506121880460300d0000b002d1f007604405207810460b6440c0c3c0000705c2d0200c00d480d00003c9540c0958010441400361140d20724049078030603411214481e030f5690f441d004880080c042d001e0915002e05c1c594010201c00d0950710a924080c1000041013a40c9584007851581303c03c460030807074103406011284500103442096485207056030309004402080c00b4020280c4001800d000601c0312280100e242c1c4034003540503072070196010084070215280c0b5500607201e50800c40110303000798200844021600d040c007100364103c82e80030b0000d00d41c0e50456411901c04035031043d58203041542c0c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 698535044 1250 698533794 698533811
    0x70308070c08030408090108091b010e06090a1d1501021b030f0d09050a060905030303010626041a2d0a0b031b04140f0c0315180a0606090305030f030901 67
    0x9852000f113020f05d10403003c0d00d40d184090000034107404001025800c1c3d98200c01280c1c0340d01d0f0000b00000d140000309181c000c1c542981d03c03000520900400745060707000040c06101040048140070611020302000920b10360660343d49041107004c0c05010b4100e401600310700000c400c048058840c00038040d000500f07940d02010100b51047c0b0701000459160006154a02c0400541c140f0060103c05089540340c811107039810000072a035240b0040c4502d0040050040741040849000c1111050350b68800c040f1030403904043c00c03c480b840c49c50081c0004180c00b440e011640c54141c0d2903002050a414504050011050004440303c0990080568030280d0721100301480c255010700000303411095901500c52800000014032084844044609401d640090103000c00300101d90a001d601101814660365a903480000c100c0311004114071081d005078402da0600c07100e1a1100140d8880c1a000408118890b542e150032595034900344070280513a0001c000e40c1c1d0620100c04020340d406407600001249000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 698536294 1250 698535044 698535053
    0x130f0e220c03200603101701060617060a0806040533160e03010c0206090f0303100b070f0c06030b1009120206031e040c08010e0c0105090d02041d0a050606060f070308070c 75
    0x5100300d540c05004140f601087c0206d8148004a00200b1510b8000300074040c1000f0b00a0124074440c0c00b56040640400001034660b621852b070306010301035940941d5a181400c1c60721965404600140300102d1b0407001681c60026208184240c000b441c0b80f00c00d030065100d0084c0072202c418001c010b04104150107040e0b4007240c03024040d0021440c1617900800c3c0900d01801c243d400d1904155000006420800612101c115030028440c180d0f048080d0f90307030b40e45c44545003010105005160003840c112080e0070001d1400e40503800401c40d02c00543d01041c1c0d2800720601140c04141e2030040f00004c84180504a000d810002d0266521183d0384031005080d03100c000043d44c1e1003108450031200ca1042040070700c0b02031000c0c0500400d1100c0310000300902e10113000040d1070340c000c415040c1e005400b503440190a40d03030f898001140c8403911031800d401e5482c500d802d6a0b183d0040e044c040d90a07100700d0380272507a1401c000d4112681e0342a03810007103040c032170156021030381e5600113800c1c2d00820014091000100c0d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 698537544 1250 698536294 698536297
    0x309020303130602010e0d020a0311070932160e0a03050124080d050702040f14090d0314010506040b0a020312150120070902130f0e220c032006 63
    0x1121066480c60102e1803c2002401c1d0b503c1c882c0407203241d0b0465094004460340014007804100e61505110a804040e151454130b01550390f030220143d241000904503281c0c80901114a130700b4115221410321020341184000018020380c3c4615010a0b20b8400c800c2c024891000c0b4080c580000f840100702e20381d01c1e151542580c3c1c03c0d0480b0b072048504c00040560b035400907080440109082c1c03014081d04082d4440c054024003850780040d003d280c440049071100d107010384c0720700a80201104241078604100c6640e5580d445640807107808203113420700e44c51b94020038040c0c2c1d50481d0f200074007107403070a81400032000306c0d90000c0303050505521046c8000580280701000c83c1d8460314a41c00c100384032010072400141003050010404c4001146860011200c160114081c81503950081001d44d9510100030308216201007940446078001c03403118049249030045103240e000d92403040d000145110004e01e41c942c18003040c1c0c4000d2600b813900000704000f07080b0440079207200d00c444004c1c0c0110806003003c210036 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 698538794 1250 698537544 698537557
    0x60f06090405010803180a0e1504020d050718170a150b030a1103150c161416090e0609300c030a0306060f1704080408070816091a060a0309020303 64
    0x40c5e0b0808101c4002d00c0001004e80701000741d0444c1c80b0503650740342076400650440041e00408407011282250002c031b4440350100e40790048444020403141c82d04280c020405c070285a501c2c001003c140d4400184203400415041c4905240da001d04501c051640d41d10249046030004c0c6c01d08603440394031514041d90140140e01c112130040f0358440c400d00303c9000f050b041c0300c1d0400140c4c014070141414000c906105400b0348500c1100510b03c40c000c002c041c00d088403199aa281d4203081e03807045005440c901d402d07400d0f1210032280320403018401e2a5140704504d8507040100c40f01d080561140420341000c0e00c0034004614203400d401d0303d075000c01d1060500c11890340c0c070002001c480c40d4400100c8050311076040c410000101002d00c2c2202e0510503500004019a801480180c02c45001c4408502071180b030000301d500500404003140c1d5461f94030900280c4070b1550394241c0c010a03070803804c00a0395001500910f032071210a642c00903807500c950b6040200c2074200e840010209543c40c030000006840c02c0005212 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 698540044 1250 698538794 698538809
    0xf0b0144010f06031b0e130f18061b02150a06090204061e080f0c0702040209030109050d0801080c09070302280809120715090f050106030308040b09010c08060f0609040501 75
    0x10b02a007004000350640c1c0c22000e2403101d521020120341900c56001803100b090301011108070010691890035680a0f0021840340511103103042c4040000c0038039006d809503071912a000500c40124041d000301d0300c20355445202800340c1c001000a04264403001c030b65590041c602a0001034860325403c80000301e0300190403a40102c0d002003010f07089584ea1041640303c10002d86040711540c036150300b1441001a029102c105204808500314003103698980640712103c20140003040501240d003001640d480310404414080f0b0152400411005004168694016400750a43d900f541301e600d01140250702c800503c0420f03d4050344800c4c00304400004001c100240c550f03a40c00da60400a9200d41080030724170554200450402550000a410310a040d10102081c880003900151a00305540c4084400b840102036520b0500003000301078110390740314000c6000342815801070740c1d0504440d080350039441c0d0040c01b1418000000d8180c0c5804001c1041f01c0202030311203401c1c2009900800c0a4642c282c20203107 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 698541294 1250 698540044 698540069
    0x70b0f0c0409092f0a1a09030114100503030a020604110a03051606090f0501020703060f1d0a0b06010314040209070e0d0503090f0a0302130c03020403080d0f0b014401 73
    0x1050410032821342d4250220100140f52142010000641611014465040c2e401d08100d69818102d010100341c8800100c051700138170101889000345104c0400c2110300790f030101c500c00d202144500300001070700d920740b100b40c00a08031600c981e00e50742005a4010040e59003c49020300100004109001402c02010340b83d0050318510304012005c1e100301d010303400a04d0021201c06007081503a80c00100003040b6500080700140b440c2e80c02c22040094150b240030380d5205802840101e010303c4001a50440c8a40100b101045584070000118182c51000100c0700d0a0032221001c100940360a01d0416000301003410004401c800703800c007181540d80c00d0001078900e87c20200d00e0400ca0700300090546403003c1d003100d0a9000301c1c21980040c01c0d030040f4040c0402010713a58441c450402e80a9411100510b030403040c0e86d030b00d40c50341d40304034005441000400c241840c1401041441c0d0f50044201d1151240b4600c9090385030356101c80c030144003548948160412802120030500103098458005000e4403c150107031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 698542544 1250 698541294 698541323
    0x1e0606130909030e030c0102100e010212040302070f08070e060f010221130509040515070306050406140f04110412030212070309080f07030809090702100f05060114070b0f0c040909 79
    0x42c2610843c0442c43c5d009821410115a16a80c0414007601c116400c0b400083c600c0701c061001c50082c01040c20459100c1605400e00080c1500090400100d0340e000692403402c9440b40300054551402d80b06004001c00080041911803508c0501d042884d10188104e0301141c01020f006c040402050300c1d801d0300310400145200c080d18004201c40701504046c0c03032503482c50074143d45a52350342c0704900f2020741c0845014080354071181f1a420007030090a00401c1400540d882d014800c0401d01d48502d6144a07040c100d9250f10389082c40c0c01010080700607540001d040c94640354060074080c040703100880860140c0036441c14103404e400c0107020b0840c082d80d10280b40038200000ea07840c0042c1d200c004401c6030300c0810b041001070340c0601101c00d447c5c001c1d102d181c40ca49072a82c0680c40d020014240c2e41c010381c104a0824071403c00c641c482c0c0d207c0d220076a1030303000109c1403200501d107500c038625000c1d2000456034006045070110711100768204240c14032992605540312400001c591040004556050300440c04 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 698543794 1250 698542544 698542547
    0x40303020f1e0c1203160503060a030c030506271e07030b1005120f1c05190e0f060403110411121e06040204060c03120621050708061e060613090903 65
    0x161080380b04d59032606483e44c180010704c0c1988904a00da060200300000000922031744652900d00000c42d40321a68600e2142c803842e0103901c030602165003251680344c00c0000824011558000c03070450b00c888014121004680f14006e8401c401c91504040301d10501800000058403c0e05e22440f42e06144503145946062004110010004080c0310000b0391001201001020003c0784030000445444030f00f400075071180320300f070324203006001105592140146680103000e070032a46103541d09604450304145070004d00c1c1088064000e03804080d00b03084042040c00860f0070198025004455841d6905042c080303040b5000b04000e408560005060804c280420320940500c40d0b0b03e80c03c14404c46096060505204004011424828002d420400c1a030201c40716001158818405010b0041160344101054415074003074007008281229140b19000c000591041c0200354035000303240200600c008803103480d081c00c1d54103e0103880305611603801c1140003a102907c0c1c000c3c20090850500101d00343e14207040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 698545044 1250 698543794 698543803
    0xf070e12031e0906121b070302030309210a140d0e030d0c0912020409111306051309230c1c140c030d0c08041e0f170303040303020f1e0c 60
    0x2444401c44000f07103d007507810b6413040c06803800d02018002040c0d480d0703100180558400041d103114040c80e040081c004050507800310085101e40b42c0c4004482045d40c040c0081d41d8121030003a1a20602901402109a500d12400d10349100c282d49900a50038003440c00d801400300c0700440c1000302a40e05c00519a614806580940c0790114042e0401800c1c9602d081052141c658800500038031665603810108100103602400914115014103940b402e40c2560141c2c2004016900940744141c0c032503210095180705c1801900d070701a038841d485085103c5218962000108168940d4445002d0031480307141940341d44484ca907034121412001400c503401c40c207289810243d503803641c0e1825044144c1c1b0b2090303502c0010300c02c007460881d441c00d00c0d481d050700d0418001c0d900864000a04041a410a8402c81401e5008206c25900c01410108486030b9540042e6041c460002d42c051003074005100240229010794090019250b008401501c1d00d4250343c4016408141120580d00c201d0003ca4000c544440411 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 698546294 1250 698545044 698545087
    0x4080d0809070b0f2110090b0d02130e10020c03030a0f02072a0f090504120c050a1b1d16030603050c0d02120a03021020030f070e1203 59
    0x900442c0d41041c81c800e0310ba101d0701d1000d22481100145504180286001c01300c601881070925401c40e00342078010564070707440ea200e1105241d051901e006103c0c034100000c0c2c8000d41e0300a0070509804c000340d03460000b40503d5404c100711402240501046011540000c2c5107aa1502018599a2400c044141e041b40c0c41d038218041e40f68814060007001070b04124030004400d0a00c801d0308542a807070000c1011500c5180c03c4040c60424210740061120800e402043c080c07481002030a444500c4030504903401d8508200240255022007160000700300040c508080c1d108000440c81c40381901c40c50700407103d400b06003800c48011541000c00c5540d181d81c203a102550b100f10f00d0144051891501d88654074005072136158807451542000d5030841d56182e01078804c071005142030384e800300c0c110b0030007035100d0020140500d000c41c1800942220103010a10b40c08000290818503421a15003400191030700000400380403c2c8294002c840348070340d803243e21000201075444021680c1d1050500041c080480780c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 698547544 1250 698546294 698546311
    0x2060307050306100804120e2d0a061e0c0201031d0d120c0504062706091802040513021b07082103060a0302150909040804031a042f0604080d08 63
    0x128107020028040c00c1f01d515840303425191103ca000350b0135000841d01e556610300c1002da0710101040301c42880e40e00c6132401a0001c201d0740c820f24190350380802d03903a1f20b541043e000252103101c20319041c0540101002c5a1940c010b14002030140d01c2030b042c0c140c49400b4110b44c0842e0ba401030601a41d0360b5032040043c0140c1d070030081b092143d003503031010140c07403402540900c10600c50000703030b0146403001c0e40741c0600713544201c0e040720000c607941c840c2c02810684143c040c89a90f03081c3c0a0080a800100d0b000312401c0350b0010f0300315030030754501da0415002500024500c04098a44112801c0204010840c56003c2d03d121800307012241740040c2c3d056441c06c007009040d004100706204004441e0744603a624000c0740d0301510303219410441e00309405007520480300000c0d8424280c00900041c001c0303050280c0140c82c424840401071400401820300c0315030701240c0007001040001c00e240110110300204103c10f0200001000340180b0034000900b1b41d40007504204426400200461001580004a980c01c81c208 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 698548794 1250 698547544 698547557
    0xc0621040501140f09061305060114011209081309020403030c060c03150303020c13060e1f0e190b0105030603120c030904020304060c0e100c2402030a0903090603140a0504030504030206030705030610 87
    0x35500c00d27444513814480c01c0904240314640e09600c3c1d00903023000407000c280030380800400ca142e240c03402080c0c100383c02001034258600004038141d030252089400740c0340c0646403410b800c4401e0f6542ca0250800c47c100c4010140c5403544d041034622582041d001071440ba402030310003800200f0500c10542901515083c50394103010040041c20b08103000990403510110f0b00802203544902d01542402c020307031101a41c1081d1500f0441c020386048049500c2889680b802d010f2040c0da4001114075000c245c03100c0d030349500100301d46161400c80314000c060100e80d0742c05480c00d00420200140807070300111002c2d280e0780e45544802d0307580d0381c1c032036121140303031804444001d05111018001004480c039940c004209400c0400490800c0c1442c5100005507040c0c103106550743d29020000300081c000e011411008680321301c4001c1a114068044e400d14500d2150054120755200e0308113030041c1c00054026001d0103020000070003da1070303840c0214428445c60310f6103607580c1001014410090036541580381003146 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 698550044 1250 698548794 698548831
    0x1b0e03101406040b060702060a09030b2d040201020f07080606150c0709051314150a0c1d06040b030c0403050d080105010c150e1006080c0621040501140f0906 69
    0x14074414050b0041d006039000550280e4840214045121307010021703520000200e05121a5940b040740c89042e07d00c594400032203511401070350020440e24801d40721b50152215010091011342e0804c180d489401441111001c003203494509081c80450303009840c59411407002c002103400e2154090295100c8802a640342240c00c1d000340d070701d65185000d00c0380002d40324004030710858540007807010b140b5080100010001844224996a840c08800700d400c0b2160100014101c03031250301c18405241036175215588044007842c440244480318800355030388a034041c40041380856191000c4d51040110340007050f03440e411800d05a183c0000d21104000300031045c2c006000c6030749d00c00e4808070200c0e80528803896500d404c0d00e0b444058a100b83c14050144625101850070b903034503400c440100d81c049816243e803500981d0501413284260b901e104200026040c2c817030840c051204441c0d60181c014000002d1071820403071001d19090040d500d440310403101c202808803520040c00500d4201001014141c40c402 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 698551294 1250 698550044 698550071
    0x501080327010f081008060f041a060a180e010c270b0d11090d05010b040b040b100804080d1b0e061e0c010b0d06061502031e0a031b0e0310 61
    0x20b640c2c0d400c00200b244d0a40801d40040940d14203e02410b0448150f41d000d15040030000f0100380202c4080c0d5000310600b03816440d404030300740c2e0580540c40207030030002c40c203003420921111840100740d00c81649640d101c2040d0340031000e124140c034000681d038640351840540a00360081c140f500e580c00c86014900b4030100036485004048980042180c0ca02191626141562081c00d02404204582050840400004100c410360150f1200e80b000c07642000300341c0b41e074000e110407900400d11541e0803100d00d518201e034040c010710115070b200740b095003110302e030400040d0180300360340428408410f003400806040d800700341c219544515406007a61114200b4681154600c0c0071990410b48650912001901b00c000050a40020700b100c00f0203018603132180c1c2186089401000302d403040c040d10a508100086400784080304072030203030710b003004140c010103a001c0b5040c40b1580079800d084140b55071408040c0e003a080400764071a4024035500e0703c41090303884106050074000300c400252002c038034004d8000c9008 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 698552544 1250 698551294 698551307
    0x30c07051e3906160302010f051021020a05150706110a1d13060303090801060503061611150f07030b01030e0a0303110909090607030c020307030903030f0e04050108032701 75
    0x20410b1162054401070003000b180d158842c00b100003840b10500d0301c0040c20316805400031240080d00501c100036541e5101460f58855145000c1c1c0c00248001d03604d90003980c90314000400103070b400281001e2003199504001507280f040c62054070300c003001c041790318424082c8911400e00300719a0061014a0440d1a201c0144101e000c03202c091390195000545000c60b0304c800c012440f20510310201000010f03243d0901800c007007424070840400b582020740200302c5003004618035000b081d540c1f10180d40b8011600d426140b0f01d501c100e80c0c20310ba11a0100a02a140c0905941c500455241d4109455400c18100080c16103c00b048230a06050406103641c4049030000342a1060942601e070015020110781e82c1440b0074850403100729071101c130000500c0011000420607a0141c445910f04005440c0001c000340d0b140d01070b9000240100b0510f03041000460b029000e841400181841c1c002030303607a854400202295800c0c0c204214560003c2840181e8030794004041c030003c1c00c021441c600c04082400001c010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 698553794 1250 698552544 698552623
    0x10e1f11161217161e0504170a1101051b0a060e0d090b0405040e0c04050108150f0c0403020402090d02130606030e1f0e07090c0507030f1d06030c07051e 67
    0x1d03810b0302c140c41004d661003400b100c0032001d610070608884204503c8000c0080c0c00c0341c024502001900300480034203000024441c00043d900400f88404030602d0801501d01e5008401c4030601d103403501c4600c11404006000c0c1031102841107030001440714954120914280d1840d0885040c0301d289141845012a00801c0d50219201140c020a000001403080c6003000c000070400741d006400c0c000040f8402c080400d80c4014144041140080c645c1d17210311b00403440c0e078140e60388251442c2c100000e202600346500140710708100504034590005003030380803820190352111301e441c0e41540c1d6030050180c01d506000740d00d2459007060050646180e071001d4010b8500403158a03002056860a05108425043c09440e008043c4440100b0800d15030190280140e8081803040740081c24075403042180701d001d9541840504601c0c440a441c0080480a1200390b90010b00310034100c000600c00f070f000054082100600700481440c122009580c4551751500c0c0001d4500d500c003145101c50004824540c00354900b0380c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 698555044 1250 698553794 698553811
    0x8150c030421030213170d0203190e0402070210120b060702180403030905030406020d0e100210050703113906040b040804030c090b090603010e1f11161217 68
    0x700c00c1c0700500b068009109184800070b0250110900140341480d100200c09041c50400980e80b18100c2c0610480e200d215524590901031076894003000b40522810540c0c003441009480145005c0042d0005100342c10207011040000f5060031501d4000c040c45d00507928040020748000742000e2495000480e05803600f514036041029401c009018940b2a800581d59190040d041c1d0399113613191800292500104001e03400802c001c51240401d0703040040c03480c060001a94007601e121088556048040d00015084004043d16007406a007503e610600801c100c4521900f4602041040021010342100a1155411006001907609079050b40414010390203540840081041c0c1d440d40382c0442039024982000e8040031340c3d2000454031450a5100d0100c084040b21002c000baa1503074101800d0306d416001d842c2d07240e0040440712160f0b00100144405109008a02003569405820950b601d500107481e883c0002007019504000d0001d04290340f4180641c0d4501610752501c0038610105291001d0130588 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 698556294 1250 698555044 698555093
    0xa0e060a0605030a02040504090f05010c08100608041407061112040b03040f0302011b0f17060604140f030f16060804050c01080403030b0301060e01080d030905060c070f0c08150c0304 80
    0xb03500200503411100a1f04004008104c1c81003603007010189500c000300c00f107440703600e4038000444050040781c50900c1394411011030142e803070600b042100c039100d010308200c5503006601c1c10503d8181c0140100800340c9030301e0b07440b150a8103034040300721301d0702d595041601c50701c0101b000184141c0c6440b004596001d07806c5481d54401000515040f4010494440496448c402d090003841d000c41c2c2c05401e80d59046034580d540e0f100000d81c03440c5001d000344103881c1668046010401000724020b80036011076806001840c031511003003858042410040071200c0680142c100008100e030000000c03051001820070391805030030310724169603001e07074440c519018541401109400502050b00c247c1044560030030203402072124655a000341c03000c000c8207006140c06030033024210780703440b8802d20071250407540000c010086511800864072075584620320a44d441c1c9440d90355040030503c80c031580c0005200d904024038441c42078450340396100c03034060f120307000002e002c0040c48082040491007180607180c150540 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 698557544 1250 698556294 698556301
    0xc26011a1e0a0815060c100b03150a0204060201060b0a09180915050601030605100e0d050c1f020c010302040303020303070806040f061403190b0c0c071805060a0e060a060503 76
    0x5640068180020822840c001509405554080c0c3c1c158041c559a05401e40c1e000754581c01c01c4054001c2c0e88014000c0d40c0000c8150410121580001c290404060290382506450050a4101002c2129003000352500000cbc2000306682c24418000108009007880d4205640c222005040c0740c280e110307420b100d01c40b0343c18a802c1501e2640c840d4500560080300c0084012044a1b0000a0a03007200c000380400d00d03004002515080c041c1c51140007070303219a982c6500d244200200100f815204000b9541c5208504082080e80c40e01c0c120020703081c002e08486121200c1e003060091070b0588400c1054101401070008200007a000419250005582d040055032696144041340003410001c070005615410f100f40040c45102002c50b440010310b007a8240d030f00000310005504003410400900916080c002d80000c0c413a90f0280c0302900f031a1310f44200366921603075250707041010351400c0300b500510269030b0014056070b441c0c83c1c492140142810b423410201803805030001503520103548500c405015000000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 698558794 1250 698557544 698557567
    0x30c03061816140f09070c060f09060c121a010c060c020c100c03031406090c031504051008061608070c0204060e0709170a0803010b070212010c26011a 66
    0x141201680c1a161100207a0321086070224000050b420f0740a08682d00300400350341848502e007441a41561181c11101c5207950710003004007080b0f071903101111f07906c440080c000f80703c0340076130040e080c601d40e82e90b00c86003503400306101194030407941c074208201b13510803400d803d03600300d011000402d070409000100e02c0e1080d4007c1c0d00308090b0405c440d074003141c2c03051140115600310845e944558080e0ba02000002490040d8030900e000544045a00031070450004001020490040d94051424040320300240010000308040d03270410388070740005c6d038000c00041c40450001c0001d2a880850078044c3c481c074020300351024040c0c0802030b00d06800c00020f0141c5c0320654503260096401014400d21042007444c0c070608c0280741c0d5034180100c1080a01c0e4440c001103004002034110046038000b400289923034640070f036281c6240c0c032001c401c90b009424601603004040c801e03c14520084419100c48910403160341040c800c1240c400d552400d801d0040005016803d50030602011101d1450040c0d903036803003280e00707 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 698560044 1250 698558794 698558803
    0x170a09021825030203101e030615090e0601091404030e010e0109050303030c030a060f0e130606050904150e031806090118121e020105121b04120b06030c030618 70
    0x1c00c0c5120030140b0b02c1c0d801180c1c1c154002c5110f114841c4003c070100d034980c007411072088007400400c8040d0398840c80500200c0d141da841302030b40114130780c3d00c11441940c446158080d00c178420502103180d00104010400c2800c2d40c01054415522000310075810702e000d580c007400407000f0702020780c100503401140f03907401d902400d0302070060f0000030212610391500c0200107000b41c1c02250360b000e02904210001410080706101c28060701d800303909080c0c2036542ca0f0b1100e8102c19484905540c550b0326181c001419844450b1502d000301c0c02103811354840598000d015042d1444e080314050190b02c20010903c8248824a0a04401c04116000303a0740f5103c0384012030306c81c855500038401c003850401001801408022841d10f9651050803c12010f9000203a80303a0a220041e8002e80441c00c10040080602e00841403a40c3c8540354410524014a5080c0a507100303801a030001c4c6101446000328806011041e070100d0b5008030218001c1501c07814030b0003ca5115030307000d01101d294000488040528000500 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 698561151 1107 698560044 698560081
    0x1e07170408150c13060e031b030a0305090d291018020904200904050f07020705060f04270c03050f0c07020f10170a090218 54
    0x1c0d52256542c2d4010038500b4a401e00300300c0030400300c000400540c060080b035901d0f516092990742c00c0c9850f00644000300046000e4210340310250750303000140c208549038035103030154480c42180e01054595010b204010407102c0f40b08070340394180c1590100ca450280304400002184d803101400f45844142601075151100c07070203811446180c40e42c2e00142000b0b24060b10001d151821403020b11a000e000720104034600340300003078044c0340d45000c0c050580c018821000710440d0b403d2909000c1c0d51000548542400b91002040c4042c070f880785802510020081040c017000c55103517035a210b045055459017100c10b4280b903c503030180700ce842880343c10b01c2041103841c2d101d0355440395450003038143c0140200320b900c481d10986500380d40e20760234400d4040003030310303112034582c0740340d114000420060007040c3e001507d282c150b0400143c0c1c0d5541e1039440350040c96440f820f080c1c8800b1040e28860190a = true := by decide +kernel

theorem cover : BRFrame.Cov 698381294 698561151 := by
  have h0 := BRFrame.cov_init 698381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 698381294 ≤ n) (h2 : n < 698561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
