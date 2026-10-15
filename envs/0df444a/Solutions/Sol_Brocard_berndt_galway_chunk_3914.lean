-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3914
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:02:52.400192+00:00
-- url     : https://prove2.me/submissions/c8c17ac1-0a1e-4c6d-9ca0-e693f15519f2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 703776978 ≤ n < 703956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 703778228 1250 703776978 703777007
    0x509030705011d0705060f031f120503120606130603020f091c03020c010f0f0c1103030d0603020f150301090908121e01060509010f11030c1006090b010c08160204150e07 74
    0x40400400411f881142c003140e500104c40404101140707000b4400f61800d00301d030b402c540c19101031080040d0074024004081c1600c01c41c50085a1026a00c0700c06109441c012142400045009100f00340308084c0250003801c03024820a01d20307800c2150100003d81d0000e061100148114481102d00d414160b05000180d060070382070074102084142407500503d060781c0800e4860402c4801c00058080084100c42c0c4030710230300010101c98403506c20b20340400c000c11007480b08078891802068810722605082c1c4000a4484186040504581c40c1a080300007526445804951651041005200d05801070742c0d00d60281d40382d90694003446030401e0303158880d03040c1138002900740a0305010f800741c81c4c3e0f0304c0850718000003040d00c4c0030b1664100d2807880a145019030b403000020740c06285008014002c2940c014812107580e044144203424040d00192401200d852001d052454100480140203491032140b031030240c401740002607608580307503012201440a030080741440c41c2250a000c81e5590100000340c0d40078 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 703779478 1250 703778228 703778239
    0x1b0427021e2a060103060e0703080408010e0607032f07080a0507110d0b1315020a050a0912020604052403010b0304030201051b192c150405090a0509030705011d0705 72
    0x1907500760ba02c0d94440051000511031520385507442407001091103408021540705c44440d840340e85400d202800380000182e104402c4c4205400034501360f1190042c809414203a00c02034400d0401425411000140c02000407080d00d010003100000440510090a425078941d8515440380d40901e0800300d000d806130341c420310a01103102c9010104141000c0d0640120084450080394246803034060803900b2444c0d503505d2024404924406141d4012008051074091560391944c40e5131614111b0207065003003403019403c00c20a002c02c0c0070600740382c00541410807001c0301e40101a0280e0642850310390091f08009400d0f41c02006100030113409002e540c2e00100b20441c610302d0500101420480380c0191200d2480c401808924112003c1c0108600c46050003044c0c1030200c4040410020202034000944440c001c2414060403220303a00008241d400303603400140028443e4030f502d0311400c040c20300034140240c01e00003044034400184007449181052601400d420803100e0b0012885810181542d00060261 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 703780728 1250 703779478 703779547
    0x4050d030203090303010e0406090507170d02030705070b09150715050c0a0c03050f121e0c0f0306010e0103020c0d030f060503070b1909030203151b0427021e 69
    0x481012040d6811f680d000b45040b280317a41c1d107003001d40103801441d01c090320070b0144100100b101202081c1e1080c404144004503818a500814100e81e00c0c46030b01e401a0031500040f20501c003403202c04005201031080144500501c601800c10300c426a4001c11040f55900101d14010084071102e000b200d41c489442d46545d42040001c2070080c00450340403c0050805c500003a001c40c8400b44d41c8162030031450340502c1c4401d03a02d0004250205403c0032800b0480c24200c1d00c0014201601035801c07a00b40070100308165046417500300041d80c41a02154003181816000d0009251801041080c62600ca030300e0380d00425410f0301c00340f000c0304540c550340020340642c03c81070062005a54441c1260041c0d441100c0d10071044640080c100d0358441c0741d82000f54180a0109000030188100c80700501500c0405e204010800e00c00c800a540741c030541c4034000905c415400d603201405c10808400b01c008a003080f015190440c03903004130342c03c100c40c100340c00b01a0fa40440d40c098030364001c0a04201c0703540c010300114041d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 703781978 1250 703780728 703780741
    0x5010c0b0708180a050c18010302011407080d1e15120f02060d1b0905030706080720030a09090b0303030f040212010e100209030105072f07051804050d030203 69
    0x10314000401040902841c400031520307000c0d04010081c00440c0b01015501107059614002d51582c00400105115400d44001400780400980721113048035416140e80300d0b00f810076511209150040c40e4251100b000520400380c0342c00c0103010f901c071017a034051090b004a00744400c0b1502101e200e101e002c00e8031801007400b07000701301502d50300b1300155800082c4400106064800254240324101068030f0150a0080d814400d42441d0300e80e01402240c4d03110700b900f481c1c80f28141561401d1a204401c005240e12003c01c10890161050721030f0308518128010142d0f40c0320403600d240d43c1c402c4a00301c00040801c0c0c4100b212480e5407203043d11a5008402951a5050600c0c0c0040034440140c4049e02c01c1c07080c0316600300e6980003503010300d1140c8215000d40700c00f40c803d0090b04000b500408881070081d420040051401c6101c0d110500e00c0c0300305040b2901c901211107407020358031580300c1010700301403141c060042443d0b902c0701142d5507843c034010920b4541e441c0620302a8105001b0a000c0d105050060050280 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 703783228 1250 703781978 703781993
    0x1801080d0f08010506090303090a0b04051c0203120c030c06010b040513060e1501050c010515130b01021c0309020a080d021c170a0b0607060c0f0e2b14030901030605010c 74
    0x46070001c840a80d00c41c106030002078114820445c421b035001740c0040d4008bc41d620540050301c01c9490485461486070240b02e9005656072480300003e500d50045070440030000c41d5080588a8105034204a0f070401c420511010300d81102071700512840400404c007041a03181000691042807400305060200602e81511124110b202511480011113265103c802591080c41a16844052440280510304000868480003902030030301c180500c0580402000c40c000c076004040301d095040c0c0c01004008092000c001169400c0d00c004010180c40f28030102c0035944020504010342000000f03001107030403044000c0d1030f194a00c444a1040040000c1034000950400c003044005441003035555410340c0c569101c2c1c4010039001030082d9002c10301050441c11700c01182c0c001d602c00c50060700d5192041803450800d603540c0c40485807441d803010300f01605030003103082c1c0c034462800720b9400c0c010960320300c3c00381e5a0780c140d801c1c018001c074035250b0020425403115030b0300d4001c2c000100401c2c00d040f0b44002640d154400b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 703784478 1250 703783228 703783231
    0x503152a0d0603170a1d0d1b06140708180411070317010e010602030409090c090207060b040b011b02061b0d020303070305060910091515020a02090a15231801080d0f08 73
    0x780041007801b500800e850340e03102c100b101d40e40b14070072580403010580a00c0c6110454044c2c2c100048140709480c4100418000321106223410030030b5541071405280008014058440030301e43c205440315481a40b9062250103070020f94406c5d211060500f0118034903941d0160305a102580d0642500c00400401c0d1b00441101c0a484400b180070481400b43d041c503102c00450360f0300c078070042440000e5040621505d40c3c001c0d041d07074500316818020307034a400b401140c2ea0703120408811a00030340c00810706c0051400740000d04125070001c031200f1441da05600d5050800e03030900001c0025810000800015581c54443d1a0340500f00300e4042241d42004945c22a0300b61641c041d04040d2544c072282000b1034034080d80200000c1082c3e8060302c2206407850b4000b5210004240201d000303081d101c000c120343c5001030180c842100100c802a428035032a04181140c80c24080301556591300c1c004200204544808692540c04180c42003500529450721940320714040d05442503c081000030311100301003d600c15440e6 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 703785728 1250 703784478 703784507
    0xc0e131103010b0d0209031b01031a0a1502011104030b010e16050f0c190c06110c031c050d050f16020c031b06040e040605060a0503152a0d0603170a 65
    0x10b458403060072543c0000d01c9622285941340c03007602c0340c01c51074401c03000300f0b04642c11003030761300340001d034424420b032400e82f1f8401c000d41d507200d80d007030000f4014840c2249004100010b40d00c00411018401030080480e40d000340c200b92651554040184004501c2c0031020760002a0380e03003004403503040524001c10900400f01910032103180010032100c101d1041080500090111400f024002c040d4540000907070754a02c24800411901c04d4481d00350368001c1200e80b001c23400034000c2d184070004003000e904040f0707000d0100814082c6c01c0c00388002102d19441010f21400c4031201081c13842c1000e0300e080e241414850206021544043c240c80125200403800ca8021001040800300010662000031035a0107070780c004400c4001508100014440300e6080b082c082ca8081c0c5492a095883e401456100c452013081c00d481d001550000c141d51008040110342c02c0da4080d0051150a0040c0080c815a03500c1424034003041c2e5180c0c07101b4400e11214220000ac1c80b14058200780ca4000e04d40d00240010a641024 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 703786978 1250 703785728 703785749
    0xc070f08150c2a0c0d0f080c07270b0d11042f22030b040314090d06150f08121c0504032106030c2105010c0e13110301 52
    0x4541c50300002800d540301c905400907400c90403203450104182540d0510a59030340392140e0520070046003090f012170110781d904140f0045032030b051500d9a07010780d03004040c901c40b544103021000603460601d0800242040c48050282041022513a00d072046c0c46141d90301e9031190000c542020001500080001841e00d01564040703045032900421816540e008401841900003c20249203065640c03401044000707681c1144041c21542c034000000e000c0c5090000034a1806000e020401081c02040498000c68039034080c1d9150100383c1d000300380ca03403502c410110341460f2206079644075590000205c1c1c0c050a078000130702c03d84629110055607113400a84522050160024071501c104e00c0080042e01501c050002c00d100e141400e140042c9480061000d5860140c0a02046030640305240202801c50341c0007031801e410310781440070900a500030402d20f4051984401c1c14600018800e01541c01c6040b041c0d03ea198803038030000244a5885111440603140c0ba250880744082c19150341c00f5a819290121034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 703788228 1250 703786978 703786981
    0x20609010b1e04062705010b030702061f030c0f180b0f04020901020106051c03120c0e040509032a010b220903050d06030c061b11010e03011e020c070f0815 68
    0x440c0080c0320a400030740c2c100c5901e4004035000d170075080e00c00c0400c9082401c20006a80c1e225031b00740c6140419940b100042e004a4041820b009010828000400343c0c140d40100c0560307641c0d82c10300700801c6540403c4050100d680200019650011441c0751704841003070034030081e101d141c0000c5020f50082d801c10b1013154003007071300701c5140d200358840e10151101601601984808051070704588891103011030001c2d070100700b1048900344d28082c802d0b1005032504c4480b101c414210400001d0400103001c40b03032520052246860a40003115001403a6109012200300c030042052190f0a54045034000b03402035109003800d8443d01c1100711900c240c400007010004040c510f525089401d845031320304048249040040110a1006440e0702008940741a01c400c2c2030100000740000f906107030041e000d0048122500c41b105254000d20400c032422030020000505140480540354028050804400201f680031800c50718445040010401500c0c918440541082c50400c040303986150000c42120002c2c2d0410 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 703789478 1250 703788228 703788289
    0xa030201120f020315090106050406090b0d1116020f030f1f0207020a06020705130501030209040201030506040b0a0f050910031e29040c050603161b12020d020609010b 73
    0x5020b0000c030300d101c000566880c28800100c0c0e00d500780c6400380c64880c0501e1000010142d025104807000c0710001d480700381c3e68619180e5001003580101481441081c1c8076441e40b1500942e000040444142260342c59012402a00500081000c103c0c3d81034020750106004603c44100018071207007007200444100c0d40c103580751002d8000f0703016000009400912a01c00030900a0f000310f45901500c5003551810b250703040b202403400583e4400e22000e034020100c240072602651080c1c100f50b0b400324001c2c0c0b004c201c00e044040811701507070160740040d207921003052081c0802d250119246030011210880741441c6410750b210080e14804452403d11501001260320041041c25041204404020701c070100389110110792030b991106003110200c403a616200804149440d00d003094070b0142c4052240c0c00b007000303401c1c10700703507208490700058084030302e101544080014070701840d070b420103c02a800340005c1c1c4103080004c0d00e402c0c0090600e00311030b4103066100c1d0300c64840c0e0103651526108075244103161155007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 703790728 1250 703789478 703789481
    0x12306070204150e01030b0703090305090439020111030408031f0b030103080405012303060103020d1b21061a220e01230a0b1e0a0216080109020a03020112 68
    0x420100c580403014107000540c111300d80c0040340c100c90243c0190074060390f0b01c850071000c44540300f81c02000305030113004010407418107501001404150352175104da01e230101c49541401c2c5000074615800c0704200300200700b0240e030a000d4008101c190f51250390842c1025a5102d81c07030300005007800d4070703403071072440d11903c03188904007440080c009114200c0e940d50312424103102d80e80c06402001d022440030200c7d2100140b40b9200746c410851400d00450458403a500110f02070351050040014160315062034200a03801080c0c0801b00c4201c68a5010b032042c0c644015a2540c85c010b0354069a075440c1c41020070658075512072201c1041d2a00e0452a581c100310003241540341411041080b092079164408a049030b620504603041e504050300ca050703e208040c107034250304600250100d0304040104000c1012007801c4014205030461030041c9440c100c031404254801d508003825020060780400c0c180c0340c448000c20b500c4800713082c54000134000540d50760041019044144002410003000c0440b501411255 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 703791978 1250 703790728 703790741
    0x804090905030403061b090608060a0603022d180a1d0a090516030c0503010c02030906030601020106051302090f0603160833030114070f1d09010617012306070204 71
    0x80b08001c418140d00c1c0c03a8481001c001b017041e0200d03c4001c00070031503501849002d44034003c01081844010705110003100a50010241d4402d44244011044140882c04a14203407124408419a85400c424400102090f02d6000194002c4505000500450105841c05545282820581a81e5407260900c00340140070462000c0c140e0b00a600250030281c2c8921842801c40b4010745408061903128010142207480722158480964030410179036105040c510042e50344a001400002502591640401c15041022001d00f00007540018000602d2910014121042d1700c02d5648034210316190b00410454108281b681c2e06100050000954401d1004040344822003149610141e6441300c0d00346034001452828020f1182d420401c80503460514604828840d00081e078130600082801c1c10107851000e8203030b01009040307804140d1044240c03142c41000d4000c04040d81d07a180c9100100103041c1c401c40040c0c01509411a4042c451000007160a80b040c4501e0741c103d03601c507038652240c0b0004008001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 703793228 1250 703791978 703791983
    0x203041707050303160509030c0904020f1809010608011a04020d0603021c021c05060105010f1710030212071503020c0106030b04060516020601030203030301181e0c020f07030804090905030403 84
    0x1060410042d0100181d80504141104030300710321485841030300d4502407002c07030a41580c1300014aa0481c505002c0b0a50014005418820303c400301d040810311120f0302200083d1f00b03402c1c0c60b0600000702024400c0301e00512000000b005441b04540989010400740200188216000309555102c2047d030f90082004542c010b001040704000ca804000d42c002c03441c1d07002d0b0301c5080809605000c0098a2a0300e419032a400030283c182d5a082500560702c410820180b0320400040c0c001a81d182101c90ba100d40c000c0c9091090303d2086480c5204104445c0d4010341d40d686c01e508030ba181048035120004085a1038241810056203030010611041d00400c02544090105c807803007018002031001b141d0020340901d000001d82c84800403210400d03641c405081c8402501640100300401054000000b00b03204100c081b18007040980512200a603c0f07218005c400c070643c0e0307507040000101e58042041485c01144c10019042d050b1031521004224040c13803040381c0c0c100761a041071608210041c01290040e5a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 703794478 1250 703793228 703793273
    0x30218120d03181101050c0a082d190e0117011d0c120c0708070b040b07090f12060e010e03030106030e100e061302040b0a091b0e010909020304 63
    0x11456218550385038004908040840d280144480c1003d01001584640e1600310003c0c0b040b08000030f004480c10381c000d03080e01409000b86400200055164401070044c0001c1c091204850040d0346c210a4164000399000c00014030200509150050150b28208040f0340794103090b00c04462020040e10000c44161305d01c11900410307800850421040106c240c0c0c40005840d0051090391a051110082d20903420b1105841c629030001400052200004090040c8245030302400d0028a5450300032985003940d0403110811fa6030b0070001c0003640051488000c02650200036202881c2102e2590310b100000000342c10f0315102c40c2140c150400c00d4100c814840342604c2141d6481d0381d2000000c0003001800509500b0340181c60702040b5400c40c502800280c2d181401c0540920f417140c00c80b03c8911848500300f203030802c1d11044150581e0392105a01002480200004108407113021754442a030100c21040b0f8080c880c034544d08904690744170b100e2200362070364101d006a50752202e0500c051815601c410605128 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 703795728 1250 703794478 703794499
    0x40609021f0206160309200406031e0303051014120f030c03270a060c022b0203060a140106180f151205190f020906070b10060804050706030218 63
    0x41c0d001072151300c0390206644541c550a00781d0021810f90b4044040039051880d01c016000c0000c40d4280e0301c3c0c1c03600748000d1002514a03929a680c80111001005640360850102c03035600905815000d003a174442015030507001c00c3c03818000003415840b00214003a0140840515492500c0c804100c6064110440b1040b05d4903001243c01007503032540710404c0d001c424040940304219000381101c00b0707410750200401041149090040071200c518120400780d900c0b140018040703802c0c0150103403101c106055030b803c50ba5413414a0051621f00f140141c100b1050274038100810b2807803000e02c408181550864a0516881c81c8000d03541c2d142e401281c0c020b242c3e9040300c080c4c0000c030500598101c1c501202507464104071104041002c4044400468405416141050484145210b00da01001c203815400c42c1c010700300b40d1035402240309608401c1048031500080c00902404d21703c505011402003416240142c00d500e030a03621a07444148901c6800d05158000c510070240e0301e4030860981c0c1d880806001c00e03140 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 703796978 1250 703795728 703795789
    0x8070503161e031d061204050309150c190524060405070305070e0f01030608061003171821030307020a030e03030f0f03040303090209090106030c0603050f04060902 72
    0xd4101000c000c44045000d142820b100140740600782c0045601529403041d40070358410200c05003072002920f6540b02c1400c000300c10348480d155040034003541c010002140c840410704284441e200700c0031901450340000784580c40403c50002003504c0c600b0980c84162021081c103190040c904000510102d00ca01c00754960340d0398400c40d184036144100012076091003981c840300c0342942100c9041d2081c3c0300003030900140c040141007080c90034440c0344040c9000a003040c0d40783c21550800d00265400c0c9000300d16520f00f00b00303110316070780c800d0681100e0001c014036210b20340b440001d1000014820a000c0c0881c918500da55150307150340f264060303180e4420f4035900c0c5400071000391941c2e074400b0100c010490700b0207550b80c182800020303075501e180c1d8004030314580f0502071540c001981005000b2410540c0f5250b00b00c005031a40c40c0d51502519460700081003507401c0d03161505548580d600007408144c075040800c0f0305c1640036440c450304690007010000b00406640040303501c64207000c582034410b5451800c80c2c0340 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 703798228 1250 703796978 703797007
    0x30f0809190b030a1a031e10060e060301060f1d060307090f0903090806070207031b1203020f010e0615551203050307031506050c1504150908070503 65
    0x1080c07030f07a51380c100101c030507500b19000c0c1d0725210080e96401d5403241a0f41d8100c4000d926812000c006240101d441030f4000c400d41c0c030f041c0c8400fa013021000242060078008182000d004640190000003488084281416001101002126060016941484003240584d10140220750241c20780c2001845040f100e03900070f50240404d641c0880c002819180001400034020401e14045e00407a8042d00074186076448103203089814500b4044069002d581c0028070010404070020594403c1e005091002c0c64045a982142ca8002610710203800c008100000c0380f5015030054aa40300c101c50320340d10201c6840d548982c0d680818007007140303001c05901e408500b44046246940d00212030143c603665482040076015403000c0c6100300c41440d40f08040400000703005902665000c1c41e03902c1c000411803078000c81107051003000d920100100f6000108040c0814080c458412143c0082d081c0316a542040c1d035441d08000c210009040c2c0c4d00f030f030b1540480c082013101c004a8071400d400008030381c0c031080402107201 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 703799478 1250 703798228 703798231
    0x7180308070c0e06040b0915030f1c020f0d0e0103180501150801200d051807060c060f0516230310060e120d0c0f050604061407030204030f0809190b03 66
    0x8240842c2c01d80000e1381c91515008190103e080a04240c4071615007411003403090317200142840d41401000540d48000c00c08000100100500c2803d1051148084c03d0190030700450440e84551030f0003e5446183c207036046101d60710354400a1034000340b000c080c3e12502c601c0c0581c0501c010420b50030407220f1003240001040c00400c0d038200d134008010400310302103a1513030074411072012032582000740240c2c259000356500c0700d9804246203103140c001c9a40320000c00e040c00c10a801000201e0003c0d4500d00070b221241c0300303898502c5201034041005081c0800040f1455292282100400c41c442e1040700c0c5c0e03018010b110300c01020306503034820b40ba424011040b074004449070003100001000c036000300d200c6241075960100c42d034aa020140a5601d2200b508a41b000303d004020b444c80c4a60050100000b103041000074070542c0030f00c50010b40e20b0703000d075890310301900d0251501003014018041800403a088003c10b8848a92100025580d420028086824602018084e40c102c1080b21800131340450041c0085 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 703800728 1250 703799478 703799489
    0x8131a131e050c100801030209060d02031509010606030c02100c0207050a0f1502030a080f0901180615080718020d0e0708300f0a0e03010c020d0206060d0b07180308070c 74
    0x1640d610903480140505071303800c9040e480002d001c9030010800360522440007500311402420380c505c2c044680e008a8070b4004e1403407000e02090702c44010006000401c0c0b00c1c00010741098030317050044910800009648004011312944180d03038540520f0080c0c0e0003003060500a00024045002503559040304205c12a00c612404141400300f1100c080c0701803000c4101d49108060341c13600300c02030f242e0500c034061109004000000566942e0320308171041802445070010b0900c500c201103400307045041002c3e58090503511001e201d50000d1401c0c4078084c0d10302c1300e40508000341c440c01601c80007990b030410041d2081028140b40c5005611011030080030120b8a000c5844510304681014011280c80c2c42c1c04040020000030501c1d0280b01c403030342e0500150000c0c0364034441460003030700300415440040d0071500ea1613091b201507417241d41c01c4c98031a41c041c88100d0b4010821034140c2c17503544483c1c49502502000a000c2d60400c0035141d00040d000340b8610507078001d1900003001989803549450f00390104031807030151 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 703801978 1250 703800728 703800733
    0x61d06090d0504180209061201141210090f150608120703120f2021040503030604330509061e221a0108131a131e05 51
    0x24000480014181c0469800c555486151601d422222980c00d094011100c0c002a000c0110240070b50720000502a03140a0031499004c6514110400e1400c0e006081c120740214074608030a000140f0110351456045610700d8040381d901c04501d030000c00c107611200d0041443c1469548006030003c9035000c00180c03107a200440300c64948851803841c1d00d0241d010010b00280c03100c040c041c50740184d45c1080802035500705000c1440d0b000c106840c1101234440c012005d00080c08200d4403042060f80c1403001c090070111174525024101910703055140c0c44001c02860141c1e860303100045e500e0a112400c44090100002102d2071116440030642003036400e41705552041c454500811088d29005080c284e20742d01a0300c001085400d00c106215000321000029404008800580c840e041407a00500d41110322503415911800c07103800c009048108090701101640c005001400005841e164503400440b0f4140d103054240e40d07800300500325002d40c255000b000d10030703820403ca0050150810b00800715116509 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 703803228 1250 703801978 703801981
    0x10e030909060a030b061302250b100b0301140d05060a02040e06101e020708030a03140a0207020a09050406090c260d1704080705161419060f0c061d06 66
    0x100f20100c075440c000a0101041c880100f81603180c02024802c2240042d007025051201d010702d109440a00041340748040445a000d840800c00084021607200d120420b03c072040f1410301d4048003c40c001400f440d8020183c1000700d1000d0341d9001c15180030994450300726a580d180c19901c01c1c0207034000c1d10524010030600c0000c0342d2189801c5e88101c02c40551562080d030200344080c50000100304000039002076004108012404800901c002c25504515480100d502c800c804a4a0b8a10000070f0003040202e106200d000010703550721030b901c0708a5480d1200803456440e10704000e4000d00751030400828036031010b00002108025501e088812044905914100380503000b002515030000e01150700015040002e40d03207116903590740c1d1a8105010301000b0b420051107581e40761404014650f4402c5000c41d48070100410081e0f0203900c401c0d02c5060301c22136191400309030749004200c05406107509012502d0340b50303001c10703126840410403550010414000c400d10803000000c4228240d182e04241d010310350 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 703804478 1250 703803228 703803241
    0x5040906090903050901080a091e2a03030f02190b0f0610050301060c0312050702011b02010e07151106040308150613031205120903091c02220608010e030909 69
    0x31404002c6a01500c805142c10280e0004440d0741d9001440b22108a40c2d4a2224012400c3c0f801c2c81c000c0303211a6101d03680490450b04004503075031416103c01c0e031052110086507002556190030802181e6142c1848000052445000d83c2417000c24000d6110201c455002c00c400e2200030400513000d203c030000b0441480d1220400d0046071042c20340e525009c0b640400040090911075030303521211502a113042c4843d8402c00076038206541d401c1c3c0c0c2050040c1e46030741c917220140120b0717041036034100c1c001d000800c54445c0300c00310745440798803074403d818110724581c1009000781d009039203200303902c80c40340c0c2034640610b05840d02a1a01e0410303908010611b0241d41000c00f5824000c007180c000b81641e0090000c0c103403a41c1d866140014194000408108041c840d0354806004948001e00034104c64014540f141280340510007040e41c0403130301c220011716182203500036844098845601c1050101000410803ca03002c100241c4219840442c156280c005494140c04e03010000d0014484101c0e0341103080e46844 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 703805728 1250 703804478 703804481
    0x509033f0f060603060d20010e03061608060f0d0302060f07090f1203140a080405160e130201050f0f1308120a110c0a150305070f0507080c0309100504090609 69
    0x80303490704950315a00002c11400c1c6050000b9507804400244001c0709141181d071181c001c14189000c5000048200728425103d40e00102d0724080d0007025002000039180c00ca846410107501000c415040c00b4608000c140d0390303202c03042c28916580e009403440400c0e1807140380081d541c10080342d20310641c01141000c01c4035944075402d20811110801c21001500f0300708500d00441c0020440f04405005082000d9a00d4150400c0900500042502d03840031a01d49410080e050000320011000801c00304441807040300a040d08e650f03044991000140642200e510040c3e48510800d4520819407001213209416031405000a2000d207800c01200f0340940e541c2c012056650406030103800301480c00f40512410140704500c0300c8050708020040f039008181c1f5001155951460344c0241c44441404a021300b0361680500071180c1210540c50310b4140c003018030400900900070030318024800040002c603590000001c01c15180018001032075164020000500501103178854404d030740c507840c205180040c60780200d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 703806978 1250 703805728 703805731
    0x509010602100e0c090c0403060b100804030e01020705060309010c030e0309030d0c0f02040c08071b120e030106031a010f0902070209060607020415080d0314010b0d0509033f 76
    0x11034000b010300e14454484880644007201c804403042c0302c0d80c03401159030780ea00c154142c0102c020f0405996034030b04609000b010b5940e5165002d001d4904050350700240360340301c8000d9910a8241c94203c4000c0030200040b4102640c07580943e5001d02d001c001d0004111065101c45011801e03030b1003c12214042c885001d85a01a610149130f00d2b0300113601407181c0a001d9005c041810744514010041400a40c1c0040c0444845400c001c0c0096401020002e8032600300c130000840c1d0301c152008000c48111a510660035907603030700c0c00c0340401141c10040980e540702504080050f5a0210440b03072582d204203c1d02c51502c40034031035400c806040b5200000d0807462442110055034025003002e0a0744e640c102800043e0340179220898110b80d9800510707000c01ca00c503e004001d0000900078181d824517105008080d21b070034031000c0c0000c1e019031004002c08094642140d150007024040401c55076102c102550950003841d80d42c42642e84440702008503220034509100034051020141107094811103030b03170580000c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 703808228 1250 703806978 703806989
    0x11a030a0f03031806110403030806120a122001092a1e05190509010b1305040504050102040312110d030c0e0f04060b18040b01030203090a08030a0b100f09050901 71
    0xa00300740d140860720a801030035a80048203040340140c50199590070480b40417071000941c4a801160500c10903501420301c68020904807107203200221003e149035102d005002009100c81103c120400c2c00602a40110003141045107601e180c0c0c1e14511041400b0304400d480840b0f5105c0f4074665604650503907011132194600ca030358103581060512a200317241c002a2014415082602c1900044aa0310050084030b090350790407807852480d20300000e000c40d103001a0021804080300340200c1c60744049070001801250b108403804507658079142443c900901c1070b038002422034044076115090242e0400f4003040c50301d4440084501501210504070107e454140420000406000d031002180c41e1450301926000d000510000700c05644d6025075040d42d004c0c1c4601400030100020158481ca050b1095028442d400c0c03c007540f4500c1e1041c4102e46416010100400008021010500c480c11a500c180c10041010300103d000e080b0486016144602044001c40010410800800c031410900b500c05d04881 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 703809478 1250 703808228 703808243
    0x30d0b01050f030726070f080c160201050f072108060d0c14011701080d020705030c0f010c080d0513060f090c050d170f04030219181805060702011a030a 67
    0x311900c004981c0c01080308695298149600c1c2d441501607031881040d4050396047d2507801a600200da0080c0c407110300100254400f10b0140b0500400901a01000d242142d0900e0103596070038940044907945e000345000074000060b008020510000006000b00c0d1440203a220400c6541d198400c0100c1681e450301c0003004101c11442c1000b0420403502c0008420310141012114143c074408803610141090740704000340d5101c2c1d07c10585058040c04042c008d08825000351030200c001c4408034994081040285040003103040070107040c420789001b41c0300468101d4605010b0381c14429081b000b5001c0021083c4c500070300e884003c10b0310075070741c1c4a0201403030760040350b402c15240f030501000401c1103c141d040d0340080071003015a06902240c0c000f03042460901c0102522241140144130726541c0554080307444034200081800b00b15a00d50301c1a01001c0058408140011001c10400c0b00d03446101001304a48100010700000c7e607010341106200c4110b0003a4843d802c6400070401da641d00d1440d07800341220 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 703810728 1250 703809478 703809481
    0x918090a020f220506011106090d21050c07020109080c0d080c010b0306010f0f080304060e040c11011e0c0c080306040c031407020105010807050901080d2708030d0b01050f03 76
    0x1070525004500c00c2c440700815454644030f8031541074144000441c0300e54501035442013008800c0da004030350070340c1c40780c0410b000301520f1034031700b00d11075542c04034035481802d0210000c036400c590807580e001e00c050844450700130301032410b00040c5d540c0b032038200da02c0490210380c40383d03400f03e6140c10003e402c002048008000d0f280e248481e8030f6203021503010b4121003a00d0354a40400b6800341e1410003a141c02000d2440002d510149000b0302c0c402400c08542041081d508100020001c195016000290116003101c001030303045404c1c9402d0701c0e00c84481c0c000000550a00405000d04800c254a0403d8410381d51420310030490302c1e40b012036030f860104c14000d1600700b050002c038a6a007042e0b40000e181e20100d003400034008109524801c4a10740803122040180c0d1202d00500c1207001c11300031040245000d40310280340d035042403011610382d001c48101408121140e05d0491a4102e604c51010884803000c1d00c0009481c0c80325105512a80454bd040c00500d040240520b0154829000c45890303054042503141107 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 703811978 1250 703810728 703810733
    0x203030403141b0a20010f1803120507030914010203040603020310081e07050a0f1e09020d060f0e010e06060a0201091b0501020d080405030a2010020918090a 69
    0x40c031004040c0070a8a001440506004203404900b650350100740301c01000d0030f0f116450100d0080081408903007041e0800040080a87d030020f240221548041c01c0104110010032024080034211b948060841540500e400141e50303081801400174030b00a47d40d03108004d440380ca440a09100885100740141e00401007000014800e0b8041c58100e03110b902e41e103d0003507581d12154603103050507280d90400c12807104480c0030440708000d00030040500341c810f03001c958909444611922900d100d1001d107402c02d070074a89003680142c2259000342101000854945042d81c0700c4d88000c0489010300c2c420140c451001103080c03620800300604941c005000c6840980d031300340078461140c001c2c40709001990b40360140d0100141e41c0150720303824a42d407a0078410741c10345000300091515520301e147c1e5051104000500000c25000300858440380b009041400c20818420a50054980c281c21011401c6c0600d854880e0920002d030010710001404890710b8000b40710107c06a081044240d8000c143e9034841d0480740c00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 703813228 1250 703811978 703811987
    0x206070f113111071227030305030402010203121f081504060b01050d02030708161d01050901021204030b1605210604020702090f01051e0a1211030f010f0501060c030203030403 77
    0x4280703402c104042581c1200551029030358200c09000c54001011442c0440c1c883c0c0c0c002541d00c194181d050007a003114220b8035400030b07140080d02000d820440004002801d5900800840700030720042c16041ba56440c203010800c211103152000c0342107140c1c0800380011000e0002501c098882d600c204d0004542d22140e07101e070001c001000025050103070074814200c1c0f456503031010b0b5110b1401a1103020440c5050014400c10340d81c07a110900c284211841c120729801510641031080003000e0030256030700d00c0120300603072034200c1d1942014402a000207012041000d2aaa014043e500d841201d0540800082007500c0342d00070007006051055228102c414034094038610160082405000103103001c2d40e035004100c6240381180c0c00c042d41414a00100000d04200440c44650805100d0703020140082100003005042c8500c10070070a88171240d61407041c030800c20012054001c1c0101210f0740541d0705480140079098000094030010b00c0c01000141d8207025a20000255505034041c6203955210b80d02030320b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 703814478 1250 703813228 703813309
    0x1612020d11061618080a05010f051e04060e030f091c030203031303090e1501110102090f0d02030f160618030305030c0c100c09090501140d0210020a0206070f11 70
    0x241045101c11303900c0e01010412914130041c1c100d01004e000780442c20704000d0b0030345154804070101c00c0e103040d00300582c084840c6420701c248078a030100280581c83d5410300304041e08003004c1c042141c2c000041c00300090000c10000f01002c94050f5005500300c102070381d03c03c04c585000309003d800758008000207841d4040d80001c1c0c0f0701c00c0c0c2c46410507242c969190b2403190102c5c0c10885900c2c4100c02e620304458034660304510b2286968000740002d41c03401c0d440001281a900817002d46c075018180504a460441d541807000c1300d17800c0485011141101d5031a00c0340f40c61080a41300b880045002078804180350b0b20300c040220103680c0c054032114690744561030320502590003409901031500911000441d158204e00944100391150394030074449a042600c14001c640c0103034010fa00b0950310441d908080d07202e525841c026641c04480c4900800d1100e002a030030040c1a440082d40988005016000c01400c2580300101c503000d4100d59a10342c128009203d44880c0b45d0304011424030000340c4803c0480c0900c0c2c2c410 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 703815728 1250 703814478 703814521
    0x40f0203160503091908040810110912070801090c1d04050a0f051903031505041505040203061c0b04150b0a1707050402180f1909111612020d1106 64
    0x1108111038090014161a085c03c50440d59001c0006081114000c1008500c0968120480400c0400e41d03030b13142400d81d84903014200d0700600030001140480001072102c40020309100f40240405882c610307241d41c3e481817901a60184001c1542e4540ca40380d803100c80b10740b09d55808002051840180d0700c501035003030500d140448040c4600303060140051142d048074801e542c442e131404107081403c205c00c0081030440d608424060351030321403100300304010040c0c240f007200e006aa00503605e41350710006c03070401103803030704c01c1401090581c200e00200088100038070b2040740207205902190501081d080103075425500c800394441c40c01c103002c0c40500c1c0f06280c16144010030004076120b0780c0e0380c0c1c40803034241d0300002880c020380040c00591485030b00700100d410104a504843d001541d00590346440c9c2001d4a90144d542e102d43c0e42c001400c8200600c1c806c8400f030548004040c28001c0b030515064101a00d5018031500500610003080702082c003440d04920104008005440540c1e0344840400b04454882480c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 703816978 1250 703815728 703815733
    0x60109180204021603110a0b0a090317011e090c0819020c160f15050706020a2c0102100204080a060905010f1409070b03150609010e0901080c040f020316050309 70
    0xc81005a03240d01c01003440c05421002590141003a08020b8252000c000072003445810803009800040c0c003044001d54041c5420b40c1c0000c60042c1424211565401e481a00c20044100c1c400800c43c10701c0307045685a0180f04070399a2100d5522000994292141d4850120101e87c00b00301051918043e14001841c00564482c01410030343c0e00e40341180380100143c4001e81d590800c400611036102408010300141c0042c0320f0183c407a0385441002003040c070880c1d802070300003940428000304040c8075261040c0c05d11555170a00344d400783c0380080b070042c180d14145c10ad405880b5201d016060520b0034000d40d01111000c10152020044c2030b1142005014000700440d480e560390302017a8100d2501d4030030468103c0c1c4402c000c4c001490320610141c0b500d010354108072030680c402d00c1001644402401030008071041034850a445104050050b00c0b0300d07031401c1d60580e001c9140000480e03812000a040c8007032034401c407014080c4e5075504480780d00b02c0c0b000f605c01c01407a01c0c082c0b0740707110480d00603001960000d120004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 703818228 1250 703816978 703817021
    0x4020d0f02041a040e0a120c060b0a06110105090610050d030909090b0103020a06020f0d03092316050d0203030a0e010c08030c0711040c0e1203040b0d020a1b05060109 73
    0xe402c54803c07501c880e030301c801125441640c906003845808102e0f040d0340010304404000382c88400d1103c0c0101e00380c0b01001803003501501000a0382d0081c103042c030b9001d807000940c5612250081d00c1400301d008e07082401c1d8030341000280300300310000301c450040040c00031204405040030b091210041803840260203010040c0000a00205203205030b100c82d50180310040401e5045104001c03500c1c0241e0f00001c2154001f840d01e05020a000ca410383c6030341014200080c54904900c1c118001d40500741140b9640c0313448607010044c5c0440803a0b00c9401c030f030805100341c48440d1207600b000b4908456500c040d400d94020710a05000303d00405501806003014102550804940c1e41c2e0010b00c0c0e402141c0d40b02640501050311310402c60b60046880040508840c217204c2c1480801c0c005119007200f4058520a492004440c518114141b00302c0f000340c080c44400300e0360307a0310b042031410296010b0481000020404007000a001c80c0386840720100c0c5900c00c2c0a41040c1e460a5080800303404e800200c081086020032 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 703819478 1250 703818228 703818233
    0x3020a03111911160e0a0603050a151503031707230715050906071d0406060e0909030a1d01052712061018090b0403080f1e04020d0f 58
    0x1c09044120111400380d402c0310714001e0000c1645201c2d12803540660b104404281048507028040c4003640d02e00e4021100c2c17952202c0340032020b0840f42e0b001a045000d602540c0781441401040e01c1c80d402c40f0410140608980152076002342156442701400103003007c2e51200c88101c81085240c1c101d1400e241805c0301c02003086410786c80701495241480000301c00220b004c1048030a4140880750014194200b140d864601c00b0340b91100002802c10b410030022081030001d00900c082c02d528100c0001e8170420401e6250703107000e400800d40c50811841100e40c0b4000541d0803500104940901d00c80e40e4aa042c02c408900140708401240c02883e81400801d01030f000440050901001c102900c05001d100325085202c03d00c540da4051461405460304041d00704904071006c50317080c0c41121480000313034646406464000d0010940303800300600c00d02d0510180000c1c164080601401307110320901480c0640c468640010442030781544801c411540d42000601503e040e4291284041c01110a09065003296 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 703820728 1250 703819478 703819511
    0x80c1207031b09112104051e1b19050907210b040b03070605041203050c030d231302090a1e0509010f060b0f30041a0709050103020a03 59
    0x6407900310b8168500501000f03440054040d00000c601c40c108000d180c03201c8400c03040300741a21100c201d2a14807070a0003040401c00d00308942c160340084004043c40d40254241c2c43c6031603a80010702484c01560210310311219143c4100310600f540900023060764105e1810b003d0002d46007004000605008042e041200300c050418401e40d901130701c25800143e050142e13000c00007100c03047c2c9600c500035800303040c0900c42d40750440221429101c40300174040b030b05c1a071450203c44910a59001c40c641d03000202e8a40356a00f0190000001080c03000c0c1004007074404111101c102170003c50314602954003480940c805800d0840e82c0d1a0410301000011400c01000c25078159102101300d074050443e41e407402040084002881100750109042100303018031494440f982c100c5000382d00003002500d200081110416071820342007040540e1102078000c1c1090107511940f50300d203044406550f21160400c0d9038140c001c03554015407190081c0c0d1241c0941a082200440003908900550410715903075220031845c28210 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 703821978 1250 703820728 703820753
    0x305190206040b07050901080403180306020d0501051503040b1311031c0e06040e0a0c0e0306090604060f060b160809030a0f050d1b0305161e020415080c120703 70
    0x140c00400481c01c0a1509100158008002404010060000c40f0301aa481004560400d0705850031074044c0c040407040f16680f020a0307200405440c80061803042d1403d003034005504a42d8101c4820800c6207501204901c00d05c01128020006c2c02c084000813245058265480b030064080c0d2159940c21140c500824944402c11451340c100c20403580c0200101a0302c25100e000e100e80a40e012400c0c2441c186031007410541c09003501d4503203600c40640e85945840780383c5c803c41505000b412111541012400e25403140c01c143c400b614401e04140155400c01468040d410450315020001d5241c4075480c40031502c62070300300d58210741c0078604001c46942641d04000484410740100505800d102292904602c0d00000c01c201c5024003180050f040c00b40e0401c10500000e00d80c042c03c5c080e55403400703251901c03021204188010f1180011421800e4800c7c011101c1f466018406d4800300f0128203910b15107503d0300d030304e8461404542e000601000c081d08051514142010310b103803c0b034504d2500c2e5522030301041c04 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 703823228 1250 703821978 703822027
    0x1c03150b032707030201030e21040614040515030402010e12010b0f0d050a020d0804081605011215120807080c0f1902090f34020f010b090109090305 65
    0x601000b44428500c40d440301610345119160002e5003041a800496203079282d611010341415900d020070041054103221000080580038110340d42403402c0f0840440301e41142c01010b00281008141c2c03050301000508a80580c2c0707000301071101007000029107600a910050049040160a90702c90209844000c04110350451110004c1486503000003403042c882d282041c558030540311603070380741c0109070081800c61a083d010744074240425403e0608007618410f9502c481c2e0280308068039007000c00e88401e1001e0076208240e0394600b9024480c0032a0f03043d82c2007604924440303d1800d20402c8042d00e21000a0740840c4254120303030800310140c64050481c5c0102200c03c0b00f5030800d0703258070800380082c4080e2035440c540c80c00c0380c0000ca45507004103440d494000d06c03e01c1c4803015000131072811030b10780b0709a0500413051078851000100341d01c03001c3c0700440a45080301c00740c81604000d058510040c080c82e42514006001c10011360710300707101040a4050301c1d0058040c4942003000c0d4a8641010384010180746 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 703824478 1250 703823228 703823249
    0xc032a1b030c0a2103020403170c160e04140a230c03030304060504060b12030706020a090909050a050d0e060d020d0e191112030d050901110a11060c04081c0315 70
    0x513024140a400710f81e0f03c03800c803003c0500c1048184000b44a00710703c01c01128a15480b0303600c0c0c40c60080c02c03a01d0504050554a020b400e202800104039091101c07131440f6921a040010f40c408403604070695070401800010031071300001c5448164100c103015100f05900b404c2040707403000382040d004a0705690046d10140d030070340d48500c2000144842d5009022403200159500903040d0561074189849000e0a00000c05040d000141055281d00c101c408001611180d102000040e5071480c04641d540c440d8a0100c41501400c1000b0324818012070109480c1400980001d01d0110b10b220f41400940c007441c0340c0c0d291315540b100801c0c03003050100840c03046486c1c1001c2c0341c00e81183c02c0c1070541c4004030a040d500d110b182040b4005804030b0001c0161646e00c40c0d507080c04221a1141100d0310b000d040b2081c0900351801020500d0041d076035000e01500c401400c0203040e00c407540c4031908c0c20381c2c1a10a601034102558042003106000c050201580800d02d00c23140340004910b01000b9144414107a11f62041c82d054 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 703825728 1250 703824478 703824503
    0x5091f0608060106020c0604120c0510030227030c090604020708030f0a06290c0109050f030a0801091103010b1309052e060e0d0503120c032a1b030c0a 66
    0x20710030040c090140126000a1400c00710381d40c00165184620b0141c035a40c0d00e9400100e004000d5803100e520090301008240c07603c0840ba01c1c100500a401400000201044602400e105454481844039180f1400303000f50842c403c1c4030043c41980080906141e40007a0300700040004160f924010350300903807540c40ca00c1c609042c0000510b080e903400d80c003c0e000040d40c200405100b010812800759201241000c0207446400c801c5401e401041000e1029015000700c1c45207465800700030000f044d03180e02980301e000b6682d8032403c5d81000c44080c0c540a100710081080140f25264031540600b4080010040c4034804035151207281080d9403050320a041e10002a2103c10312241d410882c1061101007144034aa25515004d0010094003041d0b64280c0106500903206081c40014400c0f41c0d625058a03155110908003c00003a0059008460801c404542c0c541e00d245800c00c007248000507084600640c42c00c1c165541941c0c10388400b00304e51500d05100800c1404094441800300641180c01543c000c2c030741 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 703826978 1250 703825728 703825739
    0xf0108060721091e06050106030e03040e01060c2102030901030e01020316051309150504150303050a030b0a0e0a05160c0314090d0c09090302070b0909070305091f06 72
    0x80c50005000c00c828042110070041445101c800d070348409074280003001c691901241031418003098900c098042121900782c02c04140b1445411a604a41741ca55003004000d0703032034480d29101d020760300031101d510711848010420745100700a1000d10701d0003400003010f034000704400e610f40c185050a170031025801c0465108140e40e09807040c030380d80c652184000d618510304108480518081301e00c04400b408004a81620300010305062800600841201002006071101c18040b002005225507441941170103d60700104055090140407298140c41d5036041c42e1801c01c00fa005400520350709038010180f54400a0001441c00005004036240280001e0070300300a2403151035103c103000d0500501c603211900340c0c0002e0f80800300e0300071058024842d41c6c480d030100e40002c440d02c00079600030707007148010007011400307030341a40c04890301e2407082c1c003101c5003595030b804402c4050060545582d4040749a00c001982075000b5040a507008540c102030341c03074070380404900c4440f00200d800d200c0c3d90240c1c0e5079000e019 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 703828228 1250 703826978 703826983
    0x12051819020f0904020f01140d1814030405030a030c02040b04021204120801050d0209180607050d0b0108060603010b0c1203090c1203040b040b160f1104050f190209030c090f0108 78
    0x4280e009960f00201842c16030041044110100000b40c1085a40d400034095041001c058a081c4904084144907000380b00d0404030604002241c1510802c0c0b414190941550000045500322440a0003820200d82a500c0c240c50b2241c0c11042a07070055220400d1000c6582d5038401403150214104103001a07003003509180c0f0a800d4142e070204140038480300140210340e0381d0480c2c406030f16411540e40900c0da64415140e00c81030810841450144a0030050240319038004c000f82c84010141c0e1400c0148440e000c2c01102da9080950f020703a080401003005012441000e40144070300c0921004955410305880907103211903000f15000c0340a44c00003030410f41c6a240071010072501ca00c0e1400150f04150401031290040e101e18070454000110028508000c1d55460080030032647d0450f0002114440c942000105590111111b0384100c2c80c110009070100c17403404c40213005024506880781c03000e403000c0707000009502c03070b241490f0325204003200607025503108180a84901a401107001e100c0d49002c84551 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 703829478 1250 703828228 703828249
    0xc0302120603152e1212030c2a1515060c120f021507080109050f090c0108100909110301050c07080723011d07090605011205181902 58
    0x1071003900801002500310141003141c80e00448644c0a01c25454180b0f45501c1c10500c2c43d11410240034011500080c0904514142c011503601036080c91220400b4554118212550080918003007030200b10349403190340740c40281108500411101503460704150b250041001c1c403540c00c8030340c0640c6640c101450000078031070510040103c1e003005000d07000e80340e807000f2210441c1c02e503600800c024071100000040c4200022101c00103048001d40702800e10940083c001c803c01d0040300801030804011640800014038450b01c160181c1c00900320703c3e42000011518003a014204986110003102c022424982c28411003550510500320580c4642c1640145400d68034010a0004018014002140814884022201003590055200340f0491b044c0145000c003400719940101c0c0f41d880c007a0706d400b840800804920040160a040701c1c80b0342d540741219070950b50607024041c0000c2180300720700101070f0540c000c00d8110081201034080e441000e0b500524004080458081c10f000790f480800c103605000c968107 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 703830728 1250 703829478 703829491
    0x902031009020303030103020d0813300f030804170418060f0f0b0304060f050f24010909020c030405120a030e180115021509010c020c0a15110705040c030212 69
    0x5200075107107600000d80b00c1c04140701c042c0c082c540c911004400c2041c0d6200326524414007503010001e9039200c0140300524000c6030180120800349000e44924208174610402c803460b40500303410b8098040c0d0b541241d80d118060310032540240800106503142207900c0c09000500705014a5540050780c1903042400e542496001148034070161006000091003500110b080e5101003403c0b035a07945039407a004008100c4140015510f510304401d104c01207012003c031500510700c5040800385020444004252030914a0403140407030081e8008021401c002d03005412081c90300c800750381c00c055842c404200302e6496042110044d41001503032800b0076800c2100b0034140d0600f9203855185040c7c4c0308280c882030606014080900e00150403240fa220b108000b4650034800354140d1a203a800c01d02d04040c00380106850700c03405401003111244260800950390811154100c5e200040005000d42c1034070001101c12000202c0e005d500c00100d06e50311540940b60382b0005030b40c4c0042c1c6d5044404100500c0101c05042d1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 703831978 1250 703830728 703830731
    0xa051203090606150906040308030a0c17070e0d050f010519020301060c03050c03071403031605070c0509070207170303010e0c090307090b011209080c01140f150d05060a09020310 78
    0x92064860340000c10070b038400820b030740c42c401403038502816075241d004517008a50700040000d004401c00110002031406136202203028041c2c0e010105060312500c441c005075240403204c00d800500702c18802c0111103240b1001074201c859080f52500c5942c03c0c49840d4210700741507034460f014072054180d02c000c110b2914600342c20440c15941043c0f03000b480380d40361902c090100000465119100300c0300380304603501c280d0310903103070a00303015030480560710f907001140c180600022040800c03032150300441c1202e50417135010700d02d502054104010810381100280c1384404510498801041c0351a490042c0c401a422b18001142c0f258581032050303c15410003010708052a00501c035041c590740f000a901c03030940311900400300e580c00340000101d40d9a00c04085107144181130680d40003d1054407001031850800400c003d0004072809130180010100554000a0515a2000184100d2503500c580c00c1d0100c002062090301421503100d80345051b0b82500d0301a44241e441480500b1803030204504403402a40030750 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 703833228 1250 703831978 703831981
    0xe010f05041a090d110a051905060309120d240b03070e010e06070305030402040f02251109040b2e06180b0a0c0303151a071103010507020a051203 64
    0x5004015004511544070ba0700800a08000ba501107401507405840d000703003c21581080c3c60400200c100b40c1c2080250090640a0020501d418054081d070102c810307a420401d2880d241c0740c02d1016561000380407599901800104004449070300c00100042401c0d1000801d00815070031803100792400c1500304c410070440100007000f50080e454140c0e940416a8140b0f11281341c007040043e94004c2a00580c1640002c00240c060704140e0040003a40c0554000e541c100007420758285030070100d2144034800311030410302d00485903009074904030703c2e0031b094443c1c12406c000c40041c001045503440c0030b460031030741a40714208002101003054410f65420284d02c0050141c0c5020005486920760103000300010440030641c6c5a1000c1c0d80c0b524114002e02105030425660420280003c141c041460411000203041c01124603030541c100c8030030010740342104030120400d140340f1031340c9409500c81c04c011681180c00c95080c0100d81e60a2103800c0c0700e844190040d01329008140352150400345801014129500c0c02e00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 703834478 1250 703833228 703833257
    0x5060307080a090f05100e300d090204060914091b102303060a1d06060304030c050703030e010e06040e0103140708010204090f0c020312060405061219030e01 69
    0x18820303400801101c800a84018582041242c42005280180c40781c03013072820b542c4050449a004c030300340e00c455009232403520104114881300e410b2030b46142d07481c4640042c140756121088400400c0d14502c060340c002107001845c0e001c80c06030341007980728400e129a18000c03060301c005804240d0b40d010442d100035144512004004440c1c1c0c401091449008184c4921520394540c010400c1c0414070811112980c510303400a40790004036481100c041d0b0158041401c005001800c10b00605402044109221815603909061042d2303030300010410750410000808140c04074105001c4000614020303030325443d108a8850003d03162240c50806507002d00c0c004c2004010006900c8005815240d100240360904103050010603d4803103d0742003181907520000b40015907005aa01c10358854101441c1407080c11440b00050b41c0342e028030b9600c118480004400540745140070360100e076006c81d00500f0038850300d868105081c540040701c1f540a0510510400c90f00615800c000f2600c52854240f07003ca080f0700600c0c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 703835728 1250 703834478 703834487
    0x90e01021315090e22050601091103010602030319090602120108010c0521042a050901050d050606010309020604080d0c0b0105090103050d0804150507120608060105060403030c020612011e05060307 86
    0xb13104040c8020303041408a0041810300c0b0a0b83e01302415540702c100020f1107030803c26203501003841007918072803415816040441c0c101c000e40e4102d0344103801840c29551000152040d20881c04c0b820001e03151780d00c100034005041803020b00701c4521001c0e10303c1c0081d03040000c43c0742150002e400031020312800740075100c1800c2080c0007a0b118811502042091074440340742c41229240800c0d071620880e10320203008051321190315120401c4a808030365a41d456681e640600005480042e800780058004100188255000341c00041210b44007078030b0b0302d04e45541c41c45500c1c10054007601c100c0008031490210070901007903050311800740504403090032465166545203651001010903503000e004400d00003800f17001e511000c204100200700700c00d029038039120500030010003030041c41d034201600d02a000b2032140e0300040d482e4145d1b1030180040d1700e07160450302c05413150030300d210049034000003c00807030100c2d1035800081130013042d014005a0310170304000b200c505080c0c4550009800b406051003002080c5a10 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 703836978 1250 703835728 703835747
    0x30f030f07022103070506150f12100c35010303120917030402131b110f100e10110a050904020c1c031a03030405060a09090e01021315 59
    0x1a500e03030390718101440811207481c00c5120351804030b40343da180d4280004010008005d0709124100b5034900390384218a05010308400424940c1211089400207000d00b0038010311506801208122526402c0c552820340550354a415000c00240031840c1c4600c070040101030341010030400031700500c1c8144150342c1098010005101c00b504215075080070001107100d5602107490746401100141164134079030b0300c11040b94002c0d0b40403401604030080b1501da0210350f00c991400f860300d89000032034114031501c0407103941d080303111880d015000d00640c42007120020081e05100144510300450328401d0144810b0078086031603050441c0c0d6041000b030b21b20a4000b2004c49915000c242045511400d01e10003040c0240180001c1100b40d06c60340302c41407a80300c1410000360796004a507500303112aa40c070103030150742c030007910103c1a007550040c0400d101900e0254040d000f40c280901c0c050402c81e6a03402080b080c1c0d00c0c4450f52812907507002801c0d1442c000340f400d1300ca024007048560000700144800700102082c00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 703838228 1250 703836978 703836997
    0x40c0206041a1305010905070501081503120904021303060b030c010c08190504030b100e01050301020c070b030915040804031a01230f18010f080601050121060f0b0309010b030f03 78
    0x1d040d0001103608401d007043c06501c64114000b004120014075002e42e80d1000ca01078070740410b40c20300010b1a415800c0031a240c0904014000d00070041c03002c0344001094004080d1542d105030240f050340303c000c4a885000e8000c600464020851b0304e20341d010706d800c0c828102400b904029819226001080752281180c00f4003c40b51141903110600700d00450701c600440e00000e05031022141440b141e81c03003001440b02a680c00500450160740e903001018200e10a0411403209030300200420007001030108040c66101440c041660fa81200300441d403071880100311000c581c0020003280c1401030122000c10004a00003041041d0000e5061941c0c0304141c20a0101401d402148a04c4130308503034aa8101040c600580589504941d103100404003501c800b090291a051884680000816480000d0080d040b107006071100303035600320001104281510700b189290b100945809000407080c05a03e80c0e000142140144a5180d0034022210f50a584202c510315100b03601020203014100c6001c000c079101e9a1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 703839478 1250 703838228 703838273
    0x501060e0a031b03060504080c07060306060207120c030203120309010b04050402011e02071e0303031b080403051b030316031a030c01030e0724020709090f1104140c0405040c020604 79
    0x410039005485410116013009004506103002e00042103103800142c404094202c0659480e161588021030844d00c0d03d101e58001640403810800c61000e103d004c0c282050300800703005c4003d58690300031074074010860300710b2010854004108000902d00384140c0c07031030010403a000d01c9242060f4000801615424819101d003008025990280c107000304589401001403001442d0820341000013100041414442500480d08081610055117407111281c0d0241d54180c4810895483c1da0700e040350143c1081340d801030004a41124220100800c001444c80351451040c20328030300844640c010309a1340c130300c2a01805607913803220780c0407103550103e00131071402c0080c0780024042104a0040381303041c0240c0e1045001d0241c00000c4003e452a80d000c4c84000e455a800329800250307200c10003002c0360000c12010382580044007051000501516140c81e041d030006102180c52110f444c0c60a10007441a2210444441c0000b0708108600f064000c101e21004140050070302403400307492f270f0f0403a0074689103600c507802d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 703840728 1250 703839478 703839503
    0x20309031504020618040906090302073308060a170307140a03020a08030a0605040e071a13030219030602131401170a0e010608030403150b040605010c03030504050106051509040501060e0a03 83
    0x240c646d07074405180541c000303c0070f01240c0807600303004c0c2d1aa0402d0143c82c2065003942d94002a804c00210350202030380350129504903400c11340c1411909600060496136000304c01c00310010726140e218001011417a4a500a582c0e40c0c4182c0c5016030509102442180013600300031822000b0a40100300450360075002003e90342d4075615406090000e1000da00840c3d0700c50701d44424170340b052038001440c3c000d88402207e01064440042d4070380000380600d50039074070318800361681403005003401d41c0d60b2003c20705011441ca03201601e0b513a078001644c101000342890141d44070010807400034050f2441d41551420701303088510661029200c54003140040c1182502511000c840e991800254049002014107c6c01c0d40d803656224a4031892450900384442d8603142000080c0400741b030140300f01411a00140c60b00180b0400300c1c0e4041d4003910000300181e6095513506000a01d6403100242c2c1514010649079840d542c00c0c89070100021a00103030840030400440100140003520342c2000c000c1540e800a1806426 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 703841978 1250 703840728 703840777
    0x30506060f040e0f0102090f1801150c081b0706080702031e040308031303080702010b1f12050c070605090303060105071506150504031a060a140402190203090315040206 74
    0x28202100c90f8224510900724074450224046d1b000c1e040048048a0100202106d9010444241e402c0c072005120011802c0040210340502c02d80410304034090300701a00e000b01c150b00e0341252034125140340040340c4c2e2403030807140040c201032208401401d0142010300d110304280400075a42c1c0280c0750500d211200d003220b00d4054910b40401c1c1c0b4020341d8010304d210360b00d282a03e00d203c02e10702c42c03407402c50200d04181c000c1401d1a0060144410705840508240c4994500000301e0008e100e04c1401d150601c0043d0b40400f121045a00a46214000b0601007641e11911440e189080b10001410030405810038000c2c424503a81c000102d642c655005001020451a01100c1000805141d03103e0540c070702c20307061003010244d00440030308116402511050013040007810340260301101290110b52103859100b0078014080c080c041c006601c14080d00060030b0442c610a2805414855116040540d10120345180c0314075040004408030401c6030342d02c410a04160303000c94640c1c054488464401401c0c0008041d4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 703843228 1250 703841978 703841981
    0x60915111b01120204080102040509090a1205160209041202070815040f02121915020a0e04020d060b07050609281104021c0903090603021305040b0a0f09060e0105010306030506060f04 80
    0x40d07560510303000c55845030346d040014000c0d03000c2d10a0741d000c3c020b07220000b543c0d21400b02d00c40c840310fa00022880104a6549811120344d40043d4503101e600140e0607074100540c942d01d4441d449030707100d0381d28031103a032599420183c6801d5847e440344946512103410002c0c0410708103e500c1c3c10650042c0e03900c00140c09440011152400c45568241a1040340c00240c0320b4101c20008418442c0121820352590704060800710603440360501c9000841e0b040c020a0086081070b500500701100700d8440040c00b581c6a601c824807560044100340c2d8243d1102080c400c80d01d00c2840703480b00802e0188546001c0d01c104441d480c1244081c004040e12001c20388901c5185529160101e034218410f20b02660f141c0c982c8150000020546041c080c1c3c0003501080c1d006c24040c1c003a00c210750070071100c80b45405505161004100142490009054100140582c0010040440007040000c1d006003200450010b091503000944000140d0242d410141046002c00c04608003144450f00100251074801500300303150701150 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 703844478 1250 703843228 703843247
    0x16030c0b03070507151a04110a0e0a090c03050604051602060c071104050c0703020c030d05040b0c03090907080108010b0109050d11031c0c020112050108030f1b07060915111b01 77
    0x403c01d0b484281e041e81002d5465210b819484074100486d1940c13001d08050104549000000b242001030410401d80750070b0117040d00501015000b068660001d840f150510259804200000d011944910600040380340c94081c0a5105401c2c1e11841c20303080c10880e00075070720310011704102481000041c0c00c0b000e001800b00d1888111801500501c440e0615612042c0daa1f4400403054005003e241c400c0341051074007041007130bc041440d5403147c0c20300b41441582a603a510136440108070340703c00c02603582d8948a14801500c19038485c1ca4210715513250580890944030f101025604001c82103009004a41d83c92042484207600885098050b038038420210745030000c081c0c1d00004816141c02c00c1c52009500034521000c8038402e0b0b80e02500308501441a9090382c07400e000d00015500300b444802031980120019090265008085400c80000105203134180601500300300d001400101003030180e108189201d0181c1009445c11a02003840b40f03040341c0c1c44640c400c905000d0781085440340030741340c1e200c3d43e0281c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 703845728 1250 703844478 703844483
    0x515010c0609051203240307061b060903170106020c030d08060118030c0f06050c03040e0c0f03040c150203120402041a0a1401030e19290f040516030c0b03070507 71
    0x484040300041040c15403a001110840d031100049500d8101854206d00c00e5506414064011f082c000c1c200766081d2801c04040c0c59820245908001c88800b1481c280185081540683c41d00c03401482104102440044140c1103a000e43d40900c0d130144251724002120780d076100d0980351407151925560012101c1d0f014200040c2102185600c012040c084070014000460740c459424004072503450348180d519015224004560f80c2050004020704208002e20303a034401d003400b100620344841c054080c0c169420607941901c01e00c0c482c0c4020710041d03801c40c54110180410307000a600f00307201c0d00d00141140c40d0080c00280540d03203034040c4415902e0102c120501c230b80c40c010412082d89480c1c500180038003281e48592800641802051032842002240d042101ca01264503990b00c2e48041e1105000140c0c80c503107a105801282444155500340d4403190340c001e6440010040c0c140c200741c00c0140c40c14080d03800540c03111440380001c01c00254142c10341011698031344a80c07900c95849107410f840c98001c00201 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 703846978 1250 703845728 703845733
    0x2060d0207020409111314131106030103030909050109020702062205040207030305101d0408031005040c020c150306061e07020621090114070c0c0801111b010515010c060905 76
    0x20004001614003100c010179402c2d1102c030880c444210144041c0c40e95000310440208624010a00d00c2c951b813000b07110040d0040c540c03d5000510440440c0341940300340d2047d0002408020300788070700c5a090003820300400090100b58180b80c907580004102d03100d407129400d6018810075105105810820000008040050046456100900b4041c0c054201110781d0007800141c00701c0460140e8800702d00512400e1f10303100d00303041c0340d88550703440060f9400a4081010136400d00300001e042e076945c0c05001c000507182da028000700d2040000380301d003c841040391400144400d100b00305d883d071104019201c0d802d00110a0710b40755074a40700180341c40d2050440280d00000c0000b0504140e5188852648002e512034030548481d07a502d048042c01c0b1481450351595060310440880c003030521415030031010500030304118480960303850003036084640010301081c10841c0440c4820381c083e0208082030540e41020002d02152030103070000b40c00303401852100343c14040940000350901c00ca43d4860540150301208 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 703848228 1250 703846978 703846991
    0x7210c02010b0310091112060f0406150303030f1b05160c0b07061b020303250e03060f0a0c050f07020d2d02040b0402070201020a14240114100c02060d02070204 70
    0x1040c00a0b0070043c10076100080e2101001c001b5003030040420003c0032010001d04501e44981080e003d08682c0079100340c0d045600c9000e28423541c44081c8007080211700c2500e00044401e0741541e188140d0301100080349002c030683c0743d1103601d241c010080380d05810020b0b60301076076540b1340c5c40d014000380640c1d000651100300204130303141040240d0344a203a20303120140c030311502d10311840307000ca950b4802241c8504400d090640400c0c0981007003520030103158814203041c2c01c0c140705070740844e140c190129043c10810200a0520010796803a201d81c03984000350b0f103446031500352241a110628030034000f00034090403040082600b40a0792150320080c1010102d80d490444010b240b1043d032035004030400740e100e94542181004039140600c2101e4090341d068010b403054607107035150791500e17000703000da011503a0151401070120216001c1c601440300c3c8289a003140c0c194100420800240300011b4000e0144851500040d100354103e44000d200c0c079412603500c2c4c2c0d100460600072010740a4002e0094010f8280038 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 703849478 1250 703848228 703848253
    0x100e100908070c080a03120f0902030d0c031407081c020408030a0309050610050d0605060301020f0c0f0705030d081503070506070f0201030f020a0912060204050a061707210c02010b03 80
    0x200200c0c2e000f0b21040c8441c0d51038200d0140c540310740c1040100072070b945010414a00d005900242d6807148a42030002c2c440107250042410000358100c81000102c02462420406030031103944407003d00c0f500110b508003452075a500007584120310f80c4202402c0506002003002e181c0790103c50107811310030103480d01c03407000c1078025025005141e41120540240b50000f503610b00c601700040100c5100030300b000680303440c44d1900401031101400841e0155001c0114030030700b64100c2d00400c00c00e0100310051656842c2034004a091a655802c07603403203500140581020340b03a0000b9980d4100a041f1a080800c10325031001a02c2c040c1e10380d000c0c5d900404041150b005000c0503040d6044100c3c004c0e00c0030b01000707001800c0e1000300d20510b0b8100d00440d0075070743c0c180204161520b0004075684244c40051800707484000240e403115055008800080c216917000f120b01e000c600510350800454104155088900b05942001400880580c0402a9200d0404070440c0c400d401051010001406a40320380314842c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 703850728 1250 703849478 703849493
    0x305180d0903030801080d09181103011e0e04080403020910030b01180c090305030313020112050a1d0f1f090606060302030604060605130611123405100e1009 69
    0x912090f00459084070000511038000714905000400c19a41c1000a500740f001c49206006c0c0b0b482003c03904c80c6d44080d115a00c8441c41c2c001d5018000c80344203041803650a00e16844070080d03039002080411513040500002906100546094950444012013141d6403004041710307034811544060700030250580005030100343d0200b00c444408a80e0814031085140c25410b403203044491200800a0b80308000144185054070b0308844000e105241a490524250040d0b00644909032038000d00595103290b140040c5142130328a02c0c80802400c042e01010b1804465175072170f0769008035110740e4445120841480260660b01c1103411960224041000e161501d03401402500304542c400e0103546801c1c40410182d00510944040121090040d5245810084120343d102003886541c0f243d803066a00250780b8000f00d00190814034800c48041c60f01c40c015500c140074402c444c0b0407541014031051a402c0101c0c0d4003050000b030480100c0720104204047c040c90702d10382400c0030b0344601d1041c82c0442900802005 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 703851978 1250 703850728 703850747
    0x307020f060403050415180e07020f0a0501330b031e0906010602060a06031e0c03080a0807080f010b070b04020604080109030816050c1908040504110306031209010f0305180d 76
    0x10043c041d200c00b6818015a43c81f1000d141860444aa800c020840840da01c0f8600740e01000601c1a20301070990625090f01d4000214001c44140e5141c610340a41006000c079508003100f840c0500107901122000c02407100c66441c0550725142000000003401e0b100d000b0040220344030f1003050b4000c18504006100d844007400e01441005001e40c2c030100303445100d80e005200560350000401c1c0c2c40d07481d43da0113590240050410031908640a941c00002084012014243e003051540743d000f61481c00040040080f40000d01c1c410311000c0e104018803440740c0e840d0564441e0750b8000003550712922a400000da030b500541e80210754640c20407150700b081682c0108194005c000b03050b031000704100d80c08015900b0703004a0a100da010342c0240d0a2114a071300e101484002e1600401c521403400341c60b0000b080598044241d00300c40c1d810300205028207405c1c1044a50310740080e090f105828440014002020484111811420142c0b0303040841c0082da00c0314070100d41940154201c502c014844a07003c0c014a52 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 703853228 1250 703851978 703851989
    0x6011b062310140f010305130203030c0709060503011103160c080c01020a08090705100c21030b0f0103090c05060c07090501170708060903040b0d02120106030e0d031806020307020f0604030504 84
    0x514480008100c11080d0015000f807000508126030302c00350f000114001c0000074810511801400e03170040240e2014401001c002028101070150181403c69103426203d00380e2006010b40c0c54a540c98000c08011401e0300d4000c8104201480d403965145402c5400140d010700290118200140c4c01d114480158000c20381030b401d81d25401a584d4901c14090f481d00c0041c414103030082c00c092001da001300c0c401e421501c4109d10030003401345000742d0469a03140200c1014181c01c04260f65520b6618540341c40c60b05080b9104d400d01e42403000d6801c65642501110b034910501e4003c2c0c0d03001c1201c100320761041c400310000e41002c400c02c010340d6030b40350b10406510b00d1080044c01039010f40200485c0a10002c1440303482a92164021032400e4a00742c1d003800e20740c0c001c0080b10340403582130159003881e81041a10b5402171540390340c0400c42c24008000c031030506020700d00740000e0600e482070019502c0f898102140c4410340000380141c40ba610490300b68108122901496154007452040004060308500075000760b84 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 703854478 1250 703853228 703853251
    0x20d0c020c1014070206030612070e010518160810090203091612030503070e130911030d180302061815030907050d0807150b0604030302011d0606011b0623 68
    0x1400c0d0b402e4a2240d090000002d011100b00309071005402e0000007950095405070607407046062000c03005003404440c2d044403ca00c211407004121915260414407440c003924208104c80c6d04180e900d45528440400e0f581040c007100340001403800600d581c182000b00501041035680c1c1c03402d00902a124042101e884c8030000014a001c5800140300c0042099180e058658900c1c2d80c94582060340c220300042200d5601000c401600c6054040d07601500d55414401c95001410344d05c004e04160608000d1b2031500204504040d1841502c2140f40342d48040b41d0701035070b85aa032000901d240740482854514201d81000d0342b81e0140c2e640a1920303006500c103821000c240c8241c0364403002003211200203450050095403003400840e001c1010000c004003602c00c0c6150000d0b00d015047d01044464106074401d0300540d558100e17128100510454403010f2540070805054540717007140000c1d0400b040403274040c002e01c82c030801030030070010154000206414042b00181a0030300c83d0080307115a207400c6613070541c0031 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 703855728 1250 703854478 703854499
    0x320406021615020a08090d02100c170310050f040f050c0301080f06041709031e15060f090103030f050903011a190f09020a020a15020c190213020d020d0c020c 69
    0x2c6901c0101d0180800e1158041c0c040d01801e034607a900f85030001001103178805074404440c00103a40e02090120341059030b0b1540c1d0b40c1034440342030920180c450101da03080c15103020003c02c503d00255401c210b01b9181c086030668030f246444000309006081100050103176a160100703200d000082ca00c00b0714101c411000403560103170842122241c464900b0ba81c0200780e050003980c0388404044030f201402c00800301901300d80e00f103102c00440103201c1e007805124100540251501150503000d404d0030b40d41c840f80c29a02e207010340f114034020616021052201a0811405003101200c6520400803140b4442d0020f009100964030202d014052000503500e080c8918108600d40c14490341841d4808200ea0b1154072480e0901d16000b1105d0203503111010740070441c094903003100c001030811a240405208641c50040e11107843c0319209142903501034070122040040300c07074540181d03640ba402c01000c0ca0894000343c0c4510880e44020084d00905041c02042414001c0610315681d00060301d0034240c00449441d0700700c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 703856978 1250 703855728 703855739
    0x9031e0c0215040b040b0a050d050c031e060f0607031b081306110c0621010e04051509031c14040b07031805070909050c0a080102190f3204060216 64
    0x7184114803071000e013000103100c00c0000400d040c002d8141800303103003070103880d1400040d01c12080700c034100d44c0c60004050120900000306448880403005003e00409903c035810b101c00000c10300d407242d4441c20312904000600c801090702c202c1d01201c000c500150740c4c511500d080d103001a081d8014110800b103254a514001030158854071b24001d00108100240003050032850a120b42e43e800303501060302c440c06404192240b1100c1042190003416034040e011194206450700c1170400b0144d01001082040c11814000108404811500e40c403001003040d0035109406c0310400c1c0541030054a2140398901c1310b08120a11141c1c1c0700e664070820542d0307402c000c401c6429000100034140501d000d030141d4401c10091080064540c416440c640c081d004846c01480000005071000415400180d01a500410581c083c0c07411044012804809800c0508110034041c1e030003020714081c24058031180020094664200110203403a440c052811000c0741c0e903860f205c4902a55802c500d08900180d8000000700050 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 703858228 1250 703856978 703857019
    0xa06050306010837150f090b0301110414031c030b0a150c02060c030c2407081b0912100b190e01270f0c12110d09031e0c02 54
    0x14030070443c0d030324500c0f001c0d00e00010743c0301040d9881ca00e4130041d5074641440100902095440c0180020480c421965050150b1031040e1004441c0b80c03070282c0c1c1455400804040e1a20944050300c11001403c40d21f00d0705040024a4400e2030000f4101c000040440f405200e0b80c0368101c1e0318002c1080c0d580205840e0b68034600501c0c100300040b000300152000416000600d082d50040c41c2208100c4212424040300c0c0880d6810300050303246d004130190100c03051320003401c10741d5002640034255081c404010328062030070079840b8003041508102e8000015661407503549541c11070f45645030100899034583c849604050040c104092901d1040820103411001c1d8002c0d00001415a04100c0d4a0802d69191900164094858801d03040405806020003030b03910986115110380c0034001d0700e012a00c0780d40d20501404214001c40c00040c0d40b07003010b02c54419125000104c80c0c00c1d0403210400540400b00b81400c9403082c8100b81441c15003040944000076443d44500e1200d519402140e505900400c0e00348540d1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 703859478 1250 703858228 703858261
    0x1d010501050406110f0f0a0311010c121e0f060503070509061c14120a0f08070906080903071401090507240c030905030a050d020705061204020904110a060503060108 72
    0x600181c0c00304010f00c441445800f51441ca4540ca070101d614034010b03004001c0c100120544a9511940b10054220906501c07a1a20701c0e01e5640000030401c4c02c4078154020039440c02c6619003020340c0d4481404114640c011189400d003d194100100560311480035400c020781494401d040c803d11560308c000c180d134134010342c185001c0c1d0001020034180003096106104810001c0308203803402900b03618116260031080c0310031300080b002a19480d50340ca001c40c0d0017070a41341c842010601000420000c00004640045008096640300c0c00c0c01c81995503002800c601d113102e103071001002048414106030444105401070030586119034203039414241c407410a8519500d5680800b0000d1200c0c0c0a0201600c1c040d0480f2200c41303019181c01c0c0007250715940402e14041000204403070660120f40c3c4003042c07603410300010340a40800c40c1c210b071504040b150101c50301d80c07000d840688510400c40c046410414101b03d0174201c0c2d0800781c0b070427803066503521010349960012501140850142000a000341041e04582e9 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 703860728 1250 703859478 703859489
    0xc0a061508060426030114040c030608250807230102060c1207121b0f05030c0d110c1608010c0c0c091806051501090806150d031e091d01 60
    0x6181036a220344480d400304c000c1c5504942080494440d0f040c65803a1140114007170507801409800860b551f1301070004031028070081c0c0c02010325090f0103000c44000131507200402c55400c10700304100341c03080300d91210200b001d510042480c07041090010300c2c10810b0031104c0d040c10b0a10000e070500c40c0d1032401a41c0b5000115044079003100c0401c0509040d00340c0d10185d80d041643e41c03414003042c14000000c501210f0311018119140c4c19880c40300c015082c0d101d54148403050702c911300300c2d0450a0035820900075000324140740c04034940701c404655100c603000054032040c40414086600039000e450340c50492180c94020045603500300681c058201c0e0080ca07080701d065500c000d410110710703d001504002001501103086015100201d610041200c900401d03000d040c503000c150ba0707401001000034140260784d9001c2070a980101d0108408460100200810150140c80710740c6108500e1a08840d051140042c15a54442405000a003aa40900424241c604003015424807402c0494140f14845092185 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 703861978 1250 703860728 703860733
    0x10e19050310061518051c1509032a020a03060e1006052101021c0606090e04050a0201080403020f010203090c0f0d050604021c080705010b180112020105030414030c0a061508 76
    0x54840d51182c0c0d5071040c51407203a5041d2058540f11b500240d83c4450a0300300305050007070003414000344a007400c29a41411306010041107030a450b03075005031035400340110405840010000d000b600740d29140c01740c45450340c01010b4580441c0c4915003000140a50340d210724152103410f02d082e010007540d200ba54140c5900800c15030f06640211502c0900940c0b803c1c00150a540074030501c0880e80500042a2040100c0c04002c5011401d1210081a4052030fa10840c24114004203000204030080b8003032101603020320b07003980141e54904003a464440a140e5102440d8030000c1040a41600865210107007c0100e402207000300030f070700070801e1083c02d01d0340140c21504644040703401444c08807407203c20044d190140c0c04418803035455404041e00404000d40b481d9445a04a000c1407901c6101100320070b41c00b0103892410b5050050380c03440e44070a000c2c0203050147c0000070078140301c40c40d1000310303801040d81c0c101c0b81e80d4078a426200b9150030040c4c2c0c080311b089003401d0b0400c43d9a0003100703802e0300381d5011600 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 703863228 1250 703861978 703862009
    0x307180f061214100228020102040b03040303050106081b030f07021906020403060f060305031615050420010239090c03040b011202090a0b010e1905031006 68
    0x4006000300300450300500d8940e5140400950090094603030060705000d030003041d0485011404181c248000d400c0c1040c0168030400c1518240c114004a0102e2032040e03001003004617215000a9009104540044100340b1001c804c2004066064200505a440c90345e24080d05840b07603156103032490b14a44d030102d0024010300c0000d9455203080039582c0c0c017418a104940b0803c1c6200707162803850030014026074036990001070a009200c69070240b140308030300b0504208040340c61074540d40d0300c9000b0311254a124120031540f940920660782006010403040710741c10415800c0520308004074001041034220500c0b1035460b210349640c00810040704070144140e40c40e014241101d4401342d45988444105901d42001e40c0f81c41054940154151050f00840400e543e030742400c0c00e2003584250705a2008001c3c031090007401005840c0c410704660846803d000201d80c001450300141c810b4803070682c001d03402211404903940507112300407401080b14010380541d040e19442020071002c0d0b034001c2c0a01a2141802d08 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 703864478 1250 703863228 703863269
    0x61d04030e1503010909060501080a02241c0504140a08041a07050f0f12070210140c01050901020405040e0309030714150a05072a054b0307 61
    0x481c0e031640c03280c00030100030200c042e000010a075a0800e8101d09440f96450083c1c2e010005030b03200c2c035405441c41c0b000400510344294006461024107007100f0701b054905003000e00450301140d007501c0d01071480042c2d5040100601403c6402007604580030380f00c121108484108208002c240d000d001c5400c44d078000e01e0203003450075840c6900c4c40c1242c1e175100c03040200f02d801d02050042c031803010b5881030303c406000043d640401903454990082d564002e5407500700305103c0165503501d02001103040301d003080900d0541510240c0494090b92103e10140d50918041115400c410743c01041a80d60468081010540c42c0c49100e5030ba028410003140c15901002d400d100b02c84000b02c4079500c801300204180030059150324141016084102e00001007517000c100f51040048001407101c0507030661014030501807030501001a05100c501c00c8600805040ca803680358501625003140c0c07905604140d81c0720f00d035082038030742d200352442d031040c0045080006415076181c500842c4c2c80d022100b0364003002c2c07000170442 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 703865728 1250 703864478 703864487
    0x9040b0f07020316050705010f020f0a0303050c090d05210909060409080f040801090b06060a020d230a08010e1b030103060b0f120c03010c0905060d0902030a02060418061d0403 77
    0x60054002e41c0700c140072184c001d1007404a410380e2140720b000070340349044c40e20001504c06c064842c250b20a540010182410008000071510040c0b5010f00e03010402e0348440c0b20580d10380c410b0070303512600710400ca4290000e014000400100c1d402600d0f048850034140a6200c41c03480c003039502d107240c0c0403001001090b02890301b40c0104100c0c40c0507460282c60a11103207108600c951059009501c140d444a00310410f02182d00b040d250712003800e035441840e1404e065402510361043c83d02504c24440074001750f4146644803d62103400300b11020300aa0b03200700413040980114024803640b5420314200b0006448020007c0b4030007286034440202c0d60940e421941c3e0b0300042c0003100d0400f9000503008088650355590b6001c0c4030b800384c2005014105201616003410300b90303400c0c1c0107000c041c405580020861034403000120b030310700340b4009000180075055100203402e0000e0600c2c007a52011000c940420540346600c030080d200c00c1c603004100139056660911503984050b000c542201403004400041c04213014 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 703866978 1250 703865728 703865731
    0xf031e200d0f0e18040c060207060309150c11030d141f1802130e0405010f20070201090b040e070f080105030a080304020f04140604060f030b01121b081b09040b0f 71
    0x1044244c00b80b0102281d038058070012142a501072034102001c0000640500103000600000d00d07017804591800d80307908220825450140509d240d40e91440c8034541d11403404818039070f5042058a9846d810403c1150140039101c60100d0000c1000340414a0790420405052041c2021030201304e0232490649031070403002d80540c003140200d408100d0420b050010b101e03581c000d4503d0b003182180904050500c5401c403242a01c00b8141989041c10b480c005a0042c8951600c2d00d10407019543c0d00c20740792004a0300d03601c00da403280e098071001080210718590003480982c1320b900559141010140c000c03104854601c0b0a205154158108140300710111700340d4001554058009080d0201040e00800414102d589900202c0c280403130f8071043c01318070302d424024900180001c1c19224103a90035600c8884160406200c0d940a6441410342c40041204103404c03d11034025640190305042e507681d904648942008002440c6e0400e5a8241032252a00c03242a42c0030340c4d0412003141407503484242481a403c1d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 703868228 1250 703866978 703867007
    0xd11031605090d0f03020d120509060609070c02030f0f0616080f06040209100906091406030a0f09020306040506060301060b040612270f12020105010b070f031e200d0f 73
    0x9003e10460202d0240d4042e1014030344644e00a258008103070400404d01e41098403c1e0040a04041c140701402d1000103196801001c21610810310b602c4540003070721135241a8100035050f01882e00342c4900c00e4030224111000303800c002d00380c0b1481d64455040000c0d01c220740070002c0201c2d983e81c2c0811065110300e2055580211b0184c001403a01c1001c4000490007081d6100c00d400150b01498280302003a4031081d10300082104409080144412000050ba07900008102c1544280d41d0070304441e100c2201c1d00101e450f12b1700134007600e0440c1414103040da1905d504403001d0780250b080c0b130760016907a400d0104071802c8a00c02d0751800b00043c801d00240c005452010017a502c280b0300b1646110041242003c5400f0143c42000155044119443e0188040001c0c070590015640f4141c01000402c0385c5c1012190b03225403102c040402c0e207401d03190035102d420580940ca01412050501e03113140700d800030108251020000603a413412001e000c01680d45030514411440020228811b4070704240c0290300d505100003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 703869478 1250 703868228 703868239
    0x100206040f0f08071101020f030a0c030c020f06040b03010929120a170912160e09011401260d02030a2d0203190c08090609060c010e030d1103160509 65
    0xb4502d40f0395107555000031005031850a0340c0e6402000320f42e0100f1050b400c481d40e0b0000786041c4001170704090700c005d40c0800041d0900080001072402c568807081420001d0030024200d60311107071a4100501150803d0041821480c90540009404804501e440340c0391200058071005070503400041c0b28038039880004020785031090b403d401002404000b40303d10701002c3c1140441c1c50700c5005040000800e180a070740c0c030964202445041404441140c0007054a526a510382a030751038480c013031401880e0006074601c031404400c0010404a0314424a0008101010703a91846004428a0a0346441c6140d442d540964810445140c2c024082e84030207501c000d0584034421928a80f010a4502149210100c0c006800c0000c8906003031a201071308502c1c0720000e00d408205400955201c02641c49580032441c0f00d20000302c0c10341c2d1640d44107002ca40d600c074030440c001e10215070004211070f0b50350000c000d80e01c5907601b410340c503c86813480c40003502d2142d480080902c01486031070000340c40660001400f1a0402d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 703870728 1250 703869478 703869503
    0x90309170601061413060305071808060114010512130201080606120a0c051209030d150609030602181c06051e13031106041208060f062704060f050f100206040f 70
    0x140c40708185ca40c0100595140031070315240020700105111200c41205824204403403040c800f10100140d60707410740c1c0500e56030b811040340e5100160b615000310130442011390002e10401c003646040a5036648000c0c402c2c0c031032400584a07031040004900032034074014556500100007601106968012004034926070500030f250030720340210342504a20844034100d00c0e610000701aa48a901481140701c0583e1160a0300f11407400c0041c000e044046501c0081e24858011850800540f0380c10080d07184040c0080420207140711313031142100ea01505a505072000c0e85420002100140189814200d000c0c6c07010350038203241d0329040c410708000c00740c1e80143c0810180c400058503c003420000e85008501808104c80035010386600204001c0004000c207004205100d5201ca450725000700f990401003489070320b14003c40b044002960380701200c2110036400350500600050b0004140d01250689505580014401200600303200400c84010328002c0103174050130000d40800d01178000308240910451001009 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 703871978 1250 703870728 703870747
    0xf0a03051015090f0905060609040f08070318080d02070b090a0302010507060e0a0f05010f060302010509060714120c070905040b010e0c0705150f0f010503120a020705130903091706010614 82
    0x22104a00c04c0082600da6403554030050203000c01000e079004904442c0f0360032525081d03a42820381e84821344000c02100e80418400200340c0280c0600b0300380407000849000d46565030414a40d5050f222031200c002d401140004070b04d80e19030f00d0403200d0405002d882c3d00103452840c1e00440361540030f80c02c2501c40350368a81105074200014440d400c200c6004280000b690700722070502c80e0845074018a0b4040e03040c9800d00820050742c0010980d25100401c441c0c1c151034454a0909038083c030505113607803c0c2c0d40512807101c0c0040c444007000c0c214a40c1107800300c40c00e8907103606444040b00c90558004c0c7ca480d510000403c04500a82d10480d0300116000c9000c0c2007100c3c030390326240b8000c03022a00b106480c032403200f0002c4030500c154506510807001e0f01c3d040f00951500c40483d4031410031205401a0b5000040d090301201d0003005820b0090102030a050002c111194800e0000c004030380c411800103110280001d10082e00303a1190b9500c803844400303440713941d10f484810740340c51283d01503000ca04003040c4071407400b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 703873228 1250 703871978 703871981
    0x10e030c0d03030207020909030702101d030a080c0124050409021f03051801090f0b1f090f4d13080f1609110c0f07050f0a0305101509 59
    0x45942c03080d1400358548655104016a00700d009180c1c85599105008980150b526494084080070300307400c0c0880091021b80000840ca400e440310fa03a01031050f0b43e0700e24200030b02c0c00001d11024180000070004401343c2c0a6400000018044801401c40f40c1a802e100618059000080c101e02c018030b26000904612105600c0550212040012907076070000c01c900c50250445060002c00342c40000c028800c842e54860001803140769015000c0880800020005c40b452180c2c0544840e4000c5240c00c04c0355645041406010310005a60180381000441005910502050010244024030301d00114040c4c09045141c020701e01d20043c0107942d44004034042e41060300044c81940c0310400d45020fa9814510361601e41700402070382c19000d03072165007200c5c001031100b2094001d580302001c01155522017003001c03102c540102d89092101c0d0042d0084150340b82400600c2004032642501d910810500c10303405c02c82d081b45d50b171002a11642001900b00320b9031030241e100d90044408100026609502d61800c1e00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 703874478 1250 703873228 703873249
    0x206330a170601090b0103020a02030a030f06170a050d021507080411040219020610050f220e0a0b0c1207030c090b0a0908070b030903070b09330609090c010e030c 71
    0x1e145410540040c0034000807402100241d250a0800394036201d9001002552489041076220400d075460040c60454040f0ba04104c0003410825900700030a031034070a05030745585002c1402c42d014820494802402d900100e01410340b500201c80110041c0e441d160261032035040200211840e01c41d00955088a55035440a0704010f07207005020000325440c94006407800354050180000e58038004010032140d500d84c455214113900c00d45001050100c0725918844a0054603080c80d042d81c144602c45034404d030700054001c4083d014105900054450050003051031184034400c0c02481030791000541443c0c00380d00144a04001c46c42e051210654402c14a411a00700d000b009000810347c010800c681c0700c0802031540607190110401c0d2460405003e0150349100b40d08008200700404e40c00100003060500000b183d202c42403510040c02c55624403200c82c41d5900c941c98040d21411500840c000d0b003084481e1900c01d032440001081d00da090303040107641e4481d4801c4007550521440304070300f03202d861302c00560 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 703875728 1250 703874478 703874519
    0xf0c01050106110f010b0603011203030f050c090918030307050307110f030c0d0203090604030f050a170d0c0e090406111c020301091808040911040306050906070206330a 74
    0x1000d212519140603401e000c2c010458a02d13a80c102801e102d4295120405c4034111800c0300071a010500c61860f0680282c0302141110b03840074501b0301000300c0038501600401d81a0402c90f06d105041e5250060081414298880088581d00610026407400d00a4000310781100c1030f4100441e006400358800c92030302506080b11900c0b504013260b141c070420001c101c80491641d41780040c42c1001c01d0ba0011440a0248c1e11000c1d01d001048a448800c2c03040600501c00c096411000c0b485200541000400a50b40210740e010a0759151840c4544180e01ca04442c1d400110010505500c0703440daa21240040c0000c5004802203a9040295510724485400b5a811407414960b026840c2e62400038081c040340c2c45600c0c1c9010b01056425210001080c6204803802e40e0500301317000a046016070002131850256030401802286464140540c1c40c0000544910a649039801c440b003955032903006410804412807252460903007080d000208010415443c62545009031009081b55610744401e5104250490780 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 703876978 1250 703875728 703875737
    0x815062b09110409020d0204091406070c03020d0e01080f061f0c06060506030c1b0a141c03060b0a03020906072f04060e06041509051024140f0c01050106 67
    0x20001080002d042c101030380c24085500700492041ca4004c110340520002e0000d10840d41c48100c2713010405940c411411034500c1c0000c48983e032401d0350014000f007860b010107502500c900c01002800900c10940340001e4101a50764000030b40b110340c2080c0c1900b00284c00d66502c420551044032030390b9803d12007010120940d0390b03400b50501d06800d242d0221105034003c140611420420400e426103801d084500f445103200c10007060540340d02e6a00c0c14041c18140003040d1256140000b44101e80004802c0c00030a4106401000b1680188040e811100c0a11656201500c240b29540d200f90117540903051802c4081c10b0645400141d6582210803401c4000c4544000725400f62000c12004080410724040000d503010003049081202c0750801202c0100180d124944445450403644117801410000b00f1075280c0a00c0281400d400c061a0b200141c015200810b04021161007200c03110300c0c50a0740303074001d51a92400705500013001231403588000c048205141e420000c2003440c17030091090350700a008641d603 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 703878228 1250 703876978 703876991
    0xc0c0b0c04170304080c12010b060d0504061d0c0112020d05010801200913050411030f031e09130203060a030b010b07030806121e16140f010815062b 65
    0x1002c0000c00000d080c10719500c144004d0100060008050940010440346950302d0f02d2910703c118090a402040c65801603400b00d100c1c003003c1d0064102c80c1c005d0307200d5541441020607071982c00c0c0400041c20240450b0b94800207891a030b5500800c030081001051038405460520b00541c41c0c0103590080c0d00c03d00309603548021600044140c1101491503404084200340707000001c40000300700b001c0d034201e04411507a41e280403408000503680d0100f4040409401c3d03034038042e5000c034260b45a400c00c0095801c5803140c036a5041c1c205c7e12107011504100b00c0244032080b00340c40c07201240d009400040c9040c2e00101200008000b091414071018001d0120303640c1c2d20750b21151450010111000a0000b502074489055445003840e80031170420388040c220302042e840b41c40f140003850b05d0800c1c1404004000c3c4640500840c0301c6445600e1100985c2068411002100001e001129006400c071603240b18203442501108142c640b4000502c6030003c0c401040c8525134904c120703080c829250000d06083c5958454 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 703879478 1250 703878228 703878239
    0x50d181104050c041421060709050f030a0f1e08040906051c110405070201020f04060e031501030507061d0604090c031407120f150308070501060b03060604090c0c0b0c04 74
    0x19640d20919241c14a404c0510709940d250300407920400c10743c4500074a00c0030f540c41040001ca048040411482210f803a4140900040d180c100c5038083c0301d0158080c00700d81400c83c100021014030903544001100407055290f00c4045080503500d440854141e00300400b1008119240c02401c0a00071100001800d18903160030040d1412a81c0a0054041c0070301d005000428403001566100090079600801c20b541d0b0000203e00901c100d44000b10940c002140119850341d00007081c3c000380034150110f9800d49018021705200d183c0c01d11008155a202510610000b8071078041541010128031000300790100c881c000035110741041e0406441c0741e40d0741d0b211010480c0d06005000c5101207046a0000a00b480d003401080c800100180110309a10381000d10081c20317072548180c900e0440814142681500e918003044194081c9600341d650350700345080410687d41b0903048034044c0d84004d2043d4035140c40c06800c0e03c013070800e00b264074050080640400012a81982011b0f1050b83c4925059603150b0603c0d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 703880728 1250 703879478 703879481
    0x20c0c1002150609041a09210406030501120f1b320a15140702030a050a05120405100e0d0c080303180303191107060608100b010e030a0201050d181104 66
    0x3c0c4481c1c49219560180000310340700789180e4101c0304a0109002c91541c034082143c2c40c00440404da01900780d045070000414000302e002502c2036071407955081c042e41e6a14840c2c1a11026a017002034100c2c000c01d4a0400041e1200c106204174600d01c025006c0820760712a0f08981c11030070801c011040e5069a8654010b5030000c8089040c103e900301c501303a01d000c0c101b5448203000020000c00d81c0511610480c40064042c482081d10340c1c1d0341c1d0080884800311003914000c0e48400b00828221013511450090640d01030314136040ea4240c600c00790190031402c1705500200c030510810f02d10183c1007040e020014001c01c5110184501408102c2c0c02580c3d20300741184400c1712403809113409503c50f002481404036110805098240040203050007285034040368420b56000d12551000078140c40c500b590000314004049980254075444000801400d100c80005490300f400303500e04a54160062011700300158050fa02401042442c5000098002600861403801a256040650311400c0c000d40e0000145810f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 703881978 1250 703880728 703880731
    0x7021c0b0c130906120201030507051204170c10090209090706140702040b13140a020c0a020409050f1207060c11030417011407180609080d03020c0c100215 68
    0x480614008144490300c500180000103803a141d41c045001611051007070030b08000c81c014083d981020442c00c0d03500c000c0ca0a0035140c80d1012030200781443d000800c0c1c54080c80c1645c1407400100d6103104940d8940c1e45030500e81d1480c11a10f080158144901b14580104101029071220803201c001510311f4540100300341514014110b04040d07000711014410554006000c1586400c011031058803205c0d5480020b0203011103903059604041400c42c03403407000490390054584e84901d80961203141d120004098140c1c880c8074003400032544080e01c0e4000608003548000c842c0c0e4010410751300d8444440d19110304000b03000725290481440402c0610a0103010b118142c00b0607100e0074150f01c00c14a00219030307224003607403007142c04440842c4040c50000201703400181003042d0040c0d01c200540740410000d00f01c0342d001801c0c0c0c80c101e0355041e0089941c60184000401351400c480c0100140c11200758110080d5001410902c0280030340c910016098031411100007100d442e81e0050003101c440c030040281300440 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 703883228 1250 703881978 703882009
    0x102060a1806051b0c0d030e1911011701090b0f10090b0a0c080a0c05100501270212010603050636071b1212060e160c080f0702 56
    0x90001001010301c0029111401c0c0e9a01102c0441c80d56100c41840580030303949000c0a468100c00201c00ca000d120100d8400c0381a4056202008000c0110800d9603441c058071900803070b1111540c1100c404039450616100c0c00d0001450280c8c001c0e42c0c50135503003252100c00c2c1d00c416074080e101c491000035071621132102c1d18821815521005000c0c107400d4010b10281241c4100d026000002a041448074400c10b04191401c1e00304010a50b220403900005212140d6030805171914003520311007150b83d03907040c0038882c100d0f0f84c03000d05241080114240303011400000251a20f0040d800c025000c01e103503500290500070300c095100004c0526115040c05059107981c029410079085400580300c520700b00499800c0180c0400c82c0302440c4c2d0359141c1059501d42102038852841c4509408880100510025200000303101c6503148000001c42d0002c010544120340200000e02802500281190350031201c00e541c00052480e000341e5400a0380c40b42c5909900c11429034104420004442c000d41c1880321341c0c40180302 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 703884478 1250 703883228 703883231
    0xc0d180c05012601030308071115100b03090c0103050a0e0105161407080d0c030e01180c0803040e0a09050c0a030303020702040b060a05160c0803120901111e0306030304091a0102060a 80
    0x3c1d001d4407455540f0b44140002001c4c84103100100340340c0c91082e902e020300c0141000031503480c800c044085000d09101201d1489525800c414042414500001a60702600d4010001e05811281d200150003802006240c5441559141425400c19800b4002d8078052a038501c0c1e90410403c10220040c84212041c40900162500304600c0300001d5680c402c864881955400003d403055050500b2400303001424030b5405150309151601a5551210b4401c40400d48202483c0ca800c0350b440d041551240243d100d0906401000400216100c485401034100b081c8610151034204071280c0c000741030f1040540042d000641e000c100c10045003800d108403008118212107150500a03013000041203481103c88003c0300103001c290442c1001360345004c0c003002d0074047d000ea030388802c00c145000c0704c0340c802141d5181c2c00e9801c3c100c1c81140c0040c088101c540303040c540c00850809050000061010b5440540090740521007004005520760480c80f0b107209041c1c1419440c20808568000280f40400103000c1c20f6006 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 703885728 1250 703884478 703884527
    0x22a0c040f1a10080f0c09100e010e010201061d090715020f0f01050609063c19050102030412050c130204031104060e060f0d080a0509030610030b0c0d180c0501 70
    0x29001140d069000c1000885d811551b40e030625010080d02030201625000390020720114005500441020100b8000b070340d4507004140504012400e850407441940c000c800586090486031f41c08503105980102d4500807035940a903100d00060121145032884401078000545c418075203141403003a04500400315000740910b082902c002400c054015003c3c0b440345170103400001c207404070303040c0d401206451104601c505e41908000c2c1e01d000800b02904074401c1d40658040211003450000c2c46080e601e06030300460074a414444106021001e40344241d90a00c035014100c041e13560f9001c00003124440040002da1514510701d0a01c00a589207406544980e04080c02071004400c90701781e082c0d110f2011038018900f4045140880d1040c0601e0801424945c00003481900c5250000000c204850040c0d0071208140d8030f01034400e07820841400300420745030101010458001c0040081c140c40c4205150000300c20403800d40c80ca100c1d210b601000c580d00a8101d0082110350382200950341003d407004d5822918 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 703886978 1250 703885728 703885759
    0xe120d1413170a0f08032710050402061315030f0b0108040312020d090b090f06090a030309032703060c0509030a060c170f011503022a0c040f1a 63
    0x1c8681030300070980c04980700c14a240031440c040000001d0990800007165469400e0f041000c0c06610031a8041c0c0200c880e402c1c00b00c0d04081e109142d81d40c201c081030250100450080c40c54003e0b01c400b82090b83d1124040c44070401041183d000c41e402132026840490002281682c040d041d034240d403e47c81071407458613803c0700c0940d0704015070070390042d40b502d40101d41c00c016070744000003801203110700c42c41e036032a0440c007200700314144a000e400380c6400300440380c82c400e1f5030b00b68a030b0361001250000a160061956503000034004c0e040140c1291003414500484440314443e403070038136142010b58140310701800081003405003a11601181040380d240c058900440c41340403a0303030341c003054000900540d6200003d001c010301c43c1c00390302a00c03003c507000d116003404e02c04c0c13075150628400e000c1d01c0c0040403c0121105907034002e101301c030a103050600b101441141c2d0303800040ca28541400400820380500341040300c1c070380c0c0c491051901d07958860710000380381070344c0007843c0b82002e010a01035801180d004801040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 703888228 1250 703886978 703887007
    0x81005090d0507050d120f021602040f06150c1a0a050a0c180b03090319050c070f050f06035214031305010204030c0302010305130804150e120d14 64
    0x1170480b8140010800300302c1b4402d100420f1020200325019101040c10610701040e04a143c0666000300e80921145a02e030b040a004c580031740c401d45000007200442c080c1143e010745002200340340200b0412030109000d00c4c8410390200d04881141225950308104014885a4415001001403c0c6008040758200140420404079240158030311490f0110008003030b50000c0044819611101c10350030703142c0c2100704010301030f0307040302c1d9030010a8001c8481c041920880601520110340c0c000f040c1c0301210040c0c200344580b9070310140001c1d2485410340350340c0501d4142c20407800c2e01c0c00411405440c01440341c1400880203800f641d44900e41081140140881d60342c0205c0c99824034901e000b82542e0703500c402407c50700a6040c0c1e8001000c3e54000f003400402d0040380c84c4c01400b00c90003078030240155504e91800c091901107a4600130719815040c4802c1c44074010045c06880401603504054900b01c0b1410001342c89022001c03a81d00341d03540400f40c101d06c0c2541c4034200b40c40c2d030a401c0726114100003500d581140e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 703889478 1250 703888228 703888243
    0x503061f05030727031b0801050708060f0607020d0b100602150a0e0708060f0f09060615030a06090e030a091d130c030206030a0608060601090f031b081005090d050705 73
    0xc20003000410b01c1c0e00f130381c8500c0f005403020440120310501040d030720300d81003580d503c601203421300d0f0b0005480c00040e40390040c001d06114101d560344151040d03591902f000545450100c0d1103030404000d10140e001a2038024081d07034842d010b041102c0f2a854a00c00000964605400980c01c40d0041ea030004801d509a203240381d005100e2490200b80413000d07007507646c40c0500e16440010244192414011000c2080010302c0c010551440880d201b60750700b50525a540f10140d41040d007103030100c52500350303c9580c0005183c0203c5000404610181d5600340c09069850881c1e00c012250400200c1492480d001811880244460030048038400d04210040001302002800c0c0114440d020002800f00460300341500c015640c000c10154032410421601001002070340160200e0380304101c00310740741e50300640045003160304503500b591f851415581c0340340c03c1c1d03030034005c0302c550703c0b03201403c0812061800d12981000c1e0301903000000b00c0e482c0c29002e180c81d20707904000200c1803100030801200130500201d06c40 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 703890728 1250 703889478 703889491
    0x100c0909020c0a02100c05163204061805090d0c0f0c1a030702070b0418110c030415020712080d0e0c040515030705090c0301120303060803030103030503061f0503 71
    0x40c1c82ea202885030740d043c003402e114021750140041000800f500d03041040fa492450040f022520844060b0308240411003035800f0700c07222251076003540c0b5021010000d00b0021804400c112031009240342010500761a15900302e40418203201e102120340f004684903040d880304030a00182200b01450b2409003001918800103071039011803e41c060140000c55458000501d206040304820020300c0d8050083c80d00255220030060060724800030f200c140100545d001d03560b1030110040c9620750a000d060042c421040c0e0204001c000f8001790009140c1440508010080e96020814044d040c00c1b00078101034075a0810000009003e2000b4042108541654a907a03100c00700003030b0303140d80f900f070a07803909480110f01d6a009061400704441a0708070710000c00008815001c0f01c410980310010031200440458104108034000c0c80100030340034140403540c00b95406418001010f5841d080c002e41190b0098105a0225600105000c0142080070386c91301d100d9803025030480000f00381f010007001e610010780803 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 703891978 1250 703890728 703890731
    0x6090a17190f030204050d06051e0103020f10020a0803070f1101060617072c0307091119110319140c07030209280f05090a03080105061b1e100c0909 65
    0xc5910b40c0280d0441e0080e003002451101c0c03041d442e01c0c02d100640000c40e80c00c00c4641030700c0c071a02d0313180c1400640303541030325401064030380008404014005c0c0132000300c0034002144110040040130490000086005124a903645000c8580740c80004d480100900c11040c41c582c0341400c2008519842101268144035900b044505519030310342c00c5032205048024810094849044c850314104d0305051420451800e40682d41c245a0f58104403003212860311686034110800c22008603140e5000242d0f810507002c07401c00c5014a04c90401003072031600121710301011518410510803070301e40c000d40341200c0800b183c02c116280c80e4403900c900d40c540c000c4d0701c0001d0094290502003148090342103032541d0007402e46a040c18149108200d44009003902a003116509860b00003c54500c074804140964143d030076896a884a07480c2200340305071580184201c200f0b44904842c00d08a0000c244182150b82c1c1032080c0045a44441202d520304000d03400c840e2022a92404000740d400c182c02880c07420440744895030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 703893228 1250 703891978 703891997
    0x9100305060a0c0e030d0f08010b0f0430050d0917032b0c1d0d08030c0c0a0602040e07020f03040602120d1103040804030c1a04090c03090506090a1719 66
    0x3c06031200358070381c1e41007541405191602d00003070342d0000018600f9901d660740c9140700d903a100c91000540c4211070b091001100c003000144001060602c1800c106c02420950f0500c0e2032090801440c042001c49088a6a40260854440720b0358400988000b41050f11150100801c1c01d080440d0b581c464011017802c9409602600f88001c803450800740d1070201904814484142c80344d200030308a44000c16011b145210b03042411840c1d040c070700c0c0084c0b800c036405481145151208907007004260080c0e990f031400c611130040c0a400280c2c150000e00001c2c41c4001c0c0d030b00307002e0901c001b02a04003480d00c031401076903520a0204010890b40021512030b6007000f018115985d1309040c1c456000781c00c005e42c0c19611010000107020030400120300030012207000d581e10404660316515400c441d08150310003040702c00b5060009000c0030601c5d51021481d05014240000c1c00e01055072418181441213504080300e4205628120510510458012218110a0303e080c9054040003a16081c809118034800c2048007603003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 703894478 1250 703893228 703893251
    0x50301030b012403240603090506160c0f080d021c14070e010c0c0509180f0309131107120f020d0e0d1b031a011508070c06180b09030909100305060a 65
    0x903258805d106120401c0c41030103841c0e840c0035014010302d050440f881d1042c000000d41c950400c0303c4140e113024003559092025a21500d0768041f42e1010001560001004c03c000c404d10390f050f1004000ca8250103032000041701103104040c088031505004098060510410425145e51107070207200222404d00342107244607420b0400354220380c01500a503030808155006d12105802102200c1c4a0800180445100c81010030086440f80928002c240e0840d00720200414003807070540211440c407100c03010039400e0020546900380b4240040c241600442c440046030f040d4aa4140b01c2c81e02c0c180c12a0422101c0008401d01107041c04000060281c84403095004200841d064194803100450300443d15203800c01000102004402d020b10400001034010b42c0204040d60050555502c10070054495419001158840401510015000031501c8580300140b4001400d51000300c2d000384451801540c44681d0384041c0651060050203079903140300464020000500005852030b80142c00100105001b034540 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 703895728 1250 703894478 703894511
    0xc03020903030c07090b030f030730030605030105070e060409091a1f05091e04031806031505120a080904090611070b0c0c1e0c03030307050301030b012403 68
    0x1180d905074580000200d42c4180d10300096200700b6118800020040d00a00038101a5625150460010290401d01c01c071000300706110801200c143e06a140007910540c00903c004a1005101c42c0d4000310799940344c1400182024800e055000803039080101007107070307c4000104240668840c1d041900d449160001c10402032100c810900324844d85031750850b08241c0341c4d02c411341e02e003095001e5240d8400e480003d030034a01031742a80d000321442c3c2d610400600380400d45149080c8014010740900401604c0b80da070300040d006034407000b49030070750b400107c0503604070328564600c1c3c0b241e211034451036152114071010301d00451490315180c1c1c00710f00030340d0315086030780814003034207171208054085860b00c07422080485e140e90003400703001e1142032070203520b40d100404010940294500c01d103c0c0e40c001c1a00d501309240203100343d0242c0541030100c1c2c010681e29000030b891640100c405200040001c4010020080840d84c014054170400c2109124440b0092650001c024005a41f20070581c0703800c212420710102c07 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 703896978 1250 703895728 703895737
    0x3070b0708040b0f030f07050906090108040f0c14030f07050114072105091002070f051009030b01061806090501052b09030e0f0301050408030a02030403050d05090a0b07021506040c0302 81
    0xc8a10703500c4d441c240b0080c2d44d0702d400c200c0b04000454600000104018400c00407103144180c024492800c1210500c01110a00001001141e080800c806e001d00400d00c60f400c010020b041c40e0b01660f403449400c60a050070070007001080c2e02d03581c2c8019803d00c560382c2c000310300705a1440781e11071482d00c2c1d41103818549440304584500c05080450200700c03040c101e03441002032041e098240d030000c0c6031180751001281e65140700d2127042d45040b80b10300280480e00d022581c24114041625042c0c03101034480d02d60980e074207001c1e44070901043d40d0610740100000340043d90001408a82081000c0328a4807001a01d28401d60b224040c0c0e400181c0c0046441c8103015110070860060300c0740400c40a8850310303026101c23000d60181c00344100d551650014140c6014090b003441298401011401e517202d0f9030030b200103900060000c070144201800042d0380c20089200c3c584c0700d0352412005020340c40450030a17000229025054030300310b4000b0882040d254410881080e0008404d84002503c0482404214001d00a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 703898228 1250 703896978 703896989
    0x311011409150c0a0f120e2a03100e01090501050906181507030c03020417060601080a09200109030512120705090f0d06020d0218130b1e01031104030308040b0901060503070b070804 79
    0x502a540c820080000400304071a4230109000c4c0300b08107a81003022403a0682c80344440d4035900042d0365005a606a03081803003441444030010441c00a0b0f60707512802e440d030460303001041d540031400f00b20300300760001c4003130070003102501c043d01f030410b260200256902001004507013816240ca4a42d2031030b83c42541200d0080800027403524812903503286858580505031007480c005006040072840c0344074035108401245074402500310400d0328101119400c1281c0c1c801440c1405000300000000c14018091240070510b021885c560b5180380c484041080c400140000040117030900100d19103490b45c0d01182d002e203004465043c01c018140c038154000c0e109410101e1600350010a0201c40c0950000f1001740101003102d451580098a65210044409403000036621100c41e0030080e40703590102c0011504605d062401050102c12045010704543c01a80100c0028500c0360411041c00965011290481d140700000c2c00351620707180000703a03982c000d806203103400e62000650504100d01001100d00070007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 703899478 1250 703898228 703898231
    0x7020703060905100b0a06020a0320060106230313020f030109080a1808160b03090709021c0515010915090503160f0e0f130311011409150c0a0f12 64
    0x18514200351511514541c0c0c11340d0904002d490411840e00301d10a03019550079030b0041c0000c1d205520308079240d541c400900441d0030f02001c421014118140080d0b4040c0015032070795900c010f0b0043c2401810380442808800740c003130a00a10810003060b4000c9070b50282c04890401001018a00003801000c000c44000c2c50070078005803642072140c0240c1c80340307091100e0114140c40e290340c494100f030b180c5220840d54150401210303014040310740340300007440e0401110011214001e1301c60010030205c0e40907000c002c01c000503110b003400d0030030741c40e0090030752050100b2a05106c241c01d503800030300301c0081d60298840c405198142d252110740300b0400d4800404004040720383c046031549004404030b016004481d482c6000e000c020414213809c070180743c0240c1c4c2606400c205a542e44420481581c4010801c40411101000c45044500c0901443c110641742d07000301c40319810300244003494000f5018260381034207980c1c003c10455a000c001a035061660383e00303048201c40c0007030f041111038200d00c170000300700503 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 703900728 1250 703899478 703899491
    0x501050c0114090c0a0e160807020a0602030703050a050a0207030f05030a0902030a231207020f0a0504050403080609220209040611030a0e0c01111c300b010311120702070306 76
    0x43d100010864440c0f40b090700e4104c0701d00e03290b0741c2c2e0100110044034030f1000d04000380d401143c7e0714480c00550f54022010701c180e6400020550b540803e80e0b005071404000280c43c1c005001011f40300b40b29642d04101240011032034403181d03a9002c0c1031401080e04000901801000244d4002d04a81110310925802019240001c049240034400803403440403200d1032024842d0190440341d00065158402015003228608040c256820400014002000030390070007041000002c11340c69900400c1c0c000d40c441c0e115030072246001024480c4a400040413040b5900701070303851800035140544004649901031b6210b40144c2e4032070030075901522580c5800b14050a0000030800f0459035a40411108440781086c0d0f00b05041c6030004440c501444400840d09402ca016049101098072802e919003d0180c20030300c0812210300c40f56024031607042c0c400d850406a4080c1d90010308000c6c400d0000c04002428100503040400c0d2980d003071401903030005520f00c1c0c095008102c6180c001c010b20030081d03501a2050141 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 703901978 1250 703900728 703900741
    0x7030b0111010626030c120d140c03180c130b0d02102a0305030a1a04020d06060e031605120f1009020117040201020607180506040f05011211040501050c0114 69
    0x42100326103920144a07104c0e0f41c1d90001c0207001c0100c0d002281000000c102c0240403400e220a04d910041102d0f801e2607031003052115603100400014420098a4002900d9185c41c002d07450409420b000664919041034440d9829961141c0d01380c41d004600140006214000e10041400641c0154001e548201c1024a460005500c509407689101c000c43d40c0f00c29103a8041000801c00200080003001b1a5041c0000740302c803170040e44840800740d0b11146e078158249192011500700d0303000b4072107070440f90b071115070600890b5001588203003501c90541c01000d440d40307041c0070024480f00e00c2c0a014032580706481440c10181c410440d01041014000640d501440b070482c00100400202c1c0040740070803c00e9005c00c0350321040d222440e11958040e00544000d80d00e480b001c03034481064041c0c0c54440801c2e11404522502c031500504050301c1004010440ca81c1414005045040b2425000030301030704050700802104061026074080350380c02c0c02d200381c036122202080350150020760755490814820b40200000d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 703903228 1250 703901978 703901999
    0xd0e0a020a08010e060c03070302070c1509060527120712110105070213230a0e01060522230a0b010806030f0721050d0315060e0907030b01110106 64
    0x1000e00c00c4071400c1e2401e81e1034864a003a0307034140407540da0320b8110b50f0000b40b1201d82c510040d0b0b40004503150051401486541d2621060090303000320504107822001c01d84800c1e00042c61802815090a042c1d05007106080000d1b032580541094000d0058912680c170a01d4603a00503a5244480309825145116100e034151065207aa11038152079006810b03a490b41ca0394010011910b1580e0050b0840e082078202030f040078058909200507218900c030207008850785c980e81d002749601801c40040041307001040d0039030707a50a49105400552095410b04000e1842907028080c040c10310000b10b002142d01650707510703201804404d20b0003c101008030001080070415007980031100c5200300f40c83e01070460320b650f018556174a40c413000c48941648840790500240c13440c040e58204240d24090b040e000c2124a6444505084400c2280c50200c2d403154203801004888100d803d0140003289040c80782c4081e58000941d001e6009040c2d101851759800c0c40d00e480da44112160101104400000d02c00c084d62003071b4020 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 703904478 1250 703903228 703903243
    0x1306030b01080a11120a0308090313090e06070e01020706110309040204060c020301050c0901050d0b03010e011401080106060e01091e08030c0d0215280e01051006021905030a030207080d0e 82
    0x8859841101000a02d454040c11705180c41d00745100600004945503001e0b01d02410107418210a480306001850300b5513200040e40019009003400424400300003c01103140143c05004401408201144180145da0000b906021184140f1380503000c2004556040d0842c822031403541d8019000040c0403501c1d5400c940404d48a174400c0d00200100d82c0c895802d080d4902403601600e0006000700f1280c10f41440ca03400081703400d0401000040da05d440030f15043c0c2103899801740a0300030b1138a0401000071407001c1c8100401496a400e14403021304451000078410782e200d00a102010728071b0450a03002140404082010b04104000c582d901c1040c01ea0080d03a40940d00350340001440365484212032560781e40b1800d4001c1d480c0d0032811480101c0700c000c079860360410185840600e90f451481e012030301002d00bd024007507884d03c0d2105105c0c5003030030b100a04015840c0740521241902440c02000102c0010407141c00030f1481c900140c40300081d181910043c1b0500d2034800502d410304505150711840401e80c1c5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 703905728 1250 703904478 703904483
    0xb0f0304290601320c01020c1b030706030902030a0209090f1213060908150c070f0b01060305060405041104050c07020a08100c1b0f210806030606120604021306030b01080a 75
    0x1008418400882015004c500310b03540c2c1c011002c16101c030742c0c003540100500703501182c001c00076060150b40540d0614150041d03100705201880792040361f0781d5040501c8a00050301d8646018015401c60f500840e0383d072961520000d00603107107140090390095007800483d002806d03007425200000c0484584815541000d15900020607186400281003401003868908461460f0040d01210100004541c080d0720300602070498150b08100c01000164020210b000d00c42c49408040091b5040c000c00a0443c1c03801001c01d030095107400240008512114101c10400700220790206059903604d62190041c02242c10094014503565070220b001040070403800301ca03a011920070080709100103001c88036504550b4502446ea0041d400c84000324800d09102202d0340d004121581e00b00d45001c01d032070550045240b45000084c865400d02540d4601800701c1a0849802c44017240000b000000c440c0e2030341c001400080c41004803080381c81070140c035a08000025900000021142e40c1d4491000e0b443d0708609004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 703906978 1250 703905728 703905737
    0x1b020d0e040e120c011b0903054e0d020d05130c06050906041d0f0703050c04090504020f030303040311120301030c05090604110301081006050301060b0f0304290601 72
    0x90400300c0c00d0078880d061007540781e20b0081481243e00c070b40d16243e80c1d018600c115001c2d503c1c4c6104d07a1a4140f070b20043c5e4000b45040e91110301c91803075030505a00b4a0013030606804106200800704450208141d101c100d000c114441e14a000c0a0041c2e0007140d441d001d4241111901003c203000700c0761a41980641070300c0b0800402032045549036154051012240c584c0288201a000710612419224001400407810060310b100c5c40c00c0d0b210600c110942540c1c011210541d03d07010100b0519061100142d80c00c508603007424001418041074400c0d541c06140509030724240da030f400050a656412410304d40809010f01a250390b4180707420010501e80c40e902c018107a83c403c140d006444c02140c0317001c4038100c90b01710151103211390510701007141c02c440180a581d4010703207412030500f14040c800010344c0242843c000504060f10321840d00020b541c10760780128807d0740345c454200002e66040c411624004150030346207a40742d440e85850600840154605507618520240d840d054102003081e01c0e0061809803034 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 703908228 1250 703906978 703906997
    0x2100c0903061a210a0c03060603050c1906050a030612080c061303080a0903050913050a1a090a02030612030304030302030a1b020705061605011a010e010516151b020d 73
    0x2103249101510b000198025400482580441958410140341400f04c2016102a4140c070744035050301c0c021541003a115070751b07200030800420000f0004a0880c07034041d01c0031401d440e0745802c1d9100c82e00341c9102d404240440010712007000c2d4426031103507018046c0c0200f12245d002e15404d080c010f1b40c1103089203103070ba88202404542c2c0800c040c0509400903601d5690007619036504001a006072218410841c2440824070003000703a039840c8a0000340320380468000042c145040c04041c001d58250251002410349200003955440d260204c00990001c160100543d07603440e140082803202c40004807410490002000b404109030341500114003909240c84103101003002d1100c00042c40c44185130610259100e51070400590518802800c20940310440e202c41d0f100c241d4403141c0c2519000703030380b4104282c00c80c050700c0815030304001c840004d01c41c2860700f94107103c510042180035080d4201c0c050100c0700002c0c0c18a9881c5116004044a204107280518010340e5984004c0d585000303d8504101040ca11003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 703909478 1250 703908228 703908251
    0x9020712050f070f02040e0303092a0a03061802031603060501091109100e0607050c1c150504060b420a05220608010608070201020f030105060a02100c090306 69
    0x605951000201d108203c0c078000056542c1e000040000300101d80050f22180c1c80e500701e10091001e144500700361070144c482e0302c10010f007074040001c0c07841a6000044282c100e003649511100c0240050340d03804040011020b2051a20001e2901a503000950510075074128200d607011000c102821640705400030f001d81e980f60b0a0950a07101d00782c0e441041980e0900c80da03410791612608624440382d0310b0910348465003003100031a81e60703030142c1029502c981c000d03480c883e0755040080d080d43d0f402d030405103d682d0b0034455a85a0054980d0500d10b03165554503800410305000561b40550080d1800410076603009806a40c0481d0310305807140d1600104c9400d1409108414040340010441c0d450000349514041018105603a15044040200f0000c5103905511480300000240e81d0003400140c1c83d1920698502080180700a01c010112411a4014010000c801c540b40069a064410403150143c0b98105a0001c07441c080741800740035511030400b4000c86840c1c1d00038070b0080075240109424041d9031000e6 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 703910728 1250 703909478 703909487
    0x118031712010f03020d41120703050405010c050f01090c090b0f0906040f0603060204030c0e090f0c21010609061703180103110d1a09090c0a0302150c0709020712 71
    0x203100c06500503110140020010761f402c603c8144200241c2c0725680e10740031280d000340749800c1d00781e45403010840010a10200042c02c00c003000794580e1034401345143c201d5581c0c005205000714818203042c026461500c1041040c01c1c40414840398102d0b0013004800d00c10b09120f0064180341c8140080e00d490042c0401d600d08260f011340b0400800946007180c41e456003402e0100500355a6094032a19a94400100c0000c2c01c1c0d0000340000e5000e5680c400102d420001401f0007900043c3c0425182e0348103803880c41e103c0300085805815518116102c03035005040070705018586644040c190803035403800f1030105200007592320440907684415140000c1906c1204590350300c0c450810740081f100401c0070021074540c400d800100b85003902032111030400d681c0404a13170985102459040c201062640607608604000c1e808075070025010700205240c1c484480400d566509078080a07000e6840700820401c00045441181c4007402c0100171108400d5840c00380c0c20094220380b004442c20025089100f00c0d4602c075 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 703911978 1250 703910728 703910759
    0x150403030c020d0914060403020414040b07090f0e0a1806092303040b03060d080d1a04140403030e01181401110a020304091505060d020c0609030a020c011803171201 72
    0x707604c07048810382c00c209100116030784082440390310040410011005864601400103227503030071051284542841e242813034400c480100702c507040041c0d48404100402c019040241118180000034480351186414a4040c0840a0200650407900492041006950341c001c0003514028005840d942180100e483c0b1074000c148001860b0b5441840240220070309400119045032000701098001c402c0c66540307c100350085156034194541e0744c0743c900071400b4111106669030b48100d500700900b0b80c04503824403807803001601c054205035403105049007201c400d60000c0305014072081210b017540c03003618004144550041c1051815402c0030500f080650b0980141c803801c01e4681c01a41c1402d0500e40c8440080c08507d80e0a24040c1f0841400903442d15440003c0c0400f0011442c056500d55650f5a403510f0040082c02c00344041e4403c2109041840d808a09081c51039024a4081505001412402210603454001626400c0710070102d41c01c1d00d0b00c01c8004c0442140b036820b44900ba0783d13114100420b0496 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 703913228 1250 703911978 703912003
    0x504140c091e06130e15010614040303030f09050304080a020301290904060204091118011d010309020a09020a1106090d02072705010609050a0e060d0602030612150403030c02 76
    0xd40d031110280c20461214002d9100f4005054400a2031500c04010165010020300c40c115030028801c1d0300c411a1200740203030160056041c15074403400010480200c9201d507100250400d6594203118440c0c1e001904403100003034005085070344a54403200c0b0240c4404850208a02c02c0d880c19958900c0100034200d40c128803c80140303407003030302d140c0001400311401c0c009108981040c1c0c20800813950584500c41e0620f200020318606803036030700111035202903500381443c1c00e051200080150a111914108041c00d0303941c00e1030701140414603072011442d0744649400c01c0c90340e180003142c6d014410741e02c02299039a056060040300d4035a1100098a1b4840608044220040c2c1020400303100b8005500e0b5241800a0030f502d05841c40c065804191044450a13040a40003941c2150104041c2c44d003003401e0381c0a4411940410b600d8144600005ca100e0020040246107980101c0001e5140d61250440d6405403034040a503409060400c0e10220003e100303d03000c0f0007003441c1c15800c0320090b00c0004c64480b00f09 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 703914478 1250 703913228 703913251
    0x2090a09060503190302191a0702010e0c060f120a200a051204080c0a0f020102010e121614061f090504020607030e0a18020c0709020a171005040504140c09 68
    0x420f462844d09011a200006030306610482200e40c403d00028540300c42002d0180000661000c45030312034903079400005d0104411603060658a07000d900010811641455084400c00ea0b81e00e41701c0e04044450207094004095610703200100076402100303800a42844003416990071504c610101188118010b0901d8400010802e03ca18031099000c1103c041e0898065419203043c2800c00806500d020144101141c020030840d07000c90465809009018021a0702c1010341549965520001c01c5401050044810201c800000b0018042c18030301050001303404100390b071018a05220740c01c040300a841d00c4104294501c010001e506512841544d00542e802454280382101589088031521250000140d10090304030f00042c01c80d62500100800ca00416030241e11118000501c42c2030210700e034060000903004211441203143d21040d072600c00200718a45040c581c841030804d90b00400607800194200e85043c0901c020310903242d1540c240b051000d002c45900b015a10240500d25805454030900300 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 703915728 1250 703914478 703914493
    0x120f03010b0d020403020a0b09030d031a0925110c04060b1602040f021c060512060412090b07080909090c130f0905013201030302071a070c0902090a09060503 69
    0x1c4031600024101022804005403c140d183d40018180c0302c2e40364010309180000050340b448500b0140859a10b0b4803060030304002e038460350129001d02c031049002141c031410b9100005030f050301304034100154000030311101da60521145003000d0076408102d14101403d1040c021464154a440d01a040c203840322514100d00b401641c0344d02800f4445000f10480c0d00944070310081030510300c00c1c40074200406000c40703a07440d00c0e411601440126404c5070000b03401140d100d80034104c550000241d064029034000f0010607511541002203554941c283c0015011000020759030007403100c0c2a0140001c104100d540d114161a1228059628120361240e260402c51320103100c04402101e6000f034084598120f4085400d5400380d41e03d5007103643d80307980100b01c090011800c203800403a207442c0d050135020b54101c604c800e50450710040d555424a203d40e910100e800c0c80010345210b0b0203000c2da1002a4441c0381d035040d80c1e403039a032290065040500f40034021030140b8000a840c40320350080c0c41c100e40303010f805407188 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 703916978 1250 703915728 703915739
    0xf0a0c050d0e2109011205090d1b050d180608060306040303150b030103061506110309060922091202010b0d110f0a0815060108040302100903020c0312030108120f0301 73
    0xd4448048054554000ea0090320110070003403801540c80004842c91a40e1440040c001500d11414145480141c5240104105804200042780c907007542c510700f0015020388215107110300f2400980e00c014202c0c055076088890b11908641000103100d41881c482c4a05a21032a04403076801c01210717103d40c180d1000b80842c012034066070000c001a042c2c44141400581c40324490f031415482a40f00f1a61680d494192140c1c2d04030000f0104050052464102c41041d11100071964902a41c141d01c0d200300d00000c4ea002d036960312400c1c01d41c0c0c2044440301c3c0344118030700c005524005058480e8282e0b680c000b0380a0080320b82d88180309810174103100400c108090181c3d500c81402c81e480d047c10868000126080010191b03440c0e0700400010500303100100f840300d8002c1200180100081c0481d41030103110800c1c000084e4011604500090800300000f40d00010303803c1c108d00d01000c3d041e8954040c080d8074507a41c141b50419000714143c403101800c460801c1040700c0d0b03900c450320400614418420f410b1006104 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 703918228 1250 703916978 703916981
    0x901080402210706020718020f030c030a060f0312021011120a06050409080a0906030c1704030905120c0f0d0803180c06040f050907030b0f130915050f0a0c050d 70
    0x2c480d402e075014011040307220024289070003555009040944d102c18000c100c4409090a0a07140c0701c03440300c00b5400c001c054800d00906000117045814598001f00c0041c5500f2100c1d480f5800600380c2029852017607989003000442c0071340070000e400040c083c0d161074900501043c0100d680b080c887c003c409203403840ea400c4045800501030403031030081e502e51034002642d550b1400784901184c058801156100f081010280401401e0390114041c1410f0040e002000390700040b09200c91388595501900a59992030116481411904926407061102222010760b140c0001c1d451858031041e01d00f0b00c0384044481c10071111040c40a0014000034041000a00a8440fa5003440c408600441201d00c02d010980018482c0c1d045600000c00001e082c0741c0030051440c14501454000429003030402062500901103185444510032480c06a8014049000d4010b0164444020950410700c200e12502541402c8409480146c551500c1d10002e1400714018162901c20070300d143c2c00a4503240e01c1c3c2000b8403025030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 703919478 1250 703918228 703918249
    0x1e01020d0e01023d0c0c0206070206072003010e030304082212120e0f0d031409090109020d06080f03030106030b0a03140d1215050d0c0510050301090b01050901080402 73
    0x42c1180182a00101070180711421143c40070000c400c0d50400807500a000300b005401002d40b0608141030000d040c60302c0381c000c01542d1a40c2c3d01034425039981c4046e8004980c1d2845250402021000860030196040e25800d46201d4540c43c01c6000b0701503050704100440c0e0760700094802601c2180c040020000110f881c01c2c00482c44200e502c0c0304004981c0d01d50101c503811044c6841070b41d281201c810001586076000600100c500c008641c0e500d01090000040358110341e01c00401821f10200010103038039000340c201038075a00c03d8024410380b125a124017800000c0c1d00010781c0ca00605040c414045038144010038100030198880b001181141c0c43d1030030032801b51440d005000e410441001340800031075a0054854994072641004094446103404010000251960000ba03030a2500b258040424695076000040f140c0880f0400c100f4081810511801811035005581c40017400d40040c4085810138007a5040703a103009820002d00043c48015245171281c52049400102240000380040c40c0149554 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 703920728 1250 703919478 703919507
    0x308040b0c0c03030c0a06151514090d030320031e040602070f1103120306010903030e04020c15010602010506040506100c1505010914130302150901020f0304080403021e01020d 77
    0x40b0780c04488800480c1c25584100e00e1441550040c10310380080c04510700070520115008500d01001903d0010007041103000d400c1810100000d2190980c044001c1c401034030607403c1c006106446502071031801038010300761a001c808012101c520000805140380007030360300c1480f010000c0d442c0b0b21f083d00c007150342e1800010030403141c4ca0350038401240071820300041070040038402c8420024504406081516041c00220343c03c201070400c004018550764449044000c603070b4141022029800b8080025020b4007c079100704041c2d105030007014500800740c1c40031504841d45900200031130707203c01d020711054030000c80f000c0342c01c00080031900c07000c03a00c00e456841c94107001c1d00d02096640105051102a55401e070b04c002d40c0c0b0b03038403042000481e2403c0c081860304440781c4820f003501b405d01560044d4640d400040101d00964203c030010f50020740a404480d0042d41c0c0b80441c691f43e150a03d800d12907071b0010f000c1039005100004444d148010812400c5001c00816002081044a0060121554007603268079 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 703921978 1250 703920728 703920733
    0x5130c0f0b0406200a0809130606121d060405010c14210405010b120d0906020303060d02041104030609080436051e09060615070f031206210204060506040308040b0c 72
    0x2448040c13a0240f082c100064411241d1942e00c0e1281410403c1c0d62120ba81c0c15030f0f92500c0c1030000c0114680000c00400c03108850036011074580e400c180c5140e400f030f611140320901c0c2e01403201040104001940050f1001c0266100c03103c0c080c0c092081003ca40c0100d10000160600d4821301c680788101c840150ba6200340319000111310500c1c0300010a40c11646c4c6011811198031040740c5801c0f1940107206000600182d100444c01d5160400c0003c2c10762441d040064007455481b103280000001d200222800707541c2040040c07040707061514120340c0c683e120344101980480902240c07284108041710840000e031a80c3d1907885100fa042141500034a0007400384006002c507008044110055081403a116942020152403d49800700c14014845401025040c3c100340401031480012040440d03041c10507010f20f48220000c50915604000f0a001d4000f5022801650751081c141c2580e03038901c12103c1d20981c0d061020341c0d90303901880424051400002d190031030038070090000000b034201a01496444408 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 703923228 1250 703921978 703922027
    0xe07051e0c011b0801081506040c02030f130603060e040b28060b09090a050408030705070812040b0403110706020709020d0b060406021e0a02060a030c090905130c0f0b0406 75
    0x180c0314216080c45415035003c0045800c040c481c9a0009042c1d030040050102078841903601a0750101c101200800c5c20384629501c0072002e1402d032007003041d90641d0b000c400300031703a58004260449100c14038910030040081e0070306a011844450b40710225018645c4903180100c0c1d41c5500b480500401e1030723002c5018051481300980c0e2840d8909005860042144046041c0e44000b040e0a02900d4400141294082030034101400006910300b403c40307030b20010b0743c0b0700030791100c0d01843c09501500c50820700403003030541c0038240818047d81038a007a005610984944040400500ca25519a0760a106927030140c1c001c800200314260654004040803044403200007203050724180001d019801a0f00300c07000591295000f045005100c0701c6010039003c541c0300511410003194000381883c825030f8502c004140d140c2e0140c54040d40200007032400f9040c8440103001c0c901d1300c6034121005082005080c1c03000032417900700040403254546414141c41c05910181e150605141003510390a000d11044001d9600d03030103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 703924478 1250 703923228 703923247
    0x16020a0206040b0a0e030303042d06050a020309010e0c011e3c0207030c0501030c0302070c080319080f1f08030d050601110c090609090106090504080a090e07051e 71
    0x7009102038040c03c11183d884078a00c0400030120300c500b00086000b41d20820500c00032031130828103102450000c8103074503040e841c9071881910308000500010800c60400d002d00c081c182072034029500c41d804a6000300401c01c61407203016a9031a0030883c00d404160004466844101201c40e020424449814140324800031010b500c1180000c1400c05000720034101845d1241400045c5c4070143d81c55240300500a00c1c0c203580325082c403201c140c4985814555101c0c4c9400380d190094040d00c0038150045c402100a90741d0b400300c10303100d501c048940100c2084030030400c815036000302d1907a80a41203c2030880d800343d03a81d1650b20381d22801032120000d0001110700c0021662801c1004041d070720389143c000703c2d01e03041c0707a0009490b541360903203541182d410443d490025620f4041000747e000c14112204a020385070f40f0700b040c2c010070494204100301d0b42410b04000500414000800030b2241d9603507042c446650b103010040b1041d200f900c125000440411081040030002c0d00f07084003610201101d1440c00340c0d0007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 703925728 1250 703924478 703924489
    0x6090a051306030b04050a020307060c0b190b040c110c0a081b030313081c0c0b2e060512010b030103020307150915120c110c0112060918060c1716020a02 67
    0xc54080b0f800347c0c401090201107050502210700200114204455400c6140d62004a40d01d0300500f182c0050025407000d00d0101159004195600c0c4060820031422400500c024a581d50503d5190b105201301c00304102a401d0884000c6c08503526440504401e100d007800b0079a02c1c2046c201c42039072500c420311141c00b0384a0b100d94540000c00a0b00c00400507407040003014988031050000340d03414401c00e071558801040c1c00941d0f403603005010301c0c0c1c0a083e500c5544080c00d9600580001d0340a514100940800d040c6e400c00010201c50181d207000b090343d07a036244c4003121140700900009400d80c2200d40100040d000c40000c101400d203282c204410450780711030607518004400300300f0800064056102c8002c0d40942d204018420741e25181a030040c00008007141d03039520715070106030f040041844c00813000051560120010b000481d0051040304c4d050024918a11904038041d2131702494100f141031001d00031140391401d1821641018030f10f5440011058048180385016030560258007020001a50350 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 703926978 1250 703925728 703925731
    0x10219050102130f090c020102130504231006020c0a0501020d08040f15060302040e07060e060901090f12050d0c0b060d110405010605031f0f1a040902030109021806090a051306030b 79
    0x10507070007100321380c5002c6410054405c010811001e41e44100a100f052a00040700c02003030f10403d43d80821181e00320404010b80c80c02c0764071040f51140d101d200b404420a0302249583c21101c007542141e0f000d50400b4200041c0b03181c644142405684401c2e01c03545450702400225501c94010b003101000302400d511010803008a0b8040c0040242d5690014000c43c40d02d4421000c41000d5000286080c3d03082c070901520400780c5000c02c07842580f0104075004268850301500c00a800c0d018840c2c440560341d00c54403603140c55108011111402110b280700040e0707102d00c0140081c0fa4100c210f91000c0d48550007880b03542074900340103850380382165044038016141e60058070300070400c699039507541e464007180d004140300360071040107103a41c10300c44100650340c5941070030030035601e0890f000c1c3d900c429440d50030030340780c4215404034903064000b100010302d000480d400340c00101001041c0030303070a560078001c008891080c004a40d40c444103002082c003c44c2480410010b0b1285151070000705140c680e1660014040b0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 703928228 1250 703926978 703926989
    0x106060e130504051b040e030c01050411060307080a0f0e0f0a06050c121518070816030501180b03190c080c0609031b0a030807031101051501021905010213 68
    0xc405814005508200080129a1080120801c034500b0300d07a03615900d81d0b050943ea4428480241e401c42002d903902c0c2d003c19401d001c500b00312607568080c4010540a420215000c0c0d52007614030140640d9401c1c45070440340300b604290b450059580d21501580000d00c00e11101d8a50305543e00210300c00a501045080b0300c001d80301c001000030101925004050314002002200c90031018400c2c0c044c240381100d401c0d034012200340072402440014001081c0058800011000000c0302c240901c02d00942200003107014400c003600091b5003803480c0381c0c160141c520038810381d00320040c400c890400d5000d1319405400300c0d401c018140e50701449000042c010444120b40191000194180c081141800c100a0b9241084c0c00303865242c00d104250000948440c0300661a2a0408800714492029500c01c101000a1136104040325142d15050030002c10519844d003561501d50300e40404608495484841030b100158168010004122065014500d400402d4412100c2d50340a0002c02c03a00c1c4490f65044001c0d10 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 703929478 1250 703928228 703928237
    0x5070e01030809031606170c07210e01020613030c050109050f011a0d020a231e1003090203030301121113020c060a0605010c020f010e09090f010b09250c05010606 71
    0x14603110401d805c0c884210601040c0c4003442c2c03c1000700541021880c8610400824250300980d500303407801d407030751007000d03030041003103c0c0e0000c02c04030140042d0321405040f03460341d1102c9011002c14016a6606403d40d1072042e02250410341c1d00c0041d101c4c0785080c00c41172007200081001c070714903900e01d4035120798800c4810690351290a0425401e22170b22402c1a121021104807420b2034058001c03c0e5400c2043c0200c0740c3d200400c010b00d00caa030b600040342c20391b02807018141e1415000b1200213003c200e11407400300b9105501d080f900401c03652003402a000c0150f0002c028500e1a46088846000c0603c2500d080b940102c0c1d81d13183d8000303070380c0d60017007081b043ca0318540c0584c0d07a00515030321070308200000b041313440001e00e031607014080e990744951400b400c540c0c151000320700d8090150041c2d9047c05201896640f080340309080000d02c440c00f00e039072446018414001d201d40c1546100b0002d014004440258401c4400000d05403d95122240100d21841a040ca00c070341090b6610f03043d007500c1c4290407060205 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 703930728 1250 703929478 703929487
    0x2030102120709050f010203070b0a050403020a0b0a02040e010504020711060901090e04140d0215060d030309020603330d060c0e0a030b010f0f14040b191d07030b1c05070e010308 78
    0x14248045c4201c0000c0092002c1c51600c0220b40d03554400c02e002500ba6481c0f256034200003001c00d4000c01c0700d6500990400c602010754900b2018000c00780d030241c040c0e0010990001c2c00002c4071709042c0241d600c8254003003030384001c1189820074054140c125600f1541000a0030a0010741031072240f000a012782d000c0c1803c00340700c688208016152040c10b2443d203085504c000f014040c001c805441d2550807a404540380118064075080841c090142600060340c171130000018007821040100600c0c031082c492a0b51601c811280700c10b0042c2d08004c842e8140d800101002c1c030900010850381c800c0310200110704203032541c0c20043c00031500f42041908119504600200140300000428100d04010aaa58006005070381407500b400086c641351001140102d840700000d40c440d5079409c6510414080503c1c580c2002a40c0707008241e0020360a11607036030018901c5000c130321420f20134040c905a1240203082034100400880d4000d90010943c80203561a000300320303010800000d20915203009500844070340743c49 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 703931978 1250 703930728 703930739
    0x1030b12010b040b0609010f2303090a11120a021302040b04030506071d0a1503060b0a03060e010f030807020d080f03070c060b010c0203071404090f05010e06070e090c0702030102120709 81
    0x1141c00b030260036817040005204154090313a01c458041b000d60746500d40050300e034040c184041d008030350801801010700d0380401004200100090901c1e021805034002800d1441c0c52010302441c00b03030b201070b040720b9500031160140140c2419180c104285500300c03001450207a451061102e50341240d0400caa071904040700380600564080d980c03054401c3c52010500c0c0b140b10a400140059210b8402c44c5542c2d040c020032500d5030fa0103544090010404015081e039540000e00c0700030300525460098054030a2402c00114054078600d00315002e036070b44075111500d00440c940030010046402c4504545c5544c00f08207100c800d48803e0701a40c003a146c10740359160050711610b40038060761418544a41041442d00e01600982d80c0040d07804125030305564121140150140410003820320480043c04201d200300880041140542c0b2422031424014151100303600c0755003080341d0012020000c10741c044440340c040340000f0000720046c100c0314070050005103000c0384038212041e00401142e0311008980e03090b00c00c000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 703933228 1250 703931978 703931981
    0xc04150306050405010605090f130326010803030105040f0e062707140a0518070f0c08161208010b0d0f090f0b0604050c0a0206130f0b09280203100b01030b12010b04 72
    0x1003020600715881527a140c0002109034a00d96170001404006140400d0703030000b19503000040d10070012014024041d0f840714a5599658401c1c403480d030049192000d07c48400034540b0651a141510358060f225907261211700060001c0c214803c10125456400c6005145000f00100d0000f00244091640403280d00e008007e000881503005600581c0101009402c0c0d4002141480c0c0c494400d052001c0700c2e4080d92401c0300e000300c200e0720081911030000b51030241c03088203101e032044607841808502000c010507002120344000a22803400c00b6401442030744e941800e9504031058000c05041d001448400d10785032500d070102039800030340c0d8515042091281d242084d018581e07100030b10690303851910758818802552094001c2c1040c00c1c40030f482030350004100445038030132802900503c0c04089400c0c1905ca490311451a11550f80e08040070013041e007042c001c070418640d0240e4004001c4c101e540706c447c0050024100c001d030a075040543e6900f40602c20ba40780b10352000310103003a90002500c042c01c0401d100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 703934478 1250 703933228 703933231
    0x16060e090702030a2007030b040b0a0e100c03110f12090c01050f1e03160810051e0427030905150412210c051005090c0415030605040501060509 63
    0x1402040560100400075400004807048450145000c0381071072250110390350020705402074940a0700481c18004280202103640c0c6003c0c2c1d0007680e120000da116460f40b5811602500250003898115082131821036815030300070107040a4500b00480c4856043c0c0004e91326901000308000c0380200411181500304514a00d941e00c0188040207200040310480040d0086c028107800c401c64900000b040b1040900f105007400c0c4504540350300340d4032418011a14460700150302c20303075000281020000340b9100c020404201c2101c3e8050040c42e902a00007003504001000b07101c1ca03d81260b1034904d02c0b0310725aa330b0010300803c101a8032101c001e510040c03500030710460042c1e11641c07191a4104c549488100584c0c1110115000b1040c0300c2c25020300351a0050303642c809804905004820310f0b2600440c542c010340001d1950f8882c100351103c0d280302d0510303403080700c409446440803940f04c492040307468282948400e45050740201e000c000c180d40e030759400d001d4401c11541100d0994660354104514144243c0c0719 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 703935728 1250 703934478 703934507
    0x408030f0708070504140d0c0b1903060b03062e0914010302190e0d08040803131d04060e0309060f0406080610080406050a1b0f1409090f06121606 64
    0x1402ca505000000030f01d03034001c2d406040c10401401c100000e85940c3d600a9000a9612402203200fa42e81c409001115802006405843c6000120709007540d0341300e4451501514503070301403142180c0300c1d48140300c44500d03254400e110040c50001c0c0f42c00882c0300001c40d0034140e04581d981903821802c04c0407060b456180c50303940078140350041c84000258100071084188049140c81c1a45060120700c0004400802040703010b051403000040c007268148003c80106007200c100c1030307071024055803a58440b12038100358901c20003280000d00403c000a40c260411480b0210310310440c2e041c0200b000c000744181e84168001540085e000030208450381c1c000051682c01402241d001c110040715035000703402c201c002000141004e598500280b906003d40d8840c20003d0100740703a030f000640322040094a855050b00c01c500c0401d83c44403401d035650303415800b26000c00d08050080035854590307800c208400c030f01c060700540c0d0140350150b00d9041041d0412403402c141544600318001540360000103400881001c404 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 703936978 1250 703935728 703935737
    0x714160f060b1504030803090c0a09020d051003020d110a05060f070203010608070303020312090a0c080606090a060f0e0414010c1d0d08040b130f090f1a1c0c0302090408030f07 77
    0x4030f10015081510112500002a01e590307a03240d98003541450b040b070080300d17030041a101001c030341440a54003034251403001c1d030030800054031910340100c0e0780303c802d200003544200140d0100001603040100448100e0b4050100c18425440700c0c0016040d03003000302103180c100804207514007945801d0240200422802c006824154155140251a4460103007214110701d04e480215000c50300c00c20800d03a036140c2003006041c8681d2104800c070345854081d201c1034401c8225a000c0340148440d403140004070340a0048080031546411021005d614008005640c20b60740e20901d1104a03c080c060360103070945559440d0702a0408030500050000341906213030250420352700040000d50084101c5080d1080c1001e103a40b10300741c85801102ca412550004d0003400b1031490001480040e61f04103015130942c0c014240300c510a144882c0d09200d80b007225055121203103d421030320070542d10040c0300f03003180948008001c0c907450743c000c910344403800d950440302c44c200002001901c3c0c4440e24815003200301c5142 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 703938228 1250 703936978 703936999
    0x2040b130f0b0f06121e07050c010c0306051309020117090a0c080a080a1407120f0f0e15031f030b0103020906060702030d050313060e030a0e03060403080714160f060b 73
    0x1c51164002e17902c4503502440d4110220314119602009544034194801d034482d15450b0245d40100150010392082c2d00e951700f4031805449890103805018160741c6c02030140382a0407107600c144409404660b1081e81400002c174901c0603217035080d00040b48110080340013014408000e00c0d060318031185651010009404c10190900001e045070308031400c65420b4900413811502c0e2900550755072284000040c83e002b55600d881d0100d5811403201c42007800302780c41d075190094a844041d158180140320300c0351312409030340c034103601d4807072032005580c104450b00caa8943c941c040e1143d00080b400c0759001034032011151001081103291143c902540400140c0d000b40c140626540800e43e030710f0360120042c05206011002030721541c021050b4000040d00250705210441e201c1d003600e0340b240d1002081100240f4070a500c1d00e400d00f40056414000c075030650301d40000d941c2c0d0b1a130840384100c1c0ea034419440074008000d50a1a1031401e4480b4609030f0280700ca0b409641d0007840c11108441d001001540201e50604 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 703939478 1250 703938228 703938259
    0x6072a0e01030f020f040203130201080c090102070306020d110a050301080c04230403050c160f0b04060f03021c0203161205090a060e07051f0201050109020316030902040b130f0b 78
    0x4640c0da0440c0d602490b415580546880020f84030480100841c0d00300d80b012041016909084034816140c1d4000e0300d0707030031943e180c0f070301315186512584541d84d0240e805040c0810024103258003c008041031200002001182c2810028090780490000b00000304040f00500228030306214030f1710040c508660812040d070000d124810600a140030b011010071601c800034047c18024021141e450540800b500e0341a02c0e223808080d200c040c540600c190604180e07901295844060301103d06039503503504d95030f15200800704110042c0d131007a50804180d01c141c81d10301200c0045070010750f0040c041c503900b11001c480d41c00001000c03205c2600100010030300705802e2080802e4041011540701d0f400a5000c640c080b68420b5480c80e04103540e02c1290800d1120315480601c070000c0d54803001c440e07201c1e8006d0205984c0c13204008164007098a4804c2c0c42d04141d088400341d40e00a522400c01c0b039101034404142e0080140000b4641a0141130b8480e1054880c05100207031004c078400e28a03510801c40b4000796400d00350 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 703940728 1250 703939478 703939499
    0x30106050a09020d061a0a0206010801050717070c06090317060a0303082202130608060a0204050f060d0e100501181404020409170d02130e04020d02100e06072a 70
    0xb84108000507074009421150f640f41034025a01501404500c544200344c80c100c3c207000d9502081c0401d00500411f4000700c0c0210b0107001c0c41f40242c0b42d9694403030444081070041115040094180024020002c0c4c01000040c030b68000c950286e402615400740051188030034480040d170040c11a0302c6082030707490030310000341c2010300c2e650403521038803000c000711550500c8011503103a800b4001c1d502111101c1580c0c94003c950b08480c00303956040c4155011078403078030028400c1e0b0040303000701c1e640050340481d00a00f07810304c5006441c0d004100c80c0003040039030140140790b0401d843d07203564100907601d50780103112400b440d120581804034042001c018490740031404030030a0b100508007d11a42d21004140140100031007030021060f134820341c01d99501c1355005042d000751f1010340072090003411000b0000c0c04480901440b841250040c000c50000701c0315500304201c0341c00310810002071007051020744c0c43ca5115203024003601d0b4802c04500400d03949484242e0311800480304200c91a001e0328409001d9080c42 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 703941978 1250 703940728 703940749
    0x106080f0a0e01020c100203010501140c06072d110706140313170a030c1b02010c02131b0e03011104080a060b06090d030c210c0b041406040309031103010605 69
    0x20799030001e5001100c0542901920856089204038440c00c10b540441c46807542c0110f04a404c244c07504540c010740081c48000c58054024a258a40c000d50000342e01d2a0040681c000040c0740c0c50100c55000700c4114415205000e0f41100800040740a04c005641c1c901c20411040a000581030442201e580c48141450340d101c01404c0040d11482c181d4500b0800c05901e02c0701c4c10707004801341c0840e220598980000c1c010405002000005203181c55556020855588000c005507010b0f9100040c210a40e0240840d460300d0804c2241781e142d40d040c240084440020451810b004181e50742224011300d0810103081d07982010000c848060104420060550000740d04d900c240c0d4001c2010500580e0030000400c18080c17000d2032600700c0c944a200504250340100d040e81c105100320f5030800c208004840704d0880051480300300d40403e000c1c0a454000c40d8078403888076400340c81000a04402401c4c2034207030303007098401da030102d0110b07614402c1801040784081c003401c400340ac203400170001585050300082c1c1c540c8a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 703943228 1250 703941978 703941991
    0x306100315030606080f070915050f0111072c062b051f140603070b0705070306110a08010e0c0702010f03150b0a0e01081504020906120a140106080f 65
    0x1924408076207100ca004002000450304000c041100c2540c03201c0903515019018a22426401084400b0611202d14403800c0c61081803c2088508241800140440d0824104105040c0164410300082e020b0042101c00c02801482202011502031010003800000d00c81022501c040c0c800c0d400c021587d25008906a42001a45d4a100402552400b091740344864610058914050000040c0c6144680c800c0700c00c455268100400890341d80d140556081c02060301c0e40c1c1d6143d00210000c103e81c0c41174070b029006c00d9018005403a9000e540f981d52400300c3d111140c698220490104091614a420102060040c001c2c41d80703440031807070490340b038039114801e40100a0502c10a00b0325044045d100c0e520000c00700707030707a021080c0000c0d0700c4000c0b00c4115041004504002410598906800d510078540140280d18440e185111640701d003003080040d400c80002550400400e000704064003c0d4954660b004284120000504080010704480084016000303d012301030040280071b22810300c031106907400701 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 703944478 1250 703943228 703943231
    0x11409100c170103050703020901240f021f0501090506030a080702041a041401080111090303030402061e28050702010c1511041e0609050a1203021e01140a0203061003 73
    0x4041d041500c1a02e00c8008a101a500180001c01000070014096040da8001c56012845a03651b00f150804481c5c01454900c02000040200c1c201c10b000c1d507500001e1a0203801910b0500e0458005000c9901d000300032003c1c2d0a0710b8400400421207148a1107411840036409403121540340d032031b124503906c20460300a0184ea512440140c8407070750481c00b1520010001d1090280402d015001c503420b00080c0a0035240b5481c0c851f854096800711800c8946540004d4003860466840e6000c01c98290417110301c0c4160a403201a04e0400441e25400600c2d000000070505840c1380004800958080428180181400301c20048080982c0e004400c00840b16403048058201c20311880c000000362080c250329a0644801240128422003036044041d082104503000720099903031001c00721421402881159002400401d0900c070a4841c669072141050290046405880d4081d03d9075050351115481190103955a002411a462030707036000302d4010301701110540c10341c2003100c00507c901e8840c2d0003190505 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 703945728 1250 703944478 703944491
    0x506130f092d06051503070807050a0c0b1009050c07050d140909060406030206031504050f0f04030807020c09070c020414191808070303020a0216080307030818010f0c0201140910 78
    0x460b682e0040c4000d000080c0000c400c440c0c2007144c007915a04107a40c030300c020444000000b00b40c0307480385040c0c0d000f04199580e0307190440101c4c0c03900ca40541020f00503000340800e04002007842c0b2007502070140070b07204031000706035501c1140c1441401c006602c241c003001c1050100d06004489004404d45402c0241100e2402094440a00182c0200216800250000404002c0080c24083d17803d480031409003e4509110766514103440340e84030681201d24602c0090050082404244203500c4640e001c100c600480300d42400c0b840c0058103440b02102d08000280c4802d10100842c2410300812000440c000c200404504009032105000c1039008560024640d844110f100c00a080e12803040006401c4100f0303907a00ea038181070040182d44903015403809031003100c5208120001b0100d8420490701504040d5051007038541c2c00f00d8071759402a105400808440f0070b02025100301784904c0f84c00b401032480018648048000107829030b007a00741440e00e03040000081221044010030011444030320380d400010b20 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 703946978 1250 703945728 703945811
    0x1707080117160305070f12051e030d1523010c08090112090f0b06030303091b0406170105070e24130f031a0a020906070b04020a0506130f09 61
    0xe108810702c0703041c2e051900507000014840302095001c00c1c3c500300700802000e2034582007a0411001840d00041c640c0e80f10701d4443c2e114040c010b6422102c1c01400040da480c018080310402d00395290b40461442d410074520f01080000c00d00311a18040e01501800f008182210704000b0b000e078800114050103035000050384603820381c4030748145d00360b861450030100401d141604040100d60b40d068800c0381d160b51100041041072030000103480c480c6100900404004419180785c42075800101252900a5112600418420782c003c82809030070f144080005490302c0c05200c01040f00c40b055100e140a000c40701e080701e01800407019282c2201068040c203030313170b10030480b01d04158459895001e5511000d140101004004c2030050035582c5c00380180d0302061a4452400c2d0000300c0c0329144c103035541702404010f4840042c1509515550050000304049141e540c3d800c040f44642c2c0c0318803046840090709000038004504c920501002424400d401041100c0d071a42c04a040d001c5e1a2900703013064003041d00704015 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 703948228 1250 703946978 703946983
    0x20406020c0a060c240e0c0f19140f0a1202011e050a08100b07051b0901060512070c02040f0e01140c0f0d09021c03021e07090c021e06071707080117 65
    0xc5d1030484008200d0366070324824007600c1d044103501c02c40c0700c0e10032203c200f2220b00c1c1251940c51144a9a004010342900e801011540440c0003040c1c035420810100300303200140d0741e2464070380040145d40003014007003106100041001e40221105180050380c40c00e00308105074040305070b506440ca03a08180102ea00c828941c1c81c0d0710180c992007440c407060005a500c04101001c542000b992000c3c003001000c00d41d8031010010351700001d001d418005601480308501900d40703007a0041e044042c50a122003266515000303d4140e0301030740c600d0607142c0c0d1100050205c036002403060b482110a440e540d2815070604465044080c0f080031010203807102c011909140b01400d617408842156402000e021451592034030419544c0101308084d00507020340c0708041d694042c19032280b00c44600c0500070340344140c14842003234010034010b00c0d03101c1144103a0040260807060a802c0b405c2085964000f04024a0302e01401800058507036a001048030303003070003403189403500b10304040d056035003005080074103c2c001c0d050b052 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 703949478 1250 703948228 703948283
    0x8070605060a0b160c0e150907030c02030313060b042912030d1d1606030b09090709020a020304051e0906010203122d150102100c0206060d0c0513020406020c0a060c 72
    0x420340700e0313407047c8003814801c1d031250b2141140590b101c2c815562800415421610030000074005a0010400035201c805c48500041c8014231510000402d0707200c0f14017190131181020007684060084820f0804d4104100240200c94081220707010b205028001c40c0680303c3c0580070203011100c1e10303034454451121505145015080d540000c40d4098402840c07801c55040f41c0b88542d4000c20720b8920740208600b4082c996034071a0110f80003c0c00d0052800500c0d000031f60050b02000111f010510020540b41d03200d0324034010201c0e8041c03140c00b0b000c01c040d00700140d080c800380101c1c4c150340c41040b42905003842c40c404a40d00261540c941c40391226021078071000399642900c00d01c0d02001102c108508185c040d1440710044c4002e9007168044d800782401b01c0102e4480445c403801503402400014482d142c00c0501d020618032400d0005c00b1a0390b03403804280100341e05181229555000314007071100c0e075410044041d0903042100c01c2c0340410f10f41a4080c1200409003400741c4580449000f90040140d0419680f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 703950728 1250 703949478 703949489
    0x3010207120305040b01120317070509030109030509090c030f010306020a0207050909010e15060a0b1e07210804020919141612060303020d050a0201150308070605060a0b160c 76
    0x2284041c0d00c25000500a000c12101168414106400810f61101d8030314542070071076254440358841055141c1d25111014000e00f001e003081420003414496031820700a00c61206c0c400d0301c4a43d1108004403c2128a074030081c0072804145051042218010380300c2000b80c1101e800c100010303a150314242040303003405900d408c050307004201c0b513041c086028030543c840621001d105040e16518441d551080c402403405a0b040f6520100b940d60621101c41840700510340c507852011514410784100040ca49a50070240b016607250060b0508402112034200c4001305407e1240b809480d41d20b01a40016219000584289210080c1c2d4400184506469104071009600070784001400d00d40100003100003e5010050307070000b80e1041c00d014203400640103038001c0d2a4913030050101d40040348011240c0303402c04020f040c110764035004900300b110011030360070b0701a5016001c603660b1600a420b00308180d450141c0b2107400741080032000c0102c900c80300d007901d803c444c0c3c0d5007003905104040d0929061111054000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 703951978 1250 703950728 703950743
    0xf010204180c0905011e030b0d0803100e06030703120c0b0f0604060e22051207080910170403142803140708060616120f140702011d03010207 62
    0x440c100301d5200070441c4002a40700c00344640c14584108540a40d4a0300c1103e01051080c0036018029030100d21a10030f282c0c4074640002c3d80740703049000540d1010095410303650341340000180f040c0215900c0c0f03d2400350a8a580c08001e03030a03d90003180e6540b41e140700141484180d6654241094880c0058081c2d46400c40078840080c100000d00ca0080d6400713a803010310681c6080000203900c500c21024070302c50950344402031041d88480c0401c400490341c44100303c80c2802549020f0f80400307034040180036564043c0413010344400c00042800032040316924001c050000d060300707142942520040c850390080d410302c0e0519081d0742c102046080c40c003da200c0030f01c01030000020141c0e4403900a144c3c0d01d442c4c84c41d54050081e080214054207203410240e85400010703d411000856608000006014082d803492140f54001e207e0340380c80d020300302800820000a40d11182249085038024460f50602d0261b110051034810306900180c00203880001841d444074400141804036a000c0d4184e50741d86030002003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 703953228 1250 703951978 703951987
    0x2040b03040507050a060e0607020f031906021201120503030a15051201091502070b0f040f08031501020705090c09091b070c030317070f0509040b2101060801020a050910020f0102 78
    0x300035450382e10f10301401c0c1c0940450301e00011a00c1c402e0596146104001c1e1065241101540030b014003414502003182e018418000c0d40b0004120801800880034000c0c0740c0140c86400303d101c0d10046184c1a4022901281e000e041500466400310031280c02c40105500080e800105800ca20b441d40103a0b4485540b0105850303030444c84000640210507814031071f4414090b00e4102c1214441240a890b00c0500440360000c0042c8032032243c0c0100680050042c644030440680700d41d9003d070350364411203402c0030301d602130201343c1c02e9035804116010107030404444410301440d107605550014025204200d2240e0380220201d11100e49681c800c16202548a204698901081c1801c65070440b4500c070440000d0703800ca1020a010707280ca48454040e0840340e4400e280321005032800c40300d0b034020701415075110759100d00b449851340e03540089451030440d403c412851440392003105821120b4075488140280d00420034520034075401000c8030f2084104071104603102c2c0300d8420480c43c101c1451901400d82d80f0004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 703954478 1250 703953228 703953233
    0x50c0f0a0302131a0c0616050a052506091109060907030b120601030503090a090c0206060120010501030b0a1a09181005151005070f0809041104030f050d180501030f02040b0304 77
    0x4c024034445030800d003140d045848070859458070302c82c1d100d40000026400c0c072801c440c0a105900130115860040d10031010030001010050140c070178243c040724111780d1026258100310405101c2d5000610440b075a0f007072450840080380400300c0c01407a81c002c02d90385581e480041e075980396800e084400719108a800a42c2c40745000d07580d03648182c4100e480741142d410000b81c5c503c103034055440e0703507580c90740a0079184d205c16005454040035800c0500092030003440b001101d10742441050b0081d40101c44441603418515080c50850b4240c248040b890288402c84140688030301ca8100c1d08140303500080d03240c1079900c0305000d0902010803503070800d490611081c44056582000b051003410703422900b41c142c80d80d250205550700e20a8440c0100302600c1d000340c030300100c1c04520141002c2e00001d0400300f003441624041d49001d503c550800c40d04400c0c000100f02c28442c040004a0088145041000780e050410441405040701403180904054451038101500720864040e50000d19900c801942c4038207203032 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 703955728 1250 703954478 703954529
    0xe010f03022d070f0501063b0703020702030a1b05010e0307030f03020c100f0216081e16230405060915030c1008071806091403030705120d050c0f0a030213 68
    0x1e00c2402e20181c41280615110610230390601d02c0ea50023464041c0100549000b05c41010364001c00380801c0c15400d100a01c0540c405000d00700d80340d840360360034103011010340308450041c140e90f40240f81040008007140040351000903144c0c041e031380c1043e2045a88040392800b24074010030b44500316000744090020641080c0c00244c86441e1012075002d550400710403510041c0b06911521481200358800410f18003104031161144000c0b500090a48400c0c6120001140d100c030714942c042140c03910002480c0b03c40b0a4010b102d908040c1c000c603400e0080d8149840056a03845029040e424412001a4031482542c1c0401070240d8036800030700342940a009800c8090a1200100c95210101c2c958081e06583e80d100c0c030403900300b61401030700c1e082d0f81c40d400e116035002c0c544080400c181c1c2500c0108103003404908200302c0820b40c0450600e840e44e99440c0c4095000c140e60000e420340800030005c5c0811101c001086003910340c551401d00e401a00d4100350401320702e1411069106088500340801c0d018000c4808 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 703956834 1106 703955728 703955741
    0xa0b13050c1002161a070b0a02090405010b030f0901060303020607050c031201090203010f080307230102160305030a15080c06030c0f03070e010f03022d070f0501 71
    0x10036000c00c0b01d90106041c401c01581c8182c0d43c1c520b008031000011030240405c2c2090086172458001003003614010400700608540d0044005228004c8560544401c2100100140441d507510060300415600585000d0750340a14480003c00300441402045d003101d915600400c21039036102e030300303d039903030030038040d0420364001086504800000b00366000e010f0301a0303003401660395143c00962205040580d10560894109005590218100040040c020303e460880d00c4916910300865900a00c10140050014a040300114050690000140d4814078542c04108040c20042d499041c0200142c42044205da21880c9144441e05040c80903541014810380140c1c2480300e201d2000c092500102c0d044d00c00920111400300c681c0d82d10440141480d56a0700f0118540303031880d02050b0711b0825900c01518440380c40c111381007401e5aa40101c4d02e610741c000300b500c49041190b01d0700501802c1c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 703776978 703956834 := by
  have h0 := BRFrame.cov_init 703776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 703776978 ≤ n) (h2 : n < 703956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
